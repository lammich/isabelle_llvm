section \<open>Sepref Tool\<close>
theory Sepref_Tool
imports Sepref_Translate Sepref_Definition Sepref_Combinator_Setup Sepref_Intf_Util
begin

text \<open>In this theory, we set up the sepref tool.\<close>

subsection \<open>Sepref Method\<close>


lemma CONS_init: 
  assumes "hn_refine \<Gamma> c \<Gamma>' R CP a"
  assumes "\<Gamma>' \<turnstile> \<Gamma>c'"
  assumes "\<And>a c. hn_ctxt R a c \<turnstile> hn_ctxt Rc a c"
  assumes "\<And>r. CP_assm (CP r) \<Longrightarrow> CP_cond (CP' r)"
  shows "hn_refine \<Gamma> c \<Gamma>c' Rc CP' a"
  apply (rule hn_refine_cons_cp)
  apply (rule entails_refl)
  apply (rule assms[unfolded hn_ctxt_def])+
  using assms(4) by (auto simp: CP_defs)

lemma ID_init: "\<lbrakk>ID a a' TYPE('T); hn_refine \<Gamma> c \<Gamma>' R CP a'\<rbrakk> 
  \<Longrightarrow> hn_refine \<Gamma> c \<Gamma>' R CP a" by simp

lemma TRANS_init: "\<lbrakk> hn_refine \<Gamma> c \<Gamma>' R CP a; CNV c c' \<rbrakk> 
  \<Longrightarrow> hn_refine \<Gamma> c' \<Gamma>' R CP a"
  by simp

lemma infer_post_triv: "P \<turnstile> P" by (rule entails_refl)

ML \<open>
  structure Sepref = struct
    structure sepref_preproc_simps = Named_Thms (
      val name = @{binding sepref_preproc}
      val description = "Sepref: Preprocessor simplifications"
    )

    structure sepref_opt_simps = Named_Thms (
      val name = @{binding sepref_opt_simps}
      val description = "Sepref: Post-Translation optimizations, phase 1"
    )

    structure sepref_opt_simps2 = Named_Thms (
      val name = @{binding sepref_opt_simps2}
      val description = "Sepref: Post-Translation optimizations, phase 2"
    )

    fun cons_init_tac ctxt = Sepref_Frame.weaken_post_tac ctxt THEN' resolve_tac ctxt @{thms CONS_init}
    fun cons_solve_tac dbg ctxt = let
      val dbgSOLVED' = if dbg then I else SOLVED'
    in
      dbgSOLVED' (
        resolve_tac ctxt @{thms infer_post_triv}
        ORELSE' Sepref_Translate.side_frame_tac ctxt
      )
    end

    fun cons_solve_cp_tac dbg ctxt = let
      val dbgSOLVED' = if dbg then I else SOLVED'
    in
      dbgSOLVED' (
        apply_method_noargs @{method cp_solve_cond} ctxt
      )
    end
    
    fun preproc_tac ctxt = let
      val ctxt = put_simpset HOL_basic_ss ctxt
      val ctxt = ctxt addsimps (sepref_preproc_simps.get ctxt)  
    in
      Sepref_Rules.prepare_hfref_synth_tac ctxt THEN'
      Simplifier.simp_tac ctxt
    end

    fun id_tac determ ctxt = 
      resolve_tac ctxt @{thms ID_init} 
      THEN' CONVERSION Thm.eta_conversion
      THEN' (if determ then DETERM else I) o Id_Op.id_tac Id_Op.Normal ctxt

    fun id_init_tac ctxt = 
      resolve_tac ctxt @{thms ID_init} 
      THEN' CONVERSION Thm.eta_conversion
      THEN' Id_Op.id_tac Id_Op.Init ctxt

    fun id_step_tac ctxt = 
      Id_Op.id_tac Id_Op.Step ctxt

    fun id_solve_tac ctxt = 
      Id_Op.id_tac Id_Op.Solve ctxt

    (*fun id_param_tac ctxt = CONVERSION (Refine_Util.HOL_concl_conv 
      (K (Sepref_Param.id_param_conv ctxt)) ctxt)*)

    fun monadify_tac ctxt = Sepref_Monadify.monadify_tac ctxt

    (*fun lin_ana_tac ctxt = Sepref_Lin_Ana.lin_ana_tac ctxt*)

    fun trans_tac ctxt = Sepref_Translate.trans_tac ctxt

    fun opt_tac ctxt = let 
      val opt1_ss = put_simpset HOL_basic_ss ctxt
        addsimps sepref_opt_simps.get ctxt
        addsimprocs [@{simproc "HOL.let_simp"}]
      |> Simplifier.add_cong @{thm SP_cong}
      |> Simplifier.add_cong @{thm PR_CONST_cong}

      val unsp_ss = put_simpset HOL_basic_ss ctxt addsimps @{thms SP_def}

      val opt2_ss = put_simpset HOL_basic_ss ctxt
        addsimps sepref_opt_simps2.get ctxt
        addsimprocs [@{simproc "HOL.let_simp"}]

    in 
      simp_tac opt1_ss THEN' simp_tac unsp_ss THEN'
      simp_tac opt2_ss THEN' simp_tac unsp_ss THEN'
      CONVERSION Thm.eta_conversion THEN'
      resolve_tac ctxt @{thms CNV_I}
    end

    fun sepref_tac dbg ctxt = 
      (K Sepref_Constraints.ensure_slot_tac) 
      THEN'
      Sepref_Basic.PHASES'
        [ 
          ("preproc",preproc_tac,0),
          ("cons_init",cons_init_tac,3),
          ("id",id_tac true,0),
          ("monadify",monadify_tac false,0),
          ("opt_init",fn ctxt => resolve_tac ctxt @{thms TRANS_init},1),
          ("trans",trans_tac,~1),
          ("opt",opt_tac,~1),
          ("cons_solve1",cons_solve_tac false,~1),
          ("cons_solve2",cons_solve_tac false,~1),
          ("cons_solve3",cons_solve_cp_tac false,~1),
          ("constraints",fn ctxt => K (Sepref_Constraints.solve_constraint_slot ctxt THEN Sepref_Constraints.remove_slot_tac),~1)
        ] (Sepref_Basic.flag_phases_ctrl ctxt dbg) ctxt
    
    val setup = I
      #> sepref_preproc_simps.setup 
      #> sepref_opt_simps.setup 
      #> sepref_opt_simps2.setup
  end
\<close>

setup Sepref.setup

method_setup sepref = \<open>Scan.succeed (fn ctxt =>
  SIMPLE_METHOD (DETERM (SOLVED' (IF_EXGOAL (
      Sepref.sepref_tac false ctxt  
    )) 1)))\<close>
  \<open>Automatic refinement to Imperative/HOL\<close>

method_setup sepref_dbg_keep = \<open>Scan.succeed (fn ctxt => let
    (*val ctxt = Config.put Id_Op.cfg_id_debug true ctxt*)
  in
    SIMPLE_METHOD (IF_EXGOAL (Sepref.sepref_tac true ctxt) 1)
  end)\<close>
  \<open>Automatic refinement to Imperative/HOL, debug mode\<close>

subsubsection \<open>Default Optimizer Setup\<close>

lemmas [sepref_opt_simps] = M_monad_laws

text \<open>We allow the synthesized function to contain tagged function applications.
  This is important to avoid higher-order unification problems when synthesizing
  generic algorithms, for example the to-list algorithm for foreach-loops.\<close>
lemmas [sepref_opt_simps] = Autoref_Tagging.APP_def


text \<open> Revert case-pulling done by monadify \<close>
lemma case_prod_return_opt[sepref_opt_simps]:
  "case_prod (\<lambda>a b. Mreturn (f a b)) p = Mreturn (case_prod f p)"
  by (simp split: prod.split)

lemma case_option_return_opt[sepref_opt_simps]:
  "case_option (Mreturn fn) (\<lambda>s. Mreturn (fs s)) v = Mreturn (case_option fn fs v)"
  by (simp split: option.split)

lemma case_list_return[sepref_opt_simps]:
  "case_list (Mreturn fn) (\<lambda>x xs. Mreturn (fc x xs)) l = Mreturn (case_list fn fc l)"
  by (simp split: list.split)

lemma if_return[sepref_opt_simps]:
  "If b (Mreturn t) (Mreturn e) = Mreturn (If b t e)" by simp

text \<open> In some cases, pushing in the returns is more convenient \<close>
lemma case_prod_opt2[sepref_opt_simps2]:
  "(\<lambda>x. Mreturn (case x of (a,b) \<Rightarrow> f a b)) 
  = (\<lambda>(a,b). Mreturn (f a b))"
  by auto



subsection \<open>Debugging Methods\<close>
method_setup sepref_dbg_preproc = \<open>SIMPLE_METHOD_NOPARAM' (fn ctxt => K (Sepref_Constraints.ensure_slot_tac) THEN' Sepref.preproc_tac ctxt)\<close>
  \<open>Sepref debug: Preprocessing phase\<close>
(*method_setup sepref_dbg_id_param = \<open>SIMPLE_METHOD_NOPARAM' Sepref.id_param_tac\<close>
  \<open>Sepref debug: Identify parameters phase\<close>*)
method_setup sepref_dbg_cons_init = \<open>SIMPLE_METHOD_NOPARAM' Sepref.cons_init_tac\<close>
  \<open>Sepref debug: Initialize consequence reasoning\<close>
method_setup sepref_dbg_id = \<open>SIMPLE_METHOD_NOPARAM' (Sepref.id_tac true)\<close>
  \<open>Sepref debug: Identify operations phase\<close>
method_setup sepref_dbg_id_keep = \<open>SIMPLE_METHOD_NOPARAM' (Config.put Id_Op.cfg_id_debug true #> Sepref.id_tac false)\<close>
  \<open>Sepref debug: Identify operations phase. Debug mode, keep intermediate subgoals on failure.\<close>
method_setup sepref_dbg_monadify = \<open>SIMPLE_METHOD_NOPARAM' (Sepref.monadify_tac false)\<close>
  \<open>Sepref debug: Monadify phase\<close>
method_setup sepref_dbg_monadify_keep = \<open>SIMPLE_METHOD_NOPARAM' (Sepref.monadify_tac true)\<close>
  \<open>Sepref debug: Monadify phase\<close>

method_setup sepref_dbg_monadify_arity = \<open>SIMPLE_METHOD_NOPARAM' (Sepref_Monadify.arity_tac)\<close>
  \<open>Sepref debug: Monadify phase: Arity phase\<close>
method_setup sepref_dbg_monadify_comb = \<open>SIMPLE_METHOD_NOPARAM' (Sepref_Monadify.comb_tac)\<close>
  \<open>Sepref debug: Monadify phase: Comb phase\<close>
method_setup sepref_dbg_monadify_check_EVAL = \<open>SIMPLE_METHOD_NOPARAM' (K (CONCL_COND' (not o Sepref_Monadify.contains_eval)))\<close>
  \<open>Sepref debug: Monadify phase: check_EVAL phase\<close>
method_setup sepref_dbg_monadify_mark_params = \<open>SIMPLE_METHOD_NOPARAM' (Sepref_Monadify.mark_params_tac)\<close>
  \<open>Sepref debug: Monadify phase: mark_params phase\<close>
method_setup sepref_dbg_monadify_dup = \<open>SIMPLE_METHOD_NOPARAM' (Sepref_Monadify.dup_tac)\<close>
  \<open>Sepref debug: Monadify phase: dup phase\<close>
method_setup sepref_dbg_monadify_remove_pass = \<open>SIMPLE_METHOD_NOPARAM' (Sepref_Monadify.remove_pass_tac)\<close>
  \<open>Sepref debug: Monadify phase: remove_pass phase\<close>

(*method_setup sepref_dbg_lin_ana = \<open>SIMPLE_METHOD_NOPARAM' (Sepref.lin_ana_tac true)\<close>
  \<open>Sepref debug: Linearity analysis phase\<close>*)
method_setup sepref_dbg_opt_init = \<open>SIMPLE_METHOD_NOPARAM' (fn ctxt => resolve_tac ctxt @{thms TRANS_init})\<close>
  \<open>Sepref debug: Translation phase initialization\<close>
method_setup sepref_dbg_trans = \<open>SIMPLE_METHOD_NOPARAM' Sepref.trans_tac\<close>
  \<open>Sepref debug: Translation phase\<close>
method_setup sepref_dbg_opt = \<open>SIMPLE_METHOD_NOPARAM' (fn ctxt => 
  Sepref.opt_tac ctxt
  THEN' CONVERSION Thm.eta_conversion
  THEN' TRY o resolve_tac ctxt @{thms CNV_I}
)\<close>
  \<open>Sepref debug: Optimization phase\<close>
method_setup sepref_dbg_cons_solve = \<open>SIMPLE_METHOD_NOPARAM' (Sepref.cons_solve_tac false)\<close>
  \<open>Sepref debug: Solve post-consequences\<close>
method_setup sepref_dbg_cons_solve_keep = \<open>SIMPLE_METHOD_NOPARAM' (Sepref.cons_solve_tac true)\<close>
  \<open>Sepref debug: Solve post-consequences, keep intermediate results\<close>

method_setup sepref_dbg_cons_solve_cp = \<open>SIMPLE_METHOD_NOPARAM' (Sepref.cons_solve_cp_tac false)\<close>
  \<open>Sepref debug: Solve post-consequences concrete postcond\<close>
method_setup sepref_dbg_cons_solve_cp_keep = \<open>SIMPLE_METHOD_NOPARAM' (Sepref.cons_solve_cp_tac true)\<close>
  \<open>Sepref debug: Solve post-consequences concrete postcond, keep intermediate results\<close>
  
method_setup sepref_dbg_constraints = \<open>SIMPLE_METHOD_NOPARAM' (fn ctxt => IF_EXGOAL (K (
    Sepref_Constraints.solve_constraint_slot ctxt
    THEN Sepref_Constraints.remove_slot_tac
  )))\<close>
  \<open>Sepref debug: Solve accumulated constraints\<close>

(*
  apply sepref_dbg_preproc
  apply sepref_dbg_cons_init
  apply sepref_dbg_id
  apply sepref_dbg_monadify
  apply sepref_dbg_opt_init
  apply sepref_dbg_trans
  apply sepref_dbg_opt
  apply sepref_dbg_cons_solve
  apply sepref_dbg_cons_solve
  apply sepref_dbg_cons_solve_cp
  apply sepref_dbg_constraints

*)

method_setup sepref_dbg_id_init = \<open>SIMPLE_METHOD_NOPARAM' Sepref.id_init_tac\<close>
  \<open>Sepref debug: Initialize operation identification phase\<close>
method_setup sepref_dbg_id_step = \<open>SIMPLE_METHOD_NOPARAM' Sepref.id_step_tac\<close>
  \<open>Sepref debug: Single step operation identification phase\<close>
method_setup sepref_dbg_id_solve = \<open>SIMPLE_METHOD_NOPARAM' Sepref.id_solve_tac\<close>
  \<open>Sepref debug: Complete current operation identification goal\<close>

method_setup sepref_dbg_trans_keep = \<open>SIMPLE_METHOD_NOPARAM' Sepref_Translate.trans_keep_tac\<close>
  \<open>Sepref debug: Translation phase, stop at failed subgoal\<close>

method_setup sepref_dbg_trans_step = \<open>SIMPLE_METHOD_NOPARAM' Sepref_Translate.trans_step_tac\<close>
  \<open>Sepref debug: Translation step\<close>

method_setup sepref_dbg_trans_step_keep = \<open>SIMPLE_METHOD_NOPARAM' Sepref_Translate.trans_step_keep_tac\<close>
  \<open>Sepref debug: Translation step, keep unsolved subgoals\<close>

method_setup sepref_dbg_side = \<open>SIMPLE_METHOD_NOPARAM' (fn ctxt => REPEAT_ALL_NEW_FWD (Sepref_Translate.side_cond_dispatch_tac false (K no_tac) ctxt))\<close>
method_setup sepref_dbg_side_unfold = \<open>SIMPLE_METHOD_NOPARAM' (Sepref_Translate.side_unfold_tac)\<close>
method_setup sepref_dbg_side_keep = \<open>SIMPLE_METHOD_NOPARAM' (fn ctxt => REPEAT_ALL_NEW_FWD (Sepref_Translate.side_cond_dispatch_tac true (K no_tac) ctxt))\<close>
method_setup sepref_dbg_side_bounds = \<open>SIMPLE_METHOD_NOPARAM' (Sepref_Translate.bounds_tac)\<close>

method_setup sepref_dbg_prepare_frame = \<open>SIMPLE_METHOD_NOPARAM' Sepref_Frame.prepare_frame_tac\<close>
  \<open>Sepref debug: Prepare frame inference\<close>

method_setup sepref_dbg_frame = \<open>SIMPLE_METHOD_NOPARAM' (Sepref_Frame.frame_tac (Sepref_Translate.side_fallback_tac))\<close>
  \<open>Sepref debug: Frame inference\<close>

method_setup sepref_dbg_merge = \<open>SIMPLE_METHOD_NOPARAM' (Sepref_Frame.merge_tac (Sepref_Translate.side_fallback_tac))\<close>
  \<open>Sepref debug: Frame inference, merge\<close>

method_setup sepref_dbg_frame_step = \<open>SIMPLE_METHOD_NOPARAM' (Sepref_Frame.frame_step_tac (Sepref_Translate.side_fallback_tac) false)\<close>
  \<open>Sepref debug: Frame inference, single-step\<close>

method_setup sepref_dbg_frame_step_keep = \<open>SIMPLE_METHOD_NOPARAM' (Sepref_Frame.frame_step_tac (Sepref_Translate.side_fallback_tac) true)\<close>
  \<open>Sepref debug: Frame inference, single-step, keep partially solved side conditions\<close>


subsection \<open>Utilities\<close>

subsubsection \<open>Manual hfref-proofs\<close>
method_setup sepref_to_hnr = \<open>SIMPLE_METHOD_NOPARAM' (fn ctxt => 
  Sepref.preproc_tac ctxt THEN' Sepref_Frame.weaken_post_tac ctxt)\<close>
  \<open>Sepref: Convert to hnr-goal and weaken postcondition\<close>

method_setup sepref_to_hoare = \<open>
  let
    fun sepref_to_hoare_tac ctxt = let
      val ss = put_simpset HOL_basic_ss ctxt
        addsimps @{thms hn_ctxt_def pure_def}

    in
      Sepref.preproc_tac ctxt 
      THEN' Sepref_Frame.weaken_post_tac ctxt 
      THEN' resolve_tac ctxt @{thms hn_refineI}
      THEN' asm_full_simp_tac ss
    end  
  in
    SIMPLE_METHOD_NOPARAM' sepref_to_hoare_tac
  end
\<close> \<open>Sepref: Convert to hoare-triple\<close>



subsubsection \<open>Copying of Parameters\<close>
lemma fold_COPY: "x = COPY x" by simp

sepref_register COPY

text \<open>Copy is treated as normal operator, and one can just declare rules for it! \<close>
lemma hnr_pure_COPY[sepref_fr_rules]:
  "CONSTRAINT is_pure R \<Longrightarrow> (Mreturn, RETURN o COPY) \<in> R\<^sup>k \<rightarrow>\<^sub>a\<^sub>d (\<lambda>_. R)"
  apply (intro hfrefI hn_refineI) unfolding is_pure_conv pure_def
  by vcg
  

lemma hn_id[sepref_fr_rules]: "(\<lambda>x. Mreturn x,RETURN o id) \<in> [\<lambda>_. True]\<^sub>c A\<^sup>d \<rightarrow> A [\<lambda>x r. r=x]\<^sub>c"
  apply sepref_to_hoare
  by vcg
  
subsubsection \<open>Destructors\<close>  
  
lemma hn_MK_FREEI:
  assumes "(free,RETURN o freea) \<in> A\<^sup>d \<rightarrow>\<^sub>a\<^sub>d (\<lambda>_. unit_assn)"
  shows "MK_FREE A free"
proof -  
  note [vcg_rules] = assms[to_hnr, THEN hn_refineD, unfolded hn_ctxt_def invalid_assn_def pure_def, simplified]
  show ?thesis
    by rule vcg
qed  
  
lemma MK_FREE_hrcompI[sepref_frame_free_rules]:
  assumes "MK_FREE A f" 
  shows "MK_FREE (hr_comp A R) f"
proof -
  note [vcg_rules] = assms[THEN MK_FREED]
  show ?thesis
    apply rule
    unfolding hr_comp_def
    by vcg
qed

lemma MK_FREE_hrrcompI[sepref_frame_free_rules]:
  assumes "\<And>x. MK_FREE (A x) f" 
  shows "MK_FREE (hrr_comp S A R x) f"
proof -
  note [vcg_rules] = assms[THEN MK_FREED]
  show ?thesis
    apply rule
    unfolding hrr_comp_def hr_comp_def
    apply (simp; safe)
    apply vcg
    done
qed


subsubsection \<open>Short-Circuit Boolean Evaluation\<close>
text \<open>Convert boolean operators to short-circuiting. 
  When applied before monadify, this will generate a short-circuit execution.\<close>
lemma short_circuit_conv:  
  "(a \<and> b) \<longleftrightarrow> (if a then b else False)"
  "(a \<or> b) \<longleftrightarrow> (if a then True else b)"
  "(a\<longrightarrow>b) \<longleftrightarrow> (if a then b else True)"
  by auto

subsubsection \<open>Eliminating higher-order\<close>
  (* TODO: Add similar rules for other cases! *)
  lemma ho_prod_move[sepref_preproc]: "case_prod (\<lambda>a b x. f x a b) = (\<lambda>p x. case_prod (f x) p)"
    by (auto intro!: ext)

  declare o_apply[sepref_preproc]

end
