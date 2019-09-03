section \<open>Generic VCG Framework\<close>
theory Basic_VCG
imports Main Defer_Slot
begin

text \<open>
  This theory provides a generic VCG framework. The main features are:
  
  \<^item> Automatic creation of framed rules from frame-rules and vcg-rules:
    The frame-rules are combined with the vcg rules to form the actual rule to be applied.
  
  \<^item> Backtracking control via rule priorities and PRECOND-tag:
      \<^item> The rules are ordered by user-specifiable priorities
      \<^item> Assumptions marked with PRECOND must be solved in order for the rule to be applicable.
        The VCG is the iterated on the remaining subgoals. 
    
  \<^item> Solver infrastructure. The user can register solvers, that are activated 
    for subgoals that match a solver-specific shape.

\<close>


  ML_file \<open>subgoal_focus_some.ML\<close>

  named_theorems vcg_tag_defs \<open>Definitions of internal tags\<close>


  definition [vcg_tag_defs]: "PROTECT x \<equiv> x"
  lemma PROTECT_cong[cong]: "PROTECT x = PROTECT x" ..
  lemma PROTECTI: "\<Phi> \<Longrightarrow> PROTECT \<Phi>"
    and PROTECTD: "PROTECT \<Phi> \<Longrightarrow> \<Phi>"
    by (auto simp: PROTECT_def)


  definition [vcg_tag_defs]: "CONCLUSION x \<equiv> x"
  lemma CONCLUSIONI: "\<Phi> \<Longrightarrow> CONCLUSION \<Phi>"
    and CONCLUSIOND: "CONCLUSION \<Phi> \<Longrightarrow> \<Phi>"
    by (auto simp: CONCLUSION_def)
    
  lemma recover_CONCLUSIONE: "\<lbrakk>\<not> CONCLUSION P; \<not> thesis \<Longrightarrow> P\<rbrakk> \<Longrightarrow> thesis" 
    by (auto simp: CONCLUSION_def)
    
  lemma CONCLUSION_intro[intro!]: 
    "CONCLUSION True" 
    "\<And>P. \<forall>x. CONCLUSION (P x) \<Longrightarrow> CONCLUSION (\<forall>x. P x)"
    "\<And>P Q. \<lbrakk> P \<Longrightarrow> CONCLUSION Q \<rbrakk> \<Longrightarrow> CONCLUSION (P\<longrightarrow>Q)"
    by (auto simp add: CONCLUSION_def)
    
  ML \<open>
    structure VCG_Lib = struct
    
      fun simp_only_tac thms ctxt = simp_tac (put_simpset HOL_basic_ss ctxt 
        addsimps thms)
    
      fun simp_named_thms_tac ctxt n = simp_only_tac (Named_Theorems.get ctxt n) ctxt  

      fun full_simp_only_tac thms ctxt = full_simp_tac (put_simpset HOL_basic_ss ctxt 
        addsimps thms)
    
      fun full_simp_named_thms_tac ctxt n = full_simp_only_tac (Named_Theorems.get ctxt n) ctxt  

      fun asm_simp_only_tac thms ctxt = asm_simp_tac (put_simpset HOL_basic_ss ctxt 
        addsimps thms)
    
      fun asm_simp_named_thms_tac ctxt n = asm_simp_only_tac (Named_Theorems.get ctxt n) ctxt  
      

      fun rewrite_only_conv thms ctxt = Simplifier.rewrite (put_simpset HOL_basic_ss ctxt 
        addsimps thms)
                  
          
      (* Apply conversion on given constant and its arguments *)
      fun tag_conv name cv ct = case head_of (Thm.term_of ct) of
        Const (name',_) => if name=name' then cv ct else raise CTERM ("tag_conv " ^ name, [ct])
      | _ => raise CTERM ("tag_conv " ^ name, [ct])  
        
  
      (* Apply conversion on all premises tagged with constant (and Trueprop!)*)
      fun in_tag_prems_conv name cv = Conv.params_conv ~1 (
        fn ctxt => Conv.prems_conv ~1 (
          Conv.try_conv (HOLogic.Trueprop_conv (tag_conv name (cv ctxt)))
        )
      )

      (* Simplify only given tag in premises *)
      fun simplify_tag_tac name ctxt = CONVERSION (in_tag_prems_conv name (Simplifier.rewrite) ctxt)
      
      (* Simplify premises, may solve goal *)
      fun simplify_prems_tac ctxt = 
        resolve_tac ctxt @{thms PROTECTD} THEN' asm_full_simp_tac ctxt THEN_ALL_NEW resolve_tac ctxt @{thms PROTECTI}
      
        
      (* Recover conclusion if the argument tactic put it into the assumptions in negated form.
        rc_tac is invoked on goal with recovered conclusion, if recovery took place.
        It's allowed for tac to solve the goal, in which case no recovery is attempted.
        
        This tactic is useful to clarify subgoals, but with the guarantee that the 
        conclusion is preserved.
        
        Note that you should have the CONCLUSION_intro rule.
        
      *)  
      fun RECOVER_CONCLUSION' rc_tac tac ctxt = 
        resolve_tac ctxt @{thms CONCLUSIOND}
        THEN' tac
        THEN_ALL_NEW (
          resolve_tac ctxt @{thms CONCLUSIONI}
          ORELSE'
          eresolve_tac ctxt @{thms recover_CONCLUSIONE} THEN' rc_tac
        )
        
      val RECOVER_CONCLUSION = RECOVER_CONCLUSION' (K all_tac)
        
      
      local
        fun apply_decl_attribute thm (attr:attribute) context =
          attr (context,thm) |> fst |> the_default context
    
      in          
        fun chain_decl_attribs attrs : attribute = fn (context,thm) =>
          (SOME (fold (apply_decl_attribute thm) attrs context), NONE)
    
        fun parse_attribs ctxt attrs = map (Attrib.attribute ctxt) attrs
        
        fun chained_decl_attr ctxt attrs = chain_decl_attribs (parse_attribs ctxt attrs)
      end    
      
      
      
    end
  \<close>


  (* Tag for preconditions that must be solved in order for rule to apply *)
  definition [vcg_tag_defs]: "PRECOND \<Phi> \<equiv> \<Phi>"
  lemma PRECONDI: "\<Phi> \<Longrightarrow> PRECOND \<Phi>" by (simp add: PRECOND_def)  

  definition PRIO :: "'a::numeral \<Rightarrow> bool" where [vcg_tag_defs]: "PRIO _ \<equiv> True"
  lemma PRIOI: "PRIO i" by (simp add: PRIO_def)
  
  named_theorems vcg_normalize_simps \<open>Additional normalization rules\<close>
  named_theorems vcg_normalize_congs \<open>Additional normalization congruences\<close>
  named_theorems vcg_normalize_nosplits \<open>Split rules to be removed for normalization\<close> 
    (* TODO/FIXME: How to specify the positive set here? Can we erase all split rules? *)
 
  declare if_split[vcg_normalize_nosplits]
    
  (*
    Either apply decomposition rule, 
    or apply a frame-rule instantiated with a rule
  *)
     
  named_theorems vcg_decomp_rules
  named_theorems vcg_decomp_erules
  named_theorems vcg_rules
  named_theorems vcg_frame_rules
  named_theorems vcg_frame_erules

  
  definition VCG_DECOMP_RULE :: "bool \<Rightarrow> bool" where [vcg_tag_defs]: "VCG_DECOMP_RULE x \<equiv> x"
  definition VCG_DECOMP_ERULE :: "bool \<Rightarrow> bool" where [vcg_tag_defs]: "VCG_DECOMP_ERULE x \<equiv> x"
  definition VCG_RULE :: "bool \<Rightarrow> bool" where [vcg_tag_defs]: "VCG_RULE x \<equiv> x"
    
  lemma 
    VCG_DECOMP_RULEI: "x \<Longrightarrow> VCG_DECOMP_RULE x" and
    VCG_DECOMP_RULED: "VCG_DECOMP_RULE x \<Longrightarrow> x" and
    VCG_DECOMP_ERULEI: "x \<Longrightarrow> VCG_DECOMP_ERULE x" and
    VCG_DECOMP_ERULED: "VCG_DECOMP_ERULE x \<Longrightarrow> x" and
    VCG_RULEI: "x \<Longrightarrow> VCG_RULE x" and
    VCG_RULED: "VCG_RULE x \<Longrightarrow> x"
    unfolding vcg_tag_defs .
  
    
  ML \<open>
    structure Basic_VCG = struct
      structure Static_Xform_Data = Generic_Data
      (
        type T = (Proof.context -> conv) Name_Space.table
        val empty = Name_Space.empty_table "static rule transformers"
        val merge = Name_Space.merge_tables
        val extend = I
      );
    
      
      fun print_rule_xformers verbose ctxt = let
        val table = Static_Xform_Data.get (Context.Proof ctxt)
        fun pretty_xformer (name,_) = Pretty.mark_str name
      in
        Pretty.writeln_chunks (map pretty_xformer (Name_Space.markup_table verbose ctxt table))
      end
      
      fun static_xform_rl ctxt = let 
        val table = Static_Xform_Data.get (Context.Proof ctxt)
        val cnvs = Name_Space.fold_table (fn (_,cnv) => fn s => cnv ctxt :: s) table []
      in
        fold (Conv.fconv_rule) cnvs
      end  
    
      fun add_static_xformer bnd cnv context =
        Static_Xform_Data.map (Name_Space.define context true (bnd,cnv) #> snd) context
    
      fun get_prio_thm ctxt thm = 
        case Thm.prems_of thm of 
          @{mpat "Trueprop (PRIO (numeral ?p))"}::_ => 
            (case try HOLogic.dest_numeral p of
              SOME pr => (pr,thm OF @{thms PRIOI})
            | NONE => (
              Pretty.block [Pretty.str "Invalid Priority: ", Syntax.pretty_term ctxt p]
              |> Pretty.string_of |> warning;
              (100,thm)
            ))  
        | _ => (100,thm)
            
      fun mk_framed_rl_aux fr_thm thm = let
        val n = Thm.nprems_of fr_thm
        
        fun tr 0 _ = NONE
          | tr n ls = 
              case try (op OF) (fr_thm,ls) of 
                SOME thm => SOME thm 
              | NONE => tr (n-1) (asm_rl::ls)
        
      in
        tr n [thm]
      end

      fun mk_framed_rl ctxt = let
        val simplify_thm = (static_xform_rl ctxt)
      in
        fn fr_thm => fn thm => 
          mk_framed_rl_aux fr_thm thm
          |> map_option simplify_thm

      end
      
      fun frame_rl ctxt = let
        val fr_thms = Named_Theorems.get ctxt @{named_theorems vcg_frame_rules}
        val fr_ethms = Named_Theorems.get ctxt @{named_theorems vcg_frame_erules}
        
        val mk_frl = mk_framed_rl ctxt
      
      in
        fn thm =>                 
          (map_filter (fn fr_thm => mk_frl fr_thm thm) fr_thms
          |> map (fn x => (false,x)))
          @
          (map_filter (fn fr_thm => mk_frl fr_thm thm) fr_ethms
          |> map (fn x => (true,x)))
      
      end
      
      fun get_rules ctxt = let
        datatype rl_mode = RULE | ERULE | FRAME
      
        val rls1 = Named_Theorems.get ctxt @{named_theorems vcg_decomp_rules}
        val rls1e = Named_Theorems.get ctxt @{named_theorems vcg_decomp_erules}
        val rls2 = Named_Theorems.get ctxt @{named_theorems vcg_rules}

        val rls = 
            map (fn thm => (RULE,get_prio_thm ctxt thm)) rls1 
          @ map (fn thm => (ERULE,get_prio_thm ctxt thm)) rls1e 
          @ map (fn thm => (FRAME,get_prio_thm ctxt thm)) rls2 
        |> sort (fn ((_,(i,_)), (_,(j,_))) => int_ord (i,j) |> rev_order)
        |> map (fn (f,(_,thm)) => (f,thm))

        val mk_frl = frame_rl ctxt
        
        val rls = map 
          (fn (f,thm) => 
            case f of
              FRAME => mk_frl thm
            | RULE => [(false,thm)]
            | ERULE => [(true,thm)]
          ) rls
        |> flat
      in
        rls
      end
      
      val clear_rules = 
        Context.proof_map (
          Named_Theorems.clear @{named_theorems vcg_decomp_rules}
          #> Named_Theorems.clear @{named_theorems vcg_decomp_erules}
          #> Named_Theorems.clear @{named_theorems vcg_rules})

      fun all_framed_rls ctxt =
        get_rules ctxt |> filter (not o fst) |> map snd
        
      fun all_framed_erls ctxt =
        get_rules ctxt |> filter fst |> map snd
          
          
      fun vcg_rl_from_ctxt_tac ctxt = biresolve_tac ctxt (get_rules ctxt)
        (* TODO/ FIXME: Use a net! *)
              
      fun vcg_rl_from_prems_tac ctxt = let
        val ctxt = clear_rules ctxt
        
        val ntadd = Context.proof_map oo Named_Theorems.add_thm
        
        fun is_vcg_rl _ ct = let
          val t = Thm.term_of ct
            |> Logic.strip_assums_concl
        in
          case t of
          @{mpat "Trueprop (VCG_DECOMP_RULE _)"} => true
        | @{mpat "Trueprop (VCG_DECOMP_ERULE _)"} => true
        | @{mpat "Trueprop (VCG_RULE _)"} => true
        | _ => false
        end
        
        fun declare_vcg_rl thm ctxt = case Thm.concl_of thm of
          @{mpat "Trueprop (VCG_DECOMP_RULE _)"} => let
              val thm = thm RS @{thm VCG_DECOMP_RULED}
              val ctxt = ntadd @{named_theorems vcg_decomp_rules} thm ctxt
            in ctxt end
        | @{mpat "Trueprop (VCG_DECOMP_ERULE _)"} => let
              val thm = thm RS @{thm VCG_DECOMP_ERULED}
              val ctxt = ntadd @{named_theorems vcg_decomp_erules} thm ctxt
            in ctxt end
        | @{mpat "Trueprop (VCG_RULE _)"} => let
              val thm = thm RS @{thm VCG_RULED}
              val ctxt = ntadd @{named_theorems vcg_rules} thm ctxt
            in ctxt end
        | _ => raise THM ("declare_vcg_rl: Not a vcg-rule",~1,[thm])
    
      
      in
        Subgoal_Focus_Some.FOCUS_SOME_PREMS is_vcg_rl (fn {context=ctxt, prems, ...} => let
          val ctxt = fold declare_vcg_rl prems ctxt
        in
          FIRSTGOAL (vcg_rl_from_ctxt_tac ctxt)
        end
        ) ctxt
      end
                  
      fun vcg_rl_tac ctxt = vcg_rl_from_ctxt_tac ctxt ORELSE' vcg_rl_from_prems_tac ctxt
        (* This uses rules from premises only as a fallback.
          TODO: Another option would be to always look for rules in premises,
            and treat them like any other rule!
        *)

      structure Solver_Data = Generic_Data (* TODO: Non-canonical (possibly wrong) use of binding *)
      (
        type T = (thm * bool * binding * (Proof.context -> int -> tactic)) Item_Net.T;
        val empty: T = Item_Net.init (fn (a,b) => #3 a = #3 b) (single o Thm.concl_of o #1);             
        val extend = I;
        val merge : T * T -> T = Item_Net.merge;
      );

      fun try_solvers_dflt keep dflt_tac ctxt = let
        val net = Solver_Data.get (Context.Proof ctxt)
      in
        SUBGOAL (fn (prem,i) => let 
          val krls = Item_Net.retrieve_matching net (Logic.strip_assums_concl prem)
          val tacs = 
            map (fn (thm,is_xform,_,tac) => 
                (if not is_xform andalso not keep then SOLVED' else I) 
                (CHANGED o (resolve_tac ctxt [thm] THEN' tac ctxt))
                (* TODO: Is this CHANGED actually needed? *)
              ) krls
          @ [(if not keep then SOLVED' else I) (dflt_tac ctxt)]
        in
          APPEND_LIST' tacs i
        end)
      end
            
      fun try_solvers keep ctxt = try_solvers_dflt keep (K (K no_tac)) ctxt
      
      fun try_solve ctxt = try_solvers true ctxt
      fun solve ctxt = DETERM o (try_solvers false ctxt)
      
      fun try_solve_dflt dflt_tac ctxt = try_solvers_dflt true dflt_tac ctxt
      fun solve_dflt dflt_tac ctxt = DETERM o (try_solvers_dflt false dflt_tac ctxt)
      
      fun gen_add_solver (thm,is_xform,name,solver) = 
        (Solver_Data.map (Item_Net.update (thm,is_xform,name,solver)))
        
      fun add_solver (thms,name,solver) = fold (fn thm => gen_add_solver (thm,false,name,solver)) thms
      fun add_xformer (thms,name,solver) = fold (fn thm => gen_add_solver (thm,true,name,solver)) thms

      fun rem_solver name = 
        (Solver_Data.map (Item_Net.remove (asm_rl,false,name,K (K no_tac))))
      val get_solvers = Context.Proof #> Solver_Data.get #> Item_Net.content

      fun print_solvers ctxt = let      
        val solvers = get_solvers ctxt
        fun pretty_solver (thm,is_xform,name,_) = Pretty.block [
          Binding.pretty name,Pretty.brk 1,Pretty.str (if is_xform then "(xform)" else "(solve)"),Pretty.str ":",Pretty.brk 1, Thm.pretty_thm ctxt thm]
      in 
        Pretty.fbreaks (map pretty_solver solvers) |> Pretty.block |> Pretty.string_of |> tracing;
        solvers
      end      

      fun solve_precond_tac ctxt =
        resolve_tac ctxt @{thms PRECONDI} THEN_ELSE' (solve ctxt, K all_tac)
      
      fun step_precond_tac ctxt tac = 
        tac THEN_ALL_NEW_FWD solve_precond_tac ctxt

      fun vcg_normalize_tac ctxt = let
        val ctxt = ctxt
          addsimps Named_Theorems.get ctxt @{named_theorems vcg_normalize_simps}
          |> fold Simplifier.add_cong (Named_Theorems.get ctxt @{named_theorems vcg_normalize_congs})
          |> fold Splitter.del_split (Named_Theorems.get ctxt @{named_theorems vcg_normalize_nosplits})
          
        fun is_Trueprop @{mpat "Trueprop _"} = true | is_Trueprop _ = false
      in
        CONCL_COND' (is_Trueprop) THEN_ELSE' (VCG_Lib.RECOVER_CONCLUSION (clarsimp_tac ctxt) ctxt, K all_tac)
      end 
        
      fun vcg_step_tac ctxt = let
      in
        vcg_normalize_tac ctxt THEN_ALL_NEW (
          step_precond_tac ctxt (vcg_rl_tac ctxt)
          (*ORELSE' REPEAT_DETERM1 o (match_tac ctxt @{thms conjI impI allI exI})*)
          ORELSE' solve ctxt
        )
      end  
        
      val defer_if_no_schematics_tac = SUBGOAL (fn (t,i) => 
        if has_Var t then no_tac
        else Defer_Slot.to_slot_tac i
      ) 
      
      val cfg_defer_goals = 
        Attrib.setup_config_bool @{binding vcg_defer_goals} (K false)
      
                      
      val local_setup = I
        #> Local_Theory.add_thms_dynamic (@{binding vcg_framed_rules}, all_framed_rls o Context.proof_of)  
        #> Local_Theory.add_thms_dynamic (@{binding vcg_framed_erules}, all_framed_erls o Context.proof_of)  
      
      
    end
    
  \<close>
  
  local_setup \<open>Basic_VCG.local_setup\<close>

  method_setup vcg_ensure_defer_slot = \<open>Scan.succeed (fn ctxt => SIMPLE_METHOD (
    if Config.get ctxt Basic_VCG.cfg_defer_goals then Defer_Slot.ensure_slot_tac else all_tac
  ))\<close>
  
  method_setup vcg_try_solve = \<open>Scan.succeed (fn ctxt => SIMPLE_METHOD' (TRY o resolve_tac ctxt @{thms PRECONDI} THEN' Basic_VCG.try_solve ctxt))\<close>
  method_setup vcg_solve = \<open>Scan.succeed (fn ctxt => SIMPLE_METHOD' (TRY o resolve_tac ctxt @{thms PRECONDI} THEN' Basic_VCG.solve ctxt))\<close>

  method_setup vcg_rl_internal = \<open>Scan.succeed (fn ctxt => SIMPLE_METHOD' (Basic_VCG.vcg_rl_tac ctxt))\<close>
  method_setup vcg_step_internal = \<open>Scan.succeed (fn ctxt => SIMPLE_METHOD' (Basic_VCG.vcg_step_tac ctxt))\<close>
  method_setup vcg_normalize = \<open>Scan.succeed (fn ctxt => SIMPLE_METHOD' (Basic_VCG.vcg_normalize_tac ctxt))\<close>

  attribute_setup vcg_static_xformed = 
    \<open>Scan.succeed (Thm.rule_attribute [] (fn context => Basic_VCG.static_xform_rl (Context.proof_of context)))\<close>
    \<open>Apply static rule transformations\<close>
    
    
  method vcg_rl = vcg_ensure_defer_slot, vcg_rl_internal  
  method vcg_step = vcg_ensure_defer_slot, vcg_step_internal  
        
  method vcg_solve_precond = then_else \<open>rule PRECONDI\<close> \<open>vcg_solve\<close> succeed
  method vcg = vcg_ensure_defer_slot, vcg_step_internal+

  
  (* Tag for solving by assumption*)
  definition [vcg_tag_defs]: "SOLVE_ASM \<Phi> \<equiv> \<Phi>"
  lemma SOLVE_ASMI: "\<Phi> \<Longrightarrow> SOLVE_ASM \<Phi>" by (auto simp: SOLVE_ASM_def)
  
  (*
  definition [vcg_tag_defs]: "SOLVE_SIMP \<Phi> \<equiv> \<Phi>"
  lemma SOLVE_SIMPI: "\<Phi> \<Longrightarrow> SOLVE_SIMP \<Phi>" by (auto simp: SOLVE_SIMP_def)
  *)
  
  lemma thin_TrueE: "\<lbrakk>True; P\<rbrakk> \<Longrightarrow> P" .
  lemma imp_trans: "A \<longrightarrow> B \<Longrightarrow> B \<longrightarrow> C \<Longrightarrow> A \<longrightarrow> C" by blast
  lemma imp_ball_cong: "\<lbrakk>\<And>x. x\<in>S \<Longrightarrow> P x \<longrightarrow> P' x \<rbrakk> \<Longrightarrow> (\<forall>x\<in>S. P x) \<longrightarrow> (\<forall>x\<in>S. P' x)" by simp
  lemma imp_all_cong: "\<lbrakk>\<And>x. P x \<longrightarrow> P' x \<rbrakk> \<Longrightarrow> (\<forall>x. P x) \<longrightarrow> (\<forall>x. P' x)" by simp
  
  
  named_theorems_rev 
        vcg_prep_ext_rules \<open>Normalization rules to prepare external solving\<close>
    and vcg_prep_ext_congs \<open>Congruence rules for external solving normalization\<close>
  
  (* named_theorems_rev vcg_prep_ext_start_rules \<open>Rules to start external solving normalization\<close> *)
  
  lemmas [vcg_prep_ext_congs] = Set.conj_mono imp_ball_cong imp_all_cong
  
  definition "EXT_TAG P \<equiv> P"
  lemma EXT_TAGI: "P \<Longrightarrow> EXT_TAG P" unfolding EXT_TAG_def by auto
  lemma EXT_TAGD: "EXT_TAG P \<Longrightarrow> P" unfolding EXT_TAG_def by auto
  
  lemma EXT_TAG_fold: "Trueprop P \<equiv> Trueprop (EXT_TAG P)" unfolding EXT_TAG_def . 
  lemma vcg_prep_ext_start: "\<lbrakk> EXT_TAG P; P \<longrightarrow> Q \<rbrakk> \<Longrightarrow> Q" by (blast dest: EXT_TAGD)
  
  ML \<open>
    structure VCG_External_Solving = struct
    
      fun tag_prems_tac ctxt = let open Conv in CONVERSION (
        params_conv ~1 (fn _ => prems_conv ~1 (try_conv (rewr_conv @{thm EXT_TAG_fold}))) ctxt
      ) end
    
      fun so_norm_tac ctxt = let
      
        val refl_thms = @{thms imp_refl}
        val trans_thms = @{thms imp_trans}
        val cong_thms = Named_Theorems_Rev.get ctxt @{named_theorems_rev vcg_prep_ext_congs}
        val rule_thms = Named_Theorems_Rev.get ctxt @{named_theorems_rev vcg_prep_ext_rules}
          |> map (Local_Defs.unfold ctxt @{thms atomize_imp})
      
        val refl = SOLVED' (resolve_tac ctxt refl_thms)
        val congs = resolve_tac ctxt cong_thms
        val transs = resolve_tac ctxt trans_thms
        val rules = resolve_tac ctxt rule_thms
        
        fun rec_tac i st = let
          val app_cong = congs THEN_ALL_NEW_FWD rec_tac
          val app_rl = rules
        in
          REPEAT_DETERM' (CHANGED o (transs THEN' SOLVED' (app_cong ORELSE' app_rl))) THEN' 
          refl
        end i st 
      in 
        rec_tac
      end
    
      fun prepare_subgoal_tac ctxt = let
        val norm_tac = dresolve_tac ctxt @{thms vcg_prep_ext_start} THEN' SOLVED' (so_norm_tac ctxt)
      in
        tag_prems_tac ctxt
        THEN' REPEAT_DETERM' norm_tac 
        THEN' REPEAT_DETERM' (eresolve_tac ctxt @{thms thin_TrueE conjE impE exE})
      end
    end
  \<close>

  method_setup vcg_prepare_external = \<open>Scan.succeed (fn ctxt => SIMPLE_METHOD' (VCG_External_Solving.prepare_subgoal_tac ctxt))\<close>
  
  definition [vcg_tag_defs]: "SOLVE_AUTO \<Phi> \<equiv> \<Phi>"
  lemma SOLVE_AUTOI: "\<Phi> \<Longrightarrow> SOLVE_AUTO \<Phi>" by (auto simp: SOLVE_AUTO_def)

  definition [vcg_tag_defs]: "SOLVE_DEFAULT_AUTO \<Phi> \<equiv> \<Phi>"
  lemma SOLVE_DEFAULT_AUTOI: "\<Phi> \<Longrightarrow> SOLVE_DEFAULT_AUTO \<Phi>" by (auto simp: SOLVE_DEFAULT_AUTO_def)
  
    
  definition [vcg_tag_defs]: "SOLVE_AUTO_DEFER \<Phi> \<equiv> \<Phi>"
  lemma SOLVE_AUTO_DEFERI: "\<Phi> \<Longrightarrow> SOLVE_AUTO_DEFER \<Phi>" by (auto simp: SOLVE_AUTO_DEFER_def)
  lemma SOLVE_AUTO_DEFERD: "SOLVE_AUTO_DEFER \<Phi> \<Longrightarrow> \<Phi>" by (auto simp: SOLVE_AUTO_DEFER_def)

  definition [vcg_tag_defs]: "NORMALIZE \<Phi> \<equiv> \<Phi>"
  lemma NORMALIZEI: "\<Phi> \<Longrightarrow> NORMALIZE \<Phi>" by (auto simp: NORMALIZE_def)
  
  
  ML \<open>fun solve_auto_try_defer_tac ctxt = if Config.get ctxt Basic_VCG.cfg_defer_goals then
          resolve_tac ctxt @{thms SOLVE_AUTO_DEFERD} THEN' Basic_VCG.defer_if_no_schematics_tac
        else K no_tac\<close>
  
  declaration \<open>K (Basic_VCG.add_solver (@{thms SOLVE_ASMI},@{binding solve_asm},fn ctxt => assume_tac ctxt ORELSE' resolve_tac ctxt @{thms TrueI refl order_refl}))\<close>
  
  declaration \<open>K (Basic_VCG.add_solver (@{thms SOLVE_AUTOI},@{binding solve_auto},
    fn ctxt => (VCG_External_Solving.prepare_subgoal_tac ctxt THEN' SELECT_GOAL (auto_tac ctxt))))\<close>
  declaration \<open>K (Basic_VCG.add_solver (@{thms SOLVE_AUTO_DEFERI},@{binding solve_auto_defer},fn ctxt => 
    VCG_External_Solving.prepare_subgoal_tac ctxt THEN' (
      SOLVED' (SELECT_GOAL (auto_tac ctxt)) 
      ORELSE' solve_auto_try_defer_tac ctxt
      ORELSE' (SELECT_GOAL (auto_tac ctxt))
    )))
  \<close>

  declaration \<open>K (Basic_VCG.add_solver (@{thms SOLVE_DEFAULT_AUTOI},@{binding solve_default_auto},fn ctxt => 
      VCG_External_Solving.prepare_subgoal_tac ctxt THEN'
      (SOLVED' (Basic_VCG.try_solve_dflt (SELECT_GOAL o auto_tac) ctxt)
        ORELSE' solve_auto_try_defer_tac ctxt
        ORELSE' (Basic_VCG.try_solve_dflt (SELECT_GOAL o auto_tac) ctxt)
      )))\<close>
  
    
  declaration \<open>K (Basic_VCG.add_xformer (@{thms NORMALIZEI},@{binding xform_normalize},fn ctxt => Basic_VCG.vcg_normalize_tac ctxt))\<close>
  
  declaration \<open>K (Basic_VCG.add_solver (@{thms Defer_Slot.remove_slot},@{binding remove_empty_defer_slot},fn ctxt => K all_tac))\<close>
  
  
  ML_val \<open>Basic_VCG.get_solvers @{context}\<close>
  

  method vcg' = match [[vcg_defer_goals = true]] in _ \<Rightarrow> 
    vcg, 
    defer_slot_dest?,
    all \<open>(rule SOLVE_AUTO_DEFERI)?\<close>
    
  method vcg_step' = match [[vcg_defer_goals = true]] in _ \<Rightarrow> 
    defer_slot_ensure,
    vcg_step
  
  (* Static rule simplifier *)
  named_theorems vcg_static_rl_simps \<open>Rewrite rules to be applied to 
    framed rules, to prune trivial cases, etc.\<close>
  
  lemmas dflt_prune_thm_simps[vcg_static_rl_simps] = 
    triv_forall_equality  \<comment> \<open>prunes params\<close>
    True_implies_equals implies_True_equals  \<comment> \<open>prune \<open>True\<close> in asms\<close>
    False_implies_equals  \<comment> \<open>prune \<open>False\<close> in asms\<close>

    
  declaration \<open>K (Basic_VCG.add_static_xformer @{binding static_rule_simplifier} (
    fn ctxt => Simplifier.full_rewrite 
     (put_simpset HOL_basic_ss ctxt addsimps Named_Theorems.get ctxt @{named_theorems vcg_static_rl_simps})  
  ))\<close>
  
  (*
  named_theorems vcg_struct_simps \<open>Simplification rules on command structure\<close>
  *)
  
  
  declare conjI[vcg_decomp_rules]
  
      
end
