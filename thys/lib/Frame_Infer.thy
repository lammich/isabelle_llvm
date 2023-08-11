section \<open>Frame Inference\<close>
theory Frame_Infer
imports "Sep_Algebra_Add" Basic_VCG
begin

subsection \<open>Separation Algebra Specific Setup of VCG\<close>
lemmas [vcg_prep_ext_rules] = pure_part_split_conj  
  


subsection \<open>Entails Connective\<close>
definition "entails" :: "('a::sep_algebra \<Rightarrow> bool) \<Rightarrow> _ \<Rightarrow> _" (infix "\<turnstile>" 25) where "P \<turnstile> Q \<equiv> \<forall>s. P s \<longrightarrow> Q s"
lemma entails_refl[intro!,simp]: "P \<turnstile> P" by (simp add: entails_def)

lemma entails_false[simp, intro!]: "sep_false \<turnstile> Q" by (simp add: entails_def)
lemma entails_true[simp, intro!]: "P \<turnstile> sep_true" by (simp add: entails_def)

lemma entails_trans[trans]: "P \<turnstile> Q \<Longrightarrow> Q \<turnstile> R \<Longrightarrow> P \<turnstile> R" 
  by (simp add: entails_def)

lemma entails_mp: "\<lbrakk>Q \<turnstile> Q'; P \<turnstile> Q \<and>* F\<rbrakk> \<Longrightarrow> P \<turnstile> Q' \<and>* F"
  apply (clarsimp simp: entails_def)
  using sep_conj_impl1 by blast
  
lemma conj_entails_mono: "P\<turnstile>P' \<Longrightarrow> Q\<turnstile>Q' \<Longrightarrow> P**Q \<turnstile> P'**Q'"  
  apply (clarsimp simp: entails_def)
  using sep_conj_impl by blast  

lemma entails_exI: "P\<turnstile>Q x \<Longrightarrow> P\<turnstile>(EXS x. Q x)"  
  by (metis (mono_tags, lifting) entails_def)
  
lemma entails_pureI: "\<lbrakk>pure_part P \<Longrightarrow> P\<turnstile>Q\<rbrakk> \<Longrightarrow> P\<turnstile>Q"  
  by (auto simp: entails_def intro: pure_partI)

lemma entails_lift_extract_simps: 
  "(\<up>\<Phi> \<turnstile> Q) \<longleftrightarrow> (\<Phi> \<longrightarrow> \<box> \<turnstile> Q)"
  "(\<up>\<Phi>**P \<turnstile> Q) \<longleftrightarrow> (\<Phi> \<longrightarrow> P \<turnstile> Q)"
  unfolding entails_def 
  by (auto simp: sep_algebra_simps)

lemma entails_eq_iff: "A=B \<longleftrightarrow> (A\<turnstile>B) \<and> (B\<turnstile>A)"  
  unfolding entails_def by (auto)
  
lemma entails_eqI: "\<lbrakk> A\<turnstile>B; B\<turnstile>A \<rbrakk> \<Longrightarrow> A=B" by (simp add: entails_eq_iff)

  
  
  
definition "is_sep_red P' Q' P Q \<longleftrightarrow> (\<forall>Ps Qs. (P'**Ps\<turnstile>Q'**Qs) \<longrightarrow> (P**Ps\<turnstile>Q**Qs))"

lemma is_sep_redI: "\<lbrakk>\<And>Ps Qs. P'**Ps\<turnstile>Q'**Qs \<Longrightarrow> P**Ps\<turnstile>Q**Qs \<rbrakk> \<Longrightarrow> is_sep_red P' Q' P Q"
  unfolding is_sep_red_def by blast
  
lemma is_sep_redD: "\<lbrakk>is_sep_red P' Q' P Q; P'**Ps\<turnstile>Q'**Qs\<rbrakk> \<Longrightarrow> P**Ps\<turnstile>Q**Qs"
  unfolding is_sep_red_def by blast


  
    
  
subsection \<open>Tags for Frame Inference\<close>
definition "FRI_END \<equiv> \<box>"
definition "FRAME_INFER P Qs F \<equiv> P \<turnstile> Qs ** F"
lemmas fri_prems_cong = arg_cong[where f="\<lambda>P. FRAME_INFER P _ _"]
lemma fri_prems_cong_meta: "P\<equiv>P' \<Longrightarrow> FRAME_INFER P Q F \<equiv> FRAME_INFER P' Q F" by simp

lemmas fri_concls_cong = arg_cong[where f="\<lambda>P. FRAME_INFER _ P _"]

lemma fri_prepare: "FRAME_INFER Ps (Qs**FRI_END) F \<Longrightarrow> FRAME_INFER Ps Qs F"
  by (auto simp: FRI_END_def)

lemma fri_prepare_round: "FRAME_INFER (\<box>**Ps) Qs F \<Longrightarrow> FRAME_INFER Ps Qs F" 
  by simp
  
lemma fri_end: (* Potential premises get solved by entails_refl. *)
  "Ps \<turnstile> F \<Longrightarrow> FRAME_INFER Ps FRI_END F"
  by (auto simp: FRAME_INFER_def FRI_END_def)

lemma fri_drop_pure_prem: "\<up>P \<turnstile> \<box>" "Q \<turnstile> \<box> \<Longrightarrow> \<up>P ** Q \<turnstile> \<box>"
  by(cases P; auto simp: sep_algebra_simps)+

lemma fri_step_rl:  
  assumes "P \<turnstile> Q"  (* Gets instantiated with frame_infer_rules *)
  assumes "FRAME_INFER Ps Qs F"
  shows "FRAME_INFER (P**Ps) (Q**Qs) F"
  using assms
  unfolding FRAME_INFER_def
  by (simp add: conj_entails_mono)

lemma fri_reduce_rl:
  assumes "is_sep_red P' Q' P Q"
  assumes "FRAME_INFER (P'**Ps) (Q'**Qs) F"
  shows "FRAME_INFER (P**Ps) (Q**Qs) F"
  using assms unfolding FRAME_INFER_def 
  by (auto dest: is_sep_redD)
  
  
subsection \<open>Configurable Rule Sets\<close>   
(*named_theorems fri_prepare_simps*)

named_simpset fri_prepare_simps = HOL_basic_ss_nomatch
named_simpset fri_prepare_precond_simps = HOL_basic_ss_nomatch

named_theorems fri_rules
named_theorems fri_red_rules

lemma fri_empty_concl_simp: "(\<box> ** FRI_END) = FRI_END" by simp

lemmas [named_ss fri_prepare_simps] = sep_conj_assoc sep_conj_empty sep_conj_empty' sep_conj_exists
declare entails_refl[fri_rules]
  
lemma fri_move_sep_true_forward[named_ss fri_prepare_simps]:
  "(sep_true ** sep_true) = sep_true"  
  "(sep_true ** (sep_true**A)) = (sep_true ** A)"
  "NO_MATCH sep_true A \<Longrightarrow> (A ** sep_true) = (sep_true ** A)"
  "NO_MATCH sep_true A \<Longrightarrow> (A ** (sep_true ** B)) = (sep_true ** (A**B))"
  by (auto simp: sep_algebra_simps sep_conj_c)

lemma fri_prepare_sep_true_concl[named_ss fri_prepare_simps]: 
  "FRAME_INFER Ps (sep_true ** Q) \<box> = FRAME_INFER Ps Q sep_true"
  by (auto simp: FRAME_INFER_def sep_algebra_simps sep_conj_c)

lemma fri_exI: "FRAME_INFER Ps (Qs x) F \<Longrightarrow> FRAME_INFER Ps (EXS x. Qs x) F"
  by (auto simp: FRAME_INFER_def sep_algebra_simps intro: entails_exI) 

lemma fri_trueI: "FRAME_INFER Ps Qs sep_true \<Longrightarrow> FRAME_INFER (sep_true ** Ps) Qs sep_true"  
  apply (simp add: FRAME_INFER_def sep_algebra_simps)
  by (smt entails_mp entails_refl fri_move_sep_true_forward(2) sep.mult_commute)
  
lemma fri_pureI: "\<lbrakk>P \<Longrightarrow> FRAME_INFER A Q F\<rbrakk> \<Longrightarrow> FRAME_INFER (\<up>P ** A) Q F"  
  by (cases P) (auto simp: FRAME_INFER_def sep_algebra_simps)
  
lemmas [named_ss fri_prepare_precond_simps] = pred_lift_extract_simps
lemmas [named_ss fri_prepare_precond_simps cong] = fri_prems_cong


subsection \<open>ML Code\<close>


ML \<open>

  structure Frame_Infer = struct
    open VCG_Lib
    
    (**** Utilities *)
    
    val simp_ai_tac = simp_only_tac @{thms sep_conj_assoc sep_conj_empty sep_conj_empty'}
    val simp_a_tac = simp_only_tac @{thms sep_conj_assoc}
    
    val rewrite_a_conv = rewrite_only_conv @{thms sep_conj_assoc}
    val rewrite_ai_conv = rewrite_only_conv @{thms sep_conj_assoc sep_conj_empty sep_conj_empty'}
    

    (**** Rotation Tactic *)
    
    local  
      fun eq_rotate1_tac ctxt = CONVERSION (Refine_Util.HOL_concl_conv (
          fn ctxt => Conv.arg1_conv (
            Conv.rewr_conv @{thm sep_conj_commute[THEN eq_reflection]}
            then_conv Simplifier.rewrite (put_simpset HOL_basic_ss ctxt addsimps @{thms sep_conj_assoc})
          )) ctxt)
    
      fun eq_rotateN_tac ctxt n = WITH_concl (fn 
        @{mpat "Trueprop (?lhs = _)"} => let
          val nc = length (SepConj.break_sep_conj lhs)
          val n = n mod nc
          
          fun tc 0 = K all_tac
            | tc n = eq_rotate1_tac ctxt THEN' tc (n-1)
          
        in tc n end
      | _ => K no_tac  
      )
            
      (*    
      fun eq_rotateN_tac _ 0 = K all_tac      
        | eq_rotateN_tac ctxt n = eq_rotate1_tac ctxt THEN' eq_rotateN_tac ctxt (n-1)
      *)

    in      
      (* 
        Takes a congruence rule of the form a=b \<Longrightarrow> h a = h b,
        then expects a subgoal of the form h (a\<^sub>1**...**a\<^sub>n), and produces
        a sequence of new subgoals h (...) corresponding to all rotations of the a\<^sub>is.
      *)          
      fun rotations_tac cong_rls ctxt = let
        val cong_rls = map_filter (try (fn thm => @{thm iffD2} OF [thm])) cong_rls
      in   
        resolve_tac ctxt cong_rls
        THEN'
        WITH_concl (
          fn @{mpat \<open>Trueprop (?lhs = _)\<close>} => let 
              val n = length (SepConj.break_sep_conj lhs)
              fun tac n = eq_rotateN_tac ctxt n
              val tacs = map tac (0 upto n-1)
            in
              APPEND_LIST' tacs
            end 
          |  _ => K no_tac
        ) 
        THEN' 
        resolve_tac ctxt @{thms refl}
      end  
        
      fun rotate_tac cong_rls ctxt n = let
        val cong_rls = map_filter (try (fn thm => @{thm iffD2} OF [thm])) cong_rls
      in   
        resolve_tac ctxt cong_rls  
        THEN' eq_rotateN_tac ctxt n
        THEN' resolve_tac ctxt @{thms refl}
      end
        
    end 
        
    (**** Frame Inference Tactic *)
    fun start_tac ctxt = 
            asm_simp_named_tac ctxt @{named_simpset fri_prepare_simps}
      THEN' asm_simp_named_tac ctxt @{named_simpset fri_prepare_precond_simps}
      THEN' REPEAT' (resolve_tac ctxt @{thms fri_exI fri_trueI fri_pureI})
      THEN' resolve_tac ctxt @{thms fri_prepare}
      THEN' simp_only_tac @{thms sep_conj_assoc fri_empty_concl_simp} ctxt
  
    fun end_tac ctxt =   
      simp_ai_tac ctxt
      THEN' resolve_tac ctxt @{thms fri_end}
      THEN' (resolve_tac ctxt @{thms entails_refl entails_true} 
        ORELSE' SOLVED' (REPEAT_DETERM' (resolve_tac ctxt @{thms fri_drop_pure_prem})))
      
      
    fun start_round_tac ctxt =
      simp_ai_tac ctxt
      THEN' resolve_tac ctxt @{thms fri_prepare_round}
      THEN' simp_a_tac ctxt
  
    fun solve_round_thms ctxt = let  
      val thms1 = Named_Theorems.get ctxt @{named_theorems fri_rules}
        |> map (fn thm => @{thm fri_step_rl} OF [thm])

      val thms2 = Named_Theorems.get ctxt @{named_theorems fri_red_rules}
        |> map (fn thm => @{thm fri_reduce_rl} OF [thm])
    in thms1@thms2 end
      
    fun solve_round_tac ctxt = let
      val thms = solve_round_thms ctxt
    in
      Basic_VCG.step_precond_tac ctxt (resolve_tac ctxt thms)
    end 

    fun round_tac_aux ctxt = 
      start_round_tac ctxt
      THEN' rotations_tac @{thms fri_prems_cong} ctxt 
      THEN' solve_round_tac ctxt
      
    fun round_tac ctxt = 
      round_tac_aux ctxt 
      ORELSE' (CHANGED o asm_full_simp_tac ctxt ORELSE' round_tac_aux ctxt)
              
    fun infer_tac ctxt = start_tac ctxt THEN' REPEAT' (end_tac ctxt ORELSE' round_tac ctxt)
  
    (**** Debugging Tactics *)
    fun dbg_solve_round_tac ctxt = let
      val thms = solve_round_thms ctxt
    in
      Basic_VCG.step_precond_tac ctxt (resolve_tac ctxt thms)
      ORELSE' resolve_tac ctxt thms
    end 
      
    fun dbg_round_tac_aux ctxt = 
      start_round_tac ctxt
      THEN' rotations_tac @{thms fri_prems_cong} ctxt
      THEN' dbg_solve_round_tac ctxt

    fun dbg_round_tac ctxt = 
      dbg_round_tac_aux ctxt 
      ORELSE' (CHANGED o asm_full_simp_tac ctxt ORELSE' dbg_round_tac_aux ctxt)
             
  end      
\<close>

subsubsection \<open>Methods\<close>
definition "FRAME P Q F \<equiv> P \<turnstile> Q ** F"
definition "ENTAILS P Q \<equiv> P \<turnstile> Q"
lemma ENTAILSD: "ENTAILS P Q \<Longrightarrow> P \<turnstile> Q" by (simp add: ENTAILS_def)

lemma fri_startI: 
  "\<lbrakk>pure_part P \<Longrightarrow> FRAME_INFER P Q F\<rbrakk> \<Longrightarrow> FRAME P Q F" 
  "\<lbrakk>pure_part P \<Longrightarrow> FRAME_INFER P Q \<box>\<rbrakk> \<Longrightarrow> ENTAILS P Q"
  unfolding FRAME_INFER_def FRAME_def ENTAILS_def
  by (auto intro: entails_pureI)

lemma fri_startI_extended: 
  "\<lbrakk>pure_part P \<Longrightarrow> FRAME_INFER P Q F\<rbrakk> \<Longrightarrow> FRAME P Q F" 
  "\<lbrakk>pure_part P \<Longrightarrow> FRAME_INFER P Q \<box>\<rbrakk> \<Longrightarrow> ENTAILS P Q"
  "\<lbrakk>pure_part P \<Longrightarrow> FRAME_INFER P Q \<box>\<rbrakk> \<Longrightarrow> P \<turnstile> Q"
  unfolding FRAME_INFER_def FRAME_def ENTAILS_def
  by (auto intro: entails_pureI)
  
  
method_setup fri_rotations = 
  \<open>(Attrib.thms >> (fn cong_rls => fn ctxt => SIMPLE_METHOD' (Frame_Infer.rotations_tac cong_rls ctxt )))\<close>
  \<open>Generate sequence of rotations wrt. specified congruence rule\<close>

method_setup fri_rotate = 
  \<open>(Attrib.thms -- Scan.lift (Scan.optional (Parse.$$$ ":" |-- Parse.int) 1) >> 
    (fn (cong_rls,n) => fn ctxt => SIMPLE_METHOD' (Frame_Infer.rotate_tac cong_rls ctxt n)))\<close>
  \<open>Rotate left n steps wrt. specified congruence rule\<close>

  
method_setup fri_keep_aux = 
  \<open>(Scan.succeed (fn ctxt => SIMPLE_METHOD' (Frame_Infer.infer_tac ctxt)))\<close>
  \<open>Frame Inference, solve from left to right, as far as possible\<close>

method fri_keep = (rule fri_startI_extended)?; fri_keep_aux  
  
method fri = fri_keep;fail  


method_setup fri_dbg_step = 
  \<open>(Scan.succeed (fn ctxt => SIMPLE_METHOD' (Frame_Infer.dbg_round_tac ctxt)))\<close>
  \<open>Frame Inference, one round, keep unsolved goals\<close>
  
method_setup fri_dbg_end = 
  \<open>(Scan.succeed (fn ctxt => SIMPLE_METHOD' (Frame_Infer.end_tac ctxt)))\<close>
  \<open>Frame Inference, end inference\<close>
  
subsubsection \<open>Solver Setup\<close>  

  
declaration \<open>
  K (Basic_VCG.add_solver (@{thms fri_startI},@{binding infer_frame},Frame_Infer.infer_tac))
\<close>

method_setup fri_dbg_start = 
  \<open>(Scan.succeed (fn ctxt => SIMPLE_METHOD' (TRY o resolve_tac ctxt @{thms fri_startI_extended} THEN' Frame_Infer.start_tac ctxt)))\<close>
  \<open>Frame Inference, start\<close>
  
subsection \<open>Solving Pure Assertions\<close>

lemma fri_pure_rl[fri_rules]: "PRECOND (SOLVE_DEFAULT_AUTO \<Phi>) \<Longrightarrow> \<box>\<turnstile>\<up>\<Phi>" 
  by (auto simp: sep_algebra_simps vcg_tag_defs)

abbreviation pred_lift_ASM ("\<up>\<^sub>a_" [100] 100) where "\<up>\<^sub>a\<Phi> \<equiv> \<up>SOLVE_ASM \<Phi>"
abbreviation pred_lift_AUTO_DEFER ("\<up>\<^sub>d_" [100] 100) where "\<up>\<^sub>d\<Phi> \<equiv> \<up>SOLVE_AUTO_DEFER \<Phi>"
abbreviation pred_lift_AUTO ("\<up>\<^sub>!_" [100] 100) where "\<up>\<^sub>!\<Phi> \<equiv> \<up>SOLVE_AUTO \<Phi>"






subsection \<open>Extraction\<close>

text \<open>A transformer that applies a configurable set of simplification rules 
  only to certrain parts of the subgoal, as specified by a configurable set of
  congruence rules. Afterwards, VCG normalization is performed.
  
  The envisaged use of this transformer is to process the 
  postcondition of a Hoare-triple when it is transformed to the current symbolic state,
  extracting all pure content.
\<close>


named_theorems fri_extract_congs \<open>Congruence rules for extraction\<close>
named_theorems fri_extract_simps \<open>Simplification rules for extraction\<close>

lemmas fri_basic_extract_simps = pred_lift_move_merge_simps sep_conj_exists


definition EXTRACT :: "bool \<Rightarrow> bool" where [vcg_tag_defs]: "EXTRACT x \<equiv> x"
lemma 
  EXTRACTI: "x \<Longrightarrow> EXTRACT x" and
  EXTRACTD: "EXTRACT x \<Longrightarrow> x"
  by (auto simp: vcg_tag_defs)


lemma EXTRACT_True [simp, intro!]: "EXTRACT True" unfolding EXTRACT_def by simp


ML \<open>
  structure Fri_Extract = struct
    (* TODO: Move *)
    (* Conversion wrt. congruence rule. The rule must have the form a\<equiv>b \<Longrightarrow> c\<equiv>d. *)
    fun cong_rl_conv (conv:conv) rule ct = let
      val rule = Thm.incr_indexes (Thm.maxidx_of_cterm ct + 1) rule;
      val lhs = Thm.cprop_of rule |> Thm.dest_implies |> snd |> Thm.dest_equals_lhs;
      val rule = Thm.rename_boundvars (Thm.term_of lhs) (Thm.term_of ct) rule;
      val rule =
        Thm.instantiate (Thm.match (lhs, ct)) rule
          handle Pattern.MATCH => raise CTERM ("cong_rl_conv", [lhs, ct]);
      
      val lhs' = Thm.cprop_of rule |> Thm.dest_implies |> fst |> Thm.dest_equals_lhs;
          
    in rule OF [conv lhs'] end
    
    fun cong_rls_conv conv rules = 
      Conv.first_conv (map (cong_rl_conv conv) rules)

    fun extract_basic_tac ctxt thms = let
      val ctxt = Named_Simpsets.put @{named_simpset Main_ss} ctxt addsimps @{thms fri_basic_extract_simps} addsimps thms
      val cong_thms = Named_Theorems.get ctxt @{named_theorems fri_extract_congs}
    in
      CONVERSION (Conv.top_sweep_conv (fn ctxt => cong_rls_conv (Simplifier.rewrite ctxt) cong_thms) ctxt) 
    end
            
    fun extract_tac ctxt thms =
      extract_basic_tac ctxt (
          Named_Theorems.get ctxt @{named_theorems fri_extract_simps} 
        @ Named_Theorems.get ctxt @{named_theorems vcg_tag_defs} 
        @ thms
        )
          
  end
    
\<close>

declaration \<open>
  let
  in K (I 
  #> Basic_VCG.add_xformer (@{thms EXTRACTI},@{binding extract_xformer}, fn ctxt => 
        Fri_Extract.extract_tac ctxt []
        THEN' Basic_VCG.vcg_normalize_tac ctxt
      )
  ) end
\<close>

method_setup fri_extract_basic = \<open>Scan.lift (Args.mode "no_norm") -- Attrib.thms 
  >> (fn (no_norm,thms) => fn ctxt => SIMPLE_METHOD' ( 
    Fri_Extract.extract_basic_tac ctxt thms   
    THEN' (if no_norm then K all_tac else Basic_VCG.vcg_normalize_tac ctxt)
  ))\<close>
  \<open>Extraction of pure content, only basic rules\<close>

method_setup fri_extract = \<open>Scan.lift (Args.mode "no_norm") -- Attrib.thms 
  >> (fn (no_norm,thms) => fn ctxt => SIMPLE_METHOD' ( 
    Fri_Extract.extract_tac ctxt thms   
    THEN' (if no_norm then K all_tac else Basic_VCG.vcg_normalize_tac ctxt)
  ))\<close>
  \<open>Extraction of pure content\<close>

  
  
subsection \<open>Basic Methods\<close>  
  
lemma entails_pre_cong: "A=B \<Longrightarrow> (A\<turnstile>C) = (B\<turnstile>C)" by simp 
lemma entails_post_cong: "B=C \<Longrightarrow> (A\<turnstile>B) = (A\<turnstile>C)" by simp 
  
thm conj_entails_mono

lemma sep_drule:
  "A \<turnstile> B \<Longrightarrow> B \<turnstile> Q \<Longrightarrow> A \<turnstile> Q"
  "A \<turnstile> B \<Longrightarrow> B**F \<turnstile> Q \<Longrightarrow> A**F \<turnstile> Q"
  apply (rule entails_trans; assumption)
  using entails_mp entails_trans by blast

lemma sep_rule:
  "A \<turnstile> B \<Longrightarrow> P \<turnstile> A \<Longrightarrow> P \<turnstile> B"
  "A \<turnstile> B \<Longrightarrow> P \<turnstile> A**F \<Longrightarrow> P \<turnstile> B**F"
  apply (rule entails_trans; assumption)
  using entails_mp entails_trans by blast
  
(* TODO/FIXME: Frame inference does not work the right way round for backwards reasoning *)  
lemma sep_rule':
  assumes "Q\<^sub>1 \<turnstile> Q\<^sub>1'"
  assumes "FRAME_INFER Q Q\<^sub>1' F" (* ? *)
  assumes "P \<turnstile> Q\<^sub>1 ** F"
  shows "P \<turnstile> Q"  
  oops

    
  
lemma sep_drule':
  assumes "P\<^sub>1 \<turnstile> P\<^sub>1'"
  assumes "FRAME_INFER P P\<^sub>1 F"
  assumes "P\<^sub>1' ** F \<turnstile> Q"
  shows "P \<turnstile> Q"  
  using assms
  apply (auto simp: FRAME_INFER_def entails_def)
  using sep_conj_impl by blast
  
thm entails_trans  
  
method_setup sep_drule = \<open>Attrib.thms >> (fn thms => fn ctxt => SIMPLE_METHOD' (let
  val thms0 = map_filter (try (fn thm => @{thm entails_trans} OF [thm])) thms
  val thms = map_product (fn a => try (fn b => a OF [b])) @{thms sep_drule'} thms
    |> map_filter I
 in 
    resolve_tac ctxt thms0
  ORELSE'
    resolve_tac ctxt thms 
    THEN' SOLVED' (Frame_Infer.infer_tac ctxt)
 end))\<close>  
  
  
  
method_setup sep_drule_simple = \<open>Attrib.thms >> (fn thms => fn ctxt => SIMPLE_METHOD' (let
  val thms = map_product (fn a => try (fn b => a OF [b])) @{thms sep_drule} thms
    |> map_filter I
 in 
  Frame_Infer.rotations_tac @{thms entails_pre_cong} ctxt
  THEN' resolve_tac ctxt thms 
  THEN' Frame_Infer.simp_a_tac ctxt
 end))\<close>  
  
method_setup sep_rule = \<open>Attrib.thms >> (fn thms => fn ctxt => SIMPLE_METHOD' (let
  val thms = map_product (fn a => try (fn b => a OF [b])) @{thms sep_rule} thms
    |> map_filter I
 in 
  Frame_Infer.rotations_tac @{thms entails_post_cong} ctxt
  THEN' resolve_tac ctxt thms 
  THEN' Frame_Infer.simp_a_tac ctxt
 end))\<close>  
  
subsection \<open>Utilities\<close>  
  lemma fri_red_img_is: "PRECOND (SOLVE_AUTO (k\<in>I)) \<Longrightarrow> is_sep_red (\<Union>*i\<in>I-{k}. P i) \<box> (\<Union>*i\<in>I. P i) (P k)"
    unfolding vcg_tag_defs apply (rule is_sep_redI)
    by (auto simp: conj_entails_mono sep_set_img_remove)

  lemma fri_red_img_si: "PRECOND (SOLVE_AUTO (k\<in>I)) \<Longrightarrow> is_sep_red \<box> (\<Union>*i\<in>I-{k}. P i) (P k) (\<Union>*i\<in>I. P i)"
    unfolding vcg_tag_defs apply (rule is_sep_redI)
    by (smt conj_entails_mono entails_refl sep.add.left_neutral sep.mult.left_commute sep.mult_commute sep_set_img_remove)
        
  lemma fri_red_img_ss: "PRECOND (SOLVE_AUTO (I\<inter>I' \<noteq> {})) \<Longrightarrow> is_sep_red (\<Union>*i\<in>I-I'. P i) (\<Union>*i\<in>I'-I. P i) (\<Union>*i\<in>I. P i) (\<Union>*i\<in>I'. P i)"
    unfolding vcg_tag_defs apply (rule is_sep_redI)
  proof -
    fix Ps Qs
    assume "I \<inter> I' \<noteq> {}" 
    and A: "(\<Union>*i\<in>I - I'. P i) \<and>* Ps \<turnstile> (\<Union>*i\<in>I' - I. P i) \<and>* Qs"
    
    have DJ: "(I-I') \<inter> (I\<inter>I') = {}" "(I'-I) \<inter> (I\<inter>I') = {}" by auto
    have II: "(I-I') \<union> (I\<inter>I') = I" "(I'-I) \<union> (I\<inter>I') = I'"  by auto
    
    show "(\<Union>*i\<in>I. P i) \<and>* Ps \<turnstile> (\<Union>*i\<in>I'. P i) \<and>* Qs"
      unfolding sep_set_img_union[OF DJ(1), simplified II]
      unfolding sep_set_img_union[OF DJ(2), simplified II]
      by (smt A conj_entails_mono entails_def semigroup.assoc sep.mult.semigroup_axioms sep.mult_commute)
  qed

  lemmas fri_red_img = fri_red_img_is fri_red_img_si fri_red_img_ss
 
 
end
