section \<open>Frame Inference\<close>
theory Sepref_Frame
imports Sepref_Basic Sepref_Constraints
begin
  text \<open> In this theory, we provide a specific frame inference tactic
    for Sepref.

    The first tactic, @{text frame_tac}, is a standard frame inference tactic, 
    based on the assumption that only @{const hn_ctxt}-assertions need to be
    matched.

    The second tactic, @{text merge_tac}, resolves entailments of the form
      @{text "F1 \<or>\<^sub>A F2 \<Longrightarrow>\<^sub>t ?F"}
    that occur during translation of if and case statements.
    It synthesizes a new frame ?F, where refinements of variables 
    with equal refinements in @{text F1} and @{text F2} are preserved,
    and the others are set to @{const hn_invalid}.
    \<close>


lemma recover_pure_aux: "CONSTRAINT is_pure R \<Longrightarrow> hn_invalid R x y \<turnstile> hn_ctxt R x y"
  by (auto simp: is_pure_conv invalid_pure_recover hn_ctxt_def)



lemma frame_thms:
  "P \<turnstile> P"
  "P\<turnstile>P' \<Longrightarrow> F\<turnstile>F' \<Longrightarrow> P**F \<turnstile> P'**F'"
  "CONSTRAINT is_pure R \<Longrightarrow> hn_invalid R x y \<turnstile> hn_ctxt R x y"
  "CONSTRAINT is_pure R \<Longrightarrow> hn_ctxt R x y \<turnstile> hn_val UNIV x y"
  apply -
  applyS simp
  applyS (rule conj_entails_mono; assumption)
  applyS (erule recover_pure_aux)
  applyS (simp, smt entails_def eq_UNIV_iff hn_ctxt_def is_pureE pred_lift_def pure_app_eq)
  done

named_theorems_rev sepref_frame_match_rules \<open>Sepref: Additional frame rules\<close>

text \<open>Rules to discharge unmatched stuff\<close>
(*lemma frame_rem_thms:
  "P \<Longrightarrow>\<^sub>t P"
  "P \<Longrightarrow>\<^sub>t emp"
  by sep_auto+
*)
lemma frame_rem1: "P\<turnstile>P" by simp

lemma frame_rem2: "F \<turnstile> F' \<Longrightarrow> hn_ctxt A x y ** F \<turnstile> hn_ctxt A x y ** F'"
  apply (rule conj_entails_mono) by auto

lemmas frame_rem_thms = frame_rem1 frame_rem2

named_theorems_rev sepref_frame_rem_rules
  \<open>Sepref: Additional rules to resolve remainder of frame-pairing\<close>


lemmas merge_thms = MERGE_END MERGE_STAR MERGE1_eq MERGE1_invalids
  
named_theorems sepref_frame_merge_rules \<open>Sepref: Additional merge rules\<close>

lemmas free_thms = mk_free_invalid mk_free_pure mk_free_pair
named_theorems_rev sepref_frame_free_rules \<open>Sepref: Additional free rules\<close>


text \<open>These rules are applied to recover pure values that have been destroyed by rule application\<close>

definition "RECOVER_PURE P Q \<equiv> P \<turnstile> Q"

lemma recover_pure:
  "RECOVER_PURE \<box> \<box>"
  "\<lbrakk>RECOVER_PURE P1 Q1; RECOVER_PURE P2 Q2\<rbrakk> \<Longrightarrow> RECOVER_PURE (P1**P2) (Q1**Q2)"
  "CONSTRAINT is_pure R \<Longrightarrow> RECOVER_PURE (hn_invalid R x y) (hn_ctxt R x y)"
  "RECOVER_PURE (hn_ctxt R x y) (hn_ctxt R x y)"
  unfolding RECOVER_PURE_def
  subgoal by auto
  subgoal by (drule (1) conj_entails_mono)
  subgoal by (rule recover_pure_aux)
  subgoal by auto
  done
  
lemma recover_pure_triv: 
  "RECOVER_PURE P P"
  unfolding RECOVER_PURE_def by auto


text \<open>Weakening the postcondition by converting @{const invalid_assn} to @{term "\<lambda>_ _. \<box>"}\<close>
definition "WEAKEN_HNR_POST \<Gamma> \<Gamma>' \<Gamma>'' \<equiv> (\<exists>h. \<Gamma> h) \<longrightarrow> (\<Gamma>'' \<turnstile> \<Gamma>')"

lemma weaken_hnr_postI:
  assumes "WEAKEN_HNR_POST \<Gamma> \<Gamma>'' \<Gamma>'"
  assumes "hn_refine \<Gamma> c \<Gamma>' R a"
  shows "hn_refine \<Gamma> c \<Gamma>'' R a"
  apply (rule hn_refine_preI)
  apply (rule hn_refine_cons_post)
  apply (rule assms)
  using assms(1) unfolding WEAKEN_HNR_POST_def by blast

lemma weaken_hnr_post_triv: "WEAKEN_HNR_POST \<Gamma> P P"
  unfolding WEAKEN_HNR_POST_def
  by auto

lemma weaken_hnr_post:
  "\<lbrakk>WEAKEN_HNR_POST \<Gamma> P P'; WEAKEN_HNR_POST \<Gamma>' Q Q'\<rbrakk> \<Longrightarrow> WEAKEN_HNR_POST (\<Gamma>**\<Gamma>') (P**Q) (P'**Q')"
  "WEAKEN_HNR_POST (hn_ctxt R x y) (hn_ctxt R x y) (hn_ctxt R x y)"
  "WEAKEN_HNR_POST (hn_ctxt R x y) (hn_invalid R x y) (hn_val UNIV x y)"
proof (goal_cases)
  case 1 thus ?case
    unfolding WEAKEN_HNR_POST_def
    apply clarsimp
    apply (rule conj_entails_mono) 
    apply (auto simp: sep_conj_def)
    done
next
  case 2 thus ?case by (rule weaken_hnr_post_triv)
next
  case 3 thus ?case 
    unfolding WEAKEN_HNR_POST_def 
    by (auto simp: invalid_assn_def hn_ctxt_def pure_def pure_partI)
qed



lemma reorder_enttI:
  assumes "A = C"
  assumes "B = D"
  shows "(A\<turnstile>B) \<equiv> (C\<turnstile>D)"
  apply (intro eq_reflection)
  by (simp add: assms)
  
  
(*
lemma merge_sat1: "(A\<or>\<^sub>AA' \<Longrightarrow>\<^sub>t Am) \<Longrightarrow> (A\<or>\<^sub>AAm \<Longrightarrow>\<^sub>t Am)"
  using entt_disjD1 entt_disjE by blast
lemma merge_sat2: "(A\<or>\<^sub>AA' \<Longrightarrow>\<^sub>t Am) \<Longrightarrow> (Am\<or>\<^sub>AA' \<Longrightarrow>\<^sub>t Am)"
  using entt_disjD2 entt_disjE by blast
*)


lemma merge_left_assn_cong: "L\<equiv>L' \<Longrightarrow> MERGE L frl R frr Q \<equiv> MERGE L' frl R frr Q" by simp
lemma merge_right_assn_cong: "R\<equiv>R' \<Longrightarrow> MERGE L frl R frr Q \<equiv> MERGE L frl R' frr Q" by simp

lemma MERGE_append_END: "MERGE L frl R frr Q \<equiv> MERGE (L**FRI_END) frl (R**FRI_END) frr Q"
  by (simp add: FRI_END_def)


ML {*
signature SEPREF_FRAME = sig


  (* Check if subgoal is a frame obligation *)
  (*val is_frame : term -> bool *)
  (* Check if subgoal is a merge obligation *)
  val is_merge: term -> bool
  (* Perform frame inference *)
  val frame_tac: (Proof.context -> tactic') -> Proof.context -> tactic'
  (* Perform merging *)
  val merge_tac: (Proof.context -> tactic') -> Proof.context -> tactic'

  (* Perform free synthesis *)
  val free_tac: (Proof.context -> tactic') -> Proof.context -> tactic'
  
  
  val frame_step_tac: (Proof.context -> tactic') -> bool -> Proof.context -> tactic'

  (* Reorder frame *)
  val prepare_frame_tac : Proof.context -> tactic'
  (* Solve a RECOVER_PURE goal, inserting constraints as necessary *)
  val recover_pure_tac: Proof.context -> tactic'

  (* Split precondition of hnr-goal into frame and arguments *)
  val align_goal_tac: Proof.context -> tactic'
  (* Normalize goal's precondition *)
  val norm_goal_pre_tac: Proof.context -> tactic'
  (* Rearrange precondition of hnr-term according to parameter order, normalize all relations *)
  val align_rl_conv: Proof.context -> conv

  (* Convert hn_invalid to hn_val UNIV in postcondition of hnr-goal. Makes proving the goal easier.*)
  val weaken_post_tac: Proof.context -> tactic'

  val add_normrel_eq : thm -> Context.generic -> Context.generic
  val del_normrel_eq : thm -> Context.generic -> Context.generic
  val get_normrel_eqs : Proof.context -> thm list

  val cfg_debug: bool Config.T

  val setup: theory -> theory
end


structure Sepref_Frame : SEPREF_FRAME = struct

  val cfg_debug = 
    Attrib.setup_config_bool @{binding sepref_debug_frame} (K false)

  val DCONVERSION = Sepref_Debugging.DBG_CONVERSION cfg_debug
  val dbg_msg_tac = Sepref_Debugging.dbg_msg_tac cfg_debug


  structure normrel_eqs = Named_Thms (
    val name = @{binding sepref_frame_normrel_eqs}
    val description = "Equations to normalize relations for frame matching"
  )

  val add_normrel_eq = normrel_eqs.add_thm
  val del_normrel_eq = normrel_eqs.del_thm
  val get_normrel_eqs = normrel_eqs.get

  (*val mk_entails = HOLogic.mk_binrel @{const_name "entails"}*)


  local
    open Sepref_Basic Refine_Util Conv
  
    fun assn_ord p = case apply2 dest_hn_ctxt_opt p of
        (NONE,NONE) => EQUAL
      | (SOME _, NONE) => LESS
      | (NONE, SOME _) => GREATER
      | (SOME (_,a,_), SOME (_,a',_)) => Term_Ord.fast_term_ord (a,a')

  in
    fun reorder_ctxt_conv ctxt ct = let
      val cert = Thm.cterm_of ctxt

      val new_ct = Thm.term_of ct 
        |> strip_star
        |> sort assn_ord
        |> list_star
        |> cert

      val thm = Goal.prove_internal ctxt [] (mk_cequals (ct,new_ct)) 
        (fn _ => VCG_Lib.simp_only_tac @{thms sep_conj_aci} ctxt 1)

    in
      thm
    end
  
    fun prepare_fi_conv ctxt ct = case Thm.term_of ct of
      @{mpat "?P \<turnstile> ?Q"} => let
        val cert = Thm.cterm_of ctxt
  
        (* Build table from abs-vars to ctxt *)
        val (Qm, Qum) = strip_star Q |> filter_out is_true |> List.partition is_hn_ctxt

        val Qtab = (
          Qm |> map (fn x => (#2 (dest_hn_ctxt x),(NONE,x))) 
          |> Termtab.make
        ) handle
            e as (Termtab.DUP _) => (
              tracing ("Dup heap: " ^ @{make_string} ct); raise e)
        
        (* Go over entries in P and try to find a partner *)
        val (Qtab,Pum) = fold (fn a => fn (Qtab,Pum) => 
          case dest_hn_ctxt_opt a of
            NONE => (Qtab,a::Pum)
          | SOME (_,p,_) => ( case Termtab.lookup Qtab p of
              SOME (NONE,tg) => (Termtab.update (p,(SOME a,tg)) Qtab, Pum)
            | _ => (Qtab,a::Pum)
            )
        ) (strip_star P) (Qtab,[])

        val Pum = filter_out is_true Pum

        (* Read out information from Qtab *)
        val (pairs,Qum2) = Termtab.dest Qtab |> map #2 
          |> List.partition (is_some o #1)
          |> apfst (map (apfst the))
          |> apsnd (map #2)
  
        (* Build reordered terms: P' = fst pairs * Pum, Q' = snd pairs * (Qum2*Qum) *)
        val P' = mk_star (list_star (map fst pairs), list_star Pum)
        val Q' = mk_star (list_star (map snd pairs), list_star (Qum2@Qum))
        
        val new_ct = mk_entails (P', Q') |> cert
  
        val msg_tac = dbg_msg_tac (Sepref_Debugging.msg_allgoals "Solving frame permutation") ctxt 1
        val tac = msg_tac THEN ALLGOALS (resolve_tac ctxt @{thms reorder_enttI}) THEN star_permute_tac ctxt

        val thm = Goal.prove_internal ctxt [] (mk_cequals (ct,new_ct)) (fn _ => tac)
  
      in 
        thm
      end
    | _ => no_conv ct
  
  end

  
  fun 
    is_merge @{mpat "Trueprop (MERGE _ _ _ _ _)"} = true 
  | is_merge @{mpat "Trueprop (MERGE1 _ _ _ _ _)"} = true 
  | is_merge _ = false

  fun is_frame @{mpat "Trueprop (_ \<turnstile> _)"} = true | is_frame _ = false

  fun is_free @{mpat "Trueprop (MK_FREE _ _)"} = true | is_free _ = false
    

    

  fun prepare_frame_tac ctxt = let
    open Refine_Util Conv
  in
    CONVERSION Thm.eta_conversion THEN'
    (*CONCL_COND' is_frame THEN'*)
    Frame_Infer.simp_ai_tac ctxt THEN'
    CONVERSION (HOL_concl_conv (fn _ => prepare_fi_conv ctxt) ctxt)
  end    


  fun mk_free_tac ctxt side_tac dbg = let
    val free_thms = @{thms free_thms} @
      Named_Theorems_Rev.get ctxt @{named_theorems_rev sepref_frame_free_rules} 
  in
    REPEAT' (resolve_tac ctxt free_thms THEN_ALL_NEW_FWD (
      CONCL_COND' is_free ORELSE' (if dbg then TRY_SOLVED' else SOLVED') side_tac  
    ))
  end
  
  local
    fun wrap_side_tac ctxt side_tac dbg tac = tac THEN_ALL_NEW_FWD (
      CASES' [
        (CONCL_COND' is_frame, all_tac),
        (CONCL_COND' is_merge, all_tac),
        (CONCL_COND' is_free, HEADGOAL ((if dbg then TRY_SOLVED' else SOLVED') (mk_free_tac ctxt side_tac dbg))),
        (K all_tac, HEADGOAL ((if dbg then TRY_SOLVED' else SOLVED') side_tac))
      ]
    )
  in  
    fun frame_step_tac side_tac dbg ctxt = let
      open Refine_Util Conv

      (* Constraint solving is built-in *)
      val side_tac = Sepref_Constraints.constraint_tac ctxt ORELSE' side_tac ctxt

      val frame_thms = @{thms frame_thms} @
        Named_Theorems_Rev.get ctxt @{named_theorems_rev sepref_frame_match_rules} 
      val merge_thms = @{thms merge_thms} @
        Named_Theorems.get ctxt @{named_theorems sepref_frame_merge_rules}
      val ss = put_simpset HOL_basic_ss ctxt addsimps normrel_eqs.get ctxt
      fun frame_thm_tac dbg = wrap_side_tac ctxt side_tac dbg (resolve_tac ctxt frame_thms)
      fun merge_thm_tac dbg = wrap_side_tac ctxt side_tac dbg (resolve_tac ctxt merge_thms)
  
      fun thm_tac dbg = CONCL_COND' is_merge THEN_ELSE' (merge_thm_tac dbg, frame_thm_tac dbg)
    in
      full_simp_tac ss THEN' thm_tac dbg
    end
  end  

  fun frame_loop_tac side_tac ctxt = let

  in
    TRY o (
      REPEAT_ALL_NEW (DETERM o frame_step_tac side_tac false ctxt)
    )
  end


  fun frame_tac side_tac ctxt = let
    open Refine_Util Conv
    val frame_rem_thms = @{thms frame_rem_thms}
      @ Named_Theorems_Rev.get ctxt @{named_theorems_rev sepref_frame_rem_rules}
    val solve_remainder_tac = TRY o REPEAT_ALL_NEW (DETERM o resolve_tac ctxt frame_rem_thms)
  in
    (prepare_frame_tac ctxt
      THEN' resolve_tac ctxt @{thms conj_entails_mono})
    THEN_ALL_NEW_LIST [
      frame_loop_tac side_tac ctxt,
      solve_remainder_tac
    ]  
  end

  fun merge_tac side_tac ctxt = let
    open Refine_Util Conv
    val reord_conv = Fri_Extract.cong_rl_conv (reorder_ctxt_conv ctxt) @{thm merge_left_assn_cong} 
           then_conv Fri_Extract.cong_rl_conv (reorder_ctxt_conv ctxt) @{thm merge_right_assn_cong}
           
    val merge_conv = 
      Frame_Infer.rewrite_a_conv ctxt
      then_conv reord_conv 
      then_conv Conv.rewr_conv @{thm MERGE_append_END}
      then_conv Frame_Infer.rewrite_a_conv ctxt
           
  in
    CONVERSION Thm.eta_conversion THEN'
    CONCL_COND' is_merge THEN'
    CONVERSION (HOL_concl_conv (fn _ => merge_conv) ctxt) THEN'
    frame_loop_tac side_tac ctxt
  end

  fun free_tac side_tac ctxt = 
    CONVERSION Thm.eta_conversion THEN'
    CONCL_COND' is_free THEN'
    mk_free_tac ctxt (side_tac ctxt) false
  
  val setup = normrel_eqs.setup

  local
    open Sepref_Basic
    fun is_invalid @{mpat "hn_invalid _ _ _ :: assn"} = true | is_invalid _ = false
    fun contains_invalid @{mpat "Trueprop (RECOVER_PURE ?Q _)"} = exists is_invalid (strip_star Q)
      | contains_invalid _ = false

  in
    fun recover_pure_tac ctxt = 
      CONCL_COND' contains_invalid THEN_ELSE' (
        REPEAT_ALL_NEW (DETERM o (resolve_tac ctxt @{thms recover_pure} ORELSE' Sepref_Constraints.constraint_tac ctxt)),
        resolve_tac ctxt @{thms recover_pure_triv}
      )
  end

  local
    open Sepref_Basic Refine_Util
    datatype cte = Other of term | Hn of term * term * term
    fun dest_ctxt_elem @{mpat "hn_ctxt ?R ?a ?c"} = Hn (R,a,c)
      | dest_ctxt_elem t = Other t

    fun mk_ctxt_elem (Other t) = t 
      | mk_ctxt_elem (Hn (R,a,c)) = @{mk_term "hn_ctxt ?R ?a ?c"}

    fun match x (Hn (_,y,_)) = x aconv y
      | match _ _ = false

    fun dest_with_frame (*ctxt*) _ t = let
      val (P,c,Q,R,a) = dest_hn_refine t
  
      val (_,(_,args)) = dest_hnr_absfun a
      val pre_ctes = strip_star P |> map dest_ctxt_elem

        
      val (pre_args,frame) = 
        (case split_matching match args pre_ctes of
            NONE => raise TERM("align_conv: Could not match all arguments",[P,a])
          | SOME x => x)

    in
      ((pre_args,frame),c,Q,R,a)
    end
  
    fun align_goal_conv_aux ctxt t = let
      val ((pre_args,frame),c,Q,R,a) = dest_with_frame ctxt t
      
      val P' = apply2 (list_star o map mk_ctxt_elem) (pre_args,frame) |> mk_star
      val t' = mk_hn_refine (P',c,Q,R,a)
    in t' end  

    fun align_rl_conv_aux ctxt t = let
      val ((pre_args,frame),c,Q,R,a) = dest_with_frame ctxt t

      val _ = frame = [] orelse raise TERM ("align_rl_conv: Extra preconditions in rule",[t,list_star (map mk_ctxt_elem frame)])

      val P' = list_star (map mk_ctxt_elem pre_args)
      val t' = mk_hn_refine (P',c,Q,R,a)
    in t' end  


    fun normrel_conv ctxt = let
      val ss = put_simpset HOL_basic_ss ctxt addsimps normrel_eqs.get ctxt
    in
      Simplifier.rewrite ss
    end

  in
    fun align_goal_conv ctxt = f_tac_conv ctxt (align_goal_conv_aux ctxt) (star_permute_tac ctxt)

    fun norm_goal_pre_conv ctxt = let
      open Conv
      val nr_conv = normrel_conv ctxt
    in
      HOL_concl_conv (fn _ => hn_refine_conv nr_conv all_conv all_conv all_conv all_conv) ctxt
    end  

    fun norm_goal_pre_tac ctxt = CONVERSION (norm_goal_pre_conv ctxt)

    fun align_rl_conv ctxt = let
      open Conv
      val nr_conv = normrel_conv ctxt
    in
      HOL_concl_conv (fn ctxt => f_tac_conv ctxt (align_rl_conv_aux ctxt) (star_permute_tac ctxt)) ctxt
      then_conv HOL_concl_conv (K (hn_refine_conv nr_conv all_conv nr_conv nr_conv all_conv)) ctxt
    end

    fun align_goal_tac ctxt = 
      CONCL_COND' is_hn_refine_concl 
      THEN' DCONVERSION ctxt (HOL_concl_conv align_goal_conv ctxt)
  end


  fun weaken_post_tac ctxt = TRADE (fn ctxt =>
    resolve_tac ctxt @{thms weaken_hnr_postI} 
    THEN' SOLVED' (REPEAT_ALL_NEW (DETERM o resolve_tac ctxt @{thms weaken_hnr_post weaken_hnr_post_triv}))
  ) ctxt

end
*}

setup Sepref_Frame.setup

method_setup weaken_hnr_post = \<open>Scan.succeed (fn ctxt => SIMPLE_METHOD' (Sepref_Frame.weaken_post_tac ctxt))\<close>
  \<open>Convert "hn_invalid" to "hn_ctxt (\<lambda>_ _. true)" in postcondition of hn_refine goal\<close>

lemma mod_starD: "(A**B) h \<Longrightarrow> (\<exists>h1 h2. A h1 \<and> B h2)" by (auto simp: sep_conj_def) 
  
(* TODO: Improper, modifies all h\<Turnstile>_ premises that happen to be there. Use tagging to protect! *)
method extract_hnr_invalids = (
  rule hn_refine_preI,
  ((determ \<open>drule mod_starD hn_invalidI | elim conjE exE\<close>)+)?
) \<comment> \<open>Extract \<open>hn_invalid _ _ _ = true\<close> preconditions from \<open>hn_refine\<close> goal.\<close>
  


lemmas [sepref_frame_normrel_eqs] = the_pure_pure pure_the_pure

end

