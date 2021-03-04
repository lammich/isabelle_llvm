(*
  Utility to defer subgoals into an isolated part of the proof state, 
  and recover them later.
*)
theory Defer_Slot
imports Basic_Imports
begin

definition "DEFER_SLOT (x::prop) \<equiv> x"
lemma DEFER_SLOT_cong[cong]: "PROP DEFER_SLOT x \<equiv> PROP DEFER_SLOT x" .

(* TODO: Find something better than True to put in empty slot! Perhaps "A\<Longrightarrow>A" *)
abbreviation "EMPTY_DEFER_SLOT \<equiv> PROP (DEFER_SLOT (Trueprop True))"
lemma insert_slot_rl1:
  assumes "PROP P \<Longrightarrow> PROP EMPTY_DEFER_SLOT \<Longrightarrow> PROP Q"
  shows "PROP (DEFER_SLOT (PROP P)) \<Longrightarrow> PROP Q"
  using assms unfolding DEFER_SLOT_def by simp

lemma insert_slot_rl2:
  assumes "PROP P \<Longrightarrow> PROP (DEFER_SLOT S) \<Longrightarrow> PROP Q"
  shows "PROP (DEFER_SLOT (PROP S &&& PROP P)) \<Longrightarrow> PROP Q"
  using assms unfolding DEFER_SLOT_def conjunction_def .

lemma remove_slot: "PROP (EMPTY_DEFER_SLOT)"
  unfolding DEFER_SLOT_def by (rule TrueI)

lemmas split_constraint_rls 
    = atomize_conj[symmetric] imp_conjunction all_conjunction conjunction_imp

ML \<open>
  signature DEFER_SLOT = sig
    (******** Defer Slot *)
    (* Tactic with slot subgoal *)
    val WITH_SLOT: tactic' -> tactic
    (* Process all goals in slot *)
    val ON_SLOT: tactic -> tactic
    (* Create slot as last subgoal. Fail if slot already present. *)
    val create_slot_tac: tactic
    (* Create slot if there isn't one already *)
    val ensure_slot_tac: tactic
    (* Remove empty slot *)
    val remove_slot_tac: tactic
    (* Move slot to first subgoal *)
    val prefer_slot_tac: tactic
    (* Destruct slot *)
    val dest_slot_tac: tactic'
    (* Check if goal state has slot *)
    val has_slot: thm -> bool
    (* Defer subgoal to slot *)
    val to_slot_tac: tactic'
    (* Print slot contents *)
    val print_slot_tac: Proof.context -> tactic

    (* Focus on goals in slot *)
    val focus: tactic
    (* Unfocus goals in slot *)
    val unfocus: tactic
    (* Unfocus goals, and insert them as first subgoals *)
    val unfocus_ins:tactic

    (* Focus on some goals in slot *)
    val cond_focus: (term -> bool) -> tactic
    (* Move some goals to slot *)
    val some_to_slot_tac: (term -> bool) -> tactic

  end


  structure Defer_Slot: DEFER_SLOT  = struct
    fun is_slot_goal @{mpat "DEFER_SLOT _"} = true | is_slot_goal _ = false

    fun slot_goal_num st = let
      val i = find_index is_slot_goal (Thm.prems_of st) + 1
    in
      i
    end

    fun has_slot st = slot_goal_num st > 0

    fun WITH_SLOT tac st = let
      val si = slot_goal_num st
    in
      if si>0 then tac si st else (
        if Thm.nprems_of st > 0 then warning "No defer slot" else (); 
        Seq.empty)
    end

    val to_slot_tac = IF_EXGOAL (fn i => WITH_SLOT (fn si => 
      if i<si then
        prefer_tac si THEN prefer_tac (i+1)
        THEN (
          PRIMITIVE (fn st => Drule.comp_no_flatten (st, 0) 1 @{thm insert_slot_rl1}) 
          ORELSE PRIMITIVE (fn st => Drule.comp_no_flatten (st, 0) 1 @{thm insert_slot_rl2})
        )
        THEN defer_tac 1
      else no_tac))

    val create_slot_tac = 
      COND (has_slot) no_tac
        (PRIMITIVE (Thm.implies_intr @{cterm "EMPTY_DEFER_SLOT"}) 
        THEN defer_tac 1)
        
    val ensure_slot_tac = TRY create_slot_tac
          
      
    val prefer_slot_tac = WITH_SLOT prefer_tac

    val dest_slot_tac = SELECT_GOAL (
      ALLGOALS (
        CONVERSION (Conv.rewr_conv @{thm DEFER_SLOT_def}) 
        THEN' Goal.conjunction_tac
        THEN' TRY o resolve0_tac @{thms TrueI})
      THEN distinct_subgoals_tac
    )

    val remove_slot_tac = WITH_SLOT (resolve0_tac @{thms remove_slot})

    val focus = WITH_SLOT (fn i => 
      PRIMITIVE (Goal.restrict i 1) 
      THEN ALLGOALS dest_slot_tac
      THEN create_slot_tac)

    val unfocus_ins = 
      PRIMITIVE (Goal.unrestrict 1)
      THEN WITH_SLOT defer_tac

    fun some_to_slot_tac cond = (ALLGOALS (COND' (fn t => is_slot_goal t orelse not (cond t)) ORELSE' to_slot_tac))

    val unfocus = 
      some_to_slot_tac (K true)
      THEN unfocus_ins

    fun cond_focus cond =
      focus 
      THEN some_to_slot_tac (not o cond)


    fun ON_SLOT tac = focus THEN tac THEN unfocus

    fun print_slot_tac ctxt = ON_SLOT (print_tac ctxt "SLOT:")


  end
\<close>

method_setup defer_slot_print = \<open>Scan.succeed (fn ctxt => SIMPLE_METHOD (Defer_Slot.print_slot_tac ctxt))\<close>
method_setup defer_slot_ensure = \<open>Scan.succeed (fn _ => SIMPLE_METHOD (Defer_Slot.ensure_slot_tac))\<close>
method_setup defer_slot_defer = \<open>Scan.succeed (fn _ => SIMPLE_METHOD' (Defer_Slot.to_slot_tac))\<close>
method_setup defer_slot_dest = \<open>Scan.succeed (fn _ => SIMPLE_METHOD' Defer_Slot.dest_slot_tac)\<close>
method_setup defer_slot_dest' = \<open>Scan.succeed (fn _ => SIMPLE_METHOD (Defer_Slot.prefer_slot_tac THEN FIRSTGOAL (Defer_Slot.dest_slot_tac)))\<close>



end
