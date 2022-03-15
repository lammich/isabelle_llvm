theory More_Eisbach_Tools
imports Automatic_Refinement.Refine_Util "HOL-Eisbach.Eisbach"
begin

section \<open>More Tracing\<close>

(* Copied from Eisbach_Tools *)
ML \<open>

val cfg_trace_level = Attrib.setup_config_int @{binding vcg_trace_level} (K 0)

local

fun trace_method parser print =
  Scan.lift (Parse.int) -- parser >>
    (fn (lvl,x) => fn ctxt => SIMPLE_METHOD (fn st =>
      (if not (Method.detect_closure_state st) andalso Config.get ctxt cfg_trace_level >= lvl
       then tracing (print ctxt x st) else ();
       all_tac st)));

    
val trace_goal_method = trace_method 
  (Scan.lift (Scan.optional Parse.text ""))
  (fn ctxt => fn msg => fn st => 
    let
      val t = Logic.get_goal (Thm.prop_of st) 1
    in
      Pretty.block [
        Pretty.str msg, Pretty.str ":", Pretty.brk 1, 
        Pretty.str (Syntax.string_of_term ctxt t)
      ]
      |> Pretty.string_of
    end
  )
    
val trace_msg_method = trace_method (Scan.lift Parse.text) (K (fn msg => K msg))
    
in

val _ =
  Theory.setup
   (  Method.setup @{binding vcg_trace_goal} trace_goal_method ""
   #> Method.setup @{binding vcg_trace_msg} trace_msg_method ""
   );

end
\<close>

(*
section \<open>Method Result Determinization\<close>
text \<open>The \<open>DETERM\<close> combinator on method level\<close>
method_setup determ = \<open>
  Method.text_closure >>
    (fn (text) => fn ctxt => fn using => fn st =>
      Seq.DETERM (Method.evaluate_runtime text ctxt using) st
    )
\<close>
*)

(*
section \<open>Combinators in Upcoming Isabelle (2018) Release\<close>

ML \<open>fun method_evaluate text ctxt facts =
  Method.NO_CONTEXT_TACTIC ctxt
    (Method.evaluate_runtime text ctxt facts)\<close>

method_setup all =
 \<open>Method.text_closure >> (fn m => fn ctxt => fn facts =>
   let
     fun tac i st' =
       Goal.restrict i 1 st'
       |> method_evaluate m ctxt facts
       |> Seq.map (Goal.unrestrict i)

   in SIMPLE_METHOD (ALLGOALS tac) facts end)
\<close>

method_setup determ =
 \<open>Method.text_closure >> (fn m => fn ctxt => fn facts =>
   let
     fun tac st' = method_evaluate m ctxt facts st'

   in SIMPLE_METHOD (DETERM tac) facts end)
\<close>

method_setup changed =
 \<open>Method.text_closure >> (fn m => fn ctxt => fn facts =>
   let
     fun tac st' = method_evaluate m ctxt facts st'

   in SIMPLE_METHOD (CHANGED tac) facts end)
\<close>
*)


subsection \<open>Deterministic Repeated Elimination Rule\<close>
text \<open>Attention: Slightly different semantics than @{method elim}: repeats the 
  rule as long as possible, but only on the first subgoal.\<close>
method_setup vcg_elim_determ = \<open>
  Attrib.thms >> (fn thms => fn ctxt => 
    SIMPLE_METHOD (REPEAT_DETERM1 (HEADGOAL (ematch_tac ctxt thms))))\<close>

    
subsection \<open>If-Then-Else\<close>    
(*
  TODO: Improve handling of seq. Currently, the first result is determinised

*)
method_setup then_else = \<open>let
in
  Method.text_closure -- Method.text_closure -- Method.text_closure >>
    (fn ((textb, textt), texte) => fn ctxt => fn using => fn st =>
      let
        val bmethod = Method.evaluate_runtime textb ctxt using;
        val tmethod = Method.evaluate_runtime textt ctxt using;
        val emethod = Method.evaluate_runtime texte ctxt using;
      in
        (case try (fn st => bmethod st |> Seq.pull) st of
          SOME (SOME (Seq.Result st,_)) => tmethod st
        | _ => emethod st)
      end)
end     
\<close>
    
method_setup solved_then_else = \<open>let
  infix 0 SOLVED_THEN_ELSE

  fun (tac1 SOLVED_THEN_ELSE (tac2,tac3)) st =
    tac1 st 
    |> Seq.maps (fn st' => 
         if Thm.nprems_of st' < Thm.nprems_of st then tac2 st' (* Solved goal *)
         else tac3 st' (* Did not solve goal *)
       )

in
  Method.text_closure -- Method.text_closure -- Method.text_closure >>
    (fn ((textb, textt), texte) => fn ctxt => fn using =>
      let
        val bmethod = method_evaluate textb ctxt [];
        val tmethod = method_evaluate textt ctxt [];
        val emethod = method_evaluate texte ctxt [];
      in
        SIMPLE_METHOD (bmethod SOLVED_THEN_ELSE (tmethod, emethod)) using
      end)
end     
\<close>



method_setup then_all_new_fwd =
 \<open>Method.text_closure -- Method.text_closure >> (fn (m1,m2) => fn ctxt => fn facts =>
   let
    val tac1 = method_evaluate m1 ctxt [] |> SELECT_GOAL 
    val tac2 = method_evaluate m2 ctxt [] |> SELECT_GOAL
   
   in SIMPLE_METHOD' (tac1 THEN_ALL_NEW_FWD tac2) facts end)
\<close>

method repeat_all_new_fwd methods m = (then_all_new_fwd \<open>m\<close> \<open>(repeat_all_new_fwd \<open>m\<close>)?\<close>)


method_setup focus_params_fixed =
 \<open>Method.text_closure >> (fn m1src => fn ctxt => fn facts =>
   let
      val m1 = Method.evaluate_runtime m1src ctxt []
      fun tac1 ctxt = NO_CONTEXT_TACTIC ctxt m1 
   
   in SIMPLE_METHOD' (Subgoal.FOCUS_PARAMS_FIXED (fn {context, ...} => tac1 context) ctxt) facts end)
\<close>



method_setup repeat =
 \<open>Scan.lift Parse.nat -- Method.text_closure >> (fn (n,m) => fn ctxt => fn facts =>
   let
     fun tac st' = method_evaluate m ctxt facts st'

   in SIMPLE_METHOD (REPEAT_DETERM_N n tac) facts end)
\<close>

method_setup repeat1 =
 \<open>Scan.lift Parse.nat -- Method.text_closure >> (fn (n,m) => fn ctxt => fn facts =>
   let
     fun tac st' = method_evaluate m ctxt facts st'

   in SIMPLE_METHOD (tac THEN REPEAT_DETERM_N (n-1) tac) facts end)
\<close>

method_setup parallel_all =
 \<open>Method.text_closure >> (fn m => fn ctxt => fn facts =>
   let
     fun tac st' = method_evaluate m ctxt facts st'

   in SIMPLE_METHOD (PARALLEL_GOALS tac) facts end)
\<close>

method_setup can =
 \<open>Method.text_closure >> (fn m => fn ctxt => fn facts =>
   let
    fun CAN tac st =
      case Seq.pull (tac st) of NONE => Seq.empty | _ => Seq.single st
      
     fun tac st' = method_evaluate m ctxt facts st'

   in SIMPLE_METHOD (CAN tac) facts end)
\<close>



method_setup seqs = \<open>
  let
    fun SEQS abort_tac [] = all_tac
      | SEQS abort_tac (m::ms) = m THEN_ELSE (SEQS abort_tac ms, abort_tac)
  in
    Method.text_closure --| Scan.lift @{keyword \<open>:\<close>} -- Scan.repeat1 Method.text_closure >> (fn (abm,ms) => fn ctxt => fn facts => let
      val abort_tac = method_evaluate abm ctxt facts
      val tacs = map (fn m => method_evaluate m ctxt facts) ms
    in
      SIMPLE_METHOD (SEQS abort_tac tacs) facts
    end)
  end
\<close> \<open>\<open>seqs abort m\<^sub>1 ... m\<^sub>n\<close>: Execute as many of the given methods. If one fails, execute abort\<close>


ML \<open>
  structure More_Eisbach_Basic = struct
    fun apply_method_noargs name ctxt =
      NO_CONTEXT_TACTIC ctxt (Method_Closure.apply_method ctxt name [] [] [] ctxt [])
      |> SELECT_GOAL;
  end
  
  open More_Eisbach_Basic
\<close>
    
end
