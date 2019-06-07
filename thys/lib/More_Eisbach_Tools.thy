theory More_Eisbach_Tools
imports "HOL-Eisbach.Eisbach"
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
    
    
end
