theory Ex_Call
imports Monad2
begin



  datatype err = STATIC_ERROR

  type_synonym state = "string \<Rightarrow> int"

  datatype cmd =
      Basic "state \<Rightarrow> state"
    | Call "string option" string
    | Cond "state\<Rightarrow>bool" cmd cmd
    | Seq cmd cmd   (infixr ";;" 45)
    | Return "(state \<Rightarrow> int) option"

  abbreviation "static_check \<equiv> fcheck STATIC_ERROR"


  context
    fixes \<pi> :: "string \<rightharpoonup> (bool \<times> cmd)"
  begin
    definition "execute \<equiv> REC (\<lambda>execute cmd.
      case cmd of
        Basic f \<Rightarrow> doM { s\<leftarrow>get; set (f s) }
      | Return f \<Rightarrow> doM { s\<leftarrow>get; raise (map_option (\<lambda>f. f s) f) }
      | Call x n \<Rightarrow> doM {
          (rt,c) \<leftarrow> lookup STATIC_ERROR \<pi> n;
          r \<leftarrow> handle (doM {execute c; fail STATIC_ERROR}) (return);

          static_check (rt \<longleftrightarrow> r\<noteq>None); (* Procedure must match its return spec *)

          case (x,r) of
            (None,_) \<Rightarrow> return ()                (* Ignore result, if any *)
          | (Some _, None) \<Rightarrow> fail STATIC_ERROR  (* Void method expected to return result *)
          | (Some x, Some r) \<Rightarrow> doM {            (* Assign result *)
              s\<leftarrow>get; set (s(x:=r))
            }

        }
      | Cond b c1 c2 \<Rightarrow> doM {
          s\<leftarrow>get;
          if b s then
            execute c1
          else
            execute c2

        }
      | Seq c1 c2 \<Rightarrow> doM {
          execute c1;
          execute c2
        }
    )"

  end

  lemmas execute_code[code] = REC_unfold[OF execute_def, discharge_monos]
    and execute_unfold = REC_unfold[OF execute_def, discharge_monos]
    and execute_partial_rule = REC_partial_rule[OF execute_def, discharge_monos]
    and execute_total_rule = REC_total_rule[OF execute_def, discharge_monos]
    and execute_lrmwp_partial = lrmwpe_REC_partial[OF execute_def, discharge_monos, consumes 1, case_names nonterm step]
    and execute_lrmwp_total = lrmwpe_REC_total[OF execute_def, discharge_monos, consumes 1, case_names wf step]
    and execute_sim_rule[sim_rules] = sim_REC[OF execute_def execute_def, discharge_monos]

  lemma execute_sim:
    assumes "\<pi> \<subseteq>\<^sub>m \<pi>'"
    shows "sim (execute \<pi> c) (execute \<pi>' c)"
    by (auto split: cmd.split intro!: sim_rules assms)

  context
    fixes \<pi> :: "string \<rightharpoonup> (bool \<times> cmd)"
  begin
    fun wf_cmd where
      "wf_cmd nonvoid (Basic _) \<longleftrightarrow> True"
    | "wf_cmd nonvoid (Call r n) \<longleftrightarrow> (case \<pi> n of None \<Rightarrow> False | Some (rv,_) \<Rightarrow> r\<noteq>None \<longrightarrow> rv)"
    | "wf_cmd nonvoid (Seq c1 c2) \<longleftrightarrow> wf_cmd nonvoid c1 \<and> wf_cmd nonvoid c2"
    | "wf_cmd nonvoid (Cond _ c1 c2) \<longleftrightarrow> wf_cmd nonvoid c1 \<and> wf_cmd nonvoid c2"
    | "wf_cmd nonvoid (Return r) \<longleftrightarrow> nonvoid = (r\<noteq>None)"


    fun must_return where
      "must_return (Basic _) \<longleftrightarrow> False"
    | "must_return (Call _ _) \<longleftrightarrow> False"
    | "must_return (Seq c1 c2) \<longleftrightarrow> must_return c1 \<or> must_return c2"
    | "must_return (Cond _ c1 c2) \<longleftrightarrow> must_return c1 \<and> must_return c2"
    | "must_return (Return _) \<longleftrightarrow> True"

    fun wf_proc where
      "wf_proc (nonvoid, cmd) \<longleftrightarrow> must_return cmd \<and> wf_cmd nonvoid cmd"


  context
    assumes wf: "\<forall>p\<in>ran \<pi>. wf_proc p"
  begin

    lemma procE:
      assumes "\<pi> n = Some (nv,cmd)"
      obtains "must_return cmd" "wf_cmd nv cmd"
      using assms wf by (auto simp: ran_def)

    lemma
      assumes "run (execute \<pi> c) s = r"
      assumes "wf_cmd nonvoid c"
      shows "mwp r True bot (\<lambda>r _. nonvoid \<longleftrightarrow> r\<noteq>None) (\<lambda>_ _. \<not>must_return c)"
      using assms
    proof (induction arbitrary: nonvoid rule: execute_lrmwp_partial (*lrmwpe_REC_partial[OF execute_def, discharge_monos, consumes 1]*))
      case (nonterm x s)
      then show ?case by auto
    next
      case (step f x s r)
      note "step.IH"[OF refl, THEN mwp_cons, intro!]

      from "step.hyps" "step.prems" show ?case
        by (auto
          simp: run_simps
          elim: procE
          split: cmd.splits option.splits if_splits)

    qed
  end

end




definition "Assign x f \<equiv> Basic (\<lambda>s. (s(x:=f s)))"


fun peek_state where
  "peek_state vars NTERM = (NTERM, None)"
| "peek_state vars (FAIL f) = (FAIL f, None)"
| "peek_state vars (EXC e s) = (EXC e s, Some (map s vars))"
| "peek_state vars (SUCC r s) = (SUCC r s, Some (map s vars))"

value "peek_state [''x'',''y''] (run (execute (map_of [
  (''main'', (True, Assign ''x'' (\<lambda>s. s ''x'' + 42);; Return (Some (\<lambda>_. 41))))
]) (Call (Some ''y'') ''main'')) (\<lambda>_. 0))"


end
