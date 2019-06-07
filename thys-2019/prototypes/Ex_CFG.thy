theory Ex_CFG
imports "../lib/Monad"
begin
  text \<open>
    Small demonstrator for CFG semantics by "writing" an interpreter
    in a nontermination-error monad.
    
    Includes syntactic well-formedness check and proof that well-formed programs
    do not go wrong.
  \<close>



  datatype err = STATIC_ERROR








  type_synonym state = "string \<Rightarrow> int"
  type_synonym label = string
  type_synonym proc_name = string
  type_synonym val = "int"

  datatype nt_instr = I_BASIC "state \<Rightarrow> state" | I_CALL proc_name

  datatype t_instr = TI_RETURN | TI_BR label | TI_CBR "state\<Rightarrow>bool" label label

  datatype bblock = BBLOCK (nt_instrs: "nt_instr list") (t_instr: "t_instr")


  type_synonym proc_body = "label \<rightharpoonup> bblock"
  type_synonym prog = "proc_name \<rightharpoonup> proc_body"


  context
    fixes \<pi> :: prog
  begin

    context
      fixes execute :: "proc_body \<times> label \<Rightarrow> (unit,unit,state,err) M"
    begin

      definition "exec_nt_instr ins \<equiv> case ins of
        I_BASIC f \<Rightarrow> doM { s\<leftarrow>Monad.get; Monad.set (f s)}
      | I_CALL p \<Rightarrow> doM {
          \<beta> \<leftarrow> lookup STATIC_ERROR \<pi> p;
          handle (doM {execute (\<beta>,''__start''); fail STATIC_ERROR}) (\<lambda>_. return ());
          return ()
        }"

      fun exec_t_instr where
        "exec_t_instr (TI_RETURN) = doM {
          raise ()
        }"
      | "exec_t_instr (TI_BR l) = return l"
      | "exec_t_instr (TI_CBR c l1 l2) = doM {
          s\<leftarrow>Monad.get;
          if c s then return l1 else return l2
      }"

      definition "execute_body \<equiv> \<lambda>(\<beta>,l). doM {
        bb \<leftarrow> lookup STATIC_ERROR \<beta> l;
        mfold' exec_nt_instr (nt_instrs bb);
        l \<leftarrow> exec_t_instr (t_instr bb);
        execute (\<beta>,l)
      }"
    end

    definition "execute \<equiv> REC execute_body"

    lemma mono_mfold[partial_function_mono]:
      "\<lbrakk>\<And>x s. M.mono_body (\<lambda>f. F f x s)\<rbrakk> \<Longrightarrow> M.mono_body (\<lambda>f. mfold (F f) xs s)"
      apply (induction xs arbitrary: s)
      apply simp_all
      apply pf_mono_prover
      apply pf_mono_prover
      apply simp_all
      done

    lemma mono_exec_ntinstr[partial_function_mono]: "M.mono_body (\<lambda>f. local.exec_nt_instr f ins)"
      by (cases ins; simp add: exec_nt_instr_def; pf_mono_prover)

    lemma mono_execute_body[partial_function_mono]: "\<And>x. M.mono_body (\<lambda>fa. local.execute_body fa x)"
      unfolding execute_body_def
      by pf_mono_prover

  end

  lemmas
        execute_unfold[code] = REC_unfold[OF execute_def, discharge_monos]
    and execute_partial = lrmwpe_REC_partial[OF execute_def, discharge_monos, consumes 1, case_names nonterm step]
    and execute_total = lrmwpe_REC_total[OF execute_def, discharge_monos, consumes 1, case_names wf step]
    and execute_sim[sim_rules] = sim_REC[OF execute_def execute_def, discharge_monos]

  term execute

  thm sim_rules

  lemma execute_sm_sim[sim_rules]:
    assumes "\<pi> \<subseteq>\<^sub>m \<pi>'"
    shows "sim (execute \<pi> \<beta>l) (execute \<pi>' \<beta>l)"
    using assms
    by (auto intro!: sim_rules split!: nt_instr.split simp: execute_body_def exec_nt_instr_def)


  fun wf_nt_instr where
    "wf_nt_instr \<pi> (I_BASIC f) \<longleftrightarrow> True"
  | "wf_nt_instr \<pi> (I_CALL p) \<longleftrightarrow> p\<in>dom \<pi>"

  fun wf_t_instr where
    "wf_t_instr \<pi> \<beta> (TI_RETURN) \<longleftrightarrow> True"
  | "wf_t_instr \<pi> \<beta> (TI_BR l) \<longleftrightarrow> l\<in>dom \<beta>"
  | "wf_t_instr \<pi> \<beta> (TI_CBR c l1 l2) \<longleftrightarrow> l1\<in>dom \<beta> \<and> l2\<in>dom \<beta>"

  fun wf_basic_block where
    "wf_basic_block \<pi> \<beta> (BBLOCK ntis ti) \<longleftrightarrow> (\<forall>nti\<in>List.set ntis. wf_nt_instr \<pi> nti) \<and> wf_t_instr \<pi> \<beta> ti"

  definition "wf_proc_body \<pi> b \<equiv> ''__start''\<in>dom b \<and> (\<forall>bb\<in>ran b. wf_basic_block \<pi> b bb)"

  definition "wf_prog \<pi> \<equiv> \<forall>b\<in>ran \<pi>. wf_proc_body \<pi> b"

  definition "wf_pos \<pi> \<equiv> \<lambda>(\<beta>,l). \<beta> \<in> ran \<pi> \<and> l\<in>dom \<beta>"




  lemma
    assumes "run (execute \<pi> \<beta>l) s = r"
    assumes "wf_pos \<pi> \<beta>l"
    assumes "wf_prog \<pi>"
    shows "mwp r True bot top bot"
    using assms(1,2)
  proof (induction rule: execute_partial)
    case (nonterm x s)
    then show ?case by simp
  next
    case (step f x s r)

    note step.IH[OF refl, THEN mwp_cons, intro!]

    obtain \<beta> l where [simp]: "x = (\<beta>,l)" by (cases x)
    with \<open>wf_pos \<pi> x\<close> obtain ntis ti where [simp]: "\<beta> l = Some (BBLOCK ntis ti)" and "\<beta>\<in>ran \<pi>"
      apply (auto simp: wf_pos_def)
      using bblock.exhaust by blast

    have [THEN mwp_cons, intro!]:
      "mwp (run (exec_nt_instr \<pi> f i) s) top bot bot top" if "wf_nt_instr \<pi> i" for i s
      using that
      apply (auto simp: run_simps exec_nt_instr_def split: nt_instr.splits option.split)
      using assms(3)
      by (auto simp: wf_pos_def ranI wf_prog_def wf_proc_body_def)


    from \<open>wf_prog \<pi>\<close> \<open>\<beta>\<in>ran \<pi>\<close> have "wf_basic_block \<pi> \<beta> (BBLOCK ntis ti)"
      unfolding wf_prog_def wf_proc_body_def apply (auto)
      apply (meson \<open>\<beta> l = Some (BBLOCK ntis ti)\<close> ranI wf_basic_block.simps)
      apply (meson \<open>\<beta> l = Some (BBLOCK ntis ti)\<close> ranI wf_basic_block.simps)
      done
    hence WF_NTI: "(\<forall>nti\<in>List.set ntis. wf_nt_instr \<pi> nti)"
      and WF_TI: "wf_t_instr \<pi> \<beta> ti" by simp_all

    from WF_NTI have [THEN mwp_cons, intro!]:
      "mwp (run (mfold' (exec_nt_instr \<pi> f) ntis) s) top bot bot top"
      apply (induction ntis arbitrary: s)
      by (auto simp: run_simps)

    from WF_TI have [THEN mwp_cons, intro!]: "mwp (run (exec_t_instr ti) s) top bot top (\<lambda>l _. l\<in>dom \<beta>)" for s
      apply (cases ti)
      apply (auto simp: run_simps)
      done

    from step.hyps step.prems show ?case
      by (auto simp: execute_body_def run_simps wf_pos_def split: prod.splits option.splits)

  qed


end


