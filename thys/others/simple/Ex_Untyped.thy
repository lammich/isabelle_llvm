theory Ex_Untyped
imports Monad2
begin

  typedecl global_state
  typedecl val

  datatype err = STATIC_ERROR

  datatype label_name = LABEL_NAME string
  datatype proc_name = PROC_NAME string
  datatype lvar_name = LVAR_NAME string


  datatype nt_instr =
    BASIC (resvar: lvar_name) "global_state \<Rightarrow> (val\<times>global_state)"
  | CALL (resvar: lvar_name) proc_name "lvar_name list"
  hide_const (open) resvar

  datatype t_instr =
    RETURN lvar_name
  | BR label_name
  | CBR lvar_name label_name label_name

  datatype basic_block = BBLOCK "nt_instr list" t_instr

  datatype procedure = PROC
    (params: "lvar_name list")
    (prologue: basic_block)
    (blocks: "(label_name\<times>basic_block) list")
  hide_const (open) params prologue blocks

  datatype program = PROG (procedures: "(proc_name \<times> procedure) list")
  hide_const (open) procedures


  locale program_loc =
    fixes \<pi> :: program
  begin
    definition "proc_map \<equiv> map_of (program.procedures \<pi>)"


  end

  locale procedure_loc = program_loc +
    fixes p :: procedure
  begin
    definition "block_map \<equiv> map_of (procedure.blocks p)"
  end


section \<open>Semantics\<close>

axiomatization val_to_bool :: "val \<Rightarrow> bool"

type_synonym local_state = "lvar_name \<rightharpoonup> val"
definition fresh_local_state :: local_state where "fresh_local_state \<equiv> Map.empty"

lemma fresh_local_state_empty[simp]:
  "fresh_local_state x = None"
  "dom fresh_local_state = {}"
  by (auto simp: fresh_local_state_def)

locale sem_program = program_loc +
  fixes execute_proc :: "proc_name \<times> val list \<Rightarrow> (val,unit,global_state,err) M"

locale sem_procedure = sem_program + procedure_loc


(* TODO: If we have lenses, use zoom fst\<^sub>L here! *)
definition define_lvar where
  "define_lvar name val \<equiv> doM {
    (l,g)\<leftarrow>get;
    fcheck STATIC_ERROR (name\<notin>dom l);
    let l = l(name\<mapsto>val);
    set (l,g)
  }"

definition get_lvar where
  "get_lvar name \<equiv> doM {
    (l,g)\<leftarrow>get;
    lookup STATIC_ERROR l name
  }"

definition "zoom_global m \<equiv> doM {
  (l,_)\<leftarrow>get;
  mblock (snd) (Pair l) m
}"


lemma zoom_global_alt: "zoom_global m = zoom (lift_lens STATIC_ERROR snd\<^sub>L) m"
  unfolding zoom_global_def zoom_def
  apply (rule M_eqI)
  by (auto simp: run_simps split: prod.splits mres.splits option.splits simp: mwp_def)


definition "noexcept m \<equiv> handle m (\<lambda>_. fail STATIC_ERROR)"

lemma noexcept_mono[partial_function_mono]: "\<And>x. M_mono (\<lambda>f. noexcept (f x))"
  unfolding noexcept_def by pf_mono_prover


context sem_procedure begin

  definition execute_nt_instr :: "nt_instr \<Rightarrow> (unit,val,local_state\<times>global_state,err) M"
    where "execute_nt_instr \<equiv> \<lambda>
      BASIC rvar f \<Rightarrow> doM {
        (l,g)\<leftarrow>get;
        let (r,g) = f g;
        set (l,g);
        define_lvar rvar r
      }
    | CALL rvar n args \<Rightarrow> doM {
        argvs \<leftarrow> mmap get_lvar args;
        r \<leftarrow> zoom_global (noexcept (execute_proc (n,argvs)));
        define_lvar rvar r
      }
    "

  definition execute_t_instr :: "t_instr \<Rightarrow> (label_name,val,local_state\<times>global_state,err) M"
    where "execute_t_instr \<equiv> \<lambda>
      RETURN v \<Rightarrow> doM { v\<leftarrow>get_lvar v; raise v }
    | BR label \<Rightarrow> doM { return label }
    | CBR cond iftrue iffalse \<Rightarrow> doM { v\<leftarrow>get_lvar cond; if val_to_bool v then return iftrue else return iffalse }
    "

  definition "execute_block \<equiv> \<lambda>BBLOCK ntis ti\<Rightarrow> doM {
    (* Execute nonterminal instructions *)
    mfold' execute_nt_instr ntis;
    (* Execute terminal instruction *)
    execute_t_instr ti
  }"

  definition "execute_block_reset block \<equiv> doM {
    (* Save local definitions *)
    (l,_)\<leftarrow>get;
    (* Execute block and obtain next label *)
    label \<leftarrow> execute_block block;
    (* Restore local definitions after block execution *)
    map_state (apfst (\<lambda>_. l));

    return label
  }"

  definition "execute args \<equiv> doM {
    fcheck STATIC_ERROR (length (procedure.params p) = length args);
    mblock (Pair fresh_local_state) (snd) (doM {
      (* Define Parameters*)
      mfold' (uncurry define_lvar) (zip (procedure.params p) args);

      handle (doM {
        (* Execute Prologue *)
        label \<leftarrow> execute_block (procedure.prologue p);

        (* Execute Blocks *)
        mwhile (\<lambda>_. return True) (\<lambda>label. doM {
          (* Lookup label *)
          block \<leftarrow> lookup STATIC_ERROR block_map label;
          execute_block_reset block
        }) label;

        fail STATIC_ERROR (* Unreachable *)
      }) (\<lambda>r. return r)
    })
  }"

end

context sem_program begin

  term "sem_procedure.execute execute_proc"

  definition execute_proc_body :: "proc_name \<times> val list \<Rightarrow> (val, unit, global_state, err) M"
    where
  "execute_proc_body \<equiv> \<lambda>(name,args). doM {
    proc \<leftarrow> lookup STATIC_ERROR proc_map name;
    sem_procedure.execute execute_proc proc args
  }"

end






context program_loc begin
  term "sem_program.execute_proc_body \<pi>"

  definition "execute_proc \<equiv> REC (sem_program.execute_proc_body \<pi>)"

  lemma proc_execute_mono[partial_function_mono]:
    "M_mono (\<lambda>fa. sem_procedure.execute fa p args)"
  proof -
    interpret sem_procedure \<pi> f p for f .

    show ?thesis
      unfolding execute_def execute_block_def execute_block_reset_def execute_nt_instr_def zoom_global_def
      by pf_mono_prover
  qed


  lemma execute_proc_body_mono[partial_function_mono]:
    "M.mono_body (\<lambda>fa. sem_program.execute_proc_body \<pi> fa x)"
    unfolding sem_program.execute_proc_body_def
    by pf_mono_prover



  lemmas execute_proc_unfold = REC_unfold[OF execute_proc_def, discharge_monos]
     and execute_proc_partial = lrmwpe_REC_partial[OF execute_proc_def, discharge_monos, consumes 1, case_names nterm step]
     and execute_proc_total = lrmwpe_REC_total[OF execute_proc_def, discharge_monos, consumes 1, case_names wf step]

end

term program_loc.execute_proc

lemma sim_zoom_global[sim_rules]: "sim m m' \<Longrightarrow> sim (zoom_global m) (zoom_global m')"
  by (auto simp: zoom_global_def intro!: sim_rules)

lemma sim_noexcept[sim_rules]: "sim m m' \<Longrightarrow> sim (noexcept m) (noexcept m')"
  by (auto intro!: sim_rules simp: noexcept_def)

locale prog_sim = \<pi>: program_loc \<pi> + \<pi>': program_loc \<pi>' for \<pi> \<pi>' +
  assumes proc_map_le: "\<pi>.proc_map \<subseteq>\<^sub>m \<pi>'.proc_map"
begin

  lemmas execute_proc_sim_aux = sim_REC[OF \<pi>.execute_proc_def \<pi>'.execute_proc_def, discharge_monos]

  lemma execute_block_sim[sim_rules]:
    "(\<And>x. sim (f x) (f' x)) \<Longrightarrow> sim (sem_procedure.execute_block f b) (sem_procedure.execute_block f' b)"
    by (auto
      intro!: sim_rules
      simp: sem_procedure.execute_block_def sem_procedure.execute_nt_instr_def
      split: basic_block.splits nt_instr.splits)

  lemma execute_proc_sim[sim_rules]:
    shows "sim (\<pi>.execute_proc (p,args)) (\<pi>'.execute_proc (p,args))"
    by (auto
      intro!: sim_rules execute_proc_sim_aux
      simp: sem_program.execute_proc_body_def sem_procedure.execute_def sem_procedure.execute_block_reset_def
      simp: proc_map_le
    )

end


context procedure_loc begin

  definition "wt_args args \<equiv> fcheck () (length args = length (procedure.params p))"

end

context program_loc begin

  definition wt_execute_proc :: "proc_name \<times> unit list \<Rightarrow> (unit, unit, unit, unit) M"
    where "wt_execute_proc \<equiv> \<lambda>(n,args). doM {
      p\<leftarrow>lookup () proc_map n;
      procedure_loc.wt_args p args
    }"

end

definition "wt_define_lvar name = doM {
  l\<leftarrow>get;
  fcheck () (name\<notin>l);
  let l = insert name l;
  set l
}"

definition wt_get_lvar where
  "wt_get_lvar name \<equiv> doM {
    l\<leftarrow>get;
    fcheck () (name\<in>l)
  }"


lemma lrmwp_define_lvar[THEN mwp_cons, intro!]:
  assumes "run (wt_define_lvar n) (dom l) = (SUCC () L')"
  shows "mwp (run (define_lvar n v) (l, g)) bot bot bot (\<lambda>_ (l',g'). g'=g \<and> l'=l(n\<mapsto>v) \<and> L'=insert n (dom l))"
  using assms
  by (auto
    simp: run_simps define_lvar_def wt_define_lvar_def
    split: if_splits
    )

lemma lrmwp_get_lvar[THEN mwp_cons, intro!]:
  assumes "run (wt_get_lvar n) (dom l) = SUCC () L'"
  shows "mwp (run (get_lvar n) (l, g)) bot bot bot (\<lambda>r lg'. lg'=(l,g) \<and> L'=dom l \<and> l n = Some r)"
  using assms
  by (auto
    simp: get_lvar_def wt_get_lvar_def run_simps
    split: if_splits option.splits
    )

definition "wt_zoom_global m \<equiv> doM {
  L\<leftarrow>get;
  mblock (\<lambda>_. ()) (\<lambda>_. L) m
}"


context procedure_loc begin

  abbreviation "params \<equiv> procedure.params p"
  abbreviation "prologue \<equiv> procedure.prologue p"
  abbreviation "blocks \<equiv> procedure.blocks p"





  fun wt_nt_instr where
    "wt_nt_instr (BASIC rvar f) = doM {
      wt_define_lvar rvar
    }"
  | "wt_nt_instr (CALL rvar n args) = doM {
      argvs \<leftarrow> mmap wt_get_lvar args;
      r \<leftarrow> wt_zoom_global (wt_execute_proc (n,argvs));
      wt_define_lvar rvar
    }"


  fun wt_t_instr where
    "wt_t_instr (RETURN v) = doM { wt_get_lvar v}"
  | "wt_t_instr (BR label) = doM { fcheck () (label\<in>dom block_map) }"
  | "wt_t_instr (CBR cond iftrue iffalse) = doM { wt_get_lvar cond; fcheck () ({iftrue,iffalse}\<subseteq>dom block_map) }"

  fun wt_block where
    "wt_block (BBLOCK ntis ti) = doM {
      mfold' wt_nt_instr ntis;
      wt_t_instr ti
    }"

  definition wt_blocks where
    "wt_blocks \<equiv> doM {
      l\<leftarrow>get;

      mmap (\<lambda>(_,block). doM {
        set l;
        wt_block block
      }) blocks;

      return ()
    }"

  definition wt_proc :: "(unit,unit,unit,unit) M" where "wt_proc \<equiv> doM {
    fcheck () (distinct (map fst blocks));

    mblock (\<lambda>_. {}) (\<lambda>_. ()) (doM {
      mfold' wt_define_lvar params;

      wt_block prologue;

      wt_blocks;

      return ()
    })
  }"

end


lemma mwp_eq_splitE:
  assumes "mwp m N F E S = r"
  obtains "m=NTERM" "N = r"
    | msg where "m = FAIL msg" "F msg = r"
    | e s where "m = EXC e s" "E e s = r"
    | x s where "m = SUCC x s" "S x s = r"
  using assms apply (cases m) by auto


context procedure_loc begin



  lemma lrmwp_wt_define_args[THEN mwp_cons, intro!]:
    fixes args :: "'a list"
    assumes "run (mfold' wt_define_lvar params) (dom l) = (SUCC () L')"
    assumes "length args = length params"
    shows "mwp (run (mfold' (uncurry define_lvar) (zip params args)) (l, g)) bot bot bot (\<lambda>_ (l',g'). L'=dom l' \<and> g'=g)"
  proof -
    {
      fix p and a :: "'a list"
      assume
          "length a = length p"
      and "run (mfold' wt_define_lvar p) (dom l) = (SUCC () L')"
      then have "mwp (run (mfold' (uncurry define_lvar) (zip p a)) (l, g)) bot bot bot (\<lambda>_ (l',g'). L'=dom l' \<and> g'=g)"
        apply (induction a p arbitrary: l g L' rule: list_induct2)
        apply (auto simp: run_simps elim!: mwp_eq_splitE)
        done
    }
    with assms show ?thesis by auto
  qed

end

lemma run_mmap_get_lvar[THEN mwp_cons]:
  assumes "run (mmap wt_get_lvar xs) (dom l) = (SUCC ys L')"
  shows "mwp (run (mmap get_lvar xs) (l, g)) bot bot bot (\<lambda>vs lg'. lg'=(l,g) \<and> L'=dom l \<and> length vs = length xs \<and> length ys = length xs)"
  using assms
proof (induction xs arbitrary: l g ys L')
  case Nil
  then show ?case by (auto simp: run_simps)
next
  case (Cons a xs)
  note IH = Cons.IH[THEN mwp_cons]
  from Cons.prems show ?case
    apply (auto simp: run_simps elim!: mwp_eq_splitE IH)
    done

qed


lemma run_noexcept[run_simps]:
  "run (noexcept m) s = mwp (run m s) NTERM (\<lambda>msg. FAIL msg) (\<lambda>_ _. FAIL STATIC_ERROR) (\<lambda>x s. SUCC x s)"
  by (auto simp: noexcept_def run_simps mwp_def split: mres.split)


lemma run_mmap_length_eq:
  assumes "run (mmap f xs) s = SUCC ys s'"
  shows "length ys = length xs"
  using assms apply (induction xs arbitrary: ys s)
  by (auto simp: run_simps elim!: mwp_eq_splitE)

lemma run_mmap_unit_state_idxD:
  assumes "run (mmap f xs) () = SUCC ys ()"
  assumes "i<length xs"
  shows "run (f (xs!i)) () = SUCC (ys!i) ()"
  using assms apply (induction xs arbitrary: i ys)
  by (auto simp: run_simps nth_Cons split: nat.splits elim!: mwp_eq_splitE)

lemma run_mmap_unit_state_elemD:
  assumes "run (mmap f xs) () = SUCC ys ()"
  assumes "x\<in>List.set xs"
  shows "\<exists>y\<in>List.set ys. run (f x) () = SUCC y ()"
  using assms
  by (auto simp: in_set_conv_nth Bex_def run_mmap_unit_state_idxD run_mmap_length_eq)

lemma run_mmap_idxD:
  assumes "run (mmap f xs) s = SUCC ys s'"
  assumes "i<length xs"
  shows "\<exists>s s'. run (f (xs!i)) s = SUCC (ys!i) s'"
  using assms apply (induction xs arbitrary: i ys s s')
  by (auto 0 5 simp: run_simps nth_Cons split: nat.splits elim!: mwp_eq_splitE)

lemma run_mmap_elemD:
  assumes "run (mmap f xs) s = SUCC ys s'"
  assumes "x\<in>List.set xs"
  shows "\<exists>s s'. \<exists>y\<in>List.set ys. run (f x) s = SUCC y s'"
  using assms
  by (auto simp: in_set_conv_nth Bex_def run_mmap_length_eq dest!: run_mmap_idxD)


(* TODO: Move *)
lemma mwp_map_state[simp]:
  "mwp (map_mres_state f m) N F E S = mwp m N F (\<lambda>e s. E e (f s)) (\<lambda>x s. S x (f s))"
  by (cases m) auto


context program_loc begin


  definition "wt_program \<equiv> doM {
    fcheck () (distinct (map fst (program.procedures \<pi>)));
    mmap (procedure_loc.wt_proc \<pi> o snd) (program.procedures \<pi>);
    return ()
  }"




  lemma
    assumes "(run (execute_proc (n,args)) s) = r"
    assumes "run (wt_execute_proc (n,argTs)) () = (SUCC () ())"
    assumes "length args = length argTs"
    assumes WTP: "run wt_program () = (SUCC () ())"
    shows "mwp r top bot bot top"
    using assms(1,2,3)
  proof (induction "(n,args)" s r arbitrary: n args argTs rule: execute_proc_partial)
    case (nterm x s)
    then show ?case by simp
  next
    case (step execute_proc_rec s r)

    note IH = step.hyps(1)[OF refl,THEN mwp_cons]


    interpret sem_program \<pi> execute_proc_rec .

    obtain p where PMN: "proc_map n = Some p"
      using step.prems unfolding wt_execute_proc_def
      by (auto simp: run_simps split: option.splits)

    interpret procedure_loc \<pi> p .
    interpret sem_procedure \<pi> execute_proc_rec p .

    from WTP PMN have WT_PROC: "run wt_proc () = (SUCC () ())"
      by (auto simp: wt_program_def proc_map_def run_simps
        split: if_splits
        dest!: run_mmap_unit_state_elemD
        elim!: mwp_eq_splitE)

    note PMN[simp]

    from step.prems have [simp]: "length args = length params"
      by (auto simp: wt_execute_proc_def run_simps  wt_args_def split: if_splits)

    have [THEN mwp_cons, elim!]:
      "mwp (run (execute_nt_instr i) (l, g)) top bot top (\<lambda>_ (l',g'). L'=dom l')"
      if "run (wt_nt_instr i) (dom l) = (SUCC () L')"
      for L' i l g
      using that
      by (fastforce
        simp:  run_simps execute_nt_instr_def zoom_global_alt wt_zoom_global_def
        elim!: IH mwp_eq_splitE run_mmap_get_lvar
        split: nt_instr.splits prod.splits option.splits)


    have [THEN mwp_cons, elim!]:
      "mwp (run (mfold' execute_nt_instr ins) (l, g)) top bot top (\<lambda>_ (l',g'). L'=dom l')"
      if "run (mfold' wt_nt_instr ins) (dom l) = (SUCC () L')"
      for L' ins l g
      using that
      apply (induction ins arbitrary: L' l g)
      by (auto simp: run_simps elim!: mwp_eq_splitE)

    have [THEN mwp_cons, elim!]:
      "mwp (run (execute_t_instr block) (l, g)) True bot top (\<lambda>label (l', g'). L' = dom l' \<and> label \<in> dom block_map)"
      if "run (wt_t_instr block) (dom l) = (SUCC () L')"
      for L' block l g
      using that
      by (auto
        simp: execute_t_instr_def run_simps
        elim!: mwp_eq_splitE
        split: t_instr.splits if_splits
      )


    have [THEN mwp_cons, elim!]:
      "mwp (run (execute_block block) (l, g)) top bot top (\<lambda>label (l',g'). L'=dom l' \<and> label\<in>dom block_map)"
      if "run (wt_block block) (dom l) = (SUCC () L')"
      for L' l g block
      using that
      by (auto
        simp: execute_block_def run_simps
        elim!: mwp_eq_splitE
        split: basic_block.splits)

    (*
    note EB_WRULE = lrmwpe_mwhile[where
          I="\<lambda>label (l,g). l=l\<^sub>0 \<and> label \<in> dom block_map"
      and s="(l\<^sub>0,g\<^sub>0)" for l\<^sub>0 g\<^sub>0
    ]*)

    have [THEN mwp_cons, intro!]:
      "mwp (run (execute_block_reset block) (l, g)) top bot top (\<lambda>label (l',g'). l'=l \<and> label\<in>dom block_map)"
      if "run wt_blocks (dom l) = (SUCC () L')"
      and "block_map label = Some block"
      for l block g label L'
    proof -
      from that(2) have "(label,block)\<in>list.set blocks"
        by (auto simp: block_map_def map_of_SomeD)
      with that(1) obtain L'' where "run (wt_block block) (dom l) = (SUCC () L'')"
        by (auto
          simp: wt_blocks_def run_simps
          split!: prod.splits
          elim!: mwp_eq_splitE
          dest!: run_mmap_elemD)
      with that(1) show ?thesis
        unfolding execute_block_reset_def
        by (auto elim!: simp: run_simps map_state_def)

    qed

    note EB_WRULE = mwhile_invar_rule[where
          I="\<lambda>label (l,g). l=l\<^sub>0 \<and> label \<in> dom block_map"
      and s="(l\<^sub>0,g\<^sub>0)" for l\<^sub>0 g\<^sub>0]

    note EB_WRULE = EB_WRULE[OF refl, where P="\<lambda>r. mwp r N F E S"  for N F E S, simplified]

    have "mwp (run (execute args) s) top bot bot top"
      using WT_PROC
      apply (auto
        simp: execute_def wt_proc_def run_simps
        split: if_splits prod.splits
        elim!: mwp_eq_splitE
        intro!: EB_WRULE
        )
      by simp_all

    with step.hyps(2) show ?case
      by (auto simp: execute_proc_body_def run_simps)

  qed


end

end

