section \<open>Nterm-Fail-Exception-State Monad\<close>
theory Monad
imports
  Basic_Imports ELenses
begin



  section \<open>Additions to Partial Function\<close>
  context partial_function_definitions
  begin
    lemma monotoneI:
      "(\<And>x. mono_body (\<lambda>f. F f x)) \<Longrightarrow> monotone le_fun le_fun F"
      by (auto simp: monotone_def fun_ord_def)

    lemma fp_unfold:
      assumes "f \<equiv> fixp_fun F"
      assumes "(\<And>x. mono_body (\<lambda>f. F f x))"
      shows "f x = F f x"
      using assms mono_body_fixp[of F] by auto

  end

  lemma fun_ordD: "fun_ord le f g \<Longrightarrow> le (f x) (g x)"
    by (auto simp: fun_ord_def)

  lemma fun_ord_mono_alt: "monotone le (fun_ord le') f \<longleftrightarrow> (\<forall>x. monotone le le' (\<lambda>y. f y x))"
    by (metis (mono_tags, lifting) fun_ord_def monotone_def)



  method_setup pf_mono_prover = \<open>Scan.succeed (SIMPLE_METHOD' o Subgoal.FOCUS_PREMS (fn {context=ctxt,...} => CHANGED (ALLGOALS (Partial_Function.mono_tac ctxt))))\<close>

  ML \<open>
    fun discharge_monos ctxt thm = let
      fun aux ctxt thm = let
        val prems = Thm.prems_of thm

        fun prove_simple tac t ctxt = Goal.prove ctxt [] [] t (fn {context=ctxt, ...} => ALLGOALS (tac ctxt))


        (*val mono_tac = Subgoal.FOCUS (fn {context=ctxt,...} => CHANGED (ALLGOALS (Partial_Function.mono_tac ctxt)))*)
        fun mono_tac ctxt = CHANGED o (Partial_Function.mono_tac ctxt)

        fun cinst (t as @{mpat "\<And>_. monotone (fun_ord _) _ _"}) = the_default asm_rl (try (prove_simple mono_tac t) ctxt)
          | cinst _ = asm_rl

        val insts = map cinst prems

        val thm = thm OF insts
      in
        thm
      end
    in
      (* Avoid surprises with schematic variables being instantiated *)
      singleton (Variable.trade (map o aux) ctxt) thm
    end

  \<close>

  attribute_setup discharge_monos
    = \<open>Scan.succeed (Thm.rule_attribute [] (discharge_monos o Context.proof_of))\<close>
    \<open>Try to discharge monotonicity premises\<close>




  section \<open>Monad Definition\<close>

  subsection \<open>Inner Type\<close>
  datatype (discs_sels) ('a,'e,'s,'f) mres = NTERM | FAIL (the_failure: 'f) | EXC 'e (the_state: 's) | SUCC 'a (the_state: 's)
  datatype ('a,'e,'s,'f) M = M (run: "'s \<Rightarrow> ('a,'e,'s,'f) mres")

  abbreviation "map_mres_state f \<equiv> map_mres id id f id"
  abbreviation "map_mres_fail f \<equiv> map_mres id id id f"

  lemma map_mres_state_invert[simp]:
    (*"map_mres_state f m = NTERM \<longleftrightarrow> m = NTERM"*)
    "map_mres_state f m = FAIL msg \<longleftrightarrow> m = FAIL msg"
    "map_mres_state f m = EXC e s \<longleftrightarrow> (\<exists>ss. s=f ss \<and> m = EXC e ss)"
    "map_mres_state f m = SUCC x s \<longleftrightarrow> (\<exists>ss. s=f ss \<and> m = SUCC x ss)"
    by (cases m; auto; fail)+

  lemma map_mres_fail_invert[simp]:
    (*"map_mres_state f m = NTERM \<longleftrightarrow> m = NTERM"*)
    "map_mres_fail f m = FAIL msg \<longleftrightarrow> (\<exists>msg'. msg = f msg' \<and> m = FAIL msg')"
    "map_mres_fail f m = EXC e s \<longleftrightarrow> m = EXC e s"
    "map_mres_fail f m = SUCC x s \<longleftrightarrow> m = SUCC x s"
    by (cases m; auto; fail)+

  lemma M_eqI[intro?]: "\<lbrakk> \<And>s. run m s = run m' s \<rbrakk> \<Longrightarrow> m=m'"
    by (cases m; cases m'; auto)


  subsection \<open>Ordering Structure\<close>
  abbreviation "mres_ord \<equiv> flat_ord NTERM"
  abbreviation "mres_lub \<equiv> flat_lub NTERM"
  abbreviation "mres_mono \<equiv> monotone (fun_ord mres_ord) mres_ord"
  abbreviation "M_ord \<equiv> img_ord run (fun_ord mres_ord)"
  abbreviation "M_lub \<equiv> img_lub run M (fun_lub mres_lub)"
  abbreviation "M_mono \<equiv> monotone (fun_ord M_ord) M_ord"

  interpretation M:
    partial_function_definitions "M_ord" "M_lub"
    apply (intro partial_function_image partial_function_lift flat_interpretation)
    by (auto simp: M.expand)

  subsection \<open>Basic Combinators\<close>
  
  definition REC where "REC \<equiv> M.fixp_fun"
  definition internal_nterm where "internal_nterm \<equiv> M (\<lambda>_. NTERM)"
  definition fail where "fail msg \<equiv> M (\<lambda>_. FAIL msg)"
  definition return where "return x \<equiv> M (SUCC x)"
  definition bind where "bind m f \<equiv> M (\<lambda>s. case run m s of SUCC x s \<Rightarrow> run (f x) s | NTERM \<Rightarrow> NTERM | FAIL msg \<Rightarrow> FAIL msg | EXC e s \<Rightarrow> EXC e s)"
  definition get where "get \<equiv> M (\<lambda>s. SUCC s s)"
  definition set where "set s \<equiv> M (\<lambda>_. SUCC () s)"
  definition raise where "raise e \<equiv> M (EXC e)"
  definition handle where "handle m h \<equiv> M (\<lambda>s. case run m s of EXC e s \<Rightarrow> run (h e) s | SUCC x s \<Rightarrow> SUCC x s | NTERM \<Rightarrow> NTERM | FAIL msg \<Rightarrow> FAIL msg)"

  definition mblock where "mblock begin end m \<equiv> M (map_mres_state end o run m o begin)"
  definition mfail where "mfail f m \<equiv> M (map_mres_fail f o run m)"


  text \<open>Derived, but required for some laws.\<close>
  definition "map_state f \<equiv> bind get (set o f)"


  section \<open>Syntax\<close>
  
  abbreviation (do_notation) bind_doI where "bind_doI \<equiv> bind"
  abbreviation (do_notation) then_doI where "then_doI m f \<equiv> bind_doI m (\<lambda>_. f)"

  notation bind_doI (infixr "\<bind>" 54)

  notation then_doI (infixr "\<then>" 54)

  nonterminal doI_binds and doI_bind
  syntax
    "_doI_block" :: "doI_binds \<Rightarrow> 'a" ("doM {//(2  _)//}" [12] 62)
    "_doI_bind"  :: "[pttrn, 'a] \<Rightarrow> doI_bind" ("(2_ \<leftarrow>/ _)" 13)
    "_doI_let" :: "[pttrn, 'a] \<Rightarrow> doI_bind" ("(2let _ =/ _)" [1000, 13] 13)
    "_doI_then" :: "'a \<Rightarrow> doI_bind" ("_" [14] 13)
    "_doI_final" :: "'a \<Rightarrow> doI_binds" ("_")
    "_doI_cons" :: "[doI_bind, doI_binds] \<Rightarrow> doI_binds" ("_;//_" [13, 12] 12)
    (*"_thenM" :: "['a, 'b] \<Rightarrow> 'c" (infixr "\<then>" 54)*)

  syntax (ASCII)
    "_doI_bind" :: "[pttrn, 'a] \<Rightarrow> doI_bind" ("(2_ <-/ _)" 13)
    (*"_thenM" :: "['a, 'b] \<Rightarrow> 'c" (infixr ">>" 54)*)

  translations
    "_doI_block (_doI_cons (_doI_then t) (_doI_final e))"
      \<rightleftharpoons> "CONST then_doI t e"

    "_doI_block (_doI_cons (_doI_bind p t) (_doI_final e))"
      \<rightleftharpoons> "CONST bind_doI t (\<lambda>p. e)"

    "_doI_block (_doI_cons (_doI_let p t) bs)"
      \<rightleftharpoons> "let p = t in _doI_block bs"

    "_doI_block (_doI_cons b (_doI_cons c cs))"
      \<rightleftharpoons> "_doI_block (_doI_cons b (_doI_final (_doI_block (_doI_cons c cs))))"

    "_doI_cons (_doI_let p t) (_doI_final s)"
      \<rightleftharpoons> "_doI_final (let p = t in s)"

    "_doI_block (_doI_final e)" \<rightharpoonup> "e"

  section \<open>Monad Laws\<close>

  lemma map_state_laws[simp]:
    "map_state (\<lambda>x. x) = return ()"
    "map_state id = return ()"
    "map_state (\<lambda>_. c) = set c"
    unfolding return_def bind_def map_state_def get_def set_def
    by (auto split: mres.splits)



  lemma bind_laws[simp]:
    "bind m return = m"
    "bind (return x) f = f x"
    "bind (bind m (\<lambda>x. f x)) g = bind m (\<lambda>x. bind (f x) g)"
    "bind (fail msg) f = fail msg"
    "bind (internal_nterm) f = internal_nterm"
    "bind (raise e) f = raise e"
    unfolding bind_def return_def fail_def raise_def internal_nterm_def
    by (cases m; auto split: mres.split)+

  lemma handle_laws[simp]:
    "handle (return x) h = return x"
    "handle (fail msg) h = fail msg"
    "handle (internal_nterm) h = internal_nterm"
    "handle (raise e) h = h e"
    "handle m raise = m"
    "handle (handle m (\<lambda>e. h e)) i = handle m (\<lambda>e. handle (h e) i)"
    unfolding handle_def return_def fail_def raise_def internal_nterm_def
    by ((auto split: mres.split | (cases m; auto split: mres.split)) [])+

  lemma state_laws[simp]:
    "bind get set = return ()"
    "bind get (\<lambda>s. bind (set s) (f s)) = bind get (\<lambda>s. f s ())" (* From Lars Hupel's HOL-Library.State_Monad *)
    "bind (set s) (\<lambda>_. set s') = set s'"
    "bind get (\<lambda>_. m) = m"
    "bind (set s) (\<lambda>_. get) = bind (set s) (\<lambda>_. return s)"

    "handle get h = get"
    "handle (set s) h = set s"
    unfolding handle_def return_def bind_def get_def set_def
    by (auto)

  lemma mblock_laws[simp]:
    "mblock begin end (return x) = doM {map_state (end o begin); return x}"
    "mblock begin end (raise e) = doM {map_state (end o begin); raise e}"
    "mblock begin end (fail msg) = fail msg"
    "mblock begin end (internal_nterm) = internal_nterm"
    "mblock begin end (get) = doM { s\<leftarrow>get; map_state (end o begin); return (begin s) }"
    "mblock begin end (set s) = set (end s)"
    unfolding return_def fail_def raise_def mblock_def bind_def map_state_def get_def set_def internal_nterm_def
    by (auto split: mres.splits del: ext intro!: ext)

  lemma mfail_laws[simp]:
    "mfail f (return x) = return x"
    "mfail f (raise e) = raise e"
    "mfail f (fail msg) = fail (f msg)"
    "mfail f (internal_nterm) = internal_nterm"
    "mfail f (get) = get"
    "mfail f (set s) = set s"
    unfolding return_def fail_def raise_def mfail_def bind_def map_state_def get_def set_def internal_nterm_def
    by (auto split: mres.splits del: ext intro!: ext)

  lemma m_injects[simp]: 
    "return x = return x' \<longleftrightarrow> x=x'"
    "raise e = raise e' \<longleftrightarrow> e=e'"
    "fail msg = fail msg' \<longleftrightarrow> msg=msg'"
    unfolding return_def fail_def raise_def
    by (auto dest: fun_cong)
    
  
  section \<open>Recursion Setup\<close>

  subsection \<open>Fixed-Point Induction\<close>
  lemma M_admissible_aux:
    assumes "\<forall>x s. PQ x s NTERM"
    shows "M.admissible (\<lambda>f. \<forall>x s. PQ x s (run (f x) s))"
    apply (rule admissible_fun)
    apply unfold_locales
    apply (rule admissible_image)
    apply (rule partial_function_lift)
    apply (rule flat_interpretation)
    using assms
    apply (simp add: comp_def)
    apply (smt ccpo.admissibleI chain_fun flat_lub_in_chain fun_lub_def mem_Collect_eq)
    apply (auto simp: M.expand)
    done

  lemma M_lub_fun_empty[simp]: "M.lub_fun {} x = M (\<lambda>_. NTERM)"
    by (auto simp: img_lub_def fun_lub_def flat_lub_def)


  lemma REC_unfold:
    assumes DEF: "f \<equiv> REC F"
    assumes MONO: "\<And>x. M.mono_body (\<lambda>fa. F fa x)"
    shows "f = F f"
    by (metis DEF M.mono_body_fixp MONO REC_def)

  lemma REC_partial_rule:
    fixes PQ :: "'a \<Rightarrow> 'b \<Rightarrow> ('c, 'd, 'b,'f) mres \<Rightarrow> bool"
      and F :: "('a \<Rightarrow> ('c, 'd, 'b,'f) M) \<Rightarrow> 'a \<Rightarrow> ('c, 'd, 'b,'f) M"
    assumes "f \<equiv> REC F"
        and "\<And>x. M.mono_body (\<lambda>fa. F fa x)"
        and "\<And>x s. PQ x s NTERM"
        and "\<And>f x s. \<lbrakk>\<And>x' s'. PQ x' s' (run (f x') s')\<rbrakk> \<Longrightarrow> PQ x s (run (F f x) s)"
    shows "PQ x s (run (f x) s)"
    using ccpo.fixp_induct[OF M.ccpo M_admissible_aux M.monotoneI, simplified]
    using assms
    unfolding REC_def
    by blast

  declaration \<open>Partial_Function.init "ners" @{term M.fixp_fun}
    @{term M.mono_body} @{thm M.fixp_rule_uc} @{thm M.fixp_induct_uc}
    (NONE)\<close>


  subsection \<open>Well-Founded Induction\<close>
  lemma REC_total_rule:
    fixes PQ :: "'a \<Rightarrow> 'b \<Rightarrow> ('c, 'd, 'b,'f) mres \<Rightarrow> bool"
      and F :: "('a \<Rightarrow> ('c, 'd, 'b,'f) M) \<Rightarrow> 'a \<Rightarrow> ('c, 'd, 'b,'f) M"
    assumes DEF: "f \<equiv> REC F"
        and MONO: "\<And>x. M.mono_body (\<lambda>fa. F fa x)"
        and WF: "wf R"
        and STEP: "\<And>f x s. \<lbrakk>\<And>x' s'. ((x',s'),(x,s))\<in>R \<Longrightarrow> PQ x' s' (run (f x') s')\<rbrakk> \<Longrightarrow> PQ x s (run (F f x) s)"
    shows "PQ x s (run (f x) s)"
    using WF
    apply (induction "(x,s)" arbitrary: x s)
    by (metis DEF M.mono_body_fixp MONO REC_def STEP)


  subsection \<open>Monotonicity Reasoner Setup\<close>

  lemma M_bind_mono[partial_function_mono]:
    assumes mf: "M_mono B" and mg: "\<And>y. M_mono (\<lambda>f. C y f)"
    shows "M_mono (\<lambda>f. bind (B f) (\<lambda>y. C y f))"
    apply (rule monotoneI)
    using monotoneD[OF mf] monotoneD[OF mg]
    unfolding bind_def img_ord_def fun_ord_def
    apply (auto simp: flat_ord_def run_def split!: M.splits mres.splits)
    apply (smt M.collapse M.sel mres.distinct(1) run_def)
    apply (smt M.collapse M.sel mres.distinct(1) mres.inject(1) run_def)
    apply (smt M.collapse M.sel mres.distinct(1) mres.distinct(7) run_def)
    apply (smt M.collapse M.sel mres.distinct(1) mres.distinct(9) run_def)
    apply (smt M.collapse M.sel mres.distinct(3) run_def)
    apply (smt M.collapse M.sel mres.distinct(3) mres.distinct(7) run_def)
    apply (smt M.collapse M.sel mres.distinct(3) mres.inject(2) run_def)
    apply (smt M.collapse M.sel mres.distinct(3) mres.inject(2) run_def)
    apply (smt M.collapse M.sel mres.distinct(11) mres.distinct(3) run_def)
    apply (smt M.collapse M.sel mres.distinct(5) run_def)
    apply (smt M.collapse M.sel mres.distinct(5) mres.distinct(9) run_def)
    apply (smt M.collapse M.sel mres.distinct(11) mres.distinct(5) run_def)
    apply (smt M.collapse M.sel mres.distinct(5) mres.inject(3) run_def)
    done


  lemma M_handle_mono[partial_function_mono]:
    assumes mf: "M_mono B" and mg: "\<And>y. M_mono (\<lambda>f. C y f)"
    shows "M_mono (\<lambda>f. handle (B f) (\<lambda>y. C y f))"
    apply (rule monotoneI)
    using monotoneD[OF mf] monotoneD[OF mg]
    unfolding handle_def img_ord_def fun_ord_def
    apply (auto simp: flat_ord_def run_def split!: M.splits mres.splits)
    apply (smt M.collapse M.sel mres.distinct(1) run_def)
    apply (smt M.collapse M.sel mres.distinct(1) mres.inject(1) run_def)
    apply (smt M.collapse M.sel mres.distinct(1) mres.distinct(7) run_def)
    apply (smt M.collapse M.sel mres.distinct(1) mres.distinct(9) run_def)
    apply (smt M.collapse M.sel mres.distinct(3) run_def)
    apply (smt M.collapse M.sel mres.distinct(3) mres.distinct(7) run_def)
    apply (smt M.collapse M.sel mres.distinct(3) mres.inject(2) run_def)
    apply (smt M.collapse M.sel mres.distinct(11) mres.distinct(3) run_def)
    apply (smt M.collapse M.sel mres.distinct(5) run_def)
    apply (smt M.collapse M.sel mres.distinct(5) mres.distinct(9) run_def)
    apply (smt M.collapse M.sel mres.distinct(11) mres.distinct(5) run_def)
    apply (smt M.collapse M.sel mres.distinct(5) mres.inject(3) run_def)
    apply (smt M.collapse M.sel mres.distinct(5) mres.inject(3) run_def)
    done

  lemma mblock_mono[partial_function_mono]:
    assumes "M_mono (\<lambda>fa. m fa)"
    shows "M_mono (\<lambda>fa. mblock begin end (m fa))"
    apply (rule monotoneI)
    using monotoneD[OF assms]
    unfolding mblock_def
    unfolding flat_ord_def fun_ord_def img_ord_def
    by simp metis

  lemma mfail_mono[partial_function_mono]:
    assumes "M_mono (\<lambda>fa. m fa)"
    shows "M_mono (\<lambda>fa. mfail f (m fa))"
    apply (rule monotoneI)
    using monotoneD[OF assms]
    unfolding mfail_def
    unfolding flat_ord_def fun_ord_def img_ord_def
    by simp metis


  (*
    TODO: Make this proof generic, in partial_function_definitions or so.
  *)
  lemma REC_mono_aux:
    assumes MONO: "\<And>D. monotone M.le_fun M.le_fun (B D)"
    assumes 1: "monotone M.le_fun (fun_ord M.le_fun) B"
    shows "monotone M.le_fun M.le_fun (\<lambda>D. REC (B D))"
    unfolding REC_def
    apply (rule monotoneI)
    apply (rule ccpo.fixp_lowerbound[OF M.ccpo MONO])
    apply (subst (2) ccpo.fixp_unfold[OF M.ccpo MONO])
    supply R=fun_ordD[of M.le_fun "B x" "B y" for x y]
    apply (rule R)
    apply (rule monotoneD[OF 1])
    .

  lemma REC_mono[partial_function_mono]:
    assumes MONO: "\<And>D x. M.mono_body (\<lambda>E. B D E x)"
    assumes 1: "\<And>E x. M_mono (\<lambda>D. B D E x)"
    shows "M_mono (\<lambda>D. REC (B D) x)"
    using assms REC_mono_aux fun_ord_mono_alt by metis




section \<open>Reasoning Setup\<close>

  subsection \<open>Simplifier Based\<close>
  named_theorems run_simps

  definition "mwp m N F E S \<equiv> case_mres N F E S m"

  lemma mwp_simps[simp]:
    "mwp NTERM N F E S = N"
    "mwp (FAIL msg) N F E S = F msg"
    "mwp (EXC e s) N F E S = E e s"
    "mwp (SUCC x s) N F E S = S x s"
    by (auto simp: mwp_def)

  lemma mwp_cong[cong]: "m=m' \<Longrightarrow> mwp m N F E S = mwp m' N F E S" by simp

  lemma mwp_eq_cases:
    assumes "mwp m N F E S = r"
    assumes "m = NTERM \<Longrightarrow> r = N \<Longrightarrow> thesis"
    assumes "\<And>e. m = FAIL e \<Longrightarrow> r = F e \<Longrightarrow> thesis"
    assumes "\<And>e s. m = EXC e s \<Longrightarrow> r = E e s \<Longrightarrow> thesis"
    assumes "\<And>v s. m = SUCC v s \<Longrightarrow> r = S v s \<Longrightarrow> thesis"
    shows thesis
    using assms unfolding mwp_def by (auto split: mres.splits)

  lemma mwp_invert[simp]:
    "mwp (mwp m N F E S) N' F' E' S' =
      (mwp m
        (mwp N N' F' E' S')
        (\<lambda>x. mwp (F x) N' F' E' S')
        (\<lambda>e s. mwp (E e s) N' F' E' S')
        (\<lambda>x s. mwp (S x s) N' F' E' S')
      )"
    by (auto simp: mwp_def split: mres.splits)

  lemma mwp_eqI[intro!]:
    assumes "m=NTERM \<Longrightarrow> N=N'"
    assumes "\<And>f. m=FAIL f \<Longrightarrow> F f = F' f"
    assumes "\<And>e s. m=EXC e s \<Longrightarrow> E e s = E' e s"
    assumes "\<And>x s. m=SUCC x s \<Longrightarrow> S x s = S' x s"
    shows "mwp m N F E S = mwp m N' F' E' S'"
    using assms by (cases m) auto


  lemma mwp_cons:
    assumes "mwp r N' F' E' S'"
    assumes "N'\<Longrightarrow>N"
    assumes "\<And>msg. F' msg \<Longrightarrow> F msg"
    assumes "\<And>e s. E' e s \<Longrightarrow> E e s"
    assumes "\<And>x s. S' x s \<Longrightarrow> S x s"
    shows "mwp r N F E S"
    using assms by (auto simp: mwp_def split: mres.split)

  lemma mwp_map_mres_state[simp]: "mwp (map_mres_state f s) N F E S = mwp s N F (\<lambda>e s. E e (f s)) (\<lambda>r s. S r (f s))"
    by (cases s) auto

  lemma mwp_triv[simp]: 
    "mwp m top top top top"
    "mwp m True (\<lambda>_. True) (\<lambda>_ _. True) (\<lambda>_ _. True)"
    by (cases m; auto; fail)+
  
  lemma mwp_trivI: "\<lbrakk>N; \<And>f. F f; \<And>e s. E e s; \<And>x s. S x s \<rbrakk> \<Longrightarrow> mwp m N F E S"
    by (cases m; auto)
    
    
    
  lemma flip_run_eq[simp]:
    "SUCC r s' = run c s \<longleftrightarrow> run c s = SUCC r s'" 
    "EXC e s' = run c s \<longleftrightarrow> run c s = EXC e s'" 
    by auto

  lemma flip_mwp_eq[simp]:
    "SUCC r s' = mwp m N F E S \<longleftrightarrow> mwp m N F E S = SUCC r s'" 
    "EXC e s' = mwp m N F E S \<longleftrightarrow> mwp m N F E S = EXC e s'" 
    by auto

  lemma basic_run_simps[run_simps]:
    "\<And>s. run (return x) s = SUCC x s"
    "\<And>s. run (fail msg) s = FAIL msg"
    "\<And>s. run (internal_nterm) s = NTERM"
    "\<And>s. run (raise e) s = EXC e s"
    "\<And>s. run (get) s = SUCC s s"
    "\<And>s. run (set s') s = SUCC () s'"
    by (auto simp: return_def fail_def raise_def get_def set_def internal_nterm_def)

  lemma run_Let[run_simps]: "run (let x=v in f x) s = run (f v) s" by auto

  lemma run_bind[run_simps]: "run (bind m f) s
    = (mwp (run m s) NTERM (\<lambda>x. FAIL x) (\<lambda>e s. EXC e s) (\<lambda>x s. run (f x) s))"
    unfolding bind_def mwp_def by simp

  lemma run_handle[run_simps]: "run (handle m h) s
    = (mwp (run m s) NTERM (\<lambda>msg. FAIL msg) (\<lambda>e s. run (h e) s) (\<lambda>x s. SUCC x s))"
    unfolding handle_def mwp_def by simp

  lemma run_mblock[run_simps]: "run (mblock b e m) s = map_mres_state e (run m (b s))"
    unfolding mblock_def by simp

  lemma run_mfail[run_simps]: "run (mfail f m) s = map_mres_fail f (run m s)"
    unfolding mfail_def by simp

  lemma run_map_state[run_simps]: "run (map_state f) s = SUCC () (f s)"
    unfolding map_state_def
    by (simp add: run_simps)

  lemma lrmwpe_REC_partial:
    assumes "f \<equiv> REC F"
        and "run (f x) s = r"
        and "\<And>x. M.mono_body (\<lambda>fa. F fa x)"
        and "\<And>x s. P x s NTERM"
        and "\<And>f x s r. \<lbrakk>\<And>x' s' r'. run (f x') s' = r' \<Longrightarrow> P x' s' r'; run (F f x) s = r \<rbrakk> \<Longrightarrow> P x s r"
    shows "P x s r"
  proof -
    note A = assms
    show ?thesis
      apply (rule REC_partial_rule[OF A(1,3), where PQ=P, of x s, unfolded A(2)])
      apply fact
      by (rule A(5)) auto
  qed

  lemma lrmwpe_REC_total:
    assumes "f \<equiv> REC F"
        and "run (f x) s = r"
        and "\<And>x. M.mono_body (\<lambda>fa. F fa x)"
        and "wf R"
        and "\<And>f x s r. \<lbrakk>\<And>x' s' r'. \<lbrakk>run (f x') s' = r'; ((x',s'), (x,s))\<in>R\<rbrakk> \<Longrightarrow> P x' s' r'; run (F f x) s = r \<rbrakk> \<Longrightarrow> P x s r"
    shows "P x s r"
  proof -
    note A = assms
    show ?thesis
      apply (rule REC_total_rule[OF A(1,3,4), where PQ=P, of x s, unfolded A(2)])
      by (rule A(5)) auto
  qed


  lemma mwp_inductI:
    assumes "\<And>r. run m s = r \<Longrightarrow> mwp r N F E S"
    shows "mwp (run m s) N F E S"
    using assms by auto

  subsection \<open>Simulation\<close>


  definition "sim m m' \<equiv> \<forall>s. mwp (run m s) top top (\<lambda>e s'. run m' s = EXC e s') (\<lambda>x s'. run m' s = SUCC x s')"

  named_theorems sim_rules


  lemma sim_refl[intro!,simp]: "sim m m"
    unfolding sim_def mwp_def by (auto split: mres.split)

  lemma sim_fail[sim_rules]: "sim (fail msg) m'"
    unfolding sim_def fail_def by auto

  lemma sim_internal_nterm[sim_rules]: "sim (internal_nterm) m'"
    unfolding sim_def internal_nterm_def by auto

  lemma sim_return[sim_rules]: "x=x' \<Longrightarrow> sim (return x) (return x')"
    by (auto simp: sim_def run_simps)

  lemma sim_get[sim_rules]: "sim get get"
    by (auto simp: sim_def run_simps)

  lemma sim_set[sim_rules]: "s=s' \<Longrightarrow> sim (set s) (set s')"
    by (auto simp: sim_def run_simps)


  lemma sim_REC:
    assumes DEF: "f \<equiv> REC F"
    assumes DEF': "f' \<equiv> REC F'"
    assumes MONO: "\<And>x. M.mono_body (\<lambda>f. F f x)" "\<And>x. M.mono_body (\<lambda>f. F' f x)"
    assumes SIM: "\<And>f f' x. (\<And>x. sim (f x) (f' x)) \<Longrightarrow> sim (F f x) (F' f' x)"
    shows "sim (f x) (f' x)"
    unfolding sim_def apply clarify
  proof (rule mwp_inductI)
    fix s r
    assume "run (f x) s = r"
    then show "mwp r top top (\<lambda>e s'. run (f' x) s = EXC e s') (\<lambda>xa s'. run (f' x) s = SUCC xa s')"
    proof (induction rule: lrmwpe_REC_partial[OF DEF _ MONO(1), consumes 1, case_names nterm step])
      case (nterm x s)
      then show ?case by simp
    next
      case (step f x s r)
      then show ?case
        apply (clarsimp)
        apply (subst REC_unfold[OF DEF' MONO(2)])
        apply (subst (2) REC_unfold[OF DEF' MONO(2)])
        using SIM[of f f' x]
        apply (auto simp: sim_def)
        done
    qed
  qed

  lemma sim_bind[sim_rules]:
    assumes "sim m m'" assumes "\<And>x. sim (f x) (f' x)"
    shows "sim (bind m f) (bind m' f')"
    using assms
    unfolding sim_def
    by (fastforce simp: run_simps mwp_def split: mres.splits)

  lemma sim_handle[sim_rules]:
    assumes "sim m m'" assumes "\<And>x. sim (h x) (h' x)"
    shows "sim (handle m h) (handle m' h')"
    using assms
    unfolding sim_def
    by (fastforce simp: run_simps mwp_def split: mres.splits)

  lemma sim_mblock[sim_rules]:
    "sim m m' \<Longrightarrow> sim (mblock begin end m) (mblock begin end m')"
    unfolding sim_def
    by (auto simp: run_simps mwp_def split: mres.splits)

  lemma sim_mfail[sim_rules]:
    "sim m m' \<Longrightarrow> sim (mfail fm m) (mfail fm m')"
    unfolding sim_def
    by (auto simp: run_simps mwp_def split: mres.splits)

section \<open>Integration of Lenses\<close>

subsection \<open>Monadic mblock\<close>
definition "mmblock begin end m \<equiv> doM {
  s' \<leftarrow> begin;
  s \<leftarrow> get;
  (x,s') \<leftarrow> handle (
    mblock (\<lambda>_. s') (\<lambda>_. s) (
      handle
        (doM { x\<leftarrow>m; s'\<leftarrow>get; return (x,s') })
        (\<lambda>e. doM { s'\<leftarrow>get; raise (e,s') })
    )
  ) (\<lambda>(e,s'). doM { end s'; raise e });

  end s';
  return x
}"

lemma run_mmblock[run_simps]:
  "run (mmblock begin end m) s = mwp (run begin s) NTERM FAIL EXC
    (\<lambda>s' s. mwp (run m s')
      NTERM
      FAIL
      (\<lambda>e s'. mwp (run (end s') s) NTERM FAIL EXC (\<lambda>_ s. EXC e s))
      (\<lambda>x s'. mwp (run (end s') s) NTERM FAIL EXC (\<lambda>_ s. SUCC x s))
    )"
  by (auto simp add: mmblock_def run_simps mwp_def cong del: mwp_cong split: prod.splits mres.splits)

lemma mmblock_mono[partial_function_mono]:
  "monotone M.le_fun M_ord m \<Longrightarrow> monotone M.le_fun M_ord (\<lambda>f. mmblock begin end (m f))"
  unfolding mmblock_def
  by pf_mono_prover



subsection \<open>Lifting from Sum-Type\<close>
definition "lift_sum m \<equiv> case m of Inl f \<Rightarrow> fail f | Inr x \<Rightarrow> return x"

lemma lift_sum_simps[simp]:
  "lift_sum (Inl f) = fail f"
  "lift_sum (Inr x) = return x"
  by (auto simp: lift_sum_def)

lemma run_lift_sum[run_simps]:
  "run (lift_sum m) s = (case m of Inl f \<Rightarrow> FAIL f | Inr x \<Rightarrow> SUCC x s)"
  by (auto simp: lift_sum_def run_simps split: sum.splits)

subsection \<open>Lifting Lenses\<close>

definition "mget L s \<equiv> lift_sum (eget L s)"
definition "mput L x s \<equiv> lift_sum (eput L x s)"

definition "use L \<equiv> doM { s\<leftarrow>get; mget L s }"
definition assign (infix "::=" 51) where "assign L x \<equiv> doM { s\<leftarrow>get; s\<leftarrow>mput L x s; set s }"

(*
definition "eget_cases L a f1 f2 \<equiv> case eget L a of Inr b \<Rightarrow> f1 b | Inl e \<Rightarrow> f2 e"

lemma eget_cases_split:
  "P (eget_cases L a f1 f2) \<longleftrightarrow> (epre_get L a \<longrightarrow> P (f1 (eget' L a))) \<and> (\<forall>e. eget L a = Inl e \<longrightarrow> P (f2 e))"
  unfolding eget_cases_def by (auto split: sum.split)

lemma eget_cases_split_asm:
  "P (eget_cases L a f1 f2) \<longleftrightarrow> \<not> ((epre_get L a \<and> \<not>P (f1 (eget' L a))) \<or> (\<exists>e. eget L a = Inl e \<and> \<not> P (f2 e)))"
  apply (subst eget_cases_split[of P]) by blast

definition "eput_cases L b a f1 f2 \<equiv> case eput L b a of Inr a \<Rightarrow> f1 a | Inl e \<Rightarrow> f2 e"

lemma eput_cases_split:
  "P (eput_cases L b a f1 f2) \<longleftrightarrow> (epre_put_single_point L b a \<longrightarrow> P (f1 (eput' L b a))) \<and> (\<forall>e. eput L b a = Inl e \<longrightarrow> P (f2 e))"
  unfolding eput_cases_def
  by (auto split: sum.split simp: eput_Inr_conv_sp)

lemma eput_cases_split_asm:
  "P (eput_cases L b a f1 f2) \<longleftrightarrow> \<not>((epre_put_single_point L b a \<and> \<not> P (f1 (eput' L b a))) \<or> (\<exists>e. eput L b a = Inl e \<and> \<not> P (f2 e)))"
  apply (subst eput_cases_split[of P]) by blast

lemmas epg_splits = eget_cases_split eget_cases_split_asm eput_cases_split eput_cases_split_asm
*)

abbreviation (input) "eget_cases L s f1 f2 \<equiv> case epre_get L s of None \<Rightarrow> f1 (eget' L s) | Some e \<Rightarrow> f2 e"
abbreviation (input) "eput_cases L x s f1 f2 \<equiv> case epre_put L x s of None \<Rightarrow> f1 (eput' L x s) | Some e \<Rightarrow> f2 e"

lemma run_mget[run_simps]:
  "run (mget L s) xx = (eget_cases L s (\<lambda>x. SUCC x xx) (FAIL))"
  by (auto simp: mget_def run_simps split: sum.splits option.splits)

lemma run_mput[run_simps]:
  "elens L \<Longrightarrow> run (mput L x s) xx = (eput_cases L x s (\<lambda>x. SUCC x xx) FAIL)"
  by (auto simp: mput_def run_simps split: sum.splits option.splits)

lemma run_use[run_simps]:
  "elens L \<Longrightarrow> run (use L) s = (eget_cases L s (\<lambda>x. SUCC x s) FAIL)"
  by (auto simp: use_def run_simps)

lemma run_assign[run_simps]:
  "elens L \<Longrightarrow> run (assign L x) s = eput_cases L x s (SUCC ()) FAIL"
  by (auto simp: assign_def run_simps split: option.splits)



definition "zoom L m \<equiv> mmblock (use L) (assign L) m"

lemma run_zoom[run_simps]:
  assumes [simp]: "elens L"
  shows
  "run (zoom L m) s = (
    eget_cases L s
      (\<lambda>ss. mwp (run m ss) NTERM FAIL (\<lambda>e ss. EXC e (eput' L ss s)) (\<lambda>x ss. SUCC x (eput' L ss s)))
      FAIL
    )"
  by (auto simp: zoom_def run_simps split: option.splits)


lemma zoom_mono[partial_function_mono]:
  "monotone M.le_fun M_ord m \<Longrightarrow> monotone M.le_fun M_ord (\<lambda>f. zoom L (m f))"
  unfolding zoom_def
  by pf_mono_prover

lemma zoom_get_is_use[simp]: "elens L \<Longrightarrow> zoom L get = use L"
  apply (rule)
  apply (auto simp: run_simps split: option.split)
  done

lemma zoom_set_is_assign[simp]: "ehlens L \<Longrightarrow> zoom L (set x) = (L ::= x)"
  apply (rule)
  apply (auto simp: run_simps split: option.split)
  done

lemma zoom_comp_eq[simp]: "\<lbrakk>elens L\<^sub>1; elens L\<^sub>2\<rbrakk> \<Longrightarrow> zoom (L\<^sub>1 \<bullet> L\<^sub>2) f = zoom L\<^sub>1 (zoom L\<^sub>2 f)"
  apply rule
  apply (auto simp: run_simps split: option.split)
  done

(* TODO: Move 
   TODO/FIXME: Simplifier should derive this on its own! *)  
lemma eget_put_pre: "elens L \<Longrightarrow> epre_put L x s = None \<Longrightarrow> epre_get L (eput' L x s) = None"
  by (metis (mono_tags, lifting) LENS_downstage(1) epre_get_def lens.simp_rls(4) lower_epre_put' lower_get_def lower_invert(1) lower_lens_def not_None_eq pre_eq_conv(2))
  
lemma zoom_return: "\<lbrakk>elens L\<rbrakk> \<Longrightarrow> zoom L (return x) = use L\<then>return x"
  apply (rule M_eqI)
  apply (auto simp: run_simps eget_put_pre split: option.split)
  done
  
lemma zoom_bind: "elens L \<Longrightarrow> zoom L (m\<bind>f) = zoom L m \<bind> zoom L o f"
  apply (rule M_eqI)
  apply (auto simp: run_simps eget_put_pre split: option.split)
  done
  
  
  

definition "ap_state f \<equiv> doM {s\<leftarrow>get; set (f s)}"
definition ap_lens (infix "%=" 51) where "ap_lens L f \<equiv> zoom L (ap_state f)"

lemma run_ap_state[run_simps]: "run (ap_state f) s = SUCC () (f s)"
  by (auto simp: ap_state_def run_simps)

lemma run_ap_lens[run_simps]: "elens L
  \<Longrightarrow> run (L%=f) s = (eget_cases L s (\<lambda>ss. SUCC () (eput' L (f ss) s)) FAIL)"
  by (auto simp: ap_lens_def run_simps split: option.splits)


definition "map_lens L f s \<equiv> doM {
  x \<leftarrow> mget L s;
  x \<leftarrow> f x;
  mput L x s
}"

thm run_simps

lemma run_map_lens[run_simps]:
  "elens L \<Longrightarrow> run (map_lens L f a) s = (
    eget_cases L a (\<lambda>b.
      mwp (run (f b) s) NTERM FAIL EXC (\<lambda>b s. SUCC (eput' L b a) s))
    ) FAIL"
  by (auto simp add: map_lens_def run_simps split: option.splits)


(* For presentation in paper *)
  
definition "noexc m \<equiv> \<forall>s. run m s \<noteq> NTERM \<and> \<not>is_EXC (run m s)"

lemma "elens L \<Longrightarrow> use L = zoom L get" by simp
lemma "ehlens L \<Longrightarrow> (L ::= x) = (zoom L (set x))" by simp

  
  
  
  
section \<open>Derived Constructs\<close>

subsection \<open>While\<close>

  definition "mwhile b f \<equiv> REC (\<lambda>mwhile \<sigma>. doM { ctd \<leftarrow> b \<sigma>; if ctd then doM {\<sigma>\<leftarrow>f \<sigma>; mwhile \<sigma> } else return \<sigma> })"
  abbreviation "mwhile' b f \<equiv> mwhile (\<lambda>_::unit. b) (\<lambda>_. f) ()"

  lemma sim_mwhile[sim_rules]:
    "\<lbrakk>\<And>\<sigma>. sim (b \<sigma>) (b' \<sigma>); \<And>\<sigma>. sim (f \<sigma>) (f' \<sigma>)\<rbrakk> \<Longrightarrow> sim (mwhile b f \<sigma>) (mwhile b' f' \<sigma>)"
    by (auto intro!: sim_rules sim_REC[OF mwhile_def mwhile_def, discharge_monos])

  lemma mwhile_mono[partial_function_mono]:
    assumes "\<And>x. M_mono (\<lambda>f. b f x)"
    assumes "\<And>x. M_mono (\<lambda>f. c f x)"
    shows "M_mono (\<lambda>D. mwhile (b D) (c D) \<sigma>)"
    supply assms[partial_function_mono]
    unfolding mwhile_def
    by pf_mono_prover

  lemma mwhile_invar_rule:
    assumes LR: "run (mwhile b f \<sigma>) s = r"
    assumes NTERM: "P NTERM"
    assumes INIT: "I \<sigma> s"
    assumes STEP: "\<And>\<sigma> s. \<lbrakk>I \<sigma> s\<rbrakk>
      \<Longrightarrow> mwp (run (b \<sigma>) s)
              True
              (\<lambda>msg. P (FAIL msg))
              (\<lambda>e s. P (EXC e s) )
              (\<lambda>ctd s. if ctd then (
                  mwp (run (f \<sigma>) s) True (\<lambda>msg. P (FAIL msg)) (\<lambda>e s. P (EXC e s)) I)
                else P (SUCC \<sigma> s) ) "
    shows "P r"
  proof -
    from LR INIT show ?thesis
    proof (induction rule: lrmwpe_REC_partial[OF mwhile_def, discharge_monos, consumes 1, case_names nterm step])
      case (nterm x s)
      then show ?case by (simp add: NTERM)
    next
      case (step while x s r)
      then show ?case
        using STEP[OF \<open>I x s\<close>]
        by (auto simp: run_simps mwp_def NTERM split: mres.splits)
    qed
  qed


  lemmas mwhile_unfold[code] = REC_unfold[OF mwhile_def, discharge_monos]



subsection \<open>Check\<close>
  definition "fcheck e \<phi> \<equiv> if \<phi> then return () else fail e"

  lemma fcheck_laws[simp]:
    "fcheck e True = return ()"
    "fcheck e False = fail e"
    by (auto simp: fcheck_def)

  lemma run_fcheck[run_simps]: "run (fcheck f \<Phi>) s = (if \<Phi> then SUCC () s else FAIL f)"
    by (auto simp: fcheck_def run_simps)




subsection \<open>Fold\<close>
  fun mfold where
    "mfold f [] s = return s"
  | "mfold f (x#xs) s = doM {
      s \<leftarrow> f x s;
      mfold f xs s
  }"

  abbreviation "mfold' f xs \<equiv> mfold (\<lambda>x _. f x) xs ()"

  lemma mfold_sim[sim_rules]:
    assumes [sim_rules]: "\<And>x s. sim (f x s) (f' x s)"
    shows "sim (mfold f xs s) (mfold f' xs s)"
    apply (induction xs arbitrary: s)
    apply (auto intro!: sim_rules)
    done

  lemma mfold_mono[partial_function_mono]:
    assumes [partial_function_mono]: "\<And>a \<sigma>. M_mono (\<lambda>fa. f fa a \<sigma>)"
    shows "M_mono (\<lambda>D. mfold (f D) l \<sigma>)"
  proof (induction l arbitrary: \<sigma>)
    case Nil
    then show ?case by simp pf_mono_prover
  next
    case [partial_function_mono]: (Cons a l)
    show ?case
      by simp pf_mono_prover
  qed


subsection \<open>Map\<close>

fun mmap where
  "mmap _ [] = return []"
| "mmap f (x#xs) = doM { x\<leftarrow>f x; xs\<leftarrow>mmap f xs; return (x#xs) }"

lemma mmap_sim[sim_rules]:
  assumes "\<And>x. x\<in>list.set xs \<Longrightarrow> sim (f x) (f' x)"
  shows "sim (mmap f xs) (mmap f' xs)"
  using assms
  apply (induction xs)
  by (auto intro!: sim_rules)


lemma mmap_mono[partial_function_mono]:
  assumes [partial_function_mono]: "\<And>a. M_mono (\<lambda>fa. f fa a)"
  shows "M_mono (\<lambda>D. mmap (f D) xs)"
proof (induction xs)
  case Nil
  then show ?case by simp pf_mono_prover
next
  case [partial_function_mono]: (Cons a xs)
  show ?case by simp pf_mono_prover
qed

lemma run_mmap_unit_state_idxD:
  assumes "run (mmap f xs) () = SUCC ys ()"
  assumes "i<length xs"
  shows "run (f (xs!i)) () = SUCC (ys!i) ()"
  using assms apply (induction xs arbitrary: i ys)
  by (auto simp: run_simps nth_Cons split: nat.splits elim!: mwp_eq_cases)

lemma run_mmap_length_eq:
  assumes "run (mmap f xs) s = SUCC ys s'"
  shows "length ys = length xs"
  using assms apply (induction xs arbitrary: ys s)
  by (auto simp: run_simps elim!: mwp_eq_cases)

lemma run_mmap_unit_state_elemD:
  assumes "run (mmap f xs) () = SUCC ys ()"
  assumes "x\<in>List.set xs"
  shows "\<exists>y\<in>List.set ys. run (f x) () = SUCC y ()"
  using assms
  by (auto simp: in_set_conv_nth Bex_def run_mmap_unit_state_idxD run_mmap_length_eq)

lemma run_mmap_append[run_simps]:
  "run (mmap f (xs@ys)) s = mwp (run (mmap f xs) s) NTERM FAIL EXC (\<lambda>rxs s.
  mwp (run (mmap f ys) s) NTERM FAIL EXC (\<lambda>rys s. SUCC (rxs@rys) s))"
  apply (induction xs arbitrary: s)
  apply (auto simp: run_simps mwp_def split: mres.splits)
  done


(* TODO: What are good rules for mmap ? *)



subsection \<open>Lookup\<close>

  definition "lookup f m s \<equiv> case m s of None \<Rightarrow> fail f | Some x \<Rightarrow> return x"

  lemma run_lookup[run_simps]:
    "run (lookup f m k) s = (case m k of None \<Rightarrow> FAIL f | Some v \<Rightarrow> SUCC v s)"
    by (auto simp: lookup_def run_simps split: option.splits)

  lemma lookup_sim[sim_rules]:
    assumes "\<pi> \<subseteq>\<^sub>m \<pi>'"
    shows "sim (lookup f \<pi> x2) (lookup f' \<pi>' x2)"
    using map_leD[OF assms]
    by (auto simp: sim_def run_simps split: option.split)


subsection \<open>Hiding too generic Names\<close>    
    
hide_const (open) get set M.M
    
end
