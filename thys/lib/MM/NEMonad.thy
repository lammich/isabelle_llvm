section \<open>Nondeterminism Error Monad\<close>
theory NEMonad
imports "../Basic_Imports" Flat_CCPO
begin
  subsection \<open>Type Definition\<close>
  text \<open>
    The result of a nondeterministic computation
  \<close>
  datatype 'a neM = 
    SPEC (the_spec: "'a \<Rightarrow> bool") \<comment> \<open>May return any value that satisfies a predicate\<close>
  | FAIL  \<comment> \<open>May fail\<close>

  fun map_neM where
    "map_neM f (SPEC P) = SPEC (\<lambda>y. \<exists>x. P x \<and> y=f x)"
  | "map_neM _ FAIL = FAIL"  
  
  
  
  subsection \<open>Pointwise Reasoning\<close>
  text \<open>Many theorems about the result monad can easily be 
    solved by transforming them to pointwise proposition over
    possible results.\<close>
  
  definition "is_fail m \<longleftrightarrow> m=FAIL"
  definition "is_res m x \<longleftrightarrow> (m\<noteq>FAIL \<and> the_spec m x)"
    
  lemma pw_basic:
    "is_res (SPEC P) x \<longleftrightarrow> P x"
    "\<not>is_res FAIL x"
    "is_fail m \<longleftrightarrow> m=FAIL"
    unfolding is_res_def is_fail_def by auto
  
  lemma pw_eq_iff: "m=m' \<longleftrightarrow> ((is_fail m \<longleftrightarrow> is_fail m') \<and> (\<forall>x. is_res m x \<longleftrightarrow> is_res m' x))"
    by (cases m; cases m'; auto simp add: pw_basic)
        

  subsubsection \<open>Automation\<close>
  text \<open>We first rewrite with initialization rules, that convert
    a property to a pointwise property, and then with 
    simplification rules, which syntactically decompose pointwise 
    properties.
  \<close>

  named_theorems pw_init \<open>Pointwise reasoning: initialization\<close>
  named_theorems pw_simp \<open>Pointwise reasoning: simplification\<close>

  lemmas [pw_simp] = pw_basic
  lemmas [pw_init] = pw_eq_iff
  
  method pw = ((simp only: pw_init)?; auto simp: pw_simp)
  method pw' = ((simp only: pw_init)?; simp add: pw_simp)
      
  
  lemma pw_map_neM[pw_simp]:
    "map_neM f m = FAIL \<longleftrightarrow> is_fail m"
    "is_res (map_neM f m) y \<longleftrightarrow> (\<exists>x. is_res m x \<and> y=f x)"
    apply (cases m; auto simp: is_fail_def is_res_def)
    apply (cases m; auto simp: is_fail_def is_res_def)
    done
  
  lemma pw_Let[pw_simp]:
    "Let x f = FAIL \<longleftrightarrow> is_fail (f x)"  
    "is_res (Let x f) r \<longleftrightarrow> is_res (f x) r"  
    by pw+
    
    
  subsection \<open>Basic Combinators\<close>

  subsubsection \<open>Return and Bind\<close>
  text \<open>Deterministically return a result\<close>
  definition "RETURN x \<equiv> SPEC (\<lambda>r. r=x)"
  
  text \<open>Sequential composition: apply \<open>f\<close> to every possible result of \<open>m\<close>.\<close>
  definition "BIND m f \<equiv> case m of 
    SPEC P \<Rightarrow> (if \<exists>x. P x \<and> f x = FAIL then FAIL
              else SPEC (\<lambda>r. \<exists>x Q. P x \<and> f x = SPEC Q \<and> Q r))
  | FAIL \<Rightarrow> FAIL"

  
  text \<open>Parallel composition: pair of results. 
    Note, this is subtly different from sequential composition and returning the pair,
    in case that the first result is empty, and the second one fails!
  \<close>
  definition "PAR m\<^sub>1 m\<^sub>2 \<equiv> case (m\<^sub>1,m\<^sub>2) of
    (SPEC P\<^sub>1, SPEC P\<^sub>2) \<Rightarrow> SPEC (pred_prod P\<^sub>1 P\<^sub>2)
  | _ \<Rightarrow> FAIL  
  "
  
  
  lemma BIND_simps:
    "BIND FAIL f = FAIL"
    "BIND (SPEC P) f = (
      if \<exists>x. P x \<and> f x = FAIL then FAIL
      else SPEC (\<lambda>r. \<exists>x Q. P x \<and> f x = SPEC Q \<and> Q r)
    )"  
    unfolding BIND_def by auto
  
  
  lemma pw_RETURN[pw_simp]:
    "RETURN x \<noteq> FAIL"
    "is_res (RETURN x) y \<longleftrightarrow> x=y"
    unfolding RETURN_def by pw+

  lemma pw_BIND[pw_simp]:
    "BIND m f = FAIL \<longleftrightarrow> is_fail m \<or> (\<exists>y. is_res m y \<and> is_fail (f y))"
    "is_res (BIND m f) x \<longleftrightarrow> (\<forall>y. is_res m y \<longrightarrow> \<not>is_fail (f y)) \<and> (\<exists>y. is_res m y \<and> is_res (f y) x)"
    unfolding BIND_def
    apply (auto simp: pw_simp is_fail_def split: neM.split)
    by (meson is_res_def neM.exhaust_sel)

    
  lemma pw_PAR[pw_simp]:
    "PAR m\<^sub>1 m\<^sub>2 = FAIL \<longleftrightarrow> is_fail m\<^sub>1 \<or> is_fail m\<^sub>2"
    "is_res (PAR m\<^sub>1 m\<^sub>2) rr \<longleftrightarrow> (case rr of (r\<^sub>1,r\<^sub>2) \<Rightarrow> is_res m\<^sub>1 r\<^sub>1 \<and> is_res m\<^sub>2 r\<^sub>2)"
    unfolding PAR_def is_fail_def is_res_def
    apply (cases m\<^sub>1; cases m\<^sub>2; auto)
    apply (cases m\<^sub>1; cases m\<^sub>2; auto)
    done
    
    

  text \<open>\<^const>\<open>RETURN\<close> and \<^const>\<open>BIND\<close> satisfy the monad laws:\<close>  
  lemma return_bind[simp]: "BIND (RETURN x) f = f x"
    by pw
  
  lemma bind_return[simp]: "BIND m RETURN = m"  
    by pw

  lemma bind_bind[simp]: "BIND (BIND m f) g = BIND m (\<lambda>x. BIND (f x) g)"
    by pw

  text \<open>There are also laws for the interaction of \<^const>\<open>BIND\<close> and \<^const>\<open>FAIL\<close>\<close>
  lemma fail_bind[simp]: "BIND FAIL f = FAIL" by pw
  
  text \<open>Note that \<^term>\<open>SPEC (\<lambda>_. False)\<close> is special, in that it specifies a program
    with no possible results. It's the dual to \<^const>\<open>FAIL\<close>. We call it \<open>EMPTY\<close>: \<close>
  abbreviation "EMPTY \<equiv> SPEC (\<lambda>_. False)"  
    
  text \<open>\<^const>\<open>EMPTY\<close> can be an un-intuitive corner-case for some rules, 
    like the following, that only holds for \<^term>\<open>m\<noteq>EMPTY\<close>:\<close>  
  lemma bind_fail: "BIND m (\<lambda>_. FAIL) = FAIL \<longleftrightarrow> m\<noteq>EMPTY" by pw

  lemma bind_empty[simp]: "BIND EMPTY f = EMPTY" by pw

  text \<open>Parallel can be expressed by sequential composition, except for the extreme case where
    the first component is empty, and the second one fails. 
    In this case, due to the sequential nature of BIND, the failing component will never be executed,
    and the result will be empty. For parallel composition, though, both components will be executed,
    and the failure will propagate.
  \<close>
  lemma PAR_as_BIND_iff: "PAR m\<^sub>1 m\<^sub>2 = BIND m\<^sub>1 (\<lambda>r\<^sub>1. BIND m\<^sub>2 (\<lambda>r\<^sub>2. RETURN (r\<^sub>1,r\<^sub>2))) \<longleftrightarrow> (m\<^sub>1\<noteq>EMPTY \<or> m\<^sub>2\<noteq>FAIL)"
    by pw
  
  lemma PAR_as_BIND: "m\<^sub>1\<noteq>EMPTY \<or> m\<^sub>2\<noteq>FAIL \<Longrightarrow> PAR m\<^sub>1 m\<^sub>2 = BIND m\<^sub>1 (\<lambda>r\<^sub>1. BIND m\<^sub>2 (\<lambda>r\<^sub>2. RETURN (r\<^sub>1,r\<^sub>2)))"
    by pw

  text \<open>The parallel composition operator is commutative\<close>    
  lemma PAR_commute: "PAR m\<^sub>1 m\<^sub>2 = map_neM prod.swap (PAR m\<^sub>2 m\<^sub>1)"
    by pw

    
  subsubsection \<open>Syntax\<close>  

  text \<open>We establish some syntax\<close>
    
  (*abbreviation (input) bind_doI where "bind_doI m (\<lambda>x. f x) \<equiv> BIND m (\<lambda>x. f x)"*)
  abbreviation then_doI where "then_doI m f \<equiv> BIND m (\<lambda>_. f)"

  nonterminal doI_binds and doI_bind
  syntax
    "_doI_block" :: "doI_binds \<Rightarrow> 'a" ("do\<^sub>n\<^sub>e {//(2  _)//}" [12] 62)
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
      \<rightleftharpoons> "CONST BIND t (\<lambda>p. e)"

    "_doI_block (_doI_cons (_doI_let p t) bs)"
      \<rightleftharpoons> "let p = t in _doI_block bs"

    "_doI_block (_doI_cons b (_doI_cons c cs))"
      \<rightleftharpoons> "_doI_block (_doI_cons b (_doI_final (_doI_block (_doI_cons c cs))))"

    "_doI_cons (_doI_let p t) (_doI_final s)"
      \<rightleftharpoons> "_doI_final (let p = t in s)"

    "_doI_block (_doI_final e)" \<rightharpoonup> "e"
  
    "(CONST then_doI m n)" \<rightharpoonup> "(CONST BIND m (\<lambda>_. n))"
    
   
  notation RETURN ("return\<^sub>n\<^sub>e _" 20)
  notation SPEC (binder "spec\<^sub>n\<^sub>e " 10)
  notation PAR (infixr "\<parallel>\<^sub>n\<^sub>e" 50)
  
      
  subsubsection \<open>Assert\<close>    
  text \<open>An assertion returns unit if the predicate holds, and fails otherwise.
    Note that returning unit is the functional way of having a function with no return value (e.g. void in C/C++).
  \<close>
  definition "ASSERT P \<equiv> if P then return\<^sub>n\<^sub>e () else FAIL"
  
  lemma pw_ASSERT[pw_simp]: 
    "ASSERT P = FAIL \<longleftrightarrow> \<not>P"  
    "is_res (ASSERT P) x \<longleftrightarrow> P"
    unfolding ASSERT_def
    apply pw+
    done
      
  notation ASSERT ("assert\<^sub>n\<^sub>e _" 20)

  definition "ASSUME P \<equiv> if P then return\<^sub>n\<^sub>e () else EMPTY"
  
  lemma pw_ASSUME[pw_simp]: 
    "ASSUME P \<noteq> FAIL"  
    "is_res (ASSUME P) x \<longleftrightarrow> P"
    unfolding ASSUME_def
    apply pw+
    done
      
  notation ASSUME ("assume\<^sub>n\<^sub>e _" 20)
  

  bundle monad_syntax_ne
  begin
    syntax
      "_doI_block" :: "doI_binds \<Rightarrow> 'a" ("do {//(2  _)//}" [12] 62)

    notation RETURN ("return _" 20)
    notation SPEC (binder "spec " 10)
    notation ASSERT ("assert _" 20)
    notation ASSUME ("assume _" 20)
    notation PAR (infixr "\<parallel>" 50)
      
  end
  
    
  subsubsection \<open>Recursion\<close>  
  text \<open>For recursion, we define a fixed-point combinator 
    utilizing a chain-complete partial order (CCPO).
    While CCPO's are advanced material, we try to capture the intuition
    below.
  \<close>
  

  
  context
  begin
    interpretation FR: flat_rec FAIL .
  
  (*    
    text \<open>The recursion combinator models recursive functions. 
      The recursive call is the first parameter to the function body, and
      the argument is the second parameter.
    \<close>
    definition REC :: "(('a \<Rightarrow> 'b neM) \<Rightarrow> 'a \<Rightarrow> 'b neM) \<Rightarrow> 'a \<Rightarrow> 'b neM" where "REC \<equiv> FR.REC"
  *)
        
    text \<open>The function body must be monotone. Intuitively, this means that 
      it terminates at less arguments if the recursive call terminates at less arguments.
    \<close>
    definition nres_mono :: "(('a \<Rightarrow> 'b neM) \<Rightarrow> 'a \<Rightarrow> 'b neM) \<Rightarrow> bool" where "nres_mono = FR.mono"
(*    
    text \<open>A recursive function can be unfolded, i.e., the body is inlined once.\<close>
    lemma REC_unfold: "nres_mono F \<Longrightarrow> REC F = F (REC F)"
      unfolding REC_def nres_mono_def using FR.REC_unfold .

    text \<open>Pointwise properties of recursive functions can be proved by well-founded induction 
      on the arguments.\<close>
    lemma REC_wf_induct: 
      assumes WF: "wf V"
      assumes MONO: "nres_mono F"
      assumes STEP: "\<And>x D. \<lbrakk>\<And>y. \<lbrakk>(y,x)\<in>V\<rbrakk> \<Longrightarrow> P y (D y) \<rbrakk> \<Longrightarrow> P x (F D x)"
      shows "P x (REC F x)"
      using assms unfolding nres_mono_def REC_def 
      using FR.REC_wf_induct by metis

    text \<open>For pointwise properties, which hold at non-terminating arguments, we
      can use the following induction scheme, which does not require a well-founded ordering.\<close>
    lemma REC_pointwise_induct:  
      assumes BOT: "\<And>x. P x FAIL"
      assumes STEP: "\<And>D x. (\<And>y. P y (D y)) \<Longrightarrow> P x (F D x)"
      shows "P x (REC F x)"
      using assms REC_def
      using FR.REC_pointwise_induct by metis
  *)      
  
    subsubsection \<open>Monotonicity\<close>  
    text \<open>Function bodies have to be monotone, i.e., when invoked with a recursive call 
      that terminates at less arguments, it must terminate at less arguments.
      
      This property can be established syntactically for the standard combinators
      programs are build from.
    \<close>
    
    
    named_theorems mono \<open>Monotonicity theorems for nres\<close> 
    
    definition "flat_le \<equiv> FR.le"
    
    lemma pw_flat_le[pw_init]: "flat_le m m' \<longleftrightarrow> is_fail m \<or> (\<not>is_fail m' \<and> (\<forall>x. is_res m x \<longleftrightarrow> is_res m' x))"  
      apply (cases m; cases m'; auto simp: pw_simp)
      apply (auto simp: flat_le_def FR.le_def)
      done
    
    lemma mono_alt: "nres_mono F = (\<forall>x y. fun_ord flat_le x y \<longrightarrow> fun_ord flat_le (F x) (F y))"
      unfolding nres_mono_def monotone_def FR.le_def flat_le_def ..
    
    definition nres_mono' :: "(('a \<Rightarrow> 'b neM) \<Rightarrow> 'c neM) \<Rightarrow> bool"
      where "nres_mono' F \<equiv> \<forall>D D'. fun_ord flat_le D D' \<longrightarrow> flat_le (F D) (F D')"
      
    lemma nres_monoI[mono]: 
      assumes "\<And>x. nres_mono' (\<lambda>D. F D x)"
      shows "nres_mono F"
      using assms unfolding mono_alt nres_mono'_def fun_ord_def
      by simp
    
    lemma nres_monoD: "nres_mono F \<Longrightarrow> nres_mono' (\<lambda>D. F D x)"
      unfolding mono_alt nres_mono'_def fun_ord_def
      by simp
      
    lemma mono_const[mono]: 
      "nres_mono' (\<lambda>_. c)"  
      "nres_mono' (\<lambda>D. D y)"
      unfolding nres_mono'_def fun_ord_def
      apply pw+
      done
      
    lemma mono_If[mono]: "
      nres_mono' (\<lambda>D. F D) \<Longrightarrow> nres_mono' (\<lambda>D. G D) \<Longrightarrow>
      nres_mono' (\<lambda>D. if b then F D else G D)"  
      unfolding nres_mono'_def fun_ord_def
      apply pw
      done
      
    lemma mono_BIND[mono]: "
      nres_mono' (\<lambda>D. F D) \<Longrightarrow> 
      (\<And>y. nres_mono' (\<lambda>D. G D y)) \<Longrightarrow> 
      nres_mono' (\<lambda>D. BIND (F D) (G D))"  
      unfolding nres_mono'_def fun_ord_def
      apply pw
      apply blast
      apply (smt (verit, ccfv_threshold))
      apply (smt (verit, ccfv_threshold))
      apply (smt (verit, ccfv_threshold))
      done
      
    lemma mono_PAR[mono]: "
      nres_mono' (\<lambda>D. F D) \<Longrightarrow> 
      nres_mono' (\<lambda>D. G D) \<Longrightarrow> 
      nres_mono' (\<lambda>D. PAR (F D) (G D))"
      unfolding nres_mono'_def fun_ord_def
      by (pw; blast)
     
      
      
    (*
    lemma mono_REC[mono]: 
      assumes "\<And>D. nres_mono (F D)"
      assumes "\<And>DD x. nres_mono' (\<lambda>D. F D DD x)"
      shows "nres_mono' (\<lambda>D. REC (F D) x)"  
      using assms
      unfolding nres_mono'_def flat_le_def REC_def
      apply clarsimp
      subgoal for D D'
        apply (rule FR.REC_mono[of F D D', unfolded fun_ord_def, rule_format])
        subgoal by (simp add: fun_ord_def nres_mono_def monotone_def)
        subgoal by blast
        done
      done
    *)  
      
    lemma mono_case_prod[mono]:
      assumes "\<And>a b. nres_mono' (\<lambda>D. F D a b)"
      shows "nres_mono' (\<lambda>D. case p of (a,b) \<Rightarrow> F D a b)"
      using assms
      unfolding nres_mono'_def fun_ord_def
      apply (cases p) by simp
    
    lemma mono_Let[mono]:
      assumes "\<And>x. nres_mono' (\<lambda>D. F D x)"
      shows "nres_mono' (\<lambda>D. let x=v in F D x)"
      using assms
      unfolding nres_mono'_def fun_ord_def
      by simp
      
      
      
            
  end
    
  
  subsection \<open>Weakest Precondition\<close>
  
  text \<open>Weakest precondition: \<open>m\<close> does not fail, and all possible results satisfy postcondition \<open>Q\<close>\<close>
  definition [pw_init]: "wp m Q \<longleftrightarrow> \<not>is_fail m \<and> (\<forall>x. is_res m x \<longrightarrow> Q x)"

  text \<open>Weakest liberal precondition: if \<open>m\<close> does not fail, all possible results satisfy postcondition \<open>Q\<close>\<close>
  definition [pw_init]: "wlp m Q \<longleftrightarrow> (\<not>is_fail m \<longrightarrow> (\<forall>x. is_res m x \<longrightarrow> Q x))"
  
  
  text \<open>Consequence rule: weaken postcondition \<close>  
  lemma wp_cons: "wp m Q \<Longrightarrow> (\<And>x. Q x \<Longrightarrow> Q' x) \<Longrightarrow> wp m Q'"
    by pw

  lemma wlp_cons: "wlp m Q \<Longrightarrow> (\<And>x. Q x \<Longrightarrow> Q' x) \<Longrightarrow> wlp m Q'"
    by pw
    
  lemma wp_imp_wlp: "wp m Q \<Longrightarrow> wlp m Q" by pw  
    
    
  subsection \<open>Wp-Calculus\<close>  
  text \<open>Syntactic rules for weakest precondition\<close>      
  named_theorems wp_rule \<open>Syntactic rules for wp\<close>
  
  lemma wp_RETURN_iff: "wp (RETURN x) Q \<longleftrightarrow> Q x"
    by pw
  
  lemma wp_BIND_iff: "wp (BIND m f) Q \<longleftrightarrow> wp m (\<lambda>x. wp (f x) Q)"  
    by pw

  lemma wp_PAR_iff: "wp (PAR m\<^sub>1 m\<^sub>2) Q \<longleftrightarrow> (\<exists>Q\<^sub>1 Q\<^sub>2. wp m\<^sub>1 Q\<^sub>1 \<and> wp m\<^sub>2 Q\<^sub>2 \<and> (\<forall>r\<^sub>1 r\<^sub>2. Q\<^sub>1 r\<^sub>1 \<and> Q\<^sub>2 r\<^sub>2 \<longrightarrow> Q (r\<^sub>1,r\<^sub>2)))"  
    by pw
    
  lemma wlp_PAR_iff: "wlp (PAR m\<^sub>1 m\<^sub>2) Q \<longleftrightarrow> (\<exists>Q\<^sub>1 Q\<^sub>2. wlp m\<^sub>1 Q\<^sub>1 \<and> wlp m\<^sub>2 Q\<^sub>2 \<and> (\<forall>r\<^sub>1 r\<^sub>2. Q\<^sub>1 r\<^sub>1 \<and> Q\<^sub>2 r\<^sub>2 \<longrightarrow> Q (r\<^sub>1,r\<^sub>2)))"  
    by pw
    
  lemmas [wp_rule] = 
    wp_RETURN_iff[THEN iffD2]  
    wp_BIND_iff[THEN iffD2]  

  text \<open>We do not include these in wp-rules by default,
    as they will create schematic postconditions\<close>  
  lemma wp_PAR:  
    assumes "wp m\<^sub>1 Q\<^sub>1" 
    assumes "wp m\<^sub>2 Q\<^sub>2" 
    assumes "\<And>r\<^sub>1 r\<^sub>2. Q\<^sub>1 r\<^sub>1 \<Longrightarrow> Q\<^sub>2 r\<^sub>2 \<Longrightarrow> Q (r\<^sub>1,r\<^sub>2)"
    shows "wp (PAR m\<^sub>1 m\<^sub>2) Q"
    using assms by pw
    
  lemma wlp_PAR:  
    assumes "wlp m\<^sub>1 Q\<^sub>1" 
    assumes "wlp m\<^sub>2 Q\<^sub>2" 
    assumes "\<And>r\<^sub>1 r\<^sub>2. Q\<^sub>1 r\<^sub>1 \<Longrightarrow> Q\<^sub>2 r\<^sub>2 \<Longrightarrow> Q (r\<^sub>1,r\<^sub>2)"
    shows "wlp (PAR m\<^sub>1 m\<^sub>2) Q"
    using assms by pw
    
    
  lemma wp_ASSERT[wp_rule]: "P \<Longrightarrow> Q () \<Longrightarrow> wp (ASSERT P) Q"  
    by pw

  lemma wp_ASSUME[wp_rule]: "(P \<Longrightarrow> Q ()) \<Longrightarrow> wp (ASSUME P) Q"  
    by pw
    
            
  lemma wp_SPEC[wp_rule]: "(\<And>x. P x \<Longrightarrow> Q x) \<Longrightarrow> wp (SPEC P) Q"  
    by pw
    
  lemma wp_Let[wp_rule]: "(\<And>x. x=v \<Longrightarrow> wp (f x) Q) \<Longrightarrow> wp (let x=v in f x) Q"  
    by pw
    
    
  lemma wp_if[wp_rule]: "\<lbrakk> b \<Longrightarrow> wp m Q; \<not>b \<Longrightarrow> wp m' Q \<rbrakk> \<Longrightarrow> wp (if b then m else m') Q" by simp 
    
    
  lemma wp_if_ext[wp_rule]: "\<lbrakk>b \<Longrightarrow> P; \<not>b\<Longrightarrow>Q\<rbrakk> \<Longrightarrow> if b then P else Q"   by simp
    
  lemma wp_prod_case[wp_rule]: "\<lbrakk>\<And>a b. p=(a,b) \<Longrightarrow> wp (f a b) Q\<rbrakk> \<Longrightarrow> wp (case p of (a,b) \<Rightarrow> f a b) Q"
    by (cases p) auto
  
  (*
  lemma wp_REC: 
    fixes x :: 'a and V :: "'a rel"
    assumes WF: "wf V"
    assumes MONO: "nres_mono F"
    assumes INIT: "P x"
    assumes STEP: "\<And>x D. (\<And>y. (y, x) \<in> V \<Longrightarrow> P y \<Longrightarrow> wp (D y) (Q y)) \<Longrightarrow> P x \<Longrightarrow> wp (F D x) (Q x)"
    shows "wp (REC F x) (Q x)"  
  proof -
    have "P x \<longrightarrow> wp (REC F x) (Q x)"
      apply (rule REC_wf_induct[OF WF MONO])
      apply (blast intro: STEP)
      done
    with INIT show ?thesis by blast
  qed  
  *)  
    
  lemma wlp_RETURN_iff: "wlp (RETURN x) Q \<longleftrightarrow> Q x"
    by pw

    (*
  lemma wlp_BIND_iff: "wlp (BIND m f) Q \<longleftrightarrow> wlp m (\<lambda>x. wlp (f x) Q)"  
    oops
    *)
      
  lemma wlp_BIND[wp_rule]: "wlp m (\<lambda>x. wlp (f x) Q) \<Longrightarrow> wlp (BIND m f) Q"  
    by pw
    
  lemmas [wp_rule] = 
    wlp_RETURN_iff[THEN iffD2]  

  lemma wlp_ASSERT[wp_rule]: "\<lbrakk>P\<Longrightarrow> Q()\<rbrakk> \<Longrightarrow> wlp (ASSERT P) Q"  
    by pw

  lemma wlp_ASSUME[wp_rule]: "(P \<Longrightarrow> Q ()) \<Longrightarrow> wlp (ASSUME P) Q"  
    by pw
    
            
  lemma wlp_SPEC[wp_rule]: "(\<And>x. P x \<Longrightarrow> Q x) \<Longrightarrow> wlp (SPEC P) Q"  
    by pw
    
  lemma wlp_Let[wp_rule]: "(\<And>x. x=v \<Longrightarrow> wlp (f x) Q) \<Longrightarrow> wlp (let x=v in f x) Q"  
    by pw
    
    
  lemma wlp_if[wp_rule]: "\<lbrakk> b \<Longrightarrow> wlp m Q; \<not>b \<Longrightarrow> wlp m' Q \<rbrakk> \<Longrightarrow> wlp (if b then m else m') Q" by simp 
    
    
  lemma wlp_if_ext[wp_rule]: "\<lbrakk>b \<Longrightarrow> P; \<not>b\<Longrightarrow>Q\<rbrakk> \<Longrightarrow> if b then P else Q"   by simp
    
  lemma wlp_prod_case[wp_rule]: "\<lbrakk>\<And>a b. p=(a,b) \<Longrightarrow> wlp (f a b) Q\<rbrakk> \<Longrightarrow> wlp (case p of (a,b) \<Rightarrow> f a b) Q"
    by (cases p) auto
  
  (*
  lemma wlp_REC: 
    fixes x :: 'a
    assumes INIT: "P x"
    assumes STEP: "\<And>x D. (\<And>y. P y \<Longrightarrow> wlp (D y) (Q y)) \<Longrightarrow> P x \<Longrightarrow> wlp (F D x) (Q x)"
    shows "wlp (REC F x) (Q x)"  
  proof -
    thm REC_pointwise_induct
    note R = REC_pointwise_induct[where P="\<lambda>x m. P x \<longrightarrow> wlp m (Q x)"]
    have "P x \<longrightarrow> wlp (REC F x) (Q x)"
      apply (rule R)
      apply pw
      using STEP by blast
    with INIT show ?thesis by blast
  qed  
  *)  
    
    
    
      
  (*    
  subsection \<open>Invariant Annotation\<close>
  text \<open>We annotate variants and invariants to WHILE-loops and recursions,
    such that we can automatically generate verification conditions.
    \<close>
  
  definition WHILEI :: "'a rel \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool neM) \<Rightarrow> ('a \<Rightarrow> 'a neM) \<Rightarrow> 'a \<Rightarrow> 'a neM"
    where 
    "WHILEI V I b f s \<equiv> WHILE (\<lambda>s. do\<^sub>n\<^sub>e { assert\<^sub>n\<^sub>e I s; b s }) (\<lambda>s. do\<^sub>n\<^sub>e { assert\<^sub>n\<^sub>e I s; f s }) s"
  
  lemma wp_WHILEI[wp_rule]:
    assumes "wf V"
    assumes "I s"
    assumes STEP: "\<And>s. \<lbrakk> I s \<rbrakk> \<Longrightarrow> wp (b s) (\<lambda>r. if r then wp (f s) (\<lambda>s'. I s' \<and> (s',s)\<in>V) else Q s)"
    shows "wp (WHILEI V I b f s) Q"
    using assms(1,2)
    unfolding WHILEI_def
    apply (intro wp_rule wp_WHILE[where I=I] STEP[THEN wp_cons])
    apply assumption+
    apply simp_all
    done
  
  lemma mono_WHILEI[mono]: 
    assumes "\<And>DD x. nres_mono' (\<lambda>D. b D x)"
    assumes "\<And>DD x y. nres_mono' (\<lambda>D. f D x)"
    shows "nres_mono' (\<lambda>D. WHILEI V I (b D) (f D) s)"
    unfolding WHILEI_def
    by (intro mono assms)
             
  definition RECI :: "'a rel \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> 
    (('a \<Rightarrow> 'b nres) \<Rightarrow> 'a \<Rightarrow> 'b nres) \<Rightarrow> 'a \<Rightarrow> 'b nres" where 
    "RECI V P F \<equiv> REC (\<lambda>D x. do {assert P x; F D x})"  
    
  lemma wp_RECI[wp_rule]: 
    fixes x :: 'a and V :: "'a rel"
    assumes WF: "wf V"
    assumes MONO: "nres_mono F"
    assumes INIT: "P x"
    assumes STEP: "\<And>x D. (\<And>y. (y, x) \<in> V \<Longrightarrow> P y \<Longrightarrow> wp (D y) (Q y)) \<Longrightarrow> P x \<Longrightarrow> wp (F D x) (Q x)"
    shows "wp (RECI V P F x) (Q x)"  
    unfolding RECI_def
    apply (rule wp_REC[of V _ P])
    apply fact
    apply (intro mono MONO[THEN nres_monoD])
    apply fact
    apply (intro wp_rule STEP)
    .

    
  lemma mono_RECI[mono]: 
    assumes "\<And>D. nres_mono (F D)"
    assumes "\<And>DD x. nres_mono' (\<lambda>D. F D DD x)"
    shows "nres_mono' (\<lambda>D. RECI V P (F D) x)"  
    unfolding RECI_def
    by (intro mono assms(1)[THEN nres_monoD] assms(2))
  *)  
    
  subsection \<open>Automation\<close>  
  
  named_theorems wp_recursion_rule \<open>Rule to trigger resolution with premises\<close>
  
  method wp_basic_step = 
    rule wp_rule 
  | rule wp_recursion_rule,(assumption|rprems)
  | intro mono
  
  method wp_step = find_goal \<open>wp_basic_step\<close>
  method wp = wp_step+

  
  lemmas [wp_recursion_rule] = wp_cons
      
  
  subsection \<open>Summary\<close>
  text \<open>
    We shallowly embed a basic non-deterministic PL.
    The basic combinators are
    
    \<^item> \<^term>\<open>SPEC P\<close>: Specify any result that satisfies predicate \<open>P\<close>. 
      Special cases:
      \<^item> \<^term>\<open>EMPTY = SPEC (\<lambda>_. False)\<close>: specifies a program with no results.
      \<^item> \<^term>\<open>RETURN x = SPEC (\<lambda>r. r=x)\<close>: specifies a program with the only result \<open>x\<close>.
          Syntax for return, with low binding priority: \<^term>\<open>return\<^sub>n\<^sub>e x+1\<close>.
    \<^item> \<^term>\<open>FAIL\<close>: Specifies a failing program. Failure may be due 
      to non-termination or failed assertions.
    \<^item> \<^term>\<open>BIND m f\<close>: Sequential composition. Syntax: \<^term>\<open>do\<^sub>n\<^sub>e { x\<leftarrow>m; f x }\<close>
    \<^item> \<^term>\<open>PAR m\<^sub>1 m\<^sub>2\<close>: Parallel composition. Syntax: \<^term>\<open>m\<^sub>1 \<parallel>\<^sub>n\<^sub>e m\<^sub>2\<close>
    
  
    Any combinator from HOL can be used. We provide support (automation, etc.)
    for the following:
    \<^item> \<^term>\<open>if b then m\<^sub>1 else m\<^sub>2\<close>
    \<^item> \<^term>\<open>let x=v in f x\<close>
    \<^item> \<^term>\<open>case p of (a,b) \<Rightarrow> f a b\<close>
    
    Moreover, we support the following derived combinators:
    \<^item> \<^term>\<open>ASSERT P = (if P then return\<^sub>n\<^sub>e () else FAIL)\<close>. 
      Syntax with lower binding priority: \<^term>\<open>assert\<^sub>n\<^sub>e P\<and>Q\<close>
    
    For each combinator, we need to provide:
      \<^item> wp-rule
      \<^item> mono-rule (if higher-order)
      \<^item> pw-rule (if non-recursive)
      \<^item> refinement rule (see later theory on refinement)
    
  \<close>
  
    
end
