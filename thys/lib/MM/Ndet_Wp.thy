*** obsolete, inlined into NEMonad now
theory Hoare_Logic
imports NRes
begin

  subsection \<open>Weakest Precondition\<close>
  
  text \<open>Weakest precondition: \<open>m\<close> does not fail, and all possible results satisfy postcondition \<open>Q\<close>\<close>
  definition [pw_init]: "wp m Q \<longleftrightarrow> \<not>is_fail m \<and> (\<forall>x. is_res m x \<longrightarrow> Q x)"

  text \<open>Consequence rule: weaken postcondition \<close>  
  lemma wp_cons: "wp m Q \<Longrightarrow> (\<And>x. Q x \<Longrightarrow> Q' x) \<Longrightarrow> wp m Q'"
    by pw

  subsubsection \<open>Hoare Triple\<close>  
  text \<open>Traditionally, program correctness is stated as Hoare-triples \<open>{P} c {Q}\<close>,
    where \<open>P\<close> is the precondition, and \<open>Q\<close> the post-condition.
    In our shallow embedding, the precondition is the assumptions of the theorem, such
    that our correctness statements have the form:
    \<open>P \<Longrightarrow> wp c Q\<close>
  \<close>
    
    
  subsection \<open>Wp-Calculus\<close>  
  text \<open>Syntactic rules for weakest precondition\<close>      
  named_theorems wp_rule \<open>Syntactic rules for wp\<close>
  
  lemma wp_RETURN_iff: "wp (RETURN x) Q \<longleftrightarrow> Q x"
    by pw
  
  lemma wp_BIND_iff: "wp (BIND m f) Q \<longleftrightarrow> wp m (\<lambda>x. wp (f x) Q)"  
    by pw
    
  lemmas [wp_rule] = 
    wp_RETURN_iff[THEN iffD2]  
    wp_BIND_iff[THEN iffD2]  

  lemma wp_ASSERT[wp_rule]: "P \<Longrightarrow> Q () \<Longrightarrow> wp (ASSERT P) Q"  
    by pw
        
  lemma wp_SPEC[wp_rule]: "(\<And>x. P x \<Longrightarrow> Q x) \<Longrightarrow> wp (SPEC P) Q"  
    by pw
    
  lemma wp_Let[wp_rule]: "(\<And>x. x=v \<Longrightarrow> wp (f x) Q) \<Longrightarrow> wp (let x=v in f x) Q"  
    by pw
    
    
  lemma wp_if[wp_rule]: "\<lbrakk> b \<Longrightarrow> wp m Q; \<not>b \<Longrightarrow> wp m' Q \<rbrakk> \<Longrightarrow> wp (if b then m else m') Q" by simp 
    
    
  lemma wp_if_ext[wp_rule]: "\<lbrakk>b \<Longrightarrow> P; \<not>b\<Longrightarrow>Q\<rbrakk> \<Longrightarrow> if b then P else Q"   by simp
    
  lemma wp_prod_case[wp_rule]: "\<lbrakk>\<And>a b. p=(a,b) \<Longrightarrow> wp (f a b) Q\<rbrakk> \<Longrightarrow> wp (case p of (a,b) \<Rightarrow> f a b) Q"
    by (cases p) auto
  
  
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
    
  lemma wp_WHILE:
    assumes "wf V"
    assumes "I s"
    assumes STEP: "\<And>s. \<lbrakk> I s \<rbrakk> \<Longrightarrow> wp (b s) (\<lambda>r. if r then wp (f s) (\<lambda>s'. I s' \<and> (s',s)\<in>V) else Q s)"
    shows "wp (WHILE b f s) Q"
    using assms(1,2)
    apply (induction s)
    apply (subst WHILE_unfold)
    apply (intro wp_rule STEP[THEN wp_cons])
    apply simp_all
    apply (erule wp_cons)
    by blast
    
  subsection \<open>Invariant Annotation\<close>
  text \<open>We annotate variants and invariants to WHILE-loops and recursions,
    such that we can automatically generate verification conditions.
    \<close>
  
  definition WHILEI :: "'a rel \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool nres) \<Rightarrow> ('a \<Rightarrow> 'a nres) \<Rightarrow> 'a \<Rightarrow> 'a nres"
    where 
    "WHILEI V I b f s \<equiv> WHILE (\<lambda>s. do { assert I s; b s }) (\<lambda>s. do { assert I s; f s }) s"
  
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
    
    
  subsection \<open>Automation\<close>  
  
  named_theorems wp_recursion_rule \<open>Rule to trigger resolution with premises\<close>
  
  method wp_basic_step = 
    rule wp_rule 
  | rule wp_recursion_rule,rprems
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
          Syntax for return, with low binding priority: \<^term>\<open>return x+1\<close>.
    \<^item> \<^term>\<open>FAIL\<close>: Specifies a failing program. Failure may be due 
      to non-termination or failed assertions.
    \<^item> \<^term>\<open>BIND m f\<close>: Sequential composition. Syntax: \<^term>\<open>do { x\<leftarrow>m; f x }\<close>
    \<^item> \<^term>\<open>REC F\<close>: Recursion.
    \<^item> \<^term>\<open>RECI V P F\<close>: Recursion with variant and precondition annotation. TODO: maybe also need postcond!
    
  
    Any combinator from HOL can be used. We provide support (automation, etc.)
    for the following:
    \<^item> \<^term>\<open>if b then m\<^sub>1 else m\<^sub>2\<close>
    \<^item> \<^term>\<open>let x=v in f x\<close>
    \<^item> \<^term>\<open>case p of (a,b) \<Rightarrow> f a b\<close>
    
    Moreover, we support the following derived combinators:
    \<^item> \<^term>\<open>ASSERT P = (if P then return () else FAIL)\<close>. 
      Syntax with lower binding priority: \<^term>\<open>assert P\<and>Q\<close>
    \<^item> \<^term>\<open>WHILE b f s\<close>. While loop. Defined via recursion.
    \<^item> \<^term>\<open>WHILEI V I b f s\<close>. While loop with variant and invariant annotation.
    
    For each combinator, we need to provide:
      \<^item> wp-rule
      \<^item> mono-rule (if higher-order)
      \<^item> pw-rule (if non-recursive)
      \<^item> refinement rule (see later theory on refinement)
    
  \<close>

        
    

end
