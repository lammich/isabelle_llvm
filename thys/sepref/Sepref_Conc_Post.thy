section \<open>Concrete Equality Constraints\<close>
theory Sepref_Conc_Post
imports
  Main 
  Automatic_Refinement.Misc
begin
  subsection \<open>Basic Combinators\<close>
  named_theorems CP_defs
  
  definition [CP_defs]: "CP_JOIN CP\<^sub>1 CP\<^sub>2 \<equiv> \<lambda>r. CP\<^sub>1 r \<or> CP\<^sub>2 r"
  definition [CP_defs]: "CP_EX CP \<equiv> \<lambda>r. \<exists>x. CP x r"
  definition [CP_defs]: "CP_SEQ CP\<^sub>1 CP\<^sub>2 \<equiv> \<lambda>r. \<exists>x. CP\<^sub>1 x \<and> CP\<^sub>2 x r"
  definition [CP_defs]: "CP_RPT CP \<equiv> CP\<^sup>*\<^sup>*"
  definition [CP_defs]: "CP_SPLIT CP p \<equiv> \<lambda>r. case p of (a,b) \<Rightarrow> CP a b r"
  definition [CP_defs]: "CP_EX32 CP \<equiv> \<lambda>(x\<^sub>1,x\<^sub>2). \<exists>x\<^sub>3. CP (x\<^sub>1,x\<^sub>2,x\<^sub>3)"

  definition [CP_defs]: "CP_pred P \<equiv> P::bool" \<comment> \<open>Predicate, not further interpreted, but variables inside rewritten\<close>
  
  subsection \<open>Normalization\<close>

  subsubsection \<open>Simplification\<close>
  named_theorems CP_simps
  
  lemma [CP_simps]: 
    "CP_SEQ (\<lambda>_. True) CP = CP_EX CP"
    "CP_EX (\<lambda>_. P) = P"
    by (auto simp add: CP_defs)
  
  lemma [CP_simps]: "CP_SEQ (\<lambda>r. r = x) CP = CP x"  
    by (simp add: CP_defs)
    
  lemma [CP_simps]: "CP_JOIN A A = A"  
    by (simp add: CP_defs)

  lemma [CP_simps]: "p=(a,b) \<longleftrightarrow> fst p = a \<and> snd p = b" by auto

  lemma [CP_simps]: "case_prod f = (\<lambda>p. f (fst p) (snd p))" by auto
  
        
  subsubsection \<open>Monotonicity\<close>
  
  definition [CP_defs]: "CP_TAG x \<equiv> x::bool"   \<comment> \<open>Tag that protects schematic goal that receives simplified version\<close>
  definition [CP_defs]: "CP_HANDLE x \<equiv> x::bool" \<comment> \<open>Tag that marks combinator with normalized arguments\<close>

  lemma CP_HANDLEI: "X \<Longrightarrow> CP_HANDLE X" by (simp add: CP_defs)
  lemma CP_HANDLED: "CP_HANDLE X \<Longrightarrow> X" by (simp add: CP_defs)
  
    
  named_theorems CP_monos
  
  lemma CP_JOIN_mono[CP_monos]:
    "CP_JOIN A B r \<Longrightarrow> \<lbrakk> \<And>r. A r \<Longrightarrow> CP_TAG (A' r); \<And>r. B r \<Longrightarrow> CP_TAG (B' r)  \<rbrakk> \<Longrightarrow> CP_JOIN A' B' r"  
    by (auto simp: CP_defs)
    
  lemma CP_EX_mono[CP_monos]: "CP_EX A r \<Longrightarrow> \<lbrakk>\<And>x r. A x r \<Longrightarrow> CP_TAG (A' x r)\<rbrakk> \<Longrightarrow> CP_EX A' r"  
    by (auto simp: CP_defs)

  lemma CP_EX32_mono[CP_monos]: "CP_EX32 A r \<Longrightarrow> \<lbrakk>\<And>r. A r \<Longrightarrow> CP_TAG (A' r)\<rbrakk> \<Longrightarrow> CP_EX32 A' r"  
    by (auto simp: CP_defs)
        
  lemma CP_SEQ_mono[CP_monos]: "CP_SEQ A B r \<Longrightarrow> \<lbrakk>\<And>x. A x \<Longrightarrow> CP_TAG (A' x); \<And>x r. B x r \<Longrightarrow> CP_TAG (B' x r)\<rbrakk> \<Longrightarrow> CP_SEQ A' B' r"  
    by (auto simp: CP_defs)

  lemma CP_RPT_mono[CP_monos]: "CP_RPT A x r \<Longrightarrow> \<lbrakk> \<And>x r. A x r \<Longrightarrow> CP_TAG (A' x r) \<rbrakk> \<Longrightarrow> CP_RPT A' x r"
    apply (auto simp: CP_defs)
    by (metis mono_rtranclp)
    
  lemma CP_SPLIT_unfold[CP_simps]: "CP_SPLIT P = (\<lambda>p. P (fst p) (snd p))"
    by (auto simp: CP_defs split: prod.splits)
    
  lemma CP_tagI: "A \<Longrightarrow> CP_TAG A"  
    by (auto simp: CP_defs)
    
  lemma CP_tag_cong: "CP_TAG A = CP_TAG A" by simp 
  
  subsection \<open>Combinator Normalization\<close>
  
  subsubsection \<open>Basics\<close>
  
  text \<open>Transfer information into tag\<close>
  lemma CP_tag_resolve1:
    assumes "a=b"
    assumes "CP_TAG B"
    shows "CP_TAG (a=b \<and> B)"
    using assms by auto
    
  lemma CP_tag_resolve2:
    assumes "CP_pred P"
    assumes "CP_TAG B"
    shows "CP_TAG (P \<and> B)"
    using assms by (auto simp: CP_defs)

        
  lemma CP_tag_triv: "CP_TAG True"  
    by (auto simp: CP_TAG_def)
    
  method cp_resolve_tag = (((determ \<open>erule CP_tag_resolve1 CP_tag_resolve2\<close>)+)?,rule CP_tag_triv)

  text \<open>Explode products\<close>
  (* TODO: This is too fine-grained! Only split as much as required! *)
  method cp_explode_prod = (simp only: prod_eq_iff prod.inject cnv_conj_to_meta fst_conv snd_conv cong: CP_tag_cong)
  

  subsubsection \<open>Plain equality\<close>
  method handle_plain_eqs =
    drule asm_rl[of "_=_"] asm_rl[of "_\<and>_"] asm_rl[of True] asm_rl[of "CP_pred _"],
    (elim conjE)?,
    cp_resolve_tag

  subsubsection \<open>Sequence\<close>  
    
  lemma CP_SEQE:
    assumes "CP_SEQ (\<lambda>x. A x) (\<lambda>x r. B x r) r" 
    obtains x where "A x" "B x r"
    using assms by (auto simp: CP_defs)
    
  method handle_CP_SEQ =  
    drule CP_HANDLED,
    erule CP_SEQE,
    (elim conjE)?,
    (*cp_sels_to_vars?,
    cp_vars_to_sels?,*)
    cp_explode_prod?,
    cp_resolve_tag

  subsubsection \<open>Ex\<close>      
    
  lemma CP_EXE:
    assumes "CP_EX (\<lambda>x. A x) r"  
    obtains x where "A x r"
    using assms by (auto simp: CP_defs)
    
  method handle_CP_EX =  
    drule CP_HANDLED,
    erule CP_EXE,
    (elim conjE)?,
    cp_explode_prod?,
    cp_resolve_tag

  subsubsection \<open>Ex32\<close>      
    
  lemma CP_EX32E:
    assumes "CP_EX32 CP r"  
    obtains x where "CP (fst r,snd r,x)"
    using assms by (auto simp: CP_defs)
    
  method handle_CP_EX32 =  
    drule CP_HANDLED,
    erule CP_EX32E,
    (elim conjE)?,
    cp_explode_prod?,
    cp_resolve_tag
    
    
  subsubsection \<open>Join\<close>  
  lemma handle_join_take:
    assumes "CP_JOIN (\<lambda>r. a r \<and> as r) bs r"
    assumes "\<And>r. bs r \<Longrightarrow> a r"
    obtains "a r" "CP_JOIN as bs r"
    using assms
    by (auto simp: CP_defs)
    
  lemma handle_join_drop:
    assumes "CP_JOIN (\<lambda>r. a r \<and> as r) bs r" 
    obtains "CP_JOIN as bs r"  
    using assms
    by (auto simp: CP_defs)

  lemma handle_join_last_take: 
    assumes "CP_JOIN (\<lambda>r. a r) bs r"
    assumes "\<And>r. bs r \<Longrightarrow> a r"
    obtains "a r"
    using assms
    by (auto simp: CP_defs)
       
  lemma handle_join_last_drop:
    "CP_JOIN (\<lambda>r. a r) bs r \<Longrightarrow> P \<Longrightarrow> P" .
    
    
  method handle_CP_JOIN =   
    drule CP_HANDLED,
    drule asm_rl[of "CP_JOIN _ _ _"],
    (simp only: prod_eq_iff conj_assoc)?,
    (((erule handle_join_take, blast) | erule handle_join_drop)+)?,
    ((erule handle_join_last_take, blast) | erule handle_join_last_drop),
    cp_resolve_tag

  subsubsection \<open>Repeat\<close>  
  lemma CP_RPT_split_conj: "CP_RPT (\<lambda>a b. A a b \<and> B a b) a b \<Longrightarrow> CP_RPT A a b \<and> CP_RPT B a b"
    by (simp add: CP_RPT_mono CP_tag_triv)  
    
  lemma handle_rpt_take:
    "CP_RPT (\<lambda>a b. f b = f a) a b \<Longrightarrow> f b = f a"  
    by (smt (verit, del_insts) CP_RPT_def rtranclp_induct)
    
  method handle_CP_RPT =  
    (drule CP_HANDLED),
    (elim CP_RPT_split_conj[elim_format] conjE handle_rpt_take[elim_format])?,
    cp_resolve_tag
          

  method cp_normalize_step =
    drule CP_monos[THEN CP_HANDLEI] | handle_plain_eqs|handle_CP_SEQ|handle_CP_EX|handle_CP_EX32|handle_CP_JOIN|handle_CP_RPT
    
  method cp_normalize =
    (simp only: CP_simps cong: CP_tag_cong)?;
    (determ \<open>cp_normalize_step\<close>)+  
    
    
  subsection \<open>High-Level Methods\<close>
  
  definition [CP_defs]: "CP_assm CP \<equiv> (CP::bool)" \<comment> \<open>Assumption on concrete preconds\<close>
  definition [CP_defs]: "CP_cond CP \<equiv> (CP::bool)" \<comment> \<open>Proof obligation on concrete preconds\<close>
  definition [CP_defs]: "CP_simplify A B \<equiv> \<forall>r. A r \<longrightarrow> B r" \<comment> \<open>Intermediate simp-step\<close>
  
    
  lemma cp_simplify_expose_assmI:
    assumes "CP_assm CP"
    assumes "CP \<longrightarrow> CP_TAG CP'"
    shows "CP'"
    using assms by (auto simp: CP_defs)
  
  method cp_simplify_expose_assm =
    determ \<open>drule cp_simplify_expose_assmI\<close>,
    determ \<open>((thin_tac "_")+)?\<close>, rule impI,
    (cp_normalize;fail)
    
  method cp_solve_cond = 
    (cp_simplify_expose_assm+)?;
    auto simp: CP_cond_def CP_pred_def CP_simps

  lemma CP_simplify_triv: "CP_simplify (\<lambda>_. True) (\<lambda>_. True)"  
    by (auto simp: CP_defs)    
    
  lemma CP_simplifyI: 
    assumes "\<And>r. A r \<longrightarrow> CP_TAG (B r)"
    shows "CP_simplify A B"  
    using assms by (auto simp: CP_defs)

  method cp_simplify =
    rule CP_simplify_triv
    |
    rule CP_simplifyI,
    determ \<open>((thin_tac "_")+)?\<close>, rule impI,
    (cp_normalize;fail)

    
  thm CP_simps  
    
end
