theory Proto_Sepref_Borrow
imports Sepref
begin

  (* Simple-Minded borrowing for sepref.
  
    Idea: When we can prove that we have not changed an object abstractly, 
      and its concrete value is still the same, we can reinstantiate it 
      after it has been invalidated.
      
  *)

  text \<open>Operation to reinstantiate dst, by moving source. 
    Implementations will also require a proof that the concrete objects are equal!
  \<close>
  definition "unborrow src dst \<equiv> doN {ASSERT (src=dst); RETURN ()}"
  sepref_register unborrow

  lemma unborrow_correct[refine_vcg]: "s=d \<Longrightarrow> unborrow s d \<le> SPEC (\<lambda>r. r=())"
    unfolding unborrow_def by auto
  
  
  lemma unborrow_rule[sepref_comb_rules]:
    assumes FRAME: "\<Gamma> \<turnstile> hn_ctxt R src srci ** hn_invalid R dst dsti ** F"
    assumes [simp]: "vassn_tag \<Gamma> \<Longrightarrow> srci = dsti"
    shows "hn_refine \<Gamma> (return ()) (hn_invalid R src srci ** hn_ctxt R dst dsti ** F) unit_assn (unborrow$src$dst)"
    apply (rule hn_refine_vassn_tagI)
    apply (rule hn_refine_cons_pre[OF FRAME])
    apply (rule hn_refineI)
    unfolding unborrow_def
    apply (simp add: refine_pw_simps)
    unfolding hn_ctxt_def invalid_assn_def pure_def
    by vcg'
  
  lemma unborrow_nofail[refine_pw_simps]: "nofail (unborrow a b) \<longleftrightarrow> a=b" by (auto simp: unborrow_def refine_pw_simps)  
  
  
  text \<open>Assertion that adds constraint on concrete value. Used to carry through concrete equalities.\<close>
  definition "cnc_assn \<phi> A a c \<equiv> \<up>(\<phi> c) ** A a c"
    
  lemma norm_ceq_assn[named_ss sepref_frame_normrel]: "hn_ctxt (cnc_assn \<phi> A) a c = (\<up>(\<phi> c) ** hn_ctxt A a c)"
    unfolding hn_ctxt_def cnc_assn_def by simp
  
  lemma cnc_assn_prod_conv[named_ss sepref_frame_normrel]:
    shows "\<And>A B \<phi>. A \<times>\<^sub>a cnc_assn \<phi> B = cnc_assn (\<phi> o snd) (A\<times>\<^sub>aB)"
      and "\<And>A B \<phi>. cnc_assn \<phi> A \<times>\<^sub>a B = cnc_assn (\<phi> o fst) (A\<times>\<^sub>aB)"
    unfolding cnc_assn_def
    by (auto simp: sep_algebra_simps fun_eq_iff)
    
    
  text \<open>Rule to prove a-posteriori constraint (Only useful for simple programs.
    TODO: More partial Hoare-triples would make this more useful, e.g., 
      we could assume assertions, preconditions, and even termination!
  )\<close>    
  lemma hnr_ceq_assnI:
    assumes HNR: "hn_refine \<Gamma> c \<Gamma>' R a"
    assumes HT: "llvm_htriple \<Gamma> c (\<lambda>x'. \<up>(\<phi> x') ** sep_true)"
    shows "hn_refine \<Gamma> c \<Gamma>' (cnc_assn \<phi> R) a"
  proof (rule hn_refine_nofailI)
    assume NF: "nofail a"
  
    show ?thesis
      apply (rule hn_refineI)
      apply (rule cons_post_rule)
      apply (rule htriple_conj_pure[OF HNR[THEN hn_refineD[OF _ NF]] HT])
      apply (auto simp: sep_algebra_simps pred_lift_extract_simps cnc_assn_def)
      done
      
  qed    
  

end
