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
    assumes EQI: "vassn_tag \<Gamma> \<Longrightarrow> CP_cond (srci = dsti)"
    shows "hn_refine \<Gamma> (Mreturn ()) (hn_invalid R src srci ** hn_ctxt R dst dsti ** F) unit_assn (\<lambda>_. True) (unborrow$src$dst)"
    apply (rule hn_refine_vassn_tagI)
    apply (rule hn_refine_cons_pre[OF FRAME])
    apply (rule hn_refineI)
    using EQI
    unfolding unborrow_def CP_defs
    apply (simp add: refine_pw_simps)
    unfolding hn_ctxt_def invalid_assn_def pure_def
    apply vcg'
    done
  
  lemma unborrow_nofail[refine_pw_simps]: "nofail (unborrow a b) \<longleftrightarrow> a=b" by (auto simp: unborrow_def refine_pw_simps)  
  
  (*
  text \<open>Assertion that adds constraint on concrete value. Used to carry through concrete equalities.\<close>
  definition "cnc_assn \<phi> A a c \<equiv> \<up>(\<phi> c) ** A a c"
    
  lemma norm_ceq_assn[named_ss sepref_frame_normrel]: "hn_ctxt (cnc_assn \<phi> A) a c = (\<up>(\<phi> c) ** hn_ctxt A a c)"
    unfolding hn_ctxt_def cnc_assn_def by simp
  
  lemma cnc_assn_prod_conv[named_ss sepref_frame_normrel]:
    shows "\<And>A B \<phi>. A \<times>\<^sub>a cnc_assn \<phi> B = cnc_assn (\<phi> o snd) (A\<times>\<^sub>aB)"
      and "\<And>A B \<phi>. cnc_assn \<phi> A \<times>\<^sub>a B = cnc_assn (\<phi> o fst) (A\<times>\<^sub>aB)"
    unfolding cnc_assn_def
    by (auto simp: sep_algebra_simps fun_eq_iff)
  *)
    
  (* TODO: Move *)
  lemma wpa_comm_conjI: "\<lbrakk>wpa A c Q s; wpa A c Q' s\<rbrakk> \<Longrightarrow> wpa A c (\<lambda>r s. Q r s \<and> Q' r s) s"
    unfolding wpa_def 
    apply (drule (1) wp_comm_conjI)
    by (erule wp_monoI; auto) 
  
  (* TODO: Move *)
  lemma htriple_conj_pure:
    assumes "htriple P c Q"
    assumes "htriple P c (\<lambda>r. \<up>\<Phi> r ** sep_true)"
    shows "htriple P c (\<lambda>r. \<up>\<Phi> r ** Q r)"
  proof (rule htripleI)  
    fix asf s
    assume "STATE asf P s"
    
    from wpa_comm_conjI[OF assms[THEN htripleD,OF this]]
    show "wpa (asf) c (\<lambda>r. STATE asf (\<up>\<Phi> r \<and>* Q r)) s"
      apply (rule wpa_monoI)
      apply (simp add: STATE_extract(2))
      by auto
      
  qed    
  
  text \<open>Rule to prove a-posteriori constraint (Only useful for simple programs.
    TODO: More partial Hoare-triples would make this more useful, e.g., 
      we could assume assertions, preconditions, and even termination!
  )\<close>    
  lemma hnr_ceq_assnI:
    assumes HNR: "hn_refine \<Gamma> c \<Gamma>' R CP\<^sub>1 a"
    assumes HT: "llvm_htriple \<Gamma> c (\<lambda>x'. \<up>(CP\<^sub>2 x') ** sep_true)"
    assumes IMP: "\<And>x'. CP\<^sub>1 x' \<and> CP\<^sub>2 x' \<Longrightarrow> CP x'"
    shows "hn_refine \<Gamma> c \<Gamma>' R CP a"
  proof (rule hn_refine_nofailI)
    assume NF: "nofail a"
  
    show ?thesis
      apply (rule hn_refineI)
      apply (rule cons_post_rule)
      apply (rule htriple_conj_pure[OF HNR[THEN hn_refineD[OF _ NF]] HT])
      apply (auto simp: sep_algebra_simps IMP)
      done
      
  qed    
  

end
