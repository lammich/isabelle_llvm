section \<open>Array List with Pure Refinement of Elements\<close>
theory LLVM_DS_Array_List_Pure
imports LLVM_DS_List_Assn LLVM_DS_Array_List
begin
  (* TODO: Move *)

  definition "pure_list_assn A = mk_pure_assn (\<lambda>xs ys. is_pure A \<and> list_all2 (\<flat>\<^sub>pA) xs ys)"

  lemma pure_list_assn_empty_iff:
    "\<upharpoonleft>(pure_list_assn A) [] [] = \<up>(is_pure A)"
    unfolding pure_list_assn_def
    by (auto)
    
  lemma pure_list_assn_emptyI: 
    "PRECOND (SOLVE_ASM (is_pure A)) \<Longrightarrow> \<box> \<turnstile> \<upharpoonleft>\<^sub>p(pure_list_assn A) [] []"  
    unfolding vcg_tag_defs pure_list_assn_def
    by (auto simp: sep_algebra_simps)
    
    
    
    
  lemma pure_list_assn_split2:  "\<upharpoonleft>(pure_list_assn A) (x#xs) (ys) 
      = (EXS y ys'. \<upharpoonleft>A x y ** \<upharpoonleft>(pure_list_assn A) xs ys' ** \<up>(ys=y#ys'))"
    apply (cases ys)  
    unfolding pure_list_assn_def
    by (auto simp: sep_algebra_simps pred_lift_extract_simps extract_pure_assn fun_eq_iff)

  lemma pure_list_assn_split1: "\<upharpoonleft>(pure_list_assn A) (xs) (y#ys) 
      = (EXS x xs'. \<upharpoonleft>A x y ** \<upharpoonleft>(pure_list_assn A) xs' ys ** \<up>(xs=x#xs'))"
    apply (cases xs)  
    unfolding pure_list_assn_def
    by (auto simp: sep_algebra_simps pred_lift_extract_simps extract_pure_assn fun_eq_iff)
    
  lemmas pure_list_assn_simps = pure_list_assn_empty_iff pure_list_assn_split2 pure_list_assn_split1
    
  lemma pure_list_assn_pure_partD[vcg_prep_ext_rules]: "pure_part (\<upharpoonleft>(pure_list_assn A) xs ys) 
    \<Longrightarrow> length xs = length ys \<and> is_pure A \<and> list_all2 (\<flat>\<^sub>pA) xs ys"
    unfolding pure_list_assn_def
    by (auto simp: list_all2_lengthD) 
  
  lemma pure_list_assn_pure[is_pure_rule]: "is_pure (pure_list_assn A)"
    unfolding pure_list_assn_def by auto
    
  lemma pure_list_assn_extract:  
    assumes "i < length xs"
    shows "\<upharpoonleft>(pure_list_assn A) xs ys \<turnstile> \<upharpoonleft>(pure_list_assn A) xs ys ** \<upharpoonleft>A (xs!i) (ys!i)"
    using assms
    unfolding pure_list_assn_def
    apply (auto simp: sep_algebra_simps entails_lift_extract_simps)
    by (simp add: extract_pure_assn list_all2_nthD pure_true_conv)

  lemma pure_list_assn_extract':  
    assumes "PRECOND (SOLVE_ASM (\<flat>\<^sub>p(pure_list_assn A) xs ys))" 
        and "PRECOND (SOLVE_AUTO_DEFER (i < length xs))"
    shows "\<box> \<turnstile> \<upharpoonleft>A (xs!i) (ys!i)"
    using assms 
    by (simp add: vcg_tag_defs list_all2_nthD prepare_pure_assn pure_fri_rule pure_list_assn_def)
    
        
  lemma pure_list_assn_upd:  
    assumes "i < length xs" "\<flat>\<^sub>pA x y"
    shows "\<upharpoonleft>(pure_list_assn A) xs ys \<turnstile> \<upharpoonleft>(pure_list_assn A) (xs[i:=x]) (ys[i:=y])"
    using assms
    unfolding pure_list_assn_def
    apply (auto simp: sep_algebra_simps entails_lift_extract_simps)
    by (simp add: list_all2_update_cong pure_true_conv)
      
  lemma pure_list_assn_upd':  
    assumes "PRECOND (SOLVE_ASM (\<flat>\<^sub>p(pure_list_assn A) xs ys))" 
        and "PRECOND (SOLVE_AUTO_DEFER (i < length xs))" 
    shows "\<upharpoonleft>A x y \<turnstile> \<upharpoonleft>\<^sub>p(pure_list_assn A) (xs[i:=x]) (ys[i:=y])"
    using assms unfolding vcg_tag_defs
    by (smt bury_pure_assn dr_assn_pure_asm_prefix_def entails_eq_iff entails_lift_extract_simps(1) entails_pureI prepare_pure_assn pure_list_assn_def pure_list_assn_pure_partD pure_list_assn_upd sel_mk_pure_assn(1) sep_drule(1))
    
  lemma pure_list_assn_push_back':
    assumes "PRECOND (SOLVE_ASM (\<flat>\<^sub>p(pure_list_assn A) xs ys))" 
    shows "\<upharpoonleft>A x y \<turnstile> \<upharpoonleft>\<^sub>p(pure_list_assn A) (xs@[x]) (ys@[y])"
    using assms unfolding vcg_tag_defs pure_list_assn_def
    by (auto simp: sep_algebra_simps entails_lift_extract_simps extract_pure_assn list_all2_appendI)
    
  lemma pure_list_assn_pop_back':  
    assumes "PRECOND (SOLVE_ASM (\<flat>\<^sub>p(pure_list_assn A) xs ys))" 
        and "PRECOND (SOLVE_AUTO_DEFER (xs \<noteq> []))"
      shows "\<box> \<turnstile> \<upharpoonleft>\<^sub>p(pure_list_assn A) (butlast xs) (butlast ys)"
    using assms unfolding vcg_tag_defs pure_list_assn_def
    apply (auto)  
    by (metis PRECONDI SOLVE_DEFAULT_AUTOI butlast_conv_take fri_pure_rl list_all2_lengthD list_all2_takeI)
    
  lemma pure_list_assn_last':  
    assumes "PRECOND (SOLVE_ASM (\<flat>\<^sub>p(pure_list_assn A) xs ys))" 
        and "PRECOND (SOLVE_AUTO_DEFER (xs \<noteq> []))"
      shows "\<box> \<turnstile> \<upharpoonleft>A (last xs) (last ys)"
    using assms unfolding vcg_tag_defs pure_list_assn_def
    apply auto
    by (smt entails_eq_iff extract_pure_assn hd_rev list.rel_sel list_all2_rev pure_true_conv rev_is_Nil_conv)
    
  subsection \<open>Definition of Assertion\<close>      
  definition "arl_pure_assn A \<equiv> 
    mk_assn (\<lambda>xs p. EXS ys. \<upharpoonleft>arl_assn ys p ** \<upharpoonleft>(pure_list_assn A) xs ys)"  
    
      
  lemma arl_pure_assn_init_pure: 
    "PRECOND (SOLVE_AUTO (is_pure A)) \<Longrightarrow> PRECOND (SOLVE_AUTO (4 < LENGTH('l))) \<Longrightarrow> 
      \<box> \<turnstile> \<upharpoonleft>(arl_pure_assn A) [] (init::(_,'l::len2)array_list)"  
    unfolding arl_pure_assn_def vcg_tag_defs
    supply [fri_rules] = arl_assn_init_pure[simplified] pure_list_assn_emptyI
    supply [simp] = pure_list_assn_empty_iff
    apply clarsimp  
    apply (rule ENTAILSD)
    by vcg
    
    
  subsection \<open>Operations\<close>  
    
  lemma arlp_nth_rule[vcg_rules]: "llvm_htriple
    (\<upharpoonleft>(arl_pure_assn A) al ali ** \<upharpoonleft>snat.assn i ii ** \<up>(i<length al))
    (arl_nth ali ii)
    (\<lambda>x. \<upharpoonleft>A (al!i) x ** \<upharpoonleft>(arl_pure_assn A) al ali)"  
    unfolding arl_pure_assn_def
    supply [fri_rules] = pure_list_assn_extract'
    by vcg
    
  lemma array_of_arlp_nth_rule[vcg_rules]: "llvm_htriple 
    (\<upharpoonleft>(arl_pure_assn A) xs a ** \<upharpoonleft>snat.assn i ii ** \<up>(i < length xs))
    (array_nth (array_of_arl a) ii)
    (\<lambda>xi. \<upharpoonleft>(arl_pure_assn A) xs a ** \<upharpoonleft>A (xs!i) xi)"
    unfolding arl_pure_assn_def
    supply [fri_rules] = pure_list_assn_extract'
    by vcg
    
    
  lemma arlp_upd_rule[vcg_rules]: "llvm_htriple 
    (\<upharpoonleft>(arl_pure_assn A) al ali ** \<upharpoonleft>snat.assn i ii ** \<up>(i<length al) ** \<upharpoonleft>A x xi)
    (arl_upd ali ii xi)
    (\<lambda>ali. \<upharpoonleft>(arl_pure_assn A) (al[i:=x]) ali)"  
    unfolding arl_pure_assn_def
    supply [fri_rules] = pure_list_assn_upd'
    by vcg
    
  lemma arlp_push_back_rule[vcg_rules]: "llvm_htriple
    (\<upharpoonleft>(arl_pure_assn A) al (ali::(_,'l::len2)array_list) ** \<upharpoonleft>A x xi ** \<up>\<^sub>d(length al + 1 < max_snat LENGTH('l)))
    (arl_push_back ali xi)
    (\<lambda>ali. \<upharpoonleft>(arl_pure_assn A) (al@[x]) ali)"  
    unfolding arl_pure_assn_def
    supply [fri_rules] = pure_list_assn_push_back'
    by vcg
    
  lemma arlp_pop_back_rule[vcg_rules]:
    "llvm_htriple 
      (\<upharpoonleft>(arl_pure_assn A) al ali ** \<up>\<^sub>d(al\<noteq>[])) 
      (arl_pop_back ali) 
      (\<lambda>(xi,ali). \<upharpoonleft>(arl_pure_assn A) (butlast al) ali ** \<upharpoonleft>A (last al) xi)"
    unfolding arl_pure_assn_def
    supply [fri_rules] = pure_list_assn_pop_back' pure_list_assn_last'
    by vcg

  (* TODO: Why isn't pure part properly extracted from \<flat>\<^sub>ppure_list_assn?*)  
  lemma list_assn_len_simp: "\<flat>\<^sub>p(pure_list_assn A) xs ys \<Longrightarrow> length ys = length xs"
    unfolding pure_list_assn_def by (auto dest: list_all2_lengthD)
    
    
  lemma arlp_len_rule[vcg_rules]:  
    "llvm_htriple
      (\<upharpoonleft>(arl_pure_assn A) al ali)
      (arl_len ali)
      (\<lambda>li. \<upharpoonleft>(arl_pure_assn A) al ali ** \<upharpoonleft>snat.assn (length al) li)"
    unfolding arl_pure_assn_def
    (* TODO: Why isn't pure part properly extracted from \<flat>\<^sub>ppure_list_assn?*)  
    supply [simp] = list_assn_len_simp 
    by vcg
    
  lemma arlp_free_rl[vcg_rules]:
    "llvm_htriple
      (\<upharpoonleft>(arl_pure_assn A) al ali)
      (arl_free ali)
      (\<lambda>_. \<box>)"
    unfolding arl_pure_assn_def
    by vcg
        
    
end
