theory Sorting_Insertion_Sort
imports Sorting_Setup
begin

section \<open>Insertion Sort\<close>  
        

context weak_ordering begin

definition is_insert :: "'a list \<Rightarrow> nat \<Rightarrow> 'a list nres" where "is_insert xs i \<equiv> doN {
  ASSERT (i<length xs);
  x \<leftarrow> mop_list_get xs i;

  (xs,i)\<leftarrow>WHILEIT (\<lambda>(xs',i'). 
    i'\<ge>0 \<and> i'\<le>i \<and> length xs'=length xs
  \<and> (\<forall>j\<in>{0..i'}. xs'!j = xs!j)  
  \<and> (\<forall>j\<in>{i'<..i}. xs'!j = xs!(j-1) \<and> x\<^bold><xs'!j)  
  \<and> (\<forall>j\<in>{i<..<length xs}. xs'!j=xs!j)
  ) 
    (\<lambda>(xs,i). i>0 \<and> xs!(i-1)\<^bold>>x) (\<lambda>(xs,i). doN {
      ASSERT (i>0 \<and> i<length xs);
      let xs = xs[i:=xs!(i-1)];
      let i = i-1;
      RETURN (xs,i)
    }) (xs,i);

  xs \<leftarrow> mop_list_set xs i x;  
  
  RETURN xs
}"

definition "is_insert_spec xs i xs' \<equiv> 
  \<exists>i'\<le>i.
    i<length xs
  \<and> (length xs' = length xs) 
  \<and> (\<forall>j\<in>{0..<i'}. xs'!j=xs!j)
  \<and> (xs'!i' = xs!i)
  \<and> (\<forall>j\<in>{i'<..i}. xs'!j = xs!(j-1) \<and> xs!i\<^bold><xs'!j)
  \<and> (\<forall>j\<in>{i<..<length xs}. xs'!j = xs!j)
  \<and> (i'>0 \<longrightarrow> \<not>(xs!i \<^bold>< xs'!(i'-1)) )
  "


lemma is_insert_correct: "i<length xs \<Longrightarrow> is_insert xs i \<le> SPEC (is_insert_spec xs i)"
  unfolding is_insert_def
  apply (refine_vcg WHILEIT_rule[where R="measure snd"])
  apply clarsimp_all
  apply (auto simp: nth_list_update') [2]
  apply (metis Suc_lessI Suc_pred greaterThanAtMost_iff)

  subgoal for xs' i'
    unfolding is_insert_spec_def
    apply (rule exI[where x=i']) 
    by auto
    
  done

  
lemma intv_split_auxE:  
  fixes k N :: nat
  assumes "k<N" "i'\<le>i" "i<N"
  obtains "k\<in>{0..<i'}" | "k=i'" | "k\<in>{i'<..i}" | "k\<in>{i<..<N}"  
  using assms
  by fastforce
  
  
  
lemma is_insert_spec_imp_sorted:
  "\<lbrakk>is_insert_spec xs i xs'; sorted_wrt_lt (\<^bold><) (take i xs)\<rbrakk> 
    \<Longrightarrow> sorted_wrt_lt (\<^bold><) (take (i+1) xs')"  
  (* TODO: Clean up this mess! *)
  apply (subgoal_tac "i<length xs")
  unfolding sorted_wrt_iff_nth_less le_by_lt_def
  subgoal
    apply clarsimp
    unfolding is_insert_spec_def
    apply (clarsimp;safe)
    apply (smt greaterThanAtMost_iff less_trans linorder_neqE_nat nat_Suc_less_le_imp nat_le_Suc_less_imp nz_le_conv_less unfold_lt_to_le zero_order(3))
    by (smt One_nat_def add_diff_cancel_left' atLeast0LessThan greaterThanAtMost_iff itrans le_less lessThan_iff less_Suc_eq_0_disj less_trans linorder_neqE_nat not_less_eq plus_1_eq_Suc unfold_lt_to_le wo_leI)
  subgoal
    using is_insert_spec_def by blast
  done    
  
(*  oops
  unfolding sorted_wrt_iff_nth_mono_less 
  apply auto
  unfolding is_insert_spec_def
  apply auto
  subgoal by (smt greaterThanAtMost_iff le_less le_less_trans less_Suc_eq_0_disj nat_Suc_less_le_imp nat_le_Suc_less_imp nz_le_conv_less)
  subgoal for k1 k2 i'
    apply (rule intv_split_auxE[of k1 "length xs" i' i])
    apply simp_all
    apply (rule intv_split_auxE[of k2 "length xs" i' i])
    apply simp_all [3]
    apply simp
    apply simp
    apply (metis leD less_le_trans linorder_le_less_linear linorder_neqE_nat nat_le_Suc_less_imp nz_le_conv_less zero_order(3))
    apply simp
    apply (meson greaterThanLessThan_iff not_less_eq)
    by (metis greaterThanAtMost_iff less_imp_le nat_Suc_less_le_imp)
  done    
*)  

lemma is_insert_spec_split: "is_insert_spec xs i xs' \<Longrightarrow> (\<exists>i'\<le>i. 
  xs' = take i' xs @ xs!i # drop i' (take i xs) @ drop (i+1) xs)"
  unfolding is_insert_spec_def
  apply clarify
  subgoal for i'
    apply (rule exI[where x=i'])
    apply (simp add: list_eq_iff_nth_eq)
    apply (clarsimp simp: nth_append nth_Cons split: nat.splits)
    apply (safe; clarsimp?)
    subgoal for j k
      by (metis One_nat_def Suc_le_eq add.commute add_Suc_right add_diff_cancel_left' add_diff_inverse_nat greaterThanAtMost_iff less_diff_conv plus_1_eq_Suc zero_less_Suc)
    subgoal by (metis add_Suc leI le_add_diff_inverse2)
    done
  done
  
  
lemma is_insert_spec_imp_mset_eq:
  assumes A: "is_insert_spec xs i xs'"  
  shows "mset xs' = mset xs"
proof -
  from A have L: "i<length xs"
    unfolding is_insert_spec_def by blast

  from is_insert_spec_split[OF A] obtain i' where
    I': "i'\<le>i" 
    and XS'_EQ: "xs' = take i' xs @ xs ! i # drop i' (take i xs) @ drop (i + 1) xs"
    by blast  
  
  have XS_EQ: "xs = take i' xs @ drop i' (take i xs) @ xs!i # drop (i + 1) xs"  
    using L I'
    apply auto 
    by (metis atd_lem drop_Suc_nth drop_take_drop_unsplit)  
  
  show ?thesis
    apply (rewrite in "\<hole> = _" XS'_EQ)
    apply (rewrite in "_ = \<hole>" XS_EQ)
    by (auto)  
    
qed    


definition "sort_one_more_spec xs i \<equiv> doN {
    ASSERT (i<length xs \<and> sorted_wrt_lt (\<^bold><) (take i xs)); 
    SPEC (\<lambda>xs'. mset xs' = mset xs \<and> sorted_wrt_lt (\<^bold><) (take (i+1) xs'))
  }"  

  
  
lemma is_insert_sorts_one_more[param_fo, THEN nres_relD,refine]: 
  "(is_insert, sort_one_more_spec) 
      \<in> \<langle>Id\<rangle>list_rel \<rightarrow> nat_rel \<rightarrow> \<langle>\<langle>Id\<rangle>list_rel\<rangle>nres_rel"
  apply (intro fun_relI nres_relI)    
  using is_insert_correct 
        is_insert_spec_imp_sorted is_insert_spec_imp_mset_eq
  unfolding sort_one_more_spec_def
  by (simp add: pw_le_iff refine_pw_simps; blast)

    
definition "insertion_sort_whole xs \<equiv> doN {
  (xs,_)\<leftarrow>WHILEIT (\<lambda>(xs',i). 
    i\<le>length xs' \<and> length xs'=length xs \<and> mset xs' = mset xs \<and> sorted_wrt_lt (\<^bold><) (take i xs')) 
    (\<lambda>(xs,i). i<length xs) 
    (\<lambda>(xs,i). doN {
      xs \<leftarrow> sort_one_more_spec xs i;
      ASSERT (i<length xs);
      let i=i+1;
      RETURN (xs,i)
    }) (xs,0);
  RETURN xs
}"  

lemma insertion_sort_whole_correct: 
  "insertion_sort_whole xs \<le> SPEC (sort_spec (\<^bold><) xs)"
  unfolding insertion_sort_whole_def sort_one_more_spec_def sort_spec_def sorted_sorted_wrt
  apply (refine_vcg 
    WHILEIT_rule[where R="measure (\<lambda>(_,i). length xs - i)"])           
  apply (auto dest: mset_eq_length)
  done

lemma insertion_sort_whole_refine: 
  "(insertion_sort_whole, \<lambda>xs. SPEC (sort_spec (\<^bold><) xs)) \<in> \<langle>Id\<rangle>list_rel \<rightarrow> \<langle>\<langle>Id\<rangle>list_rel\<rangle>nres_rel"
  using insertion_sort_whole_correct
  apply (intro fun_relI nres_relI)
  by auto  
  
definition "insertion_sort_whole2 xs \<equiv> doN {
  (xs,_)\<leftarrow>WHILEIT (\<lambda>(xs',i). i\<le>length xs' \<and> mset xs' = mset xs \<and> sorted_wrt_lt (\<^bold><) (take i xs')) 
    (\<lambda>(xs,i). i<length xs) 
    (\<lambda>(xs,i). doN {
      xs \<leftarrow> is_insert xs i;
      ASSERT (i<length xs);
      let i=i+1;
      RETURN (xs,i)
    }) (xs,0);
  RETURN xs
}"  

lemma insertion_sort_whole2_refines: 
  "(insertion_sort_whole2, insertion_sort_whole) \<in> \<langle>Id\<rangle>list_rel \<rightarrow> \<langle>\<langle>Id\<rangle>list_rel\<rangle>nres_rel"
  unfolding insertion_sort_whole2_def insertion_sort_whole_def
  apply (refine_rcg)
  apply refine_dref_type
  by auto
  

definition "is_insert2 xs i \<equiv> doN {
  x \<leftarrow> mop_list_get xs i;

  (xs,i)\<leftarrow>monadic_WHILEIT (\<lambda>(xs',i'). True) 
    (\<lambda>(xs,i). if i>0 then doN { y\<leftarrow>mop_list_get xs (i-1); RETURN (y\<^bold>>x) } else RETURN False) 
    (\<lambda>(xs,i). doN {
      ASSERT (i>0 \<and> i-1<length xs \<and> i<length xs);
      let xs = xs[i:=xs!(i-1)];
      let i = i-1;
      RETURN (xs,i)
    }) (xs,i);

  xs \<leftarrow> mop_list_set xs i x;  
  
  RETURN xs
}"
  
lemma is_insert2_refine: "\<lbrakk>(xs,xs')\<in>\<langle>Id\<rangle>list_rel; (i,i')\<in>Id\<rbrakk> \<Longrightarrow> is_insert2 xs i \<le> \<Down>Id (is_insert xs' i')"
  unfolding is_insert2_def is_insert_def
  apply refine_rcg
  apply refine_dref_type
  apply simp_all
  apply refine_vcg
  apply auto
  done
  
definition "is_insert3 xs l i \<equiv> doN {
  x \<leftarrow> mop_list_get xs i;

  (xs,i)\<leftarrow>monadic_WHILEIT (\<lambda>(xs',i'). True) 
    (\<lambda>(xs,i). if i>l then doN { y\<leftarrow>mop_list_get xs (i-1); RETURN (y\<^bold>>x) } else RETURN False) 
    (\<lambda>(xs,i). doN {
      ASSERT (i>0 \<and> i-1<length xs \<and> i<length xs);
      let xs = xs[i:=xs!(i-1)];
      let i = i-1;
      RETURN (xs,i)
    }) (xs,i);

  xs \<leftarrow> mop_list_set xs i x;  
  
  RETURN xs
}"


  
    
lemma is_insert3_refine: "\<lbrakk> (xs,xs')\<in>slice_rel xs\<^sub>0 l h; (i,i')\<in>idx_shift_rel l; i<h \<rbrakk> \<Longrightarrow> is_insert3 xs l i \<le>\<Down>(slice_rel xs\<^sub>0 l h) (is_insert2 xs' i')"
  unfolding is_insert2_def is_insert3_def
  supply [refine_dref_RELATES] = 
    RELATESI[of "slice_rel xs\<^sub>0 l h"] 
    RELATESI[of "slice_rel xs\<^sub>0 l h \<times>\<^sub>r idx_shift_rel l"] 
  apply (refine_rcg slice_nth_refine' slice_upd_refine')
  apply refine_dref_type
  apply (all \<open>(simp; fail)?\<close>)
  subgoal by (auto simp: idx_shift_rel_def)
  subgoal by (auto simp: idx_shift_rel_def)
  subgoal by (auto simp: idx_shift_rel_def)
  subgoal by (auto simp: idx_shift_rel_def slice_rel_def in_br_conv)
  subgoal by (auto simp: idx_shift_rel_def slice_rel_def in_br_conv)

  subgoal by (auto simp: slice_rel_def in_br_conv slice_nth idx_shift_rel_def slice_upd algebra_simps)
  done

lemma is_insert3_refine1: "\<lbrakk> (xs,xs')\<in>slice_rel xs\<^sub>0 l h; (i,i')\<in>idx_shift_rel l; i<h \<rbrakk> \<Longrightarrow> is_insert3 xs l i \<le>\<Down>(slice_rel xs\<^sub>0 l h) (is_insert xs' i')"
  using is_insert3_refine is_insert2_refine  
  by (fastforce simp: pw_le_iff refine_pw_simps)  

(*concrete_definition (in -) is_insert4 is weak_ordering.is_insert3_def*)
  
definition "insertion_sort xs l h \<equiv> doN {
  (xs,_)\<leftarrow>WHILET  
    (\<lambda>(xs,i). i<h) 
    (\<lambda>(xs,i). doN {
      xs \<leftarrow> is_insert3 xs l i;
      ASSERT (i<h);
      let i=i+1;
      RETURN (xs,i)
    }) (xs,l);
  RETURN xs
}"  
  
lemma insertion_sort_refines: "\<lbrakk> (xs,xs')\<in>slice_rel xs\<^sub>0 l h \<rbrakk> \<Longrightarrow> insertion_sort xs l h \<le>\<Down>(slice_rel xs\<^sub>0 l h) (insertion_sort_whole2 xs')"  
  unfolding insertion_sort_def insertion_sort_whole2_def  
  apply (refine_rcg is_insert3_refine1)
  supply [refine_dref_RELATES] = 
    RELATESI[of "slice_rel xs\<^sub>0 l h"] 
    RELATESI[of "slice_rel xs\<^sub>0 l h \<times>\<^sub>r idx_shift_rel l"] 
  apply refine_dref_type        
  apply auto
  apply (auto simp: idx_shift_rel_def slice_rel_def in_br_conv)
  done

lemma insertion_sort_correct: "(insertion_sort, slice_sort_spec (\<^bold><))\<in>Id \<rightarrow> Id \<rightarrow> Id \<rightarrow> \<langle>Id\<rangle>nres_rel"
  unfolding slice_sort_spec_def
  apply refine_vcg
  (* TODO: Can we do this reasoning chain more beautiful? *)
  apply (rule order_trans) apply (rule insertion_sort_refines[OF slice_in_slice_rel]; simp)
  apply (rule order_trans) apply (rule conc_fun_mono[THEN monoD]) apply (rule insertion_sort_whole2_refines[param_fo, THEN nres_relD, simplified, OF refl])
  apply (rule order_trans) apply (rule conc_fun_mono[THEN monoD]) apply (rule insertion_sort_whole_correct)
  apply (auto simp: pw_le_iff refine_pw_simps slice_rel_def in_br_conv)
  done
  
  
end  
  
context sort_impl_context begin
  sepref_register is_insert3
  
  sepref_def is_insert_impl is "uncurry2 (PR_CONST is_insert3)" 
    :: "(array_assn elem_assn)\<^sup>d *\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k \<rightarrow>\<^sub>a array_assn elem_assn"
    unfolding is_insert3_def PR_CONST_def
    supply [[goals_limit = 1]]
    apply (annot_snat_const "TYPE(size_t)")
    by sepref
  
  sepref_register insertion_sort
    
  sepref_def insertion_sort_impl is "uncurry2 (PR_CONST insertion_sort)" 
    :: "(array_assn elem_assn)\<^sup>d *\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k \<rightarrow>\<^sub>a array_assn elem_assn "
    unfolding insertion_sort_def PR_CONST_def
    apply (annot_snat_const "TYPE(size_t)")
    by sepref
    
  (*  
  lemmas insertion_sort_impl_hnr[sepref_fr_rules] = insertion_sort_impl.refine[FCOMP insertion_sort_correct]
  *)
        
end    

(*
global_interpretation insort_interp: sort_impl_context "(\<le>)" "(<)" ll_icmp_ult unat_assn
  defines insort_interp_is_insert_impl = insort_interp.is_insert_impl
      and insort_interp_insertion_sort_impl = insort_interp.insertion_sort_impl
  by (rule unat_sort_impl_context)


export_llvm "insort_interp_insertion_sort_impl :: 64 word ptr \<Rightarrow> _"
*)

end
