theory Sorting_Final_insertion_Sort
imports Sorting_Quicksort_Scheme Sorting_Unguarded_Insertion_Sort
begin

context weak_ordering begin

  definition "final_insertion_sort xs \<equiv> doN {
    ASSERT (1 < length xs);
    if length xs \<le> is_threshold then
      gen_insertion_sort True 1 (length xs) xs
    else doN {
      xs \<leftarrow> gen_insertion_sort True 1 is_threshold xs;
      gen_insertion_sort False is_threshold (length xs) xs
    }
  }"  
  
  lemma transfer_guard_over_initial_sorting:
    assumes PS: "part_sorted_wrt (le_by_lt (\<^bold><)) n xs"
    assumes B: "length xs' = length xs" "0<n" "n \<le> i" "i < length xs"
    assumes DEQ: "drop n xs' = drop n xs" 
    assumes SORTED: "sort_spec (\<^bold><) (slice 0 n xs) (slice 0 n xs')" 
    assumes LT: "xs' ! i \<^bold>< xs' ! 0" 
    shows False
  proof -
    from part_sorted_guardedI[OF PS \<open>n\<le>i\<close> \<open>i < length xs\<close>] have GUARD: "xs!0 \<^bold>\<le> xs!i"
      by (auto simp: le_by_lt)
  
    have [simp]: "xs!i = xs'!i" using B DEQ by (metis atLeastLessThan_iff conv_idxs_to_drop_eq)
      
    have "xs!0 \<in># mset (slice 0 n xs)" using B
      apply (auto simp: Misc.slice_def)
      by (metis atLeast0LessThan image_eqI le_less_trans lessThan_iff less_imp_le_nat nth_image)
    hence "xs!0 \<in># mset (slice 0 n xs')" using SORTED unfolding sort_spec_def by auto 
    then obtain j where "j<n" and [simp]: "xs!0=xs'!j" using B by (auto simp: in_set_conv_nth slice_nth)
    have "xs'!0 \<^bold>\<le> xs'!j" using SORTED B \<open>j<n\<close>
      apply (cases "j=0")
      apply simp
      unfolding sort_spec_def by (auto simp: le_by_lt sorted_wrt_iff_nth_less slice_nth)
    then show False using LT GUARD
      apply simp
      using local.trans wo_leD by blast
      
  qed
   

  lemma final_insertion_sort_correct: 
    "\<lbrakk>part_sorted_wrt (le_by_lt (\<^bold><)) is_threshold xs; 1 < length xs\<rbrakk> \<Longrightarrow> final_insertion_sort xs \<le> SPEC (sort_spec (\<^bold><) xs)"
    unfolding final_insertion_sort_def
    apply (refine_vcg gen_insertion_sort_correct[THEN order_trans])
    apply simp_all
    subgoal apply (rule sorted_wrt01) by auto  
    subgoal
      unfolding slice_sort_spec_def apply refine_vcg
      apply (auto simp: ) using slice_complete by metis
    subgoal apply (rule sorted_wrt01) by auto  
    subgoal
      unfolding slice_sort_spec_def 
      apply (refine_vcg gen_insertion_sort_correct[THEN order_trans])
      apply (simp_all)
      subgoal by (simp add: Misc.slice_def sort_spec_def) 
      subgoal for xs'
        apply (clarsimp)
        by (auto intro!: transfer_guard_over_initial_sorting)
      subgoal unfolding slice_sort_spec_def apply refine_vcg
        apply (auto simp: sort_spec_def)
        apply (metis Misc.slice_def append_take_drop_id drop0 drop_take slice_complete union_code)
        by (metis slice_complete)
      done                
    done    
  
  definition "final_insertion_sort2 xs l h \<equiv> doN {
    ASSERT (l<h);
    if h-l \<le> is_threshold then
      gen_insertion_sort2 True l (l+1) h xs
    else doN {
      xs \<leftarrow> gen_insertion_sort2 True l (l+1) (l+is_threshold) xs;
      gen_insertion_sort2 False l (l+is_threshold) h xs
    }
  }"  
    
  lemma final_insertion_sort2_refine: "\<lbrakk>(xsi,xs) \<in> slicep_rel l h\<rbrakk> 
    \<Longrightarrow> final_insertion_sort2 xsi l h \<le> \<Down>(slice_rel xsi l h) (final_insertion_sort xs)"  
    unfolding final_insertion_sort2_def final_insertion_sort_def
    apply (refine_rcg gen_insertion_sort2_refine)
    apply clarsimp_all
    apply (auto simp: slicep_rel_def idx_shift_rel_def) [7]
    apply (subst slice_rel_rebase, assumption)
    apply (refine_rcg gen_insertion_sort2_refine)
    apply (auto simp: slice_rel_alt idx_shift_rel_def slicep_rel_def)
    done
  
    
    
    
  lemma final_insertion_sort2_correct: 
    assumes [simplified, simp]: "(xs',xs)\<in>Id" "(l',l)\<in>Id" "(h',h)\<in>Id"   
    shows "final_insertion_sort2 xs' l' h' \<le> final_sort_spec xs l h"
  proof (simp,rule le_nofailI)
    assume "nofail (final_sort_spec xs l h)"
    hence PS: "part_sorted_wrt (le_by_lt (\<^bold><)) is_threshold (slice l h xs)"
      and LB: "h-l>1" "h \<le> length xs"
      unfolding final_sort_spec_def slice_sort_spec_def by (auto simp add: refine_pw_simps)
  
    from LB have LENGT1: "1 < length (slice l h xs)" by auto
      
    
    have SLR: "(xs, slice l h xs) \<in> slicep_rel l h" using LB
      by (auto simp: slicep_rel_def)
    
    note final_insertion_sort2_refine[OF SLR]
    also note final_insertion_sort_correct[OF PS LENGT1]
    also note slice_sort_spec_refine_sort'_sym[OF SLR refl refl refl] 
    also have "slice_sort_spec (\<^bold><) xs l h \<le> final_sort_spec xs l h"
      unfolding final_sort_spec_def using PS LB by simp
    finally show "final_insertion_sort2 xs l h \<le> final_sort_spec xs l h" .
  qed
  
  
end
  
context sort_impl_context begin
  sepref_register final_insertion_sort2  
  sepref_def final_insertion_sort_impl is "uncurry2 (PR_CONST final_insertion_sort2)" 
    :: "[\<lambda>_. True]\<^sub>c (woarray_slice_assn elem_assn)\<^sup>d *\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k 
      \<rightarrow> woarray_slice_assn elem_assn [\<lambda>((ai,_),_) r. r=ai]\<^sub>c"
    unfolding final_insertion_sort2_def PR_CONST_def
    apply (annot_snat_const "TYPE(size_t)")
    by sepref

end

context parameterized_weak_ordering begin  
  definition "final_insertion_sort_param cparam xs l h \<equiv> doN {
    ASSERT (l<h);
    if h-l \<le> is_threshold then
      gen_insertion_sort_param True cparam l (l+1) h xs
    else doN {
      xs \<leftarrow> gen_insertion_sort_param True cparam l (l+1) (l+is_threshold) xs;
      gen_insertion_sort_param False cparam l (l+is_threshold) h xs
    }
  }"  

  lemma final_insertion_sort_param_refine[refine]: "\<lbrakk>
    (l',l)\<in>Id; (h',h)\<in>Id; (xs',xs)\<in>cdom_list_rel cparam
  \<rbrakk> \<Longrightarrow> final_insertion_sort_param cparam xs' l' h' 
    \<le> \<Down>(cdom_list_rel cparam) (WO.final_insertion_sort2 cparam xs l h)"  
    unfolding final_insertion_sort_param_def WO.final_insertion_sort2_def
    apply refine_rcg
    apply auto
    done
  
end

context parameterized_sort_impl_context begin

  sepref_register final_insertion_sort_param
  sepref_def final_insertion_sort_param_impl is "uncurry3 (PR_CONST final_insertion_sort_param)" 
    :: "[\<lambda>_. True]\<^sub>c cparam_assn\<^sup>k *\<^sub>a wo_assn\<^sup>d *\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k 
      \<rightarrow> wo_assn [\<lambda>(((_,ai),_),_) r. r=ai]\<^sub>c"
    unfolding final_insertion_sort_param_def PR_CONST_def
    apply (annot_snat_const "TYPE(size_t)")
    by sepref

end


end
