section \<open>Introsort (roughly libstdc++ version)\<close>
theory Sorting_Introsort
imports 
  Sorting_Final_insertion_Sort Sorting_Heapsort Sorting_Log2 
  Sorting_Quicksort_Partition
  Sorting_Strings
begin


context weak_ordering begin


  (* Assemble an introsort loop, using the partitioner and heap-sort *)  
  
  definition introsort_aux4 :: "'a list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a list nres" where "introsort_aux4 xs l h d \<equiv> RECT (\<lambda>introsort_aux (xs,l,h,d). doN {
    ASSERT (l\<le>h);
    if h-l > is_threshold then doN {
      if d=0 then
        heapsort xs l h
      else doN {
        (xs,m)\<leftarrow>partition_pivot xs l h;
        xs \<leftarrow> introsort_aux (xs,l,m,d-1);
        xs \<leftarrow> introsort_aux (xs,m,h,d-1);
        RETURN xs
      }
    }
    else
      RETURN xs
  }) (xs,l,h,d)"


  lemma introsort_aux4_refine: "introsort_aux4 xs l h d \<le> (introsort_aux3 xs l h d)"
    unfolding introsort_aux4_def introsort_aux3_def
    apply (rule refine_IdD)
    apply (refine_rcg heapsort_correct' partition_pivot_correct)
    apply refine_dref_type
    apply simp_all 
    done

  lemmas introsort_aux4_correct = order_trans[OF introsort_aux4_refine introsort_aux3_correct, THEN refine_IdI]

  definition "introsort4 xs l h \<equiv> doN {
    ASSERT(l\<le>h);
    if h-l>1 then doN {
      xs \<leftarrow> introsort_aux4 xs l h (Discrete.log (h-l)*2);
      xs \<leftarrow> final_insertion_sort2 xs l h;
      RETURN xs
    } else RETURN xs
  }"  

  lemma introsort4_refine: "introsort4 xs l h \<le> introsort3 xs l h"
    unfolding introsort4_def introsort3_def
    apply (rule refine_IdD)
    apply (refine_rcg introsort_aux4_correct final_insertion_sort2_correct[THEN refine_IdI])
    by auto

  lemmas introsort4_correct = order_trans[OF introsort4_refine introsort3_correct]

end

lemma introsort_depth_limit_in_bounds_aux: (* TODO: Move depth-computation into own (inline) function *)
  assumes "n < max_snat N" "1<N" shows "Discrete.log (n) * 2 < max_snat N"
proof (cases "n=0")
  case True thus ?thesis using assms by auto
next
  case [simp]: False  
  have ?thesis if "Discrete.log (n) < max_snat (N-1)"
    using that \<open>1<N\<close> unfolding max_snat_def
    by (metis nat_mult_power_less_eq pos2 semiring_normalization_rules(33))
  moreover have "Discrete.log (n) < max_snat (N-1)"
    apply (rule discrete_log_ltI)
    using assms apply (auto simp: max_snat_def)
    by (smt Suc_diff_Suc leI le_less_trans n_less_equal_power_2 nat_power_less_imp_less not_less_eq numeral_2_eq_2 numeral_2_eq_2 zero_order(3))
  ultimately show ?thesis .
qed  
  


context sort_impl_context begin

sepref_register introsort_aux4
sepref_def introsort_aux_impl is "uncurry3 (PR_CONST introsort_aux4)" :: "(arr_assn)\<^sup>d *\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k \<rightarrow>\<^sub>a arr_assn"
  unfolding introsort_aux4_def PR_CONST_def
  apply (annot_snat_const "TYPE(size_t)")
  by sepref
  
  
  
sepref_register introsort4
sepref_def introsort_impl is "uncurry2 (PR_CONST introsort4)" :: "(arr_assn)\<^sup>d *\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k \<rightarrow>\<^sub>a arr_assn"
  unfolding introsort4_def PR_CONST_def
  apply (annot_snat_const "TYPE(size_t)")
  supply [intro!] = introsort_depth_limit_in_bounds_aux 
  by sepref

  
lemma introsort4_refine_ss_spec: "(PR_CONST introsort4, slice_sort_spec (\<^bold><))\<in>Id\<rightarrow>Id\<rightarrow>Id\<rightarrow>\<langle>Id\<rangle>nres_rel"  
  using introsort4_correct by (auto intro: nres_relI)
  
theorem introsort_impl_correct: "(uncurry2 introsort_impl, uncurry2 (slice_sort_spec (\<^bold><))) \<in> arr_assn\<^sup>d *\<^sub>a snat_assn\<^sup>k *\<^sub>a snat_assn\<^sup>k \<rightarrow>\<^sub>a arr_assn"  
  using introsort_impl.refine[FCOMP introsort4_refine_ss_spec] .
  
  
end



context parameterized_weak_ordering begin
  (* TODO: Move *)
  lemmas heapsort_param_refine'[refine] = heapsort_param_refine[unfolded heapsort1.refine[OF WO.weak_ordering_axioms, symmetric]]
  
  
  definition introsort_aux_param :: "'cparam \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a list nres" where 
    "introsort_aux_param cparam xs l h d \<equiv> RECT (\<lambda>introsort_aux (xs,l,h,d). doN {
    ASSERT (l\<le>h);
    if h-l > is_threshold then doN {
      if d=0 then
        heapsort_param cparam xs l h
      else doN {
        (xs,m)\<leftarrow>partition_pivot_param cparam xs l h;
        xs \<leftarrow> introsort_aux (xs,l,m,d-1);
        xs \<leftarrow> introsort_aux (xs,m,h,d-1);
        RETURN xs
      }
    }
    else
      RETURN xs
  }) (xs,l,h,d)"


  lemma introsort_aux_param_refine[refine]: 
    "\<lbrakk> (xs',xs)\<in>cdom_list_rel cparam; (l',l)\<in>Id; (h',h)\<in>Id; (d',d)\<in>Id
    \<rbrakk> \<Longrightarrow> introsort_aux_param cparam xs' l' h' d' \<le>\<Down>(cdom_list_rel cparam) (WO.introsort_aux4 cparam xs l h d)"
    unfolding introsort_aux_param_def WO.introsort_aux4_def 
    supply [refine_dref_RELATES] = RELATESI[of "cdom_list_rel cparam"]
    apply (refine_rcg)
    apply refine_dref_type
    apply simp_all 
    done

  definition "introsort_param cparam xs l h \<equiv> doN {
    ASSERT(l\<le>h);
    if h-l>1 then doN {
      xs \<leftarrow> introsort_aux_param cparam xs l h (Discrete.log (h-l)*2);
      xs \<leftarrow> final_insertion_sort_param cparam xs l h;
      RETURN xs
    } else RETURN xs
  }"  

  lemma introsort_param_refine: 
    "\<lbrakk> (xs',xs)\<in>cdom_list_rel cparam; (l',l)\<in>Id; (h',h)\<in>Id
    \<rbrakk> \<Longrightarrow> introsort_param cparam xs' l' h' \<le> \<Down>(cdom_list_rel cparam) (WO.introsort4 cparam xs l h)"
    unfolding introsort_param_def WO.introsort4_def
    apply (refine_rcg)
    by auto

      
  lemma introsort_param_correct: 
    assumes "(xs',xs)\<in>Id" "(l',l)\<in>Id" "(h',h)\<in>Id"
    shows "introsort_param cparam xs' l' h' \<le> pslice_sort_spec cdom pless cparam xs l h"
  proof -
    note introsort_param_refine
    also note WO.introsort4_correct
    also note slice_sort_spec_xfer
    finally show ?thesis 
      unfolding pslice_sort_spec_def
      apply refine_vcg
      using assms unfolding cdom_list_rel_alt
      by (simp add: in_br_conv)
    
  qed
  
  lemma introsort_param_correct': 
    shows "(PR_CONST introsort_param, PR_CONST (pslice_sort_spec cdom pless)) \<in> Id \<rightarrow> Id \<rightarrow> Id \<rightarrow> Id \<rightarrow> \<langle>Id\<rangle>nres_rel"
    using introsort_param_correct 
    apply (intro fun_relI nres_relI) 
    by simp
  
    
    
    
end

context parameterized_sort_impl_context begin


sepref_register introsort_aux_param
sepref_def introsort_aux_param_impl is "uncurry4 (PR_CONST introsort_aux_param)" 
  :: "cparam_assn\<^sup>k *\<^sub>a (arr_assn)\<^sup>d *\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k \<rightarrow>\<^sub>a arr_assn"
  unfolding introsort_aux_param_def PR_CONST_def
  apply (annot_snat_const "TYPE(size_t)")
  by sepref
  
  
sepref_register introsort_param
sepref_def introsort_param_impl is "uncurry3 (PR_CONST introsort_param)" :: "cparam_assn\<^sup>k *\<^sub>a (arr_assn)\<^sup>d *\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k \<rightarrow>\<^sub>a arr_assn"
  unfolding introsort_param_def PR_CONST_def
  apply (annot_snat_const "TYPE(size_t)")
  supply [intro!] = introsort_depth_limit_in_bounds_aux 
  by sepref


lemma introsort_param_impl_correct: "(uncurry3 introsort_param_impl, uncurry3 (PR_CONST (pslice_sort_spec cdom pless)))
        \<in> cparam_assn\<^sup>k *\<^sub>a arr_assn\<^sup>d *\<^sub>a snat_assn\<^sup>k *\<^sub>a snat_assn\<^sup>k \<rightarrow>\<^sub>a arr_assn"
  using introsort_param_impl.refine[FCOMP introsort_param_correct'] .
  
end



end

