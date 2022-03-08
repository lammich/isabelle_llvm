theory Sorting_Sample_Partition
imports Sorting_Quicksort_Scheme Sorting_Quicksort_Partition Sorting_Ex_Array_Idxs
begin

context weak_ordering begin
  
  definition num_samples :: "nat \<Rightarrow> nat nres" 
    where "num_samples n \<equiv> RETURN (min n 64)"

  lemma num_samples_correct: "n\<ge>4 \<Longrightarrow> num_samples n \<le> SPEC (\<lambda>i. i\<ge>3 \<and> i \<le> n)"
    unfolding num_samples_def by auto

  definition "idxs_spec xs n ns \<equiv> doN {
    ASSERT (n=length xs \<and> ns\<le>n);
    SPEC (\<lambda>idxs. 
        ns = length idxs 
      \<and> distinct idxs 
      \<and> set idxs \<subseteq> {0..<n} 
      \<and> sorted_wrt (\<lambda>i j. xs!i \<^bold>\<le> xs!j) idxs)
  }"  
    
 
  definition "equidist n ns \<equiv> doN {
    ASSERT (2\<le>ns \<and> ns\<le>n);
    let idxs = replicate ns 0;
    
    let incr = n div ns;
    let extra = n mod ns;

    ASSERT (incr>0);
          
    (_,_,_,idxs) \<leftarrow> WHILEIT 
      (\<lambda>(i,j,extra,idxs). 
          ns=length idxs
        \<and> i\<le>ns \<and> extra\<ge>0 \<and> extra < ns
        \<and> set (take i idxs) \<subseteq> {0..<j}
        \<and> distinct (take i idxs)
        \<and> j + (ns-i)*incr + extra = n
      ) 
      (\<lambda>(i,j,extra,idxs). i<ns) (\<lambda>(i,j,extra,idxs). doN {
        idxs \<leftarrow> mop_list_set idxs i j;
        ASSERT(i+1 \<le> ns);
        let i=i+1;
        ASSERT(j+incr \<le> n);
        let j=j+incr;
        (j,extra) \<leftarrow> if extra>0 then doN {
          ASSERT (j+1\<le>n);
          RETURN (j+1,extra-1)
        } else 
          RETURN (j,extra);
          
        RETURN (i,j,extra,idxs) 
      }) 
      (0,0,extra,idxs);
    
    RETURN idxs
  }"     

  lemma set_subset_conv_nth: "set xs \<subseteq> S \<longleftrightarrow> (\<forall>i<length xs. xs!i \<in> S)"
    by (auto 0 3 simp: in_set_conv_nth in_mono)
    
  
  
  lemma equidist_correct[refine_vcg]: "\<lbrakk>2\<le>ns; ns\<le>n\<rbrakk> \<Longrightarrow> 
    equidist n ns \<le> SPEC (\<lambda>idxs. length idxs = ns \<and> distinct idxs \<and> set idxs \<subseteq> {0..<n})"
    unfolding equidist_def
    apply (refine_vcg WHILEIT_rule[where R="measure (\<lambda>(i,j,extra,idxs). ns-i)"])
    apply (simp_all add: div_positive)
    apply auto []
    
    apply (auto simp: in_set_conv_nth nth_list_update' set_subset_conv_nth distinct_conv_nth)
    subgoal by (metis div_le_dividend div_mult_self1_is_m less_eq_Suc_le nat_add_left_cancel_le trans_le_add1 zero_less_diff)
    subgoal by (smt (z3) Euclidean_Division.div_less add_less_cancel_left diff_is_0_eq div_mult_self_is_m div_positive le_neq_implies_less less_add_same_cancel1 less_trans not_less_eq_eq)
    subgoal by (meson less_SucI less_antisym trans_less_add1)
    subgoal by (metis less_SucE nat_less_le)
    subgoal by (metis less_SucE nat_less_le)
    subgoal by (metis Suc_diff_le diff_Suc_Suc group_cancel.add1 mult_Suc) 
    subgoal by (meson div_positive less_le_trans pos2) 
    subgoal by (meson less_antisym trans_less_add1)
    subgoal by (metis less_SucE nat_less_le)
    subgoal by (metis less_SucE nat_less_le)
    subgoal by (metis Suc_diff_le diff_Suc_Suc group_cancel.add1 mult_Suc) 
    done      

    
          
  definition "sorted_samples_spec xs n ns \<equiv> doN {ASSERT (2\<le>ns \<and> ns\<le>n \<and> n = length xs); SPEC (\<lambda>idxs. 
      ns = length idxs 
    \<and> distinct idxs 
    \<and> set idxs \<subseteq> {0..<n} 
    \<and> sorted_wrt (\<lambda>i j. xs!i \<^bold>\<le> xs!j) idxs)}"

  definition "sorted_samples xs n ns \<equiv> doN {
    ASSERT (n = length xs);
    idxs \<leftarrow> equidist n ns;
    idxs \<leftarrow> mop_array_to_woarray idxs;
    idxs \<leftarrow> pslice_sort_spec (\<lambda>xs. {0..<length xs}) (\<lambda>xs i j. xs!i \<^bold>< xs!j) xs idxs 0 ns;
    idxs \<leftarrow> mop_woarray_to_array idxs;
    RETURN idxs
  }"  

  lemma mset_eq_imp_distinct_eq: "mset xs = mset ys \<Longrightarrow> distinct xs \<longleftrightarrow> distinct ys"
    by (metis count_mset_0_iff distinct_count_atmost_1)
  
  lemma sorted_samples_correct: "sorted_samples xs n ns \<le> sorted_samples_spec xs n ns"
    unfolding sorted_samples_def sorted_samples_spec_def pslice_sort_spec_def slice_sort_spec_def
    apply simp
    apply refine_vcg
    apply (auto simp: slice_complete' sort_spec_def)
    subgoal by (metis mset_eq_imp_distinct_eq)
    subgoal by (metis atLeastLessThan_iff mset_eq_setD subsetD)
    subgoal by (simp add: le_by_lt_def sorted_wrt_iff_nth_less wo_leI)
    done

            
  definition "sample_pivot xs n \<equiv> doN {
    ASSERT (n = length xs);
    ASSERT (n\<ge>4);
    
    ns \<leftarrow> num_samples n;
    
    idxs \<leftarrow> sorted_samples_spec xs n ns;
    
    let mi = ns div 2;
    ASSERT (1\<le>mi \<and> mi < length idxs-1);
    
    ASSERT (idxs!(mi-1)<length xs \<and> idxs!(mi)<length xs \<and> idxs!(mi+1)<length xs);
    
    ASSERT (xs!(idxs!(mi-1)) \<^bold>\<le> xs!(idxs!mi) 
          \<and> xs!(idxs!mi) \<^bold>\<le> xs!(idxs!(mi+1)));
    
    RETURN (idxs!mi)
  }"

  (* For presentation in paper *)  
  lemma "doN {
    let ns = min (length xs) 64;
    idxs \<leftarrow> equidist (length xs) ns;
    idxs \<leftarrow> slice_sort_spec (\<lambda>i j. xs!i \<^bold>< xs!j) idxs 0 ns;
    RETURN (idxs!(ns div 2))
  } \<le> sample_pivot xs n"
    using sorted_samples_correct
    unfolding sample_pivot_def num_samples_def sorted_samples_def pslice_sort_spec_def
    apply (simp only: pw_le_iff refine_pw_simps mop_array_to_woarray_def mop_woarray_to_array_def Let_def)
    apply safe
    apply simp
    apply blast
    apply blast
    apply blast
    apply blast
    by (metis (no_types, lifting))
    
    
  
  
  lemma sample_pivot_correct[refine_vcg]: "
    \<lbrakk>n=length xs; length xs \<ge> 4\<rbrakk> \<Longrightarrow> sample_pivot xs n \<le> SPEC (\<lambda>i. 
      i\<in>{0..<length xs} 
    \<and> (\<exists>j\<in>{0..<length xs}. i\<noteq>j \<and> xs!i\<^bold>\<le>xs!j)
    \<and> (\<exists>j\<in>{0..<length xs}. i\<noteq>j \<and> xs!i\<^bold>\<ge>xs!j))"
      
    unfolding sample_pivot_def sorted_samples_spec_def
    apply (refine_vcg num_samples_correct)
    apply (clarsimp_all simp: sort_spec_def)
    apply simp_all
    subgoal for idxs
      by (meson atLeastLessThan_iff diff_le_self less_imp_diff_less less_le_trans nth_mem subset_code(1))
    subgoal for idxs
      by (meson atLeastLessThan_iff diff_le_self less_imp_diff_less less_le_trans nth_mem subset_code(1))
    subgoal for idxs
      by (simp add: subset_code(1))
    subgoal 
      by  (auto simp: sorted_wrt_iff_nth_less) 
    subgoal by (auto simp: sorted_wrt_iff_nth_less)
    subgoal for idxs
      apply (rule bexI[where x="idxs!(length idxs div 2 + 1)"])
      apply (simp_all add: distinct_conv_nth)
      done
    subgoal for idxs
      apply (rule bexI[where x="idxs!(length idxs div 2 - 1)"])
      apply (auto simp: distinct_conv_nth) 
      done
    done
    
  definition "move_pivot_to_first_sample xs n \<equiv> doN {
    i \<leftarrow> sample_pivot xs n;
    if i\<noteq>0 then
      mop_list_swap xs 0 i
    else
      RETURN xs
  }"
  
  lemma move_pivot_to_first_sample_correct[refine_vcg]: 
    "\<lbrakk>n=length xs; length xs \<ge> 4\<rbrakk> \<Longrightarrow> 
    move_pivot_to_first_sample xs n \<le> SPEC (\<lambda>xs'. 
      mset xs' = mset xs
    \<and> (\<exists>j\<in>{1..<length xs'}. xs'!0\<^bold>\<le>xs'!j)
    \<and> (\<exists>j\<in>{1..<length xs'}. xs'!0\<^bold>\<ge>xs'!j)        
    )"      
    unfolding move_pivot_to_first_sample_def
    apply refine_vcg
    apply (auto simp: swap_nth)
    subgoal by (metis One_nat_def atLeastLessThan_iff le_neq_implies_less less_one nat_le_linear)
    subgoal by (metis One_nat_def atLeastLessThan_iff less_one not_le)
    done
  
  
  definition "partition_pivot_sample xs n \<equiv> doN {
    ASSERT (n=length xs);
    xs \<leftarrow> move_pivot_to_first_sample xs n;
    (xs,m) \<leftarrow> qs_partition 1 n 0 xs;
    RETURN (xs,m)
  }"
  
  
lemma slice_eq_mset_all[simp]: 
  "slice_eq_mset 0 (length xs') xs xs' \<longleftrightarrow> mset xs = mset xs'"
  unfolding slice_eq_mset_def 
  apply (auto simp: Misc.slice_def dest: mset_eq_length)  
  using mset_eq_length by fastforce

lemma slice_eq_mset_mono: "l\<le>l' \<Longrightarrow> l'\<le>h' \<Longrightarrow> h'\<le>h 
  \<Longrightarrow> slice_eq_mset l' h' xs xs' \<Longrightarrow> slice_eq_mset l h xs xs'"
  unfolding slice_eq_mset_def
  apply auto  
  subgoal by (metis min_def take_take)
  subgoal by (meson slice_eq_mset_def slice_eq_mset_subslice)
  subgoal using drop_eq_mono by blast
  done  
  
  
find_theorems slice_eq_mset
thm slice_eq_mset_alt   
  
lemma partition_pivot_sample_correct: "\<lbrakk>(xs,xs')\<in>Id; (n,n')\<in>Id; n'=length xs'\<rbrakk> 
  \<Longrightarrow> partition_pivot_sample xs n \<le> \<Down>(\<langle>Id\<rangle>list_rel \<times>\<^sub>r nat_rel) (partition3_spec xs' 0 n')"
  unfolding partition_pivot_sample_def partition3_spec_def
  apply simp
  apply (refine_vcg qs_partition_correct)
  apply auto
  apply (metis eq_imp_le mset_eq_length)
  subgoal by (metis atLeastLessThan_iff size_mset)
  subgoal by (metis atLeastLessThan_iff size_mset)
  subgoal by (smt (z3) le_SucI le_trans less_or_eq_imp_le mset_eq_length slice_eq_mset_all slice_eq_mset_subslice)
  subgoal for xs1 m xs2 j ja
    apply (rule slice_LT_I_aux[where p="xs1!0"])
    apply (auto dest: mset_eq_length slice_eq_mset_eq_length)[2]
    subgoal by (metis le_refl size_mset slice_eq_mset_eq_length)
    apply (metis One_nat_def atLeastLessThan_iff bot_nat_0.extremum less_one not_le not_less_eq_eq slice_eq_mset_eq_length slice_eq_mset_nth_outside wo_refl)
    apply (auto dest: mset_eq_length slice_eq_mset_eq_length)[1]
    done
  done  
  


end

context sort_impl_context begin

  text \<open>Introsort for sorting samples\<close>
  sublocale SAMPLE_SORT: idxs_comp "(\<^bold>\<le>)" "(\<^bold><)" lt_impl elem_assn
    by unfold_locales
    
  
  find_in_thms SAMPLE_SORT.introsort_param_impl in sepref_fr_rules

  find_theorems SAMPLE_SORT.introsort_param_impl
  
  
  sepref_register equidist
  
  sepref_def equidist_impl [llvm_inline] is 
    "uncurry equidist" :: "size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k \<rightarrow>\<^sub>a array_assn size_assn"
    unfolding equidist_def
    apply (rewrite array.fold_replicate_init)
    apply (annot_snat_const "TYPE(size_t)")
    by sepref

  lemma fold_sample_sort_spec: "pslice_sort_spec (\<lambda>xs. {0..<length xs}) (\<lambda>xs i j. xs ! i \<^bold>< xs ! j) 
    = PR_CONST (pslice_sort_spec SAMPLE_SORT.idx_cdom SAMPLE_SORT.idx_less)"
    unfolding PR_CONST_def SAMPLE_SORT.idx_cdom_def SAMPLE_SORT.idx_less_def ..    
      
  sepref_register "PR_CONST (pslice_sort_spec SAMPLE_SORT.idx_cdom SAMPLE_SORT.idx_less)"  
    
  sepref_register sorted_samples
  sepref_def sorted_samples_impl is "uncurry2 (PR_CONST sorted_samples)" 
    :: "arr_assn\<^sup>k *\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k \<rightarrow>\<^sub>a array_assn size_assn"
    unfolding PR_CONST_def
    unfolding sorted_samples_def fold_sample_sort_spec
    apply (annot_snat_const "TYPE(size_t)")
    supply [sepref_fr_rules] = SAMPLE_SORT.introsort_param_impl_correct
    apply sepref
    done
    
    
  sepref_register sorted_samples_spec  
    
  lemma sorted_samples_refine: "(PR_CONST sorted_samples, PR_CONST sorted_samples_spec)\<in> Id \<rightarrow> Id \<rightarrow> Id \<rightarrow> \<langle>Id\<rangle>nres_rel"
    using sorted_samples_correct by (auto simp: nres_relI)
  
  lemmas sorted_samples_impl_correct = sorted_samples_impl.refine[FCOMP sorted_samples_refine]
    
  sepref_register sample_pivot  
  sepref_def sample_pivot_impl is "uncurry (PR_CONST sample_pivot)" :: "arr_assn\<^sup>k *\<^sub>a size_assn\<^sup>k \<rightarrow>\<^sub>a size_assn" 
    unfolding sample_pivot_def num_samples_def min_def PR_CONST_def (* TODO: Include rule for min! *)
    apply (annot_snat_const "TYPE(size_t)")
    supply [sepref_fr_rules] = sorted_samples_impl_correct
    by sepref
    
  sepref_register partition_pivot_sample  
  sepref_def partition_pivot_sample_impl is "uncurry (PR_CONST partition_pivot_sample)" 
      :: "[\<lambda>_. True]\<^sub>c arr_assn\<^sup>d *\<^sub>a size_assn\<^sup>k \<rightarrow> arr_assn\<times>\<^sub>asize_assn [\<lambda>(ai,_) (r,_). r=ai]\<^sub>c" 
    unfolding partition_pivot_sample_def move_pivot_to_first_sample_def PR_CONST_def (* TODO: Include rule for min! *)
    apply (annot_snat_const "TYPE(size_t)")
    by sepref
    
    
end

end
