section \<open>Introsort (roughly libstdc++ version)\<close>
theory Sorting_Introsort
imports Sorting_Insertion_Sort Sorting_Heapsort Sorting_Log2
begin

text \<open>Threshold for slice size to stop (partial) sorting with quicksort\<close>
abbreviation "is_threshold \<equiv> 16::nat"  


context weak_ordering begin
  
subsection \<open>Find Median\<close>

definition "move_median_to_first ri ai bi ci (xs::'a list) \<equiv> doN {
    a \<leftarrow> mop_list_get xs ai;
    b \<leftarrow> mop_list_get xs bi;
    c \<leftarrow> mop_list_get xs ci;
  
    if a\<^bold><b then (
      if b\<^bold><c then
        mop_list_swap xs ri bi
      else if a\<^bold><c then
        mop_list_swap xs ri ci
      else 
        mop_list_swap xs ri ai
    ) 
    else if a\<^bold><c then
      mop_list_swap xs ri ai
    else if b\<^bold><c then 
      mop_list_swap xs ri ci
    else 
      mop_list_swap xs ri bi
  }"

  
lemma move_median_to_first_correct:
  "\<lbrakk> ri<ai; ai<bi; bi<ci; ci<length xs \<rbrakk> \<Longrightarrow> 
  move_median_to_first ri ai bi ci xs 
    \<le> SPEC (\<lambda>xs'. \<exists>i\<in>{ai,bi,ci}. 
        xs' = swap xs ri i
      \<and> (\<exists>j\<in>{ai,bi,ci}-{i}. xs!i\<^bold>\<le>xs!j)   
      \<and> (\<exists>j\<in>{ai,bi,ci}-{i}. xs!i\<^bold>\<ge>xs!j)   
      )"
  unfolding move_median_to_first_def
  apply refine_vcg
  supply aux = bexI[where P="\<lambda>x. _=_ x \<and> _ x", OF conjI[OF refl]]
  apply ((rule aux)?; insert connex,auto simp: unfold_lt_to_le)+
  done
  
    
lemma move_median_to_first_correct':
  "\<lbrakk> ri<ai; ai<bi; bi<ci; ci<length xs \<rbrakk> \<Longrightarrow> 
  move_median_to_first ri ai bi ci xs 
    \<le> SPEC (\<lambda>xs'. slice_eq_mset ri (ci+1) xs' xs 
      \<and> (\<exists>i\<in>{ai,bi,ci}. xs'!i\<^bold>\<le>xs'!ri)
      \<and> (\<exists>i\<in>{ai,bi,ci}. xs'!i\<^bold>\<ge>xs'!ri)
      )"
  apply (rule order_trans[OF move_median_to_first_correct])    
  by auto
  
(* TODO: Clean up prove below, to use more concise aux-lemma! *)  
lemma move_median_to_first_correct'':
  "\<lbrakk> ri<ai; ai<bi; bi<ci; ci<length xs \<rbrakk> \<Longrightarrow> 
  move_median_to_first ri ai bi ci xs 
    \<le> SPEC (\<lambda>xs'. slice_eq_mset ri (ci+1) xs' xs 
      \<and> (\<exists>i\<in>{ai..ci}. xs'!i\<^bold>\<le>xs'!ri)
      \<and> (\<exists>i\<in>{ai..ci}. xs'!i\<^bold>\<ge>xs'!ri)
      )"
  apply (rule order_trans[OF move_median_to_first_correct'])    
  by auto
  
end

context sort_impl_context begin 
  
sepref_register move_median_to_first

sepref_def move_median_to_first_impl [llvm_inline] is "uncurry4 (PR_CONST move_median_to_first)" :: "size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k *\<^sub>a (array_assn elem_assn)\<^sup>d \<rightarrow>\<^sub>a array_assn elem_assn"
  unfolding move_median_to_first_def PR_CONST_def
  by sepref
                   
end

context weak_ordering begin  
  
subsection \<open>Hoare Partitioning Scheme\<close>  
  
  
definition qsp_next_l :: "'a list \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> nat nres" where            
  "qsp_next_l xs p li \<equiv> doN {
    WHILEIT (\<lambda>li'. (\<exists>pi\<in>{li'..<length xs}. xs!pi\<^bold>\<ge>p) \<and> li\<le>li' \<and> (\<forall>i\<in>{li..<li'}. xs!i\<^bold><p)) 
      (\<lambda>li. xs!li \<^bold>< p) (\<lambda>li. RETURN (li + 1)) li
  }"  

  
lemma qsp_next_l_correct[refine_vcg]: "\<lbrakk>\<exists>pi\<in>{li..<length xs}. xs!pi \<^bold>\<ge> p\<rbrakk> 
  \<Longrightarrow> qsp_next_l xs p li 
    \<le> SPEC (\<lambda>li'. li\<le>li' \<and> li'<length xs \<and> (\<forall>i\<in>{li..<li'}. xs!i\<^bold><p) \<and> xs!li'\<^bold>\<ge>p)"
  unfolding qsp_next_l_def
  apply (refine_vcg WHILEIT_rule[where R="measure (\<lambda>li. length xs - li)"])
  apply simp_all
  subgoal by (metis atLeastLessThan_iff leI less_antisym unfold_lt_to_le)
  subgoal using less_eq_Suc_le by force
  subgoal by auto
  subgoal by auto
  subgoal by (auto simp: unfold_le_to_lt)
  done
  
  
definition qsp_next_h :: "'a list \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> nat nres" where
  "qsp_next_h xs p hi \<equiv> doN {
    ASSERT (hi>0);
    let hi = hi - 1;
    ASSERT (hi<length xs);
    WHILEIT (\<lambda>hi'. hi'\<le>hi \<and> (\<exists>pi\<le>hi'. xs!pi\<^bold>\<le>p) \<and> (\<forall>i\<in>{hi'<..hi}. xs!i\<^bold>>p))
      (\<lambda>hi. xs!hi \<^bold>> p) (\<lambda>hi. doN { ASSERT(hi>0); RETURN (hi - 1)}) hi
  }"  

lemma qsp_next_h_correct[refine_vcg]: "\<lbrakk> hi\<le>length xs; \<exists>pi<hi. xs!pi \<^bold>\<le> p \<rbrakk> 
  \<Longrightarrow> qsp_next_h xs p hi \<le> SPEC (\<lambda>hi'. hi'<hi \<and> (\<forall>i\<in>{hi'<..<hi}. xs!i\<^bold>>p) \<and> xs!hi'\<^bold>\<le>p)"
  unfolding qsp_next_h_def
  apply (refine_vcg WHILEIT_rule[where R="measure id"])
  apply (all \<open>(determ \<open>elim conjE exE\<close>)?\<close>)
  apply simp_all
  subgoal using nat_le_Suc_less_imp by blast
  subgoal by (metis gr0I le_zero_eq unfold_lt_to_le)
  subgoal by (metis One_nat_def le_step_down_nat wo_leD)
  subgoal by (metis Suc_pred greaterThanAtMost_iff linorder_neqE_nat not_less_eq)
  subgoal by (meson greaterThanAtMost_iff greaterThanLessThan_iff nat_le_Suc_less_imp)
  subgoal using wo_leI by blast
  done
  
(*
  invariant is:
  
    li\<le>hi
    hi<length xs
   
    mset is equal 
    
    xs{0..<li} < p
    xs!li \<ge> p
    
    xs!hi \<le> p
    xs{hi<..<length xs} > p
    
  variant: measure hi   
*)  
      
definition "qs_partition li\<^sub>0 hi\<^sub>0 p xs\<^sub>0 \<equiv> doN {
  ASSERT (li\<^sub>0<hi\<^sub>0 \<and> hi\<^sub>0\<le>length xs\<^sub>0);
  
  \<comment> \<open>Initialize\<close>
  li \<leftarrow> qsp_next_l xs\<^sub>0 p li\<^sub>0;
  hi \<leftarrow> qsp_next_h xs\<^sub>0 p hi\<^sub>0;
  
  ASSERT (li\<^sub>0\<le>hi);
  
  (xs,li,hi) \<leftarrow> WHILEIT 
    (\<lambda>(xs,li,hi). 
        li\<^sub>0\<le>li \<and> hi<hi\<^sub>0
      \<and> li<hi\<^sub>0 \<and> hi\<ge>li\<^sub>0  
      \<and> slice_eq_mset li\<^sub>0 hi\<^sub>0 xs xs\<^sub>0
      \<and> (\<forall>i\<in>{li\<^sub>0..<li}. xs!i \<^bold>\<le> p)
      \<and> xs!li \<^bold>\<ge> p
      \<and> (\<forall>i\<in>{hi<..<hi\<^sub>0}. xs!i \<^bold>\<ge> p)
      \<and> xs!hi \<^bold>\<le> p  
    )
    (\<lambda>(xs,li,hi). li<hi) 
    (\<lambda>(xs,li,hi). doN {
      ASSERT(li<length xs \<and> hi<length xs);
      xs \<leftarrow> mop_list_swap xs li hi;
      let li = li + 1;
      li \<leftarrow> qsp_next_l xs p li;
      hi \<leftarrow> qsp_next_h xs p hi;
      RETURN (xs,li,hi)
    }) 
    (xs\<^sub>0,li,hi);
  
  RETURN (xs,li)
}"  

(* TODO: Move. Found useful for ATPs *)
lemma strict_itrans: "a < c \<Longrightarrow> a < b \<or> b < c" for a b c :: "_::linorder"
  by auto

lemma qs_partition_correct:
  "\<lbrakk> li<hi; hi\<le>length xs\<^sub>0;  \<exists>pi\<in>{li..<hi}. p \<^bold>\<le> xs\<^sub>0 ! pi; \<exists>pi\<in>{li..<hi}. xs\<^sub>0 ! pi \<^bold>\<le> p \<rbrakk> \<Longrightarrow> qs_partition li hi p xs\<^sub>0 
  \<le> SPEC (\<lambda>(xs,i). slice_eq_mset li hi xs xs\<^sub>0 \<and> li\<le>i \<and> i<hi \<and> (\<forall>i\<in>{li..<i}. xs!i\<^bold>\<le>p) \<and> (\<forall>i\<in>{i..<hi}. xs!i\<^bold>\<ge>p) )"  
  unfolding qs_partition_def
  apply (refine_vcg WHILEIT_rule[where R="measure (\<lambda>(_,_,hi). hi)"])  
  apply (simp_all add: slice_eq_mset_eq_length unfold_lt_to_le)
  subgoal by auto
  subgoal by auto
  subgoal 
    apply clarsimp
    by (meson less_le_trans greaterThanLessThan_iff le_less_linear wo_leD)
  subgoal 
    apply clarsimp
    by (meson atLeastLessThan_iff le_less_linear less_le_trans)
  subgoal by (metis less_le_trans slice_eq_mset_eq_length)
  subgoal by (metis less_le_trans slice_eq_mset_eq_length)
  subgoal by (metis Suc_le_eq atLeastLessThan_iff swap_nth2) 
  subgoal by (metis less_trans swap_nth1) 
  subgoal by (metis less_le_trans Suc_leI atLeastLessThan_iff leI swap_nth2) 
  subgoal by (metis Suc_leI atLeastLessThan_iff atLeastSucLessThan_greaterThanLessThan leI less_le_trans slice_eq_mset_eq_length swap_nth1) 
  subgoal by (metis atLeastLessThan_iff slice_eq_mset_eq_length slice_eq_mset_swap(2)) 
  subgoal by (smt Suc_leI atLeastLessThan_iff less_trans nat_neq_iff swap_nth) 
  subgoal by (smt greaterThanLessThan_iff linorder_neqE_nat swap_indep swap_nth2) 
  subgoal by (metis atLeastLessThan_iff greaterThanLessThan_iff leD le_less_trans linorder_neqE_nat neq_iff) 
  done
  
corollary qs_partition_mset:
  "\<lbrakk> li<hi; hi\<le>length xs\<^sub>0; \<exists>i\<in>{li..<hi}. p\<^bold>\<le>xs\<^sub>0!i; \<exists>i\<in>{li..<hi}. xs\<^sub>0!i\<^bold>\<le>p \<rbrakk> \<Longrightarrow> qs_partition li hi p xs\<^sub>0 
  \<le> SPEC (\<lambda>(xs,i). slice_eq_mset li hi xs xs\<^sub>0 \<and> li\<le>i \<and> i<hi )"  
  apply (refine_vcg qs_partition_correct)
  by auto
  
definition "partition_pivot xs\<^sub>0 l h \<equiv> doN {
  ASSERT (l\<le>h \<and> h\<le>length xs\<^sub>0 \<and> h-l\<ge>4);
  let m = l + (h-l) div 2;
  xs \<leftarrow> move_median_to_first l (l+1) m (h-1) xs\<^sub>0;
  ASSERT (l<length xs \<and> length xs = length xs\<^sub>0);
  (xs,m) \<leftarrow> qs_partition (l+1) h (xs!l) xs;

  RETURN (xs,m)
}"

lemma partition_pivot_mset: "\<lbrakk> l\<le>h ; h\<le>length xs; h-l\<ge>4 \<rbrakk> \<Longrightarrow> partition_pivot xs l h 
  \<le> SPEC (\<lambda>(xs',m). slice_eq_mset l h xs' xs \<and> l<m \<and> m<h)"
  unfolding partition_pivot_def
  apply (refine_vcg move_median_to_first_correct'' qs_partition_mset)
  apply (auto 0 3 dest: slice_eq_mset_eq_length elim: )
  by (smt add.commute le_add1 le_trans order.strict_implies_order order_mono_setup.refl plus_1_eq_Suc slice_eq_mset_subslice slice_eq_mset_trans)

end  
  
context sort_impl_context begin
  
sepref_register qsp_next_l qsp_next_h 

(* TODO: We can get rid of the length xs restriction: the stopper element will always lie within <h, which is size_t representable! *)
sepref_def qsp_next_l_impl [llvm_inline] is "uncurry2 (PR_CONST qsp_next_l)" :: "[\<lambda>((xs,p),i). length xs < max_snat LENGTH(size_t)]\<^sub>a (array_assn elem_assn)\<^sup>k *\<^sub>a elem_assn\<^sup>k *\<^sub>a size_assn\<^sup>k \<rightarrow> size_assn"
  unfolding qsp_next_l_def PR_CONST_def
  apply (annot_snat_const "TYPE(size_t)")
  by sepref

sepref_def qsp_next_h_impl [llvm_inline] is "uncurry2 (PR_CONST qsp_next_h)" :: "(array_assn elem_assn)\<^sup>k *\<^sub>a elem_assn\<^sup>k *\<^sub>a size_assn\<^sup>k \<rightarrow>\<^sub>a size_assn"
  unfolding qsp_next_h_def PR_CONST_def
  apply (annot_snat_const "TYPE(size_t)")
  by sepref
  
                        
sepref_register qs_partition  
sepref_def qs_partition_impl [llvm_inline] is "uncurry3 (PR_CONST qs_partition)" :: "[\<lambda>(((l,h),p),xs). length xs < max_snat LENGTH(size_t)]\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k *\<^sub>a elem_assn\<^sup>k *\<^sub>a (array_assn elem_assn)\<^sup>d \<rightarrow> array_assn elem_assn \<times>\<^sub>a size_assn"
  unfolding qs_partition_def PR_CONST_def
  apply (annot_snat_const "TYPE(size_t)")
  supply [dest] = slice_eq_mset_eq_length
  by sepref
  
sepref_register partition_pivot  
sepref_def partition_pivot_impl [llvm_inline] is "uncurry2 (PR_CONST partition_pivot)" :: "[\<lambda>((xs,l),h). length xs < max_snat LENGTH(size_t)]\<^sub>a arr_assn\<^sup>d *\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k \<rightarrow> arr_assn \<times>\<^sub>a size_assn"
  unfolding partition_pivot_def PR_CONST_def    
  apply (annot_snat_const "TYPE(size_t)")
  by sepref
    

subsection \<open>Partial Quicksort\<close>  
 
definition "introsort_qs_aux xs\<^sub>0 l h d \<equiv> RECT (\<lambda>introsort_qs_aux (xs,l,h,d). doN {
  ASSERT (l\<le>h \<and> h\<le>length xs \<and> length xs = length xs\<^sub>0);
  
  if h-l > is_threshold then doN {
    if d>0 then doN {
      (xs,m) \<leftarrow> partition_pivot xs l h;
      
      ASSERT (l<m \<and> m<h);
  
      xs \<leftarrow> introsort_qs_aux (xs,m,h,d-1);    
      xs \<leftarrow> introsort_qs_aux (xs,l,m,d-1);    
    
      RETURN xs
    } else doN {
      xs\<leftarrow>heapsort xs l h;  
      RETURN xs
    }
  } else   
    RETURN xs
    
}) (xs\<^sub>0,l,h,d)"   
  
lemma introsort_qs_aux_mset: "\<lbrakk> l\<^sub>0\<le>h\<^sub>0; h\<^sub>0\<le>length xs\<^sub>0\<rbrakk> \<Longrightarrow> introsort_qs_aux xs\<^sub>0 l\<^sub>0 h\<^sub>0 d \<le> SPEC (\<lambda>xs'. slice_eq_mset l\<^sub>0 h\<^sub>0 xs' xs\<^sub>0)"
  unfolding introsort_qs_aux_def
  apply (refine_vcg RECT_rule[where 
    pre="\<lambda>(xs',l,h,d). l\<^sub>0\<le>l \<and> h\<le>h\<^sub>0 \<and> l\<le>h \<and> h\<le>length xs' \<and> slice_eq_mset l\<^sub>0 h\<^sub>0 xs' xs\<^sub>0" and
    V="measure (\<lambda>(_,l,h,d). h-l)"]
  
    partition_pivot_mset  
    (*qs_partition_mset*)
    
  )
  apply (all \<open>(auto dest: slice_eq_mset_eq_length;fail)?\<close>)
  apply (rule order_trans)
  apply rprems
  subgoal
    apply (auto simp: slice_eq_mset_eq_length)
    by (meson less_imp_not_less less_le_trans nat_le_linear slice_eq_mset_subslice slice_eq_mset_trans)
  subgoal by auto []
  apply refine_vcg
  apply (rule order_trans)
  apply rprems
  subgoal by (auto simp: slice_eq_mset_eq_length)
  subgoal by auto
  subgoal by refine_vcg
  
  subgoal 
    apply (refine_vcg heapsort_correct) 
    subgoal by auto
    subgoal by auto
    subgoal by clarsimp (meson slice_eq_mset_subslice slice_eq_mset_trans)
    done
  
  done
    
  
subsection \<open>Main Sorting Function\<close>  
  
definition "introsort xs l h \<equiv> doN {
  ASSERT(l\<le>h);
  if h-l>1 then doN {
    xs \<leftarrow> introsort_qs_aux xs l h (Discrete.log (h-l) * 2);
    xs \<leftarrow> insertion_sort xs l h;
    RETURN xs
  } else RETURN xs
}"  


lemma slice_sort_spec01: "h-l\<le>1 \<Longrightarrow> RETURN xs \<le> slice_sort_spec (\<^bold><) xs l h"
  unfolding slice_sort_spec_def sort_spec_def
  apply refine_vcg
  by (auto simp: sorted_wrt01)

lemma introsort_correct: 
  assumes "l\<le>h" "h\<le>length xs"
  shows "introsort xs l h \<le> slice_sort_spec (\<^bold><) xs l h"
  unfolding introsort_def 
  (* Manual refinement of LHS to use specs. TODO: Define this abstract fun explicitly! *)
  apply (cases "h-l>1")
  subgoal
    apply (simp add: assms)
    apply (rule order_trans)
    apply (rule bind_mono)
    apply (rule introsort_qs_aux_mset[OF assms])
    apply (rule insertion_sort_correct[param_fo, OF IdI IdI IdI, THEN nres_relD, simplified])
  
    (* show that slice_sort on eq-mset-slice implies slice-sort  *)
    apply (auto simp: pw_le_iff pw_nres_rel_iff refine_pw_simps slice_sort_spec_def slice_eq_mset_def intro: sort_spec_permute)  
    done
  subgoal  
    by (auto simp: slice_sort_spec01 assms)
    
  done

sepref_register introsort_qs_aux 
sepref_def introsort_qs_aux_impl is "uncurry3 (PR_CONST introsort_qs_aux)" :: "[\<lambda>(((xs,l),h),d). length xs < max_snat LENGTH(size_t)]\<^sub>a (array_assn elem_assn)\<^sup>d *\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k \<rightarrow> array_assn elem_assn"
  unfolding introsort_qs_aux_def PR_CONST_def
  apply (annot_snat_const "TYPE(size_t)")
  by sepref

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
  
sepref_register introsort 
sepref_def introsort_impl is "uncurry2 (PR_CONST introsort)" :: "[\<lambda>((xs,l),h). length xs < max_snat LENGTH(size_t)]\<^sub>a (array_assn elem_assn)\<^sup>d *\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k \<rightarrow> array_assn elem_assn"
  unfolding introsort_def PR_CONST_def
  apply (annot_snat_const "TYPE(size_t)")
  supply [intro!] = introsort_depth_limit_in_bounds_aux 
  by sepref

end  


global_interpretation elem_sort: sort_impl_context "(\<le>)" "(<)" ll_icmp_ult unat_assn
  defines elem_sort_is_insert_impl = elem_sort.is_insert_impl
      and elem_sort_insertion_sort_impl = elem_sort.insertion_sort_impl
      and elem_sort_mop_lchild_impl  = elem_sort.mop_lchild_impl 
      and elem_sort_mop_rchild_impl  = elem_sort.mop_rchild_impl 
      and elem_sort_has_rchild_impl  = elem_sort.has_rchild_impl 
      and elem_sort_has_lchild_impl  = elem_sort.has_lchild_impl 
      and elem_sort_mop_geth_impl    = elem_sort.mop_geth_impl  
      and elem_sort_mop_seth_impl    = elem_sort.mop_seth_impl  
      and elem_sort_sift_down_impl   = elem_sort.sift_down_impl
      and elem_sort_heapify_btu_impl = elem_sort.heapify_btu_impl
      and elem_sort_heapsort_impl    = elem_sort.heapsort_impl
      and elem_sort_qsp_next_l_impl       = elem_sort.qsp_next_l_impl
      and elem_sort_qsp_next_h_impl       = elem_sort.qsp_next_h_impl
      and elem_sort_qs_partition_impl     = elem_sort.qs_partition_impl
      and elem_sort_partition_pivot_impl  = elem_sort.partition_pivot_impl 
      and elem_sort_introsort_qs_aux_impl = elem_sort.introsort_qs_aux_impl
      and elem_sort_introsort_impl        = elem_sort.introsort_impl
      and elem_sort_move_median_to_first_impl = elem_sort.move_median_to_first_impl
  by (rule unat_sort_impl_context)
      
 (* TODO: Move! *)
lemmas [llvm_inline] = 
  array_swap_def word_log2_impl_def 

  
  
export_llvm 
  "elem_sort_introsort_impl :: 64 word ptr \<Rightarrow> _" is "uint64_t* introsort(uint64_t*, int64_t, int64_t)" 
  "elem_sort_introsort_qs_aux_impl :: 64 word ptr \<Rightarrow> _" is "uint64_t* introsort_aux(uint64_t*, int64_t, int64_t, int64_t)" 
  "elem_sort_heapsort_impl :: 64 word ptr \<Rightarrow> _" is "uint64_t* heapsort(uint64_t*, int64_t, int64_t)" 
  "elem_sort_insertion_sort_impl :: 64 word ptr \<Rightarrow> _" is "uint64_t* insertion_sort(uint64_t*, int64_t, int64_t)" 
  file "../code/introsort.ll"

end
