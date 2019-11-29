section \<open>Introsort (roughly libstdc++ version)\<close>
theory Sorting_Introsort
imports 
  Sorting_Unguarded_Insertion_Sort Sorting_Heapsort Sorting_Log2 
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

context sort_impl_context begin

sepref_register introsort_aux4
sepref_def introsort_aux_impl is "uncurry3 (PR_CONST introsort_aux4)" :: "(arr_assn)\<^sup>d *\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k \<rightarrow>\<^sub>a arr_assn"
  unfolding introsort_aux4_def PR_CONST_def
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

 (* TODO: Move! *)
lemmas [llvm_inline] = 
  array_swap_def word_log2_impl_def 

global_interpretation unat_sort: pure_sort_impl_context "(\<le>)" "(<)" ll_icmp_ult unat_assn
  defines unat_sort_is_guarded_insert_impl = unat_sort.is_guarded_insert_impl
      and unat_sort_is_unguarded_insert_impl = unat_sort.is_unguarded_insert_impl
      and unat_sort_unguarded_insertion_sort_impl = unat_sort.unguarded_insertion_sort_impl
      and unat_sort_guarded_insertion_sort_impl = unat_sort.guarded_insertion_sort_impl
      and unat_sort_final_insertion_sort_impl = unat_sort.final_insertion_sort_impl
      (*and unat_sort_mop_lchild_impl  = unat_sort.mop_lchild_impl 
      and unat_sort_mop_rchild_impl  = unat_sort.mop_rchild_impl 
      and unat_sort_has_rchild_impl  = unat_sort.has_rchild_impl 
      and unat_sort_has_lchild_impl  = unat_sort.has_lchild_impl 
      and unat_sort_mop_geth_impl    = unat_sort.mop_geth_impl  
      and unat_sort_mop_seth_impl    = unat_sort.mop_seth_impl*)  
      and unat_sort_sift_down_impl   = unat_sort.sift_down_impl
      and unat_sort_heapify_btu_impl = unat_sort.heapify_btu_impl
      and unat_sort_heapsort_impl    = unat_sort.heapsort_impl
      and unat_sort_qsp_next_l_impl       = unat_sort.qsp_next_l_impl
      and unat_sort_qsp_next_h_impl       = unat_sort.qsp_next_h_impl
      and unat_sort_qs_partition_impl     = unat_sort.qs_partition_impl
(*      and unat_sort_qs_partitionXXX_impl     = unat_sort.qs_partitionXXX_impl *)
      and unat_sort_partition_pivot_impl  = unat_sort.partition_pivot_impl 
      and unat_sort_introsort_aux_impl = unat_sort.introsort_aux_impl
      and unat_sort_introsort_impl        = unat_sort.introsort_impl
      and unat_sort_move_median_to_first_impl = unat_sort.move_median_to_first_impl
  by (rule unat_sort_impl_context)

thm unat_sort.introsort_impl_correct  
thm unat_sort.is_unguarded_insert_impl_def

abbreviation "string_assn \<equiv> string_assn' TYPE(size_t) TYPE(8)"  
  
global_interpretation str_sort: sort_impl_context "(\<le>)" "(<)" strcmp_impl string_assn
  defines str_sort_is_guarded_insert_impl = str_sort.is_guarded_insert_impl
      and str_sort_is_unguarded_insert_impl = str_sort.is_unguarded_insert_impl
      and str_sort_unguarded_insertion_sort_impl = str_sort.unguarded_insertion_sort_impl
      and str_sort_guarded_insertion_sort_impl = str_sort.guarded_insertion_sort_impl
      and str_sort_final_insertion_sort_impl = str_sort.final_insertion_sort_impl
      (*and str_sort_mop_lchild_impl  = str_sort.mop_lchild_impl 
      and str_sort_mop_rchild_impl  = str_sort.mop_rchild_impl 
      and str_sort_has_rchild_impl  = str_sort.has_rchild_impl 
      and str_sort_has_lchild_impl  = str_sort.has_lchild_impl 
      and str_sort_mop_geth_impl    = str_sort.mop_geth_impl  
      and str_sort_mop_seth_impl    = str_sort.mop_seth_impl  *)
      and str_sort_sift_down_impl   = str_sort.sift_down_impl
      and str_sort_heapify_btu_impl = str_sort.heapify_btu_impl
      and str_sort_heapsort_impl    = str_sort.heapsort_impl
      and str_sort_qsp_next_l_impl       = str_sort.qsp_next_l_impl
      and str_sort_qsp_next_h_impl       = str_sort.qsp_next_h_impl
      and str_sort_qs_partition_impl     = str_sort.qs_partition_impl
(*      and str_sort_qs_partitionXXX_impl     = str_sort.qs_partitionXXX_impl *)
      and str_sort_partition_pivot_impl  = str_sort.partition_pivot_impl 
      and str_sort_introsort_aux_impl = str_sort.introsort_aux_impl
      and str_sort_introsort_impl        = str_sort.introsort_impl
      and str_sort_move_median_to_first_impl = str_sort.move_median_to_first_impl
  by (rule strcmp_sort_impl_context)
  
thm str_sort.introsort_impl_correct  
  
  
(* Wrapper functions for export to LLVM. Only used for testing and profiling. *)
definition str_init :: "(8 word,size_t)array_list ptr \<Rightarrow> unit llM" where [llvm_code]:
  "str_init sp \<equiv> doM {
    ll_store init sp
  }"

definition str_append :: "(8 word,size_t)array_list ptr \<Rightarrow> 8 word \<Rightarrow> unit llM" where [llvm_code]:
  "str_append sp x \<equiv> doM {
    s \<leftarrow> ll_load sp;
    s \<leftarrow> arl_push_back s x;
    ll_store s sp
  }"

  
definition llstrcmp :: "(8 word,size_t)array_list ptr \<Rightarrow> _ \<Rightarrow> 8 word llM" where [llvm_code]:
  "llstrcmp ap bp \<equiv> doM {
    a \<leftarrow> ll_load ap;
    b \<leftarrow> ll_load bp;
    r \<leftarrow> strcmp_impl a b;
    if r\<noteq>0 then return 1 else return 0
  }"
  
  
export_llvm 
  "unat_sort_introsort_impl :: 64 word ptr \<Rightarrow> _" is "uint64_t* introsort(uint64_t*, int64_t, int64_t)" 
  "unat_sort_introsort_aux_impl :: 64 word ptr \<Rightarrow> _" is "uint64_t* introsort_aux(uint64_t*, int64_t, int64_t, int64_t)" 
  "unat_sort_heapsort_impl :: 64 word ptr \<Rightarrow> _" is "uint64_t* heapsort(uint64_t*, int64_t, int64_t)" 
  "unat_sort_final_insertion_sort_impl :: 64 word ptr \<Rightarrow> _" is "uint64_t* insertion_sort(uint64_t*, int64_t, int64_t)" 

  "str_init" is "void str_init(llstring *)"
  "str_append" is "void str_append(llstring *, char)"
  "llstrcmp" is "char llstrcmp(llstring*,llstring*)"
  "str_sort_introsort_impl" is "llstring* str_introsort(llstring*, int64_t, int64_t)" 
  
  defines \<open>typedef struct {int64_t size; struct {int64_t capacity; char *data;};} llstring;\<close>
  file "../code/introsort.ll"

end

