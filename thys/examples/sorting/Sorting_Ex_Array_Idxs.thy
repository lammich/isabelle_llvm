theory Sorting_Ex_Array_Idxs
imports Sorting_Introsort
begin

subsection \<open>Compare Indexes into Value Array\<close>

definition idx_less :: "'a::linorder list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where "idx_less vs i j \<equiv> vs!i < vs!j"
definition idx_cdom :: "'a::linorder list \<Rightarrow> nat set" where "idx_cdom vs \<equiv> {0..<length vs}"

definition "idx_pcmp vs i j \<equiv> do {
  ASSERT (i<length vs \<and> j<length vs);
  RETURN (vs!i < vs!j)
}"

sepref_def idx_pcmp_impl is "uncurry2 idx_pcmp" :: 
  "(array_assn snat_assn)\<^sup>k *\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  unfolding idx_pcmp_def
  by sepref
  

interpretation IDXO: weak_ordering_on_lt "idx_cdom vs" "idx_less vs"
  apply unfold_locales
  unfolding idx_less_def by auto

interpretation IDXO: parameterized_weak_ordering idx_cdom idx_less idx_pcmp
  apply unfold_locales
  unfolding idx_pcmp_def
  apply refine_vcg
  apply (auto simp: idx_less_def idx_cdom_def)
  done

  
global_interpretation IDXO: parameterized_sort_impl_context 
  idx_cdom idx_less idx_pcmp idx_pcmp_impl "array_assn snat_assn" size_assn
  defines IDXO_is_guarded_insert_impl = IDXO.is_guarded_param_insert_impl
      and IDXO_is_unguarded_insert_impl = IDXO.is_unguarded_param_insert_impl
      and IDXO_unguarded_insertion_sort_impl = IDXO.unguarded_insertion_sort_param_impl
      and IDXO_guarded_insertion_sort_impl = IDXO.guarded_insertion_sort_param_impl
      and IDXO_final_insertion_sort_impl = IDXO.final_insertion_sort_param_impl
      (*and IDXO_mop_lchild_impl  = IDXO.mop_lchild_impl 
      and IDXO_mop_rchild_impl  = IDXO.mop_rchild_impl 
      and IDXO_has_rchild_impl  = IDXO.has_rchild_impl 
      and IDXO_has_lchild_impl  = IDXO.has_lchild_impl 
      and IDXO_mop_geth_impl    = IDXO.mop_geth_impl  
      and IDXO_mop_seth_impl    = IDXO.mop_seth_impl*)  
      and IDXO_sift_down_impl   = IDXO.sift_down_impl
      and IDXO_heapify_btu_impl = IDXO.heapify_btu_impl
      and IDXO_heapsort_impl    = IDXO.heapsort_param_impl
      and IDXO_qsp_next_l_impl       = IDXO.qsp_next_l_impl
      and IDXO_qsp_next_h_impl       = IDXO.qsp_next_h_impl
      and IDXO_qs_partition_impl     = IDXO.qs_partition_impl
(*      and IDXO_qs_partitionXXX_impl     = IDXO.qs_partitionXXX_impl *)
      and IDXO_partition_pivot_impl  = IDXO.partition_pivot_impl 
      and IDXO_introsort_aux_impl = IDXO.introsort_aux_param_impl
      and IDXO_introsort_impl        = IDXO.introsort_param_impl
      and IDXO_move_median_to_first_impl = IDXO.move_median_to_first_param_impl
  
  apply unfold_locales
  unfolding GEN_ALGO_def refines_param_relp_def (* TODO: thm gen_refines_param_relpI *)
  by (rule idx_pcmp_impl.refine)
  
  

export_llvm 
  "IDXO_heapsort_impl :: 32 word ptr \<Rightarrow> _" is "uint64_t* heapsort_idxs(uint32_t*, uint64_t*, int64_t, int64_t)"
  "IDXO_introsort_impl :: 32 word ptr \<Rightarrow> _" is "uint64_t* introsort_idxs(uint32_t*, uint64_t*, int64_t, int64_t)"
  file "../code/introsort_param.ll"

end
