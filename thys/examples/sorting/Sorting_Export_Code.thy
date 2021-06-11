theory Sorting_Export_Code
imports Sorting_PDQ Sorting_Introsort Sorting_Strings
begin
  
text \<open>
  We instantiate Introsort and Pdqsort for unsigned \<open>i64\<close>, and for dynamic arrays of \<open>i8\<close>s \<open>string_assn\<close>.
  We then export code and generate a C header file to interface the code.
\<close>


 (* TODO: Move! *)
lemmas [llvm_inline] = 
  array_swap_def word_log2_impl_def 

  
global_interpretation unat_sort: pure_sort_impl_context "(\<le>)" "(<)" ll_icmp_ult unat_assn
  defines unat_sort_is_guarded_insert_impl = unat_sort.is_guarded_insert_impl
      and unat_sort_is_unguarded_insert_impl = unat_sort.is_unguarded_insert_impl
      and unat_sort_unguarded_insertion_sort_impl = unat_sort.unguarded_insertion_sort_impl
      and unat_sort_guarded_insertion_sort_impl = unat_sort.guarded_insertion_sort_impl
      and unat_sort_final_insertion_sort_impl = unat_sort.final_insertion_sort_impl
      and unat_sort_sift_down_impl   = unat_sort.sift_down_impl
      and unat_sort_heapify_btu_impl = unat_sort.heapify_btu_impl
      and unat_sort_heapsort_impl    = unat_sort.heapsort_impl
      and unat_sort_qsp_next_l_impl       = unat_sort.qsp_next_l_impl
      and unat_sort_qsp_next_h_impl       = unat_sort.qsp_next_h_impl
      and unat_sort_qs_partition_impl     = unat_sort.qs_partition_impl
      and unat_sort_partition_pivot_impl  = unat_sort.partition_pivot_impl 
      and unat_sort_introsort_aux_impl = unat_sort.introsort_aux_impl
      and unat_sort_introsort_impl        = unat_sort.introsort_impl
      and unat_sort_move_median_to_first_impl = unat_sort.move_median_to_first_impl
      
      and unat_sort_pdqsort_impl               = unat_sort.pdqsort_impl               
      and unat_sort_pdq_guarded_insort_impl    = unat_sort.pdq_guarded_insort_impl
      and unat_sort_pdq_unguarded_insort_impl  = unat_sort.pdq_unguarded_insort_impl
      and unat_sort_maybe_insort_impl          = unat_sort.maybe_insort_impl 
      (*and unat_sort_move_pivot_to_front_impl   = unat_sort.move_pivot_to_front_impl *)
      and unat_sort_partition_left_impl        = unat_sort.partition_left_impl
      and unat_sort_partition_right_impl       = unat_sort.partition_right_impl 
      (*and unat_sort_shuffle_impl               = unat_sort.shuffle_impl*)
      
  by (rule unat_sort_impl_context)


abbreviation "string_assn \<equiv> string_assn' TYPE(size_t) TYPE(8)"  
  
global_interpretation str_sort: sort_impl_context "(\<le>)" "(<)" strcmp_impl string_assn
  defines str_sort_is_guarded_insert_impl = str_sort.is_guarded_insert_impl
      and str_sort_is_unguarded_insert_impl = str_sort.is_unguarded_insert_impl
      and str_sort_unguarded_insertion_sort_impl = str_sort.unguarded_insertion_sort_impl
      and str_sort_guarded_insertion_sort_impl = str_sort.guarded_insertion_sort_impl
      and str_sort_final_insertion_sort_impl = str_sort.final_insertion_sort_impl
      and str_sort_sift_down_impl   = str_sort.sift_down_impl
      and str_sort_heapify_btu_impl = str_sort.heapify_btu_impl
      and str_sort_heapsort_impl    = str_sort.heapsort_impl
      and str_sort_qsp_next_l_impl       = str_sort.qsp_next_l_impl
      and str_sort_qsp_next_h_impl       = str_sort.qsp_next_h_impl
      and str_sort_qs_partition_impl     = str_sort.qs_partition_impl
      and str_sort_partition_pivot_impl  = str_sort.partition_pivot_impl 
      and str_sort_introsort_aux_impl = str_sort.introsort_aux_impl
      and str_sort_introsort_impl        = str_sort.introsort_impl
      and str_sort_move_median_to_first_impl = str_sort.move_median_to_first_impl
      
      and str_sort_pdqsort_impl               = str_sort.pdqsort_impl               
      and str_sort_pdq_guarded_insort_impl    = str_sort.pdq_guarded_insort_impl
      and str_sort_pdq_unguarded_insort_impl  = str_sort.pdq_unguarded_insort_impl
      and str_sort_maybe_insort_impl          = str_sort.maybe_insort_impl 
      (*and str_sort_move_pivot_to_front_impl   = str_sort.move_pivot_to_front_impl *)
      and str_sort_partition_left_impl        = str_sort.partition_left_impl
      and str_sort_partition_right_impl       = str_sort.partition_right_impl 
      (*and str_sort_shuffle_impl               = str_sort.shuffle_impl*)
      
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

  
text \<open>
  This command will generate \<open>introsort.ll\<close> and \<open>introsort.h\<close>.
  Despite the name, we export both, Introsort and Pdqsort to this file!
\<close>  


(*declare [[llvm_preproc_timing]]*)

export_llvm (timing)
  "unat_sort_introsort_impl :: 64 word ptr \<Rightarrow> _" is "uint64_t* introsort(uint64_t*, int64_t, int64_t)" 
  "unat_sort_introsort_aux_impl :: 64 word ptr \<Rightarrow> _" is "uint64_t* introsort_aux(uint64_t*, int64_t, int64_t, int64_t)" 
  "unat_sort_heapsort_impl :: 64 word ptr \<Rightarrow> _" is "uint64_t* heapsort(uint64_t*, int64_t, int64_t)" 
  "unat_sort_final_insertion_sort_impl :: 64 word ptr \<Rightarrow> _" is "uint64_t* insertion_sort(uint64_t*, int64_t, int64_t)" 

  "unat_sort_pdqsort_impl :: 64 word ptr \<Rightarrow> _" is "uint64_t* pdqsort(uint64_t*, int64_t, int64_t)"
  
  "str_init" is "void str_init(llstring *)"
  "str_append" is "void str_append(llstring *, char)"
  "llstrcmp" is "char llstrcmp(llstring*,llstring*)"
  "str_sort_introsort_impl" is "llstring* str_introsort(llstring*, int64_t, int64_t)" 
  "str_sort_pdqsort_impl" is "llstring* str_pdqsort(llstring*, int64_t, int64_t)" 
  
  defines \<open>typedef struct {int64_t size; struct {int64_t capacity; char *data;};} llstring;\<close>
  file "../code/introsort.ll"



end
