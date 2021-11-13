theory Sorting_Export_Code
imports Sorting_Parsort Sorting_Strings
begin

section \<open>Code Export\<close>

text \<open>
  We instantiate Introsort and Pdqsort for unsigned \<open>i64\<close>, and for dynamic arrays of \<open>i8\<close>s \<open>string_assn\<close>.
  We then export code and generate a C header file to interface the code.
\<close>


 (* TODO: Move! *)
lemmas [llvm_inline] = 
  array_swap_def word_log2_impl_def 

global_interpretation unat_sort: pure_sort_impl_context "(\<le>)" "(<)" ll_icmp_ult unat_assn
  defines unat_par_sort_impl = unat_sort.par_sort_impl
      and unat_introsort_impl = unat_sort.introsort_impl
      and unat_pdqsort_impl = unat_sort.pdqsort_impl
  by (rule unat_sort_impl_context)
  
abbreviation "string_assn \<equiv> string_assn' TYPE(size_t) TYPE(8)"  
  
global_interpretation str_sort: sort_impl_context "(\<le>)" "(<)" strcmp_impl string_assn
  defines str_par_sort_impl = str_sort.par_sort_impl
      and str_introsort_impl = str_sort.introsort_impl
      and str_pdqsort_impl = str_sort.pdqsort_impl
  by (rule strcmp_sort_impl_context)
  
  
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

definition str_free :: "(8 word,size_t)array_list ptr \<Rightarrow> unit llM" where [llvm_code]:
  "str_free ap \<equiv> doM {
    a \<leftarrow> ll_load ap;
    arl_free a
  }"
  
  
definition llstrcmp :: "(8 word,size_t)array_list ptr \<Rightarrow> _ \<Rightarrow> 8 word llM" where [llvm_code]:
  "llstrcmp ap bp \<equiv> doM {
    a \<leftarrow> ll_load ap;
    b \<leftarrow> ll_load bp;
    r \<leftarrow> strcmp_impl a b;
    if r\<noteq>0 then return 1 else return 0
  }"

  
  

declare [[llc_compile_par_call=true]]

export_llvm (timing)
  "unat_par_sort_impl :: 64 word ptr \<Rightarrow> _" is "uint64_t* par_sort(uint64_t*, int64_t)"
  "unat_introsort_impl :: 64 word ptr \<Rightarrow> _" is "uint64_t* introsort(uint64_t*, int64_t, int64_t)"
  "unat_pdqsort_impl :: 64 word ptr \<Rightarrow> _" is "uint64_t* pdqsort(uint64_t*, int64_t, int64_t)"
  
  "str_init" is "void str_init(llstring * )"
  "str_append" is "void str_append(llstring *, char)"
  "llstrcmp" is "char llstrcmp(llstring*,llstring* )"
  "str_free" is "void str_free(llstring* )"
  
  "str_par_sort_impl" is "llstring* str_par_sort(llstring*, int64_t)"  
  "str_introsort_impl" is "llstring* str_introsort(llstring*, int64_t, int64_t)"  
  "str_pdqsort_impl" is "llstring* str_pdqsort(llstring*, int64_t, int64_t)"  
  
  defines \<open>typedef struct {int64_t size; struct {int64_t capacity; char *data;};} llstring;\<close>
  file "../code/introsort.ll"

export_llvm (timing)
  "unat_par_sort_impl :: 64 word ptr \<Rightarrow> _" is "uint64_t* par_sort(uint64_t*, int64_t)"
  "unat_introsort_impl :: 64 word ptr \<Rightarrow> _" is "uint64_t* introsort(uint64_t*, int64_t, int64_t)"
  "unat_pdqsort_impl :: 64 word ptr \<Rightarrow> _" is "uint64_t* pdqsort(uint64_t*, int64_t, int64_t)"
  
  "str_init" is "void str_init(llstring * )"
  "str_append" is "void str_append(llstring *, char)"
  "llstrcmp" is "char llstrcmp(llstring*,llstring* )"
  "str_free" is "void str_free(llstring* )"
  
  "str_par_sort_impl" is "llstring* str_par_sort(llstring*, int64_t)"  
  "str_introsort_impl" is "llstring* str_introsort(llstring*, int64_t, int64_t)"  
  "str_pdqsort_impl" is "llstring* str_pdqsort(llstring*, int64_t, int64_t)"  
  
  defines \<open>typedef struct {int64_t size; struct {int64_t capacity; char *data;};} llstring;\<close>
  file "../../../regression/gencode/sorting.ll"
  
text \<open>Correctness lemmas for what we just exported.\<close>
thm unat_sort.par_sort_impl_correct
thm unat_sort.introsort_impl_correct
thm unat_sort.pdqsort_impl.refine

thm str_sort.par_sort_impl_correct
thm str_sort.introsort_impl_correct
thm str_sort.pdqsort_impl.refine

text \<open>We explicitly unfold one here, to be similar to the one displayed in the paper:\<close>
lemma "llvm_htriple 
  (woarray_slice_assn unat_assn xs xsi \<and>* snat_assn n ni \<and>* \<up>(n = length xs)) 
  (unat_par_sort_impl xsi ni)
  (\<lambda>r. \<up>(r = xsi) \<and>* (\<lambda>s. \<exists>xs'. (woarray_slice_assn unat_assn xs' xsi \<and>* \<up>(sorted xs' \<and> mset xs'=mset xs)) s))"
  using unat_sort.par_sort_impl_correct[of xs xsi n ni] 
  unfolding sort_spec_def sorted_sorted_wrt
  by (auto simp: conj_commute)
  
  
end
