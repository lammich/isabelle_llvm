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
      and unat_ppar_sort_impl = unat_sort.ppar_sort_impl
      and unat_introsort_impl = unat_sort.introsort_impl
      and unat_pdqsort_impl = unat_sort.pdqsort_impl
      and unat_ppart_seq1_impl_uncurried = unat_sort.ppart_seq1_impl_uncurried (* TODO: Workaround, as templating seems to choke on llc_par! *)
  by (rule unat_sort_impl_context)
  
abbreviation "string_assn \<equiv> string_assn' TYPE(size_t) TYPE(8)"  
  
global_interpretation str_sort: sort_impl_copy_context "(\<le>)" "(<)" strcmp_impl string_assn arl_copy arl_free
  defines str_par_sort_impl = str_sort.par_sort_impl
      and str_ppar_sort_impl = str_sort.ppar_sort_impl
      and str_introsort_impl = str_sort.introsort_impl
      and str_pdqsort_impl = str_sort.pdqsort_impl
      and str_ppart_seq1_impl_uncurried = str_sort.ppart_seq1_impl_uncurried (* TODO: Workaround, as templating seems to choke on llc_par! *)
  by (rule strcmp_sort_impl_copy_context)
  
  
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
    if r\<noteq>0 then Mreturn 1 else Mreturn 0
  }"

  
  

declare [[llc_compile_par_call=true]]

export_llvm (timing)
  "unat_par_sort_impl :: 64 word ptr \<Rightarrow> _" is "uint64_t* par_sort(uint64_t*, int64_t)"
  "unat_ppar_sort_impl :: 64 word ptr \<Rightarrow> _" is "uint64_t* ppar_sort(uint64_t*, int64_t)"
  "unat_introsort_impl :: 64 word ptr \<Rightarrow> _" is "uint64_t* introsort(uint64_t*, int64_t, int64_t)"
  "unat_pdqsort_impl :: 64 word ptr \<Rightarrow> _" is "uint64_t* pdqsort(uint64_t*, int64_t, int64_t)"
  
  "str_init" is "void str_init(llstring * )"
  "str_append" is "void str_append(llstring *, char)"
  "llstrcmp" is "char llstrcmp(llstring*,llstring* )"
  "str_free" is "void str_free(llstring* )"
  
  "str_par_sort_impl" is "llstring* str_par_sort(llstring*, int64_t)"  
  "str_ppar_sort_impl" is "llstring* str_ppar_sort(llstring*, int64_t)"  
  "str_introsort_impl" is "llstring* str_introsort(llstring*, int64_t, int64_t)"  
  "str_pdqsort_impl" is "llstring* str_pdqsort(llstring*, int64_t, int64_t)"  
  
  defines \<open>typedef struct {int64_t size; struct {int64_t capacity; char *data;};} llstring;\<close>
  file "../code/introsort.ll"

export_llvm (timing)
  "unat_par_sort_impl :: 64 word ptr \<Rightarrow> _" is "uint64_t* par_sort(uint64_t*, int64_t)"
  "unat_ppar_sort_impl :: 64 word ptr \<Rightarrow> _" is "uint64_t* ppar_sort(uint64_t*, int64_t)"
  "unat_introsort_impl :: 64 word ptr \<Rightarrow> _" is "uint64_t* introsort(uint64_t*, int64_t, int64_t)"
  "unat_pdqsort_impl :: 64 word ptr \<Rightarrow> _" is "uint64_t* pdqsort(uint64_t*, int64_t, int64_t)"
  
  "str_init" is "void str_init(llstring * )"
  "str_append" is "void str_append(llstring *, char)"
  "llstrcmp" is "char llstrcmp(llstring*,llstring* )"
  "str_free" is "void str_free(llstring* )"
  
  "str_par_sort_impl" is "llstring* str_par_sort(llstring*, int64_t)"  
  "str_ppar_sort_impl" is "llstring* str_ppar_sort(llstring*, int64_t)"  
  "str_introsort_impl" is "llstring* str_introsort(llstring*, int64_t, int64_t)"  
  "str_pdqsort_impl" is "llstring* str_pdqsort(llstring*, int64_t, int64_t)"  
  
  defines \<open>typedef struct {int64_t size; struct {int64_t capacity; char *data;};} llstring;\<close>
  file "../../../regression/gencode/sorting.ll"
  
text \<open>Correctness lemmas for what we just exported.\<close>
thm unat_sort.par_sort_impl_correct
thm unat_sort.ppar_sort_impl_correct
thm unat_sort.introsort_impl_correct
thm unat_sort.pdqsort_impl.refine

thm str_sort.par_sort_impl_correct
thm str_sort.ppar_sort_impl_correct
thm str_sort.introsort_impl_correct
thm str_sort.pdqsort_impl.refine

text \<open>We explicitly unfold one here, to be similar to the one displayed in the paper:\<close>
lemma unat_par_sort_impl_correct: "llvm_htriple 
  (woarray_slice_assn unat_assn xs xsi \<and>* snat_assn n ni \<and>* \<up>(n = length xs)) 
  (unat_par_sort_impl xsi ni)
  (\<lambda>r. \<up>(r = xsi) \<and>* (\<lambda>s. \<exists>xs'. (woarray_slice_assn unat_assn xs' xsi \<and>* \<up>(sorted xs' \<and> mset xs'=mset xs)) s))"
  using unat_sort.par_sort_impl_correct[of xs xsi n ni] 
  unfolding sort_spec_def
  by (auto simp: conj_commute)
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
(* TODO: Move *)  
(* The essence of memory allocation in Isabelle/LLVM*)

(* It's modularised quite heavily, we'll unfold almost everything, but the transition from foundation to M-monad *)  
term ll_malloc  
term llvm_alloc
term llvmt_allocp
term llvmt_alloc
term Mmalloc
thm malloc_def
thm addr_alloc_def

(* 
  In the foundation (ne-monad), the state is explicit. 
  The malloc function selects a fresh block, and allocates it. 
  It also returns an access report, reporting the block as allocated.
  
  For paper presentation: write mmap as \<mu>[b:=ALLOC vs]
  
*)
lemma "malloc vs \<mu> = do\<^sub>n\<^sub>e {
    b \<leftarrow> spec\<^sub>n\<^sub>e b. is_FRESH \<mu> b;
    return\<^sub>n\<^sub>e (b, ACC_REPORT {} {}  {b} {}, mmap \<mu> b (\<lambda>_. ALLOC vs))
  }"
  unfolding malloc_def addr_alloc_def by simp

(*
  In order to transition to the M monad, we have to prove that malloc satisfies the M-monad's invariant:
*)  
lemma "invarM (malloc vs)" by (simp add: MMonad.invarM_lemmas) 

thm MMonad.invarM_lemmas


(* 
  This invariant ensures that access reports are consistent with state-changes, and that at least one result must be returned. 
  Note that our memory already carries an invariant, that only finitely many blocks are not fresh. 
  This is required to show that a fresh block can be selected (otherwise no result would be returned by malloc), 
  and obviously preserved by allocating one more block.
*)
thm invarM_def (* \<leftarrow> this is in paper *)

(*
  Once invariant preservation is shown, we can lift malloc into the M-monad.
*)

thm Mmalloc_def  (* Show lift-definition *)

(* This Mmalloc function is then used to model the behaviour of the standard library malloc:
  The arguments are a type and a size. We require the size to be positive, and then allocate zeroes.
  Finally, we wrap the resulting block into our val data-type, and then into the corresponding 
  shallow embedding.
*)

  
end
