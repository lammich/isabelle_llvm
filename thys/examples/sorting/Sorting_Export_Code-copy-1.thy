theory Sorting_Export_Code
imports Sorting_Parsort Sorting_Strings
begin
  
(* TODO: Some hackery that needs to be integrated into main LLVM preprocessor.

  The first part transforms code theorems from locale instantiations as own constants,
  and sets up the inliner and monadifier to recognize them.
  
  The second part does the same with llvm_inline equations.
  Here, the monadifier must be changed to match against constants with still schematic types!

*)
(*
ML \<open>
  local
    open LLC_Lib
  in

    fun generalize_const ctxt c = let
      val T = Consts.the_constraint (Proof_Context.consts_of ctxt)
    in
      case c of 
        (Const (name,_)) => Const (name, T name)
      | (Free (name,_)) => Free (name, T name)  
      | _ => raise TERM ("generalize_const",[c])
    
    end
  
    fun make_cong_thm ctxt f n = let
    
      val f = generalize_const ctxt f
    
      val r_thm = Drule.infer_instantiate' ctxt [SOME (Thm.cterm_of ctxt f)] refl
      fun add_arg thm = thm RS @{thm fun_cong}
    in
      funpow n add_arg r_thm
    end
  
  
    fun declare_cong_thm thm context = let
      val ctxt = Context.proof_of context
      
      val ((_,thm),ctxt) = yield_singleton2 (Variable.import true) thm ctxt
      
      val (lhs,_) = dest_eqn_thm thm
      val (head,args) = strip_comb lhs

      val n = drop_suffix (fn t => is_Free t orelse is_Var t) args |> length
    in
      if n>0 then let
        val cong_thm = make_cong_thm ctxt head n
        val context = Named_Simpsets.add_cong @{named_simpset llvm_inline} cong_thm context
        
        val context = LLC_Preprocessor.Monadify.prepare_add_const_decl head context
      in
        context
      end
      else
        context
    end
    
    
    fun prepare_ho_thm orig_thm lthy = let
    
      val (_,lthy) = Local_Theory.note ((Binding.empty,@{attributes [llvm_code del]}),[orig_thm]) lthy
    
      val ((_,thm),lthy) = yield_singleton2 (Variable.import true) orig_thm lthy
    
      val (lhs,_) = dest_eqn_thm thm
    
      val (head,args) = strip_comb lhs

      (* Checks *)
            
      val mk_t = Drule.mk_term o Thm.cterm_of lthy
      
      val _ = is_Const head orelse raise THM ("Malformed code thm head",~1,[mk_t head,thm])

      val vars = fold Term.add_vars args [] |> map Var
      
      val _ = null vars orelse raise THM ("Fixed arguments contain variables",~1,map mk_t vars @ [thm])
      
      (* Declarations *)
            
      val (basename,_) = dest_Const head
      
      val basename = Long_Name.base_name basename
      
      val newname = basename ^ "_inst_" ^ serial_string ()
      val nctx = Variable.names_of lthy
      val (newname,_) = Name.variant newname nctx
      
      val new_lhs = Free (newname,fastype_of lhs)
      

      val def_term = @{mk_term "?new_lhs \<equiv> ?lhs"}     
      
      (* val _ = Thm.cterm_of lthy def_term |> @{print} *)
      
      
      (*val ((_ , (_ , def_thm)), lthy) = Local_Theory.define ((Binding.name basename,NoSyn), ((Binding.empty,[]),def_term)) lthy
      *)
      
      val ((lhs_t,(_,def_thm)),lthy) 
        = Specification.definition NONE [] [] (Binding.empty_atts,def_term) lthy;
      
      val new_thm = Local_Defs.unfold lthy [thm] def_thm 
        
      val (_,lthy) = Local_Theory.note ((Binding.empty,@{attributes [llvm_code]}), [new_thm]) lthy
      
      val inline_thm = (def_thm RS @{thm symmetric})
      
      val (_,lthy) = Local_Theory.note ((Binding.empty,@{attributes [llvm_inline]}), [inline_thm]) lthy
    
      val cong_rl = make_cong_thm lthy head (length args)
      val (_,lthy) = Local_Theory.note ((Binding.empty,@{attributes [named_ss llvm_inline cong]}), [cong_rl]) lthy
      
      val lthy = Local_Theory.declaration {pervasive=true, syntax=false} (fn phi => LLC_Preprocessor.Monadify.prepare_add_const_decl (Morphism.term phi head)) lthy
      
      (*
      xxx, ctd here:
        add inline rule
        add cong-rule
        add monadifier const decl (Use Local_Theory.declaration for that!)
      *)
      
    in
      lthy
    end
  

    fun prepare_llvm_code_thms lthy = let    
      val thms = Named_Theorems.get lthy @{named_theorems llvm_code}
        |> map (Local_Defs.abs_def_rule lthy)
        |> map (fn thm => (dest_eqn_thm thm |> fst,thm))
        |> filter (not o is_Const o fst)
        |> map snd
  
      val lthy = fold prepare_ho_thm thms lthy
    in lthy end
     
  end


\<close>


attribute_setup llvm_auto_cong = \<open>Scan.succeed (Thm.declaration_attribute declare_cong_thm)\<close>
*)


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

(*local_setup prepare_llvm_code_thms*)
  
abbreviation "string_assn \<equiv> string_assn' TYPE(size_t) TYPE(8)"  
  
global_interpretation str_sort: sort_impl_context "(\<le>)" "(<)" strcmp_impl string_assn
  defines str_par_sort_impl = str_sort.par_sort_impl
      and str_introsort_impl = str_sort.introsort_impl
      and str_pdqsort_impl = str_sort.pdqsort_impl
  by (rule strcmp_sort_impl_context)
  
  
(* Code theorem massaging hackery. Should be automated and integrated into llvm_inline and llvm_code/export_llvm! *)    
(*local_setup prepare_llvm_code_thms*)

(*
lemmas [llvm_auto_cong] = 
  unat_sort.SAMPLE_SORT.pcmpo_v_idx_impl_def[where 'a="size_t"]
  unat_sort.SAMPLE_SORT.pcmp_idxs_impl_def[where 'a="size_t"]
  unat_sort.SAMPLE_SORT.pcmpo_idxs_impl_def[where 'a="size_t"]
  unat_sort.SAMPLE_SORT.qsp_next_l_impl_def[where 'a="size_t"]
  unat_sort.SAMPLE_SORT.qsp_next_h_impl_def[where 'a="size_t"]
*)

  
  
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

(*
find_in_thms unat_sort.cmp_idxs_impl in llvm_code_raw

print_named_simpset llvm_pre_simp

lemma "P (llc_while (\<lambda>x. M_CONST unat_sort.cmp_idxs_impl xxx x1 x \<bind> return) (\<lambda>s. ll_sub s Numeral1 \<bind> return) xaa)"
  apply (simp named_ss llvm_pre_simp:)
oops
  
definition test :: "64 word \<Rightarrow> 64 word \<Rightarrow> 64 word \<Rightarrow> 64 word ptr \<Rightarrow> (64 word ptr \<times> 64 word) llM"
  where [llvm_code]: "test \<equiv> unat_sort.qs_partition_impl"

lemmas [llvm_inline] = unat_sort.cmp_idxs_impl_def  
  

definition "foo (a::64 word ptr) (b::64 word) (c::64 word) \<equiv> llc_while (\<lambda>i. doM {x \<leftarrow> unat_sort.cmp_idxs_impl a b i; return x}) (\<lambda>s. doM {
                                                                              xk \<leftarrow> return Numeral1;
                                                                              ll_sub s xk \<bind> return
                                                                            })
                            c"

oops
thm foo_def[llvm_dbg_pre_monadified] oops xxx: monadified's const-recognotion does not work for single constant

oops othm llvm_code_raw(127)[llvm_dbg_pre_monadify_inlined, llvm_dbg_pre_monadified]

find_in_thms unat_sort.qs_partition_impl in llvm_code_raw

oops

  
  
oops end end
*)

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
  

thm unat_sort.par_sort_impl_correct
thm unat_sort.introsort_impl_correct
thm unat_sort.pdqsort_impl.refine

thm str_sort.par_sort_impl_correct
thm str_sort.introsort_impl_correct
thm str_sort.pdqsort_impl.refine



(*

(*xxx, ctd here:
  if LLVM-inline comes with a constant definition,
  also declare cong-thm and monadify-const theorem!
*)  

ML_val \<open>@{term "unat_sort.SAMPLE_SORT.pcmpo_v_idx_impl"}\<close>

find_in_thms parameterized_sort_impl_context.pcmpo_v_idx_impl in llvm_code

(* xxx: monadify must try to MATCH, not just compare for equiv! *)




ML_val \<open>@{term \<open>unat_sort.final_insertion_sort_impl\<close>}\<close>

term "Sorting_Final_insertion_Sort.sort_impl_context.final_insertion_sort_impl ll_icmp_slt"

lemmas [cong] = refl[of "unat_sort.final_insertion_sort_impl"]
lemmas [cong] = refl[of "Sorting_Final_insertion_Sort.sort_impl_context.final_insertion_sort_impl x" for x]
lemmas [cong] = refl[of "Sorting_Final_insertion_Sort.sort_impl_context.final_insertion_sort_impl x" for x]
  
lemma "undefined unat_sort.final_insertion_sort_impl"
  apply (simp add: ll_icmp_ult_def)


oops end end end  
  
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
      and unat_sort_par_sort_aux_impl        = unat_sort.par_sort_aux_impl
      
      and unat_smpl_partition_pivot_impl = unat_sort.partition_pivot_sample_impl
      and unat_smpl_sorted_samples_impl = unat_sort.sorted_samples_impl
      and unat_smpl_sample_pivot_impl = unat_sort.sample_pivot_impl
      
      and unat_smpl_introsort_param_impl = unat_sort.SAMPLE_SORT.introsort_param_impl
                                     
      and unat_smpl_introsort_aux_param_impl        =    unat_sort.SAMPLE_SORT.introsort_aux_param_impl
      and unat_smpl_final_insertion_sort_param_impl =    unat_sort.SAMPLE_SORT.final_insertion_sort_param_impl
      and unat_smpl_heapsort_param_impl             =    unat_sort.SAMPLE_SORT.heapsort_param_impl
      and unat_smpl_sift_down_impl                  =    unat_sort.SAMPLE_SORT.sift_down_impl
      and unat_smpl_heapify_btu_impl                =    unat_sort.SAMPLE_SORT.heapify_btu_impl
      (*and unat_smpl_partition_pivot_impl            =    unat_sort.SAMPLE_SORT.partition_pivot_impl*)
      and unat_smpl_move_median_to_first_param_impl =    unat_sort.SAMPLE_SORT.move_median_to_first_param_impl
      and unat_smpl_qs_partition_impl               =    unat_sort.SAMPLE_SORT.qs_partition_impl      
      and unat_smpl_inner_partition_pivot_impl = unat_sort.SAMPLE_SORT.partition_pivot_impl
                          
      and unat_smpl_guarded_insertion_sort_param_impl   =  unat_sort.SAMPLE_SORT.guarded_insertion_sort_param_impl
      and unat_smpl_unguarded_insertion_sort_param_impl =  unat_sort.SAMPLE_SORT.unguarded_insertion_sort_param_impl
      and unat_smpl_is_guarded_param_insert_impl        =  unat_sort.SAMPLE_SORT.is_guarded_param_insert_impl
      and unat_smpl_is_unguarded_param_insert_impl      =  unat_sort.SAMPLE_SORT.is_unguarded_param_insert_impl
            
      and unat_smpl_idx_pcmp_impl = unat_sort.SAMPLE_SORT.idx_pcmp_impl
      
      
      and unat_sort_pdqsort_impl               = unat_sort.pdqsort_impl               
      and unat_sort_pdq_guarded_insort_impl    = unat_sort.pdq_guarded_insort_impl
      and unat_sort_pdq_unguarded_insort_impl  = unat_sort.pdq_unguarded_insort_impl
      and unat_sort_maybe_insort_impl          = unat_sort.maybe_insort_impl 
      (*and unat_sort_move_pivot_to_front_impl   = unat_sort.move_pivot_to_front_impl *)
      and unat_sort_partition_left_impl        = unat_sort.partition_left_impl
      and unat_sort_partition_right_impl       = unat_sort.partition_right_impl 
      (*and unat_sort_shuffle_impl               = unat_sort.shuffle_impl*)
      
  by (rule unat_sort_impl_context)

  
thm llvm_code  
  
declare [[llvm_preproc_timing]]  
  
llvm_deps "swap_eos_impl :: 64 word ptr \<Rightarrow> 64 word \<Rightarrow> 64 word \<Rightarrow> _"
thm "swap_eos_impl_def"

llvm_deps "unat_sort_qs_partition_impl :: _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> 64 word ptr \<Rightarrow> _"

definition [llvm_code]: "test \<equiv> sort_impl_context.equidist_impl"

llvm_deps test

ML_val "try"


thm sort_impl_context.sorted_samples_impl_def
thm unat_smpl_sorted_samples_impl_def
print_named_simpset llvm_inline  

llvm_deps "unat_smpl_sorted_samples_impl :: 64 word ptr \<Rightarrow> _"  
  

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
      and str_sort_par_sort_aux_impl        = str_sort.par_sort_aux_impl
      
      (* TODO: PDQsort disabled for now
      and str_sort_pdqsort_impl               = str_sort.pdqsort_impl               
      and str_sort_pdq_guarded_insort_impl    = str_sort.pdq_guarded_insort_impl
      and str_sort_pdq_unguarded_insort_impl  = str_sort.pdq_unguarded_insort_impl
      and str_sort_maybe_insort_impl          = str_sort.maybe_insort_impl 
      (*and str_sort_move_pivot_to_front_impl   = str_sort.move_pivot_to_front_impl *)
      and str_sort_partition_left_impl        = str_sort.partition_left_impl
      and str_sort_partition_right_impl       = str_sort.partition_right_impl 
      (*and str_sort_shuffle_impl               = str_sort.shuffle_impl*)
      *)
      
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

  
text \<open>
  This command will generate \<open>introsort.ll\<close> and \<open>introsort.h\<close>.
  Despite the name, we export both, Introsort and Pdqsort to this file!
\<close>  

lemma llc_par_summarize_bodies[llvm_inline]:
  "llc_par (\<lambda>x. doM {y\<leftarrow>f x; return y}) g = llc_par f g"
  "llc_par f (\<lambda>x. doM {y\<leftarrow>g x; return y}) = llc_par f g"
  by auto

(*  
llvm_deps  
"unat_sort_par_sort_aux_impl :: 64 word ptr \<Rightarrow> _"
*)  

declare [[llc_compile_par_call]]
export_llvm
"unat_sort_par_sort_aux_impl :: 64 word ptr \<Rightarrow> _"


oops
xxx, ctd here: adjust monadifier to not flatten higher-order parameters!

oops end end end

export_llvm (timing)
  "unat_sort_introsort_impl :: 64 word ptr \<Rightarrow> _" is "uint64_t* introsort(uint64_t*, int64_t, int64_t)" 
  "unat_sort_par_sort_aux_impl :: 64 word ptr \<Rightarrow> _" is "uint64_t* par_sort_aux(uint64_t*, int64_t, int64_t)" 
  "unat_sort_introsort_aux_impl :: 64 word ptr \<Rightarrow> _" is "uint64_t* introsort_aux(uint64_t*, int64_t, int64_t, int64_t)" 
  "unat_sort_heapsort_impl :: 64 word ptr \<Rightarrow> _" is "uint64_t* heapsort(uint64_t*, int64_t, int64_t)" 
  "unat_sort_final_insertion_sort_impl :: 64 word ptr \<Rightarrow> _" is "uint64_t* insertion_sort(uint64_t*, int64_t, int64_t)" 

   (* TODO: PDQsort disabled for now
  "unat_sort_pdqsort_impl :: 64 word ptr \<Rightarrow> _" is "uint64_t* pdqsort(uint64_t*, int64_t, int64_t)"
  *)  
  "str_init" is "void str_init(llstring * )"
  "str_append" is "void str_append(llstring *, char)"
  "llstrcmp" is "char llstrcmp(llstring*,llstring* )"
  "str_sort_introsort_impl" is "llstring* str_introsort(llstring*, int64_t, int64_t)" 
  "str_sort_par_sort_aux_impl" is "llstring* str_par_sort_aux(llstring*, int64_t, int64_t)"
  
  (* TODO: PDQsort disabled for now
  "str_sort_pdqsort_impl" is "llstring* str_pdqsort(llstring*, int64_t, int64_t)" 
  *)
  defines \<open>typedef struct {int64_t size; struct {int64_t capacity; char *data;};} llstring;\<close>
  file "../code/introsort.ll"

  
export_llvm (timing)
  "unat_sort_introsort_impl :: 64 word ptr \<Rightarrow> _" is "uint64_t* introsort(uint64_t*, int64_t, int64_t)" 
  "unat_sort_par_sort_aux_impl :: 64 word ptr \<Rightarrow> _" is "uint64_t* par_sort_aux(uint64_t*, int64_t, int64_t)" 
  (* TODO: PDQsort disabled for now
  "unat_sort_pdqsort_impl :: 64 word ptr \<Rightarrow> _" is "uint64_t* pdqsort(uint64_t*, int64_t, int64_t)"
  *)  
  "str_init" is "void str_init(llstring * )"
  "str_append" is "void str_append(llstring *, char)"
  "str_free" is "void str_free(llstring* )"
  "llstrcmp" is "char llstrcmp(llstring*,llstring* )"
  "str_sort_introsort_impl" is "llstring* str_introsort(llstring*, int64_t, int64_t)" 
  "str_sort_par_sort_aux_impl" is "llstring* str_par_sort_aux(llstring*, int64_t, int64_t)" 
  (* TODO: PDQsort disabled for now
  "str_sort_pdqsort_impl" is "llstring* str_pdqsort(llstring*, int64_t, int64_t)" 
  *)  
  
  defines \<open>typedef struct {int64_t size; struct {int64_t capacity; char *data;};} llstring;\<close>
  file "../../../regression/gencode/sorting.ll"
   
*)


end
