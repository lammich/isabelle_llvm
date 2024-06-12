theory Float_Setup
imports "Isabelle_LLVM.IICF"
begin

typ double
term Rep_double
  definition "dfloat_rel = br float_of_double (\<lambda>x. True)"

  abbreviation "dfloat_assn \<equiv> pure dfloat_rel"


  definition nanize_float where "nanize_float x \<equiv> if is_nan x then SPEC is_nan else RETURN x"
  lemma nanize_double_simps[simp]: 
    "\<not>is_nan x \<Longrightarrow> nanize_float x = RETURN x"
    "is_nan x \<Longrightarrow> nanize_float x = (SPEC is_nan)"
    unfolding nanize_float_def
    by auto

  definition op_lift_farith2_rm_f :: "(roundmode \<Rightarrow> ('a::len, 'b::len) IEEE.float \<Rightarrow> ('a, 'b) IEEE.float \<Rightarrow> ('a, 'b) IEEE.float) \<Rightarrow> roundmode \<Rightarrow> ('a, 'b) IEEE.float \<Rightarrow> ('a, 'b) IEEE.float \<Rightarrow> ('a, 'b) IEEE.float nres" 
    where "op_lift_farith2_rm_f f rm a b \<equiv> nanize_float (f rm a b)"

  lemma is_nan_float_of_double: "is_nan_double x \<longleftrightarrow> is_nan (float_of_double x)"
    apply transfer by simp

  lemma float_of_double_dradd: "float_of_double (dradd rm a b) = fadd rm (float_of_double a) (float_of_double b)"
    apply transfer by simp

  lemma is_nan_double_neq_bot: "is_nan_double \<noteq> bot"
    using is_nan_double.abs_eq by fastforce

  definition "mop_fadd_rup = op_lift_farith2_rm_f fadd To_pinfinity"
  sepref_register mop_fadd_rup

  lemma mop_fadd_rup_hnr[sepref_fr_rules]: "(uncurry (ll_x86_avx512_add_sd_round AVX512_FROUND_TO_POS_INF_NO_EXC), uncurry (mop_fadd_rup)) \<in> dfloat_assn\<^sup>k *\<^sub>a dfloat_assn\<^sup>k \<rightarrow>\<^sub>a dfloat_assn"
    apply(sepref_to_hoare)
    unfolding op_lift_farith2_rm_d_def xlate_rounding_mode_def nanize_double_def ndet_nan_double_def mop_fadd_rup_def ll_x86_avx512_add_sd_round_def
    unfolding op_lift_farith2_rm_f_def nanize_float_def dfloat_rel_def br_def 
    supply [simp] = is_nan_float_of_double float_of_double_dradd is_nan_double_neq_bot
    supply [split] = if_split_asm
    by vcg' 
    

  definition add_floats :: "float64 \<Rightarrow> _" where "add_floats a b c = do{
    d \<leftarrow> mop_fadd_rup a b;
    mop_fadd_rup c d
  }"

  sepref_def add_floats_ll is "uncurry2 add_floats" :: "dfloat_assn\<^sup>k *\<^sub>a dfloat_assn\<^sup>k *\<^sub>a dfloat_assn\<^sup>k \<rightarrow>\<^sub>a dfloat_assn"
    unfolding add_floats_def
    apply sepref
    done

  declare [[llc_compile_avx512f=true]]

  export_llvm add_floats_ll 


apply fri_keep
    

  thm sepref_fr_rules(1)[to_hfref]

  definition external_fun :: "8 word ptr \<Rightarrow> 64 word \<Rightarrow> 64 word llM" where "external_fun _ _ \<equiv> Mreturn 0"

  
  lemmas foo[llvm_code_raw] = LLVM_EXTERNALI[of external_fun "''external_fun''"]
  
  definition [llvm_code]: "foo (a::8 word ptr) \<equiv> doM {
    n \<leftarrow> external_fun a 42;
    external_fun a n
  }"
  
  (*lemmas [llvm_code] = external_fun_def*)
  
  llvm_deps foo
  
  
  export_llvm foo is "foobar"

  
  oops
  xxx, ctd here:
    stress test for
    - invalid names
    - non-ground external functions
    


  

oops end end end




































 abbreviation my_array_assn where
    \<open>my_array_assn \<equiv> al_assn' TYPE(64) (word_assn :: 64 word \<Rightarrow> _)\<close>
    abbreviation my_tuple_assn where
      \<open>my_tuple_assn \<equiv> my_array_assn \<times>\<^sub>a my_array_assn \<times>\<^sub>a my_array_assn\<close>

    definition length1 where
      \<open>length1 = (\<lambda>(a,b,c). length a)\<close>

    definition length2 where
      \<open>length2 = (\<lambda>(a,b,c). length b)\<close>

    definition length3 where
      \<open>length3 = (\<lambda>(a,b,c). length c)\<close>

    sepref_def length1_impl
      is \<open>RETURN o length1\<close>
      :: \<open>my_tuple_assn\<^sup>k \<rightarrow>\<^sub>a snat_assn' (TYPE(64))\<close>
      unfolding length1_def
      by sepref
    (*works*)

    sepref_def length2_impl
      is \<open>RETURN o length2\<close>
      :: \<open>my_tuple_assn\<^sup>k \<rightarrow>\<^sub>a snat_assn' (TYPE(64))\<close>
      unfolding length2_def
      by sepref
    (*works*)

    sepref_def length3_impl
      is \<open>RETURN o length3\<close>
      :: \<open>my_tuple_assn\<^sup>k \<rightarrow>\<^sub>a snat_assn' (TYPE(64))\<close>
      unfolding length3_def op_list_length_def[symmetric]
      by sepref
      
    (*fails*)



  subsection \<open>Binary Search\<close>
    
  subsubsection \<open>Abstract Algorithm\<close>
  
  abbreviation "bin_search_invar xs x \<equiv> (\<lambda>(l,h). 
        0\<le>l \<and> l\<le>h \<and> h\<le>length xs 
      \<and> (\<forall>i<l. xs!i<x) \<and> (\<forall>i\<in>{h..<length xs}. x \<le> xs!i))"
  
  definition "bin_search xs x \<equiv> do {
    (l,h) \<leftarrow> WHILEIT (bin_search_invar xs x)
      (\<lambda>(l,h). l<h) 
      (\<lambda>(l,h). do {
        ASSERT (l<length xs \<and> h\<le>length xs \<and> l\<le>h);
        let m = l + (h-l) div 2;
        if xs!m < x then RETURN (m+1,h) else RETURN (l,m)
      }) 
      (0,length xs);
    RETURN l
  }"

  
  definition "fi_spec xs x = SPEC (\<lambda>i. i=find_index (\<lambda>y. x\<le>y) xs)"
  
  lemma bin_search_correct:
    assumes "sorted xs"
    shows "bin_search xs x \<le> SPEC (\<lambda>i. i=find_index (\<lambda>y. x\<le>y) xs)"
    unfolding bin_search_def
    apply (refine_vcg WHILEIT_rule[where R="measure (\<lambda>(l,h). h-l)"])
    apply (all \<open>(auto;fail)?\<close>)

    apply (clarsimp simp: less_Suc_eq_le)
    subgoal for l h i 
      apply (frule sorted_nth_mono[OF assms, of i "l + (h-l) div 2"])
      by auto
    subgoal
      by clarsimp (meson assms leI le_less_trans sorted_iff_nth_mono)
    
    apply clarsimp
    subgoal for i
      by (simp add: find_index_eqI less_le_not_le)
      
    done

  lemma bin_search_correct': "(uncurry bin_search,uncurry fi_spec)
    \<in>[\<lambda>(xs,_). sorted xs]\<^sub>f Id \<times>\<^sub>r Id \<rightarrow> \<langle>nat_rel\<rangle>nres_rel"  
    using bin_search_correct unfolding fi_spec_def
    by (fastforce intro!: frefI nres_relI)
    
    
  subsubsection \<open>Implementation\<close>
    
  type_synonym size_t = 64
  type_synonym elem_t = 64

  sepref_def bin_search_impl is "uncurry bin_search"  
    :: "(larray_assn' TYPE(size_t) (sint_assn' TYPE(elem_t)))\<^sup>k 
        *\<^sub>a (sint_assn' TYPE(elem_t))\<^sup>k 
       \<rightarrow>\<^sub>a snat_assn' TYPE(size_t)"
    unfolding bin_search_def
    apply (rule hfref_with_rdomI)
    apply (annot_snat_const "TYPE(size_t)")
    apply sepref    
    done

  definition [llvm_code, llvm_inline]: "bin_search_impl' a x \<equiv> doM {
    a \<leftarrow> ll_load a;
    bin_search_impl a x
  }"  
    
    
  export_llvm bin_search_impl' is \<open>int64_t bin_search(larray_t*, elem_t)\<close> 
  defines \<open>
    typedef uint64_t elem_t;
    typedef struct {
      int64_t len;
      elem_t *data;
    } larray_t;
  \<close>
  file "../../regression/gencode/bin_search.ll"
    
  export_llvm bin_search_impl' is \<open>int64_t bin_search(larray_t*, elem_t)\<close> 
  defines \<open>
    typedef uint64_t elem_t;
    typedef struct {
      int64_t len;
      elem_t *data;
    } larray_t;
  \<close>
  file "code/bin_search.ll"
  
  
  lemmas bs_impl_correct = bin_search_impl.refine[FCOMP bin_search_correct']
  
  subsubsection \<open>Combined Correctness Theorem\<close>
  
  theorem bin_search_impl_correct:
    "llvm_htriple 
      (larray_assn sint_assn xs xsi ** sint_assn x xi ** \<up>(sorted xs)) 
      (bin_search_impl xsi xi)
      (\<lambda>ii. EXS i. larray_assn sint_assn xs xsi ** sint_assn x xi ** snat_assn i ii 
                  ** \<up>(i=find_index (\<lambda>y. x\<le>y) xs))"
  proof -
  
    from bin_search_correct have R: 
        "(uncurry bin_search, uncurry (\<lambda>xs x. SPEC (\<lambda>i. i = find_index ((\<le>) x) xs))) 
      \<in> [\<lambda>(xs,x). sorted xs]\<^sub>f Id \<rightarrow> \<langle>Id\<rangle>nres_rel"
      apply (intro frefI nres_relI)
      apply fastforce 
      done
  
    note bin_search_impl.refine  
    note R = bin_search_impl.refine[FCOMP R]
    note R = R[THEN hfrefD, THEN hn_refineD, of "(xs,x)" "(xsi,xi)", simplified]
    note [vcg_rules] = R
    
    show ?thesis by vcg'
  qed

  theorem bin_search_impl'_correct:
    "llvm_htriple 
      (\<upharpoonleft>ll_pto xsi xsip ** larray_assn sint_assn xs xsi ** sint_assn x xi ** \<up>(sorted xs)) 
      (bin_search_impl' xsip xi)
      (\<lambda>ii. EXS i. \<upharpoonleft>ll_pto xsi xsip ** larray_assn sint_assn xs xsi ** sint_assn x xi ** snat_assn i ii 
                  ** \<up>(i=find_index (\<lambda>y. x\<le>y) xs))"
  proof -
    interpret llvm_prim_setup .
    show ?thesis
      unfolding bin_search_impl'_def
      supply [vcg_rules] = bin_search_impl_correct
      by vcg
  qed
  
end
