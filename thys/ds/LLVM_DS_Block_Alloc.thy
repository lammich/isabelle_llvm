theory LLVM_DS_Block_Alloc
imports "../vcg/LLVM_VCG_Main"
begin

section \<open>Operations on memory blocks\<close>
context
begin
  interpretation llvm_prim_mem_setup .

definition "ll_bpto \<equiv> mk_assn (\<lambda>x p. \<up>(abase p) ** \<upharpoonleft>ll_pto x p ** ll_malloc_tag 1 p)"
definition [llvm_code, llvm_inline]: "ll_ref (x::'a::llvm_rep) \<equiv> doM { r \<leftarrow> ll_malloc TYPE('a) (1::1 word); ll_store x r; return r }"
definition ll_balloc :: "'a::llvm_rep ptr llM" where [llvm_code, llvm_inline]: "ll_balloc \<equiv> ll_malloc TYPE('a) (1::1 word)"
abbreviation "ll_balloc' TYPE('a::llvm_rep) \<equiv> ll_balloc :: 'a ptr llM"

lemma ll_range_01: "\<upharpoonleft>(ll_range {0..<1}) f p = (\<up>(abase p) ** \<upharpoonleft>ll_pto (f 0) p )"
  unfolding ll_range_def
  apply (subgoal_tac "({0..<1}::int set) = {0}")
  by auto

lemma ll_bpto_alt: "\<upharpoonleft>ll_bpto x p = (\<upharpoonleft>(ll_range {0..<1}) (\<lambda>_. x) p ** ll_malloc_tag 1 p)"
  unfolding ll_bpto_def ll_range_01
  by simp

lemma ll_bpto_null[simp]: "\<upharpoonleft>ll_bpto x null = sep_false"
  unfolding ll_bpto_def  
  by simp

    
lemma ll_ref_rule[vcg_rules]: "llvm_htriple \<box> (ll_ref x) (\<lambda>p. \<upharpoonleft>ll_bpto x p)"
  unfolding ll_bpto_def ll_ref_def 
  supply [simp] = ll_range_01
  apply vcg
  done

lemma ll_balloc_rule[vcg_rules]: "llvm_htriple \<box> (ll_balloc' TYPE('a::llvm_rep)) (\<lambda>p. \<upharpoonleft>ll_bpto (init::'a) p)"
  unfolding ll_bpto_def ll_balloc_def 
  supply [simp] = ll_range_01
  apply vcg
  done

lemma ll_free_bpto_rule[vcg_rules]: "llvm_htriple (\<upharpoonleft>ll_bpto x p) (ll_free p) (\<lambda>_. \<box>)"  
  unfolding ll_bpto_alt
  by vcg
  
lemma ll_load_bpto_rule[vcg_rules]: "llvm_htriple (\<upharpoonleft>ll_bpto x p) (ll_load p) (\<lambda>r. \<up>(r=x) ** \<upharpoonleft>ll_bpto x p)"
  unfolding ll_bpto_def
  by vcg

lemma ll_store_bpto_rule[vcg_rules]: "llvm_htriple (\<upharpoonleft>ll_bpto x p) (ll_store x' p) (\<lambda>_. \<upharpoonleft>ll_bpto x' p)"
  unfolding ll_bpto_def
  by vcg

lemma vcg_assert_valid_ptr_bpto_rule[vcg_rules]: "llvm_htriple (\<upharpoonleft>ll_bpto x p) (vcg_assert_valid_ptr p) (\<lambda>_. \<upharpoonleft>ll_bpto x p)"
  unfolding ll_bpto_def
  by vcg
    
end
  
end
