theory Sorting_Strings
imports "HOL-Library.List_Lexorder" Sorting_Setup
begin

  (* TODO: Move *)
  definition arl_copy :: "('a::llvm_rep,'l::len2) array_list \<Rightarrow> ('a,'l) array_list llM"
    where [llvm_code]: "arl_copy al \<equiv> doM {
      let (l,c,a) = al;
      a' \<leftarrow> narray_new TYPE('a) l; \<comment> \<open>Compacts the new array\<close>
      arraycpy a' a l;
      Mreturn (l,l,a')
    }"    
  
  lemma arl_copy_rule[vcg_rules]: "llvm_htriple
    (\<upharpoonleft>arl_assn xs xsi) (arl_copy xsi) (\<lambda>r. \<upharpoonleft>arl_assn xs xsi ** \<upharpoonleft>arl_assn xs r)"  
    unfolding arl_copy_def arl_assn_def arl_assn'_def
    by vcg
    
  
  lemma al_copy_hnr: "(arl_copy,RETURN o op_list_copy) \<in> (al_assn A)\<^sup>k \<rightarrow>\<^sub>a al_assn A"  
    unfolding al_assn_def hr_comp_def
    apply sepref_to_hoare 
    by vcg
  
  sepref_decl_impl al_copy_hnr uses op_list_copy.fref[of Id, simplified] .


  lemma al_copy_gen_algo[sepref_gen_algo_rules]: "GEN_ALGO arl_copy (is_copy (al_assn A))"
    using al_copy_hnr 
    unfolding GEN_ALGO_def is_copy_def COPY_def op_list_copy_def 
    .
     
    



  text \<open>The string comparison algorithm from libstdc++, abstractly: Compare min-length first, then compare lengths to break tie\<close>
  lemma list_lexorder_alt: "xs < ys \<longleftrightarrow> (let n=min (length xs) (length ys) in (take n xs < take n ys) \<or> (take n xs = take n ys \<and> length xs < length ys))"
  proof (cases "length xs < length ys")
    case True
    then show ?thesis
      apply (simp add: Let_def)
    proof (induction xs arbitrary: ys)
      case Nil
      then show ?case by (cases ys) auto 
    next
      case (Cons a xs)
      then show ?case by (cases ys) auto
    qed
  next
    case False
    then show ?thesis
      apply (simp add: Let_def)
    proof (induction xs arbitrary: ys)
      case Nil
      then show ?case by (cases ys) auto 
    next
      case (Cons a xs)
      then show ?case by (cases ys) auto
    qed
  qed
    
    
  definition cmpi :: "'a::preorder \<Rightarrow> 'a \<Rightarrow> int" where "cmpi x y \<equiv> if x = y then 0 else if x < y then -1 else (1::int)"
  
  lemma cmpi_simps[simp]: 
    "cmpi x y = 0 \<longleftrightarrow> x=y"
    "cmpi x y = -1 \<longleftrightarrow> x<y"
    "cmpi x y = 1 \<longleftrightarrow> x\<noteq>y \<and> (\<not>x<y)"
    "0 = cmpi x y \<longleftrightarrow> x=y"
    "-1 = cmpi x y \<longleftrightarrow> x<y"
    "1 = cmpi x y \<longleftrightarrow> x\<noteq>y \<and> (\<not>x<y)"
    "x=y \<Longrightarrow> cmpi x y = 0"
    "x<y \<Longrightarrow> cmpi x y = -1"
    unfolding cmpi_def by auto
  
  
  definition "compare_spec xs ys n \<equiv> doN {ASSERT (n\<le>length xs \<and> n\<le>length ys); RETURN (cmpi (take n xs) (take n ys))}"


  definition "compare1 xs ys n \<equiv> doN {
    ASSERT (n\<le>length xs \<and> n\<le>length ys);
    (i,r)\<leftarrow>WHILEIT (\<lambda>(i,r). i\<le>n \<and> r=cmpi (take i xs) (take i ys) ) (\<lambda>(i,r). i<n \<and> r=0) (\<lambda>(i,r). doN {
      x \<leftarrow> mop_list_get xs i;
      y \<leftarrow> mop_list_get ys i;
      ASSERT (i<n);
      if x=y then RETURN (i+1,0)
      else if x<y then RETURN (i+1,-1)
      else RETURN (i+1,1)
    }) (0,0);
    RETURN r
  }"

  (* TODO: Move *)    
  lemma irreflD: "irrefl R \<Longrightarrow> (x,x)\<notin>R" by (auto simp: irrefl_def) 
  
  (* TODO: Move *)
  lemma lexord_append: "length u = length w \<Longrightarrow> (u@v,w@x)\<in>lexord R \<longleftrightarrow> (u,w)\<in>lexord R \<or> (u=w \<and> (v,x)\<in>lexord R)"  
    by (induction u w rule: list_induct2) auto

  lemma lexord_irreflD: "irrefl R \<Longrightarrow> \<not>(u,u)\<in>lexord R"
    by (simp add: irreflD lexord_irrefl) 
    
  lemma lexord_irrefl_common_prefix: "irrefl R \<Longrightarrow> (u@v,u@w)\<in>lexord R \<longleftrightarrow> (v,w)\<in>lexord R"
    by (auto simp: lexord_append lexord_irreflD)
    
    
  context begin
    private lemma take_smaller: "m\<le>n \<Longrightarrow> take n xs = take m xs @ (take (n-m) (drop m xs))"
      by (metis le_add_diff_inverse take_add)
      
    private lemma compare_impl_aux1:  "\<lbrakk>aa\<le>n; aa \<le> length xs; aa\<le>length ys; take aa xs \<noteq> take aa ys\<rbrakk> \<Longrightarrow> cmpi (take n xs) (take n ys) = cmpi (take aa xs) (take aa ys)"  
      by (auto simp: take_smaller cmpi_def list_less_def lexord_append)
    
    private lemma preorder_less_irrefl: "irrefl {(x, y::_::preorder). x < y}" by (auto simp: irrefl_def) 
      
    lemma compare1_refine: "(compare1, compare_spec) \<in> Id \<rightarrow> Id \<rightarrow> Id \<rightarrow> \<langle>Id\<rangle>nres_rel"
      apply (intro fun_relI, clarsimp)
      subgoal for xs ys n
        unfolding compare1_def compare_spec_def
        apply (refine_vcg WHILEIT_rule[where R="measure (\<lambda>(i,_). n-i)"])
        by (auto simp: take_Suc_conv_app_nth list_less_def lexord_append compare_impl_aux1 lexord_irreflD[OF preorder_less_irrefl])
      done
      
  end


  abbreviation "string_assn' TYPE('size_t::len2) TYPE('w::len) \<equiv> al_assn' TYPE('size_t::len2) (unat_assn' TYPE('w::len))"
  
  sepref_definition compare_impl [llvm_inline, llvm_code] is "uncurry2 compare1" :: 
    "(string_assn' TYPE('size_t::len2) TYPE('w::len))\<^sup>k *\<^sub>a (string_assn' TYPE('size_t) TYPE('w))\<^sup>k *\<^sub>a (snat_assn' TYPE('size_t))\<^sup>k \<rightarrow>\<^sub>a sint_assn' TYPE('r::len2)"  
    unfolding compare1_def
    apply (annot_snat_const "TYPE('size_t)")
    apply (annot_sint_const "TYPE('r)")
    by sepref
  
  lemmas compare_hnr[sepref_fr_rules] = compare_impl.refine[FCOMP compare1_refine]
  
    
  definition "strcmp xs ys \<equiv> doN {
    let n = min (length xs) (length ys);
    i \<leftarrow> compare_spec xs ys n;
    if i=-1 then RETURN True
    else if i=0 then RETURN (length xs < length ys)
    else RETURN False
  }"

  lemma strcmp_correct: "strcmp xs ys \<le> RETURN (xs<ys)"  
    unfolding strcmp_def compare_spec_def
    apply (rewrite in "_ \<le> \<hole>" list_lexorder_alt)
    apply refine_vcg
    by (simp_all)
    
  lemma strcmp_refines_aux: "(strcmp,RETURN oo (<)) \<in> Id \<rightarrow> Id \<rightarrow> \<langle>Id\<rangle>nres_rel"
    using strcmp_correct by (force intro!: nres_relI)
    
  
  sepref_def strcmp_impl is "uncurry strcmp" :: "(string_assn' TYPE('size_t::len2) TYPE('w::len))\<^sup>k *\<^sub>a (string_assn' TYPE('size_t) TYPE('w))\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
    unfolding strcmp_def min_def
    apply (annot_sint_const "TYPE(2)")
    by sepref
    
  export_llvm "strcmp_impl :: 64 word \<times> 64 word \<times> 8 word ptr \<Rightarrow> 64 word \<times> 64 word \<times> 8 word ptr \<Rightarrow> 1 word llM"


  lemma strcmp_refines_relp: "GEN_ALGO strcmp_impl (refines_relp (al_assn unat_assn) (<))"
    apply rule
    using strcmp_impl.refine[FCOMP strcmp_refines_aux] .
  
  lemma strcmp_sort_impl_context: "sort_impl_context (\<le>) (<) strcmp_impl (string_assn' TYPE('size_t::len2) TYPE('w::len))"
    apply unfold_locales
    apply (auto simp: strcmp_refines_relp)
    done
  
  lemma strcmp_sort_impl_copy_context: 
    "sort_impl_copy_context (\<le>) (<) strcmp_impl (string_assn' TYPE('size_t::len2) TYPE('w::len)) arl_copy arl_free"  
  proof -
    from strcmp_sort_impl_context 
    interpret sort_impl_context "(\<le>)" "(<)" strcmp_impl "(string_assn' TYPE('size_t::len2) TYPE('w::len))" .
    
    show ?thesis
      apply unfold_locales
      apply (rule al_copy_gen_algo)
      apply (rule al_assn_free)
      done
  qed    
  
end
