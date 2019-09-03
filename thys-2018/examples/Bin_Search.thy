theory Bin_Search
imports "../sepref/IICF/IICF" "List-Index.List_Index"
begin
  (* TODO: Move to Find-Index. DONE, see AFP-4943a3cb91e3 *)  
  lemma find_index_conv_takeWhile: "find_index P xs = size(takeWhile (Not o P) xs)"
    by(induct xs) auto
  
  lemma find_index_first: "i < find_index P xs \<Longrightarrow> \<not>P (xs!i)"
    unfolding find_index_conv_takeWhile
    using takeWhile_take_has_property_nth by fastforce
  
  lemma index_first: "i<index xs x \<Longrightarrow> x\<noteq>xs!i"
    using find_index_first unfolding index_def by blast
  
  lemma find_index_append: "find_index P (xs @ ys) =
    (if \<exists>x\<in>set xs. P x then find_index P xs else size xs + find_index P ys)"
    by (induct xs) simp_all

  lemma find_index_eqI:
    assumes "i\<le>length xs"  
    assumes "\<forall>j<i. \<not>P (xs!j)"
    assumes "i<length xs \<Longrightarrow> P (xs!i)"
    shows "find_index P xs = i"
    by (metis (mono_tags, lifting) antisym_conv2 assms find_index_eq_size_conv find_index_first find_index_less_size_conv linorder_neqE_nat nth_find_index)
    
  lemma find_index_eq_iff:
    "find_index P xs = i \<longleftrightarrow> (i\<le>length xs \<and> (\<forall>j<i. \<not>P (xs!j)) \<and> (i<length xs \<longrightarrow> P (xs!i)))"  
    by (auto intro: find_index_eqI simp: nth_find_index find_index_le_size find_index_first)
    
  lemma index_eqI:
    assumes "i\<le>length xs"  
    assumes "\<forall>j<i. xs!j \<noteq> x"
    assumes "i<length xs \<Longrightarrow> xs!i = x"
    shows "index xs x = i"
    unfolding index_def by (simp add: find_index_eqI assms)
    
  lemma index_eq_iff:
    "index xs x = i \<longleftrightarrow> (i\<le>length xs \<and> (\<forall>j<i. xs!j \<noteq> x) \<and> (i<length xs \<longrightarrow> xs!i = x))"  
    by (auto intro: index_eqI simp: index_le_size index_less_size_conv dest: index_first)
    
        
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
    subgoal by clarsimp (meson assms leI le_less_trans sorted_iff_nth_mono) 
    
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

  lemma rdomp_larray_imp_len_bound: 
    "rdomp (larray_assn' TYPE('a::len2) A) xs \<Longrightarrow> length xs < max_snat LENGTH('a)"
    unfolding larray_assn_def raw_larray_assn_def larray1_rel_def
    apply (auto simp: rdomp_hrcomp_conv in_br_conv snat_rel_def snat.rel_def)
    by (simp add: list_rel_pres_length)

  sepref_definition bin_search_impl [llvm_code] is "uncurry bin_search"  
    :: "(larray_assn' TYPE(size_t) (sint_assn' TYPE(elem_t)))\<^sup>k 
        *\<^sub>a (sint_assn' TYPE(elem_t))\<^sup>k 
       \<rightarrow>\<^sub>a snat_assn' TYPE(size_t)"
    unfolding bin_search_def
    apply (rule hfref_with_rdomI)
    apply (annot_snat_const "TYPE(size_t)")
    supply rdomp_larray_imp_len_bound[dest]
    supply [simp] = max_snat_def
    apply sepref
    done
    
  export_llvm bin_search_impl is bin_search file "code/bin_search.ll"
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

end
