theory Bin_Search
imports "../sepref/IICF/IICF" "List-Index.List_Index"
begin

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

  sepref_def bin_search_impl is "uncurry bin_search"  
    :: "(larray_assn' TYPE(size_t) (sint_assn' TYPE(elem_t)))\<^sup>k 
        *\<^sub>a (sint_assn' TYPE(elem_t))\<^sup>k 
       \<rightarrow>\<^sub>a snat_assn' TYPE(size_t)"
    unfolding bin_search_def
    apply (rule hfref_with_rdomI)
    apply (annot_snat_const "TYPE(size_t)")
    apply sepref
    done

  export_llvm bin_search_impl is \<open>int64_t bin_search(larray_t, elem_t)\<close> 
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

end
