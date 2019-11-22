section \<open>Introsort (roughly libstdc++ version)\<close>
theory Sorting_Introsort
imports Sorting_Insertion_Sort Sorting_Heapsort Sorting_Log2 Sorting_Strings
begin
  
text \<open>Threshold for slice size to stop (partial) sorting with quicksort\<close>
abbreviation "is_threshold \<equiv> 16::nat"  


context weak_ordering begin
  
subsection \<open>Find Median\<close>

definition "move_median_to_first ri ai bi ci (xs::'a list) \<equiv> doN {
    ASSERT (ai\<noteq>bi \<and> ai\<noteq>ci \<and> bi\<noteq>ci \<and> ri\<noteq>ai \<and> ri\<noteq>bi \<and> ri\<noteq>ci);
    a \<leftarrow> mop_list_get xs ai;
    b \<leftarrow> mop_list_get xs bi;
    c \<leftarrow> mop_list_get xs ci;
  
    if a\<^bold><b then (
      if b\<^bold><c then
        mop_list_swap xs ri bi
      else if a\<^bold><c then
        mop_list_swap xs ri ci
      else 
        mop_list_swap xs ri ai
    ) 
    else if a\<^bold><c then
      mop_list_swap xs ri ai
    else if b\<^bold><c then 
      mop_list_swap xs ri ci
    else 
      mop_list_swap xs ri bi
  }"

lemma move_median_to_first_alt: "move_median_to_first ri ai bi ci (xs::'a list) = doN {
    ASSERT (ai\<noteq>bi \<and> ai\<noteq>ci \<and> bi\<noteq>ci \<and> ri\<noteq>ai \<and> ri\<noteq>bi \<and> ri\<noteq>ci);
  
    if\<^sub>N mop_cmp_idxs xs ai bi then (
      if\<^sub>N mop_cmp_idxs xs bi ci then
        mop_list_swap xs ri bi
      else if\<^sub>N mop_cmp_idxs xs ai ci then
        mop_list_swap xs ri ci
      else 
        mop_list_swap xs ri ai
    ) 
    else if\<^sub>N mop_cmp_idxs xs ai ci then
      mop_list_swap xs ri ai
    else if\<^sub>N mop_cmp_idxs xs bi ci then 
      mop_list_swap xs ri ci
    else 
      mop_list_swap xs ri bi
  }"
  unfolding move_median_to_first_def
  by (auto simp: pw_eq_iff refine_pw_simps split!: if_splits)
  
  
lemma move_median_to_first_correct:
  "\<lbrakk> ri<ai; ai<bi; bi<ci; ci<length xs \<rbrakk> \<Longrightarrow> 
  move_median_to_first ri ai bi ci xs 
    \<le> SPEC (\<lambda>xs'. \<exists>i\<in>{ai,bi,ci}. 
        xs' = swap xs ri i
      \<and> (\<exists>j\<in>{ai,bi,ci}-{i}. xs!i\<^bold>\<le>xs!j)   
      \<and> (\<exists>j\<in>{ai,bi,ci}-{i}. xs!i\<^bold>\<ge>xs!j)   
      )"
  unfolding move_median_to_first_def
  apply refine_vcg
  supply aux = bexI[where P="\<lambda>x. _=_ x \<and> _ x", OF conjI[OF refl]]
  apply ((rule aux)?; insert connex,auto simp: unfold_lt_to_le)+
  done
  
    
lemma move_median_to_first_correct':
  "\<lbrakk> ri<ai; ai<bi; bi<ci; ci<length xs \<rbrakk> \<Longrightarrow> 
  move_median_to_first ri ai bi ci xs 
    \<le> SPEC (\<lambda>xs'. slice_eq_mset ri (ci+1) xs' xs 
      \<and> (\<exists>i\<in>{ai,bi,ci}. xs'!i\<^bold>\<le>xs'!ri)
      \<and> (\<exists>i\<in>{ai,bi,ci}. xs'!i\<^bold>\<ge>xs'!ri)
      )"
  apply (rule order_trans[OF move_median_to_first_correct])    
  by auto
  
(* TODO: Clean up prove below, to use more concise aux-lemma! *)  
lemma move_median_to_first_correct'':
  "\<lbrakk> ri<ai; ai<bi; bi<ci; ci<length xs \<rbrakk> \<Longrightarrow> 
  move_median_to_first ri ai bi ci xs 
    \<le> SPEC (\<lambda>xs'. slice_eq_mset ri (ci+1) xs' xs 
      \<and> (\<exists>i\<in>{ai..ci}. xs'!i\<^bold>\<le>xs'!ri)
      \<and> (\<exists>i\<in>{ai..ci}. xs'!i\<^bold>\<ge>xs'!ri)
      )"
  apply (rule order_trans[OF move_median_to_first_correct'])    
  by auto
  
end

context sort_impl_context begin 
  
sepref_register move_median_to_first

sepref_def move_median_to_first_impl [llvm_inline] is "uncurry4 (PR_CONST move_median_to_first)" :: "size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k *\<^sub>a (arr_assn)\<^sup>d \<rightarrow>\<^sub>a arr_assn"
  unfolding move_median_to_first_alt PR_CONST_def
  by sepref 
                    
end

context weak_ordering begin  
  
subsection \<open>Hoare Partitioning Scheme\<close>  


definition "ungrd_qsp_next_l_spec xs pi li \<equiv> 
  doN {
    ASSERT (pi<li \<and> pi<length xs);
    ASSERT (\<exists>i\<in>{li..<length xs}. xs!i \<^bold>\<ge> xs!pi); 
    SPEC (\<lambda>li'. li\<le>li' \<and> li'<length xs \<and> (\<forall>i\<in>{li..<li'}. xs!i\<^bold><xs!pi) \<and> xs!li'\<^bold>\<ge>xs!pi)
  }"

definition "ungrd_qsp_next_h_spec xs pi hi \<equiv> 
  doN {
    ASSERT (pi<length xs \<and> hi\<le>length xs \<and> (\<exists>i\<in>{pi<..<hi}. (xs!i) \<^bold>\<le> xs!pi)); 
    SPEC (\<lambda>hi'. hi'<hi \<and> (\<forall>i\<in>{hi'<..<hi}. xs!i\<^bold>>xs!pi) \<and> xs!hi'\<^bold>\<le>xs!pi)
  }"
  
  
definition qsp_next_l :: "'a list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat nres" where            
  "qsp_next_l xs pi li \<equiv> doN {
    monadic_WHILEIT (\<lambda>li'. (\<exists>i\<in>{li'..<length xs}. xs!i\<^bold>\<ge>xs!pi) \<and> li\<le>li' \<and> (\<forall>i\<in>{li..<li'}. xs!i\<^bold><xs!pi)) 
      (\<lambda>li. doN {ASSERT (li\<noteq>pi); mop_cmp_idxs xs li pi}) (\<lambda>li. RETURN (li + 1)) li
  }"  

  
  
find_theorems monadic_WHILEIT wf
  
lemma qsp_next_l_refine: "(qsp_next_l,PR_CONST ungrd_qsp_next_l_spec)\<in>Id\<rightarrow>Id\<rightarrow>Id\<rightarrow>\<langle>Id\<rangle>nres_rel"
  unfolding qsp_next_l_def ungrd_qsp_next_l_spec_def PR_CONST_def
  apply (intro fun_relI; clarsimp)
  subgoal for xs p li 
    apply (refine_vcg monadic_WHILEIT_rule[where R="measure (\<lambda>li. length xs - li)"])
    apply simp_all
    apply safe
    subgoal by simp
    subgoal by (metis atLeastLessThan_iff leI le_less_Suc_eq wo_leD)
    subgoal using less_eq_Suc_le by force
    subgoal by auto
    subgoal by (auto simp: unfold_le_to_lt)
    done  
  done

  
(*  
definition qsp_next_l_checked :: "'a list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat nres" where            
  "qsp_next_l_checked xs pi li \<equiv> doN {
    monadic_WHILEIT (\<lambda>li'. li\<le>li' \<and> (\<forall>i\<in>{li..<li'}. xs!i\<^bold><xs!pi)) 
      (\<lambda>li'. if li'<li then doN {ASSERT (li\<noteq>pi); mop_cmp_idxs xs li' pi} else RETURN False) (\<lambda>li. RETURN (li + 1)) li
  }"  
  
lemma qsp_next_l_checked_refine: "(qsp_next_l_checked,PR_CONST ungrd_qsp_next_l_spec)\<in>Id\<rightarrow>Id\<rightarrow>Id\<rightarrow>\<langle>Id\<rangle>nres_rel"
  unfolding qsp_next_l_def ungrd_qsp_next_l_spec_def PR_CONST_def
  apply (intro fun_relI; clarsimp)
  subgoal for xs p li 
    apply (refine_vcg monadic_WHILEIT_rule[where R="measure (\<lambda>li. length xs - li)"])
    apply simp_all
    apply safe
    subgoal by simp
    subgoal by (metis atLeastLessThan_iff leI le_less_Suc_eq wo_leD)
    subgoal using less_eq_Suc_le by force
    subgoal by auto
    subgoal by (auto simp: unfold_le_to_lt)
    done  
  done
*)  
(*    
lemma qsp_next_l_correct[refine_vcg]: "\<lbrakk>\<exists>pi\<in>{li..<length xs}. xs!pi \<^bold>\<ge> p\<rbrakk> 
  \<Longrightarrow> qsp_next_l xs p li 
    \<le> SPEC (\<lambda>li'. li\<le>li' \<and> li'<length xs \<and> (\<forall>i\<in>{li..<li'}. xs!i\<^bold><p) \<and> xs!li'\<^bold>\<ge>p)"
  unfolding qsp_next_l_def
  apply (refine_vcg WHILEIT_rule[where R="measure (\<lambda>li. length xs - li)"])
  apply simp_all
  subgoal by (metis atLeastLessThan_iff leI less_antisym unfold_lt_to_le)
  subgoal using less_eq_Suc_le by force
  subgoal by auto
  subgoal by auto
  subgoal by (auto simp: unfold_le_to_lt)
  done
*)
  
definition qsp_next_h :: "'a list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat nres" where
  "qsp_next_h xs pi hi \<equiv> doN {
    ASSERT (hi>0);
    let hi = hi - 1;
    ASSERT (hi<length xs);
    monadic_WHILEIT (\<lambda>hi'. hi'\<le>hi \<and> (\<exists>i\<le>hi'. xs!i\<^bold>\<le>xs!pi) \<and> (\<forall>i\<in>{hi'<..hi}. xs!i\<^bold>>xs!pi))
      (\<lambda>hi. doN {ASSERT(pi\<noteq>hi); mop_cmp_idxs xs pi hi}) (\<lambda>hi. doN { ASSERT(hi>0); RETURN (hi - 1)}) hi
  }"  

  
lemma qsp_next_h_refine: "(qsp_next_h,PR_CONST (ungrd_qsp_next_h_spec)) \<in> Id \<rightarrow> Id \<rightarrow> Id \<rightarrow> \<langle>Id\<rangle>nres_rel"
  unfolding qsp_next_h_def ungrd_qsp_next_h_spec_def PR_CONST_def
  apply (refine_vcg monadic_WHILEIT_rule[where R="measure id"] split_ifI)
  apply (all \<open>(determ \<open>elim conjE exE\<close>)?\<close>)
  apply simp_all
  subgoal by force
  subgoal by (meson greaterThanLessThan_iff nat_le_Suc_less_imp)
  subgoal by (meson greaterThanAtMost_iff greaterThanLessThan_iff nat_le_Suc_less_imp wo_leD)
  subgoal by (metis gr0I le_zero_eq unfold_lt_to_le)
  subgoal by (metis One_nat_def le_step_down_nat wo_leD)
  subgoal by (metis Suc_pred greaterThanAtMost_iff linorder_neqE_nat not_less_eq)
  subgoal by (meson greaterThanAtMost_iff greaterThanLessThan_iff nat_le_Suc_less_imp)
  subgoal using wo_leI by blast
  done  

  

  
(*  
lemma qsp_next_h_correct[refine_vcg]: "\<lbrakk> hi\<le>length xs; \<exists>pi<hi. xs!pi \<^bold>\<le> p \<rbrakk> 
  \<Longrightarrow> qsp_next_h xs p hi \<le> SPEC (\<lambda>hi'. hi'<hi \<and> (\<forall>i\<in>{hi'<..<hi}. xs!i\<^bold>>p) \<and> xs!hi'\<^bold>\<le>p)"
  unfolding qsp_next_h_def
  apply (refine_vcg WHILEIT_rule[where R="measure id"])
  apply (all \<open>(determ \<open>elim conjE exE\<close>)?\<close>)
  apply simp_all
  subgoal using nat_le_Suc_less_imp by blast
  subgoal by (metis gr0I le_zero_eq unfold_lt_to_le)
  subgoal by (metis One_nat_def le_step_down_nat wo_leD)
  subgoal by (metis Suc_pred greaterThanAtMost_iff linorder_neqE_nat not_less_eq)
  subgoal by (meson greaterThanAtMost_iff greaterThanLessThan_iff nat_le_Suc_less_imp)
  subgoal using wo_leI by blast
  done
*)
  
    
(*
  invariant is:
  
    li\<le>hi
    hi<length xs
   
    mset is equal 
    
    xs{0..<li} < p
    xs!li \<ge> p
    
    xs!hi \<le> p
    xs{hi<..<length xs} > p
    
  variant: measure hi   
*)  


definition "qs_partition li\<^sub>0 hi\<^sub>0 pi xs\<^sub>0 \<equiv> doN {
  ASSERT (pi < li\<^sub>0 \<and> li\<^sub>0<hi\<^sub>0 \<and> hi\<^sub>0\<le>length xs\<^sub>0);
  
  \<comment> \<open>Initialize\<close>
  li \<leftarrow> ungrd_qsp_next_l_spec xs\<^sub>0 pi li\<^sub>0;
  hi \<leftarrow> ungrd_qsp_next_h_spec xs\<^sub>0 pi hi\<^sub>0;
  
  ASSERT (li\<^sub>0\<le>hi);
  
  (xs,li,hi) \<leftarrow> WHILEIT 
    (\<lambda>(xs,li,hi). 
        li\<^sub>0\<le>li \<and> hi<hi\<^sub>0
      \<and> li<hi\<^sub>0 \<and> hi\<ge>li\<^sub>0  
      \<and> slice_eq_mset li\<^sub>0 hi\<^sub>0 xs xs\<^sub>0
      \<and> xs!pi = xs\<^sub>0!pi
      \<and> (\<forall>i\<in>{li\<^sub>0..<li}. xs!i \<^bold>\<le> xs\<^sub>0!pi)
      \<and> xs!li \<^bold>\<ge> xs\<^sub>0!pi
      \<and> (\<forall>i\<in>{hi<..<hi\<^sub>0}. xs!i \<^bold>\<ge> xs\<^sub>0!pi)
      \<and> xs!hi \<^bold>\<le> xs\<^sub>0!pi  
    )
    (\<lambda>(xs,li,hi). li<hi) 
    (\<lambda>(xs,li,hi). doN {
      ASSERT(li<length xs \<and> hi<length xs \<and> li\<noteq>hi);
      xs \<leftarrow> mop_list_swap xs li hi;
      let li = li + 1;
      li \<leftarrow> ungrd_qsp_next_l_spec xs pi li;
      hi \<leftarrow> ungrd_qsp_next_h_spec xs pi hi;
      RETURN (xs,li,hi)
    }) 
    (xs\<^sub>0,li,hi);
  
  RETURN (xs,li)
}"  



(* TODO: Move. Found useful for ATPs *)
lemma strict_itrans: "a < c \<Longrightarrow> a < b \<or> b < c" for a b c :: "_::linorder"
  by auto
  
lemma qs_partition_correct:
  "\<lbrakk> pi<li; li<hi; hi\<le>length xs\<^sub>0; \<exists>i\<in>{li..<hi}. xs\<^sub>0!pi\<^bold>\<le>xs\<^sub>0!i; \<exists>i\<in>{li..<hi}. xs\<^sub>0!i\<^bold>\<le>xs\<^sub>0!pi \<rbrakk> \<Longrightarrow> qs_partition li hi pi xs\<^sub>0 
  \<le> SPEC (\<lambda>(xs,i). slice_eq_mset li hi xs xs\<^sub>0 \<and> li\<le>i \<and> i<hi \<and> (\<forall>i\<in>{li..<i}. xs!i\<^bold>\<le>xs\<^sub>0!pi) \<and> (\<forall>i\<in>{i..<hi}. xs!i\<^bold>\<ge>xs\<^sub>0!pi) )"  
  unfolding qs_partition_def ungrd_qsp_next_l_spec_def ungrd_qsp_next_h_spec_def
  apply (refine_vcg WHILEIT_rule[where R="measure (\<lambda>(_,_,hi). hi)"])  
  supply [[put_named_ss HOL_ss]]
  apply (all \<open>(clarsimp;fail)?\<close>)
  apply clarsimp_all
  supply [[put_named_ss Main_ss]]
  apply (simp_all add: slice_eq_mset_eq_length unfold_lt_to_le)
  
  subgoal by fastforce
  subgoal by auto
  
  
  subgoal  by (smt greaterThanLessThan_iff leI less_le_trans)
  subgoal 
    by (metis (no_types) atLeastLessThan_iff le_less_trans le_less_linear)
  subgoal
    by (metis less_trans less_le_trans slice_eq_mset_eq_length swap_length)
    
  subgoal
    by (metis Suc_leI atLeastLessThan_iff less_le_trans less_not_sym slice_eq_mset_eq_length swap_indep swap_length swap_nth2)
  
  subgoal
    by (metis dual_order.strict_trans leD leI slice_eq_mset_eq_length swap_length)
     
  subgoal 
    by (metis (no_types, lifting) Suc_le_lessD dual_order.strict_trans greaterThanLessThan_iff leD linorder_neqE_nat swap_indep swap_length swap_nth1)
  subgoal apply clarsimp
    by (smt Suc_leI atLeastLessThan_iff le_def less_trans le_neq_implies_less swap_indep swap_length swap_nth2)
      
  subgoal apply clarsimp
    by (smt greaterThanLessThan_iff less_trans not_le_imp_less le_neq_implies_less swap_indep swap_length swap_nth1)
     
  subgoal
    by (meson atLeastLessThan_iff le_less_trans less_imp_le_nat slice_eq_mset_swap(1))
    
  subgoal apply clarsimp
    by (metis less_irrefl less_imp_not_less less_le_trans swap_indep)
    
  subgoal apply clarsimp
    by (smt Suc_leI atLeastLessThan_iff le_def less_le_trans less_Suc_eq swap_indep swap_length swap_nth1)
  subgoal apply clarsimp
    by (metis le_def less_trans swap_indep)
      
  subgoal apply clarsimp
    by (smt greaterThanLessThan_iff le_def less_le_trans le_neq_implies_less less_imp_le_nat slice_eq_mset_eq_length swap_indep swap_nth2)
    
  subgoal
    by (metis le_def less_trans swap_indep)
  subgoal
    by (metis greaterThanLessThan_iff strict_itrans le_neq_implies_less)
    
  done
    
corollary qs_partition_mset:
  "\<lbrakk> pi<li; li<hi; hi\<le>length xs\<^sub>0; \<exists>i\<in>{li..<hi}. xs\<^sub>0!pi\<^bold>\<le>xs\<^sub>0!i; \<exists>i\<in>{li..<hi}. xs\<^sub>0!i\<^bold>\<le>xs\<^sub>0!pi \<rbrakk> \<Longrightarrow> qs_partition li hi pi xs\<^sub>0 
  \<le> SPEC (\<lambda>(xs,i). slice_eq_mset li hi xs xs\<^sub>0 \<and> li\<le>i \<and> i<hi )"  
  apply (refine_vcg qs_partition_correct)
  by auto

  
(*definition "qs_partitionXXX li\<^sub>0 hi\<^sub>0 pi xs\<^sub>0 \<equiv> doN {
  ASSERT (pi < li\<^sub>0 \<and> li\<^sub>0<hi\<^sub>0 \<and> hi\<^sub>0\<le>length xs\<^sub>0);
  
  (xs,li,hi,_) \<leftarrow> WHILEIT (\<lambda>_. True) (\<lambda>(xs,li,hi,brk). \<not>brk) (\<lambda>(xs,li,hi,brk). doN {
      ASSERT (length xs = length xs\<^sub>0);
      li \<leftarrow> ungrd_qsp_next_l_spec xs pi li;
      hi \<leftarrow> ungrd_qsp_next_h_spec xs pi hi;
      
      if \<not>(li<hi) then RETURN (xs,li,hi,True)
      else doN {
        ASSERT(li<length xs \<and> hi<length xs \<and> li\<noteq>hi);
        xs \<leftarrow> mop_list_swap xs li hi;
        let li = li + 1;
        RETURN (xs,li,hi,False)
      }
    
    })
    (xs\<^sub>0,li\<^sub>0,hi\<^sub>0,False);

  RETURN (xs,li)
}"  
*)

  
  
    
definition "partition_pivot xs\<^sub>0 l h \<equiv> doN {
  ASSERT (l\<le>h \<and> h\<le>length xs\<^sub>0 \<and> h-l\<ge>4);
  let m = l + (h-l) div 2;
  xs \<leftarrow> move_median_to_first l (l+1) m (h-1) xs\<^sub>0;
  ASSERT (l<length xs \<and> length xs = length xs\<^sub>0);
  (xs,m) \<leftarrow> qs_partition (l+1) h l xs;

  RETURN (xs,m)
}"

lemma partition_pivot_mset: "\<lbrakk> l\<le>h ; h\<le>length xs; h-l\<ge>4 \<rbrakk> \<Longrightarrow> partition_pivot xs l h 
  \<le> SPEC (\<lambda>(xs',m). slice_eq_mset l h xs' xs \<and> l<m \<and> m<h)"
  unfolding partition_pivot_def
  apply (refine_vcg move_median_to_first_correct'' qs_partition_mset)
  apply (auto 0 3 dest: slice_eq_mset_eq_length elim: )
  by (smt add.commute le_add1 le_trans order.strict_implies_order order_mono_setup.refl plus_1_eq_Suc slice_eq_mset_subslice slice_eq_mset_trans)

end
  

(*
xxx, ctd here: Refine or change to use woarray (and eoarray where necessary)
  \<rightarrow> may need woarray cmp_idxs function!
*)

context sort_impl_context begin
  
sepref_register ungrd_qsp_next_l_spec ungrd_qsp_next_h_spec 

(* TODO: We can get rid of the length xs restriction: the stopper element will always lie within <h, which is size_t representable! *)
sepref_definition qsp_next_l_impl [llvm_inline] is "uncurry2 (qsp_next_l)" :: "[\<lambda>((xs,p),i). length xs < max_snat LENGTH(size_t)]\<^sub>a (arr_assn)\<^sup>k *\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k \<rightarrow> size_assn"
  unfolding qsp_next_l_def PR_CONST_def
  apply (annot_snat_const "TYPE(size_t)")
  by sepref

lemmas [sepref_fr_rules] = qsp_next_l_impl.refine[FCOMP qsp_next_l_refine]  
  
sepref_definition qsp_next_h_impl [llvm_inline] is "uncurry2 (qsp_next_h)" :: "(arr_assn)\<^sup>k *\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k \<rightarrow>\<^sub>a size_assn"
  unfolding qsp_next_h_def PR_CONST_def
  apply (annot_snat_const "TYPE(size_t)")
  by sepref
  
lemmas [sepref_fr_rules] = qsp_next_h_impl.refine[FCOMP qsp_next_h_refine]  
  
                        
sepref_register qs_partition  
sepref_def qs_partition_impl (*[llvm_inline]*) is "uncurry3 (PR_CONST qs_partition)" :: "[\<lambda>(((l,h),p),xs). length xs < max_snat LENGTH(size_t)]\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k *\<^sub>a (arr_assn)\<^sup>d \<rightarrow> arr_assn \<times>\<^sub>a size_assn"
  unfolding qs_partition_def PR_CONST_def
  apply (annot_snat_const "TYPE(size_t)")
  supply [dest] = slice_eq_mset_eq_length
  by sepref

(*sepref_register qs_partitionXXX  
sepref_def qs_partitionXXX_impl (*[llvm_inline]*) is "uncurry3 (PR_CONST qs_partitionXXX)" :: "[\<lambda>(((l,h),p),xs). length xs < max_snat LENGTH(size_t)]\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k *\<^sub>a (arr_assn)\<^sup>d \<rightarrow> arr_assn \<times>\<^sub>a size_assn"
  unfolding qs_partitionXXX_def PR_CONST_def
  apply (annot_snat_const "TYPE(size_t)")
  supply [dest] = slice_eq_mset_eq_length
  by sepref
*)  

sepref_register partition_pivot  
sepref_def partition_pivot_impl [llvm_inline] is "uncurry2 (PR_CONST partition_pivot)" :: "[\<lambda>((xs,l),h). length xs < max_snat LENGTH(size_t)]\<^sub>a arr_assn\<^sup>d *\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k \<rightarrow> arr_assn \<times>\<^sub>a size_assn"
  unfolding partition_pivot_def PR_CONST_def    
  apply (annot_snat_const "TYPE(size_t)")
  by sepref

  

subsection \<open>Partial Quicksort\<close>  
 
definition "introsort_qs_aux xs\<^sub>0 l h d \<equiv> RECT (\<lambda>introsort_qs_aux (xs,l,h,d). doN {
  ASSERT (l\<le>h \<and> h\<le>length xs \<and> length xs = length xs\<^sub>0);
  
  if h-l > is_threshold then doN {
    if d>0 then doN {
      (xs,m) \<leftarrow> partition_pivot xs l h;
      
      ASSERT (l<m \<and> m<h);
  
      xs \<leftarrow> introsort_qs_aux (xs,l,m,d-1);    
      xs \<leftarrow> introsort_qs_aux (xs,m,h,d-1);    
    
      RETURN xs
    } else doN {
      xs\<leftarrow>heapsort xs l h;  
      RETURN xs
    }
  } else   
    RETURN xs
    
}) (xs\<^sub>0,l,h,d)"   
  
lemma introsort_qs_aux_mset: "\<lbrakk> l\<^sub>0\<le>h\<^sub>0; h\<^sub>0\<le>length xs\<^sub>0\<rbrakk> \<Longrightarrow> introsort_qs_aux xs\<^sub>0 l\<^sub>0 h\<^sub>0 d \<le> SPEC (\<lambda>xs'. slice_eq_mset l\<^sub>0 h\<^sub>0 xs' xs\<^sub>0)"
  unfolding introsort_qs_aux_def
  apply (refine_vcg RECT_rule[where 
    pre="\<lambda>(xs',l,h,d). l\<^sub>0\<le>l \<and> h\<le>h\<^sub>0 \<and> l\<le>h \<and> h\<le>length xs' \<and> slice_eq_mset l\<^sub>0 h\<^sub>0 xs' xs\<^sub>0" and
    V="measure (\<lambda>(_,l,h,d). h-l)"]
  
    partition_pivot_mset  
    (*qs_partition_mset*)
    
  )
  apply (all \<open>(auto dest: slice_eq_mset_eq_length;fail)?\<close>)
  apply (rule order_trans)
  apply rprems
  subgoal
    apply (auto simp: slice_eq_mset_eq_length)
    by (meson less_imp_not_less less_le_trans nat_le_linear slice_eq_mset_subslice slice_eq_mset_trans)
  subgoal by auto []
  apply refine_vcg
  apply (rule order_trans)
  apply rprems
  subgoal by (auto simp: slice_eq_mset_eq_length)
  subgoal by auto
  subgoal by refine_vcg
  
  subgoal 
    apply (refine_vcg heapsort_correct) 
    subgoal by auto
    subgoal by auto
    subgoal by clarsimp (meson slice_eq_mset_subslice slice_eq_mset_trans)
    done
  
  done
    
  
subsection \<open>Main Sorting Function\<close>  
  
definition "introsort xs l h \<equiv> doN {
  ASSERT(l\<le>h);
  if h-l>1 then doN {
    xs \<leftarrow> introsort_qs_aux xs l h (Discrete.log (h-l) * 2);
    xs \<leftarrow> insertion_sort xs l h;
    RETURN xs
  } else RETURN xs
}"  


lemma slice_sort_spec01: "h-l\<le>1 \<Longrightarrow> RETURN xs \<le> slice_sort_spec (\<^bold><) xs l h"
  unfolding slice_sort_spec_def sort_spec_def
  apply refine_vcg
  by (auto simp: sorted_wrt01)

lemma introsort_correct: 
  assumes "l\<le>h" "h\<le>length xs"
  shows "introsort xs l h \<le> slice_sort_spec (\<^bold><) xs l h"
  unfolding introsort_def 
  (* Manual refinement of LHS to use specs. TODO: Define this abstract fun explicitly! *)
  apply (cases "h-l>1")
  subgoal
    apply (simp add: assms)
    apply (rule order_trans)
    apply (rule bind_mono)
    apply (rule introsort_qs_aux_mset[OF assms])
    apply (rule insertion_sort_correct[param_fo, OF IdI IdI IdI, THEN nres_relD, simplified])
  
    (* show that slice_sort on eq-mset-slice implies slice-sort  *)
    apply (auto simp: pw_le_iff pw_nres_rel_iff refine_pw_simps slice_sort_spec_def slice_eq_mset_def intro: sort_spec_permute)  
    done
  subgoal  
    by (auto simp: slice_sort_spec01 assms)
    
  done

sepref_register introsort_qs_aux 
sepref_def introsort_qs_aux_impl is "uncurry3 (PR_CONST introsort_qs_aux)" :: "[\<lambda>(((xs,l),h),d). length xs < max_snat LENGTH(size_t)]\<^sub>a (arr_assn)\<^sup>d *\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k \<rightarrow> arr_assn"
  unfolding introsort_qs_aux_def PR_CONST_def
  apply (annot_snat_const "TYPE(size_t)")
  by sepref

lemma introsort_depth_limit_in_bounds_aux: (* TODO: Move depth-computation into own (inline) function *)
  assumes "n < max_snat N" "1<N" shows "Discrete.log (n) * 2 < max_snat N"
proof (cases "n=0")
  case True thus ?thesis using assms by auto
next
  case [simp]: False  
  have ?thesis if "Discrete.log (n) < max_snat (N-1)"
    using that \<open>1<N\<close> unfolding max_snat_def
    by (metis nat_mult_power_less_eq pos2 semiring_normalization_rules(33))
  moreover have "Discrete.log (n) < max_snat (N-1)"
    apply (rule discrete_log_ltI)
    using assms apply (auto simp: max_snat_def)
    by (smt Suc_diff_Suc leI le_less_trans n_less_equal_power_2 nat_power_less_imp_less not_less_eq numeral_2_eq_2 numeral_2_eq_2 zero_order(3))
  ultimately show ?thesis .
qed  
  
sepref_register introsort 
sepref_def introsort_impl is "uncurry2 (PR_CONST introsort)" :: "[\<lambda>((xs,l),h). length xs < max_snat LENGTH(size_t)]\<^sub>a (arr_assn)\<^sup>d *\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k \<rightarrow> arr_assn"
  unfolding introsort_def PR_CONST_def
  apply (annot_snat_const "TYPE(size_t)")
  supply [intro!] = introsort_depth_limit_in_bounds_aux 
  by sepref

end  


global_interpretation unat_sort: pure_sort_impl_context "(\<le>)" "(<)" ll_icmp_ult unat_assn
  defines unat_sort_is_insert_impl = unat_sort.is_insert_impl
      and unat_sort_is_unguarded_insert_impl = unat_sort.is_unguarded_insert_impl
      and unat_sort_insertion_sort_impl = unat_sort.insertion_sort_impl
      and unat_sort_mop_lchild_impl  = unat_sort.mop_lchild_impl 
      and unat_sort_mop_rchild_impl  = unat_sort.mop_rchild_impl 
      and unat_sort_has_rchild_impl  = unat_sort.has_rchild_impl 
      and unat_sort_has_lchild_impl  = unat_sort.has_lchild_impl 
      and unat_sort_mop_geth_impl    = unat_sort.mop_geth_impl  
      and unat_sort_mop_seth_impl    = unat_sort.mop_seth_impl  
      and unat_sort_sift_down_impl   = unat_sort.sift_down_impl
      and unat_sort_heapify_btu_impl = unat_sort.heapify_btu_impl
      and unat_sort_heapsort_impl    = unat_sort.heapsort_impl
      and unat_sort_qsp_next_l_impl       = unat_sort.qsp_next_l_impl
      and unat_sort_qsp_next_h_impl       = unat_sort.qsp_next_h_impl
      and unat_sort_qs_partition_impl     = unat_sort.qs_partition_impl
(*      and unat_sort_qs_partitionXXX_impl     = unat_sort.qs_partitionXXX_impl *)
      and unat_sort_partition_pivot_impl  = unat_sort.partition_pivot_impl 
      and unat_sort_introsort_qs_aux_impl = unat_sort.introsort_qs_aux_impl
      and unat_sort_introsort_impl        = unat_sort.introsort_impl
      and unat_sort_move_median_to_first_impl = unat_sort.move_median_to_first_impl
  by (rule unat_sort_impl_context)

  
abbreviation "string_assn \<equiv> string_assn' TYPE(size_t) TYPE(8)"  
  
global_interpretation str_sort: sort_impl_context "(\<le>)" "(<)" strcmp_impl string_assn
  defines str_sort_is_insert_impl = str_sort.is_insert_impl
      and str_sort_insertion_sort_impl = str_sort.insertion_sort_impl
      and str_sort_mop_lchild_impl  = str_sort.mop_lchild_impl 
      and str_sort_mop_rchild_impl  = str_sort.mop_rchild_impl 
      and str_sort_has_rchild_impl  = str_sort.has_rchild_impl 
      and str_sort_has_lchild_impl  = str_sort.has_lchild_impl 
      and str_sort_mop_geth_impl    = str_sort.mop_geth_impl  
      and str_sort_mop_seth_impl    = str_sort.mop_seth_impl  
      and str_sort_sift_down_impl   = str_sort.sift_down_impl
      and str_sort_heapify_btu_impl = str_sort.heapify_btu_impl
      and str_sort_heapsort_impl    = str_sort.heapsort_impl
      and str_sort_qsp_next_l_impl       = str_sort.qsp_next_l_impl
      and str_sort_qsp_next_h_impl       = str_sort.qsp_next_h_impl
      and str_sort_qs_partition_impl     = str_sort.qs_partition_impl
      and str_sort_partition_pivot_impl  = str_sort.partition_pivot_impl 
      and str_sort_introsort_qs_aux_impl = str_sort.introsort_qs_aux_impl
      and str_sort_introsort_impl        = str_sort.introsort_impl
      and str_sort_move_median_to_first_impl = str_sort.move_median_to_first_impl
  by (rule strcmp_sort_impl_context)
  
  
  
        
 (* TODO: Move! *)
lemmas [llvm_inline] = 
  array_swap_def word_log2_impl_def 

  
term arl_new_raw term arl_push_back 

(*abbreviation "str_empty \<equiv> arl_new_raw :: (8 word,size_t)array_list llM"
abbreviation "str_append \<equiv> arl_push_back :: (8 word,size_t)array_list \<Rightarrow> _"
*)

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
  
(*term unat_sort_qs_partitionXXX_impl  *)

term unat_sort_is_unguarded_insert_impl

  
export_llvm 
  "unat_sort_introsort_impl :: 64 word ptr \<Rightarrow> _" is "uint64_t* introsort(uint64_t*, int64_t, int64_t)" 
  "unat_sort_introsort_qs_aux_impl :: 64 word ptr \<Rightarrow> _" is "uint64_t* introsort_aux(uint64_t*, int64_t, int64_t, int64_t)" 
  "unat_sort_heapsort_impl :: 64 word ptr \<Rightarrow> _" is "uint64_t* heapsort(uint64_t*, int64_t, int64_t)" 
  "unat_sort_insertion_sort_impl :: 64 word ptr \<Rightarrow> _" is "uint64_t* insertion_sort(uint64_t*, int64_t, int64_t)" 

  "unat_sort_is_unguarded_insert_impl :: 64 word ptr \<Rightarrow> _" is "uint64_t* is_unguarded_insert(uint64_t*, int64_t, int64_t)" 
  
(*  "unat_sort_qs_partitionXXX_impl :: 64 word \<Rightarrow> 64 word \<Rightarrow> 64 word \<Rightarrow> 64 word ptr \<Rightarrow> (64 word ptr \<times> 64 word) llM" *)
  
  "str_init" is "void str_init(llstring *)"
  "str_append" is "void str_append(llstring *, char)"
  "llstrcmp" is "char llstrcmp(llstring*,llstring*)"
  "str_sort_introsort_impl" is "llstring* str_introsort(llstring*, int64_t, int64_t)" 
  
  defines \<open>typedef struct {int64_t size; struct {int64_t capacity; char *data;};} llstring;\<close>
  file "../code/introsort.ll"

(* XXX/TODO: We have a signed/unsigned problem for the strcmp export!
  we defined it on unsigned 8-bit words, while C++ seems to use signed char by default!
  THIS IS INCONSISTENT! 
*)  
  
  

end

xxx, ctd here: 
  Try unguarded-insertion optimization (sorry proofs just to try possible speedup!)





