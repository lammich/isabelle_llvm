theory Sorting_Quicksort_Partition
imports Sorting_Quicksort_Scheme
begin
  
hide_const (open) Transcendental.pi \<comment> \<open>\<open>pi\<close> is the implementation of \<open>p\<close>, not some constant related to a circle ;)\<close>

(* TODO: Move. Found useful for ATPs *)
lemma strict_itrans: "a < c \<Longrightarrow> a < b \<or> b < c" for a b c :: "_::linorder"
  by auto


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

sepref_def move_median_to_first_impl [llvm_inline] is "uncurry4 (PR_CONST move_median_to_first)" 
  :: "[\<lambda>_. True]\<^sub>c size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k *\<^sub>a (arr_assn)\<^sup>d 
    \<rightarrow> arr_assn [\<lambda>((((_,_),_),_),ai) r. r=ai]\<^sub>c"
  unfolding move_median_to_first_alt PR_CONST_def
  by sepref 
                    
end

context weak_ordering begin  
  
subsection \<open>Hoare Partitioning Scheme\<close>  


definition "ungrd_qsp_next_l_spec xs pi li hi \<equiv> 
  doN {
    ASSERT (pi<li \<and> pi<hi \<and> hi\<le>length xs);
    ASSERT (\<exists>i\<in>{li..<hi}. xs!i \<^bold>\<ge> xs!pi); 
    SPEC (\<lambda>li'. li\<le>li' \<and> li'<hi \<and> (\<forall>i\<in>{li..<li'}. xs!i\<^bold><xs!pi) \<and> xs!li'\<^bold>\<ge>xs!pi)
  }"

definition "ungrd_qsp_next_h_spec xs pi hi \<equiv> 
  doN {
    ASSERT (pi<length xs \<and> hi\<le>length xs \<and> (\<exists>i\<in>{pi<..<hi}. (xs!i) \<^bold>\<le> xs!pi)); 
    SPEC (\<lambda>hi'. hi'<hi \<and> (\<forall>i\<in>{hi'<..<hi}. xs!i\<^bold>>xs!pi) \<and> xs!hi'\<^bold>\<le>xs!pi)
  }"
  
  
definition qsp_next_l :: "'a list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat nres" where            
  "qsp_next_l xs pi li hi \<equiv> doN {
    monadic_WHILEIT (\<lambda>li'. (\<exists>i\<in>{li'..<hi}. xs!i\<^bold>\<ge>xs!pi) \<and> li\<le>li' \<and> (\<forall>i\<in>{li..<li'}. xs!i\<^bold><xs!pi)) 
      (\<lambda>li. doN {ASSERT (li\<noteq>pi); mop_cmp_idxs xs li pi}) (\<lambda>li. RETURN (li + 1)) li
  }"  

  
lemma qsp_next_l_refine: "(qsp_next_l,PR_CONST ungrd_qsp_next_l_spec)\<in>Id\<rightarrow>Id\<rightarrow>Id\<rightarrow>Id\<rightarrow>\<langle>Id\<rangle>nres_rel"
  unfolding qsp_next_l_def ungrd_qsp_next_l_spec_def PR_CONST_def
  apply (intro fun_relI; clarsimp)
  subgoal for xs p li hi
    apply (refine_vcg monadic_WHILEIT_rule[where R="measure (\<lambda>li. hi - li)"])
    apply simp_all
    subgoal by auto
    apply safe
    subgoal by (metis atLeastLessThan_iff leI le_less_Suc_eq wo_leD)
    subgoal by (metis atLeastLessThan_iff leI le_less_Suc_eq)
    subgoal using less_eq_Suc_le by force
    subgoal by auto
    subgoal by (auto simp: unfold_le_to_lt)
    done  
  done


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

definition "qs_partition li\<^sub>0 hi\<^sub>0 pi xs\<^sub>0 \<equiv> doN {
  ASSERT (pi < li\<^sub>0 \<and> li\<^sub>0<hi\<^sub>0 \<and> hi\<^sub>0\<le>length xs\<^sub>0);
  
  \<comment> \<open>Initialize\<close>
  li \<leftarrow> ungrd_qsp_next_l_spec xs\<^sub>0 pi li\<^sub>0 hi\<^sub>0;
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
      ASSERT(li<hi \<and> li<length xs \<and> hi<length xs \<and> li\<noteq>hi);
      xs \<leftarrow> mop_list_swap xs li hi;
      let li = li + 1;
      li \<leftarrow> ungrd_qsp_next_l_spec xs pi li hi\<^sub>0;
      hi \<leftarrow> ungrd_qsp_next_h_spec xs pi hi;
      RETURN (xs,li,hi)
    }) 
    (xs\<^sub>0,li,hi);
  
  RETURN (xs,li)
}"  

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
  subgoal
    by (metis le_trans order.strict_implies_order slice_eq_mset_eq_length swap_length) 
  subgoal apply (clarsimp simp: swap_def)
    by (metis (full_types) More_List.swap_def atLeastSucLessThan_greaterThanLessThan greaterThanLessThan_iff less_le_trans swap_nth2) 
  subgoal
    by (metis (mono_tags) greaterThanLessThan_iff leD le_less_trans less_le_trans nat_le_linear not_less_eq_eq slice_eq_mset_eq_length swap_indep swap_nth1) 
  subgoal 
    by (smt Suc_le_lessD dual_order.trans greaterThanLessThan_iff leI less_imp_le_nat swap_indep swap_length swap_nth1) 
  subgoal
    by (smt Suc_le_lessD atLeastLessThan_iff le_less_trans less_imp_le_nat slice_eq_mset_eq_length slice_eq_mset_swap(2)) 
    
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
    

definition "partition_pivot xs\<^sub>0 l h \<equiv> doN {
  ASSERT (l\<le>h \<and> h\<le>length xs\<^sub>0 \<and> h-l\<ge>4);
  let m = l + (h-l) div 2;
  xs\<^sub>1 \<leftarrow> move_median_to_first l (l+1) m (h-1) xs\<^sub>0;
  ASSERT (l<length xs\<^sub>1 \<and> length xs\<^sub>1 = length xs\<^sub>0);
  (xs,m) \<leftarrow> qs_partition (l+1) h l xs\<^sub>1;

  \<comment> \<open>TODO: Use an auxiliary lemma, instead of this assertion chain! \<close>
  ASSERT (l<m \<and> m<h);
  ASSERT ((\<forall>i\<in>{l+1..<m}. xs!i\<^bold>\<le>xs\<^sub>1!l) \<and> xs!l\<^bold>\<le>xs\<^sub>1!l);
  ASSERT (\<forall>i\<in>{l..<m}. xs!i\<^bold>\<le>xs\<^sub>1!l);
  ASSERT (\<forall>i\<in>{m..<h}. xs\<^sub>1!l\<^bold>\<le>xs!i);
  
  
  RETURN (xs,m)
}"

lemma slice_LT_I_aux:
  assumes B: "l<m" "m<h" "h\<le>length xs"
  assumes BND: "\<forall>i\<in>{l..<m}. xs!i\<^bold>\<le>p" "\<forall>i\<in>{m..<h}. p\<^bold>\<le>xs!i"
  shows "slice_LT (\<^bold>\<le>) (slice l m xs) (slice m h xs)"
  unfolding slice_LT_def
  using B apply (clarsimp simp: in_set_conv_nth slice_nth)
  subgoal for i j
    apply (rule trans[OF BND(1)[THEN bspec, of "l+i"] BND(2)[THEN bspec, of "m+j"]])
    by auto
  done
  
lemma partition_pivot_correct: "\<lbrakk>(xs,xs')\<in>Id; (l,l')\<in>Id; (h,h')\<in>Id\<rbrakk> 
  \<Longrightarrow> partition_pivot xs l h \<le> \<Down>Id (partition3_spec xs' l' h')"
  unfolding partition_pivot_def partition3_spec_def
  apply (refine_vcg move_median_to_first_correct'' qs_partition_correct)
  apply (all \<open>auto 0 3 dest: slice_eq_mset_eq_length; fail\<close>) [17]
  apply clarsimp
  subgoal for xs\<^sub>1 xs\<^sub>2 i m j
    apply (subst slice_eq_mset_nth_outside, assumption)
    apply (auto dest: slice_eq_mset_eq_length)
    done
  subgoal apply clarsimp by (metis (full_types) Suc_leI atLeastLessThan_iff le_neq_implies_less)
  subgoal by auto  
  subgoal 
    apply simp
    by (metis Suc_le_eq le_add2 le_refl order.strict_trans plus_1_eq_Suc slice_eq_mset_subslice slice_eq_mset_trans)
  apply (all \<open>auto; fail\<close>) [2]
  subgoal by (auto dest: slice_eq_mset_eq_length intro!: slice_LT_I_aux)
  done
  
end  
  
context sort_impl_context begin
  
sepref_register ungrd_qsp_next_l_spec ungrd_qsp_next_h_spec 

(* TODO: We can get rid of the length xs restriction: the stopper element will always lie within <h, which is size_t representable! *)
sepref_definition qsp_next_l_impl [llvm_inline] is "uncurry3 (qsp_next_l)" :: "(arr_assn)\<^sup>k *\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k \<rightarrow>\<^sub>a size_assn"
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
sepref_def qs_partition_impl (*[llvm_inline]*) is "uncurry3 (PR_CONST qs_partition)" 
  :: "[\<lambda>_. True]\<^sub>c size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k *\<^sub>a (arr_assn)\<^sup>d 
    \<rightarrow> arr_assn \<times>\<^sub>a size_assn [\<lambda>(((_,_),_),ai) (r,_). r=ai]\<^sub>c"
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
sepref_def partition_pivot_impl [llvm_inline] is "uncurry2 (PR_CONST partition_pivot)" 
  :: "[\<lambda>_. True]\<^sub>c arr_assn\<^sup>d *\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k \<rightarrow> arr_assn \<times>\<^sub>a size_assn [\<lambda>((ai,_),_) (r,_). r=ai]\<^sub>c"
  unfolding partition_pivot_def PR_CONST_def    
  apply (annot_snat_const "TYPE(size_t)")
  by sepref

  

end


subsection \<open>Parameterization\<close>

context parameterized_weak_ordering begin
  thm WO.qsp_next_l_def

  definition qsp_next_l_param :: "'cparam \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat nres" where            
    "qsp_next_l_param cparam xs pi li hi \<equiv> doN {
      monadic_WHILEIT (\<lambda>_. True) 
        (\<lambda>li. doN {ASSERT (li\<noteq>pi); pcmp_idxs2 cparam xs li pi}) 
        (\<lambda>li. doN {ASSERT (li<hi); RETURN (li + 1)}) li
    }"  
  
  lemma qsp_next_l_param_refine[refine]: "\<lbrakk>
    (xs',xs)\<in>cdom_list_rel cparam; (p',p)\<in>Id; (i',i)\<in>Id; (h',h)\<in>Id
  \<rbrakk> \<Longrightarrow> qsp_next_l_param cparam xs' p' i' h' \<le>\<Down>nat_rel (WO.ungrd_qsp_next_l_spec cparam xs p i h)"
  proof (goal_cases)
    case 1
    then have "qsp_next_l_param cparam xs' p' i' h' \<le>\<Down>nat_rel (WO.qsp_next_l cparam xs p i h)" 
      unfolding qsp_next_l_param_def WO.qsp_next_l_def
      apply refine_rcg
      by auto
    also note WO.qsp_next_l_refine[param_fo, OF IdI IdI IdI IdI, of cparam xs p i h, THEN nres_relD]
    finally show ?case unfolding PR_CONST_def .
  qed 
  
    
  definition qsp_next_h_param :: "'cparam \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat nres" where
    "qsp_next_h_param cparam xs pi hi \<equiv> doN {
      ASSERT (hi>0);
      let hi = hi - 1;
      ASSERT (hi<length xs);
      monadic_WHILEIT (\<lambda>_. True)
        (\<lambda>hi. doN {ASSERT(pi\<noteq>hi); pcmp_idxs2 cparam xs pi hi}) 
        (\<lambda>hi. doN { ASSERT(hi>0); RETURN (hi - 1)}) hi
    }"  

  lemma qsp_next_h_param_refine[refine]: "\<lbrakk>
    (xs',xs)\<in>cdom_list_rel cparam; (p',p)\<in>Id; (h',h)\<in>Id
  \<rbrakk> \<Longrightarrow> qsp_next_h_param cparam xs' p' h' \<le>\<Down>nat_rel (WO.ungrd_qsp_next_h_spec cparam xs p h)"      
  proof goal_cases
    case 1
    then have "qsp_next_h_param cparam xs' p' h' \<le>\<Down>nat_rel (WO.qsp_next_h cparam xs p h)"
      unfolding qsp_next_h_param_def WO.qsp_next_h_def
      apply refine_rcg
      by (auto simp: cdom_list_rel_alt in_br_conv)
    also note WO.qsp_next_h_refine[param_fo, THEN nres_relD]
    finally show ?thesis by simp 
  qed    
    
  definition "qs_partition_param cparam li\<^sub>0 hi\<^sub>0 pi xs\<^sub>0 \<equiv> doN {
    ASSERT (pi < li\<^sub>0 \<and> li\<^sub>0<hi\<^sub>0 \<and> hi\<^sub>0\<le>length xs\<^sub>0);
    
    \<comment> \<open>Initialize\<close>
    li \<leftarrow> qsp_next_l_param cparam xs\<^sub>0 pi li\<^sub>0 hi\<^sub>0;
    hi \<leftarrow> qsp_next_h_param cparam xs\<^sub>0 pi hi\<^sub>0;
    
    ASSERT (li\<^sub>0\<le>hi);
    
    (xs,li,hi) \<leftarrow> WHILEIT 
      (\<lambda>_. True)
      (\<lambda>(xs,li,hi). li<hi) 
      (\<lambda>(xs,li,hi). doN {
        ASSERT(li<hi \<and> li<length xs \<and> hi<length xs \<and> li\<noteq>hi);
        xs \<leftarrow> mop_list_swap xs li hi;
        let li = li + 1;
        li \<leftarrow> qsp_next_l_param cparam xs pi li hi\<^sub>0;
        hi \<leftarrow> qsp_next_h_param cparam xs pi hi;
        RETURN (xs,li,hi)
      }) 
      (xs\<^sub>0,li,hi);
    
    RETURN (xs,li)
  }"  

  lemma qs_partition_param_refine[refine]: "\<lbrakk>
    (li',li)\<in>Id; (hi',hi)\<in>Id; (pi',pi)\<in>Id; (xs',xs)\<in>cdom_list_rel cparam
  \<rbrakk> \<Longrightarrow> qs_partition_param cparam li' hi' pi' xs' 
    \<le> \<Down>(cdom_list_rel cparam \<times>\<^sub>r nat_rel) (WO.qs_partition cparam li hi pi xs)" 
    unfolding qs_partition_param_def WO.qs_partition_def
    supply [refine_dref_RELATES] = RELATESI[of "cdom_list_rel cparam"]
    apply refine_rcg
    apply refine_dref_type
    apply (auto simp: cdom_list_rel_alt in_br_conv)
    done

 definition "move_median_to_first_param cparam ri ai bi ci (xs::'a list) = doN {
    ASSERT (ai \<noteq> bi \<and> ai \<noteq> ci \<and> bi \<noteq> ci \<and> ri \<noteq> ai \<and> ri \<noteq> bi \<and> ri \<noteq> ci);
    if\<^sub>N pcmp_idxs2 cparam xs ai bi then (
      if\<^sub>N pcmp_idxs2 cparam xs bi ci then
        mop_list_swap xs ri bi
      else if\<^sub>N pcmp_idxs2 cparam xs ai ci then
        mop_list_swap xs ri ci
      else 
        mop_list_swap xs ri ai
    ) 
    else if\<^sub>N pcmp_idxs2 cparam xs ai ci then
      mop_list_swap xs ri ai
    else if\<^sub>N pcmp_idxs2 cparam xs bi ci then 
      mop_list_swap xs ri ci
    else 
      mop_list_swap xs ri bi
  }"

  
  (* TODO:Move *)
  lemma mop_list_swap_cdom_refine[refine]: "\<lbrakk>
    (xs',xs)\<in>cdom_list_rel cparam; (i',i)\<in>Id; (j',j)\<in>Id
  \<rbrakk> \<Longrightarrow> mop_list_swap xs' i' j' \<le> \<Down> (cdom_list_rel cparam) (mop_list_swap xs i j)"
    apply simp
    apply refine_rcg
    apply (clarsimp_all simp: cdom_list_rel_def list_rel_imp_same_length)
    apply (parametricity)
    by auto
  
  lemma move_median_to_first_param_refine[refine]: "\<lbrakk>
    (ri',ri)\<in>Id; (ai',ai)\<in>Id; (bi',bi)\<in>Id; (ci',ci)\<in>Id; (xs',xs)\<in>cdom_list_rel cparam 
  \<rbrakk> \<Longrightarrow> move_median_to_first_param cparam ri' ai' bi' ci' xs' 
    \<le> \<Down>(cdom_list_rel cparam) (WO.move_median_to_first cparam ri ai bi ci xs)"
    unfolding move_median_to_first_param_def WO.move_median_to_first_alt
    apply refine_rcg  
    by auto  
    
  definition "partition_pivot_param cparam xs\<^sub>0 l h \<equiv> doN {
    ASSERT (l\<le>h \<and> h\<le>length xs\<^sub>0 \<and> h-l\<ge>4);
    let m = l + (h-l) div 2;
    xs\<^sub>1 \<leftarrow> move_median_to_first_param cparam l (l+1) m (h-1) xs\<^sub>0;
    ASSERT (l<length xs\<^sub>1 \<and> length xs\<^sub>1 = length xs\<^sub>0);
    (xs,m) \<leftarrow> qs_partition_param cparam (l+1) h l xs\<^sub>1;
  
    RETURN (xs,m)
  }"

  lemma partition_pivot_param_refine[refine]: "\<lbrakk> (xs',xs)\<in>cdom_list_rel cparam; (l',l)\<in>Id; (h',h)\<in>Id
    \<rbrakk> \<Longrightarrow> partition_pivot_param cparam xs' l' h' 
        \<le> \<Down>(cdom_list_rel cparam \<times>\<^sub>r nat_rel) (WO.partition_pivot cparam xs l h)"
    unfolding partition_pivot_param_def WO.partition_pivot_def   
    apply refine_rcg
    apply (auto simp: cdom_list_rel_alt in_br_conv)
    done    
        
end


context parameterized_sort_impl_context begin

  (* TODO: Move *)
  abbreviation "arr_assn \<equiv> wo_assn"

  
sepref_register qsp_next_l_param qsp_next_h_param

(* TODO: We can get rid of the length xs restriction: the stopper element will always lie within <h, which is size_t representable! *)
sepref_def qsp_next_l_impl [llvm_inline] is "uncurry4 (PR_CONST qsp_next_l_param)" 
  :: "cparam_assn\<^sup>k *\<^sub>a (arr_assn)\<^sup>k *\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k \<rightarrow>\<^sub>a size_assn"
  unfolding qsp_next_l_param_def PR_CONST_def
  apply (annot_snat_const "TYPE(size_t)")
  by sepref
 
sepref_def qsp_next_h_impl [llvm_inline] is "uncurry3 (PR_CONST qsp_next_h_param)" :: "cparam_assn\<^sup>k *\<^sub>a (arr_assn)\<^sup>k *\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k \<rightarrow>\<^sub>a size_assn"
  unfolding qsp_next_h_param_def PR_CONST_def
  apply (annot_snat_const "TYPE(size_t)")
  by sepref
  
                        
sepref_register qs_partition_param  
sepref_def qs_partition_impl is "uncurry4 (PR_CONST qs_partition_param)" 
  :: "[\<lambda>_. True]\<^sub>c cparam_assn\<^sup>k *\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k *\<^sub>a (arr_assn)\<^sup>d 
    \<rightarrow> arr_assn \<times>\<^sub>a size_assn [\<lambda>((((_,_),_),_),ai) (r,_). r=ai]\<^sub>c"
  unfolding qs_partition_param_def PR_CONST_def
  apply (annot_snat_const "TYPE(size_t)")
  supply [dest] = slice_eq_mset_eq_length
  by sepref

sepref_register move_median_to_first_param

sepref_def move_median_to_first_param_impl (*[llvm_inline] *)
  is "uncurry5 (PR_CONST move_median_to_first_param)" 
  :: "[\<lambda>_. True]\<^sub>c cparam_assn\<^sup>k *\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k *\<^sub>a (arr_assn)\<^sup>d 
    \<rightarrow> arr_assn [\<lambda>(((((_,_),_),_),_),ai) r. r=ai]\<^sub>c"
  unfolding move_median_to_first_param_def PR_CONST_def
  by sepref  
  
  
sepref_register partition_pivot_param  
sepref_def partition_pivot_impl (*[llvm_inline] *)
  is "uncurry3 (PR_CONST partition_pivot_param)" 
  :: "[\<lambda>_. True]\<^sub>c cparam_assn\<^sup>k *\<^sub>a arr_assn\<^sup>d *\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k 
    \<rightarrow> arr_assn \<times>\<^sub>a size_assn [\<lambda>(((_,ai),_),_) (r,_). r=ai]\<^sub>c"
  unfolding partition_pivot_param_def PR_CONST_def    
  apply (annot_snat_const "TYPE(size_t)")
  by sepref
  

end

end                           

