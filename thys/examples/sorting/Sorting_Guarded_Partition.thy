theory Sorting_Guarded_Partition
imports Sorting_Quicksort_Scheme
begin
  
hide_const (open) Transcendental.pi \<comment> \<open>\<open>pi\<close> is the implementation of \<open>p\<close>, not some constant related to a circle ;)\<close>

(* TODO: Move. Found useful for ATPs *)
lemma strict_itrans: "a < c \<Longrightarrow> a < b \<or> b < c" for a b c :: "_::linorder"
  by auto

(* Guarded partitioning scheme, using sentinels. *)  
  
  

context weak_ordering begin  
  
subsection \<open>Hoare Partitioning Scheme\<close>  


definition "ungrd_qsg_next_l_spec si xs p li \<equiv> 
  doN {
    ASSERT (li \<le> si \<and> si<length xs \<and> xs!si \<^bold>\<ge> p);
    SPEC (\<lambda>li'. li\<le>li' \<and> li' \<le> si \<and> (\<forall>i\<in>{li..<li'}. xs!i\<^bold><p) \<and> xs!li'\<^bold>\<ge>p)
  }"

definition "ungrd_qsg_next_h_spec si xs p hi \<equiv> 
  doN {
    ASSERT (si < hi \<and> hi\<le>length xs \<and> xs!si \<^bold>\<le> p);
    SPEC (\<lambda>hi'. si\<le>hi' \<and> hi'<hi \<and> (\<forall>i\<in>{hi'<..<hi}. xs!i\<^bold>>p) \<and> xs!hi'\<^bold>\<le>p)
  }"
  
  
definition qsg_next_l :: "nat \<Rightarrow> 'a list \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> nat nres" where            
  "qsg_next_l si xs p li \<equiv> doN {
    monadic_WHILEIT (\<lambda>li'. li\<le>li' \<and> (\<forall>i\<in>{li..<li'}. xs!i\<^bold><p) \<and> li'\<le> si) 
      (\<lambda>li. doN { mop_cmp_idx_v xs li p}) (\<lambda>li. do { ASSERT (li < si); RETURN (li + 1) }) li
  }"  

  
lemma qsg_next_l_refine: "(qsg_next_l,PR_CONST ungrd_qsg_next_l_spec)\<in>Id\<rightarrow>Id\<rightarrow>Id\<rightarrow>Id\<rightarrow>\<langle>Id\<rangle>nres_rel"
  unfolding qsg_next_l_def ungrd_qsg_next_l_spec_def PR_CONST_def
  apply (intro fun_relI; clarsimp)
  subgoal for si xs p li
    apply (refine_vcg monadic_WHILEIT_rule[where R="measure (\<lambda>li. si - li)"] split_ifI)
    apply clarsimp_all
    subgoal by (metis le_eq_less_or_eq wo_leD)
    subgoal by (metis atLeastLessThan_iff less_Suc_eq)
    subgoal by (metis diff_less_mono2 lessI)
    subgoal using wo_not_le_imp_less by blast
    done
  done


definition qsg_next_h :: "nat \<Rightarrow> 'a list \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> nat nres" where
  "qsg_next_h si xs p hi \<equiv> doN {
    ASSERT (hi>0);
    let hi = hi - 1;
    monadic_WHILEIT (\<lambda>hi'. si\<le>hi' \<and> hi'\<le>hi \<and> (\<forall>i\<in>{hi'<..hi}. xs!i\<^bold>>p))
      (\<lambda>hi. doN { mop_cmp_v_idx xs p hi}) (\<lambda>hi. doN { ASSERT(hi>0); RETURN (hi - 1)}) hi
  }"  

  
lemma qsg_next_h_refine: "(qsg_next_h,PR_CONST (ungrd_qsg_next_h_spec)) \<in> Id \<rightarrow> Id \<rightarrow> Id \<rightarrow> Id \<rightarrow> \<langle>Id\<rangle>nres_rel"
  unfolding qsg_next_h_def ungrd_qsg_next_h_spec_def PR_CONST_def
  apply (refine_vcg monadic_WHILEIT_rule[where R="measure id"] split_ifI)
  apply (all \<open>(determ \<open>elim conjE exE\<close>)?\<close>)
  apply simp_all
  subgoal by (metis bot_nat_0.extremum_uniqueI gr0I wo_leD)
  subgoal by (metis One_nat_def le_step_down_nat wo_leD)
  subgoal by (metis Suc_le_eq Suc_pred greaterThanAtMost_iff less_Suc_eq less_Suc_eq_le)
  subgoal by (simp add: greaterThanAtMost_upt)
  subgoal using unfold_le_to_lt by presburger
  done
  

definition "ungrd_qsg_next_lh_spec si0 siN xs p li hi \<equiv> doN {
  li \<leftarrow> ungrd_qsg_next_l_spec siN xs p li;
  hi \<leftarrow> ungrd_qsg_next_h_spec si0 xs p hi;
  RETURN (li,hi)
}"  

(* Situation at start, and after swaps *)
definition "qsg_part_assn1 li\<^sub>0 hi\<^sub>0 p xs\<^sub>0 li hi xs \<equiv>
    0 < li\<^sub>0 \<and> li\<^sub>0\<le>hi\<^sub>0 \<and> hi\<^sub>0<length xs\<^sub>0 \<and> xs\<^sub>0!(li\<^sub>0-1) \<^bold>\<le> p \<and> p \<^bold>\<le> xs\<^sub>0!hi\<^sub>0
  \<and> slice_eq_mset li\<^sub>0 hi\<^sub>0 xs xs\<^sub>0
  \<and> li\<^sub>0\<le>li \<and> li\<le>hi \<and> hi\<le>hi\<^sub>0
  \<and> (\<forall>i\<in>{li\<^sub>0..<li}. xs!i \<^bold>\<le> p) 
  \<and> (\<forall>i\<in>{hi..<hi\<^sub>0}. p \<^bold>\<le> xs!i) 
"

definition "qsg_part_assn2 li\<^sub>0 hi\<^sub>0 p xs\<^sub>0 li hi xs \<equiv>
    0 < li\<^sub>0 \<and> li\<^sub>0\<le>hi\<^sub>0 \<and> hi\<^sub>0<length xs\<^sub>0 \<and> xs\<^sub>0!(li\<^sub>0-1) \<^bold>\<le> p \<and> p \<^bold>\<le> xs\<^sub>0!hi\<^sub>0
  \<and> slice_eq_mset li\<^sub>0 hi\<^sub>0 xs xs\<^sub>0
  \<and> li\<^sub>0\<le>li \<and> li\<le>hi+1 \<and> hi<hi\<^sub>0 \<and> li\<le>hi\<^sub>0
  \<and> (\<forall>i\<in>{li\<^sub>0..<li}. xs!i \<^bold>\<le> p) 
  \<and> (\<forall>i\<in>{hi<..<hi\<^sub>0}. p \<^bold>\<le> xs!i) 
  \<and> xs!li \<^bold>\<ge> p
  \<and> xs!hi \<^bold>\<le> p  
"

lemma qsg_part_12_aux:
  assumes SENTINELS: "xs ! (li\<^sub>0 - Suc 0) \<^bold>\<le> p" "p \<^bold>\<le> xs ! hi\<^sub>0"
  assumes LI_LE_HI: "li \<le> hi"
  assumes LI'_BOUND: "li \<le> li'" "li' \<le> hi\<^sub>0"
  assumes HI'_BOUND: "li\<^sub>0 - Suc 0 \<le> hi'" "hi' < hi" 
  assumes 
  UPTO_LI: "\<forall>i\<in>{li\<^sub>0..<li}. xs ! i \<^bold>\<le> p" and
  LI_TO_LI': "\<forall>i\<in>{li..<li'}. xs ! i \<^bold>< p" and
  DOWNTO_HI: "\<forall>i\<in>{hi..<hi\<^sub>0}. p \<^bold>\<le> xs ! i" and
  HI'_TO_HI: "\<forall>i\<in>{hi'<..<hi}. p \<^bold>< xs ! i"
  shows "li' \<le> Suc hi'" "(\<forall>i\<in>{li\<^sub>0..<li'}. xs ! i \<^bold>\<le> p)" "(\<forall>i\<in>{hi'<..<hi\<^sub>0}. p \<^bold>\<le> xs ! i)"
proof -

  show G1: "(\<forall>i\<in>{li\<^sub>0..<li'}. xs ! i \<^bold>\<le> p)" using UPTO_LI LI_TO_LI' by (auto simp: unfold_lt_to_le)
  
  show G2: "(\<forall>i\<in>{hi'<..<hi\<^sub>0}. p \<^bold>\<le> xs ! i)" using HI'_TO_HI DOWNTO_HI by (auto simp: unfold_lt_to_le)
  
  consider "li<li'" | "hi' < hi-1" | "li'=li" "hi'=hi-1"
    using \<open>hi' < hi\<close> \<open>li \<le> li'\<close> by linarith
  then show "li' \<le> Suc hi'" proof cases
    case 1
    hence "xs!(li'-1) \<^bold>< p" using LI_TO_LI' by simp
    moreover have "\<forall>i\<in>{hi'<..hi\<^sub>0}. p \<^bold>\<le> xs!i" using \<open>p \<^bold>\<le> xs ! hi\<^sub>0\<close>
      by (metis G2 greaterThanAtMost_iff greaterThanLessThan_iff le_eq_less_or_eq)
    ultimately show ?thesis
      using \<open>li' \<le> hi\<^sub>0\<close>
      apply clarsimp
      by (metis Suc_leD Suc_lessE \<open>xs ! (li' - 1) \<^bold>< p\<close> diff_Suc_1 greaterThanAtMost_iff le_def unfold_lt_to_le)
  next
    case 2
    hence "p \<^bold>< xs!(hi'+1)" using HI'_TO_HI by simp
    moreover have "(\<forall>i\<in>{li\<^sub>0-1..<li'}. xs ! i \<^bold>\<le> p)" using G1 \<open>xs ! (li\<^sub>0 - Suc 0) \<^bold>\<le> p\<close> 
      apply clarsimp
      by (metis atLeastLessThan_iff le_antisym le_refl nat_le_Suc_less_imp nat_less_le nat_neq_iff)
    ultimately show ?thesis
      using \<open>li\<^sub>0 - Suc 0 \<le> hi'\<close>
      apply clarsimp
      by (meson atLeastLessThan_iff le_SucI le_def unfold_lt_to_le)
  next
    case 3
    then show ?thesis using \<open>li\<le>hi\<close> by linarith
  qed
qed  

lemma qsg_part_12: "qsg_part_assn1 li\<^sub>0 hi\<^sub>0 p xs\<^sub>0 li hi xs 
  \<Longrightarrow> ungrd_qsg_next_lh_spec (li\<^sub>0-1) hi\<^sub>0 xs p li hi \<le> SPEC (\<lambda>(li',hi').
    qsg_part_assn2 li\<^sub>0 hi\<^sub>0 p xs\<^sub>0 li' hi' xs \<and> hi'<hi
     )"
  unfolding ungrd_qsg_next_lh_spec_def ungrd_qsg_next_l_spec_def ungrd_qsg_next_h_spec_def
  apply refine_vcg
  unfolding qsg_part_assn1_def
  apply (clarsimp_all simp: slice_eq_mset_eq_length)
  subgoal by (metis hd_drop_conv_nth slice_eq_mset_def)
  subgoal by linarith
  subgoal for i
    apply (subst slice_eq_mset_nth_outside, assumption)
    apply auto
    by (metis diff_diff_cancel less_imp_diff_less slice_eq_mset_eq_length)
  subgoal for hi' li'  
    unfolding qsg_part_assn2_def
    apply (clarsimp intro!: qsg_part_12_aux)
    apply (blast dest: qsg_part_12_aux)
    done
  done  

  
  
definition "qsg_partition_aux li\<^sub>0 hi\<^sub>0 p xs\<^sub>0 \<equiv> doN {
  \<comment> \<open>Initialize\<close>
  ASSERT (li\<^sub>0>0);
  (li,hi) \<leftarrow> ungrd_qsg_next_lh_spec (li\<^sub>0-1) hi\<^sub>0 xs\<^sub>0 p li\<^sub>0 hi\<^sub>0;
  
  (xs,li,hi) \<leftarrow> WHILEIT 
    (\<lambda>(xs,li,hi). qsg_part_assn2 li\<^sub>0 hi\<^sub>0 p xs\<^sub>0 li hi xs)
    (\<lambda>(xs,li,hi). li<hi) 
    (\<lambda>(xs,li,hi). doN {
      ASSERT(li<hi \<and> li<length xs \<and> hi<length xs \<and> li\<noteq>hi);
      xs \<leftarrow> mop_list_swap xs li hi;
      let li = li + 1;
      
      (li,hi) \<leftarrow> ungrd_qsg_next_lh_spec (li\<^sub>0-1) hi\<^sub>0 xs p li hi;
      RETURN (xs,li,hi)
    }) 
    (xs\<^sub>0,li,hi);
  
  RETURN (xs,li)
}"  


definition "gpartition_spec li hi p xs xs' m \<equiv> 
    slice_eq_mset li hi xs' xs 
  \<and> m\<in>{li..hi}
  \<and> (\<forall>i\<in>{li..<m}. xs'!i \<^bold>\<le> p)
  \<and> (\<forall>i\<in>{m..<hi}. p \<^bold>\<le> xs'!i)"


definition "gpartition_SPEC li hi p xs \<equiv> do {
  ASSERT (li\<le>hi \<and> hi\<le>length xs);
  SPEC (\<lambda>(xs',m). gpartition_spec li hi p xs xs' m)
}"

lemma qsg_part1_init: "\<lbrakk>0 < li; hi < length xs; xs ! (li - Suc 0) \<^bold>\<le> p; p \<^bold>\<le> xs ! hi; li \<le> hi\<rbrakk> \<Longrightarrow> qsg_part_assn1 li hi p xs li hi xs"
  unfolding qsg_part_assn1_def
  by simp

lemma qsg_part2_in_bounds: 
  assumes "qsg_part_assn2 li\<^sub>0 hi\<^sub>0 p xs\<^sub>0 li hi xs" 
  shows "li<length xs" "hi<length xs"
  using assms unfolding qsg_part_assn2_def
  by (auto dest: slice_eq_mset_eq_length)
  
  
lemma qsg_part_21: "\<lbrakk>qsg_part_assn2 li\<^sub>0 hi\<^sub>0 p xs\<^sub>0 li hi xs; li < hi\<rbrakk> \<Longrightarrow> qsg_part_assn1 li\<^sub>0 hi\<^sub>0 p xs\<^sub>0 (Suc li) hi (swap xs li hi)"
  unfolding qsg_part_assn2_def qsg_part_assn1_def
  apply (intro conjI)
  apply clarsimp_all
  subgoal by (metis atLeastLessThan_iff diff_diff_cancel less_Suc_eq_le less_imp_diff_less nat_less_le slice_eq_mset_eq_length swap_indep swap_nth1)
  subgoal by (metis Suc_diff_Suc diff_is_0_eq greaterThanLessThan_iff nat.simps(3) not_less_iff_gr_or_eq slice_eq_mset_eq_length strict_itrans swap_indep swap_nth2)
  done
  
lemma qsg_part_2fin: "\<lbrakk>qsg_part_assn2 li\<^sub>0 hi\<^sub>0 p xs\<^sub>0 li hi xs; \<not> li < hi\<rbrakk> \<Longrightarrow> gpartition_spec li\<^sub>0 hi\<^sub>0 p xs\<^sub>0 xs li"  
  unfolding qsg_part_assn2_def gpartition_spec_def
  apply clarsimp
  by (metis atLeastLessThan_iff atLeastSucLessThan_greaterThanLessThan le_antisym linorder_le_less_linear nat_Suc_less_le_imp)
  
lemma qsg_partition_aux_correct:
  "\<lbrakk>0<li; hi<length xs; xs!(li-1) \<^bold>\<le> p; p \<^bold>\<le> xs!hi\<rbrakk> \<Longrightarrow> qsg_partition_aux li hi p xs \<le> gpartition_SPEC li hi p xs"  
  unfolding qsg_partition_aux_def gpartition_SPEC_def
  apply (refine_vcg WHILEIT_rule[where R="measure (\<lambda>(_,_,hi). hi)"] qsg_part_12[where xs\<^sub>0=xs])  
  apply clarsimp_all
  subgoal by (simp add: qsg_part1_init)
  subgoal by (simp add: qsg_part2_in_bounds)
  subgoal by (simp add: qsg_part2_in_bounds)
  subgoal by (simp add: qsg_part_21)
  subgoal by (simp add: qsg_part_2fin)
  done    

definition "qsg_partition li\<^sub>0 hi\<^sub>0 p xs\<^sub>0 \<equiv> do {
  ASSERT (li\<^sub>0+1<hi\<^sub>0 \<and> hi\<^sub>0\<le>length xs\<^sub>0);

  (e0,xs) \<leftarrow> mop_idx_v_swap xs\<^sub>0 li\<^sub>0 (COPY p);
  let li=li\<^sub>0+1;
  
  let hi=hi\<^sub>0-1;
  (eN,xs) \<leftarrow> mop_idx_v_swap xs hi (COPY p);

  (xs,m) \<leftarrow> qsg_partition_aux li hi p xs;
  
  let li = li-1;

  let e0ok = e0 \<^bold>\<le> p;
  let eNok = p \<^bold>\<le> eN;
  (_,xs) \<leftarrow> mop_idx_v_swap xs li e0;
  (_,xs) \<leftarrow> mop_idx_v_swap xs hi eN;
  
  ASSERT (slice_eq_mset li (hi+1) xs xs\<^sub>0);
  
  if e0ok \<and> eNok then
    RETURN (xs,m)
  else if e0ok \<and> \<not>eNok then do {
    xs \<leftarrow> mop_list_swap xs m hi;
    ASSERT (m<hi\<^sub>0);
    let m=m+1;
    RETURN (xs,m)
  } else if eNok then do {
    ASSERT (1\<le>m);
    let m=m-1;
    xs \<leftarrow> mop_list_swap xs li m;
    RETURN (xs,m)
  } else do {
    xs \<leftarrow> mop_list_swap xs li hi;
    RETURN (xs,m)
  }
  
}"


term mop_cmp_idx_v

definition "qsg_partition_wrapper li hi p xs \<equiv> do {
  if li<hi then (
    if li+1<hi then qsg_partition li hi p xs
    else doN {
      if\<^sub>N mop_cmp_idx_v xs li p then RETURN (xs,hi)
      else RETURN (xs,li)
    }
  ) else RETURN (xs,li)
}"


(* TODO: Move *)
lemma slice_update_outside[simp]: "i\<notin>{l..<h} \<Longrightarrow> slice l h (xs[i:=x]) = slice l h xs"
  unfolding Misc.slice_def
  apply auto
  by (metis drop_take leI take_update_cancel)

lemma slice_eq_mset_upd_outside: "slice_eq_mset l h xs xs' \<Longrightarrow> i\<notin>{l..<h} \<Longrightarrow> i<length xs' \<Longrightarrow> slice_eq_mset l h (xs[i:=x]) (xs'[i:=x])"
  unfolding slice_eq_mset_def
  apply (auto simp: drop_update_swap not_le)
  by (metis drop_update_cancel drop_update_swap leI)


lemma qsg_partition_correct: "li+1<hi \<Longrightarrow> qsg_partition li hi p xs \<le> gpartition_SPEC li hi p xs"
  unfolding qsg_partition_def gpartition_SPEC_def
  apply (refine_vcg qsg_partition_aux_correct[THEN order_trans])
  apply simp_all
  apply clarsimp_all
  apply simp_all
  unfolding gpartition_SPEC_def
  apply refine_vcg
  apply clarsimp_all
  apply simp_all
  unfolding gpartition_spec_def
  apply clarsimp_all
  apply (simp_all add: slice_eq_mset_eq_length)
  subgoal for xs' m
    apply (drule slice_eq_mset_upd_outside[where i="li" and x="xs ! li"]; simp?)
    apply (drule slice_eq_mset_upd_outside[where i="hi - Suc 0" and x="xs ! (hi - Suc 0)"]; simp?)
    apply (simp add: list_update_swap)
    apply (erule slice_eq_mset_subslice)
    apply auto
    done
  subgoal for xs' m
    apply (intro conjI)
    subgoal by simp
    subgoal by (auto simp: nth_list_update' slice_eq_mset_eq_length)
    subgoal by (clarsimp simp: nth_list_update' slice_eq_mset_eq_length)
    done
  subgoal for xs' m
    apply (intro conjI)
    subgoal
      apply (simp (no_asm_simp) add: slice_eq_mset_eq_length swap_nth nth_list_update) 
      using connex
      by blast
    subgoal by (fastforce simp: slice_eq_mset_eq_length swap_nth nth_list_update)
    done
  subgoal for xs' m
    apply (intro conjI)
    subgoal by (metis Suc_le_D Suc_to_right atLeastLessThan_iff le_Suc_eq le_eq_less_or_eq nz_le_conv_less slice_eq_mset_swap(1) zero_less_Suc)
    subgoal by simp 
    subgoal by simp 
    subgoal by (fastforce simp add: slice_eq_mset_eq_length swap_nth nth_list_update) 
    subgoal
      apply (simp (no_asm_simp) add: slice_eq_mset_eq_length swap_nth nth_list_update)
      apply safe
      subgoal using connex apply blast done
      subgoal by (metis atLeastLessThan_iff le_def le_eq_less_or_eq nat_le_Suc_less_imp)
      subgoal using connex by blast
      subgoal using connex by blast
      subgoal by (metis Suc_le_D Suc_le_lessD Suc_to_right atLeastLessThan_iff nat_in_between_eq(2))
      by (meson atLeastLessThan_iff le_antisym linorder_not_le nat_le_Suc_less_imp)
    done  
  subgoal for xs' m
    apply (intro conjI)
    subgoal by simp 
    subgoal
      apply (simp (no_asm_simp) add: slice_eq_mset_eq_length swap_nth nth_list_update) 
      using connex
      by blast
    subgoal
      apply (simp (no_asm_simp) add: slice_eq_mset_eq_length swap_nth nth_list_update)
      by (meson atLeastLessThan_iff connex diff_is_0_eq' diffs0_imp_equal le_def nat_le_Suc_less_imp)
    done
  done

  
  sepref_register gpartition_SPEC
  
  lemma qsg_partition_wrapper_refine: "(qsg_partition_wrapper, PR_CONST gpartition_SPEC) \<in> Id \<rightarrow> Id \<rightarrow> Id \<rightarrow> Id \<rightarrow> \<langle>Id\<rangle>nres_rel"
    unfolding qsg_partition_wrapper_def
    apply (clarsimp split!: if_split intro!: nres_relI)
    subgoal by (simp add: qsg_partition_correct)
    unfolding gpartition_SPEC_def
    apply (all refine_vcg)
    apply simp_all
    unfolding gpartition_spec_def
    apply auto
    subgoal by (metis connex le_less_Suc_eq strict_itrans wo_leD)
    subgoal by (metis le_less_Suc_eq strict_itrans wo_leI)
    done
  
  
end  
  

(* TODO: Move to Sorting-Setup *)

find_theorems GEN_ALGO


  
term "GEN_ALGO"

term mop_list_copy


context sort_impl_context begin

  
sepref_register ungrd_qsg_next_l_spec ungrd_qsg_next_h_spec 

(* TODO: We can get rid of the length xs restriction: the stopper element will always lie within <h, which is size_t representable! *)
sepref_definition qsg_next_l_impl [llvm_inline] is "uncurry3 (qsg_next_l)" :: "size_assn\<^sup>k *\<^sub>a (arr_assn)\<^sup>k *\<^sub>a elem_assn\<^sup>k *\<^sub>a size_assn\<^sup>k \<rightarrow>\<^sub>a size_assn"
  unfolding qsg_next_l_def PR_CONST_def
  apply (annot_snat_const "TYPE(size_t)")
  by sepref

lemmas [sepref_fr_rules] = qsg_next_l_impl.refine[FCOMP qsg_next_l_refine]  
  
term qsg_next_h

sepref_definition qsg_next_h_impl [llvm_inline] is "uncurry3 (qsg_next_h)" :: "size_assn\<^sup>k *\<^sub>a (arr_assn)\<^sup>k *\<^sub>a elem_assn\<^sup>k *\<^sub>a size_assn\<^sup>k \<rightarrow>\<^sub>a size_assn"
  unfolding qsg_next_h_def PR_CONST_def
  apply (annot_snat_const "TYPE(size_t)")
  by sepref
  
lemmas [sepref_fr_rules] = qsg_next_h_impl.refine[FCOMP qsg_next_h_refine]  
  

sepref_register qsg_partition_aux  
sepref_def qsg_partition_aux_impl (*[llvm_inline]*) is "uncurry3 (PR_CONST qsg_partition_aux)" 
  :: "[\<lambda>_. True]\<^sub>c size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k *\<^sub>a elem_assn\<^sup>k *\<^sub>a (arr_assn)\<^sup>d 
    \<rightarrow> arr_assn \<times>\<^sub>a size_assn [\<lambda>(((_,_),_),ai) (r,_). r=ai]\<^sub>c"
  unfolding qsg_partition_aux_def PR_CONST_def ungrd_qsg_next_lh_spec_def
  apply (simp only: nres_monad_laws split)
  apply (annot_snat_const "TYPE(size_t)")
  by sepref

(* TODO: Move *)                  
lemma unfold_let_le: "(let x = a\<^bold>\<le>b in f x) = (let x = \<not> b\<^bold><a in f x)"  
  by (simp add: unfold_le_to_lt)
        
(* TODO: Move *)                  
  
definition "list_guarded_swap xs i j \<equiv> if i\<noteq>j then mop_list_swap xs i j else RETURN xs "  
  
lemma list_guarded_swap_refine[refine]: 
  "\<lbrakk> (xs,xs')\<in>\<langle>Id\<rangle>list_rel; (i,i')\<in>Id; (j,j')\<in>Id \<rbrakk> \<Longrightarrow> list_guarded_swap xs i j \<le>\<Down>Id (mop_list_swap xs' i' j')"
  unfolding list_guarded_swap_def
  apply simp
  apply refine_vcg
  by simp

sepref_register list_guarded_swap  
  
sepref_def list_guarded_swap_impl [llvm_inline] is "uncurry2 list_guarded_swap" 
  :: "[\<lambda>_. True]\<^sub>c arr_assn\<^sup>d *\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k \<rightarrow> arr_assn [\<lambda>((p,_),_) r. r=p]\<^sub>c"
  unfolding list_guarded_swap_def
  by sepref

end

context sort_impl_copy_context begin
  
(* Some refinement to tame exploding sepref *)  
definition "qsg_partition_swap_back hi\<^sub>0 li hi m xs e0ok eNok \<equiv> do {
  if e0ok \<and> eNok then
    RETURN (xs,m)
  else if e0ok \<and> \<not>eNok then do {
    xs \<leftarrow> list_guarded_swap xs m hi;
    ASSERT (m<hi\<^sub>0);
    let m=m+1;
    RETURN (xs,m)
  } else if eNok then do {
    ASSERT (1\<le>m);
    let m=m-1;
    xs \<leftarrow> list_guarded_swap xs li m;
    RETURN (xs,m)
  } else do {
    xs \<leftarrow> list_guarded_swap xs li hi;
    RETURN (xs,m)
  }

}"
  
definition "qsg_partition2 li hi\<^sub>0 p xs\<^sub>0 \<equiv> do {
  (e0,xs) \<leftarrow> mop_idx_v_swap xs\<^sub>0 li (COPY p);
  ASSERT (li<hi\<^sub>0);
  let li=li+1;
  
  ASSERT (hi\<^sub>0>0);
  let hi=hi\<^sub>0-1;
  (eN,xs) \<leftarrow> mop_idx_v_swap xs hi (COPY p);

  (xs,m) \<leftarrow> qsg_partition_aux li hi p xs;
  
  ASSERT (li>0);
  let li = li-1;

  let e0ok = e0 \<^bold>\<le> p;
  let eNok = p \<^bold>\<le> eN;
  (_,xs) \<leftarrow> mop_idx_v_swap xs li e0;
  (_,xs) \<leftarrow> mop_idx_v_swap xs hi eN;

  qsg_partition_swap_back hi\<^sub>0 li hi m xs e0ok eNok
}"

lemma qsg_partition2_refine: "(PR_CONST  qsg_partition2, PR_CONST qsg_partition) \<in> Id \<rightarrow> Id \<rightarrow> Id \<rightarrow> Id \<rightarrow> \<langle>Id\<rangle>nres_rel"
  unfolding qsg_partition2_def qsg_partition_def qsg_partition_swap_back_def PR_CONST_def
  apply refine_rcg
  apply refine_dref_type
  apply simp_all
  done

sepref_register qsg_partition_swap_back

sepref_def qsg_partition_swap_back_impl is "uncurry6 (qsg_partition_swap_back)" 
  :: "[\<lambda>_. True]\<^sub>c size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k *\<^sub>a (arr_assn)\<^sup>d *\<^sub>a bool1_assn\<^sup>k *\<^sub>a bool1_assn\<^sup>k
    \<rightarrow> arr_assn \<times>\<^sub>a size_assn [\<lambda>((((((_,_),_),_),ai),_),_) (r,_). r=ai]\<^sub>c"
  unfolding qsg_partition_swap_back_def PR_CONST_def
  apply (annot_snat_const "TYPE(size_t)")
  by sepref_dbg_keep
  
  

sepref_register qsg_partition

sepref_definition qsg_partition_impl [llvm_code] (*[llvm_inline]*) is "uncurry3 (PR_CONST qsg_partition2)" 
  :: "[\<lambda>_. True]\<^sub>c size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k *\<^sub>a elem_assn\<^sup>k *\<^sub>a (arr_assn)\<^sup>d 
    \<rightarrow> arr_assn \<times>\<^sub>a size_assn [\<lambda>(((_,_),_),ai) (r,_). r=ai]\<^sub>c"
  unfolding qsg_partition2_def PR_CONST_def unfold_let_le
  supply [[goals_limit = 1]]
  apply (annot_snat_const "TYPE(size_t)")
  apply sepref_dbg_keep
  done

lemmas qsg_partition_impl'_hnr[sepref_fr_rules] = qsg_partition_impl.refine[FCOMP qsg_partition2_refine]


sepref_register qsg_partition_wrapper
sepref_definition qsg_partition_wrapper_impl [llvm_code] is "uncurry3 (qsg_partition_wrapper)"
  :: "[\<lambda>_. True]\<^sub>c size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k *\<^sub>a elem_assn\<^sup>k *\<^sub>a (arr_assn)\<^sup>d 
    \<rightarrow> arr_assn \<times>\<^sub>a size_assn [\<lambda>(((_,_),_),ai) (r,_). r=ai]\<^sub>c"
  unfolding qsg_partition_wrapper_def PR_CONST_def
  apply (annot_snat_const "TYPE(size_t)")
  by sepref


lemmas qsg_partition_wrapper_impl'_hnr[sepref_fr_rules] = qsg_partition_wrapper_impl.refine[FCOMP qsg_partition_wrapper_refine]  
  

end

(*
  skip for now, as we won't yet be able to distribute the comparator data over many threads!

subsection \<open>Parameterization\<close>

context parameterized_weak_ordering begin
  thm WO.qsg_next_l_def

  definition qsg_next_l_param :: "'cparam \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat nres" where            
    "qsg_next_l_param cparam xs pi li hi \<equiv> doN {
      monadic_WHILEIT (\<lambda>_. True) 
        (\<lambda>li. doN {ASSERT (li\<noteq>pi); pcmp_idxs2 cparam xs li pi}) 
        (\<lambda>li. doN {ASSERT (li<hi); RETURN (li + 1)}) li
    }"  
  
  lemma qsg_next_l_param_refine[refine]: "\<lbrakk>
    (xs',xs)\<in>cdom_list_rel cparam; (p',p)\<in>Id; (i',i)\<in>Id; (h',h)\<in>Id
  \<rbrakk> \<Longrightarrow> qsg_next_l_param cparam xs' p' i' h' \<le>\<Down>nat_rel (WO.ungrd_qsg_next_l_spec cparam xs p i h)"
  proof (goal_cases)
    case 1
    then have "qsg_next_l_param cparam xs' p' i' h' \<le>\<Down>nat_rel (WO.qsg_next_l cparam xs p i h)" 
      unfolding qsg_next_l_param_def WO.qsg_next_l_def
      apply refine_rcg
      by auto
    also note WO.qsg_next_l_refine[param_fo, OF IdI IdI IdI IdI, of cparam xs p i h, THEN nres_relD]
    finally show ?case unfolding PR_CONST_def .
  qed 
  
    
  definition qsg_next_h_param :: "'cparam \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat nres" where
    "qsg_next_h_param cparam xs pi hi \<equiv> doN {
      ASSERT (hi>0);
      let hi = hi - 1;
      ASSERT (hi<length xs);
      monadic_WHILEIT (\<lambda>_. True)
        (\<lambda>hi. doN {ASSERT(pi\<noteq>hi); pcmp_idxs2 cparam xs pi hi}) 
        (\<lambda>hi. doN { ASSERT(hi>0); RETURN (hi - 1)}) hi
    }"  

  lemma qsg_next_h_param_refine[refine]: "\<lbrakk>
    (xs',xs)\<in>cdom_list_rel cparam; (p',p)\<in>Id; (h',h)\<in>Id
  \<rbrakk> \<Longrightarrow> qsg_next_h_param cparam xs' p' h' \<le>\<Down>nat_rel (WO.ungrd_qsg_next_h_spec cparam xs p h)"      
  proof goal_cases
    case 1
    then have "qsg_next_h_param cparam xs' p' h' \<le>\<Down>nat_rel (WO.qsg_next_h cparam xs p h)"
      unfolding qsg_next_h_param_def WO.qsg_next_h_def
      apply refine_rcg
      by (auto simp: cdom_list_rel_alt in_br_conv)
    also note WO.qsg_next_h_refine[param_fo, THEN nres_relD]
    finally show ?thesis by simp 
  qed    
    
  definition "qsg_partition_param cparam li\<^sub>0 hi\<^sub>0 pi xs\<^sub>0 \<equiv> doN {
    ASSERT (pi < li\<^sub>0 \<and> li\<^sub>0<hi\<^sub>0 \<and> hi\<^sub>0\<le>length xs\<^sub>0);
    
    \<comment> \<open>Initialize\<close>
    li \<leftarrow> qsg_next_l_param cparam xs\<^sub>0 pi li\<^sub>0 hi\<^sub>0;
    hi \<leftarrow> qsg_next_h_param cparam xs\<^sub>0 pi hi\<^sub>0;
    
    ASSERT (li\<^sub>0\<le>hi);
    
    (xs,li,hi) \<leftarrow> WHILEIT 
      (\<lambda>_. True)
      (\<lambda>(xs,li,hi). li<hi) 
      (\<lambda>(xs,li,hi). doN {
        ASSERT(li<hi \<and> li<length xs \<and> hi<length xs \<and> li\<noteq>hi);
        xs \<leftarrow> mop_list_swap xs li hi;
        let li = li + 1;
        li \<leftarrow> qsg_next_l_param cparam xs pi li hi\<^sub>0;
        hi \<leftarrow> qsg_next_h_param cparam xs pi hi;
        RETURN (xs,li,hi)
      }) 
      (xs\<^sub>0,li,hi);
    
    RETURN (xs,li)
  }"  

  lemma qsg_partition_param_refine[refine]: "\<lbrakk>
    (li',li)\<in>Id; (hi',hi)\<in>Id; (pi',pi)\<in>Id; (xs',xs)\<in>cdom_list_rel cparam
  \<rbrakk> \<Longrightarrow> qsg_partition_param cparam li' hi' pi' xs' 
    \<le> \<Down>(cdom_list_rel cparam \<times>\<^sub>r nat_rel) (WO.qsg_partition cparam li hi pi xs)" 
    unfolding qsg_partition_param_def WO.qsg_partition_def
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
    (xs,m) \<leftarrow> qsg_partition_param cparam (l+1) h l xs\<^sub>1;
  
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

  
sepref_register qsg_next_l_param qsg_next_h_param

(* TODO: We can get rid of the length xs restriction: the stopper element will always lie within <h, which is size_t representable! *)
sepref_def qsg_next_l_impl [llvm_inline] is "uncurry4 (PR_CONST qsg_next_l_param)" 
  :: "cparam_assn\<^sup>k *\<^sub>a (arr_assn)\<^sup>k *\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k \<rightarrow>\<^sub>a size_assn"
  unfolding qsg_next_l_param_def PR_CONST_def
  apply (annot_snat_const "TYPE(size_t)")
  by sepref
 
sepref_def qsg_next_h_impl [llvm_inline] is "uncurry3 (PR_CONST qsg_next_h_param)" :: "cparam_assn\<^sup>k *\<^sub>a (arr_assn)\<^sup>k *\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k \<rightarrow>\<^sub>a size_assn"
  unfolding qsg_next_h_param_def PR_CONST_def
  apply (annot_snat_const "TYPE(size_t)")
  by sepref
  
                        
sepref_register qsg_partition_param  
sepref_def qsg_partition_impl is "uncurry4 (PR_CONST qsg_partition_param)" 
  :: "[\<lambda>_. True]\<^sub>c cparam_assn\<^sup>k *\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k *\<^sub>a (arr_assn)\<^sup>d 
    \<rightarrow> arr_assn \<times>\<^sub>a size_assn [\<lambda>((((_,_),_),_),ai) (r,_). r=ai]\<^sub>c"
  unfolding qsg_partition_param_def PR_CONST_def
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

*)

end                           

