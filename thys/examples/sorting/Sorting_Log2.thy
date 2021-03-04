theory Sorting_Log2
imports Sorting_Setup
begin


section \<open>Count Leading Zeroes and Log2\<close>
(* TODO: Define semantics of llvm.ctlz intrinsic! *)

subsection \<open>Explicit Implementation by Loop\<close>

definition word_clz' :: "'a::len word \<Rightarrow> nat" where
  "word_clz' x \<equiv> if x=0 then 0 else word_clz x"

lemma word_clz'_eq: "x\<noteq>0 \<Longrightarrow> word_clz' x = word_clz x" 
  by (simp add: word_clz'_def)  
  
lemma of_bl_eqZ: 
  "\<lbrakk> length xs = LENGTH ('a::len) \<rbrakk> \<Longrightarrow> (of_bl xs :: 'a word) = 0 \<longleftrightarrow> (xs = replicate LENGTH('a) False)"  
  apply auto
  by (metis to_bl_0 to_bl_use_of_bl word_bl_Rep')    

lemma word_clz'_rec: "word_clz' x = (if x <=s 0 then 0 else 1 + word_clz' (x << 1))"  
  (* TODO: Clean up this mess! *)  
  apply (clarsimp simp: word_clz'_def word_clz_def)
  apply (cases "to_bl x")
  apply auto
  apply (simp add: word_msb_alt word_sle_msb_le)
  apply (simp add: word_msb_alt word_sle_msb_le)
  apply (simp add: word_msb_alt word_sle_msb_le shiftl_bl)
  apply (subst (asm) of_bl_eqZ)
  apply (auto) [] 
  apply (metis length_Cons word_bl_Rep')
  apply (metis length_append_singleton length_replicate replicate_Suc replicate_append_same rotate1_rl' to_bl_0 word_bl.Rep_eqD)
  apply (simp add: word_msb_alt word_sle_msb_le)
  apply (simp add: bl_shiftl shiftl_bl)
  apply (subst (asm) of_bl_eqZ)
  apply auto
  apply (metis length_Cons word_bl_Rep')
  apply (subst word_bl.Abs_inverse)
  apply auto 
  apply (metis length_Cons word_bl_Rep')
  apply (subgoal_tac "True\<in>set list")
  apply simp
  by (simp add: eq_zero_set_bl)
  
lemma word_clz'_rec2: "word_clz' x = (if 0 <s x then 1 + word_clz' (x << 1) else 0)"  
  by (meson signed.not_le word_clz'_rec)

lemma word_clz'_simps2:
  "0 <s x \<Longrightarrow> word_clz' x = 1 + word_clz' (x << 1)"
  "\<not>(0 <s x) \<Longrightarrow> word_clz' x = 0"  
  using word_clz'_rec2 by metis+
  
definition word_clz2 :: "'a::len2 word \<Rightarrow> nat nres"
  where "word_clz2 x \<equiv> do {
    (c,_) \<leftarrow> WHILET (\<lambda>(c,x). 0 <s x) (\<lambda>(c,x). do {
      ASSERT (c + 1 < max_snat LENGTH('a));
      RETURN (c+1,x << 1)
    }) (0,x);
    RETURN c
  }"

lemma word_clz'_fits_snat: "word_clz' (x::'a::len2 word) < max_snat LENGTH('a)"
  unfolding word_clz'_def using word_clz_nonzero_max[of x]
  apply (auto simp: word_size max_snat_def) 
  by (meson le_def n_less_equal_power_2 nat_le_Suc_less_imp order_trans)
  
lemma word_clz2_refine: "word_clz2 x\<^sub>0 \<le> RETURN (word_clz' x\<^sub>0)"
  unfolding word_clz2_def
  supply [refine_vcg] = WHILET_rule[
    where I="\<lambda>(c,x). word_clz' x\<^sub>0 = c + word_clz' x"
      and R="measure (word_clz' o snd)"
  ]
  apply refine_vcg
  using word_clz'_fits_snat[of x\<^sub>0]
  apply (auto simp: word_clz'_simps2)
  done

lemma word_clz2_refine': "(word_clz2, RETURN o word_clz') \<in> Id \<rightarrow> \<langle>Id\<rangle>nres_rel"
  by (auto intro!: nres_relI simp: word_clz2_refine)
  
  
sepref_def word_clz'_impl is word_clz2 :: "(word_assn' TYPE('a::len2))\<^sup>k \<rightarrow>\<^sub>a snat_assn' TYPE('a)"  
  unfolding word_clz2_def
  apply (rewrite at "(_ + \<hole>,_)" snat_const_fold[where 'a='a])
  apply (rewrite at "(_ << \<hole>)" snat_const_fold[where 'a='a])
  apply (rewrite at "(\<hole>,_)" snat_const_fold[where 'a='a])
  by sepref

export_llvm "word_clz'_impl :: 64 word \<Rightarrow> 64 word llM" 

sepref_register word_clz word_clz'
lemmas [sepref_fr_rules] = word_clz'_impl.refine[FCOMP word_clz2_refine']

lemma word_clz_alt: "word_clz x = (if x=0 then size x else word_clz' x)"
  unfolding word_clz'_def by (auto simp: word_size)

  
    
sepref_def word_clz_impl 
  is "RETURN o word_clz" :: "[\<lambda>_. LENGTH('a)>2]\<^sub>a (word_assn' TYPE('a::len2))\<^sup>k \<rightarrow> snat_assn' TYPE('a)"  
  unfolding word_clz_alt
  by sepref
  
export_llvm "word_clz_impl :: 64 word \<Rightarrow> _"   

lemma word_clz_nonzero_max': "x\<noteq>0 \<Longrightarrow> word_clz (x::'a::len2 word) < LENGTH('a)"
  using word_clz_nonzero_max[of x] unfolding word_size
  by simp

sepref_def word_log2_impl is 
  "RETURN o word_log2" :: "[\<lambda>x. x>0 \<and> LENGTH('a)>2]\<^sub>a (word_assn' TYPE('a::len2))\<^sup>k \<rightarrow> snat_assn' TYPE('a)"
  unfolding word_log2_def word_size
  apply (annot_snat_const "TYPE('a)")
  supply [simp] = word_clz_nonzero_max'
  by sepref

export_llvm "word_log2_impl :: 64 word \<Rightarrow> _"

subsection \<open>Connection with \<^const>\<open>Discrete.log\<close>\<close>

lemma discrete_log_ltI: (* TODO: Check how precise this bound is! *)
  assumes "n\<noteq>0" "N\<noteq>0" "n<2^N"
  shows "Discrete.log n < N"
  using assms
  by (metis Discrete.log_le_iff leD linorder_neqE_nat log_exp log_exp2_le order_less_le zero_order(3))


lemma unat_x_div_2_conv:
  fixes x y :: "'a::len2 word"
  shows "unat x div 2 = unat y \<longleftrightarrow> y = x div 2"
proof -
  have A: "2 = unat (2::'a word)"
    by (metis le_less_trans len2_simps(2) n_less_equal_power_2 of_nat_numeral unat_of_nat_len)
  
  have B: "unat x div 2 = unat (x div 2)"
    unfolding A
    by (simp add: unat_div)

  show ?thesis  
    by (auto simp: B dest: word_unat.Rep_eqD)

qed    

lemma take_size_m1_to_bl:
  fixes x :: "'a::len word"
  shows "take (size x - Suc 0) (to_bl x) = butlast (to_bl x)"
  by (simp add: butlast_conv_take word_size_bl)
  
lemma takeWhile_butlast_eqI: "\<lbrakk>x\<in>set xs; \<not>P x\<rbrakk> \<Longrightarrow> takeWhile P (butlast xs) = takeWhile P xs"  
  by (metis append_Nil2 butlast.simps(2) butlast_append list.simps(3) split_list_last takeWhile_tail)

lemma takeWhile_butlast_eqI': "\<lbrakk>\<exists>x\<in>set xs. \<not>P x\<rbrakk> \<Longrightarrow> takeWhile P (butlast xs) = takeWhile P xs"  
  by (metis append_Nil2 butlast.simps(2) butlast_append list.simps(3) split_list_last takeWhile_tail)
  
  
lemma ex_True_in_set_conv: "(\<exists>x\<in>S. x) \<longleftrightarrow> True\<in>S" by auto  
  
lemma word_clz_rec: 
  fixes x :: "'a::len2 word" 
  shows "2\<le>x \<Longrightarrow> word_clz (x div 2) = word_clz x + 1"
  unfolding word_clz_def shiftr1_is_div_2[symmetric]
  apply (auto simp: bl_shiftr word_size)
  apply (subst bl_shiftr)
  apply (simp add: word_size Suc_leI)
  apply (auto simp: take_size_m1_to_bl)
  apply (subst takeWhile_butlast_eqI')
  apply (simp_all add: ex_True_in_set_conv)
  apply (rule ccontr)
  apply (simp only: eq_zero_set_bl[symmetric])
  by (metis le_unat_uoi len2_simps(2) n_less_equal_power_2 of_nat_numeral unat_0 unat_of_nat_len word_le_0_iff zero_neq_numeral)

lemma word_clz_ge2_max: "2\<le>(x::'a::len2 word) \<Longrightarrow> word_clz x + 1 < size x"  
  apply (simp only: word_clz_rec[symmetric] word_size)
  apply (rule word_clz_nonzero_max[of "x div 2", unfolded word_size])
  by (smt One_nat_def Suc_pred add.left_neutral add.right_neutral add_diff_cancel_left' add_diff_cancel_right' add_left_cancel diff_Suc_Suc div_less div_of_0_id div_self lessI less_eq_Suc_le less_one linorder_neqE_nat linorder_not_le mult.right_neutral not_numeral_le_zero numeral_2_eq_2 numeral_One numeral_le_one_iff order_less_le overflow_safe_hbound_check pos2 power.simps(1) power.simps(2) semiring_norm(69) unat_0 unat_div unat_eq_zero unat_gt_0 unat_x_div_2_conv word_clz_rec word_gt_0_no word_le_nat_alt zero_less_one zero_neq_one)
  
  
  
lemma word_log2_rec: 
  fixes x :: "'a::len2 word" shows "2\<le>x \<Longrightarrow> word_log2 x = Suc (word_log2 (x div 2))"
  apply (auto simp: word_log2_def word_size word_clz_rec)
  using word_clz_ge2_max[unfolded word_size, of x]
  by auto

lemma word_log2_is_discrete_log:
  fixes x :: "'a::len2 word"
  shows "word_log2 x = Discrete.log (unat x)"
  apply (cases "x=0")
  apply simp
  subgoal proof -
    assume "x \<noteq> 0"
    hence "unat x > 0" by (simp add: unat_gt_0)
    then show ?thesis
    proof (induction "unat x" arbitrary: x rule: log_induct)
      case one
      hence "x=1" using word_unat_Rep_inject1 by auto
      then show ?case 
        unfolding word_log2_def
        by (auto simp: word_size)  
      
    next
      case double
      
      from double.hyps(2) have "Discrete.log (unat x div 2) = word_log2 (x div 2)"
        by (metis unat_x_div_2_conv)
      
      then show ?case  
        apply (subst log_rec, simp add: \<open>2 \<le> unat x\<close>)
        apply simp
        apply (subst word_log2_rec)
        apply auto
        using double.hyps(1) le_unat_uoi word_le_nat_alt by fastforce
      
    qed
  qed
  done      

lemma word_log2_refine_unat: "(word_log2, Discrete.log) \<in> unat_rel' TYPE('a::len2) \<rightarrow> nat_rel"
  using word_log2_is_discrete_log
  by (fastforce simp: unat_rel_def unat.rel_def in_br_conv)
  
lemma word_log2_refine_snat: "(word_log2, Discrete.log) \<in> snat_rel' TYPE('a::len2) \<rightarrow> nat_rel"
  using word_log2_is_discrete_log
  by (fastforce simp: snat_rel_def snat.rel_def in_br_conv snat_eq_unat)

sepref_register Discrete.log

lemmas discrete_log_unat_hnr[sepref_fr_rules] = word_log2_impl.refine[FCOMP word_log2_refine_unat]
lemmas discrete_log_snat_hnr[sepref_fr_rules] = word_log2_impl.refine[FCOMP word_log2_refine_snat]

end
