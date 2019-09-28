theory Sorting_Misc
imports "../../sepref/IICF/IICF" "HOL-Library.Discrete"
begin
  hide_const (open) pi Word.slice

(* TODO: Move *)  
lemma WHILEIT_rule_amend_invar:
  assumes "wf R"
  assumes "I s" "I\<^sub>0 s"
  assumes "\<And>s. \<lbrakk>I s; I\<^sub>0 s; b s\<rbrakk> \<Longrightarrow> f s \<le> SPEC (\<lambda>s'. I s' \<and> I\<^sub>0 s' \<and> (s', s) \<in> R)"
  assumes "\<And>s. \<lbrakk>I s; I\<^sub>0 s; \<not> b s\<rbrakk> \<Longrightarrow> \<Phi> s"
  shows "WHILEIT I\<^sub>0 b f s \<le> SPEC \<Phi>"
  apply (rule order_trans)  
  apply (rule WHILEIT_weaken[where I="\<lambda>s. I s \<and> I\<^sub>0 s"])
  apply simp
  apply (rule WHILEIT_rule)
  apply fact
  using assms by auto
  


  
  
  
  
(* TODO: Move *) thm specify_left
lemma specify_left_pw: "\<lbrakk> nofail m; \<And>v. inres m v \<Longrightarrow> f v \<le> m' \<rbrakk> \<Longrightarrow> doN { v\<leftarrow>m; f v} \<le> m'"
  by (auto simp: pw_le_iff refine_pw_simps)


(* TODO: Move, replace Misc.slice_Len lemma *)
declare Misc.slice_len[simp del]
lemma slice_len[simp]: "\<lbrakk> to \<le> length xs \<rbrakk> \<Longrightarrow> length (Misc.slice from to xs) = to - from"
  unfolding Misc.slice_def
  by simp

lemma slice_empty_range[simp]: "h\<le>l \<Longrightarrow> Misc.slice l h xs = []"  
  unfolding Misc.slice_def
  by simp
  
lemma slice_upd: "\<lbrakk>l < h; h \<le> length xs; i < h - l\<rbrakk> \<Longrightarrow> (Misc.slice l h xs)[i:=x] = Misc.slice l h (xs[l + i := x])"
  unfolding Misc.slice_def
  by (simp add: drop_update_swap)
  
(* TODO: Move *)
lemma swap_nth1[simp]: "\<lbrakk>i<length xs \<rbrakk> \<Longrightarrow> swap xs i j ! i = xs!j"
  by (auto simp: swap_def nth_list_update')

(* TODO: Move *)
lemma swap_nth2[simp]: "\<lbrakk>j<length xs \<rbrakk> \<Longrightarrow> swap xs i j ! j = xs!i"
  by (auto simp: swap_def nth_list_update')

lemma swap_indep[simp]: "\<lbrakk>k\<noteq>i; k\<noteq>j\<rbrakk> \<Longrightarrow> swap xs i j ! k = xs!k"  
  by (auto simp: swap_def nth_list_update')

(* TODO: Move *)  
lemma slice_swap: "\<lbrakk>i\<in>{l..<h}; j\<in>{l..<h}; h\<le>length xs\<rbrakk> \<Longrightarrow> Misc.slice l h (swap xs i j) = swap (Misc.slice l h xs) (i-l) (j-l)"  
  unfolding Misc.slice_def swap_def
  by (auto simp: drop_update_swap)
  
lemma take_swap_outside[simp]: "l\<le>i \<Longrightarrow> l\<le>j \<Longrightarrow> take l (swap xs i j) = take l xs"  
  by (simp add: More_List.swap_def)

lemma drop_swap_outside[simp]: "i<h \<Longrightarrow> j<h \<Longrightarrow> drop h (swap xs i j) = drop h xs"  
  by (simp add: More_List.swap_def)

    
lemma slice_append:
  "\<lbrakk>l\<le>m; m\<le>h\<rbrakk> \<Longrightarrow> Misc.slice l m xs @ Misc.slice m h xs = Misc.slice l h xs"  
  apply (auto simp: Misc.slice_def)
  by (metis Nat.add_diff_assoc2 add_diff_cancel_left' drop_drop le_Suc_ex le_add_diff_inverse2 take_add)
  
    

(* TODO: Move *)  
lemma slice_extend1_left: "\<lbrakk>0<l; l\<le>h; h\<le>length xs\<rbrakk> \<Longrightarrow> slice (l-Suc 0) h xs = xs!(l-Suc 0) # slice l h xs"
  apply (rule nth_equalityI)
  by (auto simp: slice_nth nth_Cons split: nat.splits)
  
lemma slice_swap_outside:
  "\<lbrakk>i\<notin>{l..<h}; j\<notin>{l..<h}\<rbrakk> \<Longrightarrow> slice l h (swap xs i j) = slice l h xs"
  unfolding Misc.slice_def swap_def
  apply simp
  by (metis drop_take drop_upd_irrelevant leI take_update_cancel)
  

  
  
  
lemma set_slice_conv: "\<lbrakk> h\<le>length xs \<rbrakk> \<Longrightarrow> set (slice l h xs) = { xs!i | i. i\<in>{l..<h} }"  
  apply (safe;clarsimp simp: in_set_conv_nth)
  subgoal
    by (metis add.commute dual_order.strict_trans2 le_add2 less_diff_conv slice_nth)
  subgoal
    by (smt Misc.slice_def add_diff_inverse_nat diff_less_mono dual_order.trans leD less_imp_le_nat nth_drop nth_take)
  done
  
lemma slice_singleton[simp]: "l<length xs \<Longrightarrow> slice l (Suc l) xs = [xs!l]"  
  by (simp add: Misc.slice_def drop_Suc_nth)
  
  
lemma slice_split_hd: "\<lbrakk>l<h; h\<le>length xs\<rbrakk> \<Longrightarrow> slice l h xs = xs!l # slice (Suc l) h xs"  
  apply (auto simp: Misc.slice_def)
  by (metis Suc_diff_Suc drop_Suc_nth less_le_trans take_Suc_Cons)
  
  
    
      
definition "slice_eq_mset l h xs xs' \<equiv> length xs = length xs' \<and> take l xs = take l xs' \<and> mset (Misc.slice l h xs) = mset (Misc.slice l h xs') \<and> drop h xs = drop h xs'"    

lemma slice_eq_mset_refl[simp, intro!]: "slice_eq_mset l h xs xs" by (auto simp: slice_eq_mset_def)
lemma slice_eq_mset_sym[sym]: "slice_eq_mset l h xs xs' \<Longrightarrow> slice_eq_mset l h xs' xs"
  unfolding slice_eq_mset_def by auto
lemma slice_eq_mset_trans[trans]: "\<lbrakk> slice_eq_mset l h xs\<^sub>1 xs\<^sub>2; slice_eq_mset l h xs\<^sub>2 xs\<^sub>3 \<rbrakk> \<Longrightarrow> slice_eq_mset l h xs\<^sub>1 xs\<^sub>3"
  by (auto simp: slice_eq_mset_def)

    
lemma slice_eq_mset_swapI: "\<lbrakk>i\<in>{l..<h}; j\<in>{l..<h}; h\<le>length xs\<rbrakk> \<Longrightarrow> slice_eq_mset l h (swap xs i j) xs"  
  by (auto simp: slice_eq_mset_def slice_swap)

lemma slice_eq_mset_swap[simp]: 
  "\<lbrakk>i\<in>{l..<h}; j\<in>{l..<h}; h\<le>length ys \<rbrakk> \<Longrightarrow> slice_eq_mset l h (swap xs i j) ys \<longleftrightarrow> slice_eq_mset l h xs ys"  
  "\<lbrakk>i\<in>{l..<h}; j\<in>{l..<h}; h\<le>length xs \<rbrakk> \<Longrightarrow> slice_eq_mset l h (swap xs i j) ys \<longleftrightarrow> slice_eq_mset l h xs ys"  
  by (auto simp: slice_eq_mset_def slice_swap)
  
  
  
lemma slice_eq_mset_eq_length: "slice_eq_mset l h xs xs' \<Longrightarrow> length xs = length xs'"
  by (auto simp: slice_eq_mset_def)
  
lemma slice_eq_mset_eq_outside:
  assumes "slice_eq_mset l h xs xs'"  
  shows "h'\<le>l \<Longrightarrow> slice l' h' xs = slice l' h' xs'"
    and "h\<le>l' \<Longrightarrow> slice l' h' xs = slice l' h' xs'"
  using assms
  apply (clarsimp_all simp: slice_eq_mset_def Misc.slice_def)  
  apply (metis drop_take min.absorb1 take_take)
  by (metis drop_eq_mono)
  
lemma slice_eq_mset_nth_outside:  
  "\<lbrakk> slice_eq_mset l h xs xs'; i\<notin>{l..<h}; i<length xs\<rbrakk> \<Longrightarrow> xs!i = xs'!i"
  unfolding slice_eq_mset_def
  apply clarsimp
  by (smt drop_eq_mono hd_drop_conv_nth leI length_take list_update_id min_def nth_list_update_eq take_update)
  
lemma slice_eq_mset_set_inside: 
  "\<lbrakk> slice_eq_mset l h xs xs' \<rbrakk> \<Longrightarrow> set (slice l h xs) = set (slice l h xs')" 
  unfolding slice_eq_mset_def by (auto dest: mset_eq_setD)

lemma slice_eq_mset_subslice: "\<lbrakk> slice_eq_mset l' h' xs xs'; l\<le>l'; l'\<le>h'; h'\<le>h \<rbrakk> \<Longrightarrow> slice_eq_mset l h xs xs'"  
  apply (auto simp: slice_eq_mset_def)
  subgoal by (smt append_eq_append_conv le_Suc_ex length_take take_add)
  subgoal premises assms proof -
    from assms have [simp]:
      "Misc.slice l h xs = Misc.slice l l' xs @ Misc.slice l' h' xs @ Misc.slice h' h xs" 
      "Misc.slice l h xs' = Misc.slice l l' xs' @ Misc.slice l' h' xs' @ Misc.slice h' h xs'" 
      by (auto simp: slice_append)
      
    from assms have [simp]: "Misc.slice l l' xs = Misc.slice l l' xs'"  
      by (simp add: Misc.slice_def take_drop)

    from assms have [simp]: "Misc.slice h' h xs = Misc.slice h' h xs'"  
      by (simp add: Misc.slice_def take_drop)
            
    show ?thesis
      by (simp add: assms)
  qed
  subgoal using drop_eq_mono by blast
  done


(* TODO: Move *)

definition "slice_rel xs\<^sub>0 l h \<equiv> br (Misc.slice l h) (\<lambda>xs. l\<le>h \<and> h\<le>length xs \<and> length xs=length xs\<^sub>0 \<and> take l xs = take l xs\<^sub>0 \<and> drop h xs = drop h xs\<^sub>0)"
  
definition "idx_shift_rel s \<equiv> {(i,i'). i = i'+s}"

lemma slice_nth_refine: "\<lbrakk> (xs,xs')\<in>slice_rel xs\<^sub>0 l h; (i,i')\<in>idx_shift_rel l; i<h \<rbrakk> \<Longrightarrow> xs!i = xs'!i'"  
  by (auto simp: slice_rel_def in_br_conv slice_nth idx_shift_rel_def algebra_simps)

lemma slice_nth_refine': "\<lbrakk>(xs,xs')\<in>slice_rel xs\<^sub>0 l h; (i,i')\<in>idx_shift_rel l\<rbrakk>  
  \<Longrightarrow> mop_list_get xs i \<le>\<Down>Id (mop_list_get xs' i')"  
  apply (auto simp: pw_le_iff refine_pw_simps idx_shift_rel_def)
  by (auto simp: slice_rel_def in_br_conv slice_nth algebra_simps)
  
  
lemma slice_upd_refine: "\<lbrakk> (xs,xs')\<in>slice_rel xs\<^sub>0 l h; (i,i')\<in>idx_shift_rel l; i<h; (x,x')\<in>Id \<rbrakk> 
  \<Longrightarrow> (xs[i:=x], xs'[i':=x'])\<in>slice_rel xs\<^sub>0 l h"  
  by (auto simp: slice_rel_def in_br_conv slice_upd idx_shift_rel_def algebra_simps)

lemma slice_upd_refine': "\<lbrakk> (xs,xs')\<in>slice_rel xs\<^sub>0 l h; (i,i')\<in>idx_shift_rel l; (x,x')\<in>Id \<rbrakk> 
  \<Longrightarrow> mop_list_set xs i x \<le>\<Down>(slice_rel xs\<^sub>0 l h) (mop_list_set xs' i' x')"  
  apply (auto simp: pw_le_iff refine_pw_simps)
  by (auto simp: slice_rel_def in_br_conv slice_upd idx_shift_rel_def algebra_simps)
    
lemma slice_in_slice_rel[simp]: "\<lbrakk>l\<le>h; h\<le>length xs\<rbrakk> \<Longrightarrow> (xs, Misc.slice l h xs) \<in> slice_rel xs l h"  
  unfolding slice_rel_def in_br_conv by auto

(* TODO: Move *)
lemma unat_gtZ_prenorm[fcomp_prenorm_simps]: "(x,y)\<in>unat_rel \<Longrightarrow> 0<x \<longleftrightarrow> 0<y"
  by (simp add: in_br_conv unat.rel_def unat_gt_0 unat_rel_def word_neq_0_conv)

lemma snat_gtZ_prenorm[fcomp_prenorm_simps]: "(x,y)\<in>snat_rel \<Longrightarrow> 0<x \<longleftrightarrow> 0<y"
  by (simp add: in_br_conv snat.rel_def snat_eq_unat(2) unat_gt_0 snat_rel_def word_neq_0_conv)



(* TODO: Move *)
lemma word_log2_zero[simp]: "word_log2 0 = 0"
  unfolding word_log2_def word_size by auto

lemma word_clz_1[simp]: "word_clz (1::'a::len word) = LENGTH ('a) - 1"
  unfolding word_clz_def
  apply (simp add: to_bl_1)
  by (simp add: takeWhile_replicate takeWhile_tail)

  
  
(* CG-pre setup for LENGTH constants *)
lemmas [named_ss llvm_inline] = 
  len_of_numeral_defs of_nat_numeral
  
(* Sepref setup for LENGTH *)
  
sepref_register "LENGTH(_)"

context begin
  lemma size_fits_snat_aux: "x < 2^(x-Suc 0) \<longleftrightarrow> x=0 \<or> x>2"
    by (smt diff_Suc_1 gr0_implies_Suc le0 le_less_trans less_numeral_extra(4) less_one linorder_neqE_nat nat_neq_iff not_less_eq not_numeral_less_one numeral_2_eq_2 order_less_irrefl power_0 power_one_right suc_le_pow_2 zero_diff zero_less_one)
  
  lemma size_fits_snat_aux2: "LENGTH('a)>2 \<Longrightarrow> snat_invar (of_nat LENGTH('a) :: 'a::len2 word)"
    unfolding snat_invar_alt
    apply (rule exI[where x = "LENGTH('a) - 1"])
    by (auto simp: unat_of_nat size_fits_snat_aux)
    
end    

    
lemma LENGTH_refine[sepref_fr_rules]: 
  "LENGTH('a)>2 \<Longrightarrow> (uncurry0 (return (of_nat (LENGTH('a::len2))::'a word)), uncurry0 (RETURN (PR_CONST LENGTH('a)))) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a snat_assn"
  apply sepref_to_hoare
  unfolding snat_rel_def snat.rel_def 
  supply [simp] = in_br_conv word_size size_fits_snat_aux2
  apply vcg'
  apply (simp_all add: size_fits_snat_aux snat_eq_unat(1) unat_of_nat_eq)
  done

lemma size_refine[sepref_fr_rules]: "LENGTH('a)>2 \<Longrightarrow> (return o (\<lambda>_. of_nat (LENGTH('a))), RETURN o size) \<in> (word_assn' TYPE('a::len2))\<^sup>k \<rightarrow>\<^sub>a snat_assn' TYPE('a)"
  apply sepref_to_hoare
  unfolding snat_rel_def snat.rel_def 
  supply [simp] = in_br_conv word_size size_fits_snat_aux2
  apply vcg'
  by (simp add: size_fits_snat_aux snat_eq_unat(1) unat_of_nat_eq)
  

end
