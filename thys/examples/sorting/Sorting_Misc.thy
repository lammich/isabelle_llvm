theory Sorting_Misc
imports "../../sepref/IICF/IICF" "HOL-Library.Discrete"
begin
  hide_const (open) pi Word.slice


lemma WHILEIT_unfold': "WHILEIT I b c s = doN { ASSERT (I s); if b s then doN { s\<leftarrow>c s; WHILEIT I b c s } else RETURN s }"
  apply (rewrite in "\<hole>=_" WHILEIT_unfold)
  by (auto)

  
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
  

(* TODO: Move *)
abbreviation monadic_If :: "bool nres \<Rightarrow> 'a nres \<Rightarrow> 'a nres \<Rightarrow> 'a nres" ("(if\<^sub>N (_)/ then (_)/ else (_))" [0, 0, 10] 10)
  where "monadic_If b x y \<equiv> doN { t \<leftarrow> b; if t then x else y }"
  
(* TODO: Move *)
lemma monadic_WHILEIT_rule:
  assumes "wf R"
  assumes "I s"
  assumes STEP: "\<And>s. I s \<Longrightarrow> b s \<le> SPEC (\<lambda>r. if r then c s \<le> SPEC (\<lambda>s'. I s' \<and> (s',s)\<in>R) else \<Phi> s)"
  shows "monadic_WHILEIT I b c s \<le> SPEC \<Phi>"
  using \<open>wf R\<close> \<open>I s\<close> apply (induction s rule: wf_induct_rule)
  apply (subst monadic_WHILEIT_unfold)
  apply (refine_vcg)
  apply (rule STEP[THEN order_trans], assumption)
  apply (refine_vcg)
  subgoal
    apply (split if_splits; simp)
    apply (rule order_trans, assumption)
    apply (refine_vcg)
    apply blast
    done
  subgoal
    by auto  
  done

(* Required as VCG-rule when using monadic_WHILEIT_rule *)    
lemma split_ifI: "\<lbrakk> b\<Longrightarrow>P; \<not>b\<Longrightarrow>Q \<rbrakk> \<Longrightarrow> If b P Q" by simp 
  

  (* TODO: Move *)  
  lemma flatf_fixp_dep_transfer:
    \<comment> \<open>Transfer rule for fixed points\<close>
    assumes TR_BOT[simp]: "\<And>x x' arb m. tr arb x x' b m"
    assumes MONO: "flatf_mono b B"
    assumes FP': "fp' = B' fp'"
    assumes R0: "P arb\<^sub>0 x x'"
    assumes RS: "\<And>f f' x x' arb.
       \<lbrakk>\<And>x x' arb. P arb x x' \<Longrightarrow> tr arb x x' (f x) (f' x'); P arb x x'; fp' = f'\<rbrakk>
       \<Longrightarrow> tr arb x x' (B f x) (B' f' x')"
    shows "tr arb\<^sub>0 x x' (flatf_fp b B x) (fp' x')"
    supply rl=flatf_fp_induct_pointwise[where 
      pre="\<lambda>(a,x) y. P a y x" and a="(arb\<^sub>0,_)" and
      post="\<lambda>(a,x') x fp. tr a x x' fp (fp' x')"
      , OF _ MONO]
    apply (rule rl[simplified])
    apply clarsimp
    apply (rule R0)
    apply (subst FP')
    apply clarsimp
    apply (blast intro: RS)
    done
    
  lemma RECT_dep_refine:
    assumes M: "trimono body"
    assumes R0: "(x,x')\<in>R arb\<^sub>0"
    assumes S0: "SS = S arb\<^sub>0 x"
    assumes RS: "\<And>f f' x x' arb. \<lbrakk> \<And>x x' arb. (x,x')\<in>R arb \<Longrightarrow> f x \<le>\<Down>(S arb x) (f' x'); (x,x')\<in>R arb \<rbrakk> 
      \<Longrightarrow> body f x \<le>\<Down>(S arb x) (body' f' x')"
    shows "RECT (\<lambda>f x. body f x) x \<le>\<Down>SS (RECT (\<lambda>f' x'. body' f' x') x')"
    unfolding RECT_def S0
    apply (clarsimp simp add: M)
  
    apply (rule flatf_fixp_dep_transfer[where 
          fp'="flatf_gfp body" 
      and B'=body 
      and P="\<lambda>arb x x'. (x',x)\<in>R arb"
      and arb\<^sub>0=arb\<^sub>0, 
      OF _ _ flatf_ord.fixp_unfold[OF M[THEN trimonoD_flatf_ge]] R0])
    apply simp
    apply (simp add: trimonoD)
    by (rule RS)
  
  
  
lemma sorted_lelI:
  assumes "transp R"
  assumes "sorted_wrt R xs\<^sub>1"  
  assumes "sorted_wrt R xs\<^sub>2"  
  assumes "xs\<^sub>1\<noteq>[] \<Longrightarrow> R (last xs\<^sub>1) x"
  assumes "\<forall>y\<in>set xs\<^sub>2. R x y"
  shows "sorted_wrt R (xs\<^sub>1@x#xs\<^sub>2)"
  using assms
  apply (cases xs\<^sub>1 rule: rev_cases)
  apply (auto simp: sorted_wrt_append dest: transpD)
  done
  
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
  
lemma slice_map: "Misc.slice l h (map f xs) = map f (Misc.slice l h xs)"
  unfolding Misc.slice_def 
  by (simp add: drop_map take_map)

lemma slice_upd_sym: "\<lbrakk>l \<le>i; i<h; h \<le> length xs\<rbrakk> \<Longrightarrow> Misc.slice l h (xs[i := x]) = (Misc.slice l h xs)[i-l:=x]"
  unfolding Misc.slice_def
  by (simp add: drop_update_swap)
  
lemma take_slice: "take n (slice l h xs) = slice l (min h (l+n)) xs"
  apply (clarsimp simp: Misc.slice_def min_def)
  using le_add_diff_inverse by fastforce

lemma drop_slice: "drop n (slice l h xs) = slice (l+n) h xs"  
  by (auto simp: Misc.slice_def drop_take algebra_simps)
  
lemma slice_Suc_conv: "\<lbrakk>l\<le>h; Suc h\<le>length xs\<rbrakk> \<Longrightarrow> slice l (Suc h) xs = slice l h xs @ [xs!h]"  
  apply (auto simp add: list_eq_iff_nth_eq slice_nth nth_append)
  by (metis Nat.le_imp_diff_is_add Suc_diff_le add.commute less_antisym)
  
  
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
  
lemma set_slice_subsetI: "\<lbrakk> l'\<le>l; h\<le>h' \<rbrakk> \<Longrightarrow> set (slice l h xs) \<subseteq> set (slice l' h' xs)"
  unfolding Misc.slice_def
  apply auto
  by (metis (no_types, hide_lams) drop_take in_mono min.absorb1 set_drop_subset_set_drop set_take_subset subset_eq take_take)

  
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
  "\<lbrakk>i\<in>{l..<h}; j\<in>{l..<h}; h\<le>length ys \<rbrakk> \<Longrightarrow> slice_eq_mset l h xs (swap ys i j) \<longleftrightarrow> slice_eq_mset l h xs ys"  
  "\<lbrakk>i\<in>{l..<h}; j\<in>{l..<h}; h\<le>length xs \<rbrakk> \<Longrightarrow> slice_eq_mset l h xs (swap ys i j) \<longleftrightarrow> slice_eq_mset l h xs ys"  
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
  
definition  idx_shift_rel :: "nat \<Rightarrow> nat rel" where "idx_shift_rel s \<equiv> {(i,i'). i = i'+s}"

lemma idx_shift_rel_alt: "l\<le>ii \<Longrightarrow> (ii,i)\<in>idx_shift_rel l \<longleftrightarrow> i=ii-l"
  by (auto simp: idx_shift_rel_def)


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

  
lemma slice_rel_rebase: "(xsi', xs) \<in> slice_rel xsi l h \<Longrightarrow> slice_rel xsi l h = slice_rel xsi' l h"
  by (auto simp: slice_rel_def in_br_conv)


  
  
  
(* TODO: Move *)  
  
  definition "list_rel_on R I xs ys \<equiv> I\<subseteq>{0..<length ys} \<and> length xs = length ys \<and> (\<forall>i\<in>I. R (xs!i) (ys!i))"

  lemma list_rel_on_gen_trans[trans]: "list_rel_on R\<^sub>1 I\<^sub>1 xs ys \<Longrightarrow> list_rel_on R\<^sub>2 I\<^sub>2 ys zs \<Longrightarrow> list_rel_on (R\<^sub>1 OO R\<^sub>2) (I\<^sub>1\<inter>I\<^sub>2) xs zs"
    unfolding list_rel_on_def 
    by auto
    
  lemma list_rel_on_gen_trans'[trans]: "\<lbrakk>list_rel_on R\<^sub>1 I\<^sub>1 xs ys; list_rel_on R\<^sub>2 I\<^sub>2 ys zs; R'=R\<^sub>1 OO R\<^sub>2; I'=I\<^sub>1\<inter>I\<^sub>2\<rbrakk> \<Longrightarrow> list_rel_on R' I' xs zs"
    unfolding list_rel_on_def 
    by auto
  
  lemma list_rel_on_empty: "list_rel_on R {} xs ys \<longleftrightarrow> length xs = length ys"  
    unfolding list_rel_on_def 
    by auto

  lemma list_rel_on_whole: "list_rel_on R {0..<length ys} xs ys \<longleftrightarrow> list_all2 R xs ys"      
    unfolding list_rel_on_def 
    by (auto simp: list_all2_conv_all_nth)

  lemma list_rel_on_combine: "list_rel_on R\<^sub>1 I\<^sub>1 xs ys \<Longrightarrow> list_rel_on R\<^sub>2 I\<^sub>2 xs ys \<Longrightarrow> list_rel_on (sup R\<^sub>1 R\<^sub>2) (I\<^sub>1\<union>I\<^sub>2) xs ys"  
    unfolding list_rel_on_def 
    by auto

  lemma list_rel_on_mono: "R\<^sub>1\<le>R\<^sub>2 \<Longrightarrow> I\<^sub>2\<subseteq>I\<^sub>1 \<Longrightarrow> list_rel_on R\<^sub>1 I\<^sub>1 \<le> list_rel_on R\<^sub>2 I\<^sub>2"  
    unfolding list_rel_on_def 
    by auto

  lemma list_rel_on_union: "list_rel_on R (I\<^sub>1\<union>I\<^sub>2) xs ys \<longleftrightarrow> list_rel_on R I\<^sub>1 xs ys \<and> list_rel_on R I\<^sub>2 xs ys"
    unfolding list_rel_on_def 
    by auto
      
  lemma list_rel_on_lenD: "list_rel_on R I xs ys \<Longrightarrow> length xs = length ys"          
    unfolding list_rel_on_def 
    by auto
    

  definition "slicep_rel l h \<equiv> {(xsi,xs). xs=slice l h xsi \<and> l\<le>h \<and> h\<le>length xsi}"  
     
  definition "eq_outside_range xs xs\<^sub>0 l h \<equiv> l\<le>h \<and> h\<le>length xs\<^sub>0 \<and> length xs=length xs\<^sub>0 \<and> take l xs = take l xs\<^sub>0 \<and> drop h xs = drop h xs\<^sub>0"
  lemma eq_outside_range_list_rel_on_conv: 
    "eq_outside_range xs ys l h \<longleftrightarrow> l\<le>h \<and> h\<le>length xs \<and> list_rel_on (=) ({0..<l}\<union>{h..<length ys}) xs ys"
    unfolding eq_outside_range_def list_rel_on_def
    apply clarsimp
    apply (simp only: list_eq_iff_nth_eq) 
    apply (safe; clarsimp)
    by (metis diff_less_mono le_add_diff_inverse)
  
  lemma eq_outside_rane_lenD: "eq_outside_range xs xs\<^sub>0 l h \<Longrightarrow> length xs = length xs\<^sub>0"
    unfolding eq_outside_range_def by auto

  lemma eq_outside_range_gen_trans: "\<lbrakk>eq_outside_range xs ys l h; eq_outside_range ys zs l' h'; ll=min l l'; hh=max h h'\<rbrakk> 
    \<Longrightarrow> eq_outside_range xs zs ll hh"  
    unfolding eq_outside_range_list_rel_on_conv
    apply (safe; (clarsimp simp: list_rel_on_lenD)?)
    subgoal by auto
    subgoal
      apply (clarsimp simp: list_rel_on_union; intro conjI)
      apply (erule (1) list_rel_on_gen_trans'[where I\<^sub>1="{0..<l}" and I\<^sub>2="{0..<l'}"]; auto)
      apply (erule (1) list_rel_on_gen_trans'[where I\<^sub>1="{h..<_}" and I\<^sub>2="{h'..<_}"]; auto)
      done
    done  

  lemma eq_outside_range_triv: "eq_outside_range xs xs l h \<longleftrightarrow> l \<le> h \<and> h \<le> length xs"  
    unfolding eq_outside_range_def
    by simp
    
  
  lemma eq_outside_range_sym: "eq_outside_range xs xs' l h \<Longrightarrow> eq_outside_range xs' xs l h"
    unfolding eq_outside_range_def by auto
    
          
  lemma slice_rel_alt: "(xsi,xs)\<in>slice_rel xs\<^sub>0 l h \<longleftrightarrow> (xsi,xs)\<in>slicep_rel l h \<and> eq_outside_range xsi xs\<^sub>0 l h"
    unfolding slice_rel_def slicep_rel_def eq_outside_range_def in_br_conv
    by auto
   
  lemma slice_eq_outside_range: "\<lbrakk>eq_outside_range xs ys l h; {l..<h}\<inter>{l'..<h'}={}\<rbrakk> \<Longrightarrow> slice l' h' xs = slice l' h' ys"
    unfolding Misc.slice_def eq_outside_range_def
    apply simp apply (safe;clarsimp?)
    subgoal by (metis drop_take le_def min.absorb1 take_take) 
    subgoal by (metis drop_eq_mono leI) 
    subgoal by (metis append_take_drop_id)
    done
    
  lemma slicep_rel_eq_outside_range: "\<lbrakk>eq_outside_range xs ys l h; {l..<h}\<inter>{l'..<h'}={}\<rbrakk> 
    \<Longrightarrow> (xs,ss)\<in>slicep_rel l' h' \<longleftrightarrow> (ys,ss)\<in>slicep_rel l' h'"
    unfolding slicep_rel_def
    by (auto simp add: slice_eq_outside_range eq_outside_rane_lenD)
        
  lemma slicep_rel_append: "\<lbrakk> (xs,ys\<^sub>1)\<in>slicep_rel l m; (xs,ys\<^sub>2)\<in>slicep_rel m h \<rbrakk> \<Longrightarrow> (xs, ys\<^sub>1@ys\<^sub>2)\<in>slicep_rel l h"
    unfolding slicep_rel_def
    by (auto simp: slice_append)
  
  lemma slicep_rel_take: "\<lbrakk>(xsi, xs) \<in> slicep_rel l h; n\<le>length xs\<rbrakk> \<Longrightarrow> (xsi, take n xs) \<in> slicep_rel l (n+l)"
    unfolding slicep_rel_def
    by (auto simp: take_slice algebra_simps)
  
  lemma slicep_rel_drop: "\<lbrakk>(xsi, xs) \<in> slicep_rel l h; n\<le>length xs\<rbrakk> \<Longrightarrow> (xsi, drop n xs) \<in> slicep_rel (n+l) h"
    unfolding slicep_rel_def
    by (auto simp: drop_slice algebra_simps)
  
  
  lemma eq_outside_range_nth:
    "eq_outside_range xs xs' l h \<Longrightarrow> i<l \<Longrightarrow> xs!i = xs'!i"
    "eq_outside_range xs xs' l h \<Longrightarrow> h\<le>i \<Longrightarrow> xs!i = xs'!i"
    unfolding eq_outside_range_def
    apply (clarsimp_all)
    subgoal by (metis nth_take)
    subgoal by (metis le_Suc_ex nth_drop)
    done
    
  lemma eq_outside_erange_upd_inside: "\<lbrakk> i\<in>{l..<h} \<rbrakk> \<Longrightarrow> eq_outside_range xs (xs'[i:=x]) l h \<longleftrightarrow> eq_outside_range xs xs' l h"
    unfolding eq_outside_range_def
    by auto
  
    
    
(* TODO: Unify these concepts! *)
lemma slice_eq_mset_alt: 
  "\<lbrakk>l\<le>h; h\<le>length xs'\<rbrakk> \<Longrightarrow> slice_eq_mset l h xs xs' \<longleftrightarrow> eq_outside_range xs xs' l h \<and> mset (slice l h xs) = mset (slice l h xs')"
  unfolding slice_eq_mset_def eq_outside_range_def by auto

  
  
  
  
  
  
  
  
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
lemmas [llvm_pre_simp] = len_of_numeral_defs of_nat_numeral
  
(* Sepref setup for LENGTH *)
  
sepref_register "LENGTH(_)"

context begin
  lemma size_fits_snat_aux: "x < 2^(x-Suc 0) \<longleftrightarrow> x=0 \<or> x>2"
    by (smt diff_Suc_1 gr0_implies_Suc le0 le_less_trans less_numeral_extra(4) less_one linorder_neqE_nat nat_neq_iff not_less_eq not_numeral_less_one numeral_2_eq_2 order_less_irrefl power_0 power_one_right suc_le_pow_2 zero_diff zero_less_one)
  
  lemma size_fits_snat_aux2: "LENGTH('a)>2 \<Longrightarrow> snat_invar (of_nat LENGTH('a) :: 'a::len2 word)"
    unfolding snat_invar_alt
    apply (rule exI[where x = "LENGTH('a) - 1"])
    apply (auto simp: unat_of_nat size_fits_snat_aux)
    by (simp add: size_fits_snat_aux take_bit_nat_eq_self)
    
end    

    
lemma LENGTH_refine[sepref_fr_rules]: 
  "LENGTH('a)>2 \<Longrightarrow> (uncurry0 (return (of_nat (LENGTH('a::len2))::'a word)), uncurry0 (RETURN (PR_CONST LENGTH('a)))) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a snat_assn"
  apply sepref_to_hoare
  unfolding snat_rel_def snat.rel_def 
  supply [simp] = in_br_conv word_size size_fits_snat_aux2
  apply vcg'
  by (metis n_less_equal_power_2 size_fits_snat_aux2 snat_eq_unat_aux2 unat_of_nat_len)

lemma size_refine[sepref_fr_rules]: "LENGTH('a)>2 \<Longrightarrow> (return o (\<lambda>_. of_nat (LENGTH('a))), RETURN o size) \<in> (word_assn' TYPE('a::len2))\<^sup>k \<rightarrow>\<^sub>a snat_assn' TYPE('a)"
  apply sepref_to_hoare
  unfolding snat_rel_def snat.rel_def 
  supply [simp] = in_br_conv word_size size_fits_snat_aux2
  apply vcg'
  by (metis n_less_equal_power_2 of_nat_inverse size_fits_snat_aux2 snat_eq_unat_aux2)
  
  
(* TODO: Move *)  
(* Assertion-guarded operations on nats, which are going to be refined to bounded numbers *)
    named_theorems mop_nat_defs

  definition mop_nat_sub :: "nat \<Rightarrow> nat \<Rightarrow> nat nres" where [mop_nat_defs]: "mop_nat_sub a b \<equiv> doN { ASSERT (a\<ge>b); RETURN (a-b) }"
  definition mop_nat_add_bnd :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat nres" where [mop_nat_defs]: "mop_nat_add_bnd h a b \<equiv> doN { ASSERT (a+b\<le>h); RETURN (a+b) }"
  definition mop_nat_div :: "nat \<Rightarrow> nat \<Rightarrow> nat nres" where [mop_nat_defs]: "mop_nat_div a b \<equiv> doN { ASSERT (b\<noteq>0); RETURN (a div b) }"
  
  sepref_register mop_nat_sub mop_nat_add_bnd mop_nat_div
  
  context fixes dummy :: "'l::len2" begin
    private abbreviation (input) "N \<equiv> snat_assn' TYPE('l)"
  
    sepref_def snat_sub_impl [llvm_inline] is "uncurry mop_nat_sub" :: "N\<^sup>k*\<^sub>aN\<^sup>k\<rightarrow>\<^sub>aN"
      unfolding mop_nat_defs by sepref
  
    sepref_def snat_add_bnd_impl [llvm_inline] is "uncurry2 mop_nat_add_bnd" :: "N\<^sup>k*\<^sub>aN\<^sup>k*\<^sub>aN\<^sup>k\<rightarrow>\<^sub>aN"
      unfolding mop_nat_defs by sepref
  
    sepref_def snat_div_impl [llvm_inline] is "uncurry mop_nat_div" :: "N\<^sup>k*\<^sub>aN\<^sup>k\<rightarrow>\<^sub>aN"
      unfolding mop_nat_defs by sepref

  end    
      

  
  
  
  
  
  
  
  

end
