theory Intro_Sort
imports "../sepref/IICF/IICF" "HOL-Library.Discrete"
begin

hide_const (open) pi Word.slice

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
  

definition "sort_spec xs xs' \<equiv> mset xs'=mset xs \<and> sorted xs'" 
  
definition "slice_sort_spec xs\<^sub>0 l h \<equiv> doN {
    ASSERT (l\<le>h \<and> h\<le>length xs\<^sub>0);
    SPEC (\<lambda>xs. length xs = length xs\<^sub>0 \<and> take l xs = take l xs\<^sub>0 \<and> drop h xs = drop h xs\<^sub>0 \<and> sort_spec (Misc.slice l h xs\<^sub>0) (Misc.slice l h xs))
  }"
  
  

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


section \<open>Heapsort\<close>  
  
(* TODO: Refine lemmas to support more general datatypes! *)
type_synonym size_t = "64"
type_synonym elem_t = "64"

abbreviation "size_assn \<equiv> snat_assn' TYPE(size_t)"
abbreviation "elem_assn \<equiv> unat_assn' TYPE(elem_t)"

abbreviation "arr_assn \<equiv> array_assn elem_assn"




locale heap_range_context =
  fixes l h :: nat
  assumes ran_not_empty[arith,simp]: "l\<le>h"
begin  

  (*lemma l_le_h[arith,simp]: "l\<le>h" by simp*)

  definition "in_heap i \<equiv> i\<in>{l..<h}"

  (*  
  definition parent where "parent i \<equiv> (i-l+1) div 2 + l - 1"
  definition lchild where "lchild i \<equiv> 2*(i-l+1) - 1 + l"
  definition rchild where "rchild i \<equiv> 2*(i-l+1) + l"
  *)
  
  definition parent where "parent i \<equiv> (i-1-l) div 2 + l"
  definition lchild where "lchild i \<equiv> 2*(i-l) + 1 + l"
  definition rchild where "rchild i \<equiv> 2*(i-l) + 2+ l"
  
  
  
  
  definition has_parent where "has_parent i \<equiv> in_heap i \<and> i>l"
  definition has_lchild where "has_lchild i \<equiv> in_heap i \<and> in_heap (lchild i)"
  definition has_rchild where "has_rchild i \<equiv> in_heap i \<and> in_heap (rchild i)"
  
  context begin
    private method prove = (
      unfold in_heap_def parent_def has_parent_def lchild_def rchild_def has_lchild_def has_rchild_def, 
      auto)

    text \<open>Optimized checks, normalize to i-l, for index shift\<close>
    lemma has_rchild_ihs: "in_heap i \<Longrightarrow> has_rchild i \<longleftrightarrow> i-l<(h-l-1) div 2"
      by prove

    lemma has_lchild_ihs: "in_heap i \<Longrightarrow> has_lchild i \<longleftrightarrow> (i-l) < (h-l) div 2"  
      by prove
      
    lemma has_parent_ihs: "in_heap i \<Longrightarrow> has_parent i \<longleftrightarrow> i-l > 0"
      by prove
      
    lemma lchild_ihs: "lchild i - l = 2*(i-l)+1"  
      by prove
      
    lemma rchild_ihs: "rchild i - l = 2*(i-l)+2"  
      by prove
      
    lemma parent_ihs: "parent i - l = (i-l-1) div 2"
      by prove
      
    lemma in_heapI: "\<lbrakk> l\<le>i; i<h \<rbrakk> \<Longrightarrow> in_heap i" by prove
      
    lemma in_heap_bounds[arith,simp]: 
      assumes "in_heap i" 
      shows "l\<le>i" and "i<h"
      using assms by prove

    lemma in_heap_triv[simp]: 
      "has_parent i \<Longrightarrow> in_heap i"        
      "has_lchild i \<Longrightarrow> in_heap i"        
      "has_rchild i \<Longrightarrow> in_heap i"        
      by prove
            
    lemma parent_in_heap[simp]: 
      "has_parent i \<Longrightarrow> in_heap (parent i)" 
      "has_parent i \<Longrightarrow> has_lchild (parent i)" 
      by prove
    
    lemma children_in_heap[simp]: 
      "has_lchild i \<Longrightarrow> in_heap (lchild i)"
      "has_rchild i \<Longrightarrow> in_heap (rchild i)"
      by prove
      

    lemma parent_of_child[simp]:
      "has_lchild i \<Longrightarrow> parent (lchild i) = i"
      "has_rchild i \<Longrightarrow> parent (rchild i) = i"
      by prove

    lemma children_differ[simp]:
      "lchild i \<noteq> rchild i" 
      "rchild i \<noteq> lchild i" 
      by prove

    lemma parent_less[arith,simp]: "has_parent i \<Longrightarrow> parent i < i" by prove

    lemma children_greater[arith,simp]: 
      "lchild i > i" 
      "rchild i > i"
      by prove

      
    lemma children_diff_add_simps[simp]:
      "lchild i \<noteq> i"  
      "i \<noteq> lchild i"  
      "rchild i \<noteq> i"  
      "i \<noteq> rchild i"  
      by prove
      
    lemma parent_diff_add_simps[simp]: 
      assumes "has_parent i" shows "i \<noteq> parent i" and "parent i \<noteq> i"
      using assms by prove
      
    lemma rchild_imp_lchild[simp, intro]: "has_rchild i \<Longrightarrow> has_lchild i" by prove

    lemma no_parent_is_root: "in_heap i \<Longrightarrow> \<not>has_parent i \<longleftrightarrow> i=l" by prove
    
    lemma root_no_parent[simp, intro!]: "\<not>has_parent l" by prove
    
    
    lemma root_in_heap[simp]: "in_heap l\<longleftrightarrow>l<h" using ran_not_empty by prove
    
                      
    lemma child_of_parent: "has_parent i \<Longrightarrow> lchild (parent i) = i \<or> has_rchild (parent i) \<and> rchild (parent i) = i" by prove
                
    lemma children_of_parent_cases[consumes 1]:
      assumes "has_parent i"
      obtains (left) "has_parent i" "lchild (parent i) = i" 
            | (right) "has_parent i" "has_rchild (parent i)" "rchild (parent i) = i"
      using assms child_of_parent by blast            

    lemma lchild_of_no_rchild_term[intro,simp]: "\<lbrakk>\<not>has_rchild i; has_lchild i\<rbrakk> \<Longrightarrow> \<not>has_lchild (lchild i)" by prove 
      
      
          
  end

  lemmas heap_context_defs[no_atp] = in_heap_def parent_def lchild_def rchild_def has_parent_def has_lchild_def has_rchild_def
  
  
  definition is_heap :: "'a::linorder list \<Rightarrow> bool" 
    where "is_heap xs \<equiv> (h\<le>length xs) \<and> (\<forall>i. has_parent i \<longrightarrow> xs!parent i \<ge> xs!i)"

    
  subsection \<open>Heap Property implies Minimal Element at Top\<close>
  context
    fixes xs
    assumes H: "is_heap xs"
  begin  

    lemma parent_el_greater[simp]: "has_parent i \<Longrightarrow> xs!i \<le> xs!parent i"
      using H
      unfolding is_heap_def 
      by simp
    
    lemma root_greatest:
      assumes "in_heap i"
      shows "xs!i \<le> xs!l"
      using assms 
    proof (induction i rule: less_induct)
      case (less i)
      note [simp] = \<open>in_heap i\<close>
      
      show ?case proof cases
        assume [simp]: "has_parent i"
        have "xs!i \<le> xs!parent i" by simp
        also from less.IH[of "parent i"] have "xs!parent i \<le> xs!l" by simp
        finally show ?case .
      next
        assume "\<not>has_parent i" 
        hence "i=l" by (simp add: no_parent_is_root)
        thus ?case by simp
      qed  
    qed
  
  end  

    
  subsection \<open>Sift-Up Lemmas\<close>    
  definition is_heap_except_up :: "nat \<Rightarrow> 'a::linorder list \<Rightarrow> bool" 
    where "is_heap_except_up j xs \<equiv> 
      (h\<le>length xs) 
      \<and> (\<forall>i. has_parent i \<and> i\<noteq>j \<longrightarrow> xs!parent i \<ge> xs!i)
      \<and> (has_parent j \<and> has_lchild j \<longrightarrow> xs!parent j \<ge> xs!lchild j)
      \<and> (has_parent j \<and> has_rchild j \<longrightarrow> xs!parent j \<ge> xs!rchild j)"

  lemma is_heap_except_up_len_bound[simp, intro]: 
    assumes "is_heap_except_up i xs"
    shows "h\<le>length xs"     
    using assms unfolding is_heap_except_up_def
    by auto
        
  lemma sift_up_lemma:
    assumes HP: "has_parent i"
    assumes IHE: "is_heap_except_up i xs"
    assumes GE: "xs!i \<ge> xs!parent i"
    shows "is_heap_except_up (parent i) (swap xs i (parent i))"
  proof -
    from assms(2) have [simp, arith]: "h\<le>length xs" unfolding is_heap_except_up_def by auto
  
    have X[simp]: "i<length xs" if "in_heap i" for i
      using in_heap_bounds(2)[OF that] by simp

    have HPROP: "xs!j \<le> xs!parent j" if "has_parent j" "j\<noteq>i" for j
      using that IHE unfolding is_heap_except_up_def by simp
      
      
    show ?thesis using HP
      unfolding is_heap_except_up_def
      apply (clarsimp; safe)
      subgoal
        apply (clarsimp simp: swap_nth HPROP GE; safe)
        subgoal by (metis GE HPROP order.trans)
        by (metis IHE child_of_parent is_heap_except_up_def parent_in_heap(2))

      subgoal
        by (smt HPROP X children_in_heap(1) children_greater(1) has_parent_def leI less_le_trans less_not_sym parent_in_heap(2) parent_less parent_of_child(1) swap_nth) 
      subgoal 
        by (smt HPROP X children_greater(2) children_in_heap(2) dual_order.strict_trans eq_iff has_parent_def leD le_less_linear parent_diff_add_simps(2) parent_in_heap(1) parent_of_child(2) swap_nth)
        
      done
      
  qed

  text \<open>Terminate when reached root\<close>
  lemma sift_up_term1: "is_heap_except_up l xs \<Longrightarrow> is_heap xs"
    unfolding is_heap_def is_heap_except_up_def by auto
  
  text \<open>Terminate when parent is greater or equal\<close>  
  lemma sift_up_term2: "\<lbrakk>is_heap_except_up i xs; xs!i\<le>xs!parent i\<rbrakk> \<Longrightarrow> is_heap xs"
    unfolding is_heap_def is_heap_except_up_def by auto
    
  (* XXX: Use is_heap_context_except_down i (xs[i:=v]) instead, and refine from swap-lemmas!    
    
  text \<open>Move-optimized sift-up: Let \<open>v\<close> be value to be sifted-up.
    We first only make space for \<open>v\<close>, by moving down values, 
    but not assigning \<open>v\<close>.
  
    Invariants are heap-except, and the value at current index is \<open>\<le>v\<close>
  \<close>  

  
  text \<open>
    Shifting is always valid for heap-except property.#
    Though should only be done if \<open>v \<ge> xs!parent i\<close>, to preserve \<open>v \<ge> xs!i\<close> invariant. 
  \<close>  
  lemma sift_up_lemma':
    assumes HP: "has_parent i"
    assumes IHE: "is_heap_except_up i xs"
    shows "is_heap_except_up (parent i) (xs[i:=xs!parent i])"
  proof -
    from assms(2) have [simp, arith]: "h\<le>length xs" unfolding is_heap_except_up_def by auto
  
    have X[simp]: "i<length xs" if "in_heap i" for i
      using in_heap_bounds(2)[OF that] by simp

    have HPROP: "xs!j \<le> xs!parent j" if "has_parent j" "j\<noteq>i" for j
      using that IHE unfolding is_heap_except_up_def by simp
      
    have [simp]: "i\<noteq>parent (parent i)" if "has_parent (parent i)"
      by (metis HP less_not_sym parent_less that) 
      
    show ?thesis using HP
      unfolding is_heap_except_up_def
      apply (clarsimp simp: ; safe)
      apply (all \<open>clarsimp simp: nth_list_update HPROP\<close>)
      subgoal
        by (metis IHE child_of_parent is_heap_except_up_def parent_in_heap(2))
      subgoal
        by (smt HPROP children_greater(1) children_in_heap(1) dual_order.trans heap_range_context.has_parent_def heap_range_context.parent_in_heap(2) heap_range_context_axioms less_not_sym no_parent_is_root parent_of_child(1))
      subgoal
        by (metis HP HPROP child_of_parent children_diff_add_simps(1) children_greater(2) heap_range_context.children_in_heap(2) heap_range_context_axioms in_heap_bounds(1) le_def no_parent_is_root order.trans parent_in_heap(1) parent_of_child(2))
        
      done        
      
  qed
  
  text \<open>Terminate optimized sift-up\<close>
  lemma sift_up'_term1: "\<lbrakk>is_heap_except_up l xs; xs!l\<le>v\<rbrakk> \<Longrightarrow> is_heap (xs[l:=v])"
    unfolding is_heap_def is_heap_except_up_def 
    apply simp
    by (metis dual_order.trans nth_list_update_eq nth_list_update_neq nth_update_invalid root_no_parent)
  
  lemma sift_up'_term2: "\<lbrakk>is_heap_except_up i xs; xs!i\<le>v; v\<le>xs!parent i\<rbrakk> \<Longrightarrow> is_heap (xs[i:=v])"
    unfolding is_heap_def is_heap_except_up_def 
    by (smt dual_order.trans length_list_update nth_list_update nth_list_update_neq nth_update_invalid)
  *)
  

  
  lemma grow_heap_context: "heap_range_context l (Suc h)" 
    apply unfold_locales using ran_not_empty by linarith 
    
  text \<open>Initializes a sift-up cycle by extending the heap by one element to the right\<close>  
  lemma sift_up_init:
    assumes "is_heap xs"
    assumes "h<length xs"
    shows "heap_range_context.is_heap_except_up l (Suc h) h xs"
  proof -
    interpret N: heap_range_context l "Suc h" using grow_heap_context .
  
    show ?thesis
      using assms
      unfolding is_heap_def is_heap_except_up_def N.is_heap_except_up_def
      unfolding N.heap_context_defs heap_context_defs
      by auto
      
  qed
  
  subsection \<open>Sift-Down Lemmas\<close>    

  definition is_heap_except_down :: "nat \<Rightarrow> 'a::linorder list \<Rightarrow> bool"
    where "is_heap_except_down j xs \<equiv>
        (h\<le>length xs) 
      \<and> (\<forall>i. has_parent i \<and> parent i \<noteq> j \<longrightarrow> xs!parent i \<ge> xs!i)
      \<and> (\<forall>i. has_parent i \<and> has_parent j \<and> parent i = j \<longrightarrow> xs!parent j \<ge> xs!i)"

  lemma is_heap_except_down_len_bound[simp, intro]: 
    assumes "is_heap_except_down i xs"
    shows "h\<le>length xs"     
    using assms unfolding is_heap_except_down_def
    by auto
          
  lemma sift_down_lemma_left:
    assumes HRC: "has_rchild i"
    assumes IHE: "is_heap_except_down i xs"
    assumes GE: "xs!lchild i \<ge> xs!i" "xs!lchild i \<ge> xs!rchild i"
    shows "is_heap_except_down (lchild i) (swap xs i (lchild i))"
  proof -  
    show ?thesis 
      using IHE HRC GE
      unfolding is_heap_except_down_def
      apply (clarsimp)
      by (smt child_of_parent children_greater(1) children_in_heap(1) eq_iff heap_range_context.has_parent_def heap_range_context_axioms in_heap_bounds(2) less_imp_le_nat less_le_trans parent_of_child(1) rchild_imp_lchild swap_nth)
      
  qed

  lemma sift_down_lemma_right:
    assumes HRC: "has_rchild i"
    assumes IHE: "is_heap_except_down i xs"
    assumes GE: "xs!rchild i \<ge> xs!i" "xs!lchild i \<le> xs!rchild i"
    shows "is_heap_except_down (rchild i) (swap xs i (rchild i))"
  proof -  
    show ?thesis 
      using IHE HRC GE
      unfolding is_heap_except_down_def
      apply (clarsimp)
      by (smt child_of_parent children_greater(2) children_in_heap(2) dual_order.trans eq_iff heap_range_context.has_parent_def heap_range_context_axioms in_heap_bounds(2) less_le parent_less parent_of_child(2) swap_nth)
      
  qed
  
    
  lemma sift_down_lemma_left_no_right_child:
    assumes HRC: "has_lchild i" "\<not>has_rchild i"
    assumes IHE: "is_heap_except_down i xs"
    assumes GE: "xs!lchild i \<ge> xs!i"
    shows "is_heap_except_down (lchild i) (swap xs i (lchild i))"
  proof -  
    from IHE have [simp, arith]: "h\<le>length xs" unfolding is_heap_except_down_def by auto
    
    have X[simp]: "i<length xs" if "in_heap i" for i
      using in_heap_bounds(2)[OF that] by simp
      
    show ?thesis 
      using IHE HRC GE
      unfolding is_heap_except_down_def
      apply clarsimp
      by (smt X child_of_parent children_greater(1) children_in_heap(1) heap_range_context.has_parent_def heap_range_context.parent_of_child(1) heap_range_context_axioms le_less_trans less_imp_le_nat parent_in_heap(1) swap_nth)
      
  qed

  
  lemma sift_down_term1: "\<not>has_lchild j \<Longrightarrow> is_heap_except_down j xs \<longleftrightarrow> is_heap xs"
    unfolding is_heap_except_down_def is_heap_def
    by auto
  
  lemma sift_down_term2: "\<lbrakk>is_heap_except_down j xs; has_rchild j; xs!j\<ge>xs!lchild j; xs!j\<ge>xs!rchild j \<rbrakk> \<Longrightarrow> is_heap xs"
    unfolding is_heap_except_down_def is_heap_def
    apply (clarsimp)
    by (metis children_of_parent_cases)
  
  lemma sift_down_term3: "\<lbrakk>is_heap_except_down j xs; has_lchild j; \<not>has_rchild j; xs!j\<ge>xs!lchild j \<rbrakk> \<Longrightarrow> is_heap xs"
    unfolding is_heap_except_down_def is_heap_def
    apply (clarsimp)
    by (metis children_of_parent_cases)

  (* XXX: Use is_heap_context_except_down i (xs[i:=v]) instead, and refine from swap-lemmas!    
  lemma sift_down_lemma_left':
    assumes HRC: "has_rchild i"
    assumes IHE: "is_heap_except_down i xs"
    assumes GE: "xs!lchild i \<ge> xs!rchild i"
    shows "is_heap_except_down (lchild i) (xs[i:=xs!lchild i])"
  proof -  
    show ?thesis 
      using IHE HRC GE
      unfolding is_heap_except_down_def
      apply clarsimp
      by (smt children_greater(1) children_in_heap(1) dual_order.strict_trans2 eq_iff heap_range_context.child_of_parent heap_range_context.has_parent_def heap_range_context.in_heap_bounds(1) heap_range_context.in_heap_bounds(2) heap_range_context.in_heap_triv(3) heap_range_context.rchild_imp_lchild heap_range_context_axioms less_le_trans nth_list_update parent_of_child(1))
      
  qed
  
  lemma sift_down_lemma_right':
    assumes HRC: "has_rchild i"
    assumes IHE: "is_heap_except_down i xs"
    assumes GE: "xs!lchild i \<le> xs!rchild i"
    shows "is_heap_except_down (rchild i) (xs[i:=xs!rchild i])"
  proof -  
    show ?thesis 
      using IHE HRC GE
      unfolding is_heap_except_down_def
      apply clarsimp
      by (smt child_of_parent children_greater(2) children_in_heap(2) dual_order.strict_trans eq_iff heap_range_context.has_parent_def heap_range_context_axioms in_heap_bounds(2) le_less_linear nth_list_update_eq nth_list_update_neq parent_of_child(2))
      
  qed
  
  lemma sift_down_lemma_left_no_right_child':
    assumes HRC: "has_lchild i" "\<not>has_rchild i"
    assumes IHE: "is_heap_except_down i xs"
    shows "is_heap_except_down (lchild i) (xs[i:=xs!lchild i])"
  proof -  
    show ?thesis 
      using IHE HRC
      unfolding is_heap_except_down_def
      apply (clarsimp simp: nth_list_update)
      by (smt child_of_parent children_greater(1) children_in_heap(1) eq_iff heap_range_context.in_heap_triv(2) heap_range_context_axioms in_heap_bounds(1) in_heap_bounds(2) leD less_le_trans no_parent_is_root nth_list_update' parent_of_child(1))
      
  qed
    
  lemma sift_down'_term1: "\<lbrakk>is_heap_except_down j xs; v\<le>xs!j; \<not>has_lchild j \<rbrakk> \<Longrightarrow> is_heap (xs[j:=v])"
    unfolding is_heap_except_down_def is_heap_def
    apply simp
    by (smt heap_range_context.parent_in_heap(2) heap_range_context_axioms nth_list_update' order.trans)
    
  lemma sift_down_term2': "\<lbrakk>is_heap_except_down j xs; v\<le>xs!j; has_rchild j; v\<ge>xs!lchild j; v\<ge>xs!rchild j \<rbrakk> \<Longrightarrow> is_heap (xs[j:=v])"
    unfolding is_heap_except_down_def is_heap_def
    apply (clarsimp)
    by (smt child_of_parent dual_order.trans nth_list_update_eq nth_list_update_neq nth_update_invalid)
  
  lemma sift_down_term3': "\<lbrakk>is_heap_except_down j xs; v\<le>xs!j; has_lchild j; \<not>has_rchild j; v\<ge>xs!lchild j \<rbrakk> \<Longrightarrow> is_heap (xs[j:=v])"
    unfolding is_heap_except_down_def is_heap_def
    apply (clarsimp)
    by (smt child_of_parent dual_order.trans nth_list_update_eq nth_list_update_neq nth_update_invalid)  
  *)
      
  lemma shrink_heap_context: "Suc l<h \<Longrightarrow> heap_range_context l (h-Suc 0)" 
    apply unfold_locales using ran_not_empty by linarith 
  
  text \<open>Initializes a sift-down cycle by swapping the first and last element, and then shrinking the heap by one element\<close>
  lemma sift_down_init:  
    assumes "is_heap xs"
    assumes LT: "Suc l < h"
    shows "heap_range_context.is_heap_except_down l (h-Suc 0) l (swap xs l (h-Suc 0))"
  proof -
    interpret N: heap_range_context l "h-Suc 0" using shrink_heap_context[OF LT] .
    
    show ?thesis
      using assms
      unfolding is_heap_def is_heap_except_down_def N.is_heap_except_down_def
      unfolding N.heap_context_defs heap_context_defs
      by (auto simp: swap_nth)
      
  qed    
        
    
  subsection \<open>Bottom-up Heapify\<close>

  text \<open>The nodes from index \<open>l'\<close> upwards satisfy the heap criterion\<close>
  definition is_heap_btu :: "nat \<Rightarrow> 'a::linorder list \<Rightarrow> bool" where "is_heap_btu l' xs \<equiv> 
        (l'\<le>h \<and> h\<le>length xs) 
      \<and> (\<forall>i. has_parent i \<and> parent i \<ge> l' \<longrightarrow> xs!parent i \<ge> xs!i)"

  text \<open>Bottom-up heapify starts with only the last element being a heap\<close>
  lemma btu_heapify_init: "h\<le>length xs \<Longrightarrow> is_heap_btu (h-Suc 0) xs"  
    unfolding is_heap_btu_def
    apply auto
    by (meson dual_order.trans in_heap_bounds(2) in_heap_triv(1) nat_le_Suc_less_imp not_le parent_less)
        
  text \<open>When we have reached the lower index, we have a complete heap\<close>    
  lemma btu_heapify_term: "is_heap_btu l xs \<longleftrightarrow> is_heap xs"
    unfolding is_heap_btu_def is_heap_def
    by (auto simp: less_imp_le_nat)
      
      
  text \<open>All nodes in between l' and h form a valid heap, with downwards-hole at j\<close>
  definition is_heap_except_down_btu :: "nat \<Rightarrow> nat \<Rightarrow> 'a::linorder list \<Rightarrow> bool"
    where "is_heap_except_down_btu l' j xs \<equiv>
        (l'\<le>j \<and> j<h \<and> h\<le>length xs) 
      \<and> (\<forall>i. has_parent i \<and> parent i \<ge> l' \<and> parent i \<noteq> j \<longrightarrow> xs!parent i \<ge> xs!i)
      \<and> (\<forall>i. has_parent i \<and> has_parent j \<and> parent j \<ge>l' \<and> parent i = j \<longrightarrow> xs!parent j \<ge> xs!i)"

  lemma is_heap_except_down_btu_lenD: "is_heap_except_down_btu l' j xs \<Longrightarrow> h\<le>length xs"    
    unfolding is_heap_except_down_btu_def by auto
      
  text \<open>A sift-down round starts by including one more left element, and marking it as a hole\<close>
  lemma btu_sift_down_init: "\<lbrakk>is_heap_btu l' xs; l'>l\<rbrakk> \<Longrightarrow> is_heap_except_down_btu (l'-1) (l'-1) xs"  
    unfolding is_heap_except_down_btu_def is_heap_btu_def 
    apply auto
    using leD parent_less by blast
  
      
  text \<open>Sift-down completed, we have a complete heap from \<open>l'\<close> upwards\<close>
  lemma btu_sift_down_term1: "\<not>has_lchild j \<Longrightarrow> is_heap_except_down_btu l' j xs \<Longrightarrow> is_heap_btu l' xs"
    unfolding is_heap_except_down_btu_def is_heap_btu_def 
    by auto
      
  lemma btu_sift_down_term2: "\<lbrakk>is_heap_except_down_btu l' j xs; has_rchild j; xs!j\<ge>xs!lchild j; xs!j\<ge>xs!rchild j \<rbrakk> 
    \<Longrightarrow> is_heap_btu l' xs"
    unfolding is_heap_except_down_btu_def is_heap_btu_def
    apply (clarsimp)
    by (smt dual_order.trans child_of_parent in_heap_bounds(2) in_heap_triv(3) le_cases not_le)
  
  lemma btu_sift_down_term3: "\<lbrakk>is_heap_except_down_btu l' j xs; has_lchild j; \<not>has_rchild j; xs!j\<ge>xs!lchild j \<rbrakk> \<Longrightarrow> is_heap_btu l' xs"
    unfolding is_heap_except_down_btu_def is_heap_btu_def
    apply (clarsimp)
    by (metis child_of_parent dual_order.trans in_heap_bounds(2) in_heap_triv(2) less_imp_le)
  

  

  lemma btu_heapify_down_left:
    assumes HRC: "has_rchild i"
    assumes IHE: "is_heap_except_down_btu l' i xs"
    assumes GE: "xs!lchild i \<ge> xs!i" "xs!lchild i \<ge> xs!rchild i"
    shows "is_heap_except_down_btu l' (lchild i) (swap xs i (lchild i))"
  proof -
    from IHE have [simp, arith]: "h\<le>length xs" unfolding is_heap_except_down_btu_def by auto
    
    have X[simp]: "i<length xs" if "in_heap i" for i
      using in_heap_bounds(2)[OF that] by simp
    
    show ?thesis
      using HRC IHE GE
      unfolding is_heap_except_down_btu_def
      apply (clarsimp simp: swap_nth)
      by (smt child_of_parent children_greater(1) children_in_heap(1) heap_range_context.has_parent_def heap_range_context_axioms leD le_cases less_le_trans parent_of_child(1) rchild_imp_lchild)
      
  qed  
        
  lemma btu_heapify_down_right:
    assumes HRC: "has_rchild i"
    assumes IHE: "is_heap_except_down_btu l' i xs"
    assumes GE: "xs!rchild i \<ge> xs!i" "xs!lchild i \<le> xs!rchild i"
    shows "is_heap_except_down_btu l' (rchild i) (swap xs i (rchild i))"
  proof -
    from IHE have [simp, arith]: "h\<le>length xs" unfolding is_heap_except_down_btu_def by auto
    
    have X[simp]: "i<length xs" if "in_heap i" for i
      using in_heap_bounds(2)[OF that] by simp
    
    show ?thesis
      using HRC IHE GE
      unfolding is_heap_except_down_btu_def
      apply (clarsimp simp: swap_nth)
      by (smt child_of_parent children_greater(2) children_in_heap(2) dual_order.strict_trans2 heap_range_context.has_parent_def heap_range_context_axioms less_imp_le_nat parent_of_child(2))
      
  qed  
    
  lemma btu_heapify_down_left_no_right_child:
    assumes HRC: "has_lchild i" "\<not>has_rchild i"
    assumes IHE: "is_heap_except_down_btu l' i xs"
    assumes GE: "xs!lchild i \<ge> xs!i"
    shows "is_heap_except_down_btu l' (lchild i) (swap xs i (lchild i))"
  proof -
    from IHE have [simp, arith]: "h\<le>length xs" unfolding is_heap_except_down_btu_def by auto
    
    have X[simp]: "i<length xs" if "in_heap i" for i
      using in_heap_bounds(2)[OF that] by simp
    
    show ?thesis
      using HRC IHE GE
      unfolding is_heap_except_down_btu_def
      apply (clarsimp simp: swap_nth)
      by (smt child_of_parent children_greater(1) children_in_heap(1) heap_range_context.has_parent_def heap_range_context_axioms leD le_cases less_le_trans parent_of_child(1))
      
  qed  
    
  definition "sift_up_invar xs\<^sub>0 i xs \<equiv>
      slice_eq_mset l h xs xs\<^sub>0      
    \<and> is_heap_except_up i xs"  
    
  lemma sift_up_invar_init: 
    assumes "is_heap xs" "slice_eq_mset l h xs xs\<^sub>0" "h<length xs" 
    shows "heap_range_context.sift_up_invar l (Suc h) xs\<^sub>0 h xs"
  proof -
    interpret N: heap_range_context l "Suc h" by (simp add: grow_heap_context)
    
    show ?thesis 
      using assms
      by (meson N.sift_up_invar_def le_eq_less_or_eq nat_in_between_eq(1) ran_not_empty sift_up_init slice_eq_mset_subslice)
      
  qed    
      
  lemma sift_up_invar_step: "\<lbrakk>sift_up_invar xs\<^sub>0 i xs; has_parent i; xs!i\<ge>xs!parent i \<rbrakk> 
    \<Longrightarrow> sift_up_invar xs\<^sub>0 (parent i) (swap xs i (parent i))"
    unfolding sift_up_invar_def
    by (auto simp: sift_up_lemma)
    
  lemma sift_up_invar_term1: "\<lbrakk>sift_up_invar xs\<^sub>0 l xs\<rbrakk> \<Longrightarrow> is_heap xs \<and> slice_eq_mset l h xs xs\<^sub>0"
    unfolding sift_up_invar_def
    using sift_up_term1 by blast
    
  lemma sift_up_invar_term2: "\<lbrakk>sift_up_invar xs\<^sub>0 i xs; xs!i\<le>xs!parent i\<rbrakk> 
    \<Longrightarrow> is_heap xs \<and> slice_eq_mset l h xs xs\<^sub>0"
    unfolding sift_up_invar_def
    using sift_up_term2 by blast

  definition "sift_down_invar xs\<^sub>0 i xs \<equiv>
      slice_eq_mset l h xs xs\<^sub>0      
    \<and> is_heap_except_down i xs"  

  lemma sift_down_invar_step:
    assumes "sift_down_invar xs\<^sub>0 i xs"
    shows "\<lbrakk>has_rchild i; xs!i\<le>xs!lchild i; xs!lchild i \<ge> xs!rchild i\<rbrakk> \<Longrightarrow> sift_down_invar xs\<^sub>0 (lchild i) (swap xs i (lchild i))" 
      and "\<lbrakk>has_rchild i; xs!i\<le>xs!rchild i; xs!lchild i \<le> xs!rchild i\<rbrakk> \<Longrightarrow> sift_down_invar xs\<^sub>0 (rchild i) (swap xs i (rchild i))"
      and "\<lbrakk>has_lchild i; \<not>has_rchild i; xs!i\<le>xs!lchild i\<rbrakk> \<Longrightarrow> sift_down_invar xs\<^sub>0 (lchild i) (swap xs i (lchild i))" 
    using assms unfolding sift_down_invar_def
    by (auto simp: sift_down_lemma_left sift_down_lemma_right sift_down_lemma_left_no_right_child)

  thm sift_down_init (*xxx, ctd here: we need to initialize from heapsort loop invariant*)
  lemma sift_down_invar_init: 
    assumes "is_heap xs" "Suc l < h" 
    shows "heap_range_context.sift_down_invar l (h-Suc 0) (swap xs l (h-Suc 0)) l (swap xs l (h-Suc 0))"
  proof -
    interpret N: heap_range_context l "h-Suc 0" using assms shrink_heap_context by auto
    show ?thesis using sift_down_init assms unfolding N.sift_down_invar_def 
      by (auto simp: sift_down_init)
      
  qed  

  
  definition "heapify_btu_invar xs\<^sub>0 l' xs \<equiv>
      slice_eq_mset l h xs xs\<^sub>0      
    \<and> is_heap_btu l' xs"
  
  definition "sift_down_btu_invar xs\<^sub>0 l' i xs \<equiv> 
      slice_eq_mset l h xs xs\<^sub>0      
    \<and> is_heap_except_down_btu l' i xs"
    
    
          
end  

interpretation singleton_heap_context: heap_range_context l "(Suc l)"
  by unfold_locales auto

lemma singleton_no_relatives[simp, intro!]:
  "\<not>singleton_heap_context.has_parent l i"  
  "\<not>singleton_heap_context.has_lchild l i"  
  "\<not>singleton_heap_context.has_rchild l i"  
  unfolding singleton_heap_context.heap_context_defs 
  by auto
  
lemma singleton_heap: "l<length xs \<Longrightarrow> singleton_heap_context.is_heap l xs"  
  unfolding singleton_heap_context.is_heap_def
  by auto

  
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
  


    
context heap_range_context begin  
  
  definition "sift_down i xs \<equiv> doN {
    ASSERT (in_heap i \<and> i<length xs);
    (xs,i,_) \<leftarrow> WHILEIT (\<lambda>(xs,i,ctd). in_heap i) 
      (\<lambda>(xs,i,ctd). has_rchild i \<and> ctd) 
      (\<lambda>(xs,i,ctd). doN {
        lc \<leftarrow> mop_list_get xs (lchild i);
        rc \<leftarrow> mop_list_get xs (rchild i);
        v \<leftarrow> mop_list_get xs i;
      
        if lc < rc then
          if v < rc then doN {
            xs \<leftarrow> mop_list_swap xs i (rchild i);
            RETURN (xs,rchild i,True)
          } else RETURN (xs,i,False)
        else if v < lc then doN {
          xs \<leftarrow> mop_list_swap xs i (lchild i);
          RETURN (xs,lchild i,True)
        } else RETURN (xs,i,False)
      }) 
    (xs,i,True);
  
    ASSERT (in_heap i);
    ASSERT (has_lchild i \<longrightarrow> lchild i < length xs);
    
    if has_lchild i \<and> xs!i < xs!lchild i then
      mop_list_swap xs i (lchild i)
    else 
      RETURN xs
      
  }"

  lemma in_heap_len_bound: "in_heap i \<Longrightarrow> h\<le>length xs \<Longrightarrow> i<length xs"
    using in_heap_bounds(2) less_le_trans by blast
  
    
    
  lemma sift_down_btu_correct:
    assumes "heapify_btu_invar xs\<^sub>0 l' xs" "l<l'"
    shows "sift_down (l'-Suc 0) xs \<le> SPEC (\<lambda>xs'. heapify_btu_invar xs\<^sub>0 (l'-Suc 0) xs')"
    unfolding sift_down_def 
    apply (refine_vcg WHILEIT_rule_amend_invar[where 
      I="\<lambda>(xs,i,ctd). 
          sift_down_btu_invar xs\<^sub>0 (l'-Suc 0) i xs 
          \<and> h\<le>length xs
          \<and> (\<not>ctd \<longrightarrow> has_rchild i \<and> xs!i\<ge>xs!lchild i \<and> xs!i\<ge>xs!rchild i)"
      and
      R = "measure (\<lambda>(xs,i,ctd). (if ctd then 1 else 0) + h - i)"    
    ]) 
    using assms
    unfolding heapify_btu_invar_def sift_down_btu_invar_def
    apply (all \<open>(auto simp: in_heap_len_bound diff_less_mono2; fail)?\<close>)
    subgoal unfolding is_heap_btu_def by (auto intro!: in_heapI)
    subgoal unfolding is_heap_btu_def by auto
    subgoal using btu_sift_down_init by auto
    subgoal unfolding is_heap_btu_def by auto
    subgoal by (auto simp: btu_heapify_down_right)
    subgoal by (simp add: diff_less_mono2 less_Suc_eq)
    subgoal by (simp add: diff_less_mono less_imp_le)
    subgoal by (auto simp add: btu_heapify_down_left)
    subgoal by (simp add: diff_less_mono2 less_Suc_eq)
    subgoal by (simp add: diff_less_mono less_imp_le)
    subgoal 
      apply clarsimp
      by (meson btu_heapify_down_left_no_right_child btu_sift_down_term1 lchild_of_no_rchild_term less_le_not_le)
    subgoal 
      apply clarsimp
      using btu_sift_down_term1 btu_sift_down_term2 btu_sift_down_term3 not_less by blast
    done    
  

  lemma sift_down_restore_correct: 
    assumes A: "l<h" "sift_down_invar xs\<^sub>0 l xs"
    shows "sift_down l xs \<le> SPEC (\<lambda>xs'. slice_eq_mset l h xs' xs\<^sub>0 \<and> is_heap xs')"  
    unfolding sift_down_def
    apply (refine_vcg WHILEIT_rule_amend_invar[where 
      I="\<lambda>(xs,i,ctd). 
          sift_down_invar xs\<^sub>0 i xs 
          \<and> h\<le>length xs
          \<and> (\<not>ctd \<longrightarrow> has_rchild i \<and> xs!i\<ge>xs!lchild i \<and> xs!i\<ge>xs!rchild i)"
      and
      R = "measure (\<lambda>(xs,i,ctd). (if ctd then 1 else 0) + h - i)"    
    ]) 
    apply (all \<open>(auto simp: in_heap_len_bound diff_less_mono2 A sift_down_invar_step; fail)?\<close>)
    apply clarsimp_all
    subgoal using A unfolding sift_down_invar_def is_heap_except_down_def by auto
    subgoal using A unfolding sift_down_invar_def is_heap_except_down_def by auto
    subgoal by (simp add: diff_less_mono2 less_SucI)
    subgoal by (simp add: Suc_diff_le less_imp_le)
    subgoal by (simp add: diff_less_mono2 less_Suc_eq)
    subgoal by (simp add: Suc_diff_le less_imp_le)
    subgoal unfolding sift_down_invar_def by simp
    subgoal by (meson lchild_of_no_rchild_term less_imp_le not_le sift_down_invar_def sift_down_lemma_left_no_right_child sift_down_term1)
    subgoal unfolding sift_down_invar_def by simp
    subgoal unfolding sift_down_invar_def by (meson leI sift_down_term1 sift_down_term2 sift_down_term3)
    done
    
      
    
    
    
    
  text \<open>Deferred swap optimization\<close>
  definition "sift_down1 i xs \<equiv> doN {
    ASSERT (in_heap i);
    v \<leftarrow> mop_list_get xs i;
    (xs,i,_) \<leftarrow> WHILEIT (\<lambda>(xs,i,ctd). in_heap i) (\<lambda>(xs,i,ctd). has_rchild i \<and> ctd) (\<lambda>(xs,i,ctd). doN {
      lc \<leftarrow> mop_list_get xs (lchild i);
      rc \<leftarrow> mop_list_get xs (rchild i);
    
      if lc < rc then
        if v < rc then doN {
          t \<leftarrow> mop_list_get xs (rchild i);
          xs \<leftarrow> mop_list_set xs i t;
          RETURN (xs,rchild i,True)
        } else RETURN (xs,i,False)
      else if v < lc then doN {
        t \<leftarrow> mop_list_get xs (lchild i);
        xs \<leftarrow> mop_list_set xs i t;
        RETURN (xs,lchild i,True)
      } else RETURN (xs,i,False)
    }) (xs,i,True);

    ASSERT (in_heap i);
    ASSERT (has_lchild i \<longrightarrow> lchild i < length xs);
    
    xs \<leftarrow> (if has_lchild i \<and> v < xs!lchild i then doN {
      t \<leftarrow> mop_list_get xs (lchild i);
      xs \<leftarrow> mop_list_set xs i t;
      xs \<leftarrow> mop_list_set xs (lchild i) v;
      RETURN xs
    } else doN {
      xs \<leftarrow> mop_list_set xs i v;
      RETURN xs
    });

  
    RETURN xs
  }"


  definition "swap_opt_rel v \<equiv> {((xs,i,ctd),(xs',i',ctd')). xs' = xs[i:=v] \<and> i<length xs \<and> i'=i \<and> ctd'=ctd }"
  
  
  lemma sift_down1_refine: "sift_down1 i\<^sub>0 xs \<le>\<Down>Id (sift_down i\<^sub>0 xs)"
    unfolding sift_down1_def sift_down_def
    apply (intro refine0)
    subgoal by simp
    apply (rule specify_left_pw, simp)
    subgoal for v
      apply (rule refine)
      apply (rule WHILEIT_refine[where R="swap_opt_rel v"])
      subgoal by (auto simp: swap_opt_rel_def)
      subgoal by (auto simp: swap_opt_rel_def)
      subgoal by (auto simp: swap_opt_rel_def)
      subgoal for s s'
        apply (clarsimp simp: swap_opt_rel_def split del: if_split)
        apply (intro refine0 if_refine)
        apply (all \<open>(auto; auto simp: swap_def;fail)?\<close>)
        done
      subgoal for s s'
        supply [simp del] = conc_Id  
        apply (clarsimp simp: swap_opt_rel_def split del: if_split)
        apply (intro refine0 if_refine)
        apply (all \<open>(auto; auto simp: swap_def;fail)?\<close>)
        (*apply simp apply refine_rcg
        apply (auto simp: swap_def)*)
        done
      done
    done
  

    
  text \<open>Index shift optimization\<close>
  
  definition "ihs_opt_rel \<equiv> {((xs,i,ctd),(xs',i',ctd')). xs' = xs \<and> i' = i+l \<and> ctd'=ctd }"
  
  definition "sift_down2 i\<^sub>0 xs \<equiv> doN {
    ASSERT (l\<le>i\<^sub>0);
    let i = i\<^sub>0 - l;
    ASSERT (l+i<h);
    v \<leftarrow> mop_list_get xs (l+i);
    ASSERT (l<h);
    
    (xs,i,_) \<leftarrow> WHILEIT (\<lambda>(xs,i,ctd). i<h-l) (\<lambda>(xs,i,ctd). i<(h-l-1) div 2 \<and> ctd) (\<lambda>(xs,i,ctd). doN {
      ASSERT (l+i<h \<and> l+2*i+2 < h);
      let lci = 2*i+1;
      let rci = 2*i+2;
      lc \<leftarrow> mop_list_get xs (l + lci);
      rc \<leftarrow> mop_list_get xs (l + rci);
    
      if lc < rc then
        if v < rc then doN {
          t \<leftarrow> mop_list_get xs (l + rci);
          xs \<leftarrow> mop_list_set xs (l + i) t;
          RETURN (xs,rci,True)
        } else RETURN (xs,i,False)
      else if v < lc then doN {
        t \<leftarrow> mop_list_get xs (l + lci);
        xs \<leftarrow> mop_list_set xs (l + i) t;
        RETURN (xs,lci,True)
      } else RETURN (xs,i,False)
    }) (xs,i,True);
    
    ASSERT (l<h \<and> l+i<h \<and> ( i < (h-l) div 2 \<longrightarrow> l + 2*i+1 < h \<and> l + 2*i+1 < length xs));
    
    xs \<leftarrow> (if i < (h-l) div 2 \<and> v < xs!(l + 2*i+1) then doN {
      t \<leftarrow> mop_list_get xs (l + 2*i+1);
      xs \<leftarrow> mop_list_set xs (l + i) t;
      xs \<leftarrow> mop_list_set xs (l + 2*i+1) v;
      RETURN xs
    } else doN {
      xs \<leftarrow> mop_list_set xs (l+i) v;
      RETURN xs
    });

  
    RETURN xs
  }"
    
  lemma ihs_opt_rel_alt: "((xs,i,ctd), (xs',i',ctd'))\<in>ihs_opt_rel \<longleftrightarrow> xs'=xs \<and> (i',i)\<in>idx_shift_rel l \<and> ctd'=ctd"
    unfolding ihs_opt_rel_def idx_shift_rel_def by auto
  
  lemma idx_shift_adjust:
    assumes "(i',i)\<in>idx_shift_rel l"
    shows 
      "in_heap i' \<longleftrightarrow> i<h-l"
      "has_lchild i' \<longleftrightarrow> i<(h-l) div 2"
      "has_rchild i' \<longleftrightarrow> i<(h-l-1) div 2"
      "lchild i' = 2*i+1+l"
      "rchild i' = 2*i+2+l"
      "i+l = i'"
    using assms
    thm lchild_ihs
    unfolding idx_shift_rel_def 
      in_heap_def 
      has_rchild_def rchild_def
      has_lchild_def lchild_def
    by auto
    

  lemma sift_down2_refine: "sift_down2 i xs \<le> \<Down>Id (sift_down1 i xs)"
    unfolding sift_down1_def sift_down2_def
    apply (rewrite at "let i=i-l in _" Let_def)
    apply (rewrite at "let _=2*_+1 in _" Let_def)
    apply (rewrite at "let _=2*_+2 in _" Let_def)
    apply (simp del: conc_Id cong: if_cong)
    apply refine_rcg
    supply [refine_dref_RELATES] = RELATESI[of ihs_opt_rel]  
    apply refine_dref_type
    apply (clarsimp_all simp: ihs_opt_rel_alt idx_shift_adjust algebra_simps)
    subgoal unfolding in_heap_def by auto
    subgoal unfolding in_heap_def idx_shift_rel_def by auto
    subgoal by auto
    subgoal unfolding idx_shift_rel_def by auto
    subgoal unfolding idx_shift_rel_def by auto
    subgoal by auto
    done

    
end        
    
concrete_definition sift_down3 is heap_range_context.sift_down2_def
    
context heap_range_context begin  

  lemma sift_down3_full_refine: "sift_down3 l h i xs \<le> sift_down i xs"
  proof -
    note sift_down3.refine[OF heap_range_context_axioms, symmetric, THEN meta_eq_to_obj_eq]
    also note sift_down2_refine 
    also note sift_down1_refine 
    finally show ?thesis by simp
  qed

  lemmas sift_down3_btu_correct = order_trans[OF sift_down3_full_refine sift_down_btu_correct]
  lemmas sift_down3_restore_correct = order_trans[OF sift_down3_full_refine sift_down_restore_correct]
  
  definition "heapify_btu xs\<^sub>0 \<equiv> doN {
    ASSERT(h>0);
    (xs,l') \<leftarrow> WHILEIT (\<lambda>(xs,l'). heapify_btu_invar xs\<^sub>0 l' xs \<and> l'\<ge>l) 
      (\<lambda>(xs,l'). l'>l) 
      (\<lambda>(xs,l'). doN {
        ASSERT (l'>0);
        let l'=l'-1;
        xs \<leftarrow> sift_down3 l h l' xs;
        RETURN (xs,l')
      })
      (xs\<^sub>0,h-1);
    RETURN xs
  }"    
    
  lemma heapify_btu_correct: "\<lbrakk> l<h; h\<le>length xs\<^sub>0 \<rbrakk> \<Longrightarrow> heapify_btu xs\<^sub>0 \<le> SPEC (\<lambda>xs. slice_eq_mset l h xs xs\<^sub>0 \<and> is_heap xs)"
    unfolding heapify_btu_def
    apply simp
    apply (refine_vcg WHILEIT_rule[where R="measure snd"] sift_down3_btu_correct)
    apply (all \<open>(auto;fail)?\<close>)
    apply clarsimp_all (* Required to get rid of local variables that will obfuscate locale abbreviations! *)
    subgoal by (simp add: heapify_btu_invar_def btu_heapify_init)
    subgoal by (auto simp: heapify_btu_invar_def)
    subgoal by (auto simp: heapify_btu_invar_def btu_heapify_term)
    done
    
    
end

concrete_definition heapify_btu1 is heap_range_context.heapify_btu_def

context heap_range_context begin  
  lemmas heapify_btu1_correct = heapify_btu_correct[unfolded heapify_btu1.refine[OF heap_range_context_axioms]]
end

definition "heapsort l h\<^sub>0 xs\<^sub>0 \<equiv> doN {
  ASSERT (l\<le>h\<^sub>0);
  if h\<^sub>0-l > 1 then doN {
    xs \<leftarrow> heapify_btu1 l h\<^sub>0 xs\<^sub>0;
    
    (xs,h)\<leftarrow>WHILEIT (\<lambda>(xs,h). 
        l<h \<and> h\<le>h\<^sub>0 
      \<and> heap_range_context.is_heap l h xs
      \<and> slice_eq_mset l h\<^sub>0 xs xs\<^sub>0
      \<and> sorted (slice h h\<^sub>0 xs)
      \<and> (\<forall>a\<in>set (slice l h xs). \<forall>b\<in>set (slice h h\<^sub>0 xs). a\<le>b)
    ) 
      (\<lambda>(xs,h). Suc l < h) 
      (\<lambda>(xs,h). doN {
        ASSERT (h>0);
        xs \<leftarrow> mop_list_swap xs l (h-1);
        xs \<leftarrow> sift_down3 l (h-1) l xs;
        RETURN (xs,h-1)
      })
      (xs,h\<^sub>0);
    
    RETURN xs
  } else
    RETURN xs\<^sub>0
}"

  
lemma heapsort_correct:
  assumes "l\<le>h\<^sub>0" "h\<^sub>0\<le>length xs\<^sub>0"
  shows "heapsort l h\<^sub>0 xs\<^sub>0 \<le> SPEC (\<lambda>xs. slice_eq_mset l h\<^sub>0 xs xs\<^sub>0 \<and> sorted (slice l h\<^sub>0 xs))"
proof -
  interpret initial: heap_range_context l h\<^sub>0 by unfold_locales fact


  thm heap_range_context.sift_down_restore_correct[of l _ xs\<^sub>0]
  
  show ?thesis  
    using assms unfolding heapsort_def
    apply (refine_vcg WHILEIT_rule[where R="measure snd"] initial.heapify_btu1_correct )
    apply (all \<open>(auto dest: slice_eq_mset_eq_length;fail)?\<close>)
    
    apply clarsimp
    subgoal premises prems for xs\<^sub>1 xs h proof -
      (* TODO: This is the argument that swapping the max-element to the end will preserve the
          sortedness criteria. Though apparently simple, the reasoning seems to be much too complex here.
          Try to improve on that!
      *)
      interpret heap_range_context l h using prems by (unfold_locales) auto
      interpret N: heap_range_context l "h-Suc 0" using prems by (unfold_locales) auto
      
      from prems have 
        [simp]: "length xs = length xs\<^sub>0" 
        and [simp, arith]: "h\<^sub>0 \<le> length xs\<^sub>0"
      by (auto simp: slice_eq_mset_eq_length)
      
      {
        fix xs'
        assume A: "slice_eq_mset l (h - Suc 0) xs' (swap xs l (h - Suc 0))"  
        hence "slice_eq_mset l h\<^sub>0 xs' (swap xs l (h - Suc 0))"
          apply (rule slice_eq_mset_subslice)
          using prems by auto
        from this[symmetric] have "slice_eq_mset l h\<^sub>0 xs' xs"  
          apply -
          apply (drule slice_eq_mset_swap(2)[THEN iffD1, rotated -1])
          using prems by (auto dest: slice_eq_mset_sym)
        also note \<open>slice_eq_mset l h\<^sub>0 xs xs\<^sub>0\<close>   
        finally have G1: "slice_eq_mset l h\<^sub>0 xs' xs\<^sub>0" .

        note [simp] = slice_eq_mset_eq_length[OF G1]
        
        have [simp]: "slice (h - Suc 0) h\<^sub>0 xs' = (xs'!(h-Suc 0))#slice h h\<^sub>0 xs'"
          apply (rule slice_extend1_left)
          using prems by (auto)
        
          
        have "slice h h\<^sub>0 xs' = slice h h\<^sub>0 (swap xs l (h - Suc 0))"
          apply (rule slice_eq_mset_eq_outside(2)[OF A]) using prems by auto
        also have "\<dots> = slice h h\<^sub>0 xs" 
          by (metis Suc_lessD atLeastLessThan_iff leI le_antisym le_zero_eq nat_less_le nz_le_conv_less \<open>Suc l < h\<close> slice_swap_outside)
        finally have [simp]: "slice h h\<^sub>0 xs' = slice h h\<^sub>0 xs" .
          
        have [arith,simp]: "h - Suc 0 < length xs\<^sub>0" "l<length xs\<^sub>0" using prems by (auto)
        have [simp]: "xs' ! (h - Suc 0) = xs!l" 
          using slice_eq_mset_nth_outside[OF A, of "h-Suc 0"] 
          by auto
          
        have "xs!l \<in> set (slice l h xs)" using prems by (auto simp: set_slice_conv)
        then have G2: "sorted (slice (h - Suc 0) h\<^sub>0 xs')" 
          using prems 
          by auto

        have [simp]: "slice l (h - Suc 0) (swap xs l (h - Suc 0)) = xs!(h-Suc 0)#(slice (Suc l) (h-Suc 0) xs)"
          apply (rule nth_equalityI)
          apply (auto simp: nth_list_update slice_nth swap_nth Suc_diff_Suc \<open>Suc l < h\<close>)
          done
          
        have "in_heap (h - Suc 0)"
          unfolding in_heap_def apply simp
          using \<open>Suc l < h\<close> by linarith
        
        have G3: "\<forall>a \<in> set (slice l (h - Suc 0) xs'). \<forall>b \<in> set (slice (h - Suc 0) h\<^sub>0 xs'). a\<le>b" 
          thm slice_eq_mset_set_inside[OF A]
          apply (simp add: slice_eq_mset_set_inside[OF A])
          using \<open>\<forall>x\<in>set (slice l h xs). \<forall>_\<in>_. _\<close>
          apply (auto simp: set_slice_conv root_greatest[OF \<open>is_heap xs\<close> \<open>in_heap (h-Suc 0)\<close>])
          subgoal using N.ran_not_empty \<open>in_heap (h - Suc 0)\<close> in_heap_bounds(2) by blast  
          subgoal for j 
            apply (subgoal_tac "in_heap j")
            using root_greatest[OF \<open>is_heap xs\<close>, of j] apply blast
            unfolding in_heap_def by simp
          subgoal by (metis Suc_le_lessD diff_le_self less_imp_le less_le_trans)
          done
          
        note G1 G2 G3
      } note aux=this
      note rl = N.sift_down3_restore_correct[OF _ sift_down_invar_init[OF \<open>is_heap xs\<close> \<open>Suc l < h\<close>]]
      
      show ?thesis
        apply (refine_vcg rl)
        using \<open>Suc l < h\<close> \<open>h\<le>h\<^sub>0\<close>
        apply (auto simp: aux)
        thm prems
        done
        
    qed
    apply clarsimp
    subgoal premises prems for xs\<^sub>1 xs h
    proof -
      have [simp]: "h=l+1" using prems by auto
    
      from prems have [simp]: "length xs = length xs\<^sub>0"
        and [simp, arith]: "l<length xs\<^sub>0" "h<length xs\<^sub>0"
        by (auto dest: slice_eq_mset_eq_length)
      
      have "set (slice l (Suc l) xs) = {xs!l}" by simp
      
      show ?thesis using prems
        by (auto simp: slice_split_hd)
    qed
    subgoal
      by (metis Misc.slice_len One_nat_def add.right_neutral add_Suc_right add_diff_cancel_left' initial.ran_not_empty leI le_less le_neq_implies_less nat_in_between_eq(2) sorted01)
    done
    
qed
                                                                                    

sepref_register sift_down3
sepref_def sift_down_impl is "uncurry3 sift_down3" :: "size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k *\<^sub>a arr_assn\<^sup>d \<rightarrow>\<^sub>a arr_assn"
  unfolding sift_down3_def
  apply (annot_snat_const "TYPE (size_t)")
  apply (rewrite in "if \<hole> then _ else _" short_circuit_conv)
  apply sepref_dbg_keep (* TODO: Takes loooong *)
  done


  
term heapify_btu1

sepref_register heapify_btu1
sepref_def heapify_btu_impl is "uncurry2 heapify_btu1" :: "size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k *\<^sub>a arr_assn\<^sup>d \<rightarrow>\<^sub>a arr_assn"
  unfolding heapify_btu1_def
  apply (annot_snat_const "TYPE (size_t)")
  by sepref
  
sepref_register heapsort  
sepref_def heapsort_impl is "uncurry2 heapsort" :: "size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k *\<^sub>a arr_assn\<^sup>d \<rightarrow>\<^sub>a arr_assn"
  unfolding heapsort_def
  apply (rewrite at "sift_down3 _ _ \<hole> _" fold_COPY)
  apply (annot_snat_const "TYPE (size_t)")
  by sepref
  
term heapsort  
  
export_llvm sift_down_impl heapify_btu_impl heapsort_impl

oops  
xxx, ctd here:
  clean up. 
    sorting/ folder
    Sorting_Setup.thy
    Heapsort.thy
    Insertion_Sort.thy
    Introsort.thy
     
  then: Check current introsort quadratic degeneration on sorted data (should not happen!)
    Assemble introsort
    Benchmark heapsort and insertion-sort implementations separately
    
    
  


  

section \<open>Count Leading Zeroes and Log2\<close>
(* TODO: Define semantics of llvm.ctlz intrinsic! *)

subsection \<open>Explicit Implementation by Loop\<close>

definition word_clz' :: "'a::len word \<Rightarrow> nat" where
  "word_clz' x \<equiv> if x=0 then 0 else word_clz x"

lemma word_clz'_eq: "x\<noteq>0 \<Longrightarrow> word_clz' x = word_clz x" 
  by (simp add: word_clz'_def)  
  
lemma of_bl_eqZ: 
  "\<lbrakk> length xs = LENGTH ('a::len0) \<rbrakk> \<Longrightarrow> (of_bl xs :: 'a word) = 0 \<longleftrightarrow> (xs = replicate LENGTH('a) False)"  
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

lemma word_clz_nonzero_max': "x\<noteq>0 \<Longrightarrow> word_clz (x::'a::len2 word) \<le> LENGTH('a) - Suc 0"
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
  

section \<open>Insertion Sort\<close>  
        

definition "is_insert xs i \<equiv> doN {
  ASSERT (i<length xs);
  x \<leftarrow> mop_list_get xs i;

  (xs,i)\<leftarrow>WHILEIT (\<lambda>(xs',i'). 
    i'\<ge>0 \<and> i'\<le>i \<and> length xs'=length xs
  \<and> (\<forall>j\<in>{0..i'}. xs'!j = xs!j)  
  \<and> (\<forall>j\<in>{i'<..i}. xs'!j = xs!(j-1) \<and> x<xs'!j)  
  \<and> (\<forall>j\<in>{i<..<length xs}. xs'!j=xs!j)
  ) 
    (\<lambda>(xs,i). i>0 \<and> xs!(i-1)>x) (\<lambda>(xs,i). doN {
      ASSERT (i>0 \<and> i<length xs);
      let xs = xs[i:=xs!(i-1)];
      let i = i-1;
      RETURN (xs,i)
    }) (xs,i);

  xs \<leftarrow> mop_list_set xs i x;  
  
  RETURN xs
}"

definition "is_insert_spec xs i xs' \<equiv> 
  \<exists>i'\<le>i.
    i<length xs
  \<and> (length xs' = length xs) 
  \<and> (\<forall>j\<in>{0..<i'}. xs'!j=xs!j)
  \<and> (xs'!i' = xs!i)
  \<and> (\<forall>j\<in>{i'<..i}. xs'!j = xs!(j-1) \<and> xs!i<xs'!j)
  \<and> (\<forall>j\<in>{i<..<length xs}. xs'!j = xs!j)
  \<and> (i'>0 \<longrightarrow> \<not>(xs!i < xs'!(i'-1)) )
  "


lemma is_insert_correct: "i<length xs \<Longrightarrow> is_insert xs i \<le> SPEC (is_insert_spec xs i)"
  unfolding is_insert_def
  apply (refine_vcg WHILEIT_rule[where R="measure snd"])
  apply clarsimp_all
  apply (auto simp: nth_list_update') [2]
  apply (metis Suc_lessI Suc_pred greaterThanAtMost_iff)

  subgoal for xs' i'
    unfolding is_insert_spec_def
    apply (rule exI[where x=i']) 
    by auto
    
  done

  
lemma intv_split_auxE:  
  fixes k N :: nat
  assumes "k<N" "i'\<le>i" "i<N"
  obtains "k\<in>{0..<i'}" | "k=i'" | "k\<in>{i'<..i}" | "k\<in>{i<..<N}"  
  using assms
  by fastforce
  
  
  
lemma is_insert_spec_imp_sorted:
  "\<lbrakk>is_insert_spec xs i xs'; sorted (take i xs)\<rbrakk> 
    \<Longrightarrow> sorted (take (i+1) xs')"  
  (* TODO: Clean up this mess! *)
  apply (subgoal_tac "i<length xs")
  unfolding sorted_iff_nth_mono_less 
  apply auto
  unfolding is_insert_spec_def
  apply auto
  subgoal by (smt greaterThanAtMost_iff le_less le_less_trans less_Suc_eq_0_disj nat_Suc_less_le_imp nat_le_Suc_less_imp nz_le_conv_less)
  subgoal for k1 k2 i'
    apply (rule intv_split_auxE[of k1 "length xs" i' i])
    apply simp_all
    apply (rule intv_split_auxE[of k2 "length xs" i' i])
    apply simp_all [3]
    apply simp
    apply simp
    apply (metis leD less_le_trans linorder_le_less_linear linorder_neqE_nat nat_le_Suc_less_imp nz_le_conv_less zero_order(3))
    apply simp
    apply (meson greaterThanLessThan_iff not_less_eq)
    by (metis greaterThanAtMost_iff less_imp_le nat_Suc_less_le_imp)
  done    

lemma is_insert_spec_split: "is_insert_spec xs i xs' \<Longrightarrow> (\<exists>i'\<le>i. 
  xs' = take i' xs @ xs!i # drop i' (take i xs) @ drop (i+1) xs)"
  unfolding is_insert_spec_def
  apply clarify
  subgoal for i'
    apply (rule exI[where x=i'])
    apply (simp add: list_eq_iff_nth_eq)
    apply (clarsimp simp: nth_append nth_Cons split: nat.splits)
    apply (safe; clarsimp?)
    subgoal for j k
      by (metis One_nat_def Suc_le_eq add.commute add_Suc_right add_diff_cancel_left' add_diff_inverse_nat greaterThanAtMost_iff less_diff_conv plus_1_eq_Suc zero_less_Suc)
    subgoal by (metis add_Suc leI le_add_diff_inverse2)
    done
  done
  
  
lemma is_insert_spec_imp_mset_eq:
  assumes A: "is_insert_spec xs i xs'"  
  shows "mset xs' = mset xs"
proof -
  from A have L: "i<length xs"
    unfolding is_insert_spec_def by blast

  from is_insert_spec_split[OF A] obtain i' where
    I': "i'\<le>i" 
    and XS'_EQ: "xs' = take i' xs @ xs ! i # drop i' (take i xs) @ drop (i + 1) xs"
    by blast  
  
  have XS_EQ: "xs = take i' xs @ drop i' (take i xs) @ xs!i # drop (i + 1) xs"  
    using L I'
    apply auto 
    by (metis atd_lem drop_Suc_nth drop_take_drop_unsplit)  
  
  show ?thesis
    apply (rewrite in "\<hole> = _" XS'_EQ)
    apply (rewrite in "_ = \<hole>" XS_EQ)
    by (auto)  
    
qed    


definition "sort_one_more_spec xs i \<equiv> doN {
    ASSERT (i<length xs \<and> sorted (take i xs)); 
    SPEC (\<lambda>xs'. mset xs' = mset xs \<and> sorted (take (i+1) xs'))
  }"  

  
  
lemma is_insert_sorts_one_more[param_fo, THEN nres_relD,refine]: 
  "(is_insert, sort_one_more_spec) 
      \<in> \<langle>Id\<rangle>list_rel \<rightarrow> nat_rel \<rightarrow> \<langle>\<langle>Id\<rangle>list_rel\<rangle>nres_rel"
  apply (intro fun_relI nres_relI)    
  using is_insert_correct 
        is_insert_spec_imp_sorted is_insert_spec_imp_mset_eq
  unfolding sort_one_more_spec_def
  by (simp add: pw_le_iff refine_pw_simps; blast)

    
definition "insertion_sort_whole xs \<equiv> doN {
  (xs,_)\<leftarrow>WHILEIT (\<lambda>(xs',i). 
    i\<le>length xs' \<and> length xs'=length xs \<and> mset xs' = mset xs \<and> sorted (take i xs')) 
    (\<lambda>(xs,i). i<length xs) 
    (\<lambda>(xs,i). doN {
      xs \<leftarrow> sort_one_more_spec xs i;
      ASSERT (i<length xs);
      let i=i+1;
      RETURN (xs,i)
    }) (xs,0);
  RETURN xs
}"  

lemma insertion_sort_whole_correct: 
  "insertion_sort_whole xs \<le> SPEC (sort_spec xs)"
  unfolding insertion_sort_whole_def sort_one_more_spec_def sort_spec_def
  apply (refine_vcg 
    WHILEIT_rule[where R="measure (\<lambda>(_,i). length xs - i)"])           
  apply (auto dest: mset_eq_length)
  done

lemma insertion_sort_whole_refine: 
  "(insertion_sort_whole, \<lambda>xs. SPEC (sort_spec xs)) \<in> \<langle>Id\<rangle>list_rel \<rightarrow> \<langle>\<langle>Id\<rangle>list_rel\<rangle>nres_rel"
  using insertion_sort_whole_correct
  apply (intro fun_relI nres_relI)
  by auto  
  
definition "insertion_sort_whole2 xs \<equiv> doN {
  (xs,_)\<leftarrow>WHILEIT (\<lambda>(xs',i). i\<le>length xs' \<and> mset xs' = mset xs \<and> sorted (take i xs')) 
    (\<lambda>(xs,i). i<length xs) 
    (\<lambda>(xs,i). doN {
      xs \<leftarrow> is_insert xs i;
      ASSERT (i<length xs);
      let i=i+1;
      RETURN (xs,i)
    }) (xs,0);
  RETURN xs
}"  

lemma insertion_sort_whole2_refines: 
  "(insertion_sort_whole2, insertion_sort_whole) \<in> \<langle>Id\<rangle>list_rel \<rightarrow> \<langle>\<langle>Id\<rangle>list_rel\<rangle>nres_rel"
  unfolding insertion_sort_whole2_def insertion_sort_whole_def
  apply (refine_rcg)
  apply refine_dref_type
  by auto
  

definition "is_insert2 xs i \<equiv> doN {
  x \<leftarrow> mop_list_get xs i;

  (xs,i)\<leftarrow>monadic_WHILEIT (\<lambda>(xs',i'). True) 
    (\<lambda>(xs,i). if i>0 then doN { y\<leftarrow>mop_list_get xs (i-1); RETURN (y>x) } else RETURN False) 
    (\<lambda>(xs,i). doN {
      ASSERT (i>0 \<and> i-1<length xs \<and> i<length xs);
      let xs = xs[i:=xs!(i-1)];
      let i = i-1;
      RETURN (xs,i)
    }) (xs,i);

  xs \<leftarrow> mop_list_set xs i x;  
  
  RETURN xs
}"
  
lemma is_insert2_refine: "\<lbrakk>(xs,xs')\<in>\<langle>Id\<rangle>list_rel; (i,i')\<in>Id\<rbrakk> \<Longrightarrow> is_insert2 xs i \<le> \<Down>Id (is_insert xs' i')"
  unfolding is_insert2_def is_insert_def
  apply refine_rcg
  apply refine_dref_type
  apply simp_all
  apply refine_vcg
  apply auto
  done
  
definition "is_insert3 xs l i \<equiv> doN {
  x \<leftarrow> mop_list_get xs i;

  (xs,i)\<leftarrow>monadic_WHILEIT (\<lambda>(xs',i'). True) 
    (\<lambda>(xs,i). if i>l then doN { y\<leftarrow>mop_list_get xs (i-1); RETURN (y>x) } else RETURN False) 
    (\<lambda>(xs,i). doN {
      ASSERT (i>0 \<and> i-1<length xs \<and> i<length xs);
      let xs = xs[i:=xs!(i-1)];
      let i = i-1;
      RETURN (xs,i)
    }) (xs,i);

  xs \<leftarrow> mop_list_set xs i x;  
  
  RETURN xs
}"


  
    
lemma is_insert3_refine: "\<lbrakk> (xs,xs')\<in>slice_rel xs\<^sub>0 l h; (i,i')\<in>idx_shift_rel l; i<h \<rbrakk> \<Longrightarrow> is_insert3 xs l i \<le>\<Down>(slice_rel xs\<^sub>0 l h) (is_insert2 xs' i')"
  unfolding is_insert2_def is_insert3_def
  supply [refine_dref_RELATES] = 
    RELATESI[of "slice_rel xs\<^sub>0 l h"] 
    RELATESI[of "slice_rel xs\<^sub>0 l h \<times>\<^sub>r idx_shift_rel l"] 
  apply (refine_rcg slice_nth_refine' slice_upd_refine')
  apply refine_dref_type
  apply (all \<open>(simp; fail)?\<close>)
  subgoal by (auto simp: idx_shift_rel_def)
  subgoal by (auto simp: idx_shift_rel_def)
  subgoal by (auto simp: idx_shift_rel_def)
  subgoal by (auto simp: idx_shift_rel_def slice_rel_def in_br_conv)
  subgoal by (auto simp: idx_shift_rel_def slice_rel_def in_br_conv)

  subgoal by (auto simp: slice_rel_def in_br_conv slice_nth idx_shift_rel_def slice_upd algebra_simps)
  done

lemma is_insert3_refine1: "\<lbrakk> (xs,xs')\<in>slice_rel xs\<^sub>0 l h; (i,i')\<in>idx_shift_rel l; i<h \<rbrakk> \<Longrightarrow> is_insert3 xs l i \<le>\<Down>(slice_rel xs\<^sub>0 l h) (is_insert xs' i')"
  using is_insert3_refine is_insert2_refine  
  by (fastforce simp: pw_le_iff refine_pw_simps)  

definition "insertion_sort xs l h \<equiv> doN {
  (xs,_)\<leftarrow>WHILET  
    (\<lambda>(xs,i). i<h) 
    (\<lambda>(xs,i). doN {
      xs \<leftarrow> is_insert3 xs l i;
      ASSERT (i<h);
      let i=i+1;
      RETURN (xs,i)
    }) (xs,l);
  RETURN xs
}"  
  
lemma insertion_sort_refines: "\<lbrakk> (xs,xs')\<in>slice_rel xs\<^sub>0 l h \<rbrakk> \<Longrightarrow> insertion_sort xs l h \<le>\<Down>(slice_rel xs\<^sub>0 l h) (insertion_sort_whole2 xs')"  
  unfolding insertion_sort_def insertion_sort_whole2_def  
  apply (refine_rcg is_insert3_refine1)
  supply [refine_dref_RELATES] = 
    RELATESI[of "slice_rel xs\<^sub>0 l h"] 
    RELATESI[of "slice_rel xs\<^sub>0 l h \<times>\<^sub>r idx_shift_rel l"] 
  apply refine_dref_type        
  apply auto
  apply (auto simp: idx_shift_rel_def slice_rel_def in_br_conv)
  done

lemma insertion_sort_correct: "(insertion_sort, slice_sort_spec)\<in>Id \<rightarrow> Id \<rightarrow> Id \<rightarrow> \<langle>Id\<rangle>nres_rel"
  unfolding slice_sort_spec_def 
  apply refine_vcg
  (* TODO: Can we do this reasoning chain more beautiful? *)
  apply (rule order_trans) apply (rule insertion_sort_refines[OF slice_in_slice_rel]; simp)
  apply (rule order_trans) apply (rule conc_fun_mono[THEN monoD]) apply (rule insertion_sort_whole2_refines[param_fo, THEN nres_relD, simplified, OF refl])
  apply (rule order_trans) apply (rule conc_fun_mono[THEN monoD]) apply (rule insertion_sort_whole_correct)
  apply (auto simp: pw_le_iff refine_pw_simps slice_rel_def in_br_conv)
  done
  
  
sepref_def is_insert_impl is "uncurry2 is_insert3" 
  :: "(array_assn elem_assn)\<^sup>d *\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k \<rightarrow>\<^sub>a array_assn elem_assn"
  unfolding is_insert3_def
  supply [[goals_limit = 1]]
  apply (annot_snat_const "TYPE(size_t)")
  by sepref
  
  
    
sepref_def insertion_sort_impl is "uncurry2 insertion_sort" 
  :: "(array_assn elem_assn)\<^sup>d *\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k \<rightarrow>\<^sub>a array_assn elem_assn "
  unfolding insertion_sort_def
  apply (annot_snat_const "TYPE(size_t)")
  by sepref
    
export_llvm insertion_sort_impl

lemmas insertion_sort_impl_hnr[sepref_fr_rules] = insertion_sort_impl.refine[FCOMP insertion_sort_correct]

  
term mop_list_swap
definition "move_median_to_first ri ai bi ci (xs::'a::linorder list) \<equiv> doN {
    a \<leftarrow> mop_list_get xs ai;
    b \<leftarrow> mop_list_get xs bi;
    c \<leftarrow> mop_list_get xs ci;
  
    if a<b then (
      if b<c then
        mop_list_swap xs ri bi
      else if a<c then
        mop_list_swap xs ri ci
      else 
        mop_list_swap xs ri ai
    ) 
    else if a<c then
      mop_list_swap xs ri ai
    else if b<c then 
      mop_list_swap xs ri ci
    else 
      mop_list_swap xs ri bi
  }"

    
lemma move_median_to_first_correct:
  "\<lbrakk> ri<ai; ai<bi; bi<ci; ci<length xs \<rbrakk> \<Longrightarrow> 
  move_median_to_first ri ai bi ci xs 
    \<le> SPEC (\<lambda>xs'. slice_eq_mset ri (ci+1) xs' xs 
      \<and> (\<exists>i\<in>{ai..ci}. xs'!i\<le>xs'!ri)
      \<and> (\<exists>i\<in>{ai..ci}. xs'!i\<ge>xs'!ri)
      )"
  unfolding move_median_to_first_def
  apply refine_vcg
  apply clarsimp_all
  apply (
      rule bexI[where x="ai"]; auto; fail
    | rule bexI[where x="bi"]; auto; fail
    | rule bexI[where x="ci"]; auto; fail
  )+
  done
  
  
(*lemma move_median_to_first_mset_spec:
  "\<lbrakk> ri<length xs; ai<length xs; bi<length xs; ci<length xs \<rbrakk> \<Longrightarrow> 
  move_median_to_first ri ai bi ci xs 
    \<le> SPEC (\<lambda>xs'. mset xs' = mset xs \<and> (\<exists>i1\<in>{ai,bi,ci}. xs!ai\<le>xs!ri))"
  unfolding move_median_to_first_def
  apply refine_vcg
  apply auto
  done
*)
  
  
definition qsp_next_l :: "'a::linorder list \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> nat nres" where            
  "qsp_next_l xs p li \<equiv> doN {
    WHILEIT (\<lambda>li'. (\<exists>pi\<in>{li'..<length xs}. xs!pi\<ge>p) \<and> li\<le>li' \<and> (\<forall>i\<in>{li..<li'}. xs!i<p)) 
      (\<lambda>li. xs!li < p) (\<lambda>li. RETURN (li + 1)) li
  }"  

  
lemma qsp_next_l_correct[refine_vcg]: "\<lbrakk>\<exists>pi\<in>{li..<length xs}. xs!pi \<ge> p\<rbrakk> 
  \<Longrightarrow> qsp_next_l xs p li 
    \<le> SPEC (\<lambda>li'. li\<le>li' \<and> li'<length xs \<and> (\<forall>i\<in>{li..<li'}. xs!i<p) \<and> xs!li'\<ge>p)"
  unfolding qsp_next_l_def
  apply (refine_vcg WHILEIT_rule[where R="measure (\<lambda>li. length xs - li)"])
  apply simp_all
  subgoal using less_eq_Suc_le by force
  subgoal apply auto by (metis atLeastLessThan_iff less_SucE)
  subgoal by auto
  subgoal by auto
  done
  
  
definition qsp_next_h :: "'a::linorder list \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> nat nres" where
  "qsp_next_h xs p hi \<equiv> doN {
    ASSERT (hi>0);
    let hi = hi - 1;
    ASSERT (hi<length xs);
    WHILEIT (\<lambda>hi'. hi'\<le>hi \<and> (\<exists>pi\<le>hi'. xs!pi\<le>p) \<and> (\<forall>i\<in>{hi'<..hi}. xs!i>p))
      (\<lambda>hi. xs!hi > p) (\<lambda>hi. doN { ASSERT(hi>0); RETURN (hi - 1)}) hi
  }"  

lemma qsp_next_h_correct[refine_vcg]: "\<lbrakk> hi\<le>length xs; \<exists>pi<hi. xs!pi \<le> p \<rbrakk> 
  \<Longrightarrow> qsp_next_h xs p hi \<le> SPEC (\<lambda>hi'. hi'<hi \<and> (\<forall>i\<in>{hi'<..<hi}. xs!i>p) \<and> xs!hi'\<le>p)"
  unfolding qsp_next_h_def
  apply (refine_vcg WHILEIT_rule[where R="measure id"])
  apply (all \<open>(auto;fail)?\<close>)
  subgoal
    using nat_le_Suc_less_imp
    by auto
  subgoal using leD by force  
  subgoal apply clarsimp by (metis One_nat_def leD le_step_down_nat)
  subgoal apply clarsimp by (metis Suc_lessI Suc_pred greaterThanAtMost_iff)
  done
  
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
      
definition "qs_partition li\<^sub>0 hi\<^sub>0 p xs\<^sub>0 \<equiv> doN {
  ASSERT (li\<^sub>0<hi\<^sub>0 \<and> hi\<^sub>0\<le>length xs\<^sub>0);
  
  \<comment> \<open>Initialize\<close>
  li \<leftarrow> qsp_next_l xs\<^sub>0 p li\<^sub>0;
  hi \<leftarrow> qsp_next_h xs\<^sub>0 p hi\<^sub>0;
  
  ASSERT (li\<^sub>0\<le>hi);
  
  (xs,li,hi) \<leftarrow> WHILEIT 
    (\<lambda>(xs,li,hi). 
        li\<^sub>0\<le>li \<and> hi<hi\<^sub>0
      \<and> li<hi\<^sub>0 \<and> hi\<ge>li\<^sub>0  
      \<and> slice_eq_mset li\<^sub>0 hi\<^sub>0 xs xs\<^sub>0
      \<and> (\<forall>i\<in>{li\<^sub>0..<li}. xs!i \<le> p)
      \<and> xs!li \<ge> p
      \<and> (\<forall>i\<in>{hi<..<hi\<^sub>0}. xs!i\<ge>p)
      \<and> xs!hi \<le> p  
    )
    (\<lambda>(xs,li,hi). li<hi) 
    (\<lambda>(xs,li,hi). doN {
      ASSERT(li<length xs \<and> hi<length xs);
      xs \<leftarrow> mop_list_swap xs li hi;
      let li = li + 1;
      li \<leftarrow> qsp_next_l xs p li;
      hi \<leftarrow> qsp_next_h xs p hi;
      RETURN (xs,li,hi)
    }) 
    (xs\<^sub>0,li,hi);
  
  RETURN (xs,li)
}"  
  

lemma qs_partition_correct:
  "\<lbrakk> li<hi; hi\<le>length xs\<^sub>0;  \<exists>pi\<in>{li..<hi}. p \<le> xs\<^sub>0 ! pi; \<exists>pi\<in>{li..<hi}. xs\<^sub>0 ! pi \<le> p \<rbrakk> \<Longrightarrow> qs_partition li hi p xs\<^sub>0 
  \<le> SPEC (\<lambda>(xs,i). slice_eq_mset li hi xs xs\<^sub>0 \<and> li\<le>i \<and> i<hi \<and> (\<forall>i\<in>{li..<i}. xs!i\<le>p) \<and> (\<forall>i\<in>{i..<hi}. xs!i\<ge>p) )"  
  unfolding qs_partition_def
  apply (refine_vcg WHILEIT_rule[where R="measure (\<lambda>(_,_,hi). hi)"])  
  apply (simp_all add: slice_eq_mset_eq_length)
  subgoal by auto
  subgoal by auto
  subgoal 
    apply clarsimp
    by (meson greaterThanLessThan_iff leD le_less_linear less_le_trans)
  subgoal 
    apply clarsimp
    by (meson atLeastLessThan_iff leD leI less_le_trans)
  subgoal by (auto)
  subgoal by (auto)
  subgoal by (auto dest: slice_eq_mset_eq_length)
  subgoal by (auto dest: slice_eq_mset_eq_length)
  subgoal apply clarsimp
    by (metis atLeastSucLessThan_greaterThanLessThan greaterThanLessThan_iff swap_nth2)
  subgoal by (auto)
  subgoal
    apply clarsimp
    by (metis (mono_tags, hide_lams) atLeastSucLessThan_greaterThanLessThan greaterThanLessThan_iff le_cases less_le_trans neq_iff swap_nth2)
  subgoal apply clarsimp
    by (metis greaterThanLessThan_iff leD le_less_linear less_le_trans order.strict_trans swap_nth1)
  subgoal by auto
  subgoal apply (clarsimp)
    by (smt Suc_leI atLeastLessThan_iff dual_order.order_iff_strict leI less_trans swap_nth)
  subgoal 
    apply clarsimp
    by (smt antisym_conv2 greaterThanLessThan_iff le_less_linear less_imp_not_eq2 less_trans slice_eq_mset_eq_length swap_nth)
  subgoal apply clarsimp 
    by (metis greaterThanLessThan_iff le_less_linear le_less_trans order.not_eq_order_implies_strict)  
    
  done
  
corollary qs_partition_mset:
  "\<lbrakk> li<hi; hi\<le>length xs\<^sub>0; \<exists>i\<in>{li..<hi}. p\<le>xs\<^sub>0!i; \<exists>i\<in>{li..<hi}. xs\<^sub>0!i\<le>p \<rbrakk> \<Longrightarrow> qs_partition li hi p xs\<^sub>0 
  \<le> SPEC (\<lambda>(xs,i). slice_eq_mset li hi xs xs\<^sub>0 \<and> li\<le>i \<and> i<hi )"  
  apply (refine_vcg qs_partition_correct)
  by auto

abbreviation "is_threshold \<equiv> 16::nat"  

definition "partition_pivot xs\<^sub>0 l h \<equiv> doN {
  ASSERT (l\<le>h \<and> h\<le>length xs\<^sub>0 \<and> h-l\<ge>4);
  let m = l + (h-l) div 2;
  xs \<leftarrow> move_median_to_first l (l+1) m (h-1) xs\<^sub>0;
  ASSERT (l<length xs \<and> length xs = length xs\<^sub>0);
  (xs,m) \<leftarrow> qs_partition (l+1) h (xs!l) xs;

  RETURN (xs,m)
}"

lemma partition_pivot_mset: "\<lbrakk> l\<le>h ; h\<le>length xs; h-l\<ge>4 \<rbrakk> \<Longrightarrow> partition_pivot xs l h 
  \<le> SPEC (\<lambda>(xs',m). slice_eq_mset l h xs' xs \<and> l<m \<and> m<h)"
  unfolding partition_pivot_def
  apply (refine_vcg move_median_to_first_correct qs_partition_mset)
  apply (auto 0 3 dest: slice_eq_mset_eq_length elim: )
  by (smt add.commute le_add1 le_trans order.strict_implies_order order_mono_setup.refl plus_1_eq_Suc slice_eq_mset_subslice slice_eq_mset_trans)
  

 
definition "introsort_qs_aux xs\<^sub>0 l h \<equiv> RECT (\<lambda>introsort_qs_aux (xs,l,h). doN {
  ASSERT (l\<le>h \<and> h\<le>length xs \<and> length xs = length xs\<^sub>0);
  
  if h-l > is_threshold then doN {
    (xs,m) \<leftarrow> partition_pivot xs l h;
    
    ASSERT (l<m \<and> m<h);

    xs \<leftarrow> introsort_qs_aux (xs,l+1,m);    
    xs \<leftarrow> introsort_qs_aux (xs,m,h);    
  
    RETURN xs
  } else   
    RETURN xs
    
}) (xs\<^sub>0,l,h)"   
  
lemma introsort_qs_aux_mset: "\<lbrakk> l\<^sub>0\<le>h\<^sub>0; h\<^sub>0\<le>length xs\<^sub>0\<rbrakk> \<Longrightarrow> introsort_qs_aux xs\<^sub>0 l\<^sub>0 h\<^sub>0 \<le> SPEC (\<lambda>xs'. slice_eq_mset l\<^sub>0 h\<^sub>0 xs' xs\<^sub>0)"
  unfolding introsort_qs_aux_def
  apply (refine_vcg RECT_rule[where 
    pre="\<lambda>(xs',l,h). l\<^sub>0\<le>l \<and> h\<le>h\<^sub>0 \<and> l\<le>h \<and> h\<le>length xs' \<and> slice_eq_mset l\<^sub>0 h\<^sub>0 xs' xs\<^sub>0" and
    V="measure (\<lambda>(_,l,h). h-l)"]
  
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
  done
    
  
definition "introsort xs l h \<equiv> doN {
  xs \<leftarrow> introsort_qs_aux xs l h;
  xs \<leftarrow> insertion_sort xs l h;
  RETURN xs
}"  

thm insertion_sort_correct[param_fo, THEN nres_relD, simplified]

text \<open> Sorting a permutation of a list amounts to sorting the list! \<close>
lemma sort_spec_permute: "\<lbrakk>mset xs' = mset xs; sort_spec xs' ys\<rbrakk> \<Longrightarrow> sort_spec xs ys"
  unfolding sort_spec_def by auto

lemma introsort_correct: 
  assumes "l\<le>h" "h\<le>length xs"
  shows "introsort xs l h \<le> slice_sort_spec xs l h"
  unfolding introsort_def 
  (* Manual refinement of LHS to use specs. TODO: Define this abstract fun explicitly! *)
  apply (simp)
  apply (rule order_trans)
  apply (rule bind_mono)
  apply (rule introsort_qs_aux_mset[OF assms])
  apply (rule insertion_sort_correct[param_fo, OF IdI IdI IdI, THEN nres_relD, simplified])

  (* show that slice_sort on eq-mset-slice implies slice-sort  *)
  apply (auto simp: pw_le_iff pw_nres_rel_iff refine_pw_simps slice_sort_spec_def slice_eq_mset_def intro: sort_spec_permute)  
  done
  

term move_median_to_first  

find_theorems nfoldli

find_consts name: "monadic"

find_in_thms array_assn  op_list_set in sepref_fr_rules

sepref_register move_median_to_first

sepref_def move_median_to_first_impl is "uncurry4 move_median_to_first" :: "size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k *\<^sub>a (array_assn elem_assn)\<^sup>d \<rightarrow>\<^sub>a array_assn elem_assn"
  unfolding move_median_to_first_def
  by sepref
                   
  
term qsp_next_l
term b_assn

sepref_register qsp_next_l qsp_next_h 
sepref_def qsp_next_l_impl is "uncurry2 qsp_next_l" :: "[\<lambda>((xs,p),i). length xs < max_snat LENGTH(size_t)]\<^sub>a(array_assn elem_assn)\<^sup>k *\<^sub>a elem_assn\<^sup>k *\<^sub>a size_assn\<^sup>k \<rightarrow> size_assn"
  unfolding qsp_next_l_def
  apply (annot_snat_const "TYPE(size_t)")
  by sepref

sepref_def qsp_next_h_impl is "uncurry2 qsp_next_h" :: "(array_assn elem_assn)\<^sup>k *\<^sub>a elem_assn\<^sup>k *\<^sub>a size_assn\<^sup>k \<rightarrow>\<^sub>a size_assn"
  unfolding qsp_next_h_def
  apply (annot_snat_const "TYPE(size_t)")
  by sepref
  
                        
sepref_register qs_partition  
  
sepref_def qs_partition_impl is "uncurry3 qs_partition" :: "[\<lambda>(((l,h),p),xs). length xs < max_snat LENGTH(size_t)]\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k *\<^sub>a elem_assn\<^sup>k *\<^sub>a (array_assn elem_assn)\<^sup>d \<rightarrow> array_assn elem_assn \<times>\<^sub>a size_assn"
  unfolding qs_partition_def
  apply (annot_snat_const "TYPE(size_t)")
  supply [dest] = slice_eq_mset_eq_length
  by sepref
  
term partition_pivot  
  
term introsort_qs_aux
  
sepref_def introsort_qs_aux_impl is "uncurry2 introsort_qs_aux" :: "[\<lambda>((xs,l),h). length xs < max_snat LENGTH(size_t)]\<^sub>a (array_assn elem_assn)\<^sup>d *\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k \<rightarrow> array_assn elem_assn"
  unfolding introsort_qs_aux_def partition_pivot_def
  apply (annot_snat_const "TYPE(size_t)")
  by sepref

sepref_def introsort_impl is "uncurry2 introsort" :: "[\<lambda>((xs,l),h). length xs < max_snat LENGTH(size_t)]\<^sub>a (array_assn elem_assn)\<^sup>d *\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k \<rightarrow> array_assn elem_assn"
  unfolding introsort_def
  by sepref
    
  
find_theorems "return" "Monad.bind"
(* TODO: Move! *)


export_llvm introsort_impl is "uint64_t* introsort(uint64_t*, int64_t, int64_t)" file "code/introsort.ll"
  
    
oops  
                
qs_partition (qsp_next_xxx)  
  oops                                                                                                                  
  xxx, add this!
  find_in_thms mop_list_swap in sepref_fr_rules
  
  
find_theorems insertion_sort
  
xxx, ctd here: 
  generate llvm for array and hi,lo indices!
  maybe define array-segment refinement?


oops
xxx, ctd here:
  Assemble intro_sort
  generate llvm

  
xxx, ctd here: 
  do recursive quicksort. But stop short at small intervals.
    Only show mset preservation! 
  
  
lemmas insertion_sort_impl_hnr[sepref_fr_rules] 
  = insertion_sort_impl.refine[FCOMP insertion_sort2_refines[FCOMP insertion_sort_correct, simplified]]

xxx, do partial quicksort!
  partition (median of 3, which partitioning algorithm does STL use)
  implement by recursion (?). 
  stop if partition < threshold

                  
  oops
xxx: t sepref_def  
xxx, add assertions and export to LLVM!
  
thm is_insert_def
  
      
  
  find_theorems "sorted _ \<longleftrightarrow> _" nth  
    
  oops
  xxx, ctd here:
    postcond. and show that this implies sorting spec! 
  
(*

  TODO: Use llcm.ctlz instrinsic!

*)  
  
  
(*
  Notes: 
    introsort_loop: upper half by recursion, lower-half by loop
      saves stack space?

    final_insertion_sort: strange structure, using insertion-sort for the first max 16 elements,
      and unguarded_insertion_sort for the rest. 
      The stl-impl also relies on partial sortedness here!

    __insertion_sort        
      I don't really understand the comp (first,i) branch.
       
*)
  
  
  

end
