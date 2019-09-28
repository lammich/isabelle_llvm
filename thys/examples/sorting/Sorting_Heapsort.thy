theory Sorting_Heapsort
imports Sorting_Setup
begin


locale heap_range_context = 
  fixes l h :: nat
  assumes ran_not_empty[arith,simp]: "l\<le>h"
begin  

  (*lemma l_le_h[arith,simp]: "l\<le>h" by simp*)

  definition "in_heap i \<equiv> i\<in>{l..<h}"

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
      
    lemma in_heap_bounds[simp]: 
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

    lemmas in_heap_simps = in_heap_triv parent_in_heap children_in_heap
            

    lemma parent_of_child[simp]:
      "has_lchild i \<Longrightarrow> parent (lchild i) = i"
      "has_rchild i \<Longrightarrow> parent (rchild i) = i"
      by prove

    lemma children_differ[simp]:
      "lchild i \<noteq> rchild i" 
      "rchild i \<noteq> lchild i" 
      by prove

    lemma parent_less[simp]: "has_parent i \<Longrightarrow> parent i < i" by prove

    lemma children_greater[simp]: 
      "lchild i > i" 
      "rchild i > i"
      by prove

      
    lemma children_diff_add_simps[iff]:
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
    
    lemma root_no_parent[iff]: "\<not>has_parent l" by prove
    
    
    lemma root_in_heap: "in_heap l\<longleftrightarrow>l<h" using ran_not_empty by prove
    
                      
    lemma child_of_parent: "has_parent i \<Longrightarrow> lchild (parent i) = i \<or> has_rchild (parent i) \<and> rchild (parent i) = i" by prove
                
    lemma children_of_parent_cases[consumes 1]:
      assumes "has_parent i"
      obtains (left) "has_parent i" "lchild (parent i) = i" 
            | (right) "has_parent i" "has_rchild (parent i)" "rchild (parent i) = i"
      using assms child_of_parent by blast            

    lemma lchild_of_no_rchild_term: "\<lbrakk>\<not>has_rchild i; has_lchild i\<rbrakk> \<Longrightarrow> \<not>has_lchild (lchild i)" by prove 
      
      
          
  end

  lemmas heap_context_defs[no_atp] = in_heap_def parent_def lchild_def rchild_def has_parent_def has_lchild_def has_rchild_def
end  
  
locale heap_context = weak_ordering + heap_range_context begin
  
  definition is_heap :: "'a list \<Rightarrow> bool" 
    where "is_heap xs \<equiv> (h\<le>length xs) \<and> (\<forall>i. has_parent i \<longrightarrow> xs!parent i \<^bold>\<ge> xs!i)"

    
  subsection \<open>Heap Property implies Minimal Element at Top\<close>
  context
    fixes xs
    assumes H: "is_heap xs"
  begin  

    lemma parent_el_greater[simp]: "has_parent i \<Longrightarrow> xs!i \<^bold>\<le> xs!parent i"
      using H
      unfolding is_heap_def 
      by simp
    
    lemma root_greatest:
      assumes "in_heap i"
      shows "xs!i \<^bold>\<le> xs!l"
      using assms 
    proof (induction i rule: less_induct)
      case (less i)
      note [simp] = \<open>in_heap i\<close>
      
      show ?case proof cases
        assume [simp]: "has_parent i"
        have "xs!i \<^bold>\<le> xs!parent i" by simp
        also from less.IH[of "parent i"] have "xs!parent i \<^bold>\<le> xs!l" by simp
        finally show ?case .
      next
        assume "\<not>has_parent i" 
        hence "i=l" by (simp add: no_parent_is_root)
        thus ?case by simp
      qed  
    qed
  
  end  

    
  subsection \<open>Sift-Up Lemmas\<close>    
  definition is_heap_except_up :: "nat \<Rightarrow> 'a list \<Rightarrow> bool" 
    where "is_heap_except_up j xs \<equiv> 
      (h\<le>length xs) 
      \<and> (\<forall>i. has_parent i \<and> i\<noteq>j \<longrightarrow> xs!parent i \<^bold>\<ge> xs!i)
      \<and> (has_parent j \<and> has_lchild j \<longrightarrow> xs!parent j \<^bold>\<ge> xs!lchild j)
      \<and> (has_parent j \<and> has_rchild j \<longrightarrow> xs!parent j \<^bold>\<ge> xs!rchild j)"

  lemma is_heap_except_up_len_bound[simp, intro]: 
    assumes "is_heap_except_up i xs"
    shows "h\<le>length xs"     
    using assms unfolding is_heap_except_up_def
    by auto
        
  lemma sift_up_lemma:
    assumes HP: "has_parent i"
    assumes IHE: "is_heap_except_up i xs"
    assumes GE: "xs!i \<^bold>\<ge> xs!parent i"
    shows "is_heap_except_up (parent i) (swap xs i (parent i))"
  proof -
    from assms(2) have [simp, arith]: "h\<le>length xs" unfolding is_heap_except_up_def by auto
  
    have X[simp]: "i<length xs" if "in_heap i" for i
      using in_heap_bounds(2)[OF that] by simp

    have HPROP: "xs!j \<^bold>\<le> xs!parent j" if "has_parent j" "j\<noteq>i" for j
      using that IHE unfolding is_heap_except_up_def by simp
      
      
    show ?thesis using HP
      unfolding is_heap_except_up_def
      apply (clarsimp; safe)
      subgoal
        apply (clarsimp simp: swap_nth HPROP GE; safe)
        subgoal by (metis GE HPROP trans)
        by (metis IHE child_of_parent is_heap_except_up_def parent_in_heap(2))

      subgoal
        by (smt HPROP X children_greater(1) has_lchild_def in_heap_bounds(1) parent_of_child(1) trans nat_less_le no_parent_is_root parent_in_heap(2) parent_less less_le_trans swap_indep swap_nth)
      subgoal 
        by (smt HPROP X children_greater(2) has_parent_def has_rchild_def parent_less parent_of_child(2) less_le trans less_trans swap_nth)
        
      done
      
  qed

  text \<open>Terminate when reached root\<close>
  lemma sift_up_term1: "is_heap_except_up l xs \<Longrightarrow> is_heap xs"
    unfolding is_heap_def is_heap_except_up_def by auto
  
  text \<open>Terminate when parent is greater or equal\<close>  
  lemma sift_up_term2: "\<lbrakk>is_heap_except_up i xs; xs!i\<^bold>\<le>xs!parent i\<rbrakk> \<Longrightarrow> is_heap xs"
    unfolding is_heap_def is_heap_except_up_def by auto
  
  lemma grow_heap_context: "heap_range_context l (Suc h)" 
    apply unfold_locales using ran_not_empty by linarith 
    
  text \<open>Initializes a sift-up cycle by extending the heap by one element to the right\<close>  
  lemma sift_up_init:
    assumes "is_heap xs"
    assumes "h<length xs"
    shows "heap_context.is_heap_except_up (\<^bold>\<le>) l (Suc h) h xs"
  proof -
    interpret N: heap_range_context l "Suc h" using grow_heap_context .
    interpret N: heap_context "(\<^bold>\<le>)" "(\<^bold><)" l "Suc h" by unfold_locales
  
    show ?thesis
      using assms
      unfolding is_heap_def is_heap_except_up_def N.is_heap_except_up_def
      unfolding N.heap_context_defs heap_context_defs
      by auto
      
  qed
  
  subsection \<open>Sift-Down Lemmas\<close>    

  definition is_heap_except_down :: "nat \<Rightarrow> 'a list \<Rightarrow> bool"
    where "is_heap_except_down j xs \<equiv>
        (h\<le>length xs) 
      \<and> (\<forall>i. has_parent i \<and> parent i \<noteq> j \<longrightarrow> xs!parent i \<^bold>\<ge> xs!i)
      \<and> (\<forall>i. has_parent i \<and> has_parent j \<and> parent i = j \<longrightarrow> xs!parent j \<^bold>\<ge> xs!i)"

  lemma is_heap_except_down_len_bound[simp, intro]: 
    assumes "is_heap_except_down i xs"
    shows "h\<le>length xs"     
    using assms unfolding is_heap_except_down_def
    by auto
          
  lemma sift_down_lemma_left:
    assumes HRC: "has_rchild i"
    assumes IHE: "is_heap_except_down i xs"
    assumes GE: "xs!lchild i \<^bold>\<ge> xs!i" "xs!lchild i \<^bold>\<ge> xs!rchild i"
    shows "is_heap_except_down (lchild i) (swap xs i (lchild i))"
  proof -  
    show ?thesis 
      using IHE HRC GE
      unfolding is_heap_except_down_def
      apply (clarsimp)
      by (smt child_of_parent children_greater(1) children_in_heap(1) dual_order.trans has_parent_def parent_diff_add_simps(1) in_heap_bounds(2) leD order_less_le parent_of_child(1) rchild_imp_lchild swap_indep swap_nth1 swap_nth2)
      
  qed

  lemma sift_down_lemma_right:
    assumes HRC: "has_rchild i"
    assumes IHE: "is_heap_except_down i xs"
    assumes GE: "xs!rchild i \<^bold>\<ge> xs!i" "xs!lchild i \<^bold>\<le> xs!rchild i"
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
    assumes GE: "xs!lchild i \<^bold>\<ge> xs!i"
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
  
  lemma sift_down_term2: "\<lbrakk>is_heap_except_down j xs; has_rchild j; xs!j\<^bold>\<ge>xs!lchild j; xs!j\<^bold>\<ge>xs!rchild j \<rbrakk> \<Longrightarrow> is_heap xs"
    unfolding is_heap_except_down_def is_heap_def
    apply (clarsimp)
    by (metis children_of_parent_cases)
  
  lemma sift_down_term3: "\<lbrakk>is_heap_except_down j xs; has_lchild j; \<not>has_rchild j; xs!j\<^bold>\<ge>xs!lchild j \<rbrakk> \<Longrightarrow> is_heap xs"
    unfolding is_heap_except_down_def is_heap_def
    apply (clarsimp)
    by (metis children_of_parent_cases)
     
  lemma shrink_heap_context: "Suc l<h \<Longrightarrow> heap_range_context l (h-Suc 0)" 
    apply unfold_locales using ran_not_empty by linarith 
  
  text \<open>Initializes a sift-down cycle by swapping the first and last element, and then shrinking the heap by one element\<close>
  lemma sift_down_init:  
    assumes "is_heap xs"
    assumes LT: "Suc l < h"
    shows "heap_context.is_heap_except_down (\<^bold>\<le>) l (h-Suc 0) l (swap xs l (h-Suc 0))"
  proof -
    interpret N: heap_context "(\<^bold>\<le>)" "(\<^bold><)" l "h-Suc 0"
      apply intro_locales
      using shrink_heap_context[OF LT] .
    
    show ?thesis
      using assms
      unfolding is_heap_def is_heap_except_down_def N.is_heap_except_down_def
      unfolding N.heap_context_defs heap_context_defs
      by (auto simp: swap_nth)
      
  qed    
        
    
  subsection \<open>Bottom-up Heapify\<close>

  text \<open>The nodes from index \<open>l'\<close> upwards satisfy the heap criterion\<close>
  definition is_heap_btu :: "nat \<Rightarrow> 'a list \<Rightarrow> bool" where "is_heap_btu l' xs \<equiv> 
        (l'\<le>h \<and> h\<le>length xs) 
      \<and> (\<forall>i. has_parent i \<and> parent i \<ge> l' \<longrightarrow> xs!parent i \<^bold>\<ge> xs!i)"

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
  definition is_heap_except_down_btu :: "nat \<Rightarrow> nat \<Rightarrow> 'a list \<Rightarrow> bool"
    where "is_heap_except_down_btu l' j xs \<equiv>
        (l'\<le>j \<and> j<h \<and> h\<le>length xs) 
      \<and> (\<forall>i. has_parent i \<and> parent i \<ge> l' \<and> parent i \<noteq> j \<longrightarrow> xs!parent i \<^bold>\<ge> xs!i)
      \<and> (\<forall>i. has_parent i \<and> has_parent j \<and> parent j \<ge>l' \<and> parent i = j \<longrightarrow> xs!parent j \<^bold>\<ge> xs!i)"

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
      
  lemma btu_sift_down_term2: "\<lbrakk>is_heap_except_down_btu l' j xs; has_rchild j; xs!j\<^bold>\<ge>xs!lchild j; xs!j\<^bold>\<ge>xs!rchild j \<rbrakk> 
    \<Longrightarrow> is_heap_btu l' xs"
    unfolding is_heap_except_down_btu_def is_heap_btu_def
    apply (clarsimp)
    by (smt dual_order.trans child_of_parent in_heap_bounds(2) in_heap_triv(3) le_cases not_le)
  
  lemma btu_sift_down_term3: "\<lbrakk>is_heap_except_down_btu l' j xs; has_lchild j; \<not>has_rchild j; xs!j\<^bold>\<ge>xs!lchild j \<rbrakk> \<Longrightarrow> is_heap_btu l' xs"
    unfolding is_heap_except_down_btu_def is_heap_btu_def
    apply (clarsimp)
    by (metis child_of_parent dual_order.trans in_heap_bounds(2) in_heap_triv(2) less_imp_le)
  

  

  lemma btu_heapify_down_left:
    assumes HRC: "has_rchild i"
    assumes IHE: "is_heap_except_down_btu l' i xs"
    assumes GE: "xs!lchild i \<^bold>\<ge> xs!i" "xs!lchild i \<^bold>\<ge> xs!rchild i"
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
    assumes GE: "xs!rchild i \<^bold>\<ge> xs!i" "xs!lchild i \<^bold>\<le> xs!rchild i"
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
    assumes GE: "xs!lchild i \<^bold>\<ge> xs!i"
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
    shows "heap_context.sift_up_invar (\<^bold>\<le>) l (Suc h) xs\<^sub>0 h xs"
  proof -
    interpret N: heap_context "(\<^bold>\<le>)" "(\<^bold><)" l "Suc h" by intro_locales (simp add: grow_heap_context)
    
    show ?thesis 
      using assms
      by (meson N.sift_up_invar_def le_eq_less_or_eq nat_in_between_eq(1) ran_not_empty sift_up_init slice_eq_mset_subslice)
      
  qed    
      
  lemma sift_up_invar_step: "\<lbrakk>sift_up_invar xs\<^sub>0 i xs; has_parent i; xs!i\<^bold>\<ge>xs!parent i \<rbrakk> 
    \<Longrightarrow> sift_up_invar xs\<^sub>0 (parent i) (swap xs i (parent i))"
    unfolding sift_up_invar_def
    by (auto simp: sift_up_lemma)
    
  lemma sift_up_invar_term1: "\<lbrakk>sift_up_invar xs\<^sub>0 l xs\<rbrakk> \<Longrightarrow> is_heap xs \<and> slice_eq_mset l h xs xs\<^sub>0"
    unfolding sift_up_invar_def
    using sift_up_term1 by blast
    
  lemma sift_up_invar_term2: "\<lbrakk>sift_up_invar xs\<^sub>0 i xs; xs!i\<^bold>\<le>xs!parent i\<rbrakk> 
    \<Longrightarrow> is_heap xs \<and> slice_eq_mset l h xs xs\<^sub>0"
    unfolding sift_up_invar_def
    using sift_up_term2 by blast

  definition "sift_down_invar xs\<^sub>0 i xs \<equiv>
      slice_eq_mset l h xs xs\<^sub>0      
    \<and> is_heap_except_down i xs"  

  lemma sift_down_invar_step:
    assumes "sift_down_invar xs\<^sub>0 i xs"
    shows "\<lbrakk>has_rchild i; xs!i\<^bold>\<le>xs!lchild i; xs!lchild i \<^bold>\<ge> xs!rchild i\<rbrakk> \<Longrightarrow> sift_down_invar xs\<^sub>0 (lchild i) (swap xs i (lchild i))" 
      and "\<lbrakk>has_rchild i; xs!i\<^bold>\<le>xs!rchild i; xs!lchild i \<^bold>\<le> xs!rchild i\<rbrakk> \<Longrightarrow> sift_down_invar xs\<^sub>0 (rchild i) (swap xs i (rchild i))"
      and "\<lbrakk>has_lchild i; \<not>has_rchild i; xs!i\<^bold>\<le>xs!lchild i\<rbrakk> \<Longrightarrow> sift_down_invar xs\<^sub>0 (lchild i) (swap xs i (lchild i))" 
    using assms unfolding sift_down_invar_def
    by (auto simp: sift_down_lemma_left sift_down_lemma_right sift_down_lemma_left_no_right_child)

  thm sift_down_init (*xxx, ctd here: we need to initialize from heapsort loop invariant*)
  lemma sift_down_invar_init: 
    assumes "is_heap xs" "Suc l < h" 
    shows "heap_context.sift_down_invar (\<^bold>\<le>) l (h-Suc 0) (swap xs l (h-Suc 0)) l (swap xs l (h-Suc 0))"
  proof -
    interpret N: heap_context "(\<^bold>\<le>)" "(\<^bold><)" l "h-Suc 0" apply intro_locales using assms shrink_heap_context by auto
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

context weak_ordering begin

  sublocale singleton_heap_context: heap_context "(\<^bold>\<le>)" "(\<^bold><)" l "(Suc l)"
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

end  
    
context heap_context begin  
  
  definition sift_down :: "nat \<Rightarrow> 'a list \<Rightarrow> 'a list nres" where "sift_down i xs \<equiv> doN {
    ASSERT (in_heap i \<and> i<length xs);
    (xs,i,_) \<leftarrow> WHILEIT (\<lambda>(xs,i,ctd). in_heap i) 
      (\<lambda>(xs,i,ctd). has_rchild i \<and> ctd) 
      (\<lambda>(xs,i,ctd). doN {
        lc \<leftarrow> mop_list_get xs (lchild i);
        rc \<leftarrow> mop_list_get xs (rchild i);
        v \<leftarrow> mop_list_get xs i;
      
        if lc \<^bold>< rc then
          if v \<^bold>< rc then doN {
            xs \<leftarrow> mop_list_swap xs i (rchild i);
            RETURN (xs,rchild i,True)
          } else RETURN (xs,i,False)
        else if v \<^bold>< lc then doN {
          xs \<leftarrow> mop_list_swap xs i (lchild i);
          RETURN (xs,lchild i,True)
        } else RETURN (xs,i,False)
      }) 
    (xs,i,True);
  
    ASSERT (in_heap i);
    ASSERT (has_lchild i \<longrightarrow> lchild i < length xs);
    
    if has_lchild i \<and> xs!i \<^bold>< xs!lchild i then
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
          \<and> (\<not>ctd \<longrightarrow> has_rchild i \<and> xs!i\<^bold>\<ge>xs!lchild i \<and> xs!i\<^bold>\<ge>xs!rchild i)"
      and
      R = "measure (\<lambda>(xs,i,ctd). (if ctd then 1 else 0) + h - i)"    
    ]) 
    using assms
    unfolding heapify_btu_invar_def sift_down_btu_invar_def
    apply (simp_all del: in_heap_simps)
    apply (all \<open>(auto simp: in_heap_len_bound diff_less_mono2 wo_leI; fail)?\<close>)
    subgoal unfolding is_heap_btu_def by (auto intro!: in_heapI)
    subgoal unfolding is_heap_btu_def by auto
    subgoal using btu_sift_down_init by auto
    subgoal unfolding is_heap_btu_def by auto
    subgoal by (force simp: asym wo_leI simp: btu_heapify_down_right)   
    subgoal by (simp add: diff_less_mono2 less_Suc_eq)
    subgoal by simp (metis wo_leI wo_less_trans)
    subgoal by (simp add: diff_less_mono less_imp_le)
    subgoal by (force simp add: btu_heapify_down_left asym wo_leI)
    subgoal by (simp add: diff_less_mono2 less_Suc_eq)
    subgoal apply simp using local.trans wo_leI by blast
    subgoal by (simp add: diff_less_mono less_imp_le)
    subgoal 
      apply clarsimp
      using btu_heapify_down_left_no_right_child btu_sift_down_term1 connex lchild_of_no_rchild_term wo_leD by blast
    subgoal 
      apply clarsimp
      using btu_sift_down_term1 btu_sift_down_term2 btu_sift_down_term3 wo_leI by blast
    done    
  

  lemma sift_down_restore_correct: 
    assumes A: "l<h" "sift_down_invar xs\<^sub>0 l xs"
    shows "sift_down l xs \<le> SPEC (\<lambda>xs'. slice_eq_mset l h xs' xs\<^sub>0 \<and> is_heap xs')"  
    unfolding sift_down_def
    apply (refine_vcg WHILEIT_rule_amend_invar[where 
      I="\<lambda>(xs,i,ctd). 
          sift_down_invar xs\<^sub>0 i xs 
          \<and> h\<le>length xs
          \<and> (\<not>ctd \<longrightarrow> has_rchild i \<and> xs!i\<^bold>\<ge>xs!lchild i \<and> xs!i\<^bold>\<ge>xs!rchild i)"
      and
      R = "measure (\<lambda>(xs,i,ctd). (if ctd then 1 else 0) + h - i)"    
    ]) 
    apply clarsimp_all
    apply (all \<open>(auto simp: in_heap_len_bound diff_less_mono2 A sift_down_invar_step wo_leI root_in_heap; fail)?\<close>)
    subgoal using A unfolding sift_down_invar_def is_heap_except_down_def by auto
    subgoal using A unfolding sift_down_invar_def is_heap_except_down_def by auto
    subgoal using asym sift_down_invar_step(2) wo_leI by blast
    subgoal by (simp add: diff_less_mono2 less_SucI)
    subgoal using wo_less_trans wo_not_le_imp_less by blast
    subgoal by (simp add: Suc_diff_le less_imp_le)
    subgoal using asym sift_down_invar_step(1) wo_leI by blast
    subgoal by (simp add: diff_less_mono2 less_Suc_eq)
    subgoal using itrans wo_leI by blast 
    subgoal by (simp add: Suc_diff_le less_imp_le)
    subgoal unfolding sift_down_invar_def by simp
    subgoal by (meson lchild_of_no_rchild_term sift_down_invar_def sift_down_invar_step(3) sift_down_term1 wo_leD wo_leI wo_less_not_sym)
    subgoal by (meson lchild_of_no_rchild_term less_imp_le not_le sift_down_invar_def sift_down_lemma_left_no_right_child sift_down_term1)
    (*subgoal unfolding sift_down_invar_def by simp*)
    subgoal unfolding sift_down_invar_def by (meson wo_leI sift_down_term1 sift_down_term2 sift_down_term3)
    done
    
      
    
    
    
    
  text \<open>Deferred swap optimization\<close>
  definition sift_down1 :: "nat \<Rightarrow> 'a list \<Rightarrow> 'a list nres" where "sift_down1 i xs \<equiv> doN {
    ASSERT (in_heap i);
    v \<leftarrow> mop_list_get xs i;
    (xs,i,_) \<leftarrow> WHILEIT (\<lambda>(xs,i,ctd). in_heap i) (\<lambda>(xs,i,ctd). has_rchild i \<and> ctd) (\<lambda>(xs,i,ctd). doN {
      lc \<leftarrow> mop_list_get xs (lchild i);
      rc \<leftarrow> mop_list_get xs (rchild i);
    
      if lc \<^bold>< rc then
        if v \<^bold>< rc then doN {
          t \<leftarrow> mop_list_get xs (rchild i);
          xs \<leftarrow> mop_list_set xs i t;
          RETURN (xs,rchild i,True)
        } else RETURN (xs,i,False)
      else if v \<^bold>< lc then doN {
        t \<leftarrow> mop_list_get xs (lchild i);
        xs \<leftarrow> mop_list_set xs i t;
        RETURN (xs,lchild i,True)
      } else RETURN (xs,i,False)
    }) (xs,i,True);

    ASSERT (in_heap i);
    ASSERT (has_lchild i \<longrightarrow> lchild i < length xs);
    
    xs \<leftarrow> (if has_lchild i \<and> v \<^bold>< xs!lchild i then doN {
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
  

  (* Auxiliary definitions to reduce proof complexity in sepref-step.
    TODO: Without these, the sepref step gets really slow, which is another indication that we
      should separate the bound-proofs from the actual transfer step!
  *)
  definition [simp]: "mop_lchild2 i \<equiv> doN { ASSERT (2*i+1<h); RETURN (2*i+1) }"
  definition [simp]: "mop_rchild2 i \<equiv> doN { ASSERT (2*i+2<h); RETURN (2*i+2) }"
  definition [simp]: "has_rchild2 i \<equiv> i<(h-l-1) div 2"
  definition [simp]: "has_lchild2 i \<equiv> i<(h-l) div 2"
  definition [simp]: "mop_geth2 xs i \<equiv> doN { ASSERT(l+i\<le>h); mop_list_get xs (l+i) }"
  definition [simp]: "mop_seth2 xs i x \<equiv> doN { ASSERT(l+i\<le>h); mop_list_set xs (l+i) x }"

end  
  
concrete_definition mop_lchild3 is heap_context.mop_lchild2_def
concrete_definition mop_rchild3 is heap_context.mop_rchild2_def
concrete_definition has_rchild3 is heap_context.has_rchild2_def
concrete_definition has_lchild3 is heap_context.has_lchild2_def
concrete_definition mop_geth3   is heap_context.mop_geth2_def
concrete_definition mop_seth3   is heap_context.mop_seth2_def
  
lemmas h_aux_refines = mop_lchild3.refine mop_rchild3.refine has_rchild3.refine 
  has_lchild3.refine mop_geth3.refine mop_seth3.refine  

context heap_context begin  
  
  definition sift_down2 :: "nat \<Rightarrow> 'a list \<Rightarrow> 'a list nres" where "sift_down2 i\<^sub>0 xs \<equiv> doN {
    ASSERT (l\<le>i\<^sub>0 \<and> l<h);
    let i = i\<^sub>0 - l;
    v \<leftarrow> mop_geth3 l h xs i;
    
    (xs,i,_) \<leftarrow> WHILEIT (\<lambda>(xs,i,ctd). i<h-l) (\<lambda>(xs,i,ctd). has_rchild3 l h i \<and> ctd) (\<lambda>(xs,i,ctd). doN {
      lci \<leftarrow> mop_lchild3 h i;
      rci \<leftarrow> mop_rchild3 h i;
      lc \<leftarrow> mop_geth3 l h xs lci;
      rc \<leftarrow> mop_geth3 l h xs rci;
    
      if lc \<^bold>< rc then
        if v \<^bold>< rc then doN {
          xs \<leftarrow> mop_seth3 l h xs i rc;
          RETURN (xs,rci,True)
        } else RETURN (xs,i,False)
      else if v \<^bold>< lc then doN {
        xs \<leftarrow> mop_seth3 l h xs i lc;
        RETURN (xs,lci,True)
      } else RETURN (xs,i,False)
    }) (xs,i,True);
    
    if has_lchild3 l h i then doN {
      lci \<leftarrow> mop_lchild3 h i;
      lc \<leftarrow> mop_geth3 l h xs lci;
      if v \<^bold>< lc then doN {
        xs \<leftarrow> mop_seth3 l h xs i lc;
        xs \<leftarrow> mop_seth3 l h xs lci v;
        RETURN xs
      } else doN {
        xs \<leftarrow> mop_seth3 l h xs i v;
        RETURN xs
      }  
    } else doN {
      xs \<leftarrow> mop_seth3 l h xs i v;
      RETURN xs
    }  
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
      "i'<x \<longleftrightarrow> i<x-l"
      "i'\<le>h \<longleftrightarrow> i\<le>h-l"
    using assms
    thm lchild_ihs
    unfolding idx_shift_rel_def 
      in_heap_def 
      has_rchild_def rchild_def
      has_lchild_def lchild_def
    by auto
    

  lemma sift_down2_refine: "sift_down2 i xs \<le> \<Down>Id (sift_down1 i xs)"
    unfolding sift_down1_def sift_down2_def 
    unfolding h_aux_refines[OF heap_context_axioms, symmetric]
    supply [simp del] = conc_Id
    apply (simp cong: if_cong)
    apply (rewrite at "let i=i-l in _" Let_def)
    apply (intro refine0)
    apply (all \<open>unfold in_heap_def; simp_all; fail \<close>) [3]
    apply (rule bind_refine)
    focus
      apply refine_rcg
      supply [refine_dref_RELATES] = RELATESI[of ihs_opt_rel]  
      apply refine_dref_type
      apply (simp_all add: ihs_opt_rel_alt)
      apply (all \<open>(determ \<open>elim conjE\<close>)?; simp?\<close>)
      apply (clarsimp_all simp: idx_shift_adjust ihs_opt_rel_alt simp del: in_heap_simps)
      unfolding in_heap_def idx_shift_rel_def ihs_opt_rel_alt
      apply (auto simp: algebra_simps)
      solved
    subgoal for s s'
      supply [split del] = if_split
      apply (cases s; simp)
      apply (cases s'; simp)
      apply (split if_split; intro conjI impI; simp)
      subgoal
        apply refine_rcg
        apply (simp_all add: ihs_opt_rel_alt)
        apply (all \<open>determ \<open>elim conjE\<close>; simp?\<close>)
        apply (auto simp: algebra_simps idx_shift_adjust)
        done
      subgoal  
        apply (split if_split, intro impI conjI refine0)
        apply (simp_all add: ihs_opt_rel_alt)
        apply (all \<open>determ \<open>elim conjE\<close>; simp?\<close>)
        apply (auto simp: ihs_opt_rel_alt idx_shift_adjust algebra_simps)
        done
    done
  done  

    
end        

thm mop_lchild3.refine
    
concrete_definition sift_down3 for less l h i\<^sub>0 xs is heap_context.sift_down2_def 



    
context heap_context begin  

  lemma sift_down3_full_refine: "sift_down3 (\<^bold><) l h i xs \<le> sift_down i xs"
  proof -
    note sift_down3.refine[OF heap_context_axioms, symmetric, THEN meta_eq_to_obj_eq]
    also note sift_down2_refine 
    also note sift_down1_refine 
    finally show ?thesis by simp
  qed

  lemmas sift_down3_btu_correct = order_trans[OF sift_down3_full_refine sift_down_btu_correct]
  lemmas sift_down3_restore_correct = order_trans[OF sift_down3_full_refine sift_down_restore_correct]
  
  definition "heapify_btu xs\<^sub>0 \<equiv> doN {
    ASSERT(h>0);
    (xs,l') \<leftarrow> WHILET 
      (\<lambda>(xs,l'). l'>l) 
      (\<lambda>(xs,l'). doN {
        ASSERT (l'>0);
        let l'=l'-1;
        xs \<leftarrow> sift_down3 (\<^bold><) l h l' xs;
        RETURN (xs,l')
      })
      (xs\<^sub>0,h-1);
    RETURN xs
  }"    
    
  lemma heapify_btu_correct: "\<lbrakk> l<h; h\<le>length xs\<^sub>0 \<rbrakk> \<Longrightarrow> heapify_btu xs\<^sub>0 \<le> SPEC (\<lambda>xs. slice_eq_mset l h xs xs\<^sub>0 \<and> is_heap xs)"
    unfolding heapify_btu_def
    apply simp
    apply (refine_vcg WHILET_rule[where I="\<lambda>(xs,l'). heapify_btu_invar xs\<^sub>0 l' xs \<and> l'\<ge>l" and R="measure snd"] sift_down3_btu_correct)
    apply (all \<open>(auto;fail)?\<close>)
    apply clarsimp_all (* Required to get rid of local variables that will obfuscate locale abbreviations! *)
    subgoal by (simp add: heapify_btu_invar_def btu_heapify_init)
    subgoal by (auto simp: heapify_btu_invar_def)
    subgoal by (auto simp: heapify_btu_invar_def btu_heapify_term)
    done
    
    
end

concrete_definition heapify_btu1 for less l h xs\<^sub>0 is heap_context.heapify_btu_def


context heap_context begin  
  lemmas heapify_btu1_correct = heapify_btu_correct[unfolded heapify_btu1.refine[OF heap_context_axioms]]
end

context weak_ordering begin

  (* TODO: We keep \<le> out of the definition (although it occurs in invariants). 
    Otherwise, getting rid of the \<le> ghost parameter is difficult!
  *)

  definition heapsort :: "'a list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a list nres" where "heapsort xs\<^sub>0 l h\<^sub>0 \<equiv> doN {
    ASSERT (l\<le>h\<^sub>0);
    if h\<^sub>0-l > 1 then doN {
      xs \<leftarrow> heapify_btu1 (\<^bold><) l h\<^sub>0 xs\<^sub>0;
      
      (xs,h)\<leftarrow>WHILEIT (\<lambda>(xs,h). 
          l<h \<and> h\<le>h\<^sub>0 
        \<and> heap_context.is_heap (le_by_lt (\<^bold><)) l h xs
        \<and> slice_eq_mset l h\<^sub>0 xs xs\<^sub>0
        \<and> sorted_wrt_lt (\<^bold><) (slice h h\<^sub>0 xs)
        \<and> (\<forall>a\<in>set (slice l h xs). \<forall>b\<in>set (slice h h\<^sub>0 xs). (le_by_lt (\<^bold><)) a b)
      ) 
        (\<lambda>(xs,h). Suc l < h) 
        (\<lambda>(xs,h). doN {
          ASSERT (h>0);
          xs \<leftarrow> mop_list_swap xs l (h-1);
          xs \<leftarrow> sift_down3 (\<^bold><) l (h-1) l xs;
          RETURN (xs,h-1)
        })
        (xs,h\<^sub>0);
      
      RETURN xs
    } else
      RETURN xs\<^sub>0
  }"
  
  
    
  lemma heapsort_correct:
    assumes "l\<le>h\<^sub>0" "h\<^sub>0\<le>length xs\<^sub>0"
    shows "heapsort xs\<^sub>0 l h\<^sub>0 \<le> SPEC (\<lambda>xs. slice_eq_mset l h\<^sub>0 xs xs\<^sub>0 \<and> sorted_wrt_lt (\<^bold><) (slice l h\<^sub>0 xs))"
  proof -
    interpret initial: heap_context "(\<^bold>\<le>)" "(\<^bold><)" l h\<^sub>0 by unfold_locales fact
  
    show ?thesis  
      using assms unfolding heapsort_def le_by_lt
      apply (refine_vcg WHILEIT_rule[where R="measure snd"] initial.heapify_btu1_correct )
      apply (all \<open>(auto dest: slice_eq_mset_eq_length;fail)?\<close>)
      
      apply clarsimp
      subgoal premises prems for xs\<^sub>1 xs h proof -
        (* TODO: This is the argument that swapping the max-element to the end will preserve the
            sortedness criteria. Though apparently simple, the reasoning seems to be much too complex here.
            Try to improve on that!
        *)
        interpret heap_context "(\<^bold>\<le>)" "(\<^bold><)" l h using prems by (unfold_locales) auto
        interpret N: heap_context "(\<^bold>\<le>)" "(\<^bold><)" l "h-Suc 0" using prems by (unfold_locales) auto
        
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
          then have G2: "sorted_wrt (\<^bold>\<le>) (slice (h - Suc 0) h\<^sub>0 xs')" 
            using prems 
            by (auto)
  
          have [simp]: "slice l (h - Suc 0) (swap xs l (h - Suc 0)) = xs!(h-Suc 0)#(slice (Suc l) (h-Suc 0) xs)"
            apply (rule nth_equalityI)
            apply (auto simp: nth_list_update slice_nth swap_nth Suc_diff_Suc \<open>Suc l < h\<close>)
            done
            
          have "in_heap (h - Suc 0)"
            unfolding in_heap_def apply simp
            using \<open>Suc l < h\<close> by linarith
          
          have G3: "\<forall>a \<in> set (slice l (h - Suc 0) xs'). \<forall>b \<in> set (slice (h - Suc 0) h\<^sub>0 xs'). a\<^bold>\<le>b" 
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
          by (auto simp: slice_split_hd le_by_lt)
      qed
      subgoal
        by (simp add: sorted_wrt01)
      done
      
  qed
end

concrete_definition heapsort1 for less xs\<^sub>0 l h\<^sub>0 is weak_ordering.heapsort_def


context weak_ordering begin  
  lemmas heapsort1_correct = heapsort_correct[unfolded heapsort1.refine[OF weak_ordering_axioms]]
end



     
  
context sort_impl_context begin

sepref_register mop_lchild3 mop_rchild3 has_rchild3 has_lchild3 mop_geth3  mop_seth3  
sepref_def mop_lchild_impl [llvm_inline] is "uncurry mop_lchild3" :: "size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k \<rightarrow>\<^sub>a size_assn"
  unfolding mop_lchild3_def apply (annot_snat_const "TYPE (size_t)") by sepref
  
sepref_def mop_rchild_impl [llvm_inline] is "uncurry mop_rchild3" :: "size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k \<rightarrow>\<^sub>a size_assn"
  unfolding mop_rchild3_def apply (annot_snat_const "TYPE (size_t)") by sepref
  
sepref_def has_lchild_impl [llvm_inline] is "uncurry2 (RETURN ooo has_lchild3)" :: "[\<lambda>((l,h),i). l\<le>h]\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k \<rightarrow> bool1_assn"
  unfolding has_lchild3_def apply (annot_snat_const "TYPE (size_t)") by sepref
  
sepref_def has_rchild_impl [llvm_inline] is "uncurry2 (RETURN ooo has_rchild3)" :: "[\<lambda>((l,h),i). l<h]\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k \<rightarrow> bool1_assn"
  unfolding has_rchild3_def apply (annot_snat_const "TYPE (size_t)") by sepref

sepref_def mop_geth_impl [llvm_inline] is "uncurry3 mop_geth3" :: "size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k *\<^sub>a arr_assn\<^sup>k *\<^sub>a size_assn\<^sup>k \<rightarrow>\<^sub>a elem_assn"
  unfolding mop_geth3_def by sepref
  
sepref_def mop_seth_impl [llvm_inline] is "uncurry4 mop_seth3" :: "size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k *\<^sub>a arr_assn\<^sup>d *\<^sub>a size_assn\<^sup>k *\<^sub>a elem_assn\<^sup>k \<rightarrow>\<^sub>a arr_assn"
  unfolding mop_seth3_def by sepref
  
sepref_register "sift_down3 (\<^bold><)"
sepref_def sift_down_impl is "uncurry3 (PR_CONST (sift_down3  (\<^bold><)))" :: "size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k *\<^sub>a arr_assn\<^sup>d \<rightarrow>\<^sub>a arr_assn"
  unfolding sift_down3_def PR_CONST_def
  apply sepref_dbg_keep
  done

sepref_register "heapify_btu1 (\<^bold><)"
sepref_def heapify_btu_impl is "uncurry2 (PR_CONST (heapify_btu1  (\<^bold><)))" :: "size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k *\<^sub>a arr_assn\<^sup>d \<rightarrow>\<^sub>a arr_assn"
  unfolding heapify_btu1_def PR_CONST_def
  apply (annot_snat_const "TYPE (size_t)")
  by sepref
  
sepref_register "heapsort1 (\<^bold><)"
sepref_def heapsort_impl is "uncurry2 (PR_CONST (heapsort1  (\<^bold><)))" :: "arr_assn\<^sup>d *\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k \<rightarrow>\<^sub>a arr_assn"
  unfolding heapsort1_def PR_CONST_def
  apply (rewrite at "sift_down3 _ _ _ \<hole> _" fold_COPY)
  apply (annot_snat_const "TYPE (size_t)")
  by sepref

sepref_register heapsort    
lemmas heapsort_hnr[sepref_fr_rules] = heapsort_impl.refine[unfolded heapsort1.refine[OF weak_ordering_axioms,symmetric]]  
  
  
end  

(*  
global_interpretation heapsort_interp: sort_impl_context "(\<le>)" "(<)" ll_icmp_ult unat_assn
  defines heapsort_interp_mop_lchild_impl  = heapsort_interp.mop_lchild_impl 
      and heapsort_interp_mop_rchild_impl  = heapsort_interp.mop_rchild_impl 
      and heapsort_interp_has_rchild_impl  = heapsort_interp.has_rchild_impl 
      and heapsort_interp_has_lchild_impl  = heapsort_interp.has_lchild_impl 
      and heapsort_interp_mop_geth_impl    = heapsort_interp.mop_geth_impl  
      and heapsort_interp_mop_seth_impl    = heapsort_interp.mop_seth_impl  
      and heapsort_interp_sift_down_impl   = heapsort_interp.sift_down_impl
      and heapsort_interp_heapify_btu_impl = heapsort_interp.heapify_btu_impl
      and heapsort_interp_heapsort_impl    = heapsort_interp.heapsort_impl
  by (rule unat_sort_impl_context)

export_llvm "heapsort_interp_heapsort_impl :: 64 word ptr \<Rightarrow> _" is "uint64_t* heapsort(uint64_t*, int64_t,int64_t)"
  file "../code/heapsort.ll"

*)

end
