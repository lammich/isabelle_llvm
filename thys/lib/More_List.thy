theory More_List
imports Main "HOL-Library.Multiset"
begin

subsection \<open>Swap two elements of a list, by index\<close>

(* Move to List *)

definition "swap l i j \<equiv> l[i := l!j, j:=l!i]"
lemma swap_nth[simp]: "\<lbrakk>i < length l; j<length l; k<length l\<rbrakk> \<Longrightarrow>
  swap l i j!k = (
    if k=i then l!j
    else if k=j then l!i
    else l!k
  )"
  unfolding swap_def
  by auto

lemma swap_set[simp]: "\<lbrakk> i < length l; j<length l \<rbrakk> \<Longrightarrow> set (swap l i j) = set l"  
  unfolding swap_def
  by auto

lemma swap_length[simp]: "length (swap l i j) = length l"  
  unfolding swap_def
  by auto

lemma swap_same[simp]: "swap l i i = l"
  unfolding swap_def by auto

lemma distinct_swap[simp]: 
  "\<lbrakk>i<length l; j<length l\<rbrakk> \<Longrightarrow> distinct (swap l i j) = distinct l"
  unfolding swap_def
  by auto

lemma map_swap: "\<lbrakk>i<length l; j<length l\<rbrakk> 
  \<Longrightarrow> map f (swap l i j) = swap (map f l) i j"
  unfolding swap_def 
  by (auto simp add: map_update)



(* Move to Multiset *)  

lemma swap_multiset[simp]: "\<lbrakk> i < length l; j<length l \<rbrakk> \<Longrightarrow> mset (swap l i j) = mset l"  
  unfolding swap_def
  by (auto simp: mset_swap)
  
  
  
  

end
