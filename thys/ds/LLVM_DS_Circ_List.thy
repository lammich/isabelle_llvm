section \<open>Circular Singly Linked Lists\<close>
theory LLVM_DS_Circ_List
imports LLVM_DS_List_Seg
begin

text \<open>
  Example of circular lists, with efficient append, prepend, pop, and rotate
  operations.
  
  TODO: Add delete operation,. e.g. by iterating pop
\<close>

subsection \<open>Datatype Definition\<close>

type_synonym 'a cs_list = "'a node ptr"

definition "cs_list_assn \<equiv> mk_assn (\<lambda>xs p. lseg xs p p ** \<up>(xs=[] \<longleftrightarrow> p=null))"

lemma cs_list_assn_simps:
  "\<upharpoonleft>cs_list_assn xs null = \<up>(xs=[])"
  "\<upharpoonleft>cs_list_assn [] p = \<up>(p=null)"
  unfolding cs_list_assn_def 
  by (auto simp: sep_algebra_simps)


subsection \<open>Operations\<close>
subsubsection \<open>Allocate Empty List\<close>
definition cs_empty :: "'a::llvm_rep cs_list llM" where [llvm_code, llvm_inline]:
  "cs_empty \<equiv> Mreturn null"

lemma cs_empty_rule: "llvm_htriple \<box> cs_empty (\<lambda>r. \<upharpoonleft>cs_list_assn [] r)"
  unfolding cs_empty_def cs_list_assn_def
  by vcg

subsubsection \<open>Prepend Element\<close>

definition cs_prepend :: "'a::llvm_rep \<Rightarrow> 'a cs_list \<Rightarrow> 'a cs_list llM" where [llvm_code]:
  "cs_prepend x p \<equiv> 
    if p=null then doM {
      p \<leftarrow> ll_balloc;
      ll_store (Node x p) p;
      Mreturn p
    } else doM {
      n \<leftarrow> ll_load p;
      q \<leftarrow> ll_ref (Node (node.val n) (node.next n));
      ll_store (Node x q) p;
      Mreturn p
    }"

lemma cs_prepend_rule: 
  "llvm_htriple (\<upharpoonleft>cs_list_assn xs p) (cs_prepend x p) (\<lambda>r. \<upharpoonleft>cs_list_assn (x#xs) r)"
  unfolding cs_prepend_def cs_list_assn_def
  apply (cases "xs"; simp)
  apply vcg
  done

subsubsection \<open>Append Element\<close>
definition cs_append :: "'a::llvm_rep \<Rightarrow> 'a cs_list \<Rightarrow> 'a cs_list llM" where [llvm_code]:
  "cs_append x p \<equiv> doM {
    if p=null then doM {
      p \<leftarrow> ll_balloc;
      ll_store (Node x p) p;
      Mreturn p
    } else doM {
      n \<leftarrow> ll_load p;
      q \<leftarrow> ll_ref (Node (node.val n) (node.next n));
      ll_store (Node x q) p;
      Mreturn q
    }
  }"

lemma cs_append_rule: 
  "llvm_htriple (\<upharpoonleft>cs_list_assn xs p) (cs_append x p) (\<lambda>r. \<upharpoonleft>cs_list_assn (xs@[x]) r)"
  unfolding cs_append_def cs_list_assn_def
  apply (cases "xs"; simp add: lseg_append)
  apply vcg
  done

subsubsection \<open>Pop First Element\<close>

definition cs_pop :: "'a::llvm_rep cs_list \<Rightarrow> ('a\<times>'a cs_list) llM" where [llvm_code]:
  "cs_pop p \<equiv> doM {
    n\<^sub>1 \<leftarrow> ll_load p;
    let p\<^sub>2 = node.next n\<^sub>1;
    tmp \<leftarrow> ll_ptrcmp_eq p\<^sub>2 p;
    if to_bool tmp then doM {
      ll_free p;
      Mreturn (node.val n\<^sub>1,null) \<comment> \<open>Singleton list becomes empty list\<close>
    } else doM {
      n\<^sub>2 \<leftarrow> ll_load p\<^sub>2;
      ll_store n\<^sub>2 p;
      ll_free p\<^sub>2;
      Mreturn (node.val n\<^sub>1,p)
    }
  }"

  
lemma ll_bpto_not_same1: 
  "(\<upharpoonleft>ll_bpto x p \<and>* \<upharpoonleft>ll_bpto y p) = sep_false"  
  apply (auto simp: ll_bpto_def sep_algebra_simps ll_pto_not_same)
  by (simp add: ll_pto_not_same sep.mult.left_commute sep.mult_commute)

lemma ll_bpto_not_same2: 
  "(\<upharpoonleft>ll_bpto x p \<and>* \<upharpoonleft>ll_bpto y p ** F) = sep_false"  
  apply (auto simp: ll_bpto_def sep_algebra_simps ll_pto_not_same)
  by (simp add: ll_pto_not_same sep.mult.left_commute sep.mult_commute)

lemmas ll_bpto_not_same = ll_bpto_not_same1 ll_bpto_not_same2  
    
context  
begin
  interpretation llvm_prim_ctrl_setup .
  interpretation llvm_prim_arith_setup .
  
lemma cs_pop_rule: 
  "llvm_htriple (\<upharpoonleft>cs_list_assn (x#xs) p) (cs_pop p) (\<lambda>(y,p'). \<upharpoonleft>cs_list_assn xs p' ** \<up>(y=x))"
  unfolding cs_list_assn_def cs_pop_def
  apply (cases xs; simp)
  supply [simp] = ll_bpto_not_same
  apply vcg
  done

end
  
subsubsection \<open>Rotate\<close>

definition cs_rotate :: "'a::llvm_rep cs_list \<Rightarrow> 'a cs_list llM" where [llvm_code]:
  "cs_rotate p \<equiv> if p=null then Mreturn null else doM {
    n \<leftarrow> ll_load p;
    Mreturn (node.next n)
  }"

  
lemma list01_cases:
  obtains (Nil) "xs=[]" | (Sng) x where "xs=[x]" | (Long) x y xs' where "xs=x#y#xs'"
  by (rule remdups_adj.cases)
  
  
  
lemma cs_rotate_rule: 
  "llvm_htriple (\<upharpoonleft>cs_list_assn xs p) (cs_rotate p) (\<lambda>r. \<upharpoonleft>cs_list_assn (rotate1 xs) r)"
  unfolding cs_list_assn_def cs_rotate_def
  apply (cases xs rule: list01_cases; simp add: lseg_append)
  apply vcg
  done

subsection \<open>Test\<close>
definition [llvm_code]: "test \<equiv> doM {
  l \<leftarrow> cs_empty;
  l \<leftarrow> cs_append 1 l;
  l \<leftarrow> cs_append 2 l;
  l \<leftarrow> cs_append 3 l;
  l \<leftarrow> cs_prepend 4 l;
  l \<leftarrow> cs_rotate l;
  (v1,l)\<leftarrow>cs_pop l;
  (v2,l)\<leftarrow>cs_pop l;
  (v3,l)\<leftarrow>cs_pop l;
  (v4,l)\<leftarrow>cs_pop l;
  Mreturn (v1,v2,v3,v4)
}"

(* TODO: Move! *)

export_llvm 
  "cs_empty :: 64 word cs_list llM"
  "cs_prepend :: 64 word \<Rightarrow> _"
  "cs_append :: 64 word \<Rightarrow> _"
  "cs_pop :: 64 word cs_list \<Rightarrow> _"

export_llvm "test :: (64 word \<times> _) llM"

end
