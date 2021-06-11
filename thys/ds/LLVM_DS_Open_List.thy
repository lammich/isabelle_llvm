section \<open>Open Singly Linked Lists\<close>
theory LLVM_DS_Open_List
imports LLVM_DS_List_Seg (*Imp_List_Spec*)
begin

subsection \<open>Definitions\<close>
type_synonym 'a os_list = "'a node ptr"

definition os_list_assn :: "('a list, ('a::llvm_rep) os_list) dr_assn" where
  "os_list_assn \<equiv> mk_assn (\<lambda>l p. lseg l p null)"

lemma os_list_assn_simps:
  "\<upharpoonleft>os_list_assn [] p = \<up>(p=null)"
  "\<upharpoonleft>os_list_assn xs null = \<up>(xs=[])"
  "\<upharpoonleft>os_list_assn (x#xs) p = (EXS q. \<upharpoonleft>ll_bpto (Node x q) p ** \<upharpoonleft>os_list_assn xs q)"
  unfolding os_list_assn_def
  subgoal by auto
  subgoal by auto
  subgoal by (cases "p=null") (auto simp: sep_algebra_simps)
  done
  
  
  
subsection \<open>Operations\<close>
subsubsection \<open>Allocate Empty List\<close>

definition os_empty :: "_ os_list llM" where [llvm_code, llvm_inline]:
  "os_empty \<equiv> return null"

lemma os_empty_rule[vcg_rules]: "llvm_htriple \<box> os_empty (\<lambda>r. \<upharpoonleft>os_list_assn [] r)"
  unfolding os_empty_def os_list_assn_def
  apply vcg
  done

subsubsection \<open>Delete\<close>  

partial_function (ners) os_delete :: "_ os_list \<Rightarrow> unit llM" where
  "os_delete p = doM { 
    if p=null then return () 
    else doM {
      n \<leftarrow> ll_load p;
      ll_free p;
      os_delete (node.next n)
    }
  }"

lemma os_delete_rule[vcg_rules]: 
  "llvm_htriple (\<upharpoonleft>os_list_assn xs p) (os_delete p) (\<lambda>_. \<box>)"  
proof (induction xs arbitrary: p)
  case Nil
  note [simp] = os_list_assn_simps
  show ?case 
    apply (subst os_delete.simps)
    by vcg
next
  case (Cons a xs)
  
  note [vcg_rules] = Cons.IH
  note [simp] = os_list_assn_simps
  
  interpret llvm_prim_ctrl_setup .
  
  show ?case 
    apply (subst os_delete.simps)
    apply vcg
    done
    
  
qed
  
  
  
  
subsubsection \<open>Emptiness check\<close>
text \<open>A linked list is empty, iff it is the null pointer.\<close>

find_consts bool "1 word"

definition os_is_empty :: "_ os_list \<Rightarrow> 1 word llM" where [llvm_code, llvm_inline]:
  "os_is_empty b \<equiv> return (from_bool (b = null))"

lemma os_is_empty_rule[vcg_rules]: 
  "llvm_htriple (\<upharpoonleft>os_list_assn xs b) (os_is_empty b) (\<lambda>r. \<upharpoonleft>os_list_assn xs b ** \<up>(r = from_bool (xs = [])))"
  unfolding os_is_empty_def os_list_assn_def
  apply (cases "b=null"; cases xs; simp)
  apply vcg
  done
  
subsubsection \<open>Prepend\<close>

text \<open>To push an element to the front of a list we allocate a new node which
  stores the element and the old list as successor. The new list is the new 
  allocated reference.\<close>

  
definition os_prepend :: "'a \<Rightarrow> 'a::llvm_rep os_list \<Rightarrow> 'a os_list llM" where [llvm_code, llvm_inline]:
  "os_prepend a n = doM { ll_ref (Node a n) }"

lemma os_prepend_rule[vcg_rules]:
  "llvm_htriple (\<upharpoonleft>os_list_assn xs n) (os_prepend x n) (\<lambda>r. \<upharpoonleft>os_list_assn (x # xs) r)"
  unfolding os_prepend_def os_list_assn_def
  apply vcg
  done

subsubsection\<open>Pop\<close>
text \<open>To pop the first element out of the list we look up the value and the
  reference of the node and return the pair of those.\<close>

definition os_pop :: "'a::llvm_rep os_list \<Rightarrow> ('a \<times> 'a os_list) llM" where
  [llvm_code]: "os_pop p = doM { n \<leftarrow> ll_load p; ll_free p; return (node.val n, node.next n) }"

lemma os_pop_rule[vcg_rules]:
  "xs \<noteq> [] \<Longrightarrow> llvm_htriple 
    (\<upharpoonleft>os_list_assn xs r) 
    (os_pop r) 
    (\<lambda>(x,r'). \<up>(x=hd xs) ** \<upharpoonleft>os_list_assn (tl xs) r')
  "
  apply (cases xs; simp)
  unfolding os_pop_def os_list_assn_def
  by vcg

subsubsection \<open>Reverse\<close>

text \<open>The following reversal function is equivalent to the one from 
  Imperative HOL. And gives a more difficult example.\<close>

partial_function (ners) os_reverse_aux 
  :: "'a::llvm_rep os_list \<Rightarrow> 'a os_list \<Rightarrow> 'a os_list llM" 
  where
  "os_reverse_aux q p = doM {
    if p=null then return q
    else doM {
      v \<leftarrow> ll_load p;
      ll_store (Node (node.val v) q) p;
      os_reverse_aux p (node.next v)
    }
  }"

lemmas [llvm_code] = os_reverse_aux.simps
  
lemma os_reverse_aux_simps[simp]:
  "os_reverse_aux q null = return q"
  "p\<noteq>null \<Longrightarrow> os_reverse_aux q p = doM {
      v \<leftarrow> ll_load p;
      ll_store (Node (node.val v) q) p;
      os_reverse_aux p (node.next v)
    }"
  apply (subst os_reverse_aux.simps)
  apply simp
  apply (subst os_reverse_aux.simps)
  apply simp
  done

  
definition [llvm_code, llvm_inline]: "os_reverse p = os_reverse_aux null p"

lemma os_reverse_aux_rule: 
  "llvm_htriple 
    (\<upharpoonleft>os_list_assn xs p ** \<upharpoonleft>os_list_assn ys q) 
    (os_reverse_aux q p)
    (\<lambda>r. \<upharpoonleft>os_list_assn ((rev xs) @ ys) r)"
proof (induct xs arbitrary: p q ys)
  case Nil 
  thus ?case
    supply [simp] = os_list_assn_simps
    apply vcg
    done
next
  case (Cons x xs)
  
  note [vcg_rules] = Cons.hyps[where ys = "x#ys"]
  note [simp, named_ss fri_prepare_simps] = os_list_assn_simps
  
  show ?case
    apply (cases "p\<noteq>null"; simp)
    by vcg

qed

lemma os_reverse_rule[vcg_rules]: "llvm_htriple 
  (\<upharpoonleft>os_list_assn xs p) 
  (os_reverse p) 
  (\<lambda>r. \<upharpoonleft>os_list_assn (rev xs) r)"
  unfolding os_reverse_def
  supply [simp] = os_list_assn_simps
  supply R = os_reverse_aux_rule[where ys="[]", simplified]
  supply [vcg_rules] = R
  by vcg
  

subsubsection \<open>Remove\<close>
 
text \<open>Remove all appearances of an element from a linked list.\<close>

partial_function (ners) os_rem 
  :: "'a::llvm_rep \<Rightarrow> 'a node ptr \<Rightarrow> 'a node ptr llM" 
  where 
  "os_rem x p = doM {
    if p=null then return null
    else doM {
      n \<leftarrow> ll_load p;
      q \<leftarrow> os_rem x (node.next n);
      if node.val n = x then doM {
        ll_free p;
        return q
      } else doM {
        ll_store (Node (node.val n) q) p;
        return p
      }
    } 
  }"

lemmas [llvm_code] = os_rem.simps  
  
lemma [simp]: 
  "os_rem x null = return null"
  "p\<noteq>null \<Longrightarrow> os_rem x p = doM {
      n \<leftarrow> ll_load p;
      q \<leftarrow> os_rem x (node.next n);
      if node.val n = x then doM {
        ll_free p;
        return q
      } else doM {
        ll_store (Node (node.val n) q) p;
        return p
      }
    }"
  apply (subst os_rem.simps, simp)+
  done

lemma os_rem_rule[vcg_rules]: 
  "llvm_htriple (\<upharpoonleft>os_list_assn xs p) (os_rem x p) (\<lambda>r. \<upharpoonleft>os_list_assn (removeAll x xs) r)"
proof (induct xs arbitrary: p x) (* Have to generalize over x, as 
    preprocessor introduces a new variable. *)
  case Nil 
  
  note [simp] = os_list_assn_simps
  show ?case
    apply vcg
    done
next
  case (Cons y xs) 
  
  note [vcg_rules] = Cons.hyps
  
  note [simp] = os_list_assn_simps
  show ?case 
    apply (cases "p=null"; simp)
    by vcg
  
qed

export_llvm 
  "os_empty :: 64 word node ptr llM"
  "os_is_empty :: 64 word node ptr \<Rightarrow> _"
  "os_prepend :: 64 word \<Rightarrow> _"
  "os_pop :: 64 word node ptr \<Rightarrow> _"
  "os_reverse:: 64 word node ptr \<Rightarrow> _"
  "os_rem :: 64 word \<Rightarrow> _"

  
  
end
