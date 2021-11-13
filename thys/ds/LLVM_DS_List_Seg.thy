section \<open>Singly Linked List Segments\<close>
theory LLVM_DS_List_Seg
imports LLVM_DS_Block_Alloc
begin

subsection \<open>Nodes\<close>
text \<open>
  We define a node of a list to contain a data value and a next pointer.
\<close>

datatype 'a node = Node (val: 'a) ("next": "'a node ptr")
hide_const (open) node.val node.next

subsubsection \<open>Encoding to heap-representable\<close>

instantiation node :: (llvm_rep)llvm_rep
begin
  definition "to_val_node \<equiv> \<lambda>Node a b \<Rightarrow> LL_STRUCT [to_val a, to_val b]"
  definition "from_val_node p \<equiv> case llvm_val.the_fields p of [a,b] \<Rightarrow> Node (from_val a) (from_val b)"
  definition [simp]: "struct_of_node (_::(('a) node) itself) \<equiv> VS_STRUCT [struct_of TYPE('a), struct_of TYPE('a node ptr)]"
  definition [simp]: "init_node ::('a) node \<equiv> Node init init"
  
  instance
    apply standard
    unfolding from_val_node_def to_val_node_def struct_of_node_def init_node_def
    (* TODO: Clean proof here, not breaking abstraction barriers! *)
    apply (auto simp: to_val_word_def init_zero fun_eq_iff split: node.splits)
    subgoal for v v1 v2
      apply (cases v)
      apply (auto split: list.splits)
      done
    subgoal
      by (simp add: LLVM_Shallow.null_def to_val_ptr_def)
    done

end

subsubsection \<open>Setup for LLVM code export\<close>
text \<open>Declare structure to code generator.\<close>
lemma to_val_node[ll_to_val]: "to_val x = LL_STRUCT [to_val (node.val x), to_val (node.next x)]"
  apply (cases x)
  apply (auto simp: to_val_node_def)
  done

text \<open>Declare as named structure. Required b/c of circular reference.\<close>
lemma [ll_identified_structures]: "ll_is_identified_structure ''node'' TYPE(_ node)"  
  unfolding ll_is_identified_structure_def
  by simp

subsubsection \<open>Code Generator Preprocessor Setup\<close>  
text \<open>The next two are auxiliary lemmas\<close>
lemma node_insert_value:
  "ll_insert_value (Node x n) x' 0 = return (Node x' n)"
  "ll_insert_value (Node x n) n' (Suc 0) = return (Node x n')"

  apply (simp_all add: ll_insert_value_def llvm_insert_value_def Let_def checked_from_val_def 
                to_val_node_def from_val_node_def)
  done

lemma node_extract_value:
  "ll_extract_value (Node x n) 0 = return x"  
  "ll_extract_value (Node x n) (Suc 0) = return n"  
  apply (simp_all add: ll_extract_value_def llvm_extract_value_def Let_def checked_from_val_def 
                to_val_node_def from_val_node_def)
  done
  
text \<open>Lemmas to translate node construction and destruction\<close>
lemma inline_return_node[llvm_pre_simp]: "return (Node a x) = doM {
    r \<leftarrow> ll_insert_value init a 0;
    r \<leftarrow> ll_insert_value r x 1;
    return r
  }"
  apply (auto simp: node_insert_value)
  done

lemma inline_node_case[llvm_pre_simp]: "(case x of (Node a n) \<Rightarrow> f a n) = doM {
  a \<leftarrow> ll_extract_value x 0;
  n \<leftarrow> ll_extract_value x 1;
  f a n
}"  
  apply (cases x)
  apply (auto simp: node_extract_value)
  done
  
lemma inline_return_node_case[llvm_pre_simp]: "doM {return (case x of (Node a n) \<Rightarrow> f a n)} = doM {
  a \<leftarrow> ll_extract_value x 0;
  n \<leftarrow> ll_extract_value x 1;
  return (f a n)
}"  
  apply (cases x)
  apply (auto simp: node_extract_value)
  done
  
lemmas [llvm_inline] = node.val_def node.next_def

(* TODO: Move *)  

subsection \<open>List Segment Assertion\<close>
text \<open>
  Intuitively, \<open>lseg l p s\<close> describes a list starting at \<open>p\<close> and
  ending with a pointer \<open>s\<close>. The content of the list are \<open>l\<close>.
  Note that the pointer \<open>s\<close> may also occur earlier in the list, in which
  case it is handled as a usual next-pointer.
\<close>


fun lseg 
  :: "'a::llvm_rep list \<Rightarrow> 'a node ptr \<Rightarrow> 'a node ptr \<Rightarrow> ll_assn"
  where
  "lseg [] p s = \<up>(p=s)"
| "lseg (x#l) p s = (
    if p=null then sep_false 
    else (EXS q. \<upharpoonleft>ll_bpto (Node x q) p ** lseg l q s))"

lemma lseg_if_splitf1[simp]: 
  "lseg l null null = \<up>(l=[])"
  apply (cases l, simp_all)
  done

lemma lseg_if_splitf2[simp]: 
  "lseg (x#xs) p q 
    = (EXS n. \<upharpoonleft>ll_bpto (Node x n) p ** lseg xs n q ** \<up>(p\<noteq>null))"
  apply (cases p, simp_all add: sep_algebra_simps)
  done

subsection \<open>Lemmas\<close>

lemma lseg_Cons[simp]: "lseg (x#l) p s = (EXS q. \<upharpoonleft>ll_bpto (Node x q) p ** lseg l q s)"
  by simp
  
lemmas [simp del] = lseg.simps(2)  

lemma lseg_append: "lseg (xs@ys) p s = (EXS q. lseg xs p q ** lseg ys q s)"  
  apply (induction xs arbitrary: p)
  apply (auto simp: sep_algebra_simps pred_lift_extract_simps)
  done
  
corollary lseg_split: "lseg (xs@ys) p s \<turnstile> (EXS q. lseg xs p q ** lseg ys q s)"
  by (simp add: lseg_append)

corollary lseg_fuse: "lseg xs p q ** lseg ys q s \<turnstile> lseg (xs@ys) p s"
  by (metis entails_def lseg_append)

  
  
end
