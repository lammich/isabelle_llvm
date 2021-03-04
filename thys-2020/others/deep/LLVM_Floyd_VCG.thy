theory LLVM_Floyd_VCG
imports Monad2 LLVM_Typecheck Sep_Algebra_Add
begin


definition "EXACT h h' \<equiv> h'=h"
lemma strictly_exact_EXACT[simp]: "strictly_exact (EXACT h)"
  unfolding EXACT_def by (auto intro: strictly_exactI)

lemma EXACT_split: "a##b \<Longrightarrow> EXACT (a+b) = (EXACT a ** EXACT b)"
  unfolding EXACT_def sep_conj_def by auto
  
lemma EXACT_zero[simp]: "EXACT 0 = \<box>" by (auto simp: sep_algebra_simps EXACT_def)

lemma EXACT_eq_iff[simp]: "EXACT a = EXACT b \<longleftrightarrow> a=b"
  unfolding EXACT_def by metis





typ val
typ vaddr
typ "val memory"

term \<open>(\<bowtie>)\<close>


fun va_disj :: "vaddr \<Rightarrow> vaddr \<Rightarrow> bool" where
  "va_disj [] _ \<longleftrightarrow> False"
| "va_disj _ [] \<longleftrightarrow> False"
| "va_disj (VA_ARRAY_IDX _ # _) (VA_FIELD_IDX _ # _) \<longleftrightarrow> True"
| "va_disj (VA_FIELD_IDX _ # _) (VA_ARRAY_IDX _ # _) \<longleftrightarrow> True"
| "va_disj (VA_ARRAY_IDX i # as) (VA_ARRAY_IDX j # bs) \<longleftrightarrow> (i=j \<longrightarrow> va_disj as bs)"
| "va_disj (VA_FIELD_IDX i # as) (VA_FIELD_IDX j # bs) \<longleftrightarrow> (i=j \<longrightarrow> va_disj as bs)"

lemma va_disj_add_simps[simp]: "\<not>va_disj uu []" by (cases uu) auto

lemma va_disj_irrefl[simp]: "\<not>(va_disj as as)"
  apply (induction as)
  subgoal by simp
  subgoal for a as by (cases a) auto
  done

lemma va_disj_sym: "va_disj as bs \<longleftrightarrow> va_disj bs as"
  by (induction as bs rule: va_disj.induct) auto
  

lemma array_struct_indepL_iff1[simp]: 
  "lower_lens (array_item\<^sub>L i) \<bowtie> lower_lens (struct_field\<^sub>L j)"
  apply unfold_locales
  by (auto simp: struct_field\<^sub>L_def array_item\<^sub>L_def is_VSTRUCT_def is_VARRAY_def)

lemma array_struct_indepL_iff2[simp]: 
  "lower_lens (struct_field\<^sub>L j) \<bowtie> lower_lens (array_item\<^sub>L i)"
  by (simp add: lens_indep_sym)
  
lemmas array_struct_indepL_iff = array_struct_indepL_iff1 array_struct_indepL_iff2
  
lemma array_item\<^sub>L_rn[simp]: "rnlens (lower_lens (array_item\<^sub>L i))"
  apply (rule rnlensI[where x="VINT (Inr (lconst 32 1))" and y="VINT (Inr (lconst 32 0))" and s="VARRAY (replicate (i+1) undefined)"])
  by auto

lemma struct_field\<^sub>L_rn[simp]: "rnlens (lower_lens (struct_field\<^sub>L i))"
  apply (rule rnlensI[where x="VINT (Inr (lconst 32 1))" and y="VINT (Inr (lconst 32 0))" and s="VSTRUCT (replicate (i+1) undefined)"])
  by auto
  
  
lemma array_array_indepL_iff[simp]: "lower_lens (array_item\<^sub>L i) \<bowtie> lower_lens (array_item\<^sub>L j) \<longleftrightarrow> i\<noteq>j"  
  apply rule
  subgoal by auto
  subgoal
    apply unfold_locales
    by (auto simp: struct_field\<^sub>L_def array_item\<^sub>L_def is_VARRAY_def list_update_swap)
  done
  
lemma struct_struct_indepL_iff[simp]: "lower_lens (struct_field\<^sub>L i) \<bowtie> lower_lens (struct_field\<^sub>L j) \<longleftrightarrow> i\<noteq>j"  
  apply rule
  subgoal by auto
  subgoal
    apply unfold_locales
    by (auto simp: struct_field\<^sub>L_def array_item\<^sub>L_def is_VSTRUCT_def list_update_swap)
  done

  
(* TODO: Move *)  
lemma rnl_id[simp]: "rnlens (id\<^sub>L::'a\<Longrightarrow>'a) \<longleftrightarrow> (\<exists>x y::'a. x\<noteq>y)"  
  by (auto simp: rnlens_def)
  
lemma rnl_vai[simp]: "rnlens (lower_lens (lens_of_vai a))"
  by (cases a)  auto
  
lemma rnl_vaddr[simp]: "rnlens (lower_lens (lens_of_vaddr a))"
  by (induction a) auto
  
(* TODO: <-- direction should also hold, but requires some lemmas on lens composition and indep *)    
lemma "va_disj a b \<Longrightarrow> lower_lens (lens_of_vaddr a) \<bowtie> lower_lens (lens_of_vaddr b)"  
  apply (induction a b rule: va_disj.induct)
  apply (auto) []
  apply (auto) []
  apply (auto simp: lens_indep_extend2) []
  apply (auto simp: lens_indep_extend2) []
  subgoal for i as j bs
    apply (cases "i=j")
    apply (auto simp: lens_indep_extend2 lens_indep_left_comp)
    done
  subgoal for i as j bs
    apply (cases "i=j")
    apply (auto simp: lens_indep_extend2 lens_indep_left_comp)
    done
  done    
  
  
datatype primval = PVINT "nat + lint" | PVPTR "addr option option"
  
  
definition "va_disj' A B \<equiv> \<forall>a\<in>dom A. \<forall>b\<in>dom B. va_disj a b"

lemma va_disj'_imp_dom_disj[simp]: "va_disj' A B \<Longrightarrow> dom A \<inter> dom B = {}"
  apply (auto simp: va_disj'_def)
  by (meson domI va_disj_irrefl)

  
  
  
typedef va_sep = "{ as::vaddr \<rightharpoonup> primval . \<forall>a\<in>dom as. \<forall>b\<in>dom as. a=b \<or> va_disj a b }" by auto
setup_lifting type_definition_va_sep

instantiation va_sep :: "{unique_zero_sep_algebra, stronger_sep_algebra}" begin

  lift_definition sep_disj_va_sep :: "va_sep \<Rightarrow> va_sep \<Rightarrow> bool" is "va_disj'" .
  lift_definition plus_va_sep :: "va_sep \<Rightarrow> va_sep \<Rightarrow> va_sep" is "\<lambda>as bs. if va_disj' as bs then as++bs else as"
    by (auto 6 3 split: if_splits simp: Ball_def va_disj_sym va_disj'_def simp: domIff)

  lift_definition zero_va_sep :: va_sep is "Map.empty" by auto
      
  instance
    apply standard
    apply (transfer; auto simp: va_disj'_def)
    apply (transfer; auto 0 3 simp: va_disj'_def intro: va_disj_sym[THEN iffD1]) 
    apply (transfer; auto)
    apply (determ \<open>transfer\<close>; auto 0 3 simp: va_disj'_def map_add_comm intro: domI va_disj_sym[THEN iffD1])
    apply (determ transfer; auto simp: va_disj'_def domI)
    apply (determ transfer; auto  simp: va_disj'_def domI)
    apply (determ transfer; auto  simp: va_disj'_def domI)
    apply (determ transfer) using va_disj'_imp_dom_disj apply fastforce
    apply (determ transfer; auto  simp: va_disj'_def domI)
    done
    
end  

(* TODO: Move *)
lemma size_list_nth_estimation[termination_simp]: 
  "x1 < length vs \<Longrightarrow> size (vs ! x1) < Suc (size_list size vs)"
  by (meson less_irrefl_nat not_less_eq nth_mem size_list_estimation)

lemma size_enumerate_estimation[termination_simp]:
   "(a, b) \<in> list.set (List.enumerate 0 vs) \<Longrightarrow> size b < Suc (size_list size vs)"  
  by (metis enumerate_eq_zip lessI not_less set_zip_rightD size_list_estimation')
  
  
lift_definition va_int :: "(nat+lint) \<Rightarrow> va_sep" is "\<lambda>i. [ [] \<mapsto> PVINT i]" by auto
lift_definition va_ptr :: "addr option option \<Rightarrow> va_sep" is "\<lambda>a. [ [] \<mapsto> PVPTR a]" by auto
lift_definition va_in_array :: "nat \<Rightarrow> va_sep \<Rightarrow> va_sep" is "\<lambda>i m. \<lambda>VA_ARRAY_IDX j#as\<Rightarrow> if i=j then m as else None | _ \<Rightarrow> None"
  by (fastforce split: list.splits va_item.splits if_splits)
lift_definition va_in_struct :: "nat \<Rightarrow> va_sep \<Rightarrow> va_sep" is "\<lambda>i m. \<lambda>VA_FIELD_IDX j#as\<Rightarrow> if i=j then m as else None | _ \<Rightarrow> None"
  by (fastforce split: list.splits va_item.splits if_splits)


fun va_cons :: "va_item \<Rightarrow> va_sep \<Rightarrow> va_sep" where
  "va_cons (VA_ARRAY_IDX i) = va_in_array i"
| "va_cons (VA_FIELD_IDX i) = va_in_struct i"
  
definition va_append :: "vaddr \<Rightarrow> va_sep \<Rightarrow> va_sep" where "va_append \<equiv> foldr va_cons"

lemma va_append_append_eq[simp]: "va_append a (va_append b s) = va_append (a@b) s"
  by (auto simp: va_append_def)

lemma va_append_Nil[simp]: "va_append [] s = s"
  by (auto simp: va_append_def)
    
  
fun val_\<alpha> :: "val \<Rightarrow> va_sep" where
  "val_\<alpha> (VINT i) = va_int i"
| "val_\<alpha> (VPTR a) = va_ptr a"
| "val_\<alpha> (VARRAY vs) = (fold (\<lambda>(i,v) s. s + va_in_array i (val_\<alpha> v)) (List.enumerate 0 vs) 0)"
| "val_\<alpha> (VSTRUCT vs) = (fold (\<lambda>(i,v) s. s + va_in_struct i (val_\<alpha> v)) (List.enumerate 0 vs) 0)"
  
lemma va_prim_dj:
  "va_int i ## x \<longleftrightarrow> x=0"    
  "va_ptr p ## x \<longleftrightarrow> x=0"
  by (determ transfer; auto simp: va_disj'_def)+

lemma va_array_struct_dj:
  "va_in_array i v ## va_in_struct j v'"
  "va_in_struct j v' ## va_in_array i v"
  by (determ transfer; auto simp: va_disj'_def split: list.splits va_item.splits if_splits)+
  
lemma va_array_array_dj:
  "va_in_array i v ## va_in_array j v' \<longleftrightarrow> i\<noteq>j \<or> v##v'"
  apply (determ transfer)
  apply (rule)
  subgoal by (force simp: va_disj'_def dom_def split: list.splits va_item.splits if_splits)
  subgoal by (auto simp: va_disj'_def dom_def split: list.splits va_item.splits if_splits)
  done

lemma va_struct_struct_dj:
  "va_in_struct i v ## va_in_struct j v' \<longleftrightarrow> i\<noteq>j \<or> v##v'"
  apply (determ transfer)
  apply (rule)
  subgoal by (force simp: va_disj'_def dom_def split: list.splits va_item.splits if_splits)
  subgoal by (auto simp: va_disj'_def dom_def split: list.splits va_item.splits if_splits)
  done
  
lemmas va_djs[simp] = va_prim_dj va_array_struct_dj va_array_array_dj va_struct_struct_dj

lemma va_cons_dj_iff: "va_cons a x ## va_cons b y \<longleftrightarrow> (a=b \<longrightarrow> x##y)"
  by (cases a; cases b) auto

lemma va_append_same_dj_iff[simp]: "va_append a x ## va_append a y \<longleftrightarrow> (x##y)"
  apply (induction a)
  apply (auto simp: va_append_def va_cons_dj_iff)
  done
  
lemma to_va_append:
  "va_in_array i s = va_append [VA_ARRAY_IDX i] s"
  "va_in_struct i s = va_append [VA_FIELD_IDX i] s"
  "va_cons a s = va_append [a] s"
  by (auto simp: va_append_def)
  
  
  
  
term EXACT

  
lemma va_in_array_comm_plus[simp]: "va_in_array i (s+t) = va_in_array i s + va_in_array i t"  
  apply transfer
  apply (rule ext)
  apply (auto 0 0 split: list.splits va_item.splits option.splits if_splits simp: map_add_def)
  apply (auto 0 0 simp: va_disj'_def split: list.splits va_item.splits option.splits if_splits)
  apply (auto simp: dom_def) []
  apply (force simp: dom_def split: list.splits va_item.splits option.splits if_splits) []
  done

lemma va_in_struct_comm_plus[simp]: "va_in_struct i (s+t) = va_in_struct i s + va_in_struct i t"  
  apply transfer
  apply (rule ext)
  apply (auto 0 0 split: list.splits va_item.splits option.splits if_splits simp: map_add_def)
  apply (auto 0 0 simp: va_disj'_def split: list.splits va_item.splits option.splits if_splits)
  apply (auto simp: dom_def) []
  apply (force simp: dom_def split: list.splits va_item.splits option.splits if_splits) []
  done
  
  
lemma va_cons_comm_plus[simp]: "va_cons a (s\<^sub>1+s\<^sub>2) = va_cons a s\<^sub>1 + va_cons a s\<^sub>2"  
  by (cases a; auto)
  
lemma va_append_comm_plus[simp]:  "va_append a (s\<^sub>1+s\<^sub>2) = va_append a s\<^sub>1 + va_append a s\<^sub>2"  
  by (induction a) (auto simp: va_append_def)
  
lemma va_in_x_zero[simp]:
  "va_in_array i 0 = 0"  
  "va_in_struct i 0 = 0"  
  by (determ transfer; auto intro!: ext split: list.splits va_item.splits; fail)+
  
lemma va_cons_zero[simp]: "va_cons a 0 = 0"  
  by (cases a) auto
  
lemma va_append_zero[simp]: "va_append a 0 = 0"  
  by (induction a) (auto simp: va_append_def)
  
  
definition "points_to a v \<equiv> EXACT (va_append a (val_\<alpha> v))"
  
find_theorems "List.enumerate _ (_@_) "


lemma fold_in_array_disj_aux: "i\<ge>length xs \<Longrightarrow> fold (\<lambda>(i, v) s. s + va_in_array i (val_\<alpha> v)) (List.enumerate 0 xs) 0 ## va_in_array i (val_\<alpha> v)"
  apply (induction xs arbitrary: i v rule: rev_induct)
  apply (auto simp: enumerate_append_eq)
  done
  
lemma fold_in_struct_disj_aux: "i\<ge>length xs \<Longrightarrow> fold (\<lambda>(i, v) s. s + va_in_struct i (val_\<alpha> v)) (List.enumerate 0 xs) 0 ## va_in_struct i (val_\<alpha> v)"
  apply (induction xs arbitrary: i v rule: rev_induct)
  apply (auto simp: enumerate_append_eq)
  done
         
  

lemma pto_split_array:
  "points_to a (VARRAY xs) = (\<And>* map (\<lambda>(i,x). points_to (a@[VA_ARRAY_IDX i]) x) (List.enumerate 0 xs))"
  apply (auto simp: points_to_def)
  apply (induction xs rule: rev_induct)
  apply (auto simp: enumerate_append_eq EXACT_split fold_in_array_disj_aux sep_algebra_simps)
  apply (auto simp: to_va_append)
  done

lemma pto_split_struct:
  "points_to a (VSTRUCT xs) = (\<And>* map (\<lambda>(i,x). points_to (a@[VA_FIELD_IDX i]) x) (List.enumerate 0 xs))"
  apply (auto simp: points_to_def)
  apply (induction xs rule: rev_induct)
  apply (auto simp: enumerate_append_eq EXACT_split fold_in_struct_disj_aux sep_algebra_simps)
  apply (auto simp: to_va_append)
  done

xxx, ctd here: Towards separation logic and rules.  
  1. Separate out memory model from control flow and deep embedding. 
  2. Transfer sep-algebra
  3. Use generic block-allocator in memory model, with sep-algebra
  4. Transfer/adapt tooling from IMPlusPlus/ ImpHOL-VCG
   


  
  
lemma "va_append"  
  


lemma "va_append [VA_ARRAY_IDX 2, VA_FIELD_IDX 1] (va_int i) = foos"
  apply (simp add: va_append_def)


definition "val_assn v \<equiv> EXACT (val_\<alpha> v)"

definition "fold_idx f l a \<equiv> fold f (zip l [0..<length l]) a"

find_theorems List.enumerate



lemma "val_assn (VSTRUCT flds) = fold (\<lambda>(i,v). va_in_struct i (val_assn v)) (List.enumerate 0 flds) \<box>"
  unfolding val_assn_def
  apply (simp)



oops
xxx, ctd here: Derive assertions, and show how to combine/split them?


  
  oops
  ; auto simp: va_disj'_def split: list.splits va_item.splits if_splits)
  
  
  
  
  
fun val_\<alpha>_aux :: "val \<Rightarrow> vaddr \<rightharpoonup> primval" where
  "val_\<alpha>_aux (VINT i) = [ [] \<mapsto> PVINT i ]"
| "val_\<alpha>_aux (VPTR a) = [ [] \<mapsto> PVPTR a ]"
| "val_\<alpha>_aux (VARRAY vs) = (\<lambda>VA_ARRAY_IDX i # as \<Rightarrow> if i<length vs then val_\<alpha>_aux (vs!i) as else None | _ \<Rightarrow> None)"
| "val_\<alpha>_aux (VSTRUCT vs) = (\<lambda>VA_FIELD_IDX i # as \<Rightarrow> if i<length vs then val_\<alpha>_aux (vs!i) as else None | _ \<Rightarrow> None)"


lemma val_\<alpha>_aux_dj: "as\<in>dom (val_\<alpha>_aux v) \<Longrightarrow> bs \<in> dom (val_\<alpha>_aux v) \<Longrightarrow> as\<noteq>bs \<Longrightarrow> va_disj as bs"
  apply (induction v arbitrary: as bs rule: val_\<alpha>_aux.induct)
  apply (auto split: list.splits va_item.splits if_splits; blast)+
  done

lift_definition val_\<alpha> :: "val \<Rightarrow> va_sep" is val_\<alpha>_aux using val_\<alpha>_aux_dj by auto
  

  
lemma "val_\<alpha>"



oops
xxx, ctd here: \<alpha> :: val \<Rightarrow> va_sep
  which laws are required?



thm is_VSTRUCT_def
find_theorems  lower_lens
  

find_theorems "(\<bowtie>)" "(\<bullet>\<^sub>L)"




oops
xxx, ctd here: Separation algebra on abstraction of values!

  Attempt 1:
    abstract to function from addresses to primitive values
    requires separation algebra on addr = block_addr \<times> vaddr
    
      \<rightarrow> block_addr: Simple \<noteq> algebra
      \<rightarrow> vaddr: Do disjoint-predicate: Disjoint if no addr is prefix of other addr
        \<longrightarrow> Should map to lens independence

    functors to describe content of arrays and structures (relate them to val), with split rules.
        



\<rightarrow> Generalization to memory is straightforward (block_allocator!)

definition 






(* TODO: Move *)
lemma mwp_mono[mono]:
  assumes "N\<longrightarrow>N'" "\<And>e. F e \<longrightarrow> F' e" "\<And>e s. E e s \<longrightarrow> E' e s" "\<And>r s. S r s \<longrightarrow> S' r s"
  shows "mwp m N F E S \<le> mwp m N' F' E' S'"
  using assms
  by (auto simp: mwp_def split: mres.split) 


(* TODO: Move *)
lemma mwp_combine: 
  assumes "mwp c N F E S"
  assumes "mwp c N' F' E' S'"
  shows "mwp c (N\<and>N') (\<lambda>msg. F msg \<and> F' msg) (\<lambda>e s. E e s \<and> E' e s) (\<lambda>r s. S r s \<and> S' r s)"
  using assms
  by (auto simp: mwp_def split: mres.split)
  
  
inductive eventually for P E where
  evtl_reached: "\<lbrakk>P \<sigma> = Some \<Phi>; \<Phi> s\<rbrakk> \<Longrightarrow> eventually P E f \<sigma> s"
| evtl_step: "\<lbrakk>P \<sigma> = None; mwp (run (c \<sigma>) s) top bot E (eventually P E c)\<rbrakk> \<Longrightarrow> eventually P E c \<sigma> s"  


definition "exec_block_loop_body epn block_map label \<equiv> doM {
    \<comment> \<open>Lookup label\<close>
    block \<leftarrow> lookup (STATIC_ERROR ''undef label'') block_map label;
    exec_block_reset epn block
  }"

definition "exec_block_loop epn block_map label \<equiv>         
  mwhile (\<lambda>_. return True) (exec_block_loop_body epn block_map) label"


lemma floyd_partial_main_lemma:
  assumes "eventually P E (exec_block_loop_body epn block_map) label\<^sub>0 s\<^sub>0"
  assumes "\<And>label \<Phi> s. \<lbrakk>P label = Some \<Phi>; \<Phi> s\<rbrakk> 
    \<Longrightarrow> mwp (run (exec_block_loop_body epn block_map label) s) top err.is_static E (eventually P E (exec_block_loop_body epn block_map))"
  shows "mwp (run (exec_block_loop epn block_map label\<^sub>0) s\<^sub>0) top err.is_static E bot"
proof -
  show "mwp (run (exec_block_loop epn block_map label\<^sub>0) s\<^sub>0) top err.is_static E bot"  
    unfolding exec_block_loop_def
    apply (rule mwhile_invar_rule[OF refl, where I="eventually P E (exec_block_loop_body epn block_map)"])
    apply simp
    apply (fact)
    apply (auto simp: run_simps cong del: mwp_cong)
    apply (erule eventually.cases; clarsimp)
    subgoal
      apply (rule mwp_cons[OF assms(2)])
      apply (assumption|simp)+
      done
    subgoal
      by (erule mwp_cons) auto 
    done

qed



definition "init_proc_state params args \<equiv> mfold' (uncurry define_lvar) (zip (map snd params) args)"

definition "proc_epilogue r \<equiv> doM {
  lbs \<leftarrow> use (exec_state.local_blocks\<^sub>L)\<^sub>S;
  mfold' (\<lambda>x. zoom (exec_state.memory\<^sub>L)\<^sub>S (block_free block_type.ON_STACK x)) lbs;
  return r
}"

lemma init_proc_state_eapprox:
  "mwp (run (init_proc_state params args) s) bot err.is_static bot top"  
proof -

  have R1: "mwp (run (define_lvar n v) s) bot err.is_static bot top" for n v s
    unfolding define_lvar_def
    by (auto simp: run_simps split: option.split)
    
  thm R1[THEN mwp_cons]  

  have "mwp (run (mfold' (uncurry define_lvar) pas) s) bot err.is_static bot top" for pas s
    apply (induction pas arbitrary: s)
    apply (auto simp: run_simps intro!: R1[THEN mwp_cons])
    done

  then show ?thesis  
    by (auto simp: init_proc_state_def)
  
qed    

lemma proc_epilogue_eapprox: "mwp (run (proc_epilogue r) s) bot ((=) MEM_ERROR) bot top"
proof -
  have R1: "mwp (run (mfold' (\<lambda>x. zoom (exec_state.memory\<^sub>L)\<^sub>S (block_free block_type.ON_STACK x)) lbs) s) bot ((=) MEM_ERROR) bot top"
    for lbs
    apply (induction lbs arbitrary: s)
    apply (auto simp: run_simps block_free_def split: option.split)
    done

  show ?thesis
    unfolding proc_epilogue_def
    by (auto simp: run_simps split: option.split intro!: R1[THEN mwp_cons])
    
qed    

lemma
  assumes "mwp (run (exec_proc epn p args) \<mu>) top no_static_err (top::'e \<Rightarrow> _) top"
  assumes "P args \<mu>"
  assumes PL: "mwp (run (init_proc_state (procedure.params p) args) (mk_fresh_exec_state \<mu>)) top top (top::'e \<Rightarrow> _) P\<^sub>l"
  assumes PROL: "\<And>s. P\<^sub>l () s \<Longrightarrow> mwp (run (exec_block epn (procedure.prologue p)) s) top err.is_static QQQ XXX"
  assumes EPIL: "\<And>r s. QQQ r s 
       \<Longrightarrow> mwp (run (proc_epilogue r) s) top err.is_static (top::'e \<Rightarrow> _)
            (\<lambda>r s. Q r (get' exec_state.memory\<^sub>L s))"
            
  assumes IV_INIT: "\<And>label s. XXX label s \<Longrightarrow> eventually INVARS QQQ (exec_block_loop_body epn (map_of (procedure.blocks p))) label s"            
  assumes IV_STEP: "\<And>label s \<Phi>. \<lbrakk> INVARS label = Some \<Phi>; \<Phi> s \<rbrakk> \<Longrightarrow>
    mwp (run (exec_block_loop_body epn (map_of (procedure.blocks p)) label) s) top err.is_static QQQ
            (eventually INVARS QQQ (exec_block_loop_body epn (map_of (procedure.blocks p))))"
              
  shows "mwp (run (exec_proc epn p args) \<mu>) top bot (top::'e \<Rightarrow> _) Q"
proof -
  obtain params prologue blocks rtype where [simp]: "p=PROC params prologue blocks rtype"
    by (cases p)


  have "mwp (run (exec_proc epn p args) \<mu>) top err.is_static (bot::'e \<Rightarrow> _) Q" 
    unfolding exec_proc_def
    apply (subst exec_block_loop_body_def[symmetric])
    apply (subst exec_block_loop_def[symmetric])
    apply (subst init_proc_state_def[symmetric])
    apply (subst proc_epilogue_def[symmetric])
    apply (auto simp: run_simps cong del: mwp_cong split: option.split)
    apply (rule mwp_cons)
    apply (rule mwp_combine[OF init_proc_state_eapprox])
    apply (rule PL[simplified])
    apply simp
    apply simp
    apply simp
    apply simp
    apply (rule mwp_cons)
    apply (rule PROL[simplified])
    apply simp
    apply simp
    apply simp
    apply (rule mwp_cons)
    apply (rule mwp_combine[OF proc_epilogue_eapprox])
    apply (rule EPIL)
    apply simp
    apply simp
    apply clarsimp
    apply simp
    apply simp
    apply (rule mwp_cons)
    apply (rule floyd_partial_main_lemma[where P=INVARS and E=QQQ])
    apply simp_all
    thm IV_INIT[simplified]
    apply (rule IV_INIT[simplified]; simp)
    subgoal
      apply (rule mwp_cons)
      thm IV_STEP[simplified]
      apply (rule IV_STEP[simplified])
      apply simp+
      done
    subgoal  
      apply (rule mwp_cons)
      apply (rule mwp_combine[OF proc_epilogue_eapprox])
      apply (rule EPIL)
      by auto
    done
    
  from mwp_combine[OF this assms(1)] show ?thesis
    by (rule mwp_cons) auto
  
qed
  
xxx, ctd here: What is QQQ and XXX in context of procedures + sep-logic assertions?





























definition "whilek (k::nat) b c s \<equiv> doM {
  (s,_) \<leftarrow> mwhile 
    (\<lambda>(s,k). doM { return (b s \<and> k>0)}) 
    (\<lambda>(s,k). doM { s \<leftarrow> c s; return (s, k - 1) })
    (s,k); 
  return s
  }"

lemma whilek_unfold: "whilek k b c s 
  = (if b s \<and> k>0 then doM { s \<leftarrow> c s; whilek (k - 1) b c s   } else return s)"
  unfolding whilek_def
  apply (subst mwhile_unfold)
  apply (rule M_eqI)
  apply (auto simp: run_simps)
  done

lemma whilek0[simp]: "whilek 0 b c \<sigma> = return \<sigma>"
  apply (subst whilek_unfold) by simp


definition "fin_Qk k b c Q \<sigma> s \<equiv> 
  mwp (run (whilek k b c \<sigma>) s) (True) top top (\<lambda>\<sigma> s. \<not>b \<sigma> \<and> Q \<sigma> s)"

lemma "fin_Qk 0 b c Q \<sigma> s \<longleftrightarrow> \<not>b \<sigma> \<and> Q \<sigma> s"
  unfolding fin_Qk_def by (simp add: run_simps)



lemma fin_Qk_unfold: "fin_Qk 0 b c Q \<sigma> s = (
    if b \<sigma> \<and> (0::nat)>0 then
      mwp (run (c \<sigma>) s) top top top (fin_Qk (k-1) b c Q)
    else
      \<not>b \<sigma> \<and> Q \<sigma> s
  )"
  unfolding fin_Qk_def
  apply (subst whilek_unfold)
  apply (auto simp: run_simps)
  done

lemma 
  shows "mwp (run (mwhile (\<lambda>_. return True) step l) s) bot bot Q bot"
  apply (rule mwhile_invar_rule[OF refl])




lemma "mwp (run (whilek ))"  


  oops
   xxx: Iterate execution at most k times ... 
    show relation with while-loop









end
