theory IICF_Shared_Lists
imports "Isabelle_LLVM.IICF"
begin

section \<open>Lists with Element-wise Ownership\<close>


(* TODO: Move *)  
lemma list_all2_append2: "length xs' = length ys' \<Longrightarrow> list_all2 P (xs@xs') (ys@ys') \<longleftrightarrow> list_all2 P xs ys \<and> list_all2 P xs' ys'"  
  by (auto simp: list_all2_append list_all2_iff)

(* TODO: Move *)  
lemma rev_induct2 [consumes 1, case_names Nil snoc]:
  "length xs = length ys \<Longrightarrow> P [] [] \<Longrightarrow>
   (\<And>x xs y ys. length xs = length ys \<Longrightarrow> P xs ys \<Longrightarrow> P (xs@[x]) (ys@[y]))
   \<Longrightarrow> P xs ys"
proof (induct xs arbitrary: ys rule: rev_induct)
  case (snoc x xs ys) then show ?case by (cases ys rule: rev_cases) simp_all
qed simp

lemma map_by_map_idx: "map f xs = map (f o nth xs) [0..<length xs]"  
  apply (induction xs rule: rev_induct)
  by auto
  
lemma map2_map_conv: "map2 f (map g xs) (map h ys) = map2 (\<lambda>x y. f (g x) (h y)) xs ys"
  apply(induction xs ys rule: list_induct2')
  by auto
  
lemma map2_same[simp]: "map2 f xs xs = map (\<lambda>x. f x x) xs"
  apply (induction xs) by auto
  
  
thm list.rel_map
lemma list_all2_map_map_conv: "list_all2 P (map f xs) (map g ys) = list_all2 (\<lambda>x y. P (f x) (g y)) xs ys"
  by (auto simp: list.rel_map)
  
  

(* Split *)
definition "sl_split s xs = map (\<lambda>i. if i\<in>s \<and> i<length xs then xs!i else None) [0..<length xs]"

(* Join *)
fun join_option where
  "join_option None y = y"
| "join_option x None = x"  
| "join_option _ _ = None"  (* Corner case mapped symmetrically to None *)

lemma join_option_add_simp[simp]: "join_option x None = x" by (cases x) auto

definition "sl_join = map2 join_option"

(* Conversion from/to plain list *)
definition "sl_of_list = map Some"
definition "list_of_sl = map the"

(* Structure *)
definition "sl_struct xs = map ((=)None) xs"
definition "sl_compat s\<^sub>1 s\<^sub>2 = list_all2 (\<or>) s\<^sub>1 s\<^sub>2"
definition "sl_complete s \<longleftrightarrow> set s \<subseteq> {False}"
definition "sl_indexes s = {i . i<length s \<and> \<not>s!i}"

abbreviation "sl_indexes' xs \<equiv> sl_indexes (sl_struct xs)"

definition "sl_struct_join s\<^sub>1 s\<^sub>2 = map2 (=) s\<^sub>1 s\<^sub>2"
definition "sl_struct_split I s = map (\<lambda>i. if i\<in>I then s!i else True) [0..<length s]"

(* Operations *)
definition "sl_get xs i = (if i<length xs then the (xs!i) else undefined (i-length xs))"
definition "sl_put xs i x = xs[i:=Some x]"


lemma sl_indexes_alt: "sl_indexes' xs = {i . i<length xs \<and> xs!i \<noteq> None}"
  unfolding sl_indexes_def sl_struct_def
  by auto


lemma sl_indexes_of_list[simp]: "sl_indexes' (sl_of_list xs) = {0..<length xs}"
  unfolding sl_indexes_def sl_struct_def sl_of_list_def by auto

lemma sl_struct_put[simp]: "i\<in>sl_indexes' xs \<Longrightarrow> sl_struct (sl_put xs i x) = sl_struct xs"
  unfolding sl_indexes_def sl_struct_def sl_put_def 
  by (auto simp: map_update list_update_same_conv)

lemma sl_get_of_list[simp]: "i<length xs \<Longrightarrow> sl_get (sl_of_list xs) i = xs!i"  
  unfolding sl_get_def sl_of_list_def by simp
  
lemma sl_put_of_list[simp]: "sl_put (sl_of_list xs) i x = sl_of_list (xs[i:=x])"
  unfolding sl_put_def sl_of_list_def 
  by (simp add: map_update)
  
lemma sl_list_of_list[simp]: "list_of_sl (sl_of_list xs) = xs"
  unfolding list_of_sl_def sl_of_list_def by auto

lemma sl_of_list_length[simp]: "length (sl_of_list xs) = length xs"  
  unfolding sl_of_list_def by auto
    
lemma sl_split_length[simp]: "length (sl_split s xs) = length xs"    
  unfolding sl_split_def by auto

lemma sl_struct_length[simp]: "length (sl_struct xs) = length xs"  
  unfolding sl_struct_def by auto
  
lemma sl_join_length_nopre: "length (sl_join xs ys) = min (length xs) (length ys)"  
  unfolding sl_join_def by simp

lemma sl_struct_join_length_nopre: "length (sl_struct_join s\<^sub>1 s\<^sub>2) = min (length s\<^sub>1) (length s\<^sub>2)"  
  unfolding sl_struct_join_def by auto

lemma sl_compat_lengthD: "sl_compat s\<^sub>1 s\<^sub>2 \<Longrightarrow> length s\<^sub>1 = length s\<^sub>2"  
  unfolding sl_compat_def by (auto simp: list_all2_lengthD)
  
lemma sl_join_struct_length[simp]: "sl_compat s\<^sub>1 s\<^sub>2 \<Longrightarrow> length (sl_struct_join s\<^sub>1 s\<^sub>2) = length s\<^sub>2"  
  by (auto dest: sl_compat_lengthD simp: sl_struct_join_length_nopre)
  
lemma sl_join_length[simp]: "sl_compat (sl_struct xs) (sl_struct ys) \<Longrightarrow> length (sl_join xs ys) = length ys"  
  by (auto dest: sl_compat_lengthD simp: sl_join_length_nopre)
  
lemma sl_struct_join[simp]: "sl_struct (sl_join xs ys) = sl_struct_join (sl_struct xs) (sl_struct ys)"
  unfolding sl_compat_def sl_join_def sl_struct_join_def sl_struct_def
  by (auto simp add: map2_map_conv)
  
lemma sl_join_indexes_nopre: "sl_indexes (sl_struct_join s\<^sub>1 s\<^sub>2) = ((sl_indexes s\<^sub>1 \<union> sl_indexes s\<^sub>2) - (sl_indexes s\<^sub>1 \<inter> sl_indexes s\<^sub>2)) \<inter> ({0..<min (length s\<^sub>1) (length s\<^sub>2)})"  
  unfolding sl_indexes_def
  apply (simp add: sl_struct_join_def)
  by auto
  
lemma sl_compat_idx_djD: "sl_compat s\<^sub>1 s\<^sub>2 \<Longrightarrow> sl_indexes s\<^sub>1 \<inter> sl_indexes s\<^sub>2 = {}"  
  unfolding sl_compat_def sl_indexes_def
  by (auto simp: sl_struct_def dest: list_all2_nthD) 
  
lemma sl_indexes_lengthD: "i\<in>sl_indexes s \<Longrightarrow> i<length s"  
  unfolding sl_indexes_def by auto
  
lemma sl_join_indexes[simp]: "sl_compat s\<^sub>1 s\<^sub>2 \<Longrightarrow> sl_indexes (sl_struct_join s\<^sub>1 s\<^sub>2) = sl_indexes s\<^sub>1 \<union> sl_indexes s\<^sub>2"  
  by (auto 0 3 simp: sl_join_indexes_nopre dest: sl_compat_idx_djD sl_compat_lengthD sl_indexes_lengthD)


lemma sl_get_split: "i\<in>s \<Longrightarrow> sl_get (sl_split s xs) i = sl_get xs i"
  unfolding sl_get_def sl_split_def 
  apply (cases "i<length xs")
  by (auto simp: nth_undefined)
  
lemma sl_put_split: "i\<in>s \<Longrightarrow> sl_put (sl_split s xs) i x = sl_split s (sl_put xs i x)"  
  unfolding sl_put_def sl_split_def 
  apply (cases "i<length xs")
  by (auto simp: nth_list_update intro: nth_equalityI)
  

lemma nth_map2: "\<lbrakk> i<length xs; i<length ys \<rbrakk> \<Longrightarrow> map2 f xs ys ! i = f (xs!i) (ys!i)" by simp

lemma map2_update1: "map2 f (xs[i:=x]) ys = (map2 f xs ys)[i := f x (ys!i)]"
  by (metis list_update_id map_update old.prod.case zip_update)

lemma map2_update2: "map2 f xs (ys[i:=y]) = (map2 f xs ys)[i := f (xs!i) y]"
  by (metis list_update_id map_update old.prod.case zip_update)
    
  
lemma sl_get_join: "sl_compat (sl_struct xs) (sl_struct ys) \<Longrightarrow> i<length ys \<Longrightarrow> sl_get (sl_join xs ys) i = (if i\<in>sl_indexes' xs then sl_get xs i else sl_get ys i)"
  unfolding sl_indexes_def sl_compat_def sl_get_def sl_join_def sl_struct_def
  by (auto simp add: list.rel_map nth_map2 list_all2_lengthD dest: list_all2_nthD2)

lemma sl_get_join1: "sl_compat (sl_struct xs) (sl_struct ys) \<Longrightarrow> i\<in>sl_indexes' xs \<Longrightarrow> sl_get (sl_join xs ys) i = sl_get xs i"
  apply (subst sl_get_join)
  by (auto 0 3 simp: sl_get_join dest: sl_indexes_lengthD sl_compat_lengthD)
            
lemma sl_get_join2: "sl_compat (sl_struct xs) (sl_struct ys) \<Longrightarrow> i\<in>sl_indexes' ys \<Longrightarrow> sl_get (sl_join xs ys) i = sl_get ys i"
  apply (subst sl_get_join)
  by (auto 0 3 simp: sl_get_join dest: sl_indexes_lengthD sl_compat_lengthD sl_compat_idx_djD)

lemma sl_put_join1: "sl_compat (sl_struct xs) (sl_struct ys) \<Longrightarrow> i\<in>sl_indexes' xs \<Longrightarrow> sl_put (sl_join xs ys) i x = sl_join (sl_put xs i x) ys"
  unfolding sl_indexes_def sl_compat_def sl_put_def sl_join_def sl_struct_def
  by (auto 0 3 simp add: list.rel_map nth_map2 list_all2_lengthD map2_update1 dest: list_all2_nthD2)
  
lemma sl_put_join2: "sl_compat (sl_struct xs) (sl_struct ys) \<Longrightarrow> i\<in>sl_indexes' ys \<Longrightarrow> sl_put (sl_join xs ys) i x = sl_join xs (sl_put ys i x)"
  unfolding sl_indexes_def sl_compat_def sl_put_def sl_join_def sl_struct_def
  by (auto 0 3 simp add: list.rel_map nth_map2 list_all2_lengthD map2_update2 dest: list_all2_nthD2)

lemma sl_struct_split[simp]: "sl_struct (sl_split s xs) = sl_struct_split s (sl_struct xs)"
  unfolding sl_struct_def sl_split_def sl_struct_split_def
  by auto
  
lemma sl_compat_splitI: "s\<inter>s'={} \<Longrightarrow> sl_compat (sl_struct_split s (sl_struct xs)) (sl_struct_split s' (sl_struct xs))"
  by (auto simp: sl_compat_def sl_struct_split_def list.rel_map intro!: list.rel_refl)
  
  
lemma sl_indexes_split: "sl_indexes (sl_struct_split I s) = I \<inter> sl_indexes s"
  unfolding sl_indexes_def sl_struct_split_def
  by auto
  
  
lemma sl_of_list_complete[simp]: "sl_complete (sl_struct (sl_of_list xs))"  
  unfolding sl_complete_def sl_struct_def sl_of_list_def by auto
  
lemma sl_get_complete[simp]: "sl_complete (sl_struct xs) \<Longrightarrow> sl_get xs i = list_of_sl xs!i"  
  unfolding sl_complete_def sl_struct_def sl_of_list_def sl_get_def list_of_sl_def
  apply (cases "i<length xs")  
  by (simp_all add: nth_undefined)
  
  
lemma slcompat_None_lower_bound:
  assumes "sl_compat (sl_struct xs\<^sub>1) (sl_struct xs\<^sub>2)"  
  shows "replicate_mset (length xs\<^sub>1) None \<subseteq># mset xs\<^sub>1 + mset xs\<^sub>2"  
proof -
  from assms show ?thesis
    unfolding sl_compat_def sl_struct_def
    apply (simp add: list.rel_map)
    apply (induction xs\<^sub>1 xs\<^sub>2 rule: list_all2_induct)
    apply (auto)
    subgoal by (metis add_mset_add_single mset_le_incr_right1)
    subgoal by (meson mset_le_add_mset_decr_left1 subset_mset.dual_order.refl subset_mset.dual_order.trans)
    done
    
qed      
  

lemma mset_join_idxs_eq:
  assumes "sl_compat (sl_struct xs\<^sub>1) (sl_struct xs\<^sub>2)"  
  shows "mset (sl_join xs\<^sub>1 xs\<^sub>2) = mset xs\<^sub>1 + mset xs\<^sub>2 - replicate_mset (length xs\<^sub>1) None"
  using sl_compat_lengthD[OF assms] assms
  apply simp
  apply (induction xs\<^sub>1 xs\<^sub>2 rule: list_induct2)
  subgoal by (auto simp: sl_join_def)
  subgoal for x xs y ys
    using slcompat_None_lower_bound[of xs ys]
    unfolding sl_compat_def sl_struct_def
    apply (auto simp: sl_join_def)
    subgoal by (metis add_mset_add_single subset_mset.add_diff_assoc2)
    subgoal by (metis add_mset_add_single subset_mset.add_diff_assoc2)
    done
  done
  
  
definition "WITH_IDXS ls xs m \<equiv> do {
  ASSERT (ls\<subseteq>sl_indexes' xs);

  let xs\<^sub>1 = sl_split ls xs;
  let xs\<^sub>2 = sl_split (-ls) xs;
  
  (r,xs\<^sub>1',xs\<^sub>2') \<leftarrow> m xs\<^sub>1 xs\<^sub>2;
  
  ASSERT (sl_struct xs\<^sub>1' = sl_struct xs\<^sub>1);
  ASSERT (sl_struct xs\<^sub>2' = sl_struct xs\<^sub>2);

  RETURN (r,sl_join xs\<^sub>1' xs\<^sub>2')
}"

lemma WITH_IDXS_rule[refine_vcg]:
  assumes "ls \<subseteq> sl_indexes' xs"
  assumes "\<And>xs\<^sub>1 xs\<^sub>2. \<lbrakk> 
    xs\<^sub>1 = sl_split ls xs; 
    xs\<^sub>2 = sl_split (-ls) xs;
    sl_compat (sl_struct xs\<^sub>1) (sl_struct xs\<^sub>2)
  \<rbrakk> \<Longrightarrow> m xs\<^sub>1 xs\<^sub>2 \<le> SPEC (\<lambda>(r,xs\<^sub>1',xs\<^sub>2'). 
            sl_struct xs\<^sub>1' = sl_struct xs\<^sub>1 
          \<and> sl_struct xs\<^sub>2' = sl_struct xs\<^sub>2   
          \<and> P (r, sl_join xs\<^sub>1' xs\<^sub>2')
        )
        "
  shows "WITH_IDXS ls xs m \<le> SPEC P"
  unfolding WITH_IDXS_def
  apply refine_vcg
  apply fact
  apply (refine_vcg assms(2))
  apply (auto simp: sl_compat_splitI)
  done

  
lemma WITH_IDXS_mono[refine_mono]: 
  "\<lbrakk>\<And>a b. f a b \<le> f' a b\<rbrakk> \<Longrightarrow> WITH_IDXS ls xs f \<le> WITH_IDXS ls xs f'"
  unfolding WITH_IDXS_def
  by refine_mono

lemma WITH_IDXS_mono_flat[refine_mono]: 
  "\<lbrakk>\<And>a b. flat_ge (f a b) (f' a b)\<rbrakk> \<Longrightarrow> flat_ge (WITH_IDXS ls xs f) (WITH_IDXS ls xs f')"
  unfolding WITH_IDXS_def
  by refine_mono
  
  
find_in_thms WHILEIT in sepref_monadify_arity sepref_monadify_comb 

find_theorems WHILEIT PR_CONST

  
(* Monadifier setup *)

lemma WITH_IDXS_pat[def_pat_rules]:
  "WITH_IDXS$ls \<equiv> UNPROTECT (WITH_IDXS ls)"
  by (simp)

term WITH_IDXS  
  
lemma id_WITH_IDXS[id_rules]: 
  "PR_CONST (WITH_IDXS ls) ::\<^sub>i TYPE('a option list \<Rightarrow> ('a option list \<Rightarrow> 'a option list \<Rightarrow> ('b \<times> 'c option list \<times> 'c option list) nres) \<Rightarrow> ('b \<times> 'c option list) nres)"
  by simp

lemma WITH_IDXS_arity[sepref_monadify_arity]: "PR_CONST (WITH_IDXS ls) \<equiv> \<lambda>\<^sub>2xs f. SP (PR_CONST (WITH_IDXS ls))$xs$(\<lambda>\<^sub>2a b. f$a$b)"
  by simp

lemma WITH_IDXS_comb[sepref_monadify_comb]:  
  "PR_CONST (WITH_IDXS ls)$xs$f = Refine_Basic.bind$(EVAL$xs)$(\<lambda>\<^sub>2xs. SP (PR_CONST (WITH_IDXS ls))$xs$f)"
  by simp

  
(* TODO: Move *)
lemma fold_is_None': "(=)None = is_None" by auto

lemma sl_struct_param[param]: "(sl_struct,sl_struct) \<in> \<langle>\<langle>A\<rangle>option_rel\<rangle>list_rel \<rightarrow> \<langle>bool_rel\<rangle>list_rel"  
  unfolding sl_struct_def fold_is_None'
  by parametricity
  
term sl_indexes  

lemma sl_indexes_param[param]: "(sl_indexes, sl_indexes) \<in> \<langle>bool_rel\<rangle>list_rel \<rightarrow> \<langle>nat_rel\<rangle>set_rel" by simp

term sl_split

lemma sl_split_param[param]: "(sl_split,sl_split) \<in> \<langle>nat_rel\<rangle>set_rel \<rightarrow> \<langle>\<langle>A\<rangle>option_rel\<rangle>list_rel \<rightarrow> \<langle>\<langle>A\<rangle>option_rel\<rangle>list_rel"
  unfolding sl_split_def
  apply parametricity
  by auto

term sl_join

lemma join_option_param[param]: "(join_option, join_option) \<in> \<langle>A\<rangle>option_rel \<rightarrow> \<langle>A\<rangle>option_rel \<rightarrow> \<langle>A\<rangle>option_rel"
  by (auto simp: option_rel_def)

lemma sl_join_param[param]: "(sl_join, sl_join) \<in> \<langle>\<langle>A\<rangle>option_rel\<rangle>list_rel \<rightarrow> \<langle>\<langle>A\<rangle>option_rel\<rangle>list_rel \<rightarrow> \<langle>\<langle>A\<rangle>option_rel\<rangle>list_rel"  
  unfolding sl_join_def
  by parametricity
  
  
  
lemma WITH_IDXS_refine[refine]:
  assumes "(ls',ls)\<in>Id"
  assumes "(xs',xs) \<in> \<langle>\<langle>A\<rangle>option_rel\<rangle>list_rel"
  assumes [refine]: "\<lbrakk>ls \<subseteq> sl_indexes' xs; ls' \<subseteq> sl_indexes' xs'\<rbrakk> 
    \<Longrightarrow> m' (sl_split ls' xs') (sl_split (-ls') xs') \<le> \<Down>(R\<times>\<^sub>r\<langle>\<langle>A\<rangle>option_rel\<rangle>list_rel\<times>\<^sub>r\<langle>\<langle>A\<rangle>option_rel\<rangle>list_rel) (m (sl_split ls xs) (sl_split (-ls) xs))"
  shows "WITH_IDXS ls' xs' m' \<le>\<Down>(R \<times>\<^sub>r \<langle>\<langle>A\<rangle>option_rel\<rangle>list_rel) (WITH_IDXS ls xs m)"
  unfolding WITH_IDXS_def
  apply (rule nres_relD)
  using assms(1,2)
  apply refine_rcg
  subgoal
    apply (subgoal_tac "(sl_indexes' xs', sl_indexes' xs)\<in>\<langle>nat_rel\<rangle>set_rel")
    apply simp
    by parametricity
  apply clarsimp  
  subgoal for _ xx1s xx2s _ xx1s' xx2s'
    apply (subgoal_tac "(sl_struct xx1s',sl_struct xx1s) \<in> \<langle>bool_rel\<rangle>list_rel")
    apply (subgoal_tac "(sl_struct xs',sl_struct xs) \<in> \<langle>bool_rel\<rangle>list_rel")
    apply auto []
    apply parametricity
    apply parametricity
    done
  apply clarsimp  
  subgoal for _ xx1s xx2s _ xx1s' xx2s'
    apply (subgoal_tac "(sl_struct xx2s',sl_struct xx2s) \<in> \<langle>bool_rel\<rangle>list_rel")
    apply (subgoal_tac "(sl_struct xs',sl_struct xs) \<in> \<langle>bool_rel\<rangle>list_rel")
    apply auto []
    apply parametricity
    apply parametricity
    done
  subgoal  
    apply parametricity
    by simp_all  
  done  
  
    
(*  
lemma join_option_eq_Some_iff[simp]: 
  "join_option (Some xv) y = Some xv' \<longleftrightarrow> xv'=xv \<and> y=None"
  "join_option x (Some yv) = Some yv' \<longleftrightarrow> yv'=yv \<and> x=None"
  "join_option None y = Some yv' \<longleftrightarrow> y=Some yv'"
  "join_option x None = Some xv' \<longleftrightarrow> x=Some xv'"
  apply (cases y; auto)
  apply (cases x; auto)
  apply (cases y; auto)
  apply (cases x; auto)
  done


lemma param_join_option[param]: "(join_option,join_option) \<in> \<langle>A\<rangle>option_rel \<rightarrow> \<langle>A\<rangle>option_rel \<rightarrow> \<langle>A\<rangle>option_rel"
  by (auto simp: option_rel_def)


lemma join_idxs_param[param]: "(join_idxs,join_idxs) \<in> \<langle>\<langle>A\<rangle>option_rel\<rangle>list_rel \<rightarrow> \<langle>\<langle>A\<rangle>option_rel\<rangle>list_rel \<rightarrow> \<langle>\<langle>A\<rangle>option_rel\<rangle>list_rel"
  unfolding join_idxs_def
  by parametricity

(*
definition "join_idxs xs\<^sub>1 xs\<^sub>2 = map (\<lambda>i. if i<length xs\<^sub>1 \<and> i<length xs\<^sub>2 then (if xs\<^sub>1!i=None then xs\<^sub>2!i else xs\<^sub>1!i) else None) [0..<length xs\<^sub>1]"
*)

lemma map_compat_split_aux: "map ((=) None \<circ> (\<lambda>i. P i ((xs @ [x]) ! i))) [0..<length xs] = map ((=) None \<circ> (\<lambda>i. P i (xs ! i))) [0..<length xs]" by simp

lemma map_compat_split_aux1: "
    (map ((=) None \<circ> (\<lambda>i. if i \<in> ls \<and> i < Suc (length xs) then (xs @ [x]) ! i else None)) [0..<length xs]) 
  = (map ((=) None \<circ> (\<lambda>i. if i \<in> ls \<and> i < length xs then xs ! i else None)) [0..<length xs])"
  by simp

lemma map_compat_split_aux2: "
    (map ((=) None \<circ> (\<lambda>i. if i \<in> ls \<or> Suc (length xs) \<le> i then None else (xs @ [x]) ! i)) [0..<length xs])
  = (map ((=) None \<circ> (\<lambda>i. if i \<in> ls \<or> length xs \<le> i then None else xs ! i)) [0..<length xs])"  
  by simp

lemma slcompat_struct_split[simp]: "slcompat (slstruct (split_idxs_left ls xs)) (slstruct (split_idxs_right ls xs))"
  unfolding slcompat_def slstruct_def split_idxs_left_def split_idxs_right_def
  apply (induction xs rule: rev_induct)
  apply simp
  by (clarsimp simp: list_all2_append map_compat_split_aux1 map_compat_split_aux2)

lemma "i\<in>ls \<Longrightarrow> split_idxs_left ls xs ! i = xs ! i"
  unfolding split_idxs_left_def
  apply (cases "i<length xs")
  by (auto simp: nth_undefined)
  
lemma "i\<notin>ls \<Longrightarrow> split_idxs_right ls xs ! i = xs ! i"
  unfolding split_idxs_right_def
  apply (cases "i<length xs")
  by (auto simp: nth_undefined)

lemma opt_list_rel_imp_same_sl_struct: "(xs', xs) \<in> \<langle>\<langle>A\<rangle>option_rel\<rangle>list_rel \<Longrightarrow> slstruct xs' = slstruct xs"  
  unfolding slstruct_def
  apply (rule IdD)
  apply (subst list_rel_id_simp[symmetric])
  apply parametricity
  by auto


lemma opt_list_rel_imp_same_sl_indexes: "(xs', xs) \<in> \<langle>\<langle>A\<rangle>option_rel\<rangle>list_rel \<Longrightarrow> sl_indexes xs' = sl_indexes xs"  
  unfolding sl_indexes_def
  apply (auto simp: list_rel_imp_same_length)
  apply (metis not_None_eq option_rel_simp(2) pair_in_Id_conv param_nth)
  apply (metis not_None_eq option_rel_simp(1) pair_in_Id_conv param_nth)
  done
  
  
lemma slstruct_eq_imps: "slstruct a = slstruct b \<Longrightarrow> length a = length b \<and> sl_indexes a = sl_indexes b"  
  unfolding slstruct_def sl_indexes_def
  apply (auto dest: map_eq_imp_length_eq)
  apply (metis (full_types) length_map not_Some_eq nth_map)
  apply (metis (full_types) length_map not_Some_eq nth_map)
  done
  
term split_idxs_left  
lemma split_idxs_left_param[param]: "(split_idxs_left,split_idxs_left) \<in> \<langle>Id\<rangle>set_rel \<rightarrow> \<langle>\<langle>A\<rangle>option_rel\<rangle>list_rel \<rightarrow> \<langle>\<langle>A\<rangle>option_rel\<rangle>list_rel"
  unfolding split_idxs_left_def
  apply parametricity
  by auto
  
lemma split_idxs_right_param[param]: "(split_idxs_right,split_idxs_right) \<in> \<langle>Id\<rangle>set_rel \<rightarrow> \<langle>\<langle>A\<rangle>option_rel\<rangle>list_rel \<rightarrow> \<langle>\<langle>A\<rangle>option_rel\<rangle>list_rel"
  unfolding split_idxs_right_def
  apply parametricity
  by auto
  
term join_idxs

lemma sl_indexes_alt: "sl_indexes xs = {i . i<length (slstruct xs) \<and> \<not>(slstruct xs)!i}"
  unfolding sl_indexes_def slstruct_def
  by auto
  
lemma length_slstruct[simp]: "length (slstruct xs) = length xs" unfolding slstruct_def by auto
  
lemma length_join_idxs[simp]: "length (join_idxs xs\<^sub>1 xs\<^sub>2) = min (length xs\<^sub>1) (length xs\<^sub>2)"  
  unfolding join_idxs_def by auto

lemma sl_indexes_in_range: "sl_indexes xs \<subseteq> {0..<length xs}"  
  unfolding sl_indexes_def by auto
  

  
lemma slcompat_alt: "slcompat (slstruct xs\<^sub>1) (slstruct xs\<^sub>2) \<longleftrightarrow> (length xs\<^sub>1 = length xs\<^sub>2 \<and> sl_indexes xs\<^sub>1 \<inter> sl_indexes xs\<^sub>2 = {})"  
  unfolding sl_indexes_alt slcompat_def
  by (auto 0 2 dest: list_all2_lengthD simp: list_all2_conv_all_nth)
  
lemma in_sl_indexes_iff: "i \<in> sl_indexes xs \<longleftrightarrow> (i<length xs \<and> xs!i\<noteq>None)"  
  unfolding sl_indexes_def by auto
  
lemma join_idxs_nth: "\<lbrakk> i<length xs\<^sub>1; i<length xs\<^sub>2 \<rbrakk> \<Longrightarrow> join_idxs xs\<^sub>1 xs\<^sub>2 ! i = join_option (xs\<^sub>1!i) (xs\<^sub>2!i)"  
  unfolding join_idxs_def
  by (auto simp: )
  
  
lemma slstruct_empty[simp]: "slstruct [] = []" unfolding slstruct_def by auto 
lemma slstruct_Cons[simp]: "slstruct (x#xs) = (x=None)#slstruct xs" unfolding slstruct_def by auto 
lemma slstruct_append[simp]: "slstruct (xs@ys) = slstruct xs @ slstruct ys" unfolding slstruct_def by auto 
  
lemma slcompat_empty[simp]: "slcompat [] []"
  unfolding slcompat_def by auto
  
lemma slcompat_Cons[simp]: "slcompat (x#xs) (y#ys) \<longleftrightarrow> (x\<or>y) \<and> slcompat xs ys"  
  unfolding slcompat_def by auto

    
lemma slcompat_Snoc[simp]: "slcompat (xs@[x]) (ys@[y]) \<longleftrightarrow> slcompat xs ys \<and> (x\<or>y)"  
  unfolding slcompat_def 
  by (auto simp: list_all2_append2)
  
    

lemma join_idxs_empty[simp]: "join_idxs [] [] = []"
  unfolding join_idxs_def by auto

lemma join_idxs_Cons[simp]: "join_idxs (x#xs) (y#ys) = join_option x y # join_idxs xs ys"
  unfolding join_idxs_def
  by auto
  
lemma join_idxs_append[simp]: "length xs = length ys \<Longrightarrow> join_idxs (xs@xs') (ys@ys') = join_idxs xs ys @ join_idxs xs' ys'"
  unfolding join_idxs_def
  by auto


lemma slcompat_None_lower_bound:
  assumes "slcompat (slstruct xs\<^sub>1) (slstruct xs\<^sub>2)"  
  shows "replicate_mset (length xs\<^sub>1) None \<subseteq># mset xs\<^sub>1 + mset xs\<^sub>2"  
proof -
  from assms have "length xs\<^sub>1 = length xs\<^sub>2" by (auto simp: slcompat_alt)
  then show ?thesis using assms
    apply (induction xs\<^sub>1 xs\<^sub>2 rule: list_induct2)
    apply simp
    apply (clarsimp)
    by (meson mset_le_add_mset_decr_left1 mset_subset_eq_add_mset_cancel)
qed      
  
lemma mset_join_idxs_eq:
  assumes "slcompat (slstruct xs\<^sub>1) (slstruct xs\<^sub>2)"  
  shows "mset (join_idxs xs\<^sub>1 xs\<^sub>2) = mset xs\<^sub>1 + mset xs\<^sub>2 - replicate_mset (length xs\<^sub>1) None"
proof -
  from assms have "length xs\<^sub>1 = length xs\<^sub>2" by (auto simp: slcompat_alt)
  then show ?thesis using assms
    apply (induction xs\<^sub>1 xs\<^sub>2 rule: list_induct2)
    apply simp
    apply (clarsimp;safe; clarsimp)
    subgoal
      apply (subst subset_mset.add_diff_assoc[of _ _ "{#_#}", simplified])
      apply (drule slcompat_None_lower_bound)
      by auto
    subgoal
      apply (subst subset_mset.add_diff_assoc[of _ _ "{#_#}", simplified])
      apply (drule slcompat_None_lower_bound)
      by auto
    done  
qed    
    

lemma split_idxs_length[simp]:
  "length (split_idxs_left s xs) = length xs"
  "length (split_idxs_right s xs) = length xs"
  unfolding split_idxs_left_def split_idxs_right_def
  by auto
  
lemma sl_indexes_split_left[simp]: "sl_indexes (split_idxs_left s xs) = s \<inter> sl_indexes xs"
  unfolding sl_indexes_def split_idxs_left_def
  by (auto split: if_splits)
  
lemma sl_indexes_split_right[simp]: "sl_indexes (split_idxs_right s xs) = sl_indexes xs - s"
  unfolding sl_indexes_def split_idxs_right_def
  by (auto split: if_splits)
  

lemma slstruct_join_idxs[simp]:
  shows "slstruct (join_idxs xs ys) = map2 (=) (slstruct xs) (slstruct ys)"
  apply (induction xs arbitrary: ys)
  apply (simp add: join_idxs_def)
  subgoal for a xs ys
    apply (cases ys)
    by (auto simp: join_idxs_def)
  done
  
  
  
lemma slstruct_split_recombine:
  "map2 (=) (slstruct (split_idxs_left s xs)) (slstruct (split_idxs_right s xs)) = slstruct xs"  
  unfolding slstruct_def split_idxs_right_def split_idxs_left_def fun_eq_iff
  apply (simp add: map2_map_conv)
  apply (rewrite in "_ = \<hole>" map_by_map_idx)
  by simp
  

lemma join_split_idxs: "join_idxs (split_idxs_left s xs) (split_idxs_right s xs) = xs"
  unfolding join_idxs_def split_idxs_left_def split_idxs_right_def
  apply (simp add: map2_map_conv)
  apply (rewrite at "_ = \<hole>" list.map_id[symmetric])
  apply (rewrite in "_ = \<hole>" map_by_map_idx)
  by simp
*)  


end
