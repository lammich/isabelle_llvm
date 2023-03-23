theory Sorting_Par_Partition
imports Sorting_Setup Sorting_Guarded_Partition
begin

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
  
  


section \<open>Abstract Algorithm\<close>

subsection \<open>Lists with Element-wise Ownership\<close>

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

(* Monadifier setup *)
lemma WITH_IDXS_arity[sepref_monadify_arity]: "WITH_IDXS \<equiv> \<lambda>\<^sub>2ls xs f. SP WITH_IDXS$ls$xs$(\<lambda>\<^sub>2a b. f$a$b)"
  by simp

lemma WITH_IDXS_comb[sepref_monadify_comb]:  
  "WITH_IDXS$ls$xs$f = Refine_Basic.bind$(EVAL$ls)$(\<lambda>\<^sub>2ls. Refine_Basic.bind$(EVAL$xs)$(\<lambda>\<^sub>2xs. SP WITH_IDXS$ls$xs$f))"
  by simp

lemma WITH_IDXS_mono_flat[refine_mono]: 
  "\<lbrakk>\<And>a b. flat_ge (f a b) (f' a b)\<rbrakk> \<Longrightarrow> flat_ge (WITH_IDXS ls xs f) (WITH_IDXS ls xs f')"
  unfolding WITH_IDXS_def
  by refine_mono
  
  
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
  
  
  
  
  subsection \<open>Step 1: Partition the Array\<close>

  (* TODO: Move near set_drop_conv *)
  lemma set_take_conv_nth: "set (take m xs) = {xs!i| i. i<m \<and> i<length xs}"
    by (auto 0 3 simp: in_set_conv_nth) 

  lemma set_drop_conv_nth: "set (drop m xs) = {xs!i| i. i\<ge>m \<and> i<length xs}" by (rule set_drop_conv)
      
    
text \<open>Partitioning, with potentially overlapping partitioning criteria\<close>
locale partitioning = 
  fixes P\<^sub>1 :: "'a \<Rightarrow> bool"  \<comment> \<open>Element can be in partition 1\<close>
  fixes P\<^sub>2 :: "'a \<Rightarrow> bool"  \<comment> \<open>Element can be in partition 2\<close>
  assumes P_complete: "P\<^sub>1 x \<or> P\<^sub>2 x"
begin  
  definition "partition_spec xs m xs' \<equiv> 
    mset xs' = mset xs 
  \<and> m\<le>length xs
  \<and> (\<forall>i<m. P\<^sub>1 (xs'!i))  
  \<and> (\<forall>i\<in>{m..<length xs}. P\<^sub>2 (xs'!i))
    "

  lemma partition_spec_alt: "partition_spec xs m xs' \<longleftrightarrow>
    mset xs' = mset xs 
  \<and> m\<le>length xs
  \<and> set (take m xs') \<subseteq> Collect P\<^sub>1
  \<and> set (drop m xs') \<subseteq> Collect P\<^sub>2
  "  
    unfolding partition_spec_def
    by (fastforce simp: set_take_conv_nth set_drop_conv_nth dest: mset_eq_length)  
    
  lemma partition_spec_permute: "mset xs = mset xs\<^sub>1 \<Longrightarrow> partition_spec xs m xs' = partition_spec xs\<^sub>1 m xs'"  
    unfolding partition_spec_def
    by (auto dest: mset_eq_length)
    
    
end

(*
  Step 1: partition the array, and keep track of the set of small/big indices
    in practice, the array will be partitioned into multiple slices, and the sets will be intervals
*)


(* An array together with sets of small/big elements *)
locale is_ppart = partitioning + 
  fixes xs ss bs
  assumes complete: "ss \<union> bs = {0..<length xs}"
  assumes disjoint: "ss \<inter> bs = {}"
  assumes ss_in_P1: "i\<in>ss \<Longrightarrow> P\<^sub>1 (xs!i)"
  assumes bs_in_P2: "i\<in>bs \<Longrightarrow> P\<^sub>2 (xs!i)"
  


context partitioning begin
  
  definition "ppart_spec xs xs' ss bs \<longleftrightarrow> mset xs' = mset xs \<and> is_ppart P\<^sub>1 P\<^sub>2 xs' ss bs"  
    
  abbreviation "ppart_SPEC xs \<equiv> SPEC (\<lambda>(xs',ss,bs). ppart_spec xs xs' ss bs)"
  
  subsection \<open>Step 2: compute mid-index, filter misplaced indexes\<close>

  (*
    Step 2: compute position of bound (first position of big element)
  *)  
  
  definition "ppart_mpos ss \<equiv> card ss"
  definition "ppart_filter m ss bs \<equiv> ({i\<in>ss. m\<le>i},{i\<in>bs. i<m})"
end  
  
(*
  Number of misplaced elements small and big elements is the same.
  Lemma is generalized for sets of indexes, no matter how they are formed.
*)
locale misplaced_elements =
  fixes ss bs n
  assumes SSU: "ss \<union> bs = {0..<n}" "ss \<inter> bs = {}" 
  fixes m ss\<^sub>1 ss\<^sub>2 bs\<^sub>1 bs\<^sub>2
  assumes m_def: "m = card ss"
  assumes ss\<^sub>1_def: "ss\<^sub>1 = {i\<in>ss. i<m}"
  assumes ss\<^sub>2_def: "ss\<^sub>2 = {i\<in>ss. m\<le>i}"
  assumes bs\<^sub>1_def: "bs\<^sub>1 = {i\<in>bs. m\<le>i}"
  assumes bs\<^sub>2_def: "bs\<^sub>2 = {i\<in>bs. i<m}"
begin

  lemma finiteIs1[simp, intro!]:
    "finite ss" "finite bs"
    using SSU
    by (metis finite_Un finite_atLeastLessThan)+
    
  lemma finiteIs2[simp, intro!]:
    "finite ss\<^sub>1" "finite ss\<^sub>2" "finite bs\<^sub>1" "finite bs\<^sub>2"
    unfolding ss\<^sub>1_def ss\<^sub>2_def bs\<^sub>1_def bs\<^sub>2_def by auto

  lemma m_le_n: "m\<le>n" 
  proof - 
    have "card ss + card bs = n"
      using SSU
      by (simp add: card_Un_Int)
      
    thus "m\<le>n" unfolding m_def by auto 
  qed              

  lemma ss_split: "ss = ss\<^sub>1 \<union> ss\<^sub>2"
    and ss_dj: "ss\<^sub>1 \<inter> ss\<^sub>2 = {}"
    unfolding ss\<^sub>1_def ss\<^sub>2_def 
    by auto
    
  lemma bs_split: "bs = bs\<^sub>1 \<union> bs\<^sub>2"
    and bs_dj: "bs\<^sub>1 \<inter> bs\<^sub>2 = {}"
    unfolding bs\<^sub>1_def bs\<^sub>2_def 
    by auto

  lemma low_range_split: "{0..<m} = ss\<^sub>1 \<union> bs\<^sub>2"
    and low_range_dj: "ss\<^sub>1 \<inter> bs\<^sub>2 = {}" 
    unfolding ss\<^sub>1_def bs\<^sub>2_def using SSU m_le_n
    by auto
    
  lemma high_range_split: "{m..<n} = bs\<^sub>1 \<union> ss\<^sub>2"
    and high_range_dj: "bs\<^sub>1 \<inter> ss\<^sub>2 = {}" 
    unfolding bs\<^sub>1_def ss\<^sub>2_def using SSU
    by auto
    
  lemma same_djs: 
    "ss\<^sub>1 \<inter> bs\<^sub>1 = {}"  
    "ss\<^sub>2 \<inter> bs\<^sub>2 = {}"  
    unfolding bs\<^sub>1_def bs\<^sub>2_def ss\<^sub>1_def ss\<^sub>2_def
    by auto
    
  lemma in_range: 
    "ss\<^sub>1 \<subseteq> {0..<n}"          
    "ss\<^sub>2 \<subseteq> {0..<n}"          
    "bs\<^sub>1 \<subseteq> {0..<n}"          
    "bs\<^sub>2 \<subseteq> {0..<n}"
    using SSU
    unfolding bs\<^sub>1_def bs\<^sub>2_def ss\<^sub>1_def ss\<^sub>2_def
    by auto
    
    
  lemma misplaced_same_card:
    shows "card ss\<^sub>2 = card bs\<^sub>2"
  proof -
    from ss_split ss_dj have 1: "card ss\<^sub>1 + card ss\<^sub>2 = m" by (simp add: card_Un_disjoint m_def)
    also from low_range_split[symmetric] have "m = card (ss\<^sub>1 \<union> bs\<^sub>2)" by simp
    also from low_range_dj have "\<dots> = card ss\<^sub>1 + card bs\<^sub>2"   
      by (simp add: card_Un_disjoint)
    finally show ?thesis by simp  
  qed
end  
  
  
locale ppar_step2 = partitioning + is_ppart
begin  
  abbreviation "m \<equiv> ppart_mpos ss"
  
  
  definition "ss\<^sub>1 = {i\<in>ss. i<m}"
  definition "ss\<^sub>2 = fst (ppart_filter m ss bs)"
  
  definition "bs\<^sub>1 = {i\<in>bs. m\<le>i}"
  definition "bs\<^sub>2 = snd (ppart_filter m ss bs)"


  sublocale misplaced: misplaced_elements ss bs "length xs" m ss\<^sub>1 ss\<^sub>2 bs\<^sub>1 bs\<^sub>2 
    apply unfold_locales
    unfolding ppart_mpos_def ppart_filter_def ss\<^sub>1_def ss\<^sub>2_def bs\<^sub>1_def bs\<^sub>2_def
    using complete disjoint
    by auto

  (*
    Same number of misplaced small and big indexes
  *)  
  thm misplaced.misplaced_same_card
  
  (*
    All other indexes are well-placed
  *)  
  lemma low_nbs2_well_placed: assumes "i<m" "i\<notin>bs\<^sub>2" shows "P\<^sub>1 (xs!i)"
  proof -
    from assms misplaced.low_range_split have "i\<in>ss\<^sub>1" by fastforce
    with misplaced.ss_split have "i\<in>ss" by auto
    with ss_in_P1 show ?thesis by auto
  qed  
    
  lemma high_nss2_well_placed: assumes "m\<le>i" "i<length xs" "i\<notin>ss\<^sub>2" shows "P\<^sub>2 (xs!i)"
  proof -
    from assms misplaced.high_range_split have "i\<in>bs\<^sub>1" by fastforce
    with misplaced.bs_split have "i\<in>bs" by auto
    with bs_in_P2 show ?thesis by auto
  qed  

end  
  
subsection \<open>Step 3: compute swaps\<close>
  
  
locale swap_spec_pre = 
  fixes src dst :: "nat set" and xs :: "'a list"
  assumes src_dst_dj: "src \<inter> dst = {}" 
  assumes src_ss: "src \<subseteq> {0..<length xs}"
  assumes dst_ss: "dst \<subseteq> {0..<length xs}"
  assumes card_eq: "card src = card dst"
begin
  lemma finite_src[simp,intro!]: "finite src" using src_ss by (blast intro: finite_subset)
  lemma finite_dst[simp,intro!]: "finite dst" using dst_ss by (blast intro: finite_subset)
end  

locale swap_spec = swap_spec_pre + fixes xs' :: "'a list"
  assumes elems_outside: "i\<notin>src \<union> dst \<Longrightarrow> i<length xs \<Longrightarrow> xs'!i=xs!i"
  assumes elems_src: "i\<in>src \<Longrightarrow> \<exists>j\<in>dst. xs'!i=xs!j"
  assumes elems_dst: "i\<in>dst \<Longrightarrow> \<exists>j\<in>src. xs'!i=xs!j"
  assumes permut: "mset xs' = mset xs"
begin
  lemma length_xs'_eq[simp]: "length xs' = length xs"
    using mset_eq_length[OF permut] by blast

end  
  
context swap_spec_pre begin

  lemma swap_spec_refl: 
    assumes [simp]: "src={}"
    shows "swap_spec src dst xs xs"
    apply unfold_locales
    using card_eq
    by auto


end

definition "swap_SPEC ss bs xs \<equiv> do { ASSERT (swap_spec_pre ss bs xs); SPEC (swap_spec ss bs xs) }"


(* Sanity check lemma *)
lemma swap_spec_exists:
  assumes "swap_spec_pre src dst xs"
  shows "\<exists>xs'. swap_spec src dst xs xs'"
  using assms
proof (induction "card src" arbitrary: src dst)
  case 0
  then interpret swap_spec_pre src dst xs by simp
  
  from 0 card_eq have [simp]: "src={}" "dst={}" by auto
  
  show ?case 
    apply (rule exI[where x=xs])
    apply unfold_locales
    by auto
  
next
  case (Suc n)
  then interpret swap_spec_pre src dst xs by simp

  from \<open>Suc n = card src\<close>[symmetric] card_eq obtain i j src' dst' where 
    [simp]: "src=insert i src'" "dst=insert j dst'" 
    and NI: "i\<notin>src'" "j\<notin>dst'" 
    and CARD: "card src' = n" "card dst' = n"
    by (auto simp: card_Suc_eq_finite)
    
  have [simp]: "i<length xs" "j<length xs" using src_ss dst_ss by auto
    
  have "swap_spec_pre src' dst' xs"
    apply unfold_locales
    using src_dst_dj src_ss dst_ss card_eq CARD
    by auto
  with Suc.hyps(1)[of src' dst'] obtain xs' where "swap_spec src' dst' xs xs'" 
    using CARD by blast
  then interpret IH: swap_spec src' dst' xs xs' .
    
  have "swap_spec src dst xs (swap xs' i j)"
    apply unfold_locales
    subgoal for k by (auto simp: IH.elems_outside)
    subgoal for k
      apply (cases "k=i"; simp)
      subgoal
        using IH.elems_outside IH.elems_src NI(2) \<open>j < length xs\<close> by blast
      subgoal
        by (metis IH.elems_src \<open>dst = insert j dst'\<close> \<open>src = insert i src'\<close> disjoint_iff insertCI src_dst_dj swap_indep)
      done
    subgoal for k
      apply (cases "k=j"; simp)
      subgoal
        using IH.elems_dst IH.elems_outside NI(1) \<open>i < length xs\<close> by blast
      subgoal
        by (metis IH.elems_dst \<open>dst = insert j dst'\<close> \<open>src = insert i src'\<close> disjoint_iff insertCI src_dst_dj swap_indep)
      done
    subgoal
      by (simp add: IH.permut)
    done  
  thus ?case ..    
qed      
  
  
context ppar_step2 begin    
  (*
    ss\<^sub>2 and bs\<^sub>2 satisfy precondition for swapping
  *)
  lemma swap_spec_pre: "swap_spec_pre ss\<^sub>2 bs\<^sub>2 xs"
    apply unfold_locales
    using misplaced.same_djs misplaced.in_range
    by (auto simp: misplaced.misplaced_same_card)
    
end    
  
locale ppar_step3 = ppar_step2 + swap_spec ss\<^sub>2 bs\<^sub>2 xs
begin  

  lemma "mset xs' = mset xs" by (rule permut)

  
  lemma elems_ss1: "i\<in>ss\<^sub>1 \<Longrightarrow> xs'!i = xs!i"
    using elems_outside[of i] misplaced.in_range misplaced.low_range_dj misplaced.ss_dj
    by fastforce

  lemma elems_bs1: "i\<in>bs\<^sub>1 \<Longrightarrow> xs'!i = xs!i"
    using elems_outside[of i] misplaced.in_range misplaced.high_range_dj misplaced.bs_dj
    by fastforce
        
  lemma partitioned1: assumes "i<m" shows "P\<^sub>1 (xs'!i)" 
  proof -
    have "i\<in>ss\<^sub>1 \<union> bs\<^sub>2"
      using assms misplaced.low_range_split by fastforce
    then show ?thesis 
      apply rule
      subgoal 
        apply (simp add: elems_ss1)
        using misplaced.ss_split ss_in_P1 by auto
      subgoal 
        by (metis UnCI elems_dst misplaced.ss_split ss_in_P1)
      done
      
  qed  
      
  lemma partitioned2: assumes "m\<le>i" "i<length xs" shows "P\<^sub>2 (xs'!i)"
  proof -
    have "i\<in>ss\<^sub>2 \<union> bs\<^sub>1"
      using assms misplaced.high_range_split by fastforce
    then show ?thesis 
      apply rule
      subgoal
        by (metis bs_in_P2 dual_order.refl elems_src in_mono le_sup_iff misplaced.bs_split)
      subgoal 
        apply (simp add: elems_bs1)
        using misplaced.bs_split bs_in_P2 by auto
      done
      
  qed
    

  lemma is_valid_partition: "partition_spec xs m xs'"
    unfolding partition_spec_def
    by (auto simp: permut misplaced.m_le_n partitioned1 partitioned2)

end


  


subsection \<open>The Algorithm\<close>

context partitioning begin
  definition "ppart1 xs \<equiv> do {
    (xs,ss,bs) \<leftarrow> ppart_SPEC xs;
    let m = ppart_mpos ss;

    let (ss\<^sub>2,bs\<^sub>2) = ppart_filter m ss bs;
    
    xs \<leftarrow> swap_SPEC ss\<^sub>2 bs\<^sub>2 xs;
  
    RETURN (m,xs)
  }"

  lemma ppart1_valid_partitition: "ppart1 xs \<le> SPEC (\<lambda>(m,xs'). partition_spec xs m xs')"
    unfolding ppart1_def ppart_spec_def swap_SPEC_def
    apply refine_vcg
    apply clarsimp_all
  proof -
    fix xs\<^sub>1 ss bs ss\<^sub>2X bs\<^sub>2X
    assume 
      pp_flt: "ppart_filter (ppart_mpos ss) ss bs = (ss\<^sub>2X, bs\<^sub>2X)" and
      [simp]: "mset xs\<^sub>1 = mset xs" and
      "is_ppart P\<^sub>1 P\<^sub>2 xs\<^sub>1 ss bs"
  
      
    interpret is_ppart P\<^sub>1 P\<^sub>2 xs\<^sub>1 ss bs by fact  
    interpret ppar_step2 P\<^sub>1 P\<^sub>2 xs\<^sub>1 ss bs by unfold_locales
    
    have [simp]: "ss\<^sub>2X = ss\<^sub>2" "bs\<^sub>2X = bs\<^sub>2" unfolding ss\<^sub>2_def bs\<^sub>2_def using pp_flt
      by auto

    show "swap_spec_pre ss\<^sub>2X bs\<^sub>2X xs\<^sub>1" using swap_spec_pre by simp 
      
    fix xs'  
    assume sspec: "swap_spec ss\<^sub>2X bs\<^sub>2X xs\<^sub>1 xs'"
  
          
    interpret swap_spec ss\<^sub>2 bs\<^sub>2 xs\<^sub>1 xs' 
      using sspec by simp
      
    interpret ppar_step3 P\<^sub>1 P\<^sub>2 xs\<^sub>1 ss bs xs'
      by unfold_locales 
      
    show "partition_spec xs m xs'"  
      using \<open>mset xs\<^sub>1 = mset xs\<close> is_valid_partition partition_spec_permute by blast
  qed    
end
  
section \<open>Refinement to Parallel Partitioning\<close>  
  
context partitioning begin
  
  (*
    Parallel partitioning with interval, abstract level
  *)
  
  lemma ppart_spec_merge:
    assumes "ppart_spec xs\<^sub>1 xs\<^sub>1' ss\<^sub>1 bs\<^sub>1"
    assumes "ppart_spec xs\<^sub>2 xs\<^sub>2' ss\<^sub>2 bs\<^sub>2"
    defines "ss\<^sub>2' \<equiv> (+)(length xs\<^sub>1)`ss\<^sub>2"
    defines "bs\<^sub>2' \<equiv> (+)(length xs\<^sub>1)`bs\<^sub>2"
    shows "ppart_spec (xs\<^sub>1@xs\<^sub>2) (xs\<^sub>1'@xs\<^sub>2') (ss\<^sub>1 \<union> ss\<^sub>2') (bs\<^sub>1 \<union> bs\<^sub>2')"
    using assms(1,2)
    unfolding ppart_spec_def 
  proof clarsimp
    assume "mset xs\<^sub>1' = mset xs\<^sub>1" "mset xs\<^sub>2' = mset xs\<^sub>2"
    hence [simp]: "length xs\<^sub>1' = length xs\<^sub>1" "length xs\<^sub>2' = length xs\<^sub>2"
      by (auto dest: mset_eq_length)
  
  
    assume "is_ppart P\<^sub>1 P\<^sub>2 xs\<^sub>1' ss\<^sub>1 bs\<^sub>1" "is_ppart P\<^sub>1 P\<^sub>2 xs\<^sub>2' ss\<^sub>2 bs\<^sub>2"

    then interpret p1: is_ppart P\<^sub>1 P\<^sub>2 xs\<^sub>1' ss\<^sub>1 bs\<^sub>1 + p2: is_ppart P\<^sub>1 P\<^sub>2 xs\<^sub>2' ss\<^sub>2 bs\<^sub>2 .
    
    from p2.complete have sb\<^sub>2_Un: "ss\<^sub>2' \<union> bs\<^sub>2' = {length xs\<^sub>1' ..< length (xs\<^sub>1'@xs\<^sub>2')}"
      unfolding ss\<^sub>2'_def bs\<^sub>2'_def
      by (auto simp flip: image_Un)
      
    from p2.disjoint have sb\<^sub>2_dj: "ss\<^sub>2' \<inter> bs\<^sub>2' = {}"
      unfolding ss\<^sub>2'_def bs\<^sub>2'_def
      by auto
      
    have sb'_dj: "(ss\<^sub>1\<union>bs\<^sub>1) \<inter> (ss\<^sub>2'\<union>bs\<^sub>2') = {}"  
      apply (simp add: p1.complete)
      unfolding ss\<^sub>2'_def bs\<^sub>2'_def
      by auto
      
    
    from p1.complete have ss\<^sub>1_in_range: "\<And>i. i\<in>ss\<^sub>1 \<Longrightarrow> i<length xs\<^sub>1" by auto 
    from p1.complete have bs\<^sub>1_in_range: "\<And>i. i\<in>bs\<^sub>1 \<Longrightarrow> i<length xs\<^sub>1" by auto 

    from sb\<^sub>2_Un have ss\<^sub>2'_in_range: "\<And>i. i\<in>ss\<^sub>2' \<Longrightarrow> length xs\<^sub>1\<le>i" by auto 
    from sb\<^sub>2_Un have bs\<^sub>2'_in_range: "\<And>i. i\<in>bs\<^sub>2' \<Longrightarrow> length xs\<^sub>1\<le>i" by auto 
    
          
    show "is_ppart P\<^sub>1 P\<^sub>2 (xs\<^sub>1' @ xs\<^sub>2') (ss\<^sub>1 \<union> ss\<^sub>2') (bs\<^sub>1 \<union> bs\<^sub>2')"
      apply unfold_locales
      subgoal
        apply (rule trans[where s="(ss\<^sub>1\<union>bs\<^sub>1)\<union>(ss\<^sub>2' \<union> bs\<^sub>2')"])
        apply blast
        apply (simp add: sb\<^sub>2_Un p1.complete) by auto
      subgoal
        using p1.disjoint p2.disjoint sb\<^sub>2_dj sb'_dj by blast     
      subgoal for i
        apply (auto simp: nth_append p1.ss_in_P1 ss\<^sub>1_in_range dest: ss\<^sub>2'_in_range)
        apply (auto simp: ss\<^sub>2'_def p2.ss_in_P1)
        done
      subgoal for i
        apply (auto simp: nth_append p1.bs_in_P2 bs\<^sub>1_in_range dest: bs\<^sub>2'_in_range)
        apply (auto simp: bs\<^sub>2'_def p2.bs_in_P2)
        done
      done    
  qed      
        
  
  definition "partition_slices d xs = RECT (\<lambda>partition_slices (d,xs). do {
    ASSERT (d>0);
    let len = length xs;
    if (len \<le> d) then do {
      (xs,ss,bs) \<leftarrow> ppart_SPEC xs;
      RETURN (xs,ss,bs)
    } else do {
      let si = len - d;
      (((ss\<^sub>1,bs\<^sub>1),(ss\<^sub>2,bs\<^sub>2)),xs) \<leftarrow> WITH_SPLIT si xs (\<lambda>xs\<^sub>1 xs\<^sub>2. do {
        ((xs\<^sub>1,ivs\<^sub>1),(xs\<^sub>2,ivs\<^sub>2)) \<leftarrow> nres_par (partition_slices) (ppart_SPEC) (d,xs\<^sub>1) xs\<^sub>2;
        RETURN (((ivs\<^sub>1,ivs\<^sub>2),xs\<^sub>1,xs\<^sub>2))
      });
      
      let ss\<^sub>2 = (+)si`ss\<^sub>2;
      let bs\<^sub>2 = (+)si`bs\<^sub>2;
      
      RETURN (xs,ss\<^sub>1\<union>ss\<^sub>2, bs\<^sub>1 \<union> bs\<^sub>2)
    }
  }) (d,xs)"
  
  lemma ppart_spec_imp_len_eq: "ppart_spec xs xs' ss bs \<Longrightarrow> length xs' = length xs"
    unfolding ppart_spec_def
    by (auto dest: mset_eq_length)
  
  
  lemma partition_slices_refine_aux: "d>0 \<Longrightarrow> partition_slices d xs \<le> ppart_SPEC xs"
    unfolding partition_slices_def
    
    thm RECT_rule
    
    apply (refine_vcg RECT_rule[
      where 
            V="measure (\<lambda>(d,xs). length xs)" 
        and pre="\<lambda>(d,xs). d>0" 
        and M="\<lambda>(d,xs). Refine_Basic.SPEC (\<lambda>(xs', ss, bs). ppart_spec xs xs' ss bs)", 
      THEN order_trans])
    apply (all \<open>(thin_tac "RECT _ = _")?\<close>)
    
    subgoal by simp  
    subgoal by simp  
    subgoal by clarsimp
    subgoal by clarsimp
    subgoal by simp 
    
    apply (drule sym[of "length _" "length _ - _"]) (* Turn around problematic premise for simplifier *)
    
    apply (rule order_trans)
    apply rprems
    subgoal by force
    subgoal by auto
    
    apply refine_vcg
    subgoal by (auto dest: ppart_spec_imp_len_eq)
    subgoal by (auto dest: ppart_spec_imp_len_eq)
    subgoal by (auto intro: ppart_spec_merge)
    subgoal by auto
    done    
    
    
  lemma partition_slices_refine: "\<lbrakk> (xs,xs')\<in>\<langle>Id\<rangle>list_rel; d>0\<rbrakk> \<Longrightarrow> partition_slices d xs \<le> \<Down>Id (ppart_SPEC xs')"
    by (auto simp: partition_slices_refine_aux)
  
    
    
    
end
    

section \<open>Refinement to Parallel Swap\<close>

  
(* TODO: Move *)

lemma sl_indexes_finite[simp, intro!]: "finite (sl_indexes s)" by (auto simp: sl_indexes_def)

lemma sl_struct_join_split: "sl_struct_join (sl_struct_split I s) (sl_struct_split (-I) s) = s"
  unfolding sl_struct_join_def sl_struct_split_def
  by (auto simp: map2_map_conv map_nth) 


lemma sl_join_split_eq: "sl_join (sl_split s xs) (sl_split (-s) xs) = xs"  
  unfolding sl_join_def sl_split_def 
  apply (rewrite at "_ = \<hole>" map_nth[symmetric])
  by (auto simp: map2_map_conv)
  
    
thm list_induct2    
    
locale swap_opt_spec_pre = 
  fixes src dst :: "nat set" and xs :: "'a option list"
  assumes src_dst_dj: "src \<inter> dst = {}" 
  assumes src_ss: "src \<subseteq> sl_indexes' xs"
  assumes dst_ss: "dst \<subseteq> sl_indexes' xs"
  assumes card_eq: "card src = card dst"
begin  

  lemma finite_src[simp,intro!]: "finite src" apply (rule finite_subset[OF src_ss]) by auto
  lemma finite_dst[simp,intro!]: "finite dst" apply (rule finite_subset[OF dst_ss]) by auto

   
  (*assumes idxs_dj: "src \<inter> dst = {}"
  assumes idxs_card_eq: "card src = card dst"
  *)
  lemma idxs_in_bounds: "src\<union>dst \<subseteq> sl_indexes' xs" using src_ss dst_ss by auto
  

end
  
locale swap_opt_spec = swap_opt_spec_pre +  
  fixes xs'
  assumes struct_eq[simp]: "sl_struct xs' = sl_struct xs"
  assumes elems_outside: "i\<notin>src \<union> dst \<Longrightarrow> i\<in>sl_indexes' xs \<Longrightarrow> sl_get xs' i=sl_get xs i"
  assumes elems_src: "i\<in>src \<Longrightarrow> \<exists>j\<in>dst. sl_get xs' i = sl_get xs j"
  assumes elems_dst: "i\<in>dst \<Longrightarrow> \<exists>j\<in>src. sl_get xs' i = sl_get xs j"
  assumes permut: "mset xs' = mset xs"
begin

  lemma length_eq[simp]: "length xs' = length xs" using mset_eq_length[OF permut] .




end  
  
  

locale swap_opt_spec_pre_split = swap_opt_spec_pre ss bs xs for ss bs xs + 
  fixes ss\<^sub>1 ss\<^sub>2 bs\<^sub>1 bs\<^sub>2
  assumes split_complete: "ss = ss\<^sub>1 \<union> ss\<^sub>2" "bs = bs\<^sub>1 \<union> bs\<^sub>2"
  assumes split_dj: "ss\<^sub>1 \<inter> ss\<^sub>2 = {}" "bs\<^sub>1 \<inter> bs\<^sub>2 = {}"
  assumes split_card_eq1: "card bs\<^sub>1 = card ss\<^sub>1"
  assumes ss\<^sub>1_ne: "ss\<^sub>1\<noteq>{}"
begin  
  lemma finites[simp,intro!]: 
    "finite ss\<^sub>1"
    "finite ss\<^sub>2"
    "finite bs\<^sub>1"
    "finite bs\<^sub>2"
    using finite_src finite_dst
    by (auto simp: split_complete)

  lemma card_ss_eq: "card ss = card ss\<^sub>1 + card ss\<^sub>2" using split_complete split_dj by (auto simp: card_Un_disjoint)
  lemma card_bs_eq: "card bs = card bs\<^sub>1 + card bs\<^sub>2" using split_complete split_dj by (auto simp: card_Un_disjoint)

  lemma split_card_eq2: "card bs\<^sub>2 = card ss\<^sub>2"
    by (metis card_bs_eq card_ss_eq diff_add_inverse card_eq split_card_eq1)

  lemmas split_card_eq = split_card_eq1 split_card_eq2
  
  
  sublocale p1: swap_opt_spec_pre ss\<^sub>1 bs\<^sub>1 "(sl_split (ss\<^sub>1\<union>bs\<^sub>1) xs)"
    apply unfold_locales
    using split_dj src_dst_dj idxs_in_bounds
    apply (auto simp: split_card_eq)
    subgoal using split_complete(1) split_complete(2) by blast
    subgoal by (auto simp: sl_indexes_split split_complete)
    subgoal by (auto simp: sl_indexes_split split_complete)
    done

  sublocale p2: swap_opt_spec_pre ss\<^sub>2 bs\<^sub>2 "(sl_split (-ss\<^sub>1-bs\<^sub>1) xs)"
    apply unfold_locales
    using split_dj src_dst_dj idxs_in_bounds
    apply (auto simp: split_card_eq)
    subgoal using split_complete(1) split_complete(2) by blast
    subgoal by (auto simp: sl_indexes_split split_complete)
    subgoal by (auto simp: sl_indexes_split split_complete)
    done
  
  lemma extreme:
    assumes "ss\<^sub>2={}"  
    shows "bs\<^sub>2={}" "ss\<^sub>1=ss" "bs\<^sub>1=bs"
    using assms split_complete split_dj split_card_eq
    by auto
    
  lemma idxs1_in_bounds: "ss\<^sub>1 \<union> bs\<^sub>1 \<subseteq> sl_indexes' xs"  
    using dst_ss split_complete(1) split_complete(2) src_ss by blast

  lemma decreasing: "card ss\<^sub>2 < card ss"  
    using card_ss_eq ss\<^sub>1_ne by fastforce
    
    
  lemma join:
    assumes "swap_opt_spec ss\<^sub>1 bs\<^sub>1 (sl_split (ss\<^sub>1\<union>bs\<^sub>1) xs) xs\<^sub>1'"
    assumes "swap_opt_spec ss\<^sub>2 bs\<^sub>2 (sl_split (-ss\<^sub>1-bs\<^sub>1) xs) xs\<^sub>2'"
    shows "swap_opt_spec ss bs xs (sl_join xs\<^sub>1' xs\<^sub>2')"
  proof -
    interpret p1: swap_opt_spec ss\<^sub>1 bs\<^sub>1 "(sl_split (ss\<^sub>1\<union>bs\<^sub>1) xs)" xs\<^sub>1' by fact
    interpret p2: swap_opt_spec ss\<^sub>2 bs\<^sub>2 "(sl_split (-ss\<^sub>1-bs\<^sub>1) xs)" xs\<^sub>2' by fact
  
    
    have COMPAT[simp]: "sl_compat (sl_struct_split (ss\<^sub>1 \<union> bs\<^sub>1) (sl_struct xs)) (sl_struct_split (- ss\<^sub>1 - bs\<^sub>1) (sl_struct xs))"
      by (auto intro: sl_compat_splitI)
    
      
    have "mset xs = mset (sl_join (sl_split (ss\<^sub>1\<union>bs\<^sub>1) xs) (sl_split (-ss\<^sub>1-bs\<^sub>1) xs))"  
      using sl_join_split_eq[of "ss\<^sub>1\<union>bs\<^sub>1" xs]
      by simp
    also have "\<dots> = mset (sl_split (ss\<^sub>1 \<union> bs\<^sub>1) xs) + mset (sl_split (- ss\<^sub>1 - bs\<^sub>1) xs) - replicate_mset (length xs) None"  
      by (simp add: mset_join_idxs_eq)
    finally have mset_xs_conv: "mset xs = mset (sl_split (ss\<^sub>1 \<union> bs\<^sub>1) xs) + mset (sl_split (- ss\<^sub>1 - bs\<^sub>1) xs) - replicate_mset (length xs) None" .
      
      
    show ?thesis
      apply unfold_locales
      subgoal
        using sl_struct_join_split[of "ss\<^sub>1\<union>bs\<^sub>1"]
        by auto
      subgoal
        apply simp
        apply (subst sl_get_join)
        by (auto dest: sl_indexes_lengthD simp: split_complete sl_indexes_split p2.elems_outside sl_get_split)
      subgoal for i
        apply (simp add: split_complete; safe)  
        subgoal
          by (metis Un_iff COMPAT p1.elems_src p1.src_ss p1.struct_eq p2.struct_eq sl_get_join1 sl_get_split sl_struct_split subset_iff)
        subgoal 
          apply (frule p2.elems_src; clarsimp)
          by (metis COMPAT IntD1 UnI2 p1.struct_eq p2.dst_ss p2.src_ss p2.struct_eq sl_get_join2 sl_get_split sl_indexes_split sl_struct_split subsetD)
        done
      subgoal
        apply (simp add: split_complete; safe)  
        subgoal by (metis COMPAT in_mono p1.dst_ss p1.elems_dst p1.struct_eq p2.struct_eq sl_get_join1 sl_get_split sl_struct_split sup_ge1)
        subgoal 
          apply (frule p2.elems_dst; clarsimp)
          by (metis COMPAT IntD1 Un_Int_eq(2) in_mono p1.struct_eq p2.dst_ss p2.src_ss p2.struct_eq sl_get_join2 sl_get_split sl_indexes_split sl_struct_split)
        done
      subgoal
        by (simp add: mset_join_idxs_eq mset_xs_conv p1.permut p2.permut)
      done  
  qed        

end
  

definition "swap_opt_SPEC ss bs xs \<equiv> do {ASSERT (swap_opt_spec_pre ss bs xs); SPEC (swap_opt_spec ss bs xs)}"

definition "split_sets_eq_SPEC ss bs = do {
  ASSERT (ss\<noteq>{} \<and> bs\<noteq>{} \<and> finite ss \<and> finite bs);
  SPEC (\<lambda>((ss\<^sub>1,ss\<^sub>2),(bs\<^sub>1,bs\<^sub>2)). 
    ss = ss\<^sub>1 \<union> ss\<^sub>2 \<and> bs = bs\<^sub>1 \<union> bs\<^sub>2
  \<and> ss\<^sub>1 \<inter> ss\<^sub>2 = {} \<and> bs\<^sub>1 \<inter> bs\<^sub>2 = {}
  \<and> ss\<^sub>1 \<noteq> {}
  \<and> card ss\<^sub>1 = card bs\<^sub>1
  )
}"


lemma (in swap_opt_spec_pre) split_sets_eq_SPEC_swap_rl:
  shows "src\<noteq>{} \<Longrightarrow> split_sets_eq_SPEC src dst \<le> SPEC (\<lambda>((ss\<^sub>1,ss\<^sub>2),(bs\<^sub>1,bs\<^sub>2)). swap_opt_spec_pre_split src dst xs ss\<^sub>1 ss\<^sub>2 bs\<^sub>1 bs\<^sub>2)"
  unfolding split_sets_eq_SPEC_def
  apply refine_vcg
  subgoal using card_eq by force
  subgoal by simp
  subgoal by simp
  apply unfold_locales
  apply clarsimp_all
  done

(*
definition "swap_opt_pre_split_SPEC ss bs xs \<equiv> do {
  ASSERT (swap_opt_spec_pre ss bs xs);
  SPEC (\<lambda>((ss\<^sub>1,ss\<^sub>2),(bs\<^sub>1,bs\<^sub>2)). swap_opt_spec_pre_split ss bs xs ss\<^sub>1 ss\<^sub>2 bs\<^sub>1 bs\<^sub>2)
}"
*)


definition "par_swap_aux ss bs xs \<equiv> RECT (\<lambda>par_swap (ss,bs,xs). do {
  ASSERT (swap_opt_spec_pre ss bs xs);
    
  ((ss\<^sub>1,ss\<^sub>2),(bs\<^sub>1,bs\<^sub>2)) \<leftarrow> split_sets_eq_SPEC ss bs;
  
  if (ss\<^sub>2={}) then do {
    ASSERT (bs\<^sub>2={} \<and> ss\<^sub>1=ss \<and> bs\<^sub>1=bs);
    swap_opt_SPEC ss\<^sub>1 bs\<^sub>1 xs
  } else do {
    (_,xs) \<leftarrow> WITH_IDXS (ss\<^sub>1\<union>bs\<^sub>1) xs (\<lambda>xs\<^sub>1 xs\<^sub>2. do {
      (xs\<^sub>1,xs\<^sub>2) \<leftarrow> nres_par (\<lambda>(ss\<^sub>1,bs\<^sub>1,xs\<^sub>1). (swap_opt_SPEC ss\<^sub>1 bs\<^sub>1 xs\<^sub>1)) (par_swap) (ss\<^sub>1,bs\<^sub>1,xs\<^sub>1) (ss\<^sub>2,bs\<^sub>2,xs\<^sub>2);
      RETURN ((),xs\<^sub>1,xs\<^sub>2)
    });
    RETURN xs
  }
}) (ss,bs,xs)"  




lemma par_swap_aux_correct:
  shows "ss\<noteq>{} \<Longrightarrow> par_swap_aux ss bs xs \<le> swap_opt_SPEC ss bs xs"
  unfolding par_swap_aux_def swap_opt_SPEC_def
  supply R = RECT_rule[where V="measure (card o fst)" and pre="\<lambda>(ss,bs,xs). ss\<noteq>{} \<and> swap_opt_spec_pre ss bs xs"]
  apply refine_vcg
  apply (refine_vcg R[where M="\<lambda>(ss,bs,xs). SPEC (swap_opt_spec ss bs xs)", THEN order_trans])
  apply (all \<open>(thin_tac "RECT _ = _")?\<close>)
  subgoal by simp
  subgoal by simp
  subgoal by simp
  subgoal by simp
  
  apply (clarsimp)
  subgoal for par_swap ss bs xs proof goal_cases
    case 1
    
    note IH = \<open>\<lbrakk>_;_\<rbrakk> \<Longrightarrow> par_swap _ \<le>  _\<close>
    
    note [simp] = \<open>ss\<noteq>{}\<close>
    
    note SOS_PRE[simp] = \<open>swap_opt_spec_pre ss bs xs\<close>
    
    interpret swap_opt_spec_pre ss bs xs by fact
    
    show ?case 
      apply (rule split_sets_eq_SPEC_swap_rl[THEN order_trans])
      apply simp
      apply (rule refine_vcg)
      apply clarsimp
      subgoal for ss\<^sub>1 ss\<^sub>2 bs\<^sub>1 bs\<^sub>2 proof goal_cases
        case 1
        then interpret swap_opt_spec_pre_split ss bs xs ss\<^sub>1 ss\<^sub>2 bs\<^sub>1 bs\<^sub>2 .
        
        show ?thesis
          apply (refine_vcg)
          subgoal by (simp add: extreme)
          subgoal by (simp add: extreme)
          subgoal by (simp add: extreme)
          subgoal by (simp add: extreme)
          subgoal by (simp add: extreme)
          subgoal by (rule idxs1_in_bounds)
          subgoal
            using p1.swap_opt_spec_pre_axioms
            by clarsimp 
          apply clarsimp  
          subgoal for xs\<^sub>1'
            apply (rule IH[THEN order_trans])
            subgoal
              using p2.swap_opt_spec_pre_axioms
              by clarsimp 
            subgoal by (rule decreasing)
            apply clarsimp
            subgoal for xs\<^sub>2' proof goal_cases
              case 1
              then interpret 
                p1: swap_opt_spec ss\<^sub>1 bs\<^sub>1 "sl_split (ss\<^sub>1 \<union> bs\<^sub>1) xs" xs\<^sub>1' +
                p2: swap_opt_spec ss\<^sub>2 bs\<^sub>2 "sl_split (- ss\<^sub>1 - bs\<^sub>1) xs" xs\<^sub>2' by simp_all
              from 1 join have "swap_opt_spec ss bs xs (sl_join xs\<^sub>1' xs\<^sub>2')" by simp
              then show ?thesis
                by simp
            qed  
            done
          done
      qed
      done
  qed
  subgoal by simp
done  
            

definition "par_swap ss bs xs \<equiv> do {
  if (ss={}) then RETURN xs
  else do {
    let xs = sl_of_list xs;
    xs \<leftarrow> par_swap_aux ss bs xs;
    RETURN (list_of_sl xs)
  }
}"



context swap_spec_pre begin

  lemma to_opt: "swap_opt_spec_pre src dst (sl_of_list xs)"
    apply unfold_locales
    using src_dst_dj src_ss dst_ss card_eq
    by auto
  


end

(* TODO: Move *)
lemma mset_of_list_permut: "mset xs = mset (sl_of_list xs\<^sub>0) \<Longrightarrow> mset (list_of_sl xs) = mset xs\<^sub>0" 
  unfolding sl_of_list_def list_of_sl_def
  by (simp add: mset_map_id)




context swap_opt_spec begin

  lemma to_plain:
    assumes [simp]: "xs = sl_of_list xs\<^sub>0"
    shows "swap_spec src dst xs\<^sub>0 (list_of_sl xs')"
    apply unfold_locales
    subgoal by (simp add: src_dst_dj)
    subgoal using src_ss by simp
    subgoal using dst_ss by simp
    subgoal by (simp add: card_eq)
    subgoal for i using elems_outside[of i] by simp
    subgoal for i using elems_src[of i] by simp
    subgoal for i using elems_dst[of i] by simp
    subgoal using permut by (simp add: mset_of_list_permut)
    done

end
  
lemma par_swap_refine_aux: "par_swap ss bs xs \<le> swap_SPEC ss bs xs"
  unfolding par_swap_def swap_SPEC_def
  apply refine_vcg
  apply (simp add: swap_spec_pre.swap_spec_refl)
  apply (rule order_trans[OF par_swap_aux_correct])
  apply simp
  apply (simp add: swap_opt_SPEC_def)
  apply refine_vcg
  apply (simp add: swap_spec_pre.to_opt)
  apply (simp add: swap_opt_spec.to_plain)
  done

lemma par_swap_refine: "\<lbrakk>(ss,ss')\<in>\<langle>Id\<rangle>set_rel; (bs,bs')\<in>\<langle>Id\<rangle>set_rel; (xs,xs')\<in>\<langle>Id\<rangle>list_rel\<rbrakk> 
  \<Longrightarrow> par_swap ss bs xs \<le>\<Down>(\<langle>Id\<rangle>list_rel) (swap_SPEC ss' bs' xs')"
  by (auto simp: par_swap_refine_aux)
  
  
  
section \<open>Wrap-Up: Parallel Algorithm on Abstract Level\<close>
  
context partitioning begin

definition "ppart2 d xs \<equiv> do {
  (xs,ss,bs) \<leftarrow> partition_slices d xs;
  let m = ppart_mpos ss;

  let (ss\<^sub>2,bs\<^sub>2) = ppart_filter m ss bs;
  
  xs \<leftarrow> par_swap ss\<^sub>2 bs\<^sub>2 xs;

  RETURN (m,xs)
}"
  
lemma ppart2_refine: "\<lbrakk> 0<d; (xs,xs')\<in>\<langle>Id\<rangle>list_rel \<rbrakk> \<Longrightarrow> ppart2 d xs \<le> \<Down>Id (ppart1 xs')"
  unfolding ppart2_def ppart1_def
  apply (refine_rcg partition_slices_refine par_swap_refine)
  by auto

end  

section "Interval Lists" 
  
type_synonym iv = "nat \<times> nat"

definition iv_\<alpha> :: "iv \<Rightarrow> nat set" where "iv_\<alpha> \<equiv> \<lambda>(l,h). {l..<h}"
definition iv_invar :: "iv \<Rightarrow> bool" where "iv_invar \<equiv> \<lambda>(l,h). l<h"

definition iv_make :: "nat \<Rightarrow> nat \<Rightarrow> iv" where "iv_make l h \<equiv> (l,h)"

lemma iv_make_\<alpha>[simp]: "iv_\<alpha> (iv_make l h) = {l..<h}"
  and iv_make_invar[simp]: "l<h \<Longrightarrow> iv_invar (iv_make l h)"
  unfolding iv_make_def iv_\<alpha>_def iv_invar_def by auto

type_synonym ivl = "iv list"

definition ivl_\<alpha> :: "ivl \<Rightarrow> nat set" where "ivl_\<alpha> ivls = \<Union>{ {l..<h} | l h. (l,h)\<in>set ivls }"

locale ivl_invar =
  fixes ivls :: ivl
  assumes distinct: "distinct ivls"
  assumes non_empty: "(l,h)\<in>set ivls \<Longrightarrow> l<h"
  assumes non_overlapping: "\<lbrakk>i\<^sub>1\<in>set ivls; i\<^sub>2\<in>set ivls; i\<^sub>1\<noteq>i\<^sub>2\<rbrakk> \<Longrightarrow> case_prod atLeastLessThan i\<^sub>1 \<inter> case_prod atLeastLessThan i\<^sub>2 = {}"
begin

  lemma in_set_ivlsD: "\<lbrakk> (l,h)\<in>set ivls \<rbrakk> \<Longrightarrow> {l..<h} \<subseteq> ivl_\<alpha> ivls \<and> l<h"
    using non_empty
    by (auto simp: ivl_\<alpha>_def)
  
end  


lemma ivl_\<alpha>_empty_list[simp]: "ivl_\<alpha> [] = {}" by (simp add: ivl_\<alpha>_def)

lemma ivl_\<alpha>_Cons[simp]: "ivl_\<alpha> ((l,h)#ivls) = {l..<h} \<union> ivl_\<alpha> ivls"
  by (auto simp: ivl_\<alpha>_def)
  
lemma ivl_\<alpha>_append[simp]: "ivl_\<alpha> (ivls\<^sub>1@ivls\<^sub>2) = ivl_\<alpha> ivls\<^sub>1 \<union> ivl_\<alpha> ivls\<^sub>2"
  apply (auto simp: ivl_\<alpha>_def)
  by (metis atLeastLessThan_iff)

lemma in_ivl_\<alpha>_conv: "x\<in>ivl_\<alpha> ivls \<longleftrightarrow> (\<exists>(l,h)\<in>set ivls. x\<in>{l..<h})"  
  unfolding ivl_\<alpha>_def 
  by (auto 0 3)
  
lemma iv_dj_ivl_\<alpha>_conv: "{l..<h} \<inter> ivl_\<alpha> ivls = {} \<longleftrightarrow> (\<forall>(l',h')\<in>set ivls. {l..<h} \<inter> {l'..<h'} = {})"  
  apply (auto 0 3 simp: in_ivl_\<alpha>_conv)
  unfolding ivl_\<alpha>_def
  by (smt (verit, ccfv_threshold) Int_iff Union_iff atLeastLessThan_iff empty_iff less_or_eq_imp_le linorder_not_le mem_Collect_eq)
  
lemma in_set_ivls_\<alpha>: "(l,h)\<in>set ivls \<Longrightarrow> {l..<h} \<subseteq> ivl_\<alpha> ivls"  
  by (auto simp: in_set_conv_decomp)
  
lemma ivl_\<alpha>_dj_conv: "ivl_\<alpha> ivls\<^sub>1 \<inter> ivl_\<alpha> ivls\<^sub>2 = {} \<longleftrightarrow> (\<forall>(l,h)\<in>set ivls\<^sub>1. \<forall>(l',h')\<in>set ivls\<^sub>2. {l..<h} \<inter> {l'..<h'} = {})"
  apply (auto simp: in_set_conv_decomp in_ivl_\<alpha>_conv) 
  by (metis Int_iff UnCI atLeastLessThan_iff empty_iff less_le_not_le linorder_not_le)
  
  
lemma ivl_invar_empty_list[simp]: "ivl_invar []" by (simp add: ivl_invar_def) 
  
lemma ivl_invar_Cons[simp]: "ivl_invar ((l,h)#ivls) \<longleftrightarrow> l<h \<and> {l..<h} \<inter> ivl_\<alpha> ivls = {} \<and> ivl_invar ivls"  
  unfolding ivl_invar_def
  apply (intro conjI iffI)
  subgoal by auto
  subgoal apply (auto simp: in_ivl_\<alpha>_conv) by (metis order_le_less_trans)
  subgoal by auto
  subgoal by auto
  subgoal by (clarsimp simp: in_ivl_\<alpha>_conv)
  subgoal apply (clarsimp simp: in_ivl_\<alpha>_conv) 
    by (metis atLeastLessThan_iff disjoint_iff dual_order.refl in_ivl_\<alpha>_conv old.prod.case)
  subgoal by auto
  subgoal apply (clarsimp simp: iv_dj_ivl_\<alpha>_conv) by blast
  done


lemma ivl_invar_append[simp]: "ivl_invar (ivls\<^sub>1@ivls\<^sub>2) \<longleftrightarrow> ivl_invar ivls\<^sub>1 \<and> ivl_invar ivls\<^sub>2 \<and> ivl_\<alpha> ivls\<^sub>1 \<inter> ivl_\<alpha> ivls\<^sub>2 = {}" 
  unfolding ivl_invar_def
  apply (intro conjI iffI)
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by simp
  subgoal by auto
  subgoal apply (auto simp: in_ivl_\<alpha>_conv) by (metis disjoint_iff dual_order.strict_trans2)
  subgoal apply (simp add: ivl_\<alpha>_dj_conv) by fast
  subgoal by simp
  subgoal by (clarsimp simp: ivl_\<alpha>_dj_conv) blast
  done  








  
definition "ivl_empty = []"

definition "ivl_add l h ivls = (l,h)#ivls"

definition "ivl_is_empty ivls \<longleftrightarrow> ivls=[]"


lemma ivl_empty_invar[simp]: "ivl_invar ivl_empty" 
  and ivl_empty_\<alpha>[simp]: "ivl_\<alpha> ivl_empty = {}"
  unfolding ivl_\<alpha>_def ivl_invar_def ivl_empty_def
  by auto

lemma ivl_is_empty_\<alpha>[simp]: "ivl_invar ivls \<Longrightarrow> ivl_is_empty ivls \<longleftrightarrow> ivl_\<alpha> ivls={}"  
  unfolding ivl_\<alpha>_def ivl_invar_def ivl_is_empty_def
  apply auto
  by (metis atLeastLessThan_empty_iff ex_in_conv set_empty surj_pair)
  
    
lemma 
  assumes INV: "ivl_invar ivls" and PRE: "l<h" "{l..<h} \<inter> ivl_\<alpha> ivls = {}"
  shows ivl_add_invar[simp]: "ivl_invar (ivl_add l h ivls)"
    and ivl_add_\<alpha>[simp]: "ivl_\<alpha> (ivl_add l h ivls) = {l..<h} \<union> ivl_\<alpha> ivls"
  using assms
  unfolding ivl_add_def  
  by auto
      
(* Filtering intervals *)



  
(* Only elements < m *)
definition "ivl_filter_less m ivl \<equiv> 
  nfoldli ivl (\<lambda>_. True) (\<lambda>(l,h) res. 
    if h\<le>m then RETURN (ivl_add l h res)  \<comment> \<open>l..<h  m\<close>
    else if m\<le>l then RETURN res           \<comment> \<open>m  l..<h\<close>
    else RETURN (ivl_add l m res)         \<comment> \<open>l .. m ..<h\<close>
  ) ivl_empty"

lemma ivl_filter_less_correct:
  assumes "ivl_invar ivl"  
  shows "ivl_filter_less m ivl \<le> SPEC (\<lambda>ivl'. ivl_invar ivl' \<and> ivl_\<alpha> ivl' = { x\<in>ivl_\<alpha> ivl. x<m })"
proof -  
  interpret I0: ivl_invar ivl by fact

  show ?thesis
    unfolding ivl_filter_less_def
    apply (refine_vcg nfoldli_rule[where I="\<lambda>l\<^sub>1 l\<^sub>2 ivl'. 
        ivl_invar ivl' \<and> ivl_\<alpha> ivl' = { x\<in>ivl_\<alpha> l\<^sub>1. x<m }
      "])
    using assms  
    apply (clarsimp_all)
    subgoal by (auto intro: ivl_add_invar)
    subgoal by (subst ivl_add_\<alpha>; force)
    subgoal by auto
    subgoal by (rule ivl_add_invar; force)
    subgoal by (subst ivl_add_\<alpha>; force)
    done
qed  
  
(* Only elements \<ge> m *)
definition "ivl_filter_gte m ivl \<equiv> 
  nfoldli ivl (\<lambda>_. True) (\<lambda>(l,h) res. 
    if h\<le>m then RETURN res                    \<comment> \<open>l..<h  m\<close>
    else if m\<le>l then RETURN (ivl_add l h res) \<comment> \<open>m  l..<h\<close>
    else RETURN (ivl_add m h res)              \<comment> \<open>l .. m ..<h\<close>
  ) ivl_empty"

lemma ivl_filter_gte_correct:
  assumes "ivl_invar ivl"  
  shows "ivl_filter_gte m ivl \<le> SPEC (\<lambda>ivl'. ivl_invar ivl' \<and> ivl_\<alpha> ivl' = { x\<in>ivl_\<alpha> ivl. m\<le>x })"
proof -  
  interpret I0: ivl_invar ivl by fact

  show ?thesis
    unfolding ivl_filter_gte_def
    apply (refine_vcg nfoldli_rule[where I="\<lambda>l\<^sub>1 l\<^sub>2 ivl'. 
        ivl_invar ivl' \<and> ivl_\<alpha> ivl' = { x\<in>ivl_\<alpha> l\<^sub>1. m\<le>x }
      "])
    using assms  
    apply (clarsimp_all)
    subgoal by auto
    subgoal by (auto intro: ivl_add_invar)
    subgoal by (subst ivl_add_\<alpha>; force)
    subgoal by (rule ivl_add_invar; force)
    subgoal by (subst ivl_add_\<alpha>; force)
    done
    
qed  


(* Taking the smallest of two intervals, chopping the other *)

definition "ivls_split iv\<^sub>1 iv\<^sub>2 = do {
  ASSERT (iv\<^sub>1 \<noteq> []);
  ASSERT (iv\<^sub>2 \<noteq> []);

  ((l\<^sub>1,h\<^sub>1),iv\<^sub>1) \<leftarrow> mop_list_pop_last iv\<^sub>1;
  ((l\<^sub>2,h\<^sub>2),iv\<^sub>2) \<leftarrow> mop_list_pop_last iv\<^sub>2;
  
  ASSERT(l\<^sub>1<h\<^sub>1);
  ASSERT(l\<^sub>2<h\<^sub>2);
  
  let d\<^sub>1 = h\<^sub>1-l\<^sub>1;
  let d\<^sub>2 = h\<^sub>2-l\<^sub>2;
  
  if (d\<^sub>1 < d\<^sub>2) then do {
    iv\<^sub>2 \<leftarrow> mop_list_append iv\<^sub>2 (l\<^sub>2+d\<^sub>1,h\<^sub>2);
    RETURN ((iv_make l\<^sub>1 h\<^sub>1, iv\<^sub>1),(iv_make l\<^sub>2 (l\<^sub>2+d\<^sub>1),iv\<^sub>2))
  } else if (d\<^sub>2 < d\<^sub>1) then do {
    iv\<^sub>1 \<leftarrow> mop_list_append iv\<^sub>1 (l\<^sub>1+d\<^sub>2,h\<^sub>1);
    RETURN ((iv_make l\<^sub>1 (l\<^sub>1+d\<^sub>2), iv\<^sub>1),(iv_make l\<^sub>2 h\<^sub>2,iv\<^sub>2))
  } else do {
    ASSERT (d\<^sub>1=d\<^sub>2);
    RETURN ((iv_make l\<^sub>1 h\<^sub>1, iv\<^sub>1),(iv_make l\<^sub>2 h\<^sub>2,iv\<^sub>2))
  }
}"


definition "iv_rel \<equiv> br iv_\<alpha> iv_invar"
definition "ivl_rel \<equiv> br ivl_\<alpha> ivl_invar"

lemma ivls_split_refine: "(ivls_split, split_sets_eq_SPEC) 
  \<in> ivl_rel \<rightarrow> ivl_rel \<rightarrow> \<langle> (iv_rel \<times>\<^sub>r ivl_rel) \<times>\<^sub>r (iv_rel \<times>\<^sub>r ivl_rel) \<rangle>nres_rel"
  unfolding ivls_split_def split_sets_eq_SPEC_def
  apply (refine_vcg SPEC_refine)
  apply (clarsimp_all simp: iv_rel_def ivl_rel_def in_br_conv)
  apply (clarsimp_all simp: neq_Nil_rev_conv)
  apply force
  apply force
  by blast
  
context weak_ordering begin

  sublocale gen_part: partitioning "\<lambda>x. x\<^bold>\<le>p" "\<lambda>x. x\<^bold>\<ge>p" for p
    apply unfold_locales using connex .

  


end
  
  
  
find_theorems "_ \<le> \<Down>_ (SPEC _)"  


xxx, ctd here:
  refine ppart and par_swap to use intervals!

oops  
  
context weak_ordering begin
  term partition_spec 
  term partition_SPEC
  
  \<rightarrow> skip partitioning context for weak_ordering, as we are interested in 
    Hoare-style partitions, that do not get disbalanced that easily!
  
  

context partitioning begin

term ppart_SPEC

term partition3_spec

find_theorems name: partition


oops
  

oops
xxx, ctd here




  definition "partition_slices d xs = RECT (\<lambda>partition_slices (d,xs). do {
    ASSERT (d>0);
    let len = length xs;
    if (len \<le> d) then do {
      (xs,ss,bs) \<leftarrow> ppart_SPEC xs;
      RETURN (xs,ss,bs)
    } else do {
      let si = len - d;
      (((ss\<^sub>1,bs\<^sub>1),(ss\<^sub>2,bs\<^sub>2)),xs) \<leftarrow> WITH_SPLIT si xs (\<lambda>xs\<^sub>1 xs\<^sub>2. do {
        ((xs\<^sub>1,ivs\<^sub>1),(xs\<^sub>2,ivs\<^sub>2)) \<leftarrow> nres_par (partition_slices) (ppart_SPEC) (d,xs\<^sub>1) xs\<^sub>2;
        RETURN (((ivs\<^sub>1,ivs\<^sub>2),xs\<^sub>1,xs\<^sub>2))
      });
      
      let ss\<^sub>2 = (+)si`ss\<^sub>2;
      let bs\<^sub>2 = (+)si`bs\<^sub>2;
      
      RETURN (xs,ss\<^sub>1\<union>ss\<^sub>2, bs\<^sub>1 \<union> bs\<^sub>2)
    }
  }) (d,xs)"


  
  
  
  
oops    
xxx: now the whole sequence ... first using swap_SPEC!
  
  
oops  
  xxx, ctd here:
    just finished par_swap_correct.
    Now do par_partition (the whole sequence)
    
    clean up a bit
    refine to intervals
  
  
oops    
    
  
  
  xxx, ctd here: this splitting logic can be done on set-based model, too! Then refine to intervals!
  
  
  
  term WITH_SPLIT  
  
    
  oops

  xxx, ctd here
  
    we just made the thing independent from sorting-setup, 
      by just specifying a partitioning locale, that may have overlapping predicates.
  
    now specify how to enhance a slice (or interval) partitioner 
    into partitioning parallel stripes of the array, and yield interval representations of ss and bs.
  
  
  
  
  xxx, ctd here:
    we'll need partition-spec from sorting-setup!
        
  then think about implementation with intervals, and slice-partitioning function.
  use with-split to have slice-partitioner locally!?
    
      
  
  oops
  xxx, ctd here:
    specify in nres-monad, and prove correct!
      
    
    
    
    
    
    oops      
    xxx, ctd here: how to describe the swap.
      as set of pairs?!
      permutation of indices?
    
  
  





end
