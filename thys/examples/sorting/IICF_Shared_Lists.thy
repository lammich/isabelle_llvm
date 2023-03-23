theory IICF_Shared_Lists
imports "Isabelle_LLVM.IICF"
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
  

lemma nth_map2: "\<lbrakk> i<length xs; i<length ys \<rbrakk> \<Longrightarrow> map2 f xs ys ! i = f (xs!i) (ys!i)" by simp

lemma map2_update1: "map2 f (xs[i:=x]) ys = (map2 f xs ys)[i := f x (ys!i)]"
  by (metis list_update_id map_update old.prod.case zip_update)

lemma map2_update2: "map2 f xs (ys[i:=y]) = (map2 f xs ys)[i := f (xs!i) y]"
  by (metis list_update_id map_update old.prod.case zip_update)
    
lemma list_all2_map_map_conv: "list_all2 P (map f xs) (map g ys) = list_all2 (\<lambda>x y. P (f x) (g y)) xs ys"
  by (auto simp: list.rel_map)
  


section \<open>Lists with Element-wise Ownership\<close>


  
subsection \<open>Abstract Operations\<close>
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


subsection \<open>Lemmas for Abstract Operations\<close>

lemma sl_indexes_alt: "sl_indexes' xs = {i . i<length xs \<and> xs!i \<noteq> None}"
  unfolding sl_indexes_def sl_struct_def
  by auto

lemma sl_of_list_empty[simp]: "sl_of_list [] = []"
  by (auto simp: sl_of_list_def)

lemma sl_of_list_eq_empty_conv[simp]: "sl_of_list xs = [] \<longleftrightarrow> xs=[]"
  by (auto simp: sl_of_list_def)

lemma sl_split_empty[simp]: "sl_split s [] = []" by (auto simp: sl_split_def) 
  
lemma sl_split_eq_empty_conv[simp]: "sl_split s xs = [] \<longleftrightarrow> xs=[]"  by (auto simp: sl_split_def)

lemma sl_struct_empty[simp]: "sl_struct [] = []" by (auto simp: sl_struct_def)
lemma sl_struct_eq_empty_conv[simp]: "sl_struct xs = [] \<longleftrightarrow> xs=[]" by (auto simp: sl_struct_def)

lemma sl_compat_empty[simp]: "sl_compat [] []" unfolding sl_compat_def by auto
lemma sl_compat_empty_conv[simp]: 
  "sl_compat [] xs\<^sub>2 \<longleftrightarrow> xs\<^sub>2 = []" 
  "sl_compat xs\<^sub>1 [] \<longleftrightarrow> xs\<^sub>1 = []" 
  unfolding sl_compat_def by auto


lemma sl_join_empty[simp]: 
  "sl_join [] xs = []"
  "sl_join xs [] = []"
  unfolding sl_join_def by auto

lemma sl_join_eq_empty_conv[simp]: "sl_compat (sl_struct xs\<^sub>1) (sl_struct xs\<^sub>2) \<Longrightarrow> sl_join xs\<^sub>1 xs\<^sub>2 = [] \<longleftrightarrow> xs\<^sub>1=[] \<and> xs\<^sub>2=[]"  
  unfolding sl_join_def
  by auto
  
lemma sl_indexes_empty[simp]: "sl_indexes [] = {}"
  unfolding sl_indexes_def by auto
  
  
  
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

lemma list_eq_iff_sl_eq: "xs=xs' 
  \<longleftrightarrow> (length xs = length xs' \<and> sl_indexes' xs = sl_indexes' xs' \<and> (\<forall>i\<in>sl_indexes' xs'. sl_get xs i = sl_get xs' i))"
  apply (rule iffI)
  apply (auto; fail)
  apply (clarsimp simp: sl_indexes_alt sl_get_def list_eq_iff_nth_eq)
  by (smt (verit) mem_Collect_eq option.exhaust_sel option.sel)
  
  
lemma sl_join_split_eq: "sl_join (sl_split ls xs) (sl_split (-ls) xs) = xs"  
  apply (auto simp: list_eq_iff_sl_eq sl_compat_splitI sl_indexes_split )
  apply (subst sl_get_join)
  apply (simp add: sl_compat_splitI; fail)
  apply (auto dest: sl_indexes_lengthD; fail) []
  apply (auto simp: sl_get_split sl_indexes_split)
  done
  
lemma sl_put_empty_iff[simp]: "sl_put xs i x = [] \<longleftrightarrow> xs=[]"  
  unfolding sl_put_def by auto


lemma sl_get_put[simp]: "i\<in>sl_indexes' xs \<Longrightarrow> sl_get (sl_put xs i x) i = x"  
  unfolding sl_get_def sl_put_def
  by (auto dest: sl_indexes_lengthD)

lemma sl_get_put_indep[simp]: "i\<noteq>j \<Longrightarrow> sl_get (sl_put xs i x) j = sl_get xs j"  
  unfolding sl_get_def sl_put_def
  by (auto)

lemma sl_put_get[simp]: "i\<in>sl_indexes' xs \<Longrightarrow> sl_put xs i (sl_get xs i) = xs"  
  unfolding sl_get_def sl_put_def sl_indexes_alt
  by auto
    
definition "sl_split1' b x \<equiv> if b then x else None"  
lemma sl_split1'_simp[simp]:
  "sl_split1' True x = x"
  "sl_split1' False x = None"
  "sl_split1' b None = None"
  unfolding sl_split1'_def by auto

      
lemma sl_split_snoc: "sl_split ls (xs@[x]) = sl_split ls xs @ [ sl_split1' (length xs \<in> ls) x]"  
  unfolding sl_split_def
  by auto
  
lemma sl_struct_Cons[simp]: "sl_struct (x#xs) = (x=None)#sl_struct xs"
  by (auto simp: sl_struct_def)


lemma sl_compat_Cons[simp]: "sl_compat (x#xs) (y#ys) \<longleftrightarrow> (x\<or>y) \<and> sl_compat xs ys"  
  unfolding sl_compat_def
  by simp
      
lemma sl_join_Cons[simp]: "sl_join (x#xs) (y#ys) = join_option x y # sl_join xs ys"  
  unfolding sl_join_def by simp
  
lemma sl_indexes_finite[simp, intro!]: "finite (sl_indexes s)" by (auto simp: sl_indexes_def)

lemma sl_struct_join_split: "sl_struct_join (sl_struct_split I s) (sl_struct_split (-I) s) = s"
  unfolding sl_struct_join_def sl_struct_split_def
  by (auto simp: map2_map_conv map_nth) 

(*
lemma sl_join_split_eq: "sl_join (sl_split s xs) (sl_split (-s) xs) = xs"  
  unfolding sl_join_def sl_split_def 
  apply (rewrite at "_ = \<hole>" map_nth[symmetric])
  by (auto simp: map2_map_conv)
*)  
  
lemma mset_of_list_permut: "mset xs = mset (sl_of_list xs\<^sub>0) \<Longrightarrow> mset (list_of_sl xs) = mset xs\<^sub>0" 
  unfolding sl_of_list_def list_of_sl_def
  by (simp add: mset_map_id)

lemma length_sl_put[simp]: "length (sl_put xs i x) = length xs" unfolding sl_put_def by auto


lemma sl_swap_aux: "\<lbrakk>i \<in> sl_indexes' xs; j \<in> sl_indexes' xs\<rbrakk> 
  \<Longrightarrow> sl_put (sl_put xs i (sl_get xs j)) j (sl_get xs i) = swap xs i j"
  by (auto simp add: list_eq_iff_nth_eq sl_put_def sl_get_def sl_indexes_alt swap_def)
  
  
  
(* TODO: Move *)  
lemma sl_struct_swap[simp]: "\<lbrakk> i\<in>sl_indexes' xs; j\<in>sl_indexes' xs \<rbrakk> \<Longrightarrow> sl_struct (swap xs i j) = sl_struct xs"
  by (simp flip: sl_swap_aux)
  
  
lemma sl_get_swap_iff: "\<lbrakk> i\<in>sl_indexes' xs; j\<in>sl_indexes' xs \<rbrakk> \<Longrightarrow> sl_get (swap xs i j) k = (if k=i then sl_get xs j else if k=j then sl_get xs i else sl_get xs k)"  
  by (auto simp add: sl_get_def swap_nth dest!: sl_indexes_lengthD)
  
lemma sl_get_swap_other: "\<lbrakk>k\<noteq>i; k\<noteq>j\<rbrakk> \<Longrightarrow> sl_get (swap xs i j) k = sl_get xs k"  
  by (simp add: sl_get_def swap_def)

  


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

  
(* TODO: Move *)
lemma fold_is_None': "(=)None = is_None" by auto

lemma sl_struct_param[param]: "(sl_struct,sl_struct) \<in> \<langle>\<langle>A\<rangle>option_rel\<rangle>list_rel \<rightarrow> \<langle>bool_rel\<rangle>list_rel"  
  unfolding sl_struct_def fold_is_None'
  by parametricity
  
lemma sl_indexes_param[param]: "(sl_indexes, sl_indexes) \<in> \<langle>bool_rel\<rangle>list_rel \<rightarrow> \<langle>nat_rel\<rangle>set_rel" by simp

lemma sl_split_param[param]: "(sl_split,sl_split) \<in> \<langle>nat_rel\<rangle>set_rel \<rightarrow> \<langle>\<langle>A\<rangle>option_rel\<rangle>list_rel \<rightarrow> \<langle>\<langle>A\<rangle>option_rel\<rangle>list_rel"
  unfolding sl_split_def
  apply parametricity
  by auto

lemma join_option_param[param]: "(join_option, join_option) \<in> \<langle>A\<rangle>option_rel \<rightarrow> \<langle>A\<rangle>option_rel \<rightarrow> \<langle>A\<rangle>option_rel"
  by (auto simp: option_rel_def)

lemma sl_join_param[param]: "(sl_join, sl_join) \<in> \<langle>\<langle>A\<rangle>option_rel\<rangle>list_rel \<rightarrow> \<langle>\<langle>A\<rangle>option_rel\<rangle>list_rel \<rightarrow> \<langle>\<langle>A\<rangle>option_rel\<rangle>list_rel"  
  unfolding sl_join_def
  by parametricity
  
lemma sl_complete_sl_of_list_of_sl[simp]: "sl_complete (sl_struct xs) \<Longrightarrow> sl_of_list (list_of_sl xs) = xs"
  unfolding sl_of_list_def list_of_sl_def sl_complete_def
  apply (induction xs)
  by auto
  
  
  
subsection \<open>Sepref ADT Setup\<close>  
sepref_decl_op slist_swap: "swap:: _ option list \<Rightarrow> _ "
  :: "[\<lambda>((l,i),j). i\<in>sl_indexes' l \<and> j\<in>sl_indexes' l]\<^sub>f (\<langle>\<langle>A\<rangle>option_rel\<rangle>list_rel \<times>\<^sub>r nat_rel) \<times>\<^sub>r nat_rel \<rightarrow> \<langle>\<langle>A\<rangle>option_rel\<rangle>list_rel" 
  apply rule
  apply (clarsimp dest!: sl_indexes_lengthD)
  apply parametricity
  by auto

sepref_decl_op sl_of_list :: "\<langle>Id::'a rel\<rangle>list_rel \<rightarrow> \<langle>\<langle>Id::'a rel\<rangle>option_rel\<rangle>list_rel" . 
  
sepref_decl_op list_of_sl :: "[\<lambda>xs. sl_complete (sl_struct xs) ]\<^sub>f \<langle>\<langle>Id::'a rel\<rangle>option_rel\<rangle>list_rel \<rightarrow> \<langle>Id::'a rel\<rangle>list_rel" by auto 
  
  
    
subsection \<open>With-Idxs Combinator\<close>  
  
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

end
