theory Sorting_Par_Partition
imports Sorting_Setup
begin

section \<open>Abstract Algorithm\<close>

subsection \<open>Lists with Element-wise Ownership\<close>

(* Split *)
definition "split_idxs_left ls xs = map (\<lambda>i. if i\<in>ls \<and> i<length xs then xs!i else None) [0..<length xs]"

definition "split_idxs_right ls xs = map (\<lambda>i. if i\<in>ls \<or> i\<ge>length xs then None else xs!i) [0..<length xs]"

(* Join *)
fun join_option where
  "join_option None y = y"
| "join_option x None = x"  
| "join_option _ _ = None"  (* Corner case mapped symmetrically to None *)

lemma join_option_add_simp[simp]: "join_option x None = x" by (cases x) auto

definition "join_idxs = map2 join_option"

(* Conversion from/to plain list *)
definition "sl_of_list = map Some"
definition "list_of_sl = map the"

(* Structure *)
definition "sl_struct xs = map ((=)None) xs"
definition "sl_compat s\<^sub>1 s\<^sub>2 = list_all2 (\<or>) s\<^sub>1 s\<^sub>2"
definition "sl_complete s \<longleftrightarrow> set s \<subseteq> {True}"
definition "sl_indexes xs = {i . i<length xs \<and> xs!i\<noteq>None}"

(* Operations *)
definition "sl_get xs i = the (xs!i)"
definition "sl_set xs i x = xs[i:=Some x]"


lemma sl_indexes_alt: "sl_indexes xs = {i . i<length (sl_struct xs) \<and> \<not>(sl_struct xs)!i}"
  unfolding sl_indexes_def sl_struct_def
  by auto


lemma "sl_indexes (sl_of_list xs) = {0..<length xs}"
  unfolding sl_indexes_def sl_of_list_def by auto

lemma "i\<in>sl_indexes xs \<Longrightarrow> sl_struct (sl_set xs i x) = sl_struct xs"
  unfolding sl_indexes_alt sl_struct_def sl_set_def 
  by (auto simp: map_update list_update_same_conv)

  
  

          


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

(* TODO: Move *)  
lemma list_all2_append2: "length xs' = length ys' \<Longrightarrow> list_all2 P (xs@xs') (ys@ys') \<longleftrightarrow> list_all2 P xs ys \<and> list_all2 P xs' ys'"  
  by (auto simp: list_all2_append list_all2_iff)
    
lemma slcompat_Snoc[simp]: "slcompat (xs@[x]) (ys@[y]) \<longleftrightarrow> slcompat xs ys \<and> (x\<or>y)"  
  unfolding slcompat_def 
  by (auto simp: list_all2_append2)
  
    
(* TODO: Move *)  
lemma rev_induct2 [consumes 1, case_names Nil snoc]:
  "length xs = length ys \<Longrightarrow> P [] [] \<Longrightarrow>
   (\<And>x xs y ys. length xs = length ys \<Longrightarrow> P xs ys \<Longrightarrow> P (xs@[x]) (ys@[y]))
   \<Longrightarrow> P xs ys"
proof (induct xs arbitrary: ys rule: rev_induct)
  case (snoc x xs ys) then show ?case by (cases ys rule: rev_cases) simp_all
qed simp

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
  
  
lemma map_by_map_idx: "map f xs = map (f o nth xs) [0..<length xs]"  
  apply (induction xs rule: rev_induct)
  by auto
  
lemma map2_map_conv: "map2 f (map g xs) (map h ys) = map2 (\<lambda>x y. f (g x) (h y)) xs ys"
  apply(induction xs ys rule: list_induct2')
  by auto
  
lemma map2_same[simp]: "map2 f xs xs = map (\<lambda>x. f x x) xs"
  apply (induction xs) by auto
  
  
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
    ss\<^sub>2 and bs\<^sub>2 are a swap-spec (sanity check)
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


  
  




context partitioning begin
  definition "ppart1 xs \<equiv> do {
    (xs,ss,bs) \<leftarrow> ppart_SPEC xs;
    let m = ppart_mpos ss;

    let (ss\<^sub>2,bs\<^sub>2) = ppart_filter m ss bs;
    
    xs \<leftarrow> SPEC (swap_spec ss\<^sub>2 bs\<^sub>2 xs);
  
    RETURN (m,xs)
  }"

  lemma ppart1_valid_partitition: "ppart1 xs \<le> SPEC (\<lambda>(m,xs'). partition_spec xs m xs')"
    unfolding ppart1_def ppart_spec_def
    apply refine_vcg
    apply clarsimp_all
  proof -
    fix xs\<^sub>1 ss bs ss\<^sub>2X bs\<^sub>2X xs'
    assume 
      pp_flt: "ppart_filter (ppart_mpos ss) ss bs = (ss\<^sub>2X, bs\<^sub>2X)" and
      sspec: "swap_spec ss\<^sub>2X bs\<^sub>2X xs\<^sub>1 xs'" and
      [simp]: "mset xs\<^sub>1 = mset xs" and
      "is_ppart P\<^sub>1 P\<^sub>2 xs\<^sub>1 ss bs"
  
      
    interpret is_ppart P\<^sub>1 P\<^sub>2 xs\<^sub>1 ss bs by fact  
    interpret ppar_step2 P\<^sub>1 P\<^sub>2 xs\<^sub>1 ss bs by unfold_locales
    
    have [simp]: "ss\<^sub>2X = ss\<^sub>2" "bs\<^sub>2X = bs\<^sub>2" unfolding ss\<^sub>2_def bs\<^sub>2_def using pp_flt
      by auto
    
    interpret swap_spec ss\<^sub>2 bs\<^sub>2 xs\<^sub>1 xs' 
      using sspec by simp
      
    interpret ppar_step3 P\<^sub>1 P\<^sub>2 xs\<^sub>1 ss bs xs'
      by unfold_locales 
      
    show "partition_spec xs m xs'"  
      using \<open>mset xs\<^sub>1 = mset xs\<close> is_valid_partition partition_spec_permute by blast
  qed    

  
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
        
  
  definition "partition_slices xs d = RECT (\<lambda>partition_slices (xs,d). do {
    ASSERT (d>0);
    let len = length xs;
    if (len \<le> d) then do {
      (xs,ss,bs) \<leftarrow> ppart_SPEC xs;
      RETURN (xs,ss,bs)
    } else do {
      let si = len - d;
      (((ss\<^sub>1,bs\<^sub>1),(ss\<^sub>2,bs\<^sub>2)),xs) \<leftarrow> WITH_SPLIT si xs (\<lambda>xs\<^sub>1 xs\<^sub>2. do {
        ((xs\<^sub>1,ivs\<^sub>1),(xs\<^sub>2,ivs\<^sub>2)) \<leftarrow> nres_par (partition_slices) (ppart_SPEC) (xs\<^sub>1,d) xs\<^sub>2;
        RETURN (((ivs\<^sub>1,ivs\<^sub>2),xs\<^sub>1,xs\<^sub>2))
      });
      
      let ss\<^sub>2 = (+)si`ss\<^sub>2;
      let bs\<^sub>2 = (+)si`bs\<^sub>2;
      
      RETURN (xs,ss\<^sub>1\<union>ss\<^sub>2, bs\<^sub>1 \<union> bs\<^sub>2)
    }
  }) (xs,d)"
  
  lemma ppart_spec_imp_len_eq: "ppart_spec xs xs' ss bs \<Longrightarrow> length xs' = length xs"
    unfolding ppart_spec_def
    by (auto dest: mset_eq_length)
  
  
  lemma partition_slices_correct: "d>0 \<Longrightarrow> partition_slices xs d \<le> ppart_SPEC xs"
    unfolding partition_slices_def
    
    thm RECT_rule
    
    apply (refine_vcg RECT_rule[where V="measure (\<lambda>(xs,d). length xs)" and pre="\<lambda>(xs,d). d>0" and M="\<lambda>(xs,d). Refine_Basic.SPEC (\<lambda>(xs', ss, bs). ppart_spec xs xs' ss bs)", THEN order_trans])
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
end
    

(* Parallel swap with (arbitrary) intervals, abstract level *)  

(* Lists where only some of the indexes are accessible *)

  
    
thm list_induct2    
    
definition "WITH_IDXS ls xs m \<equiv> do {
  ASSERT (ls\<subseteq>sl_indexes xs);

  let xs\<^sub>1 = split_idxs_left ls xs;
  let xs\<^sub>2 = split_idxs_right ls xs;
  
  (r,xs\<^sub>1',xs\<^sub>2') \<leftarrow> m xs\<^sub>1 xs\<^sub>2;
  
  ASSERT (slstruct xs\<^sub>1' = slstruct xs\<^sub>1);
  ASSERT (slstruct xs\<^sub>2' = slstruct xs\<^sub>2);

  RETURN (r,join_idxs xs\<^sub>1' xs\<^sub>2')
}"

lemma WITH_IDXS_rule[refine_vcg]:
  assumes "ls \<subseteq> sl_indexes xs"
  assumes "\<And>xs\<^sub>1 xs\<^sub>2. \<lbrakk> 
    xs\<^sub>1 = split_idxs_left ls xs; 
    xs\<^sub>2 = split_idxs_right ls xs;
    slcompat (slstruct xs\<^sub>1) (slstruct xs\<^sub>2)
  \<rbrakk> \<Longrightarrow> m xs\<^sub>1 xs\<^sub>2 \<le> SPEC (\<lambda>(r,xs\<^sub>1',xs\<^sub>2'). 
            slstruct xs\<^sub>1' = slstruct xs\<^sub>1 
          \<and> slstruct xs\<^sub>2' = slstruct xs\<^sub>2   
          \<and> P (r, join_idxs xs\<^sub>1' xs\<^sub>2')
        )
        "
  shows "WITH_IDXS ls xs m \<le> SPEC P"
  unfolding WITH_IDXS_def
  apply refine_vcg
  apply fact
  apply (refine_vcg assms(2))
  apply auto
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
  
lemma WITH_IDXS_refine[refine]:
  assumes "(ls',ls)\<in>Id"
  assumes "(xs',xs) \<in> \<langle>\<langle>A\<rangle>option_rel\<rangle>list_rel"
  assumes [refine]: "\<lbrakk>ls \<subseteq> sl_indexes xs; ls' \<subseteq> sl_indexes xs'\<rbrakk> 
    \<Longrightarrow> m' (split_idxs_left ls' xs') (split_idxs_right ls' xs') \<le> \<Down>(R\<times>\<^sub>r\<langle>\<langle>A\<rangle>option_rel\<rangle>list_rel\<times>\<^sub>r\<langle>\<langle>A\<rangle>option_rel\<rangle>list_rel) (m (split_idxs_left ls xs) (split_idxs_right ls xs))"
  shows "WITH_IDXS ls' xs' m' \<le>\<Down>(R \<times>\<^sub>r \<langle>\<langle>A\<rangle>option_rel\<rangle>list_rel) (WITH_IDXS ls xs m)"
  unfolding WITH_IDXS_def
  apply refine_rcg
  using assms(1,2)
  apply -
  subgoal by (simp add: opt_list_rel_imp_same_sl_indexes)
  
  subgoal
    apply (clarsimp simp: opt_list_rel_imp_same_sl_struct)
    apply (rule sym)
    apply (rule opt_list_rel_imp_same_sl_struct)
    apply parametricity apply simp 
    done
  
  subgoal
    apply (clarsimp simp: opt_list_rel_imp_same_sl_struct)
    apply (rule sym)
    apply (rule opt_list_rel_imp_same_sl_struct)
    apply parametricity apply simp 
    done
    
  subgoal
    apply simp  
    apply parametricity
    apply auto
    done
  done      
  

term swap_spec  
  
lemma swap_spec_join:
  assumes "swap_spec ss\<^sub>1 bs\<^sub>1 xs\<^sub>1 xs\<^sub>1'"
  assumes "swap_spec ss\<^sub>2 bs\<^sub>2 xs\<^sub>2 xs\<^sub>2'"
  assumes SS1: "ss\<^sub>1 \<union> bs\<^sub>1 \<subseteq> sl_indexes xs\<^sub>1"
  assumes SS2: "ss\<^sub>2 \<union> bs\<^sub>2 \<subseteq> sl_indexes xs\<^sub>2"
  assumes COMPAT: "slcompat (slstruct xs\<^sub>1) (slstruct xs\<^sub>2)"
  shows "swap_spec (ss\<^sub>1\<union>ss\<^sub>2) (bs\<^sub>1\<union>bs\<^sub>2) (join_idxs xs\<^sub>1 xs\<^sub>2) (join_idxs xs\<^sub>1' xs\<^sub>2')"
proof -
  interpret s1: swap_spec ss\<^sub>1 bs\<^sub>1 xs\<^sub>1 xs\<^sub>1' + s2: swap_spec ss\<^sub>2 bs\<^sub>2 xs\<^sub>2 xs\<^sub>2' by fact+

  from COMPAT have [simp]: "length xs\<^sub>1 = length xs\<^sub>2" and IDX_DJ: "sl_indexes xs\<^sub>1 \<inter> sl_indexes xs\<^sub>2 = {}"
    unfolding slcompat_alt by auto
  
  have [simp]: "sl_indexes xs\<^sub>1' = sl_indexes xs\<^sub>1"  
    apply (auto simp: in_sl_indexes_iff)
    apply (metis SS1 \<open>length xs\<^sub>1 = length xs\<^sub>2\<close> in_mono in_sl_indexes_iff not_Some_eq s1.elems_outside)
    by (metis SS1 Un_iff \<open>length xs\<^sub>1 = length xs\<^sub>2\<close> in_sl_indexes_iff not_None_eq s1.elems_dst s1.elems_outside s1.elems_src subset_eq)

  have [simp]: "sl_indexes xs\<^sub>2' = sl_indexes xs\<^sub>2"  
    apply (auto simp: in_sl_indexes_iff)
    subgoal by (metis SS2 in_sl_indexes_iff not_Some_eq s2.elems_outside subsetD)
    subgoal by (metis SS2 Un_iff in_sl_indexes_iff option.exhaust s2.elems_dst s2.elems_outside s2.elems_src subset_eq)
    done
        
  have COMPAT': "slcompat (slstruct xs\<^sub>1') (slstruct xs\<^sub>2')"  
    unfolding slcompat_alt using IDX_DJ
    by simp
    
    
    
  show ?thesis
    apply unfold_locales
    subgoal
      using IDX_DJ SS1 SS2 s1.src_dst_dj s2.src_dst_dj by blast
    subgoal
      using sl_indexes_in_range SS1 SS2 by force
    subgoal
      using sl_indexes_in_range SS1 SS2 by force
    subgoal
      by (metis IDX_DJ SS1 SS2 card_Un_disjoint disjoint_mono le_supE s1.card_eq s1.finite_dst s1.finite_src s2.card_eq s2.finite_dst s2.finite_src)
    subgoal for i
      by (auto simp: join_idxs_nth s1.elems_outside s2.elems_outside)
      
    subgoal for i
      using set_mp[OF s1.src_ss, of i] set_mp[OF s2.src_ss, of i]
      apply (auto simp: join_idxs_nth)
      apply (frule s1.elems_src; clarsimp)
      subgoal for j
        apply (rule bexI[where x=j]; simp?)
        using set_mp[OF s1.dst_ss, of j] SS1
        apply (auto simp: join_idxs_nth)
        by (metis IDX_DJ \<open>sl_indexes xs\<^sub>2' = sl_indexes xs\<^sub>2\<close> disjoint_iff in_mono in_sl_indexes_iff s2.length_xs'_eq)
        
      apply (frule s2.elems_src; clarsimp)
      subgoal for j
        apply (rule bexI[where x=j]; simp?)
        using set_mp[OF s2.dst_ss, of j] SS2
        apply (auto simp: join_idxs_nth)
        by (metis (mono_tags, lifting) IDX_DJ \<open>length xs\<^sub>1 = length xs\<^sub>2\<close> \<open>sl_indexes xs\<^sub>1' = sl_indexes xs\<^sub>1\<close> disjoint_iff in_mono in_sl_indexes_iff s1.length_xs'_eq)

      done
      
    subgoal for i
      using set_mp[OF s1.dst_ss, of i] set_mp[OF s2.dst_ss, of i]
      apply (auto simp: join_idxs_nth)
      apply (frule s1.elems_dst; clarsimp)
      subgoal for j
        apply (rule bexI[where x=j]; simp?)
        using set_mp[OF s1.src_ss, of j] SS1
        apply (auto simp: join_idxs_nth)
        by (metis IDX_DJ \<open>sl_indexes xs\<^sub>2' = sl_indexes xs\<^sub>2\<close> disjoint_iff in_mono in_sl_indexes_iff s2.length_xs'_eq)
        
      apply (frule s2.elems_dst; clarsimp)
      subgoal for j
        apply (rule bexI[where x=j]; simp?)
        using set_mp[OF s2.src_ss, of j] SS2
        apply (auto simp: join_idxs_nth)
        by (metis (mono_tags, lifting) IDX_DJ \<open>length xs\<^sub>1 = length xs\<^sub>2\<close> \<open>sl_indexes xs\<^sub>1' = sl_indexes xs\<^sub>1\<close> disjoint_iff in_mono in_sl_indexes_iff s1.length_xs'_eq)
      done
      
    subgoal
      using s1.permut s2.permut  
      by (simp add: mset_join_idxs_eq COMPAT COMPAT')
    done      
    
qed      
        
        
  
definition "split_swap_spec ss bs \<equiv> do {
  ASSERT (ss\<noteq>{});
  ASSERT (ss\<inter>bs={} \<and> card ss = card bs);
  SPEC (\<lambda>((ss\<^sub>1,ss\<^sub>2),(bs\<^sub>1,bs\<^sub>2)). 
    ss = ss\<^sub>1 \<union> ss\<^sub>2 
  \<and> bs = bs\<^sub>1 \<union> bs\<^sub>2 
  \<and> ss\<^sub>1\<inter>ss\<^sub>2={}      
  \<and> bs\<^sub>1\<inter>bs\<^sub>2={}
  \<and> card ss\<^sub>1 = card bs\<^sub>1
  \<and> card ss\<^sub>2 = card bs\<^sub>2
  \<and> ss\<^sub>1\<noteq>{}
)}"

  
term swap_spec
find_theorems swap_spec

term WITH_IDXS

definition "swap_opt_spec_pre ss bs xs \<equiv> swap_spec_pre ss bs xs \<and> ss\<union>bs \<subseteq> sl_indexes xs"
definition "swap_opt_spec_post ss bs xs xs' \<equiv> swap_spec ss bs xs xs' \<and> slstruct xs' = slstruct xs"

lemma swap_opt_spec_pre_empty_ss_iff: "swap_opt_spec_pre {} bs xs \<longleftrightarrow> bs={}"
  unfolding swap_opt_spec_pre_def
  unfolding swap_spec_pre_def
  by (auto simp: subset_eq_atLeast0_lessThan_finite)


definition "swap_opt_SPEC ss bs xs \<equiv> do {ASSERT (swap_opt_spec_pre ss bs xs); SPEC (swap_opt_spec_post ss bs xs)}"

definition "par_swap ss bs xs \<equiv> RECT (\<lambda>par_swap (ss,bs,xs). do {
  ASSERT (swap_opt_spec_pre ss bs xs);
    
  ((ss\<^sub>1,ss\<^sub>2),(bs\<^sub>1,bs\<^sub>2)) \<leftarrow> split_swap_spec ss bs;
  
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
  

lemma split_swap_spec_rl:
  assumes "swap_opt_spec_pre ss bs xs"
  assumes "ss\<noteq>{}"
  shows "split_swap_spec ss bs \<le> SPEC (\<lambda>((ss\<^sub>1,ss\<^sub>2),(bs\<^sub>1,bs\<^sub>2)). 
    swap_opt_spec_pre ss\<^sub>1 bs\<^sub>1 (split_idxs_left (ss\<^sub>1\<union>bs\<^sub>1) xs)
  \<and> swap_opt_spec_pre ss\<^sub>2 bs\<^sub>2 (split_idxs_right (ss\<^sub>1\<union>bs\<^sub>1) xs)
  \<and> ss = ss\<^sub>1\<union>ss\<^sub>2 \<and> bs=bs\<^sub>1\<union>bs\<^sub>2 \<and> ss\<^sub>1\<noteq>{} \<and> ss\<^sub>1\<inter>ss\<^sub>2={}
  )"
proof -
  from assms(1)[unfolded swap_opt_spec_pre_def] interpret swap_spec_pre ss bs xs by simp
  from assms(1)[unfolded swap_opt_spec_pre_def] have IDX: "ss \<union> bs \<subseteq> sl_indexes xs" by simp
  
  {
    fix ss\<^sub>1 ss\<^sub>2 bs\<^sub>1 bs\<^sub>2
    assume EQ: "ss = ss\<^sub>1 \<union> ss\<^sub>2" "bs = bs\<^sub>1 \<union> bs\<^sub>2" 
    assume DJ: "ss\<^sub>1 \<inter> ss\<^sub>2 = {}" "bs\<^sub>1 \<inter> bs\<^sub>2 = {}" 
    assume CARD: "card ss\<^sub>1 = card bs\<^sub>1" "card ss\<^sub>2 = card bs\<^sub>2" 
    assume "ss\<^sub>1 \<noteq> {}"
    
    have 1: "swap_opt_spec_pre ss\<^sub>1 bs\<^sub>1 (split_idxs_left (ss\<^sub>1 \<union> bs\<^sub>1) xs)"  
      unfolding swap_opt_spec_pre_def
      apply (intro conjI)
      apply unfold_locales
      subgoal using EQ src_dst_dj by blast
      subgoal using EQ(1) src_ss by auto
      subgoal using EQ(2) dst_ss by auto
      subgoal by (simp add: CARD)
      subgoal using EQ(1) EQ(2) IDX by auto
      done
      
    have 2: "swap_opt_spec_pre ss\<^sub>2 bs\<^sub>2 (split_idxs_right (ss\<^sub>1 \<union> bs\<^sub>1) xs)"  
      unfolding swap_opt_spec_pre_def
      apply (intro conjI)
      apply unfold_locales
      subgoal using EQ src_dst_dj by blast
      subgoal using EQ(1) src_ss by auto
      subgoal using EQ(2) dst_ss by auto
      subgoal by (simp add: CARD)
      subgoal apply auto using IDX EQ DJ src_dst_dj by auto
      done
      
    note 1 2      
  } note aux=this
  
  
  show ?thesis
    unfolding split_swap_spec_def
    using assms(2)
    apply refine_vcg
    by (clarsimp_all simp: src_dst_dj card_eq aux)
qed    
    
  
lemma swap_opt_spec_split_complete: "swap_opt_spec_pre ss bs (split_idxs_left (ss \<union> bs) xs) \<Longrightarrow> swap_opt_spec_pre ss bs xs"
  unfolding swap_opt_spec_pre_def swap_spec_pre_def 
  by auto
  
lemma par_swap_correct:
  shows "ss\<noteq>{} \<Longrightarrow> par_swap ss bs xs \<le> swap_opt_SPEC ss bs xs"
  unfolding par_swap_def swap_opt_SPEC_def
  supply R = RECT_rule[where V="measure (card o fst)" and pre="\<lambda>(ss,bs,xs). ss\<noteq>{} \<and> swap_opt_spec_pre ss bs xs"]
  apply refine_vcg
  apply (refine_vcg R[where M="\<lambda>(ss,bs,xs). SPEC (swap_opt_spec_post ss bs xs)", THEN order_trans])
  apply (all \<open>(thin_tac "RECT _ = _")?\<close>)
  subgoal by simp
  subgoal by simp
  subgoal by simp
  
  apply (clarsimp)
  apply (clarsimp)
  subgoal for par_swap ss bs xs proof goal_cases
    case 1
    
    note IH = \<open>\<lbrakk>_;_\<rbrakk> \<Longrightarrow> par_swap _ \<le>  _\<close>
    
    have FIN_SS: "finite ss"
      by (meson "1"(5) swap_opt_spec_pre_def swap_spec_pre.finite_src)
    
    show ?case 
      apply (refine_vcg split_swap_spec_rl)
      apply fact
      apply fact
      subgoal by (clarsimp simp: swap_opt_spec_pre_empty_ss_iff)
      subgoal by (clarsimp simp: swap_opt_spec_pre_empty_ss_iff)
      subgoal by (clarsimp simp: swap_opt_spec_pre_empty_ss_iff)
      subgoal by (clarsimp; simp add: swap_opt_spec_split_complete)
      subgoal by (clarsimp simp: )
      subgoal by (simp add: swap_opt_spec_pre_def)
      subgoal by auto
      apply clarsimp
      apply (refine_vcg IH)
      subgoal for ss\<^sub>2 bs\<^sub>1 bs\<^sub>2 ss\<^sub>1
        using FIN_SS 
        by (auto simp: card_Un_disjoint) 
      subgoal unfolding swap_opt_spec_post_def by simp
      subgoal unfolding swap_opt_spec_post_def by simp
      subgoal for ss\<^sub>2 bs\<^sub>1 bs\<^sub>2 ss\<^sub>1 xs\<^sub>1 xs\<^sub>2
        unfolding swap_opt_spec_post_def
        apply (clarsimp simp: slstruct_split_recombine)
        apply (rewrite join_split_idxs[symmetric, where s="ss\<^sub>1\<union>bs\<^sub>1"])
        apply (rule swap_spec_join)
        apply simp_all
        subgoal by (simp add: swap_opt_spec_pre_def)
        subgoal by (simp add: swap_opt_spec_pre_def)
        done
      done        
  qed
  subgoal by clarsimp 
  done
  

  
  
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
