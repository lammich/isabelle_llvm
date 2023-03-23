theory Sorting_Par_Partition
imports Sorting_Setup Sorting_Guarded_Partition IICF_DS_Interval_List IICF_Shared_Lists IICF_DS_Array_Idxs Sorting_Sample_Partition
begin

(* TODO: Move *)

definition nat_div_round_up :: "nat \<Rightarrow> nat \<Rightarrow> nat nres" where "nat_div_round_up p q \<equiv> doN {
  ASSERT (q\<noteq>0);
  let r = p div q;
  if p mod q = 0 then 
    RETURN r 
  else doN {
    ASSERT (r+1\<le>p);
    RETURN (r+1)
  }
}"  

lemma nat_div_round_up_correct[refine_vcg]: "q\<noteq>0 \<Longrightarrow> nat_div_round_up p q \<le>  SPEC (\<lambda>r. r*q \<in> {p..<p+q})"
  unfolding nat_div_round_up_def
  apply refine_vcg
  apply (auto simp: algebra_simps modulo_nat_def)
  subgoal 
    by (metis less_add_same_cancel1 nle_le times_div_less_eq_dividend)
  subgoal
    by (metis div_le_dividend gr0_implies_Suc leI le_antisym less_Suc_eq_le mult_Suc not_add_less1)
  subgoal
    using dividend_less_times_div less_imp_le_nat by presburger
  done
  

sepref_register nat_div_round_up

sepref_def nat_div_round_up_impl is "uncurry nat_div_round_up" :: "(snat_assn' TYPE('l::len2))\<^sup>k *\<^sub>a (snat_assn' TYPE('l))\<^sup>k \<rightarrow>\<^sub>a snat_assn' TYPE('l)"
  unfolding nat_div_round_up_def
  apply (annot_snat_const "TYPE('l)")
  by sepref



(* TODO: Move *)

(* Copy-nth implementation for woarray_slice_assn *)

term woarray_slice_assn

find_theorems woarray_slice_assn

thm eoarray_slice_assn_def

term sao_assn

definition [llvm_inline]: "array_cp_nth (cp :: 'a::llvm_rep \<Rightarrow> 'a llM) p i \<equiv> doM {
  r\<leftarrow>array_nth p i;
  r\<leftarrow>cp r;
  Mreturn r
}"

lemma sao_assn_cp_rl[vcg_rules]:
  fixes A :: "('a,'c::llvm_rep) dr_assn"
  fixes cp
  assumes copy_elem_rl[vcg_rules]: "\<And>a c. llvm_htriple (\<upharpoonleft>A a c) (cp c) (\<lambda>r. \<upharpoonleft>A a c ** \<upharpoonleft>A a r)"
  shows "llvm_htriple 
    (\<upharpoonleft>(sao_assn A) xs p \<and>* \<upharpoonleft>snat.assn i ii \<and>* \<up>\<^sub>d(i < length xs \<and> xs!i\<noteq>None)) 
    (array_cp_nth cp p ii)
    (\<lambda>ri. \<upharpoonleft>A (the (xs!i)) ri \<and>* \<upharpoonleft>(sao_assn A) (xs) p)"
  unfolding sao_assn_def array_cp_nth_def
  supply [simp] = lo_extract_elem
  by vcg

sepref_decl_op list_cp_get: nth :: "[\<lambda>(l,i). i<length l]\<^sub>f \<langle>A\<rangle>list_rel \<times>\<^sub>r nat_rel \<rightarrow> A" .
  
lemma woarray_slice_cp_nth_hnr:
  assumes "GEN_ALGO cp (is_copy A)"
  shows "(uncurry (array_cp_nth cp), uncurry mop_list_cp_get) \<in> (woarray_slice_assn A)\<^sup>k *\<^sub>a snat_assn\<^sup>k \<rightarrow>\<^sub>a A"
proof -

  from assms have copy_elem_rl[vcg_rules]: "\<And>a c. llvm_htriple (A a c) (cp c) (\<lambda>r. A a c ** A a r)" 
    unfolding GEN_ALGO_def is_copy_def
    apply -
    apply (drule hfrefD; simp)
    apply (drule hn_refineD; simp)
    apply (erule htriple_ent_post[rotated])
    apply (simp add: sep_algebra_simps)
    done
  

  show ?thesis
    apply sepref_to_hoare
    unfolding woarray_slice_assn_def eoarray_slice_assn_def hr_comp_def in_snat_rel_conv_assn
    supply [dest] = list_rel_imp_same_length
    apply (clarsimp simp: refine_pw_simps some_list_rel_conv)
    by vcg
    
qed  

context
  notes [fcomp_norm_simps] = list_rel_id_simp
begin
  sepref_decl_impl (ismop) woarray_slice_cp_nth_hnr uses mop_list_cp_get.fref[of Id] .
end

section \<open>Abstract Algorithm\<close>

  
  subsection \<open>Step 1: Partition the Array\<close>

  (* TODO: Move near set_drop_conv *)
  lemma set_take_conv_nth: "set (take m xs) = {xs!i| i. i<m \<and> i<length xs}"
    by (auto 0 3 simp: in_set_conv_nth) 

  lemma set_drop_conv_nth: "set (drop m xs) = {xs!i| i. i\<ge>m \<and> i<length xs}" by (rule set_drop_conv)
      
(* TODO: Move *)  
lemma slice_eq_mset_whole_iff: 
  "slice_eq_mset 0 (length xs) xs' xs \<longleftrightarrow> mset xs' = mset xs"  
  "slice_eq_mset 0 (length xs') xs' xs \<longleftrightarrow> mset xs' = mset xs"  
  unfolding slice_eq_mset_def Misc.slice_def
  apply clarsimp
  apply (metis dual_order.refl mset_eq_length take_all_iff)
  apply clarsimp
  apply (metis dual_order.refl mset_eq_length take_all_iff)
  done

context weak_ordering begin  

  (* Partitioning the whole list *)

  abbreviation "gpartition_all_spec p xs xs' m \<equiv> gpartition_spec 0 (length xs) p xs xs' m"

  lemma gpartition_all_spec_alt1: "gpartition_all_spec p xs xs' m \<longleftrightarrow> 
      mset xs' = mset xs 
    \<and> m\<le>length xs
    \<and> (\<forall>i<m. xs'!i \<^bold>\<le> p)  
    \<and> (\<forall>i\<in>{m..<length xs}. xs'!i \<^bold>\<ge> p)
  "
    unfolding gpartition_spec_def
    by (auto simp: slice_eq_mset_whole_iff)
  
  lemma gpartition_all_spec_alt2: "gpartition_all_spec p xs xs' m \<longleftrightarrow>
    mset xs' = mset xs 
  \<and> m\<le>length xs
  \<and> (\<forall>x\<in>set (take m xs'). x\<^bold>\<le>p)
  \<and> (\<forall>x\<in>set (drop m xs'). p\<^bold>\<le>x)
  "  
    unfolding gpartition_all_spec_alt1
    by (fastforce simp: set_take_conv_nth set_drop_conv_nth dest: mset_eq_length)  
    
  lemma gpartition_spec_permute: "mset xs = mset xs\<^sub>1 \<Longrightarrow> gpartition_all_spec p xs xs' m = gpartition_all_spec p xs\<^sub>1 xs' m"  
    unfolding gpartition_all_spec_alt1
    by (auto dest: mset_eq_length)
    
    
end

(*
  Step 1: partition the array, and keep track of the set of small/big indices
    in practice, the array will be partitioned into multiple slices, and the sets will be intervals
*)


(* An array together with sets of small/big elements *)
locale is_ppart = weak_ordering + 
  fixes p xs ss bs
  assumes complete: "ss \<union> bs = {0..<length xs}"
  assumes disjoint: "ss \<inter> bs = {}"
  assumes ss_in_P1: "i\<in>ss \<Longrightarrow> xs!i \<^bold>\<le> p"
  assumes bs_in_P2: "i\<in>bs \<Longrightarrow> p \<^bold>\<le> xs!i"
  


context weak_ordering begin
  
  definition "ppart_spec p xs xs' ss bs \<longleftrightarrow> mset xs' = mset xs \<and> is_ppart (\<^bold>\<le>) (\<^bold><) p xs' ss bs"  
    
  definition "ppart_SPEC p n xs \<equiv> doN { ASSERT(n=length xs); SPEC (\<lambda>(xs',ss,bs). ppart_spec p xs xs' ss bs) }"
  
  (* For paper *)
  lemma "ppart_SPEC p (length xs) xs = SPEC (\<lambda>(xs',ss,bs). 
    mset xs' = mset xs
  \<and> ss \<union> bs = {0..<length xs'} \<and> ss \<inter> bs = {}
  \<and> (\<forall>i\<in>ss. xs'!i \<^bold>\<le> p) \<and> (\<forall>i\<in>bs. p \<^bold>\<le> xs'!i)
  )"
    unfolding ppart_SPEC_def ppart_spec_def is_ppart_def is_ppart_axioms_def
    by (auto simp: weak_ordering_axioms)
    
  
  
  
  subsection \<open>Step 2: compute mid-index, filter misplaced indexes\<close>

  (*
    Step 2: compute position of bound (first position of big element)
  *)  
  
  definition ppart_mpos :: "nat set \<Rightarrow> nat" where "ppart_mpos ss \<equiv> card ss"
  definition ppart_filter :: "nat \<Rightarrow> nat set \<Rightarrow> nat set \<Rightarrow> nat set \<times> nat set" where "ppart_filter m ss bs \<equiv> ({i\<in>ss. m\<le>i},{i\<in>bs. i<m})"
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
  
  
locale ppar_step2 = is_ppart
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
  lemma low_nbs2_well_placed: assumes "i<m" "i\<notin>bs\<^sub>2" shows "xs!i \<^bold>\<le> p"
  proof -
    from assms misplaced.low_range_split have "i\<in>ss\<^sub>1" by fastforce
    with misplaced.ss_split have "i\<in>ss" by auto
    with ss_in_P1 show ?thesis by auto
  qed  
    
  lemma high_nss2_well_placed: assumes "m\<le>i" "i<length xs" "i\<notin>ss\<^sub>2" shows "p \<^bold>\<le> xs!i"
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
  
(* For presentation in paper *)
lemma "swap_spec_pre src dst xs \<longleftrightarrow> 
  src \<inter> dst = {} \<and> src \<union> dst \<subseteq> {0..<length xs} \<and> card src = card dst
  "
  unfolding swap_spec_pre_def
  by blast

lemma "swap_spec src dst xs xs' \<longleftrightarrow> 
    swap_spec_pre src dst xs
  \<and> mset xs' = mset xs \<and> (\<forall>i. i\<notin>src \<union> dst \<and> i<length xs \<longrightarrow> xs'!i=xs!i)
  \<and> (\<forall>i\<in>src. \<exists>j\<in>dst. xs'!i=xs!j) \<and> (\<forall>j\<in>dst. \<exists>i\<in>src. xs'!j=xs!i)
  "
  unfolding swap_spec_def swap_spec_axioms_def
  by blast




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
        
  lemma partitioned1: assumes "i<m" shows "xs'!i \<^bold>\<le> p" 
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
      
  lemma partitioned2: assumes "m\<le>i" "i<length xs" shows "p \<^bold>\<le> xs'!i"
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
    

  lemma is_valid_partition: "gpartition_all_spec p xs xs' m"
    unfolding gpartition_all_spec_alt1
    by (auto simp: permut misplaced.m_le_n partitioned1 partitioned2)

end


  


subsection \<open>The Algorithm\<close>

context weak_ordering begin
  definition "ppart1 p n xs \<equiv> do {
    (xs,ss,bs) \<leftarrow> ppart_SPEC p n xs;
    let m = ppart_mpos ss;

    let (ss\<^sub>2,bs\<^sub>2) = ppart_filter m ss bs;
    
    xs \<leftarrow> swap_SPEC ss\<^sub>2 bs\<^sub>2 xs;
  
    RETURN (m,xs)
  }"

  (* For presentation in paper *)
  lemma "ppart1 p (length xs) xs = doN {
    (xs,ss,bs) \<leftarrow> ppart_SPEC p (length xs) xs;
    let m = card ss;
    let (ss,bs) = ({i\<in>ss. m\<le>i},{i\<in>bs. i<m});
    xs \<leftarrow> swap_SPEC ss bs xs;
    RETURN (m,xs)
  }"
    unfolding ppart1_def ppart_mpos_def ppart_filter_def
    by simp
  
  
  
  lemma ppart1_valid_partitition: "n=length xs \<Longrightarrow> ppart1 p n xs \<le> SPEC (\<lambda>(m,xs'). gpartition_all_spec p xs xs' m)"
    unfolding ppart1_def ppart_spec_def swap_SPEC_def ppart_SPEC_def
    apply refine_vcg
    apply clarsimp_all
  proof -
    fix xs\<^sub>1 ss bs ss\<^sub>2X bs\<^sub>2X
    assume 
      pp_flt: "ppart_filter (ppart_mpos ss) ss bs = (ss\<^sub>2X, bs\<^sub>2X)" and
      [simp]: "mset xs\<^sub>1 = mset xs" and
      "is_ppart (\<^bold>\<le>) (\<^bold><) p xs\<^sub>1 ss bs"
  
      
    interpret is_ppart "(\<^bold>\<le>)" "(\<^bold><)" p xs\<^sub>1 ss bs by fact  
    interpret ppar_step2 "(\<^bold>\<le>)" "(\<^bold><)" p xs\<^sub>1 ss bs by unfold_locales
    
    have [simp]: "ss\<^sub>2X = ss\<^sub>2" "bs\<^sub>2X = bs\<^sub>2" unfolding ss\<^sub>2_def bs\<^sub>2_def using pp_flt
      by auto

    show "swap_spec_pre ss\<^sub>2X bs\<^sub>2X xs\<^sub>1" using swap_spec_pre by simp 
      
    fix xs'  
    assume sspec: "swap_spec ss\<^sub>2X bs\<^sub>2X xs\<^sub>1 xs'"
  
          
    interpret swap_spec ss\<^sub>2 bs\<^sub>2 xs\<^sub>1 xs' 
      using sspec by simp
      
    interpret ppar_step3 "(\<^bold>\<le>)" "(\<^bold><)" p xs\<^sub>1 ss bs xs'
      by unfold_locales 
      
    show "gpartition_all_spec p xs xs' m"  
      using \<open>mset xs\<^sub>1 = mset xs\<close> is_valid_partition gpartition_spec_permute by blast
  qed    
  
  (* For presentation in paper *)
  lemma "ppart1 p (length xs) xs \<le> SPEC (\<lambda>(m, xs'). 
      mset xs' = mset xs \<and> m \<le> length xs 
    \<and> (\<forall>i<m. xs' ! i \<^bold>\<le> p) \<and> (\<forall>i\<in>{m..<length xs}. p \<^bold>\<le> xs' ! i))"
    using ppart1_valid_partitition[OF refl, of p xs] 
    unfolding gpartition_all_spec_alt1 by simp
    
  
end
  
section \<open>Refinement to Parallel Partitioning\<close>  

context weak_ordering begin
  
  (*
    Parallel partitioning with interval, abstract level
  *)
  
  lemma ppart_spec_merge:
    assumes "ppart_spec p xs\<^sub>1 xs\<^sub>1' ss\<^sub>1 bs\<^sub>1"
    assumes "ppart_spec p xs\<^sub>2 xs\<^sub>2' ss\<^sub>2 bs\<^sub>2"
    defines "ss\<^sub>2' \<equiv> (+)(length xs\<^sub>1)`ss\<^sub>2"
    defines "bs\<^sub>2' \<equiv> (+)(length xs\<^sub>1)`bs\<^sub>2"
    shows "ppart_spec p (xs\<^sub>1@xs\<^sub>2) (xs\<^sub>1'@xs\<^sub>2') (ss\<^sub>1 \<union> ss\<^sub>2') (bs\<^sub>1 \<union> bs\<^sub>2')"
    using assms(1,2)
    unfolding ppart_spec_def 
  proof clarsimp
    assume "mset xs\<^sub>1' = mset xs\<^sub>1" "mset xs\<^sub>2' = mset xs\<^sub>2"
    hence [simp]: "length xs\<^sub>1' = length xs\<^sub>1" "length xs\<^sub>2' = length xs\<^sub>2"
      by (auto dest: mset_eq_length)
  
  
    assume "is_ppart (\<^bold>\<le>) (\<^bold><) p xs\<^sub>1' ss\<^sub>1 bs\<^sub>1" "is_ppart (\<^bold>\<le>) (\<^bold><) p xs\<^sub>2' ss\<^sub>2 bs\<^sub>2"

    then interpret p1: is_ppart "(\<^bold>\<le>)" "(\<^bold><)" p xs\<^sub>1' ss\<^sub>1 bs\<^sub>1 + p2: is_ppart "(\<^bold>\<le>)" "(\<^bold><)" p xs\<^sub>2' ss\<^sub>2 bs\<^sub>2 .
    
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
    
          
    
    show "is_ppart (\<^bold>\<le>) (\<^bold><) p (xs\<^sub>1' @ xs\<^sub>2') (ss\<^sub>1 \<union> ss\<^sub>2') (bs\<^sub>1 \<union> bs\<^sub>2')"
      apply unfold_locales
      subgoal
        apply (rule HOL.trans[where s="(ss\<^sub>1\<union>bs\<^sub>1)\<union>(ss\<^sub>2' \<union> bs\<^sub>2')"])
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
        
  
  definition "gpartition_slices d p len xs = RECT (\<lambda>gpartition_slices (len,xs). do {
    ASSERT (d>0);
    ASSERT (len = length xs);
    if (len \<le> d) then do {
      (xs,ss,bs) \<leftarrow> ppart_SPEC p len xs;
      RETURN (xs,ss,bs)
    } else do {
      let si = len - d;
      (((ss\<^sub>1,bs\<^sub>1),(ss\<^sub>2,bs\<^sub>2)),xs) \<leftarrow> WITH_SPLIT si xs (\<lambda>xs\<^sub>1 xs\<^sub>2. do {
        ((xs\<^sub>1,ivs\<^sub>1),(xs\<^sub>2,ivs\<^sub>2)) \<leftarrow> nres_par (gpartition_slices) (ppart_SPEC p d) (si,xs\<^sub>1) xs\<^sub>2;
        RETURN (((ivs\<^sub>1,ivs\<^sub>2),xs\<^sub>1,xs\<^sub>2))
      });
      
      ASSERT(iv_incr_elems_abs_bound ss\<^sub>2 si len);
      ss\<^sub>2\<leftarrow>mop_set_incr_elems si ss\<^sub>2;
      
      ASSERT(iv_incr_elems_abs_bound bs\<^sub>2 si len);
      bs\<^sub>2\<leftarrow>mop_set_incr_elems si bs\<^sub>2;
      
      ss\<leftarrow>mop_set_union_disj ss\<^sub>1 ss\<^sub>2;
      bs\<leftarrow>mop_set_union_disj bs\<^sub>1 bs\<^sub>2;
      
      RETURN (xs,ss,bs)
    }
  }) (len,xs)"
  
  lemma ppart_spec_imp_len_eq: "ppart_spec p xs xs' ss bs \<Longrightarrow> length xs' = length xs"
    unfolding ppart_spec_def
    by (auto dest: mset_eq_length)
  
  lemma ppart_spec_len_bound: 
    assumes "ppart_spec p xs xs' ss bs" 
    shows "ss\<subseteq>{0..<length xs}" "bs\<subseteq>{0..<length xs}"  
    using assms unfolding ppart_spec_def is_ppart_def is_ppart_axioms_def 
    by (auto dest!: mset_eq_length)
    
  lemma ppart_spec_lb_imp_disj:
    assumes "ppart_spec p xs xs' ss bs"
    shows "ss \<inter> (+)(length xs)`ss' = {}" "bs \<inter> (+)(length xs)`bs' = {}"
    using ppart_spec_len_bound[OF assms]
    by auto
    
  
  lemma gpartition_slices_refine_aux: "d>0 \<Longrightarrow> gpartition_slices d p len xs \<le> ppart_SPEC p len xs"
    unfolding gpartition_slices_def ppart_SPEC_def
    
    thm RECT_rule
    
    apply refine_vcg
    
    apply (refine_vcg RECT_rule[
      where 
            V="measure (\<lambda>(_,xs). length xs)" 
        and pre="\<lambda>(len,xs). len=length xs" 
        and M="\<lambda>(d,xs). Refine_Basic.SPEC (\<lambda>(xs', ss, bs). ppart_spec p xs xs' ss bs)", 
      THEN order_trans])
    apply (all \<open>(thin_tac "RECT _ = _")?\<close>)
    
    subgoal by simp  
    subgoal by auto
    subgoal by simp  
    subgoal by clarsimp
    subgoal by simp  
    
    apply (drule sym[of "length _" "_ - _"]) (* Turn around problematic premise for simplifier *)
    
    apply (rule order_trans)
    apply rprems 
    
    subgoal by force
    subgoal by auto
    
    apply refine_vcg
    subgoal by (auto dest: ppart_spec_imp_len_eq)
    subgoal by (auto dest: ppart_spec_imp_len_eq)
    subgoal by (auto dest: ppart_spec_imp_len_eq)
    subgoal
      apply clarsimp
      apply (rule iv_incr_elems_abs_bound_card_boundI) 
      apply (erule ppart_spec_len_bound)
      by simp
    subgoal 
      apply clarsimp
      apply (rule iv_incr_elems_abs_bound_card_boundI) 
      apply (erule ppart_spec_len_bound)
      by simp
    subgoal by (simp add: ppart_spec_lb_imp_disj)
    subgoal by (simp add: ppart_spec_lb_imp_disj)
    subgoal by (auto intro: ppart_spec_merge)
    subgoal by auto
    done    
    
    
  lemma gpartition_slices_refine: "\<lbrakk> (xs,xs')\<in>\<langle>Id\<rangle>list_rel; d>0\<rbrakk> \<Longrightarrow> gpartition_slices d p n xs \<le> \<Down>Id (ppart_SPEC p n xs')"
    by (auto simp: gpartition_slices_refine_aux)
  
    
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
    xs \<leftarrow> mop_sl_of_list xs;
    xs \<leftarrow> par_swap_aux ss bs xs;
    mop_list_of_sl xs
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

  lemma to_plain_complete:
    assumes [simp]: "xs = sl_of_list xs\<^sub>0"
    shows "sl_complete (sl_struct xs')"
    by simp


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
  apply (simp add: swap_opt_spec.to_plain_complete)
  apply (simp add: swap_opt_spec.to_plain)
  done

lemma par_swap_refine: "\<lbrakk>(ss,ss')\<in>\<langle>Id\<rangle>set_rel; (bs,bs')\<in>\<langle>Id\<rangle>set_rel; (xs,xs')\<in>\<langle>Id\<rangle>list_rel\<rbrakk> 
  \<Longrightarrow> par_swap ss bs xs \<le>\<Down>(\<langle>Id\<rangle>list_rel) (swap_SPEC ss' bs' xs')"
  by (auto simp: par_swap_refine_aux)
  

  
  
definition "swap_o_intv_aux \<equiv> \<lambda>(l\<^sub>1,h\<^sub>1) (l\<^sub>2,h\<^sub>2) xs\<^sub>0. doN {
  ASSERT (l\<^sub>1\<le>h\<^sub>1 \<and> l\<^sub>2\<le>h\<^sub>2 \<and> h\<^sub>2-l\<^sub>2 = h\<^sub>1-l\<^sub>1);
  (xs,_,_)\<leftarrow>WHILEIT 
    (\<lambda>(xs,i\<^sub>1,i\<^sub>2). i\<^sub>1\<in>{l\<^sub>1..h\<^sub>1} \<and> i\<^sub>2\<in>{l\<^sub>2..h\<^sub>2} \<and> i\<^sub>1-l\<^sub>1 = i\<^sub>2-l\<^sub>2 \<and> swap_opt_spec {l\<^sub>1..<i\<^sub>1} {l\<^sub>2..<i\<^sub>2} xs\<^sub>0 xs)
    (\<lambda>(xs,i\<^sub>1,i\<^sub>2). i\<^sub>1<h\<^sub>1) 
    (\<lambda>(xs,i\<^sub>1,i\<^sub>2). doN {
      ASSERT(i\<^sub>1<h\<^sub>1 \<and> i\<^sub>2<h\<^sub>2);
      xs\<leftarrow>mop_slist_swap xs i\<^sub>1 i\<^sub>2;
      RETURN (xs,i\<^sub>1+1,i\<^sub>2+1)
    }) (xs\<^sub>0,l\<^sub>1,l\<^sub>2);
  RETURN xs
}"  

lemma swap_opt_spec_empty[simp]: "swap_opt_spec {} {} xs\<^sub>0 xs\<^sub>0"
  apply unfold_locales
  by auto

(* TODO: Move *)  
lemma sl_struct_swap[simp]: "\<lbrakk> i\<in>sl_indexes' xs; j\<in>sl_indexes' xs \<rbrakk> \<Longrightarrow> sl_struct (swap xs i j) = sl_struct xs"
  by (simp flip: sl_swap_aux)
  
  
lemma sl_get_swap_iff: "\<lbrakk> i\<in>sl_indexes' xs; j\<in>sl_indexes' xs \<rbrakk> \<Longrightarrow> sl_get (swap xs i j) k = (if k=i then sl_get xs j else if k=j then sl_get xs i else sl_get xs k)"  
  by (auto simp add: sl_get_def swap_nth dest!: sl_indexes_lengthD)
  
lemma sl_get_swap_other: "\<lbrakk>k\<noteq>i; k\<noteq>j\<rbrakk> \<Longrightarrow> sl_get (swap xs i j) k = sl_get xs k"  
  by (simp add: sl_get_def)
  
  
lemma swap_o_intv_aux_correct:
  assumes "l\<^sub>1\<le>h\<^sub>1" "l\<^sub>2\<le>h\<^sub>2"
  shows "swap_o_intv_aux (l\<^sub>1,h\<^sub>1) (l\<^sub>2,h\<^sub>2) xs\<^sub>0  \<le> swap_opt_SPEC {l\<^sub>1..<h\<^sub>1} {l\<^sub>2..<h\<^sub>2} xs\<^sub>0"
  unfolding swap_opt_SPEC_def
  apply refine_vcg
proof -  
  assume "swap_opt_spec_pre {l\<^sub>1..<h\<^sub>1} {l\<^sub>2..<h\<^sub>2} xs\<^sub>0"

  then interpret swap_opt_spec_pre "{l\<^sub>1..<h\<^sub>1}" "{l\<^sub>2..<h\<^sub>2}" xs\<^sub>0 .
  
  {
    fix xs i\<^sub>1 i\<^sub>2
    assume B1: "l\<^sub>1 \<le> i\<^sub>1" "i\<^sub>1 < h\<^sub>1"
    assume B2: "l\<^sub>2 \<le> i\<^sub>2" "i\<^sub>2 < h\<^sub>2" 
    
    assume "swap_opt_spec {l\<^sub>1..<i\<^sub>1} {l\<^sub>2..<i\<^sub>2} xs\<^sub>0 xs"
    then interpret this: swap_opt_spec "{l\<^sub>1..<i\<^sub>1}" "{l\<^sub>2..<i\<^sub>2}" xs\<^sub>0 xs .
    
    have [simp]: "i\<^sub>1 \<in> sl_indexes' xs\<^sub>0" "i\<^sub>2 \<in> sl_indexes' xs\<^sub>0" using B1 B2 src_ss dst_ss by auto
    
    
    have "swap_opt_spec {l\<^sub>1..<Suc i\<^sub>1} {l\<^sub>2..<Suc i\<^sub>2} xs\<^sub>0 (swap xs i\<^sub>1 i\<^sub>2)"
      apply unfold_locales
      subgoal using B1 B2 src_dst_dj by fastforce
      subgoal using B1 B2 src_ss by fastforce
      subgoal using B1 B2 dst_ss by fastforce
      subgoal using B1 B2 this.card_eq by (metis Suc_diff_le card_atLeastLessThan)
      subgoal using B1 B2 src_ss dst_ss by fastforce
      subgoal using B1 B2 this.elems_outside by (auto simp: sl_get_swap_other) 
      subgoal for j
        apply (subgoal_tac "j\<noteq>i\<^sub>2 \<and> j\<in>sl_indexes' xs\<^sub>0")
        apply clarsimp
        apply (cases "j<i\<^sub>1")
        subgoal using this.elems_src[of j] by (auto simp: sl_get_swap_iff)
        subgoal using B1 B2 src_dst_dj by (auto simp: this.elems_outside sl_get_swap_iff)
        using B1 B2 src_dst_dj src_ss by auto  
      subgoal for j
        apply (subgoal_tac "j\<noteq>i\<^sub>1 \<and> j\<in>sl_indexes' xs\<^sub>0")
        apply clarsimp
        apply (cases "j<i\<^sub>2")
        subgoal using this.elems_dst[of j] by (auto simp: sl_get_swap_iff)
        subgoal using B1 B2 src_dst_dj by (auto simp: this.elems_outside sl_get_swap_iff)
        using B1 B2 src_dst_dj dst_ss by auto  
      by (metis \<open>i\<^sub>1 \<in> sl_indexes' xs\<^sub>0\<close> \<open>i\<^sub>2 \<in> sl_indexes' xs\<^sub>0\<close> sl_indexes_lengthD sl_struct_length swap_multiset this.length_eq this.permut)  
  } note aux=this
  
  show "swap_o_intv_aux (l\<^sub>1, h\<^sub>1) (l\<^sub>2, h\<^sub>2) xs\<^sub>0 \<le> SPEC (swap_opt_spec {l\<^sub>1..<h\<^sub>1} {l\<^sub>2..<h\<^sub>2} xs\<^sub>0)"
    unfolding swap_o_intv_aux_def
    apply (refine_vcg WHILEIT_rule[where R="measure (\<lambda>(_,i,_). h\<^sub>1-i)"])
    apply (clarsimp_all simp: assms swap_opt_spec.struct_eq aux)
    subgoal using card_eq by simp
    subgoal by auto
    subgoal using src_ss by fastforce
    subgoal using dst_ss by fastforce
    subgoal using Suc_diff_le by presburger
    subgoal using diff_less_mono2 lessI by presburger
    subgoal for xs i2 using assms(2) eq_diff_iff by blast
    done
    
qed

(* Transform this to intervals *)

(* As we, technically, allow intervals to be empty here, we guard against empty intervals. *)
definition "swap_o_intv \<equiv> \<lambda>(l\<^sub>1,h\<^sub>1) (l\<^sub>2,h\<^sub>2) xs. 
  if l\<^sub>1\<le>h\<^sub>1 \<and> l\<^sub>2\<le>h\<^sub>2 then swap_o_intv_aux (l\<^sub>1,h\<^sub>1) (l\<^sub>2,h\<^sub>2) xs else RETURN xs"

lemma swap_opt_spec_pre_empty1_conv: "swap_opt_spec_pre {} bs xs\<^sub>0 \<longleftrightarrow> bs={}"  
  unfolding swap_opt_spec_pre_def 
  by (auto dest: finite_subset[OF _ sl_indexes_finite])
  
lemma swap_opt_spec_pre_empty2_conv: "swap_opt_spec_pre ss {} xs\<^sub>0 \<longleftrightarrow> ss={}"  
  unfolding swap_opt_spec_pre_def 
  by (auto dest: finite_subset[OF _ sl_indexes_finite])
  
  
lemma swap_o_intv_correct:
  shows "swap_o_intv (l\<^sub>1,h\<^sub>1) (l\<^sub>2,h\<^sub>2) xs\<^sub>0  \<le> swap_opt_SPEC {l\<^sub>1..<h\<^sub>1} {l\<^sub>2..<h\<^sub>2} xs\<^sub>0"
  unfolding swap_o_intv_def
  apply (cases "l\<^sub>1 \<le> h\<^sub>1"; cases "l\<^sub>2 \<le> h\<^sub>2"; simp)
  apply (simp add: swap_o_intv_aux_correct)
  unfolding swap_opt_SPEC_def
  apply (all refine_vcg)
  apply (simp_all add: swap_opt_spec_pre_empty1_conv swap_opt_spec_pre_empty2_conv)
  done
  
  
  
lemma swap_o_intv_refine: "(swap_o_intv, swap_opt_SPEC) \<in> iv_rel \<rightarrow> iv_rel \<rightarrow> Id \<rightarrow> \<langle>Id\<rangle>nres_rel"
  by (clarsimp simp: iv_rel_def in_br_conv iv_\<alpha>_def intro!: nres_relI swap_o_intv_correct)
  
context
  notes [fcomp_norm_simps] = iv_assn_def[symmetric]
begin  
  
  private abbreviation (input) "ivA \<equiv> iv_assn_raw :: _ \<Rightarrow> size_t word \<times> _ \<Rightarrow> _"

  sepref_definition swap_o_intv_impl [llvm_code] is "uncurry2 swap_o_intv" 
    :: "[\<lambda>_. True]\<^sub>c ivA\<^sup>k *\<^sub>a ivA\<^sup>k *\<^sub>a (oarray_idxs_assn A)\<^sup>d \<rightarrow> oarray_idxs_assn A [\<lambda>((_,_),xsi) ri. ri=xsi]\<^sub>c"
    unfolding swap_o_intv_def swap_o_intv_aux_def iv_assn_raw_def
    apply (annot_snat_const "TYPE(size_t)")
    by sepref
  
  lemmas swap_o_intv_oidxs_hnr[sepref_fr_rules] = swap_o_intv_impl.refine[FCOMP swap_o_intv_refine]  
  
end  
  
    
section \<open>Wrap-Up: Parallel Algorithm on Abstract Level\<close>
  
context weak_ordering begin

definition "ppart2 d p n xs \<equiv> do {
  (xs,ss,bs) \<leftarrow> gpartition_slices d p n xs;
  m \<leftarrow> mop_set_card ss;

  let (ss\<^sub>2,bs\<^sub>2) = ppart_filter m ss bs;
  
  xs \<leftarrow> par_swap ss\<^sub>2 bs\<^sub>2 xs;

  RETURN (m,xs)
}"
  


term gpartition_all_spec

thm ppart1_valid_partitition

lemma ppart2_refine: "\<lbrakk> 0<d; (xs,xs')\<in>\<langle>Id\<rangle>list_rel; n=length xs' \<rbrakk> \<Longrightarrow> ppart2 d p n xs \<le> \<Down>Id (ppart1 p n xs')"
  unfolding ppart2_def ppart1_def ppart_mpos_def
  apply (refine_rcg gpartition_slices_refine par_swap_refine)
  by auto

  
lemma ppart2_refine_p_all_spec: 
  assumes "0<d" "n=length xs"  
  shows "ppart2 d p n xs \<le> (SPEC(\<lambda>(m,xs'). gpartition_all_spec p xs xs' m))"
proof -  
  note ppart2_refine
  also note ppart1_valid_partitition
  finally show ?thesis using assms by simp
qed


term partition3_spec
thm partition3_spec_def

term qs_partition

term WITH_SPLIT


definition "ppart_partition_pivot_par d xs n \<equiv> doN {
  ASSERT (n=length xs \<and> 4\<le>length xs);
  
  xs \<leftarrow> move_pivot_to_first_sample xs n;

  p \<leftarrow> mop_list_cp_get xs 0;
    
  (m,xs) \<leftarrow> WITH_SPLIT 1 xs (\<lambda>xs\<^sub>1 xs\<^sub>2. doN {
    ASSERT (n>0);
    (m,xs\<^sub>2) \<leftarrow> ppart2 d p (n-1) xs\<^sub>2;
    RETURN (m,xs\<^sub>1,xs\<^sub>2)
  });
  
  ASSERT (m+1 \<le> n);
  
  let m'=m+1;
  
  if m'=n then doN {
    xs\<leftarrow>mop_list_swap xs 0 m;
    RETURN (xs,m)
  } else RETURN (xs,m')
}"

lemma move_pivot_to_first_sample_weak_correct: 
  "\<lbrakk>n=length xs; length xs \<ge> 4\<rbrakk> \<Longrightarrow> move_pivot_to_first_sample xs n \<le> SPEC (\<lambda>xs'. mset xs' = mset xs)"
  apply refine_vcg by simp


lemma mset_eq_sum_mset_lengthD: "mset xs = mset xs\<^sub>1 + mset xs\<^sub>2 \<Longrightarrow> length xs = length xs\<^sub>1+length xs\<^sub>2"
  by (metis size_mset size_union)


lemma slice_LT_by_nthI:
  assumes "l\<le>m" "m\<le>h" "h\<le>length xs"
  assumes "\<forall>i\<in>{l..<m}. xs!i\<^bold>\<le>p" "\<forall>i\<in>{m..<h}. p\<^bold>\<le>xs!i"
  shows "slice_LT (\<^bold>\<le>) (Misc.slice l m xs) (Misc.slice m h xs)"  
  using assms
  unfolding slice_LT_def Ball_def in_set_conv_nth
  by (force simp: slice_nth intro: trans[of _ p]) 
  
  
lemma ppart_partition_pivot_par_refines_part3: "\<lbrakk>0<d; n=length xs\<rbrakk> \<Longrightarrow> ppart_partition_pivot_par d xs n \<le> partition3_spec xs 0 n"
  unfolding partition3_spec_def ppart_partition_pivot_par_def
  apply (refine_vcg ppart2_refine_p_all_spec move_pivot_to_first_sample_weak_correct)
  apply (clarsimp_all dest!: sym[of "_+_" "mset _"] simp: gpartition_spec_def slice_eq_mset_whole_iff)
  subgoal by (auto dest: mset_eq_length)
  subgoal by (auto dest: mset_eq_sum_mset_lengthD)
  subgoal by (auto dest: mset_eq_length mset_eq_sum_mset_lengthD)
  subgoal by (auto dest: mset_eq_length mset_eq_sum_mset_lengthD)
  subgoal by (auto dest: mset_eq_length mset_eq_sum_mset_lengthD)
  
  (* Swapping: multiset equal *)
  subgoal by (subst swap_multiset; auto dest: mset_eq_length)
    
  (* Swapping: partitioning *)
  subgoal for xs\<^sub>1 xs\<^sub>2 xs\<^sub>2' m
    apply (rule slice_LT_by_nthI[where p="xs\<^sub>1 ! 0"])
    apply clarsimp_all
    subgoal by (drule mset_eq_length)+ auto
    subgoal by (drule mset_eq_length)+ (auto simp: length_Suc_conv swap_nth)
    subgoal by (drule mset_eq_length)+ (auto simp: length_Suc_conv swap_nth)
    done
    
  (* Shifting: partitioning *)
  subgoal for xs\<^sub>2 m xs\<^sub>2' xs\<^sub>1
    apply (rule slice_LT_by_nthI[where p="xs\<^sub>1 ! 0"])
    apply clarsimp_all
    subgoal by (drule mset_eq_length mset_eq_sum_mset_lengthD)+ (auto)
    subgoal by (drule mset_eq_length mset_eq_sum_mset_lengthD)+ (auto simp: length_Suc_conv nth_Cons')
    subgoal by (drule mset_eq_length mset_eq_sum_mset_lengthD)+ (force simp: length_Suc_conv nth_Cons')
    done
  done    
  
  
  



  
definition align_chunk_size :: "nat \<Rightarrow> nat \<Rightarrow> nat nres" where "align_chunk_size d n = doN {
  ASSERT (d>0);
  if n=0 \<or> d=1 then RETURN d
  else doN {
    p \<leftarrow> nat_div_round_up n d;
    nat_div_round_up n p
  }
}"  

lemma align_chunk_size_correct[refine_vcg]: "d>0 \<Longrightarrow> align_chunk_size d n \<le> SPEC (\<lambda>r. r>0)"
  unfolding align_chunk_size_def
  apply refine_vcg
  by (auto intro: ccontr[of "0<_"])

  
definition "ppart_partition_pivot d xs n \<equiv> 
  if n\<le>d then partition_pivot_sample xs n
  else doN {
    d \<leftarrow> align_chunk_size d n;
    ppart_partition_pivot_par d xs n
  }"  
  
  
lemma ppart_partition_pivot_refines_part3: "\<lbrakk>0<d; n=length xs\<rbrakk> \<Longrightarrow> ppart_partition_pivot d xs n \<le> partition3_spec xs 0 n"
  unfolding ppart_partition_pivot_def
  apply (split if_split, intro conjI impI)
  subgoal
    using partition_pivot_sample_correct[of xs xs n n]
    by (auto)
  subgoal
    apply (rule specify_left)  
    apply (rule align_chunk_size_correct, simp)
    apply (rule ppart_partition_pivot_par_refines_part3)
    by auto
  done    
  
    
end  

  



(* Taking the smallest of two intervals, chopping the other *)

definition "split_sets_eq1 s\<^sub>1 s\<^sub>2 = do {

  (c\<^sub>1,r\<^sub>1) \<leftarrow> mop_set_rm_subset s\<^sub>1;
  (c\<^sub>2,r\<^sub>2) \<leftarrow> mop_set_rm_subset s\<^sub>2;
    
  let card\<^sub>1 = op_set_card c\<^sub>1;
  let card\<^sub>2 = op_set_card c\<^sub>2;

  let mc = min card\<^sub>1 card\<^sub>2;
  
  (c\<^sub>1\<^sub>1,c\<^sub>1\<^sub>2) \<leftarrow> mop_set_split_card mc c\<^sub>1;
  (c\<^sub>2\<^sub>1,c\<^sub>2\<^sub>2) \<leftarrow> mop_set_split_card mc c\<^sub>2;
  
  r\<^sub>1 \<leftarrow> mop_set_union_disj r\<^sub>1 c\<^sub>1\<^sub>2;
  r\<^sub>2 \<leftarrow> mop_set_union_disj r\<^sub>2 c\<^sub>2\<^sub>2;

  RETURN ((c\<^sub>1\<^sub>1,r\<^sub>1),(c\<^sub>2\<^sub>1,r\<^sub>2))
}"



lemma ivls_split_refine: "(split_sets_eq1, split_sets_eq_SPEC) \<in> Id \<rightarrow> Id \<rightarrow> \<langle>Id\<rangle>nres_rel"
  unfolding split_sets_eq1_def split_sets_eq_SPEC_def
  apply clarsimp
  apply (refine_vcg SPEC_refine)
  apply simp_all
  subgoal by blast
  subgoal by blast
  apply (intro conjI)
  subgoal by blast
  subgoal by blast
  subgoal by blast
  subgoal by (metis Int_Un_distrib inf_commute)
  subgoal by (metis card_gt_0_iff min_less_iff_conj sup_bot_left)
  done

abbreviation "iv_assn_sz \<equiv> iv_assn' TYPE(size_t)"  
abbreviation "iv_lb_assn_sz \<equiv> iv_lb_assn' TYPE(size_t)"  
abbreviation "ivl_assn_sz \<equiv> ivl_assn' TYPE(size_t)"  
  

sepref_definition split_sets_eq_impl [llvm_inline] is "uncurry split_sets_eq1" :: "ivl_assn_sz\<^sup>d *\<^sub>a ivl_assn_sz\<^sup>d \<rightarrow>\<^sub>a (iv_assn_sz \<times>\<^sub>a ivl_assn_sz) \<times>\<^sub>a (iv_assn_sz \<times>\<^sub>a ivl_assn_sz)"
  unfolding split_sets_eq1_def min_def
  by sepref
  
sepref_register split_sets_eq_SPEC
lemmas split_sets_eq_impl_spec_refine[sepref_fr_rules] = split_sets_eq_impl.refine[FCOMP ivls_split_refine]


  
context weak_ordering begin
  term partition_spec 
  term partition_SPEC

  definition "ppart_seq1 p h xs \<equiv> do {
    ASSERT (h = length xs);
    (xs,m) \<leftarrow> gpartition_SPEC 0 h p xs;
    RETURN (xs,{0..<m},{m..<h})
  }"
  
  
  lemma gpartition_all_imp_ppart_spec: 
    "gpartition_all_spec p xs xs' m \<Longrightarrow> ppart_spec p xs xs' {0..<m} {m..<length xs}"
    unfolding gpartition_all_spec_alt1 ppart_spec_def
    apply (clarsimp) 
    apply (frule mset_eq_length)
    apply unfold_locales
    apply auto
    done

  sepref_register ppart_SPEC   
       
  lemma ppart_seq1_refine: "(ppart_seq1, PR_CONST ppart_SPEC) \<in> Id \<rightarrow> Id \<rightarrow> Id \<rightarrow> \<langle>Id\<rangle>nres_rel"
    unfolding ppart_seq1_def gpartition_SPEC_def ppart_SPEC_def PR_CONST_def
    apply refine_vcg
    by (clarsimp_all simp: gpartition_all_imp_ppart_spec)

  (*
    Refinement to match technical requirements of Sepref:
    
    Recursion must not rely on frame (all used parameters must be arguments to recursive function)
    Pivot element must be explicitly copied
    
    If doing sequential partitioning, the result must be converted from iv to ivl. 
    We currently do that by op_set_union_disj _ {}, and a custom_fold to include the length parameter.
    TODO: a iv_to_ivl conversion operator would not need the custom fold, 
    and save the (trivial) disjoint side-condition that, nevertheless, has to be solved by sepref
  *)  
    
  definition "gpartition_slices2 d p len xs = RECT (\<lambda>gpartition_slices (d,p,len,xs). do {
    ASSERT (d>0);
    ASSERT (len = length xs);
    if (len \<le> d) then do {
      (xs,ss,bs) \<leftarrow> ppart_SPEC p len xs;
      RETURN (xs,op_set_union_disj ss {},op_set_union_disj bs {})
    } else do {
      let si = len - d;
      (((ss\<^sub>1,bs\<^sub>1),(ss\<^sub>2,bs\<^sub>2)),xs) \<leftarrow> WITH_SPLIT si xs (\<lambda>xs\<^sub>1 xs\<^sub>2. do {
        let p_copy = COPY p;
        ((xs\<^sub>1,ivs\<^sub>1),(xs\<^sub>2,ivs\<^sub>2)) \<leftarrow> nres_par (gpartition_slices) (\<lambda>(p,d,xs). ppart_SPEC p d xs) (d,p,si,xs\<^sub>1) (p_copy,d,xs\<^sub>2);
        RETURN (((ivs\<^sub>1,ivs\<^sub>2),xs\<^sub>1,xs\<^sub>2))
      });
      
      ASSERT(iv_incr_elems_abs_bound ss\<^sub>2 si len);
      ss\<^sub>2\<leftarrow>mop_set_incr_elems si ss\<^sub>2;
      
      ASSERT(iv_incr_elems_abs_bound bs\<^sub>2 si len);
      bs\<^sub>2\<leftarrow>mop_set_incr_elems si bs\<^sub>2;
      
      ss\<leftarrow>mop_set_union_disj ss\<^sub>1 ss\<^sub>2;
      bs\<leftarrow>mop_set_union_disj bs\<^sub>1 bs\<^sub>2;
      
      RETURN (xs,ss,bs)
    }
  }) (d,COPY p,len,xs)"
    
  lemma gpartition_slices2_refine: "(gpartition_slices2, PR_CONST gpartition_slices) 
    \<in> nat_rel \<rightarrow> Id \<rightarrow> nat_rel \<rightarrow> \<langle>Id\<rangle>list_rel \<rightarrow> \<langle>\<langle>Id\<rangle>list_rel \<times>\<^sub>r Id \<times>\<^sub>r Id\<rangle>nres_rel"
  proof (intro fun_relI, clarsimp, goal_cases)
    case (1 d\<^sub>0 p\<^sub>0 len\<^sub>0 xs\<^sub>0)
    
    define R1 where "R1={((d\<^sub>0,p\<^sub>0,len,xs),(len,xs)) | (len::nat) (xs::'a list). True }"
    note [refine_dref_RELATES] = RELATESI[of R1]
    
    
    show ?case
      unfolding gpartition_slices2_def gpartition_slices_def
      apply (rewrite at "let _ = COPY _ in  _" Let_def)
      apply refine_rcg
      apply refine_dref_type
      unfolding R1_def
      by simp_all
    
  qed
    
end






   
context sort_impl_copy_context begin




  definition [llvm_code]: "swap_o_intv_impl_uncurried \<equiv> (\<lambda>(a, x, y). swap_o_intv_impl a x y)"


  sepref_def par_swap_aux_impl is "uncurry2 par_swap_aux" 
    :: "[\<lambda>_. True]\<^sub>c ivl_assn_sz\<^sup>d *\<^sub>a ivl_assn_sz\<^sup>d *\<^sub>a (oarray_idxs_assn elem_assn)\<^sup>d \<rightarrow> oarray_idxs_assn elem_assn [\<lambda>((_,_),xsi) xsi'. xsi'=xsi]\<^sub>c"
    unfolding par_swap_aux_def
    supply [[goals_limit = 1]]
    apply (rewrite RECT_cp_annot[where CP="\<lambda>(_,_,xsi) xsi'. xsi'=xsi"])
    supply [sepref_comb_rules] = hn_RECT_cp_annot_noframe
    supply [sepref_opt_simps] = swap_o_intv_impl_uncurried_def[symmetric]
    by sepref    
    
  sepref_def par_swap_impl is "uncurry2 par_swap" 
    :: "[\<lambda>_. True]\<^sub>c ivl_assn_sz\<^sup>d *\<^sub>a ivl_assn_sz\<^sup>d *\<^sub>a (arr_assn)\<^sup>d \<rightarrow> arr_assn [\<lambda>((_,_),xsi) xsi'. xsi'=xsi]\<^sub>c"
    unfolding par_swap_def
    by sepref
    
    
  sepref_definition ppart_seq_impl [llvm_inline] is "uncurry2 ppart_seq1" :: "[\<lambda>_. True]\<^sub>c elem_assn\<^sup>k *\<^sub>a size_assn\<^sup>k *\<^sub>a arr_assn\<^sup>d \<rightarrow> arr_assn \<times>\<^sub>a iv_assn_sz \<times>\<^sub>a iv_assn_sz [\<lambda>(_,xsi) (xsi',_,_). xsi'=xsi]\<^sub>c" 
    unfolding ppart_seq1_def
    apply (annot_snat_const "TYPE(size_t)")
    by sepref
  
  lemmas ppart_seq_impl_hnr[sepref_fr_rules] = ppart_seq_impl.refine[FCOMP ppart_seq1_refine]
    

  (* We fold that, because the parallel operator works only with functions wight now.
    TODO: use automatic extraction (like for REC) to extract functions from parallel operator upon code generation!
  *)
  definition [llvm_code]: "ppart_seq1_impl_uncurried \<equiv> \<lambda>(p,d,xs). ppart_seq_impl p d xs"
    
  
  sepref_register gpartition_slices
  
  sepref_definition gpartition_slices_impl [llvm_code] is "uncurry3 gpartition_slices2" :: 
    "[\<lambda>_. True]\<^sub>c size_assn\<^sup>k *\<^sub>a elem_assn\<^sup>k *\<^sub>a size_assn\<^sup>k *\<^sub>a arr_assn\<^sup>d \<rightarrow> arr_assn \<times>\<^sub>a ivl_assn_sz \<times>\<^sub>a ivl_assn_sz [\<lambda>(_,xsi) (xsi',_,_). xsi'=xsi]\<^sub>c"
    unfolding gpartition_slices2_def
    supply [[goals_limit = 1]]
    
    apply (rewrite RECT_cp_annot[where CP="\<lambda>(_,_,_,xsi) (xsi',_,_). xsi'=xsi"])
    apply (rewrite ivl_fold_custom_empty[where 'l=size_t])
    apply (rewrite ivl_fold_custom_empty[where 'l=size_t])
  
    supply [sepref_comb_rules] = hn_RECT_cp_annot_noframe
    
    supply [sepref_opt_simps] = ppart_seq1_impl_uncurried_def[symmetric]
    
    
    by sepref (* Takes looooong ~30 sec *)

  context
    notes [fcomp_norm_simps] = list_rel_id_simp
  begin    

    lemmas gpartition_slices_hnr[sepref_fr_rules] = gpartition_slices_impl.refine[FCOMP gpartition_slices2_refine]

  end  
    

  thm ppart_filter_def
  lemma ppart_filter_alt: "ppart_filter m ss bs = ( ss\<inter>{m..}, bs \<inter> {0..<m} )"
    unfolding ppart_filter_def by auto
  
  sepref_def ppart_filter_impl is "uncurry2 (RETURN ooo ppart_filter)" :: "size_assn\<^sup>k *\<^sub>a ivl_assn_sz\<^sup>d *\<^sub>a ivl_assn_sz\<^sup>d \<rightarrow>\<^sub>a ivl_assn_sz \<times>\<^sub>a ivl_assn_sz"
    unfolding ppart_filter_alt
    apply (annot_snat_const "TYPE(size_t)")
    by sepref
    
        
  sepref_register ppart2  
  sepref_def ppart_impl is "uncurry3 (PR_CONST ppart2)" 
    :: "[\<lambda>_. True]\<^sub>c size_assn\<^sup>k *\<^sub>a elem_assn\<^sup>k *\<^sub>a size_assn\<^sup>k *\<^sub>a arr_assn\<^sup>d \<rightarrow> size_assn \<times>\<^sub>a arr_assn [\<lambda>(((_,_),_),xsi) (_,ri). ri=xsi]\<^sub>c"
    unfolding ppart2_def PR_CONST_def
    by sepref

  find_theorems ppart1
    
  thm ppart_impl.refine ppart2_refine  
  (* TODO: Find out what is needed for sorting, and assemble! *)      
  
  sepref_register ppart_partition_pivot_par
  sepref_def ppart_partition_pivot_par_impl is "uncurry2 (PR_CONST ppart_partition_pivot_par)" 
    :: "[\<lambda>_. True]\<^sub>c size_assn\<^sup>k *\<^sub>a arr_assn\<^sup>d *\<^sub>a size_assn\<^sup>k \<rightarrow> arr_assn \<times>\<^sub>a size_assn [\<lambda>((_,xsi),_) (xsi',_). xsi'=xsi]\<^sub>c"
    unfolding ppart_partition_pivot_par_def move_pivot_to_first_sample_def PR_CONST_def
    apply (annot_snat_const "TYPE(size_t)")
    by sepref


  sepref_register ppart_partition_pivot
  sepref_def ppart_partition_pivot_impl is "uncurry2 (PR_CONST ppart_partition_pivot)" 
    :: "[\<lambda>_. True]\<^sub>c size_assn\<^sup>k *\<^sub>a arr_assn\<^sup>d *\<^sub>a size_assn\<^sup>k \<rightarrow> arr_assn \<times>\<^sub>a size_assn [\<lambda>((_,xsi),_) (xsi',_). xsi'=xsi]\<^sub>c"
    unfolding ppart_partition_pivot_def align_chunk_size_def PR_CONST_def
    apply (annot_snat_const "TYPE(size_t)")
    by sepref
    
    
  
end      
    
  
find_consts name: "ll_cmp"

(*
global_interpretation test: sort_impl_copy_context "(\<le>)" "(<)" ll_icmp_ult "unat_assn' TYPE(size_t)" Mreturn free_pure
  defines test_ppart_impl = test.ppart_impl
      and test_ppart_partition_pivot_par_impl = test.ppart_partition_pivot_par_impl
      and test_par_swap_impl = test.par_swap_impl
      and test_gpartition_slices_impl = test.gpartition_slices_impl
      and test_ppart_seq1_impl_uncurried = test.ppart_seq1_impl_uncurried (* TODO: Workaround, as templating seems to choke on llc_par! *)
  apply unfold_locales
  apply (auto simp: mk_free_pure free_pure_def[abs_def])
  apply rule apply sepref
  apply (rule is_copy_pure_gen_algo) apply solve_constraint
  done
  
declare [[llc_compile_par_call=true]]
export_llvm (timing) test_ppart_partition_pivot_par_impl
*)


end
