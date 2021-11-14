theory Sorting_Unguarded_Insertion_Sort
imports Sorting_Setup Sorting_Partially_Sorted
begin


(* TODO: Move *)


  
lemma mop_eo_extract_slice_refine: "\<lbrakk> (i, i') \<in> idx_shift_rel l; (xs, xs') \<in> slice_rel xs\<^sub>0 l h\<rbrakk>
       \<Longrightarrow> mop_eo_extract xs i \<le> \<Down> (Id \<times>\<^sub>r slice_rel xs\<^sub>0 l h) (mop_eo_extract xs' i')"  
  by (auto intro!: refine0 simp: idx_shift_rel_def slice_rel_def in_br_conv take_map drop_map slice_nth slice_upd_sym algebra_simps)
       
  
lemma mop_eo_set_slice_refine: "\<lbrakk>(i, i') \<in> idx_shift_rel l; (xs, xs') \<in> slice_rel xs\<^sub>0 l h; (v,v')\<in>Id\<rbrakk> 
      \<Longrightarrow> mop_eo_set xs i v \<le> \<Down> (slice_rel xs\<^sub>0 l h) (mop_eo_set xs' i' v')"  
  by (auto intro!: refine0 simp: idx_shift_rel_def slice_rel_def in_br_conv take_map drop_map slice_nth slice_upd_sym algebra_simps)
  
lemma mop_to_eo_conv_slice_refine: "\<lbrakk>(xs, xs') \<in> slice_rel xs\<^sub>0 l h; (i, i') \<in> idx_shift_rel l\<rbrakk>
    \<Longrightarrow> mop_to_eo_conv xs \<le> \<Down> (slice_rel (map Some xs\<^sub>0) l h) (mop_to_eo_conv xs')"  
  by (auto simp: idx_shift_rel_def slice_rel_def in_br_conv slice_map take_map drop_map)  
  
lemma mop_to_wo_conv_slice_refine: "\<lbrakk>(xs, xs') \<in> slice_rel (map Some xs\<^sub>0) l h\<rbrakk> \<Longrightarrow> mop_to_wo_conv xs \<le> \<Down> (slice_rel xs\<^sub>0 l h) (mop_to_wo_conv xs')"
  apply simp
  apply (intro refine0)
  subgoal
    apply (simp add: slice_rel_def in_br_conv)
    apply (auto simp: in_set_conv_nth slice_nth list_eq_iff_nth_eq algebra_simps)
    by (metis Groups.add_ac(2) add_diff_inverse_nat less_diff_conv)
  subgoal  
    by (auto simp: slice_rel_def in_br_conv drop_map take_map slice_map)
  done


context weak_ordering begin
  lemma mop_cmp_v_idx_slice_refine: "\<lbrakk> (xs, xs') \<in> slice_rel xs\<^sub>0 l h; (i, i') \<in> idx_shift_rel l; (v,v')\<in>Id \<rbrakk>
    \<Longrightarrow> mop_cmpo_v_idx xs v i \<le> \<Down> bool_rel (mop_cmpo_v_idx xs' v' i')"
    supply [simp del] = conc_Id
    by (auto intro!: refine0 simp: idx_shift_rel_def slice_rel_def in_br_conv slice_nth algebra_simps)
end  



  context weak_ordering begin

  
    definition "is_insert_spec_aux xs i xs' \<equiv> 
      \<exists>i'\<le>i.
        i<length xs
      \<and> (length xs' = length xs) 
      \<and> (\<forall>j\<in>{0..<i'}. xs'!j=xs!j)
      \<and> (xs'!i' = xs!i)
      \<and> (\<forall>j\<in>{i'<..i}. xs'!j = xs!(j-1) \<and> xs!i\<^bold><xs'!j)
      \<and> (\<forall>j\<in>{i<..<length xs}. xs'!j = xs!j)
      \<and> (i'>0 \<longrightarrow> \<not>(xs!i \<^bold>< xs'!(i'-1)) )
      "
      
    lemma is_insert_spec_aux_imp_sorted:
      "\<lbrakk>is_insert_spec_aux xs i xs'; sorted_wrt_lt (\<^bold><) (take i xs)\<rbrakk> 
        \<Longrightarrow> sorted_wrt_lt (\<^bold><) (take (i+1) xs')"  
      (* TODO: Clean up this mess! *)
      apply (subgoal_tac "i<length xs")
      unfolding sorted_wrt_iff_nth_less le_by_lt_def
      subgoal
        apply clarsimp
        unfolding is_insert_spec_aux_def
        apply (clarsimp;safe)
        apply (smt greaterThanAtMost_iff less_trans linorder_neqE_nat nat_Suc_less_le_imp nat_le_Suc_less_imp nz_le_conv_less unfold_lt_to_le zero_order(3))
        by (smt One_nat_def add_diff_cancel_left' atLeast0LessThan greaterThanAtMost_iff itrans le_less lessThan_iff less_Suc_eq_0_disj less_trans linorder_neqE_nat not_less_eq plus_1_eq_Suc unfold_lt_to_le wo_leI)
      subgoal
        using is_insert_spec_aux_def by blast
      done    
    
    definition is_insert :: "bool \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> 'a list nres" where "is_insert GUARDED xs i \<equiv> doN {
      ASSERT ((\<not>GUARDED \<longrightarrow> 0<i) \<and> i<length xs);
      x \<leftarrow> mop_list_get xs i;
    
      (xs,i)\<leftarrow>WHILEIT (\<lambda>(xs',i'). 
        i'\<ge>0 \<and> (\<not>GUARDED \<longrightarrow> i'>0) \<and> i'\<le>i \<and> length xs'=length xs
      \<and> (\<forall>j\<in>{0..i'}. xs'!j = xs!j)  
      \<and> (\<forall>j\<in>{i'<..i}. xs'!j = xs!(j-1) \<and> x\<^bold><xs'!j)  
      \<and> (\<forall>j\<in>{i<..<length xs}. xs'!j=xs!j)
      ) 
        (\<lambda>(xs,i). (GUARDED \<longrightarrow> i>0) \<and> xs!(i-1)\<^bold>>x) (\<lambda>(xs,i). doN {
          ASSERT (i>0 \<and> i<length xs);
          let xs = xs[i:=xs!(i-1)];
          let i = i-1;
          RETURN (xs,i)
        }) (xs,i);
    
      xs \<leftarrow> mop_list_set xs i x;  
      
      RETURN xs
    }"
    
    definition "is_insert_spec GUARDED xs i \<equiv> doN {
      ASSERT (i<length xs \<and> (\<not>GUARDED \<longrightarrow> 0<i \<and> \<not>xs!i\<^bold><xs!0));
      SPEC (is_insert_spec_aux xs i)
    }"  

    text \<open>When unguarded, the first element of the list cannot change\<close>
    lemma is_insert_spec_alt: "is_insert_spec GUARDED xs i = doN {
      ASSERT (i<length xs \<and> (\<not>GUARDED \<longrightarrow> 0<i \<and> \<not>xs!i\<^bold><xs!0));
      SPEC (\<lambda>xs'. is_insert_spec_aux xs i xs' \<and> (\<not>GUARDED \<longrightarrow> xs'!0 = xs!0))
    }"
      unfolding is_insert_spec_def 
      apply (simp only: pw_eq_iff refine_pw_simps; clarsimp; safe)
      unfolding is_insert_spec_aux_def
      apply clarsimp
      by (metis Suc_leI Suc_to_right atLeast0LessThan greaterThanAtMost_iff lessThan_iff not_less_eq)
    
    lemma is_insert_correct: "is_insert GUARDED xs i \<le> is_insert_spec GUARDED xs i"
      unfolding is_insert_def is_insert_spec_def
      apply (refine_vcg WHILEIT_rule[where R="measure snd"])
      apply clarsimp_all
      subgoal by (metis Suc_lessI Suc_to_right)
      subgoal by linarith
      subgoal by (metis Suc_lessI Suc_pred greaterThanAtMost_iff le_less_trans nth_list_update')
    
      subgoal for xs' i'
        unfolding is_insert_spec_aux_def
        apply (rule exI[where x=i']) 
        by auto
        
      done
      
    definition is_insert2 :: "bool \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> 'a list nres" where "is_insert2 GUARDED xs i \<equiv> doN {
      ASSERT ((\<not>GUARDED\<longrightarrow>0<i) \<and> i<length xs);
      
      xs \<leftarrow> mop_to_eo_conv xs;
      
      (x,xs) \<leftarrow> mop_eo_extract xs i;
    
      (xs,i)\<leftarrow>monadic_WHILEIT (\<lambda>(xs',i'). True) 
        (\<lambda>(xs,i). if \<not>GUARDED \<or> i>0 then doN { ASSERT (i>0); mop_cmpo_v_idx xs x (i-1)} else RETURN False) (\<lambda>(xs,i). doN {
          ASSERT (i>0);
          (t,xs) \<leftarrow> mop_eo_extract xs (i-1);
          xs \<leftarrow> mop_eo_set xs i t;
          let i = i-1;
          RETURN (xs,i)
        }) (xs,i);
    
      xs \<leftarrow> mop_eo_set xs i x;  
      
      xs \<leftarrow> mop_to_wo_conv xs;
      
      RETURN xs
    }"
    
    
    definition "ii2_loop_rel \<equiv> {((xs',i'), (xs,i)). i'=i \<and> length xs' = length xs \<and> i<length xs \<and> (\<forall>j\<in>{0..<length xs}-{i}. xs'!j = Some (xs!j)) \<and> xs'!i=None}"
    
    lemma is_insert2_refine: "is_insert2 GUARDED xs i \<le>\<Down>(\<langle>Id\<rangle>list_rel) (is_insert GUARDED xs i)"
      unfolding is_insert2_def is_insert_def
      supply [simp del] = conc_Id
      
      apply simp
      apply (intro refine0; simp)
      apply (rule refine)
      apply (rule monadic_WHILEIT_refine_WHILEIT[where R=ii2_loop_rel])
      subgoal by (auto simp: ii2_loop_rel_def)
      subgoal by simp
      subgoal
        apply (clarsimp split: prod.splits simp: ii2_loop_rel_def)
        apply refine_vcg
        apply (auto)
        done
      subgoal  
        apply clarsimp
        apply refine_vcg
        unfolding ii2_loop_rel_def
        apply (auto simp: nth_list_update split: if_splits)
        done
      subgoal
        apply refine_vcg
        apply (auto simp: ii2_loop_rel_def nth_list_update in_set_conv_nth intro: list_eq_iff_nth_eq[THEN iffD2])  
        done
      done
      
      
    definition "is_insert3 GUARDED xs l i \<equiv> doN {
    
      ASSERT (i<length xs);
      
      xs \<leftarrow> mop_to_eo_conv xs;
      
      (x,xs) \<leftarrow> mop_eo_extract xs i;
    
      (xs,i)\<leftarrow>monadic_WHILEIT (\<lambda>(xs',i'). True) 
        (\<lambda>(xs,i). if \<not>GUARDED \<or> i>l then doN {ASSERT (i>0); mop_cmpo_v_idx xs x (i-1)} else RETURN False) (\<lambda>(xs,i). doN {
          ASSERT (i>0);
          (t,xs) \<leftarrow> mop_eo_extract xs (i-1);
          xs \<leftarrow> mop_eo_set xs i t;
          let i = i-1;
          RETURN (xs,i)
        }) (xs,i);
    
      xs \<leftarrow> mop_eo_set xs i x;  
      
      xs \<leftarrow> mop_to_wo_conv xs;
      
      RETURN xs
    }"
  
    
  lemma is_insert3_refine: "\<lbrakk> (xs,xs')\<in>slice_rel xs\<^sub>0 l h; (i,i')\<in>idx_shift_rel l; i<h \<rbrakk> 
    \<Longrightarrow> is_insert3 GUARDED xs l i \<le>\<Down>(slice_rel xs\<^sub>0 l h) (is_insert2 GUARDED xs' i')"
    unfolding is_insert2_def is_insert3_def
    supply [simp del] = conc_Id
    (*apply (simp cong: if_cong)*)
    supply [refine_dref_RELATES] = 
      RELATESI[of "slice_rel xs\<^sub>0 l h"] 
      RELATESI[of "slice_rel (map Some xs\<^sub>0) l h"] 
      RELATESI[of "slice_rel (map Some xs\<^sub>0) l h \<times>\<^sub>r idx_shift_rel l"] 
    apply (refine_rcg slice_nth_refine' slice_upd_refine' 
      mop_eo_extract_slice_refine mop_eo_set_slice_refine mop_to_eo_conv_slice_refine
      mop_cmp_v_idx_slice_refine mop_to_wo_conv_slice_refine
    )
    apply refine_dref_type
    apply (all \<open>(assumption|simp add: idx_shift_rel_def;simp add: slice_rel_def in_br_conv)?\<close>)
    done

  lemma is_insert3_refine': "\<lbrakk> (xs,xs')\<in>slicep_rel l h; (i,i')\<in>idx_shift_rel l; i<h \<rbrakk> 
    \<Longrightarrow> is_insert3 GUARDED xs l i \<le>\<Down>(slice_rel xs l h) (is_insert2 GUARDED xs' i')"
    unfolding is_insert2_def is_insert3_def
    supply [simp del] = conc_Id
    (*apply (simp cong: if_cong)*)
    supply [refine_dref_RELATES] = 
      RELATESI[of "slicep_rel l h"] 
      RELATESI[of "slice_rel (map Some xs) l h"] 
      RELATESI[of "slice_rel (map Some xs) l h \<times>\<^sub>r idx_shift_rel l"] 
    apply (refine_rcg slice_nth_refine' slice_upd_refine' 
      mop_eo_extract_slice_refine mop_eo_set_slice_refine mop_to_eo_conv_slice_refine
      mop_cmp_v_idx_slice_refine mop_to_wo_conv_slice_refine
    )
    apply refine_dref_type
    apply (all \<open>(assumption|simp add: idx_shift_rel_def;simp add: slice_rel_def slicep_rel_def in_br_conv)?\<close>)
    done
    
  lemma is_insert3_correct: "\<lbrakk> (xs,xs')\<in>slice_rel xs\<^sub>0 l h; (i,i')\<in>idx_shift_rel l; i<h \<rbrakk> 
    \<Longrightarrow> is_insert3 GUARDED xs l i \<le>\<Down>(slice_rel xs\<^sub>0 l h) (is_insert_spec GUARDED xs' i')"
    using is_insert3_refine is_insert2_refine is_insert_correct 
    apply (subgoal_tac "i'<length xs'")
    subgoal by (auto simp: pw_le_iff refine_pw_simps; blast) [] 
    subgoal unfolding slice_rel_def idx_shift_rel_def in_br_conv by auto
    done

  lemma is_insert3_correct': "\<lbrakk> (xs,xs')\<in>slicep_rel l h; (i,i')\<in>idx_shift_rel l; i<h \<rbrakk> 
    \<Longrightarrow> is_insert3 GUARDED xs l i \<le>\<Down>(slice_rel xs l h) (is_insert_spec GUARDED xs' i')"
    using is_insert3_refine' is_insert2_refine is_insert_correct 
    apply (subgoal_tac "i'<length xs'")
    subgoal by (auto simp: pw_le_iff refine_pw_simps; blast) [] 
    subgoal unfolding slice_rel_def slicep_rel_def idx_shift_rel_def in_br_conv by auto
    done
    
        
end
  
context sort_impl_context begin
  sepref_register 
    is_guarded_insert3: "is_insert3 True"
    is_unguarded_insert3: "is_insert3 False"
  
  sepref_def is_guarded_insert_impl is "uncurry2 (PR_CONST (is_insert3 True))" 
    :: "[\<lambda>_. True]\<^sub>c (woarray_slice_assn elem_assn)\<^sup>d *\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k 
      \<rightarrow> woarray_slice_assn elem_assn [\<lambda>((ai,_),_) r. r=ai]\<^sub>c"
    unfolding is_insert3_def PR_CONST_def
    apply (simp named_ss HOL_ss:)
    supply [[goals_limit = 1]]
    apply (annot_snat_const "TYPE(size_t)")
    by sepref

  sepref_def is_unguarded_insert_impl is "uncurry2 (PR_CONST (is_insert3 False))" 
    :: "[\<lambda>_. True]\<^sub>c (woarray_slice_assn elem_assn)\<^sup>d *\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k 
      \<rightarrow> woarray_slice_assn elem_assn [\<lambda>((ai,_),_) r. r=ai]\<^sub>c"
    unfolding is_insert3_def PR_CONST_def
    apply (simp named_ss HOL_ss:)
    supply [[goals_limit = 1]]
    apply (annot_snat_const "TYPE(size_t)")
    by sepref
    

  (* Approximation of what would be generated for pure elements *)      
  thm is_unguarded_insert_impl_def[unfolded eo_extract_impl_def cmpo_v_idx_impl_def, simplified bind_laws split]  
  
  (* For presentation in paper *)
  lemma "is_unguarded_insert_impl \<equiv> \<lambda>xs _ i. doM {
     x \<leftarrow> array_nth xs i;
     (xs, i) \<leftarrow> llc_while (\<lambda>(xs, i). doM {
       bi \<leftarrow> ll_sub i 1;
       t \<leftarrow> array_nth xs bi;
       b \<leftarrow> lt_impl x t;
       array_upd xs bi t;
       return b
     }) (\<lambda>(xs, i). doM {
       i' \<leftarrow> ll_sub i 1;
       t \<leftarrow> array_nth xs i';
       xs \<leftarrow> array_upd xs i t;
       i \<leftarrow> ll_sub i 1;
       return (xs, i)
    })
    (xs, i);
    array_upd xs i x
  }"
    using is_unguarded_insert_impl_def[unfolded M_CONST_def eo_extract_impl_def cmpo_v_idx_impl_def, simplified bind_laws split] 
    by simp
    
end    



context weak_ordering begin

  lemma is_insert_spec_aux_split: "is_insert_spec_aux xs i xs' \<Longrightarrow> (\<exists>i'\<le>i. 
    xs' = take i' xs @ xs!i # drop i' (take i xs) @ drop (i+1) xs \<and> i<length xs)"
    unfolding is_insert_spec_aux_def
    apply clarify
    subgoal for i'
      apply (rule exI[where x=i'])
      apply (simp add: list_eq_iff_nth_eq)
      apply (clarsimp simp: nth_append nth_Cons split: nat.splits)
      apply (safe; clarsimp?)
      subgoal for j k
        by (metis One_nat_def Suc_le_eq add.commute add_Suc_right add_diff_cancel_left' add_diff_inverse_nat greaterThanAtMost_iff less_diff_conv plus_1_eq_Suc zero_less_Suc)
      subgoal by (metis add_Suc leI le_add_diff_inverse2)
      done
    done
    
    
  lemma is_insert_spec_aux_imp_mset_eq:
    assumes A: "is_insert_spec_aux xs i xs'"  
    shows "mset xs' = mset xs"
  proof -
    from A have L: "i<length xs"
      unfolding is_insert_spec_aux_def by blast
  
    from is_insert_spec_aux_split[OF A] obtain i' where
      I': "i'\<le>i" 
      and XS'_EQ: "xs' = take i' xs @ xs ! i # drop i' (take i xs) @ drop (i + 1) xs"
      by blast  
    
    have XS_EQ: "xs = take i' xs @ drop i' (take i xs) @ xs!i # drop (i + 1) xs"  
      using L I'
      apply auto 
      by (metis atd_lem drop_Suc_nth drop_take_drop_unsplit)  
    
    show ?thesis
      apply (rewrite in "\<hole> = _" XS'_EQ)
      apply (rewrite in "_ = \<hole>" XS_EQ)
      by (auto)  
      
  qed    

  
  lemma is_insert_spec_aux_imp_mset_eq':
    assumes A: "is_insert_spec_aux xs i xs'"  
    shows "mset (take (i+1) xs') = mset (take (i+1) xs)"
    using A
  proof -
    from A have L: "i<length xs"
      unfolding is_insert_spec_aux_def by blast
  
    from is_insert_spec_aux_split[OF A] obtain i' where
      I': "i'\<le>i" 
      and "xs' = take i' xs @ xs ! i # drop i' (take i xs) @ drop (i + 1) xs"
      by blast  
    hence XS'_EQ: "take (i+1) xs' = take i' xs @ xs ! i # drop i' (take i xs)" using L
      by (auto simp: take_Cons split: nat.splits)   
      
    have XS_EQ: "take (i+1) xs = take i' xs @ drop i' (take i xs) @ [xs!i]" using L I'
      using L I'
      apply auto
      by (metis append.assoc drop_take le_add_diff_inverse take_Suc_conv_app_nth take_add)        
    
    show ?thesis
      apply (rewrite in "\<hole> = _" XS'_EQ)
      apply (rewrite in "_ = \<hole>" XS_EQ)
      by (auto)  
      
  qed    
  
    
  lemma is_insert_spec_aux_imp_rest_eq:
    assumes A: "is_insert_spec_aux xs i xs'"  
    shows "drop (i+1) xs' = drop (i+1) xs"
    using A unfolding is_insert_spec_aux_def 
    apply (simp add: list_eq_iff_nth_eq)
    by force 

  lemma is_insert_spec_aux_imp_length_eq:
    assumes A: "is_insert_spec_aux xs i xs'"  
    shows "length xs' = length xs"
    using A unfolding is_insert_spec_aux_def 
    by force 
    
      
  definition "sort_one_more_spec GUARDED xs i \<equiv> doN {
      ASSERT (i<length xs \<and> sorted_wrt_lt (\<^bold><) (take i xs));
      ASSERT (\<not>GUARDED \<longrightarrow> 0<i \<and> \<not>xs!i\<^bold><xs!0); 
      SPEC (\<lambda>xs'. mset (take (i+1) xs') = mset (take (i+1) xs) \<and> drop (i+1) xs' = drop (i+1) xs \<and> length xs'=length xs \<and> sorted_wrt_lt (\<^bold><) (take (i+1) xs') \<and> (\<not>GUARDED \<longrightarrow> xs'!0 = xs!0))
    }"  
    
  (* For presentation in paper *)  
  lemma "sort_one_more_spec G xs i = doN {
      ASSERT (i<length xs \<and> sorted_wrt_lt (\<^bold><) (slice 0 i xs));
      ASSERT (G \<or> 0<i \<and> \<not>(xs!i\<^bold><xs!0));
      SPEC (\<lambda>xs'. inres (slice_sort_spec (\<^bold><) xs 0 (i+1)) xs' \<and> (\<not>G \<longrightarrow> xs'!0 = xs!0))
    }"
    unfolding slice_sort_spec_def sort_one_more_spec_def
    apply (simp only: pw_eq_iff refine_pw_simps; safe)
    apply (simp_all add: Misc.slice_def sort_spec_def)
    done
    
  lemma "sort_one_more_spec G xs i = doN {
      ASSERT (i<length xs \<and> sorted_wrt_lt (\<^bold><) (slice 0 i xs));
      ASSERT (G \<or> 0<i \<and> \<not>(xs!i\<^bold><xs!0));
      SPEC (\<lambda>xs'. sort_spec (\<^bold><) (slice 0 (i+1) xs) (slice 0 (i+1) xs') 
          \<and> length xs'=length xs 
          \<and> slice (i+1) (length xs) xs' = slice (i+1) (length xs) xs 
          \<and> (\<not>G \<longrightarrow> xs'!0 = xs!0))
    }"
    unfolding slice_sort_spec_def sort_one_more_spec_def
    apply (simp only: pw_eq_iff refine_pw_simps; safe)
    apply (simp_all add: Misc.slice_def sort_spec_def)
    done
    
    
    
  lemma conv_idxs_to_drop_eq: "length xs = length ys \<Longrightarrow> (\<forall>j\<in>{n..<length ys}. xs ! j = ys ! j) \<longleftrightarrow> drop n xs = drop n ys"
    apply (simp add: list_eq_iff_nth_eq)
    apply (safe;clarsimp)
    by (metis add_diff_cancel_left' diff_less_mono le_iff_add)

    (*
  lemma is_insert_sorts_one_more[param_fo, THEN nres_relD,refine]: 
    "(is_insert_spec GUARDED, sort_one_more_spec GUARDED) 
        \<in> \<langle>Id\<rangle>list_rel \<rightarrow> nat_rel \<rightarrow> \<langle>\<langle>Id\<rangle>list_rel\<rangle>nres_rel"
    apply (intro fun_relI nres_relI; auto)    
    unfolding sort_one_more_spec_def is_insert_spec_alt is_insert_spec_aux_def
    apply (clarsimp simp: pw_le_iff refine_pw_simps)
    apply (intro conjI)
    subgoal sledgehammer sorry
    subgoal apply (simp add: list_eq_iff_nth_eq)
    *)
    
        
  lemma is_insert_sorts_one_more[param_fo, THEN nres_relD,refine]: 
    "(is_insert_spec GUARDED, sort_one_more_spec GUARDED) 
        \<in> \<langle>Id\<rangle>list_rel \<rightarrow> nat_rel \<rightarrow> \<langle>\<langle>Id\<rangle>list_rel\<rangle>nres_rel"
    apply (intro fun_relI nres_relI)    
    using is_insert_spec_aux_imp_sorted is_insert_spec_aux_imp_mset_eq' 
      is_insert_spec_aux_imp_rest_eq is_insert_spec_aux_imp_length_eq
    unfolding sort_one_more_spec_def is_insert_spec_alt
    apply (simp add: pw_le_iff refine_pw_simps)
    apply (auto simp: )
    done

      
  definition "gen_insertion_sort GUARDED i\<^sub>0 h xs \<equiv> doN {
    ASSERT ((\<not>GUARDED \<longrightarrow> 0<i\<^sub>0) \<and> h\<le>length xs);
    (xs,_)\<leftarrow>WHILEIT (\<lambda>(xs',i). 
        i\<^sub>0\<le>i \<and> i\<le>h \<and> length xs'=length xs \<and> mset (take i xs') = mset (take i xs) \<and> drop i xs' = drop i xs \<and> sorted_wrt_lt (\<^bold><) (take i xs')
      \<and> (\<not>GUARDED \<longrightarrow> xs'!0 = xs!0)
      ) 
      (\<lambda>(xs,i). i<h) 
      (\<lambda>(xs,i). doN {
        xs \<leftarrow> sort_one_more_spec GUARDED xs i;
        ASSERT (i<h);
        let i=i+1;
        RETURN (xs,i)
      }) (xs,i\<^sub>0);
    RETURN xs
  }"  
  
    
  lemma gen_insertion_sort_correct: 
    "\<lbrakk>sorted_wrt_lt (\<^bold><) (take i\<^sub>0 xs); \<not>GUARDED \<longrightarrow> 0<i\<^sub>0; i\<^sub>0<h; h\<le>length xs; \<not>GUARDED \<longrightarrow> (\<forall>i\<in>{i\<^sub>0..<h}. \<not>xs!i \<^bold>< xs!0) \<rbrakk> 
      \<Longrightarrow> gen_insertion_sort GUARDED i\<^sub>0 h xs \<le> slice_sort_spec (\<^bold><) xs 0 h"
    unfolding gen_insertion_sort_def sort_one_more_spec_def slice_sort_spec_def sort_spec_def
    apply (refine_vcg 
      WHILEIT_rule[where R="measure (\<lambda>(_,i). length xs - i)"])       
      
    apply (all \<open>(clarsimp;fail)?\<close>) 
    subgoal by clarsimp (metis atLeastLessThan_iff hd_drop_conv_nth less_le_trans)
    subgoal by clarsimp (metis hd_drop_conv_nth less_le_trans take_Suc_conv_app_nth union_code)
    subgoal apply clarsimp by (metis drop_Suc tl_drop)
    subgoal apply simp by force
    subgoal apply simp by (metis Misc.slice_def drop0 drop_take)
    subgoal by (clarsimp simp: Misc.slice_def)    
    done

(*
  
  lemma "\<lbrakk>part_sorted_wrt (le_by_lt (\<^bold><)) n xs; sort_spec (\<^bold><) (slice 0 n xs) (slice 0 n xs'); drop n xs' = drop n xs\<rbrakk> 
    \<Longrightarrow> part_sorted_wrt (le_by_lt (\<^bold><)) n xs'"
    unfolding sort_spec_def
    apply auto
  proof -
    define xs\<^sub>1 where "xs\<^sub>1 = slice 0 n xs"
    define xs\<^sub>2 where "xs\<^sub>2 = drop n xs"
    have "xs = xs\<^sub>1@xs\<^sub>2" unfolding xs\<^sub>1_def xs\<^sub>2_def Misc.slice_def by auto
    thm part_sorted_concatI
  
    
    
    unfolding sort_spec_def
    apply auto
    
    
  oops end end
*)  


      
  definition "gen_insertion_sort2 GUARDED l i h xs \<equiv> doN {
    (xs,_)\<leftarrow>WHILET
      (\<lambda>(xs,i). i<h) 
      (\<lambda>(xs,i). doN {
        xs \<leftarrow> is_insert3 GUARDED xs l i;
        ASSERT (i<h);
        let i=i+1;
        RETURN (xs,i)
      }) (xs,i);
    RETURN xs
  }"  
    
  lemma is_insert3_sorts_one_more: 
    assumes "(xs,xs')\<in>slicep_rel l h" "(i,i')\<in>idx_shift_rel l" "i<h"
    shows "is_insert3 GUARDED xs l i \<le>\<Down>(slice_rel xs l h) (sort_one_more_spec GUARDED xs' i')"
  proof -
    note is_insert3_correct' 
    also note is_insert_sorts_one_more
    finally show ?thesis using assms by simp
  qed

  
  lemma gen_insertion_sort2_refine: 
    "\<lbrakk> (xsi,xs) \<in> slicep_rel l h; (ii,i)\<in>idx_shift_rel l; (ji,j)\<in>idx_shift_rel l \<rbrakk> 
      \<Longrightarrow> gen_insertion_sort2 GUARDED l ii ji xsi \<le>\<Down>(slice_rel xsi l h) (gen_insertion_sort GUARDED i j xs)"
    unfolding gen_insertion_sort_def gen_insertion_sort2_def
    apply (refine_rcg is_insert3_sorts_one_more)
    supply [refine_dref_RELATES] = RELATESI[of "slice_rel xsi l h \<times>\<^sub>r idx_shift_rel l"] 
    apply refine_dref_type
    apply clarsimp_all
    applyS (auto simp: idx_shift_rel_def slice_rel_alt eq_outside_range_triv slicep_rel_def)[]
    applyS (auto simp: idx_shift_rel_def slicep_rel_def)[]
    applyS (auto simp: idx_shift_rel_def slice_rel_alt) []
    applyS (auto simp: idx_shift_rel_def slicep_rel_def)[]
    subgoal
      apply (clarsimp simp: idx_shift_rel_def slice_rel_alt) []
      by (erule (1) eq_outside_range_gen_trans; auto)
    done
  
        
end
    
context sort_impl_context begin
  
  sepref_register 
    unguarded_insertion_sort2: "gen_insertion_sort2 False"
    guarded_insertion_sort2: "gen_insertion_sort2 True"
    
  sepref_def unguarded_insertion_sort_impl is "uncurry3 (PR_CONST (gen_insertion_sort2 False))" 
    :: "[\<lambda>_. True]\<^sub>c size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k *\<^sub>a (woarray_slice_assn elem_assn)\<^sup>d 
      \<rightarrow> woarray_slice_assn elem_assn [\<lambda>(((_,_),_),ai) r. r=ai]\<^sub>c"
    unfolding gen_insertion_sort2_def PR_CONST_def
    apply (annot_snat_const "TYPE(size_t)")
    by sepref
    
  sepref_def guarded_insertion_sort_impl is "uncurry3 (PR_CONST (gen_insertion_sort2 True))" 
    :: "[\<lambda>_. True]\<^sub>c size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k *\<^sub>a (woarray_slice_assn elem_assn)\<^sup>d 
      \<rightarrow> woarray_slice_assn elem_assn [\<lambda>(((_,_),_),ai) r. r=ai]\<^sub>c"
    unfolding gen_insertion_sort2_def PR_CONST_def
    apply (annot_snat_const "TYPE(size_t)")
    by sepref
    
end    

    
context parameterized_weak_ordering begin  

  definition "is_insert_param GUARDED cparam xs l i \<equiv> doN {
  
    ASSERT (i<length xs);
    
    \<^cancel>\<open>ASSERT (set xs \<subseteq> cdom);\<close>
    
    xs \<leftarrow> mop_to_eo_conv xs;
    
    (x,xs) \<leftarrow> mop_eo_extract xs i;

    \<^cancel>\<open>
    ASSERT (x \<in> cdom);
    ASSERT (\<forall>x. Some x \<in> set xs \<longrightarrow> x\<in>cdom);
    \<close>
      
    (xs,i)\<leftarrow>monadic_WHILEIT (\<lambda>(xs',i'). True) 
      (\<lambda>(xs,i). if \<not>GUARDED \<or> i>l then doN {ASSERT (i>0); pcmpo_v_idx2 cparam xs x (i-1)} else RETURN False) (\<lambda>(xs,i). doN {
        ASSERT (i>0);
        (t,xs) \<leftarrow> mop_eo_extract xs (i-1);
        xs \<leftarrow> mop_eo_set xs i t;
        let i = i-1;
        RETURN (xs,i)
      }) (xs,i);
  
    xs \<leftarrow> mop_eo_set xs i x;  
    
    xs \<leftarrow> mop_to_wo_conv xs;
    
    RETURN xs
  }"
  

  term is_insert4
      
  lemma is_insert_param_refine[refine]:
    assumes "(xs',xs)\<in>cdom_list_rel cparam"
    assumes "(l',l)\<in>Id"
    assumes "(i',i)\<in>Id"
    shows "is_insert_param GUARDED cparam xs' l' i' \<le>\<Down>(cdom_list_rel cparam) (WO.is_insert3 cparam GUARDED xs l i)"
    supply [refine_dref_RELATES] = RELATESI[of "cdom_list_rel cparam"] RELATESI[of "cdom_olist_rel cparam"]
    unfolding is_insert_param_def WO.is_insert3_def
    apply refine_rcg
    apply (refine_dref_type)
    using assms
    by (auto simp: cdom_list_rel_alt cdom_olist_rel_alt in_br_conv)
      
  definition "gen_insertion_sort_param GUARDED cparam l i h xs \<equiv> doN {
    (xs,_)\<leftarrow>WHILET
      (\<lambda>(xs,i). i<h) 
      (\<lambda>(xs,i). doN {
        xs \<leftarrow> is_insert_param GUARDED cparam xs l i;
        ASSERT (i<h);
        let i=i+1;
        RETURN (xs,i)
      }) (xs,i);
    RETURN xs
  }"  

  lemma gen_insertion_sort_param_refinep[refine]:
    "\<lbrakk>
      (l',l)\<in>Id; (i',i)\<in>Id; (h',h)\<in>Id; (xs',xs)\<in>cdom_list_rel cparam
    \<rbrakk> \<Longrightarrow> gen_insertion_sort_param GUARDED cparam l' i' h' xs' 
    \<le> \<Down>(cdom_list_rel cparam) (WO.gen_insertion_sort2 cparam GUARDED l i h xs)"
    unfolding gen_insertion_sort_param_def WO.gen_insertion_sort2_def
    supply [refine_dref_RELATES] = RELATESI[of "cdom_list_rel cparam"]
    apply refine_rcg
    apply refine_dref_type
    apply auto
    done

  

end

    
context parameterized_sort_impl_context begin
    
  sepref_register 
    is_guarded_param_insert3: "is_insert_param True"
    is_unguarded_param_insert3: "is_insert_param False"
  
  sepref_def is_guarded_param_insert_impl is "uncurry3 (PR_CONST (is_insert_param True))" 
    :: "[\<lambda>_. True]\<^sub>c cparam_assn\<^sup>k *\<^sub>a wo_assn\<^sup>d *\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k 
      \<rightarrow> wo_assn [\<lambda>(((_,ai),_),_) r. r=ai]\<^sub>c"
    unfolding is_insert_param_def PR_CONST_def
    apply (simp named_ss HOL_ss:)
    supply [[goals_limit = 1]]
    apply (annot_snat_const "TYPE(size_t)")
    by sepref

  sepref_def is_unguarded_param_insert_impl is "uncurry3 (PR_CONST (is_insert_param False))" 
    :: "[\<lambda>_. True]\<^sub>c cparam_assn\<^sup>k *\<^sub>a wo_assn\<^sup>d *\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k 
      \<rightarrow> wo_assn [\<lambda>(((_,ai),_),_) r. r=ai]\<^sub>c"
    unfolding is_insert_param_def PR_CONST_def
    apply (simp named_ss HOL_ss:)
    supply [[goals_limit = 1]]
    apply (annot_snat_const "TYPE(size_t)")
    by sepref
  

    
  sepref_register 
    unguarded_insertion_sort_param: "gen_insertion_sort_param False"
    guarded_insertion_sort_param: "gen_insertion_sort_param True"
    
  sepref_def unguarded_insertion_sort_param_impl is "uncurry4 (PR_CONST (gen_insertion_sort_param False))" 
    :: "[\<lambda>_. True]\<^sub>c cparam_assn\<^sup>k *\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k *\<^sub>a wo_assn\<^sup>d 
      \<rightarrow> wo_assn [\<lambda>((((_,_),_),_),ai) r. r=ai]\<^sub>c"
    unfolding gen_insertion_sort_param_def PR_CONST_def
    apply (annot_snat_const "TYPE(size_t)")
    by sepref
    
  sepref_def guarded_insertion_sort_param_impl is "uncurry4 (PR_CONST (gen_insertion_sort_param True))" 
    :: "[\<lambda>_. True]\<^sub>c cparam_assn\<^sup>k *\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k *\<^sub>a wo_assn\<^sup>d 
      \<rightarrow> wo_assn [\<lambda>((((_,_),_),_),ai) r. r=ai]\<^sub>c"
    unfolding gen_insertion_sort_param_def PR_CONST_def
    apply (annot_snat_const "TYPE(size_t)")
    by sepref
    
end


end
