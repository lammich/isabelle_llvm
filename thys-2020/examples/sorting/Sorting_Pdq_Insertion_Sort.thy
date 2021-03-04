section \<open>Insertion Sorts for PDQ-Sort\<close>
theory Sorting_Pdq_Insertion_Sort
imports Sorting_Setup Sorting_Partially_Sorted
begin

  (* Partially overlapping with Sorting_Unguarded_Insertion_Sort, but the details of the 
    required specs are different enough, such that we decided for the redundancy, rarther than
    trying to find a good generalization.
  *)


  subsection \<open>Insertion Sort\<close>

  subsubsection \<open>Abstract Algorithm\<close>
    
  context weak_ordering begin
    definition "pdq_sort_one_more_spec GUARDED xs l i \<equiv> doN {
      ASSERT (sorted_wrt_lt (\<^bold><) (slice l i xs) \<and> l\<le>i \<and> i<length xs \<and> (\<not>GUARDED \<longrightarrow> 0<l \<and> \<not> xs!(l-1) \<^bold>> xs!i ) );
      SPEC (\<lambda>xs'. slice_eq_mset l (Suc i) xs xs' \<and> sorted_wrt_lt (\<^bold><) (slice l (Suc i) xs'))
    }"
    
  
    definition "pdq_guarded_sort_spec G xs l h \<equiv> doN {
      ASSERT (\<not>G \<longrightarrow> 0<l \<and> (\<forall>x\<in>set (slice l h xs). \<not> x \<^bold>< xs!(l-1)));
      slice_sort_spec (\<^bold><) xs l h
    }"
    
    
    definition pdq_insort where "pdq_insort GUARDED xs\<^sub>0 l h \<equiv> doN {
      ASSERT( l\<le>h \<and> h\<le>length xs\<^sub>0 \<and> (\<not>GUARDED \<longrightarrow> 0<l \<and> (\<forall>x\<in>set (slice l h xs\<^sub>0). \<not> x \<^bold>< xs\<^sub>0!(l-1))));
      
      if l\<noteq>h then doN {
        ASSERT (l<h);
        (_,xs)\<leftarrow>WHILEIT 
          (\<lambda>(i,xs). l<i \<and> i\<le>h \<and> slice_eq_mset l h xs\<^sub>0 xs \<and> sorted_wrt_lt (\<^bold><) (slice l i xs))
          (\<lambda>(i,xs). i<h)
          (\<lambda>(i,xs). doN {
            xs \<leftarrow> pdq_sort_one_more_spec GUARDED xs l i;
            ASSERT (i<h);
            RETURN (i+1,xs)
          })
          (l+1,xs\<^sub>0);
        RETURN xs
      } else RETURN xs\<^sub>0
    }"
  
    
    lemma insort_correct_aux1: "h\<le>length xs \<Longrightarrow> (\<forall>x\<in>set (slice l h xs). \<not> x \<^bold>< k) \<longleftrightarrow> (\<forall>j\<in>{l..<h}. \<not> xs!j \<^bold>< k)"
      by (auto simp: Ball_def set_slice_conv)
    
      
    lemma insort_correct: "pdq_insort G xs l h \<le> pdq_guarded_sort_spec G xs l h"
      unfolding pdq_insort_def slice_sort_spec_sem_alt pdq_guarded_sort_spec_def pdq_sort_one_more_spec_def
      apply (refine_vcg WHILEIT_rule[where R="measure (\<lambda>(i,_). h-i)"])
      apply (clarsimp_all simp: slice_eq_mset_eq_length)
      subgoal 
        apply (subst (asm) slice_eq_mset_nth_outside, assumption)
        apply (auto simp: slice_eq_mset_eq_length) [2]
        apply (simp add: slice_eq_mset_set_inside)
        apply (simp add: insort_correct_aux1 slice_eq_mset_eq_length)
        done
      subgoal by (meson Suc_leI dual_order.refl le_SucI less_imp_le slice_eq_mset_subslice slice_eq_mset_trans) 
      subgoal by simp
      done

     
    definition "pdq_is_insert GUARDED xs\<^sub>0 l i\<^sub>0 \<equiv> doN {
      ASSERT ( l\<le>i\<^sub>0 \<and> i\<^sub>0<length xs\<^sub>0 \<and> (\<not>GUARDED \<longrightarrow> 0<l \<and> \<not>(xs\<^sub>0!(l-1) \<^bold>> xs\<^sub>0!i\<^sub>0)));
      
      tmp \<leftarrow> mop_list_get xs\<^sub>0 i\<^sub>0;
      
      (xs,i)\<leftarrow>WHILEIT 
        (\<lambda>(xs,i). 
            l\<le>i \<and> i\<le>i\<^sub>0
          \<and> eq_outside_range xs\<^sub>0 xs l (i\<^sub>0+1)
          \<and> (\<forall>j\<in>{l..<i}. xs\<^sub>0!j = xs!j)
          \<and> (\<forall>j\<in>{i<..i\<^sub>0}. xs\<^sub>0!(j-1) = xs!j \<and> tmp \<^bold>< xs!j)
          \<and> (\<not>GUARDED \<longrightarrow> i\<ge>1)
        )
        (\<lambda>(xs,i). (\<not>GUARDED \<or> l<i) \<and> tmp \<^bold>< xs!(i-1) )
        (\<lambda>(xs,i). doN {
          ASSERT (i\<ge>1);
          x \<leftarrow> mop_list_get xs (i-1);
          xs \<leftarrow> mop_list_set xs i x;
          RETURN (xs,i-1)
        })
        (xs\<^sub>0,i\<^sub>0);
        
      xs \<leftarrow> mop_list_set xs i tmp;  
        
      RETURN xs
    }"
      
    
    lemma is_insert_aux1: 
      assumes BOUNDS: "l \<le> i" "i \<le> i\<^sub>0" "i\<^sub>0<length xs" "length xs\<^sub>0 = length xs"
      assumes PRFX_EQ: "\<forall>j\<in>{l..<i}. xs\<^sub>0 ! j = xs ! j"
      assumes SFX_SHIFT: "\<forall>j\<in>{i<..i\<^sub>0}. xs\<^sub>0 ! (j - Suc 0) = xs ! j \<and> xs\<^sub>0!i\<^sub>0 \<^bold>< xs!j"
      assumes SORTED: "sorted_wrt_lt (\<^bold><) (slice l i\<^sub>0 xs\<^sub>0)"
      assumes GUARD: "l < i \<longrightarrow> \<not> xs\<^sub>0 ! i\<^sub>0 \<^bold>< xs ! (i - Suc 0)"
      shows "mset (slice l (Suc i\<^sub>0) xs\<^sub>0) = mset (slice l (Suc i\<^sub>0) (xs[i := xs\<^sub>0 ! i\<^sub>0]))"
        and "sorted_wrt_lt (\<^bold><) (slice l (Suc i\<^sub>0) (xs[i := xs\<^sub>0 ! i\<^sub>0]))"
    proof -
      define sxs\<^sub>0 where "sxs\<^sub>0 = slice l (Suc i\<^sub>0) xs\<^sub>0"
      define sxs' where "sxs' = slice l (Suc i\<^sub>0) (xs[i := xs\<^sub>0 ! i\<^sub>0])" 
      
      
      have "slice l i\<^sub>0 xs\<^sub>0 = butlast sxs\<^sub>0"
        unfolding sxs\<^sub>0_def using BOUNDS
        by (simp add: slice_Suc_conv)
    
      with SORTED have SORTED': "sorted_wrt_lt (\<^bold><) (butlast sxs\<^sub>0)" by simp 
        
      have [simp]: "length sxs\<^sub>0 = length sxs'"
        unfolding sxs'_def sxs\<^sub>0_def using BOUNDS 
        by (auto)
        
      have [simp]: "length sxs' = i\<^sub>0+1-l"  
        unfolding sxs'_def using BOUNDS 
        by (auto)
        
      
      from PRFX_EQ have 1: "\<forall>j\<in>{0..<i-l}. sxs\<^sub>0 ! j = sxs' ! j"
        unfolding sxs'_def sxs\<^sub>0_def using BOUNDS 
        by (auto simp: slice_nth)
        
      from SFX_SHIFT have 2: "\<forall>j\<in>{i-l..<i\<^sub>0-l}. sxs\<^sub>0 ! j = sxs' ! (j + 1)"
        unfolding sxs'_def sxs\<^sub>0_def using BOUNDS 
        apply (auto simp: slice_nth)
        by (smt One_nat_def Suc_leI add.commute add_Suc_right diff_add_inverse greaterThanAtMost_iff le_add_diff_inverse le_imp_less_Suc less_diff_conv plus_1_eq_Suc)
        
      have 3: "sxs\<^sub>0!(i\<^sub>0-l) = sxs'!(i-l)" 
        unfolding sxs'_def sxs\<^sub>0_def using BOUNDS 
        by (auto simp: slice_nth)

      have A: "sxs\<^sub>0 = take (i-l) sxs' @ drop (i-l+1) sxs' @ [sxs'!(i-l)]"  
        apply (subst list_eq_iff_nth_eq) using BOUNDS
        apply (auto simp: nth_append 1 2 3)
        by (metis "3" add_diff_cancel_right' leI le_add_diff_inverse2 less_antisym less_diff_conv)
        
      have B: "sxs' = take (i-l) sxs' @ sxs'!(i-l) # drop (i-l+1) sxs'"
        using BOUNDS by (auto simp: id_take_nth_drop)
      
      show "mset sxs\<^sub>0 = mset sxs'"  
        apply (rewrite in "mset \<hole> = _" A)
        apply (rewrite in "_ = mset \<hole>" B)
        by simp

      from SFX_SHIFT have S: "\<forall>j\<in>{i-l..<i\<^sub>0-l}. sxs' ! (i-l) \<^bold>< sxs' ! (j+1)"
        unfolding sxs'_def sxs\<^sub>0_def using BOUNDS 
        by (auto simp: slice_nth nth_list_update less_diff_conv)
        
      from GUARD have GUARD': "i=l \<or> \<not> sxs'!(i-l) \<^bold>< sxs'!(i-Suc 0-l)"
        unfolding sxs'_def sxs\<^sub>0_def using BOUNDS 
        by (auto simp: slice_nth)
        
      show "sorted_wrt_lt (\<^bold><) sxs'"  
        apply (rewrite B)
        apply (rule sorted_lelI)
        
        using SORTED'[unfolded A]
        apply (auto simp add: sorted_wrt_append butlast_append le_by_lt)
        subgoal
          using GUARD'
          by (simp add: add.commute BOUNDS last_take_nth_conv le_imp_less_Suc less_diff_conv less_imp_le_nat wo_leI)
        subgoal premises prems
          using S prems(1) by (auto simp: in_set_conv_nth unfold_lt_to_le)
        done
        
    qed
    
    lemma pdq_is_insert_correct: "pdq_is_insert G xs\<^sub>0 l i\<^sub>0 \<le> pdq_sort_one_more_spec G xs\<^sub>0 l i\<^sub>0"
      unfolding pdq_is_insert_def pdq_sort_one_more_spec_def
      apply (refine_vcg WHILEIT_rule[where R="measure (\<lambda>(_,i). i)"])
      apply simp_all
      apply (all \<open>(elim conjE)?\<close>)
      apply (simp_all add: slice_eq_mset_eq_length eq_outside_rane_lenD eq_outside_range_triv) 
      apply clarsimp_all
      subgoal 
        by (metis One_nat_def eq_outside_range_def last_take_nth_conv le_less_trans less_le nat_le_Suc_less_imp)
      subgoal by (simp add: eq_outside_erange_upd_inside)
      subgoal
        apply (clarsimp simp: nth_list_update)
        by (metis One_nat_def atLeastLessThan_iff eq_outside_range_def last_take_nth_conv le_neq_implies_less less_not_refl2 nat_le_Suc_less_imp nat_minus1_less_if_neZ order_trans)
      subgoal
        by (metis One_nat_def Suc_leI diff_0_eq_0 diff_is_0_eq eq_outside_range_def last_take_nth_conv le_antisym not_less_eq_eq)  
      subgoal for xs i
        apply (thin_tac "\<not>G \<longrightarrow> _")+
        apply (clarsimp simp: slice_eq_mset_alt)
        apply (intro conjI)
        apply (auto simp: eq_outside_erange_upd_inside eq_outside_rane_lenD intro!: is_insert_aux1)
        done
      subgoal for xs i
        apply (thin_tac "\<not>G \<longrightarrow> _")+
        apply (auto simp: eq_outside_rane_lenD intro!: is_insert_aux1)
        done
      done    


      
    subsubsection \<open>Loop unrolling Optimization\<close>
    text \<open>Avoid move from/to temporary variable when the element is already at correct position.\<close>
            
    definition "pdq_is_insert' GUARDED xs l i \<equiv> doN {
      ASSERT ( l\<le>i \<and> i<length xs \<and> (\<not>GUARDED \<longrightarrow> i\<ge>1));
      if ((\<not>GUARDED \<or> l<i) \<and> xs!i \<^bold>< xs!(i-1)) then doN {
        tmp \<leftarrow> mop_list_get xs i;
        ASSERT (i\<ge>1);
        x \<leftarrow> mop_list_get xs (i-1);
        xs \<leftarrow> mop_list_set xs i x;
        (xs,i)\<leftarrow>WHILEIT (\<lambda>(xs,i). \<not>GUARDED \<longrightarrow> i\<ge>1)
          (\<lambda>(xs,i). (\<not>GUARDED \<or> l<i) \<and> tmp \<^bold>< xs!(i-1) )
          (\<lambda>(xs,i). doN {
            ASSERT (i\<ge>1);
            x \<leftarrow> mop_list_get xs (i-1);
            xs \<leftarrow> mop_list_set xs i x;
            RETURN (xs,i-1)
          })
          (xs,i-1);
        
        xs \<leftarrow> mop_list_set xs i tmp;
        RETURN xs
      } else RETURN xs
    }"
      
    
    lemma pdq_is_insert'_refine: "pdq_is_insert' G xs l i \<le> pdq_is_insert G xs l i"
      unfolding pdq_is_insert_def
      
      apply (rewrite WHILEIT_unfold')
      unfolding pdq_is_insert'_def
      supply if_split[split del]
      apply (cases "(\<not> G \<or> l < i) \<and> xs ! i \<^bold>< xs ! (i - 1)"; simp only:; simp)
      subgoal
        apply (rule refine_IdD)
        apply refine_vcg
        apply refine_dref_type
        apply (clarsimp_all simp only: list_rel_id_simp prod_rel_id_simp IdI)
        apply simp_all
        done
      subgoal
        by (simp add: pw_le_iff refine_pw_simps split!: if_splits)
      done
      
      
      
    subsection \<open>Maybe Insertion Sort\<close>  
    text \<open>Will stop sorting after a few swaps\<close>
    abbreviation "partial_insertion_sort_limit \<equiv> 8::nat"

    
    subsubsection \<open>Abstract Algorithm\<close>
    definition "maybe_sort_spec xs l h \<equiv> doN {
      ASSERT (l\<le>h \<and> h\<le>length xs);
      SPEC (\<lambda>(r,xs'). slice_eq_mset l h xs xs' \<and> (r \<longrightarrow> sorted_wrt_lt (\<^bold><) (slice l h xs')))
    }"
      
    definition "maybe_sort_one_more_spec xs l i \<equiv> doN {
      ASSERT (sorted_wrt_lt (\<^bold><) (slice l i xs) \<and> l\<le>i \<and> i<length xs );
      SPEC (\<lambda>(d,xs'). slice_eq_mset l (Suc i) xs xs' \<and> d\<le>i-l \<and> sorted_wrt_lt (\<^bold><) (slice l (Suc i) xs'))
    }"
    
    
    
    definition maybe_insort where "maybe_insort xs\<^sub>0 l h \<equiv> doN {
      ASSERT( l\<le>h \<and> h\<le>length xs\<^sub>0 );
      
      if l\<noteq>h then doN {
        ASSERT (l<h);
        (i,_,xs)\<leftarrow>WHILEIT 
          (\<lambda>(i,nc,xs). 
            l<i \<and> i\<le>h 
            \<and> slice_eq_mset l h xs\<^sub>0 xs 
            \<and> sorted_wrt_lt (\<^bold><) (slice l i xs))
          (\<lambda>(i,nc,xs). i<h \<and> nc>0)
          (\<lambda>(i,nc,xs). doN {
            (d,xs) \<leftarrow> maybe_sort_one_more_spec xs l i;
            
            let nc = (if d<nc then nc-d else 0);
            ASSERT (i<h);
            RETURN (i+1,nc,xs)
          })
          (l+1,partial_insertion_sort_limit+1,xs\<^sub>0);
        RETURN (i=h,xs)
      } else RETURN (True,xs\<^sub>0)
    }"
      
                                  
    lemma maybe_insort_correct: "maybe_insort xs l h \<le> maybe_sort_spec xs l h"
      unfolding maybe_insort_def maybe_sort_spec_def maybe_sort_one_more_spec_def
      apply (refine_vcg WHILEIT_rule[where R="measure (\<lambda>(i,_). h-i)"])
      apply (clarsimp_all simp: slice_eq_mset_eq_length)
      subgoal by (meson Suc_leI dual_order.refl le_SucI less_imp_le slice_eq_mset_subslice slice_eq_mset_trans) 
      subgoal by simp
      done

      
      
    definition "maybe_is_insert xs\<^sub>0 l i\<^sub>0 \<equiv> doN {
      ASSERT ( l\<le>i\<^sub>0 \<and> i\<^sub>0<length xs\<^sub>0);
      
      tmp \<leftarrow> mop_list_get xs\<^sub>0 i\<^sub>0;
      
      (xs,i)\<leftarrow>WHILEIT 
        (\<lambda>(xs,i). 
            l\<le>i \<and> i\<le>i\<^sub>0
          \<and> eq_outside_range xs\<^sub>0 xs l (i\<^sub>0+1)
          \<and> (\<forall>j\<in>{l..<i}. xs\<^sub>0!j = xs!j)
          \<and> (\<forall>j\<in>{i<..i\<^sub>0}. xs\<^sub>0!(j-1) = xs!j \<and> tmp \<^bold>< xs!j)
        )
        (\<lambda>(xs,i). l<i \<and> tmp \<^bold>< xs!(i-1) )
        (\<lambda>(xs,i). doN {
          ASSERT (i\<ge>1);
          x \<leftarrow> mop_list_get xs (i-1);
          xs \<leftarrow> mop_list_set xs i x;
          RETURN (xs,i-1)
        })
        (xs\<^sub>0,i\<^sub>0);
        
      xs \<leftarrow> mop_list_set xs i tmp;  
        
      ASSERT (i\<le>i\<^sub>0);
      RETURN (i\<^sub>0-i,xs)
    }"
      
      
    lemma maybe_is_insert_correct: "maybe_is_insert xs\<^sub>0 l i\<^sub>0 \<le> maybe_sort_one_more_spec xs\<^sub>0 l i\<^sub>0"
      unfolding maybe_is_insert_def maybe_sort_one_more_spec_def
      apply (refine_vcg WHILEIT_rule[where R="measure (\<lambda>(_,i). i)"])
      apply simp_all
      apply (all \<open>(elim conjE)?\<close>)
      apply (simp_all add: slice_eq_mset_eq_length eq_outside_rane_lenD eq_outside_range_triv) 
      apply clarsimp_all
      subgoal by (simp add: eq_outside_erange_upd_inside)
      subgoal
        by (auto simp: nth_list_update)
      subgoal for xs i
        apply (clarsimp simp: slice_eq_mset_alt)
        apply (intro conjI)
        apply (auto simp: eq_outside_erange_upd_inside eq_outside_rane_lenD intro: is_insert_aux1)
        done
      subgoal for xs i
        apply (auto simp: eq_outside_rane_lenD intro: is_insert_aux1)
        done
      done    
      

    subsubsection \<open>Loop Unrolling Optimization\<close>  
            
    definition "maybe_is_insert' xs l i\<^sub>0 \<equiv> doN {
      let i = i\<^sub>0;
      ASSERT ( l\<le>i \<and> i<length xs);

      if (l<i \<and> xs!i \<^bold>< xs!(i-1)) then doN {
        tmp \<leftarrow> mop_list_get xs i;
        
        ASSERT (i\<ge>1);
        x \<leftarrow> mop_list_get xs (i-1);
        xs \<leftarrow> mop_list_set xs i x;
        
        (xs,i)\<leftarrow>WHILET 
          (\<lambda>(xs,i). l<i \<and> tmp \<^bold>< xs!(i-1) )
          (\<lambda>(xs,i). doN {
            ASSERT (i\<ge>1);
            x \<leftarrow> mop_list_get xs (i-1);
            xs \<leftarrow> mop_list_set xs i x;
            RETURN (xs,i-1)
          })
          (xs,i-1);
          
        xs \<leftarrow> mop_list_set xs i tmp;  
        ASSERT (i\<le>i\<^sub>0);
        RETURN (i\<^sub>0-i,xs)
      } else RETURN (0,xs)
    }"
      
      
    lemma maybe_is_insert'_refine: "maybe_is_insert' xs l i \<le> maybe_is_insert xs l i"
      unfolding maybe_is_insert_def
      
      apply (rewrite WHILEIT_unfold')
      unfolding maybe_is_insert'_def Let_def
      supply if_split[split del]
      apply (cases "l < i \<and> xs ! i \<^bold>< xs ! (i - 1)"; simp only:; simp)
      subgoal
        apply (rule refine_IdD)
        apply refine_vcg
        apply refine_dref_type
        apply (clarsimp_all simp only: list_rel_id_simp prod_rel_id_simp IdI)
        apply simp_all
        done
      subgoal
        by (simp add: pw_le_iff refine_pw_simps split!: if_splits)
      done
      

  subsection \<open>Refinements to Explicit Ownership\<close>      
      
    definition "pdq_is_insert2' GUARDED xs l i \<equiv> doN {
      xs \<leftarrow> mop_to_eo_conv xs;
      
      if\<^sub>N (if (\<not>GUARDED \<or> l<i) then doN { ASSERT (i\<ge>1); mop_cmpo_idxs xs i (i-1) } else RETURN False) then doN {
      
        (tmp,xs) \<leftarrow> mop_eo_extract xs i;

        ASSERT (i\<ge>1);
        (x,xs) \<leftarrow> mop_eo_extract xs (i-1);
        xs \<leftarrow> mop_eo_set xs i x;
                
        (xs,i)\<leftarrow>monadic_WHILEIT 
          (\<lambda>_. True)
          (\<lambda>(xs,i). if (\<not>GUARDED \<or> l<i) then doN { ASSERT (i\<ge>1); mop_cmpo_v_idx xs tmp (i-1) } else RETURN False )
          (\<lambda>(xs,i). doN {
            ASSERT (i>0);
            (x,xs) \<leftarrow> mop_eo_extract xs (i-1);
            xs \<leftarrow> mop_eo_set xs i x;
            RETURN (xs,i-1)
          })
          (xs,i-1);
        xs \<leftarrow> mop_eo_set xs i tmp;  
        xs \<leftarrow> mop_to_wo_conv xs;
        RETURN xs
      } else mop_to_wo_conv xs
    }"
      
    definition "pdq_ii2_loop_rel \<equiv> {((xs',i'), (xs,i)). i'=i \<and> length xs' = length xs \<and> i<length xs \<and> (\<forall>j\<in>{0..<length xs}-{i}. xs'!j = Some (xs!j)) \<and> xs'!i=None}"
    
    lemma pdq_is_insert2'_refine: "pdq_is_insert2' G xs l i \<le>\<Down>(\<langle>Id\<rangle>list_rel) (pdq_is_insert' G xs l i)"
    proof -
    
      have 1: "mop_cmpo_idxs (map Some xs) i (i - 1) = doN { ASSERT (i<length xs); RETURN (xs!i \<^bold>< xs!(i-1)) }"
        by (auto simp: pw_eq_iff refine_pw_simps)
      
      show ?thesis
        unfolding pdq_is_insert2'_def pdq_is_insert'_def
        supply [simp del] = conc_Id
        supply [split del] = if_split
        apply (
          cases "\<not> G \<or> l < i"; 
          simp named_ss HOL_ss: split del: if_split;
          cases "xs ! i \<^bold>< xs ! (i - 1)"; 
          simp named_ss HOL_ss: mop_to_eo_conv_def nres_monad_laws 1 split del: if_split)
        subgoal 
          apply (intro refine0; simp)
          apply linarith
          apply (rule refine)
          apply (rule refine)
          apply blast
          apply (rule refine)
          apply (rule monadic_WHILEIT_refine_WHILEIT[where R=pdq_ii2_loop_rel])
          subgoal by (auto simp: pdq_ii2_loop_rel_def nth_list_update split: if_splits)
          subgoal by simp
          subgoal
            apply (thin_tac "G \<longrightarrow> _")+
            apply (clarsimp split: prod.splits if_splits simp: pdq_ii2_loop_rel_def)
            apply refine_vcg
            apply (auto) 
            done
          subgoal  
            apply (thin_tac "G \<longrightarrow> _")+
            apply clarsimp
            apply refine_vcg
            unfolding pdq_ii2_loop_rel_def
            apply (auto simp: nth_list_update split: if_splits)
            done
          subgoal
            apply (thin_tac "G \<longrightarrow> _")+
            apply refine_vcg
            apply (auto simp: pdq_ii2_loop_rel_def nth_list_update in_set_conv_nth split: if_split intro: list_eq_iff_nth_eq[THEN iffD2])  
            done
          done
        subgoal by refine_rcg auto
        subgoal by refine_rcg auto
        subgoal by refine_rcg auto
        done
    qed  
      
    definition "pdq_is_insert2 GUARDED xs\<^sub>0 l i\<^sub>0 \<equiv> doN {
      xs \<leftarrow> mop_to_eo_conv xs\<^sub>0;
      
      (tmp,xs) \<leftarrow> mop_eo_extract xs i\<^sub>0;
      
      (xs,i)\<leftarrow>monadic_WHILEIT 
        (\<lambda>(xs,i). True
        )
        (\<lambda>(xs,i). if (\<not>GUARDED \<or> l<i) then doN { ASSERT (i>0); mop_cmpo_v_idx xs tmp (i-1) } else RETURN False )
        (\<lambda>(xs,i). doN {
          ASSERT (i>0);
          (x,xs) \<leftarrow> mop_eo_extract xs (i-1);
          xs \<leftarrow> mop_eo_set xs i x;
          RETURN (xs,i-1)
        })
        (xs,i\<^sub>0);
        
      xs \<leftarrow> mop_eo_set xs i tmp;  
        
      xs \<leftarrow> mop_to_wo_conv xs;
      
      RETURN xs
    }"
      
    lemma pdq_is_insert2_refine: "pdq_is_insert2 G xs l i \<le>\<Down>(\<langle>Id\<rangle>list_rel) (pdq_is_insert G xs l i)"
      unfolding pdq_is_insert2_def pdq_is_insert_def
      supply [simp del] = conc_Id
      
      apply simp
      apply (intro refine0; simp)
      apply (rule refine)
      apply (rule monadic_WHILEIT_refine_WHILEIT[where R=pdq_ii2_loop_rel])
      subgoal by (auto simp: pdq_ii2_loop_rel_def)
      subgoal by simp
      subgoal
        apply (clarsimp split: prod.splits simp: pdq_ii2_loop_rel_def)
        apply refine_vcg
        apply (auto)
        done
      subgoal  
        apply clarsimp
        apply refine_vcg
        unfolding pdq_ii2_loop_rel_def
        apply (auto simp: nth_list_update split: if_splits)
        done
      subgoal
        apply refine_vcg
        apply (auto simp: pdq_ii2_loop_rel_def nth_list_update in_set_conv_nth intro: list_eq_iff_nth_eq[THEN iffD2])  
        done
      done
      

      
    definition "maybe_is_insert2 xs\<^sub>0 l i\<^sub>0 \<equiv> doN {
      ASSERT ( l\<le>i\<^sub>0 \<and> i\<^sub>0<length xs\<^sub>0);

      xs \<leftarrow> mop_to_eo_conv xs\<^sub>0;
            
      (tmp,xs) \<leftarrow> mop_eo_extract xs i\<^sub>0;
      
      (xs,i)\<leftarrow>monadic_WHILEIT 
        (\<lambda>(xs,i). True)
        (\<lambda>(xs,i). if l<i then doN { ASSERT (i>0); mop_cmpo_v_idx xs tmp (i-1) } else RETURN False )
        (\<lambda>(xs,i). doN {
          ASSERT (i>0);
          (x,xs) \<leftarrow> mop_eo_extract xs (i-1);
          xs \<leftarrow> mop_eo_set xs i x;
          RETURN (xs,i-1)
        })
        (xs,i\<^sub>0);
        
      xs \<leftarrow> mop_eo_set xs i tmp;  
      
      xs \<leftarrow> mop_to_wo_conv xs;
        
      ASSERT (i\<le>i\<^sub>0);
      RETURN (i\<^sub>0-i,xs)
    }"
      
    lemma maybe_is_insert2_refine: "maybe_is_insert2 xs l i \<le>\<Down>(Id \<times>\<^sub>r \<langle>Id\<rangle>list_rel) (maybe_is_insert xs l i)"
      unfolding maybe_is_insert2_def maybe_is_insert_def
      supply [simp del] = conc_Id
      
      apply simp
      apply (intro refine0; simp)
      apply (rule refine)
      apply (rule monadic_WHILEIT_refine_WHILEIT[where R=pdq_ii2_loop_rel])
      subgoal by (auto simp: pdq_ii2_loop_rel_def)
      subgoal by simp
      subgoal
        apply (clarsimp split: prod.splits simp: pdq_ii2_loop_rel_def)
        apply refine_vcg
        apply (auto)
        done
      subgoal  
        apply clarsimp
        apply refine_vcg
        unfolding pdq_ii2_loop_rel_def
        apply (auto simp: nth_list_update split: if_splits)
        done
      subgoal
        apply refine_vcg
        apply (auto simp: pdq_ii2_loop_rel_def nth_list_update in_set_conv_nth intro: list_eq_iff_nth_eq[THEN iffD2])  
        done
      done

      
    definition "maybe_is_insert2' xs l i\<^sub>0 \<equiv> doN {
      let i=i\<^sub>0;
      ASSERT ( l\<le>i \<and> i<length xs);
      xs \<leftarrow> mop_to_eo_conv xs;
      
      if\<^sub>N (if l<i then doN { ASSERT (i>0); mop_cmpo_idxs xs i (i-1) } else RETURN False) then doN {
        (tmp,xs) \<leftarrow> mop_eo_extract xs i\<^sub>0;
        
        ASSERT (i\<ge>1);
        (x,xs) \<leftarrow> mop_eo_extract xs (i-1);
        xs \<leftarrow> mop_eo_set xs i x;
        
        (xs,i)\<leftarrow>monadic_WHILEIT 
          (\<lambda>_. True)
          (\<lambda>(xs,i). if l<i then doN { ASSERT (i\<ge>1); mop_cmpo_v_idx xs tmp (i-1) } else RETURN False )
          (\<lambda>(xs,i). doN {
            ASSERT (i\<ge>1);
            (x,xs) \<leftarrow> mop_eo_extract xs (i-1);
            xs \<leftarrow> mop_eo_set xs i x;
            RETURN (xs,i-1)
          })
          (xs,i-1);
          
        xs \<leftarrow> mop_eo_set xs i tmp;  
        xs \<leftarrow> mop_to_wo_conv xs;
          
        ASSERT (i\<le>i\<^sub>0);
        RETURN (i\<^sub>0-i,xs)
      } else doN {
        xs \<leftarrow> mop_to_wo_conv xs;
        RETURN (0,xs)
      }
    }"
      
    lemma maybe_is_insert2'_refine: "maybe_is_insert2' xs l i \<le>\<Down>(Id \<times>\<^sub>r \<langle>Id\<rangle>list_rel) (maybe_is_insert' xs l i)"
    proof -
      have 1: "mop_cmpo_idxs (map Some xs) i (i - 1) = doN { ASSERT (i<length xs); RETURN (xs!i \<^bold>< xs!(i-1)) }"
        by (auto simp: pw_eq_iff refine_pw_simps)
    
      show ?thesis
        unfolding maybe_is_insert2'_def maybe_is_insert'_def Let_def
        supply [simp del] = conc_Id
        supply [split del] = if_split
        apply (
          cases "l < i"; 
          simp named_ss HOL_ss: split del: if_split;
          cases "xs ! i \<^bold>< xs ! (i - 1)"; 
          simp named_ss HOL_ss: mop_to_eo_conv_def nres_monad_laws 1 split del: if_split)
          
        subgoal 
          apply (intro refine0; simp)
          apply (intro refine0; simp)
          apply (rule refine)
          apply (rule monadic_WHILEIT_refine_WHILET[where R=pdq_ii2_loop_rel])
          subgoal by (auto simp: pdq_ii2_loop_rel_def nth_list_update split: if_splits)
          subgoal
            apply (clarsimp split: prod.splits simp: pdq_ii2_loop_rel_def split: if_split)
            apply refine_vcg
            apply (auto)
            done
          subgoal  
            apply clarsimp
            apply refine_vcg
            unfolding pdq_ii2_loop_rel_def
            apply (auto simp: nth_list_update split: if_splits)
            done
          subgoal
            apply refine_vcg
            apply (auto simp: pdq_ii2_loop_rel_def nth_list_update in_set_conv_nth split: if_splits intro: list_eq_iff_nth_eq[THEN iffD2])  
            done
          done
        subgoal by refine_rcg auto
        subgoal by refine_rcg auto
        subgoal by refine_rcg auto
        done
        
    qed
                        
  end

  
subsection \<open>Refinement to Isabelle-LLVM\<close>  
  
context sort_impl_context begin
  sepref_register 
    pdq_is_guarded_insert3: "pdq_is_insert2 True"
    pdq_is_unguarded_insert3: "pdq_is_insert2 False"
    maybe_is_insert3: "maybe_is_insert2"
  
  sepref_def pdq_is_guarded_insert_impl [llvm_inline] is "uncurry2 (PR_CONST (pdq_is_insert2' True))" 
    :: "(woarray_assn elem_assn)\<^sup>d *\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k \<rightarrow>\<^sub>a woarray_assn elem_assn"
    unfolding pdq_is_insert2'_def PR_CONST_def
    apply (simp named_ss HOL_ss:)
    supply [[goals_limit = 1]]
    apply (annot_snat_const "TYPE(size_t)")
    by sepref

  sepref_def pdq_is_unguarded_insert_impl [llvm_inline] is "uncurry2 (PR_CONST (pdq_is_insert2' False))" 
    :: "(woarray_assn elem_assn)\<^sup>d *\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k \<rightarrow>\<^sub>a woarray_assn elem_assn"
    unfolding pdq_is_insert2'_def PR_CONST_def
    apply (simp named_ss HOL_ss:)
    supply [[goals_limit = 1]]
    apply (annot_snat_const "TYPE(size_t)")
    by sepref

  sepref_def maybe_is_insert_impl [llvm_inline] is "uncurry2 (PR_CONST maybe_is_insert2')" 
    :: "(woarray_assn elem_assn)\<^sup>d *\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k \<rightarrow>\<^sub>a size_assn \<times>\<^sub>a woarray_assn elem_assn"
    unfolding maybe_is_insert2'_def PR_CONST_def
    supply [[goals_limit = 1]]
    apply (annot_snat_const "TYPE(size_t)")
    by sepref
    

  sepref_register 
    pdq_is_guarded_som: "pdq_sort_one_more_spec True"
    pdq_is_unguarded_som: "pdq_sort_one_more_spec False"
    maybe_sort_one_more_spec
    
   lemma pdq_is_insert2_refine': "(PR_CONST (pdq_is_insert2 G), PR_CONST (pdq_sort_one_more_spec G))\<in>Id \<rightarrow> Id \<rightarrow> Id \<rightarrow> \<langle>Id\<rangle>nres_rel"
   proof -
     note pdq_is_insert2_refine also note pdq_is_insert_correct 
     finally show ?thesis by (auto intro!: nres_relI) 
   qed

   lemma pdq_is_insert2'_refine': "(PR_CONST (pdq_is_insert2' G), PR_CONST (pdq_sort_one_more_spec G))\<in>Id \<rightarrow> Id \<rightarrow> Id \<rightarrow> \<langle>Id\<rangle>nres_rel"
   proof -
     note pdq_is_insert2'_refine also note pdq_is_insert'_refine also note pdq_is_insert_correct 
     finally show ?thesis by (auto intro!: nres_relI) 
   qed
   
   lemma maybe_is_insert2_refine': "(PR_CONST (maybe_is_insert2), PR_CONST (maybe_sort_one_more_spec))\<in>Id \<rightarrow> Id \<rightarrow> Id \<rightarrow> \<langle>Id\<rangle>nres_rel"
   proof -
     note maybe_is_insert2_refine also note maybe_is_insert_correct 
     finally show ?thesis by (auto intro!: nres_relI) 
   qed
      
   lemma maybe_is_insert2'_refine': "(PR_CONST (maybe_is_insert2'), PR_CONST (maybe_sort_one_more_spec))\<in>Id \<rightarrow> Id \<rightarrow> Id \<rightarrow> \<langle>Id\<rangle>nres_rel"
   proof -
     note maybe_is_insert2'_refine also note maybe_is_insert'_refine also note maybe_is_insert_correct 
     finally show ?thesis by (auto intro!: nres_relI) 
   qed
   
     
   lemmas [sepref_fr_rules] = 
     pdq_is_unguarded_insert_impl.refine[FCOMP pdq_is_insert2'_refine']  
     pdq_is_guarded_insert_impl.refine[FCOMP pdq_is_insert2'_refine']  
     maybe_is_insert_impl.refine[FCOMP maybe_is_insert2'_refine']     
    

     
  sepref_register 
    pdq_unguarded_insort: "pdq_insort False"
    pdq_guarded_insort: "pdq_insort True"
    maybe_insort
    
  sepref_def pdq_unguarded_insort_impl is "uncurry2 (PR_CONST (pdq_insort False))" 
    :: "(woarray_assn elem_assn)\<^sup>d *\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k \<rightarrow>\<^sub>a woarray_assn elem_assn"
    unfolding pdq_insort_def PR_CONST_def
    apply (simp named_ss HOL_ss:)
    apply (annot_snat_const "TYPE(size_t)")
    by sepref
    
  sepref_def pdq_guarded_insort_impl is "uncurry2 (PR_CONST (pdq_insort True))" 
    :: "(woarray_assn elem_assn)\<^sup>d *\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k \<rightarrow>\<^sub>a woarray_assn elem_assn"
    unfolding pdq_insort_def PR_CONST_def
    apply (simp named_ss HOL_ss:)
    apply (annot_snat_const "TYPE(size_t)")
    by sepref
     
  sepref_def maybe_insort_impl is "uncurry2 (PR_CONST maybe_insort)" 
    :: "(woarray_assn elem_assn)\<^sup>d *\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn \<times>\<^sub>a woarray_assn elem_assn"
    unfolding maybe_insort_def PR_CONST_def
    apply (simp named_ss HOL_ss:)
    apply (annot_snat_const "TYPE(size_t)")
    by sepref
    
    
  definition "pdq_insort_decG G xs l h \<equiv> if G then pdq_insort True xs l h else pdq_insort False xs l h"  
  lemma insort_is_decG: "pdq_insort = pdq_insort_decG" unfolding pdq_insort_decG_def by (auto intro!: ext)
    
  sepref_definition pdq_insort_impl [llvm_inline] is "uncurry3 (PR_CONST pdq_insort_decG)" 
    :: "bool1_assn\<^sup>k *\<^sub>a (woarray_assn elem_assn)\<^sup>d *\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k \<rightarrow>\<^sub>a woarray_assn elem_assn"
    unfolding pdq_insort_decG_def PR_CONST_def by sepref
     
    
  sepref_register 
    pdq_guarded_sort_spec
    maybe_sort_spec
    
  lemma pdq_insort_refine': "(PR_CONST pdq_insort_decG, PR_CONST pdq_guarded_sort_spec) \<in> Id \<rightarrow> Id \<rightarrow> Id \<rightarrow> Id \<rightarrow> \<langle>Id\<rangle>nres_rel"
    using insort_correct by (auto intro!: nres_relI simp: insort_is_decG)
    
  lemma maybe_insort_refine': "(PR_CONST maybe_insort, PR_CONST maybe_sort_spec) \<in> Id \<rightarrow> Id \<rightarrow> Id \<rightarrow> \<langle>Id\<rangle>nres_rel"  
    using maybe_insort_correct by (auto intro!: nres_relI)
    
  lemmas [sepref_fr_rules] = 
    pdq_insort_impl.refine[FCOMP pdq_insort_refine']  
    maybe_insort_impl.refine[FCOMP maybe_insort_refine']
    
             
end    
  
(* TODO: Parameterized comparisons *)  

end
