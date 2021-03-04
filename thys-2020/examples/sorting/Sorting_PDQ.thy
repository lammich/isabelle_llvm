theory Sorting_PDQ
imports Sorting_Setup Sorting_Partially_Sorted Sorting_Pdq_Insertion_Sort Sorting_Heapsort Sorting_Log2
begin

  subsection \<open>Auxiliary Definitions\<close>


  lemma slice_split_part: "l\<le>m \<Longrightarrow> m<h \<Longrightarrow> h\<le>length xs \<Longrightarrow> slice l h xs = slice l m xs @ xs!m # slice (Suc m) h xs"
    by (metis less_imp_le slice_append slice_split_hd)

  
  (* The set properties *)

  context weak_ordering begin
    lemma sorted_wrt_slice_iff_nth_less: "\<lbrakk> l\<le>h; h\<le>length xs \<rbrakk> \<Longrightarrow> sorted_wrt R (slice l h xs) \<longleftrightarrow> (\<forall>i j. l\<le>i \<and> i<j \<and> j<h \<longrightarrow> R (xs!i) (xs!j))"  
      unfolding sorted_wrt_iff_nth_less
      apply (clarsimp simp: slice_nth)      
      apply auto
      by (metis (full_types) diff_add_inverse diff_less_mono le_eq_less_or_eq le_trans nat_le_iff_add)
      

    lemma range_leq_set_slice_conv: 
      "h\<le>length xs \<Longrightarrow> (\<forall>i\<in>{l..<h}. xs!i \<^bold>\<le> pv) \<longleftrightarrow> (\<forall>x\<in>set (slice l h xs). x\<^bold>\<le>pv)"
      "h\<le>length xs \<Longrightarrow> (\<forall>i\<in>{l..<h}. xs!i \<^bold>\<ge> pv) \<longleftrightarrow> (\<forall>x\<in>set (slice l h xs). x\<^bold>\<ge>pv)"
      by (auto simp: set_slice_conv Ball_def)
      
      
  
    text \<open>Predicate to express that slice is partitioned\<close>              
    definition "partitioned pv xs l h m \<equiv> 
          l\<le>m \<and> m<h \<and> h\<le>length xs
        \<and> (\<forall>i\<in>{l..<m}. xs!i \<^bold>\<le> pv)
        \<and> xs!m = pv 
        \<and> (\<forall>i\<in>{m<..<h}. xs!i \<^bold>\<ge> pv)"

    lemma partitioned_alt: "partitioned pv xs l h m \<longleftrightarrow> 
          l\<le>m \<and> m<h \<and> h\<le>length xs
        \<and> (\<forall>x\<in>set (slice l m xs). x \<^bold>\<le> pv)
        \<and> xs!m = pv 
        \<and> (\<forall>x\<in>set (slice (m+1) h xs). x \<^bold>\<ge> pv)"    
      unfolding partitioned_def
      apply (rule iffI)
      subgoal by (auto simp: in_set_conv_nth slice_nth) []
      subgoal by (auto simp: range_leq_set_slice_conv[symmetric])
      done


    text \<open>Shuffling a partition does not change partitioned property\<close>            
    lemma shuffle_pres_part:
      "partitioned pv xs\<^sub>1 l h m \<Longrightarrow> slice_eq_mset l m xs\<^sub>1 xs\<^sub>2 \<Longrightarrow> partitioned pv xs\<^sub>2 l h m"  
      "partitioned pv xs\<^sub>1 l h m \<Longrightarrow> slice_eq_mset (Suc m) h xs\<^sub>1 xs\<^sub>2 \<Longrightarrow> partitioned pv xs\<^sub>2 l h m"
      unfolding partitioned_alt
      (* TODO: Clean up proof *)
      apply (clarsimp_all simp: slice_eq_mset_alt )
      apply (clarsimp_all simp: slice_eq_mset_eq_length eq_outside_range_nth slice_eq_outside_range dest: mset_eq_setD)
      apply (clarsimp_all simp: slice_eq_mset_alt )
      apply (auto simp:  eq_outside_range_nth slice_eq_outside_range dest: mset_eq_setD)
      done
      

    text \<open>After sorting the partitions, the whole slice is sorted.\<close>  
    lemma parts_sorted_imp_sorted:
      assumes "partitioned pv xs l h m"
      assumes "sorted_wrt_lt (\<^bold><) (slice l m xs)"
      assumes "sorted_wrt_lt (\<^bold><) (slice (Suc m) h xs)"
      shows "sorted_wrt_lt (\<^bold><) (slice l h xs)"
      using assms
      unfolding partitioned_def
      apply (clarsimp simp: slice_nth le_by_lt sorted_wrt_slice_iff_nth_less)
      by (metis (no_types, lifting) Suc_leI atLeastLessThan_iff greaterThanLessThan_iff linorder_neqE_nat local.trans)
      
            
  end    

  (*
    Configuration options for Pdqsort
  *)    
  abbreviation "is_threshold \<equiv> 16::nat"  (* TODO/FIXME: replace by pdq_is_threshold, and remove *)
  abbreviation "pdq_is_threshold \<equiv> 24"
    
  abbreviation "ninther_threshold \<equiv> 128::nat"

  context weak_ordering begin
    subsection \<open>Phases of Quicksort Scheme\<close>
    
    definition "part_range_cond xs l h \<equiv> (
          \<exists>i\<in>{l+1..<h}. xs!i \<^bold>\<le> xs!l)
        \<and> (\<exists>i\<in>{l+1..<h}. xs!i \<^bold>\<ge> xs!l)"

    text \<open>Pivot has been selected and moved to front\<close>      
    definition "R_PV_TO_FRONT l h xs xs' \<equiv> l+1<h \<and> h\<le>length xs \<and> slice_eq_mset l h xs xs' \<and> part_range_cond xs' l h"
    
    text \<open>Slice has been partitioned\<close>
    definition "R_PART pv l h m xs xs' \<equiv> l\<le>m \<and> m<h \<and> h\<le>length xs \<and> slice_eq_mset l h xs xs' \<and> partitioned pv xs' l h m"

    text \<open>Left partition has been sorted\<close>    
    definition "R_SORT_L pv l h m xs xs' \<equiv> R_PART pv l h m xs xs' \<and> sorted_wrt_lt (\<^bold><) (slice l m xs')"
    
    text \<open>Right partition has been sorted\<close>
    definition "R_SORT_R pv l h m xs xs' \<equiv> R_SORT_L pv l h m xs xs' \<and> sorted_wrt_lt (\<^bold><) (slice (Suc m) h xs')"

    text \<open>When right partition has been sorted, the whole slice is already sorted. \<close>  
    lemma R_SORT_R_sorted: "R_SORT_R pv l h m xs xs' \<Longrightarrow> slice_eq_mset l h xs xs' \<and> sorted_wrt_lt (\<^bold><) (slice l h xs')"
      unfolding R_SORT_R_def R_SORT_L_def R_PART_def
      by (auto simp: parts_sorted_imp_sorted)

    text \<open>Sorting the whole partition, e.g., due to heapsort fallback\<close>      
    lemma R_PART_SORT: "R_PART pv l h m xs xs' \<Longrightarrow> slice_sort_spec (\<^bold><) xs' l h \<le> SPEC (\<lambda>xs''. slice_eq_mset l h xs xs'' \<and> sorted_wrt_lt (\<^bold><) (slice l h xs''))"  
      unfolding slice_sort_spec_sem_alt R_PART_def
      apply refine_vcg
      apply (auto simp: slice_eq_mset_eq_length dest: slice_eq_mset_trans)
      done

      
    subsection \<open>Specifications of Subroutines\<close>
      

    text \<open>Move pivot to front\<close>          
    definition "pivot_to_front_spec xs l h \<equiv> doN {
      ASSERT (l + 4 < h \<and> h \<le> length xs);
      SPEC (\<lambda>xs'. 
          slice_eq_mset l h xs xs'
        \<and> part_range_cond xs' l h
      )
    }"

    lemma pivot_to_front_spec_rl: "\<lbrakk> l + 4 < h; h\<le>length xs \<rbrakk> \<Longrightarrow> pivot_to_front_spec xs l h \<le> SPEC (\<lambda>xs'. R_PV_TO_FRONT l h xs xs')"
      unfolding pivot_to_front_spec_def R_PV_TO_FRONT_def
      by auto

    text \<open>Partition\<close>          
    definition "partition_spec xs l h \<equiv> doN {
      ASSERT ( 
          l + 1 < h \<and> h \<le> length xs 
        \<and> part_range_cond xs l h
      );
      SPEC (\<lambda>(alrp::bool,m,xs'). 
          slice_eq_mset l h xs xs'
        \<and> l\<le>m \<and> m<h
        \<and> partitioned (xs!l) xs' l h m
      )
    }"

    definition "partition_left_spec \<equiv> partition_spec" (* No discrimination required on this abs-level *)
    
    lemma partition_spec_rl: "R_PV_TO_FRONT l h xs\<^sub>0 xs \<Longrightarrow> partition_spec xs l h \<le> SPEC (\<lambda>(_,m,xs'). m<h \<and> R_PART (xs!l) l h m xs\<^sub>0 xs')"
      unfolding partition_spec_def R_PV_TO_FRONT_def R_PART_def 
      apply refine_vcg 
      by (auto simp: slice_eq_mset_eq_length dest: slice_eq_mset_trans)
    
      
    lemma aux1: 
      assumes BOUNDS: "l \<le> m" "m < h" "h \<le> length xs'"
      assumes NOT_LESS: "\<not> prev \<^bold>< pv"
      assumes PART: "partitioned pv xs' l h m"
      assumes LPART: "\<forall>x\<in>set (slice l h xs'). prev \<^bold>\<le> x"
      shows "
       \<lbrakk>0 < l; part_range_cond xs l h; slice_eq_mset l h xs xs' \<rbrakk>
       \<Longrightarrow> sorted_wrt_lt (\<^bold><) (slice l m xs')"  
    proof -
    
      from NOT_LESS have "pv \<^bold>\<le> prev" using wo_leI by blast
    
      from PART have LEFT_PART_LE: "\<forall>i\<in>{l..<m}. xs'!i \<^bold>\<le> pv"
        unfolding partitioned_def by auto
      
      from LPART have PREV_LE: "\<forall>i\<in>{l..<h}. prev \<^bold>\<le> xs'!i"
        using assms(3) range_leq_set_slice_conv(2) by blast
        
      {
        fix i j
        assume "l\<le>i" "i<j" "j<m"
        hence "xs'!i \<^bold>\<le> xs'!j"
        by (meson LEFT_PART_LE PREV_LE \<open>pv \<^bold>\<le> prev\<close> assms(2) atLeastLessThan_iff le_less_trans less_imp_le_nat local.trans)
      }
      then show "sorted_wrt_lt (\<^bold><) (slice l m xs')"
        using BOUNDS
        by (auto simp: sorted_wrt_slice_iff_nth_less le_by_lt)
    qed    
    
    text \<open>Correctness lemma for the partition-left optimization for many equal elements.\<close>      
    lemma partition_left_spec_rl: "\<lbrakk>R_PV_TO_FRONT l h xs\<^sub>0 xs; 0<l; \<not>(xs!(l-1) \<^bold>< xs!l); (\<forall>x\<in>set (slice l h xs\<^sub>0). xs\<^sub>0!(l-1) \<^bold>\<le> x) \<rbrakk> 
      \<Longrightarrow> partition_left_spec xs l h \<le> SPEC (\<lambda>(_,m,xs'). m<h \<and> R_SORT_L (xs!l) l h m xs\<^sub>0 xs')"
      unfolding partition_spec_def partition_left_spec_def R_PV_TO_FRONT_def R_PART_def R_SORT_L_def
      apply refine_vcg 
      apply (auto simp: slice_eq_mset_eq_length slice_eq_mset_nth_outside slice_eq_mset_set_inside aux1 dest: slice_eq_mset_trans)
      done

    text \<open>Shuffle. We only specify that the partitions must contain the same elements.\<close>        
    definition "shuffle_spec xs l h m \<equiv> doN {
      ASSERT (l\<le>m \<and> m<h \<and> h\<le>length xs);
      SPEC (\<lambda>(unbal,xs'). 
        eq_outside_range xs xs' l h
      \<and> mset (slice l m xs) = mset (slice l m xs')  
      \<and> xs!m = xs'!m
      \<and> mset (slice (m+1) h xs) = mset (slice (m+1) h xs')  
      )
    }"

    lemma shuffle_rule: "\<lbrakk>R_PART pv l h m xs\<^sub>0 xs\<rbrakk> \<Longrightarrow> shuffle_spec xs l h m \<le> SPEC (\<lambda>(_,xs'). R_PART pv l h m xs\<^sub>0 xs')"
      unfolding R_PART_def shuffle_spec_def partitioned_alt
      apply refine_vcg
      apply (auto simp: slice_eq_mset_alt eq_outside_rane_lenD dest: mset_eq_setD)
      apply (simp add: slice_eq_mset_alt eq_outside_range_def)
      subgoal for xs\<^sub>2 
        apply (rewrite in "\<hole> = _" slice_split_part; simp add: eq_outside_rane_lenD)
        apply (rewrite in "_ = \<hole>" slice_split_part; simp add: eq_outside_rane_lenD)
        done
      done

    text \<open>Maybe-Sort: The specification nondeterministically decides whether to sort or not. 
      In any case, the elements are permutated.
    \<close>          
    lemma maybe_sort_rule1: "R_PART pv l h m xs\<^sub>0 xs \<Longrightarrow> maybe_sort_spec xs l m 
      \<le> SPEC (\<lambda>(r,xs'). (r\<longrightarrow>R_SORT_L pv l h m xs\<^sub>0 xs') \<and> R_PART pv l h m xs\<^sub>0 xs')"
      unfolding maybe_sort_spec_def R_PART_def R_SORT_L_def
      apply (refine_vcg)
      apply (clarsimp_all simp: slice_eq_mset_eq_length)
      subgoal by (meson eq_imp_le less_imp_le slice_eq_mset_subslice slice_eq_mset_trans)
      subgoal using shuffle_pres_part(1) by blast
      subgoal by (meson less_or_eq_imp_le slice_eq_mset_subslice slice_eq_mset_trans)
      subgoal using shuffle_pres_part(1) by blast
      done

      
    lemma maybe_sort_rule2: "R_SORT_L pv l h m xs\<^sub>0 xs \<Longrightarrow> maybe_sort_spec xs (Suc m) h 
      \<le> SPEC (\<lambda>(r,xs'). (r\<longrightarrow>R_SORT_R pv l h m xs\<^sub>0 xs') \<and> (\<not>r \<longrightarrow> R_SORT_L pv l h m xs\<^sub>0 xs'))"
      unfolding maybe_sort_spec_def R_PART_def  R_SORT_L_def R_SORT_R_def
      apply (refine_vcg)
      apply (clarsimp_all simp: slice_eq_mset_eq_length slice_eq_mset_eq_outside(1))
      subgoal
        by (meson le_SucI nat_in_between_eq(2) order.strict_implies_order slice_eq_mset_subslice slice_eq_mset_trans)
      subgoal
        using shuffle_pres_part(2) by blast 
      subgoal
        by (meson le_SucI le_refl less_imp_le_nat slice_eq_mset_subslice slice_eq_mset_trans) 
      subgoal
        using shuffle_pres_part(2) by blast 
      done
    
    lemma sort_rule1: "R_PART pv l h m xs\<^sub>0 xs \<Longrightarrow> slice_sort_spec (\<^bold><) xs l m
      \<le> SPEC (\<lambda>xs'. R_SORT_L pv l h m xs\<^sub>0 xs')"
      unfolding slice_sort_spec_sem_alt R_PART_def  R_SORT_L_def R_SORT_R_def
      apply (refine_vcg)
      apply (clarsimp_all simp: slice_eq_mset_eq_length slice_eq_mset_eq_outside(1))
      subgoal by (meson le_refl less_imp_le_nat slice_eq_mset_subslice slice_eq_mset_trans)
      subgoal using shuffle_pres_part(1) by blast
      done

      
    lemma sort_again_rule1: "R_SORT_L pv l h m xs\<^sub>0 xs \<Longrightarrow> slice_sort_spec (\<^bold><) xs l m
      \<le> SPEC (\<lambda>xs'. R_SORT_L pv l h m xs\<^sub>0 xs')"
      unfolding slice_sort_spec_sem_alt R_PART_def  R_SORT_L_def R_SORT_R_def
      apply (refine_vcg)
      apply (clarsimp_all simp: slice_eq_mset_eq_length slice_eq_mset_eq_outside(1))
      subgoal by (meson le_refl less_imp_le_nat slice_eq_mset_subslice slice_eq_mset_trans)
      subgoal using shuffle_pres_part(1) by blast
      done
            
    lemma sort_rule2: "R_SORT_L pv l h m xs\<^sub>0 xs \<Longrightarrow> slice_sort_spec (\<^bold><) xs (Suc m) h
      \<le> SPEC (\<lambda>xs'. R_SORT_R pv l h m xs\<^sub>0 xs')"
      unfolding slice_sort_spec_sem_alt R_PART_def R_SORT_L_def R_SORT_R_def
      apply (refine_vcg)
      apply (clarsimp_all simp: slice_eq_mset_eq_length slice_eq_mset_eq_outside(1))
      subgoal by (meson le_Suc_eq less_imp_le_nat nat_in_between_eq(2) slice_eq_mset_subslice slice_eq_mset_trans)
      subgoal using shuffle_pres_part(2) by blast
      done
            
      
    text \<open>Fallback sorting. Will be instantiated by Heapsort later.\<close>  
    definition "fallback_sort_spec \<equiv> slice_sort_spec (\<^bold><)"      
      

    subsection \<open>Abstract Pdqsort\<close>          
    text \<open>Recursive Pdqsort function.\<close>
    definition "pdqsort_aux leftmost xs l h (d::nat) \<equiv> RECT (\<lambda>pdqsort_aux (leftmost,xs,l,h,d). doN {
      ASSERT (l\<le>h \<and> h\<le>length xs \<and> 0<d);
      ASSERT (\<not>leftmost \<longrightarrow> l>0 \<and> (\<forall>x\<in>set (slice l h xs). xs!(l-1) \<^bold>\<le> x));
      
      if (h-l < pdq_is_threshold) then 
        pdq_guarded_sort_spec leftmost xs l h
      else doN {
        xs \<leftarrow> pivot_to_front_spec xs l h;

        ASSERT (l-1<length xs \<and> l<length xs);
        ASSERT (\<not>leftmost \<longrightarrow> l>0);         
        if (\<not>leftmost \<and> \<not>(xs!(l-1) \<^bold>< xs!l)) then doN {
          (_,m,xs) \<leftarrow> partition_left_spec xs l h;
          ASSERT (m<h);
          pdqsort_aux (False,xs,m+1,h,d)
        } else doN {
          (alrp,m,xs) \<leftarrow> partition_spec xs l h;
          (unbal,xs) \<leftarrow> shuffle_spec xs l h m;
          
          ASSERT (0<d);
          let d = (if unbal then d-1 else d);
          
          (didsort,xs) \<leftarrow> 
            if d=0 then doN {xs \<leftarrow> fallback_sort_spec xs l h; RETURN (True,xs)}
            else if alrp \<and> \<not>unbal then doN {
              (r,xs) \<leftarrow> maybe_sort_spec xs l m;
              if r then doN {
                ASSERT (m<h);
                maybe_sort_spec xs (m+1) h
              } else RETURN (False,xs)
            } else RETURN (False,xs);
            
          if didsort then RETURN xs 
          else doN { \<^cancel>\<open>TODO: Test optimization of not sorting left partition again, if maybe_sort sorted it\<close>
            xs \<leftarrow> pdqsort_aux (leftmost,xs,l,m,d);
            ASSERT (m<h);
            xs \<leftarrow> pdqsort_aux (False,xs,m+1,h,d);
            RETURN xs
          } 
        }
      }
    
    }) (leftmost,xs,l,h,d)"
    

    (*
      The correctness proof is some manual fiddling with the VCG, 
      but essentially uses the lemmas proved above.
    *)    
    lemma pdqsort_aux_correct:
      assumes "l\<le>h" "h\<le>length xs" "\<not>leftmost \<Longrightarrow> l>0 \<and> (\<forall>x\<in>set (slice l h xs). xs!(l-1) \<^bold>\<le> x)" "d>0"  
      shows "pdqsort_aux leftmost xs l h d \<le> slice_sort_spec (\<^bold><) xs l h"
      unfolding pdqsort_aux_def fallback_sort_spec_def
      
      apply (rule order_trans)
      apply (rule RECT_rule[where 
            V="measure (\<lambda>(leftmost,xs,l,h,d). h-l)" 
        and pre="\<lambda>(leftmost,xs,l,h,d). l\<le>h \<and> h\<le>length xs \<and> 0<d \<and> (\<not>leftmost \<longrightarrow> l>0 \<and> (\<forall>x\<in>set (slice l h xs). xs!(l-1) \<^bold>\<le> x))"
        and M="\<lambda>(leftmost,xs,l,h,d). slice_sort_spec (\<^bold><) xs l h"
        ], refine_mono)

              
      subgoal by simp  
      subgoal using assms by auto
      subgoal premises prems for pdqsort args proof -
      
        obtain leftmost xs l h d where [simp]: "args = (leftmost, xs, l, h, d)" by (cases args)
      
        note IH = prems(1)
        note LEFTMOST = prems(2)
      
        {
          fix pv m xs xs' and d'::nat
          assume "R_SORT_L pv l h m xs xs'" and "0<d'"
          hence "pdqsort (False,xs',Suc m,h,d') \<le> SPEC (\<lambda>xs''. R_SORT_R pv l h m xs xs'')"
            apply -
            apply (rule order_trans[OF IH])
            subgoal by (simp add: R_SORT_L_def R_PART_def partitioned_alt)
            subgoal by (auto simp add: R_SORT_L_def R_PART_def partitioned_alt)
            subgoal by (simp add: sort_rule2)
            done
        } note rec_sort_r_rl = this
        
        {
          fix pv m xs' and d'::nat
          assume "R_PART pv l h m xs xs'" and "0<d'"
          hence "pdqsort (leftmost,xs',l,m,d') \<le> SPEC (\<lambda>xs''. R_SORT_L pv l h m xs xs'')"
            apply -
            apply (rule order_trans[OF IH])
            subgoal using LEFTMOST 
              apply (clarsimp simp: R_PART_def slice_eq_mset_eq_length slice_eq_mset_nth_outside slice_eq_mset_set_inside) 
              apply (drule set_rev_mp[OF _ set_slice_subsetI, of _ l m _ l h])
              by auto
            subgoal by (auto simp add: R_SORT_L_def R_PART_def partitioned_alt)
            subgoal by (simp add: sort_rule1)
            done
        } note rec_sort_l_rl = this
        
        {
          fix pv m xs' and d'::nat
          assume "R_SORT_L pv l h m xs xs'" and "0<d'"
          hence "pdqsort (leftmost,xs',l,m,d') \<le> SPEC (\<lambda>xs''. R_SORT_L pv l h m xs xs'')"
          using rec_sort_l_rl unfolding R_SORT_L_def by blast
        } note rec_sort_l_again_rl = this
              
        
        show ?thesis
          apply (rewrite in "_\<le>\<hole>" slice_sort_spec_sem_alt)
          apply (cases args,simp)
          apply (refine_vcg pivot_to_front_spec_rl partition_spec_rl partition_left_spec_rl shuffle_rule; assumption?)
          using LEFTMOST
          apply (clarsimp_all simp: slice_eq_mset_eq_length eq_outside_rane_lenD)
          apply (all \<open>assumption?\<close>)
          subgoal 
            apply (simp add: slice_sort_spec_sem_alt pdq_guarded_sort_spec_def)
            apply refine_vcg
            by (auto simp: unfold_le_to_lt)
          subgoal by simp
          subgoal unfolding R_PV_TO_FRONT_def by (auto simp: slice_eq_mset_eq_length)
          subgoal unfolding R_PV_TO_FRONT_def by (auto simp: slice_eq_mset_eq_length)
          subgoal 
            apply (refine_vcg rec_sort_r_rl, assumption)
            by (clarsimp_all simp: R_SORT_R_sorted)
          subgoal by (simp add: R_PART_SORT)
          subgoal
            apply (all \<open>erule maybe_sort_rule1[THEN order_trans]\<close>)
            apply (all \<open>refine_vcg\<close>)
            apply clarsimp_all
            apply (all \<open>(erule maybe_sort_rule2[THEN order_trans])?\<close>)
            apply (all \<open>(refine_vcg)?\<close>)
            apply (clarsimp_all simp: R_SORT_R_sorted)
            subgoal
              apply (refine_vcg rec_sort_l_again_rl, assumption)
              apply (refine_vcg rec_sort_r_rl, assumption)
              by (clarsimp_all simp: R_SORT_R_sorted)
            subgoal
              apply (refine_vcg rec_sort_l_rl, assumption)
              apply (refine_vcg rec_sort_r_rl, assumption)
              by (clarsimp_all simp: R_SORT_R_sorted)
            done
          subgoal
            apply (intro conjI impI)  
            subgoal
              apply (refine_vcg rec_sort_l_rl, assumption, simp)
              apply (refine_vcg rec_sort_r_rl, assumption, simp)
              by (clarsimp_all simp: R_SORT_R_sorted)
            subgoal
              apply (refine_vcg rec_sort_l_rl, assumption)
              apply (refine_vcg rec_sort_r_rl, assumption)
              by (clarsimp_all simp: R_SORT_R_sorted)
            done
          done
      qed
      subgoal by simp
      done      
      

    text \<open>Main Pdqsort function. Just a wrapper for the recursive function, 
      initializing the maximum number of bad partitions before switching to fallback sorting.\<close>        
    definition "pdqsort xs l h \<equiv> doN {
      ASSERT (l\<le>h);
      let size = h-l;
      if (size>1) then pdqsort_aux True xs l h (Discrete.log size)
      else RETURN xs
    }"  
      
    lemma pdqsort_correct: "pdqsort xs l h \<le> slice_sort_spec (\<^bold><) xs l h"
    proof -
      have log_pos_aux: "1<x \<Longrightarrow> 0 < Discrete.log x" for x
        apply (subst log_rec) by auto 
        
      {
        assume "l\<le>h" "h\<le>length xs"
        hence ?thesis
          unfolding pdqsort_def
          apply (cases "1 < h-l"; simp)
          subgoal by (rule pdqsort_aux_correct; simp add: log_pos_aux)
          subgoal unfolding slice_sort_spec_def sort_spec_def by refine_vcg (auto simp: sorted_wrt01)
          done
      } thus ?thesis unfolding slice_sort_spec_def by (simp only: pw_le_iff refine_pw_simps) blast
    qed    
      
    
    subsection \<open>Implementation of Subroutines\<close>
    
    
    definition "sort_two xs i j \<equiv> doN {
      ASSERT (i<length xs \<and> j<length xs \<and> i\<noteq>j);
      if\<^sub>N mop_cmp_idxs xs j i then mop_list_swap xs i j else RETURN xs
      
      \<^cancel>\<open>if (xs!j \<^bold>< xs!i) then mop_list_swap xs i j else RETURN xs\<close>
    }"              
    
    definition "sort_three xs i j k \<equiv> doN {
      xs \<leftarrow> sort_two xs i j;
      xs \<leftarrow> sort_two xs j k;
      xs \<leftarrow> sort_two xs i j;
      RETURN xs
    }"              

    lemma sort_three_rule: "\<lbrakk>
      {i,j,k}\<subseteq>{l..<h}; i\<noteq>j; i\<noteq>k; j\<noteq>k; h\<le>length xs
    \<rbrakk> \<Longrightarrow> sort_three xs i j k \<le> SPEC (\<lambda>xs'. slice_eq_mset l h xs xs' \<and> xs'!i \<^bold>\<le> xs'!j \<and> xs'!j \<^bold>\<le> xs'!k \<and> (\<forall>l\<in>-{i,j,k}. xs!l=xs'!l))"
      unfolding sort_three_def sort_two_def
      apply simp
      apply (simp add: swap_nth unfold_le_to_lt split: if_splits)
      apply (simp add: unfold_lt_to_le)
      done
      
    
    definition "three_sorted xs i j k \<equiv> {i,j,k} \<subseteq> {0..<length xs} \<and> xs!i \<^bold>\<le> xs!j \<and> xs!j \<^bold>\<le> xs!k"

    lemma sort_three_sorted_rl: "sort_three xs\<^sub>1 i j k \<le> SPEC (\<lambda>xs\<^sub>2. length xs\<^sub>1=length xs\<^sub>2 \<and> slice_eq_mset l h xs\<^sub>1 xs\<^sub>2 \<and> three_sorted xs\<^sub>2 i j k)"  
      if "{i,j,k}\<subseteq>{l..<h}" "i\<noteq>j" "i\<noteq>k" "j\<noteq>k" "l<h" "h\<le>length xs\<^sub>1" for i j k and xs\<^sub>1 xs\<^sub>2 :: "'a list"
      using that
      apply (refine_vcg sort_three_rule[where l=l and h=h])
      apply (auto simp: slice_eq_mset_eq_length three_sorted_def)
      done
    
        
    lemma three_sorted_imp_part_range_cond: "\<lbrakk> three_sorted xs i l k; l<i; l<k; i<h; k<h \<rbrakk> \<Longrightarrow> part_range_cond xs l h"
      unfolding three_sorted_def part_range_cond_def by auto

    lemma three_sorted_swap_imp_part_range_cond: "\<lbrakk> three_sorted xs i j k; i\<noteq>j; j\<noteq>k; l<i; l<j; l<k; i<h; j<h; k<h; h\<le>length xs \<rbrakk> \<Longrightarrow> part_range_cond (swap xs l j) l h"
      unfolding three_sorted_def part_range_cond_def by (auto simp: swap_nth)
          
                  
    definition "move_pivot_to_front xs l h \<equiv> doN {
      ASSERT (l\<le>h \<and> h>0);
      let size = h-l;
      let s2 = size div 2;

      if (size > ninther_threshold) then doN {
        \<^cancel>\<open>ASSERT (l+s2+1<h \<and> h\<ge>3 \<and> s2\<ge>1 \<and> s2<h );\<close>
        xs\<leftarrow>sort_three xs l              (l + s2)       (h - 1);
        xs\<leftarrow>sort_three xs (l + 1)        (l + (s2 - 1)) (h - 2);
        xs\<leftarrow>sort_three xs (l + 2)        (l + (s2 + 1)) (h - 3);
        xs\<leftarrow>sort_three xs (l + (s2 - 1)) (l + s2)       (l + (s2 + 1));
        xs \<leftarrow> mop_list_swap xs l (l+s2);
        \<^cancel>\<open>ASSERT (xs!l \<^bold>\<le> xs!(l + (s2 + 1)) \<and> xs!(l + (s2 - 1)) \<^bold>\<le> xs!l);\<close>
        RETURN xs
      } else doN {
        \<^cancel>\<open>ASSERT (l+s2 \<noteq> h-1 \<and> l+s2<h \<and> h>0);\<close>
        sort_three xs (l+s2) l (h-1)
      }
    }"
    
    
    lemma move_pivot_to_front_refine: "move_pivot_to_front xs l h \<le> pivot_to_front_spec xs l h"
      unfolding move_pivot_to_front_def pivot_to_front_spec_def
      apply (refine_vcg sort_three_sorted_rl[where l=l and h=h]) 
      apply (all \<open>elim conjE; assumption?\<close>)
      supply [[linarith_split_limit = 15]]
      apply simp_all
      subgoal by (auto)
      subgoal by (auto)
      subgoal by (auto)
      subgoal by (auto)
      subgoal by (metis slice_eq_mset_trans)
      subgoal by (erule three_sorted_swap_imp_part_range_cond) auto
      subgoal by (auto)
      subgoal by (erule three_sorted_imp_part_range_cond; auto)
      done    

      
      
    definition "shuffle_left xs i j \<equiv> doN {ASSERT (i\<noteq>j); mop_list_swap xs i j}"  
    definition "shuffle_right xs i j \<equiv> doN {ASSERT (i\<noteq>j); mop_list_swap xs i j}"  
      
    definition "shuffle xs l h m \<equiv> doN {
      ASSERT (l\<le>h \<and> l\<le>m \<and> m+1\<le>h);
      let size = h-l;
      let l_size = m-l;
      let r_size = h - (m+1);
      let highly_unbal = l_size < size div 8 \<or> r_size < size div 8;
    
      if highly_unbal then doN {
        xs \<leftarrow> if l_size \<ge> is_threshold then doN {  \<^cancel>\<open>FIXME: This should be pdq_is_threshold!\<close>
\<^cancel>\<open>          ASSERT (l + l_size div 4 < h \<and> m>0 \<and> m\<ge>l_size div 4);
\<close>          xs \<leftarrow> shuffle_left xs l (l+l_size div 4);
          xs \<leftarrow> shuffle_left xs (m-1) (m - l_size div 4);
          
          if l_size > ninther_threshold then doN {
\<^cancel>\<open>            ASSERT (
                l+1\<le>h \<and> l_size div 4 + 1\<le>h \<and> l + (l_size div 4 + 1)\<le>h 
              \<and> l+2\<le>h \<and> l_size div 4 + 2\<le>h \<and> l + (l_size div 4 + 2)\<le>h
              \<and> m\<ge>2 \<and> m\<ge>3 \<and> m\<ge>l_size div 4 + 1 \<and> m\<ge>l_size div 4 + 2);
\<close>            
            xs \<leftarrow> shuffle_left xs (l + 1) (l + (l_size div 4 + 1));
            xs \<leftarrow> shuffle_left xs (l + 2) (l + (l_size div 4 + 2));
            xs \<leftarrow> shuffle_left xs (m - 2) (m - (l_size div 4 + 1));
            xs \<leftarrow> shuffle_left xs (m - 3) (m - (l_size div 4 + 2));
            RETURN xs
          } else RETURN xs
        } else RETURN xs;
        xs \<leftarrow> if r_size \<ge> is_threshold then doN {  \<^cancel>\<open>FIXME: This should be pdq_is_threshold!\<close>
 \<^cancel>\<open>         ASSERT (m+1\<le>h \<and> m + 1 + r_size div 4\<le>h \<and> h\<ge>1 \<and> h\<ge>r_size div 4);
 \<close>         xs \<leftarrow> shuffle_right xs (m+1) (m + 1 + r_size div 4);
          xs \<leftarrow> shuffle_right xs (h-1) (h - r_size div 4);
          if r_size > ninther_threshold then doN {
  \<^cancel>\<open>          ASSERT (m+2\<le>h \<and> 1 + r_size div 4\<le>h \<and> 2 + r_size div 4\<le>h \<and> 3 + r_size div 4\<le>h 
                  \<and> h\<ge>2 \<and> h\<ge>3 \<and> h\<ge>(1 + r_size div 4) \<and> h\<ge>(2 + r_size div 4) );
  \<close>          xs \<leftarrow> shuffle_right xs (m + 2) (m + (2 + r_size div 4));
            xs \<leftarrow> shuffle_right xs (m + 3) (m + (3 + r_size div 4));
            xs \<leftarrow> shuffle_right xs (h - 2) (h - (1 + r_size div 4));  
            xs \<leftarrow> shuffle_right xs (h - 3) (h - (2 + r_size div 4));          
            RETURN xs
          } else RETURN xs
        } else RETURN xs;
        RETURN (True,xs)
      } else
        RETURN (False,xs)
    }"
      
    definition "shuffled l h m xs xs' \<equiv>         
        l\<le>m \<and> m<h \<and> h\<le>length xs 
      \<and> eq_outside_range xs xs' l h
      \<and> mset (slice l m xs) = mset (slice l m xs')  
      \<and> xs!m = xs'!m
      \<and> mset (slice (m+1) h xs) = mset (slice (m+1) h xs')"
    
      
    lemma eq_outside_range_swap: "{i,j}\<subseteq>{l..<h} \<Longrightarrow> eq_outside_range xs (swap xs' i j) l h = eq_outside_range xs xs' l h"  
      by (auto simp: eq_outside_range_def)
    
      
    lemma shuffled_left: "\<lbrakk> {i,j}\<subseteq>{l..<m}; shuffled l h m xs xs' \<rbrakk> \<Longrightarrow> shuffled l h m xs (swap xs' i j)"  
      unfolding shuffled_def
      by (auto simp: eq_outside_range_swap slice_swap eq_outside_rane_lenD slice_swap_outside)
      
    lemma shuffled_right: "\<lbrakk> {i,j}\<subseteq>{Suc m..<h}; shuffled l h m xs xs' \<rbrakk> \<Longrightarrow> shuffled l h m xs (swap xs' i j)"  
      unfolding shuffled_def
      by (auto simp: eq_outside_range_swap slice_swap eq_outside_rane_lenD slice_swap_outside)
      
    lemma shuffle_spec_alt: "shuffle_spec xs l h m = doN {ASSERT (l\<le>m \<and> m<h \<and> h\<le>length xs); SPEC (\<lambda>(_,xs'). shuffled l h m xs xs')}"  
      unfolding shuffle_spec_def shuffled_def by (auto simp: pw_eq_iff refine_pw_simps)
      
    lemma shuffled_refl: "shuffled l h m xs xs \<longleftrightarrow> l\<le>m \<and> m<h \<and> h\<le>length xs"   
      by (auto simp: shuffled_def eq_outside_range_triv)
      
    lemma shuffle_left_rl: "shuffled l h m xs xs' \<Longrightarrow> i\<noteq>j \<Longrightarrow> {i,j}\<subseteq>{l..<m} \<Longrightarrow> shuffle_left xs' i j \<le> SPEC (\<lambda>xs''. shuffled l h m xs xs'')"  
      unfolding shuffle_left_def
      apply refine_vcg
      apply (simp_all add: shuffled_left)
      by (auto simp: shuffled_def eq_outside_rane_lenD)
      
    lemma shuffle_right_rl: "shuffled l h m xs xs' \<Longrightarrow> i\<noteq>j \<Longrightarrow> {i,j}\<subseteq>{Suc m..<h} \<Longrightarrow> shuffle_right xs' i j \<le> SPEC (\<lambda>xs''. shuffled l h m xs xs'')"  
      unfolding shuffle_right_def
      apply refine_vcg
      apply (simp_all add: shuffled_right)
      by (auto simp: shuffled_def eq_outside_rane_lenD)
      
      
    
    lemma shuffle_correct: "shuffle xs l h m \<le> shuffle_spec xs l h m"       
      unfolding shuffle_spec_alt
      apply (refine_vcg)
      unfolding shuffle_def
      apply (subgoal_tac "shuffled l h m xs xs")
      apply refine_vcg
      apply (simp_all add: shuffled_refl)
      apply (all \<open>(thin_tac "m-l < _ \<or> _")?\<close>)

      (* TODO: The splitter is probably getting in the way here! *)
      subgoal
        apply (refine_vcg shuffle_left_rl; assumption?) 
        apply (simp_all add: shuffled_refl)
        supply [[linarith_split_limit = 25]]
        apply auto [6]
        apply (refine_vcg shuffle_right_rl; assumption?) 
        apply (simp_all add: shuffled_refl)
        apply auto [6]
        apply (refine_vcg shuffle_right_rl; assumption?) 
        apply (simp_all)
        apply auto
        done
      subgoal  
        apply (refine_vcg shuffle_right_rl; assumption?) 
        apply (simp_all add: shuffled_refl)
        apply auto
        done      
      done  
    
    
      
    text \<open>
      Some definitions to hide away propositions that would overwhelm the linarith-solver of the simplifier.
    \<close>  
    (*
      Elements in between l<..i are smaller than pivot.
        * at beginning of loop, will be i-1, 
        * after swapping, will be i
    *)  
    definition "AUX_SMALLER C l h xs i \<equiv> l<h \<and> h\<le>length xs \<and> l\<le>i \<and> i<h \<and> (\<forall>k\<in>{l<..i}. C (xs!k) (xs!l))"  
    
    (*
      Elements in between j..<h are not smaller than pivot
      
      * at beginning of loop, will be j+1
      * after swapping, will be j
    *)
    definition "AUX_NOTSM C l h xs j   \<equiv> l<h \<and> h\<le>length xs \<and> l<j \<and> j\<le>h \<and> (\<forall>k\<in>{j..<h}. C (xs!k) (xs!l))"
    
    
    definition "RIGHT_GUARD C l h xs i \<equiv> l<h \<and> h\<le>length xs \<and> (\<exists>k\<in>{i<..<h}. \<not> C (xs!k) (xs!l))"
    
    definition "LEFT_GUARD C l xs j \<equiv> l<length xs \<and> (\<exists>k\<in>{l<..<j}. \<not> C (xs!k) (xs!l))"
    

    lemma AUX_SMALLER_init: "\<lbrakk> l<h; h\<le>length xs \<rbrakk> \<Longrightarrow> AUX_SMALLER C l h xs l"
      unfolding AUX_SMALLER_def by auto
        
    lemma AUX_NOTSM_init: "\<lbrakk>l<h; h\<le>length xs\<rbrakk> \<Longrightarrow> AUX_NOTSM C l h xs h"  
      unfolding AUX_NOTSM_def by auto

    lemma RIGHT_GUARD_from_prc: "part_range_cond xs l h \<Longrightarrow> l<h \<and> h\<le>length xs \<Longrightarrow> RIGHT_GUARD (\<^bold><) l h xs l"  
      unfolding part_range_cond_def RIGHT_GUARD_def
      by (auto simp: unfold_le_to_lt)

    lemma LEFT_GUARD_from_prc: "part_range_cond xs l h \<Longrightarrow> l<h \<and> h\<le>length xs \<Longrightarrow> LEFT_GUARD (\<^bold>>) l xs h"  
      unfolding part_range_cond_def LEFT_GUARD_def
      by (auto simp: unfold_le_to_lt)
      
            
    lemma LEFT_GUARD_init: "\<lbrakk>AUX_SMALLER (Not oo C) l h xs (i - Suc 0); l < i;  Suc l < j\<^sub>0; i \<noteq> Suc l\<rbrakk> \<Longrightarrow> LEFT_GUARD C l xs j\<^sub>0"        
      unfolding AUX_SMALLER_def LEFT_GUARD_def
      by fastforce 
    
    lemma RIGHT_GUARD_init: " \<lbrakk>AUX_NOTSM (Not \<circ>\<circ> C) l h xs (Suc j); AUX_SMALLER C l h xs i\<^sub>0; Suc j \<noteq> h\<rbrakk> \<Longrightarrow> RIGHT_GUARD C l h xs i\<^sub>0"        
      unfolding AUX_NOTSM_def RIGHT_GUARD_def AUX_SMALLER_def
      by fastforce 
            
    
    lemma PV_SWAP:
      assumes "AUX_SMALLER C l h xs (i-1)" "AUX_NOTSM (Not oo C) l h xs (j+1)"
      assumes "l<i" "i<j" "\<not> C(xs!i) (xs!l)" "C (xs!j) (xs!l)"
      shows "AUX_SMALLER C l h (swap xs i j) i" "AUX_NOTSM (Not oo C) l h (swap xs i j) j"
      using assms
      unfolding AUX_SMALLER_def AUX_NOTSM_def
      by (auto simp: swap_nth)
      
          
    lemma PARTITIONED_FINALLY: "\<not>(i<j) \<Longrightarrow> \<not>xs!i\<^bold><xs!l \<Longrightarrow> AUX_SMALLER (\<^bold><) l h xs (i-1) \<Longrightarrow> AUX_NOTSM (Not oo (\<^bold><)) l h xs (j+1) \<Longrightarrow> partitioned (xs!l) (swap xs l (i-Suc 0)) l h (i-Suc 0)"
      unfolding partitioned_def AUX_SMALLER_def AUX_NOTSM_def
      apply (auto simp: swap_nth unfold_lt_to_le)
      apply (metis Suc_leI atLeastLessThan_iff connex leD le_less_linear le_neq_implies_less le_trans nat_le_Suc_less_imp)
      by (metis atLeastLessThan_iff connex leD leI le_neq_implies_less le_trans nat_le_Suc_less_imp not_less_eq_eq)

    lemma PARTITIONED_FINALLY2: "\<not>(i<j) \<Longrightarrow> \<not> xs!j\<^bold>>xs!l \<Longrightarrow> AUX_SMALLER (Not oo (\<^bold>>)) l h xs (i-1) \<Longrightarrow> AUX_NOTSM (\<^bold>>) l h xs (j+1) \<Longrightarrow> partitioned (xs!l) (swap xs l j) l h j"
      unfolding partitioned_def AUX_SMALLER_def AUX_NOTSM_def
      apply (simp add: unfold_lt_to_le swap_nth; safe; simp)
      subgoal using connex by blast
      subgoal by (meson connex dual_order.order_iff_strict greaterThanAtMost_iff leI less_le_trans nat_le_Suc_less_imp)
      subgoal by (meson connex dual_order.order_iff_strict greaterThanAtMost_iff leI less_le_trans nat_le_Suc_less_imp)
      done
      
          
    definition "mop_C_idx C xs i j \<equiv> doN { ASSERT (i<length xs \<and> j<length xs); RETURN (C (xs!i) (xs!j)) }"           
        

    definition "find_next_unguarded C xs l h i\<^sub>0 \<equiv> doN {
      ASSERT(l<length xs \<and> l\<le>i\<^sub>0 \<and> i\<^sub>0<h \<and> h\<le>length xs \<and> (\<exists>si\<in>{i\<^sub>0<..<h}. \<not> C (xs!si) (xs!l)) );
      monadic_WHILEIT (\<lambda>i. i\<^sub>0<i \<and> i<h \<and> (\<forall>j\<in>{i\<^sub>0<..<i}. C (xs!j) (xs!l))) 
        (\<lambda>i. doN { ASSERT (i\<noteq>l); mop_C_idx C xs i l } ) 
        (\<lambda>i. doN { ASSERT (i<h); RETURN (i+1)}) 
        (i\<^sub>0 + 1)
    }"  

    definition "find_next_guarded C xs l h i\<^sub>0 \<equiv> doN {
      ASSERT(l<length xs \<and> l\<le>i\<^sub>0 \<and> i\<^sub>0<h \<and> h\<le>length xs );
      monadic_WHILEIT (\<lambda>i. i\<^sub>0<i \<and> i<h \<and> (\<forall>j\<in>{i\<^sub>0<..<i}. C (xs!j) (xs!l))) 
        (\<lambda>i. if i < h - 1 then doN { ASSERT (i\<noteq>l); mop_C_idx C xs i l } else RETURN False) 
        (\<lambda>i. doN { ASSERT (i<h); RETURN (i+1)}) 
        (i\<^sub>0 + 1)
    }"  

    definition "first_find_next C xs l j h i\<^sub>0 \<equiv> doN {
      ASSERT (j<h);    
      if j+1=h then find_next_guarded C xs l h i\<^sub>0
      else find_next_unguarded C xs l h i\<^sub>0
    }"  
    
        
    definition "find_prev_unguarded C xs l j\<^sub>0 \<equiv> doN {
      ASSERT(l<length xs \<and> l+1<j\<^sub>0 \<and> j\<^sub>0\<le>length xs \<and> (\<exists>si\<in>{l<..<j\<^sub>0}. \<not>C (xs!si) (xs!l)) \<and> j\<^sub>0\<ge>1 );
      monadic_WHILEIT (\<lambda>j. l<j \<and> j<j\<^sub>0 \<and> (\<forall>k\<in>{j<..<j\<^sub>0}. C (xs!k) (xs!l))) 
        (\<lambda>j. mop_C_idx C xs j l) 
        (\<lambda>j. doN {ASSERT(j\<ge>1); RETURN (j-1)}) 
        (j\<^sub>0 - 1)
    }"  
      
    definition "find_prev_guarded C xs l j\<^sub>0 \<equiv> doN {
      ASSERT(l<length xs \<and> l+1<j\<^sub>0 \<and> j\<^sub>0\<le>length xs \<and> j\<^sub>0\<ge>1 );
      monadic_WHILEIT (\<lambda>j. l<j \<and> j<j\<^sub>0 \<and> (\<forall>k\<in>{j<..<j\<^sub>0}. C (xs!k) (xs!l))) 
        (\<lambda>j. if l+1<j then mop_C_idx C xs j l else RETURN False ) 
        (\<lambda>j. doN {ASSERT(j\<ge>1); RETURN (j-1)}) 
        (j\<^sub>0 - 1)
    }"  
    
    definition "first_find_prev C xs l i h \<equiv> doN {
      ASSERT (l<h);
      if i=l+1 then find_prev_guarded C xs l h
      else find_prev_unguarded C xs l h
    }"  

           
    lemma find_next_unguarded_rl: "\<lbrakk> AUX_SMALLER C l h xs i\<^sub>0; RIGHT_GUARD C l h xs i\<^sub>0 \<rbrakk>
      \<Longrightarrow> find_next_unguarded C xs l h i\<^sub>0 \<le> SPEC (\<lambda>i. i\<^sub>0<i \<and> i<h \<and> AUX_SMALLER C l h xs (i-1) \<and> \<not>C (xs!i) (xs!l) )"  
      unfolding find_next_unguarded_def AUX_SMALLER_def RIGHT_GUARD_def mop_C_idx_def
      apply (refine_vcg monadic_WHILEIT_rule[where R="measure (\<lambda>i. length xs - i)"])
      apply clarsimp_all
      subgoal 
        apply safe
        apply simp_all
        subgoal by (metis Suc_lessI greaterThanLessThan_iff less_antisym)
        subgoal by (metis greaterThanLessThan_iff less_SucE)
        subgoal by auto
        done
      done

    lemma find_next_guarded_rl: "\<lbrakk> AUX_SMALLER C l h xs i\<^sub>0; i\<^sub>0+1<h \<rbrakk>
      \<Longrightarrow> find_next_guarded C xs l h i\<^sub>0 \<le> SPEC (\<lambda>i. i\<^sub>0<i \<and> i<h \<and> AUX_SMALLER C l h xs (i-1) \<and> ( i=h-1 \<or> \<not>C (xs!i) (xs!l) ) )"  
      unfolding find_next_guarded_def AUX_SMALLER_def RIGHT_GUARD_def mop_C_idx_def
      apply (refine_vcg monadic_WHILEIT_rule[where R="measure (\<lambda>i. length xs - i)"])
      apply clarsimp_all
      subgoal by (fastforce elim: less_SucE)
      subgoal by auto  
      done
      
   lemma first_find_next_rl: "\<lbrakk> AUX_NOTSM (Not oo C) l h xs (j+1); i\<^sub>0+1<h; AUX_SMALLER C l h xs i\<^sub>0; i\<^sub>0+1 < h \<rbrakk> \<Longrightarrow>
      first_find_next C xs l j h i\<^sub>0 \<le> SPEC (\<lambda>i. i\<^sub>0<i \<and> i<h \<and> AUX_SMALLER C l h xs (i-1) \<and> ( i=h-1 \<or> \<not>C (xs!i) (xs!l) ))"
      unfolding first_find_next_def
      apply (refine_vcg find_next_guarded_rl find_next_unguarded_rl) 
      apply (auto simp: RIGHT_GUARD_init)
      apply (auto simp: AUX_NOTSM_def)
      done
      
      
            
    lemma find_prev_unguarded_rl: "\<lbrakk> AUX_NOTSM C l h xs j\<^sub>0; LEFT_GUARD C l xs j\<^sub>0 \<rbrakk> \<Longrightarrow>
      find_prev_unguarded C xs l j\<^sub>0 \<le> SPEC (\<lambda>j. l<j \<and> j<j\<^sub>0 \<and> AUX_NOTSM C l h xs (j+1) \<and> \<not>C (xs!j) (xs!l))"
      unfolding find_prev_unguarded_def AUX_NOTSM_def LEFT_GUARD_def mop_C_idx_def
      apply (refine_vcg monadic_WHILEIT_rule[where R="measure (\<lambda>i. i)"])
      apply simp_all
      apply auto []
      apply auto []
      apply auto []
      subgoal
        apply safe
        apply simp_all
        subgoal by (metis (full_types) greaterThanLessThan_iff leD le_less_linear le_neq_implies_less nat_le_Suc_less_imp)
        subgoal by (metis greaterThanLessThan_iff leD linorder_neqE_nat nat_le_Suc_less_imp)
        subgoal by auto
        done
      done
      

    lemma find_prev_guarded_rl: "\<lbrakk> AUX_NOTSM C l h xs j\<^sub>0; l+1 < j\<^sub>0 \<rbrakk> \<Longrightarrow>
      find_prev_guarded C xs l j\<^sub>0 \<le> SPEC (\<lambda>j. l<j \<and> j<j\<^sub>0 \<and> AUX_NOTSM C l h xs (j+1) \<and> (j = l+1 \<or> \<not>C (xs!j) (xs!l)))"
      unfolding find_prev_guarded_def AUX_NOTSM_def LEFT_GUARD_def mop_C_idx_def
      apply (refine_vcg monadic_WHILEIT_rule[where R="measure (\<lambda>i. i)"])
      apply simp_all
      apply auto []
      apply auto []
      apply (metis Suc_le_lessD atLeastLessThan_iff atLeastSucLessThan_greaterThanLessThan 
              greaterThanLessThan_iff leD le_less_linear less_imp_diff_less nat_le_Suc_less_imp nat_neq_iff)
      apply auto []
      done
      
      
    lemma first_find_prev_rl: "\<lbrakk> AUX_SMALLER (Not oo C) l h xs (i-1); l<i; AUX_NOTSM C l h xs j\<^sub>0; l+1 < j\<^sub>0 \<rbrakk> \<Longrightarrow>
      first_find_prev C xs l i j\<^sub>0 \<le> SPEC (\<lambda>j. l<j \<and> j<j\<^sub>0 \<and> AUX_NOTSM C l h xs (j+1) \<and> (j = l+1 \<or> \<not>C (xs!j) (xs!l)))"
      unfolding first_find_prev_def
      apply (refine_vcg find_prev_guarded_rl find_prev_unguarded_rl; assumption?) 
      apply (auto simp: LEFT_GUARD_init)
      done
 
       
      
           
    definition "part_right_invar xs\<^sub>0 l h \<equiv> \<lambda>(xs,i,j). 
        slice_eq_mset l h xs\<^sub>0 xs
      \<and> xs\<^sub>0!l = xs!l  
      \<and> l < h \<and> h\<le>length xs
      \<and> {i,j} \<subseteq> {l<..<h}
      \<and> AUX_SMALLER (\<^bold><) l h xs (i-1)
      \<and> AUX_NOTSM (Not oo (\<^bold><)) l h xs (j+1)
      \<and> \<not> xs!i \<^bold>< xs!l \<and> (i<j \<longrightarrow> xs!j \<^bold>< xs!l)
      "

    lemma part_right_invar_boundsD:
      assumes "part_right_invar xs\<^sub>0 l h (xs,i,j)"  
      shows "i<length xs" "j<length xs" "length xs\<^sub>0 = length xs" "i - Suc 0 < length xs" "l \<le> i-Suc 0" "i-Suc 0 < h" "xs\<^sub>0!l = xs!l"
      using assms unfolding part_right_invar_def AUX_SMALLER_def AUX_NOTSM_def
      apply (auto simp: slice_eq_mset_eq_length)
      done
      
    lemma part_right_invar_pres:
      assumes "part_right_invar xs\<^sub>0 l h (xs,i,j)" "i<j"  
      shows "AUX_SMALLER (\<^bold><) l h (swap xs i j) i"
        and "RIGHT_GUARD (\<^bold><) l h (swap xs i j) i"
        and "AUX_NOTSM (Not oo (\<^bold><)) l h (swap xs i j) j"
        and "LEFT_GUARD (Not oo (\<^bold><)) l (swap xs i j) j"
      using assms unfolding part_right_invar_def
      apply -
      subgoal by (auto simp: PV_SWAP)
      subgoal unfolding RIGHT_GUARD_def by (auto simp: swap_nth)
      subgoal by (auto simp: PV_SWAP)
      subgoal unfolding LEFT_GUARD_def by (auto simp: swap_nth)
      done
      

    lemma mop_list_safe_swap: "mop_list_swap xs i j = doN { ASSERT (i<length xs \<and> j<length xs); if i\<noteq>j then mop_list_swap xs i j else RETURN xs }" 
      by (auto simp: pw_eq_iff refine_pw_simps)
            
    definition "partition_right xs l h \<equiv> doN {
      ASSERT (l<h \<and> h\<le>length xs);
      
      i \<leftarrow> find_next_unguarded (\<^bold><) xs l h l;
      
      j \<leftarrow> first_find_prev (Not oo (\<^bold><)) xs l i h;

      let alrp = i\<ge>j;
      
      (xs,i,j)\<leftarrow> 
        WHILEIT 
          (part_right_invar xs l h) 
          (\<lambda>(xs,i,j). i<j) 
          (\<lambda>(xs,i,j). doN {
            ASSERT (i\<noteq>j);
            xs\<leftarrow>mop_list_swap xs i j;
            i\<leftarrow>find_next_unguarded (\<^bold><) xs l h i;
            j\<leftarrow>find_prev_unguarded (Not oo (\<^bold><)) xs l j;
            RETURN (xs,i,j)
          }) 
          (xs,i,j);

      ASSERT (i\<ge>1);          
      xs \<leftarrow> mop_list_swap xs l (i-1);
      
      ASSERT (\<forall>k\<in>{l..<i-1}. xs!k\<^bold><xs!(i-1)); \<comment> \<open>Not required by high-level spec, but to ensure that left side contains only truly smaller elements\<close>
      
      RETURN (alrp,i-1,xs)
    }"  
      
    lemma bincond_double_neg[simp]: "Not oo (Not oo C) = C" by (intro ext) auto
    
    
    lemma partition_right_correct: "partition_right xs l h \<le> partition_spec xs l h"            
      unfolding partition_right_def partition_spec_def
      apply (refine_vcg find_next_unguarded_rl first_find_prev_rl[where h=h] find_prev_unguarded_rl[where h=h]  WHILEIT_rule[where R="measure (\<lambda>(xs,i,j). j)"])
      apply (all \<open>(elim conjE)?, assumption?\<close>)
      apply (simp_all add: )
      
      apply (clarsimp_all simp: AUX_SMALLER_init AUX_NOTSM_init RIGHT_GUARD_from_prc part_right_invar_boundsD part_right_invar_pres)
      subgoal unfolding part_right_invar_def by auto 
      subgoal unfolding part_right_invar_def by auto 
      subgoal unfolding part_right_invar_def by auto
      subgoal unfolding part_right_invar_def AUX_SMALLER_def by (auto simp: swap_nth)
      subgoal unfolding part_right_invar_def AUX_SMALLER_def by auto
      subgoal 
        apply (erule PARTITIONED_FINALLY)
        unfolding part_right_invar_def 
        by clarsimp_all
      done  

      
      
      
    definition "part_left_invar xs\<^sub>0 l h \<equiv> \<lambda>(xs,i,j). 
        slice_eq_mset l h xs\<^sub>0 xs
      \<and> xs\<^sub>0!l = xs!l  
      \<and> l < h \<and> h\<le>length xs
      \<and> {i,j} \<subseteq> {l<..<h}
      \<and> AUX_SMALLER (Not oo (\<^bold>>)) l h xs (i-1)
      \<and> AUX_NOTSM (\<^bold>>) l h xs (j+1)
      \<and> \<not> xs!j \<^bold>> xs!l \<and> (i<j \<longrightarrow> xs!i \<^bold>> xs!l)
      "

    lemma part_left_invar_boundsD:
      assumes "part_left_invar xs\<^sub>0 l h (xs,i,j)"  
      shows "i<length xs" "j<length xs" "length xs\<^sub>0 = length xs" "i - Suc 0 < length xs" "l \<le> i-Suc 0" "i-Suc 0 < h" "xs\<^sub>0!l = xs!l" "l\<le>j" "j<h"
      using assms unfolding part_left_invar_def AUX_SMALLER_def AUX_NOTSM_def
      apply (auto simp: slice_eq_mset_eq_length)
      done
      
    lemma part_left_invar_pres:
      assumes "part_left_invar xs\<^sub>0 l h (xs,i,j)" "i<j"  
      shows "AUX_SMALLER (Not oo (\<^bold>>)) l h (swap xs i j) i"
        and "RIGHT_GUARD (Not oo (\<^bold>>)) l h (swap xs i j) i"
        and "AUX_NOTSM (\<^bold>>) l h (swap xs i j) j"
        and "LEFT_GUARD (\<^bold>>) l (swap xs i j) j"
      using assms unfolding part_left_invar_def
      apply -
      subgoal by (auto simp: PV_SWAP)
      subgoal unfolding RIGHT_GUARD_def by (auto simp: swap_nth)
      subgoal using PV_SWAP by fastforce
      subgoal unfolding LEFT_GUARD_def by (auto simp: swap_nth)
      done
      
      
    definition "partition_left xs l h \<equiv> doN {
      ASSERT (l<h \<and> h\<le>length xs);
      
      j \<leftarrow> find_prev_unguarded (\<^bold>>) xs l h;
      
      i \<leftarrow> first_find_next (Not oo (\<^bold>>)) xs l j h l;

      (xs,i,j)\<leftarrow> 
        WHILEIT 
          (part_left_invar xs l h) 
          (\<lambda>(xs,i,j). i<j) 
          (\<lambda>(xs,i,j). doN {
            ASSERT (i\<noteq>j);
            xs\<leftarrow>mop_list_swap xs i j;
            j\<leftarrow>find_prev_unguarded (\<^bold>>) xs l j;
            i\<leftarrow>find_next_unguarded (Not oo (\<^bold>>)) xs l h i;
            RETURN (xs,i,j)
          }) 
          (xs,i,j);
      
      ASSERT (l\<noteq>j);
      xs \<leftarrow> mop_list_swap xs l j;
      
      ASSERT (\<forall>k\<in>{j<..<h}. xs!k\<^bold>>xs!j); \<comment> \<open>Not required by high-level spec, but to ensure that right side contains only truly greater elements\<close>
      
      RETURN (False,j,xs)
    }"  
      
      
    lemma partition_left_correct: "partition_left xs l h \<le> partition_left_spec xs l h"            
      unfolding partition_left_def partition_spec_def partition_left_spec_def
      apply (refine_vcg find_next_unguarded_rl first_find_next_rl[where h=h] find_prev_unguarded_rl[where h=h]  WHILEIT_rule[where R="measure (\<lambda>(xs,i,j). j)"])
      apply (all \<open>(elim conjE)?, assumption?\<close>)
      apply (simp_all add: )
      apply (clarsimp_all simp: AUX_SMALLER_init AUX_NOTSM_init LEFT_GUARD_from_prc part_left_invar_boundsD part_left_invar_pres)  
      subgoal unfolding part_left_invar_def AUX_NOTSM_def by auto        
      subgoal unfolding part_left_invar_def AUX_NOTSM_def by auto        
      subgoal unfolding part_left_invar_def AUX_NOTSM_def by (auto simp: swap_nth)
      subgoal unfolding part_left_invar_def AUX_NOTSM_def by auto
      subgoal unfolding part_left_invar_def by auto
      subgoal 
        apply (erule PARTITIONED_FINALLY2)
        unfolding part_left_invar_def 
        by clarsimp_all
      done  
      

    text \<open>We use the guarded arithmetic operations on natural numbers, to avoid to many
      in-bounds conditions to be visible to the simplifier ... this would make the simplifier
      extremely slow when invoked from within Sepref in the next step.
    \<close>  
      
    definition "shuffle2 xs l h m \<equiv> doN {
      size \<leftarrow> mop_nat_sub h l;
      l_size \<leftarrow> mop_nat_sub m l;
      t_m1 \<leftarrow> mop_nat_add_bnd h m 1;
      r_size \<leftarrow> mop_nat_sub h t_m1;
      t_sd8 \<leftarrow> mop_nat_div size 8;
      
      let highly_unbal = l_size < t_sd8 \<or> r_size < t_sd8;
    
      if highly_unbal then doN {
        xs \<leftarrow> if l_size \<ge> is_threshold then doN {
          t_lsd4 \<leftarrow> mop_nat_div l_size 4;
          i_lls4 \<leftarrow> mop_nat_add_bnd h l t_lsd4; \<^cancel>\<open>l + l_size div 4\<close>
          i_mm1 \<leftarrow> mop_nat_sub m 1; \<^cancel>\<open>m-1\<close>
          i_mmls4 \<leftarrow> mop_nat_sub m t_lsd4; \<^cancel>\<open>m - l_size div 4\<close>
          
          xs \<leftarrow> shuffle_left xs l i_lls4;
          xs \<leftarrow> shuffle_left xs i_mm1 i_mmls4;
          
          if l_size > ninther_threshold then doN {
            i_l1 \<leftarrow> mop_nat_add_bnd h l 1;
            i_l2 \<leftarrow> mop_nat_add_bnd h l 2;
            i_mm2 \<leftarrow> mop_nat_sub m 2;
            i_mm3 \<leftarrow> mop_nat_sub m 3;
            
            i_lls41 \<leftarrow> mop_nat_add_bnd h i_lls4 1;
            i_lls42 \<leftarrow> mop_nat_add_bnd h i_lls4 2;
            i_mmls41 \<leftarrow> mop_nat_sub i_mmls4 1;             
            i_mmls42 \<leftarrow> mop_nat_sub i_mmls4 2;             
          
            xs \<leftarrow> shuffle_left xs i_l1 i_lls41;
            xs \<leftarrow> shuffle_left xs i_l2 i_lls42;
            xs \<leftarrow> shuffle_left xs i_mm2 i_mmls41;
            xs \<leftarrow> shuffle_left xs i_mm3 i_mmls42;
            RETURN xs
          } else RETURN xs
        } else RETURN xs;
        xs \<leftarrow> if r_size \<ge> is_threshold then doN {
          i_m1 \<leftarrow> mop_nat_add_bnd h m 1;
          i_h1 \<leftarrow> mop_nat_sub h 1;
          
          t_rsd4 \<leftarrow> mop_nat_div r_size 4;
          i_mp1 \<leftarrow> mop_nat_add_bnd h i_m1 t_rsd4;
          i_hm \<leftarrow> mop_nat_sub h t_rsd4;
        
          xs \<leftarrow> shuffle_right xs i_m1 i_mp1;
          xs \<leftarrow> shuffle_right xs i_h1 i_hm;
          if r_size > ninther_threshold then doN {
          
            i_m2 \<leftarrow> mop_nat_add_bnd h m 2;
            i_m3 \<leftarrow> mop_nat_add_bnd h m 3;
            i_h2 \<leftarrow> mop_nat_sub h 2;
            i_h3 \<leftarrow> mop_nat_sub h 3;
            i_hm1 \<leftarrow> mop_nat_sub i_hm 1;
            i_hm2 \<leftarrow> mop_nat_sub i_hm 2;
            i_mp2 \<leftarrow> mop_nat_add_bnd h i_mp1 1;
            i_mp3 \<leftarrow> mop_nat_add_bnd h i_mp1 2;
          
            xs \<leftarrow> shuffle_right xs i_m2 i_mp2;
            xs \<leftarrow> shuffle_right xs i_m3 i_mp3;
            xs \<leftarrow> shuffle_right xs i_h2 i_hm1;  
            xs \<leftarrow> shuffle_right xs i_h3 i_hm2;          
            RETURN xs
          } else RETURN xs
        } else RETURN xs;
        RETURN (True,xs)
      } else
        RETURN (False,xs)
    }"
      
    lemma shuffle2_aux: "\<lbrakk> ninther_threshold < m - l; l \<le> h; l \<le> m; m + 1 \<le> h\<rbrakk>  \<Longrightarrow> l + (m - l) div 4 + 1 \<le> h"
      apply simp
      done
    
    lemma mop_nat_simps:
      "a+b\<le>h \<Longrightarrow> mop_nat_add_bnd h a b = RETURN (a+b)"
      "b\<le>a \<Longrightarrow> mop_nat_sub a b = RETURN (a-b)"
      "b\<noteq>0 \<Longrightarrow> mop_nat_div a b = RETURN (a div b)" 
      by (simp_all add: mop_nat_defs)
      
    lemma shuffle2_refine: "shuffle2 xs l h m \<le> shuffle xs l h m"
    proof -

      have A: 
        "(shuffle_right,shuffle_right)\<in>Id \<rightarrow> nat_rel \<rightarrow> nat_rel \<rightarrow> \<langle>Id\<rangle>nres_rel" 
        "(shuffle_left,shuffle_left)\<in>Id \<rightarrow> nat_rel \<rightarrow> nat_rel \<rightarrow> \<langle>Id\<rangle>nres_rel"
        by (auto intro!: nres_relI)
      note A = A[param_fo]  
        
        
      {
        assume "l\<le>h" "l\<le>m" "m+1\<le>h"
        then have ?thesis
          unfolding shuffle2_def
          apply (simp split del: if_split add: Let_def mop_nat_simps cong: if_cong)
          unfolding shuffle_def Let_def
          apply (simp named_ss Main_ss: split del: if_split cong: if_cong)
          apply (split if_split; intro conjI impI; simp only: if_True if_False)
          apply (split if_split; intro conjI impI; simp only: if_True if_False)
          apply (all \<open>(cases "ninther_threshold < m - l"; simp only: if_True if_False)?\<close>)
          apply (all \<open>(cases "is_threshold \<le> h - Suc m"; simp only: if_True if_False)?\<close>)
          apply (all \<open>(cases "ninther_threshold < h - Suc m"; simp only: if_True if_False)?\<close>)
          apply (simp_all add: algebra_simps del: One_nat_def add: Suc_eq_plus1)
          apply (rule refine_IdD) 
          apply (refine_rcg A[THEN nres_relD]; (rule IdI)?; simp)
          apply (rule refine_IdD) 
          apply (refine_rcg A[THEN nres_relD]; (rule IdI)?; simp)
          apply (rule refine_IdD) 
          apply (refine_rcg A[THEN nres_relD]; (rule IdI)?; simp)
          done          
      } thus ?thesis
        unfolding shuffle_def by (simp only: pw_le_iff refine_pw_simps) blast 
    qed            

    text \<open>Again, we replace the nat arithmetic by assertion-guarded operations, to avoid 
      overwhelming the simplifier.\<close>    
    definition "move_pivot_to_front2 xs l h \<equiv> doN {
      ASSERT (l\<le>h \<and> h>0);
      
      size \<leftarrow> mop_nat_sub h l;
      s2 \<leftarrow> mop_nat_div size 2;
      
      if (size > ninther_threshold) then doN {
        \<^cancel>\<open>ASSERT (l+s2+1<h \<and> h\<ge>3 \<and> s2\<ge>1 \<and> s2<h );\<close>
        ASSERT (l+2\<le>h \<and> l+s2+1\<le>h \<and> l+s2\<ge>1 \<and> h\<ge>3 );
        xs\<leftarrow>sort_three xs l              (l + s2)      (h - 1);
        xs\<leftarrow>sort_three xs (l + 1)        (l + s2 - 1) (h - 2);
        xs\<leftarrow>sort_three xs (l + 2)        (l + s2 + 1) (h - 3);
        xs\<leftarrow>sort_three xs (l + s2 - 1) (l + s2)       (l + s2 + 1);
        ASSERT (l\<noteq>l+s2);
        xs \<leftarrow> mop_list_swap xs l (l+s2);
        \<^cancel>\<open>ASSERT (xs!l \<^bold>\<le> xs!(l + (s2 + 1)) \<and> xs!(l + (s2 - 1)) \<^bold>\<le> xs!l);\<close>
        RETURN xs
      } else doN {
        ASSERT (l+s2\<le>h \<and> h\<ge>1);
        sort_three xs (l+s2) l (h-1)
      }
    }"
    

    lemma move_pivot_to_front2_refine: "move_pivot_to_front2 xs l h \<le> move_pivot_to_front xs l h"    
      unfolding move_pivot_to_front2_def move_pivot_to_front_def Let_def mop_nat_defs
      apply (simp split del: if_split)
      apply (rule refine_IdD)
      apply refine_rcg
      apply refine_dref_type
      apply simp_all
      done
    

    text \<open>We explicitly introduce evaluation order of conditions that must be short-circuited.\<close>  
    definition "pdqsort_aux2 leftmost xs l h (d::nat) \<equiv> RECT (\<lambda>pdqsort_aux (leftmost,xs,l,h,d). doN {
      ASSERT (l\<le>h);
      
      if (h-l < pdq_is_threshold) then 
        pdq_guarded_sort_spec leftmost xs l h
      else doN {
        xs \<leftarrow> pivot_to_front_spec xs l h;

        ASSERT (\<not>leftmost \<longrightarrow> l>0);         
        if\<^sub>N (if leftmost then RETURN False else doN { ASSERT (l\<ge>1); b\<leftarrow>mop_cmp_idxs xs (l-1) l; RETURN (\<not>b) } ) then doN {
          (_,m,xs) \<leftarrow> partition_left_spec xs l h;
          ASSERT (m<h);
          pdqsort_aux (False,xs,m+1,h,d)
        } else doN {
          (alrp,m,xs) \<leftarrow> partition_spec xs l h;
          (unbal,xs) \<leftarrow> shuffle_spec xs l h m;
          
          ASSERT (0<d);
          let d = (if unbal then d-1 else d);
          
          (didsort,xs) \<leftarrow> 
            if d=0 then doN {xs \<leftarrow> fallback_sort_spec xs l h; RETURN (True,xs)}
            else if alrp \<and> \<not>unbal then doN {
              (r,xs) \<leftarrow> maybe_sort_spec xs l m;
              if r then doN {
                ASSERT (m<h);
                maybe_sort_spec xs (m+1) h
              } else RETURN (False,xs)
            } else RETURN (False,xs);
            
          if didsort then RETURN xs 
          else doN { \<^cancel>\<open>TODO: Test optimization of not sorting left partition again, if maybe_sort sorted it\<close>
            xs \<leftarrow> pdqsort_aux (leftmost,xs,l,m,d);
            ASSERT (m<h);
            xs \<leftarrow> pdqsort_aux (False,xs,m+1,h,d);
            RETURN xs
          } 
        }
      }
    
    }) (leftmost,xs,l,h,d)"

    (* TODO: Move. TODO: really refine2? *)      
    lemma ifN_refine[refine2]:
      assumes "b\<le>RETURN b'" "c\<le>\<Down>R c'" "d\<le>\<Down>R d'"
      shows "(if\<^sub>N b then c else d) \<le>\<Down>R (if b' then c' else d')"
      using assms if_bind_cond_refine by blast
    
    lemma pdqsort_aux2_refine: "pdqsort_aux2 leftmost xs l h d \<le> pdqsort_aux leftmost xs l h d"
      unfolding pdqsort_aux2_def pdqsort_aux_def
      apply (rule refine_IdD if_bind_cond_refine)
      apply refine_rcg
      apply refine_dref_type
      apply (all \<open>(simp named_ss HOL_ss: prod_rel_simp pair_in_Id_conv)?\<close>)
      apply (all \<open>(elim conjE)?\<close>)
      apply simp_all
      by auto
      
          
  end
  
  
  subsection \<open>Refinement to Isabelle-LLVM\<close>

  text \<open>Some boilerplate code for every subroutine.\<close>  
  
  context sort_impl_context begin
    
    sepref_register 
      left_find_prev_ug: "find_prev_unguarded (\<^bold>>)"
      left_find_next_ug: "find_next_unguarded (Not oo (\<^bold>>))"
      left_find_next_g: "find_next_guarded (Not oo (\<^bold>>))"
      left_first_find_next: "first_find_next (Not oo (\<^bold>>))"

      
    lemma mop_C_idx_unfolds:
      "mop_C_idx (\<^bold>>) xs i j = mop_cmp_idxs xs j i"                                                             
      "mop_C_idx (Not oo (\<^bold>>)) xs i j = doN { b\<leftarrow>mop_cmp_idxs xs j i; RETURN (\<not>b) }"  
      "mop_C_idx (\<^bold><) xs i j = mop_cmp_idxs xs i j"                                                             
      "mop_C_idx (Not oo (\<^bold><)) xs i j = doN { b\<leftarrow>mop_cmp_idxs xs i j; RETURN (\<not>b) }"  
      unfolding mop_C_idx_def
      by (auto simp: pw_eq_iff refine_pw_simps)
      
    sepref_def left_find_prev_ug_impl [llvm_inline] is "uncurry2 (PR_CONST (find_prev_unguarded (\<^bold>>)))" :: "arr_assn\<^sup>k *\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k \<rightarrow>\<^sub>a size_assn"
      unfolding find_prev_unguarded_def mop_C_idx_unfolds PR_CONST_def
      apply (annot_snat_const "TYPE(size_t)")
      by sepref

    sepref_def left_find_next_ug_impl [llvm_inline] is "uncurry3 (PR_CONST (find_next_unguarded (Not oo (\<^bold>>))))" :: "arr_assn\<^sup>k *\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k \<rightarrow>\<^sub>a size_assn"
      unfolding find_next_unguarded_def mop_C_idx_unfolds PR_CONST_def
      apply (annot_snat_const "TYPE(size_t)")
      by sepref

    sepref_def left_find_next_g_impl [llvm_inline] is "uncurry3 (PR_CONST (find_next_guarded (Not oo (\<^bold>>))))" :: "arr_assn\<^sup>k *\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k \<rightarrow>\<^sub>a size_assn"
      unfolding find_next_guarded_def mop_C_idx_unfolds PR_CONST_def
      apply (annot_snat_const "TYPE(size_t)")
      by sepref
            
    sepref_def left_first_find_next_impl [llvm_inline] is "uncurry4 (PR_CONST (first_find_next (Not oo (\<^bold>>))))" :: "arr_assn\<^sup>k *\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k \<rightarrow>\<^sub>a size_assn"
      unfolding first_find_next_def PR_CONST_def
      apply (annot_snat_const "TYPE(size_t)")
      by sepref
      

    sepref_def partition_left_impl is "uncurry2 (PR_CONST partition_left)" :: "arr_assn\<^sup>d *\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn \<times>\<^sub>a size_assn \<times>\<^sub>a arr_assn"
      unfolding partition_left_def PR_CONST_def
      by sepref
      

    thm partition_right_def  
      
    sepref_register 
      right_find_prev_ug: "find_prev_unguarded (Not oo (\<^bold><))"
      right_find_next_ug: "find_next_unguarded (\<^bold><)"
      right_find_next_g: "find_prev_guarded (Not oo (\<^bold><))"
      right_first_find_next: "first_find_prev (Not oo (\<^bold><))"
      
      
    sepref_def right_find_prev_ug_impl [llvm_inline] is "uncurry2 (PR_CONST (find_prev_unguarded (Not oo (\<^bold><))))" :: "arr_assn\<^sup>k *\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k \<rightarrow>\<^sub>a size_assn"
      unfolding find_prev_unguarded_def mop_C_idx_unfolds PR_CONST_def
      apply (annot_snat_const "TYPE(size_t)")
      by sepref

    sepref_def right_find_next_ug_impl [llvm_inline] is "uncurry3 (PR_CONST (find_next_unguarded (\<^bold><)))" :: "arr_assn\<^sup>k *\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k \<rightarrow>\<^sub>a size_assn"
      unfolding find_next_unguarded_def mop_C_idx_unfolds PR_CONST_def
      apply (annot_snat_const "TYPE(size_t)")
      by sepref

    sepref_def right_find_prev_g_impl [llvm_inline] is "uncurry2 (PR_CONST (find_prev_guarded (Not oo (\<^bold><))))" :: "arr_assn\<^sup>k *\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k \<rightarrow>\<^sub>a size_assn"
      unfolding find_prev_guarded_def mop_C_idx_unfolds PR_CONST_def
      apply (annot_snat_const "TYPE(size_t)")
      by sepref
            
    sepref_def right_first_find_prev_impl [llvm_inline] is "uncurry3 (PR_CONST (first_find_prev (Not oo (\<^bold><))))" :: "arr_assn\<^sup>k *\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k \<rightarrow>\<^sub>a size_assn"
      unfolding first_find_prev_def PR_CONST_def
      apply (annot_snat_const "TYPE(size_t)")
      by sepref
      
    sepref_def partition_right_impl [llvm_inline] is "uncurry2 (PR_CONST partition_right)" :: "arr_assn\<^sup>d *\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn \<times>\<^sub>a size_assn \<times>\<^sub>a arr_assn"
      unfolding partition_right_def PR_CONST_def
      apply (rewrite at "mop_list_swap _ _ (_-1)" mop_list_safe_swap)
      apply (annot_snat_const "TYPE(size_t)")
      by sepref

    sepref_register shuffle2  
      
    sepref_def shuffle_impl [llvm_inline] is "uncurry3 shuffle2"   :: "arr_assn\<^sup>d *\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn \<times>\<^sub>a arr_assn"
      unfolding shuffle2_def PR_CONST_def shuffle_left_def shuffle_right_def
      apply (annot_snat_const "TYPE(size_t)")
      by sepref
            
    sepref_register sort_three  
      
    sepref_def sort_three_impl [llvm_inline] is "uncurry3 (PR_CONST sort_three)"   :: "arr_assn\<^sup>d *\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k \<rightarrow>\<^sub>a arr_assn"
      unfolding sort_three_def sort_two_def PR_CONST_def
      by sepref
      
    sepref_def move_pivot_to_front_impl [llvm_inline] is "uncurry2 (PR_CONST move_pivot_to_front2)" :: "arr_assn\<^sup>d *\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k \<rightarrow>\<^sub>a arr_assn"
      unfolding move_pivot_to_front2_def PR_CONST_def
      apply (annot_snat_const "TYPE(size_t)")
      by sepref
      

    sepref_register pivot_to_front_spec partition_left_spec partition_spec shuffle_spec fallback_sort_spec
    
    lemma move_pivot_to_front2_refine': "(PR_CONST move_pivot_to_front2, PR_CONST pivot_to_front_spec)\<in>Id\<rightarrow>Id\<rightarrow>Id\<rightarrow>\<langle>Id\<rangle>nres_rel"
    proof - 
      note move_pivot_to_front2_refine also note move_pivot_to_front_refine 
      finally show ?thesis by (auto intro!: nres_relI)
    qed

    lemma partition_left_refine': "(PR_CONST partition_left, PR_CONST partition_left_spec) \<in> Id\<rightarrow>Id\<rightarrow>Id\<rightarrow>\<langle>Id\<rangle>nres_rel"
      using partition_left_correct by (auto intro!: nres_relI)
    
    lemma partition_right_refine': "(PR_CONST partition_right, PR_CONST partition_spec) \<in> Id\<rightarrow>Id\<rightarrow>Id\<rightarrow>\<langle>Id\<rangle>nres_rel"
      using partition_right_correct by (auto intro!: nres_relI)
      
    lemma shuffle_refine': "(shuffle2, shuffle_spec) \<in> Id\<rightarrow>Id\<rightarrow>Id\<rightarrow>Id\<rightarrow>\<langle>Id\<rangle>nres_rel"  
    proof -
      note shuffle2_refine also note shuffle_correct 
      finally show ?thesis by (auto intro!: nres_relI) 
    qed
      
    lemma heapsort_refine_fbs': "(PR_CONST heapsort,PR_CONST fallback_sort_spec) \<in> Id \<rightarrow> Id \<rightarrow> Id \<rightarrow> \<langle>Id\<rangle>nres_rel"  
      unfolding fallback_sort_spec_def PR_CONST_def
      using heapsort_correct'[OF IdI IdI IdI] by (auto intro!: nres_relI)
            
    lemmas [sepref_fr_rules] = 
      move_pivot_to_front_impl.refine[FCOMP move_pivot_to_front2_refine']
      partition_left_impl.refine[FCOMP partition_left_refine']
      partition_right_impl.refine[FCOMP partition_right_refine']
      shuffle_impl.refine[FCOMP shuffle_refine']
      heapsort_hnr[FCOMP heapsort_refine_fbs']
    
    sepref_register pdqsort_aux
    sepref_def pdqsort_aux_impl [llvm_inline] is "uncurry4 (PR_CONST pdqsort_aux2)" :: "bool1_assn\<^sup>k *\<^sub>a arr_assn\<^sup>d *\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k \<rightarrow>\<^sub>a arr_assn"
      unfolding pdqsort_aux2_def PR_CONST_def
      supply [[goals_limit = 1]]
      apply (annot_snat_const "TYPE(size_t)")
      by sepref
            
    lemma pdqsort_aux2_refine': "(PR_CONST pdqsort_aux2, PR_CONST pdqsort_aux) \<in> Id \<rightarrow> Id \<rightarrow> Id \<rightarrow> Id \<rightarrow> Id \<rightarrow> \<langle>Id\<rangle>nres_rel"  
      using pdqsort_aux2_refine by (auto intro: nres_relI)
      
    lemmas [sepref_fr_rules] = pdqsort_aux_impl.refine[FCOMP pdqsort_aux2_refine']
      
      
      
    sepref_register pdqsort  
    sepref_def pdqsort_impl is "uncurry2 (PR_CONST pdqsort)" :: "arr_assn\<^sup>d *\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k \<rightarrow>\<^sub>a arr_assn"
      unfolding pdqsort_def PR_CONST_def
      apply (annot_snat_const "TYPE(size_t)")
      by sepref
                        
  end

end
