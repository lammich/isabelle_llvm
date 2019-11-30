theory Sorting_Quicksort_Scheme
imports Sorting_Setup Sorting_Partially_Sorted
begin


  abbreviation "is_threshold \<equiv> 16::nat"

  context weak_ordering begin

    definition "partition1_spec xs \<equiv> doN { 
      ASSERT (length xs \<ge> 4); 
      SPEC (\<lambda>(xs1,xs2). mset xs = mset xs1 + mset xs2 \<and> xs1\<noteq>[] \<and> xs2\<noteq>[] \<and> slice_LT (\<^bold>\<le>) xs1 xs2)
    }"
    definition introsort_aux1 :: "'a list \<Rightarrow> nat \<Rightarrow> 'a list nres" where "introsort_aux1 xs d \<equiv> RECT (\<lambda>introsort_aux1 (xs,d). doN {
      if length xs > is_threshold then doN {
        if d=0 then
          SPEC (sort_spec (\<^bold><) xs)
        else doN {
          (xs1,xs2)\<leftarrow>partition1_spec xs;
          xs1 \<leftarrow> introsort_aux1 (xs1,d-1);
          xs2 \<leftarrow> introsort_aux1 (xs2,d-1);
          RETURN (xs1@xs2)
        }
      }
      else
        RETURN xs
    }) (xs,d)"
    
    lemma slice_strict_LT_imp_LE: "slice_LT (\<^bold><) xs ys \<Longrightarrow> slice_LT (le_by_lt (\<^bold><)) xs ys"  
      apply (erule slice_LT_mono)
      by (meson le_by_lt_def wo_less_asym)
      
    lemma introsort_aux1_correct: "introsort_aux1 xs d \<le> SPEC (\<lambda>xs'. mset xs' = mset xs \<and> part_sorted_wrt (le_by_lt (\<^bold><)) is_threshold xs')"
    
      unfolding introsort_aux1_def partition1_spec_def sort_spec_def
      
      apply (refine_vcg RECT_rule_arb[where V="measure (\<lambda>(xs,d). d+1)" and pre="\<lambda>xss (xs',d). xss=xs'"])
      apply (all \<open>(auto intro: sorted_wrt_imp_part_sorted part_sorted_wrt_init; fail)?\<close>)
      apply (rule order_trans)
      apply rprems
      applyS (simp)
      subgoal by auto
      apply refine_vcg
      subgoal
        apply (rule order_trans)
        apply rprems
        applyS simp
        subgoal by auto
        apply refine_vcg  
        subgoal by auto
        subgoal
          apply clarsimp
          apply (rule part_sorted_concatI; assumption?) 
          apply (subst slice_LT_mset_eq1, assumption)
          apply (subst slice_LT_mset_eq2, assumption)
          using le_by_lt by blast
        done
      done
    
      
    definition "partition2_spec xs \<equiv> doN { 
      ASSERT (length xs \<ge> 4); 
      SPEC (\<lambda>(xs',i). mset xs' = mset xs \<and> 0<i \<and> i<length xs \<and> slice_LT (\<^bold>\<le>) (take i xs') (drop i xs'))
    }"
      
    lemma partition2_spec_refine: "(xs,xs')\<in>Id \<Longrightarrow> partition2_spec xs \<le>\<Down>(br (\<lambda>(xs,i). (take i xs, drop i xs)) (\<lambda>(xs,i). 0<i \<and> i<length xs)) (partition1_spec xs')"
      unfolding partition1_spec_def partition2_spec_def
      apply (refine_vcg RES_refine)
      by (auto dest: mset_eq_length simp: in_br_conv simp flip: mset_append)
      
    definition introsort_aux2 :: "'a list \<Rightarrow> nat \<Rightarrow> 'a list nres" where "introsort_aux2 xs d \<equiv> RECT (\<lambda>introsort_aux (xs,d). doN {
      if length xs > is_threshold then doN {
        if d=0 then
          SPEC (sort_spec (\<^bold><) xs)
        else doN {
          (xs,m)\<leftarrow>partition2_spec xs;
          ASSERT (m\<le>length xs);
          xs1 \<leftarrow> introsort_aux (take m xs,d-1);
          xs2 \<leftarrow> introsort_aux (drop m xs,d-1);
          RETURN (xs1@xs2)
        }
      }
      else
        RETURN xs
    }) (xs,d)"
      
    lemma introsort_aux2_refine: "introsort_aux2 xs d \<le>\<Down>Id (introsort_aux1 xs d)"  
      unfolding introsort_aux2_def introsort_aux1_def
      apply (refine_rcg partition2_spec_refine)
      apply refine_dref_type
      apply (auto simp: in_br_conv)
      done
      
    
    definition "partition3_spec xs l h \<equiv> doN { 
      ASSERT (h-l\<ge>4 \<and> h\<le>length xs); 
      SPEC (\<lambda>(xs',i). slice_eq_mset l h xs' xs \<and> l<i \<and> i<h \<and> slice_LT (\<^bold>\<le>) (slice l i xs') (slice i h xs')) 
    }"
    
    lemma partition3_spec_refine: "(xsi,xs) \<in> slice_rel xs\<^sub>0 l h \<Longrightarrow> partition3_spec xsi l h  \<le>\<Down>(slice_rel xs\<^sub>0 l h \<times>\<^sub>r idx_shift_rel l) (partition2_spec xs)"
      unfolding partition3_spec_def partition2_spec_def
      apply (refine_vcg RES_refine)
      apply (auto simp: slice_rel_def in_br_conv) [2]
      apply (clarsimp simp: slice_rel_def in_br_conv)
      subgoal for xs'i ii
        apply (rule exI[where x="slice l h xs'i"])
        apply (rule conjI)
        subgoal by (auto simp: slice_eq_mset_def)
        apply (simp add: idx_shift_rel_alt)
        by (auto simp: slice_eq_mset_def take_slice drop_slice)
      done

      
    lemma partition3_spec_refine': "\<lbrakk>(xsi,xs) \<in> slicep_rel l h; xsi'=xsi; l'=l; h'=h\<rbrakk> 
      \<Longrightarrow> partition3_spec xsi l h  \<le>\<Down>(slice_rel xsi' l' h' \<times>\<^sub>r idx_shift_rel l') (partition2_spec xs)"
      unfolding partition3_spec_def partition2_spec_def
      apply (refine_vcg RES_refine)
      apply (auto simp: slicep_rel_def in_br_conv) [2]
      apply (clarsimp simp: slice_rel_def slicep_rel_def in_br_conv)
      subgoal for xs'i ii
        apply (rule exI[where x="slice l h xs'i"])
        apply (rule conjI)
        subgoal by (auto simp: slice_eq_mset_def)
        apply (simp add: idx_shift_rel_alt)
        by (auto simp: slice_eq_mset_def take_slice drop_slice)
      done
      
      
    definition introsort_aux3 :: "'a list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a list nres" where "introsort_aux3 xs l h d 
    \<equiv> RECT (\<lambda>introsort_aux (xs,l,h,d). doN {
        ASSERT (l\<le>h);
        if h-l > is_threshold then doN {
          if d=0 then
            slice_sort_spec (\<^bold><) xs l h
          else doN {
            (xs,m)\<leftarrow>partition3_spec xs l h;
            xs \<leftarrow> introsort_aux (xs,l,m,d-1);
            xs \<leftarrow> introsort_aux (xs,m,h,d-1);
            RETURN xs
          }
        }
        else
          RETURN xs
      }) (xs,l,h,d)"
      
    lemma introsort_aux3_refine: "(xsi,xs)\<in>slicep_rel l h \<Longrightarrow> introsort_aux3 xsi l h d \<le> \<Down>(slice_rel xsi l h) (introsort_aux2 xs d)"  
      unfolding introsort_aux3_def introsort_aux2_def
      
      supply recref = RECT_dep_refine[where 
          R="\<lambda>_. {((xsi::'a list, l, h, di::nat), (xs, d)). (xsi, xs) \<in> slicep_rel l h \<and> di=d}" and
          S="\<lambda>_ (xsi::'a list, l, h, di::nat). slice_rel xsi l h" and
          arb\<^sub>0 = "()"
          ]

      apply (refine_rcg 
        recref 
        partition3_spec_refine'
        slice_sort_spec_refine_sort'
        ; (rule refl)?
        )

      subgoal by auto
      subgoal by auto
      subgoal by (auto simp: slicep_rel_def)
      subgoal by (auto simp: slicep_rel_def)
      subgoal by auto
      subgoal by auto
      subgoal by auto
      subgoal by auto
      subgoal by auto
      subgoal by auto
      apply (rprems)
      subgoal by (auto simp: slice_rel_alt idx_shift_rel_def slicep_rel_take)
      apply rprems  
      subgoal by (auto simp: slice_rel_alt idx_shift_rel_def slicep_rel_eq_outside_range slicep_rel_drop)
      subgoal
        apply (clarsimp simp: slice_rel_alt idx_shift_rel_def)
        apply (rule conjI)
        subgoal
          apply (rule slicep_rel_append)
          apply (subst slicep_rel_eq_outside_range; assumption?) 
          by auto 
        subgoal 
          apply (drule (1) eq_outside_range_gen_trans[OF _ _ refl refl])
          apply (erule (1) eq_outside_range_gen_trans)
          apply (auto simp: max_def algebra_simps slicep_rel_def split: if_splits)
          done 
        done
      subgoal by (auto simp: slice_rel_alt eq_outside_range_triv slicep_rel_def)
      done
    

    definition "slice_part_sorted_spec xsi l h \<equiv> doN { ASSERT (l\<le>h \<and> h\<le>length xsi); SPEC (\<lambda>xsi'. 
        eq_outside_range xsi' xsi l h 
      \<and> mset (slice l h xsi') = mset (slice l h xsi) 
      \<and> part_sorted_wrt (le_by_lt (\<^bold><)) is_threshold (slice l h xsi'))}"
    
          
    lemma introsort_aux3_correct: "introsort_aux3 xsi l h d \<le> slice_part_sorted_spec xsi l h"
    proof -
    
(*      have "(xsi, slice l h xsi) \<in> slicep_rel l h"
        unfolding slicep_rel_def apply auto
        *)
    
      have A: "\<Down> (slice_rel xsi l h) (SPEC (\<lambda>xs'. mset xs' = mset (slice l h xsi) \<and> part_sorted_wrt (le_by_lt (\<^bold><)) 16 xs'))
        \<le> slice_part_sorted_spec xsi l h"
        apply (clarsimp simp: slice_part_sorted_spec_def pw_le_iff refine_pw_simps)
        apply (auto simp: slice_rel_alt  slicep_rel_def)
        done
    
      note introsort_aux3_refine[of xsi "slice l h xsi" l h d]
      also note introsort_aux2_refine
      also note introsort_aux1_correct
      also note A
      finally show ?thesis
        apply (clarsimp simp: slicep_rel_def slice_part_sorted_spec_def)
        by (auto simp: pw_le_iff refine_pw_simps)
        
    qed    
      

    text \<open>In the paper, we summarized steps 2 and 3. Here are the relevant lemmas: \<close>        
    lemma partition3_spec_alt: "partition3_spec xs l h = \<Down>(slice_rel xs l h \<times>\<^sub>r Id) (doN { ASSERT (l\<le>h \<and> h\<le>length xs); (xs\<^sub>1,xs\<^sub>2) \<leftarrow> partition1_spec (slice l h xs); RETURN (xs\<^sub>1@xs\<^sub>2, l+length xs\<^sub>1) })"  
      unfolding partition3_spec_def partition1_spec_def
      apply (auto simp: pw_eq_iff refine_pw_simps)
      apply (auto simp: slice_eq_mset_def slice_rel_def in_br_conv)
      subgoal
        by (smt Sorting_Misc.slice_len diff_is_0_eq leD le_add_diff_inverse less_imp_le_nat less_le_trans list.size(3) mset_append slice_append)
      subgoal by (metis mset_append)
      subgoal
        by (metis Misc.slice_len add_le_cancel_left drop_all drop_append_miracle leI le_add_diff_inverse)
      subgoal
        by (metis Misc.slice_def add_diff_cancel_left' append_assoc append_eq_conv_conj drop_slice drop_take drop_take_drop_unsplit)
      done

    corollary partition3_spec_alt': "partition3_spec xs l h = \<Down>({((xsi',m),(xs\<^sub>1,xs\<^sub>2)). (xsi',xs\<^sub>1@xs\<^sub>2)\<in>slice_rel xs l h \<and> m=l + length xs\<^sub>1 }) (doN { ASSERT (l\<le>h \<and> h\<le>length xs); partition1_spec (slice l h xs)})"  
      unfolding partition3_spec_alt
      apply (auto simp: pw_eq_iff refine_pw_simps)
      done
      
    corollary partition3_spec_direct_refine: "\<lbrakk> h-l\<ge>4; (xsi,xs)\<in>slicep_rel l h \<rbrakk> \<Longrightarrow> partition3_spec xsi l h \<le> \<Down>({((xsi',m),(xs\<^sub>1,xs\<^sub>2)). (xsi',xs\<^sub>1@xs\<^sub>2)\<in>slice_rel xsi l h \<and> m=l + length xs\<^sub>1 }) (partition1_spec xs)"  
      unfolding partition3_spec_alt'
      apply (auto simp: pw_le_iff refine_pw_simps)
      apply (auto simp: slicep_rel_def)
      done
      
          
    lemma slice_part_sorted_spec_alt: "slice_part_sorted_spec xsi l h = \<Down> (slice_rel xsi l h) (doN { ASSERT(l\<le>h \<and> h\<le>length xsi); SPEC (\<lambda>xs'. mset xs' = mset (slice l h xsi) \<and> part_sorted_wrt (le_by_lt (\<^bold><)) 16 xs') })"
      apply (clarsimp simp: slice_part_sorted_spec_def pw_eq_iff refine_pw_simps)
      apply (auto simp: slice_rel_alt  slicep_rel_def eq_outside_rane_lenD)
      done

    (* Extracted this subgoal to present it in paper *)      
    lemma introsort_aux3_direct_refine_aux1': "(xs', xs\<^sub>1 @ xs\<^sub>2) \<in> slice_rel xs l h \<Longrightarrow> xs\<^sub>1 = slice l (l + length xs\<^sub>1) xs'"
      apply (clarsimp simp: slice_rel_def in_br_conv)
      by (metis Misc.slice_def add_diff_cancel_left' append.assoc append_eq_conv_conj append_take_drop_id)
      
    lemma introsort_aux3_direct_refine_aux1: "\<lbrakk>(xsi', xs\<^sub>1 @ xs\<^sub>2) \<in> slice_rel xsi l' h'\<rbrakk> \<Longrightarrow> (xsi', xs\<^sub>1) \<in> slicep_rel l' (l' + length xs\<^sub>1)"  
      apply (simp add: slicep_rel_def introsort_aux3_direct_refine_aux1')
      apply (auto simp: slice_rel_alt slicep_rel_def)
      by (metis Misc.slice_len ab_semigroup_add_class.add_ac(1) le_add1 length_append ordered_cancel_comm_monoid_diff_class.add_diff_inverse)
    
    lemma introsort_aux3_direct_refine: "(xsi,xs)\<in>slicep_rel l h \<Longrightarrow> introsort_aux3 xsi l h d \<le> \<Down>(slice_rel xsi l h) (introsort_aux1 xs d)"  
      unfolding introsort_aux3_def introsort_aux1_def
      
      supply [refine del] = RECT_refine
      
      supply recref = RECT_dep_refine[where 
          R="\<lambda>_. {((xsi::'a list, l, h, di::nat), (xs, d)). (xsi, xs) \<in> slicep_rel l h \<and> di=d}" and
          S="\<lambda>_ (xsi::'a list, l, h, di::nat). slice_rel xsi l h" and
          arb\<^sub>0 = "()"
          ]

      apply (refine_rcg 
        recref
        slice_sort_spec_refine_sort'
        partition3_spec_direct_refine
        ; (rule refl)?
        )

      subgoal by auto
      subgoal by auto
      subgoal by (auto simp: slicep_rel_def)
      subgoal by (auto simp: slicep_rel_def)
      subgoal by auto
      subgoal by auto
      subgoal by auto
      subgoal by auto
      subgoal by auto
      subgoal by auto
      subgoal by auto
      apply (rprems)
      subgoal by (clarsimp simp: introsort_aux3_direct_refine_aux1)
      apply rprems  
      subgoal
        apply (auto simp: slice_rel_alt slicep_rel_def)
        subgoal by (metis Misc.slice_def drop_append_miracle drop_slice eq_outside_range_def)
        subgoal by (metis Nat.add_diff_assoc Sorting_Misc.slice_len add_diff_cancel_left' add_le_cancel_left diff_add_zero diff_is_0_eq length_append)
        subgoal by (simp add: eq_outside_rane_lenD)
        done
      subgoal
        apply (clarsimp simp: slice_rel_alt idx_shift_rel_def)
        apply (rule conjI)
        subgoal
          apply (rule slicep_rel_append)
          apply (subst slicep_rel_eq_outside_range; assumption?) 
          by auto 
        subgoal 
          apply (drule (1) eq_outside_range_gen_trans[OF _ _ refl refl])
          apply (erule (1) eq_outside_range_gen_trans)
          apply (auto simp: max_def algebra_simps slicep_rel_def split: if_splits)
          done 
        done
      subgoal by (auto simp: slice_rel_alt eq_outside_range_triv slicep_rel_def)
      done
      
      
      
      
      
      
      
    
    definition "final_sort_spec xs l h \<equiv> doN {
      ASSERT (h-l>1 \<and> part_sorted_wrt (le_by_lt (\<^bold><)) is_threshold (slice l h xs));
      slice_sort_spec (\<^bold><) xs l h
      }"
    
    definition "introsort3 xs l h \<equiv> doN {
      ASSERT(l\<le>h);
      if h-l>1 then doN {
        xs \<leftarrow> slice_part_sorted_spec xs l h;
        xs \<leftarrow> final_sort_spec xs l h;
        RETURN xs
      } else RETURN xs
    }"  
    
    
    lemma introsort3_correct: "introsort3 xs l h \<le> slice_sort_spec (\<^bold><) xs l h"
      apply (cases "l\<le>h \<and> h\<le>length xs")
      subgoal
        apply (cases "1<h-l")
        subgoal
          unfolding introsort3_def slice_part_sorted_spec_def final_sort_spec_def slice_sort_spec_alt
          by (auto simp: pw_le_iff refine_pw_simps eq_outside_rane_lenD elim: eq_outside_range_gen_trans[of _ _ l h _ l h l h, simplified])
        subgoal
          unfolding introsort3_def slice_sort_spec_alt slice_part_sorted_spec_def final_sort_spec_def
          by (simp add: eq_outside_range_triv sorted_wrt01)
        done
      subgoal            
        unfolding slice_sort_spec_alt
        apply refine_vcg 
        by simp
      done
      
      
          
  end  




end
