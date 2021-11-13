theory Sorting_Parsort
imports Sorting_Introsort Sorting_PDQ Sorting_Sample_Partition
begin

find_theorems nres_par
context weak_ordering begin
  
  definition "par_sort_aux3 xs n d \<equiv> RECT (\<lambda>par_sort_aux (xs,n,d::nat). doN {
    ASSERT (n = length xs);
    if d=0 \<or> n<par_sort_seq_threshold then
      pdqsort xs 0 n
    else doN {
      (xs,m) \<leftarrow> partition_pivot_sample xs n;
      bad \<leftarrow> bad_partition m n;
      (_,xs) \<leftarrow> WITH_SPLIT m xs (\<lambda>xs\<^sub>1 xs\<^sub>2. doN {
        ASSERT (length xs\<^sub>2 = length xs - m);
        ASSERT (d>0);
        ASSERT (n\<ge>m);
        (xs\<^sub>1,xs\<^sub>2) \<leftarrow> if bad then doN {
          xs\<^sub>1 \<leftarrow> par_sort_aux (xs\<^sub>1,m,d-1);
          xs\<^sub>2 \<leftarrow> par_sort_aux (xs\<^sub>2,n-m,d-1);
          RETURN (xs\<^sub>1,xs\<^sub>2)
        } else doM {
          nres_par par_sort_aux par_sort_aux (xs\<^sub>1,m,d-1) (xs\<^sub>2,n-m,d-1)
        };
          
        RETURN ((),xs\<^sub>1,xs\<^sub>2)
      });
      RETURN xs
    }
  }) (xs,n,d)"


  (* TODO: Move *)
  lemma introsort4_refines_spec: "\<lbrakk>(xs',xs)\<in>\<langle>Id\<rangle>list_rel; (l',l)\<in>nat_rel; (h',h)\<in>nat_rel\<rbrakk> \<Longrightarrow> introsort4 xs' l' h' \<le> \<Down> Id (slice_sort_spec (\<^bold><) xs l h)"
    using introsort4_correct by auto
  
  lemma pdqsort_refines_spec: "\<lbrakk>(xs',xs)\<in>\<langle>Id\<rangle>list_rel; (l',l)\<in>nat_rel; (h',h)\<in>nat_rel\<rbrakk> \<Longrightarrow> pdqsort xs' l' h' \<le> \<Down> Id (slice_sort_spec (\<^bold><) xs l h)"
    using pdqsort_correct by auto
  
  lemma par_sort_aux3_refine: "par_sort_aux3 xs n d \<le>\<Down>Id (par_sort_aux2 xs n d)"
    unfolding par_sort_aux3_def par_sort_aux2_def
    thm partition_pivot_correct partition_pivot_sample_correct
    apply (refine_rcg partition_pivot_sample_correct introsort4_refines_spec pdqsort_refines_spec)
    apply refine_dref_type
    by auto    
    
  (* TODO: Move *)  
  lemma slice_sort_spec_complete: "slice_sort_spec lt xs 0 (length xs) = SPEC (sort_spec lt xs)"  
    unfolding slice_sort_spec_def sort_spec_def
    apply clarsimp
    by (metis le_refl mset_eq_length slice_complete)
    
  lemma par_sort_aux3_correct:
    assumes "n=length xs"  
    shows "par_sort_aux3 xs n d \<le> SPEC (sort_spec (\<^bold><) xs)"
  proof -
    note par_sort_aux3_refine[where d=d]
    also note par_sort_aux2_refine[OF assms]
    also note par_sort_aux_correct
    also note slice_sort_spec_complete
    finally show ?thesis by simp 
  qed
    
  definition "par_sort xs n \<equiv> doN {
    if n>1 then doN {
      par_sort_aux3 xs n (Discrete.log n * 2)
    } else RETURN xs
  }"
  
  thm sort_spec_def
  
  lemma par_sort_correct: "n=length xs \<Longrightarrow> par_sort xs n \<le> SPEC (sort_spec (\<^bold><) xs)"
    unfolding par_sort_def 
    apply (refine_vcg par_sort_aux3_correct)
    by (simp add: sort_spec_def sorted_wrt01)
        
end    
    

definition "map_res f m \<equiv> doM { x\<leftarrow>m; return (f x) }"

lemma map_res_return[sepref_opt_simps2]: "map_res \<phi> (return x) = return (\<phi> x)"
  unfolding map_res_def by auto

lemma map_res_bind[sepref_opt_simps2]: "map_res \<phi> (doM {x\<leftarrow>m; f x}) = doM {x\<leftarrow>m; map_res \<phi> (f x)}"  
  unfolding map_res_def by auto

lemma map_res_prod_case[sepref_opt_simps2]: "map_res \<phi> (case p of (a,b) \<Rightarrow> f a b) = (case p of (a,b) \<Rightarrow> map_res \<phi> (f a b))" 
  by (rule prod.case_distrib)

lemmas [sepref_opt_simps2] = prod.sel  
  
  
definition [llvm_inline]: "ars_with_split_nores i a m \<equiv> doM {
  (a\<^sub>1,a\<^sub>2) \<leftarrow> ars_split i a;
  (_,_) \<leftarrow> m a\<^sub>1 a\<^sub>2;
  ars_join a\<^sub>1 a\<^sub>2;
  return a
}"

lemma ars_with_split_bind_unit[sepref_opt_simps2]: "doM {
  (uu::unit,xs) \<leftarrow> ars_with_split i a m;
  mm uu xs
} = doM {
  xs\<leftarrow>ars_with_split_nores i a (\<lambda>xs1 xs2. map_res snd (m xs1 xs2));
  mm () xs
}"
  unfolding ars_with_split_def ars_with_split_nores_def map_res_def
  apply (rule M_eqI)
  apply (simp add: mwp_def run_simps split!: prod.split mres.split)
  done
    
  
lemma sepref_adhoc_opt_case_add_const[sepref_opt_simps]:
  "(case case x of (a1c, a2c) \<Rightarrow> (c, a1c, a2c) of (uu, a, b) \<Rightarrow> m uu a b) = (case x of (a,b) \<Rightarrow> m c a b)" by simp

context sort_impl_context begin
  
  sepref_register bad_partition
  sepref_def bad_partition_impl [llvm_inline] is "uncurry bad_partition" :: "size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
    unfolding bad_partition_def
    apply (annot_snat_const "TYPE(size_t)")
    by sepref

  sepref_register par_sort_aux3
  
  sepref_def par_sort_aux_impl is "uncurry2 (PR_CONST par_sort_aux3)" 
    :: "[\<lambda>_. True]\<^sub>c (arr_assn)\<^sup>d *\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k  
    \<rightarrow> arr_assn [\<lambda>((ai,_),_) r. r=ai]\<^sub>c"
  unfolding par_sort_aux3_def PR_CONST_def
  supply [[goals_limit = 1]]
  apply (annot_snat_const "TYPE(size_t)")
  apply (rewrite RECT_cp_annot[where CP="\<lambda>(ai,_,_) r. r=ai"])
  
  supply [sepref_comb_rules] = hn_RECT_cp_annot_noframe
  apply sepref_dbg_preproc
  apply sepref_dbg_cons_init
  apply sepref_dbg_id
  apply sepref_dbg_monadify
  apply sepref_dbg_opt_init
  apply sepref_dbg_trans
  apply sepref_dbg_opt
  apply sepref_dbg_cons_solve
  apply sepref_dbg_cons_solve
  apply sepref_dbg_cons_solve_cp
  apply sepref_dbg_constraints
  done
  

  sepref_def par_sort_impl is "uncurry (PR_CONST par_sort)" 
    :: "[\<lambda>_. True]\<^sub>c (arr_assn)\<^sup>d *\<^sub>a size_assn\<^sup>k  
    \<rightarrow> arr_assn [\<lambda>(ai,_) r. r=ai]\<^sub>c"
    unfolding par_sort_def PR_CONST_def
    apply (annot_snat_const "TYPE(size_t)")
    supply [intro!] = introsort_depth_limit_in_bounds_aux 
    by sepref
  

  lemma par_sort_refine_aux: "(uncurry par_sort, uncurry (\<lambda>xs n. doN {ASSERT (n=length xs); SPEC (sort_spec (\<^bold><) xs) })) \<in> Id \<times>\<^sub>r Id \<rightarrow> \<langle>Id\<rangle>nres_rel"  
    using par_sort_correct[OF refl]
    by (auto simp: pw_nres_rel_iff pw_le_iff refine_pw_simps)
        
  theorem par_sort_impl_correct: "llvm_htriple (arr_assn xs xsi ** snat_assn n ni ** \<up>(n = length xs)) 
    (par_sort_impl xsi ni) 
    (\<lambda>r. \<up>(r=xsi) ** (EXS xs'. arr_assn xs' xsi ** \<up>(sort_spec (\<^bold><) xs xs')))"
    apply (cases "n=length xs"; simp)
    apply (rule cons_rule)
    supply R = par_sort_impl.refine[unfolded PR_CONST_def,FCOMP par_sort_refine_aux, to_hnr, simplified]
    supply R = R[of xs xsi n ni]
    apply (rule R[THEN hn_refineD])
    apply (simp)
    apply (simp add: hn_ctxt_def sep_algebra_simps)
    apply (auto simp add: hn_ctxt_def sep_algebra_simps pure_def invalid_assn_def)
    done
  

end

end
