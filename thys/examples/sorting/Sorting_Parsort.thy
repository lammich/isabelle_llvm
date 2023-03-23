section \<open>Parallel Quicksort\<close>
theory Sorting_Parsort
imports Sorting_Introsort Sorting_PDQ Sorting_Par_Partition
begin



context weak_ordering begin

  subsection \<open>Abstract Algorithm\<close>
  text \<open>We use a few straightforward refinement steps to develop the abstract parallel 
    quicksort algorithm\<close>
          
  definition bad_partition :: "nat \<Rightarrow> nat \<Rightarrow> bool nres" where 
  "bad_partition m n \<equiv> do {
    ASSERT (m\<le>n);
    RETURN (m < n div 8 \<or> n-m < n div 8)
  }"

  lemma bad_partition_triv: "m\<le>n \<Longrightarrow> bad_partition m n \<le> SPEC (\<lambda>_. True)"
    unfolding bad_partition_def
    apply refine_vcg
    by simp
  
  abbreviation "par_sort_seq_threshold::nat \<equiv> 100000"  
  abbreviation "ppar_chunk_size::nat \<equiv> 1000000"  
    
  definition "par_sort_aux xs d \<equiv> RECT (\<lambda>par_sort_aux (xs,d::nat). doN {
    let n = length xs;
    if d=0 \<or> n<par_sort_seq_threshold then
      slice_sort_spec (\<^bold><) xs 0 n
    else doN {
      (xs',m) \<leftarrow> partition3_spec xs 0 n;
      bad \<leftarrow> bad_partition m n;
      
      ASSERT (length xs' = length xs);
      (_,xs'') \<leftarrow> WITH_SPLIT m xs' (\<lambda>xs\<^sub>1 xs\<^sub>2. doN {
        ASSERT (length xs' = length xs\<^sub>1 + length xs\<^sub>2);
        (xs\<^sub>1',xs\<^sub>2') \<leftarrow> if bad then doN {
          xs\<^sub>1' \<leftarrow> par_sort_aux (xs\<^sub>1,d-1);
          ASSERT (length xs\<^sub>1' = length xs\<^sub>1);
          xs\<^sub>2' \<leftarrow> par_sort_aux (xs\<^sub>2,d-1);
          ASSERT (length xs\<^sub>2' = length xs\<^sub>2);
          RETURN (xs\<^sub>1',xs\<^sub>2')
        } else doN {
          xs\<^sub>1' \<leftarrow> par_sort_aux (xs\<^sub>1,d-1);
          ASSERT (length xs\<^sub>1' = length xs\<^sub>1);
          xs\<^sub>2' \<leftarrow> par_sort_aux (xs\<^sub>2,d-1);
          ASSERT (length xs\<^sub>2' = length xs\<^sub>2);
          RETURN (xs\<^sub>1',xs\<^sub>2')
        };
        RETURN ((),xs\<^sub>1',xs\<^sub>2')
      });
      RETURN xs''
    }
  }) (xs,d)"
  
  
  lemma par_sort_aux_correct: "par_sort_aux xs d \<le> slice_sort_spec (\<^bold><) xs 0 (length xs)"
    unfolding par_sort_aux_def 
    apply (subst if_cancel)
    apply (refine_vcg RECT_rule_arb[where V="measure (\<lambda>(_,d). d)" and pre="\<lambda>xss (xs,d). xss=xs"])
    apply simp_all [2]
    unfolding slice_sort_spec_def partition3_spec_def
    apply (refine_vcg bad_partition_triv)
    apply simp_all 
    apply (meson slice_eq_mset_all slice_eq_mset_def)
    apply (rule order_trans) apply (rprems)
    apply simp
    apply simp
    apply refine_vcg
    apply (clarsimp)
    apply (rule order_trans) apply (rprems)
    apply simp
    apply simp
    apply refine_vcg
    apply (clarsimp_all)
    subgoal for xs' xs\<^sub>2' xs\<^sub>1 xs\<^sub>2 xc x1b
      
      unfolding sort_spec_def slice_eq_mset_def slice_LT_def
      apply (auto simp: slice_complete' sorted_wrt_append le_by_lt slice_append1' slice_append2')
      by (metis set_mset_mset)
    done
    
  text \<open>Introducing explicit parameter for list length\<close>  
  definition "par_sort_aux2 xs n d \<equiv> RECT (\<lambda>par_sort_aux (xs,n,d::nat). doN {
    ASSERT (n = length xs);
    if d=0 \<or> n<par_sort_seq_threshold then
      slice_sort_spec (\<^bold><) xs 0 n
    else doN {
      (xs,m) \<leftarrow> partition3_spec xs 0 n;
      bad \<leftarrow> bad_partition m n;
      (_,xs) \<leftarrow> WITH_SPLIT m xs (\<lambda>xs\<^sub>1 xs\<^sub>2. doN {
        ASSERT (length xs\<^sub>2 = length xs - m);
        ASSERT (n\<ge>m);
        (xs\<^sub>1,xs\<^sub>2) \<leftarrow> if bad then doN {
          xs\<^sub>1 \<leftarrow> par_sort_aux (xs\<^sub>1,m,d-1);
          xs\<^sub>2 \<leftarrow> par_sort_aux (xs\<^sub>2,n-m,d-1);
          RETURN (xs\<^sub>1,xs\<^sub>2)
        } else doN {
          nres_par par_sort_aux par_sort_aux (xs\<^sub>1,m,d-1) (xs\<^sub>2,n-m,d-1)
        };
        RETURN ((),xs\<^sub>1,xs\<^sub>2)
      });
      RETURN xs
    }
  }) (xs,n,d)"

  
  lemma par_sort_aux2_refine: "n=length xs \<Longrightarrow> par_sort_aux2 xs n d \<le> \<Down>(\<langle>Id\<rangle>list_rel) (par_sort_aux xs d)"
    unfolding par_sort_aux2_def par_sort_aux_def nres_par_def
    apply (refine_rcg)
    supply [refine_dref_RELATES] = RELATESI[where R="{((xs,n,d),(xs',d')). xs'=xs \<and> d'=d \<and> length xs'=n}"]
    apply refine_dref_type
    apply (simp_all (no_asm_use)) (* TODO: This is a hack against a yet unidentified simplifier loop *)
    apply auto
    done



  text \<open>Fixing concrete algorithms to be used\<close>
  
  text \<open>Version with sequential partitioner\<close>
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

  
  text \<open>Version with parallel partitioner\<close>
  definition "ppar_sort_aux3 xs n d \<equiv> RECT (\<lambda>par_sort_aux (xs,n,d::nat). doN {
    ASSERT (n = length xs);
    if d=0 \<or> n<par_sort_seq_threshold then
      pdqsort xs 0 n
    else doN {
      (xs,m) \<leftarrow> ppart_partition_pivot ppar_chunk_size xs n;
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

  lemma ppart_partition_pivot_refines_part3': "\<lbrakk>0<d'; n=length xs; (xs',xs)\<in>Id; (n',n)\<in>Id; l=0\<rbrakk> 
    \<Longrightarrow> ppart_partition_pivot d' xs' n' \<le> \<Down>Id (partition3_spec xs l n)"
    using ppart_partition_pivot_refines_part3
    by (simp add: ) 
    
    
  lemma ppar_sort_aux3_refine: "ppar_sort_aux3 xs n d \<le>\<Down>Id (par_sort_aux2 xs n d)"
    unfolding ppar_sort_aux3_def par_sort_aux2_def
    find_theorems ppart_partition_pivot
    thm ppart_partition_pivot_refines_part3[THEN refine_IdI]
    apply (refine_rcg ppart_partition_pivot_refines_part3' introsort4_refines_spec pdqsort_refines_spec)
    apply refine_dref_type
    by auto    
    
        
  (* TODO: Move *)  
  lemma slice_sort_spec_complete: "slice_sort_spec lt xs 0 (length xs) = SPEC (sort_spec lt xs)"  
    unfolding slice_sort_spec_def sort_spec_def
    apply clarsimp
    by (metis le_refl mset_eq_length slice_complete)

  lemma par_sort_aux2_correct:
    assumes "n=length xs"  
    shows "par_sort_aux2 xs n d \<le> SPEC (sort_spec (\<^bold><) xs)"
  proof -
    note par_sort_aux2_refine[OF assms]
    also note par_sort_aux_correct
    also note slice_sort_spec_complete
    finally show ?thesis by simp 
  qed
    
        
  lemma par_sort_aux3_correct:
    assumes "n=length xs"  
    shows "par_sort_aux3 xs n d \<le> SPEC (sort_spec (\<^bold><) xs)"
  proof -
    note par_sort_aux3_refine[where d=d]
    also note par_sort_aux2_correct[OF assms]
    finally show ?thesis by simp 
  qed

  lemma ppar_sort_aux3_correct:
    assumes "n=length xs"  
    shows "ppar_sort_aux3 xs n d \<le> SPEC (sort_spec (\<^bold><) xs)"
  proof -
    note ppar_sort_aux3_refine[where d=d]
    also note par_sort_aux2_correct[OF assms]
    finally show ?thesis by simp 
  qed
      
  
  text \<open>Initializing depth bound\<close>
  definition "par_sort xs n \<equiv> doN {
    if n>1 then doN {
      par_sort_aux3 xs n (Discrete.log n * 2)
    } else RETURN xs
  }"
  
  lemma par_sort_correct: "n=length xs \<Longrightarrow> par_sort xs n \<le> SPEC (sort_spec (\<^bold><) xs)"
    unfolding par_sort_def 
    apply (refine_vcg par_sort_aux3_correct)
    by (simp add: sort_spec_def sorted_wrt01)

    
  definition "ppar_sort xs n \<equiv> doN {
    if n>1 then doN {
      ppar_sort_aux3 xs n (Discrete.log n * 2)
    } else RETURN xs
  }"
  
  lemma ppar_sort_correct: "n=length xs \<Longrightarrow> ppar_sort xs n \<le> SPEC (sort_spec (\<^bold><) xs)"
    unfolding ppar_sort_def 
    apply (refine_vcg ppar_sort_aux3_correct)
    by (simp add: sort_spec_def sorted_wrt01)
            
end    
    
subsection \<open>Refining to LLVM\<close>


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
  apply sepref
(* 
  (* debugging boilerplate: *)
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
*)  
  done
  

  sepref_register par_sort
  sepref_def par_sort_impl is "uncurry (PR_CONST par_sort)" 
    :: "[\<lambda>_. True]\<^sub>c (arr_assn)\<^sup>d *\<^sub>a size_assn\<^sup>k  
    \<rightarrow> arr_assn [\<lambda>(ai,_) r. r=ai]\<^sub>c"
    unfolding par_sort_def PR_CONST_def
    apply (annot_snat_const "TYPE(size_t)")
    supply [intro!] = introsort_depth_limit_in_bounds_aux 
    by sepref
  
  thm par_sort_impl.refine[to_hnr, unfolded hn_ctxt_def, of xs xsi n ni]
      
  subsection \<open>Final Correctness Theorem as Hoare-Triple\<close>
  
  lemma par_sort_refine_aux: "(uncurry par_sort, uncurry (\<lambda>xs n. doN {ASSERT (n=length xs); SPEC (sort_spec (\<^bold><) xs) })) \<in> Id \<times>\<^sub>r Id \<rightarrow> \<langle>Id\<rangle>nres_rel"  
    using par_sort_correct[OF refl]
    by (auto simp: pw_nres_rel_iff pw_le_iff refine_pw_simps)
        
  text \<open>We unfold the definition of \<open>hnr\<close>, to extract a correctness statement as Hoare-Triple\<close>  
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
  
  text \<open>With the sorting specification unfolded, too. 
    Note that \<^const>\<open>mset\<close> and \<^const>\<open>sorted_wrt\<close> are standard concepts from Isabelle's library.
  \<close>  
  theorem par_sort_impl_correct': "llvm_htriple (arr_assn xs xsi ** snat_assn n ni ** \<up>(n = length xs)) 
    (par_sort_impl xsi ni) 
    (\<lambda>r. \<up>(r=xsi) ** (EXS xs'. arr_assn xs' xsi ** \<up>(mset xs' = mset xs \<and> sorted_wrt (\<^bold>\<le>) xs')))"
    apply (rule cons_rule[OF par_sort_impl_correct])
    apply simp
    apply (clarsimp simp add: sep_algebra_simps)
    apply (auto simp: sort_spec_def le_by_lt)
    done
    
    

end


context sort_impl_copy_context begin
  sepref_register ppar_sort_aux3
  sepref_def ppar_sort_aux_impl is "uncurry2 (PR_CONST ppar_sort_aux3)" 
    :: "[\<lambda>_. True]\<^sub>c (arr_assn)\<^sup>d *\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k  
    \<rightarrow> arr_assn [\<lambda>((ai,_),_) r. r=ai]\<^sub>c"
  unfolding ppar_sort_aux3_def PR_CONST_def
  supply [[goals_limit = 1]]
  apply (annot_snat_const "TYPE(size_t)")
  apply (rewrite RECT_cp_annot[where CP="\<lambda>(ai,_,_) r. r=ai"])
  
  supply [sepref_comb_rules] = hn_RECT_cp_annot_noframe
  apply sepref
(* 
  (* debugging boilerplate: *)
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
*)  
  done
  
  sepref_register ppar_sort
  sepref_def ppar_sort_impl is "uncurry (PR_CONST ppar_sort)" 
    :: "[\<lambda>_. True]\<^sub>c (arr_assn)\<^sup>d *\<^sub>a size_assn\<^sup>k  
    \<rightarrow> arr_assn [\<lambda>(ai,_) r. r=ai]\<^sub>c"
    unfolding ppar_sort_def PR_CONST_def
    apply (annot_snat_const "TYPE(size_t)")
    supply [intro!] = introsort_depth_limit_in_bounds_aux 
    by sepref
  
  thm ppar_sort_impl.refine[to_hnr, unfolded hn_ctxt_def, of xs xsi n ni]
      
  subsection \<open>Final Correctness Theorem as Hoare-Triple\<close>
  
  lemma ppar_sort_refine_aux: "(uncurry ppar_sort, uncurry (\<lambda>xs n. doN {ASSERT (n=length xs); SPEC (sort_spec (\<^bold><) xs) })) \<in> Id \<times>\<^sub>r Id \<rightarrow> \<langle>Id\<rangle>nres_rel"  
    using ppar_sort_correct[OF refl]
    by (auto simp: pw_nres_rel_iff pw_le_iff refine_pw_simps)
        
  text \<open>We unfold the definition of \<open>hnr\<close>, to extract a correctness statement as Hoare-Triple\<close>  
  theorem ppar_sort_impl_correct: "llvm_htriple (arr_assn xs xsi ** snat_assn n ni ** \<up>(n = length xs)) 
    (ppar_sort_impl xsi ni) 
    (\<lambda>r. \<up>(r=xsi) ** (EXS xs'. arr_assn xs' xsi ** \<up>(sort_spec (\<^bold><) xs xs')))"
    apply (cases "n=length xs"; simp)
    apply (rule cons_rule)
    supply R = ppar_sort_impl.refine[unfolded PR_CONST_def,FCOMP ppar_sort_refine_aux, to_hnr, simplified]
    supply R = R[of xs xsi n ni]
    apply (rule R[THEN hn_refineD])
    apply (simp)
    apply (simp add: hn_ctxt_def sep_algebra_simps)
    apply (auto simp add: hn_ctxt_def sep_algebra_simps pure_def invalid_assn_def)
    done
  
  text \<open>With the sorting specification unfolded, too. 
    Note that \<^const>\<open>mset\<close> and \<^const>\<open>sorted_wrt\<close> are standard concepts from Isabelle's library.
  \<close>  
  theorem ppar_sort_impl_correct': "llvm_htriple (arr_assn xs xsi ** snat_assn n ni ** \<up>(n = length xs)) 
    (ppar_sort_impl xsi ni) 
    (\<lambda>r. \<up>(r=xsi) ** (EXS xs'. arr_assn xs' xsi ** \<up>(mset xs' = mset xs \<and> sorted_wrt (\<^bold>\<le>) xs')))"
    apply (rule cons_rule[OF ppar_sort_impl_correct])
    apply simp
    apply (clarsimp simp add: sep_algebra_simps)
    apply (auto simp: sort_spec_def le_by_lt)
    done
    
    

end

end
