theory LLVM_Memory_RS
imports 
  "../basic/LLVM_Basic_Main"
  Sep_Value_RS 
  Sep_Array_Block_RS
begin
  
  definition "vpto_assn x p \<equiv> VAL.pto p (VAL.val x)"

  interpretation ab: array_block2 "STATIC_ERROR ''''" MEM_ERROR "vload MEM_ERROR::_ \<Rightarrow> (llvm_primval val,_,_,_,_) M" "vstore MEM_ERROR" "checked_gep MEM_ERROR" val_\<alpha> vpto_assn "\<lambda>v. v\<in>range val_\<alpha>"
    apply unfold_locales
    unfolding vpto_assn_def
    apply (rule vload_rule)
    apply (rule vstore_rule)
    subgoal by simp
    subgoal by auto
    subgoal by (auto simp: VAL.val_def)
    subgoal by auto []
    done
  
  
  datatype llvm_amemory = LLVM_AMEMORY (the_amemory: "(nat \<Rightarrow> (nat \<Rightarrow> llvm_primval aval) \<times> int tsa_opt)")
  
  instantiation llvm_amemory :: unique_zero_sep_algebra begin
    definition "sep_disj_llvm_amemory a b \<equiv> the_amemory a ## the_amemory b"
    definition "plus_llvm_amemory a b \<equiv> LLVM_AMEMORY (the_amemory a + the_amemory b)"
    definition "zero_llvm_amemory \<equiv> LLVM_AMEMORY 0"
  
    instance
      apply standard
      unfolding sep_disj_llvm_amemory_def plus_llvm_amemory_def zero_llvm_amemory_def
      apply (auto simp: sep_algebra_simps llvm_amemory.expand)
      done
      
  end    
  
  type_synonym llvm_assn = "llvm_amemory \<Rightarrow> bool"
  
  definition "llvm_\<alpha> \<equiv> LLVM_AMEMORY o ab.ba.\<alpha> o llvm_memory.the_memory"
  definition "llvm_pto x p \<equiv> (ab.ba.pto (llvm_val.the_val x) (llvm_ptr.the_ptr p)) o llvm_amemory.the_amemory"
  (*definition "llvm_is_base_ptr p \<equiv> ab.is_base_ptr (llvm_ptr.the_ptr p)"*)
  
  definition "llvm_malloc_tag n p \<equiv> ab.ba.tag n (llvm_ptr.the_ptr p) o llvm_amemory.the_amemory"
  
  instantiation llvm_ptr :: addr_algebra begin
    definition "abase_llvm_ptr = abase o llvm_ptr.the_ptr"
    definition "acompat_llvm_ptr a b \<equiv> acompat (llvm_ptr.the_ptr a) (llvm_ptr.the_ptr b)"
    definition "adiff_llvm_ptr a b \<equiv> adiff (llvm_ptr.the_ptr a) (llvm_ptr.the_ptr b)"
    definition "aidx_llvm_ptr a i \<equiv> LLVM_PTR ((llvm_ptr.the_ptr a) +\<^sub>a i)"
    
    instance
      apply standard
      unfolding abase_llvm_ptr_def acompat_llvm_ptr_def adiff_llvm_ptr_def aidx_llvm_ptr_def
      apply (intro part_equivpI sympI transpI)
      apply (metis ab.block_ptr_imp_abase ab.is_block_ptr_simps(2) acompat_refl llvm_ptr.sel)
      apply (auto intro: acompat_trans simp: acompat_dom)
      done
  end
  
  
  (*
  definition "llvm_idx_ptr p i \<equiv> LLVM_PTR (ab.idx_ptr (llvm_ptr.the_ptr p) i)"
  definition "llvm_is_arr_ptr p \<equiv> ab.is_arr_ptr (llvm_ptr.the_ptr p)"
  
  lemma llvm_idx_ptr_add[simp]: "llvm_idx_ptr (llvm_idx_ptr p i) j = llvm_idx_ptr p (i+j)"
    by (cases p) (auto simp: llvm_idx_ptr_def)
  
  lemma llvm_is_arr_ptr_idx[simp]: "llvm_is_arr_ptr (llvm_idx_ptr p i) \<longleftrightarrow> llvm_is_arr_ptr p"
    by (cases p) (auto simp: llvm_idx_ptr_def llvm_is_arr_ptr_def)
  *)  
  
  lemma llvm_pto_null_eq[simp]: "llvm_pto x llvm_null = sep_false"
    by (auto simp: llvm_pto_def llvm_null_def)
  
  lemma xfer_htriple: 
    assumes "htriple ab.ba.\<alpha> P c Q"
    assumes "P' = P o llvm_amemory.the_amemory"
    assumes "c' = llvm_zoom_base \<alpha> c"
    assumes "\<And>r. Q' (\<alpha> r) = Q r o llvm_amemory.the_amemory"
    shows "htriple llvm_\<alpha> P' c' Q'"
    using assms unfolding htriple_alt llvm_zoom_base_def llvm_\<alpha>_def wp_def
    apply (clarsimp simp: run_simps)
  proof goal_cases
    case A: (1 p s f)
    
    
    
    find_theorems llvm_memory.the_memory\<^sub>L
    
    from \<open>p##f\<close> \<open>LLVM_AMEMORY (ab.ba.\<alpha> (get' llvm_memory.the_memory\<^sub>L s)) = p + f\<close>
    have "llvm_amemory.the_amemory p ## llvm_amemory.the_amemory f"
      and "ab.ba.\<alpha> (get' llvm_memory.the_memory\<^sub>L s) = llvm_amemory.the_amemory p + llvm_amemory.the_amemory f"
      by (auto simp: sep_disj_llvm_amemory_def plus_llvm_amemory_def)
    
    from A(1)[rule_format] show ?case
      apply (rule mwp_cons)
      apply (intro conjI; fact)
      apply (clarsimp_all simp: run_simps)
      by (metis (full_types) assms(4) comp_apply llvm_amemory.sel plus_llvm_amemory_def sep_disj_llvm_amemory_def)
    
  qed  
    
    
  
  
  lemma llvm_load_rule[vcg_rules]: "htriple llvm_\<alpha> (llvm_pto x p) (llvm_load p) (\<lambda>r. \<up>(r=x) ** llvm_pto x p)"
    apply (rule xfer_htriple[OF ab.ba.load_rule])
    unfolding llvm_pto_def llvm_load_def
    apply simp
    apply simp
    apply (rule ext)
    apply (auto simp: sep_algebra_simps pred_lift_extract_simps)
    done

  lemma llvm_store_unchecked_rule[vcg_rules]: "htriple llvm_\<alpha> (llvm_pto xx p) (llvm_store_unchecked x p) (\<lambda>_. llvm_pto x p)"
    apply (rule xfer_htriple[OF ab.ba.store_rule])
    unfolding llvm_pto_def llvm_store_unchecked_def
    apply simp
    apply simp
    apply (rule ext)
    apply (auto simp: sep_algebra_simps pred_lift_extract_simps)
    done

    
  lemma llvm_store_rule[vcg_rules]: "llvm_vstruct x = llvm_vstruct xx 
    \<Longrightarrow> htriple llvm_\<alpha> (llvm_pto xx p) (llvm_store x p) (\<lambda>_. llvm_pto x p)"
    unfolding llvm_store_def
    by vcg
    
    
  lemma the_amemoryZ[simp]: "the_amemory 0 = 0" by (auto simp: zero_llvm_amemory_def)

  lemma the_amemoryZ_iff[simp]: "the_amemory x = 0 \<longleftrightarrow> x=0" 
    by (auto simp: zero_llvm_amemory_def llvm_amemory.expand)
    
    
  lemma xfer_sep_conj1: "((\<lambda>x. a (the_amemory x)) ** (\<lambda>x. b (the_amemory x))) = (a**b) o the_amemory"  
    apply (rule ext)
    apply (auto 3 3 simp: sep_conj_def sep_disj_llvm_amemory_def plus_llvm_amemory_def)
    by (metis (full_types) llvm_amemory.exhaust_sel llvm_amemory.sel)

  lemma xfer_sep_conj2: "((a o the_amemory) ** (b o the_amemory)) = (a**b) o the_amemory"  
    using xfer_sep_conj1 unfolding comp_def .

  lemmas xfer_sep_conj = xfer_sep_conj1 xfer_sep_conj2
            
  lemma xfer_sep_list_conj1: "(\<And>*map (\<lambda>x. f x o the_amemory) l) = (\<And>*map f l) o the_amemory"  
    apply (induction l)
    apply auto
    by (auto simp: sep_algebra_simps xfer_sep_conj)

  lemma xfer_sep_list_conj2: "(\<And>*map (\<lambda>x s. f x (the_amemory s)) l) = (\<And>*map f l) o the_amemory"  
    using xfer_sep_list_conj1 unfolding comp_def .
      
  lemmas xfer_sep_list_conj = xfer_sep_list_conj1 xfer_sep_list_conj2  

  lemma xfer_sep_set_img1: "(\<Union>*x\<in>I. f x o the_amemory) = (\<Union>*x\<in>I. f x) o the_amemory"  
  proof (cases "finite I")  
    case True then show ?thesis
      by (induction) (auto del: ext intro!: ext simp: sep_algebra_simps xfer_sep_conj)
  qed auto   

  lemma xfer_sep_set_img2: "(\<Union>*x\<in>I. (\<lambda>s. f x (the_amemory s))) = (\<Union>*x\<in>I. f x) o the_amemory"  
    using xfer_sep_set_img1 unfolding comp_def .
      
  lemmas xfer_sep_set_img = xfer_sep_set_img1 xfer_sep_set_img2  
  
      
  lemma llvm_allocn_rule[vcg_rules]: 
    "htriple llvm_\<alpha> 
      \<box> 
      (llvm_allocn v n) 
      (\<lambda>r. (\<Union>*i\<in>{0..<int n}. llvm_pto v (r +\<^sub>a i)) 
        ** llvm_malloc_tag (int n) r ** \<up>(abase r))"  
    apply (rule xfer_htriple[OF ab.ba_allocn_rule])
    unfolding llvm_pto_def llvm_allocn_def llvm_malloc_tag_def abase_llvm_ptr_def aidx_llvm_ptr_def
    apply (rule ext) apply (auto simp: sep_algebra_simps) []
    apply simp
    apply (rule ext)
    apply (auto simp: sep_algebra_simps pred_lift_extract_simps xfer_sep_set_img xfer_sep_conj)
    done
            
    
    
  lemma llvm_free_rule[vcg_rules]:
    "htriple llvm_\<alpha> 
      ((\<Union>*i\<in>{0..<n}. EXS v. llvm_pto v (p +\<^sub>a i)) 
        ** llvm_malloc_tag n p)
      (llvm_free p)
      (\<lambda>_. \<box>)"  
    apply (rule xfer_htriple[OF ab.ba_freen_rule[where p="llvm_ptr.the_ptr p" and n=n], where \<alpha>=id])
    apply (cases p; simp add: )
    
    unfolding llvm_pto_def llvm_free_def llvm_malloc_tag_def aidx_llvm_ptr_def
    apply (auto simp: sep_algebra_simps)
    apply (subst xfer_sep_set_img xfer_sep_conj)+
    apply (cases p; simp)
    by (metis llvm_val.sel)
  
  lemma llvm_checked_idx_ptr_rule[vcg_rules]:
    "abase p \<Longrightarrow>
      htriple llvm_\<alpha>
        (llvm_pto v (p +\<^sub>a i))
        (llvm_checked_idx_ptr p i)
        (\<lambda>r. \<up>(r= p +\<^sub>a i) ** llvm_pto v (p +\<^sub>a i))
    "
    
    supply R=xfer_htriple[OF ab.checked_idx_ptr_rule[where p="llvm_ptr.the_ptr p" and i=i and xx="llvm_val.the_val v"], where \<alpha>=LLVM_PTR]
    apply (rule R)
    unfolding llvm_checked_idx_ptr_def llvm_pto_def abase_llvm_ptr_def aidx_llvm_ptr_def
    apply (auto simp: xfer_sep_conj sep_algebra_simps pred_lift_extract_simps)
    done
    
  
end
