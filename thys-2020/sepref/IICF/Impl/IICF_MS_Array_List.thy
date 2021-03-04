theory IICF_MS_Array_List
imports 
  "../Intf/IICF_List" IICF_Array
begin
  definition "ms_irel M N \<equiv> br (\<lambda>(l,xs). take l xs) (\<lambda>(l,xs). l\<le>N \<and> N = length xs \<and> N<M)"

  
  definition "ms_empty N \<equiv> RETURN (0::nat,replicate N init)"
  definition "ms_is_empty \<equiv> \<lambda>(l,_). RETURN (l=0)"
  definition "ms_length \<equiv> \<lambda>(l,_). RETURN l"
  definition "ms_push_back \<equiv> \<lambda>(l,xs) x. doN {ASSERT (l < length xs); RETURN (l+1,xs[l:=x])}"
  definition "ms_last \<equiv> \<lambda>(l,xs). doN {ASSERT (0<l \<and> l\<le>length xs); RETURN (xs!(l-1))}"
  definition "ms_butlast \<equiv> \<lambda>(l,xs). doN {ASSERT (l>0); RETURN (l-1,xs)}"
  definition "ms_get \<equiv> \<lambda>(l,xs) i. doN {ASSERT (i<length xs); RETURN (xs!i)}"
  definition "ms_set \<equiv> \<lambda>(l,xs) i x. doN {ASSERT (i<length xs); RETURN (l,xs[i:=x])}"

  context begin
  
    private method ms_prove_refine = 
      (unfold ms_irel_def curry0_def;
        intro nres_relI fun_relI frefI;
        simp?;
        refine_vcg?;
        (auto simp: in_br_conv)
      )
  
    lemma ms_empty_correct: "N<M \<Longrightarrow> (ms_empty N,mop_list_empty) \<in> \<langle>ms_irel M N\<rangle>nres_rel"
      unfolding ms_empty_def by ms_prove_refine
      
    lemma ms_is_empty_correct: "(ms_is_empty,mop_list_is_empty) \<in> ms_irel M N \<rightarrow> \<langle>bool_rel\<rangle>nres_rel"  
      unfolding ms_is_empty_def by ms_prove_refine

    lemma ms_length_correct: "(ms_length,mop_list_length) \<in> ms_irel M N \<rightarrow> \<langle>nat_rel\<rangle>nres_rel"  
      unfolding ms_length_def by ms_prove_refine
    
    lemma ms_push_back_correct: "(uncurry ms_push_back,uncurry mop_list_append) 
      \<in> [\<lambda>(xs,x). length xs < N]\<^sub>f (ms_irel M N \<times>\<^sub>r Id) \<rightarrow> \<langle>ms_irel M N\<rangle>nres_rel"  
      unfolding ms_push_back_def 
      supply [simp] = take_update_last
      by ms_prove_refine 
      
    lemma ms_last_correct: "(ms_last,mop_list_last)\<in>ms_irel M N \<rightarrow> \<langle>Id\<rangle>nres_rel"  
      unfolding ms_last_def supply [simp] = last_take_nth_conv by ms_prove_refine

    lemma ms_butlast_correct: "(ms_butlast,mop_list_butlast)\<in>ms_irel M N \<rightarrow> \<langle>ms_irel M N\<rangle>nres_rel"  
      unfolding ms_butlast_def supply [simp] = butlast_take by ms_prove_refine
    
    lemma ms_get_correct: "(ms_get,mop_list_get)\<in>ms_irel M N \<rightarrow> nat_rel \<rightarrow> \<langle>Id\<rangle>nres_rel"  
      unfolding ms_get_def by ms_prove_refine

    lemma ms_set_correct: "(ms_set,mop_list_set)\<in>ms_irel M N \<rightarrow> nat_rel \<rightarrow> Id \<rightarrow> \<langle>ms_irel M N\<rangle>nres_rel"  
      unfolding ms_set_def by ms_prove_refine
    
  end

  type_synonym ('l,'a) marl = "'l word \<times> 'a ptr"

  lemma ms_irel_prenorm: 
    assumes "((l,xs),xs')\<in>ms_irel M N"
    shows "length xs = N \<and> l=length xs' \<and> length xs'\<le>N \<and> N < M"
    using assms
    unfolding ms_irel_def
    by (auto simp: in_br_conv)
  
    
  context
    fixes M :: nat
    defines "M \<equiv> max_snat (LENGTH ('l::len2))"
    notes [fcomp_prenorm_simps] = ms_irel_prenorm[where M=M]
  begin
    abbreviation "marl2_assn \<equiv> snat_assn' TYPE('l) \<times>\<^sub>a array_assn id_assn"
  
    
    sepref_definition marl_empty_impl [llvm_inline] is "ms_empty" :: "(snat_assn' TYPE('l))\<^sup>k \<rightarrow>\<^sub>a marl2_assn"
      unfolding ms_empty_def
      supply [sepref_import_param] = IdI[of init]
      apply (annot_snat_const "TYPE('l)")
      apply (rewrite array_fold_custom_replicate)
      by sepref

      
    definition [simp]: "marl_empty_aux (N::nat) \<equiv> op_list_empty"  
    
    sepref_decl_op marl_empty: marl_empty_aux :: "nat_rel \<rightarrow> \<langle>A\<rangle>list_rel" .
    
    lemma ms_empty_correct': "(ms_empty,RETURN o op_marl_empty) 
      \<in> [\<lambda>N. N<M]\<^sub>f\<^sub>d nat_rel \<rightarrow> (\<lambda>N. \<langle>ms_irel M N\<rangle>nres_rel)"
      apply (rule frefI) using ms_empty_correct by auto

    (*    
    definition "marl_assn' TYPE('l) N A \<equiv> hr_comp (hr_comp marl2_assn (ms_irel (max_snat LENGTH('l)) N))
                                     (\<langle>the_pure A\<rangle>list_rel)" 
    *)
    
    definition "marl_assn' TYPE('l) A N \<equiv> hrr_comp nat_rel
                                    (\<lambda>N _. hr_comp marl2_assn (ms_irel M N))
                                    (\<lambda>_. \<langle>the_pure A\<rangle>list_rel) N ()"
                                         
    lemmas [fcomp_norm_unfold] = marl_assn'_def[symmetric, abs_def]
    
    lemma marl_assn'_fold''[fcomp_norm_unfold]:
      "hrr_comp nat_rel (\<lambda>x _. hr_comp (snat_assn \<times>\<^sub>a array_assn id_assn) (ms_irel M x)) (\<lambda>x. \<langle>the_pure A\<rangle>list_rel)
      = (\<lambda>N _. marl_assn' TYPE('l) A N)"
      unfolding marl_assn'_def
      by auto
    
    lemma marl_assn'_fold'[fcomp_norm_unfold]: 
      "hr_comp (hr_comp (snat_assn \<times>\<^sub>a array_assn id_assn) (ms_irel M N)) (\<langle>the_pure A\<rangle>list_rel)
        = marl_assn' TYPE('l) A N"
      unfolding marl_assn'_def
      unfolding hrr_comp_def 
      apply (auto simp: fun_eq_iff sep_algebra_simps pred_lift_extract_simps)
      unfolding non_dep2_def by metis+
    
    sepref_decl_impl marl_empty: marl_empty_impl.refine[FCOMP ms_empty_correct'] by simp 
  
    sepref_definition marl_is_empty_impl [llvm_inline] is ms_is_empty :: "marl2_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
      unfolding ms_is_empty_def
      apply (annot_snat_const "TYPE('l)")
      apply sepref_dbg_keep
      done
      
    sepref_decl_impl (ismop) marl_is_empty_impl.refine[FCOMP ms_is_empty_correct[of M]] .
      
    sepref_definition marl_length_impl [llvm_inline] is ms_length :: "marl2_assn\<^sup>k \<rightarrow>\<^sub>a snat_assn' TYPE('l)"
      unfolding ms_length_def
      by sepref
    sepref_decl_impl (ismop) marl_length_impl.refine[FCOMP ms_length_correct[of M]] .

  
    sepref_definition marl_push_back_impl [llvm_code] is 
      "uncurry ms_push_back" :: "[\<lambda>((l,a),_). length a < M ]\<^sub>a marl2_assn\<^sup>d*\<^sub>aid_assn\<^sup>k \<rightarrow> marl2_assn"
      unfolding ms_push_back_def M_def
      apply (annot_snat_const "TYPE('l)")
      apply sepref_dbg_keep
      done

    sepref_decl_impl (ismop) marl_push_back_impl.refine[FCOMP ms_push_back_correct[where M=M]]  
      by (parametricity add: IdI[of N])
      
      
    sepref_definition marl_last_impl [llvm_code] is 
      "ms_last" :: "marl2_assn\<^sup>k \<rightarrow>\<^sub>a id_assn"
      unfolding ms_last_def M_def
      apply (annot_snat_const "TYPE('l)")
      apply sepref_dbg_keep
      done
    sepref_decl_impl (ismop) marl_last_impl.refine[FCOMP ms_last_correct[where M=M]] .
      
    sepref_definition marl_butlast_impl [llvm_code] is 
      "ms_butlast" :: "marl2_assn\<^sup>d \<rightarrow>\<^sub>a marl2_assn"
      unfolding ms_butlast_def M_def
      apply (annot_snat_const "TYPE('l)")
      apply sepref_dbg_keep
      done
    sepref_decl_impl (ismop) marl_butlast_impl.refine[FCOMP ms_butlast_correct[where M=M]] .
      
    
    sepref_definition marl_get_impl [llvm_inline] is 
      "uncurry ms_get" :: "marl2_assn\<^sup>k *\<^sub>a (snat_assn' TYPE('l))\<^sup>k \<rightarrow>\<^sub>a id_assn"
      unfolding ms_get_def M_def
      apply sepref_dbg_keep
      done
    sepref_decl_impl (ismop) marl_get_impl.refine[FCOMP ms_get_correct[where M=M]] .
      
    sepref_definition marl_set_impl [llvm_inline] is 
      "uncurry2 ms_set" :: "marl2_assn\<^sup>d *\<^sub>a (snat_assn' TYPE('l))\<^sup>k *\<^sub>a id_assn\<^sup>k \<rightarrow>\<^sub>a marl2_assn"
      unfolding ms_set_def M_def
      apply sepref_dbg_keep
      done
    sepref_decl_impl (ismop) marl_set_impl.refine[FCOMP ms_set_correct[where M=M]] .
  end
          
     
  lemma fold_marl_empty:
    "[] = op_marl_empty N"
    "RETURN [] = mop_marl_empty N" 
    "op_list_empty = op_marl_empty N"
    "mop_list_empty = mop_marl_empty N"
    by auto


  (* TODO: Move *)    
    
  schematic_goal [sepref_frame_free_rules]: "MK_FREE (marl_assn' TYPE('l::len2) A N) ?f"
    unfolding marl_assn'_fold'[symmetric]
    by sepref_dbg_side
  
  lemma marl_assn'_boundsD[sepref_bounds_dest]:
     "rdomp (marl_assn' TYPE('l::len2) A N) xs \<Longrightarrow> length xs \<le> N \<and> N < max_snat LENGTH('l)"  
    unfolding marl_assn'_def
    supply [sepref_bounds_dest] = ms_irel_prenorm
    by sepref_bounds
      
  lemma bind_assoc_tagged: "bind$(bind$m$f)$g = bind$m$(\<lambda>\<^sub>2x. bind$(f$x)$g)" 
    unfolding autoref_tag_defs by simp 
      
    
    
experiment begin    

  sepref_definition test is "\<lambda>N. (do {
    let x = op_marl_empty N;
    RETURN (x@[1::nat])
  })" :: "[\<lambda>N. N\<ge>10]\<^sub>a\<^sub>d (snat_assn' TYPE(64))\<^sup>k \<rightarrow> (\<lambda>N _. marl_assn' TYPE(64) (snat_assn' TYPE(64)) N)"
    apply (annot_snat_const "TYPE(64)")
    by sepref
    

end

end
