theory IICF_Array_Map_Total
imports "../Intf/IICF_Map" IICF_Array
begin
  text \<open>
    Map implementation where lookup is only valid for elements 
    already in the map.
  \<close>

  type_synonym 'a amt1 = "'a list"

  definition amt1_rel :: "nat \<Rightarrow> ('a amt1 \<times> (nat\<rightharpoonup>'a)) set"
    where "amt1_rel N \<equiv> {(xs,m). length xs = N \<and> dom m \<subseteq> {0..<N} \<and> (\<forall>k v. m k = Some v \<longrightarrow> v=xs!k)}"

  definition amt1_init :: "nat \<Rightarrow> 'a::llvm_rep amt1 nres" where "amt1_init N \<equiv> RETURN (replicate N init)"
  definition amt1_lookup :: "nat \<Rightarrow> 'a amt1 \<Rightarrow> 'a nres" 
    where "amt1_lookup k m \<equiv> mop_list_get m k"
    
  definition amt1_update :: "nat \<Rightarrow> 'a \<Rightarrow> 'a amt1 \<Rightarrow> 'a amt1 nres"
    where "amt1_update k v m \<equiv> mop_list_set m k v"
  
  sepref_decl_op amt_empty: "\<lambda>(N::nat). Map.empty :: nat \<rightharpoonup> _" :: "nat_rel \<rightarrow> \<langle>nat_rel,V\<rangle> map_rel" .
  
  lemma amt_fold_custom_empty:
    "op_map_empty = op_amt_empty N"
    "Map.empty = op_amt_empty N"
    "mop_map_empty = mop_amt_empty N"
    by auto
  
  
  lemma amt1_empty_refine: "(amt1_init,mop_amt_empty) 
    \<in> nat_rel \<rightarrow>\<^sub>f\<^sub>d (\<lambda>N. \<langle>amt1_rel N\<rangle>nres_rel)"
    unfolding amt1_init_def
    by (auto intro!: frefI nres_relI simp: amt1_rel_def in_br_conv fun_eq_iff)
  
  lemma amt1_lookup_refine: 
    "(amt1_lookup, mop_map_the_lookup) \<in> nbn_rel N \<rightarrow> amt1_rel N \<rightarrow> \<langle>Id\<rangle>nres_rel"
    apply (clarsimp simp: amt1_lookup_def)
    apply (refine_vcg)
    apply (auto simp: amt1_rel_def in_br_conv)
    done
    
  lemma amt1_update_refine:
    "(amt1_update, mop_map_update) 
      \<in> nbn_rel N \<rightarrow>Id \<rightarrow> amt1_rel N \<rightarrow> \<langle>amt1_rel N\<rangle>nres_rel"
    unfolding amt1_update_def 
    apply (refine_vcg frefI)
    by (auto simp: amt1_rel_def in_br_conv fun_eq_iff)
    
  
    
  context
    fixes L :: "'l::len2 itself"  
    (*notes [fcomp_norm_unfold] = snatb_rel_def[symmetric]*)
  begin
    
    private abbreviation (input) "amt2_assn \<equiv> array_assn id_assn"
  
    definition "amt_assn V N \<equiv> hr_comp 
      (hr_comp amt2_assn (amt1_rel N))
      (\<langle>nat_rel, the_pure V\<rangle>map_rel)"
    lemmas [fcomp_norm_unfold] = amt_assn_def[symmetric]
  
    lemma amt_assn_fold'[fcomp_norm_unfold]: 
      "hrr_comp nat_rel (\<lambda>x _. hr_comp (IICF_Array.array_assn id_assn) (amt1_rel x))
                        (\<lambda>x. \<langle>nat_rel, the_pure V\<rangle>map_rel) = (\<lambda>N _. amt_assn V N)"
      unfolding amt_assn_def 
      by (auto simp: fun_eq_iff hrr_comp_def pred_lift_extract_simps; smt non_dep_def)
    

    lemma amt_assn_intf[intf_of_assn]: "intf_of_assn V TYPE('v) \<Longrightarrow> intf_of_assn (amt_assn V N) (TYPE((nat,'v)i_map))"
      by simp
        
    sepref_definition amt_init_impl [llvm_inline] is "amt1_init"
      :: "(snat_assn' TYPE('l))\<^sup>k \<rightarrow>\<^sub>a amt2_assn"
      unfolding amt1_init_def
      supply [sepref_import_param] = IdI[of init]
      apply (subst array_fold_custom_replicate)
      by sepref
      
     
    sepref_decl_impl (ismop) amt_empty: amt_init_impl.refine[FCOMP amt1_empty_refine] .
    
    sepref_definition amt_lookup_impl [llvm_inline] is "uncurry amt1_lookup" 
      :: "(snat_assn' TYPE('l))\<^sup>k *\<^sub>a amt2_assn\<^sup>k \<rightarrow>\<^sub>a id_assn"
      unfolding amt1_lookup_def
      by sepref
    sepref_decl_impl (ismop) amt_lookup_impl.refine[FCOMP amt1_lookup_refine] 
      uses mop_map_the_lookup.fref[where K=Id] .
                                                            
    sepref_definition amt_update_impl [llvm_inline] is "uncurry2 amt1_update"  
      :: "(snat_assn' TYPE('l))\<^sup>k *\<^sub>a id_assn\<^sup>k *\<^sub>a amt2_assn\<^sup>d \<rightarrow>\<^sub>a amt2_assn"
      unfolding amt1_update_def
      by sepref
    sepref_decl_impl (ismop) amt_update_impl.refine[FCOMP amt1_update_refine] 
      uses mop_map_update.fref[where K=Id] .
  
  end    
  
  type_synonym ('v) amt = "'v ptr"
  
  schematic_goal [sepref_frame_free_rules]: "MK_FREE (amt_assn N V) (?fr)"
    unfolding amt_assn_def
    by sepref_dbg_side



end
