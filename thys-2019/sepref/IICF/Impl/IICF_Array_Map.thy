theory IICF_Array_Map
imports IICF_Array "../Intf/IICF_Map" "../Intf/IICF_List"
begin

  definition "am1_rel N
    \<equiv> br (\<lambda>xs k. if k<length xs then xs!k else None) (\<lambda>xs. length xs = N)"
    

  definition "am1_empty N \<equiv> replicate N None"
  definition "am1_update k v xs \<equiv> mop_list_set xs k (Some v)"
  definition "am1_delete k xs \<equiv> mop_list_set xs k None"
  definition "am1_lookup k xs \<equiv> mop_list_get xs k"
  definition "am1_contains_key k xs \<equiv> doN {x \<leftarrow> mop_list_get xs k; RETURN (\<not>is_None x)}"

      
  sepref_decl_op am_custom_empty: "\<lambda>_::nat. Map.empty::nat\<rightharpoonup>_" :: "nat_rel \<rightarrow> \<langle>nat_rel,V\<rangle>map_rel" .
    
  lemma fold_am_custom_empty:
    "Map.empty = op_am_custom_empty N"
    "op_map_empty = op_am_custom_empty N"
    "mop_map_empty = mop_am_custom_empty N"
    by auto
  
  
  
  lemma am1_empty_refine: "(am1_empty, op_am_custom_empty) \<in> nat_rel \<rightarrow>\<^sub>f\<^sub>d (\<lambda>N. am1_rel N)"
    unfolding am1_empty_def am1_rel_def
    by (auto simp: in_br_conv fun_eq_iff intro!: frefI)

  lemma am1_update_refine: "(uncurry2 am1_update, uncurry2 mop_map_update) 
    \<in> (nbn_rel N \<times>\<^sub>r Id)\<times>\<^sub>ram1_rel N \<rightarrow>\<^sub>f \<langle>am1_rel N\<rangle>nres_rel"  
    apply (rule frefI; clarsimp)
    unfolding am1_update_def am1_rel_def
    apply refine_vcg
    by (auto simp: in_br_conv)
    
  lemma am1_delete_refine: "(uncurry am1_delete, uncurry mop_map_delete) 
    \<in> nbn_rel N \<times>\<^sub>r am1_rel N \<rightarrow>\<^sub>f \<langle>am1_rel N\<rangle>nres_rel"
    apply (rule frefI; clarsimp)
    unfolding am1_delete_def am1_rel_def
    apply refine_vcg
    by (auto simp: in_br_conv)

  lemma am1_lookup_refine: "(uncurry am1_lookup, uncurry mop_map_lookup)
    \<in> nbn_rel N \<times>\<^sub>r am1_rel N \<rightarrow>\<^sub>f \<langle>Id\<rangle>nres_rel"
    apply (rule frefI; clarsimp)
    unfolding am1_lookup_def am1_rel_def
    apply refine_vcg
    by (auto simp: in_br_conv)
    
  lemma am1_contains_key_refine: "(uncurry am1_contains_key, uncurry mop_map_contains_key)
    \<in> nbn_rel N \<times>\<^sub>r am1_rel N \<rightarrow>\<^sub>f \<langle>bool_rel\<rangle>nres_rel"
    apply (rule frefI; clarsimp)
    unfolding am1_contains_key_def am1_rel_def
    apply refine_vcg
    by (auto simp: in_br_conv split: option.splits)
    
  context dflt_pure_option begin  
  
    definition "am2_assn \<equiv> IICF_Array.array_assn option_assn"
  
    definition "am_assn N \<equiv> hr_comp am2_assn (am1_rel N)"
    
    lemma am_assn_intf[intf_of_assn]: 
      "intf_of_assn A TYPE('v) \<Longrightarrow> intf_of_assn (am_assn N) (TYPE((nat,'v)i_map))"
      by simp
    
    context 
      fixes DUMMY :: "'l::len2 itself" 
      notes [fcomp_norm_unfold] = am_assn_def[symmetric]
      notes [fcomp_norm_simps] = map_rel_Id option_rel_id_simp 
        (* TODO: Declare by default! *) hrr_comp_id_conv
    begin
    
      private abbreviation (input) "K_assn \<equiv> snat_assn' TYPE('l)"
    
      sepref_definition am2_empty is "RETURN o am1_empty" 
        :: "K_assn\<^sup>k \<rightarrow>\<^sub>a am2_assn"
        unfolding am1_empty_def am2_assn_def
        apply (rewrite array_fold_custom_replicate)
        by sepref
        
        sepref_decl_impl (no_register) am2_empty: am2_empty.refine[FCOMP am1_empty_refine] 
          uses op_am_custom_empty.fref[where V=Id] .
        
      sepref_definition am2_lookup [llvm_inline] is "uncurry am1_lookup" 
        :: "K_assn\<^sup>k *\<^sub>a am2_assn\<^sup>k \<rightarrow>\<^sub>a option_assn"
        unfolding am1_lookup_def am2_assn_def
        by sepref

      sepref_decl_impl (no_register,ismop) am2_lookup: am2_lookup.refine[FCOMP am1_lookup_refine] 
        uses mop_map_lookup.fref[where K=Id and V=Id] .

      sepref_definition am2_contains_key [llvm_inline] is "uncurry am1_contains_key" 
        :: "K_assn\<^sup>k *\<^sub>a am2_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
        unfolding am1_contains_key_def am2_assn_def
        by sepref

      sepref_decl_impl (no_register,ismop) am2_contains_key: am2_contains_key.refine[FCOMP am1_contains_key_refine] 
        uses mop_map_contains_key.fref[where K=Id and V=Id] .
        
                        
      sepref_definition am2_update [llvm_inline] is "uncurry2 am1_update"  
        :: "K_assn\<^sup>k *\<^sub>a A\<^sup>k *\<^sub>a am2_assn\<^sup>d \<rightarrow>\<^sub>a am2_assn"
        unfolding am1_update_def am2_assn_def
        by sepref

        
      sepref_decl_impl (no_register,ismop) am2_update: am2_update.refine[FCOMP am1_update_refine] 
        uses mop_map_update.fref[where K=Id and V=Id] .

      sepref_definition am2_delete [llvm_inline] is "uncurry am1_delete"  
        :: "K_assn\<^sup>k *\<^sub>a am2_assn\<^sup>d \<rightarrow>\<^sub>a am2_assn"
        unfolding am1_delete_def am2_assn_def
        by sepref

      sepref_decl_impl (no_register,ismop) am2_delete: am2_delete.refine[FCOMP am1_delete_refine] 
        uses mop_map_delete.fref[where K=Id and V=Id] .
                  
      lemma am_assn_free[sepref_frame_free_rules]: "MK_FREE (am_assn N) narray_free"  
        unfolding am_assn_def am2_assn_def
        by (rule sepref_frame_free_rules)+
        
    end
  end
  
  concrete_definition snat_am_empty[llvm_code,llvm_inline] is snat.am2_empty_def
  concrete_definition snat_am_lookup[llvm_code,llvm_inline] is snat.am2_lookup_def
  concrete_definition snat_am_contains_key[llvm_code,llvm_inline] is snat.am2_contains_key_def
  concrete_definition snat_am_update[llvm_code,llvm_inline] is snat.am2_update_def
  concrete_definition snat_am_delete[llvm_code,llvm_inline] is snat.am2_delete_def
  
  thm snat_am_empty.refine
  lemmas [unfolded snat_am_empty.refine,sepref_fr_rules] = snat.am2_empty_hnr snat.am2_empty_hnr_mop
  lemmas [unfolded snat_am_lookup.refine,sepref_fr_rules] = snat.am2_lookup_hnr snat.am2_lookup_hnr_mop
  lemmas [unfolded snat_am_contains_key.refine,sepref_fr_rules] = snat.am2_contains_key_hnr snat.am2_contains_key_hnr_mop
  lemmas [unfolded snat_am_update.refine,sepref_fr_rules] = snat.am2_update_hnr snat.am2_update_hnr_mop
  lemmas [unfolded snat_am_delete.refine,sepref_fr_rules] = snat.am2_delete_hnr snat.am2_delete_hnr_mop
  
  
  
  export_llvm 
    "snat_am_empty :: 32 word \<Rightarrow> 32 word ptr llM"
    "snat_am_lookup :: 32 word \<Rightarrow> 32 word ptr \<Rightarrow> 32 word llM"
    "snat_am_contains_key :: 32 word \<Rightarrow> 32 word ptr \<Rightarrow> 1 word llM"
    "snat_am_update :: 32 word \<Rightarrow> 32 word \<Rightarrow> 32 word ptr \<Rightarrow> 32 word ptr llM"
    "snat_am_delete :: 32 word \<Rightarrow> 32 word ptr \<Rightarrow> 32 word ptr llM"
  
  
  abbreviation "snat_am_assn' TYPE('l::len2) \<equiv> snat.am_assn :: nat \<Rightarrow> (nat \<Rightarrow> nat option) \<Rightarrow> 'l word ptr \<Rightarrow> llvm_amemory \<Rightarrow> bool"

  
(*  method frame_solve_simple = 
    rule fr_round1_init, 
    (determ \<open>rule fr_round1_match | rule fr_round1_nomatch\<close>)+, 
    rule fr_round1_finalize,
    tactic \<open>\<close>
*)    
      
  
  experiment
  begin

  
    sepref_definition test [llvm_code] is "\<lambda>N. doN {
      ASSERT (10 \<le>N \<and> N\<le>42);
      m \<leftarrow> mop_am_custom_empty N;
      m \<leftarrow> mop_map_update 4 2 m;
      if op_map_contains_key 4 m then doN {
        m \<leftarrow> mop_map_update 5 2 m;
        m \<leftarrow> mop_map_update 6 2 m;
        m \<leftarrow> mop_map_delete 5 m;
        RETURN (the (m 4))
      } else doN {
        RETURN (the (m 0))
      }
    }" :: "(snat_assn' TYPE(32))\<^sup>k \<rightarrow>\<^sub>a snat_assn' TYPE(32)"
      supply [simp] = max_snat_def (* TODO: This reasoning should work by default *)
      apply (annot_snat_const "TYPE(32)")
      by sepref
    
    export_llvm test
    
  end
  

end
