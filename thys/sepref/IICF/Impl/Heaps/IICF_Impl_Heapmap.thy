section \<open>Implementation of Heaps by Arrays\<close>
theory IICF_Impl_Heapmap
imports 
  IICF_Abs_Heapmap 
  "../IICF_Array" 
  "../IICF_Array_List" 
  "../IICF_Array_Map_Total" 
  "../IICF_Indexed_Array_List"
begin
    
  locale hm_impl = hmstruct prio for prio :: "'e \<Rightarrow> 'p::linorder" +
    fixes prio_assn :: "'p \<Rightarrow> 'pi::llvm_rep \<Rightarrow> assn"
      and elem_assn :: "'e \<Rightarrow> 'ei::llvm_rep \<Rightarrow> assn"
      and prio_impl le_prio_impl lt_prio_impl
      and ltype :: "'l::len2 itself"
    assumes prio_is_pure[safe_constraint_rules]: "is_pure prio_assn"
    assumes elem_is_pure[safe_constraint_rules]: "is_pure elem_assn"  
    assumes prio_impl_refine[sepref_fr_rules]: "(prio_impl, RETURN o prio)\<in>elem_assn\<^sup>k \<rightarrow>\<^sub>a prio_assn"
    assumes le_prio_impl_refine[sepref_fr_rules]: 
      "(uncurry le_prio_impl, uncurry (RETURN oo (\<le>))) \<in> prio_assn\<^sup>k *\<^sub>a prio_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
    assumes lt_prio_impl_refine[sepref_fr_rules]: 
      "(uncurry lt_prio_impl, uncurry (RETURN oo (<))) \<in> prio_assn\<^sup>k *\<^sub>a prio_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
      
  begin

    context
      fixes N :: nat
    begin
    abbreviation "idx_assn \<equiv> snatb_assn' TYPE('l) N"
    abbreviation "idx1_assn \<equiv> snatb_assn' TYPE('l) (Suc N)"

    sepref_register prio

    sepref_register "(\<le>) :: 'p \<Rightarrow> 'p \<Rightarrow> bool"
    sepref_register "(<) :: 'p \<Rightarrow> 'p \<Rightarrow> bool"
    
    lemmas [sepref_frame_free_rules] = 
      mk_free_is_pure[OF prio_is_pure]
      mk_free_is_pure[OF elem_is_pure]
    
    definition "hm2_assn \<equiv> b_assn (ial_assn' TYPE('l) N \<times>\<^sub>a amt_assn elem_assn N) (\<lambda>_. 4<LENGTH('l) \<and> N<max_snat LENGTH('l))"
      
    lemma hm2_assn_rdomp_boundsI: "rdomp (hm2_assn) (ag, bq) \<Longrightarrow> 4<LENGTH('l) \<and> N<max_snat LENGTH('l)"
      unfolding hm2_assn_def by auto
    
    
    find_theorems amt_assn
    
    sepref_definition hm_append_impl is "uncurry2 hm_append_op"
      :: "hm2_assn\<^sup>d*\<^sub>aidx_assn\<^sup>k*\<^sub>aelem_assn\<^sup>k \<rightarrow>\<^sub>a hm2_assn"
      apply (rule hfref_with_rdomI)
      unfolding hm_append_op_def hm2_assn_def
      by sepref
      
    lemmas [sepref_fr_rules] = hm_append_impl.refine
      
    sepref_definition hm_length_impl is "RETURN o hm_length" :: "hm2_assn\<^sup>k \<rightarrow>\<^sub>a snatb_assn' TYPE('l) (N+1)"
      apply (rule hfref_with_rdomI)
      unfolding hm_length_def hm2_assn_def
      by sepref
      
    lemmas [sepref_fr_rules] = hm_length_impl.refine
      
    term hm2_assn  
    sepref_register hm_key_of_op  
    sepref_definition hm_key_of_impl is "uncurry hm_key_of_op" :: "hm2_assn\<^sup>k *\<^sub>a idx1_assn\<^sup>d \<rightarrow>\<^sub>a idx_assn"
      apply (rule hfref_with_rdomI)
      unfolding hm_key_of_op_def hm2_assn_def
      apply (annot_snat_const "TYPE('l)")
      by sepref
    lemmas [sepref_fr_rules] = hm_key_of_impl.refine
      
    (* Optimization *)
    definition "hm_the_lookup_op' k hm \<equiv> do {
      let (pq,ml) = hm;
      v \<leftarrow> mop_map_the_lookup k ml;
      RETURN v
    }"
    lemma hm_the_lookup_op'_refine: 
      "(hm_the_lookup_op', hm_the_lookup_op) \<in> nat_rel \<rightarrow> Id \<rightarrow> \<langle>Id\<rangle>nres_rel"
      apply (intro fun_relI nres_relI)
      unfolding hm_the_lookup_op'_def hm_the_lookup_op_def
      apply refine_vcg
      apply (auto)
      apply (auto simp: heapmap_\<alpha>_def hmr_invar_def restrict_map_def split: if_split_asm)
      done

    sepref_definition hm_the_lookup_impl is "uncurry hm_the_lookup_op'" :: "idx_assn\<^sup>k*\<^sub>ahm2_assn\<^sup>k \<rightarrow>\<^sub>a elem_assn"
      apply (rule hfref_with_rdomI)
      unfolding hm_the_lookup_op'_def hm2_assn_def Let_def
      by sepref
    lemmas hm_the_lookup_impl_refine[sepref_fr_rules] 
      = hm_the_lookup_impl.refine[FCOMP hm_the_lookup_op'_refine]

    sepref_definition hm_val_of_impl is "uncurry hm_val_of_op" :: "hm2_assn\<^sup>k*\<^sub>aidx1_assn\<^sup>k \<rightarrow>\<^sub>a elem_assn"  
      unfolding hm_val_of_op_def
      by sepref
    lemmas [sepref_fr_rules] = hm_val_of_impl.refine
      
    sepref_register hm_prio_of_op
    sepref_definition hm_prio_of_impl is "uncurry (PR_CONST hm_prio_of_op)" :: "hm2_assn\<^sup>k*\<^sub>aidx1_assn\<^sup>k \<rightarrow>\<^sub>a prio_assn"  
      unfolding hm_prio_of_op_def PR_CONST_def
      by sepref
    lemmas [sepref_fr_rules] = hm_prio_of_impl.refine
      
    definition "parent_valid h i \<equiv> hm_valid h (h.parent i)"
    definition "parent_valid' h i \<equiv> i>(1::nat)"
    
    lemma valid_parent_pat[def_pat_rules]: "hm_valid$h$(h.parent$i) \<equiv> parent_valid$h$i"
      unfolding parent_valid_def autoref_tag_defs by simp
    
    lemma parent_valid'_refine: "(uncurry parent_valid',uncurry parent_valid) \<in> [\<lambda>(h,i). hm_valid h i]\<^sub>f Id\<times>\<^sub>rId\<rightarrow>Id"
      apply rule
      unfolding hm_valid_def parent_valid_def parent_valid'_def hm_length_def h.parent_def 
      by auto
    
    sepref_definition parent_valid_impl is "uncurry (RETURN oo parent_valid')" :: "hm2_assn\<^sup>k*\<^sub>aidx1_assn\<^sup>d \<rightarrow>\<^sub>a bool1_assn" 
      unfolding parent_valid'_def
      apply (annot_snat_const "TYPE('l)")
      by sepref
    lemmas [sepref_fr_rules] = parent_valid_impl.refine[FCOMP parent_valid'_refine]
    
    sepref_definition hm_exch_impl is "uncurry2 hm_exch_op" :: "hm2_assn\<^sup>d*\<^sub>aidx1_assn\<^sup>d*\<^sub>aidx1_assn\<^sup>d \<rightarrow>\<^sub>a hm2_assn"
      apply (rule hfref_with_rdomI)
      unfolding hm_exch_op_def hm2_assn_def
      apply (annot_snat_const "TYPE('l)")
      supply [simp] = hm_valid_def
      by sepref
    lemmas [sepref_fr_rules] = hm_exch_impl.refine
    
    sepref_definition parent_impl is "RETURN o h.parent" :: "[\<lambda>_. 4<LENGTH('l)]\<^sub>aidx1_assn\<^sup>d \<rightarrow> idx1_assn"
      unfolding h.parent_def
      apply (rule hfref_bassn_resI)
      subgoal by auto
      apply (annot_snat_const "TYPE('l)")
      by sepref
      
    lemmas [sepref_fr_rules] = parent_impl.refine    
    
    find_theorems hm_swim_op
    sepref_register h.parent hm_exch_op
    
    (* TODO: Very specialized workaround lemma, to work around invalid-recombination
      problem for case that B is pure. DUP in IICF_Heap_Impl.thy
    *)    
    lemma workaround_invalid_recombine_pure3: "is_pure B \<Longrightarrow> hn_ctxt (invalid_assn A \<times>\<^sub>a invalid_assn B) ax px \<turnstile> hn_invalid (A \<times>\<^sub>a B) ax px"
      unfolding hn_ctxt_def invalid_assn_def prod_assn_def entails_def
      by (auto split: prod.split elim!: is_pureE 
        simp: sep_algebra_simps pure_part_pure_conj_eq)
      argo
    
    find_theorems is_pure b_assn  
    
    sepref_register hm_swim_op
    sepref_definition hm_swim_impl is "uncurry (PR_CONST hm_swim_op)" :: "hm2_assn\<^sup>d*\<^sub>aidx1_assn\<^sup>k \<rightarrow>\<^sub>a hm2_assn"
      unfolding hm_swim_op_def PR_CONST_def
      (* TODO: Workaround/Hack *)
      supply X[sepref_frame_match_rules] = workaround_invalid_recombine_pure3[where B="snatb_assn _", simplified]
      supply [simp] = hm2_assn_rdomp_boundsI
      by sepref
    lemmas [sepref_fr_rules] = hm_swim_impl.refine
    
    sepref_register hm_insert_op
    sepref_definition hm_insert_impl is "uncurry2 (PR_CONST hm_insert_op)" 
      :: "idx_assn\<^sup>k*\<^sub>aelem_assn\<^sup>k*\<^sub>ahm2_assn\<^sup>d \<rightarrow>\<^sub>a hm2_assn"
      unfolding hm_insert_op_def PR_CONST_def
      by sepref
    lemmas [sepref_fr_rules] = hm_insert_impl.refine
    
    lemma rewr_2kleN: "2*k \<le> n \<longleftrightarrow> k \<le> n div 2" for k :: nat by auto
      
    sepref_definition hm_has_child_impl is "uncurry (RETURN oo hm_has_child_op)" :: "hm2_assn\<^sup>k*\<^sub>aidx1_assn\<^sup>d \<rightarrow>\<^sub>a bool1_assn"
      unfolding hm_has_child_op_def
      apply (rewrite rewr_2kleN)
      supply [simp,dest] = hm2_assn_rdomp_boundsI
      apply (annot_snat_const "TYPE('l)")
      by sepref
      
    lemmas [sepref_fr_rules] = hm_has_child_impl.refine    

    sepref_definition hm_left_child_impl is "RETURN o hm_left_child_op" :: "[\<lambda>i. 2*i\<le>N \<and> N<max_snat LENGTH('l) \<and> 4<LENGTH('l)]\<^sub>a idx1_assn\<^sup>d \<rightarrow> idx1_assn"
      unfolding hm_left_child_op_def
      apply (rule hfref_bassn_resI)
      subgoal by auto
      apply (annot_snat_const "TYPE('l)")
      by sepref
    lemmas [sepref_fr_rules] = hm_left_child_impl.refine  

    lemma rewr_kp1len: "k+1 \<le> n \<longleftrightarrow> k<(n::nat)" by auto
    
    sepref_definition hm_has_next_child_impl is "uncurry (RETURN oo hm_has_next_child_op)" :: "hm2_assn\<^sup>k*\<^sub>aidx1_assn\<^sup>d \<rightarrow>\<^sub>a bool1_assn"
      unfolding hm_has_next_child_op_def
      apply (rewrite rewr_kp1len)
      by sepref
    lemmas [sepref_fr_rules] = hm_has_next_child_impl.refine    

    sepref_definition hm_next_child_impl is "RETURN o hm_next_child_op" :: "[\<lambda>i. i<N \<and> N<max_snat LENGTH('l) \<and> 4<LENGTH('l)]\<^sub>a idx1_assn\<^sup>d \<rightarrow> idx1_assn"
      unfolding hm_next_child_op_def
      apply (rule hfref_bassn_resI)
      subgoal by auto
      apply (annot_snat_const "TYPE('l)")
      by sepref
    lemmas [sepref_fr_rules] = hm_next_child_impl.refine  
    
    
    lemma sink_sepref_aux2: "\<lbrakk>hm_has_child_op (ag, bq) a2'; rdomp hm2_assn (ag, bq)\<rbrakk>
       \<Longrightarrow> 2 * a2' \<le> N"   
      unfolding hm_has_child_op_def hm2_assn_def hm_length_def 
      by sepref_bounds
       
    lemma sink_sepref_aux3: "\<lbrakk>hm_has_next_child_op (ag, bq) i; rdomp hm2_assn (ag, bq)\<rbrakk> \<Longrightarrow> i<N" 
      unfolding hm_has_next_child_op_def hm2_assn_def hm_length_def 
      by sepref_bounds
       
    sepref_register hm_sink_op
    sepref_definition hm_sink_impl is "uncurry (PR_CONST hm_sink_op)" :: "hm2_assn\<^sup>d*\<^sub>aidx1_assn\<^sup>k \<rightarrow>\<^sub>a hm2_assn"
      unfolding hm_sink_op_def PR_CONST_def
      supply [simp] = hm_length_def
      supply [simp] = sink_sepref_aux2 sink_sepref_aux3
      supply X[sepref_frame_match_rules] = workaround_invalid_recombine_pure3[where B="snatb_assn _", simplified]
      supply [simp,dest] = hm2_assn_rdomp_boundsI
      by sepref
    lemmas [sepref_fr_rules] = hm_sink_impl.refine
      
    sepref_register hm_repair_op  
    sepref_definition hm_repair_impl is "uncurry (PR_CONST hm_repair_op)" :: "hm2_assn\<^sup>d*\<^sub>aidx1_assn\<^sup>k \<rightarrow>\<^sub>a hm2_assn"
      unfolding hm_repair_op_def PR_CONST_def
      by sepref
    lemmas [sepref_fr_rules] = hm_repair_impl.refine
      
    sepref_definition hm_is_empty_impl is "hm_is_empty_op" :: "hm2_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
      unfolding hm_is_empty_op_def
      apply (annot_snat_const "TYPE('l)")
      by sepref
    
    (* Cannot do lookup, unless we have option type! 
      \<rightarrow> Do contains_key and the_lookup instead!
    sepref_definition hm_lookup_impl is "uncurry hm_lookup" :: "hm2_assn\<^sup>k*\<^sub>aidx_assn\<^sup>k \<rightarrow>\<^sub>a elem_assn"
    *)  
      
    sepref_register hm_contains_key_op
    sepref_definition hm_contains_key_impl is "uncurry (PR_CONST hm_contains_key_op)" :: "idx_assn\<^sup>k *\<^sub>a hm2_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
      apply (rule hfref_with_rdomI)
      unfolding hm_contains_key_op_def hm2_assn_def PR_CONST_def
      by sepref
    lemmas [sepref_fr_rules] = hm_contains_key_impl.refine  
      
    lemma hm_index_impl_aux1: "\<lbrakk>b \<in> set a1'; rdomp (ial_assn N) a1'; N<max_snat LENGTH('l)\<rbrakk>
       \<Longrightarrow> Suc (index a1' b) < max_snat LENGTH('l)"  
      apply sepref_bounds
      by (meson index_less less_trans_Suc)
      
    sepref_definition hm_index_impl is "uncurry hm_index_op" :: "hm2_assn\<^sup>k*\<^sub>aidx_assn\<^sup>d\<rightarrow>\<^sub>aidx1_assn"
      unfolding hm_index_op_def hm2_assn_def
      apply (rule hfref_bassn_resI)
      subgoal 
        apply (clarsimp simp: uncurry_def) 
        apply refine_vcg 
        apply sepref_bounds
        by (auto simp: heapmap_\<alpha>_def restrict_map_eq)
      supply [simp] = heapmap_\<alpha>_def restrict_map_eq hm_index_impl_aux1
      apply (rule hfref_with_rdomI)
      apply (annot_snat_const "TYPE('l)")
      by sepref
    lemmas [sepref_fr_rules] = hm_index_impl.refine  
      
    term hm_update_op
    sepref_definition hm_update_impl is "uncurry2 hm_update_op" :: "hm2_assn\<^sup>d*\<^sub>aidx1_assn\<^sup>d*\<^sub>aelem_assn\<^sup>k \<rightarrow>\<^sub>a hm2_assn"
      unfolding hm_update_op_def hm2_assn_def
      apply (rule hfref_with_rdomI)
      supply [simp] = hm_valid_def
      apply (annot_snat_const "TYPE('l)")
      by sepref
    lemmas [sepref_fr_rules] = hm_update_impl.refine
    
    sepref_register hm_decrease_key_op
    sepref_definition hm_decrease_key_impl is "uncurry2 (PR_CONST hm_decrease_key_op)" :: "idx_assn\<^sup>k *\<^sub>a elem_assn\<^sup>k *\<^sub>a hm2_assn\<^sup>d \<rightarrow>\<^sub>a hm2_assn "
      unfolding hm_decrease_key_op_def PR_CONST_def
      by sepref
    lemmas [sepref_fr_rules] = hm_decrease_key_impl.refine
          
    sepref_register hm_increase_key_op
    sepref_definition hm_increase_key_impl is "uncurry2 (PR_CONST hm_increase_key_op)" :: "idx_assn\<^sup>k *\<^sub>a elem_assn\<^sup>k *\<^sub>a hm2_assn\<^sup>d \<rightarrow>\<^sub>a hm2_assn "
      unfolding hm_increase_key_op_def PR_CONST_def
      by sepref
    lemmas [sepref_fr_rules] = hm_increase_key_impl.refine

    sepref_register hm_change_key_op
    sepref_definition hm_change_key_impl is "uncurry2 (PR_CONST hm_change_key_op)" :: "idx_assn\<^sup>k *\<^sub>a elem_assn\<^sup>k *\<^sub>a hm2_assn\<^sup>d \<rightarrow>\<^sub>a hm2_assn "
      unfolding hm_change_key_op_def PR_CONST_def
      by sepref
    lemmas [sepref_fr_rules] = hm_change_key_impl.refine
        
    sepref_register hm_set_op
    sepref_definition hm_set_impl is "uncurry2 (PR_CONST hm_set_op)" :: "idx_assn\<^sup>k*\<^sub>aelem_assn\<^sup>k*\<^sub>ahm2_assn\<^sup>d \<rightarrow>\<^sub>a hm2_assn"
      unfolding hm_set_op_def PR_CONST_def
      by sepref
    lemmas [sepref_fr_rules] = hm_set_impl.refine
          
    sepref_register hm_butlast_op  
    sepref_definition hm_butlast_impl is "hm_butlast_op" :: "hm2_assn\<^sup>d \<rightarrow>\<^sub>a hm2_assn"
      unfolding hm_butlast_op_def hm2_assn_def
      apply (rule hfref_with_rdomI)
      apply (annot_snat_const "TYPE('l)")
      by sepref
    lemmas [sepref_fr_rules] = hm_butlast_impl.refine      
      
    lemma hm_pop_min_impl_aux1: 
      "\<lbrakk>hm_valid (pq, m) (Suc 0); rdomp hm2_assn (pq, m)\<rbrakk> \<Longrightarrow> 0<N"
      unfolding hm2_assn_def hm_valid_def hm_length_def
      by (cases pq; sepref_bounds)
      
    sepref_register hm_pop_min_op
    sepref_definition hm_pop_min_impl is "PR_CONST hm_pop_min_op" :: "hm2_assn\<^sup>d \<rightarrow>\<^sub>a (idx_assn \<times>\<^sub>a elem_assn) \<times>\<^sub>a hm2_assn"
      unfolding hm_pop_min_op_def PR_CONST_def
      supply [simp] = hm_pop_min_impl_aux1
      apply (annot_snat_const "TYPE('l)")
      by sepref
    lemmas [sepref_fr_rules] = hm_pop_min_impl.refine      
    
    sepref_register hm_remove_op 
    sepref_definition hm_remove_impl is "uncurry (PR_CONST hm_remove_op)" :: "idx_assn\<^sup>k *\<^sub>a hm2_assn\<^sup>d \<rightarrow>\<^sub>a hm2_assn"
      unfolding hm_remove_op_def PR_CONST_def
      (* TODO Hack/Workaround: Prevents b_assn to be degraded when comparing.
        Deeper problem to fix: Do not degrade b_assn, even if operation is on basic assn!
      *)
      apply (rewrite at "if \<hole>\<noteq>_ then _ else _" fold_COPY)
      by sepref
    lemmas [sepref_fr_rules] = hm_remove_impl.refine
    
    sepref_register hm_peek_min_op
    sepref_definition hm_peek_min_impl is "hm_peek_min_op" :: "hm2_assn\<^sup>k \<rightarrow>\<^sub>a idx_assn\<times>\<^sub>aelem_assn"
      unfolding hm_peek_min_op_def hm_kv_of_op_def
      supply [simp] = hm_pop_min_impl_aux1
      apply (annot_snat_const "TYPE('l)")
      by sepref
    lemmas [sepref_fr_rules] = hm_peek_min_impl.refine

    end
    
    
    sepref_decl_op hm_empty: "\<lambda>_::nat. op_map_empty" :: "nat_rel \<rightarrow> \<langle>K,V\<rangle>map_rel" .
    
    context fixes N :: nat begin
      sepref_decl_op hm_empty_fixed: "op_hm_empty N" :: "\<langle>K,V\<rangle>map_rel" .
    end
    

    lemma fold_custom_hm_empty:
      "Map.empty = op_hm_empty N"
      "RETURN Map.empty = mop_hm_empty N"
      "mop_map_empty = mop_hm_empty N"
      by auto
    

    lemma fold_custom_hm_empty_fixed:
      "Map.empty = op_hm_empty_fixed N"
      "RETURN Map.empty = mop_hm_empty_fixed N"
      "mop_map_empty = mop_hm_empty_fixed N"
      by auto
      
      
    term hm_empty_op   
    
    definition "hm_empty_op' N \<equiv> do { m\<leftarrow>mop_amt_empty N; RETURN (op_ial_empty N,m) }"
    
    lemma hm_empty_op_N: "hm_empty_op' N = hm_empty_op"
      by (auto simp: hm_empty_op_def hm_empty_op'_def)

    lemma hm_empty_op'_aref: "(hm_empty_op', mop_hm_empty) \<in> nat_rel \<rightarrow> \<langle>heapmap_rel\<rangle>nres_rel"  
      using hm_empty_op_aref by (auto simp: hm_empty_op_N)
          
      
    sepref_definition hm_empty_impl is "hm_empty_op'" :: "[\<lambda>_. 4<LENGTH('l)]\<^sub>a\<^sub>d (snat_assn' TYPE('l))\<^sup>k \<rightarrow> hm2_assn"
      unfolding hm_empty_op_def hm_empty_op'_def hm2_assn_def
      apply (rule hfref_with_rdomI)
      by sepref
      
    definition "hm12_assn \<equiv> hrr_comp nat_rel hm2_assn (\<lambda>_. heapmap_rel)"
    
    lemma hm12_assn_fold': "hr_comp (hm2_assn N) heapmap_rel = hm12_assn N"
      unfolding hm12_assn_def
      by auto
    
    context 
      notes [fcomp_norm_unfold] = hm12_assn_def[symmetric] hm12_assn_fold'
    begin
    
      lemmas hm_empty_ref12 = hm_empty_impl.refine[FCOMP hm_empty_op'_aref]
      lemmas hm_insert_ref12 = hm_insert_impl.refine[unfolded PR_CONST_def, FCOMP hm_insert_op_aref]
      lemmas hm_is_empty_ref12 = hm_is_empty_impl.refine[FCOMP hm_is_empty_op_aref]
      lemmas hm_the_lookup_ref12 = hm_the_lookup_impl_refine[FCOMP hm_the_lookup_op_aref]
      lemmas hm_contains_key_ref12 = hm_contains_key_impl.refine[unfolded PR_CONST_def, FCOMP hm_contains_key_op_aref]
      lemmas hm_decrease_key_ref12 = hm_decrease_key_impl.refine[unfolded PR_CONST_def, FCOMP hm_decrease_key_op_aref]
      lemmas hm_increase_key_ref12 = hm_increase_key_impl.refine[unfolded PR_CONST_def, FCOMP hm_increase_key_op_aref]
      lemmas hm_change_key_ref12 = hm_change_key_impl.refine[unfolded PR_CONST_def, FCOMP hm_change_key_op_aref]
      lemmas hm_set_ref12 = hm_set_impl.refine[unfolded PR_CONST_def, FCOMP hm_set_op_aref]
      lemmas hm_pop_min_ref12 = hm_pop_min_impl.refine[unfolded PR_CONST_def, FCOMP hm_pop_min_op_aref]
      lemmas hm_remove_ref12 = hm_remove_impl.refine[unfolded PR_CONST_def, FCOMP hm_remove_op_aref]
      lemmas hm_peek_min_ref12 = hm_peek_min_impl.refine[FCOMP hm_peek_min_op_aref]
            
    end

    definition "hm_assn N \<equiv> hr_comp (hm12_assn N) (\<langle>nat_rel, Id\<rangle>map_rel)"
    
    lemma hm_assn_fold': "hrr_comp nat_rel hm12_assn (\<lambda>x. \<langle>nat_rel, Id\<rangle>map_rel) = hm_assn"
      by (auto simp: hm_assn_def fun_eq_iff)
    
    context
      notes [fcomp_norm_unfold] = hm_assn_def[symmetric] hm_assn_fold'
    begin
      (*lemmas hm_empty_hnr = hm_empty_ref12[FCOMP mop_hm_empty_fref]*)
      
      sepref_decl_impl (ismop) hm_empty_ref12 
        uses mop_hm_empty.fref[where K=Id and V=Id] fixes 'l by parametricity simp
      
      context 
        fixes N :: nat and Ni :: "'l word"
        assumes Ni_ref: "(Ni,N)\<in>snat_rel' TYPE('l)"
      begin  
        lemma hm_empty_fixed_ref: 
          "(uncurry0 (hm_empty_impl Ni), uncurry0 (PR_CONST (mop_hm_empty_fixed N))) \<in> [\<lambda>_. 4 < LENGTH('l)]\<^sub>a unit_assn\<^sup>k \<rightarrow> hm12_assn N"
          apply rule
          apply (drule hfrefD[OF hm_empty_ref12, of N Ni])
          using Ni_ref
          by (simp add: pure_def)
      
        sepref_decl_impl (ismop,no_register) hm_empty_fixed: hm_empty_fixed_ref
          uses mop_hm_empty_fixed.fref[where K=Id and V=Id] fixes 'l by parametricity simp
          
      end
        
      sepref_decl_impl (ismop) hm_insert_ref12 uses mop_map_update_new.fref[where K=Id and V=Id] .
      sepref_decl_impl (ismop) hm_is_empty_ref12 uses mop_map_is_empty.fref[where K=Id and V=Id] .
      sepref_decl_impl (ismop) hm_the_lookup_ref12 uses mop_map_the_lookup.fref[where K=Id and V=Id] .
      sepref_decl_impl (ismop) hm_contains_key_ref12 uses mop_map_contains_key.fref[where K=Id and V=Id] .
      sepref_decl_impl (ismop) hm_decrease_key_ref12 uses mop_pm_decrease_key.fref[where K=Id and V=Id] .
      sepref_decl_impl (ismop) hm_increase_key_ref12 uses mop_pm_increase_key.fref[where K=Id and V=Id] .
      sepref_decl_impl (ismop) hm_change_key_ref12 uses mop_map_update_ex.fref[where K=Id and V=Id] .
      sepref_decl_impl (ismop) hm_set_ref12 uses mop_map_update.fref[where K=Id and V=Id] .
      sepref_decl_impl (ismop) hm_pop_min_ref12 uses mop_pm_pop_min.fref[where K=Id and V=Id] .
      sepref_decl_impl (ismop) hm_remove_ref12 uses mop_map_delete_ex.fref[where K=Id and V=Id] .
      sepref_decl_impl (ismop) hm_peek_min_ref12 uses mop_pm_peek_min.fref[where K=Id and V=Id] .
    end    
        
  end      

    
  global_interpretation 
    HM: hm_impl id "snat_assn' TYPE('l)" "snat_assn' TYPE('l)" return ll_icmp_sle ll_icmp_slt "TYPE('l::len2)" 
    defines 
           hm_empty_impl = HM.hm_empty_impl
       and hm_append_impl = HM.hm_append_impl
       and hm_insert_impl = HM.hm_insert_impl
       and hm_length_impl = HM.hm_length_impl
       and hm_swim_impl = HM.hm_swim_impl
       and hm_sink_impl = HM.hm_sink_impl
       and hm_is_empty_impl = HM.hm_is_empty_impl
       and hm_the_lookup_impl = HM.hm_the_lookup_impl
       and hm_contains_key_impl = HM.hm_contains_key_impl
       and hm_decrease_key_impl = HM.hm_decrease_key_impl
       and hm_increase_key_impl = HM.hm_increase_key_impl
       and hm_change_key_impl = HM.hm_change_key_impl
       and hm_parent_impl = HM.parent_impl
       and hm_parent_valid_impl = HM.parent_valid_impl
       and hm_next_child_impl = HM.hm_next_child_impl
       and hm_has_next_child_impl = HM.hm_has_next_child_impl
       and hm_left_child_impl = HM.hm_left_child_impl
       and hm_has_child_impl = HM.hm_has_child_impl
       and hm_repair_impl = HM.hm_repair_impl
       and hm_set_impl = HM.hm_set_impl
       and hm_pop_min_impl = HM.hm_pop_min_impl
       and hm_remove_impl = HM.hm_remove_impl
       and hm_peek_min_impl = HM.hm_peek_min_impl
       
       and hm_exch_impl = HM.hm_exch_impl
       and hm_update_impl = HM.hm_update_impl
       and hm_index_impl = HM.hm_index_impl
       and hm_prio_of_impl = HM.hm_prio_of_impl
       and hm_val_of_impl = HM.hm_val_of_impl
       and hm_key_of_impl = HM.hm_key_of_impl
       and hm_butlast_impl = HM.hm_butlast_impl
    
    
    apply unfold_locales
    apply (rule pure_pure)
    apply sepref
    apply sepref
    apply sepref
    done
    
  type_synonym 'l heapmap = "'l ial \<times> 'l word amt"  

  abbreviation hm_assn' where "hm_assn' TYPE('l::len2) \<equiv> HM.hm_assn :: _ \<Rightarrow> _ \<Rightarrow> 'l heapmap \<Rightarrow> _"
  
  
  schematic_goal [sepref_frame_free_rules]: "MK_FREE (HM.hm_assn N) (?fr)"
    unfolding HM.hm_assn_def HM.hm12_assn_def HM.hm2_assn_def
    by sepref_dbg_side_keep
    
  term  HM.hm_assn
    
  lemma hm_assn_intf[intf_of_assn]: 
    "intf_of_assn (HM.hm_assn N) (TYPE((nat,nat)i_map))"
    by simp
    
  lemmas [llvm_code,llvm_inline] = 
    HM.hm_append_impl_def
    HM.hm_is_empty_impl_def
    HM.hm_length_impl_def
    HM.hm_the_lookup_impl_def
    HM.hm_contains_key_impl_def
    HM.parent_impl_def
    HM.parent_valid_impl_def
    HM.hm_prio_of_impl_def
    HM.hm_val_of_impl_def
    HM.hm_key_of_impl_def
    HM.hm_next_child_impl_def
    HM.hm_has_next_child_impl_def
    HM.hm_left_child_impl_def
    HM.hm_has_child_impl_def
    HM.hm_butlast_impl_def

    
  lemmas [llvm_code] = 
    HM.hm_insert_impl_def
    HM.hm_decrease_key_impl_def
    HM.hm_increase_key_impl_def
    HM.hm_change_key_impl_def
    HM.hm_swim_impl_def
    HM.hm_sink_impl_def
    HM.hm_exch_impl_def
    HM.hm_update_impl_def
    HM.hm_index_impl_def
    HM.hm_repair_impl_def
    HM.hm_set_impl_def
    HM.hm_pop_min_impl_def
    HM.hm_remove_impl_def
    HM.hm_peek_min_impl_def
    HM.hm_empty_impl_def
    

  term HM.hm_prio_of_impl  
  thm HM.hm_prio_of_impl_def
    
    
  export_llvm
    "hm_empty_impl :: _ \<Rightarrow> 32 heapmap llM"
    "hm_append_impl:: _ \<Rightarrow> 32 word \<Rightarrow> _"
    "hm_is_empty_impl :: 32 heapmap \<Rightarrow> _"
    "hm_the_lookup_impl :: _ \<Rightarrow> 32 heapmap \<Rightarrow> _"
    "hm_contains_key_impl :: _ \<Rightarrow> 32 heapmap \<Rightarrow> _"
    "hm_decrease_key_impl :: _ \<Rightarrow> _ \<Rightarrow> 32 heapmap \<Rightarrow> _"
    "hm_increase_key_impl :: _ \<Rightarrow> _ \<Rightarrow> 32 heapmap \<Rightarrow> _"
    "hm_change_key_impl :: _ \<Rightarrow> _ \<Rightarrow> 32 heapmap \<Rightarrow> _"
    "hm_set_impl :: _ \<Rightarrow> _ \<Rightarrow> 32 heapmap \<Rightarrow> _"
    "hm_pop_min_impl :: 32 heapmap \<Rightarrow> _"
    "hm_remove_impl :: _ \<Rightarrow> 32 heapmap \<Rightarrow> _"
    "hm_peek_min_impl :: 32 heapmap \<Rightarrow> _"
    file "heapmap.ll"
    
    

  context 
    fixes N Ni
    assumes NiREF: "(Ni,N)\<in>snat_rel' TYPE(32)"
    notes [sepref_fr_rules] = HM.hm_empty_fixed_hnr_mop[OF NiREF]
    
    (*notes [sepref_import_param] = NiREF
    notes [[sepref_register_adhoc N]]
    *)
  begin
  
    definition "snatb (x::nat) \<equiv> x"
    lemma snatb_hnr: "(return,RETURN o snatb) \<in> [\<lambda>x. x<N]\<^sub>a snat_assn\<^sup>k \<rightarrow> snatb_assn N"
      unfolding snatb_def
      by sepref_to_hoare vcg
  
    definition "heapmap_test \<equiv> do {
      ASSERT (42<N);
      m \<leftarrow> HM.mop_hm_empty_fixed N;
      m \<leftarrow> mop_map_update (snatb 7)  (snatb 3) m;
      m \<leftarrow> mop_map_update (snatb 6)  (snatb 2) m;
      m \<leftarrow> mop_map_update (snatb 16) (snatb 1) m;
      (k,v) \<leftarrow> mop_pm_peek_min id m;
      RETURN k
    }"
  
    sepref_definition heapmap_test_impl_aux is "uncurry0 heapmap_test" :: "unit_assn\<^sup>k \<rightarrow>\<^sub>a snat_assn' TYPE(32)"
      unfolding heapmap_test_def
      supply [sepref_fr_rules] = snatb_hnr
      apply (annot_snat_const "TYPE(32)")
      by sepref
      
  end

  concrete_definition heapmap_test_impl is heapmap_test_impl_aux_def
  declare heapmap_test_impl_def[llvm_code]
  
  export_llvm heapmap_test_impl
  
  lemma "(heapmap_test_impl_aux, heapmap_test) \<in> snat_assn\<^sup>k \<rightarrow>\<^sub>a snat_assn"
    apply rule
    apply (rule hn_refine_preI)
    using heapmap_test_impl_aux.refine[to_hnr]
    by (simp add: pure_def pred_lift_extract_simps sep_algebra_simps)
    
end    
