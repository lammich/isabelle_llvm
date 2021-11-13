section \<open>Implementation of Heaps with Arrays\<close>
theory IICF_Impl_Heap
imports 
  IICF_Abs_Heap 
  "../IICF_Array" 
  "../IICF_Array_List" 
begin

  (* TODO: Move *)
  
  term al_assn

  (* TODO: Move *)      
  lemma size_mset_param[param]: "(size,size)\<in>\<langle>A\<rangle>mset_rel \<rightarrow> nat_rel"  
    by (auto simp: mset_rel_def p2rel_def rel_mset_size)
    

  (* TODO: Move *)
  lemma rdomp_ref_mk_assn_iff[simp]: "rdomp \<upharpoonleft>(mk_assn A) = rdomp A"
    by (auto simp: rdomp_def)
  
  thm vcg_prep_ext_rules  
    
  find_theorems pure_part  
    
  lemma rdomp_arl_assn_len:
    assumes "rdomp \<upharpoonleft>(arl_assn:: ('a::llvm_rep list, 'l::len2 word \<times> 'l word \<times> 'a ptr) dr_assn) xs"
    shows "length xs < max_snat LENGTH('l)"
    using assms
    by (auto 
      simp: rdomp_def arl_assn_def arl_assn'_def sep_algebra_simps pred_lift_extract_simps
      simp: snat.assn_def
      )

  find_theorems vassn_tag hn_refine

      
  (* TODO: Very specialized workaround lemma, to work around invalid-recombination
    problem for case that B is pure 
  *)    
  lemma workaround_invalid_recombine_pure2: "is_pure B \<Longrightarrow> hn_ctxt (invalid_assn A \<times>\<^sub>a B) ax px \<turnstile> hn_invalid (A \<times>\<^sub>a B) ax px"
    unfolding hn_ctxt_def invalid_assn_def prod_assn_def entails_def
    by (auto split: prod.split elim!: is_pureE 
      simp: sep_algebra_simps pure_part_pure_conj_eq)
    
  (* TODO: Move
    TODO: Should be generic algorithm!
  *)  
  lemma mop_list_swap_unfold: "mop_list_swap xs i j = do {
    xi \<leftarrow> mop_list_get xs i;
    xj \<leftarrow> mop_list_get xs j;
    xs \<leftarrow> mop_list_set xs i xj;
    mop_list_set xs j xi
  }"
  by (auto simp: pw_eq_iff refine_pw_simps swap_def)
  
    


  text \<open>We implement the heap data structure by an array.
    The implementation is automatically synthesized by the Sepref-tool.
    \<close>
  subsection \<open>Setup of the Sepref-Tool\<close>

  (* TODO: Move *)
  lemma mset_rel_id: "\<langle>Id\<rangle>mset_rel = Id"
    unfolding mset_rel_def apply (simp add: rel2p multiset.rel_eq)
    by (simp only: p2rel)
  
  
  locale heap_impl = heapstruct prio for prio :: "'e \<Rightarrow> 'p::linorder" +
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
      
    fixes N defines "N\<equiv>LENGTH('l)"
    (*assumes l_len[simp,arith]: "4 < LENGTH('l)"*)
  begin
      
    abbreviation "assn \<equiv> al_assn' TYPE('l) elem_assn"
    abbreviation "idx_assn \<equiv> snat_assn' TYPE('l)"
    definition "heap_assn \<equiv> hr_comp (al_assn elem_assn) heap_rel1"

    lemma mk_free_heap_assn[sepref_frame_free_rules]: "MK_FREE heap_assn arl_free"
      unfolding heap_assn_def
      by (rule sepref_frame_free_rules)+
  
    (*context
      assumes l_len_pre: "(4 < LENGTH('l))"
    begin  
      private lemma l_len: "4 < LENGTH('l)" using l_len_pre unfolding vcg_tag_defs by auto
    *)  
  
      sepref_register prio
  
      sepref_register "(\<le>) :: 'p \<Rightarrow> 'p \<Rightarrow> bool"
      sepref_register "(<) :: 'p \<Rightarrow> 'p \<Rightarrow> bool"
      
      lemmas [sepref_frame_free_rules] = 
        mk_free_is_pure[OF prio_is_pure]
        mk_free_is_pure[OF elem_is_pure]
          
      sepref_register update_op
      sepref_definition update_impl is "uncurry2 update_op" 
        :: "assn\<^sup>d *\<^sub>a idx_assn\<^sup>k *\<^sub>a elem_assn\<^sup>k \<rightarrow>\<^sub>a assn"
        unfolding update_op_def[abs_def]
        apply (annot_snat_const "TYPE('l)")
        by sepref
      lemmas [sepref_fr_rules] = update_impl.refine
          
      sepref_register val_of_op
      sepref_definition val_of_impl is "uncurry val_of_op" :: "assn\<^sup>k *\<^sub>a idx_assn\<^sup>k \<rightarrow>\<^sub>a elem_assn"
        unfolding val_of_op_def[abs_def]
        apply (annot_snat_const "TYPE('l)")
        by sepref
      lemmas [sepref_fr_rules] = val_of_impl.refine
    
      sepref_register exch_op
      sepref_definition exch_impl is "uncurry2 exch_op" :: "assn\<^sup>d *\<^sub>a idx_assn\<^sup>k *\<^sub>a idx_assn\<^sup>k \<rightarrow>\<^sub>a assn"
        unfolding exch_op_def[abs_def] mop_list_swap_unfold
        apply (annot_snat_const "TYPE('l)")
        by sepref
        
      lemmas [sepref_fr_rules] = exch_impl.refine
    
      sepref_register valid
      sepref_definition valid_impl is "uncurry (RETURN oo valid)" :: "assn\<^sup>k *\<^sub>a idx_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
        unfolding valid_def[abs_def]
        apply (annot_snat_const "TYPE('l)")
        by sepref
      lemmas [sepref_fr_rules] = valid_impl.refine
          
      sepref_register prio_of_op  
      sepref_definition prio_of_impl is "uncurry (PR_CONST prio_of_op)" :: "assn\<^sup>k *\<^sub>a idx_assn\<^sup>k \<rightarrow>\<^sub>a prio_assn"
        unfolding prio_of_op_def[abs_def] PR_CONST_def
        by sepref
      lemmas [sepref_fr_rules] = prio_of_impl.refine
      
      sepref_definition append_impl is "uncurry mop_list_append" 
        :: "[\<lambda>(xs,_). length xs + 1 < max_snat LENGTH('l)]\<^sub>a assn\<^sup>d *\<^sub>a elem_assn\<^sup>k \<rightarrow> assn"
        by sepref
      lemmas [sepref_fr_rules] = append_impl.refine 
      
      sepref_register swim_op
      sepref_definition swim_impl is 
        "uncurry (PR_CONST swim_op)" :: "[\<lambda>_. 4<LENGTH('l)]\<^sub>a assn\<^sup>d *\<^sub>a idx_assn\<^sup>k \<rightarrow> assn"
        unfolding swim_op_def[abs_def] parent_def PR_CONST_def
        apply (annot_snat_const "TYPE('l)")
        (* TODO: Workaround/Hack *)
        supply [sepref_frame_match_rules] = workaround_invalid_recombine_pure2[where B=snat_assn, simplified]
        by sepref_dbg_keep
  
      lemmas [sepref_fr_rules] = swim_impl.refine
  
      
      lemma overflow_safe_hbound_check: "2*k\<le>n \<longleftrightarrow> k\<le>n div 2" for k n :: nat by auto
      
      (*lemma bound_aux1: "rdomp assn xs \<Longrightarrow> j\<le>length xs div 2 \<Longrightarrow> 2*j < max_snat LENGTH('l)"  
        apply sepref_bounds*)

      (*          
      lemma bound_aux2: "\<lbrakk>rdomp assn a1'; 2 * a2' < length a1'\<rbrakk> 
        \<Longrightarrow> Suc (2 * a2') < max_snat LENGTH('l)"  
        apply sepref_bounds
        apply (drule al_assn_len_bound)
        by auto
      *)
        
      sepref_register sink_op
      sepref_definition sink_impl is "uncurry (PR_CONST sink_op)" :: "[\<lambda>_. 4<LENGTH('l)]\<^sub>a assn\<^sup>d *\<^sub>a idx_assn\<^sup>k \<rightarrow> assn"
        unfolding sink_op_opt_def[abs_def] sink_op_opt_eq[symmetric,abs_def]  PR_CONST_def
        unfolding overflow_safe_hbound_check Suc_eq_plus1
        (* TODO: Workaround/Hack *)
        supply [sepref_frame_match_rules] = workaround_invalid_recombine_pure2[where B=snat_assn, simplified]
        apply (annot_snat_const "TYPE('l)")
        by sepref
        
      lemmas [sepref_fr_rules] = sink_impl.refine
  
      
      lemma prenorm_heaprel1_len: "(h,m)\<in>heap_rel1 \<Longrightarrow> length h = size m"
        unfolding heap_rel1_def in_br_conv
        by auto
      lemma max_snat_param: "(max_snat,max_snat)\<in>nat_rel \<rightarrow> nat_rel" by simp

      context
        notes [fcomp_norm_unfold] = heap_assn_def[symmetric] list_rel_id_simp mset_rel_id
        notes [fcomp_prenorm_simps] = prenorm_heaprel1_len
        notes [param] = IdI[of N] max_snat_param
      begin    
      
        sepref_definition empty_impl is "uncurry0 empty_op" :: "[\<lambda>_. 4<N]\<^sub>a unit_assn\<^sup>k \<rightarrow> assn"
          unfolding empty_op_def N_def
          apply (rewrite al_fold_custom_empty[where 'l='l])
          by sepref
        sepref_decl_impl (no_register) heap_empty: empty_impl.refine[FCOMP empty_op_refine] 
          uses op_mset_empty.fref[of Id] .
    
        sepref_definition is_empty_impl is "is_empty_op" :: "assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
          unfolding is_empty_op_def[abs_def]
          apply (annot_snat_const "TYPE('l)")
          by sepref
        sepref_decl_impl heap_is_empty: is_empty_impl.refine[FCOMP is_empty_op_refine] 
          uses op_mset_is_empty.fref[of Id] .  
    
        sepref_definition insert_impl
          is "uncurry insert_op" :: "[\<lambda>(_,xs). 4<N \<and> length xs+1 < max_snat N]\<^sub>a elem_assn\<^sup>k *\<^sub>a assn\<^sup>d \<rightarrow> assn"
          unfolding insert_op_def[abs_def] append_op_def N_def
          by sepref
        sepref_decl_impl heap_insert: insert_impl.refine[FCOMP insert_op_refine] 
          uses op_mset_insert.fref[of Id] .
          
        sepref_definition pop_min_impl is "pop_min_op" :: "[\<lambda>_. 4<N]\<^sub>a assn\<^sup>d \<rightarrow> elem_assn \<times>\<^sub>a assn"
          unfolding pop_min_op_def[abs_def] butlast_op_def N_def
          apply (annot_snat_const "TYPE('l)")
          by sepref
        sepref_decl_impl (no_mop) heap_pop_min: pop_min_impl.refine[FCOMP pop_min_op_refine] 
          uses op_prio_pop_min.fref[of Id] .
        
        
    
        sepref_definition peek_min_impl is "peek_min_op" :: "assn\<^sup>k \<rightarrow>\<^sub>a elem_assn"
          unfolding peek_min_op_def[abs_def]
          apply (annot_snat_const "TYPE('l)")
          by sepref
        sepref_decl_impl (no_mop) heap_peek_min: peek_min_impl.refine[FCOMP peek_min_op_refine] 
          uses op_prio_peek_min.fref[of Id] .
                  
      end
    (*end        *)

  end  
    

  global_interpretation heap_impl id snat_assn snat_assn return ll_icmp_sle ll_icmp_slt "TYPE('l::len2)" "LENGTH('l)"
    defines h_update_impl = update_impl
        and h_val_of_impl = val_of_impl
        and h_exch_impl = exch_impl
        and h_valid_impl = valid_impl
        and h_prio_of_impl = prio_of_impl
        and h_append_impl = append_impl
        and h_swim_impl = swim_impl
        and h_sink_impl = sink_impl
        and h_empty_impl = empty_impl
        and h_is_empty_impl = is_empty_impl
        and h_insert_impl = insert_impl
        and h_pop_min_impl = pop_min_impl
        and h_peek_min_impl = peek_min_impl
  
    apply unfold_locales
    apply (rule pure_pure)
    apply sepref
    apply sepref
    apply sepref
    apply simp
    done

   
  lemmas heap_impl_inlines = 
    heap_impl.valid_impl_def[OF heap_impl_axioms]  
    heap_impl.prio_of_impl_def[OF heap_impl_axioms]
    heap_impl.val_of_impl_def[OF heap_impl_axioms]
    heap_impl.append_impl_def[OF heap_impl_axioms]
    heap_impl.exch_impl_def[OF heap_impl_axioms]
    heap_impl.empty_impl_def[OF heap_impl_axioms]
    heap_impl.is_empty_impl_def[OF heap_impl_axioms]
    heap_impl.insert_impl_def[OF heap_impl_axioms]
    heap_impl.pop_min_impl_def[OF heap_impl_axioms]
    heap_impl.peek_min_impl_def[OF heap_impl_axioms]
    
    h_swim_impl_def[symmetric]
    h_sink_impl_def[symmetric]
    
  lemmas [llvm_inline] = update_impl_def 
  lemmas [llvm_inline] = val_of_impl_def 
  lemmas [llvm_inline] = exch_impl_def    
  lemmas [llvm_inline] = h_valid_impl_def[unfolded heap_impl_inlines]
  lemmas [llvm_inline] = h_prio_of_impl_def[unfolded heap_impl_inlines]
  lemmas [llvm_inline] = h_append_impl_def[unfolded heap_impl_inlines]
  lemmas [llvm_code] = h_swim_impl_def[unfolded heap_impl.swim_impl_def[OF heap_impl_axioms], unfolded heap_impl_inlines]
  lemmas [llvm_code] = h_sink_impl_def[unfolded heap_impl.sink_impl_def[OF heap_impl_axioms], unfolded heap_impl_inlines]
  lemmas [llvm_inline] = h_empty_impl_def[unfolded heap_impl_inlines]
  lemmas [llvm_inline] = h_is_empty_impl_def[unfolded heap_impl_inlines]
  lemmas [llvm_inline] = h_insert_impl_def[unfolded heap_impl_inlines]
  lemmas [llvm_inline] = h_pop_min_impl_def[unfolded heap_impl_inlines]
  lemmas [llvm_inline] = h_peek_min_impl_def[unfolded heap_impl_inlines]
  
  definition [simp]: "op_heap_custom_empty (_::'a::len2 itself) (_::'l::len2 itself) \<equiv> op_mset_empty"
  context fixes Q T :: "_::len2 itself" begin sepref_register "op_heap_custom_empty Q T" end
  
  lemma op_heap_custom_empty_hnr[sepref_fr_rules]:
    shows "(
      uncurry0 (empty_impl::('a::len2 word,'l)array_list llM ), 
      uncurry0 (RETURN (PR_CONST (op_heap_custom_empty TYPE('a) TYPE('l))))) \<in> [\<lambda>_. 4<LENGTH('l::len2)]\<^sub>a unit_assn\<^sup>k \<rightarrow> heap_assn"
    unfolding op_heap_custom_empty_def PR_CONST_def
    by (rule heap_empty_hnr[unfolded PRECOND_def])
    
  lemma heap_fold_custom_empty: 
    "{#} = op_heap_custom_empty TYPE('a::len2) TYPE('l::len2)"
    "op_mset_empty = op_heap_custom_empty TYPE('a::len2) TYPE('l::len2)"
    "mop_mset_empty = RETURN (op_heap_custom_empty TYPE('a::len2) TYPE('l::len2))"
    by auto
  
    
      
  
    
definition "sort_by_prio l\<^sub>0 \<equiv> do {
  q \<leftarrow> nfoldli l\<^sub>0 (\<lambda>_. True) (\<lambda>x q. do { ASSERT (size q < length l\<^sub>0); mop_mset_insert x q }) {#};
  ASSERT (q = mset l\<^sub>0);
  (l,q) \<leftarrow> WHILEIT (\<lambda>(l,q). sorted l \<and> (\<forall>x\<in>set l. \<forall>y\<in>#q. x\<le>y) \<and> mset l + q = mset l\<^sub>0) 
    (\<lambda>(l,q). \<not>op_mset_is_empty q) (\<lambda>(l,q). 
  do {
    (x,q) \<leftarrow> mop_prio_pop_min id q;
    ASSERT (size l < length l\<^sub>0);
    RETURN (l@[x],q)
  }) (op_list_empty,q);
  RETURN l
}"

lemma sort_by_prio_correct: "sort_by_prio l \<le> SPEC (\<lambda>l'. sorted l' \<and> mset l' = mset l)"
  unfolding sort_by_prio_def mop_prio_pop_min_def
  
  apply (refine_vcg 
    nfoldli_rule[where I="\<lambda>ll _ q. q = mset ll"]
    WHILEIT_rule[where R="measure (\<lambda>(l,q). size q)"]
    )
  apply (auto 0 3 dest: in_diffD simp: size_Diff1_less sorted_append_bigger)
  subgoal by (metis add_cancel_right_right le_add1 nat_less_le size_eq_0_iff_empty size_mset size_union) 
  subgoal by (metis insert_DiffM union_iff) 
  done
  


(* TODO: Move  *)
function list_intv_induction where
  "list_intv_induction l u = (if l<u then list_intv_induction (Suc l) u else ())"
  by pat_completeness auto

termination
  apply (relation "measure (\<lambda>(l,u). u-l)")
  by auto
  
  
(*  
lemma nfoldli_range_to_while: "nfoldli [l..<u] c f \<sigma> = do {
    (_,\<sigma>) \<leftarrow> WHILET 
      (\<lambda>(i,\<sigma>). i<u \<and> c \<sigma>) 
      (\<lambda>(i,\<sigma>). do { \<sigma> \<leftarrow> f i \<sigma>; ASSERT (i<u); RETURN (i+1,\<sigma>) })
      (l,\<sigma>);
    RETURN \<sigma>
  }"
proof (induction l u arbitrary: \<sigma> rule: list_intv_induction.induct)
  case (1 l u)
  show ?case proof (cases "l<u")
    case False thus ?thesis
      by (rewrite WHILET_unfold) simp
      
  next
    case True 
    thm "1.IH"[OF True, abs_def]
    thus ?thesis 
      by (rewrite WHILET_unfold) (simp add: upt_conv_Cons "1.IH"[OF True, abs_def])
  qed
qed
*)  



sepref_definition sort_impl [llvm_code] is 
  "sort_by_prio" :: "[\<lambda>l. length l < max_snat LENGTH(64)]\<^sub>a (al_assn' TYPE(64) (snat_assn' TYPE(64)))\<^sup>k \<rightarrow> al_assn' TYPE(64) (snat_assn' TYPE(64))"
  unfolding sort_by_prio_def[abs_def] 
  apply (rewrite nfoldli_by_idx)
  apply (rewrite nfoldli_upt_by_while)
  apply (rewrite heap_fold_custom_empty[where 'l=64 and 'a="64"])
  apply (rewrite at op_list_empty al_fold_custom_empty[where 'l=64])
  apply (annot_snat_const "TYPE(64)")
  by sepref

  
  
export_llvm (no_header)
  sort_impl is "sort" 
  "arl_new_raw :: (64 word,64) array_list llM" is "arl_new"
  "arl_push_back :: _ \<Rightarrow> _ \<Rightarrow> (64 word,64) array_list llM" is "arl_push_back"
  file "sort.ll"
  (* CAREFUL: The calling conventions generated by this LLVM code are hard/impossible to 
    interface from C !? *)
  
end
