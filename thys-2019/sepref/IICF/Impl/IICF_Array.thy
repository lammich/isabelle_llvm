theory IICF_Array
imports "../Intf/IICF_List" 
begin




section \<open>Plain Arrays Implementing List Interface\<close>

subsection \<open>Abstract Replicate-Init Operation\<close>
  definition [simp]: "replicate_init_raw n \<equiv> replicate n init"

  locale replicate_init = 
    fixes repl :: "'a \<Rightarrow> nat \<Rightarrow> 'a list"  
    assumes repl_def[simp]: "repl i n = replicate n i"
  begin
  
    context fixes i::'a begin
      sepref_register "repl i" 
    end
    
    lemma replicate_init_param:
      fixes A :: "'a \<Rightarrow> 'c::llvm_rep \<Rightarrow> assn"
      assumes INIT: "GEN_ALGO i (is_init A)"
      shows "(RETURN o replicate_init_raw, RETURN o PR_CONST (repl i)) \<in> nat_rel \<rightarrow>\<^sub>f \<langle>\<langle>the_pure A\<rangle>list_rel\<rangle>nres_rel"
    proof -
      from INIT have [param]: "(init,i) \<in> the_pure A" unfolding is_init_def GEN_ALGO_def by simp
      show ?thesis
        unfolding repl_def replicate_init_raw_def PR_CONST_def 
        apply (rule frefI)
        apply (parametricity)
        done
        
    qed
    
    lemma fold_replicate_init: "replicate n i = repl i n" by simp
  end

subsection \<open>Abstract grow-init Operation\<close>

  definition [simp]: "op_list_grow_init i ns os xs \<equiv> take os xs @ replicate (ns - os) i" 
  context fixes i begin
    sepref_register "op_list_grow_init i"
  end

  definition [simp]: "grow_init_raw ns os xs \<equiv> take os xs @ replicate (ns - os) init"

  lemma grow_init_param:
    fixes A :: "'a \<Rightarrow> 'c::llvm_rep \<Rightarrow> assn"
    assumes INIT: "GEN_ALGO i (is_init A)"
    shows "(uncurry2 (RETURN ooo grow_init_raw), uncurry2 (RETURN ooo PR_CONST (op_list_grow_init i))) \<in> [\<lambda>_. True]\<^sub>f (nat_rel \<times>\<^sub>r nat_rel) \<times>\<^sub>r \<langle>the_pure A\<rangle>list_rel \<rightarrow> \<langle>\<langle>the_pure A\<rangle>list_rel\<rangle>nres_rel"
  proof -  
    from INIT have [param]: "(init,i) \<in> the_pure A" unfolding is_init_def GEN_ALGO_def by simp
    have "(grow_init_raw, op_list_grow_init i) \<in> nat_rel \<rightarrow> nat_rel \<rightarrow> \<langle>the_pure A\<rangle>list_rel \<rightarrow> \<langle>the_pure A\<rangle>list_rel"
      unfolding op_list_grow_init_def grow_init_raw_def
      by parametricity
    from this[to_fref] show ?thesis unfolding PR_CONST_def  
      by (auto intro!: frefI nres_relI dest!: frefD)
      
  qed
  
  
    
    
  sepref_decl_op list_free: "\<lambda>_::_ list. ()" :: "\<langle>A\<rangle>list_rel \<rightarrow> unit_rel" .

  

subsection \<open>Definition of Assertion\<close>

  text \<open>Lists of fixed length are directly implemented with arrays. \<close>
  
  hide_const (open) LLVM_DS_Array.array_assn
  
  abbreviation "raw_array_assn \<equiv> \<upharpoonleft>LLVM_DS_NArray.narray_assn"

  definition array_assn where "array_assn A \<equiv> hr_comp raw_array_assn (\<langle>the_pure A\<rangle>list_rel)"
  lemmas [safe_constraint_rules] = CN_FALSEI[of is_pure "array_assn A" for A]

subsection \<open>Interface Implementation\<close>  
    
definition [simp]: "array_replicate_init i n \<equiv> replicate n i"
interpretation array: replicate_init array_replicate_init by unfold_locales simp


context 
  notes [fcomp_norm_unfold] = array_assn_def[symmetric]
  (*notes [simp] = pure_def hn_ctxt_def is_array_def invalid_assn_def*)
begin  

  lemma array_get_hnr_aux: "(uncurry array_nth,uncurry (RETURN oo op_list_get)) 
    \<in> [\<lambda>(l,i). i<length l]\<^sub>a raw_array_assn\<^sup>k *\<^sub>a snat_assn\<^sup>k \<rightarrow> id_assn"  
    unfolding snat_rel_def snat.assn_is_rel[symmetric]
    apply sepref_to_hoare
    apply vcg'
    done
    
  sepref_decl_impl array_get: array_get_hnr_aux .  

  lemma array_set_hnr_aux: "(uncurry2 array_upd,uncurry2 (RETURN ooo op_list_set)) 
    \<in> [\<lambda>((l,i),_). i<length l]\<^sub>a raw_array_assn\<^sup>d *\<^sub>a snat_assn\<^sup>k *\<^sub>a id_assn\<^sup>k \<rightarrow> raw_array_assn"  
    unfolding snat_rel_def snat.assn_is_rel[symmetric] 
    apply sepref_to_hoare
    apply (clarsimp simp: invalid_assn_def)
    apply (rule htriple_pure_preI, ((determ \<open>drule pure_part_split_conj|erule conjE\<close>)+)?)
    apply vcg
    done
    
  sepref_decl_impl array_set: array_set_hnr_aux .
  
  lemma hn_array_repl_init_raw:
    shows "(narray_new TYPE('c::llvm_rep),RETURN o replicate_init_raw) \<in> snat_assn\<^sup>k \<rightarrow>\<^sub>a raw_array_assn"
    unfolding snat_rel_def snat.assn_is_rel[symmetric]
    apply sepref_to_hoare
    apply vcg'
    done

  sepref_decl_impl (no_mop) hn_array_repl_init_raw uses array.replicate_init_param . 
  
  lemma hn_array_grow_init_raw:
    shows "(uncurry2 array_grow, uncurry2 (RETURN ooo grow_init_raw)) 
      \<in> [\<lambda>((ns,os),xs). os\<le>length xs \<and> os\<le>ns]\<^sub>a snat_assn\<^sup>k *\<^sub>a snat_assn\<^sup>k *\<^sub>a raw_array_assn\<^sup>d \<rightarrow> raw_array_assn"
    unfolding snat_rel_def snat.assn_is_rel[symmetric]
    apply sepref_to_hoare
    by vcg'
    
  sepref_decl_impl (no_mop) hn_array_grow_init_raw uses grow_init_param .
  
  sepref_decl_op array_custom_replicate: op_list_replicate :: "nat_rel \<rightarrow> A \<rightarrow> \<langle>A\<rangle>list_rel" .
  
  lemma hn_array_replicate_new_raw:
    "(uncurry narray_new_init, uncurry (RETURN oo op_array_custom_replicate)) \<in> snat_assn\<^sup>k *\<^sub>a id_assn\<^sup>k \<rightarrow>\<^sub>a raw_array_assn"
    unfolding snat_rel_def snat.assn_is_rel[symmetric]
    apply sepref_to_hoare
    by vcg
    
  sepref_decl_impl hn_array_replicate_new_raw .
  
  lemma array_fold_custom_replicate: 
    "replicate = op_array_custom_replicate"
    "op_list_replicate = op_array_custom_replicate"
    "mop_list_replicate = mop_array_custom_replicate"
    by (auto del: ext intro!: ext)
  
  lemma hn_array_free_raw: "(narray_free,RETURN o op_list_free) \<in> raw_array_assn\<^sup>d \<rightarrow>\<^sub>a unit_assn"
    by sepref_to_hoare vcg
  
  sepref_decl_impl array_free: hn_array_free_raw .
  lemmas array_mk_free[sepref_frame_free_rules] = hn_MK_FREEI[OF array_free_hnr]
  
end  
  
  
  
section \<open>Arrays with Length\<close>

definition "larray1_rel = br snd (\<lambda>(n,xs). n = length xs)"
abbreviation "larray_impl_assn' TYPE('b::len2) \<equiv> snat_assn' TYPE('b) \<times>\<^sub>a array_assn id_assn"
definition "raw_larray_assn \<equiv> hr_comp (larray_impl_assn' TYPE(_)) larray1_rel"

definition "larray_assn A \<equiv>  hr_comp raw_larray_assn (\<langle>the_pure A\<rangle>list_rel)"

abbreviation larray_assn' 
  :: "'b itself \<Rightarrow> ('a \<Rightarrow> 'c \<Rightarrow> llvm_amemory \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'b::len2 word \<times> 'c::llvm_rep ptr \<Rightarrow> llvm_amemory \<Rightarrow> bool" 
  where
  "larray_assn' _ == larray_assn"

type_synonym ('x,'l) larray = "'l word \<times> 'x ptr"

lemma larray1_rel_prenorm: "((n, xs), ys) \<in> larray1_rel \<longleftrightarrow> n = length ys \<and> xs=ys"  
  by (auto simp: larray1_rel_def in_br_conv)


definition [simp]: "larray_replicate_init i n \<equiv> replicate n i"
interpretation larray: replicate_init larray_replicate_init by unfold_locales simp
  

context 
  notes [fcomp_norm_unfold] = raw_larray_assn_def[symmetric] larray_assn_def[symmetric]
  notes [fcomp_prenorm_simps] = larray1_rel_prenorm
begin

sepref_decl_op larray_custom_replicate: op_list_replicate :: "nat_rel \<rightarrow> A \<rightarrow> \<langle>A\<rangle>list_rel" .

definition "la_replicate1 n i \<equiv> (n, replicate n i)"
lemma la_replicate1_refine: "(la_replicate1,op_larray_custom_replicate) \<in> nat_rel \<rightarrow> Id \<rightarrow> larray1_rel"
  by (auto simp: larray1_rel_def in_br_conv la_replicate1_def)
  
sepref_definition la_replicate_impl [llvm_inline] is "uncurry (RETURN oo la_replicate1)" 
  :: "(snat_assn' TYPE('b::len2))\<^sup>k *\<^sub>a id_assn\<^sup>k \<rightarrow>\<^sub>a larray_impl_assn' TYPE('b::len2)"
  unfolding la_replicate1_def 
  apply (rewrite array_fold_custom_replicate)
  apply sepref_dbg_keep
  done
  
sepref_decl_impl la_replicate_impl.refine[FCOMP la_replicate1_refine] . 

lemma larray_fold_custom_replicate: 
  "replicate = op_larray_custom_replicate"
  "op_list_replicate = op_larray_custom_replicate"
  "mop_list_replicate = mop_larray_custom_replicate"
  by (auto del: ext intro!: ext)



definition "la_replicate_init1 n \<equiv> (n, array_replicate_init init n)"
lemma la_replicate_init1_refine: "(la_replicate_init1, replicate_init_raw) \<in> nat_rel \<rightarrow> larray1_rel"
  by (auto simp: larray1_rel_def in_br_conv la_replicate_init1_def)
  
    
sepref_definition la_replicate_init_impl [llvm_inline] is "(RETURN o la_replicate_init1)" 
  :: "(snat_assn' TYPE('b::len2))\<^sup>k \<rightarrow>\<^sub>a larray_impl_assn' TYPE('b::len2)"
  unfolding la_replicate_init1_def 
  apply sepref_dbg_keep
  done

sepref_decl_impl (no_mop) la_replicate_init_impl.refine[FCOMP la_replicate_init1_refine] uses larray.replicate_init_param .
  


definition "la_grow_init1 \<equiv> \<lambda>ns os (n,xs). (ns, op_list_grow_init init ns os xs)"
lemma la_grow_init1_refine: "(uncurry2 la_grow_init1, uncurry2 grow_init_raw) 
  \<in> [\<lambda>((ns,os),xs). os\<le>length xs \<and> os\<le>ns]\<^sub>f (nat_rel \<times>\<^sub>r nat_rel) \<times>\<^sub>r larray1_rel \<rightarrow> larray1_rel"
  by (auto simp: larray1_rel_def in_br_conv la_grow_init1_def intro!: frefI)
  
    
sepref_definition la_grow_init_impl [llvm_inline] is "(uncurry2 (RETURN ooo la_grow_init1))" 
  :: "[\<lambda>((ns,os),(n,xs)). os\<le>length xs \<and> os\<le>ns]\<^sub>a (snat_assn' TYPE('b::len2))\<^sup>k *\<^sub>a (snat_assn' TYPE('b::len2))\<^sup>k *\<^sub>a (larray_impl_assn' TYPE('b::len2))\<^sup>d \<rightarrow> larray_impl_assn' TYPE('b::len2)"
  unfolding la_grow_init1_def 
  by sepref

sepref_decl_impl (no_mop) la_grow_init_impl.refine[FCOMP la_grow_init1_refine] uses grow_init_param .

definition [simp]: "op_list_grow_init' i ns xs \<equiv> xs@replicate (ns-length xs) i"

lemma op_list_grow_init'_alt: "op_list_grow_init' i ns xs = op_list_grow_init i ns (length xs) xs" by simp


definition "la_length1 nxs \<equiv> case nxs of (n,_) \<Rightarrow> id n"
lemma la_length1_refine: "(la_length1,op_list_length) \<in> larray1_rel \<rightarrow> nat_rel"
  by (auto simp: larray1_rel_def in_br_conv la_length1_def)

sepref_definition la_length_impl [llvm_inline] is "RETURN o la_length1" :: "(larray_impl_assn' TYPE('b::len2))\<^sup>k \<rightarrow>\<^sub>a snat_assn' TYPE('b)"
  unfolding la_length1_def 
  apply sepref_dbg_keep
  done
  
sepref_decl_impl la_length_impl.refine[FCOMP la_length1_refine] . 


  
definition "la_is_empty1 nxs \<equiv> case nxs of (n,_) \<Rightarrow> n=0"
lemma la_is_empty1_refine: "(la_is_empty1,op_list_is_empty) \<in> larray1_rel \<rightarrow> bool_rel"
  by (auto simp: larray1_rel_def in_br_conv la_is_empty1_def)
    
sepref_definition la_is_empty_impl [llvm_inline] is "RETURN o la_is_empty1" :: "(larray_impl_assn' TYPE('b::len2))\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  unfolding la_is_empty1_def 
  apply (annot_snat_const "TYPE('b)")
  apply sepref_dbg_keep
  done

sepref_decl_impl la_is_empty_impl.refine[FCOMP la_is_empty1_refine] . 
  

  
definition "la_get1 nxs i \<equiv> case nxs of (n,xs) \<Rightarrow> xs!i"
lemma la_get1_refine: "(la_get1,op_list_get) \<in> larray1_rel \<rightarrow> nat_rel \<rightarrow> Id"
  by (auto simp: larray1_rel_def in_br_conv la_get1_def)
  
sepref_definition la_get_impl [llvm_inline] is "uncurry (RETURN oo la_get1)" :: "[\<lambda>(la,i). i<length (snd la)]\<^sub>a (larray_impl_assn' TYPE('b::len2))\<^sup>k *\<^sub>a (snat_assn' TYPE('c::len2))\<^sup>k \<rightarrow> id_assn"
  unfolding la_get1_def la_length1_def
  apply sepref_dbg_keep
  done
  
sepref_decl_impl la_get_impl.refine[FCOMP la_get1_refine] .
  

definition "la_set1 nxs i x \<equiv> case nxs of (n,xs) \<Rightarrow> (n,xs[i:=x])"
lemma la_set1_refine: "(la_set1,op_list_set) \<in> larray1_rel \<rightarrow> nat_rel \<rightarrow> Id \<rightarrow> larray1_rel"
  by (auto simp: larray1_rel_def in_br_conv la_set1_def)
  
sepref_definition la_set_impl [llvm_inline] is "uncurry2 (RETURN ooo la_set1)" 
  :: "[\<lambda>((la,i),_). i<length (snd la)]\<^sub>a (larray_impl_assn' TYPE('b::len2))\<^sup>d *\<^sub>a (snat_assn' TYPE('c::len2))\<^sup>k *\<^sub>a id_assn\<^sup>k \<rightarrow> larray_impl_assn' TYPE('b::len2)"
  unfolding la_set1_def
  apply sepref_dbg_keep
  done
  
sepref_decl_impl la_set_impl.refine[FCOMP la_set1_refine] .

definition "la_free1 nxs \<equiv> case nxs of (_,xs) \<Rightarrow> op_list_free xs"
lemma la_free1_refine: "(la_free1,op_list_free) \<in> larray1_rel \<rightarrow> unit_rel" by auto

sepref_definition la_free_impl [llvm_inline] is "RETURN o la_free1" :: "(larray_impl_assn' TYPE(_))\<^sup>d \<rightarrow>\<^sub>a unit_assn"
  unfolding la_free1_def
  by sepref

sepref_decl_impl larray_free: la_free_impl.refine[FCOMP la_free1_refine] .
lemmas larray_mk_free[sepref_frame_free_rules] = hn_MK_FREEI[OF larray_free_hnr]
  
end
  

lemma rdomp_larray_imp_len_bound: 
  "rdomp (larray_assn' TYPE('a::len2) A) xs \<Longrightarrow> length xs < max_snat LENGTH('a)"
  unfolding larray_assn_def raw_larray_assn_def larray1_rel_def
  apply (auto simp: rdomp_hrcomp_conv in_br_conv snat_rel_def snat.rel_def)
  by (simp add: list_rel_pres_length)




subsection \<open>Ad-Hoc Regression Tests\<close>
  
sepref_definition example1 [llvm_code] is "\<lambda>n. RETURN (replicate (n+1) (snat_init TYPE(32)))" 
  :: "[\<lambda>n. n\<in>{1..<150}]\<^sub>a (snat_assn' TYPE(32))\<^sup>k \<rightarrow> array_assn (snat_assn' TYPE(32))"
  supply [simp] = max_snat_def
  apply (annot_snat_const "TYPE(32)")
  apply (rewrite array.fold_replicate_init)
  apply sepref_dbg_keep
  done
  
sepref_definition example2 [llvm_code] is \<open>\<lambda>n. do {
  ASSERT (n>10);
  let a = replicate n (snat_const TYPE(64) 42);
  let a = a[snat_const TYPE(32) 3:=0];
  ASSERT (a!1=42 \<and> a!2=42);
  RETURN (a!snat_const TYPE(32) 1 + a!snat_const TYPE(32) 2)
}\<close> :: "(snat_assn' TYPE(32))\<^sup>k \<rightarrow>\<^sub>a snat_assn' TYPE(64)"
  supply [simp] = max_snat_def
  apply (annot_snat_const "TYPE(64)")
  apply (rewrite array_fold_custom_replicate)
  apply sepref_dbg_keep
  done
  
  
sepref_definition example1n [llvm_code] is "\<lambda>n. RETURN (replicate (n+1) (snat_init TYPE(8)))" 
  :: "[\<lambda>n. n\<in>{1..<150}]\<^sub>a (snat_assn' TYPE(32))\<^sup>k \<rightarrow> larray_assn' TYPE(32) (snat_assn' TYPE(8))"
  supply [simp] = max_snat_def
  apply (rewrite larray.fold_replicate_init)
  apply (annot_snat_const "TYPE(32)")
  apply sepref_dbg_keep
  done
  
  
sepref_definition example2n [llvm_code] is \<open>\<lambda>n. do {
  ASSERT (n>10);
  let a = replicate n (snat_const TYPE(64) 42);
  let a = a[snat_const TYPE(32) 3:=0];
  ASSERT (a!1=42 \<and> a!2=42);
  RETURN (a!snat_const TYPE(32) 1 + a!snat_const TYPE(32) 2)
}\<close> :: "(snat_assn' TYPE(32))\<^sup>k \<rightarrow>\<^sub>a snat_assn' TYPE(64)"
  supply [simp] = max_snat_def
  apply (annot_snat_const "TYPE(64)")
  apply (rewrite larray_fold_custom_replicate)
  apply sepref_dbg_keep
  done

  
export_llvm example1 example2 example1n example2n
    
  
end
