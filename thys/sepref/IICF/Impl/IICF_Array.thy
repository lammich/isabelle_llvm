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

  lemma array_assn_comp: "hr_comp (array_assn id_assn) (\<langle>the_pure A\<rangle>list_rel) = array_assn (A)"
    unfolding array_assn_def by simp
  
  
subsection \<open>Interface Implementation\<close>  
    
definition [simp]: "array_replicate_init i n \<equiv> replicate n i"
interpretation array: replicate_init array_replicate_init by unfold_locales simp




context 
  notes [fcomp_norm_unfold] = array_assn_def[symmetric] array_assn_comp
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
    \<in> [\<lambda>((l,i),_). i<length l]\<^sub>a [\<lambda>_. True]\<^sub>c raw_array_assn\<^sup>d *\<^sub>a snat_assn\<^sup>k *\<^sub>a id_assn\<^sup>k 
      \<rightarrow>\<^sub>d (\<lambda>_. raw_array_assn) [\<lambda>((ai,_),_) r. r=ai]\<^sub>c"  
    unfolding snat_rel_def snat.assn_is_rel[symmetric] 
    apply sepref_to_hoare
    apply (clarsimp simp: invalid_assn_def)
    apply (rule htriple_pure_preI, ((determ \<open>drule pure_part_split_conj|erule conjE\<close>)+)?)
    apply vcg
    done
    
  sepref_decl_impl array_set: array_set_hnr_aux .

  sepref_definition array_swap [llvm_code] is "uncurry2 (mop_list_swap)" 
    :: "[\<lambda>_. True]\<^sub>c (array_assn id_assn)\<^sup>d *\<^sub>a (snat_assn)\<^sup>k *\<^sub>a (snat_assn)\<^sup>k 
      \<rightarrow> array_assn id_assn [\<lambda>((ai,_),_) r. r=ai]\<^sub>c"
    unfolding gen_mop_list_swap by sepref
    
  sepref_decl_impl (ismop) array_swap.refine .
  
    
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
  
section \<open>Array Slice\<close>

subsection \<open>Definition of Assertion\<close>

  text \<open>Lists of fixed length are directly implemented with arrays. \<close>
  
  hide_const (open) LLVM_DS_Array.array_assn
  
  abbreviation "raw_array_slice_assn \<equiv> \<upharpoonleft>LLVM_DS_NArray.array_slice_assn"

  definition array_slice_assn where "array_slice_assn A \<equiv> hr_comp raw_array_slice_assn (\<langle>the_pure A\<rangle>list_rel)"
  lemmas [safe_constraint_rules] = CN_FALSEI[of is_pure "array_slice_assn A" for A]

  lemma array_slice_assn_comp: "hr_comp (array_slice_assn id_assn) (\<langle>the_pure A\<rangle>list_rel) = array_slice_assn (A)"
    unfolding array_slice_assn_def by simp
  
  
subsection \<open>Interface Implementation\<close>  

context 
  notes [fcomp_norm_unfold] = array_slice_assn_def[symmetric] array_slice_assn_comp
  (*notes [simp] = pure_def hn_ctxt_def is_array_def invalid_assn_def*)
begin  

  lemma array_slice_get_hnr_aux: "(uncurry array_nth,uncurry (RETURN oo op_list_get)) 
    \<in> [\<lambda>(l,i). i<length l]\<^sub>a raw_array_slice_assn\<^sup>k *\<^sub>a snat_assn\<^sup>k \<rightarrow> id_assn"  
    unfolding snat_rel_def snat.assn_is_rel[symmetric]
    apply sepref_to_hoare
    apply vcg'
    done
    
  sepref_decl_impl array_slice_get: array_slice_get_hnr_aux .  

  lemma array_slice_set_hnr_aux: "(uncurry2 array_upd,uncurry2 (RETURN ooo op_list_set)) 
    \<in> [\<lambda>((l,i),_). i<length l]\<^sub>a [\<lambda>_. True]\<^sub>c raw_array_slice_assn\<^sup>d *\<^sub>a snat_assn\<^sup>k *\<^sub>a id_assn\<^sup>k 
    \<rightarrow>\<^sub>d (\<lambda>_. raw_array_slice_assn) [\<lambda>((ai,_),_) r. r=ai]\<^sub>c"  
    unfolding snat_rel_def snat.assn_is_rel[symmetric] 
    apply sepref_to_hoare
    apply (clarsimp simp: invalid_assn_def)
    apply (rule htriple_pure_preI, ((determ \<open>drule pure_part_split_conj|erule conjE\<close>)+)?)
    apply vcg
    done
    
  sepref_decl_impl array_slice_set: array_slice_set_hnr_aux .

  sepref_definition array_slice_swap [llvm_code] is "uncurry2 (mop_list_swap)" 
    :: "[\<lambda>_. True]\<^sub>c (array_slice_assn id_assn)\<^sup>d *\<^sub>a (snat_assn)\<^sup>k *\<^sub>a (snat_assn)\<^sup>k 
      \<rightarrow> array_slice_assn id_assn [\<lambda>((ai,_),_) r. r=ai]\<^sub>c"
    unfolding gen_mop_list_swap by sepref
    
  sepref_decl_impl (ismop) array_slice_swap.refine .
  
  definition ars_split :: "_ word \<Rightarrow> 'a::llvm_rep ptr \<Rightarrow> ('a ptr \<times> 'a ptr) llM" 
    where [llvm_inline]: "ars_split i p \<equiv> doM { p\<^sub>2 \<leftarrow> ll_ofs_ptr p i; Mreturn (p,p\<^sub>2)}"
  definition ars_join :: "'a::llvm_rep ptr \<Rightarrow> 'a ptr \<Rightarrow> 'a ptr llM" 
    where [llvm_inline]: "ars_join p\<^sub>1 p\<^sub>2 \<equiv> Mreturn p\<^sub>1"
  
  context begin
    interpretation llvm_prim_mem_setup .  
    interpretation llvm_prim_arith_setup .  

    (* TODO: Move *)
    lemma in_snat_rel_int: "(ii,i)\<in>snat_rel \<Longrightarrow> sint ii = int i"
      by (metis cnv_snat_to_uint(2) in_br_conv snat.rel_def snat_eq_unat(2) snat_rel_def uint_nat)
    
    lemma ll_ofs_ptr_raw_array_slice_rl[vcg_rules]:
      assumes A: "i<length a"
      shows "llvm_htriple (snat_assn i ii ** raw_array_slice_assn a ai) (ll_ofs_ptr ai ii) (\<lambda>r. \<up>(r=ai+\<^sub>aint i) ** snat_assn i ii ** raw_array_slice_assn a ai)"
      unfolding LLVM_DS_NArray.array_slice_assn_def
      apply (subgoal_tac "a\<noteq>[]")
      subgoal
        apply simp
        supply [simp] = in_snat_rel_int A
        by vcg
      subgoal using A by simp
      done
      
    definition "ars_joinable ai\<^sub>1 ai\<^sub>2 n \<equiv> ai\<^sub>2 = ai\<^sub>1 +\<^sub>a int n"    
    lemma ars_join_rl[vcg_rules]:
      shows "llvm_htriple 
        (raw_array_slice_assn a\<^sub>1 ai\<^sub>1 ** raw_array_slice_assn a\<^sub>2 ai\<^sub>2 ** \<up>\<^sub>!(ars_joinable ai\<^sub>1 ai\<^sub>2 (length a\<^sub>1))) 
        (ars_join ai\<^sub>1 ai\<^sub>2) 
        (\<lambda>r. \<up>(r=ai\<^sub>1) ** raw_array_slice_assn (a\<^sub>1@a\<^sub>2) ai\<^sub>1)"    
      unfolding ars_join_def
      supply [simp] = array_slice_assn_split
      unfolding ars_joinable_def
      by vcg  
        
    lemma ars_split_rl[vcg_rules]:
      "llvm_htriple 
        (snat_assn i ii ** raw_array_slice_assn a ai ** \<up>\<^sub>d(i < length a)) 
        (ars_split ii ai)
        (\<lambda>(a\<^sub>1,a\<^sub>2). raw_array_slice_assn (take i a) a\<^sub>1 ** raw_array_slice_assn (drop i a) a\<^sub>2 ** snat_assn i ii ** \<up>(a\<^sub>1=ai \<and> ars_joinable a\<^sub>1 a\<^sub>2 i))"
      unfolding ars_split_def ars_joinable_def
      apply vcg
      apply (subst append_take_drop_id[symmetric, where n=i])
      apply (subst array_slice_assn_split)
      apply vcg_try_solve
      done
  
      
    definition "WITH_SPLIT i xs m \<equiv> doN {
      ASSERT (i<length xs);
      let xs\<^sub>1 = take i xs;
      let xs\<^sub>2 = drop i xs;
      (r,xs\<^sub>1',xs\<^sub>2') \<leftarrow> m xs\<^sub>1 xs\<^sub>2;
      ASSERT (length xs\<^sub>1' = length xs\<^sub>1 \<and> length xs\<^sub>2'=length xs\<^sub>2);
      RETURN (r,xs\<^sub>1'@xs\<^sub>2')
    }"  
    
    (* Monotonicity setup *)
    lemma WITH_SPLIT_mono[refine_mono]: 
      "\<lbrakk>\<And>a b. f a b \<le> f' a b\<rbrakk> \<Longrightarrow> WITH_SPLIT xs n f \<le> WITH_SPLIT xs n f'"
      unfolding WITH_SPLIT_def
      by refine_mono
    
    (* Monadifier setup *)
    lemma WITH_SPLIT_arity[sepref_monadify_arity]: "WITH_SPLIT \<equiv> \<lambda>\<^sub>2xs n f. SP WITH_SPLIT$xs$n$(\<lambda>\<^sub>2a b. f$a$b)"
      by simp
    
    lemma WITH_SPLIT_comb[sepref_monadify_comb]:  
      "WITH_SPLIT$xs$n$f = Refine_Basic.bind$(EVAL$xs)$(\<lambda>\<^sub>2xs. Refine_Basic.bind$(EVAL$n)$(\<lambda>\<^sub>2n. SP WITH_SPLIT$xs$n$f))"
      by simp
    
    thm sepref_monadify_comb  
      
      
    definition [llvm_inline]: "ars_with_split i a m \<equiv> doM {
      (a\<^sub>1,a\<^sub>2) \<leftarrow> ars_split i a;
      (r,_,_) \<leftarrow> m a\<^sub>1 a\<^sub>2;
      ars_join a\<^sub>1 a\<^sub>2;
      Mreturn (r,a)
    }"

    lemma ars_with_split_for_paper: "ars_with_split i a m = doM {
      p\<^sub>2 \<leftarrow> ll_ofs_ptr a i;
      (r, _, _) \<leftarrow> m a p\<^sub>2;
      Mreturn (r, a)
    }"
      unfolding ars_with_split_def ars_split_def ars_join_def
      by simp
    
      
    (* Monotonicity setup *)
    lemma ars_with_split_mono[partial_function_mono]:
      assumes "\<And>xs\<^sub>1 xs\<^sub>2. M_mono' (\<lambda>D. m D xs\<^sub>1 xs\<^sub>2)"
      shows "M_mono' (\<lambda>D. ars_with_split i a (m D))"
      unfolding ars_with_split_def using assms
      by pf_mono_prover
    

    lemma hn_WITH_SPLIT_aux:
      assumes MHN: "\<And>xs\<^sub>1 xsi\<^sub>1 xs\<^sub>2 xsi\<^sub>2. hn_refine (raw_array_slice_assn xs\<^sub>1 xsi\<^sub>1 ** raw_array_slice_assn xs\<^sub>2 xsi\<^sub>2 ** F) (mi xsi\<^sub>1 xsi\<^sub>2) (F') (R \<times>\<^sub>a raw_array_slice_assn \<times>\<^sub>a raw_array_slice_assn) (CP' xsi\<^sub>1 xsi\<^sub>2) (m xs\<^sub>1 xs\<^sub>2)"
      assumes CP': "\<And>xsi\<^sub>1 xsi\<^sub>2 ri xsi\<^sub>1' xsi\<^sub>2'. CP' xsi\<^sub>1 xsi\<^sub>2 (ri,xsi\<^sub>1',xsi\<^sub>2') \<Longrightarrow> xsi\<^sub>1'=xsi\<^sub>1 \<and> xsi\<^sub>2'=xsi\<^sub>2 \<and> CP ri"
      shows "hn_refine 
        (raw_array_slice_assn xs xsi ** snat_assn n ni ** F) 
        (ars_with_split ni xsi mi) 
        (snat_assn n ni) 
        (\<lambda>(r,xs) (ri,xsi). R r ri ** raw_array_slice_assn xs xsi ** F') 
        (\<lambda>(ri,xsi'). xsi'=xsi \<and> CP ri) 
        (WITH_SPLIT n xs m)"  
      apply (sepref_to_hoare)
      unfolding ars_with_split_def WITH_SPLIT_def
      
      supply [simp del] = List.take_all List.drop_all
      supply [simp] = pure_def refine_pw_simps
      
      apply (clarsimp simp: )
      
      supply [vcg_rules] = hn_refineD[OF MHN]
      
      apply vcg
      apply (drule CP')
      apply (fold inres_def)
      apply vcg
      done

    lemma hn_WITH_SPLIT_simplified:
      assumes MHN: "\<And>xs\<^sub>1 xsi\<^sub>1 xs\<^sub>2 xsi\<^sub>2. 
        hn_refine (raw_array_slice_assn xs\<^sub>1 xsi\<^sub>1 ** raw_array_slice_assn xs\<^sub>2 xsi\<^sub>2) 
                  (mi xsi\<^sub>1 xsi\<^sub>2) 
                  (\<box>) 
                  (R \<times>\<^sub>a raw_array_slice_assn \<times>\<^sub>a raw_array_slice_assn) 
                  (\<lambda>(ri,xsi\<^sub>1',xsi\<^sub>2'). xsi\<^sub>1'=xsi\<^sub>1 \<and> xsi\<^sub>2' = xsi\<^sub>2) 
                  (m xs\<^sub>1 xs\<^sub>2)"
      shows "hn_refine 
        (raw_array_slice_assn xs xsi ** snat_assn n ni) 
        (ars_with_split ni xsi mi) 
        (snat_assn n ni) 
        (\<lambda>(r,xs) (ri,xsi). R r ri ** raw_array_slice_assn xs xsi) 
        (\<lambda>(ri,xsi'). xsi'=xsi) 
        (WITH_SPLIT n xs m)"  
      using hn_WITH_SPLIT_aux[where 
        F=\<box> and F'=\<box> and
        CP'="\<lambda>xsi\<^sub>1 xsi\<^sub>2 (ri,xsi\<^sub>1',xsi\<^sub>2'). xsi\<^sub>1'=xsi\<^sub>1 \<and> xsi\<^sub>2' = xsi\<^sub>2" and
        CP="\<lambda>_. True"] MHN
      apply (simp add: sep_algebra_simps) 
      by blast
      
      
    lemma list_rel_take: "(xs,ys)\<in>\<langle>A\<rangle>list_rel \<Longrightarrow> (take n xs, take n ys) \<in> \<langle>A\<rangle>list_rel"  
      unfolding list_rel_def by auto
      
    lemma list_rel_drop: "(xs,ys)\<in>\<langle>A\<rangle>list_rel \<Longrightarrow> (drop n xs, drop n ys) \<in> \<langle>A\<rangle>list_rel"  
      unfolding list_rel_def by auto
      
    lemma list_rel_append: "(xs\<^sub>1,ys\<^sub>1)\<in> \<langle>A\<rangle>list_rel \<Longrightarrow> (xs\<^sub>2,ys\<^sub>2)\<in> \<langle>A\<rangle>list_rel \<Longrightarrow> (xs\<^sub>1@xs\<^sub>2,ys\<^sub>1@ys\<^sub>2)\<in> \<langle>A\<rangle>list_rel"  
      unfolding list_rel_def 
      using list_all2_appendI by blast
    
    (*  
    lemma hn_WITH_SPLIT_array_slice:
      assumes MHN: "\<And>xs\<^sub>1 xs\<^sub>2 xsi\<^sub>2. hn_refine 
        (hn_ctxt (array_slice_assn A) xs\<^sub>1 xsi ** hn_ctxt (array_slice_assn A) xs\<^sub>2 xsi\<^sub>2 ** F) 
        (mi xsi xsi\<^sub>2) (F') 
        (R \<times>\<^sub>a array_slice_assn A \<times>\<^sub>a array_slice_assn A) 
        (CP' xsi xsi\<^sub>2) 
        (m xs\<^sub>1 xs\<^sub>2)"
      assumes CP': "\<And>xsi\<^sub>2 ri xsi\<^sub>1' xsi\<^sub>2'. CP' xsi xsi\<^sub>2 (ri,xsi\<^sub>1',xsi\<^sub>2') \<Longrightarrow> xsi\<^sub>1'=xsi \<and> xsi\<^sub>2'=xsi\<^sub>2 \<and> CP ri"
      shows "hn_refine 
        (hn_ctxt (array_slice_assn A) xs xsi ** hn_ctxt snat_assn n ni ** F) 
        (ars_with_split ni xsi mi) 
        (hn_ctxt snat_assn n ni ** F') 
        (R \<times>\<^sub>a array_slice_assn A) 
        (\<lambda>(ri,xsi'). xsi'=xsi \<and> CP ri) 
        (WITH_SPLIT n xs m)"  
      apply (sepref_to_hoare)
      unfolding ars_with_split_def WITH_SPLIT_def array_slice_assn_def hr_comp_def
      
      supply [simp del] = List.take_all List.drop_all
      supply [simp] = pure_def refine_pw_simps list_rel_imp_same_length
      supply [elim] = list_rel_take list_rel_drop list_rel_append
      
      apply (clarsimp simp: )
      
      supply R = hn_refineD[OF MHN, unfolded hn_ctxt_def array_slice_assn_def hr_comp_def prod_assn_def]
      thm R
      supply [vcg_rules] = R
      
      apply vcg
      apply (drule CP')
      apply (fold inres_def)
      apply vcg
      done
    *)
      
    lemma hn_WITH_SPLIT_template_aux:
      assumes sl_assn_def: "sl_assn = hr_comp raw_array_slice_assn (\<langle>A\<rangle>list_rel)"
      assumes MHN: "\<And>xs\<^sub>1 xs\<^sub>2 xsi\<^sub>2. hn_refine 
        (hn_ctxt (sl_assn) xs\<^sub>1 xsi ** hn_ctxt (sl_assn) xs\<^sub>2 xsi\<^sub>2 ** hn_ctxt snat_assn n ni ** F) 
        (mi xsi xsi\<^sub>2) (F') 
        (R \<times>\<^sub>a sl_assn \<times>\<^sub>a sl_assn) 
        (CP' xsi xsi\<^sub>2) 
        (m xs\<^sub>1 xs\<^sub>2)"
      assumes CP': "\<And>xsi\<^sub>2 ri xsi\<^sub>1' xsi\<^sub>2'. CP' xsi xsi\<^sub>2 (ri,xsi\<^sub>1',xsi\<^sub>2') \<Longrightarrow> xsi\<^sub>1'=xsi \<and> xsi\<^sub>2'=xsi\<^sub>2 \<and> CP ri"
      shows "hn_refine 
        (hn_ctxt (sl_assn) xs xsi ** hn_ctxt snat_assn n ni ** F) 
        (ars_with_split ni xsi mi) 
        (hn_ctxt snat_assn n ni ** F') 
        (R \<times>\<^sub>a sl_assn) 
        (\<lambda>(ri,xsi'). xsi'=xsi \<and> CP ri) 
        (WITH_SPLIT n xs m)"  
      apply (sepref_to_hoare)
      unfolding ars_with_split_def WITH_SPLIT_def sl_assn_def hr_comp_def
      
      supply [simp del] = List.take_all List.drop_all
      supply [simp] = pure_def refine_pw_simps list_rel_imp_same_length
      supply [elim] = list_rel_take list_rel_drop list_rel_append
      
      apply (clarsimp simp: )
      
      supply R = hn_refineD[OF MHN, unfolded hn_ctxt_def sl_assn_def hr_comp_def prod_assn_def]
      thm R
      supply [vcg_rules] = R
      
      apply vcg
      apply (drule CP')
      apply (fold inres_def)
      apply vcg
      done
      
      
      
    lemma hn_WITH_SPLIT_template: 
      assumes sl_assn_def: "sl_assn = hr_comp raw_array_slice_assn (\<langle>A\<rangle>list_rel)"
      assumes FR: "\<Gamma> \<turnstile> hn_ctxt sl_assn xs xsi ** hn_ctxt snat_assn n ni ** \<Gamma>\<^sub>1"
      assumes HN: "\<And>xs\<^sub>1 xsi\<^sub>1 xs\<^sub>2 xsi\<^sub>2. \<lbrakk> CP_assm (xsi\<^sub>1 = xsi) \<rbrakk> \<Longrightarrow> hn_refine 
        (hn_ctxt sl_assn xs\<^sub>1 xsi\<^sub>1 ** hn_ctxt sl_assn xs\<^sub>2 xsi\<^sub>2 ** hn_ctxt snat_assn n ni ** \<Gamma>\<^sub>1) 
        (mi xsi\<^sub>1 xsi\<^sub>2) 
        (\<Gamma>\<^sub>2 xs\<^sub>1 xsi\<^sub>1 xs\<^sub>2 xsi\<^sub>2) (R) (CP xsi\<^sub>1 xsi\<^sub>2) (m xs\<^sub>1 xs\<^sub>2)"
      assumes CP: "\<And>xsi\<^sub>2 ri' xsi\<^sub>1' xsi\<^sub>2'. CP_assm (CP xsi xsi\<^sub>2 (ri',xsi\<^sub>1',xsi\<^sub>2')) \<Longrightarrow> CP_cond (xsi\<^sub>1' = xsi \<and> xsi\<^sub>2'=xsi\<^sub>2)"  
      assumes FR2: "\<And>xs\<^sub>1 xsi\<^sub>1 xs\<^sub>2 xsi\<^sub>2. \<Gamma>\<^sub>2 xs\<^sub>1 xsi\<^sub>1 xs\<^sub>2 xsi\<^sub>2 \<turnstile>
        hn_invalid sl_assn xs\<^sub>1 xsi\<^sub>1 ** hn_invalid sl_assn xs\<^sub>2 xsi\<^sub>2 ** \<Gamma>\<^sub>1'"
      assumes FR3: "\<And>x xi. hn_ctxt R x xi \<turnstile> hn_ctxt (R' \<times>\<^sub>a sl_assn \<times>\<^sub>a sl_assn) x xi"  
        
      (*  
      assumes FR3: "\<And>xs\<^sub>1' xsi\<^sub>1' xs\<^sub>2' xsi\<^sub>2' r' ri'. hn_ctxt R (r',xs\<^sub>1',xs\<^sub>2') (ri',xsi\<^sub>1',xsi\<^sub>2') \<turnstile>
        hn_ctxt R' r' ri' ** hn_ctxt (array_slice_assn A) xs\<^sub>1' xsi\<^sub>1' ** hn_ctxt (array_slice_assn A) xs\<^sub>2' xsi\<^sub>2'" *)
      assumes CP2: "\<And>xsi\<^sub>2. CP_simplify (CP_EX32 (CP xsi xsi\<^sub>2)) (CP')"  
      shows "hn_refine 
        (\<Gamma>) 
        (ars_with_split ni xsi mi) 
        (hn_invalid sl_assn xs xsi ** \<Gamma>\<^sub>1') 
        (R' \<times>\<^sub>a sl_assn) 
        (CP') 
        (WITH_SPLIT$n$xs$(\<lambda>\<^sub>2a b. m a b))"  
      unfolding autoref_tag_defs PROTECT2_def
      apply (rule hn_refine_cons_pre)
      applyS (rule FR)
      apply1 extract_hnr_invalids
      supply R = hn_WITH_SPLIT_template_aux[OF sl_assn_def,where CP="\<lambda>ri. \<exists>xsi\<^sub>2 xsi\<^sub>2'. CP xsi xsi\<^sub>2 (ri,xsi,xsi\<^sub>2')"]
      thm R
      apply (rule hn_refine_cons_cp[OF _ R])
      applyS (fri)
      apply1 extract_hnr_invalids
      apply (rule hn_refine_cons[OF _ HN])
      applyS (fri)
      applyS (simp add: CP_defs)
      applyS (sep_drule FR2; simp; rule entails_refl)
      focus
        apply clarsimp
        apply (sep_drule FR3[unfolded hn_ctxt_def])
        apply simp
        apply (rule entails_refl)
        solved
      focus
        using CP unfolding CP_defs apply blast solved
      applyS (simp add: hn_ctxt_def invalid_pure_recover)
      applyS (rule entails_refl)
      focus
        using CP2 unfolding CP_defs apply blast solved
      done  

      
    lemma hn_WITH_SPLIT_array_slice[sepref_comb_rules]: 
      assumes FR: "\<Gamma> \<turnstile> hn_ctxt (array_slice_assn A) xs xsi ** hn_ctxt snat_assn n ni ** \<Gamma>\<^sub>1"
      assumes HN: "\<And>xs\<^sub>1 xsi\<^sub>1 xs\<^sub>2 xsi\<^sub>2. \<lbrakk> CP_assm (xsi\<^sub>1 = xsi) \<rbrakk> \<Longrightarrow> hn_refine 
        (hn_ctxt (array_slice_assn A) xs\<^sub>1 xsi\<^sub>1 ** hn_ctxt (array_slice_assn A) xs\<^sub>2 xsi\<^sub>2 ** hn_ctxt snat_assn n ni ** \<Gamma>\<^sub>1) 
        (mi xsi\<^sub>1 xsi\<^sub>2) 
        (\<Gamma>\<^sub>2 xs\<^sub>1 xsi\<^sub>1 xs\<^sub>2 xsi\<^sub>2) (R) (CP xsi\<^sub>1 xsi\<^sub>2) (m xs\<^sub>1 xs\<^sub>2)"
      assumes CP: "\<And>xsi\<^sub>2 ri' xsi\<^sub>1' xsi\<^sub>2'. CP_assm (CP xsi xsi\<^sub>2 (ri',xsi\<^sub>1',xsi\<^sub>2')) \<Longrightarrow> CP_cond (xsi\<^sub>1' = xsi \<and> xsi\<^sub>2'=xsi\<^sub>2)"  
      assumes FR2: "\<And>xs\<^sub>1 xsi\<^sub>1 xs\<^sub>2 xsi\<^sub>2. \<Gamma>\<^sub>2 xs\<^sub>1 xsi\<^sub>1 xs\<^sub>2 xsi\<^sub>2 \<turnstile>
        hn_invalid (array_slice_assn A) xs\<^sub>1 xsi\<^sub>1 ** hn_invalid (array_slice_assn A) xs\<^sub>2 xsi\<^sub>2 ** \<Gamma>\<^sub>1'"
      assumes FR3: "\<And>x xi. hn_ctxt R x xi \<turnstile> hn_ctxt (R' \<times>\<^sub>a array_slice_assn A \<times>\<^sub>a array_slice_assn A) x xi"  
        
      (*  
      assumes FR3: "\<And>xs\<^sub>1' xsi\<^sub>1' xs\<^sub>2' xsi\<^sub>2' r' ri'. hn_ctxt R (r',xs\<^sub>1',xs\<^sub>2') (ri',xsi\<^sub>1',xsi\<^sub>2') \<turnstile>
        hn_ctxt R' r' ri' ** hn_ctxt (array_slice_assn A) xs\<^sub>1' xsi\<^sub>1' ** hn_ctxt (array_slice_assn A) xs\<^sub>2' xsi\<^sub>2'" *)
      assumes CP2: "\<And>xsi\<^sub>2. CP_simplify (CP_EX32 (CP xsi xsi\<^sub>2)) (CP')"  
      shows "hn_refine 
        (\<Gamma>) 
        (ars_with_split ni xsi mi) 
        (hn_invalid (array_slice_assn A) xs xsi ** \<Gamma>\<^sub>1') 
        (R' \<times>\<^sub>a array_slice_assn A) 
        (CP') 
        (WITH_SPLIT$n$xs$(\<lambda>\<^sub>2a b. m a b))"  
        
      apply (rule hn_WITH_SPLIT_template[of "array_slice_assn A", OF _ assms]; assumption?)
      unfolding array_slice_assn_def ..
            
  end  
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


lemma larray_assn_comp: "hr_comp (larray_assn id_assn) (\<langle>the_pure A\<rangle>list_rel) = larray_assn A"
  unfolding larray_assn_def by simp
    
definition [simp]: "larray_replicate_init i n \<equiv> replicate n i"
interpretation larray: replicate_init larray_replicate_init by unfold_locales simp
  

context 
  notes [fcomp_norm_unfold] = raw_larray_assn_def[symmetric] larray_assn_def[symmetric] larray_assn_comp
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

sepref_definition larray_swap is "uncurry2 (mop_list_swap)" 
  :: "(larray_assn' TYPE('l::len2) id_assn)\<^sup>d *\<^sub>a (snat_assn)\<^sup>k *\<^sub>a (snat_assn)\<^sup>k \<rightarrow>\<^sub>a larray_assn' TYPE('l::len2) id_assn"
  unfolding gen_mop_list_swap by sepref
  
sepref_decl_impl (ismop) larray_swap.refine .




definition "la_free1 nxs \<equiv> case nxs of (_,xs) \<Rightarrow> op_list_free xs"
lemma la_free1_refine: "(la_free1,op_list_free) \<in> larray1_rel \<rightarrow> unit_rel" by auto

sepref_definition la_free_impl [llvm_inline] is "RETURN o la_free1" :: "(larray_impl_assn' TYPE(_))\<^sup>d \<rightarrow>\<^sub>a unit_assn"
  unfolding la_free1_def
  by sepref

sepref_decl_impl larray_free: la_free_impl.refine[FCOMP la_free1_refine] .
lemmas larray_mk_free[sepref_frame_free_rules] = hn_MK_FREEI[OF larray_free_hnr]
  
end
  

lemma larray_boundD[sepref_bounds_dest]: 
  "rdomp (larray_assn' TYPE('a::len2) A) xs \<Longrightarrow> length xs < max_snat LENGTH('a)"
  unfolding larray_assn_def raw_larray_assn_def larray1_rel_def
  apply (auto simp: rdomp_hrcomp_conv in_br_conv snat_rel_def snat.rel_def)
  by (simp add: list_rel_pres_length)




subsection \<open>Ad-Hoc Regression Tests\<close>
  
sepref_definition example1 [llvm_code] is "\<lambda>n. RETURN (replicate (n+1) (snat_init TYPE(32)))" 
  :: "[\<lambda>n. n\<in>{1..<150}]\<^sub>a (snat_assn' TYPE(32))\<^sup>k \<rightarrow> array_assn (snat_assn' TYPE(32))"
  apply (annot_snat_const "TYPE(32)")
  apply (rewrite array.fold_replicate_init)
  apply sepref
  done
  
sepref_definition example2 [llvm_code] is \<open>\<lambda>n. do {
  ASSERT (n>10);
  let a = replicate n (snat_const TYPE(64) 42);
  let a = a[snat_const TYPE(32) 3:=0];
  ASSERT (a!1=42 \<and> a!2=42);
  RETURN (a!snat_const TYPE(32) 1 + a!snat_const TYPE(32) 2)
}\<close> :: "(snat_assn' TYPE(32))\<^sup>k \<rightarrow>\<^sub>a snat_assn' TYPE(64)"
  apply (annot_snat_const "TYPE(64)")
  apply (rewrite array_fold_custom_replicate)
  apply sepref
  done
  
  
sepref_definition example1n [llvm_code] is "\<lambda>n. RETURN (replicate (n+1) (snat_init TYPE(8)))" 
  :: "[\<lambda>n. n\<in>{1..<150}]\<^sub>a (snat_assn' TYPE(32))\<^sup>k \<rightarrow> larray_assn' TYPE(32) (snat_assn' TYPE(8))"
  apply (rewrite larray.fold_replicate_init)
  apply (annot_snat_const "TYPE(32)")
  apply sepref
  done
  
  
sepref_definition example2n [llvm_code] is \<open>\<lambda>n. do {
  ASSERT (n>10);
  let a = replicate n (snat_const TYPE(64) 42);
  let a = a[snat_const TYPE(32) 3:=0];
  ASSERT (a!1=42 \<and> a!2=42);
  RETURN (a!snat_const TYPE(32) 1 + a!snat_const TYPE(32) 2)
}\<close> :: "(snat_assn' TYPE(32))\<^sup>k \<rightarrow>\<^sub>a snat_assn' TYPE(64)"
  apply (annot_snat_const "TYPE(64)")
  apply (rewrite larray_fold_custom_replicate)
  apply sepref
  done

  
  
sepref_definition example3 [llvm_code] is \<open>uncurry (\<lambda>xs n. RECT (\<lambda>D (xs,n). doN {
  ASSERT (n = length xs);
  if n<10 then RETURN xs
  else doN {
    (_,xs) \<leftarrow> WITH_SPLIT 5 xs (\<lambda>xs\<^sub>1 xs\<^sub>2. doN {
      xs\<^sub>1 \<leftarrow> mop_list_set xs\<^sub>1 0 3;
      xs\<^sub>2 \<leftarrow> D (xs\<^sub>2, (n-5));
      RETURN (True,xs\<^sub>1,xs\<^sub>2)
    });
    RETURN xs
  }
}) (xs,n))\<close> :: "[\<lambda>_. True]\<^sub>c (array_slice_assn (snat_assn' TYPE(64)))\<^sup>d *\<^sub>a (snat_assn' TYPE(64))\<^sup>k \<rightarrow> array_slice_assn (snat_assn' TYPE(64)) [\<lambda>(xs,n) r. r=xs]\<^sub>c"
  apply (annot_snat_const "TYPE(64)")
  apply (subst RECT_cp_annot[where CP="\<lambda>(xs,n) r. r=xs"])
  apply sepref
  done
  
  
  
export_llvm example1 example2 example1n example2n example3
    

  
end
