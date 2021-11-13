theory Proto_IICF_EOArray
imports IICF_Array "../../../ds/Proto_EOArray" "../../../sepref/Proto_Sepref_Borrow" "../Intf/IICF_List"
begin

(* TODO: Move. Generalization of hr_comp *)
definition "assn_comp A B a c \<equiv> EXS b. A a b ** B b c"

lemma assn_comp_def_rev: "assn_comp A B a c \<equiv> EXS b. B b c ** A a b"
  unfolding assn_comp_def by (auto simp add: sep_algebra_simps fun_eq_iff sep_conj_c)


lemma assn_comp_id[simp]: 
  "assn_comp id_assn B = B"
  "assn_comp A id_assn = A"
  unfolding assn_comp_def 
  by (auto simp: fun_eq_iff sep_algebra_simps pure_def)

lemma assn_comp_assoc[simp]: "assn_comp (assn_comp A B) C = assn_comp A (assn_comp B C)"  
  unfolding assn_comp_def 
  by (auto simp: fun_eq_iff sep_algebra_simps)
  
lemma hr_comp_to_assn_comp: "hr_comp A B = assn_comp (pure B) A"
  unfolding assn_comp_def hr_comp_def pure_def 
  by (auto simp: fun_eq_iff sep_algebra_simps)
  
lemma assn_comp_summarize_pure: 
  "assn_comp (pure A) (pure B) = pure (B O A)"  
  "assn_comp (pure A) (assn_comp (pure B) C) = assn_comp (pure (B O A)) C"
  unfolding assn_comp_def pure_def 
  by (auto simp: fun_eq_iff sep_algebra_simps)


context begin
  interpretation llvm_prim_mem_setup .  
  
  lemma list_assn_take_drop: "\<upharpoonleft>(list_assn A) xs xs' 
    \<turnstile> \<upharpoonleft>(list_assn A) (take n xs) (take n xs') ** \<upharpoonleft>(list_assn A) (drop n xs) (drop n xs')"
    apply (cases "n>length xs")
    subgoal
      by (metis append_take_drop_id entails_eq_iff entails_pureI length_take list_assn_append list_assn_pure_part)
    apply (cases "length xs \<noteq> length xs'")  
    subgoal by simp
    apply (subst list_assn_append[symmetric])
    apply simp_all
    done
  
  lemma list_assn_take_drop_red: "is_sep_red (\<upharpoonleft>(list_assn A) (drop n xs) (drop n xs')) \<box> (\<upharpoonleft>(list_assn A) xs xs') (\<upharpoonleft>(list_assn A) (take n xs) (take n xs'))"
    apply (rule is_sep_redI)
    apply (sep_drule list_assn_take_drop[of A xs xs' n])
    by (simp add: conj_entails_mono)
    
  lemma list_assn_append_red: "is_sep_red \<box> (\<upharpoonleft>(list_assn A) ys ys') (\<upharpoonleft>(list_assn A) xs xs') (\<upharpoonleft>(list_assn A) (xs@ys) (xs'@ys'))"  
    apply (rule is_sep_redI)
    apply (cases "length xs = length xs'"; simp)
    apply (cases "length ys = length ys'"; simp?)
    subgoal using conj_entails_mono by blast
    subgoal by (metis entails_def mod_starD)
    done
    
    
    
  lemma hn_WITH_SPLIT_assn_comp_template_aux:
    assumes sl_assn_def: "sl_assn = assn_comp (\<upharpoonleft>(list_assn A)) (raw_array_slice_assn)"
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
    unfolding ars_with_split_def WITH_SPLIT_def sl_assn_def assn_comp_def_rev
    
    supply [simp del] = List.take_all List.drop_all
    supply [simp] = pure_def refine_pw_simps list_rel_imp_same_length
    supply [elim] = list_rel_take list_rel_drop list_rel_append
    
    apply (clarsimp simp: )
    
    supply R = hn_refineD[OF MHN, unfolded hn_ctxt_def sl_assn_def assn_comp_def_rev prod_assn_def]
    thm R
    supply [vcg_rules] = R
    
    supply [fri_red_rules] = list_assn_take_drop_red list_assn_append_red
    supply [named_ss fri_prepare_simps] = prod_assn_pair_conv
    
    apply vcg
    apply (drule CP')
    apply (fold inres_def)
    apply vcg
    done

    lemma hn_WITH_SPLIT_assn_comp_template: 
      assumes sl_assn_def: "sl_assn = assn_comp (\<upharpoonleft>(list_assn A)) (raw_array_slice_assn)"
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
      supply R = hn_WITH_SPLIT_assn_comp_template_aux[OF sl_assn_def,where CP="\<lambda>ri. \<exists>xsi\<^sub>2 xsi\<^sub>2'. CP xsi xsi\<^sub>2 (ri,xsi,xsi\<^sub>2')"]
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
    
    
    
    
end



  
  
  
  


hide_const (open) LLVM_DS_Array.array_assn LLVM_DS_NArray.array_slice_assn

definition "eoarray_assn A \<equiv> \<upharpoonleft>(nao_assn (mk_assn A))"



sepref_decl_op eo_extract: 
  "\<lambda>xs i. (the (xs!i), xs[i:=None])" 
  :: "[\<lambda>(xs::'a option list,i). i<length xs \<and> xs!i\<noteq>None]\<^sub>f 
  \<langle>\<langle>Id\<rangle>option_rel\<rangle>list_rel\<times>\<^sub>rnat_rel \<rightarrow> \<langle>(Id::'a rel) \<times>\<^sub>r \<langle>\<langle>Id::'a rel\<rangle>option_rel\<rangle>list_rel\<rangle>nres_rel"
  by auto

sepref_decl_op eo_set: 
  "\<lambda>xs i (x::'a). xs[i:=Some x]" 
  :: "[\<lambda>((xs::'a option list,i),x::'a). i<length xs \<and> xs!i=None]\<^sub>f 
  (\<langle>\<langle>Id\<rangle>option_rel\<rangle>list_rel\<times>\<^sub>rnat_rel)\<times>\<^sub>rId \<rightarrow> \<langle>\<langle>\<langle>Id::'a rel\<rangle>option_rel\<rangle>list_rel\<rangle>nres_rel"
  by auto


    
context
  notes [fcomp_norm_simps] = option_rel_id_simp list_rel_id prod_rel_id_simp hrr_comp_id_conv
begin  
  

  lemma eo_set_hnr_aux: "(uncurry2 array_upd,uncurry2 (RETURN ooo op_eo_set)) 
    \<in> [\<lambda>((xs,i),_). i<length xs \<and> xs!i=None]\<^sub>a [\<lambda>_. True]\<^sub>c (eoarray_assn A)\<^sup>d *\<^sub>a snat_assn\<^sup>k *\<^sub>a A\<^sup>d 
      \<rightarrow>\<^sub>d (\<lambda>_. eoarray_assn A) [\<lambda>((xsi,_),_) ri. ri=xsi]\<^sub>c"
    unfolding snat_rel_def snat.assn_is_rel[symmetric] 
    apply sepref_to_hoare
    apply (clarsimp simp: invalid_assn_def eoarray_assn_def)
    apply (rule htriple_pure_preI, ((determ \<open>drule pure_part_split_conj|erule conjE\<close>)+)?)
    apply vcg
    done

  lemma eo_set_hnr_aux_nondep: "(uncurry2 array_upd,uncurry2 (RETURN ooo op_eo_set)) 
    \<in> [\<lambda>((xs,i),_). i<length xs \<and> xs!i=None]\<^sub>a (eoarray_assn A)\<^sup>d *\<^sub>a snat_assn\<^sup>k *\<^sub>a A\<^sup>d \<rightarrow> eoarray_assn A"
    unfolding snat_rel_def snat.assn_is_rel[symmetric] 
    apply sepref_to_hoare
    apply (clarsimp simp: invalid_assn_def eoarray_assn_def)
    apply (rule htriple_pure_preI, ((determ \<open>drule pure_part_split_conj|erule conjE\<close>)+)?)
    apply vcg
    done

(*  lemma eo_set_hnr_aux: "(uncurry2 array_upd,uncurry2 (RETURN ooo op_eo_set)) 
    \<in> [\<lambda>((xs,i),_). i<length xs \<and> xs!i=None]\<^sub>a (eoarray_assn A)\<^sup>d *\<^sub>a snat_assn\<^sup>k *\<^sub>a A\<^sup>d \<rightarrow> eoarray_assn A"
    unfolding snat_rel_def snat.assn_is_rel[symmetric] 
    apply sepref_to_hoare
    apply (clarsimp simp: invalid_assn_def eoarray_assn_def)
    apply (rule htriple_pure_preI, ((determ \<open>drule pure_part_split_conj|erule conjE\<close>)+)?)
    apply vcg
    done
*)
    
  sepref_decl_impl eo_set_dep: eo_set_hnr_aux by simp  
  sepref_decl_impl (no_register) eo_set_nondep: eo_set_hnr_aux_nondep by simp  
    
  definition [llvm_inline]: "eo_extract_impl p i \<equiv> doM { r \<leftarrow> array_nth p i; return (r,p) }"

  
  lemma eo_extract_hnr_aux: "(uncurry eo_extract_impl,uncurry (RETURN oo op_eo_extract)) 
    \<in> [\<lambda>(xs,i). i<length xs \<and> xs!i\<noteq>None]\<^sub>a [\<lambda>_. True]\<^sub>c (eoarray_assn A)\<^sup>d *\<^sub>a snat_assn\<^sup>k 
      \<rightarrow>\<^sub>d (\<lambda>_. A\<times>\<^sub>aeoarray_assn A) [\<lambda>(ai,_) (_,x). x=ai]\<^sub>c"  
    unfolding snat_rel_def snat.assn_is_rel[symmetric]
    apply sepref_to_hoare
    apply (clarsimp simp: invalid_assn_def eoarray_assn_def)
    apply (rule htriple_pure_preI, ((determ \<open>drule pure_part_split_conj|erule conjE\<close>)+)?)
    unfolding eo_extract_impl_def
    apply vcg'
    done
    
  
  lemma eo_extract_hnr_aux_nondep: "(uncurry eo_extract_impl,uncurry (RETURN oo op_eo_extract)) 
    \<in> [\<lambda>(xs,i). i<length xs \<and> xs!i\<noteq>None]\<^sub>a (eoarray_assn A)\<^sup>d *\<^sub>a snat_assn\<^sup>k \<rightarrow> A\<times>\<^sub>aeoarray_assn A"  
    unfolding snat_rel_def snat.assn_is_rel[symmetric]
    apply sepref_to_hoare
    apply (clarsimp simp: invalid_assn_def eoarray_assn_def)
    apply (rule htriple_pure_preI, ((determ \<open>drule pure_part_split_conj|erule conjE\<close>)+)?)
    unfolding eo_extract_impl_def
    apply vcg'
    done
    
    
  sepref_decl_impl eo_extract_dep: eo_extract_hnr_aux by simp
  print_theorems
  sepref_decl_impl (no_register) eo_extract_nondep: eo_extract_hnr_aux_nondep by simp
  print_theorems
  
  (*thm eo_extract_dep_hnr_mop[to_hnr]
  thm eo_extract_dep_hnr_mop[to_hnr, to_hfref]
  *)
  
  
end  

  

definition "some_rel \<equiv> br the (Not o is_None)"

lemma some_rel_simps[simp]: 
  "(None,x)\<notin>some_rel"
  "(Some x,y)\<in>some_rel \<longleftrightarrow> x=y"
  unfolding some_rel_def 
  by (auto simp: in_br_conv)

lemma some_rel_conv: "(x,y)\<in>some_rel \<longleftrightarrow> x=Some y"  
  unfolding some_rel_def 
  by (auto simp: in_br_conv)

lemma some_list_rel_conv: "(xs,ys)\<in>\<langle>some_rel\<rangle>list_rel \<longleftrightarrow> xs = map Some ys"  
  apply (cases "length xs = length ys") 
  subgoal by (induction rule: list_induct2) (auto simp: some_rel_conv)
  subgoal using length_map list_rel_pres_length by blast
  done

  
lemma None_not_in_set_conv: assumes "None\<notin>set xs" obtains ys where "xs = map Some ys"
  using assms
  by (metis (full_types) ex_map_conv option.exhaust)
      

definition "woarray_assn A \<equiv> hr_comp (eoarray_assn A) (\<langle>some_rel\<rangle>list_rel)"

lemma woarray_assn_conv: "woarray_assn A xs ys = eoarray_assn A (map Some xs) ys"
  unfolding woarray_assn_def hr_comp_def
  by (auto simp: some_list_rel_conv sep_algebra_simps)


(* TODO: Move *)
lemma mk_assn_eq_conv[simp]: "mk_assn A = mk_assn B \<longleftrightarrow> A=B"
  by (metis dr_assn_inverses(2) mk_assn_def)

 
    
definition [to_relAPP]: "oelem_rel A \<equiv> {(a, Some b) | a b. (a,b)\<in>A} \<union> {(x,None) | x. True}"  

lemma pure_oelem_assn_conv:
  assumes "is_pure A"
  shows "oelem_assn (mk_assn A) = mk_assn (pure (\<langle>the_pure A\<rangle>oelem_rel))"
  apply (subst pure_the_pure[of A, symmetric], fact)
  apply (auto simp: pure_def oelem_assn_def oelem_rel_def fun_eq_iff sep_algebra_simps split: option.splits)  
  done

lemma pure_list_assn_to_rel_conv:
  assumes "is_pure A" 
  shows "\<upharpoonleft>(list_assn (mk_assn A)) = (\<lambda>x y. \<up>((y,x)\<in>\<langle>(the_pure A)\<rangle>list_rel ))"  
  apply (subst pure_the_pure[of A, symmetric], fact)

  apply (intro ext)
  subgoal for xs ys s
    apply (cases "length xs = length ys")
    subgoal
      apply rotate_tac
      apply (induction xs ys arbitrary: s rule: list_induct2)
      apply (auto simp: sep_algebra_simps pred_lift_extract_simps pure_def)
      done
    subgoal
      by (auto simp: sep_algebra_simps pred_lift_extract_simps list_rel_imp_same_length)  
    done
  done
  
lemma oelem_some_rel_conv: "\<langle>A\<rangle>oelem_rel O some_rel = A"
  unfolding oelem_rel_def some_rel_def  
  by (fastforce simp: in_br_conv)
  
lemma pure_woarray_assn_conv: "is_pure A \<Longrightarrow> woarray_assn A = array_assn A"
  unfolding woarray_assn_def eoarray_assn_def array_assn_def nao_assn_def
  unfolding hr_comp_def 
  apply simp
  apply (clarsimp simp: fun_eq_iff pure_oelem_assn_conv pure_list_assn_to_rel_conv sep_algebra_simps pred_lift_extract_simps)
  by (smt list_rel_compp oelem_some_rel_conv relcomp.simps)
    
definition [simp]: "mop_array_to_woarray xs \<equiv> RETURN (xs::_ list)"  
definition [simp]: "mop_woarray_to_array xs \<equiv> RETURN (xs::_ list)"  
sepref_register mop_array_to_woarray mop_woarray_to_array

lemma mop_array_to_woarray_impl[sepref_fr_rules]: "CONSTRAINT is_pure A \<Longrightarrow> (return,mop_array_to_woarray) \<in> (array_assn A)\<^sup>d \<rightarrow>\<^sub>a woarray_assn A"
  unfolding mop_array_to_woarray_def pure_woarray_assn_conv CONSTRAINT_def
  apply sepref_to_hoare
  apply vcg
  done
  
lemma mop_woarray_to_array_impl[sepref_fr_rules]: "CONSTRAINT is_pure A 
  \<Longrightarrow> (return,mop_woarray_to_array) \<in> (woarray_assn A)\<^sup>d \<rightarrow>\<^sub>a array_assn A"
  unfolding mop_array_to_woarray_def pure_woarray_assn_conv CONSTRAINT_def
  apply sepref_to_hoare
  apply vcg
  done

  
    
definition [simp]: "mop_to_wo_conv xs \<equiv> doN{ ASSERT (None\<notin>set xs); RETURN (map the xs) }"
sepref_register mop_to_wo_conv 

lemma mop_to_wo_conv_hnr_dep[sepref_fr_rules]: "(return,mop_to_wo_conv) \<in> 
  [\<lambda>_. True]\<^sub>c (eoarray_assn A)\<^sup>d \<rightarrow> (woarray_assn A) [\<lambda>x r. r=x]\<^sub>c"
  unfolding mop_to_wo_conv_def
  apply sepref_to_hoare
  apply (auto simp: refine_pw_simps sep_algebra_simps woarray_assn_conv simp del: pred_lift_extract_simps elim!: None_not_in_set_conv)
  apply vcg
  done
  
lemma mop_to_wo_conv_hnr_nondep: "(return,mop_to_wo_conv)\<in>(eoarray_assn A)\<^sup>d \<rightarrow>\<^sub>a woarray_assn A"
  unfolding mop_to_wo_conv_def
  apply sepref_to_hoare
  apply (auto simp: refine_pw_simps sep_algebra_simps woarray_assn_conv simp del: pred_lift_extract_simps elim!: None_not_in_set_conv)
  by vcg
  
definition [simp]: "mop_to_eo_conv xs \<equiv> RETURN (map Some xs)"

lemma mop_to_eo_conv_hnr_dep[sepref_fr_rules]: "(return,mop_to_eo_conv)\<in> [\<lambda>_. True]\<^sub>c (woarray_assn A)\<^sup>d \<rightarrow> (eoarray_assn A) [\<lambda>x r. r=x]\<^sub>c"
  apply sepref_to_hoare
  apply (auto simp: sep_algebra_simps woarray_assn_conv)
  by vcg

lemma mop_to_eo_conv_hnr_nondep: "(return,mop_to_eo_conv)\<in>(woarray_assn A)\<^sup>d \<rightarrow>\<^sub>a eoarray_assn A"
  apply sepref_to_hoare
  apply (auto simp: sep_algebra_simps woarray_assn_conv)
  by vcg

lemmas eo_hnr_dep = eo_extract_dep_hnr eo_extract_dep_hnr_mop eo_set_dep_hnr eo_set_dep_hnr_mop 
  mop_to_wo_conv_hnr_dep mop_to_eo_conv_hnr_dep
lemmas eo_hnr_nondep = eo_extract_nondep_hnr eo_extract_nondep_hnr_mop eo_set_nondep_hnr eo_set_nondep_hnr_mop
  mop_to_wo_conv_hnr_nondep mop_to_eo_conv_hnr_nondep

lemma wo_array_get_hnrs[sepref_fr_rules]:   
  "CONSTRAINT Sepref_Basic.is_pure A \<Longrightarrow> (uncurry array_nth, uncurry (RETURN \<circ>\<circ> op_list_get)) \<in> [pre_list_get]\<^sub>a (woarray_assn A)\<^sup>k *\<^sub>a snat_assn\<^sup>k \<rightarrow> A"
  "CONSTRAINT Sepref_Basic.is_pure A \<Longrightarrow> (uncurry array_nth, uncurry mop_list_get) \<in> (woarray_assn A)\<^sup>k *\<^sub>a snat_assn\<^sup>k \<rightarrow>\<^sub>a A"
  using array_get_hnr[of A] array_get_hnr_mop[of A]    
  by (simp_all add: pure_woarray_assn_conv)      
      
lemma wo_array_set_hnrs[sepref_fr_rules]:
  "CONSTRAINT Sepref_Basic.is_pure A \<Longrightarrow>
    (uncurry2 array_upd, uncurry2 (RETURN ooo op_list_set)) \<in> 
      [pre_list_set]\<^sub>a [\<lambda>_. True]\<^sub>c (woarray_assn A)\<^sup>d *\<^sub>a snat_assn\<^sup>k *\<^sub>a A\<^sup>k \<rightarrow>\<^sub>d (\<lambda>_. woarray_assn A) [\<lambda>((ai,_),_) r. r=ai]\<^sub>c"
  "CONSTRAINT Sepref_Basic.is_pure A \<Longrightarrow> (uncurry2 array_upd, uncurry2 mop_list_set) \<in> [\<lambda>_. True]\<^sub>c (woarray_assn A)\<^sup>d *\<^sub>a snat_assn\<^sup>k *\<^sub>a A\<^sup>k \<rightarrow> woarray_assn A [\<lambda>((ai,_),_) r. r=ai]\<^sub>c"
  using array_set_hnr[of A] array_set_hnr_mop[of A]
  by (simp_all add: pure_woarray_assn_conv)
  
definition [simp]: "MOVE \<equiv> RETURN"  
sepref_register MOVE
  
lemma MOVE_rl[sepref_fr_rules]: "(return, MOVE)\<in>[\<lambda>_. True]\<^sub>c A\<^sup>d \<rightarrow> A [\<lambda>xi r. r=xi]\<^sub>c"
  unfolding MOVE_def 
  apply sepref_to_hoare
  by vcg

  
  
definition "swap_eo xs i j \<equiv> doN {
  ASSERT (i\<noteq>j);
  xs \<leftarrow> mop_to_eo_conv xs;
  (vi,xs) \<leftarrow> mop_eo_extract xs i;
  (vj,xs) \<leftarrow> mop_eo_extract xs j;
  xs \<leftarrow> mop_eo_set xs i vj;
  xs \<leftarrow> mop_eo_set xs j vi;
  xs \<leftarrow> mop_to_wo_conv xs;
  xs \<leftarrow> MOVE xs;
  RETURN xs
}"  
    
lemma swap_eo_refine: "(uncurry2 swap_eo,uncurry2 mop_list_swap) \<in> [\<lambda>((xs,i),j). i\<noteq>j]\<^sub>f (Id\<times>\<^sub>rId)\<times>\<^sub>rId \<rightarrow> \<langle>Id\<rangle>nres_rel"  
  apply (rule frefI; clarsimp simp: swap_eo_def swap_def pw_nres_rel_iff refine_pw_simps map_update)
  apply (safe; clarsimp?)
  apply (metis None_notin_image_Some list.set_map list_update_overwrite list_update_swap map_update)
  apply (metis None_notin_image_Some list.set_map list_update_overwrite list_update_swap map_update)
  apply (metis list_update_overwrite list_update_swap)
  done

  
(*  
definition "forget_cncs x \<equiv> RETURN ()"  

lemma forget_cncs_rule[sepref_comb_rules]:
  assumes FRAME: "\<Gamma> \<turnstile> hn_ctxt R src srci ** hn_invalid R dst dsti ** F"
  assumes [simp]: "vassn_tag \<Gamma> \<Longrightarrow> srci = dsti"
  shows "hn_refine \<Gamma> (return ()) (hn_invalid R src srci ** hn_ctxt R dst dsti ** F) unit_assn (unborrow$src$dst)"
  apply (rule hn_refine_vassn_tagI)
  apply (rule hn_refine_cons_pre[OF FRAME])
  apply (rule hn_refineI)
  unfolding unborrow_def
  apply (simp add: refine_pw_simps)
  unfolding hn_ctxt_def invalid_assn_def pure_def
  by vcg'
*)


context 
  fixes A :: "'a \<Rightarrow> 'b::llvm_rep \<Rightarrow> assn"
  notes [fcomp_norm_simps] = list_rel_id
begin
  sepref_definition swap_eo_impl [llvm_code] is "uncurry2 swap_eo" 
    :: "[\<lambda>_. True]\<^sub>c (woarray_assn A)\<^sup>d *\<^sub>a snat_assn\<^sup>k *\<^sub>a snat_assn\<^sup>k \<rightarrow> woarray_assn A [\<lambda>((ai,_),_) r. r=ai]\<^sub>c"
    unfolding swap_eo_def
    by sepref
  
  sepref_decl_impl (ismop) swap_eo_impl.refine[FCOMP swap_eo_refine] uses mop_list_swap.fref[where A=Id] .
end  
  
export_llvm "swap_eo_impl :: 8 word ptr \<Rightarrow> 64 word \<Rightarrow> 64 word \<Rightarrow> 8 word ptr llM"

  


subsection \<open>Array-Slice\<close>

definition "eoarray_slice_assn A \<equiv> \<upharpoonleft>(sao_assn (mk_assn A))"

    
context
  notes [fcomp_norm_simps] = option_rel_id_simp list_rel_id prod_rel_id_simp hrr_comp_id_conv
begin  
  

  lemma eos_set_hnr_aux: "(uncurry2 array_upd,uncurry2 (RETURN ooo op_eo_set)) 
    \<in> [\<lambda>((xs,i),_). i<length xs \<and> xs!i=None]\<^sub>a [\<lambda>_. True]\<^sub>c (eoarray_slice_assn A)\<^sup>d *\<^sub>a snat_assn\<^sup>k *\<^sub>a A\<^sup>d 
      \<rightarrow>\<^sub>d (\<lambda>_. eoarray_slice_assn A) [\<lambda>((xsi,_),_) ri. ri=xsi]\<^sub>c"
    unfolding snat_rel_def snat.assn_is_rel[symmetric] 
    apply sepref_to_hoare
    apply (clarsimp simp: invalid_assn_def eoarray_slice_assn_def)
    apply (rule htriple_pure_preI, ((determ \<open>drule pure_part_split_conj|erule conjE\<close>)+)?)
    apply vcg
    done

  lemma eos_set_hnr_aux_nondep: "(uncurry2 array_upd,uncurry2 (RETURN ooo op_eo_set)) 
    \<in> [\<lambda>((xs,i),_). i<length xs \<and> xs!i=None]\<^sub>a (eoarray_slice_assn A)\<^sup>d *\<^sub>a snat_assn\<^sup>k *\<^sub>a A\<^sup>d \<rightarrow> eoarray_slice_assn A"
    unfolding snat_rel_def snat.assn_is_rel[symmetric] 
    apply sepref_to_hoare
    apply (clarsimp simp: invalid_assn_def eoarray_slice_assn_def)
    apply (rule htriple_pure_preI, ((determ \<open>drule pure_part_split_conj|erule conjE\<close>)+)?)
    apply vcg
    done
    
  sepref_decl_impl eos_set_dep: eos_set_hnr_aux by simp  
  sepref_decl_impl (no_register) eos_set_nondep: eos_set_hnr_aux_nondep by simp  
    
  
  lemma eos_extract_hnr_aux: "(uncurry eo_extract_impl,uncurry (RETURN oo op_eo_extract)) 
    \<in> [\<lambda>(xs,i). i<length xs \<and> xs!i\<noteq>None]\<^sub>a [\<lambda>_. True]\<^sub>c (eoarray_slice_assn A)\<^sup>d *\<^sub>a snat_assn\<^sup>k 
      \<rightarrow>\<^sub>d (\<lambda>_. A\<times>\<^sub>aeoarray_slice_assn A) [\<lambda>(ai,_) (_,x). x=ai]\<^sub>c"  
    unfolding snat_rel_def snat.assn_is_rel[symmetric]
    apply sepref_to_hoare
    apply (clarsimp simp: invalid_assn_def eoarray_slice_assn_def)
    apply (rule htriple_pure_preI, ((determ \<open>drule pure_part_split_conj|erule conjE\<close>)+)?)
    unfolding eo_extract_impl_def
    apply vcg'
    done
    
  
  lemma eos_extract_hnr_aux_nondep: "(uncurry eo_extract_impl,uncurry (RETURN oo op_eo_extract)) 
    \<in> [\<lambda>(xs,i). i<length xs \<and> xs!i\<noteq>None]\<^sub>a (eoarray_slice_assn A)\<^sup>d *\<^sub>a snat_assn\<^sup>k \<rightarrow> A\<times>\<^sub>aeoarray_slice_assn A"  
    unfolding snat_rel_def snat.assn_is_rel[symmetric]
    apply sepref_to_hoare
    apply (clarsimp simp: invalid_assn_def eoarray_slice_assn_def)
    apply (rule htriple_pure_preI, ((determ \<open>drule pure_part_split_conj|erule conjE\<close>)+)?)
    unfolding eo_extract_impl_def
    apply vcg'
    done
    
    
  sepref_decl_impl eos_extract_dep: eos_extract_hnr_aux by simp
  print_theorems
  sepref_decl_impl (no_register) eos_extract_nondep: eos_extract_hnr_aux_nondep by simp
  print_theorems
  
  (*thm eo_extract_dep_hnr_mop[to_hnr]
  thm eo_extract_dep_hnr_mop[to_hnr, to_hfref]
  *)
  
  
end  


definition "woarray_slice_assn A \<equiv> hr_comp (eoarray_slice_assn A) (\<langle>some_rel\<rangle>list_rel)"

thm hn_WITH_SPLIT_template

term sao_assn

find_theorems "hr_comp (hr_comp _ _)"

lemma sao_assn_as_comp: "sao_assn A = mk_assn (assn_comp (\<upharpoonleft>(list_assn (oelem_assn A))) raw_array_slice_assn)"
  unfolding sao_assn_def assn_comp_def
  by (auto simp: fun_eq_iff sep_algebra_simps sep_conj_c)

lemma hr_comp_list_list_Cons: "hr_comp \<upharpoonleft>(list_assn B) (\<langle>A\<rangle>list_rel) (x # xs) (z # zs) = (hr_comp (\<upharpoonleft>B) A x z ** hr_comp \<upharpoonleft>(list_assn B) (\<langle>A\<rangle>list_rel) (xs) (zs))"
  by (auto 0 3 simp: hr_comp_def sep_algebra_simps fun_eq_iff list_rel_split_left_iff)  
  


lemma hr_comp_list_list_conv: 
  "hr_comp (\<upharpoonleft>(list_assn B)) (\<langle>A\<rangle>list_rel) = \<upharpoonleft>(list_assn (mk_assn (hr_comp (\<upharpoonleft>B) A)))"
  apply (rule ext)
  apply (rule ext)
  subgoal for xs zs
    apply (cases "length xs = length zs")
    subgoal 
      apply (induction xs zs rule: list_induct2)
      subgoal
        by (auto simp: hr_comp_def sep_algebra_simps)
      subgoal for x xs z zs
        by (simp add: hr_comp_list_list_Cons)
      done
    subgoal
      unfolding hr_comp_def
      by (auto simp: sep_algebra_simps list_rel_imp_same_length)
    done
  done
  
lemma comp_oelem_some_id: "hr_comp \<upharpoonleft>(oelem_assn (mk_assn A)) some_rel = A"  
  by (auto 
    simp: hr_comp_def fun_eq_iff oelem_assn_def some_rel_def in_br_conv sep_algebra_simps
    split: option.splits)
  
  
lemma woarray_slice_assn_assn_as_comp_list: 
  "woarray_slice_assn A = assn_comp (\<upharpoonleft>(list_assn (mk_assn A))) raw_array_slice_assn"
  unfolding woarray_slice_assn_def eoarray_slice_assn_def hr_comp_to_assn_comp sao_assn_as_comp
  apply (simp add: sel_mk_assn[abs_def])
  apply (simp flip: assn_comp_assoc)
  apply (simp only: hr_comp_list_list_conv comp_oelem_some_id flip: hr_comp_to_assn_comp)
  done

lemmas hn_WITH_SPLIT_woarray_slice[sepref_comb_rules] = 
  hn_WITH_SPLIT_assn_comp_template[OF woarray_slice_assn_assn_as_comp_list]


lemma woarray_slice_assn_conv: "woarray_slice_assn A xs ys = eoarray_slice_assn A (map Some xs) ys"
  unfolding woarray_slice_assn_def hr_comp_def
  by (auto simp: some_list_rel_conv sep_algebra_simps)

  
lemma pure_woarray_slice_assn_conv: 
  "is_pure A \<Longrightarrow> woarray_slice_assn A = array_slice_assn A"
  unfolding woarray_slice_assn_def eoarray_slice_assn_def array_slice_assn_def sao_assn_def
  unfolding hr_comp_def 
  apply simp
  apply (clarsimp simp: fun_eq_iff pure_oelem_assn_conv pure_list_assn_to_rel_conv sep_algebra_simps)
  by (smt list_rel_compp oelem_some_rel_conv relcomp.simps)
  
  
lemma mop_to_wos_conv_hnr_dep[sepref_fr_rules]: "(return,mop_to_wo_conv) \<in> 
  [\<lambda>_. True]\<^sub>c (eoarray_slice_assn A)\<^sup>d \<rightarrow> (woarray_slice_assn A) [\<lambda>x r. r=x]\<^sub>c"
  unfolding mop_to_wo_conv_def
  apply sepref_to_hoare
  apply (auto simp: refine_pw_simps sep_algebra_simps woarray_slice_assn_conv simp del: pred_lift_extract_simps elim!: None_not_in_set_conv)
  apply vcg
  done
  
lemma mop_to_wos_conv_hnr_nondep: "(return,mop_to_wo_conv)\<in>(eoarray_slice_assn A)\<^sup>d \<rightarrow>\<^sub>a woarray_slice_assn A"
  unfolding mop_to_wo_conv_def
  apply sepref_to_hoare
  apply (auto simp: refine_pw_simps sep_algebra_simps woarray_slice_assn_conv simp del: pred_lift_extract_simps elim!: None_not_in_set_conv)
  by vcg

lemma mop_to_eos_conv_hnr_dep[sepref_fr_rules]: "(return,mop_to_eo_conv)\<in> [\<lambda>_. True]\<^sub>c (woarray_slice_assn A)\<^sup>d \<rightarrow> (eoarray_slice_assn A) [\<lambda>x r. r=x]\<^sub>c"
  apply sepref_to_hoare
  apply (auto simp: sep_algebra_simps woarray_slice_assn_conv)
  by vcg

lemma mop_to_eos_conv_hnr_nondep: "(return,mop_to_eo_conv)\<in>(woarray_slice_assn A)\<^sup>d \<rightarrow>\<^sub>a eoarray_slice_assn A"
  apply sepref_to_hoare
  apply (auto simp: sep_algebra_simps woarray_slice_assn_conv)
  by vcg

lemma wos_array_get_hnrs[sepref_fr_rules]:   
  "CONSTRAINT Sepref_Basic.is_pure A \<Longrightarrow> (uncurry array_nth, uncurry (RETURN \<circ>\<circ> op_list_get)) \<in> [pre_list_get]\<^sub>a (woarray_slice_assn A)\<^sup>k *\<^sub>a snat_assn\<^sup>k \<rightarrow> A"
  "CONSTRAINT Sepref_Basic.is_pure A \<Longrightarrow> (uncurry array_nth, uncurry mop_list_get) \<in> (woarray_slice_assn A)\<^sup>k *\<^sub>a snat_assn\<^sup>k \<rightarrow>\<^sub>a A"
  using array_slice_get_hnr[of A] array_slice_get_hnr_mop[of A]    
  by (simp_all add: pure_woarray_slice_assn_conv)      
      
lemma wos_array_set_hnrs[sepref_fr_rules]:
  "CONSTRAINT Sepref_Basic.is_pure A \<Longrightarrow>
    (uncurry2 array_upd, uncurry2 (RETURN ooo op_list_set)) \<in> 
      [pre_list_set]\<^sub>a [\<lambda>_. True]\<^sub>c (woarray_slice_assn A)\<^sup>d *\<^sub>a snat_assn\<^sup>k *\<^sub>a A\<^sup>k \<rightarrow>\<^sub>d (\<lambda>_. woarray_slice_assn A) [\<lambda>((ai,_),_) r. r=ai]\<^sub>c"
  "CONSTRAINT Sepref_Basic.is_pure A \<Longrightarrow> (uncurry2 array_upd, uncurry2 mop_list_set) \<in> 
    [\<lambda>_. True]\<^sub>c (woarray_slice_assn A)\<^sup>d *\<^sub>a snat_assn\<^sup>k *\<^sub>a A\<^sup>k \<rightarrow> woarray_slice_assn A [\<lambda>((ai,_),_) r. r=ai]\<^sub>c"
  using array_slice_set_hnr[of A] array_slice_set_hnr_mop[of A]
  by (simp_all add: pure_woarray_slice_assn_conv)      
  
  
context 
  fixes A :: "'a \<Rightarrow> 'b::llvm_rep \<Rightarrow> assn"
  notes [fcomp_norm_simps] = list_rel_id
begin
  sepref_definition swap_eos_impl [llvm_code] is "uncurry2 swap_eo" 
    :: "[\<lambda>_. True]\<^sub>c (woarray_slice_assn A)\<^sup>d *\<^sub>a snat_assn\<^sup>k *\<^sub>a snat_assn\<^sup>k \<rightarrow> woarray_slice_assn A [\<lambda>((ai,_),_) r. r=ai]\<^sub>c"
    unfolding swap_eo_def
    by sepref
  
  sepref_decl_impl (ismop) swap_eos_impl.refine[FCOMP swap_eo_refine] uses mop_list_swap.fref[where A=Id] .
end  
  
export_llvm "swap_eos_impl :: 8 word ptr \<Rightarrow> 64 word \<Rightarrow> 64 word \<Rightarrow> 8 word ptr llM"
  
  
  
(*
oops

xxx, ctd here: 
  implement cmp_idxs in sorting-setup

  then try to refine swap-based algorithms. 
  then try to do delayed-swap optimization! We have to shift to option-list for 
    that, but hopefully can do as refinement step!


wo_array_assn -- owns whole array
  and conversions between eo and wo!

  use these to implement swap and cmp_elems!

  then think how to implement delayed-swap-optimization!
*)




end
