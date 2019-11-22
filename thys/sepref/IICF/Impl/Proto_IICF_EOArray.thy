theory Proto_IICF_EOArray
imports IICF_Array "../../../ds/Proto_EOArray" "../../../sepref/Proto_Sepref_Borrow" "../Intf/IICF_List"
begin



hide_const (open) LLVM_DS_Array.array_assn

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
    \<in> [\<lambda>((xs,i),_). i<length xs \<and> xs!i=None]\<^sub>a\<^sub>d (eoarray_assn A)\<^sup>d *\<^sub>a snat_assn\<^sup>k *\<^sub>a A\<^sup>d \<rightarrow> (\<lambda>_ ((xsi,_),_). cnc_assn (\<lambda>x. x=xsi) (eoarray_assn A))"
    unfolding snat_rel_def snat.assn_is_rel[symmetric] 
    apply sepref_to_hoare
    apply (clarsimp simp: invalid_assn_def eoarray_assn_def cnc_assn_def[abs_def])
    apply (rule htriple_pure_preI, ((determ \<open>drule pure_part_split_conj|erule conjE\<close>)+)?)
    apply vcg
    done

  lemma eo_set_hnr_aux_nondep: "(uncurry2 array_upd,uncurry2 (RETURN ooo op_eo_set)) 
    \<in> [\<lambda>((xs,i),_). i<length xs \<and> xs!i=None]\<^sub>a (eoarray_assn A)\<^sup>d *\<^sub>a snat_assn\<^sup>k *\<^sub>a A\<^sup>d \<rightarrow> eoarray_assn A"
    unfolding snat_rel_def snat.assn_is_rel[symmetric] 
    apply sepref_to_hoare
    apply (clarsimp simp: invalid_assn_def eoarray_assn_def cnc_assn_def[abs_def])
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
    
  sepref_decl_impl (no_register) eo_set_dep: eo_set_hnr_aux by simp  
  sepref_decl_impl eo_set_nondep: eo_set_hnr_aux_nondep by simp  
    
  definition [llvm_inline]: "eo_extract_impl p i \<equiv> doM { r \<leftarrow> array_nth p i; return (r,p) }"

  
  lemma eo_extract_hnr_aux: "(uncurry eo_extract_impl,uncurry (RETURN oo op_eo_extract)) 
    \<in> [\<lambda>(xs,i). i<length xs \<and> xs!i\<noteq>None]\<^sub>a\<^sub>d (eoarray_assn A)\<^sup>d *\<^sub>a snat_assn\<^sup>k \<rightarrow> (\<lambda>_ cargs. A\<times>\<^sub>acnc_assn (\<lambda>x. x=fst cargs) (eoarray_assn A))"  
    unfolding snat_rel_def snat.assn_is_rel[symmetric]
    apply sepref_to_hoare
    apply (clarsimp simp: invalid_assn_def eoarray_assn_def cnc_assn_def[abs_def])
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
    
    
  sepref_decl_impl (no_register) eo_extract_dep: eo_extract_hnr_aux by simp
  sepref_decl_impl eo_extract_nondep: eo_extract_hnr_aux_nondep by simp

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
  by (auto simp: some_list_rel_conv pred_lift_extract_simps sep_algebra_simps)


(* TODO: Move *)
lemma mk_assn_eq_conv[simp]: "mk_assn A = mk_assn B \<longleftrightarrow> A=B"
  by (metis dr_assn_inverses(2) mk_assn_def)

 
    
definition [to_relAPP]: "oelem_rel A \<equiv> {(a, Some b) | a b. (a,b)\<in>A} \<union> {(x,None) | x. True}"  

lemma pure_oelem_assn_conv:
  assumes "is_pure A"
  shows "oelem_assn (mk_assn A) = mk_assn (pure (\<langle>the_pure A\<rangle>oelem_rel))"
  apply (subst pure_the_pure[of A, symmetric], fact)
  apply (auto simp: pure_def oelem_assn_def oelem_rel_def fun_eq_iff pred_lift_extract_simps sep_algebra_simps split: option.splits)  
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
    
definition [simp]: "mop_to_wo_conv xs \<equiv> doN{ ASSERT (None\<notin>set xs); RETURN (map the xs) }"
sepref_register mop_to_wo_conv 

lemma mop_to_wo_conv_hnr_dep: "(return,mop_to_wo_conv)\<in>(eoarray_assn A)\<^sup>d \<rightarrow>\<^sub>a\<^sub>d (\<lambda>_ xi. cnc_assn (\<lambda>x. x=xi) (woarray_assn A))"
  unfolding mop_to_wo_conv_def cnc_assn_def
  apply sepref_to_hoare
  apply (auto simp: refine_pw_simps sep_algebra_simps woarray_assn_conv elim!: None_not_in_set_conv)
  by vcg
  
lemma mop_to_wo_conv_hnr_nondep[sepref_fr_rules]: "(return,mop_to_wo_conv)\<in>(eoarray_assn A)\<^sup>d \<rightarrow>\<^sub>a woarray_assn A"
  unfolding mop_to_wo_conv_def cnc_assn_def
  apply sepref_to_hoare
  apply (auto simp: refine_pw_simps sep_algebra_simps woarray_assn_conv elim!: None_not_in_set_conv)
  by vcg
  
definition [simp]: "mop_to_eo_conv xs \<equiv> RETURN (map Some xs)"

lemma mop_to_eo_conv_hnr_dep: "(return,mop_to_eo_conv)\<in>(woarray_assn A)\<^sup>d \<rightarrow>\<^sub>a\<^sub>d (\<lambda>_ xi. cnc_assn (\<lambda>x. x=xi) (eoarray_assn A))"
  unfolding mop_to_eo_conv_def cnc_assn_def
  apply sepref_to_hoare
  apply (auto simp: sep_algebra_simps woarray_assn_conv)
  by vcg

lemma mop_to_eo_conv_hnr_nondep[sepref_fr_rules]: "(return,mop_to_eo_conv)\<in>(woarray_assn A)\<^sup>d \<rightarrow>\<^sub>a eoarray_assn A"
  unfolding mop_to_eo_conv_def cnc_assn_def
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
    (uncurry2 array_upd, uncurry2 (RETURN ooo op_list_set)) \<in> [pre_list_set]\<^sub>a (woarray_assn A)\<^sup>d *\<^sub>a snat_assn\<^sup>k *\<^sub>a A\<^sup>k \<rightarrow> woarray_assn A"
  "CONSTRAINT Sepref_Basic.is_pure A \<Longrightarrow> (uncurry2 array_upd, uncurry2 mop_list_set) \<in> (woarray_assn A)\<^sup>d *\<^sub>a snat_assn\<^sup>k *\<^sub>a A\<^sup>k \<rightarrow>\<^sub>a woarray_assn A"
  using array_set_hnr[of A] array_set_hnr_mop[of A]
  by (simp_all add: pure_woarray_assn_conv)      
  
definition [simp]: "MOVE \<equiv> RETURN"  
sepref_register MOVE
  
lemma MOVE_rl[sepref_fr_rules]: "(return, MOVE)\<in>A\<^sup>d\<rightarrow>\<^sub>aA"
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
  sepref_definition swap_eo_impl [llvm_code] is "uncurry2 swap_eo" :: "(woarray_assn A)\<^sup>d *\<^sub>a snat_assn\<^sup>k *\<^sub>a snat_assn\<^sup>k \<rightarrow>\<^sub>a woarray_assn A"
    unfolding swap_eo_def
    by sepref
  
  sepref_decl_impl (ismop) swap_eo_impl.refine[FCOMP swap_eo_refine] uses mop_list_swap.fref[where A=Id] .
end  
  
export_llvm "swap_eo_impl :: 8 word ptr \<Rightarrow> 64 word \<Rightarrow> 64 word \<Rightarrow> 8 word ptr llM"

  
  
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
