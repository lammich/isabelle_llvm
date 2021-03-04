theory IICF_Array_of_Array_List
imports "../Intf/IICF_List_List" "../../../ds/Array_of_Array_List"
begin
  
  abbreviation "raw_aal_assn TYPE('l::len2) TYPE('ll::len2) 
    \<equiv> \<upharpoonleft>(Array_of_Array_List.aal_assn :: (_,('l,_,'ll) array_array_list)dr_assn)"

  definition aal_assn where "aal_assn A \<equiv> hr_comp (raw_aal_assn TYPE(_) TYPE(_)) (\<langle>\<langle>the_pure A\<rangle>list_rel\<rangle>list_rel)"
  lemmas [safe_constraint_rules] = CN_FALSEI[of is_pure "aal_assn A" for A]

  abbreviation aal_assn' where "aal_assn' TYPE('l::len2) TYPE('ll::len2) \<equiv> aal_assn :: _ \<Rightarrow> _ \<Rightarrow> ('l,_,'ll) array_array_list \<Rightarrow> _"
  

  context 
    fixes l_dummy :: "'l::len2 itself"
    fixes ll_dummy :: "'ll::len2 itself"
    fixes L LL AA
    defines [simp]: "L \<equiv> (LENGTH ('l))"
    defines [simp]: "LL \<equiv> (LENGTH ('ll))"
    defines [simp]: "AA \<equiv> raw_aal_assn TYPE('l::len2) TYPE('ll::len2)"
  begin  

    private lemma n_unf: "hr_comp AA (\<langle>\<langle>the_pure A\<rangle>list_rel\<rangle>list_rel) = aal_assn A" unfolding aal_assn_def AA_def ..
  
    private lemma params: 
      "(L,L)\<in>nat_rel"
      "(LL,LL)\<in>nat_rel"
      "(max_snat, max_snat) \<in> Id \<rightarrow> Id"
      by auto
    
    context 
      notes [fcomp_norm_unfold] = n_unf
      notes [param] = params
    begin
    
      private method p_hnr = unfold snat_rel_def snat.assn_is_rel[symmetric]; sepref_to_hoare; vcg
    
      lemma aal_push_back_hnr_aux: "(uncurry2 aal_push_back, uncurry2 (RETURN ooo op_list_list_push_back)) 
        \<in> [\<lambda>((xss,i),x). i < length xss \<and> length (xss!i) + 1 < max_snat LL]\<^sub>a 
            AA\<^sup>d *\<^sub>a snat_assn\<^sup>k *\<^sub>a id_assn\<^sup>k \<rightarrow> AA"
        by p_hnr
    
      sepref_decl_impl aal_push_back_hnr_aux
        unfolding short_circuit_conv by parametricity
                
      lemma aal_pop_back_hnr_aux: "(uncurry aal_pop_back, uncurry (RETURN oo op_list_list_pop_back)) 
        \<in> [\<lambda>(xss,i). i<length xss \<and> xss!i\<noteq>[]]\<^sub>a AA\<^sup>d *\<^sub>a snat_assn\<^sup>k \<rightarrow> id_assn \<times>\<^sub>a AA"
        by p_hnr

      sepref_decl_impl aal_pop_back_hnr_aux    
        unfolding short_circuit_conv conv_to_is_Nil by parametricity

      lemma aal_idx_hnr_aux: "(uncurry2 aal_idx, uncurry2 (RETURN ooo op_list_list_idx)) 
        \<in> [\<lambda>((xss,i),j). i<length xss \<and> j < length (xss!i)]\<^sub>a AA\<^sup>k *\<^sub>a snat_assn\<^sup>k *\<^sub>a snat_assn\<^sup>k \<rightarrow> id_assn"
        by p_hnr

      sepref_decl_impl aal_idx_hnr_aux         
        unfolding short_circuit_conv by parametricity

      lemma aal_upd_hnr_aux: "(uncurry3 aal_upd, uncurry3 (RETURN oooo op_list_list_upd)) 
        \<in> [\<lambda>(((xss,i),j),x). i<length xss \<and> j < length (xss!i)]\<^sub>a AA\<^sup>d *\<^sub>a snat_assn\<^sup>k *\<^sub>a snat_assn\<^sup>k *\<^sub>a id_assn\<^sup>k \<rightarrow> AA"
        by p_hnr

      sepref_decl_impl aal_upd_hnr_aux         
        unfolding short_circuit_conv by parametricity
        
                
      lemma aal_llen_hnr_aux: "(uncurry aal_llen, uncurry (RETURN oo op_list_list_llen)) 
        \<in> [\<lambda>(xss,i). i<length xss]\<^sub>a AA\<^sup>k *\<^sub>a snat_assn\<^sup>k \<rightarrow> snat_assn"
        by p_hnr
        
      sepref_decl_impl aal_llen_hnr_aux .
                
      lemma aal_len_hnr_aux: "(aal_len,RETURN o op_list_list_len) \<in> AA\<^sup>k \<rightarrow>\<^sub>a snat_assn" by p_hnr
      sepref_decl_impl aal_len_hnr_aux .
                
      lemma aal_empty_hnr_aux: "(aal_new_raw, RETURN o op_list_list_lempty) \<in> [\<lambda>_. 4<LL]\<^sub>a snat_assn\<^sup>k \<rightarrow> AA"
        by p_hnr

      sepref_decl_impl (no_register) aal_empty: aal_empty_hnr_aux .

      
      lemma aal_take_hnr_aux: "(uncurry2 aal_take, uncurry2 (RETURN ooo op_list_list_take)) 
        \<in> [\<lambda>((xss,i),l). i<length xss \<and> l \<le> length (xss!i)]\<^sub>a AA\<^sup>d *\<^sub>a snat_assn\<^sup>k *\<^sub>a snat_assn\<^sup>k \<rightarrow> AA"
        by p_hnr

      sepref_decl_impl aal_take_hnr_aux    
        unfolding short_circuit_conv by parametricity
      
    end
  end  

  definition op_aal_lempty where [simp]: "op_aal_lempty TYPE('l::len2) TYPE('ll::len2) \<equiv> op_list_list_lempty"
  sepref_register "op_aal_lempty TYPE('l::len2) TYPE('ll::len2)"
  
  lemma aal_lempty_hnr[sepref_fr_rules]: 
    "(aal_new_raw, RETURN \<circ> (PR_CONST (op_aal_lempty TYPE('l::len2) TYPE('ll::len2)))) 
      \<in> [\<lambda>x. 4 < LENGTH('ll)]\<^sub>a snat_assn\<^sup>k \<rightarrow> aal_assn' TYPE('l) TYPE('ll) A"
    using aal_empty_hnr by simp
    
  lemma aal_fold_custom_empty:
    "replicate n [] = op_aal_lempty TYPE('l::len2) TYPE('ll::len2) n"
    "op_list_list_lempty n = op_aal_lempty TYPE('l::len2) TYPE('ll::len2) n"
    "mop_list_list_lempty n = RETURN (op_aal_lempty TYPE('l::len2) TYPE('ll::len2) n)"
    by simp_all
  
    
  (* TODO: Move *)  
  lemma rdomp_conv_pure_part: "rdomp A a \<longleftrightarrow> (\<exists>c. pure_part (A a c))"
    unfolding rdomp_def pure_part_def by blast
    
  lemma pure_part_EXS_conv[simp]: "pure_part (EXS x. A x) \<longleftrightarrow> (\<exists>x. pure_part (A x))"  
    by (auto simp: pure_part_def)
    
  lemma pure_part_set_imgD:
    assumes "pure_part (\<Union>*i\<in>I. f i)"  
    shows "\<forall>i\<in>I. pure_part (f i)"
  proof (cases "finite I")  
    assume "finite I"
    thus ?thesis using assms
      by (induction I) (auto dest!: pure_part_split_conj)
  next
    assume "infinite I"  
    with assms have False by simp
    thus ?thesis ..
  qed
    
  
  lemma pure_part_arl_assnD[vcg_prep_ext_rules]: "pure_part (\<upharpoonleft>arl_assn xs (a::(_,'l::len2) array_list)) 
    \<Longrightarrow> length xs < max_snat LENGTH('l)"
    unfolding arl_assn_def arl_assn'_def
    apply (cases a)
    by (auto dest!: pure_part_split_conj snat.vcg_prep_delete_assn)
    

  lemma aal_assn_boundsD_aux1:
    assumes A: "rdomp (aal_assn' TYPE('l::len2) TYPE('ll::len2) A) xss"  
    shows "length xss < max_snat LENGTH('l)" (is ?G1)
      and "\<forall>xs\<in>set xss. length xs < max_snat LENGTH('ll)" (is ?G2)
      (*and "\<forall>xs\<in>set xss. \<forall>x\<in>set xs. rdomp A x" (is ?G3)*)
      
  proof -    
    from A obtain x :: "('b,'ll) array_list list" and y where
      REL: "(y, xss) \<in> \<langle>\<langle>the_pure A\<rangle>list_rel\<rangle>list_rel"
      and "length x = length y"
      and PP: "\<forall>xa\<in>{0..<length y}. pure_part (\<upharpoonleft>arl_assn (y ! xa) (x ! xa))"
      and LENY: "length y < max_snat LENGTH('l)"
      unfolding 
        IICF_Array_of_Array_List.aal_assn_def
        Array_of_Array_List.aal_assn_def
        nao_assn_def 
      apply (auto simp: rdomp_hrcomp_conv)
      apply (auto 
        simp: rdomp_conv_pure_part in_set_conv_nth
        dest!: pure_part_split_conj pure_part_set_imgD snat.vcg_prep_delete_assn) 
        
      done

    from REL have [simp]: "length xss = length y"  
      by (auto dest!: list_rel_imp_same_length)
      
    from LENY show "length xss < max_snat LENGTH('l)" by simp 
      
    have "\<forall>xs\<in>set xss. length xs < max_snat LENGTH('ll) \<^cancel>\<open>\<and> (\<forall>x\<in>set xs. rdomp A x)\<close>"
    proof (rule ballI; clarsimp simp: in_set_conv_nth)  
      fix i
      assume ILEN: "i<length y"
    
      from REL ILEN have "(y!i,xss!i)\<in>\<langle>the_pure A\<rangle>list_rel"
        by parametricity simp_all
      then have [simp]: "length (xss!i) = length (y!i)"
        by (auto dest!: list_rel_imp_same_length)
    
      from PP ILEN have "pure_part (\<upharpoonleft>arl_assn (y ! i) (x ! i))" by auto
      hence "length (y!i) < max_snat LENGTH('ll)"
        by (auto dest!: pure_part_arl_assnD)
      then show "length (xss ! i) < max_snat LENGTH('ll)" by auto
    qed
    thus ?G2 by blast
  qed      

  lemma aal_assn_boundsD':
    assumes A: "rdomp (aal_assn' TYPE('l::len2) TYPE('ll::len2) A) xss"  
    shows "length xss < max_snat LENGTH('l) 
      \<and> (\<forall>xs\<in>set xss. length xs < max_snat LENGTH('ll))"
    using aal_assn_boundsD_aux1[OF A] by auto
      
  lemma aal_assn_boundsD[sepref_bounds_dest]:  
    assumes A: "rdomp (aal_assn' TYPE('l::len2) TYPE('ll::len2) A) xss"  
    shows "length xss < max_snat LENGTH('l)"
    using aal_assn_boundsD_aux1[OF A] by auto
    
  subsection \<open>Ad-Hoc Regression Tests\<close>
    
  experiment
  begin
    sepref_definition example [llvm_code] is "\<lambda>n. do {
      let l = replicate n [];
      
      let l = op_list_list_push_back l (n-1) 42;
      let l = op_list_list_push_back l (n-1) 43;
      let (x,l) = op_list_list_pop_back l (n-1);
      let l = op_list_list_push_back l (n-1) x;
      let l = op_list_list_take l (n-1) 1;
      
      RETURN l
    }" :: "[\<lambda>n. n\<in>{1..150}]\<^sub>a (snat_assn' TYPE(32))\<^sup>k \<rightarrow> aal_assn' TYPE(32) TYPE(32) (snat_assn' TYPE(32))"
    apply (rewrite aal_fold_custom_empty[where 'l=32 and 'll=32])
    apply (annot_snat_const "TYPE(32)")
    apply sepref
    done
  
    export_llvm (no_header) example is example
  
    
  end  
  
  
  
            
        
end
