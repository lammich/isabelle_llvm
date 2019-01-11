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
    supply [simp] = max_snat_def
    apply sepref_dbg_keep
    done
  
    export_llvm example is example
  
    
  end  
  
  
  
            
        
end
