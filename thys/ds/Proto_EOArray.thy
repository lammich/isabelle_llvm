theory Proto_EOArray
imports LLVM_DS_NArray
begin
  
  subsection \<open>List Assertion\<close>

  definition "list_assn A \<equiv> mk_assn (\<lambda>xs xsi. \<up>(length xs = length xsi) ** (\<Union>*i\<in>{0..<length xs}. \<upharpoonleft>A (xs!i) (xsi!i)))"

  text \<open>Inductive characterization\<close>
  lemma list_assn_ee_simp:
    "\<upharpoonleft>(list_assn A) [] [] = \<box>"
    unfolding list_assn_def
    by (auto simp: sep_algebra_simps)
  
  lemma list_assn_nm_simp:
    "\<upharpoonleft>(list_assn A) [] (xi#xsi) = sep_false"
    "\<upharpoonleft>(list_assn A) (x#xs) [] = sep_false"
    unfolding list_assn_def
    by (auto simp: sep_algebra_simps)


  lemma list_assn_cc_simp:
    shows "\<upharpoonleft>(list_assn A) (x#xs) (xi#xsi) = (\<upharpoonleft>A x xi ** \<upharpoonleft>(list_assn A) xs xsi)"
  proof -
    have intv_conv1: "{0..<Suc n} = insert 0 (Suc`{0..<n})" for n by auto
    have 1: "(\<Union>*i\<in>{0..<Suc n}. A i) = (A 0 ** (\<Union>*i\<in>{0..<n}. A (Suc i)))" for A :: "nat \<Rightarrow> ll_assn" and n
      by (simp del: image_Suc_atLeastLessThan add: intv_conv1 sep_set_img_map)
  
    show ?thesis
      unfolding list_assn_def
      by (auto simp: sep_algebra_simps entails_lift_extract_simps entails_eq_iff 1)
      
  qed    
  

  lemmas list_assn_simps[simp] = list_assn_ee_simp list_assn_nm_simp list_assn_cc_simp
  
  lemma list_assn_empty1_conv[simp]: "\<upharpoonleft>(list_assn A) [] ys = \<up>(ys=[])"
    by (cases ys) (auto simp: sep_algebra_simps)

  lemma list_assn_empty2_conv[simp]: "\<upharpoonleft>(list_assn A) xs [] = \<up>(xs=[])"
    by (cases xs) (auto simp: sep_algebra_simps)
    
    
  lemma list_assn_cons1_conv: "\<upharpoonleft>(list_assn A) (x#xs) yys = (EXS y ys. \<up>(yys=y#ys) ** \<upharpoonleft>A x y ** \<upharpoonleft>(list_assn A) xs ys)"
    apply (cases yys)
    by (auto simp: entails_eq_iff sep_algebra_simps)
  
  lemma list_assn_cons2_conv: "\<upharpoonleft>(list_assn A) xxs (y#ys) = (EXS x xs. \<up>(xxs=x#xs) ** \<upharpoonleft>A x y ** \<upharpoonleft>(list_assn A) xs ys)"
    apply (cases xxs)
    by (auto simp: entails_eq_iff sep_algebra_simps)
  
  lemma list_assn_append1_conv: "\<upharpoonleft>(list_assn A) (xs\<^sub>1@xs\<^sub>2) yys = (EXS ys\<^sub>1 ys\<^sub>2. \<up>(yys=ys\<^sub>1@ys\<^sub>2) ** \<upharpoonleft>(list_assn A) xs\<^sub>1 ys\<^sub>1 ** \<upharpoonleft>(list_assn A) xs\<^sub>2 ys\<^sub>2)"
    apply (induction xs\<^sub>1 arbitrary: yys)
    by (auto simp: sep_algebra_simps list_assn_cons1_conv)
  
  lemma list_assn_append2_conv: "\<upharpoonleft>(list_assn A) xxs (ys\<^sub>1@ys\<^sub>2) = (EXS xs\<^sub>1 xs\<^sub>2. \<up>(xxs=xs\<^sub>1@xs\<^sub>2) ** \<upharpoonleft>(list_assn A) xs\<^sub>1 ys\<^sub>1 ** \<upharpoonleft>(list_assn A) xs\<^sub>2 ys\<^sub>2)"
    apply (induction ys\<^sub>1 arbitrary: xxs)
    by (auto simp: sep_algebra_simps list_assn_cons2_conv)

  lemma list_assn_neq_len[simp]: 
    "length xs \<noteq> length xsi \<Longrightarrow> \<upharpoonleft>(list_assn A) xs xsi = sep_false"  
    "length xsi \<noteq> length xs \<Longrightarrow> \<upharpoonleft>(list_assn A) xs xsi = sep_false"  
    by (auto simp: list_assn_def)
    
  lemma list_assn_append[simp]: "length xs\<^sub>1 = length ys\<^sub>1 
    \<Longrightarrow> \<upharpoonleft>(list_assn A) (xs\<^sub>1@xs\<^sub>2) (ys\<^sub>1@ys\<^sub>2) = (\<upharpoonleft>(list_assn A) xs\<^sub>1 ys\<^sub>1 ** \<upharpoonleft>(list_assn A) xs\<^sub>2 ys\<^sub>2)"  
    apply (induction rule: list_induct2)
    by (auto simp: sep_algebra_simps)
    
    
  lemma list_assn_pure_part[vcg_prep_ext_rules]: 
    "pure_part (\<upharpoonleft>(list_assn A) xs ys) \<Longrightarrow> length xs = length ys" (* TODO: Extraction should also go to elements! *)  
    unfolding list_assn_def
    apply (vcg_prepare_external)
    by (auto)
    

  definition "oelem_assn A \<equiv> mk_assn (\<lambda>None \<Rightarrow> \<lambda>_. \<box> | Some x \<Rightarrow> \<lambda>xi. \<upharpoonleft>A x xi)"

  lemma oelem_assn_simps[simp]:
    "\<upharpoonleft>(oelem_assn A) None xi = \<box>"
    "\<upharpoonleft>(oelem_assn A) (Some x) xi = \<upharpoonleft>A x xi"  
    unfolding oelem_assn_def by auto


  lemma split_list_according:
    assumes "xs = xs\<^sub>1@x#xs\<^sub>2"
    assumes "length ys = length xs"
    obtains ys\<^sub>1 y ys\<^sub>2 where "ys = ys\<^sub>1@y#ys\<^sub>2" "length ys\<^sub>1 = length xs\<^sub>1" "length ys\<^sub>2 = length xs\<^sub>2"
      using assms
      apply (subst (asm) id_take_nth_drop[of "length xs\<^sub>1" ys])
      by auto
  

  lemma lo_focus_elem_gen:
    assumes "i<length xs" "xs!i = Some x"  
    shows "\<upharpoonleft>(list_assn (oelem_assn A)) xs ys = ((\<upharpoonleft>A x (ys!i)) ** \<upharpoonleft>(list_assn (oelem_assn A)) (xs[i:=None]) (ys[i:=anything]))"
  proof (cases "length ys = length xs")
    case [simp]: True
    
    obtain xs\<^sub>1 xs\<^sub>2 where XSF[simp]: "xs = xs\<^sub>1@Some x#xs\<^sub>2" and [simp]: "i = length xs\<^sub>1" 
      using id_take_nth_drop[OF assms(1)] assms(2) by fastforce
    obtain ys\<^sub>1 y ys\<^sub>2 where [simp]: "ys = ys\<^sub>1@y#ys\<^sub>2" "length ys\<^sub>1 = length xs\<^sub>1" "length ys\<^sub>2 = length xs\<^sub>2"
      using split_list_according[OF XSF True] .
      
    show ?thesis
      by (simp add: nth_append list_update_append sep_algebra_simps sep_conj_c)
      
  qed simp
      
  text \<open>Extract element from list assertion\<close>
  lemma lo_extract_elem:
    assumes "i<length xs" "xs!i = Some x"  
    shows "\<upharpoonleft>(list_assn (oelem_assn A)) xs ys = ((\<upharpoonleft>A x (ys!i)) ** \<upharpoonleft>(list_assn (oelem_assn A)) (xs[i:=None]) ys)"
    by (metis list_update_id lo_focus_elem_gen[OF assms])
    
  
  text \<open>Insert element into list assertion\<close>  
  lemma lo_insert_elem:
    assumes "i<length xs" "xs!i = None"
    shows "\<upharpoonleft>(list_assn (oelem_assn A)) (xs[i:=Some x]) (ys[i:=y]) = (\<upharpoonleft>A x y ** \<upharpoonleft>(list_assn (oelem_assn A)) xs ys)"
    apply (cases "length ys = length xs")
    using lo_focus_elem_gen[of i "xs[i:=Some x]" x A "ys[i:=y]" "ys!i"] using assms
    apply simp_all
    by (metis list_update_id)
    
  
  definition "nao_assn A \<equiv> mk_assn (\<lambda>xs p. EXS xsi. \<upharpoonleft>narray_assn xsi p ** \<upharpoonleft>(list_assn (oelem_assn A)) xs xsi)"

  
  lemma nao_nth_rule[vcg_rules]: "llvm_htriple 
    (\<upharpoonleft>(nao_assn A) xs p \<and>* \<upharpoonleft>snat.assn i ii \<and>* \<up>\<^sub>d(i < length xs \<and> xs!i\<noteq>None)) 
    (array_nth p ii)
    (\<lambda>ri. \<upharpoonleft>A (the (xs!i)) ri \<and>* \<upharpoonleft>(nao_assn A) (xs[i:=None]) p)"  
    unfolding nao_assn_def
    supply [simp] = lo_extract_elem
    apply vcg'
    done
  
  
  lemma nao_upd_rule_snat[vcg_rules]: "llvm_htriple 
    (\<upharpoonleft>(nao_assn A) xs p \<and>* \<upharpoonleft>A x xi \<and>* \<upharpoonleft>snat.assn i ii \<and>* \<up>\<^sub>d(i < length xs \<and> xs!i=None)) 
    (array_upd p ii xi)
    (\<lambda>r. \<up>(r = p) \<and>* \<upharpoonleft>(nao_assn A) (xs[i := Some x]) p)"
    unfolding nao_assn_def 
    supply [simp] = lo_insert_elem
    apply vcg'
    done

    
    
  definition "sao_assn A \<equiv> mk_assn (\<lambda>xs p. EXS xsi. \<upharpoonleft>array_slice_assn xsi p ** \<upharpoonleft>(list_assn (oelem_assn A)) xs xsi)"

  
  lemma sao_nth_rule[vcg_rules]: "llvm_htriple 
    (\<upharpoonleft>(sao_assn A) xs p \<and>* \<upharpoonleft>snat.assn i ii \<and>* \<up>\<^sub>d(i < length xs \<and> xs!i\<noteq>None)) 
    (array_nth p ii)
    (\<lambda>ri. \<upharpoonleft>A (the (xs!i)) ri \<and>* \<upharpoonleft>(sao_assn A) (xs[i:=None]) p)"  
    unfolding sao_assn_def
    supply [simp] = lo_extract_elem
    apply vcg'
    done
  
  
  lemma sao_upd_rule_snat[vcg_rules]: "llvm_htriple 
    (\<upharpoonleft>(sao_assn A) xs p \<and>* \<upharpoonleft>A x xi \<and>* \<upharpoonleft>snat.assn i ii \<and>* \<up>\<^sub>d(i < length xs \<and> xs!i=None)) 
    (array_upd p ii xi)
    (\<lambda>r. \<up>(r = p) \<and>* \<upharpoonleft>(sao_assn A) (xs[i := Some x]) p)"
    unfolding sao_assn_def 
    supply [simp] = lo_insert_elem
    apply vcg'
    done
    
    
        
(*
  xxx, ctd here: new, free, then integrate into sepref!   
    XXX: First integrate into sepref, than care about new and free.
      for sorting algos, we only need get and set!
        
*)    
    
    
    
        
  
end
