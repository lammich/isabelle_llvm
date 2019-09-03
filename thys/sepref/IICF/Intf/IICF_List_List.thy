theory IICF_List_List
imports 
  "../../Sepref"
begin


  context begin
    private abbreviation (input) "LR A \<equiv> \<langle>\<langle>A\<rangle>list_rel\<rangle>list_rel"

    sepref_decl_op list_list_lempty: "\<lambda>n. replicate n []" :: "nat_rel \<rightarrow> LR A" .
    sepref_decl_op list_list_push_back: "\<lambda>xss i x. xss[i:=xss!i@[x]]" 
      :: "[\<lambda>((xss,i),_). i<length xss]\<^sub>f (LR A \<times>\<^sub>r nat_rel) \<times>\<^sub>r A \<rightarrow> LR A" .

    sepref_decl_op list_list_pop_back: "\<lambda>xss i. (last (xss!i), xss[i:=butlast (xss!i)])" 
      :: "[\<lambda>(xss,i). i<length xss \<and> xss!i\<noteq>[]]\<^sub>f (LR A \<times>\<^sub>r nat_rel)\<rightarrow> A \<times>\<^sub>r LR A" 
      unfolding conv_to_is_Nil short_circuit_conv
      by parametricity
      
    sepref_decl_op list_list_upd: "\<lambda>xss i j x. xss[i:=(xss!i)[j:=x]]" 
      :: "[\<lambda>(((xss,i),j),x). i<length xss \<and> j<length (xss!i)]\<^sub>f (((LR A \<times>\<^sub>r nat_rel) \<times>\<^sub>r nat_rel) \<times>\<^sub>r A) \<rightarrow> LR A" 
      unfolding short_circuit_conv
      by parametricity
      
    sepref_decl_op list_list_idx: "\<lambda>xss i j. xss!i!j" :: "[\<lambda>((xss,i),j). i<length xss \<and> j<length (xss!i)]\<^sub>f ((LR A \<times>\<^sub>r nat_rel) \<times>\<^sub>r nat_rel) \<rightarrow> A" 
      unfolding short_circuit_conv
      by parametricity
    
    sepref_decl_op list_list_llen: "\<lambda>xss i. length (xss!i)" :: "[\<lambda>(xss,i). i<length xss]\<^sub>f LR A \<times>\<^sub>r nat_rel \<rightarrow> nat_rel" .
    (* TODO: list_list is a proper subtype of list. So share operations! length, empty, ... *)
    sepref_decl_op list_list_len: "length :: _ list list \<Rightarrow> _" :: "LR A \<rightarrow> nat_rel" .
    
    sepref_decl_op list_list_take: "\<lambda>xss i l. (xss[i:=take l (xss!i)])" 
      :: "[\<lambda>((xss,i),l). i<length xss \<and> l\<le>length (xss!i)]\<^sub>f ((LR A \<times>\<^sub>r nat_rel) \<times>\<^sub>r nat_rel)\<rightarrow> LR A" 
      unfolding conv_to_is_Nil short_circuit_conv
      by parametricity
    
  end

  locale list_list_custom_empty = 
    fixes rel empty PRE and op_custom_empty :: "nat \<Rightarrow> 'a list list"
    assumes customize_hnr_aux: "(empty,(RETURN o (op_list_list_lempty::nat \<Rightarrow> 'a list list))) \<in> [PRE]\<^sub>a snat_assn\<^sup>k \<rightarrow> rel"
    assumes op_custom_empty_def: "op_custom_empty = op_list_list_lempty"
  begin
    sepref_register op_custom_empty :: "nat \<Rightarrow> 'c list list"
  
    lemma fold_custom_empty:
      "replicate n [] = op_custom_empty n"
      "op_list_list_lempty = op_custom_empty"
      "mop_list_list_lempty n = RETURN (op_custom_empty n)"
      unfolding op_custom_empty_def by simp_all
  
    lemmas custom_hnr[sepref_fr_rules] = customize_hnr_aux[folded op_custom_empty_def]
  end


  text \<open>Fold lemmas for manual folding.\<close>
  (* TODO: Why not use interface and op-id for that? *)
  lemma fold_op_list_list_push_back: "xss[i:=xss!i@[x]] = op_list_list_push_back xss i x" by simp
  lemma fold_op_list_list_pop_back: "(last (xss!i), xss[i:=butlast (xss!i)]) = op_list_list_pop_back xss i" by simp
  lemma fold_op_list_list_upd: "xss[i:=(xss!i)[j:=x]] = op_list_list_upd xss i j x" by simp
  lemma fold_op_list_list_idx: "xs!i!j = op_list_list_idx xs i j" by simp
  lemma fold_op_list_list_llen: "length (xs!i) = op_list_list_llen xs i" by simp
  lemma fold_op_list_list_take: "xss[i:=take n (xss!i)] = op_list_list_take xss i n" by simp

  lemmas fold_op_list_list = 
    fold_op_list_list_push_back
    fold_op_list_list_pop_back 
    fold_op_list_list_upd
    fold_op_list_list_idx
    fold_op_list_list_llen
    fold_op_list_list_take  
  
end
