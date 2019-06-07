theory IICF_Indexed_Array_List
imports 
  "HOL-Library.Rewrite"
  "../Intf/IICF_List"
  "List-Index.List_Index"
  IICF_Array
  IICF_MS_Array_List
begin



  (* TODO: Move *)

  abbreviation "snatb_rel N \<equiv> b_rel snat_rel (\<lambda>x. x<N)"
  abbreviation "snatb_rel' TYPE('l::len2) N \<equiv> b_rel (snat_rel' TYPE('l)) (\<lambda>x. x<N)"
  abbreviation "snatb_assn N \<equiv> b_assn snat_assn (\<lambda>x. x<N)"
  abbreviation "snatb_assn' TYPE('l::len2) N \<equiv> (snatb_assn N :: _ \<Rightarrow> 'l word \<Rightarrow> _)"
    

  (* TODO: Move *)
  lemma R_comp_brel_id_conv[fcomp_norm_simps]: "R O b_rel Id P = b_rel R P" by auto
  
  
  (* TODO: Move, clean up proof *)
  lemma snat_rel_range: "Range (snat_rel' TYPE('l)) = {0..<max_snat LENGTH('l::len2)}"
    apply (auto simp: Range_iff snat_rel_def snat.rel_def in_br_conv)
    subgoal for x
      apply (rule exI[where x="word_of_int (int x)"])
      apply (auto simp: max_snat_def snat_invar_def)
      subgoal
        by (metis One_nat_def snat_eq_unat(1) snat_in_bounds_aux unat_of_nat_eq word_of_nat) 
      subgoal
        by (metis One_nat_def Word_Lemmas.of_nat_power diff_less len_gt_0 max_unat_def n_less_equal_power_2 not_msb_from_less power_0 word_of_nat)
      done
    done
            
  (* TODO: Move *)  
  lemma in_snat_nbn_conv: "(a,b)\<in>(R O nbn_rel N) \<longleftrightarrow> (a,b)\<in>R \<and> b<N" by auto
    
  lemma range_comp_nbn_conv: "Range (R O nbn_rel N) = Range R \<inter> {0..<N}"
    by (auto 0 3 simp: b_rel_def)
    
  
  (*
  lemma range_snatb_conv: "Range (snatb_rel' TYPE('l) N) = {0..<N} \<inter> Range (snat_rel' TYPE('l::len2))"
    unfolding snatb_rel_def 
    by (auto simp: range_comp_nbn_conv)
    
  lemma in_snatb_rel_bound: "(a,b)\<in>snatb_rel N \<Longrightarrow> b<N" 
    by (simp add: in_snat_nbn_conv snatb_rel_def)
  *)  

  

  text \<open>We implement distinct lists of natural numbers in the range @{text "{0..<N}"}
    by a length counter and two arrays of size @{text N}. 
    The first array stores the list, and the second array stores the positions of
    the elements in the list, or @{text N} if the element is not in the list.

    This allows for an efficient index query.

    The implementation is done in two steps: 
      First, we use a list and a fixed size list for the index mapping.
      Second, we refine the lists to arrays.
 \<close>

  type_synonym aial = "nat list \<times> nat option list"

  locale ial_invar = fixes
         maxsize :: nat 
    and  l :: "nat list"
    and qp :: "nat option list"
    assumes maxsize_eq[simp]: "maxsize = length qp"
    assumes l_distinct[simp]: "distinct l"
    assumes l_set: "set l \<subseteq> {0..<length qp}"
    assumes qp_def: "\<forall>k<length qp. qp!k = (if k\<in>set l then Some (List_Index.index l k) else None)"
  begin  
    lemma l_len: "length l \<le> length qp"
    proof -
      from card_mono[OF _ l_set] have "card (set l) \<le> length qp" by auto
      with distinct_card[OF l_distinct] show ?thesis by simp
    qed  

    lemma idx_len[simp]: "i<length l \<Longrightarrow> l!i < length qp"
      using l_set
      by (metis atLeastLessThan_iff nth_mem psubsetD psubsetI)

    lemma l_set_simp[simp]: "k\<in>set l \<Longrightarrow> k < length qp" 
      by (auto dest: set_mp[OF l_set])

    lemma qpk_idx: "k<length qp \<Longrightarrow> qp ! k \<noteq> None \<longleftrightarrow> k \<in> set l"
    proof (rule iffI)
      assume A: "k<length qp"
      {
        assume "qp!k \<noteq> None"
        with spec[OF qp_def, of k] A show "k\<in>set l" 
          by (auto split: if_split_asm)
      }
      {
        assume "k\<in>set l"
        thus "qp!k\<noteq>None"
          using qp_def by (auto split: if_split_asm) []
      }
    qed 

    lemma lqpk[simp]: "k \<in> set l \<Longrightarrow> l ! (the (qp ! k)) = k"
      using spec[OF qp_def, of k] by auto

    lemma "\<lbrakk>i<length l; j<length l; l!i=l!j\<rbrakk> \<Longrightarrow> i=j"
      by (simp add: nth_eq_iff_index_eq)
      
    lemmas index_swap[simp] = index_swap_if_distinct[folded swap_def, OF l_distinct]  

    lemma swap_invar:  
      assumes "i<length l" "j<length l"
      shows "ial_invar (length qp) (swap l i j) (qp[l ! j := Some i, l ! i := Some j])"
      using assms
      apply unfold_locales
      apply auto []
      apply auto []
      apply auto []
      apply (auto simp: simp: nth_list_update nth_eq_iff_index_eq index_nth_id) []
      using qp_def apply auto [2]
      done

  end

  definition "ial_rel1 maxsize \<equiv> br fst (uncurry (ial_invar maxsize))"

  
  definition op_ial_empty_sz :: "nat \<Rightarrow> 'a list" 
    where [simp]: "op_ial_empty_sz ms \<equiv> op_list_empty"
  
  
  definition "aial_empty N \<equiv> do {
    let l = op_marl_empty N;
    let qp = op_array_custom_replicate N None;
    RETURN (l,qp)
  }"

  lemma aial_empty_refine: "(aial_empty N,RETURN op_list_empty) \<in> \<langle>ial_rel1 N\<rangle>nres_rel"
    unfolding aial_empty_def
    apply (refine_vcg nres_relI)
    apply (clarsimp simp: ial_rel1_def br_def)
    apply unfold_locales
    apply auto
    done
  
  
  definition "aial_swap \<equiv> \<lambda>(l,qp) i j. do {
    vi \<leftarrow> mop_list_get l i;
    vj \<leftarrow> mop_list_get l j;
    l \<leftarrow> mop_list_set l i vj;
    l \<leftarrow> mop_list_set l j vi;
    qp \<leftarrow> mop_list_set qp vj (Some i);
    qp \<leftarrow> mop_list_set qp vi (Some j);
    RETURN (l,qp)
  }"

  lemma in_ial_rel1_conv: 
    "((pq, qp), l) \<in> ial_rel1 ms \<longleftrightarrow> pq=l \<and> ial_invar ms l qp" 
    by (auto simp: ial_rel1_def in_br_conv)

  lemma aial_swap_refine: 
    "(aial_swap,mop_list_swap) \<in> ial_rel1 maxsize \<rightarrow> nat_rel \<rightarrow> nat_rel \<rightarrow> \<langle>ial_rel1 maxsize\<rangle>nres_rel"
  proof (intro fun_relI nres_relI; clarsimp simp: in_ial_rel1_conv; refine_vcg; clarsimp)
    fix l qp i j
    assume [simp]: "i<length l" "j<length l" and "ial_invar maxsize l qp"
    then interpret ial_invar maxsize l qp by simp

    show "aial_swap (l, qp) i j \<le> SPEC (\<lambda>c. (c, swap l i j) \<in> ial_rel1 maxsize)"
      unfolding aial_swap_def
      apply refine_vcg
      apply (auto simp add: in_ial_rel1_conv swap_def[symmetric] swap_invar)
      done
  qed    
  

  definition aial_length :: "aial \<Rightarrow> nat nres" 
    where "aial_length \<equiv> \<lambda>(l,_). RETURN (op_list_length l)"

  lemma aial_length_refine: "(aial_length, mop_list_length) \<in> ial_rel1 maxsize \<rightarrow> \<langle>nbn_rel (maxsize+1)\<rangle>nres_rel"
    apply (intro fun_relI nres_relI)
    unfolding ial_rel1_def in_br_conv aial_length_def ial_invar_def
    apply (auto split: if_splits)
    by (meson ial_invar.intro ial_invar.l_len le_imp_less_Suc)
  
  
  definition aial_index :: "aial \<Rightarrow> nat \<Rightarrow> nat nres" where
    "aial_index \<equiv> \<lambda>(l,qp) k. do {
      ASSERT (k\<in>set l);
      i \<leftarrow> mop_list_get qp k;
      ASSERT (i\<noteq>None);
      RETURN (the i)
    }"

  lemma aial_index_refine: 
    "(uncurry aial_index, uncurry mop_list_index) \<in> 
      [\<lambda>(l,k). k\<in>set l]\<^sub>f ial_rel1 maxsize \<times>\<^sub>r nat_rel \<rightarrow> \<langle>nat_rel\<rangle>nres_rel"  
    apply (intro fun_relI nres_relI frefI)
    unfolding ial_rel1_def
  proof (clarsimp simp:  in_br_conv)
    fix l qp k
    assume "ial_invar maxsize l qp"
    then interpret ial_invar maxsize l qp .

    assume "k\<in>set l"
    then show "aial_index (l,qp) k \<le> RETURN (index l k)"
      unfolding aial_index_def
      apply (refine_vcg)
      by (auto simp: qp_def)
  qed
  
  definition aial_butlast :: "aial \<Rightarrow> aial nres" where
    "aial_butlast \<equiv> \<lambda>(l,qp). do {
      ASSERT (l\<noteq>[]);
      len \<leftarrow> mop_list_length l;
      k \<leftarrow> mop_list_get l (len - 1);
      l \<leftarrow> mop_list_butlast l;
      qp \<leftarrow> mop_list_set qp k None;
      RETURN (l,qp)
    }"

  lemma aial_butlast_refine: "(aial_butlast, mop_list_butlast) \<in> ial_rel1 maxsize \<rightarrow> \<langle>ial_rel1 maxsize\<rangle>nres_rel"  
    apply (intro fun_relI nres_relI)
    unfolding ial_rel1_def
  proof (clarsimp simp: in_br_conv simp del: mop_list_butlast_alt)
    fix l qp
    assume "ial_invar maxsize l qp"
    then interpret ial_invar maxsize l qp .

    {
      assume A: "l\<noteq>[]"
      have "ial_invar (length qp) (butlast l) (qp[l ! (length l - Suc 0) := None])"
        apply standard
        apply clarsimp_all
        apply (auto simp: distinct_butlast) []
        using l_set apply (auto dest: in_set_butlastD) []
        using qp_def A l_distinct
        apply (auto simp: nth_list_update neq_Nil_rev_conv index_append simp del: l_distinct)
        done
    } note aux1=this

    show "aial_butlast (l, qp) \<le> \<Down> (br fst (uncurry (ial_invar maxsize))) (mop_list_butlast l)"
      unfolding aial_butlast_def mop_list_butlast_alt
      apply refine_vcg
      apply (clarsimp_all simp: in_br_conv aux1)
      done
  qed    


  definition aial_append :: "aial \<Rightarrow> nat \<Rightarrow> aial nres" where
    "aial_append \<equiv> \<lambda>(l,qp) k. do {
      ASSERT (k<length qp \<and> k\<notin>set l \<and> length l < length qp);
      len \<leftarrow> mop_list_length l;
      l \<leftarrow> mop_list_append l k;
      qp \<leftarrow> mop_list_set qp k (Some len);
      RETURN (l,qp)
    }"

  lemma aial_append_refine: 
    "(uncurry aial_append,uncurry mop_list_append) \<in> 
      [\<lambda>(l,k). k<maxsize \<and> k\<notin>set l]\<^sub>f ial_rel1 maxsize \<times>\<^sub>r nat_rel \<rightarrow> \<langle>ial_rel1 maxsize\<rangle>nres_rel"
    apply (intro frefI nres_relI)  
    unfolding ial_rel1_def
  proof (clarsimp simp: in_br_conv)
    fix l qp k
    assume KLM: "k<maxsize" and KNL: "k\<notin>set l"
    assume "ial_invar maxsize l qp"
    then interpret ial_invar maxsize l qp .
  
    from KLM have KLL: "k<length qp" by simp
  
    note distinct_card[OF l_distinct, symmetric]
    also from KNL l_set have "set l \<subseteq> {0..<k} \<union> {Suc k..<length qp}"
      by (auto simp: nat_less_le)
    from card_mono[OF _ this] have "card (set l) \<le> card \<dots>"
      by simp
    also note card_Un_le
    also have "card {0..<k} + card {Suc k..<length qp} = k + (length qp - Suc k)" 
      by simp
    also have "\<dots> < length qp" using KLL by simp
    finally have LLEN: "length l < length qp" .
  
    have aux1[simp]: "ial_invar (length qp) (l @ [k]) (qp[k := Some (length l)])"
      apply standard
      apply (clarsimp_all simp: KNL KLL)
      using KLL apply (auto simp: Suc_le_eq LLEN) []
      apply (auto simp: index_append KNL nth_list_update')
      apply (simp add: qp_def)
      apply (simp add: qp_def)
      done
  
    show "aial_append (l, qp) k \<le> \<Down> (br fst (uncurry (ial_invar maxsize))) (RETURN (l@[k]))"
      unfolding aial_append_def mop_list_append_def
      apply refine_vcg
      apply (clarsimp_all simp: in_br_conv KLL KNL LLEN)
      done
  qed    
  
  
  definition aial_get :: "aial \<Rightarrow> nat \<Rightarrow> nat nres" where
    "aial_get \<equiv> \<lambda>(l,qp) i. mop_list_get l i"

  lemma aial_get_refine: "(aial_get,mop_list_get) \<in> ial_rel1 maxsize \<rightarrow> nat_rel \<rightarrow> \<langle>nat_rel\<rangle>nres_rel"  
    apply (intro fun_relI nres_relI)
    unfolding aial_get_def ial_rel1_def mop_list_get_def in_br_conv
    apply refine_vcg
    apply clarsimp_all
    done

    
  definition aial_contains :: "nat \<Rightarrow> aial \<Rightarrow> bool nres" where
    "aial_contains \<equiv> \<lambda>k (l,qp). do {
      ASSERT (k<length qp);
      i \<leftarrow> mop_list_get qp k;
      RETURN (i\<noteq>None)
    }"

  lemma aial_contains_refine: "(uncurry aial_contains,uncurry mop_list_contains) 
    \<in> [\<lambda>(k,_). k<maxsize]\<^sub>f (nat_rel \<times>\<^sub>r ial_rel1 maxsize) \<rightarrow> \<langle>bool_rel\<rangle>nres_rel"  
    apply (intro frefI nres_relI)
    unfolding ial_rel1_def
  proof (clarsimp simp: in_br_conv)
    fix l qp k
    assume A: "k<maxsize"
    assume "ial_invar maxsize l qp"
    then interpret ial_invar maxsize l qp .
    

    show "aial_contains k (l, qp) \<le> RETURN (k\<in>set l)"
      unfolding aial_contains_def
      apply refine_vcg
      using A
      by (auto simp: l_len qp_def split: if_split_asm)
      
  qed    
      

  type_synonym 'l ial = "('l,'l word) marl \<times> 'l word ptr"
  
  context
    fixes M :: nat
    defines "M \<equiv> max_snat (LENGTH ('l::len2))"
  begin
  
    abbreviation "ial2_assn N 
      \<equiv> marl_assn' TYPE('l) (snat_assn' TYPE('l)) N \<times>\<^sub>a array_assn (snat_option_assn' TYPE('l))"
      
    private abbreviation (input) "idx_assn \<equiv> snat_assn' TYPE('l)"
    
    definition ial_assn :: "_ \<Rightarrow> _ \<Rightarrow> 'l ial \<Rightarrow> _" where "ial_assn N \<equiv> hr_comp (hr_comp (ial2_assn N) (ial_rel1 N)) (\<langle>nbn_rel N\<rangle>list_rel)"
    lemmas [fcomp_norm_unfold] = ial_assn_def[symmetric]

    (* TODO: Move *)
    lemma list_rel_below_id_ext: "A\<subseteq>Id \<Longrightarrow> \<langle>A\<rangle>list_rel \<subseteq> Id"
      by (metis list_rel_id list_rel_mono)
      
    lemma b_rel_below: "b_rel R \<Phi> \<subseteq> R" by (simp add: b_rel_def)
    
    lemma br_comp_b_rel_Id_conv: "br \<alpha> I O b_rel Id \<Phi> = br \<alpha> (\<lambda>x. I x \<and> \<Phi> (\<alpha> x))"
      by (auto simp: in_br_conv)
      
    find_theorems "?x = ?y" "_\<in>?x \<longleftrightarrow> _\<in>?y"  
      
    lemma b_rel_Id_list_rel_conv: "\<langle>b_rel Id \<Phi>\<rangle>list_rel = b_rel Id (\<lambda>xs. \<forall>x\<in>set xs. \<Phi> x)"  
      apply (clarsimp simp: set_eq_iff)
      subgoal for xs ys
        apply (induction xs arbitrary: ys)
        subgoal by auto
        subgoal for x xs ys by (cases ys) auto
        done  
      done
      
    
    lemma ial_rel1_comp_nbn_rel[fcomp_norm_unfold, simp]: "ial_rel1 N O \<langle>nbn_rel N\<rangle>list_rel = ial_rel1 N"
      apply (clarsimp simp: ial_rel1_def in_br_conv; safe; clarsimp simp: in_br_conv)
      subgoal using list_rel_below_id_ext[OF b_rel_below] by auto []
      subgoal for a b  
        apply (simp add: b_rel_Id_list_rel_conv br_comp_b_rel_Id_conv in_br_conv)
        by (metis (full_types) ial_invar.l_set_simp ial_invar_def)
      done  
        
    
    
    lemma ial_assn_fold'[fcomp_norm_unfold]: "hrr_comp nat_rel
                        (hrr_comp nat_rel (\<lambda>N. marl_assn' TYPE('l) snat_assn N \<times>\<^sub>a array_assn snat.option_assn)
                          ial_rel1)
                        (\<lambda>x. \<langle>nat_rel\<rangle>list_rel) = ial_assn"
      unfolding ial_assn_def
      by (auto simp: fun_eq_iff hrr_comp_nondep hr_comp_assoc)
    
    abbreviation "ial_assn' TYPE('l) N \<equiv> ial_assn N"

    
    sepref_definition ial_empty_impl [llvm_code]
      is aial_empty :: "idx_assn\<^sup>k \<rightarrow>\<^sub>a\<^sub>d ial2_assn"
      unfolding aial_empty_def
      supply [simp] = snat_rel_imp_less_max_snat
      by sepref
        
    definition [simp]: "ial_empty_aux (N::nat) \<equiv> op_list_empty"
    sepref_decl_op ial_empty: ial_empty_aux :: "nat_rel \<rightarrow> \<langle>A\<rangle>list_rel" .
    lemma ial_fold_custom_empty:
      "[] = op_ial_empty N"
      "op_list_empty = op_ial_empty N"
      "mop_list_empty = mop_ial_empty N"
      by auto
    
    lemma aial_empty_refine': 
      "(aial_empty, RETURN o op_ial_empty) \<in> nat_rel \<rightarrow>\<^sub>f\<^sub>d (\<lambda>N. \<langle>ial_rel1 N\<rangle>nres_rel)"
      apply (rule frefI)
      using aial_empty_refine
      by auto

    sepref_decl_impl ial_empty_impl.refine[FCOMP aial_empty_refine'] uses op_ial_empty.fref[where A="Id"] .
    
    sepref_definition ial_swap_impl [llvm_code] is "uncurry2 aial_swap" :: "(ial2_assn N)\<^sup>d*\<^sub>aidx_assn\<^sup>k*\<^sub>aidx_assn\<^sup>k \<rightarrow>\<^sub>a ial2_assn N"
      unfolding aial_swap_def
      by sepref
    sepref_decl_impl (ismop) ial_swap_impl.refine[FCOMP aial_swap_refine, of N N for N] uses mop_list_swap.fref[where A="nbn_rel N"] .
      
    sepref_definition ial_length_impl [llvm_inline] is "aial_length" :: "(ial2_assn N)\<^sup>k \<rightarrow>\<^sub>a idx_assn"
      unfolding aial_length_def
      by sepref
    sepref_decl_impl (ismop) ial_length_impl.refine[FCOMP aial_length_refine, of N N for N] uses mop_list_length.fref[where A="nbn_rel N"] .
              
    sepref_definition ial_index_impl [llvm_inline] is "uncurry aial_index" :: "(ial2_assn N)\<^sup>k *\<^sub>a idx_assn\<^sup>k \<rightarrow>\<^sub>a idx_assn"
      unfolding aial_index_def
      by sepref
      
    context 
      (*notes snatb_rel_def[symmetric, fcomp_norm_unfold] *)
    begin  
      sepref_decl_impl (ismop) ial_index_impl.refine[FCOMP aial_index_refine, of N N for N] 
      uses mop_list_index.fref[where A="nbn_rel N"]
      .
    end  
    
      
    sepref_definition ial_butlast_impl [llvm_code] is "aial_butlast" :: "(ial2_assn N)\<^sup>d \<rightarrow>\<^sub>a ial2_assn N"
      unfolding aial_butlast_def
      apply (annot_snat_const "TYPE('l)")
      by sepref
    sepref_decl_impl (ismop) ial_butlast_impl.refine[FCOMP aial_butlast_refine, of N N for N] 
      uses mop_list_butlast.fref[where A="nbn_rel N"] .
    
    private lemma aial_append_impl_aux: "((l, qp), l') \<in> ial_rel1 maxsize \<Longrightarrow> l'=l \<and> maxsize = length qp"
      unfolding ial_rel1_def
      by (clarsimp simp: in_br_conv ial_invar.maxsize_eq[symmetric])
    
    sepref_definition ial_append_impl [llvm_code] is "uncurry aial_append" :: "[\<lambda>(lqp,_). lqp\<in>Domain (ial_rel1 N)]\<^sub>a (ial2_assn N)\<^sup>d *\<^sub>a idx_assn\<^sup>k \<rightarrow> ial2_assn N"
      unfolding aial_append_def
      supply [dest!] = aial_append_impl_aux
      by sepref
    
    lemmas ial_append_impl_refine_aux = ial_append_impl.refine[of N, FCOMP aial_append_refine[of N]] for N

    private lemma append_fref': "(uncurry mop_list_append, uncurry mop_list_append) \<in> \<langle>nbn_rel N\<rangle>list_rel \<times>\<^sub>r nbn_rel N \<rightarrow>\<^sub>f \<langle>\<langle>nbn_rel N\<rangle>list_rel\<rangle>nres_rel"  
      by (rule mop_list_append.fref)
    
    (* TODO: Move *)            
    lemma right_unique_inv[relator_props]: "IS_LEFT_UNIQUE R \<Longrightarrow> IS_RIGHT_UNIQUE (R\<inverse>)" 
      by (simp add: IS_LEFT_UNIQUE_def)
    lemma left_unique_inv[relator_props]: "IS_RIGHT_UNIQUE R \<Longrightarrow> IS_LEFT_UNIQUE (R\<inverse>)"
      by (simp add: IS_LEFT_UNIQUE_def)
      
    lemma left_unique_id[relator_props]: "IS_LEFT_UNIQUE Id" by (auto simp: IS_LEFT_UNIQUE_def) 

    context
      (*notes [fcomp_norm_unfold] = snatb_rel_def[symmetric]*)
    begin      
      sepref_decl_impl (ismop) ial_append_impl_refine_aux[where N = N] uses append_fref'[where N=N]
        apply parametricity
        apply simp
        apply simp
        by tagged_solver+
    
      sepref_definition ial_get_impl [llvm_inline] is "uncurry aial_get" :: "(ial2_assn N)\<^sup>k *\<^sub>a idx_assn\<^sup>k \<rightarrow>\<^sub>a idx_assn"
        unfolding aial_get_def by sepref
  
      sepref_decl_impl (ismop) ial_get: ial_get_impl.refine[FCOMP aial_get_refine, of N N for N] 
        uses mop_list_get.fref[where A="nbn_rel N"] .

      sepref_definition ial_contains_impl [llvm_code] is "uncurry aial_contains" :: "idx_assn\<^sup>k *\<^sub>a (ial2_assn N)\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
        unfolding aial_contains_def 
        by sepref
        
      private lemma list_contains_fref': 
        "(uncurry mop_list_contains, uncurry mop_list_contains) \<in> nbn_rel N \<times>\<^sub>r \<langle>nbn_rel N\<rangle>list_rel \<rightarrow>\<^sub>f \<langle>bool_rel\<rangle>nres_rel"  
        apply (rule mop_list_contains.fref)
        by tagged_solver+
        
      sepref_decl_impl (ismop) ial_contains_impl.refine[FCOMP aial_contains_refine, of N N]
        uses list_contains_fref'[where N=N]
        apply parametricity
        unfolding IS_BELOW_ID_def by auto

    end            
  end
  
  schematic_goal [sepref_frame_free_rules]: "MK_FREE (ial_assn N) (?fr)"
    unfolding ial_assn_def
    by sepref_dbg_side
  
end
