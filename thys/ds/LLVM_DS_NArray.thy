section \<open>Array with Potential Zero Size\<close>
theory LLVM_DS_NArray
imports "LLVM_DS_Array"
begin

  term array_assn

  type_synonym 'a narray = "'a ptr"
  
  definition "narray_assn \<equiv> mk_assn (\<lambda>xs p. case xs of [] \<Rightarrow> \<up>(p=null) | _ \<Rightarrow> \<upharpoonleft>array_assn xs p)"
  
  term array_new
  
  definition [llvm_inline]: 
    "narray_new TYPE('a::llvm_rep) n \<equiv> if n=signed_nat 0 then return null else array_new TYPE('a) n"

  thm array_new_rule_snat[no_vars]
  
  lemma narray_new_rule_snat[vcg_rules]: 
    "llvm_htriple (\<upharpoonleft>snat.assn n ni) (narray_new TYPE(_) ni) (\<upharpoonleft>narray_assn (replicate n init))"
    unfolding narray_assn_def narray_new_def
    supply [split] = list.split
    apply vcg_monadify
    apply vcg
    
    done

  (* TODO: From an abstract point of view, 
    it's a bad idea to split init by the simplifier! 
    Remove that from default setup!
  *)      
  lemma narray_assn_init_pure: "\<box> \<turnstile> \<upharpoonleft>narray_assn [] null"  
    unfolding narray_assn_def
    by (auto simp: sep_algebra_simps)
    
    
  thm array_nth_rule_snat[no_vars]  
    
  lemma narray_nth_rule[vcg_rules]: "llvm_htriple 
    (\<upharpoonleft>narray_assn xs p \<and>* \<upharpoonleft>snat.assn i ii \<and>* \<up>\<^sub>d(i < length xs)) 
    (array_nth p ii)
    (\<lambda>r. \<up>(r = xs ! i) \<and>* \<upharpoonleft>narray_assn xs p)"  
    unfolding narray_assn_def 
    apply (clarsimp split: list.split)
    apply vcg
    done
    
  thm array_upd_rule_snat[no_vars]  

  lemma narray_upd_rule_snat[vcg_rules]: "llvm_htriple 
    (\<upharpoonleft>narray_assn xs p \<and>* \<upharpoonleft>snat.assn i ii \<and>* \<up>\<^sub>d(i < length xs)) 
    (array_upd p ii x)
    (\<lambda>r. \<up>(r = p) \<and>* \<upharpoonleft>narray_assn (xs[i := x]) p)"
    unfolding narray_assn_def 
    apply (clarsimp split: list.splits nat.splits; intro allI impI conjI)
    apply vcg
    done
    
  definition [llvm_code]: "narray_free p \<equiv> if p=null then return () else array_free p"
  
  thm array_free_rule[no_vars]
  
  lemma narray_free_rule[vcg_rules]: 
    "llvm_htriple (\<upharpoonleft>narray_assn xs p) (narray_free p) (\<lambda>_. \<box>)"
    unfolding narray_assn_def narray_free_def
    apply (cases xs; clarsimp)
    apply vcg
    done


  lemma narrayset_rule_snat[vcg_rules]: "llvm_htriple 
    (\<upharpoonleft>narray_assn dst dsti ** \<upharpoonleft>snat.assn n ni ** \<up>\<^sub>d(n\<le>length dst))
    (arrayset dsti c ni)
    (\<lambda>_. \<upharpoonleft>narray_assn (replicate n c @ drop n dst) dsti)"  
    unfolding narray_assn_def
    apply (cases dst; clarsimp split: list.splits)
    supply [vcg_rules] = arrayset_zerosize_rule
    by vcg
        
  definition [llvm_code]: "narray_new_init n (c::'a::llvm_rep) \<equiv> doM { 
    r \<leftarrow> narray_new TYPE('a) n; 
    arrayset r c n;
    return r
  }"
  
  lemma narray_new_init_rule[vcg_rules]: "llvm_htriple   
    (\<upharpoonleft>snat.assn n ni) 
    (narray_new_init ni c) 
    (\<lambda>r. \<upharpoonleft>narray_assn (replicate n c) r)"
    unfolding narray_new_init_def
    by vcg 
    
  lemma arraycpy_0_rl:
    "llvm_htriple (\<upharpoonleft>snat.assn 0 ni) (arraycpy dsti srci ni) (\<lambda>_. \<box>)"  
    unfolding arraycpy_def
    apply (subst llc_while_unfold)
    apply vcg_monadify
    apply vcg'
    done
    
  lemma narraycpy_rule_snat[vcg_rules]: 
    "llvm_htriple 
      (\<upharpoonleft>narray_assn dst dsti ** \<upharpoonleft>narray_assn src srci ** \<upharpoonleft>snat.assn n ni ** \<up>\<^sub>d(n\<le>length src \<and> n\<le>length dst))
      (arraycpy dsti srci ni)
      (\<lambda>_. \<upharpoonleft>narray_assn (take n src @ drop n dst) dsti ** \<upharpoonleft>narray_assn src srci)"
    unfolding narray_assn_def
    apply (cases dst; cases src; simp)
    supply [vcg_rules] = arraycpy_0_rl
    apply vcg
    apply (clarsimp split: list.splits)
    apply vcg
    done

  
  definition [llvm_code]: "array_grow newsz oldsz src \<equiv> doM {
    dst \<leftarrow> narray_new TYPE(_) newsz;
    arraycpy dst src oldsz;
    narray_free src;
    return dst
  }"  
  
  lemma narray_grow_rule_snat[vcg_rules]: "llvm_htriple 
    (\<upharpoonleft>narray_assn src srci ** \<upharpoonleft>snat.assn newsz newszi ** \<upharpoonleft>snat.assn oldsz oldszi ** \<up>(oldsz \<le> length src \<and> oldsz \<le> newsz))
    (array_grow newszi oldszi srci)
    (\<lambda>dsti. \<upharpoonleft>narray_assn (take oldsz src@replicate (newsz - oldsz) init) dsti)"
    unfolding array_grow_def
    by vcg
      
      
  definition [llvm_code]: "example1 (n::64 word) \<equiv> doM {
    a \<leftarrow> narray_new TYPE(8 word) n;
    array_upd a (1::64 word) 42;
    narray_free a
  }"  
    
  export_llvm (debug) example1 (* is "example1" file "exampel1.ll"*)
    
  
  
  
subsection \<open>Array Slices\<close>    

context begin

  interpretation llvm_prim_mem_setup .
    
  definition "array_base_assn \<equiv> mk_assn (\<lambda>n p. if n=0 then \<up>(p=null) else ll_malloc_tag (int n) p)"

  definition "array_slice_assn \<equiv> mk_assn (\<lambda>xs p. 
    if xs=[] then \<box> 
    else \<upharpoonleft>(ll_range {0..<int (length xs)}) ((!) xs o nat) p
  )"

  lemma array_slice_empty[sep_algebra_simps]: 
    "\<upharpoonleft>array_slice_assn [] p = \<box>"
    "\<upharpoonleft>array_slice_assn xs null = \<up>(xs=[])"
    unfolding array_slice_assn_def
    by (auto simp add: sep_algebra_simps ll_range_def)
  
  lemma array_assn_split: "\<upharpoonleft>narray_assn xs p = (\<upharpoonleft>array_slice_assn xs p ** \<upharpoonleft>array_base_assn (length xs) p)"
    unfolding array_assn_def narray_assn_def array_slice_assn_def array_base_assn_def
    by (auto simp: sep_algebra_simps split: list.split)
  
  lemma array_slice_split_aux: "{0..<i + j} = {0..<i} \<union> {i..<i+j}" if "i\<ge>0" "j\<ge>0" for i j :: int
    using that by auto
    
    
  lemma ll_range_shift:
    "\<upharpoonleft>(ll_range {l+ofs..<h+ofs}) f p = \<upharpoonleft>(ll_range {l..<h}) (\<lambda>i. f (i+ofs)) (p+\<^sub>aofs)"
  proof -
    have "(\<Union>*i\<in>{l + ofs..<h + ofs}. \<upharpoonleft>ll_pto (f i) (p +\<^sub>a i)) = (\<Union>*i\<in>((+)ofs)`{l..<h}. \<upharpoonleft>ll_pto (f i) (p +\<^sub>a i))" 
      by simp
    also have "\<dots> = (\<Union>*x\<in>{l..<h}. \<upharpoonleft>ll_pto (f (x + ofs)) (p +\<^sub>a (ofs + x)))"  
      apply (subst sep_set_img_map)
      apply (simp_all add: algebra_simps)
      done
    finally show ?thesis
      apply (simp add: ll_range_def)
      apply (cases "abase p"; simp add: sep_algebra_simps)
      done
  qed    
    
  (* TODO: Move *)
  lemma ll_range_empty[sep_algebra_simps]: "\<upharpoonleft>(ll_range {}) f p = \<up>(abase p)" unfolding ll_range_def by (auto)
  
  (* TODO: Move *)
  lemma ll_range_no_base[sep_algebra_simps]: "\<not>abase p \<Longrightarrow> \<upharpoonleft>(ll_range I) f p = sep_false"
    unfolding ll_range_def by (auto)
  
    
  lemma array_slice_assn_split: "\<upharpoonleft>array_slice_assn (xs\<^sub>1@xs\<^sub>2) p = (\<upharpoonleft>array_slice_assn xs\<^sub>1 p ** \<upharpoonleft>array_slice_assn xs\<^sub>2 (p +\<^sub>a int (length xs\<^sub>1)))"  
  proof -

    have 1: "\<upharpoonleft>(ll_range {0..<int (length xs\<^sub>1)}) (\<lambda>i. (xs\<^sub>1 @ xs\<^sub>2) ! nat i) p 
      = \<upharpoonleft>(ll_range {0..<int (length xs\<^sub>1)}) (\<lambda>i. xs\<^sub>1 ! nat i) p"
      apply (rule ll_range_cong)
      apply auto
      done
      
    have "\<upharpoonleft>(ll_range {int (length xs\<^sub>1)..<int (length xs\<^sub>1) + int (length xs\<^sub>2)}) (\<lambda>x. (xs\<^sub>1 @ xs\<^sub>2) ! nat x) p
      = \<upharpoonleft>(ll_range {0+int (length xs\<^sub>1)..<int (length xs\<^sub>2) + int (length xs\<^sub>1)}) (\<lambda>x. (xs\<^sub>1 @ xs\<^sub>2) ! nat x) p"  
      by (simp add: algebra_simps)
    also have "\<dots> = \<upharpoonleft>(ll_range {0..<int (length xs\<^sub>2)}) (\<lambda>i. (xs\<^sub>1 @ xs\<^sub>2) ! nat (i + int (length xs\<^sub>1))) (p +\<^sub>a int (length xs\<^sub>1))"
      apply (subst ll_range_shift)
      ..
    also have "\<dots> = \<upharpoonleft>(ll_range {0..<int (length xs\<^sub>2)}) (\<lambda>i. xs\<^sub>2 ! nat i) (p +\<^sub>a int (length xs\<^sub>1))"
      apply (rule ll_range_cong)
      apply (auto simp: nth_append nat_add_distrib)
      done
    finally show ?thesis
      unfolding array_slice_assn_def
      apply (simp add: comp_def array_slice_split_aux ll_range_merge[symmetric] 1)
      apply (cases "abase p")
      apply (auto simp: sep_algebra_simps)
      done
    
  qed    

  lemma array_slice_assn_cnv_range_upd:  
    "i<length xs \<Longrightarrow> \<upharpoonleft>array_slice_assn (xs[i:=x]) p = (\<upharpoonleft>(ll_range {0..<int (length xs)}) (((!) xs \<circ> nat)(int i := x)) p)"
    unfolding array_slice_assn_def
    apply (simp add: sep_algebra_simps)
    apply (rule ll_range_cong)
    by auto
      

  lemma array_slice_nth_rule_snat[vcg_rules]: "llvm_htriple 
    (\<upharpoonleft>array_slice_assn xs p ** \<upharpoonleft>snat.assn i ii ** \<up>\<^sub>d(i<length xs))
    (array_nth p ii)
    (\<lambda>r. \<up>(r = xs!i) ** \<upharpoonleft>array_slice_assn xs p)"
    unfolding array_nth_def array_slice_assn_def snat.assn_def
    supply [simp] = cnv_snat_to_uint and [simp del] = nat_uint_eq
    by vcg
    
    
  lemma array_slice_rule_snat[vcg_rules]: "llvm_htriple
    (\<upharpoonleft>array_slice_assn xs p ** \<upharpoonleft>snat.assn i ii ** \<up>\<^sub>d(i<length xs))
    (array_upd p ii x)
    (\<lambda>r. \<up>(r=p) ** \<upharpoonleft>array_slice_assn (xs[i:=x]) p)"
    apply (cases "i<length xs") 
    subgoal
      apply (subst array_slice_assn_cnv_range_upd; simp)
      unfolding array_upd_def array_slice_assn_def snat.assn_def
      supply [simp] = cnv_snat_to_uint and [simp del] = nat_uint_eq
      supply [fri_rules] = fri_abs_cong_rl
      apply vcg
      done
    subgoal by vcg  
    done
    
    
end  
  
  
end
