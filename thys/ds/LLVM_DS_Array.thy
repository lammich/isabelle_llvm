section \<open>Arrays\<close>
theory LLVM_DS_Array
imports LLVM_DS_Arith
begin

text \<open>Implementing Lists by Arrays\<close>

context begin

  interpretation llvm_prim_mem_setup .

  definition "array_assn \<equiv> mk_assn (\<lambda>xs p. 
    \<upharpoonleft>(ll_range {0..<int (length xs)}) ((!) xs o nat) p ** ll_malloc_tag (int (length xs)) p
  )"
  
  lemma array_assn_not_null[simp]: "\<upharpoonleft>array_assn xs null = sep_false"
    by (auto simp: array_assn_def)
  
  definition [llvm_inline]: "array_new TYPE('a::llvm_rep) n \<equiv> ll_malloc TYPE('a) n"
  definition [llvm_inline]: "array_free a \<equiv> ll_free a"
  definition [llvm_inline]: "array_nth a i \<equiv> doM { p \<leftarrow> ll_ofs_ptr a i; ll_load p }"
  definition [llvm_inline]: "array_upd a i x \<equiv> doM { p \<leftarrow> ll_ofs_ptr a i; ll_store x p; return a }"


  lemma ll_range_cong: "I=I' \<Longrightarrow> (\<And>i. i\<in>I' \<Longrightarrow> f i = f' i) \<Longrightarrow> p=p' 
    \<Longrightarrow> \<upharpoonleft>(ll_range I) f p = \<upharpoonleft>(ll_range I') f' p'"
    unfolding ll_range_def 
    by simp
  
  lemma array_assn_cnv_range_malloc: 
    "\<upharpoonleft>array_assn (replicate n init) p = (\<upharpoonleft>(ll_range {0..<int n}) (\<lambda>_. init) p ** ll_malloc_tag (int n) p)"  
    unfolding array_assn_def
    apply (simp add: sep_algebra_simps)
    apply (rule sep_conj_trivial_strip2)
    apply (rule ll_range_cong)
    by auto
  
  lemma array_assn_cnv_range_upd:  
    "\<upharpoonleft>array_assn (xs[i:=x]) p = (\<upharpoonleft>(ll_range {0..<int (length xs)}) (((!) xs \<circ> nat)(int i := x)) p ** ll_malloc_tag (int (length xs)) p)"
    unfolding array_assn_def
    apply (simp add: sep_algebra_simps)
    apply (rule sep_conj_trivial_strip2)
    apply (rule ll_range_cong)
    by auto
    

  lemma pos_sint_to_uint: "0 \<le> sint i \<Longrightarrow> sint i = uint i"  
    by (smt Suc_n_not_le_n Suc_pred bintrunc_mod2p int_mod_eq' len_gt_0 power_increasing_iff sint_range' uint_sint)
    
  lemma array_new_rule_sint[vcg_rules]: "llvm_htriple 
    (\<upharpoonleft>sint.assn n ni ** \<up>\<^sub>d(n>0)) 
    (array_new TYPE('a::llvm_rep) ni) 
    (\<upharpoonleft>array_assn (replicate (nat n) init))"
    unfolding array_new_def array_assn_cnv_range_malloc sint.assn_def
    supply [simp] = pos_sint_to_uint
    by vcg

  lemma array_new_rule_uint[vcg_rules]: "llvm_htriple 
    (\<upharpoonleft>uint.assn n ni ** \<up>\<^sub>d(n>0)) 
    (array_new TYPE('a::llvm_rep) ni) 
    (\<upharpoonleft>array_assn (replicate (nat n) init))"
    unfolding array_new_def array_assn_cnv_range_malloc uint.assn_def
    by vcg

  lemma array_new_rule_unat[vcg_rules]: "llvm_htriple 
    (\<upharpoonleft>unat.assn n ni ** \<up>\<^sub>d(n>0)) 
    (array_new TYPE('a::llvm_rep) ni) 
    (\<upharpoonleft>array_assn (replicate n init))"
    unfolding array_new_def array_assn_cnv_range_malloc unat.assn_def
    apply (simp add: )
    by vcg

  lemma array_new_rule_snat[vcg_rules]: "llvm_htriple 
    (\<upharpoonleft>snat.assn n ni ** \<up>\<^sub>d(n>0)) 
    (array_new TYPE('a::llvm_rep) ni) 
    (\<upharpoonleft>array_assn (replicate n init))"
    unfolding array_new_def array_assn_cnv_range_malloc snat.assn_def
    supply [simp] = cnv_snat_to_uint and [simp del] = nat_uint_eq
    by vcg
    
      
  lemma array_free_rule[vcg_rules]: "llvm_htriple (\<upharpoonleft>array_assn xs p) (array_free p) (\<lambda>_. \<box>)"
    unfolding array_free_def array_assn_def
    by vcg

  lemma array_cast_index: 
    assumes "uint (ii::'a::len word) < max_sint LENGTH('a)"  
    shows "sint ii = uint ii" "nat (uint ii) < n \<longleftrightarrow> uint ii < int n"
      "unat ii < n \<longleftrightarrow> uint ii < int n"
    using assms                                                                          
    by (simp_all add: max_sint_def msb_uint_big sint_eq_uint unat_def nat_less_iff del: nat_uint_eq)
    
  abbreviation (input) "in_range_nat i (ii::'a::len word) xs \<equiv> i<length xs \<and> int i<max_sint LENGTH('a)"  
  abbreviation (input) "in_range_uint i (ii::'a::len word) xs \<equiv> i<int (length xs) \<and> i<max_sint LENGTH('a)"

  lemma array_nth_rule_sint[vcg_rules]: "llvm_htriple 
    (\<upharpoonleft>array_assn xs p ** \<upharpoonleft>sint.assn i ii ** \<up>\<^sub>d(0\<le>i \<and> i<int (length xs)))
    (array_nth p ii)
    (\<lambda>r. \<up>(r = xs!nat i) ** \<upharpoonleft>array_assn xs p)"
    unfolding array_nth_def array_assn_def sint.assn_def
    by vcg

  lemma array_nth_rule_uint[vcg_rules]: "llvm_htriple 
    (\<upharpoonleft>array_assn xs p ** \<upharpoonleft>uint.assn i ii ** \<up>\<^sub>d(in_range_uint i ii xs))
    (array_nth p ii)
    (\<lambda>r. \<up>(r = xs!nat i) ** \<upharpoonleft>array_assn xs p)"
    unfolding array_nth_def array_assn_def uint.assn_def
    supply [simp] = array_cast_index
    by vcg
      
  lemma array_nth_rule_unat[vcg_rules]: "llvm_htriple 
    (\<upharpoonleft>array_assn xs p ** \<upharpoonleft>unat.assn i ii ** \<up>\<^sub>d(in_range_nat i ii xs))
    (array_nth p ii)
    (\<lambda>r. \<up>(r = xs!i) ** \<upharpoonleft>array_assn xs p)"
    unfolding array_nth_def array_assn_def unat.assn_def unat_def
    supply [simp] = array_cast_index
    by vcg

  lemma array_nth_rule_snat[vcg_rules]: "llvm_htriple 
    (\<upharpoonleft>array_assn xs p ** \<upharpoonleft>snat.assn i ii ** \<up>\<^sub>d(i<length xs))
    (array_nth p ii)
    (\<lambda>r. \<up>(r = xs!i) ** \<upharpoonleft>array_assn xs p)"
    unfolding array_nth_def array_assn_def snat.assn_def
    supply [simp] = cnv_snat_to_uint and [simp del] = nat_uint_eq
    by vcg
    
  lemma array_upd_rule_sint[vcg_rules]: "llvm_htriple
    (\<upharpoonleft>array_assn xs p ** \<upharpoonleft>sint.assn i ii ** \<up>\<^sub>d(0\<le>i \<and> i < int (length xs)))
    (array_upd p ii x)
    (\<lambda>r. \<up>(r=p) ** \<upharpoonleft>array_assn (xs[nat i:=x]) p)"
    unfolding array_assn_cnv_range_upd
    unfolding array_upd_def array_assn_def sint.assn_def
    supply [fri_rules] = fri_abs_cong_rl
    by vcg

  lemma array_upd_rule_uint[vcg_rules]: "llvm_htriple
    (\<upharpoonleft>array_assn xs p ** \<upharpoonleft>uint.assn i ii ** \<up>\<^sub>din_range_uint i ii xs)
    (array_upd p ii x)
    (\<lambda>r. \<up>(r=p) ** \<upharpoonleft>array_assn (xs[nat i:=x]) p)"
    unfolding array_assn_cnv_range_upd
    unfolding array_upd_def array_assn_def uint.assn_def
    supply [simp] = array_cast_index
    supply [fri_rules] = fri_abs_cong_rl
    by vcg
        
  lemma array_upd_rule_nat[vcg_rules]: "llvm_htriple
    (\<upharpoonleft>array_assn xs p ** \<upharpoonleft>unat.assn i ii ** \<up>\<^sub>din_range_nat i ii xs)
    (array_upd p ii x)
    (\<lambda>r. \<up>(r=p) ** \<upharpoonleft>array_assn (xs[i:=x]) p)"
    unfolding array_assn_cnv_range_upd
    unfolding array_upd_def array_assn_def unat.assn_def unat_def
    supply [simp] = array_cast_index
    supply [fri_rules] = fri_abs_cong_rl
    by vcg
    
  lemma array_upd_rule_snat[vcg_rules]: "llvm_htriple
    (\<upharpoonleft>array_assn xs p ** \<upharpoonleft>snat.assn i ii ** \<up>\<^sub>d(i<length xs))
    (array_upd p ii x)
    (\<lambda>r. \<up>(r=p) ** \<upharpoonleft>array_assn (xs[i:=x]) p)"
    unfolding array_assn_cnv_range_upd
    unfolding array_upd_def array_assn_def snat.assn_def
    supply [simp] = cnv_snat_to_uint and [simp del] = nat_uint_eq
    supply [fri_rules] = fri_abs_cong_rl
    apply vcg
    done

end    
    
subsection \<open>Basic Algorithms\<close>

subsubsection \<open>Array-Copy\<close>
definition "arraycpy dst src (n::'a::len2 word) \<equiv> 
  doM {
    llc_while 
      (\<lambda>i. ll_icmp_ult i n) 
      (\<lambda>i. doM { 
        x\<leftarrow>array_nth src i;
        array_upd dst i x;
        i\<leftarrow>ll_add i (signed_nat 1);
        return i
      }) (signed_nat 0);
    return ()
  }"

declare arraycpy_def[llvm_code]
  
export_llvm "arraycpy :: 8 word ptr \<Rightarrow> _ \<Rightarrow> 64 word \<Rightarrow> _" is "arraycpy"

(* TODO: Move / REMOVE?*)
lemma unat_not_msb_imp_less_max_sint: "x \<in> unat ` {w::'a::len word. \<not> msb w} \<Longrightarrow> int x < max_sint LENGTH('a)"
  by (auto simp: unat_def[abs_def] msb_uint_big max_sint_def simp del: nat_uint_eq)


lemma arraycpy_rule_snat[vcg_rules]: 
  "llvm_htriple 
    (\<upharpoonleft>array_assn dst dsti ** \<upharpoonleft>array_assn src srci ** \<upharpoonleft>snat.assn n ni ** \<up>\<^sub>d(n\<le>length src \<and> n\<le>length dst))
    (arraycpy dsti srci ni)
    (\<lambda>_. \<upharpoonleft>array_assn (take n src @ drop n dst) dsti ** \<upharpoonleft>array_assn src srci)"
  unfolding arraycpy_def
  apply (rewrite annotate_llc_while[where 
    I="\<lambda>ii t. EXS i dst'. \<upharpoonleft>snat.assn i ii ** \<upharpoonleft>array_assn dst' dsti ** \<upharpoonleft>array_assn src srci
      ** \<up>\<^sub>d(0\<le>i \<and> i\<le>n \<and> dst' = take i src @ drop i dst) ** \<up>\<^sub>a(t = n-i)"
    and R = "measure id"
      ])
  apply vcg_monadify
  apply vcg'
  apply (auto simp: list_update_append upd_conv_take_nth_drop take_Suc_conv_app_nth) 
  done

subsubsection \<open>Array-Set\<close>
    
definition arrayset :: "'b::llvm_rep ptr \<Rightarrow> 'b \<Rightarrow> 'a::len2 word \<Rightarrow> unit llM" where
  [llvm_code]: "arrayset dst c n \<equiv> doM {
    llc_while
      (\<lambda>i. ll_cmp (i<n))
      (\<lambda>i. doM {
        array_upd dst i c;
        let i=i+(signed_nat 1);
        return i
      }) (signed_nat 0);
    return ()
  }"  
  

(*declare arrayset_def[llvm_code]*)

export_llvm (debug) "arrayset :: 32 word ptr \<Rightarrow> 32 word \<Rightarrow> 64 word \<Rightarrow> _"

lemma arrayset_rule_snat[vcg_rules]: "llvm_htriple 
  (\<upharpoonleft>array_assn dst dsti ** \<upharpoonleft>snat.assn n ni ** \<up>\<^sub>d(n\<le>length dst))
  (arrayset dsti c ni)
  (\<lambda>_. \<upharpoonleft>array_assn (replicate n c @ drop n dst) dsti)"  
  unfolding arrayset_def
  apply (rewrite annotate_llc_while[where 
    I="\<lambda>ii t. EXS i dst'. \<upharpoonleft>snat.assn i ii ** \<upharpoonleft>array_assn dst' dsti 
      ** \<up>\<^sub>d(0\<le>i \<and> i\<le>n \<and> dst' = replicate i c @ drop i dst) ** \<up>\<^sub>a(t = n-i)"
    and R="measure id"  
  ])
  apply vcg_monadify
  apply vcg'
  apply (auto simp: nth_append list_update_append replicate_Suc_conv_snoc simp del: replicate_Suc)
  by (metis Cons_nth_drop_Suc less_le_trans list_update_code(2))
  
text \<open>Array-Set also works for zero-size, and any pointer, including \<open>null\<close>\<close>  
lemma arrayset_zerosize_rule: "llvm_htriple (\<upharpoonleft>snat.assn 0 ni) (arrayset p c ni) (\<lambda>_. \<box>)"  
  unfolding arrayset_def
  apply (rewrite annotate_llc_while[where I="\<lambda>ii _. EXS i. \<upharpoonleft>snat.assn i ii" and R="{}"])
  apply vcg_monadify
  apply vcg
  done
  

subsubsection \<open>Array-New-Init\<close>
  
definition "array_new_init n (c::'a::llvm_rep) \<equiv> doM { 
  r \<leftarrow> array_new TYPE('a) n; 
  arrayset r c n;
  return r
}"

lemma array_new_init_rule[vcg_rules]: "llvm_htriple   
  (\<upharpoonleft>snat.assn n ni ** \<up>\<^sub>d(n>0)) 
  (array_new_init ni c) 
  (\<lambda>r. \<upharpoonleft>array_assn (replicate n c) r)"
  unfolding array_new_init_def
  by vcg


end
