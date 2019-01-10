theory LLVM_Examples
imports LLVM_Shallow_RS
begin

interpretation llvm_prim_setup .


definition pure_rel :: "(_\<Rightarrow>_\<Rightarrow>bool) \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> bool" ("\<flat>_" [1000] 1000) where "\<flat>R i a \<equiv> R i a"
definition pure_rel_assn ("\<upharpoonleft>_" [1000] 1000) where "\<upharpoonleft>R a b \<equiv> \<up>\<flat>R a b"

lemma [fri_pure_erules]: "\<flat>R a b \<longrightarrow> \<box> \<turnstile> \<upharpoonleft>R a b"
  by (auto simp: sep_algebra_simps pure_rel_assn_def)


definition "uint_rel i a \<equiv> i = uint a"
definition "sint_rel i a \<equiv> i = sint a"
definition "unat_rel i a \<equiv> i = unat a"

definition [llvm_inline]: "ll_add' \<equiv> ll_add"
definition [llvm_inline]: "ll_icmp_ule' \<equiv> ll_icmp_ule"
definition [llvm_inline]: "ll_icmp_ne' \<equiv> ll_icmp_ne"

lemma [vcg_rules]:
  fixes w\<^sub>1 w\<^sub>2 :: "'a::len word"
  shows "WBOUNDS (i\<^sub>1+i\<^sub>2 \<in> uints LENGTH('a)) \<Longrightarrow> llvm_htriple (\<upharpoonleft>uint_rel i\<^sub>1 w\<^sub>1 ** \<upharpoonleft>uint_rel i\<^sub>2 w\<^sub>2) (ll_add' w\<^sub>1 w\<^sub>2) (\<lambda>r. \<upharpoonleft>uint_rel (i\<^sub>1+i\<^sub>2) r)"
  unfolding vcg_tag_defs ll_add'_def  pure_rel_assn_def
  apply vcg'
  apply (auto simp: uints_num uint_rel_def pure_rel_def)
  apply uint_arith
  done 

lemma [vcg_rules]:
  fixes w\<^sub>1 w\<^sub>2 :: "'a::len word"
  shows "WBOUNDS (i\<^sub>1+i\<^sub>2 \<in> unats LENGTH('a)) \<Longrightarrow> llvm_htriple (\<upharpoonleft>unat_rel i\<^sub>1 w\<^sub>1 ** \<upharpoonleft>unat_rel i\<^sub>2 w\<^sub>2) (ll_add' w\<^sub>1 w\<^sub>2) (\<lambda>r.  \<upharpoonleft>unat_rel (i\<^sub>1+i\<^sub>2) r)"
  unfolding vcg_tag_defs ll_add'_def   pure_rel_assn_def
  apply vcg'
  apply (auto simp: unats_def pure_rel_def unat_rel_def)
  apply unat_arith
  done 
  
  
lemma [vcg_rules]:
  fixes w\<^sub>1 w\<^sub>2 :: "'a::len word"
  shows "llvm_htriple (\<upharpoonleft>uint_rel i\<^sub>1 w\<^sub>1 ** \<upharpoonleft>uint_rel i\<^sub>2 w\<^sub>2) (ll_icmp_ule' w\<^sub>1 w\<^sub>2) (\<lambda>r. \<up>(r = from_bool (i\<^sub>1 \<le> i\<^sub>2)))"
  unfolding vcg_tag_defs ll_icmp_ule'_def pure_rel_assn_def
  apply vcg'
  apply (auto simp: uint_rel_def pure_rel_def)
  apply uint_arith
  done 

lemma [vcg_rules]:
  fixes w\<^sub>1 w\<^sub>2 :: "'a::len word"
  shows "llvm_htriple (\<upharpoonleft>uint_rel i\<^sub>1 w\<^sub>1 ** \<upharpoonleft>uint_rel i\<^sub>2 w\<^sub>2) (ll_icmp_ne' w\<^sub>1 w\<^sub>2) (\<lambda>r. \<up>(r = from_bool (i\<^sub>1 \<noteq> i\<^sub>2)))"
  unfolding vcg_tag_defs ll_icmp_ne'_def   pure_rel_assn_def
  apply vcg'
  apply (auto simp: uint_rel_def pure_rel_def)
  apply uint_arith
  done 

definition unsigned :: "'a::len word \<Rightarrow> 'a word" where [llvm_inline]: "unsigned x \<equiv> x"  
definition signed :: "'a::len word \<Rightarrow> 'a word" where [llvm_inline]: "signed x \<equiv> x"  
  
lemma [fri_safe_intro_rules]: 
  "\<box> \<turnstile> \<upharpoonleft>sint_rel 0 (signed 0)" 
  "PRECOND (WBOUNDS (LENGTH('a)>1)) \<Longrightarrow> \<box> \<turnstile> \<upharpoonleft>sint_rel 1 (signed (1::'a::len word))" 
  unfolding vcg_tag_defs
  by (auto simp: entails_def sint_rel_def pure_rel_def pure_rel_assn_def signed_def sep_algebra_simps)

lemma [fri_safe_intro_rules]: 
  "\<box> \<turnstile> \<upharpoonleft>uint_rel 0 (unsigned 0)" 
  "\<box> \<turnstile> \<upharpoonleft>uint_rel 1 (unsigned (1::'a::len word))" 
  by (auto simp: entails_def uint_rel_def pure_rel_def  pure_rel_assn_def unsigned_def sep_algebra_simps) 

lemma [fri_safe_intro_rules]: 
  "\<box> \<turnstile> \<upharpoonleft>unat_rel 0 (unsigned 0)" 
  "\<box> \<turnstile> \<upharpoonleft>unat_rel 1 (unsigned (1::'a::len word))" 
  by (auto simp: entails_def unat_rel_def pure_rel_def pure_rel_assn_def unsigned_def sep_algebra_simps) 
    
  


(* TODO: Move *)
definition max_unat :: "nat \<Rightarrow> nat" where "max_unat n \<equiv> 2^n"  
abbreviation (input) "min_uint \<equiv> 0::int"
definition max_uint :: "nat \<Rightarrow> int" where "max_uint n \<equiv> 2^n"  

definition min_sint :: "nat \<Rightarrow> int" where "min_sint n \<equiv> -(2^(n-1))"
definition max_sint :: "nat \<Rightarrow> int" where "max_sint n \<equiv> 2^(n-1)"  


lemma in_unats_conv[simp]: "x\<in>unats n \<longleftrightarrow> x<max_unat n" by (auto simp: unats_def max_unat_def)
  
lemma in_uints_conv[simp]: "x\<in>uints n \<longleftrightarrow> min_uint \<le> x \<and> x<max_uint n"
  by (auto simp: uints_num max_uint_def)

lemma in_sints_conv[simp]: "n\<noteq>0 \<Longrightarrow> x\<in>sints n \<longleftrightarrow> min_sint n \<le> x \<and> x<max_sint n"
  by (auto simp: sints_num min_sint_def max_sint_def)



definition "nth' s i \<equiv> if 0\<le>i \<and> i<int (length s) then s!nat i else 0"  
definition "string_assn s p \<equiv> \<up>(0\<notin>List.set s) ** ll_range ({0..int (length s)}) (nth' s) p "
  
lemma string_notZ[simp]: "0\<in>List.set s \<Longrightarrow> string_assn s p = sep_false"
  unfolding string_assn_def
  by (auto simp: sep_algebra_simps)

lemma string_abase[simp]: "\<not>abase p \<Longrightarrow> string_assn s p = sep_false"
  unfolding string_assn_def
  by (auto simp: sep_algebra_simps)
  
lemma string_extract[fri_extract0_rules]: "string_assn s p \<turnstile> \<up>(abase p \<and> 0\<notin>List.set s) ** sep_true"
  apply (cases "abase p \<and> 0\<notin>List.set s") by (auto simp: sep_algebra_simps entails_def)

lemma nth'_eq_Z_conv: "0\<notin>List.set s \<Longrightarrow> nth' s i = 0 \<longleftrightarrow> i<0 \<or> i\<ge>int (length s)"
  unfolding nth'_def by (auto simp add: in_set_conv_nth)
  
  
  
  
lemma load_string_rule[vcg_rules]:
  assumes "PRECOND (IDX (0\<le>p'-\<^sub>ap \<and> p'-\<^sub>ap \<le> int (length s)))"
  shows "llvm_htriple (string_assn s p ** \<up>(p~\<^sub>ap')) (ll_load p') (\<lambda>r. \<up>(r = nth' s (p'-\<^sub>ap)) ** string_assn s p)"
  using assms unfolding vcg_tag_defs string_assn_def
  apply vcg
  done  

lemma ofs_ptr_string_rule[vcg_rules]:
  assumes "PRECOND (IDX (p' -\<^sub>a p + sint i \<in> {0..int (length s)} ))"
  shows "llvm_htriple (string_assn s p ** \<up>(p~\<^sub>ap')) (ll_ofs_ptr p' i) (\<lambda>p''. \<up>(p''=p'+\<^sub>asint i) ** string_assn s p)"  
  using assms unfolding vcg_tag_defs string_assn_def
  by vcg
  
  
definition strlen :: "8 word ptr \<Rightarrow> 'a::len word llM" where "strlen p \<equiv> doM {
  (l,_) \<leftarrow> llc_while 
    (\<lambda>(l,p). doM { c \<leftarrow> ll_load p; ll_icmp_ne c 0}) 
    (\<lambda>(l,p). doM { p \<leftarrow> ll_ofs_ptr p (1::32 word); l \<leftarrow> ll_add' l (unsigned 1); return (l,p) })
    (unsigned 0,p);
  return l
}"


definition streq :: "8 word ptr \<Rightarrow> 8 word ptr \<Rightarrow> 1 word llM" where
  "streq s\<^sub>1 s\<^sub>2 \<equiv> doM {
    (s\<^sub>1,s\<^sub>2)\<leftarrow>llc_while 
      (\<lambda>(s\<^sub>1,s\<^sub>2). doM { x\<leftarrow>ll_load s\<^sub>1; y\<leftarrow>ll_load s\<^sub>2; return (from_bool (x\<noteq>0 \<and> x=y)) })
      (\<lambda>(s\<^sub>1,s\<^sub>2). doM { s\<^sub>1\<leftarrow>ll_ofs_ptr s\<^sub>1 (1::8 word); s\<^sub>2\<leftarrow>ll_ofs_ptr s\<^sub>2 (1::8 word); return (s\<^sub>1,s\<^sub>2) })
      (s\<^sub>1,s\<^sub>2);
  
    x\<leftarrow>ll_load s\<^sub>1; 
    y\<leftarrow>ll_load s\<^sub>2;  

    return (from_bool (x=y))
  }"
  
  
prepare_code_thms [llvm_code] streq_def
prepare_code_thms [llvm_code] strlen_def

export_llvm 
  streq is streq 
  "strlen :: _ \<Rightarrow> 64 word llM" is my_strlen
  file "string.ll"

lemma "int (length s\<^sub>0) + 1 < max_uint LENGTH ('a::len) \<Longrightarrow> llvm_htriple (string_assn s\<^sub>0 p\<^sub>0) (strlen p\<^sub>0 :: 'a word llM) (\<lambda>l. \<upharpoonleft>uint_rel (int (length s\<^sub>0)) l ** string_assn s\<^sub>0 p\<^sub>0)"
  unfolding strlen_def
  
  apply (rewrite annotate_llc_while[where
    I="\<lambda>(l,p) t. EXS i::int. \<upharpoonleft>uint_rel i l ** \<up>(p=p\<^sub>0 +\<^sub>a i \<and> 0\<le>i \<and> i\<le>int (length s\<^sub>0)) ** \<up>(t = (int (length s\<^sub>0) - i)) ** string_assn s\<^sub>0 p\<^sub>0"
    and R="measure nat"
  ])
  supply [simp] = nth'_eq_Z_conv
  apply vcg'
  done

lemma nth'_Nil[simp]: "nth' [] i = 0" by (auto simp: nth'_def)
lemma nth'_Z_iff[simp]: "0\<notin>List.set xs \<Longrightarrow> nth' xs 0 = 0 \<longleftrightarrow> xs=[]"
  by (cases xs) (auto simp: nth'_def neq_Nil_conv)
  
lemma nth'_Cons_iff: "0\<le>i \<Longrightarrow> nth' (x#xs) i = (if i=0 then x else nth' xs (i-1))"
  by (auto simp: nth'_def nat_diff_distrib')
  
lemma nth'_nth_conv: "0\<le>i \<Longrightarrow> i<int (length xs) \<Longrightarrow> nth' xs i = xs!nat i"
  by (auto simp: nth'_def)
    
  
lemma streq_aux: 
  assumes A: "0\<notin>List.set s\<^sub>1" "0\<notin>List.set s\<^sub>2"  
  shows "s\<^sub>1 = s\<^sub>2 \<longleftrightarrow> (\<forall>i\<in>{0..int (length s\<^sub>1)} \<inter> {0..int (length s\<^sub>2)}. nth' s\<^sub>1 i = nth' s\<^sub>2 i)"  
proof safe
  assume B: "\<forall>i\<in>{0..int (length s\<^sub>1)} \<inter> {0..int (length s\<^sub>2)}. nth' s\<^sub>1 i = nth' s\<^sub>2 i"

  consider "length s\<^sub>1 < length s\<^sub>2" | "length s\<^sub>1 = length s\<^sub>2" | "length s\<^sub>1 > length s\<^sub>2"
    using nat_neq_iff by blast
  hence "length s\<^sub>1 = length s\<^sub>2"
    apply cases
    using B
    apply (auto simp: A split: if_splits) 
    apply (metis assms(2) atLeastAtMost_iff less_irrefl not_le nth'_def nth'_eq_Z_conv of_nat_0_le_iff of_nat_less_iff)
    by (metis assms(1) atLeastAtMost_iff not_le nth'_def nth'_eq_Z_conv of_nat_less_0_iff of_nat_less_iff order_refl)
  
  moreover from B have "s\<^sub>1!i = s\<^sub>2!i" if "i<length s\<^sub>2" for i 
    using that
    apply (auto simp: nth'_nth_conv \<open>length s\<^sub>1 = length s\<^sub>2\<close>)
    by (metis (no_types, hide_lams) \<open>length s\<^sub>1 = length s\<^sub>2\<close> atLeastAtMost_iff int_nat_eq le_less nth'_def of_nat_0_le_iff of_nat_eq_iff of_nat_less_iff)
  ultimately show "s\<^sub>1 = s\<^sub>2" by (simp add: list_eq_iff_nth_eq)
qed    
  
  
lemma "LENGTH ('a::len)>1 
  \<Longrightarrow> llvm_htriple (string_assn s\<^sub>1 p\<^sub>1 ** string_assn s\<^sub>2 p\<^sub>2) (streq p\<^sub>1 p\<^sub>2) (\<lambda>r. \<up>(to_bool r \<longleftrightarrow> s\<^sub>1 = s\<^sub>2) ** string_assn s\<^sub>1 p\<^sub>1 ** string_assn s\<^sub>2 p\<^sub>2)"
proof -  
  
  have [simp]: "\<And>i. \<lbrakk>0 \<notin> list.set s\<^sub>1; 0 \<notin> list.set s\<^sub>2; 0 \<le> i;
            i \<le> int (length s\<^sub>1); int (length s\<^sub>1) \<noteq> i; nth' s\<^sub>1 (i) = nth' s\<^sub>2 (i)\<rbrakk>
           \<Longrightarrow> i + 1 \<le> int (length s\<^sub>2)"
    by (metis discrete le_less not_le nth'_eq_Z_conv)


  show ?thesis
  
  unfolding streq_def
  apply (rewrite annotate_llc_while[where I="\<lambda>(p\<^sub>1',p\<^sub>2') t. string_assn s\<^sub>1 p\<^sub>1 ** string_assn s\<^sub>2 p\<^sub>2 ** 
    \<up>(p\<^sub>1' ~\<^sub>a p\<^sub>1 \<and> p\<^sub>2' ~\<^sub>a p\<^sub>2 \<and> (let i=p\<^sub>1' -\<^sub>a p\<^sub>1 in i \<in> {0..int (length s\<^sub>1)} \<inter> {0..int (length s\<^sub>2)} \<and> p\<^sub>2' -\<^sub>a p\<^sub>2 = i \<and> (\<forall>j\<in>{0..<i}. nth' s\<^sub>1 j = nth' s\<^sub>2 j)) )
    ** \<up>(t = int (length s\<^sub>1) - (p\<^sub>1' -\<^sub>a p\<^sub>1))
  " and R="measure nat"])
  
  supply [simp] = Let_def nth'_eq_Z_conv streq_aux
  apply vcg
  done
qed  
    

definition [llvm_code]: "test3 (argc::32 word) (argv::8 word ptr ptr) \<equiv> doM {
  p \<leftarrow> ll_malloc TYPE(32 word) (30::32 word);
  p \<leftarrow> ll_ofs_ptr p (5::32 word);
  x \<leftarrow> ll_load p;
  x \<leftarrow> ll_add x 10;
  x \<leftarrow> ll_udiv x 4;
  x \<leftarrow> ll_add x argc;
  ll_store x p;
  x \<leftarrow> ll_load p;
  p \<leftarrow> ll_ofs_ptr p ((-5)::32 word);
  ll_free p;
  return x
}"

export_llvm test3 is main file "test3.ll"

lemma "llvm_htriple \<box> (test3 argc argv) (\<lambda>r. \<up>(r=2 + argc))"  
  unfolding test3_def
  apply vcg
  done  


definition "euclid (a::32 word) b \<equiv> doM {
  (a,b) \<leftarrow> llc_while 
    (\<lambda>(a,b) \<Rightarrow> ll_icmp_ne a b) 
    (\<lambda>(a,b) \<Rightarrow> doM {
      x \<leftarrow> ll_icmp_ule a b;
      llc_if x (doM {
        b \<leftarrow> ll_sub b a;
        return (a,b)
      }) (doM {
        a \<leftarrow> ll_sub a b;
        return (a,b)
      })
    })
    (a,b);
  return a
}"

prepare_code_thms [llvm_code] euclid_def

export_llvm euclid_raw_thms: euclid is euclid file "euclid.ll"


definition "test4 a b c \<equiv> doM {
  (a,b,c) \<leftarrow> llc_while 
    (\<lambda>(a,b,c). ll_icmp_eq a b) (\<lambda>(a,b,c). 
    doM {
      a \<leftarrow> return (a+b+c+1);
      b \<leftarrow> ll_sub b 1;
      c \<leftarrow> ll_add c b;
      return (a,b,c)
    })
    (a,b,c);
    
    return a
  }"

prepare_code_thms [llvm_code] test4_def

export_llvm test4_raw: "test4 :: 32 word \<Rightarrow> _"




thm test4_raw


thm euclid_raw_thms

value "run (euclid 126 86) llvm_empty_memory"

  
lemma gcd_diff1': "gcd (a::int) (b-a) = gcd a b"
  by (metis gcd.commute gcd_diff1)   

lemma "\<lbrakk> 0<a\<^sub>0; 0<b\<^sub>0 \<rbrakk> \<Longrightarrow> llvm_htriple \<box> (euclid a\<^sub>0 b\<^sub>0) (\<lambda>r. \<up>(uint r = gcd (uint a\<^sub>0) (uint b\<^sub>0)))"
  unfolding euclid_def
  apply (rewrite annotate_llc_while[where 
    I="\<lambda>(a,b) t. \<up>(t = (uint a + uint b)) ** \<up>(0<a \<and> 0<b \<and> gcd (uint a) (uint b) = gcd (uint a\<^sub>0) (uint b\<^sub>0))" 
    and R="measure nat"  
  ])
  apply vcg'
  apply (simp_all add: gcd_diff1 gcd_diff1' uint_arith_simps)
  done

  
  
definition "euclid2 (a::32 word) b \<equiv> doM {
  (a,b) \<leftarrow> llc_while 
    (\<lambda>(a,b) \<Rightarrow> ll_icmp_ne a b) 
    (\<lambda>(a,b) \<Rightarrow> doM {
      x \<leftarrow> ll_icmp_ule a b;
      llc_if x (return (a,b-a)) (return (a-b,b))
    })
    (a,b);
  return a
}"
  
  
prepare_code_thms [llvm_code] euclid2_def

export_llvm "euclid2" is euclid file "euclid2.ll"
  
  
lemma "\<lbrakk> 0<a\<^sub>0; 0<b\<^sub>0 \<rbrakk> \<Longrightarrow> llvm_htriple \<box> (euclid2 a\<^sub>0 b\<^sub>0) (\<lambda>r. \<up>(uint r = gcd (uint a\<^sub>0) (uint b\<^sub>0)))"
  unfolding euclid2_def
  apply (rewrite annotate_llc_while[where 
    I="\<lambda>(a,b) t. \<up>(t = (uint a + uint b)) ** \<up>(0<a \<and> 0<b \<and> gcd (uint a) (uint b) = gcd (uint a\<^sub>0) (uint b\<^sub>0))" 
    and R="measure nat"  
  ])
  apply vcg'
  apply (simp_all add: gcd_diff1 gcd_diff1' uint_arith_simps)
  done



end
