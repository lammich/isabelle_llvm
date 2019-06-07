section \<open>Array of Array Lists\<close>
theory Array_of_Array_List
imports LLVM_DS_Array_List
begin


subsection \<open>Arrays that own their Elements\<close>


  definition "idxe_map l i \<equiv> if i<length l then Some (l!i) else None"

  lemma idxe_map_empty[simp]: "idxe_map [] = Map.empty" unfolding idxe_map_def by auto
  
  lemma idxe_map_dom[simp]: "dom (idxe_map l) = {0..<length l}" unfolding idxe_map_def by (auto split: if_splits)
  
  lemma le_idxe_map_updI: "i<length l \<Longrightarrow> m \<subseteq>\<^sub>m idxe_map l \<Longrightarrow> m(i\<mapsto>l!i) \<subseteq>\<^sub>m idxe_map l"
    unfolding idxe_map_def map_le_def by (auto split: if_splits)
    
  lemma le_idxe_map_delD: "m \<subseteq>\<^sub>m idxe_map l \<Longrightarrow> m(i:=None) \<subseteq>\<^sub>m idxe_map (l[i:=x])"
    unfolding idxe_map_def map_le_def by (auto split: if_splits)
    
  lemma le_idxe_map_delD': "m \<subseteq>\<^sub>m idxe_map l \<Longrightarrow> m(i:=None) \<subseteq>\<^sub>m idxe_map l"
    unfolding idxe_map_def map_le_def by (auto split: if_splits)
    
  lemma le_idxe_mapD: "m \<subseteq>\<^sub>m idxe_map l \<Longrightarrow> i<length l \<Longrightarrow> m i = Some xi \<Longrightarrow> l!i = xi"  
    unfolding idxe_map_def map_le_def 
    apply (clarsimp split: if_splits) by (metis domI option.inject)
    
    
  definition "nao_assn A R \<equiv> mk_assn (\<lambda>xss a. EXS xs. 
       \<upharpoonleft>narray_assn xs a 
    ** \<up>(length xs = length xss) 
    ** \<up>(R \<subseteq>\<^sub>m idxe_map xs)
    ** (\<Union>*i\<in>{0..<length xss} - dom R. \<upharpoonleft>A (xss!i) (xs!i))  
  )"

  definition [llvm_inline]: "nao_new TYPE('a::llvm_rep) n \<equiv> narray_new TYPE('a) n"

  
  lemma nao_repl_init_aux: 
    assumes [fri_rules]: "\<box> \<turnstile> \<upharpoonleft>A x init"
    shows "\<box> \<turnstile> (\<Union>*i\<in>{0..<n::nat}. \<upharpoonleft>A x init)"  
    unfolding vcg_tag_defs
    apply (induction n)
    subgoal by simp
    subgoal for n 
    proof (simp add: atLeast0_lessThan_Suc del: replicate_Suc, goal_cases)
      case 1 note [fri_rules] = 1(1)
      show ?case by (rule ENTAILSD) vcg
    qed    
    done
  
  
  lemma nao_new_init_rl:
    assumes "\<box> \<turnstile> \<upharpoonleft>A x init"
    shows "llvm_htriple (\<upharpoonleft>snat.assn n ni) (nao_new TYPE('a::llvm_rep) ni) (\<lambda>a. \<upharpoonleft>(nao_assn A Map.empty) (replicate n x) a)"
    unfolding nao_assn_def nao_new_def
    supply [fri_rules] = nao_repl_init_aux[OF assms]
    by vcg

  definition [llvm_code, llvm_inline]: "nao_nth a i \<equiv> array_nth a i"  
  
  lemma nao_nth_aux: 
    assumes "i<length xs" "i\<notin>R"  
    shows "sep_set_img ({0..<length xs} - R) P 
        = (P i ** sep_set_img ({0..<length xs} - insert i R) P)"
  proof -
    from assms have 1: "{0..<length xs} - R = insert i ({0..<length xs} - insert i R)" by auto
    show ?thesis
      by (subst 1) auto
  qed    
  
  lemma ndomIff: "i\<notin>dom m \<longleftrightarrow> m i = None" by auto
  
  lemma nao_nth_rule[vcg_rules]: "llvm_htriple 
    (\<upharpoonleft>(nao_assn A R) xs a ** \<upharpoonleft>snat.assn i ii ** \<up>(i<length xs \<and> i\<notin>dom R)) 
    (nao_nth a ii) 
    (\<lambda>xi. \<upharpoonleft>(nao_assn A (R(i\<mapsto>xi))) xs a ** \<upharpoonleft>A (xs!i) xi)"
    unfolding nao_assn_def nao_nth_def
    supply fri_red_img[fri_red_rules]
    supply nao_nth_aux[simp]
    supply ndomIff[simp] le_idxe_map_updI[simp]
    by vcg
    
    
  definition [llvm_code, llvm_inline]: "nao_upd a i x \<equiv> array_upd a i x"   

  lemma nao_upd_aux: 
    fixes I xs
    defines "I \<equiv> {0..<length xs}"
    assumes "i\<in>I" "i\<in>R" and [simp]: "length xsi = length xs"
    shows "(\<Union>*j\<in>I - (R - {i}). \<upharpoonleft>A (xs[i := x] ! j) (xsi[i := xi] ! j)) = (\<upharpoonleft>A x xi ** (\<Union>*j\<in>I - R. \<upharpoonleft>A (xs ! j) (xsi ! j)))"
  proof -
    from assms have 1: "I - (R - {i}) = insert i (I-R)" by auto
    from assms have [simplified,simp]: "i\<notin>I-R" by auto
    have [simp]: "i<length xs" using \<open>i\<in>I\<close> unfolding I_def by auto
    have [simp]: "j\<in>I-R \<Longrightarrow> i\<noteq>j" for j using \<open>i\<in>R\<close> by auto
    show ?thesis apply (subst 1) by simp
  qed  
          
  term restrict_map
  
  lemma nao_upd_rule[vcg_rules]: "llvm_htriple
    (\<upharpoonleft>(nao_assn A R) xs a ** \<upharpoonleft>A x xi ** \<upharpoonleft>snat.assn i ii ** \<up>(i<length xs \<and> i\<in>dom R))
    (nao_upd a ii xi)
    (\<lambda>a'. \<up>(a'=a) ** \<upharpoonleft>(nao_assn A (R(i:=None))) (xs[i:=x]) a)"
    unfolding nao_assn_def nao_upd_def
    supply nao_upd_aux[simp] le_idxe_map_delD[simp] domI[simp]
    by vcg
  
  definition [llvm_code, llvm_inline]: "nao_rejoin a i \<equiv> return ()"  
  
  lemma nao_rejoin_aux: "i<length xs \<Longrightarrow> {0..<length xs} - (dom R - {i}) = insert i ({0..<length xs} - dom R)" by auto
  
  lemma nao_rejoin_rule[vcg_rules]: "llvm_htriple 
    (\<upharpoonleft>(nao_assn A R) xs a ** \<upharpoonleft>A x xi ** \<up>(x=xs!i) ** \<upharpoonleft>snat.assn i ii ** \<up>(i<length xs \<and> R i = Some xi))
    (nao_rejoin a ii)
    (\<lambda>_. \<upharpoonleft>(nao_assn A (R(i:=None))) xs a)"
    unfolding nao_rejoin_def nao_assn_def
    supply [simp] = le_idxe_map_delD' nao_rejoin_aux domI le_idxe_mapD
    by vcg
  
  
  definition [llvm_inline]: "nao_open a \<equiv> return ()"  
    
  lemma nao_open_rl[vcg_rules]: "llvm_htriple (\<upharpoonleft>(nao_assn A R) xss a) (nao_open a) (\<lambda>_. 
    EXS xs. 
       \<upharpoonleft>narray_assn xs a 
    ** \<up>(length xs = length xss) 
    ** \<up>(R \<subseteq>\<^sub>m idxe_map xs)
    ** (\<Union>*i\<in>{0..<length xss} - dom R. \<upharpoonleft>A (xss!i) (xs!i))  
  )"
    unfolding nao_open_def nao_assn_def by vcg
  
  
      
  definition [llvm_inline]: "nao_free free a len \<equiv> doM {
    llc_while 
      (\<lambda>i. ll_icmp_slt i len)
      (\<lambda>i. doM {
        x \<leftarrow> nao_nth a i;
        free x;
        i \<leftarrow> ll_add i (signed_nat 1);
        return i
      })
      (signed_nat 0);
      
    nao_open a;
    narray_free a
  }"
    
  definition "iseg_map n f (i::nat) \<equiv> if i<n then Some (f i) else None"
  lemma iseg_mapZ[simp]: "iseg_map 0 f = Map.empty" unfolding iseg_map_def by (intro ext) (auto)
  
  lemma iseg_map_upd_end_eq: "iseg_map n f(n \<mapsto> x) = iseg_map (Suc n) (f(n:=x))" 
    apply (intro ext)
    by (auto simp: iseg_map_def restrict_map_def)
    
  lemma iseg_map_dom[simp]: "dom (iseg_map n f) = {0..<n}"  
    by (auto simp: iseg_map_def split: if_splits)
    
  lemma nao_free_rl:
    assumes [vcg_rules]: "\<And>x xi. llvm_htriple (\<upharpoonleft>A x xi) (free xi) (\<lambda>_. \<box>)"
    shows "llvm_htriple 
      (\<upharpoonleft>(nao_assn A Map.empty) xs a ** \<upharpoonleft>snat.assn l li ** \<up>(l = length xs)) 
      (nao_free free a li) 
      (\<lambda>_. \<box>)"  
    unfolding nao_free_def
    apply (rewrite annotate_llc_while[where 
      I="\<lambda>ii t. EXS f i. \<upharpoonleft>snat.assn i ii ** \<upharpoonleft>(nao_assn A (iseg_map i f)) xs a ** \<up>(i\<le>length xs) ** \<up>\<^sub>!(t = length xs - i)"
      and R="less_than"]
      )
    supply [simp] = iseg_map_upd_end_eq 
    apply vcg_monadify
    by vcg


  subsection \<open>Array of Array Lists\<close>        

  type_synonym ('ll,'a,'l) array_array_list = "'ll word \<times> ('a,'l) array_list ptr"

  definition "aal_assn \<equiv> mk_assn (\<lambda>xs (ni,a). 
    \<upharpoonleft>snat.assn (length xs) ni ** \<upharpoonleft>(nao_assn arl_assn Map.empty) xs a)"

  abbreviation "aal_assn' TYPE('ll::len2) TYPE('a::llvm_rep) TYPE('l::len2) \<equiv> aal_assn :: (_,('ll,'a,'l) array_array_list) dr_assn"
      
  
  definition [llvm_code,llvm_inline]: "aal_new_raw n \<equiv> doM {
    a\<leftarrow>nao_new TYPE(('a::llvm_rep,'l::len2) array_list) n;
    return (n,a)
  }"
  
  (*abbreviation "aal_new TYPE('ll::len2) TYPE('a::llvm_rep) TYPE('l::len2) n \<equiv> aal_new_raw n :: ('ll,'a,'l) array_array_list llM"*)

  lemma snat_z_z_init[fri_rules]: "\<box> \<turnstile> \<upharpoonleft>\<^sub>psnat.assn 0 0"
    unfolding snat.assn_def 
    by (auto simp: snat_invar_def sep_algebra_simps)  
    
  lemma narray_assn_null_init[fri_rules]: "\<box> \<turnstile> \<upharpoonleft>narray_assn [] null"  
    unfolding narray_assn_def
    by (auto simp: sep_algebra_simps)
   
  thm fri_rules  
    
  lemma arl_init: "PRECOND (SOLVE_AUTO (4<LENGTH('l))) 
    \<Longrightarrow> \<box> \<turnstile> \<upharpoonleft>arl_assn [] (init::('a::llvm_rep,'l::len2) array_list)"  
    unfolding arl_assn_def arl_assn'_def vcg_tag_defs
    apply simp 
    apply (rule ENTAILSD)
    apply vcg
    done

  lemma aal_new_rl[vcg_rules]: "llvm_htriple 
    (\<upharpoonleft>snat.assn n ni ** \<up>(4<LENGTH('l::len2))) 
    (aal_new_raw ni)
    (\<lambda>p. \<upharpoonleft>(aal_assn' TYPE('ll::len2) TYPE('a::llvm_rep) TYPE('l::len2)) (replicate n []) p)
    "
    unfolding aal_assn_def aal_new_raw_def
    supply [vcg_rules] = nao_new_init_rl[OF arl_init]
    by vcg
    
  definition aal_push_back :: "('l::len2,'a::llvm_rep,'ll::len2) array_array_list \<Rightarrow> 'l word \<Rightarrow> 'a \<Rightarrow> ('l,'a,'ll) array_array_list llM"
    where [llvm_code, llvm_inline]: "aal_push_back na i x \<equiv> doM {
    let (n,a) = na;
    aa \<leftarrow> nao_nth a i;
    aa \<leftarrow> arl_push_back aa x;
    a \<leftarrow> nao_upd a i aa;
    return (n,a)
  }"  

  lemma aal_push_back_rl[vcg_rules]:
    fixes a :: "('ll::len2,'a::llvm_rep,'l::len2) array_array_list"
    shows "llvm_htriple 
      (\<upharpoonleft>aal_assn xss a ** \<upharpoonleft>snat.assn i ii ** \<up>(i<length xss \<and> length (xss!i) + 1 < max_snat LENGTH('l)))
      (aal_push_back a ii x)
      (\<lambda>a. \<upharpoonleft>aal_assn (xss[i:=(xss!i) @ [x]]) a)
    "
    unfolding aal_assn_def aal_push_back_def
    by vcg
    
  definition [llvm_code, llvm_inline]: "aal_pop_back na i \<equiv> doM {
    let (n,a) = na;
    aa \<leftarrow> nao_nth a i;
    (r,aa) \<leftarrow> arl_pop_back aa;
    a \<leftarrow> nao_upd a i aa;
    return (r,(n,a))
  }"

  lemma aal_pop_back_rl[vcg_rules]:
    fixes a :: "('ll::len2,'a::llvm_rep,'l::len2) array_array_list"
    shows "llvm_htriple 
      (\<upharpoonleft>aal_assn xss a ** \<upharpoonleft>snat.assn i ii ** \<up>(i<length xss \<and> xss!i \<noteq> []))
      (aal_pop_back a ii)
      (\<lambda>(x,a). \<upharpoonleft>aal_assn (xss[i:=butlast (xss!i)]) a ** \<up>(x = last (xss!i)))
    "
    unfolding aal_assn_def aal_pop_back_def
    by vcg
      
    
  definition [llvm_code, llvm_inline]: "aal_idx na i j \<equiv> doM {
    let (n,a) = na;
    aa \<leftarrow> nao_nth a i;
    r \<leftarrow> arl_nth aa j;
    nao_rejoin a i;
    return r
  }"    
    
  lemma aal_idx_rl[vcg_rules]: "llvm_htriple 
    (\<upharpoonleft>aal_assn xss a ** \<upharpoonleft>snat.assn i ii ** \<upharpoonleft>snat.assn j jj ** \<up>(i<length xss \<and> j<length (xss!i)))
    (aal_idx a ii jj)
    (\<lambda>x. \<upharpoonleft>aal_assn xss a ** \<up>(x = xss!i!j))"
    unfolding aal_assn_def aal_idx_def
    by vcg
    
    
  definition [llvm_code, llvm_inline]: "aal_llen na i \<equiv> doM {
    let (n,a) = na;
    aa \<leftarrow> nao_nth a i;
    r \<leftarrow> arl_len aa;
    nao_rejoin a i;
    return r
  }"    
    
  lemma aal_llen_rl[vcg_rules]: "llvm_htriple 
    (\<upharpoonleft>aal_assn xss a ** \<upharpoonleft>snat.assn i ii ** \<up>(i<length xss))
    (aal_llen a ii)
    (\<lambda>xi. EXS x. \<upharpoonleft>aal_assn xss a **\<upharpoonleft>snat.assn x xi ** \<up>(x = length (xss!i)))"
    unfolding aal_assn_def aal_llen_def
    by vcg
    
  definition [llvm_code, llvm_inline]: "aal_len na \<equiv> doM {
    let (n,a) = na;
    return n
  }" 
  
  lemma aal_len_rl[vcg_rules]: "llvm_htriple
    (\<upharpoonleft>aal_assn xss a)
    (aal_len a)
    (\<lambda>ni. \<upharpoonleft>aal_assn xss a ** \<upharpoonleft>snat.assn (length xss) ni)"
    unfolding aal_len_def aal_assn_def 
    by vcg

  definition [llvm_code, llvm_inline]: "aal_take na i l \<equiv> doM {
    let (n,a) = na;
    aa \<leftarrow> nao_nth a i;
    aa \<leftarrow> arl_take aa l;
    a \<leftarrow> nao_upd a i aa;
    return (n,a)
  }" 

  lemma aal_take_rl[vcg_rules]: "llvm_htriple
    (\<upharpoonleft>aal_assn xss a ** \<upharpoonleft>snat.assn i ii ** \<upharpoonleft>snat.assn l li ** \<up>(i<length xss \<and> l \<le> length (xss!i)))
    (aal_take a ii li)
    (\<lambda>a. \<upharpoonleft>aal_assn (xss[i := take l (xss!i)]) a)"
    unfolding aal_assn_def aal_take_def
    by vcg
        
    
  definition [llvm_code]: "aal_free na \<equiv> doM {
    let (n,a) = na;
    nao_free arl_free a n
  }"
  
  
  lemma aal_free_rl[vcg_rules]: "llvm_htriple 
    (\<upharpoonleft>aal_assn xss a) 
    (aal_free a) 
    (\<lambda>_. \<box>)"
    unfolding aal_assn_def aal_free_def
    supply [vcg_rules] = nao_free_rl[OF arl_free_rule] 
    by vcg
    
    
    
  export_llvm
    "aal_new_raw :: 64 word \<Rightarrow> (64,8 word,64) array_array_list llM"
    "aal_push_back :: (64,8 word,64) array_array_list \<Rightarrow> 64 word \<Rightarrow> 8 word \<Rightarrow> (64,8 word,64) array_array_list llM"  
    "aal_pop_back :: (64,8 word,64) array_array_list \<Rightarrow> 64 word \<Rightarrow> (8 word \<times> (64,8 word,64) array_array_list) llM"  
    "aal_idx :: (64,8 word,64) array_array_list \<Rightarrow> 64 word \<Rightarrow> 64 word \<Rightarrow> 8 word llM"  
    "aal_llen :: (64,8 word,64) array_array_list \<Rightarrow> 64 word \<Rightarrow> 64 word llM"  
    "aal_len :: (64,8 word,64) array_array_list \<Rightarrow> 64 word llM"  
    "aal_free :: (64,8 word,64) array_array_list \<Rightarrow> unit llM"  
    "aal_take :: (64,8 word,64) array_array_list \<Rightarrow> 64 word \<Rightarrow> 64 word \<Rightarrow> ((64,8 word,64) array_array_list) llM"  
    

end
