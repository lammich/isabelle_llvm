section \<open>Array-Lists\<close>
theory LLVM_DS_Array_List
imports LLVM_DS_NArray
begin
  type_synonym ('a,'l) array_list = "'l word \<times> 'l word \<times> 'a narray"

  subsection \<open>Auxiliary Functions\<close>

  definition [llvm_inline]: "arl_initial_size \<equiv> return ((signed_nat (8::_::len word)))"

  definition arl_push_back' :: "('a::llvm_rep,'l::len2) array_list \<Rightarrow> 'a \<Rightarrow> ('a,'l) array_list llM"    
    where [llvm_inline]: "arl_push_back' al x \<equiv> doM {
      let (l,c,a) = al;
      array_upd a l x;
      l \<leftarrow> ll_add l (signed_nat 1);
      return (l,c,a)
    }"
  
      
  definition arl_aux_compute_size :: "'l::len2 word \<Rightarrow> 'l word \<Rightarrow> 'l word llM" 
  where [llvm_inline]:   
    "arl_aux_compute_size c c' \<equiv> doM {
      max::'l word \<leftarrow> ll_max_snat;
      max \<leftarrow> ll_udiv max (signed_nat 2);
      b \<leftarrow> ll_icmp_ule c max;
      llc_if b (doM {
          c \<leftarrow> ll_mul c (signed_nat 2);
          cok \<leftarrow> ll_icmp_sle c' c;
          llc_if cok (return c) (return c')
        }) 
        (return c')
    }"
  
  
  definition arl_resize :: "'l word \<Rightarrow> ('a::llvm_rep,'l::len2) array_list \<Rightarrow> ('a,'l) array_list llM"
    where [llvm_code]: "arl_resize c' al \<equiv> doM {
      let (l,c,a) = al;
      c \<leftarrow> arl_aux_compute_size c c';
      a' \<leftarrow> narray_new TYPE('a) c;
      arraycpy a' a l;
      narray_free a;
      return (l,c,a')
    }"    
  
      
  definition arl_ensure_capacity :: "'l word \<Rightarrow> ('a::llvm_rep,'l::len2) array_list \<Rightarrow> ('a,'l) array_list llM"  
    where [llvm_inline]: "arl_ensure_capacity c' al \<equiv> doM {
      let (l,c,a) = al;
      cok \<leftarrow> ll_icmp_sle c' c;
      llc_if cok (return (l,c,a)) (arl_resize c' (l,c,a))
    }"

  
  
  subsection \<open>Interface Functions\<close>

  definition arl_new_raw :: "('a::llvm_rep,'l::len2) array_list llM"
  where [llvm_code,llvm_inline]: "arl_new_raw \<equiv> doM {
    c \<leftarrow> arl_initial_size;
    a \<leftarrow> narray_new TYPE('a) c;
    return (signed_nat 0,c,a)
  }"
    
  definition arl_new :: "'a::llvm_rep itself \<Rightarrow> 'l::len2 itself \<Rightarrow> ('a,'l) array_list llM"
  where [llvm_inline]: "arl_new TYPE('a::llvm_rep) TYPE('l::len2) \<equiv> arl_new_raw"

  
  definition arl_new_sz_raw :: "'l::len2 word \<Rightarrow> ('a::llvm_rep,'l) array_list llM"
  where [llvm_code,llvm_inline]: "arl_new_sz_raw n \<equiv> doM {
    a \<leftarrow> narray_new TYPE('a) n;
    return (n,n,a)
  }"

  definition arl_new_sz :: "'a::llvm_rep itself \<Rightarrow> 'l::len2 word \<Rightarrow> ('a,'l) array_list llM" 
    where [llvm_inline]: "arl_new_sz TYPE('a) n \<equiv> arl_new_sz_raw n"
      
  definition arl_clear :: "('a::llvm_rep,'l::len2) array_list \<Rightarrow> ('a::llvm_rep,'l) array_list llM"
    where [llvm_code,llvm_inline]: "arl_clear al \<equiv> doM {
      let (l,c,a) = al;
      return (signed_nat 0,c,a)
    }"  
    
  definition arl_free :: "('a::llvm_rep,'l::len) array_list \<Rightarrow> unit llM" 
  where [llvm_code,llvm_inline]: "arl_free al \<equiv> doM {
    let (_,_,a) = al;
    narray_free a
  }"
  

  definition arl_nth :: "('a::llvm_rep,'l::len2) array_list \<Rightarrow> 'll::len2 word \<Rightarrow> 'a llM"
    where [llvm_code,llvm_inline]: "arl_nth al i \<equiv> doM {
      let (l,c,a) = al;
      array_nth a i
    }"
    
  definition arl_upd :: "('a::llvm_rep,'l::len2) array_list \<Rightarrow> 'll::len2 word \<Rightarrow> 'a \<Rightarrow> ('a,'l) array_list llM"
    where [llvm_code,llvm_inline]: "arl_upd al i x \<equiv> doM {
      let (l,c,a) = al;
      array_upd a i x;
      return (l,c,a)
    }"
  
  definition arl_len :: "('a::llvm_rep,'l::len2) array_list \<Rightarrow> 'l word llM" 
    where [llvm_code,llvm_inline]: "arl_len al \<equiv> let (l,c,a) = al in return l"
    
    
  definition [llvm_code,llvm_inline]: "arl_push_back al x \<equiv> doM {
    l \<leftarrow> arl_len al;
    l \<leftarrow> ll_add l (signed_nat 1);
    al \<leftarrow> arl_ensure_capacity l al;
    arl_push_back' al x
  }"

  definition [llvm_code,llvm_inline]: "arl_pop_back al \<equiv> doM {
    let (l,c,a) = al;
    l \<leftarrow> ll_sub l (signed_nat 1);
    r \<leftarrow> array_nth a l;
    return (r,(l,c,a))
  }"
  
  definition [llvm_code,llvm_inline]: "arl_take l' al \<equiv> doM {
    let (l,c,a) = al;
    return (l',c,a)
  }"

  definition [llvm_code,llvm_inline]: "arl_last al \<equiv> doM {
    let (l,c,a) = al;
    l \<leftarrow> ll_sub l (signed_nat 1);
    r \<leftarrow> array_nth a l;
    return r
  }"
  
  definition [llvm_code,llvm_inline]: "arl_butlast al \<equiv> doM {
    let (l,c,a) = al;
    l \<leftarrow> ll_sub l (signed_nat 1);
    return (l,c,a)
  }"
  
    
  text \<open>Direct access to array underlying array-list \<close>
  definition array_of_arl :: "('a::llvm_rep,'l::len2) array_list \<Rightarrow> 'a ptr" where 
    [llvm_inline]: "array_of_arl \<equiv> \<lambda>(l,c,a). a"
  
  
  export_llvm (debug)
    "arl_new_raw :: (64 word,64) array_list llM" is "arl_new"
    "arl_new_sz_raw :: 64 word \<Rightarrow> (64 word,64) array_list llM"
    "arl_clear :: (64 word,64) array_list \<Rightarrow> (64 word,64) array_list llM"
    "arl_free :: (64 word,64) array_list \<Rightarrow> unit llM" is "arl_free"
    "arl_nth :: (64 word,64) array_list \<Rightarrow> 64 word \<Rightarrow> 64 word llM" is "arl_nth"
    "arl_upd :: (64 word,64) array_list \<Rightarrow> 64 word \<Rightarrow> 64 word \<Rightarrow> (64 word,64) array_list llM" is "arl_upd"
    "arl_len :: (64 word,64) array_list \<Rightarrow> 64 word llM" is "arl_len"
    "arl_push_back :: (64 word,64) array_list \<Rightarrow> 64 word \<Rightarrow> (64 word,64) array_list llM" is "arl_push_back"
    "arl_pop_back :: (64 word,64) array_list \<Rightarrow> (64 word \<times> (64 word,64) array_list) llM" is "arl_pop_back"
    "arl_take :: 64 word \<Rightarrow> (64 word,64) array_list \<Rightarrow> (64 word,64) array_list llM" is "arl_take"
    "arl_last :: (64 word,64) array_list \<Rightarrow> 64 word llM" is "arl_last"
    "arl_butlast :: (64 word,64) array_list \<Rightarrow> ((64 word,64) array_list) llM" is "arl_butlast"
    
    
  subsection \<open>Reasoning Setup\<close>  
  
  definition arl_assn' :: "('a::llvm_rep list \<times> nat, 'l::len2 word \<times> 'l word \<times> 'a ptr) dr_assn"
    where "arl_assn' \<equiv> mk_assn (\<lambda>(xs,c) (li,ci,ai). 
      EXS l a. \<upharpoonleft>snat.assn l li ** \<upharpoonleft>snat.assn c ci ** \<upharpoonleft>narray_assn a ai 
        ** \<up>(LENGTH('l)>4 \<and> l\<le>c \<and> c=length a \<and> xs = take l a))"
      
  definition arl_assn :: "('a::llvm_rep list, 'l::len2 word \<times> 'l word \<times> 'a ptr) dr_assn"
    where "arl_assn \<equiv> mk_assn (\<lambda>xs ali. EXS c. \<upharpoonleft>arl_assn' (xs,c) ali)"
    
  subsubsection \<open>Auxiliary Rules\<close>
  
  lemma arl_aux_compute_size_rule[vcg_rules]: 
    "llvm_htriple 
      (\<up>\<^sub>d(LENGTH('a)>2) ** \<upharpoonleft>snat.assn c ci ** \<upharpoonleft>snat.assn c' ci' ** \<up>\<^sub>d(c\<le>c')) 
      (arl_aux_compute_size ci (ci'::'a::len2 word)) 
      (\<lambda>ri. EXS r. \<upharpoonleft>snat.assn r ri ** \<up>(max c c' \<le> r))"  
    unfolding arl_aux_compute_size_def
    apply (vcg_monadify)
    by vcg
    
    
  lemma arl_resize_rule[vcg_rules]: 
    "llvm_htriple 
      (\<upharpoonleft>snat.assn l li ** \<upharpoonleft>snat.assn c (ci::'l::len2 word) ** \<upharpoonleft>narray_assn a ai ** \<upharpoonleft>snat.assn c\<^sub>n ci\<^sub>n
        ** \<up>\<^sub>d(LENGTH('l)>2 \<and> c\<^sub>n>c \<and> l\<le>c \<and> c=length a)
      ) 
      (arl_resize ci\<^sub>n (li,ci,ai))
      (\<lambda>(li,ci,ai). EXS c' a'. \<upharpoonleft>snat.assn l li ** \<upharpoonleft>snat.assn c' ci ** \<upharpoonleft>narray_assn a' ai
        ** \<up>(c'\<ge>c\<^sub>n \<and> c'=length a' \<and> take l a' = take l a)
      )"  
    unfolding arl_resize_def
    by vcg'
  
    
  lemma arl_ensure_capacity_rule[vcg_rules]: 
    "llvm_htriple
      (\<upharpoonleft>arl_assn' (al,oc) ali ** \<upharpoonleft>snat.assn c ci) (arl_ensure_capacity ci ali) 
      (\<lambda>ali. EXS c'. \<upharpoonleft>arl_assn' (al,c') ali ** \<up>(c'\<ge>c))
    "  
    unfolding arl_assn'_def arl_ensure_capacity_def
    by vcg
    
  lemma arl_push_back'_rule[vcg_rules]:
    "llvm_htriple 
      (\<upharpoonleft>arl_assn' (al,c) ali ** \<up>\<^sub>d(length al < c)) 
      (arl_push_back' ali x) 
      (\<lambda>ali. EXS c. \<upharpoonleft>arl_assn' (al@[x],c) ali)"
    unfolding arl_assn'_def arl_push_back'_def
    apply (vcg_monadify)
    apply vcg'
    apply (auto simp: take_update_last)
    done
        
  lemma arl_len_rule_internal:
    "llvm_htriple (\<upharpoonleft>arl_assn' (al,c) ali) (arl_len ali) (\<lambda>li. \<upharpoonleft>arl_assn' (al,c) ali ** \<upharpoonleft>snat.assn (length al) li)"  
    unfolding arl_assn'_def arl_len_def
    by vcg
  
  subsubsection \<open>Interface Rules\<close>

  lemma arl_new_raw_rule[vcg_rules]: 
    "llvm_htriple (\<up>(LENGTH('l)>4)) (arl_new_raw) (\<lambda>ali. \<upharpoonleft>arl_assn [] (ali::(_,'l::len2)array_list))"
    unfolding arl_new_def arl_new_raw_def arl_initial_size_def arl_assn_def arl_assn'_def
    apply (vcg_monadify)
    by vcg'
  
      
  lemma arl_new_rule[vcg_rules]: 
    "llvm_htriple (\<up>(LENGTH('c)>4)) (arl_new TYPE('a::llvm_rep) TYPE('c::len2)) (\<lambda>ali. \<upharpoonleft>arl_assn [] ali)"
    unfolding arl_new_def arl_new_raw_def arl_initial_size_def arl_assn_def arl_assn'_def
    apply (vcg_monadify)
    by vcg'

  lemma arl_new_sz_rule[vcg_rules]: 
    "llvm_htriple 
      (\<upharpoonleft>snat.assn n ni ** \<up>(LENGTH('c::len2)>4)) 
      (arl_new_sz TYPE('a::llvm_rep) (ni::'c word)) 
      (\<lambda>ali. \<upharpoonleft>arl_assn (replicate n init) ali)"
    unfolding arl_new_sz_def arl_new_sz_raw_def arl_initial_size_def arl_assn_def arl_assn'_def
    apply (vcg_monadify)
    by vcg'
    
  lemma arl_assn_init_pure: 
    "PRECOND (SOLVE_AUTO (4 < LENGTH('l))) \<Longrightarrow> \<box> \<turnstile> \<upharpoonleft>arl_assn [] (init::(_,'l::len2)array_list)"  
    unfolding arl_assn_def arl_assn'_def vcg_tag_defs
    unfolding snat.assn_def snat_invar_def
    supply [fri_rules] = narray_assn_init_pure
    apply simp
    apply (rule ENTAILSD)
    by vcg
    
  lemma arl_clear_rule[vcg_rules]: 
    "llvm_htriple 
      (\<upharpoonleft>arl_assn al ali) 
      (arl_clear ali) 
      (\<lambda>ali. \<upharpoonleft>arl_assn [] ali)"
    unfolding arl_clear_def arl_assn_def arl_assn'_def
    by (vcg_monadify) vcg'
    
  lemma arl_free_rule[vcg_rules]:
    "llvm_htriple (\<upharpoonleft>arl_assn al ali) (arl_free ali) (\<lambda>_. \<box>)"  
    unfolding arl_assn_def arl_assn'_def arl_free_def
    by vcg
    
  lemma arl_nth_rule[vcg_rules]:
    "llvm_htriple 
      (\<upharpoonleft>arl_assn al ali ** \<upharpoonleft>snat.assn i ii ** \<up>\<^sub>d(i<length al)) 
      (arl_nth ali ii)
      (\<lambda>x. \<upharpoonleft>arl_assn al ali ** \<up>(x = al!i))"
    unfolding arl_assn_def arl_assn'_def arl_nth_def
    by vcg
  
  lemma array_of_arl_nth_rule[vcg_rules]: "llvm_htriple 
    (\<upharpoonleft>arl_assn xs a ** \<upharpoonleft>snat.assn i ii ** \<up>(i < length xs))
    (array_nth (array_of_arl a) ii)
    (\<lambda>x. \<upharpoonleft>arl_assn xs a ** \<up>(x = xs!i))"
    unfolding arl_assn_def arl_assn'_def array_of_arl_def by vcg
    
  lemma arl_upd_rule[vcg_rules]:
    "llvm_htriple 
      (\<upharpoonleft>arl_assn al ali ** \<upharpoonleft>snat.assn i ii ** \<up>\<^sub>d(i<length al)) 
      (arl_upd ali ii x)
      (\<lambda>ali. \<upharpoonleft>arl_assn (al[i:=x]) ali)"
    unfolding arl_assn_def arl_assn'_def arl_upd_def
    by vcg
    
  lemma arl_len_rule[vcg_rules]:
    "llvm_htriple (\<upharpoonleft>arl_assn al ali) (arl_len ali) (\<lambda>li. \<upharpoonleft>arl_assn al ali ** \<upharpoonleft>snat.assn (length al) li)"  
    unfolding arl_assn_def
    supply arl_len_rule_internal[vcg_rules]
    by vcg
    
  lemma arl_push_back_rule[vcg_rules]:
    "llvm_htriple (\<upharpoonleft>arl_assn al (ali::(_,'l::len2)array_list) ** \<up>\<^sub>d(length al + 1 < max_snat LENGTH('l))) (arl_push_back ali x) (\<lambda>ali. \<upharpoonleft>arl_assn (al@[x]) ali)"  
    unfolding arl_assn_def arl_push_back_def
    supply arl_len_rule_internal[vcg_rules]
    apply (vcg_monadify)
    by vcg'

  lemma arl_pop_back_rule[vcg_rules]:
    "llvm_htriple (\<upharpoonleft>arl_assn al (ali::(_,'l::len2)array_list) ** \<up>\<^sub>d(al\<noteq>[])) (arl_pop_back ali) (\<lambda>(x,ali). \<upharpoonleft>arl_assn (butlast al) ali ** \<up>(x=last al))"  
    unfolding arl_assn_def arl_assn'_def arl_pop_back_def
    supply arl_len_rule_internal[vcg_rules]
    apply (vcg_monadify)
    apply vcg'
    by (auto simp: take_minus_one_conv_butlast last_take_nth_conv)
    
  lemma arl_take_rule[vcg_rules]:
    "llvm_htriple 
      (\<upharpoonleft>arl_assn al (ali::(_,'l::len2)array_list) ** \<upharpoonleft>snat.assn l li ** \<up>\<^sub>d(l \<le> length al)) 
      (arl_take li ali) 
      (\<lambda>ali. \<upharpoonleft>arl_assn (take l al) ali)"  
    unfolding arl_assn_def arl_assn'_def arl_take_def
    by vcg
    

  lemma arl_last_rule[vcg_rules]:
    "llvm_htriple (\<upharpoonleft>arl_assn al (ali::(_,'l::len2)array_list) ** \<up>\<^sub>d(al\<noteq>[])) (arl_last ali) (\<lambda>x. \<upharpoonleft>arl_assn al ali ** \<up>(x=last al))"  
    unfolding arl_assn_def arl_assn'_def arl_last_def
    supply arl_len_rule_internal[vcg_rules]
    apply (vcg_monadify)
    apply vcg'
    by (auto simp: last_take_nth_conv)
    
    
  lemma arl_butlast_rule[vcg_rules]:
    "llvm_htriple (\<upharpoonleft>arl_assn al (ali::(_,'l::len2)array_list) ** \<up>\<^sub>d(al\<noteq>[])) (arl_butlast ali) (\<lambda>ali. \<upharpoonleft>arl_assn (butlast al) ali)"  
    unfolding arl_assn_def arl_assn'_def arl_butlast_def
    supply arl_len_rule_internal[vcg_rules]
    apply (vcg_monadify)
    apply vcg'
    by (auto simp: take_minus_one_conv_butlast)
    
    
    
    
        
end
