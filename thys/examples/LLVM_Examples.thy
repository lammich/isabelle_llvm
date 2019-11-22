section \<open>Examples\<close>
theory LLVM_Examples
imports 
  "../ds/LLVM_DS_Dflt"
  "../ds/LLVM_DS_Array_List"
begin

text \<open>Examples on top of Isabelle-LLVM basic layer. 
  For the verification of more complex algorithms, consider using
  Isabelle-LLVM with the Refinement Framework, and the Sepref tool.
  See, e.g., @{file Bin_Search.thy}.
\<close>

(* TODO: Parts of this file are incomplete, the examples could me more elaborate! *)

subsection \<open>Numeric Algorithms\<close>

subsubsection \<open>Exponentiation\<close>

definition exp :: "'a::len word \<Rightarrow> 'b::len word llM" where [llvm_code]: "exp r \<equiv> doM {
  a \<leftarrow> ll_const (unsigned 1);
  (a,r) \<leftarrow> llc_while 
    (\<lambda>(a,r). doM { ll_icmp_ult (unsigned 0) r}) 
    (\<lambda>(a,r). doM {
      return (a*unsigned 2,r-unsigned 1)
    })
    (a,r);
  return a
}"

abbreviation exp32::"32 word \<Rightarrow> 32 word llM" where "exp32 \<equiv> exp"
abbreviation exp64::"64 word \<Rightarrow> 64 word llM" where "exp64 \<equiv> exp"

export_llvm 
  exp32 is "uint32_t exp32 (uint32_t)" 
  exp64 is "uint64_t exp64 (uint64_t)" 
  file "code/exp.ll"

lemma exp_aux1: 
  assumes "2 ^ nat k < (N::int)" "t \<le> k" "0 < t" 
  shows "2 * 2 ^ nat (k - t) < N"
proof -
  have "\<lbrakk>2 ^ k < N; 0 < t; t \<le> k\<rbrakk> \<Longrightarrow> 2 * 2 ^ (k - t) < (N::int)" for k t :: nat
    by (metis Suc_leI diff_less less_le_trans not_less power.simps(2) power_increasing_iff rel_simps(49) semiring_norm(76))
  with assms show ?thesis
    by (auto simp add: nat_diff_distrib' dest!: nat_mono simp flip: zero_less_nat_eq)
qed  
  
lemma exp_aux2:  "\<lbrakk>t \<le> k; 0 < t\<rbrakk> \<Longrightarrow> nat (1+k-t) = Suc (nat (k-t))" by simp

lemma exp_correct:
  assumes "LENGTH('b::len) \<ge> 2"
  shows "llvm_htriple 
    (\<upharpoonleft>uint.assn k (ki::'a::len word) ** \<up>(2^nat k \<in> uints LENGTH('b))) 
    (exp ki) 
    (\<lambda>r::'b word. \<upharpoonleft>uint.assn (2^nat k) r ** \<upharpoonleft>uint.assn k ki)"
  unfolding exp_def
  apply (rewrite annotate_llc_while[where 
    I="\<lambda>(ai,ri) t. EXS a r. \<upharpoonleft>uint.assn a ai ** \<upharpoonleft>uint.assn r ri ** \<up>\<^sub>d( 0\<le>r \<and> r\<le>k \<and> a = 2^nat (k-r) ) ** \<up>\<^sub>!(t = r)"
    and R="measure nat"
    ])
  apply vcg_monadify  
  apply (vcg'; (clarsimp simp: algebra_simps)?)
  using assms
  apply (simp_all add: exp_aux1 exp_aux2)
  done


text \<open>Executability of semantics inside Isabelle\<close>
value "run (exp64 32) llvm_empty_memory"

subsubsection \<open>Euclid's Algorithm\<close>

                       
definition [llvm_code]: "euclid (a::'a::len word) b \<equiv> doM {
  (a,b) \<leftarrow> llc_while 
    (\<lambda>(a,b) \<Rightarrow> ll_cmp (a \<noteq> b))
    (\<lambda>(a,b) \<Rightarrow> if (a\<le>b) then return (a,b-a) else return (a-b,b))
    (a,b);
  return a
}"
  
export_llvm (debug) (no_while) 
  "euclid :: 64 word \<Rightarrow> 64 word \<Rightarrow> 64 word llM" is "uint64_t euclid (uint64_t, uint64_t)"
  file "code/euclid.ll"

  
lemma gcd_diff1': "gcd (a::int) (b-a) = gcd a b"
  by (metis gcd.commute gcd_diff1)   
  

lemma "llvm_htriple 
  (\<upharpoonleft>uint.assn a\<^sub>0 ai ** \<upharpoonleft>uint.assn b\<^sub>0 bi ** \<up>\<^sub>d(0<a\<^sub>0 \<and> 0<b\<^sub>0)) 
  (euclid ai bi) 
  (\<lambda>ri. \<upharpoonleft>uint.assn (gcd a\<^sub>0 b\<^sub>0) ri)"
  unfolding euclid_def
  apply (rewrite annotate_llc_while[where 
    I="\<lambda>(ai,bi) t. EXS a b. \<upharpoonleft>uint.assn a ai ** \<upharpoonleft>uint.assn b bi 
        ** \<up>\<^sub>a(t=a+b) ** \<up>\<^sub>d(0<a \<and> 0<b \<and> gcd a b = gcd a\<^sub>0 b\<^sub>0)" 
    and R="measure nat"  
  ])
  apply vcg_monadify
  apply (vcg'; clarsimp?)
  apply (simp_all add: gcd_diff1 gcd_diff1')
  done

subsubsection \<open>Fibonacci Numbers\<close>

definition fib :: "'n::len word \<Rightarrow> 'n word llM" where [llvm_code]: "fib n \<equiv> REC (\<lambda>fib' n. 
  if n\<le>unsigned 1 then return n 
  else doM { 
    n\<^sub>1 \<leftarrow> fib' (n-unsigned 1); 
    n\<^sub>2 \<leftarrow> fib' (n-unsigned 2); 
    return (n\<^sub>1+n\<^sub>2)     
  }) n"

abbreviation fib64 :: "64 word \<Rightarrow> 64 word llM" where "fib64 \<equiv> fib"
export_llvm thms: fib64
  
(* TODO: Arbitrary fixed-point reasoning not yet supported in VCG!
  set up a rule with pre and post consequence rule, 
  and seplogic-assertions

lemma
  assumes MONO: "\<And>x. M.mono_body (\<lambda>fa. F fa x)"
  assumes "P x s m"
  assumes "wf R"
  assumes "\<And>D x s m. \<lbrakk> P x s m; \<And>x' s' m'. \<lbrakk> P x' s' m'; (m',m)\<in>R \<rbrakk> \<Longrightarrow> wp (D x') Q s' \<rbrakk> \<Longrightarrow> wp (F D x) Q s"
  shows "wp (REC F x) Q s"
  using assms(3,2)
  apply (induction m arbitrary: x s rule: wf_induct_rule)
  apply (subst REC_unfold) apply simp apply (rule MONO)
  using assms(4) by simp
  
  

lemma "llvm_htriple (\<upharpoonleft>uint.assn n ni) (fib ni) (\<lambda>ri. \<upharpoonleft>uint.assn x ri)"
  unfolding fib_def
  apply vcg_monadify
  apply vcg
  find_theorems wp REC
*)
  
prepare_code_thms (LLVM) [code] fib_def  (* Set up code equation. Required to execute semantics in Isabelle. *)

value "map (\<lambda>n. run (fib64 n) (LLVM_MEMORY (MEMORY []))) [0,1,2,3]"


(*
lemmas [named_ss llvm_inline cong] = refl[of "numeral _"]
*)

definition test :: "64 word \<Rightarrow> 64 word \<Rightarrow> _ llM"
where [llvm_code]: "test a b \<equiv> doM {

  return (a,b) 
}"

ML_val \<open>
  local open LLC_Preprocessor
    val ctxt = @{context}
  in

    val thm = @{thm test_def}
      |> cthm_inline ctxt
      |> cthm_monadify ctxt
  
  end
\<close>


find_theorems llc_while

lemma "foo (test)"
  unfolding test_def
  apply (simp named_ss llvm_inline:)
  oops

export_llvm test



text \<open>Example and Regression Tests using LLVM-VCG directly, 
i.e., without Refinement Framework\<close>

subsection \<open>Regression Tests\<close>
typedef my_pair = "UNIV :: (64 word \<times> 32 word) set" by simp

lemmas my_pair_bij[simp] = Abs_my_pair_inverse[simplified] Rep_my_pair_inverse

instantiation my_pair :: llvm_rep
begin
  definition "from_val_my_pair \<equiv> Abs_my_pair o from_val"
  definition "to_val_my_pair \<equiv> to_val o Rep_my_pair"
  definition [simp]: "struct_of_my_pair (_:: my_pair itself) \<equiv> struct_of TYPE(64 word \<times> 32 word)"
  definition "init_my_pair \<equiv> Abs_my_pair init"

  instance
    apply standard
    unfolding from_val_my_pair_def to_val_my_pair_def struct_of_my_pair_def init_my_pair_def
    apply (auto simp: to_val_word_def)
    done

end

definition my_fst :: "my_pair \<Rightarrow> 64 word llM" where [llvm_inline]: "my_fst \<equiv> ll_extract_fst"
definition my_snd :: "my_pair \<Rightarrow> 32 word llM" where [llvm_inline]: "my_snd \<equiv> ll_extract_snd"
definition my_ins_fst :: "my_pair \<Rightarrow> 64 word \<Rightarrow> my_pair llM" where [llvm_inline]: "my_ins_fst \<equiv> ll_insert_fst"
definition my_ins_snd :: "my_pair \<Rightarrow> 32 word \<Rightarrow> my_pair llM" where [llvm_inline]: "my_ins_snd \<equiv> ll_insert_snd"
definition my_gep_fst :: "my_pair ptr \<Rightarrow> 64 word ptr llM" where [llvm_inline]: "my_gep_fst \<equiv> ll_gep_fst"
definition my_gep_snd :: "my_pair ptr \<Rightarrow> 32 word ptr llM" where [llvm_inline]: "my_gep_snd \<equiv> ll_gep_snd"


definition [llvm_code]: "add_add (a::_ word) \<equiv> doM {
  x \<leftarrow> ll_add a a;
  x \<leftarrow> ll_add x x;
  return x
}"

definition [llvm_code]: "test_named (a::32 word) (b::64 word) \<equiv> doM {
  a \<leftarrow> add_add a;
  b \<leftarrow> add_add b;
  let n = (init::my_pair);
  a \<leftarrow> my_fst n;
  b \<leftarrow> my_snd n;
  n \<leftarrow> my_ins_fst n init;
  n \<leftarrow> my_ins_snd n init;
  
  p \<leftarrow> ll_malloc TYPE(my_pair) (1::64 word);
  p1 \<leftarrow> my_gep_fst p;
  p2 \<leftarrow> my_gep_snd p;
  
  return b
}"



lemma [ll_is_pair_type_thms]: "ll_is_pair_type False TYPE(my_pair) TYPE(64 word) TYPE(32 word)"
  unfolding ll_is_pair_type_def
  by auto

export_llvm (debug) test_named file "code/test_named.ll"





  
subsection \<open>Array List Examples\<close>

definition [llvm_code]: "cr_big_al (n::64 word) \<equiv> doM {
  a \<leftarrow> arl_new TYPE(64 word) TYPE(64);
  (_,a) \<leftarrow> llc_while 
    (\<lambda>(n,a). ll_icmp_ult (signed_nat 0) n) 
    (\<lambda>(n,a). doM { a \<leftarrow> arl_push_back a n; n \<leftarrow> ll_sub n (signed_nat 1); return (n,a) }) 
    (n,a);
  
  (_,s) \<leftarrow> llc_while 
    (\<lambda>(n,s). ll_icmp_ult (signed_nat 0) n) 
    (\<lambda>(n,s). doM { n \<leftarrow> ll_sub n (signed_nat 1); x \<leftarrow> arl_nth a n; s\<leftarrow>ll_add x s; return (n,s) }) 
    (n,signed_nat 0);
    
  return s    
}"

declare Let_def[llvm_inline]
export_llvm (debug) cr_big_al is "cr_big_al" file "code/cr_big_al.ll"


subsection \<open>Sorting\<close>

definition [llvm_inline]: "llc_for_range l h c s \<equiv> doM {
  (_,s) \<leftarrow> llc_while (\<lambda>(i,s). ll_cmp (i<h)) (\<lambda>(i,s). doM { 
    s\<leftarrow>c i s; 
    i \<leftarrow> ll_add i 1; 
    return (i,s)}
  ) (l,s);
  return s
}"

lemma llc_for_range_rule:
  assumes [vcg_rules]: "\<And>i ii si. llvm_htripleF F 
      (\<upharpoonleft>snat.assn i ii ** \<up>\<^sub>d(lo\<le>i \<and> i<hi) ** I i si) 
      (c ii si) 
      (\<lambda>si. I (i+1) si)"
  shows "llvm_htripleF F
      (\<upharpoonleft>snat.assn lo loi ** \<upharpoonleft>snat.assn hi hii ** \<up>(lo\<le>hi) ** I lo si)
      (llc_for_range loi hii c si)
      (\<lambda>si. I hi si)"
  unfolding llc_for_range_def
  apply (rewrite at 1 to "signed_nat 1" signed_nat_def[symmetric])
  apply (rewrite annotate_llc_while[where 
    I="\<lambda>(ii,si) t. EXS i. \<upharpoonleft>snat.assn i ii ** \<up>(lo\<le>i \<and> i\<le>hi) ** \<up>\<^sub>!(t=hi-i) ** I i si" 
    and R="measure id"])
  apply vcg_monadify
  apply vcg'
  done
  
definition llc_for_range_annot :: "(nat \<Rightarrow> 'b::llvm_rep \<Rightarrow> ll_assn)
  \<Rightarrow> 'a::len word \<Rightarrow> 'a word \<Rightarrow> ('a word \<Rightarrow> 'b \<Rightarrow> 'b llM) \<Rightarrow> 'b \<Rightarrow> 'b llM"
  where [llvm_inline]: "llc_for_range_annot I \<equiv> llc_for_range"  
declare [[vcg_const "llc_for_range_annot I"]]
  
lemmas annotate_llc_for_range = llc_for_range_annot_def[symmetric]

lemmas llc_for_range_annot_rule[vcg_rules] 
  = llc_for_range_rule[where I=I, unfolded annotate_llc_for_range[of I]] for I


(* TODO: Move *)
lemma sep_red_idx_setI:  
  assumes "\<And>I I'. I\<inter>I'={} \<Longrightarrow> A (I\<union>I') = (A I ** A I')"
  shows "is_sep_red (A (I-I')) (A (I'-I)) (A I) (A I')"
proof -
  define I\<^sub>1 where "I\<^sub>1 \<equiv> I-I'"
  define I\<^sub>2 where "I\<^sub>2 \<equiv> I'-I"
  define C where "C \<equiv> I\<inter>I'"

  have S1: "I = I\<^sub>1 \<union> C" "I'=I\<^sub>2 \<union> C" and S2: "I-I' = I\<^sub>1" "I'-I=I\<^sub>2" and DJ: "I\<^sub>1\<inter>C={}" "I\<^sub>2\<inter>C={}"
    unfolding I\<^sub>1_def I\<^sub>2_def C_def by auto

  show ?thesis  
    apply (rule is_sep_redI)
    apply (simp only: S2; simp only: S1)
    apply (auto simp: DJ assms)
    by (simp add: conj_entails_mono sep_conj_left_commute)
    
qed    

lemma sep_set_img_reduce:
  "is_sep_red (\<Union>*i\<in>I-I'. f i) (\<Union>*i\<in>I'-I. f i) (\<Union>*i\<in>I. f i) (\<Union>*i\<in>I'. f i)"
  by (rule sep_red_idx_setI) simp

(* TODO: Move *)  
  
lemma is_sep_red_false[simp]: "is_sep_red P' Q' sep_false Q"
  by (auto simp: is_sep_red_def)

  
(* TODO: Move *)  
lemma entails_pre_pure[sep_algebra_simps]: 
  "(\<up>\<Phi> \<turnstile> Q) \<longleftrightarrow> (\<Phi> \<longrightarrow> \<box>\<turnstile>Q)"  
  "(\<up>\<Phi>**P \<turnstile> Q) \<longleftrightarrow> (\<Phi> \<longrightarrow> P\<turnstile>Q)"  
  by (auto simp: entails_def sep_algebra_simps pred_lift_extract_simps)
  
  
  
definition "lstr_assn A I \<equiv> mk_assn (\<lambda>as cs. \<up>(length cs = length as \<and> (\<forall>i\<in>I. i<length as)) ** (\<Union>*i\<in>I. \<upharpoonleft>A (as!i) (cs!i)))"

lemma lstr_assn_union: "I\<inter>I'={} \<Longrightarrow> 
  \<upharpoonleft>(lstr_assn A (I\<union>I')) as cs = (\<upharpoonleft>(lstr_assn A I) as cs ** \<upharpoonleft>(lstr_assn A I') as cs)"
  by (auto simp: lstr_assn_def sep_algebra_simps pred_lift_extract_simps)

  
lemma lstr_assn_red: "is_sep_red 
  (\<upharpoonleft>(lstr_assn A (I-I')) as cs) (\<upharpoonleft>(lstr_assn A (I'-I)) as cs)
  (\<upharpoonleft>(lstr_assn A I) as cs) (\<upharpoonleft>(lstr_assn A I') as cs)"  
  by (rule sep_red_idx_setI) (simp add: lstr_assn_union)

lemma lstr_assn_red': "PRECOND (SOLVE_AUTO (I\<inter>I'\<noteq>{})) \<Longrightarrow> is_sep_red 
  (\<upharpoonleft>(lstr_assn A (I-I')) as cs) (\<upharpoonleft>(lstr_assn A (I'-I)) as cs)
  (\<upharpoonleft>(lstr_assn A I) as cs) (\<upharpoonleft>(lstr_assn A I') as cs)"  
  by (rule sep_red_idx_setI) (simp add: lstr_assn_union)
  
    
lemma lstr_assn_singleton: "\<upharpoonleft>(lstr_assn A {i}) as cs = (\<up>(length cs = length as \<and> i<length as) ** \<upharpoonleft>A (as!i) (cs!i))"  
  by (auto simp: lstr_assn_def sep_algebra_simps pred_lift_extract_simps)
  
lemma lstr_assn_empty: "\<upharpoonleft>(lstr_assn A {}) as cs = \<up>(length cs = length as)"  
  by (auto simp: lstr_assn_def sep_algebra_simps pred_lift_extract_simps)
    
lemma lstr_assn_out_of_range: 
  "\<not>(length cs = length as \<and> (\<forall>i\<in>I. i<length as)) \<Longrightarrow> \<upharpoonleft>(lstr_assn A I) as cs = sep_false"  
  "i\<in>I \<Longrightarrow> \<not>i<length as \<Longrightarrow> \<upharpoonleft>(lstr_assn A I) as cs = sep_false"  
  "i\<in>I \<Longrightarrow> \<not>i<length cs \<Longrightarrow> \<upharpoonleft>(lstr_assn A I) as cs = sep_false"  
  "length cs \<noteq> length as \<Longrightarrow> \<upharpoonleft>(lstr_assn A I) as cs = sep_false"  
  by (auto simp: lstr_assn_def sep_algebra_simps pred_lift_extract_simps)
  
  
  
lemma lstr_assn_idx_left[fri_red_rules]:
  assumes "PRECOND (SOLVE_AUTO (length cs = length as \<and> i\<in>I \<and> i<length as))"
  shows "is_sep_red \<box> (\<upharpoonleft>(lstr_assn A (I-{i})) as cs) (\<upharpoonleft>A ai (cs!i)) (\<upharpoonleft>(lstr_assn A I) (as[i:=ai]) cs)"
proof -

  from assms have [simp]: "{i} - I = {}" "length cs = length as" "i<length as" and "i\<in>I" 
    unfolding vcg_tag_defs by auto

  have "(\<Union>*i\<in>I - {i}. \<upharpoonleft>A (as ! i) (cs ! i)) 
    = (\<Union>*ia\<in>I - {i}. \<upharpoonleft>A (as[i := ai] ! ia) (cs ! ia))"
    by (rule sep_set_img_cong) auto
  then have 1: "\<upharpoonleft>(lstr_assn A (I-{i})) as cs = \<upharpoonleft>(lstr_assn A (I-{i})) (as[i:=ai]) cs"
    by (auto simp: lstr_assn_def sep_algebra_simps pred_lift_extract_simps)
  
  show ?thesis
    using lstr_assn_red[of A "{i}" I "as[i:=ai]" cs]
    by (simp add: 1 lstr_assn_singleton lstr_assn_empty sep_algebra_simps)
    
qed
  
lemma lstr_assn_idx_right[fri_red_rules]:
  assumes "PRECOND (SOLVE_AUTO (i\<in>I))"
  shows "is_sep_red (\<upharpoonleft>(lstr_assn A (I-{i})) as cs) \<box> (\<upharpoonleft>(lstr_assn A I) as cs) (\<upharpoonleft>A (as!i) (cs!i))"
proof -  
  from assms have [simp]: "{i} - I = {}" "i\<in>I" 
    unfolding vcg_tag_defs by auto
  
  show ?thesis
    using lstr_assn_red[of A I "{i}" "as" cs]
    apply (cases "length cs = length as \<and> (\<forall>i\<in>I. i<length as )"; simp add: lstr_assn_out_of_range)
    apply (simp add: lstr_assn_singleton lstr_assn_empty sep_algebra_simps)
    done
qed  
  
(* TODO: Move *)
lemma is_pure_lst_assn[is_pure_rule]: "is_pure A \<Longrightarrow> is_pure (lstr_assn A I)"
  unfolding lstr_assn_def is_pure_def
  by (auto simp: sep_is_pure_assn_conjI sep_is_pure_assn_imgI)
  
lemma vcg_prep_lstr_assn: (* TODO: Need mechanism to recursively prepare pure parts of A! *)
  "pure_part (\<upharpoonleft>(lstr_assn A I) as cs) \<Longrightarrow> length cs = length as \<and> (\<forall>i\<in>I. i<length as)"
  by (auto simp: lstr_assn_def sep_algebra_simps dest: pure_part_split_conj)


(* TODO: Move *)  
lemma pure_fri_auto_rule: "PRECOND (SOLVE_AUTO (\<flat>\<^sub>pA a c)) \<Longrightarrow> \<box> \<turnstile> \<upharpoonleft>\<^sub>pA a c"
  using pure_fri_rule
  unfolding vcg_tag_defs .


lemma pure_part_prepD: "pure_part (\<Union>*i\<in>I. f i) \<Longrightarrow> \<forall>i\<in>I. pure_part (f i)"
  by (metis Set.set_insert pure_part_split_conj sep_set_img_insert)

lemma pure_part_imp_pure_assn: "is_pure A \<Longrightarrow> pure_part (\<upharpoonleft>A a c) \<Longrightarrow> \<flat>\<^sub>pA a c"
  by (simp add: extract_pure_assn)  
  
  
    
definition "aa_assn A \<equiv> mk_assn (\<lambda>as p. EXS cs. 
  \<upharpoonleft>array_assn cs p ** \<up>(is_pure A \<and> list_all2 (\<flat>\<^sub>pA) as cs))"  

   
lemma aa_nth_rule[vcg_rules]: "llvm_htriple 
  (\<upharpoonleft>(aa_assn A) as p ** \<upharpoonleft>snat.assn i ii ** \<up>\<^sub>d(i<length as))
  (array_nth p ii)
  (\<lambda>c. \<upharpoonleft>(aa_assn A) as p ** \<upharpoonleft>A (as!i) c)"
  unfolding aa_assn_def
  apply (clarsimp simp: list_all2_conv_all_nth)
  supply pure_fri_auto_rule[fri_rules]
  apply vcg
  done  

lemma aa_upd_rule[vcg_rules]: "llvm_htriple 
  (\<upharpoonleft>(aa_assn A) as p ** \<upharpoonleft>snat.assn i ii ** \<upharpoonleft>A a c ** \<up>\<^sub>d(i<length as))
  (array_upd p ii c)
  (\<lambda>c. \<upharpoonleft>(aa_assn A) (as[i:=a]) p)"
proof (cases "is_pure A")
  case [is_pure_rule,simp]: True
  (*note thin_dr_pure[vcg_prep_external_drules del]*)
  note [simp] = nth_list_update pure_part_imp_pure_assn
  
  show ?thesis
    unfolding aa_assn_def list_all2_conv_all_nth
    supply pure_fri_auto_rule[fri_rules]
    apply vcg
    done
qed (clarsimp simp: aa_assn_def)      




definition [llvm_inline]: "qs_swap A i j \<equiv> doM {
  llc_if (ll_cmp' (i\<noteq>j)) (doM {
    x \<leftarrow> array_nth A i;
    y \<leftarrow> array_nth A j;
    array_upd A i y;
    array_upd A j x;
    return ()
  }) (return ())
}"

definition [llvm_code]: "qs_partition A lo hi \<equiv> doM {
  hi \<leftarrow> ll_sub hi (signed_nat 1);
  pivot \<leftarrow> array_nth A hi;
  let i = lo;
  
  i \<leftarrow> llc_for_range lo hi (\<lambda>j i. doM {
    Aj \<leftarrow> array_nth A j;
    if Aj < pivot then doM {
      qs_swap A i j;
      i \<leftarrow> ll_add i (signed_nat 1);
      return i
    } else return i
  }) i;
  
  qs_swap A i hi;
  return i
}"


definition [llvm_code]: "qs_quicksort A lo hi \<equiv> doM {
  REC (\<lambda>quicksort (lo,hi). doM {
    if lo < hi then doM {
      p \<leftarrow> qs_partition A lo hi;
      quicksort (lo, p-1);
      quicksort (p+1,hi)
    } else
      return ()
  
  }) (lo,hi);
  return ()
}"

(* TODO: Prepare-code-thms after inlining! *)
(* prepare_code_thms  qs_partition_def[unfolded llc_for_range_def] *)


(*prepare_code_thms [llvm_code] qs_quicksort_def*)


llvm_deps foo: "qs_quicksort :: 64 word ptr \<Rightarrow> 64 word \<Rightarrow> 64 word \<Rightarrow> unit llM"


export_llvm "qs_quicksort :: 64 word ptr \<Rightarrow> 64 word \<Rightarrow> 64 word \<Rightarrow> unit llM" is "qs_quicksort"
  file \<open>code/qs_quicksort.ll\<close>

  
lemma qs_swap_aa_rule[vcg_rules]: "llvm_htriple 
  (\<upharpoonleft>(aa_assn A) xs p ** \<upharpoonleft>snat.assn i ii ** \<upharpoonleft>snat.assn j ji ** \<up>\<^sub>d(i<length xs \<and> j<length xs))
  (qs_swap p ii ji)
  (\<lambda>_. \<upharpoonleft>(aa_assn A) (swap xs i j) p)"  
  unfolding qs_swap_def swap_def
  apply vcg_monadify
  apply vcg'
  done
  
lemma qs_swap_rule[vcg_rules]: "llvm_htriple 
  (\<upharpoonleft>array_assn xs A ** \<upharpoonleft>snat.assn i ii ** \<upharpoonleft>snat.assn j ji ** \<up>\<^sub>d(i<length xs \<and> j<length xs))
  (qs_swap A ii ji)
  (\<lambda>_. \<upharpoonleft>array_assn (swap xs i j) A)"  
  unfolding qs_swap_def swap_def
  apply vcg_monadify
  apply vcg'
  done
  

  
    
fun at_idxs :: "'a list \<Rightarrow> nat list \<Rightarrow> 'a list" (infixl "\<exclamdown>" 100) where
  "at_idxs xs [] = []"
| "at_idxs xs (i#is) = xs!i # at_idxs xs is"  
  
lemma at_idxs_eq_map_nth: "at_idxs xs is = map (nth xs) is"
  by (induction "is") auto

lemma at_idxs_append[simp]: "at_idxs xs (is\<^sub>1@is\<^sub>2) = at_idxs xs is\<^sub>1 @ at_idxs xs is\<^sub>2"  
  by (induction is\<^sub>1) auto
  
lemma at_idxs_ran_zero: "hi\<le>length xs \<Longrightarrow> at_idxs xs [0..<hi] = take hi xs"  
  by (induction hi) (auto simp: take_Suc_conv_app_nth)
  
lemma at_idxs_slice: "hi\<le>length xs \<Longrightarrow> at_idxs xs [lo..<hi] = Misc.slice lo hi xs"
  apply (induction lo)
  apply (auto simp: Misc.slice_def at_idxs_ran_zero)
  by (simp add: at_idxs_eq_map_nth drop_take map_nth_upt_drop_take_conv)

(* TODO: Move *)     
lemma pure_part_split_img:
  assumes "pure_part (\<Union>*i\<in>I. f i)"  
  shows "(\<forall>i\<in>I. pure_part (f i))"  
proof (cases "finite I")
  assume "finite I"
  then show ?thesis using assms
    by (induction) (auto dest: pure_part_split_conj)
next
  assume "infinite I" with assms show ?thesis by simp    
qed

  
lemma "pure_part (\<upharpoonleft>(lstr_assn A I) as cs) \<Longrightarrow> (length cs = length as) \<and> (\<forall>i\<in>I. i<length as \<and> pure_part (\<upharpoonleft>A (as!i) (cs!i)))"
  by (auto simp: lstr_assn_def is_pure_def list_all2_conv_all_nth sep_algebra_simps 
    dest!: pure_part_split_conj pure_part_split_img)

(* TODO: Move *)    
lemma lstr_assn_insert: "i\<notin>I \<Longrightarrow> \<upharpoonleft>(lstr_assn A (insert i I)) as cs = (\<up>(i < length as) ** \<upharpoonleft>A (as!i) (cs!i) ** \<upharpoonleft>(lstr_assn A I) as cs)"
  by (auto simp: lstr_assn_def sep_algebra_simps pred_lift_extract_simps)
    

lemma fri_lstr_pure_rl[fri_rules]:
  "PRECOND (SOLVE_ASM (\<flat>\<^sub>p(lstr_assn A I) as cs)) \<Longrightarrow> PRECOND (SOLVE_AUTO (i\<in>I)) \<Longrightarrow> \<box> \<turnstile> \<upharpoonleft>\<^sub>pA (as!i) (cs!i)"
  unfolding vcg_tag_defs
  by (auto simp: dr_assn_pure_asm_prefix_def lstr_assn_insert dr_assn_pure_prefix_def
    simp: sep_algebra_simps
    elim!: Set.set_insert dest!: pure_part_split_conj)
  

lemma length_swap[simp]: "length (swap xs i j) = length xs"
  by (auto simp: swap_def)    

  
lemma at_idxs_cong:
  assumes "\<And>i. i\<in>List.set I \<Longrightarrow> xs!i = ys!i"
  shows "xs\<exclamdown>I = ys\<exclamdown>I"
  using assms 
  apply (induction I)
  apply auto
  done
    
lemma at_idxs_upd_out[simp]: "i\<notin>List.set I \<Longrightarrow> xs[i:=x] \<exclamdown> I = xs\<exclamdown>I"
  by (auto intro: at_idxs_cong simp: nth_list_update')
  
lemma at_idxs_swap_out[simp]: "i\<notin>List.set I \<Longrightarrow> j\<notin>List.set I \<Longrightarrow> (swap xs i j)\<exclamdown>I = xs\<exclamdown>I"  
  unfolding swap_def
  by auto

lemma mset_swap'[simp]: "\<lbrakk>i<length xs; j<length xs\<rbrakk> \<Longrightarrow> mset (swap xs i j) = mset xs"
  unfolding swap_def
  apply (auto simp: mset_swap)
  done  
  
  
find_theorems at_idxs Misc.slice  
find_theorems mset nth    


        
lemma "llvm_htriple 
  (\<upharpoonleft>(aa_assn snat.assn) as A ** \<upharpoonleft>snat.assn lo loi  ** \<upharpoonleft>snat.assn hi hii 
    ** \<up>\<^sub>d(lo<hi \<and> hi\<le>length as)) 
  (qs_partition A loi hii)
  (\<lambda>pi. EXS as' p. \<upharpoonleft>(aa_assn snat.assn) as' A ** \<upharpoonleft>snat.assn p pi 
    ** \<up>( lo\<le>p \<and> p<hi 
        \<and> length as' = length as
        \<and> as'\<exclamdown>[0..<lo] = as\<exclamdown>[0..<lo]     
        \<and> as'\<exclamdown>[hi..<length as] = as\<exclamdown>[hi..<length as]
        \<and> mset (as') = mset (as)
        \<and> (\<forall>i\<in>{lo..<p}. as!i \<le> as!p)
        \<and> (\<forall>i\<in>{p..<hi}. as!p \<le> as!i)
         ))"
  unfolding qs_partition_def
  apply (rewrite annotate_llc_for_range[where 
    I="\<lambda>j ii. EXS i as'. \<upharpoonleft>snat.assn i ii ** \<upharpoonleft>(aa_assn snat.assn) as' A 
      ** \<up>(length as'=length as 
        \<and> lo\<le>i \<and> i<hi
        \<and> as'\<exclamdown>[0..<lo] = as\<exclamdown>[0..<lo]     
        \<and> as'\<exclamdown>[hi..<length as] = as\<exclamdown>[hi..<length as]
        \<and> mset (as') = mset (as)
      )
    
    "])
  apply vcg_monadify
  apply vcg'
  apply clarsimp_all
  apply auto
  prefer 2
  apply (subst at_idxs_swap_out)
  apply simp 
  apply simp
  apply linarith
  apply simp
  oops 
(*  
xxx, ctd here: sharpen invariant!
  
    
  xxx, try "arr_assn A \<equiv> array o lst A"
  try to set up rules for nth and upd, using a set of externalized indexes (and their intermediate values).
    supplement frame inference by internalize/externalize rules
  
  
  
  
  apply vcg_try_solve
  apply vcg_try_solve
  
  apply vcg_rl back back
  apply vcg_try_solve
  apply (fri_dbg_step) back
  apply vcg_try_solve
  
  
  
  oops
  xxx, ctd here: Intro-trule for pure lstr-assn
  
  oops
  xxx, ctd here: The array itself contains data, which needs to be abstracted over!
    we will need to relate xs!i to some abstract value!
  

  oops
  
  
  
  
  xxx, integrate reduction rules into frame inference!
  xxx: simplify the resulting set differences during frame inference!
    Most important: Elimination of empty sets!
    
      


  xxx, ctd here: Integrate into frame inference  
    "cut" is a bad name for this concept
        
        
  find_theorems sep_set_img  
    
  ML_val \<open>@{term \<open>\<Union>*x\<in>y. p\<close>}\<close>  
    
  lemma
    assumes "\<upharpoonleft>(lstr_assn A (I-I')) as cs \<turnstile> \<upharpoonleft>(lstr_assn A (I'-I)) as cs"  
    shows "\<upharpoonleft>(lstr_assn A I) as cs \<turnstile> \<upharpoonleft>(lstr_assn A I') as cs"
    
    
    oops
  xxx, ctd here: do list_assn, with index set. 
  
  derive rules to split/join those assertions. also rules for pure-case.
  in practice, let the lstr-assertions fragment, until some rule/frame forces a re-union.
    
    
    
      
    
      
  thm vcg_frame_erules
  
  apply vcg_rl
         
         
  
term "xs\<exclamdown>[2..<5]"

find_consts "nat \<Rightarrow> nat \<Rightarrow> _ list \<Rightarrow> _ list"  
  
*)  
  
  

end

