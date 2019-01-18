section \<open>LLVM Shallow Embedding --- Reasoning Setup\<close>
theory LLVM_Shallow_RS
imports 
  "Monadify"
  LLVM_Shallow
  LLVM_Memory_RS
  
begin


subsection \<open>Monadification Setup for VCG\<close>

ML \<open>
  structure LLVM_VCG_Monadify = struct
    structure Monadify = Gen_Monadify_Cong (
    
      fun mk_return x = @{mk_term "return ?x ::_ llM"}
      fun mk_bind m f = @{mk_term "bind ?m ?f ::_ llM"}
    
      fun dest_return @{mpat "return ?x ::_ llM"} = SOME x | dest_return _ = NONE
      fun dest_bind @{mpat "bind ?m ?f ::_ llM"} = SOME (m,f) | dest_bind _ = NONE
      
      fun dest_monadT (Type (@{type_name M},[T,@{typ unit},@{typ llvm_memory},@{typ err}])) = SOME T | dest_monadT _ = NONE
      val bind_return_thm = @{lemma "bind m return = m" by simp}
      val return_bind_thm = @{lemma "bind (return x) f = f x" by simp}
      val bind_bind_thm = @{lemma "bind (bind m (\<lambda>x. f x)) g = bind m (\<lambda>x. bind (f x) g)" by simp}
      
    )
    
    val _ = Theory.setup
     (Attrib.setup \<^binding>\<open>vcg_const\<close>
      (Args.term >> (fn t => Thm.declaration_attribute (K (Monadify.prepare_add_const_decl t))))
      "declaration of new coercions")

    fun monadify_all_tac ctxt = CONVERSION (Conv.top_sweep_conv (Monadify.monadify_conv) ctxt)
      
  end
\<close>

named_theorems vcg_monadify_xforms

method_setup vcg_monadify_raw = \<open>Scan.succeed (SIMPLE_METHOD' o LLVM_VCG_Monadify.monadify_all_tac)\<close>
method vcg_monadify_xform_raw = (simp only: vcg_monadify_xforms)?


(* xform (monadify xform)+ *)
method vcg_monadify uses simp = 
  vcg_monadify_xform_raw; ((changed \<open>vcg_monadify_raw; vcg_monadify_xform_raw\<close>)+)?


(* TODO: Automatically do monadification when preparing Hoare triple! *)

declare llvm_inline_bind_laws[vcg_monadify_xforms]


subsection \<open>Abbreviations for VCG\<close>

type_synonym ll_assn = "(llvm_amemory \<Rightarrow> bool)"
abbreviation llvm_htriple 
  :: "ll_assn \<Rightarrow> 'a llM \<Rightarrow> ('a \<Rightarrow> ll_assn) \<Rightarrow> bool" 
  where "llvm_htriple \<equiv> htriple llvm_\<alpha>"
abbreviation llvm_htripleF 
  :: "ll_assn \<Rightarrow> ll_assn \<Rightarrow> 'a llM \<Rightarrow> ('a \<Rightarrow> ll_assn) \<Rightarrow> bool" 
  where "llvm_htripleF \<equiv> htripleF llvm_\<alpha>"
abbreviation "llSTATE \<equiv> STATE llvm_\<alpha>"
abbreviation "llPOST \<equiv> POSTCOND llvm_\<alpha>"

locale llvm_prim_setup
(* Locale to contain primitive VCG setup, without data refinement *)

subsection \<open>General VCG Setup\<close>
lemma fri_extract_prod_case[fri_extract_simps]: "(case p of (a,b) \<Rightarrow> (P a b :: ll_assn)) = (EXS a b. \<up>(p=(a,b)) ** P a b)"  
  apply (cases p) apply (rule ext)
  apply (auto simp: sep_algebra_simps pred_lift_extract_simps)
  done
  
lemma norm_prod_case[vcg_normalize_simps]:
  "wp (case p of (a,b) \<Rightarrow> f a b) Q s \<longleftrightarrow> (\<forall>a b. p=(a,b) \<longrightarrow> wp (f a b) Q s)" 
  by (auto split: prod.split) 


subsection \<open>Assertions\<close>

  
typedef ('a,'c) dr_assn = "UNIV :: ('a \<Rightarrow> 'c \<Rightarrow> ll_assn) set" by simp
setup_lifting type_definition_dr_assn
  
lemma dr_assn_inverses[simp]:
  "Abs_dr_assn (Rep_dr_assn A) = A"
  "Rep_dr_assn (Abs_dr_assn B) = B"
  using Rep_dr_assn_inverse Abs_dr_assn_inverse by auto

definition dr_assn_prefix :: "('a, 'b) dr_assn \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> ll_assn" ("\<upharpoonleft>_" [1000] 1000) where
  "\<upharpoonleft>A a c \<equiv> Rep_dr_assn A a c"
  
definition "is_pure A \<equiv> \<forall>a c. sep_is_pure_assn (\<upharpoonleft>A a c)"

definition dr_assn_pure_prefix ("\<upharpoonleft>\<^sub>p_" [1000] 1000) where  
  "\<upharpoonleft>\<^sub>pA a c \<equiv> \<up>pure_part (\<upharpoonleft>A a c) (** \<up>(is_pure A) *)"
  
definition dr_assn_pure_asm_prefix ("\<flat>\<^sub>p_" [1000] 1000) where  
  "\<flat>\<^sub>pA a c \<equiv> pure_part (\<upharpoonleft>A a c) \<and> is_pure A"
  
lemma pure_fri_rule[fri_rules]: "PRECOND (SOLVE_ASM (\<flat>\<^sub>pA a c)) \<Longrightarrow> \<box> \<turnstile> \<upharpoonleft>\<^sub>pA a c"  
  unfolding vcg_tag_defs entails_def dr_assn_pure_prefix_def dr_assn_pure_asm_prefix_def
    is_pure_def
  apply clarsimp
  apply (subst pure_part_pure_eq[symmetric])  
  apply (auto simp: sep_algebra_simps)
  done

lemma prepare_pure_assn[fri_prepare_simps]: "\<upharpoonleft>A a c = \<upharpoonleft>\<^sub>pA a c" if "is_pure A"
  using that 
  by (simp add: dr_assn_pure_prefix_def is_pure_def)

lemma extract_pure_assn[fri_extract_simps]: "\<upharpoonleft>A a c = \<up>\<flat>\<^sub>pA a c" if "is_pure A"
  using that
  unfolding vcg_tag_defs entails_def dr_assn_pure_asm_prefix_def is_pure_def
  apply (auto simp: sep_algebra_simps)
  done
  
attribute_setup is_pure_rule = \<open>Attrib.add_del 
    (VCG_Lib.chained_decl_attr @{context} @{attributes [fri_prepare_simps, fri_extract_simps]})
    (VCG_Lib.chained_decl_attr @{context} @{attributes [fri_prepare_simps del, fri_extract_simps del]})
  \<close>
  \<open>Rules to introduce pure assertions\<close>


lemma prep_ext_state[vcg_prep_external_drules]: 
  "llSTATE P s \<Longrightarrow> pure_part P"  
  unfolding STATE_def by (blast intro: pure_partI)
  
lemma prep_ext_pure_part_pure[vcg_prep_external_drules]: 
  "pure_part (\<upharpoonleft>\<^sub>pA a c) \<Longrightarrow> pure_part (\<upharpoonleft>A a c)"  
  unfolding dr_assn_pure_prefix_def by simp
  
text \<open>This rule is to be overloaded by later rules\<close>  
lemma thin_dr_pure[vcg_prep_external_drules]: "pure_part (\<upharpoonleft>A a c) \<Longrightarrow> True" ..
    
lemma thin_dr_pure_asm[vcg_prep_external_drules]: "(\<flat>\<^sub>pA a c) \<Longrightarrow> pure_part (\<upharpoonleft>A a c)"
  unfolding dr_assn_pure_asm_prefix_def by simp
  
definition "mk_assn \<equiv> Abs_dr_assn"  
definition "mk_pure_assn A \<equiv> mk_assn (\<lambda>a c. \<up>A a c)"  

lemma is_pure_mk_pure[simp]: "is_pure (mk_pure_assn A)"
  unfolding is_pure_def mk_pure_assn_def mk_assn_def dr_assn_prefix_def
  by (auto)

lemma sel_mk_assn[simp]: "\<upharpoonleft>(mk_assn A) a c = A a c"  
  by (auto simp: mk_assn_def dr_assn_prefix_def)
  
lemma sel_mk_pure_assn[simp]: 
  "\<upharpoonleft>(mk_pure_assn A) a c = \<up>(A a c)"
  "\<upharpoonleft>\<^sub>p(mk_pure_assn A) a c = \<up>(A a c)"
  "\<flat>\<^sub>p(mk_pure_assn A) a c = A a c"
  apply (auto simp: mk_pure_assn_def dr_assn_pure_prefix_def dr_assn_pure_asm_prefix_def)
  apply (auto simp: mk_assn_def is_pure_def dr_assn_prefix_def sep_algebra_simps)
  done
  
lemma mk_pure_assn_extractI:
  assumes "pure_part (\<upharpoonleft>(mk_pure_assn A) a c)"
  assumes "A a c \<Longrightarrow> \<Phi> a c"
  shows "\<Phi> a c"
  using assms
  by auto

lemma mk_assn_extractI:  
  assumes "pure_part (\<upharpoonleft>(mk_assn A) a c)"
  assumes "A a c \<turnstile> \<up>\<Phi> a c ** sep_true"
  shows "\<Phi> a c"
  using assms
  by (auto simp: entails_def sep_conj_def pred_lift_def sep_algebra_simps)
  
lemma mk_assn_extractI':
  assumes "pure_part (\<upharpoonleft>(mk_assn A) a c)"
  assumes "FRAME (A a c) (\<up>\<Phi> a c) F"
  shows "\<Phi> a c"
  apply (rule mk_assn_extractI[OF assms(1)])
  using assms(2) unfolding FRAME_def
  by (metis (no_types, lifting) entails_def entails_mp sep_conj_commute)
  
    
(* Use as [fri_rules] to for 'matching' of abstract values by auto during frame inference *)
lemma fri_abs_cong_rl: "PRECOND (SOLVE_AUTO (a=a')) \<Longrightarrow> \<upharpoonleft>A a c \<turnstile> \<upharpoonleft>A a' c"  
  unfolding vcg_tag_defs by auto

  

subsection \<open>Memory Reasoning\<close>
locale llvm_prim_mem_setup
sublocale llvm_prim_setup < llvm_prim_mem_setup .

subsubsection \<open>Pointers\<close>

text \<open>Assertion for pointer to single value\<close>
definition ll_pto :: "('a::llvm_rep, 'a ptr) dr_assn"
  where "ll_pto \<equiv> mk_assn (\<lambda>v p. llvm_pto (to_val v) (the_raw_ptr p))"

instantiation ptr :: (llvm_rep) addr_algebra begin  
  definition "abase \<equiv> abase o the_raw_ptr"
  definition "acompat a b \<equiv> acompat (the_raw_ptr a) (the_raw_ptr b)"
  definition "adiff a b \<equiv> adiff (the_raw_ptr a) (the_raw_ptr b)"
  definition aidx_ptr :: "'a ptr \<Rightarrow> int \<Rightarrow> 'a ptr" where "aidx a i \<equiv> PTR (aidx (the_raw_ptr a) i)"
  
  instance
    apply standard
    apply (intro part_equivpI sympI transpI)
    unfolding abase_ptr_def acompat_ptr_def adiff_ptr_def aidx_ptr_def
    apply (metis acompat_equiv part_equivp_def ptr.sel)
    apply (auto intro: acompat_sym acompat_trans simp: acompat_dom)
    done

end
  
  
text \<open>Assertion to range of array\<close>  
definition "ll_range I \<equiv> mk_assn (\<lambda>f p. \<up>(abase p) ** (\<Union>*i\<in>I. \<upharpoonleft>ll_pto (f i) (p +\<^sub>a i)))"

lemma ll_range_preep_pure[vcg_prep_external_drules]: 
  "pure_part (\<upharpoonleft>(ll_range I) f p) \<Longrightarrow> abase p"
  unfolding ll_range_def
  apply (erule mk_assn_extractI')
  by vcg_try_solve
  
lemma ll_range_not_base: "\<not>abase p \<Longrightarrow> \<upharpoonleft>(ll_range I) f p = sep_false"
  unfolding ll_range_def by auto

lemma null_not_base[simp]: "\<not>abase null"  
  apply (auto simp: abase_ptr_def null_def)
  apply (auto simp: abase_llvm_ptr_def llvm_null_def)
  done
  
lemma ll_range_not_null[simp]: "\<upharpoonleft>(ll_range I) f null = sep_false"
  by (simp add: ll_range_not_base)
  
    
lemma ll_pto_not_same: "(\<upharpoonleft>ll_pto x p ** \<upharpoonleft>ll_pto y p) = sep_false"
  apply (rule ext)
  apply (auto simp: ll_pto_def llvm_pto_def ab.ba.pto_def split: rptr.splits addr.splits)
  apply (auto simp: sep_algebra_simps sep_conj_def)
  apply (auto simp: sep_disj_llvm_amemory_def sep_algebra_simps ab.pto_def split: baddr.splits)
  apply (auto simp: vpto_assn_def)
  done


lemma ll_range_merge: "I\<^sub>1\<inter>I\<^sub>2={} \<Longrightarrow> (\<upharpoonleft>(ll_range I\<^sub>1) f p ** \<upharpoonleft>(ll_range I\<^sub>2) f p) = \<upharpoonleft>(ll_range (I\<^sub>1\<union>I\<^sub>2)) f p"
  unfolding ll_range_def
  by (auto simp: sep_algebra_simps)

lemma ll_range_bogus_upd[simp]: "x\<notin>I \<Longrightarrow> \<upharpoonleft>(ll_range I) (f(x:=v)) p = \<upharpoonleft>(ll_range I) f p"  
  unfolding ll_range_def
  apply (cases "abase p"; simp add: sep_algebra_simps)
  by (rule sep_set_img_cong) (auto)
  
  
lemma open_ll_range: "i\<in>I \<Longrightarrow> \<upharpoonleft>(ll_range I) f p = (\<up>abase p ** \<upharpoonleft>ll_pto (f i) (p +\<^sub>a i) ** \<upharpoonleft>(ll_range (I-{i})) f p)"
  unfolding ll_range_def
  apply (cases "abase p"; simp add: sep_algebra_simps)
  by (auto simp:  sep_set_img_remove)

lemma 
  assumes "I\<inter>I'\<noteq>{}"  
  assumes "F \<turnstile> \<upharpoonleft>(ll_range (I'-I)) f p ** F'"
  shows "\<upharpoonleft>(ll_range I) f p ** F \<turnstile> \<upharpoonleft>(ll_range I') f p ** \<upharpoonleft>(ll_range (I-I')) f p ** F'"
proof -
  have "\<upharpoonleft>(ll_range I) f p ** F \<turnstile> \<upharpoonleft>(ll_range I) f p ** \<upharpoonleft>(ll_range (I'-I)) f p ** F'"
    using assms(2) conj_entails_mono by blast
  also have "\<dots> = (\<upharpoonleft>(ll_range (I \<union> (I'-I))) f p ** F')"
    apply (subst ll_range_merge[symmetric])
    by auto
  also have "\<dots> = ((\<upharpoonleft>(ll_range I') f p ** \<upharpoonleft>(ll_range (I-I')) f p) ** F')"
    apply (rewrite in "_=\<hole>" ll_range_merge)
    apply (auto simp: Un_commute)
    done
  finally show ?thesis by simp  
qed    
    
  
subsubsection \<open>Load and Store\<close>
context llvm_prim_mem_setup begin
lemma checked_from_val_rule[vcg_rules]: "llvm_htriple \<box> (checked_from_val (to_val x)) (\<lambda>r. \<up>(r=x))"  
  unfolding checked_from_val_def
  by vcg
  
text \<open>Standard rules for load and store from pointer\<close>  
lemma ll_load_rule[vcg_rules]: "llvm_htriple (\<upharpoonleft>ll_pto x p) (ll_load p) (\<lambda>r. \<up>(r=x) ** \<upharpoonleft>ll_pto x p)"
  unfolding ll_load_def ll_pto_def 
  by vcg

lemma ll_store_rule[vcg_rules]: "llvm_htriple (\<upharpoonleft>ll_pto xx p) (ll_store x p) (\<lambda>_. \<upharpoonleft>ll_pto x p)"
  unfolding ll_store_def ll_pto_def
  by vcg
  
text \<open>Rules for load and store from indexed pointer, wrt. range\<close>  

lemmas [fri_extract_simps] = sep_conj_assoc


find_theorems htriple EXTRACT
thm vcg_decomp_rules

lemma ll_load_rule_range[vcg_rules]:
  shows "llvm_htriple (\<upharpoonleft>(ll_range I) a p ** \<up>\<^sub>!( p' ~\<^sub>a p \<and> p' -\<^sub>a p \<in> I )) (ll_load p') (\<lambda>r. \<up>(r = a (p' -\<^sub>a p)) ** \<upharpoonleft>(ll_range I) a p)"
  unfolding vcg_tag_defs
  apply (rule htriple_vcgI')
  apply fri_extract_basic
  apply (simp add: open_ll_range)
  apply fri_extract
  apply vcg
  done

lemma ll_store_rule_range[vcg_rules]:
  shows "llvm_htriple (\<upharpoonleft>(ll_range I) a p ** \<up>\<^sub>!( p' ~\<^sub>a p \<and> p' -\<^sub>a p \<in> I )) (ll_store x p') (\<lambda>_. \<upharpoonleft>(ll_range I) (a(p' -\<^sub>a p := x)) p)"
  unfolding vcg_tag_defs
  apply (rule htriple_vcgI')
  apply fri_extract_basic
  apply (simp add: open_ll_range)
  apply fri_extract
  by vcg

subsubsection \<open>Offsetting Pointers\<close>

(* TODO: The LLVM semantics also allows pointers one past the end of a range, 
  which is not supported by these rules yet.
*)

text \<open>Rule for indexing pointer. Note, the new target address must exist\<close>
lemma ll_ofs_ptr_rule[vcg_rules]: 
  "llvm_htriple 
    (\<upharpoonleft>ll_pto v (p +\<^sub>a (sint i)) ** \<up>\<^sub>!(abase p))
    (ll_ofs_ptr p i) 
    (\<lambda>r. \<up>(r= p +\<^sub>a (sint i)) ** \<upharpoonleft>ll_pto v (p +\<^sub>a (sint i)))"
  unfolding ll_ofs_ptr_def ll_pto_def abase_ptr_def aidx_ptr_def
  by vcg

text \<open>Rule for indexing pointer into range. Note, the new target address must exist\<close>
  
lemma ll_ofs_ptr_rule'[vcg_rules]: 
  shows "llvm_htriple 
    (\<upharpoonleft>(ll_range I) x p ** \<up>\<^sub>!(p ~\<^sub>a p' \<and> (p' +\<^sub>a sint i) -\<^sub>a p \<in> I)) 
    (ll_ofs_ptr p' i) 
    (\<lambda>r. \<up>(r= p' +\<^sub>a sint i) ** \<upharpoonleft>(ll_range I) x p)"
  unfolding vcg_tag_defs
  apply (rule htriple_vcgI')
  apply fri_extract_basic
  apply (simp add: open_ll_range vcg_tag_defs)
  apply fri_extract
  apply vcg
  done

  
subsubsection \<open>Allocate and Free\<close>

text \<open>Memory allocation tag, which expresses ownership of an allocated block.\<close>
definition ll_malloc_tag :: "int \<Rightarrow> 'a::llvm_rep ptr \<Rightarrow> _" 
  where "ll_malloc_tag n p \<equiv> \<up>(n\<ge>0) ** llvm_malloc_tag n (the_raw_ptr p)"

text \<open>Allocation returns an array-base pointer to an initialized range, 
  as well as an allocation tag\<close>
lemma ll_malloc_rule[vcg_rules]: 
  "llvm_htriple 
    (\<up>(n\<noteq>0)) 
    (ll_malloc TYPE('a::llvm_rep) n) 
    (\<lambda>r. \<upharpoonleft>(ll_range {0..< uint n}) (\<lambda>_. init) r ** ll_malloc_tag (uint n) r)"
  unfolding ll_malloc_def ll_pto_def ll_malloc_tag_def ll_range_def 
  supply [simp] = list_conj_eq_sep_set_img uint_nat abase_ptr_def aidx_ptr_def unat_gt_0
  apply vcg
  done

  
text \<open>Free takes a range and the matching allocation tag\<close>
lemma ll_free_rule[vcg_rules]:
  "llvm_htriple 
    (\<upharpoonleft>(ll_range {0..<n}) blk p ** ll_malloc_tag n p)
    (ll_free p)
    (\<lambda>_. \<box>)
  "
  unfolding ll_free_def ll_pto_def ll_malloc_tag_def ll_range_def vcg_tag_defs
  supply [simp] = list_conj_eq_sep_set_img abase_ptr_def aidx_ptr_def 
  supply [fri_prepare_simps] = sep_set_img_pull_EXS
  by vcg
  
end  

  
subsection \<open>Arithmetic Instructions\<close>
  
text \<open>Tag for arithmetic bounds check proof obligations\<close>
definition [vcg_tag_defs]: "WBOUNDS \<Phi> \<longleftrightarrow> \<Phi>"  
lemma WBOUNDSI: "\<Phi> \<Longrightarrow> WBOUNDS \<Phi>" by (simp add: WBOUNDS_def)
lemma WBOUNDSD: "WBOUNDS \<Phi> \<Longrightarrow> \<Phi>" by (simp add: WBOUNDS_def)
declaration \<open>K (Basic_VCG.add_solver (@{thms WBOUNDSI},@{binding solve_wbounds},fn ctxt => SELECT_GOAL (auto_tac ctxt)))\<close>
  
  
abbreviation "in_srange op (a::'a::len word) (b::'a word) \<equiv> op (sint a) (sint b) \<in> sints (LENGTH ('a))"
      
lemma udivrem_is_undef_word_conv:
  fixes a b :: "'a::len word"
  shows "udivrem_is_undef (word_to_lint a) (word_to_lint b) \<longleftrightarrow> b=0"  
  by (auto simp: udivrem_is_undef_def word_to_lint_to_uint_0_iff)
  
lemma sdivrem_is_undef_word_conv:
  fixes a b :: "'a::len word"
  shows "sdivrem_is_undef (word_to_lint a) (word_to_lint b) \<longleftrightarrow> b=0 \<or> \<not>in_srange (sdiv) a b"  
  by (auto simp: sdivrem_is_undef_def sdivrem_ovf_def word_to_lint_to_sint_conv)
  
  
subsubsection \<open>VCG Simplifications and Rules\<close>  
text \<open>
  Most of the rules for arithmetic are set up as simplifications.
  For operations with side-conditions, we have both, 
  a conditional simplification rule and a Hoare-rule. 
  Note that the Hoare-rule will only be tried if the simplification rule did not 
  succeed.
\<close>
  
lemma cond_llvm_htripleI: "x = return y \<Longrightarrow> llvm_htriple \<box> x (\<lambda>r. \<up>(r=y))" by vcg


locale llvm_prim_arith_setup

sublocale llvm_prim_setup < llvm_prim_arith_setup .
  
context llvm_prim_arith_setup begin
context 
  notes [simp] = op_lift_arith2'_def op_lift_arith2_def 
                  op_lift_cmp_def op_lift_ptr_cmp_def op_lift_iconv_def 
  notes [simp] = word_to_lint_convs[symmetric]
  notes [simp] = from_bool_lint_conv udivrem_is_undef_word_conv sdivrem_is_undef_word_conv
  notes [simp] = word_to_lint_to_uint_conv word_to_lint_to_sint_conv
begin

paragraph \<open>Arithmetic\<close>

lemma ll_add_simp[vcg_normalize_simps]: "ll_add a b = return (a + b)" by (auto simp: ll_add_def)
lemma ll_sub_simp[vcg_normalize_simps]: "ll_sub a b = return (a - b)" by (auto simp: ll_sub_def)
lemma ll_mul_simp[vcg_normalize_simps]: "ll_mul a b = return (a * b)" by (auto simp: ll_mul_def)
lemma ll_udiv_simp[vcg_normalize_simps]: "b\<noteq>0 \<Longrightarrow> ll_udiv a b = return (a div b)" by (auto simp: ll_udiv_def)
lemma ll_urem_simp[vcg_normalize_simps]: "b\<noteq>0 \<Longrightarrow> ll_urem a b = return (a mod b)" by (auto simp: ll_urem_def)

lemma ll_sdiv_simp[vcg_normalize_simps]: "\<lbrakk>b\<noteq>0; in_srange (sdiv) a b\<rbrakk> \<Longrightarrow> ll_sdiv a b = return (a sdiv b)" 
  by (auto simp: ll_sdiv_def Let_def)
lemma ll_srem_simp[vcg_normalize_simps]: "\<lbrakk>b\<noteq>0; in_srange (sdiv) a b\<rbrakk> \<Longrightarrow> ll_srem a b = return (a smod b)" 
  by (auto simp: ll_srem_def)

lemma ll_udiv_rule[vcg_rules]: "WBOUNDS (b\<noteq>0) \<Longrightarrow> llvm_htriple \<box> (ll_udiv a b) (\<lambda>r. \<up>(r = a div b))" 
  unfolding vcg_tag_defs by vcg
lemma ll_urem_rule[vcg_rules]: "WBOUNDS (b\<noteq>0) \<Longrightarrow> llvm_htriple \<box> (ll_urem a b) (\<lambda>r. \<up>(r = a mod b))" 
  unfolding vcg_tag_defs by vcg
lemma ll_sdiv_rule[vcg_rules]: "\<lbrakk>WBOUNDS (b\<noteq>0); WBOUNDS (in_srange (sdiv) a b)\<rbrakk> \<Longrightarrow> llvm_htriple \<box> (ll_sdiv a b) (\<lambda>r. \<up>(r = a sdiv b))"
  unfolding vcg_tag_defs by vcg
lemma ll_srem_rule[vcg_rules]: "\<lbrakk>WBOUNDS (b\<noteq>0); WBOUNDS (in_srange (sdiv) a b)\<rbrakk> \<Longrightarrow> llvm_htriple \<box> (ll_srem a b) (\<lambda>r. \<up>(r = a smod b))"
  unfolding vcg_tag_defs by vcg

paragraph \<open>Comparison\<close>
lemma ll_icmp_simps[vcg_normalize_simps]: 
  "ll_icmp_eq a b = return (from_bool (a = b))" 
  "ll_icmp_ne a b = return (from_bool (a \<noteq> b))" 
  "ll_icmp_sle a b = return (from_bool (a <=s b))" 
  "ll_icmp_slt a b = return (from_bool (a <s b))" 
  "ll_icmp_ule a b = return (from_bool (a \<le> b))" 
  "ll_icmp_ult a b = return (from_bool (a < b))" 
  unfolding ll_icmp_eq_def ll_icmp_ne_def ll_icmp_sle_def ll_icmp_slt_def ll_icmp_ule_def ll_icmp_ult_def
  by auto

lemma ll_ptrcmp_simps[vcg_normalize_simps]: 
  "ll_ptrcmp_eq a b = return (from_bool (a = b))" 
  "ll_ptrcmp_ne a b = return (from_bool (a \<noteq> b))" 
  unfolding ll_ptrcmp_eq_def ll_ptrcmp_ne_def 
  by auto
  
paragraph \<open>Bitwise\<close>

lemma ll_and_simp[vcg_normalize_simps]: "ll_and a b = return (a AND b)" by (auto simp: ll_and_def)
lemma ll_or_simp[vcg_normalize_simps]: "ll_or a b = return (a OR b)" by (auto simp: ll_or_def)
lemma ll_xor_simp[vcg_normalize_simps]: "ll_xor a b = return (a XOR b)" by (auto simp: ll_xor_def)
  
lemma ll_shl_simp[vcg_normalize_simps]: "unat b < LENGTH ('a) \<Longrightarrow> ll_shl (a::'a::len word) b = return (a << unat b)" 
  by (auto simp: ll_shl_def Let_def shift_ovf_def unat_def bitSHL'_def)
  
lemma ll_lshr_simp[vcg_normalize_simps]: "unat b < LENGTH ('a) \<Longrightarrow> ll_lshr (a::'a::len word) b = return (a >> unat b)" 
  by (auto simp: ll_lshr_def Let_def shift_ovf_def unat_def bitLSHR'_def)

lemma ll_ashr_simp[vcg_normalize_simps]: "unat b < LENGTH ('a) \<Longrightarrow> ll_ashr (a::'a::len word) b = return (a >>> unat b)" 
  by (auto simp: ll_ashr_def Let_def shift_ovf_def unat_def bitASHR'_def)
  
lemma [vcg_rules]:
  fixes a b :: "'a::len word" 
  assumes "WBOUNDS (unat b < LENGTH ('a))"  
  shows ll_shl_rule: "llvm_htriple \<box> (ll_shl a b) (\<lambda>r. \<up>(r=a<<unat b))"
    and ll_lshr_rule: "llvm_htriple \<box> (ll_lshr a b) (\<lambda>r. \<up>(r=a>>unat b))"
    and ll_ashr_rule: "llvm_htriple \<box> (ll_ashr a b) (\<lambda>r. \<up>(r=a>>>unat b))"
  using assms unfolding vcg_tag_defs
  by vcg  
  
paragraph \<open>Conversion\<close>
    
lemma ll_trunc_simp[vcg_normalize_simps]: "is_down' UCAST ('a\<rightarrow>'b) \<Longrightarrow> ll_trunc (a::'a::len word) TYPE('b::len word) = return (UCAST ('a\<rightarrow>'b) a)"
  by (auto simp: ll_trunc_def llb_trunc_def Let_def)
  
lemma ll_zext_simp[vcg_normalize_simps]: "is_up' UCAST ('a\<rightarrow>'b) \<Longrightarrow> ll_zext (a::'a::len word) TYPE('b::len word) = return (UCAST ('a\<rightarrow>'b) a)"
  by (auto simp: ll_zext_def llb_zext_def Let_def)
  
lemma ll_sext_simp[vcg_normalize_simps]: "is_up' SCAST ('a\<rightarrow>'b) \<Longrightarrow> ll_sext (a::'a::len word) TYPE('b::len word) = return (SCAST ('a\<rightarrow>'b) a)"
  by (auto simp: ll_sext_def llb_sext_def Let_def)

  
lemmas ll_trunc_rule[vcg_rules] = cond_llvm_htripleI[OF ll_trunc_simp, OF WBOUNDSD]
lemmas ll_zext_rule[vcg_rules] = cond_llvm_htripleI[OF ll_zext_simp, OF WBOUNDSD]
lemmas ll_sext_rule[vcg_rules] = cond_llvm_htripleI[OF ll_sext_simp, OF WBOUNDSD]
    
end
end

subsection \<open>Control Flow\<close>

locale llvm_prim_ctrl_setup

sublocale llvm_prim_setup < llvm_prim_ctrl_setup .

context llvm_prim_ctrl_setup begin

text \<open>The if command is handled by a set of normalization rules.
  Note that the VCG will split on the introduced conjunction automatically.
\<close>

lemma llc_if_simps[vcg_normalize_simps]:
  "llc_if 1 t e = t"
  "r\<noteq>0 \<Longrightarrow> llc_if r t e = t"
  "llc_if 0 t e = e"
  by (auto simp: llc_if_def)
  
lemma llc_if_simp[vcg_normalize_simps]: "wp (llc_if b t e) Q s \<longleftrightarrow> (to_bool b \<longrightarrow> wp t Q s) \<and> (\<not>to_bool b \<longrightarrow> wp e Q s)"
  unfolding llc_if_def by simp

lemma if_simp[vcg_normalize_simps]: "wp (If b t e) Q s \<longleftrightarrow> (b \<longrightarrow> wp t Q s) \<and> (\<not>b \<longrightarrow> wp e Q s)"
  by simp
  
end  
    
text \<open>The while command is handled by a standard invariant/variant rule.\<close>  

lemma llc_while_unfold: "llc_while b f \<sigma> = doM { ctd \<leftarrow> b \<sigma>; llc_if ctd (doM { \<sigma>\<leftarrow>f \<sigma>; llc_while b f \<sigma>}) (return \<sigma>)}"
  unfolding llc_while_def
  unfolding llc_while_def llc_if_def
  apply (rewrite mwhile_unfold)
  apply simp
  done

definition llc_while_annot :: "('\<sigma>::llvm_rep \<Rightarrow> 't \<Rightarrow> llvm_amemory \<Rightarrow> bool) \<Rightarrow> ('t\<times>'t) set \<Rightarrow> ('\<sigma>\<Rightarrow>1 word llM) \<Rightarrow> _"
  where [llvm_inline]: "llc_while_annot I R \<equiv> llc_while"

declare [[vcg_const "llc_while_annot I R"]]
  
lemma annotate_llc_while: "llc_while = llc_while_annot I R" by (simp add: llc_while_annot_def) 
  
context llvm_prim_ctrl_setup begin
  
lemma basic_while_rule:
  assumes "wf R"
  assumes "llSTATE (I \<sigma> t) s"
  assumes STEP: "\<And>\<sigma> t s. \<lbrakk> llSTATE (I \<sigma> t) s \<rbrakk> \<Longrightarrow> wp (b \<sigma>) (\<lambda>ctd s\<^sub>1. 
    (to_bool ctd \<longrightarrow> wp (f \<sigma>) (\<lambda>\<sigma>' s\<^sub>2. llSTATE (EXS t'. I \<sigma>' t' ** \<up>((t',t)\<in>R)) s\<^sub>2) s\<^sub>1)
  \<and> (\<not>to_bool ctd \<longrightarrow> Q \<sigma> s\<^sub>1)
    ) s"
  shows "wp (llc_while b f \<sigma>) Q s"
  using assms(1,2)
proof (induction t arbitrary: \<sigma> s)
  case (less t)
  show ?case 
    apply (subst llc_while_unfold)
    apply (simp add: vcg_normalize_simps)
    apply (rule wp_monoI[OF STEP])
    apply fact
    subgoal for r s\<^sub>1
      apply (cases "to_bool r"; simp add: vcg_normalize_simps)
      apply (erule wp_monoI; clarsimp; fri_extract)
      apply (rule less.IH; assumption)
      done
    done
qed          

text \<open>
  Standard while rule. 
  Note that the second parameter of the invariant is the termination measure, which must
  decrease wrt. a well-founded relation. It is initialized as a schematic variable, and must be 
  derivable via frame inference. In practice, the invariant will contain a \<open>\<up>(t=\<dots>)\<close> part.
\<close>  
lemma llc_while_annot_rule[vcg_decomp_erules]:  
  assumes "llSTATE P s"
  assumes "FRAME P (I \<sigma> t) F"
  assumes WF: "SOLVE_AUTO_DEFER (wf R)"
  assumes STEP: "\<And>\<sigma> t s. \<lbrakk> llSTATE ((I \<sigma> t ** F)) s \<rbrakk> \<Longrightarrow> EXTRACT (wp (b \<sigma>) (\<lambda>ctd s\<^sub>1. 
    (to_bool ctd \<longrightarrow> wp (f \<sigma>) (\<lambda>\<sigma>' s\<^sub>2. llPOST (EXS t'. I \<sigma>' t' ** \<up>((t',t)\<in>R) ** F) s\<^sub>2) s\<^sub>1)
  \<and> (\<not>to_bool ctd \<longrightarrow> Q \<sigma> s\<^sub>1)
    ) s)"
  shows "wp (llc_while_annot I R b f \<sigma>) Q s"
proof -
  from \<open>llSTATE P s\<close> \<open>FRAME P (I \<sigma> t) F\<close> have PRE: "llSTATE (I \<sigma> t ** F) s"
    by (simp add: FRAME_def STATE_def entails_def)

  show ?thesis  
    unfolding llc_while_annot_def
    apply (rule basic_while_rule[where I="\<lambda>\<sigma> t. I \<sigma> t ** F" and R=R])
    subgoal using WF unfolding vcg_tag_defs .
    apply (rule PRE)
    using STEP unfolding vcg_tag_defs
    apply (simp add: sep_algebra_simps)
    done
  
qed  
  
end

subsection \<open>LLVM Code Generator Setup\<close>

text \<open>Useful shortcuts\<close>

subsubsection \<open>Direct Arithmetic\<close>

(* TODO: How would we handle conditional rules, like from return (a div b) to ll_udiv?
  We would have to transform the program to a weaker one, that asserts preconditions, and
  then reason about this!
*)

context begin
  interpretation llvm_prim_arith_setup .

  lemma arith_inlines[llvm_inline, vcg_monadify_xforms]: 
    "return (a+b) = ll_add a b" 
    "return (a-b) = ll_sub a b" 
    "return (a*b) = ll_mul a b" 
  
    "return (a AND b) = ll_and a b" 
    "return (a OR b) = ll_or a b" 
    "return (a XOR b) = ll_xor a b" 
    by vcg
    
end  

subsubsection \<open>Direct Comparison\<close>
abbreviation (input) ll_cmp' :: "bool \<Rightarrow> 1 word" where "ll_cmp' \<equiv> from_bool"
definition [vcg_monadify_xforms,llvm_inline]: "ll_cmp b \<equiv> return (ll_cmp' b)"
  
(* To work with current monadify implementation, 
  we have to replace each operation by a constants
  
  TODO: Can we change monadifier?
*)

definition "ll_cmp'_eq a b \<equiv> ll_cmp' (a=b)"
definition "ll_cmp'_ne a b \<equiv> ll_cmp' (a\<noteq>b)"
definition "ll_cmp'_ule a b \<equiv> ll_cmp' (a\<le>b)"
definition "ll_cmp'_ult a b \<equiv> ll_cmp' (a<b)"
definition "ll_cmp'_sle a b \<equiv> ll_cmp' (a <=s b)"
definition "ll_cmp'_slt a b \<equiv> ll_cmp' (a <s b)"
                                          
lemmas ll_cmp'_defs = ll_cmp'_eq_def ll_cmp'_ne_def ll_cmp'_ule_def ll_cmp'_ult_def ll_cmp'_sle_def ll_cmp'_slt_def

lemmas [llvm_inline, vcg_monadify_xforms] = ll_cmp'_defs[symmetric]

context begin
  interpretation llvm_prim_arith_setup .

  lemma ll_cmp'_xforms[vcg_monadify_xforms,llvm_inline]:
    "return (ll_cmp'_eq  a b) = ll_icmp_eq a b" 
    "return (ll_cmp'_ne  a b) = ll_icmp_ne a b" 
    "return (ll_cmp'_ult a b) = ll_icmp_ult a b" 
    "return (ll_cmp'_ule a b) = ll_icmp_ule a b" 
    "return (ll_cmp'_slt a b) = ll_icmp_slt a b" 
    "return (ll_cmp'_sle a b) = ll_icmp_sle a b" 
    unfolding ll_cmp_def ll_cmp'_defs
    by (all vcg_normalize)

  lemma ll_ptrcmp'_xforms[vcg_monadify_xforms,llvm_inline]:
    "return (ll_cmp'_eq  a b) = ll_ptrcmp_eq a b" 
    "return (ll_cmp'_ne  a b) = ll_ptrcmp_ne a b" 
    unfolding ll_cmp_def ll_cmp'_defs
    by (all vcg_normalize)
    
    
end    

subsubsection \<open>Boolean Operations\<close>
lemma llvm_if_inline[llvm_inline,vcg_monadify_xforms]: "If b t e = llc_if (from_bool b) t e"  
  by (auto simp: llc_if_def)
  
lemma (in llvm_prim_arith_setup) llvm_from_bool_inline[llvm_inline]: 
  "from_bool (a\<and>b) = (from_bool a AND from_bool b)"  
  "from_bool (a\<or>b) = (from_bool a OR from_bool b)"  
  "(from_bool (\<not>a)::1 word) = (1 - (from_bool a :: 1 word))"  
  subgoal by (metis (full_types) from_bool_1 from_bool_mask_simp from_bool_to_bool_iff word_bool_alg.conj_zero_left word_bw_comms(1))
  subgoal by (metis (full_types) from_bool_1 from_bool_neq_0 word_bool_alg.disj_absorb word_bool_alg.disj_zero_left word_log_esimps(3))
  subgoal by (metis (full_types) cancel_comm_monoid_add_class.diff_cancel diff_zero from_bool_eq_if')
  done

subsubsection \<open>Products\<close>
  
lemma inline_prod_case[llvm_inline]: "(\<lambda>(a,b). f a b) = (\<lambda>x. doM { a\<leftarrow>prod_extract_fst x; b \<leftarrow> prod_extract_snd x; f a b })"  
  by (auto simp: prod_ops_simp)
  
lemma inline_return_prod_case[llvm_inline]: 
  "return (case x of (a,b) \<Rightarrow> f a b) = (case x of (a,b) \<Rightarrow> return (f a b))" by (rule prod.case_distrib)
  
  
lemma inline_return_prod[llvm_inline]: "return (a,b) = doM { x \<leftarrow> prod_insert_fst init a; x \<leftarrow> prod_insert_snd x b; return x }"  
  by (auto simp: prod_ops_simp)
  
subsubsection \<open>Marking of constants\<close>    
definition "ll_const x \<equiv> return x"

lemma ll_const_inline[llvm_inline]: "bind (ll_const x) f = f x" by (auto simp: ll_const_def)
  
declare [[vcg_const "numeral a"]]
declare [[vcg_const "ll_const c"]]

  
section \<open>Data Refinement\<close>  

locale standard_opr_abstraction = 
  fixes \<alpha> :: "'c \<Rightarrow> 'a"
    and I :: "'c \<Rightarrow> bool"
    and dflt_PRE1 :: "('a\<Rightarrow>'a) \<Rightarrow> 'c itself \<Rightarrow> 'a \<Rightarrow> bool"
    and dflt_PRE2 :: "('a\<Rightarrow>'a\<Rightarrow>'a) \<Rightarrow> 'c itself \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"
    and dflt_EPURE :: "'a \<Rightarrow> 'c \<Rightarrow> bool"
    
  assumes dflt_EPURE_correct: "\<And>c. I c \<Longrightarrow> dflt_EPURE (\<alpha> c) c"  
begin

definition "assn \<equiv> mk_pure_assn (\<lambda>a c. I c \<and> a=\<alpha> c)"
                           
lemma assn_pure[is_pure_rule]: "is_pure assn"
  by (auto simp: assn_def)

lemma vcg_prep_delete_assn[vcg_prep_external_drules]: 
  "pure_part (\<upharpoonleft>assn a c) \<Longrightarrow> dflt_EPURE a c"
  by (auto simp: assn_def dflt_EPURE_correct)
  

definition "is_un_op PRE cop mop aop \<equiv> 
  (\<forall>a::'c. I a \<and> PRE TYPE('c) (\<alpha> a) \<longrightarrow> I (mop a) \<and> \<alpha> (mop a) = aop (\<alpha> a) \<and> cop a = return (mop a))"
  
definition "is_bin_op PRE cop mop aop \<equiv> 
  (\<forall>a b::'c. I a \<and> I b \<and> PRE TYPE('c) (\<alpha> a) (\<alpha> b) \<longrightarrow> I (mop a b) \<and> \<alpha> (mop a b) = aop (\<alpha> a) (\<alpha> b) \<and> cop a b = return (mop a b))"

abbreviation "is_un_op' cop mop aop \<equiv> is_un_op (dflt_PRE1 aop) cop mop aop"
abbreviation "is_bin_op' cop mop aop \<equiv> is_bin_op (dflt_PRE2 aop) cop mop aop"

lemma is_un_opI[intro?]:
  assumes "\<And>a. \<lbrakk>I a; PRE TYPE('c) (\<alpha> a)\<rbrakk> \<Longrightarrow> cop a = return (mop a)"
  assumes "\<And>a. \<lbrakk>I a; PRE TYPE('c) (\<alpha> a)\<rbrakk> \<Longrightarrow> I (mop a)"
  assumes "\<And>a. \<lbrakk>I a; PRE TYPE('c) (\<alpha> a)\<rbrakk> \<Longrightarrow> \<alpha> (mop a) = aop (\<alpha> a)"
  shows "is_un_op PRE cop mop aop"
  using assms unfolding is_un_op_def by blast

lemma is_bin_opI[intro?]:
  assumes "\<And>a b. \<lbrakk>I a; I b; PRE TYPE('c) (\<alpha> a) (\<alpha> b)\<rbrakk> \<Longrightarrow> cop a b = return (mop a b)"
  assumes "\<And>a b. \<lbrakk>I a; I b; PRE TYPE('c) (\<alpha> a) (\<alpha> b)\<rbrakk> \<Longrightarrow> I (mop a b)"
  assumes "\<And>a b. \<lbrakk>I a; I b; PRE TYPE('c) (\<alpha> a) (\<alpha> b)\<rbrakk> \<Longrightarrow> \<alpha> (mop a b) = aop (\<alpha> a) (\<alpha> b)"
  shows "is_bin_op PRE cop mop aop"
  using assms unfolding is_bin_op_def by blast

lemma un_op_tmpl:
  fixes w :: "'c"
  assumes A: "is_un_op PRE cop mop aop"
  shows "llvm_htriple 
    (\<upharpoonleft>assn i w ** \<up>\<^sub>d(PRE TYPE('c) i)) 
    (cop w) 
    (\<lambda>r. \<upharpoonleft>assn (aop i) r ** \<upharpoonleft>assn i w)
    "
proof -
  interpret llvm_prim_arith_setup .

  show ?thesis
    using A
    unfolding is_un_op_def assn_def apply clarsimp
    by vcg
    
qed
  
  
lemma bin_op_tmpl:
  fixes w\<^sub>1 w\<^sub>2 :: "'c"
  assumes A: "is_bin_op PRE cop mop aop"
  shows "llvm_htriple 
    (\<upharpoonleft>assn i\<^sub>1 w\<^sub>1 ** \<upharpoonleft>assn i\<^sub>2 w\<^sub>2 ** \<up>\<^sub>d(PRE TYPE('c) i\<^sub>1 i\<^sub>2)) 
    (cop w\<^sub>1 w\<^sub>2) 
    (\<lambda>r. \<upharpoonleft>assn (aop i\<^sub>1 i\<^sub>2) r ** \<upharpoonleft>assn i\<^sub>1 w\<^sub>1 ** \<upharpoonleft>assn i\<^sub>2 w\<^sub>2)
    "
proof -
  interpret llvm_prim_arith_setup .

  show ?thesis
    using A
    unfolding is_bin_op_def assn_def apply clarsimp
    by vcg
    
qed

end

interpretation bool: standard_opr_abstraction "to_bool::1 word \<Rightarrow> bool" "\<lambda>_. True" \<open>\<lambda>_ _ _. True\<close> \<open>\<lambda>_ _ _ _. True\<close> "\<lambda>_ _. True" 
  by standard auto

context standard_opr_abstraction begin

  definition "is_cmp_op cop mop aop \<equiv> 
    (\<forall>a b. I a \<and> I b \<longrightarrow> (cop a b = return (from_bool (mop a b)) \<and> (mop a b \<longleftrightarrow> aop (\<alpha> a) (\<alpha> b))))"
  
  lemma is_cmp_opI[intro?]:
    assumes "\<And>a b. \<lbrakk>I a; I b\<rbrakk> \<Longrightarrow> cop a b = return (from_bool (mop a b))"
    assumes "\<And>a b. \<lbrakk>I a; I b\<rbrakk> \<Longrightarrow> mop a b \<longleftrightarrow> aop (\<alpha> a) (\<alpha> b)"
    shows "is_cmp_op cop mop aop"
    using assms unfolding is_cmp_op_def by blast
    
  lemma cmp_op_tmpl:
    fixes w\<^sub>1 w\<^sub>2 :: "'c"
    assumes "is_cmp_op cop mop aop"
    shows "llvm_htriple 
      (\<upharpoonleft>assn i\<^sub>1 w\<^sub>1 ** \<upharpoonleft>assn i\<^sub>2 w\<^sub>2) 
      (cop w\<^sub>1 w\<^sub>2) 
      (\<lambda>r. \<upharpoonleft>bool.assn (aop i\<^sub>1 i\<^sub>2) r ** \<upharpoonleft>assn i\<^sub>1 w\<^sub>1 ** \<upharpoonleft>assn i\<^sub>2 w\<^sub>2)
      "
    using assms unfolding is_cmp_op_def assn_def bool.assn_def apply clarsimp
    by vcg

end
  
subsection \<open>Arithmetic\<close>

   
lemma to_bool_logics:
  fixes a b :: "1 word"
  shows "to_bool (a&&b) \<longleftrightarrow> to_bool a \<and> to_bool b"  
    and "to_bool (a||b) \<longleftrightarrow> to_bool a \<or> to_bool b"  
    and "to_bool (a XOR b) \<longleftrightarrow> to_bool a \<noteq> to_bool b"  
    and "to_bool (NOT a) \<longleftrightarrow> \<not>to_bool a"  
  apply (cases a; cases b; simp; fail)
  apply (cases a; cases b; simp; fail)
  apply (cases a; cases b; simp; fail)
  apply (cases a; simp; fail)
  done

context begin                                             

interpretation llvm_prim_arith_setup .

abbreviation ll_not1 :: "1 word \<Rightarrow> 1 word llM" where "ll_not1 x \<equiv> ll_add x 1"  
    
lemma ll_not1_inline[llvm_inline]: "return (~~x) \<equiv> ll_not1 x"
  by (auto simp: word1_NOT_eq arith_inlines)
  
lemma bool_bin_ops:
  "bool.is_bin_op' ll_and (AND) (\<and>)" 
  "bool.is_bin_op' ll_or (OR) (\<or>)" 
  "bool.is_bin_op' ll_xor (XOR) (\<noteq>)" 
  apply (all \<open>rule\<close>)
  apply (simp_all only: to_bool_logics)
  apply (all \<open>vcg_normalize?\<close>)
  done

lemma bool_un_ops:
  "bool.is_un_op' ll_not1 bitNOT Not" 
  apply (all \<open>rule\<close>)
  apply (simp_all only: to_bool_logics)
  apply (all \<open>vcg_normalize?\<close>)
  apply (simp_all add: word1_NOT_eq)
  done
    
lemmas bool_op_rules[vcg_rules] = 
  bool_bin_ops[THEN bool.bin_op_tmpl]
  bool_un_ops[THEN bool.un_op_tmpl]
  
end  
  

(* TODO: Move *)
definition snats :: "nat \<Rightarrow> nat set"
  where "snats n = {i. i < 2 ^ (n-1)}"

definition max_unat :: "nat \<Rightarrow> nat" where "max_unat n \<equiv> 2^n"  
abbreviation (input) "min_uint \<equiv> 0::int"
definition max_uint :: "nat \<Rightarrow> int" where "max_uint n \<equiv> 2^n"  

definition min_sint :: "nat \<Rightarrow> int" where "min_sint n \<equiv> -(2^(n-1))"
definition max_sint :: "nat \<Rightarrow> int" where "max_sint n \<equiv> 2^(n-1)"  

definition "max_snat n \<equiv> (2::nat)^(n-1)"



lemma in_unats_conv[simp]: "x\<in>unats n \<longleftrightarrow> x<max_unat n" by (auto simp: unats_def max_unat_def)
  
lemma in_sints_conv[simp]: "n\<noteq>0 \<Longrightarrow> x\<in>sints n \<longleftrightarrow> min_sint n \<le> x \<and> x<max_sint n"
  by (auto simp: sints_num min_sint_def max_sint_def)


lemma in_uints_conv[simp]: "x\<in>uints n \<longleftrightarrow> min_uint \<le> x \<and> x<max_uint n"
  by (auto simp: uints_num max_uint_def)

lemma in_snats_conv[simp]: "n\<in>snats N \<longleftrightarrow> n<max_snat N"
  by (auto simp: snats_def max_snat_def)
  
  
lemma in_range_uint_conv[simp]: "x\<in>range (uint::'a::len word \<Rightarrow> _) \<longleftrightarrow> min_uint \<le> x \<and> x<max_uint LENGTH('a)"
  by (auto simp: uints_num max_uint_def word_uint.Rep_range) 
  
  
lemma uint_lt_max_uint[simp]: "uint (w::'a::len word) < max_uint LENGTH('a)"  
  using max_uint_def by auto

lemma unat_lt_max_unat[simp]: "unat (w::'a::len word) < max_unat LENGTH('a)"  
  using max_unat_def by auto

lemma sint_cmp_extr_sint[simp]: 
  "min_sint LENGTH('a) \<le> sint (w::'a::len word)"  
  "sint (w::'a::len word) < max_sint LENGTH('a)"  
  unfolding max_sint_def min_sint_def using sint_range' by auto 
  
definition snat :: "_::len2 word \<Rightarrow> nat" where "snat \<equiv> nat o sint"

(* TODO: Move *)       
lemma not_bin_nth_if_less: "\<lbrakk>0\<le>i; i<2^n\<rbrakk> \<Longrightarrow> \<not>(bin_nth i n)"
  apply auto
  using bintrunc_mod2p nth_bintr by force
       
  
lemma snat_zero[simp]: "snat 0 = 0" by (auto simp: snat_def)
lemma snat_one[simp]: "snat (1) = 1" by (auto simp: snat_def)
  
lemma snat_numeral[simp]:
  fixes b
  defines "w::'a::len2 word \<equiv> numeral b"
  defines "n::nat \<equiv> numeral b"
  assumes A: "n<max_snat LENGTH('a)"
  shows "snat w = n"    
proof -  
  have MSB: "\<not>msb w" using A
    apply (simp add: w_def n_def max_snat_def not_bin_nth_if_less)
    apply (rule not_bin_nth_if_less)
    apply simp
    by (metis of_nat_less_iff of_nat_numeral semiring_1_class.of_nat_power)
  
  have "snat w = nat (sint w)" by (simp add: snat_def)
  also have "sint w = uint w" using MSB by (simp add: sint_eq_uint)
  also have "\<dots> = numeral b mod 2^LENGTH('a)" unfolding w_def by (rule uint_numeral)
  also have "\<dots> = numeral b" 
  proof (rule mod_pos_pos_trivial)
    have "int n < int (Suc 1 ^ len_of (TYPE('a)::'a itself))"
      by (metis One_nat_def assms(3) diff_le_self lessI max_snat_def numerals(2) of_nat_less_iff order_less_le_trans power_increasing_iff)
    then show "(numeral b::int) < 2 ^ len_of (TYPE('a)::'a itself)"
      by (simp add: n_def)
  qed simp
  finally show ?thesis unfolding n_def by simp
qed  

abbreviation (input) "word_len \<equiv> \<lambda>_::'a::len0 word. LENGTH('a)"

lemma snat_lt_max_snat[simp]: "snat w < max_snat (word_len w)"
  by (auto simp: snat_def max_snat_def sint_range')
  
subsubsection \<open>Reflection of Maximum Representable Values\<close>  
  
definition ll_max_uint :: "'l::len word llM" where [llvm_inline]: "ll_max_uint \<equiv> ll_sub 0 1"
definition ll_max_sint :: "'l::len2 word llM" where [llvm_inline]: "ll_max_sint \<equiv> doM {r \<leftarrow> ll_max_uint; ll_lshr r 1}"
  
context llvm_prim_arith_setup begin  

lemma ll_max_uint_simp[vcg_normalize_simps]: "(ll_max_uint::'l::len word llM) = return (word_of_int (max_uint LENGTH('l) - 1))"
  unfolding ll_max_uint_def max_uint_def
  apply vcg_normalize
  by (simp add: word_of_int_minus)

lemma len_neq_one_conv: 
  "LENGTH('l::len) \<noteq> Suc 0 \<longleftrightarrow> (\<exists>n. LENGTH('l) = Suc (Suc n))"
  apply auto
  by (metis One_nat_def Suc_pred' len_gt_0 neq0_conv)
  
lemma word_of_int_div2: "0\<le>w \<Longrightarrow> w<2^LENGTH('a) \<Longrightarrow> word_of_int w div (2::'a::len word) = word_of_int (w div 2)"  
  apply (simp add: word_uint_eq_iff uint_word_of_int uint_div bintrunc_mod2p) 
  by (smt int_mod_eq' mod_self zdiv_eq_0_iff)

lemma word_of_int_shr1: "0\<le>w \<Longrightarrow> w<2^LENGTH('a::len) \<Longrightarrow> (word_of_int w :: 'a word) >> Suc 0 = word_of_int (w div 2)"
  by (auto simp: shiftr1_is_div_2[simplified] word_of_int_div2)

lemma ll_max_sint_aux1: "((4::int) * 2 ^ n - 1) div 2 < 4 * 2 ^ n" 
proof -
  have "((4::int) * 2 ^ n - 1) < (4::int) * 2 ^ n" by auto
  hence "((4::int) * 2 ^ n - 1) div 2 \<le> ((4::int) * 2 ^ n) div 2" by auto
  also have "\<dots> < 4 * 2^n" by auto
  finally show ?thesis .
qed  
 
lemma ll_max_sint_simp[vcg_normalize_simps]: "(ll_max_sint::'l::len2 word llM) = return (word_of_int (max_sint LENGTH('l) - 1))"
  unfolding ll_max_sint_def 
  supply [simp] = Suc_lessI max_sint_def max_uint_def len_neq_one_conv
  apply vcg_normalize
  apply (simp add: word_of_int_shr1)
  apply (rule len2E[where 'a='l]; simp)
  apply (subst word_of_int_inj)
  apply (auto simp: field_simps)
  apply (simp add: nonneg_mod_div)
  apply (simp add: ll_max_sint_aux1)
  apply (smt one_le_power)
  by (simp add: pos_add_strict)
    

lemma ll_max_uint_rule[vcg_rules]: "llvm_htriple \<box> (ll_max_uint::'l::len word llM) (\<lambda>r. \<up>(uint r = max_uint (LENGTH('l)) - 1))"
  supply [simp] = max_uint_def zmod_minus1 uint_word_ariths
  unfolding ll_max_uint_def max_uint_def
  by vcg'
    
lemma ll_max_sint_rule: "llvm_htriple (\<box>) (ll_max_sint::'l::len2 word llM) (\<lambda>r. \<up>(uint r = max_sint LENGTH('l) - 1))"
  apply vcg'
  apply (auto simp add: uint_word_of_int max_sint_def)
  by (smt diff_le_self int_mod_eq power_increasing_iff zless2p)
  

end  
  
subsubsection \<open>Signed Integers\<close>

interpretation sint: standard_opr_abstraction sint 
  "\<lambda>_. True" 
  "\<lambda>op (_::'a::len word itself) a. op a \<in> sints LENGTH('a)" 
  "\<lambda>op (_::'a::len word itself) a b. op a b \<in> sints LENGTH('a)" 
  "\<lambda>a c. a\<in>sints LENGTH('a)"
  by standard auto

  

method prove_sint_op uses simp = (
  rule sint.is_bin_opI sint.is_cmp_opI sint.is_un_opI; 
  (auto simp: min_sint_def max_sint_def vcg_normalize_simps simp)?; 
  (determ uint_arith; fail)?)  

lemma sint_neq_ZD: "sint b \<noteq> 0 \<Longrightarrow> b\<noteq>0" by auto
    
context begin                                             

interpretation llvm_prim_arith_setup .


lemma sint_bin_ops:
  "sint.is_bin_op' ll_add (+) (+)" 
  "sint.is_bin_op' ll_sub (-) (-)"  
  "sint.is_bin_op' ll_mul ( *) ( *)"  
  "sint.is_bin_op (\<lambda>(_::'a::len word itself) a b. b\<noteq>0 \<and> a sdiv b \<in> sints LENGTH('a)) ll_sdiv (sdiv) (sdiv)"  
  "sint.is_bin_op (\<lambda>(_::'a::len word itself) a b. b\<noteq>0 \<and> a sdiv b \<in> sints LENGTH('a)) ll_srem (smod) (smod)"
  supply [simp del] = in_sints_conv
  apply (all \<open>prove_sint_op simp:  sint_neq_ZD\<close>)
  apply (simp_all add: sbintrunc_eq_if_in_range sint_word_ariths signed_mod_arith signed_div_arith)
  using smod_word_min smod_word_max 
  by (auto simp add: in_sints_conv min_sint_def max_sint_def)
  
lemma sint_cmp_ops: 
  "sint.is_cmp_op ll_icmp_eq (=) (=)" 
  "sint.is_cmp_op ll_icmp_ne (\<noteq>) (\<noteq>)"
  "sint.is_cmp_op ll_icmp_sle (\<lambda>a b. a <=s b) (\<le>)" (* FIXME: Why isn't <=s and <s proper infix operator? *) 
  "sint.is_cmp_op ll_icmp_slt (\<lambda>a b. a <s b) (<)" 
  by (all \<open>prove_sint_op simp: word_sle_def word_sless_def le_less\<close>)

lemmas sint_rules[vcg_rules] =  
  sint_bin_ops[THEN sint.bin_op_tmpl]
  sint_cmp_ops[THEN sint.cmp_op_tmpl]
  
    
definition signed :: "'a::len word \<Rightarrow> 'a word" where [llvm_inline]: "signed c \<equiv> c"  
  
declare [[vcg_const "signed (numeral a)"]]
declare [[vcg_const "signed (-numeral a)"]]
declare [[vcg_const "signed 0"]]
declare [[vcg_const "signed (-0)"]]
declare [[vcg_const "signed 1"]]
declare [[vcg_const "signed (-1)"]]


lemma monadify_signed[vcg_monadify_xforms]: 
  "return (signed x) = ll_const (signed x)" by (simp add: ll_const_def)

  
lemma ll_const_signed_aux: "\<lbrakk>n\<noteq>0; - (2 ^ (n - Suc 0)) \<le> i; i < 2 ^ (n - Suc 0)\<rbrakk>
         \<Longrightarrow> (i + 2 ^ (n - Suc 0)) mod 2 ^ n - 2 ^ (n - Suc 0) = (i::int)"  
  by (cases n; simp)
  
lemma ll_const_signed_rule[vcg_rules]: 
  "llvm_htriple \<box> (ll_const (signed 0)) (\<lambda>r. \<upharpoonleft>sint.assn 0 r)"
  "llvm_htriple (\<up>\<^sub>d(LENGTH('a::len) \<noteq> 1)) (ll_const (signed (1::'a word))) (\<lambda>r. \<upharpoonleft>sint.assn 1 r)"
  "llvm_htriple (\<up>\<^sub>d(numeral w \<in> sints LENGTH('a))) (ll_const (signed (numeral w::'a::len word))) (\<lambda>r. \<upharpoonleft>sint.assn (numeral w) r)"
  unfolding ll_const_def signed_def sint.assn_def
  supply [simp] = sbintrunc_mod2p max_sint_def min_sint_def ll_const_signed_aux
  by vcg

  
(* TODO: Move *)
lemma lt_exp2n_signed_estimate[simp]:
  fixes x::int
  defines "n\<equiv>LENGTH('a::len)"
  assumes A: "ASSUMPTION (n > n')" "x<2^n'"
  shows "x < max_sint n"
  using A unfolding ASSUMPTION_def max_sint_def
  by (smt One_nat_def Suc_le_mono Suc_pred assms(1) len_gt_0 less_eq_Suc_le power_increasing_iff)
    
end  
  
    
  
  
subsubsection \<open>Unsigned Integers\<close>

interpretation uint: standard_opr_abstraction uint 
  "\<lambda>_. True" 
  "\<lambda>op (_::'a::len word itself) a. op a \<in> uints LENGTH('a)" 
  "\<lambda>op (_::'a::len word itself) a b. op a b \<in> uints LENGTH('a)" 
  "\<lambda>a c. a\<in>uints LENGTH('a)"
  by standard auto


method prove_uint_op uses simp = (
  rule uint.is_bin_opI uint.is_cmp_opI uint.is_un_opI; 
  (auto simp: max_uint_def vcg_normalize_simps simp)?; 
  (determ uint_arith; fail)?)  

lemma uint_neq_ZD: "uint b \<noteq> 0 \<Longrightarrow> b\<noteq>0" by auto
    
context begin                                             

interpretation llvm_prim_arith_setup .


lemma uint_bin_ops_arith:
  "uint.is_bin_op (\<lambda>(_::'a::len word itself) a b. a+b < max_uint LENGTH('a)) ll_add (+) (+)" 
  "uint.is_bin_op (\<lambda>_ a b. b\<le>a) ll_sub (-) (-)"  
  "uint.is_bin_op (\<lambda>(_::'a::len word itself) a b. a*b < max_uint LENGTH('a)) ll_mul ( *) ( *)"  
  "uint.is_bin_op (\<lambda>_ a b. b\<noteq>0) ll_udiv (div) (div)"  
  "uint.is_bin_op (\<lambda>_ a b. b\<noteq>0) ll_urem (mod) (mod)"
  by (all \<open>prove_uint_op simp: uint_mult_lem uint_neq_ZD uint_div uint_mod\<close>)

(* TODO: Remove preconditions! *)
lemma uint_bin_ops_bitwise:
  "uint.is_bin_op' ll_and (AND) (AND)" 
  "uint.is_bin_op' ll_or (OR) (OR)" 
  "uint.is_bin_op' ll_xor (XOR) (XOR)" 
  by (all \<open>prove_uint_op simp: uint_and uint_or uint_xor\<close>)

lemmas uint_bin_ops = uint_bin_ops_arith uint_bin_ops_bitwise
  
lemma uint_cmp_ops: 
  "uint.is_cmp_op ll_icmp_eq (=) (=)" 
  "uint.is_cmp_op ll_icmp_ne (\<noteq>) (\<noteq>)"
  "uint.is_cmp_op ll_icmp_ule (\<le>) (\<le>)" 
  "uint.is_cmp_op ll_icmp_ult (<) (<)" 
  by (all \<open>prove_uint_op\<close>)
  
lemmas uint_rules[vcg_rules] =
  uint_bin_ops[THEN uint.bin_op_tmpl]
  uint_cmp_ops[THEN uint.cmp_op_tmpl]
  
  
definition unsigned :: "'a::len word \<Rightarrow> 'a word" where [llvm_inline]: "unsigned c \<equiv> c"  
  
declare [[vcg_const "unsigned (numeral a)"]]
declare [[vcg_const "unsigned 0"]]
declare [[vcg_const "unsigned 1"]]

lemma monadify_unsigned[vcg_monadify_xforms]: 
  "return (unsigned x) = ll_const (unsigned x)" by (simp add: ll_const_def)

  
lemma ll_const_unsigned_rule[vcg_rules]: 
  "llvm_htriple \<box> (ll_const (unsigned 0)) (\<lambda>r. \<upharpoonleft>uint.assn 0 r)"
  "llvm_htriple \<box> (ll_const (unsigned 1)) (\<lambda>r. \<upharpoonleft>uint.assn 1 r)"
  "llvm_htriple (\<up>\<^sub>d(numeral w \<in> uints LENGTH('a))) (ll_const (unsigned (numeral w::'a::len word))) (\<lambda>r. \<upharpoonleft>uint.assn (numeral w) r)"
  unfolding ll_const_def unsigned_def uint.assn_def
  supply [simp] = bintrunc_mod2p max_uint_def
  by vcg

  
(* TODO: Move *)
lemma lt_exp2n_estimate[simp]: 
  fixes x::int
  defines "n\<equiv>LENGTH('a::len)"
  assumes A: "ASSUMPTION (n \<ge> n')" "x<2^n'"
  shows "x < max_uint n"
  using A unfolding ASSUMPTION_def max_uint_def
  by (smt power_increasing_iff)

    
end  

subsubsection \<open>Natural Numbers by unsigned\<close>

find_theorems "uint _ < max_uint _"

interpretation unat: standard_opr_abstraction unat 
  "\<lambda>_. True" 
  "\<lambda>op (_::'a::len word itself) a. op a \<in> unats LENGTH('a)" 
  "\<lambda>op (_::'a::len word itself) a b. op a b \<in> unats LENGTH('a)" 
  "\<lambda>a c. a\<in>unats LENGTH('a)"
  by standard auto


method prove_unat_op uses simp = (
  rule unat.is_bin_opI unat.is_cmp_opI; 
  (auto simp: max_unat_def vcg_normalize_simps simp)?; 
  (determ unat_arith; fail)?)  

lemma unat_neq_ZD: "unat b \<noteq> 0 \<Longrightarrow> b\<noteq>0" by auto
    
context begin                                             

interpretation llvm_prim_arith_setup .


lemma unat_bin_ops:
  "unat.is_bin_op (\<lambda>(_::'a::len word itself) a b. a+b < max_unat LENGTH('a)) ll_add (+) (+)" 
  "unat.is_bin_op (\<lambda>_ a b. b\<le>a) ll_sub (-) (-)"  
  "unat.is_bin_op (\<lambda>(_::'a::len word itself) a b. a*b < max_unat LENGTH('a)) ll_mul ( *) ( *)"  
  "unat.is_bin_op (\<lambda>_ a b. b\<noteq>0) ll_udiv (div) (div)"  
  "unat.is_bin_op (\<lambda>_ a b. b\<noteq>0) ll_urem (mod) (mod)"
  by (all \<open>prove_unat_op simp: unat_mult_lem unat_neq_ZD unat_div unat_mod\<close>)

lemma unat_cmp_ops: 
  "unat.is_cmp_op ll_icmp_eq (=) (=)" 
  "unat.is_cmp_op ll_icmp_ne (\<noteq>) (\<noteq>)"
  "unat.is_cmp_op ll_icmp_ule (\<le>) (\<le>)" 
  "unat.is_cmp_op ll_icmp_ult (<) (<)" 
  by (all \<open>prove_unat_op\<close>)
  
lemmas unat_rules[vcg_rules] =
  unat_bin_ops[THEN unat.bin_op_tmpl]
  unat_cmp_ops[THEN unat.cmp_op_tmpl]
  
  
definition unsigned_nat :: "'a::len word \<Rightarrow> 'a word" where [llvm_inline]: "unsigned_nat c \<equiv> c"  
  
declare [[vcg_const "unsigned_nat (numeral a)"]]
declare [[vcg_const "unsigned_nat 0"]]
declare [[vcg_const "unsigned_nat 1"]]

lemma monadify_unsigned_nat[vcg_monadify_xforms]: 
  "return (unsigned_nat x) = ll_const (unsigned_nat x)" 
  by (simp add: ll_const_def)
  
lemma ll_const_unsigned_nat_rule[vcg_rules]: 
  "llvm_htriple \<box> (ll_const (unsigned_nat 0)) (\<lambda>r. \<upharpoonleft>unat.assn 0 r)"
  "llvm_htriple \<box> (ll_const (unsigned_nat 1)) (\<lambda>r. \<upharpoonleft>unat.assn 1 r)"
  "llvm_htriple (\<up>\<^sub>d(numeral w \<in> unats LENGTH('a))) (ll_const (unsigned_nat (numeral w::'a::len word))) (\<lambda>r. \<upharpoonleft>unat.assn (numeral w) r)"
  unfolding ll_const_def unsigned_nat_def unat.assn_def 
  supply [simp] = bintrunc_mod2p max_unat_def unat_numeral and [simp del] = unat_bintrunc
  by vcg
  
(* TODO: Move *)
lemma lt_exp2n_nat_estimate[simp]: 
  fixes x::nat
  defines "n\<equiv>LENGTH('a::len)"
  assumes A: "ASSUMPTION (n \<ge> n')" "x<2^n'"
  shows "x < max_unat n"
  using A unfolding ASSUMPTION_def max_unat_def
  by (meson le_def le_less_trans nat_power_less_imp_less pos2)

    
end  


subsubsection \<open>Natural Numbers by signed\<close>


definition "snat_invar (w::'a::len2 word) \<equiv> \<not>msb w"
interpretation snat: standard_opr_abstraction snat "snat_invar" 
  "\<lambda>op (_::'a::len2 word itself) a. op a \<in> snats LENGTH('a)" 
  "\<lambda>op (_::'a::len2 word itself) a b. op a b \<in> snats LENGTH('a)" 
  "\<lambda>a c. a\<in>snats LENGTH('a)" 
  apply standard apply (auto simp: snat_invar_def) done

lemma snat_invar_alt: "snat_invar (w::'a::len2 word) \<longleftrightarrow> (\<exists>n. word_len w = Suc n \<and> unat w < 2^n)"  
  apply (cases "word_len w")
  apply (auto simp: snat_invar_def msb_unat_big)
  done

lemma snat_eq_unat: 
  "unat w < 2^(word_len w - 1) \<Longrightarrow> snat w = unat w"  
  "snat_invar w \<Longrightarrow> snat w = unat w"  
  by (auto simp: snat_def unat_def sint_eq_uint msb_uint_big snat_invar_alt)


lemma cnv_snat_to_uint:
  assumes "snat_invar w"
  shows "snat w = nat (uint w)" 
    and "sint w = uint w"
    and "unat w = nat (uint w)"
  using assms apply -
  apply (simp add: snat_eq_unat(2) unat_def sint_eq_uint)
  apply (simp add: sint_eq_uint snat_invar_def)
  apply (simp add: unat_def)
  done
      


method prove_snat_op uses simp = (
  rule snat.is_bin_opI snat.is_cmp_opI; 
  (auto simp: max_snat_def snat_invar_alt snat_eq_unat vcg_normalize_simps simp)?)  
    
context begin                                             

interpretation llvm_prim_arith_setup .


lemma snat_in_bounds_aux: "(a::nat)<2^(x-Suc 0) \<Longrightarrow> a<2^x"
  by (metis diff_le_self leI le_less_trans less_not_refl nat_power_less_imp_less numeral_2_eq_2 zero_less_Suc)

lemma snat_bin_ops:
  "snat.is_bin_op' ll_add (+) (+)" 
  "snat.is_bin_op (\<lambda>_ a b. b\<le>a) ll_sub (-) (-)"  
  "snat.is_bin_op' ll_mul ( *) ( *)"  
  "snat.is_bin_op (\<lambda>_ a b. b\<noteq>0) ll_udiv (div) (div)"  
  "snat.is_bin_op (\<lambda>_ a b. b\<noteq>0) ll_urem (mod) (mod)"
  
  apply (prove_snat_op simp: unat_word_ariths)
  apply (prove_snat_op simp: unat_word_ariths unat_sub_if')
  apply (prove_snat_op simp: unat_word_ariths)
  subgoal
    apply (prove_snat_op simp: unat_word_ariths)
    apply (subst ll_udiv_simp; auto)
    apply (metis div_le_dividend le_less_trans power_Suc unat_div unat_of_nat word_arith_nat_defs(6))
    apply (subst snat_eq_unat)
    apply (auto simp: unat_div)
    apply (metis div_le_dividend le_less_trans)
    done
  subgoal  
    apply (prove_snat_op simp: unat_word_ariths)
    apply (subst ll_urem_simp; auto)
    apply (meson le_less_trans mod_less_eq_dividend)
    apply (subst snat_eq_unat)
    apply (auto simp: unat_mod)
    apply (meson le_less_trans mod_less_eq_dividend)
    done
  done
  
lemma snat_cmp_ops:
  "snat.is_cmp_op ll_icmp_eq (=) (=)" 
  "snat.is_cmp_op ll_icmp_ne (\<noteq>) (\<noteq>)"
  "snat.is_cmp_op ll_icmp_ule (\<le>) (\<le>)" 
  "snat.is_cmp_op ll_icmp_ult (<) (<)" 
  "snat.is_cmp_op ll_icmp_sle (\<lambda>a b. a <=s b) (\<le>)" 
  "snat.is_cmp_op ll_icmp_slt (\<lambda>a b. a <s b) (<)" 
  
  apply (prove_snat_op)
  apply (prove_snat_op)
  apply (prove_snat_op simp: word_le_nat_alt word_less_nat_alt)
  apply (prove_snat_op simp: word_le_nat_alt word_less_nat_alt)
  apply (prove_snat_op simp: word_le_nat_alt word_less_nat_alt word_sle_msb_le msb_unat_big)
  apply (prove_snat_op simp: word_le_nat_alt word_less_nat_alt word_sle_msb_le word_sless_msb_less msb_unat_big)
  done
  
  
lemmas snat_rules[vcg_rules] =
  snat_bin_ops[THEN snat.bin_op_tmpl]
  snat_cmp_ops[THEN snat.cmp_op_tmpl]
  
  
  
definition signed_nat :: "'a::len2 word \<Rightarrow> 'a word" where [llvm_inline]: "signed_nat c \<equiv> c"  
  
declare [[vcg_const "signed_nat (numeral a)"]]
declare [[vcg_const "signed_nat 0"]]
declare [[vcg_const "signed_nat 1"]]

lemma monadify_signed_nat[vcg_monadify_xforms]: "return (signed_nat x) = ll_const (signed_nat x)" by (simp add: ll_const_def)

  
lemma ll_const_signed_nat_aux1: "(w::nat) < 2^(n-1) \<Longrightarrow> w mod (2^n) = w"  
  by (simp add: snat_in_bounds_aux)
  
lemma ll_const_signed_nat_aux2: "\<lbrakk>numeral w < (2::nat) ^ (LENGTH('a::len2) - Suc 0)\<rbrakk> \<Longrightarrow> \<not>msb (numeral w::'a word)"  
  by (auto simp: msb_unat_big snat_in_bounds_aux unat_numeral simp del: unat_bintrunc)
  
  
lemma ll_const_signed_nat_rule[vcg_rules]: 
  "llvm_htriple (\<box>) (ll_const (signed_nat (0::'a word))) (\<lambda>r. \<upharpoonleft>snat.assn 0 r)"
  "llvm_htriple (\<box>) (ll_const (signed_nat (1::'a word))) (\<lambda>r. \<upharpoonleft>snat.assn 1 r)"
  "llvm_htriple (\<up>\<^sub>d(numeral w \<in> snats LENGTH('a))) (ll_const (signed_nat (numeral w::'a::len2 word))) (\<lambda>r. \<upharpoonleft>snat.assn (numeral w) r)"
  unfolding ll_const_def signed_nat_def snat.assn_def 
  apply vcg'
  subgoal by (simp add: not0_implies_Suc snat_invar_alt) 
  subgoal by (simp add: snat_invar_def) 
  subgoal 
    apply (cases "LENGTH('a)"; simp)
    by (metis One_nat_def ll_const_signed_nat_aux2 max_snat_def snat_invar_def)
  done
      
end  

lemma lt_exp2n_snat_estimate[simp]: 
  fixes x::nat
  defines "n\<equiv>LENGTH('a::len)"
  assumes A: "ASSUMPTION (n > n')" "x<2^n'"
  shows "x < max_snat n"
  using A unfolding ASSUMPTION_def max_snat_def
  by (metis Suc_diff_1 Suc_leI leI le_less_trans nat_power_less_imp_less numeral_2_eq_2 order_less_irrefl zero_less_Suc)




definition [llvm_inline]: "ll_max_snat \<equiv> ll_max_sint"

lemma ll_max_snat_rule[vcg_rules]: "llvm_htriple (\<box>) ll_max_snat (\<lambda>r::'l word. \<upharpoonleft>snat.assn (max_snat LENGTH('l::len2) - 1) r)"
proof -
  interpret llvm_prim_arith_setup .
  
  have [simp]: "snat_invar (word_of_int (max_sint LENGTH('l) - 1)::'l word)" 
    apply (rule len2E[where 'a='l]; simp)
    apply (auto simp: snat_invar_alt unat_def len_neq_one_conv max_sint_def max_snat_def snat_def uint_word_of_int)
    by (smt int_mod_eq' one_le_power)
  
  
  show ?thesis
    unfolding ll_max_snat_def snat.assn_def
    apply vcg'
    apply (simp add: cnv_snat_to_uint uint_word_of_int)
    apply (clarsimp simp: len_neq_one_conv max_sint_def max_snat_def snat_def)
    apply (simp add: nat_mod_distrib nat_mult_distrib nat_diff_distrib' nat_power_eq less_imp_diff_less)
    done
qed    




subsection \<open>Memory\<close>

subsubsection \<open>Arrays\<close>

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
    

  lemma pos_sint_to_uint: "0\<le>sint i \<Longrightarrow> sint i = uint i"  
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
    apply (simp add: unat_def)
    by vcg

  lemma array_new_rule_snat[vcg_rules]: "llvm_htriple 
    (\<upharpoonleft>snat.assn n ni ** \<up>\<^sub>d(n>0)) 
    (array_new TYPE('a::llvm_rep) ni) 
    (\<upharpoonleft>array_assn (replicate n init))"
    unfolding array_new_def array_assn_cnv_range_malloc snat.assn_def
    supply [simp] = cnv_snat_to_uint
    by vcg
    
      
  lemma array_free_rule[vcg_rules]: "llvm_htriple (\<upharpoonleft>array_assn xs p) (array_free p) (\<lambda>_. \<box>)"
    unfolding array_free_def array_assn_def
    by vcg

  lemma array_cast_index: 
    assumes "uint (ii::'a::len word) < max_sint LENGTH('a)"  
    shows "sint ii = uint ii" "nat (uint ii) < n \<longleftrightarrow> uint ii < int n"
    using assms
    by (simp_all add: max_sint_def msb_uint_big sint_eq_uint unat_def nat_less_iff)
    
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
    supply [simp] = cnv_snat_to_uint
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
    supply [simp] = cnv_snat_to_uint
    supply [fri_rules] = fri_abs_cong_rl
    by vcg
    
    
    
    
    
    
    
    
end  

subsection \<open>Control Flow\<close>

definition "ABSTRACT c ty P s \<equiv> \<exists>F a. llSTATE (\<upharpoonleft>ty a c ** F) s \<and> P a"  

lemma ABSTRACT_pure: "is_pure A \<Longrightarrow> ABSTRACT c A P h \<longleftrightarrow> (\<exists>a. \<flat>\<^sub>pA a c \<and> P a)"
  unfolding ABSTRACT_def  
  apply (auto simp: STATE_extract)
  apply (auto simp: STATE_def dr_assn_pure_asm_prefix_def sep_conj_def pure_part_def)
  by (metis (full_types) extract_pure_assn pred_lift_def sep_add_zero_sym sep_disj_commute sep_disj_zero sep_empty_app)

lemma ABSTRACT_erule[vcg_decomp_erules]:
  assumes "llSTATE P s"
  assumes "FRAME P (\<upharpoonleft>ty a c) F"
  assumes "llSTATE (\<upharpoonleft>ty a c ** F) s \<Longrightarrow> EXTRACT (Q a)"
  shows "ABSTRACT c ty Q s"
  using assms
  by (auto simp: FRAME_def ABSTRACT_def STATE_def entails_def vcg_tag_defs)


context begin
  interpretation llvm_prim_arith_setup + llvm_prim_ctrl_setup .

  lemma dr_normalize_llc_if[vcg_normalize_simps]: 
    "\<flat>\<^sub>pbool.assn b bi \<Longrightarrow> wp (llc_if bi t e) Q s \<longleftrightarrow> ((b \<longrightarrow> wp t Q s) \<and> (\<not>b\<longrightarrow>wp e Q s))"
    unfolding bool.assn_def by vcg_normalize


  lemma llc_while_annot_dr_rule[vcg_decomp_erules]:  
    assumes "llSTATE P s"
    assumes "FRAME P (I \<sigma> t) F"
    assumes WF: "SOLVE_AUTO_DEFER (wf R)"
    assumes STEP: "\<And>\<sigma> t s. \<lbrakk> llSTATE ((I \<sigma> t ** F)) s \<rbrakk> \<Longrightarrow> EXTRACT (wp (b \<sigma>) (\<lambda>ctdi s\<^sub>1. 
        ABSTRACT ctdi bool.assn (\<lambda>ctd. 
            (ctd \<longrightarrow> wp (f \<sigma>) (\<lambda>\<sigma>' s\<^sub>2. llPOST (EXS t'. I \<sigma>' t' ** \<up>\<^sub>d((t',t)\<in>R) ** F) s\<^sub>2) s\<^sub>1)
          \<and> (\<not>ctd \<longrightarrow> Q \<sigma> s\<^sub>1)
        ) s\<^sub>1
      ) s)"
    shows "wp (llc_while_annot I R b f \<sigma>) Q s"
    using assms(1) apply -
    apply vcg_rl
    apply fact
    apply fact
    apply (drule STEP)
    apply (simp add: fri_extract_simps ABSTRACT_pure vcg_tag_defs bool.assn_def)    
    done
    
end



section \<open>Basic Algorithms\<close>

subsection \<open>Array-Copy\<close>
(* TODO: Still twice as slow as same function compiled with clang! 
  We need native while-loop! *)
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

prepare_code_thms [llvm_code] arraycpy_def
  
export_llvm "arraycpy :: 8 word ptr \<Rightarrow> _ \<Rightarrow> 64 word \<Rightarrow> _" is "arraycpy"

(* TODO: Move / REMOVE?*)
lemma unat_not_msb_imp_less_max_sint: "x \<in> unat ` {w::'a::len word. \<not> msb w} \<Longrightarrow> int x < max_sint LENGTH('a)"
  by (auto simp: unat_def[abs_def] msb_uint_big max_sint_def)


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

subsection \<open>Array-Set\<close>
    
definition arrayset :: "'b::llvm_rep ptr \<Rightarrow> 'b \<Rightarrow> 'a::len2 word \<Rightarrow> unit llM" where
  "arrayset dst c n \<equiv> doM {
    llc_while
      (\<lambda>i. ll_cmp (i<n))
      (\<lambda>i. doM {
        array_upd dst i c;
        let i=i+(signed_nat 1);
        return i
      }) (signed_nat 0);
    return ()
  }"  
  
prepare_code_thms (LLVM) [llvm_code] arrayset_def

export_llvm "arrayset :: 32 word ptr \<Rightarrow> 32 word \<Rightarrow> 64 word \<Rightarrow> _"

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
  

subsection \<open>Array-New-Init\<close>
  
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
