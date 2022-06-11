section \<open>LLVM Shallow Embedding --- Reasoning Setup\<close>
theory LLVM_Shallow_RS
imports 
  "../basic/LLVM_Basic_Main"
  LLVM_Simple_Memory_RS
begin


subsection \<open>Monadification Setup for VCG\<close>

ML \<open>
  structure LLVM_VCG_Monadify = struct
    structure Monadify = Gen_Monadify_Cong (
    
      fun mk_return x = @{mk_term "Mreturn ?x ::_ llM"}
      fun mk_bind m f = @{mk_term "Mbind ?m ?f ::_ llM"}
    
      fun dest_return @{mpat "Mreturn ?x ::_ llM"} = SOME x | dest_return _ = NONE
      fun dest_bind @{mpat "Mbind ?m ?f ::_ llM"} = SOME (m,f) | dest_bind _ = NONE

      val dest_monadT = try LLC_Lib.dest_llM  

      val bind_return_thm = @{lemma "Mbind m Mreturn = m" by simp}
      val return_bind_thm = @{lemma "Mbind (Mreturn x) f = f x" by simp}
      val bind_bind_thm = @{lemma "Mbind (Mbind m (\<lambda>x. f x)) g = Mbind m (\<lambda>x. Mbind (f x) g)" by simp}
      
    )
    
    val _ = Theory.setup
     (Attrib.setup \<^binding>\<open>vcg_const\<close>
      (Args.term >> (fn t => Thm.declaration_attribute (K (Monadify.prepare_add_const_decl false t))))
      "declaration of new vcg-constant")

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
  where "llvm_htriple \<equiv> htriple"
(*abbreviation llvm_htripleF 
  :: "ll_assn \<Rightarrow> ll_assn \<Rightarrow> 'a llM \<Rightarrow> ('a \<Rightarrow> ll_assn) \<Rightarrow> bool" 
  where "llvm_htripleF \<equiv> htripleF llvm_\<alpha>"
abbreviation "llSTATE \<equiv> STATE llvm_\<alpha>"
abbreviation "llPOST \<equiv> POSTCOND llvm_\<alpha>"
*)

locale llvm_prim_setup
(* Locale to contain primitive VCG setup, without data refinement *)

subsection \<open>General VCG Setup\<close>
lemma fri_extract_prod_case[fri_extract_simps]: "(case p of (a,b) \<Rightarrow> (P a b :: ll_assn)) = (EXS a b. \<up>(p=(a,b)) ** P a b)"  
  apply (cases p) apply (rule ext)
  apply (auto simp: sep_algebra_simps)
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
  "\<upharpoonleft>\<^sub>pA a c \<equiv> \<up>pure_part (\<upharpoonleft>A a c)"
  
definition dr_assn_pure_asm_prefix ("\<flat>\<^sub>p_" [1000] 1000) where  
  "\<flat>\<^sub>pA a c \<equiv> pure_part (\<upharpoonleft>A a c) \<and> is_pure A"
  
lemma pure_fri_rule[fri_rules]: "PRECOND (SOLVE_ASM (\<flat>\<^sub>pA a c)) \<Longrightarrow> \<box> \<turnstile> \<upharpoonleft>\<^sub>pA a c"  
  unfolding vcg_tag_defs entails_def dr_assn_pure_prefix_def dr_assn_pure_asm_prefix_def
    is_pure_def
  apply clarsimp
  apply (subst pure_part_pure_eq[symmetric])  
  apply (auto simp: sep_algebra_simps)
  done

lemma prepare_pure_assn[named_ss fri_prepare_simps]: "\<upharpoonleft>A a c = \<upharpoonleft>\<^sub>pA a c" if "is_pure A"
  using that 
  by (simp add: dr_assn_pure_prefix_def is_pure_def)

lemma extract_pure_assn[fri_extract_simps]: "\<upharpoonleft>A a c = \<up>\<flat>\<^sub>pA a c" if "is_pure A"
  using that
  unfolding vcg_tag_defs entails_def dr_assn_pure_asm_prefix_def is_pure_def
  apply (auto simp: sep_algebra_simps)
  done
  
attribute_setup is_pure_rule = \<open>Attrib.add_del 
    (VCG_Lib.chained_decl_attr @{context} @{attributes [named_ss fri_prepare_simps, fri_extract_simps]})
    (VCG_Lib.chained_decl_attr @{context} @{attributes [named_ss fri_prepare_simps del, fri_extract_simps del]})
  \<close>
  \<open>Rules to introduce pure assertions\<close>


(*lemmas [vcg_prep_ext_start_rules] = 
  rev_mp[of "pure_part _"]
  rev_mp[of "llSTATE _ _"]
  rev_mp[of "\<flat>\<^sub>p _ _ _"]
*)  

text \<open>This rule is to be overloaded by later rules\<close>  
(*lemma thin_pure[vcg_prep_ext_rules]: "pure_part A \<Longrightarrow> True" ..*)
    
lemma pure_part_pureD[vcg_prep_ext_rules]: "pure_part (\<up>\<Phi>) \<Longrightarrow> \<Phi>" by simp

(*lemma prep_ext_state[vcg_prep_ext_rules]: 
  "llSTATE P s \<Longrightarrow> pure_part P"  
  unfolding STATE_def by (blast intro: pure_partI)*)
  
lemma prep_ext_pure_part_pure[vcg_prep_ext_rules]: 
  "pure_part (\<upharpoonleft>\<^sub>pA a c) \<Longrightarrow> pure_part (\<upharpoonleft>A a c)"  
  unfolding dr_assn_pure_prefix_def by simp
    
lemma thin_dr_pure_asm[vcg_prep_ext_rules]: "(\<flat>\<^sub>pA a c) \<Longrightarrow> pure_part (\<upharpoonleft>A a c)"
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
  
lemma pure_part_mk_assnD[vcg_prep_ext_rules]: 
  "pure_part (\<upharpoonleft>(mk_assn f) a c) \<Longrightarrow> pure_part (f a c)" 
  by auto
  
  
    
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
  
lemma ll_pto_null[simp]: "\<upharpoonleft>ll_pto x null = sep_false"
  by (simp add: ll_pto_def null_def llvm_pto_def)

  
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
    apply (auto intro: acompat_trans simp: acompat_dom)
    done

end

find_theorems pure_part

lemma ll_pto_base[vcg_prep_ext_rules]: "pure_part (\<upharpoonleft>ll_pto x p) \<Longrightarrow> abase p"
  by (simp add: ll_pto_def null_def llvm_pto_def abase_ptr_def split: llvm_ptr.splits)

lemma abase_not_null[simp]: "\<not>abase null"  
  by (auto simp: abase_ptr_def null_def)
  

text \<open>Assertion to range of array\<close>  
definition "ll_range I \<equiv> mk_assn (\<lambda>f p. \<up>(abase p) ** (\<Union>*i\<in>I. \<upharpoonleft>ll_pto (f i) (p +\<^sub>a i)))"
  
lemma ll_range_not_null[simp]: "\<upharpoonleft>(ll_range I) f null = sep_false"
  by (simp add: ll_range_def)
  
lemma ll_range_base[vcg_prep_ext_rules]: "pure_part (\<upharpoonleft>(ll_range I) xs p) \<Longrightarrow> abase p"
  unfolding ll_range_def apply (cases "abase p") apply (simp_all) done
    
lemma ll_pto_not_same: "(\<upharpoonleft>ll_pto x p ** \<upharpoonleft>ll_pto y p) = sep_false"
  apply (rule ext)
  apply (auto simp add: ll_pto_def llvm_pto_def sep_conj_def sep_algebra_simps split: llvm_ptr.splits)
  done

lemma ll_range_merge: "I\<^sub>1\<inter>I\<^sub>2={} \<Longrightarrow> (\<upharpoonleft>(ll_range I\<^sub>1) f p ** \<upharpoonleft>(ll_range I\<^sub>2) f p) = \<upharpoonleft>(ll_range (I\<^sub>1\<union>I\<^sub>2)) f p"
  unfolding ll_range_def
  by (auto simp: sep_algebra_simps)

lemma ll_range_bogus_upd[simp]: "x\<notin>I \<Longrightarrow> \<upharpoonleft>(ll_range I) (f(x:=v)) p = \<upharpoonleft>(ll_range I) f p"  
  unfolding ll_range_def
  apply (cases "abase p"; simp add: sep_algebra_simps)
  by (rule sep_set_img_cong) (auto)
  
  
lemma open_ll_range: "i\<in>I \<Longrightarrow> \<upharpoonleft>(ll_range I) f p = (\<up>(abase p) ** \<upharpoonleft>ll_pto (f i) (p +\<^sub>a i) ** \<upharpoonleft>(ll_range (I-{i})) f p)"
  unfolding ll_range_def
  by (auto simp: sep_algebra_simps  sep_set_img_remove)

lemma diff_ll_range:
  assumes "F \<turnstile> \<upharpoonleft>(ll_range (I'-I)) f p ** F'"
  shows "\<upharpoonleft>(ll_range I) f p ** F \<turnstile> \<upharpoonleft>(ll_range I') f p ** \<upharpoonleft>(ll_range (I-I')) f p ** F'"
proof -
  have "\<upharpoonleft>(ll_range I) f p ** F \<turnstile> \<upharpoonleft>(ll_range I) f p ** \<upharpoonleft>(ll_range (I'-I)) f p ** F'"
    using assms(1) conj_entails_mono by blast
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

lemma checked_from_val_rule[vcg_rules]: "llvm_htriple (\<box>) (checked_from_val (to_val x)) (\<lambda>r. \<up>(r=x))"  
  unfolding checked_from_val_def
  by vcg
  
  
    
find_theorems "HT "   pure_part



  
text \<open>Standard rules for load and store from pointer\<close>  
lemma ll_load_rule[vcg_rules]: "llvm_htriple (\<upharpoonleft>ll_pto x p) (ll_load p) (\<lambda>r. \<up>(r=x) ** \<upharpoonleft>ll_pto x p)"
  unfolding ll_load_def ll_pto_def llvm_load_def llvm_extract_addr_def to_val_ptr_def
  apply (simp add: llvm_pto_def split!: llvm_ptr.splits)
  apply vcg
  done

lemma ll_store_rule[vcg_rules]: "llvm_htriple (\<upharpoonleft>ll_pto xx p) (ll_store x p) (\<lambda>_. \<upharpoonleft>ll_pto x p)"
  unfolding ll_store_def ll_pto_def llvm_store_def llvm_extract_addr_def to_val_ptr_def
  apply (simp add: llvm_pto_def split!: llvm_ptr.splits)
  apply vcg
  done
  
text \<open>Rules for load and store from indexed pointer, wrt. range\<close>  

lemmas [fri_extract_simps] = sep_conj_assoc


lemma ll_load_rule_range[vcg_rules]:
  shows "llvm_htriple (\<upharpoonleft>(ll_range I) a p ** \<up>\<^sub>!( p' ~\<^sub>a p \<and> p' -\<^sub>a p \<in> I )) (ll_load p') (\<lambda>r. \<up>(r = a (p' -\<^sub>a p)) ** \<upharpoonleft>(ll_range I) a p)"
  apply vcg
  apply (clarsimp simp: open_ll_range)
  apply vcg
  done

lemma ll_store_rule_range[vcg_rules]:
  shows "llvm_htriple (\<upharpoonleft>(ll_range I) a p ** \<up>\<^sub>!( p' ~\<^sub>a p \<and> p' -\<^sub>a p \<in> I )) (ll_store x p') (\<lambda>_. \<upharpoonleft>(ll_range I) (a(p' -\<^sub>a p := x)) p)"
  apply vcg
  apply (clarsimp simp: open_ll_range)
  apply vcg
  done


lemma ll_load_rule_range':
  shows "llvm_htriple (\<upharpoonleft>(ll_range I) a p ** \<up>\<^sub>!( ofs \<in> I )) (ll_load (p +\<^sub>a ofs)) (\<lambda>r. \<up>(r = a ofs) ** \<upharpoonleft>(ll_range I) a p)"
  apply vcg
  done

lemma ll_store_rule_range':
  shows "llvm_htriple (\<upharpoonleft>(ll_range I) a p ** \<up>\<^sub>!( ofs \<in> I )) (ll_store x (p +\<^sub>a ofs)) (\<lambda>_. \<upharpoonleft>(ll_range I) (a(ofs := x)) p)"
  apply vcg
  apply (clarsimp simp: open_ll_range)
  apply vcg
  done

subsubsection \<open>Offsetting Pointers\<close>

(* TODO: The LLVM semantics also allows pointers one past the end of a range, 
  which is not supported by these rules yet.
*)

(* TODO: Move *)
lemma extract_sint_to_val[vcg_normalize_simps]: "llvm_extract_sint (to_val i) = Mreturn (sint i)"
  unfolding llvm_extract_sint_def to_val_word_def
  by (simp add: sint_uint)

lemma extract_unat_to_val[vcg_normalize_simps]: "llvm_extract_unat (to_val n) = Mreturn (unat n)"
  unfolding llvm_extract_unat_def to_val_word_def
  by (auto split: llvm_val.split)
  
  
  
lemma abase_is_ptr[simp]: "abase (the_raw_ptr p) \<Longrightarrow> llvm_ptr.is_addr (the_raw_ptr p)"
  unfolding abase_ptr_def apply (cases p) subgoal for lp apply (cases lp) apply auto done done
  

text \<open>Rule for indexing pointer. Note, the new target address must exist\<close>

(* TODO: Move *)
lemma from_val_LL_PTR[simp]: "from_val (LL_PTR p) = PTR p"
  unfolding from_val_ptr_def by simp

lemma ll_ofs_ptr_rule[vcg_rules]: 
  "llvm_htriple 
    (\<upharpoonleft>ll_pto v (p +\<^sub>a (sint i)) ** \<up>\<^sub>!(abase p))
    (ll_ofs_ptr p i) 
    (\<lambda>r. \<up>(r= p +\<^sub>a (sint i)) ** \<upharpoonleft>ll_pto v (p +\<^sub>a (sint i)))"
  unfolding ll_ofs_ptr_def llvm_ofs_ptr_def llvm_extract_ptr_def ll_pto_def abase_ptr_def aidx_ptr_def
    to_val_ptr_def
  apply vcg
  done

text \<open>Rule for indexing pointer into range. Note, the new target address must exist\<close>
  
lemma ll_ofs_ptr_rule'[vcg_rules]: 
  shows "llvm_htriple 
    (\<upharpoonleft>(ll_range I) x p ** \<up>\<^sub>!(p ~\<^sub>a p' \<and> (p' +\<^sub>a sint i) -\<^sub>a p \<in> I)) 
    (ll_ofs_ptr p' i) 
    (\<lambda>r. \<up>(r= p' +\<^sub>a sint i) ** \<upharpoonleft>(ll_range I) x p)"
  apply vcg
  apply (clarsimp simp: open_ll_range)
  apply vcg
  done

  
subsubsection \<open>Allocate and Free\<close>

text \<open>Memory allocation tag, which expresses ownership of an allocated block.\<close>
definition ll_malloc_tag :: "int \<Rightarrow> 'a::llvm_rep ptr \<Rightarrow> _" 
  where "ll_malloc_tag n p \<equiv> \<up>(n\<ge>0) ** llvm_blockp (the_raw_ptr p) (nat n)"

(* TODO: Move *)
lemma abase_ptr_iff: "abase (PTR r) \<longleftrightarrow> abase r"
  by (simp add: abase_ptr_def)

lemma the_raw_PTR_aidx: "the_raw_ptr (PTR r +\<^sub>a x) = r +\<^sub>a x"
  by (simp add: aidx_ptr_def)

lemma range_split_last: "l\<le>h \<Longrightarrow> {l..<1+h} = insert h {l..<h}" for l h :: int by auto
  
(* TODO: Move *)
lemma llvm_blockv_Nil[simp]: "llvm_blockv [] b = 0"
  by (simp add: llvm_blockv_def)

  
lemma block_base_abase[simp]: "llvm_ptr_is_block_base p \<Longrightarrow> abase (PTR p)"  
  by (cases p; auto simp: llvm_ptr_is_block_base_def abase_ptr_def)
  
lemma llvm_pto_is_ato: "\<lbrakk>llvm_ptr.is_addr p; addr.index (llvm_ptr.the_addr p) \<ge> 0\<rbrakk> 
  \<Longrightarrow> llvm_pto x p = EXACT (llvm_ato x (llvm_ptr.the_addr p))"  
  by (cases p; simp add: llvm_pto_def)
  
find_theorems "to_val (from_val _)"  
  
lemma range_split_aux: "(\<Union>*i\<in>{0..<int (length xs)}. llvm_pto (to_val ((from_val ((xs @ [x]) ! nat i)) :: 'a :: llvm_rep )) (f i))
  = (\<Union>*i\<in>{0..<int (length xs)}. llvm_pto (to_val ((from_val (xs ! nat i)) :: 'a )) (f i))" 
  apply (rule sep_set_img_cong) 
  apply (auto)
  done
  
(* TODO: Move *)  
lemma is_addr_add[simp]: "llvm_ptr.is_addr (p +\<^sub>a i) \<longleftrightarrow> llvm_ptr.is_addr p"  
  by (cases p; auto)
  
lemma addr_idx_the_addr_add[simp]: "llvm_ptr.is_addr p \<Longrightarrow> addr.index (llvm_ptr.the_addr (p +\<^sub>a i)) = addr.index (llvm_ptr.the_addr p) + i"
  by (cases p) auto
  
lemma blockv_range_conv:
  "\<lbrakk>llvm_ptr_is_block_base p; \<forall>x\<in>set xs. llvm_struct_of_val x = struct_of TYPE('a::llvm_rep) \<rbrakk> \<Longrightarrow> 
  EXACT (llvm_blockv xs (llvm_ptr_the_block p)) 
  = (\<upharpoonleft>(ll_range {0..<int (length xs)}) (\<lambda>i. from_val (xs ! nat i) :: 'a ) (PTR p))"
  apply (induction xs rule: rev_induct)
  apply (auto simp: ll_range_def range_split_last sep_algebra_simps EXACT_split ll_pto_def)
  apply (auto simp: llvm_ptr_is_block_base_def range_split_aux the_raw_PTR_aidx)
  apply (auto simp: llvm_pto_is_ato llvm_ptr_is_block_base_def range_split_aux the_raw_PTR_aidx)
  apply (subst sep_conj_commute)
  apply (cases p; simp)
  by (smt (z3) fold_addr_add llvm_ptr.sel llvm_ptr_the_block_def)
  
  
lemma blockvp_range_conv:
  assumes "\<forall>x\<in>set xs. llvm_struct_of_val x = struct_of TYPE('a::llvm_rep)"
  shows "llvm_blockvp xs p = (\<up>(llvm_ptr_is_block_base p) ** \<upharpoonleft>(ll_range {0..<int (length xs)}) (\<lambda>i. from_val (xs!nat i) :: 'a) (PTR p))"
  unfolding llvm_blockvp_def
  apply (cases "llvm_ptr_is_block_base p"; simp add: sep_algebra_simps blockv_range_conv assms)
  done
  
lemma ll_range_init_conv_aux: "\<upharpoonleft>(ll_range {0..<uint n}) (\<lambda>i. from_val (replicate (unat n) (llvm_zero_initializer (struct_of TYPE('a::llvm_rep))) ! nat i)) p
  = \<upharpoonleft>(ll_range {0..<uint n}) (\<lambda>_. init::'a) p"  
  apply (cases "abase p"; simp add: ll_range_def sep_algebra_simps)
  apply (rule sep_set_img_cong; clarsimp)
  subgoal for i
    apply (subgoal_tac "nat i < unat n")
    apply simp
    subgoal by (metis from_to_id' init_zero)
    subgoal by (metis Word.of_nat_unat nat_less_iff)
    done
  done
  

text \<open>Allocation returns an array-base pointer to an initialized range, 
  as well as an allocation tag\<close>
lemma ll_malloc_rule[vcg_rules]: 
  "llvm_htriple 
    (\<up>(n\<noteq>0)) 
    (ll_malloc TYPE('a::llvm_rep) n) 
    (\<lambda>r. \<upharpoonleft>(ll_range {0..< uint n}) (\<lambda>_. init) r ** ll_malloc_tag (uint n) r)"
  unfolding ll_malloc_def ll_pto_def ll_malloc_tag_def llvm_alloc_def    
  supply [simp] = unat_gt_0 abase_ptr_iff the_raw_PTR_aidx blockvp_range_conv ll_range_init_conv_aux
  apply vcg  
  done
  
(* TODO: Move *)  
lemma llvm_blockvp_empty[simp]: "llvm_blockvp [] p = \<up>llvm_ptr_is_block_base p"  
  unfolding llvm_blockvp_def by simp
  
(* TODO: Move *)  
lemma llvm_ptr_is_block_base_NULL[simp]: "\<not>llvm_ptr_is_block_base PTR_NULL" by (simp add: llvm_ptr_is_block_base_def)

(* TODO: Move *)  
lemma llvm_blockvp_split[simp]: "llvm_blockvp (xs@[x]) p = (llvm_blockvp xs p ** llvm_pto x (p +\<^sub>a (int (length xs))))"
  unfolding llvm_blockvp_def
  apply (cases p; simp add: sep_algebra_simps llvm_pto_def EXACT_split)
  apply (auto simp: )
  subgoal for pp
    apply (cases pp; auto simp add: llvm_ptr_is_block_base_def llvm_ptr_the_block_def sep_algebra_simps)
    done
  subgoal by (simp add: llvm_ptr_is_block_base_def)
  done
  
lemma free_blockvp_aux: 
  assumes [simp]: "llvm_ptr_is_block_base p"
  shows "(\<Union>*i\<in>{0..<n}. llvm_pto (to_val (f i)) (p +\<^sub>a i)) = llvm_blockvp (map (to_val o f o int) [0..<nat n]) p"
proof -

  have 1: "{0..<Suc n} = insert n {0..<n}" for n by auto

  have A: "(\<Union>*i\<in>{0..<n}. llvm_pto (to_val (f (int i))) (p +\<^sub>a int i)) = llvm_blockvp (map (to_val o f o int) [0..<n]) p"
    for n :: nat
    apply (induction n)
    apply (auto simp: sep_algebra_simps 1 sep_conj_c)
    done

  have B: "n\<ge>0 \<Longrightarrow> {0..<nat n} = nat`{0..<n}"
    apply (induction "nat n" arbitrary: n)
    apply auto
    by (metis image_atLeastZeroLessThan_int image_eqI int_nat_eq lessThan_iff of_nat_0_le_iff of_nat_eq_iff)
  
    
  show ?thesis
    apply (cases "n\<ge>0"; (simp add: sep_algebra_simps)?)  
    using A[of "nat n"] 
    apply (simp add: B)
    apply (subst (asm) sep_set_img_map)
    subgoal by (simp add: eq_nat_nat_iff inj_on_def)
    by simp
    
qed          
  
  
text \<open>Free takes a range and the matching allocation tag\<close>
lemma ll_free_rule[vcg_rules]:
  "llvm_htriple 
    (\<upharpoonleft>(ll_range {0..<n}) blk p ** ll_malloc_tag n p)
    (ll_free p)
    (\<lambda>_. \<box>)
  "
  unfolding ll_free_def ll_pto_def ll_malloc_tag_def ll_range_def vcg_tag_defs llvm_free_def
    llvm_extract_ptr_def to_val_ptr_def
  apply (cases p; simp)  
  subgoal for pp
    apply (cases "llvm_ptr_is_block_base pp")
    subgoal
      supply [simp] = list_conj_eq_sep_set_img abase_ptr_def aidx_ptr_def 
      supply [named_ss fri_prepare_simps] = sep_set_img_pull_EXS
      apply (simp add: )
      apply (simp add: sep_algebra_simps)
      apply (subst free_blockvp_aux)
      apply vcg
      supply [vcg_rules] = llvmt_freep_rule[where xs="map _ [0..<nat n]", simplified]
      apply vcg
      done
    subgoal by (simp add: llvm_blockp_def)
    done  
  done
  
  (* TODO: xxx, ctd here: the new 'simple' memory model is a mess, but try and ctd here *)
  
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
  
lemma cond_llvm_htripleI: "x = Mreturn y \<Longrightarrow> llvm_htriple \<box> x (\<lambda>r. \<up>(r=y))" by vcg


locale llvm_prim_arith_setup

sublocale llvm_prim_setup < llvm_prim_arith_setup .



definition "vcg_assert_valid_ptr p \<equiv> llvmt_check_ptr (the_raw_ptr p)"  

  
context llvm_prim_arith_setup begin
context 
  notes [simp] = op_lift_arith2'_def op_lift_arith2_def 
                 op_lift_farith1_f_def op_lift_farith2_f_def
                 op_lift_farith1_d_def op_lift_farith2_d_def
                 op_lift_farith1_rm_f_def op_lift_farith2_rm_f_def op_lift_farith3_rm_f_def
                 op_lift_farith1_rm_d_def op_lift_farith2_rm_d_def op_lift_farith3_rm_d_def
                 op_lift_cmp_def op_lift_iconv_def 
  notes [simp] = word_to_lint_convs[symmetric]
  notes [simp] = from_bool_lint_conv udivrem_is_undef_word_conv sdivrem_is_undef_word_conv
  notes [simp] = word_to_lint_to_uint_conv word_to_lint_to_sint_conv
begin

paragraph \<open>Arithmetic\<close>

lemma ll_add_simp[vcg_normalize_simps]: "ll_add a b = Mreturn (a + b)" by (auto simp: ll_add_def)
lemma ll_sub_simp[vcg_normalize_simps]: "ll_sub a b = Mreturn (a - b)" by (auto simp: ll_sub_def)
lemma ll_mul_simp[vcg_normalize_simps]: "ll_mul a b = Mreturn (a * b)" by (auto simp: ll_mul_def)
lemma ll_udiv_simp[vcg_normalize_simps]: "b\<noteq>0 \<Longrightarrow> ll_udiv a b = Mreturn (a div b)" by (auto simp: ll_udiv_def)
lemma ll_urem_simp[vcg_normalize_simps]: "b\<noteq>0 \<Longrightarrow> ll_urem a b = Mreturn (a mod b)" by (auto simp: ll_urem_def)

lemma ll_sdiv_simp[vcg_normalize_simps]: "\<lbrakk>b\<noteq>0; in_srange (sdiv) a b\<rbrakk> \<Longrightarrow> ll_sdiv a b = Mreturn (a sdiv b)" 
  by (auto simp: ll_sdiv_def Let_def)
lemma ll_srem_simp[vcg_normalize_simps]: "\<lbrakk>b\<noteq>0; in_srange (sdiv) a b\<rbrakk> \<Longrightarrow> ll_srem a b = Mreturn (a smod b)" 
  by (auto simp: ll_srem_def)

lemma ll_udiv_rule[vcg_rules]: "WBOUNDS (b\<noteq>0) \<Longrightarrow> llvm_htriple \<box> (ll_udiv a b) (\<lambda>r. \<up>(r = a div b))" 
  unfolding vcg_tag_defs by vcg
lemma ll_urem_rule[vcg_rules]: "WBOUNDS (b\<noteq>0) \<Longrightarrow> llvm_htriple \<box> (ll_urem a b) (\<lambda>r. \<up>(r = a mod b))" 
  unfolding vcg_tag_defs by vcg
lemma ll_sdiv_rule[vcg_rules]: "\<lbrakk>WBOUNDS (b\<noteq>0); WBOUNDS (in_srange (sdiv) a b)\<rbrakk> \<Longrightarrow> llvm_htriple \<box> (ll_sdiv a b) (\<lambda>r. \<up>(r = a sdiv b))"
  unfolding vcg_tag_defs by vcg
lemma ll_srem_rule[vcg_rules]: "\<lbrakk>WBOUNDS (b\<noteq>0); WBOUNDS (in_srange (sdiv) a b)\<rbrakk> \<Longrightarrow> llvm_htriple \<box> (ll_srem a b) (\<lambda>r. \<up>(r = a smod b))"
  unfolding vcg_tag_defs by vcg


lemma ll_fadd_f_simp[vcg_normalize_simps]:     "ll_fadd_f a b = nanize_single (a + b)" by (auto    simp: ll_fadd_f_def) 
lemma ll_fsub_f_simp[vcg_normalize_simps]:     "ll_fsub_f a b = nanize_single (a - b)" by (auto    simp: ll_fsub_f_def) 
lemma ll_fmul_f_simp[vcg_normalize_simps]:     "ll_fmul_f a b = nanize_single (a * b)" by (auto    simp: ll_fmul_f_def) 
lemma ll_fdiv_f_simp[vcg_normalize_simps]:     "ll_fdiv_f a b = nanize_single (a / b)" by (auto    simp: ll_fdiv_f_def) 
lemma ll_frem_f_simp[vcg_normalize_simps]:     "ll_frem_f a b = nanize_single (srem a b)" by (auto simp: ll_frem_f_def) 
lemma ll_sqrt_f32_simp[vcg_normalize_simps]: "ll_sqrt_f32 a = nanize_single (ssqrt a)" by (auto simp:  ll_sqrt_f32_def)
  
lemma ll_fadd_d_simp[vcg_normalize_simps]: "ll_fadd_d a b =   nanize_double (a + b)" by (auto simp: ll_fadd_d_def) 
lemma ll_fsub_d_simp[vcg_normalize_simps]: "ll_fsub_d a b =   nanize_double (a - b)" by (auto simp: ll_fsub_d_def) 
lemma ll_fmul_d_simp[vcg_normalize_simps]: "ll_fmul_d a b =   nanize_double (a * b)" by (auto simp: ll_fmul_d_def) 
lemma ll_fdiv_d_simp[vcg_normalize_simps]: "ll_fdiv_d a b =   nanize_double (a / b)" by (auto simp: ll_fdiv_d_def) 
lemma ll_frem_d_simp[vcg_normalize_simps]: "ll_frem_d a b =   nanize_double (drem a b)" by (auto simp: ll_frem_d_def) 
lemma ll_sqrt_f64_simp[vcg_normalize_simps]: "ll_sqrt_f64 a = nanize_double (dsqrt a)" by (auto simp: ll_sqrt_f64_def) 
  

lemmas [vcg_normalize_simps] = xlate_rounding_mode_simps

lemma ll_x86_avx512_ss_simps[vcg_normalize_simps]:
  "ll_x86_avx512_add_ss_round rm a b = doM {rm \<leftarrow> xlate_rounding_mode rm;   nanize_single (sradd rm a b)}"
  "ll_x86_avx512_sub_ss_round rm a b = doM {rm \<leftarrow> xlate_rounding_mode rm;   nanize_single (srsub rm a b)}"
  "ll_x86_avx512_mul_ss_round rm a b = doM {rm \<leftarrow> xlate_rounding_mode rm;   nanize_single (srmul rm a b)}"
  "ll_x86_avx512_div_ss_round rm a b = doM {rm \<leftarrow> xlate_rounding_mode rm;   nanize_single (srdiv rm a b)}"
  "ll_x86_avx512_sqrt_ss      rm a =   doM {rm \<leftarrow> xlate_rounding_mode rm;   nanize_single (srsqrt rm a)}"
  "ll_x86_avx512_vfmadd_f32   rm a b c = doM {rm \<leftarrow> xlate_rounding_mode rm; nanize_single (srfmadd rm a b c)}"
  unfolding
    ll_x86_avx512_add_ss_round_def
    ll_x86_avx512_sub_ss_round_def
    ll_x86_avx512_mul_ss_round_def
    ll_x86_avx512_div_ss_round_def
    ll_x86_avx512_sqrt_ss_def
    ll_x86_avx512_vfmadd_f32_def
  by auto  

lemma ll_x86_avx512_sd_simps[vcg_normalize_simps]:
  "ll_x86_avx512_add_sd_round rm a b = doM {rm \<leftarrow> xlate_rounding_mode rm;   nanize_double (dradd rm a b)}"
  "ll_x86_avx512_sub_sd_round rm a b = doM {rm \<leftarrow> xlate_rounding_mode rm;   nanize_double (drsub rm a b)}"
  "ll_x86_avx512_mul_sd_round rm a b = doM {rm \<leftarrow> xlate_rounding_mode rm;   nanize_double (drmul rm a b)}"
  "ll_x86_avx512_div_sd_round rm a b = doM {rm \<leftarrow> xlate_rounding_mode rm;   nanize_double (drdiv rm a b)}"
  "ll_x86_avx512_sqrt_sd      rm a =   doM {rm \<leftarrow> xlate_rounding_mode rm;   nanize_double (drsqrt rm a)}"
  "ll_x86_avx512_vfmadd_f64   rm a b c = doM {rm \<leftarrow> xlate_rounding_mode rm; nanize_double (drfmadd rm a b c)}"
  unfolding
    ll_x86_avx512_add_sd_round_def
    ll_x86_avx512_sub_sd_round_def
    ll_x86_avx512_mul_sd_round_def
    ll_x86_avx512_div_sd_round_def
    ll_x86_avx512_sqrt_sd_def
    ll_x86_avx512_vfmadd_f64_def
  by auto  
    
  
  
paragraph \<open>Comparison\<close>
lemma ll_icmp_simps[vcg_normalize_simps]: 
  "ll_icmp_eq a b = Mreturn (from_bool (a = b))" 
  "ll_icmp_ne a b = Mreturn (from_bool (a \<noteq> b))" 
  "ll_icmp_sle a b = Mreturn (from_bool (a <=s b))" 
  "ll_icmp_slt a b = Mreturn (from_bool (a <s b))" 
  "ll_icmp_ule a b = Mreturn (from_bool (a \<le> b))" 
  "ll_icmp_ult a b = Mreturn (from_bool (a < b))" 
  unfolding ll_icmp_eq_def ll_icmp_ne_def ll_icmp_sle_def ll_icmp_slt_def ll_icmp_ule_def ll_icmp_ult_def
  by auto
 
  
definition [vcg_normalize_simps]: "check_ptrs_cmp p\<^sub>1 p\<^sub>2 = (
  if p\<^sub>1=null \<or> p\<^sub>2=null then Mreturn () else doM { vcg_assert_valid_ptr p\<^sub>1; vcg_assert_valid_ptr p\<^sub>2; Mreturn ()})"
  
  
lemma word1_to_lint_ltrue: "word_to_lint (1::1 word) = ltrue"  
  unfolding word_to_lint_def ltrue_def by auto
  
lemma word1_to_lint_lfalse: "word_to_lint (0::1 word) = lfalse"  
  unfolding word_to_lint_def lfalse_def by auto
    
lemma ll_ptrcmp_simps[vcg_normalize_simps]: 
  "ll_ptrcmp_eq a b = doM { check_ptrs_cmp a b; Mreturn (from_bool (a = b))}" 
  "ll_ptrcmp_ne a b = doM { check_ptrs_cmp a b; Mreturn (from_bool (a \<noteq> b))}" 
  unfolding ll_ptrcmp_eq_def ll_ptrcmp_ne_def check_ptrs_cmp_def llvm_ptr_eq_def llvm_ptr_neq_def llvm_extract_ptr_def
  unfolding to_val_ptr_def null_def
  subgoal
    apply (cases a; cases b; auto simp: vcg_normalize_simps from_val_word_def)
    subgoal by (auto simp: word1_to_lint_lfalse word1_to_lint_ltrue bool_to_lint_def)
    subgoal by (auto simp: word1_to_lint_lfalse word1_to_lint_ltrue bool_to_lint_def)
    unfolding vcg_assert_valid_ptr_def llvmt_ptr_eq_def llvmt_check_ptrcmp_def
    apply (auto simp: lint_to_word_def)
    done
  subgoal
    apply (cases a; cases b; auto simp: vcg_normalize_simps from_val_word_def)
    subgoal by (auto simp: word1_to_lint_lfalse word1_to_lint_ltrue bool_to_lint_def)
    subgoal by (auto simp: word1_to_lint_lfalse word1_to_lint_ltrue bool_to_lint_def)
    unfolding vcg_assert_valid_ptr_def llvmt_ptr_neq_def llvmt_check_ptrcmp_def
    apply (auto simp: lint_to_word_def)
    done
  done  
  
lemma ll_fcmp_f_simp[vcg_normalize_simps]:
  "ll_fcmp_oeq_f a b = Mreturn (from_bool (\<not>is_nan_single a \<and> \<not>is_nan_single b \<and> eq_single a b))"
  "ll_fcmp_ogt_f a b = Mreturn (from_bool (\<not>is_nan_single a \<and> \<not>is_nan_single b \<and> a > b))"
  "ll_fcmp_oge_f a b = Mreturn (from_bool (\<not>is_nan_single a \<and> \<not>is_nan_single b \<and> a \<ge> b))"
  "ll_fcmp_olt_f a b = Mreturn (from_bool (\<not>is_nan_single a \<and> \<not>is_nan_single b \<and> a < b))"
  "ll_fcmp_ole_f a b = Mreturn (from_bool (\<not>is_nan_single a \<and> \<not>is_nan_single b \<and> a \<le> b))"
  "ll_fcmp_one_f a b = Mreturn (from_bool (\<not>is_nan_single a \<and> \<not>is_nan_single b \<and> \<not>eq_single a b))"
  "ll_fcmp_ord_f a b = Mreturn (from_bool (\<not>is_nan_single a \<and> \<not>is_nan_single b))"

  "ll_fcmp_ueq_f a b = Mreturn (from_bool (is_nan_single a \<or> is_nan_single b \<or> eq_single a b))"
  "ll_fcmp_ugt_f a b = Mreturn (from_bool (is_nan_single a \<or> is_nan_single b \<or> a > b))"
  "ll_fcmp_uge_f a b = Mreturn (from_bool (is_nan_single a \<or> is_nan_single b \<or> a \<ge> b))"
  "ll_fcmp_ult_f a b = Mreturn (from_bool (is_nan_single a \<or> is_nan_single b \<or> a < b))"
  "ll_fcmp_ule_f a b = Mreturn (from_bool (is_nan_single a \<or> is_nan_single b \<or> a \<le> b))"
  "ll_fcmp_une_f a b = Mreturn (from_bool (is_nan_single a \<or> is_nan_single b \<or> \<not>eq_single a b))"
  "ll_fcmp_uno_f a b = Mreturn (from_bool (is_nan_single a \<or> is_nan_single b))"
  
  unfolding 
    ll_fcmp_oeq_f_def
    ll_fcmp_ogt_f_def
    ll_fcmp_oge_f_def
    ll_fcmp_olt_f_def
    ll_fcmp_ole_f_def
    ll_fcmp_one_f_def
    ll_fcmp_ord_f_def
  
    ll_fcmp_ueq_f_def
    ll_fcmp_ugt_f_def
    ll_fcmp_uge_f_def
    ll_fcmp_ult_f_def
    ll_fcmp_ule_f_def
    ll_fcmp_une_f_def
    ll_fcmp_uno_f_def
  
  apply (auto simp: op_lift_fcmp_f_def)
  done
    

lemma ll_fcmp_d_simp[vcg_normalize_simps]:
  "ll_fcmp_oeq_d a b = Mreturn (from_bool (\<not>is_nan_double a \<and> \<not>is_nan_double b \<and> eq_double a b))"
  "ll_fcmp_ogt_d a b = Mreturn (from_bool (\<not>is_nan_double a \<and> \<not>is_nan_double b \<and> a > b))"
  "ll_fcmp_oge_d a b = Mreturn (from_bool (\<not>is_nan_double a \<and> \<not>is_nan_double b \<and> a \<ge> b))"
  "ll_fcmp_olt_d a b = Mreturn (from_bool (\<not>is_nan_double a \<and> \<not>is_nan_double b \<and> a < b))"
  "ll_fcmp_ole_d a b = Mreturn (from_bool (\<not>is_nan_double a \<and> \<not>is_nan_double b \<and> a \<le> b))"
  "ll_fcmp_one_d a b = Mreturn (from_bool (\<not>is_nan_double a \<and> \<not>is_nan_double b \<and> \<not>eq_double a b))"
  "ll_fcmp_ord_d a b = Mreturn (from_bool (\<not>is_nan_double a \<and> \<not>is_nan_double b))"

  "ll_fcmp_ueq_d a b = Mreturn (from_bool (is_nan_double a \<or> is_nan_double b \<or> eq_double a b))"
  "ll_fcmp_ugt_d a b = Mreturn (from_bool (is_nan_double a \<or> is_nan_double b \<or> a > b))"
  "ll_fcmp_uge_d a b = Mreturn (from_bool (is_nan_double a \<or> is_nan_double b \<or> a \<ge> b))"
  "ll_fcmp_ult_d a b = Mreturn (from_bool (is_nan_double a \<or> is_nan_double b \<or> a < b))"
  "ll_fcmp_ule_d a b = Mreturn (from_bool (is_nan_double a \<or> is_nan_double b \<or> a \<le> b))"
  "ll_fcmp_une_d a b = Mreturn (from_bool (is_nan_double a \<or> is_nan_double b \<or> \<not>eq_double a b))"
  "ll_fcmp_uno_d a b = Mreturn (from_bool (is_nan_double a \<or> is_nan_double b))"
  
  unfolding 
    ll_fcmp_oeq_d_def
    ll_fcmp_ogt_d_def
    ll_fcmp_oge_d_def
    ll_fcmp_olt_d_def
    ll_fcmp_ole_d_def
    ll_fcmp_one_d_def
    ll_fcmp_ord_d_def
  
    ll_fcmp_ueq_d_def
    ll_fcmp_ugt_d_def
    ll_fcmp_uge_d_def
    ll_fcmp_ult_d_def
    ll_fcmp_ule_d_def
    ll_fcmp_une_d_def
    ll_fcmp_uno_d_def
  
  apply (auto simp: op_lift_fcmp_d_def)
  done
  
      
  
paragraph \<open>Bitwise\<close>

lemma ll_and_simp[vcg_normalize_simps]: "ll_and a b = Mreturn (a AND b)" by (auto simp: ll_and_def)
lemma ll_or_simp[vcg_normalize_simps]: "ll_or a b = Mreturn (a OR b)" by (auto simp: ll_or_def)
lemma ll_xor_simp[vcg_normalize_simps]: "ll_xor a b = Mreturn (a XOR b)" by (auto simp: ll_xor_def)
  
lemma ll_shl_simp[vcg_normalize_simps]: "unat b < LENGTH ('a) \<Longrightarrow> ll_shl (a::'a::len word) b = Mreturn (a << unat b)" 
  by (auto simp: ll_shl_def Let_def shift_ovf_def bitSHL'_def)
  
lemma ll_lshr_simp[vcg_normalize_simps]: "unat b < LENGTH ('a) \<Longrightarrow> ll_lshr (a::'a::len word) b = Mreturn (a >> unat b)" 
  by (auto simp: ll_lshr_def Let_def shift_ovf_def bitLSHR'_def)

lemma ll_ashr_simp[vcg_normalize_simps]: "unat b < LENGTH ('a) \<Longrightarrow> ll_ashr (a::'a::len word) b = Mreturn (a >>> unat b)" 
  by (auto simp: ll_ashr_def Let_def shift_ovf_def bitASHR'_def)
  
lemma [vcg_rules]:
  fixes a b :: "'a::len word" 
  assumes "WBOUNDS (unat b < LENGTH ('a))"  
  shows ll_shl_rule: "llvm_htriple \<box> (ll_shl a b) (\<lambda>r. \<up>(r=a<<unat b))"
    and ll_lshr_rule: "llvm_htriple \<box> (ll_lshr a b) (\<lambda>r. \<up>(r=a>>unat b))"
    and ll_ashr_rule: "llvm_htriple \<box> (ll_ashr a b) (\<lambda>r. \<up>(r=a>>>unat b))"
  using assms unfolding vcg_tag_defs
  by vcg  
  
paragraph \<open>Conversion\<close>
    
lemma ll_trunc_simp[vcg_normalize_simps]: "is_down' UCAST ('a\<rightarrow>'b) \<Longrightarrow> ll_trunc (a::'a::len word) TYPE('b::len word) = Mreturn (UCAST ('a\<rightarrow>'b) a)"
  by (auto simp: ll_trunc_def llb_trunc_def Let_def)
  
lemma ll_zext_simp[vcg_normalize_simps]: "is_up' UCAST ('a\<rightarrow>'b) \<Longrightarrow> ll_zext (a::'a::len word) TYPE('b::len word) = Mreturn (UCAST ('a\<rightarrow>'b) a)"
  by (auto simp: ll_zext_def llb_zext_def Let_def)
  
lemma ll_sext_simp[vcg_normalize_simps]: "is_up' SCAST ('a\<rightarrow>'b) \<Longrightarrow> ll_sext (a::'a::len word) TYPE('b::len word) = Mreturn (SCAST ('a\<rightarrow>'b) a)"
  by (auto simp: ll_sext_def llb_sext_def Let_def)

  
lemmas ll_trunc_rule[vcg_rules] = cond_llvm_htripleI[OF ll_trunc_simp, OF WBOUNDSD]
lemmas ll_zext_rule[vcg_rules] = cond_llvm_htripleI[OF ll_zext_simp, OF WBOUNDSD]
lemmas ll_sext_rule[vcg_rules] = cond_llvm_htripleI[OF ll_sext_simp, OF WBOUNDSD]
    
end
end

(* TODO: Proper handling of ptrcmp
context
begin
  interpretation llvm_prim_arith_setup .

  text \<open>Comparison with null are always simplified\<close>  
  lemma ll_ptrcmp_null_simps[vcg_normalize_simps]: 
    "ll_ptrcmp_eq a null = doM { Mreturn (from_bool (a = null))}" 
    "ll_ptrcmp_eq null b = doM { Mreturn (from_bool (b = null))}" 
    "ll_ptrcmp_ne a null = doM { Mreturn (from_bool (a \<noteq> null))}" 
    "ll_ptrcmp_ne null b = doM { Mreturn (from_bool (b \<noteq> null))}" 
    by (vcg_normalize; simp add: eq_commute[of null]; fail)+
  
end
*)

context llvm_prim_mem_setup begin
  lemma vcg_assert_valid_ptr_rule[vcg_rules]: "llvm_htriple (\<upharpoonleft>ll_pto x p) (vcg_assert_valid_ptr p) (\<lambda>_. \<upharpoonleft>ll_pto x p)"
    unfolding vcg_assert_valid_ptr_def ll_pto_def
    apply vcg
    done
  
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
  
lemma llc_if_simp[vcg_normalize_simps]: "wpa A (llc_if b t e) Q s \<longleftrightarrow> (to_bool b \<longrightarrow> wpa A t Q s) \<and> (\<not>to_bool b \<longrightarrow> wpa A e Q s)"
  unfolding llc_if_def by simp

lemma if_simp[vcg_normalize_simps]: "wpa A (If b t e) Q s \<longleftrightarrow> (b \<longrightarrow> wpa A t Q s) \<and> (\<not>b \<longrightarrow> wpa A e Q s)"
  by simp
  
end  
    
text \<open>The while command is handled by a standard invariant/variant rule.\<close>  

lemma llc_while_unfold: "llc_while b f \<sigma> = doM { ctd \<leftarrow> b \<sigma>; llc_if ctd (doM { \<sigma>\<leftarrow>f \<sigma>; llc_while b f \<sigma>}) (Mreturn \<sigma>)}"
  unfolding llc_while_def
  unfolding llc_while_def llc_if_def
  apply (rewrite Mwhile_unfold)
  apply simp
  done

definition llc_while_annot :: "('\<sigma>::llvm_rep \<Rightarrow> 't \<Rightarrow> llvm_amemory \<Rightarrow> bool) \<Rightarrow> ('t\<times>'t) set \<Rightarrow> ('\<sigma>\<Rightarrow>1 word llM) \<Rightarrow> _"
  where [llvm_pre_simp]: "llc_while_annot I R \<equiv> llc_while"

declare [[vcg_const "llc_while_annot I R"]]
  
lemma annotate_llc_while: "llc_while = llc_while_annot I R" by (simp add: llc_while_annot_def) 
  
context llvm_prim_ctrl_setup begin

lemma basic_while_rule:
  assumes "wf R"
  assumes "STATE asf (I \<sigma> t) s"
  assumes STEP: "\<And>\<sigma> t s. \<lbrakk> STATE asf (I \<sigma> t) s \<rbrakk> \<Longrightarrow> wpa A (b \<sigma>) (\<lambda>ctd s\<^sub>1. 
    (to_bool ctd \<longrightarrow> wpa A (f \<sigma>) (\<lambda>\<sigma>' s\<^sub>2. STATE asf (EXS t'. I \<sigma>' t' ** \<up>((t',t)\<in>R)) s\<^sub>2) s\<^sub>1)
  \<and> (\<not>to_bool ctd \<longrightarrow> Q \<sigma> s\<^sub>1)
    ) s"
  shows "wpa A (llc_while b f \<sigma>) Q s"
  using assms(1,2)
proof (induction t arbitrary: \<sigma> s)
  case (less t)
  show ?case 
    apply (subst llc_while_unfold)
    apply vcg
    apply (rule wpa_monoI[OF STEP])
    apply fact
    subgoal for r s\<^sub>1
      apply (cases "to_bool r"; simp add: vcg_normalize_simps)
      apply vcg
      apply (erule wpa_monoI; clarsimp; fri_extract)
      apply (rule less.IH; assumption)
      done
    subgoal by simp  
    subgoal by simp  
    done
qed          

text \<open>
  Standard while rule. 
  Note that the second parameter of the invariant is the termination measure, which must
  decrease wrt. a well-founded relation. It is initialized as a schematic variable, and must be 
  derivable via frame inference. In practice, the invariant will contain a \<open>\<up>(t=\<dots>)\<close> part.
\<close>  
lemma llc_while_annot_rule[vcg_decomp_erules]:  
  assumes "STATE asf P s"
  assumes "FRAME P (I \<sigma> t) F"
  assumes WF: "SOLVE_AUTO_DEFER (wf R)"
  assumes STEP: "\<And>\<sigma> t s. \<lbrakk> STATE asf ((I \<sigma> t ** F)) s \<rbrakk> \<Longrightarrow> EXTRACT (wpa A (b \<sigma>) (\<lambda>ctd s\<^sub>1. 
    (to_bool ctd \<longrightarrow> wpa A (f \<sigma>) (\<lambda>\<sigma>' s\<^sub>2. POSTCOND asf (EXS t'. I \<sigma>' t' ** \<up>((t',t)\<in>R) ** F) s\<^sub>2) s\<^sub>1)
  \<and> (\<not>to_bool ctd \<longrightarrow> Q \<sigma> s\<^sub>1)
    ) s)"
  shows "wpa A (llc_while_annot I R b f \<sigma>) Q s"
proof -
  from \<open>STATE asf P s\<close> \<open>FRAME P (I \<sigma> t) F\<close> have PRE: "STATE asf (I \<sigma> t ** F) s"
    using FRAME_def STATE_monoI by blast

  note STEP'=STEP[unfolded vcg_tag_defs]  
    
  show ?thesis  
    unfolding llc_while_annot_def
    apply (rule basic_while_rule[where I="\<lambda>\<sigma> t. I \<sigma> t ** F" and R=R])
    subgoal using WF unfolding vcg_tag_defs .
    apply (rule PRE)
    apply (erule wpa_monoI[OF STEP'])
    apply auto
    apply (erule wpa_monoI;simp add: sep_algebra_simps)
    apply (erule wpa_monoI;simp add: sep_algebra_simps)
    done
  
qed  
  
end

subsection \<open>LLVM Code Generator Setup\<close>

lemma elim_higher_order_return[llvm_pre_simp]: "doM { x::_\<Rightarrow>_ \<leftarrow> Mreturn f; m x } = m f" by simp


text \<open>Useful shortcuts\<close>

subsubsection \<open>Direct Arithmetic\<close>

(* TODO: How would we handle conditional rules, like from Mreturn (a div b) to ll_udiv?
  We would have to transform the program to a weaker one, that asserts preconditions, and
  then reason about this!
*)

context begin
  interpretation llvm_prim_arith_setup .

  lemma arith_inlines[llvm_pre_simp, vcg_monadify_xforms]: 
    "Mreturn (a+b) = ll_add a b" 
    "Mreturn (a-b) = ll_sub a b" 
    "Mreturn (a*b) = ll_mul a b" 
  
    "Mreturn (a AND b) = ll_and a b" 
    "Mreturn (a OR b) = ll_or a b" 
    "Mreturn (a XOR b) = ll_xor a b" 
    by vcg                                           

  lemma farith_inlines_f[llvm_pre_simp, vcg_monadify_xforms]: 
    "nanize_single (a+b) = ll_fadd_f a b" 
    "nanize_single (a-b) = ll_fsub_f a b" 
    "nanize_single (a*b) = ll_fmul_f a b" 
    "nanize_single (a/b) = ll_fdiv_f a b" 
    "nanize_single (srem a b) = ll_frem_f a b" 
    "nanize_single (ssqrt a) = ll_sqrt_f32 a" 
    by vcg

  lemma farith_inlines_d[llvm_pre_simp, vcg_monadify_xforms]: 
    "nanize_double (a+b) = ll_fadd_d a b" 
    "nanize_double (a-b) = ll_fsub_d a b" 
    "nanize_double (a*b) = ll_fmul_d a b" 
    "nanize_double (a/b) = ll_fdiv_d a b" 
    "nanize_double (drem a b) = ll_frem_d a b" 
    "nanize_double (dsqrt a) = ll_sqrt_f64 a" 
    by vcg
    
  term sqrt  
    
end  

text \<open>Activates AVX512f for Isabelle/LLVM \<close>
locale llvm_avx512f_setup begin

declare [[llc_compile_avx512f]]

context begin
  interpretation llvm_prim_arith_setup .

  fun avx512_rm where
    "avx512_rm To_nearest = AVX512_FROUND_TO_NEAREST_NO_EXC"
  | "avx512_rm float_To_zero = AVX512_FROUND_TO_ZERO_NO_EXC"
  | "avx512_rm To_pinfinity = AVX512_FROUND_TO_POS_INF_NO_EXC"
  | "avx512_rm To_ninfinity = AVX512_FROUND_TO_NEG_INF_NO_EXC"
  
  lemmas [llvm_pre_simp(*, vcg_monadify_xforms*)] = avx512_rm.simps
  
  lemma avx512_arith_inlines[llvm_pre_simp(*, vcg_monadify_xforms*)]:
    "nanize_double (dradd rm a b) = ll_x86_avx512_add_sd_round (avx512_rm rm) a b"
    "nanize_double (drsub rm a b) = ll_x86_avx512_sub_sd_round (avx512_rm rm) a b"
    "nanize_double (drmul rm a b) = ll_x86_avx512_mul_sd_round (avx512_rm rm) a b"
    "nanize_double (drdiv rm a b) = ll_x86_avx512_div_sd_round (avx512_rm rm) a b"
    "nanize_double (drsqrt rm a) = ll_x86_avx512_sqrt_sd (avx512_rm rm) a"
    "nanize_double (drfmadd rm a b c) = ll_x86_avx512_vfmadd_f64 (avx512_rm rm) a b c"
    by (cases rm; vcg)+

  lemma avx512_arith_inlines_ss[llvm_pre_simp(*, vcg_monadify_xforms*)]:
    "nanize_single (sradd rm a b) = ll_x86_avx512_add_ss_round (avx512_rm rm) a b"
    "nanize_single (srsub rm a b) = ll_x86_avx512_sub_ss_round (avx512_rm rm) a b"
    "nanize_single (srmul rm a b) = ll_x86_avx512_mul_ss_round (avx512_rm rm) a b"
    "nanize_single (srdiv rm a b) = ll_x86_avx512_div_ss_round (avx512_rm rm) a b"
    "nanize_single (srsqrt rm a) = ll_x86_avx512_sqrt_ss (avx512_rm rm) a"
    "nanize_single (srfmadd rm a b c) = ll_x86_avx512_vfmadd_f32 (avx512_rm rm) a b c"
    by (cases rm; vcg)+
      
end
end


subsubsection \<open>Direct Comparison\<close>
abbreviation (input) ll_cmp' :: "bool \<Rightarrow> 1 word" where "ll_cmp' \<equiv> from_bool"
definition [vcg_monadify_xforms,llvm_inline]: "ll_cmp b \<equiv> Mreturn (ll_cmp' b)"
  
(* To work with current monadify implementation, 
  we have to replace each operation by a constants
  
  TODO: Can we change monadifier?
*)

definition "ll_cmp'_eq a b \<equiv> ll_cmp' (a=b)"
definition "ll_cmp'_ne a b \<equiv> ll_cmp' (a\<noteq>b)"
definition "ll_cmp'_ule a b \<equiv> ll_cmp' (a\<le>b)" for a b :: "_ word"
definition "ll_cmp'_ult a b \<equiv> ll_cmp' (a<b)" for a b :: "_ word"
definition "ll_cmp'_sle a b \<equiv> ll_cmp' (a <=s b)" for a b :: "_ word"
definition "ll_cmp'_slt a b \<equiv> ll_cmp' (a <s b)" for a b :: "_ word"

definition "ll_cmp'_fle_f a b \<equiv> ll_cmp' (a\<le>b)" for a b :: "single"
definition "ll_cmp'_flt_f a b \<equiv> ll_cmp' (a<b)" for a b :: "single"
                                          
definition "ll_cmp'_fle_d a b \<equiv> ll_cmp' (a\<le>b)" for a b :: "double"
definition "ll_cmp'_flt_d a b \<equiv> ll_cmp' (a<b)" for a b :: "double"

lemmas ll_cmp'_defs = ll_cmp'_eq_def ll_cmp'_ne_def ll_cmp'_ule_def ll_cmp'_ult_def ll_cmp'_sle_def ll_cmp'_slt_def
                      ll_cmp'_fle_f_def ll_cmp'_flt_f_def
                      ll_cmp'_fle_d_def ll_cmp'_flt_d_def

lemmas [llvm_pre_simp, vcg_monadify_xforms] = ll_cmp'_defs[symmetric]

(* TODO: Move *)
lemma fcompare_has_ord_semantics:
  "a<b \<Longrightarrow> \<not>is_nan_single a \<and> \<not>is_nan_single b"
  "a\<le>b \<Longrightarrow> \<not>is_nan_single a \<and> \<not>is_nan_single b"
  apply (all transfer')
  unfolding less_float_def less_eq_float_def flt_def fle_def fcompare_def 
  by auto

lemma fcompare_ord_conv:
  "\<not> is_nan_single a \<and> \<not> is_nan_single b \<and> a < b \<longleftrightarrow> a < b"  
  "\<not> is_nan_single a \<and> \<not> is_nan_single b \<and> a \<le> b \<longleftrightarrow> a \<le> b"  
  using fcompare_has_ord_semantics by blast+
  

lemma dcompare_has_ord_semantics:
  "a<b \<Longrightarrow> \<not>is_nan_double a \<and> \<not>is_nan_double b"
  "a\<le>b \<Longrightarrow> \<not>is_nan_double a \<and> \<not>is_nan_double b"
  apply (all transfer')
  unfolding less_float_def less_eq_float_def flt_def fle_def fcompare_def 
  by auto

lemma dcompare_ord_conv:
  "\<not> is_nan_double a \<and> \<not> is_nan_double b \<and> a < b \<longleftrightarrow> a < b"  
  "\<not> is_nan_double a \<and> \<not> is_nan_double b \<and> a \<le> b \<longleftrightarrow> a \<le> b"  
  using dcompare_has_ord_semantics by blast+

    
context begin
  interpretation llvm_prim_arith_setup .

  lemma ll_cmp'_xforms[vcg_monadify_xforms,llvm_pre_simp]:
    "Mreturn (ll_cmp'_eq  a b) = ll_icmp_eq a b" 
    "Mreturn (ll_cmp'_ne  a b) = ll_icmp_ne a b" 
    "Mreturn (ll_cmp'_ult a b) = ll_icmp_ult a b" 
    "Mreturn (ll_cmp'_ule a b) = ll_icmp_ule a b" 
    "Mreturn (ll_cmp'_slt a b) = ll_icmp_slt a b" 
    "Mreturn (ll_cmp'_sle a b) = ll_icmp_sle a b" 
    unfolding ll_cmp_def ll_cmp'_defs
    by (all vcg_normalize)


  lemma ll_cmp'_float_xforms[vcg_monadify_xforms,llvm_pre_simp]:
    "Mreturn (ll_cmp'_flt_f  a b) = ll_fcmp_olt_f a b" 
    "Mreturn (ll_cmp'_fle_f  a b) = ll_fcmp_ole_f a b" 
    unfolding ll_cmp'_defs
    apply (all vcg_normalize)
    apply (simp_all add: fcompare_ord_conv)
    done
    
  lemma ll_cmp'_double_xforms[vcg_monadify_xforms,llvm_pre_simp]:
    "Mreturn (ll_cmp'_flt_d a b) = ll_fcmp_olt_d a b" 
    "Mreturn (ll_cmp'_fle_d a b) = ll_fcmp_ole_d a b" 
    unfolding ll_cmp'_defs
    apply (all vcg_normalize)
    apply (simp_all add: dcompare_ord_conv)
    done
    
  text \<open>Comparison with null pointers can be transformed automatically.
    Any other pointer comparisons carry additional precondition, and cannot
    be generated from pure statements.\<close>  
  definition "ll_eq_null a \<equiv> ll_cmp'_eq a null"  
  definition "ll_ne_null a \<equiv> ll_cmp'_ne a null"  
    
  lemma ll_ptrcmp'_xforms[vcg_monadify_xforms,llvm_pre_simp]:
    "Mreturn (ll_eq_null a) = ll_ptrcmp_eq a null" 
    "Mreturn (ll_ne_null a) = ll_ptrcmp_ne a null" 
    "ll_cmp'_eq a null = ll_eq_null a" 
    "ll_cmp'_eq null b = ll_eq_null b" 
    "ll_cmp'_ne a null = ll_ne_null a" 
    "ll_cmp'_ne null b = ll_ne_null b" 
    unfolding ll_cmp_def ll_cmp'_defs ll_eq_null_def ll_ne_null_def
    by (all \<open>vcg_normalize; simp add: eq_commute[of null]\<close>)
  
    
end    

subsubsection \<open>Boolean Operations\<close>
lemma llvm_if_inline[llvm_pre_simp,vcg_monadify_xforms]: "If b t e = llc_if (from_bool b) t e"  
  by (auto simp: llc_if_def)
  
lemma from_bool_to_bool1[llvm_pre_simp]: "from_bool (to_bool (x::1 word)) = x"
  by (metis from_bool_1 to_bool_eq word1_cases)
  
lemma (in llvm_prim_arith_setup) llvm_from_bool_inline[llvm_pre_simp]: 
  "from_bool (a\<and>b) = (from_bool a AND from_bool b)"  
  "from_bool (a\<or>b) = (from_bool a OR from_bool b)"  
  "(from_bool (\<not>a)::1 word) = (1 - (from_bool a :: 1 word))"  
  subgoal by (metis and.idem and_zero_eq bit.conj_zero_left from_bool_eq_if')
  subgoal by (smt (z3) from_bool_0 or.idem word_bw_comms(2) word_log_esimps(3))
  subgoal by (metis (full_types) cancel_comm_monoid_add_class.diff_cancel diff_zero from_bool_eq_if')
  done

subsubsection \<open>Products\<close>
  
lemma inline_prod_case[llvm_pre_simp]: "(\<lambda>(a,b). f a b) = (\<lambda>x. doM { a\<leftarrow>prod_extract_fst x; b \<leftarrow> prod_extract_snd x; f a b })"  
  by (auto simp: prod_ops_simp)
  
lemma inline_return_prod_case[llvm_pre_simp]: 
  "Mreturn (case x of (a,b) \<Rightarrow> f a b) = (case x of (a,b) \<Rightarrow> Mreturn (f a b))" by (rule prod.case_distrib)
  
  
lemma inline_return_prod[llvm_pre_simp]: "Mreturn (a,b) = doM { x \<leftarrow> prod_insert_fst init a; x \<leftarrow> prod_insert_snd x b; Mreturn x }"  
  by (auto simp: prod_ops_simp)
  
lemma ll_extract_pair_pair:
  "ll_extract_value (a,b) 0 = Mreturn a"
  "ll_extract_value (a,b) 1 = Mreturn b" 
  unfolding ll_extract_value_def llvm_extract_value_def checked_from_val_def
  by auto
  
txt \<open>This lemma removes insert-extracts artifacts. 
  This makes code lemmas smaller, and can speed up preprocessing significantly.\<close>
lemma ins_extr_prod_simp[llvm_pre_simp]: "doM {
    (x::'a::llvm_rep \<times> 'b::llvm_rep) \<leftarrow> ll_insert_value init a 0;
    x \<leftarrow> ll_insert_value x b Numeral1;
    a::'a \<leftarrow> ll_extract_value x 0;
    b::'b \<leftarrow> ll_extract_value x Numeral1;
    f a b
  } = f a b"
  apply (simp add: ll_insert_value_def ll_extract_value_def llvm_insert_value_def llvm_extract_value_def checked_from_val_def)
  done
  
  
subsubsection \<open>Marking of constants\<close>    
definition "ll_const x \<equiv> Mreturn x"

lemma ll_const_inline[llvm_pre_simp]: "Mbind (ll_const x) f = f x" by (auto simp: ll_const_def)
  
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

lemma vcg_prep_delete_assn[vcg_prep_ext_rules]: 
  "pure_part (\<upharpoonleft>assn a c) \<Longrightarrow> dflt_EPURE a c"
  by (auto simp: assn_def dflt_EPURE_correct)
  

definition "is_un_op PRE cop mop aop \<equiv> 
  (\<forall>a::'c. I a \<and> PRE TYPE('c) (\<alpha> a) \<longrightarrow> I (mop a) \<and> \<alpha> (mop a) = aop (\<alpha> a) \<and> cop a = Mreturn (mop a))"
  
definition "is_bin_op PRE cop mop aop \<equiv> 
  (\<forall>a b::'c. I a \<and> I b \<and> PRE TYPE('c) (\<alpha> a) (\<alpha> b) \<longrightarrow> I (mop a b) \<and> \<alpha> (mop a b) = aop (\<alpha> a) (\<alpha> b) \<and> cop a b = Mreturn (mop a b))"

abbreviation "is_un_op' cop mop aop \<equiv> is_un_op (dflt_PRE1 aop) cop mop aop"
abbreviation "is_bin_op' cop mop aop \<equiv> is_bin_op (dflt_PRE2 aop) cop mop aop"

lemma is_un_opI[intro?]:
  assumes "\<And>a. \<lbrakk>I a; PRE TYPE('c) (\<alpha> a)\<rbrakk> \<Longrightarrow> cop a = Mreturn (mop a)"
  assumes "\<And>a. \<lbrakk>I a; PRE TYPE('c) (\<alpha> a)\<rbrakk> \<Longrightarrow> I (mop a)"
  assumes "\<And>a. \<lbrakk>I a; PRE TYPE('c) (\<alpha> a)\<rbrakk> \<Longrightarrow> \<alpha> (mop a) = aop (\<alpha> a)"
  shows "is_un_op PRE cop mop aop"
  using assms unfolding is_un_op_def by blast

lemma is_bin_opI[intro?]:
  assumes "\<And>a b. \<lbrakk>I a; I b; PRE TYPE('c) (\<alpha> a) (\<alpha> b)\<rbrakk> \<Longrightarrow> cop a b = Mreturn (mop a b)"
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
    (\<forall>a b. I a \<and> I b \<longrightarrow> (cop a b = Mreturn (from_bool (mop a b)) \<and> (mop a b \<longleftrightarrow> aop (\<alpha> a) (\<alpha> b))))"
  
  lemma is_cmp_opI[intro?]:
    assumes "\<And>a b. \<lbrakk>I a; I b\<rbrakk> \<Longrightarrow> cop a b = Mreturn (from_bool (mop a b))"
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
  
subsection \<open>Booleans\<close>

   
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

abbreviation (input) ll_not1 :: "1 word \<Rightarrow> 1 word llM" where "ll_not1 x \<equiv> ll_add x 1"  
    
lemma ll_not1_inline[llvm_pre_simp]: "Mreturn (~~x) \<equiv> ll_not1 x"
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
  "bool.is_un_op' ll_not1 (NOT) Not" 
  apply (all \<open>rule\<close>)
  apply (simp_all only: to_bool_logics)
  apply (all \<open>vcg_normalize?\<close>)
  apply (simp_all add: word1_NOT_eq)
  done
    
lemmas bool_op_rules[vcg_rules] = 
  bool_bin_ops[THEN bool.bin_op_tmpl]
  bool_un_ops[THEN bool.un_op_tmpl]
  
end  
  

subsection \<open>Control Flow\<close>

definition "ABSTRACT asf c ty P s \<equiv> \<exists>F a. STATE asf (\<upharpoonleft>ty a c ** F) s \<and> P a"  

(*
lemma ABSTRACT_pure: "is_pure PP \<Longrightarrow> ABSTRACT A asf c PP P h \<longleftrightarrow> (\<exists>a. \<flat>\<^sub>pPP a c \<and> P a)"
  unfolding ABSTRACT_def  
  apply (auto simp: STATE_extract)
  apply (auto simp: STATE_def dr_assn_pure_asm_prefix_def sep_conj_def pure_part_def)
  
  oops
  by (metis (full_types) extract_pure_assn pred_lift_def sep_add_zero_sym sep_disj_commute sep_disj_zero sep_empty_app)
*)  

lemma ABSTRACT_erule[vcg_decomp_erules]:
  assumes "STATE asf P s"
  assumes "FRAME P (\<upharpoonleft>ty a c) F"
  assumes "STATE asf (\<upharpoonleft>ty a c ** F) s \<Longrightarrow> EXTRACT (Q a)"
  shows "ABSTRACT asf c ty Q s"
  using assms
  by (force simp: FRAME_def ABSTRACT_def STATE_def entails_def vcg_tag_defs)
  


context begin
  interpretation llvm_prim_arith_setup + llvm_prim_ctrl_setup .

  lemma dr_normalize_llc_if[vcg_normalize_simps]: 
    "\<flat>\<^sub>pbool.assn b bi \<Longrightarrow> wpa A (llc_if bi t e) Q s \<longleftrightarrow> ((b \<longrightarrow> wpa A t Q s) \<and> (\<not>b\<longrightarrow>wpa A e Q s))"
    unfolding bool.assn_def by vcg_normalize


  lemma llc_while_annot_dr_rule[vcg_decomp_erules]:  
    assumes "STATE asf P s"
    assumes "FRAME P (I \<sigma> t) F"
    assumes WF: "SOLVE_AUTO_DEFER (wf R)"
    assumes STEP: "\<And>\<sigma> t s. \<lbrakk> STATE asf ((I \<sigma> t ** F)) s \<rbrakk> \<Longrightarrow> EXTRACT (wpa A (b \<sigma>) (\<lambda>ctdi s\<^sub>1. 
        ABSTRACT asf ctdi bool.assn (\<lambda>ctd. 
            (ctd \<longrightarrow> wpa A (f \<sigma>) (\<lambda>\<sigma>' s\<^sub>2. POSTCOND asf (EXS t'. I \<sigma>' t' ** \<up>\<^sub>d((t',t)\<in>R) ** F) s\<^sub>2) s\<^sub>1)
          \<and> (\<not>ctd \<longrightarrow> Q \<sigma> s\<^sub>1)
        ) s\<^sub>1
      ) s)"
    shows "wpa A (llc_while_annot I R b f \<sigma>) Q s"
    using assms(1) apply -
    apply vcg_rl
    apply fact
    apply fact
    apply (drule STEP)
    apply (simp add: fri_extract_simps vcg_tag_defs bool.assn_def)   
    apply (simp add: ABSTRACT_def)
    apply (erule wpa_monoI)
    apply auto
    done
    
end
  
  
end
