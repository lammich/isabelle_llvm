section \<open>Basic Definitions\<close>
theory Sepref_Basic
imports 
  "../ds/LLVM_DS_NArray"
  "HOL-Eisbach.Eisbach"
  Refine_Monadic_Add
  "Lib/Sepref_Misc"
  "Lib/Structured_Apply"
  Sepref_Id_Op
begin
no_notation i_ANNOT (infixr ":::\<^sub>i" 10)
no_notation CONST_INTF (infixr "::\<^sub>i" 10)

no_notation pred_K ("\<langle>_\<rangle>")


type_synonym assn = ll_assn



text \<open>
  In this theory, we define the basic concept of refinement 
  from a nondeterministic program specified in the 
  Isabelle Refinement Framework to an imperative deterministic one 
  specified in Imperative/HOL.
\<close>

subsection {* Values on Heap *}
text \<open>We tag every refinement assertion with the tag @{text hn_ctxt}, to
  avoid higher-order unification problems when the refinement assertion 
  is schematic.\<close>
definition hn_ctxt :: "('a\<Rightarrow>'c\<Rightarrow>assn) \<Rightarrow> 'a \<Rightarrow> 'c \<Rightarrow> assn" 
  \<comment> \<open>Tag for refinement assertion\<close>
  where
  "hn_ctxt P a c \<equiv> P a c"

definition pure :: "('b \<times> 'a) set \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> assn"
  \<comment> \<open>Pure binding, not involving the heap\<close>
  where "pure R \<equiv> (\<lambda>a c. \<up>((c,a)\<in>R))"

lemma pure_app_eq: "pure R a c = \<up>((c,a)\<in>R)" by (auto simp: pure_def)

lemma pure_eq_conv[simp]: "pure R = pure R' \<longleftrightarrow> R=R'"
  unfolding pure_def 
  apply (rule iffI)
  apply safe
  apply (meson pure_assn_eq_conv)
  apply (meson pure_assn_eq_conv)
  done

lemma pure_rel_eq_false_iff: "pure R x y = sep_false \<longleftrightarrow> (y,x)\<notin>R"
  by (auto simp: pure_def sep_algebra_simps)
    
lemma pure_part_pure[simp]: "pure_part (pure R a c) \<longleftrightarrow> (c,a)\<in>R"  
  by (simp add: pure_app_eq)
  
definition is_pure :: "(_ \<Rightarrow> _ \<Rightarrow> assn) \<Rightarrow> bool" where "is_pure P \<equiv> \<exists>P'. \<forall>x x'. P x x'=\<up>(P' x x')"
lemma is_pureI[intro?]: 
  assumes "\<And>x x'. P x x' = \<up>(P' x x')"
  shows "is_pure P"
  using assms unfolding is_pure_def by blast

lemma is_pureE:
  assumes "is_pure P"
  obtains P' where "\<And>x x'. P x x' = \<up>(P' x x')"
  using assms unfolding is_pure_def by blast

lemma pure_pure[simp]: "is_pure (pure P)"
  unfolding pure_def by rule blast
lemma pure_hn_ctxt[intro!]: "is_pure P \<Longrightarrow> is_pure (hn_ctxt P)"
  unfolding hn_ctxt_def[abs_def] .


definition the_pure :: "('b \<Rightarrow> 'a \<Rightarrow> assn) \<Rightarrow> ('a \<times> 'b) set" 
  where "the_pure P \<equiv> THE P'. \<forall>x x'. P x x'=\<up>((x',x)\<in>P')"

lemma the_pure_pure[simp]: "the_pure (pure R) = R"
  unfolding pure_def the_pure_def
  by (rule theI2[where a=R]) auto

lemma is_pure_alt_def: "is_pure R \<longleftrightarrow> (\<exists>Ri. \<forall>x y. R x y = \<up>((y,x)\<in>Ri))"
  unfolding is_pure_def
  apply auto
  apply (rename_tac P')
  apply (rule_tac x="{(x,y). P' y x}" in exI)
  apply auto
  done

lemma pure_the_pure[simp]: "is_pure R \<Longrightarrow> pure (the_pure R) = R"
  unfolding is_pure_alt_def pure_def the_pure_def
  apply (intro ext)
  apply clarsimp
  apply (rename_tac a c Ri)
  apply (rule_tac a=Ri in theI2)
  apply auto
  done
  
lemma is_pure_conv: "is_pure R \<longleftrightarrow> (\<exists>R'. R = pure R')"
  unfolding pure_def is_pure_alt_def by force

lemma is_pure_the_pure_id_eq[simp]: "is_pure R \<Longrightarrow> the_pure R = Id \<longleftrightarrow> R=pure Id"  
  by (auto simp: is_pure_conv)

lemma is_pure_iff_pure_assn: "is_pure P = (\<forall>x x'. sep_is_pure_assn (P x x'))"
  unfolding is_pure_def 
  apply (rule iffI)
  apply auto []
  apply (rule exI[where x="\<lambda>a c. pure_part (P a c)"])
  apply auto
  done


abbreviation "hn_val R \<equiv> hn_ctxt (pure R)"

lemma hn_val_unfold: "hn_val R a b = \<up>((b,a)\<in>R)"
  by (simp add: hn_ctxt_def pure_def)


definition "invalid_assn R x y \<equiv> \<up>(pure_part (R x y))"

abbreviation "hn_invalid R \<equiv> hn_ctxt (invalid_assn R)"

lemma invalidate_clone: "R x y = (invalid_assn R x y ** R x y)"
  unfolding invalid_assn_def
  by (metis (mono_tags, lifting) pure_partI pure_part_pure_eq pure_part_split_conj pure_true_conv sep.add.right_neutral sep_conj_commute sep_is_pure_assn_def)

lemma invalidate_clone': "hn_ctxt R x y = (hn_invalid R x y ** hn_ctxt R x y)"
  unfolding hn_ctxt_def using invalidate_clone .

lemma invalid_pure_recover: "invalid_assn (pure R) x y = pure R x y"
  unfolding invalid_assn_def pure_def by auto

lemma hn_invalidI: "hn_ctxt P x y s \<Longrightarrow> hn_invalid P x y = \<box>"
  by (auto simp: invalid_assn_def hn_ctxt_def pure_partI pure_true_conv)

lemma invalid_assn_cong[cong]:
  assumes "x\<equiv>x'"
  assumes "y\<equiv>y'"
  assumes "R x' y' \<equiv> R' x' y'"
  shows "invalid_assn R x y = invalid_assn R' x' y'"
  using assms unfolding invalid_assn_def
  by simp

subsection \<open>Constraints in Refinement Relations\<close>

definition rdomp :: "('a \<Rightarrow> 'c \<Rightarrow> assn) \<Rightarrow> 'a \<Rightarrow> bool" where
  "rdomp R a \<equiv> \<exists>h c. R a c h"

(*abbreviation "rdom R \<equiv> Collect (rdomp R)"*)

lemma rdomp_ctxt[simp]: "rdomp (hn_ctxt R) = rdomp R"
  by (simp add: hn_ctxt_def[abs_def])  

lemma rdomp_pure[simp]: "rdomp (pure R) a \<longleftrightarrow> a\<in>Range R"
  unfolding rdomp_def pure_def by (auto simp: pred_lift_extract_simps)

(*lemma rdom_pure[simp]: "rdom (pure R) = Range R"
  unfolding rdomp_def[abs_def] pure_def by (auto simp: pred_lift_extract_simps)
*)  

lemma rdomp_invalid_simp[simp]: "rdomp (invalid_assn P) x = rdomp P x"
  by (auto simp: invalid_assn_def rdomp_def pure_part_def pred_lift_extract_simps)

lemma Range_of_constraint_conv[simp]: "Range (A\<inter>UNIV\<times>C) = Range A \<inter> C"
  by auto


subsection \<open>Heap-Nres Refinement Calculus\<close>

text \<open>Predicate that expresses refinement. Given a heap
  @{text "\<Gamma>"}, program @{text "c"} produces a heap @{text "\<Gamma>'"} and
  a concrete result that is related with predicate @{text "R"} to some
  abstract result from @{text "m"}\<close>
  
definition "hn_refine \<Gamma> c \<Gamma>' R CP m \<equiv> nofail m \<longrightarrow>
  llvm_htriple \<Gamma> c (\<lambda>r. \<Gamma>' ** \<up>(CP r) ** (EXS x. R x r ** \<up>(RETURN x \<le> m)))"

lemma hn_refineI[intro?]:
  assumes "nofail m 
    \<Longrightarrow> llvm_htriple \<Gamma> c (\<lambda>r. \<Gamma>' ** \<up>(CP r) ** (EXS x. R x r ** \<up>(RETURN x \<le> m)))"
  shows "hn_refine \<Gamma> c \<Gamma>' R CP m"
  using assms unfolding hn_refine_def by blast

lemma hn_refineD:
  assumes "hn_refine \<Gamma> c \<Gamma>' R CP m"
  assumes "nofail m"
  shows "llvm_htriple \<Gamma> c (\<lambda>r. \<Gamma>' ** \<up>(CP r) ** (EXS x. R x r ** \<up>(RETURN x \<le> m)))"
  using assms unfolding hn_refine_def by blast

lemma hn_refine_preI: 
  assumes "\<And>h. \<Gamma> h \<Longrightarrow> hn_refine \<Gamma> c \<Gamma>' R CP a"
  shows "hn_refine \<Gamma> c \<Gamma>' R CP a"
  using assms unfolding hn_refine_def
  apply auto
  by (meson htriple_pure_preI pure_part_def)

lemma hn_refine_nofailI: 
  assumes "nofail a \<Longrightarrow> hn_refine \<Gamma> c \<Gamma>' R CP a"  
  shows "hn_refine \<Gamma> c \<Gamma>' R CP a"
  using assms by (auto simp: hn_refine_def)

lemma hn_refine_false[simp]: "hn_refine sep_false c \<Gamma>' R CP m"
  by rule auto

lemma hnr_FAIL[simp, intro!]: "hn_refine \<Gamma> c \<Gamma>' R CP FAIL"
  by rule auto

lemma hn_refine_frame:
  assumes "hn_refine P' c Q' R CP m"
  assumes "P \<turnstile> P' ** F"
  shows "hn_refine P c (Q' ** F) R CP m"
  using assms
  unfolding hn_refine_def entails_def
  apply clarsimp
  apply (rule cons_rule[where P="P'**F", rotated])
  apply simp
  apply simp
  apply (rule cons_post_rule)
  apply (erule frame_rule)
  apply (auto simp: sep_algebra_simps pred_lift_extract_simps)
  by (metis sep.mult_commute)

lemma hn_refine_frame': "hn_refine \<Gamma> c \<Gamma>' R CP m \<Longrightarrow> hn_refine (\<Gamma>**F) c (\<Gamma>'**F) R CP m"  
  by (simp add: hn_refine_frame)
  
lemma hn_refine_cons:
  assumes I: "P\<turnstile>P'"
  assumes R: "hn_refine P' c Q R CP m"
  assumes I': "Q\<turnstile>Q'"
  assumes R': "\<And>x y. R x y \<turnstile> R' x y"
  shows "hn_refine P c Q' R' CP m"
  using R unfolding hn_refine_def
  apply clarify
  apply (erule cons_rule)
  using I apply (simp add: entails_def)
  using I' R'
  by (smt entails_def sep_conj_impl)

lemma hn_refine_cons_cp:
  assumes I: "P \<turnstile> P'"
  assumes R: "hn_refine P' c Q R CP m"
  assumes I': "Q \<turnstile> Q'"
  assumes R': "\<And>x y. R x y \<turnstile> R' x y"
  assumes CP': "\<And>y. CP y \<Longrightarrow> CP' y"
  shows "hn_refine P c Q' R' CP' m"
  using R unfolding hn_refine_def
  apply clarify
  apply (erule cons_rule)
  subgoal using I by (simp add: entails_def)
  apply (simp add: sep_algebra_simps)
  by (metis CP' I' R' conj_entails_mono entails_def)
  
  
(*lemma hn_refine_cons:
  assumes I: "P\<Longrightarrow>\<^sub>AP'"
  assumes R: "hn_refine P' c Q R m"
  assumes I': "Q\<Longrightarrow>\<^sub>AQ'"
  assumes R': "\<And>x y. R x y \<Longrightarrow>\<^sub>A R' x y"
  shows "hn_refine P c Q' R' m"
  using R unfolding hn_refine_def
  apply clarsimp
  apply (rule cons_pre_rule[OF I])
  apply (erule cons_post_rule)
  apply (rule ent_star_mono ent_refl I' R' ent_ex_preI ent_ex_postI)+
  done
*)
lemma hn_refine_cons_pre:
  assumes I: "P \<turnstile> P'"
  assumes R: "hn_refine P' c Q R CP m"
  shows "hn_refine P c Q R CP m"
  apply (rule hn_refine_cons[OF I R])
  by auto

lemma hn_refine_cons_post:
  assumes R: "hn_refine P c Q R CP m"
  assumes I: "Q\<turnstile>Q'"
  shows "hn_refine P c Q' R CP m"
  using assms
  by (rule hn_refine_cons[OF entails_refl _ _ entails_refl])

lemma hn_refine_cons_cp_only:
  assumes R: "hn_refine P c Q R CP m"
  assumes I: "\<And>x. CP x \<Longrightarrow> CP' x"
  shows "hn_refine P c Q R CP' m"
  apply (rule hn_refine_cons_cp[OF _ R])
  using assms
  apply (auto)
  done
  
lemma hn_refine_cons_res: 
  "\<lbrakk> hn_refine \<Gamma> f \<Gamma>' R CP g; \<And>a c. R a c \<turnstile> R' a c \<rbrakk> \<Longrightarrow> hn_refine \<Gamma> f \<Gamma>' R' CP g"
  by (erule hn_refine_cons[OF entails_refl]) auto

lemma hn_refine_ref:
  assumes LE: "m\<le>m'"
  assumes R: "hn_refine P c Q R CP m"
  shows "hn_refine P c Q R CP m'"
  apply rule
  apply (rule cons_post_rule)
  apply (rule hn_refineD[OF R])
  using LE apply (simp add: pw_le_iff)
  by (smt LE order_trans pred_lift_extract_simps(2) sep_conj_commute sep_conj_impl)

lemma hn_refine_cons_complete:
  assumes I: "P\<turnstile>P'"
  assumes R: "hn_refine P' c Q R CP m"
  assumes I': "Q\<turnstile>Q'"
  assumes R': "\<And>x y. R x y \<turnstile> R' x y"
  assumes LE: "m\<le>m'"
  shows "hn_refine P c Q' R' CP m'"
  apply (rule hn_refine_ref[OF LE])
  apply (rule hn_refine_cons[OF I R I' R'])
  done
 
lemma hn_refine_augment_res:
  assumes A: "hn_refine \<Gamma> f \<Gamma>' R CP g"
  assumes B: "g \<le>\<^sub>n SPEC \<Phi>"
  shows "hn_refine \<Gamma> f \<Gamma>' (\<lambda>a c. R a c ** \<up>(\<Phi> a)) CP g"
  apply (rule hn_refineI)
  apply (rule cons_post_rule)
  apply (erule A[THEN hn_refineD])
  apply (erule sep_conj_impl, simp)
  apply (clarsimp simp: sep_algebra_simps) apply (rule exI)
  using B
  apply (auto simp: pred_lift_extract_simps pw_le_iff pw_leof_iff)
  done

subsection \<open>Product Types\<close>
text \<open>Some notion for product types is already defined here, as it is used 
  for currying and uncurrying, which is fundamental for the sepref tool\<close>
definition prod_assn :: "('a1\<Rightarrow>'c1\<Rightarrow>assn) \<Rightarrow> ('a2\<Rightarrow>'c2\<Rightarrow>assn) 
  \<Rightarrow> 'a1*'a2 \<Rightarrow> 'c1*'c2 \<Rightarrow> assn" where
  "prod_assn P1 P2 a c \<equiv> case (a,c) of ((a1,a2),(c1,c2)) \<Rightarrow>
  P1 a1 c1 ** P2 a2 c2"

notation prod_assn (infixr "\<times>\<^sub>a" 70)
  
lemma prod_assn_pure_conv[simp]: "prod_assn (pure R1) (pure R2) = pure (R1 \<times>\<^sub>r R2)"
  by (auto simp: pure_def prod_assn_def pred_lift_extract_simps fun_eq_iff)

lemma prod_assn_pair_conv[simp]: 
  "prod_assn A B (a1,b1) (a2,b2) = (A a1 a2 ** B b1 b2)"
  unfolding prod_assn_def by auto

lemma prod_assn_true[simp]: "prod_assn (\<lambda>_ _. sep_true) (\<lambda>_ _. sep_true) = (\<lambda>_ _. sep_true)"
  by (auto simp: hn_ctxt_def prod_assn_def fun_eq_iff)

subsection "Convenience Lemmas"

lemma hn_refine_guessI:
  assumes "hn_refine P f P' R CP f'"
  assumes "f=f_conc"
  shows "hn_refine P f_conc P' R CP f'"
  \<comment> \<open>To prove a refinement, first synthesize one, and then prove equality\<close>
  using assms by simp


lemma imp_correctI:
  assumes R: "hn_refine \<Gamma> c \<Gamma>' R CP a"
  assumes C: "a \<le> SPEC \<Phi>"
  shows "llvm_htriple \<Gamma> c (\<lambda>r'. EXS r. \<Gamma>' ** \<up>(CP r') ** R r r' ** \<up>(\<Phi> r))"
  apply (rule cons_post_rule)
  apply (rule hn_refineD[OF R])
  apply (rule le_RES_nofailI[OF C])
  apply (force simp: sep_algebra_simps dest: order_trans[OF _ C])
  done

lemma hnr_pre_ex_conv: 
  shows "hn_refine (EXS x. \<Gamma> x) c \<Gamma>' R CP a \<longleftrightarrow> (\<forall>x. hn_refine (\<Gamma> x) c \<Gamma>' R CP a)"
  unfolding hn_refine_def
  apply (safe; clarsimp?)
  subgoal by (metis (mono_tags, lifting) cons_rule)
  subgoal premises prems
    supply [vcg_rules] = prems(1)[THEN spec]
    by vcg
  done

lemma hnr_pre_pure_conv:  
  shows "hn_refine (\<up>P ** \<Gamma>) c \<Gamma>' R CP a \<longleftrightarrow> (P \<longrightarrow> hn_refine \<Gamma> c \<Gamma>' R CP a)"
  unfolding hn_refine_def
  apply (cases P)
  apply (auto simp: sep_algebra_simps)
  done

lemma hn_refine_split_post:
  assumes "hn_refine \<Gamma> c \<Gamma>' R CP a"
  shows "hn_refine \<Gamma> c (\<Gamma>' or \<Gamma>'') R CP a"
  apply (rule hn_refine_cons_post[OF assms])
  apply (auto simp: entails_def)
  done

lemma hn_refine_post_other: 
  assumes "hn_refine \<Gamma> c \<Gamma>'' R CP a"
  shows "hn_refine \<Gamma> c (\<Gamma>' or \<Gamma>'') R CP a"
  apply (rule hn_refine_cons_post[OF assms])
  apply (auto simp: entails_def)
  done


subsubsection \<open>Return\<close>

lemma hnr_RETURN_pass:
  "hn_refine (hn_ctxt R x p) (Mreturn p) (hn_invalid R x p) R (\<lambda>r. r=p) (RETURN x)"
  \<comment> \<open>Pass on a value from the heap as Mreturn value\<close>
  apply (subst invalidate_clone')
  apply rule unfolding hn_ctxt_def
  apply vcg
  done

lemma hnr_RETURN_pure:
  assumes "(c,a)\<in>R"
  shows "hn_refine emp (Mreturn c) emp (pure R) (\<lambda>r. r=c) (RETURN a)"
  \<comment> \<open>Return pure value\<close>
  unfolding hn_refine_def using assms
  supply [simp] = pure_def
  by vcg
  
subsubsection \<open>Assertion\<close>

lemma hnr_ASSERT:
  assumes "\<Phi> \<Longrightarrow> hn_refine \<Gamma> c \<Gamma>' R CP c'"
  shows "hn_refine \<Gamma> c \<Gamma>' R CP (do { ASSERT \<Phi>; c'})"
  using assms
  apply (cases \<Phi>)
  by auto

subsubsection \<open>Bind\<close>
lemma bind_det_aux: "\<lbrakk> RETURN x \<le> m; RETURN y \<le> f x \<rbrakk> \<Longrightarrow> RETURN y \<le> m \<bind> f"
  apply (rule order_trans[rotated])
  apply (rule Refine_Basic.bind_mono)
  apply assumption
  apply (rule order_refl)
  apply simp
  done

  
definition "MK_FREE R f \<equiv> \<forall>a c. llvm_htriple (R a c) (f c) (\<lambda>_::unit. \<box>)"  

lemma MK_FREEI[intro?]: "\<lbrakk>\<And>a c. llvm_htriple (R a c) (f c) (\<lambda>_. \<box>)\<rbrakk> \<Longrightarrow> MK_FREE R f"
  by (auto simp: MK_FREE_def)

lemma MK_FREED: "MK_FREE R f \<Longrightarrow> llvm_htriple (R a c) (f c) (\<lambda>_. \<box>)"
  by (auto simp: MK_FREE_def)
  
lemma mk_free_pure: "MK_FREE (pure R) (\<lambda>_. Mreturn ())"
  apply rule unfolding pure_def
  by vcg

(*
  TODO: Should be synthesized once relations are known
*)
lemma mk_free_is_pure: "is_pure A \<Longrightarrow> MK_FREE A (\<lambda>_. Mreturn ())"
  apply rule unfolding pure_def is_pure_def
  by vcg

  
  
lemma mk_free_invalid: "MK_FREE (invalid_assn R) (\<lambda>_. Mreturn ())"
  apply rule unfolding invalid_assn_def
  by vcg

lemma mk_free_pair: 
  assumes "MK_FREE R\<^sub>1 f\<^sub>1" 
  assumes "MK_FREE R\<^sub>2 f\<^sub>2"  
  shows "MK_FREE (R\<^sub>1\<times>\<^sub>aR\<^sub>2) (\<lambda>(c\<^sub>1,c\<^sub>2). doM {f\<^sub>1 c\<^sub>1; f\<^sub>2 c\<^sub>2})"
  supply [vcg_rules] = assms[THEN MK_FREED]
  apply (rule)
  by vcg
  
  

  
lemma hnr_bind:
  assumes D1: "hn_refine \<Gamma> m' \<Gamma>1 Rh CP\<^sub>1 m"
  assumes D2: 
    "\<And>x x'. RETURN x \<le> m \<Longrightarrow> CP\<^sub>1 x' \<Longrightarrow> hn_refine (hn_ctxt Rh x x' ** \<Gamma>1) (f' x') (\<Gamma>2 x x') R (CP\<^sub>2 x') (f x)"
  assumes IMP: "\<And>x x'. \<Gamma>2 x x' \<turnstile> hn_ctxt Rx x x' ** \<Gamma>'"
  assumes MKF: "MK_FREE Rx fr"
  shows "hn_refine \<Gamma> (doM {x\<leftarrow>m'; r \<leftarrow> f' x; fr x; Mreturn r}) \<Gamma>' R (\<lambda>r. \<exists>x'. CP\<^sub>1 x' \<and> CP\<^sub>2 x' r) (m\<bind>f)"
  apply rule
  supply [vcg_rules] = D1[THEN hn_refineD]
  supply [simp] = pw_bind_nofail
  apply vcg
proof goal_cases
  case C: (1 asf r s x)
  hence "nofail (f x)" by (simp add: refine_pw_simps pw_le_iff)
  
  note [vcg_rules] = D2[unfolded hn_ctxt_def, OF \<open>RETURN x \<le> m\<close>, THEN hn_refineD, OF _ \<open>nofail (f x)\<close>, of r]
  
  note [vcg_rules] = MKF[THEN MK_FREED]
  
  
  have [fri_red_rules]: "is_sep_red (\<Gamma>') \<box> (\<Gamma>2 x x') (Rx x x')" for x x'
    using IMP
    apply (auto simp: is_sep_red_def hn_ctxt_def)
  proof -
    fix Ps :: "llvm_amemory \<Rightarrow> bool" and Qs :: "llvm_amemory \<Rightarrow> bool"
    assume "\<Gamma>' \<and>* Ps \<turnstile> Qs"
    then have f1: "Ps \<and>* \<Gamma>' \<turnstile> Qs"
      by (simp add: sep.mult_commute)
    have "\<Gamma>2 x x' \<turnstile> \<Gamma>' \<and>* Rx x x'"
      by (metis (no_types) IMP hn_ctxt_def sep.mult_commute)
    then have "Ps \<and>* \<Gamma>2 x x' \<turnstile> Qs \<and>* Rx x x'"
      using f1 by (simp add: conj_entails_mono entails_mp)
    then show "\<Gamma>2 x x' \<and>* Ps \<turnstile> Rx x x' \<and>* Qs"
      by (simp add: sep.mult_commute)
  qed
  
  note [simp] = refine_pw_simps pw_le_iff
  show ?case using C by vcg
qed  

text \<open>Version for manual synthesis, if freeing of bound variable has been inserted manually\<close>
lemma hnr_bind_manual_free:
  assumes D1: "hn_refine \<Gamma> m' \<Gamma>1 Rh CP\<^sub>1 m"
  assumes D2: 
    "\<And>x x'. RETURN x \<le> m \<Longrightarrow> CP\<^sub>1 x' \<Longrightarrow> hn_refine (hn_ctxt Rh x x' ** \<Gamma>1) (f' x') (\<Gamma>') R (CP\<^sub>2 x') (f x)"
  shows "hn_refine \<Gamma> (Mbind m' f') \<Gamma>' R (\<lambda>r. \<exists>x'. CP\<^sub>1 x' \<and> CP\<^sub>2 x' r) (m\<bind>f)"
  apply rule
  supply [vcg_rules] = D1[THEN hn_refineD]
  supply [simp] = pw_bind_nofail
  apply vcg
proof goal_cases
  case C: (1 asf r s x)
  hence "nofail (f x)" by (simp add: refine_pw_simps pw_le_iff)
  
  note [vcg_rules] = D2[unfolded hn_ctxt_def, OF \<open>RETURN x \<le> m\<close>, THEN hn_refineD, OF _ \<open>nofail (f x)\<close>, of r]
  
  note [simp] = refine_pw_simps pw_le_iff
  show ?case using C by vcg
qed  





subsubsection \<open>Recursion\<close>

definition "hn_rel P m \<equiv> \<lambda>r. EXS x. \<up>(RETURN x \<le> m) ** P x r"

lemma hn_refine_alt: "hn_refine Fpre c Fpost P CP m \<equiv> nofail m \<longrightarrow>
  llvm_htriple Fpre c (\<lambda>r. hn_rel P m r ** \<up>(CP r) ** Fpost)"
  apply (rule eq_reflection)
  unfolding hn_refine_def hn_rel_def
  by (auto simp: sep_conj_commute)


lemma hnr_RECT_cp:
  assumes S: "\<And>cf af ax px. \<lbrakk>C px;
    \<And>ax px. C px \<Longrightarrow> hn_refine (hn_ctxt Rx ax px ** F) (cf px) (F' ax px) Ry (CP px) (af ax)\<rbrakk> 
    \<Longrightarrow> hn_refine (hn_ctxt Rx ax px ** F) (cB cf px) (F' ax px) Ry (CP px) (aB af ax)"
  assumes M: "M_mono_body cB"
  assumes C: "C px"
  shows "hn_refine 
    (hn_ctxt Rx ax px ** F) (MMonad.REC cB px) (F' ax px) Ry (CP px) (RECT aB ax)"
  unfolding RECT_def 
proof (simp add: , intro conjI impI)
  assume "trimono aB"
  hence "flatf_mono_ge aB" by (simp add: trimonoD)
  have "\<forall>ax px. C px \<longrightarrow>
    hn_refine (hn_ctxt Rx ax px ** F) (MMonad.REC cB px) (F' ax px) Ry (CP px)
      (flatf_gfp aB ax)"
      
    apply (rule flatf_ord.fixp_induct[OF _ \<open>flatf_mono_ge aB\<close>])  

    apply (rule flatf_admissible_pointwise)
    apply simp

    apply (auto simp: hn_refine_alt) []

    apply clarsimp
    
    apply (subst MMonad.REC_unfold[of cB, OF M])
    apply (rule S)
    apply blast
    apply blast
    done
  thus "hn_refine (hn_ctxt Rx ax px ** F) (MMonad.REC cB px) (F' ax px) Ry (CP px) (flatf_gfp aB ax)" 
    using C
    by simp
qed
  
  
  
  
    

lemma hnr_RECT:
  assumes S: "\<And>cf af ax px. \<lbrakk>
    \<And>ax px. hn_refine (hn_ctxt Rx ax px ** F) (cf px) (F' ax px) Ry (CP px) (af ax)\<rbrakk> 
    \<Longrightarrow> hn_refine (hn_ctxt Rx ax px ** F) (cB cf px) (F' ax px) Ry (CP px) (aB af ax)"
  assumes M: "M_mono_body cB"
  shows "hn_refine 
    (hn_ctxt Rx ax px ** F) (MMonad.REC cB px) (F' ax px) Ry (CP px) (RECT aB ax)"
  unfolding RECT_def 
proof (simp, intro conjI impI)
  assume "trimono aB"
  hence "flatf_mono_ge aB" by (simp add: trimonoD)
  have "\<forall>ax px. 
    hn_refine (hn_ctxt Rx ax px ** F) (MMonad.REC cB px) (F' ax px) Ry (CP px) 
      (flatf_gfp aB ax)"
      
    apply (rule flatf_ord.fixp_induct[OF _ \<open>flatf_mono_ge aB\<close>])  

    apply (rule flatf_admissible_pointwise)
    apply simp

    apply (auto simp: hn_refine_alt) []

    apply clarsimp
    apply (subst MMonad.REC_unfold[of cB, OF M])
    apply (rule S)
    apply blast
    done
  thus "hn_refine (hn_ctxt Rx ax px ** F) (MMonad.REC cB px) (F' ax px) Ry (CP px) (flatf_gfp aB ax)" 
    by simp
qed

subsubsection \<open>Merging\<close>

definition "MERGE \<Gamma>1 f1 \<Gamma>2 f2 \<Gamma>' \<equiv> llvm_htriple \<Gamma>1 f1 (\<lambda>_. \<Gamma>') \<and> llvm_htriple \<Gamma>2 f2 (\<lambda>_. \<Gamma>')"

lemma MERGED: 
  assumes "MERGE \<Gamma>1 f1 \<Gamma>2 f2 \<Gamma>'"
  shows "llvm_htriple \<Gamma>1 f1 (\<lambda>_. \<Gamma>')" "llvm_htriple \<Gamma>2 f2 (\<lambda>_. \<Gamma>')"
  using assms by (auto simp: MERGE_def)

lemma MERGEI[intro?]: 
  assumes "llvm_htriple \<Gamma>1 f1 (\<lambda>_. \<Gamma>')" "llvm_htriple \<Gamma>2 f2 (\<lambda>_. \<Gamma>')"
  shows "MERGE \<Gamma>1 f1 \<Gamma>2 f2 \<Gamma>'"
  using assms by (auto simp: MERGE_def)

definition "MERGE1 R1 f1 R2 f2 R' \<equiv> \<forall> a c. MERGE (R1 a c) (f1 c) (R2 a c) (f2 c) (R' a c)"

lemma MERGE1I[intro?]: 
  assumes "\<And>a c. llvm_htriple (R1 a c) (f1 c) (\<lambda>_. R' a c)" 
      and "\<And>a c. llvm_htriple (R2 a c) (f2 c) (\<lambda>_. R' a c)"
  shows "MERGE1 R1 f1 R2 f2 R'"
  using assms by (auto simp: MERGE1_def MERGE_def)

lemma MERGE1D: 
  assumes "MERGE1 R1 f1 R2 f2 R'"
  shows "\<And>a c. llvm_htriple (R1 a c) (f1 c) (\<lambda>_. R' a c)" 
    and "\<And>a c. llvm_htriple (R2 a c) (f2 c) (\<lambda>_. R' a c)"
  using assms by (auto simp: MERGE1_def MERGE_def)
  
lemma MERGE_STAR:
  assumes "MERGE1 R1 f1 R2 f2 R'" "MERGE \<Gamma>1 fs1 \<Gamma>2 fs2 \<Gamma>'" 
  shows "MERGE (hn_ctxt R1 a c ** \<Gamma>1) (doM {f1 c;fs1}) (hn_ctxt R2 a c ** \<Gamma>2) (doM {f2 c;fs2}) (hn_ctxt R' a c ** \<Gamma>')"
proof -
  note [vcg_rules] = MERGE1D[OF assms(1)] MERGED[OF assms(2)]

  show ?thesis unfolding hn_ctxt_def by rule vcg
qed  

lemma MERGE_triv: "MERGE \<Gamma> (Mreturn ()) \<Gamma> (Mreturn ()) \<Gamma>"
  apply (rule) unfolding FRI_END_def by vcg

lemma MERGE_END: "MERGE FRI_END (Mreturn ()) FRI_END (Mreturn ()) \<box>"
  apply (rule) unfolding FRI_END_def by vcg

lemma MERGE1_eq: "MERGE1 P (\<lambda>_. Mreturn ()) P (\<lambda>_. Mreturn ()) P"  
  by rule vcg
  
lemma MERGE1_invalids: 
  assumes "MK_FREE R f"  
  shows "MERGE1 (invalid_assn R) (\<lambda>_. Mreturn ()) R f (invalid_assn R)" (is ?left)
    and "MERGE1 R f (invalid_assn R) (\<lambda>_. Mreturn ()) (invalid_assn R)" (is ?right)
proof -
  note [vcg_rules] = MK_FREED[OF assms]

  show ?left
    apply rule
    apply vcg []
    apply (subst invalidate_clone[of R])
    unfolding invalid_assn_def
    by vcg
    
  show ?right
    apply rule
    apply (subst invalidate_clone[of R])
    unfolding invalid_assn_def
    by vcg
    
qed  
  

subsection \<open>ML-Level Utilities\<close>
ML \<open>
  signature SEPREF_BASIC = sig
    (* Destroy lambda term, Mreturn function to reconstruct. Bound var is replaced by free. *)
    val dest_lambda_rc: Proof.context -> term -> ((term * (term -> term)) * Proof.context)
    (* Apply function under lambda. Bound var is replaced by free. *)
    val apply_under_lambda: (Proof.context -> term -> term) -> Proof.context -> term -> term

    (* 'a nres type *)
    val is_nresT: typ -> bool
    val mk_nresT: typ -> typ
    val dest_nresT: typ -> typ

    (* Make certified == *)
    val mk_cequals: cterm * cterm -> cterm
    (* Make \<Longrightarrow>\<^sub>A *)
    val mk_entails: term * term -> term


    (* Operations on pre-terms *)
    val constrain_type_pre: typ -> term -> term (* t::T *)

    val mk_pair_in_pre: term -> term -> term -> term (* (c,a) \<in> R *)

    val mk_compN_pre: int -> term -> term -> term  (* f o...o g*)

    val mk_curry0_pre: term -> term                (* curry0 f *) 
    val mk_curry_pre: term -> term                 (* curry f *) 
    val mk_curryN_pre: int -> term -> term         (* curry (...(curry f)...) *) 

    val mk_uncurry0_pre: term -> term              (* uncurry0 f *)       
    val mk_uncurry_pre: term -> term               (* uncurry f *)
    val mk_uncurryN_pre: int -> term -> term       (* uncurry (...(uncurry f)...) *)



    (* Conversion for hn_refine - term*)
    val hn_refine_conv: conv -> conv -> conv -> conv -> conv -> conv -> conv

    (* Conversion on abstract value (last argument) of hn_refine - term *)
    val hn_refine_conv_a: conv -> conv

    (* Conversion on abstract value of hn_refine term in conclusion of theorem *)
    val hn_refine_concl_conv_a: (Proof.context -> conv) -> Proof.context -> conv

    (* Destruct hn_refine term *)
    val dest_hn_refine: term -> term * term * term * term * term * term 
    (* Make hn_refine term *)
    val mk_hn_refine: term * term * term * term * term * term -> term
    (* Check if given term is Trueprop (hn_refine ...). Use with CONCL_COND'. *)
    val is_hn_refine_concl: term -> bool

    (* Destruct abs-fun, returns RETURN-flag, (f, args) *)
    val dest_hnr_absfun: term -> bool * (term * term list)
    (* Make abs-fun. *)
    val mk_hnr_absfun: bool * (term * term list) -> term
    (* Make abs-fun. Guess RETURN-flag from type. *)
    val mk_hnr_absfun': (term * term list) -> term
    
    (* Prove permutation of *. To be used with f_tac_conv. *)
    val star_permute_tac: Proof.context -> tactic

    (* Make separation conjunction *)
    val mk_star: term * term -> term
    (* Make separation conjunction from list. "[]" yields "\<box>". *)
    val list_star: term list -> term
    (* Decompose separation conjunction. "\<box>" yields "[]". *)
    val strip_star: term -> term list

    (* Check if true-assertion *)
    val is_true: term -> bool

    (* Check if term is hn_ctxt-assertion *)
    val is_hn_ctxt: term -> bool 
    (* Decompose hn_ctxt-assertion *)
    val dest_hn_ctxt: term -> term * term * term
    (* Decompose hn_ctxt-assertion, NONE if term has wrong format *)
    val dest_hn_ctxt_opt: term -> (term * term * term) option
      

    type phases_ctrl = {
      trace: bool,            (* Trace phases *)
      trace_goals: bool,      (* Trace intermediate goal states *)
      int_res: bool,          (* Stop with intermediate result *)
      start: string option,   (* Start with this phase. NONE: First phase *)
      stop: string option     (* Stop after this phase. NONE: Last phase *)
    }

    (* No tracing or intermediate result, all phases *)
    val dflt_phases_ctrl: phases_ctrl 
    (* Tracing, intermediate result, all phases *)
    val dbg_phases_ctrl: phases_ctrl
    (* Tracing, goal-tracing, intermediate result, all phases *)
    val full_dbg_phases_ctrl: phases_ctrl
    
    val cfg_trace_phase_goals: bool Config.T
    val flag_phases_ctrl: Proof.context -> bool -> phases_ctrl

    (* Name, tactic, expected number of created goals (may be negative for solved goals) *)
    type phase = string * (Proof.context -> tactic') * int

    (* Perform sequence of tactics (tac,n), each expected to create n new goals, 
       or solve goals if n is negative. 
       Debug-flag: Stop with intermediate state after tactic 
       fails or produces less/more goals as expected. *)   
    val PHASES': phase list -> phases_ctrl -> Proof.context -> tactic'

  end

  structure Sepref_Basic: SEPREF_BASIC = struct

    fun is_nresT (Type (@{type_name nres},[_])) = true | is_nresT _ = false
    fun mk_nresT T = Type(@{type_name nres},[T])
    fun dest_nresT (Type (@{type_name nres},[T])) = T | dest_nresT T = raise TYPE("dest_nresT",[T],[])


    fun dest_lambda_rc ctxt (Abs (x,T,t)) = let
        val (u,ctxt) = yield_singleton Variable.variant_fixes x ctxt
        val u = Free (u,T)
        val t = subst_bound (u,t)
        val reconstruct = Term.lambda_name (x,u)
      in
        ((t,reconstruct),ctxt)
      end
    | dest_lambda_rc _ t = raise TERM("dest_lambda_rc",[t])

    fun apply_under_lambda f ctxt t = let
      val ((t,rc),ctxt) = dest_lambda_rc ctxt t
      val t = f ctxt t
    in
      rc t
    end


    (* Functions on pre-terms *)
    fun mk_pair_in_pre x y r = Const (@{const_name Set.member}, dummyT) $
      (Const (@{const_name Product_Type.Pair}, dummyT) $ x $ y) $ r


    fun mk_uncurry_pre t = Const(@{const_name uncurry}, dummyT)$t
    fun mk_uncurry0_pre t = Const(@{const_name uncurry0}, dummyT)$t
    fun mk_uncurryN_pre 0 = mk_uncurry0_pre
      | mk_uncurryN_pre 1 = I
      | mk_uncurryN_pre n = mk_uncurry_pre o mk_uncurryN_pre (n-1)

    fun mk_curry_pre t = Const(@{const_name curry}, dummyT)$t
    fun mk_curry0_pre t = Const(@{const_name curry0}, dummyT)$t
    fun mk_curryN_pre 0 = mk_curry0_pre
      | mk_curryN_pre 1 = I
      | mk_curryN_pre n = mk_curry_pre o mk_curryN_pre (n-1)


    fun mk_compN_pre 0 f g = f $ g
      | mk_compN_pre n f g = let
          val g = fold (fn i => fn t => t$Bound i) (n-2 downto 0) g
          val t = Const(@{const_name "Fun.comp"},dummyT) $ f $ g

          val t = fold (fn i => fn t => Abs ("x"^string_of_int i,dummyT,t)) (n-1 downto 1) t
        in
          t
        end

    fun constrain_type_pre T t = Const(@{syntax_const "_type_constraint_"},T-->T) $ t




    local open Conv in
      fun hn_refine_conv c1 c2 c3 c4 c5 c6 ct = case Thm.term_of ct of
        @{mpat "hn_refine _ _ _ _ _ _"} => let
          val cc = combination_conv
        in
          cc (cc (cc (cc (cc (cc all_conv c1) c2) c3) c4) c5) c6 ct
        end
      | _ => raise CTERM ("hn_refine_conv",[ct])
  
      val hn_refine_conv_a = hn_refine_conv all_conv all_conv all_conv all_conv all_conv
  
      fun hn_refine_concl_conv_a conv ctxt = Refine_Util.HOL_concl_conv 
        (fn ctxt => hn_refine_conv_a (conv ctxt)) ctxt
  
    end

    (* FIXME: Strange dependency! *)
    val mk_cequals = uncurry SMT_Util.mk_cequals
  
    val mk_entails = HOLogic.mk_binrel @{const_name "entails"}
  
    val mk_star = HOLogic.mk_binop @{const_name "sep_conj"}

    fun list_star [] = @{term "\<box>::assn"}
      | list_star [a] = a
      | list_star (a::l) = mk_star (a,list_star l)

    fun strip_star @{mpat "?a**?b"} = strip_star a @ strip_star b
      | strip_star @{mpat "\<box>"} = []
      | strip_star t = [t]

    fun is_true @{mpat "sep_true"} = true | is_true _ = false
  
    fun is_hn_ctxt @{mpat "hn_ctxt _ _ _"} = true | is_hn_ctxt _ = false
    fun dest_hn_ctxt @{mpat "hn_ctxt ?R ?a ?p"} = (R,a,p) 
      | dest_hn_ctxt t = raise TERM("dest_hn_ctxt",[t])
  
    fun dest_hn_ctxt_opt @{mpat "hn_ctxt ?R ?a ?p"} = SOME (R,a,p) 
      | dest_hn_ctxt_opt _ = NONE
  
    fun strip_abs_args (t as @{mpat "PR_CONST _"}) = (t,[])
      | strip_abs_args @{mpat "?f$?a"} = (case strip_abs_args f of (f,args) => (f,args@[a]))
      | strip_abs_args t = (t,[])
  
    fun dest_hnr_absfun @{mpat "RETURN$?a"} = (true, strip_abs_args a)
      | dest_hnr_absfun f = (false, strip_abs_args f)
  
    fun mk_hnr_absfun (true,fa) = Autoref_Tagging.list_APP fa |> (fn a => @{mk_term "RETURN$?a"})
      | mk_hnr_absfun (false,fa) = Autoref_Tagging.list_APP fa
  
    fun mk_hnr_absfun' fa = let
      val t = Autoref_Tagging.list_APP fa
      val T = fastype_of t
    in
      case T of
        Type (@{type_name nres},_) => t
      | _ => @{mk_term "RETURN$?t"}
  
    end  
  
    fun dest_hn_refine @{mpat "hn_refine ?P ?c ?Q ?R ?CP ?a"} = (P,c,Q,R,CP,a)
      | dest_hn_refine t = raise TERM("dest_hn_refine",[t])
  
    fun mk_hn_refine (P,c,Q,R,CP,a) = @{mk_term "hn_refine ?P ?c ?Q ?R ?CP ?a"}
  
    val is_hn_refine_concl = can (HOLogic.dest_Trueprop #> dest_hn_refine)
  
    fun star_permute_tac ctxt = ALLGOALS (
      VCG_Lib.simp_only_tac @{thms sep_conj_empty sep_conj_empty' sep_conj_ac} ctxt)
      

    type phases_ctrl = {
      trace: bool,            
      trace_goals: bool,
      int_res: bool,          
      start: string option,   
      stop: string option     
    }

    val dflt_phases_ctrl = {trace=false,trace_goals=false,int_res=false,start=NONE,stop=NONE} 
    val dbg_phases_ctrl = {trace=true,trace_goals=false,int_res=true,start=NONE,stop=NONE}
    val full_dbg_phases_ctrl = {trace=true,trace_goals=true,int_res=true,start=NONE,stop=NONE}
    
    val cfg_trace_phase_goals = Attrib.setup_config_bool @{binding sepref_trace_phase_goals} (K false)
    
    fun flag_phases_ctrl ctxt dbg =
      case (Config.get ctxt cfg_trace_phase_goals, dbg) of
        (_, false) => dflt_phases_ctrl
      | (false, true) => dbg_phases_ctrl
      | (true,true) => full_dbg_phases_ctrl

    type phase = string * (Proof.context -> tactic') * int

    local
      fun ph_range phases start stop = let
        fun find_phase name = let
          val i = find_index (fn (n,_,_) => n=name) phases
          val _ = if i<0 then error ("No such phase: " ^ name) else ()
        in
          i
        end

        val i = case start of NONE => 0 | SOME n => find_phase n
        val j = case stop of NONE => length phases - 1 | SOME n => find_phase n

        val phases = take (j+1) phases |> drop i

        val _ = case phases of [] => error "No phases selected, range is empty" | _ => ()
      in
        phases
      end
    in  
  
      fun PHASES' phases ctrl ctxt = let
        val phases = ph_range phases (#start ctrl) (#stop ctrl)
        val phases = map (fn (n,tac,d) => (n,tac ctxt,d)) phases
  
        fun r [] _ st = Seq.single st
          | r ((name,tac,d)::tacs) i st = let
              val n = Thm.nprems_of st
              val bailout_tac = if #int_res ctrl then all_tac else no_tac
              fun trace_tac msg st = (if #trace ctrl then tracing msg else (); Seq.single st)
              
              val trace_goal_tac = if #trace_goals ctrl then print_tac ctxt "Proof state" else all_tac
              
              val trace_start_tac = trace_tac ("Phase " ^ name)
            in
              K trace_goal_tac THEN' K trace_start_tac THEN' IF_EXGOAL (tac)
              THEN_ELSE' (
                fn i => fn st => 
                  (* Bail out if a phase does not solve/create exactly the expected subgoals *)
                  if Thm.nprems_of st = n+d then
                    ((trace_tac "  Done" THEN r tacs i) st)
                  else
                    (trace_tac "*** Wrong number of produced goals" THEN bailout_tac) st
                
              , 
                K (trace_tac "*** Phase tactic failed" THEN bailout_tac))
            end i st
  
      in
        r phases
      end


    end

  end


  signature SEPREF_DEBUGGING = sig
    (*************************)
    (* Debugging *)
    (* Centralized debugging mode flag *)
    val cfg_debug_all: bool Config.T

    val is_debug: bool Config.T -> Proof.context -> bool
    val is_debug': Proof.context -> bool

    (* Conversion, trace errors if custom or central debugging flag is activated *)
    val DBG_CONVERSION: bool Config.T -> Proof.context -> conv -> tactic'

    (* Conversion, trace errors if central debugging flag is activated *)
    val DBG_CONVERSION': Proof.context -> conv -> tactic'

    (* Tracing message and current subgoal *)
    val tracing_tac': string -> Proof.context -> tactic'
    (* Warning message and current subgoal *)
    val warning_tac': string -> Proof.context -> tactic'
    (* Error message and current subgoal *)
    val error_tac': string -> Proof.context -> tactic'

    (* Trace debug message *)
    val dbg_trace_msg: bool Config.T -> Proof.context -> string -> unit
    val dbg_trace_msg': Proof.context -> string -> unit
    
    val dbg_trace: bool Config.T -> Proof.context -> (Proof.context -> string) -> unit
    val dbg_trace': Proof.context -> (Proof.context -> string) -> unit

    val dbg_msg_tac: bool Config.T -> (Proof.context -> int -> thm -> string) -> Proof.context -> tactic'
    val dbg_msg_tac': (Proof.context -> int -> thm -> string) -> Proof.context -> tactic'

    val msg_text: string -> Proof.context -> int -> thm -> string
    val msg_subgoal: string -> Proof.context -> int -> thm -> string
    val msg_from_subgoal: string -> (term -> Proof.context -> string) -> Proof.context -> int -> thm -> string
    val msg_allgoals: string -> Proof.context -> int -> thm -> string

  end

  structure Sepref_Debugging: SEPREF_DEBUGGING = struct

    val cfg_debug_all = 
      Attrib.setup_config_bool @{binding sepref_debug_all} (K false)

    fun is_debug cfg ctxt = Config.get ctxt cfg orelse Config.get ctxt cfg_debug_all
    fun is_debug' ctxt = Config.get ctxt cfg_debug_all

    fun dbg_trace cfg ctxt obj = 
      if is_debug cfg ctxt then  
        tracing ((obj ctxt))
      else ()

    fun dbg_trace' ctxt obj = 
      if is_debug' ctxt then  
        tracing ((obj ctxt))
      else ()

    fun dbg_trace_msg cfg ctxt msg =   
      if is_debug cfg ctxt then  
        tracing msg
      else ()
    fun dbg_trace_msg' ctxt msg = 
      if is_debug' ctxt then  
        tracing msg
      else ()

    fun DBG_CONVERSION cfg ctxt cv i st = 
      Seq.single (Conv.gconv_rule cv i st)
      handle e as THM _   => (dbg_trace cfg ctxt (K (@{make_string} e)); Seq.empty)
           | e as CTERM _ => (dbg_trace cfg ctxt (K (@{make_string} e)); Seq.empty)
           | e as TERM _  => (dbg_trace cfg ctxt (K (@{make_string} e)); Seq.empty)
           | e as TYPE _  => (dbg_trace cfg ctxt (K (@{make_string} e)); Seq.empty);

    fun DBG_CONVERSION' ctxt cv i st = 
      Seq.single (Conv.gconv_rule cv i st)
      handle e as THM _   => (dbg_trace' ctxt (K (@{make_string} e)); Seq.empty)
           | e as CTERM _ => (dbg_trace' ctxt (K (@{make_string} e)); Seq.empty)
           | e as TERM _  => (dbg_trace' ctxt (K (@{make_string} e)); Seq.empty)
           | e as TYPE _  => (dbg_trace' ctxt (K (@{make_string} e)); Seq.empty);


    local 
      fun gen_subgoal_msg_tac do_msg msg ctxt = IF_EXGOAL (fn i => fn st => let
        val t = nth (Thm.prems_of st) (i-1)
        val _ = Pretty.block [Pretty.str msg, Pretty.fbrk, Syntax.pretty_term ctxt t]
          |> Pretty.string_of |> do_msg

      in
        Seq.single st
      end)
    in       
      val tracing_tac' = gen_subgoal_msg_tac tracing
      val warning_tac' = gen_subgoal_msg_tac warning
      val error_tac' = gen_subgoal_msg_tac error
    end


    fun dbg_msg_tac cfg msg ctxt =
      if is_debug cfg ctxt then (fn i => fn st => (tracing (msg ctxt i st); Seq.single st))
      else K all_tac
    fun dbg_msg_tac' msg ctxt =
      if is_debug' ctxt then (fn i => fn st => (tracing (msg ctxt i st); Seq.single st))
      else K all_tac

    fun msg_text msg _ _ _ = msg

    fun msg_from_subgoal msg sgmsg ctxt i st = 
      case try (nth (Thm.prems_of st)) (i-1) of
        NONE => msg ^ "\n" ^ "Subgoal out of range"
      | SOME t => msg ^ "\n" ^ sgmsg t ctxt

    fun msg_subgoal msg = msg_from_subgoal msg (fn t => fn ctxt =>
      Syntax.pretty_term ctxt t |> Pretty.string_of
    )

    fun msg_allgoals msg ctxt _ st = 
      msg ^ "\n" ^ Pretty.string_of (Pretty.chunks (Goal_Display.pretty_goals ctxt st))

  end
\<close>


ML \<open>
  (* Tactics for produced subgoals *)
  infix 1 THEN_NEXT THEN_ALL_NEW_LIST THEN_ALL_NEW_LIST'
  signature STACTICAL = sig
    (* Apply first tactic on this subgoal, and then second tactic on next subgoal *)
    val THEN_NEXT: tactic' * tactic' -> tactic'
    (* Apply tactics to the current and following subgoals *)
    val APPLY_LIST: tactic' list -> tactic'
    (* Apply list of tactics on subgoals emerging from tactic. 
      Requires exactly one tactic per emerging subgoal.*)
    val THEN_ALL_NEW_LIST: tactic' * tactic' list -> tactic'
    (* Apply list of tactics to subgoals emerging from tactic, use fallback for additional subgoals. *)
    val THEN_ALL_NEW_LIST': tactic' * (tactic' list * tactic') -> tactic'

  end

  structure STactical : STACTICAL = struct
    infix 1 THEN_WITH_GOALDIFF
    fun (tac1 THEN_WITH_GOALDIFF tac2) st = let
      val n1 = Thm.nprems_of st
    in
      st |> (tac1 THEN (fn st => tac2 (Thm.nprems_of st - n1) st ))
    end

    fun (tac1 THEN_NEXT tac2) i = 
      tac1 i THEN_WITH_GOALDIFF (fn d => (
        if d < ~1 then 
          (error "THEN_NEXT: Tactic solved more than one goal"; no_tac) 
        else 
          tac2 (i+1+d)
      ))

    fun APPLY_LIST [] = K all_tac
      | APPLY_LIST (tac::tacs) = tac THEN_NEXT APPLY_LIST tacs
            
    fun (tac1 THEN_ALL_NEW_LIST tacs) i = 
      tac1 i 
      THEN_WITH_GOALDIFF (fn d =>
        if d+1 <> length tacs then (
          error "THEN_ALL_NEW_LIST: Tactic produced wrong number of goals"; no_tac
        ) else APPLY_LIST tacs i
      )

    fun (tac1 THEN_ALL_NEW_LIST' (tacs,rtac)) i =  
      tac1 i 
      THEN_WITH_GOALDIFF (fn d => let
        val _ = if d+1 < length tacs then error "THEN_ALL_NEW_LIST': Tactic produced too few goals" else ();
        val tacs' = tacs @ replicate (d + 1 - length tacs) rtac
      in    
        APPLY_LIST tacs' i
      end)


  end


  open STactical
\<close>

end
