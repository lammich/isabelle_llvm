section \<open>HOL Setup\<close>
theory Sepref_HOL_Bindings
imports Sepref_Tool
begin

subsection \<open>Assertion Annotation\<close>
text \<open>Annotate an assertion to a term. The term must then be refined with this assertion.\<close>
(* TODO: Version for monadic expressions.*)
definition ASSN_ANNOT :: "('a \<Rightarrow> 'ai \<Rightarrow> assn) \<Rightarrow> 'a \<Rightarrow> 'a" where [simp]: "ASSN_ANNOT A x \<equiv> x"
context fixes A :: "'a \<Rightarrow> 'ai \<Rightarrow> assn" begin
  sepref_register "PR_CONST (ASSN_ANNOT A)"
  lemma [def_pat_rules]: "ASSN_ANNOT$A \<equiv> UNPROTECT (ASSN_ANNOT A)" by simp
  lemma [sepref_fr_rules]: "(return o (\<lambda>x. x), RETURN o PR_CONST (ASSN_ANNOT A)) \<in> A\<^sup>d\<rightarrow>\<^sub>aA"
    by sepref_to_hoare vcg
    
end  

lemma annotate_assn: "x \<equiv> ASSN_ANNOT A x" by simp


subsection \<open>Identity Relations\<close>
definition "IS_ID R \<equiv> R=Id"
definition "IS_BELOW_ID R \<equiv> R\<subseteq>Id"

lemma [safe_constraint_rules]: 
  "IS_ID Id"
  "IS_ID R1 \<Longrightarrow> IS_ID R2 \<Longrightarrow> IS_ID (R1 \<rightarrow> R2)"
  "IS_ID R \<Longrightarrow> IS_ID (\<langle>R\<rangle>option_rel)"
  "IS_ID R \<Longrightarrow> IS_ID (\<langle>R\<rangle>list_rel)"
  "IS_ID R1 \<Longrightarrow> IS_ID R2 \<Longrightarrow> IS_ID (R1 \<times>\<^sub>r R2)"
  "IS_ID R1 \<Longrightarrow> IS_ID R2 \<Longrightarrow> IS_ID (\<langle>R1,R2\<rangle>sum_rel)"
  by (auto simp: IS_ID_def)

lemma [safe_constraint_rules]: 
  "IS_BELOW_ID Id"
  "IS_BELOW_ID R \<Longrightarrow> IS_BELOW_ID (\<langle>R\<rangle>option_rel)"
  "IS_BELOW_ID R1 \<Longrightarrow> IS_BELOW_ID R2 \<Longrightarrow> IS_BELOW_ID (R1 \<times>\<^sub>r R2)"
  "IS_BELOW_ID R1 \<Longrightarrow> IS_BELOW_ID R2 \<Longrightarrow> IS_BELOW_ID (\<langle>R1,R2\<rangle>sum_rel)"
  by (auto simp: IS_ID_def IS_BELOW_ID_def option_rel_def sum_rel_def list_rel_def)

lemma IS_BELOW_ID_fun_rel_aux: "R1\<supseteq>Id \<Longrightarrow> IS_BELOW_ID R2 \<Longrightarrow> IS_BELOW_ID (R1 \<rightarrow> R2)"
  by (auto simp: IS_BELOW_ID_def dest: fun_relD)

corollary IS_BELOW_ID_fun_rel[safe_constraint_rules]: 
  "IS_ID R1 \<Longrightarrow> IS_BELOW_ID R2 \<Longrightarrow> IS_BELOW_ID (R1 \<rightarrow> R2)"
  using IS_BELOW_ID_fun_rel_aux[of Id R2]
  by (auto simp: IS_ID_def)


lemma IS_BELOW_ID_list_rel[safe_constraint_rules]: 
  "IS_BELOW_ID R \<Longrightarrow> IS_BELOW_ID (\<langle>R\<rangle>list_rel)"
  unfolding IS_BELOW_ID_def
proof safe
  fix l l'
  assume A: "R\<subseteq>Id" 
  assume "(l,l')\<in>\<langle>R\<rangle>list_rel"
  thus "l=l'"
    apply induction
    using A by auto
qed

lemma IS_ID_imp_BELOW_ID[constraint_rules]: 
  "IS_ID R \<Longrightarrow> IS_BELOW_ID R"
  by (auto simp: IS_ID_def IS_BELOW_ID_def )



subsection \<open>Inverse Relation\<close>

lemma inv_fun_rel_eq[simp]: "(A\<rightarrow>B)\<inverse> = A\<inverse>\<rightarrow>B\<inverse>"
  by (auto dest: fun_relD)

lemma inv_option_rel_eq[simp]: "(\<langle>K\<rangle>option_rel)\<inverse> = \<langle>K\<inverse>\<rangle>option_rel"
  by (auto simp: option_rel_def)

lemma inv_prod_rel_eq[simp]: "(P \<times>\<^sub>r Q)\<inverse> = P\<inverse> \<times>\<^sub>r Q\<inverse>"
  by (auto)

lemma inv_sum_rel_eq[simp]: "(\<langle>P,Q\<rangle>sum_rel)\<inverse> = \<langle>P\<inverse>,Q\<inverse>\<rangle>sum_rel"
  by (auto simp: sum_rel_def)

lemma inv_list_rel_eq[simp]: "(\<langle>R\<rangle>list_rel)\<inverse> = \<langle>R\<inverse>\<rangle>list_rel"
  unfolding list_rel_def
  apply safe
  apply (subst list.rel_flip[symmetric])
  apply (simp add: conversep_iff[abs_def])
  apply (subst list.rel_flip[symmetric])
  apply (simp add: conversep_iff[abs_def])
  done

lemmas [constraint_simps] =
  Relation.converse_Id
  inv_fun_rel_eq
  inv_option_rel_eq
  inv_prod_rel_eq
  inv_sum_rel_eq
  inv_list_rel_eq


subsection \<open>Single Valued and Total Relations\<close>

(* TODO: Link to other such theories: Transfer, Autoref *)
definition "IS_LEFT_UNIQUE R \<equiv> single_valued (R\<inverse>)"
definition "IS_LEFT_TOTAL R \<equiv> Domain R = UNIV"
definition "IS_RIGHT_TOTAL R \<equiv> Range R = UNIV"
abbreviation (input) "IS_RIGHT_UNIQUE \<equiv> single_valued"

lemmas IS_RIGHT_UNIQUED = single_valuedD
lemma IS_LEFT_UNIQUED: "\<lbrakk>IS_LEFT_UNIQUE r; (y, x) \<in> r; (z, x) \<in> r\<rbrakk> \<Longrightarrow> y = z"
  by (auto simp: IS_LEFT_UNIQUE_def dest: single_valuedD)

lemma prop2p:
  "IS_LEFT_UNIQUE R = left_unique (rel2p R)"
  "IS_RIGHT_UNIQUE R = right_unique (rel2p R)"
  "right_unique (rel2p (R\<inverse>)) = left_unique (rel2p R)"
  "IS_LEFT_TOTAL R = left_total (rel2p R)"
  "IS_RIGHT_TOTAL R = right_total (rel2p R)"
  by (auto 
    simp: IS_LEFT_UNIQUE_def left_unique_def single_valued_def
    simp: right_unique_def
    simp: IS_LEFT_TOTAL_def left_total_def
    simp: IS_RIGHT_TOTAL_def right_total_def
    simp: rel2p_def
    )

lemma p2prop:
  "left_unique P = IS_LEFT_UNIQUE (p2rel P)"
  "right_unique P = IS_RIGHT_UNIQUE (p2rel P)"
  "left_total P = IS_LEFT_TOTAL (p2rel P)"
  "right_total P = IS_RIGHT_TOTAL (p2rel P)"
  "bi_unique P \<longleftrightarrow> left_unique P \<and> right_unique P"
  by (auto 
    simp: IS_LEFT_UNIQUE_def left_unique_def single_valued_def
    simp: right_unique_def bi_unique_alt_def
    simp: IS_LEFT_TOTAL_def left_total_def
    simp: IS_RIGHT_TOTAL_def right_total_def
    simp: p2rel_def
    )

lemmas [safe_constraint_rules] = 
  single_valued_Id  
  prod_rel_sv 
  list_rel_sv 
  option_rel_sv 
  sum_rel_sv

lemma [safe_constraint_rules]:
  "IS_LEFT_UNIQUE Id"
  "IS_LEFT_UNIQUE R1 \<Longrightarrow> IS_LEFT_UNIQUE R2 \<Longrightarrow> IS_LEFT_UNIQUE (R1\<times>\<^sub>rR2)"
  "IS_LEFT_UNIQUE R1 \<Longrightarrow> IS_LEFT_UNIQUE R2 \<Longrightarrow> IS_LEFT_UNIQUE (\<langle>R1,R2\<rangle>sum_rel)"
  "IS_LEFT_UNIQUE R \<Longrightarrow> IS_LEFT_UNIQUE (\<langle>R\<rangle>option_rel)"
  "IS_LEFT_UNIQUE R \<Longrightarrow> IS_LEFT_UNIQUE (\<langle>R\<rangle>list_rel)"
  by (auto simp: IS_LEFT_UNIQUE_def prod_rel_sv sum_rel_sv option_rel_sv list_rel_sv)

lemma IS_LEFT_TOTAL_alt: "IS_LEFT_TOTAL R \<longleftrightarrow> (\<forall>x. \<exists>y. (x,y)\<in>R)"
  by (auto simp: IS_LEFT_TOTAL_def)

lemma IS_RIGHT_TOTAL_alt: "IS_RIGHT_TOTAL R \<longleftrightarrow> (\<forall>x. \<exists>y. (y,x)\<in>R)"
  by (auto simp: IS_RIGHT_TOTAL_def)

lemma [safe_constraint_rules]:
  "IS_LEFT_TOTAL Id"
  "IS_LEFT_TOTAL R1 \<Longrightarrow> IS_LEFT_TOTAL R2 \<Longrightarrow> IS_LEFT_TOTAL (R1\<times>\<^sub>rR2)"
  "IS_LEFT_TOTAL R1 \<Longrightarrow> IS_LEFT_TOTAL R2 \<Longrightarrow> IS_LEFT_TOTAL (\<langle>R1,R2\<rangle>sum_rel)"
  "IS_LEFT_TOTAL R \<Longrightarrow> IS_LEFT_TOTAL (\<langle>R\<rangle>option_rel)"
  apply (auto simp: IS_LEFT_TOTAL_alt sum_rel_def option_rel_def list_rel_def)
  apply (rename_tac x; case_tac x; auto)
  apply (rename_tac x; case_tac x; auto)
  done

lemma [safe_constraint_rules]: "IS_LEFT_TOTAL R \<Longrightarrow> IS_LEFT_TOTAL (\<langle>R\<rangle>list_rel)"
  unfolding IS_LEFT_TOTAL_alt
proof safe
  assume A: "\<forall>x.\<exists>y. (x,y)\<in>R"
  fix l
  show "\<exists>l'. (l,l')\<in>\<langle>R\<rangle>list_rel"
    apply (induction l)
    using A
    by (auto simp: list_rel_split_right_iff)
qed

lemma [safe_constraint_rules]:
  "IS_RIGHT_TOTAL Id"
  "IS_RIGHT_TOTAL R1 \<Longrightarrow> IS_RIGHT_TOTAL R2 \<Longrightarrow> IS_RIGHT_TOTAL (R1\<times>\<^sub>rR2)"
  "IS_RIGHT_TOTAL R1 \<Longrightarrow> IS_RIGHT_TOTAL R2 \<Longrightarrow> IS_RIGHT_TOTAL (\<langle>R1,R2\<rangle>sum_rel)"
  "IS_RIGHT_TOTAL R \<Longrightarrow> IS_RIGHT_TOTAL (\<langle>R\<rangle>option_rel)"
  apply (auto simp: IS_RIGHT_TOTAL_alt sum_rel_def option_rel_def) []
  apply (auto simp: IS_RIGHT_TOTAL_alt sum_rel_def option_rel_def) []
  apply (auto simp: IS_RIGHT_TOTAL_alt sum_rel_def option_rel_def) []
  apply (rename_tac x; case_tac x; auto)
  apply (clarsimp simp: IS_RIGHT_TOTAL_alt option_rel_def)
  apply (rename_tac x; case_tac x; auto)
  done

lemma [safe_constraint_rules]: "IS_RIGHT_TOTAL R \<Longrightarrow> IS_RIGHT_TOTAL (\<langle>R\<rangle>list_rel)"
  unfolding IS_RIGHT_TOTAL_alt
proof safe
  assume A: "\<forall>x.\<exists>y. (y,x)\<in>R"
  fix l
  show "\<exists>l'. (l',l)\<in>\<langle>R\<rangle>list_rel"
    apply (induction l)
    using A
    by (auto simp: list_rel_split_left_iff)
qed
  
lemma [constraint_simps]:
  "IS_LEFT_TOTAL (R\<inverse>) \<longleftrightarrow> IS_RIGHT_TOTAL R "
  "IS_RIGHT_TOTAL (R\<inverse>) \<longleftrightarrow> IS_LEFT_TOTAL R  "
  "IS_LEFT_UNIQUE (R\<inverse>) \<longleftrightarrow> IS_RIGHT_UNIQUE R"
  "IS_RIGHT_UNIQUE (R\<inverse>) \<longleftrightarrow> IS_LEFT_UNIQUE R "
  by (auto simp: IS_RIGHT_TOTAL_alt IS_LEFT_TOTAL_alt IS_LEFT_UNIQUE_def)

lemma [safe_constraint_rules]:
  "IS_RIGHT_UNIQUE A \<Longrightarrow> IS_RIGHT_TOTAL B \<Longrightarrow> IS_RIGHT_TOTAL (A\<rightarrow>B)"
  "IS_RIGHT_TOTAL A \<Longrightarrow> IS_RIGHT_UNIQUE B \<Longrightarrow> IS_RIGHT_UNIQUE (A\<rightarrow>B)"
  "IS_LEFT_UNIQUE A \<Longrightarrow> IS_LEFT_TOTAL B \<Longrightarrow> IS_LEFT_TOTAL (A\<rightarrow>B)"
  "IS_LEFT_TOTAL A \<Longrightarrow> IS_LEFT_UNIQUE B \<Longrightarrow> IS_LEFT_UNIQUE (A\<rightarrow>B)"
  apply (simp_all add: prop2p rel2p)
  (*apply transfer_step TODO: Isabelle 2016 *)
  apply (blast intro!: transfer_raw)+
  done

lemma [constraint_rules]: 
  "IS_BELOW_ID R \<Longrightarrow> IS_RIGHT_UNIQUE R"
  "IS_BELOW_ID R \<Longrightarrow> IS_LEFT_UNIQUE R"
  "IS_ID R \<Longrightarrow> IS_RIGHT_TOTAL R"
  "IS_ID R \<Longrightarrow> IS_LEFT_TOTAL R"
  by (auto simp: IS_BELOW_ID_def IS_ID_def IS_LEFT_UNIQUE_def IS_RIGHT_TOTAL_def IS_LEFT_TOTAL_def
    intro: single_valuedI)

thm constraint_rules

subsubsection \<open>Additional Parametricity Lemmas\<close>
(* TODO: Move. Problem: Depend on IS_LEFT_UNIQUE, which has to be moved to!*)

lemma param_distinct[param]: "\<lbrakk>IS_LEFT_UNIQUE A; IS_RIGHT_UNIQUE A\<rbrakk> \<Longrightarrow> (distinct, distinct) \<in> \<langle>A\<rangle>list_rel \<rightarrow> bool_rel"  
  apply (fold rel2p_def)
  apply (simp add: rel2p)
  apply (rule distinct_transfer)
  apply (simp add: p2prop)
  done

lemma param_Image[param]: 
  assumes "IS_LEFT_UNIQUE A" "IS_RIGHT_UNIQUE A"
  shows "((``), (``)) \<in> \<langle>A\<times>\<^sub>rB\<rangle>set_rel \<rightarrow> \<langle>A\<rangle>set_rel \<rightarrow> \<langle>B\<rangle>set_rel"
  apply (clarsimp simp: set_rel_def; intro conjI)  
  apply (fastforce dest: IS_RIGHT_UNIQUED[OF assms(2)])
  apply (fastforce dest: IS_LEFT_UNIQUED[OF assms(1)])
  done

lemma pres_eq_iff_svb: "((=),(=))\<in>K\<rightarrow>K\<rightarrow>bool_rel \<longleftrightarrow> (single_valued K \<and> single_valued (K\<inverse>))"
  apply (safe intro!: single_valuedI)
  apply (metis (full_types) IdD fun_relD1)
  apply (metis (full_types) IdD fun_relD1)
  by (auto dest: single_valuedD)

definition "IS_PRES_EQ R \<equiv> ((=), (=))\<in>R\<rightarrow>R\<rightarrow>bool_rel"
lemma [constraint_rules]: "\<lbrakk>single_valued R; single_valued (R\<inverse>)\<rbrakk> \<Longrightarrow> IS_PRES_EQ R"
  by (simp add: pres_eq_iff_svb IS_PRES_EQ_def)


subsection \<open>Bounded Assertions\<close>
definition "b_rel R P \<equiv> R \<inter> UNIV\<times>Collect P"
definition "b_assn A P \<equiv> \<lambda>x y. \<up>(P x) ** A x y"

lemma b_assn_pure_conv[constraint_simps]: "b_assn (pure R) P = pure (b_rel R P)"
  by (auto del: ext intro!: ext simp: b_rel_def b_assn_def pure_def pred_lift_extract_simps)
lemmas [sepref_import_rewrite, sepref_frame_normrel_eqs, fcomp_norm_unfold] 
  = b_assn_pure_conv[symmetric]

lemma b_rel_nesting[simp]: 
  "b_rel (b_rel R P1) P2 = b_rel R (\<lambda>x. P1 x \<and> P2 x)"
  by (auto simp: b_rel_def)
lemma b_rel_triv[simp]: 
  "b_rel R (\<lambda>_. True) = R"
  by (auto simp: b_rel_def)
lemma b_assn_nesting[simp]: 
  "b_assn (b_assn A P1) P2 = b_assn A (\<lambda>x. P1 x \<and> P2 x)"
  by (auto simp: b_assn_def pure_def pred_lift_extract_simps del: ext intro!: ext)
lemma b_assn_triv[simp]: 
  "b_assn A (\<lambda>_. True) = A"
  by (auto simp: b_assn_def pure_def pred_lift_extract_simps del: ext intro!: ext)

lemmas [constraint_simps,sepref_import_rewrite, sepref_frame_normrel_eqs, fcomp_norm_unfold]
  = b_rel_nesting b_assn_nesting

lemma b_rel_simp[simp]: "(x,y)\<in>b_rel R P \<longleftrightarrow> (x,y)\<in>R \<and> P y"
  by (auto simp: b_rel_def)

lemma b_assn_simp[simp]: "b_assn A P x y = (\<up>(P x) ** A x y)"
  by (auto simp: b_assn_def)

lemma b_rel_Range[simp]: "Range (b_rel R P) = Range R \<inter> Collect P" by auto
lemma b_assn_rdom[simp]: "rdomp (b_assn R P) x \<longleftrightarrow> rdomp R x \<and> P x"
  by (auto simp: rdomp_def pred_lift_extract_simps)


lemma b_rel_below_id[constraint_rules,relator_props]: 
  "IS_BELOW_ID R \<Longrightarrow> IS_BELOW_ID (b_rel R P)"
  by (auto simp: IS_BELOW_ID_def)

lemma b_rel_left_unique[constraint_rules,relator_props]: 
  "IS_LEFT_UNIQUE R \<Longrightarrow> IS_LEFT_UNIQUE (b_rel R P)"
  by (auto simp: IS_LEFT_UNIQUE_def single_valued_def)
  
lemma b_rel_right_unique[constraint_rules,relator_props]: 
  "IS_RIGHT_UNIQUE R \<Longrightarrow> IS_RIGHT_UNIQUE (b_rel R P)"
  by (auto simp: single_valued_def)

\<comment> \<open>Registered as safe rule, although may loose information in the 
    odd case that purity depends condition.\<close>
lemma b_assn_is_pure[safe_constraint_rules, simp]:
  "is_pure A \<Longrightarrow> is_pure (b_assn A P)"
  by (auto simp: is_pure_conv b_assn_pure_conv)

lemma R_comp_brel_id_conv[fcomp_norm_simps]: "R O b_rel Id P = b_rel R P" by auto
  
  
\<comment> \<open>Most general form\<close>
lemma b_assn_subtyping_match[sepref_frame_match_rules]:
  assumes "hn_ctxt (b_assn A P) x y \<turnstile> hn_ctxt A' x y"
  assumes "\<lbrakk>vassn_tag (hn_ctxt A x y); vassn_tag (hn_ctxt A' x y); P x\<rbrakk> \<Longrightarrow> P' x"
  shows "hn_ctxt (b_assn A P) x y \<turnstile> hn_ctxt (b_assn A' P') x y"
  using assms
  unfolding hn_ctxt_def b_assn_def entails_def vassn_tag_def
  by (auto simp: pred_lift_extract_simps)
  
\<comment> \<open>Simplified forms:\<close>
lemma b_assn_subtyping_match_eqA[sepref_frame_match_rules]:
  assumes "\<lbrakk>vassn_tag (hn_ctxt A x y); P x\<rbrakk> \<Longrightarrow> P' x"
  shows "hn_ctxt (b_assn A P) x y \<turnstile> hn_ctxt (b_assn A P') x y"
  apply (rule b_assn_subtyping_match)
  subgoal 
    unfolding hn_ctxt_def b_assn_def entails_def vassn_tag_def
    by (auto simp: pred_lift_extract_simps)
  subgoal
    using assms .
  done  

lemma b_assn_subtyping_match_tR[sepref_frame_match_rules]:
  assumes "\<lbrakk>P x\<rbrakk> \<Longrightarrow> hn_ctxt A x y \<turnstile> hn_ctxt A' x y"
  shows "hn_ctxt (b_assn A P) x y \<turnstile> hn_ctxt A' x y"
  using assms
  unfolding hn_ctxt_def b_assn_def entails_def
  by (auto simp: pred_lift_extract_simps)

lemma b_assn_subtyping_match_tL[sepref_frame_match_rules]:
  assumes "hn_ctxt A x y \<turnstile> hn_ctxt A' x y"
  assumes "\<lbrakk>vassn_tag (hn_ctxt A x y)\<rbrakk> \<Longrightarrow> P' x"
  shows "hn_ctxt A x y \<turnstile> hn_ctxt (b_assn A' P') x y"
  using assms
  unfolding hn_ctxt_def b_assn_def entails_def vassn_tag_def
  by (auto simp: pred_lift_extract_simps)


lemma b_assn_subtyping_match_eqA_tR[sepref_frame_match_rules]: 
  "hn_ctxt (b_assn A P) x y \<turnstile> hn_ctxt A x y"
  unfolding hn_ctxt_def b_assn_def entails_def
  by (auto simp: pred_lift_extract_simps)

lemma b_assn_subtyping_match_eqA_tL[sepref_frame_match_rules]:
  assumes "\<lbrakk>vassn_tag (hn_ctxt A x y)\<rbrakk> \<Longrightarrow> P' x"
  shows "hn_ctxt A x y \<turnstile> hn_ctxt (b_assn A P') x y"
  using assms
  unfolding hn_ctxt_def b_assn_def entails_def vassn_tag_def
  by (auto simp: pred_lift_extract_simps)

  
lemma b_rel_gen_merge:
  assumes A: "MERGE1 A f B g C"  
  shows "MERGE1 (b_assn A P) f (b_assn B Q) g (b_assn C (\<lambda>x. P x \<or> Q x))"  
  supply [vcg_rules] = MERGE1D[OF A]
  apply rule
  by vcg
  
lemmas b_rel_merge_eq[sepref_frame_merge_rules] = b_rel_gen_merge[where P=P and Q=P for P, simplified]
lemmas [sepref_frame_merge_rules] = b_rel_gen_merge
lemmas b_rel_merge_left[sepref_frame_merge_rules] = b_rel_gen_merge[where Q="\<lambda>_. True", simplified]
lemmas b_rel_merge_right[sepref_frame_merge_rules] = b_rel_gen_merge[where P="\<lambda>_. True", simplified]
  
(*  
\<comment> \<open>General form\<close>
lemma b_rel_subtyping_merge[sepref_frame_merge_rules]:
  assumes "hn_ctxt A x y \<or>\<^sub>A hn_ctxt A' x y \<Longrightarrow>\<^sub>t hn_ctxt Am x y"
  shows "hn_ctxt (b_assn A P) x y \<or>\<^sub>A hn_ctxt (b_assn A' P') x y \<Longrightarrow>\<^sub>t hn_ctxt (b_assn Am (\<lambda>x. P x \<or> P' x)) x y"
  using assms
  unfolding hn_ctxt_def b_assn_def entailst_def entails_def
  by (fastforce simp: vassn_tag_def)
  
\<comment> \<open>Simplified forms\<close>
lemma b_rel_subtyping_merge_eqA[sepref_frame_merge_rules]:
  shows "hn_ctxt (b_assn A P) x y \<or>\<^sub>A hn_ctxt (b_assn A P') x y \<Longrightarrow>\<^sub>t hn_ctxt (b_assn A (\<lambda>x. P x \<or> P' x)) x y"
  apply (rule b_rel_subtyping_merge)
  by simp

lemma b_rel_subtyping_merge_tL[sepref_frame_merge_rules]:
  assumes "hn_ctxt A x y \<or>\<^sub>A hn_ctxt A' x y \<Longrightarrow>\<^sub>t hn_ctxt Am x y"
  shows "hn_ctxt A x y \<or>\<^sub>A hn_ctxt (b_assn A' P') x y \<Longrightarrow>\<^sub>t hn_ctxt Am x y"
  using b_rel_subtyping_merge[of A x y A' Am "\<lambda>_. True" P', simplified] assms .

lemma b_rel_subtyping_merge_tR[sepref_frame_merge_rules]:
  assumes "hn_ctxt A x y \<or>\<^sub>A hn_ctxt A' x y \<Longrightarrow>\<^sub>t hn_ctxt Am x y"
  shows "hn_ctxt (b_assn A P) x y \<or>\<^sub>A hn_ctxt A' x y \<Longrightarrow>\<^sub>t hn_ctxt Am x y"
  using b_rel_subtyping_merge[of A x y A' Am P "\<lambda>_. True", simplified] assms .

lemma b_rel_subtyping_merge_eqA_tL[sepref_frame_merge_rules]:
  shows "hn_ctxt A x y \<or>\<^sub>A hn_ctxt (b_assn A P') x y \<Longrightarrow>\<^sub>t hn_ctxt A x y"
  using b_rel_subtyping_merge_eqA[of A "\<lambda>_. True" x y P', simplified] .

lemma b_rel_subtyping_merge_eqA_tR[sepref_frame_merge_rules]:
  shows "hn_ctxt (b_assn A P) x y \<or>\<^sub>A hn_ctxt A x y \<Longrightarrow>\<^sub>t hn_ctxt A x y"
  using b_rel_subtyping_merge_eqA[of A P x y "\<lambda>_. True", simplified] .

(* TODO: Combinatorial explosion :( *)
lemma b_assn_invalid_merge1: "hn_invalid (b_assn A P) x y \<or>\<^sub>A hn_invalid (b_assn A P') x y
  \<Longrightarrow>\<^sub>t hn_invalid (b_assn A (\<lambda>x. P x \<or> P' x)) x y"
  by (sep_auto simp: hn_ctxt_def invalid_assn_def entailst_def)

lemma b_assn_invalid_merge2: "hn_invalid (b_assn A P) x y \<or>\<^sub>A hn_invalid A x y
  \<Longrightarrow>\<^sub>t hn_invalid A x y"
  by (sep_auto simp: hn_ctxt_def invalid_assn_def entailst_def)
lemma b_assn_invalid_merge3: "hn_invalid A x y \<or>\<^sub>A hn_invalid (b_assn A P) x y
  \<Longrightarrow>\<^sub>t hn_invalid A x y"
  by (sep_auto simp: hn_ctxt_def invalid_assn_def entailst_def)

lemma b_assn_invalid_merge4: "hn_invalid (b_assn A P) x y \<or>\<^sub>A hn_ctxt (b_assn A P') x y
  \<Longrightarrow>\<^sub>t hn_invalid (b_assn A (\<lambda>x. P x \<or> P' x)) x y"
  by (sep_auto simp: hn_ctxt_def invalid_assn_def entailst_def)
lemma b_assn_invalid_merge5: "hn_ctxt (b_assn A P') x y \<or>\<^sub>A hn_invalid (b_assn A P) x y
  \<Longrightarrow>\<^sub>t hn_invalid (b_assn A (\<lambda>x. P x \<or> P' x)) x y"
  by (sep_auto simp: hn_ctxt_def invalid_assn_def entailst_def)

lemma b_assn_invalid_merge6: "hn_invalid (b_assn A P) x y \<or>\<^sub>A hn_ctxt A x y
  \<Longrightarrow>\<^sub>t hn_invalid A x y"
  by (sep_auto simp: hn_ctxt_def invalid_assn_def entailst_def)
lemma b_assn_invalid_merge7: "hn_ctxt A x y \<or>\<^sub>A hn_invalid (b_assn A P) x y
  \<Longrightarrow>\<^sub>t hn_invalid A x y"
  by (sep_auto simp: hn_ctxt_def invalid_assn_def entailst_def)

lemma b_assn_invalid_merge8: "hn_ctxt (b_assn A P) x y \<or>\<^sub>A hn_invalid A x y
  \<Longrightarrow>\<^sub>t hn_invalid A x y"
  by (sep_auto simp: hn_ctxt_def invalid_assn_def entailst_def)
lemma b_assn_invalid_merge9: "hn_invalid A x y \<or>\<^sub>A hn_ctxt (b_assn A P) x y
  \<Longrightarrow>\<^sub>t hn_invalid A x y"
  by (sep_auto simp: hn_ctxt_def invalid_assn_def entailst_def)

lemmas b_assn_invalid_merge[sepref_frame_merge_rules] = 
  b_assn_invalid_merge1
  b_assn_invalid_merge2
  b_assn_invalid_merge3
  b_assn_invalid_merge4
  b_assn_invalid_merge5
  b_assn_invalid_merge6
  b_assn_invalid_merge7
  b_assn_invalid_merge8
  b_assn_invalid_merge9

*)



abbreviation nbn_rel :: "nat \<Rightarrow> (nat \<times> nat) set" 
  \<comment> \<open>Natural numbers with upper bound.\<close>
  where "nbn_rel n \<equiv> b_rel nat_rel (\<lambda>x::nat. x<n)"  


lemma in_R_comp_nbn_conv: "(a,b)\<in>(R O nbn_rel N) \<longleftrightarrow> (a,b)\<in>R \<and> b<N" by auto
lemma range_comp_nbn_conv: "Range (R O nbn_rel N) = Range R \<inter> {0..<N}"
  by (auto 0 3 simp: b_rel_def)

lemma mk_free_b_assn[sepref_frame_free_rules]:
  assumes "MK_FREE A f"  
  shows "MK_FREE (b_assn A P) f"  
proof -
  note [vcg_rules] = assms[THEN MK_FREED]
  show ?thesis by rule vcg
qed

lemma intf_of_b_rel[synth_rules]: "INTF_OF_REL R I \<Longrightarrow> INTF_OF_REL (b_rel R P) I" by simp

lemma b_assn_intf[intf_of_assn]: "intf_of_assn V I \<Longrightarrow> intf_of_assn (b_assn V P) I"
  by simp
  
    
subsection \<open>Tool Setup\<close>
lemmas [sepref_relprops] = 
  sepref_relpropI[of IS_LEFT_UNIQUE]
  sepref_relpropI[of IS_RIGHT_UNIQUE]
  sepref_relpropI[of IS_LEFT_TOTAL]
  sepref_relpropI[of IS_RIGHT_TOTAL]
  sepref_relpropI[of is_pure]
  sepref_relpropI[of "IS_PURE \<Phi>" for \<Phi>]
  sepref_relpropI[of IS_ID]
  sepref_relpropI[of IS_BELOW_ID]
 


lemma [sepref_relprops_simps]:
  "CONSTRAINT (IS_PURE IS_ID) A \<Longrightarrow> CONSTRAINT (IS_PURE IS_BELOW_ID) A"
  "CONSTRAINT (IS_PURE IS_ID) A \<Longrightarrow> CONSTRAINT (IS_PURE IS_LEFT_TOTAL) A"
  "CONSTRAINT (IS_PURE IS_ID) A \<Longrightarrow> CONSTRAINT (IS_PURE IS_RIGHT_TOTAL) A"
  "CONSTRAINT (IS_PURE IS_BELOW_ID) A \<Longrightarrow> CONSTRAINT (IS_PURE IS_LEFT_UNIQUE) A"
  "CONSTRAINT (IS_PURE IS_BELOW_ID) A \<Longrightarrow> CONSTRAINT (IS_PURE IS_RIGHT_UNIQUE) A"
  by (auto 
    simp: IS_ID_def IS_BELOW_ID_def IS_PURE_def IS_LEFT_UNIQUE_def
    simp: IS_LEFT_TOTAL_def IS_RIGHT_TOTAL_def
    simp: single_valued_below_Id)

declare True_implies_equals[sepref_relprops_simps]

lemma [sepref_relprops_transform]: "single_valued (R\<inverse>) = IS_LEFT_UNIQUE R"
  by (auto simp: IS_LEFT_UNIQUE_def)

  
subsection \<open>Default Initializers\<close>  
text \<open>We define a generic algorithm scheme to determine the abstract counterpart of
  the \<^term>\<open>init::'a::llvm_rep\<close> value wrt. an assertion. This is important for 
  initializing container data structures directly from zero-initializing \<open>calloc\<close>, 
  rather than having to \<open>memset\<close> each array.\<close>

definition is_init :: "('a \<Rightarrow> 'c::llvm_rep \<Rightarrow> assn) \<Rightarrow> 'a \<Rightarrow> bool" 
  where "is_init A i \<equiv> is_pure A \<and> (init,i) \<in> the_pure A"
  
lemma is_init_id_assn[sepref_gen_algo_rules]: "GEN_ALGO init (is_init id_assn)"
  by (auto simp: GEN_ALGO_def is_init_def)
  
  
subsection \<open>Arithmetics\<close>

subsubsection \<open>Connecting to Standard Operation Abstraction from LLVM-RS\<close>

text \<open>We will hide the connection behind an additional abstraction layer, 
  introduced by definitions. So, the definitions from this locale should not 
  be used by the end-user.
\<close>
context standard_opr_abstraction begin
  definition "rel \<equiv> br \<alpha> I"

  lemma assn_is_rel: "\<upharpoonleft>assn = pure rel"
    unfolding pure_def rel_def in_br_conv assn_def
    apply (intro ext)
    apply (auto simp: pred_lift_extract_simps)
    done
    
  abbreviation (input) sepref_assn where "sepref_assn \<equiv> pure rel"  

  lemma hn_un_op:
    assumes "is_un_op PRE cop xmop aop"  
    shows "(cop,(RETURN o aop)) \<in> [\<lambda>a. PRE TYPE('c) a]\<^sub>a sepref_assn\<^sup>k \<rightarrow> sepref_assn"
    unfolding assn_is_rel[symmetric]
    apply sepref_to_hoare
    supply [vcg_rules] = un_op_tmpl[OF assms]
    by vcg
      
  lemma hn_bin_op:
    assumes "is_bin_op PRE cop xmop aop"  
    shows "(uncurry cop,uncurry (RETURN oo aop)) \<in> [\<lambda>(a,b). PRE TYPE('c) a b]\<^sub>a sepref_assn\<^sup>k *\<^sub>a sepref_assn\<^sup>k \<rightarrow> sepref_assn"
    unfolding assn_is_rel[symmetric]
    apply sepref_to_hoare
    supply [vcg_rules] = bin_op_tmpl[OF assms]
    by vcg
    
  lemma hn_cmp_op:  
    assumes "is_cmp_op cop xmop aop"
    shows "(uncurry cop, uncurry (RETURN oo aop)) \<in> sepref_assn\<^sup>k *\<^sub>a sepref_assn\<^sup>k \<rightarrow>\<^sub>a bool.sepref_assn"
    unfolding assn_is_rel[symmetric] bool.assn_is_rel[symmetric]
    apply sepref_to_hoare
    supply [vcg_rules] = cmp_op_tmpl[OF assms]
    by vcg
    

end

subsubsection \<open>Operator Setup\<close>

text \<open>Not-Equals is an operator in LLVM, but not in HOL\<close>
definition [simp]: "op_neq a b \<equiv> a\<noteq>b"  
lemma op_neq_pat[def_pat_rules]: "Not$((=)$a$b) \<equiv> op_neq$a$b" by simp
sepref_register op_neq_word: "op_neq :: _ word \<Rightarrow> _"


text \<open>For technical reasons, we need the operands as parameters to the operators 
  on the concrete side of refinement theorems. Thus, we define the following shortcut
  for comparison operators. \<close>    
(* TODO/FIXME: This, in turn, relies on LLVM-inlining of from_bool (comparison)! 
  Perhaps we should directly generate the ll_icmp instructions
*)  
definition [llvm_inline]: "lift_cmp_op c a b \<equiv> from_bool (c a b)"  
  


   
subsubsection \<open>Boolean\<close>

definition "bool1_rel \<equiv> bool.rel"
abbreviation "bool1_assn \<equiv> (pure bool1_rel)"

lemma bool_const_refine[sepref_import_param]:
  "(0,False)\<in>bool1_rel"  
  "(1,True)\<in>bool1_rel"  
  by (auto simp: bool1_rel_def bool.rel_def in_br_conv)
  

lemma hn_bool_ops[sepref_fr_rules]:
  "(uncurry ll_and, uncurry (RETURN \<circ>\<circ> (\<and>))) \<in> bool1_assn\<^sup>k *\<^sub>a bool1_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  "(uncurry ll_or, uncurry (RETURN \<circ>\<circ> (\<or>))) \<in> bool1_assn\<^sup>k *\<^sub>a bool1_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  "(uncurry ll_xor, uncurry (RETURN \<circ>\<circ> (op_neq))) \<in> bool1_assn\<^sup>k *\<^sub>a bool1_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  "(ll_not1, RETURN \<circ> Not) \<in> bool1_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  using bool_bin_ops[THEN bool.hn_bin_op, folded bool1_rel_def, unfolded to_hfref_post]
    and bool_un_ops[THEN bool.hn_un_op, folded bool1_rel_def]
  unfolding op_neq_def  
  by simp_all

text \<open>We define an implies connective, using sepref\<close>
sepref_definition ll_implies is "uncurry (RETURN oo (\<longrightarrow>))" :: "bool1_assn\<^sup>k *\<^sub>a bool1_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  unfolding imp_conv_disj
  by sepref

declare ll_implies_def[llvm_inline]
declare ll_implies.refine[sepref_fr_rules]

lemma is_init_bool[sepref_gen_algo_rules]:
  "GEN_ALGO False (is_init bool1_assn)"
  unfolding GEN_ALGO_def is_init_def
  unfolding bool1_rel_def bool.rel_def
  by (simp add: in_br_conv)

subsubsection \<open>Direct Word Arithmetic\<close>

abbreviation "word_rel \<equiv> (Id::(_::len word \<times> _) set)"
abbreviation "word_assn \<equiv> (id_assn::_::len word \<Rightarrow> _)"

(* TODO: Move *)  
definition ll_not :: "'a::len word \<Rightarrow> 'a word llM" where 
  [llvm_inline]: "ll_not a \<equiv> doM { a \<leftarrow> ll_sub 0 a; ll_sub a 1 }"
  
context llvm_prim_arith_setup begin
  
  lemma ll_not_normalize[vcg_normalize_simps]: "ll_not a = return (~~a)"
    unfolding ll_not_def
    supply [simp] = NOT_eq
    by vcg_normalize
  
end  


context begin  
  interpretation llvm_prim_arith_setup .  
 
sepref_register 
  plus_word: "(+):: _ word \<Rightarrow> _"  
  minus_word: "(-):: _ word \<Rightarrow> _"  
  times_word: "(*):: _ word \<Rightarrow> _"  
  and_word: "(AND):: _ word \<Rightarrow> _"  
  or_word: "(OR):: _ word \<Rightarrow> _"  
  xor_word: "(XOR):: _ word \<Rightarrow> _"  
  
lemma word_param_imports[sepref_import_param]:
  "((+),(+)) \<in> word_rel \<rightarrow> word_rel \<rightarrow> word_rel"
  "((-),(-)) \<in> word_rel \<rightarrow> word_rel \<rightarrow> word_rel"
  "((*),(*)) \<in> word_rel \<rightarrow> word_rel \<rightarrow> word_rel"
  "((AND),(AND)) \<in> word_rel \<rightarrow> word_rel \<rightarrow> word_rel"
  "((OR),(OR)) \<in> word_rel \<rightarrow> word_rel \<rightarrow> word_rel"
  "((XOR),(XOR)) \<in> word_rel \<rightarrow> word_rel \<rightarrow> word_rel"
  by simp_all

sepref_register 
  not_word: "bitNOT:: _ word \<Rightarrow> _"  

lemma hn_word_NOT[sepref_fr_rules]: "(ll_not,RETURN o bitNOT) \<in> word_assn\<^sup>k \<rightarrow>\<^sub>a word_assn"
  by sepref_to_hoare vcg
  
sepref_register 
  div_word: "(div):: _ word \<Rightarrow> _"  
  mod_word: "(mod):: _ word \<Rightarrow> _"  
  sdiv_word: "(sdiv):: _ word \<Rightarrow> _"  
  smod_word: "(smod):: _ word \<Rightarrow> _"  
  
lemma hn_word_div_op[sepref_fr_rules]:
  "(uncurry (ll_udiv),uncurry (RETURN oo (div))) \<in> [\<lambda>(_,d). d\<noteq>0]\<^sub>a word_assn\<^sup>k *\<^sub>a word_assn\<^sup>k \<rightarrow> word_assn"  
  "(uncurry (ll_urem),uncurry (RETURN oo (mod))) \<in> [\<lambda>(_,d). d\<noteq>0]\<^sub>a word_assn\<^sup>k *\<^sub>a word_assn\<^sup>k \<rightarrow> word_assn"  
  "(uncurry (ll_sdiv),uncurry (RETURN oo (sdiv))) \<in> [\<lambda>(c,d). d\<noteq>0 \<and> in_srange (sdiv) c d]\<^sub>a word_assn\<^sup>k *\<^sub>a word_assn\<^sup>k \<rightarrow> word_assn"  
  "(uncurry (ll_srem),uncurry (RETURN oo (smod))) \<in> [\<lambda>(c,d). d\<noteq>0 \<and> in_srange (sdiv) c d]\<^sub>a word_assn\<^sup>k *\<^sub>a word_assn\<^sup>k \<rightarrow> word_assn"  
  by (sepref_to_hoare; vcg; fail)+

sepref_register 
  eq_word: "(=):: _ word \<Rightarrow> _"  
  neq_word: "op_neq:: _ word \<Rightarrow> _"  
  ult_word: "(<):: _ word \<Rightarrow> _"  
  ule_word: "(\<le>):: _ word \<Rightarrow> _"  
  slt_word: "(<s):: _ word \<Rightarrow> _"  
  sle_word: "(<=s):: _ word \<Rightarrow> _"  
    
lemma hn_word_icmp_op[sepref_fr_rules]:
  "(uncurry (ll_icmp_eq), uncurry (RETURN oo (=))) \<in> word_assn\<^sup>k *\<^sub>a word_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  "(uncurry (ll_icmp_ne), uncurry (RETURN oo (op_neq))) \<in> word_assn\<^sup>k *\<^sub>a word_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  "(uncurry (ll_icmp_ult), uncurry (RETURN oo (<))) \<in> word_assn\<^sup>k *\<^sub>a word_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  "(uncurry (ll_icmp_ule), uncurry (RETURN oo (\<le>))) \<in> word_assn\<^sup>k *\<^sub>a word_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  "(uncurry (ll_icmp_slt), uncurry (RETURN oo (\<lambda>a b. a <s b))) \<in> word_assn\<^sup>k *\<^sub>a word_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  "(uncurry (ll_icmp_sle), uncurry (RETURN oo (\<lambda>a b. a <=s b))) \<in> word_assn\<^sup>k *\<^sub>a word_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  unfolding bool1_rel_def bool.rel_def
  supply [simp] = in_br_conv
  apply (sepref_to_hoare; vcg; fail)+
  done
  

lemma is_init_word[sepref_gen_algo_rules]:
  "GEN_ALGO 0 (is_init word_assn)"
  unfolding GEN_ALGO_def is_init_def
  by (simp)
  
end  
      

subsubsection \<open>Integer by Word\<close>
  
definition "sint_rel \<equiv> sint.rel"
abbreviation "sint_assn \<equiv> pure sint_rel"  

abbreviation (input) "sint_rel' TYPE('a::len) \<equiv> sint_rel :: ('a word \<times> _) set"
abbreviation (input) "sint_assn' TYPE('a::len) \<equiv> sint_assn :: _ \<Rightarrow> 'a word \<Rightarrow> _"


definition [simp]: "sint_const TYPE('a::len) c \<equiv> (c::int)"
context fixes c::int begin
  sepref_register "sint_const TYPE('a::len) c" :: "int"
end


lemma fold_sint:
  "0 = sint_const TYPE('a::len) 0"  
  "1 = sint_const TYPE('a::len) 1"  
  "-1 \<equiv> (sint_const TYPE('a::len) (-1))"  
  "numeral n \<equiv> (sint_const TYPE('a::len) (numeral n))"
  "-(numeral n) \<equiv> (sint_const TYPE('a::len) (-numeral n))"
  by simp_all


lemma hn_sint_0[sepref_import_param]:
  "(0,sint_const TYPE('a) 0) \<in> sint_rel' TYPE('a::len)"
  by (auto simp: sint_rel_def sint.rel_def in_br_conv)

lemma hn_sint_1[sepref_fr_rules]:
  "LENGTH('a)\<noteq>1 \<Longrightarrow> hn_refine \<box> (return 1) \<box> (sint_assn' TYPE('a::len)) (RETURN$PR_CONST (sint_const TYPE('a) 1))"
  apply sepref_to_hoare unfolding sint_rel_def sint.rel_def in_br_conv by vcg

lemma hn_sint_minus_1[sepref_fr_rules]:
  "hn_refine \<box> (return (-1)) \<box> (sint_assn' TYPE('a::len)) (RETURN$PR_CONST (sint_const TYPE('a) (-1)))"
  apply sepref_to_hoare unfolding sint_rel_def sint.rel_def in_br_conv by vcg
  
lemma hn_sint_numeral[sepref_fr_rules]:
  "\<lbrakk>numeral n \<in> sints LENGTH('a)\<rbrakk> \<Longrightarrow> 
    hn_refine \<box> (return (numeral n)) \<box> (sint_assn' TYPE('a::len)) (RETURN$(PR_CONST (sint_const TYPE('a) (numeral n))))"
  apply sepref_to_hoare unfolding sint_rel_def sint.rel_def in_br_conv 
  apply vcg'
  by (auto simp: sbintrunc_mod2p min_sint_def max_sint_def ll_const_signed_aux)

lemma hn_sint_minus_numeral[sepref_fr_rules]:
  "\<lbrakk>-numeral n \<in> sints LENGTH('a)\<rbrakk> \<Longrightarrow> 
    hn_refine \<box> (return (-numeral n)) \<box> (sint_assn' TYPE('a::len)) (RETURN$(PR_CONST (sint_const TYPE('a) (-numeral n))))"
  apply sepref_to_hoare unfolding sint_rel_def sint.rel_def in_br_conv 
  apply vcg'
  apply (auto simp: sbintrunc_mod2p min_sint_def max_sint_def ll_const_signed_aux)
  by (smt diff_Suc_less int_mod_eq' len_gt_0 neg_numeral_le_numeral power_strict_increasing_iff)

  
sepref_register 
  plus_int: "(+)::int\<Rightarrow>_"    :: "int \<Rightarrow> int \<Rightarrow> int"
  minus_int: "(-)::int\<Rightarrow>_"   :: "int \<Rightarrow> int \<Rightarrow> int"
  times_int: "(*)::int\<Rightarrow>_"  :: "int \<Rightarrow> int \<Rightarrow> int"
  sdiv_int: "(sdiv)::int\<Rightarrow>_" :: "int \<Rightarrow> int \<Rightarrow> int"
  smod_int: "(smod)::int\<Rightarrow>_" :: "int \<Rightarrow> int \<Rightarrow> int"
  
sepref_register 
  eq_int: "(=)::int\<Rightarrow>_"        :: "int \<Rightarrow> int \<Rightarrow> bool"
  op_neq_int: "op_neq::int\<Rightarrow>_" :: "int \<Rightarrow> int \<Rightarrow> bool"
  lt_int: "(<)::int\<Rightarrow>_"        :: "int \<Rightarrow> int \<Rightarrow> bool"
  le_int: "(\<le>)::int\<Rightarrow>_"        :: "int \<Rightarrow> int \<Rightarrow> bool"
  
sepref_register    
  and_int: "(AND):: int \<Rightarrow> _"  
  or_int: "(OR):: int \<Rightarrow> _"  
  xor_int: "(XOR):: int \<Rightarrow> _"  

    
thm sint_cmp_ops[THEN sint.hn_cmp_op, folded sint_rel_def, unfolded to_hfref_post]  
thm sint_bin_ops[THEN sint.hn_bin_op, folded sint_rel_def, unfolded to_hfref_post]  
  
lemma hn_sint_ops[sepref_fr_rules]:
  "(uncurry ll_add, uncurry (RETURN \<circ>\<circ> (+)))
    \<in> [\<lambda>(a, b). a + b \<in> sints LENGTH('a)]\<^sub>a sint_assn\<^sup>k *\<^sub>a sint_assn\<^sup>k \<rightarrow> sint_assn' TYPE('a::len)"
  "(uncurry ll_sub, uncurry (RETURN \<circ>\<circ> (-)))
    \<in> [\<lambda>(a, b). a - b \<in> sints LENGTH('a)]\<^sub>a sint_assn\<^sup>k *\<^sub>a sint_assn\<^sup>k \<rightarrow> sint_assn' TYPE('a::len)"
  "(uncurry ll_mul, uncurry (RETURN \<circ>\<circ> (*)))
    \<in> [\<lambda>(a, b). a * b \<in> sints LENGTH('a)]\<^sub>a sint_assn\<^sup>k *\<^sub>a sint_assn\<^sup>k \<rightarrow> sint_assn' TYPE('a::len)"
  "(uncurry ll_sdiv, uncurry (RETURN \<circ>\<circ> (sdiv)))
    \<in> [\<lambda>(a, b). b \<noteq> 0 \<and> a sdiv b \<in> sints LENGTH('a)]\<^sub>a sint_assn\<^sup>k *\<^sub>a sint_assn\<^sup>k \<rightarrow> sint_assn' TYPE('a::len)"
  "(uncurry ll_srem, uncurry (RETURN \<circ>\<circ> (smod)))
    \<in> [\<lambda>(a, b). b \<noteq> 0 \<and> a sdiv b \<in> sints LENGTH('a)]\<^sub>a sint_assn\<^sup>k *\<^sub>a sint_assn\<^sup>k \<rightarrow> sint_assn' TYPE('a::len)"
    
  "(uncurry ll_icmp_eq, uncurry (RETURN \<circ>\<circ> (=))) \<in> sint_assn\<^sup>k *\<^sub>a sint_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  "(uncurry ll_icmp_ne, uncurry (RETURN \<circ>\<circ> (op_neq))) \<in> sint_assn\<^sup>k *\<^sub>a sint_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  "(uncurry ll_icmp_sle, uncurry (RETURN \<circ>\<circ> (\<le>))) \<in> sint_assn\<^sup>k *\<^sub>a sint_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  "(uncurry ll_icmp_slt, uncurry (RETURN \<circ>\<circ> (<))) \<in> sint_assn\<^sup>k *\<^sub>a sint_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  unfolding op_neq_def
  using sint_bin_ops[THEN sint.hn_bin_op, folded sint_rel_def, unfolded to_hfref_post]
    and sint_cmp_ops[THEN sint.hn_cmp_op, folded sint_rel_def bool1_rel_def, unfolded to_hfref_post]
  apply simp_all
  done

      
definition [simp]: "sint_init TYPE('a::len) \<equiv> 0::int"

(* TODO: Add rule for 0 *)
lemma is_init_sint[sepref_gen_algo_rules]:
  "GEN_ALGO (sint_init TYPE('a::len)) (is_init (sint_assn' TYPE('a)))"
  unfolding GEN_ALGO_def sint_init_def is_init_def
  unfolding sint_rel_def sint.rel_def
  by (simp add: in_br_conv)
  
lemma is_init_sint0[sepref_gen_algo_rules]: 
  "GEN_ALGO (sint_const TYPE('a::len) 0) (is_init (sint_assn' TYPE('a)))"
  using is_init_sint[where 'a='a]
  by simp
  

subsubsection \<open>Natural Numbers by Unsigned Word\<close>

sepref_register 
  plus_nat: "(+)::nat\<Rightarrow>_"    :: "nat \<Rightarrow> nat \<Rightarrow> nat"
  minus_nat: "(-)::nat\<Rightarrow>_"   :: "nat \<Rightarrow> nat \<Rightarrow> nat"
  times_nat: "(*)::nat\<Rightarrow>_"  :: "nat \<Rightarrow> nat \<Rightarrow> nat"
  div_nat: "(div)::nat\<Rightarrow>_"   :: "nat \<Rightarrow> nat \<Rightarrow> nat"
  mod_nat: "(mod)::nat\<Rightarrow>_"   :: "nat \<Rightarrow> nat \<Rightarrow> nat"
  
sepref_register 
  eq_nat: "(=)::nat\<Rightarrow>_"        :: "nat \<Rightarrow> nat \<Rightarrow> bool"
  op_neq_nat: "op_neq::nat\<Rightarrow>_" :: "nat \<Rightarrow> nat \<Rightarrow> bool"
  lt_nat: "(<)::nat\<Rightarrow>_"        :: "nat \<Rightarrow> nat \<Rightarrow> bool"
  le_nat: "(\<le>)::nat\<Rightarrow>_"        :: "nat \<Rightarrow> nat \<Rightarrow> bool"
  
sepref_register    
  and_nat: "(AND):: nat \<Rightarrow> _"  
  or_nat: "(OR):: nat \<Rightarrow> _"  
  xor_nat: "(XOR):: nat \<Rightarrow> _"  
  


definition unat_rel :: "('a::len word \<times> nat) set" where "unat_rel \<equiv> unat.rel"
abbreviation "unat_assn \<equiv> pure unat_rel"  

abbreviation (input) "unat_rel' TYPE('a::len) \<equiv> unat_rel :: ('a word \<times> _) set"
abbreviation (input) "unat_assn' TYPE('a::len) \<equiv> unat_assn :: _ \<Rightarrow> 'a word \<Rightarrow> _"

definition [simp]: "unat_const TYPE('a::len) c \<equiv> (c::nat)"
context fixes c::nat begin
  sepref_register "unat_const TYPE('a::len) c" :: "nat"
end

lemma fold_unat:
  "0 = unat_const TYPE('a::len) 0"  
  "1 = unat_const TYPE('a::len) 1"  
  "numeral n \<equiv> (unat_const TYPE('a::len) (numeral n))"
  by simp_all

  
lemma hn_unat_0[sepref_fr_rules]:
  "hn_refine \<box> (return 0) \<box> (unat_assn' TYPE('a::len)) (RETURN$PR_CONST (unat_const TYPE('a) 0))"
  apply sepref_to_hoare
  unfolding unat_rel_def unat.rel_def in_br_conv
  apply vcg
  done
  
lemma hn_unat_1[sepref_fr_rules]:
  "hn_refine \<box> (return 1) \<box> (unat_assn' TYPE('a::len)) (RETURN$PR_CONST (unat_const TYPE('a) 1))"
  apply sepref_to_hoare
  unfolding unat_rel_def unat.rel_def in_br_conv
  apply vcg
  done
  
  
lemma hn_unat_numeral[sepref_fr_rules]:
  "\<lbrakk>numeral n \<in> unats LENGTH('a)\<rbrakk> \<Longrightarrow> 
    hn_refine \<box> (return (numeral n)) \<box> (unat_assn' TYPE('a::len)) (RETURN$(PR_CONST (unat_const TYPE('a) (numeral n))))"
  apply sepref_to_hoare unfolding unat_rel_def unat.rel_def in_br_conv 
  apply vcg'
  by (metis in_unats_conv int_nat_eq of_nat_numeral uint_nonnegative unat_bintrunc unat_def word_of_int_numeral word_uint.Rep_inverse' word_unat.Rep_cases)

  
lemma hn_unat_ops[sepref_fr_rules]:
  "(uncurry ll_add, uncurry (RETURN \<circ>\<circ> (+))) \<in> [\<lambda>(a, b). a + b < max_unat LENGTH('a)]\<^sub>a unat_assn\<^sup>k *\<^sub>a unat_assn\<^sup>k \<rightarrow> unat_assn' TYPE('a::len)"
  "(uncurry ll_sub, uncurry (RETURN \<circ>\<circ> (-))) \<in> [\<lambda>(a, b). b \<le> a]\<^sub>a unat_assn\<^sup>k *\<^sub>a unat_assn\<^sup>k \<rightarrow> unat_assn"
  "(uncurry ll_mul, uncurry (RETURN \<circ>\<circ> (*))) \<in> [\<lambda>(a, b). a * b < max_unat LENGTH('a)]\<^sub>a unat_assn\<^sup>k *\<^sub>a unat_assn\<^sup>k \<rightarrow> unat_assn' TYPE('a::len)"
  "(uncurry ll_udiv, uncurry (RETURN \<circ>\<circ> (div))) \<in> [\<lambda>(a, b). b \<noteq> 0]\<^sub>a unat_assn\<^sup>k *\<^sub>a unat_assn\<^sup>k \<rightarrow> unat_assn"
  "(uncurry ll_urem, uncurry (RETURN \<circ>\<circ> (mod))) \<in> [\<lambda>(a, b). b \<noteq> 0]\<^sub>a unat_assn\<^sup>k *\<^sub>a unat_assn\<^sup>k \<rightarrow> unat_assn"
  
  "(uncurry ll_and, uncurry (RETURN \<circ>\<circ> (AND))) \<in> unat_assn\<^sup>k *\<^sub>a unat_assn\<^sup>k \<rightarrow>\<^sub>a unat_assn"
  "(uncurry ll_or, uncurry (RETURN \<circ>\<circ> (OR))) \<in> unat_assn\<^sup>k *\<^sub>a unat_assn\<^sup>k \<rightarrow>\<^sub>a unat_assn"
  "(uncurry ll_xor, uncurry (RETURN \<circ>\<circ> (XOR))) \<in> unat_assn\<^sup>k *\<^sub>a unat_assn\<^sup>k \<rightarrow>\<^sub>a unat_assn"
  
  "(uncurry ll_icmp_eq, uncurry (RETURN \<circ>\<circ> (=))) \<in> unat_assn\<^sup>k *\<^sub>a unat_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  "(uncurry ll_icmp_ne, uncurry (RETURN \<circ>\<circ> (op_neq))) \<in> unat_assn\<^sup>k *\<^sub>a unat_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  "(uncurry ll_icmp_ule, uncurry (RETURN \<circ>\<circ> (\<le>))) \<in> unat_assn\<^sup>k *\<^sub>a unat_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  "(uncurry ll_icmp_ult, uncurry (RETURN \<circ>\<circ> (<))) \<in> unat_assn\<^sup>k *\<^sub>a unat_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"  
  unfolding op_neq_def
  
  using unat_bin_ops[THEN unat.hn_bin_op, folded unat_rel_def]
    and unat_bin_ops_bitwise[THEN unat.hn_bin_op, folded unat_rel_def]
    and unat_cmp_ops[THEN unat.hn_cmp_op, folded unat_rel_def bool1_rel_def]
  by (simp_all add: prod_casesK)
  
definition [simp]: "unat_init TYPE('a::len) \<equiv> 0::nat"

lemma is_init_unat[sepref_gen_algo_rules]:
  "GEN_ALGO (unat_init TYPE('a::len)) (is_init (unat_assn' TYPE('a)))"
  unfolding GEN_ALGO_def unat_init_def is_init_def
  unfolding unat_rel_def unat.rel_def
  by (simp add: in_br_conv)
  
lemma is_init_unat0[sepref_gen_algo_rules]: 
  "GEN_ALGO (unat_const TYPE('a::len2) 0) (is_init (unat_assn' TYPE('a)))"
  using is_init_unat[where 'a='a]
  by simp
  
      
subsubsection \<open>Natural Numbers by Signed Word\<close>

definition snat_rel :: "('a::len2 word \<times> nat) set" where "snat_rel \<equiv> snat.rel"
abbreviation "snat_assn \<equiv> pure snat_rel"  

abbreviation (input) "snat_rel' TYPE('a::len2) \<equiv> snat_rel :: ('a word \<times> _) set"
abbreviation (input) "snat_assn' TYPE('a::len2) \<equiv> snat_assn :: _ \<Rightarrow> 'a word \<Rightarrow> _"

definition [simp]: "snat_const TYPE('a::len2) c \<equiv> (c::nat)"
context fixes c::nat begin
  sepref_register "snat_const TYPE('a::len2) c" :: "nat"
end


lemma fold_snat:
  "0 = snat_const TYPE('a::len2) 0"  
  "1 = snat_const TYPE('a::len2) 1"  
  "numeral n \<equiv> (snat_const TYPE('a::len2) (numeral n))"
  by simp_all

(* TODO: Move, and use for proofs about snat in LLVM_Shallow_RS *)  
lemma snat_invar_0: "snat_invar (0)"  
  by (simp add: snat_invar_def)

lemma snat_invar_1: "snat_invar (1)"  
  by (simp add: snat_invar_def)
  
lemma snat_invar_numeral: "\<lbrakk> numeral a < max_snat LENGTH('a::len2) \<rbrakk> \<Longrightarrow>
  snat_invar (numeral a::'a word)"
  by (metis (full_types) One_nat_def ll_const_signed_nat_aux2 max_snat_def snat_invar_def)
  
  
lemma hn_snat_0[sepref_fr_rules]:
  "hn_refine \<box> (return 0) \<box> (snat_assn' TYPE('a::len2)) (RETURN$PR_CONST (snat_const TYPE('a) 0))"
  apply sepref_to_hoare
  unfolding snat_rel_def snat.rel_def in_br_conv
  supply [simp] = snat_invar_0
  apply vcg
  done
  
lemma hn_snat_1[sepref_fr_rules]:
  "hn_refine \<box> (return 1) \<box> (snat_assn' TYPE('a::len2)) (RETURN$PR_CONST (snat_const TYPE('a) 1))"
  apply sepref_to_hoare
  unfolding snat_rel_def snat.rel_def in_br_conv
  supply [simp] = snat_invar_1
  apply vcg
  done
  
  
lemma hn_snat_numeral[sepref_fr_rules]:
  "\<lbrakk>numeral n \<in> snats LENGTH('a)\<rbrakk> \<Longrightarrow> 
    hn_refine \<box> (return (numeral n)) \<box> (snat_assn' TYPE('a::len2)) (RETURN$(PR_CONST (snat_const TYPE('a) (numeral n))))"
  apply sepref_to_hoare unfolding snat_rel_def snat.rel_def in_br_conv 
  supply [simp] = snat_invar_numeral
  apply vcg'
  done
  
lemma hn_snat_ops[sepref_fr_rules]:
  "(uncurry ll_add, uncurry (RETURN \<circ>\<circ> (+))) \<in> [\<lambda>(a, b). a + b < max_snat LENGTH('a)]\<^sub>a snat_assn\<^sup>k *\<^sub>a snat_assn\<^sup>k \<rightarrow> snat_assn' TYPE('a::len2)"
  "(uncurry ll_sub, uncurry (RETURN \<circ>\<circ> (-))) \<in> [\<lambda>(a, b). b \<le> a]\<^sub>a snat_assn\<^sup>k *\<^sub>a snat_assn\<^sup>k \<rightarrow> snat_assn"
  "(uncurry ll_mul, uncurry (RETURN \<circ>\<circ> (*))) \<in> [\<lambda>(a, b). a * b < max_snat LENGTH('a)]\<^sub>a snat_assn\<^sup>k *\<^sub>a snat_assn\<^sup>k \<rightarrow> snat_assn' TYPE('a::len2)"
  "(uncurry ll_udiv, uncurry (RETURN \<circ>\<circ> (div))) \<in> [\<lambda>(a, b). b \<noteq> 0]\<^sub>a snat_assn\<^sup>k *\<^sub>a snat_assn\<^sup>k \<rightarrow> snat_assn"
  "(uncurry ll_urem, uncurry (RETURN \<circ>\<circ> (mod))) \<in> [\<lambda>(a, b). b \<noteq> 0]\<^sub>a snat_assn\<^sup>k *\<^sub>a snat_assn\<^sup>k \<rightarrow> snat_assn"
  
  "(uncurry ll_icmp_eq, uncurry (RETURN \<circ>\<circ> (=))) \<in> snat_assn\<^sup>k *\<^sub>a snat_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  "(uncurry ll_icmp_ne, uncurry (RETURN \<circ>\<circ> (op_neq))) \<in> snat_assn\<^sup>k *\<^sub>a snat_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  "(uncurry ll_icmp_sle, uncurry (RETURN \<circ>\<circ> (\<le>))) \<in> snat_assn\<^sup>k *\<^sub>a snat_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  "(uncurry ll_icmp_slt, uncurry (RETURN \<circ>\<circ> (<))) \<in> snat_assn\<^sup>k *\<^sub>a snat_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"  
  unfolding op_neq_def
  using snat_bin_ops[THEN snat.hn_bin_op, folded snat_rel_def]
    and snat_cmp_ops[THEN snat.hn_cmp_op, folded snat_rel_def bool1_rel_def]
  by simp_all
  

definition [simp]: "snat_init TYPE('a::len) \<equiv> 0::nat"

lemma is_init_snat[sepref_gen_algo_rules]:
  "GEN_ALGO (snat_init TYPE('a::len2)) (is_init (snat_assn' TYPE('a)))"
  unfolding GEN_ALGO_def snat_init_def is_init_def
  unfolding snat_rel_def snat.rel_def
  by (simp add: snat_invar_0 in_br_conv)
  
lemma is_init_snat0[sepref_gen_algo_rules]: 
  "GEN_ALGO (snat_const TYPE('a::len2) 0) (is_init (snat_assn' TYPE('a)))"
  using is_init_snat[where 'a='a]
  by simp
  
  
subsubsection \<open>Ad-Hoc Method to Annotate Number Constructors\<close>  
lemma annot_num_const_cong: 
  "\<And>a b. snat_const a b = snat_const a b" 
  "\<And>a b. sint_const a b = sint_const a b" 
  "\<And>a b. unat_const a b = unat_const a b" 
  "ASSERT \<Phi> = ASSERT \<Phi>"
  "WHILEIT I = WHILEIT I"
  by simp_all
  
lemma unat_const_fold: 
  "0 = unat_const TYPE('a::len) 0"
  "1 = unat_const TYPE('a::len) 1"
  "numeral n = unat_const TYPE('a::len) (numeral n)"
  by simp_all
  
lemma snat_const_fold: 
  "0 = snat_const TYPE('a::len2) 0"
  "1 = snat_const TYPE('a::len2) 1"
  "numeral n = snat_const TYPE('a::len2) (numeral n)"
  by simp_all

lemma sint_const_fold: 
  "0 = sint_const TYPE('a::len) 0"
  "1 = sint_const TYPE('a::len) 1"
  "numeral n = sint_const TYPE('a::len) (numeral n)"
  "-sint_const TYPE('a::len) c = sint_const TYPE('a::len) (-c)"
  by simp_all
  
    
method annot_sint_const for T::"'a::len itself" = 
  (simp only: sint_const_fold[where 'a='a] cong: annot_num_const_cong)
  
method annot_snat_const for T::"'a::len2 itself" = 
  (simp only: snat_const_fold[where 'a='a] cong: annot_num_const_cong)
  
method annot_unat_const for T::"'a::len itself" = 
  (simp only: unat_const_fold[where 'a='a] cong: annot_num_const_cong)
  
  
subsection \<open>HOL Combinators\<close>

subsubsection \<open>If\<close>

lemma hn_if_aux:
  assumes P: "\<Gamma> \<turnstile> hn_val bool1_rel a a' ** \<Gamma>1"
  assumes RT: "a \<Longrightarrow> hn_refine (hn_val bool1_rel a a' ** \<Gamma>1) b' \<Gamma>2b R b"
  assumes RE: "\<not>a \<Longrightarrow> hn_refine (hn_val bool1_rel a a' ** \<Gamma>1) c' \<Gamma>2c R c"
  assumes MERGE: "MERGE \<Gamma>2b fb \<Gamma>2c fc \<Gamma>'"
  shows "hn_refine \<Gamma> 
    (llc_if a' (doM {r\<leftarrow>b'; fb; return r}) (doM {r\<leftarrow>c'; fc; return r})) 
    \<Gamma>' R (if a then b else c)"
  apply (rule hn_refine_nofailI)  
  apply (rule hn_refine_cons_pre[OF P])
proof (cases a, goal_cases)
  assume NF: "nofail (if a then b else c)"
  
  have [vcg_normalize_simps, fri_prepare_simps]: "hn_val bool1_rel = \<upharpoonleft>bool.assn"
    unfolding bool1_rel_def bool.assn_is_rel hn_ctxt_def ..
  
  note [vcg_rules] = MERGED[OF MERGE]  
    
  {
    case [simp]: 1
    from NF have [simp]: "nofail b" by simp
  
    note [vcg_rules] = RT[THEN hn_refineD, simplified]
  
    show ?case by rule vcg
  }
  {
    case [simp]: 2
    from NF have [simp]: "nofail c" by simp
  
    note [vcg_rules] = RE[THEN hn_refineD, simplified]
  
    show ?case by rule vcg
  }  
qed    


lemma hn_if[sepref_comb_rules]:
  assumes P: "\<Gamma> \<turnstile> hn_val bool1_rel a a' ** \<Gamma>1"
  assumes RT: "a \<Longrightarrow> hn_refine (hn_val bool1_rel a a' ** \<Gamma>1) b' \<Gamma>2b R b"
  assumes RE: "\<not>a \<Longrightarrow> hn_refine (hn_val bool1_rel a a' ** \<Gamma>1) c' \<Gamma>2c R c"
  assumes MERGE: "TERM If \<Longrightarrow> MERGE \<Gamma>2b fb \<Gamma>2c fc \<Gamma>'"
  shows "hn_refine \<Gamma> 
    (llc_if a' (doM {r\<leftarrow>b'; fb; return r}) (doM {r\<leftarrow>c'; fc; return r})) 
    \<Gamma>' R (If$a$b$c)"
  using P RT RE MERGE[OF TERMI]
  unfolding APP_def PROTECT2_def 
  by (rule hn_if_aux)


subsubsection \<open>While\<close>  
(* TODO: Move WHILE-stuff to HOL-Bindings Theory *)
lemma WHILEIT_pat[def_pat_rules]:
  "WHILEIT$I \<equiv> UNPROTECT (WHILEIT I)"
  "WHILET \<equiv> PR_CONST (WHILEIT (\<lambda>_. True))"
  by (simp_all add: WHILET_def)

lemma id_WHILEIT[id_rules]: 
  "PR_CONST (WHILEIT I) ::\<^sub>i TYPE(('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a nres) \<Rightarrow> 'a \<Rightarrow> 'a nres)"
  by simp

lemma WHILE_arities[sepref_monadify_arity]:
  (*"WHILET \<equiv> WHILEIT$(\<lambda>\<^sub>2_. True)"*)
  "PR_CONST (WHILEIT I) \<equiv> \<lambda>\<^sub>2b f s. SP (PR_CONST (WHILEIT I))$(\<lambda>\<^sub>2s. b$s)$(\<lambda>\<^sub>2s. f$s)$s"
  by (simp_all add: WHILET_def)

lemma WHILEIT_comb[sepref_monadify_comb]:
  "PR_CONST (WHILEIT I)$(\<lambda>\<^sub>2x. b x)$f$s \<equiv> 
    Refine_Basic.bind$(EVAL$s)$(\<lambda>\<^sub>2s. 
      SP (PR_CONST (monadic_WHILEIT I))$(\<lambda>\<^sub>2x. (EVAL$(b x)))$f$s
    )"
  by (simp_all add: WHILEIT_to_monadic)
  
lemma monadic_WHILEIT_pat[def_pat_rules]:
  "monadic_WHILEIT$I \<equiv> UNPROTECT (monadic_WHILEIT I)"
  by auto  
    
lemma id_monadic_WHILEIT[id_rules]: 
  "PR_CONST (monadic_WHILEIT I) ::\<^sub>i TYPE(('a \<Rightarrow> bool nres) \<Rightarrow> ('a \<Rightarrow> 'a nres) \<Rightarrow> 'a \<Rightarrow> 'a nres)"
  by simp
    
lemma monadic_WHILEIT_arities[sepref_monadify_arity]:
  "PR_CONST (monadic_WHILEIT I) \<equiv> \<lambda>\<^sub>2b f s. SP (PR_CONST (monadic_WHILEIT I))$(\<lambda>\<^sub>2s. b$s)$(\<lambda>\<^sub>2s. f$s)$s"
  by (simp)

lemma monadic_WHILEIT_comb[sepref_monadify_comb]:
  "PR_CONST (monadic_WHILEIT I)$b$f$s \<equiv> 
    Refine_Basic.bind$(EVAL$s)$(\<lambda>\<^sub>2s. 
      SP (PR_CONST (monadic_WHILEIT I))$b$f$s
    )"
  by (simp)
  
  
lemma hn_refine_add_invalid: (* Very customized rule for manual derivation of while *)
  "hn_refine (hn_ctxt Rs a b ** \<Gamma>) c \<Gamma>' R m \<Longrightarrow> hn_refine (hn_ctxt Rs a b ** \<Gamma>) c (hn_invalid Rs a b ** \<Gamma>') R m"
  by (smt hn_refine_frame' invalidate_clone' sep_conj_commute sep_conj_left_commute)
  
lemma hn_monadic_WHILE_aux:
  assumes FR: "P \<turnstile> hn_ctxt Rs s' s ** \<Gamma>"
  assumes b_ref: "\<And>s s'. I s' \<Longrightarrow> hn_refine 
    (hn_ctxt Rs s' s ** \<Gamma>)
    (b s)
    (\<Gamma>b s' s)
    (pure bool1_rel)
    (b' s')"
  assumes b_fr: "\<And>s' s. \<Gamma>b s' s \<turnstile> hn_ctxt Rs s' s ** \<Gamma>"

  assumes f_ref: "\<And>s' s. \<lbrakk>I s'\<rbrakk> \<Longrightarrow> hn_refine
    (hn_ctxt Rs s' s ** \<Gamma>)
    (f s)
    (\<Gamma>f s' s)
    Rs
    (f' s')"
  assumes f_fr: "\<And>s' s. \<Gamma>f s' s \<turnstile> hn_ctxt Rsf s' s ** \<Gamma>"
  assumes free: "MK_FREE Rsf fr"
  (*assumes PREC: "precise Rs"*)
  shows "hn_refine (P) (llc_while b (\<lambda>s. doM {r \<leftarrow> f s; fr s; return r}) s) (hn_invalid Rs s' s ** \<Gamma>) Rs (monadic_WHILEIT I b' f' s')"
  apply1 (rule hn_refine_cons_pre[OF FR])
  apply (rule hn_refine_add_invalid)
  
  apply (rule hn_refine_synthI)
  unfolding monadic_WHILEIT_def
  focus (rule hnr_RECT[where F'="\<lambda>s' s. \<Gamma>" and Ry=Rs])
    apply1 (rule hnr_ASSERT)
    focus (rule hnr_bind_manual_free)
      applyS (rule b_ref; simp)
      apply1 (rule hn_refine_cons_pre, sep_drule b_fr, rule entails_refl)
      focus (rule hn_if_aux[OF _ _ _ MERGE_triv])
        apply (fri_rotate entails_pre_cong :-1) apply (rule conj_entails_mono[OF entails_refl]) apply (rule entails_refl)
        focus (* Then-Part *)
          apply1 (rule hn_refine_cons_pre, sep_drule drop_hn_val, simp, rule entails_refl)
          apply (rule hnr_bind_manual_free)
          applyS (rule f_ref, simp)
          apply1 (rule hn_refine_cons_pre, sep_drule f_fr, simp, rule entails_refl)
          apply (rule hnr_freeI[OF free])
          apply (rule hn_refine_cons_pre[rotated], assumption)
          applyS (simp add: sep_conj_ac; rule entails_refl)
          solved
        focus (* Else-Part *)  
          apply (rule hn_refine_cons_post)
          apply (rule hn_refine_frame[OF hnr_RETURN_pass])
          apply (fri_rotate entails_pre_cong :1) apply (rule entails_refl)
          apply1 (sep_drule drop_hn_invalid)
          apply1 (sep_drule drop_hn_val)
          apply (simp)
          solved
        solved
      solved
    focus apply pf_mono_prover solved
    solved
  subgoal by (simp add: llc_while_def mwhile_def llc_if_def cong: if_cong)
  subgoal ..
  subgoal ..
  done

lemma hn_monadic_WHILE_lin[sepref_comb_rules]:
  assumes "INDEP Rs"
  assumes FR: "P \<turnstile> hn_ctxt Rs s' s ** \<Gamma>"
  assumes b_ref: "\<And>s s'. I s' \<Longrightarrow> hn_refine 
    (hn_ctxt Rs s' s ** \<Gamma>)
    (b s)
    (\<Gamma>b s' s)
    (pure bool1_rel)
    (b' s')"
  assumes b_fr: "\<And>s' s. TERM (monadic_WHILEIT,''cond'') \<Longrightarrow> \<Gamma>b s' s \<turnstile> hn_ctxt Rs s' s ** \<Gamma>"

  assumes f_ref: "\<And>s' s. I s' \<Longrightarrow> hn_refine
    (hn_ctxt Rs s' s ** \<Gamma>)
    (f s)
    (\<Gamma>f s' s)
    Rs
    (f' s')"
  assumes f_fr: "\<And>s' s. TERM (monadic_WHILEIT,''body'') \<Longrightarrow> \<Gamma>f s' s \<turnstile> hn_ctxt Rsf s' s ** \<Gamma>"
  assumes free: "TERM (monadic_WHILEIT,''free-old-state'') \<Longrightarrow> MK_FREE Rsf fr"
  shows "hn_refine 
    P 
    (llc_while b (\<lambda>s. doM {r \<leftarrow> f s; fr s; return r}) s) 
    (hn_invalid Rs s' s ** \<Gamma>)
    Rs 
    (PR_CONST (monadic_WHILEIT I)$(\<lambda>\<^sub>2s'. b' s')$(\<lambda>\<^sub>2s'. f' s')$(s'))"
  using assms(2-)
  unfolding APP_def PROTECT2_def CONSTRAINT_def PR_CONST_def
  by (rule hn_monadic_WHILE_aux)


  
subsubsection \<open>Let\<close>
lemma hn_let[sepref_comb_rules]:
  "hn_refine \<Gamma> c \<Gamma>' R (Refine_Basic.bind$(PASS$v)$(\<lambda>\<^sub>2x. f x)) \<Longrightarrow> hn_refine \<Gamma> c \<Gamma>' R (Let$v$(\<lambda>\<^sub>2x. f x))" 
  by simp
    
subsection \<open>Unit\<close>

lemma unit_hnr[sepref_import_param]: "((),())\<in>unit_rel" by auto
  
  
subsection "Product"


lemmas [sepref_import_rewrite, sepref_frame_normrel_eqs, fcomp_norm_unfold] = prod_assn_pure_conv[symmetric]


(* TODO Add corresponding rules for other types and add to datatype snippet *)
lemma intf_of_prod_assn[intf_of_assn]:
  assumes "intf_of_assn A TYPE('a)" "intf_of_assn B TYPE('b)"
  shows "intf_of_assn (prod_assn A B) TYPE('a * 'b)"
  by simp

lemma pure_prod[constraint_rules]: 
  assumes P1: "is_pure P1" and P2: "is_pure P2"
  shows "is_pure (prod_assn P1 P2)"
proof -
  from P1 obtain P1' where P1': "\<And>x x'. P1 x x' = \<up>(P1' x x')"
    using is_pureE by blast
  from P2 obtain P2' where P2': "\<And>x x'. P2 x x' = \<up>(P2' x x')"
    using is_pureE by blast

  show ?thesis proof
    fix x x'
    show "prod_assn P1 P2 x x' =
         \<up> (case (x, x') of ((a1, a2), c1, c2) \<Rightarrow> P1' a1 c1 \<and> P2' a2 c2)"
      unfolding prod_assn_def
      apply (simp add: P1' P2' sep_algebra_simps split: prod.split)
      done
  qed
qed

lemma prod_frame_match[sepref_frame_match_rules]:
  assumes "hn_ctxt A (fst x) (fst y) \<turnstile> hn_ctxt A' (fst x) (fst y)"
  assumes "hn_ctxt B (snd x) (snd y) \<turnstile> hn_ctxt B' (snd x) (snd y)"
  shows "hn_ctxt (prod_assn A B) x y \<turnstile> hn_ctxt (prod_assn A' B') x y"
  apply (cases x; cases y; simp)
  apply (simp add: hn_ctxt_def)
  apply (rule conj_entails_mono)
  using assms apply (auto simp: hn_ctxt_def)
  done

lemma prod_frame_merge[sepref_frame_merge_rules]:
  assumes "MERGE1 A frl1 A' frr1 Am"  
  assumes "MERGE1 B frl2 B' frr2 Bm"  
  shows "MERGE1 
    (prod_assn A B) (\<lambda>(a,b). doM {frl1 a; frl2 b}) 
    (prod_assn A' B') (\<lambda>(a,b). doM {frr1 a; frr2 b}) 
    (prod_assn Am Bm)"
  supply [vcg_rules] = MERGE1D[OF assms(1)] MERGE1D[OF assms(2)]
  by rule vcg
    
  

lemma entt_invalid_prod: "hn_invalid (prod_assn A B) p p' \<turnstile> hn_ctxt (prod_assn (invalid_assn A) (invalid_assn B)) p p'"
  unfolding hn_ctxt_def invalid_assn_def prod_assn_def
  by (auto split: prod.splits simp: entails_def pred_lift_extract_simps dest: pure_part_split_conj)

lemma gen_merge_cons_left: "L\<turnstile>L' \<Longrightarrow> MERGE L' fl R fr M \<Longrightarrow> MERGE L fl R fr M"  
  unfolding MERGE_def 
  by (metis (mono_tags, lifting) cons_rule[where Q=Q and Q'=Q for Q] entails_def)
  
lemma gen_merge_cons_right: "R\<turnstile>R' \<Longrightarrow> MERGE L fl R' fr M \<Longrightarrow> MERGE L fl R fr M"  
  unfolding MERGE_def
  by (metis (mono_tags, lifting) cons_rule[where Q=Q and Q'=Q for Q] entails_def)
  
lemmas gen_merge_cons = gen_merge_cons_left gen_merge_cons_right

lemmas invalid_prod_merge[sepref_frame_merge_rules] = gen_merge_cons[OF entt_invalid_prod]

lemma prod_assn_ctxt: "prod_assn A1 A2 x y = z \<Longrightarrow> hn_ctxt (prod_assn A1 A2) x y = z"
  by (simp add: hn_ctxt_def)

(* TODO: Move *)  
lemma drop_pureD: "is_pure A \<Longrightarrow> hn_ctxt A a b \<turnstile> \<box>"
  by (auto simp: is_pure_def entails_def pred_lift_extract_simps hn_ctxt_def)
  

lemma hn_case_prod_aux:
  assumes FR: "\<Gamma> \<turnstile> hn_ctxt (prod_assn P1 P2) p' p ** \<Gamma>1"
  assumes Pair: "\<And>a1 a2 a1' a2'. \<lbrakk>p'=(a1',a2')\<rbrakk> 
    \<Longrightarrow> hn_refine (hn_ctxt P1 a1' a1 ** hn_ctxt P2 a2' a2 ** \<Gamma>1 ** hn_invalid (prod_assn P1 P2) p' p) (f a1 a2) 
          (hn_ctxt P1' a1' a1 ** hn_ctxt P2' a2' a2 ** hn_ctxt XX1 p' p ** \<Gamma>1') R (f' a1' a2')"
  assumes PURE: "Sepref_Basic.is_pure XX1"
  shows "hn_refine \<Gamma> (case_prod f p) (hn_ctxt (prod_assn P1' P2') p' p ** \<Gamma>1')
    R (case_prod f' p')" (is "?G \<Gamma>")
    apply1 (rule hn_refine_cons_pre[OF FR])
    apply1 extract_hnr_invalids
    apply1 (cases p; cases p'; simp add: prod_assn_pair_conv[THEN prod_assn_ctxt])
    apply (rule hn_refine_cons[OF _ Pair _ entails_refl])
    applyS (simp add: hn_ctxt_def)
    applyS simp
    using PURE apply (sep_drule drop_pureD[OF PURE])
    by (simp add: hn_ctxt_def sep_conj_ac)
  
    
    
lemma hn_case_prod'[sepref_comb_rules]:
  assumes FR: "\<Gamma> \<turnstile> hn_ctxt (prod_assn P1 P2) p' p ** \<Gamma>1"
  assumes Pair: "\<And>a1 a2 a1' a2'. \<lbrakk>p'=(a1',a2')\<rbrakk> 
    \<Longrightarrow> hn_refine (hn_ctxt P1 a1' a1 ** hn_ctxt P2 a2' a2 ** \<Gamma>1 ** hn_invalid (prod_assn P1 P2) p' p) (f a1 a2) 
          (\<Gamma>2 a1 a2 a1' a2') R (f' a1' a2')"
  assumes FR2: "\<And>a1 a2 a1' a2'. \<Gamma>2 a1 a2 a1' a2' \<turnstile> hn_ctxt P1' a1' a1 ** hn_ctxt P2' a2' a2 ** hn_ctxt XX1 p' p ** \<Gamma>1'"        
  assumes PURE: "CONSTRAINT Sepref_Basic.is_pure XX1"
  shows "hn_refine \<Gamma> (case_prod f p) (hn_ctxt (prod_assn P1' P2') p' p ** \<Gamma>1')
    R (case_prod$(\<lambda>\<^sub>2a b. f' a b)$p')" (is "?G \<Gamma>")
    unfolding autoref_tag_defs PROTECT2_def
    apply (rule hn_case_prod_aux[OF _ hn_refine_cons_post])
    apply fact
    apply fact
    using FR2 apply blast
    using PURE by simp

lemma hn_Pair[sepref_fr_rules]: "(uncurry (return oo Pair), uncurry (RETURN oo Pair)) \<in> A\<^sup>d *\<^sub>a B\<^sup>d \<rightarrow>\<^sub>a A\<times>\<^sub>aB"    
  by sepref_to_hoare vcg
    
(*
lemma fst_hnr[sepref_fr_rules]: "(return o fst,RETURN o fst) \<in> (prod_assn A B)\<^sup>d \<rightarrow>\<^sub>a A"
  by sepref_to_hoare vcg
lemma snd_hnr[sepref_fr_rules]: "(return o snd,RETURN o snd) \<in> (prod_assn A B)\<^sup>d \<rightarrow>\<^sub>a B"
  by sepref_to_hoare sep_auto
*)

lemmas [constraint_simps] = prod_assn_pure_conv
lemmas [sepref_import_param] = param_prod_swap

lemma rdomp_prodD[dest!]: "rdomp (prod_assn A B) (a,b) \<Longrightarrow> rdomp A a \<and> rdomp B b"
  unfolding rdomp_def prod_assn_def
  by (auto simp: sep_conj_def)

subsection \<open>Option\<close>  

   
lemma option_patterns[def_pat_rules]: 
  "(=)$x$None \<equiv> is_None$x"
  "(=)$None$x \<equiv> is_None$x"
  "op_neq$x$None \<equiv> Not$(is_None$x)"
  "op_neq$None$x \<equiv> Not$(is_None$x)"
  apply (all \<open>rule eq_reflection\<close>)
  by (auto split: option.splits)

  
text \<open>Option type via unused implementation value\<close>  
locale dflt_option =   
  fixes dflt and A :: "'a \<Rightarrow> 'c::llvm_rep \<Rightarrow> assn" and is_dflt
  assumes UU: "A a dflt = sep_false"
  assumes CMP: "llvm_htriple \<box> (is_dflt k) (\<lambda>r. \<upharpoonleft>bool.assn (k=dflt) r)"
begin
  
  definition "option_assn a c \<equiv> if c=dflt then \<up>(a=None) else EXS aa. \<up>(a=Some aa) ** A aa c"
  
  lemma hn_None[sepref_fr_rules]: "(uncurry0 (return dflt), uncurry0 (RETURN None)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a option_assn"  
    apply sepref_to_hoare unfolding option_assn_def 
    apply vcg'
    done
  
  lemma hn_Some[sepref_fr_rules]: "(return, RETURN o Some) \<in> A\<^sup>d \<rightarrow>\<^sub>a option_assn"  
    apply sepref_to_hoare
    subgoal for a c
      apply (cases "c=dflt")
      using UU apply simp
      unfolding option_assn_def
      apply vcg
      done
    done
  
  lemma hn_the[sepref_fr_rules]: "(return, RETURN o the) \<in> [\<lambda>x. x \<noteq> None]\<^sub>a option_assn\<^sup>d \<rightarrow> A"
    apply sepref_to_hoare
    unfolding option_assn_def 
    apply clarsimp
    apply vcg'
    done
    
  lemma hn_is_None[sepref_fr_rules]: "(is_dflt, RETURN o is_None) \<in> option_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
    unfolding bool1_rel_def bool.assn_is_rel[symmetric]
    apply sepref_to_hoare
    unfolding option_assn_def 
    apply clarsimp
    supply CMP[vcg_rules]
    apply vcg'
    done
    
  definition [llvm_inline]: "free_option fr c \<equiv> doM { d\<leftarrow>is_dflt c; llc_if d (return ()) (fr c) }"
    
  lemma mk_free_option[sepref_frame_free_rules]:
    assumes [THEN MK_FREED, vcg_rules]: "MK_FREE A fr"  
    shows "MK_FREE option_assn (free_option fr)"
    apply rule
    unfolding free_option_def option_assn_def
    apply clarsimp
    supply CMP[vcg_rules]
    apply vcg
    done
    
  lemma option_assn_pure[safe_constraint_rules]:
    assumes "is_pure A" 
    shows "is_pure option_assn"  
  proof -
    from assms obtain P where [simp]: "A = (\<lambda>a c. \<up>(P a c))"
      unfolding is_pure_def by blast
  
    show ?thesis  
      apply (rule is_pureI[where P'="\<lambda>a c. if c=dflt then a=None else \<exists>aa. a=Some aa \<and> P aa c"])
      unfolding option_assn_def
      by (auto simp: sep_algebra_simps pred_lift_extract_simps)
      
  qed    
    
    
end    

locale dflt_pure_option = dflt_option +
  assumes A_pure[safe_constraint_rules]: "is_pure A"
begin
  find_theorems MK_FREE is_pure

  lemma A_free[sepref_frame_free_rules]: "MK_FREE A (\<lambda>_. return ())"
    by (rule mk_free_is_pure[OF A_pure])

end  


interpretation snat: dflt_pure_option "-1" snat_assn "ll_icmp_eq (-1)"
  apply unfold_locales
  subgoal
    apply (auto simp: snat_rel_def pure_def pred_lift_extract_simps del: ext intro!: ext)
    apply (auto simp: snat.rel_def in_br_conv snat_invar_def)
    done
  subgoal proof goal_cases
    case 1
    interpret llvm_prim_arith_setup .
    show ?case
      unfolding bool.assn_def
      apply vcg'
      done
    qed
  subgoal by simp  
  done

abbreviation snat_option_assn' :: "'a itself \<Rightarrow> nat option \<Rightarrow> 'a::len2 word \<Rightarrow> llvm_amemory \<Rightarrow> bool" where
  "snat_option_assn' _ \<equiv> snat.option_assn"
  
  
subsection \<open>Additional Operations\<close>  

text \<open>Additional operations, for which we need the basic framework already set up.\<close>
  
subsubsection \<open>Subtraction that Saturates at 0 on Underflow\<close>  
  
definition op_nat_sub_ovf :: "nat \<Rightarrow> nat \<Rightarrow> nat" where "op_nat_sub_ovf a b \<equiv> if a\<le>b then 0 else a-b"
lemma op_nat_sub_ovf_is_sub[simp]: "op_nat_sub_ovf = (-)"
  unfolding op_nat_sub_ovf_def by (auto split: if_split del: ext intro!: ext)

lemma fold_nat_sub_ovf: "(-) = op_nat_sub_ovf" by simp
  
sepref_definition snat_sub_ovf_impl [llvm_inline] is "uncurry (RETURN oo op_nat_sub_ovf)" 
  :: "(snat_assn' TYPE('l::len2))\<^sup>k *\<^sub>a (snat_assn' TYPE('l::len2))\<^sup>k \<rightarrow>\<^sub>a snat_assn' TYPE('l::len2)"
  unfolding op_nat_sub_ovf_def 
  apply (annot_snat_const "TYPE('l)")
  by sepref
  
declare snat_sub_ovf_impl.refine[sepref_fr_rules]
  
  
  
  
  
    


subsection \<open>Ad-Hoc Regression Tests\<close>  
  
sepref_definition example1 is "\<lambda>x. ASSERT (x\<in>{-10..10}) \<then> 
    RETURN (x<5 \<and> x\<noteq>2 \<longrightarrow> x-2 \<noteq> 0)" :: "(sint_assn' TYPE(7))\<^sup>k \<rightarrow>\<^sub>a (bool1_assn)" 
  supply [simp] = min_sint_def max_sint_def
  apply (annot_sint_const "TYPE(7)")
  apply sepref_dbg_keep
  done

sepref_definition example2 is "\<lambda>x. ASSERT (x\<in>{-10..10}) \<then> RETURN (x+(-1) * (7 smod 15) - 3 sdiv 2)" :: "(sint_assn' TYPE(7))\<^sup>k \<rightarrow>\<^sub>a (sint_assn' TYPE(7))" 
  supply [simp] = min_sint_def max_sint_def
  apply (annot_sint_const "TYPE(7)")
  apply sepref_dbg_keep
  done

sepref_definition example1n is "\<lambda>x. ASSERT (x\<in>{2..10}) \<then> 
    RETURN (x<5 \<and> x\<noteq>2 \<longrightarrow> x-2 \<noteq> 0)" :: "(snat_assn' TYPE(7))\<^sup>k \<rightarrow>\<^sub>a (bool1_assn)" 
  supply [simp] = max_snat_def
  apply (annot_snat_const "TYPE(7)")
  apply sepref_dbg_keep
  done

sepref_definition example2n is "\<lambda>x. ASSERT (x\<in>{5..10}) \<then> RETURN ((x-1) * (7 mod 15) - 3 div 2)" 
  :: "(snat_assn' TYPE(7))\<^sup>k \<rightarrow>\<^sub>a (snat_assn' TYPE(7))" 
  supply [simp] = max_snat_def
  apply (annot_snat_const "TYPE(7)")
  apply sepref_dbg_keep
  done
  
      
lemmas [llvm_code] = example1_def example2_def example1n_def example2n_def  
  
llvm_deps example1 example2 example1n example2n

export_llvm example1 example2 example1n example2n
  

definition example3_abs :: "'a::len word \<Rightarrow> 'a word \<Rightarrow> 'a word nres" where "example3_abs a b \<equiv> do {
    (a,b) \<leftarrow> WHILET (\<lambda>(a,b). a\<noteq>b) (\<lambda>(a,b). if a<b then RETURN (a,b-a) else RETURN (a-b,b)) (a,b);
    RETURN a
  }"

sepref_definition example3 is "uncurry example3_abs" :: "word_assn\<^sup>k *\<^sub>a word_assn\<^sup>k \<rightarrow>\<^sub>a word_assn"
  unfolding example3_abs_def
  apply sepref_dbg_keep
  done

definition example3n_abs :: "nat \<Rightarrow> nat \<Rightarrow> nat nres" where "example3n_abs a b \<equiv> do {
    (a,b) \<leftarrow> WHILET (\<lambda>(a,b). a\<noteq>b) (\<lambda>(a,b). if a<b then RETURN (a,b-a) else RETURN (a-b,b)) (a,b);
    RETURN a
  }"

sepref_definition example3n is "uncurry example3n_abs" :: "(snat_assn' TYPE(32))\<^sup>k *\<^sub>a (snat_assn' TYPE(32))\<^sup>k \<rightarrow>\<^sub>a (snat_assn' TYPE(32))"
  unfolding example3n_abs_def
  apply sepref_dbg_keep
  done
  
  
    
lemmas [llvm_code] = example3_def example3n_def  
export_llvm
  "example3 :: 32 word \<Rightarrow> _"
  "example3 :: 64 word \<Rightarrow> _"
  "example3n"


(* TODO: Characters as i8 *)  
  
end
