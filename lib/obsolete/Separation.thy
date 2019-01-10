*** obsolete
theory Separation
imports
  "Frame_Infer"
begin

lemmas [vcg_static_rl_simps] = sep_conj_assoc sep_conj_false_simps

locale conc_heap_defs =
  fixes \<alpha> :: "'h \<Rightarrow> 'a::sep_algebra"
  fixes I :: "'h \<Rightarrow> bool"
  fixes wp :: "'c \<Rightarrow> ('r \<Rightarrow> 'h \<Rightarrow> bool) \<Rightarrow> 'h \<Rightarrow> bool"

locale conc_heap = conc_heap_defs where \<alpha>=\<alpha> and I=I and wp=wp
  for \<alpha> :: "'h \<Rightarrow> 'a::sep_algebra"
  and I :: "'h \<Rightarrow> bool"
  and wp :: "'c \<Rightarrow> ('r \<Rightarrow> 'h \<Rightarrow> bool) \<Rightarrow> 'h \<Rightarrow> bool" +
  assumes wp_mono: "Q\<le>Q' \<Longrightarrow> wp c Q \<le> wp c Q'"
begin
  lemma wp_monoI:
    assumes "wp c Q h"
    assumes "\<And>r x. Q r x \<Longrightarrow> Q' r x"
    shows "wp c Q' h"
    using assms wp_mono[of Q Q' c] by auto

  definition (in conc_heap_defs) "has_rep s \<equiv> (\<exists>h f. I h \<and> s##f \<and> s+f = \<alpha> h)"

  subsection \<open>Hoare Triple\<close>

  definition (in conc_heap_defs) "htriple P c Q \<longleftrightarrow> (\<forall>F h. I h \<and> (P**F) (\<alpha> h) \<longrightarrow>
        wp c (\<lambda>r h'. I h' \<and> (Q r ** F) (\<alpha> h')) h)"

  lemma htriple_cong[vcg_normalize_congs]:
    "htriple P c Q = htriple P c Q" by simp

  lemma frame_rule: "htriple P c Q \<Longrightarrow> htriple (P ** F) c (\<lambda>r. Q r ** F)"
    unfolding htriple_def
    by (fastforce)

  lemma cons_rule:
    assumes "htriple P c Q"
    assumes "\<And>h. P' h \<Longrightarrow> P h"
    assumes "\<And>r h. Q r h \<Longrightarrow> Q' r h"
    shows "htriple P' c Q'"
    unfolding htriple_def
  proof clarsimp
    fix F h
    assume "I h" "(P' \<and>* F) (\<alpha> h)"
    with assms(2) have "(P \<and>* F) (\<alpha> h)"
      using sep_conj_impl1 by blast
    with assms(1) \<open>I h\<close> have "wp c (\<lambda>r h'. I h' \<and> (Q r \<and>* F) (\<alpha> h')) h"
      unfolding htriple_def by auto
    thus "wp c (\<lambda>r h'. I h' \<and> (Q' r \<and>* F) (\<alpha> h')) h"
      apply (rule wp_monoI)
      using assms(3)
      using sep_conj_impl1 by blast
  qed

  lemma cons_pre_rule:
    assumes "htriple P c Q"
    assumes "\<And>h. P' h \<Longrightarrow> P h"
    shows "htriple P' c Q"
    using assms by (blast intro: cons_rule)

  lemma cons_post_rule:
    assumes "htriple P c Q"
    assumes "\<And>r h. Q r h \<Longrightarrow> Q' r h"
    shows "htriple P c Q'"
    using assms by (blast intro: cons_rule)

  (* For use with frame solver *)
  lemma cons_rule':
    assumes "htriple P c Q"
    assumes "ENTAILS P' P"
    assumes "\<And>r. ENTAILS (Q r) (Q' r)"
    shows "htriple P' c Q'"
    apply (rule cons_rule)
    apply fact
    using assms(2-)
    by (auto simp: ENTAILS_def entails_def)

  lemma htriple_extract_pure:
    "htriple (\<up>\<Phi> ** P) c Q \<longleftrightarrow> (\<Phi> \<longrightarrow> htriple P c Q)"
    "htriple (\<up>\<Phi>) c Q \<longleftrightarrow> (\<Phi> \<longrightarrow> htriple \<box> c Q)"
    unfolding htriple_def by (auto simp: sep_algebra_simps pred_lift_extract_simps)


  subsection \<open>Garbage Collected Semantics\<close>

  definition (in conc_heap_defs) "htripleg P c Q \<longleftrightarrow> htriple P c (\<lambda>r. Q r ** sep_true)"

  lemma htriplegI: "htriple P c (\<lambda>r. Q r ** sep_true) \<Longrightarrow> htripleg P c Q"
    unfolding htripleg_def by simp

  lemma htripleg_by_htriple: "htriple P c Q \<Longrightarrow> htripleg P c Q"
    unfolding htriple_def htripleg_def
    apply (clarsimp)
    by (smt intuitionistic_sep_conj_sep_true intuitionistic_sep_impl_sep_true_simp sep_conj_sep_impl_sep_conj2 wp_monoI)

  lemma has_rep_sumI:
    assumes "x##y" "has_rep (x+y)"
    shows "has_rep x" "has_rep y"
    using assms apply -
    apply (clarsimp simp: has_rep_def sep_algebra_simps)
    apply (metis sep_add_left_commute sep_disj_addD1 sep_disj_addD2 sep_disj_addI2)
    by (smt has_rep_def sep_add_assoc sep_add_disjD sep_add_disjI1 sep_add_left_commute sep_disj_commuteI)

  lemma frame_ruleg: "htripleg P c Q \<Longrightarrow> htripleg (P ** F) c (\<lambda>r. Q r ** F)"
    unfolding htripleg_def htriple_def
    apply (simp)
    by (smt sep.mult.left_commute sep_conj_commute wp_monoI)



  lemma cons_ruleg:
    assumes "htripleg P c Q"
    assumes "\<And>s. \<lbrakk>P' s\<rbrakk> \<Longrightarrow> P s"
    assumes "\<And>r s. \<lbrakk>Q r s\<rbrakk> \<Longrightarrow> Q' r s"
    shows "htripleg P' c Q'"
    unfolding htripleg_def
    apply (rule cons_rule[OF assms(1)[unfolded htripleg_def]])
    apply fact
    using assms(3) by (simp add: sep_conj_impl)


  lemma cons_pre_ruleg:
    assumes "htripleg P c Q"
    assumes "\<And>s. \<lbrakk>P' s\<rbrakk> \<Longrightarrow> P s"
    shows "htripleg P' c Q"
    using assms by (blast intro: cons_ruleg)

  lemma cons_post_ruleg:
    assumes "htripleg P c Q"
    assumes "\<And>r s. \<lbrakk>Q r s\<rbrakk> \<Longrightarrow> Q' r s"
    shows "htripleg P c Q'"
    using assms by (blast intro: cons_ruleg)

  (* For use with frame solver *)
  lemma cons_ruleg':
    assumes "htripleg P c Q"
    assumes "ENTAILS P' P"
    assumes "\<And>r. ENTAILS (Q r) (Q' r)"
    shows "htripleg P' c Q'"
    apply (rule cons_ruleg)
    apply fact
    using assms(2-)
    by (auto simp: ENTAILS_def entails_def)

  lemma htripleg_extract_pure:
    "htripleg (\<up>\<Phi> ** P) c Q \<longleftrightarrow> (\<Phi> \<longrightarrow> htripleg P c Q)"
    "htripleg (\<up>\<Phi>) c Q \<longleftrightarrow> (\<Phi> \<longrightarrow> htripleg \<box> c Q)"
    unfolding htripleg_def by (auto simp: sep_algebra_simps htriple_extract_pure)


  subsection \<open>VCG Setup\<close>

  definition (in conc_heap_defs) STATE :: "('a \<Rightarrow> bool) \<Rightarrow> 'h \<Rightarrow> bool" where "STATE P h \<equiv> I h \<and> P (\<alpha> h)"
  lemma STATEI: "STATE P s \<Longrightarrow> STATE P s" .
  lemma STATE_cong: "s=s' \<Longrightarrow> STATE P s = STATE P s'" by simp

  lemma STATE_extract[vcg_normalize_simps]:
    "STATE (\<up>\<Phi>) h \<longleftrightarrow> \<Phi> \<and> STATE \<box> h"
    "STATE (\<up>\<Phi> ** P) h \<longleftrightarrow> \<Phi> \<and> STATE P h"
    "STATE (EXS x. Q x) h \<longleftrightarrow> (\<exists>x. STATE (Q x) h)"
    "STATE (\<lambda>_. False) h \<longleftrightarrow> False"
    "STATE ((\<lambda>_. False) ** P) h \<longleftrightarrow> False"
    by (auto simp: STATE_def sep_algebra_simps pred_lift_extract_simps)

  lemma STATE_false: "STATE (\<lambda>_. False) h = False" by (auto simp: STATE_def)

  lemma STATE_apply_FRAME: "STATE P h \<Longrightarrow> FRAME P Q F \<Longrightarrow> STATE (Q**F) h"
    unfolding STATE_def FRAME_def entails_def
    by blast


  lemma STATE_monoI: "STATE P s \<Longrightarrow> P\<turnstile>Q \<Longrightarrow> STATE Q s"
    by (auto simp: STATE_def entails_def)

  lemma STATE_monoI': "STATE P s \<Longrightarrow> ENTAILS P Q \<Longrightarrow> STATE Q s"
    by (auto simp: STATE_def entails_def ENTAILS_def)


end

definition POSTCOND where [vcg_tag_defs]:
  "POSTCOND \<alpha> I \<equiv> conc_heap_defs.STATE \<alpha> I"
lemma POSTCONDI:
  "conc_heap_defs.STATE \<alpha> I A h \<Longrightarrow> POSTCOND \<alpha> I A h"
  by (auto simp add: POSTCOND_def)
lemma POSTCOND_cong[vcg_normalize_congs]: "POSTCOND \<alpha> I A = POSTCOND \<alpha> I A" ..

lemma POSTCOND_triv_simps[vcg_normalize_simps]:
  "conc_heap_defs.STATE \<alpha> I A h \<Longrightarrow> POSTCOND \<alpha> I sep_true h"
  "\<not>POSTCOND \<alpha> I sep_false h"
  unfolding POSTCOND_def conc_heap_defs.STATE_def by auto


lemma start_entailsE:
  assumes "conc_heap_defs.STATE \<alpha> I P h"
  assumes "ENTAILS P P'"
  shows "conc_heap_defs.STATE \<alpha> I P' h"
  using assms unfolding conc_heap_defs.STATE_def ENTAILS_def entails_def
  by auto

  declaration \<open>
    K (Basic_VCG.add_xformer (@{thms POSTCONDI},@{binding postcond_xformer},
      fn ctxt =>
        eresolve_tac ctxt @{thms start_entailsE}
    ))
  \<close>


context conc_heap begin
  abbreviation "POST \<equiv> POSTCOND \<alpha> I"

  lemma htriple_wpD[vcg_frame_erules]:
    assumes "STATE S h"
    assumes "PRECOND (FRAME S P F)"
    assumes "htriple P c Q"
    assumes "\<And>h' r. \<lbrakk> STATE (EXTRACT (Q r ** F)) h'\<rbrakk> \<Longrightarrow> PRECOND (EXTRACT (R r h'))"
    shows "wp c R h"
    (*using frame_rule[OF \<open>htriple P c Q\<close>, of F]*)
    using assms
    unfolding htriple_def vcg_tag_defs STATE_def FRAME_def entails_def
    by (fastforce elim: wp_monoI)


  lemma htripleg_wpD[vcg_frame_erules]:
    assumes "STATE S h"
    assumes "PRECOND (FRAME S P F)"
    assumes "htripleg P c Q"
    assumes "\<And>h' r. \<lbrakk> STATE (EXTRACT (Q r ** F ** sep_true)) h'\<rbrakk> \<Longrightarrow> PRECOND (EXTRACT (R r h'))"
    shows "wp c R h"
    apply (rule htriple_wpD[OF assms(1,2) assms(3)[unfolded htripleg_def]])
    using assms(4)
    unfolding vcg_tag_defs
    by (auto simp: sep_algebra_simps sep_conj_c)

  (* Prune rules for trivial cases. *)
  lemma htriple_wpD_prune_simps[vcg_static_rl_simps]:
    "EXTRACT sep_false = sep_false" (* TODO: Move *)
    "\<not> (STATE (sep_false) h')"
    by (auto simp add: STATE_def sep_algebra_simps vcg_tag_defs)

  lemma htriple_wpI[vcg_decomp_rules]:
    assumes "\<And>F h. \<lbrakk> (STATE (EXTRACT (P ** F)) h) \<rbrakk>
      \<Longrightarrow> EXTRACT (wp c (\<lambda>r h'. POST (Q r ** F) h') h)"
    shows "htriple P c Q"
    using assms
    unfolding STATE_def vcg_tag_defs htriple_def
    by auto

  lemma htripleg_wpI[vcg_decomp_rules]:
    assumes "\<And>F h. \<lbrakk> (STATE (EXTRACT (P ** F)) h) \<rbrakk>
      \<Longrightarrow> EXTRACT (wp c (\<lambda>r h'. POST (Q r ** F ** sep_true) h') h)"
    shows "htripleg P c Q"
    unfolding htripleg_def
    apply (rule htriple_wpI)
    unfolding vcg_tag_defs
    apply (erule wp_monoI[OF assms[unfolded vcg_tag_defs]])
    unfolding STATE_def
    by (auto simp: sep_algebra_simps sep_conj_c)

  lemma htriple_wp_no_frameD:
    assumes "STATE P h"
    assumes "htriple P c Q"
    assumes "\<And>h' r. \<lbrakk> (STATE (EXTRACT (Q r)) h')\<rbrakk> \<Longrightarrow> PRECOND (EXTRACT (R r h'))"
    shows "wp c R h"
    using htriple_wpD[OF assms(1) _ assms(2), of \<box> R] assms(3)
    by (simp add: FRAME_def vcg_tag_defs)

  lemma htripleg_wp_no_frameD:
    assumes "STATE P h"
    assumes "htripleg P c Q"
    assumes "\<And>h' r. \<lbrakk> (STATE (EXTRACT (Q r ** sep_true)) h')\<rbrakk> \<Longrightarrow> PRECOND (EXTRACT (R r h'))"
    shows "wp c R h"
    using htripleg_wpD[OF assms(1) _ assms(2), of \<box> R] assms(3)
    by (simp add: FRAME_def vcg_tag_defs)

end


end
