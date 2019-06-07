theory Sep_Generic_Wp
imports 
  "../lib/Sep_Algebra_Add" 
  "../lib/Frame_Infer"
  "../lib/Monad"
begin

section \<open>General VCG Setup for Separation Logic\<close>

(* TODO: Move to Library *)

locale generic_wp_defs =
  fixes wp :: "'c \<Rightarrow> ('r \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> 's \<Rightarrow> bool"
begin
  definition "htripleF \<alpha> F P c Q \<equiv> (\<forall>s. (P**F) (\<alpha> s) \<longrightarrow>
      wp c (\<lambda>r s'. (Q r ** F) (\<alpha> s')) s)"

  definition "htriple \<alpha> P c Q \<equiv> (\<forall>F s. (P**F) (\<alpha> s) \<longrightarrow>
      wp c (\<lambda>r s'. (Q r ** F) (\<alpha> s')) s)"

  lemma htriple_as_F_eq: "htriple \<alpha> P c Q = (\<forall>F. htripleF \<alpha> F P c Q)"    
    unfolding htriple_def htripleF_def by blast
      
end


locale generic_wp = generic_wp_defs wp
  for wp :: "'c \<Rightarrow> ('r \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> 's \<Rightarrow> bool" +
  assumes wp_mono: "Q\<le>Q' \<Longrightarrow> wp c Q \<le> wp c Q'"
begin

  lemma wp_monoI:
    assumes "wp c Q s"
    assumes "\<And>r x. Q r x \<Longrightarrow> Q' r x"
    shows "wp c Q' s"
    using assms wp_mono[of Q Q' c] by auto
      
  lemma htripleI:     
    assumes "\<And>F s. (P**F) (\<alpha> s) \<Longrightarrow> wp c (\<lambda>r s'. (Q r ** F) (\<alpha> s')) s"
    shows "htriple \<alpha> P c Q"
    using assms by (auto simp: htriple_def)

  lemma htripleFI:     
    assumes "\<And>s. (P**F) (\<alpha> s) \<Longrightarrow> wp c (\<lambda>r s'. (Q r ** F) (\<alpha> s')) s"
    shows "htripleF \<alpha> F P c Q"
    using assms by (auto simp: htripleF_def)
        
  lemma htripleD:  
    assumes "htriple \<alpha> P c Q"
    assumes "(P**F) (\<alpha> s)"
    shows "wp c (\<lambda>r s'. (Q r ** F) (\<alpha> s')) s"
    using assms by (auto simp: htriple_def)
    
  lemma htriple_triv[simp, intro!]: "htriple \<alpha> sep_false c Q"
    by (auto simp: htriple_def)
      
  lemma frame_rule: "htriple \<alpha> P c Q \<Longrightarrow> htriple \<alpha> (P ** F) c (\<lambda>r. Q r ** F)"
    unfolding htriple_def
    by (fastforce)

  lemma cons_rule:
    assumes "htriple \<alpha> P c Q"
    assumes "\<And>s. P' s \<Longrightarrow> P s"
    assumes "\<And>r s. Q r s \<Longrightarrow> Q' r s"
    shows "htriple \<alpha> P' c Q'"
    unfolding htriple_def
  proof clarsimp
    fix F s
    assume "(P' \<and>* F) (\<alpha> s)"
    with assms(2) have "(P \<and>* F) (\<alpha> s)"
      using sep_conj_impl1 by blast
    with assms(1) have "wp c (\<lambda>r s'. (Q r \<and>* F) (\<alpha> s')) s"
      unfolding htriple_def by auto
    thus "wp c (\<lambda>r s'. (Q' r \<and>* F) (\<alpha> s')) s"
      apply (rule wp_monoI)
      using assms(3)
      using sep_conj_impl1 by blast
  qed

  lemma cons_post_rule:
    assumes "htriple \<alpha> P c Q"
    assumes "\<And>r s. Q r s \<Longrightarrow> Q' r s"
    shows "htriple \<alpha> P c Q'"
    using cons_rule assms by blast
  
  
  lemma htriple_alt:
    "htriple \<alpha> P c Q 
      = (\<forall>p s f. p##f \<and> \<alpha> s = p + f \<and> P p \<longrightarrow> wp c (\<lambda>r s'. \<exists>p'. p'##f \<and> \<alpha> s'=p'+f \<and> Q r p') s)"
  proof (rule iffI, goal_cases)
    case 1
    show ?case
      using htripleD[OF 1, where F="EXACT x" for x]
        by (auto simp: sep_conj_def)
    
  next
    case 2
    show ?case proof (rule htripleI)
      fix F s 
      assume "(P \<and>* F) (\<alpha> s)"
      then obtain p f where "p##f" "P p" "F f" "\<alpha> s = p+f"
        by (blast elim: sep_conjE)
      with 2 have "wp c (\<lambda>r s'. \<exists>p'. p' ## f \<and> \<alpha> s' = p' + f \<and> Q r p') s" by blast
      then show "wp c (\<lambda>r s'. (Q r \<and>* F) (\<alpha> s')) s"
        apply (rule wp_monoI)
        using \<open>F f\<close> by (auto intro: sep_conjI)
    qed
  qed
  
  lemma htripleI': 
    assumes "\<And>p s f. \<lbrakk> p##f; \<alpha> s = p + f; P p\<rbrakk> \<Longrightarrow> wp c (\<lambda>r s'. \<exists>p'. p'##f \<and> \<alpha> s'=p'+f \<and> Q r p') s"
    shows "htriple \<alpha> P c Q"
    using assms by (auto simp: htriple_alt)

  lemma htripleD': 
    assumes "htriple \<alpha> P c Q"
    assumes "p##f" "\<alpha> s = p + f" "P p"
    shows "wp c (\<lambda>r s'. \<exists>p'. p'##f \<and> \<alpha> s'=p'+f \<and> Q r p') s"
    using assms by (auto simp: htriple_alt)
        
    
    
  lemma htriple_extract_pre_pure: 
    "htriple \<alpha> (\<up>\<Phi>**P) c Q \<longleftrightarrow> \<Phi> \<longrightarrow> htriple \<alpha> P c Q"  
    by (cases \<Phi>) (auto simp: sep_algebra_simps)
    
  (*
  lemma htriple_extract_pre_EXS: 
    assumes "\<And>x s. \<Phi> x \<Longrightarrow> P s \<Longrightarrow> f x ## s"
    shows "htriple \<alpha> (EXS x. \<up>\<Phi> x ** EXACT (f x) ** P) c Q \<longleftrightarrow> (\<exists>x. \<Phi> x \<and> htriple \<alpha> (EXACT (f x) ** P) c Q)"
    apply rule
  *)  
    
  thm htripleD
  
  thm option.simps
  
  lemma sv_htripleD:
    assumes "htriple \<alpha> P c Q"
    assumes "(P**F) (\<alpha> s)"
    assumes "\<And>r s. (Q r ** F) (\<alpha> s) \<Longrightarrow> Q' r s"
    shows "wp c Q' s"
    using assms 
    by (force simp: htriple_def intro: wp_monoI)
  
  lemma sv_htripleFD:
    assumes "htripleF \<alpha> F P c Q"
    assumes "(P**F) (\<alpha> s)"
    assumes "\<And>r s. (Q r ** F) (\<alpha> s) \<Longrightarrow> Q' r s"
    shows "wp c Q' s"
    using assms 
    by (force simp: htripleF_def intro: wp_monoI)
    
    
end



definition STATE :: "('s \<Rightarrow> 'a::sep_algebra) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> 's \<Rightarrow> bool" 
  where "STATE \<alpha> P s \<equiv> P (\<alpha> s)"

lemma STATE_assn_cong[fri_extract_congs]: "P\<equiv>P' \<Longrightarrow> STATE \<alpha> P s \<equiv> STATE \<alpha> P' s" by simp
  
lemma STATE_extract[vcg_normalize_simps]:
  "STATE \<alpha> (\<up>\<Phi>) h \<longleftrightarrow> \<Phi> \<and> STATE \<alpha> \<box> h"
  "STATE \<alpha> (\<up>\<Phi> ** P) h \<longleftrightarrow> \<Phi> \<and> STATE \<alpha> P h"
  "STATE \<alpha> (EXS x. Q x) h \<longleftrightarrow> (\<exists>x. STATE \<alpha> (Q x) h)"
  "STATE \<alpha> (\<lambda>_. False) h \<longleftrightarrow> False"
  "STATE \<alpha> ((\<lambda>_. False) ** P) h \<longleftrightarrow> False"
  by (auto simp: STATE_def sep_algebra_simps pred_lift_extract_simps)
 

definition POSTCOND :: "('s \<Rightarrow> 'a::sep_algebra) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> 's \<Rightarrow> bool" 
  where [vcg_tag_defs]: "POSTCOND \<alpha> \<equiv> STATE \<alpha>"
  
lemma POSTCONDI:
  "STATE \<alpha> A h \<Longrightarrow> POSTCOND \<alpha> A h"
  by (auto simp add: POSTCOND_def)
lemma POSTCOND_cong[vcg_normalize_congs]: "POSTCOND \<alpha> A = POSTCOND \<alpha> A" ..

lemma POSTCOND_triv_simps[vcg_normalize_simps]:
  "POSTCOND \<alpha> sep_true h"
  "\<not>POSTCOND \<alpha> sep_false h"
  unfolding POSTCOND_def STATE_def by auto
  
lemma start_entailsE:
  assumes "STATE \<alpha> P h"
  assumes "ENTAILS P P'"
  shows "STATE \<alpha> P' h"
  using assms unfolding STATE_def ENTAILS_def entails_def
  by auto

declaration \<open>
  K (Basic_VCG.add_xformer (@{thms POSTCONDI},@{binding postcond_xformer},
    fn ctxt => eresolve_tac ctxt @{thms start_entailsE}
  ))
\<close>


named_theorems htriple_vcg_intros
named_theorems htriple_vcg_intro_congs
definition [vcg_tag_defs]: "DECOMP_HTRIPLE \<phi> \<equiv> \<phi>"
lemma DECOMP_HTRIPLEI: "\<phi> \<Longrightarrow> DECOMP_HTRIPLE \<phi>" unfolding vcg_tag_defs by simp

 
context generic_wp begin
  thm frame_rule
  thm cons_rule  
    
  lemma htriple_vcg_frame_erule[vcg_frame_erules]:
    assumes S: "STATE \<alpha> P' s"
    assumes F: "PRECOND (FRAME P' P F)"
    assumes HT: "htriple \<alpha> P c Q"  
    assumes P: "\<And>r s. STATE \<alpha> (Q r ** F) s \<Longrightarrow> PRECOND (EXTRACT (Q' r s))"
    shows "wp c Q' s"
  proof -
    from S F have "(P \<and>* F) (\<alpha> s)"
      unfolding vcg_tag_defs
      by (metis (no_types) FRAME_def entails_def STATE_def)
    with P show ?thesis
      unfolding vcg_tag_defs
      by (metis (no_types) STATE_def sv_htripleD[OF HT])
      
  qed

  lemma htripleF_vcg_frame_erule[vcg_frame_erules]:
    assumes S: "STATE \<alpha> P' s"
    assumes F: "PRECOND (FRAME P' P F)"
    assumes HT: "htripleF \<alpha> F P c Q"  
    assumes P: "\<And>r s. STATE \<alpha> (Q r ** F) s \<Longrightarrow> PRECOND (EXTRACT (Q' r s))"
    shows "wp c Q' s"
  proof -
    from S F have "(P \<and>* F) (\<alpha> s)"
      unfolding vcg_tag_defs
      by (metis (no_types) FRAME_def entails_def STATE_def)
    with P show ?thesis
      unfolding vcg_tag_defs
      by (metis (no_types) STATE_def sv_htripleFD[OF HT])
      
  qed
  
  
  
  lemma htriple_vcgI': 
    assumes "\<And>F s. STATE \<alpha> (P**F) s \<Longrightarrow> wp c (\<lambda>r. POSTCOND \<alpha> (Q r ** F)) s"
    shows "htriple \<alpha> P c Q"
    apply (rule htripleI)
    using assms unfolding vcg_tag_defs STATE_def .
  
  lemma htriple_vcgI[htriple_vcg_intros]: 
    assumes "\<And>F s. STATE \<alpha> (P**F) s \<Longrightarrow> EXTRACT (wp c (\<lambda>r. POSTCOND \<alpha> (Q r ** F)) s)"
    shows "htriple \<alpha> P c Q"
    apply (rule htripleI)
    using assms unfolding vcg_tag_defs STATE_def .

  lemma htripleF_vcgI[htriple_vcg_intros]: 
    assumes "\<And>s. STATE \<alpha> (P**F) s \<Longrightarrow> EXTRACT (wp c (\<lambda>r. POSTCOND \<alpha> (Q r ** F)) s)"
    shows "htripleF \<alpha> F P c Q"
    apply (rule htripleFI)
    using assms unfolding vcg_tag_defs STATE_def .
    
      
  lemma htriple_decompI[vcg_decomp_rules]: 
    "DECOMP_HTRIPLE (htriple \<alpha> P c Q) \<Longrightarrow> htriple \<alpha> P c Q"
    "DECOMP_HTRIPLE (htripleF \<alpha> F P c Q) \<Longrightarrow> htripleF \<alpha> F P c Q"
    unfolding vcg_tag_defs by auto

  lemma htriple_assn_cong[htriple_vcg_intro_congs]: 
    "P\<equiv>P' \<Longrightarrow> Q\<equiv>Q' \<Longrightarrow>  htriple \<alpha> P c Q \<equiv> htriple \<alpha> P' c Q'" by simp

  lemma htripleF_assn_cong[htriple_vcg_intro_congs]: 
    "P\<equiv>P' \<Longrightarrow> Q\<equiv>Q' \<Longrightarrow>  htripleF \<alpha> F P c Q \<equiv> htripleF \<alpha> F P' c Q'" by simp
            
  lemma htriple_ent_pre:
    "P\<turnstile>P' \<Longrightarrow> htriple \<alpha> P' c Q \<Longrightarrow> htriple \<alpha> P c Q"
    unfolding entails_def
    apply (erule cons_rule) by blast+
    
  lemma htriple_ent_post:
    "\<lbrakk>\<And>r. Q r \<turnstile> Q' r\<rbrakk> \<Longrightarrow> htriple \<alpha> P c Q \<Longrightarrow> htriple \<alpha> P c Q'"
    unfolding entails_def
    apply (erule cons_rule) by blast+
   
  lemma htriple_pure_preI: "\<lbrakk>pure_part P \<Longrightarrow> htriple \<alpha> P c Q\<rbrakk> \<Longrightarrow> htriple \<alpha> P c Q"  
    by (meson htriple_def pure_partI sep_conjE)
    
     
end


declaration \<open>
  K (Basic_VCG.add_xformer (@{thms DECOMP_HTRIPLEI},@{binding decomp_htriple_xformer},
    fn ctxt => 
      (full_simp_tac (put_simpset HOL_basic_ss ctxt 
        addsimps (Named_Theorems.get ctxt @{named_theorems vcg_tag_defs})
        |> fold Simplifier.add_cong (Named_Theorems.get ctxt @{named_theorems htriple_vcg_intro_congs})
      ))
      THEN' resolve_tac ctxt (Named_Theorems.get ctxt @{named_theorems htriple_vcg_intros})
  ))
\<close>





section \<open>Setup for mres-Monad\<close>

  definition "wp c Q s \<equiv> mwp (run c s) bot bot bot Q"
  definition "wlp c Q s \<equiv> mwp (run c s) top top top Q"
  
  (* Definition for presentation in paper *)
  lemma "wp c Q s = (\<exists>r s'. run c s = SUCC r s' \<and> Q r s')"
    unfolding wp_def mwp_def by (auto split: mres.splits)
  
  
  lemma wlp_true[simp, intro!]: 
    "wlp c (\<lambda>_ _. True) s"
    "wlp c top s"
    by (auto simp: wlp_def mwp_def split: mres.splits)
  
  interpretation generic_wp wp 
    by unfold_locales (auto simp: wp_def elim!: mwp_cons) 

  lemma wp_return[vcg_normalize_simps]: "wp (return x) Q s \<longleftrightarrow> Q x s"  
    by (auto simp: wp_def run_simps)

  lemma wp_fail[vcg_normalize_simps]: "\<not> wp (fail x) Q s"  
    by (auto simp: wp_def run_simps)

  lemma wp_fcheck[vcg_normalize_simps]: "wp (fcheck e \<Phi>) Q s \<longleftrightarrow> \<Phi> \<and> Q () s"  
    by (auto simp: wp_def run_simps)
            
  lemma wp_bind[vcg_normalize_simps]: "wp (m\<bind>f) Q s = wp m (\<lambda>x. wp (f x) Q) s"  
    by (auto simp: wp_def run_simps)
    
    

  thm vcg_normalize_simps






end
