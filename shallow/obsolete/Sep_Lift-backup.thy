theory Sep_Lift
imports "../lib/Sep_Algebra_Add" "../lib/Monad" "HOL-Library.Rewrite"
begin

  locale generic_wp =
    fixes wp :: "'c \<Rightarrow> ('r \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> 's \<Rightarrow> bool"
    assumes wp_mono: "Q\<le>Q' \<Longrightarrow> wp c Q \<le> wp c Q'"
  begin
  
    lemma wp_monoI:
      assumes "wp c Q s"
      assumes "\<And>r x. Q r x \<Longrightarrow> Q' r x"
      shows "wp c Q' s"
      using assms wp_mono[of Q Q' c] by auto
        
    definition "htriple \<alpha> P c Q \<equiv> (\<forall>F s. (P**F) (\<alpha> s) \<longrightarrow>
        wp c (\<lambda>r s'. (Q r ** F) (\<alpha> s')) s)"
  
    lemma htripleI:     
      assumes "\<And>F s. (P**F) (\<alpha> s) \<Longrightarrow> wp c (\<lambda>r s'. (Q r ** F) (\<alpha> s')) s"
      shows "htriple \<alpha> P c Q"
      using assms by (auto simp: htriple_def)
      
    lemma htripleD:  
      assumes "htriple \<alpha> P c Q"
      assumes "(P**F) (\<alpha> s)"
      shows "wp c (\<lambda>r s'. (Q r ** F) (\<alpha> s')) s"
      using assms by (auto simp: htriple_def)
      
        
        
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
          
  end

  definition "wp c Q s \<equiv> mwp (run c s) bot bot bot Q"
  
  interpretation generic_wp wp 
    by unfold_locales (auto simp: wp_def elim!: mwp_cons) 
   
    
  record ('asmall,'csmall,'abig,'cbig) sep_lifter =
    lift :: "'asmall::unique_zero_sep_algebra \<Rightarrow> 'abig::unique_zero_sep_algebra"  
    project :: "'abig \<Rightarrow> 'asmall"
    
    L :: "'csmall \<Longrightarrow> 'cbig"
    \<alpha>b :: "('csmall \<Rightarrow> 'asmall) \<Rightarrow> 'cbig \<Rightarrow> 'abig"
    
  hide_const (open) lift project L \<alpha>b  

  locale pre_sep_lifter = 
    fixes LFT :: "('asmall::unique_zero_sep_algebra,'csmall,'abig::unique_zero_sep_algebra,'cbig) sep_lifter"
  begin
    abbreviation lift where "lift \<equiv> sep_lifter.lift LFT"
    abbreviation project where "project \<equiv> sep_lifter.project LFT"
    abbreviation L where "L \<equiv> sep_lifter.L LFT"
    abbreviation \<alpha>b where "\<alpha>b \<equiv> sep_lifter.\<alpha>b LFT"
  end  
  
      
  locale sep_lifter = pre_sep_lifter LFT 
    for LFT :: "('asmall::unique_zero_sep_algebra,'csmall,'abig::unique_zero_sep_algebra,'cbig) sep_lifter" +
      
    assumes lift_pres_zero[simp]: "lift 0 = 0" 
        and lift_add_distrib[simp]: "a\<^sub>1##a\<^sub>2 \<Longrightarrow> lift (a\<^sub>1+a\<^sub>2) = lift a\<^sub>1 + lift a\<^sub>2"
        and lift_disj_distrib[simp]: "lift a\<^sub>1 ## lift a\<^sub>2 \<longleftrightarrow> a\<^sub>1##a\<^sub>2"
    assumes project_pres_zero[simp]: "project 0 = 0"
        and project_add_distrib[simp]: "b\<^sub>1##b\<^sub>2 \<Longrightarrow> project (b\<^sub>1 + b\<^sub>2) = project b\<^sub>1 + project b\<^sub>2"
        and project_disj_distrib[simp]: "b\<^sub>1##b\<^sub>2 \<Longrightarrow> project b\<^sub>1 ## project b\<^sub>2"     
    assumes project_lift_id[simp]: "project (lift a) = a"
    assumes disj_project_imp_lift: "a ## project b \<Longrightarrow> lift a ## b"    
                
    assumes complete_split: "\<exists>b\<^sub>2. b = lift (project b) + b\<^sub>2 \<and> (project b\<^sub>2 = 0)"
    
    assumes lensL[simp, intro!]: "lens L"  
    assumes precond: "\<lbrakk>lift p ## f; \<alpha>b \<alpha>s cb = lift p + f; p\<noteq>0\<rbrakk> \<Longrightarrow> pre_get L cb \<and> pre_put L cb"
    assumes get_xfer: "\<lbrakk>lift p ## f; \<alpha>b \<alpha>s cb = lift p + f; p\<noteq>0; project f = 0\<rbrakk> \<Longrightarrow> \<alpha>s (get' L cb) = p"
    assumes put_xfer: "\<lbrakk>lift p ## f; \<alpha>b \<alpha>s cb = lift p + f; p\<noteq>0; project f = 0\<rbrakk> \<Longrightarrow> \<alpha>b \<alpha>s (put' L x cb) = lift (\<alpha>s x) + f"
    
  begin

    lemma "project (\<alpha>b \<alpha>s cb) \<noteq> 0 \<Longrightarrow> pre_get L cb"
      by (metis complete_split disj_project_imp_lift precond sep_disj_zero)

    lemma "project (\<alpha>b \<alpha>s cb) \<noteq> 0 \<Longrightarrow> \<alpha>s (get' L cb) = project (\<alpha>b \<alpha>s cb)"
      by (metis complete_split get_xfer sep_disj_zero sep_lifter.disj_project_imp_lift sep_lifter_axioms)
      
        
  
  
    lemma lift_eqZ_iffZ[simp]: "lift a = 0 \<longleftrightarrow> a=0"
      by (metis lift_pres_zero project_lift_id)
  
    
    lemma disj_project_eq_lift: 
      "a ## project b \<longleftrightarrow> lift a ## b"
      "project b ## a \<longleftrightarrow> b ## lift a"
      using disj_project_imp_lift project_disj_distrib apply fastforce
      by (metis disj_project_imp_lift project_disj_distrib project_lift_id sep_disj_commute)
  
    lemma proj_Z_imp_disj1:
      assumes "project b = 0"
      shows "lift a ## b"
      by (simp add: assms disj_project_imp_lift)
      
    lemmas proj_Z_imp_disj[simp] = proj_Z_imp_disj1 proj_Z_imp_disj1[THEN sep_disj_commuteI]  
      
    lemma splitE: obtains b\<^sub>2 where "b = lift (project b) + b\<^sub>2" "project b\<^sub>2 = 0"
      using complete_split by (fastforce simp: )

    lemma projectZ_add_distrib[simp]: 
      "b\<^sub>1##b\<^sub>2 \<Longrightarrow> project (b\<^sub>1 + b\<^sub>2) = 0 \<longleftrightarrow> project b\<^sub>1=0 \<and> project b\<^sub>2=0"  
      by (auto simp: )
      
    lemma lift_operation:
      assumes NZ: "\<not>P 0"
      assumes HT: "htriple \<alpha>s P c Q"
      shows "htriple (\<alpha>b \<alpha>s) (P o project) (zoom (lift_lens e L) c) (\<lambda>r. Q r o project)"
    proof (rule htripleI'; clarsimp)
      fix p s f
      assume A: "p ## f" "\<alpha>b \<alpha>s s = p + f" and "P (project p)"
      hence [simp]: "project p\<noteq>0" "p\<noteq>0" "p##f" "f##p" using NZ by (auto simp: sep_algebra_simps)

      from splitE[of p] obtain p\<^sub>2 where PEQ: "p = lift (project p) + p\<^sub>2" and [simp]: "project p\<^sub>2 = 0" .
      from splitE[of f] obtain f\<^sub>2 where FEQ: "f = lift (project f) + f\<^sub>2" and [simp]: "project f\<^sub>2 = 0" .
      
      have [simp]: "p\<^sub>2 ## f\<^sub>2" 
        by (metis A(1) FEQ PEQ \<open>project f\<^sub>2 = 0\<close> \<open>project p\<^sub>2 = 0\<close> proj_Z_imp_disj1 sep_add_disjD sep_disj_addD)
      hence [simp]: "f\<^sub>2 ## p\<^sub>2" by (rule sep_disj_commuteI) 
      
      from A have OFR: "\<alpha>b \<alpha>s s = lift (project p + project f) + (p\<^sub>2+f\<^sub>2)"
        apply (simp) 
        apply (rewrite in "\<hole> = _" PEQ)
        apply (rewrite in "\<hole> = _" FEQ)
        by (auto simp: sep_algebra_simps)
        
        
      note GET = get_xfer[OF _ OFR, simplified]
      note PUT = put_xfer[OF _ OFR, simplified]
      
      thm htripleD'
      
      note HT' = htripleD'[OF HT _ GET \<open>P (project p)\<close>, simplified]  
      note HT' = HT'[unfolded wp_def]
      
      from precond[OF _ OFR] have [simp]: "pre_get L s" "pre_put L s" by auto
      
      
      show "wp (zoom (lift_lens e L) c) (\<lambda>r s'. \<exists>p'. p' ## f \<and> \<alpha>b \<alpha>s s' = p' + f \<and> Q r (project p')) s"
        apply (auto simp: wp_def run_simps split: option.splits)
        apply (simp cong del: mwp_cong add: PUT)
        apply (rule mwp_cons[OF HT'])
        apply (clarsimp_all simp: )
        subgoal for x s' p'
          apply (intro exI[where x="lift p' + p\<^sub>2"] conjI; ((simp|intro conjI)+)?)
          apply (rewrite in "_ ## \<hole>" FEQ; auto)
          apply (rewrite in "_ ## \<hole>" FEQ; auto)
          apply (rewrite in "_ = \<hole>" FEQ; auto simp: sep_algebra_simps)
          done
        done  
      
    qed

      
  end

  definition "list\<alpha> \<alpha> l i \<equiv> if i<length l then \<alpha> (l!i) else (0::_::unique_zero_sep_algebra)"  
  
  lemma list\<alpha>_upd[simp]: 
    "i<length xs \<Longrightarrow> list\<alpha> \<alpha> (xs[i := x]) = (list\<alpha> \<alpha> xs)(i:=\<alpha> x)"
    by (rule ext) (auto simp: list\<alpha>_def)

  definition "idx_lifter i \<equiv> \<lparr> 
    sep_lifter.lift = fun_upd (\<lambda>x. 0) i,
    sep_lifter.project = (\<lambda>f. f i),
    sep_lifter.L = idx\<^sub>L i,
    sep_lifter.\<alpha>b = list\<alpha>
        \<rparr>"
    
  lemma idx_lifter[simp, intro!]: "sep_lifter (idx_lifter i)"
    apply unfold_locales
    apply (simp_all add: idx_lifter_def)
    apply (auto simp: sep_algebra_simps)
    apply (auto simp: sep_disj_fun_def sep_algebra_simps intro!: exI[where x="f(i:=0::'a)" for f])
    apply (auto simp: list\<alpha>_def[abs_def])
    subgoal
      by (smt fun_upd_same plus_fun_def unique_zero_simps(4))
    subgoal
      by (smt fun_upd_same idxL_getput'(1) idxL_pre(1) plus_fun_def sep_add_commute sep_disj_zero unique_zero_simps(2))
    subgoal
      apply (rule ext; auto)
      apply (auto simp: fun_eq_iff sep_disj_fun_def )
      subgoal
        by (smt fun_upd_same idxL_getput'(2) idxL_pre(2) nth_list_update plus_fun_def unique_zero_simps(2))
      subgoal
        by (smt LENS_downstage(4) fun_upd_same idx\<^sub>L_def list\<alpha>_def list\<alpha>_upd option.sel plus_fun_def unique_zero_simps(4))
      subgoal by (smt idxL_getput'(2) idxL_pre(2) length_list_update nth_list_update_neq sep_add_zero unique_zero_simps(4))
      subgoal by (metis (mono_tags, lifting) idxL_getput'(2) idxL_pre(2) length_list_update unique_zero_simps(4))
      done
    done
    
  fun option\<alpha> :: "_ \<Rightarrow> 'a::unique_zero_sep_algebra option \<Rightarrow> 'a" 
    where "option\<alpha> \<alpha> None = 0" | "option\<alpha> \<alpha> (Some x) = \<alpha> x"
    
  lemma option\<alpha>_alt: "option\<alpha> \<alpha> x = (case x of None \<Rightarrow> 0 | Some y \<Rightarrow> \<alpha> y)" by (cases x) auto 
    
  definition "option_lifter \<equiv> \<lparr>
    sep_lifter.lift = id,
    sep_lifter.project = id,
    sep_lifter.L = the\<^sub>L,
    sep_lifter.\<alpha>b = option\<alpha>
  \<rparr>"  
    
  lemma option_lifter[simp, intro!]: "sep_lifter option_lifter"
    apply unfold_locales
    apply (auto simp: option_lifter_def)
    apply (auto simp: option\<alpha>_alt split: option.splits)
    done
  
  definition 
    compose_lifter :: 
    "('as::unique_zero_sep_algebra,'cs,'ab::unique_zero_sep_algebra,'cb) sep_lifter 
      \<Rightarrow> ('ab,'cb,'al::unique_zero_sep_algebra,'cl) sep_lifter
      \<Rightarrow> ('as, 'cs, 'al, 'cl) sep_lifter"
  where "compose_lifter l\<^sub>1 l\<^sub>2 \<equiv> \<lparr>
    sep_lifter.lift = sep_lifter.lift l\<^sub>2 o sep_lifter.lift l\<^sub>1,
    sep_lifter.project = sep_lifter.project l\<^sub>1 o sep_lifter.project l\<^sub>2,
    sep_lifter.L = sep_lifter.L l\<^sub>2 \<bullet>\<^sub>L sep_lifter.L l\<^sub>1,
    sep_lifter.\<alpha>b = sep_lifter.\<alpha>b l\<^sub>2 o sep_lifter.\<alpha>b l\<^sub>1
  \<rparr>"  
    
  lemma
    fixes l\<^sub>1 :: "('as::unique_zero_sep_algebra, 'cs, 'ab::unique_zero_sep_algebra, 'cb) sep_lifter" 
      and l\<^sub>2 :: "('ab, 'cb, 'al::unique_zero_sep_algebra, 'cl) sep_lifter"
    assumes "sep_lifter l\<^sub>1"  
    assumes "sep_lifter l\<^sub>2"  
    shows "sep_lifter (compose_lifter l\<^sub>1 l\<^sub>2)"
  proof -
    interpret l1: sep_lifter l\<^sub>1 by fact
    interpret l2: sep_lifter l\<^sub>2 by fact
    
    have [intro]: "\<exists>b\<^sub>2. b = l2.lift (l1.lift (l1.project (l2.project b))) + b\<^sub>2 \<and> l1.project (l2.project b\<^sub>2) = 0" for b
    proof -
      from l2.splitE[of b] obtain b\<^sub>2 
        where 1: "b = l2.lift (l2.project b) + b\<^sub>2" and [simp]: "l2.project b\<^sub>2 = 0" .
      from l1.splitE[of "l2.project b"] obtain b\<^sub>1 
        where 2: "l2.project b = l1.lift (l1.project (l2.project b)) + b\<^sub>1" and [simp]: "l1.project b\<^sub>1 = 0" .
      show ?thesis  
        apply (rule exI[where x="l2.lift b\<^sub>1 + b\<^sub>2"])
        apply (rewrite in "\<hole> = _" 1)
        apply (rewrite in "\<hole> = _" 2)
        apply (auto simp: sep_algebra_simps)
        done
    qed
        
    show ?thesis
      apply unfold_locales
      apply (clarsimp_all simp: compose_lifter_def)
      subgoal by (auto simp: simp: l1.disj_project_eq_lift l2.disj_project_eq_lift) []
      subgoal by auto
      subgoal for p f \<alpha>s cl proof (intro conjI)
        assume A: "l2.lift (l1.lift p) ## f" "l2.\<alpha>b (l1.\<alpha>b \<alpha>s) cl = l2.lift (l1.lift p) + f" "p \<noteq> 0"
        
        show "pre_get l2.L cl"
          using l2.precond l2.get_xfer A by auto
      
        thm l1.precond  
      
        apply (intro conjI)
        apply (rule l2.precond[THEN conjunct1]; assumption?; simp)
        
        apply (rule l1.precond[THEN conjunct1])
        
      subgoal 
        
      
      subgoal for b
        thm l1.splitE
      
      
      subgoal 
        by (metis l1.project_lift_id l1.project_pres_zero l2.precond)
      subgoal sorry
      subgoal
        by (simp add: \<open>\<And>p f cb \<alpha>s. \<lbrakk>l2.lift (l1.lift p) ## f; l2.\<alpha>b (l1.\<alpha>b \<alpha>s) cb = l2.lift (l1.lift p) + f; p \<noteq> 0\<rbrakk> \<Longrightarrow> pre_get l2.L cb\<close>)
      subgoal
        by (simp add: \<open>\<And>p f cb \<alpha>s. \<lbrakk>l2.lift (l1.lift p) ## f; l2.\<alpha>b (l1.\<alpha>b \<alpha>s) cb = l2.lift (l1.lift p) + f; p \<noteq> 0\<rbrakk> \<Longrightarrow> pre_get l1.L (get' l2.L cb)\<close>)
      subgoal sorry
      subgoal sorry
    
    
      
  definition "lift_idx i x \<equiv> fun_upd (\<lambda>x. 0) i x"
  definition "project_idx i f \<equiv> f i"
  
  interpretation fun_upd_lifter: sep_lifter "lift_idx i" "project_idx i" for i
    apply unfold_locales
    apply (auto simp: sep_algebra_simps lift_idx_def project_idx_def)
    apply (auto simp: sep_disj_fun_def sep_algebra_simps intro!: exI[where x="f(i:=0::'b)" for f])
    done
  
  definition "list\<alpha> \<alpha> l i \<equiv> if i<length l then \<alpha> (l!i) else (0::_::unique_zero_sep_algebra)"  
  
  lemma list\<alpha>_upd[simp]: 
    "i<length xs \<Longrightarrow> list\<alpha> \<alpha> (xs[i := x]) = (list\<alpha> \<alpha> xs)(i:=\<alpha> x)"
    by (rule ext) (auto simp: list\<alpha>_def)
    
  lemma lift_idx_same[simp]: "lift_idx i x i = x" by (auto simp: lift_idx_def)
    
  lemma idx_lifter_aux1:
    assumes "lift_idx i p ## f" "list\<alpha> \<alpha>s xs = lift_idx i p + f" "p \<noteq> 0"
    shows "i<length xs" 
    apply (rule ccontr)
    using fun_cong[where x=i, OF assms(2)] assms(1,3)
    apply (auto simp: list\<alpha>_def sep_algebra_simps)
    by (metis lift_idx_same sep_disj_commuteI sep_disj_fun_def unique_zero_simps(4))
    

  lemma idx_lifter_aux2: "\<lbrakk>list\<alpha> \<alpha> xs = lift_idx i a + b; i < length xs\<rbrakk> \<Longrightarrow> \<alpha> (xs!i) = a + project_idx i b"  
    apply (drule fun_cong[where x=i])
    apply (auto simp: list\<alpha>_def project_idx_def)
    done
    
  interpretation idx_lifter: sep_lens_lifter "lift_idx i" "project_idx i" "idx\<^sub>L i" list\<alpha> for i
    apply unfold_locales
    apply (auto simp: idx_lifter_aux1) [7]
    apply (frule (2) idx_lifter_aux1; simp add: idx_lifter_aux2)
    apply (frule (2) idx_lifter_aux1; simp add: sep_algebra_simps)
    apply (rule ext; auto simp: project_idx_def lift_idx_def)
    done
    
  
  interpretation id_lifter: sep_lifter id id 
    by unfold_locales auto
    
  fun option\<alpha> :: "_ \<Rightarrow> 'a::unique_zero_sep_algebra option \<Rightarrow> 'a" 
    where "option\<alpha> \<alpha> None = 0" | "option\<alpha> \<alpha> (Some x) = \<alpha> x"
    
  lemma option\<alpha>_alt: "option\<alpha> \<alpha> x = (case x of None \<Rightarrow> 0 | Some y \<Rightarrow> \<alpha> y)" by (cases x) auto 
    
  interpretation option_lifter: sep_lens_lifter id id "the\<^sub>L" option\<alpha>
    apply unfold_locales
    apply (auto simp: option\<alpha>_alt split: option.splits)
    done
    
  lemma 
    assumes "sep_lens_lifter lift\<^sub>1 project\<^sub>1 L\<^sub>1 \<alpha>\<^sub>1"  
    assumes "sep_lens_lifter lift\<^sub>2 project\<^sub>2 L\<^sub>2 \<alpha>\<^sub>2"  
    shows "sep_lens_lifter (lift\<^sub>2 o lift\<^sub>1) (project\<^sub>1 o project\<^sub>2) (L\<^sub>2 \<bullet>\<^sub>L L\<^sub>1) (\<alpha>\<^sub>2 o \<alpha>\<^sub>1)"
    
    
    
    
oops    
    
  xxx: How to terminate lifter nesting? 
    wrap lifter into typedef, and define operations on lifters:
    
    
    element access
    composition
    
        
    
end
