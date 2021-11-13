theory Sep_Generic_Wp
imports 
  "../lib/Sep_Algebra_Add" 
  "../lib/Frame_Infer"
  "../lib/Monad"
begin

section \<open>General VCG Setup for Separation Logic\<close>

locale generic_wp =
  fixes wp :: "'c \<Rightarrow> ('r \<Rightarrow> 'i::interference \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> 's \<Rightarrow> bool"
  assumes wp_comm_inf: "inf (wp c Q) (wp c Q') = wp c (inf Q Q')"
begin

  lemma wp_comm_conj: "wp c (\<lambda>r i. Q r i and Q' r i) s \<longleftrightarrow> wp c Q s \<and> wp c Q' s"
    using wp_comm_inf[of c Q Q']
    unfolding inf_fun_def inf_bool_def by metis

  lemma wp_comm_conjI: "\<lbrakk> wp c Q s; wp c Q' s \<rbrakk> \<Longrightarrow> wp c (\<lambda>r i s. Q r i s \<and> Q' r i s) s"
    using wp_comm_inf[of c Q Q']
    unfolding inf_fun_def inf_bool_def by metis


  lemma wp_mono: "Q\<le>Q' \<Longrightarrow> wp c Q \<le> wp c Q'"
    by (metis (mono_tags) antisym_conv le_inf_iff order_refl wp_comm_inf)

  lemma wp_monoI:
    assumes "wp c Q s"
    assumes "\<And>r i x. Q r i x \<Longrightarrow> Q' r i x"
    shows "wp c Q' s"
    using assms wp_mono[of Q Q' c]
    by (metis le_funI predicate1D predicate1I wp_mono)
    
end

definition "wp c Q s \<equiv> mwp (run c s) bot bot bot (\<lambda>r i s. Q r i s)"

lemma wp_false[simp]: "\<not>wp c (\<lambda>_ _ _. False) s"
  unfolding wp_def fun_eq_iff mwp_def
  by (auto split: mres.split)

interpretation generic_wp wp 
  apply unfold_locales 
  unfolding wp_def fun_eq_iff inf_fun_def inf_bool_def mwp_def
  by (auto split: mres.split)

lemma wp_return[vcg_normalize_simps]: "wp (return x) Q s \<longleftrightarrow> Q x 0 s"  
  by (auto simp: wp_def run_simps)

lemma wp_fail[vcg_normalize_simps]: "\<not> wp (fail x) Q s"  
  by (auto simp: wp_def run_simps)

lemma wp_fcheck[vcg_normalize_simps]: "wp (fcheck e \<Phi>) Q s \<longleftrightarrow> \<Phi> \<and> Q () 0 s"  
  by (auto simp: wp_def run_simps)

lemma wp_interfer[vcg_normalize_simps]: "wp (interfer i) Q s = Q () i s"  
  by (auto simp: wp_def run_simps)
  
lemma mwp_add_intf_cong:
  assumes "\<And>e i' s. E' e i' s = E e (i+i') s"
  assumes "\<And>x i' s. S' x i' s = S x (i+i') s"
  shows "mwp (add_intf i m) N F E S = mwp m N F E' S'"  
  using assms apply (cases m; auto) done 
  
lemma wp_bind[vcg_normalize_simps]: "wp (m\<bind>f) Q s = wp m (\<lambda>x i. wp (f x) (\<lambda>x' i'. Q x' (i+i'))) s"  
  by (auto simp: wp_def run_simps mwp_add_intf_cong)

lemma wp_par: "wp (par E m\<^sub>1 m\<^sub>2) Q s = wp m\<^sub>1 (\<lambda>x\<^sub>1 i\<^sub>1 s. wp m\<^sub>2 (\<lambda>x\<^sub>2 i\<^sub>2 s. nointer i\<^sub>1 i\<^sub>2 \<and> Q (x\<^sub>1,x\<^sub>2) (i\<^sub>1+i\<^sub>2) s) s) s"  
  apply (auto simp: wp_def run_simps)
  apply (auto simp: mwp_def split: mres.splits if_splits)
  done
  
lemma wp_get[vcg_normalize_simps]: "wp (Monad.get) Q s = Q s 0 s"  
  by (auto simp: wp_def run_simps)
  
lemma wp_set[vcg_normalize_simps]: "wp (Monad.set s') Q s = Q () 0 s'"
  by (auto simp: wp_def run_simps)
  
  
locale abs_mem =
  fixes allocated :: "'s \<Rightarrow> 'addr set"  
    and freed :: "'s \<Rightarrow> 'addr set"
  assumes alloc_free_dj: "allocated s \<inter> freed s = {}"  
begin

  definition "valid_trans s s' \<equiv> allocated s \<subseteq> allocated s' \<union> freed s' \<and> freed s \<subseteq> freed s'"

  lemma vt_refl[simp, intro!]: "valid_trans s s" 
    unfolding valid_trans_def by simp
  lemma vt_trans[trans]: "valid_trans s\<^sub>1 s\<^sub>2 \<Longrightarrow> valid_trans s\<^sub>2 s\<^sub>3 \<Longrightarrow> valid_trans s\<^sub>1 s\<^sub>3" 
    unfolding valid_trans_def by auto
  
  definition "used_mem s \<equiv> allocated s \<union> freed s"
  definition "new_mem s s' \<equiv> used_mem s' - used_mem s"
  
  lemma new_mem_refl[simp]: "new_mem s s = {}" unfolding new_mem_def by auto 
  
  lemma new_mem_trans1: "\<lbrakk>valid_trans s\<^sub>1 s\<^sub>2\<rbrakk> \<Longrightarrow> new_mem s\<^sub>2 s\<^sub>3 \<subseteq> new_mem s\<^sub>1 s\<^sub>3"
    unfolding valid_trans_def new_mem_def used_mem_def
    by auto
    
  lemma new_mem_trans2: "valid_trans s\<^sub>2 s\<^sub>3 \<Longrightarrow> new_mem s\<^sub>1 s\<^sub>2 \<subseteq> new_mem s\<^sub>1 s\<^sub>3"
    unfolding valid_trans_def new_mem_def used_mem_def
    by auto
  
end  

locale abs_sep = abs_mem allocated freed 
    for allocated :: "'s \<Rightarrow> 'addr set"  
    and freed :: "'s \<Rightarrow> 'addr set"+
  fixes \<alpha> :: "'s \<Rightarrow> 'a::sep_algebra"
    and addrs :: "'a \<Rightarrow> 'addr set"
  assumes addr_cover[simp]: "addrs (\<alpha> s) = allocated s"    
      and addr_dj: "a##b \<Longrightarrow> addrs a \<inter> addrs b = {}"
      and addr_add[simp]: "a##b \<Longrightarrow> addrs (a+b) = addrs a \<union> addrs b"
begin
  lemma addrsZ[simp]: "addrs 0 = {}"
    using addr_dj disjoint_zero_sym by blast

  lemma addr_djI[intro]:
    "a##b \<Longrightarrow> x\<in>addrs a \<Longrightarrow> x\<notin>addrs b"  
    "a##b \<Longrightarrow> x\<in>addrs b \<Longrightarrow> x\<notin>addrs a"  
    using addr_dj by auto
    

end  
  

locale generic_sep_logic = abs_sep allocated freed \<alpha> addrs
    for allocated :: "'s \<Rightarrow> 'addr set"  
    and freed :: "'s \<Rightarrow> 'addr set"
    and \<alpha> :: "'s \<Rightarrow> 'a::sep_algebra"
    and addrs :: "'a \<Rightarrow> 'addr set" +
  fixes touches :: "'i::interference \<Rightarrow> 'addr set"
  assumes touches0[simp]: "touches 0 = {}"  
      and touches_add[simp]: "touches (a+b) = touches a \<union> touches b"
      and touches_nointer[simp]: "touches a \<inter> touches b = {} \<Longrightarrow> nointer a b"
      
begin

  definition "wpa A c Q s \<equiv> wp c (\<lambda>r i s'. 
      touches i \<inter> (A \<union> freed s) = {} 
    \<and> touches i \<subseteq> allocated s \<union> new_mem s s' 
    \<and> valid_trans s s'
    \<and> Q r s') s"

  lemma wpa_monoI:
    assumes "wpa A c Q s"
    assumes "\<And>r s'. \<lbrakk> valid_trans s s'; Q r s' \<rbrakk> \<Longrightarrow> Q' r s'"
    assumes "A' \<union> freed s \<subseteq> A \<union> freed s"
    shows "wpa A' c Q' s"
    using assms unfolding wpa_def
    by (blast intro: wp_monoI)
    
    
  lemma wpa_return[vcg_normalize_simps]: "wpa A (return x) Q s = Q x s"
    by (simp add: wpa_def vcg_normalize_simps)

  lemma wpa_bindI[vcg_decomp_rules]: "wpa A m (\<lambda>x. wpa A (f x) Q) s \<Longrightarrow> wpa A (doM {x\<leftarrow>m; f x}) Q s"  
    apply (simp add: wpa_def vcg_normalize_simps)
    apply (erule wp_monoI; clarsimp)
    apply (erule wp_monoI; clarsimp)
    unfolding new_mem_def used_mem_def valid_trans_def
    using alloc_free_dj
    by fast

  lemma wpa_parI:
    assumes "wpa (A \<union> (used_mem s - I\<^sub>1)) c\<^sub>1 (\<lambda>r\<^sub>1 s\<^sub>1. wpa (A \<union> (used_mem s\<^sub>1 - I\<^sub>2)) c\<^sub>2 (\<lambda>r\<^sub>2. Q (r\<^sub>1,r\<^sub>2)) s\<^sub>1) s"
    assumes "I\<^sub>1 \<inter> I\<^sub>2 = {}" 
    assumes "I\<^sub>1 \<subseteq> used_mem s" "I\<^sub>2 \<subseteq> used_mem s"
    shows "wpa A (par E c\<^sub>1 c\<^sub>2) Q s"
    using assms
    unfolding wpa_def
    apply (clarsimp simp: wp_par)
    apply (erule wp_monoI; clarsimp)
    apply (erule wp_monoI; clarsimp)
    apply (intro conjI)
    subgoal
      apply (auto intro!: touches_nointer)
      unfolding valid_trans_def used_mem_def new_mem_def
      by fast    
    subgoal using valid_trans_def by auto 
    subgoal by (meson Diff_subset_conv new_mem_trans2 subset_trans)
    subgoal
      by (smt (verit) Diff_eq_empty_iff Diff_iff IntI Un_iff alloc_free_dj new_mem_def subsetI used_mem_def valid_trans_def)
    subgoal
      by (meson vt_trans)
    done
    
        
  lemma wpa_false[vcg_normalize_simps]: "\<not>wpa A m (\<lambda>_ _. False) s"  
    by (simp add: wpa_def vcg_normalize_simps)
  
  lemma wpa_fail[vcg_normalize_simps]: "\<not>wpa A (fail msg) Q s"  
    by (simp add: wpa_def vcg_normalize_simps)

  lemma wpa_fcheck[vcg_normalize_simps]: "wpa A (fcheck msg \<Phi>) Q s \<longleftrightarrow> \<Phi> \<and> Q () s"  
    by (simp add: wpa_def vcg_normalize_simps)
        
  lemma wpa_interfer[vcg_normalize_simps]: "wpa A (interfer i) Q s 
    \<longleftrightarrow> (touches i \<inter> (A\<union>freed s) = {} \<and> touches i \<subseteq> allocated s \<and> Q () s)"  
    by (simp add: wpa_def vcg_normalize_simps)
    
  lemma wpa_get[vcg_normalize_simps]: "wpa A (Monad.get) Q s \<longleftrightarrow> Q s s"  
    by (simp add: wpa_def vcg_normalize_simps)
    
  lemma wpa_set[vcg_normalize_simps]: "wpa A (Monad.set s') Q s \<longleftrightarrow> valid_trans s s' \<and> Q () s'"
    by (simp add: wpa_def vcg_normalize_simps)
    
    
  (* definition "restrA asf s \<equiv> addrs asf \<union> freed s" *)
    
  definition "STATE asf P s \<equiv> \<exists>as. as ## asf \<and> \<alpha> s = as+asf \<and> P as"
  definition "htriple P c Q \<equiv> (\<forall>s asf. STATE asf P s 
    \<longrightarrow> wpa (addrs asf) c (\<lambda>r s'. STATE asf (Q r) s') s)"

  lemma htripleI[intro?]:
    assumes "\<And>s asf. STATE asf P s \<Longrightarrow> wpa (addrs asf) c (\<lambda>r s'. STATE asf (Q r) s') s"
    shows "htriple P c Q"
    using assms unfolding htriple_def by blast
  
  lemma htripleD: 
    assumes "htriple P c Q"
    assumes "STATE asf P s"
    shows "wpa (addrs asf) c (\<lambda>r s'. STATE asf (Q r) s') s"
    using assms unfolding htriple_def by blast
  
  lemma STATE_triv[simp]: "\<not>STATE asf sep_false s"
    by (simp add: STATE_def)
    
  lemma STATE_monoI: "STATE asf P s \<Longrightarrow> P \<turnstile> P' \<Longrightarrow> STATE asf P' s"  
    unfolding STATE_def entails_def by blast
    
  lemma STATE_frame1:
    "STATE asf (P**F) s \<Longrightarrow> \<exists>asf'. asf'##asf \<and> F asf' \<and> STATE (asf'+asf) P s"  
    unfolding STATE_def
    apply (auto simp: sep_algebra_simps sep_conj_def)
    by (smt (verit, ccfv_threshold) Un_iff addr_add sep_add_assoc sep_add_commute sep_disj_addD2 sep_disj_addI3 sep_disj_commuteI subset_eq)

  lemma STATE_frame2: 
    assumes "STATE (asf'+asf) P s"
    assumes "asf' ## asf"  
    assumes "F asf'"
    shows "STATE asf (P**F) s"
    using assms
    unfolding STATE_def
    apply (auto simp: sep_algebra_simps sep_conj_def)
    by (smt (verit, ccfv_threshold) Un_iff addr_add sep_add_assoc sep_add_commute sep_disj_addD2 sep_disj_addI3 sep_disj_commuteI subset_eq)
          

  lemma htriple_triv[simp, intro!]: "htriple sep_false c Q"
    by (auto simp: htriple_def)
      
  lemma cons_rule:
    assumes "htriple P c Q"
    assumes "\<And>s. P' s \<Longrightarrow> P s"
    assumes "\<And>r s. Q r s \<Longrightarrow> Q' r s"
    shows "htriple P' c Q'"
  proof
    fix asf s
    assume "STATE asf P' s"
    with STATE_monoI assms(2) have "STATE asf P s" unfolding entails_def by blast
    from htripleD[OF assms(1) this] have "wpa (addrs asf) c (\<lambda>r. STATE asf (Q r)) s" .
    then show "wpa (addrs asf) c (\<lambda>r. STATE asf (Q' r)) s"
      apply (rule wpa_monoI)
      apply (erule STATE_monoI)
      using assms(3) unfolding entails_def 
      by auto
      
  qed  
      
  lemma cons_post_rule:
    assumes "htriple P c Q"
    assumes "\<And>r s. Q r s \<Longrightarrow> Q' r s"
    shows "htriple P c Q'"
    using cons_rule assms by blast
    
  lemma apply_htriple_rule:
    assumes "STATE asf (P**F) s"
    assumes "htriple P c Q"
    assumes "\<And>s' r. STATE asf (Q r ** F) s' \<Longrightarrow> Q' r s'"
    shows "wpa (addrs asf) c Q' s"  
  proof -
    from STATE_frame1[OF assms(1)] obtain asf' where 
      D: "asf' ## asf" "F asf'" 
      and S: "STATE (asf' + asf) P s" 
      by blast
  
    from htripleD[OF assms(2) S] have "wpa (addrs (asf'+asf)) c (\<lambda>r s'. STATE (asf' + asf) (Q r) s') s" .
    moreover have "\<lbrakk>STATE (asf' + asf) (Q r) s'; valid_trans s s'\<rbrakk> \<Longrightarrow> STATE asf (Q r ** F) s'" for r s'
      by (rule STATE_frame2; (assumption|rule D)?)
    ultimately have "wpa (addrs asf)  c (\<lambda>r s'. STATE asf (Q r ** F) s') s"
      apply (rule wpa_monoI) by (auto simp: D)
    then show ?thesis using assms(3)
      by (rule wpa_monoI) auto
  qed

        
  lemma frame_rule: "htriple P c Q \<Longrightarrow> htriple (P ** F) c (\<lambda>r. Q r ** F)"
    apply rule
    apply (erule apply_htriple_rule)
    .
    
  
  lemma ht_par:
    assumes "htriple P\<^sub>1 m\<^sub>1 Q\<^sub>1"  
    assumes "htriple P\<^sub>2 m\<^sub>2 Q\<^sub>2"  
    shows "htriple (P\<^sub>1**P\<^sub>2) (par E m\<^sub>1 m\<^sub>2) (\<lambda>(r\<^sub>1,r\<^sub>2). Q\<^sub>1 r\<^sub>1 ** Q\<^sub>2 r\<^sub>2)"
    apply (rule)
    unfolding STATE_def
    apply (clarsimp simp: sep_conj_def)
    subgoal for s asf as\<^sub>1 as\<^sub>2
    apply (rule wpa_parI[where I\<^sub>1="addrs as\<^sub>1" and I\<^sub>2="addrs as\<^sub>2"])
    apply (rule wpa_monoI)
    apply (rule htripleD[OF assms(1), where asf="as\<^sub>2+asf"])
    subgoal
      unfolding STATE_def
      apply (rule exI[where x=as\<^sub>1])
      apply (auto simp: sep_algebra_simps)
      subgoal
        using sep_disj_addI3 sep_disj_commute by blast
      subgoal 
        by (metis sep_add_commute sep_add_left_commute sep_disj_addD1 sep_disj_addD2)
      done  
      (*subgoal 
        by (me tis UnE UnI2 addr_add in_mono sep_disj_addD sep_disj_commute)
      subgoal
        by (metis UnE \<open>\<lbrakk>asf ## as\<^sub>1 + as\<^sub>2; \<alpha> s = asf + (as\<^sub>1 + as\<^sub>2); A \<subseteq> addrs asf \<union> freed s; as\<^sub>1 ## as\<^sub>2; P\<^sub>1 as\<^sub>1; P\<^sub>2 as\<^sub>2\<rbrakk> \<Longrightarrow> as\<^sub>1 ## as\<^sub>2 + asf\<close> \<open>\<lbrakk>asf ## as\<^sub>1 + as\<^sub>2; \<alpha> s = asf + (as\<^sub>1 + as\<^sub>2); A \<subseteq> addrs asf \<union> freed s; as\<^sub>1 ## as\<^sub>2; P\<^sub>1 as\<^sub>1; P\<^sub>2 as\<^sub>2\<rbrakk> \<Longrightarrow> asf + (as\<^sub>1 + as\<^sub>2) = as\<^sub>1 + (as\<^sub>2 + asf)\<close> addr_add addr_cover used_mem_def)
      done*)
    subgoal for r\<^sub>1 s\<^sub>1
      unfolding STATE_def
      apply clarsimp
      subgoal for as\<^sub>1'
        apply (rule wpa_monoI)
        apply (rule htripleD[OF assms(2), where asf="as\<^sub>1'+asf"])
        subgoal
          unfolding STATE_def
          apply (rule exI[where x=as\<^sub>2])
          apply (auto simp: sep_algebra_simps)
          subgoal by (meson sep_add_disjD sep_disj_addI2 sep_disj_commuteI)
          subgoal by (meson sep_add_left_commute sep_disj_addD1 sep_disj_addD2 sep_disj_commuteI)
          (*subgoal by (metis Un_iff addr_add sep_disj_addD2 sep_disj_commuteI subset_Un_eq valid_trans_def)
          subgoal by (metis UnE \<open>\<lbrakk>asf ## as\<^sub>1 + as\<^sub>2; \<alpha> s = asf + (as\<^sub>1 + as\<^sub>2); A \<subseteq> addrs asf \<union> freed s; as\<^sub>1 ## as\<^sub>2; P\<^sub>1 as\<^sub>1; P\<^sub>2 as\<^sub>2; valid_trans s s\<^sub>1; as\<^sub>1' ## as\<^sub>2 + asf; \<alpha> s\<^sub>1 = as\<^sub>1' + (as\<^sub>2 + asf); Q\<^sub>1 r\<^sub>1 as\<^sub>1'; A \<subseteq> addrs (as\<^sub>2 + asf) \<union> freed s\<^sub>1; used_mem s - addrs as\<^sub>1 \<subseteq> addrs (as\<^sub>2 + asf) \<union> freed s\<^sub>1\<rbrakk> \<Longrightarrow> as\<^sub>1' + (as\<^sub>2 + asf) = as\<^sub>2 + (as\<^sub>1' + asf)\<close> \<open>\<lbrakk>asf ## as\<^sub>1 + as\<^sub>2; \<alpha> s = asf + (as\<^sub>1 + as\<^sub>2); A \<subseteq> addrs asf \<union> freed s; as\<^sub>1 ## as\<^sub>2; P\<^sub>1 as\<^sub>1; P\<^sub>2 as\<^sub>2; valid_trans s s\<^sub>1; as\<^sub>1' ## as\<^sub>2 + asf; \<alpha> s\<^sub>1 = as\<^sub>1' + (as\<^sub>2 + asf); Q\<^sub>1 r\<^sub>1 as\<^sub>1'; A \<subseteq> addrs (as\<^sub>2 + asf) \<union> freed s\<^sub>1; used_mem s - addrs as\<^sub>1 \<subseteq> addrs (as\<^sub>2 + asf) \<union> freed s\<^sub>1\<rbrakk> \<Longrightarrow> as\<^sub>2 ## as\<^sub>1' + asf\<close> addr_add addr_cover used_mem_def)*)
          done
        subgoal for r\<^sub>2 s\<^sub>2
          unfolding STATE_def
          apply clarsimp
          subgoal for as\<^sub>2'
            apply (rule exI[where x="as\<^sub>1'+as\<^sub>2'"])
            apply auto
            subgoal by (meson sep_add_disjD sep_add_disjI1 sep_disj_commuteI)
            subgoal by (metis sep_add_assoc sep_add_commute sep_add_disjD sep_disj_addD1 sep_disj_addD2)
            subgoal by (metis sep_add_disjD sep_disj_commuteI)
            (*subgoal by (metis UnE subsetD valid_trans_def)*)
            done
          done  
        subgoal
          by (smt (z3) Diff_subset_conv Un_subset_iff addr_add addr_cover inf_sup_ord(3) inf_sup_ord(4) sep_add_disjD sep_disj_addD2 used_mem_def)
        done
      done
      subgoal by (smt (z3) DiffD2 Diff_subset Un_iff addr_add addr_cover sep_add_disjD subsetD subsetI used_mem_def)
      subgoal using addr_dj by presburger
      subgoal by (metis addr_add addr_cover le_sup_iff sup_ge1 used_mem_def)
      subgoal by (metis addr_add addr_cover inf_sup_ord(3) le_supE used_mem_def)
      done
    done

subsection \<open>Realizable abstract Predicates\<close>    
  definition "realizable P \<equiv> \<exists>s as asf. P as \<and> \<alpha> s = as + asf \<and> as ## asf"
  
  lemma realizable_conjD: "realizable (P**Q) \<Longrightarrow> realizable P \<and> realizable Q"
    apply (clarsimp simp: realizable_def sep_conj_def sep_algebra_simps sep_conj_c; intro conjI)
    subgoal for s x asf y
      apply (rule exI[where x=s])
      apply (rule exI[where x="x"])
      apply simp
      apply (rule exI[where x="asf+y"])
      by (meson sep_add_left_commute sep_disj_addD1 sep_disj_addD2 sep_disj_addI2 sep_disj_commuteI)
    
    subgoal for s x asf y
      apply (rule exI[where x=s])
      apply (rule exI[where x="y"])
      apply simp
      apply (rule exI[where x="asf+x"])
      by (metis sep_add_assoc sep_add_commute sep_disj_addD2 sep_disj_addI1 sep_disj_commuteI)
      
    done

  lemma realizable_emp[simp]: "realizable \<box>"    
    by (auto simp add: realizable_def sep_algebra_simps)
          
  lemma realizable_pure[simp]: "realizable (\<up>\<phi>) \<longleftrightarrow> \<phi>"  
    by (auto simp add: realizable_def sep_algebra_simps)
      
  lemma realizable_extract_pure[simp]: "realizable (\<up>\<phi> ** P) \<longleftrightarrow> \<phi> \<and> realizable P"  
    by (auto simp add: realizable_def sep_algebra_simps)
      
  lemma htriple_false: "htriple P c (\<lambda>r s. False) \<longleftrightarrow> \<not>realizable P"
    unfolding htriple_def STATE_def
    by (auto simp: wpa_false realizable_def)
    
    
  lemma htriple_realizable_preI: 
    assumes "realizable P \<Longrightarrow> htriple P c Q"
    shows "htriple P c Q"
    using assms
    using cons_post_rule htriple_false by fastforce
    
  lemma STATE_realizableI: "STATE f P s \<Longrightarrow> realizable P"  
    unfolding STATE_def realizable_def by auto
    
    
subsection \<open>VCG Setup\<close>    
    
lemma STATE_assn_cong[fri_extract_congs]: "P\<equiv>P' \<Longrightarrow> STATE f P s \<equiv> STATE f P' s" by simp
  
lemma STATE_extract[vcg_normalize_simps]:
  "STATE asf (\<up>\<Phi>) h \<longleftrightarrow> \<Phi> \<and> STATE asf \<box> h"
  "STATE asf (\<up>\<Phi> ** P) h \<longleftrightarrow> \<Phi> \<and> STATE asf P h"
  "STATE asf (EXS x. Q x) h \<longleftrightarrow> (\<exists>x. STATE asf (Q x) h)"
  "STATE asf (\<lambda>_. False) h \<longleftrightarrow> False"
  "STATE asf ((\<lambda>_. False) ** P) h \<longleftrightarrow> False"
  by (auto simp: STATE_def sep_algebra_simps)
 

definition POSTCOND where [vcg_tag_defs]: "POSTCOND \<equiv> STATE"
  
lemma POSTCONDI:
  "STATE asf Q h \<Longrightarrow> POSTCOND asf Q h"
  by (auto simp add: POSTCOND_def)
lemma POSTCOND_cong[vcg_normalize_congs]: "POSTCOND asf Q = POSTCOND asf Q" ..

lemma POSTCOND_triv_simps[vcg_normalize_simps]:
  (* "POSTCOND A asf sep_true h" *)
  "\<not>POSTCOND asf sep_false h"
  unfolding POSTCOND_def STATE_def by auto
  
lemma start_entailsE:
  assumes "STATE asf P h"
  assumes "ENTAILS P P'"
  shows "STATE asf P' h"
  using assms unfolding STATE_def ENTAILS_def entails_def
  by auto

declaration \<open>fn phi =>
   (Basic_VCG.add_xformer (map (Morphism.thm phi) @{thms POSTCONDI},@{binding postcond_xformer},
    fn ctxt => eresolve_tac ctxt (map (Morphism.thm phi) @{thms start_entailsE})
  ))
\<close>

named_theorems htriple_vcg_intros
named_theorems htriple_vcg_intro_congs
definition [vcg_tag_defs]: "DECOMP_HTRIPLE \<phi> \<equiv> \<phi>"
lemma DECOMP_HTRIPLEI: "\<phi> \<Longrightarrow> DECOMP_HTRIPLE \<phi>" unfolding vcg_tag_defs by simp

  lemma htriple_vcg_frame_erule[vcg_frame_erules]:
    assumes S: "STATE asf P' s"
    assumes F: "PRECOND (FRAME P' P F)"
    assumes HT: "htriple P c Q"  
    assumes P: "\<And>r s. STATE asf (Q r ** F) s \<Longrightarrow> PRECOND (EXTRACT (Q' r s))"
    shows "wpa (addrs asf) c Q' s"
  proof -
    from S F have S': "STATE asf (P**F) s"
      unfolding PRECOND_def FRAME_def
      using STATE_monoI by blast

    show ?thesis
      apply (rule apply_htriple_rule[OF S' HT])
      using P unfolding vcg_tag_defs .
      
  qed    
  
  lemma htriple_vcgI': 
    assumes "\<And>asf s. STATE asf P s \<Longrightarrow> wpa (addrs asf) c (\<lambda>r. POSTCOND asf (Q r)) s"
    shows "htriple P c Q"
    apply (rule htripleI)
    using assms unfolding vcg_tag_defs .
  
  lemma htriple_vcgI[htriple_vcg_intros]: 
    assumes "\<And>asf s. STATE asf P s \<Longrightarrow> EXTRACT (wpa (addrs asf) c (\<lambda>r. POSTCOND asf (Q r)) s)"
    shows "htriple P c Q"
    apply (rule htripleI)
    using assms unfolding vcg_tag_defs STATE_def .

      
  lemma htriple_decompI[vcg_decomp_rules]: 
    "DECOMP_HTRIPLE (htriple P c Q) \<Longrightarrow> htriple P c Q"
    unfolding vcg_tag_defs by auto

  lemma htriple_assn_cong[htriple_vcg_intro_congs]: 
    "P\<equiv>P' \<Longrightarrow> Q\<equiv>Q' \<Longrightarrow>  htriple P c Q \<equiv> htriple P' c Q'" by simp

  lemma htriple_ent_pre:
    "P\<turnstile>P' \<Longrightarrow> htriple P' c Q \<Longrightarrow> htriple P c Q"
    unfolding entails_def
    apply (erule cons_rule) by blast+
    
  lemma htriple_ent_post:
    "\<lbrakk>\<And>r. Q r \<turnstile> Q' r\<rbrakk> \<Longrightarrow> htriple P c Q \<Longrightarrow> htriple P c Q'"
    unfolding entails_def
    apply (erule cons_rule) by blast+
   
  lemma htriple_pure_preI: "\<lbrakk>pure_part P \<Longrightarrow> htriple P c Q\<rbrakk> \<Longrightarrow> htriple P c Q"  
    using entails_pureI htriple_ent_pre by blast
    
  
  declaration \<open>
    fn phi => (Basic_VCG.add_xformer (map (Morphism.thm phi) @{thms DECOMP_HTRIPLEI},@{binding decomp_htriple_xformer},
      fn ctxt => 
        (full_simp_tac (put_simpset HOL_basic_ss ctxt 
          addsimps (Named_Theorems.get ctxt @{named_theorems vcg_tag_defs})
          |> fold Simplifier.add_cong (Named_Theorems.get ctxt @{named_theorems htriple_vcg_intro_congs})
        ))
        THEN' resolve_tac ctxt (Named_Theorems.get ctxt @{named_theorems htriple_vcg_intros})
    ))
  \<close>
  
end

    
(*    
oops    
  xxx, ctd here: 
    just went back to a wp-based characterization. (wpa)
    we can prove the relevant rules. and a hoare-rule for par!
    
    ctd:
      remaining rules for wpa
      setup vcg (go back to state/postcond based)
    
  
   
            
  
  definition "htriple P c Q \<equiv> (\<forall>s as asf. as##asf \<and> \<alpha> s = as+asf \<and> P as \<longrightarrow>
      wp c 
        (\<lambda>r i s'. \<exists>as'. as' ## asf \<and> \<alpha> s' = as'+asf \<and> Q r as' 
            \<and> valid_trans s s'
            \<and> touches i \<subseteq> addrs as \<union> new_mem s s'
        ) 
        s
      )"
  
  lemma
    fixes P
    defines "A \<equiv> \<Inter>{addrs as | as . P as}"
    (* assumes "\<forall>as. P as \<longrightarrow> A \<subseteq> addrs as" *)
    assumes "\<And>F s. (P**F) (\<alpha> s) 
      \<Longrightarrow> wp c (\<lambda>r i s'. (Q r ** F) (\<alpha> s') \<and> valid_trans s s' \<and> touches i \<subseteq> A \<union> new_mem s s') s"
    shows "htriple P c Q"
    unfolding htriple_def
    apply clarify
    subgoal for s as asf
      apply (rule wp_monoI)
      thm assms(2)[of "EXACT asf" s]
      apply (rule assms(2)[of "EXACT asf" s])
      using assms(1) 
      apply (auto simp: sep_conj_def sep_algebra_simps) 
      done    
    done  
      

  lemma htripleI[intro?]:
    assumes "\<And>s as asf. \<lbrakk>as##asf; \<alpha> s = as+asf; P as\<rbrakk> \<Longrightarrow> wp c 
        (\<lambda>r i s'. \<exists>as'. as' ## asf \<and> \<alpha> s' = as'+asf \<and> Q r as' 
            \<and> valid_trans s s'
            \<and> touches i \<subseteq> addrs as \<union> new_mem s s'
        ) 
        s"
    shows "htriple P c Q"    
    using assms unfolding htriple_def by blast  
    
  lemma htripleD:
    assumes "htriple P c Q"  
    assumes "as##asf" "\<alpha> s = as+asf" "P as"
    shows "wp c 
        (\<lambda>r i s'. \<exists>as'. as' ## asf \<and> \<alpha> s' = as'+asf \<and> Q r as' 
            \<and> valid_trans s s'
            \<and> touches i \<subseteq> addrs as \<union> new_mem s s'
        ) 
        s"
    using assms unfolding htriple_def by blast  

  lemma frame_rule: 
    assumes "htriple P c Q"  
    shows "htriple (P ** F) c (\<lambda>r. Q r ** F)"
    unfolding htriple_def sep_conj_def
  proof (clarsimp, goal_cases)
    case (1 s asf as\<^sub>1 as\<^sub>2)
    
    note [simp] = \<open>as\<^sub>1 ## as\<^sub>2\<close>
    
    have [simp]: "as\<^sub>2 ## asf"
      using "1"(1) "1"(3) sep_add_disjD by blast

    have [simp]: "as\<^sub>1 ## (as\<^sub>2+asf)"
      by (simp add: "1"(1) sep_disj_addI3)
    
    have [simp]: "\<alpha> s = as\<^sub>1 + (as\<^sub>2+asf)"
      by (metis "1"(2) \<open>as\<^sub>1 ## as\<^sub>2 + asf\<close> \<open>as\<^sub>2 ## asf\<close> sep_add_assoc sep_disj_addD) 
      
    from assms[unfolded htriple_def, rule_format, of as\<^sub>1 "as\<^sub>2+asf" s, simplified, OF \<open>P as\<^sub>1\<close>]  
    show ?case
      apply (rule wp_monoI; clarsimp)
      subgoal for r i x as'
        apply (rule exI[where x="as'+as\<^sub>2"])
        apply (intro conjI)
        subgoal by (simp add: sep_disj_addI1)
        subgoal using sep_add_assoc sep_disj_addD by force
        subgoal using "1"(5) \<open>as\<^sub>2 ## asf\<close> sep_disj_addD1 by blast
        subgoal by blast
        done
      done
    
  qed
      
  lemma cons_rule:
    assumes "htriple P c Q"
    assumes "\<And>s. P' s \<Longrightarrow> P s"
    assumes "\<And>r s. Q r s \<Longrightarrow> Q' r s"
    shows "htriple P' c Q'"
    using assms 
    unfolding htriple_def
    by (smt (verit) wp_monoI)

  lemma ht_false[simp]:
    "htriple (sep_false) c Q"  
    by (simp_all add: htripleI)
    
  lemma htriple_pre_pureI:
    assumes "pure_part P \<Longrightarrow> htriple P c Q"
    shows "htriple P c Q"  
    using assms unfolding pure_part_def htriple_def
    by blast

      
  lemma htriple_extract_pre_pure1:
    assumes "\<Phi> \<Longrightarrow> htriple P c Q"
    shows "htriple (\<up>\<Phi> ** P) c Q"  
    using assms
    by (cases \<Phi>; simp add: sep_algebra_simps)
    
  lemma htriple_extract_pre_pure2:
    assumes "\<Phi> \<Longrightarrow> htriple \<box> c Q"
    shows "htriple (\<up>\<Phi>) c Q"  
    using assms
    by (cases \<Phi>; simp add: sep_algebra_simps)
    
  lemmas htriple_extract_pre_pure = htriple_extract_pre_pure1 htriple_extract_pre_pure2  
    
        
  lemma ht_return: "htriple \<box> (return x) (\<lambda>r. \<up>(r=x))"
    unfolding htriple_def
    by (auto simp: wp_return sep_algebra_simps)
  
    
  lemma ht_fcheck[vcg_rules]: "\<Phi> \<Longrightarrow> htriple \<box> (fcheck e \<Phi>) (\<lambda>_. \<box>)"
    unfolding htriple_def
    by (auto simp: wp_return sep_algebra_simps)
      
  lemma touches_seq_aux:
    assumes VT: "valid_trans s sh" "valid_trans sh s'"
    assumes TSS: "touches i\<^sub>2 \<subseteq> addrs ash \<union> new_mem sh s'"
    assumes AS: "as##asf" "ash##asf" "\<alpha> s = as+asf" "\<alpha> sh = ash + asf"
    shows "touches i\<^sub>2 \<subseteq> addrs as \<union> new_mem s s'"  
  proof -  
    have SS1: "new_mem sh s' \<subseteq> new_mem s s'" by (simp add: VT new_mem_trans1) 
    
    have "a\<in>addrs ash - new_mem s s' \<Longrightarrow> a\<in>addrs as" for a proof -
      assume A: "a\<in>addrs ash - new_mem s s'"
      hence "a\<in>allocated sh" by (metis DiffD1 UnI1 addr_add addr_cover AS(2,4))
      also have "allocated sh \<subseteq> allocated s \<union> new_mem s sh"
        using alloc_free_dj VT new_mem_def valid_trans_def by fastforce
      also have "allocated s = addrs as \<union> addrs asf" 
        by (metis addr_add addr_cover AS(1,3))
      finally have "a\<in>addrs as \<union> addrs asf \<union> new_mem s sh" . 
      moreover have "a\<notin>addrs asf"
        by (metis A DiffD1 IntI addr_dj assms(5) empty_iff)
      moreover have "a\<notin>new_mem s sh" 
        using A assms(2) new_mem_def valid_trans_def by auto
      ultimately show ?thesis by blast
    qed      
    with SS1 TSS show ?thesis by blast
  qed      
    
  lemma ht_bind:
    assumes "htriple P m (\<lambda>x. Qh x)"
    assumes "\<And>x. htriple (Qh x) (f x) Q"
    shows "htriple P (doM {x\<leftarrow>m; f x}) Q"
    unfolding htriple_def apply (clarsimp simp: wp_bind)
    apply (rule wp_monoI)
    apply (rule htripleD[OF assms(1)]; assumption)
    apply clarsimp
    apply (rule wp_monoI)
    apply (rule htripleD[OF assms(2)]; assumption)
    apply clarsimp
    apply (intro exI conjI; (assumption|rule refl)?) 
    apply (blast dest: vt_trans)
    subgoal by (meson equalityD2 new_mem_trans2 subset_trans sup.mono)
    apply (rule touches_seq_aux; assumption)
    done
    
  lemma new_mem_seq_dj: "new_mem s s\<^sub>1 \<inter> new_mem s\<^sub>1 s\<^sub>2 = {}" unfolding new_mem_def by auto 
    
  lemma ht_par:
    assumes "htriple P\<^sub>1 m\<^sub>1 Q\<^sub>1"  
    assumes "htriple P\<^sub>2 m\<^sub>2 Q\<^sub>2"  
    shows "htriple (P\<^sub>1**P\<^sub>2) (par E m\<^sub>1 m\<^sub>2) (\<lambda>(r\<^sub>1,r\<^sub>2). Q\<^sub>1 r\<^sub>1 ** Q\<^sub>2 r\<^sub>2)"
    unfolding htriple_def apply (clarsimp simp: wp_par sep_conj_def)
    subgoal for s asf as\<^sub>1 as\<^sub>2
      apply (subgoal_tac "as\<^sub>1##asf \<and> as\<^sub>2##asf")
      defer 
      using sep_add_disjD apply blast
      apply (rule wp_monoI)
      thm htripleD[OF assms(1), of as\<^sub>1 "as\<^sub>2+asf"]
      apply (rule htripleD[OF assms(1), of as\<^sub>1 "as\<^sub>2+asf"]) 
      subgoal by (meson sep_disj_addI3)
      subgoal by (simp add: sep_algebra_simps)
      subgoal by simp
      apply clarsimp
      subgoal for r\<^sub>1 i\<^sub>1 s\<^sub>1 as\<^sub>1'
        apply (rule wp_monoI)
        thm htripleD[OF assms(2), of as\<^sub>2 "as\<^sub>1'+asf"]
        apply (rule htripleD[OF assms(2), of as\<^sub>2 "as\<^sub>1'+asf"]) 
        subgoal by (meson sep_disj_addI2 sep_disj_commute)
        subgoal by (metis sep_add_left_commute sep_disj_addD1 sep_disj_addD2)
        subgoal by blast
        apply (clarsimp; intro conjI)
        
        subgoal for r\<^sub>2 i\<^sub>2 s\<^sub>2 as\<^sub>2' 
          apply (subgoal_tac "new_mem s s\<^sub>1 \<inter> new_mem s\<^sub>1 s\<^sub>2 = {}")
          apply (subgoal_tac "addrs as\<^sub>1 \<inter> addrs as\<^sub>2 = {}")
          apply (subgoal_tac "addrs as\<^sub>1 \<inter> new_mem s\<^sub>1 s\<^sub>2 = {}")
          apply (subgoal_tac "addrs as\<^sub>2 \<inter> new_mem s s\<^sub>1 = {}")
          subgoal apply (rule touches_nointer) by blast
          subgoal
            by (smt (verit, ccfv_threshold) DiffD2 Int_emptyI Un_commute new_mem_def addr_add addr_cover in_mono sup_ge1)
          subgoal
            by (smt (verit, del_insts) DiffD2 new_mem_def addr_add addr_cover disjoint_iff_not_equal subsetD sup.boundedE valid_trans_def)
          subgoal using addr_dj by presburger
          subgoal using new_mem_seq_dj by fastforce
          done
        subgoal for r\<^sub>2 i\<^sub>2 s\<^sub>2 as\<^sub>2'
          apply (rule exI[where x="as\<^sub>2'+as\<^sub>1'"])
          apply (intro conjI)
          subgoal by (meson sep_disj_addD2 sep_disj_addI1)
          subgoal by (metis sep_add_assoc sep_disj_addD)
          subgoal by (metis sep_add_commute sep_disj_addD1 sep_disj_commuteI)
          subgoal by (meson vt_trans)
          subgoal by (blast dest: new_mem_trans2)
          subgoal by (blast dest: new_mem_trans1)
        done
      done
    done
  done
    

  

  (* VCG setup *)
  
  definition "HT P c Q \<equiv> htriple P c Q"
  
  lemmas [vcg_decomp_rules] = ht_bind[folded HT_def]
  
  
  lemma HT_rule[vcg_decomp_rules]:
    "HT P c Q \<Longrightarrow> htriple P c Q" unfolding HT_def by simp

    
  (* TODO: Move *)    
  lemma HT_return[vcg_decomp_rules]: "ENTAILS P (Q x) \<Longrightarrow> HT P (return x) Q"
    unfolding HT_def
    by (smt (verit, best) ENTAILSD vt_refl bot_least entails_def htripleI touches0 wp_return)
      
  (*lemma cons_rule_vcg[vcg_decomp_rules]:
    assumes "HT P c Q'"
    assumes "\<And>r. ENTAILS (Q' r) (Q r)"
    shows "htriple P c (\<lambda>r. Q r)"
    using assms unfolding ENTAILS_def HT_def
    by (metis cons_rule entails_def)
  *)
  
  lemma cons_rule_ENT:
    assumes "HT P c Q"
    assumes "\<And>r. ENTAILS (Q r) (Q' r)"
    shows "HT P c Q'"
    by (smt (verit, best) HT_def ENTAILSD assms(1) assms(2) cons_rule entails_def)
  
    
  lemma frame_rule_vcg[vcg_frame_rules]:
    assumes "htriple P' c Q"
    assumes "PRECOND (FRAME P P' F)"
    shows "HT P c (\<lambda>r. Q r ** F)"
    unfolding HT_def
    apply (rule cons_rule)
    apply (rule frame_rule)
    apply fact
    using assms(2) unfolding PRECOND_def FRAME_INFER_def FRAME_def entails_def apply blast
    by blast

  lemma HT_extract_pre_pure1:
    assumes "\<Phi> \<Longrightarrow> HT P c Q"
    shows "HT (\<up>\<Phi> ** P) c Q"  
    using assms
    by (cases \<Phi>; simp add: sep_algebra_simps HT_def)

  lemma HT_extract_pre_pure2:
    assumes "\<Phi> \<Longrightarrow> HT \<box> c Q"
    shows "HT (\<up>\<Phi>) c Q"  
    using assms
    by (cases \<Phi>; simp add: sep_algebra_simps HT_def)
    
  lemmas HT_extract_pre_pure = HT_extract_pre_pure1 HT_extract_pre_pure2  
    
          
  lemma REC_rule: (* Needs annotation to be usable in automated setting! *)
    assumes WF: "wf V"
    assumes MONO: "\<And>x. M.mono_body (\<lambda>fa. B fa x)"
    assumes STEP: "\<And>D t x. \<lbrakk>\<And>t' x. (t',t)\<in>V \<Longrightarrow> htriple (P t' x ** F) (D x) (Q x) \<rbrakk> \<Longrightarrow> htriple (P t x ** F) (B D x) (Q x)"
    assumes INIT: "P' \<turnstile> P t x ** F"
    shows "htriple P' (REC B x) (Q x)"
  proof -  
      
    have "htriple (P t x ** F) (REC B x) (Q x)"
      using WF
      apply (induction t arbitrary: x)
      apply (subst REC_unfold[OF reflexive MONO])
      by (rule STEP)
    thus ?thesis
      apply (rule cons_rule)
      subgoal using INIT unfolding entails_def by simp
      subgoal .
      .
  qed
    
        
end

*)

end
