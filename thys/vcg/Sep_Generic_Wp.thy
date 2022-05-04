theory Sep_Generic_Wp
imports 
  "../lib/Sep_Algebra_Add" 
  "../lib/Frame_Infer"
  "../lib/MM/MMonad"
begin


context intf_consistent_loc begin  
  
  lemma intf_r_alloc: "addr.block`r \<subseteq> Collect (is_ALLOC s) \<union> a"
    by (smt (verit, best) Un_def cell.exhaust_disc image_subset_iff intf_ref_not_freed intf_ref_not_fresh is_FRESH'_eq mem_Collect_eq sup_ge1)
  
  lemma intf_w_alloc: "addr.block`w \<subseteq> Collect (is_ALLOC s) \<union> a"
    by (smt (verit, best) Un_def cell.exhaust_disc image_subset_iff intf_ref_not_freed intf_ref_not_fresh is_FRESH'_eq mem_Collect_eq sup_ge1)

end

section \<open>General VCG Setup for Separation Logic\<close>

locale generic_wp =
  fixes wp :: "'c \<Rightarrow> ('r \<Rightarrow> intf \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> 's \<Rightarrow> bool"
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

hide_const (open) NEMonad.wp

definition wp where "wp c Q s \<equiv> NEMonad.wp (run c s) (\<lambda>(r,i,s). Q r i s)"

lemma pw_wp[pw_init]: "wp c Q s \<longleftrightarrow> \<not>is_fail (run c s) \<and> (\<forall>r i s'. is_res (run c s) (r,i,s') \<longrightarrow> Q r i s')"
  unfolding wp_def by pw


lemma wp_cons: "\<lbrakk> wp c Q s; \<And>r i s'. Q r i s' \<Longrightarrow> Q' r i s' \<rbrakk> \<Longrightarrow> wp c Q' s"  
  by pw
  
lemma wp_false[simp]: "\<not>wp c (\<lambda>_ _ _. False) s" by pw

interpretation generic_wp wp 
  apply unfold_locales 
  unfolding fun_eq_iff inf_fun_def inf_bool_def
  by pw

lemma wp_return[vcg_normalize_simps]: "wp (Mreturn x) Q s \<longleftrightarrow> Q x 0 s" by pw

lemma wp_fail[vcg_normalize_simps]: "\<not> wp (Mfail) Q s" by pw 

lemma wp_assert[vcg_normalize_simps]: "wp (Massert \<Phi>) Q s \<longleftrightarrow> \<Phi> \<and> Q () 0 s" by pw
  
lemma wp_bind[vcg_normalize_simps]: "wp (doM {x\<leftarrow>m; f x}) Q s = wp m (\<lambda>x i. wp (f x) (\<lambda>x' i'. Q x' (i+i'))) s"  
  by (pw; blast)
  
lemma wp_par:  
  assumes "wp m\<^sub>1 Q\<^sub>1 s"
  assumes "wp m\<^sub>2 Q\<^sub>2 s"
  assumes "\<And>r\<^sub>1 s\<^sub>1 i\<^sub>1 r\<^sub>2 s\<^sub>2 i\<^sub>2. \<lbrakk> 
      intf_consistent s i\<^sub>1 s\<^sub>1; intf_consistent s i\<^sub>2 s\<^sub>2; spar_feasible i\<^sub>1 i\<^sub>2;
      Q\<^sub>1 r\<^sub>1 i\<^sub>1 s\<^sub>1; Q\<^sub>2 r\<^sub>2 i\<^sub>2 s\<^sub>2 
    \<rbrakk> 
    \<Longrightarrow> intf_norace i\<^sub>1 i\<^sub>2 \<and> Q (r\<^sub>1,r\<^sub>2) (i\<^sub>1+i\<^sub>2) (combine_states s\<^sub>1 i\<^sub>2 s\<^sub>2)"
  shows "wp (Mpar m\<^sub>1 m\<^sub>2) Q s"
  using assms apply -
  apply pw 
  apply (meson res_run_consistentI)
  apply (meson res_run_consistentI)
  done
  
lemma wp_malloc[vcg_normalize_simps]: "wp (Mmalloc xs) Q s \<longleftrightarrow> (\<forall>r. is_FRESH s r \<longrightarrow> Q r (intf_a r) (addr_alloc xs r s))"  
  supply [pw_simp] = malloc_def
  by pw
  
lemma wp_free[vcg_normalize_simps]: "wp (Mfree b) Q s \<longleftrightarrow> is_ALLOC s b \<and> Q () (intf_f b) (addr_free b s)"  
  supply [pw_simp] = mfree_def
  by pw
  
lemma wp_load[vcg_normalize_simps]: "wp (Mload a) Q s \<longleftrightarrow> is_valid_addr s a \<and> Q (get_addr s a) (intf_r a) s"  
  supply [pw_simp] = mload_def
  by pw

lemma wp_mstore[vcg_normalize_simps]: "wp (Mstore a x) Q s \<longleftrightarrow> is_valid_addr s a \<and> Q () (intf_w a) (put_addr s a x)"  
  supply [pw_simp] = mstore_def
  by pw

lemma wp_valid_addr[vcg_normalize_simps]: "wp (Mvalid_addr a) Q s \<longleftrightarrow> is_valid_addr s a \<and> Q () (intf_r a) s"  
  supply [pw_simp] = mvalid_addr_def
  by pw
  
(*lemma wp_valid_ptr_addr[vcg_normalize_simps]: "wp (Mvalid_ptr_addr a) Q s \<longleftrightarrow> is_valid_ptr_addr s a \<and> Q () (intf_e (addr.block a)) s"  
  supply [pw_simp] = mvalid_ptr_addr_def
  by pw
*)    


locale abs_sep =  
  fixes \<alpha> :: "'v memory \<Rightarrow> 'a::{stronger_sep_algebra}"
    and addrs :: "'a \<Rightarrow> addr set"    (* Addresses *)
    and blocks :: "'a \<Rightarrow> block set"  (* Blocks *)
    and aget :: "'a \<Rightarrow> addr \<Rightarrow> 'v"   (* Modeled values *) 
    and bget :: "'a \<Rightarrow> block \<Rightarrow> nat" (* Modeled block sizes *)

  assumes disj_iff: "as\<^sub>1 ## as\<^sub>2 \<longleftrightarrow> (addrs as\<^sub>1 \<inter> addrs as\<^sub>2 = {} \<and> blocks as\<^sub>1 \<inter> blocks as\<^sub>2 = {})"
  assumes zero_char[simp]: "addrs 0 = {}" "blocks 0 = {}"
  assumes plus_char[simp]: "as\<^sub>1 ## as\<^sub>2 \<Longrightarrow> addrs (as\<^sub>1+as\<^sub>2) = addrs as\<^sub>1 \<union> addrs as\<^sub>2 \<and> blocks (as\<^sub>1+as\<^sub>2) = blocks as\<^sub>1 \<union> blocks as\<^sub>2"
    
  assumes aget_add: "as\<^sub>1 ## as\<^sub>2 \<Longrightarrow> a\<in>addrs as\<^sub>1 \<Longrightarrow> aget (as\<^sub>1 + as\<^sub>2) a = aget as\<^sub>1 a"
  assumes bget_add: "as\<^sub>1 ## as\<^sub>2 \<Longrightarrow> b\<in>blocks as\<^sub>1 \<Longrightarrow> bget (as\<^sub>1 + as\<^sub>2) b = bget as\<^sub>1 b"
  
  assumes complete: "\<lbrakk> A \<subseteq> Collect (is_valid_addr s); B \<subseteq> Collect (is_ALLOC s) \<rbrakk> \<Longrightarrow>
    \<exists>as\<^sub>1 as\<^sub>2. addrs as\<^sub>1 = A \<and> blocks as\<^sub>1 = B \<and> as\<^sub>1##as\<^sub>2 \<and> \<alpha> s = as\<^sub>1+as\<^sub>2"
  
  assumes \<alpha>_iff: "\<alpha> s = as \<longleftrightarrow> (
    addrs as = Collect (is_valid_addr s) \<and> blocks as = Collect (is_ALLOC s)
  \<and> (\<forall>a. is_valid_addr s a \<longrightarrow> aget as a = get_addr s a)  
  \<and> (\<forall>b. is_ALLOC s b \<longrightarrow> bget as b = block_size s b)
  )"
  
begin

  abbreviation "caddrs s \<equiv> Collect (is_valid_addr s)"
  abbreviation "cblocks s \<equiv> Collect (is_ALLOC s)"

  lemma aget_add': "as\<^sub>1 ## as\<^sub>2 \<Longrightarrow> a\<in>addrs as\<^sub>2 \<Longrightarrow> aget (as\<^sub>1 + as\<^sub>2) a = aget as\<^sub>2 a"
    by (metis aget_add sep_add_commute sep_disj_commuteI)
  
  lemma bget_add': "as\<^sub>1 ## as\<^sub>2 \<Longrightarrow> b\<in>blocks as\<^sub>2 \<Longrightarrow> bget (as\<^sub>1 + as\<^sub>2) b = bget as\<^sub>2 b"
    by (metis bget_add sep_add_commute sep_disj_commuteI)

  lemmas get_add = aget_add aget_add' bget_add bget_add'  
    
  lemma \<alpha>_simps:
    "addrs (\<alpha> s) = caddrs s"
    "blocks (\<alpha> s) = cblocks s"
    "is_valid_addr s a \<Longrightarrow> aget (\<alpha> s) a = get_addr s a"
    "is_ALLOC s b \<Longrightarrow> bget (\<alpha> s) b = block_size s b"
    using \<alpha>_iff[THEN iffD1, OF refl] by auto

  lemma \<alpha>_eqI: 
    assumes "addrs as = caddrs s" 
    assumes "blocks as = cblocks s"
    assumes "\<And>a. is_valid_addr s a \<longrightarrow> aget as a = get_addr s a"
    assumes "\<And>b. is_ALLOC s b \<longrightarrow> bget as b = block_size s b"
    shows "\<alpha> s = as"  
    apply (subst \<alpha>_iff) using assms by blast

  lemma complete': 
    assumes "A \<subseteq> caddrs s" "B \<subseteq> cblocks s" 
    obtains as\<^sub>1 as\<^sub>2 where
      "addrs as\<^sub>1 = A"
      "blocks as\<^sub>1 = B" 
      "addrs as\<^sub>2 = caddrs s - A"
      "blocks as\<^sub>2 = cblocks s - B"
      "as\<^sub>1##as\<^sub>2" 
      "\<alpha> s = as\<^sub>1+as\<^sub>2"
  proof -  
    from complete[OF assms] obtain as\<^sub>1 as\<^sub>2 where
      [simp]:
      "addrs as\<^sub>1 = A"
      "blocks as\<^sub>1 = B" 
      "\<alpha> s = as\<^sub>1+as\<^sub>2"
      and
      DJ: "as\<^sub>1##as\<^sub>2" 
      by blast
      
    from \<alpha>_simps[of s] DJ have 
      "A \<union> addrs as\<^sub>2 = caddrs s" 
      "B \<union> blocks as\<^sub>2 = cblocks s" 
      by (simp_all add: plus_char)
    with \<open>as\<^sub>1##as\<^sub>2\<close> have
      "addrs as\<^sub>2 = caddrs s - A"
      "blocks as\<^sub>2 = cblocks s - B"
      by (auto simp: disj_iff)
      
    show ?thesis
      apply rule
      by fact+
  qed
  
  
      
  (* Partial Characterization *)  
    
  (* As sep-logic *)
  definition "pchar as s \<equiv> \<exists>f. as##f \<and> \<alpha> s = as + f"
  
  (* Via concrete memory *)
  lemma pchar_alt: "pchar as s \<longleftrightarrow> (
    addrs as \<subseteq> caddrs s \<and> blocks as \<subseteq> cblocks s
  \<and> (\<forall>a\<in>addrs as. aget as a = get_addr s a)  
  \<and> (\<forall>b\<in>blocks as. bget as b = block_size s b)  
  )" 
  proof (rule, goal_cases)
    case 1
    then show ?case by (metis Int_Collect Un_Int_eq(3) \<alpha>_simps(1) \<alpha>_simps(2) \<alpha>_simps(3) \<alpha>_simps(4) aget_add bget_add inf_sup_ord(3) pchar_def plus_char)
  next
    case 2
    
    from complete'[of "addrs as" s  "blocks as"]
    obtain as\<^sub>1 as\<^sub>2 where
      "addrs as\<^sub>1 = addrs as" 
      "blocks as\<^sub>1 = blocks as"
      "addrs as\<^sub>2 = Collect (is_valid_addr s) - addrs as"
      "blocks as\<^sub>2 = {b. is_ALLOC s b} - blocks as"
      "as\<^sub>1 ## as\<^sub>2"
      and
      C1: "\<alpha> s = as\<^sub>1 + as\<^sub>2"
      using 2 by blast
      
    have "as ## as\<^sub>2"
      using \<open>addrs as\<^sub>1 = addrs as\<close> \<open>as\<^sub>1 ## as\<^sub>2\<close> \<open>blocks as\<^sub>1 = blocks as\<close> disj_iff by auto
      
    moreover have "\<alpha> s = as + as\<^sub>2" using C1
      unfolding \<alpha>_iff
      apply clarsimp
      by (smt (verit, ccfv_threshold) "2" Un_iff \<open>addrs as\<^sub>1 = addrs as\<close> \<open>as ## as\<^sub>2\<close> \<open>as\<^sub>1 ## as\<^sub>2\<close> \<open>blocks as\<^sub>1 = blocks as\<close> 
        aget_add' bget_add' mem_Collect_eq plus_char sep_add_commute sep_disj_commuteI)
    
    ultimately show ?case unfolding pchar_def by blast
  qed
  

  lemma pchar_completeI: 
    assumes "pchar as s"
    assumes "addrs as = caddrs s"
    assumes "blocks as = cblocks s"
    shows "\<alpha> s = as"
    using \<alpha>_eqI assms pchar_alt by auto
    
  lemma pchar_add: 
    assumes "pchar as\<^sub>1 s"
    assumes "pchar as\<^sub>2 s"
    assumes "as\<^sub>1 ## as\<^sub>2"
    shows "pchar (as\<^sub>1+as\<^sub>2) s"
    using assms
    unfolding pchar_alt
    by (auto simp: get_add)
  
    
  lemma pchar_xfer: 
    assumes "pchar as s" 
    assumes "\<forall>a\<in>addrs as. is_valid_addr s' a \<and> get_addr s' a = get_addr s a"
    assumes "\<forall>b\<in>blocks as. is_ALLOC s' b \<and> block_size s' b = block_size s b"
    shows "pchar as s'"
    using assms unfolding pchar_alt
    by auto
    
    
    
  lemma addrs_djI[intro]:
    "a##b \<Longrightarrow> x\<in>addrs a \<Longrightarrow> x\<notin>addrs b"  
    "a##b \<Longrightarrow> x\<in>addrs b \<Longrightarrow> x\<notin>addrs a"  
    by (auto simp: disj_iff)
    
  lemma blocks_djI[intro]:
    "a##b \<Longrightarrow> x\<in>blocks a \<Longrightarrow> x\<notin>blocks b"  
    "a##b \<Longrightarrow> x\<in>blocks b \<Longrightarrow> x\<notin>blocks a"  
    by (auto simp: disj_iff)

text \<open>Eliminating the interference, only maintaining a set of forbidden addresses\<close>  

definition "STATE asf P s \<equiv> \<exists>as. as ## asf \<and> \<alpha> s = as+asf \<and> P as"

definition "intf_excludes i asf 
  \<equiv> intf.r i \<union> intf.w i \<subseteq> -addrs asf \<and> intf.f i \<subseteq> - (addr.block`addrs asf \<union> blocks asf)"
    
lemma intf_excludes_simps[simp]:
  "intf_excludes 0 asf"  
  "intf_excludes i 0"  
  unfolding intf_excludes_def by auto
  
  
definition wpa where [pw_init]: "wpa asf c Q s \<equiv> wp c (\<lambda>r i s'. 
    Q r s' 
  \<and> intf_excludes i asf
) s"

lemma wpa_monoI:
  assumes "wpa A c Q s"
  assumes "\<And>r s'. \<lbrakk> Q r s' \<rbrakk> \<Longrightarrow> Q' r s'"
  assumes "blocks A' \<subseteq> blocks A" "addrs A' \<subseteq> addrs A"
  shows "wpa A' c Q' s"
  using assms unfolding wpa_def intf_excludes_def
  by (blast intro: wp_monoI)



definition "htriple P c Q \<equiv> (\<forall>s asf. STATE asf P s 
  \<longrightarrow> wpa asf c (\<lambda>r s'. STATE asf (Q r) s') s)"

lemma htripleI[intro?]:
  assumes "\<And>s asf. STATE asf P s \<Longrightarrow> wpa asf c (\<lambda>r s'. STATE asf (Q r) s') s"
  shows "htriple P c Q"
  using assms unfolding htriple_def by blast

lemma htripleD: 
  assumes "htriple P c Q"
  assumes "STATE asf P s"
  shows "wpa asf c (\<lambda>r s'. STATE asf (Q r) s') s"
  using assms unfolding htriple_def by blast


lemma wpa_false[vcg_normalize_simps]: "\<not>wpa A m (\<lambda>_ _. False) s"  
  by (simp add: wpa_def vcg_normalize_simps)

lemma wpa_return[vcg_normalize_simps]: "wpa asf (Mreturn x) Q s \<longleftrightarrow> Q x s" by pw

lemma wpa_fail[vcg_normalize_simps]: "\<not> wpa asf (Mfail) Q s" by pw 

lemma wpa_assert[vcg_normalize_simps]: "wpa asf (Massert \<Phi>) Q s \<longleftrightarrow> \<Phi> \<and> Q () s" by pw

lemma wpa_bindI[vcg_decomp_rules]: "wpa asf m (\<lambda>x. wpa asf (f x) Q) s \<Longrightarrow> wpa asf (doM {x\<leftarrow>m; f x}) Q s"  
  unfolding wpa_def intf_excludes_def
  apply (simp add: vcg_normalize_simps)
  apply (erule wp_cons)
  apply clarify
  apply (erule wp_cons)
  apply auto
  done
  
lemma wpa_ifI[vcg_decomp_rules]: 
  assumes "b \<Longrightarrow> wpa asf c Q s"
  assumes "\<not>b \<Longrightarrow> wpa asf e Q s"
  shows "wpa asf (if b then c else e) Q s"  
  using assms by auto
  
  
(* TODO: Move *)  
declare sep_disj_commuteI[sym]  
  

  lemma STATE_triv[simp]: "\<not>STATE asf sep_false s"
    by (simp add: STATE_def)
    
  lemma STATE_monoI: "STATE asf P s \<Longrightarrow> P \<turnstile> P' \<Longrightarrow> STATE asf P' s"  
    unfolding STATE_def entails_def by blast
    
  lemma STATE_frame1:
    "STATE asf (P**F) s \<Longrightarrow> \<exists>asf'. asf'##asf \<and> F asf' \<and> STATE (asf'+asf) P s"  
    unfolding STATE_def
    apply (auto simp: sep_algebra_simps sep_conj_def)
    by fastforce

  lemma STATE_frame2: 
    assumes "STATE (asf'+asf) P s"
    assumes "asf' ## asf"  
    assumes "F asf'"
    shows "STATE asf (P**F) s"
    using assms
    unfolding STATE_def
    apply (auto simp: sep_algebra_simps sep_conj_def) 
    by (metis assms(2) sep_add_assoc sep_add_commute sep_disj_add_eq)

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
    from htripleD[OF assms(1) this] have "wpa asf c (\<lambda>r. STATE asf (Q r)) s" .
    then show "wpa asf c (\<lambda>r. STATE asf (Q' r)) s"
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
    shows "wpa asf c Q' s"  
  proof -
    from STATE_frame1[OF assms(1)] obtain asf' where 
      D: "asf' ## asf" "F asf'" 
      and S: "STATE (asf' + asf) P s" 
      by blast
  
    from htripleD[OF assms(2) S] have "wpa (asf'+asf) c (\<lambda>r s'. STATE (asf' + asf) (Q r) s') s" .
    moreover have "\<lbrakk>STATE (asf' + asf) (Q r) s'\<rbrakk> \<Longrightarrow> STATE asf (Q r ** F) s'" for r s'
      by (rule STATE_frame2; (assumption|rule D)?)
    ultimately have "wpa (asf)  c (\<lambda>r s'. STATE asf (Q r ** F) s') s"
      apply (rule wpa_monoI) by (auto simp: D)
    then show ?thesis using assms(3)
      by (rule wpa_monoI) auto
  qed

        
  lemma frame_rule: "htriple P c Q \<Longrightarrow> htriple (P ** F) c (\<lambda>r. Q r ** F)"
    apply rule
    apply (erule apply_htriple_rule)
    .
    
    
(* This rule is used to show disjointness in the lemma below.
  Just using blast there will be inefficient due to big terms.
*)    
lemma dj_subsetXI:    
  assumes "a\<subseteq>a\<^sub>1\<union>a\<^sub>2"
  assumes "b\<subseteq>b\<^sub>1\<union>b\<^sub>2"
  assumes "a\<^sub>1\<inter>b\<^sub>1 = {}"
  assumes "a\<^sub>1\<inter>b\<^sub>2 = {}"
  assumes "a\<^sub>2\<inter>b\<^sub>1 = {}"
  assumes "a\<^sub>2\<inter>b\<^sub>2 = {}"
  shows "a\<inter>b = {}"
  using assms
  by blast  
  
    
lemma ht_par:
  assumes HT1: "htriple P\<^sub>1 m\<^sub>1 Q\<^sub>1"
  assumes HT2: "htriple P\<^sub>2 m\<^sub>2 Q\<^sub>2"
  shows "htriple (P\<^sub>1**P\<^sub>2) (m\<^sub>1 \<parallel>\<^sub>M m\<^sub>2) (\<lambda>(r\<^sub>1,r\<^sub>2). Q\<^sub>1 r\<^sub>1 ** Q\<^sub>2 r\<^sub>2)"
proof
  fix s asf
  
  \<comment> \<open>Precondition\<close>
  assume "STATE asf (P\<^sub>1 \<and>* P\<^sub>2) s"
  then obtain as\<^sub>1 as\<^sub>2 where 
        [simp]: "as\<^sub>1 ## as\<^sub>2" "(as\<^sub>1 + as\<^sub>2) ## asf" 
    and S_SPLIT: "\<alpha> s = as\<^sub>1 + as\<^sub>2 + asf" 
    and PRECOND[simp]: "P\<^sub>1 as\<^sub>1" "P\<^sub>2 as\<^sub>2"
    unfolding STATE_def by (auto simp: sep_conj_def)

  have [simp, symmetric, simp]: "as\<^sub>1 ## asf" "as\<^sub>2 ## asf"
    using \<open>as\<^sub>1 ## as\<^sub>2\<close> \<open>as\<^sub>1 + as\<^sub>2 ## asf\<close> sep_add_disjD apply blast
    using \<open>as\<^sub>1 ## as\<^sub>2\<close> \<open>as\<^sub>1 + as\<^sub>2 ## asf\<close> sep_add_disjD apply blast
    done   

  \<comment> \<open>Addresses breakdown on concrete level\<close>    
  have CA_SPLIT: "caddrs s = addrs as\<^sub>1 \<union> addrs as\<^sub>2 \<union> addrs asf"  
    and CB_SPLIT: "cblocks s = blocks as\<^sub>1 \<union> blocks as\<^sub>2 \<union> blocks asf"
    using S_SPLIT by (simp_all flip: \<alpha>_simps)
    
  have ADDRS_DJ: 
    "addrs as\<^sub>1 \<inter> addrs as\<^sub>2 = {}"  
    "addrs as\<^sub>1 \<inter> addrs asf = {}"  
    "addrs as\<^sub>2 \<inter> addrs asf = {}"  
  and BLOCKS_DJ:   
    "blocks as\<^sub>1 \<inter> blocks as\<^sub>2 = {}"  
    "blocks as\<^sub>1 \<inter> blocks asf = {}"  
    "blocks as\<^sub>2 \<inter> blocks asf = {}"  
    using disj_iff by force+
          
  \<comment> \<open>Re-shuffle to get frames\<close>
  have S1: "STATE (as\<^sub>2 + asf) P\<^sub>1 s"  
    unfolding STATE_def by (auto simp: sep_conj_def sep_algebra_simps S_SPLIT intro!: exI[where x="as\<^sub>1"])
    
  have S2: "STATE (as\<^sub>1 + asf) P\<^sub>2 s"  
    unfolding STATE_def by (auto simp: sep_conj_def sep_algebra_simps S_SPLIT intro!: exI[where x="as\<^sub>2"])

  \<comment> \<open>Executions\<close>  
  note WPA1 = htripleD[OF HT1 S1]
  note WPA2 = htripleD[OF HT2 S2]
  
  \<comment> \<open>Break down \<open>wpa\<close>\<close>
  show "wpa asf (m\<^sub>1 \<parallel>\<^sub>M m\<^sub>2) (\<lambda>r. STATE asf (case r of (r\<^sub>1, r\<^sub>2) \<Rightarrow> Q\<^sub>1 r\<^sub>1 \<and>* Q\<^sub>2 r\<^sub>2)) s"
    using WPA1 WPA2
    apply (simp add: wpa_def)
    apply (erule (1) wp_par, thin_tac "wp _ _ _"; clarsimp)
  proof goal_cases
    case (1 x\<^sub>1 s\<^sub>1 i\<^sub>1 x\<^sub>2 s\<^sub>2 i\<^sub>2)

    \<comment> \<open>Make assumptions explicit\<close>
    
    interpret feasible_parallel_execution s s\<^sub>1 i\<^sub>1 s\<^sub>2 i\<^sub>2 using 1 apply unfold_locales by simp_all

    note STATE1 = \<open>STATE (as\<^sub>2 + asf) (Q\<^sub>1 x\<^sub>1) s\<^sub>1\<close>
    note STATE2 = \<open>STATE (as\<^sub>1 + asf) (Q\<^sub>2 x\<^sub>2) s\<^sub>2\<close>
    note IEXCL1 = \<open>intf_excludes i\<^sub>1 (as\<^sub>2 + asf)\<close>
    note IEXCL2 = \<open>intf_excludes i\<^sub>2 (as\<^sub>1 + asf)\<close>

    
    from IEXCL1 IEXCL2 have G_EXCL: "intf_excludes (i\<^sub>1 + i\<^sub>2) asf"
      unfolding intf_excludes_def
      by auto
        
      
      
    \<comment> \<open>Prove race freedom\<close>
    have G1: "intf_norace i\<^sub>1 i\<^sub>2"
    proof -
    
      text \<open>From consistency, we know that interference only talks about valid addresses.
        Note that the allocated addresses are on over-approximation here
      \<close>
      have SS1: "r\<^sub>1 \<union> w\<^sub>1 \<subseteq> addrs as\<^sub>1 \<union> c1.allocated_addrs_approx" "f\<^sub>1 \<subseteq> blocks as\<^sub>1 \<union> a\<^sub>1"
        using c1.rw_valid_or_alloc IEXCL1 ADDRS_DJ c1.f_valid_or_alloc BLOCKS_DJ
        unfolding CA_SPLIT CB_SPLIT intf_excludes_def
        by auto
        
      have SS2: "r\<^sub>2 \<union> w\<^sub>2 \<subseteq> addrs as\<^sub>2 \<union> c2.allocated_addrs_approx" "f\<^sub>2 \<subseteq> blocks as\<^sub>2 \<union> a\<^sub>2"
        using c2.rw_valid_or_alloc IEXCL2 ADDRS_DJ c2.f_valid_or_alloc BLOCKS_DJ
        unfolding CA_SPLIT CB_SPLIT intf_excludes_def
        by auto
    
      text \<open>The allocations are disjoint by feasibility assumption\<close>  
      note alloc_addrs_disj alloc_disj
      
      text \<open>The allocations are disjoint from the original addresses by consistency\<close>
      from c1.a_dj_valid c1.a_dj_alloc c2.a_dj_valid c2.a_dj_alloc
      have ORIG_DJ: 
        "(addrs as\<^sub>1 \<union> addrs as\<^sub>2) \<inter> (c1.allocated_addrs_approx \<union> c2.allocated_addrs_approx) = {}"
        "(blocks as\<^sub>1 \<union> blocks as\<^sub>2) \<inter> (a\<^sub>1 \<union> a\<^sub>2) = {}"
        unfolding CA_SPLIT CB_SPLIT by blast+
        
      note ADDRS_DJ BLOCKS_DJ
      
      have G1: "(r\<^sub>1\<union>w\<^sub>1) \<inter> (r\<^sub>2\<union>w\<^sub>2) = {}"
        apply (rule dj_subsetXI, fact, fact, fact)
        using ORIG_DJ apply blast
        using ORIG_DJ apply blast
        using alloc_addrs_approx_disj .
        
      have G2: "f\<^sub>1\<inter>f\<^sub>2={}" 
        apply (rule dj_subsetXI, fact, fact, fact)
        using ORIG_DJ apply blast
        using ORIG_DJ apply blast
        by fact
        
      note c1.rw_valid_or_alloc
      note IEXCL1  
        
      have G3: "addr.block`(r\<^sub>1\<union>w\<^sub>1) \<inter> f\<^sub>2 = {}"
      proof -
        have "f\<^sub>2 \<subseteq> -addr.block`(addrs as\<^sub>1 \<union> addrs asf)"  
          using IEXCL2 unfolding intf_excludes_def by simp
        moreover have "addr.block`(r\<^sub>1\<union>w\<^sub>1) \<subseteq> addr.block`(addrs as\<^sub>1 \<union> addrs asf) \<union> a\<^sub>1"  
          using SS1(1) by auto
        ultimately show ?thesis  
          using alloc_free_dj
          by blast
      qed  

      have G4: "addr.block`(r\<^sub>2\<union>w\<^sub>2) \<inter> f\<^sub>1 = {}"
      proof -
        have "f\<^sub>1 \<subseteq> -addr.block`(addrs as\<^sub>2 \<union> addrs asf)"  
          using IEXCL1 unfolding intf_excludes_def by simp
        moreover have "addr.block`(r\<^sub>2\<union>w\<^sub>2) \<subseteq> addr.block`(addrs as\<^sub>2 \<union> addrs asf) \<union> a\<^sub>2"  
          using SS2(1) by auto
        ultimately show ?thesis  
          using free_alloc_dj
          by blast
      qed  
        
      show "intf_norace i\<^sub>1 i\<^sub>2"
        unfolding intf_norace_def Let_def
        apply simp
        using G1 G2 G3 G4
        by blast
        
    qed
        
        
    \<comment> \<open>Now we have a valid parallel execution\<close>  
    interpret valid_parallel_execution s s\<^sub>1 i\<^sub>1 s\<^sub>2 i\<^sub>2 apply unfold_locales by fact+
    
    have G2: "STATE asf (Q\<^sub>1 x\<^sub>1 \<and>* Q\<^sub>2 x\<^sub>2) s'" 
    proof -
    
      note \<open>STATE (as\<^sub>2 + asf) (Q\<^sub>1 x\<^sub>1) s\<^sub>1\<close> \<open>STATE (as\<^sub>1 + asf) (Q\<^sub>2 x\<^sub>2) s\<^sub>2\<close>
      then obtain as\<^sub>1' as\<^sub>2' where 
            A12_FMT:
        "\<alpha> s\<^sub>1 = as\<^sub>1' + as\<^sub>2 + asf"
        "\<alpha> s\<^sub>2 = as\<^sub>1 + as\<^sub>2' + asf"
        and ASx'_DJS:
        "as\<^sub>1' ## (as\<^sub>2 + asf)"
        "as\<^sub>2' ## (as\<^sub>1 + asf)"
        and 
        "Q\<^sub>1 x\<^sub>1 as\<^sub>1'"
        "Q\<^sub>2 x\<^sub>2 as\<^sub>2'"
        unfolding STATE_def
        by (auto simp: sep_algebra_simps )
    
      from ASx'_DJS have [simp, symmetric, simp]:
        "as\<^sub>1' ## as\<^sub>2"  
        "as\<^sub>1' ## asf"  
        "as\<^sub>2' ## as\<^sub>1"  
        "as\<^sub>2' ## asf"  
        by auto
        
      \<comment> \<open>Addresses breakdown on concrete level\<close>    
      have CA'_SPLIT: 
          "caddrs s\<^sub>1 = addrs as\<^sub>1' \<union> addrs as\<^sub>2 \<union> addrs asf"  
          "caddrs s\<^sub>2 = addrs as\<^sub>1 \<union> addrs as\<^sub>2' \<union> addrs asf"  
        and CB'_SPLIT: 
          "cblocks s\<^sub>1 = blocks as\<^sub>1' \<union> blocks as\<^sub>2 \<union> blocks asf"
          "cblocks s\<^sub>2 = blocks as\<^sub>1 \<union> blocks as\<^sub>2' \<union> blocks asf"
        using A12_FMT by (simp_all flip: \<alpha>_simps)
        
      have ADDRS'_DJ: 
        "addrs as\<^sub>1' \<inter> addrs as\<^sub>2 = {}" 
        "addrs as\<^sub>1' \<inter> addrs asf = {}" 
        "addrs as\<^sub>2' \<inter> addrs as\<^sub>1 = {}" 
        "addrs as\<^sub>2' \<inter> addrs asf = {}" 
        using disj_iff by force+
        
      have BLOCKS'_DJ: 
        "blocks as\<^sub>1' \<inter> blocks as\<^sub>2 = {}" 
        "blocks as\<^sub>1' \<inter> blocks asf = {}" 
        "blocks as\<^sub>2' \<inter> blocks as\<^sub>1 = {}" 
        "blocks as\<^sub>2' \<inter> blocks asf = {}" 
        using disj_iff by force+
        
      have AS1'_EQ: "addrs as\<^sub>1' = addrs as\<^sub>1 \<union> c1.allocated_addrs - c1.freed_addrs"
        apply auto
        subgoal using ADDRS'_DJ(1) ADDRS'_DJ(2) CA'_SPLIT(1) CA_SPLIT c1.allocated_addrs_def by auto
        subgoal using CA'_SPLIT(1) c1.valid_s'_alt' by auto
        subgoal using ADDRS_DJ(1) ADDRS_DJ(2) CA'_SPLIT(1) CA_SPLIT c1.freed_addrs_def by auto
        subgoal by (metis CA'_SPLIT(1) CA_SPLIT DiffD2 UnE UnI2 c1.allocated_addrs_def c1.valid_s'_alt inf_sup_aci(5))
        done
      
      have AS2'_EQ: "addrs as\<^sub>2' = addrs as\<^sub>2 \<union> c2.allocated_addrs - c2.freed_addrs"
        apply auto
        subgoal using ADDRS'_DJ(3) ADDRS'_DJ(4) CA'_SPLIT(2) CA_SPLIT c2.allocated_addrs_def by auto
        subgoal by (simp add: CA'_SPLIT(2) c2.freed_addrs_def)
        subgoal using CA'_SPLIT(2) CA_SPLIT \<open>as\<^sub>1 ## as\<^sub>2\<close> \<open>asf ## as\<^sub>2\<close> addrs_djI(2) c2.freed_addrs_def by force
        subgoal using CA'_SPLIT(2) CA_SPLIT c2.allocated_addrs_def by force
        done

      have CB1_EQ: "cblocks s\<^sub>1 = cblocks s \<union> a\<^sub>1 - f\<^sub>1"  
        by (auto simp: c1.is_ALLOC'_eq)

      have CB2_EQ: "cblocks s\<^sub>2 = cblocks s \<union> a\<^sub>2 - f\<^sub>2"  
        by (auto simp: c2.is_ALLOC'_eq)
        
                
      have B1'_EQ: "blocks as\<^sub>1' = blocks as\<^sub>1 \<union> a\<^sub>1 - f\<^sub>1" 
        apply (auto simp: )
        subgoal using BLOCKS'_DJ(1) BLOCKS'_DJ(2) CB'_SPLIT(1) CB_SPLIT c1.is_ALLOC'_eq by auto
        subgoal using CB'_SPLIT(1) c1.is_FREED'_eq by blast
        subgoal using BLOCKS_DJ(1) BLOCKS_DJ(2) CB'_SPLIT(1) CB_SPLIT c1.is_ALLOC'_eq by auto
        subgoal using CB'_SPLIT(1) CB_SPLIT c1.a_dj_alloc c1.is_ALLOC'_eq by auto
        done

      have B2'_EQ: "blocks as\<^sub>2' = blocks as\<^sub>2 \<union> a\<^sub>2 - f\<^sub>2" 
        apply (auto simp: )
        subgoal using BLOCKS'_DJ(3,4) CB'_SPLIT(2) CB_SPLIT c2.is_ALLOC'_eq by auto
        subgoal using CB'_SPLIT(2) c2.is_FREED'_eq by blast
        subgoal using BLOCKS_DJ CB'_SPLIT(2) CB_SPLIT c2.is_ALLOC'_eq by auto
        subgoal using CB'_SPLIT(2) CB_SPLIT c2.a_dj_alloc c2.is_ALLOC'_eq by auto
        done

                
      \<comment> \<open>The new abstract state covers exactly the addresses of the concrete state\<close>  
      have COVERAGE: 
        "caddrs s' = addrs as\<^sub>1' \<union> addrs as\<^sub>2' \<union> addrs asf"
        "cblocks s' = blocks as\<^sub>1' \<union> blocks as\<^sub>2' \<union> blocks asf"
      proof -
          
        have "caddrs s' = (caddrs s\<^sub>1 - c2.freed_addrs) \<union> (caddrs s\<^sub>2 - c1.freed_addrs)"  
          by (simp add: valid_addr'')
        also note c1.valid_s'_alt'  
        also note c2.valid_s'_alt'  
        finally have "caddrs s' = (caddrs s \<union> c1.allocated_addrs \<union> c2.allocated_addrs) - c1.freed_addrs - c2.freed_addrs" by blast
        also note CA_SPLIT
        also have "(addrs as\<^sub>1 \<union> addrs as\<^sub>2 \<union> addrs asf \<union> c1.allocated_addrs \<union> c2.allocated_addrs) - c1.freed_addrs - c2.freed_addrs
          = (addrs as\<^sub>1 \<union> c1.allocated_addrs - c1.freed_addrs) 
          \<union> (addrs as\<^sub>2 \<union> c2.allocated_addrs - c2.freed_addrs)
          \<union> addrs asf"
          apply auto
          subgoal using CA'_SPLIT(1) c1.valid_s'_alt' by auto
          subgoal using alloc_freed_addrs_disj(2) by auto
          subgoal by (simp add: CA'_SPLIT(1) c1.freed_addrs_def)
          subgoal by (simp add: CA'_SPLIT(2) c2.freed_addrs_def)
          subgoal using alloc_freed_addrs_disj(1) by blast
          subgoal using CA'_SPLIT(2) c2.valid_s'_alt' by auto
          done
        also note AS1'_EQ[symmetric]   
        also note AS2'_EQ[symmetric]
        finally show "caddrs s' = addrs as\<^sub>1' \<union> addrs as\<^sub>2' \<union> addrs asf" .
      
        have "cblocks s' = (cblocks s\<^sub>1 - f\<^sub>2) \<union> (cblocks s\<^sub>2 - f\<^sub>1)"
          by (auto simp: is_ALLOC'_eq c1.is_ALLOC'_eq c2.is_ALLOC'_eq)
        also note CB1_EQ
        also note CB2_EQ
        finally have "cblocks s' = cblocks s \<union> a\<^sub>1 \<union> a\<^sub>2 - f\<^sub>1 - f\<^sub>2"
          by auto
        also note CB_SPLIT
        also have "blocks as\<^sub>1 \<union> blocks as\<^sub>2 \<union> blocks asf \<union> a\<^sub>1 \<union> a\<^sub>2 - f\<^sub>1 - f\<^sub>2
          = (blocks as\<^sub>1 \<union> a\<^sub>1 - f\<^sub>1) \<union> (blocks as\<^sub>2 \<union> a\<^sub>2 - f\<^sub>2) \<union> blocks asf"
          apply auto
          subgoal using CB'_SPLIT(1) c1.is_ALLOC'_eq by auto
          subgoal using free_alloc_dj by blast
          subgoal using CB'_SPLIT(1) CB1_EQ by blast
          subgoal using CB'_SPLIT(2) CB2_EQ by blast
          subgoal using alloc_free_dj by auto
          subgoal using CB'_SPLIT(2) CB2_EQ by blast
          done
        also note B1'_EQ[symmetric]
        also note B2'_EQ[symmetric]
        finally show "cblocks s' = blocks as\<^sub>1' \<union> blocks as\<^sub>2' \<union> blocks asf" .
      qed  
      
      \<comment> \<open>The abstract states from both sides are disjoint\<close>  
      have DISJOINT[simp]: "as\<^sub>1' ## as\<^sub>2'" 
        apply (simp add: disj_iff)
        using ADDRS_DJ BLOCKS_DJ
        apply (auto simp: AS1'_EQ AS2'_EQ B1'_EQ B2'_EQ)
        subgoal using CA_SPLIT c2.allocated_addrs_def by auto
        subgoal by (simp add: CA_SPLIT c1.allocated_addrs_def)
        subgoal by (meson alloc_addrs_disj disjoint_iff)
        subgoal by (metis B2'_EQ Diff_iff IntD1 Un_Int_eq(2) \<open>as\<^sub>1 ## as\<^sub>2'\<close> blocks_djI(1))
        subgoal by (metis B1'_EQ DiffI Un_upper2 \<open>as\<^sub>2 ## as\<^sub>1'\<close> blocks_djI(1) subset_iff)
        subgoal by (meson alloc_disj disjoint_iff)
        done


      \<comment> \<open>The new abstract states characterize their concrete counterparts.
        In the rest of this proof, we will transfer these to \<open>s'\<close>, using
        the fact that \<open>s'\<close> is equal to \<open>s\<^sub>1\<close>/\<open>s\<^sub>2\<close>/\<open>asf\<close> on the relevant addresses
       \<close>  
      have "pchar as\<^sub>1' s\<^sub>1" "pchar asf s\<^sub>1" "pchar as\<^sub>2' s\<^sub>2"  
        unfolding pchar_def
        by (auto simp: A12_FMT sep_algebra_simps 
          intro: exI[where x="as\<^sub>2+asf"] exI[where x="as\<^sub>1+asf"] exI[where x="as\<^sub>1'+as\<^sub>2"]
        )
        
        
                
      have "pchar as\<^sub>1' s'"
        apply (rule pchar_xfer[OF \<open>pchar as\<^sub>1' s\<^sub>1\<close>]; intro ballI conjI)
      proof -
      
        from IEXCL2 have "addrs as\<^sub>1 \<inter> w\<^sub>2 = {}"  
          unfolding intf_excludes_def by auto
        then have "addrs as\<^sub>1' \<inter> (w\<^sub>2) = {}" 
          apply (auto simp add: AS1'_EQ)
          by (smt (verit, ccfv_threshold) Un_iff alloc_disj c1.allocated_addrs_approx c1.valid_s_not_alloc c2.rw_valid_or_alloc disjoint_iff mem_Collect_eq subset_eq)
        
        have "addr.block`addrs as\<^sub>1' \<inter> a\<^sub>2 = {}"
          apply (auto simp add: AS1'_EQ)
          subgoal using CA_SPLIT c2.a_dj_valid by auto
          subgoal using alloc_disj c1.allocated_addrs_approx by blast
          done
          
        fix a 
        assume A: "a \<in> addrs as\<^sub>1'"
        thus "is_valid_addr s' a"
          using  CA'_SPLIT COVERAGE(1)
          by (auto simp:)
        thus "get_addr s' a = get_addr s\<^sub>1 a" 
          using A \<open>addrs as\<^sub>1' \<inter> (w\<^sub>2) = {}\<close> \<open>addr.block`addrs as\<^sub>1' \<inter> a\<^sub>2 = {}\<close>
          by (auto simp add: get_addr_combine)
      next
        fix b
        assume A: "b \<in> blocks as\<^sub>1'"
        thus "is_ALLOC s' b"
          using CB'_SPLIT COVERAGE(2) by auto
        show "block_size s' b = block_size s\<^sub>1 b"
          (* TODO: That's a generic lemma from valid-combination! *)
          by (metis A UnCI \<open>is_ALLOC s' b\<close> \<open>pchar as\<^sub>1' s\<^sub>1\<close> block_size_combine c2.is_FREED'_eq cell.disc(2) combine_states_def is_FREED'_eq pchar_alt subset_Collect_conv)
      qed    

      moreover
      
      have "pchar asf s'"
        apply (rule pchar_xfer[OF \<open>pchar asf s\<^sub>1\<close>]; intro ballI conjI)
      proof -
      
        from IEXCL2 have "addrs asf \<inter> w\<^sub>2 = {}"  
          unfolding intf_excludes_def by auto
        
        have \<open>addr.block`addrs asf \<inter> a\<^sub>2 = {}\<close>
          using c2.a_dj_valid
          unfolding CA_SPLIT by blast
      
        fix a
        assume A: "a \<in> addrs asf"
        thus "is_valid_addr s' a"
          using \<open>caddrs s' = addrs as\<^sub>1' \<union> addrs as\<^sub>2' \<union> addrs asf\<close> by blast
        thus "get_addr s' a = get_addr s\<^sub>1 a" 
          using A \<open>addrs asf \<inter> (w\<^sub>2) = {}\<close> \<open>addr.block`addrs asf \<inter> a\<^sub>2 = {}\<close>
          by (auto simp add: get_addr_combine)
      next
        fix b
        assume A: "b \<in> blocks asf"
        thus "is_ALLOC s' b"
          using CB'_SPLIT COVERAGE(2) by auto
        show "block_size s' b = block_size s\<^sub>1 b"
          (* TODO: That's a generic lemma from valid-combination! *)
          by (metis A CB'_SPLIT(1) UnI2 Un_upper2 \<open>is_ALLOC s' b\<close> block_size_combine c2.is_FREED'_eq combine_states_def is_ALLOC_conv is_FREED'_eq subset_Collect_conv)
      qed    
        
      moreover
      
      have "pchar as\<^sub>2' s'"
        apply (rule pchar_xfer[OF \<open>pchar as\<^sub>2' s\<^sub>2\<close>]; intro ballI conjI)
      proof -
      
        from IEXCL1 have "addrs as\<^sub>2 \<inter> w\<^sub>1 = {}"  
          unfolding intf_excludes_def by auto
        then have "addrs as\<^sub>2' \<inter> (w\<^sub>1) = {}" 
          apply (auto simp add: AS2'_EQ)
          by (smt (verit, ccfv_threshold) Un_iff alloc_blocks_def alloc_disj c1.intf_w_alloc c1.rw_valid_s c2.allocated_addrs_approx c2.intf_a_alloc disjoint_iff fresh_freed_not_valid(1) image_subset_iff mem_Collect_eq subset_iff)
        
        have "addr.block`addrs as\<^sub>2' \<inter> a\<^sub>1 = {}"
          apply (auto simp add: AS2'_EQ)
          subgoal using CA_SPLIT c1.a_dj_valid by auto
          subgoal using alloc_disj c2.allocated_addrs_approx by blast
          done
      
        fix a 
        assume A: "a \<in> addrs as\<^sub>2'"
        
        from A show "is_valid_addr s' a"
          using  CA'_SPLIT COVERAGE(1)
          by (auto simp:)
        thus "get_addr s' a = get_addr s\<^sub>2 a" 
          using A \<open>addrs as\<^sub>2' \<inter> (w\<^sub>1) = {}\<close> \<open>addr.block`addrs as\<^sub>2' \<inter> a\<^sub>1 = {}\<close>
          apply (auto simp add: get_addr_combine)
          apply (subst valid_addr'_outside_wa_eq_orig[of a]; auto?)
          apply (subst valid_addr'_outside_wa_eq_orig[of a]; auto?)
          done
      next
        fix b
        assume A: "b \<in> blocks as\<^sub>2'"
        thus "is_ALLOC s' b"
          using CB'_SPLIT COVERAGE(2) by auto
        show "block_size s' b = block_size s\<^sub>2 b"
          (* TODO: That's a generic lemma from valid-combination! *)
          by (metis (no_types, lifting) A UnCI \<open>is_ALLOC s' b\<close> \<open>pchar as\<^sub>2' s\<^sub>2\<close> block_size_combine c1.is_FREED'_eq combine_states_def is_ALLOC_conv is_FREED'_eq par_blocks_same_length pchar_alt subset_Collect_conv)
      qed    
      
      ultimately
      
      have "pchar (as\<^sub>1' + as\<^sub>2' + asf) s'"
        apply (intro pchar_add)
        by simp_all
        
      \<comment> \<open>As these addresses cover all of \<open>s'\<close>, we can write the abstraction of \<open>s'\<close> accordingly\<close>
      from pchar_completeI[OF this] COVERAGE have "\<alpha> s' = as\<^sub>1' + as\<^sub>2' + asf" by simp
      
      \<comment> \<open>From the correctness of the parallel strands, and disjointness of \<open>as\<^sub>1' ## as\<^sub>2'\<close>,
        we get that both postconditions hold simultaneously
      \<close>
      moreover have "(Q\<^sub>1 x\<^sub>1 ** Q\<^sub>2 x\<^sub>2) (as\<^sub>1' + as\<^sub>2')"
        by (meson \<open>Q\<^sub>1 x\<^sub>1 as\<^sub>1'\<close> \<open>Q\<^sub>2 x\<^sub>2 as\<^sub>2'\<close> \<open>as\<^sub>1' ## as\<^sub>2'\<close> sep_conjI)
      
      ultimately show ?thesis
        unfolding STATE_def apply -
        apply (rule exI[where x = "as\<^sub>1' + as\<^sub>2'"])
        apply (simp)
        done
    qed    
    
    show ?case using G1 G2 G_EXCL by blast
  qed 
qed        
   

  
subsection \<open>Realizable abstract Predicates\<close>    
  definition "realizable P \<equiv> \<exists>s as asf. P as \<and> \<alpha> s = as + asf \<and> as ## asf"
  
  lemma realizable_conjD: "realizable (P**Q) \<Longrightarrow> realizable P \<and> realizable Q"
    apply (clarsimp simp: realizable_def sep_conj_def sep_algebra_simps sep_conj_c; intro conjI)
    subgoal for s x asf y
      apply (rule exI[where x=s])
      apply (rule exI[where x="x"])
      apply simp
      apply (rule exI[where x="asf+y"])
      by simp
    
    subgoal for s x asf y
      apply (rule exI[where x=s])
      apply (rule exI[where x="y"])
      apply simp
      apply (rule exI[where x="asf+x"])
      by (simp add: sep_algebra_simps)
      
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
    shows "wpa asf c Q' s"
  proof -
    from S F have S': "STATE asf (P**F) s"
      unfolding PRECOND_def FRAME_def
      using STATE_monoI by blast

    show ?thesis
      apply (rule apply_htriple_rule[OF S' HT])
      using P unfolding vcg_tag_defs .
      
  qed    
  
  lemma htriple_vcgI': 
    assumes "\<And>asf s. STATE asf P s \<Longrightarrow> wpa asf c (\<lambda>r. POSTCOND asf (Q r)) s"
    shows "htriple P c Q"
    apply (rule htripleI)
    using assms unfolding vcg_tag_defs .
  
  lemma htriple_vcgI[htriple_vcg_intros]: 
    assumes "\<And>asf s. STATE asf P s \<Longrightarrow> EXTRACT (wpa asf c (\<lambda>r s. EXTRACT (POSTCOND asf (Q r) s)) s)"
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

end
