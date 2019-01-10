(* TODO: Move to Refine-Monadic *)
theory Refine_Monadic_Add
imports Refine_Monadic_Thin
begin

  definition "monadic_WHILEIT I b f s \<equiv> do {
    RECT (\<lambda>D s. do {
      ASSERT (I s);
      bv \<leftarrow> b s;
      if bv then do {
        s \<leftarrow> f s;
        D s
      } else do {RETURN s}
    }) s
  }"
  
  
  
  lemma WHILEIT_to_monadic: "WHILEIT I b f s = monadic_WHILEIT I (\<lambda>s. RETURN (b s)) f s"
    unfolding WHILEIT_def monadic_WHILEIT_def
    unfolding WHILEI_body_def bind_ASSERT_eq_if
    by (simp cong: if_cong)
  

lemma monadic_WHILEIT_refine[refine]:  
  assumes [refine]: "(s',s) \<in> R"
  assumes [refine]: "\<And>s' s. \<lbrakk> (s',s)\<in>R; I s \<rbrakk> \<Longrightarrow> I' s'"  
  assumes [refine]: "\<And>s' s. \<lbrakk> (s',s)\<in>R; I s; I' s' \<rbrakk> \<Longrightarrow> b' s' \<le>\<Down>bool_rel (b s)"
  assumes [refine]: "\<And>s' s. \<lbrakk> (s',s)\<in>R; I s; I' s'; nofail (b s); inres (b s) True \<rbrakk> \<Longrightarrow> f' s' \<le>\<Down>R (f s)"
  shows "monadic_WHILEIT I' b' f' s' \<le>\<Down>R (monadic_WHILEIT I b f s)"
  unfolding monadic_WHILEIT_def
  by (refine_rcg bind_refine'; assumption?; auto)
  
lemma monadic_WHILEIT_refine_WHILEIT[refine]:  
  assumes [refine]: "(s',s) \<in> R"
  assumes [refine]: "\<And>s' s. \<lbrakk> (s',s)\<in>R; I s \<rbrakk> \<Longrightarrow> I' s'"  
  assumes [THEN order_trans,refine_vcg]: "\<And>s' s. \<lbrakk> (s',s)\<in>R; I s; I' s' \<rbrakk> \<Longrightarrow> b' s' \<le> SPEC (\<lambda>r. r = b s)"
  assumes [refine]: "\<And>s' s. \<lbrakk> (s',s)\<in>R; I s; I' s'; b s \<rbrakk> \<Longrightarrow> f' s' \<le>\<Down>R (f s)"
  shows "monadic_WHILEIT I' b' f' s' \<le>\<Down>R (WHILEIT I b f s)"
  unfolding WHILEIT_to_monadic
  by (refine_vcg; assumption?; auto)
  
lemma monadic_WHILEIT_refine_WHILET[refine]:  
  assumes [refine]: "(s',s) \<in> R"
  assumes [THEN order_trans,refine_vcg]: "\<And>s' s. \<lbrakk> (s',s)\<in>R \<rbrakk> \<Longrightarrow> b' s' \<le> SPEC (\<lambda>r. r = b s)"
  assumes [refine]: "\<And>s' s. \<lbrakk> (s',s)\<in>R; b s \<rbrakk> \<Longrightarrow> f' s' \<le>\<Down>R (f s)"
  shows "monadic_WHILEIT (\<lambda>_. True) b' f' s' \<le>\<Down>R (WHILET b f s)"
  unfolding WHILET_def
  by (refine_vcg; assumption?)  



end
