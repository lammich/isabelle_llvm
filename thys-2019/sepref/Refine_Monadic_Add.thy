(* TODO: Move to Refine-Monadic *)
theory Refine_Monadic_Add
imports Refine_Monadic_Thin
begin

  lemma bind_res_singleton[simp]: "bind (RES {x}) f = f x"
    by (auto simp: pw_eq_iff refine_pw_simps)



  lemma option_rel_inv_conv:
    "(x,Some v')\<in>\<langle>V\<rangle>option_rel \<longleftrightarrow> (\<exists>v. x=Some v \<and> (v,v')\<in>V)"
    "(Some v,x')\<in>\<langle>V\<rangle>option_rel \<longleftrightarrow> (\<exists>v'. x'=Some v' \<and> (v,v')\<in>V)"
    subgoal by (cases x; auto)
    subgoal by (cases x'; auto)
    done



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


(* TODO: Move *)    
lemma monadic_WHILEIT_unfold:
  "monadic_WHILEIT I b f s = do { ASSERT (I s); bb\<leftarrow>b s; if bb then do { s \<leftarrow> f s; monadic_WHILEIT I b f s } else RETURN s }"      
  unfolding monadic_WHILEIT_def
  apply (subst RECT_unfold)
  apply refine_mono
  by simp



(* TODO: Move *)
lemma WHILEIT_refine_new_invar':
  assumes R0: "I' x' \<Longrightarrow> (x,x')\<in>R"
  assumes INV0: "\<lbrakk> I' x'; (x,x')\<in>R \<rbrakk> \<Longrightarrow> I x"
  assumes COND_REF: "\<And>x x'. \<lbrakk> (x,x')\<in>R; I x; I' x' \<rbrakk> \<Longrightarrow> b x = b' x'"
  assumes STEP_REF: 
    "\<And>x x'. \<lbrakk> (x,x')\<in>R; b x; b' x'; I x; I' x' \<rbrakk> \<Longrightarrow> f x \<le> \<Down>R (f' x')"
  assumes STEP_INV: 
    "\<And>x x'. \<lbrakk> (x,x')\<in>R; b x; b' x'; I x; I' x' \<rbrakk> \<Longrightarrow> f x \<le>\<^sub>n SPEC I"
  shows "WHILEIT I b f x \<le>\<Down>R (WHILEIT I' b' f' x')"
  apply (rule WHILEIT_refine_genR[where 
    I=I and I'=I' and x'=x' and x=x and R=R and b=b and b'=b' and f'=f' and f=f
    and R'="{ (c,a). (c,a)\<in>R \<and> I c }"
    ])
  using assms STEP_INV[THEN leofD[rotated]]
  by (auto intro: add_invar_refineI)
  


abbreviation (do_notation) bind_doN where "bind_doN \<equiv> Refine_Basic.bind"

notation (output) bind_doN (infixr "\<bind>" 54)
notation (ASCII output) bind_doN (infixr ">>=" 54)

nonterminal doN_binds and doN_bind
syntax
  "_doN_block" :: "doN_binds \<Rightarrow> 'a" ("doN {//(2  _)//}" [12] 62)
  "_doN_bind"  :: "[pttrn, 'a] \<Rightarrow> doN_bind" ("(2_ \<leftarrow>/ _)" 13)
  "_doN_let" :: "[pttrn, 'a] \<Rightarrow> doN_bind" ("(2let _ =/ _)" [1000, 13] 13)
  "_doN_then" :: "'a \<Rightarrow> doN_bind" ("_" [14] 13)
  "_doN_final" :: "'a \<Rightarrow> doN_binds" ("_")
  "_doN_cons" :: "[doN_bind, doN_binds] \<Rightarrow> doN_binds" ("_;//_" [13, 12] 12)
  "_thenM" :: "['a, 'b] \<Rightarrow> 'c" (infixr "\<then>" 54)

syntax (ASCII)
  "_doN_bind" :: "[pttrn, 'a] \<Rightarrow> doN_bind" ("(2_ <-/ _)" 13)
  "_thenM" :: "['a, 'b] \<Rightarrow> 'c" (infixr ">>" 54)

translations
  "_doN_block (_doN_cons (_doN_then t) (_doN_final e))"
    \<rightleftharpoons> "CONST bind_doN t (\<lambda>_. e)"
  "_doN_block (_doN_cons (_doN_bind p t) (_doN_final e))"
    \<rightleftharpoons> "CONST bind_doN t (\<lambda>p. e)"
  "_doN_block (_doN_cons (_doN_let p t) bs)"
    \<rightleftharpoons> "let p = t in _doN_block bs"
  "_doN_block (_doN_cons b (_doN_cons c cs))"
    \<rightleftharpoons> "_doN_block (_doN_cons b (_doN_final (_doN_block (_doN_cons c cs))))"
  "_doN_cons (_doN_let p t) (_doN_final s)"
    \<rightleftharpoons> "_doN_final (let p = t in s)"
  "_doN_block (_doN_final e)" \<rightharpoonup> "e"
  "(m \<then> n)" \<rightharpoonup> "(m \<bind> (\<lambda>_. n))"



lemma Nil_eq_upt_conv: "[] = [l..<h] \<longleftrightarrow> l\<ge>h"
  by (metis upt_eq_Nil_conv zero_le)

lemma eq_upt_Cons_conv: "ll#xs = [l..<h] \<longleftrightarrow> (l<h \<and> ll=l \<and> xs = [l+1..<h])"
  by (metis upt_eq_Cons_conv)
  
(* TODO: Move! Ultimately, we want sepref-rules and a foreach-statement *)  
lemma nfoldli_upt_by_while:
  "nfoldli [l..<h] c f \<sigma> =
  doN { (_,\<sigma>)\<leftarrow>WHILET (\<lambda>(i,\<sigma>). i<h \<and> c \<sigma>) (\<lambda>(i,\<sigma>). doN { \<sigma> \<leftarrow> f i \<sigma>; ASSERT (i<h); RETURN (i+1,\<sigma>) }) (l,\<sigma>); RETURN \<sigma> }
  "
proof (induction "[l..<h]" arbitrary: l \<sigma>)
  case Nil thus ?case
    apply (simp add: Nil_eq_upt_conv)
    apply (subst WHILET_unfold)
    by simp
next
  case (Cons ll xs)
  
  from Cons.hyps(2)[symmetric] have [simp]: "l<h" and [simp]: "ll=l" "[l..<h] = l#[l+1..<h]" "xs=[l+1..<h]"
    by (auto simp: upt_eq_Cons_conv)
  
  note IH = Cons.hyps(1)[of "Suc l",simplified,abs_def]  
    
  from Cons.hyps(2) show ?case
    apply (subst WHILET_unfold)
    apply (auto simp add: IH)
    done
    
qed    

 
  
end
