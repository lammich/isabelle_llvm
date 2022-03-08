section \<open>Automatic Refinement to Parallel Execution\<close>
theory Sepref_Parallel
imports Sepref_Tool
begin

  text \<open>Abstractly, we define an annotation, that maps to sequnetial execution\<close>
  definition "nres_par f g x y \<equiv> do { r1\<leftarrow>f x; r2\<leftarrow>g y; RETURN (r1,r2) }"

  subsection \<open>Setup Boilerplate\<close>
  text \<open>Boilerplate required by the IRF to set up higher-order combinator\<close>
  lemma nres_par_arity[sepref_monadify_arity]:
    "nres_par \<equiv> \<lambda>\<^sub>2f g x y. SP nres_par $ (\<lambda>\<^sub>2x. f$x) $ (\<lambda>\<^sub>2y. g$y) $ x $ y" 
    by (simp_all)
  
  lemma nres_par_comb[sepref_monadify_comb]:
    "nres_par$f$g$x$y \<equiv> 
      Refine_Basic.bind$(EVAL$x)$(\<lambda>\<^sub>2x. Refine_Basic.bind$(EVAL$y)$(\<lambda>\<^sub>2y. 
        (SP nres_par$f$g$x$y)))"
    by (simp_all)
  
  lemma nres_par_id[id_rules]: 
    "nres_par ::\<^sub>i TYPE(('a \<Rightarrow> 'b nres) \<Rightarrow> ('c \<Rightarrow> 'd nres) \<Rightarrow> 'a \<Rightarrow> 'c \<Rightarrow> ('b \<times> 'd) nres)"
    by simp
  
    
  lemma nres_par_pw[refine_pw_simps]:
    "nofail (nres_par f g x y) = (nofail (f x) \<and> ((\<exists>xa. inres (f x) xa) \<longrightarrow> nofail (g y)))"
    "inres (nres_par f g x y) r \<longleftrightarrow> (nofail (f x) \<longrightarrow>
     (\<exists>ya. inres (f x) ya \<and> (nofail (g y) \<longrightarrow> (\<exists>yb. inres (g y) yb \<and> (ya, yb) = r))))"
    unfolding nres_par_def
    by (simp_all add: refine_pw_simps)
    
  lemma nres_par_vcg[refine_vcg]:
    assumes "f x \<le> SPEC (\<lambda>r\<^sub>1. g y \<le> SPEC (\<lambda>r\<^sub>2. \<Phi> (r\<^sub>1,r\<^sub>2)))"
    shows "nres_par f g x y \<le> SPEC \<Phi>"
    using assms by (auto simp: refine_pw_simps pw_le_iff nres_par_def)
    
  lemma nres_par_refine[refine]:
    assumes "f x \<le> \<Down>Rx (f' x')"
    assumes "g y \<le> \<Down>Ry (g' y')"
    assumes "\<And>rx rx' ry ry'. (rx,rx')\<in>Rx \<Longrightarrow> (ry,ry')\<in>Ry \<Longrightarrow> ((rx,ry), (rx',ry'))\<in>R"
    shows "nres_par f g x y \<le>\<Down>R (nres_par f' g' x' y')"
    using assms 
    by (simp add: refine_pw_simps pw_le_iff nres_par_def; blast)


  lemma nres_par_mono[refine_mono]:
    assumes "\<And>x. f x \<le> f' x" 
    assumes "\<And>y. g y \<le> g' y"  
    shows "nres_par f g x y \<le> nres_par f' g' x y"
    using assms 
    by (simp add: refine_pw_simps pw_le_iff nres_par_def; blast)
    
  lemma nres_par_flat_mono[refine_mono]:
    assumes "\<And>x. flat_ge (f x) (f' x)" 
    assumes "\<And>y. flat_ge (g y) (g' y)"  
    shows "flat_ge (nres_par f g x y) (nres_par f' g' x y)"
    using assms 
    by (simp add: refine_pw_simps pw_flat_ge_iff nres_par_def; blast)


    
  subsection \<open>Refinement Rule\<close>        
  
  text \<open>Refinement rule from annotation to actual parallel execution\<close>
  
  (* TODO: Move *)
  lemma ht_llc_par:
    assumes "llvm_htriple P\<^sub>1 (m\<^sub>1 x\<^sub>1) Q\<^sub>1"  
    assumes "llvm_htriple P\<^sub>2 (m\<^sub>2 x\<^sub>2) Q\<^sub>2"  
    shows "llvm_htriple (P\<^sub>1**P\<^sub>2) (llc_par m\<^sub>1 m\<^sub>2 x\<^sub>1 x\<^sub>2) (\<lambda>(r\<^sub>1,r\<^sub>2). Q\<^sub>1 r\<^sub>1 ** Q\<^sub>2 r\<^sub>2)"
    unfolding llc_par_def
    supply [vcg_rules] = ht_par[OF assms]
    by (vcg)
    
    
  lemma hnr_nres_par_aux:
    assumes A: "hn_refine (Ax) (fi xi) (Ax') Rx CP\<^sub>1 (f x)"
    assumes B: "hn_refine (Ay) (gi yi) (Ay') Ry CP\<^sub>2 (g y)"
    shows "hn_refine (Ax ** Ay) (llc_par fi gi xi yi) (Ax' ** Ay') (Rx\<times>\<^sub>aRy) (\<lambda>(rxi,ryi). CP\<^sub>1 rxi \<and> CP\<^sub>2 ryi) (nres_par f g x y)"
  proof -
    note [vcg_rules] = ht_llc_par[where m\<^sub>1=fi and m\<^sub>2=gi, OF A[THEN hn_refineD] B[THEN hn_refineD]]

    from A[THEN hn_refineD] have 
      NSUCCA: "\<exists>r. inres (f x) r" if "realizable Ax"
      using that
      apply (cases "f x \<noteq> SUCCEED")
      subgoal by (auto simp: refine_pw_simps pw_eq_iff)
      apply (clarsimp simp: htriple_false)
      done
    
    show ?thesis
      apply sepref_to_hoare
      apply (rule htriple_realizable_preI; drule realizable_conjD; clarify)
      supply [simp] = refine_pw_simps NSUCCA inres_def[symmetric]
      apply (vcg)
      done
  qed
      
  lemma hnr_nres_par[sepref_comb_rules]:
    assumes FR: "P \<turnstile> hn_ctxt Ax x xi ** hn_ctxt Ay y yi ** F"
    assumes A: "hn_refine (hn_ctxt Ax x xi) (fi xi) Ax' Rx CP\<^sub>1 (f x)"
    assumes B: "hn_refine (hn_ctxt Ay y yi) (gi yi) Ay' Ry CP\<^sub>2 (g y)"
    shows "hn_refine 
      P 
      (llc_par fi gi xi yi) 
      (Ax' ** Ay' ** F) (Rx\<times>\<^sub>aRy) (\<lambda>(rxi,ryi). CP\<^sub>1 rxi \<and> CP\<^sub>2 ryi)
      (nres_par$(\<lambda>\<^sub>2x. f x)$(\<lambda>\<^sub>2y. g y)$x$y)"
    apply (rule hn_refine_cons_post)
    unfolding autoref_tag_defs PROTECT2_def
    apply (rule hn_refine_frame[OF hnr_nres_par_aux, where F=F])
    apply fact
    apply fact
    subgoal using FR unfolding hn_ctxt_def by (auto simp: algebra_simps)
    subgoal unfolding hn_ctxt_def by (auto simp: algebra_simps)
    done
  

end
