section \<open>The Monadic Refinement Framework --- Naked\<close>
(* TODO: Move to Refine_Monadic entry! *)
theory Refine_Monadic_Thin
imports 
  "Refine_Monadic.Refine_Chapter"
  "Refine_Monadic.Refine_Basic"
  "Refine_Monadic.Refine_Leof"
  "Refine_Monadic.Refine_Heuristics"
  "Refine_Monadic.Refine_More_Comb"
  "Refine_Monadic.Refine_While"
  "Refine_Monadic.Refine_Foreach" 
  "Refine_Monadic.Refine_Transfer"
  "Refine_Monadic.Refine_Pfun"
begin
  text {*
    Monadic Refinement Framework, without Autoref.
    *}

  subsection \<open>Convenience Constructs\<close>

  definition "REC_annot pre post body x \<equiv> 
    REC (\<lambda>D x. do {ASSERT (pre x); r\<leftarrow>body D x; ASSERT (post x r); RETURN r}) x"
  
  theorem REC_annot_rule[refine_vcg]:
    assumes M: "trimono body"
    and P: "pre x"
    and S: "\<And>f x. \<lbrakk>\<And>x. pre x \<Longrightarrow> f x \<le> SPEC (post x); pre x\<rbrakk> 
            \<Longrightarrow> body f x \<le> SPEC (post x)"
    and C: "\<And>r. post x r \<Longrightarrow> \<Phi> r"
    shows "REC_annot pre post body x \<le> SPEC \<Phi>"
  proof -
    from `trimono body` have [refine_mono]:
      "\<And>f g x xa. (\<And>x. flat_ge (f x) (g x)) \<Longrightarrow> flat_ge (body f x) (body g x)"
      "\<And>f g x xa. (\<And>x. f x \<le> g x) \<Longrightarrow> body f x \<le> body g x"
      apply -
      unfolding trimono_def monotone_def fun_ord_def mono_def le_fun_def
      apply (auto)
      done
  
    show ?thesis
      unfolding REC_annot_def
      apply (rule order_trans[where y="SPEC (post x)"])
      apply (refine_rcg 
        refine_vcg 
        REC_rule[where pre=pre and M="\<lambda>x. SPEC (post x)"]
        order_trans[OF S]
      )
      apply fact
      apply simp
      using C apply (auto) []
      done
  qed
  
  subsection \<open>Syntax Sugar\<close>
  locale Refine_Monadic_Syntax begin
  
    notation SPEC (binder "spec " 10)
    notation ASSERT ("assert")
    notation RETURN ("return")
    notation FOREACH ("foreach")
    notation WHILE ("while")
    notation WHILET ("while\<^sub>T")
    notation WHILEI ("while\<^bsup>_\<^esup>")
    notation WHILET ("while\<^sub>T")
    notation WHILEIT ("while\<^sub>T\<^bsup>_\<^esup>")

    notation RECT (binder "rec\<^sub>T " 10)
    notation REC (binder "rec " 10)

    notation SELECT (binder "select " 10)
      
  end
    
end
