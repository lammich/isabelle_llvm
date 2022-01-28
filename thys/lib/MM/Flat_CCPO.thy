section \<open>Flat Chain Complete Partial Orders\<close>
theory Flat_CCPO
imports Main
begin

  text \<open>We establish some theory for recursion, based on flat orderings. \<close>

  subsection \<open>Auxiliary lemmas\<close>
  
  text \<open>Technical shortcut: Derive less-than from less-or-equal:\<close>  
  definition "mk_lt l a b \<equiv> l a b \<and> a\<noteq>b"
  
  lemma preorder_mk_ltI:
    assumes 
      "\<And>x. le x x"
      "\<And>x y z. \<lbrakk>le x y; le y z\<rbrakk> \<Longrightarrow> le x z"
      "\<And>x y. \<lbrakk>le x y; le y x\<rbrakk> \<Longrightarrow> x = y"
    shows "class.preorder le (mk_lt le)"
    apply unfold_locales
    by (auto intro: assms simp: mk_lt_def)
  
  
  
  text \<open>Fixed points are monotone\<close>
  lemma (in ccpo) fixp_mono:  
    assumes MF: "monotone (\<le>) (\<le>) f"
    assumes MF': "monotone (\<le>) (\<le>) f'"
    assumes LF: "\<And>x. f x \<le> f' x"
    shows "ccpo.fixp Sup (\<le>) f \<le> ccpo.fixp Sup (\<le>) f'"
    by (metis LF MF MF' local.fixp_lowerbound local.fixp_unfold)
  
  text \<open>CCPOs extend to pointwise ordering on functions\<close>     
  lemma (in ccpo) ccpo_ext_fun: 
    "class.ccpo (fun_lub Sup) (fun_ord (\<le>)) (mk_lt (fun_ord (\<le>)))"  
    apply unfold_locales
    apply (auto simp: mk_lt_def fun_ord_def fun_eq_iff)
    subgoal using order.antisym by blast
    subgoal by metis
    subgoal using order.trans by blast
    subgoal by (simp add: order.antisym)
    subgoal by (metis (mono_tags, lifting) chain_fun fun_lub_def local.ccpo_Sup_upper mem_Collect_eq)
    subgoal by (smt (verit, best) chain_fun fun_lub_def local.ccpo_Sup_least mem_Collect_eq)
    done

  subsection \<open>Flat Ordering\<close>
    
  text \<open>We establish a theory of flat orderings, parameterized with the bottom element\<close>
  locale flat_rec =
    fixes bot :: "'a" 
  begin
    subsubsection \<open>Definitions\<close>
    definition "le a b \<equiv> a=bot \<or> a=b"
    definition "lt \<equiv> mk_lt le"
    text \<open>A chain is a set of mutually comparable elements\<close>  
    abbreviation "chain \<equiv> Complete_Partial_Order.chain le"

    text \<open>Least upper bound in flat ordering\<close>
    definition "lub M \<equiv> if M - {bot} = {} then bot else THE m. M-{bot}={m}"

    subsubsection \<open>Auxiliary Lemmas\<close>
    lemma lub_simps[simp]:
      "lub {} = bot"  
      "lub {x} = x"  
      "lub {bot,x} = x"
      unfolding lub_def by auto

    lemma fun_lub_empty: "fun_lub lub {} = (\<lambda>_. bot)"
      by (auto simp: fun_lub_def)
    
    lemma fun_lub_apply: "fun_lub L A x = L {f x | f. f\<in>A}"  
      unfolding fun_lub_def
      by meson
      
    lemma chain_apply:
      assumes "Complete_Partial_Order.chain (fun_ord le) A"
      shows "chain {f x |f. f \<in> A}"
      using assms
      unfolding Complete_Partial_Order.chain_def fun_ord_def
      by blast
      
              
    subsubsection \<open>CCPO property\<close>    
    text \<open>Our structure is a partial order\<close> 
    interpretation ord: order le lt
      apply unfold_locales 
      unfolding le_def lt_def mk_lt_def
      apply auto
      done
    
    text \<open>For a flat ordering, chains are either empty, singleton, 
      or doubleton sets that contain \<^term>\<open>bot\<close>.\<close>
    lemma chain_cases:
      assumes "chain M"
      obtains "M={}" | "M={bot}" | x where "x\<noteq>bot" "M={x}" | x where "x\<noteq>bot" "M={bot,x}"
      using assms
      unfolding chain_def le_def
      by fast

      
    text \<open>Our structure is a chain complete partial order, 
      i.e., every chain has a least upper bound\<close>        
    interpretation ord: ccpo lub le lt
      apply unfold_locales
      apply (auto simp: le_def lub_def elim: chain_cases)
      done
      
    subsubsection \<open>Pointwise extension to functions\<close>
    interpretation f_ord: ccpo "fun_lub lub" "fun_ord le" "mk_lt (fun_ord le)"
      by (rule ord.ccpo_ext_fun)

    subsubsection \<open>Recursion combinator\<close>  
    
    abbreviation mono :: "(('b \<Rightarrow> 'a) \<Rightarrow> 'b \<Rightarrow> 'a) \<Rightarrow> bool" 
      where "mono \<equiv> monotone (fun_ord le) (fun_ord le)"
    definition "REC F \<equiv> if mono F then f_ord.fixp F else (\<lambda>_. bot)"

    text \<open>Unfold rule\<close>    
    lemma REC_unfold: "mono F \<Longrightarrow> REC F = F (REC F)"
      unfolding REC_def
      by (auto intro: f_ord.fixp_unfold)
    
    text \<open>Well-founded induction rule\<close>    
    lemma REC_wf_induct: 
      assumes WF: "wf V"
      assumes MONO: "mono F"
      assumes STEP: "\<And>x D. \<lbrakk>\<And>y. \<lbrakk>(y,x)\<in>V\<rbrakk> \<Longrightarrow> P y (D y) \<rbrakk> \<Longrightarrow> P x (F D x)"
      shows "P x (REC F x)"
      using WF
      apply (induction x)
      apply (subst REC_unfold[OF MONO])
      by (rule STEP)

    text \<open>Pointwise induction rule\<close>    
    lemma REC_pointwise_induct:
      assumes BOT: "\<And>x. P x bot"
      assumes STEP: "\<And>D x. (\<And>y. P y (D y)) \<Longrightarrow> P x (F D x)"
      shows "P x (REC F x)"
      unfolding REC_def
    proof (clarsimp simp: BOT)
      assume "mono F"
      then have "\<forall>x. P x (f_ord.fixp F x)"
        apply (induction F rule: f_ord.fixp_induct; simp add: BOT fun_lub_empty STEP)
        apply (rule ccpo.admissibleI)
        apply clarify
        subgoal for A x
          apply (auto simp: fun_lub_apply dest!: chain_apply[where x=x])
          apply (erule chain_cases; force)
          done
      done
      thus "P x (f_ord.fixp F x)" ..
    qed

    text \<open>Monotonicity Rule\<close> 
    lemma REC_mono:
      assumes M: "\<And>D. mono (F D)"
      assumes "\<And>x. fun_ord le (F D x) (F D' x)"
      shows "fun_ord le (REC (F D)) (REC (F D'))"
      unfolding REC_def 
      apply (simp add: M)
      apply (rule f_ord.fixp_mono)
      apply (simp add: M)
      apply (simp add: M)
      by fact
           
  end

  subsection \<open>General Setup\<close>
  
  lemma (in ccpo) partial_function_definitions: "partial_function_definitions (\<le>) Sup"
    using local.ccpo_Sup_least local.ccpo_Sup_upper local.dual_order.antisym local.order_trans partial_function_definitions_def by blast
    
  
  locale rec_setup =
    fixes lub le lt
    assumes A: "class.ccpo lub le lt"
  begin
  
    interpretation ccpo lub le lt by (rule A)

    abbreviation "bt \<equiv> lub {}"
        
    interpretation f_ord: ccpo "fun_lub lub" "fun_ord le" "mk_lt (fun_ord le)"
      by (rule ccpo_ext_fun)

    lemma fun_lub_empty: "fun_lub lub {} = (\<lambda>_. bt)"
      by (auto simp: fun_lub_def)

    lemma fun_lub_apply: "fun_lub L A x = L {f x | f. f\<in>A}"  
      unfolding fun_lub_def
      by meson
      
    lemma chain_apply:
      assumes "Complete_Partial_Order.chain (fun_ord le) A"
      shows "Complete_Partial_Order.chain le {f x |f. f \<in> A}"
      using assms
      unfolding Complete_Partial_Order.chain_def fun_ord_def
      by blast
            
        
    abbreviation fmono :: "(('b \<Rightarrow> 'a) \<Rightarrow> 'b \<Rightarrow> 'a) \<Rightarrow> bool" 
      where "fmono \<equiv> monotone (fun_ord le) (fun_ord le)"
      
    lemma fmono_alt: "fmono F = (\<forall>x y. fun_ord le x y \<longrightarrow> fun_ord le (F x) (F y))"
      unfolding monotone_def ..
      
      
      
    definition "REC F \<equiv> if fmono F then f_ord.fixp F else (\<lambda>_. bt)"
    
    lemma REC_unfold: "fmono F \<Longrightarrow> REC F = F (REC F)"
      unfolding REC_def
      by (auto intro: f_ord.fixp_unfold)
  
    find_theorems "ccpo.admissible" fun_ord
      
    text \<open>Pointwise induction rule\<close>    
    lemma REC_pointwise_induct:
      assumes BOT: "\<And>x. P x bt"
      assumes ADM: "\<And>x. ccpo.admissible lub le (P x)"
      assumes STEP: "\<And>D x. (\<And>y. P y (D y)) \<Longrightarrow> P x (F D x)"
      shows "P x (REC F x)"
      unfolding REC_def
    proof (clarsimp simp: BOT)
      assume "fmono F"
      then have "\<forall>x. P x (f_ord.fixp F x)"
        apply (induction F rule: f_ord.fixp_induct; simp add: BOT fun_lub_empty STEP)
        apply (rule admissible_fun[OF partial_function_definitions])
        apply (rule ADM)
      done
      thus "P x (f_ord.fixp F x)" ..
    qed
  
    lemma REC_wf_induct: 
      assumes WF: "wf V"
      assumes MONO: "fmono F"
      assumes STEP: "\<And>x D. \<lbrakk>\<And>y. \<lbrakk>(y,x)\<in>V\<rbrakk> \<Longrightarrow> P y (D y) \<rbrakk> \<Longrightarrow> P x (F D x)"
      shows "P x (REC F x)"
      using WF
      apply (induction x)
      apply (subst REC_unfold[OF MONO])
      by (rule STEP)
    
    
    lemma REC_mono:
      assumes M: "\<And>D. fmono (F D)"
      assumes "\<And>x. fun_ord le (F D x) (F D' x)"
      shows "fun_ord le (REC (F D)) (REC (F D'))"
      unfolding REC_def 
      apply (simp add: M)
      apply (rule f_ord.fixp_mono)
      apply (simp add: M)
      apply (simp add: M)
      by fact
  
  
  end
  
end
