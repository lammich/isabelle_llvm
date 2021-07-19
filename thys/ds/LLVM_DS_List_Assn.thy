section \<open>Nested List Assertion\<close>
theory LLVM_DS_List_Assn
imports "../vcg/LLVM_VCG_Main"
begin
  (* TODO: Improve handling of pure assertions. 
    Dirty hacks like for pure list-assn shouldn't be necessary!
  *)

  (* TODO: Move *)  
  lemma gen_drule:
    assumes "P\<turnstile>Q"
    assumes "FRAME A P F"
    assumes "Q**F\<turnstile>B"
    shows "A\<turnstile>B"
    using assms unfolding FRAME_def
    using sep_rule(1) sep_rule(2) by blast
  


  (* TODO: Move *)
  lemma pure_part_set_imgD[vcg_prep_ext_rules]:
    shows "pure_part (sep_set_img S P) \<longrightarrow> (\<forall>x\<in>S. pure_part (P x))"
  proof (cases "finite S")
    case True thus ?thesis
      by (induction S) (auto dest: pure_part_split_conj)
  next
    case False then show ?thesis by simp
  qed    


  
  
  
  
  subsection \<open>Tags\<close>  
  text \<open>Ghost instructions to guide the VCG and Frame Inference\<close>
  lemma entails_is_noop_htriple: "(A \<turnstile> B) \<Longrightarrow> llvm_htriple A (return x) (\<lambda>_. B)"
    apply (auto simp: htriple_def wp_return)
    by (metis entails_def sep_conj_impl1)

  lemma tag_op_ruleI: 
    assumes "tag_op = return x"  
    assumes "A\<turnstile>B"
    shows "llvm_htriple A tag_op (\<lambda>_. B)"
    using entails_is_noop_htriple assms by metis

  text \<open>Assertion to be matched with anything. 
    To obtain abstract from concrete variable.\<close>  
  definition "tag_assn \<equiv> mk_pure_assn (\<lambda>_ _. True)"
  lemma tag_assn_pure[is_pure_rule]: "is_pure (tag_assn)" unfolding tag_assn_def by auto
  
  lemma tag_assnI[fri_rules]: "PRECOND (SOLVE_ASM (\<flat>\<^sub>pA a c)) \<Longrightarrow> \<box> \<turnstile> \<upharpoonleft>\<^sub>ptag_assn a c"
    by (auto simp: tag_assn_def sep_algebra_simps)
    
  (* TODO: Move *)  
  lemma split_pure_assn: "is_pure A \<Longrightarrow> \<upharpoonleft>A a c \<turnstile> \<upharpoonleft>A a c ** \<upharpoonleft>A a c"
    by (smt entails_eq_iff entails_pureI extract_pure_assn pure_part_pureD pure_true_conv sep.add.right_neutral)  
    
  definition tag_split_pure :: "'b::llvm_rep \<Rightarrow> unit llM" 
    where "tag_split_pure x = return ()"  

  lemma tag_split_pure_rl[vcg_rules]:
    shows "llvm_htriple 
      (\<up>(is_pure A) ** \<upharpoonleft>A a c)
      (tag_split_pure c)
      (\<lambda>_. \<upharpoonleft>A a c ** \<upharpoonleft>A a c)"
    supply [vcg_rules] = tag_op_ruleI[OF tag_split_pure_def[where x=c] split_pure_assn[of A a c]]
    by vcg  
    
    
  lemma bury_pure_assn: "is_pure A \<Longrightarrow> \<upharpoonleft>A a c \<turnstile> \<box>"
    by (smt entails_eq_iff entails_pureI extract_pure_assn pure_part_pureD pure_true_conv)

  lemma bury_pure_assn': "\<upharpoonleft>\<^sub>pA a c \<turnstile> \<box>"
    by (simp add: dr_assn_pure_prefix_def entails_lift_extract_simps(1))
    
        
  definition tag_bury_pure :: "'b::llvm_rep \<Rightarrow> unit llM" 
    where "tag_bury_pure x = return ()"  

  lemma tag_bury_pure_rl[vcg_rules]:
    shows "llvm_htriple 
      (\<up>(is_pure A) ** \<upharpoonleft>A a c)
      (tag_bury_pure c)
      (\<lambda>_. \<box>)"
    supply [vcg_rules] = tag_op_ruleI[OF tag_bury_pure_def[where x=c] bury_pure_assn[of A a c]]
    by vcg  
    
    
      
  
  
  subsection \<open>Map of Valid Indexes in List\<close>
  (* TODO: DUP in Array_of_Array_List. *)
  definition "idxe_map l i \<equiv> if i<length l then Some (l!i) else None"

  lemma idxe_map_empty[simp]: "idxe_map [] = Map.empty" unfolding idxe_map_def by auto
  
  lemma idxe_map_dom[simp]: "dom (idxe_map l) = {0..<length l}" unfolding idxe_map_def by (auto split: if_splits)
  
  lemma le_idxe_map_updI: "i<length l \<Longrightarrow> m \<subseteq>\<^sub>m idxe_map l \<Longrightarrow> m(i\<mapsto>l!i) \<subseteq>\<^sub>m idxe_map l"
    unfolding idxe_map_def map_le_def by (auto split: if_splits)
    
  lemma le_idxe_map_delD: "m \<subseteq>\<^sub>m idxe_map l \<Longrightarrow> m(i:=None) \<subseteq>\<^sub>m idxe_map (l[i:=x])"
    unfolding idxe_map_def map_le_def by (auto split: if_splits)
    
  lemma le_idxe_map_delD': "m \<subseteq>\<^sub>m idxe_map l \<Longrightarrow> m(i:=None) \<subseteq>\<^sub>m idxe_map l"
    unfolding idxe_map_def map_le_def by (auto split: if_splits)
    
  lemma le_idxe_mapD: "m \<subseteq>\<^sub>m idxe_map l \<Longrightarrow> m i = Some xi \<Longrightarrow> l!i = xi"  
    unfolding idxe_map_def map_le_def 
    apply (clarsimp split: if_splits) 
    by (metis domI domIff option.inject)

  lemma le_idxe_map_lenD: "m \<subseteq>\<^sub>m idxe_map l \<Longrightarrow> m i = Some xi \<Longrightarrow> i < length l"  
    unfolding idxe_map_def map_le_def 
    apply (clarsimp split: if_splits) 
    by (metis domI domIff)

  lemma le_idxe_map_append1I: "A\<subseteq>\<^sub>midxe_map (xs@[y]) \<Longrightarrow> A(length xs := None)\<subseteq>\<^sub>midxe_map (xs)"  
    by (auto simp: map_le_def idxe_map_def split: if_splits)

  lemma le_idxe_map_append2I: "A\<subseteq>\<^sub>midxe_map xs \<Longrightarrow> A\<subseteq>\<^sub>midxe_map (xs@ys)"  
    by (auto simp: map_le_def idxe_map_def split: if_splits)
    
  subsection \<open>Nested List Assertion\<close>

  definition "list_assn A R \<equiv> mk_assn (\<lambda>xs ys. 
     \<up>(length xs=length ys) 
  ** \<up>(R \<subseteq>\<^sub>m idxe_map ys)
  ** (\<Union>*i\<in>{0..<length ys} - dom R. \<upharpoonleft>A (xs!i) (ys!i)))"

    
  lemma list_assn_pure_partD[vcg_prep_ext_rules]:
    "pure_part (\<upharpoonleft>(list_assn A R) xs ys) 
      \<Longrightarrow> length xs = length ys \<and> R \<subseteq>\<^sub>m idxe_map ys \<and> (\<forall>x\<in>{0..<length ys} - dom R. pure_part (\<upharpoonleft>A (xs ! x) (ys ! x)))"
    unfolding list_assn_def
    apply vcg_prepare_external by blast
    

  subsection \<open>Transformations\<close>  
  
  subsubsection \<open>Initialization and Destruction\<close>
    text \<open>Initialization if there is a pure initial element\<close>    
  lemma list_assn_init_pure: 
    assumes "\<box> \<turnstile> \<upharpoonleft>A x xi"
    shows "\<box> \<turnstile> \<upharpoonleft>(list_assn A Map.empty) (replicate n x) (replicate n xi)"
  proof -
    have "\<box> \<turnstile> (\<Union>*xa\<in>{0..<n}. \<upharpoonleft>A x xi)" 
      apply (induction n)
      subgoal by simp
      subgoal for n
        apply (simp add: atLeast0_lessThan_Suc)
        using conj_entails_mono[OF assms] by simp
      done    
    
    thus ?thesis
      unfolding list_assn_def 
      by (simp add: sep_algebra_simps)
  qed
    
  text \<open>Arbitrary initialization, no elements owned. Can be used to justify init-algorithm\<close>
  lemma list_assn_init_none:
    assumes "length xs = length ys"
    shows "\<box> \<turnstile> \<upharpoonleft>(list_assn A (idxe_map ys)) xs ys"
    using assms unfolding list_assn_def 
    by (simp add: sep_algebra_simps)
  
  lemma list_assn_empty: "\<box> \<turnstile> \<upharpoonleft>(list_assn A Map.empty) [] []"  
    unfolding list_assn_def
    by (auto simp: sep_algebra_simps)
    
  text \<open>Destruction if all elements have been extracted\<close>
  lemma list_assn_free_none:
    assumes "dom R \<supseteq> {0..<length ys}"
    shows "\<upharpoonleft>(list_assn A R) xs ys \<turnstile> \<box>"
    using assms unfolding list_assn_def 
    by (auto simp: sep_algebra_simps entails_lift_extract_simps dest: map_le_implies_dom_le)

  subsubsection \<open>Extracting and Joining Elements\<close>  
  
  lemma list_assn_extract_aux: 
    assumes "i<length xs" "i\<notin>R"  
    shows "sep_set_img ({0..<length xs} - R) P 
        = (P i ** sep_set_img ({0..<length xs} - insert i R) P)"
  proof -
    from assms have 1: "{0..<length xs} - R = insert i ({0..<length xs} - insert i R)" by auto
    show ?thesis
      by (subst 1) auto
  qed    
  
  
  lemma list_assn_extract:
    assumes "i<length xs" "R i = None"
    shows "\<upharpoonleft>(list_assn A R) xs ys \<turnstile> \<upharpoonleft>(list_assn A (R(i\<mapsto>ys!i))) xs ys ** \<upharpoonleft>A (xs!i) (ys!i)"
    using assms unfolding list_assn_def
    supply [simp] = le_idxe_map_updI list_assn_extract_aux ndomIff
    supply fri_red_img[fri_red_rules]
    apply (clarsimp simp: sep_algebra_simps entails_lift_extract_simps)
    apply (rule ENTAILSD)
    apply vcg
    done
    
  lemma list_assn_upd_aux: 
    fixes I xs xsi
    defines "I \<equiv> {0..<length xsi}"
    assumes "i\<in>I" "i\<in>R" and [simp]: "length xsi = length xs"
    shows "(\<Union>*j\<in>I - (R - {i}). \<upharpoonleft>A (xs[i := x] ! j) (xsi[i := xi] ! j)) = (\<upharpoonleft>A x xi ** (\<Union>*j\<in>I - R. \<upharpoonleft>A (xs ! j) (xsi ! j)))"
  proof -
    from assms have 1: "I - (R - {i}) = insert i (I-R)" by auto
    from assms have [simplified,simp]: "i\<notin>I-R" by auto
    have [simp]: "i<length xs" using \<open>i\<in>I\<close> unfolding I_def by auto
    have [simp]: "j\<in>I-R \<Longrightarrow> i\<noteq>j" for j using \<open>i\<in>R\<close> by auto
    show ?thesis apply (subst 1) by simp
  qed  
    
  lemma list_assn_update:
    assumes "R i \<noteq> None"
    shows "\<upharpoonleft>(list_assn A R) xs ys ** \<upharpoonleft>A x y \<turnstile> \<upharpoonleft>(list_assn A (R(i:=None))) (xs[i:=x]) (ys[i:=y])"
    using assms unfolding list_assn_def
    apply -
    apply (rule entails_pureI)
    
    supply [simp] = le_idxe_map_updI le_idxe_map_delD
    supply fri_red_img[fri_red_rules]
    apply (clarsimp simp: sep_algebra_simps entails_lift_extract_simps)
    apply (subst list_assn_upd_aux)
    subgoal by (metis domI idxe_map_dom map_leD)
    apply auto [2]
    apply (rule ENTAILSD)
    apply vcg
    done
    
  lemma list_assn_join:
    assumes "R i = Some y"
    assumes "x = xs!i"
    shows "\<upharpoonleft>(list_assn A R) xs ys ** \<upharpoonleft>A x y \<turnstile> \<upharpoonleft>(list_assn A (R(i:=None))) xs ys"
    apply (rule entails_pureI)
    apply (subst (asm) list_assn_def)
    apply (clarsimp simp: sep_algebra_simps dest!: pure_part_split_conj)
    apply (rule entails_trans[OF list_assn_update[where i=i]])
    using assms by (auto dest: le_idxe_mapD)
    
  lemma list_assn_join':
    assumes "R i = None"
    assumes "x = xs!i" "y=ys!i"
    shows "\<upharpoonleft>(list_assn A (R(i\<mapsto>ys!i))) xs ys ** \<upharpoonleft>A x y \<turnstile> \<upharpoonleft>(list_assn A R) xs ys"
    apply (sep_drule_simple list_assn_join[where i=i])
    using assms by (auto simp: fun_upd_idem)

  subsubsection \<open>Push and Pop\<close>    
  lemma list_assn_push_back:
    shows "(\<upharpoonleft>(list_assn A R) xs ys ** \<upharpoonleft>A x y) \<turnstile> (\<upharpoonleft>(list_assn A R) (xs@[x]) (ys@[y]))"
    unfolding list_assn_def
    apply (clarsimp simp: sep_algebra_simps atLeast0_lessThan_Suc entails_lift_extract_simps 
      insert_Diff_if le_idxe_map_append2I; safe)
    apply (auto dest: le_idxe_map_lenD; fail)
    apply (rule ENTAILSD)
    supply [simp] = nth_append
    by vcg

    
    
  lemma list_assn_pop_back1:
    assumes "R (length xs - 1) \<noteq> None"
    shows "\<upharpoonleft>(list_assn A R) xs ys \<turnstile> \<upharpoonleft>(list_assn A (R(length xs-1 := None))) (butlast xs) (butlast ys)"  
    using assms unfolding list_assn_def
    apply (rule_tac entails_pureI)
    apply (cases xs rule: rev_cases; cases ys rule: rev_cases)
    apply (clarsimp_all 
      dest!: pure_part_split_conj 
      simp: sep_algebra_simps atLeast0_lessThan_Suc domI set_minus_minus_disj_conv)
    apply (rule ENTAILSD)
    supply [simp] = le_idxe_map_append1I
    by vcg
    
    
  lemma list_assn_pop_back2:
    assumes "xs\<noteq>[]" "R (length xs - 1) = None"
    shows "(\<upharpoonleft>(list_assn A R) xs ys) \<turnstile> (\<upharpoonleft>(list_assn A R) (butlast xs) (butlast ys) ** \<upharpoonleft>A (last xs) (last ys))"  
    apply (rule entails_pureI) using assms
    apply vcg_prepare_external
    apply (sep_drule_simple list_assn_extract[where i="length xs - 1"])
    subgoal by (cases ys; simp)
    subgoal by simp
    apply (sep_drule_simple list_assn_pop_back1)
    subgoal by auto
    by (cases ys rule: rev_cases; simp add: last_conv_nth fun_upd_idem)
    
    
  subsection \<open>Fri-Reduce Rules for List-Assertion\<close>  
  lemma la_red_extract:
    "PRECOND (SOLVE_AUTO (R i = None \<and> i<length xs)) 
      \<Longrightarrow> is_sep_red (\<upharpoonleft>(list_assn A (R(i\<mapsto>ys!i))) xs ys) \<box> (\<upharpoonleft>(list_assn A R) xs ys) (\<upharpoonleft>A (xs!i) (ys!i))"
    apply (clarsimp simp: vcg_tag_defs)
    apply (rule is_sep_redI)
    apply (sep_drule_simple list_assn_extract, assumption+)
    apply (erule gen_drule, fri)
    apply (rule ENTAILSD, fri)
    done
  
  lemma la_red_join:
    "PRECOND (SOLVE_AUTO (R i = None \<and> i<length xs \<and> x=xs!i \<and> y=ys!i)) 
      \<Longrightarrow> is_sep_red \<box> (\<upharpoonleft>(list_assn A (R(i\<mapsto>ys!i))) xs ys) (\<upharpoonleft>A x y) (\<upharpoonleft>(list_assn A R) xs ys)"
    apply (clarsimp simp: vcg_tag_defs)
    apply (rule is_sep_redI)
    apply (sep_rule list_assn_join')
    apply assumption+
    apply (erule gen_drule, fri)
    apply (rule ENTAILSD, fri)
    done
    

  subsection \<open>Tags for List-Assertion\<close>
  
  definition tag_la_upd :: "'b::llvm_rep \<Rightarrow> 'a word \<Rightarrow> 'd::llvm_rep \<Rightarrow> unit llM" 
    where "tag_la_upd p i y = return ()"  

  lemma tag_la_upd_rl[vcg_rules]:
    shows "llvm_htriple 
      (\<upharpoonleft>tag_assn i ii ** \<upharpoonleft>AA ys p ** \<upharpoonleft>(list_assn A R) xs ys ** \<upharpoonleft>A x y ** \<up>(R i \<noteq> None))
      (tag_la_upd p ii y)
      (\<lambda>_. \<upharpoonleft>(list_assn A (R(i:=None))) (xs[i:=x]) (ys[i:=y]) ** \<upharpoonleft>AA ys p)"
    supply [vcg_rules] = tag_op_ruleI[OF tag_la_upd_def[where i=ii] list_assn_update[where i=i]]
    by vcg  
    

  definition tag_la_join :: "'b::llvm_rep \<Rightarrow> 'a word \<Rightarrow> 'd::llvm_rep \<Rightarrow> unit llM" 
    where "tag_la_join p i y = return ()"
    
  lemma tag_la_join_rl[vcg_rules]:
    shows "llvm_htriple 
      (\<upharpoonleft>tag_assn i ii ** \<upharpoonleft>AA ys p ** \<upharpoonleft>(list_assn A R) xs ys ** \<upharpoonleft>A x y ** \<up>(R i = Some y \<and> x=xs!i))
      (tag_la_join p ii y)
      (\<lambda>_. \<upharpoonleft>(list_assn A (R(i:=None))) xs ys ** \<upharpoonleft>AA ys p)"
    supply [vcg_rules] = tag_op_ruleI[OF tag_la_join_def[where i=ii] list_assn_join[where i=i]]
    by vcg  
    
  definition "tag_la_extract p i = return ()"  

      
  (*
    TODO: We have to use tag-assn for pure (i), and variables (AA) for impure assertions: 
      Otherwise, current frame-inference's pure extraction will not unify 
      variable assertion with pure assertion! FIX THAT! 
  *)  
    
  lemma tag_la_extract_rl[vcg_rules]: 
    "llvm_htriple
      (\<upharpoonleft>tag_assn i ii ** \<upharpoonleft>AA ys p ** \<upharpoonleft>(list_assn A R) xs ys ** \<up>(R i = None \<and> i<length xs))
      (tag_la_extract p ii)
      (\<lambda>_. \<upharpoonleft>(list_assn A (R(i\<mapsto>ys!i))) xs ys ** \<upharpoonleft>A (xs!i) (ys!i) ** \<upharpoonleft>AA ys p ** \<up>(length xs = length ys))" 
    supply [vcg_rules] = tag_op_ruleI[OF tag_la_extract_def[where i=ii] list_assn_extract[where i=i]]
    apply vcg
    done

        
  definition "tag_la_push_back p x = return ()"    
  
  lemma tag_la_push_back_rl[vcg_rules]:
    "llvm_htriple 
      (\<upharpoonleft>AA ys p ** \<upharpoonleft>(list_assn A R) xs ys ** \<upharpoonleft>A x y)
      (tag_la_push_back p y)
      (\<lambda>_. \<upharpoonleft>(list_assn A R) (xs@[x]) (ys@[y]) ** \<upharpoonleft>AA ys p)"
    supply [vcg_rules] = tag_op_ruleI[OF tag_la_push_back_def[where p=p] list_assn_push_back]
    by vcg

  definition "tag_la_pop_back p = return ()"
  lemma tag_la_pop_back_rl[vcg_rules]:
    "llvm_htriple
      (\<upharpoonleft>AA ys p ** \<upharpoonleft>(list_assn A R) xs ys ** \<up>(xs\<noteq>[] \<and> R (length xs-1) = None))
      (tag_la_pop_back p)
      (\<lambda>_. \<upharpoonleft>AA ys p ** \<upharpoonleft>(list_assn A R) (butlast xs) (butlast ys) ** \<upharpoonleft>A (last xs) (last ys) ** \<up>(xs\<noteq>[] \<and> ys\<noteq>[]))"  
    supply [vcg_rules] = tag_op_ruleI[OF tag_la_pop_back_def[where p=p] list_assn_pop_back2]
    apply (rule htriple_pure_preI)
    by vcg
  
  subsection \<open>Pure List Assertion\<close>  
  (* TODO: is_pure list_assn rule *)
  
  definition "tag_la_exfree_pure p i = return ()"  

  lemma bury_pure_red: "PRECOND (SOLVE_ASM (is_pure A)) \<Longrightarrow> is_sep_red \<box> \<box> (\<upharpoonleft>A a c) \<box>"
    unfolding vcg_tag_defs
    apply (rule is_sep_redI)
    apply (sep_drule bury_pure_assn)
    by simp
  
  lemma tag_la_exfree_pure_rl[vcg_rules]: 
    "llvm_htriple
      (\<upharpoonleft>tag_assn i ii ** \<upharpoonleft>AA ys p ** \<upharpoonleft>(list_assn A R) xs ys ** \<up>(is_pure A \<and> R i = None \<and> i<length xs))
      (tag_la_exfree_pure p ii)
      (\<lambda>_. \<upharpoonleft>(list_assn A (R(i\<mapsto>ys!i))) xs ys ** \<upharpoonleft>AA ys p ** \<up>(length xs = length ys))" 
    supply R[vcg_rules] = 
      tag_op_ruleI[OF tag_la_exfree_pure_def[where i=ii] list_assn_extract[where i=i], of xs R A ys]
    thm R
    apply vcg
    apply vcg_try_solve
    subgoal (* TODO: Dirty hack! *)
      unfolding FRAME_INFER_def FRI_END_def
      apply (sep_drule_simple bury_pure_assn')
      by simp
    done

end
