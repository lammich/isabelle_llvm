section \<open>Next/Previous Floating Point Number\<close>
theory IEEE_Fp_Nextfloat
imports IEEE_Fp_Add_Basic "HOL-Library.Rewrite"
begin

  subsection \<open>Miscellaneous\<close>
  subsubsection \<open>Basic Properties\<close>
  (*
  (* TODO: Move *)  
  lemma zero_neq_topfloat[simp]:
    "0\<noteq>topfloat"  
    "topfloat\<noteq>0"  
    by (metis bottomfloat_simps(3) diff_diff_cancel diff_zero float_sel_simps(12) leD nat_le_linear nat_power_eq_Suc_0_iff power_0 two_plen_gt1)+
    
  lemma mzero_neq_topfloat[simp]: 
    "-0 \<noteq> topfloat"  
    "topfloat \<noteq> -0"  
    by (metis float_sel_simps(13) float_sel_simps(8) len_not_eq_0 len_num1)+
    
  lemma mtopfloat_neq_Z[simp]: 
    "-topfloat \<noteq> 0"
    "-topfloat \<noteq> -0"
    "0 \<noteq> -topfloat"
    "-0 \<noteq> -topfloat"
    subgoal by (metis minus_minus_float mzero_neq_topfloat(1)) 
    subgoal by (metis minus_minus_float zero_neq_topfloat(1))
    subgoal by (metis minus_minus_float mzero_neq_topfloat(1)) 
    subgoal by (metis minus_minus_float zero_neq_topfloat(1))
    done    
  lemma float_neq_neg[simp]: 
    "is_finite x \<Longrightarrow> x \<noteq> -x"
    "is_finite x \<Longrightarrow> -x \<noteq> x"
    by (metis float_neg_sign)+ 

  lemmas [simp, intro!] = finite_topfloat  
    
    
  lemma zero_finite[simp,intro!]: "is_finite 0"  
    by (meson float_zero1 is_finite_def)

  lemma plus_inf_not_zero[simp]: "\<not>is_zero \<infinity>"
    using infinite_infinity(1) is_finite_def by blast  

  lemma topfloat_not_zero[simp]: "\<not>is_zero topfloat"
    using is_zero_cases by fastforce
  *)      

  lemma threshold_positive: "threshold TYPE(('e,'f) float) > 0"  
    unfolding threshold_def
    apply (simp add: field_simps)
    by (smt (z3) two_less_eq_exp_length)
    
  lemma threshold_not_negative[simp]: 
    "\<not>threshold TYPE(('e,'f) float) \<le> 0"  
    "threshold TYPE(('e,'f) float) \<noteq> 0"  
    using threshold_positive
    by (smt (verit))+
    
    
    
  lemma largest_gtZ: "largest TYPE((_,_) float) > 0"  
    by (simp add: divide_less_eq largest_def power_gt1_lemma)

  lemma largest_gtZ'[simp]: 
    "\<not>(largest TYPE((_,_) float) < 0)"  
    "largest TYPE((_,_) float) \<noteq> 0"  
    by (smt (verit) largest_gtZ)+

  lemma threshold_gt_largest: "threshold TYPE(('e,'f) float) > largest TYPE(('e,'f) float)"  
    unfolding threshold_def largest_def
    by (auto simp: field_simps)

    
    
  lemma less_neq_topfloat:  
    fixes f f' :: "('e,'f) float"
    assumes LENE: "1 < LENGTH('e)"
    assumes FIN: "is_finite f" "is_finite f'"
    assumes VLT: "valof f < valof f'"
    shows "f\<noteq>topfloat"
    by (smt (verit) LENE FIN VLT float_val_le_largest valof_topfloat)
    
    
  lemma ex_less_eq_float_conv:
    assumes "1 < LENGTH('e)"
    shows "(\<exists>x::('e,'f) float. is_finite x \<and> valof x \<le> r) \<longleftrightarrow> valof (bottomfloat::('e,'f) float) \<le> r"  
    apply auto
    subgoal using assms float_val_ge_bottomfloat by force
    done
    
  lemma no_finite_ge_aux[simp]:
    "1<LENGTH('e) \<Longrightarrow> (\<forall>x::('e, 'f) float. is_finite x \<longrightarrow> \<not> r \<le> valof x) \<longleftrightarrow> largest TYPE(('e, 'f) float) < r"
    apply auto
    subgoal by (smt (verit, best) One_nat_def finite_topfloat valof_topfloat)
    subgoal by (smt (verit, best) One_nat_def float_val_le_largest)
    done    

  lemma no_finite_lt_aux[simp]:
    "1<LENGTH('e) \<Longrightarrow> (\<forall>x::('e, 'f) float. is_finite x \<longrightarrow> \<not> valof x \<le> r) \<longleftrightarrow> r < -largest TYPE(('e, 'f) float)"
    apply auto
    subgoal by (smt (verit, best) One_nat_def bottomfloat_eq_m_largest finite_bottomfloat)
    subgoal by (smt (verit, ccfv_threshold) One_nat_def float_val_ge_largest)
    done    
    
  lemma valof_eqZ_cases:
    assumes "valof f = 0"
    assumes "is_finite f"
    obtains "f=-0" | "f=0"  
    using assms(1) assms(2) sign_neg_iff_valof sign_pos_iff_valof by fastforce
    
    
  lemma nz_float_eq_valof_iff: "\<lbrakk>\<not>is_zero f; is_finite f; is_finite f'; 1 < LENGTH('e)\<rbrakk> \<Longrightarrow> f=f' \<longleftrightarrow> valof f = valof f'"
    for f :: "('e,'f) float"
    by (auto simp: is_zero_iff_valof0 dest: valof_almost_injective)
    
    

  subsubsection \<open>Closest\<close>  

  lemma is_closest_unique':
    fixes x :: real
    assumes "is_closest v s x a"
    assumes "is_closest v s x a'"
    assumes "\<forall>b\<in>s. \<forall>b'\<in>s. v b \<noteq> v b' \<longrightarrow> \<bar>v b - x\<bar> \<noteq> \<bar>v b' - x\<bar>"
    shows "v a = v a'"
    using assms
    unfolding is_closest_def
    apply (clarsimp)
    by fastforce
    
  lemma valof_closest_T_I:
    fixes f :: "('e,'f) float"
    assumes "1 < LENGTH('e)" "s\<noteq>{}"
    assumes CLF: "is_closest valof s r f"
    assumes UNIQ: "\<forall>b\<in>s. \<forall>b'\<in>s. valof b \<noteq> valof b' \<longrightarrow> \<bar>valof b - r\<bar> \<noteq> \<bar>valof b' - r\<bar>"
    shows "valof (closest valof (\<lambda>_. True) s r :: ('e,'f) float) = valof f"  
  proof -
    let ?f = "closest valof (\<lambda>_. True) s r :: ('e,'f) float"
    
    have CLC: "is_closest valof s r ?f"
      by (rule closest_is_closest) fact
    
    from is_closest_unique'[OF CLC CLF UNIQ] show ?thesis .
  qed
            
  lemma closest_eq_in_setD: "\<lbrakk>closest valof p s r = f; s\<noteq>{}\<rbrakk> \<Longrightarrow> f\<in>s"
    using closest_in_set finite by blast
    
    
  lemma closest_unique_predI:
    assumes "s\<noteq>{}"
    assumes "\<And>a. is_closest valof s r a \<Longrightarrow> P a"
    shows "P (closest valof p s r)"  
    by (simp add: assms(1) assms(2) closest_is_closest)
    
  lemma closest_precise_eqI: "\<lbrakk>x\<in>s; \<not>is_zero x; s\<subseteq>Collect is_finite\<rbrakk> \<Longrightarrow> closest valof p s (valof x) = x"
    apply (rule closest_unique_predI)
    apply (auto simp: is_closest_def)
    subgoal for a
      apply (subgoal_tac "valof a = valof x")
      by (auto simp add: subset_eq valof_nonzero_injective)
    done
    
  lemma finite_closest_valofI: "s\<noteq>{} \<Longrightarrow> s\<subseteq>Collect is_finite \<Longrightarrow> is_finite (closest valof p s r)"  
    using closest_eq_in_setD by blast
    
    
  lemma is_zero_closestI:
    assumes "0\<in>s \<or> -0\<in>s"
    assumes "s\<subseteq>Collect is_finite"
    shows "is_zero (closest valof p s 0)"
    apply (rule closest_unique_predI)
    using assms apply auto
    unfolding is_closest_def
    by (auto 0 3 simp: is_zero_iff_valof0)

    
  subsubsection \<open>Round\<close>  
  lemma is_zero_round_zero[simp]:
    shows "is_zero (IEEE.round m 0::('e, 'f) float)" (is "is_zero ?f")
    apply (cases m; auto)
    apply (auto intro!: is_zero_closestI)
    done
    
  lemma is_finite_roundI:
    assumes [simp]: "1<LENGTH('e)"
    assumes "m\<noteq>To_nearest" 
    assumes "- largest TYPE(('e, 'f) float) \<le> r"
    assumes "r\<le>largest TYPE(('e, 'f) float)"
    shows "is_finite (round m r :: ('e, 'f) float)"  
    using assms 
    apply (cases m; simp)
    apply (auto intro!: finite_closest_valofI)   
    done
        
  lemma is_finite_round_nearestI: 
    assumes "- threshold TYPE(('e, 'f) float) < r"
    assumes "r<threshold TYPE(('e, 'f) float)"
    shows "is_finite (round To_nearest r :: ('e, 'f) float)"  
    using assms 
    by (auto intro!: finite_closest_valofI)   
    
  subsubsection \<open>Zerosign\<close>
  lemma zerosign_eqZ_conv[simp]:
    fixes f :: "('e,'f) float"
    assumes "is_finite f"
    shows "zerosign s f = 0 \<longleftrightarrow> valof f=0 \<and> s=0"
    using assms
    by (auto simp: zerosign_def is_zero_iff_valof0)
    
  lemma zerosign_eqMZ_conv[simp]:
    fixes f :: "('e,'f) float"
    assumes "is_finite f"
    shows "zerosign s f = -0 \<longleftrightarrow> valof f=0 \<and> s>0"
    using assms
    by (auto simp: zerosign_def is_zero_iff_valof0)

  lemma zerosign_infty[simp]:
    "zerosign s (-\<infinity>) = -\<infinity>"
    "zerosign s (\<infinity>) = \<infinity>"
    by (simp_all add: zerosign_def)  
    
  lemma zerosign_top[simp]:
    "zerosign s (-topfloat) = -topfloat"
    "zerosign s (topfloat) = topfloat"
    by (simp_all add: zerosign_def)  
    
        
  subsection \<open>Basic Definition\<close>

  find_theorems "_ = 2^LENGTH(_)"
  find_consts "_ word" name: max
  
  lift_definition next_float :: "('e,'f) float \<Rightarrow> ('e,'f) float" is
    "\<lambda>(s,e,f). if s=1 then (
        if f=0 \<and> e=0 then (0,e,f)
        else if f=0 then (s,e-1,f-1)
        else (s,e,f-1)
      ) else (
        if f=-1 then (s,e+1,0)
        else (s,e,f+1)
      )
    " .

  lemma sign_next_float: "sign (next_float f) = (if f=-0 then 0 else sign f)"      
    apply transfer'
    apply (auto split: if_splits)
    done
    
  
  
  lemma exp_next_float: "is_finite f \<Longrightarrow> f\<noteq>topfloat \<Longrightarrow> exponent (next_float f) = (if f=-0 then 0 else (
    if sign f = 1 \<and> fraction f = 0 then exponent f - 1
    else if sign f = 0 \<and> fraction f = 2^LENGTH('f)-1 then exponent f + 1
    else exponent f))" for f :: "('e,'f) float"
    unfolding float_defs
    apply transfer'
    apply clarsimp
    apply (auto split: if_splits simp: unat_eq_0 unat_minus_one unat_minus_one_word)
    subgoal by (metis emax_def less_not_refl2 unat_Suc2)
    apply (simp add: unat_minus_one_word word_eq_unatI)
    apply (simp add: unat_minus_one_word word_eq_unatI)
    done
    
  lemma frac_next_float: "is_finite f \<Longrightarrow> f\<noteq>topfloat \<Longrightarrow> fraction (next_float f) = (if f=-0 then 0 else (
    if sign f = 1 \<and> fraction f = 0 then 2^LENGTH('f)-1
    else if sign f = 1 then fraction f - 1
    else if fraction f = 2^LENGTH('f)-1 then 0
    else fraction f + 1
  ))" for f :: "('e,'f) float"
    unfolding float_defs
    apply transfer'
    apply clarsimp
    apply (auto split: if_splits simp: unat_eq_0 unat_minus_one unat_minus_one_word)
    subgoal by (simp add: unat_minus_one_word word_eq_unatI)
    subgoal using unat_Suc2 by blast
    subgoal by (simp add: unat_minus_one_word word_eq_unatI)
    subgoal using unat_Suc2 by auto
    done
        
  lemmas next_float_defs = sign_next_float frac_next_float exp_next_float  

  subsection \<open>Additional Properties\<close>
  lemma next_float_finiteI[simp]: "\<lbrakk>is_finite f; f\<noteq>topfloat\<rbrakk> \<Longrightarrow> is_finite (next_float f)"
    by (auto simp: float_defs next_float_defs float_eq_conv Suc_lessI)
  
  subsection \<open>Correctness\<close>
  lemma next_float_increases:
    fixes f :: "('e,'f) float"
    assumes "is_finite f" "f\<noteq>topfloat" "f\<noteq>-0" 
    shows "valof f < valof (next_float f)" 
    using assms
    apply (simp add: valof_eq next_float_defs)
    apply (clarsimp simp: float_defs float_eq_conv)
    
    apply (cases f rule: sign_cases; simp)
    subgoal
      apply (cases "fraction f = 2 ^ LENGTH('f) - Suc 0"; cases "exponent f = 0"; simp add: nat_gtZ_or_Z)
      apply (simp_all add: divide_less_eq)
      done
    subgoal
      apply (cases "fraction f = 0"; simp add: )
      apply (intro conjI impI)
      apply (simp_all add: divide_less_eq fp_pred_exp_less)
      done
    done

    
  lemma next_float_mzero[simp]: "next_float (-0) = 0"  
    by (auto simp add: float_eq_conv valof_eq next_float_defs)
    
  lemma next_float_tight: 
    fixes f f' :: "('e,'f) float"
    assumes "is_finite f" "f\<noteq>topfloat" 
    assumes "is_finite f'" 
    assumes "valof f < valof f'"
    shows "valof (next_float f) \<le> valof f'"
    
    using assms
    apply (simp flip: fcc_le_valof fcc_lt_valof add: next_float_finiteI)
    
    apply (cases f f' rule: fcc_le_cases; 
      clarsimp simp: fcc_lt_def fcc_le_def is_zero_iff_valof0 next_float_defs
    )
    
    using float_frac_le[where a=f']
    apply (safe, simp_all) (* Significantly speeds up the following auto *)
    apply (auto
      simp: fcc_le_samesign_def fcc_lt_samesign_def next_float_defs 
      split: if_splits)
    done

    

  subsection \<open>Previous Float\<close>  
  lift_definition prev_float :: "('e,'f) float \<Rightarrow> ('e,'f) float" is
    "\<lambda>(s,e,f). if s=0 then (
        if f=0 \<and> e=0 then (1,e,f)
        else if f=0 then (s,e-1,-1)
        else (s,e,f-1)
      ) else (
        if f=-1 then (s,e+1,0)
        else (s,e,f+1)
      )
    " .

  lemma sign_prev_float: "sign (prev_float f) = (if f=0 then 1 else sign f)"      
    apply transfer'
    apply (auto split: if_splits)
    done

  lemma exp_prev_float: "is_finite f \<Longrightarrow> f\<noteq>bottomfloat \<Longrightarrow> exponent (prev_float f) = (
    if fraction f = 0 \<and> sign f = 0 \<and> exponent f \<noteq> 0 then exponent f-1
    else if fraction f = 2^LENGTH('f)-1 \<and> sign f = 1 then exponent f + 1
    else exponent f
  )" for f :: "('e,'f) float"
    unfolding float_defs
    apply transfer'
    subgoal for ff
      apply (cases ff)
      subgoal for s e f
        apply (auto split: if_splits simp: unat_eq_0 word_eq_unatI unat_minus_one unat_minus_one_word)
        subgoal by (metis emax_def nat_neq_iff unat_Suc2)
        subgoal by (metis One_nat_def degenerate_word_ne1 unat_1)
        subgoal by (metis One_nat_def degenerate_word_ne1 unsigned_1)
        done
      done
    done

  lemma frac_prev_float: "is_finite f \<Longrightarrow> f\<noteq>bottomfloat \<Longrightarrow> fraction (prev_float f) = (if f=0 then 0 else (
    if sign f = 0 \<and> fraction f = 0 then 2^LENGTH('f)-1
    else if sign f = 0 then fraction f - 1
    else if fraction f = 2^LENGTH('f)-1 then 0
    else fraction f + 1
  ))" for f :: "('e,'f) float"
    unfolding float_defs
    apply transfer'
    subgoal for ff
      apply (cases ff; simp)
      subgoal for s e f
        apply (intro allI conjI impI; (elim conjE)?)
        apply (simp_all add: unat_Suc2 unat_eq_0 word_eq_unatI unat_minus_one unat_minus_one_word)
        subgoal
          by (metis One_nat_def Suc_diff_diff Suc_unat_minus_one diff_Suc_1 diff_numeral_special(10) nat_neq_iff 
                unat_bintrunc_neg unat_max_word_pos unat_minus_one_word unsigned_eq_0_iff)
        done
      done
    done
      
  lemmas prev_float_defs = sign_prev_float frac_prev_float exp_prev_float  
    
  lemma prev_float_finiteI[simp]: "\<lbrakk>is_finite f; f\<noteq>bottomfloat\<rbrakk> \<Longrightarrow> is_finite (prev_float f)"
    by (auto simp: float_defs prev_float_defs float_eq_conv Suc_lessI)

  lemma prev_float_ne_top: "\<lbrakk>is_finite f; f\<noteq>bottomfloat\<rbrakk> \<Longrightarrow> prev_float f \<noteq> topfloat"  
    apply (clarsimp simp: float_defs prev_float_defs float_eq_conv)
    by (metis Suc_pred fraction_upper_bound less_zeroE nat_neq_iff)
    
  lemma next_float_ne_bot: "\<lbrakk>is_finite f; f\<noteq>topfloat\<rbrakk> \<Longrightarrow> next_float f \<noteq> bottomfloat"  
    apply (clarsimp simp: float_defs next_float_defs float_eq_conv)
    by (metis Suc_pred fraction_upper_bound less_zeroE nat_neq_iff)
      
  lemma next_float_eq_zero_conv: "\<lbrakk>is_finite f; f\<noteq>topfloat\<rbrakk> \<Longrightarrow> next_float f = 0 \<longleftrightarrow> f=-0"  
    by (clarsimp simp: next_float_defs float_eq_conv)

  lemma prev_float_eq_nzero_conv: "\<lbrakk>is_finite f; f\<noteq>bottomfloat\<rbrakk> \<Longrightarrow> prev_float f = -0 \<longleftrightarrow> f=0"  
    by (clarsimp simp: prev_float_defs float_eq_conv)
    
        
  lemma prev_next_float_id[simp]:
    fixes f :: "('e,'f) float"
    assumes "is_finite f" 
    assumes "f\<noteq>topfloat"  
    shows "prev_float (next_float f) = f"
  proof -
    note A = next_float_finiteI[OF assms] next_float_ne_bot[OF assms]
    
    note B = next_float_defs[of f, simplified assms, simplified]
    
    note C = prev_float_defs[of "next_float f", simplified A B, simplified]
    
    note D = next_float_eq_zero_conv[of f, simplified assms, simplified]
    
    have [simp]: "fraction f - Suc 0 \<noteq> 2 ^ LENGTH('f) - Suc 0"
      by (metis Suc_lessD Suc_pred Word.of_nat_neq_0 fraction_upper_bound of_nat_2p two_plen_gt1 zero_less_diff)
    
    show ?thesis
      apply (rule float_eqI)
      unfolding C D
      apply (simp add: )
      apply (simp add: )
      apply (simp split!: if_splits add: float_eq_conv)
      done
  qed    
    
  lemma next_prev_float_id[simp]:
    fixes f :: "('e,'f) float"
    assumes "is_finite f" 
    assumes "f\<noteq>bottomfloat"  
    shows "next_float (prev_float f) = f"
  proof -
    note A = prev_float_finiteI[OF assms] prev_float_ne_top[OF assms]
    
    note B = prev_float_defs[of f, simplified assms, simplified]
    
    note C = next_float_defs[of "prev_float f", simplified A B, simplified]
    
    note D = prev_float_eq_nzero_conv[of f, simplified assms, simplified]
    
    have [simp]: "fraction f - Suc 0 \<noteq> 2 ^ LENGTH('f) - Suc 0"
      by (metis Suc_lessD Suc_pred Word.of_nat_neq_0 fraction_upper_bound of_nat_2p two_plen_gt1 zero_less_diff)
    
    show ?thesis
      apply (rule float_eqI)
      unfolding C D
      apply (simp_all)
      apply (simp add: float_eq_conv)
      done
  qed    

  
  lemma prev_float_tight: 
    fixes f f' :: "('e,'f) float"
    assumes "is_finite f" 
    assumes "is_finite f'" "f'\<noteq>bottomfloat" 
    assumes "valof f < valof f'"
    shows "valof f \<le> valof (prev_float f')"
    by (smt (verit, ccfv_threshold) assms(1) assms(2) assms(3) assms(4) next_float_tight next_prev_float_id prev_float_finiteI prev_float_ne_top)
        

    
    
    
  lemma nextfloat_even_odd:
    assumes "is_finite f" "f \<noteq> topfloat" "f\<noteq>-0"
    assumes "even (fraction f)"
    shows "odd (fraction (next_float f))"
    using assms by (auto simp add: next_float_defs)

  lemma nextfloat_odd_even:
    assumes "is_finite f" "f \<noteq> topfloat"
    assumes "odd (fraction f)"
    shows "even (fraction (next_float f))"
    using assms by (auto simp add: next_float_defs)
    
  lemma next_float_eqZ_iff: "\<lbrakk>is_finite f; f\<noteq>topfloat\<rbrakk> \<Longrightarrow> next_float f = 0 \<longleftrightarrow> f=-0"
    by (metis leD next_float_increases next_float_mzero sign_next_float valof_nonneg valof_zero(1))  


  definition "next_float' f \<equiv> 
    if f=-0 then next_float 0 
    else if next_float f = -0 then 0
    else next_float f"  
    
  context
    fixes f :: "('e,'f) float"
    assumes FIN: "is_finite f"
    assumes FNT: "f\<noteq>topfloat"
  begin
    lemma next_float'_finiteI: "is_finite (next_float' f)"
      by (simp add: FIN FNT next_float'_def)
  
    lemma next_float'_increases: "valof f < valof (next_float' f)"
      by (metis (no_types, lifting) FIN FNT float_class_consts(21) float_ineqs(13) float_neq_minus_self next_float'_def next_float_increases valof_zero(1) valof_zero(2))
  
    lemma next_float'_even_iff[simp]: "even (fraction (next_float' f)) \<longleftrightarrow> odd (fraction f)"
      by (metis (no_types, lifting) FIN FNT float_class_consts(21) float_defs(27) float_ineqs(13) float_sel_simps(11) float_sel_simps(7) next_float'_def nextfloat_even_odd nextfloat_odd_even sign_pos_iff_valof)

    lemma next_float'_tight: 
      fixes f' :: "('e,'f) float"
      shows "is_finite f' \<Longrightarrow> valof f < valof f' \<Longrightarrow> valof (next_float' f) \<le> valof f'"
      apply (auto simp: next_float'_def FIN FNT intro: next_float_tight)
      by (metis FIN FNT next_float_tight valof_zero(2))
            
  end

  lemma next_float'_not_minus_zer[simp]: "next_float' f \<noteq> -0"
    by (metis float_sel_simps(7) float_sel_simps(8) next_float'_def sign_next_float zero_neq_one)
      
  
  
  lemma next_float'_if_nothing_in_between:
    fixes f :: "('e,'f) float"
    assumes LENE: "1 < LENGTH('e)"
    assumes FIN: "is_finite f" "is_finite f'"
    assumes VLT: "valof f < valof f'" and [simp]: "f'\<noteq>-0"
    assumes NIB: "\<nexists>b::('e,'f) float. is_finite b \<and> valof f < valof b \<and> valof b < valof f'"
    shows "f' = next_float' f"  
  proof -
    have FNT: "f\<noteq>topfloat"
      using VLT assms(1) assms(3) finite_topfloat less_neq_topfloat by blast 

    hence FNF: "is_finite (next_float' f)"
      using assms(2) next_float'_finiteI by blast
      
    have FLT: "valof f < valof (next_float' f)" 
      by (simp add: \<open>f \<noteq> topfloat\<close> assms(2) next_float'_increases)
    
    have NFLE: "valof (next_float' f) \<le> valof f'"
      by (simp add: VLT \<open>f \<noteq> topfloat\<close> assms(2) assms(3) next_float'_tight)  

    have "\<not>(valof (next_float' f) < valof f')" 
      apply (rule)
      using NIB FNF FLT by blast
     
    hence VEQ: "valof (next_float' f) = valof f'" using NFLE by auto  
    show "f' = next_float' f" 
      using valof_almost_injective[OF FNF FIN(2) VEQ]
      by (auto simp: FNT FIN)
      
      
  qed    
  
        
  lemma next_float_if_nothing_in_between:
    fixes f :: "('e,'f) float"
    assumes LENE: "1 < LENGTH('e)"
    assumes FIN: "is_finite f" "is_finite f'"
    assumes VLT: "valof f < valof f'"
    assumes NZ: "f\<noteq>-0" "f'\<noteq>0"
    assumes NIB: "\<nexists>b::('e,'f) float. is_finite b \<and> valof f < valof b \<and> valof b < valof f'"
    shows "f' = next_float f"  
  proof -
    have FNT: "f\<noteq>topfloat"
      using VLT assms(1) assms(3) finite_topfloat less_neq_topfloat by blast 

    hence FNF: "is_finite (next_float f)"
      using assms(2) next_float_finiteI by blast
      
    from NZ have FLT: "valof f < valof (next_float f)" 
      by (simp add: \<open>f \<noteq> topfloat\<close> assms(2) next_float_increases)
    
    have NFLE: "valof (next_float f) \<le> valof f'"
      by (simp add: VLT \<open>f \<noteq> topfloat\<close> assms(2) assms(3) next_float_tight)  

    have "\<not>(valof (next_float f) < valof f')" 
      apply (rule)
      using NIB FNF FLT by blast
     
    hence VEQ: "valof (next_float f) = valof f'" using NFLE by auto  
    show "f' = next_float f" 
      using valof_almost_injective[OF FNF FIN(2) VEQ]
      by (auto simp: NZ next_float_eqZ_iff FNT FIN)
      
  qed    
      
  lemma valof_nextfloat': "f\<noteq>-0 \<Longrightarrow> valof (next_float' f) = valof (next_float f)"
    unfolding next_float'_def
    by auto
    

  subsection \<open>Bounding Result of Rounding\<close>    
  
  subsubsection \<open>To Negative Infinity\<close>
  lemma bprec_round_ninf:
    fixes f :: "('e,'f) float"
    assumes "1 < LENGTH('e)"
    assumes "is_finite f" "f\<noteq>topfloat"
    assumes "valof f \<le> r" "r < valof (next_float f)"
    shows "valof (round To_ninfinity r :: ('e,'f) float) = valof f"  
    using assms
    apply (auto)
    subgoal by (smt (verit, ccfv_SIG) largest_gtZ) 
    subgoal using float_val_le_largest next_float_finiteI by force
    subgoal using float_val_ge_largest by fastforce
    subgoal
      apply (rule valof_closest_T_I)
      apply auto
      unfolding is_closest_def apply (auto simp: assms)
      using assms(2) assms(3) assms(5) next_float_tight by fastforce
    done  
    

  subsubsection \<open>To Positive Infinity\<close>
  lemma bprec_round_pinf:
    fixes f :: "('e,'f) float"
    assumes "1 < LENGTH('e)"
    assumes "is_finite f" "f\<noteq>bottomfloat"
    assumes "valof (prev_float f) < r" "r \<le> valof f"
    shows "valof (round To_pinfinity r :: ('e,'f) float) = valof f"  
    using assms
    apply (auto)
    subgoal by (smt (verit, ccfv_SIG) largest_gtZ) 
    subgoal using float_val_le_largest by fastforce
    subgoal using float_val_ge_largest prev_float_finiteI by fastforce
    subgoal
      apply (rule valof_closest_T_I)
      using prev_float_finiteI[OF assms(2,3)]
      apply auto 
      unfolding is_closest_def apply (auto simp: assms)
      using assms(2) assms(3) assms(4) prev_float_tight by fastforce
    done  

  subsubsection \<open>To Zero\<close>
    
  lemma bprec_round_zero_neg:
    fixes f :: "('e,'f) float"
    assumes "1 < LENGTH('e)"
    assumes "is_finite f" "f\<noteq>bottomfloat" "r \<le> 0"
    assumes "valof (prev_float f) < r" "r \<le> valof f"
    shows "valof (round float_To_zero r :: ('e,'f) float) = valof f"  
    apply (auto)
    subgoal by (smt (verit, ccfv_SIG) largest_gtZ)
    subgoal using assms(4) assms(6) by force
    subgoal using assms(1) assms(2) assms(5) float_val_ge_largest prev_float_finiteI by fastforce
    subgoal
      apply (rule valof_closest_T_I)
      using assms(1)
      using prev_float_finiteI[OF assms(2,3)]
      apply auto 
      unfolding is_closest_def using assms apply (auto)
      subgoal using prev_float_tight by fastforce
      using prev_float_tight by fastforce
    done  
  
  lemma bprec_round_zero_pos:
    fixes f :: "('e,'f) float"
    assumes "1 < LENGTH('e)"
    assumes "is_finite f" "f\<noteq>topfloat" "0 \<le> r"
    assumes "valof f \<le> r" "r < valof (next_float f)"
    shows "valof (round float_To_zero r :: ('e,'f) float) = valof f"  
    using assms
    apply (auto)
    subgoal using float_val_ge_largest by fastforce
    subgoal using float_val_le_largest next_float_finiteI by fastforce
    subgoal
      apply (rule valof_closest_T_I)
      apply auto 
      unfolding is_closest_def apply (auto simp: assms)
      subgoal using assms(2) assms(3) assms(4) assms(5) assms(6) next_float_tight by fastforce
      using assms(2) assms(3) assms(6) next_float_tight by fastforce
    done  
    
  subsubsection \<open>To Nearest\<close>

  lemma valof_closest_even_I:
    fixes f :: "('e,'f) float"
    defines "p\<equiv>(\<lambda>f. even (fraction f))"
    assumes "1 < LENGTH('e)"
    assumes CLF: "is_closest valof {f. is_finite f} r f"
    assumes "\<And>f'. \<lbrakk>is_closest valof {f. is_finite f} r f'; p f'\<rbrakk> \<Longrightarrow> p f"
    shows "valof (closest valof p {f. is_finite f} r :: ('e,'f) float) = valof f"  
  proof -
    let ?f = "closest valof p {f. is_finite f} r :: ('e,'f) float"
    
    have CLC: "is_closest valof {f. is_finite f} r ?f"
      apply (rule closest_is_closest)
      using is_finite_nonempty by blast
    hence FINFF[simp]: "is_finite ?f" and C1: "\<forall>b::('e,'f) float. is_finite b \<longrightarrow> \<bar>valof ?f - r\<bar> \<le> \<bar>valof b - r\<bar>"
      unfolding is_closest_def by auto
      
    from CLF have FINF[simp]: "is_finite f" and C2: "\<forall>b::('e,'f) float. is_finite b \<longrightarrow> \<bar>valof f - r\<bar> \<le> \<bar>valof b - r\<bar>"
      unfolding is_closest_def by auto
      
    from C1 C2 have EQ: "\<bar>valof ?f - r\<bar> = \<bar>valof f - r\<bar>"
      by (meson \<open>is_finite f\<close> is_finite_closest nle_le)  
    
    show ?thesis proof (rule ccontr)
      assume A: "valof ?f \<noteq> valof f"
      with EQ have "valof ?f - r = -valof f + r" by auto
      hence "valof ?f = 2*r-valof f" by auto
      
      consider "valof f < valof ?f" | "valof ?f < valof f" using A by fastforce
      then show False proof cases
        case 1
        
        from 1 have "f\<noteq>topfloat"
          by (metis assms(2) float_val_le_largest is_finite_closest leD valof_topfloat)
        
        have NIB: "\<nexists>b::('e,'f) float. is_finite b \<and> valof f < valof b \<and> valof b < valof ?f"
          using 1 C1 C2 by fastforce
        
        {
          assume "?f\<noteq>-0"  
            
          have "?f = next_float' f" 
            apply (rule next_float'_if_nothing_in_between)
            apply fact+
            done
            
          hence False
            by (metis CLF FINF \<open>f \<noteq> topfloat\<close> assms(1) assms(4) closest_is_everything finite is_finite_nonempty next_float'_even_iff)  
        } moreover {
          assume "?f=-0"
          hence False 
            by (metis (no_types, lifting) "1" CLC FINF FINFF NIB \<open>f \<noteq> topfloat\<close> assms(1) assms(2) assms(4) float_defs(26) float_defs(27) float_sel_simps(13) next_float'_def next_float'_even_iff next_float_if_nothing_in_between next_float_mzero nextfloat_odd_even sign_pos_iff_valof)
        }    
        ultimately show False by blast
      next
        case 2
          
        from 2 have "?f\<noteq>topfloat"
          by (metis FINF assms(2) finite_topfloat less_neq_topfloat)
        
        have NIB: "\<nexists>b::('e,'f) float. is_finite b \<and> valof ?f < valof b \<and> valof b < valof f"
          using 2 C1 C2 by fastforce
        
        {
          assume "f\<noteq>-0"  
            
          have "f = next_float' ?f" 
            apply (rule next_float'_if_nothing_in_between)
            apply fact+
            done
            
          hence False
            by (metis CLF FINFF \<open>closest valof p {f. is_finite f} r \<noteq> topfloat\<close> assms(1) assms(4) closest_is_everything finite is_finite_nonempty next_float'_even_iff)
        } moreover {
          assume "f=-0"
          hence False 
            by (smt (verit, best) "2" CLF FINF FINFF NIB assms(1) assms(2) closest_is_everything finite float_defs(27) float_sel_simps(11) is_finite_nonempty largest_gtZ next_float'_increases next_float'_tight next_float_eqZ_iff next_float_finiteI nextfloat_even_odd nextfloat_odd_even valof_eq_zero_conv valof_nextfloat' valof_topfloat)
        }    
        ultimately show False by blast
      qed  
    qed
  qed      

      
  lemma bprec_round_nearest_down:
    fixes f :: "('e,'f) float"
    assumes "1 < LENGTH('e)"
    assumes "is_finite f" "f\<noteq>topfloat" 
    assumes "valof f \<le> r" "r \<le> valof (next_float f)"
    assumes "\<bar>r - valof f\<bar> < \<bar>valof (next_float f) - r\<bar>"
    shows "valof (round To_nearest r :: ('e,'f) float) = valof f"  
    using assms
    apply (auto)
    subgoal using float_val_gt_threshold by fastforce
    subgoal using float_val_lt_threshold next_float_finiteI by fastforce
    subgoal using float_val_gt_threshold by fastforce
    subgoal
      apply (rule valof_closest_even_I)
      apply auto 
      subgoal
        unfolding is_closest_def apply (auto simp: assms)
        using assms(2) assms(3) assms(6) next_float_tight by fastforce
      subgoal
        unfolding is_closest_def apply (auto simp: assms)
        by (smt (verit, best) assms(2) assms(3) assms(4) float_sel_simps(11) float_sel_simps(12) next_float_tight valof_almost_injective)
      
      done  
    done    

  lemma bprec_round_nearest_up:
    fixes f :: "('e,'f) float"
    assumes "1 < LENGTH('e)"
    assumes "is_finite f" "f\<noteq>topfloat"
    assumes "valof f \<le> r" "r \<le> valof (next_float f)"
    assumes "\<bar>r - valof f\<bar> > \<bar>valof (next_float f) - r\<bar>"
    shows "valof (round To_nearest r :: ('e,'f) float) = valof (next_float f)"  
    using assms
    apply (auto)
    subgoal using float_val_gt_threshold by fastforce
    subgoal using float_val_lt_threshold next_float_finiteI by fastforce
    subgoal using float_val_gt_threshold by force
    subgoal
      apply (rule valof_closest_even_I)
      apply auto 
      using next_float_finiteI[OF assms(2,3)]
      subgoal
        unfolding is_closest_def apply (auto simp: assms)
        using assms(2) assms(3) assms(6) next_float_tight by fastforce
      subgoal
        unfolding is_closest_def apply (auto simp: assms)
        by (smt (verit, best) \<open>is_finite (next_float f)\<close> assms(2) assms(3) assms(5) float_sel_simps(11) float_sel_simps(12) next_float_tight valof_almost_injective)
      done  
    done    

  lemma bprec_round_nearest_down_even:
    fixes f :: "('e,'f) float"
    assumes "1 < LENGTH('e)"
    assumes "is_finite f" "f\<noteq>topfloat"
    assumes "valof f \<le> r" "r \<le> valof (next_float f)"
    assumes "\<bar>r - valof f\<bar> = \<bar>valof (next_float f) - r\<bar>" "even (fraction f)"
    shows "valof (round To_nearest r :: ('e,'f) float) = valof f"  
    using assms
    apply (auto)
    subgoal using float_val_gt_threshold by fastforce
    subgoal using float_val_lt_threshold next_float_finiteI by fastforce
    subgoal using float_val_gt_threshold by fastforce
    subgoal
      apply (rule valof_closest_even_I)
      apply auto 
      subgoal
        unfolding is_closest_def apply (auto simp: assms)
        using assms(2) assms(3) assms(6) next_float_tight by fastforce
      done  
    done    
    
  lemma bprec_round_nearest_up_even:
    fixes f :: "('e,'f) float"
    assumes "1 < LENGTH('e)"
    assumes "is_finite f" "f\<noteq>topfloat"
    assumes "valof f \<le> r" "r \<le> valof (next_float f)"
    assumes "\<bar>r - valof f\<bar> = \<bar>valof (next_float f) - r\<bar>" "even (fraction (next_float f))"
    shows "valof (round To_nearest r :: ('e,'f) float) = valof (next_float f)"  
    using assms
    apply (auto)
    subgoal using float_val_gt_threshold by fastforce
    subgoal using float_val_lt_threshold next_float_finiteI by fastforce
    subgoal using float_val_gt_threshold by fastforce
    subgoal
      apply (rule valof_closest_even_I)
      apply auto 
      subgoal
        using next_float_finiteI[OF assms(2,3)]
        unfolding is_closest_def apply (auto simp: assms)
        using assms(2) assms(3) assms(6) next_float_tight by fastforce
      done  
    done    
  
  
end
