section \<open>Next Floating Point Number\<close>
theory IEEE_Fp_Nextfloat
imports IEEE_Fp_Add_Basic "HOL-Library.Rewrite"
begin

  subsection \<open>Miscellaneous\<close>
  subsubsection \<open>Basic Properties\<close>
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
    subgoal using finite_bottomfloat by blast 
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
    apply (clarsimp simp: float_defs next_float_defs float_eq_conv)
    by (metis One_nat_def Suc_lessI diff_Suc_1 emax_pos(1) less_imp_diff_less less_numeral_extra(3))
  
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
    apply (clarsimp simp: float_defs prev_float_defs float_eq_conv)
    by (metis One_nat_def Suc_lessI diff_Suc_1 emax_ge1 emax_gt1_iff_e_gt1 less_imp_diff_less nat_less_le not_less)

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
      apply (metis One_nat_def Suc_diff_Suc Suc_pred diff_Suc_1 float_sel_simps(11) fraction_upper_bound nat_less_le two_plen_gt1)    
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
      by (simp add: FIN FNT next_float'_def next_float_finiteI)
  
    lemma next_float'_increases: "valof f < valof (next_float' f)"
      by (smt (verit, ccfv_SIG) FIN FNT float_sel_simps(7) next_float'_def next_float_increases sign_pos_iff_valof valof_zero(2) zero_finite zero_neq_topfloat(1))
  
    lemma next_float'_even_iff[simp]: "even (fraction (next_float' f)) \<longleftrightarrow> odd (fraction f)"
      by (metis (no_types, lifting) FIN FNT float_defs(27) float_sel_simps(11) float_sel_simps(7) next_float'_def nextfloat_even_odd nextfloat_odd_even sign_pos_iff_valof zero_finite zero_neq_topfloat(1))

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
      subgoal using prev_float_tight zero_finite by fastforce
      using prev_float_tight by force
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
      subgoal using assms(2) assms(3) assms(4) assms(5) assms(6) next_float_tight zero_finite by fastforce
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
            by (smt (verit, best) "1" CLF FINF NIB \<open>f \<noteq> topfloat\<close> assms(1) assms(4) closest_is_everything finite fraction_uminus is_finite_nonempty is_zero_cases next_float'_even_iff next_float'_finiteI next_float'_increases next_float'_tight valof_nonzero_injective valof_zero(1) valof_zero(2) zero_finite)
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
            by (smt (z3) "2" CLF FINF FINFF NIB \<open>closest valof p {f. is_finite f} r \<noteq> topfloat\<close> assms(1) closest_is_everything finite float_defs(27) float_sel_simps(11) is_finite_nonempty mzero_neq_topfloat(2) next_float_finiteI next_float_increases next_float_mzero next_float_tight nextfloat_even_odd nextfloat_odd_even sign_neg_iff_valof sign_pos_iff_valof valof_zero(2))
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
        
    
  subsection \<open>Executable Proof of Rounding Result\<close>  
            
    
  definition "z_compat f (s::nat) \<equiv> is_zero f \<longrightarrow> sign f=0 \<longleftrightarrow> s=0"  
  
  lemma z_compat_simps[simp]:
    "z_compat (-0) s \<longleftrightarrow> s\<noteq>0"
    "z_compat (0) s \<longleftrightarrow> s=0"
    "\<not>is_zero f \<Longrightarrow> z_compat f s"
    by (auto simp: z_compat_def)
  
  
  subsubsection \<open>To Negative Infinity\<close>  
    
  definition check_zs_r_ninf :: "nat \<Rightarrow> real \<Rightarrow> ('e, 'f) float \<Rightarrow> bool"
  where "check_zs_r_ninf s r f \<equiv> if r < -largest TYPE(('e,'f) float) then f=minus_infinity
    else if largest TYPE(('e,'f) float) < r then f=topfloat
    else if r = largest TYPE(('e,'f) float) then f=topfloat
    else if f=topfloat \<or> \<not>is_finite f then False
    else valof f \<le> r \<and> r < valof (next_float' f) \<and> z_compat f s"

  lemma check_zs_r_ninf:
    fixes f :: "('e,'f) float"
    assumes LEN: "1 < LENGTH('e)"
    assumes "check_zs_r_ninf s r f"
    shows "zerosign s (round To_ninfinity r) = f"
  proof -
    let ?f = "closest valof (\<lambda>a. True) {a::('e,'f) float. is_finite a \<and> valof a \<le> r} r"
  
    
    have CLTF[simp]: "closest valof (\<lambda>a. True) {a. is_finite a \<and> valof a \<le> valof (topfloat::('e,'f) float)} (valof (topfloat::('e,'f) float)) = (topfloat::('e,'f) float)"
      apply (rule closest_precise_eqI)
      apply (auto simp: finite_topfloat)
      done

      
    have FF[simp]: "-valof (topfloat::('e,'f) float) \<le> r \<Longrightarrow> is_finite ?f"     
      by (smt (verit, best) assms(1) bottomfloat_eq_m_largest closest_eq_in_setD empty_subsetI finite_bottomfloat mem_Collect_eq nan_not_finite subset_eq valof_topfloat)
      
    have [simp]: "r < - largest TYPE(('e, 'f) IEEE.float) \<Longrightarrow> round To_ninfinity r = (-\<infinity>::('e, 'f) IEEE.float)"
      by simp
    
    have [simp]: "r > largest TYPE(('e, 'f) IEEE.float) \<Longrightarrow> round To_ninfinity r = (topfloat::('e, 'f) IEEE.float)"
      apply simp
      by (smt (verit, del_insts) largest_gtZ)

    have [simp]: "round To_ninfinity (largest TYPE(('e, 'f) IEEE.float)) = (topfloat::('e, 'f) IEEE.float)"
      apply (simp flip: valof_topfloat[OF LEN])
      by (metis assms(1) largest_gtZ' valof_topfloat)
      
          
    note ISZ = is_zero_iff_valof0[OF FF]    

    have NTF: "-valof (topfloat::('e,'f) float) \<le>r \<Longrightarrow> r<valof (topfloat::('e,'f) float) \<Longrightarrow> ?f \<noteq> topfloat"
      by (metis (no_types, lifting) Collect_empty_eq assms(1) bottomfloat_eq_m_largest closest_eq_in_setD finite_bottomfloat linorder_le_less_linear mem_Collect_eq order.asym valof_topfloat verit_la_disequality)
    
      
    thm bprec_round_ninf  
    
   
    note [simp del] = round.simps valof_zero
          
    show ?thesis
      using assms(2) unfolding check_zs_r_ninf_def
      apply (clarsimp split!: if_splits simp: zerosign_def)
    proof -
      assume BOUNDS: 
        "\<not> r < - largest TYPE(('e, 'f) IEEE.float)"
        "\<not> largest TYPE(('e, 'f) IEEE.float) < r" 
        "r \<noteq> largest TYPE(('e, 'f) IEEE.float)" 
        "f \<noteq> topfloat" 
      assume FIN: "is_finite f"  
      assume INTERV: "valof f \<le> r" "r < valof (next_float' f)"  
      
      note BP = bprec_round_ninf[of f r, OF LEN FIN \<open>f\<noteq>topfloat\<close>]
    
      let ?f="IEEE.round To_ninfinity r :: ('e,'f) float"
      
      have FINF: "is_finite ?f"
        using BOUNDS
        apply (simp add: round.simps)
        by (smt (verit, best) FF LEN valof_topfloat)
      
      
      {
        assume Z: "is_zero (?f)"
        assume COMP: "z_compat f 0"
        hence 1: "valof (next_float' f) = valof (next_float f)"
          by (auto simp: next_float'_def z_compat_def valof_zero)

        with BP INTERV have "valof (?f) = valof f"
          by simp  
          
        with Z COMP show "f=0"
          apply (auto dest!: val_zero)
          by (metis FIN is_zero_cases is_zero_iff_valof0 z_compat_simps(1))
                
      }
      
      {
        assume Z: "is_zero (?f)"
        assume COMP: "0 < s" "z_compat f s"
        hence "f\<noteq>0" by auto
              
        show "-0=f" proof (rule sym,rule ccontr)
          assume "f\<noteq>-0"
          with BP INTERV have "valof ?f = valof f" by (simp add: next_float'_def valof_zero split: if_splits)
          with Z \<open>f\<noteq>0\<close> \<open>f\<noteq>-0\<close> show False
            by (metis FIN val_zero valof_almost_injective valof_zero(1) zero_finite)
        qed    
      }

      {
        assume A: "\<not>is_zero ?f"
      
        show "IEEE.round To_ninfinity r = f"
        proof (cases "f=-0")
          case True
          then show ?thesis
            by (smt (verit, ccfv_threshold) BOUNDS(2) Collect_empty_eq INTERV(1) INTERV(2) LEN \<open>\<not> is_zero (IEEE.round To_ninfinity r)\<close> bprec_round_ninf closest_eq_in_setD is_zero_iff_valof0 mem_Collect_eq next_float'_def round.simps(4) valof_zero(1) valof_zero(2) zero_finite zero_neq_topfloat(1))
        next
          case False
          hence 1: "valof (next_float' f) = valof (next_float f)"
            by (simp add: valof_nextfloat')
          from BP[OF INTERV[unfolded 1]] have "valof ?f = valof f" .
          with A valof_almost_injective[OF FINF FIN this] show "?f=f" 
            by auto
        qed
      }      
    qed
  qed    

  subsubsection \<open>To Positive Infinity\<close>  
  
  definition check_zs_r_pinf :: "nat \<Rightarrow> real \<Rightarrow> ('e, 'f) float \<Rightarrow> bool"
  where "check_zs_r_pinf s r f \<equiv> if r < -largest TYPE(('e,'f) float) then f=bottomfloat
    else if largest TYPE(('e,'f) float) < r then f=plus_infinity
    else if r = - largest TYPE(('e,'f) float) then f=bottomfloat
    else if f=bottomfloat \<or> \<not>is_finite f then False
    else if f=0 then r=0 \<and> s=0
    else valof (prev_float f) < r \<and> r \<le> valof f \<and> z_compat f s"
        
    
        
  lemma check_zs_r_pinf:
    fixes f :: "('e,'f) float"
    assumes LEN[simp]: "1 < LENGTH('e)"
    assumes "check_zs_r_pinf s r f"
    shows "zerosign s (round To_pinfinity r) = f"
  proof -
    let ?f="IEEE.round To_pinfinity r :: ('e,'f) float"

    note [simp] = LEN[simplified]
    
    have [simp]: "r < - largest TYPE(('e, 'f) IEEE.float) \<Longrightarrow> ?f = bottomfloat"
      by simp
    
    have [simp]: "r > largest TYPE(('e, 'f) IEEE.float) \<Longrightarrow> ?f = plus_infinity"
      apply simp
      by (smt (verit, del_insts) largest_gtZ)
  
    have [simp]: "round To_pinfinity (-largest TYPE(('e, 'f) IEEE.float)) = (bottomfloat::('e, 'f) IEEE.float)"
      apply (auto simp flip: valof_topfloat[OF LEN])
      subgoal by (metis assms(1) largest_gtZ' valof_topfloat)
      by (smt (verit) Collect_cong LEN Orderings.order_eq_iff bottomfloat_eq_m_largest closest_precise_eqI finite_bottomfloat float_val_ge_bottomfloat is_zero_iff_valof0 largest_gtZ mem_Collect_eq valof_topfloat)
  
    note [simp del] = round.simps valof_zero

    
              
    show ?thesis
      using assms(2) unfolding check_zs_r_pinf_def
      apply (clarsimp split!: if_splits simp: zerosign_def)
    proof -
      assume INTERV: "valof (prev_float f) < r" "r \<le> valof f"
        and NBOT: "f\<noteq>-topfloat"
        and FIN[simp]: "is_finite f"
        and BOUNDS: "\<not> r < - largest TYPE(('e, 'f) IEEE.float)" "\<not> largest TYPE(('e, 'f) IEEE.float) < r"
        and NZ: "f\<noteq>0"
      note BP = bprec_round_pinf[of f r, OF LEN FIN NBOT INTERV]
    
      from BOUNDS have [simp]: "is_finite ?f" by (auto intro!: is_finite_roundI)
      
      {
        assume "is_zero ?f" "z_compat f 0"
        then show False using NZ by (auto simp: is_zero_iff_valof0 BP elim: valof_eqZ_cases)
      }
      {
        assume "is_zero ?f" "0 < s" "z_compat f s"
        then show "-0=f" using NZ by (auto simp: is_zero_iff_valof0 BP elim: valof_eqZ_cases)
      }

      {
        assume "\<not>is_zero ?f"
        thus "?f = f" by (simp add: BP nz_float_eq_valof_iff)
      }
    qed   
  qed         

  subsubsection \<open>To Zero\<close>  
  
  definition check_zs_r_tz :: "nat \<Rightarrow> real \<Rightarrow> ('e, 'f) float \<Rightarrow> bool"
  where "check_zs_r_tz s r f \<equiv> if r < -largest TYPE(('e,'f) float) then f=bottomfloat
    else if largest TYPE(('e,'f) float) < r then f=topfloat
    else if r = - largest TYPE(('e,'f) float) then f=bottomfloat
    else if r = largest TYPE(('e,'f) float) then f=topfloat
    else if f=bottomfloat \<or> f=topfloat \<or> \<not>is_finite f then False
    else if is_zero f then (s=0) = (f=0) \<and> valof (prev_float (-0::('e,'f) float)) < r \<and> r < valof (next_float (0::('e,'f) float))
    else if r<0 then valof (prev_float f) < r \<and> r \<le> valof f
    else valof f \<le> r \<and> r < valof (next_float f)"
  


              
  lemma not_disjE: assumes "\<not>(A\<or>B)" obtains "\<not>A" "\<not>B" using assms by blast
  lemma not_notE: assumes "\<not>\<not>A" obtains "A" using assms by blast
  
  
  lemma check_zs_r_tz:
    fixes f :: "('e,'f) float"
    assumes LEN[simp]: "1 < LENGTH('e)"
    assumes "check_zs_r_tz s r f"
    shows "zerosign s (round float_To_zero r) = f"
  proof -
    let ?f="IEEE.round float_To_zero r :: ('e,'f) float"

    note [simp] = LEN[simplified]
    
    have [simp]: "r < - largest TYPE(('e, 'f) IEEE.float) \<Longrightarrow> ?f = bottomfloat"
      by simp
    
    have [simp]: "r > largest TYPE(('e, 'f) IEEE.float) \<Longrightarrow> ?f = topfloat"
      apply simp
      by (smt (verit, del_insts) largest_gtZ)
  
    have [simp]: "round float_To_zero (-largest TYPE(('e, 'f) IEEE.float)) = (bottomfloat::('e, 'f) IEEE.float)"
      apply (auto simp flip: valof_topfloat[OF LEN])
      subgoal by (metis assms(1) largest_gtZ' valof_topfloat)
      by (smt (verit, ccfv_SIG) Collect_cong LEN Orderings.order_eq_iff bottomfloat_eq_m_largest closest_precise_eqI finite_bottomfloat float_val_ge_largest float_val_le_largest is_zero_cases largest_gtZ mem_Collect_eq valof_topfloat valof_zero(1) valof_zero(2))

    have [simp]: "round float_To_zero (largest TYPE(('e, 'f) IEEE.float)) = (topfloat::('e, 'f) IEEE.float)"
      apply (auto simp flip: valof_topfloat[OF LEN])
      subgoal by (metis assms(1) largest_gtZ' valof_topfloat)
      by (simp add: closest_precise_eqI finite_topfloat subset_eq)
        
    note [simp del] = round.simps

                  
    show ?thesis
      using assms(2) unfolding check_zs_r_tz_def
      apply (simp only: split: if_splits)
      apply (all \<open>(elim conjE not_disjE not_notE)?;(simp add: zerosign_def; fail)?\<close>)
    proof -
      assume BOUNDS: "\<not> r < - largest TYPE(('e, 'f) IEEE.float)" "\<not> largest TYPE(('e, 'f) IEEE.float) < r"
      from BOUNDS have FINF[simp]: "is_finite ?f" by (auto intro!: is_finite_roundI)

      {
        assume "is_zero f" "(s = 0) = (f = 0)"
        assume INTERV: "valof (prev_float (- 0)::('e, 'f) IEEE.float) < r" "r < valof (next_float 0::('e, 'f) IEEE.float)"
        
        have "valof ?f = 0"
          by (metis INTERV LEN bprec_round_zero_neg bprec_round_zero_pos is_finite_uminus mtopfloat_neq_Z(4) nle_le valof_zero(1) valof_zero(2) zero_finite)
        thus "zerosign s ?f = f" 
          by (metis FINF \<open>(s = 0) = (f = 0)\<close> \<open>is_zero f\<close> is_zero_cases is_zero_iff_valof0 zerosign_def)
        
      }    

      { 
        assume "r < 0" and INTERV: "valof (prev_float f) < r" "r \<le> valof f" and FIN[simp]: "is_finite f"
        and NBOT: \<open>f\<noteq>-topfloat\<close>
        and NZ: "\<not> is_zero f"
        
        from \<open>r<0\<close> have "r\<le>0" by auto
        
        from bprec_round_zero_neg[OF LEN FIN NBOT \<open>r\<le>0\<close> INTERV] have [simp]: "valof ?f = valof f" by simp
        
        note A = nz_float_eq_valof_iff[of _ f, simplified]
        
        then show "zerosign s ?f = f"
          using NZ
          apply (auto simp add: zerosign_def A)
          apply (auto simp: is_zero_iff_valof0 elim!: valof_eqZ_cases)
          done
          
      }
       
      { 
        assume "\<not>r < 0" and INTERV: "valof f \<le> r" "r < valof (next_float f)" and FIN[simp]: "is_finite f"
        and NBOT: \<open>f\<noteq>topfloat\<close>
        and NZ: "\<not> is_zero f"
        
        from \<open>\<not>r<0\<close> have "r\<ge>0" by auto
        
        from bprec_round_zero_pos[OF LEN FIN NBOT \<open>r\<ge>0\<close> INTERV] have [simp]: "valof ?f = valof f" by simp
        
        note A = nz_float_eq_valof_iff[of _ f, simplified]
        
        then show "zerosign s ?f = f"
          using NZ
          apply (auto simp add: zerosign_def A)
          apply (auto simp: is_zero_iff_valof0 elim!: valof_eqZ_cases)
          done
          
      }
    
    qed   
  qed         
  

  subsubsection \<open>To Nearest\<close>  

  definition "is_close r (f::('e,'f) float) \<equiv> 
    is_finite f \<and> (
    if is_zero f then
      valof (prev_float (-0)::('e,'f) float)<r \<and> r<valof (next_float 0::('e,'f) float)
    else
      valof (prev_float f)<r \<and> r<(valof (next_float f)))"  
    
  find_theorems next_float'    
      
  definition "prev_float' f \<equiv> if f=0 then prev_float (-0) else prev_float f"
  definition "next_float'' f \<equiv> if f=-0 then next_float (0) else next_float f"
  
  definition "lbound r f \<equiv> if r < valof f then prev_float' f else zerosign 0 f"  
  definition "rbound r f \<equiv> if r \<ge> valof f then next_float'' f else zerosign (if r<0 then 1 else 0) f"  
        
  locale non_extreme_bounded =
    fixes f :: "('e,'f) float"
      and r :: real
      
    (*assumes R_BOUNDS: "-largest TYPE(('e,'f) float) < r" "r < largest TYPE(('e,'f) float)"  *)
    assumes LEN: "1 < LENGTH('e)"
    assumes FBOUNDS[simp]: "f\<noteq>bottomfloat" "f\<noteq>topfloat"
    
    assumes CLOSE: "is_close r f"
    
  begin  

    lemma FIN[simp, intro!]: "is_finite f" using CLOSE by (auto simp: is_close_def) 

    lemma R_BOUNDS: "-largest TYPE(('e,'f) float) < r" "r < largest TYPE(('e,'f) float)"    
      apply (smt (verit, ccfv_SIG) CLOSE FBOUNDS(1) LEN float_val_ge_largest is_close_def is_finite_uminus mtopfloat_neq_Z(2) prev_float_finiteI zero_finite)
      by (smt (verit, ccfv_SIG) CLOSE FBOUNDS(2) LEN finite_topfloat is_close_def less_neq_topfloat next_float_tight topfloat_not_zero valof_nonzero_injective valof_topfloat zero_finite zero_neq_topfloat(1))
      
    lemma bound_bounds:
      "valof (lbound r f) \<le> r" "r<valof (rbound r f)"
      using CLOSE 
      by (auto 
        simp: lbound_def rbound_def is_close_def 
        simp: prev_float'_def next_float''_def zerosign_def
        elim!: is_zero_cases
        split: if_splits)
  
    lemma rb_is_next_lb: "rbound r f = next_float (lbound r f)"
      using CLOSE FBOUNDS
      by (auto 
        simp: lbound_def rbound_def is_close_def 
        simp: prev_float'_def next_float''_def zerosign_def
        elim!: is_zero_cases
        split: if_splits)
        
    lemma rbound_finite[simp, intro!]: "is_finite (rbound r f)" 
      by (auto simp: rbound_def next_float''_def)
        
    lemma lbound_finite[simp, intro!]: "is_finite (lbound r f)" 
      by (auto simp: lbound_def prev_float'_def)
        
    lemma lbound_ntop[simp]: "lbound r f \<noteq> topfloat"
      by (simp add: lbound_def prev_float'_def prev_float_ne_top zerosign_def)  
      
    lemma rbound_nbot[simp]: "rbound r f \<noteq> -topfloat"
      by (simp add: next_float_ne_bot rb_is_next_lb)
      
  end      

  
  definition "check_zs_r_tn_aux s r f \<equiv> let
      f\<^sub>1 = lbound r f;
      f\<^sub>2 = rbound r f;
      \<delta>\<^sub>1 = \<bar>r - valof f\<^sub>1\<bar>;
      \<delta>\<^sub>2 = \<bar>r - valof f\<^sub>2\<bar>
    in
      if \<delta>\<^sub>1<\<delta>\<^sub>2 then f = zerosign s f\<^sub>1
      else if \<delta>\<^sub>2<\<delta>\<^sub>1 then f = zerosign s f\<^sub>2
      else if even (fraction f\<^sub>1) then f = zerosign s f\<^sub>1
      else f = zerosign s f\<^sub>2"
          
  definition check_zs_r_tn :: "nat \<Rightarrow> real \<Rightarrow> ('e, 'f) float \<Rightarrow> bool"
  where "check_zs_r_tn s r f \<equiv> if r \<le> -threshold TYPE(('e,'f) float) then f=minus_infinity
    else if threshold TYPE(('e,'f) float) \<le> r then f=plus_infinity
    else if f=topfloat then \<bar>r - valof f\<bar> < \<bar>r - valof (prev_float f)\<bar>
    else if f=bottomfloat then \<bar>r - valof f\<bar> < \<bar>r - valof (next_float f)\<bar>
    else if \<not>is_close r f \<or> f=topfloat \<or> f=bottomfloat then False
    else check_zs_r_tn_aux s r f
    "
  
  lemma to_nearest_topfloat_case:
    fixes t :: "('e,'f) float"
    defines "t \<equiv> topfloat"
    assumes LEN[simp]: "1 < LENGTH('e)"
    assumes "\<bar>r - valof t\<bar> < \<bar>r - valof (prev_float t)\<bar>"
    assumes "r<threshold TYPE(('e,'f) float)"
    shows "round To_nearest r = t"
    using assms(2,3,4)
    unfolding t_def
    apply auto    
    subgoal 
      by (smt (verit) LEN bottomfloat_eq_m_largest finite_topfloat float_sel_simps(13) float_val_gt_threshold largest_gtZ less_neq_topfloat prev_float_finiteI sign_pos_iff_valof)
    subgoal 
      apply (rule closest_unique_predI)
      apply blast
      apply (auto simp: is_closest_def)
      by (smt (verit, best) LEN bottomfloat_eq_m_largest finite_topfloat largest_gtZ less_neq_topfloat prev_float_finiteI prev_float_tight topfloat_not_zero valof_nonzero_injective valof_topfloat)
    done
     
  lemma to_nearest_bottomfloat_case:
    fixes t :: "('e,'f) float"
    defines "t \<equiv> -topfloat"
    assumes LEN[simp]: "1 < LENGTH('e)"
    assumes "\<bar>r - valof t\<bar> < \<bar>r - valof (next_float t)\<bar>"
    assumes "r>-threshold TYPE(('e,'f) float)"
    shows "round To_nearest r = t"
    using assms(2,3,4)
    unfolding t_def
    apply auto    
    subgoal 
      by (smt (verit, ccfv_threshold) LEN finite_bottomfloat float_neq_neg(1) float_val_ge_bottomfloat float_val_lt_threshold next_float_finiteI)
    subgoal 
      apply (rule closest_unique_predI)
      apply blast
      apply (auto simp: is_closest_def)
      by (smt (verit, ccfv_SIG) LEN finite_bottomfloat float_neq_neg(1) float_val_ge_bottomfloat mtopfloat_neq_Z(2) mtopfloat_neq_Z(3) next_float_finiteI next_float_tight valof_almost_injective)
    done

    
        
    
  lemma zerosign_eqI: "\<lbrakk>is_finite f; is_finite f'; valof f = valof f'\<rbrakk> \<Longrightarrow> zerosign s f = zerosign s f'"  
    by (metis valof_nonzero_injective zerosign_def)
  
      
  lemma check_zs_r_tn:
    fixes f :: "('e,'f) float"
    assumes LEN[simp]: "1 < LENGTH('e)"
    assumes "check_zs_r_tn s r f"
    shows "zerosign s (round To_nearest r) = f"
  proof -
    let ?f="IEEE.round To_nearest r :: ('e,'f) float"

    let ?c="closest valof (\<lambda>a:: ('e,'f) float. even (fraction a)) (Collect is_finite) r"
    
    note [simp] = LEN[simplified]
  
    have [simp]: "r \<le> - threshold TYPE(('e, 'f) float) \<Longrightarrow> ?f=-\<infinity>"
      by simp
        
    have [simp]: "r \<ge> threshold TYPE(('e, 'f) float) \<Longrightarrow> ?f=\<infinity>"
      by (auto 0 2 dest: order_trans)
    
    
    have [simp]: "r\<le>-largest TYPE(('e, 'f) float) \<Longrightarrow> ?c=bottomfloat"
      by (smt (verit, best) abs_if assms(1) bottomfloat_eq_m_largest closest_is_closest finite_bottomfloat float_val_ge_bottomfloat is_closest_def is_finite_nonempty largest_gtZ mem_Collect_eq next_float_increases next_float_mzero next_prev_float_id prev_float_finiteI prev_float_ne_top valof_zero(1))
      
    have [simp]: "r\<ge>largest TYPE(('e, 'f) float) \<Longrightarrow> ?c=topfloat"
      by (smt (verit) LEN abs_if closest_is_closest finite_topfloat is_closest_def is_finite_nonempty less_neq_topfloat mem_Collect_eq topfloat_not_zero valof_nonzero_injective valof_topfloat)
      
    note [simp] = to_nearest_bottomfloat_case to_nearest_topfloat_case  
      
    note [simp del] = round.simps 
  
    show ?thesis
      using assms(2) unfolding check_zs_r_tn_def
      apply (clarsimp split!: if_splits)
    proof goal_cases
      case 1

      have [simp]: "is_finite ?f" 
        using "1"(1) "1"(2) is_finite_round_nearestI by force
            
      from 1 interpret non_extreme_bounded f r
        apply unfold_locales
        apply simp_all
        done
  
      define f\<^sub>1 where "f\<^sub>1 = lbound r f"  
      define f\<^sub>2 where "f\<^sub>2 = rbound r f"  
        
      have [simp]: "rbound r f = next_float f\<^sub>1"
        unfolding f\<^sub>1_def using rb_is_next_lb by auto
        
      have [simp]: "f\<^sub>1\<noteq>topfloat"  
        unfolding f\<^sub>1_def by simp

      have BOUND: "valof f\<^sub>1 \<le> r" "r \<le> valof (next_float f\<^sub>1)"  
        subgoal by (simp add: bound_bounds(1) f\<^sub>1_def)
        subgoal using bound_bounds(2) by auto
        done
        
      have [simp]: "odd (fraction f\<^sub>1) = even (fraction (next_float f\<^sub>1))"
        using bound_bounds(1) bound_bounds(2) f\<^sub>1_def f\<^sub>2_def nextfloat_even_odd nextfloat_odd_even by fastforce  
        
      have [simp, intro!]: "is_finite f\<^sub>1" unfolding f\<^sub>1_def by blast  
      note [simp] = f\<^sub>1_def[symmetric]
              
      from \<open>check_zs_r_tn_aux s r f\<close> show ?case
        unfolding Let_def check_zs_r_tn_aux_def
        by (auto 
          split: if_splits 
          intro!: zerosign_eqI
          intro: bprec_round_nearest_down bprec_round_nearest_up 
          intro: bprec_round_nearest_down_even bprec_round_nearest_up_even 
          simp: BOUND)
    qed 
  qed      

  subsubsection \<open>Arbitrary Rounding Mode\<close>  
  
  fun check_zs_r where
    "check_zs_r To_ninfinity s r f = check_zs_r_ninf s r f"
  | "check_zs_r To_pinfinity s r f = check_zs_r_pinf s r f"
  | "check_zs_r float_To_zero s r f = check_zs_r_tz s r f"
  | "check_zs_r To_nearest s r f = check_zs_r_tn s r f"
  
  lemma check_zs_r_alt: "check_zs_r m s r f = (case m of 
    To_ninfinity \<Rightarrow> check_zs_r_ninf s r f
  | To_pinfinity \<Rightarrow> check_zs_r_pinf s r f
  | float_To_zero \<Rightarrow> check_zs_r_tz s r f  
  | To_nearest \<Rightarrow> check_zs_r_tn s r f
  )"
    apply (cases m) by (auto simp: fun_eq_iff)
  
    
  lemma check_zs_r:
    fixes f :: "('e,'f) float"
    assumes LEN[simp]: "1 < LENGTH('e)"
    assumes "check_zs_r m s r f"
    shows "zerosign s (round m r) = f"
    using assms
    apply (cases m; 
      simp 
        del: round.simps 
        add: check_zs_r_ninf check_zs_r_pinf check_zs_r_tn check_zs_r_tz)
    done
  
    
    
    
  instantiation IEEE.float :: (len,len) equal
  begin
  
    lift_definition equal_float :: "('a,'b) float \<Rightarrow> ('a,'b) float \<Rightarrow> bool" is "(=)" .
  
    instance
      apply standard
      apply transfer
      by auto
  end  
    
  export_code check_zs_r checking SML  
    
    
  subsection \<open>Executable Result Checks for Operations\<close>

  (* Setup for sqrt *)
  lemma le_sqrt_code[code_unfold]: "a \<le> sqrt b \<longleftrightarrow> (if b<0 then a\<le>0 \<and> -a\<^sup>2\<le>b else a\<le>0 \<or> a\<^sup>2\<le>b)"
    by (smt (verit) real_sqrt_abs real_sqrt_le_iff real_sqrt_minus)
    
  lemma lt_sqrt_code[code_unfold]: "a < sqrt b \<longleftrightarrow> (if b<0 then a\<le>0 \<and> -a\<^sup>2<b else a<0 \<or> a\<^sup>2<b)"
    by (smt (verit, ccfv_SIG) real_sqrt_abs real_sqrt_less_mono real_sqrt_minus)
    
  lemma sqrt_le_code[code_unfold]: "sqrt a \<le> b \<longleftrightarrow> (if a<0 then 0\<le>b \<or> a\<le>-b\<^sup>2 else 0\<le>b \<and> a\<le>b\<^sup>2)"  
    by (smt (verit, best) real_sqrt_abs real_sqrt_minus sqrt_ge_absD sqrt_le_D)
    
  lemma sqrt_lt_code[code_unfold]: "sqrt a < b \<longleftrightarrow> (if a<0 then 0<b \<or> a < -b\<^sup>2 else 0\<le>b \<and> a<b\<^sup>2)"  
    by (smt (verit, best) real_sqrt_abs real_sqrt_minus sqrt_ge_absD sqrt_le_D)
    
  
  
  text \<open>Handling NaN\<close>
  
  lift_definition nan01 :: "('e,'f) float" is "(0,-1,1)" .
  
  lemma sign_nan01[simp]: "sign nan01 = 0" by transfer simp
  lemma exponent_nan01[simp]: "exponent (nan01::('e,'f) float) = emax TYPE (('e,'f) float)"
    apply transfer
    by (auto simp: emax_def)
    
  lemma fraction_nan01[simp]: "fraction (nan01::('e,'f) float) = 1"
    apply transfer
    by (auto simp: emax_def)

  lemma is_nan01[simp]: "is_nan nan01" by (auto simp: is_nan_def) 

  definition eq_nan (infix "=\<^sub>N\<^sub>a\<^sub>N" 50) where "eq_nan a b \<equiv> if a=b then True else is_nan a \<and> is_nan b"
  
  thm the_nan_is_nan
  
  lemma eq_nan_refl[simp]: "a=\<^sub>N\<^sub>a\<^sub>Na"
    unfolding eq_nan_def 
    by auto

  lemma eq_nan_sym[sym]: "a=\<^sub>N\<^sub>a\<^sub>Nb \<Longrightarrow> b=\<^sub>N\<^sub>a\<^sub>Na"
    unfolding eq_nan_def 
    by auto
    
  lemma eq_nan_trans[trans]: "a=\<^sub>N\<^sub>a\<^sub>Nb \<Longrightarrow> b =\<^sub>N\<^sub>a\<^sub>N c \<Longrightarrow> a =\<^sub>N\<^sub>a\<^sub>N c"
    unfolding eq_nan_def 
    by (auto split: if_splits)

  lemma eq_nan_eqI: "a = b \<Longrightarrow> a =\<^sub>N\<^sub>a\<^sub>N b" by simp  
    
          
  lemma eq_nan_simps[simp]: 
    "\<not>is_nan a \<Longrightarrow> a =\<^sub>N\<^sub>a\<^sub>N b \<longleftrightarrow> a=b"
    "\<not>is_nan b \<Longrightarrow> a =\<^sub>N\<^sub>a\<^sub>N b \<longleftrightarrow> a=b"
    "is_nan a \<Longrightarrow> a =\<^sub>N\<^sub>a\<^sub>N b \<longleftrightarrow> is_nan b"
    "is_nan b \<Longrightarrow> a =\<^sub>N\<^sub>a\<^sub>N b \<longleftrightarrow> is_nan a"
    unfolding eq_nan_def 
    by auto
        
  lemma check_decomp_aux: "if a then cb else cc \<Longrightarrow> (cb\<Longrightarrow>b=\<^sub>N\<^sub>a\<^sub>Nres) \<Longrightarrow> (cc\<Longrightarrow>c=\<^sub>N\<^sub>a\<^sub>Nres) \<Longrightarrow> 
    (if a then b else c) =\<^sub>N\<^sub>a\<^sub>N res" by simp     
  
  definition check_fadd :: "roundmode \<Rightarrow> ('e ,'f) float \<Rightarrow> ('e ,'f) float \<Rightarrow> ('e ,'f) float \<Rightarrow> bool"
    where "check_fadd m a b res =
      (if is_nan a \<or> is_nan b \<or> (is_infinity a \<and> is_infinity b \<and> sign a \<noteq> sign b)
       then is_nan res
       else if (is_infinity a) then res=a
       else if (is_infinity b) then res=b
       else
         check_zs_r m
           (if is_zero a \<and> is_zero b \<and> sign a = sign b then sign a
            else if m = To_ninfinity then 1 else 0)
           (valof a + valof b) res)"
  
  lemma check_fadd:
    fixes a b c :: "('e,'f) float"
    assumes LEN[simp]: "1 < LENGTH('e)"
    shows "check_fadd m a b c \<Longrightarrow> fadd m a b =\<^sub>N\<^sub>a\<^sub>N c"
    unfolding fadd_def check_fadd_def
    apply (elim check_decomp_aux check_zs_r[OF LEN, THEN eq_nan_eqI])
    by simp_all
  
  definition check_fsub :: "roundmode \<Rightarrow> ('e ,'f) float \<Rightarrow> ('e ,'f) float \<Rightarrow> ('e ,'f) float \<Rightarrow> bool"
    where "check_fsub m a b res =
      (if is_nan a \<or> is_nan b \<or> (is_infinity a \<and> is_infinity b \<and> sign a = sign b)
       then is_nan res
       else if is_infinity a then res=a
       else if is_infinity b then res = - b
       else
        check_zs_r m
          (if is_zero a \<and> is_zero b \<and> sign a \<noteq> sign b then sign a
           else if m = To_ninfinity then 1 else 0)
          (valof a - valof b) res)"
    
  lemma check_fsub:
    fixes a b c :: "('e,'f) float"
    assumes LEN[simp]: "1 < LENGTH('e)"
    shows "check_fsub m a b c \<Longrightarrow> fsub m a b =\<^sub>N\<^sub>a\<^sub>N c"
    unfolding fsub_def check_fsub_def
    apply (elim check_decomp_aux check_zs_r[OF LEN, THEN eq_nan_eqI])
    by simp_all
    
  definition check_fmul :: "roundmode \<Rightarrow> ('e ,'f) float \<Rightarrow> ('e ,'f) float \<Rightarrow> ('e ,'f) float \<Rightarrow> bool"
    where "check_fmul m a b res =
      (if is_nan a \<or> is_nan b \<or> (is_zero a \<and> is_infinity b) \<or> (is_infinity a \<and> is_zero b)
       then is_nan res
       else if is_infinity a \<or> is_infinity b
       then (if sign a = sign b then res=plus_infinity else res=minus_infinity)
       else check_zs_r m (if sign a = sign b then 0 else 1 ) (valof a * valof b) res)"
       
  lemma check_fmul:
    fixes a b c :: "('e,'f) float"
    assumes LEN[simp]: "1 < LENGTH('e)"
    shows "check_fmul m a b c \<Longrightarrow> fmul m a b =\<^sub>N\<^sub>a\<^sub>N c"
    unfolding fmul_def check_fmul_def
    apply (elim check_decomp_aux check_zs_r[OF LEN, THEN eq_nan_eqI])
    by simp_all
  
  definition check_fdiv :: "roundmode \<Rightarrow> ('e ,'f) float \<Rightarrow> ('e ,'f) float \<Rightarrow> ('e ,'f) float \<Rightarrow> bool"
    where "check_fdiv m a b res =
      (if is_nan a \<or> is_nan b \<or> (is_zero a \<and> is_zero b) \<or> (is_infinity a \<and> is_infinity b)
       then is_nan res
       else if is_infinity a \<or> is_zero b
       then (if sign a = sign b then res=plus_infinity else res=minus_infinity)
       else if is_infinity b
       then (if sign a = sign b then res=0 else res=- 0)
       else check_zs_r m (if sign a = sign b then 0 else 1) (valof a / valof b) res)"
    
  lemma check_fdiv:
    fixes a b c :: "('e,'f) float"
    assumes LEN[simp]: "1 < LENGTH('e)"
    shows "check_fdiv m a b c \<Longrightarrow> fdiv m a b =\<^sub>N\<^sub>a\<^sub>N c"
    unfolding fdiv_def check_fdiv_def
    apply (elim check_decomp_aux check_zs_r[OF LEN, THEN eq_nan_eqI])
    by simp_all
    
    
  (* fmul-add uses yet another concept to handle zero sign. We convert here *)  
  lemma float_round_alt: "float_round m s r = zerosign (if s then 1 else 0) (round m r)"
    unfolding float_round_def zerosign_def
    by (simp)  
    
    
  definition "check_fr m s r f \<equiv> check_zs_r m (if s then 1 else 0) r f"  
  
  lemma check_fr:
    fixes f :: "('e,'f) float"
    assumes LEN[simp]: "1 < LENGTH('e)"
    assumes "check_fr m s r f"
    shows "float_round m s r = f"
    using assms
    unfolding check_fr_def float_round_alt
    by (rule check_zs_r)
    
  
  (* TODO: This semantics is wrong *)  
  definition check_fmul_add :: "roundmode \<Rightarrow> ('t ,'w) float \<Rightarrow> ('t ,'w) float \<Rightarrow> ('t ,'w) float \<Rightarrow> ('t ,'w) float \<Rightarrow> bool"
    where "check_fmul_add mode x y z res =
      (let signP = if sign x = sign y then 0 else 1 in
      let infP = is_infinity x  \<or> is_infinity y
      in
      if is_nan x \<or> is_nan y \<or> is_nan z then is_nan res
      else if is_infinity x \<and> is_zero y \<or>
             is_zero x \<and> is_infinity y \<or>
             is_infinity z \<and> infP \<and> signP \<noteq> sign z then
        is_nan res
      else if is_infinity z \<and> (sign z = 0) \<or> infP \<and> (signP = 0)
        then res=plus_infinity
      else if is_infinity z \<and> (sign z = 1) \<or> infP \<and> (signP = 1)
        then res=minus_infinity
      else let 
        r1 = valof x * valof y;
        r2 = valof z;
        r = r1+r2
      in 
        if r=0 then ( \<comment> \<open>Exact Zero Case. Same sign rules as for add apply. \<close>
          if r1=0 \<and> r2=0 \<and> signP=sign z then res = zerosign signP 0
          else if mode = To_ninfinity then res = -0
          else res = 0
        ) else ( \<comment> \<open>Not exactly zero: Rounding has sign of exact value, even if rounded val is zero\<close>
          check_zs_r mode (if r<0 then 1 else 0) r res
        ))
      "
      
    
  lemma check_fmul_add:
    fixes a b c d :: "('e,'f) float"
    assumes LEN[simp]: "1 < LENGTH('e)"
    shows "check_fmul_add m a b c d \<Longrightarrow> fmul_add m a b c =\<^sub>N\<^sub>a\<^sub>N d"
    unfolding fmul_add_def check_fmul_add_def Let_def
    apply (elim check_decomp_aux check_zs_r[OF LEN, THEN eq_nan_eqI])
    by simp_all


    
  lemma abs_le_abs_conv: "\<bar>a\<bar> \<le> \<bar>b\<bar> \<longleftrightarrow> (
    if a<0 \<and> b<0 then -a\<le>-b
    else if a<0 then -a\<le>b
    else if b<0 then a\<le>-b
    else a\<le>b
  )" for a b :: real by simp

  lemma le_conv_abs: "a\<le>b \<longleftrightarrow> (
    if a<0 \<and> b<0 then \<bar>b\<bar> \<le> \<bar>a\<bar>
    else if a<0 then True
    else if b<0 then False
    else \<bar>a\<bar> \<le> \<bar>b\<bar>
  )" for a b :: real
    by (auto)
  
    
    
  lemma nz_nlt_conv: "a\<noteq>0 \<Longrightarrow> \<not>(a<0) \<longleftrightarrow> a>0" for a :: real by auto
      
  lemma order_sqrt:
    fixes x y z r a
    defines "SS \<equiv> sqrt a"
    shows
    "x + SS = SS + x"
    "x + (SS + y) = SS + (x + y)"
    
    "x+y+z = x+(y+z)"
    "x+y-z = x+(y-z)"
    "x-y+z = x-(y-z)"
    "x-y-z = x-(y+z)"
    
    (*"x+(y+z) = x+y+z"
    "x+(y-z) = x+y-z"
    "x-(y+z) = x-y-z"
    "x-(y-z) = x-y+z"
    *)
    
    "SS + x \<le> y \<longleftrightarrow> SS \<le> y-x"
    "x \<le> SS + y \<longleftrightarrow> x-y \<le> SS"
    
    unfolding SS_def
    apply (auto simp: field_split_simps)
    done
  
  
  lemma shift_cmp_right: 
    "a+b \<le> c \<longleftrightarrow> b \<le> c-a" 
    "a * sqrt b \<le> c \<longleftrightarrow> (if a=0 then 0\<le>c else if a<0 then c/a \<le> sqrt b else sqrt b \<le> c/a)"
    for a b c :: real 
    by (auto simp: field_split_simps)
    
  lemma shift_cmp_left: 
    "a \<le> b + c \<longleftrightarrow> a-b \<le> c" 
    "a \<le> b * sqrt c \<longleftrightarrow> (if b=0 then a\<le>0 else if b>0 then a/b \<le> sqrt c else sqrt c \<le> a/b)"
    for a b c :: real 
    by (auto simp: field_split_simps)
    
  thm linorder_cases[where x=0]  
    
  lemma sqrt_sgn[simp]: "sqrt (sgn r) = sgn r"
    by (auto simp: sgn_real_def field_simps real_sqrt_minus)
  
  lemma mult_sqrt: 
    "r*sqrt a = sqrt (sgn r * r\<^sup>2*a)"
    "sqrt a*r = sqrt (sgn r * r\<^sup>2*a)"
    by (auto simp: field_simps real_sqrt_mult sgn_real_def real_sqrt_minus)
  
  lemma div_sqrt: 
    "r/sqrt a = sqrt (sgn r * r\<^sup>2/a)"
    "sqrt a/r = sqrt (sgn r * a / r\<^sup>2)"
    by (auto simp: field_simps real_sqrt_mult real_sqrt_divide sgn_real_def real_sqrt_minus)

    
  definition "sqrt_le_sqrt_plus_r a b r \<equiv> (
    if r = 0 then a \<le> b
    else if a = 0 then - r \<le> sqrt b
    else if b = 0 then sqrt a \<le> r
    else if a < 0 \<and> r < 0 \<and> b < 0 then a + r\<^sup>2 \<le> b \<and> - (b - (a + r\<^sup>2))\<^sup>2 \<le> b * (4 * r\<^sup>2)
    else if a < 0 \<and> b < 0 then - r\<^sup>2 \<le> b \<or> a + r\<^sup>2 \<le> b \<or> b * (4 * r\<^sup>2) \<le> - (b - (a + r\<^sup>2))\<^sup>2
    else if r < 0 \<and> b < 0 then False
    else if b < 0 then - r\<^sup>2 \<le> b \<and> a + b \<le> r\<^sup>2 \<and> - (a + b - r\<^sup>2)\<^sup>2 \<le> b * (4 * r\<^sup>2)
    else if a < 0 \<and> r < 0 then r\<^sup>2 \<le> b \<or> b + r\<^sup>2 \<le> - a \<or> (- a - (b + r\<^sup>2))\<^sup>2 \<le> b * (4 * r\<^sup>2)
    else if a < 0 then True
    else if r < 0 then r\<^sup>2 \<le> b \<and> a \<le> b + r\<^sup>2 \<and> b * (4 * r\<^sup>2) \<le> (a - (b + r\<^sup>2))\<^sup>2
    else a \<le> b + r\<^sup>2 \<or> (a - (b + r\<^sup>2))\<^sup>2 \<le> b * (4 * r\<^sup>2))"  
   
        
  lemma sqrt_le_sqrt_plus_r:
    shows "sqrt a \<le> sqrt b + r \<longleftrightarrow> sqrt_le_sqrt_plus_r a b r"
  proof -

    { 
      fix xb
      assume A: "r<0"
      have "a + (r * r + r * (sqrt b * 2)) \<le> xb \<longleftrightarrow> sqrt b \<ge> (-a + xb - r\<^sup>2)/(2*r)"
        using A
        by (auto simp: field_simps power2_eq_square)
    } note 1=this

    { 
      fix xb
      assume A: "0<r"
      have "a + (r * r + r * (sqrt b * 2)) \<le> xb \<longleftrightarrow> sqrt b \<le> (-a +xb - r\<^sup>2)/(2*r)"
        using A
        by (auto simp: field_simps power2_eq_square)
    } note 2=this
    
    have C1: "a \<le> b + x \<longleftrightarrow> a-b \<le> x" for x by auto
    
    {
      fix xb
      assume A: "r<0"
      have "xb \<le> r * r + r * (sqrt b * 2) \<longleftrightarrow> sqrt b \<le> (xb-r\<^sup>2) / (2*r)"
        using A
        by (auto simp: field_simps power2_eq_square)
    
    } note 3=this
    
    {
      fix xb
      assume A: "0<r"
      have "xb \<le> r * r + r * (sqrt b * 2) \<longleftrightarrow> (xb-r\<^sup>2) / (2*r) \<le> sqrt b"
        using A
        by (auto simp: field_simps power2_eq_square)
    
    } note 4=this
        
          
  
    show ?thesis
      apply (cases "r=0"; cases "r<0"; cases "a=0"; cases "a<0"; cases "b=0"; cases "b<0"; simp add: nz_nlt_conv field_split_simps real_0_le_add_iff)
      apply (simp_all add: sqrt_le_sqrt_plus_r_def)
      unfolding sqrt_le_code
      apply (simp_all add: field_simps power2_eq_square real_0_le_add_iff)
      unfolding 1 2 C1 3 4
      unfolding le_sqrt_code sqrt_le_code
      by (simp_all add: field_split_simps power2_eq_square)
  qed
    
  definition "sqrt_diff_cmp_le a r b s \<equiv> sqrt_le_sqrt_plus_r (sgn s * s\<^sup>2 * (4 * b)) (sgn r * r\<^sup>2 * (4 * a)) (- (\<bar>a\<bar> + (r * r - (\<bar>b\<bar> + s * s))))"

  export_code sqrt_diff_cmp_le in SML
  
  lemma sqrt_diff_cmp_le:
    shows "\<bar>sqrt a - r\<bar> \<le> \<bar>sqrt b - s\<bar> \<longleftrightarrow> sqrt_diff_cmp_le a r b s"
  proof -  
  
    note CC = linorder_cases[where x=0]
  
    show ?thesis
      apply (simp add: abs_le_square_iff power2_eq_square field_simps)
      apply (simp_all add: order_sqrt mult_sqrt)
      apply (simp flip: sqrt_le_sqrt_plus_r add: sqrt_diff_cmp_le_def)
      apply (simp add: field_split_simps power2_eq_square)
      done
      
  qed        
  
  definition "sqrt_lt_sqrt_plus_r a b r \<equiv> (
    if r = 0 then a < b
    else if a = 0 then - r < sqrt b
    else if b = 0 then sqrt a < r
    else if a < 0 \<and> r < 0 \<and> b < 0 then (a + r\<^sup>2 \<le> b \<and> - (b - (a + r\<^sup>2))\<^sup>2 < b * (4 * r\<^sup>2))
    else if a < 0 \<and> b < 0 then (- r\<^sup>2 < b \<or> a + r\<^sup>2 < b \<or> b * (4 * r\<^sup>2) < - (b - (a + r\<^sup>2))\<^sup>2)
    else if r < 0 \<and> b < 0 then False
    else if b < 0 then (- r\<^sup>2 \<le> b \<and> a + b \<le> r\<^sup>2 \<and> - (a + b - r\<^sup>2)\<^sup>2 < b * (4 * r\<^sup>2))
    else if a < 0 \<and> r < 0 then (r\<^sup>2 < b \<or> b + r\<^sup>2 < - a \<or> (- a - (b + r\<^sup>2))\<^sup>2 < b * (4 * r\<^sup>2))
    else if a < 0 then True
    else if r < 0 then (r\<^sup>2 \<le> b \<and> a \<le> b + r\<^sup>2 \<and> b * (4 * r\<^sup>2) < (a - (b + r\<^sup>2))\<^sup>2)
    else (a < b + r\<^sup>2 \<or> (a - (b + r\<^sup>2))\<^sup>2 < b * (4 * r\<^sup>2)))"
   
  lemma sqrt_lt_sqrt_plus_r:
    shows "sqrt a < sqrt b + r \<longleftrightarrow> sqrt_lt_sqrt_plus_r a b r"
  proof -

    { 
      fix xb
      assume A: "r<0"
      have "a + (r * r + r * (sqrt b * 2)) < xb \<longleftrightarrow> sqrt b > (-a + xb - r\<^sup>2)/(2*r)"
        using A
        by (auto simp: field_simps power2_eq_square)
    } note 1=this

    { 
      fix xb
      assume A: "0<r"
      have "a + (r * r + r * (sqrt b * 2)) < xb \<longleftrightarrow> sqrt b < (-a +xb - r\<^sup>2)/(2*r)"
        using A
        by (auto simp: field_simps power2_eq_square)
    } note 2=this
    
    have C1: "a < b + x \<longleftrightarrow> a-b < x" for x by auto
    
    {
      fix xb
      assume A: "r<0"
      have "xb < r * r + r * (sqrt b * 2) \<longleftrightarrow> sqrt b < (xb-r\<^sup>2) / (2*r)"
        using A
        by (auto simp: field_simps power2_eq_square)
    
    } note 3=this
    
    {
      fix xb
      assume A: "0<r"
      have "xb < r * r + r * (sqrt b * 2) \<longleftrightarrow> (xb-r\<^sup>2) / (2*r) < sqrt b"
        using A
        by (auto simp: field_simps power2_eq_square)
    
    } note 4=this
        
          
  
    show ?thesis
      apply (cases "r=0"; cases "r<0"; cases "a=0"; cases "a<0"; cases "b=0"; cases "b<0"; simp add: nz_nlt_conv field_split_simps real_0_less_add_iff)
      apply (simp_all add: sqrt_lt_sqrt_plus_r_def)
      unfolding sqrt_lt_code
      apply (simp_all add: field_simps power2_eq_square real_0_less_add_iff real_0_le_add_iff)
      unfolding 1 2 C1 3 4
      unfolding lt_sqrt_code sqrt_lt_code le_sqrt_code sqrt_le_code
      apply (simp_all add: field_split_simps power2_eq_square)
      done
  qed
    
  definition "sqrt_diff_cmp_lt a r b s \<equiv> sqrt_lt_sqrt_plus_r (sgn s * s\<^sup>2 * (4 * b)) (sgn r * r\<^sup>2 * (4 * a)) (- (\<bar>a\<bar> + (r * r - (\<bar>b\<bar> + s * s))))"

  export_code sqrt_diff_cmp_lt in SML
  
  (* TODO: Move  *)
  lemma abs_lt_square_iff: "\<bar>x\<bar> < \<bar>y\<bar> \<longleftrightarrow> x\<^sup>2 < y\<^sup>2" for x y :: "'a::linordered_idom"
    using abs_le_square_iff linorder_not_le by blast

  lemma power_strict_mono_iff [simp]:
    fixes a b :: "'a::linordered_idom"
    shows "\<lbrakk>a \<ge> 0; b \<ge> 0; n>0\<rbrakk> \<Longrightarrow> a ^ n < b ^ n \<longleftrightarrow> a < b"
    using power_less_imp_less_base power_strict_mono by blast
    
    
  definition "lt_pos_sqrt_diff a b x \<equiv> let
    n\<^sub>1 = x<a\<^sup>2;
    n\<^sub>2 = x<b\<^sup>2
  in case (n\<^sub>1,n\<^sub>2) of
    (False,False) \<Rightarrow> a > b
  | (True,True)   \<Rightarrow> a<b
  | (False,True)  \<Rightarrow>  4*x < (a+b)\<^sup>2
  | (True,False)  \<Rightarrow> (a+b)\<^sup>2 < 4*x
  "  
    
  lemma sqrt_diff_cmp_pos:
    assumes "a>0" "b>0" "x>0"
    shows "\<bar>sqrt x - a\<bar> < \<bar>sqrt x - b\<bar> \<longleftrightarrow> lt_pos_sqrt_diff a b x"  
  proof -
  
    have 1: "sqrt x < a \<longleftrightarrow> x<a\<^sup>2" by (smt (verit, ccfv_SIG) assms(1) le_sqrt_code real_le_rsqrt)
    have 2: "sqrt x < b \<longleftrightarrow> x<b\<^sup>2" by (smt (verit, ccfv_SIG) assms(2) le_sqrt_code real_le_rsqrt)
  
    have 3: "(a < 2 * sqrt x - b) = ((a + b)\<^sup>2 < 4 * x)"
    proof -
      have "(a < 2 * sqrt x - b) \<longleftrightarrow> a+b < sqrt (4*x)" by (auto simp: field_split_simps real_sqrt_mult)
      also have "\<dots> \<longleftrightarrow> (a+b)\<^sup>2 < 4*x" using assms(1) assms(2) lt_sqrt_code real_less_rsqrt by force
      finally show ?thesis .
    qed
    
    have 4: "(2 * sqrt x - a < b) = (4 * x < (a + b)\<^sup>2)"
    proof -
      have "(2 * sqrt x - a < b) \<longleftrightarrow> 2 * sqrt x < a+b" by auto
      also have "\<dots> \<longleftrightarrow> (2*sqrt x)\<^sup>2 < (a+b)\<^sup>2"
        by (smt (verit, ccfv_SIG) assms(1) assms(2) assms(3) pos2 power_strict_mono real_sqrt_gt_zero)
      finally show ?thesis using assms(3) by auto  
    qed
    
    show ?thesis
      using assms
      by (cases "sqrt x - a < 0"; cases "sqrt x - b < 0"; (simp add: abs_real_def lt_pos_sqrt_diff_def Let_def 1 2 3 4 split: bool.splits))
  qed
  
      
    
  lemma sqrt_diff_cmp_lt:
    shows "\<bar>sqrt a - r\<bar> < \<bar>sqrt b - s\<bar> \<longleftrightarrow> sqrt_diff_cmp_lt a r b s"
  proof -  
  
    note CC = linorder_cases[where x=0]
  
    find_theorems "\<bar>_\<bar> \<le> \<bar>_\<bar> \<longleftrightarrow> _"
    
    show ?thesis
      apply (simp add: abs_lt_square_iff power2_eq_square field_simps)
      apply (simp_all add: order_sqrt mult_sqrt)
      apply (simp flip: sqrt_lt_sqrt_plus_r add: sqrt_diff_cmp_lt_def)
      apply (simp add: field_split_simps power2_eq_square)
      done
      
  qed        
    
  definition "check_zs_r_sqrt m s r res \<equiv> check_zs_r m s (sqrt r) res"
  
  lemmas [code_unfold] = check_zs_r_sqrt_def[symmetric] 
  
  lemma sqrt_cmp_z_simps:
    "sqrt x < 0 \<longleftrightarrow> x<0"
    "sqrt x > 0 \<longleftrightarrow> x>0"
    "sqrt x = 0 \<longleftrightarrow> x=0"
    "sqrt x \<le> 0 \<longleftrightarrow> x\<le>0"
    "sqrt x \<ge> 0 \<longleftrightarrow> x\<ge>0"
    by auto
    
  lemma sqrt_eq_conv:
    "sqrt r = x \<longleftrightarrow> sgn r = sgn x \<and> \<bar>r\<bar> = x\<^sup>2"  
    "x = sqrt r \<longleftrightarrow> sgn r = sgn x \<and> \<bar>r\<bar> = x\<^sup>2"  
    apply (auto simp: field_split_simps sgn_real_def power2_eq_square)
    by (metis abs_of_nonpos linorder_le_less_linear real_sqrt_abs2 real_sqrt_minus verit_minus_simplify(4))+
    

  (*
    TODO: We use the more complicated sqrt_diff_cmp_lt here, 
    as it is hard, without rewrite-with-cong-rules, to do the rewrite
    under the side-conditions enforced by the if-statements, i.e.,
    that the operands are actually positive!
    
    See thm sqrt_diff_cmp_pos for a simpler version, that, however, requires these side conditions
  *)    
  schematic_goal check_zs_r_sqrt_code[code]: "check_zs_r_sqrt m s r res \<longleftrightarrow> ?foo"  
    unfolding check_zs_r_sqrt_def
    unfolding check_zs_r_alt check_zs_r_tn_def check_zs_r_tn_aux_def lbound_def rbound_def is_close_def Let_def
    unfolding check_zs_r_tz_def check_zs_r_pinf_def check_zs_r_ninf_def
    unfolding sqrt_cmp_z_simps sqrt_diff_cmp_lt
    unfolding sqrt_eq_conv
    by (rule refl)
    
  export_code check_zs_r_sqrt in SML  
    
        
  definition check_fsqrt :: "roundmode \<Rightarrow> ('e ,'f) float \<Rightarrow> ('e ,'f) float \<Rightarrow> bool"
    where "check_fsqrt m a res =
      (if is_nan a then is_nan res
       else if is_zero a \<or> is_infinity a \<and> sign a = 0 then res=a
       else if sign a = 1 then is_nan res
       else check_zs_r_sqrt m (sign a) (valof a) res)"

  lemma check_fsqrt:
    fixes a b :: "('e,'f) float"
    assumes LEN[simp]: "1 < LENGTH('e)"
    shows "check_fsqrt m a b \<Longrightarrow> fsqrt m a =\<^sub>N\<^sub>a\<^sub>N b"
    unfolding fsqrt_def check_fsqrt_def Let_def check_zs_r_sqrt_def
    apply (elim check_decomp_aux check_zs_r[OF LEN, THEN eq_nan_eqI])
    by simp_all
       
           
  export_code check_fadd check_fsub check_fmul check_fdiv check_fmul_add check_fsqrt checking SML  

  find_consts "(_,_) float \<Rightarrow> (_,_) float"  
    
    
  term valof
  
  find_theorems zerosign float_round
  
  
  
  
end
