section \<open>Next Floating Point Number\<close>
theory IEEE_Fp_Nextfloat
imports IEEE_Fp_Add_Basic
begin

  subsection \<open>Basic Definition\<close>

  lift_definition next_float :: "('e,'f) float \<Rightarrow> ('e,'f) float" is
    "\<lambda>(s,e,f). if s=1 then (
        if f=0 \<and> e=0 then (0,e,f)
        else if f=0 then (s,e-1,f-1)
        else (s,e,f-1)
      ) else (
        if f=max_word then (s,e+1,0)
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
  lemma next_float_finiteI: "\<lbrakk>is_finite f; f\<noteq>topfloat\<rbrakk> \<Longrightarrow> is_finite (next_float f)"
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

  (* TODO: Move *)  
  lemma zero_neq_topfloat[simp]:
    "0\<noteq>topfloat"  
    "topfloat\<noteq>0"  
    by (metis bottomfloat_simps(3) diff_diff_cancel diff_zero float_sel_simps(12) leD nat_le_linear nat_power_eq_Suc_0_iff power_0 two_plen_gt1)+
    
  lemma mzero_neq_topfloat[simp]: 
    "-0 \<noteq> topfloat"  
    "topfloat \<noteq> -0"  
    by (metis float_sel_simps(13) float_sel_simps(8) len_not_eq_0 len_num1)+
    
  lemma zero_finite[simp]: "is_finite 0"  
    by (meson float_zero1 is_finite_def)
    
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

  lemma largest_gtZ: "largest TYPE((_,_) float) > 0"  
    by (simp add: divide_less_eq largest_def power_gt1_lemma)

  lemma largest_gtZ'[simp]: "\<not>(largest TYPE((_,_) float) < 0)"  
    by (smt (verit) largest_gtZ)
    
        
  lemma 
    assumes "is_finite f" "f\<noteq>topfloat"
    assumes "valof f \<le> r" "r < valof (next_float f)"
    shows "round To_ninfinity r = f"  
    apply (auto dest: order.strict_trans simp: not_less)
    xxx, cdt here
    
  next step:
    rounding is ndet in zero case.
    disambiguate that. 
    Should be unique together with zerosign
       
    
  term fadd  
    
  value "fadd To_nearest  0 (0::(11,52)float)"
  
  oops  
  xxx, ctd here: do rounding  
      
  
  value "(12.78368::real) + (12.34781283)"  

  find_consts "(_,_)float \<Rightarrow> _ word"
  
  
  value "valof (next_float 0::(11,52)float) + 1.6728" 
  
  value "next_float (0::(52,15)float)"  
    
    
    

end
