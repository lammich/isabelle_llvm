section \<open>Converting Float to Double\<close>
theory IEEE_Float_Extend
imports "../More_Eisbach_Tools" IEEE_Fp_Add_Basic "../LLVM_More_Word_Lemmas" IEEE_Float_To_Word
begin
  text \<open>
    LLVM code only accepts double (64 bit) constants, 
    even for float (32 bit) type. In that case, 
    LLVM requires that the specified double is exactly 
    representable as a float. 
    
    In this theory, we formalize and prove correct this conversion, and reflect it to Isabelle-ML, 
    such that we can use the verified conversion in our code generator.
  \<close>

  subsection \<open>Find Highest Bit\<close>
  (*
    given n>0, find h such that
    
      2^h\<le>n<2^(h+1)
  *)  
  fun highest_bit :: "nat \<Rightarrow> nat"  where
    "highest_bit n = (if n<2 then 0 else 1 + highest_bit (n div 2) )"  
  declare highest_bit.simps[simp del]  
      
  lemma highest_bit_lower: "0<n \<Longrightarrow> 2^highest_bit n \<le> n"  
    apply (induction n rule: highest_bit.induct)
    apply (subst highest_bit.simps)
    by auto
    
  lemma highest_bit_upper: "n < 2^(highest_bit n+1)"  
    apply (induction n rule: highest_bit.induct)
    apply (subst highest_bit.simps)
    by auto
    
  lemmas highest_bit_bounds = highest_bit_lower highest_bit_upper
    
  definition "lower_bits n \<equiv> n - 2^highest_bit n"
  
  lemma lower_bits_upper: "lower_bits n < 2^highest_bit n"
    unfolding lower_bits_def
    using highest_bit_bounds[of n]
    by (auto)
  
  lemma highest_lower_char: "0<n \<Longrightarrow> 2^highest_bit n + lower_bits n = n"
    by (simp add: highest_bit_lower lower_bits_def)
  
  text \<open>Can also be expressed with floorlog! \<close>
  lemma highest_bit_is_floorlog: "highest_bit n = floorlog 2 n - 1"  
    by (smt (verit, ccfv_SIG) Suc_pred' add_diff_cancel_right' floorlog_ge_SucI floorlog_leI highest_bit.simps highest_bit_lower highest_bit_upper le_less_trans nat_less_le one_less_numeral_iff semiring_norm(76) zero_less_diff zero_order(1))

  lemma compute_highest_bit:
    "highest_bit 0 = 0"  
    "highest_bit 1 = 0"
    "highest_bit (Suc 0) = 0"
    "highest_bit (numeral n) = (if numeral n < (2::nat) then 0 else 1 + highest_bit (numeral n div 2))"
    by (subst highest_bit.simps; simp; fail)+

  lemma highest_bit_mono: "a\<le>b \<Longrightarrow> highest_bit a \<le> highest_bit b"  
    unfolding highest_bit_is_floorlog
    using diff_le_mono floorlog_mono by presburger

  lemma highest_bit_mono': "a<b \<Longrightarrow> highest_bit a \<le> highest_bit b"  
    using highest_bit_mono by simp
    
    
    
  
  subsection \<open>Extend Floating Point Number\<close>

  text \<open>Locale to summarize correctness criterion:
    all (meaningful) properties are preserved. In case of NaN, 
    the payload is bit-shifted.
  \<close>
  locale correct_extension =
    fixes f\<^sub>1 :: "('e\<^sub>1,'f\<^sub>1) float"
      and f\<^sub>2 :: "('e\<^sub>2,'f\<^sub>2) float"
    fixes \<Delta>\<^sub>F
    defines "\<Delta>\<^sub>F \<equiv> LENGTH('f\<^sub>2) - LENGTH('f\<^sub>1)"  
    assumes preserves_sign[simp]: "sign f\<^sub>2 = sign f\<^sub>1"  
    assumes preserves_finiteness[simp]: 
      "is_finite f\<^sub>2 \<longleftrightarrow> is_finite f\<^sub>1"
      "is_infinity f\<^sub>2 \<longleftrightarrow> is_infinity f\<^sub>1"
    assumes preserves_nan[simp]: "is_nan f\<^sub>2 \<longleftrightarrow> is_nan f\<^sub>1"
    assumes preserves_valof[simp]: "is_finite f\<^sub>1 \<Longrightarrow> valof f\<^sub>2 = valof f\<^sub>1"
    assumes preserves_nan_payload[simp]: "is_nan f\<^sub>1 \<Longrightarrow> fraction f\<^sub>2 = fraction f\<^sub>1 * 2^\<Delta>\<^sub>F"
  begin
  
  
  end
  

  text \<open>We only cover the case where \<open>f\<^sub>1 \<le> 2^(e\<^sub>2-1) - 2^(e\<^sub>1-1)\<close>.
    In this case, a denormal number is always extended to a normal number.
  \<close>
  locale float_extend_conv =
    fixes F1 :: "('e\<^sub>1,'f\<^sub>1) float itself"
    fixes F2 :: "('e\<^sub>2,'f\<^sub>2) float itself"
    assumes ELEN': "LENGTH('e\<^sub>1) \<le> LENGTH('e\<^sub>2)"
    assumes FLEN': "LENGTH('f\<^sub>1) \<le> LENGTH('f\<^sub>2)"
    assumes E\<^sub>2_cond': "LENGTH('f\<^sub>1) \<le> 2^(LENGTH('e\<^sub>2)-1)-2^(LENGTH('e\<^sub>1)-1)"
  begin
  
    context
      fixes E\<^sub>1 E\<^sub>2 F\<^sub>1 F\<^sub>2 \<Delta>\<^sub>E \<Delta>\<^sub>F \<Delta>\<^sub>B B\<^sub>1 B\<^sub>2
      fixes f :: "('e\<^sub>1,'f\<^sub>1) float"
      defines "E\<^sub>1 \<equiv> LENGTH('e\<^sub>1)"
      defines "E\<^sub>2 \<equiv> LENGTH('e\<^sub>2)"
      defines "F\<^sub>1 \<equiv> LENGTH('f\<^sub>1)"
      defines "F\<^sub>2 \<equiv> LENGTH('f\<^sub>2)"
      
      defines B\<^sub>1_def': "B\<^sub>1 \<equiv> bias TYPE(('e\<^sub>1,'f\<^sub>1)float)"
      defines B\<^sub>2_def': "B\<^sub>2 \<equiv> bias TYPE(('e\<^sub>2,'f\<^sub>2)float)"
      
      defines "\<Delta>\<^sub>E \<equiv> E\<^sub>2 - E\<^sub>1"
      defines "\<Delta>\<^sub>F \<equiv> F\<^sub>2 - F\<^sub>1"
      defines "\<Delta>\<^sub>B \<equiv> B\<^sub>2 - B\<^sub>1"
      
    begin
  
      definition conv_norm :: "('e\<^sub>2,'f\<^sub>2) float" where                 
        "conv_norm \<equiv> Abs_float' (sign f) (exponent f + \<Delta>\<^sub>B) (2^\<Delta>\<^sub>F*fraction f)"
    
      definition conv_denorm :: "('e\<^sub>2,'f\<^sub>2) float" where 
        "conv_denorm \<equiv> let
          h = highest_bit (fraction f);
          r = lower_bits  (fraction f)
        in
          Abs_float' (sign f) (\<Delta>\<^sub>B+1 - LENGTH('f\<^sub>1) + h) (2^(LENGTH('f\<^sub>2)-h) * r)"
    
      definition conv_zero :: "('e\<^sub>2,'f\<^sub>2) float" where
        "conv_zero \<equiv> if sign f = 0 then 0 else minus_zero"

      definition conv_inf :: "('e\<^sub>2,'f\<^sub>2) float" where
        "conv_inf \<equiv> if sign f = 0 then plus_infinity else minus_infinity"

      definition conv_nan :: "('e\<^sub>2,'f\<^sub>2) float" where
        "conv_nan \<equiv> Abs_float' (sign f) (emax TYPE(('e\<^sub>2, 'f\<^sub>2)float)) (fraction f * 2^\<Delta>\<^sub>F)"
                
      definition conv :: "('e\<^sub>2,'f\<^sub>2) float" where
        "conv \<equiv> 
             if is_normal f then conv_norm
        else if is_denormal f then conv_denorm
        else if is_infinity f then conv_inf
        else if is_zero f then conv_zero
        else conv_nan" 
  
      schematic_goal conv_eq_unfolded: 
        defines "TAG \<equiv> \<lambda>x. x"
        shows "conv = TAG ?foo" 
        unfolding conv_def conv_norm_def conv_denorm_def conv_inf_def conv_zero_def conv_nan_def
        unfolding TAG_def ..
        
                  
      lemma ELEN: "E\<^sub>1 \<le> E\<^sub>2"    
        unfolding E\<^sub>1_def E\<^sub>2_def using ELEN' by auto
                    
      lemma FLEN: "F\<^sub>1 \<le> F\<^sub>2"    
        unfolding F\<^sub>1_def F\<^sub>2_def using FLEN' by auto
          
      lemma LEN_ne_Z[simp]: 
        "E\<^sub>1\<noteq>0" "E\<^sub>2\<noteq>0" "F\<^sub>1\<noteq>0" "F\<^sub>2\<noteq>0" 
        "E\<^sub>1>0" "E\<^sub>2>0" "F\<^sub>1>0" "F\<^sub>2>0" 
        "E\<^sub>1\<ge>Suc 0" "E\<^sub>2\<ge>Suc 0" "F\<^sub>1\<ge>Suc 0" "F\<^sub>2\<ge>Suc 0" 
        unfolding E\<^sub>1_def E\<^sub>2_def F\<^sub>1_def F\<^sub>2_def 
        by (auto simp: Suc_leI)

      lemma B\<^sub>1_def: "B\<^sub>1 = 2^(E\<^sub>1-1)-1"  
        unfolding B\<^sub>1_def' bias_def E\<^sub>1_def ..
        
      lemma B\<^sub>2_def: "B\<^sub>2 = 2^(E\<^sub>2-1)-1"  
        unfolding B\<^sub>2_def' bias_def E\<^sub>2_def ..
        
      lemma fr_bound[simp]: "fraction f < 2 ^ F\<^sub>1"  
        unfolding F\<^sub>1_def by (simp add: fraction_upper_bound)
        
      lemma exp_bound[simp]: "exponent f < 2 ^ E\<^sub>1"  
        unfolding E\<^sub>1_def by (simp add: exponent_upper_bound)
        
      lemmas shortcut_defs[no_atp] = E\<^sub>1_def E\<^sub>2_def F\<^sub>1_def F\<^sub>2_def B\<^sub>1_def' B\<^sub>2_def'
      lemmas shortcut_folds[simp, no_atp] = shortcut_defs[symmetric]

      lemma LEN2_conv:
        "E\<^sub>2 = E\<^sub>1 + \<Delta>\<^sub>E"  
        "F\<^sub>2 = F\<^sub>1 + \<Delta>\<^sub>F"  
        unfolding \<Delta>\<^sub>E_def \<Delta>\<^sub>F_def using ELEN FLEN by auto

      lemma BLEN: "B\<^sub>1 \<le> B\<^sub>2"  
        unfolding B\<^sub>1_def B\<^sub>2_def using ELEN 
        by (meson diff_le_mono one_le_numeral power_increasing)
        
      lemma bias2_conv: "B\<^sub>2 = B\<^sub>1 + \<Delta>\<^sub>B"  
        unfolding \<Delta>\<^sub>B_def using BLEN by simp
      
                      
      lemma \<Delta>\<^sub>B_alt: "\<Delta>\<^sub>B = 2^(E\<^sub>1-1)*(2^\<Delta>\<^sub>E - 1)"
        unfolding \<Delta>\<^sub>B_def \<Delta>\<^sub>E_def B\<^sub>1_def B\<^sub>2_def
        using ELEN
        by (auto simp: algebra_simps Suc_le_eq simp flip: power_add)
      
  
      lemma aux_simp1[simp]: "E\<^sub>2 - E\<^sub>1 + (E\<^sub>1 - Suc 0) = E\<^sub>2 - 1"  
        by (simp add: ELEN Suc_le_eq)
        
        
      lemma \<Delta>\<^sub>B_lt[simp]: "\<Delta>\<^sub>B < 2 ^ E\<^sub>2" 
        unfolding \<Delta>\<^sub>B_alt \<Delta>\<^sub>E_def
        using ELEN 
        by (auto simp: algebra_simps LEN2_conv less_imp_diff_less simp flip: power_add)
        
  
      lemma \<Delta>\<^sub>B_lt'[simp]: "Suc \<Delta>\<^sub>B < 2 ^ E\<^sub>2" 
        unfolding \<Delta>\<^sub>B_alt \<Delta>\<^sub>E_def
        using ELEN 
        apply (auto simp: algebra_simps LEN2_conv simp flip: power_add)
        by (smt (verit, best) LEN2_conv(1) LEN_ne_Z(6) Suc_pred diff_less less_imp_diff_less linorder_neqE_nat not_less_eq one_less_numeral_iff pos2 power_Suc power_less_power_Suc semiring_norm(76) zero_less_power)
        
      lemma sign_lt[simp]: "sign f < 2"  
        by (cases f rule: sign_cases) auto
        

        
      abbreviation "H \<equiv> highest_bit (fraction f)"   
      abbreviation "L \<equiv> lower_bits (fraction f)"   
        
      lemma H_upper: "H < F\<^sub>1"
        by (metis LEN_ne_Z(3) floorlog_leI fr_bound highest_bit.simps highest_bit_is_floorlog highest_bit_lower leD less_imp_diff_less less_nat_zero_code nat_less_le nat_neq_iff one_less_numeral_iff pos2 semiring_norm(76))
                      
      lemma [simp]: "Suc (\<Delta>\<^sub>B + H) - F\<^sub>1 < 2 ^ E\<^sub>2"
        using H_upper \<Delta>\<^sub>B_lt' by linarith
        
      lemma [simp]: "2 ^ (F\<^sub>2 - H) * L < 2 ^ F\<^sub>2"   
        using FLEN H_upper diff_le_self lower_bits_upper nat_less_power_trans by auto

      lemma E\<^sub>2_cond: "F\<^sub>1 \<le> 2^(E\<^sub>2-1)-2^(E\<^sub>1-1)" using E\<^sub>2_cond' by simp
        
      lemma \<Delta>\<^sub>B_bound[simp]: "Suc \<Delta>\<^sub>B > F\<^sub>1"
        by (metis B\<^sub>1_def B\<^sub>2_def E\<^sub>2_cond \<Delta>\<^sub>B_def diff_diff_left le_add_diff_inverse le_imp_less_Suc one_le_numeral one_le_power)
          
      lemma [simp]: "Suc \<Delta>\<^sub>B \<ge> F\<^sub>1" 
        using \<Delta>\<^sub>B_bound by linarith
             
      lemma [simp]: "\<not>(Suc (\<Delta>\<^sub>B+H) \<le> F\<^sub>1)"  
        using \<Delta>\<^sub>B_bound by linarith

        
      lemma [simp]: "fraction f * 2 ^ \<Delta>\<^sub>F < 2 ^ F\<^sub>2"
        by (simp add: LEN2_conv(2) nat_mult_power_less_eq)
        
      lemma [simp]: "emax TYPE(('e\<^sub>2, 'f\<^sub>2) IEEE.float) = 2 ^ E\<^sub>2 - 1"  
        unfolding emax_def E\<^sub>2_def
        using unat_minus_one_word by blast
        
      (*lemma [simp]: "emax TYPE(('e\<^sub>2, 'f\<^sub>2) IEEE.float) < 2 ^ E\<^sub>2"  
        unfolding emax_def E\<^sub>2_def
        by blast
      *)
        
                
      lemma exp_\<Delta>\<^sub>B_bound[simp]: "(IEEE.exponent f + \<Delta>\<^sub>B) < 2 ^ E\<^sub>2"  
        unfolding \<Delta>\<^sub>B_alt \<Delta>\<^sub>E_def
      proof (simp add: algebra_simps flip: power_add )
        show "exponent f + (2 ^ (E\<^sub>2 - Suc 0) - 2 ^ (E\<^sub>1 - Suc 0)) < 2 ^ E\<^sub>2" (is "?lhs<_")
        proof -
          have "?lhs = exponent f + (2^(E\<^sub>2-1) - 2^(E\<^sub>1-1))" using ELEN by auto
          also have "\<dots> < 2^E\<^sub>1 + (2^(E\<^sub>2-1) - 2^(E\<^sub>1-1))" using exponent_upper_bound[of f] by (simp)
          also have "\<dots> = 2^(E\<^sub>1-1) + 2^(E\<^sub>1-1) + (2^(E\<^sub>2-1) - 2^(E\<^sub>1-1))" using ELEN 
            by (metis LEN_ne_Z(5) Suc_diff_1 mult.commute mult_2_right power_Suc)
          also have "\<dots> = 2^(E\<^sub>1-1) + 2^(E\<^sub>2-1)" using ELEN by simp
          also have "\<dots> \<le> 2^(E\<^sub>2-1) + 2^(E\<^sub>2-1)" using ELEN by simp
          also have "\<dots> \<le> 2^E\<^sub>2"
            by (metis LEN_ne_Z(6) Suc_pred' le_refl mult.commute mult_2_right power_Suc)
          finally show ?thesis .
        qed        
      qed
  
      theorem conv_norm_correct: 
        "is_normal f \<Longrightarrow> valof (conv_norm) = valof f"
        "is_normal f \<Longrightarrow> sign conv_norm = sign f"
        unfolding is_normal_def valof_eq conv_norm_def
        apply simp_all
        apply (simp add: bias2_conv LEN2_conv)
        apply (simp add: field_simps power_add of_nat_diff fraction_upper_bound)
        done

        
        
      lemma exponent_bound_finite:
        assumes "exponent f < 2 ^ E\<^sub>1 - Suc 0"  
        shows "exponent f + \<Delta>\<^sub>B < 2 ^ E\<^sub>2 - Suc 0"  
      proof -
      
        have "(2::nat)^E\<^sub>1 = (2::nat)^(E\<^sub>1-1) + (2::nat)^(E\<^sub>1-1)"
          by (metis LEN_ne_Z(5) Suc_diff_1 mult.commute mult_2_right power_Suc)
        then have "(2::nat) ^ E\<^sub>1 + (2 ^ (E\<^sub>2 - Suc 0) - 2 ^ (E\<^sub>1 - Suc 0)) = 2 ^ (E\<^sub>1 - Suc 0) + 2 ^ (E\<^sub>2 - Suc 0)"
          using ELEN 
          by (simp add: algebra_simps)
        also have "(2::nat) ^ (E\<^sub>1 - Suc 0) \<le> 2 ^ (E\<^sub>2 - Suc 0)"  
          using ELEN by simp
        finally  
        have "(2::nat) ^ E\<^sub>1 + (2 ^ (E\<^sub>2 - Suc 0) - 2 ^ (E\<^sub>1 - Suc 0)) \<le> 2 ^ E\<^sub>2"
          apply (simp)
          by (metis LEN_ne_Z(6) One_nat_def Suc_diff_1 mult.commute mult_2_right power_Suc)
        then have 1: "2 ^ E\<^sub>1 - Suc 0 + (2 ^ (E\<^sub>2 - Suc 0) - 2 ^ (E\<^sub>1 - Suc 0)) \<le> 2 ^ E\<^sub>2 - Suc 0" 
          by auto
        
        show ?thesis using assms
          unfolding \<Delta>\<^sub>B_def B\<^sub>1_def B\<^sub>2_def 
          apply (auto simp: algebra_split_simps)
          using 1 by linarith
      qed  
        
      lemma conv_norm_normal: "is_normal f \<Longrightarrow> is_normal conv_norm"
        unfolding is_normal_def valof_eq conv_norm_def emax_eq
        by (simp_all add: exponent_bound_finite)
        
                 
      theorem conv_denorm_correct: 
        "is_denormal f \<Longrightarrow> valof (conv_denorm) = valof f"
        "is_denormal f \<Longrightarrow> sign (conv_denorm) = sign f"
        unfolding is_denormal_def
        apply (rewrite in "_ = \<hole>" valof_eq)
        apply simp_all
        apply (subst highest_lower_char[of "fraction f", symmetric], simp)
        unfolding valof_eq conv_denorm_def Let_def
        apply simp_all
        apply (clarsimp simp: )
        apply (simp add: bias2_conv LEN2_conv)
      proof goal_cases
        case 1
        assume "exponent f = 0" and "0 < fraction f"
  
        have 1: "2 ^ (F\<^sub>1 + \<Delta>\<^sub>F - H) * real L / 2 ^ (F\<^sub>1 + \<Delta>\<^sub>F) = real L / 2^H"
          using H_upper 
          by (simp add: power_diff)
        
        have [simp]: "F\<^sub>1 + (H + (Suc (\<Delta>\<^sub>B + H) - F\<^sub>1)) = 2*H + \<Delta>\<^sub>B + 1"
          apply (simp)
          using \<Delta>\<^sub>B_bound by linarith
          
        have [simp]: "F\<^sub>1 + (Suc (\<Delta>\<^sub>B + H) - F\<^sub>1) = \<Delta>\<^sub>B + H + 1"  
          apply (simp)
          using \<Delta>\<^sub>B_bound by linarith
          
        have "2 ^ (Suc \<Delta>\<^sub>B - F\<^sub>1 + H) * (1 + 2 ^ (F\<^sub>1 + \<Delta>\<^sub>F - H) * real L / 2 ^ (F\<^sub>1 + \<Delta>\<^sub>F)) / 2 ^ (B\<^sub>1 + \<Delta>\<^sub>B) =
          2 * (2 ^ H + real L) / (2 ^ B\<^sub>1 * 2 ^ F\<^sub>1)" 
          unfolding 1
          apply simp
          apply (auto simp: field_split_simps simp flip: power_add)
          done
            
        then show ?case 
          apply (cases f rule: sign_cases)
          apply (auto simp: field_simps)
          done
          
      qed

      lemma conv_denorm_normal: "is_denormal f \<Longrightarrow> is_normal conv_denorm"
        unfolding conv_denorm_def is_denormal_def is_normal_def Let_def
        apply auto
        subgoal using \<Delta>\<^sub>B_bound by linarith
        subgoal using H_upper \<Delta>\<^sub>B_lt' by linarith
        done
      
      theorem conv_zero_correct: "is_zero f \<Longrightarrow> is_zero conv_zero \<and> sign conv_zero = sign f"
        unfolding conv_zero_def
        apply (cases f rule: sign_cases)
        by auto
      
      theorem conv_inf_correct: "is_infinity f \<Longrightarrow> is_infinity conv_inf \<and> sign conv_inf = sign f"
        unfolding conv_inf_def
        apply (cases f rule: sign_cases)
        by auto
        
      theorem conv_nan_correct: "is_nan f \<Longrightarrow> is_nan conv_nan \<and> sign conv_nan = sign f \<and> fraction conv_nan = fraction f * 2^\<Delta>\<^sub>F"
        unfolding conv_nan_def is_nan_def
        by (simp)
        
      lemma normal_imp_finite: "is_normal ff \<Longrightarrow> is_finite ff"
        by (simp add: is_finite_def)

      lemma denormal_imp_finite: "is_denormal ff \<Longrightarrow> is_finite ff"
        by (simp add: is_finite_def)

      lemma zero_imp_finite: "is_zero ff \<Longrightarrow> is_finite ff"  
        by (simp add: is_finite_def)
                        
      lemma infinity_finite: "is_infinity f \<Longrightarrow> \<not>is_finite f"
        using finite_infinity by auto
        
      lemma [simp, intro!]: "\<not>is_finite conv_inf"  
        unfolding conv_inf_def by auto
        
      lemma nan_imp_not_infinity: "is_nan ff \<Longrightarrow> \<not>is_infinity ff"  
        using float_distinct(1) by blast
        
      lemma conv_norm_nan: "is_normal f \<Longrightarrow> \<not> is_nan conv_norm"  
        by (meson conv_norm_normal float_distinct(2))

      lemma conv_denorm_nan: "is_denormal f \<Longrightarrow> \<not> is_nan conv_denorm"  
        by (meson conv_denorm_normal float_distinct(2))
        
      lemma [simp, intro!]: "\<not>is_nan conv_zero"  
        unfolding conv_zero_def
        by (simp add: is_nan_def)
        
      lemma [simp, intro!]: "\<not>is_nan conv_inf"  
        unfolding conv_inf_def
        by (simp add: is_nan_def)
                
      lemma conv_correct_aux:
        "sign conv = sign f"  
        "is_finite conv \<longleftrightarrow> is_finite f"
        "is_infinity conv \<longleftrightarrow> is_infinity f"
        "is_nan conv \<longleftrightarrow> is_nan f"
        "is_finite f \<Longrightarrow> valof conv = valof f"
        "is_nan f \<Longrightarrow> fraction conv = fraction f * 2^\<Delta>\<^sub>F"
        supply [simp, intro] = conv_denorm_normal conv_norm_normal normal_imp_finite denormal_imp_finite zero_imp_finite infinity_finite finite_infinity
          conv_nan_correct conv_norm_correct conv_denorm_correct conv_zero_correct conv_inf_correct
          nan_imp_not_infinity conv_norm_nan conv_denorm_nan
        
        apply (cases f rule: float_cases'; simp add: conv_def)
        apply (cases f rule: float_cases'; simp add: conv_def) 
        apply (cases f rule: float_cases'; simp add: conv_def) 
        apply (cases f rule: float_cases'; simp add: conv_def) 
        apply (cases f rule: float_cases'; simp add: conv_def val_zero) 
        apply (cases f rule: float_cases'; simp add: conv_def) 
        done
              
      lemma conv_correct: "correct_extension f conv"  
        apply unfold_locales
        apply (simp_all add: conv_correct_aux \<Delta>\<^sub>F_def)
        done
        
    end
  end    

subsection \<open>Standard Float Sizes\<close>  
  
  
  context begin
    interpretation float_extend_conv "TYPE((8,23) float)" "TYPE((11,52)float)"
      apply unfold_locales
      by simp_all
  
    definition [code del]: "float_extend_32_64 \<equiv> conv"
      
    lemmas float_extend_32_64_code[code] = conv_eq_unfolded[folded float_extend_32_64_def]  

    lemmas float_extend_32_64_correct = conv_correct[folded float_extend_32_64_def]
          
  end

  definition "fext_word_32_64 = fp64_of_float o float_extend_32_64 o float_of_fp32"
  


end
