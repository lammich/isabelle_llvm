section \<open>Floating Points as Integers\<close>
text \<open>Used for LLVM code generator, as LLVM represents floating point constants
  as integer numbers.
\<close>
theory IEEE_Float_Extend_Integer
imports LLVM_More_Word_Lemmas IEEE_Float_To_Word IEEE_Float_Extend
begin

subsection \<open>Miscellaneous Lemmas\<close>

  lemma int_bit_shift_add_bound:
    fixes e f :: int
    assumes LF: "f<2^F"
        and LE: "e<2^E"
    shows "f+e*2^F < 2^(E+F)"
  proof -
    from LE have "e \<le> 2^E - 1" by simp
    hence "e*2^F \<le> (2^E - 1) * 2^F" by simp
    also have "\<dots> = 2^(E+F) - 2^F" by (simp add: power_add algebra_simps)
    finally have "e * 2 ^ F \<le> 2 ^ (E + F) - 2 ^ F" .
    thus ?thesis using LF by linarith
  qed
  
  lemma nat_bit_shift_add_bound:
    fixes e f :: nat
    assumes LF: "f<2^F"
        and LE: "e<2^E"
    shows "f+e*2^F < 2^(E+F)"
  proof -
    from LE have "e \<le> 2^E - 1" by simp
    hence "e*2^F \<le> (2^E - 1) * 2^F" by simp
    also have "\<dots> = 2^(E+F) - 2^F" by (simp add: power_add algebra_simps)
    finally have "e * 2 ^ F \<le> 2 ^ (E + F) - 2 ^ F" .
    thus ?thesis using LF
      by (metis LE add.commute nat_add_offset_less)
  qed
  
  
  lemma uint_bit_shift_add_bound:
    fixes f :: "'f::len word"
      and e :: "'e::len word"
    shows "uint (f) + uint (e) * 2 ^ LENGTH('f) < 2^(LENGTH('e) + LENGTH('f))"
    apply (rule int_bit_shift_add_bound)
    by auto

  lemma unat_bit_shift_add_bound:
    fixes f :: "'f::len word"
      and e :: "'e::len word"
    shows "unat (f) + unat (e) * 2 ^ LENGTH('f) < 2^(LENGTH('e) + LENGTH('f))"
    apply (rule nat_bit_shift_add_bound)
    by auto
    
  lemma uint_word_cat_eq:
    fixes w\<^sub>1 :: "'l\<^sub>1::len word"
    fixes w\<^sub>2 :: "'l\<^sub>2::len word"
    assumes "LENGTH('l\<^sub>1) + LENGTH('l\<^sub>2) \<le> LENGTH('l\<^sub>3)"
    shows "uint (word_cat w\<^sub>1 w\<^sub>2 :: 'l\<^sub>3::len word) = uint w\<^sub>2 + uint w\<^sub>1 * 2^LENGTH('l\<^sub>2)"  
  proof -
    have [simp]: 
      "is_up UCAST('l\<^sub>1 \<rightarrow> 'l\<^sub>3)" 
      "is_up UCAST('l\<^sub>2 \<rightarrow> 'l\<^sub>3)" 
      using assms 
      by (auto simp add: is_up)

    have [simp]: "LENGTH('l\<^sub>2) < LENGTH('l\<^sub>3)"
      using assms 
      by (metis add_diff_cancel_right' add_leD2 diff_is_0_eq' le_neq_implies_less len_not_eq_0)
      
          
      
    have B2: "uint w\<^sub>2 + uint w\<^sub>1 * uint ((2::'l\<^sub>3 word) ^ LENGTH('l\<^sub>2)) < 2 ^ LENGTH('l\<^sub>3)"
      apply (simp add: uint_2p_alt)
      apply (rule order.strict_trans2[OF uint_bit_shift_add_bound])
      using assms by simp

    have B1: "uint w\<^sub>1 * uint ((2::'l\<^sub>3 word) ^ LENGTH('l\<^sub>2)) < 2 ^ LENGTH('l\<^sub>3)" 
      by (smt (verit) B2 uint_ge_0)
          
    show ?thesis  
      apply (simp add: word_cat_eq' concat_bit_eq take_bit_eq_mod push_bit_eq_mult)
      apply (simp add: uint_word_ariths uint_up_ucast B1 B2)
      apply (simp add: uint_2p_alt)
      done
  qed      

  lemma unat_word_cat_eq:
    fixes w\<^sub>1 :: "'l\<^sub>1::len word"
    fixes w\<^sub>2 :: "'l\<^sub>2::len word"
    assumes "LENGTH('l\<^sub>1) + LENGTH('l\<^sub>2) \<le> LENGTH('l\<^sub>3)"
    shows "unat (word_cat w\<^sub>1 w\<^sub>2 :: 'l\<^sub>3::len word) = unat w\<^sub>2 + unat w\<^sub>1 * 2^LENGTH('l\<^sub>2)"  
  proof -
    have [simp]: 
      "is_up UCAST('l\<^sub>1 \<rightarrow> 'l\<^sub>3)" 
      "is_up UCAST('l\<^sub>2 \<rightarrow> 'l\<^sub>3)" 
      using assms 
      by (auto simp add: is_up)

    have [simp]: "LENGTH('l\<^sub>2) < LENGTH('l\<^sub>3)"
      using assms 
      by (metis add_diff_cancel_right' add_leD2 diff_is_0_eq' le_neq_implies_less len_not_eq_0)
      
          
      
    have B2: "unat w\<^sub>2 + unat w\<^sub>1 * unat ((2::'l\<^sub>3 word) ^ LENGTH('l\<^sub>2)) < 2 ^ LENGTH('l\<^sub>3)"
      apply (simp)
      apply (rule order.strict_trans2[OF unat_bit_shift_add_bound])
      using assms by simp

    have B1: "unat w\<^sub>1 * unat ((2::'l\<^sub>3 word) ^ LENGTH('l\<^sub>2)) < 2 ^ LENGTH('l\<^sub>3)" 
      using B2 by linarith
          
    find_theorems unat ucast  
      
    show ?thesis  
      apply (simp add: word_cat_eq' concat_bit_eq take_bit_eq_mod push_bit_eq_mult)
      apply (simp add: unat_word_ariths unat_ucast_upcast B1 B2)
      using B2 by auto
  qed      
  
  
subsection \<open>Floating Point to Integer Conversion\<close>  
  
  context float_conv_word
  begin    
    lemma uint_WoF_alt: "uint (WoF f) = (fraction f) + (exponent f) * 2 ^ LENGTH('f) + (sign f) * 2 ^ LENGTH('l\<^sub>1)"  
      unfolding WoF_def word_of_float_def
      apply simp
      apply transfer'
      apply (clarsimp)
      apply (subst uint_word_cat_eq, simp add: LEN1)
      apply (subst uint_word_cat_eq, simp add: LEN1')
      by simp

    lemma unat_WoF_alt: "unat (WoF f) = (fraction f) + (exponent f) * 2 ^ LENGTH('f) + (sign f) * 2 ^ LENGTH('l\<^sub>1)"  
      unfolding WoF_def word_of_float_def
      apply simp
      apply transfer'
      apply (clarsimp)
      apply (subst unat_word_cat_eq, simp add: LEN1)
      apply (subst unat_word_cat_eq, simp add: LEN1')
      by simp
            
    lemma fraction_FoW: "fraction (FoW a) = unat a mod 2^LENGTH('f)"  
      unfolding FoW_def float_of_word_def
      apply simp
      apply transfer'
      apply (clarsimp simp: apsnd_def map_prod_def word_split_def split: prod.split)
      by (simp add: unat_ucast LEN1' mod_mod_power)
      
    lemma exponent_FoW: "exponent (FoW a) = unat a div 2 ^ LENGTH('f) mod 2 ^ LENGTH('e)"  
      unfolding FoW_def float_of_word_def
      apply simp
      apply transfer'
      apply (clarsimp simp: apsnd_def map_prod_def drop_bit_eq_div word_split_def split: prod.split)
      apply (simp add: unat_ucast LEN1' mod_mod_power unat_div algebra_simps power_mod_div)
      done
      
    lemma sign_FoW: "sign (FoW a) = unat a div 2 ^ (LENGTH('e) + LENGTH('f))"  
      unfolding FoW_def float_of_word_def
      apply simp
      apply transfer'
      apply (clarsimp simp: apsnd_def map_prod_def drop_bit_eq_div word_split_def split: prod.split)
      apply (simp add: unat_ucast LEN LEN1' mod_mod_power unat_div algebra_simps power_mod_div)
      by (metis LEN1 LEN1' bits_div_by_1 div_exp_mod_exp_eq numeral_2_eq_2 power_one_right unat_word_ariths(6) unsigned_1)
      
    lemmas FoW_components = fraction_FoW exponent_FoW sign_FoW
            
  end    

  subsection \<open>Verified Extension on Integer Representation\<close>  
    
    
  definition "fext_int_32_64 \<equiv> integer_of_word o fext_word_32_64 o word_of_integer"
  
  theorem fext_int_32_64_correct:
    fixes i32 :: "integer"
    defines "i64 \<equiv> fext_int_32_64 i32"
    defines "f32 \<equiv> float_of_fp32 (word_of_integer i32)"
    defines "f64 \<equiv> float_of_fp64 (word_of_integer i64)"
    shows "correct_extension f32 f64"
    unfolding assms fext_int_32_64_def fext_word_32_64_def
    by (simp add: float_extend_32_64_correct)
  

  subsubsection \<open>Direct Implementation for Efficient Code Generation\<close>  
    
  lemma let_distrib: "f (let x=v in g x) = (let x=v in f (g x))" by simp   
        
  lemma Abs_float'_parts_bounds:
    "s<2 \<Longrightarrow> sign (Abs_float' s e f :: ('e,'f) float) = s"
    "e<2^LENGTH('e) \<Longrightarrow> exponent (Abs_float' s e f :: ('e,'f) float) = e"
    "f<2^LENGTH('f) \<Longrightarrow> fraction (Abs_float' s e f :: ('e,'f) float) = f"
    by auto
  
  
  lemma unat_div_bound_aux: "(2^LENGTH('l)-1) div x < n \<Longrightarrow> unat (a::'l::len word) div x < n"
    by (metis One_nat_def Suc_pred bot_nat_0.not_eq_extremum div_by_0 div_less_iff_less_mult le_less_trans less_mult_imp_div_less linorder_not_le not_less_eq unsigned_less)
    
  lemma highest_bit_mod_lessI: "n>0 \<Longrightarrow> highest_bit n < m \<Longrightarrow> highest_bit (w mod n) < m"    
    by (meson highest_bit_mono mod_le_divisor order_le_less_trans) 
    
  lemma highest_bit_mod_leI: "n>0 \<Longrightarrow> highest_bit n \<le> m \<Longrightarrow> highest_bit (w mod n) \<le> m"    
    by (meson highest_bit_mono mod_le_divisor order_subst2)
        
  find_theorems lower_bits  
    
  lemma p2_high_times_low_bound_aux: 
    "highest_bit w \<le> l \<Longrightarrow> 2^l\<le>k \<Longrightarrow> 2 ^ (l - highest_bit w) * lower_bits w < k"
    by (smt (verit, best) diff_diff_cancel diff_le_self dual_order.trans less_le_not_le lower_bits_upper nat_less_power_trans)
  
  
  
  lemma p2_times_lower_bits_bound:
    assumes MNZ: "m\<noteq>0"
    assumes L: "2^n * 2^highest_bit m \<le> k"
    shows "2 ^ (n - x) * lower_bits (w mod m) < k"  
  proof -
    have "2 ^ (n - x) * lower_bits (w mod m) \<le> 2^n * lower_bits (w mod m)" by simp
    also note lower_bits_upper
    also have "highest_bit (w mod m) \<le> highest_bit m" using MNZ highest_bit_mono by force
    also note L
    finally show ?thesis by simp 
  qed
  
  find_theorems exponent float_of_fp32

    
  definition "is_normal_fp32n w \<equiv> is_normal (float_of_fp32 (word_of_nat (nat_of_integer w)))"
    
  schematic_goal is_normal_fp32_code[code]: 
    defines "TAG \<equiv> \<lambda>x. x"
    shows "is_normal_fp32n w = TAG ?foo"
    unfolding is_normal_fp32n_def
    unfolding FP32.FoW_components is_normal_def emax_def shiftr_eq_div[symmetric] 
      mod_2p_is_mask unsigned_minus_1_eq_mask
      unat_of_nat
    apply (simp add: mask_shift_mask_simp)
    by (simp add: TAG_def)

  definition "is_denormal_fp32n w \<equiv> is_denormal (float_of_fp32 (word_of_nat (nat_of_integer w)))"
    
  schematic_goal is_denormal_fp32_code[code]: 
    defines "TAG \<equiv> \<lambda>x. x"
    shows "is_denormal_fp32n w = TAG ?foo"
    unfolding is_denormal_fp32n_def FP32.FoW_components is_denormal_def emax_def shiftr_eq_div[symmetric] 
      mod_2p_is_mask unsigned_minus_1_eq_mask
      unat_of_nat
    apply (simp add: mask_shift_mask_simp)
    by (simp add: TAG_def)
    
  definition "is_infinity_fp32n w \<equiv> is_infinity (float_of_fp32 (word_of_nat (nat_of_integer w)))"
    
  schematic_goal is_infinity_fp32_code[code]: 
    defines "TAG \<equiv> \<lambda>x. x"
    shows "is_infinity_fp32n w = TAG ?foo"
    unfolding is_infinity_fp32n_def FP32.FoW_components is_infinity_def emax_def shiftr_eq_div[symmetric] 
      mod_2p_is_mask unsigned_minus_1_eq_mask
      unat_of_nat
    apply (simp add: mask_shift_mask_simp)
    by (simp add: TAG_def)
    
  definition "is_zero_fp32n w \<equiv> is_zero (float_of_fp32 (word_of_nat (nat_of_integer w)))"
    
  schematic_goal is_zero_fp32_code[code]: 
    defines "TAG \<equiv> \<lambda>x. x"
    shows "is_zero_fp32n w = TAG ?foo"
    unfolding is_zero_fp32n_def FP32.FoW_components is_zero_def emax_def shiftr_eq_div[symmetric] 
      mod_2p_is_mask unsigned_minus_1_eq_mask
      unat_of_nat
    apply (simp add: mask_shift_mask_simp) (* TODO: Optimize that further! *)
    by (simp add: TAG_def)

  definition "is_nan_fp32n w \<equiv> is_nan (float_of_fp32 (word_of_nat (nat_of_integer w)))"
    
  schematic_goal is_nan_fp32_code[code]: 
    defines "TAG \<equiv> \<lambda>x. x"
    shows "is_nan_fp32n w = TAG ?foo"
    unfolding is_nan_fp32n_def FP32.FoW_components is_nan_def emax_def shiftr_eq_div[symmetric] 
      mod_2p_is_mask unsigned_minus_1_eq_mask
      unat_of_nat
    apply (simp add: mask_shift_mask_simp)
    by (simp add: TAG_def)
    
  lemmas fp32_of_nat_sel_defs = is_normal_fp32n_def is_denormal_fp32n_def is_infinity_fp32n_def is_zero_fp32n_def is_nan_fp32n_def
        
  
  lemma bias_eq_mask: "bias (TYPE(('e,'f) float)) = mask (LENGTH('e)-1)"
    unfolding bias_def mask_eq_exp_minus_1 by simp
  
  lemma emax_eq_mask: "emax (TYPE(('e,'f) float)) = mask (LENGTH('e))"
    unfolding emax_def
    by (simp add: unsigned_minus_1_eq_mask)
    
    
  definition "fp32n_fraction x \<equiv> and (nat_of_integer x) (mask 23)"  
  definition "fp32n_sign x \<equiv> and (nat_of_integer x) (mask 32) >> 31"
  definition "fp32_exponent x \<equiv> and (nat_of_integer x >> 23) (mask 8)"  

    
  lemma fp32n_sign_geZ_conv: "fp32n_sign i > 0 \<Longrightarrow> fp32n_sign i = 1"
    unfolding fp32n_sign_def
    apply (rule bit_select_cases[of 32 31 "nat_of_integer i"])
    by auto
  
  definition [code_unfold]: "fext_int_32_64' x \<equiv> integer_of_nat (
    if is_normal_fp32n x then 
        (fp32n_sign x << 63) 
      + (fp32_exponent x << 52) + 0x3800000000000000
      + (fp32n_fraction x << 29)
    else if is_denormal_fp32n x then 
        (fp32n_sign x << 63) 
      + (lower_bits (fp32n_fraction x) << 52 - highest_bit (fp32n_fraction x))
      + (0x36A0000000000000 + (highest_bit (fp32n_fraction x) << 52))
    else if is_infinity_fp32n x then 
        (fp32n_sign x << 63) 
      + 0x7FF0000000000000
    else if is_zero_fp32n x then 
      (fp32n_sign x << 63) 
    else 
        (fp32n_sign x << 63) 
      + 0x7FF0000000000000
      + (fp32n_fraction x << 29)
    )"
  
  
  lemma fext_int_32_64'_eq[code]:
    shows "fext_int_32_64 x = fext_int_32_64' x"
    unfolding fext_int_32_64_def fext_word_32_64_def float_extend_32_64_code FP32.FoW_components 
      integer_of_word_def word_of_integer_def comp_def
    unfolding FP64.unat_WoF_alt 
    unfolding 
      if_distrib[of fraction] let_distrib[of fraction]
      if_distrib[of exponent] let_distrib[of exponent]
      if_distrib[of sign] Let_def
    apply (repeat_all_new_fwd \<open>determ \<open>subst Abs_float'_parts_bounds\<close>\<close>; 
      (simp add: unat_div_bound_aux bias_def highest_bit_mod_lessI compute_highest_bit
            add: emax_def unat_minus_one_word p2_high_times_low_bound_aux highest_bit_mod_leI
      ; fail)?)
    unfolding fp32_of_nat_sel_defs[symmetric]
    
    unfolding emax_def shiftr_eq_div[symmetric] mod_2p_is_mask shiftl_t2n'[symmetric] t2n_shiftl_conv
      unat_of_nat unat_minus_one_word
    
    apply (simp split del: if_split cong: if_cong add: mask_shift_mask_simp bias_eq_mask emax_eq_mask)  
    
    unfolding if_distrib[of "\<lambda>x. x << _"]
    
    apply (simp split del: if_split cong: if_cong flip: fp32n_fraction_def fp32n_sign_def fp32_exponent_def)
    
    apply (simp split del: if_split cong: if_cong add: mask_eq_exp_minus_1 word_shiftl_add_distrib')
    
    unfolding fext_int_32_64'_def 
    
    apply (rule arg_cong[where f=integer_of_nat])
    
    apply (auto simp: fp32n_sign_geZ_conv)
    done
    
    
  export_code fext_int_32_64 in SML module_name LLVM_Extend_Float_Double

  subsection \<open>Reflecting into Isabelle-ML environment\<close>
  text \<open>We reflect the verified conversion procedure into Isabelle's ML environment,
    such that it can be used from within the LLVM code generator\<close>
      
  code_reflect LLVM_Extend_Float_Double functions
    fext_int_32_64
  
  ML_val \<open>LLVM_Extend_Float_Double.fext_int_32_64\<close>

  text \<open>Correctness theorem:\<close>
  thm fext_int_32_64_correct
  
  ML_val \<open>
    Word32.toInt (Word32.fromInt (~1))
  
  \<close>
  

end
