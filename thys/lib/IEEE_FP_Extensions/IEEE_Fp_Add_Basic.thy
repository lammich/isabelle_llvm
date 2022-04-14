section \<open>Basic Lemmas for Floating Point Reasoning\<close>
theory IEEE_Fp_Add_Basic
imports "../IEEE_Floating_Point/Conversion_IEEE_Float" "HOL-Library.Rewrite" "HOL-Library.Extended_Real"
begin

  no_notation IEEE.plus_infinity ("\<infinity>")

  instantiation float :: (type,type)infinity
  begin
    definition "infinity_float = plus_infinity"
    instance by standard
  end

  lemma plus_infinity_conv[simp]: "plus_infinity = \<infinity>" unfolding infinity_float_def ..


  subsection \<open>Bounds\<close>  
  lemma fraction_upper_bound: "fraction (a::('a,'b) float) < 2^LENGTH('b)"
    apply transfer
    by auto

  lemma exponent_upper_bound: "exponent f < 2 ^ LENGTH('e)" for f :: "('e,'f) float" 
    apply transfer
    by auto
    
  lemma emax_gt1_iff_e_gt1[simp]: "Suc 0 < emax TYPE(('e, 'f) float) \<longleftrightarrow> LENGTH('e)>1"
    apply (clarsimp simp: emax_def)
    by (smt (z3) Suc_lessI len_gt_0 mask_1 max_word_mask sint_n1 unat_1 unat_eq_1 unat_max_word_pos word_sint_1)
  
  lemma emax_ge1[simp]: "emax TYPE(('e, 'f) float) \<ge> Suc 0"  
    apply (clarsimp simp: emax_def)
    by (meson le_zero_eq max_word_not_0 not_less_eq_eq unat_eq_zero)

  lemma emax_eq1_iff[simp]: "emax TYPE(('e, 'f) float) = Suc 0 \<longleftrightarrow> LENGTH('e) = 1"  
    apply (clarsimp simp: emax_def)
    by (simp add: unat_eq_1)
    
  lemma emax_leq1_iff[simp]: "emax TYPE(('e, 'f) float) \<le> Suc 0 \<longleftrightarrow> LENGTH('e) = 1"  
    apply (clarsimp simp: emax_def)
    by (smt (z3) leD le_SucE le_numeral_extra(4) sint_minus1 unat_1 unat_eq_1 unat_max_word_pos word_sint_1)

  lemma exp_le_emax[simp]: 
    "exponent f \<le> emax TYPE(('e, 'f) float)" for f :: "('e, 'f) float" 
    apply transfer
    apply (auto simp: emax_def)
    using word_le_nat_alt by blast

  subsection \<open>Lemmas about numbers\<close>

  lemma pow2N_le1_conv[simp]: "2^n \<le> Suc 0 \<longleftrightarrow> n<1"
    using le_eq_less_or_eq by force 

  lemma degenerate_word_ne1[simp]: "a\<noteq>1 \<longleftrightarrow> a=0" for a :: "1 word"
    using degenerate_word by force

  lemma nat_gtZ_or_Z[simp]: "0<n \<or> n=0" for n :: nat by auto
  
  lemma gt_Z_le_1_conv[simp]: "0<n \<Longrightarrow> n\<le>Suc 0 \<longleftrightarrow> n=Suc 0" by auto
  
  lemma two_plen_gt1[simp]: "Suc 0 < 2 ^ LENGTH('f::len)"
    by (metis One_nat_def unat_lt2p unsigned_1)


  lemma fp_frac_part_lt2: "1 + real (2 ^ F - Suc 0) / 2 ^ F < 2" by simp  
        
  lemma fp_pred_exp_less: "2 ^ (e - Suc 0) * (1 + real (2 ^ F - Suc 0) / 2 ^ F) < 2 ^ e" if "e>0" 
    using that by (cases e) auto

  lemma fp_val_exp_less_is_less:
    fixes f :: "('e,'f) float"
    assumes "e<e'"
    shows "2 ^ e * (1 + real (fraction f) / 2 ^ LENGTH('f)) / 2 ^ B
         < 2 ^ e' * (1 + real (fraction f') / 2 ^ LENGTH('f)) / 2 ^ B"    
         (is "?l < ?r")
  proof -
    have "(1 + real (fraction f) / 2 ^ LENGTH('f)) < 2"
      by (simp add: fraction_upper_bound) 
    hence "?l < 2^(e+1)/2^B"
      by (simp add: divide_strict_right_mono)
    also have "\<dots> \<le> 2^e'/2^B" using assms
      by (smt (verit, ccfv_SIG) Suc_leI add.commute divide_right_mono exp_less plus_1_eq_Suc zero_le_power)
    also have "\<dots> \<le> ?r"
      by (simp add: divide_le_cancel)  
    finally show ?thesis .   
  qed
      
  lemma fp_val_denorm_less_norm: "real (fraction f) * 2 < 2 ^ e * 2 ^ LENGTH('f)" if "0<e"
    for f :: "('e,'f) float"
  proof -
    have "real (fraction f) < 2^LENGTH('f)"
      by (simp add: fraction_upper_bound)
    hence "real (fraction f) * 2 < 2*2^LENGTH('f)" by linarith
    also have "(2::real)\<le>2^e" using \<open>0<e\<close> by (cases e) auto
    hence "(2::real)*2^LENGTH('f) \<le> 2^e * 2^LENGTH('f)" by auto
    finally show ?thesis .
  qed
        
  subsection \<open>Classification\<close>  
  
  
    lemma float_cases':
      obtains "  is_nan f" "\<not> is_normal f" "\<not> is_denormal f" "\<not> is_zero f" "\<not> is_infinity f"
            | "\<not> is_nan f" "  is_normal f" "\<not> is_denormal f" "\<not> is_zero f" "\<not> is_infinity f"
            | "\<not> is_nan f" "\<not> is_normal f" "  is_denormal f" "\<not> is_zero f" "\<not> is_infinity f"
            | "\<not> is_nan f" "\<not> is_normal f" "\<not> is_denormal f" "  is_zero f" "\<not> is_infinity f"
            | "\<not> is_nan f" "\<not> is_normal f" "\<not> is_denormal f" "\<not> is_zero f" "  is_infinity f"
      by (metis float_cases float_distinct normal_imp_not_zero)
    
    lemma float_cases_eqs:
      obtains 
        "f=\<infinity>" 
      | "f=-\<infinity>" 
      | "f=0" 
      | "f=-0" 
      | "is_nan f" "\<not>is_finite f" "\<not>is_zero f" "\<not>is_infinity f"
      | "is_finite f" "\<not>is_zero f" "\<not>is_infinity f" "\<not>is_nan f"
      by (metis float_cases_finite infinity_float_def is_infinity_cases is_zero_cases nan_not_finite)
      
  
    lemma normalize_sign[simp]:
      "sign f \<noteq> 0 \<longleftrightarrow> sign f = Suc 0"
      "sign f \<noteq> Suc 0 \<longleftrightarrow> sign f = 0"
      by (cases f rule: sign_cases; simp)+
  
      
      
      
    subsubsection \<open>Valueizing NaN\<close>
    text \<open>Make all NaNs a value, tagged by a constant\<close>
    definition "the_nan x \<equiv> if is_nan x then x else some_nan"
    
    lemma ex_nan: "\<exists>x. is_nan x"  
      unfolding is_nan_def
      apply transfer
      apply (auto simp: emax_def)
      using unat_max_word_pos by blast
      
    lemma some_nan_is_nan[simp]: "is_nan some_nan"
      unfolding some_nan_def 
      using someI_ex[OF ex_nan] .
    
    lemma the_nan_is_nan[simp, intro!]: "is_nan (the_nan x)"
      unfolding the_nan_def by auto
  
    lemma the_nan_cong[cong]: "the_nan x = the_nan x" by simp
    
    lemma some_nan_conv[simp]: "some_nan = the_nan some_nan"
      unfolding the_nan_def by simp
        
    lemma is_nanE[elim!]: assumes "is_nan x" obtains xx where "x = the_nan xx"
      using assms unfolding the_nan_def by metis

  
    subsubsection \<open>Floating point selectors\<close>        
    lemmas float_sel_simps[simp] = 
      infinity_simps
      zero_simps
      topfloat_simps
      bottomfloat_simps
      
    lemma the_nan_simps[simp]: 
      "IEEE.exponent (the_nan x::('e, 'f) float) = emax TYPE(('e, 'f) float)"      
      "IEEE.fraction (the_nan x) \<noteq> 0"
      subgoal by (meson is_nan_def the_nan_is_nan)
      subgoal by (meson is_nan_def the_nan_is_nan)
      done
      
    lemma is_infinity_inf[simp,intro!]: "is_infinity \<infinity>"
      by (simp add: float_defs(2) flip: plus_infinity_conv) 
    
    
  subsubsection \<open>Conmponent-Wise Equality\<close>
  lemma float_eq_conv: "a=b \<longleftrightarrow> sign a = sign b \<and> fraction a = fraction b \<and> exponent a = exponent b"
    apply (transfer)
    by (auto simp flip: word_unat_eq_iff)
    

  lemma infinity_simps'[simp]:
    "sign (\<infinity>::('e, 'f)float) = 0"
    "sign (-\<infinity>::('e, 'f)float) = 1"
    "exponent (\<infinity>::('e, 'f)float) = emax TYPE(('e, 'f)float)"
    "exponent (-\<infinity>::('e, 'f)float) = emax TYPE(('e, 'f)float)"
    "fraction (\<infinity>::('e, 'f)float) = 0"
    "fraction (-\<infinity>::('e, 'f)float) = 0"
    by (simp_all flip: plus_infinity_conv)
    
    
  lemma float_class_consts[simp, intro!]:
    "\<not>is_infinity (the_nan x)"
    (* "is_nan       (the_nan x)" *)
    "\<not>is_zero     (the_nan x)"
    "\<not>is_finite   (the_nan x)"
    "\<not>is_normal   (the_nan x)"
    "\<not>is_denormal (the_nan x)"
    
    "is_infinity  \<infinity>"
    "\<not>is_nan      \<infinity>"
    "\<not>is_zero     \<infinity>"
    "\<not>is_finite   \<infinity>"
    "\<not>is_normal   \<infinity>"
    "\<not>is_denormal \<infinity>"

    "is_infinity  (-\<infinity>)"
    "\<not>is_nan      (-\<infinity>)"
    "\<not>is_zero     (-\<infinity>)"
    "\<not>is_finite   (-\<infinity>)"
    "\<not>is_normal   (-\<infinity>)"
    "\<not>is_denormal (-\<infinity>)"

    "\<not>is_infinity 0"
    "\<not>is_nan      0"
    "is_zero      0"
    " is_finite   0"
    "\<not>is_normal   0"
    "\<not>is_denormal 0"
        
    "\<not>is_infinity (-0)"
    "\<not>is_nan      (-0)"
    " is_zero     (-0)"
    " is_finite   (-0)"
    "\<not>is_normal   (-0)"
    "\<not>is_denormal (-0)"
    
    "\<not>is_infinity topfloat"                    
    "\<not>is_nan      topfloat"
    "\<not>is_zero     topfloat"
    " is_finite   topfloat"
    " is_normal   (topfloat :: ('e,'f) float) \<longleftrightarrow> LENGTH('e)>1"
    " is_denormal (topfloat:: ('e,'f) float) \<longleftrightarrow> LENGTH('e) = 1"
    
    "\<not>is_infinity bottomfloat"                    
    "\<not>is_nan      bottomfloat"
    "\<not>is_zero     bottomfloat"
    " is_finite   bottomfloat"
    " is_normal   (bottomfloat:: ('e,'f) float) \<longleftrightarrow> LENGTH('e)>1"
    " is_denormal (bottomfloat:: ('e,'f) float) \<longleftrightarrow> LENGTH('e) = 1"
    
    apply (simp_all add: float_defs flip: plus_infinity_conv)
    apply (metis One_nat_def Suc_pred' emax_pos(1) n_not_Suc_n)
    apply (metis Suc_lessI len_gt_0)
    apply (metis One_nat_def Suc_pred' emax_pos(1) n_not_Suc_n)
    apply (metis Suc_lessI len_gt_0)
    done
  
  (*lemmas [simp, intro!] = finite_topfloat  *)
  
  (* (the_nan x) \<infinity> -\<infinity> 0 -0 topfloat -topfloat *)
  lemma float_ineqs[simp, symmetric, simp]:
    "the_nan x \<noteq> \<infinity>"
    "the_nan x \<noteq> -\<infinity>"
    "the_nan x \<noteq> 0"
    "the_nan x \<noteq> -0"
    "the_nan x \<noteq> topfloat"
    "the_nan x \<noteq> -topfloat"
        
    "\<infinity> \<noteq> (0 :: (_,_) float)"
    "\<infinity> \<noteq> (-0 :: (_,_) float)"
    "\<infinity> \<noteq> topfloat"
    "\<infinity> \<noteq> -topfloat"
    
    "-\<infinity> \<noteq> (0:: (_,_) float)"
    "-\<infinity> \<noteq> topfloat"
    
    "0 \<noteq> topfloat"
    "0 \<noteq> -topfloat"
    
    "-0 \<noteq> topfloat"
    
    apply safe
    apply (
      drule arg_cong[where f=is_finite] arg_cong[where f=is_nan] arg_cong[where f=is_zero] arg_cong[where f=sign]; 
      simp; fail)+
    done
    
            
  subsection \<open>Almost-Injectivity of \<^const>\<open>valof\<close>\<close>  
        
  lemma valof_nonzero_injective:
    fixes x\<^sub>1 x\<^sub>2 :: "('e,'f) float"
    assumes FIN: "is_finite x\<^sub>1" "is_finite x\<^sub>2" and NZ: "\<not>(is_zero x\<^sub>1 \<and> is_zero x\<^sub>2)" 
    assumes VEQ: "valof x\<^sub>1 = valof x\<^sub>2"
    shows "x\<^sub>1=x\<^sub>2"
  proof -
    define s\<^sub>1 where "s\<^sub>1 = sign x\<^sub>1"
    define s\<^sub>2 where "s\<^sub>2 = sign x\<^sub>2"
  
    define e\<^sub>1 where "e\<^sub>1 = exponent x\<^sub>1"
    define e\<^sub>2 where "e\<^sub>2 = exponent x\<^sub>2"
    
    define f\<^sub>1 where "f\<^sub>1 = real (fraction x\<^sub>1)"
    define f\<^sub>2 where "f\<^sub>2 = real (fraction x\<^sub>2)"
    
    define B where "B = bias TYPE(('e, 'f) IEEE.float)"
    define F where "F = (2::real)^LENGTH('f)"
    
    note defs = s\<^sub>1_def s\<^sub>2_def e\<^sub>1_def e\<^sub>2_def f\<^sub>1_def f\<^sub>2_def B_def F_def
  
    have aux1: "fraction x\<^sub>1 = fraction x\<^sub>2 \<longleftrightarrow> f\<^sub>1=f\<^sub>2" unfolding defs by simp
      
    text \<open>Bounds\<close>
    have [simp]: "F\<noteq>0" unfolding defs by simp
    
    have NZ': "\<not>(e\<^sub>1=0 \<and> f\<^sub>1=0 \<and> e\<^sub>2=0 \<and> f\<^sub>2=0)" 
      using NZ
      unfolding defs is_zero_def
      by (auto simp: )
    
    have f_bounds: "f\<^sub>1\<in>{0..<F}" "f\<^sub>2\<in>{0..<F}" 
      unfolding defs by (auto simp: fraction_upper_bound)
    
    note [intro] = f_bounds[simplified]
      
    have s_bounds: "s\<^sub>1\<in>{0,1}" "s\<^sub>2\<in>{0,1}"  
      unfolding defs using sign_cases by auto
    
    have normal_pos:
      "0 < 2 ^ e\<^sub>1 * (1 + f\<^sub>1 / F)" 
      "0 < 2 ^ e\<^sub>2 * (1 + f\<^sub>2 / F)" 
      using f_bounds apply -
      apply (smt (verit) atLeastLessThan_iff divide_eq_0_iff divide_pos_pos mult_pos_pos power_eq_0_iff zero_le_power) 
      by (smt (verit, best) atLeastLessThan_iff divide_nonneg_nonneg zero_less_mult_iff zero_less_power)
      
    have nf_bounds: "(1 + f\<^sub>1 / F) \<in> {1..<2}" "(1 + f\<^sub>2 / F) \<in> {1..<2}" 
      using f_bounds by auto
      
      
    have normal_eq_aux: "f\<^sub>1 = f\<^sub>2 \<and> e\<^sub>1 = e\<^sub>2" if "2 ^ e\<^sub>1 * (1 + f\<^sub>1 / F) = 2 ^ e\<^sub>2 * (1 + f\<^sub>2 / F)"  
    proof -
      consider "e\<^sub>1=e\<^sub>2" | "e\<^sub>1<e\<^sub>2" | "e\<^sub>1>e\<^sub>2" by linarith
      then show ?thesis proof cases
        case 1 thus ?thesis using that by simp
      next
        case 2 then obtain d where [simp]: "e\<^sub>2=Suc (e\<^sub>1+d)"
          using less_natE by blast
      
        from that have False  
          using nf_bounds
          apply (clarsimp simp:)
          by (smt (verit, ccfv_SIG) "2" divide_less_eq le_divide_eq_1_pos nonzero_mult_div_cancel_left not_less_eq plus_1_eq_Suc power_add power_one_right power_strict_increasing_iff that zero_less_power)
        thus ?thesis ..  
      next
        case 3 then obtain d where [simp]: "e\<^sub>1=Suc (e\<^sub>2+d)"
          using less_natE by blast
      
        from that have False  
          using nf_bounds
          apply (clarsimp simp:)
          by (smt (verit, ccfv_SIG) "3" divide_less_eq le_divide_eq_1_pos nonzero_mult_div_cancel_left not_less_eq plus_1_eq_Suc power_add power_one_right power_strict_increasing_iff that zero_less_power)
        thus ?thesis ..  
      qed    
    qed
      
    have sign_eqI: "s\<^sub>1=s\<^sub>2 \<and> a=b" if "(-1)^s\<^sub>1 * a = (-1)^s\<^sub>2 * b" "a\<ge>0" "b\<ge>0" "a>0 \<or> b>0" for a b :: real
      using that s_bounds by auto
      
      
    have G1: "\<lbrakk>e\<^sub>1=0; e\<^sub>2=0; (- 1) ^ s\<^sub>1 * f\<^sub>1 = (- 1) ^ s\<^sub>2 * f\<^sub>2\<rbrakk> \<Longrightarrow> s\<^sub>1 = s\<^sub>2 \<and> f\<^sub>1 = f\<^sub>2"  
      apply (drule sign_eqI)
      using NZ' f_bounds by auto
    
    have G23_aux1: "2 * f / (2 ^ B * F) < 2/2^B" if B: "f\<in>{0..<F}" for f
    proof -
      have "2 * f / (2 ^ B * F) = 2 * (f/F) / 2^B" by simp
      also have "f/F < 1" using B by simp
      finally show ?thesis by (simp add: divide_strict_right_mono)
    qed
  
    have G23_aux2: "2 ^ e * (1 + f / F) / 2 ^ B \<ge> 2/2^B" if B: "f\<in>{0..<F}" "0 < e" for e :: nat and f :: real
    proof -
      have [simp]: "a/b \<le> c/b \<longleftrightarrow> a\<le>c" if "b>0" for a b c :: real
        using divide_le_cancel that by auto
      
      have "(2::real)^e \<ge> 2" using B
        by (metis One_nat_def Suc_leI exp_less power_one_right) 
      moreover have "(1 + f / F) / 2 ^ B \<ge> 1/2^B"
        using B by (clarsimp)
      ultimately show ?thesis
        by (smt (verit, ccfv_SIG) divide_le_cancel le_divide_eq_1_pos nonzero_mult_div_cancel_left zero_le_power)   
    qed    
      
    have mult_div_assoc: "a*b/c = a*(b/c)" for a b c :: real by simp
    
    have G2: "\<lbrakk>0 < e\<^sub>1; (- 1) ^ s\<^sub>1 * 2 ^ e\<^sub>1 * (1 + f\<^sub>1 / F) / 2 ^ B = (- 1) ^ s\<^sub>2 * 2 * f\<^sub>2 / (2 ^ B * F)\<rbrakk> \<Longrightarrow> False"
      apply (simp only: mult.assoc mult_div_assoc)
      apply (drule sign_eqI)
      subgoal using normal_pos f_bounds by simp
      subgoal using normal_pos f_bounds by simp
      subgoal using normal_pos f_bounds by simp
      apply clarsimp
      apply (drule G23_aux2[OF \<open>f\<^sub>1\<in>{0..<F}\<close>])
      using G23_aux1[OF \<open>f\<^sub>2\<in>{0..<F}\<close>]
      by simp
    
    have G3: "\<lbrakk>0 < e\<^sub>2; (- 1) ^ s\<^sub>1 * 2 * f\<^sub>1 / (2 ^ B * F) = (- 1) ^ s\<^sub>2 * 2 ^ e\<^sub>2 * (1 + f\<^sub>2 / F) / 2 ^ B\<rbrakk> \<Longrightarrow> False"
      apply (simp only: mult.assoc mult_div_assoc)
      apply (drule sign_eqI)
      subgoal using normal_pos f_bounds by simp
      subgoal using normal_pos f_bounds by simp
      subgoal using normal_pos f_bounds by simp
      apply clarsimp
      apply (drule G23_aux2[OF \<open>f\<^sub>2\<in>{0..<F}\<close>])
      using G23_aux1[OF \<open>f\<^sub>1\<in>{0..<F}\<close>]
      by simp
      
    have G4: "\<lbrakk>(- 1) ^ s\<^sub>1 * 2 ^ e\<^sub>1 * (1 + f\<^sub>1 / F) = (- 1) ^ s\<^sub>2 * 2 ^ e\<^sub>2 * (1 + f\<^sub>2 / F)\<rbrakk> \<Longrightarrow> s\<^sub>1 = s\<^sub>2 \<and> f\<^sub>1 = f\<^sub>2 \<and> e\<^sub>1 = e\<^sub>2"  
      apply (simp only: mult.assoc)
      apply (drule sign_eqI)
      using normal_pos
      apply (auto dest: normal_eq_aux)
      done
    
    
      
    from VEQ show ?thesis
      apply (simp add: valof_eq is_zero_def float_eq_conv aux1 flip: defs cong: if_cong)
      apply (simp split: if_splits)
      apply (rule G1; simp)
      apply (rule G2; simp)
      apply (rule G3; simp)
      apply (rule G4; simp)
      done
      
  qed    
    
  text \<open> Finite floating point numbers are mapped uniquely to reals,
    except for zero and negative zero.
  \<close>
  theorem valof_almost_injective: 
    fixes x\<^sub>1 x\<^sub>2 :: "('e,'f) float"
    assumes FIN: "is_finite x\<^sub>1" "is_finite x\<^sub>2" 
    assumes VEQ: "valof x\<^sub>1 = valof x\<^sub>2"
    shows "x\<^sub>1=x\<^sub>2 \<or> (x\<^sub>1=0 \<and> x\<^sub>2=-0) \<or> (x\<^sub>1=-0 \<and> x\<^sub>2=0)"
    using assms 
    apply (cases "\<not>(is_zero x\<^sub>1 \<and> is_zero x\<^sub>2)")
    apply (drule (3) valof_nonzero_injective; simp)
    by (auto elim!: is_zero_cases)
  
    
  subsection \<open>Conversion to \<open>val_of\<close>\<close>  

  named_theorems fp_to_val

  context
    fixes f :: "('e,'f) float"
    assumes FIN: "is_finite f"
  begin
      
    lemma is_zero_iff_valof0[fp_to_val]: "is_zero f \<longleftrightarrow> valof f = 0"
      by (metis FIN float_zero1 is_finite_def val_zero valof_nonzero_injective)
  
    lemma sign_pos_iff_valof[fp_to_val]: "sign f = 0 \<longleftrightarrow> f\<noteq>-0 \<and> valof f \<ge> 0"  
      apply rule
      subgoal by (auto simp: valof_eq)
      subgoal 
        apply (cases f rule: sign_cases)
        apply (auto 
          simp: valof_eq field_simps float_eq_conv
          split: if_splits)
        by (smt (z3) mult_nonneg_nonneg of_nat_0_le_iff power_add zero_less_power)  
      done

    lemma sign_neg_iff_valof[fp_to_val]: "sign f = Suc 0 \<longleftrightarrow> f\<noteq>0 \<and> valof f \<le> 0"
      apply rule
      subgoal by (auto simp: valof_eq)
      subgoal 
        apply (cases f rule: sign_cases)
        apply (auto 
          simp: valof_eq field_simps float_eq_conv
          split: if_splits)
        by (smt (z3) mult_nonneg_nonneg of_nat_0_le_iff power_add zero_less_power)  
      done
                
  end  
    
  subsection \<open>Component-Wise Floating Point Operations\<close>  

  definition "Abs_float' s e f \<equiv> Abs_float (of_nat s, of_nat e, of_nat f)"
  
  lemma Abs_float'_parts[simp]:
    "sign (Abs_float' s e f :: ('e,'f) float) = s mod 2"
    "exponent (Abs_float' s e f :: ('e,'f) float) = e mod 2^LENGTH('e)"
    "fraction (Abs_float' s e f :: ('e,'f) float) = f mod 2^LENGTH('f)"
    unfolding Abs_float'_def
    apply (all transfer')
    by (simp_all add: unat_of_nat)

  subsubsection \<open>Compare\<close>  
  definition "fcc_le_samesign f f' \<longleftrightarrow> (
    if exponent f < exponent f' then True 
    else if exponent f = exponent f' then fraction f \<le> fraction f'
    else False
  )"
  
  definition "fcc_le f f' \<longleftrightarrow> (
    if is_zero f \<and> is_zero f' then True
    else if sign f \<noteq> sign f' then sign f = 1 \<and> sign f'=0
    else if sign f = 0 then fcc_le_samesign f f'
    else fcc_le_samesign f' f
  )"
  
  definition "fcc_lt_samesign f f' \<longleftrightarrow> (
    if exponent f < exponent f' then True 
    else if exponent f = exponent f' then fraction f < fraction f'
    else False
  )"
  
  definition "fcc_lt f f' \<longleftrightarrow> (
    if is_zero f \<and> is_zero f' then False
    else if sign f \<noteq> sign f' then sign f = 1 \<and> sign f'=0
    else if sign f = 0 then fcc_lt_samesign f f'
    else fcc_lt_samesign f' f
  )"
  
  
  lemma fcc_le_cases:
    obtains 
      "is_zero f" "is_zero f'"
    | "\<not>(is_zero f \<and> is_zero f')" "sign f \<noteq> sign f'" 
    | "\<not>(is_zero f \<and> is_zero f')" "sign f = 0" "sign f'=0"
    | "\<not>(is_zero f \<and> is_zero f')" "sign f = 1" "sign f'=1"
    by (metis sign_cases)

  context begin
    private lemma aux_le_ee_conv:
      fixes f f' :: "('e,'f) float"
      assumes [simp]: "sign f = sign f'" "exponent f = exponent f'"
      shows "valof f \<le> valof f' \<longleftrightarrow> (
        if sign f'=0 then fraction f \<le> fraction f'
        else fraction f' \<le> fraction f)"
      apply (cases f' rule: sign_cases)  
      apply (auto simp add: valof_eq field_simps)
      done

    private lemma aux_lt_ee_conv:
      fixes f f' :: "('e,'f) float"
      assumes [simp]: "sign f = sign f'" "exponent f = exponent f'"
      shows "valof f < valof f' \<longleftrightarrow> (
        if sign f'=0 then fraction f < fraction f'
        else fraction f' < fraction f)"
      apply (cases f' rule: sign_cases)  
      apply (auto simp add: valof_eq field_simps)
      done
      
  
  
    private lemma aux_pos_lt_eltI:
      fixes f f' :: "('e,'f) float"
      assumes [simp]: "sign f = 0" "sign f' = 0" 
      assumes ELT: "exponent f < exponent f'"
      shows "valof f < valof f'"
      using ELT
      supply [simp del] = zero_le_power2 power2_less_0
      apply (auto simp add: valof_eq fp_val_exp_less_is_less)
      apply (auto simp add: valof_eq field_simps zero_compare_simps fp_val_denorm_less_norm) []
      done
    
    private lemma aux_neg_lt_eltI:
      fixes f f' :: "('e,'f) float"
      assumes [simp]: "sign f = Suc 0" "sign f' = Suc 0" 
      assumes ELT: "exponent f < exponent f'"
      shows "valof f > valof f'"
      using ELT
      supply [simp del] = zero_le_power2 power2_less_0
      apply (auto simp add: valof_eq fp_val_exp_less_is_less)
      apply (auto simp add: valof_eq field_simps zero_compare_simps fp_val_denorm_less_norm) []
      done
        
          
        
    lemma fcc_le_valof:
      fixes f f' :: "('e,'f) float"
      assumes [simp]: "is_finite f" "is_finite f'"  
      shows "fcc_le f f' \<longleftrightarrow> valof f \<le> valof f'"
    proof (cases f f' rule: fcc_le_cases; clarsimp simp: fcc_le_def is_zero_iff_valof0)
      {
        assume ZERO: "valof f = 0 \<longrightarrow> valof f' \<noteq> 0"
        
        {
          assume SIGN: "sign f \<noteq> sign f'"
          show "(sign f = Suc 0 \<and> sign f' = 0) = (valof f \<le> valof f')"
            by (smt (z3) SIGN ZERO assms(1) assms(2) normalize_sign(2) sign_pos_iff_valof valof_zero(2))
        }
        
        {
          assume S: "sign f = 0" "sign f' = 0"
          show "fcc_le_samesign f f' = (valof f \<le> valof f')"
            apply (auto simp add: fcc_le_samesign_def S(1) S(2) aux_le_ee_conv aux_pos_lt_eltI[THEN less_imp_le])
            by (meson S(1) S(2) aux_pos_lt_eltI leD less_linear)
        
        }
        
        {
          assume S: "sign f = Suc 0" "sign f' = Suc 0"
          show "fcc_le_samesign f' f = (valof f \<le> valof f')"
            apply (auto simp add: fcc_le_samesign_def S(1) S(2) aux_le_ee_conv aux_neg_lt_eltI[THEN less_imp_le])
            by (meson S(1) S(2) aux_neg_lt_eltI leD less_linear)
            
        }
      }
    qed      
      
      
      
    lemma fcc_lt_valof:
      fixes f f' :: "('e,'f) float"
      assumes [simp]: "is_finite f" "is_finite f'"  
      shows "fcc_lt f f' \<longleftrightarrow> valof f < valof f'"
    proof (cases f f' rule: fcc_le_cases; clarsimp simp: fcc_lt_def is_zero_iff_valof0)
      {
        assume ZERO: "valof f = 0 \<longrightarrow> valof f' \<noteq> 0"
        
        {
          assume SIGN: "sign f \<noteq> sign f'"
          show "(sign f = Suc 0 \<and> sign f' = 0) = (valof f < valof f')"
            by (smt (z3) One_nat_def SIGN ZERO sign_cases valof_nonneg valof_nonpos)
        
        }
        
        {
          assume S: "sign f = 0" "sign f' = 0"
          show "fcc_lt_samesign f f' = (valof f < valof f')"
            apply (auto simp add: fcc_lt_samesign_def S(1) S(2) aux_lt_ee_conv aux_pos_lt_eltI)
            by (meson S(1) S(2) aux_pos_lt_eltI less_asym' less_linear)
        
        }
        
        {
          assume S: "sign f = Suc 0" "sign f' = Suc 0"
          show "fcc_lt_samesign f' f = (valof f < valof f')"
            apply (auto simp add: fcc_lt_samesign_def S(1) S(2) aux_lt_ee_conv aux_neg_lt_eltI)
            by (meson S(1) S(2) aux_neg_lt_eltI not_less_iff_gr_or_eq)
        }
      }
    qed      
    
  end    
  
subsection \<open>Basic FP-algebra\<close>  
  

lemma is_zero_alt: "is_zero x \<longleftrightarrow> x=0 \<or> x=-0"
  by (auto elim!: is_zero_cases)

lemma is_infinity_alt: "is_infinity x \<longleftrightarrow> x=\<infinity> \<or> x=-\<infinity>"
  by (auto elim!: is_infinity_cases)
  
lemma sign_convs[simp]: 
  "0 < sign x \<longleftrightarrow> sign x = 1" 
  "sign x\<noteq>0 \<longleftrightarrow> sign x = 1" 
  "sign x\<noteq>Suc 0 \<longleftrightarrow> sign x = 0" 
  subgoal by (metis neq0_conv sign_cases zero_neq_one)
  subgoal by (metis sign_cases zero_neq_one)
  subgoal by (metis One_nat_def sign_cases zero_neq_one)
  done

lemma valof_eq_zero_conv: "IEEE.is_finite a \<Longrightarrow> valof a = 0 \<longleftrightarrow> a=0 \<or> a=-0"  
  using valof_almost_injective by fastforce 


lemma float_eq_minus_minus_conv[simp]: "-a=-b \<longleftrightarrow> a=b" for a b :: "(_,_)float"
  by (metis minus_minus_float)

lemma float_neq_minus_self[simp, symmetric, simp]: "a \<noteq> -a" 
  for a :: "(_,_)float" 
  apply (metis float_neg_sign)
  done
  
lemma float_le_inf_simps[simp]:
  "-\<infinity> \<le> u \<longleftrightarrow> \<not>is_nan u"
  "\<infinity> \<le> u \<longleftrightarrow> u = \<infinity>"
  "u \<le> \<infinity> \<longleftrightarrow> \<not>is_nan u"
  "u \<le> -\<infinity> \<longleftrightarrow> u=-\<infinity>"
  subgoal unfolding float_defs by simp 
  subgoal by (auto simp: less_eq_float_def fle_def fcompare_def is_infinity_alt)
  subgoal unfolding float_defs by simp
  subgoal by (auto simp: less_eq_float_def fle_def fcompare_def is_infinity_alt)
  done
  
end
