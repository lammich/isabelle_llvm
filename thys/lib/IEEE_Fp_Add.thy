section \<open>Additional Floating-Point Properties\<close>
theory IEEE_Fp_Add
imports IEEE_Floating_Point.Conversion_IEEE_Float IEEE_Floating_Point.FP64
begin

  subsection \<open>Miscellaneous Lemmas\<close>

  
  lift_definition smallest_pos :: "('e,'f) float" is "(0,0,1)" .
  
  lemma smallest_pos_simps[simp]:
    "sign smallest_pos = 0"
    "exponent smallest_pos = 0"
    "fraction smallest_pos = 1"
    apply (transfer; simp)+
    done
  
      
  lemma [simp]: "is_denormal smallest_pos"
    by (simp add: is_denormal_def)
    
  lemma [simp]: "is_finite smallest_pos"
    by (simp add: is_finite_def)
  
  lemma [simp]: "\<not>is_zero smallest_pos"
    by (simp add: is_zero_def)
  
  lemma valof_smallest_pos: "valof (smallest_pos :: ('a,'b) float) =  2 / (2 ^ (2 ^ (LENGTH('a) - Suc 0) - Suc 0) * 2 ^ LENGTH('b))"
    apply transfer
    apply (auto simp: bias_def)
    done

  lemma valof_smallest_pos_pos: "0<valof smallest_pos" by (simp add: valof_smallest_pos)
  
  
  text \<open>Attain sup/inf lemmas for finite sets and linear orders\<close>
  lemma finite_attains_inf:
    fixes f :: "'a \<Rightarrow> 'b::linorder"
    assumes "finite s"
    assumes "s\<noteq>{}"
    shows "\<exists>x\<in>s. \<forall>y\<in>s. f x \<le> f y"
    using assms  
  proof induction
    case empty
    then show ?case by simp
  next
    case (insert x F)
    show ?case
    proof (cases "\<forall>y\<in>F. f x \<le> f y")
      case True thus ?thesis by blast
    next
      case False
      then obtain y where "y\<in>F" "f x > f y" by auto
      with insert.IH obtain x' where "x'\<in>F" "\<forall>y'\<in>F. f x' \<le> f y'" by blast
      with \<open>f x > f y\<close> show ?thesis by force
    qed  
  qed  
    
  lemma finite_attains_sup:
    fixes f :: "'a \<Rightarrow> 'b::linorder"
    assumes "finite s"
    assumes "s\<noteq>{}"
    shows "\<exists>x\<in>s. \<forall>y\<in>s. f y \<le> f x"
    using assms  
  proof induction
    case empty
    then show ?case by simp
  next
    case (insert x F)
    show ?case
    proof (cases "\<forall>y\<in>F. f x \<ge> f y")
      case True thus ?thesis by blast
    next
      case False
      then obtain y where "y\<in>F" "f x < f y" by auto
      with insert.IH obtain x' where "x'\<in>F" "\<forall>y'\<in>F. f x' \<ge> f y'" by blast
      with \<open>f x < f y\<close> show ?thesis by force
    qed  
  qed  
  


  context begin

    subsection \<open>Basic Classification Lemmas\<close>  
    private lemma conv_distinct_lemma1: "\<not>(a\<and>b) \<Longrightarrow> a \<Longrightarrow> \<not>b" by blast 
    private lemma conv_distinct_lemma2: "\<not>(a\<and>b) \<Longrightarrow> b \<Longrightarrow> \<not>a" by blast 
      
    private lemma mult_div_assoc: "a*b/c = a*(b/c)" for a b c :: real by simp  
    
    
    lemmas float_distinct' = 
      float_distinct[THEN conv_distinct_lemma1]  
      float_distinct[THEN conv_distinct_lemma2]
      finite_infinity
      finite_nan
      
    lemma float_eq_conv: "a=b \<longleftrightarrow> sign a = sign b \<and> fraction a = fraction b \<and> exponent a = exponent b"
      apply (transfer)
      by auto
    
    
    lemma fraction_upper_bound: "fraction (a::('a,'b) float) < 2^LENGTH('b)"
      apply transfer
      by auto
  
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
    
    lemma the_nan_is_nan: "is_nan (the_nan x)"
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
      
            
    subsubsection \<open>Floating point classes and constants\<close>  
    (* is_infinity is_nan is_zero is_finite is_normal is_denormal     
       (the_nan x) \<infinity> -\<infinity> 0 -0 topfloat bottomfloat
    *)
    
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
            
    lemma pow2N_le1_conv[simp]: "2^n \<le> Suc 0 \<longleftrightarrow> n<1"
      using le_eq_less_or_eq by force 
      
      
    private lemma class_topfloat_auxs: 
      "\<not>is_zero topfloat"
      "is_normal (topfloat :: ('e, 'f) float) \<longleftrightarrow> LENGTH('e)>1"
      "is_denormal (topfloat :: ('e, 'f) float) \<longleftrightarrow> LENGTH('e) = 1"
      apply (metis One_nat_def Suc_leI diff_diff_cancel diff_zero float_defs(30) fraction_upper_bound is_zero_def less_one the_nan_simps(2))
      subgoal unfolding is_normal_def by simp
      subgoal unfolding is_denormal_def by (simp)
      done
        
        
        
    lemma float_class_consts[simp, intro!]:
      "\<not>is_infinity (the_nan x)"
      "is_nan       (the_nan x)"
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
      
      supply [simp] = the_nan_is_nan finite_topfloat class_topfloat_auxs
      apply (all \<open>
          (rule float_distinct' the_nan_is_nan; simp; fail 
        | (simp; fail) 
        | (simp del: float_sel_simps add: float_defs; fail))?\<close>)
      done

      
      
    subsubsection \<open>Floating point constants inequalities\<close>
    
    (* Symmetry reduction for next lemma *)
    lemma float_eq_minus_minus_conv[simp]: "-a=-b \<longleftrightarrow> a=b" for a b :: "(_,_)float"
      by (metis minus_minus_float)
    
    lemma float_neq_minus_self[simp, symmetric, simp]: "a \<noteq> -a" 
      for a :: "(_,_)float" 
      apply (metis float_neg_sign)
      done
      
    (* (the_nan x) \<infinity> -\<infinity> 0 -0 topfloat -topfloat *)
    lemma float_ineqs[simp, symmetric, simp]:
      "the_nan x \<noteq> \<infinity>"
      "the_nan x \<noteq> -\<infinity>"
      "the_nan x \<noteq> 0"
      "the_nan x \<noteq> -0"
      "the_nan x \<noteq> topfloat"
      "the_nan x \<noteq> -topfloat"
          
      "\<infinity> \<noteq> 0"
      "\<infinity> \<noteq> -0"
      "\<infinity> \<noteq> topfloat"
      "\<infinity> \<noteq> -topfloat"
      
      "-\<infinity> \<noteq> 0"
      "-\<infinity> \<noteq> topfloat"
      
      "0 \<noteq> topfloat"
      "0 \<noteq> -topfloat"
      
      "-0 \<noteq> topfloat"
      
      apply safe
      apply (
        drule arg_cong[where f=is_finite] arg_cong[where f=is_nan] arg_cong[where f=is_zero] arg_cong[where f=sign]; 
        simp; fail)+
      done
      
      
    subsection \<open>Rewrite rules for class cases\<close>  
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
      
    lemma float_le_inf_simps[simp]:
      "-\<infinity> \<le> u \<longleftrightarrow> \<not>is_nan u"
      "\<infinity> \<le> u \<longleftrightarrow> u = \<infinity>"
      "u \<le> \<infinity> \<longleftrightarrow> \<not>is_nan u"
      "u \<le> -\<infinity> \<longleftrightarrow> u=-\<infinity>"
      subgoal by (auto simp add: float_defs)
      subgoal by (auto simp: less_eq_float_def fle_def fcompare_def is_infinity_alt)
      subgoal by (auto simp add: float_defs)
      subgoal by (auto simp: less_eq_float_def fle_def fcompare_def is_infinity_alt)
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
      
      (*define nv\<^sub>1 where "nv\<^sub>1 = 2 ^ e\<^sub>1 * (1 + f\<^sub>1 / F)"
      define nv\<^sub>2 where "nv\<^sub>2 = 2 ^ e\<^sub>2 * (1 + f\<^sub>2 / F)"
      *)
      
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
      apply (auto simp: is_zero_alt)
      done


      
    subsection \<open>Rounding\<close>  
      
    subsubsection \<open>Non-zero\<close>
    
    lemma is_closest_precise: "\<lbrakk>x\<in>s; s\<subseteq>Collect is_finite; \<not>is_zero x\<rbrakk> \<Longrightarrow> is_closest valof (s) (valof x) a \<longleftrightarrow> a=x"  
      unfolding is_closest_def
      apply auto
      apply (drule spec[where x=x]; simp)
      by (simp add: subset_eq valof_nonzero_injective)
    
    lemma closest_precise: "\<lbrakk> x\<in>s; s\<subseteq>Collect is_finite; \<not>is_zero x\<rbrakk> \<Longrightarrow> closest valof p s (valof x) = x"
      unfolding closest_def
      apply (rule some_equality)
      apply (auto simp: is_closest_precise)
      done
        
    lemma threshold_pos: "threshold TYPE(('e,'f) float) > 0"
      unfolding threshold_def
      apply simp 
      apply (intro mult_pos_pos divide_pos_pos)
      apply (simp_all add: algebra_simps)
      by (smt (verit, best) le_divide_eq_1_pos less_nat_zero_code power_0 power_strict_increasing_iff)
      
    lemma round_valof: "\<lbrakk> IEEE.is_finite x; \<not>IEEE.is_zero x; 1<LENGTH('e) \<rbrakk> \<Longrightarrow> round m (valof x) = x" for x :: "('e,'f) float"
      apply (cases m; simp)
      using threshold_pos[where 'e='e and 'f='f]
      using float_val_lt_threshold[of x] float_val_gt_threshold[of x]
      apply (auto intro: closest_precise)
      apply (metis One_nat_def float_val_le_largest leD)
      apply (metis One_nat_def float_val_le_largest leD)
      apply (metis One_nat_def float_val_ge_largest leD)
      apply (metis One_nat_def float_val_ge_largest leD)
      apply (metis One_nat_def float_val_le_largest leD)
      apply (metis One_nat_def float_val_ge_largest leD)
      apply (metis One_nat_def float_val_ge_largest leD)
      apply (metis One_nat_def float_val_le_largest leD)
      apply (metis One_nat_def float_val_ge_largest leD)
      done
    
    subsubsection \<open>Zero\<close>
    
    lemma valof_eq_zero_conv: "IEEE.is_finite a \<Longrightarrow> valof a = 0 \<longleftrightarrow> a=0 \<or> a=-0"  
      using valof_almost_injective by fastforce 
    
    lemma is_closest_zero: "0\<in>s \<Longrightarrow> -0\<in>s \<Longrightarrow> s\<subseteq>Collect IEEE.is_finite \<Longrightarrow> is_closest valof s 0 a \<longleftrightarrow> is_zero a"
      unfolding is_closest_def
      apply (auto simp: is_zero_alt)
      apply (metis abs_le_zero_iff abs_zero mem_Collect_eq subset_eq valof_eq_zero_conv)
      done
      
    lemma closest_zero: "\<lbrakk> 0\<in>s; -0\<in>s; s\<subseteq>Collect is_finite\<rbrakk> \<Longrightarrow> is_zero (closest valof p s 0)"  
      unfolding closest_def
      by (smt (verit) is_closest_zero is_zero_alt someI_ex)

    lemma round_zero: "Suc 0 < LENGTH('e) \<Longrightarrow> IEEE.is_zero (round m 0 :: ('e,'f) float)"  
      apply (cases m; simp)
      using threshold_pos[where 'e='e and 'f='f]
      apply (auto intro: closest_zero)
      apply (smt (verit, best) One_nat_def finite_topfloat float_val_ge_largest valof_topfloat)
      apply (smt (verit, best) One_nat_def finite_topfloat float_val_ge_largest valof_topfloat)
      apply (smt (verit, best) One_nat_def finite_topfloat float_val_ge_largest valof_topfloat)
      done
    
    subsubsection \<open>Rounding and \<^const>\<open>valof\<close>\<close>    
    lemma valof_round_valof: "\<lbrakk> IEEE.is_finite x; Suc 0<LENGTH('e) \<rbrakk> 
      \<Longrightarrow> valof (round m (valof x) :: ('e,'f) float) = valof x" for x :: "('e,'f) float"
      by (metis One_nat_def round_valof round_zero val_zero)
      
      
    subsection \<open>Bounding the Rounding\<close>        
    text \<open>Rounding will not round beyond a representable bound of the exact value.
      This is useful to prove non-overflow of rounded computations in the rounding direction,
      e.g., when rounding up, and one knows that the actual value is \<open>\<le>x\<close>, the the rounded up
      value will also stay \<open>\<le>x\<close>.
    \<close>
    
    (* TODO: Move *)
    lemma closestI: 
      fixes v :: "('e, 'f)float \<Rightarrow> real"
      assumes "finite s" and "s \<noteq> {}"
      assumes "\<And>b. \<lbrakk> b\<in>s; is_closest v s x b; \<forall>b'. is_closest v s x b' \<and> p b' \<longrightarrow> p b \<rbrakk> \<Longrightarrow> P b"
      shows "P (closest v p s x)"
      using closest_in_set[OF assms(1,2)] closest_is_everything[OF assms(1,2)] assms(3) 
      by metis

      
    lemma closest_cases:
      fixes v :: "('e, 'f)float \<Rightarrow> real"
      assumes "finite s" and "s \<noteq> {}"
      obtains b where "closest v p s x = b" "b\<in>s" "is_closest v s x b" "\<forall>b'. is_closest v s x b' \<and> p b' \<longrightarrow> p b"
      using assms closestI[OF assms] by fast

    lemma ex_closest_finite:
      fixes x :: "_::linorder"
      assumes "finite s" 
      assumes "s\<noteq>{}"  
      shows "\<exists>a. is_closest v s x a" 
    proof -
      show ?thesis
        unfolding is_closest_def Bex_def[symmetric] Ball_def[symmetric]
        apply (rule finite_attains_inf)
        by fact+
    qed  
    
    lemma ex_closest_finite_tiebreak:
      fixes x :: "_::linorder"
      assumes "finite s" 
      assumes "s\<noteq>{}"  
      shows "\<exists>a. is_closest v s x a \<and> ((\<exists>b. is_closest v s x b \<and> p b) \<longrightarrow> p a)"
      by (meson assms ex_closest_finite)
    
    lemma closest_in_s: "finite s \<Longrightarrow> s\<noteq>{} \<Longrightarrow> closest v p s x \<in> s" for x :: "_::linorder"
      unfolding closest_def
      by (smt (verit, ccfv_threshold) ex_closest_finite_tiebreak is_closest_def someI_ex)
      
      
    lemma largest_pos: "largest TYPE(('e,'f)float) > 0"
      unfolding largest_def 
      by (simp_all add: divide_less_eq power_gt1_lemma)
      
            
    lemma threshold_pos'[simp]: "\<not>(threshold TYPE(('e, 'f) float) \<le> 0)"  
      using threshold_pos leD by blast
    
            
    lemma m_threshold_not_le_threshold_trans: "\<lbrakk>x \<le> - threshold TYPE(('e, 'f) float); threshold TYPE(('e, 'f) float) \<le> x\<rbrakk> \<Longrightarrow> False"  
      by (smt (z3) threshold_pos)

    declare round.simps[simp del]
      
    lemma zerosign_no_zero[simp]: "\<not>is_zero a \<Longrightarrow> zerosign s a = a"
      by (auto simp: zerosign_def)
    
      
            
    context 
      fixes u :: "('e, 'f) float"
      assumes LEN: "Suc 0 < LENGTH('e)"
      assumes FIN: "is_finite u"
    begin  
      lemma round_aux_not_gt_largest:  
        "\<lbrakk>x \<le> valof u; largest TYPE(('e, 'f) float) < x\<rbrakk> \<Longrightarrow> u=xx"
        by (smt (verit, best) One_nat_def float_val_le_largest FIN LEN)
    
      lemma round_aux_not_ge_threshold: "\<lbrakk>x \<le> valof u; threshold TYPE(('e, 'f) IEEE.float) \<le> x \<rbrakk> \<Longrightarrow> u = xx"
        by (metis One_nat_def float_val_lt_threshold leD le_less_trans FIN LEN)
      
      lemma round_aux_not_le_threshold: "\<lbrakk>valof u \<le> x; x \<le> - threshold TYPE(('e, 'f) IEEE.float)\<rbrakk> \<Longrightarrow> u = xx"  
        using FIN LEN float_val_gt_threshold by fastforce
      
      lemma round_aux_not_lt_largest: "\<lbrakk>valof u \<le> x; x < - largest TYPE(('e, 'f) IEEE.float)\<rbrakk> \<Longrightarrow> False"  
        by (smt (verit, del_insts) FIN LEN One_nat_def float_val_ge_largest)
      
        
      private lemma LEN': "1 < LENGTH('e)" using LEN by simp 
        
      lemmas round_auxs = round_aux_not_gt_largest round_aux_not_ge_threshold
                          round_aux_not_le_threshold round_aux_not_lt_largest
                          valof_topfloat[OF LEN'] float_val_ge_bottomfloat[OF LEN' FIN] 
                          round.simps not_less not_le float_val_le_largest[OF FIN LEN']
                          largest_pos 

      lemmas round_auxsD = round_aux_not_lt_largest m_threshold_not_le_threshold_trans
                          
                                
      theorem round_ubounded: "x \<le> valof u \<Longrightarrow> round m x \<le> u"
        apply (cases m)
        using FIN
        apply (auto simp: round_auxs)
        subgoal by (rule closestI; auto simp: is_closest_def; fail)
        subgoal by (rule closestI; auto simp: is_closest_def; fail)
        subgoal by (rule closestI; auto simp: is_closest_def; fail)
        subgoal
          apply (rule closestI; auto simp: is_closest_def)
          by (metis One_nat_def bottomfloat_eq_m_largest finite_bottomfloat LEN)
        done
              
      theorem round_lbounded: "x \<ge> valof u \<Longrightarrow> round m x \<ge> u"
        apply (cases m)
        using FIN
        apply (auto simp: round_auxs dest: round_auxsD) 
        subgoal by (rule closestI; auto simp: is_closest_def; fail)
        subgoal by (rule closestI; auto simp: is_closest_def; fail)
        subgoal
          apply (rule closestI; auto simp: is_closest_def)
          by (metis finite_topfloat valof_topfloat[OF LEN'])
        subgoal by (rule closestI; auto simp: is_closest_def; fail)
        done

        
                
    end
      
      
      
      
    subsection \<open>Lower and Upper Bounding\<close>  
      
      
    definition "ubound d r \<equiv> d=\<infinity> \<or> (is_finite d \<and> valof d \<ge> r)"  
    definition "lbound d r \<equiv> d=-\<infinity> \<or> (is_finite d \<and> valof d \<le> r)"  
      
    lemma bound_simps[simp]: 
      "\<not>ubound (the_nan x) r"
      "\<not>lbound (the_nan x) r"
      "\<not>ubound (-\<infinity>) r"  
      "ubound (\<infinity>) r"  
      "\<not>lbound \<infinity> r"  
      "lbound (-\<infinity>) r"  
      unfolding ubound_def lbound_def 
      by auto
      
      
    lemma round_not_nan:
      assumes LEN: "Suc 0 < LENGTH('e)"
      shows "\<not>is_nan (round m x :: ('e,'f) float)"  
      apply (cases m; simp add: round_auxs round.simps; intro impI)
      apply (rule closestI; auto)
      apply (rule closestI; auto)
      apply (rule closestI; auto simp: not_less valof_topfloat[simplified, OF LEN])
      apply (rule closestI; auto simp: not_less valof_topfloat[simplified, OF LEN] valof_uminus)
      done
          
      
    lemma ubound_round: "1 < LENGTH('e) \<Longrightarrow> ubound (round To_pinfinity x :: ('e,'f) float) x"
      unfolding ubound_def 
      apply (auto simp: finite_topfloat not_le not_less round.simps)
      subgoal by (smt (verit, ccfv_SIG) largest_pos)
      subgoal by (simp add: bottomfloat_eq_m_largest)
      subgoal 
        using closest_in_s[of "{a. is_finite a \<and> x \<le> valof a}" valof "(\<lambda>_. True)" x]
        apply auto
        by (smt (verit, ccfv_threshold) One_nat_def closest_is_closest empty_iff finite_topfloat is_closest_def mem_Collect_eq valof_topfloat)
      subgoal
        using closest_in_s[of "{a. is_finite a \<and> x \<le> valof a}" valof "(\<lambda>_. True)" x]
        apply auto
        by (smt (verit, del_insts) Collect_empty_eq One_nat_def closest_in_s finite finite_topfloat mem_Collect_eq valof_topfloat)
      done
      
      
    lemma lbound_round: "1 < LENGTH('e) \<Longrightarrow> lbound (round To_ninfinity x :: ('e,'f) float) x"
      unfolding lbound_def 
      apply (auto simp: finite_topfloat not_le not_less valof_topfloat round.simps)
      subgoal 
        apply (subgoal_tac "\<exists>xa. is_finite xa \<and> valof xa \<le> x")
        using closest_in_s[of "{a. is_finite a \<and> x \<ge> valof a}" valof "(\<lambda>_. True)" x]
        apply auto 
        by (smt (verit, best) One_nat_def bottomfloat_eq_m_largest finite_bottomfloat)
      subgoal
        apply (subgoal_tac "\<exists>xa. is_finite xa \<and> valof xa \<le> x")
        using closest_in_s[of "{a. is_finite a \<and> x \<ge> valof a}" valof "(\<lambda>_. True)" x]
        apply auto
        by (smt (verit, best) One_nat_def bottomfloat_eq_m_largest finite_bottomfloat)
      done
      
    lemma ubound_zerosign[simp]: "ubound (zerosign s d) x = ubound d x"  
      unfolding zerosign_def ubound_def 
      apply (auto dest: float_distinct' simp: val_zero)
      unfolding is_finite_def
      apply auto
      done  

    lemma lbound_zerosign[simp]: "lbound (zerosign s d) x = lbound d x"  
      unfolding zerosign_def lbound_def 
      apply (auto dest: float_distinct' simp: val_zero)
      unfolding is_finite_def
      apply auto
      done  
      
            
    lemma ubound_trans[trans]: "ubound f x \<Longrightarrow> x'\<le>x \<Longrightarrow> ubound f x'"  
      unfolding ubound_def by auto
      
    lemma lbound_trans[trans]: "lbound f x \<Longrightarrow> x\<le>x' \<Longrightarrow> lbound f x'"  
      unfolding lbound_def by auto
    
      
    lemma ubound_finite_conv: "\<not>is_infinity d \<Longrightarrow> ubound d x \<longleftrightarrow> is_finite d \<and> valof d \<ge> x"  
      by (auto simp add: ubound_def)
      
    lemma lbound_finite_conv: "\<not>is_infinity d \<Longrightarrow> lbound d x \<longleftrightarrow> is_finite d \<and> valof d \<le> x"  
      by (auto simp add: lbound_def)

      
    (* upper-bound, non-negative *)        
    definition "ub_nn f x \<equiv> ubound f x \<and> x\<ge>0 \<and> sign f=0"  
    (* upper-bound, positive and finite *)
    definition "ub_pf f x \<equiv> ubound f x \<and> x>0 \<and> \<not>is_infinity f"  
    
    (* lower-bound, non-negative *)        
    definition "lb_nn f x \<equiv> lbound f x \<and> x\<ge>0 \<and> sign f=0"  
    (* lower-bound, positive and finite *)
    definition "lb_pf f x \<equiv> lbound f x \<and> x>0 \<and> sign f=0 \<and> \<not>is_infinity f"  
    
    lemma lbound_sign_nonneg: "lbound f x \<Longrightarrow> sign f = 0 \<Longrightarrow> x\<ge>0"
      by (smt (z3) float_neg_sign1 infinity_simps(1) lbound_def valof_nonneg)
    
    lemma lb_nnI[intro?]: "lbound f x \<Longrightarrow> sign f=0 \<Longrightarrow> lb_nn f x"
      unfolding lb_nn_def using lbound_sign_nonneg by blast
      
    lemma lb_nnE: assumes "lb_nn f x" obtains "lbound f x" "x\<ge>0" "sign f=0"
      using assms unfolding lb_nn_def by simp
      
      
      
            
    context
      fixes f\<^sub>1 f\<^sub>2 :: "('e,'f) float"
      assumes LEN[simp]: "Suc 0 < LENGTH('e)"
    begin    
      
      
    lemma ubound_fadd_pinf: "ubound f\<^sub>1 x\<^sub>1 \<Longrightarrow> ubound f\<^sub>2 x\<^sub>2 \<Longrightarrow> ubound (fadd To_pinfinity f\<^sub>1 f\<^sub>2) (x\<^sub>1+x\<^sub>2)"
      apply (auto simp add: fadd_def elim!: is_infinity_cases)
      apply (rule ubound_trans)
      apply (rule ubound_round)
      apply (auto simp add: ubound_def)
      done
      
    lemma ubound_fsub_pinf: "ubound f\<^sub>1 x\<^sub>1 \<Longrightarrow> lbound f\<^sub>2 x\<^sub>2 \<Longrightarrow> ubound (fsub To_pinfinity f\<^sub>1 f\<^sub>2) (x\<^sub>1-x\<^sub>2)"
      apply (auto simp add: fsub_def elim!: is_infinity_cases)
      apply (rule ubound_trans)
      apply (rule ubound_round, simp)
      apply (simp add: ubound_finite_conv lbound_finite_conv)
      done

    lemma lbound_fadd_pinf: "lbound f\<^sub>1 x\<^sub>1 \<Longrightarrow> lbound f\<^sub>2 x\<^sub>2 \<Longrightarrow> lbound (fadd To_ninfinity f\<^sub>1 f\<^sub>2) (x\<^sub>1+x\<^sub>2)"
      apply (auto simp add: fadd_def elim!: is_infinity_cases)
      apply (rule lbound_trans)
      apply (rule lbound_round)
      apply (auto simp add: lbound_def)
      done
      
    lemma lbound_fsub_pinf: "lbound f\<^sub>1 x\<^sub>1 \<Longrightarrow> ubound f\<^sub>2 x\<^sub>2 \<Longrightarrow> lbound (fsub To_ninfinity f\<^sub>1 f\<^sub>2) (x\<^sub>1-x\<^sub>2)"
      apply (auto simp add: fsub_def elim!: is_infinity_cases)
      apply (rule lbound_trans)
      apply (rule lbound_round)
      apply (auto simp add: lbound_def ubound_def)
      done
      
          
      

    lemma valof_nonpos': "sign x = Suc 0 \<Longrightarrow> valof x \<le> 0"  
      by (simp add: valof_nonpos)
            

    lemma ubound_fmul_pinf: "\<lbrakk>ubound f\<^sub>1 x\<^sub>1; ubound f\<^sub>2 x\<^sub>2; \<not>is_infinity f\<^sub>1; \<not>is_zero f\<^sub>1; x\<^sub>1\<ge>0; x\<^sub>2\<ge>0\<rbrakk> 
      \<Longrightarrow> ubound (fmul To_pinfinity f\<^sub>1 f\<^sub>2) (x\<^sub>1*x\<^sub>2)"
      apply (auto simp add: fmul_def elim!: is_infinity_cases)
      subgoal
        apply (rule ubound_trans)
        apply (rule ubound_round, simp)
        apply (clarsimp simp: ubound_finite_conv lbound_finite_conv) 
        apply (meson mult_mono')
        done
      subgoal 
        apply (auto simp: ubound_finite_conv dest!: valof_nonpos')
        using valof_eq_zero_conv by fastforce
      subgoal
        apply (rule ubound_trans)
        apply (rule ubound_round, simp)
        by (meson mult_mono' ubound_finite_conv)
      done  
      
      
    lemma ubound_fmadd_pinf: "\<lbrakk> ubound f\<^sub>1 x\<^sub>1; ubound f\<^sub>2 x\<^sub>2; ubound f\<^sub>3 x\<^sub>3; sign f\<^sub>1=0; sign f\<^sub>2=0; sign f\<^sub>3=0; \<not>is_infinity f\<^sub>1; \<not>is_zero f\<^sub>1; x\<^sub>1\<ge>0; x\<^sub>2\<ge>0; x\<^sub>3\<ge>0 \<rbrakk>
      \<Longrightarrow> ubound (fmul_add To_pinfinity f\<^sub>1 f\<^sub>2 f\<^sub>3) (x\<^sub>1*x\<^sub>2+x\<^sub>3) \<and> sign (fmul_add To_pinfinity f\<^sub>1 f\<^sub>2 f\<^sub>3) = 0"
      apply (auto simp add: fmul_add_def float_round_def Let_def cong: if_cong)
      subgoal
        by (smt (verit, ccfv_SIG) LEN One_nat_def float_class_consts(22) float_ineqs(8) is_zero_alt mult_mono' ubound_def ubound_finite_conv ubound_round valof_zero(1) valof_zero(2))
      subgoal
        by (smt (verit, ccfv_SIG) LEN One_nat_def is_infinity_alt mult_mono' ubound_def ubound_round)
      subgoal
        by (smt (verit, ccfv_SIG) IEEE_Fp_Add.ubound_fmul_pinf LEN \<open>\<lbrakk>ubound f\<^sub>1 x\<^sub>1; ubound f\<^sub>2 x\<^sub>2; ubound f\<^sub>3 x\<^sub>3; sign f\<^sub>1 = 0; sign f\<^sub>2 = 0; sign f\<^sub>3 = 0; \<not> is_infinity f\<^sub>1; \<not> is_zero f\<^sub>1; 0 \<le> x\<^sub>1; 0 \<le> x\<^sub>2; 0 \<le> x\<^sub>3; \<not> is_zero (IEEE.round To_pinfinity (valof f\<^sub>1 * valof f\<^sub>2 + valof f\<^sub>3)); \<not> is_infinity f\<^sub>3; \<not> is_infinity f\<^sub>2; \<not> is_nan f\<^sub>1; \<not> is_nan f\<^sub>2; \<not> is_nan f\<^sub>3\<rbrakk> \<Longrightarrow> ubound (IEEE.round To_pinfinity (valof f\<^sub>1 * valof f\<^sub>2 + valof f\<^sub>3)) (x\<^sub>1 * x\<^sub>2 + x\<^sub>3)\<close> float_class_consts(22) float_distinct(1) float_neq_minus_self fmul_def infinite_infinity(1) is_finite_uminus is_zero_alt sign_convs(3) ubound_def ubound_finite_conv valof_nonpos' valof_nonzero_injective valof_zero(1) zero_le_mult_iff)
      done
      
    lemma lbound_fmul_ninf: "\<lbrakk> lbound f\<^sub>1 x\<^sub>1; lbound f\<^sub>2 x\<^sub>2; \<not>is_infinity f\<^sub>1; \<not>is_zero f\<^sub>1; sign f\<^sub>1=0; sign f\<^sub>2=0 \<rbrakk> 
      \<Longrightarrow> lbound (fmul To_ninfinity f\<^sub>1 f\<^sub>2) (x\<^sub>1*x\<^sub>2)"  
      apply (auto simp add: fmul_def elim!: is_infinity_cases)
      apply (rule lbound_trans)
      apply (rule lbound_round, simp)
      by (meson lbound_finite_conv mult_mono' valof_nonneg)
      
    lemma lbound_fmadd_ninf: "\<lbrakk>lbound f\<^sub>1 x\<^sub>1; lbound f\<^sub>2 x\<^sub>2; lbound f\<^sub>3 x\<^sub>3; sign f\<^sub>1=0; sign f\<^sub>2=0; sign f\<^sub>3=0; \<not>is_infinity f\<^sub>1; \<not>is_zero f\<^sub>1\<rbrakk> 
      \<Longrightarrow> lbound (fmul_add To_ninfinity f\<^sub>1 f\<^sub>2 f\<^sub>3) (x\<^sub>1*x\<^sub>2+x\<^sub>3)"
      apply (auto simp: fmul_add_def float_round_def cong: if_cong elim: is_infinity_cases)
      apply (auto simp add: Let_def lbound_def)
      subgoal by (smt (verit) mult_nonneg_nonneg valof_nonneg)
      subgoal by (metis LEN One_nat_def lbound_def lbound_round)
      subgoal by (smt (verit, best) LEN One_nat_def lbound_def lbound_round mult_mono valof_nonneg)
      done
            
      
    lemma sign_float_round_zero_conv: "sign (float_round To_ninfinity toneg 0 :: ('e,'f) float) = (if toneg then 1 else 0)"  
      by (auto simp: float_round_def Let_def round_zero)
    

    lemma float_round_as_zerosign: "float_round m s x = zerosign (if s then 1 else 0) (round m x)"  
      unfolding float_round_def zerosign_def
      by auto
      
      
    (* TODO: Generalize to round m *)
    lemma sign_float_round_ninf_aux: 
      "\<lbrakk>is_finite (f :: ('e,'f) float); 0<valof f; valof f \<le> x\<rbrakk> \<Longrightarrow> sign (float_round To_ninfinity True (x) :: ('e,'f) float) = 0"  
      apply (frule (1) round_lbounded[OF LEN, where m=To_ninfinity])
      apply (auto simp: float_round_def Let_def is_zero_alt)
      by (smt (z3) LEN One_nat_def float_le float_le_inf_simps(4) lbound_def lbound_round sign_cases valof_nonpos)
      

    
      
            
    lemma valof_smallest_pos_lt1: "valof (smallest_pos::('e,'f) float) < 1"  
    proof -
      have "(2::real) \<le> 2 ^ LENGTH('f)" by simp
      moreover have "(1::real) < 2 ^ (2 ^ (LENGTH('e) - Suc 0) - Suc 0)"
        by (metis LEN One_nat_def numeral_One numeral_less_iff one_less_power semiring_norm(76) zero_less_diff)
      ultimately have "(2::real) < 2 ^ LENGTH('f) * 2 ^ (2 ^ (LENGTH('e) - Suc 0) - Suc 0)"
        by (smt (verit, ccfv_SIG) LEN add_diff_cancel_right' len_gt_0 less_exp less_trans_Suc power_Suc0_right power_add power_strict_increasing_iff zero_less_diff)
    
      then show ?thesis
        by (auto simp: valof_smallest_pos algebra_simps)
    qed  
      
    lemma valof_smallest_pos_sqare_less: 
      "valof ((smallest_pos::('e,'f) float)) * valof ((smallest_pos::('e,'f) float)) < valof ((smallest_pos::('e,'f) float))"  
      using valof_smallest_pos_lt1
      by (simp add: valof_smallest_pos_pos)
      
      
    lemma aux1: "2/(B*2^f) \<le> (2^e)*(1+x)/B" if "B>0" "e>0" "x\<ge>0" for B x :: real
    proof -
      have "2/(2^f) \<le> (2^e)*(1+x)"
        by (smt (verit) divide_numeral_1 field_sum_of_halves le_divide_eq_1_pos less_one nonzero_mult_div_cancel_left numerals(1) power_0 power_eq_0_iff power_less_imp_less_exp power_one_right that(2) that(3)) sorry
      thus ?thesis using \<open>B>0\<close>
        by (metis divide_divide_eq_left' divide_right_mono less_eq_real_def)
    qed
    
    
      
    lemma aux2: "2/(B*2^f) \<le> 2*real b / (B*2^f)" if "B>0" "b>0"
      by (smt (verit) One_nat_def Suc_leI divide_divide_eq_left divide_le_cancel of_nat_1 of_nat_mono that(1) that(2) zero_less_power)  
      
      
    lemma smallest_pos_smallest: "is_finite b \<Longrightarrow> valof b > 0 \<Longrightarrow> valof b \<ge> valof (smallest_pos :: ('a,'b) float)" for b :: "('a,'b) float"
      apply (subgoal_tac "sign b = 0 \<and> (exponent b = 0 \<longrightarrow> fraction b > 0)")
      subgoal by (auto simp add: valof_eq aux1 aux2)
      by (metis is_zero_def leD neq0_conv order_refl sign_cases val_zero valof_nonpos)
      
      
    lemma smallest_pos_square_round_down_to_zero: "is_zero (round To_ninfinity (valof (smallest_pos::('e,'f) float) * valof (smallest_pos::('e,'f) float)) ::('e,'f) float)"
      apply (auto simp: round_auxs round.simps)
      subgoal 
        using float_val_le_largest[of "smallest_pos::('e,'f) float", simplified] valof_smallest_pos_sqare_less
        by simp
      subgoal
        by (smt (verit) not_square_less_zero)
      subgoal
        apply (rule closestI)
        subgoal by simp
        subgoal by auto
        subgoal for b
          apply (auto simp: is_closest_def)
          by (metis (no_types, hide_lams) float_class_consts(22) is_zero_alt leD le_less_trans less_eq_real_def smallest_pos_smallest valof_eq_zero_conv valof_smallest_pos_sqare_less zero_le_square)
        done  
      done      
      
    lemma [simp]: "\<not>is_infinity smallest_pos"
      by (simp add: float_distinct'(15)) 
      
    lemma [simp]: "valof smallest_pos \<noteq> 0"
      by (smt (z3) valof_smallest_pos_pos) 
      
    lemma "fmul_add To_ninfinity (smallest_pos::('e,'f) float) (smallest_pos) 0 = -0"  
      by (auto simp add: fmul_add_def float_round_as_zerosign zerosign_def finite_nan Let_def smallest_pos_square_round_down_to_zero)
      
    notepad begin  
      fix a b c :: "('e,'f) float"
      assume F[simp]: "is_finite a" "is_finite b"
      and GT: "valof a > 0" "valof b > 0" and CZ[simp]: "c=0"
      and Z: "is_zero (IEEE.round To_ninfinity (valof a * valof b) :: ('e,'f) float)"
      
      have [simp]: "sign a = 0" "sign b = 0"
        using GT valof_nonpos by fastforce+
      have [simp]: "\<not>is_infinity a" "\<not>is_infinity b"
        by (simp_all add: finite_infinity)
      
      have "fmul_add To_ninfinity a b c = -0"
        using GT
        apply (simp add: fmul_add_def float_round_as_zerosign Z zerosign_def finite_nan)
        done
      
    
    
    end
      
    lemma 
      assumes "\<not>is_nan f\<^sub>1" "\<not>is_nan f\<^sub>2" "\<not>is_nan f\<^sub>3" "sign f\<^sub>1=0" "sign f\<^sub>2=0" "sign f\<^sub>3=0" "\<not>is_infinity f\<^sub>1" "\<not>is_zero f\<^sub>1" 
      shows "sign (fmul_add To_ninfinity f\<^sub>1 f\<^sub>2 f\<^sub>3) = 0"
    proof -
    
      have GEZ: "valof f\<^sub>1\<ge>0" "valof f\<^sub>2\<ge>0" "valof f\<^sub>3\<ge>0" using assms 
        by (simp_all add: valof_nonneg)
      
      have NI_IF3: "\<not>is_infinity f\<^sub>3 \<longleftrightarrow> is_finite f\<^sub>3"
        using assms(3) finite_infinity float_cases_finite by blast
      
      from assms show ?thesis
        apply (cases "is_infinity f\<^sub>2"; cases "is_infinity f\<^sub>3"; simp?)
        apply (auto simp: fmul_add_def cong: if_cong)
        apply (auto simp add: Let_def sign_float_round_zero_conv)
        subgoal
          apply (auto simp: float_round_as_zerosign)
        
        
         sorry
        subgoal
          apply (rule sign_float_round_ninf_aux[where f=f\<^sub>3]; auto simp: NI_IF3)
          using GEZ by auto
      
      
     

    lemma ub_pf_alt: "ub_pf f x \<longleftrightarrow> ub_nn f x \<and> x>0 \<and> \<not>is_infinity f"
      unfolding ub_pf_def ub_nn_def ubound_def
      using valof_nonpos by fastforce
    

    lemma ub_nn_gt0D: "ub_nn f x \<Longrightarrow> x>0 \<Longrightarrow> \<not>is_zero f"
      apply (auto simp: ub_nn_def ubound_def)
      by (simp add: val_zero)
          

    lemma ubound_round': 
      assumes "x'\<ge>x"
      shows "ubound (round To_pinfinity x' :: ('e,'f) float) x"  
      using assms ubound_round ubound_trans by force
      
    lemma sign_zerosign: 
      "sign (zerosign 0 x) = (if is_zero x then 0 else sign x)"  
      "sign (zerosign 1 x) = (if is_zero x then 1 else sign x)"  
      by (auto simp: zerosign_def) 

    lemma fmul_pinf_sign_aux: "\<lbrakk> sign f\<^sub>1 = 0;  sign f\<^sub>2 = 0; 
     \<not> is_zero (IEEE.round To_pinfinity (valof f\<^sub>1 * valof f\<^sub>2) :: ('e,'f) float)\<rbrakk>
    \<Longrightarrow> sign (IEEE.round To_pinfinity (valof f\<^sub>1 * valof f\<^sub>2) :: ('e,'f) float) = 0"  
      by (smt (z3) LEN One_nat_def infinity_simps(1) is_zero_alt mult_nonneg_nonneg sign_cases ubound_def ubound_round valof_eq_zero_conv valof_nonneg valof_nonpos)
      
    lemma fmul_pinf_pf_nn: "ub_pf f\<^sub>1 x\<^sub>1 \<Longrightarrow> ub_nn f\<^sub>2 x\<^sub>2 \<Longrightarrow> ub_nn (fmul To_pinfinity f\<^sub>1 f\<^sub>2) (x\<^sub>1*x\<^sub>2)"
      unfolding ub_pf_alt apply clarify
      apply (frule (1) ub_nn_gt0D)
      apply (auto simp add: fmul_def float_round_def Let_def ub_nn_def sign_zerosign fmul_pinf_sign_aux cong: if_cong) 
      subgoal
        apply (rule ubound_round')
        apply (auto simp: ubound_def mult_mono)
        done
      done

    lemma fadd_pinf_sign_aux: "\<lbrakk> sign f\<^sub>1 = 0;  sign f\<^sub>2 = 0; 
     \<not> is_zero (IEEE.round To_pinfinity (valof f\<^sub>1 + valof f\<^sub>2) :: ('e,'f) float)\<rbrakk>
    \<Longrightarrow> sign (IEEE.round To_pinfinity (valof f\<^sub>1 + valof f\<^sub>2) :: ('e,'f) float) = 0"  
      by (smt (z3) LEN One_nat_def infinity_simps(1) is_zero_alt sign_cases ubound_def ubound_round valof_eq_zero_conv valof_nonneg valof_nonpos)
      
      
    lemma fadd_pinf_sign_aux': "\<lbrakk>sign f\<^sub>1 = 0; sign f\<^sub>2 = 0; \<not>is_nan f\<^sub>1; \<not>is_nan f\<^sub>2\<rbrakk> \<Longrightarrow> sign (fadd To_pinfinity f\<^sub>1 f\<^sub>2) = 0"  
      unfolding fadd_def
      by (auto simp: sign_zerosign fadd_pinf_sign_aux)
      
    lemma ubound_not_nan: "ubound f x \<Longrightarrow> \<not>is_nan f"
      by auto  
      
    lemma fadd_pinf_nn_nn: "ub_nn f\<^sub>1 x\<^sub>1 \<Longrightarrow> ub_nn f\<^sub>2 x\<^sub>2 \<Longrightarrow> ub_nn (fadd To_pinfinity f\<^sub>1 f\<^sub>2) (x\<^sub>1+x\<^sub>2)"
      unfolding ub_nn_def
      by (auto simp: ubound_fadd_pinf fadd_pinf_sign_aux' ubound_finite_conv ubound_not_nan)
      
    lemma fmadd_pinf_pf_nn_nn: "ub_pf f\<^sub>1 x\<^sub>1 \<Longrightarrow> ub_nn f\<^sub>2 x\<^sub>2 \<Longrightarrow> ub_nn f\<^sub>3 x\<^sub>3 \<Longrightarrow> ub_nn (fmul_add To_pinfinity f\<^sub>1 f\<^sub>2 f\<^sub>3) (x\<^sub>1*x\<^sub>2+x\<^sub>3)"
      unfolding ub_nn_def ub_pf_alt
      apply (auto intro: fadd_pinf_sign_aux' ubound_finite_conv ubound_not_nan)
      subgoal apply (rule ubound_fmadd_pinf[THEN conjunct1], assumption+) by (auto simp: ubound_finite_conv val_zero)
      subgoal apply (rule ubound_fmadd_pinf[THEN conjunct2], assumption+) by (auto simp: ubound_finite_conv val_zero)
      done  
            
      
    end  
    

    lemma ubound_zero[simp]: "ubound 0 0" unfolding ubound_def by simp
    
    lemma ub_nn_zero[simp]: "ub_nn 0 0" unfolding ub_nn_def by simp
    
        
    definition "fold_fmadd xs \<equiv> fold (\<lambda>(c,x) s. s + c*x) xs 0" for xs :: "(real\<times>real) list"
    
    definition "fold_fmadd_ub xs \<equiv> fold (\<lambda>(c,x) s. fmul_add To_pinfinity c x s) xs 0" for xs :: "(_) list"
    
    lemma fold_fm_add_ub_refine:
      fixes xsi :: "(('e,'f) float \<times> ('e,'f) float) list"
      assumes LEN[simp]: "Suc 0 < LENGTH('e)"
      assumes "list_all2 (rel_prod ub_pf ub_nn) xsi xs"
      shows "ub_nn (fold_fmadd_ub xsi) (fold_fmadd xs)"
    proof -
      {
        fix si :: "('e,'f) float" and s
        assume A: "ub_nn si s"
        have "ub_nn (fold (\<lambda>(c,x) s. fmul_add To_pinfinity c x s) xsi si) (fold (\<lambda>(c,x) s. c*x + s) xs s)"
          using assms(2) A
        proof (induction arbitrary: si s rule: list_all2_induct)
          case Nil
          then show ?case by auto
        next
          case (Cons cxi xsi cx xs)
          obtain ci xi c x where [simp]: "cxi = (ci,xi)" "cx=(c,x)" by fastforce
          
          show ?case
            apply clarsimp
            apply (rule Cons.IH)
            apply (rule fmadd_pinf_pf_nn_nn)
            using Cons.prems Cons.hyps
            apply (simp_all)
            done
        qed
      } from this[OF ub_nn_zero] show ?thesis
        unfolding fold_fmadd_ub_def fold_fmadd_def  
        by (simp add: algebra_simps)
    qed      
    
    xxx, ctd here: 
      integrate 1<LENGTH requirement in lbound relation
      also do lower-bound (lb_nn, lb_pf?)
    
      can we integrate additional bounds, i.e., capping values at 1 ...
      \<rightarrow> shouldn't be a problem to strengthen bounds, based on the real value
    
    

    lemma fless_le: "a<b \<longleftrightarrow> a\<le>b \<and> \<not>a \<doteq> b"  
      by (metis IEEE.less_eq_float_def IEEE.less_float_def ccode.simps(8) feq_def float_defs(10) float_defs(12) float_eq_def)
      
    lemma fle_less: "a\<le>b \<longleftrightarrow> a<b \<or> a\<doteq>b"  
      by (meson IEEE.less_eq_float_def feq_def fless_le float_defs(12) float_eq_def)
      


          
    
    definition ge_ub :: "('e, 'f) float \<Rightarrow> real \<Rightarrow> ('e, 'f) float \<Rightarrow> bool" 
      where "ge_ub d x u \<equiv> 1<LENGTH('e) \<and> is_finite d \<and> is_finite u \<and> valof d \<in> {x..valof u}"
    
    
    
    
    
    
    
    
    
    
    
    
    
      

  end
end
