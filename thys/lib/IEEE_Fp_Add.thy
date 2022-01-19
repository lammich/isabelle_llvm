section \<open>Additional Floating-Point Properties\<close>
theory IEEE_Fp_Add
imports 
  IEEE_Floating_Point.Conversion_IEEE_Float IEEE_Floating_Point.FP64
  IEEE_Fp_Add_Basic
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
  
      

            
    subsubsection \<open>Floating point classes and constants\<close>  
    (* is_infinity is_nan is_zero is_finite is_normal is_denormal     
       (the_nan x) \<infinity> -\<infinity> 0 -0 topfloat bottomfloat
    *)
    
            
      
      
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
      
      

  subsection \<open>Next Floating Point Number\<close>

  find_consts "_\<Rightarrow>_\<Rightarrow>_ \<Rightarrow> (_,_) float"
  
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
    
  find_theorems "unat (_+_)"
    
  lemma degenerate_word_ne1: "a\<noteq>1 \<longleftrightarrow> a=0" for a :: "1 word"
    using degenerate_word by force
  
  
  lemma exp_next_float: "is_finite f \<Longrightarrow> f\<noteq>topfloat \<Longrightarrow> exponent (next_float f) = (if f=-0 then 0 else (
    if sign f = 1 \<and> fraction f = 0 then exponent f - 1
    else if sign f = 0 \<and> fraction f = 2^LENGTH('f)-1 then exponent f + 1
    else exponent f))" for f :: "('e,'f) float"
    unfolding float_defs
    apply transfer'
    apply clarsimp
    apply (auto split: if_splits simp: unat_eq_0 unat_minus_one degenerate_word_ne1 unat_minus_one_word)
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
    apply (auto split: if_splits simp: unat_eq_0 unat_minus_one degenerate_word_ne1 unat_minus_one_word)
    subgoal by (simp add: unat_minus_one_word word_eq_unatI)
    subgoal using unat_Suc2 by blast
    subgoal by (simp add: unat_minus_one_word word_eq_unatI)
    subgoal using unat_Suc2 by auto
    done
        
  lemmas next_float_defs = sign_next_float frac_next_float exp_next_float  
    
  lemma next_float_not_inf: "\<lbrakk>is_finite f; f \<noteq> topfloat\<rbrakk> \<Longrightarrow> \<not>is_infinity (next_float f)"
    unfolding is_infinity_def
    apply (simp add: next_float_defs)
    apply (auto simp: is_nan_def float_eq_conv)
    subgoal by (metis One_nat_def unsigned_1 unsigned_less)
    subgoal by (metis One_nat_def unsigned_1 unsigned_less)
    subgoal by (metis One_nat_def unsigned_1 unsigned_less)
    done

  lemma next_float_not_nan: "\<lbrakk>is_finite f; f \<noteq> topfloat\<rbrakk> \<Longrightarrow> \<not>is_nan (next_float f)"
    unfolding is_nan_def
    apply (simp add: next_float_defs)
    apply (auto simp: is_nan_def float_eq_conv)
    subgoal by (metis Suc_pred diff_le_self float_exp_le not_less_eq_eq)
    subgoal by (metis One_nat_def Suc_n_not_le_n Suc_pred emax_pos(1) float_exp_le)
    subgoal by (metis Suc_pred diff_le_self float_exp_le not_less_eq_eq)
    subgoal by (metis Suc_pred diff_le_self float_exp_le not_less_eq_eq)
    subgoal by (metis One_nat_def Suc_n_not_le_n Suc_pred emax_pos(1) float_exp_le)
    done
    
  lemma next_float_minus0: "next_float (-0) = 0"  
    by (simp add: float_eq_conv next_float_defs)
    
    
  find_theorems sign name: cases  
      
  lemma nat_gtZ_or_Z: "0<n \<or> n=0" for n :: nat by auto
  
  lemma gt_Z_le_1_conv: "0<n \<Longrightarrow> n\<le>Suc 0 \<longleftrightarrow> n=Suc 0" by auto
  
  lemma two_plen_gt1: "Suc 0 < 2 ^ LENGTH('f::len)"
    by (metis One_nat_def unat_lt2p unsigned_1)
  
  lemma nat_eqZ_cases: fixes n :: nat obtains "n=0" | "n>0" by blast 
    
  lemma next_float_aux:
    assumes "Suc 0 < e" 
    shows "2 ^ (e - Suc 0) * (1 + real (2 ^ F - Suc 0) / 2 ^ F) < 2 ^ e" (is "?a < ?b") 
  proof -
    have "1 + real (2 ^ F - Suc 0) / 2 ^ F < 2"
      by (auto simp: divide_less_eq)
    hence "?a < 2*2^(e-1)" by simp
    also have "\<dots> = 2^e" using assms by (metis gr_implies_not_zero power_eq_if)
    finally show ?thesis .
  qed
  
  lemma next_float_increases:
    fixes f :: "('e,'f) float"
    assumes "is_finite f" "f\<noteq>topfloat" "f\<noteq>-0" 
    shows "valof f < valof (next_float f)" 
    using assms
    apply (simp add: valof_eq next_float_defs)
    apply (clarsimp simp: float_defs float_eq_conv two_plen_gt1 nat_gtZ_or_Z)
    
    apply (cases f rule: sign_cases; simp)
    subgoal
      apply (cases "fraction f = 2 ^ LENGTH('f) - Suc 0"; cases "exponent f = 0"; simp add: nat_gtZ_or_Z)
      apply (simp_all add: divide_less_eq)
      done
    subgoal
      apply (cases "fraction f = 0"; simp add: gt_Z_le_1_conv)
      apply (intro conjI impI)
      apply (simp_all add: divide_less_eq next_float_aux)
      done
    done
    
    
  lemma next_float_tight_aux1: "\<lbrakk>f < f'; BF>0\<rbrakk> \<Longrightarrow> BF + real f * (BF) \<le> real f' * (BF)"  
    by (metis Groups.add_ac(2) Groups.mult_ac(2) Suc_eq_plus1 Suc_leI distrib_left less_eq_real_def mult.right_neutral mult_1s(1) mult_left_mono of_nat_add of_nat_mono of_nat_numeral) 
    
    
  lemma neg_le_posI: "\<lbrakk> a\<ge>0; b\<ge>0 \<rbrakk> \<Longrightarrow> -a\<le>b" for a b :: real by simp
  lemma not_pos_le_neg_conv: "\<lbrakk> a\<ge>0; b\<ge>0 \<rbrakk> \<Longrightarrow> a\<le>-b \<longleftrightarrow> a=0 \<and> b=0" for a b :: real by argo
  lemma not_pos_lt_negI: "\<lbrakk> a\<ge>0; b\<ge>0 \<rbrakk> \<Longrightarrow> \<not>a < -b" for a b :: real by argo
    
  lemma next_float_tight_aux2: "\<lbrakk>Suc 0 <  2 ^ F; 0<e';
     2 * real ( 2 ^ F - Suc 0) < real f' * 2 ^ e' + 2 ^ e' *  2 ^ F\<rbrakk>
    \<Longrightarrow> 2 * 2 ^ F \<le> real f' * 2 ^ e' + 2 ^ F * 2 ^ e'"
  proof goal_cases
    case 1
    
    from 1 have "(2::real)\<le>2^e'" by (cases e') auto
    hence "2*2^F \<le> (2^F :: real) * 2^e'" by simp
    then show ?case by (smt (verit) mult_nonneg_nonneg of_nat_0_le_iff zero_le_power)
  qed
  
  (* Attempt to compare two floats, component-wise *)

  (*  
  definition "fcc_le_samesign f f' \<longleftrightarrow> (
    exponent f < exponent f'
  \<or> (exponent f = exponent f' \<and> fraction f \<le> fraction f')
  )"
  
  definition "fcc_le f f' \<longleftrightarrow> (
    (is_zero f \<and> is_zero f')
  \<or> (sign f=1 \<and> sign f'=0)
  \<or> (sign f = sign f' \<and> sign f' = 0 \<and> fcc_le_samesign f f')  
  \<or> (sign f = sign f' \<and> sign f' = 1 \<and> fcc_le_samesign f' f)
  )"
  *)

  lemma denorm_less_norm_aux: "real (fraction f) * 2 < 2 ^ e * 2 ^ LENGTH('f)" if "0<e"
    for f :: "('e,'f) float"
  proof -
    have "real (fraction f) < 2^LENGTH('f)"
      by (simp add: fraction_upper_bound)
    hence "real (fraction f) * 2 < 2*2^LENGTH('f)" by linarith
    also have "(2::real)\<le>2^e" using \<open>0<e\<close> by (cases e) auto
    hence "(2::real)*2^LENGTH('f) \<le> 2^e * 2^LENGTH('f)" by auto
    finally show ?thesis .
  qed
  
  
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
  
  lemma fcc_le_cases:
    obtains 
      "is_zero f" "is_zero f'"
    | "\<not>(is_zero f \<and> is_zero f')" "sign f \<noteq> sign f'" 
    | "\<not>(is_zero f \<and> is_zero f')" "sign f = 0" "sign f'=0"
    | "\<not>(is_zero f \<and> is_zero f')" "sign f = 1" "sign f'=1"
    by (metis sign_convs(2))

  lemma fcc_le_aux1: "(a\<longrightarrow>\<not>b) \<Longrightarrow> a\<and>b\<longleftrightarrow>False" by blast 
    
  lemma finite_is_zero_iff_valof0: "is_finite f \<Longrightarrow> is_zero f \<longleftrightarrow> valof f = 0"
    by (auto simp: val_zero valof_eq_zero_conv is_zero_alt)
  
  lemma pos_le_ee_conv:
    fixes f f' :: "('e,'f) float"
    assumes [simp]: "sign f = 0" "sign f' = 0" "exponent f = exponent f'"
    shows "valof f \<le> valof f' \<longleftrightarrow> fraction f \<le> fraction f'"
    apply (auto simp add: valof_eq field_simps)
    done

  lemma pos_lt_ee_conv:
    fixes f f' :: "('e,'f) float"
    assumes [simp]: "sign f = 0" "sign f' = 0" "exponent f = exponent f'"
    shows "valof f < valof f' \<longleftrightarrow> fraction f < fraction f'"
    apply (auto simp add: valof_eq field_simps)
    done
    
    
  lemma exp_less_is_less:
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
          
    
    
  lemma pos_le_eltI:
    fixes f f' :: "('e,'f) float"
    assumes [simp]: "sign f = 0" "sign f' = 0" 
    assumes ELT: "exponent f < exponent f'"
    shows "valof f \<le> valof f'"
    using ELT
    apply (auto simp add: valof_eq exp_less_is_less[THEN less_imp_le])
    apply (auto simp add: valof_eq field_simps zero_compare_simps denorm_less_norm_aux[THEN less_imp_le]) []
    done

  lemma pos_lt_eltI:
    fixes f f' :: "('e,'f) float"
    assumes [simp]: "sign f = 0" "sign f' = 0" 
    assumes ELT: "exponent f < exponent f'"
    shows "valof f < valof f'"
    using ELT
    apply (auto simp add: valof_eq exp_less_is_less)
    apply (auto simp add: valof_eq field_simps zero_compare_simps denorm_less_norm_aux) []
    done
    
            
  lemma neg_le_ee_conv:
    fixes f f' :: "('e,'f) float"
    assumes [simp]: "sign f = 1" "sign f' = 1" "exponent f = exponent f'"
    shows "valof f \<le> valof f' \<longleftrightarrow> fraction f \<ge> fraction f'"
    apply (auto simp add: valof_eq field_simps)
    done

  lemma neg_le_eltI:
    fixes f f' :: "('e,'f) float"
    assumes [simp]: "sign f = 1" "sign f' = 1" 
    and ELT: "exponent f < exponent f'"
    shows "valof f \<ge> valof f'"
    using ELT
    apply (auto simp add: valof_eq exp_less_is_less[THEN less_imp_le])
    apply (auto simp add: valof_eq field_simps zero_compare_simps denorm_less_norm_aux[THEN less_imp_le])
    done
    
        
  lemma fcc_le_valof:
    fixes f f' :: "('e,'f) float"
    assumes [simp]: "is_finite f" "is_finite f'"  
    shows "fcc_le f f' \<longleftrightarrow> valof f \<le> valof f'"
  proof (cases f f' rule: fcc_le_cases; clarsimp simp: fcc_le_def fcc_le_aux1 finite_is_zero_iff_valof0)
    {
      assume ZERO: "valof f = 0 \<longrightarrow> valof f' \<noteq> 0"
      
      {
        assume SIGN: "sign f \<noteq> sign f'"
        show "(sign f = Suc 0 \<and> sign f' = 0) = (valof f \<le> valof f')"
          by (smt (z3) ZERO SIGN sign_convs(2) sign_convs(3) valof_nonneg valof_nonpos)
      
      }
      
      {
        assume S: "sign f = 0" "sign f' = 0"
        show "fcc_le_samesign f f' = (valof f \<le> valof f')"
          apply (auto simp add: fcc_le_samesign_def)
          subgoal by (simp add: S(1) S(2) pos_le_ee_conv)
          subgoal using S(1) S(2) pos_le_ee_conv by blast
          subgoal using S(1) S(2) pos_le_eltI by blast
          by (smt (verit) S(1) S(2) ZERO assms(1) assms(2) neqE pos_le_eltI val_zero valof_nonzero_injective)
      
      }
      
      {
        assume S: "sign f = Suc 0" "sign f' = Suc 0"
        show "fcc_le_samesign f' f = (valof f \<le> valof f')"
          apply (auto simp add: fcc_le_samesign_def)
          subgoal by (simp add: S(1) S(2) neg_le_ee_conv)
          subgoal by (simp add: S(1) S(2) neg_le_ee_conv)
          subgoal by (simp add: S(1) S(2) neg_le_eltI)
          by (smt (verit) One_nat_def S(1) S(2) ZERO assms(1) assms(2) neg_le_eltI neqE val_zero valof_nonzero_injective)
          
      }
    }
  qed      
  

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
  

  lemma fcc_lt_valof:
    fixes f f' :: "('e,'f) float"
    assumes [simp]: "is_finite f" "is_finite f'"  
    shows "fcc_lt f f' \<longleftrightarrow> valof f < valof f'"
  proof (cases f f' rule: fcc_le_cases; clarsimp simp: fcc_lt_def finite_is_zero_iff_valof0)
    {
      assume ZERO: "valof f = 0 \<longrightarrow> valof f' \<noteq> 0"
      
      {
        assume SIGN: "sign f \<noteq> sign f'"
        show "(sign f = Suc 0 \<and> sign f' = 0) = (valof f < valof f')"
          by (smt (z3) ZERO SIGN sign_convs(2) sign_convs(3) valof_nonneg valof_nonpos)
      
      }
      
      {
        assume S: "sign f = 0" "sign f' = 0"
        show "fcc_lt_samesign f f' = (valof f < valof f')"
          apply (auto simp add: fcc_lt_samesign_def)
          subgoal by (simp add: S(1) S(2) pos_lt_ee_conv)
          subgoal using S(1) S(2) pos_lt_ee_conv by blast
          subgoal using S(1) S(2) pos_lt_eltI by blast
          by (meson S(1) S(2) leD nat_neq_iff pos_le_eltI)
      
      }
      
      {
        assume S: "sign f = Suc 0" "sign f' = Suc 0"
        show "fcc_lt_samesign f' f = (valof f < valof f')"
          apply (auto simp add: fcc_lt_samesign_def)
          subgoal by (metis One_nat_def S(1) S(2) neg_le_ee_conv not_less)
          subgoal
            by (metis One_nat_def S(1) S(2) neg_le_ee_conv verit_comp_simplify1(3))
          subgoal
            by (metis One_nat_def S(1) S(2) ZERO assms(1) assms(2) leD neg_le_eltI not_less_iff_gr_or_eq val_zero valof_nonzero_injective)
          subgoal
            by (simp add: S(1) S(2) leD neg_le_eltI)
          done
      }
    }
  qed      
  
    
    
  
(*  
  lemma denorm_less_norm_aux: "real (fraction f) * 2 < 2 ^ e * 2 ^ LENGTH('f)" if "0<e"
    for f :: "('e,'f) float"
  proof -
    have "real (fraction f) < 2^LENGTH('f)"
      by (simp add: fraction_upper_bound)
    hence "real (fraction f) * 2 < 2*2^LENGTH('f)" by linarith
    also have "(2::real)\<le>2^e" using \<open>0<e\<close> by (cases e) auto
    hence "(2::real)*2^LENGTH('f) \<le> 2^e * 2^LENGTH('f)" by auto
    finally show ?thesis .
  qed
  
  lemma denorm_less_norm_aux': 
    "real (fraction f) * 2 < real (fraction f') * 2 ^ e + 2 ^ e * 2 ^ LENGTH('f)" if "0 < e"
    for f f' :: "('e,'f) float"
  proof -
    have "real (fraction f) < 2^LENGTH('f)"
      by (simp add: fraction_upper_bound)
    hence "real (fraction f) * 2 < 2*2^LENGTH('f)" by linarith
    also have "(2::real)\<le>2^e" using \<open>0<e\<close> by (cases e) auto
    hence "(2::real)*2^LENGTH('f) \<le> 2^e * 2^LENGTH('f)" by auto
    finally show ?thesis
      by (smt (verit, best) mult_nonneg_nonneg of_nat_0_le_iff zero_le_power)
  qed
*)  
  lemma pos_le_neg_conv: "\<lbrakk>a\<ge>0; b\<ge>0\<rbrakk> \<Longrightarrow> (a\<le>-b) \<longleftrightarrow> a=b \<and> b=0" for a b :: real by auto
  

  lemma next_float_finiteI: "\<lbrakk>is_finite f; f\<noteq>topfloat\<rbrakk> \<Longrightarrow> is_finite (next_float f)"
    apply (clarsimp simp: float_defs next_float_defs float_eq_conv)
    by (metis (no_types, lifting) Suc_lessI diff_Suc_Suc emax_ge1 less_eq_Suc_le less_imp_diff_less minus_nat.diff_0 two_plen_gt1)
    
    
  lemma float_frac_not_gt: "\<not>(2 ^ LENGTH('f) - Suc 0 < fraction f)" for f :: "('e,'f) float"
    using float_frac_le linorder_not_less by auto
    
  lemma float_frac_le': "fraction f \<le> 2 ^ LENGTH('f) - Suc 0" for f :: "('e,'f) float" 
    using float_frac_le by auto
    
  lemma next_float_tight: 
    fixes f f' :: "('e,'f) float"
    assumes "is_finite f" "f\<noteq>topfloat" 
    assumes "is_finite f'" 
    assumes "valof f < valof f'"
    shows "valof (next_float f) \<le> valof f'"
    
    using assms
    apply (simp flip: fcc_le_valof fcc_lt_valof add: next_float_finiteI)
    
    apply (cases f f' rule: fcc_le_cases; 
      clarsimp simp: fcc_lt_def fcc_le_def finite_is_zero_iff_valof0 next_float_defs
    )
    apply (auto 
      simp: fcc_le_samesign_def fcc_lt_samesign_def next_float_defs float_frac_le' float_frac_not_gt 
      split: if_splits)
    done
    
  xxx, ctd here:
    clean-up
    then use to verify rounded results
        
          
      
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
        by (smt (verit) divide_numeral_1 field_sum_of_halves le_divide_eq_1_pos less_one nonzero_mult_div_cancel_left numerals(1) power_0 power_eq_0_iff power_less_imp_less_exp power_one_right that(2) that(3))
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
