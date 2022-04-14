theory IEEE_Bounds
imports IEEE_Fp_Add_Basic IEEE_Fp_Nextfloat "../LLVM_More_Word_Lemmas"
begin

  lemmas [simp] = valof_uminus

  lemma minus_eq_inf_conv[simp]: "-x = (\<infinity>::(_,_)float) \<longleftrightarrow> x=-\<infinity>"
    by (metis minus_minus_float)

  lemma threshold_pos: "threshold TYPE(('e,'f) float) > 0"
    unfolding threshold_def
    apply simp 
    apply (intro mult_pos_pos divide_pos_pos)
    apply (simp_all add: algebra_simps)
    by (smt (verit, best) le_divide_eq_1_pos less_nat_zero_code power_0 power_strict_increasing_iff)

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

  lemma round_zero[simp]: "IEEE.is_zero (round m 0 :: ('e::len2,'f) float)"  
    apply (cases m; simp)
    using threshold_pos[where 'e='e and 'f='f]
    apply (auto intro: closest_zero)
    done
  
  subsubsection \<open>Rounding and \<^const>\<open>valof\<close>\<close>    
  lemma valof_round_valof[simp]: "\<lbrakk> IEEE.is_finite x \<rbrakk> 
    \<Longrightarrow> valof (round m (valof x) :: ('e::len2,'f) float) = valof x" for x :: "('e::len2,'f) float"
    by (metis One_nat_def len2_simps(1) round_valof round_zero val_zero)

  definition "valof' f \<equiv> 
    if is_finite f then valof f 
    else if f=-\<infinity> then -\<infinity> 
    else if f=\<infinity> then \<infinity> 
    else undefined"

  lemma valof'_simps[simp]: 
    "is_finite f \<Longrightarrow> valof' f = ereal (valof f)" 
    "valof' \<infinity> = \<infinity>"
    "\<not>is_nan x \<Longrightarrow> valof' (-x) = - valof' x"
    apply (auto simp: valof'_def)
    by (cases x rule: float_cases'; auto simp: is_finite_def is_infinity_alt)
    
  lemma round_not_nan[simp, intro!]:
    shows "\<not>is_nan (round m x :: ('e::len2,'f) float)"
  proof -
    have 1: "is_finite x \<Longrightarrow> \<not>is_nan x" for x :: "('e::len2,'f) float"
      apply (cases x rule: float_cases')
      by auto
  
    show ?thesis
      by (cases m; simp; intro impI 1 finite_closest_valofI; auto)
  qed  

  lemma round_neq_the_nan[simp]: "(round m x :: ('e::len2,'f) float) \<noteq> the_nan xx"
    using round_not_nan[of m x]
    by (metis the_nan_is_nan)
  

  lemma round_to_pinf_aux1[simp]:
    assumes "\<not> largest TYPE(('e::len2, 'f) float) < x" 
    shows "is_finite (closest valof (\<lambda>a. True) {a. is_finite a \<and> x \<le> valof a} x :: ('e::len2, 'f) float)"
    using assms
    by (auto intro: finite_closest_valofI)
      
  lemma round_to_pinf_aux2[simp]:
    assumes "\<not> largest TYPE(('e::len2, 'f) float) < x" 
    shows "(closest valof (\<lambda>a. True) {a. is_finite a \<and> x \<le> valof a} x :: ('e::len2, 'f) float) \<noteq> - \<infinity>"
  proof - 
    from round_to_pinf_aux1[OF assms]
    show ?thesis by auto
  qed
    
  lemma round_to_ninf_aux1[simp]:
    assumes "\<not> x < -largest TYPE(('e::len2, 'f) float)"
    shows "is_finite (closest valof (\<lambda>a. True) {a. is_finite a \<and> valof a \<le> x} x :: ('e::len2, 'f) float)"
    using assms
    by (auto intro!: finite_closest_valofI)
    
  
    
  lemma round_pinf_bound: "x \<le> valof' (round To_pinfinity x :: ('e::len2,'f) float)"
    apply (auto simp: valof'_def valof_topfloat)
    by (smt (verit, best) Collect_empty_eq One_nat_def closest_eq_in_setD finite_topfloat len2_simps(1) mem_Collect_eq valof_topfloat)

  lemma round_ninf_bound: "valof' (round To_ninfinity x :: ('e::len2,'f) float) \<le> x"
    apply (auto simp: valof'_def valof_topfloat)
    by (smt (verit, best) Collect_empty_eq One_nat_def bottomfloat_eq_m_largest closest_eq_in_setD float_class_consts(39) len2_simps(1) mem_Collect_eq)
    
  lemma round_toZ_bound1: "0\<le>x \<Longrightarrow> valof' (round float_To_zero x :: ('e::len2,'f) float) \<le> x"
    apply (auto simp: valof'_def valof_topfloat)
    subgoal by (smt (verit, ccfv_threshold) largest_gtZ'(1))
    subgoal by (smt (verit, del_insts) Collect_empty_eq closest_eq_in_setD float_class_consts(21) float_class_consts(9) mem_Collect_eq valof_zero(1))
    subgoal by (smt (verit) largest_gtZ'(1))
    subgoal by (smt (verit) Collect_empty_eq closest_eq_in_setD float_class_consts(21) mem_Collect_eq valof_zero(1))
    subgoal by (metis (no_types, lifting) Collect_empty_eq abs_zero closest_eq_in_setD float_class_consts(21) mem_Collect_eq valof_zero(1))
    done

  lemma round_toZ_bound2: "x\<le>0 \<Longrightarrow> x\<le>valof' (round float_To_zero x :: ('e::len2,'f) float)"
    apply (auto simp: valof'_def valof_topfloat)
    subgoal by (smt (verit, ccfv_threshold) Collect_empty_eq abs_of_nonpos closest_eq_in_setD float_class_consts(15) float_class_consts(21) mem_Collect_eq valof_zero(1))
    subgoal by (smt (verit, del_insts) Collect_empty_eq closest_eq_in_setD float_class_consts(21) float_class_consts(9) mem_Collect_eq valof_zero(1))
    subgoal by (smt (verit, best) Collect_empty_eq closest_eq_in_setD float_class_consts(21) mem_Collect_eq valof_zero(1))
    done

    
  lemmas [simp del] = round.simps  
    
  lemma valof'_zerosign[simp]: "valof' (zerosign s x) = valof' x"
    unfolding zerosign_def by (auto simp: is_zero_alt)
    
  lemma zerosign_zerosimps[simp]:
    "is_zero f \<Longrightarrow> zerosign (Suc 0) f = -0"
    "is_zero f \<Longrightarrow> zerosign 0 f = 0"
    by (auto simp: zerosign_def)
    
  lemma zerosign_round_z[simp]: 
    "zerosign 0 (round m 0) = 0" 
    "zerosign (Suc 0) (round m 0) = -0" 
    by simp_all 
    
  lemma valof_round_zero[simp]:
    "valof (round m 0) = 0"
    by (simp add: val_zero)

  lemma valof'_round_zero[simp]:
    "valof' (round m 0) = 0"
    by (metis float_class_consts(21) valof'_simps(1) valof'_zerosign valof_zero(1) zero_ereal_def zerosign_round_z(1))
        
  definition ub :: "real \<Rightarrow> ('e::len2, 'f) float \<Rightarrow> bool"
    where "ub x f \<equiv> \<not>is_nan f \<and> ereal x \<le> valof' f"
  
  definition lb :: "real \<Rightarrow> ('e::len2, 'f) float \<Rightarrow> bool"
    where "lb x f \<equiv> \<not>is_nan f \<and> valof' f \<le> ereal x"
    
  lemma zerosign_eq_nan[simp]: "zerosign s f = the_nan x \<longleftrightarrow> f=the_nan x"  
    by (auto simp: zerosign_def)

    
  lemma round_pinf_bound': "a\<le>b \<Longrightarrow> a \<le> valof' (IEEE.round To_pinfinity b :: ('e::len2, 'f) float)"      
    by (meson dual_order.trans round_pinf_bound)
    
  lemma round_ninf_bound': "a\<le>b \<Longrightarrow> valof' (IEEE.round To_ninfinity a :: ('e::len2, 'f) float) \<le> b"
    using le_ereal_le round_ninf_bound by blast
    
  lemma fadd_ub: "\<lbrakk> ub x\<^sub>1 f\<^sub>1; ub x\<^sub>2 f\<^sub>2 \<rbrakk> \<Longrightarrow> ub (x\<^sub>1+x\<^sub>2) (fadd To_pinfinity f\<^sub>1 f\<^sub>2)"
    unfolding ub_def
    apply (cases f\<^sub>1 rule: float_cases_eqs; cases f\<^sub>2 rule: float_cases_eqs)
    by (auto simp: fadd_def intro!: round_pinf_bound')

  lemma fadd_lb: "\<lbrakk> lb x\<^sub>1 f\<^sub>1; lb x\<^sub>2 f\<^sub>2 \<rbrakk> \<Longrightarrow> lb (x\<^sub>1+x\<^sub>2) (fadd To_ninfinity f\<^sub>1 f\<^sub>2)"
    unfolding lb_def
    apply (cases f\<^sub>1 rule: float_cases_eqs; cases f\<^sub>2 rule: float_cases_eqs)
    by (auto simp: fadd_def intro!: round_ninf_bound')
    
    
  lemma fmul_ub_pos: 
    fixes f\<^sub>1 f\<^sub>2 :: "('e::len2,'f) float"
    shows "\<lbrakk> \<not>is_infinity f\<^sub>1; 0<x\<^sub>1; 0<x\<^sub>2; ub x\<^sub>1 f\<^sub>1; ub x\<^sub>2 f\<^sub>2 \<rbrakk> 
      \<Longrightarrow> ub (x\<^sub>1*x\<^sub>2) (fmul To_pinfinity f\<^sub>1 f\<^sub>2)"
    unfolding ub_def
    apply (cases f\<^sub>1 rule: float_cases_eqs; cases f\<^sub>2 rule: float_cases_eqs; simp)
    apply (auto simp: fmul_def mult_nonneg_nonpos mult_mono' sign_pos_iff_valof intro!: round_pinf_bound')
    done

  lemma fmul_lb_pos: 
    fixes f\<^sub>1 f\<^sub>2 :: "('e::len2,'f) float"
    shows "\<lbrakk> \<not>is_infinity f\<^sub>1; 0\<le>valof' f\<^sub>1; 0\<le>valof' f\<^sub>2; lb x\<^sub>1 f\<^sub>1; lb x\<^sub>2 f\<^sub>2 \<rbrakk> 
      \<Longrightarrow> lb (x\<^sub>1*x\<^sub>2) (fmul To_ninfinity f\<^sub>1 f\<^sub>2)"
    unfolding lb_def
    apply (cases f\<^sub>1 rule: float_cases_eqs; cases f\<^sub>2 rule: float_cases_eqs; simp)
    apply (auto 
      simp: fmul_def mult_nonneg_nonpos mult_mono' sign_pos_iff_valof
      intro!: round_ninf_bound')
    done

  lemma fmul_add_ub_pos1:    
    fixes f\<^sub>1 f\<^sub>2 f\<^sub>3 :: "('e::len2,'f) float"
    shows "\<lbrakk> \<not>is_infinity f\<^sub>1; 0<x\<^sub>1; 0\<le>x\<^sub>2; 0\<le>x\<^sub>3; ub x\<^sub>1 f\<^sub>1; ub x\<^sub>2 f\<^sub>2; ub x\<^sub>3 f\<^sub>3 \<rbrakk> \<Longrightarrow> 
      ub (x\<^sub>1*x\<^sub>2 + x\<^sub>3) (fmul_add To_pinfinity f\<^sub>1 f\<^sub>2 f\<^sub>3)"
    unfolding ub_def
    apply (subgoal_tac "sign f\<^sub>1 = 0")
    apply (rule conjI)
    subgoal
      apply (cases f\<^sub>1 rule: float_cases_eqs; simp; cases f\<^sub>2 rule: float_cases_eqs; simp; cases f\<^sub>3 rule: float_cases_eqs; simp)
      by (auto simp: fmul_add_def Let_def)
    subgoal
      unfolding fmul_add_def
      apply (rewrite Let_def)
      apply (rewrite Let_def)
      apply (simp)
      apply (intro impI conjI)
      apply (auto simp: is_zero_alt is_infinity_alt)
      subgoal
        unfolding Let_def if_distrib[of valof']
        apply (simp split del: if_split cong: if_cong)
        apply (auto intro!: round_pinf_bound')
        subgoal by (smt (verit) ereal_less_eq(3) float_cases_finite is_infinity_alt mult_mono valof'_def zero_ereal_def)
        subgoal by (smt (verit) ereal_less_eq(3) float_cases_finite is_infinity_alt mult_mono valof'_def zero_ereal_def)
        done
      subgoal
        unfolding Let_def if_distrib[of valof']
        apply (simp split del: if_split cong: if_cong)
        apply (auto intro!: round_pinf_bound')
        subgoal by (smt (verit) ereal_less_eq(3) float_cases_finite is_infinity_alt mult_mono valof'_def zero_ereal_def)
        subgoal by (smt (verit) ereal_less_eq(3) float_cases_finite is_infinity_alt mult_mono valof'_def zero_ereal_def)
        done
      done
    subgoal using float_cases_finite valof_nonpos by fastforce   
  done  
      
  lemma fmul_add_ub_pos2:    
    fixes f\<^sub>1 f\<^sub>2 f\<^sub>3 :: "('e::len2,'f) float"
    shows "\<lbrakk> \<not>is_infinity f\<^sub>1; 0<x\<^sub>1; 0<x\<^sub>2; ub x\<^sub>1 f\<^sub>1; ub x\<^sub>2 f\<^sub>2; ub x\<^sub>3 f\<^sub>3 \<rbrakk> \<Longrightarrow> 
      ub (x\<^sub>1*x\<^sub>2 + x\<^sub>3) (fmul_add To_pinfinity f\<^sub>1 f\<^sub>2 f\<^sub>3)"
    unfolding ub_def
    apply (cases f\<^sub>1 rule: float_cases_eqs; simp; cases f\<^sub>2 rule: float_cases_eqs; simp; cases f\<^sub>3 rule: float_cases_eqs; simp)
    apply (auto
      simp: fmul_add_def Let_def mult_nonneg_nonpos mult_mono' sign_pos_iff_valof field_simps
      simp: add_mono 
      intro!: round_pinf_bound'
      elim!: add_decreasing[of _ "_*_" "_*_"]
      )
    using mult_mono' by fastforce
    
    
  lemma fmul_add_lb_nneg:    
    fixes f\<^sub>1 f\<^sub>2 f\<^sub>3 :: "('e::len2,'f) float"
    shows "\<lbrakk> \<not>is_infinity f\<^sub>1; 0\<le>valof' f\<^sub>1; 0\<le>valof' f\<^sub>2; lb x\<^sub>1 f\<^sub>1; lb x\<^sub>2 f\<^sub>2; lb x\<^sub>3 f\<^sub>3 \<rbrakk> \<Longrightarrow> 
      lb (x\<^sub>1*x\<^sub>2 + x\<^sub>3) (fmul_add To_ninfinity f\<^sub>1 f\<^sub>2 f\<^sub>3)"
    unfolding lb_def
    apply (rule conjI)
    subgoal
      apply (auto simp: fmul_add_def)
      apply (auto simp add: Let_def is_zero_alt is_infinity_alt split: if_splits)
      done
    subgoal
      unfolding fmul_add_def
      apply (rewrite Let_def)
      apply (rewrite Let_def)
      apply (simp)
      apply (intro impI conjI)
      apply (auto simp: is_zero_alt is_infinity_alt)
      subgoal
        unfolding Let_def if_distrib[of valof']
        apply (simp split del: if_split cong: if_cong)
        apply (auto intro!: round_ninf_bound')
        subgoal by (smt (verit) ereal_less_eq(3) float_cases_finite is_infinity_alt mult_mono valof'_def zero_ereal_def)
        subgoal by (smt (verit, ccfv_SIG) ereal_less_eq(3) ereal_less_eq(5) float_cases_finite is_infinity_alt mult_mono' valof'_simps(1))
        done
      subgoal
        unfolding Let_def if_distrib[of valof']
        apply (simp split del: if_split cong: if_cong)
        apply (auto intro!: round_ninf_bound')
        subgoal by (smt (verit) ereal_less_eq(3) float_cases_finite is_infinity_alt mult_mono valof'_def zero_ereal_def)
        subgoal by (smt (verit, ccfv_SIG) ereal_less_eq(3) ereal_less_eq(5) float_cases_finite is_infinity_alt mult_mono' valof'_simps(1))
        done
      done
    done
          
  lemma add_upper_bound': "\<lbrakk> \<not>is_nan x; \<not>is_nan y; x\<noteq>-\<infinity>; y\<noteq>-\<infinity> \<rbrakk> \<Longrightarrow>
    valof x + valof y \<le> valof' (fadd To_pinfinity x y)" for x y :: "('e::len2,'f) float"
    apply (auto simp add: fadd_def is_infinity_alt)
    apply (rule order_trans[OF _ round_pinf_bound])
    apply (subgoal_tac "is_finite x \<and> is_finite y")
    apply simp
    using float_cases_finite[of x] float_cases_finite[of y] by (auto simp: is_infinity_alt)
    
  lemma sub_upper_bound': "\<lbrakk> \<not>is_nan x; \<not>is_nan y; x\<noteq>-\<infinity>; y\<noteq>\<infinity> \<rbrakk> \<Longrightarrow>
    valof x - valof y \<le> valof' (fsub To_pinfinity x y)" for x y :: "('e::len2,'f) float"
    apply (auto simp add: fsub_def is_infinity_alt)
    apply (rule order_trans[OF _ round_pinf_bound])
    apply (subgoal_tac "is_finite x \<and> is_finite y")
    apply simp
    using float_cases_finite[of x] float_cases_finite[of y] by (auto simp: is_infinity_alt)
    
  lemma mul_upper_bound': "\<lbrakk> \<not>is_nan x; \<not>is_nan y; \<not>is_infinity x; \<not>is_infinity y \<rbrakk> \<Longrightarrow>
    valof x * valof y \<le> valof' (fmul To_pinfinity x y)" for x y :: "('e::len2,'f) float"
    apply (auto simp add: fmul_def is_infinity_alt is_zero_alt)
    apply (rule order_trans[OF _ round_pinf_bound])
    apply (subgoal_tac "is_finite x \<and> is_finite y")
    apply simp
    using float_cases_finite[of x] float_cases_finite[of y] 
    by (auto simp: is_infinity_alt)
    
    
    
    
    
    

end
