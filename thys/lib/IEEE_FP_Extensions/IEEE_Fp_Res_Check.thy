section \<open>Floating-Point Operation Result Checker\<close>
theory IEEE_Fp_Res_Check
imports IEEE_Fp_Nextfloat
begin


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
      by (metis assms(1) largest_gtZ'(1) valof_topfloat)
      
          
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
            by (simp add: FIN val_zero valof_eq_zero_conv)
        qed    
      }

      {
        assume A: "\<not>is_zero ?f"
      
        show "IEEE.round To_ninfinity r = f"
        proof (cases "f=-0")
          case True
          then show ?thesis
            by (metis A FINF INTERV(1) INTERV(2) LEN bprec_round_ninf float_class_consts(21) float_ineqs(13) is_zero_iff_valof0 next_float'_def valof_eq_zero_conv valof_zero(2))
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
      subgoal by (metis assms(1) largest_gtZ'(1) valof_topfloat)
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
      subgoal by (metis assms(1) largest_gtZ'(1) valof_topfloat)
      by (smt (verit, ccfv_SIG) Collect_cong LEN Orderings.order_eq_iff bottomfloat_eq_m_largest closest_precise_eqI finite_bottomfloat float_val_ge_largest float_val_le_largest is_zero_cases largest_gtZ mem_Collect_eq valof_topfloat valof_zero(1) valof_zero(2))

    have [simp]: "round float_To_zero (largest TYPE(('e, 'f) IEEE.float)) = (topfloat::('e, 'f) IEEE.float)"
      apply (auto simp flip: valof_topfloat[OF LEN])
      subgoal by (metis assms(1) largest_gtZ'(1) valof_topfloat)
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
          by (metis INTERV(1) INTERV(2) LEN bprec_round_zero_neg bprec_round_zero_pos float_class_consts(21) float_class_consts(26) float_class_consts(27) float_class_consts(38) nle_le valof_zero(1) valof_zero(2)) 
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
      apply (smt (verit) CLOSE FBOUNDS(1) LEN bottomfloat_eq_m_largest float_class_consts(27) float_class_consts(38) float_val_ge_bottomfloat is_close_def is_zero_iff_valof0 prev_float_finiteI valof_eq_zero_conv)
      by (smt (verit, del_insts) CLOSE FBOUNDS(2) LEN float_class_consts(27) float_ineqs(15) float_val_le_largest is_close_def next_float'_def next_float'_finiteI next_float_finiteI)
      
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
      by (smt (verit, ccfv_threshold) LEN bottomfloat_eq_m_largest float_class_consts(33) float_ineqs(13) float_ineqs(15) less_neq_topfloat next_float_tight next_prev_float_id prev_float_finiteI valof_almost_injective valof_eq_zero_conv valof_topfloat)
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
      by (smt (verit, best) LEN bottomfloat_eq_m_largest finite_bottomfloat float_class_consts(33) float_val_ge_bottomfloat largest_gtZ next_float_finiteI next_float_tight valof_topfloat)
    subgoal 
      apply (rule closest_unique_predI)
      apply blast
      apply (auto simp: is_closest_def)
      by (smt (verit, best) LEN bottomfloat_eq_m_largest float_class_consts(38) float_class_consts(39) float_eq_minus_minus_conv float_ineqs(13) float_neq_minus_self float_val_ge_largest next_float_increases next_float_tight valof_nonzero_injective)
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
      by (smt (verit) LEN abs_if closest_is_closest float_val_le_largest is_closest_def is_finite_nonempty mem_Collect_eq next_float'_finiteI next_float'_increases)
      
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
    
  export_code check_zs_r_sqrt checking SML
    
        
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

  

end



