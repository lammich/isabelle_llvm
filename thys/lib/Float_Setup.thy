theory Float_Setup
imports "Isabelle_LLVM.IICF" "Isabelle_LLVM.IEEE_Bounds"
begin

  lemmas[simp del] = IEEE.round.simps

  lemma P_ifI:"(x \<Longrightarrow> P a) \<Longrightarrow> (\<not>x \<Longrightarrow> P b) \<Longrightarrow> P (if x then a else b)"
    by simp

  lemma mult_add_ge_0: "a * b + c = 0 \<Longrightarrow> a \<ge> 0 \<Longrightarrow> b \<ge> 0 \<Longrightarrow> c \<ge> 0 \<Longrightarrow> (a = 0 \<or> b = 0) \<and> (c::_::linordered_semiring_strict) = 0"
    by (metis add_nonneg_eq_0_iff antisym_conv2 mult_nonneg_nonneg mult_pos_pos)
  
  lemma valof'_finite_to_valof: "ereal r \<le> valof' fl \<Longrightarrow> is_finite fl \<Longrightarrow> r \<le> valof fl"
    unfolding valof'_def by simp

  lemma exp_le_float: "exponent a \<le> emax TYPE(('e, 'f)float) - 1 \<Longrightarrow> is_finite a"
    for a::"('e, 'f)float"
    unfolding float_defs
    by auto

  lemma nnan_ninf_eq_fin [simp]: "\<not>is_nan fl \<Longrightarrow> (\<not>is_infinity fl) = is_finite fl"
    using float_cases_finite  using finite_infinity by blast

  lemma nnan_nfin_eq_inf [simp]: "\<not>is_nan fl \<Longrightarrow> (\<not>is_finite fl) = is_infinity fl"
    using float_cases_finite  using finite_infinity by blast

  lemma round_zero_zero: "IEEE.round m 0 = (0 :: ('e,'f) float) \<or> IEEE.round m 0 = (-0 :: ('e,'f) float)"
    using is_zero_alt is_zero_round_zero by blast

  lemma valof'_round_valof:
    fixes fl::"('e::len2,'f) float"
    assumes FIN: "is_finite fl"
    shows "valof' (IEEE.round m (valof fl)::('e::len2,'f) float) = valof' fl"
    unfolding valof'_def
    apply(cases "is_zero fl")
    subgoal
      using assms round_zero_zero[of m, where 'e='e and 'f='f] 
      by (auto dest!: val_zero)
    subgoal
      using assms round_valof[OF FIN, of m] by auto 
    done

  lemma fin_inf_contr: "is_finite fl \<Longrightarrow> is_infinity fl \<Longrightarrow> False"
    using finite_infinity by blast

  lemma fin_inf_any: "is_finite fl \<Longrightarrow> is_infinity fl \<Longrightarrow> P"
    using finite_infinity by blast

  lemma pinf_is_infinity: "fl = \<infinity> \<Longrightarrow> is_infinity fl"
    by blast
  lemma ninf_is_infinity: "fl = -\<infinity> \<Longrightarrow> is_infinity fl"
    by blast

  lemma is_finite_npinf:"is_finite fl \<Longrightarrow> fl \<noteq> \<infinity>" 
    by fastforce
  lemma is_finite_nninf:"is_finite fl \<Longrightarrow> fl \<noteq> -\<infinity>" 
    by fastforce





  lemma "exponent (Abs_float (s,e,f)) = unat e"
  by (simp add: exponent.abs_eq)

  lemma sign_1[simp]: "sign (1::('e,'f) float) = 0"
    unfolding one_float_def by (auto simp: sign.abs_eq)

  lemma exponent_1: "exponent (1::('e,'f) float) = 2 ^ (LENGTH('e) - 1) - 1"
    unfolding one_float_def by (auto simp: exponent.abs_eq unat_minus_one)

  lemma fraction_1[simp]: "fraction (1::('e,'f) float) = 0"
    unfolding one_float_def by (auto simp: fraction.abs_eq)

  lemma minus_minus_2_pow: "(2 ^ (x - 1) - 1 :: nat) \<le> 2 ^ x - 2"
    apply(induction x) by auto

  lemma is_finite_1[simp]: "is_finite (1::('e,'f) float)"
    using minus_minus_2_pow[of "LENGTH('e)"]
    by (auto intro: exp_le_float simp: exponent_1 emax_def unat_minus_one_word )

  lemma nnan_1[simp]: "\<not>is_nan (1::('e,'f) float)"
    using is_finite_1 nan_not_finite by blast


  section \<open>Double assn and basic operations\<close>

  definition "dfloat_rel = br float_of_double (\<lambda>x. True)"

  abbreviation "dfloat_assn \<equiv> pure dfloat_rel"

  abbreviation "dfloat_intv_assn \<equiv> dfloat_assn \<times>\<^sub>a dfloat_assn"

  lemma dfloat_intv_assn_alt: "dfloat_intv_assn = pure (dfloat_rel \<times>\<^sub>r dfloat_rel)"
    by simp

  lemma mk_free_dfloat_assn[sepref_frame_free_rules]: "MK_FREE dfloat_assn (\<lambda>_. return\<^sub>M ())"
    apply(rule mk_free_is_pure) 
    by simp


  definition nanize_float where "nanize_float x \<equiv> if is_nan x then SPEC is_nan else RETURN x"
  lemma nanize_float_simps[simp]: 
    "\<not>is_nan x \<Longrightarrow> nanize_float x = RETURN x"
    "is_nan x \<Longrightarrow> nanize_float x = (SPEC is_nan)"
    unfolding nanize_float_def
    by auto

  definition op_farith1_rm :: "(roundmode \<Rightarrow> ('a::len, 'b::len) IEEE.float \<Rightarrow> ('a, 'b) IEEE.float) \<Rightarrow> roundmode \<Rightarrow> ('a, 'b) IEEE.float \<Rightarrow> ('a, 'b) IEEE.float nres" 
    where "op_farith1_rm f rm a \<equiv> nanize_float (f rm a)"
  definition op_farith2_rm :: "(roundmode \<Rightarrow> ('a::len, 'b::len) IEEE.float \<Rightarrow> ('a, 'b) IEEE.float \<Rightarrow> ('a, 'b) IEEE.float) \<Rightarrow> roundmode \<Rightarrow> ('a, 'b) IEEE.float \<Rightarrow> ('a, 'b) IEEE.float \<Rightarrow> ('a, 'b) IEEE.float nres" 
    where "op_farith2_rm f rm a b \<equiv> nanize_float (f rm a b)"
  definition op_farith3_rm :: "(roundmode \<Rightarrow> ('a::len, 'b::len) IEEE.float \<Rightarrow> ('a::len, 'b::len) IEEE.float \<Rightarrow> ('a, 'b) IEEE.float \<Rightarrow> ('a, 'b) IEEE.float) \<Rightarrow> roundmode \<Rightarrow> ('a::len, 'b::len) IEEE.float \<Rightarrow> ('a, 'b) IEEE.float \<Rightarrow> ('a, 'b) IEEE.float \<Rightarrow> ('a, 'b) IEEE.float nres" 
    where "op_farith3_rm f rm a b c \<equiv> nanize_float (f rm a b c)"

  lemma is_nan_float_of_double: "is_nan_double x \<longleftrightarrow> is_nan (float_of_double x)"
    apply transfer by simp

  lemma float_of_double_dradd: "float_of_double (dradd rm a b) = fadd rm (float_of_double a) (float_of_double b)"
    apply transfer by simp

  lemma float_of_double_drsub: "float_of_double (drsub rm a b) = fsub rm (float_of_double a) (float_of_double b)"
    apply transfer by simp

  lemma float_of_double_drmul: "float_of_double (drmul rm a b) = fmul rm (float_of_double a) (float_of_double b)"
    apply transfer by simp

  lemma float_of_double_drfmadd: "float_of_double (drfmadd rm a b c) = fmul_add rm (float_of_double a) (float_of_double b) (float_of_double c)"
    apply transfer by simp

  lemma is_nan_double_neq_bot: "is_nan_double \<noteq> bot"
    using is_nan_double.abs_eq by fastforce


  subsection \<open>Round up operations\<close>
  
  definition mop_add_rup :: "('e::len2, 'f) float \<Rightarrow> ('e::len2, 'f) float \<Rightarrow> ('e::len2, 'f) float nres" where 
    "mop_add_rup = op_farith2_rm fadd To_pinfinity"
  sepref_register mop_add_rup

  definition mop_sub_rup :: "('e::len2, 'f) float \<Rightarrow> ('e::len2, 'f) float \<Rightarrow> ('e::len2, 'f) float nres" where
    "mop_sub_rup = op_farith2_rm fsub To_pinfinity"
  sepref_register mop_sub_rup

  definition mop_mul_rup :: "('e::len2, 'f) float \<Rightarrow> ('e::len2, 'f) float \<Rightarrow> ('e::len2, 'f) float nres" where 
    "mop_mul_rup = op_farith2_rm fmul To_pinfinity"
  sepref_register mop_mul_rup

  definition mop_fma_rup :: "('e::len2, 'f) float \<Rightarrow> ('e::len2, 'f) float \<Rightarrow> ('e::len2, 'f) float \<Rightarrow> ('e::len2, 'f) float nres" where
    "mop_fma_rup = op_farith3_rm fmul_add To_pinfinity"
  sepref_register mop_fma_rup


  lemma mop_add_rup_hnr[sepref_fr_rules]: "(uncurry (ll_x86_avx512_add_sd_round AVX512_FROUND_TO_POS_INF_NO_EXC), uncurry (mop_add_rup)) \<in> dfloat_assn\<^sup>k *\<^sub>a dfloat_assn\<^sup>k \<rightarrow>\<^sub>a dfloat_assn"
    apply(sepref_to_hoare)
    unfolding op_lift_farith2_rm_d_def xlate_rounding_mode_def nanize_double_def ndet_nan_double_def ll_x86_avx512_add_sd_round_def
    unfolding op_farith2_rm_def dfloat_rel_def mop_add_rup_def
    supply [simp] = is_nan_float_of_double float_of_double_dradd is_nan_double_neq_bot in_br_conv
    supply [split] = if_split_asm
    by vcg

  lemma mop_sub_rup_hnr[sepref_fr_rules]: "(uncurry (ll_x86_avx512_sub_sd_round AVX512_FROUND_TO_POS_INF_NO_EXC), uncurry (mop_sub_rup)) \<in> dfloat_assn\<^sup>k *\<^sub>a dfloat_assn\<^sup>k \<rightarrow>\<^sub>a dfloat_assn"
    apply(sepref_to_hoare)
    unfolding op_lift_farith2_rm_d_def xlate_rounding_mode_def nanize_double_def ndet_nan_double_def ll_x86_avx512_sub_sd_round_def
    unfolding op_farith2_rm_def dfloat_rel_def mop_sub_rup_def
    supply [simp] = is_nan_float_of_double float_of_double_drsub is_nan_double_neq_bot in_br_conv
    supply [split] = if_split_asm
    by vcg

  lemma mop_mul_rup_hnr[sepref_fr_rules]: "(uncurry (ll_x86_avx512_mul_sd_round AVX512_FROUND_TO_POS_INF_NO_EXC), uncurry (mop_mul_rup)) \<in> dfloat_assn\<^sup>k *\<^sub>a dfloat_assn\<^sup>k \<rightarrow>\<^sub>a dfloat_assn"
    apply(sepref_to_hoare)
    unfolding ll_x86_avx512_mul_sd_round_def op_lift_farith2_rm_d_def xlate_rounding_mode_def nanize_double_def ndet_nan_double_def
    unfolding op_farith2_rm_def dfloat_rel_def mop_mul_rup_def 
    supply [simp] = is_nan_float_of_double float_of_double_drmul is_nan_double_neq_bot in_br_conv
    by vcg

  lemma mop_fma_rup_hnr[sepref_fr_rules]: "(uncurry2 (ll_x86_avx512_vfmadd_f64 AVX512_FROUND_TO_POS_INF_NO_EXC), uncurry2 (mop_fma_rup)) \<in> dfloat_assn\<^sup>k *\<^sub>a dfloat_assn\<^sup>k *\<^sub>a dfloat_assn\<^sup>k \<rightarrow>\<^sub>a dfloat_assn"
    apply(sepref_to_hoare)
    unfolding ll_x86_avx512_vfmadd_f64_def op_lift_farith3_rm_d_def xlate_rounding_mode_def nanize_double_def ndet_nan_double_def
    unfolding mop_fma_rup_def op_farith3_rm_def dfloat_rel_def
    supply [simp] = is_nan_double_neq_bot is_nan_float_of_double float_of_double_drfmadd in_br_conv
    by vcg

  definition add_floats_up :: "float64 \<Rightarrow> _" where "add_floats_up a b c = do{
    d \<leftarrow> mop_add_rup a b;
    e \<leftarrow> mop_mul_rup c d;
    mop_fma_rup d e a
  }"

  sepref_def add_floats_up_ll is "uncurry2 add_floats_up" :: "dfloat_assn\<^sup>k *\<^sub>a dfloat_assn\<^sup>k *\<^sub>a dfloat_assn\<^sup>k \<rightarrow>\<^sub>a dfloat_assn"
    unfolding add_floats_up_def
    apply sepref
    done

  declare [[llc_compile_avx512f=true]]

  export_llvm add_floats_up_ll 



  subsection \<open>Round down operations\<close>

  definition mop_add_rdn :: "('e::len2, 'f) float \<Rightarrow> ('e::len2, 'f) float \<Rightarrow> ('e::len2, 'f) float nres" where
    "mop_add_rdn = op_farith2_rm fadd To_ninfinity"
  sepref_register mop_add_rdn

  definition mop_sub_rdn :: "('e::len2, 'f) float \<Rightarrow> ('e::len2, 'f) float \<Rightarrow> ('e::len2, 'f) float nres" where
    "mop_sub_rdn = op_farith2_rm fsub To_ninfinity"
  sepref_register mop_sub_rdn

  definition mop_mul_rdn :: "('e::len2, 'f) float \<Rightarrow> ('e::len2, 'f) float \<Rightarrow> ('e::len2, 'f) float nres" where
    "mop_mul_rdn = op_farith2_rm fmul To_ninfinity"
  sepref_register mop_mul_rdn

  definition mop_fma_rdn :: "('e::len2, 'f) float \<Rightarrow> ('e::len2, 'f) float \<Rightarrow> ('e::len2, 'f) float \<Rightarrow> ('e::len2, 'f) float nres" where 
    "mop_fma_rdn = op_farith3_rm fmul_add To_ninfinity"
  sepref_register mop_fma_rdn

  lemma mop_add_rdn_hnr[sepref_fr_rules]: "(uncurry (ll_x86_avx512_add_sd_round AVX512_FROUND_TO_NEG_INF_NO_EXC), uncurry (mop_add_rdn)) \<in> dfloat_assn\<^sup>k *\<^sub>a dfloat_assn\<^sup>k \<rightarrow>\<^sub>a dfloat_assn"
    apply(sepref_to_hoare)
    unfolding op_lift_farith2_rm_d_def xlate_rounding_mode_def nanize_double_def ndet_nan_double_def ll_x86_avx512_add_sd_round_def
    unfolding op_farith2_rm_def dfloat_rel_def mop_add_rdn_def
    supply [simp] = is_nan_float_of_double float_of_double_dradd is_nan_double_neq_bot in_br_conv
    supply [split] = if_split_asm
    by vcg

  (*No refinement from real implemented yet (only round up)*)
  lemma mop_sub_rdn_hnr[sepref_fr_rules]: "(uncurry (ll_x86_avx512_sub_sd_round AVX512_FROUND_TO_NEG_INF_NO_EXC), uncurry (mop_sub_rdn)) \<in> dfloat_assn\<^sup>k *\<^sub>a dfloat_assn\<^sup>k \<rightarrow>\<^sub>a dfloat_assn"
    apply(sepref_to_hoare)
    unfolding op_lift_farith2_rm_d_def xlate_rounding_mode_def nanize_double_def ndet_nan_double_def ll_x86_avx512_sub_sd_round_def
    unfolding op_farith2_rm_def dfloat_rel_def mop_sub_rdn_def
    supply [simp] = is_nan_float_of_double float_of_double_drsub is_nan_double_neq_bot in_br_conv
    supply [split] = if_split_asm
    by vcg

  lemma mop_mul_rdn_hnr[sepref_fr_rules]: "(uncurry (ll_x86_avx512_mul_sd_round AVX512_FROUND_TO_NEG_INF_NO_EXC), uncurry (mop_mul_rdn)) \<in> dfloat_assn\<^sup>k *\<^sub>a dfloat_assn\<^sup>k \<rightarrow>\<^sub>a dfloat_assn"
    apply(sepref_to_hoare)
    unfolding ll_x86_avx512_mul_sd_round_def op_lift_farith2_rm_d_def xlate_rounding_mode_def nanize_double_def ndet_nan_double_def
    unfolding op_farith2_rm_def dfloat_rel_def mop_mul_rdn_def 
    supply [simp] = is_nan_float_of_double float_of_double_drmul is_nan_double_neq_bot in_br_conv
    by vcg

  lemma mop_fma_rdn_hnr[sepref_fr_rules]: "(uncurry2 (ll_x86_avx512_vfmadd_f64 AVX512_FROUND_TO_NEG_INF_NO_EXC), uncurry2 (mop_fma_rdn)) \<in> dfloat_assn\<^sup>k *\<^sub>a dfloat_assn\<^sup>k *\<^sub>a dfloat_assn\<^sup>k \<rightarrow>\<^sub>a dfloat_assn"
    apply(sepref_to_hoare)
    unfolding ll_x86_avx512_vfmadd_f64_def op_lift_farith3_rm_d_def xlate_rounding_mode_def nanize_double_def ndet_nan_double_def
    unfolding mop_fma_rdn_def op_farith3_rm_def dfloat_rel_def
    supply [simp] = is_nan_double_neq_bot is_nan_float_of_double float_of_double_drfmadd in_br_conv
    by vcg

  definition add_floats_dn :: "float64 \<Rightarrow> _" where "add_floats_dn a b c = do{
    d \<leftarrow> mop_add_rdn a b;
    e \<leftarrow> mop_mul_rdn c d;
    mop_fma_rdn d e a
  }"

  sepref_def add_floats_dn_ll is "uncurry2 add_floats_dn" :: "dfloat_assn\<^sup>k *\<^sub>a dfloat_assn\<^sup>k *\<^sub>a dfloat_assn\<^sup>k \<rightarrow>\<^sub>a dfloat_assn"
    unfolding add_floats_dn_def
    apply sepref
    done

  experiment
  begin
    declare [[llc_compile_avx512f=true]]
    export_llvm add_floats_dn_ll 
  end  

  subsection \<open>Constants\<close>


  lemma float_of_fp64_hnr[sepref_fr_rules]: "(Mreturn o double_of_word, RETURN o float_of_fp64) \<in> word_assn\<^sup>k \<rightarrow>\<^sub>a dfloat_assn"
    apply(sepref_to_hoare)
    unfolding dfloat_rel_def in_br_conv
    apply vcg' 
    apply transfer 
    apply (rule refl)
    done

  definition "word_float_test = do{
    let a = float_of_fp64 0x3FE0000000000000;
    let b = float_of_fp64 0x4004000000000000;
    mop_mul_rdn a b
  }"

  experiment
  begin
    sepref_def word_float_test_ll is "uncurry0 word_float_test" :: "unit_assn\<^sup>k \<rightarrow>\<^sub>a dfloat_assn"
      unfolding word_float_test_def
      apply sepref
      done
  
    export_llvm word_float_test_ll
  end

  subsubsection \<open>Zero\<close>

  definition "op_fp64_0 = float_of_fp64 0x0000000000000000"

  lemma valof_fp64_0[simp]: "valof (op_fp64_0) = 0"
    by (simp add: op_fp64_0_def)

  lemma is_finite_op_fp64_0[simp]: "is_finite op_fp64_0"
    unfolding op_fp64_0_def by simp

  lemma not_infinity_op_fp64_0[simp]: "\<not>is_infinity op_fp64_0"
    unfolding op_fp64_0_def by simp

  lemma valof'_fp64_0[simp]: "valof' (op_fp64_0) = 0"
    unfolding valof'_def by auto

  lemma nnan_op_fp64_0[simp]: "\<not>is_nan op_fp64_0"
    unfolding op_fp64_0_def by simp

  lemma sign_op_fp64_0[simp]: "sign op_fp64_0 = 0"
    unfolding op_fp64_0_def by simp

  sepref_def op_fp64_0_ll [llvm_inline] is "uncurry0 (RETURN op_fp64_0)" :: "unit_assn\<^sup>k \<rightarrow>\<^sub>a dfloat_assn"
    unfolding word_float_test_def op_fp64_0_def
    apply sepref
    done


  subsubsection \<open>One\<close>
  
  definition "op_fp64_1 = float_of_fp64 0x3FF0000000000000"
  
  lemma float_of_fp64_1:"(1 :: (11, 52) IEEE.float) = op_fp64_1"
    unfolding float_of_fp64_def float_of_word_def one_float_def word_split_def op_fp64_1_def
    by simp

  lemma valof_fp64_1[simp]: "valof (op_fp64_1) = 1"
    using float_of_fp64_1 by simp

  lemma is_finite_op_fp64_1[simp]: "is_finite op_fp64_1"
    by (simp flip: float_of_fp64_1)

  lemma not_infinity_op_fp64_1[simp]: "\<not>is_infinity op_fp64_1"
    by (simp flip: float_of_fp64_1)

  lemma valof'_fp64_1[simp]: "valof' (op_fp64_1) = 1"
    unfolding valof'_def by auto

  lemma nnan_op_fp64_1[simp]: "\<not>is_nan op_fp64_1"
    by(simp flip: float_of_fp64_1)

  lemma sign_op_fp64_1[simp]: "sign op_fp64_1 = 0"
    by(simp flip: float_of_fp64_1)

  sepref_def op_fp64_1_ll [llvm_inline] is "uncurry0 (RETURN op_fp64_1)" :: "unit_assn\<^sup>k \<rightarrow>\<^sub>a dfloat_assn"
    unfolding word_float_test_def op_fp64_1_def
    apply sepref
    done


  subsection \<open>Comparison Operations\<close>

  (* TODO: Move *)
  lemma float_le_not_nan:
    "a\<le>b \<Longrightarrow> \<not>is_nan a"
    "a\<le>b \<Longrightarrow> \<not>is_nan b"
    by (auto simp: less_eq_float_def fle_def fcompare_def)
    
  lemma float_lt_not_nan:
    "a<b \<Longrightarrow> \<not>is_nan a"
    "a<b \<Longrightarrow> \<not>is_nan b"
    by (auto simp: less_float_def flt_def fcompare_def)
    
  lemma double_lt_not_nan:
    "a<b \<Longrightarrow> \<not>is_nan_double a"
    "a<b \<Longrightarrow> \<not>is_nan_double b"
    by (transfer; blast dest: float_lt_not_nan; fail)+
  
  lemma double_le_not_nan:
    "a\<le>b \<Longrightarrow> \<not>is_nan_double a"
    "a\<le>b \<Longrightarrow> \<not>is_nan_double b"
    by (transfer; blast dest: float_le_not_nan; fail)+
  
  (* TODO: Move *)
  lemma bool_to_lint_to_word_simp: "lint_to_word (bool_to_lint x) = from_bool x"
    apply (cases x)
    unfolding bool_to_lint_def
    unfolding lint_to_word_def
    by auto
    
  lemma from_bool_bool1_rel: "(from_bool x, y) \<in> bool1_rel \<longleftrightarrow> x = y"
    unfolding bool1_rel_def bool.rel_def 
    by(auto simp: in_br_conv)

  lemma bool_to_lint_to_word_bool1_rel: "(lint_to_word (bool_to_lint x), y) \<in> bool1_rel \<longleftrightarrow> x = y"
    using from_bool_bool1_rel unfolding from_bool_lint_conv .
    
    
  (* TODO: Move *)
  lemma ll_fcmp_ole_d_alt: "ll_fcmp_ole_d a b = Mreturn (from_bool (a \<le> b))"
    unfolding op_lift_fcmp_d_def ll_fcmp_ole_d_def
    apply (simp add: bool_to_lint_to_word_simp)
    apply (fo_rule arg_cong)
    by (blast dest: double_le_not_nan)
    
  lemma ll_fcmp_olt_d_alt: "ll_fcmp_olt_d a b = Mreturn (from_bool (a < b))"
    unfolding op_lift_fcmp_d_def ll_fcmp_olt_d_def
    apply (simp add: bool_to_lint_to_word_simp)
    apply (fo_rule arg_cong)
    by (blast dest: double_lt_not_nan)
    
    
  sepref_register "(\<le>) :: (_,_) float \<Rightarrow> _"  
  sepref_register "(<) :: (_,_) float \<Rightarrow> _"  
    
  lemma fleq_d_hnr[sepref_fr_rules]: "(uncurry ll_fcmp_ole_d, uncurry (RETURN oo (\<le>))) \<in> dfloat_assn\<^sup>k *\<^sub>a dfloat_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
    apply(sepref_to_hoare)
    unfolding ll_fcmp_ole_d_alt dfloat_rel_def
    supply [simp] = in_br_conv from_bool_bool1_rel less_eq_double.rep_eq[symmetric]
    by vcg
    
  lemma flt_d_hnr[sepref_fr_rules]: "(uncurry ll_fcmp_olt_d, uncurry (RETURN oo (<))) \<in> dfloat_assn\<^sup>k *\<^sub>a dfloat_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
    apply(sepref_to_hoare)
    unfolding ll_fcmp_olt_d_alt dfloat_rel_def
    supply [simp] = in_br_conv from_bool_bool1_rel less_double.rep_eq[symmetric]
    by vcg
    
    
  subsubsection \<open>Legacy \<open>op_ole_d\<close>\<close>

  definition "op_ole_d a b = (if is_nan a \<or> is_nan b then False else a \<le> b)"
  sepref_register op_ole_d

  lemma op_ole_d_is_le: "op_ole_d a b \<longleftrightarrow> a\<le>b"
    unfolding op_ole_d_def
    by (auto dest: float_le_not_nan)
  
  
  lemma op_ole_le: "\<not>is_nan a \<Longrightarrow> \<not>is_nan b \<Longrightarrow> op_ole_d a b \<longleftrightarrow> a \<le> b"
    unfolding op_ole_d_def by simp

  lemma op_ole_valof'_le: "\<not>is_nan a \<Longrightarrow> \<not>is_nan b \<Longrightarrow> op_ole_d a b \<longleftrightarrow> valof' a \<le> valof' b"
    unfolding op_ole_d_def valof'_def by (auto simp: is_infinity_alt) 


  (*This proof could be nicer with existing setup, e.g. look at find_theorems bool1_rel "(\<le>)"*)
  lemma op_ole_d_hnr[sepref_fr_rules]: "(uncurry ll_fcmp_ole_d, uncurry (RETURN oo op_ole_d)) \<in> dfloat_assn\<^sup>k *\<^sub>a dfloat_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
    apply(sepref_to_hoare)
    unfolding ll_fcmp_ole_d_def op_lift_fcmp_d_def 
    unfolding op_ole_d_def dfloat_rel_def
    supply[simp] = in_br_conv bool_to_lint_to_word_bool1_rel is_nan_float_of_double less_eq_double.rep_eq
    by vcg


  definition add_floats_comp_dn :: "float64 \<Rightarrow> _" where "add_floats_comp_dn a b c = do{
    if op_ole_d b c then do {
      d \<leftarrow> mop_add_rdn a b;
      e \<leftarrow> mop_mul_rdn c d;
      mop_fma_rdn d e a
    } else do {
      d \<leftarrow> mop_add_rdn a c;
      e \<leftarrow> mop_mul_rdn b d;
      mop_fma_rdn d e a
    }
  }"

  sepref_def add_floats_comp_dn_ll is "uncurry2 add_floats_comp_dn" :: "dfloat_assn\<^sup>k *\<^sub>a dfloat_assn\<^sup>k *\<^sub>a dfloat_assn\<^sup>k \<rightarrow>\<^sub>a dfloat_assn"
    unfolding add_floats_comp_dn_def
    apply sepref
    done

  subsubsection \<open>Min/Max\<close>

  sepref_def min_double_impl is "uncurry (RETURN oo min)" :: "dfloat_assn\<^sup>k *\<^sub>a dfloat_assn\<^sup>k \<rightarrow>\<^sub>a dfloat_assn"
    unfolding min_def
    apply sepref
    done

  sepref_def max_double_impl is "uncurry (RETURN oo max)" :: "dfloat_assn\<^sup>k *\<^sub>a dfloat_assn\<^sup>k \<rightarrow>\<^sub>a dfloat_assn"
    unfolding max_def
    apply sepref
    done
  
  subsubsection \<open>Legacy\<close>
  definition "op_min_double fl\<^sub>1 fl\<^sub>2 = (if fl\<^sub>1 \<le> fl\<^sub>2 then fl\<^sub>1 else fl\<^sub>2)"

  definition "op_max_double fl\<^sub>1 fl\<^sub>2 = (if fl\<^sub>1 \<le> fl\<^sub>2 then fl\<^sub>2 else fl\<^sub>1)"

  sepref_def op_min_double_ll is "uncurry (RETURN oo op_min_double)" :: "dfloat_assn\<^sup>k *\<^sub>a dfloat_assn\<^sup>k \<rightarrow>\<^sub>a dfloat_assn"
    unfolding op_min_double_def
    apply sepref
    done

  sepref_def op_max_double_ll is "uncurry (RETURN oo op_max_double)" :: "dfloat_assn\<^sup>k *\<^sub>a dfloat_assn\<^sup>k \<rightarrow>\<^sub>a dfloat_assn"
    unfolding op_max_double_def
    apply sepref
    done

  subsection \<open>Basic Arithmetic Operations\<close>
    

  definition "mop_fadd a b \<equiv> nanize_float (a+b)"
  definition "mop_fsub a b \<equiv> nanize_float (a-b)"
  definition "mop_fmul a b \<equiv> nanize_float (a*b)"
  definition "mop_fdiv a b \<equiv> nanize_float (a/b)"
  definition "mop_fsqrt a \<equiv> nanize_float (float_sqrt a)"
  (* TODO: fma, sqrt, \<dots> *)
    
  lemma wpa_ndet_nan_double[vcg_normalize_simps]: "wpa asf ndet_nan_double Q s \<longleftrightarrow> (\<forall>x'. is_nan_double x' \<longrightarrow> Q x' s)"
    unfolding ndet_nan_double_def
    supply [simp] = is_nan_double_neq_bot
    by (auto simp: wpa_spec) 
    
  
  thm vcg_decomp_erules
  
  lemma wpa_nanize_double_simp[vcg_normalize_simps]: "wpa asf (nanize_double x) Q s \<longleftrightarrow> 
      (is_nan_double x \<longrightarrow> (\<forall>x'. is_nan_double x' \<longrightarrow> Q x' s)) 
    \<and> (\<not>is_nan_double x \<longrightarrow> Q x s)"
    unfolding nanize_double_def ndet_nan_double_def
    supply [simp] = is_nan_double_neq_bot
    by (auto simp: wpa_spec wpa_return) 
    
  
  context begin
    interpretation llvm_prim_arith_setup .

    lemma fadd_double_hnr[sepref_fr_rules]: "(uncurry ll_fadd_d, uncurry mop_fadd) \<in> dfloat_assn\<^sup>k *\<^sub>a dfloat_assn\<^sup>k \<rightarrow>\<^sub>a dfloat_assn"
      apply sepref_to_hoare
      unfolding dfloat_rel_def
      apply (simp add: in_br_conv mop_fadd_def nanize_float_def)
      supply [simp] = is_nan_float_of_double plus_double.rep_eq
      by vcg
  
    lemma fsub_double_hnr[sepref_fr_rules]: "(uncurry ll_fsub_d, uncurry mop_fsub) \<in> dfloat_assn\<^sup>k *\<^sub>a dfloat_assn\<^sup>k \<rightarrow>\<^sub>a dfloat_assn"
      apply sepref_to_hoare
      unfolding dfloat_rel_def
      apply (simp add: in_br_conv mop_fsub_def nanize_float_def)
      supply [simp] = is_nan_float_of_double minus_double.rep_eq
      by vcg
  
    lemma fmul_double_hnr[sepref_fr_rules]: "(uncurry ll_fmul_d, uncurry mop_fmul) \<in> dfloat_assn\<^sup>k *\<^sub>a dfloat_assn\<^sup>k \<rightarrow>\<^sub>a dfloat_assn"
      apply sepref_to_hoare
      unfolding dfloat_rel_def
      apply (simp add: in_br_conv mop_fmul_def nanize_float_def)
      supply [simp] = is_nan_float_of_double times_double.rep_eq
      by vcg
    
    lemma fdiv_double_hnr[sepref_fr_rules]: "(uncurry ll_fdiv_d, uncurry mop_fdiv) \<in> dfloat_assn\<^sup>k *\<^sub>a dfloat_assn\<^sup>k \<rightarrow>\<^sub>a dfloat_assn"
      apply sepref_to_hoare
      unfolding dfloat_rel_def
      apply (simp add: in_br_conv mop_fdiv_def nanize_float_def)
      supply [simp] = is_nan_float_of_double divide_double.rep_eq
      by vcg

    lemma fsqrt_double_hnr[sepref_fr_rules]: "(ll_sqrt_f64, mop_fsqrt) \<in> dfloat_assn\<^sup>k \<rightarrow>\<^sub>a dfloat_assn"
      apply sepref_to_hoare
      unfolding dfloat_rel_def
      apply (simp add: in_br_conv mop_fsqrt_def nanize_float_def)
      supply [simp] = is_nan_float_of_double dsqrt_def drsqrt.rep_eq float_sqrt_def
      by vcg
      
          
  end    
    
    
    
  section \<open>Non-negative real double precision assn\<close>
    
  subsection \<open>Auxiliary Definitions & Lemmas for the Assertion\<close>

  lemma nnan_inres_op_farith1_rm: "\<not>is_nan fl\<^sub>2 \<Longrightarrow> inres (op_farith1_rm f rm fl\<^sub>1) fl\<^sub>2 \<Longrightarrow> fl\<^sub>2 = f rm fl\<^sub>1"
    unfolding op_farith1_rm_def nanize_float_def by(auto split: if_splits)

  lemma nnan_inres_op_farith2_rm: "\<not>is_nan fl\<^sub>3 \<Longrightarrow> inres (op_farith2_rm f rm fl\<^sub>1 fl\<^sub>2) fl\<^sub>3 \<Longrightarrow> fl\<^sub>3 = f rm fl\<^sub>1 fl\<^sub>2"
    unfolding op_farith2_rm_def nanize_float_def by(auto split: if_splits)

  lemma nnan_inres_op_farith3_rm: "\<not>is_nan fl\<^sub>4 \<Longrightarrow> inres (op_farith3_rm f rm fl\<^sub>1 fl\<^sub>2 fl\<^sub>3) fl\<^sub>4 \<Longrightarrow> fl\<^sub>4 = f rm fl\<^sub>1 fl\<^sub>2 fl\<^sub>3"
    unfolding op_farith3_rm_def nanize_float_def by(auto split: if_splits)



  text \<open>
    nn_real_invar: Non-negative real invar.
    For vanilla floats represeanting only reals, we exclude floats that are NaN as they do not 
    have any meaning when translating to reals.
    We also limit the floats only to positive values. For addition this eliminates the edge case 
    \<open>\<infinity> + -\<infinity> = NaN\<close>. 
    For multiplication this is necessary to preserve the bounds. E.g. 0.5 is a lower bound of 1,
    but multiplying by -1 yields -0.5 which is an upper bound -1.
  \<close>
  definition "nn_real_invar fl \<equiv> \<not>is_nan fl \<and> sign fl = 0"

  definition "pfin_real_invar fl \<equiv> \<not>is_nan fl \<and> \<not>is_zero fl \<and> is_finite fl \<and> sign fl = 0"

  lemma pfin_real_invar_alt: "pfin_real_invar fl = (\<not>is_nan fl \<and> \<not>is_zero fl \<and> \<not>is_infinity fl \<and> sign fl = 0)"
    unfolding pfin_real_invar_def 
    using nnan_nfin_eq_inf by blast

  lemma eq_the_nan1: "fl\<^sub>1 = the_nan fl\<^sub>2 \<Longrightarrow> \<not>is_nan fl\<^sub>1 \<Longrightarrow> False"
    by simp

  lemma is_nan_eq_the_nan: "is_nan fl \<longleftrightarrow> fl = the_nan fl"
    unfolding the_nan_def by auto

  lemma nn_real_invar_valof': "LENGTH('e) > 1 \<Longrightarrow> nn_real_invar (fl:: ('e,'f) float) \<Longrightarrow> valof' fl \<ge> 0"
    unfolding nn_real_invar_def valof'_def
    using float_cases_finite by (force simp: is_infinity_alt intro!: valof_nonneg) 

  lemma pfin_real_invar_valof': "LENGTH('e) > 1 \<Longrightarrow> pfin_real_invar (fl:: ('e,'f) float) \<Longrightarrow> valof' fl > 0 \<and> valof' fl < \<infinity>" 
    unfolding pfin_real_invar_def valof'_def
    using float_cases_finite by (auto simp: is_zero_iff_valof0 sign_pos_iff_valof)

  lemma pfin_real_invar_valof: "LENGTH('e) > 1 \<Longrightarrow> pfin_real_invar (fl:: ('e,'f) float) \<Longrightarrow> valof fl > 0" 
    unfolding pfin_real_invar_def
    using float_cases_finite sign_neg_iff_valof by (fastforce)


  definition "round_protect = IEEE.round"

  lemma is_nan_zerosign[simp]: "is_nan (zerosign s p) = is_nan p"
    unfolding zerosign_def by auto

  lemma is_nan_fadd: "is_nan (fadd m fl\<^sub>1 fl\<^sub>2) \<longleftrightarrow> is_nan fl\<^sub>1 \<or> is_nan fl\<^sub>2 \<or> (is_infinity fl\<^sub>1 \<and> is_infinity fl\<^sub>2 \<and> sign fl\<^sub>1 \<noteq> sign (fl\<^sub>2 :: ('e::len2,'f) float))" 
    unfolding fadd_def 
    apply (cases fl\<^sub>1 rule: float_cases_eqs; cases fl\<^sub>2 rule: float_cases_eqs)
    apply (auto dest!: closest_eq_in_setD finite_infinity simp: zerosign_def round_valof)+ 
    done

  lemma is_nan_fsub: "is_nan (fsub m fl\<^sub>1 fl\<^sub>2) \<longleftrightarrow> is_nan fl\<^sub>1 \<or> is_nan fl\<^sub>2 \<or> (is_infinity fl\<^sub>1 \<and> is_infinity fl\<^sub>2 \<and> sign fl\<^sub>1 = sign (fl\<^sub>2 :: ('e::len2,'f) float))" 
    unfolding fsub_def 
    apply (cases fl\<^sub>1 rule: float_cases_eqs; cases fl\<^sub>2 rule: float_cases_eqs)
    apply (auto dest!: closest_eq_in_setD finite_infinity simp: zerosign_def round_valof)+ 
    done

  lemma is_nan_fmul: "is_nan (fmul m fl\<^sub>1 fl\<^sub>2) \<longleftrightarrow> is_nan fl\<^sub>1 \<or> is_nan fl\<^sub>2 \<or> (is_zero fl\<^sub>1 \<and> is_infinity fl\<^sub>2) \<or> (is_infinity fl\<^sub>1 \<and> is_zero (fl\<^sub>2 :: ('e::len2,'f) float))" 
    unfolding fmul_def 
    apply (cases fl\<^sub>1 rule: float_cases_eqs; cases fl\<^sub>2 rule: float_cases_eqs)
    apply (auto split: if_splits) 
    done

  lemma is_nan_fmul_add: "is_nan (fmul_add m fl\<^sub>1 fl\<^sub>2 fl\<^sub>3) \<longleftrightarrow> is_nan fl\<^sub>1 \<or> is_nan fl\<^sub>2 \<or> is_nan (fl\<^sub>3 :: ('e::len2,'f) float) \<or> 
    (let signP = if sign fl\<^sub>1 = sign fl\<^sub>2 then 0 else 1; infP = is_infinity fl\<^sub>1 \<or> is_infinity fl\<^sub>2 in 
      is_infinity fl\<^sub>1 \<and> is_zero fl\<^sub>2 \<or> is_zero fl\<^sub>1 \<and> is_infinity fl\<^sub>2 \<or> is_infinity fl\<^sub>3 \<and> infP \<and> signP \<noteq> sign fl\<^sub>3 )" 
    unfolding fmul_add_def 
    apply (cases fl\<^sub>1 rule: float_cases_eqs; cases fl\<^sub>2 rule: float_cases_eqs; cases fl\<^sub>3 rule: float_cases_eqs)
    by (auto split: if_splits simp: Let_def)



  lemma "nn_real_invar fl\<^sub>1 \<Longrightarrow> nn_real_invar fl\<^sub>2 \<Longrightarrow> inres (mop_add_rup fl\<^sub>1 fl\<^sub>2) fl\<^sub>3 \<Longrightarrow> \<not>is_nan (fl\<^sub>3 :: ('e::len2,'f) float)"
    unfolding mop_add_rup_def op_farith2_rm_def nanize_float_def nn_real_invar_def
    by(auto split: if_splits simp: is_nan_fadd)
  
  lemma sign_zerosign_alt: "s \<le> 1 \<Longrightarrow> sign (zerosign s a) = (if is_zero a then s else sign a)"
    unfolding zerosign_def
    by auto

  lemma sign_zerosign0: "sign (zerosign 0 a) = (if is_zero a then 0 else sign a)"
    unfolding zerosign_def
    by auto

  lemma sign_zerosign1: "sign (zerosign (Suc 0) a) = (if is_zero a then 1 else sign a)"
    unfolding zerosign_def
    by auto

  lemma zero_sign_zerosign: "is_zero a \<Longrightarrow> sign (zerosign s a) = min 1 s"
    unfolding zerosign_def by simp 

  lemma nzero_sign_zerosign: "\<not>is_zero a \<Longrightarrow> sign (zerosign s a) = sign a"
    unfolding zerosign_def by simp 

  lemma threshold_negative: "- threshold TYPE(('e,'f) float) < 0"
    using threshold_positive by simp

  lemma largest_ltZ: "-largest TYPE(('e,'f) float) < 0"  
    by (simp add: divide_less_eq largest_def power_gt1_lemma)

  lemma nzero_fin_sign_eq_valof_ge0: "\<not> is_zero fl \<Longrightarrow> is_finite fl \<Longrightarrow> sign fl = 0 \<longleftrightarrow> valof fl \<ge> 0" 
    apply(subst sign_pos_iff_valof)
    apply assumption by blast

  lemma nzero_fin_sign_eq_valof_gt0: "\<not> is_zero fl \<Longrightarrow> is_finite fl \<Longrightarrow> sign fl = 0 \<longleftrightarrow> valof fl > 0" 
    using is_zero_iff_valof0 sign_neg_iff_valof by fastforce


  lemma valof'_nonneg:
    "valof' x \<ge> 0" if "sign x = 0" and "\<not>is_nan x" for x::"('e, 'f)float"
    using that float_cases_finite[of x] 
    by (auto simp: valof_nonneg is_infinity_alt) 

  
  lemma valof'_nonpos:
    "valof' x \<le> 0" if "sign x = 1" and "\<not>is_nan x" for x::"('e, 'f)float"
    using that float_cases_finite[of x] 
    by (auto simp: valof_nonpos is_infinity_alt) 


  lemma nzero_fin_sign_eq_valof'_gt0: "\<not> is_zero fl \<Longrightarrow> is_finite fl \<Longrightarrow> sign fl = 0 \<longleftrightarrow> valof' fl > 0" 
    using is_zero_iff_valof0 sign_neg_iff_valof by fastforce

  lemma valof_leq_ereal_ninf: "valof' fl \<le> ereal x \<Longrightarrow> \<not>is_nan fl \<Longrightarrow> fl \<noteq> \<infinity>"
    unfolding valof'_def by auto



  lemma nzero_fin_sign_eq_valof_plus_gt0: 
    assumes Z1: "\<not> is_zero fl\<^sub>1"
    and S1: "sign fl\<^sub>1 = 0"
    and F1: "is_finite fl\<^sub>1"
    and S2: "sign fl\<^sub>2 = 0"
    and F2: "is_finite fl\<^sub>2"
    shows "valof fl\<^sub>1 + valof fl\<^sub>2 > 0" 
  proof -
    have "valof fl\<^sub>1 > 0"
      using nzero_fin_sign_eq_valof_gt0[OF Z1 F1] S1 by blast
    moreover have "valof fl\<^sub>2 \<ge> 0"
      using S2 valof_nonneg by blast
    ultimately show ?thesis by argo
  qed

  lemma orthogonal_abs_area1: "(a::_::linordered_idom) < b \<Longrightarrow> \<bar>x - a\<bar> \<le> \<bar>y - a\<bar> \<Longrightarrow> \<bar>y - b\<bar> \<le> \<bar>x - b\<bar> \<Longrightarrow> x \<noteq> y \<Longrightarrow> x + y \<ge> 2 * a \<and> x + y \<le> 2 * b \<and> y > x"
    by linarith

  lemma is_closest_mono:
    fixes a::"_::linordered_idom"
    assumes AB: "a < b"
    assumes CA: "is_closest v s a x"
    assumes CB: "is_closest v s b y"
    shows "v x \<le> v y"
  proof(cases "v x = v y")
    case True
    then show ?thesis by simp
  next
    case False
    from CA CB have D1: "\<bar>v x - a\<bar> \<le> \<bar>v y - a\<bar>" and D2: "\<bar>v y - b\<bar> \<le> \<bar>v x - b\<bar>"
      unfolding is_closest_def
      by presburger+
    have "v x < v y"
      using orthogonal_abs_area1[OF AB D1 D2 False] by blast
    then show ?thesis by linarith
  qed


  lemma closest_mono: 
    fixes v :: "('e, 'f)float \<Rightarrow> real"
    assumes AB: "a \<le> b"
    assumes NE: "s \<noteq> {}"
    shows "v (closest v p s a) \<le> v (closest v p s b)"
  proof -
    have A: "is_closest v s a (closest v p s a)"
     and B: "is_closest v s b (closest v p s b)"
      using closest_is_closest[OF NE] by auto
    show ?thesis 
      apply(cases "a < b")
      using is_closest_mono[OF _ A B] apply assumption
      using AB by simp
  qed



  lemma is_closest_mono_To_nearest:
    fixes a b and s s' :: "('e,'f) float set"
    defines "s \<equiv> {c. is_finite c \<and> \<bar>valof c\<bar> \<le> \<bar>a\<bar>}"
    and "s' \<equiv> {c. is_finite c \<and> \<bar>valof c\<bar> \<le> \<bar>b\<bar>}"
    assumes AB: "a \<le> b"
    assumes CA: "is_closest valof s a x"
    assumes CB: "is_closest valof s' b y"
    shows "valof x \<le> valof y"
  proof(cases "valof x = valof y")
    case True
    then show ?thesis by simp
  next
    case False

    consider (l0) "a \<le> 0 \<and> b \<le> 0" | (d0) "a \<le> 0 \<and> b \<ge> 0" | (g0) "a \<ge> 0 \<and> b \<ge> 0"
      using AB by linarith
    hence "valof x < valof y"
    proof cases
      case l0 
      then show ?thesis 
        by (smt (verit, del_insts) AB CA CB False abs_of_nonneg assms(1) assms(2) is_closest_def mem_Collect_eq)
    next
      case d0
      have "0 \<in> s" and "0 \<in> s'"
        unfolding s_def s'_def
        by fastforce+
      then show ?thesis
        by (smt (verit, best) CA CB False abs_of_nonneg abs_of_nonpos d0 is_closest_def valof_zero(1))
    next
      case g0
      hence "s \<subseteq> s'" 
        using AB s'_def s_def by force
      then show ?thesis 
        by (smt (verit, del_insts) CA CB Collect_mono_iff False abs_of_nonpos assms(1) assms(2) g0 is_closest_def mem_Collect_eq)
    qed
    then show ?thesis by linarith
  qed

  lemma closest_mono_To_nearest: 
    fixes a b and s s' :: "('e,'f) float set"
    defines "s \<equiv> {c. is_finite c \<and> \<bar>valof c\<bar> \<le> \<bar>a\<bar>}"
    and "s' \<equiv> {c. is_finite c \<and> \<bar>valof c\<bar> \<le> \<bar>b\<bar>}"
    assumes AB: "a \<le> b"
    assumes V0: "v 0 = 0"
    shows "valof (closest valof p s a) \<le> valof (closest valof p s' b)"
  proof -
    have SNE1: "s \<noteq> {}" and SNE2: "s' \<noteq> {}"
      using V0 s_def s'_def by force+
    have A: "is_closest valof s a (closest valof p s a)"
     and B: "is_closest valof s' b (closest valof p s' b)"
      using closest_is_closest[OF SNE1] closest_is_closest[OF SNE2] by auto
    show ?thesis 
      using is_closest_mono_To_nearest[OF AB A[unfolded s_def] B[unfolded s'_def]]
      unfolding s_def s'_def .
  qed




  lemma is_closest_mono_To_pinfinity:
    fixes a b and s s' :: "('e,'f) float set"
    defines "s \<equiv> {c. is_finite c \<and> a \<le> valof c}"
    and "s' \<equiv> {c. is_finite c \<and> b \<le> valof c}"
    assumes AB: "a < b"
    assumes CA: "is_closest valof s a x"
    assumes CB: "is_closest valof s' b y"
    shows "valof x \<le> valof y"
  proof(cases "valof x = valof y")
    case True
    then show ?thesis by simp
  next
    case False
    from AB have "s' \<subseteq> s" unfolding s_def s'_def 
      by fastforce
    moreover from CA CB have XS: "x \<in> s" and YS': "y \<in> s'" and YS: "y \<in> s"
      using calculation unfolding is_closest_def by blast+
    ultimately consider (xs') "x \<in> s'" | (xs) "x \<in> s - s'" by blast

    hence "valof x < valof y" 
    proof cases
      case xs'
      with CA CB YS have D1: "\<bar>valof x - a\<bar> \<le> \<bar>valof y - a\<bar>" and D2: "\<bar>valof y - b\<bar> \<le> \<bar>valof x - b\<bar>"
        unfolding is_closest_def
        by presburger+
      show ?thesis using orthogonal_abs_area1[OF AB D1 D2 False]
        by blast
    next
      case xs
      hence "x \<in> {c. is_finite c \<and> a \<le> valof c \<and> valof c < b}"
        unfolding s_def s'_def by force
      then show ?thesis
        using YS' s'_def by auto
    qed
    then show ?thesis by linarith
  qed

  lemma closest_mono_To_pinfinity: 
    fixes a b and s s' :: "('e::len2,'f) float set"
    defines "s \<equiv> {c. is_finite c \<and> a \<le> valof c}"
    and "s' \<equiv> {c. is_finite c \<and> b \<le> valof c}"
    assumes AB: "a \<le> b"
    assumes BL: "b \<le> largest TYPE (('e::len2,'f) float)"
    shows "valof (closest valof p s a) \<le> valof (closest valof p s' b)"
  proof -
    from AB have "s' \<subseteq> s" unfolding s_def s'_def 
      by fastforce
    hence "topfloat \<in> s'" and "topfloat \<in> s" unfolding s'_def
      by (auto simp add: assms(4) valof_topfloat)


    hence A: "is_closest valof s a (closest valof p s a)"
     and B: "is_closest valof s' b (closest valof p s' b)"
      by(auto intro: closest_is_closest) 
    show ?thesis 
      apply (cases "a < b")
      using AB is_closest_mono_To_pinfinity[OF _ A[unfolded s_def] B[unfolded s'_def]]
      unfolding s_def s'_def by auto
  qed



  lemma is_closest_mono_To_ninfinity:
    fixes a b and s s' :: "('e,'f) float set"
    defines "s \<equiv> {c. is_finite c \<and> valof c \<le> a}"
    and "s' \<equiv> {c. is_finite c \<and> valof c \<le> b}"
    assumes AB: "a < b"
    assumes CA: "is_closest valof s a x"
    assumes CB: "is_closest valof s' b y"
    shows "valof x \<le> valof y"
  proof(cases "valof x = valof y")
    case True
    then show ?thesis by simp
  next
    case False
    from AB have "s \<subseteq> s'" unfolding s_def s'_def 
      by fastforce
    moreover from CA CB have XS: "x \<in> s" and YS': "y \<in> s'" and YS: "x \<in> s'"
      using calculation unfolding is_closest_def by blast+
    ultimately consider (xs') "y \<in> s" | (xs) "y \<in> s' - s" by blast

    hence "valof x < valof y" 
    proof cases
      case xs'
      with CA CB YS have D1: "\<bar>valof x - a\<bar> \<le> \<bar>valof y - a\<bar>" and D2: "\<bar>valof y - b\<bar> \<le> \<bar>valof x - b\<bar>"
        unfolding is_closest_def
        by blast+
      show ?thesis using orthogonal_abs_area1[OF AB D1 D2 False]
        by blast
    next
      case xs
      hence "y \<in> {c. is_finite c \<and> a < valof c \<and> valof c \<le> b}"
        unfolding s_def s'_def by force
      then show ?thesis
        using XS s_def by auto
    qed
    then show ?thesis by linarith
  qed

  lemma closest_mono_To_ninfinity: 
    fixes a b and s s' :: "('e::len2,'f) float set"
    defines "s \<equiv> {c. is_finite c \<and> valof c \<le> a}"
    and "s' \<equiv> {c. is_finite c \<and> valof c \<le> b}"
    assumes AB: "a \<le> b"
    assumes BL: "-largest TYPE (('e::len2,'f) float) \<le> a"
    shows "valof (closest valof p s a) \<le> valof (closest valof p s' b)"
  proof -
    from AB have "s \<subseteq> s'" unfolding s_def s'_def 
      by fastforce
    hence "bottomfloat \<in> s" and "bottomfloat \<in> s'" unfolding s_def
      by (auto simp add: BL valof_topfloat )


    hence A: "is_closest valof s a (closest valof p s a)"
     and B: "is_closest valof s' b (closest valof p s' b)"
      by(auto intro: closest_is_closest) 
    show ?thesis 
      apply (cases "a < b")
      using AB is_closest_mono_To_ninfinity[OF _ A[unfolded s_def] B[unfolded s'_def]]
      unfolding s_def s'_def by auto
  qed



  lemma is_finite_round_to_zero: "is_finite (IEEE.round float_To_zero x)" 
    apply (clarsimp simp: round.simps) 
    apply(rule finite_closest_valofI)
    by force+

  lemma "s \<noteq> {} \<Longrightarrow> s \<subseteq> Collect is_finite \<Longrightarrow> - largest TYPE(('e::len2,'f) IEEE.float) \<le> valof (closest valof p s a::('e::len2,'f) float)"
    by(auto intro!: float_val_ge_largest finite_closest_valofI)

  lemma "s \<noteq> {} \<Longrightarrow> s \<subseteq> Collect is_finite \<Longrightarrow> valof (closest valof p s a::('e::len2,'f) float) \<le> largest TYPE(('e::len2,'f) IEEE.float)"
    by(auto intro!: float_val_le_largest finite_closest_valofI)


  lemma round_mono: "a \<le> b \<Longrightarrow> is_finite (IEEE.round rm a :: ('e::len2, 'f)float) \<Longrightarrow> is_finite (IEEE.round rm b :: ('e::len2, 'f)float) 
    \<Longrightarrow> valof (IEEE.round rm a :: ('e::len2, 'f)float) \<le> valof (IEEE.round rm b :: ('e::len2, 'f)float)"
    apply(cases rm)
    supply[simp] = round.simps
    subgoal
      by(auto split: if_splits intro: closest_mono)
    subgoal 
      by(auto split: if_splits intro: closest_mono_To_nearest
        simp: valof_nonneg valof_topfloat float_val_ge_largest float_val_le_largest) 
    subgoal 
      by(auto split: if_splits intro: closest_mono_To_pinfinity 
        simp: valof_topfloat float_val_ge_largest)
    subgoal 
      by(auto split: if_splits intro: closest_mono_To_ninfinity 
        simp: valof_topfloat float_val_le_largest) 
    done



  lemma sign_closest_plus_0:
    assumes NZ: "\<not>is_zero (closest valof p s (valof fl\<^sub>1 + valof fl\<^sub>2))"
    assumes SFIN: "s \<subseteq> Collect is_finite"
    assumes V1: "sign fl\<^sub>1 = 0"
    assumes V2: "sign fl\<^sub>2 = 0"
    assumes Z1: "\<not> is_zero fl\<^sub>1"
    assumes Z2: "\<not> is_zero fl\<^sub>2" 
    assumes FS1: "fl\<^sub>1 \<in> s"
    assumes FS2: "fl\<^sub>2 \<in> s"
    shows "sign (closest valof p s (valof fl\<^sub>1 + valof fl\<^sub>2)) = 0"
  proof -

    have NES: "s \<noteq> {}"
      using FS1 by blast
    have FIN1: "is_finite fl\<^sub>1" and FIN2: "is_finite fl\<^sub>2"
      using FS1 FS2 SFIN by blast+

    have V1: "valof fl\<^sub>1 > 0" and V2: "valof fl\<^sub>2 > 0"
      using V1[unfolded nzero_fin_sign_eq_valof_gt0[OF Z1 FIN1]]
      using V2[unfolded nzero_fin_sign_eq_valof_gt0[OF Z2 FIN2]] .
    hence A: "valof fl\<^sub>1 \<le> valof fl\<^sub>1 + valof fl\<^sub>2"
      by linarith
    moreover have "valof (closest valof p s (valof fl\<^sub>1)) = valof fl\<^sub>1"
      using closest_precise[OF FS1 SFIN Z1] by simp
    ultimately show ?thesis
      unfolding nzero_fin_sign_eq_valof_gt0[OF NZ finite_closest_valofI[OF NES SFIN]] 
      using closest_mono[OF A NES, of valof p] V1 
      by linarith 
  qed



  lemma order_transE: 
    fixes a::"_::preorder" 
    assumes "a \<le> b" 
    and "b \<le> c"
    and "(a \<le> c \<Longrightarrow> P)" 
    shows "P" 
  proof -
    from assms(1,2) have "a \<le> c" 
      using order_trans by blast
    with assms(3) show ?thesis by blast
  qed


  lemma float_val_gt_threshold_len2e:
    fixes a::"('e::len2,'f)float"
    assumes "is_finite a"
    shows "valof a > - threshold TYPE(('e::len2,'f)float)"
    using float_val_gt_threshold assms by force

  lemma float_val_ge_largest_len2e:
    fixes a::"('e::len2,'f)float"
    assumes "is_finite a"
    shows "valof a \<ge> - largest TYPE(('e::len2,'f)float)"
    using assms float_val_ge_largest by force


  lemma valof_topfloat_gt0: "valof (topfloat::('e, 'f)float) > 0"
    by (auto  simp: emax_eq divide_simps float_defs 
              intro!: mult_pos_pos zero_less_power power_gt1_lemma) 

  lemma sign_closest_0': "v \<ge> 0 \<Longrightarrow> 0 \<in> s \<Longrightarrow> s \<subseteq> Collect is_finite 
    \<Longrightarrow> \<not>is_zero (closest valof p s v) \<Longrightarrow> sign (closest valof p s v) = 0"
    by (metis (no_types, lifting) antisym_conv2 closest_mono empty_iff finite_closest_valofI is_zero_alt is_zero_closestI sign_pos_iff_valof valof_zero(1) valof_zero(2))

  lemma sign_s0_closest_0: "v \<ge> 0 \<Longrightarrow> x \<in> s \<Longrightarrow> s \<subseteq> Collect is_finite \<Longrightarrow> valof ` s \<subseteq> {r. r > 0} \<Longrightarrow> sign (closest valof p s v) = 0"
    apply(drule memb_imp_not_empty)
    by (metis closest_eq_in_setD imageI linorder_not_le sign_cases subset_Collect_conv valof_nonpos)

  lemma is_zero_round_zero':
    shows "v = 0 \<Longrightarrow> is_zero (IEEE.round m v::('e, 'f) float)"
    using is_zero_round_zero by blast

  lemma sign_round_gt0: 
    "v > 0 \<Longrightarrow> \<not>is_zero (IEEE.round rm v::('e::len2, 'f)float) \<Longrightarrow> sign ((IEEE.round rm v)::('e::len2, 'f)float) = 0"
    apply(cases rm)
    supply[simp] = round.simps
    subgoal 
      using threshold_negative[where ?'e='e and ?'f = 'f]
      by (auto simp: valof_topfloat_gt0 intro!: sign_closest_0' ) 
    subgoal 
      using largest_ltZ[where ?'e='e and ?'f = 'f]
      by (auto simp: sign_zerosign0 valof_topfloat_gt0 intro!: sign_closest_0' )
      (*TODO clean up proofs*)
    subgoal
      using largest_ltZ[where ?'e='e and ?'f = 'f]
      by (auto simp: sign_zerosign0 valof_topfloat intro!: sign_s0_closest_0[where ?x=topfloat])
    subgoal
      using largest_ltZ[where ?'e='e and ?'f = 'f]
      by (auto simp: sign_zerosign0 valof_topfloat_gt0 intro!: sign_closest_0')
    done

  lemma sign_zerosign_0_round_ge0: 
    "v \<ge> 0 \<Longrightarrow> sign (zerosign 0 (IEEE.round rm v)::('e::len2, 'f)float) = 0"
    apply(cases "is_zero (IEEE.round rm v::('e::len2, 'f)float)")
    using is_zero_round_zero' sign_round_gt0 
    apply (force simp: sign_zerosign0)+
    done

  lemma sign_zerosign_1_round_ge0: 
    "v \<ge> 0 \<Longrightarrow> \<not>is_zero (IEEE.round rm v::('e::len2, 'f)float) \<Longrightarrow> sign (zerosign (Suc 0) (IEEE.round rm v)::('e::len2, 'f)float) = 0"
    apply(clarsimp simp: sign_zerosign1) 
    using sign_round_gt0 by force

  lemma sign_zerosign_round_ge0: 
    "v \<ge> 0 \<Longrightarrow> \<not>is_zero (IEEE.round rm v::('e::len2, 'f)float) \<Longrightarrow> sign (zerosign x (IEEE.round rm v)::('e::len2, 'f)float) = 0"
    by (metis nzero_sign_zerosign sign_zerosign_0_round_ge0)


  lemma non_zero_gt: "\<not>is_zero a \<Longrightarrow> sign a = 0 \<Longrightarrow> (is_finite b \<Longrightarrow> valof a \<le> valof b) \<Longrightarrow> is_finite a \<Longrightarrow> \<not>is_zero b" 
    using is_zero_cases sign_neg_iff_valof by fastforce


  lemma valof_lt_plus: "is_finite fl\<^sub>1 \<Longrightarrow> sign fl\<^sub>2 = 0 \<Longrightarrow> is_finite (IEEE.round rm (valof fl\<^sub>1 + valof fl\<^sub>2) :: ('e::len2,'f) float) \<Longrightarrow> valof fl\<^sub>1 \<le> valof (IEEE.round rm (valof (fl\<^sub>1 :: ('e::len2,'f) float) + valof (fl\<^sub>2 :: ('e::len2,'f) float))  :: ('e::len2,'f) float)"
    apply(subst valof_round_valof[symmetric, of fl\<^sub>1 rm])
    apply assumption
    apply(rule round_mono[of "valof fl\<^sub>1" "(valof fl\<^sub>1 + valof fl\<^sub>2)" rm, simplified]; cases "is_zero fl\<^sub>1")
    apply (auto simp: valof_nonneg round_valof is_finite_def val_zero) 
    done

  lemma float_bounds_contr: "\<not>-largest TYPE(('e::len2, 'f) float) \<le> valof (fl :: ('e::len2, 'f) float) \<Longrightarrow> \<not>valof (fl :: ('e::len2, 'f) float) \<le> largest TYPE(('e::len2, 'f) float) \<Longrightarrow> False"
    by (metis abs_le_iff eq_abs_iff' largest_gtZ linorder_le_cases order_less_imp_le)

  lemma float_bounds_lb_contr: "valof (fl :: ('e::len2, 'f) float) < -largest TYPE(('e::len2, 'f) float) \<Longrightarrow> is_finite fl \<Longrightarrow> False"
    using float_val_ge_largest_len2e by fastforce

  lemma float_bounds_ub_contr: "largest TYPE(('e::len2, 'f) float) < valof (fl :: ('e::len2, 'f) float) \<Longrightarrow> is_finite fl \<Longrightarrow> False"
    using float_val_le_largest by fastforce





  lemma sign0_fadd: "\<not>is_nan (fadd rm fl\<^sub>1 fl\<^sub>2) \<Longrightarrow> sign fl\<^sub>1 = 0 \<Longrightarrow> sign fl\<^sub>2 = 0 \<Longrightarrow> sign (fadd rm fl\<^sub>1 (fl\<^sub>2:: ('e::len2,'f) float)) = 0"
    unfolding fadd_def
    apply (cases fl\<^sub>1 rule: float_cases_eqs; cases fl\<^sub>2 rule: float_cases_eqs)
    apply (simp_all add: is_zero_closestI Collect_mono_iff sign_zerosign0 sign_zerosign1 closest_precise)[35]
    using float_val_ge_largest_len2e round_valof apply fastforce
    using float_val_ge_largest_len2e round_valof apply fastforce
    apply(rule P_ifI)
    apply simp
    apply(rule P_ifI) 
    apply simp
    apply(rule P_ifI) 
    apply simp
    apply(rule sign_zerosign_round_ge0)
    apply (auto simp: valof_nonneg) []
    apply(rule non_zero_gt[of fl\<^sub>1])
    using valof_lt_plus apply auto
    done

  lemma sign0_fsub_fin2_nninf: "\<not>is_nan (fsub rm fl\<^sub>1 fl\<^sub>2) \<Longrightarrow> rm \<noteq> To_ninfinity \<Longrightarrow> is_finite fl\<^sub>2 \<Longrightarrow> valof' fl\<^sub>2 \<le> valof' fl\<^sub>1 \<Longrightarrow> sign fl\<^sub>1 = 0 \<Longrightarrow> sign fl\<^sub>2 = 0 \<Longrightarrow> sign (fsub rm fl\<^sub>1 (fl\<^sub>2:: ('e::len2,'f) float)) = 0"
    unfolding fsub_def
    apply (cases fl\<^sub>1 rule: float_cases_eqs; cases fl\<^sub>2 rule: float_cases_eqs)
    by(simp_all add: finite_infinity sign_zerosign_0_round_ge0)

  lemma sign0_fmul: "\<lbrakk>\<not>is_nan (fmul rm fl\<^sub>1 fl\<^sub>2); sign fl\<^sub>1 = 0; sign fl\<^sub>2 = 0\<rbrakk> \<Longrightarrow> sign (fmul rm fl\<^sub>1 (fl\<^sub>2:: ('e::len2,'f) float)) = 0"
    unfolding fmul_def
    apply (cases fl\<^sub>1 rule: float_cases_eqs; cases fl\<^sub>2 rule: float_cases_eqs)
    apply (simp_all add: finite_infinity is_zero_closestI Collect_mono_iff sign_zerosign0 sign_zerosign1 closest_precise)[35] 
    apply(rule P_ifI)
    apply simp
    apply(rule P_ifI)
    apply simp
    apply(rule P_ifI)
    apply (simp add: sign_zerosign_0_round_ge0 valof_nonneg)
    by presburger

  (* Legacy lemma, has unnecessary assumptions *)  
  lemma sign0_fmul_too_weak: "\<not>is_nan (fmul rm fl\<^sub>1 fl\<^sub>2) \<Longrightarrow> sign fl\<^sub>1 = 0 \<Longrightarrow> sign fl\<^sub>2 = 0 \<Longrightarrow> \<not>is_zero fl\<^sub>2 \<Longrightarrow> is_finite fl\<^sub>2 \<Longrightarrow> sign (fmul rm fl\<^sub>1 (fl\<^sub>2:: ('e::len2,'f) float)) = 0"
    by (simp add: sign0_fmul)
    
  lemma sign0_fmul_add: "\<not>is_nan (fmul_add rm fl\<^sub>1 fl\<^sub>2 fl\<^sub>3) \<Longrightarrow> sign fl\<^sub>1 = 0 \<Longrightarrow> sign fl\<^sub>2 = 0 \<Longrightarrow> \<not>is_zero fl\<^sub>2 \<Longrightarrow> is_finite fl\<^sub>2 \<Longrightarrow> sign fl\<^sub>3 = 0 \<Longrightarrow> sign (fmul_add rm fl\<^sub>1 fl\<^sub>2 (fl\<^sub>3:: ('e::len2,'f) float)) = 0"
    unfolding fmul_add_def
    apply (cases fl\<^sub>1 rule: float_cases_eqs; cases fl\<^sub>2 rule: float_cases_eqs)
    apply (simp_all add: is_zero_closestI Collect_mono_iff sign_zerosign0 sign_zerosign1 closest_precise)[35]
    apply fastforce
    subgoal
      unfolding Let_def
      apply(rule P_ifI)
      apply(rule P_ifI)
      apply force
      apply simp
      apply(rule conjI)
      by (fastforce simp: sign_pos_iff_valof sign_zerosign_0_round_ge0)+
    subgoal
      unfolding Let_def
      apply(rule P_ifI)
      apply simp
      apply(rule P_ifI)
      apply simp
      apply(rule P_ifI)
      apply simp
      apply(rule P_ifI)
      apply simp
      apply(rule P_ifI)
      apply(rule P_ifI)
      apply simp
      apply(rule P_ifI)
      apply (metis add_cancel_left_left float_cases_finite is_zero_iff_valof0 less_numeral_extra(3) nzero_fin_sign_eq_valof_gt0 pos_add_strict zero_less_mult_iff)
      apply simp
      by (auto simp: dual_order.strict_iff_not valof_nonneg sign_zerosign_0_round_ge0)
    done



  lemma mop_add_rup_real_invar:
    fixes fl\<^sub>1 fl\<^sub>2 fl\<^sub>3 :: "('e::len2,'f) float"
    assumes INV1: "nn_real_invar fl\<^sub>1"
    assumes INV2: "nn_real_invar fl\<^sub>2"
    assumes RES: "inres (mop_add_rup fl\<^sub>1 fl\<^sub>2) fl\<^sub>3"
    shows "nn_real_invar fl\<^sub>3"
  proof -
    have "\<not> is_nan fl\<^sub>3" and "sign fl\<^sub>3 = 0" 
      using INV1 INV2 RES
      unfolding mop_add_rup_def op_farith2_rm_def nanize_float_def nn_real_invar_def
      by(auto split: if_splits simp: is_nan_fadd intro!: sign0_fadd) 
    thus ?thesis
      unfolding nn_real_invar_def by simp
  qed

  lemma mop_sub_rup_real_invar:
    fixes fl\<^sub>1 fl\<^sub>2 fl\<^sub>3 :: "('e::len2,'f) float"
    assumes INV1: "nn_real_invar fl\<^sub>1"
    assumes INV2: "nn_real_invar fl\<^sub>2"
    assumes LE: "valof' fl\<^sub>2 \<le> valof' fl\<^sub>1"
    assumes NINF: "is_finite fl\<^sub>2"
    assumes RES: "inres (mop_sub_rup fl\<^sub>1 fl\<^sub>2) fl\<^sub>3"
    shows "nn_real_invar fl\<^sub>3"
  proof -
    have "\<not> is_nan fl\<^sub>3" and "sign fl\<^sub>3 = 0" 
      using INV1 INV2 LE RES NINF
      unfolding mop_sub_rup_def op_farith2_rm_def nanize_float_def nn_real_invar_def
      by(auto split: if_splits simp: is_nan_fsub intro!: sign0_fsub_fin2_nninf elim: fin_inf_any) 
    thus ?thesis
      unfolding nn_real_invar_def by simp
  qed

  lemma mop_mul_rup_real_invar:
    assumes INV1: "nn_real_invar fl\<^sub>1"
    assumes INV2: "pfin_real_invar fl\<^sub>2"
    assumes RES: "inres (mop_mul_rup fl\<^sub>1 fl\<^sub>2) fl\<^sub>3"
    shows "nn_real_invar (fl\<^sub>3 :: ('e::len2,'f) float)"
  proof -
    have "\<not> is_nan fl\<^sub>3" and "sign fl\<^sub>3 = 0"
      using INV1 INV2 RES
      unfolding mop_mul_rup_def op_farith2_rm_def nanize_float_def nn_real_invar_def pfin_real_invar_def
      by(auto split: if_splits simp: is_nan_fmul sign0_fmul intro: fin_inf_contr dest: fin_inf_contr) 
    thus ?thesis
      unfolding nn_real_invar_def by simp
  qed

  lemma mop_mul_add_rup_real_invar:
    assumes INV1: "nn_real_invar fl\<^sub>1"
    assumes INV2: "pfin_real_invar fl\<^sub>2"
    assumes INV3: "nn_real_invar fl\<^sub>3"
    assumes RES: "inres (mop_fma_rup fl\<^sub>1 fl\<^sub>2 fl\<^sub>3) fl\<^sub>4"
    shows "nn_real_invar (fl\<^sub>4 :: ('e::len2,'f) float)"
  proof -
    have A: "\<not> is_nan fl\<^sub>4" and "sign fl\<^sub>4 = 0"
      using INV1 INV2 INV3 RES
      unfolding mop_fma_rup_def op_farith3_rm_def nanize_float_def nn_real_invar_def pfin_real_invar_def
      by(auto split: if_splits simp: is_nan_fmul_add sign0_fmul_add intro: fin_inf_contr dest: fin_inf_contr) 
    thus ?thesis
      unfolding nn_real_invar_def by simp
  qed

  lemma mop_add_rdn_real_invar:
    fixes fl\<^sub>1 fl\<^sub>2 fl\<^sub>3 :: "('e::len2,'f) float"
    assumes INV1: "nn_real_invar fl\<^sub>1"
    assumes INV2: "nn_real_invar fl\<^sub>2"
    assumes RES: "inres (mop_add_rdn fl\<^sub>1 fl\<^sub>2) fl\<^sub>3"
    shows "nn_real_invar fl\<^sub>3"
  proof -
    have "\<not> is_nan fl\<^sub>3" and "sign fl\<^sub>3 = 0" 
      using INV1 INV2 RES
      unfolding mop_add_rdn_def op_farith2_rm_def nanize_float_def nn_real_invar_def
      by(auto split: if_splits simp: is_nan_fadd intro!: sign0_fadd) 
    thus ?thesis
      unfolding nn_real_invar_def by simp
  qed

  lemma mop_mul_rdn_real_invar:
    assumes INV1: "nn_real_invar fl\<^sub>1"
    assumes INV2: "pfin_real_invar fl\<^sub>2"
    assumes RES: "inres (mop_mul_rdn fl\<^sub>1 fl\<^sub>2) fl\<^sub>3"
    shows "nn_real_invar (fl\<^sub>3 :: ('e::len2,'f) float)"
  proof -
    have "\<not> is_nan fl\<^sub>3" and "sign fl\<^sub>3 = 0"
      using INV1 INV2 RES
      unfolding mop_mul_rdn_def op_farith2_rm_def nanize_float_def nn_real_invar_def pfin_real_invar_def
      by(auto split: if_splits simp: is_nan_fmul sign0_fmul intro: fin_inf_contr dest: fin_inf_contr)
    thus ?thesis
      unfolding nn_real_invar_def by simp
  qed

  lemma mop_mul_add_rdn_real_invar:
    assumes INV1: "nn_real_invar fl\<^sub>1"
    assumes INV2: "pfin_real_invar fl\<^sub>2"
    assumes INV3: "nn_real_invar fl\<^sub>3"
    assumes RES: "inres (mop_fma_rdn fl\<^sub>1 fl\<^sub>2 fl\<^sub>3) fl\<^sub>4"
    shows "nn_real_invar (fl\<^sub>4 :: ('e::len2,'f) float)"
  proof -
    have A: "\<not> is_nan fl\<^sub>4" and "sign fl\<^sub>4 = 0"
      using INV1 INV2 INV3 RES
      unfolding mop_fma_rdn_def op_farith3_rm_def nanize_float_def nn_real_invar_def pfin_real_invar_def
      by(auto split: if_splits simp: is_nan_fmul_add sign0_fmul_add intro: fin_inf_contr dest: fin_inf_contr) 
    thus ?thesis
      unfolding nn_real_invar_def by simp
  qed

  lemma nn_real_invar_op_fp64_0[simp]: "nn_real_invar op_fp64_0"
    unfolding nn_real_invar_def by simp

  lemma nn_real_invar_op_fp64_1[simp]: "nn_real_invar op_fp64_1"
    unfolding nn_real_invar_def by simp



  subsection \<open>Assertion\<close>


  definition "nn_real_ub_rel = {(fl,r). ereal r \<le> valof' fl \<and> nn_real_invar fl}"

  definition "pfin_real_ub_rel = {(fl,r). ereal r \<le> valof' fl \<and> pfin_real_invar fl}"

  lemma in_nn_real_ub_rel_conv: "(fl,r) \<in> nn_real_ub_rel \<longleftrightarrow> ereal r \<le> valof' fl \<and> nn_real_invar fl"
    unfolding nn_real_ub_rel_def by fast

  lemma in_pfin_real_ub_rel_conv: "(fl,r) \<in> pfin_real_ub_rel \<longleftrightarrow> ereal r \<le> valof' fl \<and> pfin_real_invar fl"
    unfolding pfin_real_ub_rel_def by fast


  definition "nn_real_lb_rel = {(fl,r). valof' fl \<le> ereal r \<and> nn_real_invar fl}"

  definition "pfin_real_lb_rel = {(fl,r). valof' fl \<le> ereal r \<and> pfin_real_invar fl}"

  lemma in_nn_real_lb_rel_conv: "(fl,r) \<in> nn_real_lb_rel \<longleftrightarrow> valof' fl \<le> ereal r \<and> nn_real_invar fl"
    unfolding nn_real_lb_rel_def by fast

  lemma in_pfin_real_lb_rel_conv: "(fl,r) \<in> pfin_real_lb_rel \<longleftrightarrow> valof' fl \<le> ereal r \<and> pfin_real_invar fl"
    unfolding pfin_real_lb_rel_def by fast
(*
  lemma sign0_finite: "sign fl = 0 \<Longrightarrow> \<not>is_nan fl \<Longrightarrow> valof' fl < \<infinity> \<Longrightarrow> is_finite fl"
    unfolding valof'_def using float_cases_finite[of fl] apply (auto simp: )
*)
  lemma nn_real_lb_rel_le_inf: "(fl,r) \<in> nn_real_lb_rel \<Longrightarrow> is_finite fl"
    unfolding nn_real_lb_rel_def
    apply(cases fl rule: float_cases_eqs)
    by (auto simp: nn_real_invar_def)

  lemma nn_real_lb_rel_ge0: "(fl,r) \<in> nn_real_lb_rel \<Longrightarrow> r \<ge> 0"
    unfolding nn_real_lb_rel_def nn_real_invar_def 
    using order_trans by (fastforce dest!: valof'_nonneg)

  lemma pfin_real_lb_rel_gt0: "(fl,r) \<in> pfin_real_lb_rel \<Longrightarrow> r > 0"
    unfolding pfin_real_lb_rel_def pfin_real_invar_def using float_cases_finite[of fl] 
    by (auto simp: nzero_fin_sign_eq_valof'_gt0 dest: valof_leq_ereal_ninf)

  text \<open>REMINDER: A lot of these proofs have been done in a similar manner in IEEE_Bounds.thy\<close>


  subsection \<open>Uniform basic operations\<close>

  definition "op_add_ub = (+)"
  definition "op_mul_ub = (*)"
  definition "op_fma_ub a b c = a * b + c"
  definition "op_min_ub = min"
  definition "op_max_ub = max"
  definition "op_0_ub_nn = 0"
  definition "op_1_ub_nn = 1"
(*  definition "op_0_ub = 0"
  definition "op_1_ub = 1"*)

  definition "op_add_lb = (+)"
  definition "op_mul_lb = (*)"
  definition "op_fma_lb a b c = a * b + c"
  definition "op_min_lb = min"
  definition "op_max_lb = max"
  definition "op_0_lb_nn = 0"
  definition "op_1_lb_nn = 1"
(*  definition "op_0_lb = 0"
  definition "op_1_lb = 1"*)

  subsection \<open>Mixed basic operations\<close>

  definition "op_sub_ub = (-)"
  definition "op_sub_lb = (-)"

  definition "mop_leq_sound_nn a b = SPEC(\<lambda>r. r \<longrightarrow> a \<le> b)" \<comment> \<open>upper bound/lower bound, sound comparison\<close>
  definition "mop_leq_cmplt_nn a b = SPEC(\<lambda>r. a \<le> b \<longrightarrow> r)" \<comment> \<open>lower bound/upper bound, complete comparison\<close>



  subsection \<open>Refinement Proofs\<close>

  lemma mop_add_rup_nn_correct: 
    fixes fl\<^sub>1 fl\<^sub>2 :: "('e::len2,'f) float"
    assumes F1: "(fl\<^sub>1, r\<^sub>1) \<in> nn_real_ub_rel"
    assumes F2: "(fl\<^sub>2, r\<^sub>2) \<in> nn_real_ub_rel"
    shows "mop_add_rup fl\<^sub>1 fl\<^sub>2 \<le> \<Down> nn_real_ub_rel ((Refine_Basic.RETURN \<circ>\<circ> op_add_ub) r\<^sub>1 r\<^sub>2)"
  proof -

    have A: "nofail (mop_add_rup fl\<^sub>1 fl\<^sub>2)"
      unfolding mop_add_rup_def op_farith2_rm_def nanize_float_def
      by simp

    {
      fix fl\<^sub>3
      assume RES: "inres (mop_add_rup fl\<^sub>1 fl\<^sub>2) fl\<^sub>3"
      hence B: "nn_real_invar fl\<^sub>3" and F3: "fl\<^sub>3 = fadd To_pinfinity fl\<^sub>1 fl\<^sub>2" 
        using mop_add_rup_real_invar[OF _ _ RES] F1 F2
        by(auto simp: in_nn_real_ub_rel_conv mop_add_rup_def nn_real_invar_def nnan_inres_op_farith2_rm)
      have "ereal (r\<^sub>1+r\<^sub>2) \<le> valof' (fl\<^sub>3)"
        using F1 F2 unfolding in_nn_real_ub_rel_conv nn_real_invar_def F3
        apply (cases fl\<^sub>1 rule: float_cases_eqs; cases fl\<^sub>2 rule: float_cases_eqs)
        apply (auto simp: fadd_def intro!: round_pinf_bound' dest: fin_inf_contr)
        done
      note B this
    } note B = this

    show ?thesis
      by (clarsimp simp: refine_pw_simps pw_le_iff A B in_nn_real_ub_rel_conv op_add_ub_def)
  qed

  lemma mop_mul_rup_nn_correct: 
    fixes fl\<^sub>1 fl\<^sub>2 :: "('e::len2,'f) float"
    assumes P2: "r\<^sub>2 \<ge> 0"
    assumes F1: "(fl\<^sub>1, r\<^sub>1) \<in> nn_real_ub_rel"
    assumes F2: "(fl\<^sub>2, r\<^sub>2) \<in> pfin_real_ub_rel"
    shows "mop_mul_rup fl\<^sub>1 fl\<^sub>2 \<le> \<Down> nn_real_ub_rel ((Refine_Basic.RETURN \<circ>\<circ> op_mul_ub) r\<^sub>1 r\<^sub>2)"
  proof -

    have A: "nofail (mop_mul_rup fl\<^sub>1 fl\<^sub>2)"
      unfolding mop_mul_rup_def op_farith2_rm_def nanize_float_def
      by simp

    {
      fix fl\<^sub>3
      assume RES: "inres (mop_mul_rup fl\<^sub>1 fl\<^sub>2) fl\<^sub>3"
      hence B: "nn_real_invar fl\<^sub>3" and F3: "fl\<^sub>3 = fmul To_pinfinity fl\<^sub>1 fl\<^sub>2"
        using mop_mul_rup_real_invar[OF _ _ RES] F1 F2
        by(auto simp: in_nn_real_ub_rel_conv in_pfin_real_ub_rel_conv mop_mul_rup_def nn_real_invar_def nnan_inres_op_farith2_rm)
      have "ereal (r\<^sub>1*r\<^sub>2) \<le> valof' (fl\<^sub>3)"
        using P2 F1 F2 B unfolding in_nn_real_ub_rel_conv in_pfin_real_ub_rel_conv nn_real_invar_def pfin_real_invar_def F3
        apply (cases fl\<^sub>1 rule: float_cases_eqs; cases fl\<^sub>2 rule: float_cases_eqs)
        by (auto simp: fmul_def mult_nonneg_nonpos mult_mono' sign_pos_iff_valof 
          intro!: round_pinf_bound' mult_nonpos_nonneg mult_mono dest!: fin_inf_contr) 
      note B this
    } note B = this

    show ?thesis
      by (clarsimp simp: refine_pw_simps pw_le_iff A B in_nn_real_ub_rel_conv op_mul_ub_def)
  qed


  lemma mop_fma_rup_nn_correct: 
    fixes fl\<^sub>1 fl\<^sub>2 fl\<^sub>3 :: "('e::len2,'f) float"
    assumes P2: "r\<^sub>2 \<ge> 0"
    assumes F1: "(fl\<^sub>1, r\<^sub>1) \<in> nn_real_ub_rel"
    assumes F2: "(fl\<^sub>2, r\<^sub>2) \<in> pfin_real_ub_rel"
    assumes F3: "(fl\<^sub>3, r\<^sub>3) \<in> nn_real_ub_rel"
    shows "mop_fma_rup fl\<^sub>1 fl\<^sub>2 fl\<^sub>3 \<le> \<Down> nn_real_ub_rel ((Refine_Basic.RETURN \<circ>\<circ>\<circ> op_fma_ub) r\<^sub>1 r\<^sub>2 r\<^sub>3)"
  proof -

    have A: "nofail (mop_fma_rup fl\<^sub>1 fl\<^sub>2 fl\<^sub>3)"
      unfolding mop_fma_rup_def op_farith3_rm_def nanize_float_def
      by simp

    {
      fix fl\<^sub>4
      assume RES: "inres (mop_fma_rup fl\<^sub>1 fl\<^sub>2 fl\<^sub>3) fl\<^sub>4"
      hence B: "nn_real_invar fl\<^sub>4" and F4: "fl\<^sub>4 = fmul_add To_pinfinity fl\<^sub>1 fl\<^sub>2 fl\<^sub>3"
        using mop_mul_add_rup_real_invar[OF _ _ _ RES] F1 F2 F3 pfin_real_invar_valof nn_real_invar_valof'
        by(auto simp: in_nn_real_ub_rel_conv in_pfin_real_ub_rel_conv mop_fma_rup_def nn_real_invar_def nnan_inres_op_farith3_rm)
      have "ereal (op_fma_ub r\<^sub>1 r\<^sub>2 r\<^sub>3) \<le> valof' (fl\<^sub>4)"
        using P2 F1 F2 F3 B unfolding in_nn_real_ub_rel_conv in_pfin_real_ub_rel_conv nn_real_invar_def pfin_real_invar_def F4
        apply (cases fl\<^sub>1 rule: float_cases_eqs; cases fl\<^sub>2 rule: float_cases_eqs)
        apply simp_all
        subgoal
          by (simp add: fmul_add_def Let_def)[]
        subgoal
          using float_cases_finite[of fl\<^sub>3]  mult_nonpos_nonneg
          by (fastforce 
            simp: op_fma_ub_def fmul_add_def Let_def valof'_round_valof[of fl\<^sub>3 To_pinfinity]
            intro: round_pinf_bound' intro!:  mult_nonpos_nonneg add_nonpos_nonpos
            dest: fin_inf_contr )
        subgoal
          using float_cases_finite[of fl\<^sub>3]
          by (auto dest!: valof_nonneg mult_add_ge_0
            simp: is_zero_iff_valof0 op_fma_ub_def fmul_add_def Let_def 
            intro!: round_pinf_bound' mult_mono add_mono
            elim!: valof'_finite_to_valof
          ) 

        done
      note B this
    } note B = this
    show ?thesis
      by (clarsimp simp: refine_pw_simps pw_le_iff A B in_nn_real_ub_rel_conv)
  qed

  lemma mop_add_rdn_nn_correct: 
    fixes fl\<^sub>1 fl\<^sub>2 :: "('e::len2,'f) float"
    assumes F1: "(fl\<^sub>1, r\<^sub>1) \<in> nn_real_lb_rel"
    assumes F2: "(fl\<^sub>2, r\<^sub>2) \<in> nn_real_lb_rel"
    shows "mop_add_rdn fl\<^sub>1 fl\<^sub>2 \<le> \<Down> nn_real_lb_rel ((Refine_Basic.RETURN \<circ>\<circ> op_add_lb) r\<^sub>1 r\<^sub>2)"
  proof -

    have A: "nofail (mop_add_rdn fl\<^sub>1 fl\<^sub>2)"
      unfolding mop_add_rdn_def op_farith2_rm_def nanize_float_def
      by simp

    {
      fix fl\<^sub>3
      assume RES: "inres (mop_add_rdn fl\<^sub>1 fl\<^sub>2) fl\<^sub>3"
      hence B: "nn_real_invar fl\<^sub>3" and F3: "fl\<^sub>3 = fadd To_ninfinity fl\<^sub>1 fl\<^sub>2" 
        using mop_add_rdn_real_invar[OF _ _ RES] F1 F2
        by(auto simp: in_nn_real_lb_rel_conv mop_add_rdn_def nn_real_invar_def nnan_inres_op_farith2_rm)
      have "valof' (fl\<^sub>3) \<le> ereal (r\<^sub>1+r\<^sub>2)"
        using F1 F2 unfolding in_nn_real_lb_rel_conv nn_real_invar_def F3
        apply (cases fl\<^sub>1 rule: float_cases_eqs; cases fl\<^sub>2 rule: float_cases_eqs)
        apply (auto simp: fadd_def intro!: round_ninf_bound' dest: fin_inf_contr)
        done
      note B this
    } note B = this

    show ?thesis
      by (clarsimp simp: refine_pw_simps pw_le_iff A B in_nn_real_lb_rel_conv op_add_lb_def)
  qed

  lemma mop_mul_rdn_nn_correct: 
    fixes fl\<^sub>1 fl\<^sub>2 :: "('e::len2,'f) float"
    assumes F1: "(fl\<^sub>1, r\<^sub>1) \<in> nn_real_lb_rel"
    assumes F2: "(fl\<^sub>2, r\<^sub>2) \<in> pfin_real_lb_rel"
    shows "mop_mul_rdn fl\<^sub>1 fl\<^sub>2 \<le> \<Down> nn_real_lb_rel ((Refine_Basic.RETURN \<circ>\<circ> op_mul_lb) r\<^sub>1 r\<^sub>2)"
  proof -

    have A: "nofail (mop_mul_rdn fl\<^sub>1 fl\<^sub>2)"
      unfolding mop_mul_rdn_def op_farith2_rm_def nanize_float_def
      by simp

    {
      fix fl\<^sub>3
      assume RES: "inres (mop_mul_rdn fl\<^sub>1 fl\<^sub>2) fl\<^sub>3"
      hence B: "nn_real_invar fl\<^sub>3" and F3: "fl\<^sub>3 = fmul To_ninfinity fl\<^sub>1 fl\<^sub>2"
        using mop_mul_rdn_real_invar[OF _ _ RES] F1 F2
        by(auto simp: in_nn_real_lb_rel_conv in_pfin_real_lb_rel_conv mop_mul_rdn_def nn_real_invar_def nnan_inres_op_farith2_rm)
      have "valof' (fl\<^sub>3) \<le> ereal (r\<^sub>1*r\<^sub>2)"
        using F1 F2 B unfolding in_nn_real_lb_rel_conv in_pfin_real_lb_rel_conv nn_real_invar_def pfin_real_invar_def F3
        apply (cases fl\<^sub>1 rule: float_cases_eqs; cases fl\<^sub>2 rule: float_cases_eqs)
        by (auto simp: fmul_def mult_nonneg_nonpos mult_mono' sign_pos_iff_valof intro!: round_ninf_bound' dest: fin_inf_contr) 
      note B this
    } note B = this

    show ?thesis
      by (clarsimp simp: refine_pw_simps pw_le_iff A B in_nn_real_lb_rel_conv op_mul_lb_def)
  qed

  lemma mop_fma_rdn_nn_correct: 
    fixes fl\<^sub>1 fl\<^sub>2 fl\<^sub>3 :: "('e::len2,'f) float"
    assumes F1: "(fl\<^sub>1, r\<^sub>1) \<in> nn_real_lb_rel"
    assumes F2: "(fl\<^sub>2, r\<^sub>2) \<in> pfin_real_lb_rel"
    assumes F3: "(fl\<^sub>3, r\<^sub>3) \<in> nn_real_lb_rel"
    shows "mop_fma_rdn fl\<^sub>1 fl\<^sub>2 fl\<^sub>3 \<le> \<Down> nn_real_lb_rel ((Refine_Basic.RETURN \<circ>\<circ>\<circ> op_fma_lb) r\<^sub>1 r\<^sub>2 r\<^sub>3)"
  proof -

    have P1: "r\<^sub>1 \<ge> 0"
      using nn_real_lb_rel_ge0[OF F1] .
    have P2: "r\<^sub>2 > 0" using pfin_real_lb_rel_gt0[OF F2] .
    have P3: "r\<^sub>3 \<ge> 0" using nn_real_lb_rel_ge0[OF F3] .

    have A: "nofail (mop_fma_rdn fl\<^sub>1 fl\<^sub>2 fl\<^sub>3)"
      unfolding mop_fma_rdn_def op_farith3_rm_def nanize_float_def
      by simp

    {
      fix fl\<^sub>4
      assume RES: "inres (mop_fma_rdn fl\<^sub>1 fl\<^sub>2 fl\<^sub>3) fl\<^sub>4"
      hence B: "nn_real_invar fl\<^sub>4" and F4: "fl\<^sub>4 = fmul_add To_ninfinity fl\<^sub>1 fl\<^sub>2 fl\<^sub>3"
        using mop_mul_add_rdn_real_invar[OF _ _ _ RES] F1 F2 F3 pfin_real_invar_valof nn_real_invar_valof'
        by(auto simp: in_nn_real_lb_rel_conv in_pfin_real_lb_rel_conv mop_fma_rdn_def nn_real_invar_def nnan_inres_op_farith3_rm)
      have "valof' (fl\<^sub>4) \<le> ereal (op_fma_lb r\<^sub>1 r\<^sub>2 r\<^sub>3)"
        using F1 F2 F3 B unfolding in_nn_real_lb_rel_conv in_pfin_real_lb_rel_conv nn_real_invar_def pfin_real_invar_def F4
        apply (cases fl\<^sub>1 rule: float_cases_eqs; cases fl\<^sub>2 rule: float_cases_eqs; cases fl\<^sub>3 rule: float_cases_eqs)
        apply simp_all        
        subgoal using P1 P2 P3 
          by (auto simp: fmul_add_def op_fma_lb_def Let_def)
        subgoal using P1 P2 P3 
          by (auto simp: fmul_add_def op_fma_lb_def is_infinity_alt Let_def 
            dest: valof_leq_ereal_ninf split: if_splits
            intro!: round_ninf_bound' intro: add_increasing)
        subgoal using P1 P2 P3 
          by(auto simp: fmul_add_def op_fma_lb_def Let_def valof_nonneg 
            intro!: round_ninf_bound' add_increasing2 mult_mono)
        subgoal using P1 P2 P3 
          by(auto simp: fmul_add_def op_fma_lb_def Let_def valof_nonneg 
            intro!: round_ninf_bound' mult_mono add_mono)
        done
      note B this
    } note B = this
    show ?thesis
      by (clarsimp simp: refine_pw_simps pw_le_iff A B in_nn_real_lb_rel_conv)
  qed

  lemma mop_sub_rup_nn_correct: 
    fixes fl\<^sub>1 fl\<^sub>2 :: "('e::len2,'f) float"
    assumes LE: "r\<^sub>2 \<le> r\<^sub>1"
    assumes F1: "(fl\<^sub>1, r\<^sub>1) \<in> nn_real_ub_rel"
    assumes F2: "(fl\<^sub>2, r\<^sub>2) \<in> nn_real_lb_rel"
    shows "mop_sub_rup fl\<^sub>1 fl\<^sub>2 \<le> \<Down> nn_real_ub_rel ((Refine_Basic.RETURN \<circ>\<circ> op_sub_ub) r\<^sub>1 r\<^sub>2)"
  proof -

    have A: "nofail (mop_sub_rup fl\<^sub>1 fl\<^sub>2)"
      unfolding mop_sub_rup_def op_farith2_rm_def nanize_float_def
      by simp

    have AUX1: "is_finite fl\<^sub>2" using nn_real_lb_rel_le_inf[OF F2] .

    from F1 F2 have AUX2: "valof' fl\<^sub>2 \<le> valof' fl\<^sub>1"
      unfolding nn_real_ub_rel_def nn_real_lb_rel_def
      using le_ereal_le[OF _ LE] order_trans by fast
    {
      fix fl\<^sub>3
      assume RES: "inres (mop_sub_rup fl\<^sub>1 fl\<^sub>2) fl\<^sub>3"
      hence B: "nn_real_invar fl\<^sub>3" and F3: "fl\<^sub>3 = fsub To_pinfinity fl\<^sub>1 fl\<^sub>2" 
        using mop_sub_rup_real_invar[OF _ _ AUX2 AUX1 RES] F1 F2
        by(auto simp: in_nn_real_ub_rel_conv in_nn_real_lb_rel_conv mop_sub_rup_def nn_real_invar_def nnan_inres_op_farith2_rm)
      have "ereal (r\<^sub>1-r\<^sub>2) \<le> valof' (fl\<^sub>3)"
        using F1 F2 unfolding in_nn_real_ub_rel_conv in_nn_real_lb_rel_conv nn_real_invar_def F3
        apply (cases fl\<^sub>1 rule: float_cases_eqs; cases fl\<^sub>2 rule: float_cases_eqs)
        apply (auto simp: fsub_def intro!: round_pinf_bound' dest: fin_inf_contr)
        done
      note B this
    } note B = this

    show ?thesis
      by (clarsimp simp: refine_pw_simps pw_le_iff A B in_nn_real_ub_rel_conv op_sub_ub_def)
  qed

  lemma mop_leq_sound_nn_correct:
    fixes fl\<^sub>1 fl\<^sub>2 fl\<^sub>3 :: "('e,'f) float"
    assumes F1: "(fl\<^sub>1, r\<^sub>1) \<in> nn_real_ub_rel"
    assumes F2: "(fl\<^sub>2, r\<^sub>2) \<in> nn_real_lb_rel"
    shows "RETURN (op_ole_d fl\<^sub>1 fl\<^sub>2) \<le> mop_leq_sound_nn r\<^sub>1 r\<^sub>2"
  proof -

    from F1 F2 have NN1: "\<not> is_nan fl\<^sub>1" and NN2: "\<not> is_nan fl\<^sub>2"
      unfolding nn_real_ub_rel_def nn_real_lb_rel_def nn_real_invar_def
      by auto


    have "valof' fl\<^sub>1 \<le> valof' fl\<^sub>2 \<Longrightarrow> ereal r\<^sub>1 \<le> ereal r\<^sub>2"
      apply(rule order_trans[of _ "valof' fl\<^sub>1"])
      using F1 unfolding nn_real_ub_rel_def apply blast
      apply(rule order_trans[of _ "valof' fl\<^sub>2"])
      apply assumption
      using F2 unfolding nn_real_lb_rel_def by blast

    thus ?thesis
      unfolding mop_leq_sound_nn_def op_ole_valof'_le[OF NN1 NN2]
      by auto
  qed

  lemma mop_leq_cmplt_nn_correct:
    fixes fl\<^sub>1 fl\<^sub>2 fl\<^sub>3 :: "('e,'f) float"
    assumes F1: "(fl\<^sub>1, r\<^sub>1) \<in> nn_real_lb_rel"
    assumes F2: "(fl\<^sub>2, r\<^sub>2) \<in> nn_real_ub_rel"
    shows "RETURN (op_ole_d fl\<^sub>1 fl\<^sub>2) \<le> mop_leq_cmplt_nn r\<^sub>1 r\<^sub>2"
  proof -

    from F1 F2 have NN1: "\<not> is_nan fl\<^sub>1" and NN2: "\<not> is_nan fl\<^sub>2"
      unfolding nn_real_ub_rel_def nn_real_lb_rel_def nn_real_invar_def
      by auto


    have "ereal r\<^sub>1 \<le> ereal r\<^sub>2 \<Longrightarrow> valof' fl\<^sub>1 \<le> valof' fl\<^sub>2"
      apply(rule order_trans[of _ "ereal r\<^sub>1"])
      using F1 unfolding nn_real_lb_rel_def apply blast
      apply(rule order_trans[of _ "ereal r\<^sub>2"])
      apply assumption
      using F2 unfolding nn_real_ub_rel_def by blast

    thus ?thesis
      unfolding mop_leq_cmplt_nn_def op_ole_valof'_le[OF NN1 NN2]
      by auto
  qed

  lemma op_add_ub_nn_refine: "(mop_add_rup, RETURN oo op_add_ub) \<in> nn_real_ub_rel \<rightarrow> nn_real_ub_rel \<rightarrow> \<langle>nn_real_ub_rel\<rangle>nres_rel"
    by (refine_vcg mop_add_rup_nn_correct)

  lemma op_mul_ub_nn_refine: "(uncurry mop_mul_rup, uncurry (RETURN oo op_mul_ub)) \<in> [\<lambda> (r\<^sub>1,r\<^sub>2). 0 \<le> r\<^sub>2]\<^sub>f nn_real_ub_rel \<times>\<^sub>r pfin_real_ub_rel \<rightarrow> \<langle>nn_real_ub_rel\<rangle>nres_rel"
    apply (rule frefI)
    apply(refine_vcg )
    using mop_mul_rup_nn_correct by force

  lemma op_fma_ub_nn_refine: "(uncurry2 mop_fma_rup, uncurry2 (RETURN ooo op_fma_ub)) \<in> [(\<lambda> ((r\<^sub>1,r\<^sub>2),r\<^sub>3). 0 \<le> r\<^sub>2)]\<^sub>f (nn_real_ub_rel \<times>\<^sub>r pfin_real_ub_rel) \<times>\<^sub>r nn_real_ub_rel \<rightarrow> \<langle>nn_real_ub_rel\<rangle>nres_rel"
    apply (rule frefI)
    apply(refine_vcg )
    using mop_fma_rup_nn_correct by force

  lemma op_min_ub_nn_refine: "(op_min_double, op_min_ub) \<in> nn_real_ub_rel \<rightarrow> nn_real_ub_rel \<rightarrow> nn_real_ub_rel"
    apply(refine_vcg )
    unfolding in_nn_real_ub_rel_conv op_min_double_def op_min_ub_def
    using min_le_iff_disj by auto 

  lemma op_max_ub_nn_refine: "(op_max_double, op_max_ub) \<in> nn_real_ub_rel \<rightarrow> nn_real_ub_rel \<rightarrow> nn_real_ub_rel"
    apply(refine_vcg )
    unfolding in_nn_real_ub_rel_conv op_max_double_def op_max_ub_def
    apply (clarsimp simp: nn_real_invar_def op_ole_valof'_le split!: if_splits)
    apply (meson op_ole_le op_ole_valof'_le order_transE)
    by (meson linorder_le_cases op_ole_le op_ole_valof'_le order_transE)
    
    
  lemma op_0_ub_nn_refine: "(op_fp64_0, op_0_ub_nn) \<in> nn_real_ub_rel"
    unfolding nn_real_ub_rel_def op_0_ub_nn_def
    by auto

  lemma op_1_ub_nn_refine: "(op_fp64_1, op_1_ub_nn) \<in> nn_real_ub_rel"
    unfolding nn_real_ub_rel_def op_1_ub_nn_def
    by auto

  lemma op_add_lb_nn_refine: "(mop_add_rdn, RETURN oo op_add_lb) \<in> nn_real_lb_rel \<rightarrow> nn_real_lb_rel \<rightarrow> \<langle>nn_real_lb_rel\<rangle>nres_rel"
    by (refine_vcg mop_add_rdn_nn_correct)

  lemma op_mul_lb_nn_refine: "(mop_mul_rdn, (RETURN oo op_mul_lb)) \<in> nn_real_lb_rel \<rightarrow> pfin_real_lb_rel \<rightarrow> \<langle>nn_real_lb_rel\<rangle>nres_rel"
    by(refine_vcg mop_mul_rdn_nn_correct)

  lemma op_fma_lb_nn_refine: "(mop_fma_rdn, (RETURN ooo op_fma_lb)) \<in> nn_real_lb_rel \<rightarrow> pfin_real_lb_rel \<rightarrow> nn_real_lb_rel \<rightarrow> \<langle>nn_real_lb_rel\<rangle>nres_rel"
    by(refine_vcg mop_fma_rdn_nn_correct)

  lemma op_min_lb_nn_refine: "(op_min_double, op_min_lb) \<in> nn_real_lb_rel \<rightarrow> nn_real_lb_rel \<rightarrow> nn_real_lb_rel"
    apply(refine_vcg )
    unfolding in_nn_real_lb_rel_conv op_min_double_def op_min_lb_def
    apply (clarsimp simp: nn_real_invar_def op_ole_valof'_le split!: if_splits)
    apply (meson op_ole_le op_ole_valof'_le order_transE)
    by (meson linorder_le_cases op_ole_le op_ole_valof'_le order_transE)

  lemma op_max_lb_nn_refine: "(op_max_double, op_max_lb) \<in> nn_real_lb_rel \<rightarrow> nn_real_lb_rel \<rightarrow> nn_real_lb_rel"
    apply(refine_vcg )
    unfolding in_nn_real_lb_rel_conv op_max_double_def op_max_lb_def
    using le_max_iff_disj by auto

  lemma op_0_lb_nn_refine: "(op_fp64_0, op_0_lb_nn) \<in> nn_real_lb_rel"
    unfolding nn_real_lb_rel_def op_0_lb_nn_def
    by auto

  lemma op_1_lb_nn_refine: "(op_fp64_1, op_1_lb_nn) \<in> nn_real_lb_rel"
    unfolding nn_real_lb_rel_def op_1_lb_nn_def
    by auto

  lemma mop_sub_rup_nn_refine: "(uncurry mop_sub_rup, uncurry (RETURN oo op_sub_ub)) \<in> [\<lambda> (r\<^sub>1,r\<^sub>2). r\<^sub>2 \<le> r\<^sub>1]\<^sub>f nn_real_ub_rel \<times>\<^sub>r nn_real_lb_rel \<rightarrow> \<langle>nn_real_ub_rel\<rangle>nres_rel"
    apply (rule frefI)
    apply(refine_vcg )
    using mop_sub_rup_nn_correct by fastforce

  lemma mop_leq_sound_nn_refine: "((RETURN oo op_ole_d), mop_leq_sound_nn) \<in> nn_real_ub_rel \<rightarrow> nn_real_lb_rel \<rightarrow> \<langle>bool_rel\<rangle>nres_rel"
    apply(refine_vcg )
    by (auto simp: mop_leq_sound_nn_correct)

  lemma mop_leq_cmplt_nn_refine: "((RETURN oo op_ole_d), mop_leq_cmplt_nn) \<in> nn_real_lb_rel \<rightarrow> nn_real_ub_rel \<rightarrow> \<langle>bool_rel\<rangle>nres_rel"
    apply(refine_vcg )
    by (auto simp: mop_leq_cmplt_nn_correct)


  subsection \<open>Assertions\<close>

  lift_definition ereal_of_double :: "double \<Rightarrow> ereal" is valof' .
  lift_definition sign_double :: "double \<Rightarrow> nat" is sign .

  definition "nn_real_ub_double_rel = {(fl,r). ereal r \<le> ereal_of_double fl \<and> \<not>is_nan_double fl \<and> sign_double fl = 0}"
  definition "pfin_real_ub_double_rel = {(fl,r). ereal r \<le> ereal_of_double fl \<and> \<not>is_nan_double fl \<and> \<not>is_zero_double fl \<and> is_finite_double fl \<and> sign_double fl = 0}"

  lemma nn_real_ub_double_rel_alt: "nn_real_ub_double_rel = dfloat_rel O nn_real_ub_rel"
    unfolding nn_real_ub_double_rel_def dfloat_rel_def nn_real_ub_rel_def nn_real_invar_def
    by (auto simp: in_br_conv br_comp_alt; transfer; blast) 

  lemma pfin_real_ub_double_rel_alt: "pfin_real_ub_double_rel = dfloat_rel O pfin_real_ub_rel"
    unfolding pfin_real_ub_double_rel_def dfloat_rel_def pfin_real_ub_rel_def pfin_real_invar_def
    by (auto simp: in_br_conv br_comp_alt; transfer; auto dest: finite_infinity) 

  definition "nn_real_lb_double_rel = {(fl,r). ereal_of_double fl \<le> ereal r \<and> \<not>is_nan_double fl \<and> sign_double fl = 0}"
  definition "pfin_real_lb_double_rel = {(fl,r). ereal_of_double fl \<le> ereal r \<and> \<not>is_nan_double fl \<and> \<not>is_zero_double fl \<and> is_finite_double fl \<and> sign_double fl = 0}"

  lemma nn_real_lb_double_rel_alt: "nn_real_lb_double_rel = dfloat_rel O nn_real_lb_rel"
    unfolding nn_real_lb_double_rel_def dfloat_rel_def nn_real_lb_rel_def nn_real_invar_def
    by (auto simp: in_br_conv br_comp_alt; transfer; blast) 

  lemma pfin_real_lb_double_rel_alt: "pfin_real_lb_double_rel = dfloat_rel O pfin_real_lb_rel"
    unfolding pfin_real_lb_double_rel_def dfloat_rel_def pfin_real_lb_rel_def pfin_real_invar_def
    by (auto simp: in_br_conv br_comp_alt; transfer; auto dest: finite_infinity) 


  abbreviation "nn_real_ub_assn \<equiv> pure nn_real_ub_double_rel"
  abbreviation "pfin_real_ub_assn \<equiv> pure pfin_real_ub_double_rel"

  abbreviation "nn_real_lb_assn \<equiv> pure nn_real_lb_double_rel"
  abbreviation "pfin_real_lb_assn \<equiv> pure pfin_real_lb_double_rel"


  lemma nn_real_ub_assn_alt: "nn_real_ub_assn = pure (dfloat_rel O nn_real_ub_rel)"
    unfolding nn_real_ub_double_rel_alt by(rule refl)

  lemma pfin_real_ub_assn_alt: "pfin_real_ub_assn = pure (dfloat_rel O pfin_real_ub_rel)"
    unfolding pfin_real_ub_double_rel_alt by(rule refl)

  lemma nn_real_lb_assn_alt: "nn_real_lb_assn = pure (dfloat_rel O nn_real_lb_rel)"
    unfolding nn_real_lb_double_rel_alt by(rule refl)

  lemma pfin_real_lb_assn_alt: "pfin_real_lb_assn = pure (dfloat_rel O pfin_real_lb_rel)"
    unfolding pfin_real_lb_double_rel_alt by(rule refl)

  sepref_register 
    add_ub_real:   "op_add_ub::real\<Rightarrow>_"           :: "real \<Rightarrow> real \<Rightarrow> real"
    mul_ub_real:   "op_mul_ub::real\<Rightarrow>_"           :: "real \<Rightarrow> real \<Rightarrow> real"
    fma_ub_real:   "op_fma_ub::real\<Rightarrow>_"           :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real"
    min_ub_real:   "op_min_ub::real\<Rightarrow>_"           :: "real \<Rightarrow> real \<Rightarrow> real"
    max_ub_real:   "op_max_ub::real\<Rightarrow>_"           :: "real \<Rightarrow> real \<Rightarrow> real"
    zero_ub_real:  "op_0_ub_nn::real"             :: "real"
    one_ub_real:   "op_1_ub_nn::real"             :: "real"

    add_lb_real:   "op_add_lb::real\<Rightarrow>_"           :: "real \<Rightarrow> real \<Rightarrow> real"
    mul_lb_real:   "op_mul_lb::real\<Rightarrow>_"           :: "real \<Rightarrow> real \<Rightarrow> real"
    fma_lb_real:   "op_fma_lb::real\<Rightarrow>_"           :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real"
    min_lb_real:   "op_min_lb::real\<Rightarrow>_"           :: "real \<Rightarrow> real \<Rightarrow> real"
    max_lb_real:   "op_max_lb::real\<Rightarrow>_"           :: "real \<Rightarrow> real \<Rightarrow> real"
    zero_lb_real:  "op_0_lb_nn::real"             :: "real"
    one_lb_real:   "op_1_lb_nn::real"             :: "real"

    sub_ub_real:   "op_sub_ub::real\<Rightarrow>_"           :: "real \<Rightarrow> real \<Rightarrow> real"
    leq_sound_real:"mop_leq_sound_nn::real\<Rightarrow>_"    :: "real \<Rightarrow> real \<Rightarrow> bool nres"
    leq_cmplt_real:"mop_leq_cmplt_nn::real\<Rightarrow>_"    :: "real \<Rightarrow> real \<Rightarrow> bool nres"



    context
      notes [fcomp_norm_unfold] = nn_real_ub_assn_alt[symmetric] pfin_real_ub_assn_alt[symmetric]
        nn_real_lb_assn_alt[symmetric] pfin_real_lb_assn_alt[symmetric]
    begin
      lemmas op_add_ub_nn_hnr[sepref_fr_rules]     = mop_add_rup_hnr[FCOMP op_add_ub_nn_refine]
      lemmas op_mul_ub_nn_hnr[sepref_fr_rules]     = mop_mul_rup_hnr[FCOMP op_mul_ub_nn_refine]
      lemmas op_fma_ub_nn_hnr[sepref_fr_rules]     = mop_fma_rup_hnr[FCOMP op_fma_ub_nn_refine]
      lemmas op_min_ub_nn_hnr[sepref_fr_rules]     = op_min_double_ll.refine[FCOMP op_min_ub_nn_refine]
      lemmas op_max_ub_nn_hnr[sepref_fr_rules]     = op_max_double_ll.refine[FCOMP op_max_ub_nn_refine]
      lemmas op_0_ub_nn_hnr[sepref_fr_rules]       = op_fp64_0_ll.refine[FCOMP op_0_ub_nn_refine]
      lemmas op_1_ub_nn_hnr[sepref_fr_rules]       = op_fp64_1_ll.refine[FCOMP op_1_ub_nn_refine]

      lemmas op_add_lb_nn_hnr[sepref_fr_rules]     = mop_add_rdn_hnr[FCOMP op_add_lb_nn_refine]
      lemmas op_mul_lb_nn_hnr[sepref_fr_rules]     = mop_mul_rdn_hnr[FCOMP op_mul_lb_nn_refine]
      lemmas op_fma_lb_nn_hnr[sepref_fr_rules]     = mop_fma_rdn_hnr[FCOMP op_fma_lb_nn_refine]
      lemmas op_min_lb_nn_hnr[sepref_fr_rules]     = op_min_double_ll.refine[FCOMP op_min_lb_nn_refine]
      lemmas op_max_lb_nn_hnr[sepref_fr_rules]     = op_max_double_ll.refine[FCOMP op_max_lb_nn_refine]
      lemmas op_0_lb_nn_hnr[sepref_fr_rules]       = op_fp64_0_ll.refine[FCOMP op_0_lb_nn_refine]
      lemmas op_1_lb_nn_hnr[sepref_fr_rules]       = op_fp64_1_ll.refine[FCOMP op_1_lb_nn_refine]

      lemmas op_sub_ub_hnr[sepref_fr_rules]        = mop_sub_rup_hnr[FCOMP mop_sub_rup_nn_refine]
      lemmas mop_leq_sound_nn_hnr[sepref_fr_rules] = op_ole_d_hnr[FCOMP mop_leq_sound_nn_refine]
      lemmas mop_leq_cmplt_nn_hnr[sepref_fr_rules] = op_ole_d_hnr[FCOMP mop_leq_cmplt_nn_refine]
    end


  section \<open>Interval real double precision assn\<close>

  text \<open>
    This assertion represents input data where the real value lies in between two floating-point 
    values. The higher value is considered the upper bound and the lower value is considered the
    lower bound.
  \<close>

  definition "pfin_real_intv_rel = {((fl\<^sub>l,fl\<^sub>u),r). valof' fl\<^sub>l \<le> ereal r \<and> ereal r \<le> valof' fl\<^sub>u \<and> pfin_real_invar fl\<^sub>l \<and> pfin_real_invar fl\<^sub>u}"

  lemma pfin_real_intv_rel_gt0: "((fl\<^sub>l,fl\<^sub>u),r) \<in> pfin_real_intv_rel \<Longrightarrow> r > 0"
    unfolding pfin_real_intv_rel_def pfin_real_invar_def
    by (auto simp: nzero_fin_sign_eq_valof'_gt0 dest: valof_leq_ereal_ninf)

  lemma pfin_real_intv_lb: "((fl\<^sub>l,fl\<^sub>u),r) \<in> pfin_real_intv_rel \<Longrightarrow> (fl\<^sub>l,r) \<in> pfin_real_lb_rel"
    unfolding pfin_real_intv_rel_def pfin_real_lb_rel_def by blast

  lemma pfin_real_intv_ub: "((fl\<^sub>l,fl\<^sub>u),r) \<in> pfin_real_intv_rel \<Longrightarrow> (fl\<^sub>u,r) \<in> pfin_real_ub_rel"
    unfolding pfin_real_intv_rel_def pfin_real_ub_rel_def by blast

  subsection \<open>Operations on intervals\<close>

  definition mop_mul_intv_rup :: "('e::len2, 'f) float \<Rightarrow> ('e::len2, 'f) float \<times> ('e::len2, 'f) float \<Rightarrow> ('e::len2, 'f) float nres" where 
    "mop_mul_intv_rup = (\<lambda> fl\<^sub>1 (fl\<^sub>l,fl\<^sub>u). mop_mul_rup fl\<^sub>1 fl\<^sub>u)"
  sepref_register mop_mul_intv_rup

  definition mop_fma_intv_rup :: "('e::len2, 'f) float \<Rightarrow> ('e::len2, 'f) float \<times> ('e::len2, 'f) float \<Rightarrow> ('e::len2, 'f) float \<Rightarrow> ('e::len2, 'f) float nres" where
    "mop_fma_intv_rup = (\<lambda> fl\<^sub>1 (fl\<^sub>l,fl\<^sub>u) fl\<^sub>3. mop_fma_rup fl\<^sub>1 fl\<^sub>u fl\<^sub>3)"
  sepref_register mop_fma_intv_rup

  definition mop_mul_intv_rdn :: "('e::len2, 'f) float \<Rightarrow> ('e::len2, 'f) float \<times> ('e::len2, 'f) float \<Rightarrow> ('e::len2, 'f) float nres" where 
    "mop_mul_intv_rdn = (\<lambda> fl\<^sub>1 (fl\<^sub>l,fl\<^sub>u). mop_mul_rdn fl\<^sub>1 fl\<^sub>l)"
  sepref_register mop_mul_intv_rdn

  definition mop_fma_intv_rdn :: "('e::len2, 'f) float \<Rightarrow> ('e::len2, 'f) float \<times> ('e::len2, 'f) float \<Rightarrow> ('e::len2, 'f) float \<Rightarrow> ('e::len2, 'f) float nres" where
    "mop_fma_intv_rdn = (\<lambda> fl\<^sub>1 (fl\<^sub>l,fl\<^sub>u) fl\<^sub>3. mop_fma_rdn fl\<^sub>1 fl\<^sub>l fl\<^sub>3)"
  sepref_register mop_fma_intv_rdn

  sepref_def mop_mul_intv_rup_ll is "uncurry mop_mul_intv_rup" :: "dfloat_assn\<^sup>k *\<^sub>a dfloat_intv_assn\<^sup>k \<rightarrow>\<^sub>a dfloat_assn"
    unfolding mop_mul_intv_rup_def
    apply sepref
    done

  sepref_def mop_fma_intv_rup_ll is "uncurry2 mop_fma_intv_rup" :: "dfloat_assn\<^sup>k *\<^sub>a dfloat_intv_assn\<^sup>k *\<^sub>a dfloat_assn\<^sup>k \<rightarrow>\<^sub>a dfloat_assn"
    unfolding mop_fma_intv_rup_def
    apply sepref
    done

  sepref_def mop_mul_intv_rdn_ll is "uncurry mop_mul_intv_rdn" :: "dfloat_assn\<^sup>k *\<^sub>a dfloat_intv_assn\<^sup>k \<rightarrow>\<^sub>a dfloat_assn"
    unfolding mop_mul_intv_rdn_def
    apply sepref
    done

  sepref_def mop_fma_intv_rdn_ll is "uncurry2 mop_fma_intv_rdn" :: "dfloat_assn\<^sup>k *\<^sub>a dfloat_intv_assn\<^sup>k *\<^sub>a dfloat_assn\<^sup>k \<rightarrow>\<^sub>a dfloat_assn"
    unfolding mop_fma_intv_rdn_def
    apply sepref
    done

  subsection \<open>Correctness of operations\<close>

  lemma mop_mul_rup_nn_intv_correct: 
    fixes fl\<^sub>1 fl\<^sub>l fl\<^sub>u :: "('e::len2,'f) float"
    assumes F1: "(fl\<^sub>1, r\<^sub>1) \<in> nn_real_ub_rel"
    assumes F2: "((fl\<^sub>l,fl\<^sub>u), r\<^sub>2) \<in> pfin_real_intv_rel"
    shows "mop_mul_intv_rup fl\<^sub>1 (fl\<^sub>l,fl\<^sub>u) \<le> \<Down> nn_real_ub_rel ((Refine_Basic.RETURN \<circ>\<circ> op_mul_ub) r\<^sub>1 r\<^sub>2)"
    unfolding mop_mul_intv_rup_def
    using mop_mul_rup_nn_correct[OF _ F1 pfin_real_intv_ub[OF F2]] pfin_real_intv_rel_gt0[OF F2]
    by force


  lemma mop_fma_rup_nn_intv_correct: 
    fixes fl\<^sub>1 fl\<^sub>l fl\<^sub>u fl\<^sub>3 :: "('e::len2,'f) float"
    assumes F1: "(fl\<^sub>1, r\<^sub>1) \<in> nn_real_ub_rel"
    assumes F2: "((fl\<^sub>l,fl\<^sub>u), r\<^sub>2) \<in> pfin_real_intv_rel"
    assumes F3: "(fl\<^sub>3, r\<^sub>3) \<in> nn_real_ub_rel"
    shows "mop_fma_intv_rup fl\<^sub>1 (fl\<^sub>l,fl\<^sub>u) fl\<^sub>3 \<le> \<Down> nn_real_ub_rel ((Refine_Basic.RETURN \<circ>\<circ>\<circ> op_fma_ub) r\<^sub>1 r\<^sub>2 r\<^sub>3)"
    unfolding mop_fma_intv_rup_def
    using mop_fma_rup_nn_correct[OF _ F1 pfin_real_intv_ub[OF F2] F3] pfin_real_intv_rel_gt0[OF F2]
    by force


  lemma mop_mul_rdn_nn_intv_correct: 
    fixes fl\<^sub>1 fl\<^sub>l fl\<^sub>u :: "('e::len2,'f) float"
    assumes F1: "(fl\<^sub>1, r\<^sub>1) \<in> nn_real_lb_rel"
    assumes F2: "((fl\<^sub>l,fl\<^sub>u), r\<^sub>2) \<in> pfin_real_intv_rel"
    shows "mop_mul_intv_rdn fl\<^sub>1 (fl\<^sub>l,fl\<^sub>u) \<le> \<Down> nn_real_lb_rel ((Refine_Basic.RETURN \<circ>\<circ> op_mul_lb) r\<^sub>1 r\<^sub>2)"
    unfolding mop_mul_intv_rdn_def
    using mop_mul_rdn_nn_correct[OF F1 pfin_real_intv_lb[OF F2]] by simp

  lemma mop_fma_rdn_nn_intv_correct: 
    fixes fl\<^sub>1 fl\<^sub>l fl\<^sub>u fl\<^sub>3 :: "('e::len2,'f) float"
    assumes F1: "(fl\<^sub>1, r\<^sub>1) \<in> nn_real_lb_rel"
    assumes F2: "((fl\<^sub>l,fl\<^sub>u), r\<^sub>2) \<in> pfin_real_intv_rel"
    assumes F3: "(fl\<^sub>3, r\<^sub>3) \<in> nn_real_lb_rel"
    shows "mop_fma_intv_rdn fl\<^sub>1 (fl\<^sub>l,fl\<^sub>u) fl\<^sub>3 \<le> \<Down> nn_real_lb_rel ((Refine_Basic.RETURN \<circ>\<circ>\<circ> op_fma_lb) r\<^sub>1 r\<^sub>2 r\<^sub>3)"
    unfolding mop_fma_intv_rdn_def
    using mop_fma_rdn_nn_correct[OF F1 pfin_real_intv_lb[OF F2] F3] by simp


  lemma op_mul_ub_nn_intv_refine: "(mop_mul_intv_rup, RETURN oo op_mul_ub) \<in> nn_real_ub_rel \<rightarrow> pfin_real_intv_rel \<rightarrow> \<langle>nn_real_ub_rel\<rangle>nres_rel"
    apply refine_vcg
    using mop_mul_rup_nn_intv_correct by force

  lemma op_fma_ub_nn_intv_refine: "(mop_fma_intv_rup, RETURN ooo op_fma_ub) \<in> nn_real_ub_rel \<rightarrow> pfin_real_intv_rel \<rightarrow> nn_real_ub_rel \<rightarrow> \<langle>nn_real_ub_rel\<rangle>nres_rel"
    apply refine_vcg
    using mop_fma_rup_nn_intv_correct by force

  lemma op_mul_lb_nn_intv_refine: "(mop_mul_intv_rdn, RETURN oo op_mul_lb) \<in> nn_real_lb_rel \<rightarrow> pfin_real_intv_rel \<rightarrow> \<langle>nn_real_lb_rel\<rangle>nres_rel"
    apply refine_vcg 
    using mop_mul_rdn_nn_intv_correct by fast

  lemma op_fma_lb_nn_intv_refine: "(mop_fma_intv_rdn, (RETURN ooo op_fma_lb)) \<in> nn_real_lb_rel \<rightarrow> pfin_real_intv_rel \<rightarrow> nn_real_lb_rel \<rightarrow> \<langle>nn_real_lb_rel\<rangle>nres_rel"
    apply refine_vcg 
    using mop_fma_rdn_nn_intv_correct by fast

  definition "pfin_real_intv_double_rel = {((fl\<^sub>l,fl\<^sub>u),r). ereal_of_double fl\<^sub>l \<le> ereal r \<and> ereal r \<le> ereal_of_double fl\<^sub>u \<and> \<not>is_nan_double fl\<^sub>l \<and> \<not>is_zero_double fl\<^sub>l \<and> is_finite_double fl\<^sub>l \<and> sign_double fl\<^sub>l = 0 \<and> \<not>is_nan_double fl\<^sub>u \<and> \<not>is_zero_double fl\<^sub>u \<and> is_finite_double fl\<^sub>u \<and> sign_double fl\<^sub>u = 0}"

  abbreviation "pfin_real_intv_assn \<equiv> pure pfin_real_intv_double_rel"

  lemma br_prod_comp: "(br \<alpha>\<^sub>1 I\<^sub>1 \<times>\<^sub>r br \<alpha>\<^sub>2 I\<^sub>2) O R = {((a, b), c) | a b c. I\<^sub>1 a \<and> I\<^sub>2 b \<and> ((\<alpha>\<^sub>1 a, \<alpha>\<^sub>2 b), c) \<in> R}"
    unfolding dfloat_rel_def 
    by (auto simp: in_br_conv intro!: relcompI)

  lemma pfin_real_intv_double_rel_alt: "pfin_real_intv_double_rel = (dfloat_rel \<times>\<^sub>r dfloat_rel) O pfin_real_intv_rel"
    unfolding dfloat_rel_def pfin_real_intv_double_rel_def pfin_real_intv_rel_def pfin_real_invar_def
    by(auto simp: br_prod_comp; transfer; auto)

  lemma pfin_real_intv_assn_alt: "pfin_real_intv_assn = hr_comp dfloat_intv_assn pfin_real_intv_rel"
    unfolding pfin_real_intv_double_rel_alt dfloat_intv_assn_alt
    by (simp add: hr_comp_pure)


  context
    notes [fcomp_norm_unfold] = nn_real_ub_assn_alt[symmetric] pfin_real_intv_assn_alt[symmetric]
      nn_real_lb_assn_alt[symmetric]
  begin
    lemmas op_mul_ub_nn_intv_hnr[sepref_fr_rules] = mop_mul_intv_rup_ll.refine[FCOMP op_mul_ub_nn_intv_refine]
    lemmas op_fma_ub_nn_intv_hnr[sepref_fr_rules] = mop_fma_intv_rup_ll.refine[FCOMP op_fma_ub_nn_intv_refine]

    lemmas op_mul_lb_nn_intv_hnr[sepref_fr_rules] = mop_mul_intv_rdn_ll.refine[FCOMP op_mul_lb_nn_intv_refine]
    lemmas op_fma_lb_nn_intv_hnr[sepref_fr_rules] = mop_fma_intv_rdn_ll.refine[FCOMP op_fma_lb_nn_intv_refine]
  end


end
