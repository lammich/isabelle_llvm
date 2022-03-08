(* Parts copied from: afp/IEEE_Floating_Point/Double.thy by Lei Yu, University of Cambridge *)
theory LLVM_Single
imports IEEE_Floating_Point.Conversion_IEEE_Float (*IEEE_Floating_Point.FP64*) LLVM_More_Word
begin

type_synonym fp32="32 word"
type_synonym "float32" = "(8,23) float"

lift_definition fp32_of_float :: "float32 \<Rightarrow> fp32" is
  "\<lambda>(s::1 word, e::8 word, f::23 word). word_cat s (word_cat e f::31 word)" .

lift_definition float_of_fp32 :: "fp32 \<Rightarrow> float32" is
  "\<lambda>x. apsnd word_split (word_split x::1 word * 31 word)" .

definition "rel_fp32 \<equiv> (\<lambda>x (y::fp32). x = float_of_fp32 y)"

definition eq_fp32::"float32 \<Rightarrow> float32 \<Rightarrow> bool" where [simp]: "eq_fp32 \<equiv> (=)"

lemma float_of_fp32_inverse[simp]: "fp32_of_float (float_of_fp32 a) = a"
  by (auto
      simp: fp32_of_float_def float_of_fp32_def Abs_float_inverse apsnd_def map_prod_def word_size
      dest!: word_cat_split_alt[rotated]
      split: prod.splits)

lemma float_of_fp32_inj_iff[simp]: "fp32_of_float r = fp32_of_float s \<longleftrightarrow> r = s"
  using Rep_float_inject
  by (force simp: fp32_of_float_def word_cat_inj word_size split: prod.splits)

lemma fp32_of_float_inverse[simp]: "float_of_fp32 (fp32_of_float a) = a"
  using float_of_fp32_inj_iff float_of_fp32_inverse by blast




  
typedef single = "UNIV::float32 set" ..


setup_lifting type_definition_single

text \<open>Operations with default round-to-nearest\<close>

instantiation single :: "{uminus,plus,times,minus,zero,one,abs,ord,inverse,finite}" begin
  lift_definition uminus_single::"single \<Rightarrow> single" is uminus .
  lift_definition plus_single::"single \<Rightarrow> single \<Rightarrow> single" is plus .
  lift_definition times_single::"single \<Rightarrow> single \<Rightarrow> single" is times .
  lift_definition divide_single::"single \<Rightarrow> single \<Rightarrow> single" is divide .
  lift_definition inverse_single::"single \<Rightarrow> single" is inverse .
  lift_definition minus_single::"single \<Rightarrow> single \<Rightarrow> single" is minus .
  lift_definition zero_single::"single" is "0::float32" .
  lift_definition one_single::"single" is "1::float32" .
  lift_definition less_eq_single::"single \<Rightarrow> single \<Rightarrow> bool" is "(\<le>)" .
  lift_definition less_single::"single \<Rightarrow> single \<Rightarrow> bool" is "(<)" .
  instance proof
    have [simp]: "(UNIV :: single set) = Abs_single`(UNIV::float32 set)"
      apply auto
      by (metis Abs_single_cases range_eqI)
    show "finite (UNIV :: single set)" by (simp)
  qed
end

text \<open>Operations with explicit rounding mode\<close>

lift_definition sradd :: "roundmode \<Rightarrow> single \<Rightarrow> single \<Rightarrow> single" is fadd .
lift_definition srsub :: "roundmode \<Rightarrow> single \<Rightarrow> single \<Rightarrow> single" is fsub .
lift_definition srmul :: "roundmode \<Rightarrow> single \<Rightarrow> single \<Rightarrow> single" is fmul .
lift_definition srdiv :: "roundmode \<Rightarrow> single \<Rightarrow> single \<Rightarrow> single" is fdiv .
lift_definition srrem :: "roundmode \<Rightarrow> single \<Rightarrow> single \<Rightarrow> single" is frem .
lift_definition srsqrt :: "roundmode \<Rightarrow> single \<Rightarrow> single" is fsqrt .
lift_definition srfmadd :: "roundmode \<Rightarrow> single \<Rightarrow> single \<Rightarrow> single \<Rightarrow> single" is fmul_add .

definition "srem \<equiv> srrem To_nearest"
definition "ssqrt \<equiv> srsqrt To_nearest"

lift_definition eq_single::"single\<Rightarrow>single\<Rightarrow>bool" is float_eq .

lift_definition sqrt_single::"single\<Rightarrow>single" is float_sqrt .

no_notation plus_infinity ("\<infinity>")

lift_definition infinity_single::"single" ("\<infinity>") is plus_infinity .

lift_definition is_normal::"single \<Rightarrow> bool" is IEEE.is_normal .
lift_definition is_zero::"single \<Rightarrow> bool" is IEEE.is_zero .
lift_definition is_finite::"single \<Rightarrow> bool" is IEEE.is_finite .
lift_definition is_nan::"single \<Rightarrow> bool" is IEEE.is_nan .


lift_definition single_of_word :: "32 word \<Rightarrow> single" is float_of_fp32 .
lift_definition word_of_single :: "single \<Rightarrow> 32 word" is fp32_of_float .

lemma float_of_fp32_zero[simp]: "float_of_fp32 0 = 0"
  unfolding zero_float_def float_of_fp32_def
  by (auto simp: Abs_float_inject)

lemma fp32_of_float_zero[simp]: "fp32_of_float 0 = 0"
  by (metis float_of_fp32_inverse float_of_fp32_zero)
  
  
lemma single_of_word_inv[simp]:
  "single_of_word (word_of_single d) = d"
  "word_of_single (single_of_word w) = w"
  by (determ transfer, simp)+
    
  
lemma single_of_word_zero[simp]: "single_of_word 0 = 0"
  by transfer' simp
  
lemma word_of_single_zero[simp]: "word_of_single 0 = 0"  
  by transfer' simp
  

lift_definition real_of_single :: "single \<Rightarrow> real" is IEEE.valof .

lift_definition round_single :: "roundmode \<Rightarrow> real \<Rightarrow> single" is round .

abbreviation round_nearest where "round_nearest \<equiv> round_single To_nearest"
abbreviation round_zero where "round_zero \<equiv> round_single float_To_zero"
abbreviation round_up where "round_up \<equiv> round_single To_pinfinity"
abbreviation round_down where "round_down \<equiv> round_single To_ninfinity"


  
  
end
