theory LLVM_Float_Types
imports "IEEE_FP_Extensions/IEEE_Float_Extend_Integer"
begin

subsection \<open>Double\<close>

typedef double = "UNIV::(11, 52) float set"
  morphisms float_of_double double_of_float  
  ..
  
setup_lifting type_definition_double

text \<open>Operations with default round-to-nearest\<close>

instantiation double :: "{uminus,plus,times,minus,zero,one,abs,ord,inverse,finite}" begin
  lift_definition uminus_double::"double \<Rightarrow> double" is uminus .
  lift_definition plus_double::"double \<Rightarrow> double \<Rightarrow> double" is plus .
  lift_definition times_double::"double \<Rightarrow> double \<Rightarrow> double" is times .
  lift_definition divide_double::"double \<Rightarrow> double \<Rightarrow> double" is divide .
  lift_definition inverse_double::"double \<Rightarrow> double" is inverse .
  lift_definition minus_double::"double \<Rightarrow> double \<Rightarrow> double" is minus .
  lift_definition zero_double::"double" is "0::float64" .
  lift_definition one_double::"double" is "1::float64" .
  lift_definition less_eq_double::"double \<Rightarrow> double \<Rightarrow> bool" is "(\<le>)" .
  lift_definition less_double::"double \<Rightarrow> double \<Rightarrow> bool" is "(<)" .
  instance proof
    have [simp]: "(UNIV :: double set) = double_of_float`(UNIV::float64 set)"
      apply auto
      by (metis double_of_float_cases range_eqI)
    show "finite (UNIV :: double set)" by (simp)
  qed
end

text \<open>Operations with explicit rounding mode\<close>

lift_definition dradd :: "roundmode \<Rightarrow> double \<Rightarrow> double \<Rightarrow> double" is fadd .
lift_definition drsub :: "roundmode \<Rightarrow> double \<Rightarrow> double \<Rightarrow> double" is fsub .
lift_definition drmul :: "roundmode \<Rightarrow> double \<Rightarrow> double \<Rightarrow> double" is fmul .
lift_definition drdiv :: "roundmode \<Rightarrow> double \<Rightarrow> double \<Rightarrow> double" is fdiv .
lift_definition drrem :: "roundmode \<Rightarrow> double \<Rightarrow> double \<Rightarrow> double" is frem .
lift_definition drsqrt :: "roundmode \<Rightarrow> double \<Rightarrow> double" is fsqrt .
lift_definition drfmadd :: "roundmode \<Rightarrow> double \<Rightarrow> double \<Rightarrow> double \<Rightarrow> double" is fmul_add .

definition "drem \<equiv> drrem To_nearest"
definition "dsqrt \<equiv> drsqrt To_nearest"

lift_definition eq_double::"double\<Rightarrow>double\<Rightarrow>bool" is float_eq .

lift_definition sqrt_double::"double\<Rightarrow>double" is float_sqrt .

lift_definition infinity_double::"double" is plus_infinity .

lift_definition is_normal_double::"double \<Rightarrow> bool" is IEEE.is_normal .
lift_definition is_zero_double::"double \<Rightarrow> bool" is IEEE.is_zero .
lift_definition is_finite_double::"double \<Rightarrow> bool" is IEEE.is_finite .
lift_definition is_nan_double::"double \<Rightarrow> bool" is IEEE.is_nan .


lift_definition double_of_word :: "64 word \<Rightarrow> double" is float_of_fp64 .
lift_definition word_of_double :: "double \<Rightarrow> 64 word" is fp64_of_float .

lemma double_of_word_inv[simp]:
  "double_of_word (word_of_double d) = d"
  "word_of_double (double_of_word w) = w"
  by (determ transfer, simp)+
  
lemma double_of_word_zero[simp]: "double_of_word 0 = 0"
  by transfer' simp
  
lemma word_of_double_zero[simp]: "word_of_double 0 = 0"  
  by transfer' simp
  

lift_definition real_of_double :: "double \<Rightarrow> real" is IEEE.valof .

lift_definition round_double :: "roundmode \<Rightarrow> real \<Rightarrow> double" is round .

abbreviation round_double_nearest where "round_double_nearest \<equiv> round_double To_nearest"
abbreviation round_double_zero where "round_double_zero \<equiv> round_double float_To_zero"
abbreviation round_double_up where "round_double_up \<equiv> round_double To_pinfinity"
abbreviation round_double_down where "round_double_down \<equiv> round_double To_ninfinity"

subsection \<open>Single\<close>
typedef single = "UNIV::float32 set" 
  morphisms float_of_single single_of_float  
  ..


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
    have [simp]: "(UNIV :: single set) = single_of_float`(UNIV::float32 set)"
      apply auto
      by (metis single_of_float_cases range_eqI)
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

lift_definition infinity_single::"single" is plus_infinity .

lift_definition is_normal_single::"single \<Rightarrow> bool" is IEEE.is_normal .
lift_definition is_zero_single::"single \<Rightarrow> bool" is IEEE.is_zero .
lift_definition is_finite_single::"single \<Rightarrow> bool" is IEEE.is_finite .
lift_definition is_nan_single::"single \<Rightarrow> bool" is IEEE.is_nan .


lift_definition single_of_word :: "32 word \<Rightarrow> single" is float_of_fp32 .
lift_definition word_of_single :: "single \<Rightarrow> 32 word" is fp32_of_float .

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

abbreviation round_single_nearest where "round_single_nearest \<equiv> round_single To_nearest"
abbreviation round_single_zero where "round_single_zero \<equiv> round_single float_To_zero"
abbreviation round_single_up where "round_single_up \<equiv> round_single To_pinfinity"
abbreviation round_single_down where "round_single_down \<equiv> round_single To_ninfinity"


subsection \<open>Extension Correctness Theorem\<close>

text \<open>Version for single and double: \<close>
theorem fext_int_single_double_correct:
  fixes i32 :: "integer"
  defines "i64 \<equiv> fext_int_32_64 i32"
  defines "f32 \<equiv> single_of_word (word_of_integer i32)"
  defines "f64 \<equiv> double_of_word (word_of_integer i64)"
  shows "correct_extension (float_of_single f32) (float_of_double f64)"
  using double_of_word.rep_eq f32_def f64_def fext_int_32_64_correct i64_def single_of_word.rep_eq 
  by presburger

end
