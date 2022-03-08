(* Parts copied from: afp/IEEE_Floating_Point/Double.thy by Lei Yu, University of Cambridge *)
theory LLVM_Double
imports IEEE_Floating_Point.Conversion_IEEE_Float IEEE_Floating_Point.FP64 LLVM_More_Word
begin


  
typedef double = "UNIV::(11, 52) float set" ..

(*lifting_update Float.float.lifting
lifting_forget Float.float.lifting

lifting_update IEEE.float.lifting
lifting_forget IEEE.float.lifting

lifting_update word.lifting
lifting_forget word.lifting
*)

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
    have [simp]: "(UNIV :: double set) = Abs_double`(UNIV::float64 set)"
      apply auto
      by (metis Abs_double_cases range_eqI)
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

no_notation plus_infinity ("\<infinity>")

lift_definition infinity_double::"double" ("\<infinity>") is plus_infinity .

lift_definition is_normal::"double \<Rightarrow> bool" is IEEE.is_normal .
lift_definition is_zero::"double \<Rightarrow> bool" is IEEE.is_zero .
lift_definition is_finite::"double \<Rightarrow> bool" is IEEE.is_finite .
lift_definition is_nan::"double \<Rightarrow> bool" is IEEE.is_nan .


lift_definition double_of_word :: "64 word \<Rightarrow> double" is float_of_fp64 .
lift_definition word_of_double :: "double \<Rightarrow> 64 word" is fp64_of_float .

lemma float_of_fp64_zero[simp]: "float_of_fp64 0 = 0"
  unfolding zero_float_def float_of_fp64_def
  by (auto simp: Abs_float_inject)

lemma fp64_of_float_zero[simp]: "fp64_of_float 0 = 0"
  by (metis float_of_fp64_inverse float_of_fp64_zero)
  
  
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

abbreviation round_nearest where "round_nearest \<equiv> round_double To_nearest"
abbreviation round_zero where "round_zero \<equiv> round_double float_To_zero"
abbreviation round_up where "round_up \<equiv> round_double To_pinfinity"
abbreviation round_down where "round_down \<equiv> round_double To_ninfinity"


  
  
end
