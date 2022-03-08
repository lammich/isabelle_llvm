theory FP_test_base
imports 
  "../../thys/lib/IEEE_Fp_Nextfloat"
  "HOL-Library.Code_Target_Nat"
  "HOL-Library.Code_Target_Int"
begin

  type_synonym float32 = "(8,23)float"
  type_synonym float64 = "(11,52)float"

  
  definition fp_gen :: "integer \<Rightarrow> integer \<Rightarrow> integer \<Rightarrow> (_,_) float" 
    where "fp_gen s f e \<equiv> Abs_float (of_nat (nat_of_integer s), of_int (int_of_integer e), of_nat (nat_of_integer f))"
  
  definition fp32 :: "_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> float32" where "fp32 \<equiv> fp_gen"
  definition fp64 :: "_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> float64" where "fp64 \<equiv> fp_gen"
  
  (* Signalling and exceptions are not supported by this framework, so we just map all NaNs to the same value *)
  definition sNaN32 :: float32 where "sNaN32 \<equiv> nan01"
  definition qNaN32 :: float32 where "qNaN32 \<equiv> nan01"
  definition sNaN64 :: float64 where "sNaN64 \<equiv> nan01"
  definition qNaN64 :: float64 where "qNaN64 \<equiv> nan01"
  
  
  definition "plus_zero32::float32 \<equiv> 0"
  definition "minus_zero32::float32 \<equiv> -0"
  definition "plus_inf32::float32 \<equiv> \<infinity>"
  definition "minus_inf32::float32 \<equiv> -\<infinity>"

  definition "plus_zero64::float64 \<equiv> 0"
  definition "minus_zero64::float64 \<equiv> -0"
  definition "plus_inf64::float64 \<equiv> \<infinity>"
  definition "minus_inf64::float64 \<equiv> -\<infinity>"
  
  definition check_fadd32 :: "_ \<Rightarrow> float32 \<Rightarrow> _" where "check_fadd32 \<equiv> check_fadd"
  definition check_fsub32 :: "_ \<Rightarrow> float32 \<Rightarrow> _" where "check_fsub32 \<equiv> check_fsub"
  definition check_fmul32 :: "_ \<Rightarrow> float32 \<Rightarrow> _" where "check_fmul32 \<equiv> check_fmul"
  definition check_fdiv32 :: "_ \<Rightarrow> float32 \<Rightarrow> _" where "check_fdiv32 \<equiv> check_fdiv"
  definition check_fmul_add32 :: "_ \<Rightarrow> float32 \<Rightarrow> _" where "check_fmul_add32 \<equiv> check_fmul_add"
  
  definition check_fadd64 :: "_ \<Rightarrow> float64 \<Rightarrow> _" where "check_fadd64 \<equiv> check_fadd"
  definition check_fsub64 :: "_ \<Rightarrow> float64 \<Rightarrow> _" where "check_fsub64 \<equiv> check_fsub"
  definition check_fmul64 :: "_ \<Rightarrow> float64 \<Rightarrow> _" where "check_fmul64 \<equiv> check_fmul"
  definition check_fdiv64 :: "_ \<Rightarrow> float64 \<Rightarrow> _" where "check_fdiv64 \<equiv> check_fdiv"
  definition check_fmul_add64 :: "_ \<Rightarrow> float64 \<Rightarrow> _" where "check_fmul_add64 \<equiv> check_fmul_add"
  
    
  export_code 
    fp32 fp64 
    sNaN32 qNaN32 plus_zero32 minus_zero32 plus_inf32 minus_inf32
    sNaN64 qNaN64 plus_zero64 minus_zero64 plus_inf64 minus_inf64
    
    check_fadd32 check_fsub32 check_fmul32 check_fdiv32 check_fmul_add32
    check_fadd64 check_fsub64 check_fmul64 check_fdiv64 check_fmul_add64
    To_pinfinity To_ninfinity To_nearest float_To_zero
    in SML module_name FP_test_base
    file "FP_test_base.sml"
  
  
  declare [[code abort: closest]]
  
  term round

  definition [code del]: "closest_tn y \<equiv> closest (valof) (\<lambda>a. even (fraction a)) {a. is_finite a} y"
  definition [code del]: "closest_tz y \<equiv> closest (valof) (\<lambda>a. True) {a. is_finite a \<and> \<bar>valof a\<bar> \<le> \<bar>y\<bar>} y"
  definition [code del]: "closest_tpi y \<equiv> closest (valof) (\<lambda>a. True) {a. is_finite a \<and> valof a \<ge> y} y"
  definition [code del]: "closest_tni y \<equiv> closest (valof) (\<lambda>a. True) {a. is_finite a \<and> valof a \<le> y} y"
  
  lemmas [code del] = some_nan_def
  
  
  fun roundx :: "roundmode \<Rightarrow> real \<Rightarrow> ('e ,'f) float"
  where
    "roundx To_nearest y =
     (if y \<le> - threshold TYPE(('e ,'f) float) then minus_infinity
      else if y \<ge> threshold TYPE(('e ,'f) float) then plus_infinity
      else closest_tn y)"
  | "roundx float_To_zero y =
     (if y < - largest TYPE(('e ,'f) float) then bottomfloat
      else if y > largest TYPE(('e ,'f) float) then topfloat
      else closest_tz y)"
  | "roundx To_pinfinity y =
     (if y < - largest TYPE(('e ,'f) float) then bottomfloat
      else if y > largest TYPE(('e ,'f) float) then plus_infinity
      else closest_tpi y)"
  | "roundx To_ninfinity y =
     (if y < - largest TYPE(('e ,'f) float) then minus_infinity
      else if y > largest TYPE(('e ,'f) float) then topfloat
      else closest_tni y)"
    
  lemma [code]: "round m y = roundx m y"  
    apply (cases m)
    by (auto simp: closest_tn_def closest_tz_def closest_tpi_def closest_tni_def)
  
  
  value "valof (fp32 1 0x48FDB5 (-78+127))"  
  value "valof (fp32 0 0x4381CE (-73+127))"  
    
  value "check_fmul32 To_pinfinity (fp32 1 0x48FDB5 (-78+127)) (fp32 0 0x4381CE (-73+127)) (fp32 1 0x000000 0)"
    
  
  
  value [nbe] "fadd To_nearest (fp32 0 0 127) (fp32 1 0x7FFFFF 254)"
  
  (*
  - 340282346638528859811704183484516925439
  
  - 340282346638528859811704183484516925440
  
  *)    
    
    
  find_consts "(_,_) float \<Rightarrow> _ word"
  
  ML_val \<open>
    @{code "fp32"} 0 0xF4 (~4)
  
  \<close>
  
  
  

end
