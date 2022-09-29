section \<open>Shallow Embedding of LLVM Semantics\<close>
theory LLVM_Shallow
imports Main  
  "Simple_Memory"
begin


  subsection \<open>Shallow Embedding of Values\<close>  

  text \<open>We use a type class to characterize types that can be injected into the value type.
    We will instantiate this type class to obtain injections from types of shape 
    \<open>T = T\<times>T | _ word | _ ptr\<close>
  
    Although, this type class can be instantiated by other types, those will not be accepted 
    by the code generator.
    
    We also define a class \<open>llvm_repv\<close>, which additionally contains \<open>unit\<close>. 
    This is required for void functions, and if-the-else statements that produce no result.
    
    Again, while this class might be instantiated for other types, those will be rejected
    by the code generator.
  \<close>
  
  class llvm_repv  
    
  class llvm_rep = llvm_repv +
    fixes to_val :: "'a \<Rightarrow> llvm_val"
      and from_val :: "llvm_val \<Rightarrow> 'a"
      and struct_of :: "'a itself \<Rightarrow> llvm_struct"
      and init :: 'a
    assumes from_to_id[simp]: "from_val o to_val = id"
    assumes to_from_id[simp]: "llvm_struct_of_val v = struct_of TYPE('a) \<Longrightarrow> to_val (from_val v) = v"
    assumes struct_of_matches[simp]: "llvm_struct_of_val (to_val x) = (struct_of TYPE('a))"
    assumes init_zero: "to_val init = llvm_zero_initializer (struct_of TYPE('a))"
    
  begin
  
    lemma from_to_id'[simp]: "from_val (to_val x) = x" 
      using pointfree_idE[OF from_to_id] .
  
    lemma "to_val x = to_val y \<longleftrightarrow> x=y"  
      by (metis from_to_id')
      
  end
  
  text \<open>We use a phantom type to attach the type of the pointed to value to a pointer.
    Note that we define pointers for any datatype. While it will always point to 
    representable datatypes, this enables easy \<open>llvm_rep\<close> instantiations for recursive structures
    via pointers, such as linked list cells. 
  \<close>
  
  datatype 'a ptr = PTR (the_raw_ptr: llvm_ptr)
  definition null :: "'a ptr" where "null = PTR PTR_NULL"
  

  text \<open>We instantiate the type classes for the supported types, 
    i.e., unit, word, ptr, and prod.\<close>
  
  instance unit :: llvm_repv by standard
  
  instantiation word :: (len) llvm_rep begin
    definition "to_val w \<equiv> LL_INT (lconst (len_of TYPE('a)) (uint w))"
    definition "from_val v \<equiv> word_of_int (lint_to_uint (llvm_val.the_int v))"
    definition [simp]: "struct_of_word (_::'a word itself) \<equiv> VS_INT (len_of TYPE('a))"
    definition [simp]: "init_word \<equiv> 0::'a word"
    
    
    lemma int_inv_aux: "width i = LENGTH('a) \<Longrightarrow> lconst LENGTH('a) (uint (word_of_int (lint_to_uint i) :: 'a word)) = i"
      by (metis uint_const uint_eq uint_lower_bound uint_upper_bound width_lconst word_of_int_inverse word_ubin.norm_Rep)
    
    instance
      apply standard
      apply (rule ext)
      apply (simp_all add: from_val_word_def to_val_word_def)
      subgoal for v apply (cases v) using int_inv_aux by auto
      done
      
  end

  instantiation single :: llvm_rep begin
    definition "to_val w \<equiv> LL_SINGLE w"
    definition "from_val v \<equiv> llvm_val.the_single v"
    definition [simp]: "struct_of_single (_::single itself) \<equiv> VS_SINGLE"
    definition [simp]: "init_single \<equiv> 0::single"

    instance
      apply standard
      apply (simp_all add: fun_eq_iff from_val_single_def to_val_single_def)
      subgoal for v by (cases v; simp)
      done
      
  end
  
  instantiation double :: llvm_rep begin
    definition "to_val w \<equiv> LL_DOUBLE w"
    definition "from_val v \<equiv> llvm_val.the_double v"
    definition [simp]: "struct_of_double (_::double itself) \<equiv> VS_DOUBLE"
    definition [simp]: "init_double \<equiv> 0::double"

    instance
      apply standard
      apply (simp_all add: fun_eq_iff from_val_double_def to_val_double_def)
      subgoal for v by (cases v; simp)
      done
      
  end
    
  instantiation ptr :: (type) llvm_rep begin
    definition "to_val_ptr \<equiv> LL_PTR o ptr.the_raw_ptr"
    definition "from_val_ptr v \<equiv> PTR (llvm_val.the_ptr v)"
    definition [simp]: "struct_of_ptr (_::'a ptr itself) \<equiv> VS_PTR"
    definition [simp]: "init_ptr::'a ptr \<equiv> null"
  
    instance
      apply standard
      apply (rule ext)
      apply (simp_all add: from_val_ptr_def to_val_ptr_def null_def)
      subgoal for v apply (cases v) by auto
      done
      
  end
  
  instantiation prod :: (llvm_rep, llvm_rep) llvm_rep begin
    definition "to_val_prod \<equiv> \<lambda>(a,b). LL_STRUCT [to_val a, to_val b]"
    definition "from_val_prod p \<equiv> case llvm_val.the_fields p of [a,b] \<Rightarrow> (from_val a, from_val b)"
    definition [simp]: "struct_of_prod (_::('a\<times>'b) itself) \<equiv> VS_STRUCT [struct_of TYPE('a), struct_of TYPE('b)]"
    definition [simp]: "init_prod ::'a\<times>'b \<equiv> (init,init)"
    
    instance
      apply standard
      apply (rule ext)
      apply (auto simp: from_val_prod_def to_val_prod_def init_zero)
      subgoal for v by (cases v) auto
      done
      
  end

  lemma to_val_prod_conv[simp]: "to_val (a,b) = LL_STRUCT [to_val a, to_val b]"
    unfolding to_val_prod_def by auto
  
  context
    includes monad_syntax_M
  begin
    
    
  text \<open>Checked conversion from value\<close>  
  definition checked_from_val :: "llvm_val \<Rightarrow> 'a::llvm_rep llM" where
    "checked_from_val v \<equiv> doM {
      assert (llvm_struct_of_val v = struct_of TYPE('a));
      return (from_val v)
    }" 

      
  subsection \<open>Instructions\<close>  
  
  text \<open>The instructions are arranged in the order as they are described in the 
    LLVM Language Reference Manual \<^url>\<open>https://llvm.org/docs/LangRef.html\<close>.\<close>
    
  
  subsubsection \<open>Binary Integer Operations\<close>  
  text \<open>We define a generic lifter for binary arithmetic operations.
    It is parameterized by an error condition.
  \<close> (* TODO: Use precondition instead of negated precondition! *)
  
  definition op_lift_arith2 :: "_ \<Rightarrow> _ \<Rightarrow> 'a::len word \<Rightarrow> 'a word \<Rightarrow> 'a word llM"
    where "op_lift_arith2 ovf f a b \<equiv> doM {
    let a = word_to_lint a;
    let b = word_to_lint b;
    assert (\<not>ovf a b);
    return (lint_to_word (f a b))
  }"
        
  definition "op_lift_arith2' \<equiv> op_lift_arith2 (\<lambda>_ _. False)"

  definition udivrem_is_undef :: "lint \<Rightarrow> lint \<Rightarrow> bool" 
    where "udivrem_is_undef a b \<equiv> lint_to_uint b=0"
  definition sdivrem_is_undef :: "lint \<Rightarrow> lint \<Rightarrow> bool" 
    where "sdivrem_is_undef a b \<equiv> lint_to_sint b=0 \<or> sdivrem_ovf a b"
  
  definition "ll_add \<equiv> op_lift_arith2' (+)"
  definition "ll_sub \<equiv> op_lift_arith2' (-)"
  definition "ll_mul \<equiv> op_lift_arith2' (*)"
  definition "ll_udiv \<equiv> op_lift_arith2 udivrem_is_undef (div)"
  definition "ll_urem \<equiv> op_lift_arith2 udivrem_is_undef (mod)"
  definition "ll_sdiv \<equiv> op_lift_arith2 sdivrem_is_undef (sdiv\<^sub>l\<^sub>i\<^sub>n\<^sub>t)"
  definition "ll_srem \<equiv> op_lift_arith2 sdivrem_is_undef (smod\<^sub>l\<^sub>i\<^sub>n\<^sub>t)"

  subsubsection \<open>Binary Floating Point Operations\<close>  
  definition ndet_nan_double :: "double llM" where "ndet_nan_double \<equiv> Mspec is_nan_double"
  definition ndet_nan_single :: "single llM" where "ndet_nan_single \<equiv> Mspec is_nan_single"
  
  definition nanize_double where "nanize_double x \<equiv> if is_nan_double x then ndet_nan_double else return x"
  lemma nanize_double_simps[simp]: 
    "\<not>is_nan_double x \<Longrightarrow> nanize_double x = Mreturn x"
    "is_nan_double x \<Longrightarrow> nanize_double x = ndet_nan_double"
    unfolding nanize_double_def
    by auto

  definition nanize_single where "nanize_single x \<equiv> if is_nan_single x then ndet_nan_single else return x"
  lemma nanize_single_simps[simp]: 
    "\<not>is_nan_single x \<Longrightarrow> nanize_single x = Mreturn x"
    "is_nan_single x \<Longrightarrow> nanize_single x = ndet_nan_single"
    unfolding nanize_single_def
    by auto
      
  text \<open>We define a generic lifter for binary arithmetic operations.
    It is parameterized by an error condition.
  \<close> (* TODO: Use precondition instead of negated precondition! *)
  
  definition op_lift_farith1_d :: "_ \<Rightarrow> double \<Rightarrow> double llM"
    where "op_lift_farith1_d f a \<equiv> doM {
    nanize_double (f a)
  }"
  
  definition op_lift_farith2_d :: "_ \<Rightarrow> double \<Rightarrow> double \<Rightarrow> double llM"
    where "op_lift_farith2_d f a b \<equiv> doM {
    nanize_double (f a b)
  }"

  definition op_lift_farith3_d :: "_ \<Rightarrow> double \<Rightarrow> double \<Rightarrow> double \<Rightarrow> double llM"
    where "op_lift_farith3_d f a b c \<equiv> doM {
    nanize_double (f a b c)
  }"
  
  definition op_lift_farith1_f :: "_ \<Rightarrow> single \<Rightarrow> single llM"
    where "op_lift_farith1_f f a \<equiv> doM {
    nanize_single (f a)
  }"
  
  definition op_lift_farith2_f :: "_ \<Rightarrow> single \<Rightarrow> single \<Rightarrow> single llM"
    where "op_lift_farith2_f f a b \<equiv> doM {
    nanize_single (f a b)
  }"

  definition op_lift_farith3_f :: "_ \<Rightarrow> single \<Rightarrow> single \<Rightarrow> single \<Rightarrow> single llM"
    where "op_lift_farith3_f f a b c \<equiv> doM {
    nanize_single (f a b c)
  }"
          
  definition "ll_fadd_d \<equiv> op_lift_farith2_d (+)"
  definition "ll_fsub_d \<equiv> op_lift_farith2_d (-)"
  definition "ll_fmul_d \<equiv> op_lift_farith2_d (*)"
  definition "ll_fdiv_d \<equiv> op_lift_farith2_d (/)"
  definition "ll_frem_d \<equiv> op_lift_farith2_d (drem)"     
  definition "ll_sqrt_f64 \<equiv> op_lift_farith1_d (dsqrt)"

  definition "ll_fadd_f \<equiv> op_lift_farith2_f (+)"
  definition "ll_fsub_f \<equiv> op_lift_farith2_f (-)"
  definition "ll_fmul_f \<equiv> op_lift_farith2_f (*)"
  definition "ll_fdiv_f \<equiv> op_lift_farith2_f (/)"
  definition "ll_frem_f \<equiv> op_lift_farith2_f (srem)"     
  definition "ll_sqrt_f32 \<equiv> op_lift_farith1_f (ssqrt)"
    
  subsubsection \<open>Compare Operations\<close>
  definition op_lift_cmp :: "_ \<Rightarrow> 'a::len word \<Rightarrow> 'a word \<Rightarrow> 1 word llM"
    where "op_lift_cmp f a b \<equiv> doM {
    let a = word_to_lint a;
    let b = word_to_lint b;
    return (lint_to_word (bool_to_lint (f a b)))
  }"
    
  definition "ll_icmp_eq \<equiv>  op_lift_cmp (=)"
  definition "ll_icmp_ne \<equiv>  op_lift_cmp (\<noteq>)"
  definition "ll_icmp_sle \<equiv> op_lift_cmp (\<le>\<^sub>s)"
  definition "ll_icmp_slt \<equiv> op_lift_cmp (<\<^sub>s)"
  definition "ll_icmp_ule \<equiv> op_lift_cmp (\<le>)"
  definition "ll_icmp_ult \<equiv> op_lift_cmp (<)"

  subsubsection \<open>Floating Point Compare Operations\<close>
  definition op_lift_fcmp_d :: "bool \<Rightarrow> _ \<Rightarrow> double \<Rightarrow> double \<Rightarrow> 1 word llM"
    where "op_lift_fcmp_d ordered f a b \<equiv> doM {
      if ordered then
        return (lint_to_word (bool_to_lint (\<not>is_nan_double a \<and> \<not>is_nan_double b \<and> f a b)))
      else
        return (lint_to_word (bool_to_lint (is_nan_double a \<or> is_nan_double b \<or> f a b)))
    
  }"
  definition op_lift_fcmp_f :: "bool \<Rightarrow> _ \<Rightarrow> single \<Rightarrow> single \<Rightarrow> 1 word llM"
    where "op_lift_fcmp_f ordered f a b \<equiv> doM {
      if ordered then
        return (lint_to_word (bool_to_lint (\<not>is_nan_single a \<and> \<not>is_nan_single b \<and> f a b)))
      else
        return (lint_to_word (bool_to_lint (is_nan_single a \<or> is_nan_single b \<or> f a b)))
    
  }"
    
  (* from the LLVM docs: (we skip true and false here, as they are not required for our purpose )
    oeq: yields true if both operands are not a QNAN and op1 is equal to op2.
    ogt: yields true if both operands are not a QNAN and op1 is greater than op2.
    oge: yields true if both operands are not a QNAN and op1 is greater than or equal to op2.
    olt: yields true if both operands are not a QNAN and op1 is less than op2.
    ole: yields true if both operands are not a QNAN and op1 is less than or equal to op2.
    one: yields true if both operands are not a QNAN and op1 is not equal to op2.
    ord: yields true if both operands are not a QNAN.
    ueq: yields true if either operand is a QNAN or op1 is equal to op2.
    ugt: yields true if either operand is a QNAN or op1 is greater than op2.
    uge: yields true if either operand is a QNAN or op1 is greater than or equal to op2.
    ult: yields true if either operand is a QNAN or op1 is less than op2.
    ule: yields true if either operand is a QNAN or op1 is less than or equal to op2.
    une: yields true if either operand is a QNAN or op1 is not equal to op2.
    uno: yields true if either operand is a QNAN.
  *)
  
  definition "ll_fcmp_oeq_d \<equiv> op_lift_fcmp_d True (eq_double)"
  definition "ll_fcmp_ogt_d \<equiv> op_lift_fcmp_d True (>)"
  definition "ll_fcmp_oge_d \<equiv> op_lift_fcmp_d True (\<ge>)"
  definition "ll_fcmp_olt_d \<equiv> op_lift_fcmp_d True (<)"
  definition "ll_fcmp_ole_d \<equiv> op_lift_fcmp_d True (\<le>)"
  definition "ll_fcmp_one_d \<equiv> op_lift_fcmp_d True (Not oo eq_double)"
  definition "ll_fcmp_ord_d \<equiv> op_lift_fcmp_d True (\<lambda>_ _. True)"

  definition "ll_fcmp_ueq_d \<equiv> op_lift_fcmp_d False (eq_double)"
  definition "ll_fcmp_ugt_d \<equiv> op_lift_fcmp_d False (>)"
  definition "ll_fcmp_uge_d \<equiv> op_lift_fcmp_d False (\<ge>)"
  definition "ll_fcmp_ult_d \<equiv> op_lift_fcmp_d False (<)"
  definition "ll_fcmp_ule_d \<equiv> op_lift_fcmp_d False (\<le>)"
  definition "ll_fcmp_une_d \<equiv> op_lift_fcmp_d False (Not oo eq_double)"
  definition "ll_fcmp_uno_d \<equiv> op_lift_fcmp_d False (\<lambda>_ _. False)"
  
  definition "ll_fcmp_oeq_f \<equiv> op_lift_fcmp_f True (eq_single)"
  definition "ll_fcmp_ogt_f \<equiv> op_lift_fcmp_f True (>)"
  definition "ll_fcmp_oge_f \<equiv> op_lift_fcmp_f True (\<ge>)"
  definition "ll_fcmp_olt_f \<equiv> op_lift_fcmp_f True (<)"
  definition "ll_fcmp_ole_f \<equiv> op_lift_fcmp_f True (\<le>)"
  definition "ll_fcmp_one_f \<equiv> op_lift_fcmp_f True (Not oo eq_single)"
  definition "ll_fcmp_ord_f \<equiv> op_lift_fcmp_f True (\<lambda>_ _. True)"

  definition "ll_fcmp_ueq_f \<equiv> op_lift_fcmp_f False (eq_single)"
  definition "ll_fcmp_ugt_f \<equiv> op_lift_fcmp_f False (>)"
  definition "ll_fcmp_uge_f \<equiv> op_lift_fcmp_f False (\<ge>)"
  definition "ll_fcmp_ult_f \<equiv> op_lift_fcmp_f False (<)"
  definition "ll_fcmp_ule_f \<equiv> op_lift_fcmp_f False (\<le>)"
  definition "ll_fcmp_une_f \<equiv> op_lift_fcmp_f False (Not oo eq_single)"
  definition "ll_fcmp_uno_f \<equiv> op_lift_fcmp_f False (\<lambda>_ _. False)"
  
  subsubsection "AVX512f: sd-operations with rounding mode"
  text \<open>The code generator creates the insertion/extraction into vector type.\<close>
  (* TODO: Add vector type to memory model! *)

  (*Rounding mode constants, from LLVM's smmintrin.h:
  
    #define _MM_FROUND_TO_NEAREST_INT    0x00
    #define _MM_FROUND_TO_NEG_INF        0x01
    #define _MM_FROUND_TO_POS_INF        0x02
    #define _MM_FROUND_TO_ZERO           0x03
    #define _MM_FROUND_CUR_DIRECTION     0x04
    
    #define _MM_FROUND_RAISE_EXC         0x00
    #define _MM_FROUND_NO_EXC            0x08
  *) 
  
  abbreviation (input) "AVX512_MM_FROUND_TO_NEAREST_INT \<equiv> 0x00 :: nat"
  abbreviation (input) "AVX512_MM_FROUND_TO_NEG_INF     \<equiv> 0x01 :: nat"
  abbreviation (input) "AVX512_MM_FROUND_TO_POS_INF     \<equiv> 0x02 :: nat"
  abbreviation (input) "AVX512_MM_FROUND_TO_ZERO        \<equiv> 0x03 :: nat"
  abbreviation (input) "AVX512_MM_FROUND_CUR_DIRECTION  \<equiv> 0x04 :: nat"   
  
  abbreviation (input) "AVX512_MM_FROUND_RAISE_EXC      \<equiv> 0x00 :: nat"
  abbreviation (input) "AVX512_MM_FROUND_NO_EXC         \<equiv> 0x08 :: nat"
  
  (* We support the following combinations (from Intel's Intrinsics guide, without CUR_DIRECTION)
    (_MM_FROUND_TO_NEAREST_INT |_MM_FROUND_NO_EXC) // round to nearest, and suppress exceptions
    (_MM_FROUND_TO_NEG_INF |_MM_FROUND_NO_EXC)     // round down, and suppress exceptions
    (_MM_FROUND_TO_POS_INF |_MM_FROUND_NO_EXC)     // round up, and suppress exceptions
    (_MM_FROUND_TO_ZERO |_MM_FROUND_NO_EXC)        // truncate, and suppress exceptions
    
  *)

  abbreviation (input) "AVX512_FROUND_TO_NEAREST_NO_EXC \<equiv> 0x08 :: nat"
  abbreviation (input) "AVX512_FROUND_TO_NEG_INF_NO_EXC \<equiv> 0x09 :: nat"
  abbreviation (input) "AVX512_FROUND_TO_POS_INF_NO_EXC \<equiv> 0x0A :: nat"
  abbreviation (input) "AVX512_FROUND_TO_ZERO_NO_EXC \<equiv> 0x0B :: nat"

  (* Alternative definitions, showing consistency! *)  
  lemma "AVX512_FROUND_TO_NEAREST_NO_EXC = AVX512_MM_FROUND_TO_NEAREST_INT OR AVX512_MM_FROUND_NO_EXC" by eval
  lemma "AVX512_FROUND_TO_NEG_INF_NO_EXC = AVX512_MM_FROUND_TO_NEG_INF OR AVX512_MM_FROUND_NO_EXC" by eval
  lemma "AVX512_FROUND_TO_POS_INF_NO_EXC = AVX512_MM_FROUND_TO_POS_INF OR AVX512_MM_FROUND_NO_EXC" by eval
  lemma "AVX512_FROUND_TO_ZERO_NO_EXC = AVX512_MM_FROUND_TO_ZERO OR AVX512_MM_FROUND_NO_EXC" by eval

  definition xlate_rounding_mode :: "nat \<Rightarrow> roundmode llM" where "xlate_rounding_mode rm \<equiv> 
         if rm = AVX512_FROUND_TO_NEAREST_NO_EXC then return To_nearest
    else if rm = AVX512_FROUND_TO_NEG_INF_NO_EXC then return To_ninfinity
    else if rm = AVX512_FROUND_TO_POS_INF_NO_EXC then return To_pinfinity
    else if rm = AVX512_FROUND_TO_ZERO_NO_EXC then return float_To_zero
    else fail"
    
  lemma xlate_rounding_mode_simps:  
    "xlate_rounding_mode AVX512_FROUND_TO_NEAREST_NO_EXC = (return To_nearest)"
    "xlate_rounding_mode AVX512_FROUND_TO_NEG_INF_NO_EXC = (return To_ninfinity)"
    "xlate_rounding_mode AVX512_FROUND_TO_POS_INF_NO_EXC = (return To_pinfinity)"
    "xlate_rounding_mode AVX512_FROUND_TO_ZERO_NO_EXC = (return float_To_zero)"
    unfolding xlate_rounding_mode_def by simp_all
    
  definition op_lift_farith1_rm_d :: "(roundmode \<Rightarrow> double \<Rightarrow> double) \<Rightarrow> nat \<Rightarrow> double \<Rightarrow> double llM" 
    where "op_lift_farith1_rm_d f rm a \<equiv> doM { rm \<leftarrow> xlate_rounding_mode rm; nanize_double (f rm a) }"
  definition op_lift_farith2_rm_d :: "(roundmode \<Rightarrow> double \<Rightarrow> double \<Rightarrow> double) \<Rightarrow> nat \<Rightarrow> double \<Rightarrow> double \<Rightarrow> double llM" 
    where "op_lift_farith2_rm_d f rm a b \<equiv> doM { rm \<leftarrow> xlate_rounding_mode rm; nanize_double (f rm a b) }"
  definition op_lift_farith3_rm_d :: "(roundmode \<Rightarrow> double \<Rightarrow> double \<Rightarrow> double \<Rightarrow> double) \<Rightarrow> nat \<Rightarrow> double \<Rightarrow> double \<Rightarrow> double \<Rightarrow> double llM" 
    where "op_lift_farith3_rm_d f rm a b c \<equiv> doM { rm \<leftarrow> xlate_rounding_mode rm; nanize_double (f rm a b c) }"

  definition op_lift_farith1_rm_f :: "(roundmode \<Rightarrow> single \<Rightarrow> single) \<Rightarrow> nat \<Rightarrow> single \<Rightarrow> single llM" 
    where "op_lift_farith1_rm_f f rm a \<equiv> doM { rm \<leftarrow> xlate_rounding_mode rm; nanize_single (f rm a) }"
  definition op_lift_farith2_rm_f :: "(roundmode \<Rightarrow> single \<Rightarrow> single \<Rightarrow> single) \<Rightarrow> nat \<Rightarrow> single \<Rightarrow> single \<Rightarrow> single llM" 
    where "op_lift_farith2_rm_f f rm a b \<equiv> doM { rm \<leftarrow> xlate_rounding_mode rm; nanize_single (f rm a b) }"
  definition op_lift_farith3_rm_f :: "(roundmode \<Rightarrow> single \<Rightarrow> single \<Rightarrow> single \<Rightarrow> single) \<Rightarrow> nat \<Rightarrow> single \<Rightarrow> single \<Rightarrow> single \<Rightarrow> single llM" 
    where "op_lift_farith3_rm_f f rm a b c \<equiv> doM { rm \<leftarrow> xlate_rounding_mode rm; nanize_single (f rm a b c) }"
    
        
  definition "ll_x86_avx512_add_sd_round \<equiv> op_lift_farith2_rm_d dradd"
  definition "ll_x86_avx512_sub_sd_round \<equiv> op_lift_farith2_rm_d drsub"
  definition "ll_x86_avx512_mul_sd_round \<equiv> op_lift_farith2_rm_d drmul"
  definition "ll_x86_avx512_div_sd_round \<equiv> op_lift_farith2_rm_d drdiv"
  definition "ll_x86_avx512_sqrt_sd \<equiv> op_lift_farith1_rm_d drsqrt"
  definition "ll_x86_avx512_vfmadd_f64 \<equiv> op_lift_farith3_rm_d drfmadd"

  definition "ll_x86_avx512_add_ss_round \<equiv> op_lift_farith2_rm_f sradd"
  definition "ll_x86_avx512_sub_ss_round \<equiv> op_lift_farith2_rm_f srsub"
  definition "ll_x86_avx512_mul_ss_round \<equiv> op_lift_farith2_rm_f srmul"
  definition "ll_x86_avx512_div_ss_round \<equiv> op_lift_farith2_rm_f srdiv"
  definition "ll_x86_avx512_sqrt_ss \<equiv> op_lift_farith1_rm_f srsqrt"
  definition "ll_x86_avx512_vfmadd_f32 \<equiv> op_lift_farith3_rm_f srfmadd"
  
  subsubsection \<open>Bitwise Binary Operations\<close>                                      
  definition "shift_ovf a n \<equiv> nat (lint_to_uint n) \<ge> width a"
  definition "bitSHL' a n \<equiv> bitSHL a (nat (lint_to_uint n))"
  definition "bitASHR' a n \<equiv> bitASHR a (nat (lint_to_uint n))"
  definition "bitLSHR' a n \<equiv> bitLSHR a (nat (lint_to_uint n))"
  
  definition "ll_shl \<equiv> op_lift_arith2 shift_ovf bitSHL'"  
  definition "ll_lshr \<equiv> op_lift_arith2 shift_ovf bitLSHR'"  
  definition "ll_ashr \<equiv> op_lift_arith2 shift_ovf bitASHR'"
  
  definition "ll_and \<equiv> op_lift_arith2' (lliAND)"
  definition "ll_or \<equiv> op_lift_arith2' (lliOR)"
  definition "ll_xor \<equiv> op_lift_arith2' (lliXOR)"
    

  subsubsection \<open>Aggregate Operations\<close>
  text \<open>In LLVM, there is an \<open>extractvalue\<close> and \<open>insertvalue\<close> operation.
    In our shallow embedding, these get instantiated for \<open>fst\<close> and \<open>snd\<close>.\<close>
    
    
  definition ll_extract_value :: "'t::llvm_rep \<Rightarrow> nat \<Rightarrow> 't\<^sub>1::llvm_rep llM"
    where "ll_extract_value p i \<equiv> doM {
      r \<leftarrow> llvm_extract_value (to_val p) i;
      checked_from_val r
    }"  
    
  definition ll_insert_value :: "'t::llvm_rep \<Rightarrow> 't\<^sub>1::llvm_rep \<Rightarrow> nat \<Rightarrow> 't::llvm_rep llM"
    where "ll_insert_value p x i \<equiv> doM {
      r \<leftarrow> llvm_insert_value (to_val p) (to_val x) i;
      checked_from_val r
    }"
    
  definition ll_dest_union :: "'t::llvm_rep \<Rightarrow> nat \<Rightarrow> 't\<^sub>1::llvm_rep llM" 
    where "ll_dest_union p i \<equiv> doM {
      r \<leftarrow> llvm_dest_union (to_val p) i;
      checked_from_val r
    }" 

  definition ll_make_union :: "'t::llvm_rep itself \<Rightarrow> 't\<^sub>1::llvm_rep \<Rightarrow> nat \<Rightarrow> 't::llvm_rep llM"
    where "ll_make_union TYPE('t) x i \<equiv> doM {
      r \<leftarrow> llvm_make_union (struct_of TYPE('t)) (to_val x) i;
      checked_from_val r
    }"
        
    
  subsubsection \<open>Memory Access and Addressing Operations\<close>
    
  definition ll_load :: "'a::llvm_rep ptr \<Rightarrow> 'a llM" where
    "ll_load p \<equiv> doM {
      r \<leftarrow> llvm_load (to_val p);
      checked_from_val r
    }"
    
  definition ll_store :: "'a::llvm_rep \<Rightarrow> 'a ptr \<Rightarrow> unit llM" where
    "ll_store v p \<equiv> doM {
      llvm_store (to_val v) (to_val p)
    }"

  text \<open>Note that LLVM itself does not have malloc and free instructions.
    However, these are primitive instructions in our abstract memory model, 
    such that we have to model them in our semantics.
    
    The code generator will map them to the C standard library 
    functions \<open>calloc\<close> and \<open>free\<close>.
  \<close>
    
  definition ll_malloc :: "'a::llvm_rep itself \<Rightarrow> _::len word \<Rightarrow> 'a ptr llM" where
    "ll_malloc TYPE('a) n = doM {
      assert (unat n > 0); \<comment> \<open>Disallow empty malloc\<close>
      r \<leftarrow> llvm_alloc (struct_of TYPE ('a)) (to_val n);
      return (from_val r)
    }"
        
  definition ll_free :: "'a::llvm_rep ptr \<Rightarrow> unit llM" 
    where "ll_free p \<equiv> doM {
      llvm_free (to_val p)
    }"


  text \<open>As for the aggregate operations, the \<open>getelementptr\<close> instruction is instantiated 
    for pointer and structure indexing. \<close>
      
  definition ll_ofs_ptr :: "'a::llvm_rep ptr \<Rightarrow> _::len word \<Rightarrow> 'a ptr llM" where "ll_ofs_ptr p ofs = doM {
    r \<leftarrow> llvm_ofs_ptr (to_val p) (to_val ofs);
    return (from_val r)
  }"  

  (* disabled in simple memory model
  definition ll_gep_struct :: "'p::llvm_rep ptr \<Rightarrow> nat \<Rightarrow> 'a::llvm_rep ptr llM" where "ll_gep_struct p i = doM {
    fcheck (STATIC_ERROR ''gep_struct: Expected struct type'') (llvm_is_s_struct (struct_of TYPE('p)));
    r \<leftarrow> llvm_checked_gep (the_raw_ptr p) (PFLD i);
    return (PTR r)
  }"
  *)

  subsubsection \<open>Pointer Comparison\<close>  
  text \<open>Note: There are no pointer comparison instructions in LLVM. 
    To compare pointers in LLVM, they have to be casted to integers first.
    However, our abstract memory model cannot assign a bit-width to pointers.
    
    Thus, we model pointer comparison instructions in our semantics, and let the 
    code generator translate them to integer comparisons. 
    
    Up to now, we only model pointer equality. 
    
    Note that the operand pointers must be null, or point to currently allocated memory.
    
    For less-than, more preconditions are required, which are consistent with the 
    actual memory layout of LLVM. We could, e.g., adopt the rules from the C standard here.
  \<close>
  
  text \<open>Check if a pair of pointers is valid for comparison operation, i.e., one is null or both are currently allocated\<close>
  (*definition check_ptrs_cmp :: "'a::llvm_rep ptr \<Rightarrow> 'a ptr \<Rightarrow> unit llM" where
    "check_ptrs_cmp p\<^sub>1 p\<^sub>2 \<equiv> if p\<^sub>1=null \<or> p\<^sub>2=null then return () else doM { ll_load p\<^sub>1; ll_load p\<^sub>2; return ()}"
  
  definition op_lift_ptr_cmp :: "_ \<Rightarrow> 'a::llvm_rep ptr \<Rightarrow> 'a ptr \<Rightarrow> 1 word llM"
    where "op_lift_ptr_cmp f a b \<equiv> doM {
    check_ptrs_cmp a b;  
    return (lint_to_word (bool_to_lint (f a b)))
  }"*)
  
  definition ll_ptrcmp_eq :: "'a ptr \<Rightarrow> 'a ptr \<Rightarrow> 1 word llM" where "ll_ptrcmp_eq a b \<equiv> doM {
    r \<leftarrow> llvm_ptr_eq (to_val a) (to_val b);
    return (from_val r)
  }"
  definition ll_ptrcmp_ne :: "'a ptr \<Rightarrow> 'a ptr \<Rightarrow> 1 word llM" where "ll_ptrcmp_ne a b \<equiv> doM {
    r \<leftarrow> llvm_ptr_neq (to_val a) (to_val b);
    return (from_val r)
  }"
  
  subsubsection \<open>Conversion Operations\<close>
  definition "llb_trunc i w \<equiv> doM {
    assert (width i > w);
    return (trunc w i)
  }"
  
  definition "llb_sext i w \<equiv> doM {
    assert (width i < w);
    return (sext w i)
  }"
  
  definition "llb_zext i w \<equiv> doM {
    assert (width i < w);
    return (zext w i)
  }"
  
  definition op_lift_iconv :: "_ \<Rightarrow> 'a::len word \<Rightarrow> 'b::len word itself  \<Rightarrow> 'b word llM"
    where "op_lift_iconv f a _ \<equiv> doM {
    let a = word_to_lint a;
    let w = LENGTH('b);
    r \<leftarrow> f a w;
    return (lint_to_word r)
  }"
  
  definition "ll_trunc \<equiv> op_lift_iconv llb_trunc"
  definition "ll_sext \<equiv> op_lift_iconv llb_sext"
  definition "ll_zext \<equiv> op_lift_iconv llb_zext"
  
    
        
        
  subsection \<open>Control Flow\<close>  

  text \<open>Our shallow embedding uses a structured control flow, which allows
    only sequential composition, if-then-else, and function calls.
    
    The code generator then maps sequential composition to basic blocks, 
    and if-then-else to a control flow graph with conditional branching.
    Function calls are mapped to LLVM function calls.  
   \<close>
  
  text \<open>We use the to Boolean conversion from word-lib. We re-state its semantics here.\<close>
    
  lemma to_bool_as_lint_to_bool:
    "to_bool (w::1 word) = lint_to_bool (word_to_lint w)"
    unfolding to_bool_def word_to_lint_def
    apply (clarsimp simp: ltrue_def lfalse_def lint_to_bool_def)
    apply transfer
    apply auto
    done
  
  lemma to_bool_eq[simp]: "to_bool (w::1 word) \<longleftrightarrow> w\<noteq>0"
    by (rule to_bool_neq_0)
  
  definition llc_if :: "1 word \<Rightarrow> 'a::llvm_repv llM \<Rightarrow> 'a llM \<Rightarrow> 'a llM" where
    "llc_if b t e \<equiv> doM {
      if to_bool b then t else e
    }"
  
  lemma mono_llc_If[partial_function_mono]: "
    \<lbrakk> M_mono' (\<lambda>D. F D); M_mono' (\<lambda>D. G D) \<rbrakk> \<Longrightarrow>
    M_mono' (\<lambda>D. llc_if b (F D) (G D))"  
    unfolding llc_if_def by pf_mono_prover
    
  subsubsection \<open>Parallel Combinator\<close>  
  definition llc_par :: "('a \<Rightarrow> 'ar llM) \<Rightarrow> ('b \<Rightarrow> 'br llM) \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> ('ar \<times> 'br) llM" where 
    "llc_par f g a b \<equiv> Mpar (f a) (g b)"

  lemma mono_llc_par[partial_function_mono]: "
    \<lbrakk>\<And>x. M_mono' (\<lambda>D. F D x); \<And>x. M_mono' (\<lambda>D. G D x) \<rbrakk>
    \<Longrightarrow> M_mono' (\<lambda>D. llc_par (F D) (G D) x\<^sub>1 x\<^sub>2)"
    unfolding llc_par_def 
    by pf_mono_prover
    
  subsubsection \<open>While-Combinator\<close>
  text \<open>
    Note: later in this development, we introduce a flag to control direct translation.
      If disabled, the code generator will refuse to accept while, but the 
      preprocessor will transform it into a tail recursive function.
  \<close>
    
  definition llc_while :: "('a::llvm_repv \<Rightarrow> 1 word llM) \<Rightarrow> ('a \<Rightarrow> 'a llM) \<Rightarrow> 'a \<Rightarrow> 'a llM" where
    "llc_while b f s\<^sub>0 \<equiv> Mwhile (\<lambda>s. doM {bb \<leftarrow> b s; return to_bool bb}) f s\<^sub>0"
      
  lemma gen_code_thm_llc_while:
    assumes "f \<equiv> llc_while b body"
    shows "f s = doM { ctd \<leftarrow> b s; llc_if ctd (doM { s\<leftarrow>body s; f s}) (return s)}"
    unfolding assms
    unfolding llc_while_def llc_if_def
    apply (rewrite Mwhile_unfold)
    by simp

  lemma llc_while_mono[partial_function_mono]:      
    assumes "\<And>x. M_mono' (\<lambda>f. b f x)"
    assumes "\<And>x. M_mono' (\<lambda>f. c f x)"
    shows "M_mono' (\<lambda>D. llc_while (b D) (c D) \<sigma>)"
    using assms unfolding llc_while_def 
    by pf_mono_prover
    
  (* 'Definition' of llc_while for presentation in paper: *)  
  lemma "llc_while b c s \<equiv> doM { x \<leftarrow> b s; llc_if x (doM {s\<leftarrow>c s; llc_while b c s}) (return s) }"
    unfolding llc_while_def llc_if_def
    apply (rewrite Mwhile_unfold)
    by simp
    
      
    
end
end
