section \<open>Shallow Embedding of LLVM Semantics\<close>
theory LLVM_Shallow
imports Main  
  "LLVM_Memory"
  "Monadify"
  "../lib/Definition_Utils" 
keywords "export_llvm" "llvm_deps" :: thy_decl
begin
  text \<open>We define a type synonym for the LLVM monad\<close>
  type_synonym 'a llM = "('a,unit,llvm_memory,err) M"
  translations
    (type) "'a llM" \<leftharpoondown> (type) "('a, unit, llvm_memory, err) M"
  
    

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
      and struct_of :: "'a itself \<Rightarrow> llvm_vstruct"
      and init :: 'a
    assumes from_to_id[simp]: "from_val o to_val = id"
    assumes struct_of_matches[simp]: "llvm_vstruct (to_val x) = (struct_of TYPE('a))"
    assumes init_zero: "to_val init = llvm_zero_initializer (struct_of TYPE('a))"
    
  begin
  
    lemma from_to_id'[simp]: "from_val (to_val x) = x" 
      using pointfree_idE[OF from_to_id] .
  
    lemma "to_val x = to_val y \<longleftrightarrow> x=y"  
      by (metis from_to_id')
      
  end
  
  text \<open>We use a phantom type to attach the type of the pointed to value to a pointer.\<close>
  datatype 'a::llvm_rep ptr = PTR (the_raw_ptr: llvm_ptr)
  definition null :: "'a::llvm_rep ptr" where "null = PTR llvm_null"
  

  text \<open>We instantiate the type classes for the supported types, 
    i.e., unit, word, ptr, and prod.\<close>
  
  instance unit :: llvm_repv by standard
  
  instantiation word :: (len) llvm_rep begin
    definition "to_val w \<equiv> llvm_int (lconst (len_of TYPE('a)) (uint w))"
    definition "from_val v \<equiv> word_of_int (lint_to_uint (llvm_the_int v))"
    definition [simp]: "struct_of_word (_::'a word itself) \<equiv> llvm_s_int (len_of TYPE('a))"
    definition [simp]: "init_word \<equiv> 0::'a word"
    
    instance
      apply standard
      apply (rule ext)
      apply (auto simp: from_val_word_def to_val_word_def)
      apply (auto simp: llvm_s_int_def llvm_zero_initializer_def llvm_int_def)
      done
      
  end
  
  instantiation ptr :: (llvm_rep) llvm_rep begin
    definition "to_val \<equiv> llvm_ptr o ptr.the_raw_ptr"
    definition "from_val v \<equiv> PTR (llvm_the_ptr v)"
    definition [simp]: "struct_of_ptr (_::'a ptr itself) \<equiv> llvm_s_ptr"
    definition [simp]: "init_ptr::'a ptr \<equiv> null"
  
    instance
      apply standard
      apply (rule ext)
      apply (auto simp: from_val_ptr_def to_val_ptr_def)
      apply (auto simp: llvm_zero_initializer_def llvm_ptr_def llvm_s_ptr_def null_def llvm_null_def)
      done
      
  end
  
  instantiation prod :: (llvm_rep, llvm_rep) llvm_rep begin
    definition "to_val_prod \<equiv> \<lambda>(a,b). llvm_pair (to_val a) (to_val b)"
    definition "from_val_prod p \<equiv> case llvm_the_pair p of (a,b) \<Rightarrow> (from_val a, from_val b)"
    definition [simp]: "struct_of_prod (_::('a\<times>'b) itself) \<equiv> llvm_s_pair (struct_of TYPE('a)) (struct_of TYPE('b))"
    definition [simp]: "init_prod ::'a\<times>'b \<equiv> (init,init)"
    
    instance
      apply standard
      apply (rule ext)
      apply (auto simp: from_val_prod_def to_val_prod_def)
      apply (auto simp: llvm_pair_def llvm_s_pair_def init_zero llvm_zero_initializer_def)
      done
      
  end

  text \<open>Checked conversion from value\<close>  
  definition checked_from_val :: "llvm_val \<Rightarrow> 'a::llvm_rep llM" where
    "checked_from_val v \<equiv> doM {
      fcheck (STATIC_ERROR ''Type mismatch'') (llvm_vstruct v = struct_of TYPE('a));
      return (from_val v)
    }" 
  
  subsection \<open>Instructions\<close>  
  
  text \<open>The instructions are arranged in the order as they are described in the 
    LLVM Language Reference Manual \<^url>\<open>https://llvm.org/docs/LangRef.html\<close>.\<close>
    
  
  subsubsection \<open>Binary Operations\<close>  
  text \<open>We define a generic lifter for binary arithmetic operations.
    It is parameterized by an error condition.
  \<close> (* TODO: Use precondition instead of negated precondition! *)
  
  definition op_lift_arith2 :: "_ \<Rightarrow> _ \<Rightarrow> 'a::len word \<Rightarrow> 'a word \<Rightarrow> 'a word llM"
    where "op_lift_arith2 ovf f a b \<equiv> doM {
    let a = word_to_lint a;
    let b = word_to_lint b;
    fcheck (OVERFLOW_ERROR) (\<not>ovf a b);
    return (lint_to_word (f a b))
  }"
        
  definition "op_lift_arith2' \<equiv> op_lift_arith2 (\<lambda>_ _. False)"

  definition udivrem_is_undef :: "lint \<Rightarrow> lint \<Rightarrow> bool" 
    where "udivrem_is_undef a b \<equiv> lint_to_uint b=0"
  definition sdivrem_is_undef :: "lint \<Rightarrow> lint \<Rightarrow> bool" 
    where "sdivrem_is_undef a b \<equiv> lint_to_sint b=0 \<or> sdivrem_ovf a b"
  
  definition "ll_add \<equiv> op_lift_arith2' (+)"
  definition "ll_sub \<equiv> op_lift_arith2' (-)"
  definition "ll_mul \<equiv> op_lift_arith2' ( * )"
  definition "ll_udiv \<equiv> op_lift_arith2 udivrem_is_undef (div)"
  definition "ll_urem \<equiv> op_lift_arith2 udivrem_is_undef (mod)"
  definition "ll_sdiv \<equiv> op_lift_arith2 sdivrem_is_undef (sdiv)"
  definition "ll_srem \<equiv> op_lift_arith2 sdivrem_is_undef (smod)"
  
  
  subsubsection \<open>Compare Operations\<close>
  definition op_lift_cmp :: "_ \<Rightarrow> 'a::len word \<Rightarrow> 'a word \<Rightarrow> 1 word llM"
    where "op_lift_cmp f a b \<equiv> doM {
    let a = word_to_lint a;
    let b = word_to_lint b;
    return (lint_to_word (bool_to_lint (f a b)))
  }"
    
  definition op_lift_ptr_cmp :: "_ \<Rightarrow> 'a::llvm_rep ptr \<Rightarrow> 'a ptr \<Rightarrow> 1 word llM"
    where "op_lift_ptr_cmp f a b \<equiv> doM {
    return (lint_to_word (bool_to_lint (f a b)))
  }"
  
  definition "ll_icmp_eq \<equiv>  op_lift_cmp (=)"
  definition "ll_icmp_ne \<equiv>  op_lift_cmp (\<noteq>)"
  definition "ll_icmp_sle \<equiv> op_lift_cmp (\<le>\<^sub>s)"
  definition "ll_icmp_slt \<equiv> op_lift_cmp (<\<^sub>s)"
  definition "ll_icmp_ule \<equiv> op_lift_cmp (\<le>)"
  definition "ll_icmp_ult \<equiv> op_lift_cmp (<)"

  text \<open>Note: There are no pointer compare instructions in LLVM. 
    To compare pointers in LLVM, they have to be casted to integers first.
    However, our abstract memory model cannot assign a bit-width to pointers.
    
    Thus, we model pointer comparison instructions in our semantics, and let the 
    code generator translate them to integer comparisons. 
    
    Up to now, we only model pointer equality. 
    For less-than, suitable preconditions are required, which are consistent with the 
    actual memory layout of LLVM. We could, e.g., adopt the rules from the C standard here.
  \<close>
  definition "ll_ptrcmp_eq \<equiv> op_lift_ptr_cmp (=)"
  definition "ll_ptrcmp_ne \<equiv> op_lift_ptr_cmp (\<noteq>)"
  

  
  subsubsection \<open>Bitwise Binary Operations\<close>  
  definition "shift_ovf a n \<equiv> nat (lint_to_uint n) \<ge> width a"
  definition "bitSHL' a n \<equiv> bitSHL a (nat (lint_to_uint n))"
  definition "bitASHR' a n \<equiv> bitASHR a (nat (lint_to_uint n))"
  definition "bitLSHR' a n \<equiv> bitLSHR a (nat (lint_to_uint n))"
  
  definition "ll_shl \<equiv> op_lift_arith2 shift_ovf bitSHL'"  
  definition "ll_lshr \<equiv> op_lift_arith2 shift_ovf bitLSHR'"  
  definition "ll_ashr \<equiv> op_lift_arith2 shift_ovf bitASHR'"
  
  definition "ll_and \<equiv> op_lift_arith2' (AND)"
  definition "ll_or \<equiv> op_lift_arith2' (OR)"
  definition "ll_xor \<equiv> op_lift_arith2' (XOR)"
    

  subsubsection \<open>Aggregate Operations\<close>
  text \<open>In LLVM, there is an \<open>extractvalue\<close> and \<open>insertvalue\<close> operation.
    In our shallow embedding, these get instantiated for \<open>fst\<close> and \<open>snd\<close>.\<close>
  definition ll_extract_fst :: "('a::llvm_rep \<times> 'b::llvm_rep) \<Rightarrow> 'a llM" where "ll_extract_fst ab \<equiv> return (fst ab)"
  definition ll_extract_snd :: "('a::llvm_rep \<times> 'b::llvm_rep) \<Rightarrow> 'b llM" where "ll_extract_snd ab \<equiv> return (snd ab)"
  definition ll_insert_fst :: "('a::llvm_rep \<times> 'b::llvm_rep) \<Rightarrow> 'a \<Rightarrow> ('a\<times>'b) llM" where "ll_insert_fst ab a \<equiv> return (a,snd ab)"
  definition ll_insert_snd :: "('a::llvm_rep \<times> 'b::llvm_rep) \<Rightarrow> 'b \<Rightarrow> ('a\<times>'b) llM" where "ll_insert_snd ab b \<equiv> return (fst ab,b)"
    
  subsubsection \<open>Memory Access and Addressing Operations\<close>
    
  definition ll_load :: "'a::llvm_rep ptr \<Rightarrow> 'a llM" where
    "ll_load p \<equiv> doM {
      r \<leftarrow> llvm_load (the_raw_ptr p);
      checked_from_val r
    }"
    
  definition ll_store :: "'a::llvm_rep \<Rightarrow> 'a ptr \<Rightarrow> unit llM" where
    "ll_store v p \<equiv> llvm_store (to_val v) (the_raw_ptr p)"

  text \<open>Note that LLVM itself does not have malloc and free instructions.
    However, these are primitive instructions in our abstract memory model, 
    such that we have to model them in our semantics.
    
    The code generator will map them to the C standard library 
    functions \<open>calloc\<close> and \<open>free\<close>.
  \<close>
    
  definition ll_malloc :: "'a::llvm_rep itself \<Rightarrow> _::len word \<Rightarrow> 'a ptr llM" where
    "ll_malloc TYPE('a) n = doM {
      fcheck MEM_ERROR (unat n > 0); \<comment> \<open>Disallow empty malloc\<close>
      r \<leftarrow> llvm_allocn (to_val (init::'a)) (unat n);
      return (PTR r)
    }"
        
  definition ll_free :: "'a::llvm_rep ptr \<Rightarrow> unit llM" 
    where "ll_free p \<equiv> llvm_free (the_raw_ptr p)"


  text \<open>As for the aggregate operations, the \<open>getelementptr\<close> instruction is instantiated 
    for pointer indexing, fst, and snd. \<close>
      
  definition ll_ofs_ptr :: "'a::llvm_rep ptr \<Rightarrow> _::len word \<Rightarrow> 'a ptr llM" where "ll_ofs_ptr p ofs = doM {
    r \<leftarrow> llvm_checked_idx_ptr (the_raw_ptr p) (sint ofs);
    return (PTR r)
  }"  

  definition ll_gep_fst :: "('a::llvm_rep \<times> 'b::llvm_rep) ptr \<Rightarrow> 'a ptr llM" where "ll_gep_fst p = doM {
    r \<leftarrow> llvm_checked_gep (the_raw_ptr p) PFST;
    return (PTR r)
  }"

  definition ll_gep_snd :: "('a::llvm_rep \<times> 'b::llvm_rep) ptr \<Rightarrow> 'b ptr llM" where "ll_gep_snd p = doM {
    r \<leftarrow> llvm_checked_gep (the_raw_ptr p) PSND;
    return (PTR r)
  }"

  
  subsubsection \<open>Conversion Operations\<close>
  definition "llb_trunc i w \<equiv> doM {
    fcheck (STATIC_ERROR ''Trunc must go to smaller type'') (width i > w);
    return (trunc w i)
  }"
  
  definition "llb_sext i w \<equiv> doM {
    fcheck (STATIC_ERROR ''Sext must go to greater type'') (width i < w);
    return (sext w i)
  }"
  
  definition "llb_zext i w \<equiv> doM {
    fcheck (STATIC_ERROR ''Zext must go to greater type'') (width i < w);
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
    by (metis bin_rest_BIT bin_rest_x2)
  
  lemma to_bool_eq[simp]: "to_bool (w::1 word) \<longleftrightarrow> w\<noteq>0"
    by (rule to_bool_neq_0)
  
  definition llc_if :: "1 word \<Rightarrow> 'a::llvm_repv llM \<Rightarrow> 'a llM \<Rightarrow> 'a llM" where
    "llc_if b t e \<equiv> doM {
      if to_bool b then t else e
    }"
  
  lemma llc_if_mono[partial_function_mono]:      
    "\<lbrakk>monotone orda ordb F; monotone orda ordb G\<rbrakk> \<Longrightarrow> monotone orda ordb (\<lambda>f. llc_if b (F f) (G f))"
    unfolding llc_if_def by pf_mono_prover

  subsubsection \<open>While-Combinator\<close>
  text \<open>
    Note that we also include the while combinator at this point, as we plan
    to add direct translation of while to a control flow graph as an optional 
    feature of the code generator. 
    
    In the current state, the code generator will recognize the while combinator, 
    but refuse to translate it.
  
    Note that the standard way of using a while combinator is to translate it to 
    a tail recursive function call, which the preprocessor can do automatically.
  \<close>
    
  definition llc_while :: "('a::llvm_repv \<Rightarrow> 1 word llM) \<Rightarrow> ('a \<Rightarrow> 'a llM) \<Rightarrow> 'a \<Rightarrow> 'a llM" where
    "llc_while b f s\<^sub>0 \<equiv> mwhile (\<lambda>s. b s \<bind> return o to_bool) f s\<^sub>0"
      
  lemma gen_code_thm_llc_while:
    assumes "f \<equiv> llc_while b body"
    shows "f s = doM { ctd \<leftarrow> b s; llc_if ctd (doM { s\<leftarrow>body s; f s}) (return s)}"
    unfolding assms
    unfolding llc_while_def llc_if_def
    apply (rewrite mwhile_unfold)
    by simp

    
  (* TODO: This setup belongs to the preprocessor. Move! *)  
  lemma llc_while_mono[partial_function_mono]:      
    assumes "\<And>x. M_mono (\<lambda>f. b f x)"
    assumes "\<And>x. M_mono (\<lambda>f. c f x)"
    shows "M_mono (\<lambda>D. llc_while (b D) (c D) \<sigma>)"
    using assms unfolding llc_while_def by pf_mono_prover
      
  declaration \<open>fn _ => Definition_Utils.declare_extraction_group @{binding LLVM} #> snd\<close>
    
  declaration {* fn _ =>
    Definition_Utils.add_extraction (@{extraction_group LLVM},\<^here>) {
      pattern = Logic.varify_global @{term "llc_while b body"},
      gen_thm = @{thm gen_code_thm_llc_while},
      gen_tac = K (K no_tac)
    }
  *}

  declaration {*fn _ =>
    Definition_Utils.add_extraction (@{extraction_group LLVM},\<^here>) {
      pattern = Logic.varify_global @{term "REC (B::('a \<Rightarrow> 'b llM) \<Rightarrow> 'a \<Rightarrow> 'b llM)"},
      gen_thm = @{thm REC_unfold},
      gen_tac = Partial_Function.mono_tac
    }
  *}
    
  subsection \<open>Code Generator\<close>
  
  text \<open>General functions\<close>
  ML \<open> structure LLC_Lib = 
    struct
      fun dest_llM (Type (@{type_name M},[T,@{typ unit},@{typ llvm_memory},@{typ err}])) = T
        | dest_llM ty = raise TYPE("dest_llM",[ty],[]);
      
      val is_llM = can dest_llM

      
      fun dest_numeralT (Type (@{type_name \<open>bit0\<close>},[ty])) = 2*dest_numeralT ty
        | dest_numeralT (Type (@{type_name \<open>bit1\<close>},[ty])) = 2*dest_numeralT ty+1
        | dest_numeralT (Type (@{type_name \<open>num0\<close>},[])) = 0
        | dest_numeralT (Type (@{type_name \<open>num1\<close>},[])) = 1
        | dest_numeralT ty = raise TYPE ("dest_numeralT",[ty],[])
    
      fun dest_wordT (Type (@{type_name word},[T])) = dest_numeralT T
        | dest_wordT T = raise TYPE("dest_wordT",[T],[])
        
      fun dest_word_const (t) = HOLogic.dest_number t |>> dest_wordT
      
      
      (* TODO: Move *)
      fun instantiate_uc (tyenv,tenv) thm = let
        val thy = Thm.theory_of_thm thm
        
        val tyi = Vartab.dest tyenv |> map (fn (n,(s,T)) => ((n,s),Thm.global_ctyp_of thy T))
        val ti = Vartab.dest tenv |> map (fn (n,(s,t)) => ((n,s),Thm.global_cterm_of thy t))
      in
        Thm.instantiate (tyi,ti) thm
      end

      fun is_monomorphic_const (Const (_,T)) = 
        not (Term.exists_subtype (fn TVar _ => true | TFree _ => true | _ => false) T)
      | is_monomorphic_const _ = false

      fun assert_monomorphic_const t = 
        is_monomorphic_const t orelse 
          raise TYPE("Expected monomorphic constant",[fastype_of t],[t])
            

      fun unique_variant1 n name ntab = let
        val name' = if n=0 then name else name ^ Int.toString n
      in    
        if Symtab.defined ntab name' then unique_variant1 (n+1) name ntab
        else (name', Symtab.insert_set name' ntab)
      end
      
      val unique_variant = unique_variant1 0
      
      
      fun the_assert msg NONE = raise Fail msg 
         | the_assert _ (SOME x) = x 
      
                    
    end
  \<close>
  
  text \<open>The intermediate representation of shallowly embedded LLVM programs.\<close>
  ML \<open> structure LLC_Intermediate = 
    struct
    
      (* LLC intermediate representation. Somewhere in between Isabelle and LLVM-IR *)    
      
      datatype llc_type = TInt of int | TPtr of llc_type | TPair of llc_type*llc_type
      datatype llc_const = CInit | CInt of int | CNull
      datatype llc_opr = OVar of string | OConst of llc_const
      type llc_topr = llc_type * llc_opr
      datatype llc_topr' = OOOp of llc_topr | OOType of llc_type

      datatype llc_cmd = 
                 CmIf of llc_topr * llc_block * llc_block
               | CmWhile of (llc_type * string) option * llc_block * llc_block * llc_topr
               | CmInstr of string * llc_topr' list
               | CmCall of llc_type option * string * llc_topr list
      
          and llc_block =
                BlBind of (llc_type * string) option * llc_cmd * llc_block
              | BlReturn of llc_topr option 
    
      datatype llc_eqn =              
                EQN of llc_type option * string * (llc_type * string) list * llc_block
    
    end
  \<close>
        
  text \<open>Parser from Isabelle terms to intermediate representation\<close>
  ML \<open> structure LLC_Compiler = 
    struct
      open LLC_Lib LLC_Intermediate
    
      (* Direct compilation of while: not (yet) supported
      val llc_compile_while =
        Config.bool (Config.declare ("llc_compile_while", \<^here>) (fn _ => Config.Bool true));
      *)
      
      fun head_of_cthm thm = case Thm.prop_of thm of
        @{mpat "Trueprop (?lhs = _)"} => head_of lhs
      | _ => raise THM ("head_of_cthm",~1,[thm])  
    
    
      fun compute_fun_names fixes thms = let
        val _ = map (assert_monomorphic_const o fst) fixes
      
        val ftab = Termtab.make fixes
        val names = fold (fn (_,n) => Symtab.update_new (n,())) fixes Symtab.empty
        
        fun add_thm thm (ftab,names) = let
          val c = head_of_cthm thm
        in
          if Termtab.defined ftab c then
            (ftab,names)
          else let
            val n = dest_Const c |> fst |> Name.desymbolize NONE
            val (n,names) = unique_variant n names
            val ftab = Termtab.update_new (c,n) ftab
          in
            (ftab,names)
          end
        end
        
        val (ftab,_) = fold add_thm thms (ftab,names)
      in
        ftab
      end

      
      

                
      (* TODO/FIXME: Populate with actual instructions! Register them, together with their compilers! *)  
      fun is_llvm_instr name = String.isPrefix "LLVM_Shallow.ll_" name
                
                      
      fun llc_parse_type (Type (@{type_name word},[T])) = dest_numeralT T |> TInt
        | llc_parse_type (Type (@{type_name ptr},[T])) = llc_parse_type T |> TPtr
        | llc_parse_type (Type (@{type_name prod},[Ta,Tb])) = TPair (llc_parse_type Ta, llc_parse_type Tb)
        | llc_parse_type T = raise TYPE ("llc_parse_type: ",[T],[])
        
      fun llc_parse_vtype (Type (@{type_name unit},[])) = NONE
        | llc_parse_vtype T = SOME (llc_parse_type T)
        
      fun llc_parse_const @{mpat (typs) \<open>init::?'v_T::llvm_rep\<close>} = (llc_parse_type T, CInit)
        | llc_parse_const @{mpat (typs) \<open>null::?'v_T::llvm_rep ptr\<close>} = (TPtr (llc_parse_type T), CNull)
        | llc_parse_const t = case try dest_word_const t of
            SOME (w,v) => (TInt w, CInt v)
          | NONE => raise TERM ("llc_parse_const: ",[t])
      
      local    
        datatype llc_env = ENV of Symtab.set * (llc_type * string) Termtab.table * (llc_type * string) option list   
        
        fun make_uniqueN n tab name = let
          val name' = if n=0 then name else name ^ Int.toString n
        in
          if Symtab.defined tab name' then
            make_uniqueN (n+1) tab name
          else
            name'
        end
        
        val make_unique = make_uniqueN 0
        
        
        val env_empty = ENV (Symtab.empty,Termtab.empty,[])
        
        fun env_add_sym name (ENV (syms,params,bnds)) = let
          val name = Name.desymbolize NONE name |> make_unique syms
          val syms = Symtab.insert_set name syms
        in
          (name,ENV (syms,params,bnds))
        end
        
        fun env_add_bound lty name env = let
          val (name,env) = env_add_sym name env
          val ENV (syms,params,bnds) = env
          val bnds = SOME (lty,name)::bnds
        in
          (name,ENV (syms,params,bnds))
        end
        
        fun env_add_unit_bound (ENV (syms,params,bnds)) = ENV (syms,params,NONE::bnds)
        
        fun env_add_param v env = let
          val (iname,ty) = dest_Var v
          val name = fst iname
          val lty = llc_parse_type ty
        
          val (name,env) = env_add_sym name env
          val ENV (syms,params,bnds) = env
          val params = Termtab.update_new (v,(lty,name)) params
        in
          ((lty,name),ENV (syms,params,bnds))
        end

        fun env_lookup_bound (ENV (_,_,bnds)) i = case nth bnds i of SOME x => x | NONE => raise TERM ("Reference to bound unit variable",[])
        fun env_lookup_param (ENV (_,params,_)) v = Termtab.lookup params v |> the
                
      
        fun env_parse_add_bound T x env = case llc_parse_vtype T of
          NONE => (NONE, env_add_unit_bound env)
        | SOME ty => let
            val (x,env) = env_add_bound ty x env
          in
            (SOME (ty,x),env)
          end  
        
        
      in
      
        fun llc_parse_op env (Bound i) = env_lookup_bound env i ||> OVar
          | llc_parse_op env (t as Var _) = env_lookup_param env t ||> OVar
          | llc_parse_op _ t = llc_parse_const t ||> OConst
      
        fun llc_parse_op' _ (t as @{mpat \<open>TYPE (_)\<close>}) = t |> Logic.dest_type |> llc_parse_type |> OOType
          | llc_parse_op' env t = llc_parse_op env t |> OOOp
          
        fun llc_parse_op_bool env t = let
          val (ty,x) = llc_parse_op env t
          val _ = ty=TInt 1 orelse raise TERM ("parse_op_bool: not a Boolean",[t])
        in
          (ty,x)
        end  
          
        fun ftab_lookup ftab f = let
          val fname = Termtab.lookup ftab f
          val _ = is_none fname andalso raise TYPE("No such function in ftab",[fastype_of f],[f])
          val fname = the fname
        in fname end  
        
        fun llc_parse_cmd ftab env rty t = 
          let
            val (f,args) = strip_comb t
            val _ = is_Const f orelse raise TERM ("parse_cmd: Invalid head",[f])
  
            val (cname,_) = dest_Const f
          in
            case cname of
              @{const_name \<open>llc_if\<close>} => (case args of 
                  [arg_cond,arg_then,arg_else] => CmIf 
                    (llc_parse_op_bool env arg_cond, 
                     llc_parse_block ftab env arg_then |> fst, 
                     llc_parse_block ftab env arg_else |> fst)
                | _ => raise TERM ("parse_cmd: If needs 3 arguments",[t])
              )
            | @{const_name \<open>llc_while\<close>} => (case args of [@{mpat "\<lambda>_. ?tcond"}, @{mpat "\<lambda>xb. ?tbody"}, arg_inits] => let
                    val inits = llc_parse_op_bool env arg_inits
                    
                    val (sv,env) = env_parse_add_bound xb_T xb env
                    val (cond,_) = llc_parse_block ftab env tcond
                    val (body,_) = llc_parse_block ftab env tbody
                  in
                    CmWhile (sv, cond, body, inits)
                  end
                | _ => raise TERM ("parse_cmd: While needs 3 arguments",[t])
              )
            | _ => 
                if is_llvm_instr cname then CmInstr (cname,map (llc_parse_op' env) args)
                else CmCall (rty, ftab_lookup ftab f,map (llc_parse_op env) args)
                   
          end
        and llc_parse_block ftab env @{mpat "bind ?m (\<lambda>x. ?f)"} = 
          let
            val rty = llc_parse_vtype x_T
            val cmd = llc_parse_cmd ftab env rty m
            val (sv,env) = env_parse_add_bound x_T x env
            val (blk,env) = llc_parse_block ftab env f
          in
            (BlBind (sv,cmd,blk),env)
          end
          | llc_parse_block _ env @{mpat "return ()"} = (BlReturn NONE, env)
          | llc_parse_block _ env @{mpat "return ?x"} = (llc_parse_op env x |> SOME |> BlReturn, env)
          | llc_parse_block _ _ t = raise TERM ("llc_parse_block: structural error",[t])
          
          
        fun llc_parse_eqn ftab @{mpat "Trueprop (?lhs = ?rhs)"} = let
          val (hdc,params) = strip_comb lhs
        
          val _ = is_Const hdc orelse raise (TERM ("llc_parse_eqn: Expected constant head", [hdc]))
          val _ = map (fn a => is_Var a orelse raise TERM ("llc_parse_eqn: arguments must be vars",[a])) params

          val fname = ftab_lookup ftab hdc 
                    
          val (params,env) = fold_map env_add_param params env_empty
          val (blk,env) = llc_parse_block ftab env rhs
          
          val rlty = fastype_of lhs |> dest_llM |> llc_parse_vtype
          
          val _ = env
        in
          EQN (rlty,fname,params,blk)
        end
        | llc_parse_eqn _ t = raise TERM ("llc_parse_eqn: Expected equation of form lhs = rhs", [t])
          
          
      end      
      
      fun parse_cthms ftab thms = map (llc_parse_eqn ftab o Thm.prop_of) thms
            
      
          
    end
    
  \<close>  

  text \<open>LLVM Builder. Interface to build actual LLVM text.\<close>
  ML_file "LLVM_Builder.ml"
  
  text \<open>Compiler from intermediate representation to actual LLVM text.\<close>
  ML \<open> structure LLC_Backend = 
    struct
      open LLC_Lib LLC_Intermediate
    
      type vtab = LLVM_Builder.value Symtab.table
      type builder = vtab -> string -> llc_topr' list -> LLVM_Builder.T -> LLVM_Builder.value option
    
      fun llc_ty (TInt w) = LLVM_Builder.mkty_i w
        | llc_ty (TPtr ty) = LLVM_Builder.mkty_ptr (llc_ty ty)
        | llc_ty (TPair (ty1, ty2)) = LLVM_Builder.mkty_struct [llc_ty ty1, llc_ty ty2]
      
      
      fun llc_const_to_val ty CInit = LLVM_Builder.mkc_zeroinit (llc_ty ty)
        | llc_const_to_val ty (CInt v) = LLVM_Builder.mkc_i (llc_ty ty) v
        | llc_const_to_val ty (CNull) = LLVM_Builder.mkc_null (llc_ty ty)
      
      fun llc_op_to_val vtab (_,OVar x) = the_assert ("Variable not in vtab " ^ x) (Symtab.lookup vtab x)
        | llc_op_to_val _ (ty,OConst c) = llc_const_to_val ty c
        
      
      
      fun arith_instr_builder iname vtab dst [OOOp x1, OOOp x2] b = (
        LLVM_Builder.mk_arith_instr iname b dst (llc_op_to_val vtab x1) (llc_op_to_val vtab x2) |> SOME
      ) | arith_instr_builder _ _ _ _ _ = raise Fail "arith_instr_builder: invalid arguments"
      
      fun icmp_instr_builder cmpcode vtab dst [OOOp x1, OOOp x2] b = (
        LLVM_Builder.mk_icmp_instr cmpcode b dst (llc_op_to_val vtab x1) (llc_op_to_val vtab x2) |> SOME
      ) | icmp_instr_builder _ _ _ _ _ = raise Fail "icmp_instr_builder: invalid arguments"

      fun ptrcmp_instr_builder cmpcode vtab dst [OOOp x1, OOOp x2] b = (
        LLVM_Builder.mk_ptrcmp_instr cmpcode b dst (llc_op_to_val vtab x1) (llc_op_to_val vtab x2) |> SOME
      ) | ptrcmp_instr_builder _ _ _ _ _ = raise Fail "icmp_instr_builder: invalid arguments"
            
      fun conv_instr_builder cmpcode vtab dst [OOOp x1, OOType ty] b = (
        LLVM_Builder.mk_conv_instr cmpcode b dst (llc_op_to_val vtab x1) (llc_ty ty) |> SOME
      ) | conv_instr_builder _ _ _ _ _ = raise Fail "conv_instr_builder: invalid arguments"

      fun extract_value_builder idx vtab dst [OOOp x1] b = (
        LLVM_Builder.mk_extractvalue b dst (llc_op_to_val vtab x1) idx |> SOME
      ) | extract_value_builder _ _ _ _ _ = raise Fail "extract_value_builder: invalid arguments"

      fun insert_value_builder idx vtab dst [OOOp x1, OOOp x2] b = (
        LLVM_Builder.mk_insertvalue b dst (llc_op_to_val vtab x1) (llc_op_to_val vtab x2) idx |> SOME
      ) | insert_value_builder _ _ _ _ _ = raise Fail "insert_value_builder: invalid arguments"
      
      fun malloc_builder vtab dst [OOType ty, OOOp x] b = (
        LLVM_Builder.mk_malloc b dst (llc_ty ty) (llc_op_to_val vtab x) |> SOME
      ) | malloc_builder _ _ _ _ = raise Fail "malloc_builder: invalid arguments"
            
      fun free_builder vtab _ [OOOp x] b = (
        LLVM_Builder.mk_free b (llc_op_to_val vtab x); NONE
      ) | free_builder _ _ _ _ = raise Fail "free_builder: invalid arguments"

      fun load_builder vtab dst [OOOp x] b = (
        LLVM_Builder.mk_load b dst (llc_op_to_val vtab x) |> SOME
      ) | load_builder _ _ _ _ = raise Fail "load_builder: invalid arguments"
      
      fun store_builder vtab _ [OOOp x1, OOOp x2] b = (
        LLVM_Builder.mk_store b (llc_op_to_val vtab x1) (llc_op_to_val vtab x2); NONE
      ) | store_builder _ _ _ _ = raise Fail "store_builder: invalid arguments"

      fun ofs_ptr_builder vtab dst [OOOp x1, OOOp x2] b = (
        LLVM_Builder.mk_ofs_ptr b dst (llc_op_to_val vtab x1) (llc_op_to_val vtab x2) |> SOME
      ) | ofs_ptr_builder _ _ _ _ = raise Fail "ofs_ptr_builder: invalid arguments"
      
      fun gep_idx_builder idx vtab dst [OOOp x1] b = (
        LLVM_Builder.mk_gep_idx b dst (llc_op_to_val vtab x1) (LLVM_Builder.mkc_iw 32 idx) |> SOME
      ) | gep_idx_builder _ _ _ _ _ = raise Fail "gep_idx_builder: invalid arguments"
      
      fun register_builder (b:builder) (n:string) = Symtab.update_new (n,b)
      
      fun register_prfx_builder prfx b n = let
        val iname = Long_Name.base_name n |> unprefix prfx
      in
        register_builder (b iname) n
      end

      val builders = Symtab.empty
        |> fold (register_prfx_builder "ll_" arith_instr_builder) 
          [@{const_name ll_add}, @{const_name ll_sub}, @{const_name ll_mul},
           @{const_name ll_udiv}, @{const_name ll_urem}, @{const_name ll_sdiv}, @{const_name ll_srem},
           @{const_name ll_shl}, @{const_name ll_lshr}, @{const_name ll_ashr},
           @{const_name ll_and}, @{const_name ll_or}, @{const_name ll_xor}
          ]
        |> fold (register_prfx_builder "ll_" conv_instr_builder) [
             @{const_name ll_trunc}, @{const_name ll_sext}, @{const_name ll_zext}
          ]  
        |> fold (register_prfx_builder "ll_icmp_" icmp_instr_builder) [
             @{const_name ll_icmp_eq}, @{const_name ll_icmp_ne}, 
             @{const_name ll_icmp_slt}, @{const_name ll_icmp_sle}, 
             @{const_name ll_icmp_ult}, @{const_name ll_icmp_ule} 
          ]  
        |> fold (register_prfx_builder "ll_ptrcmp_" ptrcmp_instr_builder) [
             @{const_name ll_ptrcmp_eq}, @{const_name ll_ptrcmp_ne}
          ]  
        |> register_builder (extract_value_builder 0) @{const_name ll_extract_fst}          
        |> register_builder (extract_value_builder 1) @{const_name ll_extract_snd}          
        |> register_builder (insert_value_builder 0) @{const_name ll_insert_fst}          
        |> register_builder (insert_value_builder 1) @{const_name ll_insert_snd}          

        |> register_builder (malloc_builder) @{const_name ll_malloc}          
        |> register_builder (free_builder) @{const_name ll_free}          
        |> register_builder (load_builder) @{const_name ll_load}          
        |> register_builder (store_builder) @{const_name ll_store}          
      
        |> register_builder (ofs_ptr_builder) @{const_name ll_ofs_ptr}          
        |> register_builder (gep_idx_builder 0) @{const_name ll_gep_fst}          
        |> register_builder (gep_idx_builder 1) @{const_name ll_gep_snd}          
            

      fun vtab_bind (SOME dst) (SOME v) vtab = Symtab.update_new (dst,v) vtab  
        | vtab_bind (SOME dst) NONE _ = raise Fail ("Void instruction bound to value (" ^ dst ^ ") ")
        | vtab_bind _ _ vtab = vtab
        
      fun build_instr b vtab dst (iname,args) = let
        val bld = Symtab.lookup builders iname 
          |> the_assert ("Unknown instruction " ^ iname)
          
        val v = bld vtab (the_default "uu" dst) args b
      in
        vtab_bind dst v vtab
      end  
      
      fun build_call b vtab dst (rty,pname,args) = let
        val args = map (llc_op_to_val vtab) args
        val rty = map_option llc_ty rty
        
        val v = case rty of 
          NONE => (LLVM_Builder.mk_call_void b pname args; NONE)
        | SOME rty => LLVM_Builder.mk_call b (the_default "uu" dst) rty pname args |> SOME
        
      in
        vtab_bind dst v vtab
      end
      
      fun build_if build_block b vtab dst (op_cond, blk_then, blk_else) = let
        val l_then = LLVM_Builder.variant_label b "then"
        val l_else = LLVM_Builder.variant_label b "else"
        val l_ctd_if = LLVM_Builder.variant_label b "ctd_if"
      
        val _ = LLVM_Builder.mk_cbr b (llc_op_to_val vtab op_cond) l_then l_else
        
        val _ = LLVM_Builder.open_bb b l_then 
        val r_then = build_block b vtab blk_then
        val l_then' = LLVM_Builder.mk_br b l_ctd_if
        
        val _ = LLVM_Builder.open_bb b l_else
        val r_else = build_block b vtab blk_else
        val l_else' = LLVM_Builder.mk_br b l_ctd_if
        
        val _ = LLVM_Builder.open_bb b l_ctd_if
        val res = case (r_then, r_else) of
          (NONE,NONE) => NONE
        | (SOME r_then, SOME r_else) => 
            SOME (LLVM_Builder.mk_phi b (the_default "uu" dst) [(r_then,l_then'), (r_else,l_else')])
        | _ => raise Fail ("If type mismatch (void/non-void)")
      in
        vtab_bind dst res vtab
      end
      
      (*fun build_while build_block b vtab dst (sv,blk_cond, blk_body, op_init) = let
        val l_start = LLVM_Builder.variant_label b "while_start"
        val l_body = LLVM_Builder.variant_label b "while_body"
        val l_end = LLVM_Builder.variant_label b "while_end"
        
        val _ = LLVM_Builder.open_bb b l_body
        val s_body = build_block b vtab blk_body
        val l_body' = LLVM_Builder.mk_br b l_start
        
        val _ = LLVM_Builder.open_bb b l_start
        
        val s_body = build_block b vtab blk_body
        val l_body' = LLVM_Builder.mk_br b l_start
        
        
        
        
      
      in
        1
      end*)
      
      fun build_cmd b vtab dst (CmInstr ia) = build_instr b vtab dst ia
        | build_cmd b vtab dst (CmCall na) = build_call b vtab dst na
        | build_cmd b vtab dst (CmIf bte) = build_if build_block b vtab dst bte
        | build_cmd _ _ _ (CmWhile _) = raise Fail "Direct while compilation still to be done!"
        (*| build_cmd b vtab dst (CmWhile cbi) = build_while build_block b vtab dst cbi*)
      and build_block b vtab (BlBind (dst,cmd,blk)) = let
            val dst = map_option snd dst
            val vtab = build_cmd b vtab dst cmd
          in
            build_block b vtab blk
          end
        | build_block _ vtab (BlReturn x) = map_option (llc_op_to_val vtab) x
              
        
        
      fun build_eqn b (EQN (rty, pname, params, blk)) = let
        val params = map (apfst llc_ty) params
        val rty = map_option llc_ty rty
        
        val paramsv = LLVM_Builder.open_proc b rty pname params
        
        val vtab = fold (Symtab.update_new o apfst snd) (params ~~ paramsv) Symtab.empty
        
        val retv = build_block b vtab blk
        
        val _ = LLVM_Builder.mk_return b retv
        val _ = LLVM_Builder.close_proc b
      in
        ()
      end
    
      fun eqns_to_llvm eqns = let
        val b = LLVM_Builder.builder ()
        val _ = map (build_eqn b) eqns
        val res = LLVM_Builder.string_of b
      in
        res
      end
      
      
      
    end
       
  \<close>  
    
  
subsection \<open>Preprocessor\<close>  
  text \<open>
    The actual code generator expects a set of monomorphic, well-shaped equations.
    The preprocessor processes user specified equations, monomorphizes them and 
    brings them into the right shape.
  \<close>
  
  named_theorems llvm_code \<open>Isabelle-LLVM code theorems\<close>
  named_theorems llvm_inline

  lemma llvm_inline_bind_laws[llvm_inline]:
    "bind m return = m"
    "bind (bind m (\<lambda>x. f x)) g = bind m (\<lambda>x. bind (f x) g)"
    by auto
  
  lemma unit_meta_eq: "x \<equiv> ()" by simp
  
  lemma pull_lambda_case: "(case x of (a,b) \<Rightarrow> \<lambda>y. t a b y) = (\<lambda>y. case x of (a,b) \<Rightarrow> t a b y)"
    apply (rule ext) apply (cases x) by auto

  ML \<open> structure LLC_Preprocessor = 
    struct
      open LLC_Lib
          
      structure Monadify = Gen_Monadify (
      
        fun mk_return x = @{mk_term "return ?x ::_ llM"}
        fun mk_bind m f = @{mk_term "bind ?m ?f ::_ llM"}
      
        fun dest_return @{mpat "return ?x ::_ llM"} = SOME x | dest_return _ = NONE
        fun dest_bind @{mpat "bind ?m ?f ::_ llM"} = SOME (m,f) | dest_bind _ = NONE
        
        fun dest_monadT (Type (@{type_name M},[T,@{typ unit},@{typ llvm_memory},@{typ err}])) = SOME T | dest_monadT _ = NONE

        val strip_op = K strip_comb
        
        val bind_return_thm = @{lemma "bind m return = m" by simp}
        val return_bind_thm = @{lemma "bind (return x) f = f x" by simp}
        val bind_bind_thm = @{lemma "bind (bind m (\<lambda>x. f x)) g = bind m (\<lambda>x. bind (f x) g)" by simp}
        
      )
      
      (********* Normalization of code theorems *)
      
      local
            
        fun rhs_conv cv ct =
          (case Thm.term_of ct of
            @{mpat "_\<equiv>_"} => Conv.arg_conv cv ct
          | @{mpat "Trueprop (_ = _)"} => HOLogic.Trueprop_conv (Conv.arg_conv cv) ct
          | _ => raise CTERM ("rhs_conv", [ct]));
        
        
      in      
    
        fun cthm_inline ctxt thm = let
          val inline_thms = Named_Theorems.get ctxt @{named_theorems llvm_inline}
          val ctxt = put_simpset HOL_ss ctxt addsimps inline_thms
        in
          Conv.fconv_rule (rhs_conv (Simplifier.rewrite ctxt)) thm
        end
      
        val cthm_monadify = Conv.fconv_rule o (rhs_conv o Monadify.monadify_conv)
              
        val inline_iteration_limit =
          Config.int (Config.declare ("inline_iteration_limit", \<^here>) (fn _ => Config.Int ~1));
        
        
        fun monadify_inline_cthm ctxt thm = let
          fun rpt 0 thm' = raise THM ("inline_iteration_limit exceeded",~1,[thm,thm'])
            | rpt n thm = let
            val thm' = thm |> cthm_monadify ctxt |> cthm_inline ctxt
          in
            if Thm.eq_thm_prop (thm,thm') then thm 
            else rpt (n-1) thm'
          end
          
          val it_limit = Config.get ctxt inline_iteration_limit
        in
          thm 
          |> cthm_inline ctxt
          |> rpt it_limit
        end  
    
      end        
      
      (*
        Bring code theorem into parseable format. To be applied after inlining, 
          immediately before parsing.
        
        Applies eta-expansion, return-expansion, and converts \<equiv> to =.
        Finally, it will replace unit-binds by () constants and anonymous bind.
        
        May fail on non-well-formed theorems.
      *)
      fun cthm_format ctxt thm = let
        fun ensure_abs (t as Abs _) = t
          | ensure_abs t = let
                val T = fastype_of t |> domain_type
                val x = Name.variant "x" (Term.declare_term_names t Name.context) |> fst
              in
                 Abs (x,T,incr_boundvars 1 t $ Bound 0)
              end
      
        fun normalize_bind1 t = let
          val (f,args) = strip_comb t
          val _ = is_Const f orelse raise TERM ("cthm_format: Invalid head",[f])
  
          val args_is_M = fastype_of f |> binder_types |> map is_llM
                  
          val _ = length args_is_M = length args orelse raise TYPE ("cthm_format: All arguments must be explicit", [fastype_of f], [t])
          
          val args = map2 (fn isM => isM?normalize) args_is_M args
          
        in
          list_comb (f, args)
        end  
          
        and normalize @{mpat "bind ?m ?f"} = let
            val m = normalize_bind1 m
            val f = ensure_abs f |> normalize
          in @{mk_term "bind ?m ?f"} end
        | normalize (Abs (x,T,t)) = Abs (x,T,normalize t)
        | normalize (t as @{mpat "return _"}) = t
        | normalize t = let val t = normalize_bind1 t in @{mk_term "bind ?t (\<lambda>x. return x)"} end
      
        fun normalize_eq @{mpat "?a = ?b"} = let val b = normalize b in @{mk_term "?a = ?b"} end
          | normalize_eq t = raise TERM ("format_code_thm: normalize_eq", [t])
      
        fun norm_tac ctxt = ALLGOALS (simp_tac (put_simpset HOL_ss ctxt addsimps @{thms bind_laws}))
    
        fun cthm_norm_lambda ctxt thm = let
          val thm = Local_Defs.unfold ctxt @{thms pull_lambda_case} thm
        
          fun r thm = case Thm.concl_of thm of
            @{mpat "Trueprop (_ = (\<lambda>_. _))"} => r (thm RS @{thm fun_cong})
          | _ => thm
          
        in
          r thm
        end
        
      in
        thm 
        |> (simplify (put_simpset HOL_ss ctxt addsimps @{thms Monad.bind_laws atomize_eq}))
        |> (Conv.fconv_rule (HOLogic.Trueprop_conv (Refine_Util.f_tac_conv ctxt normalize_eq (norm_tac ctxt))))
        |> cthm_norm_lambda ctxt
        |> (Conv.fconv_rule (Conv.top_sweep_conv (K (Conv.rewr_conv @{thm unit_meta_eq})) ctxt))
      end
      
        
      fun cthm_normalize ctxt = monadify_inline_cthm ctxt #> cthm_format ctxt

      
      (********* Gathering of code equations *)
      (* TODO: Use net *)
      
      fun dep_check_lhs (t as Const _) = t
        | dep_check_lhs t = raise TERM ("dep_dest_lhs: LHS must be constant",[t])
      
      fun dep_prep_code_thm thm = case Thm.prop_of thm of
        @{mpat \<open>Trueprop (?lhs = _)\<close>} => (head_of lhs |> dep_check_lhs,thm)
      | @{mpat \<open>?lhs \<equiv> _\<close>} => (head_of lhs |> dep_check_lhs,thm)
      | _ => raise THM ("dep_prep_code_thm",~1,[thm])
      
      
      fun dep_try_instantiate_code_thm c (l,thm) = let
        val thy = Thm.theory_of_thm thm
      in
        case SOME (Pattern.match thy (l,c) (Vartab.empty,Vartab.empty)) handle Pattern.MATCH => NONE of
          NONE => NONE
        | SOME m => SOME (instantiate_uc m thm)
      end
      
      fun dep_find_code_thm pthms c = 
        case get_first (dep_try_instantiate_code_thm c) pthms of
          SOME eqn => eqn
        | NONE => raise TERM ("No code equation",[c])
      
        
      fun dep_is_call_const (@{const_name bind},_) = false
        | dep_is_call_const (@{const_name return},_) = false
        | dep_is_call_const (name,T) = 
                    not (String.isPrefix "LLVM_Shallow.ll_" name)
            andalso not (String.isPrefix "LLVM_Shallow.llc_" name)
            andalso is_llM (body_type T)
            andalso not (exists (exists_subtype is_llM) (binder_types T))
        
        
        
      fun calls_of_cthm @{mpat \<open>Trueprop (_ = ?rhs)\<close>} = 
            Term.add_consts rhs [] |> filter dep_is_call_const |> map Const
        | calls_of_cthm t = raise TERM ("calls_of_cthm",[t])
                
        
      fun process_code_thm ctxt thm = let
        val thm = cthm_normalize ctxt thm
        val calls = calls_of_cthm (Thm.prop_of thm)
      in
        (thm, calls)
      end        
      
      fun gather_code_thms ctxt roots = let
        val thy = Proof_Context.theory_of ctxt
        val pthms = Named_Theorems.get ctxt @{named_theorems llvm_code}
          |> map dep_prep_code_thm
          |> Refine_Util.subsume_sort fst thy
      
        fun process_root c ctab = let
          val _ = is_Const c orelse raise TERM("gather_code_thms: Expected constant",[c])
        in
          case Termtab.lookup ctab c of
            SOME _ => ctab
          | NONE => let
              val _ = assert_monomorphic_const c
              val (teqn,calls) = dep_find_code_thm pthms c |> process_code_thm ctxt
              
              val ctab = Termtab.update_new (c,teqn) ctab
              val ctab = fold process_root calls ctab
            in
              ctab
            end
        end 

      in
        fold process_root roots Termtab.empty
        |> Termtab.dest |> map snd
      end
        
    end
  \<close>
  
  text \<open>
    The driver combines preeprocessing and code generation, 
    and defines the user interface of the code generator, namely the commands
    @{command export_llvm} and @{command llvm_deps}.
  \<close>
  
  ML \<open> structure LLC_Driver 
    = struct
    
      val cfg_llvm_debug = Attrib.setup_config_bool @{binding llvm_debug} (K false)
    
      fun pretty_cthms ctxt cthms = let 
        val ctxt = Config.put Syntax_Trans.eta_contract_raw (Config.Bool false) ctxt      
      in Pretty.big_list "Code Theorems" (map (Thm.pretty_thm ctxt) cthms) end

      fun pretty_ftab_entry ctxt (t,n) = Pretty.block [
        Syntax.pretty_term ctxt t, Pretty.brk 1, Pretty.str ":: ", Syntax.pretty_typ ctxt (fastype_of t), 
        Pretty.brk 1,Pretty.str "\<rightarrow>",Pretty.brk 1, Pretty.str n
      ]
          
      fun pretty_ftab ctxt ftab = Pretty.big_list "Symbol table:" 
        (map (pretty_ftab_entry ctxt) (Termtab.dest ftab))
                
      fun consts_to_llvm ctxt cns = let
        val dbg = Config.get ctxt cfg_llvm_debug
        
        fun trace s = if dbg then Pretty.string_of (s ()) |> tracing else ()
      
        val _ = trace (fn () => Pretty.str "Gathering code theorems")
        val cthms = LLC_Preprocessor.gather_code_thms ctxt (map fst cns)
        val _ = trace (fn () => pretty_cthms ctxt cthms)
        
        val _ = trace (fn () => Pretty.str "Computing symbol table")
        val fixes = map_filter (fn (_,NONE) => NONE | (cn,SOME name) => SOME (cn,name)) cns
        val ftab = LLC_Compiler.compute_fun_names fixes cthms
        val _ = trace (fn () => pretty_ftab ctxt ftab)
        
        
        val _ = trace (fn () => Pretty.str "Translating code theorems to IL")
        val eqns = LLC_Compiler.parse_cthms ftab cthms
        
        val _ = trace (fn () => Pretty.str "Writing LLVM")
        val res = LLC_Backend.eqns_to_llvm eqns
      in
        (cthms,res)
      end
      
      local
        val using_master_directory =
          File.full_path o Resources.master_directory o Proof_Context.theory_of;
          
        fun prepare_path ctxt (s,pos) = let
          val _ = Position.report pos Markup.language_path;
          val path = Path.explode s;
          val _ = Position.report pos (Markup.path (Path.smart_implode path));
          val path = using_master_directory ctxt path
        in path end
      
        fun write_out NONE s = writeln s
          | write_out (SOME path) s = File.write path s
      in
        fun export_llvm ctxt cns path = let
          val ctxt = Config.put Syntax_Trans.eta_contract_raw (Config.Bool false) ctxt
          val (cthms,llvm_code) = consts_to_llvm ctxt cns
          val _ = write_out path llvm_code
        in
          cthms
        end
        
        val export_llvm_cmd = (Args.mode "debug" -- Parse_Spec.opt_thm_name ":" -- (Scan.repeat1 (Parse.term -- Scan.option (@{keyword "is"} |-- Parse.name )) -- Scan.option ((@{keyword "file"} |-- Parse.position Parse.path))) 
            >> (fn ((dbg,bnd),(cns,path)) => fn lthy => let 
            
              local
                val lthy = (dbg?Config.put cfg_llvm_debug true) lthy
              in
                val cns = map (apfst (Syntax.read_term lthy)) cns
                val path = Option.map (prepare_path lthy) path 
                
                val cthms = export_llvm lthy cns path
              end
              
              val (_,lthy) = Local_Theory.note (bnd,cthms) lthy 
              
            in lthy end))
        
        val llvm_deps_cmd = Parse_Spec.opt_thm_name ":" -- Scan.repeat1 Parse.term
          >> (fn (bnd,cns) => fn lthy => let
              val cns = map (Syntax.read_term lthy) cns
              val cthms = LLC_Preprocessor.gather_code_thms lthy cns
              val (_,lthy) = Local_Theory.note (bnd,cthms) lthy 
              
              val _ = pretty_cthms lthy cthms |> Pretty.string_of |> writeln
          
             in lthy end 
          )
        
            
      end

      val _ = Outer_Syntax.local_theory @{command_keyword export_llvm} "generate LLVM code for constants" export_llvm_cmd
      val _ = Outer_Syntax.local_theory @{command_keyword llvm_deps} "Print LLVM code theorems for constants" llvm_deps_cmd
    end
  \<close>
  
  
  subsection \<open>Ad-Hoc Regression Tests\<close>
  
  definition exp :: "64 word \<Rightarrow> 64 word llM" where "exp i \<equiv> doM {
    s \<leftarrow> ll_insert_fst init 1;
    s \<leftarrow> ll_insert_snd s i;
    s \<leftarrow> llc_while
      (\<lambda>s. doM {
        i \<leftarrow> ll_extract_snd s;
        ll_icmp_ne i 0
      })
      (\<lambda>s. doM {
        c \<leftarrow> ll_extract_fst s;
        i \<leftarrow> ll_extract_snd s;
        
        c \<leftarrow> ll_mul c 2;
        i \<leftarrow> ll_sub i 1;
        
        s \<leftarrow> ll_insert_fst init c;
        s \<leftarrow> ll_insert_snd s i;
        
        return s
      })
      s;
  
    ll_extract_fst s
  }"
  
  text \<open>Executability of semantics inside Isabelle\<close>
  value "run (exp 32) heap_empty"
  
  definition streq :: "8 word ptr \<Rightarrow> 8 word ptr \<Rightarrow> 1 word llM" where [llvm_code]: "streq s\<^sub>1 s\<^sub>2 = doM {
      x \<leftarrow> ll_load s\<^sub>1;
      ll_load s\<^sub>2 \<bind> ll_icmp_eq x
    }"
  
  export_llvm streq  
  
  definition [llvm_code]: "test2 (n::32 word) \<equiv> doM {
    n \<leftarrow> ll_add n 42;
    p \<leftarrow> ll_malloc TYPE(16 word) n;
    p \<leftarrow> ll_ofs_ptr p (5::32 word);
    ll_store 42 p;
    r \<leftarrow> ll_load p; 
    return r  
  }"
  
  definition [llvm_code]: "add_add (a::_ word) \<equiv> doM {
    x \<leftarrow> ll_add a a;
    x \<leftarrow> ll_add x x;
    return x
  }"

  definition [llvm_code]: "add_add_driver (a::32 word) (b::64 word) \<equiv> doM {
    a \<leftarrow> add_add a;
    b \<leftarrow> add_add b;
    a \<leftarrow> ll_zext a TYPE(64 word);
    b \<leftarrow> ll_add a b;
    return b
  }"
    

  ML_val \<open>
    val thms = LLC_Preprocessor.gather_code_thms @{context} [@{const add_add_driver}]
    val ftab = LLC_Compiler.compute_fun_names [(@{const add_add_driver},"foo")] thms
    val eqns = LLC_Compiler.parse_cthms ftab thms
  \<close>
  
  export_llvm add_add_driver
  
  definition [llvm_code]: "main (argc::32 word) (argv::8 word ptr ptr) \<equiv> doM {
    r \<leftarrow> test2 argc;
    r \<leftarrow> ll_zext r TYPE(32 word);
    return r
  }" 

  definition [llvm_code]: "main_exp (argc::32 word) (argv::8 word ptr ptr) \<equiv> doM {
    argc \<leftarrow> ll_zext argc TYPE(64 word);
    r \<leftarrow> exp argc;
    r \<leftarrow> ll_trunc r TYPE(32 word);
    return r
  }" 
  
prepare_code_thms [llvm_code] exp_def
  
    
export_llvm foobar: main_exp is main file "code/exp.ll"

export_llvm (debug) main is main file "code/test2.ll"

value "run (main 0 null) llvm_empty_memory"
      
end
