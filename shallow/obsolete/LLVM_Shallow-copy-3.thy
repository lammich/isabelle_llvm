theory LLVM_Shallow
imports Main  
  "LLVM_Memory"
  "../lib/Definition_Utils" 
keywords "export_llvm" "export_llvm_new" :: thy_decl
begin
    
  class llvm_repv  
    
  class llvm_rep = llvm_repv +
    fixes to_val :: "'a \<Rightarrow> llvm_val"
      and from_val :: "llvm_val \<Rightarrow> 'a"
      and struct_of :: "'a itself \<Rightarrow> llvm_vstruct"
      and init :: 'a
    assumes from_to_id[simp]: "from_val o to_val = id"
    assumes struct_of_matches[simp]: "llvm_vstruct (to_val x) = (struct_of TYPE('a))"
    
  begin
  
    lemma from_to_id'[simp]: "from_val (to_val x) = x" 
      using pointfree_idE[OF from_to_id] .
  
  end
  
  datatype 'a::llvm_rep ptr = PTR (the_raw_ptr: llvm_ptr)
  definition null where "null = PTR llvm_null"
  
  (*definition init :: "'a::llvm_rep" where "init \<equiv> from_val (init_val (struct_of TYPE('a)))"*)

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
      done
      
  end
  
    
  
  type_synonym 'a llM = "('a,unit,llvm_memory,err) M"
    
  text \<open>Check that pointer is in bounds\<close>  
  
  definition check_ptr :: "'a::llvm_rep ptr \<Rightarrow> unit llM" where
    "check_ptr p \<equiv> llvm_check_ptr (the_raw_ptr p)"
  

  definition ll_malloc :: "'a::llvm_rep itself \<Rightarrow> _::len word \<Rightarrow> 'a ptr llM" where
    "ll_malloc TYPE('a) n = doM {
      r \<leftarrow> llvm_allocn (to_val (init::'a)) (unat n);
      return (PTR r)
    }"
        
  definition ll_free :: "'a::llvm_rep ptr \<Rightarrow> unit llM" 
    where "ll_free p \<equiv> llvm_free (the_raw_ptr p)"

  definition checked_from_val :: "llvm_val \<Rightarrow> 'a::llvm_rep llM" where
    "checked_from_val v \<equiv> doM {
      fcheck (STATIC_ERROR ''Type mismatch'') (llvm_vstruct v = struct_of TYPE('a));
      return (from_val v)
    }" 
        
  definition ll_load :: "'a::llvm_rep ptr \<Rightarrow> 'a llM" where
    "ll_load p \<equiv> doM {
      r \<leftarrow> llvm_load (the_raw_ptr p);
      checked_from_val r
    }"
    
  definition ll_store :: "'a::llvm_rep \<Rightarrow> 'a ptr \<Rightarrow> unit llM" where
    "ll_store v p \<equiv> llvm_store (to_val v) (the_raw_ptr p)"
  
 
    
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
    
    
    
  definition op_lift_arith2 :: "_ \<Rightarrow> _ \<Rightarrow> 'a::len word \<Rightarrow> 'a word \<Rightarrow> 'a word llM"
    where "op_lift_arith2 ovf f a b \<equiv> doM {
    let a = word_to_lint a;
    let b = word_to_lint b;
    fcheck (OVERFLOW_ERROR) (\<not>ovf a b);
    return (lint_to_word (f a b))
  }"
        
  definition "op_lift_arith2' \<equiv> op_lift_arith2 (\<lambda>_ _. False)"

  definition op_lift_cmp :: "_ \<Rightarrow> 'a::len word \<Rightarrow> 'a word \<Rightarrow> 1 word llM"
    where "op_lift_cmp f a b \<equiv> doM {
    let a = word_to_lint a;
    let b = word_to_lint b;
    return (lint_to_word (bool_to_lint (f a b)))
  }"
    
  
  definition op_lift_iconv :: "_ \<Rightarrow> 'a::len word \<Rightarrow> 'b::len word itself  \<Rightarrow> 'b word llM"
    where "op_lift_iconv f a _ \<equiv> doM {
    let a = word_to_lint a;
    let w = LENGTH('b);
    r \<leftarrow> f a w;
    return (lint_to_word r)
  }"
  
  
  
  definition "shift_ovf a n \<equiv> nat (lint_to_uint n) \<ge> width a"
  definition "bitSHL' a n \<equiv> bitSHL a (nat (lint_to_uint n))"
  definition "bitASHR' a n \<equiv> bitASHR a (nat (lint_to_uint n))"
  definition "bitLSHR' a n \<equiv> bitLSHR a (nat (lint_to_uint n))"
  definition udivrem_is_undef :: "lint \<Rightarrow> lint \<Rightarrow> bool" where "udivrem_is_undef a b \<equiv> lint_to_uint b=0"
  definition sdivrem_is_undef :: "lint \<Rightarrow> lint \<Rightarrow> bool" where "sdivrem_is_undef a b \<equiv> lint_to_sint b=0 \<or> sdivrem_ovf a b"
  
  definition "ll_add \<equiv> op_lift_arith2' (+)"
  definition "ll_sub \<equiv> op_lift_arith2' (-)"
  definition "ll_mul \<equiv> op_lift_arith2' ( * )"
  definition "ll_udiv \<equiv> op_lift_arith2 udivrem_is_undef (div)"
  definition "ll_urem \<equiv> op_lift_arith2 udivrem_is_undef (mod)"
  definition "ll_sdiv \<equiv> op_lift_arith2 sdivrem_is_undef (sdiv)"
  definition "ll_srem \<equiv> op_lift_arith2 sdivrem_is_undef (smod)"
  definition "ll_shl \<equiv> op_lift_arith2 shift_ovf bitSHL'"  
  definition "ll_lshr \<equiv> op_lift_arith2 shift_ovf bitLSHR'"  
  definition "ll_ashr \<equiv> op_lift_arith2 shift_ovf bitASHR'"
  definition "ll_trunc \<equiv> op_lift_iconv llb_trunc"
  definition "ll_sext \<equiv> op_lift_iconv llb_sext"
  definition "ll_zext \<equiv> op_lift_iconv llb_zext"

  definition "ll_and \<equiv> op_lift_arith2' (AND)"
  definition "ll_or \<equiv> op_lift_arith2' (OR)"
  definition "ll_xor \<equiv> op_lift_arith2' (XOR)"
  
  definition "ll_icmp_eq \<equiv>  op_lift_cmp (=)"
  definition "ll_icmp_ne \<equiv>  op_lift_cmp (\<noteq>)"
  definition "ll_icmp_sle \<equiv> op_lift_cmp (\<le>\<^sub>s)"
  definition "ll_icmp_slt \<equiv> op_lift_cmp (<\<^sub>s)"
  definition "ll_icmp_ule \<equiv> op_lift_cmp (\<le>)"
  definition "ll_icmp_ult \<equiv> op_lift_cmp (<)"

  term ll_malloc 
  term ll_free
  term ll_load
  term ll_store
                                      
  definition ll_extract_fst :: "('a::llvm_rep \<times> 'b::llvm_rep) \<Rightarrow> 'a llM" where "ll_extract_fst ab \<equiv> return (fst ab)"
  definition ll_extract_snd :: "('a::llvm_rep \<times> 'b::llvm_rep) \<Rightarrow> 'b llM" where "ll_extract_snd ab \<equiv> return (snd ab)"
  definition ll_insert_fst :: "('a::llvm_rep \<times> 'b::llvm_rep) \<Rightarrow> 'a \<Rightarrow> ('a\<times>'b) llM" where "ll_insert_fst ab a \<equiv> return (a,snd ab)"
  definition ll_insert_snd :: "('a::llvm_rep \<times> 'b::llvm_rep) \<Rightarrow> 'b \<Rightarrow> ('a\<times>'b) llM" where "ll_insert_snd ab b \<equiv> return (fst ab,b)"

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
  
  definition llc_while :: "('a::llvm_repv \<Rightarrow> 1 word llM) \<Rightarrow> ('a \<Rightarrow> 'a llM) \<Rightarrow> 'a \<Rightarrow> 'a llM" where
    "llc_while b f s\<^sub>0 \<equiv> mwhile (\<lambda>s. b s \<bind> return o to_bool) f s\<^sub>0"
  
  lemma gen_code_thm_llc_while:
    assumes "f \<equiv> llc_while b body"
    shows "f s = doM { ctd \<leftarrow> b s; llc_if ctd (doM { s\<leftarrow>body s; f s}) (return s)}"
    unfolding assms
    unfolding llc_while_def llc_if_def
    apply (rewrite mwhile_unfold)
    by simp
  
  setup {*
    Definition_Utils.add_extraction "llc_while" {
      pattern = Logic.varify_global @{term "llc_while b body"},
      gen_thm = @{thm gen_code_thm_llc_while},
      gen_tac = K (K no_tac)
    }
  *}
    
    
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
  
  value "run (exp 32) heap_empty"
    
  ML_file "LLVM_Builder.ml"

  named_theorems llvm_code \<open>Isabelle-LLVM code theorems\<close>
    
  ML \<open>
  
    structure LLVM_Compiler = struct
    
      fun dest_llM (Type (@{type_name M},[T,@{typ unit},@{typ llvm_memory},@{typ err}])) = T
        | dest_llM ty = raise TYPE("dest_llM",[ty],[]);
    
      val is_llM = can dest_llM
        
      fun normalize_code_thm ctxt thm = let
        fun ensure_abs (t as Abs _) = t
          | ensure_abs t = @{mk_term "\<lambda>x. ?t x"}
      
        fun normalize_bind1 t = let
          val (f,args) = strip_comb t
          val _ = is_Const f orelse raise TERM ("Invalid head",[f])
  
          val args_is_M = fastype_of f |> binder_types |> map is_llM
                  
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
          | normalize_eq t = raise TERM ("normalize_eq", [t])
      
        fun norm_tac ctxt = ALLGOALS (simp_tac (put_simpset HOL_ss ctxt addsimps @{thms bind_laws}))
    
      in
        thm 
        |> (simplify (put_simpset HOL_ss ctxt addsimps @{thms bind_laws atomize_eq}))
        |> (Conv.fconv_rule (HOLogic.Trueprop_conv (Refine_Util.f_tac_conv ctxt normalize_eq (norm_tac ctxt))))
      end
      
      fun dest_numeralT (Type (@{type_name \<open>bit0\<close>},[ty])) = 2*dest_numeralT ty
        | dest_numeralT (Type (@{type_name \<open>bit1\<close>},[ty])) = 2*dest_numeralT ty+1
        | dest_numeralT (Type (@{type_name \<open>num0\<close>},[])) = 0
        | dest_numeralT (Type (@{type_name \<open>num1\<close>},[])) = 1
        | dest_numeralT ty = raise TYPE ("dest_numeralT",[ty],[])
    
      fun dest_wordT (Type (@{type_name word},[T])) = dest_numeralT T
        | dest_wordT T = raise TYPE("dest_wordT",[T],[])
        
      fun dest_word_const (t) = HOLogic.dest_number t |>> dest_wordT
      
      fun ty_to_llvm (Type (@{type_name word},[T])) = dest_numeralT T |> LLVM_Builder.mkty_i
        | ty_to_llvm (Type (@{type_name ptr},[T])) = ty_to_llvm T |> LLVM_Builder.mkty_ptr
        | ty_to_llvm (Type (@{type_name prod},[Ta,Tb])) = LLVM_Builder.mkty_struct [ty_to_llvm Ta, ty_to_llvm Tb]
        | ty_to_llvm T = raise TYPE ("Cannot convert to LLVM-Type",[T],[])
        
      
      
      fun const_to_llvm @{mpat (typs) \<open>init::?'v_T::llvm_rep\<close>} = LLVM_Builder.mkc_zeroinit (ty_to_llvm T)
        | const_to_llvm t = case try dest_word_const t of
            SOME (i,t) => LLVM_Builder.mkc_iw i t
          | NONE => raise TERM ("Cannot convert constant to LLVM",[t])
            
      (*        
        | const_to_llvm (t as @{mpat "0::_ word"}) = dest_word_const t |> uncurry LLVM_Builder.mkc_iw
        | const_to_llvm (t as @{mpat "1::_ word"}) = dest_word_const t |> uncurry LLVM_Builder.mkc_iw
        | const_to_llvm (t as @{mpat "numeral _::_ word"}) = dest_word_const t |> uncurry LLVM_Builder.mkc_iw
        | const_to_llvm t = raise TERM ("Cannot convert constant to LLVM",[t])
      *)
        
      
      datatype bcontext = BCTXT of LLVM_Builder.value Termtab.table * LLVM_Builder.value option list
      
      val bcontext = BCTXT (Termtab.empty,[])
      fun bctxt_add_bound v (BCTXT (params,bnds)) = BCTXT (params,v::bnds)
      fun bctxt_add_param (p, v) (BCTXT (params,bnds)) = BCTXT (Termtab.update_new (p, v) params, bnds)
      
      fun bctxt_lookup_bound (BCTXT (_,bnds)) i = nth bnds i |> the
      fun bctxt_lookup_param (BCTXT (params,_)) p = Termtab.lookup params p |> the
      fun val_of_op bc (Bound i) = bctxt_lookup_bound bc i
        | val_of_op bc (t as Var _) = bctxt_lookup_param bc t
        | val_of_op _ t = const_to_llvm t
      
        
      type state = {
        worklist : (string * typ * string) list Unsynchronized.ref,  (* Constants for which code has to be generated *)
        processed : (typ * string) Symtab.table Unsynchronized.ref, (* Constants for which code has already been emitted, value is expected type of constant *)
        builder : LLVM_Builder.T,
        ctxt : Proof.context,
        tab : (typ * thm) Symtab.table 
      }  

      fun register_const (s:state) rname (name,ty) = let
        val rname = the_default name rname
      in
        case Symtab.lookup (!(#processed s)) name of
          NONE => (
            Unsynchronized.change (#worklist s) (curry op :: (name,ty,rname));
            Unsynchronized.change (#processed s) (Symtab.update_new (name,(ty,rname)));
            rname
          )
        | SOME (ty',rname') => (
            (ty=ty' orelse raise TYPE ("Cannot generate overloaded functions: " ^ name,[ty,ty'],[]))
              andalso (rname = rname' orelse raise Fail("Export name clash: " ^ rname' ^ " vs " ^ rname))
             ; rname)
      end
              
      fun lookup_const s (name,ty) = 
        case Symtab.lookup (!(#processed s)) name of
          NONE => register_const s NONE (name,ty)
        | SOME (_,rname) => rname
      
      fun fetch_next (s:state) = Unsynchronized.change_result (#worklist s)
        (fn [] => (NONE,[]) | x::xs => (SOME x,xs))
         
         
      fun compile_do_block (state:state) = let 
        val b = #builder state
        
        type op_builder = (bcontext -> string -> (typ * term) list -> LLVM_Builder.value option)
        type op_builder_table = op_builder Symtab.table  
  
        val val_arg = fn bc => val_of_op bc o snd
        val ty_arg = K (snd #> Logic.dest_type #> ty_to_llvm)
  
        fun opb_1args' opb bc dst [op1] = opb bc dst op1
          | opb_1args' _ _ _ ts = raise TYPE("INTERNAL: Operation expects one argument",map fst ts, map snd ts)

        fun opb_1args opb co1 cr bc dst [op1] = opb dst (co1 bc op1) |> cr
          | opb_1args _ _ _ _ _ ts = raise TYPE("INTERNAL: Operation expects one argument",map fst ts, map snd ts)
                                 
        fun opb_2args opb co1 co2 cr bc dst [op1,op2] = opb dst (co1 bc op1) (co2 bc op2) |> cr
          | opb_2args _ _ _ _ _ _ ts = raise TYPE("INTERNAL: Operation expects two arguments",map fst ts, map snd ts)
  
        fun opb_3args' opb bc dst [op1,op2,op3] = opb bc dst op1 op2 op3
          | opb_3args' _ _ _ ts = raise TYPE("INTERNAL: Operation expects three arguments",map fst ts, map snd ts)
                
        fun opb_arith iname = opb_2args (LLVM_Builder.mk_arith_instr iname b) val_arg val_arg SOME 
        fun opb_icmp iname = opb_2args (LLVM_Builder.mk_icmp_instr iname b) val_arg val_arg SOME 
          
        fun opb_iconv iname = opb_2args (LLVM_Builder.mk_conv_instr iname b) val_arg ty_arg SOME

        val opb_malloc = opb_2args (LLVM_Builder.mk_malloc b) ty_arg val_arg SOME 
        val opb_free = opb_1args' (fn bc => fn _ => fn op1 => (LLVM_Builder.mk_free b (val_arg bc op1); NONE))

        val opb_load = opb_1args (LLVM_Builder.mk_load b) val_arg SOME
        val opb_store = opb_2args (K (LLVM_Builder.mk_store b)) val_arg val_arg (K NONE)
        
                        
        val opb_extract_fst = opb_1args' (fn bc => fn dst => fn (_,t1) => let
            val op1 = val_of_op bc t1
          in 
            LLVM_Builder.mk_extractvalue b dst op1 0
            |> SOME
          end
        )  
        
        val opb_extract_snd = opb_1args' (fn bc => fn dst => fn (_,t1) => let
            val op1 = val_of_op bc t1
          in 
            LLVM_Builder.mk_extractvalue b dst op1 1
            |> SOME
          end
        )
  
        val opb_insert_fst = opb_2args 
          (fn dst => fn op1 => fn op2 => LLVM_Builder.mk_insertvalue b dst op1 op2 0)
          val_arg val_arg SOME
        val opb_insert_snd = 
          opb_2args (fn dst => fn op1 => fn op2 => LLVM_Builder.mk_insertvalue b dst op1 op2 1)
          val_arg val_arg SOME
        
        val opb_ofs_ptr = opb_2args (LLVM_Builder.mk_ofs_ptr b) val_arg val_arg SOME

        val opb_gep_fst = opb_1args (fn dst => fn op1 => LLVM_Builder.mk_gep_idx b dst op1 (LLVM_Builder.mkc_iw 32 0)) val_arg SOME
        val opb_gep_snd = opb_1args (fn dst => fn op1 => LLVM_Builder.mk_gep_idx b dst op1 (LLVM_Builder.mkc_iw 32 1)) val_arg SOME
                  
          
        fun add_op_xlate cname builder = Symtab.update_new (cname,builder)
        
        fun add_canonical_op_xlate prfx cname builder = let
          val iname = cname 
            |> Long_Name.base_name
            |> unprefix prfx
        in
          add_op_xlate cname (builder iname)
        end
        
        val add_ll_op_xlate = add_canonical_op_xlate "ll_"
        
        fun add_cmp_op_xlate cname = add_canonical_op_xlate "ll_icmp_" cname opb_icmp
        
        
        fun opb_call bc dst rty (cname,ty) ops = let
          val rname = lookup_const state (cname,ty)
          val ops = map (val_of_op bc o snd) ops;
        in
          if rty = @{typ unit} then (
            LLVM_Builder.mk_call_void b rname ops;
            NONE)
          else let
            val rty = ty_to_llvm rty
          in
            LLVM_Builder.mk_call b dst rty rname ops
            |> SOME
          end  
        end
        
        local
          fun opb_if_aux bc dst (op1: typ*term) (op2: typ*term) (op3: typ*term) = let
            val l_then = LLVM_Builder.variant_label b "then"
            val l_else = LLVM_Builder.variant_label b "else"
            val l_ctd_if = LLVM_Builder.variant_label b "ctd_if"
          
            val _ = LLVM_Builder.mk_cbr b (val_arg bc op1) l_then l_else
            
            val _ = LLVM_Builder.open_bb b l_then 
            val r_then = compile_do_block state bc (snd op2)
            val l_then' = LLVM_Builder.mk_br b l_ctd_if
            
            val _ = LLVM_Builder.open_bb b l_else
            val r_else = compile_do_block state bc (snd op3)
            val l_else' = LLVM_Builder.mk_br b l_ctd_if
            
            val _ = LLVM_Builder.open_bb b l_ctd_if
            val res = LLVM_Builder.mk_phi b dst [(r_then,l_then'), (r_else,l_else')]
          in
            SOME res
          end
        in
          val opb_if = opb_3args' opb_if_aux 
        end
        
        
        
        
              
        val op_builder_table : op_builder_table = Symtab.empty
          |> add_ll_op_xlate @{const_name ll_add} opb_arith
          |> add_ll_op_xlate @{const_name ll_sub} opb_arith
          |> add_ll_op_xlate @{const_name ll_mul} opb_arith
          |> add_ll_op_xlate @{const_name ll_udiv} opb_arith
          |> add_ll_op_xlate @{const_name ll_urem} opb_arith
          |> add_ll_op_xlate @{const_name ll_sdiv} opb_arith
          |> add_ll_op_xlate @{const_name ll_srem} opb_arith
          |> add_ll_op_xlate @{const_name ll_shl} opb_arith
          |> add_ll_op_xlate @{const_name ll_lshr} opb_arith
          |> add_ll_op_xlate @{const_name ll_ashr} opb_arith
          |> add_ll_op_xlate @{const_name ll_trunc} opb_iconv
          |> add_ll_op_xlate @{const_name ll_sext} opb_iconv
          |> add_ll_op_xlate @{const_name ll_zext} opb_iconv
          
          |> add_ll_op_xlate @{const_name ll_and} opb_arith       
          |> add_ll_op_xlate @{const_name ll_or} opb_arith
          |> add_ll_op_xlate @{const_name ll_xor} opb_arith
  
          |> add_cmp_op_xlate @{const_name ll_icmp_eq}
          |> add_cmp_op_xlate @{const_name ll_icmp_ne}
          |> add_cmp_op_xlate @{const_name ll_icmp_sle}
          |> add_cmp_op_xlate @{const_name ll_icmp_slt}
          |> add_cmp_op_xlate @{const_name ll_icmp_ule}
          |> add_cmp_op_xlate @{const_name ll_icmp_ult}
                
          |> add_op_xlate @{const_name ll_extract_fst} opb_extract_fst
          |> add_op_xlate @{const_name ll_extract_snd} opb_extract_snd
          |> add_op_xlate @{const_name ll_insert_fst} opb_insert_fst
          |> add_op_xlate @{const_name ll_insert_snd} opb_insert_snd

          |> add_op_xlate @{const_name ll_malloc} opb_malloc
          |> add_op_xlate @{const_name ll_free} opb_free
          |> add_op_xlate @{const_name ll_load} opb_load
          |> add_op_xlate @{const_name ll_store} opb_store
          
          |> add_op_xlate @{const_name ll_ofs_ptr} opb_ofs_ptr
          |> add_op_xlate @{const_name ll_gep_fst} opb_gep_fst
          |> add_op_xlate @{const_name ll_gep_snd} opb_gep_snd

          |> add_op_xlate @{const_name llc_if} opb_if
          
      
        fun bld_cmd bc dst t = let
          val (f,args) = strip_comb t
          val _ = is_Const f orelse raise TERM ("Invalid head",[f])

          val (cname,cty) = dest_Const f
          val (argTs,rty) = strip_type cty ||> dest_llM
          val ops = argTs ~~ args  (* Will fail if M-type is a function type! *)

          val opb = Symtab.lookup op_builder_table cname
        in case opb of
          NONE => opb_call bc dst rty (cname,cty) ops
        | SOME opb => opb bc dst ops
        end

      in fn bc => fn t => let
          fun bld bc @{mpat "bind ?m (\<lambda>x. ?f)"} = let
              val _ = x_T
              val resv = bld_cmd bc x m
              val bc = bctxt_add_bound resv bc
            in
              bld bc f
            end
          | bld bc @{mpat "return ?x"} = val_of_op bc x
          | bld _ t = raise TERM ("bld: bind-chain structural error",[t])
        
        in
          bld bc t
        end
      
      end        
        
      fun dest_llM_type (Type (@{type_name M},[T,@{typ unit},@{typ llvm_memory},@{typ err}])) = T
        | dest_llM_type T = raise TYPE ("dest_llM_type",[T],[])
      
      fun compile_eq state rname @{mpat "Trueprop (?lhs = ?rhs)"} = let
        val b = #builder state
        val (hdc,params) = strip_comb lhs
      
        val _ = is_Const hdc orelse raise (TERM ("llvm equation must have constant head", [hdc]))
        val _ = map (fn a => is_Var a orelse raise TERM ("arguments of llvm equation must be vars",[a])) params
        
        val rty = dest_Const hdc |> snd |> body_type |> dest_llM_type |> ty_to_llvm
        
        val param_decls = map (dest_Var #> apfst fst #> apsnd ty_to_llvm #> swap) params
        
        val param_vals = LLVM_Builder.open_proc b (SOME rty) rname param_decls
        
        val bc = bcontext |> fold bctxt_add_param (params ~~ param_vals)
        
        val retv = compile_do_block state bc rhs
        
        val _ = LLVM_Builder.mk_return b (SOME retv)
        
        val _ = LLVM_Builder.close_proc b
        
      in
        ()
      end
      | compile_eq _ _ t = raise TERM ("llvm_equation must be equation", [t])


      fun maybe_code_thm thm = 
        case Thm.prop_of thm of
          @{mpat "Trueprop (?f = _)"} => is_Const (head_of f)
        | @{mpat "?f \<equiv> _"} => is_Const (head_of f)
        | _ => false

      fun dest_code_thm thm = let
        fun err msg = raise THM ("LLVM code theorem: "^ msg,~1,[thm])
      
        fun dst lhs _ = let
          val ty = fastype_of lhs
          val _ = is_llM ty orelse err "must declare function in llM, with all parameters on LHS";
          
          val f = head_of lhs
          val _ = is_Const f orelse err "must declare constant"
          val (cname,ty) = dest_Const f
        in
          (cname,(ty,thm))
        end
      
      in
        case Thm.prop_of thm of
          @{mpat \<open>Trueprop (?lhs = ?rhs)\<close>} => dst lhs rhs
        | @{mpat \<open>?lhs \<equiv> ?rhs\<close>} => dst lhs rhs
        | _ => err "must be unconditional equation"
      end
        
      fun mk_code_tab ctxt = 
        Named_Theorems.get ctxt @{named_theorems llvm_code}
        |> filter maybe_code_thm 
        |> map (normalize_code_thm ctxt #> dest_code_thm) 
        |> (Symtab.make handle Symtab.DUP k => raise Fail ("Duplicate code theorem for " ^ k))
        

      fun new_state ctxt : state = {
        worklist = Unsynchronized.ref [],
        processed = Unsynchronized.ref Symtab.empty,
        builder = LLVM_Builder.builder (),
        ctxt = ctxt,
        tab = mk_code_tab ctxt
      }
              
      fun lookup_code_thm ({tab, ctxt, ...}:state) (cname,ty) = 
        case Symtab.lookup tab cname of
          NONE => raise Fail ("No code theorem for " ^ cname)
        | SOME (ty',thm) => (
            ty' = ty orelse raise Fail (
                "No code theorem for " ^ cname ^ " :: " ^ Syntax.string_of_typ ctxt ty 
              ^ " but for " ^ cname ^ " :: " ^ Syntax.string_of_typ ctxt ty'
            );
            thm
          )
        
      fun compile_const (s:state) (cname,ty,rname) = let
        val thm = lookup_code_thm s (cname,ty)
      in
        thm |> Thm.prop_of |> compile_eq s rname
      end
      
      fun compile_all (s:state) = 
        case fetch_next s of 
          NONE => ()
        | SOME nty => (
            compile_const s nty;
            compile_all s
          )
      
      fun register_term s (t,rname) = let
        val _ = is_Const t orelse raise TERM ("LLVM codegen expected constant",[t])
      in
        register_const s rname (dest_Const t)
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
        val _ =
          Outer_Syntax.local_theory @{command_keyword export_llvm} "generate LLVM code for constants"
            (Scan.repeat1 (Parse.term -- Scan.option (@{keyword "is"} |-- Parse.name )) -- Scan.option ((@{keyword "file"} |-- Parse.position Parse.path)) 
            >> (fn (ts,path) => fn lthy => let 
              val ts = map (apfst (Syntax.read_term lthy)) ts
              val path = Option.map (prepare_path lthy) path 
              
              val s = new_state lthy;
              val _ = map (register_term s) ts
              val _ = compile_all s 
              val _ = LLVM_Builder.string_of (#builder s) |> write_out path
            in lthy end));
      end        
      
      
    end
    
  \<close>


  named_theorems llvm_inline

  ML \<open>
    structure LLC_Lib = struct
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

  
    structure LLC_Preprocessor = struct
      open LLC_Lib
          
      (********* Normalization of code theorems *)
      
      fun cthm_inline ctxt thm = let
        val inline_thms = Named_Theorems.get ctxt @{named_theorems llvm_inline}
        val ctxt = put_simpset HOL_ss ctxt addsimps inline_thms
      in
        simplify ctxt thm
      end
      
      (*
        Bring code theorem into parseable format. To be applied after inlining, 
          immediately before parsing.
        
        Applies eta-expansion, return-expansion, and converts \<equiv> to =.
        
        May fail on non-well-formed theorems.
      *)
      fun cthm_format ctxt thm = let
        fun ensure_abs (t as Abs _) = t
          | ensure_abs t = @{mk_term "\<lambda>x. ?t x"}
      
        fun normalize_bind1 t = let
          val (f,args) = strip_comb t
          val _ = is_Const f orelse raise TERM ("format_code_thm: Invalid head",[f])
  
          val args_is_M = fastype_of f |> binder_types |> map is_llM
                  
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
    
      in
        thm 
        |> (simplify (put_simpset HOL_ss ctxt addsimps @{thms bind_laws atomize_eq}))
        |> (Conv.fconv_rule (HOLogic.Trueprop_conv (Refine_Util.f_tac_conv ctxt normalize_eq (norm_tac ctxt))))
      end
      
        
      fun cthm_normalize ctxt = cthm_inline ctxt #> cthm_format ctxt

      
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

    structure LLC_Intermediate = struct
    
      (* LLC intermediate representation. Somewhere in between Isabelle and LLVM-IR *)    
      
      datatype llc_type = TInt of int | TPtr of llc_type | TPair of llc_type*llc_type
      datatype llc_const = CInit | CInt of int  (* value *)
      datatype llc_opr = OVar of string | OConst of llc_const
      type llc_topr = llc_type * llc_opr
      datatype llc_topr' = OOOp of llc_topr | OOType of llc_type

      datatype llc_cmd = 
                 CmIf of llc_topr * llc_block * llc_block
               | CmInstr of string * llc_topr' list
               | CmCall of llc_type option * string * llc_topr list
      
          and llc_block =
                BlBind of (llc_type * string) option * llc_cmd * llc_block
              | BlReturn of llc_topr option 
    
      datatype llc_eqn =              
                EQN of llc_type option * string * (llc_type * string) list * llc_block
    
    end
    
        
    structure LLC_Compiler = struct
      open LLC_Lib LLC_Intermediate
    
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
            | _ => 
                if is_llvm_instr cname then CmInstr (cname,map (llc_parse_op' env) args)
                else CmCall (rty, ftab_lookup ftab f,map (llc_parse_op env) args)
                   
          end
        and llc_parse_block ftab env @{mpat "bind ?m (\<lambda>x. ?f)"} = 
          let
            val rty = llc_parse_vtype x_T
            val cmd = llc_parse_cmd ftab env rty m
          in
            case rty of
              SOME lty => let
                  val (x,env) = env_add_bound lty x env
                  val (blk,env) = llc_parse_block ftab env f
                in
                  (BlBind (SOME (lty,x),cmd,blk),env)
                end
            | NONE => let
                  val env = env_add_unit_bound env
                  val (blk,env) = llc_parse_block ftab env f
                in
                  (BlBind (NONE,cmd,blk),env)
                end
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
    

    structure LLC_Backend = struct
      open LLC_Lib LLC_Intermediate
    
      type vtab = LLVM_Builder.value Symtab.table
      type builder = vtab -> string -> llc_topr' list -> LLVM_Builder.T -> LLVM_Builder.value option
    
      fun llc_ty (TInt w) = LLVM_Builder.mkty_i w
        | llc_ty (TPtr ty) = LLVM_Builder.mkty_ptr (llc_ty ty)
        | llc_ty (TPair (ty1, ty2)) = LLVM_Builder.mkty_struct [llc_ty ty1, llc_ty ty2]
      
      
      fun llc_const_to_val ty CInit = LLVM_Builder.mkc_zeroinit (llc_ty ty)
        | llc_const_to_val ty (CInt v) = LLVM_Builder.mkc_i (llc_ty ty) v
      
      fun llc_op_to_val vtab (_,OVar x) = the_assert ("Variable not in vtab " ^ x) (Symtab.lookup vtab x)
        | llc_op_to_val _ (ty,OConst c) = llc_const_to_val ty c
        
      
      
      fun arith_instr_builder iname vtab dst [OOOp x1, OOOp x2] b = (
        LLVM_Builder.mk_arith_instr iname b dst (llc_op_to_val vtab x1) (llc_op_to_val vtab x2) |> SOME
      ) | arith_instr_builder _ _ _ _ _ = raise Fail "arith_instr_builder: invalid arguments"
      
      fun icmp_instr_builder cmpcode vtab dst [OOOp x1, OOOp x2] b = (
        LLVM_Builder.mk_icmp_instr cmpcode b dst (llc_op_to_val vtab x1) (llc_op_to_val vtab x2) |> SOME
      ) | icmp_instr_builder _ _ _ _ _ = raise Fail "icmp_instr_builder: invalid arguments"
      
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
      
      
      fun build_cmd b vtab dst (CmInstr ia) = build_instr b vtab dst ia
        | build_cmd b vtab dst (CmCall na) = build_call b vtab dst na
        | build_cmd b vtab dst (CmIf bte) = build_if build_block b vtab dst bte
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
       
    
    structure LLC_Driver = struct
      fun consts_to_llvm ctxt cns = let
        val cthms = LLC_Preprocessor.gather_code_thms ctxt (map fst cns)
        val fixes = map_filter (fn (_,NONE) => NONE | (cn,SOME name) => SOME (cn,name)) cns
      
        val ftab = LLC_Compiler.compute_fun_names fixes cthms
        val eqns = LLC_Compiler.parse_cthms ftab cthms
        val res = LLC_Backend.eqns_to_llvm eqns
      in
        res
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
        fun export_llvm ctxt cns path = consts_to_llvm ctxt cns |> write_out path
        
        val export_llvm_cmd = (Scan.repeat1 (Parse.term -- Scan.option (@{keyword "is"} |-- Parse.name )) -- Scan.option ((@{keyword "file"} |-- Parse.position Parse.path)) 
            >> (fn (cns,path) => fn lthy => let 
              val cns = map (apfst (Syntax.read_term lthy)) cns
              val path = Option.map (prepare_path lthy) path 
              
              val _ = export_llvm lthy cns path
            in lthy end))
        
      end

      val _ = Outer_Syntax.local_theory @{command_keyword export_llvm_new} "generate LLVM code for constants" export_llvm_cmd
    end
  \<close>
  
  prepare_code_thms [llvm_code] exp_def
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
  
  
  
  ML_val \<open>open Graph\<close>
  
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
  
    
export_llvm main_exp is main file "exp.ll"
export_llvm_new main_exp is main file "expnew.ll"

export_llvm main is main file "test2.ll"
export_llvm_new main is main file "test2new.ll"


value "run (main 0 null) llvm_empty_memory"
      
end
