theory LLVM_Shallow
imports Main  
  "List-Index.List_Index"
  "../lib/LLVM_Integer" 
  "../lib/Monad" 
  "../lib/Definition_Utils" 
  "../lib/Sep_Algebra_Add"
  "../lib/Separation"
keywords "export_llvm" :: thy_decl
begin
  

  datatype err = is_static: STATIC_ERROR string | MEM_ERROR | UNINIT_ERROR | OVERFLOW_ERROR
  hide_const (open) is_static

  datatype raw_vaitem = VA_FST | VA_SND
  type_synonym vaddr = "raw_vaitem list"
  
  datatype addr = ADDR nat nat vaddr
  
  datatype raw_ptr = RP_NULL | RP_ADDR addr
  
  datatype val = V_INT lint | V_PTR raw_ptr | V_PAIR "val \<times> val"
  
  datatype struct = S_INT nat | S_PTR | S_PAIR "struct \<times> struct"

  fun struct_of_val :: "val \<Rightarrow> struct" where
    "struct_of_val (V_INT i) = (S_INT (width i))"
  | "struct_of_val (V_PTR _) = S_PTR"
  | "struct_of_val (V_PAIR (a,b)) = S_PAIR (struct_of_val a, struct_of_val b)"
    
  fun init_val :: "struct \<Rightarrow> val" where
    "init_val (S_INT w) = V_INT (lconst w 0)"
  | "init_val (S_PTR) = V_PTR RP_NULL"
  | "init_val (S_PAIR (sa,sb)) = V_PAIR (init_val sa, init_val sb)"

  lemma of_struct_init[simp]: "struct_of_val (init_val s) = s"
    by (induction s) auto
    
  class llvm_repv  
    
  class llvm_rep = llvm_repv +
    fixes to_val :: "'a \<Rightarrow> val"
      and from_val :: "val \<Rightarrow> 'a"
      and struct_of :: "'a itself \<Rightarrow> struct"
      and init :: 'a
    assumes from_to_id[simp]: "from_val o to_val = id"
    assumes struct_of_matches[simp]: "struct_of_val (to_val x) = (struct_of TYPE('a))"
    
  begin
  
    lemma from_to_id'[simp]: "from_val (to_val x) = x" 
      using pointfree_idE[OF from_to_id] .
  
  end
  
  datatype 'a::llvm_rep ptr = PTR (the_raw_ptr: raw_ptr)
  definition null where "null = PTR RP_NULL"
  
  (*definition init :: "'a::llvm_rep" where "init \<equiv> from_val (init_val (struct_of TYPE('a)))"*)

  instance unit :: llvm_repv by standard
  
  instantiation word :: (len) llvm_rep begin
    definition "to_val w \<equiv> V_INT (lconst (len_of TYPE('a)) (uint w))"
    definition "from_val v \<equiv> case v of (V_INT i) \<Rightarrow> word_of_int (lint_to_uint i)"
    definition [simp]: "struct_of_word (_::'a word itself) \<equiv> S_INT (len_of TYPE('a))"
    definition [simp]: "init_word \<equiv> 0::'a word"
    
    instance
      apply standard
      apply (rule ext)
      apply (auto simp: from_val_word_def to_val_word_def)
      done
      
  end
  
  instantiation ptr :: (llvm_rep) llvm_rep begin
    definition "to_val \<equiv> V_PTR o ptr.the_raw_ptr"
    definition "from_val v \<equiv> case v of V_PTR p \<Rightarrow> PTR p"
    definition [simp]: "struct_of_ptr (_::'a ptr itself) \<equiv> S_PTR"
    definition [simp]: "init_ptr::'a ptr \<equiv> null"
  
    instance
      apply standard
      apply (rule ext)
      apply (auto simp: from_val_ptr_def to_val_ptr_def)
      done
      
  end
  
  instantiation prod :: (llvm_rep, llvm_rep) llvm_rep begin
    definition "to_val_prod \<equiv> V_PAIR o map_prod to_val to_val"
    definition "from_val_prod p \<equiv> case p of V_PAIR (a,b) \<Rightarrow> (from_val a, from_val b)"
    definition [simp]: "struct_of_prod (_::('a\<times>'b) itself) \<equiv> S_PAIR (struct_of TYPE('a), struct_of TYPE('b))"
    definition [simp]: "init_prod ::'a\<times>'b \<equiv> (init,init)"
    
    instance
      apply standard
      apply (rule ext)
      apply (auto simp: from_val_prod_def to_val_prod_def struct_of_prod_def)
      done
      
  end
  
    
  
  datatype heap = HEAP (the_heap: "val list option list")
  
  definition "heap_empty \<equiv> HEAP []"
  
  type_synonym 'a llM = "('a,unit,heap,err) M"

  fun load_vai :: "raw_vaitem \<Rightarrow> val \<Rightarrow> val llM" where
    "load_vai VA_FST (V_PAIR (a,b)) = return a"
  | "load_vai VA_SND (V_PAIR (a,b)) = return b" 
  | "load_vai _ _ = fail (STATIC_ERROR ''Pointer structure mismatch'')" 

  definition "load_vptr = mfold load_vai"
  
  lemma load_vptr_simps[simp]:
    "load_vptr [] = return"
    "load_vptr (a#as) v = load_vai a v \<bind> load_vptr as"
    unfolding load_vptr_def 
    by auto
    
  text \<open>Check that pointer is in bounds, and has correct type if it is accessible\<close>  
  definition check_ptr :: "'a::llvm_rep ptr \<Rightarrow> 'a::llvm_rep ptr llM" where
    "check_ptr p \<equiv> case p of
      PTR RP_NULL \<Rightarrow> return p \<comment> \<open>Null pointer always OK\<close>
    | PTR (RP_ADDR (ADDR bn idx va)) \<Rightarrow> doM {
        h \<leftarrow> get;
        let h = heap.the_heap h;
        fcheck MEM_ERROR (bn<length h); \<comment> \<open>Must point to allocated block\<close>
        let blk = h!bn;
        fcheck MEM_ERROR (blk \<noteq> None); \<comment> \<open>That has not yet been freed\<close>
        let blk = the blk;
        fcheck (STATIC_ERROR ''Zero-block'') (length blk \<noteq> 0);
        fcheck MEM_ERROR (idx \<le> length blk); \<comment> \<open>Index must be in bounds\<close>
        
        let idx = min idx (length blk - 1); \<comment> \<open>Check against structure of last entry, if one-past-end\<close>
        
        let blk = blk!idx;
        v \<leftarrow> load_vptr va blk; \<comment> \<open>The value must be loadable, 
          and have the same structure as specified by the type\<close>
        fcheck (STATIC_ERROR ''Pointer structure mismatch'') (struct_of_val v = struct_of TYPE('a));
        return p
    }"
  
  
  
  definition raw_malloc :: "val \<Rightarrow> nat \<Rightarrow> _ llM"
    where "raw_malloc vi n \<equiv> doM {
      h \<leftarrow> get;
      let h = heap.the_heap h;
      fcheck MEM_ERROR (n>0);
      set (HEAP (h @ [Some (replicate n vi)]));
      return (length h)
    }"
  
  definition ll_malloc :: "'a::llvm_rep itself \<Rightarrow> _::len word \<Rightarrow> 'a ptr llM" where
    "ll_malloc TYPE('a) n = doM {
      bn \<leftarrow> raw_malloc (to_val (init::'a)) (unat n);
      check_ptr (PTR (RP_ADDR (ADDR bn 0 [])))
    }" 
    
  definition raw_free :: "nat \<Rightarrow> unit llM"
    where "raw_free bn \<equiv> doM {
      h \<leftarrow> get;
      let h = heap.the_heap h;
      fcheck MEM_ERROR (bn<length h);
      fcheck MEM_ERROR (h!bn \<noteq> None);
      set (HEAP (h[bn:=None]))
    }"
    
    
  definition ptr_to_addr :: "'a::llvm_rep ptr \<Rightarrow> addr llM" where
    "ptr_to_addr p \<equiv> doM {
      check_ptr p;
      case the_raw_ptr p of
        RP_NULL \<Rightarrow> fail MEM_ERROR
      | RP_ADDR addr \<Rightarrow> return addr
    }"
    
  definition ptr_to_addr' :: "'a::llvm_rep ptr \<Rightarrow> _ llM" where
    "ptr_to_addr' ptr \<equiv> doM {
      addr \<leftarrow> ptr_to_addr ptr;
      case addr of ADDR bn idx va \<Rightarrow> return (bn,idx,va)
    }"
    
    
  definition ll_free :: "'a::llvm_rep ptr \<Rightarrow> unit llM" 
    where "ll_free p \<equiv> doM {
      (bn,idx,va) \<leftarrow> ptr_to_addr' p;
      fcheck MEM_ERROR (idx=0 \<and> va=[]); \<comment> \<open>Only base pointers can be freed\<close>
      raw_free bn
    }"
    
    
  fun upd_vptr :: "val \<Rightarrow> vaddr \<Rightarrow> val \<Rightarrow> val llM" where
    "upd_vptr ov [] v = doM {
      fcheck (STATIC_ERROR ''same-struct'') (struct_of_val ov = struct_of_val v);
      return v
    }"
  | "upd_vptr (V_PAIR (a,b)) (VA_FST#ptr) v = doM {
      a \<leftarrow> upd_vptr a ptr v;
      return (V_PAIR (a,b))
    }"  
  | "upd_vptr (V_PAIR (a,b)) (VA_SND#ptr) v = doM {
      b \<leftarrow> upd_vptr b ptr v;
      return (V_PAIR (a,b))
    }"  
  | "upd_vptr _ _ _ = fail (STATIC_ERROR ''Pointer structure mismatch'')"

    
  definition "raw_block_size bn \<equiv> doM {
    h \<leftarrow> get;
    let h = heap.the_heap h;
    fcheck MEM_ERROR (bn<length h); 
    let blk = h!bn;
    fcheck MEM_ERROR (blk \<noteq> None);
    let blk = the blk;
    return (length blk)
  }"
  
  fun raw_load where "raw_load (ADDR bn idx va) = doM {
    h \<leftarrow> get;
    let h = heap.the_heap h;
    fcheck MEM_ERROR (bn<length h); 
    let blk = h!bn;
    fcheck MEM_ERROR (blk \<noteq> None);
    let blk = the blk;
    fcheck MEM_ERROR (idx < length blk);
    let blk = blk!idx;
    load_vptr va blk
  }"
    
  definition ll_load :: "'a::llvm_rep ptr \<Rightarrow> 'a llM" where
    "ll_load p \<equiv> doM {
      addr \<leftarrow> ptr_to_addr p;
      v \<leftarrow> raw_load addr;
      return (from_val v)
    }"

  fun raw_store where "raw_store (ADDR bn idx va) v = doM {
    h \<leftarrow> get;
    let h = heap.the_heap h;
    fcheck MEM_ERROR (bn<length h); 
    let blk = h!bn;
    fcheck MEM_ERROR (blk \<noteq> None);
    let blk = the blk;
    fcheck MEM_ERROR (idx < length blk);
    let val = blk!idx;
    val \<leftarrow> upd_vptr val va v;
    let blk = list_update blk idx val;
    let blk = Some blk;
    let h = list_update h bn blk;
    set (HEAP h)
  }"
          
  definition ll_store :: "'a::llvm_rep \<Rightarrow> 'a ptr \<Rightarrow> unit llM" where
    "ll_store v p \<equiv> doM {
      addr \<leftarrow> ptr_to_addr p;
      raw_store addr (to_val v)
    }"
  
 
    
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
  
  
  definition "ll_add \<equiv> op_lift_arith2' (+)"
  definition "ll_sub \<equiv> op_lift_arith2' (-)"
  definition "ll_mul \<equiv> op_lift_arith2' ( * )"
  definition "ll_udiv \<equiv> op_lift_arith2' (div)"
  definition "ll_urem \<equiv> op_lift_arith2' (mod)"
  definition "ll_sdiv \<equiv> op_lift_arith2 sdivrem_ovf (div\<^sub>s)"
  definition "ll_srem \<equiv> op_lift_arith2 sdivrem_ovf (rem\<^sub>s)"
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

    (bn,idx,va) \<leftarrow> ptr_to_addr' p;
    let idx = int idx + sint ofs;
    blen \<leftarrow> raw_block_size bn;
    
    fcheck MEM_ERROR (va=[]);
    
    \<comment> \<open>Enforce inbounds semantics\<close>
    fcheck MEM_ERROR (0\<le>idx);
    let idx = nat idx;
    fcheck MEM_ERROR (idx \<le> blen);
  
    check_ptr (PTR (RP_ADDR (ADDR bn idx va)))
  }"

  definition ll_gep_fst :: "('a::llvm_rep \<times> 'b::llvm_rep) ptr \<Rightarrow> 'a ptr llM" where "ll_gep_fst p = doM {
    (bn,idx,va) \<leftarrow> ptr_to_addr' p;
    let va = va@[VA_FST];
    check_ptr (PTR (RP_ADDR (ADDR bn idx va)))
  }"

  definition ll_gep_snd :: "('a::llvm_rep \<times> 'b::llvm_rep) ptr \<Rightarrow> 'b ptr llM" where "ll_gep_snd p = doM {
    (bn,idx,va) \<leftarrow> ptr_to_addr' p;
    let va = va@[VA_SND];
    check_ptr (PTR (RP_ADDR (ADDR bn idx va)))
  }"

  definition "to_bool \<equiv> lint_to_bool o word_to_lint"
  lemma to_bool_eq[simp]: "to_bool (w::1 word) \<longleftrightarrow> w\<noteq>0"
    unfolding to_bool_def word_to_lint_def
    apply (clarsimp simp: ltrue_def)
    apply transfer
    by (auto; auto simp: Bit_eq_0_iff)
    
  
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
    
      fun dest_llM (Type (@{type_name M},[T,@{typ unit},@{typ heap},@{typ err}])) = T
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
        | const_to_llvm (t as @{mpat "0::_ word"}) = dest_word_const t |> uncurry LLVM_Builder.mkc_iw
        | const_to_llvm (t as @{mpat "1::_ word"}) = dest_word_const t |> uncurry LLVM_Builder.mkc_iw
        | const_to_llvm (t as @{mpat "numeral _::_ word"}) = dest_word_const t |> uncurry LLVM_Builder.mkc_iw
        | const_to_llvm t = raise TERM ("Cannot convert constant to LLVM",[t])
        
      
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
            val _ = LLVM_Builder.mk_br b l_ctd_if
            
            val _ = LLVM_Builder.open_bb b l_else
            val r_else = compile_do_block state bc (snd op3)
            val _ = LLVM_Builder.mk_br b l_ctd_if
            
            val _ = LLVM_Builder.open_bb b l_ctd_if
            val res = LLVM_Builder.mk_phi b dst [(r_then,l_then), (r_else,l_else)]
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
        
      fun dest_llM_type (Type (@{type_name M},[T,@{typ unit},@{typ heap},@{typ err}])) = T
        | dest_llM_type T = raise TYPE ("dest_llM_type",[T],[])
      
      fun compile_eq state rname @{mpat "Trueprop (?lhs = ?rhs)"} = let
        val b = #builder state
        val (hdc,params) = strip_comb lhs
      
        val _ = is_Const hdc orelse raise (TERM ("llvm equation must have constant head", [hdc]))
        val _ = map (fn a => is_Var a orelse raise TERM ("arguments of llvm equation must be vars",[a])) params
        
        val rty = dest_Const hdc |> snd |> body_type |> dest_llM_type |> ty_to_llvm
        
        val param_decls = map (dest_Var #> apfst fst #> apsnd ty_to_llvm #> swap) params
        
        val param_vals = LLVM_Builder.open_proc b rty rname param_decls
        
        val bc = bcontext |> fold bctxt_add_param (params ~~ param_vals)
        
        val retv = compile_do_block state bc rhs
        
        val _ = LLVM_Builder.mk_return b retv
        
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

  prepare_code_thms [llvm_code] exp_def
  definition [llvm_code]: "test2 (n::32 word) \<equiv> doM {
    n \<leftarrow> ll_add n 42;
    p \<leftarrow> ll_malloc TYPE(16 word) n;
    p \<leftarrow> ll_ofs_ptr p (5::32 word);
    ll_store 42 p;
    r \<leftarrow> ll_load p; 
    return r  
  }"
  
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
export_llvm main is main file "test2.ll"

(*
  TODO: Integrate prepare_code_thms with code exporter!
*)


fun va_dep :: "vaddr \<Rightarrow> vaddr \<Rightarrow> bool" where
  "va_dep [] _ \<longleftrightarrow> True"
| "va_dep _ [] \<longleftrightarrow> True"  
| "va_dep (x#xs) (y#ys) \<longleftrightarrow> x=y \<and> va_dep xs ys"

lemma va_dep_add_simp[simp]: "va_dep xs [] \<longleftrightarrow> True" by (cases xs) auto

lemma va_dep_alt: 
  "va_dep xs ys \<longleftrightarrow> take (min (length xs) (length ys)) xs = take (min (length xs) (length ys)) ys"
  by (induction xs ys rule: va_dep.induct) auto

lemma va_dep_refl[simp, intro!]: "va_dep xs xs" by (induction xs) auto

lemma va_dep_sym[sym]: "va_dep xs ys \<Longrightarrow> va_dep ys xs"
  unfolding va_dep_alt by (auto simp: min_def split: if_splits)

datatype prim_val = PV_INT lint | PV_PTR raw_ptr  
  
typedef sep_val = "{m :: vaddr \<rightharpoonup> prim_val . \<forall>x\<in>dom m. \<forall>y\<in>dom m. va_dep x y \<longrightarrow> x=y}"
  by auto
  
setup_lifting type_definition_sep_val  

definition "m_dep m1 m2 \<equiv> \<exists>x\<in>dom m1. \<exists>y\<in>dom m2. va_dep x y"

lemma m_dep_imp_dom_overlap: "dom m1 \<inter> dom m2 \<noteq> {} \<Longrightarrow> m_dep m1 m2"
  by (auto simp: m_dep_def)
  
lemma m_dep_sym: "m_dep m1 m2 \<Longrightarrow> m_dep m2 m1"  
  by (auto simp: m_dep_def dest: va_dep_sym)
  
lemma m_dep_empty[simp]: 
  "\<not>m_dep x Map.empty"  
  "\<not>m_dep Map.empty x"  
  by (auto simp: m_dep_def)
  
lemma m_dep_same[simp]: "m_dep x x \<longleftrightarrow> x\<noteq>Map.empty"
  apply (auto)
  apply (force simp: m_dep_def)
  done
  
  
instantiation sep_val :: unique_zero_sep_algebra begin
  lift_definition sep_disj_sep_val :: "sep_val \<Rightarrow> sep_val \<Rightarrow> bool" is "Not oo m_dep" .

  lift_definition plus_sep_val :: "sep_val \<Rightarrow> sep_val \<Rightarrow> sep_val" is "\<lambda>m1 m2. if m_dep m1 m2 then Map.empty else m1++m2"
    apply (auto split: if_splits simp: m_dep_def)
    apply blast
    apply blast
    by (meson domI va_dep_sym)

  lift_definition zero_sep_val :: "sep_val" is "Map.empty" by auto
    
  instance
    apply standard
    apply (determ transfer; auto simp: m_dep_def)
    apply (determ transfer; auto simp: m_dep_def dom_def; metis option.distinct(1) va_dep_sym)
    apply (determ transfer; auto simp: m_dep_def)
    apply (determ transfer; auto intro: m_dep_imp_dom_overlap  simp: map_add_comm m_dep_sym)
    apply (determ transfer; auto; metis UnE dom_map_add m_dep_def)
    apply (determ transfer; auto simp: m_dep_def domI)
    apply (determ transfer; simp)
    done
end    
    

lift_definition sep_cell :: "prim_val \<Rightarrow> sep_val" is "\<lambda>v. [[]\<mapsto>v]" by auto

definition "map_prefix p v \<equiv> \<lambda>p'#va \<Rightarrow> if p'=p then v va else None | _ \<Rightarrow> None"

lemma dom_map_prefix_conv[simp]: "dom (map_prefix p v) = (#) p ` dom v"
  by (auto 0 3 simp: map_prefix_def split: list.splits if_splits)

lift_definition sep_prefix :: "raw_vaitem \<Rightarrow> sep_val \<Rightarrow> sep_val" is map_prefix by auto auto


fun val_\<alpha> where
  "val_\<alpha> (V_INT x) = sep_cell (PV_INT x)"  
| "val_\<alpha> (V_PTR x) = sep_cell (PV_PTR x)"  
| "val_\<alpha> (V_PAIR (x1,x2)) = sep_prefix VA_FST (val_\<alpha> x1) + sep_prefix VA_SND (val_\<alpha> x2)"

lemma prefix_diff_dj[simp]: "i\<noteq>j \<Longrightarrow> sep_prefix i x ## sep_prefix j y"
  apply transfer apply (auto split: if_splits list.splits simp: m_dep_def) done

lemma prefix_same_dj_iff[simp]: "sep_prefix i x1 ## sep_prefix i x2 \<longleftrightarrow> x1##x2"
  apply transfer
  apply (auto simp: m_dep_def)
  done

lemma prefix_dj_iff: "sep_prefix i x ## sep_prefix j y \<longleftrightarrow> (i\<noteq>j \<or> x##y)"
  by (cases "i=j") auto
  
  
fun sep_prefixl where
  "sep_prefixl [] v = v"
| "sep_prefixl (i#is) v = sep_prefix i (sep_prefixl is v)"

definition "at_val a v \<equiv> sep_prefixl a (val_\<alpha> v)"

lemma at_val_simps[simp]:
  "at_val [] v = val_\<alpha> v"
  "at_val (i#is) v = sep_prefix i (at_val is v)"  
  by (auto simp: at_val_def)

definition "list_\<alpha> \<alpha> l i = (if i<length l then \<alpha> (l!i) else (0::_::sep_algebra))"

fun option_\<alpha> where
  "option_\<alpha> \<alpha> (Some x) = \<alpha> x" | "option_\<alpha> \<alpha> None = (0::_::sep_algebra)"

(*definition "option_\<alpha> \<alpha> v = (case v of Some x \<Rightarrow> \<alpha> x | None \<Rightarrow> (0::_::sep_algebra))"*)

definition at_idx :: "nat \<Rightarrow> 'a::sep_algebra \<Rightarrow> nat \<Rightarrow> 'a" where "at_idx i v = fun_upd (\<lambda>_. 0) i v"

lemma at_idx_disj_iff: "at_idx i v ## at_idx j w \<longleftrightarrow> i\<noteq>j \<or> v##w"
  by (auto simp: at_idx_def sep_algebra_simps sep_disj_fun_def)

lemma at_idx_disj_simps[simp]: 
  "at_idx i v ## at_idx i w \<longleftrightarrow> v##w"
  "i\<noteq>j \<Longrightarrow> at_idx i v ## at_idx j w"
  by (auto simp: at_idx_disj_iff)
  
  


type_synonym abs_heap = "nat \<Rightarrow> (nat \<Rightarrow> sep_val) \<times> nat tsa_opt"

definition block_\<alpha>vs :: "val list \<Rightarrow> nat \<Rightarrow> sep_val" where "block_\<alpha>vs = list_\<alpha> val_\<alpha>"
definition block_\<alpha>t :: "val list \<Rightarrow> nat tsa_opt" where "block_\<alpha>t = TRIV o length"
definition "block_\<alpha> blk \<equiv> (block_\<alpha>vs blk, block_\<alpha>t blk)"
definition heap_\<alpha> :: "heap \<Rightarrow> abs_heap" where "heap_\<alpha> \<equiv> list_\<alpha> (option_\<alpha> block_\<alpha>) o the_heap"

definition llvm_wp :: "'a llM \<Rightarrow> ('a \<Rightarrow> heap \<Rightarrow> bool) \<Rightarrow> heap \<Rightarrow> bool"
  where "llvm_wp (c::_ llM) Q s \<equiv> mwp (run c s) bot bot bot Q"

interpretation conc_heap heap_\<alpha> "\<lambda>_. True" llvm_wp
  apply standard
  apply (auto simp: llvm_wp_def elim!: mwp_cons)
  done

definition at_addr :: "addr \<Rightarrow> val \<Rightarrow> abs_heap" where "at_addr \<equiv> \<lambda>ADDR bi i va \<Rightarrow> \<lambda>v. at_idx bi (at_idx i (at_val va v),0)"
definition at_tag :: "nat \<Rightarrow> nat \<Rightarrow> abs_heap" where "at_tag bi s \<equiv> at_idx bi (0,TRIV s)"

definition pto :: "'a \<Rightarrow> 'a::llvm_rep ptr \<Rightarrow> abs_heap \<Rightarrow> bool" 
  where "pto v p \<equiv> case p of PTR (RP_ADDR a) \<Rightarrow> EXACT (at_addr a (to_val v)) | _ \<Rightarrow> sep_false"
  
definition "alloc_tag sz p \<equiv> case p of PTR (RP_ADDR (ADDR bi 0 [])) \<Rightarrow> \<up>(sz\<noteq>0) ** EXACT (at_tag bi sz) | _ \<Rightarrow> sep_false"

definition "is_valbase_ptr \<equiv> \<lambda>PTR (RP_ADDR (ADDR bi i [])) \<Rightarrow> True | _ \<Rightarrow> False"

definition idx_ptr :: "'a::llvm_rep ptr \<Rightarrow> nat \<Rightarrow> 'a ptr" 
  where "idx_ptr \<equiv> \<lambda>PTR (RP_ADDR (ADDR bi i [])) \<Rightarrow> \<lambda>j. PTR (RP_ADDR (ADDR bi (i + j) []))"

definition "is_array xs p \<equiv> \<up>(is_valbase_ptr p) ** \<And>* map_index (\<lambda>i x. pto x (idx_ptr p i)) xs"

lemma list_\<alpha>_snoc_disj[simp, intro!]: "list_\<alpha> \<alpha> xs ## at_idx (length xs) (\<alpha> x)"
  unfolding list_\<alpha>_def at_idx_def
  by (auto simp: sep_algebra_simps sep_disj_fun_def)

lemma list_\<alpha>_snoc_conv: "list_\<alpha> \<alpha> (xs@[x]) = list_\<alpha> \<alpha> xs + at_idx (length xs) (\<alpha> x)"
  unfolding list_\<alpha>_def at_idx_def
  by (rule ext) auto

lemma 
  heap_\<alpha>_snoc_conv: "heap_\<alpha> (HEAP (h @ [b])) = heap_\<alpha> (HEAP h) + at_idx (length h) (option_\<alpha> block_\<alpha> b)"
  and heap_\<alpha>_snoc_disj[simp, intro!]: "heap_\<alpha> (HEAP h) ## at_idx (length h) (option_\<alpha> block_\<alpha> b)"
  by (auto simp: heap_\<alpha>_def list_\<alpha>_snoc_conv)

  
lemma map_index'_replicate_conv: "map_index' i\<^sub>0 f (replicate n x) = map (\<lambda>i. f i x) [i\<^sub>0..<i\<^sub>0+n]"
  apply (induction n arbitrary: i\<^sub>0)
  apply (auto simp: upt_rec)
  done
  
  
lemma sep_list_conj_EXACT_conv: "(sep_distinct (map f xs)) \<Longrightarrow> (\<And>*map (\<lambda>x. EXACT (f x)) xs) = EXACT (sepsum_list (map f xs))"  
  apply (induction xs)
  apply (auto del: ext intro!: ext elim: sep_conjE simp: sep_algebra_simps)
  apply (rule sep_conjI[OF _ _ _ refl]; simp)
  done
  
lemma disj_sepsum_set_conv: "sep_distinct ys \<Longrightarrow> x ## sepsum_list ys \<longleftrightarrow> (\<forall>y\<in>List.set ys. x##y)"
  by (induction ys) auto
  
lemma sep_distinct_alt: "sep_distinct xs \<longleftrightarrow> (\<forall>i<length xs. \<forall>j<length xs. i\<noteq>j \<longrightarrow> xs!i ## xs!j)"
  apply (induction xs)
  apply (auto simp: disj_sepsum_set_conv sep_algebra_simps nth_Cons all_set_conv_all_nth split: nat.split)
  done
  
thm EXACT_split[symmetric]
  
lemma at_idx_0[simp]: "at_idx i 0 = 0"  
  by (rule ext) (auto simp: at_idx_def)
 
lemma at_idx_add: "at_idx i v + at_idx i w = at_idx i (v+w)"  
  by (rule ext) (auto simp: at_idx_def)
  
lemma at_idx_sum_list: "sepsum_list (map (\<lambda>x. at_idx i (f x)) xs) = at_idx i (sepsum_list (map f xs))"  
  by (induction xs) (auto simp: at_idx_add)
  
lemma at_idx_inj[simp]: 
  "at_idx i v = at_idx i w \<longleftrightarrow> v=w"
  by (auto simp: at_idx_def dest: fun_upd_eqD)
  
lemma pair_sepsum_list_map: "sepsum_list (map (\<lambda>x. (f x, g x)) xs) = (sepsum_list (map f xs), sepsum_list (map g xs))"
  by (induction xs) (auto simp: sep_algebra_simps)

lemma pair_sepsum_list_map_index: "sepsum_list (map_index' i\<^sub>0 (\<lambda>i x. (f i x, g i x)) xs) 
  = (sepsum_list (map_index' i\<^sub>0 f xs), sepsum_list (map_index' i\<^sub>0 g xs))"
  by (induction xs arbitrary: i\<^sub>0) (auto simp: sep_algebra_simps)
  
  
    
lemma sepsum_list_const[simp]: "sepsum_list (map (\<lambda>_. 0) xs) = 0"  
  by (induction xs) (auto simp: sep_algebra_simps)
  
lemma at_idx_apply: "at_idx i x j = (if i=j then x else 0)"  by (auto simp: at_idx_def)
lemma at_idx_apply_simps[simp]: 
  "at_idx i x i = x"  
  "i\<noteq>j \<Longrightarrow> at_idx i x j = 0"
  by (auto simp: at_idx_apply)

lemma nth_map_index': "i<length xs \<Longrightarrow> map_index' i\<^sub>0 f xs ! i = f (i+i\<^sub>0) (xs!i)"  
  apply (induction xs arbitrary: i i\<^sub>0)
  apply (auto simp: nth_Cons')
  done

lemma sep_distinct_map_index'_alt: "sep_distinct (map_index' i\<^sub>0 f xs) 
  \<longleftrightarrow> (\<forall>i<length xs. \<forall>j<length xs. i\<noteq>j \<longrightarrow> f (i+i\<^sub>0) (xs!i) ## f (j+i\<^sub>0) (xs!j))"  
  by (auto simp: sep_distinct_alt nth_map_index')
  
lemma list_conj_map_index_EXACT_conv:
  assumes "\<And>i j x y. \<lbrakk> i\<noteq>j \<rbrakk> \<Longrightarrow> f i x ## f j y"
  shows "(\<And>* map_index' i\<^sub>0 (\<lambda>i x. EXACT (f i x)) xs) = EXACT (sepsum_list (map_index' i\<^sub>0 f xs))"
proof -
  show ?thesis
    apply (induction xs arbitrary: i\<^sub>0)
    apply (auto del: ext intro!: ext simp: sep_conj_def disj_sepsum_set_conv)
    apply (subst disj_sepsum_set_conv)
    apply (auto simp add: sep_distinct_map_index'_alt algebra_simps assms)
    done
    
qed  

(*  
lemma sep_list_conj_map_idx_EXACT_conv: "(\<And>* (map_index (\<lambda>i x. EXACT (at_idx i (f x))) xs)) = EXACT (list_\<alpha> f xs)"  
proof -
  have "\<And>* map_index' i\<^sub>0 (\<lambda>i x. EXACT (at_idx i (f x))) xs = EXACT (\<lambda>i. if i\<^sub>0 \<le> i \<and> i < length xs + i\<^sub>0 then f (xs ! (i - i\<^sub>0)) else 0)"  
    for i\<^sub>0
    apply (induction xs arbitrary: i\<^sub>0)
    subgoal
      by (auto simp add: sep_algebra_simps intro!: ext)
    subgoal
      apply simp
      apply (subst EXACT_split[symmetric])
      apply (simp add: sep_disj_fun_def at_idx_apply)
      apply (auto simp: sep_algebra_simps nth_Cons')
      done
    done
  then show ?thesis
    unfolding list_\<alpha>_def
    by auto
qed
*)
  
lemma sepsum_map_at_idx_conv: "sepsum_list (map_index (\<lambda>i x. at_idx i (f x)) xs) = list_\<alpha> f xs"
proof -

  have "sepsum_list (map_index' i\<^sub>0 (\<lambda>i x. at_idx i (f x)) xs) = (\<lambda>i. if i\<^sub>0 \<le> i \<and> i < length xs + i\<^sub>0 then f (xs ! (i - i\<^sub>0)) else 0)"
    for i\<^sub>0
    apply (induction xs arbitrary: i\<^sub>0)
    subgoal by (rule ext) (auto)
    subgoal by (auto simp: nth_Cons')
    done
  
  then show ?thesis
    unfolding list_\<alpha>_def
    by auto
qed

find_theorems sepsum_list map

lemma sepsum_list_rep0[simp]: "sepsum_list (replicate n 0) = 0"
  by (induction n) auto

lemma list_\<alpha>_replicate_conv: "list_\<alpha> \<alpha> (replicate n x) = (\<lambda>i. if i<n then \<alpha> x else 0)"  
  by (auto simp: list_\<alpha>_def)
  
lemma sepsum_map_at_idx_const_conv: "sepsum_list (map_index (\<lambda>i x. at_idx bi (f i x)) xs) = at_idx bi (sepsum_list (map_index f xs))"
  apply (subst map_map_index[where g = "at_idx bi", symmetric])
  apply (subst at_idx_sum_list)
  by auto
  
  
lemma 
  assumes "0<n"  
  shows "htriple \<box> (ll_malloc TYPE ('a::llvm_rep) n) (\<lambda>r. is_array (replicate (unat n) init) r ** alloc_tag (unat n) r)"
proof -
  
  have 1: "(is_array (replicate (unat n) (init::'a)) (PTR (RP_ADDR (ADDR (length (the_heap h)) 0 []))) 
      \<and>* alloc_tag (unat n) (PTR (RP_ADDR (ADDR (length (the_heap h)) 0 []))) 
      \<and>* F)
      (heap_\<alpha> h + at_idx (length (the_heap h)) (option_\<alpha> block_\<alpha> (Some (replicate (unat n) (to_val (init::'a))))))"
      (is "(?A ** ?T ** ?H) (?h + ?blk)")
    if "F (heap_\<alpha> h)" for F h
  proof -
    from assms have [simp]: "0 < unat n" by (simp add: word_less_nat_alt)
  
    have "(?A ** ?T) ?blk" 
      apply (simp 
        add: is_array_def alloc_tag_def is_valbase_ptr_def idx_ptr_def pto_def at_addr_def sep_algebra_simps
        add: pred_lift_extract_simps sepsum_map_at_idx_const_conv
        add: list_conj_map_index_EXACT_conv) 
        
      apply (subst EXACT_split[symmetric])
      apply (auto simp: at_tag_def sep_algebra_simps pair_sepsum_list_map_index) []
      apply (auto  
        simp: at_tag_def sep_algebra_simps pair_sepsum_list_map_index at_idx_add sepsum_map_at_idx_conv
        simp: list_\<alpha>_replicate_conv
        simp: block_\<alpha>_def block_\<alpha>vs_def block_\<alpha>t_def
        )
      done
    from sep_conjI[of "?A ** ?T", OF this, of F, OF that _ refl] show ?thesis
      apply (cases h) 
      apply (simp add: sep_algebra_simps del: option_\<alpha>.simps)
      done
  qed

  show ?thesis
    apply vcg
    unfolding llvm_wp_def ll_malloc_def raw_malloc_def check_ptr_def POSTCOND_def using assms
    apply (auto simp: run_simps word_less_nat_alt)
    apply (simp add: STATE_def heap_\<alpha>_snoc_conv 1 del: option_\<alpha>.simps)
    done

qed    


lemma plus_upd_zero_split: "fun_upd (f+g) x 0 = (f(x:=0)) + (g(x:=0))" by auto

find_theorems "fun_upd" at_idx

lemma complete_idx_split:
  fixes h :: "nat \<Rightarrow> (_::unique_zero_sep_algebra)"
  assumes "(EXACT (at_idx bi v) ** F) h"
  assumes "\<And>w. v##w \<Longrightarrow> h bi = v+w \<Longrightarrow> w=0"
  shows "h bi = v" "F (h(bi:=0))"
  using assms  
  apply (auto simp: sep_conj_def sep_algebra_simps sep_disj_fun_def at_idx_def plus_upd_zero_split split: if_splits)
  by (metis at_idx_0 at_idx_def fun_upd_idem_iff sep_add_commute sep_add_zero sep_disj_commuteI)
  

lemma extract_at_idx: 
  assumes "(EXACT (at_idx bi v) ** F) (list_\<alpha> \<alpha> h)"
  assumes "v\<noteq>(0::_::unique_zero_sep_algebra)"
  shows "\<exists>v'. v##v' \<and> bi<length h \<and> \<alpha> (h!bi) = v + v'"
  using assms
  by (auto 
    simp: sep_conj_def sep_disj_fun_def at_idx_apply list_\<alpha>_def fun_eq_iff 
      split: if_splits
    dest!: spec[where x=bi])
  
lemma sep_cell_complete[simp]: 
  "av ## sep_cell x \<longleftrightarrow> av=0"  
  "sep_cell x ## av \<longleftrightarrow> av=0"  
  apply (determ transfer; auto simp: m_dep_def)+
  done

lemma map_prefix_eq_empty_iff[simp]: 
  "map_prefix i m = Map.empty \<longleftrightarrow> m = Map.empty" by (auto simp flip: dom_eq_empty_conv)
      
lemma sep_prefix_eq_0_iff[simp]: "sep_prefix i v = 0 \<longleftrightarrow> v=0"  
  by transfer auto
  
find_theorems sep_prefix 0  

  
fun vaddr_cases where
  "vaddr_cases [] = ()" | "vaddr_cases (VA_FST#_) = ()" | "vaddr_cases (VA_SND#_) = ()"
  

  
lemma dom_spec: "\<forall>x\<in>dom m. P x \<Longrightarrow> m x = Some y \<Longrightarrow> P x" by auto
  
find_theorems "_:dom _"

lemma map_prefix_singleton[simp]: "map_prefix i [a \<mapsto> x] = [i#a \<mapsto> x]"
  by (auto simp: map_prefix_def split: list.split)

lemma m_eq_singleton_iff: "m = [k\<mapsto>v] \<longleftrightarrow> (dom m = {k} \<and> m k = Some v)"  
  using fun_upd_same by fastforce
  
lemma map_prefix_fst_snd_indep[simp]: "\<not>m_dep (map_prefix VA_FST m\<^sub>1) (map_prefix VA_SND m\<^sub>2)"  
  by (auto simp: m_dep_def)
  
lemma map_prefix_split_lemma: "av [] = None 
  \<Longrightarrow> av = map_prefix VA_FST ((av \<circ>\<circ> (#)) VA_FST) ++ map_prefix VA_SND ((av \<circ>\<circ> (#)) VA_SND)"  
  apply (rule ext)
  using raw_vaitem.exhaust
  by (auto simp: map_prefix_def map_add_def split: list.split option.split)
  
lemma sep_val_cases:  
  obtains pv where "av = sep_cell pv"
        | av\<^sub>1 av\<^sub>2 where "av = sep_prefix VA_FST av\<^sub>1 + sep_prefix VA_SND av\<^sub>2"
proof (cases "av=0")
  case True with that(2) show ?thesis by auto
next
  case False
  hence "(\<exists>pv. av = sep_cell pv) \<or> (\<exists>av\<^sub>1 av\<^sub>2. av = sep_prefix VA_FST av\<^sub>1 + sep_prefix VA_SND av\<^sub>2)"
    apply transfer
    subgoal for av
      apply (cases "[]\<in>dom av")
      proof goal_cases
        case 1
        show ?thesis 
          apply (rule disjI1)
          using 1
          by (auto simp: m_eq_singleton_iff domI)
      next
        case 2
        show ?thesis
          apply (rule disjI2)
          apply (rule bexI[where x="av o (#)VA_FST"])
          apply (rule bexI[where x="av o (#)VA_SND"])
          using 2
          apply (auto simp: map_prefix_split_lemma)
          apply (auto simp: map_add_def fun_eq_iff map_prefix_def split: option.splits list.splits)
          apply (meson domI list.inject va_dep.simps(3))
          apply (meson domI list.inject va_dep.simps(3))
          done
      qed
      done
  thus ?thesis using that by auto    
qed    
  
(*  
lemma sep_val_cases: 
  obtains  (0) "av = 0" 
          | (cell) pv where "av=sep_cell pv" 
          | (prefix) i av\<^sub>1 av\<^sub>2 where "sep_prefix i av\<^sub>1##av\<^sub>2" "av\<^sub>1\<noteq>0" "av = sep_prefix i av\<^sub>1 + av\<^sub>2"
  apply (cases "av=0"; cases av rule: sep_val_cases)
  apply auto apply force 
*)  

find_theorems sep_cell  
  
lemma val_complete_aux:
  assumes 
    "xa\<noteq>0" "xb\<noteq>0"
    "\<And>av. av ## xa = (av = 0)" "\<And>av. av ## xb = (av = 0)"
    "av ## sep_prefix VA_FST (xa)" "av ## sep_prefix VA_SND (xb)"
  shows "av = 0"
  using assms
  by (cases av rule: sep_val_cases) auto

lemma sep_cell_ne0[simp]: "sep_cell pv \<noteq> 0"
  by transfer auto
  
lemma val_\<alpha>_ne0[simp]: "val_\<alpha> v \<noteq> 0"  
  by (induction v) auto
  
    
lemma val_\<alpha>_complete1: "av ## val_\<alpha> v \<longleftrightarrow> av = 0"    
  apply (induction v arbitrary: av)
  apply (auto simp: )
  apply (rule val_complete_aux; assumption?)
  apply auto
  done

lemma val_\<alpha>_complete2: "val_\<alpha> v ## av \<longleftrightarrow> av = 0"    
  by (simp add: sep_disj_commute val_\<alpha>_complete1)

lemmas val_\<alpha>_complete[simp] = val_\<alpha>_complete1 val_\<alpha>_complete2         
  

lemma list_\<alpha>_eq_conv: 
  "length l\<^sub>1 = length l\<^sub>2 \<Longrightarrow> list_\<alpha> \<alpha>\<^sub>1 l\<^sub>1 = list_\<alpha> \<alpha>\<^sub>2 l\<^sub>2 \<longleftrightarrow> (\<forall>i < length l\<^sub>2. \<alpha>\<^sub>1 (l\<^sub>1!i) = \<alpha>\<^sub>2 (l\<^sub>2!i))"
  unfolding list_\<alpha>_def by (auto simp: fun_eq_iff)

lemma sep_cell_inj[simp]: "sep_cell pv\<^sub>1 = sep_cell pv\<^sub>2 \<longleftrightarrow> pv\<^sub>1=pv\<^sub>2"  
  by (determ transfer) (auto simp: fun_eq_iff)

thm sep_cell_complete  
    
lemma eq_sum_disj_cases[consumes 2]:
  fixes a b c :: "'a::unique_zero_sep_algebra"
  assumes "a = b+c" "b##c" 
  obtains (zero) "a=0" "b=0" "c=0" | (inter1) "\<not>(a ## b)" | (inter2) "\<not>(a ## c)"
  using assms by auto


lemma cell_neq_prefix1: 
  "v\<noteq>0 \<Longrightarrow> sep_cell pv \<noteq> sep_prefix i v + v'"  
  by (determ transfer; clarsimp dest!: arg_cong[where f=dom]; fastforce)
  
lemma cell_neq_prefix2: 
  "v\<noteq>0 \<Longrightarrow> sep_prefix i v + v' \<noteq> sep_cell pv"  
  using cell_neq_prefix1 by metis
  
lemmas cell_neq_prefix = cell_neq_prefix1 cell_neq_prefix2  
  
lemma map_prefix_sum_cong: "map_prefix VA_FST a ++ map_prefix VA_SND b = map_prefix VA_FST a' ++ map_prefix VA_SND b'
  \<longleftrightarrow> a=a' \<and> b=b'"
  apply (auto simp: fun_eq_iff map_prefix_def map_add_def split: list.split)
  apply (auto split: option.splits)
  by (metis option.exhaust)
  

lemma sep_prefix_sum_cong: 
  "sep_prefix VA_FST a + sep_prefix VA_SND b = sep_prefix VA_FST a' + sep_prefix VA_SND b'
  \<longleftrightarrow> a=a' \<and> b=b'"
  apply (rule iffI)
  subgoal
    apply transfer
    apply (auto split: if_splits simp: m_dep_def map_prefix_sum_cong)
    done
  by auto  
  


lemma val_\<alpha>_inj[simp]: "val_\<alpha> v = val_\<alpha> w \<longleftrightarrow> v=w"  
proof (induction v arbitrary: w)
  case (V_INT x)
  then show ?case by (cases w) (auto simp: cell_neq_prefix)
next
  case (V_PTR x)
  then show ?case by (cases w) (auto simp: cell_neq_prefix)
next
  case (V_PAIR x)
  then show ?case
    apply (cases w; cases x)
    apply (auto simp: cell_neq_prefix sep_prefix_sum_cong)
    done
qed
  
  
lemma ll_free_rule:
  fixes p :: "'a::llvm_rep ptr"
  shows "htriple (is_array xs p ** alloc_tag (length xs) p) (ll_free p) (\<lambda>_. \<box>)"
  unfolding alloc_tag_def
  apply vcg
  apply (clarsimp 
    simp: STATE_def sep_algebra_simps pred_lift_extract_simps
    split: raw_ptr.splits ptr.splits addr.splits nat.splits list.splits)
proof -
  fix F h bi
  assume [simp]: "xs \<noteq> []"
  assume A: "(is_array xs (PTR (RP_ADDR (ADDR bi 0 []))::'a ptr) \<and>* EXACT (at_tag bi (length xs)) \<and>* F) (heap_\<alpha> h)"
    (is "(?A ** ?T ** F) _")
  
  obtain bls where [simp]: "h=HEAP bls" by (cases h) 
   
  have "(?A ** ?T) = EXACT (at_idx bi (list_\<alpha> (\<lambda>x. val_\<alpha> (to_val x)) xs, TRIV (length xs)))"  
    apply (simp add: is_array_def at_tag_def sep_algebra_simps is_valbase_ptr_def idx_ptr_def pto_def 
      at_addr_def list_conj_map_index_EXACT_conv sepsum_map_at_idx_const_conv)
    apply (subst EXACT_split[symmetric])
    apply (auto simp: sep_algebra_simps pair_sepsum_list_map_index) []
    apply (simp add: at_idx_add sep_algebra_simps pair_sepsum_list_map_index sepsum_map_at_idx_conv)
    done
  hence B: "(EXACT (at_idx bi (list_\<alpha> (\<lambda>x. val_\<alpha> (to_val x)) xs, TRIV (length xs))) ** F) ((list_\<alpha> (option_\<alpha> block_\<alpha>) bls))"
    using A apply (simp add: heap_\<alpha>_def) by (metis sep_conj_assoc)

  have "\<lbrakk>(list_\<alpha> (\<lambda>x. val_\<alpha> (to_val x)) xs, TRIV (length xs)) ## w;
           list_\<alpha> (option_\<alpha> block_\<alpha>) bls bi = (list_\<alpha> (\<lambda>x. val_\<alpha> (to_val x)) xs, TRIV (length xs)) + w\<rbrakk>
          \<Longrightarrow> w = 0" for w
    apply (cases w; cases "bls!bi"; simp)          
    apply (auto simp: sep_algebra_simps list_\<alpha>_def split: if_splits)
    apply (auto simp: block_\<alpha>_def block_\<alpha>vs_def block_\<alpha>t_def fun_eq_iff sep_disj_fun_def list_\<alpha>_def)
    subgoal for a aa x
      apply (drule spec[ where x=x])+
      apply (auto split: if_splits)
      done
    done
  with complete_idx_split[OF B] have 
    THIS_BLOCK: "list_\<alpha> (option_\<alpha> block_\<alpha>) bls bi = (list_\<alpha> (\<lambda>x. val_\<alpha> (to_val x)) xs, TRIV (length xs))" 
    and FRAME: "F ((list_\<alpha> (option_\<alpha> block_\<alpha>) bls)(bi := 0))"
    by auto
    
    
  from THIS_BLOCK obtain b where 
    [simp]: "bi<length bls" "bls!bi = Some b" 
    and THIS_BLOCK': "block_\<alpha> b = (list_\<alpha> (\<lambda>x. val_\<alpha> (to_val x)) xs, TRIV (length xs))"
    unfolding list_\<alpha>_def
    by (cases "bls!bi") (auto simp: sep_algebra_simps split: if_splits)
      
  from THIS_BLOCK' have [simp]: "b\<noteq>[]" "length b = length xs"
    by (auto simp: block_\<alpha>_def block_\<alpha>t_def)
    
  from THIS_BLOCK' have [simp]: "(b ! 0) = (to_val (xs ! 0))"  
    by (auto simp: block_\<alpha>_def block_\<alpha>vs_def list_\<alpha>_eq_conv)
    
  have "(list_\<alpha> (option_\<alpha> block_\<alpha>) bls)(bi := 0) = list_\<alpha> (option_\<alpha> block_\<alpha>) (bls[bi:=None])"  
    by (rule ext) (auto simp: list_\<alpha>_def)
    
  with FRAME have [simp]: "STATE F (HEAP (bls[bi := None]))"
    unfolding STATE_def by (simp add: heap_\<alpha>_def)
    
  show "llvm_wp (ll_free (PTR (RP_ADDR (ADDR bi 0 []))::'a ptr)) (\<lambda>_. POST F) h"
    unfolding llvm_wp_def ll_free_def raw_free_def ptr_to_addr'_def ptr_to_addr_def check_ptr_def POSTCOND_def
    by (auto simp: run_simps)
    
qed    
    
lemma at_idx_eq0_conv[simp]: "at_idx i v = 0 \<longleftrightarrow> v=0"
  by (auto simp: fun_eq_iff at_idx_apply)
  
lemma sep_prefixl_eq_0_conv[simp]: "sep_prefixl va v = 0 \<longleftrightarrow> v = 0"  
  by (induction va) auto
  
lemma at_val_ne0[simp]: "at_val va v \<noteq> 0" by (auto simp: at_val_def)
  
  
lemma map_prefix_inj_iff: "map_prefix i m = map_prefix j n \<longleftrightarrow> (i=j \<and> m=n) \<or> (i\<noteq>j \<and> m=Map.empty \<and> n=Map.empty)"
  by (auto simp: map_prefix_def fun_eq_iff split: list.splits; metis)
  
lemma map_prefix_inj[simp]: 
  "map_prefix i m = map_prefix i n \<longleftrightarrow> m=n"
  "i\<noteq>j \<Longrightarrow> map_prefix i m = map_prefix j n \<longleftrightarrow> m=Map.empty \<and> n=Map.empty"
  by (auto simp: map_prefix_inj_iff)
  


lemma sep_prefix_inj_iff: "sep_prefix i v = sep_prefix j w 
  \<longleftrightarrow> (i=j \<and> v=w) \<or> (i\<noteq>j \<and> v=0 \<and> w=0)"
  apply transfer
  by (auto simp: map_prefix_inj_iff)

lemma sep_prefix_inj[simp]:
  "sep_prefix i v = sep_prefix i w \<longleftrightarrow> v=w"  
  "i\<noteq>j \<Longrightarrow> sep_prefix i v = sep_prefix j w \<longleftrightarrow> v=0 \<and> w=0"
  by (auto simp: sep_prefix_inj_iff)
  
lemma sep_prefix_0[simp]: "sep_prefix i 0 = 0" by simp
  
lemma "sep_prefix i v\<^sub>2 ## fr \<Longrightarrow> v\<^sub>2\<noteq>0 \<Longrightarrow> sep_prefix i v\<^sub>1 = sep_prefix i v\<^sub>2 + fr \<longleftrightarrow> v\<^sub>1=v\<^sub>2 \<and> fr=0"
  apply rule
  subgoal
    apply (cases fr rule: sep_val_cases)
    apply auto
  
  sorry
  by auto
  
lemma map_prefix_empty[simp]: "map_prefix i Map.empty = Map.empty" by simp
  
find_theorems m_dep map_prefix
(* REDUNDANT: map_prefix_fst_snd_indep *)
lemma map_prefix_same_dep_iff[simp]: "m_dep (map_prefix i m\<^sub>1) (map_prefix i m\<^sub>2) \<longleftrightarrow> m_dep m\<^sub>1 m\<^sub>2"
  by (auto simp: m_dep_def)
  
lemma map_prefix_add[simp]: "map_prefix i (m\<^sub>1++m\<^sub>2) = map_prefix i m\<^sub>1 ++ map_prefix i m\<^sub>2"
  apply (rule ext)
  by (auto simp: map_prefix_def map_add_def split: list.split)
  

lemma sep_prefix_add[simp]: "sep_prefix i (v+w) = sep_prefix i v + sep_prefix i w"  
  apply transfer
  apply (auto)
  done
  
  
lemma load_vptr_correct:
  "at_val a x ## fr \<Longrightarrow> val_\<alpha> v = at_val a x + fr \<Longrightarrow> run (load_vptr a v) s = SUCC x s"
proof (induction a arbitrary: fr v)
  case Nil
  then show ?case by (auto simp: run_simps)
next
  case (Cons vai a)
  
  from Cons.prems obtain v\<^sub>1 v\<^sub>2 where
    [simp]: "v = V_PAIR (v\<^sub>1,v\<^sub>2)" and DJ: "sep_prefix vai (at_val a x) ## fr" 
      and PEQ: "sep_prefix VA_FST (val_\<alpha> v\<^sub>1) + sep_prefix VA_SND (val_\<alpha> v\<^sub>2) = sep_prefix vai (at_val a x) + fr"
    by (cases v) (auto simp: cell_neq_prefix)
    
  note [simp] = 
    sep_prefix_sum_cong
    sep_prefix_sum_cong[where b'=0, simplified]  
    sep_prefix_sum_cong[where a'=0, simplified]  
    sep_prefix_sum_cong[where b=0, simplified]  
    sep_prefix_sum_cong[where a=0, simplified]  
    
  have REW1: "sep_prefix VA_FST x\<^sub>1 + (sep_prefix VA_FST x\<^sub>2 + sep_prefix VA_SND x\<^sub>3) 
    = sep_prefix VA_FST (x\<^sub>1 + x\<^sub>2) +  sep_prefix VA_SND x\<^sub>3" if "x\<^sub>1##x\<^sub>2" for x\<^sub>1 x\<^sub>2 x\<^sub>3
    using that by (auto simp: sep_algebra_simps)
    
  from DJ obtain fr\<^sub>1 fr\<^sub>2 where [simp]: "fr = sep_prefix VA_FST fr\<^sub>1 + sep_prefix VA_SND fr\<^sub>2"
    by (cases fr rule: sep_val_cases) (auto)

  from PEQ DJ consider 
    (C_FST) "at_val a x ## fr\<^sub>1" "vai = VA_FST" "val_\<alpha> v\<^sub>1 = at_val a x + fr\<^sub>1" "fr\<^sub>2 = val_\<alpha> v\<^sub>2"       
  | (C_SND) "at_val a x ## fr\<^sub>2" "vai = VA_SND" "val_\<alpha> v\<^sub>2 = at_val a x + fr\<^sub>2" "fr\<^sub>1 = val_\<alpha> v\<^sub>1"  
    apply (cases vai)
    apply (auto simp: sep_algebra_simps simp del: sep_add_commute simp flip: sep_prefix_add)
    apply (subst (asm) REW1, simp)
    apply (auto simp flip: sep_prefix_add)
    apply (auto simp: sep_algebra_simps)
    done
  then show ?case
    apply cases
    apply (auto simp: run_simps Cons.IH)
    done
qed

(*
lemma "at_val ptr v\<^sub>1 ## fr \<Longrightarrow> at_val ptr v\<^sub>2 ## fr" 
proof (induction ptr arbitrary: fr)
  case Nil
  then show ?case by auto
next
  case (Cons a ptr)
  
  from Cons.prems show ?case 
    apply (cases fr rule: sep_val_cases)
    apply auto
    
  
  
qed 
*)  


lemma upd_vptr_correct:
  "at_val a xx ## fr \<Longrightarrow> val_\<alpha> v = at_val a xx + fr \<Longrightarrow> struct_of_val x = struct_of_val xx
    \<Longrightarrow> \<exists>v'. run (upd_vptr v a x) s = SUCC v' s \<and> val_\<alpha> v' = at_val a x + fr"
proof (induction v a x arbitrary: fr rule: upd_vptr.induct)
  case (1 ov v)
  then show ?case by (auto simp: run_simps)
next
  case (2 v\<^sub>1 v\<^sub>2 ptr v)
  
  have REW1: "sep_prefix VA_FST x\<^sub>1 + (sep_prefix VA_FST x\<^sub>2 + sep_prefix VA_SND x\<^sub>3) 
    = sep_prefix VA_FST (x\<^sub>1 + x\<^sub>2) +  sep_prefix VA_SND x\<^sub>3" if "x\<^sub>1##x\<^sub>2" for x\<^sub>1 x\<^sub>2 x\<^sub>3
    using that by (auto simp: sep_algebra_simps)
  
  from "2.prems"(1,2) obtain fr\<^sub>1 where 
    "at_val ptr xx ## fr\<^sub>1" 
    "val_\<alpha> v\<^sub>1 = at_val ptr xx + fr\<^sub>1" and
    [simp]: "fr = sep_prefix VA_FST fr\<^sub>1 + sep_prefix VA_SND (val_\<alpha> v\<^sub>2)"
    apply (cases fr rule: sep_val_cases)
    apply (auto simp: REW1 sep_prefix_sum_cong simp flip: sep_prefix_add)
    done
  
  from "2.IH"[OF this(1,2) \<open>struct_of_val v = struct_of_val xx\<close>]  
    obtain v' where [simp]: "run (upd_vptr v\<^sub>1 ptr v) s = SUCC v' s" "val_\<alpha> v' = at_val ptr v + fr\<^sub>1"
    by blast
  
  from \<open>at_val ptr xx ## fr\<^sub>1\<close> have [simp]: "at_val ptr v ## fr\<^sub>1" 
    (* TODO: Clean up this mess, and make a lemma instead! *)
    by (metis Rep_sep_val_inverse \<open>val_\<alpha> v' = at_val ptr v + fr\<^sub>1\<close> plus_sep_val.rep_eq sep_disj_sep_val.rep_eq val_\<alpha>_ne0 zero_sep_val.abs_eq)
  
    
  show ?case 
    apply (auto simp: run_simps sep_algebra_simps)
    apply (auto simp: sep_add_assoc)
    done
    
next
  case (3 v\<^sub>1 v\<^sub>2 ptr v)
  
  from "3.prems"(1,2) obtain fr\<^sub>2 where 
    "at_val ptr xx ## fr\<^sub>2" 
    "val_\<alpha> v\<^sub>2 = at_val ptr xx + fr\<^sub>2" and
    [simp]: "fr = sep_prefix VA_FST (val_\<alpha> v\<^sub>1) + sep_prefix VA_SND (fr\<^sub>2)"
    apply (cases fr rule: sep_val_cases)
    apply (auto simp: sep_prefix_sum_cong sep_algebra_simps simp flip: sep_prefix_add)
    done
  
  from "3.IH"[OF this(1,2) \<open>struct_of_val v = struct_of_val xx\<close>]  
    obtain v' where [simp]: "run (upd_vptr v\<^sub>2 ptr v) s = SUCC v' s" "val_\<alpha> v' = at_val ptr v + fr\<^sub>2"
    by blast
  
  from \<open>at_val ptr xx ## fr\<^sub>2\<close> have [simp]: "at_val ptr v ## fr\<^sub>2" 
    (* TODO: Clean up this mess, and make a lemma instead! *)
    by (metis Rep_sep_val_inverse \<open>val_\<alpha> v' = at_val ptr v + fr\<^sub>2\<close> plus_sep_val.rep_eq sep_disj_sep_val.rep_eq val_\<alpha>_ne0 zero_sep_val.abs_eq)
  hence [simp]: "fr\<^sub>2 ## at_val ptr v" by (simp add: sep_algebra_simps)
    
  show ?case by (auto simp: run_simps sep_algebra_simps)
next
  case ("4_1" vb v va uw)
  then show ?case by (auto simp: run_simps cell_neq_prefix)
next
  case ("4_2" vb v va uw)
  then show ?case by (auto simp: run_simps cell_neq_prefix)
next
  case ("4_3" v va uw)
  then show ?case by (auto simp: run_simps cell_neq_prefix)
next
  case ("4_4" v va uw)
  then show ?case by (auto simp: run_simps cell_neq_prefix)
qed

lemma ll_load_rule: "htriple (pto x p) (ll_load p) (\<lambda>r. pto x p ** \<up>(r=x))"
  apply vcg
  (*apply (clarsimp simp: STATE_def pto_def split: ptr.splits raw_ptr.splits)*)
proof -
  fix F h
  assume PRE: "STATE (pto x p \<and>* F) h"
  then obtain addr where [simp]: "p = PTR (RP_ADDR addr)"
    and A: "(EXACT (at_addr addr (to_val x)) \<and>* F) (heap_\<alpha> h)"
    by (clarsimp simp: STATE_def pto_def split: ptr.splits raw_ptr.splits)
    
  obtain bi idx va where [simp]: "addr = ADDR bi idx va" by (cases addr)
  obtain bls where [simp]: "h = HEAP bls" by (cases h)
    
  from extract_at_idx[OF A[unfolded at_addr_def heap_\<alpha>_def, simplified]] 
  obtain b vs' where [simp]: "bi < length bls" "bls!bi = Some b" 
    and VS'_DJ: "at_idx idx (at_val va (to_val x)) ## vs'" 
    and VS'_R: "block_\<alpha>vs b = at_idx idx (at_val va (to_val x)) + vs'"
    apply (cases "bls!bi")
    apply (auto simp: sep_algebra_simps block_\<alpha>_def)
    done
    
  have V': "at_val va (to_val x) ## vs' idx" "block_\<alpha>vs b idx = at_val va (to_val x) + vs' idx"  
    using VS'_DJ
    by (auto simp add: VS'_R sep_disj_fun_def at_idx_apply split: if_splits)
  hence IDX_LT: "idx < length b"  
    by (auto simp: block_\<alpha>vs_def list_\<alpha>_def split: if_splits)
  hence [intro]: "idx\<le>length b" and [simp]: "b\<noteq>[]" by auto
    
  from IDX_LT have [simp]: "min idx (length b - Suc 0) = idx" by auto
  
  from V' have "val_\<alpha> (b!idx) = at_val va (to_val x) + vs' idx"
    by (auto simp: block_\<alpha>vs_def list_\<alpha>_def split: if_splits)
  
  note [run_simps] = load_vptr_correct[OF V'(1) this]  
    
  
  show "llvm_wp (ll_load p) (\<lambda>r. POST ((pto x p \<and>* \<up>(r = x)) \<and>* F)) h"
    unfolding llvm_wp_def ll_load_def check_ptr_def ptr_to_addr_def POSTCOND_def
    using PRE
    apply (auto simp: run_simps sep_algebra_simps IDX_LT)
    done
    
qed  
  

lemma list_\<alpha>_upd: "i<length xs \<Longrightarrow> list_\<alpha> \<alpha> (xs[i:=x]) = (list_\<alpha> \<alpha> xs)(i := \<alpha> x)"
  by (auto simp: list_\<alpha>_def)

  
lemma 
  assumes "(EXACT (at_idx i v) ** F) (list_\<alpha> \<alpha> xs)"
  shows "(EXACT (at_idx i v') ** F) (list_\<alpha> \<alpha> (xs[i:=x']))"
  
xxx, ctd here:

  Replace a value by something with a smaller domain works!

  for functions: Replace value v at index i by value v' \<le> v works
    
  how to model operation of replacing only the vi-part of index i?
  
   (at_idx i vi ** F) v \<Longrightarrow> (at_idx i vi' ** F) ()
   
   
   
  
    
  
  


lemma ll_store_rule: "htriple (pto xx p) (ll_store x p) (\<lambda>_. pto x p)"  
  apply vcg
proof -
  fix F h
  
  assume PRE: "STATE (pto xx p \<and>* F) h"
  then obtain addr where [simp]: "p = PTR (RP_ADDR addr)"
    and A: "(EXACT (at_addr addr (to_val xx)) \<and>* F) (heap_\<alpha> h)"
    by (clarsimp simp: STATE_def pto_def split: ptr.splits raw_ptr.splits)
    
  obtain bi idx va where [simp]: "addr = ADDR bi idx va" by (cases addr)
  obtain bls where [simp]: "h = HEAP bls" by (cases h)
    
  from extract_at_idx[OF A[unfolded at_addr_def heap_\<alpha>_def, simplified]] 
  obtain b vs' where [simp]: "bi < length bls" "bls!bi = Some b" 
    and VS'_DJ: "at_idx idx (at_val va (to_val xx)) ## vs'" 
    and VS'_R: "block_\<alpha>vs b = at_idx idx (at_val va (to_val xx)) + vs'"
    apply (cases "bls!bi")
    apply (auto simp: sep_algebra_simps block_\<alpha>_def)
    done
    
  have V': "at_val va (to_val xx) ## vs' idx" "block_\<alpha>vs b idx = at_val va (to_val xx) + vs' idx"  
    using VS'_DJ
    by (auto simp add: VS'_R sep_disj_fun_def at_idx_apply split: if_splits)
  hence IDX_LT: "idx < length b"  
    by (auto simp: block_\<alpha>vs_def list_\<alpha>_def split: if_splits)
  hence [intro]: "idx\<le>length b" and [simp]: "b\<noteq>[]" by auto
    
  from IDX_LT have [simp]: "min idx (length b - Suc 0) = idx" by auto
  
  from V' have V'': "val_\<alpha> (b!idx) = at_val va (to_val xx) + vs' idx"
    by (auto simp: block_\<alpha>vs_def list_\<alpha>_def split: if_splits)
  
  note [run_simps] = load_vptr_correct[OF V'(1) V'']  
  
  obtain v' where 
    [run_simps]: "run (upd_vptr (b ! idx) va (to_val x)) (HEAP bls) = SUCC v' (HEAP bls)"  
    and "val_\<alpha> v' = at_val va (to_val x) + vs' idx"
    using upd_vptr_correct[OF V'(1) V'', of "to_val x" "HEAP bls"]
    by auto 
  
  have "STATE (pto x (PTR (RP_ADDR (ADDR bi idx va))) \<and>* F) (HEAP (bls[bi := Some (b[idx := v'])]))"  
    using PRE
    apply (simp add: STATE_def)
    apply (auto simp: pto_def at_addr_def heap_\<alpha>_def list_\<alpha>_upd)
    
    
  
  show "llvm_wp (ll_store x p) (\<lambda>r. POST (pto x p \<and>* F)) h"
    unfolding llvm_wp_def ll_store_def check_ptr_def ptr_to_addr_def POSTCOND_def
    apply (auto simp: run_simps sep_algebra_simps IDX_LT)
  


  
term "htriple \<box> (ll_malloc TYPE ('a::llvm_rep) n) (\<lambda>r. is_array (replicate (unat n) init) r ** alloc_tag (unat n) r)"
term "htriple (is_array xs p ** alloc_tag (length xs) p) (ll_free p) (\<lambda>_. \<box>)"
term "htriple (pto x p) (ll_load p) (\<lambda>r. pto x p ** \<up>(r=x))"
term "htriple (pto xx p) (ll_store x p) (\<lambda>_. pto x p)"


oops
  xxx, ctd here: Define is_array in terms of pto, and address arithmetic!
  
oops
xxx, ctd here: set-up hoare logic.
  points-to addr prim_val assertion (use EXACT)
  alloc_tag assertion
  
  
term EXACT



    
      
end
