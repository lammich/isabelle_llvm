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
  type_synonym raw_vaddr = "raw_vaitem list"
  
  datatype addr = ADDR nat nat raw_vaddr
  
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
  hide_const (open) the_heap
  
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
    
    
  fun upd_vptr :: "val \<Rightarrow> raw_vaddr \<Rightarrow> val \<Rightarrow> val llM" where
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
    return (HEAP h)
  }"
          
  definition ll_store :: "'a::llvm_rep \<Rightarrow> 'a ptr \<Rightarrow> unit llM" where
    "ll_store v p \<equiv> doM {
      addr \<leftarrow> ptr_to_addr p;
      raw_store addr (to_val v);
      return ()
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


fun va_dep :: "raw_vaddr \<Rightarrow> raw_vaddr \<Rightarrow> bool" where
  "va_dep [] _ \<longleftrightarrow> True"
| "va_dep _ [] \<longleftrightarrow> True"  
| "va_dep (x#xs) (y#ys) \<longleftrightarrow> x=y \<and> va_dep xs ys"

lemma va_dep_add_simp[simp]: "va_dep xs [] \<longleftrightarrow> True" by (cases xs) auto

lemma va_dep_alt: 
  "va_dep xs ys \<longleftrightarrow> take (min (length xs) (length ys)) xs = take (min (length xs) (length ys)) ys"
  by (induction xs ys rule: va_dep.induct) auto

lemma va_dep_refl[simp]: "va_dep xs xs" by (induction xs) auto

lemma va_dep_sym[sym]: "va_dep xs ys \<Longrightarrow> va_dep ys xs"
  unfolding va_dep_alt by (auto simp: min_def split: if_splits)

fun addr_dep :: "addr \<Rightarrow> addr \<Rightarrow> bool"
  where "addr_dep (ADDR bn1 i1 va1) (ADDR bn2 i2 va2) \<longleftrightarrow> bn1=bn2 \<and> i1=i2 \<and> va_dep va1 va2"
  
lemma addr_dep_refl[simp]: "addr_dep xs xs" by (cases xs) auto

lemma addr_dep_sym[sym]: "addr_dep xs ys \<Longrightarrow> addr_dep ys xs"
  by (cases xs; cases ys; auto simp: va_dep_sym)
  
  
  
datatype prim_val = PV_INT lint | PV_PTR raw_ptr  
  
typedef sep_val = "{m :: addr \<rightharpoonup> prim_val . \<forall>x\<in>dom m. \<forall>y\<in>dom m. addr_dep x y \<longrightarrow> x=y}"
  by auto
  
setup_lifting type_definition_sep_val  
  

definition "m_indep m1 m2 \<equiv> \<forall>x\<in>dom m1. \<forall>y\<in>dom m2. \<not>addr_dep x y"

lemma m_indep_imp_dom_disj: "m_indep m1 m2 \<Longrightarrow> dom m1 \<inter> dom m2 = {}"
  by (fastforce simp: m_indep_def dom_def) 
  
lemma m_indep_sym: "m_indep m1 m2 \<Longrightarrow> m_indep m2 m1"  
  by (auto simp: m_indep_def dest: addr_dep_sym)
  
lemma m_indep_empty[simp]: 
  "m_indep x Map.empty"  
  "m_indep Map.empty x"  
  by (auto simp: m_indep_def)
  
lemma m_indep_same[simp]: "m_indep x x \<longleftrightarrow> x=Map.empty"
  apply (auto)
  apply (force simp: m_indep_def)
  done
  
  
instantiation sep_val :: unique_zero_sep_algebra begin
  lift_definition sep_disj_sep_val :: "sep_val \<Rightarrow> sep_val \<Rightarrow> bool" is m_indep .

  lift_definition plus_sep_val :: "sep_val \<Rightarrow> sep_val \<Rightarrow> sep_val" is "\<lambda>m1 m2. if m_indep m1 m2 then m1++m2 else m1"
    by (fastforce split: if_splits simp: m_indep_def dom_def intro: addr_dep_sym)

  lift_definition zero_sep_val :: "sep_val" is "Map.empty" by auto
    
  instance
    apply standard
    apply (determ transfer; auto simp: m_indep_def)
    apply (determ transfer; auto simp: m_indep_def dom_def dest: addr_dep_sym)
    apply (determ transfer; auto simp: m_indep_def)
    apply (determ transfer; auto simp: m_indep_imp_dom_disj map_add_comm m_indep_sym)
    apply (determ transfer; auto; metis UnE dom_map_add m_indep_def)
    apply (determ transfer; auto simp: m_indep_def domI)
    apply (determ transfer; simp)
    done
end    
    
lift_definition sep_dom :: "sep_val \<Rightarrow> addr set" is dom .

lift_definition sep_cell :: "addr \<Rightarrow> prim_val \<Rightarrow> sep_val" is "\<lambda>x v. [x\<mapsto>v]" by auto

lemma sep_dom_zero[simp]: "sep_dom 0 = {}"  
  by transfer auto

lemma sep_cell_disj_iff: "sep_cell a v ## sep_cell b v' \<longleftrightarrow> \<not>addr_dep a b"
  by transfer (auto simp: m_indep_def)

lemma sep_dom_cell[simp]: "sep_dom (sep_cell a v) = {a}"
  by transfer auto

lemma sep_disj_dom: "s1 ## s2 \<longleftrightarrow> (\<forall>x1\<in>sep_dom s1. \<forall>x2\<in>sep_dom s2. \<not>addr_dep x1 x2)"
  apply transfer
  apply (auto simp: m_indep_def )
  done
  
fun idx where  
  "idx vai (ADDR bn i va) = ADDR bn i (va@[vai])"
  
abbreviation "idx_fst \<equiv> idx VA_FST"
abbreviation "idx_snd \<equiv> idx VA_SND"
    
definition "base_addr bn \<equiv> ADDR bn 0 []"  
fun ofs_addr where "ofs_addr j (ADDR bn i va) = ADDR bn (nat (int i + j)) va"
   
  
fun sep_val where
  "sep_val a (V_INT x) = sep_cell a (PV_INT x)"  
| "sep_val a (V_PTR x) = sep_cell a (PV_PTR x)"  
| "sep_val a (V_PAIR (x1,x2)) = sep_val (idx_fst a) x1 + sep_val (idx_snd a) x2"
  

definition sep_block where "sep_block a xs \<equiv> sepsum_list (map_index (\<lambda>i v. sep_val (ofs_addr (int i) a) v) xs)"


type_synonym sep_heap_base = "(sep_val \<times> (nat \<Rightarrow> nat tsa_opt))"  
typedef sep_heap = "UNIV :: sep_heap_base set" by simp

setup_lifting type_definition_sep_heap
    
instantiation sep_heap :: unique_zero_sep_algebra
begin
  lift_definition sep_disj_sep_heap :: "sep_heap \<Rightarrow> sep_heap \<Rightarrow> bool" is "(##)" .

  lift_definition plus_sep_heap :: "sep_heap \<Rightarrow> sep_heap \<Rightarrow> sep_heap" is "(+)" .
  lift_definition zero_sep_heap :: "sep_heap" is "0" .

  instance
    apply standard
    apply (determ transfer; auto)
    apply (determ transfer; auto simp: sep_algebra_simps sep_disj_commuteI)
    apply (determ transfer; auto)
    apply (determ transfer; auto simp: sep_algebra_simps)
    apply (determ transfer; auto simp: sep_algebra_simps)
    apply (determ transfer; auto simp: sep_algebra_simps dest: sep_disj_addD1)
    apply (determ transfer; auto simp: sep_algebra_simps)
    done
  
end

definition sep_tags where 
  "sep_tags \<equiv> \<lambda>HEAP h \<Rightarrow> sepsum_list (map_index (\<lambda>i. \<lambda>None\<Rightarrow>\<lambda>_. ZERO | Some l \<Rightarrow> (\<lambda>_. 0)(i:=TRIV (length l))) h)"

definition sep_blocks where
  "sep_blocks \<equiv> \<lambda>HEAP h \<Rightarrow> sepsum_list (map_index (\<lambda>i. \<lambda>None\<Rightarrow>0 | Some l \<Rightarrow> sep_block (base_addr i) l) h)"
  
(*    
fun sep_tags where 
  "sep_tags (HEAP h) i = (if i<length h then case h!i of None \<Rightarrow> ZERO | Some l \<Rightarrow> TRIV (length l) else ZERO)"

fun sep_blocks where 
  "sep_blocks (HEAP h) = fold (\<lambda>(bn,blk) s. case blk of Some blk \<Rightarrow> s + sep_block (base_addr bn) blk | _ \<Rightarrow> s) (List.enumerate 0 h) 0"
*) 
  
(*lift_definition sep_heap :: "heap \<Rightarrow> sep_heap" is "\<lambda>h::heap. (sep_blocks h, sep_tags h)" .*)

lift_definition CONTENT :: "sep_val \<Rightarrow> sep_heap" is "\<lambda>x::sep_val. (x,\<lambda>_::nat. ZERO::nat tsa_opt)" .
lift_definition TAGS :: "(nat \<Rightarrow> nat tsa_opt) \<Rightarrow> sep_heap" is "\<lambda>x::nat \<Rightarrow> nat tsa_opt. (0,x)" .

lemma CONTENT_disj_lower[sep_algebra_simps]: "CONTENT a ## CONTENT b \<longleftrightarrow> a##b"
  apply transfer'
  apply (auto simp: sep_algebra_simps)
  done

lemma TAGS_disj_lower[sep_algebra_simps]: "TAGS a ## TAGS b \<longleftrightarrow> a##b"
  apply transfer'
  apply (auto simp: sep_algebra_simps)
  done
  
  
definition "sep_heap h \<equiv> CONTENT (sep_blocks h) + TAGS (sep_tags h)"

definition llvm_wp :: "'a llM \<Rightarrow> ('a \<Rightarrow> heap \<Rightarrow> bool) \<Rightarrow> heap \<Rightarrow> bool"
  where "llvm_wp (c::_ llM) Q s \<equiv> mwp (run c s) bot bot bot Q"


interpretation conc_heap sep_heap "\<lambda>_. True" llvm_wp
  apply standard
  apply (auto simp: llvm_wp_def elim!: mwp_cons)
  done
  
fun is_base_ptr where "is_base_ptr (PTR (RP_ADDR (ADDR _ i va))) \<longleftrightarrow> i=0 \<and> va=[]" | "is_base_ptr _ \<longleftrightarrow> False"
fun the_block where "the_block (PTR (RP_ADDR (ADDR bl 0 []))) = bl" | "the_block _ = undefined"


fun is_bli_ptr where "is_bli_ptr (PTR (RP_ADDR (ADDR _ _ va))) \<longleftrightarrow> va=[]" | "is_bli_ptr _ \<longleftrightarrow> False"
fun addr_op where "addr_op f (PTR (RP_ADDR a)) = PTR (RP_ADDR (f a))" | "addr_op _ _ = undefined"
  
term ofs_addr  
  

fun pto :: "'a::llvm_rep \<Rightarrow> 'a ptr \<Rightarrow> sep_heap \<Rightarrow> bool" where 
  "pto v (PTR (RP_ADDR a)) = EXACT (CONTENT (sep_val a (to_val v)))"
| "pto v (PTR RP_NULL) = sep_false"
  
definition is_array :: "'a::llvm_rep list \<Rightarrow> 'a ptr \<Rightarrow> sep_heap \<Rightarrow> bool" where
  "is_array xs p = (\<up>(is_bli_ptr p) ** \<And>*map_index (\<lambda>i x. pto x (addr_op (ofs_addr (int i)) p)) xs)"

definition alloc_tag :: "nat \<Rightarrow> 'a::llvm_rep ptr \<Rightarrow> sep_heap \<Rightarrow> bool" where
  "alloc_tag sz p = (\<up>(is_base_ptr p \<and> sz>0) ** EXACT (TAGS ((\<lambda>_. ZERO)(the_block p := TRIV sz))))"
  
  
(*consts alloc_tag :: "nat \<Rightarrow> 'a ptr \<Rightarrow> sep_heap \<Rightarrow> bool"*)

(* TODO: Move *)
lemma disj_sepsum_set_conv: "sep_distinct ys \<Longrightarrow> x ## sepsum_list ys \<longleftrightarrow> (\<forall>y\<in>List.set ys. x##y)"
  by (induction ys) auto

lemma sep_dom_add[simp]: "a##b \<Longrightarrow> sep_dom (a+b) = sep_dom a \<union> sep_dom b"  
  by transfer (auto)
  
lemma diff_idx_not_dep[simp]: "\<not>addr_dep (idx_fst a) (idx_snd a)"  
  by (cases a) (auto simp: va_dep_alt)
  
fun is_prefix where
  "is_prefix (ADDR bn\<^sub>1 i\<^sub>1 a\<^sub>1) (ADDR bn\<^sub>2 i\<^sub>2 a\<^sub>2) \<longleftrightarrow> bn\<^sub>1=bn\<^sub>2 \<and> i\<^sub>1=i\<^sub>2 \<and> (\<exists>sfx. a\<^sub>2 = a\<^sub>1@sfx)"  
  
lemma va_dep_prf: "va_dep a\<^sub>1 a\<^sub>2 = (\<exists>sfx. a\<^sub>1 = a\<^sub>2@sfx \<or> a\<^sub>2 = a\<^sub>1@sfx)"  
  by (induction a\<^sub>1 a\<^sub>2 rule: va_dep.induct) auto
  
lemma addr_dep_prf: "addr_dep a\<^sub>1 a\<^sub>2 \<longleftrightarrow> is_prefix a\<^sub>1 a\<^sub>2 \<or> is_prefix a\<^sub>2 a\<^sub>1"
  by (cases a\<^sub>1; cases a\<^sub>2; auto simp: va_dep_prf)
  
  
lemma is_prefix_refl[simp]: "is_prefix a a" by (cases a) auto
  
lemma is_prefix_idxI: "is_prefix (idx i a) b \<Longrightarrow> is_prefix a b"
  by (cases a; cases b) auto

lemma is_prefix_idx_inj: "is_prefix (idx i a) b \<Longrightarrow> is_prefix (idx j a) b \<Longrightarrow> i=j"  
  by (cases a; cases b) auto

  
lemma dom_val_prefix: "a\<in>sep_dom (sep_val a' v) \<Longrightarrow> is_prefix a' a"  
proof (induction v arbitrary: a a')
  case (V_INT x)
  then show ?case by auto
next
  case (V_PTR x)
  then show ?case by auto
next
  case (V_PAIR x)
  then obtain x\<^sub>1 x\<^sub>2 where [simp]: "x=(x\<^sub>1,x\<^sub>2)" by (cases x)
  
  have 1: "a \<in> sep_dom (sep_val (idx_fst a') x\<^sub>1) \<Longrightarrow> is_prefix (idx_fst a') a" for a
    using V_PAIR.IH(1)[of x\<^sub>1 a "idx_fst a'"] by auto
  have 2: "a \<in> sep_dom (sep_val (idx_snd a') x\<^sub>2) \<Longrightarrow> is_prefix (idx_snd a') a" for a
    using V_PAIR.IH(2)[of x\<^sub>2 a "idx_snd a'"] by auto
  have [simp]: "sep_val (idx_fst a') x\<^sub>1 ## sep_val (idx_snd a') x\<^sub>2"
    unfolding sep_disj_dom 
  proof safe
    fix a\<^sub>1 a\<^sub>2
    assume "a\<^sub>1 \<in> sep_dom (sep_val (idx_fst a') x\<^sub>1)" "a\<^sub>2 \<in> sep_dom (sep_val (idx_snd a') x\<^sub>2)"
    with 1 2 have "is_prefix (idx_fst a') a\<^sub>1" "is_prefix (idx_snd a') a\<^sub>2" by auto
    moreover assume "addr_dep a\<^sub>1 a\<^sub>2"
    ultimately show False
      apply (simp add: addr_dep_prf)
      apply (cases a\<^sub>1; cases a\<^sub>2; cases a'; auto)
      done
  qed  
  
  from V_PAIR.prems show ?case
    apply simp
    using "1" "2" is_prefix_idxI by blast
    
qed  
  
lemma sep_val_idx_dj[simp]: "sep_val (idx_fst a') x\<^sub>1 ## sep_val (idx_snd a') x\<^sub>2"
  unfolding sep_disj_dom 
proof safe
  fix a\<^sub>1 a\<^sub>2
  assume "a\<^sub>1 \<in> sep_dom (sep_val (idx_fst a') x\<^sub>1)" "a\<^sub>2 \<in> sep_dom (sep_val (idx_snd a') x\<^sub>2)"
  with dom_val_prefix have "is_prefix (idx_fst a') a\<^sub>1" "is_prefix (idx_snd a') a\<^sub>2" by auto
  moreover assume "addr_dep a\<^sub>1 a\<^sub>2"
  ultimately show False
    apply (simp add: addr_dep_prf)
    apply (cases a\<^sub>1; cases a\<^sub>2; cases a'; auto)
    done
qed  


lemma addr_indep_imp_val_dj[simp]: "\<not>addr_dep a\<^sub>1 a\<^sub>2 \<Longrightarrow> sep_val a\<^sub>1 v\<^sub>1 ## sep_val a\<^sub>2 v\<^sub>2"
  unfolding sep_disj_dom 
  apply (clarsimp dest!: dom_val_prefix simp: addr_dep_prf)
  subgoal for x\<^sub>1 x\<^sub>2
    apply (cases a\<^sub>1; cases a\<^sub>2; cases x\<^sub>1; cases x\<^sub>2; simp)
    apply (auto simp: append_eq_append_conv2)
    done
  done  
  
lemma ofs_pos_addr_dep[simp]: "i\<ge>0 \<Longrightarrow> j\<ge>0 \<Longrightarrow> addr_dep (ofs_addr i a) (ofs_addr j a) \<longleftrightarrow> i=j"  
  by (cases a) auto
  
lemma block_distinct_aux[simp]: "sep_distinct (map_index' i\<^sub>0 (\<lambda>ia. sep_val (ofs_addr (int ia) (base_addr i))) xs)"  
  apply (induction xs arbitrary: i\<^sub>0)
  apply (auto simp: disj_sepsum_set_conv)
  done
  
lemma sep_dom_sum_eq[simp]: "sep_distinct xs \<Longrightarrow> sep_dom (sepsum_list xs) = (\<Union>x\<in>List.set xs. sep_dom x)"  
  by (induction xs) (auto)
  
(*  
lemma "ADDR bn i va \<in> sep_dom (sep_val (ofs_addr (int i') (base_addr bn')) v) \<Longrightarrow> bn=bn' \<and> i=i'"  
  using base_addr_def dom_val_prefix by fastforce
  
lemma "ADDR bn i va \<in> sep_dom (sepsum_list (map_index' i\<^sub>0 (\<lambda>i'. sep_val (ofs_addr (int i') (base_addr bn'))) xs))
  \<Longrightarrow> bn=bn' \<and> i\<ge>i\<^sub>0 \<and> i<i\<^sub>0 + length xs"  
  apply auto
  
  apply (induction xs arbitrary: i\<^sub>0)
  apply (auto)
*)  
  
  
  
lemma addr_dep_lower: "addr_dep a1 a2 \<longleftrightarrow> (\<exists>bn i va1 va2. a1=ADDR bn i va1 \<and> a2=ADDR bn i va2 \<and> va_dep va1 va2)"  
  by (cases a1; cases a2) auto

  
lemma sep_block_disjI: "i\<noteq>i' \<Longrightarrow> sep_block (base_addr i) xs ## sep_block (base_addr i') ys"
  apply (auto simp add: sep_block_def sep_disj_dom dest!: dom_val_prefix)
  apply (auto simp: addr_dep_lower base_addr_def)
  done

lemma blocks_distinct_aux[simp]: "sep_distinct (map_index' i\<^sub>0 (\<lambda>i. case_option 0 (sep_block (base_addr i))) h)"
  apply (induction h arbitrary: i\<^sub>0)
  apply (auto split: option.splits simp: disj_sepsum_set_conv sep_block_disjI)
  done

lemma heap_distinct_alloc[simp]: 
  "sep_block (base_addr (length h)) xs ## sepsum_list (map_index (\<lambda>i. case_option 0 (sep_block (base_addr i))) h)"
  apply (auto simp: sep_disj_dom sep_block_def dest!: dom_val_prefix split: option.splits)
  apply (auto simp: addr_dep_lower base_addr_def)
  done
      
(* TODO: Move *)     
lemma lift_ZERO: "(\<lambda>_. ZERO) = 0" by auto

lemma sep_distinct_alt: "sep_distinct xs \<longleftrightarrow> (\<forall>i<length xs. \<forall>j<length xs. i\<noteq>j \<longrightarrow> xs!i ## xs!j)"
  apply (induction xs)
  apply (auto simp: disj_sepsum_set_conv sep_algebra_simps nth_Cons all_set_conv_all_nth split: nat.split)
  done


lemma nth_map_index': "i<length xs \<Longrightarrow> map_index' i\<^sub>0 f xs ! i = f (i+i\<^sub>0) (xs!i)"  
  apply (induction xs arbitrary: i i\<^sub>0)
  apply (auto simp: nth_Cons')
  done
  
lemma sep_distinct_map_index'_alt: "sep_distinct (map_index' i\<^sub>0 f xs) 
  \<longleftrightarrow> (\<forall>i<length xs. \<forall>j<length xs. i\<noteq>j \<longrightarrow> f (i+i\<^sub>0) (xs!i) ## f (j+i\<^sub>0) (xs!j))"  
  by (auto simp: sep_distinct_alt nth_map_index')
  
find_theorems ZERO 0 
  
lemma disj_upd_zero_iff[simp]: "(fun_upd (\<lambda>_. 0) x a) ## (fun_upd (\<lambda>_. 0) y b) \<longleftrightarrow> x\<noteq>y \<or> a##b"
  by (auto simp: sep_disj_fun_def)

lemma CONTENT_TAG_dj[simp]:
  "CONTENT c ## TAGS t"
  "TAGS t ## CONTENT c"
  by (determ transfer; auto simp: lift_ZERO sep_algebra_simps)+
  
  
lemma heap_alloc_conv_dj[simp]: 
  "sep_heap h ## CONTENT (sep_block (base_addr (length (heap.the_heap h))) (replicate (unat n) x))"
  "sep_heap h ## TAGS ((\<lambda>_. 0)(length (heap.the_heap h) := TRIV (unat n)))"
  subgoal by (simp add: sep_heap_def sep_algebra_simps sep_blocks_def split: heap.splits)
  subgoal by (auto 
      simp: sep_heap_def sep_algebra_simps sep_tags_def lift_ZERO 
      simp: sep_distinct_map_index'_alt disj_sepsum_set_conv
      split: heap.splits option.split)
  done    
    
  
  
lemma heap_alloc_conv: "(sep_heap (HEAP (heap.the_heap h @ [Some (replicate (unat n) x)]))) = 
  sep_heap h 
  + CONTENT (sep_block (base_addr (length (heap.the_heap h))) (replicate (unat n) x)) 
  + TAGS ((\<lambda>_. 0)(length (heap.the_heap h) := TRIV (unat n)))"
  apply (simp add: sep_heap_def; transfer)
  apply (simp add: sep_algebra_simps lift_ZERO)
  apply (auto simp: sep_algebra_simps sep_blocks_def split: heap.splits) []
  apply (auto simp: sep_algebra_simps sep_tags_def lift_ZERO split: heap.splits)
  apply (subst sepsum_append)
  apply (auto simp add: sep_algebra_simps sep_distinct_map_index'_alt disj_sepsum_set_conv split: option.split)
  done


lemma list_conj_map_index_EXACT_conv:
  assumes "\<And>i j x y. \<lbrakk> i\<noteq>j \<rbrakk> \<Longrightarrow> f i x ## f j y"
  shows "(\<And>* map_index' i\<^sub>0 (\<lambda>i x. EXACT (f i x)) xs) = EXACT (sepsum_list (map_index' i\<^sub>0 f xs))"
proof -
  show ?thesis
    apply (induction xs arbitrary: i\<^sub>0)
    apply (auto del: ext intro!: ext simp: sep_conj_def sep_distinct_map_index'_alt disj_sepsum_set_conv)
    apply (subst disj_sepsum_set_conv)
    apply (auto simp add: sep_distinct_map_index'_alt algebra_simps assms)
    done
    
qed  
  
lemma lift_CONTENT0[sep_algebra_simps]: "CONTENT 0 = 0" 
  by transfer' (auto simp: sep_algebra_simps)
  
lemma CONTENT_distrib_add: "CONTENT (a+b) = CONTENT a + CONTENT b"  
  by transfer' (auto simp: sep_algebra_simps)
  
lemma sepsum_list_pull_CONTENT: "sepsum_list (map_index' i\<^sub>0 (\<lambda>i x. CONTENT (f i x)) xs) = CONTENT (sepsum_list (map_index' i\<^sub>0 f xs))"  
  apply (induction xs arbitrary: i\<^sub>0)
  apply (auto simp: sep_algebra_simps CONTENT_distrib_add)
  done
  
find_theorems map_index replicate
  
lemma map_index'_replicate_conv: "map_index' i\<^sub>0 f (replicate n x) = map (\<lambda>i. f i x) [i\<^sub>0..<i\<^sub>0+n]"
  apply (induction n arbitrary: i\<^sub>0)
  apply (auto simp: upt_rec)
  done
  
lemma CONTENT_inj[simp]: "CONTENT a = CONTENT b \<longleftrightarrow> a=b"  
  by transfer' auto
  
lemma TAGS_inj[simp]: "TAGS a = TAGS b \<longleftrightarrow> a=b"  
  by transfer' auto
  
lemma malloc_rule_aux:
  assumes "unat n>0" "F (sep_heap h)"
  shows "(is_array (replicate (unat n) (init::'a)) (PTR (RP_ADDR (ADDR (length (heap.the_heap h)) 0 []))) \<and>*
        alloc_tag (unat n) (PTR (RP_ADDR (ADDR (length (heap.the_heap h)) 0 []))) \<and>* F)
        (sep_heap h +
         CONTENT (sep_block (base_addr (length (heap.the_heap h))) (replicate (unat n) (to_val (init::'a::llvm_rep)))) +
         TAGS ((\<lambda>_. 0)(length (heap.the_heap h) := TRIV (unat n))))"
  (is "(?A ** ?T ** ?H) (?h + ?a + ?t)")
proof -
  note SCI = sep_conjI[OF _ _ _ refl]

  have "?A ?a" 
    apply (simp add: is_array_def sep_algebra_simps list_conj_map_index_EXACT_conv sepsum_list_pull_CONTENT sep_block_def)
    apply (simp add: map_index'_replicate_conv base_addr_def)
    done
  moreover have "?T ?t" using \<open>unat n>0\<close>
    by (auto simp add: alloc_tag_def sep_algebra_simps pred_lift_extract_simps)
  ultimately have "(?A ** ?T ** ?H) (?a + (?t + ?h))" 
    apply (intro SCI assms)
    apply (simp_all add: sep_algebra_simps)
    done
  thus ?thesis by (auto simp: sep_algebra_simps)
qed

  



lemma "0<n \<Longrightarrow> htriple \<box> (ll_malloc TYPE ('a::llvm_rep) n) (\<lambda>r. is_array (replicate (unat n) init) r ** alloc_tag (unat n) r)"
  apply vcg
  unfolding llvm_wp_def ll_malloc_def raw_malloc_def check_ptr_def POSTCOND_def
  apply (auto simp: run_simps word_less_nat_alt)
  
  apply (simp add: STATE_def heap_alloc_conv)
  apply (rule malloc_rule_aux)
  by auto

lemma alloc_tag_PTR_NULL[simp]: "alloc_tag (length xs) (PTR RP_NULL) = sep_false"  
  by (auto simp: alloc_tag_def)

lemma "STATE (EXACT (TAGS ((\<lambda>_. 0)(i:=TRIV len))) ** F) (HEAP h) \<Longrightarrow> (\<exists>b. i < length h \<and> h!i = Some b \<and> len=length b)"  
  apply (clarsimp simp: STATE_def sep_conj_def sep_heap_def)
  apply transfer
  apply (auto simp: sep_algebra_simps lift_ZERO)
  apply (auto simp: sep_tags_def)
  
  
lemma "htriple (is_array xs p ** alloc_tag (length xs) p) (ll_free p) (\<lambda>_. \<box>)"
  unfolding alloc_tag_def
  apply vcg
  unfolding llvm_wp_def ll_free_def raw_free_def ptr_to_addr'_def ptr_to_addr_def check_ptr_def POSTCOND_def
  apply (auto simp: run_simps split: raw_ptr.splits ptr.splits addr.splits)
  
  subgoal for F h bl
    apply (cases h)
    apply simp
    
    apply (auto simp: sep_conj_def STATE_def sep_heap_def)
    
    oops
    Intuitively: 
      sep_tags (HEAP x) at bl ha szero length
      but equal to length xs \<noteq> 0 
  
  
  oops
  apply (auto 
    simp: STATE_def is_array_def list_conj_map_index_EXACT_conv sepsum_list_pull_CONTENT
    simp: sep_algebra_simps sep_heap_def
    elim!: sep_conjE)
  apply (subst (asm) list_conj_map_index_EXACT_conv)
  apply simp
    

  
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
