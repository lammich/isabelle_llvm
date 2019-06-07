theory LLVM_Memory
imports Monad2 LLVM_Integer LLVM_Pre_Syntax Definition_Utils
begin

  section \<open>Monad Setup\<close>

  datatype err = is_static: STATIC_ERROR string | MEM_ERROR | UNINIT_ERROR | OVERFLOW_ERROR
  hide_const (open) is_static

  abbreviation lift_lens_static ("'(_')\<^sub>S")
    where "lift_lens_static \<equiv> lift_lens (STATIC_ERROR ''lens'')"

  abbreviation lift_lens_mem ("'(_')\<^sub>M")
    where "lift_lens_mem \<equiv> lift_lens MEM_ERROR"

  abbreviation lift_lens_uninit ("'(_')\<^sub>U")
    where "lift_lens_uninit \<equiv> lift_lens UNINIT_ERROR"

    
  section \<open>Values\<close>  
  
  subsection \<open>Pointers\<close>
  datatype block_addr = BLOCK_ADDR (the_block: nat)
  
  datatype va_item = VA_ARRAY_IDX (aidx: nat) | VA_FIELD_IDX (fidx: nat)
  hide_const (open) aidx fidx
  define_lenses (open) va_item

  type_synonym vaddr = "va_item list"

  datatype addr = ADDR (block_addr: block_addr) (vaddr: vaddr)
  hide_const (open) block_addr vaddr
  define_lenses (open) addr

  subsection \<open>Structured Values\<close>
  
  datatype val =
    VINT (lint: "nat + lint")   \<comment> \<open>\<open>width + lint\<close>\<close>
  | VPTR (addr: "addr option option")
  | VARRAY (items: "val list")
  | VSTRUCT (fields: "val list")

  hide_const (open) lint addr items fields
  define_lenses (open) val
    

  fun uninit where
    "uninit (TINT w) = VINT (Inl w)"
  | "uninit (TPTR _) = VPTR None"
  | "uninit (TARRAY n ty) = VARRAY (replicate n (uninit ty))"
  | "uninit (TSTRUCT tys) = VSTRUCT (map uninit tys)"

  
  fun wpi_width where
    "wpi_width (Inl w) = w"
  | "wpi_width (Inr i) = width i"
  

  fun same_struct :: "val \<Rightarrow> val \<Rightarrow> bool" where
    "same_struct (VINT a) (VINT b) \<longleftrightarrow> wpi_width a = wpi_width b"
  | "same_struct (VPTR _) (VPTR _) \<longleftrightarrow> True"
  | "same_struct (VARRAY xs) (VARRAY ys) \<longleftrightarrow> list_all2 same_struct xs ys"
  | "same_struct (VSTRUCT xs) (VSTRUCT ys) \<longleftrightarrow> list_all2 same_struct xs ys"
  | "same_struct _ _ \<longleftrightarrow> False"

  lemma same_struct_refl[simp]: "same_struct v v"
    apply (induction v)
    apply (auto simp: list.rel_refl_strong)
    done

  lemma same_struct_sym: "same_struct a b \<Longrightarrow> same_struct b a"
    apply (induction a b rule: same_struct.induct)
    apply (auto simp: list_all2_conv_all_nth)
    done

  lemma same_struct_trans[trans]: "same_struct a b \<Longrightarrow> same_struct b c \<Longrightarrow> same_struct a c"
    apply (induction a b arbitrary: c rule: same_struct.induct)
    apply simp_all
    apply (case_tac c; auto simp: list_all2_conv_all_nth in_set_conv_nth; blast)+
    done
    
  definition "put_same_struct L a b \<equiv> doM {
    v \<leftarrow> mget L b;
    fcheck (STATIC_ERROR ''val-struct change'') (same_struct a v);
    mput L a b
  }"
  
    
    
  subsection \<open>Conversion to Type-Representations\<close>  
  definition to_ptr where
    "to_ptr v \<equiv> case (v) of
        (VPTR (Some p)) \<Rightarrow> return p
      | (VPTR None) \<Rightarrow> fail UNINIT_ERROR
      | _ \<Rightarrow> fail (STATIC_ERROR ''to_ptr'')"

  definition to_addr where
    "to_addr v \<equiv> case (v) of
        (VPTR (Some (Some p))) \<Rightarrow> return p
      | (VPTR (Some None)) \<Rightarrow> fail MEM_ERROR
      | (VPTR None) \<Rightarrow> fail UNINIT_ERROR
      | _ \<Rightarrow> fail (STATIC_ERROR ''to_addr'')"

  definition to_lint where
    "to_lint v \<equiv> case (v) of
        (VINT (Inr i)) \<Rightarrow> return i
      | (VINT (Inl _)) \<Rightarrow> fail UNINIT_ERROR
      | _ \<Rightarrow> fail (STATIC_ERROR ''to_int'')"

  definition to_uint where
    "to_uint v \<equiv> doM { v\<leftarrow>to_lint v; return (lint_to_uint v) }"
      
  definition to_sint where
    "to_sint v \<equiv> doM { v\<leftarrow>to_lint v; return (lint_to_sint v) }"
      
  definition to_nat where
    "to_nat v \<equiv> doM { v \<leftarrow> to_uint v; return (nat v) }"
    
  definition to_bool where
    "to_bool v \<equiv> doM {
      v \<leftarrow> to_lint v;
      fcheck (STATIC_ERROR ''to_bool'') (width v = 1);
      return (lint_to_bool v)
    }"
    
  definition "from_addr addr \<equiv> return (VPTR (Some (Some addr)))"
  definition "from_lint i \<equiv> return (VINT (Inr i))"
  definition "from_bool b \<equiv> return (VINT (Inr (bool_to_lint b)))"
    
  
  definition "op_lift1 T R f x \<equiv> doM {
    x \<leftarrow> T x;
    r \<leftarrow> f x;
    R r
  }"
    
  definition "op_lift2 T1 T2 R f x1 x2 \<equiv> doM {
    x1 \<leftarrow> T1 x1;
    x2 \<leftarrow> T2 x2;
    r \<leftarrow> f x1 x2;
    R r
  }"

  definition "op_lift3 T1 T2 T3 R f x1 x2 x3 \<equiv> doM {
    x1 \<leftarrow> T1 x1;
    x2 \<leftarrow> T2 x2;
    x3 \<leftarrow> T3 x3;
    r \<leftarrow> f x1 x2 x3;
    R r
  }"
  
      
  section \<open>Memory\<close>  
    
  datatype block_type = ON_STACK | ON_HEAP
  hide_const (open) ON_STACK ON_HEAP
    
  datatype memory = MEM (mem: "(val \<times> block_type) option list")
  hide_const (open) mem
  define_lenses memory

  abbreviation "memL \<equiv> (mem\<^sub>L)\<^sub>S"
  abbreviation "idxL i \<equiv> (idx\<^sub>L i)\<^sub>M"

  definition "mem_empty \<equiv> MEM []"

  
  subsection \<open>Allocate and Free\<close>

  definition "block_allocate bty v \<equiv> (doM {
    \<mu>\<leftarrow>use memL;
    memL %= (\<lambda>\<mu>. \<mu>@[Some (v,bty)]);
    return (BLOCK_ADDR (length \<mu>))
  })"

  definition "block_free bty b \<equiv> doM {
    let L = memL \<bullet> idxL (the_block b);
    (_,ty')\<leftarrow>use (L \<bullet> (the\<^sub>L)\<^sub>M);
    fcheck MEM_ERROR (bty=ty');
    L := None
  }"

  definition "llb_malloc ty n \<equiv> doM {
    fcheck MEM_ERROR (n>0);
    let n = nat n;
    let v = uninit (TARRAY n ty);
    r \<leftarrow> block_allocate block_type.ON_HEAP v;
    return (ADDR r [VA_ARRAY_IDX 0])
  }"
  
  definition "llb_free addr \<equiv> doM {
    case addr of
        ADDR b [VA_ARRAY_IDX 0] \<Rightarrow> block_free block_type.ON_HEAP b
      | _ \<Rightarrow> fail MEM_ERROR
  }"
  
  definition "blockL' b \<equiv> memL \<bullet> (idx\<^sub>L (the_block b))\<^sub>S \<bullet> (the\<^sub>L)\<^sub>M"
  definition "blockL b \<equiv> memL \<bullet> (idx\<^sub>L (the_block b))\<^sub>S \<bullet> (the\<^sub>L)\<^sub>M \<bullet> (fst\<^sub>L)\<^sub>S"

  lemma blockL_elens[simp]: 
    "elens (blockL b)"
    "elens (blockL' b)"
    by (auto simp: blockL_def blockL'_def)

  subsection \<open>Load and Store\<close>
  
  definition "struct_field\<^sub>L i \<equiv> (val.fields\<^sub>L \<bullet>\<^sub>L idx\<^sub>L i)\<^sub>S"
  (*definition "static_array_item\<^sub>L i \<equiv> (val.items\<^sub>L \<bullet>\<^sub>L idx\<^sub>L i)\<^sub>S"*)
  definition "array_item\<^sub>L i \<equiv> (val.items\<^sub>L)\<^sub>S \<bullet> idxL i"

  fun lens_of_vai where
    "lens_of_vai (VA_ARRAY_IDX i) = array_item\<^sub>L i"
  | "lens_of_vai (VA_FIELD_IDX i) = struct_field\<^sub>L i"

  definition "lens_of_vaddr va \<equiv> foldr (\<lambda>vai p. lens_of_vai vai \<bullet> p) va (id\<^sub>L)\<^sub>S"

  fun lens_of_addr where
    "lens_of_addr (ADDR b va) = blockL b \<bullet> lens_of_vaddr va"
  
  
  definition llb_load where
    "llb_load addr \<equiv> use (lens_of_addr addr)"
    
  definition llb_store where
    "llb_store v addr \<equiv> doM {
      ov \<leftarrow> use (lens_of_addr addr);
      fcheck (STATIC_ERROR ''mem-struct change'') (same_struct v ov);
      lens_of_addr addr := v
    }"  

    
  subsection \<open>GEP, Insert, and Extract\<close>
  
  
  definition llb_ofs_addr :: "addr \<Rightarrow> int \<Rightarrow> _" where
    "llb_ofs_addr a i \<equiv> map_lens (addr.vaddr\<^sub>L\<bullet>\<^sub>Llast\<^sub>L\<bullet>\<^sub>Lva_item.aidx\<^sub>L)\<^sub>M (\<lambda>idx. doM {
      let idx = int idx + i;
      fcheck MEM_ERROR (idx\<ge>0);
      return (nat idx)
    }) a"
  
  definition llb_idx_array :: "addr \<Rightarrow> int \<Rightarrow> _" where
    "llb_idx_array a i \<equiv> map_lens (addr.vaddr\<^sub>L)\<^sub>S (\<lambda>x. doM {
      fcheck MEM_ERROR (i\<ge>0);
      return (x@[VA_ARRAY_IDX (nat i)])
    } ) a"
  
  definition llb_idx_field :: "addr \<Rightarrow> nat \<Rightarrow> _" where
    "llb_idx_field a i \<equiv> map_lens (addr.vaddr\<^sub>L)\<^sub>S (\<lambda>x. doM {
      return (x@[VA_FIELD_IDX i])
    } ) a"
  
  definition ll_insert_s_value' where "ll_insert_s_value' bv ev idx \<equiv> put_same_struct (struct_field\<^sub>L idx) ev bv"
  definition ll_extract_s_value' where "ll_extract_s_value' bv idx \<equiv> mget (struct_field\<^sub>L idx) bv"
  definition ll_insert_a_value' where "ll_insert_a_value' bv ev idx \<equiv> put_same_struct (array_item\<^sub>L idx) ev bv"
  definition ll_extract_a_value' where "ll_extract_a_value' bv idx \<equiv> mget (array_item\<^sub>L idx) bv"
    
    
    
section \<open>Arithmetic\<close>  
  
  definition "op_arith2 ovf f x1 x2 = doM {
    fcheck (STATIC_ERROR ''arith2 incompatible widths'') (width x1 = width x2);
    fcheck (OVERFLOW_ERROR) (\<not>ovf x1 x2);
    return (f x1 x2)
  }"

  definition "op_lift_arith2 ovf f \<equiv> op_lift2 to_lint to_lint from_lint (op_arith2 ovf f)"
  definition "op_lift_arith2' \<equiv> op_lift_arith2 (\<lambda>_ _. False)"
  definition "op_lift_cmp2 f \<equiv> op_lift2 to_lint to_lint from_bool (op_arith2 (\<lambda>_ _. False) f)"
  
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

  definition "to_iTw ty \<equiv> case ty of TINT w \<Rightarrow> return w | _ \<Rightarrow> fail (STATIC_ERROR ''Expected int type'')"
  
  definition "shift_ovf a n \<equiv> nat (lint_to_uint n) \<ge> width a"
  
  definition "bitSHL' a n \<equiv> bitSHL a (nat (lint_to_uint n))"
  definition "bitASHR' a n \<equiv> bitASHR a (nat (lint_to_uint n))"
  definition "bitLSHR' a n \<equiv> bitLSHR a (nat (lint_to_uint n))"
  
section \<open>LLVM Operations\<close>
  
  type_synonym llM = "(_,unit,memory,err) M"

  definition ll_add :: "val \<Rightarrow> val \<Rightarrow> llM" where "ll_add \<equiv> op_lift_arith2' (+)"
  definition ll_sub :: "val \<Rightarrow> val \<Rightarrow> llM" where "ll_sub \<equiv> op_lift_arith2' (-)"
  definition ll_mul :: "val \<Rightarrow> val \<Rightarrow> llM" where "ll_mul \<equiv> op_lift_arith2' ( * )"
  definition ll_udiv :: "val \<Rightarrow> val \<Rightarrow> llM" where "ll_udiv \<equiv> op_lift_arith2' (div)"
  definition ll_urem :: "val \<Rightarrow> val \<Rightarrow> llM" where "ll_urem \<equiv> op_lift_arith2' (mod)"
  definition ll_sdiv :: "val \<Rightarrow> val \<Rightarrow> llM" where "ll_sdiv \<equiv> op_lift_arith2 sdivrem_ovf (div\<^sub>s)"
  definition ll_srem :: "val \<Rightarrow> val \<Rightarrow> llM" where "ll_srem \<equiv> op_lift_arith2 sdivrem_ovf (rem\<^sub>s)"
  definition ll_shl :: "val \<Rightarrow> val \<Rightarrow> llM" where "ll_shl \<equiv> op_lift_arith2 shift_ovf bitSHL'"  
  definition ll_lshr :: "val \<Rightarrow> val \<Rightarrow> llM" where "ll_lshr \<equiv> op_lift_arith2 shift_ovf bitLSHR'"  
  definition ll_ashr :: "val \<Rightarrow> val \<Rightarrow> llM" where "ll_ashr \<equiv> op_lift_arith2 shift_ovf bitASHR'"
  definition ll_trunc :: "val \<Rightarrow> type \<Rightarrow> llM" where "ll_trunc \<equiv> op_lift2 to_lint to_iTw from_lint llb_trunc"
  definition ll_sext :: "val \<Rightarrow> type \<Rightarrow> llM" where "ll_sext \<equiv> op_lift2 to_lint to_iTw from_lint llb_sext"
  definition ll_zext :: "val \<Rightarrow> type \<Rightarrow> llM" where "ll_zext \<equiv> op_lift2 to_lint to_iTw from_lint llb_zext"

  definition ll_and :: "val \<Rightarrow> val \<Rightarrow> llM" where "ll_and \<equiv> op_lift_arith2' (AND)"
  definition ll_or :: "val \<Rightarrow> val \<Rightarrow> llM" where "ll_or \<equiv> op_lift_arith2' (OR)"
  definition ll_xor :: "val \<Rightarrow> val \<Rightarrow> llM" where "ll_xor \<equiv> op_lift_arith2' (XOR)"
  
  definition ll_icmp_eq :: "val \<Rightarrow> val \<Rightarrow> llM" where "ll_icmp_eq \<equiv> op_lift_cmp2 (=)"
  definition ll_icmp_ne :: "val \<Rightarrow> val \<Rightarrow> llM" where "ll_icmp_ne \<equiv> op_lift_cmp2 (\<noteq>)"
  definition ll_icmp_sle :: "val \<Rightarrow> val \<Rightarrow> llM" where "ll_icmp_sle \<equiv> op_lift_cmp2 (\<le>\<^sub>s)"
  definition ll_icmp_slt :: "val \<Rightarrow> val \<Rightarrow> llM" where "ll_icmp_slt \<equiv> op_lift_cmp2 (<\<^sub>s)"
  definition ll_icmp_ule :: "val \<Rightarrow> val \<Rightarrow> llM" where "ll_icmp_ule \<equiv> op_lift_cmp2 (\<le>)"
  definition ll_icmp_ult :: "val \<Rightarrow> val \<Rightarrow> llM" where "ll_icmp_ult \<equiv> op_lift_cmp2 (<)"
  
  definition ll_malloc :: "type \<Rightarrow> val \<Rightarrow> llM" where "ll_malloc \<equiv> op_lift2 return to_uint from_addr llb_malloc"
  definition ll_free :: "val \<Rightarrow> llM" where "ll_free \<equiv> op_lift1 to_addr return llb_free"
  
  definition ll_load :: "val \<Rightarrow> llM" where "ll_load \<equiv> op_lift1 to_addr return llb_load"
  definition ll_store :: "val \<Rightarrow> val \<Rightarrow> llM" where "ll_store \<equiv> op_lift2 return to_addr return llb_store"
    
  definition ll_insert_s_value :: "val \<Rightarrow> val \<Rightarrow> nat \<Rightarrow> llM" where "ll_insert_s_value bv ev idx \<equiv> put_same_struct (struct_field\<^sub>L idx) ev bv"
  definition ll_extract_s_value :: "val \<Rightarrow> nat \<Rightarrow> llM" where "ll_extract_s_value bv idx \<equiv> mget (struct_field\<^sub>L idx) bv"
  definition ll_insert_a_value :: "val \<Rightarrow> val \<Rightarrow> nat \<Rightarrow> llM" where "ll_insert_a_value bv ev idx \<equiv> put_same_struct (array_item\<^sub>L idx) ev bv"
  definition ll_extract_a_value :: "val \<Rightarrow> nat \<Rightarrow> llM" where "ll_extract_a_value bv idx \<equiv> mget (array_item\<^sub>L idx) bv"
  
  definition ll_ofs_addr :: "val \<Rightarrow> val \<Rightarrow> llM" where "ll_ofs_addr \<equiv> op_lift2 to_addr to_sint from_addr llb_ofs_addr"
  definition ll_idx_array :: "val \<Rightarrow> val \<Rightarrow> llM" where "ll_idx_array \<equiv> op_lift2 to_addr to_sint from_addr llb_idx_array"
  definition ll_idx_field :: "val \<Rightarrow> nat \<Rightarrow> llM" where "ll_idx_field \<equiv> op_lift2 to_addr return from_addr llb_idx_field"
    
  definition "llop_iconst w i \<equiv> VINT (Inr (lconst w i))"
  definition "llop_undef ty \<equiv> uninit ty"
  
  definition llc_if :: "val \<Rightarrow> llM \<Rightarrow> llM \<Rightarrow> llM" where 
    "llc_if b t e \<equiv> doM {
      b \<leftarrow> to_bool b;
      if b then t else e
    }"

  definition llc_while :: "(val \<Rightarrow> llM) \<Rightarrow> (val \<Rightarrow> llM) \<Rightarrow> val \<Rightarrow> llM" where
    "llc_while b f s\<^sub>0 \<equiv> mwhile (\<lambda>s. b s \<bind> to_bool) f s\<^sub>0"
    
  
  abbreviation "ty_i64xi64 \<equiv> TSTRUCT [TINT 64, TINT 64]"
  
  definition exp where "exp i \<equiv> doM {
    s \<leftarrow> ll_insert_s_value (llop_undef ty_i64xi64) (llop_iconst 64 1) 0;
    s \<leftarrow> ll_insert_s_value s i 1;
    
    s \<leftarrow> llc_while 
      (\<lambda>s. doM {
        c \<leftarrow> ll_extract_s_value s 0;
        i \<leftarrow> ll_extract_s_value s 1;
        ll_icmp_ne i (llop_iconst 64 0)
      })
      (\<lambda>s. doM {
        c \<leftarrow> ll_extract_s_value s 0;
        i \<leftarrow> ll_extract_s_value s 1;
        c \<leftarrow> ll_mul c (llop_iconst 64 2);
        i \<leftarrow> ll_sub i (llop_iconst 64 1);
        s \<leftarrow> ll_insert_s_value (llop_undef ty_i64xi64) c 0;
        s \<leftarrow> ll_insert_s_value s i 1;
        return s
      })
      s;
    
    c \<leftarrow> ll_extract_s_value s 0;
    return c
  }"

  
  definition exec :: "(val, unit, memory, err) M \<Rightarrow> (int, unit, memory, err) mres"
    where "exec m \<equiv> run (m \<bind> to_sint) mem_empty"
  
  term pretty_val    
    
  value "exec (ll_insert_s_value (llop_undef ty_i64xi64) (llop_iconst 64 1) 0)"
  
  value "exec (exp (llop_iconst 64 5))"
  
  thm exp_def[unfolded llc_while_def mwhile_def]
  
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
      gen_tac = Partial_Function.mono_tac
    }
  *}
    
    
  
  prepare_code_thms exp_def
  print_theorems
  
  thm exp.code
  
  lemma aux: "(NO_MATCH (bind mm ff) (f x)) \<Longrightarrow> doM { x\<leftarrow>m; f x } = doM { x\<leftarrow>m; r\<leftarrow>f x; return r }" by simp
  
  declare [[eta_contract = false]]

  ML_file "LLVM_Builder.ml"
  
  ML \<open>
  
    structure LLVM_Compiler = struct
      fun normalize_code_thm ctxt thm = let
        fun ensure_abs (t as Abs _) = t
          | ensure_abs t = @{mk_term "\<lambda>x. ?t x"}
      
        fun normalize_bind1 t = let
          val (f,args) = strip_comb t
          val _ = is_Const f orelse is_Free f orelse raise TERM ("Invalid head",[f])
  
          val _ = @{print} f
                  
          fun is_M_type (Type (@{type_name M},_)) = true | is_M_type _ = false
          
          val args_is_M = fastype_of f |> binder_types |> map is_M_type
                  
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
      
      datatype bcontext = BCTXT of LLVM_Builder.value Symtab.table * LLVM_Builder.value option list
      
      fun bctxt_add_bound v (BCTXT (args,bnds)) = BCTXT (args,v::bnds)
      
      fun bctxt_lookup_bound (BCTXT (_,bnds)) i = nth bnds i |> the
      fun bctxt_lookup_free (BCTXT (args,_)) n = Symtab.lookup args n |> the
      fun val_of_op bc (Bound i) = bctxt_lookup_bound bc i
        | val_of_op bc (Free (n,_)) = bctxt_lookup_free bc n
        | val_of_op _ t = raise TERM ("val_of_op", [t])
      
      fun compile_do_block b bc t = let
        fun bld_arith_instr bc iname dst op1 op2 = SOME (LLVM_Builder.mk_arith_instr iname b dst (val_of_op bc op1) (val_of_op bc op2))
      
      
        fun bld_cmd bc dst @{mpat "ll_add ?op1.0 ?op2.0"} = bld_arith_instr bc "add" dst op1 op2
      
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
      
      fun compile_eq
      
      xxx, skipped from here to do SHALLOW embedding of types!
      
    end
  \<close>
  
  
    
  ML_val \<open>
    let 
    
      fun ensure_abs (t as Abs _) = t
        | ensure_abs t = @{mk_term "\<lambda>x. ?t x"}
    
      fun normalize_bind1 t = let
        val (f,args) = strip_comb t
        val _ = is_Const f orelse is_Free f orelse raise TERM ("Invalid head",[f])

        val _ = @{print} f
                
        fun is_M_type (Type (@{type_name M},_)) = true | is_M_type _ = false
        
        val args_is_M = fastype_of f |> binder_types |> map is_M_type
                
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
        
      val ctxt = @{context} 
    in
      @{thms exp.code}
      |> map (simplify (put_simpset HOL_ss ctxt addsimps @{thms bind_laws atomize_eq}))
      |> map (Conv.fconv_rule (HOLogic.Trueprop_conv (Refine_Util.f_tac_conv ctxt normalize_eq (norm_tac ctxt))))
      
    end
  
  \<close>
  
  find_theorems "(_\<equiv>_)" "(_=_)"
  
  
  value "exec (exp (llop_iconst 64 5))"
  
  
  ML_val implode
  
  oops
    xxx, ctd here: 
      Produce llvm code from code equations. Generate one procedure per equation. 
      Use LLVM-generator interface in ML
      
      export_code
    
    ML_val \<open>
      val (s,context) = Name.variant "tmp" Name.context
      val (t,context) = Name.variant "tmp" context
      
      
    
    \<close>
    
    ML_val \<open>open Int\<close>

end
