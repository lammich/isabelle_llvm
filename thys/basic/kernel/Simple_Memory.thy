section \<open>Simple Memory Model\<close>
theory Simple_Memory
imports "../../lib/LLVM_Integer" "../../lib/LLVM_Float_Types" "../../lib/MM/MMonad" 
begin

  text \<open>Here, we combine a model of LLVM values, with our generic block-based memory model\<close>

  datatype llvm_ptr = is_null: PTR_NULL | is_addr: PTR_ADDR (the_addr: addr)
  hide_const (open) llvm_ptr.is_null llvm_ptr.is_addr llvm_ptr.the_addr

    
  lifting_update memory.lifting
  lifting_forget memory.lifting

          
  subsection \<open>LLVM Values\<close>
  
  datatype llvm_struct = 
    is_struct: VS_STRUCT (the_fields: "llvm_struct list") 
  | is_union: VS_UNION (the_variants: "llvm_struct list") 
  | is_int: VS_INT (the_width: nat)
  | is_single: VS_SINGLE
  | is_double: VS_DOUBLE
  | is_ptr: VS_PTR 
  hide_const (open) 
    llvm_struct.is_struct llvm_struct.the_fields
    llvm_struct.is_union llvm_struct.the_variants
    llvm_struct.is_ptr
    llvm_struct.is_single
    llvm_struct.is_double
    llvm_struct.is_int llvm_struct.the_width
  

  datatype 'v llvm_union = 
      is_zero_init: UN_ZERO_INIT (structs: "llvm_struct list")
    | is_sel: UN_SEL (lefts: "llvm_struct list") (the_val: 'v) (rights: "llvm_struct list")
  
  hide_const (open) 
    llvm_union.is_zero_init
    llvm_union.structs
    llvm_union.is_sel
    llvm_union.lefts
    llvm_union.the_val
    llvm_union.rights
  
    
      
  
  datatype llvm_val = 
    is_struct: LL_STRUCT (the_fields: "llvm_val list") 
  | is_union: LL_UNION (the_union: "llvm_val llvm_union") 
  | is_int: LL_INT (the_int: lint) 
  | is_single: LL_SINGLE (the_single: single)
  | is_double: LL_DOUBLE (the_double: double) (* 
      TODO: Similar to lint, we could encode different floating-point layouts here, 
        and restrict the code-generator to only accept the ones supported by LLVM.
    *)
  | is_ptr: LL_PTR (the_ptr: llvm_ptr)
  hide_const (open) 
    llvm_val.is_struct llvm_val.the_fields
    llvm_val.is_union llvm_val.the_union
    llvm_val.is_int llvm_val.the_int
    llvm_val.is_single llvm_val.the_single
    llvm_val.is_double llvm_val.the_double
    llvm_val.is_ptr llvm_val.the_ptr

  fun llvm_struct_of_union where
    "llvm_struct_of_union _ (UN_ZERO_INIT ss) = ss"
  | "llvm_struct_of_union sov (UN_SEL ls v rs) = (ls@sov v#rs)"

  fun vals_of_union where
    "vals_of_union (UN_ZERO_INIT _) = {}"
  | "vals_of_union (UN_SEL _ v _) = {v}"  
        
  lemma llvm_struct_of_union_cong[fundef_cong]: 
    "u=u' \<Longrightarrow> (\<And>x. x\<in>vals_of_union u' \<Longrightarrow> sov x = sov' x) \<Longrightarrow> llvm_struct_of_union sov u = llvm_struct_of_union sov' u'"
    by (cases u; auto)
  
  lemma vals_of_union_smaller[termination_simp]: "x \<in> vals_of_union un \<Longrightarrow> size x < Suc (size_llvm_union size un)" apply (cases un) by auto 
    
  fun llvm_struct_of_val where
    "llvm_struct_of_val (LL_STRUCT vs) = VS_STRUCT (map llvm_struct_of_val vs)"
  | "llvm_struct_of_val (LL_UNION un) = VS_UNION (llvm_struct_of_union llvm_struct_of_val un)"
  | "llvm_struct_of_val (LL_INT i) = VS_INT (width i)"
  | "llvm_struct_of_val (LL_SINGLE _) = VS_SINGLE"
  | "llvm_struct_of_val (LL_DOUBLE _) = VS_DOUBLE"
  | "llvm_struct_of_val (LL_PTR _) = VS_PTR"

  
  
  fun llvm_zero_initializer where
    "llvm_zero_initializer (VS_STRUCT vss) = LL_STRUCT (map llvm_zero_initializer vss)"
  | "llvm_zero_initializer (VS_UNION ss) = LL_UNION (UN_ZERO_INIT ss)"
  | "llvm_zero_initializer (VS_INT w) = LL_INT (lconst w 0)"
  | "llvm_zero_initializer (VS_SINGLE) = LL_SINGLE (single_of_word 0)"
  | "llvm_zero_initializer (VS_DOUBLE) = LL_DOUBLE (double_of_word 0)"
  | "llvm_zero_initializer VS_PTR = LL_PTR PTR_NULL"
  
  lemma struct_of_llvm_zero_initializer[simp]: "llvm_struct_of_val (llvm_zero_initializer s) = s"
    apply (induction s) 
    apply (simp_all add: map_idI)
    done

  (*type_synonym llvm_memory = "llvm_val memory"
  translations (type) "llvm_memory" \<leftharpoondown> (type) "llvm_val memory"
  *)

  type_synonym 'a llM = "('a,llvm_val) M"
  translations
    (type) "'a llM" \<leftharpoondown> (type) "('a, llvm_val) M"

    
  subsection \<open>Raw operations on values\<close>  
  
  
  fun llvm_union_len where
    "llvm_union_len (UN_ZERO_INIT ss) = length ss"
  | "llvm_union_len (UN_SEL ls v rs) = Suc (length ls + length rs)"
  
  fun llvm_union_can_dest where
    "llvm_union_can_dest (UN_ZERO_INIT ss) i \<longleftrightarrow> i < length ss"
  | "llvm_union_can_dest (UN_SEL ls v rs) i \<longleftrightarrow> i = length ls"

  fun llvm_union_dest where
    "llvm_union_dest (UN_ZERO_INIT ss) i = llvm_zero_initializer (ss!i)"
  | "llvm_union_dest (UN_SEL ls v rs) i = (if i=length ls then v else undefined ls v rs)"

  definition "llvm_union_can_make ss v i \<equiv> i<length ss \<and> llvm_struct_of_val v = ss!i"
  definition "llvm_union_make ss v i \<equiv> UN_SEL (take i ss) v (drop (Suc i) ss)"

  context
    fixes ss v i un
    assumes can_make: "llvm_union_can_make ss v i"
    defines [simp]: "un \<equiv> llvm_union_make ss v i"
  begin
    lemma un_make_simps[simp]:
      "llvm_union_len un = length ss"
      "llvm_union_can_dest un j \<longleftrightarrow> j=i"
      "j=i \<Longrightarrow> llvm_union_dest un j = v"
      "llvm_struct_of_union llvm_struct_of_val un = ss"
      using can_make
      by (auto simp: llvm_union_make_def llvm_union_can_make_def Cons_nth_drop_Suc)
      
  end  
  
    
    
  
  context
    includes monad_syntax_M
  begin
    
  definition llvm_extract_addr :: "llvm_val \<Rightarrow> addr llM" where
    "llvm_extract_addr v \<equiv> case v of LL_PTR (PTR_ADDR a) \<Rightarrow> return a | _ \<Rightarrow> fail"

  definition llvm_extract_ptr :: "llvm_val \<Rightarrow> llvm_ptr llM" where
    "llvm_extract_ptr v \<equiv> case v of LL_PTR p \<Rightarrow> return p | _ \<Rightarrow> fail"
    
  definition llvm_extract_sint :: "llvm_val \<Rightarrow> int llM" where
    "llvm_extract_sint v \<equiv> case v of LL_INT i \<Rightarrow> return (lint_to_sint i) | _ \<Rightarrow> fail" 
        
  definition llvm_extract_unat :: "llvm_val \<Rightarrow> nat llM" where
    "llvm_extract_unat v \<equiv> case v of LL_INT i \<Rightarrow> return (nat (lint_to_uint i)) | _ \<Rightarrow> fail" 

  definition llvm_extract_value :: "llvm_val \<Rightarrow> nat \<Rightarrow> llvm_val llM" where 
  "llvm_extract_value v i \<equiv> case v of 
    LL_STRUCT vs \<Rightarrow> doM {
      assert (i<length vs);
      return (vs!i)
    }
  | _ \<Rightarrow> fail"
      
  definition llvm_insert_value :: "llvm_val \<Rightarrow> llvm_val \<Rightarrow> nat \<Rightarrow> llvm_val llM" where 
  "llvm_insert_value v x i \<equiv> case v of 
    LL_STRUCT vs \<Rightarrow> doM {
      assert (i<length vs);
      assert (llvm_struct_of_val (vs!i) = llvm_struct_of_val x);
      return (LL_STRUCT (vs[i:=x]))
    }
  | _ \<Rightarrow> fail"

  definition llvm_dest_union :: "llvm_val \<Rightarrow> nat \<Rightarrow> llvm_val llM" where
    "llvm_dest_union v i \<equiv> case v of
      LL_UNION un \<Rightarrow> doM {
        assert llvm_union_can_dest un i;
        return llvm_union_dest un i
      }
    | _ \<Rightarrow> fail"
  
  definition llvm_make_union :: "llvm_struct \<Rightarrow> llvm_val \<Rightarrow> nat \<Rightarrow> llvm_val llM" where
    "llvm_make_union s x i \<equiv> case s of 
      VS_UNION ss \<Rightarrow> do {
        assert (llvm_union_can_make ss x i);
        return LL_UNION (llvm_union_make ss x i)
      }
    | _ \<Rightarrow> fail"
  
  subsection \<open>Interface functions\<close>
  
  subsubsection \<open>Typed arguments\<close>
    
  (* TODO: redundancy with is_valid_addr! *)
  definition llvmt_check_addr :: "addr \<Rightarrow> unit llM" where "llvmt_check_addr a \<equiv> doM { 
    Mvalid_addr a
  }"
    
  definition llvmt_load :: "addr \<Rightarrow> llvm_val llM" where "llvmt_load a \<equiv> doM { 
    Mload a
  }"
  
  definition "llvmt_store x a \<equiv> doM { 
    xorig \<leftarrow> llvmt_load a; 
    assert llvm_struct_of_val x = llvm_struct_of_val xorig;
    Mstore a x
  }"
  
  definition "llvmt_alloc s n \<equiv> doM {
    Mmalloc (replicate n (llvm_zero_initializer s))
  }"
  
  definition llvmt_free :: "nat \<Rightarrow> unit llM" where "llvmt_free b \<equiv> doM {
    Mfree b
  }"  

  definition "llvmt_freep p \<equiv> doM {
    assert llvm_ptr.is_addr p;
    let a = llvm_ptr.the_addr p;
  
    assert addr.index a=0;
    llvmt_free (addr.block a);
    return ()
  }"  

  definition "llvmt_allocp s n \<equiv> doM {
    b \<leftarrow> llvmt_alloc s n;
    return (PTR_ADDR (ADDR b 0))
  }"
    
  
  definition llvmt_check_ptr :: "llvm_ptr \<Rightarrow> unit llM" where "llvmt_check_ptr p \<equiv> 
    if llvm_ptr.is_null p then return ()
    else doM {
      let a = llvm_ptr.the_addr p;
      Mvalid_addr a \<comment> \<open>TODO: support 1-beyond-end pointers!\<close>
    }"
      
  definition "llvmt_ofs_ptr p ofs \<equiv> doM {
    assert (llvm_ptr.is_addr p);
    let a = llvm_ptr.the_addr p;
    let b = addr.block a;
    let i = addr.index a;
    let i = i + ofs;
    let r = PTR_ADDR (ADDR b i);
    llvmt_check_ptr r;
    return r
  }"  
    
  definition "llvmt_check_ptrcmp p\<^sub>1 p\<^sub>2 \<equiv> 
    if p\<^sub>1=PTR_NULL \<or> p\<^sub>2=PTR_NULL then 
      return () 
    else doM {
      llvmt_check_ptr p\<^sub>1;
      llvmt_check_ptr p\<^sub>2
    }"
  
  definition "llvmt_ptr_eq p\<^sub>1 p\<^sub>2 \<equiv> doM {
    llvmt_check_ptrcmp p\<^sub>1 p\<^sub>2;
    return (p\<^sub>1 = p\<^sub>2)
  }"
  
  definition "llvmt_ptr_neq p\<^sub>1 p\<^sub>2 \<equiv> doM {
    llvmt_check_ptrcmp p\<^sub>1 p\<^sub>2;
    return (p\<^sub>1 \<noteq> p\<^sub>2)
  }"
  
  subsubsection \<open>Embedded arguments\<close>

  definition "llvm_load a \<equiv> doM {
    a \<leftarrow> llvm_extract_addr a;
    llvmt_load a
  }"
  
  definition "llvm_store x a \<equiv> doM {
    a \<leftarrow> llvm_extract_addr a;
    llvmt_store x a
  }"
  
  definition "llvm_alloc s n \<equiv> doM {
    n \<leftarrow> llvm_extract_unat n;
    p \<leftarrow> llvmt_allocp s n;
    return (LL_PTR p)
  }"

  definition "llvm_extract_base_block a \<equiv> case a of ADDR b i \<Rightarrow> if i=0 then return b else fail"
  
  definition "llvm_free p \<equiv> doM {
    p \<leftarrow> llvm_extract_ptr p;
    llvmt_freep p
  }"
  
  definition "llvm_ofs_ptr p ofs \<equiv> doM {
    p \<leftarrow> llvm_extract_ptr p;
    ofs \<leftarrow> llvm_extract_sint ofs;
    r \<leftarrow> llvmt_ofs_ptr p ofs;
    return (LL_PTR r)
  }"  
  
  
  definition "llvm_ptr_eq p\<^sub>1 p\<^sub>2 \<equiv> doM {
    p\<^sub>1 \<leftarrow> llvm_extract_ptr p\<^sub>1;
    p\<^sub>2 \<leftarrow> llvm_extract_ptr p\<^sub>2;
    r \<leftarrow> llvmt_ptr_eq p\<^sub>1 p\<^sub>2;
    return (LL_INT (bool_to_lint r))
  }"  
  
  definition "llvm_ptr_neq p\<^sub>1 p\<^sub>2 \<equiv> doM {
    p\<^sub>1 \<leftarrow> llvm_extract_ptr p\<^sub>1;
    p\<^sub>2 \<leftarrow> llvm_extract_ptr p\<^sub>2;
    r \<leftarrow> llvmt_ptr_neq p\<^sub>1 p\<^sub>2;
    return (LL_INT (bool_to_lint r))
  }"  
  
end
end
