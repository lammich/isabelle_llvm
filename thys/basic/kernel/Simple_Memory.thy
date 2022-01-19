theory Simple_Memory
imports "../../lib/LLVM_Integer" "../../lib/LLVM_Double"  "../../lib/Monad" 
begin

  (* TODO: Move *)
    


  subsection \<open>Simple Memory Model\<close>

  text \<open>Note: for technical reasons (better algebraic properties), we model the index as integer,
    though valid addresses always have non-negative index\<close>
  datatype llvm_addr = ADDR (block: nat) (idx: int)
  hide_const (open) llvm_addr.block llvm_addr.idx

  datatype llvm_ptr = is_null: PTR_NULL | is_addr: PTR_ADDR (the_addr: llvm_addr)
  hide_const (open) llvm_ptr.is_null llvm_ptr.is_addr llvm_ptr.the_addr

  
  datatype err = is_static: STATIC_ERROR string | PAR_ERROR | MEM_ERROR | UNINIT_ERROR | OVERFLOW_ERROR
  hide_const (open) is_static

  
  datatype llvm_macc = MACC (reads: "llvm_addr set") (writes: "llvm_addr set")
  hide_const (open) llvm_macc.reads llvm_macc.writes
  
  instantiation llvm_macc :: interference
  begin
    definition "0 \<equiv> MACC {} {}"
    definition "a+b \<equiv> MACC (llvm_macc.reads a \<union> llvm_macc.reads b) (llvm_macc.writes a \<union> llvm_macc.writes b)"
  
    definition "nointer a b \<equiv> 
      llvm_macc.writes a \<inter> (llvm_macc.reads b \<union> llvm_macc.writes b) = {}
    \<and> llvm_macc.writes b \<inter> (llvm_macc.reads a \<union> llvm_macc.writes a) = {}"
      
    instance
      apply standard
      unfolding zero_llvm_macc_def plus_llvm_macc_def nointer_llvm_macc_def
      by (auto)
    
  end
  
  abbreviation "macc_read addrs \<equiv> MACC addrs {}"
  abbreviation "macc_write addrs \<equiv> MACC {} addrs"
  
  text \<open>Double-check:\<close>
  lemma 
    "llvm_macc.reads (macc_read a) = a"
    "llvm_macc.writes (macc_read a) = {}"
    "llvm_macc.reads (macc_write a) = {}"
    "llvm_macc.writes (macc_write a) = a"
    by auto
  
  
    
  typedef 'a memory = "UNIV :: 'a list option list set" by simp
  setup_lifting type_definition_memory

  lift_definition f_valid_addr :: "llvm_addr \<Rightarrow> 'a memory \<Rightarrow> bool" is
    "\<lambda>(ADDR b i) \<Rightarrow> \<lambda>m. 0\<le>i \<and> b<length m \<and> m!b\<noteq>None \<and> nat i<length (the (m!b))" .

  lift_definition f_valid_ptr_addr :: "llvm_addr \<Rightarrow> 'a memory \<Rightarrow> bool" is
    "\<lambda>(ADDR b i) \<Rightarrow> \<lambda>m. 0\<le>i \<and> b<length m \<and> m!b\<noteq>None \<and> nat i\<le>length (the (m!b))" .

  definition f_valid_ptr :: "llvm_ptr \<Rightarrow> 'a memory \<Rightarrow> bool" where
    "f_valid_ptr p m \<equiv> llvm_ptr.is_null p \<or> (llvm_ptr.is_addr p \<and> f_valid_ptr_addr (llvm_ptr.the_addr p) m)"
    
          
  lift_definition f_load :: "llvm_addr \<Rightarrow> 'a memory \<Rightarrow> 'a" is
    "\<lambda>(ADDR b i) \<Rightarrow> \<lambda>m. the (m!b) ! nat i" .
    
  lift_definition f_store :: "llvm_addr \<Rightarrow> 'a \<Rightarrow> 'a memory \<Rightarrow> 'a memory" is
    "\<lambda>(ADDR b i) \<Rightarrow> \<lambda>x m. m[b := Some ((the (m!b)) [nat i := x] )]" .
    
  lift_definition f_valid_block :: "nat \<Rightarrow> 'a memory \<Rightarrow> bool" is
    "\<lambda>b m. b<length m \<and> m!b\<noteq>None" .

  lift_definition f_block_size :: "nat \<Rightarrow> 'a memory \<Rightarrow> nat" is
    "\<lambda>b m. length (the (m!b))" .

  lift_definition f_freed_block :: "nat \<Rightarrow> 'a memory \<Rightarrow> bool" is
    "\<lambda>b m. b<length m \<and> m!b=None" .
            
  lift_definition f_alloc :: "'a \<Rightarrow> nat \<Rightarrow> 'a memory \<Rightarrow> nat \<times> 'a memory" is
    "\<lambda>x n m. (length m, m@[Some (replicate n x)])" .
  
  lift_definition f_free :: "nat \<Rightarrow> 'a memory \<Rightarrow> 'a memory" is
    "\<lambda>b m. m[b:=None]" .
    
  
  lemma f_load_store[simp]: "f_valid_addr a m \<Longrightarrow> f_load a (f_store a x m) = x"  
    apply transfer
    by (auto split: llvm_addr.split)
    
  lemma f_store_load[simp]: "f_valid_addr a m \<Longrightarrow> f_store a (f_load a m) m = m"  
    apply transfer
    by (auto split: llvm_addr.split)

  lemma f_store_store[simp]: "f_valid_addr a m \<Longrightarrow> f_store a x (f_store a y m) = f_store a x m"  
    apply transfer
    by (auto split: llvm_addr.split)

  lemma f_valid_store[simp]: "f_valid_addr a m \<Longrightarrow> f_valid_addr a' (f_store a x m) \<longleftrightarrow> f_valid_addr a' m"
    apply transfer
    by (clarsimp split: llvm_addr.split simp: nth_list_update) 
    
  lemma f_store_indep: "f_valid_addr a m \<Longrightarrow> f_valid_addr a' m \<Longrightarrow> a\<noteq>a' \<Longrightarrow> 
    f_store a x (f_store a' x' m) = f_store a' x' (f_store a x m)"  
    apply transfer
    apply (clarsimp split: llvm_addr.split if_splits simp: nth_list_update)
    apply (metis eq_nat_nat_iff list_update_swap)
    by (metis list_update_swap)
    
  
  lemma f_load_store_indep[simp]: "f_valid_addr a m \<Longrightarrow> f_valid_addr a' m \<Longrightarrow> a\<noteq>a' \<Longrightarrow> f_load a (f_store a' x m) = f_load a m"  
    by (metis f_load_store f_store_indep f_store_load f_valid_store)
    
  lemma f_valid_addr_alloc: "f_alloc x n m = (b,m') \<Longrightarrow> f_valid_addr a m' \<longleftrightarrow> f_valid_addr a m \<or> (\<exists>i. 0\<le>i \<and> i<int n \<and> a=ADDR b i)"  
    apply transfer
    by (auto split: llvm_addr.split if_splits simp: nth_append)
    
  lemma f_load_alloc_indep: "f_valid_addr a m \<Longrightarrow> f_alloc x n m = (b,m') \<Longrightarrow> f_load a m' = f_load a m"  
    apply transfer
    by (auto split: llvm_addr.split if_splits simp: nth_append)

  lemma f_load_alloc: "f_alloc x n m = (b,m') \<Longrightarrow> 0\<le>i \<and> i<int n \<Longrightarrow> f_load (ADDR b i) m' = x"  
    apply transfer
    by (auto split: llvm_addr.split if_splits simp: nth_append)
      
  lemma f_store_valid_block[simp]: "f_valid_addr a m \<Longrightarrow> f_valid_block b (f_store a x m) = f_valid_block b m"
    apply transfer
    by (auto split: llvm_addr.split if_splits simp: nth_list_update)
    
  lemma f_store_block_size[simp]: "f_valid_addr a m \<Longrightarrow> f_block_size b (f_store a x m) = f_block_size b m"
    apply transfer
    by (auto split: llvm_addr.split if_splits simp: nth_list_update)
    
  lemma f_store_freed_block[simp]: "f_valid_addr a m \<Longrightarrow> f_freed_block b (f_store a x m) = f_freed_block b m"
    apply transfer
    by (auto split: llvm_addr.split if_splits simp: nth_list_update)
        
  lemma f_alloc_valid_block: "f_alloc n x m = (br,m') \<Longrightarrow> f_valid_block b m' \<longleftrightarrow> f_valid_block b m \<or> b=br"  
    apply transfer
    by (auto split: llvm_addr.split if_splits simp: )
    
  lemma f_alloc_block_size_other: "f_valid_block b m \<Longrightarrow> f_alloc n x m = (br,m') \<Longrightarrow> f_block_size b m' = f_block_size b m"  
    apply transfer
    apply (auto split: llvm_addr.split if_splits simp: nth_append)
    done

  lemma f_alloc_fresh_block: "f_valid_block b m \<Longrightarrow> f_alloc n x m = (br,m') \<Longrightarrow> b\<noteq>br"  
    apply transfer
    apply (auto split: llvm_addr.split if_splits simp: nth_append)
    done
        
  lemma f_alloc_block_size_this: "f_alloc x n m = (br,m') \<Longrightarrow> f_block_size br m' = n"  
    apply transfer
    apply (auto split: llvm_addr.split if_splits simp: nth_append)
    done
    
  lemma f_alloc_freed_block: "f_alloc n x m = (br,m') \<Longrightarrow> f_freed_block b m' = f_freed_block b m"  
    apply transfer
    by (auto split: llvm_addr.split if_splits simp: nth_append)
    

  lemma f_free_valid_block[simp]: "f_valid_block b (f_free b' m) \<longleftrightarrow> f_valid_block b m \<and> b'\<noteq>b"  
    apply transfer
    by (auto split: llvm_addr.split if_splits simp: nth_append nth_list_update')
    
  lemma f_free_block_size[simp]: "b\<noteq>b' \<Longrightarrow> f_block_size b (f_free b' m) = f_block_size b m"  
    apply transfer
    by (auto split: llvm_addr.split if_splits simp: nth_append nth_list_update')
    
  lemma f_free_freed_block[simp]: "f_valid_block b' m 
    \<Longrightarrow> f_freed_block b (f_free b' m) \<longleftrightarrow> f_freed_block b m \<or> b=b'"  
    apply transfer
    by (auto split: llvm_addr.split if_splits simp: nth_append nth_list_update')
        
  lemma valid_free_disj[simp]: "f_valid_block b m \<Longrightarrow> \<not>f_freed_block b m"
    apply transfer
    by (auto split: llvm_addr.split if_splits)
    
  lemma valid_addr_valid_block[simp]: "f_valid_addr (ADDR b i) m \<Longrightarrow> f_valid_block b m"  
    apply transfer
    by (auto split: llvm_addr.split if_splits)
        
  lemma f_load_free_valid[simp]: "f_valid_addr a (f_free b m) \<Longrightarrow> f_load a (f_free b m) = f_load a m"  
    apply transfer
    by (auto split: llvm_addr.split if_splits simp: nth_list_update')
    
  lemma f_valid_addr_free[simp]: "f_valid_addr a (f_free b m) \<longleftrightarrow> f_valid_addr a m \<and> llvm_addr.block a \<noteq> b"
    apply transfer
    by (auto split: llvm_addr.split if_splits simp: nth_list_update')
  
  lemma f_valid_addr_is_ptr_valid[intro]: "f_valid_addr a s \<Longrightarrow> f_valid_ptr_addr a s"  
    apply transfer
    by (auto split: llvm_addr.split)
    
    
  lifting_update memory.lifting
  lifting_forget memory.lifting
        
  subsection \<open>LLVM Values\<close>

  datatype llvm_val = 
    is_struct: LL_STRUCT (the_fields: "llvm_val list") 
  | is_int: LL_INT (the_int: lint) 
  | is_double: LL_DOUBLE (the_double: double) (* 
      TODO: Similar to lint, we could encode different floating-point layouts here, 
        and restrict the code-generator to only accept the ones supported by LLVM.
    *)
  | is_ptr: LL_PTR (the_ptr: llvm_ptr)
  hide_const (open) 
    llvm_val.is_struct llvm_val.the_fields
    llvm_val.is_int llvm_val.the_int
    llvm_val.is_double llvm_val.the_double
    llvm_val.is_ptr llvm_val.the_ptr
  
  
  datatype llvm_struct = 
    is_struct: VS_STRUCT (the_fields: "llvm_struct list") 
  | is_int: VS_INT (the_width: nat)
  | is_double: VS_DOUBLE
  | is_ptr: VS_PTR 
  hide_const (open) 
    llvm_struct.is_struct llvm_struct.the_fields
    llvm_struct.is_ptr
    llvm_struct.is_double
    llvm_struct.is_int llvm_struct.the_width
  
  
  
  fun llvm_struct_of_val where
    "llvm_struct_of_val (LL_STRUCT vs) = VS_STRUCT (map llvm_struct_of_val vs)"
  | "llvm_struct_of_val (LL_INT i) = VS_INT (width i)"
  | "llvm_struct_of_val (LL_DOUBLE _) = VS_DOUBLE"
  | "llvm_struct_of_val (LL_PTR _) = VS_PTR"

  fun llvm_zero_initializer where
    "llvm_zero_initializer (VS_STRUCT vss) = LL_STRUCT (map llvm_zero_initializer vss)"
  | "llvm_zero_initializer (VS_INT w) = LL_INT (lconst w 0)"
  | "llvm_zero_initializer (VS_DOUBLE) = LL_DOUBLE (double_of_word 0)"
  | "llvm_zero_initializer VS_PTR = LL_PTR PTR_NULL"
  
  lemma struct_of_llvm_zero_initializer[simp]: "llvm_struct_of_val (llvm_zero_initializer s) = s"
    apply (induction s) 
    apply (simp_all add: map_idI)
    done

  type_synonym llvm_memory = "llvm_val memory"
  translations (type) "llvm_memory" \<leftharpoondown> (type) "llvm_val memory"

  abbreviation (input) "TYPE_ERROR \<equiv> STATIC_ERROR ''type''"
  
  type_synonym 'a if_llM = "('a,llvm_memory,llvm_macc) M"

  abbreviation "mfail _ \<equiv> fail"

  definition llvm_extract_addr :: "llvm_val \<Rightarrow> llvm_addr if_llM" where
    "llvm_extract_addr v \<equiv> case v of LL_PTR (PTR_ADDR a) \<Rightarrow> return a | LL_PTR PTR_NULL \<Rightarrow> mfail MEM_ERROR | _ \<Rightarrow> mfail TYPE_ERROR"

  definition llvm_extract_ptr :: "llvm_val \<Rightarrow> llvm_ptr if_llM" where
    "llvm_extract_ptr v \<equiv> case v of LL_PTR p \<Rightarrow> return p | _ \<Rightarrow> mfail TYPE_ERROR"
    
  definition llvm_extract_sint :: "llvm_val \<Rightarrow> int if_llM" where
    "llvm_extract_sint v \<equiv> case v of LL_INT i \<Rightarrow> return (lint_to_sint i) | _ \<Rightarrow> mfail TYPE_ERROR" 
        
  definition llvm_extract_unat :: "llvm_val \<Rightarrow> nat if_llM" where
    "llvm_extract_unat v \<equiv> case v of LL_INT i \<Rightarrow> return (nat (lint_to_uint i)) | _ \<Rightarrow> mfail TYPE_ERROR" 
    
  definition llvm_extract_value :: "llvm_val \<Rightarrow> nat \<Rightarrow> llvm_val if_llM" where 
  "llvm_extract_value v i \<equiv> case v of 
    LL_STRUCT vs \<Rightarrow> doM {
      fcheck TYPE_ERROR (i<length vs);
      return (vs!i)
    }
  | _ \<Rightarrow> mfail TYPE_ERROR"
      
  definition llvm_insert_value :: "llvm_val \<Rightarrow> llvm_val \<Rightarrow> nat \<Rightarrow> llvm_val if_llM" where 
  "llvm_insert_value v x i \<equiv> case v of 
    LL_STRUCT vs \<Rightarrow> doM {
      fcheck TYPE_ERROR (i<length vs);
      fcheck TYPE_ERROR (llvm_struct_of_val (vs!i) = llvm_struct_of_val x);
      return (LL_STRUCT (vs[i:=x]))
    }
  | _ \<Rightarrow> mfail TYPE_ERROR"

    
  subsection \<open>Interface functions\<close>
  
  subsubsection \<open>Typed arguments\<close>
    
  definition llvmt_check_addr :: "llvm_addr \<Rightarrow> unit if_llM" where "llvmt_check_addr a \<equiv> 
    doM { m \<leftarrow> Monad.get; fcheck MEM_ERROR (f_valid_addr a m) }"
    
  definition "llvmt_load a \<equiv> doM { 
    llvmt_check_addr a; 
    m \<leftarrow> Monad.get; 
    interfer (macc_read {a});
    return (f_load a m) 
  }"
  
  definition "llvmt_store x a \<equiv> doM { 
    xorig \<leftarrow> llvmt_load a; 
    fcheck TYPE_ERROR (llvm_struct_of_val x = llvm_struct_of_val xorig);
    m \<leftarrow> Monad.get; 
    interfer (macc_write {a});
    let m = f_store a x m; 
    Monad.set m 
  }"
  
  definition "llvmt_alloc s n \<equiv> doM {
    m \<leftarrow> Monad.get; 
    let (b,m) = f_alloc (llvm_zero_initializer s) n m;
    Monad.set m;
    return b
  }"
  
  definition "llvmt_free b \<equiv> doM {
    m \<leftarrow> Monad.get; 
    fcheck MEM_ERROR (f_valid_block b m);
    let m = f_free b m;
    Monad.set m
  }"  

  definition "llvmt_freep p \<equiv> case p of PTR_ADDR (ADDR b i) \<Rightarrow> doM {
    fcheck MEM_ERROR (i=0);
    llvmt_free b;
    return ()
  }"  

  definition "llvmt_allocp s n \<equiv> doM {
    b \<leftarrow> llvmt_alloc s n;
    return (PTR_ADDR (ADDR b 0))
  }"
    
  
  definition "llvmt_check_ptr p \<equiv> doM {
    m \<leftarrow> Monad.get;
    fcheck MEM_ERROR (f_valid_ptr p m)
  }"
      
  definition "llvmt_ofs_ptr p ofs \<equiv> doM {
    fcheck MEM_ERROR (llvm_ptr.is_addr p);
    let a = llvm_ptr.the_addr p;
    let b = llvm_addr.block a;
    let i = llvm_addr.idx a;
    let i' = i + ofs;
    fcheck MEM_ERROR (i' \<ge> 0);
    let r = PTR_ADDR (ADDR b i');
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

  definition "llvm_extract_base_block a \<equiv> case a of ADDR b i \<Rightarrow> if i=0 then return b else mfail MEM_ERROR"
  
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
