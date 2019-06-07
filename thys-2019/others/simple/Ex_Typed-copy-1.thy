theory Ex_Typed
imports Monad2 LLVM_Integer
begin
  datatype err = is_static: STATIC_ERROR string | MEM_ERROR | UNINIT_ERROR
  hide_const (open) is_static

  abbreviation lift_lens_static ("'(_')\<^sub>S")
    where "lift_lens_static \<equiv> lift_lens (STATIC_ERROR ''lens'')"

  abbreviation lift_lens_mem ("'(_')\<^sub>M")
    where "lift_lens_mem \<equiv> lift_lens MEM_ERROR"

  abbreviation lift_lens_uninit ("'(_')\<^sub>U")
    where "lift_lens_uninit \<equiv> lift_lens UNINIT_ERROR"

  datatype 'v memory = MEM (mem: "'v option list")
  hide_const (open) mem
  define_lenses memory

  abbreviation "memL \<equiv> (mem\<^sub>L)\<^sub>S"
  abbreviation "idxL i \<equiv> (idx\<^sub>L i)\<^sub>M"

  datatype block_addr = BLOCK_ADDR (the_block: nat)

  definition "mem_empty \<equiv> MEM []"

  definition "block_allocate v \<equiv> (doM {
    \<mu>\<leftarrow>use memL;
    memL %= (\<lambda>\<mu>. \<mu>@[Some v]);
    return (BLOCK_ADDR (length \<mu>))
  })"

  definition "block_free b \<equiv> doM {
    let L = memL \<bullet> idxL (the_block b);
    b\<leftarrow>use L;
    fcheck MEM_ERROR (b\<noteq>None);
    L := None
  }"

  definition "blockL b \<equiv> memL \<bullet> (idx\<^sub>L (the_block b))\<^sub>S \<bullet> (the\<^sub>L)\<^sub>M"

  lemma [simp]: "elens (blockL b)"
    by (auto simp: blockL_def)

  datatype va_item = VA_ARRAY_IDX (aidx: nat) | VA_FIELD_IDX (fidx: nat)
  hide_const (open) aidx fidx
  define_lenses (open) va_item

  type_synonym vaddr = "va_item list"

  datatype addr = ADDR (block_addr: block_addr) (vaddr: vaddr)
  hide_const (open) block_addr vaddr
  define_lenses (open) addr

  datatype val =
    VBOOL (bool: "bool option")
  | VINT (int: "int option")
  | VPTR (addr: "addr option option")
  | VARRAY (items: "val list")
  | VSTRUCT (fields: "val list")

  hide_const (open) bool int addr items fields
  define_lenses (open) val


  fun same_struct :: "val \<Rightarrow> val \<Rightarrow> bool" where
    "same_struct (VBOOL _) (VBOOL _) \<longleftrightarrow> True"
  | "same_struct (VINT _) (VINT _) \<longleftrightarrow> True"
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


  datatype (discs_sels) type =
    TBOOL | TINT | TPTR type | TARRAY nat type | TSTRUCT "type list"


  datatype memT = MEM_TYPE (memT: "type option list")
  hide_const (open) memT

  fun vaddr_of_type :: "type \<Rightarrow> vaddr \<Rightarrow> type \<Rightarrow> bool" where
    "vaddr_of_type bT [] T \<longleftrightarrow> T=bT"
  | "vaddr_of_type (TARRAY n bT) (VA_ARRAY_IDX i#as) T \<longleftrightarrow> (*i<n \<and>*) vaddr_of_type bT as T"
  | "vaddr_of_type (TSTRUCT bTs) (VA_FIELD_IDX i#as) T \<longleftrightarrow> i<length bTs \<and> vaddr_of_type (bTs!i) as T"
  | "vaddr_of_type _ _ _ \<longleftrightarrow> False"

  context fixes \<mu>T :: memT begin

    definition addr_of_type where
      "addr_of_type a T \<equiv>
        let
          b = the_block (addr.block_addr a);
          \<mu>T = memT.memT \<mu>T
        in
          if b < length \<mu>T then
            case \<mu>T!b of
              None \<Rightarrow> True
            | Some bT \<Rightarrow> vaddr_of_type bT (addr.vaddr a) T
          else False"

    fun of_type :: "type \<Rightarrow> val \<Rightarrow> bool"
    where
      "of_type TBOOL (VBOOL _) \<longleftrightarrow> True"
    | "of_type TINT (VINT _) \<longleftrightarrow> True"
    | "of_type (TPTR T) (VPTR (Some (Some a))) \<longleftrightarrow> addr_of_type a T"
    | "of_type (TPTR T) (VPTR _) \<longleftrightarrow> True"
    | "of_type (TARRAY n T) (VARRAY vs) \<longleftrightarrow> n=length vs \<and> (\<forall>v\<in>List.set vs. of_type T v)"
    | "of_type (TSTRUCT Ts) (VSTRUCT vs) \<longleftrightarrow> list_all2 of_type Ts vs"
    | "of_type _ _ \<longleftrightarrow> False"

  end

  definition mem_of_type :: "memT \<Rightarrow> val memory \<Rightarrow> bool"
    where "mem_of_type \<mu>T \<mu> \<equiv> list_all2 (rel_option (of_type \<mu>T)) (memT.memT \<mu>T) (memory.mem \<mu>)"

  lemma mem_of_type_lengthD:
    "mem_of_type \<mu>T \<mu> \<Longrightarrow> length (memT.memT \<mu>T) = length (memory.mem \<mu>)"
    "mem_of_type (MEM_TYPE Ts) \<mu> \<Longrightarrow> length (Ts) = length (memory.mem \<mu>)"
    by (auto simp: mem_of_type_def list_all2_lengthD)



  definition "struct_field\<^sub>L i \<equiv> (val.fields\<^sub>L \<bullet>\<^sub>L idx\<^sub>L i)\<^sub>S"
  (*definition "static_array_item\<^sub>L i \<equiv> (val.items\<^sub>L \<bullet>\<^sub>L idx\<^sub>L i)\<^sub>S"*)
  definition "array_item\<^sub>L i \<equiv> (val.items\<^sub>L)\<^sub>S \<bullet> idxL i"

  fun lens_of_vai where
    "lens_of_vai (VA_ARRAY_IDX i) = array_item\<^sub>L i"
  | "lens_of_vai (VA_FIELD_IDX i) = struct_field\<^sub>L i"

  definition "lens_of_vaddr va \<equiv> foldr (\<lambda>vai p. lens_of_vai vai \<bullet> p) va (id\<^sub>L)\<^sub>S"

  fun lens_of_addr where
    "lens_of_addr (ADDR b va) = blockL b \<bullet> lens_of_vaddr va"


(*
  definition op_get_field where
    "op_get_field v i \<equiv> mget (struct_field\<^sub>L i) v"
  definition op_put_field where
    "op_put_field v i v' \<equiv> mput (struct_field\<^sub>L i) v' v"

  definition op_get_array_item where
    "op_get_array_item v i \<equiv> mget (array_item\<^sub>L i) v"
  definition op_put_array_item where
    "op_put_array_item v i v' \<equiv> mput (array_item\<^sub>L i) v' v"
*)
  (*
  definition op_ptr_field where
    "op_ptr_field p i \<equiv> p \<bullet> (struct_field\<^sub>L i)"
  definition op_ptr_array_item where
    "op_ptr_array_item p i \<equiv> p \<bullet> array_item\<^sub>L i"
  *)


  datatype label_name = LABEL_NAME (the_name: string)
  hide_const (open) the_name
  datatype proc_name = PROC_NAME (the_name: string)
  hide_const (open) the_name
  datatype lvar_name = LVAR_NAME (the_name: string)
  hide_const (open) the_name

  datatype operand = OP_BCONST bool | OP_ICONST int | OP_LVAR lvar_name

  datatype icmp_code = EQ | NE | SLE | SLT
  hide_const (open) EQ NE SLE SLT


  datatype basic_instr_aux =
    ADD type operand operand
  | SUB type operand operand
  | ICMP icmp_code type operand operand
  | NOT type operand
  | AND type operand operand
  | OR type operand operand
  | ALLOCA type type operand
  | MALLOC type type operand
  | LOAD type operand
  | STORE type operand operand
  | FREE type operand
  | INSERT_A_VALUE type operand type operand nat
  | INSERT_S_VALUE type operand type operand nat
  | EXTRACT_A_VALUE type operand nat
  | EXTRACT_S_VALUE type operand nat
  | OFS_PTR type operand type operand  \<comment> \<open>\<open>getelementptr ty, ty* ptr, ty i \<close>\<close>
  | INDEX_A_PTR type operand type operand \<comment> \<open>\<open>getelementptr ty, ty* ptr, i32 0, ty i \<close>\<close>
  | INDEX_S_PTR type operand nat \<comment> \<open>\<open>getelementptr ty, ty* ptr, i32 0, ty i \<close>\<close>

  datatype nt_instr_aux =
    BASIC basic_instr_aux
  | CALL type proc_name "(type \<times> operand) list"

  datatype nt_instr = NT_INSTR "lvar_name option" nt_instr_aux


  datatype t_instr =
    RETURN type operand
  | RETURN_VOID
  | BR label_name
  | CBR operand label_name label_name

  datatype basic_block = BBLOCK "nt_instr list" t_instr

  datatype procedure = PROC
    (params: "(type \<times> lvar_name) list")
    (prologue: basic_block)
    (blocks: "(label_name\<times>basic_block) list")
    (rtype: "type option")
  hide_const (open) params prologue blocks rtype

  datatype program = PROG (procedures: "(proc_name \<times> procedure) list")
  hide_const (open) procedures


  datatype exec_state = EXEC_STATE
    (lvars: "lvar_name \<rightharpoonup> val")
    (local_blocks: "block_addr list")
    (memory: "val memory")
  hide_const (open) lvars local_blocks memory
  define_lenses (open) exec_state

  definition "lvar\<^sub>L x \<equiv> (exec_state.lvars\<^sub>L \<bullet>\<^sub>L fun\<^sub>L x \<bullet>\<^sub>L the\<^sub>L)\<^sub>S"

  fun load_opr where
    "load_opr (OP_BCONST b) = return (VBOOL (Some b))"
  | "load_opr (OP_ICONST i) = return (VINT (Some i))"
  | "load_opr (OP_LVAR x) = use (lvar\<^sub>L x)"


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

  definition to_int where
    "to_int v \<equiv> case (v) of
        (VINT (Some i)) \<Rightarrow> return i
      | (VINT None) \<Rightarrow> fail UNINIT_ERROR
      | _ \<Rightarrow> fail (STATIC_ERROR ''to_int'')"

  definition to_bool where
    "to_bool v \<equiv> case (v) of
        (VBOOL (Some i)) \<Rightarrow> return i
      | (VBOOL None) \<Rightarrow> fail UNINIT_ERROR
      | _ \<Rightarrow> fail (STATIC_ERROR ''to_bool'')"

  definition "to_idx i \<equiv> doM {fcheck MEM_ERROR (i\<ge>0); return (nat i)}"

  definition load_int where
    "load_int opr \<equiv> doM {
      v \<leftarrow> load_opr opr;
      to_int v
    }"

  definition load_ptr where
    "load_ptr opr \<equiv> doM {
      v \<leftarrow> load_opr opr;
      to_ptr v
    }"

  definition load_addr where
    "load_addr opr \<equiv> doM {
      v \<leftarrow> load_opr opr;
      to_addr v
    }"

  definition load_bool where
    "load_bool opr \<equiv> doM {
      v \<leftarrow> load_opr opr;
      to_bool v
    }"


  definition define_lvar where
    "define_lvar name val \<equiv> zoom (exec_state.lvars\<^sub>L)\<^sub>S (doM {
      l\<leftarrow>get;
      fcheck (STATIC_ERROR ''lvar redefined'') (name \<notin> dom l);
      let l = l(name\<mapsto>val);
      set l
    })"


  fun uninit where
    "uninit TBOOL = VBOOL None"
  | "uninit TINT = VINT None"
  | "uninit (TPTR _) = VPTR None"
  | "uninit (TARRAY n ty) = VARRAY (replicate n (uninit ty))"
  | "uninit (TSTRUCT tys) = VSTRUCT (map uninit tys)"

typ "(_,_,_,_) M"

definition "noexcept m \<equiv> handle m (\<lambda>_. fail (STATIC_ERROR ''noexcept''))"
lemma noexcept_mono[partial_function_mono]:
  "monotone M.le_fun M_ord m \<Longrightarrow> monotone M.le_fun M_ord (\<lambda>f. noexcept (m f))"
  unfolding noexcept_def
  by pf_mono_prover

definition "instr_add a b \<equiv> return (a+b::int)"
definition "instr_sub a b \<equiv> return (a-b::int)"

fun instr_icmp where
  "instr_icmp icmp_code.EQ a b = return (a = b)"
| "instr_icmp icmp_code.NE a b = return (a \<noteq> b)"
| "instr_icmp icmp_code.SLE a b = return (a \<le> b)"
| "instr_icmp icmp_code.SLT a b = return (a < b)"

definition "instr_not a \<equiv> return (\<not>a)"
definition "instr_and a b \<equiv> return (a\<and>b)"
definition "instr_or a b \<equiv> return (a\<or>b)"


definition "instr_alloca ty n = doM {
  fcheck MEM_ERROR (n>0);
  let n = nat n;
  let v = uninit (TARRAY n ty);
  r \<leftarrow> zoom (exec_state.memory\<^sub>L)\<^sub>S (block_allocate v);
  (exec_state.local_blocks\<^sub>L)\<^sub>S %= (#) r;
  return (ADDR r [VA_ARRAY_IDX 0])
}"

definition "instr_malloc ty n = doM {
  fcheck MEM_ERROR (n>0);
  let n = nat n;
  let v = uninit (TARRAY n ty);
  r \<leftarrow> zoom (exec_state.memory\<^sub>L)\<^sub>S (block_allocate v);
  return (ADDR r [VA_ARRAY_IDX 0])
}"

definition "instr_free addr = doM {
  case addr of
      ADDR b [VA_ARRAY_IDX 0] \<Rightarrow> zoom (exec_state.memory\<^sub>L)\<^sub>S (block_free b)
    | _ \<Rightarrow> fail MEM_ERROR
}"

definition instr_load where
  "instr_load addr \<equiv> doM {
    zoom (exec_state.memory\<^sub>L)\<^sub>S (use (lens_of_addr addr))
  }"

definition instr_store where
  "instr_store v addr \<equiv> doM {
    zoom (exec_state.memory\<^sub>L)\<^sub>S (doM {
      ov \<leftarrow> use (lens_of_addr addr);
      fcheck (STATIC_ERROR ''mem-struct change'') (same_struct v ov);
      lens_of_addr addr := v
    })
  }"

definition "put_same_struct L a b \<equiv> doM {
  v \<leftarrow> mget L b;
  fcheck (STATIC_ERROR ''val-struct change'') (same_struct a v);
  mput L a b
}"


definition "instr_insert_a_value bv ev idx \<equiv> put_same_struct (array_item\<^sub>L idx) ev bv"
definition "instr_insert_s_value bv ev idx \<equiv> put_same_struct (struct_field\<^sub>L idx) ev bv"
definition "instr_extract_a_value bv idx \<equiv> mget (array_item\<^sub>L idx) bv"
definition "instr_extract_s_value bv idx \<equiv> mget (struct_field\<^sub>L idx) bv"

definition instr_ofs_addr :: "addr \<Rightarrow> int \<Rightarrow> _" where
  "instr_ofs_addr a i \<equiv> map_lens (addr.vaddr\<^sub>L\<bullet>\<^sub>Llast\<^sub>L\<bullet>\<^sub>Lva_item.aidx\<^sub>L)\<^sub>M (\<lambda>idx. doM {
    let idx = int idx + i;
    fcheck MEM_ERROR (idx\<ge>0);
    return (nat idx)
  }) a"

definition instr_idx_array :: "addr \<Rightarrow> int \<Rightarrow> _" where
  "instr_idx_array a i \<equiv> map_lens (addr.vaddr\<^sub>L)\<^sub>S (\<lambda>x. doM {
    i \<leftarrow> to_idx i;
    return (x@[VA_ARRAY_IDX i])
  } ) a"

definition instr_idx_field :: "addr \<Rightarrow> nat \<Rightarrow> _" where
  "instr_idx_field a i \<equiv> map_lens (addr.vaddr\<^sub>L)\<^sub>S (\<lambda>x. doM {
    return (x@[VA_FIELD_IDX i])
  } ) a"

context
  fixes exec_proc_name :: "proc_name \<times> val list \<Rightarrow> (val option,unit,val memory,err) M"
begin

  primrec exec_basic_instr_aux where
    "exec_basic_instr_aux (ADD ty op1 op2) = doM {
      x1 \<leftarrow> load_int op1;
      x2 \<leftarrow> load_int op2;
      r \<leftarrow> instr_add x1 x2;
      return (Some (VINT (Some r)))
    }"
  | "exec_basic_instr_aux (SUB ty op1 op2) = doM {
      x1 \<leftarrow> load_int op1;
      x2 \<leftarrow> load_int op2;
      r \<leftarrow> instr_sub x1 x2;
      return (Some ( VINT (Some r)))
    }"
  | "exec_basic_instr_aux (ICMP code ty op1 op2) = doM {
      x1 \<leftarrow> load_int op1;
      x2 \<leftarrow> load_int op2;
      r \<leftarrow> instr_icmp code x1 x2;
      return (Some (VBOOL (Some r)))
    }"
  | "exec_basic_instr_aux (AND ty op1 op2) = doM {
      x1 \<leftarrow> load_bool op1;
      x2 \<leftarrow> load_bool op2;
      r \<leftarrow> instr_and x1 x2;
      return (Some (VBOOL (Some r)))
    }"
  | "exec_basic_instr_aux (OR ty op1 op2) = doM {
      x1 \<leftarrow> load_bool op1;
      x2 \<leftarrow> load_bool op2;
      r \<leftarrow> instr_or x1 x2;
      return (Some (VBOOL (Some r)))
    }"
  | "exec_basic_instr_aux (NOT ty op1) = doM {
      x1 \<leftarrow> load_bool op1;
      r \<leftarrow> instr_not x1;
      return (Some (VBOOL (Some r)))
    }"
  | "exec_basic_instr_aux (ALLOCA ty tyi opr) = doM {
      n \<leftarrow> load_int opr;
      addr \<leftarrow> instr_alloca ty n;
      return (Some (VPTR (Some (Some addr))))
    }"
  | "exec_basic_instr_aux (MALLOC ty tyi opr) = doM {
      n \<leftarrow> load_int opr;
      addr \<leftarrow> instr_malloc ty n;
      return (Some (VPTR (Some (Some addr))))
    }"
  | "exec_basic_instr_aux (FREE ty opr) = doM {
      addr \<leftarrow> load_addr opr;
      instr_free addr;
      return None
    }"
  | "exec_basic_instr_aux (LOAD ty opr) = doM {
      addr \<leftarrow> load_addr opr;
      r \<leftarrow> instr_load addr;
      return (Some r)
    }"
  | "exec_basic_instr_aux (STORE ty oprv oprp) = doM {
      v \<leftarrow> load_opr oprv;
      addr \<leftarrow> load_addr oprp;
      instr_store v addr;
      return None
    }"
  | "exec_basic_instr_aux (INSERT_A_VALUE bty bopr ety eopr idx) = doM {
      bv \<leftarrow> load_opr bopr;
      ev \<leftarrow> load_opr eopr;
      r \<leftarrow> instr_insert_a_value bv ev idx;
      return (Some r)
    }"
  | "exec_basic_instr_aux (INSERT_S_VALUE bty bopr ety eopr idx) = doM {
      bv \<leftarrow> load_opr bopr;
      ev \<leftarrow> load_opr eopr;
      r \<leftarrow> instr_insert_s_value bv ev idx;
      return (Some r)
    }"
  | "exec_basic_instr_aux (EXTRACT_A_VALUE bty bopr idx) = doM {
      bv \<leftarrow> load_opr bopr;
      r \<leftarrow> instr_extract_a_value bv idx;
      return (Some r)
    }"
  | "exec_basic_instr_aux (EXTRACT_S_VALUE bty bopr idx) = doM {
      bv \<leftarrow> load_opr bopr;
      r \<leftarrow> instr_extract_s_value bv idx;
      return (Some r)
    }"
  | "exec_basic_instr_aux (OFS_PTR bty bopr ity iopr) = doM {
      addr \<leftarrow> load_addr bopr;
      idx \<leftarrow> load_int iopr;
      r \<leftarrow> instr_ofs_addr addr idx;
      return (Some ((VPTR (Some (Some r)))))
    }"
  | "exec_basic_instr_aux (INDEX_A_PTR bty bopr ity iopr) = doM {
      addr \<leftarrow> load_addr bopr;
      idx \<leftarrow> load_int iopr;
      r \<leftarrow> instr_idx_array addr idx;
      return (Some ((VPTR (Some (Some r)))))
    }"
  | "exec_basic_instr_aux (INDEX_S_PTR bty bopr idx) = doM {
      addr \<leftarrow> load_addr bopr;
      r \<leftarrow> instr_idx_field addr idx;
      return (Some ((VPTR (Some (Some r)))))
    }"

  primrec exec_nt_instr_aux where
    "exec_nt_instr_aux (BASIC i) = exec_basic_instr_aux i"
  | "exec_nt_instr_aux (CALL ty name args) = doM {
      argvs \<leftarrow> mmap (load_opr o snd) args;
      r \<leftarrow> zoom (exec_state.memory\<^sub>L)\<^sub>S (noexcept (exec_proc_name (name, argvs)));
      return r
    }"

  primrec exec_nt_instr where
    "exec_nt_instr (NT_INSTR resname i) = doM {
      r \<leftarrow> exec_nt_instr_aux i;
      case resname of
        None \<Rightarrow> return ()
      | Some resvar \<Rightarrow> doM {
        r \<leftarrow> mget (the\<^sub>L)\<^sub>S r;
        define_lvar resvar r
      }
    }"

  primrec exec_t_instr where
    "exec_t_instr (RETURN_VOID) = raise None"
  | "exec_t_instr (RETURN ty opr) = doM { v \<leftarrow> load_opr opr; raise (Some v) }"
  | "exec_t_instr (BR label) = return label"
  | "exec_t_instr (CBR opr ltrue lfalse) = doM {
      v \<leftarrow> load_bool opr;
      if v then return ltrue else return lfalse
  }"

  definition "exec_block \<equiv> \<lambda>BBLOCK ntis ti\<Rightarrow> doM {
    (* Execute nonterminal instructions *)
    mfold' exec_nt_instr ntis;
    (* Execute terminal instruction *)
    exec_t_instr ti
  }"

  term mmblock

  definition "exec_block_reset block \<equiv> doM {
    (* Save local definitions *)
    saved_lvars \<leftarrow> use (exec_state.lvars\<^sub>L)\<^sub>S;

    mmblock (get) (\<lambda>s'. doM {set s'; (exec_state.lvars\<^sub>L)\<^sub>S := saved_lvars}) (exec_block block)
  }"

  definition "mk_fresh_exec_state mem \<equiv> EXEC_STATE Map.empty [] mem"

  definition "exec_proc \<equiv> \<lambda>PROC params prologue blocks rtype \<Rightarrow> \<lambda>args. doM {
    fcheck (STATIC_ERROR ''|arg| != |param|'') (length params = length args);
    mblock (mk_fresh_exec_state) (exec_state.memory) (doM {
      (* Define Parameters*)
      mfold' (uncurry define_lvar) (zip (map snd params) args);

      handle (doM {
        (* Execute Prologue *)
        label \<leftarrow> exec_block prologue;

        (* Execute Blocks *)
        let block_map = map_of blocks;
        mwhile (\<lambda>_. return True) (\<lambda>label. doM {
          (* Lookup label *)
          block \<leftarrow> lookup (STATIC_ERROR ''undef label'') block_map label;
          exec_block_reset block
        }) label;

        fail (STATIC_ERROR ''unreachable'') (* Unreachable *)
      }) (\<lambda>r. doM {
        (* Free alloca-blocks *)
        lbs \<leftarrow> use (exec_state.local_blocks\<^sub>L)\<^sub>S;
        mfold' (\<lambda>b. zoom (exec_state.memory\<^sub>L)\<^sub>S (block_free b)) lbs;
        (* Return result *)
        return r})
    })
  }"


end (* Context fixing \<open>exec_proc_name\<close> *)

term exec_proc

context fixes \<pi> :: program begin
  definition "proc_map \<equiv> map_of (program.procedures \<pi>)"

  definition "exec_proc_name \<equiv>
    REC (\<lambda>exec_proc_name (name,args). doM {
      proc \<leftarrow> lookup (STATIC_ERROR ''undef proc'') proc_map name;
      exec_proc exec_proc_name proc args
    }) "

end

term exec_proc

lemma rec_cases_instr_eq:
  "rec_nt_instr = case_nt_instr"
  "rec_nt_instr_aux = case_nt_instr_aux"
  by (intro ext; auto split: nt_instr.split nt_instr_aux.split; fail)+


thm partial_function_mono(10)

lemma execute_proc_body_mono[partial_function_mono]:
  "M.mono_body (\<lambda>fa. exec_proc fa proc args)"
  unfolding exec_proc_def exec_block_def exec_nt_instr_def exec_nt_instr_aux_def
    exec_block_reset_def
  unfolding rec_cases_instr_eq
  by pf_mono_prover


(*lemmas exec_proc_name_unfold[code] = REC_unfold[OF exec_proc_name_def, discharge_monos]*)

lemmas exec_proc_name_unfold[code] = REC_unfold[OF exec_proc_name_def, discharge_monos]
   and exec_proc_name_partial = lrmwpe_REC_partial[OF exec_proc_name_def, discharge_monos, consumes 1, case_names nterm step]
   and exec_proc_name_total = lrmwpe_REC_total[OF exec_proc_name_def, discharge_monos, consumes 1, case_names wf step]


term mwhile
term exec_proc_name

definition "test \<equiv> PROG [(PROC_NAME ''main'',PROC [] (
  BBLOCK [
    NT_INSTR (Some (LVAR_NAME ''p'')) (BASIC (MALLOC TINT TINT (OP_ICONST 5)))
    ,
    NT_INSTR (Some (LVAR_NAME ''p2'')) (BASIC (OFS_PTR (TPTR TINT) (OP_LVAR (LVAR_NAME ''p'')) TINT (OP_ICONST 2)))
    ,
    NT_INSTR None (BASIC (STORE TINT (OP_ICONST 42) (OP_LVAR (LVAR_NAME ''p2''))))

  ] (RETURN (TPTR TINT) (OP_LVAR (LVAR_NAME ''p'')))
) [] (Some (TPTR TINT)))]"


value "run (exec_proc_name test (PROC_NAME ''main'',[])) (MEM [])"


term instr_load


abbreviation "no_static_err e \<equiv> \<not>err.is_static e"

thm exec_state.memory\<^sub>L_def

lemma [simp]:
  "pre_get exec_state.memory\<^sub>L s" "pre_put exec_state.memory\<^sub>L s"
  "get' exec_state.memory\<^sub>L s = exec_state.memory s"
  by (auto simp: exec_state.memory\<^sub>L_def split: exec_state.split)

find_theorems "use"

lemma fold_elens[simp]:
  "\<lbrakk>elens L; \<And>x. x\<in>list.set xs \<Longrightarrow> elens (f x)\<rbrakk> \<Longrightarrow> elens (fold (\<lambda>x p. p \<bullet> f x) xs L)"
  by (induction xs arbitrary: L) auto

lemma foldr_elens[simp]:
  "\<lbrakk>elens L; \<And>x. x\<in>list.set xs \<Longrightarrow> elens (f x)\<rbrakk> \<Longrightarrow> elens (foldr (\<lambda>x p. f x \<bullet> p) xs L)"
  by (induction xs arbitrary: L) auto


lemma [simp]: "elens (array_item\<^sub>L idx)" by (auto simp: array_item\<^sub>L_def)
lemma [simp]: "elens (struct_field\<^sub>L idx)" by (auto simp: struct_field\<^sub>L_def)

lemma [simp]: "elens (lens_of_vai vai)" by (cases vai) auto

lemma [simp]: "elens (lens_of_vaddr va)" unfolding lens_of_vaddr_def by auto



lemma [simp]: "pre_get mem\<^sub>L s" "pre_put mem\<^sub>L s" "get' mem\<^sub>L s = memory.mem s" "put' mem\<^sub>L x s = MEM x"
  by (auto simp: mem\<^sub>L_def split: memory.split)

find_theorems "eget" "(\<bullet>)"

lemma blockL_pre_simp[simp]: "epre_get (blockL b) \<mu> = (
  if \<not> the_block b < length (memory.mem \<mu>) then
    Some (STATIC_ERROR ''lens'')
  else if (memory.mem \<mu>)!the_block b = None then
    Some MEM_ERROR
  else
    None
)"
  unfolding blockL_def
  by (auto split: option.split)

lemma blockL_get_simp[simp]:
  "\<lbrakk>the_block b < length (memory.mem \<mu>); (memory.mem \<mu>)!the_block b = Some v\<rbrakk>
    \<Longrightarrow> eget' (blockL b) \<mu> = v"
  unfolding blockL_def
  by (auto split: option.split)

lemma blockL_put_simp[simp]:
  "\<lbrakk>the_block b < length (memory.mem \<mu>); (memory.mem \<mu>)!the_block b \<noteq> None  \<rbrakk>
    \<Longrightarrow> eput' (blockL b) v \<mu> = MEM (memory.mem \<mu> [the_block b := Some v])"
  unfolding blockL_def
  by (auto split: option.split)


lemma lens_of_vaddr_Nil[simp]:
  "lens_of_vaddr [] = (id\<^sub>L)\<^sub>S"
  by (auto simp: lens_of_vaddr_def)

lemma lens_of_vaddr_Cons[simp]:
  "lens_of_vaddr (va#vas) = lens_of_vai va \<bullet> lens_of_vaddr vas"
  by (auto simp: lens_of_vaddr_def)


lemma of_type_inv2[simp]:
  "of_type \<mu>T (TARRAY n bT) bv \<longleftrightarrow> (\<exists>vs. bv = VARRAY vs \<and> n = length vs \<and> (\<forall>v\<in>list.set vs. of_type \<mu>T bT v))"
  by (cases bv) auto


lemma [simp]:
  "pre_get (val.items\<^sub>L) s \<longleftrightarrow> (\<exists>xs. s=VARRAY xs)"
  "get' val.items\<^sub>L (VARRAY vs) = vs"
  "put' val.items\<^sub>L vs' (VARRAY vs) = VARRAY vs'"
  by (auto simp: val.items\<^sub>L_def split: val.splits)

lemma [simp]:
  "pre_get (val.fields\<^sub>L) s \<longleftrightarrow> (\<exists>xs. s=VSTRUCT xs)"
  "get' val.fields\<^sub>L (VSTRUCT vs) = vs"
  "put' val.fields\<^sub>L vs' (VSTRUCT vs) = VSTRUCT vs'"
  by (auto simp: val.fields\<^sub>L_def split: val.splits)


lemma [simp]:
  "epre_get (array_item\<^sub>L i) x = (case x of VARRAY vs \<Rightarrow> if i<length vs then None else Some MEM_ERROR | _ \<Rightarrow> Some (STATIC_ERROR ''lens''))"
  "epre_put (array_item\<^sub>L i) v x = epre_get (array_item\<^sub>L i) x"
  "i<length vs \<Longrightarrow> eget' (array_item\<^sub>L i) (VARRAY vs) = vs!i"
  "i<length vs \<Longrightarrow> eput' (array_item\<^sub>L i) v (VARRAY vs) = VARRAY (vs[i:=v])"
  by (auto simp: array_item\<^sub>L_def split: option.split val.splits)

lemma [simp]:
  "epre_get (struct_field\<^sub>L i) x = (case x of VSTRUCT vs \<Rightarrow> if i<length vs then None else Some (STATIC_ERROR ''lens'') | _ \<Rightarrow> Some (STATIC_ERROR ''lens''))"
  "epre_put (struct_field\<^sub>L i) v x = epre_get (struct_field\<^sub>L i) x"
  "i<length vs \<Longrightarrow> eget' (struct_field\<^sub>L i) (VSTRUCT vs) = vs!i"
  "i<length vs \<Longrightarrow> eput' (struct_field\<^sub>L i) v (VSTRUCT vs) = VSTRUCT (vs[i:=v])"
  by (auto simp: struct_field\<^sub>L_def split: option.split val.splits)

lemma tyco_get_lens_of_vaddr_aux:
  assumes "of_type \<mu>T bT bv" "vaddr_of_type bT p T"
  shows "case epre_get (lens_of_vaddr p) bv of
    None \<Rightarrow> of_type \<mu>T T (eget' (lens_of_vaddr p) bv)
  | Some e \<Rightarrow> \<not>err.is_static e
  "
  using assms
  apply (induction bT p T arbitrary: bv rule: vaddr_of_type.induct)
  apply (auto split: option.splits val.splits simp: Ball_def in_set_conv_nth list_all2_conv_all_nth)
  apply force+
  done

lemma tyco_get_lens_of_vaddr:
  assumes "of_type \<mu>T bT bv" "vaddr_of_type bT p T"
  shows "epre_get (lens_of_vaddr p) bv = None \<Longrightarrow> of_type \<mu>T T (eget' (lens_of_vaddr p) bv)"
    and "epre_get (lens_of_vaddr p) bv = Some e \<Longrightarrow> \<not>err.is_static e"
  using tyco_get_lens_of_vaddr_aux[OF assms] by (auto)

lemma tyco_put_lens_of_vaddr_aux:
  assumes "of_type \<mu>T bT bv" "vaddr_of_type bT p T" "of_type \<mu>T T v"
  shows "case epre_put (lens_of_vaddr p) v bv of
      None \<Rightarrow> of_type \<mu>T bT (eput' (lens_of_vaddr p) v bv)
    | Some e \<Rightarrow> \<not>err.is_static e"
  using assms
  apply (induction bT p T arbitrary: bv rule: vaddr_of_type.induct)
  apply (auto split: option.splits val.splits simp: Ball_def in_set_conv_nth list_all2_conv_all_nth nth_list_update)
  apply force+
  done

lemma tyco_put_lens_of_vaddr:
  assumes "of_type \<mu>T bT bv" "vaddr_of_type bT p T" "of_type \<mu>T T v"
  shows "epre_put (lens_of_vaddr p) v bv = None \<Longrightarrow> of_type \<mu>T bT (eput' (lens_of_vaddr p) v bv)"
    and "epre_put (lens_of_vaddr p) v bv = Some e \<Longrightarrow> \<not>err.is_static e"
  using tyco_put_lens_of_vaddr_aux[OF assms] by (auto)


lemma tyco_use_lens_of_addr:
  assumes "mem_of_type \<mu>T \<mu>"
  assumes "addr_of_type \<mu>T a T"
  shows "mwp (run (use (lens_of_addr a)) \<mu>) bot no_static_err bot (\<lambda>v \<mu>'. \<mu>'=\<mu> \<and> of_type \<mu>T T v)"
  using assms
  apply (cases a)
  apply (auto
    simp: run_simps addr_of_type_def Let_def mem_of_type_def list_all2_conv_all_nth
    simp: tyco_get_lens_of_vaddr
    split: if_splits option.splits)
  done

lemma tyco_put_lens_of_addr:
  assumes "mem_of_type \<mu>T \<mu>"
  assumes "addr_of_type \<mu>T a T"
  assumes "of_type \<mu>T T v"
  shows "mwp (run ((lens_of_addr a := v)) \<mu>) bot no_static_err bot (\<lambda>_ \<mu>'. mem_of_type \<mu>T \<mu>')"
  using assms
  apply (cases a)
  apply (auto
    simp: run_simps addr_of_type_def Let_def mem_of_type_def list_all2_conv_all_nth
    simp: tyco_put_lens_of_vaddr nth_list_update
    split: if_splits option.splits)
  done


term "allocate"

fun memT_le where "memT_le (MEM_TYPE \<mu>T) (MEM_TYPE \<mu>T') \<longleftrightarrow>
  length \<mu>T \<le> length \<mu>T' \<and> (\<forall>i<length \<mu>T. \<mu>T'!i = None \<or> \<mu>T'!i=\<mu>T!i)"

lemma memT_le_refl[intro!,simp]: "memT_le \<mu>T \<mu>T"
  by (cases \<mu>T) auto

lemma memT_le_trans[trans]: "memT_le \<mu>T\<^sub>1 \<mu>T\<^sub>2 \<Longrightarrow> memT_le \<mu>T\<^sub>2 \<mu>T\<^sub>3 \<Longrightarrow> memT_le \<mu>T\<^sub>1 \<mu>T\<^sub>3"
  apply (cases \<mu>T\<^sub>1;cases \<mu>T\<^sub>2;cases \<mu>T\<^sub>3)
  apply auto
  by (metis less_le_trans)

lemma memT_le_idx_conv:
  "\<lbrakk>memT_le \<mu>T \<mu>T'; i<length (memT.memT \<mu>T); memT.memT \<mu>T' ! i \<noteq> None \<rbrakk> \<Longrightarrow> memT.memT \<mu>T' ! i = memT.memT \<mu>T ! i"
  by (cases \<mu>T; cases \<mu>T'; auto)

lemma memT_le_idx_conv1:
  "\<lbrakk> memT_le \<mu>T \<mu>T'; i<length (memT.memT \<mu>T); memT.memT \<mu>T' ! i = Some T \<rbrakk> \<Longrightarrow> memT.memT \<mu>T ! i = Some T  "
  using memT_le_idx_conv by auto

lemma addr_of_type_memT_le: "\<lbrakk>memT_le \<mu>T \<mu>T'; addr_of_type \<mu>T a T\<rbrakk> \<Longrightarrow> addr_of_type \<mu>T' a T"
  apply (cases \<mu>T; cases \<mu>T'; simp)
  apply (auto simp: addr_of_type_def Let_def split: if_splits option.splits)
  done

lemma of_type_memT_le:
  assumes "memT_le \<mu>T \<mu>T'"
  assumes "of_type \<mu>T T v"
  shows "of_type \<mu>T' T v"
  using assms
  apply (induction T v rule: of_type.induct)
  apply (auto simp: addr_of_type_memT_le list_all2_conv_all_nth)
  done


lemma tyco_block_allocate_aux:
  fixes \<mu>T T
  defines "\<mu>T' \<equiv> MEM_TYPE (memT.memT \<mu>T @ [Some T])"
  assumes "mem_of_type \<mu>T \<mu>"
  assumes "of_type \<mu>T T v"
  shows "memT_le \<mu>T \<mu>T'" "mem_of_type \<mu>T' (MEM (memory.mem \<mu> @ [Some v]))"
proof -
  show 1: "memT_le \<mu>T \<mu>T'"
    unfolding \<mu>T'_def by (cases \<mu>T) auto

  have [simp]: "length (memT.memT \<mu>T') = Suc (length (memory.mem \<mu>))"
    using assms(2) unfolding \<mu>T'_def
      by (cases \<mu>T) (auto simp: mem_of_type_def list_all2_lengthD)

  have [simp]: "memT.memT \<mu>T' ! length (memory.mem \<mu>) = Some T"
    using assms(2)
    by (auto simp: \<mu>T'_def nth_append mem_of_type_def list_all2_lengthD)

  have [simp]: "memory.mem \<mu> ! i = None" if "i<length (memT.memT \<mu>T)" "memT.memT \<mu>T' ! i = None" for i
  proof -
    from that have "memT.memT \<mu>T ! i = None" unfolding \<mu>T'_def
      by (cases \<mu>T) (auto simp: nth_append split: if_splits)
    with assms(2) that show ?thesis
      by (auto simp: mem_of_type_def list_all2_conv_all_nth)
  qed

  show "mem_of_type \<mu>T' (MEM (memory.mem \<mu> @ [Some v]))"
    using assms(2,3) 1
    unfolding mem_of_type_def
    by (auto
      simp: list_all2_conv_all_nth nth_append less_Suc_eq_le of_type_memT_le rel_option_iff memT_le_idx_conv1
      split: option.splits)
qed

lemma tyco_block_allocate:
  assumes "mem_of_type \<mu>T \<mu>"
  assumes "of_type \<mu>T T v"
  shows "mwp (run (block_allocate v) \<mu>) bot no_static_err bot (\<lambda>p \<mu>'.
    \<exists>\<mu>T'. memT_le \<mu>T \<mu>T' \<and> mem_of_type \<mu>T' \<mu>' \<and> the_block p < length (memT.memT \<mu>T') \<and> memT.memT \<mu>T'!the_block p = Some T)"
  using tyco_block_allocate_aux[OF assms]
  by (fastforce
    simp: block_allocate_def run_simps
    split: option.splits
    dest: mem_of_type_lengthD[symmetric])

lemma tyco_block_free_aux1:
  assumes "b < length (\<mu>T)"
  shows "memT_le (MEM_TYPE \<mu>T) (MEM_TYPE (\<mu>T [b := None]))"
  using assms
  by (auto simp: nth_list_update)

lemma tyco_block_free_aux2:
  assumes "the_block b < length (memory.mem \<mu>)"
  assumes "mem_of_type \<mu>T \<mu>"
  shows "mem_of_type (MEM_TYPE (memT.memT \<mu>T [the_block b := None])) (MEM (memory.mem \<mu>[the_block b := None]))"
  using assms
  apply (cases \<mu>; cases \<mu>T)
  apply (auto simp: mem_of_type_def list_all2_conv_all_nth nth_list_update)
  apply (auto simp: rel_option_iff of_type_memT_le[OF tyco_block_free_aux1] split: option.splits)
  done


lemma tyco_block_free:
  assumes "mem_of_type \<mu>T \<mu>"
  shows "mwp (run (block_free b) \<mu>) bot no_static_err bot (\<lambda>p \<mu>'.
    \<exists>\<mu>T'. memT_le \<mu>T \<mu>T' \<and> mem_of_type \<mu>T' \<mu>')"
  using assms apply (cases \<mu>T)
  using tyco_block_free_aux2[OF _ assms(1)]
  by (auto 0 3
    simp: block_free_def run_simps mem_of_type_lengthD
    intro: tyco_block_free_aux1
    split: option.splits)


definition "tyI_exec_state \<mu>T sT s \<equiv>
    mem_of_type \<mu>T (exec_state.memory s)
  \<and> rel_fun (=) (rel_option (of_type \<mu>T)) sT (exec_state.lvars s)"



definition "lvty\<^sub>L x \<equiv> lift_lens (''Undef local variable '' @ lvar_name.the_name x) (fun\<^sub>L x \<bullet>\<^sub>L the\<^sub>L)"

lemma [simp]: "elens (lvty\<^sub>L x)"
  by (auto simp: lvty\<^sub>L_def)

(* TODO: Move *)
lemma [simp]: "elens (lvar\<^sub>L x)"
  by (auto simp: lvar\<^sub>L_def)

fun tyco_load_opr where
  "tyco_load_opr (OP_BCONST _) = return TBOOL"
| "tyco_load_opr (OP_ICONST _) = return TINT"
| "tyco_load_opr (OP_LVAR x) = use (lvty\<^sub>L x)"

definition tyco_load_ty_opr where
  "tyco_load_ty_opr ty opr \<equiv> doM {
    ty' \<leftarrow>tyco_load_opr opr;
    fcheck ''Opr type mismatch'' (ty'=ty);
    return ()
  }"

lemma [simp]: "get' exec_state.lvars\<^sub>L s = exec_state.lvars s"
  by (cases s) (auto simp: exec_state.lvars\<^sub>L_def)

lemma [simp]: "pre_get exec_state.lvars\<^sub>L s"
  by (cases s) (auto simp: exec_state.lvars\<^sub>L_def)

lemma tyco_load_opr:
  assumes "tyI_exec_state \<mu>T sT s"
  assumes "run (tyco_load_opr x) sT = SUCC T sT'"
  shows "mwp (run (load_opr x) s) bot no_static_err bot (\<lambda>v s'. s'=s \<and> sT'=sT \<and> of_type \<mu>T T v)"
  using assms
  apply (cases x; simp)
  apply (auto simp: run_simps split: option.splits)
  subgoal for v
    by (auto simp: tyI_exec_state_def lvty\<^sub>L_def lvar\<^sub>L_def dest: rel_funD[where x=v and y=v])
  subgoal for v e
    by (auto simp: lvar\<^sub>L_def lvty\<^sub>L_def tyI_exec_state_def dest: rel_funD[where x=v and y=v])
  done

lemma tyco_load_ty_opr:
  assumes "tyI_exec_state \<mu>T sT s"
  assumes "run (tyco_load_ty_opr ty x) sT = SUCC () sT'"
  shows "mwp (run (load_opr x) s) bot no_static_err bot (\<lambda>v s'. s'=s \<and> sT'=sT \<and> of_type \<mu>T ty v)"
  using assms
  unfolding tyco_load_ty_opr_def
  by (auto
    simp: run_simps
    elim!: mwp_eq_cases
    split: if_splits
    intro!: tyco_load_opr[THEN mwp_cons])


lemma tyco_to_int:
  assumes "of_type \<mu>T TINT v"
  shows "mwp (run (to_int v) s) bot no_static_err bot (\<lambda>_ s'. s'=s)"
  using assms by (auto simp: to_int_def run_simps split: val.splits option.splits)

lemma tyco_to_bool:
  assumes "of_type \<mu>T TBOOL v"
  shows "mwp (run (to_bool v) s) bot no_static_err bot (\<lambda>_ s'. s'=s)"
  using assms by (auto simp: to_bool_def run_simps split: val.splits option.splits)

lemma tyco_to_addr:
  assumes "of_type \<mu>T (TPTR ty) v"
  shows "mwp (run (to_addr v) s) bot no_static_err bot (\<lambda>v s'. s'=s \<and> addr_of_type \<mu>T v ty)"
  using assms by (auto simp: to_addr_def run_simps split: val.splits option.splits)


definition "tyco_load_int ty opr \<equiv> doM {
    fcheck ''Expected INT'' (ty = TINT);
    tyco_load_ty_opr ty opr
  }"

definition "tyco_load_bool ty opr \<equiv> doM {
    fcheck ''Expected BOOL'' (ty = TBOOL);
    tyco_load_ty_opr ty opr
  }"

definition "tyco_load_addr ty opr \<equiv> doM {
    fcheck ''Expected PTR'' (is_TPTR ty);
    tyco_load_ty_opr ty opr
  }"



lemma tyco_load_int:
  assumes "tyI_exec_state \<mu>T sT s"
  assumes "run (tyco_load_int ty x) sT = SUCC () sT'"
  shows "mwp (run (load_int x) s) bot no_static_err bot (\<lambda>v s'. s'=s \<and> sT'=sT \<and> ty=TINT)"
  using assms
  by (auto
    simp: run_simps load_int_def tyco_load_int_def
    intro!: mwp_cons[OF tyco_load_ty_opr] mwp_cons[OF tyco_to_int]
    elim!: mwp_eq_cases
    split: if_splits
    )

lemma tyco_load_bool:
  assumes "tyI_exec_state \<mu>T sT s"
  assumes "run (tyco_load_bool ty x) sT = SUCC () sT'"
  shows "mwp (run (load_bool x) s) bot no_static_err bot (\<lambda>v s'. s'=s \<and> sT'=sT \<and> ty=TBOOL)"
  using assms
  by (auto
    simp: run_simps load_bool_def tyco_load_bool_def
    intro!: mwp_cons[OF tyco_load_ty_opr] mwp_cons[OF tyco_to_bool]
    elim!: mwp_eq_cases
    split: if_splits
    )

lemma tyco_load_addr:
  assumes "tyI_exec_state \<mu>T sT s"
  assumes "run (tyco_load_addr ty x) sT = SUCC () sT'"
  shows "mwp (run (load_addr x) s) bot no_static_err bot
    (\<lambda>v s'. \<exists>ty'. s'=s \<and> sT'=sT \<and> ty=TPTR ty' \<and> addr_of_type \<mu>T v ty')"
  using assms
  apply (cases ty)
  apply (auto
    simp: run_simps load_addr_def tyco_load_addr_def
    intro!: mwp_cons[OF tyco_load_ty_opr] mwp_cons[OF tyco_to_addr]
    elim!: mwp_eq_cases
    split: if_splits
    )
  done

lemma of_type_uninit[simp]: "of_type \<mu>T ty (uninit ty)"
  apply (induction ty rule: uninit.induct)
  apply (auto simp: list_all2_conv_all_nth)
  done

lemma [simp]: "pre_get exec_state.local_blocks\<^sub>L s"
  by (auto simp: exec_state.local_blocks\<^sub>L_def split: exec_state.splits)

lemma rel_fun_opt_memT_le_mono:
  "\<lbrakk>rel_fun (=) (rel_option (of_type \<mu>T)) sT s; memT_le \<mu>T \<mu>T'\<rbrakk>
       \<Longrightarrow> rel_fun (=) (rel_option (of_type \<mu>T')) sT s"
  apply (rule rel_funI, drule rel_funD, assumption; clarsimp)
  subgoal for x
    by (cases "sT x"; cases "s x"; simp add: of_type_memT_le)
  done

lemma rel_opt_memT_le_mono:
  "\<lbrakk>rel_option (of_type \<mu>T) T v; memT_le \<mu>T \<mu>T'\<rbrakk>
       \<Longrightarrow> rel_option (of_type \<mu>T') T v"
  by (cases "T"; cases "v"; simp add: of_type_memT_le)


lemma tyco_instr_alloca:
  assumes "tyI_exec_state \<mu>T sT s"
  shows "mwp (run (instr_alloca ty n) s) bot no_static_err bot
    (\<lambda>r s'. \<exists>\<mu>T'. memT_le \<mu>T \<mu>T' \<and> tyI_exec_state \<mu>T' sT s' \<and> addr_of_type \<mu>T' r ty)"
  using assms
  apply (auto
    simp: instr_alloca_def run_simps tyI_exec_state_def
    intro!: mwp_cons[OF tyco_block_allocate[where T="TARRAY (nat n) ty"]]
    split: option.splits)
  apply (cases s; simp add: exec_state.memory\<^sub>L_def exec_state.local_blocks\<^sub>L_def)
  apply (intro exI conjI, assumption, assumption)
  apply (simp add: rel_fun_opt_memT_le_mono)
  apply (auto simp: addr_of_type_def Let_def split: option.splits)
  done

lemma tyco_instr_malloc:
  assumes "tyI_exec_state \<mu>T sT s"
  shows "mwp (run (instr_malloc ty n) s) bot no_static_err bot
    (\<lambda>r s'. \<exists>\<mu>T'. memT_le \<mu>T \<mu>T' \<and> tyI_exec_state \<mu>T' sT s' \<and> addr_of_type \<mu>T' r ty)"
  using assms
  apply (auto
    simp: instr_malloc_def run_simps tyI_exec_state_def
    intro!: mwp_cons[OF tyco_block_allocate[where T="TARRAY (nat n) ty"]]
    split: option.splits)
  apply (cases s; simp add: exec_state.memory\<^sub>L_def exec_state.local_blocks\<^sub>L_def)
  apply (intro exI conjI, assumption, assumption)
  apply (simp add: rel_fun_opt_memT_le_mono)
  apply (auto simp: addr_of_type_def Let_def split: option.splits)
  done

lemma tyco_instr_free:
  assumes "tyI_exec_state \<mu>T sT s"
  shows "mwp (run (instr_free x) s) bot no_static_err bot
    (\<lambda>_ s'. \<exists>\<mu>T'. memT_le \<mu>T \<mu>T' \<and> tyI_exec_state \<mu>T' sT s')"
  using assms
  apply (auto
    simp: instr_free_def run_simps tyI_exec_state_def
    intro!: mwp_cons[OF tyco_block_free]
    split: option.splits addr.splits list.splits va_item.splits nat.splits)
  apply (cases s; simp add: exec_state.memory\<^sub>L_def exec_state.local_blocks\<^sub>L_def)
  apply (intro exI conjI, assumption, assumption)
  apply (simp add: rel_fun_opt_memT_le_mono)
  done

  primrec tyco_exec_basic_instr_aux :: "_ \<Rightarrow> (_,unit,_,_) M" where
    "tyco_exec_basic_instr_aux (ADD ty op1 op2) = doM {
      tyco_load_int ty op1;
      tyco_load_int ty op2;
      return (Some TINT)
    }"
  | "tyco_exec_basic_instr_aux (SUB ty op1 op2) = doM {
      tyco_load_int ty op1;
      tyco_load_int ty op2;
      return (Some TINT)
    }"
  | "tyco_exec_basic_instr_aux (ICMP code ty op1 op2) = doM {
      tyco_load_int ty op1;
      tyco_load_int ty op2;
      return (Some TBOOL)
    }"
  | "tyco_exec_basic_instr_aux (AND ty op1 op2) = doM {
      tyco_load_bool ty op1;
      tyco_load_bool ty op2;
      return (Some TBOOL)
    }"
  | "tyco_exec_basic_instr_aux (OR ty op1 op2) = doM {
      tyco_load_bool ty op1;
      tyco_load_bool ty op2;
      return (Some TBOOL)
    }"
  | "tyco_exec_basic_instr_aux (NOT ty op1) = doM {
      tyco_load_bool ty op1;
      return (Some TBOOL)
    }"
  | "tyco_exec_basic_instr_aux (ALLOCA ty tyi opr) = doM {
      tyco_load_int tyi opr;
      return (Some (TPTR ty))
    }"
  | "tyco_exec_basic_instr_aux (MALLOC ty tyi opr) = doM {
      tyco_load_int tyi opr;
      return (Some (TPTR ty))
    }"
  | "tyco_exec_basic_instr_aux (FREE ty opr) = doM {
      tyco_load_addr ty opr;
      return None
    }"
  | "tyco_exec_basic_instr_aux (LOAD ty opr) = doM {
      tyco_load_addr (TPTR ty) opr;
      return (Some ty)
    }"
  | "tyco_exec_basic_instr_aux (STORE ty oprv oprp) = doM {
      tyco_load_ty_opr ty oprv;
      tyco_load_addr (TPTR ty) oprp;
      return None
    }"
  | "tyco_exec_basic_instr_aux (INSERT_A_VALUE bty bopr ety eopr idx) = doM {
      tyco_load_ty_opr bty bopr;
      tyco_load_ty_opr ety eopr;
      fcheck ''insert_a_value type mismatch'' (case bty of TARRAY _ ety' \<Rightarrow> ety=ety' | _ \<Rightarrow> False);
      return (Some bty)
    }"
  | "tyco_exec_basic_instr_aux (INSERT_S_VALUE bty bopr ety eopr idx) = doM {
      tyco_load_ty_opr bty bopr;
      tyco_load_ty_opr ety eopr;
      fcheck ''insert_s_value type mismatch'' (case bty of
         TSTRUCT ftys \<Rightarrow> idx<length ftys \<and> ftys!idx = ety
       | _ \<Rightarrow> False);
      return (Some bty)
    }"
  | "tyco_exec_basic_instr_aux (EXTRACT_A_VALUE bty bopr idx) = doM {
      tyco_load_ty_opr bty bopr;
      case bty of
        TARRAY _ ty \<Rightarrow> return (Some ty)
      | _ \<Rightarrow> fail ''extract_a_value type mismatch''
    }"
  | "tyco_exec_basic_instr_aux (EXTRACT_S_VALUE bty bopr idx) = doM {
      tyco_load_ty_opr bty bopr;
      case bty of
        TSTRUCT ftys \<Rightarrow> doM {
          fcheck ''Field index out of range'' (idx < length ftys);
          return (Some (ftys!idx))
        }
      | _ \<Rightarrow> fail ''extract_s_value type mismatch''
    }"
  | "tyco_exec_basic_instr_aux (OFS_PTR bty bopr ity iopr) = doM {
      tyco_load_addr bty bopr;
      tyco_load_int ity iopr;
      return (Some bty)
    }"
  | "tyco_exec_basic_instr_aux (INDEX_A_PTR bty bopr ity iopr) = doM {
      tyco_load_addr bty bopr;
      tyco_load_int ity iopr;
      case bty of
        TPTR (TARRAY _ ty) \<Rightarrow> return (Some (TPTR ty))
      | _ \<Rightarrow> fail ''index_a_ptr type mismatch''
    }"
  | "tyco_exec_basic_instr_aux (INDEX_S_PTR bty bopr idx) = doM {
      tyco_load_addr bty bopr;
      case bty of
        TPTR (TSTRUCT ftys) \<Rightarrow> doM {
          fcheck ''index_s_ptr field index out of range'' (idx < length ftys);
          return (Some (TPTR (ftys!idx)))
        }
      | _ \<Rightarrow> fail ''index_s_ptr type mismatch''
    }"

  term lookup

  definition "param_args_match \<mu>T params args \<equiv> list_all2 (of_type \<mu>T) (map fst params) args"

  primrec tyco_exec_nt_instr_aux :: "_ \<Rightarrow> _ \<Rightarrow> (_,unit,_,_) M" where
    "tyco_exec_nt_instr_aux \<pi> (BASIC i) = tyco_exec_basic_instr_aux i"
  | "tyco_exec_nt_instr_aux \<pi> (CALL ty name args) = doM {
      proc \<leftarrow> lookup ''Undefined procedure'' (proc_map \<pi>) name;
      mmap (uncurry tyco_load_ty_opr) args;
      fcheck ''Argument type mismatch'' (map fst (procedure.params proc) = map fst args);
      return (procedure.rtype proc)
    }"




(* TODO: Move *)
lemma memory\<^sub>L_put'_sel[simp]: "put' exec_state.memory\<^sub>L (exec_state.memory s) s = s"
  by (cases s) (auto simp: exec_state.memory\<^sub>L_def)

lemma memory\<^sub>L_sel_put'[simp]: "exec_state.memory (put' exec_state.memory\<^sub>L s' s) = s'"
  by (cases s) (auto simp: exec_state.memory\<^sub>L_def)

lemma exec_state_lvars_put_memory[simp]:
  "exec_state.lvars (put' exec_state.memory\<^sub>L \<mu> s) = exec_state.lvars s"
  by (cases s) (auto simp: exec_state.memory\<^sub>L_def)

lemma exec_state_memory_put_lvars[simp]: "exec_state.memory (put' exec_state.lvars\<^sub>L lvs s) = exec_state.memory s"
  by (cases s) (auto simp: exec_state.lvars\<^sub>L_def)

lemma [simp]: "exec_state.lvars (put' exec_state.lvars\<^sub>L l s) = l"
  by (cases s) (auto simp: exec_state.lvars\<^sub>L_def)

lemma tyco_instr_load:
  assumes "tyI_exec_state \<mu>T sT s"
  assumes "addr_of_type \<mu>T addr T"
  shows "mwp (run (instr_load addr) s) bot no_static_err bot (\<lambda>v s'. s'=s \<and> of_type \<mu>T T v)"
  using assms
  by (auto
    simp: run_simps instr_load_def Let_def tyI_exec_state_def
    split: option.splits if_splits
    intro!: tyco_use_lens_of_addr[THEN mwp_cons])

named_theorems_rev tyco_rules

method tyco_step = (
    (rule tyco_rules[THEN mwp_cons]; assumption?; clarsimp?)
  | (auto simp: run_simps map_mres_state_invert elim!: mwp_eq_cases split: option.splits if_splits)
)

method tyco = use nothing in \<open>insert method_facts, tyco_step+\<close>

lemmas [tyco_rules] = tyco_load_int tyco_load_bool tyco_instr_alloca
  tyco_instr_malloc tyco_instr_free tyco_load_addr tyco_instr_load tyco_load_ty_opr
  tyco_use_lens_of_addr tyco_put_lens_of_addr
  tyco_block_free


lemma same_type_imp_same_struct: "of_type \<mu>T T a \<Longrightarrow> of_type \<mu>T T b \<Longrightarrow> same_struct a b"
  apply (induction T a arbitrary: b rule: of_type.induct)
  apply (auto simp: list_all2_conv_all_nth)
  apply (case_tac [!] b)
  apply (fastforce simp: list_all2_conv_all_nth in_set_conv_nth)+
  done


lemma tyco_instr_store[tyco_rules]:
  assumes "tyI_exec_state \<mu>T sT s"
  assumes "addr_of_type \<mu>T addr T"
  assumes "of_type \<mu>T T v"
  shows "mwp (run (instr_store v addr) s) bot no_static_err bot (\<lambda>_ s'. tyI_exec_state \<mu>T sT s')"
  using assms
  unfolding instr_store_def Let_def tyI_exec_state_def
  apply (cases s)
  apply clarsimp
  apply tyco
  apply (simp add: same_type_imp_same_struct)
  apply tyco
  done

lemma [simp]:
  "pre_get addr.vaddr\<^sub>L x"
  "get' addr.vaddr\<^sub>L (ADDR blk va) = va"
  "put' addr.vaddr\<^sub>L va' (ADDR blk va) = ADDR blk va'"
  by (auto simp: addr.vaddr\<^sub>L_def split: addr.splits)

lemma [simp]:
  "pre_get va_item.aidx\<^sub>L va = is_VA_ARRAY_IDX va"
  "get' va_item.aidx\<^sub>L (VA_ARRAY_IDX idx) = idx"
  "put' va_item.aidx\<^sub>L idx' (VA_ARRAY_IDX idx) = VA_ARRAY_IDX idx'"
  by (auto simp: va_item.aidx\<^sub>L_def split: va_item.split)


lemma vaddr_of_type_change_last_array_idx: "vaddr_of_type bT (vas @ [VA_ARRAY_IDX i]) T
  \<Longrightarrow> vaddr_of_type bT (vas @ [VA_ARRAY_IDX i']) T"
  apply (induction bT vas T rule: vaddr_of_type.induct)
  apply auto
  apply (case_tac bT; case_tac T; auto)
  done

lemma vaddr_of_type_append_aidx:
  assumes "vaddr_of_type bT vas (TARRAY n T)"
  shows "vaddr_of_type bT (vas @ [VA_ARRAY_IDX idx]) T"
  using assms
  apply (induction bT vas T rule: vaddr_of_type.induct)
  apply auto
  done

lemma addr_of_type_append_aidx:
  assumes "addr_of_type \<mu>T addr (TARRAY n T)"
  shows "addr_of_type \<mu>T (put' addr.vaddr\<^sub>L (get' addr.vaddr\<^sub>L addr @ [VA_ARRAY_IDX idx]) addr) T"
  using assms
  apply (cases addr)
  unfolding addr_of_type_def Let_def
  apply (auto simp: vaddr_of_type_append_aidx split: if_splits option.splits)
  done

lemma vaddr_of_type_append_fidx:
  assumes "vaddr_of_type bT vas (TSTRUCT Ts)"
  assumes "idx < length Ts"
  shows "vaddr_of_type bT (vas @ [VA_FIELD_IDX idx]) (Ts!idx)"
  using assms
  apply (induction bT vas T\<equiv>"Ts!idx" rule: vaddr_of_type.induct)
  apply auto
  done

lemma addr_of_type_append_fidx:
  assumes "addr_of_type \<mu>T addr (TSTRUCT Ts)"
  assumes "idx < length Ts"
  shows "addr_of_type \<mu>T (put' addr.vaddr\<^sub>L (get' addr.vaddr\<^sub>L addr @ [VA_FIELD_IDX idx]) addr) (Ts!idx)"
  using assms
  apply (cases addr)
  unfolding addr_of_type_def Let_def
  apply (auto simp: vaddr_of_type_append_fidx split: if_splits option.splits)
  done

lemma tyco_instr_ofs_addr[tyco_rules]:
  assumes "addr_of_type \<mu>T a ty"
  shows "mwp (run (instr_ofs_addr a i) s) bot no_static_err bot (\<lambda>a' s'. s'=s \<and> addr_of_type \<mu>T a' ty)"
  using assms
  apply (cases a)
  subgoal for blk va
    apply (cases va rule: rev_cases)
    subgoal by (auto simp: run_simps instr_ofs_addr_def split: option.splits)
    subgoal for vas vai
      apply (cases vai)
      by (auto
        simp: run_simps instr_ofs_addr_def addr_of_type_def Let_def
        elim!: vaddr_of_type_change_last_array_idx
        split: option.splits)
    done
  done

thm memT_le_refl

lemma tyco_exec_basic_instr_aux[tyco_rules]:
  assumes "tyI_exec_state \<mu>T sT s"
  assumes "run (tyco_exec_basic_instr_aux instr) sT = SUCC T sT'"
  shows "mwp (run (exec_basic_instr_aux instr) s) bot no_static_err bot
    (\<lambda>v s'. \<exists>\<mu>T'. memT_le \<mu>T \<mu>T' \<and> tyI_exec_state \<mu>T' sT' s' \<and> rel_option (of_type \<mu>T') T v)"
  using assms
  apply (cases instr; simp)
  subgoal unfolding instr_add_def by tyco
  subgoal unfolding instr_sub_def by tyco
  subgoal for code ty op1 op2 by (cases code; simp; tyco)
  subgoal unfolding instr_not_def by tyco
  subgoal unfolding instr_and_def by tyco
  subgoal unfolding instr_or_def by tyco
  subgoal by tyco
  subgoal by tyco
  subgoal by tyco
  subgoal by tyco
  subgoal by tyco
  subgoal
    supply [split] = type.splits
      and [simp] = same_type_imp_same_struct in_set_conv_nth Ball_def nth_list_update
    unfolding instr_insert_a_value_def put_same_struct_def
    by tyco
  subgoal
    supply [split] = type.splits val.splits
      and [simp] = same_type_imp_same_struct in_set_conv_nth Ball_def nth_list_update
      and [simp] = list_all2_conv_all_nth
    unfolding instr_insert_s_value_def put_same_struct_def
    by tyco
  subgoal
    supply [split] = type.splits val.splits
      and [simp] = same_type_imp_same_struct in_set_conv_nth Ball_def nth_list_update
      and [simp] = list_all2_conv_all_nth
    unfolding instr_extract_a_value_def put_same_struct_def
    by tyco
  subgoal
    supply [split] = type.splits val.splits
      and [simp] = same_type_imp_same_struct in_set_conv_nth Ball_def nth_list_update
      and [simp] = list_all2_conv_all_nth
    unfolding instr_extract_s_value_def put_same_struct_def
    by tyco
  subgoal by tyco
  subgoal
    supply [split] = type.splits
    supply [simp] = addr_of_type_append_aidx
    unfolding instr_idx_array_def to_idx_def
    by tyco
  subgoal
    supply [split] = type.splits
    supply [simp] = addr_of_type_append_fidx
    unfolding instr_idx_field_def to_idx_def
    apply tyco
    done
  done


lemma tyco_mmap_load_opr[tyco_rules]:
  assumes "tyI_exec_state \<mu>T sT s"
  assumes "run (mmap (uncurry tyco_load_ty_opr) ops) sT = (SUCC uus sT' :: (_,'e,_,_) mres)"
  shows "mwp (run (mmap (load_opr o snd) ops) s) bot no_static_err bot
    (\<lambda>vs s'. sT'=sT \<and> s'=s \<and> list_all2 (of_type \<mu>T) (map fst ops) vs)"
  using assms(2)
proof (induction ops arbitrary: uus)
  case Nil
  then show ?case by tyco
next
  case (Cons ty_opr ops)

  obtain ty opr where [simp]: "ty_opr=(ty,opr)" by (cases ty_opr)

  from Cons.prems obtain sTh where
        1: "run (tyco_load_ty_opr ty opr) sT = (SUCC () sTh :: (_,'e,_,_) mres)"
    and 2: "run (mmap (uncurry tyco_load_ty_opr) ops) sTh = (SUCC (tl uus) sT' :: (_,'e,_,_) mres)  "
    by (auto simp: run_simps elim!: mwp_eq_cases)

  note [tyco_rules] = tyco_load_ty_opr[OF assms(1) 1] Cons.IH[simplified]
  show ?case using 2 by tyco
qed

lemma run_noexcept[run_simps]:
  "run (noexcept m) s = mwp (run m s) NTERM FAIL (\<lambda>_ _. FAIL (STATIC_ERROR ''noexcept'')) SUCC"
  unfolding noexcept_def
  by (simp add: run_simps cong del: mwp_cong)


definition tyco_define_lvar :: "_ \<Rightarrow> _ \<Rightarrow> (_,unit,_,_) M" where
  "tyco_define_lvar ty name \<equiv> (doM {
    l\<leftarrow>get;
    fcheck (''lvar redefined'') (name \<notin> dom l);
    let l = l(name\<mapsto>ty);
    set l
  })"

lemma tyco_define_lvar[tyco_rules]:
  assumes "tyI_exec_state \<mu>T sT s"
  assumes "of_type \<mu>T ty v"
  assumes "run (tyco_define_lvar ty name) sT = SUCC () sT'"
  shows "mwp (run (define_lvar name v) s) bot no_static_err bot (\<lambda>_ s'.
    tyI_exec_state \<mu>T sT' s')"
  using assms
  unfolding define_lvar_def tyco_define_lvar_def tyI_exec_state_def
  apply tyco
  apply (metis (full_types) option.rel_distinct(1) rel_funD)
  using rel_funD by fastforce


primrec tyco_exec_nt_instr where
  "tyco_exec_nt_instr \<pi> (NT_INSTR resname i) = doM {
    rT \<leftarrow> tyco_exec_nt_instr_aux \<pi> i;
    case resname of
      None \<Rightarrow> return ()
    | Some resvar \<Rightarrow> doM {
      rT \<leftarrow> mget (lift_lens '''' the\<^sub>L) rT;
      tyco_define_lvar rT resvar
    }
  }"

context
  fixes proc :: procedure
begin

  primrec tyco_exec_t_instr where
    "tyco_exec_t_instr (RETURN_VOID) =
      fcheck ''Non-void procedure returns void'' (procedure.rtype proc = None)"
  | "tyco_exec_t_instr (RETURN ty opr) = doM {
      tyco_load_ty_opr ty opr;
      fcheck ''Procedure return type mismatch'' (procedure.rtype proc = Some ty)
    }"
  | "tyco_exec_t_instr (BR label) = fcheck ''Undefined label'' (label \<in> fst`list.set (procedure.blocks proc))"
  | "tyco_exec_t_instr (CBR opr ltrue lfalse) = doM {
      tyco_load_bool TBOOL opr;
      fcheck ''Undefined label'' ({ltrue,lfalse} \<subseteq> fst`list.set (procedure.blocks proc))
  }"


  lemma tyco_exec_t_instr[tyco_rules]:
    assumes "tyI_exec_state \<mu>T sT s"
    assumes "run (tyco_exec_t_instr instr) sT = SUCC uu sT'"
    shows "mwp (run (exec_t_instr instr) s) bot no_static_err
      (\<lambda>rv s'. s'=s \<and> sT'=sT \<and> rel_option (of_type \<mu>T) (procedure.rtype proc) rv)
      (\<lambda>l s'. s'=s \<and> sT'=sT \<and> l\<in>fst`list.set (procedure.blocks proc))"
    using assms
    apply (cases instr; simp)
    by tyco

  definition "tyco_exec_block \<pi> \<equiv> \<lambda>BBLOCK ntis ti\<Rightarrow> doM {
    (* Execute nonterminal instructions *)
    mfold' (tyco_exec_nt_instr \<pi>) ntis;
    (* Execute terminal instruction *)
    tyco_exec_t_instr ti
  }"


  definition "tyco_exec_block_reset \<pi> block \<equiv> doM {
    saved_lts \<leftarrow> get;
    mmblock get (\<lambda>_. set saved_lts) (tyco_exec_block \<pi> block)
  }"


end

definition "tyco_exec_proc \<pi> proc \<equiv>
  case proc of PROC params prologue blocks rtype \<Rightarrow> doM {
    mblock (\<lambda>_. Map.empty) (\<lambda>_. ()) (doM {

      \<comment> \<open>Define Parameters\<close>
      mfold' (uncurry tyco_define_lvar) params;

      \<comment> \<open>Execute Prologue\<close>
      tyco_exec_block proc \<pi> prologue;

      \<comment> \<open>Execute Blocks\<close>
      mmap (tyco_exec_block_reset proc \<pi>) (map snd blocks);

      return ()
    })
}"


(*
definition "tyco_exec_proc \<pi> proc args \<equiv>
  case proc of PROC params prologue blocks rtype \<Rightarrow> doM {
    fcheck (''|arg| != |param|'') (length params = length args);
    fcheck (''arg-types !~ param-types'') (args = map fst params);
    mblock (\<lambda>_. Map.empty) (\<lambda>_. ()) (doM {

      (* Define Parameters*)
      mfold' (uncurry tyco_define_lvar) params;

      (* Execute Prologue *)
      tyco_exec_block proc \<pi> prologue;

      (* Execute Blocks *)
      mmap (tyco_exec_block_reset proc \<pi>) (map snd blocks);

      return ()
    })
}"
*)

locale tyco_exec_proc_name_IH =
  fixes exec_proc_name :: "proc_name \<times> val list \<Rightarrow> (val option, unit, val memory, err) M"
    and \<pi> :: program
  assumes tyco_exec_proc_name[tyco_rules]: "\<lbrakk>
    proc_map \<pi> pname = Some proc;
    param_args_match \<mu>T (procedure.params proc) args;
    mem_of_type \<mu>T \<mu>
  \<rbrakk> \<Longrightarrow> mwp (run (exec_proc_name (pname,args)) \<mu>) top no_static_err bot
    (\<lambda>r \<mu>'. \<exists>\<mu>T'. memT_le \<mu>T \<mu>T' \<and> mem_of_type \<mu>T' \<mu>' \<and> rel_option (of_type \<mu>T') (procedure.rtype proc) r)"
begin

  lemma tyco_exec_nt_instr_aux[tyco_rules]:
    assumes "tyI_exec_state \<mu>T sT s"
    assumes "run (tyco_exec_nt_instr_aux \<pi> instr) sT = SUCC T sT'"
    shows "mwp (run (exec_nt_instr_aux exec_proc_name instr) s) top no_static_err bot
      (\<lambda>v s'. \<exists>\<mu>T'. memT_le \<mu>T \<mu>T' \<and> tyI_exec_state \<mu>T' sT' s' \<and> rel_option (of_type \<mu>T') T v)"
    using assms
    apply (cases instr; simp)
    subgoal by tyco
    subgoal
      supply [simp] = tyI_exec_state_def param_args_match_def
      supply [intro] = rel_fun_opt_memT_le_mono
      by tyco
    done

  lemma tyco_exec_nt_instr[tyco_rules]:
    assumes "tyI_exec_state \<mu>T sT s"
    assumes "run (tyco_exec_nt_instr \<pi> instr) sT = SUCC T sT'"
    shows "mwp (run (exec_nt_instr exec_proc_name instr) s) top no_static_err bot
      (\<lambda>_ s'. \<exists>\<mu>T'. memT_le \<mu>T \<mu>T' \<and> tyI_exec_state \<mu>T' sT' s')"
    using assms
    apply (cases instr; simp)
    supply [simp] = option.rel_sel
    by tyco

  lemma tyco_exec_nt_instrs[tyco_rules]:
    assumes "tyI_exec_state \<mu>T sT s"
    assumes "run (mfold' (tyco_exec_nt_instr \<pi>) instrs) sT = SUCC T sT'"
    shows "mwp (run (mfold' (exec_nt_instr exec_proc_name) instrs) s) top no_static_err bot
        (\<lambda>_ s'. \<exists>\<mu>T'. memT_le \<mu>T \<mu>T' \<and> tyI_exec_state \<mu>T' sT' s')"
    using assms
  proof (induction instrs arbitrary: \<mu>T sT s)
    case Nil
    then show ?case by tyco
  next
    case (Cons a instrs)

    from Cons.prems show ?case
      supply [dest] = memT_le_trans
      apply tyco
      (* Have to apply this rule explicitly, as assumption must be applied to
        first subgoal first, not to last subgoal as in default ;assumption?
      *)
      apply (rule Cons.IH[THEN mwp_cons], assumption)
      apply tyco
      done

  qed


  lemma tyco_exec_block[tyco_rules]:
    assumes "tyI_exec_state \<mu>T sT s"
    assumes "run (tyco_exec_block proc \<pi> blk) sT = SUCC uu sT'"
    shows "mwp (run (exec_block exec_proc_name blk) s) top no_static_err
      (\<lambda>rv s'. \<exists>\<mu>T'. memT_le \<mu>T \<mu>T' \<and> tyI_exec_state \<mu>T' sT' s' \<and> rel_option (of_type \<mu>T') (procedure.rtype proc) rv)
      (\<lambda>l s'. \<exists>\<mu>T'. memT_le \<mu>T \<mu>T' \<and> tyI_exec_state \<mu>T' sT' s' \<and> l\<in>fst`list.set (procedure.blocks proc))"
  proof -
    show ?thesis
      using assms unfolding exec_block_def tyco_exec_block_def
      apply (cases blk; simp)
      by tyco
  qed

  lemma tyco_exec_block_reset[tyco_rules]:
    assumes "tyI_exec_state \<mu>T sT s"
    assumes "run (tyco_exec_block_reset proc \<pi> blk) sT = SUCC uu sT'"
    shows "mwp (run (exec_block_reset exec_proc_name blk) s) top no_static_err
      (\<lambda>rv s'. \<exists>\<mu>T'. memT_le \<mu>T \<mu>T' \<and> exec_state.lvars s' = exec_state.lvars s \<and> sT'=sT \<and> tyI_exec_state \<mu>T' sT s' \<and> rel_option (of_type \<mu>T') (procedure.rtype proc) rv)
      (\<lambda>l s'. \<exists>\<mu>T'. memT_le \<mu>T \<mu>T' \<and> exec_state.lvars s' = exec_state.lvars s \<and> sT'=sT \<and> tyI_exec_state \<mu>T' sT s' \<and> l\<in>fst`list.set (procedure.blocks proc))"
    using assms
    unfolding tyco_exec_block_reset_def exec_block_reset_def
    apply tyco
    unfolding tyI_exec_state_def
    apply (auto intro: rel_fun_opt_memT_le_mono)
    done

  term tyco_exec_proc
  term exec_proc

  lemma tyco_mfold_define_lvar[tyco_rules]:
    assumes "tyI_exec_state \<mu>T sT s"
    assumes "map fst nvs = map snd tns"
    assumes "list_all2 (of_type \<mu>T) (map fst tns) (map snd nvs)"
    assumes "run (mfold' (uncurry tyco_define_lvar) tns) sT = SUCC () sT'"
    shows "mwp (run (mfold' (uncurry define_lvar) nvs) s) bot no_static_err bot (\<lambda>_ s'.
      tyI_exec_state \<mu>T sT' s'
    )"
    using assms
  proof (induction nvs arbitrary: tns sT s)
    case Nil
    then show ?case by tyco
  next
    case (Cons a nvs)

    note Cons.IH[tyco_rules]

    from Cons.prems show ?case
      by (cases a; clarsimp) tyco

  qed

  lemma tyI_exec_state_fresh[simp]:
    "tyI_exec_state \<mu>T Map.empty (mk_fresh_exec_state \<mu>) = mem_of_type \<mu>T \<mu>"
    by (auto simp: tyI_exec_state_def mk_fresh_exec_state_def)

  (* TODO: Move *)
  lemma tyI_exec_state_simp[simp]:
    "tyI_exec_state \<mu>T sT (EXEC_STATE lvs lbs \<mu>) \<longleftrightarrow> mem_of_type \<mu>T \<mu> \<and> rel_fun (=) (rel_option (of_type \<mu>T)) sT lvs"
    by (simp add: tyI_exec_state_def)

  lemma exec_state_memory\<^sub>L_put'_simp[simp]:
    "put' exec_state.memory\<^sub>L sh (EXEC_STATE x1 x2 x3) = EXEC_STATE x1 x2 sh"
    by (auto simp: exec_state.memory\<^sub>L_def)


  lemma tyco_mfold_free_alloca_blocks[tyco_rules]:
    assumes "tyI_exec_state \<mu>T sT s"
    shows "mwp (run (mfold' (\<lambda>x. zoom (exec_state.memory\<^sub>L)\<^sub>S (block_free x)) bs) s)
      bot no_static_err bot (\<lambda>_ s'. \<exists>\<mu>T'. memT_le \<mu>T \<mu>T' \<and>  tyI_exec_state \<mu>T' sT s')"
    using assms
  proof (induction bs arbitrary: s \<mu>T)
    case Nil
    then show ?case by tyco
  next
    case (Cons a bs)
    note Cons.IH

    from Cons.prems show ?case
      apply (cases s; simp add: )
      apply tyco
      subgoal for x1 x2 x3 sh \<mu>Th
        apply (rule Cons.IH[of \<mu>Th, THEN mwp_cons])
        by (auto simp: rel_fun_opt_memT_le_mono dest: memT_le_trans)
      done
  qed

  lemma exec_state_mem_of_typeI: "tyI_exec_state \<mu>T sT s \<Longrightarrow> mem_of_type \<mu>T (exec_state.memory s)"
    unfolding tyI_exec_state_def by simp


  lemma tyco_exec_blocks_aux:
    assumes "tyI_exec_state \<mu>T sT s"
    assumes "l\<in>L"
    assumes IH: "\<And>l \<mu>Th sh. \<lbrakk> memT_le \<mu>T \<mu>Th; tyI_exec_state \<mu>Th sT sh; l\<in>L\<rbrakk> \<Longrightarrow>
      mwp (run (f l) sh) top no_static_err
        (\<lambda>rv s'. \<exists>\<mu>T'. memT_le \<mu>Th \<mu>T' \<and> tyI_exec_state \<mu>T' sT s' \<and> rel_option (of_type \<mu>T') rT rv)
        (\<lambda>l s'. \<exists>\<mu>T'. memT_le \<mu>Th \<mu>T' \<and> tyI_exec_state \<mu>T' sT s' \<and> l\<in>L)
    "
    shows "mwp (run (mwhile (\<lambda>_. return True) f l) s)
      top no_static_err (\<lambda>rv s'. \<exists>\<mu>T'. memT_le \<mu>T \<mu>T' \<and> tyI_exec_state \<mu>T' sT s' \<and>  rel_option (of_type \<mu>T') rT rv) bot"
    apply (rule mwhile_invar_rule[OF refl,
      where I="\<lambda>l s'. \<exists>\<mu>T'. memT_le \<mu>T \<mu>T' \<and> tyI_exec_state \<mu>T' sT s' \<and> l\<in>L"])
    subgoal by simp
    subgoal using assms by auto
    subgoal
      apply tyco
      apply (rule IH[THEN mwp_cons])
      apply (assumption | simp)+
      apply (auto dest: memT_le_trans)
      done
    done


  lemma tyco_exec_block_reset_pres_sT_aux: "run (tyco_exec_block_reset proc \<pi> blk) sT = SUCC uu sT' \<Longrightarrow> sT'=sT"
    unfolding tyco_exec_block_reset_def
    by (auto simp: run_simps elim!: mwp_eq_cases)

  lemma tyco_exec_block_reset_pres_sT[simp]:
    "NO_MATCH sT' sT \<Longrightarrow> run (tyco_exec_block_reset proc \<pi> blk) sT = SUCC uu sT' \<longleftrightarrow>
    run (tyco_exec_block_reset proc \<pi> blk) sT = SUCC uu sT \<and> sT'=sT"
    using tyco_exec_block_reset_pres_sT_aux by blast

  lemma mmap_tyco_exec_block_reset_pres_sT_aux:
    assumes "run (mmap (tyco_exec_block_reset proc \<pi>) blks) s = SUCC (uul::unit list) ss'"
    shows "ss' = s"
    using assms
    apply (induction blks arbitrary: s uul)
    by (auto simp: run_simps elim!: mwp_eq_cases)

  lemma mmap_tyco_exec_block_reset_pres_sT[simp]:
    "NO_MATCH s' s \<Longrightarrow> run (mmap (tyco_exec_block_reset proc \<pi>) blks) s = SUCC (uul::unit list) s'
      \<longleftrightarrow> run (mmap (tyco_exec_block_reset proc \<pi>) blks) s = SUCC (uul::unit list) s \<and> s'=s"
    using mmap_tyco_exec_block_reset_pres_sT_aux[of proc blks s uul s'] by blast

  lemma run_tyco_mmapI:
    assumes "run (mmap (tyco_exec_block_reset proc \<pi>) blks) s = SUCC (uul::unit list) ss'"
    assumes "blk\<in>List.set blks"
    shows "run (tyco_exec_block_reset proc \<pi> blk) s = SUCC () s"
    using assms
    by (auto simp: in_set_conv_decomp run_simps elim!: mwp_eq_cases)


(*
  lemma tyco_exec_proc[tyco_rules]:
    assumes "mem_of_type \<mu>T \<mu>"
    assumes "list_all2 (of_type \<mu>T) argTs args"
    assumes "run (tyco_exec_proc \<pi> proc argTs) () = SUCC () ()"
    shows "mwp (run (exec_proc exec_proc_name proc args) \<mu>) top no_static_err bot (\<lambda>_ \<mu>'.
      \<exists>\<mu>T'. memT_le \<mu>T \<mu>T' \<and> mem_of_type \<mu>T' \<mu>'
    )"
  using assms
  unfolding tyco_exec_proc_def exec_proc_def
  (* TODO: Clean up this mess! *)
  apply (cases proc; clarsimp)
  supply [simp] = list_all2_lengthD[of _ argTs args, symmetric] exec_state_mem_of_typeI
  supply [dest] = memT_le_trans
  apply tyco
  apply (rule tyco_exec_blocks_aux[where L="fst`List.set (procedure.blocks proc)", THEN mwp_cons])
  apply (assumption)
  supply [simp] = weak_map_of_SomeI
  supply [elim!] = run_tyco_mmapI
  apply tyco
  apply (erule run_tyco_mmapI)
  using map_of_SomeD apply fastforce
  apply tyco
  apply (intro exI exec_state_mem_of_typeI conjI; assumption?)
  apply auto
  done
*)


  lemma tyco_exec_proc[tyco_rules]:
    assumes "mem_of_type \<mu>T \<mu>"
    assumes "list_all2 (of_type \<mu>T) (map fst (procedure.params proc)) args"
    assumes "run (tyco_exec_proc \<pi> proc) () = SUCC () ()"
    shows "mwp (run (exec_proc exec_proc_name proc args) \<mu>) top no_static_err bot (\<lambda>rv \<mu>'.
      \<exists>\<mu>T'. memT_le \<mu>T \<mu>T' \<and> mem_of_type \<mu>T' \<mu>' \<and> rel_option (of_type \<mu>T') (procedure.rtype proc) rv
    )"
  using assms
  unfolding tyco_exec_proc_def exec_proc_def
  (* TODO: Clean up this mess! *)
  apply (cases proc; clarsimp)
  supply [simp] = exec_state_mem_of_typeI rel_opt_memT_le_mono
  supply [dest] = memT_le_trans
  apply (frule list_all2_lengthD; simp)
  apply tyco
  apply (rule tyco_exec_blocks_aux[where L="fst`List.set (procedure.blocks proc)", THEN mwp_cons])
  apply (assumption)
  supply [simp] = weak_map_of_SomeI
  supply [elim!] = run_tyco_mmapI
  apply tyco
  apply (erule run_tyco_mmapI)
  using map_of_SomeD apply fastforce
  apply tyco
  apply (intro exI exec_state_mem_of_typeI conjI)
  prefer 2
  apply assumption
  apply auto
  done



end

definition "tyco_program \<pi> \<equiv> doM {
  fcheck ''Duplicate procedure name'' (distinct (map fst (program.procedures \<pi>)));
  mmap (tyco_exec_proc \<pi> o snd) (program.procedures \<pi>);
  return ()
}"

lemma tyco_exec_proc_name[tyco_rules]:
  assumes "(run (exec_proc_name \<pi> (pname,args)) \<mu>) = r"
  assumes "proc_map \<pi> pname = Some proc"
  assumes "param_args_match \<mu>T (procedure.params proc) args"
  assumes "mem_of_type \<mu>T \<mu>"
  assumes TYCO_PROG: "run (tyco_program \<pi>) () = SUCC () ()"
  shows "mwp r top no_static_err bot
    (\<lambda>r \<mu>'. \<exists>\<mu>T'. memT_le \<mu>T \<mu>T' \<and> mem_of_type \<mu>T' \<mu>' \<and> rel_option (of_type \<mu>T') (procedure.rtype proc) r)"
  using assms(1-4)
proof (induction "(pname,args)" \<mu> r arbitrary: pname proc args \<mu>T rule: exec_proc_name_partial)
  case (nterm s)
  then show ?case by tyco
next
  case (step exec_proc_name s r)

  from step.hyps(1)[OF refl]
  interpret tyco_exec_proc_name_IH exec_proc_name \<pi> by unfold_locales


  from step.prems have "(pname,proc) \<in> List.set (program.procedures \<pi>)"
    by (auto simp: proc_map_def map_of_SomeD)
  with TYCO_PROG have "run (tyco_exec_proc \<pi> proc) () = SUCC () ()"
    unfolding tyco_program_def
    by (auto simp: run_simps split: if_splits elim!: mwp_eq_cases dest!:run_mmap_unit_state_elemD)

  with step.hyps(2) step.prems show ?case
    unfolding param_args_match_def
    by tyco

qed

lemma mem_of_type_init[simp]: "mem_of_type (MEM_TYPE []) (MEM [])"
  by (auto simp: mem_of_type_def)



export_code tyco_program in SML

value "run (tyco_program test) ()"


typ "32 word"

oops

xxx, ctd here:
  Integer arithmetic, iXX types
  complete lens package, simp-lemma generation!
  fresh-monad to produce llvm code
  pretty-printer to actual llvm
  instantiate floyd verification, separation logic



end

