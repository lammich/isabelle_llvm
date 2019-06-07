theory LLVM_Semantics
imports Monad2 LLVM_Syntax LLVM_Memory
begin




  datatype memT = MEM_TYPE (memT: "type option list")
  hide_const (open) memT

  fun vaddr_of_type :: "type \<Rightarrow> vaddr \<Rightarrow> type \<Rightarrow> bool" where
    "vaddr_of_type bT [] T \<longleftrightarrow> T=bT"
  | "vaddr_of_type (TARRAY n bT) (VA_ARRAY_IDX i#as) T \<longleftrightarrow> \<^cancel>\<open>*i<n \<and> \<close> vaddr_of_type bT as T"
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
      "of_type (TINT w) (VINT v) \<longleftrightarrow> w = wpi_width v"
    | "of_type (TPTR T) (VPTR (Some (Some a))) \<longleftrightarrow> addr_of_type a T"
    | "of_type (TPTR T) (VPTR _) \<longleftrightarrow> True"
    | "of_type (TARRAY n T) (VARRAY vs) \<longleftrightarrow> n=length vs \<and> (\<forall>v\<in>List.set vs. of_type T v)"
    | "of_type (TSTRUCT Ts) (VSTRUCT vs) \<longleftrightarrow> list_all2 of_type Ts vs"
    | "of_type _ _ \<longleftrightarrow> False"

  end

  definition mem_of_type :: "memT \<Rightarrow> memory \<Rightarrow> bool"
    where "mem_of_type \<mu>T \<mu> \<equiv> list_all2 (rel_option (of_type \<mu>T)) (memT.memT \<mu>T) (map (map_option fst) (get' (mem\<^sub>L) \<mu>))"

  lemma mem_of_type_lengthD:
    "mem_of_type \<mu>T \<mu> \<Longrightarrow> length (memT.memT \<mu>T) = length (get' mem\<^sub>L \<mu>)"
    "mem_of_type (MEM_TYPE Ts) \<mu> \<Longrightarrow> length (Ts) = length (get' mem\<^sub>L \<mu>)"
    by (auto simp: mem_of_type_def list_all2_lengthD)





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



  datatype exec_state = EXEC_STATE
    (lvars: "lvar_name \<rightharpoonup> val")
    (local_blocks: "block_addr list")
    (memory: "memory")
  hide_const (open) lvars local_blocks memory
  define_lenses (open) exec_state

  (*
  lemma exec_state_l_indep[simp]: 
    "exec_state.lvars\<^sub>L \<bowtie> exec_state.memory\<^sub>L"
    "exec_state.lvars\<^sub>L \<bowtie> exec_state.local_blocks\<^sub>L"
    "exec_state.local_blocks\<^sub>L \<bowtie> exec_state.memory\<^sub>L"
    apply unfold_locales
    unfolding exec_state.lvars\<^sub>L_def exec_state.memory\<^sub>L_def exec_state.local_blocks\<^sub>L_def
    find_theorems "\<not>True \<longleftrightarrow> False"
    apply (simp only: LENS_downstage option.sel exec_state.simps option.simps HOL.simp_thms split: exec_state.splits | intro allI impI conjI)+
  *)
  


  definition "lvar\<^sub>L x \<equiv> (exec_state.lvars\<^sub>L \<bullet>\<^sub>L fun\<^sub>L x \<bullet>\<^sub>L the\<^sub>L)\<^sub>S"
  lemma lvar\<^sub>L_elens[simp]: "elens (lvar\<^sub>L x)"
    by (auto simp: lvar\<^sub>L_def)
  

  fun load_opr where
    "load_opr ty (OP_ICONST i) = (
      case ty of
        TINT w \<Rightarrow> doM {
          fcheck (STATIC_ERROR ''i0 type'') (w\<noteq>0); \<^cancel>\<open>TODO: How does LLVM handle overflow? The same way as lconst? \<close>
          return (VINT (Inr (lconst w i)))
        }
      | _ \<Rightarrow> fail (STATIC_ERROR ''int const with non-int type''))"
  | "load_opr _ (OP_LVAR x) = use (lvar\<^sub>L x)" \<comment> \<open>We omit a type check here\<close>



  definition "to_idx i \<equiv> doM {fcheck MEM_ERROR (i\<ge>0); return (nat i)}"

  definition load_int where
    "load_int ty opr \<equiv> doM {
      v \<leftarrow> load_opr ty opr;
      to_lint v
    }"

  definition load_ptr where
    "load_ptr ty opr \<equiv> doM {
      v \<leftarrow> load_opr ty opr;
      to_ptr v
    }"

  definition load_addr where
    "load_addr ty opr \<equiv> doM {
      v \<leftarrow> load_opr ty opr;
      to_addr v
    }"

  definition load_bool where
    "load_bool ty opr \<equiv> doM {
      v \<leftarrow> load_opr ty opr;
      to_bool v
    }"


  definition define_lvar where
    "define_lvar name val \<equiv> zoom (exec_state.lvars\<^sub>L)\<^sub>S (doM {
      l\<leftarrow>get;
      fcheck (STATIC_ERROR ''lvar redefined'') (name \<notin> dom l);
      let l = l(name\<mapsto>val);
      set l
    })"


definition "noexcept m \<equiv> handle m (\<lambda>_. fail (STATIC_ERROR ''noexcept''))"
lemma noexcept_mono[partial_function_mono]:
  "monotone M.le_fun M_ord m \<Longrightarrow> monotone M.le_fun M_ord (\<lambda>f. noexcept (m f))"
  unfolding noexcept_def
  by pf_mono_prover


fun lint_icmp where
  "lint_icmp icmp_code.EQ a b \<longleftrightarrow>  (a = b)"
| "lint_icmp icmp_code.NE a b \<longleftrightarrow>  (a \<noteq> b)"
| "lint_icmp icmp_code.ULE a b \<longleftrightarrow> (a \<le> b)"
| "lint_icmp icmp_code.ULT a b \<longleftrightarrow> (a < b)"
| "lint_icmp icmp_code.SLE a b \<longleftrightarrow> (a \<le>\<^sub>s b)"
| "lint_icmp icmp_code.SLT a b \<longleftrightarrow> (a <\<^sub>s b)"


definition "instr_alloca ty n = doM {
  fcheck MEM_ERROR (n>0);
  let n = nat n;
  let v = uninit (TARRAY n ty);
  r \<leftarrow> zoom (exec_state.memory\<^sub>L)\<^sub>S (block_allocate block_type.ON_STACK v);
  (exec_state.local_blocks\<^sub>L)\<^sub>S %= (#) r;
  return (ADDR r [VA_ARRAY_IDX 0])
}"

(*definition "instr_malloc ty n = doM {
  fcheck MEM_ERROR (n>0);
  let n = nat n;
  let v = uninit (TARRAY n ty);
  r \<leftarrow> zoom (exec_state.memory\<^sub>L)\<^sub>S (block_allocate block_type.ON_HEAP v);
  return (ADDR r [VA_ARRAY_IDX 0])
}"*)

(*
definition "instr_free addr = doM {
  case addr of
      ADDR b [VA_ARRAY_IDX 0] \<Rightarrow> zoom (exec_state.memory\<^sub>L)\<^sub>S (block_free block_type.ON_HEAP b)
    | _ \<Rightarrow> fail MEM_ERROR
}"
*)

(*
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
*)

definition "instr_malloc ty n = zoom (exec_state.memory\<^sub>L)\<^sub>S (llb_malloc ty n)"
definition "instr_free addr = zoom (exec_state.memory\<^sub>L)\<^sub>S (llb_free addr)"
definition "instr_load addr = zoom (exec_state.memory\<^sub>L)\<^sub>S (llb_load addr)"
definition "instr_store v addr = zoom (exec_state.memory\<^sub>L)\<^sub>S (llb_store v addr)"


(*definition "instr_insert_a_value bv ev idx \<equiv> put_same_struct (array_item\<^sub>L idx) ev bv"
definition "instr_insert_s_value bv ev idx \<equiv> put_same_struct (struct_field\<^sub>L idx) ev bv"
definition "instr_extract_a_value bv idx \<equiv> mget (array_item\<^sub>L idx) bv"
definition "instr_extract_s_value bv idx \<equiv> mget (struct_field\<^sub>L idx) bv"
*)

(*
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
*)

definition "instr_arith2 ovf f ty op1 op2 = doM {
  x1 \<leftarrow> load_int ty op1;
  x2 \<leftarrow> load_int ty op2;
  fcheck (STATIC_ERROR ''arith2 incompatible widths'') (width x1 = width x2);
  fcheck (OVERFLOW_ERROR) (\<not>ovf x1 x2);
  return (Some (VINT (Inr (f x1 x2))))
}"

abbreviation "instr_arith2' \<equiv> instr_arith2 (\<lambda>_ _. False)"



definition "instr_arith_cmp f ty op1 op2 = doM {
  x1 \<leftarrow> load_int ty op1;
  x2 \<leftarrow> load_int ty op2;
  fcheck (STATIC_ERROR ''arith2cmp incompatible widths'') (width x1 = width x2);
  return (Some (VINT (Inr (bool_to_lint (f x1 x2)))))
}"


definition "instr_trunc ty op1 ty' = doM {
  x \<leftarrow> load_int ty op1;
  case ty' of
    TINT w \<Rightarrow> doM {
      fcheck (STATIC_ERROR ''Trunc must go to smaller type'') (width x > w);
      return (Some (VINT (Inr (trunc w x))))
    }
  | _ \<Rightarrow> fail (STATIC_ERROR ''Non-integer type as target for trunc'')
}"

definition "instr_ext f ty op1 ty' = doM {
  x \<leftarrow> load_int ty op1;
  case ty' of
    TINT w \<Rightarrow> doM {
      fcheck (STATIC_ERROR ''ext must go to greater type'') (width x < w);
      return (Some (VINT (Inr (f w x))))
    }
  | _ \<Rightarrow> fail (STATIC_ERROR ''Non-integer type as target for ext'')
}"

context
  fixes exec_proc_name :: "proc_name \<times> val list \<Rightarrow> (val option,unit,memory,err) M"
begin

  primrec exec_basic_instr_aux where
    "exec_basic_instr_aux (ADD ty op1 op2) = instr_arith2' (+) ty op1 op2"
  | "exec_basic_instr_aux (SUB ty op1 op2) = instr_arith2' (-) ty op1 op2"
  | "exec_basic_instr_aux (MUL ty op1 op2) = instr_arith2' ( * ) ty op1 op2"
  | "exec_basic_instr_aux (UDIV ty op1 op2) = instr_arith2' (div) ty op1 op2"
  | "exec_basic_instr_aux (UREM ty op1 op2) = instr_arith2' (mod) ty op1 op2"
  | "exec_basic_instr_aux (SDIV ty op1 op2) = instr_arith2 (sdivrem_ovf) (div\<^sub>s) ty op1 op2"
  | "exec_basic_instr_aux (SREM ty op1 op2) = instr_arith2 (sdivrem_ovf) (rem\<^sub>s) ty op1 op2"
  | "exec_basic_instr_aux (SHL ty op1 op2) = instr_arith2 (shift_ovf) bitSHL' ty op1 op2"
  | "exec_basic_instr_aux (LSHR ty op1 op2) = instr_arith2 (shift_ovf) bitLSHR' ty op1 op2"
  | "exec_basic_instr_aux (ASHR ty op1 op2) = instr_arith2 (shift_ovf) bitASHR' ty op1 op2"
  | "exec_basic_instr_aux (ICMP code ty op1 op2) = instr_arith_cmp (lint_icmp code) ty op1 op2"

  | "exec_basic_instr_aux (TRUNC_TO ty op1 ty') = instr_trunc ty op1 ty'"
  | "exec_basic_instr_aux (ZEXT_TO ty op1 ty') = instr_ext zext ty op1 ty'"
  | "exec_basic_instr_aux (SEXT_TO ty op1 ty') = instr_ext sext ty op1 ty'"

  | "exec_basic_instr_aux (basic_instr_aux.AND ty op1 op2) = instr_arith2' (AND) ty op1 op2"
  | "exec_basic_instr_aux (basic_instr_aux.OR ty op1 op2) = instr_arith2' (OR) ty op1 op2"
  | "exec_basic_instr_aux (basic_instr_aux.XOR ty op1 op2) = instr_arith2' (XOR) ty op1 op2"
  | "exec_basic_instr_aux (ALLOCA ty tyi opr) = doM {
      n \<leftarrow> load_int tyi opr;
      addr \<leftarrow> instr_alloca ty (lint_to_uint n);
      return (Some (VPTR (Some (Some addr))))
    }"
  | "exec_basic_instr_aux (MALLOC ty tyi opr) = doM {
      n \<leftarrow> load_int tyi opr;
      addr \<leftarrow> instr_malloc ty (lint_to_uint n);
      return (Some (VPTR (Some (Some addr))))
    }"
  | "exec_basic_instr_aux (FREE ty opr) = doM {
      addr \<leftarrow> load_addr ty opr;
      instr_free addr;
      return None
    }"
  | "exec_basic_instr_aux (LOAD ty typ opr) = doM {
      addr \<leftarrow> load_addr typ opr;
      r \<leftarrow> instr_load addr;
      return (Some r)
    }"
  | "exec_basic_instr_aux (STORE tyv oprv typ oprp) = doM {
      v \<leftarrow> load_opr tyv oprv;
      addr \<leftarrow> load_addr typ oprp;
      instr_store v addr;
      return None
    }"
  | "exec_basic_instr_aux (INSERT_A_VALUE bty bopr ety eopr idx) = doM {
      bv \<leftarrow> load_opr bty bopr;
      ev \<leftarrow> load_opr ety eopr;
      r \<leftarrow> ll_insert_a_value' bv ev idx;
      return (Some r)
    }"
  | "exec_basic_instr_aux (INSERT_S_VALUE bty bopr ety eopr idx) = doM {
      bv \<leftarrow> load_opr bty bopr;
      ev \<leftarrow> load_opr ety eopr;
      r \<leftarrow> ll_insert_s_value' bv ev idx;
      return (Some r)
    }"
  | "exec_basic_instr_aux (EXTRACT_A_VALUE bty bopr idx) = doM {
      bv \<leftarrow> load_opr bty bopr;
      r \<leftarrow> ll_extract_a_value' bv idx;
      return (Some r)
    }"
  | "exec_basic_instr_aux (EXTRACT_S_VALUE bty bopr idx) = doM {
      bv \<leftarrow> load_opr bty bopr;
      r \<leftarrow> ll_extract_s_value' bv idx;
      return (Some r)
    }"
  | "exec_basic_instr_aux (OFS_PTR bty bopr ity iopr) = doM {
      addr \<leftarrow> load_addr (TPTR bty) bopr;
      idx \<leftarrow> load_int ity iopr;
      r \<leftarrow> llb_ofs_addr addr (lint_to_sint idx);
      return (Some ((VPTR (Some (Some r)))))
    }"
  | "exec_basic_instr_aux (INDEX_A_PTR bty bopr ity iopr) = doM {
      addr \<leftarrow> load_addr (TPTR bty) bopr;
      idx \<leftarrow> load_int ity iopr;
      r \<leftarrow> llb_idx_array addr (lint_to_uint idx);
      return (Some ((VPTR (Some (Some r)))))
    }"
  | "exec_basic_instr_aux (INDEX_S_PTR bty bopr idx) = doM {
      addr \<leftarrow> load_addr (TPTR bty) bopr;
      r \<leftarrow> llb_idx_field addr idx;
      return (Some ((VPTR (Some (Some r)))))
    }"

  primrec exec_nt_instr_aux where
    "exec_nt_instr_aux (BASIC i) = exec_basic_instr_aux i"
  | "exec_nt_instr_aux (CALL ty name args) = doM {
      argvs \<leftarrow> mmap (uncurry load_opr) args;
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
  | "exec_t_instr (RETURN ty opr) = doM { v \<leftarrow> load_opr ty opr; raise (Some v) }"
  | "exec_t_instr (BR label) = return label"
  | "exec_t_instr (CBR ty opr lt lf) = doM {
      v \<leftarrow> load_bool ty opr;
      if v then return lt else return lf
  }"

  definition "exec_block \<equiv> \<lambda>BBLOCK ntis ti\<Rightarrow> doM {
    \<comment> \<open>Execute nonterminal instructions\<close>
    mfold' exec_nt_instr ntis;
    \<comment> \<open>Execute terminal instruction\<close>
    exec_t_instr ti
  }"

  term mmblock

  definition "exec_block_reset block \<equiv> doM {
    \<comment> \<open>Save local definitions\<close>
    saved_lvars \<leftarrow> use (exec_state.lvars\<^sub>L)\<^sub>S;

    mmblock (get) (\<lambda>s'. doM {set s'; (exec_state.lvars\<^sub>L)\<^sub>S := saved_lvars}) (exec_block block)
  }"

  definition "mk_fresh_exec_state mem \<equiv> EXEC_STATE Map.empty [] mem"

  definition "exec_proc \<equiv> \<lambda>PROC params prologue blocks rtype \<Rightarrow> \<lambda>args. doM {
    fcheck (STATIC_ERROR ''|arg| != |param|'') (length params = length args);
    mblock (mk_fresh_exec_state) (get' exec_state.memory\<^sub>L) (doM {
      \<comment> \<open>Define Parameters\<close>
      mfold' (uncurry define_lvar) (zip (map snd params) args);

      handle (doM {
        \<comment> \<open>Execute Prologue\<close>
        label \<leftarrow> exec_block prologue;

        \<comment> \<open>Execute Blocks\<close>
        let block_map = map_of blocks;
        mwhile (\<lambda>_. return True) (\<lambda>label. doM {
          \<comment> \<open>Lookup label\<close>
          block \<leftarrow> lookup (STATIC_ERROR ''undef label'') block_map label;
          exec_block_reset block
        }) label;

        fail (STATIC_ERROR ''unreachable'') \<comment> \<open>Unreachable\<close>
      }) (\<lambda>r. doM {
        \<comment> \<open>Free alloca-blocks\<close>
        lbs \<leftarrow> use (exec_state.local_blocks\<^sub>L)\<^sub>S;
        mfold' (\<lambda>b. zoom (exec_state.memory\<^sub>L)\<^sub>S (block_free block_type.ON_STACK b)) lbs;
        \<comment> \<open>Return result\<close>
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

definition "foo a b \<equiv> (a::lint) = b"


definition "test \<equiv> PROG [(PROC_NAME ''main'',PROC [] (
  BBLOCK [
    NT_INSTR (Some (LVAR_NAME ''p'')) (BASIC (MALLOC (TINT 32) (TINT 32) (OP_ICONST 5)))
    ,
    NT_INSTR (Some (LVAR_NAME ''p2'')) (BASIC (OFS_PTR (TINT 32) (OP_LVAR (LVAR_NAME ''p'')) (TINT 32) (OP_ICONST 2)))
    ,
    NT_INSTR None (BASIC (STORE (TINT 32) (OP_ICONST 42) (TPTR (TINT 32)) (OP_LVAR (LVAR_NAME ''p2''))))

  ] (RETURN (TPTR (TINT 32)) (OP_LVAR (LVAR_NAME ''p'')))
) [] (Some (TPTR (TINT 32))))]"

value "run (exec_proc_name test (PROC_NAME ''main'',[])) (MEM [])"


end

