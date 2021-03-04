theory LLVM_Compiler
  imports 
    LLVM_Typecheck 
    "Show.Show_Instances" 
    "HOL-Library.RBT_Mapping" 
    "HOL-Library.List_Lexorder"
    "HOL-Library.Char_ord" 
    "HOL-Library.Code_Target_Nat" 
    "HOL-Library.Code_Target_Int" 
begin

derive "show" err


type_synonym cval = "type \<times> operand"

datatype bb_builder = BB_BUILDER 
  (name: label_name)
  (instrs: "nt_instr list")
hide_const (open) name instrs
define_lenses (open) bb_builder


datatype proc_builder = PROC_BUILDER
  (next_id: nat)
  (name: proc_name)
  (rtype: "type option")
  (params: "(type \<times> string) list")
  (lvars: "string list")
  (lvarmap: "(string,(type \<times> lvar_name)) mapping")
  (blocks: "(label_name \<times> basic_block) list")
  (current_bb: "bb_builder option")
hide_const (open) name rtype params lvars lvarmap blocks current_bb 
define_lenses (open) proc_builder


datatype prog_builder = PROG_BUILDER 
  (procs: "(proc_name \<times> procedure) list")
  (proc_map: "(string, type option) mapping")
  (current_proc: "proc_builder option")
hide_const (open) next_id procs current_proc
define_lenses (open) prog_builder

definition "the_current_proc\<^sub>L \<equiv> lift_lens ''No current proc'' (prog_builder.current_proc\<^sub>L \<bullet>\<^sub>L the\<^sub>L)"

abbreviation "params\<^sub>L \<equiv> the_current_proc\<^sub>L \<bullet> (proc_builder.params\<^sub>L)\<^sub>N"
abbreviation "lvars\<^sub>L \<equiv> the_current_proc\<^sub>L \<bullet> (proc_builder.lvars\<^sub>L)\<^sub>N"
abbreviation "lvarmap\<^sub>L \<equiv> the_current_proc\<^sub>L \<bullet> (proc_builder.lvarmap\<^sub>L)\<^sub>N"
abbreviation "blocks\<^sub>L \<equiv> the_current_proc\<^sub>L \<bullet> (proc_builder.blocks\<^sub>L)\<^sub>N"
definition "current_bb\<^sub>L \<equiv> the_current_proc\<^sub>L \<bullet> lift_lens ''No current basic block'' (proc_builder.current_bb\<^sub>L \<bullet>\<^sub>L the\<^sub>L)"


(*definition "zoom_proc \<equiv> zoom the_current_proc\<^sub>L"
definition "zoom_bb \<equiv> zoom (current_bb\<^sub>L)"
*)




definition "emit_instr i \<equiv> current_bb\<^sub>L \<bullet> (bb_builder.instrs\<^sub>L)\<^sub>N %= (\<lambda>is. is@[i])"
definition "is_open_bb (_::unit) \<equiv> doM { bb \<leftarrow> use (the_current_proc\<^sub>L \<bullet> (proc_builder.current_bb\<^sub>L)\<^sub>N); return (bb\<noteq>None) }"
definition "open_bb name \<equiv> doM {
  bbo\<leftarrow>is_open_bb (); fcheck ''Already open bb'' (\<not>bbo);
  the_current_proc\<^sub>L \<bullet> (proc_builder.current_bb\<^sub>L)\<^sub>N := Some (BB_BUILDER name [])
}"

definition "mk_bblock ti \<equiv> doM {
  instrs \<leftarrow> use (current_bb\<^sub>L \<bullet> (bb_builder.instrs\<^sub>L)\<^sub>N);
  return (BBLOCK instrs ti)
}"

definition "close_bb ti \<equiv> doM {
  name \<leftarrow> use (current_bb\<^sub>L \<bullet> (bb_builder.name\<^sub>L)\<^sub>N);
  bb \<leftarrow> mk_bblock ti;
  let nbb = (name,bb);
  blocks\<^sub>L %= (\<lambda>bs. bs@[nbb]);
  the_current_proc\<^sub>L \<bullet> (proc_builder.current_bb\<^sub>L)\<^sub>N := None
}"



definition "fresh_id (_::unit) \<equiv> doM {
  r \<leftarrow> use (the_current_proc\<^sub>L \<bullet> (proc_builder.next_id\<^sub>L)\<^sub>N);
  the_current_proc\<^sub>L \<bullet> (proc_builder.next_id\<^sub>L)\<^sub>N := Suc r;
  return r
}"

definition "fresh_lvar x \<equiv> doM {
  i\<leftarrow>fresh_id ();
  return (LVAR_NAME ((x +#+ ''_'' +#+ shows i) ''''))
}"

definition "fresh_label x \<equiv> doM {
  i\<leftarrow>fresh_id ();
  return (LABEL_NAME ((x +#+ ''_'' +#+ shows i) ''''))
}"


definition "bind_emit_instr ty i \<equiv> doM {
  rv \<leftarrow> fresh_lvar ''tmp'';
  emit_instr (NT_INSTR (Some rv) i);
  return (ty, OP_LVAR rv)
}"

definition "init_lvarmap (_::unit) \<equiv> doM {
  params \<leftarrow> use params\<^sub>L;
  mfold' (\<lambda>(ty,name). doM { 
    lv\<leftarrow>fresh_lvar name; 
    lvarmap\<^sub>L %= Mapping.update name (ty,lv) 
  }) params
}"

definition define_lvar where "define_lvar ty name \<equiv> doM {
  lvm \<leftarrow> use lvarmap\<^sub>L;
  fcheck ''Dup lvar'' (Mapping.lookup lvm name = None);
  lv \<leftarrow> fresh_lvar name;
  lvars\<^sub>L %= (#) name;
  lvarmap\<^sub>L %= Mapping.update name (ty,lv)
}"

definition "proc_entry_label \<equiv> LABEL_NAME ''__proc_entry''"

definition "open_proc rtype name params \<equiv> doM {
  cp \<leftarrow> use (prog_builder.current_proc\<^sub>L)\<^sub>N; fcheck ''Already open proc'' (cp=None);
  (prog_builder.current_proc\<^sub>L)\<^sub>N := Some (PROC_BUILDER 0 (PROC_NAME name) rtype params [] Mapping.empty [] None);

  (prog_builder.proc_map\<^sub>L)\<^sub>N %= Mapping.update name rtype;

  init_lvarmap ();
  open_bb proc_entry_label
}"

definition lookup_lvar where
  "lookup_lvar x \<equiv> doM {
    lvm \<leftarrow> use lvarmap\<^sub>L;
    lookup ''Undefined lvar'' (Mapping.lookup lvm) x
  }"


definition "build_prologue (_::unit) \<equiv> doM {
  open_bb (LABEL_NAME '''');

  \<comment> \<open>alloca parameters\<close>
  params \<leftarrow> use params\<^sub>L;
  mfold' (\<lambda>(ty,name). doM {
    (ty,v) \<leftarrow> lookup_lvar name;
    emit_instr (NT_INSTR (Some v) (BASIC (ALLOCA ty (TINT 32) (OP_ICONST 1))));
    emit_instr (NT_INSTR None (BASIC (STORE ty (OP_LVAR (LVAR_NAME name)) (TPTR ty) (OP_LVAR v))))
  }) params;

  \<comment> \<open>alloca local variables\<close>
  lvars \<leftarrow> use lvars\<^sub>L;
  mfold' (\<lambda>name. doM {
    (ty,v) \<leftarrow> lookup_lvar name;
    emit_instr (NT_INSTR (Some v) (BASIC (ALLOCA ty (TINT 32) (OP_ICONST 1))))
  }) lvars;

  prologue \<leftarrow> mk_bblock (BR proc_entry_label);
  the_current_proc\<^sub>L \<bullet> (proc_builder.current_bb\<^sub>L)\<^sub>N := None;

  return prologue
}"


definition "close_proc (_::unit) \<equiv> doM {
  cbo \<leftarrow> is_open_bb (); fcheck ''Close-Proc: Open bb'' (\<not>cbo);
  prologue \<leftarrow> build_prologue ();
  name \<leftarrow> use (the_current_proc\<^sub>L \<bullet> (proc_builder.name\<^sub>L)\<^sub>N);
  blocks \<leftarrow> use (the_current_proc\<^sub>L \<bullet> (proc_builder.blocks\<^sub>L)\<^sub>N);
  params \<leftarrow> use (the_current_proc\<^sub>L \<bullet> (proc_builder.params\<^sub>L)\<^sub>N);
  let params = map (apsnd LVAR_NAME) params;
  rtype \<leftarrow> use (the_current_proc\<^sub>L \<bullet> (proc_builder.rtype\<^sub>L)\<^sub>N);
  
  let nxproc = (name,PROC params prologue blocks rtype);
  (prog_builder.procs\<^sub>L)\<^sub>N %= (\<lambda>ps. nxproc # ps);

  (prog_builder.current_proc\<^sub>L)\<^sub>N := None
}"

definition "build_prog (_::unit) \<equiv> doM {
  cp \<leftarrow> use (prog_builder.current_proc\<^sub>L)\<^sub>N; fcheck ''Still open proc'' (cp=None);
  procs \<leftarrow> use (prog_builder.procs\<^sub>L)\<^sub>N;
  return (PROG procs) 
}"

definition "init_progb \<equiv> PROG_BUILDER [] Mapping.empty None"

type_synonym pM = "(unit, unit, prog_builder, char list) M"
type_synonym cmd = "(unit, unit, prog_builder, char list) M"
type_synonym expr = "(type\<times>operand, unit, prog_builder, char list) M"


definition "close_bb_if_open ti \<equiv> doM {
  cbb \<leftarrow> is_open_bb ();
  if cbb then doM {close_bb ti; return True} else return False
}"

definition p_proc :: "type option \<Rightarrow> string \<Rightarrow> (type\<times>string) list \<Rightarrow> cmd \<Rightarrow> pM"
  where "p_proc rtype name args body \<equiv> doM {
    open_proc rtype name args;
    body; 

    cbo \<leftarrow> is_open_bb ();
    (if rtype=None then doM {
      close_bb_if_open RETURN_VOID;
      return ()
    } else
      fcheck ''No return statement at end of non-void procedure'' (\<not>cbo));

    close_proc ()
  }"

definition c_scomp :: "cmd \<Rightarrow> cmd \<Rightarrow> cmd" (infixr ";;" 40) where "c_scomp c1 c2 \<equiv> doM {c1; c2}"

definition "l_var name \<equiv> doM {
  (ty,lv) \<leftarrow> lookup_lvar name;
  return (TPTR ty,OP_LVAR lv)
}"

definition "check_itype' msg ty \<equiv> case ty of TINT _ \<Rightarrow> return () | _ \<Rightarrow> fail msg"

abbreviation "check_itype \<equiv> check_itype' ''Expected integer type''"

fun the_ptrty where "the_ptrty msg (TPTR ty) = return ty" | "the_ptrty msg _ = fail msg"

definition "e_ofsptr ptr_exp ofs_exp \<equiv> doM {
  (ty,pv) \<leftarrow> ptr_exp;
  (ty',ov) \<leftarrow> ofs_exp;
  check_itype' ''Offset must be integer'' ty';
  case ty of
    TPTR ety \<Rightarrow> bind_emit_instr ty (BASIC (OFS_PTR ety pv ty' ov))
  | _ \<Rightarrow> fail ''ofsptr expects pointer type''
}"

definition "e_idxa ptr_exp idx_exp \<equiv> doM {
  (ty,pv) \<leftarrow> ptr_exp;
  (ty',ov) \<leftarrow> idx_exp;
  check_itype' ''Offset must be integer'' ty';
  case ty of
    TPTR (TARRAY _ ety) \<Rightarrow> bind_emit_instr (TPTR ety) (BASIC (INDEX_A_PTR ety pv ty' ov))
  | _ \<Rightarrow> fail ''idxa expects pointer to array type''
}"

definition "e_idxs ptr_exp fi \<equiv> doM {
  (ty,pv) \<leftarrow> ptr_exp;
  case ty of
    TPTR (TSTRUCT tys) \<Rightarrow> doM {
      fcheck ''sidx out of range'' (fi<length tys);
      let ety = tys!fi;
      bind_emit_instr (TPTR ety) (BASIC (INDEX_S_PTR ety pv fi))
    }
  | _ \<Rightarrow> fail ''idxs expects pointer to structure type''
}"

definition "e_deref ptr_exp \<equiv> doM {
  (ty,lv) \<leftarrow> ptr_exp;
  case ty of
    TPTR ety \<Rightarrow> bind_emit_instr ety (BASIC (LOAD ety ty lv))
  | _ \<Rightarrow> fail ''e_deref expects pointer type''
}"

definition "e_malloc ty exp \<equiv> doM {
  (ity,lv) \<leftarrow> exp;
  check_itype ity;
  bind_emit_instr (TPTR ty) (BASIC (MALLOC ty ity lv))
}"

definition "c_free exp \<equiv> doM {
  (ty,lv) \<leftarrow> exp;
  fcheck ''Free expects pointer type'' (is_TPTR ty);
  emit_instr (NT_INSTR None (BASIC (FREE ty lv)))
}"


definition "e_var \<equiv> e_deref o l_var"

definition "c_assign lexp expr \<equiv> doM {
  (ty,lv) \<leftarrow> lexp;
  (tyv,v) \<leftarrow> expr;
  case ty of
    TPTR ety \<Rightarrow> doM {
      fcheck ''c_assign type mismatch'' (ety=tyv);
      emit_instr (NT_INSTR None (BASIC (STORE tyv v ty lv)))
    }
  | _ \<Rightarrow> fail ''c_assign expects pointer type on LHS''
}"

definition "c_return expr \<equiv> doM {
  (tyv,v) \<leftarrow> expr;
  close_bb (RETURN tyv v)
}"

definition "c_if b t e \<equiv> doM {
  (tyb,v) \<leftarrow> b;
  fcheck ''Expected Boolean on if'' (tyb = TINT 1);
  l_then \<leftarrow> fresh_label ''if_then'';
  l_else \<leftarrow> fresh_label ''if_else'';
  l_end \<leftarrow> fresh_label ''if_end'';

  close_bb (CBR tyb v l_then l_else);

  open_bb l_then; t; o1\<leftarrow>close_bb_if_open (BR l_end);
  open_bb l_else; e; o2\<leftarrow>close_bb_if_open (BR l_end);

  if o1 \<or> o2 then
    open_bb l_end
  else 
    return ()

}"

(*
  \<dots> br l_while_test
  l_while_test:
    b_exp
    br \<dots> l_while_body l_while_exit

  l_while_body:
    cmd
    br l_while_test

  l_while_exit:
    \<dots>

*)

definition "c_while b_exp cmd \<equiv> doM {
  l_while_test \<leftarrow> fresh_label ''while_test'';
  l_while_body \<leftarrow> fresh_label ''while_body'';
  l_while_exit \<leftarrow> fresh_label ''while_exit'';

  close_bb (BR l_while_test);

  open_bb l_while_test;
  (tyb,bv) \<leftarrow> b_exp;
  fcheck ''Expected Boolean on while'' (tyb = TINT 1);
  close_bb (CBR tyb bv l_while_body l_while_exit);

  open_bb l_while_body;
  cmd;
  close_bb (BR l_while_test);

  open_bb l_while_exit
}"




definition e_const where 
  "e_const w i \<equiv> return (TINT w, OP_ICONST i)"


definition e_binop where
  "e_binop op a b \<equiv> doM {
    (tya,va)\<leftarrow>a;
    (tyb,vb)\<leftarrow>b;
    fcheck ''Incompatible operand type'' (tya = tyb);
    bind_emit_instr tya (BASIC (op tya va vb))
  }"

definition e_cmpop where
  "e_cmpop cc a b \<equiv> doM {
    (tya,va)\<leftarrow>a;
    (tyb,vb)\<leftarrow>b;
    fcheck ''Incompatible operand type'' (tya = tyb);
    bind_emit_instr (TINT 1) (BASIC (ICMP cc tya va vb))
  }"

abbreviation "e_add \<equiv> e_binop ADD"
abbreviation "e_sub \<equiv> e_binop SUB"
abbreviation "e_mul \<equiv> e_binop MUL"
abbreviation "e_udiv \<equiv> e_binop UDIV"
abbreviation "e_urem \<equiv> e_binop UREM"
abbreviation "e_sdiv \<equiv> e_binop SDIV"
abbreviation "e_srem \<equiv> e_binop SREM"

abbreviation "e_and \<equiv> e_binop basic_instr_aux.AND"
abbreviation "e_or \<equiv> e_binop basic_instr_aux.OR"
abbreviation "e_xor \<equiv> e_binop basic_instr_aux.XOR"

abbreviation "e_shl \<equiv> e_binop SHL"
abbreviation "e_ashr \<equiv> e_binop ASHR"
abbreviation "e_lshr \<equiv> e_binop LSHR"

definition "e_ucast w' a \<equiv> doM {
  (ty,v) \<leftarrow> a;
  case ty of 
    (TINT w) \<Rightarrow> 
      if w'<w then
        bind_emit_instr (TINT w') (BASIC (TRUNC_TO ty v (TINT w')))
      else if w'>w then
        bind_emit_instr (TINT w') (BASIC (ZEXT_TO ty v (TINT w')))
      else return (ty,v)
  | _ \<Rightarrow> fail ''ucast: no integer type''
}"

definition "e_scast w' a \<equiv> doM {
  (ty,v) \<leftarrow> a;
  case ty of 
    (TINT w) \<Rightarrow> 
      if w'<w then
        bind_emit_instr (TINT w') (BASIC (TRUNC_TO ty v (TINT w')))
      else if w'>w then
        bind_emit_instr (TINT w') (BASIC (SEXT_TO ty v (TINT w')))
      else return (ty,v)
  | _ \<Rightarrow> fail ''scast: no integer type''
}"

definition "e_call n args \<equiv> doM {
  args \<leftarrow> mmap (\<lambda>s. doM {s}) args;
  procmap \<leftarrow> use (prog_builder.proc_map\<^sub>L)\<^sub>N;
  rt \<leftarrow> lookup ''No such procedure'' (Mapping.lookup procmap) n;
  rt \<leftarrow> case rt of None \<Rightarrow> fail ''void procedure'' | Some  rt \<Rightarrow> return rt;
  
  bind_emit_instr rt ((CALL rt (PROC_NAME n) args))
}"

term "run (p_proc None ''main'' [] (c_assign (l_var ''x'') (e_const 32 42))) init_progb"


fun the_res where
  "the_res (SUCC r _) = r"

definition "mrun m s \<equiv> mwp (run m s) internal_nterm (fail o show) (\<lambda>_ _. fail ''EXC'') (\<lambda>r s. return (r,s))"

definition "ctr p args \<equiv> doM {
  (\<pi>,_) \<leftarrow> mrun (doM {p; build_prog ()}) init_progb;
  mfail (\<lambda>s. s '''') (tyco_program \<pi>);
  (r,s) \<leftarrow> mrun (exec_proc_name \<pi> (PROC_NAME ''main'',args)) (MEM []);
  return (r,s)
}"

definition pr :: "_ \<Rightarrow> (_,unit,unit,_) M" where "pr p \<equiv> doM {
  (\<pi>,_) \<leftarrow> mrun (doM {p; build_prog ()}) init_progb;
  return (string_of \<pi>)
}"

term mblock

definition "testprog \<equiv> p_proc (None) ''main'' [(TINT 32,''p'')] (
  define_lvar (TPTR (TINT 1)) ''x'';;
  c_assign (l_var ''x'') (e_malloc (TINT 1) (e_const 32 10)) ;;
  c_assign (e_ofsptr (e_var ''x'') (e_const 32 0)) (e_const 1 1)
)"

definition "testprog2 \<equiv> p_proc (Some (TINT 32)) ''main'' [(TINT 32,''argc''),(TPTR (TPTR ((TINT 8))),''args'')] (
  c_if (e_cmpop icmp_code.EQ (e_var ''argc'') (e_const 32 0)) 
    (c_return (e_const 32 1))
    (
      define_lvar (TPTR (TINT 1)) ''x'';;
      define_lvar (TPTR (TINT 1)) ''y'';;
      c_assign (l_var ''x'') (e_malloc (TINT 1) (e_var ''argc'')) ;;
      c_assign (l_var ''y'') (e_ofsptr (e_var ''x'') (e_sub (e_var ''argc'') (e_const 32 1)));;
      c_assign (e_var ''y'') (e_const 1 1) ;;
      c_if (e_cmpop icmp_code.EQ (e_deref (e_var ''y'')) (e_const 1 1))
        (c_return (e_const 32 0))
        (c_return (e_const 32 2))
    )
)"

definition "testprog3 \<equiv> doM {
  p_proc (Some (TINT 32)) ''strlen'' [(TPTR (TINT 8), ''s'')] (
    define_lvar (TINT 32) ''c'';;
    c_assign (l_var ''c'') (e_const 32 0);;
    c_while (e_cmpop icmp_code.NE (e_deref (e_var ''s'')) (e_const 8 0)) (
      c_assign (l_var ''s'') (e_ofsptr (e_var ''s'') (e_const 32 1));;
      c_assign (l_var ''c'') (e_add (e_var ''c'') (e_const 32 1))
    );;
    c_return (e_var ''c'')
  );

  p_proc (Some (TINT 32)) ''main'' [(TINT 32,''argc''),(TPTR (TPTR ((TINT 8))),''args'')] (  
    c_if (e_cmpop icmp_code.ULE (e_var ''argc'') (e_const 32 1))
    (c_return (e_const 32 0))
    (c_return (e_call ''strlen'' [e_deref (e_ofsptr (e_var ''args'') (e_const 32 1))]))
  )
}"



ML \<open>
  fun eval_pretty ctxt t = let 
    val t = Value_Command.value ctxt t
  in 
    case t of
      @{mpat "SUCC ?prog _"} => HOLogic.dest_string prog |> writeln
    | _ => Syntax.pretty_term ctxt t |> Pretty.writeln
  end
\<close>

ML_val \<open>eval_pretty @{context} @{term \<open>run (pr testprog3) ()\<close>}\<close>


value "run (ctr (testprog3) [VINT (Inr (lconst 32 1)), VPTR (Some None)]) ()"


  oops
xxx, ctd here:
  Generate malloc-stubs and free-stubs
  test with some useful programs


(*
export_code testprog in SML module_name Test file "Test.sml"

ML_file "Test.sml"

ML \<open>Test.testprog\<close>
*)

value "testprog"




datatype ('s) SM = Computation (run: "'s \<Rightarrow> 's")

definition "foo5 \<equiv> Computation id"

export_code foo5 in SML

value "run foo5 (Suc 1)"

definition "foo3 = []"
definition "foo4 = foo3"
export_code foo4 in SML



type_synonym 'a eM = "('a,unit,prog_builder,unit) M"

find_consts "nat \<Rightarrow> string"

value "(''var_'' +#+ shows (42::nat)) ''''"

definition fresh_num :: "_ eM" where "fresh_num \<equiv> doM {
  zoom (lift_lens () next_id\<^sub>L) (doM {
    n \<leftarrow> get;
    set (Suc n);
    return n
  })
}"

definition emit_instr :: "nt_instr \<Rightarrow> _ eM" where "emit_instr i \<equiv> doM {
  lift_lens () instrs\<^sub>L %= (\<lambda>is. is@[i])
}"


definition "uniq_variant s \<equiv> doM {
  n\<leftarrow>fresh_num;
  return ((s +#+ ''_'' +#+ shows n) '''')
}"

definition emit_instr_dr :: "type \<Rightarrow> nt_instr_aux \<Rightarrow> _ eM" where "emit_instr_dr ty i \<equiv> doM {
  v \<leftarrow> uniq_variant ''tmp'';
  let v = LVAR_NAME v;
  emit_instr (NT_INSTR (Some v) i);
  return (ty,OP_LVAR v)
}"

definition emit_instr_void :: "nt_instr_aux \<Rightarrow> unit eM" where "emit_instr_void i \<equiv> doM {
  emit_instr (NT_INSTR None i)
}"


type_synonym expr = "cval eM"
type_synonym cmd = "unit eM"

definition e_const :: "nat \<Rightarrow> int \<Rightarrow> expr" where 
  "e_const w i \<equiv> return (TINT w, OP_ICONST i)"

definition lookup_lvar :: "string \<Rightarrow> _ eM" where
  "lookup_lvar x \<equiv> doM {
    lvm \<leftarrow> use (lift_lens () lvarmap\<^sub>L);
    lookup () (Mapping.lookup lvm) x
  }"

definition e_var :: "string \<Rightarrow> expr" where
  "e_var x \<equiv> doM {
    (ty,lv) \<leftarrow> lookup_lvar x;
    emit_instr_dr ty (BASIC (LOAD ty (TPTR ty) (OP_LVAR lv)))
  }"

definition e_add :: "expr \<Rightarrow> expr \<Rightarrow> expr" where
  "e_add a b \<equiv> doM {
    (tya,va)\<leftarrow>a;
    (tyb,vb)\<leftarrow>b;
    emit_instr_dr tya (BASIC (ADD tya va vb))
  }"

definition c_assign :: "string \<Rightarrow> expr \<Rightarrow> cmd" where
  "c_assign x e \<equiv> doM {
    (tyl,lv) \<leftarrow> lookup_lvar x;
    (ty,v) \<leftarrow> e;
    emit_instr_void ((BASIC (STORE ty v (TPTR tyl) (OP_LVAR lv))))
  }"



value "run (c_assign ''x'' (e_add (e_const 32 4) (e_add (e_const 32 1) (e_var ''x'')))) 
  (ESTATE 0 [] (Mapping.of_alist [(''x'',(TINT 32, LVAR_NAME ''var_x''))]))"

find_consts "_ list \<Rightarrow> (_,_) mapping"


oops

xxx, ctd here:
  fresh-monad to produce llvm code
  pretty-printer to actual llvm
  instantiate floyd verification, separation logic



end
