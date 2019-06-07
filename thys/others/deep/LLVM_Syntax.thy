theory LLVM_Syntax 
  imports LLVM_Pre_Syntax
begin

subsection \<open>AST Definitions\<close>

  datatype label_name = LABEL_NAME (the_name: string)
  hide_const (open) the_name
  datatype proc_name = PROC_NAME (the_name: string)
  hide_const (open) the_name
  datatype lvar_name = LVAR_NAME (the_name: string)
  hide_const (open) the_name


  datatype operand = OP_ICONST int | OP_LVAR lvar_name

  datatype icmp_code = EQ | NE | SLE | SLT | ULE | ULT
  hide_const (open) EQ NE SLE SLT ULE ULT


  datatype basic_instr_aux =
    ADD type operand operand
  | SUB type operand operand
  | MUL type operand operand
  | UDIV type operand operand
  | UREM type operand operand
  | SDIV type operand operand
  | SREM type operand operand
  | AND type operand operand
  | OR type operand operand
  | XOR type operand operand
  | SHL type operand operand
  | ASHR type operand operand
  | LSHR type operand operand
  | TRUNC_TO type operand type
  | ZEXT_TO type operand type
  | SEXT_TO type operand type
  | ICMP icmp_code type operand operand
  | ALLOCA type type operand
  | MALLOC type type operand
  | LOAD type type operand
  | STORE type operand type operand
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
  | CBR type operand label_name label_name

  datatype basic_block = BBLOCK "nt_instr list" t_instr

  datatype procedure = PROC
    (params: "(type \<times> lvar_name) list")
    (prologue: basic_block)
    (blocks: "(label_name\<times>basic_block) list")
    (rtype: "type option")
  hide_const (open) params prologue blocks rtype

  datatype program = PROG (procedures: "(proc_name \<times> procedure) list")
  hide_const (open) procedures



end
