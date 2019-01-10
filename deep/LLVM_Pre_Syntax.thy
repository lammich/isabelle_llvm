theory LLVM_Pre_Syntax
imports Main
begin

  text \<open>LLVM Syntax which is shared between LLVM deep embedding and LLVM value model\<close>

  datatype (discs_sels) type =
    TINT nat | TPTR type | TARRAY nat type | TSTRUCT "type list"


end
