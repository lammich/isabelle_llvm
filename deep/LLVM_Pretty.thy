theory LLVM_Pretty
  imports 
    LLVM_Syntax "../lib/Monad"
    "Show.Show_Instances" 
begin

definition llvm_target_size_w :: nat where 
  "llvm_target_size_w = 64" \<comment> \<open>Width of \<open>size_t\<close> type\<close>
definition llvm_target_datalayout :: string where 
  "llvm_target_datalayout = ''e-m:e-i64:64-f80:128-n8:16:32:64-S128''" \<comment> \<open>LLVM data layout specification\<close>
definition llvm_target_triple :: string where 
  "llvm_target_triple = ''x86_64-pc-linux-gnu''" \<comment> \<open>LLVM target triple specification\<close>

definition llvm_target_size_t :: type where "llvm_target_size_t = TINT llvm_target_size_w"


(*
  Generation of stubs for custom malloc and free functions
*)

abbreviation lift_lens_ne ("'(_')\<^sub>N") where "lift_lens_ne l \<equiv> lift_lens '''' l"


datatype pretty_s = PRETTY_S 
  (out: "shows")
  (malloc_stubs: "(nat\<times>type\<times>type) list")
  (free_stubs: "(nat\<times>type) list")
hide_const (open) out malloc_stubs free_stubs
define_lenses (open) pretty_s

type_synonym 'a pM = "('a,unit,pretty_s,string) M"

definition "extract" :: "shows pM" where "extract \<equiv> doM {
  use (pretty_s.out\<^sub>L)\<^sub>N
}"

consts out :: "'a \<Rightarrow> (unit,unit,pretty_s,string) M"
abbreviation out_append (infixl "<<" 52) where "a<<b \<equiv> doM {out a; out b}"          
abbreviation out_append_space (infixl "<<." 52) where "a<<.b \<equiv> doM {out a; out '' ''; out b}"          
abbreviation out_append_comma (infixl "<<," 52) where "a<<,b \<equiv> doM {out a; out '', ''; out b}"          

definition shows_of_pM :: "unit pM \<Rightarrow> shows" 
  where "shows_of_pM m \<equiv> mwp (run (doM {m; extract}) (PRETTY_S id [] [])) 
    (shows ''<Pretty-printing error: nterm?>'')
    (\<lambda>e. shows ''<Pretty-printing error: '' o shows e o shows ''>'')
    (\<lambda>_ _. shows ''<Pretty-printing error: exception?>'')
    (\<lambda>s _. s)"


definition string_of_pM :: "unit pM \<Rightarrow> string" 
  where "string_of_pM m \<equiv> shows_of_pM m ''''"

abbreviation "shows_of s \<equiv> shows_of_pM (out s)"
abbreviation "string_of s \<equiv> string_of_pM (out s)"

fun sep_aux where
  "sep_aux sep f [] = return ()"
| "sep_aux sep f [x] = f x"
| "sep_aux sep f (x#xs) = doM {f x; sep; sep_aux sep f xs}"

abbreviation "sep s xs \<equiv> sep_aux (out s) out xs"
abbreviation "sep' f s xs \<equiv> sep_aux (out s) f xs"

definition "list_aux e l s r f xs \<equiv> if xs=[] then e else doM {l; sep_aux s f xs; r}"

lemma sep_aux_cong [fundef_cong]:
  assumes "xs = ys" and "\<And>x. x \<in> list.set ys \<Longrightarrow> f x = g x"
  shows "sep_aux s f xs = sep_aux s g ys"
using assms
proof (induct ys arbitrary: xs)
  case (Cons y ys)
  then show ?case by (cases ys) simp_all
qed simp

lemma list_aux_cong [fundef_cong]:
  assumes "xs = ys" and "\<And>x. x \<in> list.set ys \<Longrightarrow> f x = g x"
  shows "list_aux e l s r f xs = list_aux e l s r g ys"
  using sep_aux_cong [of xs ys f g s] assms
  by (auto simp: list_aux_def) 



abbreviation "list e l s r xs \<equiv> list_aux (out e) (out l) (out s) (out r) out xs"
abbreviation "list' xsout e l s r xs \<equiv> list_aux (out e) (out l) (out s) (out r) xsout xs"


definition out_id :: "(unit, 'a, pretty_s, 'b list) M \<Rightarrow> _" where "out_id \<equiv> id"
definition "out_shows s \<equiv> (pretty_s.out\<^sub>L)\<^sub>N %= (\<lambda>x. x o s)"
definition "out_shows_cls \<equiv> out_shows o shows"

adhoc_overloading out out_id out_shows out_shows_cls




definition "out_proc_name s \<equiv> ''@'' << proc_name.the_name s"
definition "out_label_name s \<equiv> out (label_name.the_name s)"
definition "out_lvar_name s \<equiv> ''%'' << lvar_name.the_name s"

fun out_type where
  "out_type (TINT w)      = ''i'' << w"
| "out_type (TPTR ty)     = out_type ty << ''*''"
| "out_type (TARRAY n ty) = ''['' << n << '' x '' << out_type ty << '']''"
| "out_type (TSTRUCT tys) = list' out_type ''{}'' ''{'' '', '' ''}'' tys"

adhoc_overloading out out_proc_name out_label_name out_lvar_name out_type      

fun out_type_option where
  "out_type_option None = out ''void''"
| "out_type_option (Some ty) = out_type ty"

fun out_operand where
  "out_operand (OP_ICONST i) = out i"
| "out_operand (OP_LVAR name) = out name"

primrec out_cmp_code where
  "out_cmp_code icmp_code.EQ = out ''eq''"
| "out_cmp_code icmp_code.NE = out ''ne''"
| "out_cmp_code icmp_code.SLE = out ''sle''"
| "out_cmp_code icmp_code.SLT = out ''slt''"
| "out_cmp_code icmp_code.ULE = out ''ule''"
| "out_cmp_code icmp_code.ULT = out ''ult''"

adhoc_overloading out out_type_option out_operand out_cmp_code       

definition out_malloc_instr :: "type \<Rightarrow> type \<Rightarrow> operand \<Rightarrow> _" where 
  "out_malloc_instr ty1 ty2 b \<equiv> doM {
    ms \<leftarrow> use (pretty_s.malloc_stubs\<^sub>L)\<^sub>N;
    let sid = length ms;
    (pretty_s.malloc_stubs\<^sub>L)\<^sub>N := ms@[(sid,ty1,ty2)];
    
    ''call'' <<. TPTR ty1 <<. ''@_malloc_stub_'' << sid << ''('' << ty2 <<. b << '')''
  }"

definition out_free_instr :: "type \<Rightarrow> operand \<Rightarrow> _" where 
  "out_free_instr ty a \<equiv> doM {
    fs \<leftarrow> use (pretty_s.free_stubs\<^sub>L)\<^sub>N;
    let sid = length fs;
    (pretty_s.free_stubs\<^sub>L)\<^sub>N := fs@[(sid,ty)];
    
    ''call'' <<. ''void'' <<. ''@_free_stub_'' << sid << ''('' << ty <<. a << '')''
  }"

primrec out_basic_instr_aux where
  "out_basic_instr_aux (ADD ty a b) =  ''add''  <<. ty <<. a <<, b"
| "out_basic_instr_aux (SUB ty a b) =  ''sub''  <<. ty <<. a <<, b"
| "out_basic_instr_aux (MUL ty a b) =  ''mul''  <<. ty <<. a <<, b"
| "out_basic_instr_aux (UDIV ty a b) = ''udiv'' <<. ty <<. a <<, b"
| "out_basic_instr_aux (UREM ty a b) = ''urem'' <<. ty <<. a <<, b"
| "out_basic_instr_aux (SDIV ty a b) = ''sdiv'' <<. ty <<. a <<, b"
| "out_basic_instr_aux (SREM ty a b) = ''srem'' <<. ty <<. a <<, b"
| "out_basic_instr_aux (basic_instr_aux.AND ty a b) = ''and'' <<. ty <<. a <<, b"
| "out_basic_instr_aux (basic_instr_aux.OR ty a b) =  ''or''  <<. ty <<. a <<, b"
| "out_basic_instr_aux (basic_instr_aux.XOR ty a b) = ''xor'' <<. ty <<. a <<, b"
| "out_basic_instr_aux (SHL ty a b) =  ''shl''  <<. ty <<. a <<, b"
| "out_basic_instr_aux (ASHR ty a b) = ''ashr'' <<. ty <<. a <<, b"
| "out_basic_instr_aux (LSHR ty a b) = ''lshr'' <<. ty <<. a <<, b"

| "out_basic_instr_aux (TRUNC_TO ty a ty') = (''trunc'' <<. ty <<. a <<. ''to'' <<. ty')"
| "out_basic_instr_aux (ZEXT_TO ty a ty') = (''zext'' <<. ty <<. a <<. ''to'' <<. ty')"
| "out_basic_instr_aux (SEXT_TO ty a ty') = (''sext'' <<. ty <<. a <<. ''to'' <<. ty')"

| "out_basic_instr_aux (ICMP c ty a b) = (''icmp'' <<. c <<. ty <<. a <<, b)"

| "out_basic_instr_aux (ALLOCA ty1 ty2 b) = (''alloca'' <<. ty1 <<, ty2 <<. b)"
| "out_basic_instr_aux (MALLOC ty1 ty2 b) = out_malloc_instr ty1 ty2 b"
| "out_basic_instr_aux (FREE ty a) = out_free_instr ty a"
| "out_basic_instr_aux (LOAD ty1 ty2 b) = (''load'' <<. ty1 <<, ty2 <<. b)"
| "out_basic_instr_aux (STORE ty1 a ty2 b) = (''store'' <<. ty1 <<. a <<, ty2 <<. b)"
  
| "out_basic_instr_aux (INSERT_A_VALUE ty1 a ty2 b idx) = (''insertvalue'' <<. ty1 <<. a <<, ty2 <<. b <<, idx)"
| "out_basic_instr_aux (INSERT_S_VALUE ty1 a ty2 b idx) = (''insertvalue'' <<. ty1 <<. a <<, ty2 <<. b <<, idx)"
| "out_basic_instr_aux (EXTRACT_A_VALUE ty1 a idx) = (''extractvalue'' <<. ty1 <<. a <<, idx)"
| "out_basic_instr_aux (EXTRACT_S_VALUE ty1 a idx) = (''extractvalue'' <<. ty1 <<. a <<, idx)"
| "out_basic_instr_aux (OFS_PTR ty1 a ty2 b) = (
    ''getelementptr'' <<. ty1 <<, TPTR ty1 <<. a <<, ty2 <<. b <<. ''; was ofs_ptr'' <<. ty1 <<. a <<, ty2 <<. b
  )"
| "out_basic_instr_aux (INDEX_A_PTR ty1 a ty2 b) = (
    ''getelementptr'' <<. ty1 <<, TPTR ty1 <<. a <<, ''i32 0'' <<, ty2 <<. b <<. '' ; was index_a_ptr'' <<. ty1 <<. a <<, ty2 <<. b
  )"
| "out_basic_instr_aux (INDEX_S_PTR ty1 a idx) = (
    ''getelementptr'' <<. ty1 <<, TPTR ty1 <<. a <<, ''i32 0, i32'' <<. idx <<. '' ; was index_a_ptr'' <<. ty1 <<. a <<, idx
  )"

adhoc_overloading out out_basic_instr_aux

primrec out_nt_instr_aux where
  "out_nt_instr_aux (BASIC i) = out i"
| "out_nt_instr_aux (CALL ty p args) = ''call'' <<. ty <<. p << list' (case_prod (<<.)) ''()'' ''('' '','' '')'' args"

adhoc_overloading out out_nt_instr_aux

fun out_nt_instr where 
  "out_nt_instr (NT_INSTR None i) = out i"
| "out_nt_instr (NT_INSTR (Some lv) i) = lv <<. ''='' <<. i"

adhoc_overloading out out_nt_instr

primrec out_t_instr where
  "out_t_instr (RETURN ty a) = ''ret '' <<. ty <<. a"
| "out_t_instr (RETURN_VOID) = out ''ret void''"
| "out_t_instr (BR l) = ''br label'' <<. ''%''<< l"
| "out_t_instr (CBR ty a l1 l2) = ''br'' <<. ty <<. a <<, ''label'' <<. ''%''<< l1 <<, ''label'' <<. ''%''<< l2"

adhoc_overloading out out_t_instr

primrec out_basic_block where
  "out_basic_block (BBLOCK ntis ti) = list ''  '' ''  '' ''\<newline>  '' ''\<newline>  '' ntis << ti << ''\<newline>''"

adhoc_overloading out out_basic_block

primrec out_nbb :: "label_name \<times> basic_block \<Rightarrow> _" where
  "out_nbb (name,bb) = name << '':\<newline>'' << bb"

definition out_params :: "(type \<times> lvar_name) list \<Rightarrow> _" 
    where "out_params \<equiv> list' (case_prod (<<.)) ''()'' ''('' '','' '')''"

fun out_named_procedure :: "proc_name \<times> procedure \<Rightarrow> _" where
  "out_named_procedure (name, PROC params bb1 bbs rt) = (
    ''define'' <<. rt <<. name << out_params params <<. ''{\<newline>''
  << bb1 << ''\<newline>''
  << sep' out_nbb ''\<newline>'' bbs << ''\<newline>''
  << ''}\<newline>''
    )"

fun out_malloc_stub :: "nat \<times> type \<times> type \<Rightarrow> _" where
  "out_malloc_stub (sid,obj_t,sarg_t) = doM {
    sarg_w \<leftarrow> case sarg_t of TINT w \<Rightarrow> return w |  _ \<Rightarrow> fail ''malloc_stub: Expected integer type for size'';
    let size_t = llvm_target_size_t;

    out ''; malloc_stub_'' << sid << ''(''<< obj_t <<, sarg_t<<'')'' <<. ''generated by pretty-printer\<newline>'';
    out ''define'' <<. TPTR obj_t <<. ''@_malloc_stub_''<<sid<<.''(''<<sarg_t<<.''%size) {\<newline>'';
    (
    if sarg_w < llvm_target_size_w then
      out ''  %x1 = zext'' <<. sarg_t <<. ''%size to'' <<. size_t << ''\<newline>''
    else if sarg_w = llvm_target_size_w then
      out ''  %x1 = add'' <<. sarg_t <<. ''%size, 0''
    else 
      fail ''  malloc_stub: Size truncation not yet supported''
    );

    out ''  %x2 = getelementptr'' <<. obj_t <<, TPTR obj_t <<. ''null'' <<, size_t <<. ''1\<newline>'';
    out ''  %x3 = ptrtoint'' <<. TPTR obj_t <<. ''%x2 to'' <<. size_t << ''\<newline>'';
    out ''  %x4 = call i8* @calloc(''<< size_t <<. ''%x1'' <<, size_t <<. ''%x3) nounwind\<newline>'';
    out ''  %x5 = bitcast i8* %x4 to'' <<. TPTR obj_t << ''\<newline>'';
    out ''  ret'' <<. TPTR obj_t <<. ''%x5'' << ''\<newline>'';
    out ''}\<newline>''
  }"

fun out_free_stub :: "nat \<times> type \<Rightarrow> _" where
  "out_free_stub (sid,obj_t) = doM {
    ''define'' <<. ''void'' <<. ''@_free_stub_'' << sid <<. ''('' << TPTR obj_t <<. ''%ptr'' << '')'' <<. ''{\<newline>'';
    ''  '' << ''%x1 = bitcast '' <<. TPTR obj_t <<. ''%ptr to i8*\<newline>'';
    ''  '' << ''call void @free(i8* %x1) nounwind\<newline>'';
    out ''}\<newline>''
  }"


term "CHR ''\"''"

primrec out_program where
  "out_program (PROG procs) = doM {
    out ''; Generated by isabelle-llvm\<newline>'';
    \<comment> \<open>Prelude\<close>
    out ''; ### Target architecture configuration\<newline>'';
    ''target datalayout = \"'' <<llvm_target_datalayout << ''\"\<newline>'';
    ''target triple = \"'' <<llvm_target_triple << ''\"\<newline>'';
    ''; CFG size_t width = '' << llvm_target_size_w << ''\"\<newline>'';
    out ''\<newline>\<newline>'';

    out ''; ### External functions\<newline>'';
    out ''declare noalias i8* @calloc(i64, i64) nounwind\<newline>'';
    out ''declare void @free(i8*) nounwind\<newline>'';
    out ''\<newline>\<newline>'';

    \<comment> \<open>Program\<close>
    out ''; ### User-Defined functions, translated from isabelle-llvm\<newline>'';
    sep' out_named_procedure ''\<newline>'' procs;
    out ''\<newline>\<newline>'';

    \<comment> \<open>Malloc and Free stubs\<close>
    out ''; ### malloc and free stubs\<newline>'';
    ms \<leftarrow> use (pretty_s.malloc_stubs\<^sub>L)\<^sub>N;
    mmap out_malloc_stub ms;
    ms \<leftarrow> use (pretty_s.free_stubs\<^sub>L)\<^sub>N;
    mmap out_free_stub ms;
    return ()
  }"

adhoc_overloading out out_program

value "string_of ((TPTR (TSTRUCT [TARRAY 4 (TINT 32), TINT 1, TINT 32  ] )))"

value "string_of (42::nat)"

end
