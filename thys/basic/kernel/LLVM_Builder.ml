signature LLVM_BUILDER = sig
  type T
  type label
  type ty
  type value
  
  val builder: unit -> T
  
  val string_of: T -> string
  
  val set_dbg_trace: T -> bool -> unit
  
  (* Types *)
  val mkty_i: int -> ty
  val mkty_double: ty
  val mkty_ptr: ty -> ty
  val mkty_array: int -> ty -> ty
  val mkty_vector: int -> ty -> ty
  val mkty_struct: ty list -> ty
  val mkty_named: T -> string -> ty
  val mkty_fptr: ty option -> ty list -> ty

  val is_primitive_ty: ty -> bool
  
  val dstty_i: ty -> int
  (* TODO: Add other dstty functions *)

  val decl_named_ty: T -> string -> ty -> ty
  
  val ty_of_val: value -> ty    

  (* Constants *)    
  val mkc_iw: int -> int -> value
  val mkc_i: ty -> int -> value
  val mkc_d: ty -> Word64.word -> value
  val mkc_undef: ty -> value
  val mkc_zeroinit: ty -> value
  val mkc_null: ty -> value
  val mkc_fun: ty -> string -> value
  
  (* Procedures *)
  val open_proc: T -> ty option -> string -> (ty * string) list -> value list
  val close_proc: T -> unit

  (* Basic Blocks *)
  val variant_label: T -> string -> label
  val open_bb: T -> label -> unit
  
  
  type regname = string option
  
  
  (* Instructions *)
  (** Arithmetic *)
  val mk_arith_instr: string -> T -> regname -> value -> value -> value
  val mk_icmp_instr: string -> T -> regname -> value -> value -> value
  val mk_fcmp_instr: string -> T -> regname -> value -> value -> value
  val mk_ptrcmp_instr: string -> T -> regname -> value -> value -> value
  val mk_conv_instr: string -> T -> regname -> value -> ty -> value
  
  (** Data Structures *)
  val mk_extractvalue: T -> regname -> value -> int -> value
  val mk_insertvalue: T -> regname -> value -> value -> int -> value

  val mk_extractelement: T -> regname -> value -> value -> value
  val mk_insertelement: T -> regname -> value -> value -> value -> value
  
  
  val mk_ofs_ptr: T -> regname -> value -> value -> value
  val mk_gep_idx: T -> regname -> value -> value -> value

  (** Memory *)
  val mk_malloc: T -> regname -> ty -> value -> value
  val mk_free: T -> value -> unit

  val mk_load: T -> regname -> value -> value
  val mk_store: T -> value -> value -> unit
  
  val mk_alloca: T -> regname -> ty -> value
  
  
    
  (** Control Flow *)  
  val mk_call: T -> regname -> ty -> string -> value list -> value
  val mk_call_void: T -> string -> value list -> unit
  val mk_return: T -> value option -> unit

  (** Call and declare function as external, e.g., for intrinsics *)
  val mk_external_call: T -> regname -> ty -> string -> value list -> value
  val mk_external_call_void: T -> string -> value list -> unit
  
  val mk_external_call_attrs: T -> regname -> ty -> string -> value list -> string list list -> value
  val mk_external_call_void_attrs: T -> string -> value list -> string list list -> unit
  
  (** Parallel *)
  val mk_par_call: T -> regname -> 
    ty -> string -> value -> 
    ty -> string -> value 
    -> value  
  
  
  (* The branch instruction builders return the label of the current basic block, that is terminated by this branch *)
  val mk_br: T -> label -> label
  val mk_cbr: T -> value -> label -> label -> label
  
  (* Phi-nodes can be dynamically extended *)

  type phi_handle
    
  val mk_phi: T -> ty -> regname -> phi_handle * value
  val phi_add: T -> phi_handle -> value * label -> unit
  
  val mk_phi': T -> regname -> (value * label) list -> value
  

  (*
  val size_t: ty
  val mk_size_of: T -> string -> ty -> value        
  *)
  
      
end



structure LLVM_Builder : LLVM_BUILDER = struct
  type 'a ref = 'a Unsynchronized.ref
  
  type regname = string option
  
  exception Error of string
  
  type label = string

    
  datatype ty = 
      TInt of int 
    | TDouble  
    | TPtr of ty 
    | TStruct of ty list 
    | TVector of int * ty 
    | TArray of int * ty 
    | TNamed of string
    | TFptr of ty option * ty list

  
  type T = {
    next_id : int ref,
    out : (unit -> string) list ref,
    in_proc : bool ref,
    curr_bb : label option ref,
    local_names : Name.context ref,
    dbg_trace : bool ref,
    ext_funs : Symtab.set ref,
    named_tys : (string * ty option) Symtab.table ref (* Maps type name to type declaration. Empty string if not (yet) declared *)
  }

  fun builder_aux () : T = { 
    next_id = Unsynchronized.ref 0, 
    out = Unsynchronized.ref [],
    in_proc = Unsynchronized.ref false,
    curr_bb = Unsynchronized.ref NONE,
    local_names = Unsynchronized.ref Name.context,
    dbg_trace = Unsynchronized.ref false,
    ext_funs = Unsynchronized.ref Symtab.empty,
    named_tys = Unsynchronized.ref Symtab.empty
  }

  fun in_bb builder = is_some (!(#curr_bb builder))
          
  fun assert c msg = c orelse raise Error msg  
  fun assert_open_bb (builder:T) = 
    case !(#curr_bb builder) of 
      NONE => raise Error "No open basic block" 
    | SOME label => label
  
  fun set_dbg_trace (b:T) x = #dbg_trace b := x
  
  infixr 2 ^#
  
  fun op ^#(a,b) = a ^ " " ^ b
  
  
        
  local
    fun write (builder:T) s = ( #out builder := s :: !(#out builder))
    
    fun the_indentation (builder:T) = 
      (if ! (#in_proc builder) then "  " else "") ^ 
      (if in_bb builder then "  " else "")

    fun writeln_trace b s = (
      if !(#dbg_trace b) then tracing (s ()) else ();
      write b s;
      write b (K "\n")
    )  
      
  in      
    fun writeln' b s = let val ind = the_indentation b in writeln_trace b (fn () => ind ^ s ()) end
    fun writeln b s = writeln' b (K s)
    fun emptyln b = writeln_trace b (K "")
  end

  fun map_named_tys (b:T) = Unsynchronized.change (#named_tys b)
  fun decl_ext_fun_raw (b:T) s = Unsynchronized.change (#ext_funs b) (Symtab.insert_set s)

  fun mk_prelude (b:T) = let
    fun check_defined (name,("",_)) = raise Error ("Undefined named type " ^ name)
      | check_defined (_,(text,_)) = text
  
    val tydecls = Symtab.dest (!(#named_tys b))
      |> map check_defined
      |> space_implode "\n"
  
    val efdecls = 
      Symtab.keys (!(#ext_funs b))
    |> space_implode "\n"
  
  in
    (* TODO/FIXME: Hardcoded target! *)
    "; Generated by Isabelle/LLVM-shallow\n"
  ^ "target datalayout = \"e-m:e-i64:64-f80:128-n8:16:32:64-S128\"\n" 
  ^ "target triple = \"x86_64-pc-linux-gnu\"\n\n"
  ^ tydecls ^ "\n\n"
  ^ efdecls ^ "\n\n"
  end 
    
  fun string_of b = mk_prelude b ^ fold (fn s => fn acc => s () ^ acc) (!(#out b)) ""

  fun builder () = let
    val b = builder_aux ();
  in 
    b
  end 
  
  
  
  fun check_named_ty b name = map_named_tys b (Symtab.default (name,("",NONE)))
  fun decl_named_ty_raw b name (text,ty) = (
    check_named_ty b name;
    case Symtab.lookup (!(#named_tys b)) name of
      SOME ("",NONE) => map_named_tys b (Symtab.update (name,(text, SOME ty)))
    | _ => raise Error ("Duplicate named type declaration:" ^# name)) 
    
  fun lookup_named_ty (b:T) name =   
    case Symtab.lookup (!(#named_tys b)) name of
      SOME (_, SOME ty) => ty
    | SOME (_, NONE) => raise Error ("Undefined (but declared) named type:" ^# name)
    | _ => raise Error ("Undeclared named type:" ^# name)
    

  (* Primitive types: those valid as vector elements *)  
  fun is_primitive_ty (TInt _) = true
    | is_primitive_ty (TDouble) = true
    | is_primitive_ty (TPtr _) = true
    | is_primitive_ty _ = false
    
      
  fun mkty_i w = TInt w
  val mkty_double = TDouble
  fun mkty_ptr ty = TPtr ty
  (*fun mkty_array n ty = "[" ^ Int.toString n ^# "x" ^# ty ^"]"*)
  (*fun mkty_struct tys = "{" ^ (separate ", " tys |> implode) ^ "}"*)
  fun mkty_array n ty = TArray (n,ty)
  fun mkty_vector n ty = ( 
    assert (is_primitive_ty ty) "mkty_vector: non-primitive element"; 
    assert (n>0) "mkty_vector: n=0";
    TVector (n,ty)
  )
  fun mkty_struct tys = TStruct tys
  fun mkty_named b name = (check_named_ty b name; TNamed name)
  fun mkty_fptr ty tys = TFptr (ty, tys)

  fun dstty_i (TInt w) = w | dstty_i _ = raise Fail "dstty_i"
  fun dstty_ptr (TPtr ty) = ty | dstty_ptr _ = raise Fail "dstty_ptr"
  
  fun isty_i (TInt _) = true | isty_i _ = false
  fun isty_f (TDouble) = true | isty_f _ = false
  
  
  
  val size_w = 64
  val size_t = mkty_i size_w (* TODO: Hardcoded target *)
  
  
  fun quote_name n = n (* TODO: Put into quotes, and escape if necessary! *)  
  
    
  datatype value = REG of ty * string | CONST of ty * string | UNNAMED
  
  fun ty_of_val (REG (ty,_)) = ty | ty_of_val (CONST (ty,_)) = ty | ty_of_val UNNAMED = raise Error ("ty_of_val UNNAMED")
  

  (* Work around ~ sign, which is - in LLVM *)  
  fun int_to_string i = if i<0 then "-"^Int.toString (abs i) else Int.toString i
  
  fun mkc_i (ty as TInt _) i = CONST (ty, int_to_string i)
    | mkc_i _ _ = raise Error ("mkc_i: Expected integer type")

  (* Also in LLC_Lib. Duplicated here as this is part of printing TCB *)  
  val str_of_w64 = Word64.fmt StringCvt.HEX #> StringCvt.padLeft #"0" 16 #> prefix "0x";  
    
  fun mkc_d (ty as TDouble) d = CONST (ty, str_of_w64 d)
    | mkc_d _ _ = raise Error ("mkc_d: Expected double type")
    
      
  fun mkc_iw w = mkc_i (mkty_i w)
  fun mkc_undef ty = CONST (ty, "undef")
  fun mkc_zeroinit ty = CONST (ty, "zeroinitializer")

  fun mkc_null (ty as TPtr _) = CONST (ty,"null")
    | mkc_null _ = raise Error ("mkc_null: Expected pointer type")
    
  fun mkc_fun (ty as TFptr _) name = CONST (ty,"@"^quote_name name)
    | mkc_fun _ _ = raise Error ("mkc_fun: Expected function type")
    
  fun iop sr f = let val s = !sr; val (r,s) = f s in sr:=s; r end
  
  fun variant_name (builder:T) s = iop (#local_names builder) (fn context => 
    let 
      val (s,context) = Name.variant s context
    in (s,context) end
    )
  
  val variant_reg = variant_name
  val variant_label = variant_name

  (*
  fun define_name (builder:T) s = iop (#local_names builder) (fn context => let
    val _ = Name.is_declared context s andalso raise Error ("define-name: Duplicate name " ^ s)
    val context = Name.declare s context
  in
    ((),context)
  end
  ) 
  *)
  
  fun fresh_id (builder:T) = iop (#next_id builder) (fn i => (i,i+1))
  val fresh_id_str = Int.toString o fresh_id
  
  
  fun check_regname b (SOME s) = let val s = variant_reg b s in SOME s end
    | check_regname _ NONE = NONE

  fun pr_tyname n = "%" ^ quote_name n
  fun pr_reg r = "%" ^ quote_name r
  fun pr_ty (TInt w) = "i" ^ Int.toString w
    | pr_ty (TDouble) = "double"
    | pr_ty (TPtr ty) = pr_ty ty ^ "*"
    | pr_ty (TVector (n, ty)) = "<" ^ Int.toString n ^# "x" ^# pr_ty ty ^">"
    | pr_ty (TArray (n, ty)) = "[" ^ Int.toString n ^# "x" ^# pr_ty ty ^"]"
    | pr_ty (TStruct tys) = "{" ^# pr_tys tys ^# "}"
    | pr_ty (TFptr (ty,tys)) = pr_ty' ty ^# "(" ^# pr_tys tys ^# ")" ^# "*"
    | pr_ty (TNamed name) = pr_tyname name
  and pr_tys tys = separate ", " (map pr_ty tys) |> implode
  and pr_ty' (NONE) = "void" | pr_ty' (SOME ty) = pr_ty ty  
      
  fun pr_param (ty,name) = pr_ty ty ^ " " ^ pr_reg name
  fun pr_params params = separate ", " (map pr_param params) |> implode
  
  
  fun pr_label l = "%"^quote_name l
  fun pr_ty_label l = "label" ^# pr_label l
  
  fun pr_proc p = "@"^quote_name p
  
  val pr_int = int_to_string 


  fun pr_ty_attrs ty attrs = pr_ty ty ^ (map (prefix " ") attrs |> implode)
  fun pr_tys_attrs tys attrs = separate ", " (map2 pr_ty_attrs tys attrs) |> implode
  
  fun decl_ext_fun_attrs b rty name ptys pattrs = let
    val raw = "declare" ^# pr_ty' rty ^# pr_proc name ^ "(" ^ pr_tys_attrs ptys pattrs ^ ")"
  in
    decl_ext_fun_raw b raw;
    name
  end  
    
  fun decl_ext_fun b rty name ptys = decl_ext_fun_attrs b rty name ptys (map (K []) ptys)

  fun decl_named_ty b name ty = let
    val text = pr_tyname name ^# "=" ^# "type" ^# pr_ty ty
  in
    decl_named_ty_raw b name (text, ty);
    mkty_named b name
  end
  
  (* Resolve named type until unnamed type is reached. *)
  fun resolve_named_ty b ty = let
    fun rsl V (TNamed name) = let
        val _ = Symtab.defined V name andalso raise Error ("Cyclic named types over " ^# name)
        val ty = lookup_named_ty b name
      in
        rsl (Symtab.insert_set name V) ty
      end
    | rsl _ ty = ty  
  in
    rsl Symtab.empty ty
  end
  
    
  fun open_bb b label = (
    assert (not (in_bb b)) "Already open basic block";
    emptyln b;
    writeln b (quote_name label ^ ":");
    #curr_bb b := SOME label
  )
  
  fun open_proc (builder:T) rty name params = let
    val _ = ! (#in_proc builder) andalso raise Error "open_proc: Already open";
    val _ = #local_names builder := Name.context;
    
    (* val _ = map (apsnd (define_name builder)) params *)
    
    val params = map (apsnd (variant_name builder)) params
    
    val _ = emptyln builder
    val _ = writeln builder ("define" ^# pr_ty' rty ^# pr_proc name ^ "(" ^ pr_params params ^ ")" ^# "{" );
    
    val _ = #in_proc builder := true;
    
    val _ = open_bb builder (variant_label builder "start")
  in
    map REG params
  end
  
  fun close_proc (builder:T) = (
    ! (#in_proc builder) orelse raise Error "close_proc: No open procedure";
    #in_proc builder := false;
    writeln builder "}"
  )
   
         
  fun pr_val (REG (_,r)) = pr_reg r
    | pr_val (CONST (_,l)) = l
    | pr_val UNNAMED = raise Error ("pr_val UNNAMED")

  fun pr_ty_val v = pr_ty (ty_of_val v) ^# pr_val v

  (*  Build %dst = s. dst must be unique. Return value (rty,%dst)
  *)
  fun mk_dst_instr' b dst rty s = let
    val _ = assert_open_bb b
    val dst = check_regname b dst
  in
    case dst of
      NONE => (writeln' b s; UNNAMED)
    | SOME dst => (
        writeln' b (fn () => pr_reg dst ^# "=" ^# s ());
        REG (rty,dst)
      )
  end
  
  fun mk_dst_instr b dst rty s = mk_dst_instr' b dst rty (K s)
  
   
  fun mk_arith_instr iname b dst op1 op2 = let
    val _ = assert (ty_of_val op1 = ty_of_val op2) "arith_instr: different types"
    val ty = ty_of_val op1
  in
    mk_dst_instr b dst ty (iname ^# pr_ty_val op1 ^ ", " ^ pr_val op2)
  end    
  
  fun mk_conv_instr iname b dst op1 ty = 
    mk_dst_instr b dst ty (iname ^# pr_ty_val op1 ^# "to" ^# pr_ty ty)
  
  fun mk_icmp_instr cty b dst op1 op2 = let
    val _ = assert (ty_of_val op1 = ty_of_val op2) "arith_instr: different types"
    val _ = assert (isty_i (ty_of_val op2)) "mk_icmp_instr: expected integer type"
  in
    mk_dst_instr b dst (mkty_i 1) ("icmp" ^# cty ^# pr_ty_val op1 ^ ", " ^ pr_val op2)
  end

  fun mk_fcmp_instr cty b dst op1 op2 = let
    val _ = assert (ty_of_val op1 = ty_of_val op2) "arith_instr: different types"
    val _ = assert (isty_f (ty_of_val op2)) "mk_fcmp_instr: expected float type"
  in
    mk_dst_instr b dst (mkty_i 1) ("fcmp" ^# cty ^# pr_ty_val op1 ^ ", " ^ pr_val op2)
  end
  
  
  fun mk_extractvalue b dst op1 idx = let
    val _ = assert (idx>=0) "extractvalue: Negative index"
    
    val ty = ty_of_val op1 |> resolve_named_ty b
    
    val dty = case ty of 
        TStruct tys => (
          assert (idx < length tys) "extractvalue: index out of bounds";
          nth tys idx
        )
      | _ => raise Error "extractvalue: expected structure type"
    
  in
    mk_dst_instr b dst dty ("extractvalue" ^# pr_ty_val op1 ^", "^ pr_int idx)
  end
  
  fun mk_insertvalue b dst op1 op2 idx = let
    val _ = assert (idx>=0) "insertvalue: Negative index"
    val ty = ty_of_val op1
  in
    mk_dst_instr b dst ty ("insertvalue" ^# pr_ty_val op1 ^", "^ pr_ty_val op2 ^", "^ pr_int idx)
  end

  fun mk_extractelement b dst op1 idx = let
    val ty = ty_of_val op1 |> resolve_named_ty b
    
    val dty = case ty of 
        TVector (_,vty) => (
          vty
        )
      | _ => raise Error "extractelement: expected vector type"
    
  in
    mk_dst_instr b dst dty ("extractelement" ^# pr_ty_val op1 ^", "^  pr_ty_val idx)
  end
  
  fun mk_insertelement b dst op1 op2 idx = let
    val ty = ty_of_val op1
  in
    mk_dst_instr b dst ty ("insertelement" ^# pr_ty_val op1 ^", "^ pr_ty_val op2 ^", "^ pr_ty_val idx)
  end
  
    
  
  type phi_handle = ty * string list ref
  
  (*  
  val mk_phi: T -> regname -> (value * label) list -> phi_handle * value
  val phi_add: T -> phi_handle -> value * label -> unit
  *)

  fun phi_add _ (ty,hnd) (v,l) = let
    val _ = ty = ty_of_val v orelse raise Error "phi_add: Wrong type"
  
    val s = "[" ^# pr_val v ^", "^ pr_label l ^# "]"
  in
    hnd := s :: !hnd 
  end
  
    
  fun mk_phi b rty dst = let
    val pairs = Unsynchronized.ref []

    (* TODO: Assert start of bb! *)
      
    fun str () = let 
      val _ = assert (not (null (!pairs))) "phi: Empty predecessor list"
      val args = separate ", " (!pairs) |> implode
    in
      "phi" ^# pr_ty rty ^# args
    end
  
    val hnd = (rty,pairs)
    
  in
    (hnd, mk_dst_instr' b dst rty str)
  end
  
  fun mk_phi' b dst (pairs as (v,_)::_) = let
    val (hnd,res) = mk_phi b (ty_of_val v) dst
    val _ = map (phi_add b hnd) pairs
  in
    res
  end
  | mk_phi' _ _ [] = raise Error "mk_phi': Empty arguments"
  
  
  fun pr_args args = separate ", " (map pr_ty_val args) |> implode
  
  fun mk_call b dst rty proc args = 
    mk_dst_instr b dst rty ("call" ^# pr_ty rty ^# pr_proc proc ^# "(" ^ pr_args args ^ ")")
  
  fun mk_call_void b proc args = let
    val _ = assert_open_bb b
  in
    "call" ^# "void" ^# pr_proc proc ^# "(" ^ pr_args args ^ ")"
    |> writeln b
  end
  
  fun mk_return b NONE = (
      assert_open_bb b;
      writeln b "ret void";
      #curr_bb b := NONE
    ) 
  | mk_return b (SOME op1) = (
      assert_open_bb b;
      writeln b ("ret" ^# pr_ty_val op1);
      #curr_bb b := NONE
    )
  
  fun mk_external_call b dst rty proc args = let
    val proc = decl_ext_fun b (SOME rty) proc (map ty_of_val args)
  in
    mk_call b dst rty proc args
  end
  
  fun mk_external_call_void b proc args = let
    val proc = decl_ext_fun b NONE proc (map ty_of_val args)
  in
    mk_call_void b proc args
  end

  fun mk_external_call_attrs b dst rty proc args attrs = let
    val proc = decl_ext_fun_attrs b (SOME rty) proc (map ty_of_val args) attrs
  in
    mk_call b dst rty proc args
  end
  
  fun mk_external_call_void_attrs b proc args attrs = let
    val proc = decl_ext_fun_attrs b NONE proc (map ty_of_val args) attrs
  in
    mk_call_void b proc args
  end
      
    
  fun mk_br b label = let
    val cbl = assert_open_bb b
    val _ = writeln b ("br" ^# pr_ty_label label)
    val _ = #curr_bb b := NONE
  in
    cbl
  end
  
  fun mk_cbr b op1 l1 l2 = let
    val cbl = assert_open_bb b
    val _ = writeln b ("br" ^# pr_ty_val op1 ^", "^  pr_ty_label l1 ^", "^ pr_ty_label l2)
    val _ = #curr_bb b := NONE
  in
    cbl
  end
  
  fun mk_ofs_ptr b dst op1 op2 = let
    val ty = ty_of_val op1
    val bty = dstty_ptr ty
  in
    mk_dst_instr b dst ty ("getelementptr" ^# pr_ty bty ^", "^ pr_ty_val op1 ^", "^ pr_ty_val op2)
  end
    
  fun dst_iconst (CONST (TInt _, v)) = the (Int.fromString v) (* TODO: Hack! Make const-structure explicit instead.*)
    | dst_iconst _ = raise Fail "Expected integer constant"
  
  fun mk_gep_idx b dst op1 op2 = let
    val ty = ty_of_val op1
    val bty = dstty_ptr ty 
    
    val rty = case resolve_named_ty b bty of
      TStruct tys => let
        val i = dst_iconst op2
        val _ = assert (0<=i andalso i<length tys) "gep_idx: Index out of range"
      in
        nth tys i
      end
    | TArray (_, ty) => ty
    | _ => raise Fail "gep_idx: Invalid base type"
  
  in
    mk_dst_instr b dst rty ("getelementptr" ^# pr_ty bty ^", "^ pr_ty_val op1 ^", "^ "i32 0" ^", "^ pr_ty_val op2)
    (* TODO: Is i32 for first index a good choice here? *)
  end
  

  fun mk_size_of b dst ty = let
    val t1 = mk_ofs_ptr b (SOME "t") (mkc_null (TPtr ty)) (mkc_i size_t 1)
    val res = mk_conv_instr "ptrtoint" b dst t1 size_t
  in
    res  
  end  

  fun cnv_to_size_t b dst op1 = let
    val w = dstty_i (ty_of_val op1)
  in 
    if w < size_w then
      mk_conv_instr "zext" b dst op1 size_t
    else if w = size_w then op1
    else raise Fail "Safe downcast to size_t not yet supported"
  end
  
  val i8ptr = mkty_ptr (mkty_i 8)
  
  fun mk_malloc b dst ty op1 = let
    val calloc_name = decl_ext_fun b (SOME i8ptr) "isabelle_llvm_calloc" [size_t, size_t]
    val op1 = cnv_to_size_t b (SOME "") op1
    val sz = mk_size_of b (SOME "") ty
    val res = mk_call b (SOME "") i8ptr calloc_name [op1,sz]
    val res = mk_conv_instr "bitcast" b dst res (mkty_ptr ty)
  in
    res
  end
  
  fun mk_free b op1 = let
    val free_name = decl_ext_fun b NONE "isabelle_llvm_free" [i8ptr]
    val _ = assert (can dstty_ptr (ty_of_val op1)) "free: expected pointer type"
    val op1 = mk_conv_instr "bitcast" b (SOME "") op1 i8ptr
    val _ = mk_call_void b free_name [op1]
  in
    ()
  end
  
  fun decl_isabelle_llvm_parallel b = let
    val fptr = mkty_fptr NONE [i8ptr]
    val _ = decl_ext_fun b NONE "isabelle_llvm_parallel" [fptr,fptr,i8ptr,i8ptr]
  in
    ()
  end
  
  fun mk_par_call_auxiliaries b rty1 proc1 aty1 rty2 proc2 aty2 = let
    val rty1 = pr_ty rty1
    val rty2 = pr_ty rty2
    val aty1 = pr_ty aty1
    val aty2 = pr_ty aty2
    val uid = fresh_id_str b
    
    val (name, text) = LLVM_Builder_templates.mk_par_call uid rty1 rty2 proc1 proc2 aty1 aty2
    
    val _ = decl_isabelle_llvm_parallel b
    
    
    val _ = decl_ext_fun_raw b text (* TODO: Somewhat of a hack. Add-to-prelude would be correct functionality here. *)
  in
    name
  end
  
  fun mk_par_call b dst rty1 proc1 arg1 rty2 proc2 arg2 = let
    val aty1 = ty_of_val arg1
    val aty2 = ty_of_val arg2
    val name = mk_par_call_auxiliaries b rty1 proc1 aty1 rty2 proc2 aty2
    val rty = mkty_struct [rty1,rty2]

    val res = mk_call b dst rty name [arg1,arg2]   
  in
    res
  end
  
  
  
  fun mk_ptrcmp_instr cty b dst op1 op2 = let
    val _ = assert (ty_of_val op1 = ty_of_val op2) "ptrcmp_instr: different types"
    val _ = assert (can dstty_ptr (ty_of_val op1)) "ptrcmp_instr: expected pointer types"
    val _ = assert (cty="eq" orelse cty="ne") "ptrcmp_instr: Only supports eq and ne comparsion!"
    val op1' = mk_conv_instr "ptrtoint" b (SOME "") op1 size_t
    val op2' = mk_conv_instr "ptrtoint" b (SOME "") op2 size_t
  in
    mk_icmp_instr cty b dst op1' op2'
  end
  
  fun mk_load b dst op1 = let 
    val rty = ty_of_val op1 |> dstty_ptr
  in
    mk_dst_instr b dst rty ("load" ^# pr_ty rty ^", "^ pr_ty_val op1)
  end

  fun mk_store b op1 op2 = let
    val _ = assert_open_bb b
  in
    writeln b ("store" ^# pr_ty_val op1 ^", "^ pr_ty_val op2)
  end   

  fun mk_alloca b dst ty = let
    val rty = mkty_ptr ty
  in
    mk_dst_instr b dst rty ("alloca" ^# pr_ty ty)
  end  
  
        
    
end
