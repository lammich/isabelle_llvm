section \<open>LLVM Code Generator\<close>
theory LLVM_Codegen
imports 
  LLVM_Shallow
  "../preproc/Monadify" (* Needed for M_CONST *)
begin

    (* DO NOT USE IN PRODUCTION VERSION \<rightarrow> SLOWDOWN *)
    declare [[ML_exception_debugger, ML_debugger, ML_exception_trace]]

  text \<open>This is the trusted part of the code generator, which accepts
    Isabelle-LLVM programs that follow a strict format 
    (fully monadified, only \<open>ll_\<close> instructions).
    
    The preprocessor and user-interface of the code generator can be found in 
    @{file "../preproc/LLVM_Codegen_Preproc.thy"}
  \<close>

  subsection \<open>Named Structures\<close>
  text \<open>
    The code generator will create identified types in LLVM for types registered here
  \<close>
  
  definition "ll_is_identified_structure (name::string) TYPE('t::llvm_rep) \<equiv> llvm_struct.is_struct (struct_of TYPE('t))"
  named_theorems ll_identified_structures \<open>LLVM: Identified Structures\<close>

  
  named_theorems ll_to_val \<open>LLVM: Equations to compute \<open>to_val\<close> shape\<close>
  
  
  (*lemma TERM_TYPE_I: "TERM (TYPE ('a))" .*)
  
  ML_val \<open> IntInf.pow (2,64)  \<close>
  
  typ "_ llM"
  
  subsection \<open>General Functions\<close>
  ML \<open> structure LLC_Lib = 
    struct
      fun dest_llM (Type (@{type_name M},[T,@{typ llvm_val}])) = T
        | dest_llM ty = raise TYPE("dest_llM",[ty],[]);
      
      val is_llM = can dest_llM

      fun dest_ptrT (Type (@{type_name ptr},[T])) = T
        | dest_ptrT ty = raise TYPE("dest_ptrT",[ty],[]);
      
      fun dest_numeralT (Type (@{type_name \<open>bit0\<close>},[ty])) = 2*dest_numeralT ty
        | dest_numeralT (Type (@{type_name \<open>bit1\<close>},[ty])) = 2*dest_numeralT ty+1
        | dest_numeralT (Type (@{type_name \<open>num0\<close>},[])) = 0
        | dest_numeralT (Type (@{type_name \<open>num1\<close>},[])) = 1
        | dest_numeralT ty = raise TYPE ("dest_numeralT",[ty],[])
    
      fun dest_wordT (Type (@{type_name word},[T])) = dest_numeralT T
        | dest_wordT T = raise TYPE("dest_wordT",[T],[])
        
      fun dest_word_const (t) = HOLogic.dest_number t |>> dest_wordT
      
      fun dest_double_const @{mpat \<open>double_of_word ?w\<close>} = let
          val (_,n) = HOLogic.dest_number w 
          val _ = 0<=n andalso n<IntInf.pow (2,64) orelse raise TERM("dest_double_const (0\<le> _ <2^64): ",[w])
          val n = Word64.fromInt n
        in n end
        | dest_double_const t = raise TERM("dest_double_const",[t])

      fun dest_float_const @{mpat \<open>single_of_word ?w\<close>} = let
          val (_,n) = HOLogic.dest_number w 
          val _ = 0<=n andalso n<IntInf.pow (2,32) orelse raise TERM("dest_float_const (0\<le> _ <2^32): ",[w])
          val n = Word32.fromInt n
        in n end
        | dest_float_const t = raise TERM("dest_float_const",[t])
        
        
      (* Testing the dest-functions, to make them fail early after forgetting to 
        adapt them for changes to foundation.
      
        We use one indirection over a function, to make failed tests visible in stack trace
      *)  
      local  
        fun test_dest_llM () = dest_llM @{typ "_ llM"}  
        val _ = test_dest_llM ()
        
        fun test_dest_ptrT () = dest_ptrT @{typ "_ ptr"}  
        val _ = test_dest_ptrT ()

        fun test_dest_numeralT () = dest_numeralT @{typ "32"} = 32 orelse error "test_dest_numeralT"
        val _ = test_dest_numeralT ()

        fun test_dest_wordT () = dest_wordT @{typ "32 word"} = 32 orelse error "test_dest_wordT"
        val _ = test_dest_wordT ()
                        
      in end
      
      fun dest_eqn @{mpat "?lhs\<equiv>?rhs"} = (lhs,rhs)
        | dest_eqn @{mpat \<open>Trueprop (?lhs = ?rhs)\<close>} = (lhs,rhs)
        | dest_eqn t = raise TERM ("dest_eqn",[t])

      val is_eqn = can dest_eqn
        
      val dest_eqn_thm = dest_eqn o Thm.prop_of  
      
      val lhs_of_eqn = fst o dest_eqn
      val rhs_of_eqn = snd o dest_eqn
      
      val head_of_eqn =head_of o lhs_of_eqn
      val head_of_eqn_thm = head_of_eqn o Thm.prop_of
      
      fun eqn_conv cvl cvr ct = let 
        val cv = Conv.arg1_conv cvl then_conv Conv.arg_conv cvr 
      in
        (case Thm.term_of ct of
          @{mpat "_\<equiv>_"} => cv ct
        | @{mpat "Trueprop (_ = _)"} => HOLogic.Trueprop_conv cv ct
        | _ => raise CTERM ("rhs_conv", [ct]))
      end
      
      fun lhs_conv cv = eqn_conv cv Conv.all_conv
      fun rhs_conv cv = eqn_conv Conv.all_conv cv
      
      (*              
      (* TODO: Move *)
      fun instantiate_uc (tyenv,tenv) thm = let
        val thy = Thm.theory_of_thm thm
        
        val tyi = Vartab.dest tyenv |> map (fn (n,(s,T)) => ((n,s),Thm.global_ctyp_of thy T))
          |> @{print}
        val ti = Vartab.dest tenv |> map (fn (n,(s,t)) => ((n,s),Thm.global_cterm_of thy t))
          |> @{print}
      in
        Thm.instantiate (tyi,ti) thm
      end
      *)

      fun is_monomorphic_type T = not (Term.exists_subtype (fn TVar _ => true | TFree _ => true | _ => false) T)
      
      fun is_ground_term t = 
        not (Term.exists_type (not o is_monomorphic_type) t)
        andalso not (Term.exists_subterm (fn tt => is_Var tt orelse is_Free tt) t)

      fun assert_ground_term t = is_ground_term t orelse           
        raise TYPE("Expected ground term",[fastype_of t],[t])
      
      (*  
      fun is_monomorphic_const (Const (_,T)) = is_monomorphic_type T
        | is_monomorphic_const _ = false

      fun assert_monomorphic_const t = 
        is_monomorphic_const t orelse 
          raise TYPE("Expected monomorphic constant",[fastype_of t],[t])
      *)      

      fun unique_variant1 n name ntab = let
        val name' = if n=0 then name else name ^ Int.toString n
      in    
        if Symtab.defined ntab name' then unique_variant1 (n+1) name ntab
        else (name', Symtab.insert_set name' ntab)
      end
      
      val unique_variant = unique_variant1 0
      
      
      fun the_assert msg NONE = raise Fail msg 
         | the_assert _ (SOME x) = x 
      
      
      fun dest_identified_structure_thm thm = case Thm.prop_of thm of 
        @{mpat (typs) "Trueprop (ll_is_identified_structure ?name TYPE(?'v_t::llvm_rep))"} => let 
          val name = HOLogic.dest_string name
        in (name,t) end
      | _ => raise THM("dest_identified_structure_thm",~1,[thm])
         
      
      fun expand_eta_all t = let
        fun declare_bnames (Free (a,_)) = Name.declare a
          | declare_bnames (Abs (x,_,t)) = declare_bnames t #> Name.declare x
          | declare_bnames (t1$t2) = declare_bnames t1 #> declare_bnames t2
          | declare_bnames _ = I
      
        val context = declare_bnames t Name.context
        val Ts = binder_types (fastype_of t)
        val xTs = Name.invent context "x" (length Ts) ~~ Ts
      
        fun exp [] t = t
          | exp (_::Ts) (Abs (x,T,t)) = Abs (x,T,exp Ts t)
          | exp ((x,T)::Ts) t = Abs (x,T,exp Ts (incr_boundvars 1 t $ Bound 0))
        
      in
        exp xTs t
      end  
      

      (* Simple name mangling. Get uniqued afterwards! *)
      fun name_of_head (Const (x,_)) = x
        | name_of_head (Free (x,_)) = x
        | name_of_head (Var ((x, _), _)) = x
        | name_of_head (f$x) = name_of_head f ^ "_" ^ name_of_head x
        | name_of_head (Abs (_,_,t)) = name_of_head t
        | name_of_head (Bound _) = "__"
      
              
      val llc_compile_while = Attrib.setup_config_bool @{binding llc_compile_while} (K true)
      
      val llc_compile_par_call = Attrib.setup_config_bool @{binding llc_compile_par_call} (K false)
      
      val llc_compile_avx512f = Attrib.setup_config_bool @{binding llc_compile_avx512f} (K false)

      val str_of_w32 = Word32.fmt StringCvt.HEX #> StringCvt.padLeft #"0" 8 #> prefix "0x";
      val str_of_w64 = Word64.fmt StringCvt.HEX #> StringCvt.padLeft #"0" 16 #> prefix "0x";
      
            
    end
  \<close>
  
  subsection \<open>Intermediate Representation\<close>
  text \<open>
    The code generator translates Isabelle terms into this intermediate representation,
    and then generates LLVM code from this. 
    No transformations are done on the intermediate representation, but it merely serves 
    to cleanly separate the interpretation and checking of Isabelle terms, and the generation
    of LLVM code.
  \<close>
  
  (*
  TODO: conceptually, named types should be disambiguated during monomorphization,
    such that all named types come without type parameters!
    Is this feasible? Monomorphization would have to define new types.
  *)  
  
  ML_val \<open>
    Word64.fromInt 63 |> Word64.fmt StringCvt.HEX |> StringCvt.padLeft #"0" 16 |> prefix "0x";
  
    Word64.fromInt 63 
  \<close>
  
  
  ML \<open> structure LLC_Intermediate = 
    struct
    
      (* LLC intermediate representation. Somewhere in between Isabelle and LLVM-IR *)    
      
      datatype llc_type = TInt of int | TFloat | TDouble | TPtr of llc_type | TStruct of llc_type list | TNamed of string
      datatype llc_const = CInit | CInt of int | CFloat of Word32.word | CDouble of Word64.word | CNull
      datatype llc_opr = OVar of string | OConst of llc_const
      type llc_topr = llc_type * llc_opr
      datatype llc_topr' = OOOp of llc_topr | OOType of llc_type | OOCIdx of int

      datatype llc_cmd = 
                 CmIf of llc_topr * llc_block * llc_block
               | CmWhile of (llc_type * string) * llc_block * llc_block * llc_topr
               | CmInstr of string * llc_topr' list
               | CmCall of llc_type option * string * llc_topr list
               | CmPar of llc_type * string * llc_topr * llc_type * string * llc_topr
      
          and llc_block =
                BlBind of (llc_type * string) option * llc_cmd * llc_block
              | BlReturn of llc_topr option 
    
      datatype llc_eqn =              
                EQN of llc_type option * string * (llc_type * string) list * llc_block
    
      datatype llc_named_type = Named_Type of string * llc_type list                
                
      
      fun pretty_mstr m s = Pretty.markup m [Pretty.str s]
      
      fun pretty_type (TInt w) = pretty_mstr Markup.keyword1 ("i" ^ Int.toString w)
        | pretty_type (TFloat) = pretty_mstr Markup.keyword1 ("float")
        | pretty_type (TDouble) = pretty_mstr Markup.keyword1 ("double")
        | pretty_type (TPtr T) = Pretty.block [pretty_type T, Pretty.str "*"]
        | pretty_type (TStruct Ts) = Pretty.list "{" "}" (map pretty_type Ts)
        | pretty_type (TNamed name) = Pretty.str name
      
      fun pretty_const CInit = pretty_mstr Markup.keyword1 "zeroinitializer"
        | pretty_const (CInt i) = pretty_mstr Markup.numeral (Int.toString i)
        | pretty_const (CFloat w) = pretty_mstr Markup.numeral (LLC_Lib.str_of_w32 w)
        | pretty_const (CDouble w) = pretty_mstr Markup.numeral (LLC_Lib.str_of_w64 w)
        | pretty_const CNull = pretty_mstr Markup.keyword1 "null"

      fun pretty_opr (OVar name) = Pretty.str name
        | pretty_opr (OConst c) = pretty_const c
        
      fun pretty_topr (T,opr) = Pretty.block [pretty_type T, Pretty.brk 1, pretty_opr opr]
      
      fun pretty_topr' (OOOp x) = pretty_topr x 
        | pretty_topr' (OOType T) = pretty_type T
        | pretty_topr' (OOCIdx idx) = pretty_mstr Markup.numeral (Int.toString idx)
      
      fun pretty_tname (T,v) = Pretty.block [pretty_type T, Pretty.brk 1, Pretty.str v]  
        
      fun pretty_type' (SOME t) = pretty_type t 
        | pretty_type' NONE = pretty_mstr Markup.keyword1 "void"  
        
      fun pretty_cmd (CmIf (b, c1, c2)) = Pretty.block [
          pretty_mstr Markup.keyword2 "if", Pretty.brk 1, pretty_topr b, Pretty.brk 1, pretty_mstr Markup.keyword2 "then", Pretty.fbrk,
            Pretty.blk (4, [pretty_block c1]),
            Pretty.fbrk, pretty_mstr Markup.keyword2 "else", Pretty.fbrk,
            Pretty.blk (4, [pretty_block c2])
          ]  
        | pretty_cmd (CmWhile (v,b,c,s)) = Pretty.block [
            pretty_mstr Markup.keyword2 "while", Pretty.enclose "[" "]" [pretty_tname v], Pretty.fbrk, 
              Pretty.blk (4, [pretty_block b]),
              Pretty.fbrk, pretty_mstr Markup.keyword2 "do", Pretty.fbrk,
              Pretty.blk (4, [pretty_block c]),
              Pretty.fbrk, pretty_mstr Markup.keyword2 "init ", pretty_topr s
          ] 
        | pretty_cmd (CmInstr (name,ops)) = Pretty.block [Pretty.str name, Pretty.brk 1, Pretty.list "" "" (map pretty_topr' ops)]
        | pretty_cmd (CmCall (T,name,ops)) = Pretty.block [pretty_type' T, pretty_mstr Markup.keyword2 " call ", Pretty.str name, Pretty.brk 1, Pretty.list "(" ")" (map pretty_topr ops)]
        | pretty_cmd (CmPar (T1,name1,op1,T2,name2,op2)) = Pretty.block [
          pretty_type (TStruct [T1,T2]), pretty_mstr Markup.keyword2 " par ", 
          Pretty.str name1, Pretty.brk 1, Pretty.list "(" ")" [pretty_topr op1], pretty_mstr Markup.keyword2 " and ",
          Pretty.str name2, Pretty.brk 1, Pretty.list "(" ")" [pretty_topr op2]
          ]
        
      and pretty_block blk = let
        fun pblst (BlBind (SOME tv,c,b)) = Pretty.block [pretty_tname tv, Pretty.str " = ", pretty_cmd c] :: pblst b
          | pblst (BlBind (NONE,c,b)) = pretty_cmd c :: pblst b
          | pblst (BlReturn NONE) = [pretty_mstr Markup.keyword2 "return"]
          | pblst (BlReturn (SOME x)) = [Pretty.block [pretty_mstr Markup.keyword2 "return ",pretty_topr x]]
          
      in
        Pretty.block (Pretty.fbreaks (pblst blk))
      end
        
      fun pretty_eqn (EQN (ty,name,params,block)) = Pretty.block [
        Pretty.block [pretty_type' ty, Pretty.brk 1, Pretty.str name, Pretty.list "(" ")" (map pretty_tname params), Pretty.str " {", 
          Pretty.fbrk, Pretty.blk (4,[pretty_block block]), Pretty.fbrk, Pretty.str "}"], Pretty.fbrk
        ]

      fun pretty_eqns eqns = Pretty.block (Pretty.fbreaks (map pretty_eqn eqns))
      
      fun pretty_named_type (Named_Type (name,tys)) = Pretty.block [pretty_mstr Markup.keyword3 "type ", Pretty.str name, Pretty.str " = ", 
        Pretty.list "{" "}" (map pretty_type tys) ]
      
      fun pretty_named_tys ntys = Pretty.block (Pretty.fbreaks (map pretty_named_type ntys))
        
      fun pretty_llc (ntys,eqns) = Pretty.block [pretty_named_tys ntys, Pretty.fbrk, pretty_eqns eqns]

    end
  \<close>
   
  lemma llc_to_val_eq_triv: "to_val x = a \<Longrightarrow> to_val x = a" by simp

    
  subsection \<open>Isabelle Term Parser\<close>
  text \<open>Parser from Isabelle terms to intermediate representation\<close>
  ML \<open> structure LLC_Compiler = 
    struct
      open LLC_Lib LLC_Intermediate
    
      (* Declare custom names for specific type instances *)
      structure Named_Type_Override = Proof_Data (
        type T = string Typtab.table
        val init = K Typtab.empty
      )
      
      fun add_named_type_override (T,name) ctxt = let
        val tab = Named_Type_Override.get ctxt
      
        val _ = is_monomorphic_type T orelse raise TYPE("Named type override: expected monomorphic type",[T],[])
        val _ = Typtab.defined tab T andalso raise TYPE("Named type override: duplicate override for type",[T],[])
        
        val name' = Name.desymbolize NONE name
        val _ = if name = name' then () else warning ("Named type override: name was desymbolized: " ^ name ^ " -> " ^ name')
      in
        Named_Type_Override.map (Typtab.update_new (T,name')) ctxt
      end
      
      
      
      (* Maps Isabelle type names to named type theorems *)
      structure Named_Type_Tab = Proof_Data (
        type T = (Proof.context -> typ -> string) Symtab.table
        val init = K Symtab.empty
      )

      (* Cache of already created llc-types *)
      structure Type_Cache = Proof_Data (
        type T = (llc_type * llc_type list) option Typtab.table
        val init = K Typtab.empty
      )

      (* Identified Structures: Maps names to field types *)
      structure Identified_Structures = Proof_Data (
        type T = llc_type list Symtab.table
        val init = K Symtab.empty
      )
      
      
      
      
      local
        (* Concatenate type name with argument names, and desymbolize type name.
           assumes argument names already desymbolized.partial_function_mono
        *)
        fun mangle_typename name args = name ^ implode (map (fn s => "_" ^ s) args)
        
      in
        (* Get default name for type *)
        fun dflt_type_name _ (Type (@{type_name word},[T])) = let
              val n = dest_numeralT T
            in
              "i" ^ Int.toString n
            end
          | dflt_type_name ctxt (Type (name,args)) = let
              val argnames = map (get_type_name_dflt ctxt) args
            in 
              mangle_typename (Name.desymbolize NONE name) argnames
            end
          | dflt_type_name _ T = raise TYPE("dflt_type_name: expected type",[T],[])
        
        (* Get name for type, using named type info. *)
        and get_type_name ctxt (T as (Type (name,_))) = (
          case Typtab.lookup (Named_Type_Override.get ctxt) T of
            SOME name => SOME name
          | NONE =>  
              case Symtab.lookup (Named_Type_Tab.get ctxt) name of
                  SOME cr_name => SOME (cr_name ctxt T)
                | NONE => NONE
          )
          | get_type_name _ T = raise TYPE("get_type_name: expected type",[T],[])
        and get_type_name_dflt ctxt T = case get_type_name ctxt T of 
              SOME n => n 
            | NONE => dflt_type_name ctxt T
        
        (* Create named type table. *)
        fun build_named_type_tables ctxt = let
          fun check_pt thm = let
            val (name,typ) = dest_identified_structure_thm thm
            val name = Name.desymbolize NONE name
            val _ = is_Type typ orelse raise TYPE("check_pt: Expected type",[typ],[])
            val (tname,args) = dest_Type typ
            
            val _ = forall is_TVar args orelse raise TYPE("check_pt: Expected simple type",[typ],[])
            
            fun cr_tyname ctxt (Type (_,args)) = map (get_type_name_dflt ctxt) args |> mangle_typename name
              | cr_tyname _ _ = raise Match
          in
            (tname,cr_tyname)
          end
          
          val typtab = Named_Theorems.get ctxt @{named_theorems ll_identified_structures} |> map check_pt |> Symtab.make
        in
          ctxt
          |> Named_Type_Tab.put typtab
        
        end
        
      
      end
      
      fun mk_undefined_ct ctxt T = Const (@{const_name undefined}, T) |> Thm.cterm_of ctxt
      
      fun try_first _ [] = NONE
        | try_first f (x::xs) = case try f x of NONE => try_first f xs | y => y

      fun dest_to_val @{mpat "to_val ?x"} = x 
        | dest_to_val t = raise TERM("dest_to_val",[t])
              
      fun dest_to_val_thm thm = case Thm.prop_of thm of 
        @{mpat "Trueprop (to_val _ = LL_STRUCT ?fs)"} => 
            HOLogic.dest_list fs 
            |> map (fastype_of o dest_to_val)
      | _ => raise THM("Invalid to_val theorem: ",~1,[thm])
        
      
      fun llc_get_type_struct ctxt T = let
        val ts_thms = Named_Theorems.get ctxt @{named_theorems ll_to_val}
        
        val thm = Drule.infer_instantiate' ctxt [SOME (mk_undefined_ct ctxt T)] @{thm llc_to_val_eq_triv}
        val thm = try_first (fn thm2 => thm OF [thm2]) ts_thms
                
        val thm = case thm of 
          NONE => raise TYPE ("Cannot find to_val theorem for type: ",[T],[])
        | SOME thm => thm
      
      in
        dest_to_val_thm thm
      end
      
      (* Lookup already cached type *)
      fun llc_lookup_type _ (Type (@{type_name word},[T])) = SOME (dest_numeralT T |> TInt, [])
        | llc_lookup_type _ (Type (@{type_name single},_)) = SOME (TFloat, [])
        | llc_lookup_type _ (Type (@{type_name double},_)) = SOME (TDouble, [])
        | llc_lookup_type ctxt (Type (@{type_name ptr},[T])) = (case llc_lookup_type ctxt T of
            NONE => NONE
          | SOME (lT,_) => SOME (TPtr lT, []))
        | llc_lookup_type ctxt T = (case Typtab.lookup (Type_Cache.get ctxt) T of
            NONE => NONE | SOME NONE => NONE | SOME x => x)
      
      
      fun llc_parse_type (Type (@{type_name word},[T])) ctxt = (dest_numeralT T |> TInt, ctxt)
        | llc_parse_type (Type (@{type_name single},_)) ctxt = (TFloat, ctxt)
        | llc_parse_type (Type (@{type_name double},_)) ctxt = (TDouble, ctxt)
        | llc_parse_type (Type (@{type_name ptr},[T])) ctxt = llc_parse_type T ctxt |>> TPtr
        | llc_parse_type (T as Type _) ctxt = llc_make_type_inst T ctxt
        | llc_parse_type T _ = raise TYPE ("llc_parse_type: ",[T],[])
      and llc_make_type_inst T ctxt = case Typtab.lookup (Type_Cache.get ctxt) T of
        SOME (SOME (llT,_)) => (llT, ctxt)
      | SOME NONE => raise TYPE ("llc_parse_type: circular type",[T],[])
      | NONE => let
          (* Get structure of type: list of field types *)
          val fTs = llc_get_type_struct ctxt T
          
          (* Get naming of type *)
          val name = get_type_name ctxt T
          
          (* Register type: as anonymous, or with llc_named *)
          fun mk_tycache_entry name = Type_Cache.map (Typtab.update_new (T,map_option (fn x => (TNamed x, [])) name))

          val ctxt = mk_tycache_entry name ctxt
                    
          (* Parse field types *)
          val (llc_fs,ctxt) = fold_map llc_parse_type fTs ctxt
          
          (* Update registry: anonymous: to llc_struct. Named: create Identified_Structures entry *)
          fun register_identified_structure name fs ctxt = let
            val _ = Symtab.defined (Identified_Structures.get ctxt) name andalso error ("Duplicate identified structure name: " ^ name)
          in
            Identified_Structures.map (Symtab.update_new (name,fs)) ctxt
          end
          
          val (res_T,ctxt) = (case name of
              NONE => (TStruct llc_fs, ctxt)
            | SOME name => (TNamed name, register_identified_structure name llc_fs ctxt)
          )

          val ctxt = Type_Cache.map (Typtab.update (T,SOME (res_T, llc_fs))) ctxt
      
        in
          (res_T,ctxt)
        end
      
      
      
      (* TODO/FIXME: Populate with actual instructions! Register them, together with their compilers! *)  
      fun is_llvm_instr name = String.isPrefix "LLVM_Shallow.ll_" name
      fun is_llvm_instr_t (Const (name,_)) = is_llvm_instr name
        | is_llvm_instr_t _ = false
                

      (* M_CONST aware strip_comb *)          
      fun strip_comb_mc t = let 
        fun stripc (t as @{mpat \<open>M_CONST _\<close>},xs) = (t,xs)
          | stripc (f$x, xs) = stripc (f, x::xs)
          | stripc  x =  x
      in  stripc(t,[])  end;
        
      fun analyze_eqn t = let
        val (lhs,rhs) = dest_eqn t
        val (hdc,params) = strip_comb_mc lhs 
      
        val hdc = Envir.beta_eta_contract hdc
        
      in
        ((lhs,(hdc,params)),rhs)
      end

      fun check_eqn t = let 
        val (res as ((_,(hdc,params)),_)) = analyze_eqn t
        val _ = assert_ground_term hdc
        
        val _ = is_llvm_instr_t hdc andalso raise TERM("Code equation for internal LLVM instruction",[t])
        
        val _ = map (fn a => is_Var a orelse raise TERM ("llc_parse_eqn: arguments must be vars",[a])) params
      in res end  
        
            
      val analyze_eqn_thm = analyze_eqn o Thm.prop_of
      val check_eqn_thm = check_eqn o Thm.prop_of
      
      fun compute_fun_names fixes thms = let
        val fixes = map (apfst Envir.beta_eta_contract) fixes
        val _ = map (assert_ground_term o fst) fixes
      
        
        val fixtab = Termtab.make fixes
        (* Pre-populate with fixed names, AND ensure no duplicate fixes *)
        val names = fold (fn (_,n) => Symtab.update_new (n,())) fixes Symtab.empty
        
        fun add_thm thm (ftab,names) = let
          val ((_,(c,_)),_) = check_eqn_thm thm
        in
          if Termtab.defined ftab c then (
            raise TERM ("More than one code equation for constant",[c])
          ) else
          case Termtab.lookup fixtab c of
            SOME n => (Termtab.update_new (c,n) ftab,names)
          | NONE => let
            val n = name_of_head c |> Name.desymbolize NONE
            val (n,names) = unique_variant n names
            val ftab = Termtab.update_new (c,n) ftab
          in
            (ftab,names)
          end
        end
        
        val (ftab,_) = fold add_thm thms (Termtab.empty,names)
      in
        ftab
      end

                
      fun llc_parse_vtype (Type (@{type_name unit},[])) ctxt = (NONE, ctxt)
        | llc_parse_vtype T ctxt = llc_parse_type T ctxt |>> SOME
        
      fun llc_parse_const @{mpat (typs) \<open>init::?'v_T::llvm_rep\<close>} ctxt = llc_parse_type T ctxt |>> (fn T => (T,CInit))
        | llc_parse_const @{mpat (typs) \<open>null::?'v_T::llvm_rep ptr\<close>} ctxt = llc_parse_type T ctxt |>> (fn T => (TPtr T, CNull))
        | llc_parse_const t ctxt = case try dest_word_const t of
            SOME (w,v) => ((TInt w, CInt v), ctxt)
          | NONE => case try dest_float_const t of
              SOME d => ((TFloat,CFloat d),ctxt)
            | NONE => case try dest_double_const t of
                SOME d => ((TDouble,CDouble d),ctxt)
              | NONE => raise TERM ("llc_parse_const",[t])
      
      fun dest_cidx t = let
        val (T,idx) = HOLogic.dest_number t
      in  
        if T = @{typ nat} orelse T = @{typ int} then idx else raise TERM("dest_cidx",[t])
      end    
          
      local    

        type Tstored = (llc_type * string) option list
            
        local
          val env_empty = (Symtab.empty,Termtab.empty,[])
          
          structure LLC_Env = Proof_Data (
            type T = Symtab.set * (llc_type * string) Termtab.table * (llc_type * string) option list   
            fun init _ = env_empty
          )
          
        in

          val env_init = LLC_Env.put env_empty
          val env_save = #3 o LLC_Env.get 
          fun env_restore bnds ctxt = let
            val (syms,params,_) = LLC_Env.get ctxt
            val ctxt = LLC_Env.put (syms,params,bnds) ctxt
          in ctxt end
        
          (* val env_syms = LLC_Env.get #> #1 *)
          val env_params = LLC_Env.get #> #2
          val env_bnds = LLC_Env.get #> #3
                
          fun make_uniqueN n tab name = let
            val name' = if n=0 then name else name ^ Int.toString n
          in
            if Symtab.defined tab name' then
              make_uniqueN (n+1) tab name
            else
              name'
          end
          
          val make_unique = make_uniqueN 0
          
          
          fun env_add_sym name ctxt = let
            val (syms,params,bnds) = LLC_Env.get ctxt
            val name = Name.desymbolize NONE name |> make_unique syms
            val syms = Symtab.insert_set name syms
            val ctxt = LLC_Env.put (syms,params,bnds) ctxt
          in
            (name,ctxt)
          end
          
          fun env_add_bound lty name ctxt = let
            val (name,ctxt) = env_add_sym name ctxt
            val (syms,params,bnds) = LLC_Env.get ctxt
            val bnds = SOME (lty,name)::bnds
            val ctxt = LLC_Env.put (syms,params,bnds) ctxt
          in
            (name,ctxt)
          end
          
          fun env_add_unit_bound ctxt = let
            val (syms,params,bnds) = LLC_Env.get ctxt
            val ctxt = LLC_Env.put (syms,params,NONE::bnds) ctxt
          in
            ctxt
          end
          
          fun env_add_param v ctxt = let
            val (iname,ty) = dest_Var v
            val name = fst iname
            val (lty,ctxt) = llc_parse_type ty ctxt
          
            val (name,ctxt) = env_add_sym name ctxt
            val (syms,params,bnds) = LLC_Env.get ctxt
            val params = Termtab.update_new (v,(lty,name)) params
            val ctxt = LLC_Env.put (syms,params,bnds) ctxt
          in
            ((lty,name),ctxt)
          end
        end

        fun env_lookup_bound ctxt i = case nth (env_bnds ctxt) i of SOME x => x | NONE => raise TERM ("Reference to bound unit variable",[])
        fun env_lookup_param ctxt v = Termtab.lookup (env_params ctxt) v |> the
                
      
        fun env_parse_add_bound T x ctxt = case llc_parse_vtype T ctxt of
          (NONE,ctxt) => (NONE, env_add_unit_bound ctxt)
        | (SOME ty,ctxt) => let
            val (x,ctxt) = env_add_bound ty x ctxt
          in
            (SOME (ty,x),ctxt)
          end  
        
        
      in
      
        fun llc_parse_op (Bound i) ctxt = (env_lookup_bound ctxt i ||> OVar, ctxt)
          | llc_parse_op (t as Var _) ctxt = (env_lookup_param ctxt t ||> OVar, ctxt)
          | llc_parse_op t ctxt = llc_parse_const t ctxt |>> apsnd OConst
      
        fun llc_parse_op' (t as @{mpat \<open>TYPE (_)\<close>}) ctxt = llc_parse_type (Logic.dest_type t) ctxt |>> OOType
          | llc_parse_op' t ctxt = (case try dest_cidx t of 
              SOME idx => (OOCIdx idx, ctxt)
            | NONE => llc_parse_op t ctxt |>> OOOp)
          
        fun llc_parse_op_opt @{mpat "()"} ctxt = (NONE, ctxt)  
          | llc_parse_op_opt t ctxt = llc_parse_op t ctxt |>> SOME
          
        fun llc_parse_op_bool t ctxt = let
          val ((ty,x),ctxt) = llc_parse_op t ctxt
          val _ = ty=TInt 1 orelse raise TERM ("parse_op_bool: not a Boolean",[t])
        in
          ((ty,x), ctxt)
        end  
          
        structure Fun_Tab = Proof_Data (
          type T = string Termtab.table 
          val init = K Termtab.empty
        )
        
        
        fun ftab_lookup ctxt f = let
          val f = Envir.beta_eta_contract f
          val fname = Termtab.lookup (Fun_Tab.get ctxt) f
          val _ = is_none fname andalso raise TYPE("No such function in ftab",[fastype_of f],[f])
          val fname = the fname
        in fname end  

        fun get_llc_type ctxt T = case llc_lookup_type ctxt T of
          SOME (lT,fsT) => (lT,fsT)
        | NONE => raise TYPE("get_llc_type: internal, unregistered type: ",[T],[])  
        
        fun get_field_types ctxt T = get_llc_type ctxt T |> snd
        
        fun check_valid_struct_inst ctxt t pT i fT = let
        
          val i = case try HOLogic.dest_number i of 
              SOME (_,i) => i 
            | NONE => raise TERM("Invalid structure instruction instance, index must be constant",[t])
        
          val fT = get_llc_type ctxt fT |> fst  
          val fTs = get_field_types ctxt pT
          val _ = i < length fTs andalso fT = nth fTs i
            orelse raise TYPE("Invalid structure instruction instance",[fastype_of (head_of t)],[t])
          
          (*val _ = Pretty.block [Pretty.str "Type instance OK ", Syntax.pretty_term ctxt t, Pretty.str " :: ", Syntax.pretty_typ ctxt (fastype_of t) ]
            |> Pretty.string_of |> writeln
          *)  
        in
          ()
        end
        
        fun check_llvm_struct_cmd ctxt (t as @{mpat (typs) \<open>ll_extract_value (_::?'v_pT::llvm_rep) ?i :: ?'v_aT::llvm_rep llM\<close>}) 
            = check_valid_struct_inst ctxt t pT i aT        
        | check_llvm_struct_cmd ctxt (t as @{mpat (typs) \<open>ll_insert_value (_::?'v_pT::llvm_rep) (_ :: ?'v_aT::llvm_rep) ?i\<close>})
            = check_valid_struct_inst ctxt t pT i aT
        (*| check_llvm_struct_cmd ctxt (t as @{mpat (typs) \<open>ll_gep_struct (_::?'v_pT::llvm_rep ptr) ?i :: ?'v_aT::llvm_rep ptr llM\<close>})
            = check_valid_struct_inst ctxt t pT i aT*)
        | check_llvm_struct_cmd _ _ = ()    
                        
        fun llc_parse_fun_name f ctxt = let
          (*val _ = check_valid_head f            
          val cname = name_of_head f
          val _ = is_llvm_instr cname andalso raise TERM("llc_parse_fun_name: expected function name, but got instruction",[f])
          *)
          val fname = ftab_lookup ctxt f
          
          val T = fastype_of f |> body_type |> dest_llM
          val (rty,ctxt) = llc_parse_vtype T ctxt
          
        in
          ((rty,fname),ctxt)
        end
        
        
        fun llc_parse_cmd rty t ctxt = 
          let
            val (f,args) = strip_comb_mc t

          in
            case f of
              Const (@{const_name \<open>llc_if\<close>},_) => (case args of 
                  [arg_cond,arg_then,arg_else] => let
                    val (l_cond, ctxt) = llc_parse_op_bool arg_cond ctxt
                    val (l_then,ctxt) = llc_parse_block arg_then ctxt
                    val (l_else,ctxt) = llc_parse_block arg_else ctxt
                  in
                    (CmIf (l_cond,l_then,l_else), ctxt)
                  end
                | _ => raise TERM ("parse_cmd: If needs 3 arguments",[t])
              )
            | Const (@{const_name \<open>llc_while\<close>},_) => (case args of [@{mpat "\<lambda>_. ?tcond"}, @{mpat "\<lambda>xb. ?tbody"}, arg_inits] => let
                    val (inits,ctxt) = llc_parse_op arg_inits ctxt

                    val env = env_save ctxt
                                        
                    val (sv,ctxt) = env_parse_add_bound xb_T xb ctxt
                    val sv = case sv of NONE => raise TERM ("While with unit-state not yet supported",[t])
                                      | SOME sv => sv
                    
                    val (cond,ctxt) = llc_parse_block tcond ctxt
                    val (body,ctxt) = llc_parse_block tbody ctxt
                    
                    val ctxt = env_restore env ctxt
                    
                  in
                    (CmWhile (sv, cond, body, inits), ctxt)
                  end
                | _ => raise TERM ("parse_cmd: While needs 3 arguments",[t])
              )
            | Const (@{const_name \<open>llc_par\<close>},_) => (case args of
                [arg_f1,arg_f2,arg_x1,arg_x2] => let
                  val ((rty1,fn1),ctxt) = llc_parse_fun_name arg_f1 ctxt
                  val ((rty2,fn2),ctxt) = llc_parse_fun_name arg_f2 ctxt
                  val (op1,ctxt) = llc_parse_op arg_x1 ctxt
                  val (op2,ctxt) = llc_parse_op arg_x2 ctxt
                in
                  case (rty1,rty2) of
                    (SOME ty1,SOME ty2) => (CmPar (ty1,fn1,op1,ty2,fn2,op2),ctxt)
                  | _ => raise TERM("parse_cmd: llc_par expects two non-void one-argument functions",[t])
                      
                
                end
              | _ => raise TERM("parse_cmd: llc_par needs 4 arguments",[t])
              )
            | _ => 
                if is_llvm_instr_t f then let 
                    val (cname,_) = dest_Const f
                    val (ops,ctxt) = fold_map llc_parse_op' args ctxt
                    val _ = check_llvm_struct_cmd ctxt t
                  in (CmInstr (cname,ops), ctxt) end
                else let 
                    val (ops,ctxt) = fold_map llc_parse_op args ctxt
                    val fname = ftab_lookup ctxt f
                  in (CmCall (rty, fname ,ops), ctxt) end
                   
          end
        and llc_parse_block @{mpat "Mbind ?m (\<lambda>x. ?f)"} ctxt = 
          let 
            val (rty,ctxt) = llc_parse_vtype x_T ctxt
            val (cmd, ctxt) = llc_parse_cmd rty m ctxt
            val env = env_save ctxt
            val (sv,ctxt) = env_parse_add_bound x_T x ctxt
            val (blk,ctxt) = llc_parse_block f ctxt
            val ctxt = env_restore env ctxt
          in
            (BlBind (sv,cmd,blk),ctxt)
          end
          | llc_parse_block @{mpat "Mreturn ()"} ctxt = (BlReturn NONE, ctxt)
          | llc_parse_block @{mpat "Mreturn ?x"} ctxt = llc_parse_op x ctxt |>> SOME |>> BlReturn
          | llc_parse_block t _ = raise TERM ("llc_parse_block: structural error",[t])
         
          
        fun llc_parse_eqn t ctxt = let
        
          fun aux () = let
            val ((lhs,(hdc,params)),rhs) = check_eqn t
          
            val fname = ftab_lookup ctxt hdc 
            
            val ctxt = env_init ctxt
                      
            val (params,ctxt) = fold_map env_add_param params ctxt
            val (blk,ctxt) = llc_parse_block rhs ctxt
            
            val (rlty, ctxt) = llc_parse_vtype (dest_llM (fastype_of lhs)) ctxt
  
            (* Erase meaningless environment after equation has been parsed! *)
            val ctxt = env_init ctxt 
          in
            (EQN (rlty,fname,params,blk), ctxt)
          end
          
          fun msg () = Pretty.block [Pretty.str "From ", Syntax.pretty_term ctxt t] |> Pretty.string_of
          
        in
          trace_exn msg aux ()
        end
          
          
      end      
      
      fun parse_cthms_aux thms ctxt = fold_map (llc_parse_eqn o Thm.prop_of) thms ctxt
      
      fun parse_cthms fixes nt_ovr thms ctxt = let
        val ftab = compute_fun_names fixes thms      
      
        val ctxt = Fun_Tab.put ftab ctxt
        
        val ctxt = fold add_named_type_override nt_ovr ctxt
        
        val (eqns,ctxt) = parse_cthms_aux thms (build_named_type_tables ctxt)
        
        val named_tys = Identified_Structures.get ctxt |> Symtab.dest |> map Named_Type
      in 
        (named_tys,eqns)
      end
     
    end
    
  \<close>  

  subsection \<open>LLVM Writer\<close>
  
  text \<open>LLVM Builder. Interface to build actual LLVM text.\<close>
  ML_file "par_wrapper.tmpl.ml"
  ML_file "LLVM_Builder.ml"
  
  text \<open>Compiler from intermediate representation to actual LLVM text.\<close>
  ML \<open> structure LLC_Backend = 
    struct
      open LLC_Lib LLC_Intermediate
    
      type vtab = LLVM_Builder.value Symtab.table
      type builder = vtab -> LLVM_Builder.regname -> llc_topr' list -> Proof.context -> LLVM_Builder.T -> LLVM_Builder.value option
    
      fun llc_ty _ (TInt w) = LLVM_Builder.mkty_i w
        | llc_ty _ (TFloat) = LLVM_Builder.mkty_float
        | llc_ty _ (TDouble) = LLVM_Builder.mkty_double
        | llc_ty b (TPtr ty) = LLVM_Builder.mkty_ptr (llc_ty b ty)
        | llc_ty b (TStruct tys) = LLVM_Builder.mkty_struct (map (llc_ty b) tys)
        | llc_ty b (TNamed name) = LLVM_Builder.mkty_named b name
      
      
      fun llc_const_to_val b ty CInit = LLVM_Builder.mkc_zeroinit (llc_ty b ty)
        | llc_const_to_val b ty (CInt v) = LLVM_Builder.mkc_i (llc_ty b ty) v
        | llc_const_to_val b ty (CFloat v) = LLVM_Builder.mkc_f (llc_ty b ty) v
        | llc_const_to_val b ty (CDouble v) = LLVM_Builder.mkc_d (llc_ty b ty) v
        | llc_const_to_val b ty (CNull) = LLVM_Builder.mkc_null (llc_ty b ty)
      
      fun llc_op_to_val _ vtab (_,OVar x) = the_assert ("Variable not in vtab " ^ x) (Symtab.lookup vtab x)
        | llc_op_to_val b _ (ty,OConst c) = llc_const_to_val b ty c
        

      fun llc_op'_to_val b vtab (OOOp x) = llc_op_to_val b vtab x  
        | llc_op'_to_val _ _ t = raise Fail ("llc_op'_to_val: Expected value operand: " ^ (LLC_Intermediate.pretty_topr' t |> Pretty.string_of))
              
      fun dstreg NONE = NONE | dstreg (SOME s) = SOME s
        
      fun unsuffix_float_instr s = 
        if String.isSuffix "_d" s then unsuffix "_d" s
        else if String.isSuffix "_f" s then unsuffix "_f" s
        else raise Fail("Expected floating point suffixed operation [_d,_f]: " ^ s)
      
      
      fun arith_instr_builder iname vtab dst [OOOp x1, OOOp x2] _ b = (
        LLVM_Builder.mk_arith_instr iname b dst (llc_op_to_val b vtab x1) (llc_op_to_val b vtab x2) |> SOME
      ) | arith_instr_builder _ _ _ _ _ _ = raise Fail "arith_instr_builder: invalid arguments"

      fun farith_instr_builder iname vtab dst [OOOp x1, OOOp x2] _ b = (
        LLVM_Builder.mk_arith_instr (unsuffix_float_instr iname) b dst (llc_op_to_val b vtab x1) (llc_op_to_val b vtab x2) |> SOME
      ) | farith_instr_builder _ _ _ _ _ _ = raise Fail "farith_instr_builder: invalid arguments"
            
      fun icmp_instr_builder cmpcode vtab dst [OOOp x1, OOOp x2] _ b = (
        LLVM_Builder.mk_icmp_instr cmpcode b dst (llc_op_to_val b vtab x1) (llc_op_to_val b vtab x2) |> SOME
      ) | icmp_instr_builder _ _ _ _ _ _ = raise Fail "icmp_instr_builder: invalid arguments"

      fun fcmp_instr_builder cmpcode vtab dst [OOOp x1, OOOp x2] _ b = (
        LLVM_Builder.mk_fcmp_instr (unsuffix_float_instr cmpcode) b dst (llc_op_to_val b vtab x1) (llc_op_to_val b vtab x2) |> SOME
      ) | fcmp_instr_builder _ _ _ _ _ _ = raise Fail "fcmp_instr_builder: invalid arguments"
      
      fun ptrcmp_instr_builder cmpcode vtab dst [OOOp x1, OOOp x2] _ b = (
        LLVM_Builder.mk_ptrcmp_instr cmpcode b dst (llc_op_to_val b vtab x1) (llc_op_to_val b vtab x2) |> SOME
      ) | ptrcmp_instr_builder _ _ _ _ _ _ = raise Fail "icmp_instr_builder: invalid arguments"
            
      fun conv_instr_builder cmpcode vtab dst [OOOp x1, OOType ty] _ b = (
        LLVM_Builder.mk_conv_instr cmpcode b dst (llc_op_to_val b vtab x1) (llc_ty b ty) |> SOME
      ) | conv_instr_builder _ _ _ _ _ _ = raise Fail "conv_instr_builder: invalid arguments"

      
      fun extract_value_builder vtab dst [OOOp x1, OOCIdx idx] _ b = (
        LLVM_Builder.mk_extractvalue b dst (llc_op_to_val b vtab x1) idx |> SOME
      ) | extract_value_builder _ _ _ _ _ = raise Fail "extract_value_builder: invalid arguments"

      fun insert_value_builder vtab dst [OOOp x1, OOOp x2, OOCIdx idx] _ b = (
        LLVM_Builder.mk_insertvalue b dst (llc_op_to_val b vtab x1) (llc_op_to_val b vtab x2) idx |> SOME
      ) | insert_value_builder _ _ _ _ _ = raise Fail "insert_value_builder: invalid arguments"
      
      fun malloc_builder vtab dst [OOType ty, OOOp x] _ b = (
        LLVM_Builder.mk_malloc b dst (llc_ty b ty) (llc_op_to_val b vtab x) |> SOME
      ) | malloc_builder _ _ _ _ _ = raise Fail "malloc_builder: invalid arguments"
            
      fun free_builder vtab _ [OOOp x] _ b = (
        LLVM_Builder.mk_free b (llc_op_to_val b vtab x); NONE
      ) | free_builder _ _ _ _ _ = raise Fail "free_builder: invalid arguments"

      fun load_builder vtab dst [OOOp x] _ b = (
        LLVM_Builder.mk_load b dst (llc_op_to_val b vtab x) |> SOME
      ) | load_builder _ _ _ _ _ = raise Fail "load_builder: invalid arguments"
      
      fun store_builder vtab _ [OOOp x1, OOOp x2] _ b = (
        LLVM_Builder.mk_store b (llc_op_to_val b vtab x1) (llc_op_to_val b vtab x2); NONE
      ) | store_builder _ _ _ _ _ = raise Fail "store_builder: invalid arguments"

      fun ofs_ptr_builder vtab dst [OOOp x1, OOOp x2] _ b = (
        LLVM_Builder.mk_ofs_ptr b dst (llc_op_to_val b vtab x1) (llc_op_to_val b vtab x2) |> SOME
      ) | ofs_ptr_builder _ _ _ _ _ = raise Fail "ofs_ptr_builder: invalid arguments"
      
      fun gep_idx_builder vtab dst [OOOp x1, OOCIdx idx] _ b = (
        LLVM_Builder.mk_gep_idx b dst (llc_op_to_val b vtab x1) (LLVM_Builder.mkc_iw 32 idx) |> SOME
      ) | gep_idx_builder _ _ _ _ _ = raise Fail "gep_idx_builder: invalid arguments"

      
      fun intrinsic_builder rty name vtab dst args _ b = let
        val args = map (llc_op'_to_val b vtab) args
        val res = LLVM_Builder.mk_external_call b dst rty name args
      in SOME res end
      
      local open LLVM_Builder in
        val ll_t_2xdouble = mkty_vector 2 mkty_double
        val ll_zeroinit_2xdouble = mkc_zeroinit ll_t_2xdouble
        val ll_t_4xfloat = mkty_vector 4 mkty_float
        val ll_zeroinit_4xfloat = mkc_zeroinit ll_t_4xfloat
      end
      
      fun llc_to_vector_2xdouble_sd b x = LLVM_Builder.mk_insertelement b (SOME "mmx_") ll_zeroinit_2xdouble x (LLVM_Builder.mkc_iw 64 0)
      fun llc_from_vector_2xdouble_sd b dst x = LLVM_Builder.mk_extractelement b dst x (LLVM_Builder.mkc_iw 64 0)

      fun llc_to_vector_4xfloat_ss b x = LLVM_Builder.mk_insertelement b (SOME "mmx_") ll_zeroinit_4xfloat x (LLVM_Builder.mkc_iw 32 0)
      fun llc_from_vector_4xfloat_ss b dst x = LLVM_Builder.mk_extractelement b dst x (LLVM_Builder.mkc_iw 32 0)
      
      fun assert_avx512f ctxt = Config.get ctxt llc_compile_avx512f orelse
                raise Fail "AVX512f support is experimental and disabled! Declare [[llc_compile_avx512f=true]] to enable!"
                  
      fun llc_op_to_2xdouble_sd b vtab = llc_op_to_val b vtab #> llc_to_vector_2xdouble_sd b          
      fun llc_op'_to_2xdouble_sd b vtab = llc_op'_to_val b vtab #> llc_to_vector_2xdouble_sd b          

      fun llc_op_to_4xfloat_ss b vtab = llc_op_to_val b vtab #> llc_to_vector_4xfloat_ss b          
      fun llc_op'_to_4xfloat_ss b vtab = llc_op'_to_val b vtab #> llc_to_vector_4xfloat_ss b          
                      
      (* {add, sub, mul, div} r x1 x2 \<rightarrow> llvm.x86.avx512.mask.XXX.sd.round x1 x2 0 -1 r *)
      fun avx512_asmd_sd_round_intrinsic_builder iname vtab dst [OOCIdx rounding, OOOp x1, OOOp x2] ctxt b = let
        val _ = assert_avx512f ctxt
        
        val iname = unsuffix "_sd_round" iname
        val iname = "llvm.x86.avx512.mask."^iname^".sd.round"

        val rounding = LLVM_Builder.mkc_iw 32 rounding
        val mask = LLVM_Builder.mkc_iw 8 ~1
        
        val cop = llc_op_to_2xdouble_sd b vtab
        
        val args = [cop x1, cop x2, ll_zeroinit_2xdouble, mask, rounding]
        val attrs = [ [],    [],       [],                 [],  ["immarg"] ]
        
        val res = LLVM_Builder.mk_external_call_attrs b (SOME "mmx_") ll_t_2xdouble iname args attrs
          |> llc_from_vector_2xdouble_sd b dst
                
      in
        SOME res
      end
      | avx512_asmd_sd_round_intrinsic_builder _ _ _ _ _ _ = raise Fail "avx512_asmd_sd_round_intrinsic_builder: invalid arguments"
      
      (* sqrt r x \<rightarrow> llvm.x86.avx512.mask.sqrt.sd x x 0 -1 r   *)
      fun avx512_sqrt_sd_round_intrinsic_builder vtab dst [OOCIdx rounding, OOOp x] ctxt b = let
        val _ = assert_avx512f ctxt
        
        val iname = "llvm.x86.avx512.mask.sqrt.sd"
        val x = llc_op_to_2xdouble_sd b vtab x
        val mask = LLVM_Builder.mkc_iw 8 ~1
        val rounding = LLVM_Builder.mkc_iw 32 rounding

        val args = [x,x,ll_zeroinit_2xdouble, mask, rounding]      
        val attrs = [ [],[],[],[],["immarg"] ]

        val res = LLVM_Builder.mk_external_call_attrs b (SOME "mmx_") ll_t_2xdouble iname args attrs
          |> llc_from_vector_2xdouble_sd b dst
              
      in
        SOME res
      end
      | avx512_sqrt_sd_round_intrinsic_builder _ _ _ _ _ = raise Fail "avx512_sqrt_sd_round_intrinsic_builder: invalid arguments"

      (* fmadd r x1 x2 x3 \<rightarrow> llvm.x86.avx512.vfmadd.f64 x1 x2 x3 r *)      
      fun avx512_vfmadd_f64_builder vtab dst [OOCIdx rounding, OOOp x1, OOOp x2, OOOp x3] ctxt b = let
        val _ = assert_avx512f ctxt

        val iname = "llvm.x86.avx512.vfmadd.f64"

        val cop = llc_op_to_val b vtab
        val rounding = LLVM_Builder.mkc_iw 32 rounding
        val args = map cop [x1,x2,x3] @ [rounding]
        val attrs = [ [],[],[],["immarg"] ]
        
        val res = LLVM_Builder.mk_external_call_attrs b dst LLVM_Builder.mkty_double iname args attrs
      in
        SOME res
      end
      | avx512_vfmadd_f64_builder _ _ _ _ _ = raise Fail "avx512_vfmadd_f64_builder: invalid arguments"
      

      (* {add, sub, mul, div} r x1 x2 \<rightarrow> llvm.x86.avx512.mask.XXX.ss.round x1 x2 0 -1 r *)
      fun avx512_asmd_ss_round_intrinsic_builder iname vtab dst [OOCIdx rounding, OOOp x1, OOOp x2] ctxt b = let
        val _ = assert_avx512f ctxt
        
        val iname = unsuffix "_ss_round" iname
        val iname = "llvm.x86.avx512.mask."^iname^".ss.round"

        val rounding = LLVM_Builder.mkc_iw 32 rounding
        val mask = LLVM_Builder.mkc_iw 8 ~1
        
        val cop = llc_op_to_4xfloat_ss b vtab
        
        val args = [cop x1, cop x2, ll_zeroinit_2xdouble, mask, rounding]
        val attrs = [ [],    [],       [],                 [],  ["immarg"] ]
        
        val res = LLVM_Builder.mk_external_call_attrs b (SOME "mmx_") ll_t_4xfloat iname args attrs
          |> llc_from_vector_4xfloat_ss b dst
                
      in
        SOME res
      end
      | avx512_asmd_ss_round_intrinsic_builder _ _ _ _ _ _ = raise Fail "avx512_asmd_ss_round_intrinsic_builder: invalid arguments"
      
      (* sqrt r x \<rightarrow> llvm.x86.avx512.mask.sqrt.ss x x 0 -1 r   *)
      fun avx512_sqrt_ss_round_intrinsic_builder vtab dst [OOCIdx rounding, OOOp x] ctxt b = let
        val _ = assert_avx512f ctxt
        
        val iname = "llvm.x86.avx512.mask.sqrt.ss"
        val x = llc_op_to_4xfloat_ss b vtab x
        val mask = LLVM_Builder.mkc_iw 8 ~1
        val rounding = LLVM_Builder.mkc_iw 32 rounding

        val args = [x,x,ll_zeroinit_4xfloat, mask, rounding]      
        val attrs = [ [],[],[],[],["immarg"] ]

        val res = LLVM_Builder.mk_external_call_attrs b (SOME "mmx_") ll_t_4xfloat iname args attrs
          |> llc_from_vector_4xfloat_ss b dst
              
      in
        SOME res
      end
      | avx512_sqrt_ss_round_intrinsic_builder _ _ _ _ _ = raise Fail "avx512_sqrt_ss_round_intrinsic_builder: invalid arguments"

      (* fmadd r x1 x2 x3 \<rightarrow> llvm.x86.avx512.vfmadd.f32 x1 x2 x3 r *)      
      fun avx512_vfmadd_f32_builder vtab dst [OOCIdx rounding, OOOp x1, OOOp x2, OOOp x3] ctxt b = let
        val _ = assert_avx512f ctxt

        val iname = "llvm.x86.avx512.vfmadd.f32"

        val cop = llc_op_to_val b vtab
        val rounding = LLVM_Builder.mkc_iw 32 rounding
        val args = map cop [x1,x2,x3] @ [rounding]
        val attrs = [ [],[],[],["immarg"] ]
        
        val res = LLVM_Builder.mk_external_call_attrs b dst LLVM_Builder.mkty_float iname args attrs
      in
        SOME res
      end
      | avx512_vfmadd_f32_builder _ _ _ _ _ = raise Fail "avx512_vfmadd_f32_builder: invalid arguments"
      
      
                  
      fun register_builder (b:builder) (n:string) = Symtab.update_new (n,b)
      
      fun register_prfx_builder prfx b n = let
        val iname = Long_Name.base_name n |> unprefix prfx
      in
        register_builder (b iname) n
      end

      val builders = Symtab.empty
        |> fold (register_prfx_builder "ll_" arith_instr_builder) 
          [@{const_name ll_add}, @{const_name ll_sub}, @{const_name ll_mul},
           @{const_name ll_udiv}, @{const_name ll_urem}, @{const_name ll_sdiv}, @{const_name ll_srem},
           @{const_name ll_shl}, @{const_name ll_lshr}, @{const_name ll_ashr},
           @{const_name ll_and}, @{const_name ll_or}, @{const_name ll_xor}
          ]
        |> fold (register_prfx_builder "ll_" farith_instr_builder) 
          [
           @{const_name ll_fadd_d}, @{const_name ll_fsub_d}, @{const_name ll_fmul_d}, @{const_name ll_fdiv_d}, @{const_name ll_frem_d},
           @{const_name ll_fadd_f}, @{const_name ll_fsub_f}, @{const_name ll_fmul_f}, @{const_name ll_fdiv_f}, @{const_name ll_frem_f}
          ]
        |> fold (register_prfx_builder "ll_" conv_instr_builder) [
             @{const_name ll_trunc}, @{const_name ll_sext}, @{const_name ll_zext}
          ]  
        |> fold (register_prfx_builder "ll_icmp_" icmp_instr_builder) [
             @{const_name ll_icmp_eq}, @{const_name ll_icmp_ne}, 
             @{const_name ll_icmp_slt}, @{const_name ll_icmp_sle}, 
             @{const_name ll_icmp_ult}, @{const_name ll_icmp_ule} 
          ]  
        |> fold (register_prfx_builder "ll_fcmp_" fcmp_instr_builder) [
             @{const_name ll_fcmp_oeq_d}, @{const_name ll_fcmp_one_d}, 
             @{const_name ll_fcmp_olt_d}, @{const_name ll_fcmp_ogt_d}, 
             @{const_name ll_fcmp_ole_d}, @{const_name ll_fcmp_oge_d}, 
             @{const_name ll_fcmp_ord_d},                                         
             @{const_name ll_fcmp_ueq_d}, @{const_name ll_fcmp_une_d}, 
             @{const_name ll_fcmp_ult_d}, @{const_name ll_fcmp_ugt_d}, 
             @{const_name ll_fcmp_ule_d}, @{const_name ll_fcmp_uge_d}, 
             @{const_name ll_fcmp_uno_d},
             
             @{const_name ll_fcmp_oeq_f}, @{const_name ll_fcmp_one_f}, 
             @{const_name ll_fcmp_olt_f}, @{const_name ll_fcmp_ogt_f}, 
             @{const_name ll_fcmp_ole_f}, @{const_name ll_fcmp_oge_f}, 
             @{const_name ll_fcmp_ord_f},
             @{const_name ll_fcmp_ueq_f}, @{const_name ll_fcmp_une_f}, 
             @{const_name ll_fcmp_ult_f}, @{const_name ll_fcmp_ugt_f}, 
             @{const_name ll_fcmp_ule_f}, @{const_name ll_fcmp_uge_f}, 
             @{const_name ll_fcmp_uno_f}
          ]  
        |> fold (register_prfx_builder "ll_ptrcmp_" ptrcmp_instr_builder) [
             @{const_name ll_ptrcmp_eq}, @{const_name ll_ptrcmp_ne}
          ]  
        |> register_builder (extract_value_builder) @{const_name ll_extract_value}          
        |> register_builder (insert_value_builder) @{const_name ll_insert_value}          

        |> register_builder (malloc_builder) @{const_name ll_malloc}          
        |> register_builder (free_builder) @{const_name ll_free}          
        |> register_builder (load_builder) @{const_name ll_load}          
        |> register_builder (store_builder) @{const_name ll_store}          
      
        |> register_builder (ofs_ptr_builder) @{const_name ll_ofs_ptr}          
        (*|> register_builder (gep_idx_builder) @{const_name ll_gep_struct}          *)
        
        |> register_builder (intrinsic_builder LLVM_Builder.mkty_double "llvm.sqrt.f64") @{const_name ll_sqrt_f64}
        |> register_builder (intrinsic_builder LLVM_Builder.mkty_float "llvm.sqrt.f32") @{const_name ll_sqrt_f32}
        
        |> fold (register_prfx_builder "ll_x86_avx512_" avx512_asmd_sd_round_intrinsic_builder) [
              @{const_name ll_x86_avx512_add_sd_round},
              @{const_name ll_x86_avx512_sub_sd_round},
              @{const_name ll_x86_avx512_mul_sd_round},
              @{const_name ll_x86_avx512_div_sd_round}
          ]
        |> register_builder (avx512_sqrt_sd_round_intrinsic_builder) @{const_name ll_x86_avx512_sqrt_sd}
        |> register_builder (avx512_vfmadd_f64_builder) @{const_name ll_x86_avx512_vfmadd_f64}
        
        |> fold (register_prfx_builder "ll_x86_avx512_" avx512_asmd_ss_round_intrinsic_builder) [
              @{const_name ll_x86_avx512_add_ss_round},
              @{const_name ll_x86_avx512_sub_ss_round},
              @{const_name ll_x86_avx512_mul_ss_round},
              @{const_name ll_x86_avx512_div_ss_round}
          ]
        |> register_builder (avx512_sqrt_ss_round_intrinsic_builder) @{const_name ll_x86_avx512_sqrt_ss}
        |> register_builder (avx512_vfmadd_f32_builder) @{const_name ll_x86_avx512_vfmadd_f32}
            

      fun vtab_bind (SOME dst) (SOME v) vtab = Symtab.update_new (dst,v) vtab  
        | vtab_bind (SOME dst) NONE _ = raise Fail ("Void instruction bound to value (" ^ dst ^ ") ")
        | vtab_bind _ _ vtab = vtab
        
      fun build_instr ctxt b vtab dst (iname,args) = let
        val bld = Symtab.lookup builders iname 
          |> the_assert ("Unknown instruction " ^ iname)
          
        val v = bld vtab (dstreg dst) args ctxt b
      in
        vtab_bind dst v vtab
      end  
      
      fun build_call _ b vtab dst (rty,pname,args) = let
        val args = map (llc_op_to_val b vtab) args
        val rty = map_option (llc_ty b) rty
        
        val v = case rty of 
          NONE => (LLVM_Builder.mk_call_void b pname args; NONE)
        | SOME rty => LLVM_Builder.mk_call b (dstreg dst) rty pname args |> SOME

      in
        vtab_bind dst v vtab
      end

      fun build_par_call ctxt b vtab dst (rty1,pname1,arg1,rty2,pname2,arg2) = let
        val _ = Config.get ctxt llc_compile_par_call orelse
                raise Fail "Parallel call is experimental and disabled! Declare [[llc_compile_par_call=true]] to enable!"
      
        val arg1 = llc_op_to_val b vtab arg1
        val arg2 = llc_op_to_val b vtab arg2
        val rty1 = llc_ty b rty1
        val rty2 = llc_ty b rty2
        
        val v = LLVM_Builder.mk_par_call b (dstreg dst) rty1 pname1 arg1 rty2 pname2 arg2
          |> SOME

      in
        vtab_bind dst v vtab
      end
      
      
            
      fun build_if build_block ctxt b vtab dst (op_cond, blk_then, blk_else) = let
        val l_then = LLVM_Builder.variant_label b "then"
        val l_else = LLVM_Builder.variant_label b "else"
        val l_ctd_if = LLVM_Builder.variant_label b "ctd_if"
      
        val _ = LLVM_Builder.mk_cbr b (llc_op_to_val b vtab op_cond) l_then l_else
        
        val _ = LLVM_Builder.open_bb b l_then 
        val r_then = build_block ctxt b vtab blk_then
        val l_then' = LLVM_Builder.mk_br b l_ctd_if
        
        val _ = LLVM_Builder.open_bb b l_else
        val r_else = build_block ctxt b vtab blk_else
        val l_else' = LLVM_Builder.mk_br b l_ctd_if
        
        val _ = LLVM_Builder.open_bb b l_ctd_if
        val res = case (r_then, r_else) of
          (NONE,NONE) => NONE
        | (SOME r_then, SOME r_else) => 
            SOME (LLVM_Builder.mk_phi' b (dstreg dst) [(r_then,l_then'), (r_else,l_else')])
        | _ => raise Fail ("If type mismatch (void/non-void)")
      in
        vtab_bind dst res vtab
      end
      
      (*
        "while [x] cond body s" is compiled to
      
        br start (in l_this)
        
        start:
          %s = Phi (l_this,%s) (l_body',%s')
          %b = \<lbrakk>cond\<rbrakk>(x\<mapsto>%s)
          cbr %b body end
      
        body:
          %s' = \<lbrakk>body\<rbrakk>(x\<mapsto>%s)
          br start (in l_body')
          
        end:
          (returns %s)

      *)
      fun build_while build_block ctxt b vtab dst (sv, blk_cond, blk_body, op_init) = let
      
        val _ = Config.get ctxt llc_compile_while orelse
                raise Fail "Direct while compilation disabled! Declare [[llc_compile_while=true]] to enable!"
      
        val l_start = LLVM_Builder.variant_label b "while_start"
        val l_body = LLVM_Builder.variant_label b "while_body"
        val l_end = LLVM_Builder.variant_label b "while_end"
        
        val v_init = llc_op_to_val b vtab op_init
        val l_this = LLVM_Builder.mk_br b l_start

        val (s_ty,sname) = apfst (llc_ty b) sv
        
        (* start: *)
        val _ = LLVM_Builder.open_bb b l_start
        
        (* s = \<Phi> [v_init,this] [\<dots>] *)
        val (phi_handle,v_state) = LLVM_Builder.mk_phi b s_ty (SOME sname)
        val _ = LLVM_Builder.phi_add b phi_handle (v_init, l_this)
        val vtab' = vtab_bind (SOME sname) (SOME v_state) vtab
        
        (* cond *)
        val r_cond = build_block ctxt b vtab' blk_cond
        val r_cond = case r_cond of SOME x => x | NONE => raise Fail "While (bug): Cond-block with no result"
        
        (* cbr r_cond body end *)
        val _ = LLVM_Builder.mk_cbr b r_cond l_body l_end
        
        (* body: *)
        val _ = LLVM_Builder.open_bb b l_body
        val r_body = build_block ctxt b vtab' blk_body
        val r_body = case r_body of SOME x => x | NONE => raise Fail "While (bug): Body-block with no result"
        val l_body' = LLVM_Builder.mk_br b l_start
        
        (* add [r_body,l_body'] to \<Phi>-node of l_start *)
        val _ = LLVM_Builder.phi_add b phi_handle (r_body,l_body')
        
        val _ = LLVM_Builder.open_bb b l_end
      in
        vtab_bind dst (SOME v_state) vtab
      end
      
      fun build_cmd ctxt b vtab dst (CmInstr ia) = build_instr ctxt b vtab dst ia
        | build_cmd ctxt b vtab dst (CmCall na) = build_call ctxt b vtab dst na
        | build_cmd ctxt b vtab dst (CmIf bte) = build_if build_block ctxt b vtab dst bte
        | build_cmd ctxt b vtab dst (CmWhile cbi) = build_while build_block ctxt b vtab dst cbi
        | build_cmd ctxt b vtab dst (CmPar na) = build_par_call ctxt b vtab dst na
            
      and build_block ctxt b vtab (BlBind (dst,cmd,blk)) = let
            val dst = map_option snd dst
            val vtab = build_cmd ctxt b vtab dst cmd
          in
            build_block ctxt b vtab blk
          end
        | build_block _ b vtab (BlReturn x) = map_option (llc_op_to_val b vtab) x
              
        
        
      fun build_eqn ctxt b (EQN (rty, pname, params, blk)) = let
        val params = map (apfst (llc_ty b)) params
        val rty = map_option (llc_ty b) rty
        
        val paramsv = LLVM_Builder.open_proc b rty pname params
        
        val vtab = fold (Symtab.update_new o apfst snd) (params ~~ paramsv) Symtab.empty
        
        val retv = build_block ctxt b vtab blk
        
        val _ = LLVM_Builder.mk_return b retv
        val _ = LLVM_Builder.close_proc b
      in
        ()
      end

      fun build_named_ty b (Named_Type (name,ftys)) = let
        val ltys = map (llc_ty b) ftys
        val sty = LLVM_Builder.mkty_struct ltys
      in
        LLVM_Builder.decl_named_ty b name sty
      end
          
      fun compile_to_llvm ctxt (tys,eqns) = let
        val b = LLVM_Builder.builder ()
        (* val _ = LLVM_Builder.set_dbg_trace b true *)
        val _ = map (build_named_ty b) tys
        val _ = map (build_eqn ctxt b) eqns
        val res = LLVM_Builder.string_of b
      in
        res
      end
      
    end
       
  \<close>  

  ML \<open> structure Simple_PP = struct
    datatype T = Empty | Word of string | NWord of string | Space of bool | Newline of bool | Block of int * T list

    datatype last_tk = NL | WR | NW | SP (* Newline | word | nonword | space *)
    
    type state = int * last_tk  (* indentation, last token *)
    
    val init_state = (0,NL)

    val indentS = "  "
    val spaceS = " "
    val newlineS = "\n"
    
    fun indentation i = implode (replicate i indentS)
    
    fun string_of' (Word kw) (i,NL) = (indentation i ^ kw, (i,WR))
      | string_of' (Word kw) (i,WR) = (spaceS ^ kw, (i,WR))
      | string_of' (Word kw) (i,NW) = (kw, (i,WR))
      | string_of' (Word kw) (i,SP) = (kw, (i,WR))
      
      | string_of' (NWord c) (i,NL) = (indentation i ^ c, (i,NW))
      | string_of' (NWord c) (i,WR) = (c, (i,NW))
      | string_of' (NWord c) (i,NW) = (c, (i,NW))
      | string_of' (NWord c) (i,SP) = (c, (i,NW))
      
      | string_of' (Newline true) (i,_) = (newlineS, (i,NL))
      | string_of' (Newline false) (i,NL) = ("", (i,NL))
      | string_of' (Newline false) (i,_) = (newlineS, (i,NL))
      
      | string_of' (Space true) (i,_) = (spaceS, (i,SP))
      | string_of' (Space false) (i,NL) = ("", (i,SP))
      | string_of' (Space false) (i,SP) = ("", (i,SP))
      | string_of' (Space false) (i,_) = (spaceS, (i,SP))
      
      | string_of' (Empty) (i,ltk) = ("", (i,ltk))
      
      | string_of' (Block (ii,tks)) (i,lt) = let 
          val (strs,(_,lt)) = fold_map string_of' tks (i+ii,lt)
          val str = implode strs
        in (str,(i,lt)) end
      
    (* User Interface *)    
    fun string_of tk = string_of' tk init_state |> fst
            
    (* Basic Functions *)
    val empty = Empty
    val word = Word
    val nword = NWord
    val brk = Newline false
    val fbrk = Newline true
    val sep = Space false
    val fsep = Space true
    
    fun block_indent i tks = Block (i,tks)
    val block = block_indent 0
    
    (* Derived Functions *)
    
    fun enclose_indent i lpar rpar prt = block_indent i ([nword lpar,prt,nword rpar])

    fun line prts = block (prts@[fbrk])
    
    val enclose = enclose_indent 0
    val paren = enclose "(" ")"
    val braces = enclose "{" "}"
    
    fun big_block lpar rpar prts = block [block_indent 1 (nword lpar::brk::prts),brk,nword rpar]
    val big_braces = big_block "{" "}"
    
    fun separate sep prts = block (Library.separate sep prts)
    val commas = separate (nword ",")
    val brks = separate brk
    val fbrks = separate fbrk

    fun list sep lpar rpar prts = enclose lpar rpar (separate sep prts)
    val parlist = list (nword ", ") "(" ")"
        
    (* enclose, enclose_indent, separate, ... *)
  
  end
  \<close>
  
  ML \<open>structure Parser_Util = struct
    fun scan_if_then_else scan1 scan2 scan3 xs = let
      val r = SOME (Scan.catch scan1 xs) handle Fail _ => NONE
    in
      case r of 
        NONE => scan3 xs
      | SOME (a,xs) => scan2 a xs
    end
    

    (* Choices, where first parser's success commits to this choice *)  
    infixr 0 |||

    fun (g,p) ||| e = scan_if_then_else g p e
        
    fun lastg (g,p) = g :|-- p
  
    val pkw = Parse.keyword_markup (true,Markup.keyword1)
    val pcm = Parse.keyword_markup (true,Markup.keyword2)

    
    fun parse_inner kws p ctxt src = let
      val s = src |> apfst cartouche |> Symbol_Pos.explode |> Symbol_Pos.cartouche_content
      val kws = kws |> map (fn x => ((x,Position.none),Keyword.no_spec))
      val kws = Keyword.add_keywords kws Keyword.empty_keywords
      val tks = s |> Token.tokenize kws {strict=true} 
      (*val _ = map (Token.reports kws) tks |> flat*)
      val tks = filter Token.is_proper tks
      
      fun parse_all src = let
        val src = map Token.init_assignable src
        val (res,_) = Scan.catch (Scan.finite Token.stopper (p --| Scan.ahead Parse.eof)) src
        
        val rp = map Token.reports_of_value src |> flat
        val _ = Context_Position.reports ctxt rp
        
        (*val _ = map Token.reports_of_value src |> flat*)
      in
        res
      end
      
      val res = parse_all tks
    in
      res
    end
                                              
        
    
  end\<close> 
               
  
  ML \<open>structure C_Interface = struct
    datatype cprim = 
        PRIM_CHAR
      | PRIM_SI8 | PRIM_UI8
      | PRIM_SI16 | PRIM_UI16
      | PRIM_SI32 | PRIM_UI32
      | PRIM_SI64 | PRIM_UI64
      | PRIM_FLOAT
      | PRIM_DOUBLE
    datatype cfield = FLD_NAMED of ctype * string | FLD_ANON of cfield list
         and ctype = 
              CTY_PRIM of cprim 
            | CTY_PTR of ctype            
            | CTY_STRUCT of cfield list
            | CTY_NAMED of string
  
         
    datatype typedef = TYPEDEF of string * ctype
    fun dest_tydef (TYPEDEF (n,t)) = (n,t)
    val mk_tydef = TYPEDEF

    (* Signature *)
    datatype c_sig = CSIG of ctype option * string * ctype list 
    
    (* Optional types, not all info needs to be specified *)
    
    datatype cfieldo = FLDO_NAMED of ctypeo option * string option
         and ctypeo = 
              CTYO_PRIM of cprim 
            | CTYO_PTR of ctypeo
            | CTYO_STRUCT of cfieldo list
            | CTYO_NAMED of string
  
    datatype crtypeo = CRTYO_UNSPEC | CRTYO_VOID | CRTYO_TY of ctypeo         
            
    datatype typedefo = TYPEDEFO of string * ctypeo
    
    datatype c_sigo = CSIGO of crtypeo * string option * ctypeo option list option
    
    fun dest_tydefo (TYPEDEFO (n,t)) = (n,t)
    val mk_tydefo = TYPEDEFO
    
    fun name_of_sig (CSIGO (_,SOME n,_)) = n
      | name_of_sig _ = error "Signature must have name"
    
         
    (* Parsing *)
    local open Parser_Util in
    
      (* TODO: Check for valid C identifier *)
      val parse_id = Parse.short_ident
      
      val parse_cprim = 
         pcm "char" >> K PRIM_CHAR
      || pcm "int8_t" >> K PRIM_SI8
      || pcm "int16_t" >> K PRIM_SI16
      || pcm "int32_t" >> K PRIM_SI32
      || pcm "int64_t" >> K PRIM_SI64
      || pcm "uint8_t" >> K PRIM_UI8
      || pcm "uint16_t" >> K PRIM_UI16
      || pcm "uint32_t" >> K PRIM_UI32
      || pcm "uint64_t" >> K PRIM_UI64
      || pcm "float" >> K PRIM_FLOAT
      || pcm "double" >> K PRIM_DOUBLE
  
      fun mk_ptr ty [] = ty
        | mk_ptr ty (_::xs) = CTYO_PTR (mk_ptr ty xs)
      
      fun parse_cfield s = (
           parse_ctype -- Scan.option parse_id --| Parse.$$$ ";" >> FLDO_NAMED
        (*|| parse_fld_struct --| Parse.$$$ ";" >> FLDO_ANON*)
      ) s
      and parse_fld_struct s = (pkw "struct" |-- Parse.$$$ "{" |-- Scan.repeat1 parse_cfield --| Parse.$$$ "}") s
      and parse_ctype1 s = (
           parse_cprim >> CTYO_PRIM
        || parse_id >> CTYO_NAMED   
        || parse_fld_struct >> CTYO_STRUCT
      ) s
      and parse_ctype_noauto s = (parse_ctype1 -- Scan.repeat (Parse.$$$ "*") >> (fn (ty,ptrs) => (mk_ptr ty ptrs))) s
      and parse_ctype s = (
           pcm "auto" >> (fn _ => NONE)
        || Parse.underscore >> (fn _ => NONE)
        || parse_ctype_noauto >> SOME
      ) s
         
      val parse_rtype = 
           pcm "auto" >> K CRTYO_UNSPEC 
        || Parse.underscore >> K CRTYO_UNSPEC 
        || pcm "void" >> K CRTYO_VOID
        || parse_ctype_noauto >> CRTYO_TY 
      
      val parse_typedef = pkw "typedef" |-- parse_ctype_noauto -- parse_id --| Parse.$$$ ";" >> (fn (ty,name) => mk_tydefo (name,ty))
      val parse_typedefs = Scan.repeat parse_typedef
    
      fun long_sig ((rt,n),args) = CSIGO (rt,SOME n,args)
      
      fun parse_wildcard p = Parse.underscore >> K NONE || p >> SOME
      
      val parse_parlist = Parse.$$$ "(" |-- Parse.enum "," parse_ctype --| Parse.$$$ ")"
      val parse_short_sig = parse_id >> (fn name => CSIGO (CRTYO_UNSPEC,SOME name,NONE))
      val parse_long_sig = 
          parse_rtype -- parse_id -- parse_wildcard parse_parlist 
        >> long_sig
        
      val parse_sig = parse_long_sig || parse_short_sig
            
    end
    
    
    
    
    
    
    (* Checking *)
    
    val ct_basic_kws =       [
      "auto",
      "break",
      "case",
      "char",
      "const",
      "continue",
      "default",
      "do",
      "double",
      "else",
      "enum",
      "extern",
      "float",
      "for",
      "goto",
      "if",
      "inline",
      "int",
      "long",
      "register",
      "restrict",
      "return",
      "short",
      "signed",
      "sizeof",
      "static",
      "struct",
      "switch",
      "typedef",
      "union",
      "unsigned",
      "void",
      "volatile",
      "while",
      "_Alignas",
      "_Alignof",
      "_Atomic",
      "_Bool",
      "_Complex",
      "_Generic",
      "_Imaginary",
      "_Noreturn",
      "_Static_assert",
      "_Thread_local"
    ]
    val ct_basic_kw_set = Symtab.make_set ct_basic_kws
    
    val ct_kws = 
    ["(",")",";","{","}","*",","] (* TODO: Complete this list *)      
    @
    ct_basic_kws
    @
    ["int8_t", "int16_t", "int32_t", "int64_t",
     "uint8_t", "uint16_t", "uint32_t", "uint64_t"]
      
    val ct_kws_context = Name.make_context ct_kws
     
    fun is_cid_start s = Symbol.is_ascii_letter s orelse s="_"
    fun is_cid_ctd s = is_cid_start s orelse Symbol.is_ascii_digit s
    
    fun is_c_identifier s =
      size s > 0 andalso is_cid_start (String.substring (s, 0, 1)) andalso
      forall_string is_cid_ctd s andalso
      not (Symtab.defined ct_basic_kw_set s);
         
    fun check_identifier name = (is_c_identifier name orelse error ("Invalid identifier " ^ name); ())
      
    fun check_decl ctab name = (Symtab.defined ctab name orelse error ("Undeclared type " ^ name); ())
          
    fun check_type ctab (CTY_NAMED name) = check_decl ctab name
      | check_type _ (CTY_PRIM _) = ()
      | check_type ctab (CTY_PTR t) = check_type ctab t
      | check_type ctab (CTY_STRUCT fs) = (map (check_field ctab) fs; ())
    and check_field ctab (FLD_NAMED (ty,name)) = (check_type ctab ty; check_identifier name)
      | check_field ctab (FLD_ANON fs) = (map (check_field ctab) fs; ())

    fun clookup ctab n = case Symtab.lookup ctab n of 
      NONE => error ("Undeclared type: " ^ n) 
    | SOME t => t  

    fun make_ctab tydefs = let
      fun add_tydef (name,ty) ctab = let
        val _ = Symtab.defined ctab name andalso error ("Duplicate typedef " ^ name)
      in
        Symtab.update (name,ty) ctab
      end
    in
      fold add_tydef tydefs Symtab.empty
    end
    
    fun mk_indirect (a,b) = ([],a@b)
    
    fun join_di (a,b) (c,d) = (a@c, b@d)
    fun flat_dis dis = fold join_di dis ([],[])
    
    fun cty_di_names (CTY_NAMED n) = ([n],[])
      | cty_di_names (CTY_STRUCT fs) = map cfld_di_names fs |> flat_dis
      | cty_di_names (CTY_PTR ty) = cty_di_names ty |> mk_indirect
      | cty_di_names (CTY_PRIM _) = ([],[])
    and cfld_di_names (FLD_NAMED (ty,_)) = cty_di_names ty
      | cfld_di_names (FLD_ANON fs) = map cfld_di_names fs |> flat_dis
    
    
    fun cty_direct_names (CTY_NAMED n) = [n]
      | cty_direct_names (CTY_STRUCT fs) = 
          map cfld_direct_names fs |> flat
      | cty_direct_names _ = []
    and cfld_direct_names (FLD_NAMED (ty,_)) = cty_direct_names ty
      | cfld_direct_names (FLD_ANON fs) = 
          map cfld_direct_names fs |> flat
        
          
          
          
    fun order_tydefs tydefs = let
      val ctab = make_ctab (map dest_tydef tydefs)

      fun succs_of_ty ty = let
        fun is_struct n = case Symtab.lookup ctab n of 
            SOME (CTY_STRUCT _) => true 
          | _ => false
        
        fun filter_indirect names = filter (not o is_struct) names
      
        val (d,i) = cty_di_names ty
        val succs = d @ filter_indirect i
      in
        succs
      end
            
      datatype state = OPEN | CLOSED
      
      fun add name (vset,res) = 
        case Symtab.lookup vset name of 
          SOME CLOSED => (vset,res) 
        | SOME OPEN => error ("C-Header: circular typedefs via " ^ name)
        | NONE => let
            val vset = Symtab.update (name,OPEN) vset
            val ty = clookup ctab name
            val succs = succs_of_ty ty
            
            (*val _ = (@{print} name, @{print} succs)*)
            
            val (vset,res) = fold add succs (vset,res)
            val vset = Symtab.update (name,CLOSED) vset
            
            val res = TYPEDEF (name,ty) :: res
          in
            (vset,res)
          end
      
      val (_,tydefs) = fold add (Symtab.keys ctab) (Symtab.empty,[])
      val tydefs = rev tydefs
    in
      tydefs
    end
    
    
            
    fun check_tdef_cycle ctab = let
    
      val clookup = clookup ctab
    
      datatype state = OPEN | CLOSE
    
      fun ccyc (CTY_NAMED name) stab = (
        case Symtab.lookup stab name of 
          NONE => Symtab.update (name,OPEN) stab |> ccyc (clookup name) |> Symtab.update (name,CLOSE)
        | SOME OPEN => error ("Circular struct via " ^ name)
        | SOME CLOSE => stab
      )
      | ccyc (CTY_STRUCT fs) stab = fold ccyc_fld fs stab
      | ccyc (CTY_PRIM _) stab = stab
      | ccyc (CTY_PTR _) stab = stab
      and 
        ccyc_fld (FLD_NAMED (ty,_)) = ccyc ty
      | ccyc_fld (FLD_ANON fs) = fold ccyc_fld fs
    
      val decls = Symtab.dest ctab |> map snd
      val _ = Symtab.empty |> fold ccyc decls   
    in
      ()
    end  
      

    (*      
    fun is_valid_rty ctab (CTY_NAMED name) = 
          (case Symtab.lookup ctab name of NONE => false | SOME t => is_valid_rty ctab t)
      | is_valid_rty _ (CTY_PRIM _) = true
      | is_valid_rty _ (CTY_PTR _) = true
      | is_valid_rty _ (CTY_STRUCT _) = false
    
    fun check_valid_rty dd t = (is_valid_rty dd t orelse error "Aggregate return type not supported by C"; ())  
    *)
      
    fun is_allowed_ty ctab (CTY_NAMED name) = 
          (case Symtab.lookup ctab name of NONE => false | SOME t => is_allowed_ty ctab t)
      | is_allowed_ty _ (CTY_PRIM _) = true
      | is_allowed_ty _ (CTY_PTR _) = true
      | is_allowed_ty _ (CTY_STRUCT _) = false

    fun check_allowed_ty dd t = (is_allowed_ty dd t orelse error "C-Header: struct argument or return types in LLVM not compatible with C-ABI!"; ())
    
    fun check_rtype _ NONE = ()
      | check_rtype dd (SOME t) = (check_type dd t; check_allowed_ty dd t)
      
    fun check_csig ctab (CSIG (rty,name,argtys)) = (
      check_rtype ctab rty;
      check_identifier name;
      map (check_type ctab) argtys;
      map (check_allowed_ty ctab) argtys;
      ()
    ) handle ERROR msg => error ("Signature " ^ name ^ ": " ^ msg)
      
    
    (* Check list of type definitions, and create lookup table *)
    fun check_tydefs tydefs = let
      val tydefs = map dest_tydef tydefs
      val _ = map (check_identifier o fst) tydefs
      
      val ctab = make_ctab tydefs
      
      val _ = check_tdef_cycle ctab
      
      fun check_tydef ctab (name,cty) = (check_identifier name; check_type ctab cty; ())
      
      val _ = map (check_tydef ctab) tydefs
    in
      ctab
    end
      
    fun check_tydefs_sigs tydefs sigs = let
      val ctab = check_tydefs tydefs
      val _ = map (check_csig ctab) sigs
    in
      ()
    end
    
    
    (* Printing *)
    local open Simple_PP in
      (* TODO: Rename _to_Cs \<mapsto> pretty_ *)
      fun cprim_to_Cs PRIM_CHAR = word "char"
        | cprim_to_Cs PRIM_SI8 = word "int8_t" 
        | cprim_to_Cs PRIM_SI16 = word "int16_t"
        | cprim_to_Cs PRIM_SI32 = word "int32_t"
        | cprim_to_Cs PRIM_SI64 = word "int64_t"
        | cprim_to_Cs PRIM_UI8 = word "uint8_t" 
        | cprim_to_Cs PRIM_UI16 = word "uint16_t"
        | cprim_to_Cs PRIM_UI32 = word "uint32_t"
        | cprim_to_Cs PRIM_UI64 = word "uint64_t"
        | cprim_to_Cs PRIM_FLOAT = word "float"
        | cprim_to_Cs PRIM_DOUBLE = word "double"
                                                  
      fun cfield_to_Cs (FLD_NAMED (ty,name)) = block [ctype_to_Cs ty, word name, nword ";"]  
        | cfield_to_Cs (FLD_ANON fs) = block [fldstruct_to_Cs empty fs, nword ";"]
      and fldstruct_to_Cs n fs = block [word "struct",n, sep, big_braces (map (line o single o cfield_to_Cs) fs) ]
      and ctype_to_Cs (CTY_PRIM t) = cprim_to_Cs t
        | ctype_to_Cs (CTY_PTR t) = block [ctype_to_Cs t, nword "*"]
        | ctype_to_Cs (CTY_STRUCT fs) = fldstruct_to_Cs empty fs
        | ctype_to_Cs (CTY_NAMED name) = word name

      fun tydef_proto_to_Cs (TYPEDEF (name,CTY_STRUCT _)) = block [word "typedef", word "struct", word name, word name, nword ";"]
        | tydef_proto_to_Cs _ = empty
        
      fun tydef_to_Cs (TYPEDEF (name,CTY_STRUCT fs)) = block [word "typedef", fldstruct_to_Cs (word name) fs, sep, word name, nword ";"]
        | tydef_to_Cs (TYPEDEF (name,ty)) = block [word "typedef", ctype_to_Cs ty, sep, word name, nword ";"]
      
      val tydefs_proto_to_Cs = fbrks o map tydef_proto_to_Cs
      val tydefs_to_Cs = fbrks o map tydef_to_Cs
        
      fun rty_to_Cs NONE = word "void" | rty_to_Cs (SOME ty) = ctype_to_Cs ty
      
      fun csig_to_Cs (CSIG (rty,name,partys)) = block [rty_to_Cs rty,fsep,word name,parlist (map ctype_to_Cs partys),word ";"]
                
      val csigs_to_Cs = fbrks o map csig_to_Cs
    end

    (* Conversion from optional to definitive C *)

    fun invent_fld_names fs = let
      fun add (FLDO_NAMED (_,SOME n)) = Name.declare n
        | add (FLDO_NAMED (SOME (CTYO_STRUCT fs),NONE)) = fold add fs
        | add _ = I

      (* Create field names. 
        Special rule: anonymous structure fields stay anonymous 
      *)    
      fun amend ((_,fld as FLDO_NAMED (SOME (CTYO_STRUCT _), NONE))) context = (fld,context)
        | amend (i,FLDO_NAMED (ty,NONE)) context = let
              val (n,context) = Name.variant ("field" ^ Int.toString i) context
            in 
              (FLDO_NAMED (ty,SOME n), context)
            end  
        | amend (_,fld) context = (fld,context) 
      
      val context = ct_kws_context |> fold add fs
      
      val fs = map_index I fs
      val (fs,_) = fold_map amend fs context
      
    in
      fs
    end
      
    fun ctypeo_to_ctype (CTYO_PRIM p) = CTY_PRIM p
      | ctypeo_to_ctype (CTYO_PTR t) = CTY_PTR (ctypeo_to_ctype t)
      | ctypeo_to_ctype (CTYO_STRUCT fso) = CTY_STRUCT (fso_to_fs fso)
      | ctypeo_to_ctype (CTYO_NAMED n) = CTY_NAMED n
    and fso_to_fs fso = invent_fld_names fso |> map cfieldo_to_cfield
    and cfieldo_to_cfield (FLDO_NAMED (NONE, _)) = error ("C-Header: incomplete type for field")
      | cfieldo_to_cfield (FLDO_NAMED (SOME (CTYO_STRUCT fso), NONE)) = FLD_ANON (map cfieldo_to_cfield fso)
      | cfieldo_to_cfield (FLDO_NAMED (_, NONE)) = error ("C-Header: incomplete name for field")
      | cfieldo_to_cfield (FLDO_NAMED (SOME cty, SOME n)) = FLD_NAMED (ctypeo_to_ctype cty,n)
    
    fun crtypeo_to_ctype CRTYO_UNSPEC = error "C-Header: unspecified return type"  
      | crtypeo_to_ctype CRTYO_VOID = NONE
      | crtypeo_to_ctype (CRTYO_TY ty) = SOME (ctypeo_to_ctype ty)
      
    fun cargo_to_carg NONE = error "C-Header: unspecified argument type"  
      | cargo_to_carg (SOME ty) = ctypeo_to_ctype ty
    fun csigo_to_csig (CSIGO (rty, SOME n, SOME argtys)) = CSIG (crtypeo_to_ctype rty, n, map cargo_to_carg argtys)
      | csigo_to_csig _ = error "C-Header: incomplete signature"
      
  
    fun ctdefo_to_ctdef (TYPEDEFO (n,ty)) = TYPEDEF (n, ctypeo_to_ctype ty)   
          
    (* Amending partial specification *)
    
    fun amend_cprim PRIM_CHAR PRIM_SI8 = PRIM_SI8
      | amend_cprim PRIM_CHAR PRIM_UI8 = PRIM_UI8
      | amend_cprim PRIM_SI8 PRIM_UI8 = PRIM_UI8
      | amend_cprim PRIM_SI8 PRIM_CHAR = PRIM_CHAR
      | amend_cprim PRIM_UI8 PRIM_SI8 = PRIM_SI8
      | amend_cprim PRIM_UI8 PRIM_CHAR = PRIM_CHAR
    
      | amend_cprim PRIM_SI16 PRIM_UI16 = PRIM_UI16
      | amend_cprim PRIM_UI16 PRIM_SI16 = PRIM_SI16
    
      | amend_cprim PRIM_SI32 PRIM_UI32 = PRIM_UI32
      | amend_cprim PRIM_UI32 PRIM_SI32 = PRIM_SI32
      
      | amend_cprim PRIM_SI64 PRIM_UI64 = PRIM_UI64
      | amend_cprim PRIM_UI64 PRIM_SI64 = PRIM_SI64
      
      | amend_cprim t ta = if t=ta then ta else error "C-Header: declared type does not match"

    fun amend_option _ NONE NONE = NONE
      | amend_option _ NONE (SOME x) = SOME x  
      | amend_option _ (SOME x) NONE = SOME x  
      | amend_option f (SOME x) (SOME x') = SOME (f x x')

    val amend_name = amend_option (K I)

    fun check_named_override ctab' cty n = let
      
      fun chk_ty (CTYO_PRIM p) (CTYO_PRIM p') stab = ( amend_cprim p p'; stab )
        | chk_ty (CTYO_PTR p) (CTYO_PTR p') stab = chk_ty p p' stab
        | chk_ty (CTYO_NAMED n) (CTYO_NAMED n') stab = (n=n' orelse error "C-Header: cannot override structure name"; stab)
        | chk_ty (CTYO_STRUCT fs) (CTYO_STRUCT fs') stab = fold2 chk_fld fs fs' stab
        | chk_ty ty (CTYO_NAMED n') stab = (case Symtab.lookup stab n' of
            NONE => chk_ty ty (clookup ctab' n') (Symtab.update (n',ty) stab)
          | SOME tyy => (tyy=ty orelse error "C-Header: ambiguous named override"; stab)  
        )
        | chk_ty _ _ _ = error "C-Header: mismatched named override"
        
      and chk_fld (FLDO_NAMED (SOME ty,_)) (FLDO_NAMED (SOME ty',_)) = chk_ty ty ty'
        | chk_fld _ _ = error "C-Header: incomplete or mismatching structure in named override"
        
    
    in
      chk_ty cty (CTYO_NAMED n) Symtab.empty;
      ()
    end
                
    fun amend_ctype _ (CTYO_PRIM p) (CTYO_PRIM p') = CTYO_PRIM (amend_cprim p p')
      | amend_ctype ctab' (CTYO_PTR t) (CTYO_PTR t') = CTYO_PTR (amend_ctype ctab' t t')
      | amend_ctype ctab' (CTYO_STRUCT fs) (CTYO_STRUCT fs') = (
          length fs = length fs' orelse error "C-Header: declared number of fields do not match";
          CTYO_STRUCT (map2 (amend_cfield ctab') fs fs')
        )
      | amend_ctype _ (CTYO_NAMED n) (CTYO_NAMED n') = (
          n=n' orelse error ("C-Header: cannot override structure name: " ^ n ^ " -> " ^ n');
          CTYO_NAMED n
        ) 
      | amend_ctype ctab' cty (CTYO_NAMED n') = ( check_named_override ctab' cty n'; CTYO_NAMED n' ) 
      | amend_ctype _ _ _ = error ("C-Header: declared structure does not match")
    and amend_cfield ctab' (FLDO_NAMED (t,n)) (FLDO_NAMED (t',n')) = FLDO_NAMED (amend_option (amend_ctype ctab') t t', amend_name n n')
          

    fun amend_crtype _ CRTYO_UNSPEC ty = ty
      | amend_crtype _ ty CRTYO_UNSPEC = ty
      | amend_crtype ctab (CRTYO_TY ty) (CRTYO_TY ty') = CRTYO_TY (amend_ctype ctab ty ty')
      | amend_crtype _ (CRTYO_VOID) (CRTYO_VOID) = CRTYO_VOID
      | amend_crtype _ _ _ = error "C-Header: return type mismatch"
      
    fun make_ctabo tydefs = let
      fun add (TYPEDEFO (name,ty)) tab = 
        if Symtab.defined tab name then error ("Duplicate typdef: " ^ name)
        else Symtab.update (name,ty) tab
    
    in
      fold add tydefs Symtab.empty
    end  
            
    fun amend_typedefs tydefs tydefs' = let
      val ctab = make_ctabo tydefs
      val ctab' = make_ctabo tydefs'
    
    in
      Symtab.join (K (uncurry (amend_ctype ctab'))) (ctab, ctab')
    end  
      
    
    fun amend_sig ctab (CSIGO (ty,n,argtys)) (CSIGO (ty',n',argtys')) = let
      fun nts NONE = "_" | nts (SOME x) = x
    
      val _ =
        case (argtys, argtys') of
          (SOME xs, SOME xs') => length xs = length xs' orelse error("C-Header: (" ^ nts n ^ "): parameter number mismatch")
        | _ => false   
    in
      CSIGO (amend_crtype ctab ty ty', amend_name n n', amend_option (map2 (amend_option (amend_ctype ctab))) argtys argtys')
    end
    
    
    local open LLC_Intermediate in      
      (* Create initial optional specification from LLVM *)
    
      fun cty_of_lty (TInt 8) = CTYO_PRIM PRIM_SI8
        | cty_of_lty (TInt 16) = CTYO_PRIM PRIM_SI16
        | cty_of_lty (TInt 32) = CTYO_PRIM PRIM_SI32
        | cty_of_lty (TInt 64) = CTYO_PRIM PRIM_SI64
        | cty_of_lty (TInt w) = error ("cty_of_lty: Unsupported integer width " ^ Int.toString w)
        | cty_of_lty (TFloat) = CTYO_PRIM PRIM_FLOAT
        | cty_of_lty (TDouble) = CTYO_PRIM PRIM_DOUBLE
        | cty_of_lty (TPtr ty) = CTYO_PTR (cty_of_lty ty)
        | cty_of_lty (TStruct tys) = CTYO_STRUCT (map cfld_of_lty tys)
        | cty_of_lty (TNamed name) = CTYO_NAMED name
      and cfld_of_lty ty = FLDO_NAMED (SOME (cty_of_lty ty),NONE)
        
      fun cty_of_rlty NONE = CRTYO_VOID
        | cty_of_rlty (SOME lty) = CRTYO_TY (cty_of_lty lty)
    
      fun csig_of_eqn (EQN (rlty,name,largs,_)) 
        = CSIGO (cty_of_rlty rlty, SOME name, SOME (map (SOME o cty_of_lty o fst) largs))
        
      fun cfield_of_lty lty = FLDO_NAMED (SOME (cty_of_lty lty), NONE)
        
      fun ctydef_of_llc_named (Named_Type (name,ltys)) = 
        TYPEDEFO (name,CTYO_STRUCT (map cfield_of_lty ltys))
        
        
    end    
    
    
  end\<close>
  
  
    
  
  
  
  ML \<open>structure LLC_HeaderGen = struct
    open C_Interface
  
    val parse_raw_tydefs = Parse.position Parse.cartouche
    val parse_raw_sig = Parse.position (Parse.cartouche || Parse.short_ident || Parse.string)
    
    val check_raw_tydefs = Parser_Util.parse_inner ct_kws parse_typedefs
    val check_raw_sig = Parser_Util.parse_inner ct_kws parse_sig
    
    fun find_reachable_types ntys eqns = let
      open LLC_Intermediate
      
      fun dest_nty (Named_Type (name,ftys)) = (name,ftys)
      fun make_ltab ntys = Symtab.make (map dest_nty ntys)
      fun mk_nty (name,ftys) = Named_Type (name,ftys)
      
      val ltab = make_ltab ntys
      
      fun llookup name = case Symtab.lookup ltab name of 
            NONE => error ("Undefined type: " ^ name)
          | SOME x => x
      
      fun rc_eqn (EQN (rty,_,args,_)) = rc_rty rty #> fold rc_ty (map fst args)
      and rc_rty NONE = I
        | rc_rty (SOME ty) = rc_ty ty
      and rc_ty (TPtr ty) = rc_ty ty
        | rc_ty (TStruct tys) = fold rc_ty tys
        | rc_ty (TNamed name) = (fn tab => 
            if Symtab.defined tab name then tab
            else let
              val tys = llookup name
              val tab = Symtab.update (name,tys) tab
            in fold rc_ty tys tab
            end
          )
        | rc_ty (TInt _) = I
        | rc_ty (TFloat) = I
        | rc_ty (TDouble) = I
      
    in
      fold rc_eqn eqns Symtab.empty
      |> Symtab.dest |> map mk_nty
    end
    
    
    fun make_header _ _ _ [] = NONE 
      | make_header hfname tydefs named_types eqns = let
    
      (* Strip down named types to what is reachable from signatures *)
      val named_types = find_reachable_types named_types (map fst eqns)
    
      (* Create joint named type table *)
      local val ctydefs = map ctydef_of_llc_named named_types in
        val ctab = amend_typedefs ctydefs tydefs
      end
      
      (* Create signatures from equations, and amend with declared signatures *)
      val sigs = map (apfst csig_of_eqn #> uncurry (amend_sig ctab)) eqns
      
      (* Convert optional type-table and signatures to definitive ones *)
      val tydefs = map ctdefo_to_ctdef (map mk_tydefo (Symtab.dest ctab))
      val sigs = map csigo_to_csig sigs

      (* Order typedefs *)
      (*xxx: we must also consider *indirect* references!
        see bin_search, where typedef uint64 elem_t gets sorted to the end!
      *)
        
        
        
      
      val tydefs = order_tydefs tydefs
      
      (* Check consistency *)
      val _ = check_tydefs_sigs tydefs sigs      
            
      (* Print *)
      fun make_hd_id name = let 
        val name = Symbol.explode name |> filter is_cid_ctd |> map Symbol.to_ascii_upper |> implode
        val name = "_" ^ name ^ "_H"
      in name end  
        
      val hfname = make_hd_id hfname
      
      val h_to_C = let
        open Simple_PP
        val hfsym = word hfname
      in block [
          (* TODO: Include information for which version of ll-file this has been generated! *)
          line [word "// Generated by Isabelle-LLVM. Do not modify."],
          line [word "#ifndef", hfsym],
          line [word "#define", hfsym, word "1"],
          fbrk, fbrk,
          tydefs_proto_to_Cs tydefs,
          fbrk, fbrk,
          tydefs_to_Cs tydefs,
          fbrk, fbrk,
          csigs_to_Cs sigs,
          fbrk, fbrk,
          line [word "#endif"]
        ]
      end
      
    in
      SOME (Simple_PP.string_of h_to_C)
    end
    
    
  end    
    
\<close>    
  

end
