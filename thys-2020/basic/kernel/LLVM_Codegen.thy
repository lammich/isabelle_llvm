section \<open>LLVM Code Generator\<close>
theory LLVM_Codegen
imports LLVM_Shallow
begin

    (* DO NOT USE IN PRODUCTION VERSION \<rightarrow> SLOWDOWN *)
    (* declare [[ML_exception_debugger, ML_debugger, ML_exception_trace]] *)

  text \<open>This is the trusted part of the code generator, which accepts
    Isabelle-LLVM programs that follow a strict format 
    (fully monadified, only \<open>ll_\<close> instructions).
    
    The preprocessor and user-interface of the code generator can be found in 
    @{file "../preproc/LLVM_Codegen_Preproc.thy"}
  \<close>

  subsection \<open>Pair Types\<close>
  text \<open>The code generator will translate pair instructions if such a predicate is registered.
    here, @{typ 't} must be of form \<open>(...)type\<close>, and \<open>tfrees 't\<^sub>1,'t\<^sub>2 \<subseteq> tfrees 't\<close>, 
    and there can only be one such predicate per type.
  \<close>
  definition 
    ll_is_pair_type :: "bool \<Rightarrow> 't::llvm_rep itself \<Rightarrow> 't\<^sub>1::llvm_rep itself \<Rightarrow> 't\<^sub>2::llvm_rep itself \<Rightarrow> bool"
  where "ll_is_pair_type anonymous _ _ _ \<equiv> struct_of TYPE('t) = llvm_s_pair (struct_of TYPE('t\<^sub>1)) (struct_of TYPE('t\<^sub>2))"

  named_theorems ll_is_pair_type_thms \<open>Isabelle-LLVM: Theorems for user-defined tuple types\<close>
  
  lemma TERM_TYPE_I: "TERM (TYPE ('a))" .
  
  lemma ll_dest_pair_type:
    assumes "ll_is_pair_type anon TYPE('t::llvm_rep) TYPE('t\<^sub>1::llvm_rep) TYPE('t\<^sub>2::llvm_rep)"
    assumes "TERM (TYPE('t))"
    shows "TERM (TYPE('t\<^sub>1))" "TERM (TYPE('t\<^sub>2))"
    .
  
  
  
  subsection \<open>General Functions\<close>
  ML \<open> structure LLC_Lib = 
    struct
      fun dest_llM (Type (@{type_name M},[T,@{typ unit},@{typ llvm_memory},@{typ err}])) = T
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
      
              
      (* TODO: Move *)
      fun instantiate_uc (tyenv,tenv) thm = let
        val thy = Thm.theory_of_thm thm
        
        val tyi = Vartab.dest tyenv |> map (fn (n,(s,T)) => ((n,s),Thm.global_ctyp_of thy T))
        val ti = Vartab.dest tenv |> map (fn (n,(s,t)) => ((n,s),Thm.global_cterm_of thy t))
      in
        Thm.instantiate (tyi,ti) thm
      end

      fun is_monomorphic_const (Const (_,T)) = 
        not (Term.exists_subtype (fn TVar _ => true | TFree _ => true | _ => false) T)
      | is_monomorphic_const _ = false

      fun assert_monomorphic_const t = 
        is_monomorphic_const t orelse 
          raise TYPE("Expected monomorphic constant",[fastype_of t],[t])
            

      fun unique_variant1 n name ntab = let
        val name' = if n=0 then name else name ^ Int.toString n
      in    
        if Symtab.defined ntab name' then unique_variant1 (n+1) name ntab
        else (name', Symtab.insert_set name' ntab)
      end
      
      val unique_variant = unique_variant1 0
      
      
      fun the_assert msg NONE = raise Fail msg 
         | the_assert _ (SOME x) = x 
      
      
      fun dest_is_pair_type_thm thm = case Thm.prop_of thm of 
        @{mpat (typs) "Trueprop (ll_is_pair_type 
            ?anon 
            TYPE(?'v_t::llvm_rep) 
            TYPE(?'v_ta::llvm_rep) 
            TYPE(?'v_tb::llvm_rep))"} => let 
              val anon = case anon of @{mpat "True"} => true | @{mpat "False"} => false | _ => raise THM("dest_is_pair_type_thm: Not a literal Boolean",~1,[thm])
            in
              (anon,t,ta,tb)
            end
      | _ => raise THM("dest_is_pair_type_thm",~1,[thm])
         
      
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
      

      fun dest_head (Const nt) = nt
        | dest_head (Free nt) = nt
        | dest_head t = raise TERM("dest_head", [t])
            
      val is_valid_head = can dest_head
      fun check_valid_head f = 
        (is_valid_head f orelse raise TERM("Invalid head (expected const or free)",[f]); f)
      
      val name_of_head = fst o dest_head
                    
      
      
      val llc_compile_while =
        Config.bool (Config.declare ("llc_compile_while", \<^here>) (fn _ => Config.Bool true));
      
      
      
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
  
  ML \<open> structure LLC_Intermediate = 
    struct
    
      (* LLC intermediate representation. Somewhere in between Isabelle and LLVM-IR *)    
      
      datatype llc_type = TInt of int | TPtr of llc_type | TPair of llc_type*llc_type | TNamed of string
      datatype llc_const = CInit | CInt of int | CNull
      datatype llc_opr = OVar of string | OConst of llc_const
      type llc_topr = llc_type * llc_opr
      datatype llc_topr' = OOOp of llc_topr | OOType of llc_type

      datatype llc_cmd = 
                 CmIf of llc_topr * llc_block * llc_block
               | CmWhile of (llc_type * string) * llc_block * llc_block * llc_topr
               | CmInstr of string * llc_topr' list
               | CmCall of llc_type option * string * llc_topr list
      
          and llc_block =
                BlBind of (llc_type * string) option * llc_cmd * llc_block
              | BlReturn of llc_topr option 
    
      datatype llc_eqn =              
                EQN of llc_type option * string * (llc_type * string) list * llc_block
    
      datatype llc_named_type = Named_Type of string * llc_type list                
                
      fun pretty_mstr m s = Pretty.markup m [Pretty.str s]
      
      fun pretty_type (TInt w) = pretty_mstr Markup.keyword1 ("i" ^ Int.toString w)
        | pretty_type (TPtr T) = Pretty.block [pretty_type T, Pretty.str "*"]
        | pretty_type (TPair (T1,T2)) = Pretty.list "{" "}" (map pretty_type [T1,T2])
        | pretty_type (TNamed name) = Pretty.str name
      
      fun pretty_const CInit = pretty_mstr Markup.keyword1 "zeroinitializer"
        | pretty_const (CInt i) = pretty_mstr Markup.numeral (Int.toString i)
        | pretty_const CNull = pretty_mstr Markup.keyword1 "null"

      fun pretty_opr (OVar name) = Pretty.str name
        | pretty_opr (OConst c) = pretty_const c
        
      fun pretty_topr (T,opr) = Pretty.block [pretty_type T, Pretty.brk 1, pretty_opr opr]
      
      fun pretty_topr' (OOOp x) = pretty_topr x 
        | pretty_topr' (OOType T) = pretty_type T
      
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
        
  subsection \<open>Isabelle Term Parser\<close>
  text \<open>Parser from Isabelle terms to intermediate representation\<close>
  ML \<open> structure LLC_Compiler = 
    struct
      open LLC_Lib LLC_Intermediate
    
      (* Maps Isabelle type names to named type theorems *)
      structure Named_Type_Tab = Proof_Data (
        type T = thm Symtab.table
        val init = K Symtab.empty
      )

      (* Record type instance: LLVM name and field types *)
      type named_type_inst = string * llc_type list
      
      (* Maps instantiated (monomorphic) Isabelle types to instances *)
      structure NTInst_Tab = Proof_Data (
        type T = named_type_inst Typtab.table
        val init = K Typtab.empty
      )

      fun build_named_type_tables ctxt = let
        fun check_pt thm = let
          val (_, typ, typa, typb) = dest_is_pair_type_thm thm
          val _ = is_Type typ orelse raise TYPE("check_pt: Expected type",[typ],[])
          val (tname,args) = dest_Type typ
          
          val _ = forall is_TVar args orelse raise TYPE("check_pt: Expected simple type",[typ],[])
          
          val tvars = Term.add_tvarsT typ []
          val tvarsa = Term.add_tvarsT typa []
          val tvarsb = Term.add_tvarsT typb []
          
          val _ = subset op= (tvarsa, tvars) andalso subset op= (tvarsb, tvars)
            orelse raise TYPE("check_pt: additional type vars in element types",[typ,typa,typb],[])
          
        in
          (tname,thm)
        end
        
        val typtab = Named_Theorems.get ctxt @{named_theorems ll_is_pair_type_thms} |> map check_pt |> Symtab.make
      in
        ctxt
        |> Named_Type_Tab.put typtab
      
      end
      
      fun mk_type_thm ctxt T = Thm.instantiate' [SOME (Thm.ctyp_of ctxt T)] [] @{thm TERM_TYPE_I}
      val dest_type_thm = Thm.prop_of #> Logic.dest_term #> Logic.dest_type

      fun inst_pair_type ctxt (T as Type(tname,_)) = let
        val thm = Symtab.lookup (Named_Type_Tab.get ctxt) tname
        val _ = is_none thm andalso raise TYPE("Not a registered pair type",[T],[]);
        val thm = the thm
        val (anon,_,_,_) = dest_is_pair_type_thm thm
      
        val ftypes = map (fn x => dest_type_thm (x OF [thm,mk_type_thm ctxt T])) @{thms ll_dest_pair_type}
      in
        (anon,ftypes)
      end
      | inst_pair_type _ T = raise TYPE("Invalid type for pair type",[T],[])
      
      fun llc_parse_type (Type (@{type_name word},[T])) ctxt = (dest_numeralT T |> TInt, ctxt)
        | llc_parse_type (Type (@{type_name ptr},[T])) ctxt = llc_parse_type T ctxt |>> TPtr
        | llc_parse_type (T as Type _) ctxt = llc_make_type_inst T ctxt
        | llc_parse_type T _ = raise TYPE ("llc_parse_type: ",[T],[])
      and
      (* Lookup or make named type instance *)
      llc_make_type_inst T ctxt = case Typtab.lookup (NTInst_Tab.get ctxt) T of
        SOME (name,_) => (TNamed name, ctxt)
      | NONE => let
          val (tname,_) = dest_Type T
          
          (* Get anonymity and instantiated field types *)
          val (anon,field_types) = inst_pair_type ctxt T
        in  
          if anon then let
            (* Recursively parse field types *)
            val (field_ltypes,ctxt) = fold_map llc_parse_type field_types ctxt
            
            val (lta,ltb) = case field_ltypes of
              [lta,ltb] => (lta,ltb)
            | _ => raise TYPE("Internal: Currently expecting exactly 2 fields!",T::field_types,[])
          in
            (TPair (lta,ltb), ctxt)
          end
          else let
            (* Make name variant *)
            val used_names = NTInst_Tab.get ctxt |> Typtab.dest |> map (fst o snd) |> Name.make_context
            val (lname,_) = Name.variant (Name.desymbolize NONE tname) used_names
            
            (* Register this instance, with empty fields first *)
            val ctxt = NTInst_Tab.map (Typtab.update (T,(lname,[]))) ctxt
            
            (* Recursively parse field types *)
            val (field_ltypes,ctxt) = fold_map llc_parse_type field_types ctxt
            
            (* Register fields for this instance *)
            val ctxt = NTInst_Tab.map (Typtab.update (T,(lname,field_ltypes))) ctxt
        
          in
            (TNamed lname, ctxt)
          end
        end
    
      fun compute_fun_names fixes thms = let
        val _ = map (assert_monomorphic_const o fst) fixes
      
        val ftab = Termtab.make fixes
        val names = fold (fn (_,n) => Symtab.update_new (n,())) fixes Symtab.empty
        
        fun add_thm thm (ftab,names) = let
          val c = head_of_eqn_thm thm
        in
          if Termtab.defined ftab c then
            (ftab,names)
          else let
            val n = name_of_head c |> Name.desymbolize NONE
            val (n,names) = unique_variant n names
            val ftab = Termtab.update_new (c,n) ftab
          in
            (ftab,names)
          end
        end
        
        val (ftab,_) = fold add_thm thms (ftab,names)
      in
        ftab
      end

                
      (* TODO/FIXME: Populate with actual instructions! Register them, together with their compilers! *)  
      fun is_llvm_instr name = String.isPrefix "LLVM_Shallow.ll_" name
                
      fun llc_parse_vtype (Type (@{type_name unit},[])) ctxt = (NONE, ctxt)
        | llc_parse_vtype T ctxt = llc_parse_type T ctxt |>> SOME
        
      fun llc_parse_const @{mpat (typs) \<open>init::?'v_T::llvm_rep\<close>} ctxt = llc_parse_type T ctxt |>> (fn T => (T,CInit))
        | llc_parse_const @{mpat (typs) \<open>null::?'v_T::llvm_rep ptr\<close>} ctxt = llc_parse_type T ctxt |>> (fn T => (TPtr T, CNull))
        | llc_parse_const t ctxt = case try dest_word_const t of
            SOME (w,v) => ((TInt w, CInt v), ctxt)
          | NONE => raise TERM ("llc_parse_const: ",[t])
      
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
          | llc_parse_op' t ctxt = llc_parse_op t ctxt |>> OOOp
          
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
          val fname = Termtab.lookup (Fun_Tab.get ctxt) f
          val _ = is_none fname andalso raise TYPE("No such function in ftab",[fastype_of f],[f])
          val fname = the fname
        in fname end  

        
        fun check_valid_pair_inst ctxt t pT i fT = let
          val (_,fTs') = inst_pair_type ctxt pT
          val _ = i < length fTs' andalso fT = nth fTs' i
            orelse raise TYPE("Invalid pair instruction instance",[fastype_of (head_of t)],[t])
          
          (*val _ = Pretty.block [Pretty.str "Type instance OK ", Syntax.pretty_term ctxt t, Pretty.str " :: ", Syntax.pretty_typ ctxt (fastype_of t) ]
            |> Pretty.string_of |> writeln
          *)  
        in
          ()
        end
        
        
        fun check_llvm_struct_cmd ctxt (t as @{mpat (typs) \<open>ll_extract_fst :: ?'v_pT::llvm_rep \<Rightarrow> ?'v_aT::llvm_rep llM\<close>}) = 
              check_valid_pair_inst ctxt t pT 0 aT
          | check_llvm_struct_cmd ctxt (t as @{mpat (typs) \<open>ll_extract_snd :: ?'v_pT::llvm_rep \<Rightarrow> ?'v_bT::llvm_rep llM\<close>}) = 
              check_valid_pair_inst ctxt t pT 1 bT
          | check_llvm_struct_cmd ctxt (t as @{mpat (typs) \<open>ll_insert_fst :: ?'v_pT::llvm_rep \<Rightarrow> ?'v_aT::llvm_rep \<Rightarrow> _\<close>}) = 
              check_valid_pair_inst ctxt t pT 0 aT
          | check_llvm_struct_cmd ctxt (t as @{mpat (typs) \<open>ll_insert_snd :: ?'v_pT::llvm_rep \<Rightarrow> ?'v_bT::llvm_rep \<Rightarrow> _\<close>}) = 
              check_valid_pair_inst ctxt t pT 1 bT
          | check_llvm_struct_cmd ctxt (t as @{mpat (typs) \<open>ll_gep_fst :: ?'v_pT::llvm_rep ptr \<Rightarrow> ?'v_aT::llvm_rep ptr llM\<close>}) = 
              check_valid_pair_inst ctxt t pT 0 aT
          | check_llvm_struct_cmd ctxt (t as @{mpat (typs) \<open>ll_gep_snd :: ?'v_pT::llvm_rep ptr \<Rightarrow> ?'v_bT::llvm_rep ptr llM\<close>}) = 
              check_valid_pair_inst ctxt t pT 1 bT
          | check_llvm_struct_cmd _ _ = ()

        
                        
        fun llc_parse_cmd rty t ctxt = 
          let
            val (f,args) = strip_comb t

            val _ = check_valid_head f            
            val cname = name_of_head f
            
          in
            case cname of
              @{const_name \<open>llc_if\<close>} => (case args of 
                  [arg_cond,arg_then,arg_else] => let
                    val (l_cond, ctxt) = llc_parse_op_bool arg_cond ctxt
                    val (l_then,ctxt) = llc_parse_block arg_then ctxt
                    val (l_else,ctxt) = llc_parse_block arg_else ctxt
                  in
                    (CmIf (l_cond,l_then,l_else), ctxt)
                  end
                | _ => raise TERM ("parse_cmd: If needs 3 arguments",[t])
              )
            | @{const_name \<open>llc_while\<close>} => (case args of [@{mpat "\<lambda>_. ?tcond"}, @{mpat "\<lambda>xb. ?tbody"}, arg_inits] => let
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
            | _ => 
                if is_llvm_instr cname then let 
                    val _ = check_llvm_struct_cmd ctxt f
                    val (ops,ctxt) = fold_map llc_parse_op' args ctxt
                  in (CmInstr (cname,ops), ctxt) end
                else let 
                    val (ops,ctxt) = fold_map llc_parse_op args ctxt
                    val fname = ftab_lookup ctxt f
                  in (CmCall (rty, fname ,ops), ctxt) end
                   
          end
        and llc_parse_block @{mpat "bind ?m (\<lambda>x. ?f)"} ctxt = 
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
          | llc_parse_block @{mpat "return ()"} ctxt = (BlReturn NONE, ctxt)
          | llc_parse_block @{mpat "return ?x"} ctxt = llc_parse_op x ctxt |>> SOME |>> BlReturn
          | llc_parse_block t _ = raise TERM ("llc_parse_block: structural error",[t])
         
          
        fun llc_parse_eqn @{mpat "Trueprop (?lhs = ?rhs)"} ctxt = let
          val (hdc,params) = strip_comb lhs
        
          val _ = check_valid_head hdc
          val _ = map (fn a => is_Var a orelse raise TERM ("llc_parse_eqn: arguments must be vars",[a])) params

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
        | llc_parse_eqn t _ = raise TERM ("llc_parse_eqn: Expected equation of form lhs = rhs", [t])
          
          
      end      
      
      fun parse_cthms_aux thms ctxt = fold_map (llc_parse_eqn o Thm.prop_of) thms ctxt
            
      fun parse_cthms ftab thms ctxt = let
        val ctxt = Fun_Tab.put ftab ctxt
        val (eqns,ctxt) = parse_cthms_aux thms (build_named_type_tables ctxt)
        
        val named_tys = NTInst_Tab.get ctxt |> Typtab.dest |> map (Named_Type o snd)
      in 
        (named_tys,eqns)
      end
          
    end
    
  \<close>  

  subsection \<open>LLVM Writer\<close>
  
  text \<open>LLVM Builder. Interface to build actual LLVM text.\<close>
  ML_file "LLVM_Builder.ml"
  
  text \<open>Compiler from intermediate representation to actual LLVM text.\<close>
  ML \<open> structure LLC_Backend = 
    struct
      open LLC_Lib LLC_Intermediate
    
      type vtab = LLVM_Builder.value Symtab.table
      type builder = vtab -> LLVM_Builder.regname -> llc_topr' list -> LLVM_Builder.T -> LLVM_Builder.value option
    
      fun llc_ty _ (TInt w) = LLVM_Builder.mkty_i w
        | llc_ty b (TPtr ty) = LLVM_Builder.mkty_ptr (llc_ty b ty)
        | llc_ty b (TPair (ty1, ty2)) = LLVM_Builder.mkty_struct [llc_ty b ty1, llc_ty b ty2]
        | llc_ty b (TNamed name) = LLVM_Builder.mkty_named b name
      
      
      fun llc_const_to_val b ty CInit = LLVM_Builder.mkc_zeroinit (llc_ty b ty)
        | llc_const_to_val b ty (CInt v) = LLVM_Builder.mkc_i (llc_ty b ty) v
        | llc_const_to_val b ty (CNull) = LLVM_Builder.mkc_null (llc_ty b ty)
      
      fun llc_op_to_val _ vtab (_,OVar x) = the_assert ("Variable not in vtab " ^ x) (Symtab.lookup vtab x)
        | llc_op_to_val b _ (ty,OConst c) = llc_const_to_val b ty c
        
      
      fun dstreg NONE = NONE | dstreg (SOME s) = SOME s
        
      
      fun arith_instr_builder iname vtab dst [OOOp x1, OOOp x2] b = (
        LLVM_Builder.mk_arith_instr iname b dst (llc_op_to_val b vtab x1) (llc_op_to_val b vtab x2) |> SOME
      ) | arith_instr_builder _ _ _ _ _ = raise Fail "arith_instr_builder: invalid arguments"
      
      fun icmp_instr_builder cmpcode vtab dst [OOOp x1, OOOp x2] b = (
        LLVM_Builder.mk_icmp_instr cmpcode b dst (llc_op_to_val b vtab x1) (llc_op_to_val b vtab x2) |> SOME
      ) | icmp_instr_builder _ _ _ _ _ = raise Fail "icmp_instr_builder: invalid arguments"

      fun ptrcmp_instr_builder cmpcode vtab dst [OOOp x1, OOOp x2] b = (
        LLVM_Builder.mk_ptrcmp_instr cmpcode b dst (llc_op_to_val b vtab x1) (llc_op_to_val b vtab x2) |> SOME
      ) | ptrcmp_instr_builder _ _ _ _ _ = raise Fail "icmp_instr_builder: invalid arguments"
            
      fun conv_instr_builder cmpcode vtab dst [OOOp x1, OOType ty] b = (
        LLVM_Builder.mk_conv_instr cmpcode b dst (llc_op_to_val b vtab x1) (llc_ty b ty) |> SOME
      ) | conv_instr_builder _ _ _ _ _ = raise Fail "conv_instr_builder: invalid arguments"

      fun extract_value_builder idx vtab dst [OOOp x1] b = (
        LLVM_Builder.mk_extractvalue b dst (llc_op_to_val b vtab x1) idx |> SOME
      ) | extract_value_builder _ _ _ _ _ = raise Fail "extract_value_builder: invalid arguments"

      fun insert_value_builder idx vtab dst [OOOp x1, OOOp x2] b = (
        LLVM_Builder.mk_insertvalue b dst (llc_op_to_val b vtab x1) (llc_op_to_val b vtab x2) idx |> SOME
      ) | insert_value_builder _ _ _ _ _ = raise Fail "insert_value_builder: invalid arguments"
      
      fun malloc_builder vtab dst [OOType ty, OOOp x] b = (
        LLVM_Builder.mk_malloc b dst (llc_ty b ty) (llc_op_to_val b vtab x) |> SOME
      ) | malloc_builder _ _ _ _ = raise Fail "malloc_builder: invalid arguments"
            
      fun free_builder vtab _ [OOOp x] b = (
        LLVM_Builder.mk_free b (llc_op_to_val b vtab x); NONE
      ) | free_builder _ _ _ _ = raise Fail "free_builder: invalid arguments"

      fun load_builder vtab dst [OOOp x] b = (
        LLVM_Builder.mk_load b dst (llc_op_to_val b vtab x) |> SOME
      ) | load_builder _ _ _ _ = raise Fail "load_builder: invalid arguments"
      
      fun store_builder vtab _ [OOOp x1, OOOp x2] b = (
        LLVM_Builder.mk_store b (llc_op_to_val b vtab x1) (llc_op_to_val b vtab x2); NONE
      ) | store_builder _ _ _ _ = raise Fail "store_builder: invalid arguments"

      fun ofs_ptr_builder vtab dst [OOOp x1, OOOp x2] b = (
        LLVM_Builder.mk_ofs_ptr b dst (llc_op_to_val b vtab x1) (llc_op_to_val b vtab x2) |> SOME
      ) | ofs_ptr_builder _ _ _ _ = raise Fail "ofs_ptr_builder: invalid arguments"
      
      fun gep_idx_builder idx vtab dst [OOOp x1] b = (
        LLVM_Builder.mk_gep_idx b dst (llc_op_to_val b vtab x1) (LLVM_Builder.mkc_iw 32 idx) |> SOME
      ) | gep_idx_builder _ _ _ _ _ = raise Fail "gep_idx_builder: invalid arguments"
      
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
        |> fold (register_prfx_builder "ll_" conv_instr_builder) [
             @{const_name ll_trunc}, @{const_name ll_sext}, @{const_name ll_zext}
          ]  
        |> fold (register_prfx_builder "ll_icmp_" icmp_instr_builder) [
             @{const_name ll_icmp_eq}, @{const_name ll_icmp_ne}, 
             @{const_name ll_icmp_slt}, @{const_name ll_icmp_sle}, 
             @{const_name ll_icmp_ult}, @{const_name ll_icmp_ule} 
          ]  
        |> fold (register_prfx_builder "ll_ptrcmp_" ptrcmp_instr_builder) [
             @{const_name ll_ptrcmp_eq}, @{const_name ll_ptrcmp_ne}
          ]  
        |> register_builder (extract_value_builder 0) @{const_name ll_extract_fst}          
        |> register_builder (extract_value_builder 1) @{const_name ll_extract_snd}          
        |> register_builder (insert_value_builder 0) @{const_name ll_insert_fst}          
        |> register_builder (insert_value_builder 1) @{const_name ll_insert_snd}          

        |> register_builder (malloc_builder) @{const_name ll_malloc}          
        |> register_builder (free_builder) @{const_name ll_free}          
        |> register_builder (load_builder) @{const_name ll_load}          
        |> register_builder (store_builder) @{const_name ll_store}          
      
        |> register_builder (ofs_ptr_builder) @{const_name ll_ofs_ptr}          
        |> register_builder (gep_idx_builder 0) @{const_name ll_gep_fst}          
        |> register_builder (gep_idx_builder 1) @{const_name ll_gep_snd}          
            

      fun vtab_bind (SOME dst) (SOME v) vtab = Symtab.update_new (dst,v) vtab  
        | vtab_bind (SOME dst) NONE _ = raise Fail ("Void instruction bound to value (" ^ dst ^ ") ")
        | vtab_bind _ _ vtab = vtab
        
      fun build_instr b vtab dst (iname,args) = let
        val bld = Symtab.lookup builders iname 
          |> the_assert ("Unknown instruction " ^ iname)
          
        val v = bld vtab (dstreg dst) args b
      in
        vtab_bind dst v vtab
      end  
      
      fun build_call b vtab dst (rty,pname,args) = let
        val args = map (llc_op_to_val b vtab) args
        val rty = map_option (llc_ty b) rty
        
        val v = case rty of 
          NONE => (LLVM_Builder.mk_call_void b pname args; NONE)
        | SOME rty => LLVM_Builder.mk_call b (dstreg dst) rty pname args |> SOME

      in
        vtab_bind dst v vtab
      end
      
      fun build_if build_block b vtab dst (op_cond, blk_then, blk_else) = let
        val l_then = LLVM_Builder.variant_label b "then"
        val l_else = LLVM_Builder.variant_label b "else"
        val l_ctd_if = LLVM_Builder.variant_label b "ctd_if"
      
        val _ = LLVM_Builder.mk_cbr b (llc_op_to_val b vtab op_cond) l_then l_else
        
        val _ = LLVM_Builder.open_bb b l_then 
        val r_then = build_block b vtab blk_then
        val l_then' = LLVM_Builder.mk_br b l_ctd_if
        
        val _ = LLVM_Builder.open_bb b l_else
        val r_else = build_block b vtab blk_else
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
      fun build_while build_block b vtab dst (sv, blk_cond, blk_body, op_init) = let
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
        val r_cond = build_block b vtab' blk_cond
        val r_cond = case r_cond of SOME x => x | NONE => raise Fail "While (bug): Cond-block with no result"
        
        (* cbr r_cond body end *)
        val _ = LLVM_Builder.mk_cbr b r_cond l_body l_end
        
        (* body: *)
        val _ = LLVM_Builder.open_bb b l_body
        val r_body = build_block b vtab' blk_body
        val r_body = case r_body of SOME x => x | NONE => raise Fail "While (bug): Body-block with no result"
        val l_body' = LLVM_Builder.mk_br b l_start
        
        (* add [r_body,l_body'] to \<Phi>-node of l_start *)
        val _ = LLVM_Builder.phi_add b phi_handle (r_body,l_body')
        
        val _ = LLVM_Builder.open_bb b l_end
      in
        vtab_bind dst (SOME v_state) vtab
      end
      
      fun build_cmd _ b vtab dst (CmInstr ia) = build_instr b vtab dst ia
        | build_cmd _ b vtab dst (CmCall na) = build_call b vtab dst na
        | build_cmd ctxt b vtab dst (CmIf bte) = build_if (build_block ctxt) b vtab dst bte
        | build_cmd ctxt b vtab dst (CmWhile cbi) = 
            if Config.get ctxt llc_compile_while then
              build_while (build_block ctxt) b vtab dst cbi
            else
              raise Fail "Direct while compilation disabled! Declare [[llc_compile_while=true]] to enable!"
            
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
    datatype T = Word of string | NWord of string | Space of bool | Newline of bool | Block of int * T list

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
      
      | string_of' (Block (ii,tks)) (i,lt) = let 
          val (strs,(_,lt)) = fold_map string_of' tks (i+ii,lt)
          val str = implode strs
        in (str,(i,lt)) end
      
    (* User Interface *)    
    fun string_of tk = string_of' tk init_state |> fst
            
    (* Basic Functions *)
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
      | PRIM_NAMED of string
    datatype cfield = FLD_NAMED of ctype * string | FLD_ANON of cfield * cfield
         and ctype = CTY_PRIM of cprim | CTY_PTR of ctype | CTY_PAIR of cfield * cfield
  
         
    datatype typedef = TYPEDEF of string * ctype
    fun dest_tydef (TYPEDEF (n,t)) = (n,t)
    val mk_tydef = TYPEDEF

    (* Signature *)
    datatype c_sig = CSIG of ctype option * string * ctype list 
    
    
         
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
      || parse_id >> PRIM_NAMED
  
      fun mk_ptr ty [] = ty
        | mk_ptr ty (_::xs) = CTY_PTR (mk_ptr ty xs)
      
      fun parse_cfield s = (
           parse_ctype -- parse_id --| Parse.$$$ ";" >> FLD_NAMED
        || parse_fld_pair --| Parse.$$$ ";" >> FLD_ANON
      ) s
      and parse_fld_pair s = (pkw "struct" |-- Parse.$$$ "{" |-- parse_cfield -- parse_cfield --| Parse.$$$ "}") s
      and parse_ctype1 s = (
           parse_cprim >> CTY_PRIM
        || parse_fld_pair >> CTY_PAIR
      ) s
      and parse_ctype s = (
        parse_ctype1 -- Scan.repeat (Parse.$$$ "*") >> (fn (ty,ptrs) => mk_ptr ty ptrs)
      ) s
         
      val parse_rtype = parse_ctype >> SOME || pcm "void" >> K NONE
      
      val parse_typedef = pkw "typedef" |-- parse_ctype -- parse_id --| Parse.$$$ ";" >> (fn (ty,name) => mk_tydef (name,ty))
      val parse_typedefs = Scan.repeat parse_typedef
    
    end
    
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
      
    (* Checking *)
    
    fun is_cid_start s = Symbol.is_ascii_letter s orelse s="_"
    fun is_cid_ctd s = is_cid_start s orelse Symbol.is_ascii_digit s
    
    fun is_c_identifier s =
      size s > 0 andalso is_cid_start (String.substring (s, 0, 1)) andalso
      forall_string is_cid_ctd s andalso
      not (Symtab.defined ct_basic_kw_set s);
         
    fun check_identifier name = (is_c_identifier name orelse error ("Invalid identifier " ^ name); ())
      

    fun check_decl (decl,_) name = (Symtab.defined decl name orelse error ("Undeclared type " ^ name); ())
    fun check_complete (decl,def) name = (check_decl (decl,def) name; Symtab.defined def name orelse error ("Incomplete type " ^ name); ())
          
    fun check_type dd (CTY_PRIM (PRIM_NAMED name)) = check_complete dd name
      | check_type _ (CTY_PRIM _) = ()
      | check_type dd (CTY_PTR (CTY_PRIM (PRIM_NAMED name))) = check_decl dd name
      | check_type dd (CTY_PTR t) = check_type dd t
      | check_type dd (CTY_PAIR (f1,f2)) = (check_field dd f1; check_field dd f2)
    and check_field dd (FLD_NAMED (ty,name)) = (check_type dd ty; check_identifier name)
      | check_field dd (FLD_ANON (f1,f2)) = (check_field dd f1; check_field dd f2)
      
    fun is_valid_rty (dd as (_,def)) (CTY_PRIM (PRIM_NAMED name)) = 
          (case Symtab.lookup def name of NONE => false | SOME t => is_valid_rty dd t)
      | is_valid_rty _ (CTY_PRIM _) = true
      | is_valid_rty _ (CTY_PTR _) = true
      | is_valid_rty _ (CTY_PAIR _) = false
    
    fun check_valid_rty dd t = (is_valid_rty dd t orelse error "Aggregate return type not supported by C"; ())  
      
    fun check_rtype _ NONE = ()
      | check_rtype dd (SOME t) = (check_type dd t; check_valid_rty dd t)
      
    fun check_csig dd (CSIG (rty,name,argtys)) = (
      check_rtype dd rty;
      check_identifier name;
      map (check_type dd) argtys;
      ()
    ) handle ERROR msg => error ("Signature " ^ name ^ ": " ^ msg)
      
    (* Check list of type definitions, and create lookup table *)
    fun check_tydefs tydefs = let
      val tydefs = map dest_tydef tydefs
      val _ = map (check_identifier o fst) tydefs
      val decl = Symtab.make_set (map fst tydefs)
            
      fun add_tydef (name,ty) def = let
        val _ = check_identifier name
        val _ = Symtab.defined def name andalso error ("Duplicate typedef " ^ name)
        val _ = check_type (decl,def) ty
        val def = Symtab.update (name,ty) def
      in
        def
      end
    
      val def = fold add_tydef tydefs Symtab.empty
    in
      (decl,def)
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
        | cprim_to_Cs (PRIM_NAMED name) = word name
                                                  
      fun cfield_to_Cs (FLD_NAMED (ty,name)) = block [ctype_to_Cs ty, word name, nword ";"]  
        | cfield_to_Cs (FLD_ANON fs) = block [fldpair_to_Cs fs, nword ";"]
      and fldpair_to_Cs (f1,f2) = block [word "struct", sep, big_braces [line [cfield_to_Cs f1], line [cfield_to_Cs f2]]]
      and ctype_to_Cs (CTY_PRIM t) = cprim_to_Cs t
        | ctype_to_Cs (CTY_PTR t) = block [ctype_to_Cs t, nword "*"]
        | ctype_to_Cs (CTY_PAIR fs) = fldpair_to_Cs fs
        
      fun tydef_to_Cs (TYPEDEF (name,ty)) = block [word "typedef", ctype_to_Cs ty, sep, word name, nword ";"]
      
      val tydefs_to_Cs = fbrks o map tydef_to_Cs
        
      fun rty_to_Cs NONE = word "void" | rty_to_Cs (SOME ty) = ctype_to_Cs ty
      
      fun csig_to_Cs (CSIG (rty,name,partys)) = block [rty_to_Cs rty,fsep,word name,parlist (map ctype_to_Cs partys),word ";"]
                
      val csigs_to_Cs = fbrks o map csig_to_Cs
    end

    
    (* Interface to LLVM types *)
    
    local open LLC_Intermediate in      
      (* TODO: Will loop on recursive types! *)
      fun lty_of_prim _ PRIM_CHAR = TInt 8
        | lty_of_prim _ PRIM_SI8 = TInt 8
        | lty_of_prim _ PRIM_SI16 = TInt 16
        | lty_of_prim _ PRIM_SI32 = TInt 32
        | lty_of_prim _ PRIM_SI64 = TInt 64
        | lty_of_prim _ PRIM_UI8 = TInt 8
        | lty_of_prim _ PRIM_UI16 = TInt 16
        | lty_of_prim _ PRIM_UI32 = TInt 32
        | lty_of_prim _ PRIM_UI64 = TInt 64
        | lty_of_prim ntab (PRIM_NAMED name) = 
            case Symtab.lookup ntab name of 
              NONE => error ("Undefined named type " ^ name)
            | SOME ty => lty_of_ctype ntab ty  
      and lty_of_cfield ntab (FLD_NAMED (ty,_)) = lty_of_ctype ntab ty
        | lty_of_cfield ntab (FLD_ANON (f1,f2)) = TPair (lty_of_cfield ntab f1, lty_of_cfield ntab f2)
      and lty_of_ctype ntab (CTY_PRIM t) = lty_of_prim ntab t               
        | lty_of_ctype ntab (CTY_PTR t) = TPtr (lty_of_ctype ntab t)
        | lty_of_ctype ntab (CTY_PAIR (f1,f2)) = TPair (lty_of_cfield ntab f1, lty_of_cfield ntab f2)
    
        
      fun cty_of_lty (TInt 8) = CTY_PRIM PRIM_SI8
        | cty_of_lty (TInt 16) = CTY_PRIM PRIM_SI16
        | cty_of_lty (TInt 32) = CTY_PRIM PRIM_SI32
        | cty_of_lty (TInt 64) = CTY_PRIM PRIM_SI64
        | cty_of_lty (TInt w) = error ("cty_of_lty: Unsupported integer width " ^ Int.toString w)
        | cty_of_lty (TPtr ty) = CTY_PTR (cty_of_lty ty)
        | cty_of_lty (TPair (ty1,ty2)) = CTY_PAIR (FLD_NAMED (cty_of_lty ty1,"fst"), FLD_NAMED (cty_of_lty ty2,"snd"))
        | cty_of_lty (TNamed name) = error ("cty_of_lty: Named ltys not supported: " ^ name)
        
        
      val cty_of_rlty = map_option cty_of_lty  
        
    end
  end\<close>
  
  
  ML \<open>structure LLC_HeaderGen = struct
    open C_Interface
  
    (* Optional signature *)
    datatype raw_sig = RSIG of ctype option option * string * ctype option list option
    
    datatype sigspec = NAME of string | SIG of raw_sig
    
    
    fun name_of_rsig (RSIG (_,name,_)) = name
    fun name_of_sigspec (NAME name) = name | name_of_sigspec (SIG sg) = name_of_rsig sg
    
    fun short_sig name = NAME name
    fun long_sig sg = SIG sg
    
    (* Parsing of optional signature *)
    fun parse_wildcard p = Parse.underscore >> K NONE || p >> SOME

    fun parse_parlist p = Parse.$$$ "(" |-- Parse.enum "," p --| Parse.$$$ ")"
        
    val parse_long_sig = 
      parse_wildcard parse_rtype -- parse_id -- Scan.option (parse_parlist (parse_wildcard parse_ctype))
      >> (fn ((r,n),p) => long_sig (RSIG (r,n,p)))
                           
    val parse_short_sig = parse_id >> short_sig  
    val parse_sig = parse_long_sig || parse_short_sig
      
    val parse_raw_sig = Parse.position (Parse.cartouche || Parse.short_ident || Parse.string)
    val parse_raw_tydefs = Parse.position Parse.cartouche
    
    val check_raw_tydefs = Parser_Util.parse_inner ct_kws parse_typedefs
    val check_raw_sig = Parser_Util.parse_inner ct_kws parse_sig
    
    
    fun check_sigs dd sigs = let
      fun add_sig (sg as RSIG (rt,name,args)) tab = let  
        val _ = map_option (check_rtype dd) rt
        val _ = map_option (map (map_option (check_type dd))) args
        val _ = check_identifier name
        
        val _ = Symtab.defined tab name andalso error ("Duplicate name")
        
        val tab = Symtab.update (name,sg) tab
        
      in tab end handle ERROR msg => error ("Signature " ^ name ^ ": " ^ msg)
        
      val tab = fold add_sig sigs Symtab.empty
    
    in
      tab
    end 
    
    fun match_sig dd (rty,args) (RSIG (crty,name,cargs)) = let
      val argtys = map fst args
      val crty = the_default (cty_of_rlty rty) crty
      
      val cargs = the_default (replicate (length argtys) NONE) cargs
    
      val _ = length argtys = length cargs orelse error ("Wrong number of arguments")
      
      val cargs = map (fn (lty,cty) => the_default (cty_of_lty lty) cty) (argtys ~~ cargs)
      
      (* Consistency check *)
      fun check_match (lty,cty) = if lty_of_ctype (snd dd) cty = lty then () else error "Type mismatch" (* TODO: More specific error message *)
      
      val _ = case (rty,crty) of 
        (NONE,NONE) => () 
      | (SOME lty, SOME cty) => check_match (lty,cty)
      | _ => error "Return type voidness mismatch"
      
      val _ = map check_match (argtys ~~ cargs)
    
    in
      CSIG (crty,name,cargs)
    end handle ERROR msg => error ("Signature " ^ name ^ ": " ^ msg)
    
    
    fun make_header hfname tydefs sigspecs eqns = let
      val sigs = map_filter (fn (NAME _) => NONE | (SIG sg) => SOME sg) sigspecs
    
      val dd = check_tydefs tydefs
      val stab = check_sigs dd sigs

      fun make_hd_id name = let 
        val name = Symbol.explode name |> filter is_cid_ctd |> map Symbol.to_ascii_upper |> implode
        val name = "_" ^ name ^ "_H"
      in name end  
        
      val hfname = make_hd_id hfname
      
            
      fun process_eqn (LLC_Intermediate.EQN (rty,name,args,_)) = case Symtab.lookup stab name of
        NONE => NONE
      | SOME sg => SOME (match_sig dd (rty,args) sg)
      
      val csigs = map_filter process_eqn eqns
      
      val _ = map (check_csig dd) csigs
      
      val h_to_C = let
        open Simple_PP
        val hfsym = word hfname
      in block [
          (* TODO: Include information for which version of ll-file this has been generated! *)
          line [word "// Generated by Isabelle-LLVM. Do not modify."],
          line [word "#ifndef", hfsym],
          line [word "#define", hfsym, word "1"],
          fbrk, fbrk,
          tydefs_to_Cs tydefs,
          fbrk, fbrk,
          csigs_to_Cs csigs,
          fbrk, fbrk,
          line [word "#endif"]
        ]
      end
      
    in
      case csigs of [] => NONE | _ => SOME (Simple_PP.string_of h_to_C)
    end
    
    
  end    
    
\<close>    
 
(*
oops   
    
    local open LLC_Intermediate Simple_PP in      
         

        

          
        fun resolve_lty_def (name,cty) ntab = 
          Symtab.update_new (name,lty_of_ctype ntab cty) ntab
          handle Symtab.DUP _ => error ("Duplicate named type " ^ name)

        fun resolve_lty_defs defs = fold resolve_lty_def defs Symtab.empty
        
        (*
        xxx, ctd here: 
          Allow named types for function return types and arguments.
          Look them up in ntab, and check for compatibility!
        *)
          
          
          
      end
      
      val parse_tyn = parse_id >> SOME || Parse.underscore >> (fn _ => NONE)
      val parse_rtyn = Parse.$$$ "void" >> (K (SOME NONE)) || parse_tyn >> map_option SOME
      val parse_parlist = Parse.$$$ "(" |-- Parse.enum "," parse_tyn --| Parse.$$$ ")"
      val parse_long_sig = parse_rtyn -- parse_id -- parse_parlist
        >> (fn ((rty,name),pars) => (name,RSIG (rty,SOME pars)))
      
      val parse_short_sig = Parse.short_ident >> (fn name => (name,RSIG (NONE,NONE)))
      val parse_sig = parse_long_sig || parse_short_sig
      
            
      
      
      
      
      val parse_sig_spec = Parse.position (Parse.cartouche || Parse.short_ident || Parse.string)
      val parse_tydefs_spec = Parse.position Parse.cartouche

            

      val check_sig_spec = parse_inner ct_kws parse_sig
      val check_tydefs_spec = parse_inner ct_kws parse_typedefs
      
      fun check_ctype tdtab lty cty = let
        val lty' = lty_of_ctype tdtab cty
        val _ = lty = lty' orelse error "Declared ctype does not match ltype" (* TODO: Better error message *)
      in
        cty
      end
      
      fun mk_ctype tdtab (lty, NONE) = check_ctype tdtab lty (cty_of_lty lty)
        | mk_ctype tdtab (lty, SOME name) = check_ctype tdtab lty (CTY_PRIM (PRIM_NAMED name))
      
      fun mk_rtype _ NONE NONE = NONE
        | mk_rtype _ NONE (SOME NONE) = NONE
        | mk_rtype _ NONE (SOME (SOME _)) = error "Return type declared for void function"
        | mk_rtype _ (SOME _) (SOME NONE) = error "Void type for non-void function"
        | mk_rtype tdtab (SOME lty) NONE = SOME (mk_ctype tdtab (lty, NONE))
        | mk_rtype tdtab (SOME lty) (SOME (SOME name)) = SOME (mk_ctype tdtab (lty,SOME name))
        
      fun mk_csig tdtab (LLC_Intermediate.EQN (rty,name,pars,_), RSIG (rtyn,partyns)) = let
        val rcty = mk_rtype tdtab rty rtyn
        
        val partyns = the_default (map (K NONE) pars) partyns
        val pars = map fst pars
        
        val _ = length pars = length partyns orelse error "Parameter number mismatch"
        val cpartys = (pars ~~ partyns) |> map (mk_ctype tdtab)
        
      in
        CSIG (rcty,name,cpartys)
      end handle ERROR msg => error ("Signature for " ^ name ^ ": " ^ msg)
        
      fun is_valid_rty tdtab (CTY_PRIM (PRIM_NAMED name)) = 
            (case Symtab.lookup tdtab name of NONE => false | SOME t => is_valid_rty tdtab t)
            
        | is_valid_rty _ (CTY_PRIM _) = true
        | is_valid_rty _ (CTY_PTR _) = true
        | is_valid_rty _ (CTY_PAIR _) = false
        
      fun is_valid_rty' tdtab = the_default true o map_option (is_valid_rty tdtab)
      
      fun check_csig tdtab (CSIG (rty,name,_)) = let
        (* TODO: Are there more restrictions? *)
        
        fun err msg = error ("In function " ^ name ^ ": " ^ msg)
      
        val _ = is_valid_rty' tdtab rty orelse err "Complex return type not supported by C"
        val _ = is_c_identifier name orelse err "Invalid name"
      in () end  
      
      fun check_tydef_name (name,_) = ( is_c_identifier name orelse error ("Invalid name " ^ name)  ;())
      
                
      fun make_header hfname eqns sigtab tydefs = let
      
        fun is_valid_cidchar s = 
          Symbol.is_ascii_letter s 
          orelse Symbol.is_ascii_digit s
          orelse s="_"

        fun make_hd_id name = let 
          val name = Symbol.explode name |> filter is_valid_cidchar |> map Symbol.to_ascii_upper |> implode
          val name = "_" ^ name ^ "_H"
        in name end  
          
        val hfname = make_hd_id hfname
      
        val _ = map check_tydef_name tydefs
        
        val tdtab = resolve_lty_defs tydefs
        
        (* Filter equations for which header entry is to be generated *)
        val eqns = map_filter (fn eqn as LLC_Intermediate.EQN (_,name,_,_) => case Symtab.lookup sigtab name of
            NONE => NONE
          | SOME sg => SOME (eqn,sg)
        ) eqns

        (* Generate header entries *)
        val csigs = map (mk_csig tdtab) eqns
        
        val _ = map (check_csig (Symtab.make tydefs)) csigs
        
        (* TODO: Check that only ASCII-Names are used *)

        val h_to_C = let
          open Simple_PP
          val hfsym = word ("_"^hfname^"_H")
        in block [
            (* TODO: Include information for which version of ll-file this has been generated! *)
            line [word "// Generated by Isabelle-LLVM. Do not modify."],
            line [word "#ifndef", hfsym],
            line [word "#define", hfsym, word "1"],
            fbrk, fbrk,
            tydefs_to_Cs tydefs,
            fbrk, fbrk,
            csigs_to_Cs csigs,
            fbrk, fbrk,
            line [word "#endif"]
          ]
        end
      
      in
        case csigs of [] => NONE | _ => SOME (Simple_PP.string_of h_to_C)
      end
  
    end
  \<close>
  *)
  
end
