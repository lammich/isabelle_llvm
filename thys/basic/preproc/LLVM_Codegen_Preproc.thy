section \<open>Preprocessor and Code-Generator User Interface\<close>
theory LLVM_Codegen_Preproc
imports 
  "../kernel/LLVM_Codegen"
  "Monadify"
  "../../lib/Definition_Utils" 
  "../../lib/Named_Simpsets" 
keywords "export_llvm" "llvm_deps" :: thy_decl
begin

  subsection \<open>Fixed-Point Unfolding Setup\<close>

  declaration \<open>fn _ => Definition_Utils.declare_extraction_group @{binding LLVM} #> snd\<close>
  declaration \<open>fn _ => Definition_Utils.declare_extraction_group @{binding LLVM_while} #> snd\<close>
    
  declaration \<open> fn _ =>
    Definition_Utils.add_extraction (@{extraction_group LLVM_while},\<^here>) {
      pattern = Logic.varify_global @{term "llc_while b body"},
      gen_thm = @{thm gen_code_thm_llc_while},
      gen_tac = K (K no_tac)
    }
  \<close>

  
  lemma REC_unfold_extr:
    assumes DEF: "f \<equiv> REC F"
    assumes MONO: "\<And>x. M_mono' (\<lambda>fa. F fa x)"
    shows "f = F f"
    using DEF MONO REC_unfold by blast
  
  declaration \<open>fn _ =>
    Definition_Utils.add_extraction (@{extraction_group LLVM},\<^here>) {
      pattern = Logic.varify_global @{term "REC (B::('a \<Rightarrow> 'b llM) \<Rightarrow> 'a \<Rightarrow> 'b llM)"},
      gen_thm = @{thm REC_unfold_extr},
      gen_tac = Partial_Function.mono_tac
    }
  \<close>

subsection \<open>Preprocessor\<close>  
  text \<open>
    The actual code generator expects a set of monomorphic, well-shaped equations.
    The preprocessor processes user specified equations, monomorphizes them and 
    brings them into the right shape.
  \<close>
  
  named_simpset llvm_pre_simp = HOL_ss

  lemmas [named_ss llvm_pre_simp cong] = refl[of "M_CONST c" for c]

  (* TODO: Also add preprocessing step for complex constant defs *)  
  attribute_setup llvm_pre_simp = \<open>
    Attrib.add_del 
      (Named_Simpsets.add_attr @{named_simpset llvm_pre_simp}) 
      (Named_Simpsets.del_attr @{named_simpset llvm_pre_simp})
  \<close>
    
  
  lemma llvm_inline_bind_laws[llvm_pre_simp]:
    "Mbind m Mreturn = m"
    "Mbind (Mbind m (\<lambda>x. f x)) g = Mbind m (\<lambda>x. Mbind (f x) g)"
    by auto
  
  lemma unit_meta_eq: "x \<equiv> ()" by simp
  
  lemma pull_lambda_case: "(case x of (a,b) \<Rightarrow> \<lambda>y. t a b y) = (\<lambda>y. case x of (a,b) \<Rightarrow> t a b y)"
    apply (rule ext) apply (cases x) by auto

  text \<open>First part of setup, for processing of code and inline theorems\<close>  
  
  named_theorems llvm_code_raw \<open>Isabelle-LLVM code theorems\<close>
  
  ML \<open> structure LLC_Preprocessor = struct
    open LLC_Lib
        
    val cfg_llvm_preproc_timing = Attrib.setup_config_bool @{binding llvm_preproc_timing} (K false)
    
    structure Monadify = struct 
      structure BT = Gen_Monadify_Cong_Basis ()
      open BT

      fun mk_return x = @{mk_term "Mreturn ?x ::_ llM"}
      fun mk_bind m f = @{mk_term "Mbind ?m ?f ::_ llM"}
    
      fun dest_return @{mpat "Mreturn ?x ::_ llM"} = SOME x | dest_return _ = NONE
      fun dest_bind @{mpat "Mbind ?m ?f ::_ llM"} = SOME (m,f) | dest_bind _ = NONE
      
      
      val dest_monadT = try dest_llM  
      (*fun dest_monadT (Type (@{type_name M},[T,@{typ llvm_memory},@{typ "llvm_macc"}])) = SOME T | dest_monadT _ = NONE*)

      
      fun strip_op _ @{mpat \<open>llc_par ?fa ?fb ?a ?b\<close>} = (@{mk_term "llc_par ?fa ?fb"},[a,b])
      | strip_op ctxt t = BT.strip_op ctxt t  
      
      
      val bind_return_thm = @{lemma "Mbind m Mreturn = m" by simp}
      val return_bind_thm = @{lemma "Mbind (Mreturn x) f = f x" by simp}
      val bind_bind_thm = @{lemma "Mbind (Mbind m (\<lambda>x. f x)) g = Mbind m (\<lambda>x. Mbind (f x) g)" by simp}
      
      structure T = Gen_Monadify (
        val mk_return = mk_return
        val mk_bind = mk_bind
        val dest_return = dest_return
        val dest_bind = dest_bind
        val dest_monadT = dest_monadT
        val strip_op = strip_op
        val bind_return_thm = bind_return_thm
        val return_bind_thm = return_bind_thm
        val bind_bind_thm = bind_bind_thm
      )
      open T
      
    end        
    
    (********* Identification of complex constant heads *)
    (* Get head of equation and conversion on this head. 
      If inline is set, TYPE() and higher-order variable arguments are treated like normal first-order arguments
    *)
    fun get_eqn_head inline t = let
      open Conv
      
      fun app c (h,cnv) = (h, fn cc => c (cnv cc))
      
      fun is_typarg @{mpat \<open>TYPE(_)\<close>} = true
        | is_typarg _ = false
      
      fun is_fo_argument x = 
        (is_Var x orelse is_Free x orelse (inline andalso is_typarg x))
        andalso (inline orelse not (Monadify.is_ho_operand x))
      
      
      fun aux @{mpat \<open>Trueprop ?t\<close>} = app arg_conv (aux t)
        | aux @{mpat \<open>?lhs = _\<close>} = app arg1_conv (aux lhs)
        | aux @{mpat \<open>?lhs \<equiv> _\<close>} = app arg1_conv (aux lhs)
        | aux (t as f$x) = (
            if is_fo_argument x then app fun_conv (aux f) 
            else (t,I)
          )  
        | aux t = (t,I)
    
    in
      aux t
    end
    
    (* Handle adding of M_CONST and constant registration to monadifier *)
    
    fun gen_prep_code_eq h_reg t_reg inline thm context = let
      val t = Thm.prop_of thm
      val _ = is_eqn t orelse raise THM ("prep_code_eq: not an equation",~1,[thm])
    
      val (h,cnv) = get_eqn_head inline t 
      
      fun prep (thm,context) = let
        open Conv
        val thm = Conv.fconv_rule (cnv (rewr_conv @{thm M_CONST_def[symmetric]})) thm
        val context = h_reg h context
      in 
        (thm,context)
      end
      
      fun need_prep (Const _) = false
        | need_prep (Free _) = false
        | need_prep @{mpat \<open>M_CONST _\<close>} = false
        | need_prep _ = true

      val (thm,context) = (thm,context) |> need_prep h ? prep  
              
      val context = t_reg thm context
    in
      (context)
    end
    
    val gen_prep_code_eq_add = gen_prep_code_eq (Monadify.prepare_add_const_decl true)
    val gen_prep_code_eq_del = gen_prep_code_eq (Monadify.prepare_remove_const_decl true)

    val add_inline_eq = gen_prep_code_eq_add (Named_Simpsets.add_simp @{named_simpset llvm_pre_simp}) true
    val del_inline_eq = gen_prep_code_eq_del (Named_Simpsets.del_simp @{named_simpset llvm_pre_simp}) true

    val add_code_eq = gen_prep_code_eq_add (Named_Theorems.add_thm @{named_theorems llvm_code_raw}) false
    val del_code_eq = gen_prep_code_eq_del (Named_Theorems.del_thm @{named_theorems llvm_code_raw}) false
        
    local 
      val to_attr = Thm.declaration_attribute 
    in
      val add_inline_eq_attr = to_attr add_inline_eq
      val del_inline_eq_attr = to_attr del_inline_eq 
  
      val add_code_eq_attr = to_attr add_code_eq 
      val del_code_eq_attr = to_attr del_code_eq 
    end
    
    
    (*    
    fun prep_code_eq thm context = let
      val t = Thm.prop_of thm
      val _ = is_eqn t orelse raise THM ("prep_code_eq: not an equation",~1,[thm])
    
      val (h,cnv) = get_eqn_head t
      
      fun prep context = let
        open Conv
        val thm = Conv.fconv_rule (cnv (rewr_conv @{thm M_CONST_def[symmetric]})) thm
        val context = Monadify.prepare_add_const_decl true h context
      in 
        (thm,context)
      end
      
      
      fun need_prep (Const _) = false
        | need_prep (Free _) = false
        | need_prep @{mpat \<open>M_CONST _\<close>} = false
        | need_prep _ = true
      
    in
      if need_prep h then prep context
      else (thm,context)
    end
    
    fun prep_code_attr attr = Thm.mixed_attribute (fn (context,thm) => let
      val (thm,context) = prep_code_eq thm context
      val (thm,context) = Thm.apply_attribute attr thm context
    in
      (context,thm)
    end)
    *)
    
  end
  \<close>      
   
  attribute_setup llvm_inline = \<open>
    Attrib.add_del 
      (LLC_Preprocessor.add_inline_eq_attr) 
      (LLC_Preprocessor.del_inline_eq_attr)
  \<close>
  
  attribute_setup llvm_code = \<open>
    Attrib.add_del 
      (LLC_Preprocessor.add_code_eq_attr) 
      (LLC_Preprocessor.del_code_eq_attr)
  \<close>
  
  
  
  ML \<open> structure LLC_Preprocessor = struct
    open LLC_Preprocessor  
    (********* Normalization of code theorems *)
    

    fun cthm_inline ctxt thm = let
      val ctxt = Named_Simpsets.put @{named_simpset llvm_pre_simp} ctxt
    in
      (* TODO: Simplifier.rewrite may introduce beta redexes. 
        Currently we eliminate them right away. Or is it OK to have beta-redexes? *)
      Conv.fconv_rule (rhs_conv (Simplifier.rewrite ctxt) then_conv Thm.beta_conversion true) thm
    end
  
    val cthm_monadify = Conv.fconv_rule o (rhs_conv o Monadify.monadify_conv)
          
    val inline_iteration_limit = Attrib.setup_config_int @{binding inline_iteration_limit} (K ~1)
    
    fun monadify_inline_cthm ctxt thm = let
      fun rpt 0 thm' = raise THM ("inline_iteration_limit exceeded",~1,[thm,thm'])
        | rpt n thm = let
        val thm' = thm |> cthm_monadify ctxt |> cthm_inline ctxt
      in
        if Thm.eq_thm_prop (thm,thm') then thm 
        else rpt (n-1) thm'
      end
      
      val it_limit = Config.get ctxt inline_iteration_limit
    in
      thm 
      |> cthm_inline ctxt
      |> rpt it_limit
    end  
    
    (*
      Bring code theorem into parseable format. To be applied after inlining, 
        immediately before parsing.
      
      Applies eta-expansion, return-expansion, and converts \<equiv> to =.
      Finally, it will replace unit-binds by () constants and anonymous bind.
      
      May fail on non-well-formed theorems.
    *)
    
    fun is_valid_fname t = is_ground_term t andalso not (LLC_Compiler.is_llvm_instr_t t)
    fun check_valid_fname t = is_valid_fname t orelse raise TYPE("Expected (ground) function name",[fastype_of t],[t])
    
    
    fun cthm_format ctxt thm = let
      fun check_valid_op t = assert_ground_term t
    
      fun check_valid_op' (t as @{mpat "llc_par ?f ?g"}) = (
        is_valid_fname f andalso is_valid_fname g orelse 
          raise TERM("cthm_format: llc_par expects function names",[t]);
          t
        )
        | check_valid_op' t = (check_valid_op t; t)
    
      fun normalize_bind1 t = let
        val (f,args) = Monadify.strip_op ctxt t
        val _ = check_valid_op' f

        val args_is_M = fastype_of f |> binder_types |> map (is_llM o body_type)
                
        val _ = length args_is_M = length args orelse raise TYPE ("cthm_format: All arguments must be explicit", [fastype_of f], [t])
        
        val args = map2 (fn isM => isM?(normalize o expand_eta_all)) args_is_M args
        
      in
        list_comb (f, args)
      end  
        
      and normalize @{mpat "Mbind ?m ?f"} = let
          val m = normalize_bind1 m
          val f = (*ensure_abs f*) expand_eta_all f |> normalize
        in @{mk_term "Mbind ?m ?f"} end
      | normalize (Abs (x,T,t)) = Abs (x,T,normalize t)
      | normalize (t as @{mpat "Mreturn _"}) = t
      | normalize t = let val t = normalize_bind1 t in @{mk_term "Mbind ?t (\<lambda>x. Mreturn x)"} end
    
      fun normalize_eq @{mpat "Trueprop (?a = ?b)"} = let val b = normalize b in @{mk_term "Trueprop (?a = ?b)"} end
        | normalize_eq @{mpat "?a \<equiv> ?b"} = let val b = normalize b in @{mk_term "?a \<equiv> ?b"} end
        | normalize_eq t = raise TERM ("format_code_thm: normalize_eq", [t])
    
      fun norm_tac ctxt = ALLGOALS (simp_tac (put_simpset HOL_ss ctxt addsimps @{thms M_monad_laws M_CONST_def}))
  
      fun cthm_norm_lambda ctxt thm = let
        val thm = Local_Defs.unfold ctxt @{thms pull_lambda_case} thm
      
        (*fun r thm = case Thm.concl_of thm of
          @{mpat "Trueprop (_ = (\<lambda>_. _))"} => r (thm RS @{thm fun_cong})
        | @{mpat "_ \<equiv> (\<lambda>_. _)"} => r (thm RS @{thm meta_fun_cong})
        | _ => thm
        *)
        
        fun r thm = case try (fn () => (thm RS @{thm fun_cong})) () of
          NONE => thm
        | SOME thm => r thm  
        
      in
        r thm
      end
      
    in
      thm 
      |> (simplify (put_simpset HOL_ss ctxt addsimps @{thms M_monad_laws atomize_eq}))
      |> cthm_norm_lambda ctxt
      |> (Conv.fconv_rule (Refine_Util.f_tac_conv ctxt normalize_eq (norm_tac)))
      |> (Conv.fconv_rule (Conv.top_sweep_conv (K (Conv.rewr_conv @{thm unit_meta_eq})) ctxt))
    end
    
    (********* Gathering of code equations *)
    (* TODO: Use net *)

    
    fun dep_prep_code_thm thm = let
      val ((_,(c,_)),_) = LLC_Compiler.analyze_eqn_thm thm
    in
      (c,thm)
    end
    
    fun dep_try_instantiate_code_thm ctxt c (l,thm) = let
      val c = Thm.cterm_of ctxt c
      val incr = Thm.maxidx_of_cterm c + 1
      val thm = Thm.incr_indexes incr thm
      val l = Thm.cterm_of ctxt l |> Thm.incr_indexes_cterm incr
    
    in
      case try Thm.match (l,c) of
        NONE => NONE
      | SOME inst => SOME (Thm.instantiate inst thm)
    end
    
    fun dep_find_code_thm ctxt pthms c = 
      case get_first (dep_try_instantiate_code_thm ctxt c) pthms of
        SOME eqn => eqn
      | NONE => raise TERM ("No code equation",[c])
    
    val cmd_name_prefix = Long_Name.qualify (Long_Name.qualifier @{const_name ll_add}) "ll_"
    val comb_name_prefix = Long_Name.qualify (Long_Name.qualifier @{const_name llc_while}) "llc_"
        
    fun dep_is_ll_comb_name name =
             name = @{const_name Mbind}
      orelse name = @{const_name Mreturn}
      orelse String.isPrefix cmd_name_prefix name
      orelse String.isPrefix comb_name_prefix name
      
    fun dep_is_ll_comb_t (Const (name,_)) = dep_is_ll_comb_name name
      | dep_is_ll_comb_t _ = false
      
      
    fun fold_aterms_mc f (t as @{mpat \<open>M_CONST _\<close>}) = f t
      | fold_aterms_mc f (t $ u) = fold_aterms_mc f t #> fold_aterms_mc f u
      | fold_aterms_mc f (Abs (_, _, t)) = fold_aterms_mc f t
      | fold_aterms_mc f a = f a;
      
      
    fun dep_is_call_const (Bound _) = false
      | dep_is_call_const t = let 
          val T = fastype_of t 
        in
          not (dep_is_ll_comb_t t)      (* Not an internal name *)
          andalso is_llM (body_type T)  (* Yields a monadic result *)
        end
      
    (*fun dep_is_call_const t = case try dest_head t of
      NONE => false
    | SOME (name,T) => 
                not (dep_is_ll_comb_name name) (* Not an internal name *)
        andalso is_llM (body_type T)           (* Yields a monadic result *)
        andalso not (exists (exists_subtype is_llM) (binder_types T)) (* No monadic parameters *)
    *)
      
    fun calls_of_cthm thm = fold_aterms_mc 
      (fn t => dep_is_call_const t?cons t) 
      (rhs_of_eqn (Thm.prop_of thm))
      []
    
    fun default_extractions ctxt = 
        Definition_Utils.get_extraction_group ctxt @{extraction_group LLVM}
      |> (not (Config.get ctxt llc_compile_while) ? 
            append (Definition_Utils.get_extraction_group ctxt @{extraction_group LLVM_while}))  
    
    fun gather_code_thms roots lthy = let
      val thy = Proof_Context.theory_of lthy
      val pthms = Named_Theorems.get lthy @{named_theorems llvm_code_raw}
        |> map dep_prep_code_thm
        |> Refine_Util.subsume_sort fst thy
    
        
      val tim = Config.get lthy cfg_llvm_preproc_timing  
        
      fun trace msg = if tim then msg () |> tracing else ()
      
      fun process_root c (ctab, lthy) = let
        val _ = check_valid_fname c
        val basename = name_of_head c |> Long_Name.base_name
      in
        case Termtab.lookup ctab c of
          SOME _ => (ctab, lthy)
        | NONE => let
            val _ = trace (fn () => "Processing " ^ basename)
            val startt = Time.now ()
        
            (* Get code theorem and inline it *)
            val teqn = dep_find_code_thm lthy pthms c |> monadify_inline_cthm lthy
            
            (* Extract recursion equations *)
            val exs = default_extractions lthy
            
            val ((teqn,add_eqns,_),lthy) = Definition_Utils.extract_recursion_eqs exs basename teqn lthy
            val teqns = teqn::add_eqns
            
            (* Inline and format again *)
            val teqns = map (monadify_inline_cthm lthy #> cthm_format lthy) teqns

            (* Update table *)
            val ctab = fold Termtab.update_new (map dep_prep_code_thm teqns) ctab
                          
            (* Find calls *)
            val calls = map calls_of_cthm teqns |> flat
            
            val stopt = Time.now()
            val _ = trace (fn () => "Done " ^ basename ^ ": " ^ Time.toString (stopt - startt))

            
            (* Recurse *)

            (** Recursion error traceback message *)                            
            fun msg () = let
              val p_msg = Pretty.block[ Pretty.str "from ", Syntax.pretty_term lthy c ]
              val p_eqns = map (Thm.pretty_thm lthy) teqns |> Pretty.fbreaks |> Pretty.block
              
              val p = Pretty.block [p_msg, Pretty.fbrk, p_eqns]
            in
              Pretty.string_of p
            end
            
            val (ctab,lthy) = trace_exn msg (fold process_root calls) (ctab,lthy)
          in
            (ctab, lthy)
          end
      end 
      
      val (ctab,lthy) = fold process_root roots (Termtab.empty,lthy)
      val thms = Termtab.dest ctab |> map snd
      
    in
      (thms,lthy)
    end
      
  end
  \<close>

  declaration \<open>K (LLC_Preprocessor.Monadify.prepare_add_const_decl false @{term "numeral a"})\<close>  
  declaration \<open>K (LLC_Preprocessor.Monadify.prepare_add_const_decl false @{term "double_of_word (numeral a)"})\<close>  
  
  attribute_setup llvm_dbg_pre_monadified = \<open>Scan.succeed (
    Thm.rule_attribute [] (LLC_Preprocessor.cthm_monadify o Context.proof_of)
  )\<close>
  
  attribute_setup llvm_dbg_pre_inlined = \<open>Scan.succeed (
    Thm.rule_attribute [] (LLC_Preprocessor.cthm_inline o Context.proof_of)
  )\<close>
  
  attribute_setup llvm_dbg_pre_monadify_inlined = \<open>Scan.succeed (
    Thm.rule_attribute [] (LLC_Preprocessor.monadify_inline_cthm o Context.proof_of)
  )\<close>
  
  attribute_setup llvm_dbg_pre_formatted = \<open>Scan.succeed (
    Thm.rule_attribute [] (LLC_Preprocessor.cthm_format o Context.proof_of)
  )\<close>
  
  attribute_setup llvm_dbg_preprocessed = \<open>Scan.succeed (
    Thm.rule_attribute [] (fn context => (
      let val ctxt = Context.proof_of context 
      in LLC_Preprocessor.monadify_inline_cthm ctxt #> LLC_Preprocessor.cthm_format ctxt 
    end))
  )\<close>
  
  attribute_setup llvm_dbg_instantiated = \<open>Args.term >> (fn c => 
    Thm.rule_attribute [] (fn context => fn thm =>
      let 
        open LLC_Preprocessor
        val ctxt = Context.proof_of context 
        val pthm = dep_prep_code_thm thm        
        val thm = the (dep_try_instantiate_code_thm ctxt c pthm)
        
      in 
        thm   
      end
    )
  )\<close>
  
declare [[Pure.of]]
    
subsection \<open>Code Generator Driver\<close>  
  text \<open>
    The driver combines preeprocessing and code generation, 
    and defines the user interface of the code generator, namely the commands
    @{command export_llvm} and @{command llvm_deps}.
  \<close>
  
  ML \<open> structure LLC_Driver 
    = struct
    
      val cfg_llvm_debug = Attrib.setup_config_bool @{binding llvm_debug} (K false)
      val cfg_llvm_timing = Attrib.setup_config_bool @{binding llvm_timing} (K false)
      val cfg_llvm_gen_header = Attrib.setup_config_bool @{binding llvm_gen_header} (K true)
    
      fun pretty_cthms ctxt cthms = let 
        val ctxt = Config.put Syntax_Trans.eta_contract false ctxt      
      in Pretty.big_list "Code Theorems" (map (Thm.pretty_thm ctxt) cthms) end

      fun pretty_ftab_entry ctxt (t,n) = Pretty.block [
        Syntax.pretty_term ctxt t, Pretty.brk 1, Pretty.str ":: ", Syntax.pretty_typ ctxt (fastype_of t), 
        Pretty.brk 1,Pretty.str "\<rightarrow>",Pretty.brk 1, Pretty.str n
      ]
          
      fun pretty_ftab ctxt ftab = Pretty.big_list "Symbol table:" 
        (map (pretty_ftab_entry ctxt) (Termtab.dest ftab))
                
        
        
        
      fun consts_to_llvm hfname cns tydefs nt_ovr lthy = let
        val dbg = Config.get lthy cfg_llvm_debug
        val tim = Config.get lthy cfg_llvm_timing
        val gen_header = Config.get lthy cfg_llvm_gen_header
        fun trace s = if dbg then Pretty.string_of (s ()) |> tracing else ()
                                       
        fun trtimed msg f x = case (dbg,tim) of
          (_,true) => timeap_msg msg f x
        | (true,_) => (trace (fn () => Pretty.str msg); f x)
        | _ => f x
        
        val (cthms,lthy) = trtimed "Gathering code theorems" (LLC_Preprocessor.gather_code_thms (map fst cns)) lthy
        val _ = trace (fn () => pretty_cthms lthy cthms)
        
        fun cmp_fixes () = let
        
          fun fx (_,NONE) = NONE
            | fx (cn, SOME csig) = SOME (cn,C_Interface.name_of_sig csig)
        
          val fixes = map_filter fx cns
        in fixes end
        
        
        val fixes = trtimed "Computing fixes table" cmp_fixes ()
        (*val _ = trace (fn () => pretty_ftab lthy ftab)*)
                  
        val (tys,eqns) = trtimed "Translating code theorems to IL" (LLC_Compiler.parse_cthms fixes nt_ovr cthms) lthy
        val _ = trace (fn () => LLC_Intermediate.pretty_llc (tys,eqns))
        
        val _ = trace (fn () => Pretty.str "Writing LLVM")
        val res = trtimed "Writing LLVM" (LLC_Backend.compile_to_llvm lthy) (tys,eqns)
        
        val hdres = if gen_header then let
            fun mk_hd eqns = let
              val sigspecs = map_filter snd cns
              fun dest_sig sg = (C_Interface.name_of_sig sg, sg) 
          
              val sigtab = Symtab.make (map dest_sig sigspecs)
              
              fun match_eqn (eqn as LLC_Intermediate.EQN (_,name,_,_)) = case Symtab.lookup sigtab name of
                NONE => NONE
              | SOME sg => SOME (eqn,sg)  
              
              val eqnsxsigs = map_filter match_eqn eqns
              
              val hdres = LLC_HeaderGen.make_header hfname tydefs tys eqnsxsigs
            in hdres end
        
            val hdres = trtimed "Preparing Header" mk_hd eqns
          in hdres end
          else NONE
        
        
      in
        ((cthms,res,hdres), lthy)
      end
      
      local
        val using_master_directory =
          File.full_path o Resources.master_directory o Proof_Context.theory_of;
          
        fun prepare_path ctxt (s,pos) = let
          val _ = Position.report pos (Markup.language_path false);
          val path = Path.explode s;
          val _ = Position.report pos (Markup.path (Path.implode path));
          val path = using_master_directory ctxt path
        in path end
      
        fun remove_ext ext p = let val (p',ext') = Path.split_ext p in if ext=ext' then p' else p end
        fun remove_all_ext p = case Path.split_ext p of (p,"") => p | (p,_) => remove_all_ext p
        
        fun prepare_hpath _ NONE = ("HEADER_NAME",NONE)
          | prepare_hpath ctxt (SOME spos) = let
              val path = prepare_path ctxt spos
                |> remove_ext "ll"
                |> Path.ext "h"
              val hfname = remove_all_ext (Path.base path) |> Path.implode
            in
              (hfname,SOME path)
            end
        
        
        fun write_out NONE s = writeln s
          | write_out (SOME path) s = File.write path s
          
        (*  
        (*
          Contains a name (used as name for generated LLVM function) and 
          an optional signature (used for header file generation).
          
          Note that this information is redundant, the name in the signature must match
          the LLVM-name. This redundancy, however, reflects the split of LLVM code 
          generator and Header file generator.
        *)  
        datatype siginfo = SIGI of string * LLC_HeaderGen.raw_sig option  
          
        fun sigi_of_sig (rsg as (LLC_HeaderGen.RSIG (_,name,_))) = SIGI (name,SOME rsg)
        fun sigi_of_name name = SIGI (name,NONE)
        
        fun sigi_name (SIGI (name,_)) = name
        fun sigi_has_sig (SIGI (_,NONE)) = false
          | sigi_has_sig (SIGI (_,SOME _)) = true
        
        fun sigi_the_sig (SIGI (_,SOME sg)) = sg
          | sigi_the_sig _ = raise Match 
          
        val parse_sigi = 
             (Parse.short_ident || Parse.string) >> sigi_of_name  
          || xxx, string needs inner parser!
          
        *)  
          
      in
        fun export_llvm cns tydefs nt_ovr path (hfname,hfpath) lthy = let
          val lthy = Config.put Syntax_Trans.eta_contract false lthy
          val ((cthms,llvm_code,hcode),lthy) = consts_to_llvm hfname cns tydefs nt_ovr lthy
          val _ = write_out path llvm_code      
          val _ = case hcode of SOME c => write_out hfpath c | NONE => ()
        in
          (cthms,lthy)
        end
        
        val parse_ty_overrides = Scan.repeat1 (Parse.typ --| @{keyword "="} -- Parse.name)
        
        val export_llvm_cmd = (
          (Args.mode "debug" 
          -- Args.mode "timing" 
          -- Args.mode "no_while" 
          -- Args.mode "no_header" 
          -- Parse_Spec.opt_thm_name ":" 
          -- Scan.repeat1 (Parse.term -- Scan.option (@{keyword "is"} |-- LLC_HeaderGen.parse_raw_sig )) 
          -- Scan.option (@{keyword "defines"} |-- LLC_HeaderGen.parse_raw_tydefs)
          -- Scan.optional (@{keyword "rewrites"} |-- parse_ty_overrides) []
          -- Scan.option ((@{keyword "file"} |-- Parse.position Parse.path))
          )
           
            >> (fn (((((((((dbg,timing),nowhile),no_header),bnd),cns),tydefs),nt_ovr),path_spos)) => fn lthy => let 
            
              local
                val lthy = (timing?Config.put cfg_llvm_timing true) lthy
                val lthy = (dbg?Config.put cfg_llvm_debug true) lthy
                val lthy = (nowhile?Config.put LLC_Lib.llc_compile_while false) lthy
                val lthy = (no_header?Config.put cfg_llvm_gen_header false) lthy
              in
                val cns = map (apfst (Syntax.read_term lthy)) cns
                val cns = map (apsnd (map_option (LLC_HeaderGen.check_raw_sig lthy))) cns
                val tydefs = the_default [] (map_option (LLC_HeaderGen.check_raw_tydefs lthy) tydefs)
                
                val nt_ovr = map (apfst (Syntax.read_typ lthy)) nt_ovr
                
                val path = Option.map (prepare_path lthy) path_spos 
                val hfnpath = prepare_hpath lthy path_spos
                
                val (cthms,lthy) = export_llvm cns tydefs nt_ovr path hfnpath lthy
              end
              
              val (_,lthy) = Local_Theory.note (bnd,cthms) lthy 
              
            in lthy end))
        
        val llvm_deps_cmd = Parse_Spec.opt_thm_name ":" -- Scan.repeat1 Parse.term
          >> (fn (bnd,cns) => fn lthy => let
              val cns = map (Syntax.read_term lthy) cns
              val _ = writeln "Gathering code theorems"
              
              val (cthms,lthy) = LLC_Preprocessor.gather_code_thms cns lthy
              val (_,lthy) = Local_Theory.note (bnd,cthms) lthy 
              
              val _ = writeln "Done"
              
              val _ = pretty_cthms lthy cthms |> Pretty.string_of |> writeln
          
             in lthy end 
          )
        
            
      end
                                                                                                                   
      val _ = Outer_Syntax.local_theory @{command_keyword export_llvm} "generate LLVM code for constants" export_llvm_cmd
      val _ = Outer_Syntax.local_theory @{command_keyword llvm_deps} "Print LLVM code theorems for constants" llvm_deps_cmd
    end
  \<close>                                                      
  
  subsection \<open>Setup for Product Type\<close>
  text \<open>We prepare a setup to compile product types to anonymous 2-element structures\<close>
  
  lemma struct_of_prod[ll_struct_of]: 
    "struct_of TYPE('a::llvm_rep\<times>'b::llvm_rep) = VS_STRUCT [struct_of TYPE('a), struct_of TYPE('b)]" by simp
  
  
  (*lemma to_val_prod[ll_to_val]: "to_val x = LL_STRUCT [to_val (fst x), to_val (snd x)]"
    by (cases x; simp)
  *)
  
  definition prod_insert_fst :: "('a::llvm_rep \<times> 'b::llvm_rep) \<Rightarrow> 'a \<Rightarrow> _" 
    where [llvm_inline]: "prod_insert_fst p x \<equiv> ll_insert_value p x 0"
  definition prod_insert_snd :: "('a::llvm_rep \<times> 'b::llvm_rep) \<Rightarrow> 'b \<Rightarrow> _" 
    where [llvm_inline]: "prod_insert_snd p x \<equiv> ll_insert_value p x 1"
  definition prod_extract_fst :: "('a::llvm_rep \<times> 'b::llvm_rep) \<Rightarrow> 'a llM"
    where [llvm_inline]: "prod_extract_fst p \<equiv> ll_extract_value p 0"
  definition prod_extract_snd :: "('a::llvm_rep \<times> 'b::llvm_rep) \<Rightarrow> 'b llM"
    where [llvm_inline]: "prod_extract_snd p \<equiv> ll_extract_value p 1"
  (*definition prod_gep_fst :: "('a::llvm_rep \<times> 'b::llvm_rep) ptr \<Rightarrow> 'a ptr llM"
    where [llvm_inline]: "prod_gep_fst p \<equiv> ll_gep_struct p 0"
  definition prod_gep_snd :: "('a::llvm_rep \<times> 'b::llvm_rep) ptr \<Rightarrow> 'b ptr llM"
    where [llvm_inline]: "prod_gep_snd p \<equiv> ll_gep_struct p 1"
  *)
  
  lemma prod_ops_simp:
    "prod_insert_fst = (\<lambda>(_,b) a. Mreturn (a,b))"
    "prod_insert_snd = (\<lambda>(a,_) b. Mreturn (a,b))"
    "prod_extract_fst = (\<lambda>(a,b). Mreturn a)"
    "prod_extract_snd = (\<lambda>(a,b). Mreturn b)"
    unfolding 
      prod_insert_fst_def prod_insert_snd_def ll_insert_value_def
      prod_extract_fst_def prod_extract_snd_def ll_extract_value_def 
    unfolding llvm_insert_value_def llvm_extract_value_def  
    apply (all \<open>intro ext\<close>  )
    apply (auto 
      simp: to_val_prod_def from_val_prod_def checked_from_val_def
      split: prod.splits
      )
    done
  
    
  subsection \<open>Ad-Hoc Regression Tests\<close>
  
experiment begin  
  
  definition exp :: "64 word \<Rightarrow> 64 word llM" where [llvm_code]: "exp i \<equiv> doM {
    s \<leftarrow> prod_insert_fst init 1;
    s \<leftarrow> prod_insert_snd s i;
    s \<leftarrow> llc_while
      (\<lambda>s. doM {
        i \<leftarrow> prod_extract_snd s;
        ll_icmp_ne i 0
      })
      (\<lambda>s. doM {
        c \<leftarrow> prod_extract_fst s;
        i \<leftarrow> prod_extract_snd s;
        
        c \<leftarrow> ll_mul c 2;
        i \<leftarrow> ll_sub i 1;
        
        s \<leftarrow> prod_insert_fst init c;
        s \<leftarrow> prod_insert_snd s i;
        
        Mreturn s
      })
      s;
  
    prod_extract_fst s
  }"
  
  
  definition streq :: "8 word ptr \<Rightarrow> 8 word ptr \<Rightarrow> 1 word llM" where [llvm_code]: "streq s\<^sub>1 s\<^sub>2 = doM {
      x \<leftarrow> ll_load s\<^sub>1;
      y \<leftarrow> ll_load s\<^sub>2;
      ll_icmp_eq x y
    }"
  
  export_llvm streq  
  
  definition [llvm_code]: "test2 (n::32 word) \<equiv> doM {
    n \<leftarrow> ll_add n 42;
    p \<leftarrow> ll_malloc TYPE(16 word) n;
    p \<leftarrow> ll_ofs_ptr p (5::32 word);
    ll_store 42 p;
    r \<leftarrow> ll_load p; 
    Mreturn r  
  }"
  
  definition [llvm_code]: "add_add (a::_ word) \<equiv> doM {
    x \<leftarrow> ll_add a a;
    x \<leftarrow> ll_add x x;
    Mreturn x
  }"

  definition [llvm_code]: "add_add_driver (a::32 word) (b::64 word) \<equiv> doM {
    a \<leftarrow> add_add a;
    b \<leftarrow> add_add b;
    a \<leftarrow> ll_zext a TYPE(64 word);
    b \<leftarrow> ll_add a b;
    Mreturn b
  }"
  
  export_llvm (debug) add_add_driver
  
  definition [llvm_code]: "main (argc::32 word) (argv::8 word ptr ptr) \<equiv> doM {
    r \<leftarrow> test2 argc;
    r \<leftarrow> ll_zext r TYPE(32 word);
    Mreturn r
  }" 

  definition [llvm_code]: "main_exp (argc::32 word) (argv::8 word ptr ptr) \<equiv> doM {
    argc \<leftarrow> ll_zext argc TYPE(64 word);
    r \<leftarrow> exp argc;
    r \<leftarrow> ll_trunc r TYPE(32 word);
    Mreturn r
  }" 

  
definition [llvm_code]: "testx (a::64 word) \<equiv> llc_while (\<lambda>a. ll_icmp_ult 0 a) (\<lambda>a. ll_sub a 1) a"
export_llvm (debug) testx

export_llvm (debug) exp_thms1: exp  


export_llvm (debug) (no_while) exp_thms2: exp  
export_llvm (debug) (no_while) exp_thms3: exp  

thm exp_thms1
thm exp_thms2
thm exp_thms3


export_llvm (debug) foobar: main_exp is main
export_llvm (debug) main is main



definition [llvm_code]: 
  "test_if_names (n::32 word) \<equiv> doM {
    tmp \<leftarrow> ll_icmp_eq n 0;
    a \<leftarrow> llc_if tmp (Mreturn null) (doM {
                                     x \<leftarrow> ll_malloc TYPE(8 word) n;
                                     Mreturn x
                                   });
    p \<leftarrow> ll_ofs_ptr a (1::32 word);
    ll_store 0x2A p;
    ll_free a;
    Mreturn ()
  }"
 
export_llvm test_if_names

definition fib :: "64 word \<Rightarrow> 64 word llM" 
  where [llvm_code]: "fib n \<equiv> REC (\<lambda>fib n. doM { 
    t\<leftarrow>ll_icmp_ule n 1; 
    llc_if t 
      (Mreturn n) 
      (doM { 
        n\<^sub>1 \<leftarrow> ll_sub n 1; 
        a\<leftarrow>fib n\<^sub>1; 
        n\<^sub>2 \<leftarrow> ll_sub n 2; 
        b\<leftarrow>fib n\<^sub>2; 
        c\<leftarrow>ll_add a b; 
        Mreturn c })} ) n"

export_llvm fib is fib


definition triple_sum :: "(64 word \<times> 64 word \<times> 64 word) ptr \<Rightarrow> 64 word llM" where [llvm_code]:
  "triple_sum abc \<equiv> doM {
    abc \<leftarrow> ll_load abc;
    a \<leftarrow> ll_extract_value abc 0;
    bc::64 word \<times> 64 word \<leftarrow> ll_extract_value abc 1;
    b \<leftarrow> ll_extract_value bc 0;
    c \<leftarrow> ll_extract_value bc 1;
    r \<leftarrow> ll_add a b;
    r \<leftarrow> ll_add r c;
    Mreturn r
   }"
   
export_llvm triple_sum is \<open>_ triple_sum(triple*)\<close> 
  defines \<open>typedef struct {int64_t a; struct {int64_t b; int64_t c;};} triple;\<close>
 
  
definition [llvm_code]: "test_ppar \<equiv> llc_par fib test2 3 3"
  
declare [[llc_compile_par_call=true]]

export_llvm test_ppar file "test_par.ll"
 
  
(* Higher-Order stuff *)

definition repeat2 :: "(_ word \<Rightarrow> _ word llM) \<Rightarrow> _" where [llvm_code]:
"repeat2 f x \<equiv> doM {
  x \<leftarrow> f x;
  f x
}"

definition [llvm_code]: "fibfib \<equiv> repeat2 fib"

export_llvm fibfib

definition times3_f :: "single \<Rightarrow> single llM" where [llvm_code]:
  "times3_f x \<equiv> doM {
    x'\<leftarrow>ll_fadd_f x x;
    x'\<leftarrow>ll_fadd_f x' x;
    x'\<leftarrow>ll_fadd_f x' (single_of_word 0x3FD55555);
    Mreturn x'
  }"


export_llvm times3_f is "float times3_f (float)"

definition times3_pf :: "(single*single) ptr \<Rightarrow> single llM" where [llvm_code]:
  "times3_pf x \<equiv> doM {
    x \<leftarrow> ll_load x;
    a \<leftarrow> ll_extract_value x 0;
    b \<leftarrow> ll_extract_value x 1;
    x'\<leftarrow>ll_fadd_f a a;
    x'\<leftarrow>ll_fadd_f x' b;
    Mreturn x'
  }"

export_llvm times3_pf is "float times3_f (dpair*)" 
  defines \<open>typedef struct {float a; float b;} dpair;\<close>


value "real_of_single (single_of_word 0x3F000000)"

(* TODO: More meaningful tests, and check results! 

  f (a,b) = (sqrt (a\<^sup>2 + b\<^sup>2) - a/b) fmod (a+b)

*)
definition test_float :: "single \<Rightarrow> single \<Rightarrow> single llM" where [llvm_code]:
  "test_float a b \<equiv> doM {
    aa \<leftarrow> ll_fmul_f a a;
    bb \<leftarrow> ll_fmul_f b b;
    t\<^sub>1 \<leftarrow> ll_fadd_f aa bb;
    t\<^sub>1 \<leftarrow> ll_sqrt_f32 t\<^sub>1;
    t\<^sub>2 \<leftarrow> ll_fdiv_f a b;
    t\<^sub>1 \<leftarrow> ll_fsub_f t\<^sub>1 t\<^sub>2;
    t\<^sub>2 \<leftarrow> ll_fadd_f a b;
    t\<^sub>1 \<leftarrow> ll_frem_f t\<^sub>1 t\<^sub>2;
    t\<^sub>1 \<leftarrow> ll_fadd_f t\<^sub>1 (single_of_word 0x3F000000);
  
    Mreturn t\<^sub>1
  }"

  
export_llvm 
  test_float is "float test_float(float,float)"
  file "../../../regression/gencode/test_float.ll"


definition times3_d :: "double \<Rightarrow> double llM" where [llvm_code]:
  "times3_d x \<equiv> doM {
    x'\<leftarrow>ll_fadd_d x x;
    x'\<leftarrow>ll_fadd_d x' x;
    x'\<leftarrow>ll_fadd_d x' (double_of_word 0x3FD5555555555555);
    Mreturn x'
  }"


export_llvm times3_d is "double times3_d (double)"

definition times3_pd :: "(double*double) ptr \<Rightarrow> double llM" where [llvm_code]:
  "times3_pd x \<equiv> doM {
    x \<leftarrow> ll_load x;
    a \<leftarrow> ll_extract_value x 0;
    b \<leftarrow> ll_extract_value x 1;
    x'\<leftarrow>ll_fadd_d a a;
    x'\<leftarrow>ll_fadd_d x' b;
    Mreturn x'
  }"

export_llvm times3_pd is "double times3_d (dpair*)" 
  defines \<open>typedef struct {double a; double b;} dpair;\<close>


value "real_of_double (double_of_word 0x3FE0000000000000)"

(* TODO: More meaningful tests, and check results! 

  f (a,b) = (sqrt (a\<^sup>2 + b\<^sup>2) - a/b) fmod (a+b)

*)
definition test_double :: "double \<Rightarrow> double \<Rightarrow> double llM" where [llvm_code]:
  "test_double a b \<equiv> doM {
    aa \<leftarrow> ll_fmul_d a a;
    bb \<leftarrow> ll_fmul_d b b;
    t\<^sub>1 \<leftarrow> ll_fadd_d aa bb;
    t\<^sub>1 \<leftarrow> ll_sqrt_f64 t\<^sub>1;
    t\<^sub>2 \<leftarrow> ll_fdiv_d a b;
    t\<^sub>1 \<leftarrow> ll_fsub_d t\<^sub>1 t\<^sub>2;
    t\<^sub>2 \<leftarrow> ll_fadd_d a b;
    t\<^sub>1 \<leftarrow> ll_frem_d t\<^sub>1 t\<^sub>2;
    t\<^sub>1 \<leftarrow> ll_fadd_d t\<^sub>1 (double_of_word 0x3FE0000000000000);
  
    Mreturn t\<^sub>1
  }"

  
export_llvm 
  test_double is "double test_double(double,double)"
  file "../../../regression/gencode/test_double.ll"
  
  
  
definition "rm_opposite rm \<equiv> 
  if rm = AVX512_FROUND_TO_POS_INF_NO_EXC then AVX512_FROUND_TO_NEG_INF_NO_EXC
  else if rm = AVX512_FROUND_TO_NEG_INF_NO_EXC then AVX512_FROUND_TO_POS_INF_NO_EXC
  else rm"

lemma rm_opposite_inlines[llvm_pre_simp]:
  "rm_opposite AVX512_FROUND_TO_POS_INF_NO_EXC = AVX512_FROUND_TO_NEG_INF_NO_EXC"
  "rm_opposite AVX512_FROUND_TO_NEG_INF_NO_EXC = AVX512_FROUND_TO_POS_INF_NO_EXC"
  "rm_opposite AVX512_FROUND_TO_NEAREST_NO_EXC = AVX512_FROUND_TO_NEAREST_NO_EXC"
  "rm_opposite AVX512_FROUND_TO_ZERO_NO_EXC = AVX512_FROUND_TO_ZERO_NO_EXC"
  unfolding rm_opposite_def by auto
  

(*
  f (a,b) = (sqrt (a\<^sup>2 + b\<^sup>2) - a/b) + a
                      ^ fused multiply-add
                               ^ needs to round opposite way
*)


definition test_avx512f_ss_tmpl :: "nat \<Rightarrow> single \<Rightarrow> single \<Rightarrow> single llM" where [llvm_pre_simp]:
"test_avx512f_ss_tmpl rm \<equiv> \<lambda>a b. doM {
  aa \<leftarrow> ll_x86_avx512_mul_ss_round rm a a;
  t\<^sub>1 \<leftarrow> ll_x86_avx512_vfmadd_f32 rm b b aa;
  t\<^sub>1 \<leftarrow> ll_x86_avx512_sqrt_ss rm t\<^sub>1;
  t\<^sub>2 \<leftarrow> ll_x86_avx512_div_ss_round (rm_opposite rm) a b;
  t\<^sub>1 \<leftarrow> ll_x86_avx512_sub_ss_round rm t\<^sub>1 t\<^sub>2;
  t\<^sub>1 \<leftarrow> ll_x86_avx512_add_ss_round rm t\<^sub>1 a;

  Mreturn t\<^sub>1
}"

definition [llvm_code]: "test_avx512f_ss_to_nearest \<equiv> test_avx512f_ss_tmpl AVX512_FROUND_TO_NEAREST_NO_EXC"
definition [llvm_code]: "test_avx512f_ss_to_pinf    \<equiv> test_avx512f_ss_tmpl AVX512_FROUND_TO_POS_INF_NO_EXC"
definition [llvm_code]: "test_avx512f_ss_to_ninf    \<equiv> test_avx512f_ss_tmpl AVX512_FROUND_TO_NEG_INF_NO_EXC"
definition [llvm_code]: "test_avx512f_ss_to_zero    \<equiv> test_avx512f_ss_tmpl AVX512_FROUND_TO_ZERO_NO_EXC"



definition test_avx512f_sd_tmpl :: "nat \<Rightarrow> double \<Rightarrow> double \<Rightarrow> double llM" where [llvm_pre_simp]:
"test_avx512f_sd_tmpl rm \<equiv> \<lambda>a b. doM {
  aa \<leftarrow> ll_x86_avx512_mul_sd_round rm a a;
  t\<^sub>1 \<leftarrow> ll_x86_avx512_vfmadd_f64 rm b b aa;
  t\<^sub>1 \<leftarrow> ll_x86_avx512_sqrt_sd rm t\<^sub>1;
  t\<^sub>2 \<leftarrow> ll_x86_avx512_div_sd_round (rm_opposite rm) a b;
  t\<^sub>1 \<leftarrow> ll_x86_avx512_sub_sd_round rm t\<^sub>1 t\<^sub>2;
  t\<^sub>1 \<leftarrow> ll_x86_avx512_add_sd_round rm t\<^sub>1 a;

  Mreturn t\<^sub>1
}"

definition [llvm_code]: "test_avx512f_sd_to_nearest \<equiv> test_avx512f_sd_tmpl AVX512_FROUND_TO_NEAREST_NO_EXC"
definition [llvm_code]: "test_avx512f_sd_to_pinf    \<equiv> test_avx512f_sd_tmpl AVX512_FROUND_TO_POS_INF_NO_EXC"
definition [llvm_code]: "test_avx512f_sd_to_ninf    \<equiv> test_avx512f_sd_tmpl AVX512_FROUND_TO_NEG_INF_NO_EXC"
definition [llvm_code]: "test_avx512f_sd_to_zero    \<equiv> test_avx512f_sd_tmpl AVX512_FROUND_TO_ZERO_NO_EXC"




declare [[llc_compile_avx512f=true]]  
export_llvm 
  test_avx512f_ss_to_nearest is "float test_avx512f_ss_to_nearest(float,float)"
  test_avx512f_ss_to_pinf    is "float test_avx512f_ss_to_pinf   (float,float)"
  test_avx512f_ss_to_ninf    is "float test_avx512f_ss_to_ninf   (float,float)"
  test_avx512f_ss_to_zero    is "float test_avx512f_ss_to_zero   (float,float)"
  test_avx512f_sd_to_nearest is "double test_avx512f_sd_to_nearest(double,double)"
  test_avx512f_sd_to_pinf    is "double test_avx512f_sd_to_pinf   (double,double)"
  test_avx512f_sd_to_ninf    is "double test_avx512f_sd_to_ninf   (double,double)"
  test_avx512f_sd_to_zero    is "double test_avx512f_sd_to_zero   (double,double)"
  file "../../../regression/gencode/test_avx512f.ll"

    
end

end
