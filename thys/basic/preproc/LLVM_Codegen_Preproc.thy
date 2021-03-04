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

  lemma llc_while_mono[partial_function_mono]:      
    assumes "\<And>x. M_mono (\<lambda>f. b f x)"
    assumes "\<And>x. M_mono (\<lambda>f. c f x)"
    shows "M_mono (\<lambda>D. llc_while (b D) (c D) \<sigma>)"
    using assms unfolding llc_while_def by pf_mono_prover
      
  declaration \<open>fn _ => Definition_Utils.declare_extraction_group @{binding LLVM} #> snd\<close>
  declaration \<open>fn _ => Definition_Utils.declare_extraction_group @{binding LLVM_while} #> snd\<close>
    
  declaration \<open> fn _ =>
    Definition_Utils.add_extraction (@{extraction_group LLVM_while},\<^here>) {
      pattern = Logic.varify_global @{term "llc_while b body"},
      gen_thm = @{thm gen_code_thm_llc_while},
      gen_tac = K (K no_tac)
    }
  \<close>

  declaration \<open>fn _ =>
    Definition_Utils.add_extraction (@{extraction_group LLVM},\<^here>) {
      pattern = Logic.varify_global @{term "REC (B::('a \<Rightarrow> 'b llM) \<Rightarrow> 'a \<Rightarrow> 'b llM)"},
      gen_thm = @{thm REC_unfold},
      gen_tac = Partial_Function.mono_tac
    }
  \<close>

subsection \<open>Preprocessor\<close>  
  text \<open>
    The actual code generator expects a set of monomorphic, well-shaped equations.
    The preprocessor processes user specified equations, monomorphizes them and 
    brings them into the right shape.
  \<close>
  
  named_theorems llvm_code \<open>Isabelle-LLVM code theorems\<close>
  
  named_simpset llvm_inline = HOL_ss

  attribute_setup llvm_inline = \<open>
    Attrib.add_del 
      (Named_Simpsets.add_attr @{named_simpset llvm_inline}) 
      (Named_Simpsets.del_attr @{named_simpset llvm_inline})
  \<close>
    
  
  lemma llvm_inline_bind_laws[llvm_inline]:
    "bind m return = m"
    "bind (bind m (\<lambda>x. f x)) g = bind m (\<lambda>x. bind (f x) g)"
    by auto
  
  lemma unit_meta_eq: "x \<equiv> ()" by simp
  
  lemma pull_lambda_case: "(case x of (a,b) \<Rightarrow> \<lambda>y. t a b y) = (\<lambda>y. case x of (a,b) \<Rightarrow> t a b y)"
    apply (rule ext) apply (cases x) by auto

  ML \<open> structure LLC_Preprocessor = 
    struct
      open LLC_Lib
          
      structure Monadify = Gen_Monadify_Cong (
      
        fun mk_return x = @{mk_term "return ?x ::_ llM"}
        fun mk_bind m f = @{mk_term "bind ?m ?f ::_ llM"}
      
        fun dest_return @{mpat "return ?x ::_ llM"} = SOME x | dest_return _ = NONE
        fun dest_bind @{mpat "bind ?m ?f ::_ llM"} = SOME (m,f) | dest_bind _ = NONE
        
        fun dest_monadT (Type (@{type_name M},[T,@{typ unit},@{typ llvm_memory},@{typ err}])) = SOME T | dest_monadT _ = NONE

        val strip_op = K strip_comb
        
        val bind_return_thm = @{lemma "bind m return = m" by simp}
        val return_bind_thm = @{lemma "bind (return x) f = f x" by simp}
        val bind_bind_thm = @{lemma "bind (bind m (\<lambda>x. f x)) g = bind m (\<lambda>x. bind (f x) g)" by simp}
        
      )
      
      (********* Normalization of code theorems *)
      
  
      fun cthm_inline ctxt thm = let
        val ctxt = Named_Simpsets.put @{named_simpset llvm_inline} ctxt
      in
        (* TODO: Simplifier.rewrite may introduce beta redexes. 
          Currently we eliminate them right away. Or is it OK to have beta-redexes? *)
        Conv.fconv_rule (rhs_conv (Simplifier.rewrite ctxt) then_conv Thm.beta_conversion true) thm
      end
    
      val cthm_monadify = Conv.fconv_rule o (rhs_conv o Monadify.monadify_conv)
            
      val inline_iteration_limit =
        Config.int (Config.declare ("inline_iteration_limit", \<^here>) (fn _ => Config.Int ~1));
      
      
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
      fun cthm_format ctxt thm = let
        fun normalize_bind1 t = let
          val (f,args) = strip_comb t
          val _ = check_valid_head f
  
          val args_is_M = fastype_of f |> binder_types |> map (is_llM o body_type)
                  
          val _ = length args_is_M = length args orelse raise TYPE ("cthm_format: All arguments must be explicit", [fastype_of f], [t])
          
          val args = map2 (fn isM => isM?(normalize o expand_eta_all)) args_is_M args
          
        in
          list_comb (f, args)
        end  
          
        and normalize @{mpat "bind ?m ?f"} = let
            val m = normalize_bind1 m
            val f = (*ensure_abs f*) expand_eta_all f |> normalize
          in @{mk_term "bind ?m ?f"} end
        | normalize (Abs (x,T,t)) = Abs (x,T,normalize t)
        | normalize (t as @{mpat "return _"}) = t
        | normalize t = let val t = normalize_bind1 t in @{mk_term "bind ?t (\<lambda>x. return x)"} end
      
        fun normalize_eq @{mpat "Trueprop (?a = ?b)"} = let val b = normalize b in @{mk_term "Trueprop (?a = ?b)"} end
          | normalize_eq @{mpat "?a \<equiv> ?b"} = let val b = normalize b in @{mk_term "?a \<equiv> ?b"} end
          | normalize_eq t = raise TERM ("format_code_thm: normalize_eq", [t])
      
        fun norm_tac ctxt = ALLGOALS (simp_tac (put_simpset HOL_ss ctxt addsimps @{thms bind_laws}))
    
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
        |> (simplify (put_simpset HOL_ss ctxt addsimps @{thms Monad.bind_laws atomize_eq}))
        |> cthm_norm_lambda ctxt
        |> (Conv.fconv_rule (Refine_Util.f_tac_conv ctxt normalize_eq (norm_tac ctxt)))
        |> (Conv.fconv_rule (Conv.top_sweep_conv (K (Conv.rewr_conv @{thm unit_meta_eq})) ctxt))
      end
      
      (********* Gathering of code equations *)
      (* TODO: Use net *)

      
      fun dep_prep_code_thm thm = let
        val c = head_of_eqn_thm thm
        val _ = check_valid_head c
      in
        (c,thm)
      end
      
      fun dep_try_instantiate_code_thm c (l,thm) = let
        val thy = Thm.theory_of_thm thm
      in
        case SOME (Pattern.match thy (l,c) (Vartab.empty,Vartab.empty)) handle Pattern.MATCH => NONE of
          NONE => NONE
        | SOME m => SOME (instantiate_uc m thm)
      end
      
      fun dep_find_code_thm pthms c = 
        case get_first (dep_try_instantiate_code_thm c) pthms of
          SOME eqn => eqn
        | NONE => raise TERM ("No code equation",[c])
      
      val cmd_name_prefix = Long_Name.qualify (Long_Name.qualifier @{const_name ll_add}) "ll_"
      val comb_name_prefix = Long_Name.qualify (Long_Name.qualifier @{const_name llc_while}) "llc_"
          
      fun dep_is_ll_comb_name name =
               name = @{const_name bind}
        orelse name = @{const_name return}
        orelse String.isPrefix cmd_name_prefix name
        orelse String.isPrefix comb_name_prefix name
        
        
      fun dep_is_call_const t = case try dest_head t of
        NONE => false
      | SOME (name,T) => 
                  not (dep_is_ll_comb_name name) (* Not an internal name *)
          andalso is_llM (body_type T)           (* Yields a monadic result *)
          andalso not (exists (exists_subtype is_llM) (binder_types T)) (* No monadic parameters *)
        
      fun calls_of_cthm thm = Term.fold_aterms 
        (fn t => dep_is_call_const t?cons t) 
        (rhs_of_eqn (Thm.prop_of thm))
        []
      
      fun default_extractions ctxt = 
          Definition_Utils.get_extraction_group ctxt @{extraction_group LLVM}
        |> (not (Config.get ctxt llc_compile_while) ? 
              append (Definition_Utils.get_extraction_group ctxt @{extraction_group LLVM_while}))  
      
      fun gather_code_thms roots lthy = let
        val thy = Proof_Context.theory_of lthy
        val pthms = Named_Theorems.get lthy @{named_theorems llvm_code}
          |> map dep_prep_code_thm
          |> Refine_Util.subsume_sort fst thy
      
        fun process_root c (ctab, lthy) = let
          val _ = check_valid_head c
          val basename = name_of_head c |> Long_Name.base_name
        in
          case Termtab.lookup ctab c of
            SOME _ => (ctab, lthy)
          | NONE => let
              val _ = assert_monomorphic_const c
              (* Get code theorem and inline it *)
              val teqn = dep_find_code_thm pthms c |> monadify_inline_cthm lthy

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
              
              (* Recurse *)
              val (ctab,lthy) = fold process_root calls (ctab,lthy)
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

  declaration \<open>K (LLC_Preprocessor.Monadify.prepare_add_const_decl @{term "numeral a"})\<close>  
  
  
    
subsection \<open>Code Generator Driver\<close>  
  text \<open>
    The driver combines preeprocessing and code generation, 
    and defines the user interface of the code generator, namely the commands
    @{command export_llvm} and @{command llvm_deps}.
  \<close>
  
  ML \<open> structure LLC_Driver 
    = struct
    
      val cfg_llvm_debug = Attrib.setup_config_bool @{binding llvm_debug} (K false)
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
                
        
        
        
      fun consts_to_llvm hfname cns tydefs lthy = let
        val dbg = Config.get lthy cfg_llvm_debug
        val gen_header = Config.get lthy cfg_llvm_gen_header
        fun trace s = if dbg then Pretty.string_of (s ()) |> tracing else ()
                                                                                                      
        val _ = trace (fn () => Pretty.str "Gathering code theorems")
        val (cthms,lthy) = LLC_Preprocessor.gather_code_thms (map fst cns) lthy
        val _ = trace (fn () => pretty_cthms lthy cthms)
        
        val _ = trace (fn () => Pretty.str "Computing symbol table")
        val fixes = map_filter (fn (_,NONE) => NONE | (cn,SOME sigspec) => SOME (cn,LLC_HeaderGen.name_of_sigspec sigspec)) cns
        val ftab = LLC_Compiler.compute_fun_names fixes cthms
        val _ = trace (fn () => pretty_ftab lthy ftab)
        
                  
        val _ = trace (fn () => Pretty.str "Translating code theorems to IL")
        val (tys,eqns) = LLC_Compiler.parse_cthms ftab cthms lthy
        val _ = trace (fn () => LLC_Intermediate.pretty_llc (tys,eqns))
        
        val _ = trace (fn () => Pretty.str "Writing LLVM")
        val res = LLC_Backend.compile_to_llvm lthy (tys,eqns)
        
        val hdres = if gen_header then let
            val _ = trace (fn () => Pretty.str "Preparing Header")
            val sigspecs = map_filter snd cns
            val hdres = LLC_HeaderGen.make_header hfname tydefs sigspecs eqns
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
          val _ = Position.report pos (Markup.path (Path.implode_symbolic path));
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
        fun export_llvm cns tydefs path (hfname,hfpath) lthy = let
          val lthy = Config.put Syntax_Trans.eta_contract false lthy
          val ((cthms,llvm_code,hcode),lthy) = consts_to_llvm hfname cns tydefs lthy
          val _ = write_out path llvm_code      
          val _ = case hcode of SOME c => write_out hfpath c | NONE => ()
        in
          (cthms,lthy)
        end
        
        val export_llvm_cmd = (
          Args.mode "debug" 
          -- Args.mode "no_while" 
          -- Args.mode "no_header" 
          -- Parse_Spec.opt_thm_name ":" 
          -- (Scan.repeat1 (Parse.term -- Scan.option (@{keyword "is"} |-- LLC_HeaderGen.parse_raw_sig )) 
          -- Scan.option (@{keyword "defines"} |-- LLC_HeaderGen.parse_raw_tydefs)
          -- Scan.option ((@{keyword "file"} |-- Parse.position Parse.path))
          ) 
            >> (fn ((((dbg,nowhile),no_header),bnd),((cns,tydefs),path_spos)) => fn lthy => let 
            
              local
                val lthy = (dbg?Config.put cfg_llvm_debug true) lthy
                val lthy = (nowhile?Config.put LLC_Lib.llc_compile_while false) lthy
                val lthy = (no_header?Config.put cfg_llvm_gen_header false) lthy
              in
                val cns = map (apfst (Syntax.read_term lthy)) cns
                val cns = map (apsnd (map_option (LLC_HeaderGen.check_raw_sig lthy))) cns
                val tydefs = the_default [] (map_option (LLC_HeaderGen.check_raw_tydefs lthy) tydefs)
                
                val path = Option.map (prepare_path lthy) path_spos 
                val hfnpath = prepare_hpath lthy path_spos
                
                val (cthms,lthy) = export_llvm cns tydefs path hfnpath lthy
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
  
  lemma ll_prod_is_pair[ll_is_pair_type_thms]: 
    "ll_is_pair_type True TYPE('a::llvm_rep \<times>'b::llvm_rep) TYPE('a) TYPE('b)"
    by (simp add: ll_is_pair_type_def)
  
  definition [llvm_inline]: "prod_insert_fst \<equiv> ll_insert_fst :: ('a::llvm_rep \<times> 'b::llvm_rep) \<Rightarrow> 'a \<Rightarrow> ('a\<times>'b) llM"
  definition [llvm_inline]: "prod_insert_snd \<equiv> ll_insert_snd :: ('a::llvm_rep \<times> 'b::llvm_rep) \<Rightarrow> 'b \<Rightarrow> ('a\<times>'b) llM"
  definition [llvm_inline]: "prod_extract_fst \<equiv> ll_extract_fst :: ('a::llvm_rep \<times> 'b::llvm_rep) \<Rightarrow> 'a llM"
  definition [llvm_inline]: "prod_extract_snd \<equiv> ll_extract_snd :: ('a::llvm_rep \<times> 'b::llvm_rep) \<Rightarrow> 'b llM"
  definition [llvm_inline]: "prod_gep_fst \<equiv> ll_gep_fst :: ('a::llvm_rep \<times> 'b::llvm_rep) ptr \<Rightarrow> 'a ptr llM"
  definition [llvm_inline]: "prod_gep_snd \<equiv> ll_gep_snd :: ('a::llvm_rep \<times> 'b::llvm_rep) ptr \<Rightarrow> 'b ptr llM"

  
  lemma prod_ops_simp:
    "prod_insert_fst = (\<lambda>(_,b) a. return (a,b))"
    "prod_insert_snd = (\<lambda>(a,_) b. return (a,b))"
    "prod_extract_fst = (\<lambda>(a,b). return a)"
    "prod_extract_snd = (\<lambda>(a,b). return b)"
    unfolding 
      prod_insert_fst_def ll_insert_fst_def 
      prod_insert_snd_def ll_insert_snd_def
      prod_extract_fst_def ll_extract_fst_def 
      prod_extract_snd_def ll_extract_snd_def       
    apply (all \<open>intro ext\<close>  )
    apply (auto 
      simp: checked_split_pair_def to_val_prod_def from_val_prod_def checked_from_val_def
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
        
        return s
      })
      s;
  
    prod_extract_fst s
  }"
  
  
  definition streq :: "8 word ptr \<Rightarrow> 8 word ptr \<Rightarrow> 1 word llM" where [llvm_code]: "streq s\<^sub>1 s\<^sub>2 = doM {
      x \<leftarrow> ll_load s\<^sub>1;
      ll_load s\<^sub>2 \<bind> ll_icmp_eq x
    }"
  
  export_llvm streq  
  
  definition [llvm_code]: "test2 (n::32 word) \<equiv> doM {
    n \<leftarrow> ll_add n 42;
    p \<leftarrow> ll_malloc TYPE(16 word) n;
    p \<leftarrow> ll_ofs_ptr p (5::32 word);
    ll_store 42 p;
    r \<leftarrow> ll_load p; 
    return r  
  }"
  
  definition [llvm_code]: "add_add (a::_ word) \<equiv> doM {
    x \<leftarrow> ll_add a a;
    x \<leftarrow> ll_add x x;
    return x
  }"

  definition [llvm_code]: "add_add_driver (a::32 word) (b::64 word) \<equiv> doM {
    a \<leftarrow> add_add a;
    b \<leftarrow> add_add b;
    a \<leftarrow> ll_zext a TYPE(64 word);
    b \<leftarrow> ll_add a b;
    return b
  }"
  
  export_llvm (debug) add_add_driver
  
  definition [llvm_code]: "main (argc::32 word) (argv::8 word ptr ptr) \<equiv> doM {
    r \<leftarrow> test2 argc;
    r \<leftarrow> ll_zext r TYPE(32 word);
    return r
  }" 

  definition [llvm_code]: "main_exp (argc::32 word) (argv::8 word ptr ptr) \<equiv> doM {
    argc \<leftarrow> ll_zext argc TYPE(64 word);
    r \<leftarrow> exp argc;
    r \<leftarrow> ll_trunc r TYPE(32 word);
    return r
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
    a \<leftarrow> llc_if tmp (return null) (doM {
                                     x \<leftarrow> ll_malloc TYPE(8 word) n;
                                     return x
                                   });
    p \<leftarrow> ll_ofs_ptr a (1::32 word);
    ll_store 0x2A p;
    ll_free a;
    return ()
  }"
 
export_llvm test_if_names

definition fib :: "64 word \<Rightarrow> 64 word llM" 
  where [llvm_code]: "fib n \<equiv> REC (\<lambda>fib n. doM { 
    t\<leftarrow>ll_icmp_ule n 1; 
    llc_if t 
      (return n) 
      (doM { 
        n\<^sub>1 \<leftarrow> ll_sub n 1; 
        a\<leftarrow>fib n\<^sub>1; 
        n\<^sub>2 \<leftarrow> ll_sub n 2; 
        b\<leftarrow>fib n\<^sub>2; 
        c\<leftarrow>ll_add a b; 
        return c })} ) n"

export_llvm fib is fib


definition triple_sum :: "(64 word \<times> 64 word \<times> 64 word) \<Rightarrow> 64 word llM" where [llvm_code]:
  "triple_sum abc \<equiv> doM {
    a \<leftarrow> ll_extract_fst abc;
    bc::64 word \<times> 64 word \<leftarrow> ll_extract_snd abc;
    b \<leftarrow> ll_extract_fst bc;
    c \<leftarrow> ll_extract_snd bc;
    r \<leftarrow> ll_add a b;
    r \<leftarrow> ll_add r c;
    return r
   }"
   
export_llvm triple_sum is \<open>_ triple_sum(triple)\<close> 
  defines \<open>typedef struct {int64_t a; struct {int64_t b; int64_t c;};} triple;\<close>
  
  

end

end
