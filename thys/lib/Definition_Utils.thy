theory Definition_Utils
imports 
  Main
  "Automatic_Refinement.Refine_Lib" 
  "HOL-Library.Rewrite"
keywords 
      "concrete_definition" :: thy_decl
  and "prepare_code_thms" :: thy_decl
  and "synth_definition" :: thy_goal

begin

  (*
    (* DO NOT USE IN PRODUCTION VERSION \<rightarrow> SLOWDOWN *)
    declare [[ML_exception_debugger, ML_debugger, ML_exception_trace]]
  *)

text \<open>
  This theory provides a tool for extracting definitions from terms, and
  for generating code equations for recursion combinators.
\<close>

(*
  TODO: Copied and merged from $AFP/Refine_Monadic/Refine_Automation
    and isafol/GRAT/gratchk/Synth_Definition

  TODO: Not properly localized  
  
  
  TODO: Finally merge Definition_Utils and Synth_Definition structure. 
    Use \<hole> instead of schematics for user interface!
    
*)

ML_val \<open>Symtab.update_list\<close>
ML \<open>
signature DEFINITION_UTILS = sig
  type extraction = {
    pattern: term,   (* Pattern to be defined as own constant *)
    gen_thm: thm,    (* Code eq generator: [| c==rhs; ... |] ==> c == ... *)
    gen_tac: local_theory -> tactic' (* Solves remaining premises of gen_thm *)
  }

  val extract_as_def: (string * typ) list -> string -> term 
    -> local_theory -> ((term * thm) * local_theory)

  (* Returns new_def_thm, code_thms, raw_def_thms *)  
  val extract_recursion_eqs: extraction list -> string -> thm 
    -> local_theory -> ((thm * thm list * thm list) * local_theory)
    
  (* Generate and register with names, code-theorems by specified attrib *)  
  val extract_recursion_eqs': extraction list -> string -> Token.src list -> thm 
    -> local_theory -> ((thm list) * local_theory)

  val declare_extraction_group: binding -> Context.generic -> string * Context.generic
  val add_extraction: xstring * Position.T -> extraction -> Context.generic -> Context.generic
  val check_extraction_group: Proof.context -> xstring * Position.T -> string
  val get_extraction_group: Proof.context -> string -> extraction list
  
  val prepare_code_thms_cmd: (xstring * Position.T) list -> Token.src list -> thm -> local_theory -> local_theory

  val sd_cmd: ((binding * Token.src list) * Token.src list) * string -> Proof.context -> Proof.state
  val sd_parser: Token.T list -> (((binding * Token.src list) * Token.src list) * string) * Token.T list
  
  
  val define_concrete_fun: extraction list option -> binding -> 
    Token.src list -> Token.src list -> indexname list -> thm ->
    cterm list -> local_theory -> (thm * thm) * local_theory
  
  val mk_qualified: string -> bstring -> binding

  (* Convert \<hole> to schematic variable *)
  val prepare_pattern: term -> term 
  
  val prepare_cd_pattern: Proof.context -> cterm -> cterm
  val add_cd_pattern: cterm -> Context.generic -> Context.generic
  val del_cd_pattern: cterm -> Context.generic -> Context.generic
  val get_cd_patterns: Proof.context -> cterm list

  val add_vc_rec_thm: thm -> Context.generic -> Context.generic
  val del_vc_rec_thm: thm -> Context.generic -> Context.generic
  val get_vc_rec_thms: Proof.context -> thm list

  val add_vc_solve_thm: thm -> Context.generic -> Context.generic
  val del_vc_solve_thm: thm -> Context.generic -> Context.generic
  val get_vc_solve_thms: Proof.context -> thm list

  val vc_solve_tac: Proof.context -> bool -> tactic'
  val vc_solve_modifiers: Method.modifier parser list

  val setup: theory -> theory
end

structure Definition_Utils :DEFINITION_UTILS = struct

  type extraction = {
    pattern: term,   (* Pattern to be defined as own constant *)
    gen_thm: thm,    (* Code eq generator: [| c==rhs; ... |] ==> c == ... *)
    gen_tac: local_theory -> tactic' (* Solves remaining premises of gen_thm *)
  }

  val eq_extraction = (op = o apply2 #pattern)
  
  structure extractions = Generic_Data (
    type T = extraction list Name_Space.table
    val empty = Name_Space.empty_table "Fixed-Point Extractions"
    val extend = I
    val merge = Name_Space.join_tables (fn _ => Library.merge eq_extraction)
  )

  fun declare_extraction_group binding context = let
    val table = extractions.get context
    val (name,table) = Name_Space.define context false (binding,[]) table
    val context = extractions.put table context
  in
    (name,context)
  end
  
  fun add_extraction namepos ex context = let
    fun f table = let
      val (key,_) = Name_Space.check context table namepos
      val table = Name_Space.map_table_entry key (Library.update eq_extraction ex) table
    in
      table
    end
  in
    extractions.map f context
  end
  
  fun check_extraction_group ctxt namepos = let
    val context = Context.Proof ctxt
    val table = extractions.get context
    val (key,_) = Name_Space.check context table namepos
  in
    key
  end
  
  fun get_extraction_group ctxt full_name = let
    val context = Context.Proof ctxt
    val table = extractions.get context
    val (_,exs) = Name_Space.check context table (full_name,Position.none)
  in 
    exs
  end
  
  
(*  
    Context.theory_map (extractions.map (
      Symtab.update_list (op = o apply2 #pattern) (name,ex)))
*)      

  (*
    Define new constant name for subterm t in context bnd.
    Returns replacement for t using the new constant and definition 
    theorem.
  *)
  fun extract_as_def bnd name t lthy = let
    val loose = rev (loose_bnos t);

    val nctx = Variable.names_of lthy
    val (name,nctx) = Name.variant name nctx (* TODO: Disambiguate name by appending serial_string() *)
    val name = name ^ serial_string()
    val (rnames,_) = fold_map (Name.variant o #1) bnd nctx
    
    (*val rnames = #1 (Variable.names_of lthy |> fold_map (Name.variant o #1) bnd);*)
    val rfrees = map (fn (name,(_,typ)) => Free (name,typ)) (rnames ~~ bnd);
    val t' = subst_bounds (rfrees,t);
    val params = map Bound (rev loose);
    
    val param_vars 
      = (Library.foldl (fn (l,i) => nth rfrees i :: l) ([],loose));
    val param_types = map fastype_of param_vars;

    val def_t = Logic.mk_equals 
      (list_comb (Free (name,param_types ---> fastype_of t'),param_vars),t')
    |> fold (Logic.all) param_vars 

    (* TODO: Makarius says: Use Local_Theory.define here! *)  
    val ((lhs_t,(_,def_thm)),lthy) 
      = Specification.definition NONE [] [] (Binding.empty_atts,def_t) lthy;

    (*val _ = tracing "xxxx";*)
    val app_t = list_comb (lhs_t, params);
  in 
    ((app_t,def_thm),lthy)
  end;


fun mk_qualified basename q = Binding.qualify true basename (Binding.name q);


local

  fun transform exs t lthy = let 
    val pat_net : extraction Item_Net.T =
      Item_Net.init (op= o apply2 #pattern) (fn {pattern, ...} => [pattern])
      |> fold Item_Net.update exs

    val thy = Proof_Context.theory_of lthy
      
    fun tr env t ctx = let
      (* Recurse for subterms *)
      val (t,ctx) = case t of
        t1$t2 => let
            val (t1,ctx) = tr env t1 ctx
            val (t2,ctx) = tr env t2 ctx
          in 
            (t1$t2,ctx)
          end
      | Abs (x,T,t) => let 
            val (t',ctx) = tr ((x,T)::env) t ctx
          in (Abs (x,T,t'),ctx) end
      | _ => (t,ctx)      

      (* Check if we match a pattern *)
      val ex = 
        Item_Net.retrieve_matching pat_net t
        |> get_first (fn ex => 
             case
               try (Pattern.first_order_match thy (#pattern ex,t)) 
                 (Vartab.empty,Vartab.empty)
             of NONE => NONE | SOME _ => SOME ex
           )
    in
      case ex of 
        NONE => (t,ctx)
      | SOME ex => let
          (* Extract as new constant *)
          val (idx,defs,lthy) = ctx
          val name = ("f_" ^ string_of_int idx)
          val ((t,def_thm),lthy) = extract_as_def env name t lthy
          val ctx = (idx+1,(def_thm,ex)::defs,lthy)
        in
          (t,ctx)
        end
    end
        
    val (t,(_,defs,lthy)) = tr [] t (0,[],lthy)
  in 
    ((t,defs),lthy)
  
  end

  fun simp_only_tac thms ctxt = simp_tac (put_simpset HOL_basic_ss ctxt addsimps thms)
  
in


fun extract_recursion_eqs [] _ def_thm lthy = ((def_thm,[],[]),lthy)
  | extract_recursion_eqs exs basename def_thm lthy = let
 
  val def_thm = Local_Defs.meta_rewrite_rule lthy def_thm

  (* Open local target *)
  val (_,lthy) = Local_Theory.begin_nested lthy 
  val lthy = Local_Theory.map_background_naming (Name_Space.mandatory_path basename) lthy
  
  val (def_thm, lthy) = yield_singleton (apfst snd oo Variable.import true) def_thm lthy
  
  val rhs = Thm.rhs_of def_thm |> Thm.term_of
  
  (* Transform RHS, generating new constants *)
  val ((rhs',aux_defs),lthy) = transform exs rhs lthy;
  val aux_def_thms = map #1 aux_defs
  
  (* Prove equality *)
  val rhs_eq_thm = Goal.prove_internal 
    lthy [] (Logic.mk_equals (rhs,rhs') |> Thm.cterm_of lthy)
    (K (ALLGOALS (simp_only_tac aux_def_thms lthy)))

  (* Generate new definition theorem *)  
  val code_thm = Thm.transitive def_thm rhs_eq_thm  
      
  (* Generate code equations *)
  fun mk_code_thm lthy (def_thm,{gen_thm, gen_tac, ...}) = let
    val ((_,def_thm),lthy') = yield_singleton2 
      (Variable.import true) def_thm lthy;
    val thm = def_thm RS gen_thm;
    val tac = SOLVED' (gen_tac lthy')
      ORELSE' (simp_only_tac aux_def_thms lthy' THEN' gen_tac lthy')
      (* TODO: The unfold auf_def_thms fallback is a dirty hack, to enable e.g., monotonicity proofs
        without proper mono-prover setup for the generated constants.
        
        A cleaner way would only generate constants along with mono-prover-setup!
      *)

    val thm = the (SINGLE (ALLGOALS tac) thm);
    val thm = singleton (Variable.export lthy' lthy) thm;
  in
    thm
  end;
  
  val aux_code_thms = map (mk_code_thm lthy) aux_defs;

  val _ = if forall Thm.no_prems aux_code_thms then () else 
    warning "Unresolved premises in code theorems"
    
  (* Close Target *)
  val lthy1 = lthy
  val lthy = Local_Theory.end_nested lthy

  (* Transfer Results *)
  val xfer = Local_Theory.standard_form lthy1 lthy Morphism.thm
  
  val code_thm = xfer code_thm
  val aux_code_thms = map xfer aux_code_thms
  val aux_def_thms = map xfer aux_def_thms
    
in
  ((code_thm,aux_code_thms,aux_def_thms),lthy)
end;

end

(*
fun extract_recursion_eqs exs basename orig_def_thm lthy = let
  val thy = Proof_Context.theory_of lthy
 
  val pat_net : extraction Item_Net.T =
    Item_Net.init (op= o apply2 #pattern) (fn {pattern, ...} => [pattern])
    |> fold Item_Net.update exs

  local
    fun tr env t ctx = let
      (* Recurse for subterms *)
      val (t,ctx) = case t of
        t1$t2 => let
            val (t1,ctx) = tr env t1 ctx
            val (t2,ctx) = tr env t2 ctx
          in 
            (t1$t2,ctx)
          end
      | Abs (x,T,t) => let 
            val (t',ctx) = tr ((x,T)::env) t ctx
          in (Abs (x,T,t'),ctx) end
      | _ => (t,ctx)      

      (* Check if we match a pattern *)
      val ex = 
        Item_Net.retrieve_matching pat_net t
        |> get_first (fn ex => 
             case
               try (Pattern.first_order_match thy (#pattern ex,t)) 
                 (Vartab.empty,Vartab.empty)
             of NONE => NONE | SOME _ => SOME ex
           )
    in
      case ex of 
        NONE => (t,ctx)
      | SOME ex => let
          (* Extract as new constant *)
          val (idx,defs,lthy) = ctx
          val name = (basename ^ "_" ^ string_of_int idx)
          val ((t,def_thm),lthy) = extract_as_def env name t lthy
          val ctx = (idx+1,(def_thm,ex)::defs,lthy)
        in
          (t,ctx)
        end
    end
  in
    fun transform t lthy = let 
      val (t,(_,defs,lthy)) = tr [] t (0,[],lthy)
    in 
      ((t,defs),lthy)
    end
  end

  (* Import theorem and extract RHS *)
  
  (* val lthy0 = lthy *)
  val orig_def_thm = Local_Defs.meta_rewrite_rule lthy orig_def_thm
  val args = Thm.lhs_of orig_def_thm |> Thm.term_of |> Term.strip_comb |> snd |> take_suffix is_Var
    |> map (fst o fst o dest_Var)
  
  val orig_def_thm = Local_Defs.abs_def_rule lthy orig_def_thm
  
  val ((_,orig_def_thm'),lthy) = yield_singleton2 
    (Variable.importT) orig_def_thm lthy;
  val (lhs,rhs) = orig_def_thm' (*|> Local_Defs.meta_rewrite_rule lthy *) |> Thm.prop_of |> Logic.dest_equals;
  
  (* Transform RHS, generating new constants *)
  val ((rhs',defs),lthy) = transform rhs lthy;
  val def_thms = map #1 defs

  (* Obtain new def_thm *)
  val def_unfold_ss = 
    put_simpset HOL_basic_ss lthy addsimps (orig_def_thm::def_thms)

  val _ = @{print}  (orig_def_thm::def_thms)
  
  local  
    val lthy0 = lthy
    val (argns,lthy) = Variable.variant_fixes args lthy
    
    val tys = fastype_of lhs |> binder_types |> take (length args)
    
    val args = map Free (argns ~~ tys)

    val lhs = list_comb (lhs,args)
    val rhs = list_comb (rhs',args)

    val new_def_ct = Logic.mk_equals (lhs,rhs) |> Thm.cterm_of lthy

    val _ = tracing "Prove"
    val new_def_thm = Goal.prove_internal lthy [] new_def_ct (K (simp_tac def_unfold_ss 1))
    val _ = tracing "Done"
  in 
    val new_def_thm = singleton (Variable.export lthy lthy0) new_def_thm
  end
  
  
  (*  
  val def_unfold_ss = 
    put_simpset HOL_basic_ss lthy addsimps (orig_def_thm::def_thms)
  val new_def_thm = Goal.prove_internal lthy
    [] (Logic.mk_equals (lhs,rhs') |> Thm.cterm_of lthy) (K (simp_tac def_unfold_ss 1))
  *)

  (* Obtain new theorem by folding with defs of generated constants *)
  (* TODO: Maybe cleaner to generate eq-thm and prove by "unfold, refl" *)
  (*val new_def_thm 
    = Library.foldr (fn (dt,t) => Local_Defs.fold lthy [dt] t) 
        (def_thms,orig_def_thm');*)

  (* Prepare code equations *)
  fun mk_code_thm lthy (def_thm,{gen_thm, gen_tac, ...}) = let
    val ((_,def_thm),lthy') = yield_singleton2 
      (Variable.import true) def_thm lthy;
    val thm = def_thm RS gen_thm;
    val tac = SOLVED' (gen_tac lthy')
      ORELSE' (simp_tac def_unfold_ss THEN' gen_tac lthy')

    val thm = the (SINGLE (ALLGOALS tac) thm);
    val thm = singleton (Variable.export lthy' lthy) thm;
  in
    thm
  end;
  
  val code_thms = map (mk_code_thm lthy) defs;

  val _ = if forall Thm.no_prems code_thms then () else 
    warning "Unresolved premises in code theorems"
    
in
  ((new_def_thm,code_thms,def_thms),lthy)
end;
*)

fun extract_recursion_eqs' exs basename attribs orig_def_thm lthy = let
  
  val ((new_def_thm,code_thms,def_thms),lthy) = extract_recursion_eqs exs basename orig_def_thm lthy

  (* Register definitions of generated constants *)
  val (_,lthy) 
    = Local_Theory.note ((mk_qualified basename "defs",[]),def_thms) lthy;
  
  val code_thms = new_def_thm::code_thms
    
  val (_,lthy) = Local_Theory.note 
    ((mk_qualified basename "code",attribs),code_thms)
     lthy;
in
  (code_thms,lthy)
end  

fun prepare_code_thms_cmd names attribs thm lthy = let
  fun name_of (Const (n,_)) = n 
    | name_of (Free (n,_)) = n
    | name_of _ = raise (THM ("No definitional theorem",0,[thm]));

  val (lhs,_) = thm |> Local_Defs.meta_rewrite_rule lthy |> Thm.prop_of |> Logic.dest_equals;
  val basename = lhs |> strip_comb |> #1 
    |> name_of 
    |> Long_Name.base_name;

  val exs_tab = extractions.get (Context.Proof lthy)
  
  val exs = map (Name_Space.check (Context.Proof lthy) exs_tab #> snd) names |> flat
  val exs = case exs of [] => Name_Space.dest_table exs_tab |> map snd |> flat | _ => exs

  val _ = case exs of [] => error "No extraction patterns selected" | _ => ()
  
  val (_,lthy) = extract_recursion_eqs' exs basename attribs thm lthy

in
  lthy
end;


fun extract_concrete_fun _ [] concl = 
  raise TERM ("Conclusion does not match any extraction pattern",[concl])
  | extract_concrete_fun thy (pat::pats) concl = (
      case Refine_Util.fo_matchp thy pat concl of
        NONE => extract_concrete_fun thy pats concl
        | SOME [t] => t
        | SOME (t::_) => (
          warning ("concrete_definition: Pattern has multiple holes, taking "
            ^ "first one: " ^ @{make_string} pat
          ); t)
        | _ => (warning ("concrete_definition: Ignoring invalid pattern " 
             ^ @{make_string} pat);
             extract_concrete_fun thy pats concl)
    )


(* Define concrete function from refinement lemma *)
fun define_concrete_fun gen_code fun_name attribs_def_raw attribs_ref_raw param_names thm pats
  (orig_lthy:local_theory) = 
let
  val lthy = orig_lthy;
  val ((inst,thm'),lthy) = yield_singleton2 (Variable.import true) thm lthy;

  val concl = thm' |> Thm.concl_of

  (*val ((typ_subst,term_subst),lthy) 
    = Variable.import_inst true [concl] lthy;
  val concl = Term_Subst.instantiate (typ_subst,term_subst) concl;
  *)

  val term_subst = #2 inst |> map (apsnd Thm.term_of) 

  val param_terms = map (fn name =>
    case AList.lookup (fn (n,v) => n = #1 v) term_subst name of
      NONE => raise TERM ("No such variable: "
                           ^Term.string_of_vname name,[concl])
    | SOME t => t
  ) param_names;

  (* 
  val _ = Syntax.pretty_term lthy concl |> Pretty.writeln
  val _ = Pretty.big_list "Patterns" (map (Syntax.pretty_term lthy o Thm.term_of) pats) |> Pretty.writeln
  *)
  
  val f_term = extract_concrete_fun (Proof_Context.theory_of lthy) pats concl;

  val lhs_type = map Term.fastype_of param_terms ---> Term.fastype_of f_term;
  val lhs_term 
    = list_comb ((Free (Binding.name_of fun_name,lhs_type)),param_terms);
  val def_term = Logic.mk_equals (lhs_term,f_term) 
    |> fold Logic.all param_terms;

  val attribs_def = map (Attrib.check_src lthy) attribs_def_raw;
  val attribs_ref = map (Attrib.check_src lthy) attribs_ref_raw;

  val ((_,(_,def_thm)),lthy) = Specification.definition 
    (SOME (fun_name,NONE,Mixfix.NoSyn)) [] [] ((Binding.empty,attribs_def),def_term) lthy;

  val folded_thm = Local_Defs.fold lthy [def_thm] thm';

  val basename = Binding.name_of fun_name
  
  val (_,lthy) 
    = Local_Theory.note 
       ((mk_qualified (basename) "refine",attribs_ref),[folded_thm]) 
       lthy;

  val lthy = case gen_code of
    NONE => lthy
  | SOME modes => let
      val (_,lthy) = extract_recursion_eqs' modes (Binding.name_of fun_name) @{attributes [code]} def_thm lthy
    in
      lthy
    end
      
      
in
  ((def_thm,folded_thm),lthy)
end;

  fun prepare_pattern t = let
    val nidx = maxidx_of_term t + 1
  
    val t_orig = t
    
    val t = map_aterms (fn 
          @{mpat (typs) "\<hole>::?'v_T"} => Var (("HOLE",nidx),T)
        | v as Var ((name,_),T) => if String.isPrefix "_" name then v else Var (("_"^name,nidx),T)
        | t => t
      ) t
    |> Term_Subst.zero_var_indexes
  
    fun is_hole (Var ((n,_),_)) = not (String.isPrefix "_" n)
      | is_hole _ = false
    
    val num_holes = fold_aterms (fn t => is_hole t ? (curry op + 1)) t 0  
      
    val _ = num_holes = 1 orelse raise TERM("cd-pattern has multiple or no holes",[t_orig,t])
  in
    t
  end


    (*val cfg_prep_code = Attrib.setup_config_bool @{binding synth_definition_prep_code} (K false)*)
    local 
      open Refine_Util
      (*val flags = parse_bool_config' "prep_code" cfg_prep_code
      val parse_flags = parse_paren_list' flags  *)

    in       
      val sd_parser = (*parse_flags --*) Parse.binding -- Parse.opt_attribs --| @{keyword "is"} 
        -- Scan.optional (Parse.attribs --| Parse.$$$ ":") [] -- Parse.term 
    end  


    fun sd_cmd (((name,attribs_def_raw),attribs_ref_raw),t_raw) lthy = let
      local
        (*val ctxt = Refine_Util.apply_configs flags lthy*)
      in
        (*val flag_prep_code = Config.get ctxt cfg_prep_code*)
      end

      val read = Syntax.read_prop (Proof_Context.set_mode Proof_Context.mode_pattern lthy)
      
      val t = t_raw |> read |> prepare_pattern
      val ctxt = Variable.declare_term t lthy
      val pat= Thm.cterm_of ctxt t
      val goal=t

      
      fun 
        after_qed [[thm]] ctxt = let
            val thm = singleton (Variable.export ctxt lthy) thm

            val (_,lthy) 
              = Local_Theory.note 
                 ((mk_qualified (Binding.name_of name) "refine_raw",[]),[thm]) 
                 lthy;

            val ((dthm,rthm),lthy) = define_concrete_fun NONE name attribs_def_raw attribs_ref_raw [] thm [pat] lthy

            (* FIXME: Does not work, as we cannot see the default extraction patterns!
            val lthy = lthy 
              |> flag_prep_code ? Refine_Automation.extract_recursion_eqs 
                [Sepref_Extraction.heap_extraction] (Binding.name_of name) dthm
            *)

            val _ = Thm.pretty_thm lthy dthm |> Pretty.string_of |> writeln
            val _ = Thm.pretty_thm lthy rthm |> Pretty.string_of |> writeln
          in
            lthy
          end
        | after_qed thmss _ = raise THM ("After-qed: Wrong thmss structure",~1,flat thmss)

    in
      Proof.theorem NONE after_qed [[ (goal,[]) ]] ctxt
    end

  
  
  

  val cd_pat_eq = apply2 (Thm.term_of #> Refine_Util.anorm_term) #> op aconv

  structure cd_patterns = Generic_Data (
    type T = cterm list
    val empty = []
    val extend = I
    val merge = merge cd_pat_eq
  ) 

  fun prepare_cd_pattern ctxt pat = 
    case Thm.term_of pat |> fastype_of of
      @{typ bool} => 
        Thm.term_of pat 
        |> HOLogic.mk_Trueprop 
        |> Thm.cterm_of ctxt
    | _ => pat

  fun add_cd_pattern pat context = 
    cd_patterns.map (insert cd_pat_eq (prepare_cd_pattern (Context.proof_of context) pat)) context

  fun del_cd_pattern pat context = 
    cd_patterns.map (remove cd_pat_eq (prepare_cd_pattern (Context.proof_of context) pat)) context

  val get_cd_patterns = cd_patterns.get o Context.Proof


    structure rec_thms = Named_Thms ( 
      val name = @{binding vcs_rec}
      val description = "VC-Solver: Recursive intro rules"
    )

    structure solve_thms = Named_Thms ( 
      val name = @{binding vcs_solve}
      val description = "VC-Solver: Solve rules"
    )

    val add_vc_rec_thm = rec_thms.add_thm
    val del_vc_rec_thm = rec_thms.del_thm
    val get_vc_rec_thms = rec_thms.get

    val add_vc_solve_thm = solve_thms.add_thm
    val del_vc_solve_thm = solve_thms.del_thm
    val get_vc_solve_thms = solve_thms.get

    val rec_modifiers = [
      Args.$$$ "rec" -- Scan.option Args.add -- Args.colon 
        >> K (Method.modifier rec_thms.add \<^here>),
      Args.$$$ "rec" -- Scan.option Args.del -- Args.colon 
        >> K (Method.modifier rec_thms.del \<^here>)
    ];

    val solve_modifiers = [
      Args.$$$ "solve" -- Scan.option Args.add -- Args.colon 
        >> K (Method.modifier solve_thms.add \<^here>),
      Args.$$$ "solve" -- Scan.option Args.del -- Args.colon 
        >> K (Method.modifier solve_thms.del \<^here>)
    ];

    val vc_solve_modifiers = 
      clasimp_modifiers @ rec_modifiers @ solve_modifiers;

    fun vc_solve_tac ctxt no_pre = let
      val rthms = rec_thms.get ctxt
      val sthms = solve_thms.get ctxt
      val pre_tac = if no_pre then K all_tac else clarsimp_tac ctxt
      val tac = SELECT_GOAL (auto_tac ctxt)
    in
      TRY o pre_tac
      THEN_ALL_NEW_FWD (TRY o REPEAT_ALL_NEW_FWD (resolve_tac ctxt rthms))
      THEN_ALL_NEW_FWD (TRY o SOLVED' (resolve_tac ctxt sthms THEN_ALL_NEW_FWD tac))
    end

    val setup = I
      #> rec_thms.setup 
      #> solve_thms.setup


end;
\<close>

setup Definition_Utils.setup


setup \<open>
  let
    fun parse_cpat cxt = let 
      val (t, (context, tks)) = Scan.lift Args.embedded_inner_syntax cxt 
      val ctxt = Context.proof_of context
      val t = Proof_Context.read_term_pattern ctxt t
           |> Definition_Utils.prepare_pattern
    in
      (Thm.cterm_of ctxt t, (context, tks))
    end

    fun do_p f = Scan.repeat1 parse_cpat >> (fn pats => 
        Thm.declaration_attribute (K (fold f pats)))
  in
    Attrib.setup @{binding "cd_patterns"} (
       Scan.lift Args.add |-- do_p Definition_Utils.add_cd_pattern
    || Scan.lift Args.del |-- do_p Definition_Utils.del_cd_pattern
    || do_p Definition_Utils.add_cd_pattern
    )
      "Add/delete concrete_definition pattern"
  end
\<close>

(* Command setup *)

(* TODO: Folding of .refine-lemma seems not to work, if the function has
  parameters on which it does not depend *)

ML \<open> Outer_Syntax.local_theory 
  @{command_keyword concrete_definition} 
  "Define constant from theorem"
  (Parse.binding 
    -- Parse.opt_attribs
    -- Scan.optional (@{keyword "for"} |-- Scan.repeat1 Args.var) []
    --| @{keyword "is"} -- Parse.opt_attribs -- Parse.thm
    -- Scan.optional (@{keyword "uses"} |-- Scan.repeat1 Args.embedded_inner_syntax) []
  >> (fn (((((name,attribs_def),params),attribs_ref),raw_thm),pats) => fn lthy => let
    val thm = 
      case Attrib.eval_thms lthy [raw_thm] of
        [thm] => thm
        | _ => error "Expecting exactly one theorem";
    val pats = case pats of 
      [] => Definition_Utils.get_cd_patterns lthy
    | l => map (Proof_Context.read_term_pattern lthy #> Definition_Utils.prepare_pattern #> Thm.cterm_of lthy #>
        Definition_Utils.prepare_cd_pattern lthy) l

  in 
    Definition_Utils.define_concrete_fun 
      NONE name attribs_def attribs_ref params thm pats lthy 
    |> snd
  end))
\<close>

text \<open> 
  Command: 
    @{text "concrete_definition name [attribs_def] for params is [attribs_ref] thm uses patterns"}
  where @{text "attribs_..."}, @{text "for"}, and @{text "uses"}-parts are optional.

  Declares a new constant @{text "name"} by matching the theorem @{text "thm"} 
  against a pattern.
  
  The definition theorem of the constant gets the attributes specified in \<open>attribs_def\<close>.
  Moreover, a new theorem is derived from \<open>thm\<close>, with the defined constant folded.
  This is registered as \<open>name.refine\<close>, with attributes [attribs_ref].
  
  If the @{text "for"} clause is given, it lists variables in the theorem, 
  and thus determines the order of parameters of the defined constant. Otherwise,
  parameters will be in order of occurrence.

  If the @{text "uses"} clause is given, it lists patterns. The conclusion of the
  theorem will be matched against each of these patterns. For the first matching
  pattern, the constant will be declared to be the term that matches the first
  non-dummy variable of the pattern. If no @{text "uses"}-clause is specified,
  the default patterns will be tried.

  Attribute: @{text "cd_patterns pats"}. Declaration attribute. Declares
    default patterns for the @{text "concrete_definition"} command.
  
\<close>

declare [[ cd_patterns "_ = \<hole>" "_ == \<hole>" ]]

ML_val \<open>Parse.binding\<close>

ML_val \<open>val x:binding = Binding.empty\<close>

ML_val \<open>@{binding foo}\<close>

ML \<open> 
  let
    val modes = (Scan.optional
     (@{keyword "("} |-- Parse.list1 (Parse.position Args.name) --| @{keyword ")"}) [])
  in
    Outer_Syntax.local_theory 
    @{command_keyword prepare_code_thms} 
    "Extract recursive code equations from definition theorem with fixed points"
    (modes -- Parse.opt_attribs -- Parse.thms1
      >> (fn ((modes,attribs),raw_thms) => fn lthy => let
        val attribs = map (Attrib.check_src lthy) attribs
        val thms = Attrib.eval_thms lthy raw_thms
      in
        fold (Definition_Utils.prepare_code_thms_cmd modes attribs) thms lthy
      end)
    )
  end
\<close>

text \<open> 
  Command: 
    @{text "prepare_code_thms (modes) thm"}
  where the @{text "(mode)"}-part is optional.

  Set up code-equations for recursions in constant defined by @{text "thm"}.
  The optional @{text "modes"} is a comma-separated list of extraction modes.
\<close>

text \<open>Example setup for option monad fixed points\<close>

lemma gen_code_thm_option_fixp:
  fixes x
  assumes D: "f \<equiv> option.fixp_fun B"
  assumes M: "(\<And>x. option.mono_body (\<lambda>f. B f x))"
  shows "f x \<equiv> B f x"
  unfolding D
  apply (subst option.mono_body_fixp)
  by (rule M)

ML_val \<open>
  Definition_Utils.add_extraction ("option",\<^here>) {
    pattern = Logic.varify_global @{term "option.fixp_fun x"},
    gen_thm = @{thm gen_code_thm_option_fixp},
    gen_tac = Partial_Function.mono_tac
  }
\<close>
  
declaration \<open>K (Definition_Utils.declare_extraction_group @{binding option} #> snd)\<close>
  
declaration \<open> fn _ =>
  Definition_Utils.add_extraction ("option",\<^here>) {
    pattern = Logic.varify_global @{term "option.fixp_fun x"},
    gen_thm = @{thm gen_code_thm_option_fixp},
    gen_tac = Partial_Function.mono_tac
  }
\<close>

  definition "option_fixp_extraction_test m n = option.fixp_fun (\<lambda>D x. 
    if x\<le>(0::int) then 
      Some 0 
    else 
      Option.bind (D (x-int m)) (\<lambda>a.
      Option.bind (D (x-n)) (\<lambda>b.
      Some (a+b)
    )))"

  prepare_code_thms (option) [code] option_fixp_extraction_test_def
  print_theorems
  export_code option_fixp_extraction_test in SML

ML \<open>
val _ = Theory.setup
  (ML_Antiquotation.inline \<^binding>\<open>extraction_group\<close>
    (Args.context -- Scan.lift (Parse.position Args.embedded) >>
      (fn (ctxt, name) => ML_Syntax.print_string (Definition_Utils.check_extraction_group ctxt name))));
\<close>  

text \<open> 
  Command: 
    @{text "synth_definition binding [def_attrs] is [ref_attrs]: term"}
  where the @{text "(def_attrs)"} and @{text "(ref_attrs)"} parts are optional.

  Sets up a schematic goal with a hole, proves the schematic goal, and  
  define what has been inserted into the hole as a new constant. 
  Moreover, generate a refinement theorem for the proved goal with the hole replaced by 
  the defined constant.
  
  The \<open>def_attrs\<close> are applied to the definition theorem, the \<open>ref_attrs\<close> to 
  the refinement theorem.
\<close>
  
  
ML \<open>
  local open Definition_Utils in
    val _ = Outer_Syntax.local_theory_to_proof @{command_keyword "synth_definition"}
      "Synthesis of constant from schematic goal with hole"
      (sd_parser >> sd_cmd)
  
  end
\<close>
  
end
