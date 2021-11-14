(*
  Simple query tool for theorem collections.
  
  Syntax: find_in_thms pattern* in thm+
  
  TODO: If Find_Theorems would export an interface to 
    decouple filtering theorems from acquiring list of theorems to filter,
    this could re-use code from there, instead of duplicating it!
    
*)

theory Find_In_Thms
  imports Main
  keywords "find_in_thms" :: diag
begin

ML \<open>
    
  structure Find_In_Thms = struct
  
    (* filter_pattern *)
    
    fun expand_abs t =
      let
        val m = Term.maxidx_of_term t + 1;
        val vs = strip_abs_vars t;
        val ts = map_index (fn (k, (_, T)) => Var ((Name.aT, m + k), T)) vs;
      in betapplys (t, ts) end;
    
    fun get_names t = Term.add_const_names t (Term.add_free_names t []);
    
    (* Does pat match a subterm of obj? *)
    fun matches_subterm ctxt (pat, obj) =
      let
        val thy = Proof_Context.theory_of ctxt;
        fun matches obj ctxt' = Pattern.matches thy (pat, obj) orelse
          (case obj of
            Abs _ =>
              let val ((_, t'), ctxt'') = Variable.dest_abs obj ctxt'
              in matches t' ctxt'' end
          | t $ u => matches t ctxt' orelse matches u ctxt'
          | _ => false);
      in matches obj ctxt end;
      
    (*
    fun matches_subterm ctxt (pat, obj) =
      let
        fun msub bounds obj = Pattern.matches thy (pat, obj) orelse
          (case obj of
            Abs (_, T, t) => msub (bounds + 1) (snd (Term.dest_abs (Name.bound bounds, T, t)))
          | t $ u => msub bounds t orelse msub bounds u
          | _ => false)
      in msub 0 obj end;
    *)
    
    fun filter_pattern ctxt pat =
      let
        val pat' = (expand_abs o Envir.eta_contract) pat;
        fun check thm = matches_subterm ctxt (pat', Thm.full_prop_of thm);
      in check end;

      
    val _ =
      Outer_Syntax.command \<^command_keyword>\<open>find_in_thms\<close>
        "find theorems matching specified patterns in theorem collection"
        (Scan.repeat Parse.term -- (\<^keyword>\<open>in\<close> |-- Parse.thms1)  >> (fn (pats,thms) =>
          Toplevel.keep (fn st => let
            val ctxt = Toplevel.context_of st
            
            fun is_plain (Facts.Named (_,NONE), []) = true
              | is_plain _ = false
            
            fun prt_of (r,s) = if is_plain (r,s) then Pretty.str (Facts.string_of_ref r)
              else Pretty.enclose "\<guillemotleft>" "\<guillemotright>" [
                  Pretty.str (Facts.string_of_ref r), 
                    Pretty.list "[" "]" (map (Token.pretty_src ctxt) s)]
            
            val thms = thms ~~ map (Attrib.eval_thms ctxt o single) thms
              |> map (apfst prt_of #> apsnd (tag_list 1))
              |> map (fn (name,ls) => map (fn (i,thm) => ((name,i),thm)) ls)
              |> flat
             
            
            val pats = map (Proof_Context.read_term_pattern ctxt) pats
            
            val filters = map (filter_pattern ctxt) pats
            fun flt (_,thm) = forall (fn flt => flt thm) filters
            val thms = filter flt thms 
            
            fun pretty_thm ((n,i),thm) = Pretty.block [
              n,Pretty.enclose "(" ")" [Pretty.str (string_of_int i)],Pretty.str ":",Pretty.brk 1,
              Thm.pretty_thm ctxt thm]
            
            val _ = map pretty_thm thms |> Pretty.big_list "Results" |> Pretty.writeln
          in () end)));

  end          
\<close>


end
