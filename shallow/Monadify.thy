theory Monadify
imports Main "Automatic_Refinement.Refine_Util"
begin
  (* TODO: Move *)
  ML \<open>
    (* Simplified output of rough term structure, for debugging purposes *)
    structure Simplified_Term_Struct : sig
      val tstruct: term -> string
    end = struct
      fun par b s = if b then "("^s^")" else s
    
      fun psi_aux p env = let
        fun r (Const (n,_)) = Long_Name.base_name n
          | r (Var (n,_)) = Term.string_of_vname n
          | r (Free (n,_)) = n
          | r (Bound i) = nth env i
          | r (Abs (x,_,t)) = par p (let val x = singleton (Name.variant_list env) x in "\<lambda>"^x^". "^psi_aux false (x::env) t end)
          | r (t as _$_) = let
              val (f,args) = strip_comb t
              val f = psi_aux true env f
              val args = map (psi_aux true env) args |> space_implode " "
              val s = f^" "^args
            in par p s end    
      in
        r
      end
      
      val tstruct = psi_aux false []
    end
  \<close>

  lemma eta_expand: "f \<equiv> \<lambda>x. f x" by (rule reflexive)
    
  ML \<open>
    functor Gen_Monadify (
      (*
        Assumes that the monad combinators have the form return$x and bind$m$f
      *)
    
      val mk_return: term -> term
      val mk_bind: term -> term -> term
      val dest_return: term -> term option
      val dest_bind: term -> (term * term) option
      val dest_monadT: typ -> typ option
      val strip_op: Proof.context -> term -> term * term list

      (* TODO: Probably can derive mk and dest functions from these theorems! *)
      val bind_return_thm : thm  (* bind m return = m *)
      val return_bind_thm : thm  (* bind (return x) f = f x  *)
      val bind_bind_thm : thm    (* bind (bind m f) g = bind m (\<lambda>x. bind (f x) g) *)
          
    ) = struct

      
    
      val monad_laws = [bind_return_thm, return_bind_thm, bind_bind_thm]
      
      
      val is_return = is_some o dest_return
      val is_bind = is_some o dest_bind
    
      val dest_monadT' = the o dest_monadT
      val is_monadT = is_some o dest_monadT
      val is_monadic = is_monadT o fastype_of
      
      
      local open Conv in

        (* TODO: Move, generally useful *)
        (* Apply conversion to direct subterms, fail if conversion fails for a subterm *)
        fun sub_conv' conv ctxt ct = (case Thm.term_of ct of
          Abs _ => abs_conv (conv o snd) ctxt
        | _$_ => comb_conv (conv ctxt)  
        | _ => all_conv
        ) ct

      end          
              
      local 
        open Conv 
        
        fun ensure_eta_conv ct = 
          (case Thm.term_of ct of 
            Abs _ => all_conv
          | _ => rewr_conv @{thm eta_expand}
          ) ct
          
        fun expand_return_thm ctxt =
          Local_Defs.meta_rewrite_rule ctxt bind_return_thm
          RS @{thm Pure.symmetric}
          
      in  
        
        fun eta_ret_conv ctxt ct = (let 
          val t = Thm.term_of ct 
          val bnd_conv = 
            arg_conv ensure_eta_conv 
            then_conv arg1_conv (sub_conv' eta_ret_conv ctxt)
            then_conv arg_conv (abs_conv (eta_ret_conv o snd) ctxt)
            
        in
          if is_monadic t then
            if is_bind t then bnd_conv
            else if is_return t then arg_conv (eta_ret_conv ctxt)
            else rewr_conv (expand_return_thm ctxt) then_conv bnd_conv
          else
            sub_conv' eta_ret_conv ctxt
        end) ct
        
      end  
      
      
      (* Generate a bind, the second term is created by F x, where x is the bound variable *)
      fun BIND M F ctxt = let
        val m = M ctxt
        val T = fastype_of m |> dest_monadT'
        val (n,ctxt) = yield_singleton Variable.variant_fixes "tmp" ctxt
        val x = Free (n,T)
        
        val f = Term.lambda x (F x ctxt)
      in 
        mk_bind m f
      end

      fun ABS_CNV (x,T,t) cnv ctxt = let
        val (n,ctxt) = yield_singleton Variable.variant_fixes x ctxt
        val t = subst_bound (Free (n,T), t)
        val t = cnv t ctxt
        val t = Term.absfree (n,T) t
      in t end  
          
      fun mk_return' t _ = mk_return t
      
      fun is_operand (Free _) = true
        | is_operand (Var _) = true
        | is_operand (Bound _) = true
        | is_operand _ = false

      val is_ho_operand = fastype_of #> body_type #> is_monadT
             
      fun process_ho_operand t = let
        val (argTs,T) = fastype_of t |> strip_type
      in
        is_monadT T andalso length (strip_abs_vars t) = length argTs
      end  
      
       
      fun mk_operand t F = 
        if is_operand t then F t 
        else if is_ho_operand t then fn ctxt => F (mk_monadify_all t ctxt) ctxt
        else BIND (mk_operation t mk_return') F
      and mk_operation t F ctxt = let
            val (f,xs) = strip_op ctxt t
            fun R t [] = F t | R t (x::xs) = mk_operand x (fn x => R (t$x) xs)
          in
            R f xs ctxt
          end
      and mk_monadify (Abs xTt) = ABS_CNV xTt mk_monadify
        | mk_monadify t = case dest_return t of
            SOME x => mk_operation x mk_return'
          | NONE => mk_operation t (fn t => K t)
      and mk_monadify_all (Abs xTt) = ABS_CNV xTt mk_monadify_all
        | mk_monadify_all t = 
            if is_monadT (fastype_of t) then mk_monadify t 
            else fn ctxt =>
              strip_comb t |> apsnd (map (fn t => mk_monadify_all t ctxt)) |> list_comb
            
      
      fun monadify ctxt t = mk_monadify t (Variable.declare_term t ctxt |> Variable.set_body false)
          
      fun monadify_conv ctxt ct = let
          val _ = is_monadT (Thm.typ_of_cterm ct |> body_type) 
            orelse raise TYPE("No monad type",[Thm.typ_of_cterm ct],[Thm.term_of ct])
      
          val ctxt = put_simpset HOL_basic_ss ctxt addsimps monad_laws
          val tac = ALLGOALS (simp_tac ctxt)
        in Refine_Util.f_tac_conv ctxt (monadify ctxt) tac then_conv eta_ret_conv ctxt end ct
        
      val monadify_all_conv = Conv.top_sweep_conv monadify_conv
        
      val monadify_all_tac = CONVERSION o monadify_all_conv
        
    end
  \<close>

  ML \<open>
    functor Gen_Monadify_Cong (
      val mk_return: term -> term
      val mk_bind: term -> term -> term
      val dest_return: term -> term option
      val dest_bind: term -> (term * term) option
      val dest_monadT: typ -> typ option
      
      val bind_return_thm : thm  (* bind m return = m *)
      val return_bind_thm : thm  (* bind (return x) f = f x  *)
      val bind_bind_thm : thm    (* bind (bind m f) g = bind m (\<lambda>x. bind (f x) g) *)
    
    ) = struct
          
      structure Consts = Generic_Data (
        type T = term Item_Net.T
        val empty = Item_Net.init (op aconv) single
        val merge = Item_Net.merge
        val extend = I
      )    
  
      val add_const_decl = Consts.map o Item_Net.update
      val remove_const_decl = Consts.map o Item_Net.remove
      val get_const_decls = Context.Proof #> Consts.get #> Item_Net.content
      
      fun prepare_const_decl t ctxt = let
        val t = singleton (Variable.export_terms (Variable.auto_fixes t ctxt) ctxt) t
        
        val _ = is_Var (head_of t) andalso 
          (Pretty.block [
            Pretty.str "Head of const is variable: ", 
            Syntax.pretty_term ctxt t
           ]) |> Pretty.string_of |> error
        
      in
        t
      end
      
      fun prepare_add_const_decl t context = add_const_decl (prepare_const_decl t (Context.proof_of context)) context
      
      
      fun is_const ctxt t = 
        Item_Net.retrieve_matching (Consts.get (Context.Proof ctxt)) t 
        |> exists (K true)
            
      fun strip_op ctxt t = let
        fun stripc (t as f$x, xs) = if is_const ctxt t then (t,xs) else stripc (f,x::xs) 
          | stripc tt = tt
      in stripc (t,[]) end

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
  \<close>
  
  (*
  (* Test Monad *)
  
  datatype 'a M = return 'a
  definition "bind \<equiv> \<lambda>return x \<Rightarrow> \<lambda>f. f x"
  
  lemma monad_laws: 
    "bind m return = m"
    "bind (return x) f = f x"
    "bind (bind m (\<lambda>x. f x)) g = bind m (\<lambda>x. bind (f x) g)"
    unfolding bind_def by (auto split: M.split)
  
  ML \<open>
  
    structure Monadify = Gen_Monadify_Cong (
    
      fun mk_return x = @{mk_term "return ?x"}
      fun mk_bind m f = @{mk_term "bind ?m ?f"}
    
      fun dest_return @{mpat "return ?x"} = SOME x | dest_return _ = NONE
      fun dest_monadT (Type (@{type_name M},[T])) = SOME T | dest_monadT _ = NONE
      
      val monad_laws = @{thms monad_laws}
    )
  \<close>
    
  
  ML_val \<open>
    val t1 = @{term "let (x,y) = p in (return (x+y+y))"} |> Simplified_Term_Struct.tstruct
    val t2 = @{term "case p of (x,y) \<Rightarrow> (return (x+y+y))"} |> Simplified_Term_Struct.tstruct
  \<close> 
  
  
  ML_val \<open>
    val ctxt = @{context}
    val ts = [
      @{term "case p of (x,y) \<Rightarrow> return (x+y+y)"},
      @{term "let (x,y) = p in return (x+y+y)"}
    ]
    
    val ts = map (Monadify.monadify ctxt #> Simplified_Term_Struct.tstruct) ts
  \<close>  
  
  lemma "P (let (x,y) = p in return (x+y+y))"
    apply (tactic \<open>CONVERSION (HOLogic.Trueprop_conv (Conv.arg_conv (Monadify.monadify_conv @{context}))) 1\<close>)
    oops
  
  
  
  context
    fixes a :: "'a list"
   begin
  
  ML_val \<open>
    val ctxt = @{context}
    val t = @{term "a @ b"}
    val ctxt' = Variable.auto_fixes t ctxt
    
    
    val t = singleton (Variable.export_terms ctxt' ctxt) t
    
    
  \<close>
  end
  
  ML_val \<open>
    let
      open Monadify
      val ctxt = @{context}
      
      val ctxt = add_const_decl (prepare_const_decl ctxt @{term "hd f"}) ctxt
      
      val t = @{cterm \<open>return (hd ([a,b,c]) (g x y))\<close>}
      val t = monadify_conv ctxt t
    
    in 
      t
    end  
  
  \<close>
  *)
end
