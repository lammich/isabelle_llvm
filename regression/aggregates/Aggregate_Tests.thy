theory Aggregate_Tests
imports "Isabelle_LLVM.LLVM_DS_All"
begin

  (*
    Test for aggregates:
  
    Main goal:
      Computations by LLVM, Codegen, and C compiler match on aggregates
    
    Coverage goal:
      * sizeof and alignment computations
      * include nested aggregates. Anonymous and named. 
        * play with alignment constraints, e.g. {i8, { i8, i32 } } vs {i8, i8, i32}
      * include struct and union
      * include all alignment cases: max-size = max-align, or max-align \<noteq> max-size
      
    Test procedure/infrastructure  
      
      * generate random aggregate types
      * convert to LLVM and C types
      * check Codegen.sizeof T = LLVM.sizeof T
        * generate LLVM code that compares static sizeof of gep-based sizeof  
          returns true/false
      * check Codegen.sizeof T = C.sizeof(T)
        * generate C program for check
          reports success/error (message and exit-code)
      
      TODO:    
      * alignment/sizeof check (2)
        * LLVM code: allocate array of two Ts, write to first, check second is still zeroinitialized
          returns true/false

      TODO:    
      * matching check: write struct/union fields in C/LLVM, check in LLVM/C
                  
    Overall infrastructure:
      * command to generate tests: parse type T, write agg_test_T.{ll,c}

      
  *)

  declare [[llc_compile_union=true]]  
  
  ML \<open>
    structure Aggregate_Tests = struct
      local 
        open Parser_Util 
        open LLC_Intermediate
              
      in
      
        val parse_id = Parse.short_ident

        fun assert_positive n = if n>0 then n else raise Fail("Positive number expected: " ^ quote (Int.toString n))
                
        val scan_int_type = unprefix "i" #> Value.parse_nat #> assert_positive #> TInt 
        
        val parse_int_type = ident_with (can scan_int_type) >> scan_int_type
        
        val is_ptr = String.explode #> forall (fn x => x = #"*")
        
        val parse_ptr = kind_with Token.Sym_Ident is_ptr
        
        fun parse_type_np s = (
             parse_int_type
          || pkw "float" >> K TFloat
          || pkw "double" >> K TDouble
          || parse_id >> TNamed
          || pcm "{" |-- Parse.enum1 "," parse_type --| pcm "}" >> TStruct
          || pcm "u{" |-- Parse.enum1 "," parse_type --| pcm "}" >> TUnion
        ) s
        and parse_type s = (
          parse_type_np -- (Scan.repeat parse_ptr >> map String.explode >> flat) >> (fn (T,ms) => fold (K TPtr) ms T)
        ) s
        
    
        val kws = ["float","double","{","}","u{",","]
    
        val check_type = parse_inner kws parse_type
  
      end
  
      
      local open C_Interface in
      
        infix 3 >>=
      
        fun m >>= f = map f m |> flat
        
        fun mapM _ [] = single []
          | mapM f (x::xs) = f x >>= (fn x' => mapM f xs >>= (fn xs' => single (x'::xs')))
        
        
        fun cty_names _ (CTYO_PRIM p) = CTY_PRIM p
          | cty_names pre (CTYO_PTR t) = CTY_PTR (cty_names pre t)
          | cty_names _ (CTYO_NAMED s) = CTY_NAMED s
          | cty_names pre (CTYO_STRUCT flds) = CTY_STRUCT (map (cty_names_fld pre) (tag_list 0 flds))
          | cty_names pre (CTYO_UNION flds) = CTY_UNION (map (cty_names_fld pre) (tag_list 0 flds))
        and 
            cty_names_fld pre (i,FLDO_NAMED (SOME t,_)) = FLD_NAMED (cty_names pre t, "f"^pre^Int.toString i)
          | cty_names_fld _ _ = error "cty_names_fld: no type-info for field"
      
        (*  
        fun cty_names _ (CTYO_PRIM p) = single (CTY_PRIM p)
          | cty_names pre (CTYO_PTR t) = map CTY_PTR (cty_names pre t)
          | cty_names _ (CTYO_NAMED s) = single (CTY_NAMED s)
          | cty_names pre (CTYO_STRUCT flds) = map CTY_STRUCT (mapM (cty_names_fld pre) (tag_list 0 flds))
          | cty_names pre (CTYO_UNION flds) = map CTY_UNION (mapM (cty_names_fld pre) (tag_list 0 flds))
        and 
            cty_names_fld pre (i,FLDO_NAMED (SOME (t as CTYO_STRUCT flds),_)) = 
              (cty_names pre t >>= (fn t => single (FLD_NAMED (t, "f"^pre^Int.toString i))))
            @ map FLD_ANON (mapM (cty_names_fld (pre^"n")) (tag_list 0 flds))
            
          | cty_names_fld pre (i,FLDO_NAMED (SOME t,_)) = cty_names pre t >>= (fn t => single (FLD_NAMED (t, "f"^pre^Int.toString i)))
          | cty_names_fld _ _ = error "cty_names_fld: no type-info for field"
        *)
      
      
      end
      
      local open LLVM_Builder in
      
        fun mk_ll_sizeof_test b name lty = let
          val _ = open_proc b (SOME (mkty_i 8)) name [] []
          val dy_sz = mk_size_of b (SOME "") lty
          val st_sz = sizeof_ty b lty |> mkc_i (size_t b)
          val res = mk_icmp_instr "eq" b (SOME "") dy_sz st_sz
          val res = mk_conv_instr "zext" b (SOME "") res (mkty_i 8)
          val _ = mk_return b (SOME res)
          val _ = close_proc b
        in
          ()
        end

        fun mk_ll_sizeof_get b name lty = let
          val _ = open_proc b (SOME (size_t b)) name [] []
          val st_sz = sizeof_ty b lty |> mkc_i (size_t b)
          val _ = mk_return b (SOME st_sz)
          val _ = close_proc b
        in
          ()
        end
              
      end
      
      local
        open Simple_PP 
      in      
      
      
      end
  
      fun make_test ctxt i llT = let
        val cT = C_Interface.cty_of_lty llT |> cty_names "" |> C_Interface.ctype_to_Cs
    
        val name = "aggr_test_" ^ Int.toString (i)
        val name_get = name ^ "_get"
        val name_test = name ^ "_test"
    
        val using_master_directory =
          File.full_path (Resources.master_directory (Proof_Context.theory_of ctxt));
        
        val base_path = ("../../regression/aggregates/generated/" ^ name)
          |> Path.explode |> using_master_directory
        val ll_path = Path.ext "gen.ll" base_path
        val c_path = Path.ext "c" base_path
          
        val b = LLVM_Builder.builder LLVM_Builder.target_x86_64_linux
            
        val lty = LLC_Backend.llc_ty b llT
        val sz = LLVM_Builder.sizeof_ty b lty
        val _ = mk_ll_sizeof_get b name_get lty
        val _ = mk_ll_sizeof_test b name_test lty
        
        (*val _ = @{print} ll_path*)
        val _ = LLVM_Builder.string_of b |> File.write ll_path
        
        
        local open C_Interface Simple_PP in
          val decls = fbrks [
            block [word "char",fsep,word name_test,nword "()",nword ";"],
            block [word "size_t",fsep,word name_get,nword "()",nword ";"],
            fbrk,
            block [word "typedef",cT,word "test_t",nword ";"],
            fbrk,
            block [word "test_t",word "test_v",nword ";"],
            block [word "size_t",word "test_size",nword "=",word "sizeof(test_t)",nword ";"]
          ] 
          
          val C_test = block [
            line [nword "if (sizeof(test_t) != ", int sz, nword ") error(\"static vs C size test failed\");"]
          ]
    
          val C_tests = fbrks [
            line [nword "if (!",word name_test,nword "()) error(\"static vs dynamic LLVM size test failed\");"],
            C_test]
          
          val ccode = fbrks [
            word "#include \"../aggr_test_common.h\"",
            decls,
            word "int main() {",
            block_indent 1 [C_tests,word "return 0;",fbrk],
            word "}"
          ]
          
        end  
        
        val _ = ccode |> Simple_PP.string_of |> File.write c_path
      in () end    
            
    end
  \<close>
  
  
  
  ML \<open>
    (*  Adapted from Larry's Random.ML, to allow for control over seeds *)
    signature RANDOM_GEN =
    sig
      type T
      val make: real -> T
      val random: T -> real
      val random_range: T -> int -> int -> int
      exception RANDOM_GEN;
    end;
    
    structure Random_Gen: RANDOM_GEN =
    struct
    
      fun rmod x y = x - y * Real.realFloor (x / y);
  
      type T = real Synchronized.var
      
      fun make seed = Synchronized.var "Rand_Gen seed" seed
        
      local
        val a = 16807.0;
        val m = 2147483647.0;
      in
      
        fun random rgstate =
          Synchronized.change_result rgstate
            (fn r => let val r' = rmod (a * r) m in (r', r') end);
      
      end;
    
      exception RANDOM_GEN;
    
      fun random_range rgstate l h =
        if h < l orelse l < 0 then raise RANDOM_GEN
        else l + Real.floor (rmod (random rgstate) (real (h - l + 1)));
      
    end;
  \<close>
  
  
  ML \<open>
    fun random_el rg xs = nth xs (Random_Gen.random_range rg 0 (length xs - 1))
    
    fun random_wel rg xs = map (uncurry replicate) xs |> flat |> random_el rg  (* TODO: Inefficient *)
    

    local    
      open LLC_Intermediate
    in
      fun llc_random_int rg = TInt (random_el rg [8,16,32,64])
    
      fun llc_random_prim rg = random_el rg [llc_random_int, K TFloat, K TDouble] rg
    
      fun llc_random_field_num rg = random_wel rg (
          map (pair 8) (1 upto 2)
        @ map (pair 4) (3 upto 4)
        @ map (pair 2) (5 upto 8)
        @ map (pair 1) (9 upto 16)
      )
      
      
      fun max a b = if a>=b then a else b
      
      fun llc_random_ty d rg = random_wel rg [(8,llc_random_prim),(2,llc_random_ptr),(max 1 (4-d),llc_random_struct (d+1)),(max 1 (4-d),llc_random_union (d+1))] rg
      and llc_random_ptr rg = TPtr (llc_random_int rg)
      and llc_random_fields d rg = map (llc_random_ty d) (replicate (llc_random_field_num rg) rg)
      and llc_random_struct d rg = TStruct (llc_random_fields d rg)
      and llc_random_union d rg = TUnion (llc_random_fields d rg)
      
    
    end    
    
    val rg = Random_Gen.make 1.0
    
    val tests = map (llc_random_struct 0) (replicate 1000 rg) |> distinct (op =) |> tag_list 1

    (*val tests = let open LLC_Intermediate in [(1,TUnion [TDouble, TStruct [TInt 8, TInt 32, TInt 32]])] end*)
    
    val _ = writeln ("Creating " ^ Int.toString (length tests) ^ " tests")
    
    
    val _ = map (uncurry (Aggregate_Tests.make_test @{context})) tests
    val _ = writeln ("Done")
  \<close>


end
