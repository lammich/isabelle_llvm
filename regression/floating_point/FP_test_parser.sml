structure FP_test_parser = struct


  fun error msg = (
    print("ERROR: " ^ msg ^ "\n");
    OS.Process.exit(OS.Process.failure)
  )

  local
    open FP_test_base
  in

    val bias32=127;

    fun hex_to_int s =
      case StringCvt.scanString (Int.scan StringCvt.HEX) s of
        NONE => error("No hex number " ^ s)
      | SOME i => IntInf.fromInt i

    fun dec_to_int s =
      case StringCvt.scanString (Int.scan StringCvt.DEC) s of
        NONE => error("No dec number " ^ s)
      | SOME i => IntInf.fromInt i

    fun sign_to_int "-" = IntInf.fromInt 1
      | sign_to_int "+" = IntInf.fromInt 0

    fun xlate_opr_fp32 s = case String.tokens (fn x => x = #"|") s of
      [s,"1",f,e] => fp32 (sign_to_int s) (hex_to_int f) (dec_to_int e + bias32)
    | [s,"0",f,"-126"] => fp32 (sign_to_int s) (hex_to_int f) (0)
    | _ => error("Invalid operand " ^ s)

    val xlate_hex_opr32 = single_of_int o hex_to_int
    val xlate_hex_opr64 = double_of_int o hex_to_int

    fun xlate_other_opr32 s =
      if String.size s = 10 andalso String.isPrefix "0x" s then xlate_hex_opr32 s
      else xlate_opr_fp32 s


    fun xlate_opr "Q" = qNaN32
      | xlate_opr "S" = sNaN32
      | xlate_opr "+Zero" = plus_zero32
      | xlate_opr "-Zero" = minus_zero32
      | xlate_opr "+Inf" = plus_inf32
      | xlate_opr "-Inf" = minus_inf32
      | xlate_opr s = xlate_other_opr32 s


    fun xlate_rm "0" = Float_To_zero
      | xlate_rm "=0" = To_nearest
      | xlate_rm ">" = To_pinfinity
      | xlate_rm "<" = To_ninfinity
      | xlate_rm x = error ("xlate_rm: " ^ x)


    fun check_vector_aux v = let
      val tks = String.tokens (Char.isSpace) v
      val (ty::f::rm::args) = tks

      val _ = ty="b32" orelse error("Unsupported ty: " ^ ty)

      val rm = xlate_rm rm
      val args = map xlate_opr args

    in
      case (f,args) of
        ("+",[a,b,c]) => check_fadd32 rm a b c
      | ("-",[a,b,c]) => check_fsub32 rm a b c
      | ("*",[a,b,c]) => check_fmul32 rm a b c
      | ("/",[a,b,c]) => check_fdiv32 rm a b c
      | ("V",[a,b]) => check_fsqrt32 rm a b
      | ("*+",[a,b,c,d]) => check_fmul_add32 rm a b c d
      | (_,_) => error("Unsupported op: " ^ f)
    end


    val failed = ref false;

    fun check_vector v = let

      fun fail () = (
        failed:=true;
        print ("FAIL: " ^ v)
      )

      val _ = (if check_vector_aux v then () else fail())

    in () end

    fun do_exit () =
      OS.Process.exit(if !failed then OS.Process.failure else OS.Process.success)


  end

  fun check_stdin () = case TextIO.inputLine TextIO.stdIn of
    NONE => ()
  | SOME s => (check_vector s; check_stdin ())


  val _ = case CommandLine.arguments() of
    [] => (check_stdin (); do_exit ())
  | xs => (map check_vector (map (fn s => s ^ "\n") xs); do_exit ())


end
