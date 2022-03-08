structure FP_test_parser = struct


  exception Error of string

  fun error msg = (
    raise Error msg
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


    fun xlate_opr "Q" = qNaN32
      | xlate_opr "S" = sNaN32
      | xlate_opr "+Zero" = plus_zero32
      | xlate_opr "-Zero" = minus_zero32
      | xlate_opr "+Inf" = plus_inf32
      | xlate_opr "-Inf" = minus_inf32
      | xlate_opr s = xlate_opr_fp32 s


    fun xlate_rm "0" = Float_To_zero
      | xlate_rm "=0" = To_nearest
      | xlate_rm ">" = To_pinfinity
      | xlate_rm "<" = To_ninfinity
      | xlate_rm x = error ("xlate_rm: " ^ x)


    fun check_vector_aux v = let
      val tks = String.tokens (fn x => x = #" ") v
      val (f::rm::args) = tks

      val rm = xlate_rm rm
      val args = map xlate_opr args

    in
      case (f,args) of
        ("b32+",[a,b,c]) => check_fadd32 rm a b c
      | ("b32-",[a,b,c]) => check_fsub32 rm a b c
      | ("b32*",[a,b,c]) => check_fmul32 rm a b c
      | ("b32/",[a,b,c]) => check_fdiv32 rm a b c
      | ("b32*+",[a,b,c,d]) => check_fmul_add32 rm a b c d
      | (_,_) => error ("Unknown fun or arg type")
    end


    fun check_vector v = let
      val _ = print (v ^ ": ")
      val res = (if check_vector_aux v then print "OK" else print "FAIL")
        handle Error msg => print ("ERROR: " ^ msg)

      val _ = print "\n"

    in () end


  end

  val _ = map check_vector (CommandLine.arguments())


end
