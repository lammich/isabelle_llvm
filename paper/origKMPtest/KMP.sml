fun map_option _ NONE = NONE
  | map_option f (SOME x) = SOME (f x)

val nat_of_integer = KMP.nat_of_integer o IntInf.fromInt

val integer_of_nat = IntInf.toInt o KMP.integer_of_nat

fun println x = print (x ^ "\n")

val string_to_word8array = Array.fromList o map (Word8.fromInt o Char.ord) o String.explode 

fun string_to_arl s = (string_to_word8array s, nat_of_integer (String.size s))

fun read_file name = let
  fun array vec = Array.tabulate (Word8Vector.length vec, fn i => Word8Vector.sub (vec, i))
  val f = BinIO.openIn name;
  val r = array (BinIO.inputAll f)
  val _ = BinIO.closeIn f
in (r,nat_of_integer (Array.length r)) end

fun kmp s t =  map_option integer_of_nat (KMP.kmp_char8_impl s t ())

fun iterate 0 _ _ = ()
  | iterate n f x = (f x; iterate (n-1) f x)


fun main () = let
  val [n,s,t] = CommandLine.arguments ();
  
  val n = case Int.fromString n of NONE => raise Match | SOME n => if n<1 then 1 else n
  val s = string_to_arl s
  val t = read_file t
  
  val start = Time.now ()
  
  val _ = iterate (n-1) (kmp s) t
  val res = kmp s t
  
  val duration = Time.toMilliseconds (Time.- (Time.now(), start))
  
  val _ = println ("Time without I/O (ms): " ^ IntInf.toString duration)
  
  val _ = println ("result (" ^ Int.toString n ^ " iterations) = " ^ (case res of NONE => "-1" | SOME res => Int.toString res))
  
in
  ()
end


val _ = if MLton.isMLton then main() else ()
