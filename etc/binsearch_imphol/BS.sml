fun map_option _ NONE = NONE
  | map_option f (SOME x) = SOME (f x)

val nat_of_integer = BS.nat_of_integer o IntInf.fromInt
val integer_of_nat = IntInf.toInt o BS.integer_of_nat
val int_of_integer = BS.Int_of_integer o IntInf.fromInt
val integer_of_int = IntInf.toInt o BS.integer_of_int

fun println x = print (x ^ "\n")

fun bin_search xs x = integer_of_nat (BS.bin_search_impl xs (int_of_integer x) ())
fun bin_search xs x = integer_of_nat (BS.bin_search_impl xs (int_of_integer x) ())

fun the (SOME x) = x

fun main () = let
  val [len] = CommandLine.arguments ()

  val len = the (Int.fromString len)
  
  val xs = Array.tabulate (len, fn x => int_of_integer (x*5))

  fun iter acc x = if x<5*len then iter (acc + bin_search xs x) (x+2) else acc

  val start = Time.now ()
  val sum = iter 0 0
  val duration = Time.toMilliseconds (Time.- (Time.now(), start))
  
  val _ = println ("Time (ms): " ^ IntInf.toString duration)
  val _ = println ("checksum " ^ Int.toString sum)
  
  val _ = println ("@ SML " ^ Int.toString len ^ " " ^ IntInf.toString duration)
in
  ()
end


val _ = if MLton.isMLton then main() else ()
