(* Test that words can handle numbers between 0 and 31 *)
val _ = if 5 <= Word.wordSize then () else raise (Fail ("wordSize less than 5"));

structure Uint32 : sig
  val set_bit : Word32.word -> IntInf.int -> bool -> Word32.word
  val shiftl : Word32.word -> IntInf.int -> Word32.word
  val shiftr : Word32.word -> IntInf.int -> Word32.word
  val shiftr_signed : Word32.word -> IntInf.int -> Word32.word
  val test_bit : Word32.word -> IntInf.int -> bool
end = struct

fun set_bit x n b =
  let val mask = Word32.<< (0wx1, Word.fromLargeInt (IntInf.toLarge n))
  in if b then Word32.orb (x, mask)
     else Word32.andb (x, Word32.notb mask)
  end

fun shiftl x n =
  Word32.<< (x, Word.fromLargeInt (IntInf.toLarge n))

fun shiftr x n =
  Word32.>> (x, Word.fromLargeInt (IntInf.toLarge n))

fun shiftr_signed x n =
  Word32.~>> (x, Word.fromLargeInt (IntInf.toLarge n))

fun test_bit x n =
  Word32.andb (x, Word32.<< (0wx1, Word.fromLargeInt (IntInf.toLarge n))) <> Word32.fromInt 0

end; (* struct Uint32 *)

(* Test that words can handle numbers between 0 and 63 *)
val _ = if 6 <= Word.wordSize then () else raise (Fail ("wordSize less than 6"));

structure Uint64 : sig
  eqtype uint64;
  val zero : uint64;
  val one : uint64;
  val fromInt : IntInf.int -> uint64;
  val toInt : uint64 -> IntInf.int;
  val toLarge : uint64 -> LargeWord.word;
  val fromLarge : LargeWord.word -> uint64
  val plus : uint64 -> uint64 -> uint64;
  val minus : uint64 -> uint64 -> uint64;
  val times : uint64 -> uint64 -> uint64;
  val divide : uint64 -> uint64 -> uint64;
  val modulus : uint64 -> uint64 -> uint64;
  val negate : uint64 -> uint64;
  val less_eq : uint64 -> uint64 -> bool;
  val less : uint64 -> uint64 -> bool;
  val notb : uint64 -> uint64;
  val andb : uint64 -> uint64 -> uint64;
  val orb : uint64 -> uint64 -> uint64;
  val xorb : uint64 -> uint64 -> uint64;
  val shiftl : uint64 -> IntInf.int -> uint64;
  val shiftr : uint64 -> IntInf.int -> uint64;
  val shiftr_signed : uint64 -> IntInf.int -> uint64;
  val set_bit : uint64 -> IntInf.int -> bool -> uint64;
  val test_bit : uint64 -> IntInf.int -> bool;
end = struct

type uint64 = IntInf.int;

val mask = 0xFFFFFFFFFFFFFFFF : IntInf.int;

val zero = 0 : IntInf.int;

val one = 1 : IntInf.int;

fun fromInt x = IntInf.andb(x, mask);

fun toInt x = x

fun toLarge x = LargeWord.fromLargeInt (IntInf.toLarge x);

fun fromLarge x = IntInf.fromLarge (LargeWord.toLargeInt x);

fun plus x y = IntInf.andb(IntInf.+(x, y), mask);

fun minus x y = IntInf.andb(IntInf.-(x, y), mask);

fun negate x = IntInf.andb(IntInf.~(x), mask);

fun times x y = IntInf.andb(IntInf.*(x, y), mask);

fun divide x y = IntInf.div(x, y);

fun modulus x y = IntInf.mod(x, y);

fun less_eq x y = IntInf.<=(x, y);

fun less x y = IntInf.<(x, y);

fun notb x = IntInf.andb(IntInf.notb(x), mask);

fun orb x y = IntInf.orb(x, y);

fun andb x y = IntInf.andb(x, y);

fun xorb x y = IntInf.xorb(x, y);

val maxWord = IntInf.pow (2, Word.wordSize);

fun shiftl x n = 
  if n < maxWord then IntInf.andb(IntInf.<< (x, Word.fromLargeInt (IntInf.toLarge n)), mask)
  else 0;

fun shiftr x n =
  if n < maxWord then IntInf.~>> (x, Word.fromLargeInt (IntInf.toLarge n))
  else 0;

val msb_mask = 0x8000000000000000 : IntInf.int;

fun shiftr_signed x i =
  if IntInf.andb(x, msb_mask) = 0 then shiftr x i
  else if i >= 64 then 0xFFFFFFFFFFFFFFFF
  else let
    val x' = shiftr x i
    val m' = IntInf.andb(IntInf.<<(mask, Word.max(0w64 - Word.fromLargeInt (IntInf.toLarge i), 0w0)), mask)
  in IntInf.orb(x', m') end;

fun test_bit x n =
  if n < maxWord then IntInf.andb (x, IntInf.<< (1, Word.fromLargeInt (IntInf.toLarge n))) <> 0
  else false;

fun set_bit x n b =
  if n < 64 then
    if b then IntInf.orb (x, IntInf.<< (1, Word.fromLargeInt (IntInf.toLarge n)))
    else IntInf.andb (x, IntInf.notb (IntInf.<< (1, Word.fromLargeInt (IntInf.toLarge n))))
  else x;

end



   fun array_blit src si dst di len = (
      src=dst andalso raise Fail ("array_blit: Same arrays");
      ArraySlice.copy {
        di = IntInf.toInt di,
        src = ArraySlice.slice (src,IntInf.toInt si,SOME (IntInf.toInt len)),
        dst = dst})

    fun array_nth_oo v a i () = Array.sub(a,IntInf.toInt i) handle Subscript => v | Overflow => v
    fun array_upd_oo f i x a () = 
      (Array.update(a,IntInf.toInt i,x); a) handle Subscript => f () | Overflow => f ()

    

structure Bits_Integer : sig
  val set_bit : IntInf.int -> IntInf.int -> bool -> IntInf.int
  val shiftl : IntInf.int -> IntInf.int -> IntInf.int
  val shiftr : IntInf.int -> IntInf.int -> IntInf.int
  val test_bit : IntInf.int -> IntInf.int -> bool
end = struct

val maxWord = IntInf.pow (2, Word.wordSize);

fun set_bit x n b =
  if n < maxWord then
    if b then IntInf.orb (x, IntInf.<< (1, Word.fromLargeInt (IntInf.toLarge n)))
    else IntInf.andb (x, IntInf.notb (IntInf.<< (1, Word.fromLargeInt (IntInf.toLarge n))))
  else raise (Fail ("Bit index too large: " ^ IntInf.toString n));

fun shiftl x n =
  if n < maxWord then IntInf.<< (x, Word.fromLargeInt (IntInf.toLarge n))
  else raise (Fail ("Shift operand too large: " ^ IntInf.toString n));

fun shiftr x n =
  if n < maxWord then IntInf.~>> (x, Word.fromLargeInt (IntInf.toLarge n))
  else raise (Fail ("Shift operand too large: " ^ IntInf.toString n));

fun test_bit x n =
  if n < maxWord then IntInf.andb (x, IntInf.<< (1, Word.fromLargeInt (IntInf.toLarge n))) <> 0
  else raise (Fail ("Bit index too large: " ^ IntInf.toString n));

end; (*struct Bits_Integer*)

structure BS : sig
  datatype int = Int_of_integer of IntInf.int
  type nat
  type num
  val nat_of_integer : IntInf.int -> nat
  val integer_of_nat : nat -> IntInf.int
  val integer_of_int : int -> IntInf.int
  val bin_search_impl : int array -> int -> (unit -> nat)
  val bin_search_impla : Uint64.uint64 array -> Uint64.uint64 -> (unit -> nat)
end = struct

datatype typerepa = Typerep of string * typerepa list;

datatype int = Int_of_integer of IntInf.int;

datatype 'a itself = Type;

fun typerep_inta t = Typerep ("Int.int", []);

type 'a typerep = {typerep : 'a itself -> typerepa};
val typerep = #typerep : 'a typerep -> 'a itself -> typerepa;

type 'a countable = {};

type 'a heap = {countable_heap : 'a countable, typerep_heap : 'a typerep};
val countable_heap = #countable_heap : 'a heap -> 'a countable;
val typerep_heap = #typerep_heap : 'a heap -> 'a typerep;

val countable_int = {} : int countable;

val typerep_int = {typerep = typerep_inta} : int typerep;

val heap_int = {countable_heap = countable_int, typerep_heap = typerep_int} :
  int heap;

fun typerep_uint64a t = Typerep ("Uint64.uint64", []);

val countable_uint64 = {} : Uint64.uint64 countable;

val typerep_uint64 = {typerep = typerep_uint64a} : Uint64.uint64 typerep;

val heap_uint64 =
  {countable_heap = countable_uint64, typerep_heap = typerep_uint64} :
  Uint64.uint64 heap;

type 'a ord = {less_eq : 'a -> 'a -> bool, less : 'a -> 'a -> bool};
val less_eq = #less_eq : 'a ord -> 'a -> 'a -> bool;
val less = #less : 'a ord -> 'a -> 'a -> bool;

val ord_integer =
  {less_eq = (fn a => fn b => IntInf.<= (a, b)),
    less = (fn a => fn b => IntInf.< (a, b))}
  : IntInf.int ord;

datatype nat = Nat of IntInf.int;

datatype num = One | Bit0 of num | Bit1 of num;

fun max A_ a b = (if less_eq A_ a b then b else a);

fun nat_of_integer k = Nat (max ord_integer (0 : IntInf.int) k);

fun len A_ a =
  (fn f_ => fn () => f_ (((fn () => IntInf.fromInt (Array.length a))) ()) ())
    (fn i => (fn () => (nat_of_integer i)));

fun integer_of_nat (Nat x) = x;

fun nth A_ a n = (fn () => Array.sub (a, IntInf.toInt (integer_of_nat n)));

fun apsnd f (x, y) = (x, f y);

fun fst (x1, x2) = x1;

val one_nat : nat = Nat (1 : IntInf.int);

fun integer_of_int (Int_of_integer k) = k;

fun less_int k l = IntInf.< (integer_of_int k, integer_of_int l);

fun less_nat m n = IntInf.< (integer_of_nat m, integer_of_nat n);

fun sgn_integer k =
  (if ((k : IntInf.int) = (0 : IntInf.int)) then (0 : IntInf.int)
    else (if IntInf.< (k, (0 : IntInf.int)) then (~1 : IntInf.int)
           else (1 : IntInf.int)));

fun divmod_integer k l =
  (if ((k : IntInf.int) = (0 : IntInf.int))
    then ((0 : IntInf.int), (0 : IntInf.int))
    else (if ((l : IntInf.int) = (0 : IntInf.int)) then ((0 : IntInf.int), k)
           else (apsnd o (fn a => fn b => IntInf.* (a, b)) o sgn_integer) l
                  (if (((sgn_integer k) : IntInf.int) = (sgn_integer l))
                    then IntInf.divMod (IntInf.abs k, IntInf.abs l)
                    else let
                           val (r, s) =
                             IntInf.divMod (IntInf.abs k, IntInf.abs l);
                         in
                           (if ((s : IntInf.int) = (0 : IntInf.int))
                             then (IntInf.~ r, (0 : IntInf.int))
                             else (IntInf.- (IntInf.~ r, (1 : IntInf.int)),
                                    IntInf.- (IntInf.abs l, s)))
                         end)));

fun divide_integer k l = fst (divmod_integer k l);

fun divide_nat m n = Nat (divide_integer (integer_of_nat m) (integer_of_nat n));

fun heap_WHILET b f s =
  (fn f_ => fn () => f_ ((b s) ()) ())
    (fn bv =>
      (if bv then (fn f_ => fn () => f_ ((f s) ()) ()) (heap_WHILET b f)
        else (fn () => s)));

fun minus_nat m n =
  Nat (max ord_integer (0 : IntInf.int)
        (IntInf.- (integer_of_nat m, integer_of_nat n)));

val zero_nat : nat = Nat (0 : IntInf.int);

fun plus_nat m n = Nat (IntInf.+ (integer_of_nat m, integer_of_nat n));

fun bin_search_impl x =
  (fn ai => fn bi =>
    (fn f_ => fn () => f_ ((len heap_int ai) ()) ())
      (fn xa =>
        (fn f_ => fn () => f_
          ((heap_WHILET (fn (a, b) => (fn () => (less_nat a b)))
             (fn (a1, a2) =>
               let
                 val x_a =
                   plus_nat a1
                     (divide_nat (minus_nat a2 a1)
                       (nat_of_integer (2 : IntInf.int)));
               in
                 (fn f_ => fn () => f_ ((nth heap_int ai x_a) ()) ())
                   (fn xb =>
                     (fn () =>
                       (if less_int xb bi then (plus_nat x_a one_nat, a2)
                         else (a1, x_a))))
               end)
             (zero_nat, xa))
          ()) ())
          (fn (a1, _) => (fn () => a1))))
    x;

fun bin_search_impla x =
  (fn ai => fn bi =>
    (fn f_ => fn () => f_ ((len heap_uint64 ai) ()) ())
      (fn xa =>
        (fn f_ => fn () => f_
          ((heap_WHILET (fn (a, b) => (fn () => (less_nat a b)))
             (fn (a1, a2) =>
               let
                 val x_a =
                   plus_nat a1
                     (divide_nat (minus_nat a2 a1)
                       (nat_of_integer (2 : IntInf.int)));
               in
                 (fn f_ => fn () => f_ ((nth heap_uint64 ai x_a) ()) ())
                   (fn xb =>
                     (fn () =>
                       (if Uint64.less xb bi then (plus_nat x_a one_nat, a2)
                         else (a1, x_a))))
               end)
             (zero_nat, xa))
          ()) ())
          (fn (a1, _) => (fn () => a1))))
    x;

end; (*struct BS*)
