(* Manually replaced IntInf by Int. Possibly unsound! *)
(* Test that words can handle numbers between 0 and 31 *)
val _ = if 5 <= Word.wordSize then () else raise (Fail ("wordSize less than 5"));

structure Uint32 : sig
  val set_bit : Word32.word -> Int.int -> bool -> Word32.word
  val shiftl : Word32.word -> Int.int -> Word32.word
  val shiftr : Word32.word -> Int.int -> Word32.word
  val shiftr_signed : Word32.word -> Int.int -> Word32.word
  val test_bit : Word32.word -> Int.int -> bool
end = struct

fun set_bit x n b =
  let val mask = Word32.<< (0wx1, Word.fromLargeInt (Int.toLarge n))
  in if b then Word32.orb (x, mask)
     else Word32.andb (x, Word32.notb mask)
  end

fun shiftl x n =
  Word32.<< (x, Word.fromLargeInt (Int.toLarge n))

fun shiftr x n =
  Word32.>> (x, Word.fromLargeInt (Int.toLarge n))

fun shiftr_signed x n =
  Word32.~>> (x, Word.fromLargeInt (Int.toLarge n))

fun test_bit x n =
  Word32.andb (x, Word32.<< (0wx1, Word.fromLargeInt (Int.toLarge n))) <> Word32.fromInt 0

end; (* struct Uint32 *)


   fun array_blit src si dst di len = (
      src=dst andalso raise Fail ("array_blit: Same arrays");
      ArraySlice.copy {
        di = Int.toInt di,
        src = ArraySlice.slice (src,Int.toInt si,SOME (Int.toInt len)),
        dst = dst})

    fun array_nth_oo v a i () = Array.sub(a,Int.toInt i) handle Subscript => v | Overflow => v
    fun array_upd_oo f i x a () = 
      (Array.update(a,Int.toInt i,x); a) handle Subscript => f () | Overflow => f ()


structure BS : sig
  datatype int = Int_of_integer of Int.int
  type nat
  type num
  val nat_of_integer : Int.int -> nat
  val integer_of_nat : nat -> Int.int
  val integer_of_int : int -> Int.int
  val bin_search_impl : int array -> int -> (unit -> nat)
end = struct

datatype typerepa = Typerep of string * typerepa list;

datatype int = Int_of_integer of Int.int;

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

type 'a ord = {less_eq : 'a -> 'a -> bool, less : 'a -> 'a -> bool};
val less_eq = #less_eq : 'a ord -> 'a -> 'a -> bool;
val less = #less : 'a ord -> 'a -> 'a -> bool;

val ord_integer =
  {less_eq = (fn a => fn b => Int.<= (a, b)),
    less = (fn a => fn b => Int.< (a, b))}
  : Int.int ord;

datatype nat = Nat of Int.int;

datatype num = One | Bit0 of num | Bit1 of num;

fun max A_ a b = (if less_eq A_ a b then b else a);

fun nat_of_integer k = Nat (max ord_integer (0 : Int.int) k);

fun len A_ a =
  (fn f_ => fn () => f_ (((fn () => Int.fromInt (Array.length a))) ()) ())
    (fn i => (fn () => (nat_of_integer i)));

fun integer_of_nat (Nat x) = x;

fun nth A_ a n = (fn () => Array.sub (a, Int.toInt (integer_of_nat n)));

fun apsnd f (x, y) = (x, f y);

fun fst (x1, x2) = x1;

val one_nat : nat = Nat (1 : Int.int);

fun integer_of_int (Int_of_integer k) = k;

fun less_int k l = Int.< (integer_of_int k, integer_of_int l);

fun less_nat m n = Int.< (integer_of_nat m, integer_of_nat n);

fun sgn_integer k =
  (if ((k : Int.int) = (0 : Int.int)) then (0 : Int.int)
    else (if Int.< (k, (0 : Int.int)) then (~1 : Int.int)
           else (1 : Int.int)));


fun divide_integer k l = Int.div (k,l);

fun divide_nat m n = Nat (divide_integer (integer_of_nat m) (integer_of_nat n));

fun heap_WHILET b f s =
  (fn f_ => fn () => f_ ((b s) ()) ())
    (fn bv =>
      (if bv then (fn f_ => fn () => f_ ((f s) ()) ()) (heap_WHILET b f)
        else (fn () => s)));

fun minus_nat m n =
  Nat (max ord_integer (0 : Int.int)
        (Int.- (integer_of_nat m, integer_of_nat n)));

val zero_nat : nat = Nat (0 : Int.int);

fun plus_nat m n = Nat (Int.+ (integer_of_nat m, integer_of_nat n));

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
                       (nat_of_integer (2 : Int.int)));
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

end; (*struct BS*)
