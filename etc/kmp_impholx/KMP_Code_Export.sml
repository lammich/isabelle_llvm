(* Test that words can handle numbers between 0 and 3 *)
val _ = if 3 <= Word.wordSize then () else raise (Fail ("wordSize less than 3"));

structure Uint8 : sig
  val set_bit : Word8.word -> Int.int -> bool -> Word8.word
  val shiftl : Word8.word -> Int.int -> Word8.word
  val shiftr : Word8.word -> Int.int -> Word8.word
  val shiftr_signed : Word8.word -> Int.int -> Word8.word
  val test_bit : Word8.word -> Int.int -> bool
end = struct

fun set_bit x n b =
  let val mask = Word8.<< (0wx1, Word.fromLargeInt (Int.toLarge n))
  in if b then Word8.orb (x, mask)
     else Word8.andb (x, Word8.notb mask)
  end

fun shiftl x n =
  Word8.<< (x, Word.fromLargeInt (Int.toLarge n))

fun shiftr x n =
  Word8.>> (x, Word.fromLargeInt (Int.toLarge n))

fun shiftr_signed x n =
  Word8.~>> (x, Word.fromLargeInt (Int.toLarge n))

fun test_bit x n =
  Word8.andb (x, Word8.<< (0wx1, Word.fromLargeInt (Int.toLarge n))) <> Word8.fromInt 0

end; (* struct Uint8 *)

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


structure KMP : sig
  type nat
  val nat_of_integer : Int.int -> nat
  val integer_of_nat : nat -> Int.int
  val kmp_char8_impl :
    Word8.word array * nat -> Word8.word array * nat -> (unit -> (nat option))
end = struct

datatype typerepa = Typerep of string * typerepa list;

datatype nat = Nat of Int.int;

datatype 'a itself = Type;

fun typerep_nata t = Typerep ("Nat.nat", []);

type 'a typerep = {typerep : 'a itself -> typerepa};
val typerep = #typerep : 'a typerep -> 'a itself -> typerepa;

type 'a countable = {};

type 'a heap = {countable_heap : 'a countable, typerep_heap : 'a typerep};
val countable_heap = #countable_heap : 'a heap -> 'a countable;
val typerep_heap = #typerep_heap : 'a heap -> 'a typerep;

val countable_nat = {} : nat countable;

val typerep_nat = {typerep = typerep_nata} : nat typerep;

val heap_nat = {countable_heap = countable_nat, typerep_heap = typerep_nat} :
  nat heap;

type 'a equal = {equal : 'a -> 'a -> bool};
val equal = #equal : 'a equal -> 'a -> 'a -> bool;

val equal_uint8 = {equal = (fn a => fn b => ((a : Word8.word) = b))} :
  Word8.word equal;

fun typerep_uint8a t = Typerep ("Uint8.uint8", []);

val countable_uint8 = {} : Word8.word countable;

val typerep_uint8 = {typerep = typerep_uint8a} : Word8.word typerep;

val heap_uint8 =
  {countable_heap = countable_uint8, typerep_heap = typerep_uint8} :
  Word8.word heap;

type 'a ord = {less_eq : 'a -> 'a -> bool, less : 'a -> 'a -> bool};
val less_eq = #less_eq : 'a ord -> 'a -> 'a -> bool;
val less = #less : 'a ord -> 'a -> 'a -> bool;

val ord_integer =
  {less_eq = (fn a => fn b => Int.<= (a, b)),
    less = (fn a => fn b => Int.< (a, b))}
  : Int.int ord;

datatype num = One | Bit0 of num | Bit1 of num;

fun eq A_ a b = equal A_ a b;

fun max A_ a b = (if less_eq A_ a b then b else a);

fun nat_of_integer k = Nat (max ord_integer (0 : Int.int) k);

fun len A_ a =
  (fn () => let
              val i = (fn () => Int.fromInt (Array.length a)) ();
            in
              nat_of_integer i
            end);

fun integer_of_nat (Nat x) = x;

fun new A_ =
  (fn a => fn b => (fn () => Array.array (Int.toInt a, b))) o integer_of_nat;

fun nth A_ a n = (fn () => Array.sub (a, Int.toInt (integer_of_nat n)));

fun upd A_ i x a =
  (fn () =>
    let
      val _ =
        (fn () => Array.update (a, Int.toInt (integer_of_nat i), x)) ();
    in
      a
    end);

fun heap_WHILET b f s =
  (fn () =>
    let
      val bv = b s ();
    in
      (if bv then (fn f_ => fn () => f_ ((f s) ()) ()) (heap_WHILET b f)
        else (fn () => s))
        ()
    end);

fun minus_nat m n =
  Nat (max ord_integer (0 : Int.int)
        (Int.- (integer_of_nat m, integer_of_nat n)));

val zero_nat : nat = Nat (0 : Int.int);

fun plus_nat m n = Nat (Int.+ (integer_of_nat m, integer_of_nat n));

fun arl_length A_ = (fn (_, a) => (fn () => a));

fun less_nat m n = Int.< (integer_of_nat m, integer_of_nat n);

val one_nat : nat = Nat (1 : Int.int);

fun arl_get A_ = (fn (a, _) => nth A_ a);

fun compute_butlast_ff_s_impl (A1_, A2_) =
  (fn xi => fn () =>
    let
      val x = arl_length A2_ xi ();
      val xa = new heap_nat x zero_nat ();
      val a =
        heap_WHILET
          (fn (a1, (_, a2a)) =>
            (fn f_ => fn () => f_ ((len heap_nat a1) ()) ())
              (fn x_g => (fn () => (less_nat a2a x_g))))
          (fn (a1, (a1a, a2a)) =>
            (fn f_ => fn () => f_
              ((heap_WHILET
                 (fn sa =>
                   (fn f_ => fn () => f_
                     ((arl_get A2_ xi (minus_nat sa one_nat)) ()) ())
                     (fn xb =>
                       (fn f_ => fn () => f_
                         ((arl_get A2_ xi (minus_nat a2a one_nat)) ()) ())
                         (fn xaa =>
                           (fn () =>
                             (less_nat zero_nat sa andalso
                               not (eq A1_ xb xaa))))))
                 (fn sa => nth heap_nat a1 (minus_nat sa one_nat)) a1a)
              ()) ())
              (fn x_g =>
                let
                  val x_h = plus_nat x_g one_nat;
                in
                  (fn f_ => fn () => f_ ((upd heap_nat a2a x_h a1) ()) ())
                    (fn x_j => (fn () => (x_j, (x_h, plus_nat a2a one_nat))))
                end))
          (xa, (zero_nat, one_nat)) ();
    in
      let
        val (a1, (_, _)) = a;
      in
        (fn () => a1)
      end
        ()
    end);

fun less_eq_nat m n = Int.<= (integer_of_nat m, integer_of_nat n);

fun equal_nat m n = (((integer_of_nat m) : Int.int) = (integer_of_nat n));

fun arl_is_empty A_ = (fn (_, n) => (fn () => (equal_nat n zero_nat)));

fun is_None a = (case a of NONE => true | SOME _ => false);

fun kmp_impl (A1_, A2_) =
  (fn ai => fn bi => fn () =>
    let
      val x = arl_is_empty A2_ ai ();
    in
      (if x then (fn () => (SOME zero_nat))
        else (fn f_ => fn () => f_ ((compute_butlast_ff_s_impl (A1_, A2_) ai)
               ()) ())
               (fn x_g =>
                 (fn f_ => fn () => f_
                   ((heap_WHILET
                      (fn (a1, (_, a2a)) =>
                        (fn f_ => fn () => f_ ((arl_length A2_ ai) ()) ())
                          (fn xa =>
                            (fn f_ => fn () => f_ ((arl_length A2_ bi) ()) ())
                              (fn xaa =>
                                (fn () =>
                                  (less_eq_nat (plus_nat a1 xa) xaa andalso
                                    is_None a2a)))))
                      (fn (a1, (a1a, a2a)) =>
                        (fn f_ => fn () => f_
                          ((heap_WHILET
                             (fn (a1b, a2b) =>
                               (if is_None a2b
                                 then (fn f_ => fn () => f_
((arl_get A2_ bi (plus_nat a1 a1b)) ()) ())
(fn x_k =>
  (fn f_ => fn () => f_ ((arl_get A2_ ai a1b) ()) ())
    (fn x_l => (fn () => (eq A1_ x_k x_l))))
                                 else (fn () => false)))
                             (fn (a1b, _) =>
                               let
                                 val x_j = plus_nat a1b one_nat;
                               in
                                 (fn f_ => fn () => f_ ((arl_length A2_ ai) ())
                                   ())
                                   (fn xa =>
                                     (fn () =>
                                       (if equal_nat x_j xa then (x_j, SOME a1)
 else (x_j, NONE))))
                               end)
                             (a1a, a2a))
                          ()) ())
                          (fn (a1b, a2b) =>
                            (if is_None a2b
                              then (fn f_ => fn () => f_ ((nth heap_nat x_g a1b)
                                     ()) ())
                                     (fn xa =>
                                       (fn f_ => fn () => f_
 ((nth heap_nat x_g a1b) ()) ())
 (fn xaa =>
   (fn () =>
     (plus_nat a1 (plus_nat (minus_nat a1b xa) one_nat),
       (minus_nat xaa one_nat, NONE)))))
                              else (fn () => (a1, (a1b, SOME a1))))))
                      (zero_nat, (zero_nat, NONE)))
                   ()) ())
                   (fn (_, a) => let
                                   val (_, aa) = a;
                                 in
                                   (fn () => aa)
                                 end)))
        ()
    end);

fun kmp_char8_impl x = kmp_impl (equal_uint8, heap_uint8) x;

end; (*struct KMP*)
