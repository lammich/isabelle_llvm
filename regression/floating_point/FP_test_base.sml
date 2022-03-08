structure FP_test_base : sig
  type 'a bit0
  type 'a bit1
  type num1
  type ('a, 'b) float
  datatype roundmode = To_nearest | Float_To_zero | To_pinfinity | To_ninfinity
  val fp32 :
    IntInf.int ->
      IntInf.int ->
        IntInf.int -> (num1 bit0 bit0 bit0, num1 bit0 bit1 bit1 bit1) float
  val fp64 :
    IntInf.int ->
      IntInf.int ->
        IntInf.int -> (num1 bit0 bit1 bit1, num1 bit1 bit0 bit1 bit0 bit0) float
  val qNaN32 : (num1 bit0 bit0 bit0, num1 bit0 bit1 bit1 bit1) float
  val qNaN64 : (num1 bit0 bit1 bit1, num1 bit1 bit0 bit1 bit0 bit0) float
  val sNaN32 : (num1 bit0 bit0 bit0, num1 bit0 bit1 bit1 bit1) float
  val sNaN64 : (num1 bit0 bit1 bit1, num1 bit1 bit0 bit1 bit0 bit0) float
  val plus_inf32 : (num1 bit0 bit0 bit0, num1 bit0 bit1 bit1 bit1) float
  val plus_inf64 : (num1 bit0 bit1 bit1, num1 bit1 bit0 bit1 bit0 bit0) float
  val minus_inf32 : (num1 bit0 bit0 bit0, num1 bit0 bit1 bit1 bit1) float
  val minus_inf64 : (num1 bit0 bit1 bit1, num1 bit1 bit0 bit1 bit0 bit0) float
  val plus_zero32 : (num1 bit0 bit0 bit0, num1 bit0 bit1 bit1 bit1) float
  val plus_zero64 : (num1 bit0 bit1 bit1, num1 bit1 bit0 bit1 bit0 bit0) float
  val check_fadd32 :
    roundmode ->
      (num1 bit0 bit0 bit0, num1 bit0 bit1 bit1 bit1) float ->
        (num1 bit0 bit0 bit0, num1 bit0 bit1 bit1 bit1) float ->
          (num1 bit0 bit0 bit0, num1 bit0 bit1 bit1 bit1) float -> bool
  val check_fadd64 :
    roundmode ->
      (num1 bit0 bit1 bit1, num1 bit1 bit0 bit1 bit0 bit0) float ->
        (num1 bit0 bit1 bit1, num1 bit1 bit0 bit1 bit0 bit0) float ->
          (num1 bit0 bit1 bit1, num1 bit1 bit0 bit1 bit0 bit0) float -> bool
  val check_fdiv32 :
    roundmode ->
      (num1 bit0 bit0 bit0, num1 bit0 bit1 bit1 bit1) float ->
        (num1 bit0 bit0 bit0, num1 bit0 bit1 bit1 bit1) float ->
          (num1 bit0 bit0 bit0, num1 bit0 bit1 bit1 bit1) float -> bool
  val check_fdiv64 :
    roundmode ->
      (num1 bit0 bit1 bit1, num1 bit1 bit0 bit1 bit0 bit0) float ->
        (num1 bit0 bit1 bit1, num1 bit1 bit0 bit1 bit0 bit0) float ->
          (num1 bit0 bit1 bit1, num1 bit1 bit0 bit1 bit0 bit0) float -> bool
  val check_fmul32 :
    roundmode ->
      (num1 bit0 bit0 bit0, num1 bit0 bit1 bit1 bit1) float ->
        (num1 bit0 bit0 bit0, num1 bit0 bit1 bit1 bit1) float ->
          (num1 bit0 bit0 bit0, num1 bit0 bit1 bit1 bit1) float -> bool
  val check_fmul64 :
    roundmode ->
      (num1 bit0 bit1 bit1, num1 bit1 bit0 bit1 bit0 bit0) float ->
        (num1 bit0 bit1 bit1, num1 bit1 bit0 bit1 bit0 bit0) float ->
          (num1 bit0 bit1 bit1, num1 bit1 bit0 bit1 bit0 bit0) float -> bool
  val check_fsub32 :
    roundmode ->
      (num1 bit0 bit0 bit0, num1 bit0 bit1 bit1 bit1) float ->
        (num1 bit0 bit0 bit0, num1 bit0 bit1 bit1 bit1) float ->
          (num1 bit0 bit0 bit0, num1 bit0 bit1 bit1 bit1) float -> bool
  val check_fsub64 :
    roundmode ->
      (num1 bit0 bit1 bit1, num1 bit1 bit0 bit1 bit0 bit0) float ->
        (num1 bit0 bit1 bit1, num1 bit1 bit0 bit1 bit0 bit0) float ->
          (num1 bit0 bit1 bit1, num1 bit1 bit0 bit1 bit0 bit0) float -> bool
  val minus_zero32 : (num1 bit0 bit0 bit0, num1 bit0 bit1 bit1 bit1) float
  val minus_zero64 : (num1 bit0 bit1 bit1, num1 bit1 bit0 bit1 bit0 bit0) float
  val check_fmul_add32 :
    roundmode ->
      (num1 bit0 bit0 bit0, num1 bit0 bit1 bit1 bit1) float ->
        (num1 bit0 bit0 bit0, num1 bit0 bit1 bit1 bit1) float ->
          (num1 bit0 bit0 bit0, num1 bit0 bit1 bit1 bit1) float ->
            (num1 bit0 bit0 bit0, num1 bit0 bit1 bit1 bit1) float -> bool
  val check_fmul_add64 :
    roundmode ->
      (num1 bit0 bit1 bit1, num1 bit1 bit0 bit1 bit0 bit0) float ->
        (num1 bit0 bit1 bit1, num1 bit1 bit0 bit1 bit0 bit0) float ->
          (num1 bit0 bit1 bit1, num1 bit1 bit0 bit1 bit0 bit0) float ->
            (num1 bit0 bit1 bit1, num1 bit1 bit0 bit1 bit0 bit0) float -> bool
end = struct

datatype int = Int_of_integer of IntInf.int;

fun integer_of_int (Int_of_integer k) = k;

fun equal_inta k l = (((integer_of_int k) : IntInf.int) = (integer_of_int l));

type 'a equal = {equal : 'a -> 'a -> bool};
val equal = #equal : 'a equal -> 'a -> 'a -> bool;

val equal_int = {equal = equal_inta} : int equal;

datatype num = One | Bit0 of num | Bit1 of num;

val one_inta : int = Int_of_integer (1 : IntInf.int);

type 'a one = {one : 'a};
val one = #one : 'a one -> 'a;

val one_int = {one = one_inta} : int one;

fun times_inta k l =
  Int_of_integer (IntInf.* (integer_of_int k, integer_of_int l));

type 'a times = {times : 'a -> 'a -> 'a};
val times = #times : 'a times -> 'a -> 'a -> 'a;

type 'a power = {one_power : 'a one, times_power : 'a times};
val one_power = #one_power : 'a power -> 'a one;
val times_power = #times_power : 'a power -> 'a times;

val times_int = {times = times_inta} : int times;

val power_int = {one_power = one_int, times_power = times_int} : int power;

datatype nat = Nat of IntInf.int;

fun integer_of_nat (Nat x) = x;

fun equal_nata m n = (((integer_of_nat m) : IntInf.int) = (integer_of_nat n));

val equal_nat = {equal = equal_nata} : nat equal;

fun times_nata m n = Nat (IntInf.* (integer_of_nat m, integer_of_nat n));

type 'a dvd = {times_dvd : 'a times};
val times_dvd = #times_dvd : 'a dvd -> 'a times;

val times_nat = {times = times_nata} : nat times;

val dvd_nat = {times_dvd = times_nat} : nat dvd;

val one_nata : nat = Nat (1 : IntInf.int);

val one_nat = {one = one_nata} : nat one;

fun plus_nata m n = Nat (IntInf.+ (integer_of_nat m, integer_of_nat n));

type 'a plus = {plus : 'a -> 'a -> 'a};
val plus = #plus : 'a plus -> 'a -> 'a -> 'a;

val plus_nat = {plus = plus_nata} : nat plus;

val zero_nata : nat = Nat (0 : IntInf.int);

type 'a zero = {zero : 'a};
val zero = #zero : 'a zero -> 'a;

val zero_nat = {zero = zero_nata} : nat zero;

type 'a semigroup_add = {plus_semigroup_add : 'a plus};
val plus_semigroup_add = #plus_semigroup_add : 'a semigroup_add -> 'a plus;

type 'a numeral =
  {one_numeral : 'a one, semigroup_add_numeral : 'a semigroup_add};
val one_numeral = #one_numeral : 'a numeral -> 'a one;
val semigroup_add_numeral = #semigroup_add_numeral :
  'a numeral -> 'a semigroup_add;

val semigroup_add_nat = {plus_semigroup_add = plus_nat} : nat semigroup_add;

val numeral_nat =
  {one_numeral = one_nat, semigroup_add_numeral = semigroup_add_nat} :
  nat numeral;

val power_nat = {one_power = one_nat, times_power = times_nat} : nat power;

type 'a ord = {less_eq : 'a -> 'a -> bool, less : 'a -> 'a -> bool};
val less_eq = #less_eq : 'a ord -> 'a -> 'a -> bool;
val less = #less : 'a ord -> 'a -> 'a -> bool;

fun max A_ a b = (if less_eq A_ a b then b else a);

val ord_integer =
  {less_eq = (fn a => fn b => IntInf.<= (a, b)),
    less = (fn a => fn b => IntInf.< (a, b))}
  : IntInf.int ord;

fun minus_nata m n =
  Nat (max ord_integer (0 : IntInf.int)
        (IntInf.- (integer_of_nat m, integer_of_nat n)));

type 'a minus = {minus : 'a -> 'a -> 'a};
val minus = #minus : 'a minus -> 'a -> 'a -> 'a;

val minus_nat = {minus = minus_nata} : nat minus;

fun apsnd f (x, y) = (x, f y);

fun divmod_integer k l =
  (if ((k : IntInf.int) = (0 : IntInf.int))
    then ((0 : IntInf.int), (0 : IntInf.int))
    else (if IntInf.< ((0 : IntInf.int), l)
           then (if IntInf.< ((0 : IntInf.int), k)
                  then IntInf.divMod (IntInf.abs k, IntInf.abs l)
                  else let
                         val (r, s) =
                           IntInf.divMod (IntInf.abs k, IntInf.abs l);
                       in
                         (if ((s : IntInf.int) = (0 : IntInf.int))
                           then (IntInf.~ r, (0 : IntInf.int))
                           else (IntInf.- (IntInf.~ r, (1 : IntInf.int)),
                                  IntInf.- (l, s)))
                       end)
           else (if ((l : IntInf.int) = (0 : IntInf.int))
                  then ((0 : IntInf.int), k)
                  else apsnd IntInf.~
                         (if IntInf.< (k, (0 : IntInf.int))
                           then IntInf.divMod (IntInf.abs k, IntInf.abs l)
                           else let
                                  val (r, s) =
                                    IntInf.divMod (IntInf.abs k, IntInf.abs l);
                                in
                                  (if ((s : IntInf.int) = (0 : IntInf.int))
                                    then (IntInf.~ r, (0 : IntInf.int))
                                    else (IntInf.- (IntInf.~
              r, (1 : IntInf.int)),
   IntInf.- (IntInf.~ l, s)))
                                end))));

fun fst (x1, x2) = x1;

fun divide_integer k l = fst (divmod_integer k l);

fun divide_nata m n =
  Nat (divide_integer (integer_of_nat m) (integer_of_nat n));

type 'a divide = {divide : 'a -> 'a -> 'a};
val divide = #divide : 'a divide -> 'a -> 'a -> 'a;

val divide_nat = {divide = divide_nata} : nat divide;

fun snd (x1, x2) = x2;

fun modulo_integer k l = snd (divmod_integer k l);

fun modulo_nata m n =
  Nat (modulo_integer (integer_of_nat m) (integer_of_nat n));

type 'a modulo =
  {divide_modulo : 'a divide, dvd_modulo : 'a dvd, modulo : 'a -> 'a -> 'a};
val divide_modulo = #divide_modulo : 'a modulo -> 'a divide;
val dvd_modulo = #dvd_modulo : 'a modulo -> 'a dvd;
val modulo = #modulo : 'a modulo -> 'a -> 'a -> 'a;

val modulo_nat =
  {divide_modulo = divide_nat, dvd_modulo = dvd_nat, modulo = modulo_nata} :
  nat modulo;

type 'a ab_semigroup_add = {semigroup_add_ab_semigroup_add : 'a semigroup_add};
val semigroup_add_ab_semigroup_add = #semigroup_add_ab_semigroup_add :
  'a ab_semigroup_add -> 'a semigroup_add;

type 'a monoid_add =
  {semigroup_add_monoid_add : 'a semigroup_add, zero_monoid_add : 'a zero};
val semigroup_add_monoid_add = #semigroup_add_monoid_add :
  'a monoid_add -> 'a semigroup_add;
val zero_monoid_add = #zero_monoid_add : 'a monoid_add -> 'a zero;

type 'a comm_monoid_add =
  {ab_semigroup_add_comm_monoid_add : 'a ab_semigroup_add,
    monoid_add_comm_monoid_add : 'a monoid_add};
val ab_semigroup_add_comm_monoid_add = #ab_semigroup_add_comm_monoid_add :
  'a comm_monoid_add -> 'a ab_semigroup_add;
val monoid_add_comm_monoid_add = #monoid_add_comm_monoid_add :
  'a comm_monoid_add -> 'a monoid_add;

type 'a mult_zero = {times_mult_zero : 'a times, zero_mult_zero : 'a zero};
val times_mult_zero = #times_mult_zero : 'a mult_zero -> 'a times;
val zero_mult_zero = #zero_mult_zero : 'a mult_zero -> 'a zero;

type 'a semigroup_mult = {times_semigroup_mult : 'a times};
val times_semigroup_mult = #times_semigroup_mult :
  'a semigroup_mult -> 'a times;

type 'a semiring =
  {ab_semigroup_add_semiring : 'a ab_semigroup_add,
    semigroup_mult_semiring : 'a semigroup_mult};
val ab_semigroup_add_semiring = #ab_semigroup_add_semiring :
  'a semiring -> 'a ab_semigroup_add;
val semigroup_mult_semiring = #semigroup_mult_semiring :
  'a semiring -> 'a semigroup_mult;

type 'a semiring_0 =
  {comm_monoid_add_semiring_0 : 'a comm_monoid_add,
    mult_zero_semiring_0 : 'a mult_zero, semiring_semiring_0 : 'a semiring};
val comm_monoid_add_semiring_0 = #comm_monoid_add_semiring_0 :
  'a semiring_0 -> 'a comm_monoid_add;
val mult_zero_semiring_0 = #mult_zero_semiring_0 :
  'a semiring_0 -> 'a mult_zero;
val semiring_semiring_0 = #semiring_semiring_0 : 'a semiring_0 -> 'a semiring;

type 'a semiring_no_zero_divisors =
  {semiring_0_semiring_no_zero_divisors : 'a semiring_0};
val semiring_0_semiring_no_zero_divisors = #semiring_0_semiring_no_zero_divisors
  : 'a semiring_no_zero_divisors -> 'a semiring_0;

type 'a monoid_mult =
  {semigroup_mult_monoid_mult : 'a semigroup_mult,
    power_monoid_mult : 'a power};
val semigroup_mult_monoid_mult = #semigroup_mult_monoid_mult :
  'a monoid_mult -> 'a semigroup_mult;
val power_monoid_mult = #power_monoid_mult : 'a monoid_mult -> 'a power;

type 'a semiring_numeral =
  {monoid_mult_semiring_numeral : 'a monoid_mult,
    numeral_semiring_numeral : 'a numeral,
    semiring_semiring_numeral : 'a semiring};
val monoid_mult_semiring_numeral = #monoid_mult_semiring_numeral :
  'a semiring_numeral -> 'a monoid_mult;
val numeral_semiring_numeral = #numeral_semiring_numeral :
  'a semiring_numeral -> 'a numeral;
val semiring_semiring_numeral = #semiring_semiring_numeral :
  'a semiring_numeral -> 'a semiring;

type 'a zero_neq_one = {one_zero_neq_one : 'a one, zero_zero_neq_one : 'a zero};
val one_zero_neq_one = #one_zero_neq_one : 'a zero_neq_one -> 'a one;
val zero_zero_neq_one = #zero_zero_neq_one : 'a zero_neq_one -> 'a zero;

type 'a semiring_1 =
  {semiring_numeral_semiring_1 : 'a semiring_numeral,
    semiring_0_semiring_1 : 'a semiring_0,
    zero_neq_one_semiring_1 : 'a zero_neq_one};
val semiring_numeral_semiring_1 = #semiring_numeral_semiring_1 :
  'a semiring_1 -> 'a semiring_numeral;
val semiring_0_semiring_1 = #semiring_0_semiring_1 :
  'a semiring_1 -> 'a semiring_0;
val zero_neq_one_semiring_1 = #zero_neq_one_semiring_1 :
  'a semiring_1 -> 'a zero_neq_one;

type 'a semiring_1_no_zero_divisors =
  {semiring_1_semiring_1_no_zero_divisors : 'a semiring_1,
    semiring_no_zero_divisors_semiring_1_no_zero_divisors :
      'a semiring_no_zero_divisors};
val semiring_1_semiring_1_no_zero_divisors =
  #semiring_1_semiring_1_no_zero_divisors :
  'a semiring_1_no_zero_divisors -> 'a semiring_1;
val semiring_no_zero_divisors_semiring_1_no_zero_divisors =
  #semiring_no_zero_divisors_semiring_1_no_zero_divisors :
  'a semiring_1_no_zero_divisors -> 'a semiring_no_zero_divisors;

type 'a cancel_semigroup_add =
  {semigroup_add_cancel_semigroup_add : 'a semigroup_add};
val semigroup_add_cancel_semigroup_add = #semigroup_add_cancel_semigroup_add :
  'a cancel_semigroup_add -> 'a semigroup_add;

type 'a cancel_ab_semigroup_add =
  {ab_semigroup_add_cancel_ab_semigroup_add : 'a ab_semigroup_add,
    cancel_semigroup_add_cancel_ab_semigroup_add : 'a cancel_semigroup_add,
    minus_cancel_ab_semigroup_add : 'a minus};
val ab_semigroup_add_cancel_ab_semigroup_add =
  #ab_semigroup_add_cancel_ab_semigroup_add :
  'a cancel_ab_semigroup_add -> 'a ab_semigroup_add;
val cancel_semigroup_add_cancel_ab_semigroup_add =
  #cancel_semigroup_add_cancel_ab_semigroup_add :
  'a cancel_ab_semigroup_add -> 'a cancel_semigroup_add;
val minus_cancel_ab_semigroup_add = #minus_cancel_ab_semigroup_add :
  'a cancel_ab_semigroup_add -> 'a minus;

type 'a cancel_comm_monoid_add =
  {cancel_ab_semigroup_add_cancel_comm_monoid_add : 'a cancel_ab_semigroup_add,
    comm_monoid_add_cancel_comm_monoid_add : 'a comm_monoid_add};
val cancel_ab_semigroup_add_cancel_comm_monoid_add =
  #cancel_ab_semigroup_add_cancel_comm_monoid_add :
  'a cancel_comm_monoid_add -> 'a cancel_ab_semigroup_add;
val comm_monoid_add_cancel_comm_monoid_add =
  #comm_monoid_add_cancel_comm_monoid_add :
  'a cancel_comm_monoid_add -> 'a comm_monoid_add;

type 'a semiring_0_cancel =
  {cancel_comm_monoid_add_semiring_0_cancel : 'a cancel_comm_monoid_add,
    semiring_0_semiring_0_cancel : 'a semiring_0};
val cancel_comm_monoid_add_semiring_0_cancel =
  #cancel_comm_monoid_add_semiring_0_cancel :
  'a semiring_0_cancel -> 'a cancel_comm_monoid_add;
val semiring_0_semiring_0_cancel = #semiring_0_semiring_0_cancel :
  'a semiring_0_cancel -> 'a semiring_0;

type 'a ab_semigroup_mult =
  {semigroup_mult_ab_semigroup_mult : 'a semigroup_mult};
val semigroup_mult_ab_semigroup_mult = #semigroup_mult_ab_semigroup_mult :
  'a ab_semigroup_mult -> 'a semigroup_mult;

type 'a comm_semiring =
  {ab_semigroup_mult_comm_semiring : 'a ab_semigroup_mult,
    semiring_comm_semiring : 'a semiring};
val ab_semigroup_mult_comm_semiring = #ab_semigroup_mult_comm_semiring :
  'a comm_semiring -> 'a ab_semigroup_mult;
val semiring_comm_semiring = #semiring_comm_semiring :
  'a comm_semiring -> 'a semiring;

type 'a comm_semiring_0 =
  {comm_semiring_comm_semiring_0 : 'a comm_semiring,
    semiring_0_comm_semiring_0 : 'a semiring_0};
val comm_semiring_comm_semiring_0 = #comm_semiring_comm_semiring_0 :
  'a comm_semiring_0 -> 'a comm_semiring;
val semiring_0_comm_semiring_0 = #semiring_0_comm_semiring_0 :
  'a comm_semiring_0 -> 'a semiring_0;

type 'a comm_semiring_0_cancel =
  {comm_semiring_0_comm_semiring_0_cancel : 'a comm_semiring_0,
    semiring_0_cancel_comm_semiring_0_cancel : 'a semiring_0_cancel};
val comm_semiring_0_comm_semiring_0_cancel =
  #comm_semiring_0_comm_semiring_0_cancel :
  'a comm_semiring_0_cancel -> 'a comm_semiring_0;
val semiring_0_cancel_comm_semiring_0_cancel =
  #semiring_0_cancel_comm_semiring_0_cancel :
  'a comm_semiring_0_cancel -> 'a semiring_0_cancel;

type 'a semiring_1_cancel =
  {semiring_0_cancel_semiring_1_cancel : 'a semiring_0_cancel,
    semiring_1_semiring_1_cancel : 'a semiring_1};
val semiring_0_cancel_semiring_1_cancel = #semiring_0_cancel_semiring_1_cancel :
  'a semiring_1_cancel -> 'a semiring_0_cancel;
val semiring_1_semiring_1_cancel = #semiring_1_semiring_1_cancel :
  'a semiring_1_cancel -> 'a semiring_1;

type 'a comm_monoid_mult =
  {ab_semigroup_mult_comm_monoid_mult : 'a ab_semigroup_mult,
    monoid_mult_comm_monoid_mult : 'a monoid_mult,
    dvd_comm_monoid_mult : 'a dvd};
val ab_semigroup_mult_comm_monoid_mult = #ab_semigroup_mult_comm_monoid_mult :
  'a comm_monoid_mult -> 'a ab_semigroup_mult;
val monoid_mult_comm_monoid_mult = #monoid_mult_comm_monoid_mult :
  'a comm_monoid_mult -> 'a monoid_mult;
val dvd_comm_monoid_mult = #dvd_comm_monoid_mult :
  'a comm_monoid_mult -> 'a dvd;

type 'a comm_semiring_1 =
  {comm_monoid_mult_comm_semiring_1 : 'a comm_monoid_mult,
    comm_semiring_0_comm_semiring_1 : 'a comm_semiring_0,
    semiring_1_comm_semiring_1 : 'a semiring_1};
val comm_monoid_mult_comm_semiring_1 = #comm_monoid_mult_comm_semiring_1 :
  'a comm_semiring_1 -> 'a comm_monoid_mult;
val comm_semiring_0_comm_semiring_1 = #comm_semiring_0_comm_semiring_1 :
  'a comm_semiring_1 -> 'a comm_semiring_0;
val semiring_1_comm_semiring_1 = #semiring_1_comm_semiring_1 :
  'a comm_semiring_1 -> 'a semiring_1;

type 'a comm_semiring_1_cancel =
  {comm_semiring_0_cancel_comm_semiring_1_cancel : 'a comm_semiring_0_cancel,
    comm_semiring_1_comm_semiring_1_cancel : 'a comm_semiring_1,
    semiring_1_cancel_comm_semiring_1_cancel : 'a semiring_1_cancel};
val comm_semiring_0_cancel_comm_semiring_1_cancel =
  #comm_semiring_0_cancel_comm_semiring_1_cancel :
  'a comm_semiring_1_cancel -> 'a comm_semiring_0_cancel;
val comm_semiring_1_comm_semiring_1_cancel =
  #comm_semiring_1_comm_semiring_1_cancel :
  'a comm_semiring_1_cancel -> 'a comm_semiring_1;
val semiring_1_cancel_comm_semiring_1_cancel =
  #semiring_1_cancel_comm_semiring_1_cancel :
  'a comm_semiring_1_cancel -> 'a semiring_1_cancel;

type 'a semidom =
  {comm_semiring_1_cancel_semidom : 'a comm_semiring_1_cancel,
    semiring_1_no_zero_divisors_semidom : 'a semiring_1_no_zero_divisors};
val comm_semiring_1_cancel_semidom = #comm_semiring_1_cancel_semidom :
  'a semidom -> 'a comm_semiring_1_cancel;
val semiring_1_no_zero_divisors_semidom = #semiring_1_no_zero_divisors_semidom :
  'a semidom -> 'a semiring_1_no_zero_divisors;

val ab_semigroup_add_nat = {semigroup_add_ab_semigroup_add = semigroup_add_nat}
  : nat ab_semigroup_add;

val monoid_add_nat =
  {semigroup_add_monoid_add = semigroup_add_nat, zero_monoid_add = zero_nat} :
  nat monoid_add;

val comm_monoid_add_nat =
  {ab_semigroup_add_comm_monoid_add = ab_semigroup_add_nat,
    monoid_add_comm_monoid_add = monoid_add_nat}
  : nat comm_monoid_add;

val mult_zero_nat = {times_mult_zero = times_nat, zero_mult_zero = zero_nat} :
  nat mult_zero;

val semigroup_mult_nat = {times_semigroup_mult = times_nat} :
  nat semigroup_mult;

val semiring_nat =
  {ab_semigroup_add_semiring = ab_semigroup_add_nat,
    semigroup_mult_semiring = semigroup_mult_nat}
  : nat semiring;

val semiring_0_nat =
  {comm_monoid_add_semiring_0 = comm_monoid_add_nat,
    mult_zero_semiring_0 = mult_zero_nat, semiring_semiring_0 = semiring_nat}
  : nat semiring_0;

val semiring_no_zero_divisors_nat =
  {semiring_0_semiring_no_zero_divisors = semiring_0_nat} :
  nat semiring_no_zero_divisors;

val monoid_mult_nat =
  {semigroup_mult_monoid_mult = semigroup_mult_nat,
    power_monoid_mult = power_nat}
  : nat monoid_mult;

val semiring_numeral_nat =
  {monoid_mult_semiring_numeral = monoid_mult_nat,
    numeral_semiring_numeral = numeral_nat,
    semiring_semiring_numeral = semiring_nat}
  : nat semiring_numeral;

val zero_neq_one_nat =
  {one_zero_neq_one = one_nat, zero_zero_neq_one = zero_nat} : nat zero_neq_one;

val semiring_1_nat =
  {semiring_numeral_semiring_1 = semiring_numeral_nat,
    semiring_0_semiring_1 = semiring_0_nat,
    zero_neq_one_semiring_1 = zero_neq_one_nat}
  : nat semiring_1;

val semiring_1_no_zero_divisors_nat =
  {semiring_1_semiring_1_no_zero_divisors = semiring_1_nat,
    semiring_no_zero_divisors_semiring_1_no_zero_divisors =
      semiring_no_zero_divisors_nat}
  : nat semiring_1_no_zero_divisors;

val cancel_semigroup_add_nat =
  {semigroup_add_cancel_semigroup_add = semigroup_add_nat} :
  nat cancel_semigroup_add;

val cancel_ab_semigroup_add_nat =
  {ab_semigroup_add_cancel_ab_semigroup_add = ab_semigroup_add_nat,
    cancel_semigroup_add_cancel_ab_semigroup_add = cancel_semigroup_add_nat,
    minus_cancel_ab_semigroup_add = minus_nat}
  : nat cancel_ab_semigroup_add;

val cancel_comm_monoid_add_nat =
  {cancel_ab_semigroup_add_cancel_comm_monoid_add = cancel_ab_semigroup_add_nat,
    comm_monoid_add_cancel_comm_monoid_add = comm_monoid_add_nat}
  : nat cancel_comm_monoid_add;

val semiring_0_cancel_nat =
  {cancel_comm_monoid_add_semiring_0_cancel = cancel_comm_monoid_add_nat,
    semiring_0_semiring_0_cancel = semiring_0_nat}
  : nat semiring_0_cancel;

val ab_semigroup_mult_nat =
  {semigroup_mult_ab_semigroup_mult = semigroup_mult_nat} :
  nat ab_semigroup_mult;

val comm_semiring_nat =
  {ab_semigroup_mult_comm_semiring = ab_semigroup_mult_nat,
    semiring_comm_semiring = semiring_nat}
  : nat comm_semiring;

val comm_semiring_0_nat =
  {comm_semiring_comm_semiring_0 = comm_semiring_nat,
    semiring_0_comm_semiring_0 = semiring_0_nat}
  : nat comm_semiring_0;

val comm_semiring_0_cancel_nat =
  {comm_semiring_0_comm_semiring_0_cancel = comm_semiring_0_nat,
    semiring_0_cancel_comm_semiring_0_cancel = semiring_0_cancel_nat}
  : nat comm_semiring_0_cancel;

val semiring_1_cancel_nat =
  {semiring_0_cancel_semiring_1_cancel = semiring_0_cancel_nat,
    semiring_1_semiring_1_cancel = semiring_1_nat}
  : nat semiring_1_cancel;

val comm_monoid_mult_nat =
  {ab_semigroup_mult_comm_monoid_mult = ab_semigroup_mult_nat,
    monoid_mult_comm_monoid_mult = monoid_mult_nat,
    dvd_comm_monoid_mult = dvd_nat}
  : nat comm_monoid_mult;

val comm_semiring_1_nat =
  {comm_monoid_mult_comm_semiring_1 = comm_monoid_mult_nat,
    comm_semiring_0_comm_semiring_1 = comm_semiring_0_nat,
    semiring_1_comm_semiring_1 = semiring_1_nat}
  : nat comm_semiring_1;

val comm_semiring_1_cancel_nat =
  {comm_semiring_0_cancel_comm_semiring_1_cancel = comm_semiring_0_cancel_nat,
    comm_semiring_1_comm_semiring_1_cancel = comm_semiring_1_nat,
    semiring_1_cancel_comm_semiring_1_cancel = semiring_1_cancel_nat}
  : nat comm_semiring_1_cancel;

val semidom_nat =
  {comm_semiring_1_cancel_semidom = comm_semiring_1_cancel_nat,
    semiring_1_no_zero_divisors_semidom = semiring_1_no_zero_divisors_nat}
  : nat semidom;

type 'a semiring_no_zero_divisors_cancel =
  {semiring_no_zero_divisors_semiring_no_zero_divisors_cancel :
     'a semiring_no_zero_divisors};
val semiring_no_zero_divisors_semiring_no_zero_divisors_cancel =
  #semiring_no_zero_divisors_semiring_no_zero_divisors_cancel :
  'a semiring_no_zero_divisors_cancel -> 'a semiring_no_zero_divisors;

type 'a semidom_divide =
  {divide_semidom_divide : 'a divide, semidom_semidom_divide : 'a semidom,
    semiring_no_zero_divisors_cancel_semidom_divide :
      'a semiring_no_zero_divisors_cancel};
val divide_semidom_divide = #divide_semidom_divide :
  'a semidom_divide -> 'a divide;
val semidom_semidom_divide = #semidom_semidom_divide :
  'a semidom_divide -> 'a semidom;
val semiring_no_zero_divisors_cancel_semidom_divide =
  #semiring_no_zero_divisors_cancel_semidom_divide :
  'a semidom_divide -> 'a semiring_no_zero_divisors_cancel;

val semiring_no_zero_divisors_cancel_nat =
  {semiring_no_zero_divisors_semiring_no_zero_divisors_cancel =
     semiring_no_zero_divisors_nat}
  : nat semiring_no_zero_divisors_cancel;

val semidom_divide_nat =
  {divide_semidom_divide = divide_nat, semidom_semidom_divide = semidom_nat,
    semiring_no_zero_divisors_cancel_semidom_divide =
      semiring_no_zero_divisors_cancel_nat}
  : nat semidom_divide;

type 'a algebraic_semidom =
  {semidom_divide_algebraic_semidom : 'a semidom_divide};
val semidom_divide_algebraic_semidom = #semidom_divide_algebraic_semidom :
  'a algebraic_semidom -> 'a semidom_divide;

type 'a semiring_modulo =
  {comm_semiring_1_cancel_semiring_modulo : 'a comm_semiring_1_cancel,
    modulo_semiring_modulo : 'a modulo};
val comm_semiring_1_cancel_semiring_modulo =
  #comm_semiring_1_cancel_semiring_modulo :
  'a semiring_modulo -> 'a comm_semiring_1_cancel;
val modulo_semiring_modulo = #modulo_semiring_modulo :
  'a semiring_modulo -> 'a modulo;

type 'a semidom_modulo =
  {algebraic_semidom_semidom_modulo : 'a algebraic_semidom,
    semiring_modulo_semidom_modulo : 'a semiring_modulo};
val algebraic_semidom_semidom_modulo = #algebraic_semidom_semidom_modulo :
  'a semidom_modulo -> 'a algebraic_semidom;
val semiring_modulo_semidom_modulo = #semiring_modulo_semidom_modulo :
  'a semidom_modulo -> 'a semiring_modulo;

val algebraic_semidom_nat =
  {semidom_divide_algebraic_semidom = semidom_divide_nat} :
  nat algebraic_semidom;

val semiring_modulo_nat =
  {comm_semiring_1_cancel_semiring_modulo = comm_semiring_1_cancel_nat,
    modulo_semiring_modulo = modulo_nat}
  : nat semiring_modulo;

val semidom_modulo_nat =
  {algebraic_semidom_semidom_modulo = algebraic_semidom_nat,
    semiring_modulo_semidom_modulo = semiring_modulo_nat}
  : nat semidom_modulo;

datatype rat = Frct of (int * int);

val one_rat : rat = Frct (one_inta, one_inta);

datatype real = Ratreal of rat;

val one_reala : real = Ratreal one_rat;

val one_real = {one = one_reala} : real one;

fun plus_int k l =
  Int_of_integer (IntInf.+ (integer_of_int k, integer_of_int l));

fun quotient_of (Frct x) = x;

fun divide_int k l =
  Int_of_integer (divide_integer (integer_of_int k) (integer_of_int l));

fun uminus_int k = Int_of_integer (IntInf.~ (integer_of_int k));

val zero_int : int = Int_of_integer (0 : IntInf.int);

fun less_int k l = IntInf.< (integer_of_int k, integer_of_int l);

fun gcd_integer k l =
  IntInf.abs
    (if ((l : IntInf.int) = (0 : IntInf.int)) then k
      else gcd_integer l (modulo_integer (IntInf.abs k) (IntInf.abs l)));

fun gcd_int (Int_of_integer x) (Int_of_integer y) =
  Int_of_integer (gcd_integer x y);

fun normalize p =
  (if less_int zero_int (snd p)
    then let
           val a = gcd_int (fst p) (snd p);
         in
           (divide_int (fst p) a, divide_int (snd p) a)
         end
    else (if equal_inta (snd p) zero_int then (zero_int, one_inta)
           else let
                  val a = uminus_int (gcd_int (fst p) (snd p));
                in
                  (divide_int (fst p) a, divide_int (snd p) a)
                end));

fun plus_rat p q =
  Frct let
         val a = quotient_of p;
         val (aa, c) = a;
         val b = quotient_of q;
         val (ba, d) = b;
       in
         normalize
           (plus_int (times_inta aa d) (times_inta ba c), times_inta c d)
       end;

fun plus_reala (Ratreal x) (Ratreal y) = Ratreal (plus_rat x y);

val plus_real = {plus = plus_reala} : real plus;

val zero_rat : rat = Frct (zero_int, one_inta);

val zero_reala : real = Ratreal zero_rat;

val zero_real = {zero = zero_reala} : real zero;

val semigroup_add_real = {plus_semigroup_add = plus_real} : real semigroup_add;

val numeral_real =
  {one_numeral = one_real, semigroup_add_numeral = semigroup_add_real} :
  real numeral;

fun times_rat p q = Frct let
                           val a = quotient_of p;
                           val (aa, c) = a;
                           val b = quotient_of q;
                           val (ba, d) = b;
                         in
                           normalize (times_inta aa ba, times_inta c d)
                         end;

fun times_reala (Ratreal x) (Ratreal y) = Ratreal (times_rat x y);

val times_real = {times = times_reala} : real times;

val power_real = {one_power = one_real, times_power = times_real} : real power;

val ab_semigroup_add_real =
  {semigroup_add_ab_semigroup_add = semigroup_add_real} : real ab_semigroup_add;

val semigroup_mult_real = {times_semigroup_mult = times_real} :
  real semigroup_mult;

val semiring_real =
  {ab_semigroup_add_semiring = ab_semigroup_add_real,
    semigroup_mult_semiring = semigroup_mult_real}
  : real semiring;

val mult_zero_real = {times_mult_zero = times_real, zero_mult_zero = zero_real}
  : real mult_zero;

val monoid_add_real =
  {semigroup_add_monoid_add = semigroup_add_real, zero_monoid_add = zero_real} :
  real monoid_add;

val comm_monoid_add_real =
  {ab_semigroup_add_comm_monoid_add = ab_semigroup_add_real,
    monoid_add_comm_monoid_add = monoid_add_real}
  : real comm_monoid_add;

val semiring_0_real =
  {comm_monoid_add_semiring_0 = comm_monoid_add_real,
    mult_zero_semiring_0 = mult_zero_real, semiring_semiring_0 = semiring_real}
  : real semiring_0;

val monoid_mult_real =
  {semigroup_mult_monoid_mult = semigroup_mult_real,
    power_monoid_mult = power_real}
  : real monoid_mult;

val semiring_numeral_real =
  {monoid_mult_semiring_numeral = monoid_mult_real,
    numeral_semiring_numeral = numeral_real,
    semiring_semiring_numeral = semiring_real}
  : real semiring_numeral;

val zero_neq_one_real =
  {one_zero_neq_one = one_real, zero_zero_neq_one = zero_real} :
  real zero_neq_one;

val semiring_1_real =
  {semiring_numeral_semiring_1 = semiring_numeral_real,
    semiring_0_semiring_1 = semiring_0_real,
    zero_neq_one_semiring_1 = zero_neq_one_real}
  : real semiring_1;

datatype 'a itself = Type;

type 'a len0 = {len_of : 'a itself -> nat};
val len_of = #len_of : 'a len0 -> 'a itself -> nat;

type 'a len = {len0_len : 'a len0};
val len0_len = #len0_len : 'a len -> 'a len0;

datatype 'a word = Word of int;

fun the_int A_ (Word x) = x;

fun equal_worda A_ v w = equal_inta (the_int A_ v) (the_int A_ w);

fun equal_word A_ = {equal = equal_worda A_} : 'a word equal;

fun one_worda A_ = Word one_inta;

fun one_word A_ = {one = one_worda A_} : 'a word one;

fun modulo_int k l =
  Int_of_integer (modulo_integer (integer_of_int k) (integer_of_int l));

fun power A_ a n =
  (if equal_nata n zero_nata then one (one_power A_)
    else times (times_power A_) a (power A_ a (minus_nata n one_nata)));

fun take_bit_int n k =
  modulo_int k (power power_int (Int_of_integer (2 : IntInf.int)) n);

fun of_inta A_ k = Word (take_bit_int (len_of (len0_len A_) Type) k);

fun times_worda A_ a b = of_inta A_ (times_inta (the_int A_ a) (the_int A_ b));

fun times_word A_ = {times = times_worda A_} : 'a word times;

fun power_word A_ = {one_power = one_word A_, times_power = times_word A_} :
  'a word power;

fun nat_of_integer k = Nat (max ord_integer (0 : IntInf.int) k);

type 'a finite = {};

datatype 'a bit0 = Abs_bit0 of int;

fun len_of_bit0 A_ uu =
  times_nata (nat_of_integer (2 : IntInf.int)) (len_of A_ Type);

fun len0_bit0 A_ = {len_of = len_of_bit0 A_} : 'a bit0 len0;

fun len_bit0 A_ = {len0_len = len0_bit0 (len0_len A_)} : 'a bit0 len;

datatype 'a bit1 = Abs_bit1 of int;

fun len_of_bit1 A_ uu =
  plus_nata (times_nata (nat_of_integer (2 : IntInf.int)) (len_of A_ Type))
    one_nata;

fun len0_bit1 A_ = {len_of = len_of_bit1 A_} : 'a bit1 len0;

fun len_bit1 A_ = {len0_len = len0_bit1 A_} : 'a bit1 len;

datatype num1 = One_num1;

fun len_of_num1 uu = one_nata;

val len0_num1 = {len_of = len_of_num1} : num1 len0;

val len_num1 = {len0_len = len0_num1} : num1 len;

fun eq A_ a b = equal A_ a b;

fun equal_proda A_ B_ (x1, x2) (y1, y2) = eq A_ x1 y1 andalso eq B_ x2 y2;

fun equal_prod A_ B_ = {equal = equal_proda A_ B_} : ('a * 'b) equal;

datatype ('a, 'b) float = Abs_float of (num1 word * ('a word * 'b word));

datatype roundmode = To_nearest | Float_To_zero | To_pinfinity | To_ninfinity;

fun nat k = Nat (max ord_integer (0 : IntInf.int) (integer_of_int k));

fun suc n = plus_nata n one_nata;

fun bias A_ B_ x =
  minus_nata
    (power power_nat (nat_of_integer (2 : IntInf.int))
      (minus_nata (len_of (len0_len A_) Type) one_nata))
    one_nata;

fun uminus_word A_ a = of_inta A_ (uminus_int (the_int A_ a));

fun the_nat A_ w = nat (the_int A_ w);

fun emax A_ B_ x = the_nat A_ (uminus_word A_ (one_worda A_));

fun sign A_ B_ (Abs_float xa) = let
                                  val (s, (_, _)) = xa;
                                in
                                  the_nat len_num1 s
                                end;

fun uminus_rat p = Frct let
                          val a = quotient_of p;
                          val (aa, b) = a;
                        in
                          (uminus_int aa, b)
                        end;

fun uminus_real (Ratreal x) = Ratreal (uminus_rat x);

fun divide_rat p q = Frct let
                            val a = quotient_of p;
                            val (aa, c) = a;
                            val b = quotient_of q;
                            val (ba, d) = b;
                          in
                            normalize (times_inta aa d, times_inta c ba)
                          end;

fun divide_real (Ratreal x) (Ratreal y) = Ratreal (divide_rat x y);

fun zero_word A_ = Word zero_int;

fun numeral A_ (Bit1 n) =
  let
    val m = numeral A_ n;
  in
    plus ((plus_semigroup_add o semigroup_add_numeral) A_)
      (plus ((plus_semigroup_add o semigroup_add_numeral) A_) m m)
      (one (one_numeral A_))
  end
  | numeral A_ (Bit0 n) =
    let
      val m = numeral A_ n;
    in
      plus ((plus_semigroup_add o semigroup_add_numeral) A_) m m
    end
  | numeral A_ One = one (one_numeral A_);

fun map_prod f g (a, b) = (f a, g b);

fun divmod_nat m n =
  let
    val k = integer_of_nat m;
    val l = integer_of_nat n;
  in
    map_prod nat_of_integer nat_of_integer
      (if ((k : IntInf.int) = (0 : IntInf.int))
        then ((0 : IntInf.int), (0 : IntInf.int))
        else (if ((l : IntInf.int) = (0 : IntInf.int))
               then ((0 : IntInf.int), k)
               else IntInf.divMod (IntInf.abs k, IntInf.abs l)))
  end;

fun of_nata A_ n =
  (if equal_nata n zero_nata
    then zero ((zero_mult_zero o mult_zero_semiring_0 o semiring_0_semiring_1)
                A_)
    else let
           val (m, q) = divmod_nat n (nat_of_integer (2 : IntInf.int));
           val ma =
             times ((times_power o power_monoid_mult o
                      monoid_mult_semiring_numeral o
                      semiring_numeral_semiring_1)
                     A_)
               (numeral
                 ((numeral_semiring_numeral o semiring_numeral_semiring_1) A_)
                 (Bit0 One))
               (of_nata A_ m);
         in
           (if equal_nata q zero_nata then ma
             else plus ((plus_semigroup_add o semigroup_add_numeral o
                          numeral_semiring_numeral o
                          semiring_numeral_semiring_1)
                         A_)
                    ma (one ((one_numeral o numeral_semiring_numeral o
                               semiring_numeral_semiring_1)
                              A_)))
         end);

fun of_int a = Frct (a, one_inta);

fun valof A_ B_ (Abs_float xa) =
  let
    val (s, (e, f)) = xa;
    val x = Type;
  in
    (if equal_worda A_ e (zero_word A_)
      then times_reala
             (times_reala
               (power power_real (uminus_real one_reala) (the_nat len_num1 s))
               (divide_real (Ratreal (of_int (Int_of_integer (2 : IntInf.int))))
                 (power power_real
                   (Ratreal (of_int (Int_of_integer (2 : IntInf.int))))
                   (bias A_ B_ x))))
             (divide_real (of_nata semiring_1_real (the_nat B_ f))
               (power power_real
                 (Ratreal (of_int (Int_of_integer (2 : IntInf.int))))
                 (len_of (len0_len B_) Type)))
      else times_reala
             (times_reala
               (power power_real (uminus_real one_reala) (the_nat len_num1 s))
               (divide_real
                 (power power_real
                   (Ratreal (of_int (Int_of_integer (2 : IntInf.int))))
                   (the_nat A_ e))
                 (power power_real
                   (Ratreal (of_int (Int_of_integer (2 : IntInf.int))))
                   (bias A_ B_ x))))
             (plus_reala one_reala
               (divide_real (of_nata semiring_1_real (the_nat B_ f))
                 (power power_real
                   (Ratreal (of_int (Int_of_integer (2 : IntInf.int))))
                   (len_of (len0_len B_) Type)))))
  end;

fun fraction A_ B_ (Abs_float xa) = let
                                      val (_, a) = xa;
                                      val (_, aa) = a;
                                    in
                                      the_nat B_ aa
                                    end;

fun exponent A_ B_ (Abs_float xa) = let
                                      val (_, (e, _)) = xa;
                                    in
                                      the_nat A_ e
                                    end;

fun is_nan A_ B_ a =
  equal_nata (exponent A_ B_ a) (emax A_ B_ Type) andalso
    not (equal_nata (fraction A_ B_ a) zero_nata);

fun int_of_nat n = Int_of_integer (integer_of_nat n);

fun of_nat A_ n =
  Word (take_bit_int (len_of (len0_len A_) Type) (int_of_nat n));

fun is_zero A_ B_ a =
  equal_nata (exponent A_ B_ a) zero_nata andalso
    equal_nata (fraction A_ B_ a) zero_nata;

fun minus_int k l =
  Int_of_integer (IntInf.- (integer_of_int k, integer_of_int l));

fun minus_rat p q =
  Frct let
         val a = quotient_of p;
         val (aa, c) = a;
         val b = quotient_of q;
         val (ba, d) = b;
       in
         normalize
           (minus_int (times_inta aa d) (times_inta ba c), times_inta c d)
       end;

fun minus_real (Ratreal x) (Ratreal y) = Ratreal (minus_rat x y);

fun largest A_ B_ x =
  times_reala
    (divide_real
      (power power_real (Ratreal (of_int (Int_of_integer (2 : IntInf.int))))
        (minus_nata (emax A_ B_ x) one_nata))
      (power power_real (Ratreal (of_int (Int_of_integer (2 : IntInf.int))))
        (bias A_ B_ x)))
    (minus_real (Ratreal (of_int (Int_of_integer (2 : IntInf.int))))
      (divide_real one_reala
        (power power_real (Ratreal (of_int (Int_of_integer (2 : IntInf.int))))
          (len_of (len0_len B_) Type))));

fun minus_word A_ a b = of_inta A_ (minus_int (the_int A_ a) (the_int A_ b));

fun topfloat A_ B_ =
  Abs_float
    (zero_word len_num1,
      (uminus_word A_ (of_inta A_ (Int_of_integer (2 : IntInf.int))),
        minus_word B_
          (power (power_word B_) (of_inta B_ (Int_of_integer (2 : IntInf.int)))
            (len_of (len0_len B_) Type))
          (one_worda B_)));

fun uminus_float A_ B_ (Abs_float x) =
  Abs_float let
              val (s, (e, f)) = x;
            in
              (minus_word len_num1 (one_worda len_num1) s, (e, f))
            end;

fun zero_float A_ B_ =
  Abs_float (zero_word len_num1, (zero_word A_, zero_word B_));

fun zerosign A_ B_ s a =
  (if is_zero A_ B_ a
    then (if equal_nata s zero_nata then zero_float A_ B_
           else uminus_float A_ B_ (zero_float A_ B_))
    else a);

fun is_denormal A_ B_ a =
  equal_nata (exponent A_ B_ a) zero_nata andalso
    not (equal_nata (fraction A_ B_ a) zero_nata);

fun less_nat m n = IntInf.< (integer_of_nat m, integer_of_nat n);

fun is_normal A_ B_ a =
  less_nat zero_nata (exponent A_ B_ a) andalso
    less_nat (exponent A_ B_ a) (emax A_ B_ Type);

fun is_finite A_ B_ a =
  is_normal A_ B_ a orelse (is_denormal A_ B_ a orelse is_zero A_ B_ a);

fun threshold A_ B_ x =
  times_reala
    (divide_real
      (power power_real (Ratreal (of_int (Int_of_integer (2 : IntInf.int))))
        (minus_nata (emax A_ B_ x) one_nata))
      (power power_real (Ratreal (of_int (Int_of_integer (2 : IntInf.int))))
        (bias A_ B_ x)))
    (minus_real (Ratreal (of_int (Int_of_integer (2 : IntInf.int))))
      (divide_real one_reala
        (power power_real (Ratreal (of_int (Int_of_integer (2 : IntInf.int))))
          (suc (len_of (len0_len B_) Type)))));

fun is_infinity A_ B_ a =
  equal_nata (exponent A_ B_ a) (emax A_ B_ Type) andalso
    equal_nata (fraction A_ B_ a) zero_nata;

fun fp_gen A_ B_ s f e =
  Abs_float
    (of_nat len_num1 (nat_of_integer s),
      (of_inta A_ (Int_of_integer e), of_nat B_ (nat_of_integer f)));

fun fp32 x =
  fp_gen (len_bit0 (len_bit0 (len_bit0 len_num1)))
    (len_bit1 (len0_bit1 (len0_bit1 (len0_bit0 len0_num1)))) x;

fun fp64 x =
  fp_gen (len_bit1 (len0_bit1 (len0_bit0 len0_num1)))
    (len_bit0 (len_bit0 (len_bit1 (len0_bit0 (len0_bit1 len0_num1))))) x;

fun plus_infinity A_ B_ =
  Abs_float (zero_word len_num1, (uminus_word A_ (one_worda A_), zero_word B_));

fun nan01 A_ B_ =
  Abs_float (zero_word len_num1, (uminus_word A_ (one_worda A_), one_worda B_));

val qNaN32 : (num1 bit0 bit0 bit0, num1 bit0 bit1 bit1 bit1) float =
  nan01 (len_bit0 (len_bit0 (len_bit0 len_num1)))
    (len_bit1 (len0_bit1 (len0_bit1 (len0_bit0 len0_num1))));

val qNaN64 : (num1 bit0 bit1 bit1, num1 bit1 bit0 bit1 bit0 bit0) float =
  nan01 (len_bit1 (len0_bit1 (len0_bit0 len0_num1)))
    (len_bit0 (len_bit0 (len_bit1 (len0_bit0 (len0_bit1 len0_num1)))));

val sNaN32 : (num1 bit0 bit0 bit0, num1 bit0 bit1 bit1 bit1) float =
  nan01 (len_bit0 (len_bit0 (len_bit0 len_num1)))
    (len_bit1 (len0_bit1 (len0_bit1 (len0_bit0 len0_num1))));

val sNaN64 : (num1 bit0 bit1 bit1, num1 bit1 bit0 bit1 bit0 bit0) float =
  nan01 (len_bit1 (len0_bit1 (len0_bit0 len0_num1)))
    (len_bit0 (len_bit0 (len_bit1 (len0_bit0 (len0_bit1 len0_num1)))));

fun dvd (A1_, A2_) a b =
  eq A1_
    (modulo ((modulo_semiring_modulo o semiring_modulo_semidom_modulo) A2_) b a)
    (zero ((zero_mult_zero o mult_zero_semiring_0 o semiring_0_semiring_1 o
             semiring_1_comm_semiring_1 o
             comm_semiring_1_comm_semiring_1_cancel o
             comm_semiring_1_cancel_semidom o semidom_semidom_divide o
             semidom_divide_algebraic_semidom o
             algebraic_semidom_semidom_modulo)
            A2_));

val plus_inf32 : (num1 bit0 bit0 bit0, num1 bit0 bit1 bit1 bit1) float =
  plus_infinity (len_bit0 (len_bit0 (len_bit0 len_num1)))
    (len_bit1 (len0_bit1 (len0_bit1 (len0_bit0 len0_num1))));

val plus_inf64 : (num1 bit0 bit1 bit1, num1 bit1 bit0 bit1 bit0 bit0) float =
  plus_infinity (len_bit1 (len0_bit1 (len0_bit0 len0_num1)))
    (len_bit0 (len_bit0 (len_bit1 (len0_bit0 (len0_bit1 len0_num1)))));

val minus_inf32 : (num1 bit0 bit0 bit0, num1 bit0 bit1 bit1 bit1) float =
  uminus_float (len_bit0 (len_bit0 (len_bit0 len_num1)))
    (len_bit1 (len0_bit1 (len0_bit1 (len0_bit0 len0_num1))))
    (plus_infinity (len_bit0 (len_bit0 (len_bit0 len_num1)))
      (len_bit1 (len0_bit1 (len0_bit1 (len0_bit0 len0_num1)))));

val minus_inf64 : (num1 bit0 bit1 bit1, num1 bit1 bit0 bit1 bit0 bit0) float =
  uminus_float (len_bit1 (len0_bit1 (len0_bit0 len0_num1)))
    (len_bit0 (len_bit0 (len_bit1 (len0_bit0 (len0_bit1 len0_num1)))))
    (plus_infinity (len_bit1 (len0_bit1 (len0_bit0 len0_num1)))
      (len_bit0 (len_bit0 (len_bit1 (len0_bit0 (len0_bit1 len0_num1))))));

val plus_zero32 : (num1 bit0 bit0 bit0, num1 bit0 bit1 bit1 bit1) float =
  zero_float (len_bit0 (len_bit0 (len_bit0 len_num1)))
    (len_bit1 (len0_bit1 (len0_bit1 (len0_bit0 len0_num1))));

val plus_zero64 : (num1 bit0 bit1 bit1, num1 bit1 bit0 bit1 bit0 bit0) float =
  zero_float (len_bit1 (len0_bit1 (len0_bit0 len0_num1)))
    (len_bit0 (len_bit0 (len_bit1 (len0_bit0 (len0_bit1 len0_num1)))));

fun equal_float A_ B_ (Abs_float xc) (Abs_float xa) =
  equal_proda (equal_word len_num1) (equal_prod (equal_word A_) (equal_word B_))
    xc xa;

fun plus_word A_ a b = of_inta A_ (plus_int (the_int A_ a) (the_int A_ b));

fun prev_float A_ B_ (Abs_float x) =
  Abs_float
    let
      val (s, (e, f)) = x;
    in
      (if equal_worda len_num1 s (zero_word len_num1)
        then (if equal_worda B_ f (zero_word B_) andalso
                   equal_worda A_ e (zero_word A_)
               then (one_worda len_num1, (e, f))
               else (if equal_worda B_ f (zero_word B_)
                      then (s, (minus_word A_ e (one_worda A_),
                                 uminus_word B_ (one_worda B_)))
                      else (s, (e, minus_word B_ f (one_worda B_)))))
        else (if equal_worda B_ f (uminus_word B_ (one_worda B_))
               then (s, (plus_word A_ e (one_worda A_), zero_word B_))
               else (s, (e, plus_word B_ f (one_worda B_)))))
    end;

fun prev_floata A_ B_ f =
  (if equal_float A_ B_ f (zero_float A_ B_)
    then prev_float A_ B_ (uminus_float A_ B_ (zero_float A_ B_))
    else prev_float A_ B_ f);

fun less_rat p q = let
                     val a = quotient_of p;
                     val (aa, c) = a;
                     val b = quotient_of q;
                     val (ba, d) = b;
                   in
                     less_int (times_inta aa d) (times_inta c ba)
                   end;

fun less_real (Ratreal x) (Ratreal y) = less_rat x y;

fun lbound A_ B_ r f =
  (if less_real r (valof A_ B_ f) then prev_floata A_ B_ f
    else zerosign A_ B_ zero_nata f);

fun less_eq_int k l = IntInf.<= (integer_of_int k, integer_of_int l);

fun less_eq_rat p q = let
                        val a = quotient_of p;
                        val (aa, c) = a;
                        val b = quotient_of q;
                        val (ba, d) = b;
                      in
                        less_eq_int (times_inta aa d) (times_inta c ba)
                      end;

fun less_eq_real (Ratreal x) (Ratreal y) = less_eq_rat x y;

fun next_float A_ B_ (Abs_float x) =
  Abs_float
    let
      val (s, (e, f)) = x;
    in
      (if equal_worda len_num1 s (one_worda len_num1)
        then (if equal_worda B_ f (zero_word B_) andalso
                   equal_worda A_ e (zero_word A_)
               then (zero_word len_num1, (e, f))
               else (if equal_worda B_ f (zero_word B_)
                      then (s, (minus_word A_ e (one_worda A_),
                                 minus_word B_ f (one_worda B_)))
                      else (s, (e, minus_word B_ f (one_worda B_)))))
        else (if equal_worda B_ f (uminus_word B_ (one_worda B_))
               then (s, (plus_word A_ e (one_worda A_), zero_word B_))
               else (s, (e, plus_word B_ f (one_worda B_)))))
    end;

fun next_floatb A_ B_ f =
  (if equal_float A_ B_ f (uminus_float A_ B_ (zero_float A_ B_))
    then next_float A_ B_ (zero_float A_ B_) else next_float A_ B_ f);

fun rbound A_ B_ r f =
  (if less_eq_real (valof A_ B_ f) r then next_floatb A_ B_ f
    else zerosign A_ B_ (if less_real r zero_reala then one_nata else zero_nata)
           f);

fun equal_roundmode To_pinfinity To_ninfinity = false
  | equal_roundmode To_ninfinity To_pinfinity = false
  | equal_roundmode Float_To_zero To_ninfinity = false
  | equal_roundmode To_ninfinity Float_To_zero = false
  | equal_roundmode Float_To_zero To_pinfinity = false
  | equal_roundmode To_pinfinity Float_To_zero = false
  | equal_roundmode To_nearest To_ninfinity = false
  | equal_roundmode To_ninfinity To_nearest = false
  | equal_roundmode To_nearest To_pinfinity = false
  | equal_roundmode To_pinfinity To_nearest = false
  | equal_roundmode To_nearest Float_To_zero = false
  | equal_roundmode Float_To_zero To_nearest = false
  | equal_roundmode To_ninfinity To_ninfinity = true
  | equal_roundmode To_pinfinity To_pinfinity = true
  | equal_roundmode Float_To_zero Float_To_zero = true
  | equal_roundmode To_nearest To_nearest = true;

fun equal_rat a b =
  equal_proda equal_int equal_int (quotient_of a) (quotient_of b);

fun equal_real (Ratreal x) (Ratreal y) = equal_rat x y;

fun equal_bool p true = p
  | equal_bool p false = not p
  | equal_bool true p = p
  | equal_bool false p = not p;

fun z_compat A_ B_ f s =
  (if is_zero A_ B_ f
    then equal_bool (equal_nata (sign A_ B_ f) zero_nata)
           (equal_nata s zero_nata)
    else true);

fun check_zs_r_pinf A_ B_ s r f =
  (if less_real r (uminus_real (largest A_ B_ Type))
    then equal_float A_ B_ f (uminus_float A_ B_ (topfloat A_ B_))
    else (if less_real (largest A_ B_ Type) r
           then equal_float A_ B_ f (plus_infinity A_ B_)
           else (if equal_real r (uminus_real (largest A_ B_ Type))
                  then equal_float A_ B_ f (uminus_float A_ B_ (topfloat A_ B_))
                  else (if equal_float A_ B_ f
                             (uminus_float A_ B_ (topfloat A_ B_)) orelse
                             not (is_finite A_ B_ f)
                         then false
                         else (if equal_float A_ B_ f (zero_float A_ B_)
                                then equal_real r zero_reala andalso
                                       equal_nata s zero_nata
                                else less_real
                                       (valof A_ B_ (prev_float A_ B_ f))
                                       r andalso
                                       (less_eq_real r (valof A_ B_ f) andalso
 z_compat A_ B_ f s))))));

fun next_floata A_ B_ f =
  (if equal_float A_ B_ f (uminus_float A_ B_ (zero_float A_ B_))
    then next_float A_ B_ (zero_float A_ B_)
    else (if equal_float A_ B_ (next_float A_ B_ f)
               (uminus_float A_ B_ (zero_float A_ B_))
           then zero_float A_ B_ else next_float A_ B_ f));

fun check_zs_r_ninf A_ B_ s r f =
  (if less_real r (uminus_real (largest A_ B_ Type))
    then equal_float A_ B_ f (uminus_float A_ B_ (plus_infinity A_ B_))
    else (if less_real (largest A_ B_ Type) r
           then equal_float A_ B_ f (topfloat A_ B_)
           else (if equal_real r (largest A_ B_ Type)
                  then equal_float A_ B_ f (topfloat A_ B_)
                  else (if equal_float A_ B_ f (topfloat A_ B_) orelse
                             not (is_finite A_ B_ f)
                         then false
                         else less_eq_real (valof A_ B_ f) r andalso
                                (less_real r
                                   (valof A_ B_ (next_floata A_ B_ f)) andalso
                                  z_compat A_ B_ f s)))));

fun check_zs_r_tz A_ B_ s r f =
  (if less_real r (uminus_real (largest A_ B_ Type))
    then equal_float A_ B_ f (uminus_float A_ B_ (topfloat A_ B_))
    else (if less_real (largest A_ B_ Type) r
           then equal_float A_ B_ f (topfloat A_ B_)
           else (if equal_real r (uminus_real (largest A_ B_ Type))
                  then equal_float A_ B_ f (uminus_float A_ B_ (topfloat A_ B_))
                  else (if equal_real r (largest A_ B_ Type)
                         then equal_float A_ B_ f (topfloat A_ B_)
                         else (if equal_float A_ B_ f
                                    (uminus_float A_ B_ (topfloat A_ B_)) orelse
                                    (equal_float A_ B_ f (topfloat A_ B_) orelse
                                      not (is_finite A_ B_ f))
                                then false
                                else (if is_zero A_ B_ f
                                       then equal_bool (equal_nata s zero_nata)
      (equal_float A_ B_ f (zero_float A_ B_)) andalso
      (less_real
         (valof A_ B_
           (prev_float A_ B_ (uminus_float A_ B_ (zero_float A_ B_))))
         r andalso
        less_real r (valof A_ B_ (next_float A_ B_ (zero_float A_ B_))))
                                       else (if less_real r zero_reala
      then less_real (valof A_ B_ (prev_float A_ B_ f)) r andalso
             less_eq_real r (valof A_ B_ f)
      else less_eq_real (valof A_ B_ f) r andalso
             less_real r (valof A_ B_ (next_float A_ B_ f)))))))));

fun abs_real a = (if less_real a zero_reala then uminus_real a else a);

fun check_zs_r_tn_aux A_ B_ s r f =
  let
    val f_1 = lbound A_ B_ r f;
    val f_2 = rbound A_ B_ r f;
    val delta_1 = abs_real (minus_real r (valof A_ B_ f_1));
    val delta_2 = abs_real (minus_real r (valof A_ B_ f_2));
  in
    (if less_real delta_1 delta_2
      then equal_float A_ B_ f (zerosign A_ B_ s f_1)
      else (if less_real delta_2 delta_1
             then equal_float A_ B_ f (zerosign A_ B_ s f_2)
             else (if dvd (equal_nat, semidom_modulo_nat)
                        (nat_of_integer (2 : IntInf.int)) (fraction A_ B_ f_1)
                    then equal_float A_ B_ f (zerosign A_ B_ s f_1)
                    else equal_float A_ B_ f (zerosign A_ B_ s f_2))))
  end;

fun is_close A_ B_ r f =
  is_finite A_ B_ f andalso
    (if is_zero A_ B_ f
      then less_real
             (valof A_ B_
               (prev_float A_ B_ (uminus_float A_ B_ (zero_float A_ B_))))
             r andalso
             less_real r (valof A_ B_ (next_float A_ B_ (zero_float A_ B_)))
      else less_real (valof A_ B_ (prev_float A_ B_ f)) r andalso
             less_real r (valof A_ B_ (next_float A_ B_ f)));

fun check_zs_r_tn A_ B_ s r f =
  (if less_eq_real r (uminus_real (threshold A_ B_ Type))
    then equal_float A_ B_ f (uminus_float A_ B_ (plus_infinity A_ B_))
    else (if less_eq_real (threshold A_ B_ Type) r
           then equal_float A_ B_ f (plus_infinity A_ B_)
           else (if equal_float A_ B_ f (topfloat A_ B_)
                  then less_real (abs_real (minus_real r (valof A_ B_ f)))
                         (abs_real
                           (minus_real r (valof A_ B_ (prev_float A_ B_ f))))
                  else (if equal_float A_ B_ f
                             (uminus_float A_ B_ (topfloat A_ B_))
                         then less_real
                                (abs_real (minus_real r (valof A_ B_ f)))
                                (abs_real
                                  (minus_real r
                                    (valof A_ B_ (next_float A_ B_ f))))
                         else (if not (is_close A_ B_ r f) orelse
                                    (equal_float A_ B_ f (topfloat A_ B_) orelse
                                      equal_float A_ B_ f
(uminus_float A_ B_ (topfloat A_ B_)))
                                then false
                                else check_zs_r_tn_aux A_ B_ s r f)))));

fun check_zs_r A_ B_ To_ninfinity s r f = check_zs_r_ninf A_ B_ s r f
  | check_zs_r A_ B_ To_pinfinity s r f = check_zs_r_pinf A_ B_ s r f
  | check_zs_r A_ B_ Float_To_zero s r f = check_zs_r_tz A_ B_ s r f
  | check_zs_r A_ B_ To_nearest s r f = check_zs_r_tn A_ B_ s r f;

fun check_fadd A_ B_ m a b res =
  (if is_nan A_ B_ a orelse
        (is_nan A_ B_ b orelse
          is_infinity A_ B_ a andalso
            (is_infinity A_ B_ b andalso
              not (equal_nata (sign A_ B_ a) (sign A_ B_ b))))
    then is_nan A_ B_ res
    else (if is_infinity A_ B_ a then equal_float A_ B_ res a
           else (if is_infinity A_ B_ b then equal_float A_ B_ res b
                  else check_zs_r A_ B_ m
                         (if is_zero A_ B_ a andalso
                               (is_zero A_ B_ b andalso
                                 equal_nata (sign A_ B_ a) (sign A_ B_ b))
                           then sign A_ B_ a
                           else (if equal_roundmode m To_ninfinity then one_nata
                                  else zero_nata))
                         (plus_reala (valof A_ B_ a) (valof A_ B_ b)) res)));

fun check_fadd32 x =
  check_fadd (len_bit0 (len_bit0 (len_bit0 len_num1)))
    (len_bit1 (len0_bit1 (len0_bit1 (len0_bit0 len0_num1)))) x;

fun check_fadd64 x =
  check_fadd (len_bit1 (len0_bit1 (len0_bit0 len0_num1)))
    (len_bit0 (len_bit0 (len_bit1 (len0_bit0 (len0_bit1 len0_num1))))) x;

fun check_fdiv A_ B_ m a b res =
  (if is_nan A_ B_ a orelse
        (is_nan A_ B_ b orelse
          (is_zero A_ B_ a andalso is_zero A_ B_ b orelse
            is_infinity A_ B_ a andalso is_infinity A_ B_ b))
    then is_nan A_ B_ res
    else (if is_infinity A_ B_ a orelse is_zero A_ B_ b
           then (if equal_nata (sign A_ B_ a) (sign A_ B_ b)
                  then equal_float A_ B_ res (plus_infinity A_ B_)
                  else equal_float A_ B_ res
                         (uminus_float A_ B_ (plus_infinity A_ B_)))
           else (if is_infinity A_ B_ b
                  then (if equal_nata (sign A_ B_ a) (sign A_ B_ b)
                         then equal_float A_ B_ res (zero_float A_ B_)
                         else equal_float A_ B_ res
                                (uminus_float A_ B_ (zero_float A_ B_)))
                  else check_zs_r A_ B_ m
                         (if equal_nata (sign A_ B_ a) (sign A_ B_ b)
                           then zero_nata else one_nata)
                         (divide_real (valof A_ B_ a) (valof A_ B_ b)) res)));

fun check_fdiv32 x =
  check_fdiv (len_bit0 (len_bit0 (len_bit0 len_num1)))
    (len_bit1 (len0_bit1 (len0_bit1 (len0_bit0 len0_num1)))) x;

fun check_fdiv64 x =
  check_fdiv (len_bit1 (len0_bit1 (len0_bit0 len0_num1)))
    (len_bit0 (len_bit0 (len_bit1 (len0_bit0 (len0_bit1 len0_num1))))) x;

fun check_fmul A_ B_ m a b res =
  (if is_nan A_ B_ a orelse
        (is_nan A_ B_ b orelse
          (is_zero A_ B_ a andalso is_infinity A_ B_ b orelse
            is_infinity A_ B_ a andalso is_zero A_ B_ b))
    then is_nan A_ B_ res
    else (if is_infinity A_ B_ a orelse is_infinity A_ B_ b
           then (if equal_nata (sign A_ B_ a) (sign A_ B_ b)
                  then equal_float A_ B_ res (plus_infinity A_ B_)
                  else equal_float A_ B_ res
                         (uminus_float A_ B_ (plus_infinity A_ B_)))
           else check_zs_r A_ B_ m
                  (if equal_nata (sign A_ B_ a) (sign A_ B_ b) then zero_nata
                    else one_nata)
                  (times_reala (valof A_ B_ a) (valof A_ B_ b)) res));

fun check_fmul32 x =
  check_fmul (len_bit0 (len_bit0 (len_bit0 len_num1)))
    (len_bit1 (len0_bit1 (len0_bit1 (len0_bit0 len0_num1)))) x;

fun check_fmul64 x =
  check_fmul (len_bit1 (len0_bit1 (len0_bit0 len0_num1)))
    (len_bit0 (len_bit0 (len_bit1 (len0_bit0 (len0_bit1 len0_num1))))) x;

fun check_fsub A_ B_ m a b res =
  (if is_nan A_ B_ a orelse
        (is_nan A_ B_ b orelse
          is_infinity A_ B_ a andalso
            (is_infinity A_ B_ b andalso
              equal_nata (sign A_ B_ a) (sign A_ B_ b)))
    then is_nan A_ B_ res
    else (if is_infinity A_ B_ a then equal_float A_ B_ res a
           else (if is_infinity A_ B_ b
                  then equal_float A_ B_ res (uminus_float A_ B_ b)
                  else check_zs_r A_ B_ m
                         (if is_zero A_ B_ a andalso
                               (is_zero A_ B_ b andalso
                                 not (equal_nata (sign A_ B_ a) (sign A_ B_ b)))
                           then sign A_ B_ a
                           else (if equal_roundmode m To_ninfinity then one_nata
                                  else zero_nata))
                         (minus_real (valof A_ B_ a) (valof A_ B_ b)) res)));

fun check_fsub32 x =
  check_fsub (len_bit0 (len_bit0 (len_bit0 len_num1)))
    (len_bit1 (len0_bit1 (len0_bit1 (len0_bit0 len0_num1)))) x;

fun check_fsub64 x =
  check_fsub (len_bit1 (len0_bit1 (len0_bit0 len0_num1)))
    (len_bit0 (len_bit0 (len_bit1 (len0_bit0 (len0_bit1 len0_num1))))) x;

val minus_zero32 : (num1 bit0 bit0 bit0, num1 bit0 bit1 bit1 bit1) float =
  uminus_float (len_bit0 (len_bit0 (len_bit0 len_num1)))
    (len_bit1 (len0_bit1 (len0_bit1 (len0_bit0 len0_num1))))
    (zero_float (len_bit0 (len_bit0 (len_bit0 len_num1)))
      (len_bit1 (len0_bit1 (len0_bit1 (len0_bit0 len0_num1)))));

val minus_zero64 : (num1 bit0 bit1 bit1, num1 bit1 bit0 bit1 bit0 bit0) float =
  uminus_float (len_bit1 (len0_bit1 (len0_bit0 len0_num1)))
    (len_bit0 (len_bit0 (len_bit1 (len0_bit0 (len0_bit1 len0_num1)))))
    (zero_float (len_bit1 (len0_bit1 (len0_bit0 len0_num1)))
      (len_bit0 (len_bit0 (len_bit1 (len0_bit0 (len0_bit1 len0_num1))))));

fun check_fr A_ B_ m s r f =
  check_zs_r A_ B_ m (if s then one_nata else zero_nata) r f;

fun check_fmul_add A_ B_ mode x y z res =
  let
    val signP =
      (if equal_nata (sign A_ B_ x) (sign A_ B_ y) then zero_nata
        else one_nata);
    val infP = is_infinity A_ B_ x orelse is_infinity A_ B_ y;
  in
    (if is_nan A_ B_ x orelse (is_nan A_ B_ y orelse is_nan A_ B_ z)
      then is_nan A_ B_ res
      else (if is_infinity A_ B_ x andalso is_zero A_ B_ y orelse
                 (is_zero A_ B_ x andalso is_infinity A_ B_ y orelse
                   is_infinity A_ B_ z andalso
                     (infP andalso not (equal_nata signP (sign A_ B_ z))))
             then is_nan A_ B_ res
             else (if is_infinity A_ B_ z andalso
                        equal_nata (sign A_ B_ z) zero_nata orelse
                        infP andalso equal_nata signP zero_nata
                    then equal_float A_ B_ res (plus_infinity A_ B_)
                    else (if is_infinity A_ B_ z andalso
                               equal_nata (sign A_ B_ z) one_nata orelse
                               infP andalso equal_nata signP one_nata
                           then equal_float A_ B_ res
                                  (uminus_float A_ B_ (plus_infinity A_ B_))
                           else let
                                  val r1 =
                                    times_reala (valof A_ B_ x) (valof A_ B_ y);
                                  val r2 = valof A_ B_ z;
                                in
                                  check_fr A_ B_ mode
                                    (if equal_real r1 zero_reala andalso
  (equal_real r2 zero_reala andalso equal_nata signP (sign A_ B_ z))
                                      then equal_nata signP one_nata
                                      else equal_roundmode mode To_ninfinity)
                                    (plus_reala r1 r2) res
                                end))))
  end;

fun check_fmul_add32 x =
  check_fmul_add (len_bit0 (len_bit0 (len_bit0 len_num1)))
    (len_bit1 (len0_bit1 (len0_bit1 (len0_bit0 len0_num1)))) x;

fun check_fmul_add64 x =
  check_fmul_add (len_bit1 (len0_bit1 (len0_bit0 len0_num1)))
    (len_bit0 (len_bit0 (len_bit1 (len0_bit0 (len0_bit1 len0_num1))))) x;

end; (*struct FP_test_base*)
