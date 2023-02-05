
structure FArray = struct
  datatype 'a Cell = Value of 'a Array.array | Upd of (int*'a*'a Cell Unsynchronized.ref);

  type 'a array = 'a Cell Unsynchronized.ref;

  fun array (size,v) = Unsynchronized.ref (Value (Array.array (size,v)));
  fun tabulate (size, f) = Unsynchronized.ref (Value (Array.tabulate(size, f)));
  fun fromList l = Unsynchronized.ref (Value (Array.fromList l));

  fun sub (Unsynchronized.ref (Value a), idx) = Array.sub (a,idx) |
      sub (Unsynchronized.ref (Upd (i,v,cr)),idx) =
        if i=idx then v
        else sub (cr,idx);

  fun length (Unsynchronized.ref (Value a)) = Array.length a |
      length (Unsynchronized.ref (Upd (i,v,cr))) = length cr;

  fun realize_aux (aref, v) =
    case aref of
      (Unsynchronized.ref (Value a)) => (
        let
          val len = Array.length a;
          val a' = Array.array (len,v);
        in
          Array.copy {src=a, dst=a', di=0};
          Unsynchronized.ref (Value a')
        end
      ) |
      (Unsynchronized.ref (Upd (i,v,cr))) => (
        let val res=realize_aux (cr,v) in
          case res of
            (Unsynchronized.ref (Value a)) => (Array.update (a,i,v); res)
        end
      );

  fun realize aref =
    case aref of
      (Unsynchronized.ref (Value _)) => aref |
      (Unsynchronized.ref (Upd (i,v,cr))) => realize_aux(aref,v);

  fun update (aref,idx,v) =
    case aref of
      (Unsynchronized.ref (Value a)) => (
        let val nref=Unsynchronized.ref (Value a) in
          aref := Upd (idx,Array.sub(a,idx),nref);
          Array.update (a,idx,v);
          nref
        end
      ) |
      (Unsynchronized.ref (Upd _)) =>
        let val ra = realize_aux(aref,v) in
          case ra of
            (Unsynchronized.ref (Value a)) => Array.update (a,idx,v);
          ra
        end
      ;


structure IsabelleMapping = struct
type 'a ArrayType = 'a array;

fun array_new (n:IntInf.int) (a:'a) = array (IntInf.toInt n, a);
fun array_of_list (xs:'a list) = fromList xs;

fun array_tabulate (n:IntInf.int) (f:IntInf.int -> 'a) = tabulate (IntInf.toInt n, f o IntInf.fromInt)

fun array_length (a:'a ArrayType) = IntInf.fromInt (length a);

fun array_get (a:'a ArrayType) (i:IntInf.int) = sub (a, IntInf.toInt i);

fun array_set (a:'a ArrayType) (i:IntInf.int) (e:'a) = update (a, IntInf.toInt i, e);

fun array_get_oo (d:'a) (a:'a ArrayType) (i:IntInf.int) =
  sub (a,IntInf.toInt i) handle Subscript => d

fun array_set_oo (d:(unit->'a ArrayType)) (a:'a ArrayType) (i:IntInf.int) (e:'a) =
  update (a, IntInf.toInt i, e) handle Subscript => d ()

end;
end;





structure STArray = struct

datatype 'a Cell = Invalid | Value of 'a array;

exception AccessedOldVersion;

type 'a starray = 'a Cell Unsynchronized.ref;

fun fromList l = Unsynchronized.ref (Value (Array.fromList l));
fun starray (size, v) = Unsynchronized.ref (Value (Array.array (size,v)));
fun tabulate (size, f) = Unsynchronized.ref (Value (Array.tabulate(size, f)));
fun sub (Unsynchronized.ref Invalid, idx) = raise AccessedOldVersion |
    sub (Unsynchronized.ref (Value a), idx) = Array.sub (a,idx);
fun update (aref,idx,v) =
  case aref of
    (Unsynchronized.ref Invalid) => raise AccessedOldVersion |
    (Unsynchronized.ref (Value a)) => (
      aref := Invalid;
      Array.update (a,idx,v);
      Unsynchronized.ref (Value a)
    );

fun length (Unsynchronized.ref Invalid) = raise AccessedOldVersion |
    length (Unsynchronized.ref (Value a)) = Array.length a


structure IsabelleMapping = struct
type 'a ArrayType = 'a starray;

fun starray_new (n:IntInf.int) (a:'a) = starray (IntInf.toInt n, a);
fun starray_of_list (xs:'a list) = fromList xs;

fun starray_tabulate (n:IntInf.int) (f:IntInf.int -> 'a) = tabulate (IntInf.toInt n, f o IntInf.fromInt)

fun starray_length (a:'a ArrayType) = IntInf.fromInt (length a);

fun starray_get (a:'a ArrayType) (i:IntInf.int) = sub (a, IntInf.toInt i);

fun starray_set (a:'a ArrayType) (i:IntInf.int) (e:'a) = update (a, IntInf.toInt i, e);

fun starray_get_oo (d:'a) (a:'a ArrayType) (i:IntInf.int) =
  sub (a,IntInf.toInt i) handle Subscript => d

fun starray_set_oo (d:(unit->'a ArrayType)) (a:'a ArrayType) (i:IntInf.int) (e:'a) =
  update (a, IntInf.toInt i, e) handle Subscript => d ()


end;

end;


structure PI_Code_Float : sig
  type nat
  val integer_of_nat : nat -> IntInf.int
  type 'a equal
  type 'a linorder
  type color
  type 'a divide
  val divide : 'a divide -> 'a -> 'a -> 'a
  datatype int = Int_of_integer of IntInf.int
  type num
  type rat
  type 'a tree
  type 'a vec
  datatype mdp =
    MDP of
      real * nat *
        ((nat * (real * (nat * real) list)) * color) tree Vector.vector
  type ('a, 'b) mapping
  type valid_MDP
  type 'a pmf
  val nat_of_integer : IntInf.int -> nat
  val update :
    'a equal * 'a linorder ->
      'a -> 'b -> (('a * 'b) * color) tree -> (('a * 'b) * color) tree
  val empty : ('a * color) tree
  val inorder : ('a * 'b) tree -> 'a list
  val d0 : valid_MDP -> ((nat * nat) * color) tree
  val ratreal : rat -> real
  val pI_code :
    valid_MDP -> ((nat * nat) * color) tree -> ((nat * nat) * color) tree
  val to_valid_MDP : mdp -> valid_MDP
  val pmf_of_list : 'a equal -> ('a * real) list -> 'a pmf
  val nat_pmf_of_list : (nat * real) list -> nat pmf
  val assoc_list_to_MDP :
    real -> ((nat * (real * (nat * real) list)) list) list -> valid_MDP
  val nat_map_from_list : (nat * 'a) list -> ((nat * 'a) * color) tree
end = struct

datatype nat = Nat of IntInf.int;

fun integer_of_nat (Nat x) = x;

fun equal_nata m n = (((integer_of_nat m) : IntInf.int) = (integer_of_nat n));

type 'a equal = {equal : 'a -> 'a -> bool};
val equal = #equal : 'a equal -> 'a -> 'a -> bool;

val equal_nat = {equal = equal_nata} : nat equal;

fun less_eq_nat m n = IntInf.<= (integer_of_nat m, integer_of_nat n);

type 'a ord = {less_eq : 'a -> 'a -> bool, less : 'a -> 'a -> bool};
val less_eq = #less_eq : 'a ord -> 'a -> 'a -> bool;
val less = #less : 'a ord -> 'a -> 'a -> bool;

fun less_nat m n = IntInf.< (integer_of_nat m, integer_of_nat n);

val ord_nat = {less_eq = less_eq_nat, less = less_nat} : nat ord;

type 'a preorder = {ord_preorder : 'a ord};
val ord_preorder = #ord_preorder : 'a preorder -> 'a ord;

type 'a order = {preorder_order : 'a preorder};
val preorder_order = #preorder_order : 'a order -> 'a preorder;

val preorder_nat = {ord_preorder = ord_nat} : nat preorder;

val order_nat = {preorder_order = preorder_nat} : nat order;

type 'a linorder = {order_linorder : 'a order};
val order_linorder = #order_linorder : 'a linorder -> 'a order;

val linorder_nat = {order_linorder = order_nat} : nat linorder;

fun eq A_ a b = equal A_ a b;

fun equal_lista A_ [] (x21 :: x22) = false
  | equal_lista A_ (x21 :: x22) [] = false
  | equal_lista A_ (x21 :: x22) (y21 :: y22) =
    eq A_ x21 y21 andalso equal_lista A_ x22 y22
  | equal_lista A_ [] [] = true;

fun equal_list A_ = {equal = equal_lista A_} : ('a list) equal;

datatype color = Red | Black;

fun equal_colora Red Black = false
  | equal_colora Black Red = false
  | equal_colora Black Black = true
  | equal_colora Red Red = true;

val equal_color = {equal = equal_colora} : color equal;

val equal_real =
  {equal = (fn a => fn b => Real.abs (a - b) < Math.pow (10.0, Real.~ 8.0))} :
  real equal;

type 'a times = {times : 'a -> 'a -> 'a};
val times = #times : 'a times -> 'a -> 'a -> 'a;

type 'a dvd = {times_dvd : 'a times};
val times_dvd = #times_dvd : 'a dvd -> 'a times;

val times_real = {times = (fn a => fn b => Real.* (a, b))} : real times;

val dvd_real = {times_dvd = times_real} : real dvd;

type 'a one = {one : 'a};
val one = #one : 'a one -> 'a;

val one_real = {one = 1.0} : real one;

type 'a uminus = {uminus : 'a -> 'a};
val uminus = #uminus : 'a uminus -> 'a -> 'a;

type 'a minus = {minus : 'a -> 'a -> 'a};
val minus = #minus : 'a minus -> 'a -> 'a -> 'a;

type 'a zero = {zero : 'a};
val zero = #zero : 'a zero -> 'a;

type 'a plus = {plus : 'a -> 'a -> 'a};
val plus = #plus : 'a plus -> 'a -> 'a -> 'a;

type 'a semigroup_add = {plus_semigroup_add : 'a plus};
val plus_semigroup_add = #plus_semigroup_add : 'a semigroup_add -> 'a plus;

type 'a cancel_semigroup_add =
  {semigroup_add_cancel_semigroup_add : 'a semigroup_add};
val semigroup_add_cancel_semigroup_add = #semigroup_add_cancel_semigroup_add :
  'a cancel_semigroup_add -> 'a semigroup_add;

type 'a ab_semigroup_add = {semigroup_add_ab_semigroup_add : 'a semigroup_add};
val semigroup_add_ab_semigroup_add = #semigroup_add_ab_semigroup_add :
  'a ab_semigroup_add -> 'a semigroup_add;

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

type 'a cancel_comm_monoid_add =
  {cancel_ab_semigroup_add_cancel_comm_monoid_add : 'a cancel_ab_semigroup_add,
    comm_monoid_add_cancel_comm_monoid_add : 'a comm_monoid_add};
val cancel_ab_semigroup_add_cancel_comm_monoid_add =
  #cancel_ab_semigroup_add_cancel_comm_monoid_add :
  'a cancel_comm_monoid_add -> 'a cancel_ab_semigroup_add;
val comm_monoid_add_cancel_comm_monoid_add =
  #comm_monoid_add_cancel_comm_monoid_add :
  'a cancel_comm_monoid_add -> 'a comm_monoid_add;

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

type 'a power = {one_power : 'a one, times_power : 'a times};
val one_power = #one_power : 'a power -> 'a one;
val times_power = #times_power : 'a power -> 'a times;

type 'a monoid_mult =
  {semigroup_mult_monoid_mult : 'a semigroup_mult,
    power_monoid_mult : 'a power};
val semigroup_mult_monoid_mult = #semigroup_mult_monoid_mult :
  'a monoid_mult -> 'a semigroup_mult;
val power_monoid_mult = #power_monoid_mult : 'a monoid_mult -> 'a power;

type 'a numeral =
  {one_numeral : 'a one, semigroup_add_numeral : 'a semigroup_add};
val one_numeral = #one_numeral : 'a numeral -> 'a one;
val semigroup_add_numeral = #semigroup_add_numeral :
  'a numeral -> 'a semigroup_add;

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

type 'a comm_semiring_1_cancel_crossproduct =
  {comm_semiring_1_cancel_comm_semiring_1_cancel_crossproduct :
     'a comm_semiring_1_cancel};
val comm_semiring_1_cancel_comm_semiring_1_cancel_crossproduct =
  #comm_semiring_1_cancel_comm_semiring_1_cancel_crossproduct :
  'a comm_semiring_1_cancel_crossproduct -> 'a comm_semiring_1_cancel;

type 'a semiring_no_zero_divisors =
  {semiring_0_semiring_no_zero_divisors : 'a semiring_0};
val semiring_0_semiring_no_zero_divisors = #semiring_0_semiring_no_zero_divisors
  : 'a semiring_no_zero_divisors -> 'a semiring_0;

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

type 'a semiring_no_zero_divisors_cancel =
  {semiring_no_zero_divisors_semiring_no_zero_divisors_cancel :
     'a semiring_no_zero_divisors};
val semiring_no_zero_divisors_semiring_no_zero_divisors_cancel =
  #semiring_no_zero_divisors_semiring_no_zero_divisors_cancel :
  'a semiring_no_zero_divisors_cancel -> 'a semiring_no_zero_divisors;

type 'a group_add =
  {cancel_semigroup_add_group_add : 'a cancel_semigroup_add,
    minus_group_add : 'a minus, monoid_add_group_add : 'a monoid_add,
    uminus_group_add : 'a uminus};
val cancel_semigroup_add_group_add = #cancel_semigroup_add_group_add :
  'a group_add -> 'a cancel_semigroup_add;
val minus_group_add = #minus_group_add : 'a group_add -> 'a minus;
val monoid_add_group_add = #monoid_add_group_add :
  'a group_add -> 'a monoid_add;
val uminus_group_add = #uminus_group_add : 'a group_add -> 'a uminus;

type 'a ab_group_add =
  {cancel_comm_monoid_add_ab_group_add : 'a cancel_comm_monoid_add,
    group_add_ab_group_add : 'a group_add};
val cancel_comm_monoid_add_ab_group_add = #cancel_comm_monoid_add_ab_group_add :
  'a ab_group_add -> 'a cancel_comm_monoid_add;
val group_add_ab_group_add = #group_add_ab_group_add :
  'a ab_group_add -> 'a group_add;

type 'a ring =
  {ab_group_add_ring : 'a ab_group_add,
    semiring_0_cancel_ring : 'a semiring_0_cancel};
val ab_group_add_ring = #ab_group_add_ring : 'a ring -> 'a ab_group_add;
val semiring_0_cancel_ring = #semiring_0_cancel_ring :
  'a ring -> 'a semiring_0_cancel;

type 'a ring_no_zero_divisors =
  {ring_ring_no_zero_divisors : 'a ring,
    semiring_no_zero_divisors_cancel_ring_no_zero_divisors :
      'a semiring_no_zero_divisors_cancel};
val ring_ring_no_zero_divisors = #ring_ring_no_zero_divisors :
  'a ring_no_zero_divisors -> 'a ring;
val semiring_no_zero_divisors_cancel_ring_no_zero_divisors =
  #semiring_no_zero_divisors_cancel_ring_no_zero_divisors :
  'a ring_no_zero_divisors -> 'a semiring_no_zero_divisors_cancel;

type 'a neg_numeral =
  {group_add_neg_numeral : 'a group_add, numeral_neg_numeral : 'a numeral};
val group_add_neg_numeral = #group_add_neg_numeral :
  'a neg_numeral -> 'a group_add;
val numeral_neg_numeral = #numeral_neg_numeral : 'a neg_numeral -> 'a numeral;

type 'a ring_1 =
  {neg_numeral_ring_1 : 'a neg_numeral, ring_ring_1 : 'a ring,
    semiring_1_cancel_ring_1 : 'a semiring_1_cancel};
val neg_numeral_ring_1 = #neg_numeral_ring_1 : 'a ring_1 -> 'a neg_numeral;
val ring_ring_1 = #ring_ring_1 : 'a ring_1 -> 'a ring;
val semiring_1_cancel_ring_1 = #semiring_1_cancel_ring_1 :
  'a ring_1 -> 'a semiring_1_cancel;

type 'a ring_1_no_zero_divisors =
  {ring_1_ring_1_no_zero_divisors : 'a ring_1,
    ring_no_zero_divisors_ring_1_no_zero_divisors : 'a ring_no_zero_divisors,
    semiring_1_no_zero_divisors_ring_1_no_zero_divisors :
      'a semiring_1_no_zero_divisors};
val ring_1_ring_1_no_zero_divisors = #ring_1_ring_1_no_zero_divisors :
  'a ring_1_no_zero_divisors -> 'a ring_1;
val ring_no_zero_divisors_ring_1_no_zero_divisors =
  #ring_no_zero_divisors_ring_1_no_zero_divisors :
  'a ring_1_no_zero_divisors -> 'a ring_no_zero_divisors;
val semiring_1_no_zero_divisors_ring_1_no_zero_divisors =
  #semiring_1_no_zero_divisors_ring_1_no_zero_divisors :
  'a ring_1_no_zero_divisors -> 'a semiring_1_no_zero_divisors;

type 'a comm_ring =
  {comm_semiring_0_cancel_comm_ring : 'a comm_semiring_0_cancel,
    ring_comm_ring : 'a ring};
val comm_semiring_0_cancel_comm_ring = #comm_semiring_0_cancel_comm_ring :
  'a comm_ring -> 'a comm_semiring_0_cancel;
val ring_comm_ring = #ring_comm_ring : 'a comm_ring -> 'a ring;

type 'a comm_ring_1 =
  {comm_ring_comm_ring_1 : 'a comm_ring,
    comm_semiring_1_cancel_comm_ring_1 : 'a comm_semiring_1_cancel,
    ring_1_comm_ring_1 : 'a ring_1};
val comm_ring_comm_ring_1 = #comm_ring_comm_ring_1 :
  'a comm_ring_1 -> 'a comm_ring;
val comm_semiring_1_cancel_comm_ring_1 = #comm_semiring_1_cancel_comm_ring_1 :
  'a comm_ring_1 -> 'a comm_semiring_1_cancel;
val ring_1_comm_ring_1 = #ring_1_comm_ring_1 : 'a comm_ring_1 -> 'a ring_1;

type 'a semidom =
  {comm_semiring_1_cancel_semidom : 'a comm_semiring_1_cancel,
    semiring_1_no_zero_divisors_semidom : 'a semiring_1_no_zero_divisors};
val comm_semiring_1_cancel_semidom = #comm_semiring_1_cancel_semidom :
  'a semidom -> 'a comm_semiring_1_cancel;
val semiring_1_no_zero_divisors_semidom = #semiring_1_no_zero_divisors_semidom :
  'a semidom -> 'a semiring_1_no_zero_divisors;

type 'a idom =
  {comm_ring_1_idom : 'a comm_ring_1,
    ring_1_no_zero_divisors_idom : 'a ring_1_no_zero_divisors,
    semidom_idom : 'a semidom,
    comm_semiring_1_cancel_crossproduct_idom :
      'a comm_semiring_1_cancel_crossproduct};
val comm_ring_1_idom = #comm_ring_1_idom : 'a idom -> 'a comm_ring_1;
val ring_1_no_zero_divisors_idom = #ring_1_no_zero_divisors_idom :
  'a idom -> 'a ring_1_no_zero_divisors;
val semidom_idom = #semidom_idom : 'a idom -> 'a semidom;
val comm_semiring_1_cancel_crossproduct_idom =
  #comm_semiring_1_cancel_crossproduct_idom :
  'a idom -> 'a comm_semiring_1_cancel_crossproduct;

val plus_real = {plus = (fn a => fn b => Real.+ (a, b))} : real plus;

val semigroup_add_real = {plus_semigroup_add = plus_real} : real semigroup_add;

val cancel_semigroup_add_real =
  {semigroup_add_cancel_semigroup_add = semigroup_add_real} :
  real cancel_semigroup_add;

val ab_semigroup_add_real =
  {semigroup_add_ab_semigroup_add = semigroup_add_real} : real ab_semigroup_add;

val minus_real = {minus = (fn a => fn b => Real.- (a, b))} : real minus;

val cancel_ab_semigroup_add_real =
  {ab_semigroup_add_cancel_ab_semigroup_add = ab_semigroup_add_real,
    cancel_semigroup_add_cancel_ab_semigroup_add = cancel_semigroup_add_real,
    minus_cancel_ab_semigroup_add = minus_real}
  : real cancel_ab_semigroup_add;

val zero_real = {zero = 0.0} : real zero;

val monoid_add_real =
  {semigroup_add_monoid_add = semigroup_add_real, zero_monoid_add = zero_real} :
  real monoid_add;

val comm_monoid_add_real =
  {ab_semigroup_add_comm_monoid_add = ab_semigroup_add_real,
    monoid_add_comm_monoid_add = monoid_add_real}
  : real comm_monoid_add;

val cancel_comm_monoid_add_real =
  {cancel_ab_semigroup_add_cancel_comm_monoid_add =
     cancel_ab_semigroup_add_real,
    comm_monoid_add_cancel_comm_monoid_add = comm_monoid_add_real}
  : real cancel_comm_monoid_add;

val mult_zero_real = {times_mult_zero = times_real, zero_mult_zero = zero_real}
  : real mult_zero;

val semigroup_mult_real = {times_semigroup_mult = times_real} :
  real semigroup_mult;

val semiring_real =
  {ab_semigroup_add_semiring = ab_semigroup_add_real,
    semigroup_mult_semiring = semigroup_mult_real}
  : real semiring;

val semiring_0_real =
  {comm_monoid_add_semiring_0 = comm_monoid_add_real,
    mult_zero_semiring_0 = mult_zero_real, semiring_semiring_0 = semiring_real}
  : real semiring_0;

val semiring_0_cancel_real =
  {cancel_comm_monoid_add_semiring_0_cancel = cancel_comm_monoid_add_real,
    semiring_0_semiring_0_cancel = semiring_0_real}
  : real semiring_0_cancel;

val ab_semigroup_mult_real =
  {semigroup_mult_ab_semigroup_mult = semigroup_mult_real} :
  real ab_semigroup_mult;

val comm_semiring_real =
  {ab_semigroup_mult_comm_semiring = ab_semigroup_mult_real,
    semiring_comm_semiring = semiring_real}
  : real comm_semiring;

val comm_semiring_0_real =
  {comm_semiring_comm_semiring_0 = comm_semiring_real,
    semiring_0_comm_semiring_0 = semiring_0_real}
  : real comm_semiring_0;

val comm_semiring_0_cancel_real =
  {comm_semiring_0_comm_semiring_0_cancel = comm_semiring_0_real,
    semiring_0_cancel_comm_semiring_0_cancel = semiring_0_cancel_real}
  : real comm_semiring_0_cancel;

val power_real = {one_power = one_real, times_power = times_real} : real power;

val monoid_mult_real =
  {semigroup_mult_monoid_mult = semigroup_mult_real,
    power_monoid_mult = power_real}
  : real monoid_mult;

val numeral_real =
  {one_numeral = one_real, semigroup_add_numeral = semigroup_add_real} :
  real numeral;

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

val semiring_1_cancel_real =
  {semiring_0_cancel_semiring_1_cancel = semiring_0_cancel_real,
    semiring_1_semiring_1_cancel = semiring_1_real}
  : real semiring_1_cancel;

val comm_monoid_mult_real =
  {ab_semigroup_mult_comm_monoid_mult = ab_semigroup_mult_real,
    monoid_mult_comm_monoid_mult = monoid_mult_real,
    dvd_comm_monoid_mult = dvd_real}
  : real comm_monoid_mult;

val comm_semiring_1_real =
  {comm_monoid_mult_comm_semiring_1 = comm_monoid_mult_real,
    comm_semiring_0_comm_semiring_1 = comm_semiring_0_real,
    semiring_1_comm_semiring_1 = semiring_1_real}
  : real comm_semiring_1;

val comm_semiring_1_cancel_real =
  {comm_semiring_0_cancel_comm_semiring_1_cancel = comm_semiring_0_cancel_real,
    comm_semiring_1_comm_semiring_1_cancel = comm_semiring_1_real,
    semiring_1_cancel_comm_semiring_1_cancel = semiring_1_cancel_real}
  : real comm_semiring_1_cancel;

val comm_semiring_1_cancel_crossproduct_real =
  {comm_semiring_1_cancel_comm_semiring_1_cancel_crossproduct =
     comm_semiring_1_cancel_real}
  : real comm_semiring_1_cancel_crossproduct;

val semiring_no_zero_divisors_real =
  {semiring_0_semiring_no_zero_divisors = semiring_0_real} :
  real semiring_no_zero_divisors;

val semiring_1_no_zero_divisors_real =
  {semiring_1_semiring_1_no_zero_divisors = semiring_1_real,
    semiring_no_zero_divisors_semiring_1_no_zero_divisors =
      semiring_no_zero_divisors_real}
  : real semiring_1_no_zero_divisors;

val semiring_no_zero_divisors_cancel_real =
  {semiring_no_zero_divisors_semiring_no_zero_divisors_cancel =
     semiring_no_zero_divisors_real}
  : real semiring_no_zero_divisors_cancel;

val uminus_real = {uminus = Real.~} : real uminus;

val group_add_real =
  {cancel_semigroup_add_group_add = cancel_semigroup_add_real,
    minus_group_add = minus_real, monoid_add_group_add = monoid_add_real,
    uminus_group_add = uminus_real}
  : real group_add;

val ab_group_add_real =
  {cancel_comm_monoid_add_ab_group_add = cancel_comm_monoid_add_real,
    group_add_ab_group_add = group_add_real}
  : real ab_group_add;

val ring_real =
  {ab_group_add_ring = ab_group_add_real,
    semiring_0_cancel_ring = semiring_0_cancel_real}
  : real ring;

val ring_no_zero_divisors_real =
  {ring_ring_no_zero_divisors = ring_real,
    semiring_no_zero_divisors_cancel_ring_no_zero_divisors =
      semiring_no_zero_divisors_cancel_real}
  : real ring_no_zero_divisors;

val neg_numeral_real =
  {group_add_neg_numeral = group_add_real, numeral_neg_numeral = numeral_real} :
  real neg_numeral;

val ring_1_real =
  {neg_numeral_ring_1 = neg_numeral_real, ring_ring_1 = ring_real,
    semiring_1_cancel_ring_1 = semiring_1_cancel_real}
  : real ring_1;

val ring_1_no_zero_divisors_real =
  {ring_1_ring_1_no_zero_divisors = ring_1_real,
    ring_no_zero_divisors_ring_1_no_zero_divisors = ring_no_zero_divisors_real,
    semiring_1_no_zero_divisors_ring_1_no_zero_divisors =
      semiring_1_no_zero_divisors_real}
  : real ring_1_no_zero_divisors;

val comm_ring_real =
  {comm_semiring_0_cancel_comm_ring = comm_semiring_0_cancel_real,
    ring_comm_ring = ring_real}
  : real comm_ring;

val comm_ring_1_real =
  {comm_ring_comm_ring_1 = comm_ring_real,
    comm_semiring_1_cancel_comm_ring_1 = comm_semiring_1_cancel_real,
    ring_1_comm_ring_1 = ring_1_real}
  : real comm_ring_1;

val semidom_real =
  {comm_semiring_1_cancel_semidom = comm_semiring_1_cancel_real,
    semiring_1_no_zero_divisors_semidom = semiring_1_no_zero_divisors_real}
  : real semidom;

val idom_real =
  {comm_ring_1_idom = comm_ring_1_real,
    ring_1_no_zero_divisors_idom = ring_1_no_zero_divisors_real,
    semidom_idom = semidom_real,
    comm_semiring_1_cancel_crossproduct_idom =
      comm_semiring_1_cancel_crossproduct_real}
  : real idom;

fun inverse_reala r = Real./ (1.0, r);

type 'a divide = {divide : 'a -> 'a -> 'a};
val divide = #divide : 'a divide -> 'a -> 'a -> 'a;

type 'a inverse = {divide_inverse : 'a divide, inverse : 'a -> 'a};
val divide_inverse = #divide_inverse : 'a inverse -> 'a divide;
val inverse = #inverse : 'a inverse -> 'a -> 'a;

type 'a division_ring =
  {inverse_division_ring : 'a inverse,
    ring_1_no_zero_divisors_division_ring : 'a ring_1_no_zero_divisors};
val inverse_division_ring = #inverse_division_ring :
  'a division_ring -> 'a inverse;
val ring_1_no_zero_divisors_division_ring =
  #ring_1_no_zero_divisors_division_ring :
  'a division_ring -> 'a ring_1_no_zero_divisors;

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

type 'a idom_divide =
  {idom_idom_divide : 'a idom, semidom_divide_idom_divide : 'a semidom_divide};
val idom_idom_divide = #idom_idom_divide : 'a idom_divide -> 'a idom;
val semidom_divide_idom_divide = #semidom_divide_idom_divide :
  'a idom_divide -> 'a semidom_divide;

type 'a field =
  {division_ring_field : 'a division_ring, idom_divide_field : 'a idom_divide};
val division_ring_field = #division_ring_field : 'a field -> 'a division_ring;
val idom_divide_field = #idom_divide_field : 'a field -> 'a idom_divide;

val divide_real = {divide = (fn a => fn b => Real./ (a, b))} : real divide;

val inverse_real = {divide_inverse = divide_real, inverse = inverse_reala} :
  real inverse;

val division_ring_real =
  {inverse_division_ring = inverse_real,
    ring_1_no_zero_divisors_division_ring = ring_1_no_zero_divisors_real}
  : real division_ring;

val semidom_divide_real =
  {divide_semidom_divide = divide_real, semidom_semidom_divide = semidom_real,
    semiring_no_zero_divisors_cancel_semidom_divide =
      semiring_no_zero_divisors_cancel_real}
  : real semidom_divide;

val idom_divide_real =
  {idom_idom_divide = idom_real,
    semidom_divide_idom_divide = semidom_divide_real}
  : real idom_divide;

val field_real =
  {division_ring_field = division_ring_real,
    idom_divide_field = idom_divide_real}
  : real field;

val ord_real =
  {less_eq = (fn a => fn b => Real.<= (a, b)),
    less = (fn a => fn b => Real.< (a, b))}
  : real ord;

fun equal_proda A_ B_ (x1, x2) (y1, y2) = eq A_ x1 y1 andalso eq B_ x2 y2;

fun equal_prod A_ B_ = {equal = equal_proda A_ B_} : ('a * 'b) equal;

val ord_integer =
  {less_eq = (fn a => fn b => IntInf.<= (a, b)),
    less = (fn a => fn b => IntInf.< (a, b))}
  : IntInf.int ord;

datatype int = Int_of_integer of IntInf.int;

datatype num = One | Bit0 of num | Bit1 of num;

datatype rat = Frct of (int * int);

datatype 'a tree = Leaf | Node of 'a tree * 'a * 'a tree;

datatype 'a mat_impl =
  Abs_mat_impl of (nat * (nat * ('a Vector.vector) Vector.vector));

datatype 'a mat = Mat_impl of 'a mat_impl;

datatype 'a vec_impl = Abs_vec_impl of (nat * 'a Vector.vector);

datatype 'a vec = Vec_impl of 'a vec_impl;

datatype cmp_val = LT | EQ | GT;

datatype mdp =
  MDP of
    real * nat *
      ((nat * (real * (nat * real) list)) * color) tree Vector.vector;

datatype ('a, 'b) mapping = Mapping of ('a * 'b) list;

datatype valid_MDP = Abs_Valid_MDP of mdp;

datatype 'a pmf = Pmf_of_mapping of ('a, real) mapping;

fun id x = (fn xa => xa) x;

fun cmp (A1_, A2_) x y =
  (if less ((ord_preorder o preorder_order o order_linorder) A2_) x y then LT
    else (if eq A1_ x y then EQ else GT));

fun plus_nat m n = Nat (IntInf.+ (integer_of_nat m, integer_of_nat n));

val one_nat : nat = Nat (1 : IntInf.int);

fun suc n = plus_nat n one_nat;

fun max A_ a b = (if less_eq A_ a b then b else a);

fun minus_nat m n =
  Nat (max ord_integer (0 : IntInf.int)
        (IntInf.- (integer_of_nat m, integer_of_nat n)));

val zero_nat : nat = Nat (0 : IntInf.int);

fun nth (x :: xs) n =
  (if equal_nata n zero_nat then x else nth xs (minus_nat n one_nat));

fun upt i j = (if less_nat i j then i :: upt (suc i) j else []);

fun fold f (x :: xs) s = fold f xs (f x s)
  | fold f [] s = s;

fun maps f [] = []
  | maps f (x :: xs) = f x @ maps f xs;

fun baliL (Node (Node (t1, (a, Red), t2), (b, Red), t3)) c t4 =
  Node (Node (t1, (a, Black), t2), (b, Red), Node (t3, (c, Black), t4))
  | baliL (Node (Leaf, (a, Red), Node (t2, (b, Red), t3))) c t4 =
    Node (Node (Leaf, (a, Black), t2), (b, Red), Node (t3, (c, Black), t4))
  | baliL (Node (Node (v, (vc, Black), vb), (a, Red), Node (t2, (b, Red), t3)))
    c t4 =
    Node (Node (Node (v, (vc, Black), vb), (a, Black), t2), (b, Red),
           Node (t3, (c, Black), t4))
  | baliL Leaf a t2 = Node (Leaf, (a, Black), t2)
  | baliL (Node (Leaf, (v, Black), vb)) a t2 =
    Node (Node (Leaf, (v, Black), vb), (a, Black), t2)
  | baliL (Node (Leaf, va, Leaf)) a t2 =
    Node (Node (Leaf, va, Leaf), (a, Black), t2)
  | baliL (Node (Leaf, va, Node (v, (ve, Black), vd))) a t2 =
    Node (Node (Leaf, va, Node (v, (ve, Black), vd)), (a, Black), t2)
  | baliL (Node (Node (vc, (vf, Black), ve), (v, Black), vb)) a t2 =
    Node (Node (Node (vc, (vf, Black), ve), (v, Black), vb), (a, Black), t2)
  | baliL (Node (Node (vc, (vf, Black), ve), va, Leaf)) a t2 =
    Node (Node (Node (vc, (vf, Black), ve), va, Leaf), (a, Black), t2)
  | baliL (Node (Node (vc, (vf, Black), ve), va, Node (v, (vh, Black), vg))) a
    t2 =
    Node (Node (Node (vc, (vf, Black), ve), va, Node (v, (vh, Black), vg)),
           (a, Black), t2)
  | baliL (Node (v, (vc, Black), vb)) a t2 =
    Node (Node (v, (vc, Black), vb), (a, Black), t2);

fun baliR t1 a (Node (t2, (b, Red), Node (t3, (c, Red), t4))) =
  Node (Node (t1, (a, Black), t2), (b, Red), Node (t3, (c, Black), t4))
  | baliR t1 a (Node (Node (t2, (b, Red), t3), (c, Red), Leaf)) =
    Node (Node (t1, (a, Black), t2), (b, Red), Node (t3, (c, Black), Leaf))
  | baliR t1 a
    (Node (Node (t2, (b, Red), t3), (c, Red), Node (v, (vc, Black), vb))) =
    Node (Node (t1, (a, Black), t2), (b, Red),
           Node (t3, (c, Black), Node (v, (vc, Black), vb)))
  | baliR t1 a Leaf = Node (t1, (a, Black), Leaf)
  | baliR t1 a (Node (v, (vc, Black), vb)) =
    Node (t1, (a, Black), Node (v, (vc, Black), vb))
  | baliR t1 a (Node (Leaf, va, Leaf)) =
    Node (t1, (a, Black), Node (Leaf, va, Leaf))
  | baliR t1 a (Node (Node (vb, (ve, Black), vd), va, Leaf)) =
    Node (t1, (a, Black), Node (Node (vb, (ve, Black), vd), va, Leaf))
  | baliR t1 a (Node (Leaf, va, Node (vc, (vf, Black), ve))) =
    Node (t1, (a, Black), Node (Leaf, va, Node (vc, (vf, Black), ve)))
  | baliR t1 a
    (Node (Node (vb, (vh, Black), vg), va, Node (vc, (vf, Black), ve))) =
    Node (t1, (a, Black),
           Node (Node (vb, (vh, Black), vg), va, Node (vc, (vf, Black), ve)));

fun paint c Leaf = Leaf
  | paint c (Node (l, (a, uu), r)) = Node (l, (a, c), r);

fun sub asa n =
  case (asa, integer_of_nat n) of (arr, i) => Vector.sub (arr, IntInf.toInt i);

fun foldl f a [] = a
  | foldl f a (x :: xs) = foldl f (f a x) xs;

fun foldr f [] = id
  | foldr f (x :: xs) = f x o foldr f xs;

fun nat_of_integer k = Nat (max ord_integer (0 : IntInf.int) k);

fun of_fun f n =
  case (integer_of_nat n,
         f o nat_of_integer) of (n, f) => Vector.tabulate (IntInf.toInt n, fn i => f ((IntInf.fromInt i)));

fun mat_of_fun xc xd xe =
  Abs_mat_impl (xc, (xd, of_fun (fn i => of_fun (fn j => xe (i, j)) xd) xc));

fun mat nr nc f = Mat_impl (mat_of_fun nr nc f);

fun rep_mat_impl (Abs_mat_impl x) = x;

fun index_mat_impl xa =
  let
    val (nr, (_, m)) = rep_mat_impl xa;
  in
    (fn (i, j) =>
      (if less_nat i nr then sub (sub m i) j
        else sub (Vector.fromList (nth [] (minus_nat i nr))) j))
  end;

fun index_mat (Mat_impl m) ij = index_mat_impl m ij;

fun snd (x1, x2) = x2;

fun fst (x1, x2) = x1;

fun dim_col_impl xa = fst (snd (rep_mat_impl xa));

fun dim_col (Mat_impl m) = dim_col_impl m;

fun vec_of_fun xb xc = Abs_vec_impl (xb, of_fun xc xb);

fun vec n f = Vec_impl (vec_of_fun n f);

fun row a i = vec (dim_col a) (fn j => index_mat a (i, j));

fun rep_Valid_MDP (Abs_Valid_MDP x) = x;

fun transitions (MDP (x1, x2, x3)) = x3;

fun states (MDP (x1, x2, x3)) = x2;

fun upd (A1_, A2_) x y Leaf = Node (Leaf, ((x, y), Red), Leaf)
  | upd (A1_, A2_) x y (Node (l, ((a, b), Black), r)) =
    (case cmp (A1_, A2_) x a of LT => baliL (upd (A1_, A2_) x y l) (a, b) r
      | EQ => Node (l, ((x, y), Black), r)
      | GT => baliR l (a, b) (upd (A1_, A2_) x y r))
  | upd (A1_, A2_) x y (Node (l, ((a, b), Red), r)) =
    (case cmp (A1_, A2_) x a
      of LT => Node (upd (A1_, A2_) x y l, ((a, b), Red), r)
      | EQ => Node (l, ((x, y), Red), r)
      | GT => Node (l, ((a, b), Red), upd (A1_, A2_) x y r));

fun update (A1_, A2_) x y t = paint Black (upd (A1_, A2_) x y t);

val empty : ('a * color) tree = Leaf;

fun from_list (A1_, A2_) =
  (fn f => foldl (fn acc => fn s => update (A1_, A2_) s (f s) acc) empty);

fun inorder Leaf = []
  | inorder (Node (l, (a, uu), r)) = inorder l @ a :: inorder r;

fun hd (x21 :: x22) = x21;

fun d0 mdp =
  from_list (equal_nat, linorder_nat)
    (fn s => fst (hd (inorder (sub (transitions (rep_Valid_MDP mdp)) s))))
    (upt zero_nat (states (rep_Valid_MDP mdp)));

val one_int : int = Int_of_integer (1 : IntInf.int);

fun of_int a = Frct (a, one_int);

fun filter p [] = []
  | filter p (x :: xs) = (if p x then x :: filter p xs else filter p xs);

fun member A_ [] y = false
  | member A_ (x :: xs) y = eq A_ x y orelse member A_ xs y;

fun color Leaf = Black
  | color (Node (uu, (uv, c), uw)) = c;

fun bheight Leaf = zero_nat
  | bheight (Node (l, (x, c), r)) =
    (if equal_colora c Black then plus_nat (bheight l) one_nat else bheight l);

fun invh Leaf = true
  | invh (Node (l, (x, c), r)) =
    equal_nata (bheight l) (bheight r) andalso (invh l andalso invh r);

fun invc Leaf = true
  | invc (Node (l, (a, c), r)) =
    (if equal_colora c Red
      then equal_colora (color l) Black andalso equal_colora (color r) Black
      else true) andalso
      (invc l andalso invc r);

fun rbt t = invc t andalso (invh t andalso equal_colora (color t) Black);

fun remdups A_ [] = []
  | remdups A_ (x :: xs) =
    (if member A_ xs x then remdups A_ xs else x :: remdups A_ xs);

fun integer_of_int (Int_of_integer k) = k;

fun real_of_int x = (Real.fromLargeInt o integer_of_int) x;

fun quotient_of (Frct x) = x;

fun ratreal r = let
                  val (p, q) = quotient_of r;
                in
                  Real./ (real_of_int p, real_of_int q)
                end;

fun length asa = nat_of_integer (IntInf.fromInt (Vector.length asa));

fun map f [] = []
  | map f (x21 :: x22) = f x21 :: map f x22;

fun lookup (A1_, A2_) Leaf x = NONE
  | lookup (A1_, A2_) (Node (l, ((a, b), uu), r)) x =
    (case cmp (A1_, A2_) x a of LT => lookup (A1_, A2_) l x | EQ => SOME b
      | GT => lookup (A1_, A2_) r x);

fun mDP_r mdp sa =
  (if less_eq_nat (states (rep_Valid_MDP mdp)) (fst sa) then 0.0
    else let
           val a_map = sub (transitions (rep_Valid_MDP mdp)) (fst sa);
         in
           (case lookup (equal_nat, linorder_nat) a_map (snd sa) of NONE => 0.0
             | SOME (r, _) => r)
         end);

fun list_of asa = map (sub asa) (upt zero_nat (length asa));

fun dim_row_impl xa = fst (rep_mat_impl xa);

fun dim_row (Mat_impl m) = dim_row_impl m;

fun rep_vec_impl (Abs_vec_impl x) = x;

fun dim_vec_impl xa = fst (rep_vec_impl xa);

fun dim_vec (Vec_impl v) = dim_vec_impl v;

fun map_mat f a = mat (dim_row a) (dim_col a) (fn ij => f (index_mat a ij));

fun one_mat (A1_, A2_) n =
  mat n n (fn (i, j) => (if equal_nata i j then one A1_ else zero A2_));

fun is_none (SOME x) = false
  | is_none NONE = true;

fun vec_index_impl xa = let
                          val (_, a) = rep_vec_impl xa;
                        in
                          sub a
                        end;

fun all_interval_nat p i j =
  less_eq_nat j i orelse p i andalso all_interval_nat p (suc i) j;

fun mat_of_row_fun_code xc xd xe =
  Abs_mat_impl
    (xc, (xd, let
                val m = of_fun (fn i => snd (rep_vec_impl (xe i))) xc;
              in
                (if all_interval_nat (fn i => equal_nata (length (sub m i)) xd)
                      zero_nat xc
                  then m
                  else (raise Fail "set_fold_cfc RBT_set: ccompare = None")
                         (fn _ =>
                           of_fun (fn i => of_fun (vec_index_impl (xe i)) xd)
                             xc))
              end));

fun vec_to_vec_impl (Vec_impl v) = v;

fun mat_of_row_fun nr nc f =
  Mat_impl (mat_of_row_fun_code nr nc (fn i => vec_to_vec_impl (f i)));

fun the (SOME x2) = x2;

fun d_lookup m x = the (lookup (equal_nat, linorder_nat) m x);

fun m_lookup (A1_, A2_) = (fn m => fn k => the (lookup (A1_, A2_) m k));

fun vec_index (Vec_impl v) i = vec_index_impl v i;

fun k_mat mdp d m =
  mat_of_row_fun (states (rep_Valid_MDP mdp)) (states (rep_Valid_MDP mdp))
    (fn i => m_lookup (equal_nat, linorder_nat) (vec_index m i) (d_lookup d i));

fun one_st (A1_, A2_) mdp = one_mat (A1_, A2_) (states (rep_Valid_MDP mdp));

fun gen_length n (x :: xs) = gen_length (suc n) xs
  | gen_length n [] = n;

fun map_filter f [] = []
  | map_filter f (x :: xs) =
    (case f x of NONE => map_filter f xs | SOME y => y :: map_filter f xs);

fun list_all p [] = true
  | list_all p (x :: xs) = p x andalso list_all p xs;

fun sorted_wrt p [] = true
  | sorted_wrt p (x :: ys) = list_all (p x) ys andalso sorted_wrt p ys;

fun m_invar A_ =
  (fn t =>
    rbt t andalso
      sorted_wrt (less ((ord_preorder o preorder_order o order_linorder) A_))
        (map fst (inorder t)));

fun sum_list A_ xs =
  foldr (plus ((plus_semigroup_add o semigroup_add_monoid_add) A_)) xs
    (zero (zero_monoid_add A_));

fun m_from_list (A1_, A2_) =
  foldl (fn acc => fn (k, v) => update (A1_, A2_) k v acc) empty;

fun transition_vecs mdp =
  vec (states (rep_Valid_MDP mdp))
    (fn s =>
      m_from_list (equal_nat, linorder_nat)
        (map (fn (a, (_, ps)) =>
               (a, vec (states (rep_Valid_MDP mdp))
                     (fn sa =>
                       sum_list monoid_add_real
                         (map (fn x =>
                                (if equal_nata (fst x) sa then snd x else 0.0))
                           ps))))
          (inorder (sub (transitions (rep_Valid_MDP mdp)) s))));

fun is_dec_det_code mdp d =
  equal_lista equal_nat (map fst (inorder d))
    (upt zero_nat (states (rep_Valid_MDP mdp))) andalso
    (m_invar linorder_nat d andalso
      all_interval_nat
        (fn s =>
          not (is_none
                (lookup (equal_nat, linorder_nat)
                  (sub (transitions (rep_Valid_MDP mdp)) s) (d_lookup d s))))
        zero_nat (states (rep_Valid_MDP mdp)));

fun least_arg_max_max_ne B_ f (x :: xs) =
  fold (fn y => fn (am, m) => let
                                val fy = f y;
                              in
                                (if less B_ m fy then (y, fy) else (am, m))
                              end)
    xs (x, f x)
  | least_arg_max_max_ne B_ a [] = (raise Fail "undefined");

fun starray_get a = STArray.IsabelleMapping.starray_get a o integer_of_nat;

fun disc (MDP (x1, x2, x3)) = x1;

fun l_a_code mdp rp v =
  let
    val (r, ps) = rp;
  in
    Real.+ (r, Real.* (disc (rep_Valid_MDP
                              mdp), foldl (fn acc => fn (s, p) =>
    Real.+ (Real.* (p, starray_get v s), acc))
                                      0.0 ps))
  end;

fun find_policy_state_code_aux mdp v s =
  least_arg_max_max_ne ord_real (fn (_, rsuccs) => l_a_code mdp rsuccs v)
    (inorder (sub (transitions (rep_Valid_MDP mdp)) s));

fun find_policy_state_code_auxa mdp v s =
  let
    val ((a, (_, _)), va) = find_policy_state_code_aux mdp v s;
  in
    (a, va)
  end;

fun a_lookup m x =
  (case lookup (equal_nat, linorder_nat) m x
    of NONE =>
      (raise Fail "MDP is missing action information")
        (fn _ => (raise Fail "undefined"))
    | SOME v => v);

fun pi_find_policy_state_code_aux mdp d v s =
  let
    val (da, va) = find_policy_state_code_auxa mdp v s;
  in
    (if Real.abs ((l_a_code mdp
                    (a_lookup (sub (transitions (rep_Valid_MDP mdp)) s) d)
                    v) - va) < Math.pow (10.0, Real.~ 8.0)
      then d else da)
  end;

fun pi_find_policy_code mdp d v =
  from_list (equal_nat, linorder_nat)
    (fn s => pi_find_policy_state_code_aux mdp (d_lookup d s) v s)
    (upt zero_nat (states (rep_Valid_MDP mdp)));

fun eliminate_entries_gen minus times v a i j =
  mat (dim_row a) (dim_col a)
    (fn (ia, ja) =>
      (if not (equal_nata ia i)
        then minus (index_mat a (ia, ja)) (times (v ia) (index_mat a (i, ja)))
        else index_mat a (ia, ja)));

fun list_update [] i y = []
  | list_update (x :: xs) i y =
    (if equal_nata i zero_nat then y :: xs
      else x :: list_update xs (minus_nat i one_nat) y);

fun mat_multrow_gen_impl xc xd xe xf =
  Abs_mat_impl let
                 val (nr, (nc, a)) = rep_mat_impl xf;
                 val ak = sub a xd;
                 val arows = list_of a;
                 val aka = Vector.fromList (map (xc xe) (list_of ak));
                 val aa = Vector.fromList (list_update arows xd aka);
               in
                 (nr, (nc, aa))
               end;

fun mat_multrow_gen mul k aa (Mat_impl a) =
  Mat_impl (mat_multrow_gen_impl mul k aa a);

fun mat_swaprows_impl xc xd xe =
  Abs_mat_impl
    let
      val (nr, (nc, a)) = rep_mat_impl xe;
    in
      (if less_nat xc nr andalso less_nat xd nr
        then let
               val ai = sub a xc;
               val aj = sub a xd;
               val arows = list_of a;
               val aa =
                 Vector.fromList (list_update (list_update arows xc aj) xd ai);
             in
               (nr, (nc, aa))
             end
        else (nr, (nc, a)))
    end;

fun mat_swaprows k l (Mat_impl a) =
  let
    val nr = dim_row_impl a;
  in
    (if less_nat l nr andalso less_nat k nr
      then Mat_impl (mat_swaprows_impl k l a)
      else (raise Fail "index out of bounds in mat_swaprows")
             (fn _ => mat_swaprows k l (Mat_impl a)))
  end;

fun gauss_jordan_main (A1_, A2_) a b i j =
  let
    val nr = dim_row a;
    val nc = dim_col a;
  in
    (if less_nat i nr andalso less_nat j nc
      then let
             val aij = index_mat a (i, j);
           in
             (if eq A2_ aij
                   (zero ((zero_mult_zero o mult_zero_semiring_0 o
                            semiring_0_semiring_1 o semiring_1_comm_semiring_1 o
                            comm_semiring_1_comm_semiring_1_cancel o
                            comm_semiring_1_cancel_semidom o semidom_idom o
                            idom_idom_divide o idom_divide_field)
                           A1_))
               then (case maps (fn ia =>
                                 (if not (eq A2_ (index_mat a (ia, j))
   (zero ((zero_mult_zero o mult_zero_semiring_0 o semiring_0_semiring_1 o
            semiring_1_comm_semiring_1 o
            comm_semiring_1_comm_semiring_1_cancel o
            comm_semiring_1_cancel_semidom o semidom_idom o idom_idom_divide o
            idom_divide_field)
           A1_)))
                                   then [ia] else []))
                            (upt (suc i) nr)
                      of [] => gauss_jordan_main (A1_, A2_) a b i (suc j)
                      | ia :: _ =>
                        gauss_jordan_main (A1_, A2_) (mat_swaprows i ia a)
                          (mat_swaprows i ia b) i j)
               else (if eq A2_ aij
                          (one ((one_numeral o numeral_neg_numeral o
                                  neg_numeral_ring_1 o ring_1_comm_ring_1 o
                                  comm_ring_1_idom o idom_idom_divide o
                                  idom_divide_field)
                                 A1_))
                      then let
                             val v = (fn ia => index_mat a (ia, j));
                           in
                             gauss_jordan_main (A1_, A2_)
                               (eliminate_entries_gen
                                 (minus
                                   ((minus_group_add o group_add_neg_numeral o
                                      neg_numeral_ring_1 o ring_1_comm_ring_1 o
                                      comm_ring_1_idom o idom_idom_divide o
                                      idom_divide_field)
                                     A1_))
                                 (times
                                   ((times_dvd o dvd_comm_monoid_mult o
                                      comm_monoid_mult_comm_semiring_1 o
                                      comm_semiring_1_comm_semiring_1_cancel o
                                      comm_semiring_1_cancel_semidom o
                                      semidom_idom o idom_idom_divide o
                                      idom_divide_field)
                                     A1_))
                                 v a i j)
                               (eliminate_entries_gen
                                 (minus
                                   ((minus_group_add o group_add_neg_numeral o
                                      neg_numeral_ring_1 o ring_1_comm_ring_1 o
                                      comm_ring_1_idom o idom_idom_divide o
                                      idom_divide_field)
                                     A1_))
                                 (times
                                   ((times_dvd o dvd_comm_monoid_mult o
                                      comm_monoid_mult_comm_semiring_1 o
                                      comm_semiring_1_comm_semiring_1_cancel o
                                      comm_semiring_1_cancel_semidom o
                                      semidom_idom o idom_idom_divide o
                                      idom_divide_field)
                                     A1_))
                                 v b i j)
                               (suc i) (suc j)
                           end
                      else let
                             val iaij =
                               inverse
                                 ((inverse_division_ring o division_ring_field)
                                   A1_)
                                 aij;
                             val aa =
                               mat_multrow_gen
                                 (times
                                   ((times_dvd o dvd_comm_monoid_mult o
                                      comm_monoid_mult_comm_semiring_1 o
                                      comm_semiring_1_comm_semiring_1_cancel o
                                      comm_semiring_1_cancel_semidom o
                                      semidom_idom o idom_idom_divide o
                                      idom_divide_field)
                                     A1_))
                                 i iaij a;
                             val ba =
                               mat_multrow_gen
                                 (times
                                   ((times_dvd o dvd_comm_monoid_mult o
                                      comm_monoid_mult_comm_semiring_1 o
                                      comm_semiring_1_comm_semiring_1_cancel o
                                      comm_semiring_1_cancel_semidom o
                                      semidom_idom o idom_idom_divide o
                                      idom_divide_field)
                                     A1_))
                                 i iaij b;
                             val v = (fn ia => index_mat aa (ia, j));
                           in
                             gauss_jordan_main (A1_, A2_)
                               (eliminate_entries_gen
                                 (minus
                                   ((minus_group_add o group_add_neg_numeral o
                                      neg_numeral_ring_1 o ring_1_comm_ring_1 o
                                      comm_ring_1_idom o idom_idom_divide o
                                      idom_divide_field)
                                     A1_))
                                 (times
                                   ((times_dvd o dvd_comm_monoid_mult o
                                      comm_monoid_mult_comm_semiring_1 o
                                      comm_semiring_1_comm_semiring_1_cancel o
                                      comm_semiring_1_cancel_semidom o
                                      semidom_idom o idom_idom_divide o
                                      idom_divide_field)
                                     A1_))
                                 v aa i j)
                               (eliminate_entries_gen
                                 (minus
                                   ((minus_group_add o group_add_neg_numeral o
                                      neg_numeral_ring_1 o ring_1_comm_ring_1 o
                                      comm_ring_1_idom o idom_idom_divide o
                                      idom_divide_field)
                                     A1_))
                                 (times
                                   ((times_dvd o dvd_comm_monoid_mult o
                                      comm_monoid_mult_comm_semiring_1 o
                                      comm_semiring_1_comm_semiring_1_cancel o
                                      comm_semiring_1_cancel_semidom o
                                      semidom_idom o idom_idom_divide o
                                      idom_divide_field)
                                     A1_))
                                 v ba i j)
                               (suc i) (suc j)
                           end))
           end
      else (a, b))
  end;

fun gauss_jordan (A1_, A2_) a b =
  gauss_jordan_main (A1_, A2_) a b zero_nat zero_nat;

fun minus_mat A_ a b =
  mat (dim_row b) (dim_col b)
    (fn ij => minus A_ (index_mat a ij) (index_mat b ij));

fun scalar_prod A_ v w =
  sum_list ((monoid_add_comm_monoid_add o comm_monoid_add_semiring_0) A_)
    (map (fn i =>
           times ((times_mult_zero o mult_zero_semiring_0) A_) (vec_index v i)
             (vec_index w i))
      (upt zero_nat (dim_vec w)));

fun mult_mat_vec A_ a v = vec (dim_row a) (fn i => scalar_prod A_ (row a i) v);

fun smult_mat A_ aa a = map_mat (times A_ aa) a;

fun policy_eval_code mdp d m =
  mult_mat_vec semiring_0_real
    (snd (gauss_jordan (field_real, equal_real)
           (minus_mat minus_real (one_st (one_real, zero_real) mdp)
             (smult_mat times_real (disc (rep_Valid_MDP mdp)) (k_mat mdp d m)))
           (one_st (one_real, zero_real) mdp)))
    (vec (states (rep_Valid_MDP mdp)) (fn i => mDP_r mdp (i, d_lookup d i)));

fun starray_tabulate n f =
  STArray.IsabelleMapping.starray_tabulate (integer_of_nat n)
    (f o nat_of_integer);

fun arr_tabulate x = (fn f => fn n => starray_tabulate n f) x;

fun policy_step_code mdp d m =
  let
    val v = policy_eval_code mdp d m;
  in
    pi_find_policy_code mdp d
      (arr_tabulate (vec_index v) (states (rep_Valid_MDP mdp)))
  end;

fun equal_option A_ NONE (SOME x2) = false
  | equal_option A_ (SOME x2) NONE = false
  | equal_option A_ (SOME x2) (SOME y2) = eq A_ x2 y2
  | equal_option A_ NONE NONE = true;

fun eq_policy mdp d1 d2 =
  all_interval_nat
    (fn x =>
      equal_option equal_nat (lookup (equal_nat, linorder_nat) d1 x)
        (lookup (equal_nat, linorder_nat) d2 x))
    zero_nat (states (rep_Valid_MDP mdp));

fun pI_code_aux mdp d m =
  let
    val da = policy_step_code mdp d m;
  in
    (if eq_policy mdp d da then d else pI_code_aux mdp da m)
  end;

fun pI_code mdp d0 =
  (if not (is_dec_det_code mdp d0) then d0
    else pI_code_aux mdp d0 (transition_vecs mdp));

fun tabulate ks f = Mapping (map (fn k => (k, f k)) ks);

fun equal_tree A_ Leaf (Node (x21, x22, x23)) = false
  | equal_tree A_ (Node (x21, x22, x23)) Leaf = false
  | equal_tree A_ (Node (x21, x22, x23)) (Node (y21, y22, y23)) =
    equal_tree A_ x21 y21 andalso (eq A_ x22 y22 andalso equal_tree A_ x23 y23)
  | equal_tree A_ Leaf Leaf = true;

fun is_MDP mdp =
  equal_nata (length (transitions mdp)) (states mdp) andalso
    (Real.<= (0.0, disc mdp) andalso Real.< (disc mdp, 1.0) andalso
      Vector.all
        (fn t =>
          rbt t andalso
            (sorted_wrt less_nat (map fst (inorder t)) andalso
              (not (equal_tree
                     (equal_prod
                       (equal_prod equal_nat
                         (equal_prod equal_real
                           (equal_list (equal_prod equal_nat equal_real))))
                       equal_color)
                     t empty) andalso
                list_all
                  (fn (_, (_, probs)) =>
                    Real.abs ((sum_list monoid_add_real
                                (map snd
                                  probs)) - 1.0) < Math.pow (10.0, Real.~ 8.0) andalso
                      list_all
                        (fn (s, p) =>
                          Real.<= (0.0, p) andalso less_nat s (states mdp))
                        probs)
                  (inorder t))))
        (transitions mdp));

val trivial_MDP : mdp = MDP (0.0, zero_nat, Vector.fromList []);

fun to_valid_MDP xa =
  Abs_Valid_MDP
    (if is_MDP xa then xa else (raise Fail "not an MDP") (fn _ => trivial_MDP));

fun mapping_of_pmf (Pmf_of_mapping x) = x;

fun power A_ a n =
  (if equal_nata n zero_nat then one (one_power A_)
    else times (times_power A_) a (power A_ a (minus_nat n one_nat)));

fun pmf_of_list_wf xs =
  list_all (fn z => Real.<= (0.0, snd z)) xs andalso
    Real.abs ((sum_list monoid_add_real
                (map snd xs)) - 1.0) < Math.pow (10.0, Real.~ 8.0);

fun pmf_of_list A_ xs =
  Pmf_of_mapping
    (if pmf_of_list_wf xs
      then let
             val xsa =
               filter
                 (fn z =>
                   not (Real.abs ((Real.* (snd
     z, power power_real (ratreal (of_int (Int_of_integer (10 : IntInf.int))))
          (nat_of_integer
            (8 : IntInf.int)))) - 0.0) < Math.pow (10.0, Real.~ 8.0)))
                 xs;
           in
             tabulate (remdups A_ (map fst xsa))
               (fn x =>
                 sum_list monoid_add_real
                   (map_filter
                     (fn xa =>
                       (if eq A_ (fst xa) x then SOME (snd xa) else NONE))
                     xsa))
           end
      else (raise Fail "Invalid list for pmf_of_list")
             (fn _ => mapping_of_pmf (pmf_of_list A_ xs)));

fun nat_pmf_of_list xs = pmf_of_list equal_nat xs;

fun size_list x = gen_length zero_nat x;

fun assoc_list_to_MDP d xs =
  to_valid_MDP
    (MDP (d, size_list xs,
           Vector.fromList
             (map (fn asa =>
                    foldr (fn (a, (r, p)) =>
                            update (equal_nat, linorder_nat) a (r, p))
                      asa empty)
               xs)));

fun nat_map_from_list xs =
  foldr (fn (a, b) => update (equal_nat, linorder_nat) a b) xs empty;

end; (*struct PI_Code_Float*)
