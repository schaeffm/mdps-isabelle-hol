
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


structure MPI_Code_Float : sig
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
  datatype mdp =
    MDP of
      real * nat *
        ((nat * (real * (nat * real) list)) * color) tree Vector.vector
  type ('a, 'b) mapping
  type valid_MDP
  type 'a pmf
  val ratreal : rat -> real
  val nat_of_integer : IntInf.int -> nat
  val empty : ('a * color) tree
  val inorder : ('a * 'b) tree -> 'a list
  val update :
    'a equal * 'a linorder ->
      'a -> 'b -> (('a * 'b) * color) tree -> (('a * 'b) * color) tree
  val v0_code : valid_MDP -> real STArray.IsabelleMapping.ArrayType
  val mPI_code : valid_MDP -> real -> nat -> ((nat * nat) * color) tree
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

type 'a one = {one : 'a};
val one = #one : 'a one -> 'a;

val one_real = {one = 1.0} : real one;

type 'a plus = {plus : 'a -> 'a -> 'a};
val plus = #plus : 'a plus -> 'a -> 'a -> 'a;

val plus_real = {plus = (fn a => fn b => Real.+ (a, b))} : real plus;

type 'a zero = {zero : 'a};
val zero = #zero : 'a zero -> 'a;

val zero_real = {zero = 0.0} : real zero;

type 'a times = {times : 'a -> 'a -> 'a};
val times = #times : 'a times -> 'a -> 'a -> 'a;

type 'a power = {one_power : 'a one, times_power : 'a times};
val one_power = #one_power : 'a power -> 'a one;
val times_power = #times_power : 'a power -> 'a times;

val times_real = {times = (fn a => fn b => Real.* (a, b))} : real times;

val power_real = {one_power = one_real, times_power = times_real} : real power;

val ord_real =
  {less_eq = (fn a => fn b => Real.<= (a, b)),
    less = (fn a => fn b => Real.< (a, b))}
  : real ord;

val preorder_real = {ord_preorder = ord_real} : real preorder;

val order_real = {preorder_order = preorder_real} : real order;

type 'a semigroup_add = {plus_semigroup_add : 'a plus};
val plus_semigroup_add = #plus_semigroup_add : 'a semigroup_add -> 'a plus;

type 'a monoid_add =
  {semigroup_add_monoid_add : 'a semigroup_add, zero_monoid_add : 'a zero};
val semigroup_add_monoid_add = #semigroup_add_monoid_add :
  'a monoid_add -> 'a semigroup_add;
val zero_monoid_add = #zero_monoid_add : 'a monoid_add -> 'a zero;

val semigroup_add_real = {plus_semigroup_add = plus_real} : real semigroup_add;

val monoid_add_real =
  {semigroup_add_monoid_add = semigroup_add_real, zero_monoid_add = zero_real} :
  real monoid_add;

val linorder_real = {order_linorder = order_real} : real linorder;

fun equal_proda A_ B_ (x1, x2) (y1, y2) = eq A_ x1 y1 andalso eq B_ x2 y2;

fun equal_prod A_ B_ = {equal = equal_proda A_ B_} : ('a * 'b) equal;

val ord_integer =
  {less_eq = (fn a => fn b => IntInf.<= (a, b)),
    less = (fn a => fn b => IntInf.< (a, b))}
  : IntInf.int ord;

type 'a divide = {divide : 'a -> 'a -> 'a};
val divide = #divide : 'a divide -> 'a -> 'a -> 'a;

datatype int = Int_of_integer of IntInf.int;

datatype num = One | Bit0 of num | Bit1 of num;

datatype rat = Frct of (int * int);

datatype 'a set = Set of 'a list | Coset of 'a list;

datatype 'a tree = Leaf | Node of 'a tree * 'a * 'a tree;

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

fun upt i j = (if less_nat i j then i :: upt (suc i) j else []);

fun fold f (x :: xs) s = fold f xs (f x s)
  | fold f [] s = s;

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

fun map f [] = []
  | map f (x21 :: x22) = f x21 :: map f x22;

fun image f (Set xs) = Set (map f xs);

fun sub asa n =
  case (asa, integer_of_nat n) of (arr, i) => Vector.sub (arr, IntInf.toInt i);

fun foldl f a [] = a
  | foldl f a (x :: xs) = foldl f (f a x) xs;

fun foldr f [] = id
  | foldr f (x :: xs) = f x o foldr f xs;

fun max A_ a b = (if less_eq A_ a b then b else a);

fun minus_nat m n =
  Nat (max ord_integer (0 : IntInf.int)
        (IntInf.- (integer_of_nat m, integer_of_nat n)));

val zero_nat : nat = Nat (0 : IntInf.int);

fun funpow n f =
  (if equal_nata n zero_nat then id else f o funpow (minus_nat n one_nat) f);

val one_int : int = Int_of_integer (1 : IntInf.int);

fun of_int a = Frct (a, one_int);

fun filter p [] = []
  | filter p (x :: xs) = (if p x then x :: filter p xs else filter p xs);

fun member A_ [] y = false
  | member A_ (x :: xs) y = eq A_ x y orelse member A_ xs y;

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

fun hd (x21 :: x22) = x21;

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

fun nat_of_integer k = Nat (max ord_integer (0 : IntInf.int) k);

fun length asa = nat_of_integer (IntInf.fromInt (Vector.length asa));

val empty : ('a * color) tree = Leaf;

fun inorder Leaf = []
  | inorder (Node (l, (a, uu), r)) = inorder l @ a :: inorder r;

fun lookup (A1_, A2_) Leaf x = NONE
  | lookup (A1_, A2_) (Node (l, ((a, b), uu), r)) x =
    (case cmp (A1_, A2_) x a of LT => lookup (A1_, A2_) l x | EQ => SOME b
      | GT => lookup (A1_, A2_) r x);

fun update (A1_, A2_) x y t = paint Black (upd (A1_, A2_) x y t);

fun gen_length n (x :: xs) = gen_length (suc n) xs
  | gen_length n [] = n;

fun map_filter f [] = []
  | map_filter f (x :: xs) =
    (case f x of NONE => map_filter f xs | SOME y => y :: map_filter f xs);

fun list_all p [] = true
  | list_all p (x :: xs) = p x andalso list_all p xs;

fun sorted_wrt p [] = true
  | sorted_wrt p (x :: ys) = list_all (p x) ys andalso sorted_wrt p ys;

fun rep_Valid_MDP (Abs_Valid_MDP x) = x;

fun transitions (MDP (x1, x2, x3)) = x3;

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

fun starray_tabulate n f =
  STArray.IsabelleMapping.starray_tabulate (integer_of_nat n)
    (f o nat_of_integer);

fun arr_tabulate x = (fn f => fn n => starray_tabulate n f) x;

fun states (MDP (x1, x2, x3)) = x2;

fun the (SOME x2) = x2;

fun d_lookup m x = the (lookup (equal_nat, linorder_nat) m x);

fun a_lookup m x =
  (case lookup (equal_nat, linorder_nat) m x
    of NONE =>
      (raise Fail "MDP is missing action information")
        (fn _ => (raise Fail "undefined"))
    | SOME v => v);

fun l_code mdp d v =
  arr_tabulate
    (fn s =>
      l_a_code mdp
        (a_lookup (sub (transitions (rep_Valid_MDP mdp)) s) (d_lookup d s)) v)
    (states (rep_Valid_MDP mdp));

fun fst (x1, x2) = x1;

fun from_list (A1_, A2_) =
  (fn f => foldl (fn acc => fn s => update (A1_, A2_) s (f s) acc) empty);

fun d0_code mdp =
  from_list (equal_nat, linorder_nat)
    (fn s => fst (hd (inorder (sub (transitions (rep_Valid_MDP mdp)) s))))
    (upt zero_nat (states (rep_Valid_MDP mdp)));

fun min A_ a b = (if less_eq A_ a b then a else b);

fun mina A_ (Set (x :: xs)) =
  fold (min ((ord_preorder o preorder_order o order_linorder) A_)) xs x;

fun r_min_code mdp =
  min ord_real 0.0
    (mina linorder_real
      (image
        (fn s =>
          mina linorder_real
            (image (fn (_, (r, _)) => r)
              (Set (inorder (sub (transitions (rep_Valid_MDP mdp)) s)))))
        (Set (upt zero_nat (states (rep_Valid_MDP mdp))))));

fun v0_code mdp =
  arr_tabulate
    (fn _ => Real./ (r_min_code mdp, Real.- (1.0, disc (rep_Valid_MDP mdp))))
    (states (rep_Valid_MDP mdp));

fun tabulate ks f = Mapping (map (fn k => (k, f k)) ks);

fun sum_list A_ xs =
  foldr (plus ((plus_semigroup_add o semigroup_add_monoid_add) A_)) xs
    (zero (zero_monoid_add A_));

fun equal_tree A_ Leaf (Node (x21, x22, x23)) = false
  | equal_tree A_ (Node (x21, x22, x23)) Leaf = false
  | equal_tree A_ (Node (x21, x22, x23)) (Node (y21, y22, y23)) =
    equal_tree A_ x21 y21 andalso (eq A_ x22 y22 andalso equal_tree A_ x23 y23)
  | equal_tree A_ Leaf Leaf = true;

fun snd (x1, x2) = x2;

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

fun least_arg_max_max_ne B_ f (x :: xs) =
  fold (fn y => fn (am, m) => let
                                val fy = f y;
                              in
                                (if less B_ m fy then (y, fy) else (am, m))
                              end)
    xs (x, f x)
  | least_arg_max_max_ne B_ a [] = (raise Fail "undefined");

fun find_policy_state_code_aux mdp v s =
  least_arg_max_max_ne ord_real (fn (_, rsuccs) => l_a_code mdp rsuccs v)
    (inorder (sub (transitions (rep_Valid_MDP mdp)) s));

fun find_policy_state_code_auxa mdp v s =
  let
    val ((a, (_, _)), va) = find_policy_state_code_aux mdp v s;
  in
    (a, va)
  end;

fun starray_set a = STArray.IsabelleMapping.starray_set a o integer_of_nat;

fun find_policy_L_code mdp v =
  fold (fn s => fn (d, va) =>
         let
           val (ds, vs) = find_policy_state_code_auxa mdp v s;
         in
           (update (equal_nat, linorder_nat) s ds d, starray_set va s vs)
         end)
    (upt zero_nat (states (rep_Valid_MDP mdp)))
    (empty, arr_tabulate (fn _ => 0.0) (states (rep_Valid_MDP mdp)));

fun abs_real a = (if Real.< (a, 0.0) then Real.~ a else a);

fun all_interval_nat p i j =
  less_eq_nat j i orelse p i andalso all_interval_nat p (suc i) j;

fun check_dist mdp va v eps =
  let
    val m =
      Real./ (Real.* (eps, Real.- (1.0, disc
  (rep_Valid_MDP
    mdp))), Real.* (ratreal
                      (of_int
                        (Int_of_integer
                          (2 : IntInf.int))), disc (rep_Valid_MDP mdp)));
  in
    all_interval_nat
      (fn s =>
        Real.< (abs_real (Real.- (starray_get va s, starray_get v s)), m))
      zero_nat (states (rep_Valid_MDP mdp))
  end;

fun l_pow_code mdp v d m = funpow m (l_code mdp d) v;

fun mpi_partial_code mdp eps d v m =
  let
    val (da, va) = find_policy_L_code mdp v;
  in
    (if Real.abs ((disc (rep_Valid_MDP
                          mdp)) - 0.0) < Math.pow (10.0, Real.~ 8.0) orelse
          check_dist mdp v va eps
      then (da, v) else mpi_partial_code mdp eps da (l_pow_code mdp va da m) m)
  end;

fun mPI_code mdp eps m =
  (if Real.<= (eps, 0.0) then (raise Fail "undefined")
    else let
           val (d, _) = mpi_partial_code mdp eps (d0_code mdp) (v0_code mdp) m;
         in
           d
         end);

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

end; (*struct MPI_Code_Float*)
