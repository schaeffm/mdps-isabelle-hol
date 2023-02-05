
fun mdp_list_to_assoc mdp_list = 
IntRedBlackMap.listItems (foldl (fn ((s,x), acc) => IntRedBlackMap.insertWith (List.@) (acc, IntInf.toInt s, [x])) IntRedBlackMap.empty mdp_list)

type nat = IntInf.int
type rat = (IntInf.int * IntInf.int)

type mdp_assoc_t = ((nat * (rat * ((nat * rat) list))) list) list
type ('nat, 'real) isa_mdp_assoc_t = (('nat * ('real * (('nat * 'real) list))) list) list

signature MDP_ISA =
sig
  type isa_nat
  type isa_real
  type isa_mdp

  val to_isa_real : rat -> isa_real
  val from_isa_real : isa_real -> real
  val isa_real_add : isa_real * isa_real -> isa_real
  val isa_real_sub : isa_real * isa_real -> isa_real
  val isa_one : isa_real
  val isa_zero : isa_real
  val isa_le: isa_real -> isa_real -> bool
  val nat_of_integer : IntInf.int -> isa_nat

  val isa_assoc_to_isa_MDP : isa_real * (isa_nat, isa_real) isa_mdp_assoc_t -> isa_mdp

  val exec : isa_mdp -> rat -> (nat * nat) list
  val exec_init : isa_mdp -> rat -> rat list -> (nat * nat) list
end

signature TO_ISA_MDP =
sig
  type isa_mdp
  type isa_nat
  type isa_real
  val assoc_to_isa_MDP : rat * mdp_assoc_t -> isa_mdp
  val convert_exec : rat * mdp_assoc_t * rat -> (nat * nat) list
  val convert_exec_init : rat list -> rat * mdp_assoc_t * rat -> (nat * nat) list
end

signature TO_ISA_MDP_CERT =
sig
  include TO_ISA_MDP
  val convert_exec_cert : rat list -> rat * mdp_assoc_t * rat -> bool
end


functor TO_ISA_MDP_FUNCTOR (MDP : MDP_ISA) : TO_ISA_MDP =
struct
open MDP

fun adjust_list_aux acc [(k,v)] = [(k, isa_real_sub(isa_one, acc))]
  | adjust_list_aux acc ((k,v)::xs) = (k, v)::adjust_list_aux (isa_real_add(acc, v)) xs

fun adjust_list xs = 
  let 
    (* val p = (foldl (fn ((_, x), acc) => from_isa_real (to_isa_real x) + acc) 0.0 xs) *)
    (* val _ = if Real.abs (Real.-(p, 1.0)) > 0.00001 then print (Real.toString p) else () *)
    val isa = map (fn (k,v) => (k, to_isa_real v)) xs

    val sorted = ListMergeSort.sort (fn ((k1,s), (k2, t)) => not (isa_le s t)) isa
  in
     adjust_list_aux isa_zero sorted
  end

fun assoc_to_isa_MDP (disc, mdp) =
  let
    fun g (r,p) = (to_isa_real r, (map (fn (k, v) => (nat_of_integer k, v)) (adjust_list p)))
    val _ = print "adjusting pmfs done\n"
    fun f acts = map (fn (k, v) => (nat_of_integer k, g v)) acts
    val mdp' = map f mdp
    val _ = print "handing mdp to isabelle\n"
    val mdp_isa = isa_assoc_to_isa_MDP (to_isa_real disc, mdp')
    val _ = print "conversion to isabelle done\n"
  in
    mdp_isa
  end

fun convert_exec (disc, mdp, eps) = exec (assoc_to_isa_MDP (disc,mdp)) eps
fun convert_exec_init init (disc, mdp, eps) = exec_init (assoc_to_isa_MDP (disc,mdp)) eps init

end

structure Float_MDP =
struct  
  type isa_real = real
  fun to_isa_real (x,y) = Real./ (Real.fromLargeInt x, Real.fromLargeInt y)
  val from_isa_real = id
  val isa_real_add = Real.+
  val isa_real_sub = Real.-
  val isa_one = 1.0
  val isa_zero = 0.0
  fun isa_le x y = Real.<=(x,y)
end

structure MDP_PIF : MDP_ISA =
struct
  open Float_MDP
  open PI_Code_Float

  type isa_nat = nat
  type isa_mdp = valid_MDP
  
  fun isa_assoc_to_isa_MDP (d, mdp) = assoc_list_to_MDP d mdp

  fun exec mdp _ = 
    let val res = inorder (pI_code mdp (d0 mdp))
    in
      map (fn (k,v) => (integer_of_nat k, integer_of_nat v)) res
    end

  fun exec_init mdp eps init = exit_fail "not implemented"

end

structure MDP_VIF : MDP_ISA =
struct
  open Float_MDP
  open VI_Code_Float

  type isa_nat = nat
  type isa_mdp = valid_MDP
  
  fun isa_assoc_to_isa_MDP (d, mdp) = assoc_list_to_MDP d mdp

  fun exec mdp eps = 
    let val res = inorder (vI_policy_code mdp (v0 mdp) (to_isa_real eps))
    in
      map (fn (k,v) => (integer_of_nat k, integer_of_nat v)) res
    end

  fun exec_init mdp eps init = 
    let val res = inorder (vI_policy_code mdp (v_map_from_list (map to_isa_real init)) (to_isa_real eps))
    in
      map (fn (k,v) => (integer_of_nat k, integer_of_nat v)) res
    end
end

structure MDP_GSF : MDP_ISA =
struct
  open Float_MDP
  open GS_Code_Float

  type isa_nat = nat
  type isa_mdp = valid_MDP
  
  fun isa_assoc_to_isa_MDP (d, mdp) = assoc_list_to_MDP d mdp

  fun exec mdp eps = 
    let val res = inorder (gS_policy_code mdp (v0 mdp) (to_isa_real eps))
    in
      map (fn (k,v) => (integer_of_nat k, integer_of_nat v)) res
    end

  fun exec_init mdp eps init = 
    let val res = inorder (gS_policy_code mdp (v_map_from_list (map to_isa_real init)) (to_isa_real eps))
    in
      map (fn (k,v) => (integer_of_nat k, integer_of_nat v)) res
    end
end

structure MDP_MPIF : MDP_ISA =
struct
  open Float_MDP
  open MPI_Code_Float

  type isa_nat = nat
  type isa_mdp = valid_MDP
  
  fun isa_assoc_to_isa_MDP (d, mdp) = assoc_list_to_MDP d mdp

  fun exec mdp eps = 
    let
        val res = inorder (mPI_code mdp (to_isa_real eps) (nat_of_integer 2))
    in
      map (fn (k,v) => (integer_of_nat k, integer_of_nat v)) res
    end
  
  fun exec_init mdp eps init = exit_fail "not implemented"

end

structure MDP_PIR : MDP_ISA =
struct
  open PI_Code_Rat
  type isa_real = real

  fun to_isa_real (n,d) = Ratreal (divide_rat (of_int (Int_of_integer n)) (of_int (Int_of_integer d)))
  fun from_isa_real (Ratreal r) = case quotient_of r of (Int_of_integer n, Int_of_integer d) => Real./ (Real.fromLargeInt n, Real.fromLargeInt d)
  val isa_le = less_eq_real

  val isa_one = Ratreal (of_int (Int_of_integer 1))
  val isa_zero = Ratreal (of_int (Int_of_integer 0))

  fun isa_real_add (x,y) = plus_reala x y
  fun isa_real_sub (x,y) = minus_reala x y

  type isa_nat = nat
  type isa_mdp = valid_MDP
  
  fun isa_assoc_to_isa_MDP (d, mdp) = assoc_list_to_MDP d mdp

  fun exec mdp _ =
    let val res = inorder (pI_code mdp (d0 mdp))
    in
      map (fn (k,v) => (integer_of_nat k, integer_of_nat v)) res
    end
  
  fun exec_init mdp eps init = exit_fail "not implemented"

end

structure MDP_VIR : MDP_ISA =
struct
  open VI_Code_Rat
  type isa_real = real
  fun to_isa_real (n,d) = Ratreal (divide_rat (of_int (Int_of_integer n)) (of_int (Int_of_integer d)))
  fun from_isa_real (Ratreal r) = case quotient_of r of (Int_of_integer n, Int_of_integer d) => Real./ (Real.fromLargeInt n, Real.fromLargeInt d)
  val isa_le = less_eq_real

  val isa_one = Ratreal (of_int (Int_of_integer 1))
  val isa_zero = Ratreal (of_int (Int_of_integer 0))

  fun isa_real_add (x,y) = plus_reala x y
  fun isa_real_sub (x,y) = minus_real x y

  type isa_nat = nat
  type isa_mdp = valid_MDP
  
  fun isa_assoc_to_isa_MDP (d, mdp) = assoc_list_to_MDP d mdp

  fun exec mdp eps = 
    let val res = inorder (vI_policy_code mdp (v0 mdp) (to_isa_real eps))
    in
      map (fn (k,v) => (integer_of_nat k, integer_of_nat v)) res
    end

  fun exec_init mdp eps init = 
    let val res = inorder (vI_policy_code mdp (v_map_from_list (map to_isa_real init)) (to_isa_real eps))
    in
      map (fn (k,v) => (integer_of_nat k, integer_of_nat v)) res
    end
end

structure MDP_GSR : MDP_ISA =
struct
  open GS_Code_Rat
  type isa_real = real
  fun to_isa_real (n,d) = Ratreal (divide_rat (of_int (Int_of_integer n)) (of_int (Int_of_integer d)))
  fun from_isa_real (Ratreal r) = case quotient_of r of (Int_of_integer n, Int_of_integer d) => Real./ (Real.fromLargeInt n, Real.fromLargeInt d)
  val isa_le = less_eq_real

  val isa_one = Ratreal (of_int (Int_of_integer 1))
  val isa_zero = Ratreal (of_int (Int_of_integer 0))

  fun isa_real_add (x,y) = plus_reala x y
  fun isa_real_sub (x,y) = minus_real x y

  type isa_nat = nat
  type isa_mdp = valid_MDP
  
  fun isa_assoc_to_isa_MDP (d, mdp) = assoc_list_to_MDP d mdp

  fun exec mdp eps = 
    let val res = inorder (gS_policy_code mdp (v0 mdp) (to_isa_real eps))
    in
      map (fn (k,v) => (integer_of_nat k, integer_of_nat v)) res
    end

  fun exec_init mdp eps init = 
    let val res = inorder (gS_policy_code mdp (v_map_from_list (map to_isa_real init)) (to_isa_real eps))
    in
      map (fn (k,v) => (integer_of_nat k, integer_of_nat v)) res
    end
end

structure MDP_MPIR : MDP_ISA =
struct
  open MPI_Code_Rat
  type isa_real = real
  fun to_isa_real (n,d) = Ratreal (divide_rat (of_int (Int_of_integer n)) (of_int (Int_of_integer d)))
  fun from_isa_real (Ratreal r) = case quotient_of r of (Int_of_integer n, Int_of_integer d) => Real./ (Real.fromLargeInt n, Real.fromLargeInt d)
  val isa_le = less_eq_real

  val isa_one = Ratreal (of_int (Int_of_integer 1))
  val isa_zero = Ratreal (of_int (Int_of_integer 0))

  fun isa_real_add (x,y) = plus_reala x y
  fun isa_real_sub (x,y) = minus_real x y

  type isa_nat = nat
  type isa_mdp = valid_MDP
  
  fun isa_assoc_to_isa_MDP (d, mdp) = assoc_list_to_MDP d mdp

  fun exec mdp eps = 
    let val res = inorder (mPI_code mdp (to_isa_real eps) (nat_of_integer 3))
    in
      map (fn (k,v) => (integer_of_nat k, integer_of_nat v)) res
    end

  fun exec_init mdp eps init = exit_fail "not implemented"

end

structure PIF = TO_ISA_MDP_FUNCTOR(MDP_PIF)
structure PIR = TO_ISA_MDP_FUNCTOR(MDP_PIR)

structure VIF = TO_ISA_MDP_FUNCTOR(MDP_VIF)
structure VIR = TO_ISA_MDP_FUNCTOR(MDP_VIR)

structure GSF = TO_ISA_MDP_FUNCTOR(MDP_GSF)
structure GSR = TO_ISA_MDP_FUNCTOR(MDP_GSR)

structure MPIF = TO_ISA_MDP_FUNCTOR(MDP_MPIF)
structure MPIR = TO_ISA_MDP_FUNCTOR(MDP_MPIR)
