(* Author: Maximilian Schäffeler *)

theory Code_Example
  imports Code_Policy_Iteration 
begin

section \<open>Code Equations for pmf\<close>
lemma [code abstype]: "embed_pmf (pmf P) = P"
  by (metis (no_types, lifting) td_pmf_embed_pmf type_definition_def)

lemmas [code_abbrev del] = pmf_integral_code_unfold

lemma [code_unfold]: 
  "measure_pmf.expectation P (f :: 'a :: enum \<Rightarrow> real) = (\<Sum>x \<in> UNIV. pmf P x * f x)"
  by (metis (no_types, lifting) UNIV_I finite_class.finite_UNIV integral_measure_pmf 
      real_scaleR_def sum.cong)

lemma [code]: "pmf (return_pmf x) = (\<lambda>y. indicat_real {y} x) " 
  by auto

lemma [code]: 
  "pmf (bind_pmf N f) = (\<lambda>i :: 'a. measure_pmf.expectation N (\<lambda>(x :: 'b ::enum). pmf (f x) i))" 
  using  Probability_Mass_Function.pmf_bind
  by fast

section \<open>Gridworld Example\<close>
(* 3 x 4 + 1 * Trap *)
type_synonym state_robot = "13"

definition "from_state x = (Rep x div 4, Rep x mod 4)"
definition "to_state x = (Abs (fst x * 4 + snd x) :: state_robot)"

(* up, right, down, left *)
type_synonym action_robot = 4

fun A_robot :: "state_robot \<Rightarrow> action_robot set" where
"A_robot pos = UNIV"

abbreviation "noise \<equiv> (0.2 :: real)"

lift_definition add_noise :: "action_robot \<Rightarrow> action_robot pmf" is "\<lambda>det rnd. (
  if det = rnd then 1 - noise else if det = rnd - 1 \<or> det = rnd + 1 then noise / 2 else 0)"
  apply (auto simp: nn_integral_count_space_finite )
  unfolding UNIV_4 using exhaust_4
  by auto

fun r_robot :: "(state_robot \<times> action_robot) \<Rightarrow> real" where
"r_robot (s,a) = (
  if from_state s = (2,3) then 1 else
  if from_state s = (1,3) then -1 else 
  if from_state s = (3,0) then 0 else
  0)"

fun K_robot :: "(state_robot \<times> action_robot) \<Rightarrow> state_robot pmf" where
"K_robot (loc, a) = 
  do {
  a \<leftarrow> add_noise a;
  let (y, x) = from_state loc;
  let (y', x') =
    (if a = 0 then (y + 1 , x)
      else if a = 1 then (y, x+1)
      else if a = 2 then (y-1, x)
      else if a = 3 then (y, x-1)
      else undefined);
   return_pmf (
      if (y,x) = (2,3) \<or> (y,x) = (1,3) \<or> (y,x) = (3,0) 
        then to_state (3,0)
      else if y' < 0 \<or> y' > 2 \<or> x' < 0 \<or> x' > 3 \<or> (y',x') = (1,1)
      then to_state (y, x)
        else to_state (y', x'))
  }"

definition "mdp_robot = (Mdpr (MDPR A_robot K_robot r_robot 0.9))"

fun pi_robot_n where
"pi_robot_n 0 d = (d, MDPR_typedef.policy_eval_arr mdp_robot d)" | 
"pi_robot_n (Suc n) d = pi_robot_n n (MDPR_typedef.policy_step_arr mdp_robot d)"

fun vi_robot_n where
"vi_robot_n (0 :: nat) v = (MDPR_typedef.find_policy_arr mdp_robot v, v)" |
"vi_robot_n (Suc n :: nat) v = vi_robot_n n (MDPR_typedef.\<L>_arr mdp_robot v)"

definition "vi_result_n n = 
  (let (d, v) = vi_robot_n n (fun_to_it 0) in
    (map Rep (IArray.list_of (Rep_iarray_type d)), IArray.list_of (Rep_iarray_type v)))"

definition "pi_result_n n =
  (let (d,v) = pi_robot_n n (fun_to_it 0) in
    (map Rep (IArray.list_of (Rep_iarray_type d)), IArray.list_of v))"

(*
value "vi_result_n 20"
value "pi_result_n 3"
*)

end