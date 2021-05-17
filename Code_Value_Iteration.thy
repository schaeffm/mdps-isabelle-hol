(* Author: Maximilian Schäffeler *)
theory Code_Value_Iteration
  imports MDPR_disc "HOL-Library.IArray"
begin

section \<open>Fix code generation for sets\<close>
lemma member_code[code del]: "x \<in> List.coset xs \<longleftrightarrow> \<not> List.member xs x"
  by (auto simp: in_set_member)

definition "bfun_to_iarray (f :: 'c::{mod_type} \<Rightarrow>\<^sub>b 'b::metric_space) = 
  IArray.of_fun (\<lambda>i. f (from_nat i)) (CARD('c))" 

lift_definition bfun_fin :: "('a::{mod_type} \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow>\<^sub>b 'b::metric_space" is "id"
  by (auto simp: bfun_def)

typedef ('s :: mod_type, 'a) iarray_type = "{arr :: 'a iarray. IArray.length arr = CARD('s)}"
  apply (auto simp:)
  apply (intro exI[of _ "IArray (SOME xs. length xs = CARD('s))"])
  apply auto
  by (metis (mono_tags, lifting) Ex_list_of_length verit_sko_ex')

definition "it_nth (arr :: ('s, 'a) iarray_type) (s :: 's :: mod_type) = 
  IArray.sub (Rep_iarray_type arr) (to_nat s)"

definition "iarray_to_bfun arr = bfun_fin (\<lambda>i. IArray.sub arr (to_nat i))"

setup_lifting type_definition_iarray_type

lift_definition fun_to_it :: "('s \<Rightarrow> 'a) \<Rightarrow> ('s::mod_type, 'a) iarray_type" is 
  "\<lambda>f. IArray.of_fun (\<lambda>i. f (from_nat i)) (CARD('s))"
  by auto

lemma "iarray_to_bfun (bfun_to_iarray f) = f"
  unfolding iarray_to_bfun_def bfun_to_iarray_def
  apply (intro bfun_eqI)
  apply (auto simp: bfun_fin.rep_eq )
  apply (subst nth_map)
   apply auto
   apply (simp add: to_nat_less_card )
  apply (subst nth_upt)
   apply auto
  by (simp add: to_nat_less_card )

lemma length_it[simp]: 
  "length (IArray.list_of (Rep_iarray_type (d :: ('c::mod_type, 'd) iarray_type))) = CARD('c)"
  using Rep_iarray_type by auto

lemma fun_to_it_inverse [simp]: "fun_to_it (it_nth d) = (d :: ('c::mod_type, 'd) iarray_type)"
  unfolding it_nth_def fun_to_it_def
  apply auto
  apply (subst map_cong[where ys = " [0..<CARD('c)]", where ?g = "(\<lambda>i. IArray.list_of _ ! i)"])
    apply auto
   apply (simp add: to_nat_from_nat_id)
  apply (subst length_it[symmetric])
  apply (subst map_nth)
  by (metis Rep_iarray_type_inverse iarray.exhaust list_of.simps)

lemma fun_to_it_inverse' [simp]: "it_nth (fun_to_it d) = d"
  unfolding it_nth_def fun_to_it_def
  apply auto
  apply (subst Abs_iarray_type_inverse)
   apply auto
  apply (subst nth_map)
   apply auto
   apply (simp add: to_nat_less_card)
  apply (subst nth_upt)
   apply auto
  by (simp add: to_nat_less_card)


lemma dist_bfun_code [code]: 
  "dist (x :: 's :: enum \<Rightarrow>\<^sub>b 'b :: {real_normed_vector}) y = (MAX a. dist (x a) (y a))"
  by (simp add: cSup_eq_Max dist_bfun.rep_eq Max_def)

datatype ('s :: enum, 'a :: enum) MDPR = 
  MDPR "('s \<Rightarrow> ('a set))" "(('s \<times> 'a) \<Rightarrow> 's pmf)" "('s \<times> 'a \<Rightarrow> real)" "real"

typedef ('s, 'a) mdpr = 
  "{x | x A K r l. x = (MDPR A K r l :: ('s :: enum, 'a :: enum) MDPR) \<and> MDP_reward A r l}"
  unfolding MDP_reward_def discrete_MDP_def MDP_reward_axioms_def
  apply auto
  by (meson Bounded_Functions.bounded_apply_bfun le_numeral_extra(3) less_numeral_extra(1))

setup_lifting type_definition_mdpr

lift_definition Mdpr :: "('s :: enum, 'a :: enum) MDPR \<Rightarrow> ('s, 'a) mdpr" is
  "\<lambda>m. case m of (MDPR A K r l) \<Rightarrow> 
  if MDP_reward A r l 
  then MDPR A K r l 
  else MDPR (\<lambda>s. UNIV) K (\<lambda>_. 0) 0"                   
  by (auto split: MDPR.splits simp: MDP_reward_def discrete_MDP_def MDP_reward_axioms_def)

lemma MDP_reward_code [code]: 
  fixes A :: "('s :: enum) \<Rightarrow> ('a :: enum) set"
  shows "MDP_reward A r l \<equiv> (\<forall>s. A s \<noteq> {}) \<and> 0 \<le> l \<and> l < 1"
  unfolding MDP_reward_def MDP_reward_axioms_def discrete_MDP_def
  apply (subst finite_imp_bounded)
  by auto

locale MDPR_typedef =
  fixes m :: "('s :: {enum, mod_type}, 'a :: {enum, wellorder}) mdpr"
begin


abbreviation "A \<equiv> (case Rep_mdpr m of MDPR A' K' r' l' \<Rightarrow> A')"
abbreviation "K \<equiv> (case Rep_mdpr m of MDPR A' K' r' l' \<Rightarrow> K')"
abbreviation "r \<equiv> (case Rep_mdpr m of MDPR A' K' r' l' \<Rightarrow> r')"
abbreviation "l \<equiv> (case Rep_mdpr m of MDPR A' K' r' l' \<Rightarrow> l')"

sublocale mdp: MDP_ord A K r l
  unfolding MDP_ord_def MDP_finite_type_def
  by (fastforce simp: Abs_mdpr_inverse intro: Abs_mdpr_cases[of "m"])

definition "value_iteration \<equiv> mdp.value_iteration"
definition "\<L> \<equiv> mdp.\<L>"
definition "K0 \<equiv> mdp.K0"
definition "find_policy \<equiv> mdp.find_policy'"
definition "vi_policy \<equiv> mdp.vi_policy'"

lemmas [simp] =
  value_iteration_def
  \<L>_def
  K0_def
  
lemma code_K0 [simp]: "K0 d S0 = S0 \<bind> (\<lambda>s. d s \<bind> (\<lambda>a. return_pmf (s, a)))"
  by (auto simp: mdp.K0_def)

lemma code_\<L> [simp]: "\<L> v s = (MAX a \<in> A s. r (s, a) +  l * measure_pmf.expectation (K (s,a)) v)"
  by (simp add: mdp.\<L>_eq_SUP_det mdp.SUP_step_det_eq cSup_eq_Max mdp.A_ne)


lift_definition \<L>\<^sub>b :: "('s \<Rightarrow>\<^sub>b real) \<Rightarrow> ('s \<Rightarrow>\<^sub>b real)" is "\<lambda>v s. \<L> v s"
  using \<L>_def mdp.\<L>_bfun by presburger

definition "\<L>_arr v = fun_to_it (\<L>\<^sub>b (bfun_fin (it_nth v)))"

lemma \<L>_arr_code: "\<L>_arr v =
  fun_to_it (\<lambda>s. (MAX a \<in> A s. r (s, a) + l * measure_pmf.expectation (K (s,a)) (it_nth v)))"
  by (auto simp add: \<L>\<^sub>b.rep_eq bfun_fin.rep_eq \<L>_arr_def mdp.\<L>_eq_SUP_det mdp.SUP_step_det_eq 
      cSup_eq_Max mdp.A_ne)

definition "find_policy_arr (v :: ('s, real) iarray_type) =
  fun_to_it (find_policy (bfun_fin (it_nth v)))"

lemma find_policy_arr_code: "find_policy_arr (v :: ('s, real) iarray_type) =
  fun_to_it (\<lambda>s. least_arg_max (\<lambda>a. 
    r (s, a) + l * measure_pmf.expectation (K (s,a)) (it_nth v)) (\<lambda>a. a \<in> A s))"
  unfolding find_policy_arr_def find_policy_def mdp.find_policy'_def
  by (auto simp: bfun_fin.rep_eq)

definition "value_iteration_arr eps v = 
  fun_to_it (value_iteration eps (bfun_fin (it_nth v)))"

lemma code_value_iteration: "value_iteration eps v = 
  (if (2 * l) * dist v (\<L>\<^sub>b v) < eps * (1 - l) \<or> eps \<le> 0
    then \<L>\<^sub>b v 
    else value_iteration eps (\<L>\<^sub>b v))"
  by (simp add: \<L>\<^sub>b.abs_eq mdp.\<L>\<^sub>b.abs_eq)

lemma code_value_iteration_arr: "value_iteration_arr eps v =
  (if \<forall>i. (2 * l) * dist (it_nth v i) (it_nth (\<L>_arr v) i) < eps * (1 - l) \<or> eps \<le> 0
    then \<L>_arr v 
    else value_iteration_arr eps (\<L>_arr v))"
  unfolding value_iteration_arr_def
  apply (subst code_value_iteration)
proof -
  have aux: "fun_to_it ((
    if (2 * l) * dist (bfun_fin (it_nth v)) (\<L>\<^sub>b (bfun_fin (it_nth v))) < eps * (1 - l) \<or> eps \<le> 0 
    then \<L>\<^sub>b (bfun_fin (it_nth v)) 
    else value_iteration eps (\<L>\<^sub>b (bfun_fin (it_nth v))))) =
   ((if 2 * l * dist (bfun_fin (it_nth v)) (\<L>\<^sub>b (bfun_fin (it_nth v))) < eps * (1 - l)  \<or> eps \<le> 0 
    then fun_to_it (\<L>\<^sub>b (bfun_fin (it_nth v))) 
    else fun_to_it (value_iteration eps (\<L>\<^sub>b (bfun_fin (it_nth v))))))"
    by simp
  have aux': "(2 * l) * dist (bfun_fin (it_nth v)) (\<L>\<^sub>b (bfun_fin (it_nth v))) < eps * (1 - l)  \<longleftrightarrow>
    (\<forall>i. (2 * l) * dist (it_nth v i) (it_nth (\<L>_arr v) i) < eps * (1 - l))"
    unfolding \<L>_arr_def
    apply (auto simp: dist_bfun_def)
    subgoal for i
      apply (intro order.strict_trans1[of "2 * l * dist (it_nth v i) (\<L>\<^sub>b (bfun_fin (it_nth v)) i)"])
      by (auto intro!: cSUP_upper2[of _ _ i] mult_left_mono simp: dist_bfun_def bfun_fin.rep_eq)
    apply (subst cSup_eq_Max)
    apply auto
      apply (cases "l = 0")
     apply (auto simp: pos_less_divide_eq[symmetric])
    apply (subst mult.commute[of "2 * l"])
    apply (subst pos_less_divide_eq[symmetric])
    using mdp.zero_le_disc apply linarith
    apply auto
    apply (subst pos_less_divide_eq)
    using mdp.zero_le_disc apply linarith
    by (auto simp: mult.commute bfun_fin.rep_eq)
  show "fun_to_it (apply_bfun (
    if 2 * l * dist (bfun_fin (it_nth v)) (\<L>\<^sub>b (bfun_fin (it_nth v))) < eps * (1 - l) \<or> eps \<le> 0
    then \<L>\<^sub>b (bfun_fin (it_nth v)) 
    else value_iteration eps (\<L>\<^sub>b (bfun_fin (it_nth v))))) =
    (if \<forall>i. (2 * l) * dist (it_nth v i) (it_nth (\<L>_arr v) i) < eps * (1 - l) \<or> eps \<le> 0 
    then \<L>_arr v 
    else fun_to_it (apply_bfun (value_iteration eps (bfun_fin (it_nth (\<L>_arr v))))))"
    apply (subst aux)
    apply (subst aux')
    by (auto simp del: value_iteration_def simp: \<L>_arr_def bfun_fin.abs_eq apply_bfun_inverse)
qed

lemma code_value_iteration': "value_iteration eps v = 
  bfun_fin (it_nth (value_iteration_arr eps (fun_to_it v)))"
  unfolding value_iteration_arr_def apply (auto simp del: value_iteration_def)
  by (simp add: apply_bfun_inverse bfun_fin.abs_eq)

definition "vi_policy_arr eps v = fun_to_it (vi_policy eps (bfun_fin (it_nth v)))"

lemma code_vi_policy_arr: "vi_policy_arr eps v = find_policy_arr (value_iteration_arr eps v)"
  unfolding mdp.vi_policy'_def value_iteration_arr_def vi_policy_arr_def vi_policy_def
  by (simp add: MDPR_typedef.find_policy_arr_def apply_bfun_inverse bfun_fin.abs_eq find_policy_def)

lemma code_vi_policy: "vi_policy eps v = (it_nth (vi_policy_arr eps (fun_to_it v)))"
  unfolding vi_policy_arr_def
  apply auto
  by (simp add: apply_bfun_inverse bfun_fin.abs_eq)

lemma vi_policy_opt: 
  "0 < eps \<and> 0 < l \<Longrightarrow> dist (mdp.\<nu>\<^sub>b (mdp.mk_stationary_det (vi_policy eps v))) mdp.\<nu>\<^sub>b_opt < eps"
  by (simp add: mdp.vi_policy'_opt MDPR_typedef.vi_policy_def)
end

lemmas [code] = 
  MDPR_typedef.code_value_iteration' 
  MDPR_typedef.code_value_iteration_arr
  MDPR_typedef.\<L>_arr_code
  MDPR_typedef.code_vi_policy
  MDPR_typedef.code_vi_policy_arr
  MDPR_typedef.find_policy_arr_code

end

