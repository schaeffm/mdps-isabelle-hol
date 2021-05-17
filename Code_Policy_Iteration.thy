(* Author: Maximilian Schäffeler *)

theory Code_Policy_Iteration
imports
  "Gauss_Jordan.Inverse_IArrays"
  "Gauss_Jordan.Code_Z2"
  "HOL-Library.Code_Target_Numeral"
  Code_Value_Iteration
begin

context MDPR_typedef
begin

sublocale mdp: MDP_ord A K r l
  unfolding MDP_ord_def MDP_finite_type_def
  by (fastforce simp: Abs_mdpr_inverse intro: Abs_mdpr_cases[of "m"])

definition "policy_iteration \<equiv> mdp.policy_iteration"
definition "policy_step \<equiv> mdp.policy_step"
definition "is_dec_det \<equiv> mdp.is_dec_det"
definition "policy_improvement \<equiv> mdp.policy_improvement"
definition "nu_mat = mdp.nu_mat"
definition "fun_to_matrix = mdp.fun_to_matrix"
definition "nu_inv_mat = mdp.nu_inv_mat"
definition "K_st = mdp.K_st"
definition "Ek_mat = mdp.Ek_mat"
definition "mk_dec_det = mdp.mk_dec_det"

lemmas [simp] =
  policy_improvement_def
  policy_step_def
  is_dec_det_def
  nu_mat_def
  fun_to_matrix_def
  nu_inv_mat_def
  K_st_def
  Ek_mat_def
  mk_dec_det_def

lift_definition r_dec\<^sub>b :: "('s \<Rightarrow> 'a pmf) \<Rightarrow> 's \<Rightarrow>\<^sub>b real" is
  "\<lambda>d s. (\<integral>a. r (s, a) \<partial>measure_pmf (d s))"
  using mdp.r_dec_bfun.

lift_definition push_exp :: "('b \<Rightarrow> 'c pmf) \<Rightarrow> ('c \<Rightarrow>\<^sub>b real) \<Rightarrow> ('b \<Rightarrow>\<^sub>b real)" is
  "\<lambda>c f s. measure_pmf.expectation (c s) f"
  using bfun_integral_bound'.

lemma code_mk_dec_det[simp]: "mk_dec_det d s = return_pmf (d s)"
  by (auto simp: mdp.mk_dec_det_def)

lemma code_push_exp[simp]: "push_exp = mdp.push_exp"
  by (auto simp: mdp.push_exp_def push_exp_def)

lemma code_K_st[simp]: "K_st d = (\<lambda>s. d s \<bind> (\<lambda>a. K (s, a)))"
  by (auto simp: mdp.K_st_def)

lemma code_nu_mat[simp]: "nu_mat d = fst (Gauss_Jordan_PA (nu_inv_mat d))"
   using matrix_inv_Gauss_Jordan_PA[OF mdp.invertible_nu_inv_max]
   by (auto simp: inverse_matrix_def mdp.nu_mat_inv)

lemma code_nu_mat'[code]: 
  "nu_mat d \<equiv> iarray_to_matrix (fst (Gauss_Jordan_iarrays_PA (matrix_to_iarray (nu_inv_mat d))))"
  apply (subst code_nu_mat)
  by (auto simp: matrix_to_iarray_fst_Gauss_Jordan_PA[symmetric] iarray_to_matrix_matrix_to_iarray)

lemma invertible_nu_inv_mat: "invertible (nu_inv_mat d)"
  using mdp.invertible_nu_inv_max by auto
  
lift_definition \<K>_st :: "('s \<Rightarrow> 'a pmf) \<Rightarrow> ('s \<Rightarrow>\<^sub>b real) \<Rightarrow>\<^sub>L 's \<Rightarrow>\<^sub>b real"
  is "(\<lambda>p. push_exp (K_st p))"
  by (auto simp: mdp.\<K>_st_def)

lemma code_\<K>_st[simp]: "\<K>_st = mdp.\<K>_st"
  by (auto simp: \<K>_st_def mdp.\<K>_st_def)

lemma code_fun_to_matrix[simp]: "fun_to_matrix = (\<lambda>f. matrix (\<lambda>v. vec_lambda (f (($) v))))"
  by (auto simp: mdp.fun_to_matrix_def)

lemma code_nu_inv_mat: "nu_inv_mat d = mat 1 - l *\<^sub>R Ek_mat d"
  by (auto simp: mdp.nu_inv_mat_eq)

definition "policy_eval_aux d = vec_lambda (apply_bfun (r_dec\<^sub>b (mk_dec_det d)))"
definition "policy_eval d = (vec_nth (nu_mat (mk_dec_det d) *v policy_eval_aux d))"

lemma code_policy_eval_aux: "vec_nth (policy_eval_aux d) = (%i. r_dec\<^sub>b (mk_dec_det d) i)"
  by (auto simp: policy_eval_aux_def)

lemma code_policy_improvement [simp]: "policy_improvement d v s =
  (if is_arg_max (\<lambda>a. mdp.L\<^sub>a a v s) (\<lambda>a. a \<in> A s) (d s) then d s
    else least_arg_max (\<lambda>a. mdp.L\<^sub>a a v s) (\<lambda>a. a \<in> A s))"
  using mdp.policy_improvement_def by auto

lemma code_is_dec_det[simp]: "is_dec_det d \<equiv> \<forall>s. d s \<in> A s"
  by (auto simp: mdp.is_dec_det_def)

lemma code_policy_step[simp]: "policy_step d = policy_improvement d (policy_eval d)"
  unfolding policy_step_def mdp.policy_step_def mdp.policy_eval_code policy_eval_def
  by (auto simp: Bfun_inverse policy_eval_aux_def r_dec\<^sub>b.rep_eq mdp.r_dec\<^sub>b.rep_eq)

lemma code_policy_iteration: "policy_iteration d = 
  (let d' = policy_step d in if d = d' \<or> \<not> is_dec_det d then d else policy_iteration d')"
  unfolding MDPR_typedef.policy_iteration_def
  by simp

definition "Ek_mat' d i = (\<chi> j. pmf (K_st d i) j)"

lemma vec_nth_Ek_mat': "vec_nth (Ek_mat' d i) = (\<lambda> j. pmf (K_st d i) j)"
  apply auto
  unfolding Ek_mat'_def
  by auto

lemma vec_nth_Ek_mat [code abstract]: "vec_nth (Ek_mat d) = Ek_mat' d"
  unfolding Ek_mat'_def
  apply (auto simp: mdp.Ek_mat_def mdp.fun_to_matrix_def mdp.\<K>_st.rep_eq mdp.push_exp_def
      apply_bfun_inverse Bfun_inverse Ek_mat'_def)
  apply (subst Bfun_inverse)
  apply (auto simp: matrix_def axis_def vec_lambda_inverse)
  apply standard
  apply (auto split: if_splits simp: indicator_def[symmetric])
  apply (subst integral_measure_pmf_real[where A = UNIV])
    apply (auto split: if_splits )
  apply standard
proof -
  fix i j
  have "(\<Sum>a\<in>UNIV. (if a = j then 1 else 0) * pmf (mdp.K_st d i) a) = 
    (\<Sum>a\<in>UNIV. (if a = j then pmf (mdp.K_st d i) j else 0))"
    by (simp add: mult_if_delta)
  also have "\<dots> = pmf (mdp.K_st d i) j"
    by auto
  finally show "(\<Sum>a\<in>UNIV. (if a = j then 1 else 0) * pmf (mdp.K_st d i) a) = pmf (mdp.K_st d i) j"
    by auto
qed

definition "policy_iteration_vec d = vec_lambda (policy_iteration (vec_nth d))"
definition "policy_step_vec d = vec_lambda (policy_step (vec_nth d))"
definition "policy_improvement_vec d v = vec_lambda (policy_improvement (vec_nth d) (vec_nth v))"
definition "policy_eval_vec d = vec_lambda (policy_eval (vec_nth d))"

lemma policy_improvement_vec_code: "vec_nth (policy_improvement_vec d v) = (\<lambda> s.
  (if is_arg_max
     (\<lambda>a. r (s, a) + l * measure_pmf.expectation (K (s, a)) (vec_nth v))
     (\<lambda>a. a \<in> A s) (d $ s)
 then d $ s
 else least_arg_max
       (\<lambda>a. r (s, a) + l * measure_pmf.expectation (K (s, a)) (vec_nth v)) (\<lambda>a. a \<in> A s)))"
  unfolding policy_improvement_vec_def
  apply standard
  apply (subst vec_lambda_beta)
  unfolding code_policy_improvement
  by simp

lemma policy_eval_vec_code [code]: "policy_eval_vec d = 
  (nu_mat (MDPR_typedef.mk_dec_det (vec_nth d)) *v policy_eval_aux (vec_nth d))"
  unfolding policy_eval_vec_def
  by (simp add: MDPR_typedef.policy_eval_def)

lemma policy_step_vec_code[code]: 
  "policy_step_vec d = (policy_improvement_vec d) (policy_eval_vec d)"
  unfolding policy_step_vec_def policy_improvement_vec_def policy_eval_vec_def code_policy_step
  by (simp add: MDPR_typedef.policy_eval_def)
  
lemma policy_iteration_vec_code: "policy_iteration_vec d = (let d' = policy_step_vec d in 
  if d = d' \<or> \<not> is_dec_det (vec_nth d) then d else policy_iteration_vec d')"
  unfolding policy_iteration_vec_def policy_step_vec_def
  apply (subst MDPR_typedef.code_policy_iteration)
  unfolding Let_def
  apply auto
   apply (metis (no_types, lifting) UNIV_I vec_lambda_inverse)
  by (simp add: vec_lambda_inverse)

definition "policy_iteration_arr d =
  fun_to_it (\<lambda>s. policy_iteration (it_nth d) s)"

definition "policy_step_arr d = 
  fun_to_it (\<lambda>s. policy_step (it_nth d) s)"

definition "policy_improvement_arr d v = 
  fun_to_it (\<lambda>s. policy_improvement (it_nth d) (\<lambda>i. IArray.sub v (to_nat i)) s)"

definition "policy_eval_arr d = 
  IArray.of_fun (\<lambda>s. policy_eval (it_nth d) (from_nat s)) (CARD('s))"

lemma policy_improvement_arr_code: "policy_improvement_arr d v = fun_to_it (\<lambda>s.
  (if is_arg_max                               
     (\<lambda>a. r (s, a) + l * measure_pmf.expectation (K (s, a)) (\<lambda>i. IArray.sub v (to_nat i)))
     (\<lambda>a. a \<in> A s) (it_nth d s)
 then it_nth d s
 else least_arg_max
       (\<lambda>a. r (s, a) + l * measure_pmf.expectation (K (s, a)) (\<lambda>i. IArray.sub v (to_nat i)))
       (\<lambda>a. a \<in> A s)))"
  unfolding policy_improvement_arr_def MDPR_typedef.code_policy_improvement
  by (simp add: to_nat_from_nat_id)

lemma policy_step_arr_code: "policy_step_arr d = (policy_improvement_arr d) (policy_eval_arr d)"
  unfolding policy_step_arr_def MDPR_typedef.code_policy_step policy_improvement_arr_def 
  by (simp add: to_nat_less_card policy_eval_arr_def)


lemma policy_iteration_arr_code: 
  shows "policy_iteration_arr d =
  (let d' = policy_step_arr d in 
    if d = d' \<or> \<not> is_dec_det (it_nth d) 
    then d 
    else policy_iteration_arr d')"
  unfolding policy_iteration_arr_def policy_step_arr_def
  apply (subst code_policy_iteration)
  apply (subst Let_def)
  apply (subst Let_def)
proof -
  have aux: "fun_to_it (if it_nth d = policy_step (it_nth d) \<or> \<not> is_dec_det (it_nth d) 
    then it_nth d 
    else policy_iteration (policy_step (it_nth d))) =
   (if it_nth d = policy_step (it_nth d) \<or> \<not> is_dec_det (it_nth d) 
    then fun_to_it (it_nth d) 
    else fun_to_it (policy_iteration (policy_step (it_nth d))))"
    by auto
  have aux': "it_nth d = policy_step (it_nth d) \<longleftrightarrow> d = fun_to_it (policy_step (it_nth d))"
    apply auto
    using fun_to_it_inverse'
    by (metis (no_types, lifting))
  show "fun_to_it (
    if it_nth d = policy_step (it_nth d) \<or> \<not> is_dec_det (it_nth d) 
    then it_nth d 
    else policy_iteration (policy_step (it_nth d))) =
    (if d = fun_to_it (policy_step (it_nth d)) \<or> \<not> is_dec_det (it_nth d) 
    then d 
    else fun_to_it (policy_iteration (it_nth (fun_to_it (policy_step (it_nth d))))))"
    apply (subst aux)
    apply (subst aux')
    by simp
qed

lemma policy_iteration_code: "policy_iteration d = it_nth (policy_iteration_arr (fun_to_it d))"
  unfolding policy_iteration_arr_def
  by auto

lemma policy_iteration_correct: 
  "d \<in> mdp.D\<^sub>D \<Longrightarrow> mdp.\<nu>\<^sub>b (mdp.mk_stationary_det (policy_iteration d)) = mdp.\<nu>\<^sub>b_opt"
  using mdp.policy_iteration_correct
  by (auto simp: policy_iteration_def)
end

instantiation  iarray_type :: (mod_type, equal) equal begin
definition "equal_iarray_type (x :: ('a, 'b) iarray_type) (y :: ('a, 'b) iarray_type) = 
  HOL.equal_class.equal (Rep_iarray_type x)  (Rep_iarray_type y)"

instance apply standard unfolding equal_iarray_type_def
  apply (auto simp: equal_eq)
  by (metis Rep_iarray_type_inverse)
end

lemmas[code] = 
  MDPR_typedef.policy_iteration_arr_code
  MDPR_typedef.policy_iteration_code
  MDPR_typedef.policy_step_arr_code
  MDPR_typedef.policy_eval_arr_def
  MDPR_typedef.policy_improvement_arr_code
  MDPR_typedef.policy_eval_def
  MDPR_typedef.code_policy_eval_aux
  MDPR_typedef.code_is_dec_det
  MDPR_typedef.code_nu_inv_mat
  MDPR_typedef.code_nu_mat'
  MDPR_typedef.code_mk_dec_det
  MDPR_typedef.code_K_st
  MDPR_typedef.r_dec\<^sub>b.rep_eq
  MDPR_typedef.\<K>_st.rep_eq
  MDPR_typedef.push_exp.rep_eq
  MDPR_typedef.code_fun_to_matrix


section \<open>Vector code equations\<close>
lemmas [code abstract] = 
  MDPR_typedef.vec_nth_Ek_mat 
  MDPR_typedef.vec_nth_Ek_mat'

lemma [code abstract]: 
  "vec_nth (iarray_to_matrix xs) = (\<lambda>i. iarray_to_vec (IArray.sub xs (to_nat i)))"
  by (auto simp: iarray_to_matrix_def iarray_to_vec_def)

lemma [code abstract]: "vec_nth (iarray_to_vec xs) = (\<lambda>i. (IArray.sub xs (to_nat i)))"
  by (auto simp: iarray_to_vec_def)

lemma [code abstract]: 
  "vec_nth (r *\<^sub>R v) = (\<lambda>i. r *\<^sub>R v $ i)"
  "vec_nth (- v) = (\<lambda>i. - v $ i)"
  by auto

end