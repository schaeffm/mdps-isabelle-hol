(* Author: Maximilian Schäffeler *)

theory MDPR_disc
  imports MDP_disc Bounded_Functions Util Blinfun_Util "Gauss_Jordan.Inverse"
begin

class ordered_real_normed_vector = real_normed_vector + ordered_real_vector

instance real :: ordered_real_normed_vector by standard

instantiation blinfun :: (real_normed_vector, ordered_real_normed_vector) ordered_real_vector 
begin
definition "less_eq_blinfun f g \<equiv> \<forall>x. blinfun_apply f x \<le> blinfun_apply g x"
definition "less_blinfun f g \<equiv> (\<forall>x. blinfun_apply f x \<le> blinfun_apply g x) \<and> (\<exists>y. f y < g y)"

instance
  apply standard
  unfolding less_eq_blinfun_def less_blinfun_def
        apply (metis dual_order.irrefl le_less le_less_trans)
  by (auto intro: order_trans 
      simp: antisym blinfun_eqI plus_blinfun.rep_eq scaleR_blinfun.rep_eq 
      scaleR_left_mono scaleR_right_mono)
end

instantiation bfun :: (_,  ordered_real_normed_vector) ordered_real_vector begin

definition "less_eq_bfun f g \<equiv> \<forall>x. apply_bfun f x \<le> apply_bfun g x"
definition "less_bfun f g \<equiv> \<forall>x. apply_bfun f x \<le> apply_bfun g x \<and> (\<exists>y. f y < g y)"

instance
  apply standard
  unfolding less_eq_bfun_def less_bfun_def
  using less_le_not_le
  by (auto intro: order.trans bfun_eqI simp: eq_iff scaleR_left_mono scaleR_right_mono)
end

instance bfun :: (_,  ordered_real_normed_vector) ordered_real_normed_vector
  by standard

section \<open>Markov Decision Processes with Rewards\<close>
text \<open>
Decision making is only meaningful if there is an objective to be achieved.
As a first step, each state-action pair is assigned a real-valued reward.
We can make certain states and actions more desirable by assigning them a higher reward.
\<close>

locale MDP_reward = discrete_MDP A K
  for
    A and 
    K :: "'s ::countable \<times> 'a ::countable \<Rightarrow> 's pmf" +
  fixes 
    r :: "('s \<times> 'a) \<Rightarrow> real" and
    l :: real
  assumes
    zero_le_disc [simp]: "0 \<le> l" and 
    disc_lt_one [simp]: "l < 1" and
    r_bounded: "bounded (range r)"
begin

text \<open>
This extension to the basic MDPs is formalized with another locale.
It assumes the existence of a reward function @{term r} which takes a state-action pair to a real number. 
We assume that the function is bounded @{prop r_bounded}.

Furthermore, we fix a discounting factor @{term l}, where @{term "0 \<le> l \<and> l < 1"}.
\<close>

subsection \<open>Properties of @{term r} and @{term "r\<^sub>M"}\<close>

definition "r\<^sub>M = (\<Squnion>sa. \<bar>r sa\<bar>)"

lemma r_bound: "\<bar>r sa\<bar> \<le> r\<^sub>M"
  unfolding r\<^sub>M_def using bounded_real r_bounded 
  by (fastforce intro!: cSUP_upper bounded_imp_bdd_above)+

lemma abs_r\<^sub>M[simp]: "\<bar>r\<^sub>M\<bar> = r\<^sub>M"
  by (metis abs_ge_zero abs_of_nonneg order_trans r_bound)

lemma r_bounded': "bounded (r ` X)"
  by (metis r_bounded bounded_subset image_mono subset_UNIV)

lemma r_bound_nonneg: "0 \<le> r\<^sub>M"
  using abs_r\<^sub>M by linarith

lemma summable_powser_const[intro]: assumes "\<bar>c\<bar> < 1" shows "summable (\<lambda>n. c^n * (x ::real))"
proof -
  have "summable (\<lambda>i. norm x * c ^ i)"
    using assms by auto
  thus ?thesis
    by (auto simp: mult.commute)
qed

lemma summable_r\<^sub>M_disc[intro, simp]: "summable (\<lambda>i. l ^ i * r\<^sub>M)"
  by auto

lemma summable_r_disc[intro, simp]:
  shows 
    "summable (\<lambda>i. \<bar>l ^ i * r (sa i)\<bar>)" 
    "summable (\<lambda>i. l ^ i * \<bar>r (sa i)\<bar>)" 
    "summable (\<lambda>i. l ^ i * r (sa i))"
proof -
  show "summable (\<lambda>i. \<bar>l ^ i * r (sa i)\<bar>)"
    apply (rule summable_comparison_test'[OF summable_r\<^sub>M_disc])
    by (auto simp: abs_mult intro!: mult_left_mono r_bound)
  thus "summable (\<lambda>i. l ^ i * r (sa i))" "summable (\<lambda>i. l ^ i * \<bar>r (sa i)\<bar>)"
    using summable_rabs_cancel by (auto simp: abs_mult)
qed

lemma abs_disc_r_le: "\<bar>\<Sum>i<N. l ^ i * r (x !! i)\<bar> \<le> (\<Sum>i<N. l^i * r\<^sub>M)"
proof -
  have "\<bar>\<Sum>i<N. l ^ i * r (x !! i)\<bar> \<le> (\<Sum>i<N. \<bar>l ^ i * r (x !! i)\<bar>)"
    by blast
  also have "\<dots> \<le> (\<Sum>i<N. l ^ i * r\<^sub>M)"
    by (auto intro: sum_mono simp: abs_mult mult_left_mono r_bound)
  finally show ?thesis .
qed

lemma sum_r\<^sub>M_le_suminf: "\<And>N. (\<Sum>i<N. l ^ i * r\<^sub>M) \<le> (\<Sum>N. l ^ N * r\<^sub>M)"
  by (auto intro: sum_le_suminf simp: r_bound_nonneg)

lemma abs_disc_r_eq [simp]: "\<bar>l ^ i * r (x !! i)\<bar> = l ^ i * \<bar>r (x !! i)\<bar>"
  by (auto simp: abs_mult)

lemma suminf_disc_abs_le: "(\<Sum>i. l ^ i * \<bar>r (x !! i)\<bar>) \<le> (\<Sum>i. l ^ i * r\<^sub>M)" 
  by (auto simp: mult_left_mono r_bound intro: suminf_le)

lemma abs_suminf_disc_le: "\<bar>(\<Sum>i. l ^ i * r (x !! i))\<bar> \<le> (\<Sum>i. l ^ i * r\<^sub>M)"
  by (auto intro!: suminf_disc_abs_le order_trans[OF summable_rabs])

lemma suminf_disc_le: "(\<Sum>i. l ^ i * r (x !! i)) \<le> (\<Sum>i. l ^ i * r\<^sub>M)"
  using abs_suminf_disc_le abs_le_D1 by blast

lemma measurable_r_nth[measurable]: "(\<lambda>t. r (t !! i)) \<in> borel_measurable S"
  by (subst measurable_compose[where g = r], measurable)

lemma measurable_suminf_reward[measurable]: "(\<lambda>t. \<Sum>i. l ^ i * r (t !! i)) \<in> borel_measurable S"
  by measurable

lemma integrable_r_state: "integrable (measure_pmf P) (\<lambda>s. \<bar>r (s, a)\<bar>)"
  using r_bound by (fastforce intro!: measure_pmf.integrable_const_bound)

lemma integrable_r_action: "integrable (measure_pmf P) (\<lambda>a. \<bar>r (s, a)\<bar>)"
  using r_bound by (fastforce intro!: measure_pmf.integrable_const_bound)

lemma exp_r_le: "measure_pmf.expectation d (\<lambda>a. \<bar>r (s, a)\<bar>) \<le> r\<^sub>M"
  using integrable_r_action
  by (auto simp add: r_bound intro: measure_pmf.integral_le_const)

section \<open>Expected Total Discounted Reward\<close>
definition "\<nu>_fin p s n = \<integral>t. (\<Sum>i<n. l ^ i * r (t !! i)) \<partial>\<T> p s"

lemma integrable_disc_reward_N: "integrable (\<T> p s) (\<lambda>x. (\<Sum>i<N. l ^ i * r (x !! i)))"
  by (fastforce simp: bounded_iff intro: abs_disc_r_le)

definition "\<nu> p s = lim (\<nu>_fin p s)"

text \<open>
We now let the horizon go to infinity and define the limit as the expected total discounted reward
@{const \<nu>}.
\<close>

definition "\<nu>_MD s \<equiv> \<Squnion>p \<in> \<Pi>\<^sub>M\<^sub>D. \<nu> (mk_markovian_det p) s"

definition "\<nu>_opt s \<equiv> \<Squnion>p \<in> \<Pi>\<^sub>H\<^sub>R. \<nu> p s"

thm integral_dominated_convergence
lemma \<nu>_fin_conv:
  shows "\<nu>_fin p s \<longlonglongrightarrow> \<integral>t. (\<Sum>i. l ^ i * r (t !! i)) \<partial>\<T> p s"
  unfolding \<nu>_fin_def
proof(intro integral_dominated_convergence[where w = "\<lambda>_. (\<Sum>i. l^i * r\<^sub>M)"])
  show "integrable (\<T> p s) (\<lambda>_. \<Sum>N. l ^ N * r\<^sub>M)"
    using prob_space.finite_measure finite_measure.integrable_const by blast
next
  show "AE x in \<T> p s. (\<lambda>N. \<Sum>i<N. l ^ i * r (x !! i)) \<longlonglongrightarrow> (\<Sum>i. l ^ i * r (x !! i))"
    apply (intro AE_I2)
    using summable_LIMSEQ summable_r_disc by blast
next
  show "\<And>N. AE x in \<T> p s. norm (\<Sum>i<N. l ^ i * r (x !! i)) \<le> (\<Sum>N. l ^ N * r\<^sub>M)"
    using abs_disc_r_le sum_r\<^sub>M_le_suminf order_trans
    by fastforce
qed auto

lemma etr_disc_eq: "\<nu> p s = \<integral>t. (\<Sum>i. l ^ i * r (t !! i)) \<partial>\<T> p s"
  using \<nu>_fin_conv \<nu>_def limI by fastforce

text \<open>We can push the limit through the expectation by application of 
@{thm integral_dominated_convergence}.\<close>

lemma integrable_disc_reward: "integrable (\<T> p s) (\<lambda>x. (\<Sum>i. l ^ i * r (x !! i)))"
  by (fastforce simp: bounded_iff intro: abs_suminf_disc_le)

lemma etr_disc_abs_le: "\<bar>\<nu> p s\<bar> \<le> (\<Sum>i. l^i * r\<^sub>M)"
  using abs_suminf_disc_le etr_disc_eq integrable_disc_reward
  by (auto intro!: prob_space.integral_le_const order_trans[OF integral_abs_bound])

lemma etr_disc_le: "\<nu> p s \<le> (\<Sum>i. l^i * r\<^sub>M)"
  by (metis abs_le_D1 etr_disc_abs_le)

lemma \<nu>_opt_bfun: "\<nu>_opt \<in> bfun"
  unfolding \<nu>_opt_def using etr_disc_abs_le policies_ne
  by (fastforce intro!: order_trans[OF cSup_abs_le] norm_le_imp_bfun[of _ "(\<Sum>i. l ^ i * r\<^sub>M)"])

lift_definition \<nu>\<^sub>b_opt :: "'s \<Rightarrow>\<^sub>b real" is \<nu>_opt
  using \<nu>_opt_bfun.

declare \<nu>\<^sub>b_opt.rep_eq[simp]

text \<open>
The expected discounted reward property is separable, which means we can express it as a combination 
of functions depending only on the state-action distrubution for a single epoch.
Thus we may express the finite horizon value in terms of @{const Pn'}.
An important consequence of this fact is that allowing history-dependent policies does not change 
the optimal value of the MDP. 
\<close>
lemma \<nu>_fin_eq_Pn: "\<nu>_fin p s n = (\<Sum>i<n. l^i * measure_pmf.expectation (Pn' p s i) r)"
proof (induction n)
  case 0
  then show ?case 
    by (auto simp: \<nu>_fin_def)
next
  case (Suc n)
  show ?case
    unfolding \<nu>_fin_def
    apply (simp add: Suc[symmetric])
    apply (subst Pn'_eq_\<T>)
    apply (subst integral_distr)
    apply simp
    apply simp
    apply (subst Bochner_Integration.integral_add)
    using integrable_disc_reward_N prob_space.finite_measure[OF \<T>_prob_space]
    by (auto simp: \<nu>_fin_def intro!: r_bound finite_measure.integrable_const_bound)
qed

lemma etr_disc_eq_Pn: "\<nu> p s = (\<Sum>i. l^i * measure_pmf.expectation (Pn' p s i) r)"
  using \<nu>_fin_eq_Pn unfolding \<nu>_def \<nu>_fin_def
  by (simp add: suminf_eq_lim)

lemma Pn'_as_markovian: "Pn' p s = Pn' (mk_markovian (as_markovian p (return_pmf s))) s"
  unfolding Pn'_def using Pn_as_markovian_eq by simp

lemma \<nu>_as_markovian: "\<nu> p s = \<nu> (mk_markovian (as_markovian p (return_pmf s))) s"
  using Pn'_as_markovian by (auto simp: etr_disc_eq_Pn)

lemma \<nu>_MR_eq_HR: "\<nu>_opt s = (\<Squnion>p \<in> \<Pi>\<^sub>M\<^sub>R. \<nu> (mk_markovian p) s)"
proof (rule antisym)
  show "\<nu>_opt s \<le> (\<Squnion>p\<in>\<Pi>\<^sub>M\<^sub>R. \<nu> (mk_markovian p) s)"
    unfolding \<nu>_opt_def
    apply (intro cSUP_mono)
    using policies_ne apply simp
    apply (auto intro!: boundedI bounded_imp_bdd_above etr_disc_abs_le)[1]
    apply (subst \<nu>_as_markovian)
    using is_\<Pi>\<^sub>M\<^sub>R_as_markovian order_refl mem_Collect_eq
    by blast
  show "(\<Squnion>p\<in>\<Pi>\<^sub>M\<^sub>R. \<nu> (mk_markovian p) s) \<le> \<nu>_opt s"
    unfolding \<nu>_opt_def
    using \<Pi>\<^sub>M\<^sub>R_ne \<Pi>\<^sub>M\<^sub>R_imp_policies
    by (auto intro!: cSUP_mono boundedI bounded_imp_bdd_above etr_disc_abs_le)
qed

lemma suminf_split_head': 
  "summable (f :: nat \<Rightarrow> 'x :: real_normed_vector) \<Longrightarrow> suminf f = f 0 + (\<Sum>n. f (Suc n))"
  by (auto simp: suminf_split_head)

subsection \<open>r dec\<close>
abbreviation "r_dec d s \<equiv> (\<integral>a. r (s, a) \<partial>measure_pmf (d s))"

lemma r_dec_eq_r_K0: "r_dec d s = measure_pmf.expectation (K0' d s) r"
  by (simp add: K0'_def)

lemma abs_r_dec_le: "\<bar>r_dec d x\<bar> \<le> r\<^sub>M"
  using exp_r_le integral_abs_bound order_trans by fast

lemma r_dec_bfun: "r_dec d \<in> bfun"
  using abs_r_dec_le by (fastforce intro!: norm_le_imp_bfun)

lift_definition r_dec\<^sub>b :: "('s \<Rightarrow> 'a pmf) \<Rightarrow> 's \<Rightarrow>\<^sub>b real" is "\<lambda>d s. r_dec d s"
  using r_dec_bfun .

lemma norm_r_bound: "norm (r_dec\<^sub>b p) \<le> r\<^sub>M"
  by (simp add: abs_r_dec_le  Bounded_Functions.norm_bound r_dec\<^sub>b.rep_eq)

lemma etr_disc_step:
  shows "\<nu> p s = r_dec (p []) s + l * (\<integral>a. \<integral>s'. \<nu> (\<pi>_Suc p (s,a)) s' \<partial>(K (s,a)) \<partial>p [] s)"
proof -
  have aux: "\<And>y t. (\<Sum>i. l ^ i * r ((y##t) !! i)) = r y + l * (\<Sum>i. l ^ i * r (t !! i))"
  proof -
    fix x xa
    have "r x + l * (\<Sum>i. l ^ i * r (xa !! i)) = r x + (\<Sum>i. l * (l ^ i * r (xa !! i)))"
      by (simp add: suminf_mult)
    also have "\<dots> = r x + (\<Sum>i. (l ^ (Suc i) * r ((x##xa) !! Suc i)))"
      by (auto simp: algebra_simps)
    also have "\<dots> = (\<Sum>i. l ^ i * r ((x ## xa) !! i))"
      apply (subst suminf_split_head)
      using suminf_mult summable_r_disc(3)
      by auto
    finally show "(\<Sum>i. l ^ i * r ((x ## xa) !! i)) = r x + l * (\<Sum>i. l ^ i * r (xa !! i))"
      by auto
  qed
  have "\<nu> p s = \<integral>t. (\<Sum>i. l ^ i * r (t !! i)) \<partial>\<T> p s"
    by (auto simp: etr_disc_eq)
  also have "\<dots> = (\<integral>a. \<integral>s'. \<integral>t'. r (s,a)  + l * (\<Sum>i. l ^ i * r (t' !! i)) 
    \<partial>\<T> (\<pi>_Suc p (s,a)) s' \<partial>(K (s,a)) \<partial>p [] s)"
    apply (subst integral_\<T>[where ?B = "\<Sum>i. l^i * r\<^sub>M"])
    using abs_suminf_disc_le apply blast
    subgoal by measurable
    apply (intro Bochner_Integration.integral_cong[OF refl])
    apply (subst suminf_split_head')
    by (auto simp add: suminf_mult mult.assoc)
  also have "\<dots> = (\<integral>a. r (s,a) \<partial>p [] s)  + l * (\<integral>a. \<integral>s'. \<nu> (\<pi>_Suc p (s,a)) s' \<partial>(K (s,a)) \<partial>p [] s)"
    apply (subst Bochner_Integration.integral_add)
    subgoal by auto
    apply (fastforce intro: abs_suminf_disc_le boundedI)
    apply (subst lebesgue_integral_const)
    apply (subst prob_space.prob_space)
    apply auto
    apply (subst Bochner_Integration.integral_add)
    subgoal by simp
    subgoal
      using prob_space.finite_measure finite_measure.integrable_const 
      apply (auto intro!: measure_pmf.integrable_const_bound AE_I2 
          order_trans[OF integral_abs_bound] prob_space.integral_le_const)
      by (auto intro!: abs_suminf_disc_le boundedI)
    apply (subst Bochner_Integration.integral_add)
    subgoal 
      by (auto intro!: measure_pmf.integrable_const_bound AE_I2 r_bound)
    subgoal apply simp
      using prob_space.finite_measure finite_measure.integrable_const 
      apply (auto intro!: measure_pmf.integrable_const_bound AE_I2 
          order_trans[OF integral_abs_bound] prob_space.integral_le_const)
      using prob_space_measure_pmf by (auto intro!: abs_suminf_disc_le boundedI)
    apply simp
    by (metis (no_types, lifting) Bochner_Integration.integral_cong etr_disc_eq)
  finally show ?thesis .
qed


section \<open>Push-Forward of a Bounded Function\<close>
lift_definition push_exp :: "('b \<Rightarrow> 'c pmf) \<Rightarrow> ('c \<Rightarrow>\<^sub>b real) \<Rightarrow> ('b \<Rightarrow>\<^sub>b real)" is
  "\<lambda>c f s. measure_pmf.expectation (c s) f"
  using bfun_integral_bound' .

lemma r_bfun: "r \<in> bfun"
  using bfun_def r_bounded by blast

lemma "r_dec\<^sub>b d = push_exp (K0' d) (Bfun r)"
  apply (intro bfun_eqI)
  unfolding push_exp.rep_eq r_dec\<^sub>b.rep_eq
  apply (auto simp: r_dec_eq_r_K0)
  by (simp add: bfun.Bfun_inverse r_bfun)

lemma norm_push_exp_le_norm: "norm (push_exp d x) \<le> norm x"
proof -
  have "\<And>s. (\<integral>s'. norm (x s') \<partial>d s) \<le> norm x"
    using measure_pmf.prob_space_axioms norm_le_norm_bfun[of x]
    by (auto intro!: prob_space.integral_le_const)
  hence aux: "\<And>s. norm (\<integral>s'. x s' \<partial>d s) \<le> norm x"
    using integral_norm_bound order_trans by blast
  have "norm (push_exp d x) = (\<Squnion>s. norm (\<integral>s'. x s' \<partial>d s))"
    unfolding push_exp.rep_eq norm_bfun_def' by auto
  also have "\<dots> \<le> norm x"
    using aux by (fastforce intro!: cSUP_least)
  finally show ?thesis .
qed

lemma push_exp_bounded_linear[simp]: "bounded_linear (push_exp d)"
  using norm_push_exp_le_norm
  by (auto intro!: bounded_linear_intro[where K = 1] bfun_eqI simp: push_exp.rep_eq)

lemma onorm_push_exp[simp]: "onorm (push_exp d) = 1"
proof -
  have "norm (push_exp d 1) = 1"
    by (auto simp: norm_bfun_def' push_exp.rep_eq)
  thus ?thesis
    by (metis antisym mult.left_neutral mult.right_neutral norm_bfun_one 
        norm_push_exp_le_norm onorm onorm_bound push_exp_bounded_linear zero_le_one)
qed

lemma push_exp_return[simp]: "push_exp return_pmf = id"
  by (metis bfun_eqI eq_id_iff expectation_return_pmf push_exp.rep_eq)

section \<open>@{term \<P>\<^sub>X}: push-forward of a function through the MDP\<close>
definition "\<P>\<^sub>X\<^sub>Y p n = push_exp (\<lambda>s. Pn' p s n)"

lemma \<P>\<^sub>X\<^sub>Y_0[simp]: "\<P>\<^sub>X\<^sub>Y p 0 = push_exp (K0' (p []))"
  by (auto intro: bfun_eqI simp: \<P>\<^sub>X\<^sub>Y_def push_exp.rep_eq)

definition "\<P>\<^sub>X p n = push_exp (\<lambda>s. Xn' (mk_markovian p) s n)"

lemma \<P>\<^sub>X_0[simp]: "\<P>\<^sub>X p 0 = id"
  by (auto intro: bfun_eqI simp: \<P>\<^sub>X_def push_exp.rep_eq)

lemma \<P>\<^sub>X_Suc: "\<P>\<^sub>X p (Suc n) v = push_exp (K_st (p 0)) ((\<P>\<^sub>X (\<lambda>n. p (Suc n)) n) v)"
  using Suc_Xn'_markovian
  by (auto intro!: abs_le_norm_bfun integral_bind[where K = "count_space UNIV"] bfun_eqI
      simp: measure_pmf_in_subprob_algebra measure_pmf_bind \<P>\<^sub>X_def  push_exp.rep_eq)

lemma \<P>\<^sub>X_bounded_linear[simp]: "bounded_linear (\<P>\<^sub>X p t)"
  unfolding \<P>\<^sub>X_def by simp

lemma norm_\<P>\<^sub>X: "onorm (\<P>\<^sub>X p t) = 1"
  unfolding \<P>\<^sub>X_def by simp

lemma \<P>\<^sub>X_Suc_n': "\<P>\<^sub>X p (Suc n) v = \<P>\<^sub>X p n (push_exp (K_st (p n)) v)"
  apply (induction n arbitrary: p v)
  apply (simp add: \<P>\<^sub>X_Suc)
  using \<P>\<^sub>X_Suc by metis

lemma \<P>\<^sub>X_sconst[simp]: "\<P>\<^sub>X (\<lambda>_. p) n = (push_exp (K_st p))^^n"
  by (induction n) (auto simp: \<P>\<^sub>X_Suc)

lemma norm_P_n[simp]: "onorm (push_exp (K_st p) ^^ n) = 1"
  using norm_\<P>\<^sub>X[of "\<lambda>_. p" n] by auto

lemma norm_\<P>\<^sub>X_apply[simp]: "norm (\<P>\<^sub>X p n x) \<le> norm x"
  by (metis \<P>\<^sub>X_bounded_linear mult_cancel_right1 norm_\<P>\<^sub>X onorm)

lemma norm_l_pow_eq [simp]: "norm (l^t *\<^sub>R F) = l^t * norm F"
  by auto

lemma \<P>\<^sub>X_bound_r: "norm (\<P>\<^sub>X p t (r_dec\<^sub>b (p t))) \<le> r\<^sub>M"
  using norm_\<P>\<^sub>X_apply norm_r_bound order.trans by blast

lemma \<P>\<^sub>X_bounded_r: "bounded (range (\<lambda>t. (\<P>\<^sub>X p t (r_dec\<^sub>b (p t)))))"
  using \<P>\<^sub>X_bound_r by (auto intro!: boundedI)

lemma summable_norm_bfun_disc: "summable (\<lambda>t. l^t * norm (apply_bfun f t))"
  by (auto simp: norm_le_norm_bfun mult.commute[of "l^_"] intro!: Abel_lemma[of _ 1 _ "norm f"])

lemma summable_discI [intro]:
  assumes "bounded (range F)"
  shows "summable (\<lambda>t. l^t * norm (F t))"
proof -
  obtain b where "\<forall>x. norm (F x) \<le> b"
    by (meson assms bounded_iff rangeI)
  thus ?thesis
    using Abel_lemma[of l 1 F b] by (auto simp: mult.commute)
qed

lemma summable_norm_disc_I [intro]:
  assumes "summable (\<lambda>t. (l^t * norm F))"
  shows "summable (\<lambda>t. norm (l^t *\<^sub>R F))"
  using assms by auto

lemma summable_norm_disc_I'[intro]:
  assumes "summable (\<lambda>t. (l^t * norm (F t)))"
  shows "summable (\<lambda>t. norm (l^t *\<^sub>R F t))"
  using assms by auto

lemma summable_norm_disc_reward'[simp]:
  shows "summable (\<lambda>t. l^t * norm (\<P>\<^sub>X p t (r_dec\<^sub>b (p t))))"
  using \<P>\<^sub>X_bounded_r by auto

lemma summable_disc_reward [intro]:
  assumes "bounded (range (F :: nat \<Rightarrow> 'b :: banach))"
  shows "summable (\<lambda>t. l^t *\<^sub>R (F t))"
proof -
  have "summable (\<lambda>t. norm (l^t *\<^sub>R (F t)))"
    using assms by blast
  thus ?thesis
    by (auto simp: summable_norm_cancel)
qed

lemma summable_disc_reward_\<P>\<^sub>X [simp]:
  shows "summable (\<lambda>t. l^t *\<^sub>R \<P>\<^sub>X p t (r_dec\<^sub>b (p t)))"
  using summable_disc_reward \<P>\<^sub>X_bounded_r by blast

lemma summable_bfun_disc [simp]: "summable (\<lambda>t. l^t * (apply_bfun f t))"
proof -
  have h: "\<And>t. l^t * norm (apply_bfun f t) = norm (l^t * apply_bfun f t)"
    by (auto simp: abs_mult)
  hence "summable (\<lambda>t. norm (l^t * (apply_bfun f t)))"
    apply (subst h[symmetric])
    using summable_norm_bfun_disc
    by blast
  thus ?thesis 
    using summable_norm_cancel by fast
qed

lemma summable_disc_norm: "summable (\<lambda>x. l^x * norm c)"
  by (auto simp: mult.commute[of "l^_"] intro!: Abel_lemma[of l 1])

lemma summable_disc[simp]: "summable (\<lambda>x. l^x * c)"
  by (simp add: summable_geometric summable_mult2)

lemma norm_bfun_disc_le: "norm f \<le> B \<Longrightarrow> (\<Sum>x. l^x * norm (apply_bfun f x)) \<le> (\<Sum>x. l^x * B)"
  by (auto intro!: suminf_le mult_left_mono Bounded_Functions.norm_bounded intro: order.trans)

lemma norm_bfun_disc_le': "norm f \<le> B \<Longrightarrow> (\<Sum>x. l^x * (apply_bfun f x)) \<le> (\<Sum>x. l^x * B)" 
  apply (intro order.trans[OF _ norm_bfun_disc_le])
  using summable_norm_bfun_disc[of f] real_norm_def
  by (auto simp add: mult_left_mono intro!: suminf_le)

lemma sum_disc_lim: assumes "\<bar>c :: real\<bar> < 1" shows "(\<Sum>x. c^x * B) = B /(1-c)"
  apply (subst suminf_mult2[where c = B, symmetric])
  apply (auto simp add: assms summable_geometric)
  apply (subst suminf_geometric[of c])
  using assms by auto


lemma sum_disc_lim_l: "(\<Sum>x. l^x * B) = B /(1-l)"
  apply (subst suminf_mult2[where c = B, symmetric])
  apply (auto simp add: summable_geometric)
  apply (subst suminf_geometric[of l])
  by auto

lemma sum_disc_bound: "(\<Sum>x. l^x * apply_bfun f x) \<le> (norm f) /(1-l)"
  using norm_bfun_disc_le' sum_disc_lim by auto

lemma sum_disc_bound': 
  "\<forall>n. norm ((f :: nat \<Rightarrow> 'b \<Rightarrow>\<^sub>b real) n) \<le> B \<Longrightarrow> norm (\<Sum>x. l^x *\<^sub>R f x) \<le> B /(1-l)"
proof -
  assume h: "\<forall>n. norm ((f :: nat \<Rightarrow> 'b \<Rightarrow>\<^sub>b real) n) \<le> B"
  hence "norm (\<Sum>x. l^x *\<^sub>R f x) \<le>  (\<Sum>x. norm (l^x *\<^sub>R f x))"
    by (fastforce intro!: boundedI summable_norm)
  also have "\<dots> \<le> (\<Sum>x. l^x * norm (f x))"
    by auto
  also have "\<dots> \<le> (\<Sum>x. l^x * B)"
    using h by (auto intro!: suminf_le boundedI simp add: mult_mono')
  also have "\<dots> = B /(1-l)"
    by (simp add: sum_disc_lim)
  finally show "norm (\<Sum>x. l^x *\<^sub>R f x) \<le> B /(1-l)".
qed

lemma disc_reward_tendsto: 
  "(\<lambda>n. \<Sum>t<n. l^t *\<^sub>R \<P>\<^sub>X p t (r_dec\<^sub>b (p t))) \<longlonglongrightarrow> (\<Sum>t. l^t *\<^sub>R \<P>\<^sub>X p t (r_dec\<^sub>b (p t)))"
  by (simp add: summable_LIMSEQ)

lemma suminf_apply_bfun:
  fixes f :: "nat \<Rightarrow> 'c \<Rightarrow>\<^sub>b real"  
  shows "summable f \<Longrightarrow> apply_bfun (\<Sum>i. f i) x = (\<Sum>i. apply_bfun (f i) x)"
  apply (subst bounded_linear.suminf[where f = "\<lambda>y. apply_bfun y x"])
  by (auto intro!: bounded_linear_intro[where K = 1] abs_le_norm_bfun)

(* 6.1.2 in Puterman *)
lemma \<nu>_bfun: "\<nu> p \<in> bfun"
  unfolding bfun_def
  apply (auto simp: bounded_iff[symmetric])
  apply (intro boundedI)
  using etr_disc_abs_le
  by auto

lemma \<nu>_fin_bfun: "(\<lambda>s. \<nu>_fin p s n) \<in> bfun"
  unfolding bfun_def
  apply (auto simp: bounded_iff[symmetric] \<nu>_fin_def)
  apply (intro boundedI[of _ "(\<Sum>i<n. l ^ i * r\<^sub>M)"])
  using etr_disc_abs_le abs_disc_r_le
  apply auto
  apply (intro order_trans[OF integral_abs_bound])
  apply (intro prob_space.integral_le_const)
  apply auto
  apply (intro finite_measure.integrable_const_bound[of _ _ "(\<Sum>i<n. l ^ i * r\<^sub>M)"])
  apply auto
  apply (intro prob_space.finite_measure)
  by auto

lift_definition \<nu>\<^sub>b :: "('s, 'a) pol \<Rightarrow> 's \<Rightarrow>\<^sub>b real" is \<nu>
  using \<nu>_bfun .

lemma \<nu>_le: "norm (\<nu>\<^sub>b p) \<le> r\<^sub>M/(1-l)"
  unfolding norm_bfun_def' using etr_disc_abs_le 
  by (auto simp: \<nu>\<^sub>b.rep_eq sum_disc_lim intro!: cSUP_least)

lemma \<nu>_HR_le [intro]: "p \<in> \<Pi>\<^sub>H\<^sub>R \<Longrightarrow> \<nu> p s \<le> \<nu>_opt s"
  unfolding \<nu>_opt_def is_policy_def 
  apply (intro cSUP_upper)
  using sum_disc_lim etr_disc_abs_le
  by (auto intro!: bounded_imp_bdd_above boundedI)

lemma \<nu>\<^sub>b_le_opt [intro]: "p \<in> \<Pi>\<^sub>H\<^sub>R \<Longrightarrow> \<nu>\<^sub>b p \<le> \<nu>\<^sub>b_opt"
  unfolding less_eq_bfun_def \<nu>\<^sub>b.rep_eq \<nu>\<^sub>b_opt.rep_eq
  using \<nu>_HR_le by auto

lemma \<nu>_elem: "\<nu>\<^sub>b (mk_markovian p) s = (\<Sum>i. l^i * \<P>\<^sub>X p i (r_dec\<^sub>b (p i)) s)"
  apply (simp only: etr_disc_eq_Pn Pn'_markovian_eq_Xn'_bind \<P>\<^sub>X_def measure_pmf_bind \<nu>\<^sub>b.rep_eq)
  apply (subst integral_bind)
  using measure_pmf_in_subprob_algebra r_bound
  by (auto simp: K0'_def push_exp.rep_eq r_dec\<^sub>b.rep_eq)

lemma \<nu>\<^sub>b_eq_\<P>\<^sub>X: "\<nu>\<^sub>b (mk_markovian p) = (\<Sum>i. l^i *\<^sub>R \<P>\<^sub>X p i (r_dec\<^sub>b (p i)))"
  by (auto intro: bfun_eqI simp: \<nu>_elem suminf_apply_bfun)

lemma \<nu>_eq_\<P>\<^sub>X: "\<nu> (mk_markovian p) = (\<Sum>i. l^i *\<^sub>R \<P>\<^sub>X p i (r_dec\<^sub>b (p i)))"
  by (metis \<nu>\<^sub>b.rep_eq \<nu>\<^sub>b_eq_\<P>\<^sub>X)

lift_definition \<K>_st :: "('s, 'a) dec \<Rightarrow> ('s \<Rightarrow>\<^sub>b real) \<Rightarrow>\<^sub>L ('s \<Rightarrow>\<^sub>b real)" is "\<lambda>p. push_exp (K_st p)"
  using push_exp_bounded_linear by auto

lemma \<K>_st_pow: "blinfun_apply (\<K>_st p ^^ n) = blinfun_apply (\<K>_st p) ^^ n"
  by (induction n) auto

lemma \<P>\<^sub>X_const: "\<P>\<^sub>X (\<lambda>_. d) n = (\<K>_st d)^^n"
  by (simp add: \<K>_st.rep_eq \<K>_st_pow)

lemma norm_\<K>_st[simp]: "norm (\<K>_st p) = 1"
  by (simp add: norm_blinfun.rep_eq \<K>_st.rep_eq)

lemma norm_\<K>_st_pow[simp]: "norm (\<K>_st p ^^ t) = 1"
  by (simp add: \<K>_st_pow norm_blinfun.rep_eq \<K>_st.rep_eq)

lemma norm_\<K>_st_l_less: "norm (l *\<^sub>R \<K>_st p) < 1"
  by auto

lemma \<K>_st_eq_\<P>\<^sub>X_one: "blinfun_apply (\<K>_st (p 0)) = \<P>\<^sub>X p 1"
  by (auto simp: \<P>\<^sub>X_Suc_n' \<K>_st.rep_eq)

text \<open>
@{term "\<K>_st d v"} defines for each state the expected value of @{term v} 
after taking a single step in the MDP according to the decision rule @{term d}.  
\<close>

subsection \<open>Properties of @{const \<K>_st}\<close>

lemma \<K>_st_pos: "0 \<le> u \<Longrightarrow> 0 \<le> \<K>_st d u"
  by (simp add: less_eq_bfun_def \<K>_st.rep_eq push_exp.rep_eq)

lemma \<K>_st_n_pos: "0 \<le> u \<Longrightarrow> 0 \<le> ((\<K>_st d)^^n) u"
  apply (induction n)
  by (auto simp: push_exp.rep_eq \<K>_st.rep_eq less_eq_bfun_def)

lemma \<K>_st_n_disc_pos: "0 \<le> u \<Longrightarrow> 0 \<le> (l^n *\<^sub>R \<K>_st d^^n) u"
  by (auto simp add: \<K>_st_n_pos scaleR_nonneg_nonneg blinfun.scaleR_left)

lemma \<K>_st_sum_pos: "0 \<le> u \<Longrightarrow> 0 \<le> (\<Sum>t\<le>n. l^t *\<^sub>R (\<K>_st d^^t)) u"
  apply (induction n)
  by (auto simp: \<K>_st_n_pos \<K>_st_pos blinfun.add_left blinfun.scaleR_left scaleR_nonneg_nonneg)

lemma \<K>_st_sum_ge: "0 \<le> u \<Longrightarrow> u \<le> (\<Sum>t\<le>n. l^t *\<^sub>R \<K>_st p^^t) u"
proof (induction n)
  case (Suc n)
  show "u \<le>(\<Sum>t\<le>Suc n. l^t *\<^sub>R \<K>_st p^^t) u"
  proof -
    have "u \<le> (\<Sum>n\<le>n. l ^ n *\<^sub>R \<K>_st p ^^ n) u"
      using Suc.IH Suc.prems by blast
    then have "u \<le> (\<Sum>n\<le>n. l ^ n *\<^sub>R \<K>_st p ^^ n) u + (l ^ Suc n *\<^sub>R \<K>_st p ^^ Suc n) u"
      by (meson \<K>_st_n_disc_pos Suc.prems le_add_same_cancel1 order_trans)
    then show ?thesis
      by (simp add: blinfun.add_left)
  qed
qed simp

lemma disc_\<K>_st_tendsto: "(\<lambda>n. (\<Sum>t\<le>n. l^t *\<^sub>R \<K>_st p^^t)) \<longlonglongrightarrow> (\<Sum>t. l^t *\<^sub>R \<K>_st p^^t)"
  apply (intro summable_LIMSEQ' summable_disc_reward)
  using norm_P_n by (auto simp: bounded_iff)

lemma disc_\<K>_st_lim: "lim (\<lambda>n. (\<Sum>t\<le>n. l^t *\<^sub>R \<K>_st p^^t)) = (\<Sum>t. l^t *\<^sub>R \<K>_st p^^t)"
  using limI disc_\<K>_st_tendsto
  by blast

lemma convergent_disc_\<K>_st: "convergent (\<lambda>n. (\<Sum>t\<le>n. l^t *\<^sub>R \<K>_st p^^t))"
  using convergent_def disc_\<K>_st_tendsto by blast

lemma \<K>_st_suminf_ge: "0 \<le> u \<Longrightarrow> u \<le> (\<Sum>t. l^t *\<^sub>R \<K>_st p^^t) u"
proof -
  assume h: "0 \<le> u"
  have aux: "\<And>x. (\<lambda>n. (\<Sum>t\<le>n. l^t *\<^sub>R \<K>_st p^^t) u x) \<longlonglongrightarrow> (\<Sum>t. l^t *\<^sub>R \<K>_st p^^t) u x"
    using bfun_tendsto_apply_bfun disc_\<K>_st_lim lim_blinfun_apply[OF convergent_disc_\<K>_st] 
    by fastforce
  have "\<And>n. u \<le> (\<Sum>t\<le>n. l^t *\<^sub>R \<K>_st p^^t) u"
    using \<K>_st_sum_ge[OF h] by blast
  thus ?thesis
    by (auto simp: less_eq_bfun_def intro!: LIMSEQ_le_const[OF aux])
qed

lemma \<K>_st_suminf_pos: 
  assumes "0 \<le> u" 
  shows "0 \<le> (\<Sum>t. l^t *\<^sub>R \<K>_st p^^t) u"
  using \<K>_st_suminf_ge assms order.trans by blast

lemma lemma_6_1_2_b:
  assumes "v \<le> u"
  shows 
    "(\<Sum>t. l^t *\<^sub>R \<K>_st p^^t) v \<le> (\<Sum>t. l^t *\<^sub>R \<K>_st p^^t) u"
proof -
  have "0 \<le> (\<Sum>n. l ^ n *\<^sub>R \<K>_st p ^^ n) (u - v)"
    by (simp add: \<K>_st_suminf_pos \<open>v \<le> u\<close>)
  hence "0 \<le> (\<Sum>t. l^t *\<^sub>R \<K>_st p^^t) u - (\<Sum>t. l^t *\<^sub>R \<K>_st p^^t) v"
    by (simp add: blinfun.diff_right)
  thus ?thesis
    by simp
qed

subsection \<open>The linear operator @{term L}\<close>
definition "L d v \<equiv> r_dec\<^sub>b d + l *\<^sub>R \<K>_st d v"
text \<open>
 We define the linear operator @{const L} as the sum of the reward and 
 the discounted evaluation of @{term v}.
\<close>

text \<open>
  The value of a markovian policy can be expressed in terms of @{const L}.
\<close>
lemma \<nu>_step: "\<nu>\<^sub>b (mk_markovian p) = L (p 0) (\<nu>\<^sub>b (mk_markovian (\<lambda>n. p (Suc n))))"
proof -
  have s: "summable (\<lambda>t. l^t *\<^sub>R (\<P>\<^sub>X p (Suc t) (r_dec\<^sub>b (p (Suc t)))))"
    apply (intro summable_disc_reward boundedI[of _ r\<^sub>M])
    using \<P>\<^sub>X_bound_r by blast
  have 
    "\<nu>\<^sub>b (mk_markovian p) = r_dec\<^sub>b (p 0) + (\<Sum>t. l^(Suc t) *\<^sub>R \<P>\<^sub>X p (Suc t) (r_dec\<^sub>b (p (Suc t))))"
    by (subst suminf_split_head) (auto simp: \<nu>\<^sub>b_eq_\<P>\<^sub>X)
  also have 
    "\<dots> = r_dec\<^sub>b (p 0) + l *\<^sub>R (\<Sum>t. \<K>_st (p 0) (l^t *\<^sub>R \<P>\<^sub>X (\<lambda>n. p (Suc n)) t (r_dec\<^sub>b (p (Suc t)))))"
    using suminf_scaleR_right[OF s] 
    by (auto simp: \<P>\<^sub>X_Suc \<K>_st.rep_eq linear_simps)
  also have 
    "\<dots> = L (p 0) (\<nu>\<^sub>b (mk_markovian (\<lambda>n. p (Suc n))))"
    by (simp add: \<nu>\<^sub>b_eq_\<P>\<^sub>X L_def \<K>_st.rep_eq bounded_linear.suminf)
  finally show ?thesis .
qed

text \<open>
  For stationary policies, since @{term "r_dec\<^sub>b d"} is the same at each epoch, 
  we can pull it out of the infinite sum.
\<close>

lemma \<nu>_stationary: "\<nu>\<^sub>b (mk_stationary d) = (\<Sum>t. l^t *\<^sub>R ((\<K>_st d)^^t)) (r_dec\<^sub>b d)"
proof -
  have "\<nu>\<^sub>b (mk_stationary d) = (\<Sum>t. (l ^ t *\<^sub>R (\<K>_st d ^^ t)) (r_dec\<^sub>b d))"
    by (simp add: \<nu>\<^sub>b_eq_\<P>\<^sub>X \<K>_st_pow \<K>_st.rep_eq \<nu>\<^sub>b.rep_eq scaleR_blinfun.rep_eq)
  also have "...  = (\<Sum>t. (l ^ t *\<^sub>R (\<K>_st d ^^ t))) (r_dec\<^sub>b d)"
    apply (subst bounded_linear.suminf[where f = "\<lambda>x. blinfun_apply x (r_dec\<^sub>b d)"]) 
    by (auto intro!: bounded_linear.suminf boundedI)
  finally show ?thesis .
qed


text \<open>
The value of the corresponding stationary policy to a decision rule @{term d} is 
a fixpoint of @{term "L d"}. It is also the unique fixpoint.
\<close>

lemma L_\<nu>_fix: "\<nu>\<^sub>b (mk_stationary d) = L d (\<nu>\<^sub>b (mk_stationary d))"
  using \<nu>_step .

lemma L_fix_\<nu>:
  assumes "L p v = v"
  shows "v = \<nu>\<^sub>b (mk_stationary p)"
  using assms proof -
  assume "L p v = v"
  hence "(id_blinfun - l *\<^sub>R \<K>_st p) v = r_dec\<^sub>b p"
    by (metis L_def add_diff_cancel blinfun.diff_left blinfun.scaleR_left blinfun_apply_id_blinfun)
  hence "v = (\<Sum>t. (l *\<^sub>R \<K>_st p)^^t) (r_dec\<^sub>b p)"
    using inv_norm_le[OF norm_\<K>_st_l_less] blinfun_apply_id_blinfun
    by (metis (no_types, lifting) blinfun_apply_blinfun_compose)
  thus "v = \<nu>\<^sub>b (mk_stationary p)"
    by (auto simp: \<nu>_stationary blincomp_scaleR_right)
qed

lemma L_\<nu>_fix_iff: "L d v = v \<longleftrightarrow> v = \<nu>\<^sub>b (mk_stationary d)"
  using L_fix_\<nu> L_\<nu>_fix by auto

section \<open>Optimality Equations\<close>
definition "\<L> (v :: 's \<Rightarrow>\<^sub>b real) s = (\<Squnion>d \<in> D\<^sub>R. L d v s)"

lemma norm_step_bound: "norm (r_dec\<^sub>b p + l *\<^sub>R blinfun_apply (\<K>_st p) v) \<le> r\<^sub>M + l * norm v"
  by (metis abs_of_nonneg mult.left_neutral mult_left_mono norm_\<K>_st norm_add_rule_thm 
      norm_blinfun norm_r_bound norm_scaleR zero_le_disc)

lemma abs_step_bound: "\<bar>r_dec\<^sub>b p s + l * \<K>_st p v s\<bar> \<le> r\<^sub>M + l * norm v"
  using order.trans[OF Bounded_Functions.norm_bounded norm_step_bound] real_norm_def 
  by (auto dest: abs_le_D1)

lemma step_bound: "r_dec\<^sub>b p s + l * \<K>_st p v s \<le> r\<^sub>M + l * norm v"
  using abs_step_bound by (auto dest: abs_le_D1)

lemma \<L>_bfun: "\<L> v \<in> bfun"
  unfolding \<L>_def bfun_def using abs_step_bound ex_dec 
  by (fastforce simp: L_def intro!: cSup_abs_le boundedI)

lift_definition \<L>\<^sub>b :: "('s \<Rightarrow>\<^sub>b real) \<Rightarrow> 's \<Rightarrow>\<^sub>b real" is "\<L>"
  using \<L>_bfun .

lemma \<K>_st_mono[intro]: "a \<le> b \<Longrightarrow> \<K>_st p a \<le> \<K>_st p b"
  by (metis \<K>_st_pos blinfun.diff_right diff_ge_0_iff_ge)

lemma \<P>\<^sub>X_mono[intro]: "a \<le> b \<Longrightarrow> \<P>\<^sub>X p n a \<le> \<P>\<^sub>X p n b"
  by (auto simp: \<P>\<^sub>X_def less_eq_bfun_def push_exp.rep_eq intro!: integral_mono)

lemma p_n_\<pi>_MD[intro]: "p \<in> \<Pi>\<^sub>M\<^sub>D \<Longrightarrow> p n \<in> D\<^sub>D"
  by auto

lemma p_n_\<pi>_MR[intro]: "p \<in> \<Pi>\<^sub>M\<^sub>R \<Longrightarrow> p n \<in> D\<^sub>R"
  by auto

lemma step_mono:
  assumes "\<L>\<^sub>b v \<le> v" "d \<in> D\<^sub>R"
  shows "L d v \<le> v"
proof -
  have "\<L>\<^sub>b v \<le> v"
    using assms by blast
  hence "\<And>s. \<L> v s \<le> v s"
    using assms \<L>\<^sub>b.rep_eq   
    by (auto simp: less_eq_bfun_def)
  hence "L d v \<le> \<L>\<^sub>b v"    
    using assms abs_step_bound unfolding less_eq_bfun_def \<L>\<^sub>b.rep_eq \<L>_def L_def 
    by (auto intro!: cSup_upper bounded_imp_bdd_above boundedI[of _ "r\<^sub>M + l * norm v"])
  thus ?thesis
    using assms order.trans by auto
qed

lemma abs_L_le[simp, intro]: "\<bar>L p v s\<bar> \<le> r\<^sub>M + l * norm v"
  unfolding L_def using abs_step_bound
  by (auto intro!: add_mono mult_left_mono)

lemma L_le[simp, intro]: "L p v s \<le> r\<^sub>M + l * norm v"
  unfolding L_def using step_bound by auto

lemma apply_bfun_bounded_above[simp, intro]: "bounded (((f :: 'c \<Rightarrow>\<^sub>b real)) ` X)"
  by (metis Bounded_Functions.norm_bounded bdd_aboveI2 bdd_above_norm image_image)

lemma apply_bfun_bdd_above[simp, intro]: "bdd_above (((f :: 'c \<Rightarrow>\<^sub>b real)) ` X)"
  by (metis apply_bfun_bounded_above bounded_imp_bdd_above)

lemma L_bounded[simp, intro]: "bounded (range (\<lambda>p. L p v s))"
  using abs_L_le by (auto intro!: boundedI)

lemma L_bounded'[simp, intro]: "bounded ((\<lambda>p. L p v s) ` X)"
  by (metis L_bounded bounded_subset image_mono subset_UNIV)

lemma L_bdd_above[simp, intro]: "bdd_above ((\<lambda>p. L p v s) ` X)"
  apply (intro bounded_imp_bdd_above)
  using L_bounded' by blast

lemma step_mono_elem:
  assumes "v \<le> \<L>\<^sub>b v"
  shows "\<forall>e > 0. \<exists>d\<in>D\<^sub>R. v \<le> L d v + e *\<^sub>R 1"
proof -
  have "\<forall>s. v s \<le> (\<Squnion>p\<in>D\<^sub>R. L p v s)"
    using assms unfolding \<L>\<^sub>b.rep_eq \<L>_def less_eq_bfun_def by auto
  hence h1: "\<forall>s. \<forall>e > 0. \<exists>d\<in>D\<^sub>R. v s - e < L d v s"
    apply (subst less_cSUP_iff[symmetric])
    using D\<^sub>R_ne apply simp
    apply auto[1]
    by (metis diff_strict_left_mono diff_strict_mono diff_zero less_eq_real_def)
  have "\<forall>e > 0. \<exists>d\<in>D\<^sub>R. \<forall>s. v s - e < L d v s"
  proof safe
    fix e ::real assume e:"0 < e"
    let ?d = "\<lambda>x. (SOME d. d\<in>D\<^sub>R \<and> v x - e < L d v x) x"
    have "\<forall>x. set_pmf (?d x) \<subseteq> A x \<and> v x - e < L ?d v x"
    proof
      fix x
      have t: "\<exists>d. d \<in> D\<^sub>R \<and> v x - e < L d v x"
        using e h1 by fastforce
      show "set_pmf (?d x) \<subseteq> A x \<and> v x - e < L ?d v x"
        using someI_ex[OF t]
        by (auto simp: is_dec_def L_def \<K>_st.rep_eq push_exp.rep_eq r_dec\<^sub>b.rep_eq K_st_def)
    qed
    thus "\<exists>d\<in>D\<^sub>R. \<forall>x. v x - e < L d v x"
      using is_dec_def by blast
  qed
  thus ?thesis
    by (fastforce simp: less_eq_bfun_def less_eq_real_def diff_less_eq)
qed


lemma \<P>\<^sub>X_Suc_n_elem: "\<P>\<^sub>X p n (\<K>_st (p n) v) = \<P>\<^sub>X p (Suc n) v"
  using \<P>\<^sub>X_Suc_n' \<K>_st.rep_eq by auto

lemma aux_aux_aux_6_2_9':
  assumes "\<L>\<^sub>b v \<le> v" "p \<in> \<Pi>\<^sub>M\<^sub>R"
  shows "\<P>\<^sub>X p n (L (p n) v) \<le> \<P>\<^sub>X p n v"
  using assms step_mono by blast

lemma aux_aux_aux_6_2_9'':
  assumes "\<L>\<^sub>b v \<le> v"
  assumes "p \<in> \<Pi>\<^sub>M\<^sub>R"
  shows "(\<P>\<^sub>X p n (r_dec\<^sub>b (p n)) + l *\<^sub>R (\<P>\<^sub>X p (Suc n) v)) \<le> \<P>\<^sub>X p n v"
proof -
  have "\<P>\<^sub>X p n (L (p n) v) = \<P>\<^sub>X p n (r_dec\<^sub>b (p n)) +  l *\<^sub>R (\<P>\<^sub>X p (Suc n) v)"
    by (auto simp add: \<P>\<^sub>X_Suc_n_elem L_def linear_simps)
  thus ?thesis
    using aux_aux_aux_6_2_9'[OF assms] by metis
qed

lemma aux_6_2_9_fin:
  assumes "\<L>\<^sub>b v \<le> v"
  assumes "p \<in> \<Pi>\<^sub>M\<^sub>R"
  shows "((\<Sum>i \<le> n. l^i *\<^sub>R \<P>\<^sub>X p i (r_dec\<^sub>b (p i))) + l^(Suc n) *\<^sub>R \<P>\<^sub>X p (Suc n) v) \<le> v"
proof (induction n)
  case 0
  then show ?case
    using assms step_mono aux_aux_aux_6_2_9''[of _ _ 0]
    by (auto simp add: L_def K_st_def \<P>\<^sub>X_Suc_n_elem \<K>_st.rep_eq p_n_\<pi>_MR)
next
  case (Suc n)
  have "((\<Sum>i \<le> Suc n. l^i *\<^sub>R \<P>\<^sub>X p i (r_dec\<^sub>b (p i))) + l^(Suc (Suc n)) *\<^sub>R \<P>\<^sub>X p (Suc (Suc n)) v) = 
    ((\<Sum>i \<le> n. l^i *\<^sub>R \<P>\<^sub>X p i (r_dec\<^sub>b (p i))) 
      + l^(Suc n) *\<^sub>R (\<P>\<^sub>X p (Suc n) (r_dec\<^sub>b (p (Suc n))) + l *\<^sub>R \<P>\<^sub>X p (Suc (Suc n)) v))"
    by (simp add: scaleR_add_right)
  also have "\<dots> \<le> ((\<Sum>i \<le> n. l^i *\<^sub>R \<P>\<^sub>X p i (r_dec\<^sub>b (p i))) + l^(Suc n) *\<^sub>R (\<P>\<^sub>X p (Suc n) v))"
    using aux_aux_aux_6_2_9''[OF assms]
    by (auto simp: scaleR_left_mono intro!: mult_left_mono)
  also have "\<dots> \<le> v"
    using Suc.IH .
  finally show ?case .
qed

lift_definition \<nu>\<^sub>b_fin :: "nat \<Rightarrow> ('s, 'a) pol \<Rightarrow> 's \<Rightarrow>\<^sub>b real" is "\<lambda>n p s. \<nu>_fin p s n"
  using \<nu>_fin_bfun
  by auto

lemma aux_6_2_9:
  assumes "\<L>\<^sub>b v \<le> v"
  assumes "p \<in> \<Pi>\<^sub>M\<^sub>R"
  shows "l^Suc n *\<^sub>R \<P>\<^sub>X p (Suc n) v - (\<Sum>i. l^(i+Suc n) *\<^sub>R \<P>\<^sub>X p (i + Suc n) (r_dec\<^sub>b (p (i + Suc n))))
    \<le> (v - (\<Sum>i. l^i *\<^sub>R \<P>\<^sub>X p i (r_dec\<^sub>b (p i))))" 
proof -
  have aux: "(\<Sum>i. l^i *\<^sub>R \<P>\<^sub>X p i (r_dec\<^sub>b (p i))) =
    (\<Sum>i. l^(i+ Suc n) *\<^sub>R \<P>\<^sub>X p (i+Suc n) (r_dec\<^sub>b (p (i + Suc n)))) 
    + (\<Sum>i<Suc n. l^i *\<^sub>R \<P>\<^sub>X p i (r_dec\<^sub>b (p i)))"
    apply (subst suminf_split_initial_segment[symmetric])
    by auto
  thus ?thesis
    using aux_6_2_9_fin[OF assms]
    by (auto simp add: add.commute lessThan_Suc_atMost le_diff_eq)
qed

lemma rhs_bound: "(\<lambda>n. norm (\<Sum>i. l^(i+Suc n) *\<^sub>R \<P>\<^sub>X p (i + Suc n) (r_dec\<^sub>b (p (i + Suc n))))) \<longlonglongrightarrow> 0"
proof- 
  have rhs_aux: "\<And>n p. 
    norm (\<Sum>k. l^(k + n) *\<^sub>R \<P>\<^sub>X p (k + n) (r_dec\<^sub>b (p (k + n)))) \<le> l^n * (r\<^sub>M/(1 - l))"
  proof -
    fix n p
    have aux: "(\<Sum>k. l^(k + n) *\<^sub>R \<P>\<^sub>X p (k + n) (r_dec\<^sub>b (p (k+n)))) = 
      l^n *\<^sub>R (\<Sum>k. (l^k *\<^sub>R \<P>\<^sub>X p (k + n) (r_dec\<^sub>b (p (k+n)))))"
      apply (subst suminf_scaleR_right)
      using \<P>\<^sub>X_bound_r
      by (auto simp: suminf_scaleR_right[symmetric] power_add intro!: suminf_cong boundedI[of _ r\<^sub>M])
    have "norm (\<Sum>k. (l^k *\<^sub>R \<P>\<^sub>X p (k + n) (r_dec\<^sub>b (p (k+n))))) \<le>
          (\<Sum>k. norm (l^k *\<^sub>R \<P>\<^sub>X p (k + n) (r_dec\<^sub>b (p (k+n)))))"
      using \<P>\<^sub>X_bound_r
      by (fastforce intro!: Series.summable_norm boundedI[of _ r\<^sub>M])
    also have "\<dots> \<le> (\<Sum>k. l^k * r\<^sub>M)"
      using \<P>\<^sub>X_bound_r by (auto simp: mult_mono intro!: suminf_le boundedI[of _ r\<^sub>M])
    also have "\<dots> \<le>  r\<^sub>M /(1-l)"
      using sum_disc_lim by simp
    finally have "norm (\<Sum>k. (l^k *\<^sub>R \<P>\<^sub>X p (k + n) (r_dec\<^sub>b (p (k+n))))) \<le> r\<^sub>M /(1-l)" .
    thus "norm (\<Sum>k. l^(k + n) *\<^sub>R \<P>\<^sub>X p (k + n) (r_dec\<^sub>b (p (k+n)))) \<le> l^n * (r\<^sub>M/(1 - l))"
      using aux mult_left_mono by fastforce
  qed
  have tendsto0: "(\<lambda>n. (l^n * (r\<^sub>M/(1 - l)))) \<longlonglongrightarrow> 0" 
    apply (intro tendsto_eq_intros) by auto
  hence "(\<lambda>n. norm (l^n * (r\<^sub>M/(1 - l)))) \<longlonglongrightarrow> 0"
    using zero_le_disc tendsto_norm_zero_iff by fastforce
  have aux: "\<And>p x. norm (\<Sum>i. l ^ (i + Suc x) *\<^sub>R \<P>\<^sub>X p (i + Suc x) (r_dec\<^sub>b (p (i + Suc x)))) \<le> 
    l ^ Suc x * (r\<^sub>M / (1 - l))"
    using rhs_aux by blast
  show "\<And>p. (\<lambda>n. norm (\<Sum>i. l^(i+Suc n) *\<^sub>R \<P>\<^sub>X p (i + Suc n) (r_dec\<^sub>b (p (i + Suc n))))) \<longlonglongrightarrow> 0"
    apply (rule Lim_null_comparison[where g = "\<lambda>n. (l^(Suc n) * (r\<^sub>M/(1 - l)))"])
    using aux tendsto0 
    by (auto simp only: eventually_True abs_norm_cancel real_norm_def mult.assoc 
        intro!: LIMSEQ_Suc tendsto_zero_mult_left_iff)
qed

(* 6.2.2 in Puterman *)
lemma aux_6_2_2:
  assumes "\<L>\<^sub>b v \<le> v"
  assumes "p \<in> \<Pi>\<^sub>M\<^sub>R"
  shows "\<nu>\<^sub>b (mk_markovian p) \<le> v"
proof -
  have aux: "(\<lambda>n. l^n * norm v) \<longlonglongrightarrow> 0"
    by (auto intro!: tendsto_eq_intros)
  have "\<And>n. norm (l^n *\<^sub>R \<P>\<^sub>X p n v) \<le> l^n * norm v"
    by (metis (no_types, lifting) \<P>\<^sub>X_bounded_linear linear_simps(5) norm_\<P>\<^sub>X_apply norm_l_pow_eq)
  hence lhs_bound: "(\<lambda>n. norm (l^n *\<^sub>R \<P>\<^sub>X p n v)) \<longlonglongrightarrow> 0"
    apply (subst Lim_transform_bound[where g = "\<lambda>n. (l^n * norm v)"])
    using aux by auto
  have "(\<lambda>n. (l^n *\<^sub>R \<P>\<^sub>X p n v)) \<longlonglongrightarrow> 0"
    using tendsto_norm_zero_cancel[OF lhs_bound] .
  hence lhs_bound': "(\<lambda>n. (l^(Suc n) *\<^sub>R \<P>\<^sub>X p (Suc n) v)) \<longlonglongrightarrow> 0"
    apply (intro LIMSEQ_Suc).
  moreover have "(\<lambda>n. (\<Sum>i. l^(i+Suc n) *\<^sub>R \<P>\<^sub>X p (i + Suc n) (r_dec\<^sub>b (p (i + Suc n))))) \<longlonglongrightarrow> 0"
    using tendsto_norm_zero_cancel[OF rhs_bound] .
  ultimately have 
    "(\<lambda>n. (l^(Suc n) *\<^sub>R \<P>\<^sub>X p (Suc n) v) - 
    (\<Sum>i. l^(i+Suc n) *\<^sub>R \<P>\<^sub>X p (i + Suc n) (r_dec\<^sub>b (p (i + Suc n)))))  \<longlonglongrightarrow> 0 - 0"
    by (fast intro!: tendsto_diff)
  hence k: "\<And>x. (\<lambda>n. ((l^(Suc n) *\<^sub>R \<P>\<^sub>X p (Suc n) v) - 
    (\<Sum>i. l^(i+Suc n) *\<^sub>R \<P>\<^sub>X p (i + Suc n) (r_dec\<^sub>b (p (i + Suc n))))) x)  \<longlonglongrightarrow> 0"
    using bfun_tendsto_apply_bfun by fastforce
  have "\<And>x. 0 \<le> (v -(\<Sum>i. l^i *\<^sub>R \<P>\<^sub>X p i (r_dec\<^sub>b (p i)))) x"
    apply (subst lim_mono[OF _ k, where Y="\<lambda>n. (v - (\<Sum>i. l^i *\<^sub>R \<P>\<^sub>X p i (r_dec\<^sub>b (p i)))) _"])
    using aux_6_2_9 assms by (auto simp: less_eq_bfun_def)
  hence "0 \<le> (v - (\<Sum>i. l^i *\<^sub>R \<P>\<^sub>X p i (r_dec\<^sub>b (p i))))"
    by (simp add: less_eq_bfun_def)
  thus ?thesis
    by (simp add: \<nu>\<^sub>b_eq_\<P>\<^sub>X)
qed

lemma lemma_6_2_2_a: 
  assumes "\<L>\<^sub>b v \<le> v" 
  shows "\<nu>\<^sub>b_opt \<le> v"
proof -
  have "\<forall>p\<in>\<Pi>\<^sub>M\<^sub>R. \<nu>\<^sub>b (mk_markovian p) \<le> v"
    using assms aux_6_2_2 by blast
  hence "\<And>x. (\<Squnion>p\<in>\<Pi>\<^sub>M\<^sub>R. \<nu>\<^sub>b (mk_markovian p) x) \<le> v x"
    using is_policy_def policies_ne
    by (auto simp: less_eq_bfun_def
        intro!: cSUP_least bounded_imp_bdd_above boundedI)
  thus ?thesis
    by (simp add: \<nu>\<^sub>b.rep_eq less_eq_bfun_def \<nu>_MR_eq_HR)
qed

lemma \<K>_st_bfun_one[simp]:"\<K>_st p 1 = 1"
  by (auto intro!: bfun_eqI simp: \<K>_st.rep_eq push_exp.rep_eq)

lemma [simp]: "((\<K>_st p)^^t) 1 = 1"
  by (induction t) auto

lemma "((\<Sum>i. l^i *\<^sub>R \<K>_st d^^i) o\<^sub>L (id_blinfun - l *\<^sub>R (\<K>_st d))) = id_blinfun"
  apply (subst inv_norm_le(2)[symmetric, where Q="(l *\<^sub>R \<K>_st d)"])
  apply auto
  by (metis (no_types, lifting) blincomp_scaleR_right inv_norm_le(2) norm_\<K>_st_l_less suminf_cong)

lemma lemma_6_2_2_b:
  assumes "v \<le> \<L>\<^sub>b v"
  shows "v \<le> \<nu>\<^sub>b_opt"
proof -
  have "\<And>s. \<forall>e>0. v s \<le> \<nu>_opt s + (e/(1-l))"
  proof (safe)
    fix s
    fix e ::real assume "e > 0"
    then obtain d where "d\<in>D\<^sub>R" and hd: "v \<le> (L d v + e *\<^sub>R 1)"
      using assms step_mono step_mono_elem by force
    hence "(\<Sum>i. l^i *\<^sub>R \<K>_st d^^i) v \<le> (\<Sum>i. l^i *\<^sub>R \<K>_st d^^i) (L d v + e*\<^sub>R 1)"
      using lemma_6_1_2_b \<K>_st_def by auto
    hence "(\<Sum>i. l^i *\<^sub>R \<K>_st d^^i) v \<le> 
      ((\<Sum>i. l^i *\<^sub>R \<K>_st d^^i) (l *\<^sub>R (\<K>_st d) v) + (\<Sum>i. l^i *\<^sub>R \<K>_st d^^i) (r_dec\<^sub>b d + e*\<^sub>R 1))"
      by (simp add: L_def add.commute add.left_commute blinfun.add_right)
    hence "((\<Sum>i. l^i *\<^sub>R \<K>_st d^^i) (v - l *\<^sub>R (\<K>_st d) v)) \<le> 
      ((\<Sum>i. l^i *\<^sub>R \<K>_st d^^i) (r_dec\<^sub>b d + e*\<^sub>R 1))"
      by (simp add: add.commute blinfun.diff_right diff_le_eq)
    hence "((\<Sum>i. l^i *\<^sub>R \<K>_st d^^i) ((id_blinfun - l *\<^sub>R (\<K>_st d)) v)) \<le> 
      ((\<Sum>i. l^i *\<^sub>R \<K>_st d^^i) (r_dec\<^sub>b d + e*\<^sub>R 1))"
      by (simp add: minus_blinfun.rep_eq scaleR_blinfun.rep_eq)
    hence "((\<Sum>i. l^i *\<^sub>R \<K>_st d^^i) o\<^sub>L (id_blinfun - l *\<^sub>R (\<K>_st d))) v \<le> 
      (\<Sum>i. l^i *\<^sub>R \<K>_st d^^i) (r_dec\<^sub>b d + e*\<^sub>R 1)"
      by simp
    hence "id_blinfun v \<le> (\<Sum>i. l^i *\<^sub>R \<K>_st d^^i) (r_dec\<^sub>b d + e*\<^sub>R 1)"
      apply (subst inv_norm_le(2)[symmetric, where Q="(l *\<^sub>R \<K>_st d)"])
      by (auto simp add: blincomp_scaleR_right)
    hence aux: "v \<le> ((\<Sum>i. l^i *\<^sub>R \<K>_st d^^i) (r_dec\<^sub>b d) + e *\<^sub>R(\<Sum>i. l^i *\<^sub>R \<K>_st d^^i) 1)"
      by (simp add: blinfun.add_right blinfun.scaleR_right)
    have "summable (\<lambda>i. l^i *\<^sub>R \<K>_st d^^i)"
      using convergent_disc_\<K>_st summable_iff_convergent'
      by (simp add: summable_iff_convergent')
    hence "v \<le> ((\<Sum>i. l^i *\<^sub>R \<K>_st d^^i) (r_dec\<^sub>b d) + e *\<^sub>R((\<Sum>i. (l^i *\<^sub>R \<K>_st d^^i) 1)))"
      apply (subst bounded_linear.suminf[OF _, symmetric, where f = "\<lambda>x. blinfun_apply x 1"])
      using aux by auto
    hence "v \<le> ((\<Sum>i. l^i *\<^sub>R \<K>_st d^^i) (r_dec\<^sub>b d) + e *\<^sub>R((\<Sum>i. l^i *\<^sub>R  ((\<K>_st d^^i) 1))))"
      by (simp add: scaleR_blinfun.rep_eq)
    hence "v \<le> ((\<Sum>i. l^i *\<^sub>R \<K>_st d^^i) (r_dec\<^sub>b d) + e *\<^sub>R (\<Sum>i. l^i *\<^sub>R  1))"
      by simp
    hence "v \<le> ((\<Sum>i. l^i *\<^sub>R \<K>_st d^^i) (r_dec\<^sub>b d) + e *\<^sub>R ((\<Sum>i. l^i) *\<^sub>R  1))"
      apply (subst bounded_linear.suminf[where f = "\<lambda>x. x *\<^sub>R 1"])
      by (auto simp add: bounded_linear_scaleR_left summable_geometric)
    hence "v \<le> ((\<Sum>i. l^i *\<^sub>R \<K>_st d^^i) (r_dec\<^sub>b d) + e *\<^sub>R (1/(1-l)) *\<^sub>R  1)"
      by (simp add: suminf_geometric)
    hence "v \<le> ((\<Sum>i. l^i *\<^sub>R \<K>_st d^^i) (r_dec\<^sub>b d) + (e/(1-l)) *\<^sub>R  1)"
      by simp
    hence aux: "v \<le> (\<nu>\<^sub>b (mk_stationary d) + (e/(1-l)) *\<^sub>R  1)"
      using \<nu>_stationary r_dec\<^sub>b_def by auto
    hence aux: "\<And>s. v s \<le> (\<nu>\<^sub>b (mk_stationary d) + (e/(1-l)) *\<^sub>R  1) s"
      by (auto simp: less_eq_bfun_def)
    show "v s \<le> \<nu>_opt s + (e/(1-l))"
      using \<open>d \<in> D\<^sub>R\<close> 
      by (auto simp: is_policy_def mk_markovian_def \<nu>\<^sub>b.rep_eq less_eq_bfun_def 
          intro!: \<nu>_HR_le order_trans[OF aux])
  qed
  hence "\<And>s. \<forall>e>0. v s \<le> \<nu>_opt s + e"
  proof safe
    fix s
    fix e :: real assume "e > 0"
    have "e * (1 - l) > 0"
      by (simp add: \<open>0 < e\<close>)
    hence "v s \<le> \<nu>_opt s + ((e * (1 - l)) / (1 - l))"
      using \<open>\<forall>e>0. v s \<le> \<nu>_opt s + (e / (1 - l))\<close> by blast
    thus "v s \<le> \<nu>_opt s + e"
      using disc_lt_one by auto
  qed
  thus ?thesis
    by (auto simp: less_eq_bfun_def intro: field_le_epsilon)
qed

lemma lemma_6_2_2_c:
  assumes "v = \<L>\<^sub>b v"
  shows "v = \<nu>\<^sub>b_opt"
  using lemma_6_2_2_a
  using assms dual_order.antisym[OF lemma_6_2_2_a lemma_6_2_2_b]
  by auto

lemma bounded_step: "bounded (range (\<lambda>p. r_dec\<^sub>b p + l *\<^sub>R (\<K>_st p) v))"
  apply (intro boundedI[of _ "r\<^sub>M + l * norm v"])
  using norm_step_bound by auto

lemma bounded_P: "bounded (\<K>_st ` X)"
  by (auto simp: bounded_iff)


lemma contraction_\<L>: "dist (\<L>\<^sub>b v) (\<L>\<^sub>b  u) \<le> l * dist v u"
proof -
  have aux: "\<And>s u v. (\<L>\<^sub>b v s) \<ge> (\<L>\<^sub>b u s) \<Longrightarrow>  dist(\<L>\<^sub>b v s) (\<L>\<^sub>b u s) \<le> l * dist v u"
  proof -
    fix s
    fix v u :: "'s \<Rightarrow>\<^sub>b real"
    assume lea: "(\<L>\<^sub>b v s) \<ge> (\<L>\<^sub>b u s)"
    have "\<L>\<^sub>b v s - \<L>\<^sub>b u s \<le> (\<Squnion>p \<in> D\<^sub>R. L p v  s) - (\<Squnion>p \<in> D\<^sub>R. L p u s)"
      unfolding \<L>\<^sub>b.rep_eq \<L>_def by auto
    also have "\<dots> \<le> (\<Squnion>p \<in> D\<^sub>R. (L p v s) - (L p u s))"
      using ex_dec calculation lea by (fastforce intro!: le_SUP_diff')
    also have "\<dots> = (\<Squnion>p \<in> D\<^sub>R. ((l *\<^sub>R  (\<K>_st p v - \<K>_st p u)) s))"
      by (simp add: L_def scale_right_diff_distrib)
    also have "\<dots> = (\<Squnion>p \<in> D\<^sub>R. l * (\<K>_st p (v - u) s))"
      by (auto simp: blinfun.diff_right)
    also have "\<dots> = l * (\<Squnion>p \<in> D\<^sub>R. (\<K>_st p (v - u)) s)"
      apply (intro bounded_SUP_mul) using D\<^sub>R_ne
      by (auto simp: bounded_P intro!: bounded_apply_blinfun bounded_apply_bfun)
    also have "\<dots> \<le> l * norm (\<Squnion>p \<in> D\<^sub>R. (\<K>_st p (v - u)) s)"
      by (simp add: mult_left_mono)
    also have "\<dots> \<le> l * (\<Squnion>p \<in> D\<^sub>R. norm ((\<K>_st p (v - u)) s))"
    proof -
      have "bounded ((\<lambda>x. norm ((\<K>_st x (v - u)) s)) ` D\<^sub>R)"
        apply (subst bounded_norm_comp)
        by (auto simp: bounded_P bounded_apply_blinfun bounded_apply_bfun)
      hence aux: "bounded ((\<lambda>x. \<bar>((\<K>_st x (v - u)) s)\<bar>) ` D\<^sub>R)"
        by auto
      thus ?thesis
        using abs_cSUP_le[OF _ aux] mult_left_mono zero_le_disc
      proof -
        have "bounded ((\<lambda>f. ((\<K>_st f) (v - u)) s) ` D\<^sub>R)"
          using \<open>bounded ((\<lambda>x. norm (((\<K>_st x) (v - u)) s)) ` D\<^sub>R)\<close> bounded_norm_comp by blast
        then have "\<bar>\<Squnion>f\<in>D\<^sub>R. apply_bfun ((\<K>_st f) (v - u)) s\<bar> \<le> (\<Squnion>f\<in>D\<^sub>R. norm ((\<K>_st f (v - u)) s))"
          using D\<^sub>R_ne by (auto simp add: abs_cSUP_le)
        then show ?thesis
          by (simp add: mult_left_mono)
      qed
    qed
    also have "\<dots> \<le> l * (\<Squnion>p \<in> D\<^sub>R. norm (\<K>_st p ((v - u))))"
      apply (intro mult_left_mono cSUP_mono)
      using D\<^sub>R_ne abs_le_norm_bfun
      by (auto simp: bounded_P bounded_apply_blinfun bounded_norm_comp 
          intro!: abs_le_norm_bfun bounded_imp_bdd_above)
    also have "\<dots> \<le> l * (\<Squnion>p \<in> D\<^sub>R. norm ((v - u)))"
      using norm_push_exp_le_norm D\<^sub>R_ne
      by (fastforce simp add: \<K>_st.rep_eq intro!: mult_left_mono cSUP_mono)
    also have "\<dots> = l * dist v u"
      using D\<^sub>R_ne by (auto simp: dist_norm)
    finally have aux: "\<L>\<^sub>b v s - \<L>\<^sub>b u s \<le> l * dist v u".
    thus  "dist(\<L>\<^sub>b v s) (\<L>\<^sub>b u s) \<le> l * dist v u"
      using aux by (simp add: dist_real_def lea)
  qed
  hence aux: "\<And>u v s. \<L>\<^sub>b u s \<le> \<L>\<^sub>b v s \<Longrightarrow> dist (\<L>\<^sub>b v s) (\<L>\<^sub>b u s) \<le> l * dist v u"
    by auto
  moreover have "\<And>u v s. \<L>\<^sub>b v s \<le> \<L>\<^sub>b u s \<Longrightarrow> dist (\<L>\<^sub>b v s) (\<L>\<^sub>b u s) \<le> l * dist v u"
    by (simp add: aux dist_commute)
  ultimately have "\<And>u v s. dist (\<L>\<^sub>b v s) (\<L>\<^sub>b u s) \<le> l * dist v u"
    using linear by blast
  thus "\<And>u v. dist (\<L>\<^sub>b v) (\<L>\<^sub>b u) \<le> l * dist v u"
    by (simp add: Bounded_Functions.dist_bound)
qed

lemma lemma_6_2_4: "is_contraction \<L>\<^sub>b"
  using contraction_\<L>
  unfolding is_contraction_def
  using zero_le_disc disc_lt_one
  by blast

lemma \<L>\<^sub>b_conv:
  shows "\<exists>!v. \<L>\<^sub>b v = v" "\<And>v. (\<lambda>n. (\<L>\<^sub>b ^^ n) v) \<longlonglongrightarrow> (THE v. \<L>\<^sub>b v = v)"
  using banach'[OF lemma_6_2_4]
  by auto

lemma contraction_L: "dist (L p v) (L p  u) \<le> l * dist v u"
proof -
  have aux: "\<And>s u v. (L p v s) \<ge> (L p u s) \<Longrightarrow>  L p v s - L p u s \<le> l * dist v u"
  proof -
    fix v u :: "'s \<Rightarrow>\<^sub>b real"
    fix s
    assume lea: "(L p v s) \<ge> (L p u s)"
    have "L p v s - L p u s = (l *\<^sub>R  (\<K>_st p v - \<K>_st p u)) s"
      by (simp add: L_def scale_right_diff_distrib)
    also have "\<dots> \<le> l * (\<K>_st p (v -u)) s"
      by (auto simp: blinfun.diff_right)
    also have "\<dots> \<le> l * norm (\<K>_st p (v - u) s)"
      by (simp add: mult_left_mono)
    also have "\<dots> \<le> l * norm (\<K>_st p (v - u))"
      by (meson Bounded_Functions.norm_bounded mult_left_mono zero_le_disc)
    also have "\<dots> \<le> l * dist v u"
      by (simp add: \<K>_st.rep_eq mult_left_mono norm_push_exp_le_norm dist_norm)
    finally show "(L p v) s -  (L p u) s \<le> l * dist v u"
      by auto
  qed
  have "\<And>v u s. dist(L p v s) (L p u s) \<le> l * dist v u"
    subgoal for v u s
      apply (cases  "(L p v s) \<ge> (L p u s)")
    unfolding dist_real_def using dist_commute
    apply (intro order.trans[OF _ aux, of _ _ s])
    apply auto
    by (simp add: aux dist_commute)
  done
  thus "dist (L p v) (L p u) \<le> l * dist v u"
    by (simp add: Bounded_Functions.dist_bound)
qed

lemma lemma_6_2_4_L: "is_contraction (L p)"
  unfolding is_contraction_def
  using contraction_L disc_lt_one zero_le_disc by blast

lemma lemma_6_2_5_a[simp]: "\<L>\<^sub>b v = v \<longleftrightarrow> v = \<nu>\<^sub>b_opt"
  using banach'(1) lemma_6_2_4 lemma_6_2_2_c by metis

lemma \<nu>\<^sub>b_opt_fix: "\<nu>\<^sub>b_opt = (THE v. \<L>\<^sub>b v = v)"
  using lemma_6_2_5_a by auto

lemma \<L>\<^sub>b_opt[simp]: "\<L>\<^sub>b \<nu>\<^sub>b_opt = \<nu>\<^sub>b_opt"
  using lemma_6_2_5_a by auto

lemma lemma_6_2_5_b: "L d v = v \<longleftrightarrow> v = \<nu>\<^sub>b (mk_stationary d)"
  using L_\<nu>_fix_iff .

lemma thm_6_2_6: "\<nu> p = \<nu>_opt \<longleftrightarrow> \<L>\<^sub>b (\<nu>\<^sub>b p) = \<nu>\<^sub>b p"
  by (metis \<nu>\<^sub>b.abs_eq \<nu>\<^sub>b.rep_eq \<nu>\<^sub>b_opt.rep_eq \<nu>\<^sub>b_opt_def lemma_6_2_5_a)

lemma \<L>\<^sub>b_lim:
  shows "\<And>v. (\<lambda>n. (\<L>\<^sub>b ^^ n) v) \<longlonglongrightarrow> \<nu>\<^sub>b_opt"
  using \<L>\<^sub>b_conv(2) \<nu>\<^sub>b_opt_fix by presburger

lemma step_v_le: "\<bar>r (s, x) + l * measure_pmf.expectation (K (s, x)) (apply_bfun v)\<bar> \<le> 
  r\<^sub>M + l * norm v"
  apply (auto intro!: order_trans[OF abs_triangle_ineq] add_mono simp: abs_mult)
  using r_bound apply blast
  apply (intro mult_mono)
  apply (auto intro!: order_trans[OF integral_abs_bound] measure_pmf.integral_le_const norm_bounded)
  by (metis (mono_tags, lifting) eventuallyI norm_le_norm_bfun real_norm_def)

lemma bounded_range_step: 
  "bounded (range (\<lambda>x. r (s, x) + l * measure_pmf.expectation (K (s, x)) (apply_bfun v)))"
  using step_v_le by (auto intro!: boundedI)

lemma bounded_abs[intro]: 
  "bounded (X' :: real set) \<Longrightarrow> bounded (abs ` X')"
  by (auto simp: bounded_iff)

lemma bounded_abs_range[intro]: 
  "bounded (range f :: real set) \<Longrightarrow> bounded (range (\<lambda>x. abs (f x)))"
  by (auto simp: bounded_iff)

abbreviation "L\<^sub>a a v s \<equiv> r (s, a) + l * measure_pmf.expectation (K (s,a)) v"

lemma SUP_step_MR_eq: 
  "(\<Squnion>d \<in> D\<^sub>R. L d v s) = (\<Squnion>pa \<in> {pa. set_pmf pa \<subseteq> A s}. (\<integral>a. L\<^sub>a a v s \<partial>measure_pmf pa))"
proof (intro antisym)
  show "(\<Squnion>d\<in>D\<^sub>R. L d v s) \<le> (\<Squnion>pa\<in>{pa. set_pmf pa \<subseteq> A s}. 
    measure_pmf.expectation pa (\<lambda>a. L\<^sub>a a v s))"
    apply (intro cSUP_mono)
    using D\<^sub>R_ne apply simp
    subgoal
      apply (intro bounded_imp_bdd_above)
      apply (intro boundedI[where B = "r\<^sub>M + l * norm v"])
      using bounded_range_step step_v_le
      by (auto intro!: order_trans[OF integral_abs_bound] 
          measure_pmf.integral_le_const bounded_integrable)
    subgoal
      apply auto
      apply (subst Bochner_Integration.integral_add)
      subgoal using r_bound by (fastforce intro!: bounded_integrable simp: bounded_iff)
      subgoal apply simp apply (intro disjI2) apply (intro bounded_integrable)
        apply (intro boundedI[of _ "norm v"])
        apply (auto simp: bounded_iff intro!: order_trans[OF integral_abs_bound] 
            measure_pmf.integral_le_const bounded_integrable )
        by (metis AE_pmfI norm_le_norm_bfun real_norm_def)
      unfolding L_def
      apply (auto simp: measure_pmf_bind L_def r_dec\<^sub>b.rep_eq \<K>_st.rep_eq push_exp.rep_eq K_st_def)
      apply (subst integral_bind[where K="count_space UNIV", where B = "norm v"])
      apply (auto simp add: is_dec_def measure_pmf_in_subprob_algebra intro: abs_le_norm_bfun)
      by fastforce
    done
  have aux: "{pa. set_pmf pa \<subseteq> A s} \<noteq> {}"
    using D\<^sub>R_ne is_dec_def by auto
  show 
    "(\<Squnion>pa\<in>{pa. set_pmf pa \<subseteq> A s}. measure_pmf.expectation pa (\<lambda>a. L\<^sub>a a v s)) \<le> (\<Squnion>d\<in>D\<^sub>R. L d v s)"
  proof (intro cSUP_least[OF aux], intro cSUP_upper2)
    fix n assume h: "n \<in> {pa. set_pmf pa \<subseteq> A s}"
    show "measure_pmf.expectation n (\<lambda>a. L\<^sub>a a v s) \<le> 
      L (\<lambda>s'. if s = s' then n else SOME a. set_pmf a \<subseteq> A s') v s"
      unfolding L_def
      apply simp
      apply (auto simp: r_dec\<^sub>b.rep_eq \<K>_st.rep_eq push_exp.rep_eq bind_return_pmf h A_ne some_in_eq)
      apply (subst Bochner_Integration.integral_add)
      subgoal using r_bound by (fastforce intro!: bounded_integrable simp: bounded_iff )
      subgoal 
        apply (auto intro!: bounded_integrable boundedI[of _ "norm v"] )
        apply (auto intro!: order_trans[OF integral_abs_bound] 
            measure_pmf.integral_le_const bounded_integrable)
        by (metis AE_pmfI norm_le_norm_bfun real_norm_def)
      apply (auto simp: measure_pmf_bind K_st_def)
      apply (subst integral_bind[where K="count_space UNIV", where B = "norm v"])
      by (auto intro: abs_le_norm_bfun simp: measure_pmf_in_subprob_algebra)
    have aux: "\<And>sa. \<exists>a. set_pmf a \<subseteq> A sa"
      using ex_dec is_dec_def by blast
    show "(\<lambda>s'. if s = s' then n else SOME a. set_pmf a \<subseteq> A s') \<in> D\<^sub>R "
      using A_ne some_in_eq D\<^sub>R_ne verit_sko_ex'
      unfolding is_dec_def using \<open>n \<in> {pa. set_pmf pa \<subseteq> A s}\<close> using mem_Collect_eq using someI_ex
      using  someI_ex[OF aux] by auto
    show "\<And>x. x \<in> {pa. set_pmf pa \<subseteq> A s} \<Longrightarrow> bdd_above ((\<lambda>d. apply_bfun (L d v) s) ` D\<^sub>R)"
      by (fastforce intro!: bounded_imp_bdd_above simp: bounded_def)
  qed
qed

lemma L_eq_L\<^sub>a: "d \<in> D\<^sub>R \<Longrightarrow> L d v s = measure_pmf.expectation (d s) (\<lambda>a. L\<^sub>a a v s)"   
  apply (auto simp: bind_return_pmf L_def r_dec\<^sub>b.rep_eq \<K>_st.rep_eq push_exp.rep_eq K_st_def)
  apply (subst Bochner_Integration.integral_add)
  apply (intro measure_pmf.integrable_const_bound[of _ r\<^sub>M])
  apply (simp add: AE_measure_pmf_iff)
  using r_bound apply blast
  apply simp
  apply (intro Bochner_Integration.integrable_mult_right)
  apply (intro measure_pmf.integrable_const_bound[of _ "norm v"])
  apply (auto simp: AE_measure_pmf_iff)
  apply (intro order.trans[OF integral_abs_bound])
  apply (intro prob_space.integral_le_const)
  apply auto
  apply (meson measure_pmf.prob_space_axioms)
  apply (meson AE_pmfI abs_le_norm_bfun)
  apply (subst (asm) measure_pmf_bind)
  apply (subst (asm) Giry_Monad.integral_bind[where K = "count_space UNIV", where B = "norm v"])
  apply auto
  apply (meson abs_le_norm_bfun)
  by (simp add: measure_pmf_in_subprob_space)

lemma SUP_step_det_eq: "(\<Squnion>d \<in> D\<^sub>D. L (mk_dec_det d) v s) = (\<Squnion>a \<in> A s. L\<^sub>a a v s)"
  apply (intro antisym)
  apply (intro cSUP_mono)
  apply simp
  using bounded_range_step apply (fastforce intro!: bounded_imp_bdd_above simp: bounded_def)
  subgoal
    unfolding mk_dec_det_def is_dec_det_def
    by (auto simp: bind_return_pmf L_def r_dec\<^sub>b.rep_eq \<K>_st.rep_eq push_exp.rep_eq K_st_def)
  apply (intro cSUP_mono)
  apply (simp add: A_ne)
  subgoal unfolding r_dec\<^sub>b.rep_eq \<K>_st.rep_eq push_exp.rep_eq bind_return_pmf by auto
  apply (intro bexI[of _ "\<lambda>s'. if s = s' then _ else SOME a. a \<in> A s'"])
  unfolding is_dec_det_def mk_dec_det_def
  by (auto simp: K_st_def L_def  r_dec\<^sub>b.rep_eq \<K>_st.rep_eq push_exp.rep_eq bind_return_pmf 
      A_ne some_in_eq)

lemma lemma_4_3_1': 
  assumes "set_pmf p \<subseteq> W" "bounded ((w :: 'c \<Rightarrow> real) ` W)" "W \<noteq> {}"
    "measure_pmf.expectation p w = (\<Squnion>((\<lambda>p. measure_pmf.expectation p w) ` {p. set_pmf p \<subseteq> W}))" 
  shows "\<exists>x \<in> W. measure_pmf.expectation p w = w x"
proof -
  have abs_w_le_sup: "\<And>y. y\<in>W \<Longrightarrow> \<bar>w y\<bar> \<le> (\<Squnion>x\<in>W. \<bar>w x\<bar>)"
    apply (intro cSUP_upper)
    apply auto
    by (metis assms(2) bounded_abs bounded_imp_bdd_above image_image)
  have "\<And>x. x \<in> set_pmf p \<Longrightarrow> w x < \<Squnion>(w ` W) \<Longrightarrow> False"
  proof -
    fix x
    assume "x \<in> set_pmf p" "w x < \<Squnion>(w ` W)"
    hence "\<exists>x'. (x' \<in> W \<and> w x < w x')"
      apply auto
      by (metis (mono_tags, hide_lams) assms(3) empty_is_image imageE less_cSupD)
    have "measure_pmf.expectation p w < measure_pmf.expectation (map_pmf (\<lambda>y. 
      if x = y then (SOME x'. x' \<in> W \<and> w x < w x') else y) p) w"
      apply simp
      apply (intro Probability_Mass_Function.measure_pmf.integral_less_AE[where A = "{x}"])
      using assms
      apply (intro measure_pmf.integrable_const_bound[where B = "\<Squnion>((\<lambda>x. \<bar>w x\<bar>) ` W)"])
      apply (simp add: AE_measure_pmf_iff)
      using assms abs_w_le_sup apply auto[1]
      apply simp
      using assms
      apply (intro measure_pmf.integrable_const_bound[where B = "\<Squnion>((\<lambda>x. \<bar>w x\<bar>) ` W)"])
      apply (simp add: AE_measure_pmf_iff)
      using assms abs_w_le_sup apply auto[1]
      apply (intro cSUP_upper)
      apply (metis (mono_tags, lifting) \<open>\<exists>x'. x' \<in> W \<and> w x < w x'\<close> someI_ex)
      apply (metis assms(2) bounded_abs bounded_imp_bdd_above image_image)
      apply simp
      using \<open>x \<in> p\<close> apply auto
        apply (meson emeasure_pmf_single_eq_zero_iff)
       apply eventually_elim
       apply (metis (no_types, lifting) \<open>\<exists>x'. x' \<in> W \<and> w x < w x'\<close> less_le verit_sko_ex')
       apply eventually_elim
      by (metis (no_types, lifting) \<open>\<exists>x'. x' \<in> W \<and> w x < w x'\<close> less_le verit_sko_ex')
    hence "measure_pmf.expectation p w < \<Squnion>((\<lambda>p. measure_pmf.expectation p w) ` {p. set_pmf p \<subseteq> W})"
      apply (subst less_cSUP_iff)
      apply auto
      using assms(1) apply blast
      apply (intro bdd_aboveI[where M = "(\<Squnion>x\<in>W. \<bar>w x\<bar>)"])
      apply (auto intro!: measure_pmf.integral_le_const)
      apply (intro measure_pmf.integrable_const_bound[where B = "\<Squnion>((\<lambda>x. \<bar>w x\<bar>) ` W)"])
      apply auto
      apply (auto simp add: AE_measure_pmf_iff)
      using abs_w_le_sup apply blast
      apply (intro cSUP_upper2)
      apply auto
      apply (intro bdd_aboveI[where M = "(\<Squnion>x\<in>W. \<bar>w x\<bar>)"])
      apply auto
      using abs_w_le_sup apply presburger
      apply (intro 
          exI[of _ "map_pmf (\<lambda>y. (if x = y then (SOME x'. x' \<in> W \<and> w x < w x') else y)) p"])
      apply auto
      apply (metis (no_types, lifting) \<open>\<exists>x'. x' \<in> W \<and> w x < w x'\<close> some_eq_ex)
      using assms(1) by blast
    thus False
      using assms by auto
  qed
  hence "\<And>x.  x\<in> set_pmf p \<Longrightarrow> w x = \<Squnion> (w ` W)"
    by (metis assms(1) assms(2) bounded_imp_bdd_above cSUP_upper less_le subsetD)
  have "(SOME x. x \<in> set_pmf p) \<in> set_pmf p"
    by (metis set_pmf_not_empty some_in_eq)
  hence "w (SOME x. x \<in> set_pmf p) =  \<Squnion> (w ` W)"
    apply auto
    by (meson \<open>\<And>x. x \<in> set_pmf p \<Longrightarrow> w x = \<Squnion> (w ` W)\<close>)
  thus ?thesis
    apply (intro bexI[of _ "SOME x. x \<in> set_pmf p"])
    apply (subst Bochner_Integration.integral_cong_AE[where ?g = "\<lambda>_. \<Squnion> (w ` W)"])
    apply (auto simp: AE_measure_pmf_iff)
    using \<open>\<And>x. x \<in> set_pmf p \<Longrightarrow> w x = \<Squnion> (w ` W)\<close> apply blast
    using \<open>(SOME x. x \<in> set_pmf p) \<in> set_pmf p\<close> assms(1) by blast
qed

lemma lemma_4_3_1: 
  assumes "set_pmf p \<subseteq> W" "integrable (measure_pmf p) w" "bounded ((w :: 'c \<Rightarrow> real) ` W)"
  shows "measure_pmf.expectation p w \<le> \<Squnion>(w ` W)"
  using assms bounded_has_Sup(1) prob_space_measure_pmf
  by (fastforce simp: AE_measure_pmf_iff  intro!: prob_space.integral_le_const)

lemma \<L>_eq_SUP_det: "\<L> v s = (\<Squnion>d \<in> D\<^sub>D. L (mk_dec_det d) v s)"
proof -
  have ge: "(\<Squnion>d \<in> D\<^sub>D. L (mk_dec_det d) v s) \<le> \<L> v s"
    unfolding \<L>_def
    apply (intro cSUP_mono)
    apply simp
    apply simp
    using D_det_to_MR
    unfolding mk_dec_det_def
    by blast
  have le: "\<L> v s \<le> (\<Squnion>d \<in> D\<^sub>D. L (mk_dec_det d) v s)"
    unfolding \<L>_def
    apply (subst SUP_step_MR_eq)
    apply (subst SUP_step_det_eq)
    apply (intro cSUP_least)
    using ex_dec is_dec_def apply blast
    apply (intro lemma_4_3_1)
    apply simp
    apply (intro  Bochner_Integration.integrable_add)
    using r_bound
    apply (auto intro: bfun_prob_space_integrable measure_pmf.integrable_const_bound[of _ "r\<^sub>M"])[1]
    apply (intro integrable_mult_right)
    apply (intro measure_pmf.integrable_const_bound[of _ "norm v"])
    apply (auto intro!: bfun_prob_space_integrable AE_I2)
    apply (intro order_trans[OF integral_abs_bound])
    apply (intro measure_pmf.integral_le_const)
    apply (intro measure_pmf.integrable_const_bound[of _ "norm v"])
    apply (auto simp add: abs_le_norm_bfun intro!: bounded_plus_comp bounded_scaleR_comp)
    apply (auto intro!: boundedI r_bound)[1]
    apply (intro boundedI[where B = "l * norm v"])
    by (fastforce simp: abs_mult abs_le_norm_bfun intro: order_trans 
        intro!: integral_abs_bound measure_pmf.integral_le_const mult_left_mono)
  thus ?thesis using le ge by auto
qed

lemma \<L>\<^sub>b_eq_SUP_det: "\<L>\<^sub>b v s = (\<Squnion>d \<in> D\<^sub>D. L (mk_dec_det d) v s)"
  using \<L>_eq_SUP_det unfolding \<L>\<^sub>b.rep_eq
  by auto

definition "\<nu>_improving v d \<longleftrightarrow> (\<forall>s. is_arg_max (\<lambda>d. (L d v) s) (\<lambda>d. d \<in> D\<^sub>R) d)"

lemma \<nu>_improving_iff: "\<nu>_improving v d \<longleftrightarrow> d \<in> D\<^sub>R \<and> (\<forall>d' \<in> D\<^sub>R. \<forall>s. L d' v s \<le> L d v s)"
  unfolding \<nu>_improving_def is_arg_max_def
  by (metis leD le_cases less_eq_real_def)

lemma \<nu>_improving_ge: "\<nu>_improving v d \<Longrightarrow> d' \<in> D\<^sub>R \<Longrightarrow> L d' v s \<le> L d v s"
  unfolding \<nu>_improving_iff by auto

lemma \<nu>_improving_imp_\<L>\<^sub>b: "\<nu>_improving v d \<Longrightarrow> \<L>\<^sub>b v = L d v"
  unfolding \<nu>_improving_iff
  by (auto intro!: bfun_eqI cSup_eq_maximum simp: \<L>\<^sub>b.rep_eq \<L>_def)

lemma \<L>\<^sub>b_imp_\<nu>_improving: 
  assumes "d \<in> D\<^sub>R" "\<L>\<^sub>b v = L d v"
  shows "\<nu>_improving v d"
  by (metis (mono_tags, lifting) L_bdd_above \<L>\<^sub>b.rep_eq \<nu>_improving_iff \<L>_def assms cSUP_upper)

lemma \<nu>_improving_alt: 
  assumes "d \<in> D\<^sub>R"
  shows "\<nu>_improving v d \<longleftrightarrow> \<L>\<^sub>b v = L d v"
  using \<L>\<^sub>b_imp_\<nu>_improving \<nu>_improving_imp_\<L>\<^sub>b assms by blast

definition "\<nu>_conserving d = \<nu>_improving (\<nu>\<^sub>b_opt) d"

lemma \<nu>_conserving_iff: "\<nu>_conserving d \<longleftrightarrow> d \<in> D\<^sub>R \<and> (\<forall>d' \<in> D\<^sub>R. \<forall>s. L d' \<nu>\<^sub>b_opt s \<le> L d \<nu>\<^sub>b_opt s)"
  unfolding \<nu>_conserving_def \<nu>_improving_def is_arg_max_def
  by (metis leD le_cases less_eq_real_def)

lemma \<nu>_conserving_ge: "\<nu>_conserving d \<Longrightarrow> d' \<in> D\<^sub>R \<Longrightarrow> L d' \<nu>\<^sub>b_opt s \<le> L d \<nu>\<^sub>b_opt s"
  unfolding \<nu>_conserving_def using \<nu>_improving_ge by auto

lemma \<nu>_conserving_imp_\<L>\<^sub>b [simp]: "\<nu>_conserving d \<Longrightarrow> L d \<nu>\<^sub>b_opt = \<nu>\<^sub>b_opt"
  unfolding \<nu>_conserving_def using \<nu>_improving_imp_\<L>\<^sub>b by force

lemma \<L>\<^sub>b_imp_\<nu>_conserving:
  assumes "d \<in> D\<^sub>R" "\<L>\<^sub>b \<nu>\<^sub>b_opt = L d \<nu>\<^sub>b_opt"
  shows "\<nu>_conserving d"
  unfolding \<nu>_conserving_def using \<L>\<^sub>b_imp_\<nu>_improving assms  by auto

lemma \<nu>_conserving_alt: 
  assumes "d \<in> D\<^sub>R"
  shows "\<nu>_conserving d \<longleftrightarrow> \<L>\<^sub>b \<nu>\<^sub>b_opt = L d \<nu>\<^sub>b_opt"
  unfolding \<nu>_conserving_def using \<nu>_improving_alt assms by auto

lemma \<nu>_conserving_alt':
  assumes "d \<in> D\<^sub>R"
  shows "\<nu>_conserving d \<longleftrightarrow> L d \<nu>\<^sub>b_opt = \<nu>\<^sub>b_opt"
  using assms \<nu>_conserving_alt by auto

theorem thm_6_2_7_a:
  assumes "\<forall>v. \<exists>d. \<nu>_improving v (mk_dec_det d)"
  shows "\<exists>d. \<nu>_conserving (mk_dec_det d)"
  using assms unfolding \<nu>_conserving_def
  by simp

lemma \<nu>_improving_D_MR: "\<nu>_improving v d \<Longrightarrow> d \<in> D\<^sub>R"
  unfolding \<nu>_improving_def is_arg_max_def
  by simp

theorem thm_6_2_7_b[simp]:
  assumes "\<nu>_conserving (mk_dec_det d)"
  shows "\<nu>\<^sub>b (mk_stationary_det d) = \<nu>\<^sub>b_opt"
  using lemma_6_2_5_b \<nu>_conserving_imp_\<L>\<^sub>b[OF assms]
  by simp

theorem thm_6_2_7_c:
  assumes "\<forall>v. \<exists>d. \<nu>_improving v (mk_dec_det d)"
  shows "\<nu>_opt s = (\<Squnion>d \<in> D\<^sub>D. \<nu> (mk_stationary (mk_dec_det d)) s)"
proof -
  obtain d where d: "\<nu>_conserving (mk_dec_det d)"
    using assms thm_6_2_7_a by auto
  hence "d \<in> D\<^sub>D" 
    unfolding \<nu>_conserving_def \<nu>_improving_def  mk_dec_det_def is_dec_def is_dec_det_def
    by (auto simp: is_arg_max_def)
  show ?thesis
    apply (subst \<nu>_MR_eq_HR)
    apply (subst eq_commute)
    apply (subst cSup_eq_maximum[where z = "\<nu>\<^sub>b_opt s"])
    apply (metis (no_types, lifting) \<nu>\<^sub>b.rep_eq d \<open>d \<in> D\<^sub>D\<close> image_iff thm_6_2_7_b)
    using \<Pi>\<^sub>M\<^sub>R_imp_policies is_policy_def apply force
    using \<nu>\<^sub>b_opt.rep_eq \<nu>_MR_eq_HR by presburger
qed

lemma thm_6_2_9_a: 
  "\<exists>d. \<nu>_conserving (mk_dec_det d) \<Longrightarrow> \<exists>d \<in> D\<^sub>D. (\<nu> (mk_stationary (mk_dec_det d))) = \<nu>_opt"
  using \<nu>_improving_D_MR thm_6_2_7_b \<nu>_conserving_def
  by (metis \<L>\<^sub>b_opt is_dec_mk_dec_det_iff mem_Collect_eq thm_6_2_6)

lemma L_le_\<L>: "d \<in> D\<^sub>R \<Longrightarrow> L d v \<le> \<L>\<^sub>b v"
  unfolding less_eq_bfun_def \<L>\<^sub>b.rep_eq \<L>_def
  by (auto intro: cSUP_upper)

lemma \<L>\<^sub>b_sup_att_dec:
  assumes "d \<in> D\<^sub>R" "\<L>\<^sub>b v = L d v"
  shows "\<exists>d' \<in> D\<^sub>D. \<L>\<^sub>b v = L (mk_dec_det d') v"
proof -
  note lemma_4_3_1'
  have "\<And>s. L d v s = measure_pmf.expectation (d s) (\<lambda>a. L\<^sub>a a v s)"
    using L_eq_L\<^sub>a assms by auto

  have "\<And>s. \<exists>a\<in> A s. L d v s = L\<^sub>a a v s"
    apply (subst L_eq_L\<^sub>a[OF assms(1)])
    apply (intro lemma_4_3_1')
    apply auto
    using assms(1) is_dec_def apply blast
    using bounded_range_step
    apply (auto simp: bounded_iff)
    apply meson
    using A_ne apply blast
    apply (subst L_eq_L\<^sub>a[OF assms(1), symmetric])
    apply (subst assms(2)[symmetric])
    using SUP_step_MR_eq \<L>\<^sub>b.rep_eq \<L>_def by presburger
  obtain d' where "\<forall>s. d' s \<in> A s \<and> L d v s = L\<^sub>a (d' s) v s"
    by (meson \<open>\<And>s. \<exists>a\<in>A s. apply_bfun (L d v) s = L\<^sub>a a (apply_bfun v) s\<close>)
  hence d'_dec: "d' \<in> D\<^sub>D"
    apply auto
    using is_dec_det_def by blast
  show ?thesis using assms
    apply (intro bexI[OF _ d'_dec])
    apply (auto intro!: bfun_eqI)
    apply (subst L_eq_L\<^sub>a[of "mk_dec_det d'"])
    apply (auto simp: mk_dec_det_def)
    using d'_dec apply blast
    using \<open>\<forall>s. d' s \<in> A s \<and> apply_bfun (L d v) s = L\<^sub>a (d' s) (apply_bfun v) s\<close> by presburger
qed

lemma thm_6_2_9_b:
  assumes "p \<in> \<Pi>\<^sub>H\<^sub>R" "\<nu> p = \<nu>_opt" 
  shows "\<exists>d \<in> D\<^sub>D. \<nu> (mk_stationary (mk_dec_det d)) = \<nu>_opt"
proof -
  have "\<nu>\<^sub>b p = \<nu>\<^sub>b_opt"
    using assms
    using \<nu>\<^sub>b.abs_eq \<nu>\<^sub>b_opt_def by presburger
  have opt_markovian: "\<forall>s. \<nu>\<^sub>b (mk_markovian (as_markovian p (return_pmf s))) s = \<nu>\<^sub>b_opt s"
    using \<nu>\<^sub>b.rep_eq \<nu>\<^sub>b_opt.rep_eq \<nu>_as_markovian assms(2) by presburger
  have "\<And>s. L (as_markovian p (return_pmf s) 0) \<nu>\<^sub>b_opt s = \<nu>\<^sub>b_opt s"
  proof -
    fix s
    let ?ps = "(as_markovian p (return_pmf s))"
    have markovian_suc_le: "\<nu>\<^sub>b (mk_markovian (\<lambda>n. as_markovian p (return_pmf s) (Suc n))) \<le> \<nu>\<^sub>b_opt"
      apply (intro \<nu>\<^sub>b_le_opt)
      using is_\<Pi>\<^sub>M\<^sub>R_as_markovian assms
      by (auto simp: is_policy_def mk_markovian_def)
    have aux_le: "\<And>x f g. f \<le> g \<Longrightarrow> apply_bfun f x \<le> apply_bfun g x"
      unfolding less_eq_bfun_def by auto
    have "\<nu>\<^sub>b_opt s = \<nu>\<^sub>b (mk_markovian ?ps) s"
      using assms \<nu>\<^sub>b.rep_eq \<nu>_as_markovian by auto
    also have "\<dots> = L (?ps 0) (\<nu>\<^sub>b (mk_markovian (\<lambda>n. ?ps (Suc n)))) s"
      apply (subst \<nu>_step)..
    also have "\<dots> \<le> L (?ps 0) (\<nu>\<^sub>b_opt) s"
      unfolding L_def
      using markovian_suc_le
      apply (auto intro!: ordered_semiring_class.mult_left_mono)
      by (meson \<K>_st_mono less_eq_bfun_def)
    finally have "\<nu>\<^sub>b_opt s \<le> L (?ps 0) (\<nu>\<^sub>b_opt) s" .
    have "as_markovian p (return_pmf s) 0 \<in> D\<^sub>R"
      using is_\<Pi>\<^sub>M\<^sub>R_as_markovian using assms
      by fast
    note  L_le_\<L>[of "?ps 0" "\<nu>\<^sub>b_opt"]
    hence "L (as_markovian p (return_pmf s) 0) \<nu>\<^sub>b_opt \<le> \<nu>\<^sub>b_opt"
      using \<L>\<^sub>b_opt \<open>as_markovian p (return_pmf s) 0 \<in> D\<^sub>R\<close> 
      by simp
    hence "L (?ps 0) (\<nu>\<^sub>b_opt) s \<le> \<nu>\<^sub>b_opt s"
      by (simp add: less_eq_bfun_def)
    thus "L (as_markovian p (return_pmf s) 0) \<nu>\<^sub>b_opt s = \<nu>\<^sub>b_opt s"
      using \<open>\<nu>\<^sub>b_opt s \<le> (L (as_markovian p (return_pmf s) 0) \<nu>\<^sub>b_opt) s\<close> 
      by linarith
  qed
  have "\<And>s v. L (p []) v s = L (as_markovian p (return_pmf s) 0) v s"
    by (auto simp: L_def r_dec\<^sub>b.rep_eq \<K>_st.rep_eq push_exp.rep_eq K_st_def)
  hence "(L (p []) \<nu>\<^sub>b_opt) = \<nu>\<^sub>b_opt"
    apply (intro bfun_eqI)
    using \<open>\<And>s. apply_bfun (L (as_markovian p (return_pmf s) 0) \<nu>\<^sub>b_opt) s = apply_bfun \<nu>\<^sub>b_opt s\<close> 
    by presburger
  hence "L (p []) \<nu>\<^sub>b_opt = \<L>\<^sub>b \<nu>\<^sub>b_opt"
    by auto
  then obtain d where "d \<in> D\<^sub>D" "L (mk_dec_det d) \<nu>\<^sub>b_opt = \<L>\<^sub>b \<nu>\<^sub>b_opt"
    using \<L>\<^sub>b_sup_att_dec
    by (metis assms(1) is_policy_def mem_Collect_eq)
  hence "\<nu>_conserving (mk_dec_det d)"
    apply (subst \<nu>_conserving_alt')
    by auto
  thus ?thesis
    using thm_6_2_9_a
    by auto
qed

lemma finite_is_arg_max: "finite X \<Longrightarrow> X \<noteq> {} \<Longrightarrow> \<exists>x. is_arg_max (f :: 'c \<Rightarrow> real) (\<lambda>x. x \<in> X) x"
  unfolding is_arg_max_def
proof (induction rule: finite_induct)
  case (insert x F)
  then show ?case
  proof (cases "\<forall>y \<in> F. f y \<le> f x")
    case True
    then show ?thesis
      by (auto intro!: exI[of _ x])
  next
    case False
    then show ?thesis
      using insert by force
  qed
qed simp

lemma finite_arg_max_le:
  assumes "finite (X :: 'c set)" "X \<noteq> {}"
  shows "s \<in> X \<Longrightarrow> (f :: 'c \<Rightarrow> real) s \<le> f (arg_max_on (f :: 'c \<Rightarrow> real) X)"
  unfolding arg_max_def arg_max_on_def
  by (metis assms(1) assms(2) finite_is_arg_max is_arg_max_linorder someI_ex)

lemma arg_max_on_in:
  assumes "finite (X :: 'c set)" "X \<noteq> {}"
  shows "(arg_max_on (f :: 'c \<Rightarrow> real)  X) \<in> X"
  unfolding arg_max_on_def arg_max_def
  by (metis assms(1) assms(2) finite_is_arg_max is_arg_max_def someI)

lemma finite_arg_max_eq_Max:
  assumes "finite (X :: 'c set)" "X \<noteq> {}"
  shows "(f :: 'c \<Rightarrow> real) (arg_max_on f X) = Max (f ` X)"
  using assms
  by (auto intro!: Max_eqI[symmetric] finite_arg_max_le arg_max_on_in)

definition "\<L>_sup_att = (\<forall>v. \<exists>d \<in> D\<^sub>R. L d v = \<L>\<^sub>b v)"

theorem thm_6_2_10_a_aux': 
  assumes "\<And>s. finite (A s)"
  assumes "is_arg_max (\<lambda>a. L\<^sub>a a (v :: 's \<Rightarrow>\<^sub>b real) s) (\<lambda>a. a \<in> A s) a"
  shows "r (s, a) + l * measure_pmf.expectation (K (s,a)) v = \<L>\<^sub>b v s"
  apply (intro antisym)
  unfolding \<L>\<^sub>b.rep_eq \<L>_eq_SUP_det SUP_step_det_eq
  apply (auto intro!: cSUP_upper2)
  subgoal
    using step_v_le by (auto intro!: boundedI[of _ "r\<^sub>M + l * norm v"] bounded_imp_bdd_above)
  using assms A_ne unfolding is_arg_max_def
  by (auto intro!: cSUP_least)


theorem thm_6_2_10_a_aux: 
  assumes "\<And>s. finite (A s)"
  shows "\<exists>d \<in> D\<^sub>D. L (mk_dec_det d) v = \<L>\<^sub>b v"
proof -
  have aux: "\<And>P. \<forall>x. \<exists>d. P d x \<Longrightarrow> \<exists>f. \<forall>x. P (f x) x"
    by metis
  have "\<And>s. \<exists>a. a \<in> A s \<and> L\<^sub>a a v s = \<L>\<^sub>b v s"
  proof -
    fix s
    show "\<exists>a. a \<in> A s \<and> L\<^sub>a a v s = \<L>\<^sub>b v s"
      apply (intro exI[of _ "arg_max_on (\<lambda>a. L\<^sub>a a v s) (A s)"])
      unfolding \<L>\<^sub>b.rep_eq \<L>_eq_SUP_det SUP_step_det_eq
      using A_ne arg_max_on_in[OF assms A_ne]
      by(auto simp: cSup_eq_Sup_fin Sup_fin_Max assms A_ne finite_arg_max_eq_Max[symmetric])
  qed
  hence "\<exists>d.
       \<forall>s. d s \<in> A s \<and> L\<^sub>a (d s) v s = (\<L>\<^sub>b v) s"
    by metis
  hence "\<exists>d \<in> D\<^sub>D. \<forall>s. L (mk_dec_det d) v s = \<L>\<^sub>b v s"
    unfolding  L_def is_dec_det_def mk_dec_det_def
    by (auto simp: r_dec\<^sub>b.rep_eq K_st_def \<K>_st.rep_eq push_exp.rep_eq  bind_return_pmf)
  thus ?thesis
    using bfun_eqI by blast
qed

lemma thm_6_2_10:
  assumes "\<forall>s. finite (A s)"
  shows "\<exists>d \<in> D\<^sub>D. \<nu>_opt = \<nu> (mk_stationary (mk_dec_det d))"
  using assms thm_6_2_10_a_aux thm_6_2_9_a
  by (metis D_det_to_MR \<nu>_conserving_def \<nu>_improving_alt mem_Collect_eq)

lemma ex_det_eps:
  assumes "0 < (e :: real)"
  shows "\<exists>d \<in> D\<^sub>D. \<L>\<^sub>b v \<le> L (mk_dec_det d) v + e *\<^sub>R 1"
proof -
  have "\<And>s. \<exists>a \<in> A s. \<L>\<^sub>b v s \<le> r (s, a) + l * measure_pmf.expectation (K (s, a)) v + e"
  proof -
    fix s 
    have aux: "\<L>\<^sub>b v s - e < \<L>\<^sub>b v s" using \<open>0 < e\<close> by auto
    have bdd: "bdd_above ((\<lambda>a. r (s, a) + l * measure_pmf.expectation (K (s, a)) v) ` A s)"
      using step_v_le by (auto intro!: boundedI[of _ "r\<^sub>M + l * norm v"] bounded_imp_bdd_above)
    have "\<exists>a_e \<in> A s. \<L>\<^sub>b v s - e < r (s, a_e) + l * measure_pmf.expectation (K (s, a_e)) v"
      unfolding \<L>\<^sub>b.rep_eq \<L>_eq_SUP_det SUP_step_det_eq
      apply (auto simp: less_cSUP_iff[OF A_ne bdd, symmetric])
      by (simp add: \<open>0 < e\<close>)
    then obtain a where "a \<in> A s" "\<L>\<^sub>b v s - e < r (s, a) + l * measure_pmf.expectation (K (s, a)) v"
      by blast
    thus "\<exists>a\<in>A s. (\<L>\<^sub>b v) s \<le> r (s, a) + l * measure_pmf.expectation (K (s, a)) v + e"
      unfolding \<L>\<^sub>b.rep_eq \<L>_eq_SUP_det SUP_step_det_eq
      by force
  qed
  hence "\<exists>d\<in>D\<^sub>D. \<forall>s. \<L>\<^sub>b v s \<le> L (mk_dec_det d) v s + e"
    apply (intro bexI[of _ "\<lambda>s. SOME a. a \<in> A s \<and> \<L>\<^sub>b v s \<le> r (s, a) 
      + l * measure_pmf.expectation (K (s, a)) v + e"])
    unfolding mk_dec_det_def
    apply (auto simp: L_def \<K>_st.rep_eq push_exp.rep_eq bind_return_pmf r_dec\<^sub>b.rep_eq K_st_def)
    apply (metis (lifting) someI_ex)
    unfolding is_dec_det_def
    by (metis (mono_tags, lifting) verit_sko_ex')
  thus ?thesis
    by (auto simp: less_eq_bfun_def)
qed

lemma ex_det_dist_eps:
  assumes "0 < (e :: real)"
  shows "\<exists>d \<in> D\<^sub>D. dist (\<L>\<^sub>b v) (L (mk_dec_det d) v) \<le> e"
proof -
  have "\<forall>d\<in>D\<^sub>D. L (mk_dec_det d) v \<le> \<L>\<^sub>b v"
    unfolding \<L>\<^sub>b.rep_eq \<L>_eq_SUP_det less_eq_bfun_def
    by (auto intro!: cSUP_upper2)
  then obtain d where "d \<in> D\<^sub>D" "L (mk_dec_det d) v \<le> (\<L>\<^sub>b v)" 
    and h2: "\<L>\<^sub>b v \<le> L (mk_dec_det d) v + e *\<^sub>R 1"
    using assms ex_det_eps by blast
  hence "0 \<le> \<L>\<^sub>b v -  L (mk_dec_det d) v"
    by simp
  moreover have "\<L>\<^sub>b v - L (mk_dec_det d) v \<le> e *\<^sub>R 1"
    using h2 by (meson diff_diff_add diff_eq_diff_less_eq)
  ultimately have "\<forall>s. \<bar>(\<L>\<^sub>b v) s -  L (mk_dec_det d) v s\<bar> \<le> e"
    unfolding less_eq_bfun_def by auto
  hence "dist (\<L>\<^sub>b v) (L (mk_dec_det d) v) \<le> e"
    unfolding dist_bfun.rep_eq
    by (auto intro!: cSUP_least simp: dist_real_def)
  thus ?thesis
    using \<open>d \<in> D\<^sub>D\<close> by auto
qed

lemma thm_6_2_11:
  assumes "eps > 0"
  shows "\<exists>d\<in>D\<^sub>D. \<nu>\<^sub>b_opt \<le> \<nu>\<^sub>b (mk_stationary (mk_dec_det d)) + eps *\<^sub>R 1"
proof -
  have "(1-l)*eps > 0"
    by (simp add: assms)
  then obtain d where "d\<in>D\<^sub>D" and d: "\<L>\<^sub>b \<nu>\<^sub>b_opt \<le> L (mk_dec_det d) \<nu>\<^sub>b_opt + ((1-l)*eps) *\<^sub>R 1"
    using ex_det_eps[of _ \<nu>\<^sub>b_opt] by auto
  let ?d = "mk_dec_det d"
  let ?lK = "l *\<^sub>R \<K>_st ?d"
  let ?lK_opt = "l *\<^sub>R \<K>_st ?d \<nu>\<^sub>b_opt"
  have "\<nu>\<^sub>b_opt \<le> L ?d \<nu>\<^sub>b_opt + ((1-l)*eps) *\<^sub>R 1"
    by (metis d \<L>\<^sub>b_conv(1) lemma_6_2_2_c)
  hence "(\<nu>\<^sub>b_opt - ?lK_opt - ((1-l)*eps) *\<^sub>R 1) \<le> r_dec\<^sub>b ?d"
    by (simp add: L_def cancel_ab_semigroup_add_class.diff_right_commute diff_le_eq)
  hence "\<forall>s. (\<Sum>i. ?lK ^^ i) (\<nu>\<^sub>b_opt - ?lK_opt - ((1-l)*eps) *\<^sub>R 1) \<le> (\<Sum>i. ?lK ^^ i) (r_dec\<^sub>b ?d)"
    by (metis (no_types, lifting) blincomp_scaleR_right lemma_6_1_2_b suminf_cong)
  hence "(\<Sum>i. ?lK ^^ i) (\<nu>\<^sub>b_opt - ?lK_opt - ((1-l)*eps) *\<^sub>R 1) \<le> (\<nu>\<^sub>b (mk_stationary ?d))"
    unfolding \<nu>_stationary by (simp add: blincomp_scaleR_right)
  hence le1: "(\<Sum>i. ?lK ^^ i) (\<nu>\<^sub>b_opt - ?lK_opt) - (\<Sum>i. ?lK ^^ i) (((1-l)*eps) *\<^sub>R 1)
    \<le> (\<nu>\<^sub>b (mk_stationary ?d))"
    by (simp add: blinfun.diff_right)
  hence le2: "((\<Sum>i. ?lK ^^ i) o\<^sub>L (id_blinfun - ?lK)) \<nu>\<^sub>b_opt - (\<Sum>i. ?lK ^^ i) (((1-l)*eps) *\<^sub>R 1) 
    \<le> (\<nu>\<^sub>b (mk_stationary ?d))"
    by (simp add: blinfun.diff_left blinfun.scaleR_left)
  hence le3: "id_blinfun \<nu>\<^sub>b_opt - (\<Sum>i. ?lK ^^ i) (((1-l)*eps) *\<^sub>R 1) \<le> \<nu>\<^sub>b (mk_stationary ?d)"
    by (subst inv_norm_le(2)[symmetric], auto)
  have s: "summable (\<lambda>i. (l *\<^sub>R \<K>_st ?d)^^i)"
    using convergent_disc_\<K>_st summable_iff_convergent'
    by (simp add: blincomp_scaleR_right summable_iff_convergent')
  have "(\<Sum>i. ?lK ^^ i) (((1-l)*eps) *\<^sub>R 1) = ((1-l)*eps) *\<^sub>R (\<Sum>i. ?lK^^i) 1"
    using blinfun.scaleR_right by blast
  also have "\<dots> = ((1-l)*eps) *\<^sub>R (\<Sum>i. (?lK^^i) 1) "
    apply (subst bounded_linear.suminf[OF _, symmetric, where f = "\<lambda>x. blinfun_apply x 1"])
    using s by auto
  also have "\<dots> = ((1-l)*eps) *\<^sub>R (\<Sum>i. (l ^ i *\<^sub>R \<K>_st ?d ^^i) 1) "
    by (simp add: blincomp_scaleR_right)
  also have "\<dots> = ((1-l)*eps) *\<^sub>R (\<Sum>i. ((l ^ i *\<^sub>R ((\<K>_st ?d ^^ i) 1))))"
    by (meson scaleR_blinfun.rep_eq)
  also have "\<dots> = ((1-l)*eps) *\<^sub>R (\<Sum>i. ((l ^ i *\<^sub>R 1)))"
    by simp
  also have "\<dots> = ((1-l)*eps) *\<^sub>R (\<Sum>i. (l ^ i)) *\<^sub>R 1"
    apply (subst bounded_linear.suminf[where f = "\<lambda>x. x *\<^sub>R 1"])
    by (auto simp add: bounded_linear_scaleR_left summable_geometric)
  also have "\<dots> = ((1-l)*eps) *\<^sub>R (1 / (1-l)) *\<^sub>R 1"
    by (simp add: suminf_geometric)
  also have "\<dots> = eps *\<^sub>R 1"
    using disc_lt_one apply auto
    using disc_lt_one by fastforce
  finally have "(\<Sum>i. ?lK ^^ i) (((1-l)*eps) *\<^sub>R 1) = eps *\<^sub>R 1" .
  hence "\<nu>\<^sub>b_opt - eps *\<^sub>R 1 \<le> (\<nu>\<^sub>b (mk_stationary ?d))"
    using le3 by auto
  thus "\<exists>d\<in>D\<^sub>D. \<nu>\<^sub>b_opt \<le> \<nu>\<^sub>b (mk_stationary (mk_dec_det d)) + eps *\<^sub>R 1"
    using \<open>d \<in> D\<^sub>D\<close> diff_le_eq by blast
qed

lemma Bfun_\<nu>_opt_eq_the: 
  assumes "\<exists>!v. f v = v"
  shows "(THE v. v \<in> bfun \<and> v = apply_bfun (f (Bfun v))) = apply_bfun (THE v. (f v) = v)"
  apply (intro the_equality)
  apply simp
  apply (metis (mono_tags, lifting) assms apply_bfun_inverse theI')
  by (metis (mono_tags, lifting) assms apply_bfun_inverse the_equality)

lemma THE_bfun1: 
  assumes "\<exists>!v. f v = v"
  shows "(THE v. v \<in> bfun \<and> v = (f (Bfun v))) = (THE v. apply_bfun (f v) = v)"
  apply (intro the_equality)
  apply simp
  apply (metis (mono_tags, lifting) assms apply_bfun_inverse theI')
  by (metis (mono_tags, lifting) assms apply_bfun_inverse the_equality)

lemma aux_conv: "(\<lambda>n. (\<L>\<^sub>b ^^ n) v) \<longlonglongrightarrow> \<nu>\<^sub>b_opt"
  using \<L>\<^sub>b_conv(2) \<nu>\<^sub>b_opt_fix by presburger

lemma lemma_6_3_1_a: "uniform_limit UNIV (\<lambda>n. (\<L>\<^sub>b ^^ n) v0) \<nu>\<^sub>b_opt sequentially"
  by (intro tendsto_bfun_uniform_limit[OF aux_conv])

lemma lemma_6_3_1_a': "uniform_limit UNIV (\<lambda>n. (\<L>\<^sub>b ^^ n) v0) \<nu>_opt sequentially"
proof -
  have "uniform_limit UNIV (\<lambda>n. (\<L>\<^sub>b ^^ n) v0) \<nu>\<^sub>b_opt sequentially"
    by (intro tendsto_bfun_uniform_limit[OF aux_conv])
  thus "uniform_limit UNIV (\<lambda>n. (\<L>\<^sub>b ^^ n) v0) \<nu>_opt sequentially"
    by (simp add: \<nu>_opt_bfun bfun.Bfun_inverse)
qed

lemma \<L>_Bfun_eq: "v0 \<in> bfun \<Longrightarrow> ((\<lambda>v. \<L> (Bfun v))^^n) v0 = (\<L>\<^sub>b ^^n) (Bfun v0)"
  apply (induction n)
  by (auto simp add: bfun.Bfun_inverse \<L>\<^sub>b.rep_eq apply_bfun_inverse)

lemma lemma_6_3_1_a'':
  assumes "v0 \<in> bfun"
  shows "uniform_limit UNIV (\<lambda>n. ((\<lambda>v. \<L> (Bfun v)) ^^ n) v0) \<nu>_opt sequentially"
  by (auto simp: assms \<L>_Bfun_eq lemma_6_3_1_a')

lemma thm_6_3_1_b_aux: "\<forall>e > 0. \<exists>N. \<forall>n \<ge> N. dist ((\<L>\<^sub>b^^n) v) ((\<L>\<^sub>b^^(Suc n)) v) < e"
proof safe
  fix e :: real
  assume "e > 0"
  hence "e/2 > 0" by auto
  have "(\<lambda>n. (\<L>\<^sub>b^^n) v) \<longlonglongrightarrow> \<nu>\<^sub>b_opt"
    using aux_conv .
  hence "(\<forall>\<^sub>F n in sequentially. (dist ((\<L>\<^sub>b^^n) v) \<nu>\<^sub>b_opt < e/2))"
    using tendsto_iff \<open>0 < e/2\<close> by fast
  then obtain N where "\<forall>n\<ge>N. dist ((\<L>\<^sub>b^^n) v) \<nu>\<^sub>b_opt < e/2"
    using eventually_sequentially by auto
  hence "\<forall>n \<ge> N. dist ((\<L>\<^sub>b^^(Suc n)) v) \<nu>\<^sub>b_opt < e/2"
    using le_SucI by blast
  hence "\<forall>n \<ge> N. dist ((\<L>\<^sub>b^^n) v) ((\<L>\<^sub>b^^(Suc n)) v) < e"
    by (metis \<open>\<forall>n\<ge>N. dist ((\<L>\<^sub>b ^^ n) v) \<nu>\<^sub>b_opt < e / 2\<close> dist_commute dist_triangle_half_r)
  thus "\<exists>N. \<forall>n\<ge>N. dist ((\<L>\<^sub>b ^^ n) v) ((\<L>\<^sub>b ^^ Suc n) v) < e"
    by blast
qed

definition "arg_max_eps f X e \<equiv> SOME x. x \<in> X \<and> (\<forall>x' \<in> X. f x' \<le> f x + e)"

lemma term_aux': "dist v (\<L>\<^sub>b v) \<le> 2 * dist v \<nu>\<^sub>b_opt"
proof -
  have le1: "dist v (\<L>\<^sub>b v) \<le> dist v \<nu>\<^sub>b_opt + dist (\<L>\<^sub>b v) \<nu>\<^sub>b_opt"
    by (simp add: dist_triangle dist_commute)
  have le2: "dist (\<L>\<^sub>b v) \<nu>\<^sub>b_opt \<le> l * dist v \<nu>\<^sub>b_opt"
    by (metis \<L>\<^sub>b_conv(1) contraction_\<L> lemma_6_2_2_c)
  show ?thesis
    apply (intro order.trans[OF le1])
    apply (auto intro!: order.trans[OF le2])
    using disc_lt_one
    by (metis mult.commute mult_cancel_right1 mult_left_mono not_le order.asym zero_le_dist)
qed

lemma L_det: "L (mk_dec_det d) v s = L\<^sub>a (d s) v s"
  unfolding L_def  plus_bfun.rep_eq mk_dec_det_def \<K>_st.rep_eq push_exp.rep_eq K_st_def 
  by (auto simp: push_exp.rep_eq r_dec\<^sub>b.rep_eq bind_return_pmf)

section \<open>Value Iteration\<close>
text \<open>
In the previous sections we derived that repeated application of @{const "\<L>\<^sub>b"} to any bounded 
function from states to the reals converges to the optimal value of the MDP @{const "\<nu>\<^sub>b_opt"}.

We can turn this procedure into an algorithm that computes not only an approximation of 
@{const "\<nu>\<^sub>b_opt"} but also a policy that is arbitrarily close to optimal.

Most of the proofs rely on the assumption that the supremum in @{const "\<L>\<^sub>b"} can always be attained.
\<close>

text \<open>
The following lemma shows that the relation we use to prove termination of the value iteration 
algorithm decreases in each step.
In essence, the distance of the estimate to the optimal value decreases by a factor of at 
least @{term l} per iteration.
\<close>

lemma vi_rel_dec: 
  assumes "l \<noteq> 0" "\<L>\<^sub>b v \<noteq> \<nu>\<^sub>b_opt"
  shows "\<lceil>log (1 / l) (dist (\<L>\<^sub>b v) \<nu>\<^sub>b_opt) + c\<rceil> < \<lceil>log (1 / l) (dist v \<nu>\<^sub>b_opt) + c\<rceil>"
proof -
  have "log (1 / l) (dist (\<L>\<^sub>b v) \<nu>\<^sub>b_opt) + c \<le> log (1 / l) (l * dist v \<nu>\<^sub>b_opt) + c"
    using contraction_\<L>[of _ "\<nu>\<^sub>b_opt"] disc_lt_one
    by (auto simp: assms less_divide_eq_1 less_le intro: log_le)
  also have "\<dots> = log (1 / l) l + log (1/l) (dist v \<nu>\<^sub>b_opt) + c"
    using assms disc_lt_one by (auto simp: less_le intro!: log_mult)
  also have "\<dots> = -(log (1 / l) (1/l)) + (log (1/l) (dist v \<nu>\<^sub>b_opt)) + c"
    apply (subst log_inverse[symmetric])
    using assms disc_lt_one
    by (auto simp: less_le right_inverse_eq)+
  also have "\<dots> = -1 + (log (1/l) (dist v \<nu>\<^sub>b_opt)) + c"
    using assms(1) disc_lt_one
    by (metis divide_pos_pos less_divide_eq_1 less_le log_eq_one zero_le_disc zero_less_one)
  also have "\<dots> = (log (1 / l) (dist v \<nu>\<^sub>b_opt)) - 1 + c"
    using assms disc_lt_one 
    by (auto simp del: times_divide_eq_right simp: less_le times_divide_eq_right[symmetric] 
        intro!: log_mult[symmetric])
  finally have "log (1 / l) (dist (\<L>\<^sub>b v) \<nu>\<^sub>b_opt) + c \<le> log (1 / l) (dist v \<nu>\<^sub>b_opt) - 1 + c" .
  thus ?thesis
    by linarith
qed

function value_iteration :: "real \<Rightarrow> ('s \<Rightarrow>\<^sub>b real) \<Rightarrow> ('s \<Rightarrow>\<^sub>b real)" where
  "value_iteration eps v =
  (if 2 * l * dist v (\<L>\<^sub>b v) < eps * (1-l) \<or> eps \<le> 0 then \<L>\<^sub>b v else value_iteration eps (\<L>\<^sub>b v))"
  by auto

termination
  apply (relation "Wellfounded.measure (\<lambda>(eps,v). 
    if v = \<nu>\<^sub>b_opt \<or> l = 0 
    then 0 
    else nat (ceiling (log (1/l) (dist v \<nu>\<^sub>b_opt) - log (1/l) ((eps * (1-l) / (2 * l)) / 4))))")
  subgoal by auto
proof -
  fix eps v
  assume h: "\<not> (2 * l * dist v (\<L>\<^sub>b v) < eps * (1 - l) \<or> eps \<le> 0)"
  show "((eps, \<L>\<^sub>b v), eps, v) \<in> Wellfounded.measure (\<lambda>(eps, v). 
    if v = \<nu>\<^sub>b_opt \<or> l = 0 
    then 0 
    else nat \<lceil>log (1 / l) (dist v \<nu>\<^sub>b_opt) - log (1 / l) (eps * (1 - l) / (2 * l) / 4)\<rceil>)"
  proof (cases "l = 0")
    case True
    then show ?thesis
      using h
      by auto
  next
    case False
    hence l_ne_zero[simp]: "l \<noteq> 0" and "eps > 0" and dist_ge: "eps * (1 - l)  \<le> dist v (\<L>\<^sub>b v) * (2 * l)"
      apply simp
      using h apply linarith
      by (metis h mult.commute not_le)
    have "\<not>  ((2 * l) * dist v (\<L>\<^sub>b v) < eps * (1 - l) \<or> eps \<le> 0 \<or> l = 0)"
      using dist_ge h l_ne_zero  zero_le_disc l_ne_zero pos_less_divide_eq zero_le_disc
      by auto
    have v_not_opt: "v \<noteq> \<nu>\<^sub>b_opt"
      using h by force
    hence aux: "eps * (1 - l)  \<le> dist v \<nu>\<^sub>b_opt * (4 * l)"
      apply (intro order.trans[OF dist_ge])
      using term_aux'  
      by (simp add: mult_left_mono vector_space_over_itself.scale_left_commute)

    hence "0 < log (1 / l) (dist v \<nu>\<^sub>b_opt * (8 * l) / (eps * (1 - l)))"
      apply (subst zero_less_log_cancel_iff)
      using disc_lt_one real_inverse_le_1_iff zero_le_disc apply fastforce
      apply (subst pos_less_divide_eq)
      apply auto
      apply (meson \<open>0 < eps\<close> diff_gt_0_iff_gt disc_lt_one mult_pos_pos)
      apply (simp add: less_le v_not_opt)
      apply (subst pos_less_divide_eq)
      apply (auto simp add: \<open>0 < eps\<close>)
      apply (rule order_class.order.strict_trans1)
      apply auto
      using l_ne_zero zero_le_disc v_not_opt
      by (meson linorder_neqE_linordered_idom mult_pos_pos not_less zero_less_dist_iff)
    thus "((eps, \<L>\<^sub>b v), eps, v) \<in> Wellfounded.measure (\<lambda>(eps, v). 
      if v = \<nu>\<^sub>b_opt \<or> l = 0 
      then 0 
      else nat \<lceil>log (1 / l) (dist v \<nu>\<^sub>b_opt) - log (1/l) (eps * (1 - l) / (2 * l) / 4)\<rceil>)"
      apply (auto simp add: v_not_opt)
      subgoal
        apply (subst log_less)
        apply auto
        using disc_lt_one
        apply (metis  divide_less_cancel divide_self_if l_ne_zero not_less zero_le_disc)
        using h less_eq_real_def zero_le_disc apply force
        apply (subst (asm) zero_less_log_cancel_iff)
        using disc_lt_one
        apply (metis  divide_less_cancel divide_self_if l_ne_zero not_less zero_le_disc)
        using \<open>0 < eps\<close> less_eq_real_def v_not_opt zero_le_disc apply auto[1]
        apply (subst pos_divide_less_eq)
        using zero_le_disc l_ne_zero
        apply linarith
        using h by force
      subgoal
        apply (subst log_less)
        apply auto
        using disc_lt_one
        apply (metis  divide_less_cancel divide_self_if l_ne_zero not_less zero_le_disc)
        using h less_eq_real_def zero_le_disc apply force
        apply (subst (asm) zero_less_log_cancel_iff)
        using disc_lt_one
        apply (metis  divide_less_cancel divide_self_if l_ne_zero not_less zero_le_disc)
        using \<open>0 < eps\<close> less_eq_real_def v_not_opt zero_le_disc apply auto[1]
        apply (subst pos_divide_less_eq)
        using zero_le_disc l_ne_zero
        apply linarith
        using h by force
      by (auto simp del: add_uminus_conv_diff simp add: vi_rel_dec diff_conv_add_uminus)
  qed
qed

lemma contraction_dist:
  fixes C :: "'b :: complete_space \<Rightarrow> 'b"
  assumes "\<And>v u. dist (C v) (C u) \<le> c  * dist v u"
  assumes "0 \<le> c" "c < 1"
  shows "(1 - c) * dist v (THE v. C v = v) \<le> dist v (C v)"
proof -
  have "is_contraction C"
    unfolding is_contraction_def using assms by auto
  then obtain v_fix where v_fix: "v_fix = (THE v. C v = v)"
    using the1_equality
    by blast
  hence "C v_fix = v_fix"
    using theI'[OF banach'(1)[OF \<open>is_contraction C\<close>]]
    apply (subst v_fix)
    by simp
  hence "(\<lambda>n. (C ^^ n) v) \<longlonglongrightarrow> v_fix"
    using banach'[OF \<open>is_contraction C\<close>]
    apply (subst (asm) the1_equality[of _ v_fix])
    by auto
  have dist_contr_le_pow: "\<And>n. dist ((C ^^ n) v) ((C ^^ Suc n) v) \<le> c ^ n * dist v (C v)"
  proof -
    fix n 
    show "dist ((C ^^ n) v) ((C ^^ Suc n) v) \<le> c ^ n * dist v (C v)"
      apply (induction n arbitrary: v)
      apply simp
      apply (simp only: funpow_simps_right(2) o_def)
      using assms apply (auto simp add: mult.assoc)
      using assms(2)
      by (metis (no_types, hide_lams) funpow_swap1 mult_left_mono order_subst1)
  qed
  have "\<forall>e > 0. dist v v_fix \<le> (\<Sum>i. dist ((C ^^ i) v) ((C ^^ (Suc i)) v)) + e"
  proof safe
    fix e ::real assume "0 < e"
    have "\<forall>\<^sub>F n in sequentially. dist ((C^^n) v) v_fix < e"
      using \<open>(\<lambda>n. (C ^^ n) v) \<longlonglongrightarrow> v_fix\<close> \<open>0 < e\<close> tendsto_iff by force
    then obtain N where "dist ((C^^N) v) v_fix < e"
      by fastforce
    have "dist v v_fix \<le> dist v ((C^^N) v) + e"
      by (metis \<open>dist ((C ^^ N) v) v_fix < e\<close> add_le_cancel_left dist_commute dist_triangle_le 
          less_eq_real_def)
    have "dist v ((C^^N) v) \<le> (\<Sum>i\<le>N. dist ((C ^^ i) v) ((C ^^ (Suc i)) v))"
    proof (induction N arbitrary: v)
      case 0
      then show ?case by simp
    next
      case (Suc N)      
      have "dist v ((C ^^ Suc N) v) \<le> dist v (C v) + dist (C v) ((C^^(Suc N)) v)"
        by metric
      also have "\<dots> =  dist v (C v) + dist (C v) ((C^^N) (C v))"
        by (metis funpow_simps_right(2) o_def)
      also have "\<dots> \<le> dist v (C v) + (\<Sum>i\<le>N. dist ((C ^^ i) (C v)) ((C ^^ Suc i) (C v)))"
        using Suc.IH add_le_cancel_left by blast
      also have "\<dots> \<le> dist v (C v) + (\<Sum>i\<le>N. dist ((C ^^Suc i) v) ((C ^^ (Suc (Suc i))) v))"
        by (simp only: funpow_simps_right(2) o_def)
      also have "\<dots> \<le> (\<Sum>i\<le>Suc N. dist ((C ^^ i) v) ((C ^^ (Suc i)) v))"
        apply (subst sum.atMost_Suc_shift)
        by simp
      finally show "dist v ((C ^^ Suc N) v) \<le> (\<Sum>i\<le>Suc N. dist ((C ^^ i) v) ((C ^^ Suc i) v))" .
    qed
    have 
      "(\<Sum>i\<le>N. dist ((C ^^ i) v) ((C ^^ Suc i) v)) \<le> (\<Sum>i. dist ((C ^^ i) v) ((C ^^ (Suc i)) v))"
      apply (intro sum_le_suminf)
      apply (auto simp del: funpow.simps)
      apply (rule summable_comparison_test[where g = "\<lambda>i. c^i * dist v (C v)"])
      apply (intro exI[of _ 0])  
      apply (auto simp del: funpow.simps)
      using dist_contr_le_pow assms by auto
    hence le_suminf: "dist v ((C^^N) v) \<le> (\<Sum>i. dist ((C ^^ i) v) ((C ^^ (Suc i)) v))"
      using \<open>dist v ((C ^^ N) v) \<le> (\<Sum>i\<le>N. dist ((C ^^ i) v) ((C ^^ Suc i) v))\<close> by linarith
    thus " dist v v_fix \<le> (\<Sum>i. dist ((C ^^ i) v) ((C ^^ Suc i) v)) + e"
      using \<open>dist v v_fix \<le> dist v ((C ^^ N) v) + e\<close> by fastforce
  qed
  hence le_suminf: "dist v v_fix \<le> (\<Sum>i. dist ((C ^^ i) v) ((C ^^ Suc i) v))"
    using field_le_epsilon by blast
  have "dist v v_fix \<le> (\<Sum>i. c ^ i * dist v (C v))"
    apply (intro order_trans[OF le_suminf])
    apply (intro suminf_le)
    using dist_contr_le_pow assms 
    apply simp
    apply (rule summable_comparison_test[where g = "\<lambda>i. c^i * dist v (C v)"])
    apply (intro exI[of _ 0])  
    apply (auto simp del: funpow.simps)
    using dist_contr_le_pow assms by auto
  hence "dist v v_fix \<le> dist v (C v) / (1 - c)"
    using sum_disc_lim
    by (metis sum_disc_lim abs_of_nonneg assms(2) assms(3))
  hence "(1 - c) * dist v v_fix \<le> dist v (C v)"
    using assms(3) mult.commute pos_le_divide_eq 
    by (metis diff_gt_0_iff_gt)
  thus ?thesis
    using v_fix by blast
qed

text \<open>
The distance between an estimate for the value and the optimal value can be bounded with respect to 
the distance between the estimate and the result of applying it to @{const \<L>\<^sub>b}
\<close>
lemma contraction_\<L>_dist: "(1 - l) * dist v \<nu>\<^sub>b_opt \<le> dist v (\<L>\<^sub>b v)"
  using contraction_dist contraction_\<L> disc_lt_one zero_le_disc
  by fastforce

lemma dist_\<L>\<^sub>b_opt_eps:
  assumes "eps > 0" "2 * l * dist v (\<L>\<^sub>b v) < eps * (1-l)"
  shows "dist (\<L>\<^sub>b v) \<nu>\<^sub>b_opt < eps / 2"
proof -
  have "dist v \<nu>\<^sub>b_opt \<le> dist v (\<L>\<^sub>b v) / (1 - l)"
    using contraction_\<L>_dist
    by (simp add: mult.commute pos_le_divide_eq)
  hence "2 * l * dist v \<nu>\<^sub>b_opt \<le> 2 * l * (dist v (\<L>\<^sub>b v) / (1 - l))"
    using contraction_\<L>_dist assms
    mult_le_cancel_left_pos[of "2 * l"]
    apply (intro  mult_left_mono[of _ _ "2 * l"])
    by auto
  hence "2 * l * dist v \<nu>\<^sub>b_opt < eps"
    apply (rule order.strict_trans1)
    by (auto simp add: assms(2) pos_divide_less_eq)
  hence "dist v \<nu>\<^sub>b_opt * l < eps / 2"
    by argo
  hence "l * dist v \<nu>\<^sub>b_opt < eps / 2"
    by (auto simp: algebra_simps)
  thus "dist (\<L>\<^sub>b v) \<nu>\<^sub>b_opt < eps / 2"
    using contraction_\<L>[of v \<nu>\<^sub>b_opt] by auto
qed

text \<open>
The estimates above allow to give a bound on the error of @{const value_iteration}.
\<close>

lemma value_iteration_error: 
  assumes "eps > 0"
  shows "dist (value_iteration eps v) \<nu>\<^sub>b_opt < eps / 2"
  using assms proof (induction eps v arbitrary:  rule: value_iteration.induct)
  case (1 eps v)
  then show ?case
    apply (subst value_iteration.simps)
    apply (auto simp del: value_iteration.simps split: if_splits)
    using dist_\<L>\<^sub>b_opt_eps
    by auto
qed

text \<open>
After the value iteration terminates, one can easily obtain a stationary deterministic 
epsilon-optimal policy.

Such a policy does not exist in general, attainment of the supremum in @{const \<L>\<^sub>b} is required.
\<close>
definition "find_policy (v :: 's \<Rightarrow>\<^sub>b real) s = 
  arg_max_on (\<lambda>a. L\<^sub>a a v s) (A s)"

definition "vi_policy eps v = find_policy (value_iteration eps v)"

lemma arg_max_SUP: "is_arg_max (f :: 'b \<Rightarrow> real) (\<lambda>x. x \<in> X) m \<Longrightarrow> f m = (\<Squnion>(f ` X))"
  unfolding is_arg_max_def
  by (auto intro!: antisym cSUP_upper bdd_aboveI[of _ "f m"] cSUP_least)

definition "has_max X \<equiv> \<exists>x \<in> X. \<forall>x' \<in> X. x' \<le> x"
definition "has_arg_max f X \<equiv> \<exists>x. is_arg_max f (\<lambda>x. x \<in> X) x"

lemma "has_max ((f :: 'b \<Rightarrow> real) ` X) \<longleftrightarrow> has_arg_max f X"
  unfolding has_max_def has_arg_max_def is_arg_max_def
  using not_less by (auto dest!: leD simp: not_less)

lemma has_arg_max_is_arg_max: "has_arg_max f X \<Longrightarrow> is_arg_max f (\<lambda>x. x \<in> X) (arg_max f (\<lambda>x. x \<in> X))"
  unfolding has_arg_max_def arg_max_def
  by (auto intro: someI)

lemma has_arg_max_arg_max: "has_arg_max f X \<Longrightarrow> (arg_max f (\<lambda>x. x \<in> X)) \<in> X"
  unfolding has_arg_max_def arg_max_def
  by (auto; metis is_arg_max_def someI_ex)

lemma app_arg_max_ge: "has_arg_max (f :: 'b \<Rightarrow> real) X \<Longrightarrow> x \<in> X \<Longrightarrow> f x \<le> f (arg_max_on f X)"
  unfolding has_arg_max_def arg_max_on_def arg_max_def is_arg_max_def
  using someI[where ?P = "\<lambda>x. x \<in> X \<and> (\<nexists>y. y \<in> X \<and> f x < f y)"]
  apply auto
  using le_less_linear by blast

lemma app_arg_max_eq_SUP: "has_arg_max (f :: 'b \<Rightarrow> real) X \<Longrightarrow> f (arg_max_on f X) = \<Squnion>(f ` X)"
  by (simp add: arg_max_SUP arg_max_on_def has_arg_max_is_arg_max)

lemma SUP_is_arg_max: assumes "x \<in> X" "bdd_above (f ` X)" "(f :: 'c \<Rightarrow> real) x = \<Squnion>(f ` X)" 
  shows "is_arg_max f (\<lambda>x. x \<in> X) x"
proof -
  show ?thesis
    unfolding is_arg_max_def
    apply simp
    using cSup_upper
    apply auto
    using assms(1) apply blast
    using assms(2) assms(3) cSUP_upper by fastforce
qed

definition "max_L_ex s v \<equiv> has_arg_max (\<lambda>a. L\<^sub>a a v s) (A s)"

text \<open>
We formalize the attainment of the supremum using a predicate @{const has_arg_max}.
\<close>
end

locale MDP_att_\<L> = MDP_reward A K r l
  for
    A and 
    K :: "'s ::countable \<times> 'a ::countable \<Rightarrow> 's pmf" and
    r and l +
  assumes Sup_att: "max_L_ex (s :: 's) v" begin
text \<open>
The error of the resulting policy is bounded by the distance from its value to the value computed 
by the value iteration plus the error in the value iteration itself.
We show that both are less than @{term "eps / 2"} when the algorithm terminates.
\<close>
lemma find_policy_error_bound:
  assumes "eps > 0" "2 * l * dist v (\<L>\<^sub>b v) < eps * (1-l)"
  shows "dist (\<nu>\<^sub>b (mk_stationary (mk_dec_det (find_policy (\<L>\<^sub>b v))))) \<nu>\<^sub>b_opt < eps"
proof -
  let ?d = "(mk_dec_det (find_policy (\<L>\<^sub>b v)))"
  let ?p = "(mk_stationary ?d)"
  have "\<And>v. (L (mk_dec_det (find_policy v)) v) = \<L>\<^sub>b v"
    unfolding find_policy_def
    apply (intro antisym)
    subgoal unfolding less_eq_bfun_def
      unfolding \<L>\<^sub>b.rep_eq \<L>_eq_SUP_det
      apply auto
      apply (intro cSUP_upper)
      apply auto
      subgoal
        unfolding arg_max_on_def
        using Sup_att unfolding is_dec_det_def has_arg_max_def L_det max_L_ex_def arg_max_def
        apply (auto elim!: has_arg_max_arg_max simp: L_det is_arg_max_def)
        by (metis (mono_tags, lifting) is_arg_max_def someI_ex)
      done
    unfolding less_eq_bfun_def
    unfolding \<L>\<^sub>b.rep_eq \<L>_eq_SUP_det
    apply auto
    apply (intro cSUP_least)
    apply auto
    using Sup_att
    by (auto intro: app_arg_max_ge simp: L_det max_L_ex_def is_dec_det_def )
  have "dist (\<nu>\<^sub>b ?p) (\<L>\<^sub>b v) = dist (L ?d (\<nu>\<^sub>b ?p)) (\<L>\<^sub>b v)"
    using L_\<nu>_fix by force
  also have "\<dots> \<le> dist (L ?d (\<nu>\<^sub>b ?p)) (\<L>\<^sub>b (\<L>\<^sub>b v)) + dist (\<L>\<^sub>b (\<L>\<^sub>b v)) (\<L>\<^sub>b v)"
    using dist_triangle by blast
  also have "\<dots> = dist (L ?d (\<nu>\<^sub>b ?p)) (L ?d (\<L>\<^sub>b v)) + dist (\<L>\<^sub>b (\<L>\<^sub>b v)) (\<L>\<^sub>b v)"
    apply (subst  \<open>\<And>v. L (mk_dec_det (find_policy v)) v = \<L>\<^sub>b v\<close>)..
  also have "\<dots> \<le> dist (L ?d (\<nu>\<^sub>b ?p)) (L ?d (\<L>\<^sub>b v)) + l * dist (\<L>\<^sub>b v) v"
    using contraction_\<L> by fastforce
  also have "\<dots> \<le> l * dist (\<nu>\<^sub>b ?p) (\<L>\<^sub>b v) + l * dist (\<L>\<^sub>b v) v"
    using contraction_L by fastforce
  finally have aux: "dist (\<nu>\<^sub>b ?p) (\<L>\<^sub>b v) \<le> l * dist (\<nu>\<^sub>b ?p) (\<L>\<^sub>b v) + l * dist (\<L>\<^sub>b v) v".
  hence "dist (\<nu>\<^sub>b ?p) (\<L>\<^sub>b v) - l * dist (\<nu>\<^sub>b ?p) (\<L>\<^sub>b v) \<le> l * dist (\<L>\<^sub>b v) v"
    by auto
  hence "(1-l) * dist (\<nu>\<^sub>b ?p) (\<L>\<^sub>b v) \<le> l * dist (\<L>\<^sub>b v) v"
    by (simp add: vector_space_over_itself.scale_left_diff_distrib)
  hence  "dist (\<nu>\<^sub>b ?p) (\<L>\<^sub>b v) \<le> (l / (1-l)) * dist (\<L>\<^sub>b v) v"
    by (simp add: mult.commute pos_le_divide_eq)
  hence  "2 * dist (\<nu>\<^sub>b ?p) (\<L>\<^sub>b v) \<le> 2 * ((l / (1-l)) * dist (\<L>\<^sub>b v) v)"
    using zero_le_disc
    using mult_left_mono by fastforce
  also have "...  = (1 / (1-l)) * (2 * l * dist (\<L>\<^sub>b v) v)"
    by simp
  also have "\<dots> \<le> (1 / (1-l)) *(eps * (1-l)) "
    using assms
    by (auto intro!: mult_left_mono simp: dist_commute pos_divide_le_eq)
  finally have "2 * dist (\<nu>\<^sub>b ?p) (\<L>\<^sub>b v) \<le>(1 / (1-l)) *(eps * (1-l)) ".
  hence lhs: "dist (\<nu>\<^sub>b ?p) (\<L>\<^sub>b v) \<le> eps / 2"
    apply auto using assms(1)
    using disc_lt_one by force
  have rhs: "dist (\<L>\<^sub>b v) \<nu>\<^sub>b_opt < eps / 2"
    using dist_\<L>\<^sub>b_opt_eps assms by blast
  have "dist (\<nu>\<^sub>b ?p) \<nu>\<^sub>b_opt \<le> dist (\<nu>\<^sub>b ?p) (\<L>\<^sub>b v) + dist (\<L>\<^sub>b v) \<nu>\<^sub>b_opt"
    using dist_triangle by blast    
  thus ?thesis 
    using lhs rhs by auto
qed

lemma value_iteration_policy_opt: 
  assumes "0 < eps"
  shows "dist (\<nu>\<^sub>b (mk_stationary (mk_dec_det (find_policy (value_iteration eps v))))) \<nu>\<^sub>b_opt < eps"
  using assms proof (induction eps "v" rule: value_iteration.induct)
  case (1 v)
  then show ?case
    apply (subst value_iteration.simps)
    apply (auto simp del: value_iteration.simps)
    using find_policy_error_bound
    by blast
qed

lemma vi_policy_opt:
  assumes "eps > 0"
  shows "dist (\<nu>\<^sub>b (mk_stationary (mk_dec_det (vi_policy eps v)))) \<nu>\<^sub>b_opt < eps"
  using assms(1) value_iteration_policy_opt vi_policy_def by presburger

section \<open>Policy Iteration\<close>
text \<open>
The Policy Iteration algorithms provides another way to find optimal policies under the expected 
total reward criterion.
It differs from Value Iteration in that it continuously improves an initial guess for an optimal 
decision rule. Its execution can be subdivided into two alternating steps: policy evaluation and 
policy improvement.

Policy evaluation means the calculation of the value of the current decision rule.

During the improvement phase, we choose the decision rule with the maximum value for L, 
while we prefer to keep the old action selection in case of ties.
\<close>

definition "policy_eval d = \<nu>\<^sub>b (mk_stationary (mk_dec_det d))"

end

locale MDP_PI = MDP_att_\<L> A K r l 
  for A :: "'s :: countable \<Rightarrow> ('a :: countable) set" and K r l
    +
  fixes arg_max_L\<^sub>a ::  "('s \<Rightarrow> real) \<Rightarrow> 's \<Rightarrow> 'a"
  assumes arg_max_L\<^sub>a [simp]: "is_arg_max (\<lambda>a. L\<^sub>a a v s) (\<lambda>a. a \<in> A s) (arg_max_L\<^sub>a v s)"
begin

definition "policy_improvement d v s = (
  if is_arg_max (\<lambda>a. L\<^sub>a a v s) (\<lambda>a. a \<in> A s) (d s) 
  then d s
  else arg_max_L\<^sub>a v s)"

definition "policy_step d = policy_improvement d (policy_eval d)"

function policy_iteration :: "('s \<Rightarrow> 'a) \<Rightarrow> ('s \<Rightarrow> 'a)" where
  "policy_iteration d = (
  let d' = policy_step d in
  if d = d' \<or> \<not>is_dec_det d then d else policy_iteration d')"
  by auto

text \<open>
The policy iteration algorithm as stated above does require that the supremum in @{const \<L>\<^sub>b} is
always attained.
\<close>

text \<open>
Each policy improvement returns a valid decision rule.
\<close>
lemma is_dec_det_pi: "is_dec_det (policy_improvement d v)"
  unfolding policy_improvement_def is_dec_det_def is_arg_max_def
  using arg_max_L\<^sub>a 
  by (auto simp: is_arg_max_linorder)

lemma eval_policy_step_L:
  assumes "is_dec_det d"
  shows "L (mk_dec_det (policy_step d)) (policy_eval d) = \<L>\<^sub>b (policy_eval d)"
  unfolding policy_eval_def policy_step_def 
  apply (intro bfun_eqI)
  unfolding L_det
  unfolding  \<L>\<^sub>b.rep_eq \<L>_eq_SUP_det SUP_step_det_eq
  unfolding policy_improvement_def
  using assms unfolding is_dec_det_def 
  apply auto
  apply (intro antisym)
  apply (intro cSUP_upper)
  apply auto
  subgoal
    using step_v_le by (auto intro!: boundedI[of _ "r\<^sub>M + l * norm _"] bounded_imp_bdd_above)
  apply (intro cSUP_least)
  apply auto
  subgoal unfolding is_arg_max_def
    by auto
  apply (intro antisym)
  apply (intro cSUP_upper)
  subgoal using assms unfolding max_L_ex_def
    unfolding arg_max_on_def
    using has_arg_max_is_arg_max[OF Sup_att[unfolded max_L_ex_def]] is_arg_max_def
    using arg_max_L\<^sub>a
    unfolding is_arg_max_def
    by auto
  subgoal
    using step_v_le by (auto intro!: boundedI[of _ "r\<^sub>M + l * norm _"] bounded_imp_bdd_above)
  apply (intro cSUP_least)
  apply auto[1]
  unfolding arg_max_on_def
  using has_arg_max_is_arg_max[OF Sup_att[unfolded max_L_ex_def]] is_arg_max_def
  using arg_max_L\<^sub>a
  unfolding arg_max_def is_arg_max_def
  apply auto
  by (meson not_le)


text \<open> The sequence of policies generated by policy iteration has monotonically increasing 
discounted reward.\<close>
lemma policy_eval_mon:
  assumes "is_dec_det d"
  shows "policy_eval d \<le> policy_eval (policy_step d)"
proof -
  let ?d' = "mk_dec_det (policy_step d)"
  let ?dp = "mk_stationary (mk_dec_det d)"

  have aux: "L (mk_dec_det d) (policy_eval d) \<le> L ?d' (policy_eval d)"
    apply (subst eval_policy_step_L)
    using assms
    by (auto simp add: MDP_reward.L_le_\<L> MDP_reward_axioms)
  have "L (mk_dec_det d) (policy_eval d) = (policy_eval d)"
    using L_\<nu>_fix policy_eval_def by presburger
  hence "policy_eval d \<le> L ?d' (policy_eval d)"
    using aux by auto
  hence "\<nu>\<^sub>b ?dp \<le> r_dec\<^sub>b ?d' 
    + l *\<^sub>R \<K>_st ?d' (\<nu>\<^sub>b ?dp)"
    unfolding policy_eval_def L_def
    by auto
  hence "(id_blinfun - l *\<^sub>R \<K>_st ?d') (\<nu>\<^sub>b ?dp) \<le> r_dec\<^sub>b ?d'"
    by (simp add: blinfun.diff_left diff_le_eq scaleR_blinfun.rep_eq)
  hence "(\<Sum>t. l ^ t *\<^sub>R \<K>_st ?d' ^^ t) ((id_blinfun - l *\<^sub>R \<K>_st ?d') (\<nu>\<^sub>b ?dp)) \<le> 
    (\<Sum>t. l ^ t *\<^sub>R \<K>_st ?d' ^^ t) (r_dec\<^sub>b ?d')"
    using lemma_6_1_2_b
    by auto
  hence "((\<Sum>t. l ^ t *\<^sub>R \<K>_st ?d' ^^ t) o\<^sub>L (id_blinfun - l *\<^sub>R \<K>_st ?d')) (\<nu>\<^sub>b ?dp) \<le> 
    (\<Sum>t. l ^ t *\<^sub>R \<K>_st ?d' ^^ t) (r_dec\<^sub>b ?d')"
    by auto
  hence "\<nu>\<^sub>b ?dp \<le> (\<Sum>t. l ^ t *\<^sub>R \<K>_st ?d' ^^ t) (r_dec\<^sub>b ?d')"
    using inv_norm_le(2)[OF norm_\<K>_st_l_less, of "?d'"] blinfun_apply_id_blinfun
    by (metis (mono_tags, lifting) blincomp_scaleR_right suminf_cong)
  hence "\<nu>\<^sub>b ?dp \<le> \<nu>\<^sub>b (mk_stationary ?d')"
    by (simp add: \<nu>_stationary)
  thus "policy_eval d \<le> policy_eval (policy_step d)"
    unfolding policy_eval_def
    by auto
qed

text \<open>
If policy iteration terminates, i.e. @{term "d = policy_step d"}, then it does so with optimal value.
\<close>
lemma policy_step_eq_imp_opt:
  assumes "is_dec_det d" "d = policy_step d" 
  shows "\<nu>\<^sub>b (mk_stationary (mk_dec_det d)) = \<nu>\<^sub>b_opt"
proof -
  have "policy_eval d = L (mk_dec_det d) (policy_eval d)"
    unfolding policy_eval_def
    using L_\<nu>_fix by auto
  also have "\<dots> = L (mk_dec_det (policy_step d)) (policy_eval d)"
    using assms by force
  also have "\<dots> = \<L>\<^sub>b (policy_eval d)"
    using assms Sup_att eval_policy_step_L by blast
  finally have "policy_eval d = \<L>\<^sub>b (policy_eval d)".
  hence "\<nu>\<^sub>b (mk_stationary (mk_dec_det d)) = \<L>\<^sub>b (\<nu>\<^sub>b (mk_stationary (mk_dec_det d)))"
    unfolding policy_eval_def by auto
  thus "\<nu>\<^sub>b (mk_stationary (mk_dec_det d)) = \<nu>\<^sub>b_opt"
    using lemma_6_2_2_c by blast
qed



definition "find_policy' (v :: 's \<Rightarrow>\<^sub>b real) s = arg_max_L\<^sub>a v s"

definition "vi_policy' eps v = find_policy' (value_iteration eps v)"

thm find_policy_error_bound
lemma find_policy'_error_bound:
  assumes "eps > 0" "(2 * l) * dist v (\<L>\<^sub>b v) < eps * (1-l)"
  shows "dist (\<nu>\<^sub>b (mk_stationary (mk_dec_det (find_policy' (\<L>\<^sub>b v))))) \<nu>\<^sub>b_opt < eps"

proof -
  let ?d = "(mk_dec_det (find_policy' (\<L>\<^sub>b v)))"
  let ?p = "(mk_stationary ?d)"
  have "\<And>v. (L (mk_dec_det (find_policy' v)) v) = \<L>\<^sub>b v"
    unfolding find_policy'_def
    apply (intro antisym)
    subgoal unfolding less_eq_bfun_def
      unfolding \<L>\<^sub>b.rep_eq \<L>_eq_SUP_det
      apply auto
      apply (intro cSUP_upper)
      apply auto
      by (metis (mono_tags, lifting) arg_max_L\<^sub>a is_arg_max_linorder is_dec_det_def)
    unfolding less_eq_bfun_def
    unfolding \<L>\<^sub>b.rep_eq \<L>_eq_SUP_det
    apply auto
    apply (intro cSUP_least)
    apply (simp; fail)
    using Sup_att
    apply (auto intro: app_arg_max_ge simp: L_det max_L_ex_def is_dec_det_def)
    by (metis (mono_tags, lifting) arg_max_L\<^sub>a is_arg_max_linorder)
  have "dist (\<nu>\<^sub>b ?p) (\<L>\<^sub>b v) = dist (L ?d (\<nu>\<^sub>b ?p)) (\<L>\<^sub>b v)"
    using L_\<nu>_fix by force
  also have "\<dots> \<le> dist (L ?d (\<nu>\<^sub>b ?p)) (\<L>\<^sub>b (\<L>\<^sub>b v)) + dist (\<L>\<^sub>b (\<L>\<^sub>b v)) (\<L>\<^sub>b v)"
    using dist_triangle by blast
  also have "\<dots> = dist (L ?d (\<nu>\<^sub>b ?p)) (L ?d (\<L>\<^sub>b v)) + dist (\<L>\<^sub>b (\<L>\<^sub>b v)) (\<L>\<^sub>b v)"
    apply (subst  \<open>\<And>v. L (mk_dec_det (find_policy' v)) v = \<L>\<^sub>b v\<close>)..
  also have "\<dots> \<le> dist (L ?d (\<nu>\<^sub>b ?p)) (L ?d (\<L>\<^sub>b v)) + l * dist (\<L>\<^sub>b v) v"
    using contraction_\<L> by fastforce
  also have "\<dots> \<le> l * dist (\<nu>\<^sub>b ?p) (\<L>\<^sub>b v) + l * dist (\<L>\<^sub>b v) v"
    using contraction_L by fastforce
  finally have "dist (\<nu>\<^sub>b ?p) (\<L>\<^sub>b v) \<le> l * dist (\<nu>\<^sub>b ?p) (\<L>\<^sub>b v) + l * dist (\<L>\<^sub>b v) v".
  hence "dist (\<nu>\<^sub>b ?p) (\<L>\<^sub>b v) - l * dist (\<nu>\<^sub>b ?p) (\<L>\<^sub>b v) \<le> l * dist (\<L>\<^sub>b v) v"
    by auto
  hence "(1-l) * dist (\<nu>\<^sub>b ?p) (\<L>\<^sub>b v) \<le> l * dist (\<L>\<^sub>b v) v"
    by (simp add: vector_space_over_itself.scale_left_diff_distrib)
  hence  "dist (\<nu>\<^sub>b ?p) (\<L>\<^sub>b v) \<le> (l / (1-l)) * dist (\<L>\<^sub>b v) v"
    by (simp add: mult.commute pos_le_divide_eq)
  hence  "2 * dist (\<nu>\<^sub>b ?p) (\<L>\<^sub>b v) \<le> 2 * ((l / (1-l)) * dist (\<L>\<^sub>b v) v)"
    using zero_le_disc
    using mult_left_mono by fastforce
  also have "...  = (1 / (1-l)) * (2 * l * dist (\<L>\<^sub>b v) v)"
    by simp
  also have "\<dots> \<le> (1 / (1-l)) *(eps * (1-l)) "
    using assms
    apply (intro mult_left_mono)
    by (auto simp add: dist_commute less_eq_real_def)
  finally have "2 * dist (\<nu>\<^sub>b ?p) (\<L>\<^sub>b v) \<le>(1 / (1-l)) *(eps * (1-l)) ".
  hence lhs: "dist (\<nu>\<^sub>b ?p) (\<L>\<^sub>b v) \<le> eps / 2"
    apply auto using assms(1)
    using disc_lt_one by force
  have rhs: "dist (\<L>\<^sub>b v) \<nu>\<^sub>b_opt < eps / 2"
    using dist_\<L>\<^sub>b_opt_eps assms by blast
  have "dist (\<nu>\<^sub>b ?p) \<nu>\<^sub>b_opt \<le> dist (\<nu>\<^sub>b ?p) (\<L>\<^sub>b v) + dist (\<L>\<^sub>b v) \<nu>\<^sub>b_opt"
    using dist_triangle by blast    
  thus ?thesis 
    using lhs rhs by auto
qed

lemma value_iteration_policy_opt': 
  assumes "0 < eps"
  shows "dist (\<nu>\<^sub>b (mk_stationary (mk_dec_det (find_policy' (value_iteration eps v))))) \<nu>\<^sub>b_opt < eps"
  using assms proof (induction eps "v" rule: value_iteration.induct)
  case (1 v)
  then show ?case
    apply (subst value_iteration.simps)
    apply (auto simp del: value_iteration.simps)
    using find_policy'_error_bound
    by blast
qed

lemma vi_policy'_opt:
  assumes "eps > 0" "l > 0"
  shows "dist (\<nu>\<^sub>b (mk_stationary (mk_dec_det (vi_policy' eps v)))) \<nu>\<^sub>b_opt < eps"
  using assms(1) assms(2) value_iteration_policy_opt' vi_policy'_def by presburger
end

text \<open>We prove termination of policy iteration only if both the state and action sets are finite.\<close>
locale MDP_PI_finite = MDP_PI A K r l argmax
  for
    A and
    K :: "'s ::countable \<times> 'a ::countable \<Rightarrow> 's pmf" and r l argmax +
  assumes fin_states: "finite (UNIV :: 's set)" and fin_actions: "\<And>s. finite (A s)"
begin

text \<open>If the state and action sets are both finite, 
  then so is the set of deterministic decision rules @{const "D\<^sub>D"}\<close>
lemma finite_D\<^sub>D[simp]: "finite D\<^sub>D"
proof -
  have "finite (\<Union>s. A s)"
    using fin_actions fin_states by blast
  hence "finite {d. \<forall>x :: 's. (x \<in> UNIV \<longrightarrow> d x \<in> (\<Union>s. A s)) \<and> (x \<notin> UNIV \<longrightarrow> d x = undefined)}"
    apply (intro finite_set_of_finite_funs)
    using fin_states apply blast
    by auto
  moreover have "D\<^sub>D \<subseteq>{d. \<forall>x :: 's. (x \<in> UNIV \<longrightarrow> d x \<in> (\<Union>s. A s)) \<and> (x \<notin> UNIV \<longrightarrow> d x = undefined)}"
    unfolding is_dec_det_def by auto
  ultimately show  ?thesis
    using finite_subset by auto
qed

lemma finite_rel: "finite {(u, v). is_dec_det u \<and> is_dec_det v \<and> \<nu>\<^sub>b (mk_stationary (mk_dec_det u)) > 
  \<nu>\<^sub>b (mk_stationary (mk_dec_det v))}"
proof-
  have "finite (D\<^sub>D \<times> D\<^sub>D)"
    by auto
  have aux: "finite {(u, v). is_dec_det u \<and> is_dec_det v}"
    by auto
  thus ?thesis
    apply (intro finite_subset[OF _ aux]) by auto
qed

lemma max_L_ex_finite[simp]: "max_L_ex s v" using Sup_att.

text \<open>
This auxiliary lemma shows that policy iteration terminates if no improvement to the value of 
the policy could be made, as then the policy remains unchanged.
\<close>
lemma eval_eq_imp_policy_eq: 
  assumes "policy_eval d = policy_eval (policy_step d)" "is_dec_det d"
  shows "d = policy_step d"
proof -
  have "\<And>s. policy_eval d s = policy_eval (policy_step d) s"
    using assms by auto
  have "policy_eval d = L (mk_dec_det d) (policy_eval (policy_step d))"
    unfolding policy_eval_def
    using L_\<nu>_fix by (auto simp: assms(1)[symmetric, unfolded policy_eval_def])
  hence "policy_eval d = \<L>\<^sub>b (policy_eval d)"
    by (metis L_\<nu>_fix policy_eval_def assms(1) assms(2) eval_policy_step_L)
  hence "\<And>s. L (mk_dec_det d) (policy_eval d) s = \<L>\<^sub>b (policy_eval d) s"
    using \<open>policy_eval d = L (mk_dec_det d) (policy_eval (policy_step d))\<close> assms(1) by auto
  hence "\<And>s. is_arg_max (\<lambda>a. L\<^sub>a a (\<nu>\<^sub>b (mk_stationary (mk_dec_det d))) s) (\<lambda>a. a \<in> A s) (d s)"
    unfolding L_det
    unfolding policy_eval_def
    unfolding  \<L>\<^sub>b.rep_eq \<L>_eq_SUP_det SUP_step_det_eq
    apply (intro SUP_is_arg_max)
    apply auto
    using assms(2) is_dec_det_def apply blast
    using step_v_le by (auto intro!: boundedI[of _ "r\<^sub>M + l * norm _"] bounded_imp_bdd_above)
  thus ?thesis
    unfolding policy_eval_def policy_step_def policy_improvement_def
    by auto
qed

text \<open>
We are now ready to prove termination in the context of finite state-action spaces.
Intuitively, the algorithm terminates as there are only finitely many decision rules,
and in each recursive call the value of the decision rule increases.
\<close>
termination policy_iteration
  apply (relation "{(u, v). u \<in> D\<^sub>D \<and> v \<in> D\<^sub>D \<and> \<nu>\<^sub>b (mk_stationary (mk_dec_det u)) > 
    \<nu>\<^sub>b (mk_stationary (mk_dec_det v))}")
  apply (auto intro: finite_acyclic_wf)
  apply (intro finite_acyclic_wf)
  using finite_rel apply simp
  apply (intro acyclicI_order)
  apply auto
  subgoal unfolding policy_step_def using is_dec_det_pi by simp
proof -
  fix d
  assume "d \<noteq> policy_step d" "is_dec_det d"
  hence aux: "\<nu>\<^sub>b (mk_stationary (mk_dec_det d)) \<le> \<nu>\<^sub>b (mk_stationary (mk_dec_det (policy_step d)))"
    using policy_eval_mon unfolding policy_eval_def by simp
  have "\<nu>\<^sub>b (mk_stationary (mk_dec_det d)) \<noteq> \<nu>\<^sub>b (mk_stationary (mk_dec_det (policy_step d)))"
    using \<open>d \<noteq> policy_step d\<close> \<open>is_dec_det d\<close> eval_eq_imp_policy_eq policy_eval_def by force
  thus "\<nu>\<^sub>b (mk_stationary (mk_dec_det d)) < \<nu>\<^sub>b (mk_stationary (mk_dec_det (policy_step d)))"
    by (simp add: aux less_le)
qed

text \<open>
The termination proof gives us access to the induction rule/simplification lemmas associated 
with the @{const policy_iteration} definition.
Thus we can prove that the algorithm finds an optimal policy.
\<close>
lemma policy_iteration_correct: 
  "d \<in> D\<^sub>D \<Longrightarrow> \<nu>\<^sub>b (mk_stationary (mk_dec_det (policy_iteration d))) = \<nu>\<^sub>b_opt" 
proof (induction d rule: policy_iteration.induct)
  case (1 d)
  have aux: "(let d' = policy_step d in if d = d' then d else policy_iteration d') = 
    (if d = policy_step d then d else policy_iteration (policy_step d))"
    by presburger
  then show ?case
    apply (subst policy_iteration.simps)
    using "1.prems" apply (auto simp del: policy_iteration.simps simp: aux split: if_splits)
    using max_L_ex_finite policy_step_eq_imp_opt apply blast
    by (metis "1.IH" is_dec_det_pi mem_Collect_eq policy_step_def)
qed

end

locale MDP_finite_type = MDP_reward A K r l
  for
    A and 
    K :: "'s ::finite \<times> 'a ::finite \<Rightarrow> 's pmf" and
    r and l
begin

text \<open>
The following proofs concern code generation, i.e. how to represent @{const \<K>_st} as a matrix.
\<close>

sublocale MDP_att_\<L>
  by (auto simp: A_ne finite_is_arg_max MDP_att_\<L>_def MDP_att_\<L>_axioms_def max_L_ex_def 
      has_arg_max_def MDP_reward_axioms) 

definition "fun_to_matrix f = matrix (\<lambda>v. (\<chi> j. f (vec_nth v) j))"
definition "Ek_mat d = fun_to_matrix (\<lambda>v. ((\<K>_st d) (Bfun v)))"
definition "nu_inv_mat d = fun_to_matrix ((\<lambda>v. ((id_blinfun - l *\<^sub>R \<K>_st d) (Bfun v))))"
definition "nu_mat d = fun_to_matrix (\<lambda>v. ((\<Sum>i. (l *\<^sub>R \<K>_st d) ^^ i) (Bfun v)))"

lemma vec_bfun[simp, intro]: "($) x \<in> bfun"
  unfolding bfun_def
  by auto

lemma bounded_linear_bfun_nth: "bounded_linear f \<Longrightarrow> bounded_linear (\<lambda>v. bfun.Bfun (($) (f v)))"
  apply (intro bounded_linear_intro[where K = "onorm f"])
  apply (auto simp: Bfun_inverse intro!: bfun_eqI)
  apply (simp add: linear_simps(1))
  apply (simp add: linear_simps(5))
  apply (subst norm_bfun_def)
  apply (subst  dist_bfun_def)
  apply (auto simp: Bfun_inverse intro!: bfun_eqI)
  apply (intro cSup_least)
  apply auto
  by (metis (no_types) Finite_Cartesian_Product.norm_nth_le mult.commute onorm order_trans)

lemma norm_bfun_le_norm_vec: "norm (bfun.Bfun (($) (x :: real^'c :: finite))) \<le> norm x"
proof -
  have "norm (bfun.Bfun (($) (x :: real^'c :: finite))) \<le> (\<Squnion>xa. \<bar>x $ xa\<bar>)"
    unfolding norm_bfun_def dist_bfun_def norm_vec_def
    by (auto simp: Bfun_inverse)
  also have "\<dots> \<le> norm x"
    apply (intro cSUP_least)
    apply auto
    using component_le_norm_cart by blast
  finally show ?thesis by auto
qed

lemma apply_nu_inv_mat: 
  "(id_blinfun - l *\<^sub>R \<K>_st d) v = Bfun (\<lambda>i. ((nu_inv_mat d) *v (vec_lambda v)) $ i)" 
  unfolding Ek_mat_def fun_to_matrix_def nu_inv_mat_def
  apply (subst matrix_vector_mul(2))
  apply auto
  subgoal
    apply (intro linearI)
    subgoal 
      by (auto simp: eq_onpI plus_vec_def vec_lambda_inverse plus_bfun.abs_eq[symmetric] 
           blinfun.add_right)
    by (auto simp del: real_scaleR_def simp: scaleR_vec_def vec_lambda_inverse
        scaleR_bfun.abs_eq[symmetric] eq_onpI blinfun.scaleR_right)
  by (simp add: apply_bfun_inverse vec_lambda_inverse)

lemma invertible_nu_inv_max: "invertible (nu_inv_mat d)"
  unfolding nu_inv_mat_def fun_to_matrix_def
  apply (subst matrix_invertible)
  subgoal 
    apply (intro linearI)
    apply (auto simp: plus_vec_def vec_lambda_inverse plus_bfun.abs_eq[symmetric] 
        eq_onpI blinfun.add_right)
    by (auto simp del: real_scaleR_def simp: scaleR_vec_def vec_lambda_inverse 
        scaleR_bfun.abs_eq[symmetric] eq_onpI blinfun.scaleR_right)
  apply (intro exI[of _ "\<lambda>v. (\<chi> j. (\<lambda>v. (\<Sum>i. (l *\<^sub>R \<K>_st d) ^^ i) (Bfun v)) (vec_nth v) j)"])
  apply auto
  subgoal 
    apply (intro linearI)
    apply (auto simp: plus_vec_def vec_lambda_inverse plus_bfun.abs_eq[symmetric] 
        eq_onpI blinfun.add_right)
    by (auto simp del: real_scaleR_def simp: scaleR_vec_def vec_lambda_inverse 
        scaleR_bfun.abs_eq[symmetric] eq_onpI blinfun.scaleR_right)
  apply standard
  apply (auto simp: vec_eq_iff)
  apply (subst vec_lambda_inverse)
  apply auto
  apply (auto simp: apply_bfun_inverse)
  apply (metis (no_types, lifting) bfun.Bfun_inverse blinfun_apply_blinfun_compose 
      blinfun_apply_id_blinfun inv_norm_le(1) norm_\<K>_st_l_less suminf_cong vec_bfun)
  apply standard
  apply (auto simp: vec_eq_iff)
  apply (subst vec_lambda_inverse)
  apply (auto simp: apply_bfun_inverse)
  by (metis (no_types, lifting) bfun.Bfun_inverse blinfun_apply_blinfun_compose 
      blinfun_apply_id_blinfun inv_norm_le(2) norm_\<K>_st_l_less suminf_cong vec_bfun)

lemma nu_mat_inv: "nu_mat d = matrix_inv (nu_inv_mat d)"
  apply (intro matrix_inv_unique[symmetric])
  unfolding nu_inv_mat_def nu_mat_def fun_to_matrix_def
  apply (subst matrix_compose_gen[symmetric])
  subgoal 
    apply (subst linear_matrix_vector_mul_eq)
    apply (intro linearI)
    apply (auto simp: plus_vec_def vec_lambda_inverse plus_bfun.abs_eq[symmetric] 
        eq_onpI blinfun.add_right)
    by (auto simp del: real_scaleR_def simp: scaleR_vec_def vec_lambda_inverse 
        scaleR_bfun.abs_eq[symmetric] eq_onpI blinfun.scaleR_right)
  subgoal 
    apply (subst linear_matrix_vector_mul_eq)
    apply (intro linearI)
    apply (auto simp: plus_vec_def vec_lambda_inverse plus_bfun.abs_eq[symmetric] 
        eq_onpI blinfun.add_right)
    by (auto simp del: real_scaleR_def simp: scaleR_vec_def vec_lambda_inverse 
        scaleR_bfun.abs_eq[symmetric] eq_onpI blinfun.scaleR_right)
  apply (auto simp: comp_def matrix_id_mat_1[symmetric])
  apply (rule arg_cong[where f =matrix])
  apply standard
  apply (auto simp: vec_nth_inverse vec_lambda_inverse Bfun_inverse apply_bfun_inverse 
      vec_eq_iff blinfun_compose.rep_eq[unfolded comp_def, symmetric])
  apply (subst blinfun_apply_blinfun_compose[symmetric])
  apply (subst inv_norm_le(1))
  apply (auto simp add: bfun.Bfun_inverse)
  apply (subst matrix_compose_gen[symmetric])
  subgoal 
    apply (subst linear_matrix_vector_mul_eq)
    apply (intro linearI)
    apply (auto simp: plus_vec_def vec_lambda_inverse plus_bfun.abs_eq[symmetric] 
        eq_onpI blinfun.add_right)
    by (auto simp del: real_scaleR_def simp: scaleR_vec_def vec_lambda_inverse 
        scaleR_bfun.abs_eq[symmetric] eq_onpI blinfun.scaleR_right)
  subgoal 
    apply (subst linear_matrix_vector_mul_eq)
    apply (intro linearI)
    apply (auto simp: plus_vec_def vec_lambda_inverse plus_bfun.abs_eq[symmetric] 
        eq_onpI blinfun.add_right)
    by (auto simp del: real_scaleR_def simp: scaleR_vec_def vec_lambda_inverse 
        scaleR_bfun.abs_eq[symmetric] eq_onpI blinfun.scaleR_right)
  apply (auto simp: comp_def matrix_id_mat_1[symmetric] vec_eq_iff)
  apply (rule arg_cong[where f ="\<lambda>x. matrix x $ _ $ _"])
  apply standard
  apply (auto simp: vec_nth_inverse vec_lambda_inverse Bfun_inverse apply_bfun_inverse 
      vec_eq_iff blinfun_compose.rep_eq[unfolded comp_def, symmetric])
  apply (subst blinfun_apply_blinfun_compose[symmetric])
  apply (subst inv_norm_le(2))
  by (auto simp add: bfun.Bfun_inverse)

lemma nu_inv_mat_eq: "nu_inv_mat d = mat 1 - l *\<^sub>R Ek_mat d"
  unfolding nu_inv_mat_def fun_to_matrix_def Ek_mat_def matrix_id_mat_1[symmetric] matrix_def
  by (auto simp: vec_eq_iff blinfun.diff_left Bfun_inverse blinfun.scaleR_left)


lemma norm_vec_le_norm_bfun: 
  "norm (vec_lambda (apply_bfun (x :: 'd::finite \<Rightarrow>\<^sub>b real))) \<le> norm x * card (UNIV :: 'd set)"
proof -
  have "norm (vec_lambda (apply_bfun x)) \<le> (\<Sum> i \<in> UNIV . \<bar>(apply_bfun x i)\<bar>)"
    unfolding norm_vec_def L2_set_def
    using L2_set_le_sum_abs unfolding L2_set_def
    by auto
  also have "\<dots> \<le> (card (UNIV :: 'd set) * (\<Squnion>xa. \<bar>apply_bfun x xa\<bar>))"
    apply (intro sum_bounded_above)
    apply auto
    apply (intro cSup_upper)
    by auto
  finally show ?thesis
    by (simp add: norm_bfun_def dist_bfun_def mult.commute)
qed

lemma "Ek_mat d *v v = vec_lambda (apply_bfun (blinfun_apply (\<K>_st d) (Bfun (vec_nth v))))"
  unfolding Ek_mat_def fun_to_matrix_def
  apply (subst matrix_vector_mul(3))
  apply auto
  apply (rule bounded_linear_compose[where f = "\<lambda>v. vec_lambda (apply_bfun v)"])
  apply (intro bounded_linear_intro[where K = "card (UNIV :: 's set)"])
  apply (auto simp: plus_vec_def)
  apply (metis (mono_tags, lifting) Cart_lambda_cong real_scaleR_def scaleR_vec_def vec_lambda_beta)
  subgoal using norm_vec_le_norm_bfun by auto
  apply (intro bounded_linear_blinfun_apply)
  apply (intro bounded_linear_intro[where K = 1])
  apply (intro bfun_eqI)
  apply (auto simp: Bfun_inverse)
  apply (simp add: bfun.Bfun_inverse bfun_eqI)
  using norm_bfun_le_norm_vec 
  by auto


lemma suminf_Ek_mat[code_unfold]: "(\<Sum>i. l^i *\<^sub>R \<K>_st d^^i) = 
  Blinfun (\<lambda>v. Bfun (\<lambda>s. (nu_mat d *v (vec_lambda (apply_bfun v))) $ s))" 
  (is "?r = ?l")
proof -
  have "(id_blinfun - l *\<^sub>R \<K>_st d) o\<^sub>L ?l = (id_blinfun - l *\<^sub>R \<K>_st d) o\<^sub>L ?r \<Longrightarrow> ?l = ?r"
    by (metis (no_types, lifting) blinfun_compose_assoc blinfun_compose_id(1) 
        inv_norm_le(2) norm_\<K>_st_l_less)
  hence l_eq_r: "(id_blinfun - l *\<^sub>R \<K>_st d) o\<^sub>L ?l = id_blinfun \<Longrightarrow> ?l = ?r"
    by (metis (no_types, lifting) blincomp_scaleR_right blinfun_compose_assoc blinfun_compose_id(2) 
        inv_norm_le(2) norm_\<K>_st_l_less suminf_cong)
  have aux: "\<And>v r. (\<chi> xa. r * v xa) = r *s (\<chi> xa. v xa)"
    by (metis (no_types, lifting) Cart_lambda_cong vec_lambda_beta vector_scalar_mult_def)
  have bl: "bounded_linear (\<lambda>v. bfun.Bfun (($) (nu_mat d *v vec_lambda (apply_bfun v))))"
    apply (rule bounded_linear_compose[where f = "\<lambda>v. Bfun (($) v)"])
    apply (intro bounded_linear_bfun_nth)
    apply simp
    apply (rule bounded_linear_compose[where g = "\<lambda>x. vec_lambda (apply_bfun x)"])
    apply auto
    apply (intro bounded_linear_intro[where K = "(card (UNIV :: 's set))"])
    apply auto
    apply (metis (no_types, lifting) plus_vec_def vec_lambda_unique)
    apply (subst aux) 
    apply (simp add: scalar_mult_eq_scaleR)
    unfolding norm_vec_def norm_bfun_def dist_bfun_def
    apply auto
    unfolding L2_set_def
  proof -
    fix x :: "'s \<Rightarrow>\<^sub>b real"
    have "sqrt (\<Sum> i \<in> UNIV . (apply_bfun x i)\<^sup>2) \<le> (\<Sum> i \<in> UNIV . \<bar>(apply_bfun x i)\<bar>)"
      using L2_set_le_sum_abs unfolding L2_set_def
      by auto
    also have 
      "(\<Sum> i \<in> UNIV . \<bar>(apply_bfun x i)\<bar>) \<le> (card (UNIV :: 's set) * (\<Squnion>xa. \<bar>apply_bfun x xa\<bar>))"
      apply (intro sum_bounded_above)
      apply auto
      apply (intro cSup_upper)
      by auto
    finally show "sqrt (\<Sum>i\<in>UNIV. \<bar>apply_bfun x i\<bar>\<^sup>2) \<le> (\<Squnion>xa. \<bar>apply_bfun x xa\<bar>) * CARD('s)"
      apply auto
      by (simp add: mult.commute)
  qed
  have aux: "\<And>i. (mat 1 - l *\<^sub>R Ek_mat d) *v 
    (matrix_inv (mat 1 - l *\<^sub>R Ek_mat d) *v vec_lambda (apply_bfun i)) = 
      (mat 1 - l *\<^sub>R Ek_mat d) ** (matrix_inv (mat 1 - l *\<^sub>R Ek_mat d)) *v vec_lambda (apply_bfun i)"
    by (meson matrix_vector_mul_assoc)
  have "(id_blinfun - l *\<^sub>R \<K>_st d) o\<^sub>L ?l = id_blinfun"
    apply (intro blinfun_eqI)
    using bl
    apply (auto simp: Blinfun_inverse blinfun_apply_inverse)
    unfolding nu_mat_def fun_to_matrix_def
    apply (subst matrix_vector_mul(2))
    subgoal
      apply (intro linearI)
       apply (auto simp: plus_vec_def vec_lambda_inverse plus_bfun.abs_eq[symmetric] 
              blinfun.add_right eq_onpI)
      by (auto simp del: real_scaleR_def simp: scaleR_vec_def vec_lambda_inverse 
          scaleR_bfun.abs_eq[symmetric] eq_onpI blinfun.scaleR_right)
    apply (auto simp: vec_lambda_inverse Bfun_inverse apply_bfun_inverse)
    by (metis (no_types, lifting) blinfun_apply_blinfun_compose bounded_linear_Blinfun_apply 
        bounded_linear_ident id_blinfun.abs_eq inv_norm_le(1) norm_\<K>_st_l_less suminf_cong)
  thus ?thesis
    using l_eq_r by auto
qed

lemma policy_eval_code: "policy_eval d = (\<lambda>v. Bfun (\<lambda>s. 
  (nu_mat (mk_dec_det d) *v (vec_lambda (apply_bfun v))) $ s)) (r_dec\<^sub>b (mk_dec_det d))"
  unfolding policy_eval_def
  apply (auto simp:  \<nu>_stationary suminf_Ek_mat)
  apply (subst Blinfun_inverse)
  apply auto
  apply (rule bounded_linear_compose[where f = "\<lambda>v. Bfun (($) v)"])
  apply (intro bounded_linear_bfun_nth)
  apply simp
  apply (rule bounded_linear_compose[where g = "\<lambda>x. vec_lambda (apply_bfun x)"])
  apply auto
  apply (intro bounded_linear_intro[where K = "(card (UNIV :: 's set))"])
  apply auto
  apply (metis (no_types, lifting) plus_vec_def  vec_lambda_unique)
  using vec_lambda_unique apply force
  unfolding norm_vec_def norm_bfun_def dist_bfun_def
  apply auto
  unfolding L2_set_def
proof -
  fix x :: "'s \<Rightarrow>\<^sub>b real"
  have "sqrt (\<Sum> i \<in> UNIV . (apply_bfun x i)\<^sup>2) \<le> (\<Sum> i \<in> UNIV . \<bar>(apply_bfun x i)\<bar>)"
    using L2_set_le_sum_abs unfolding L2_set_def
    by auto
  also have "(\<Sum> i \<in> UNIV . \<bar>(apply_bfun x i)\<bar>) \<le> (card (UNIV :: 's set) * (\<Squnion>xa. \<bar>apply_bfun x xa\<bar>))"
    apply (intro sum_bounded_above)
    apply auto
    apply (intro cSup_upper)
    by auto
  finally show "sqrt (\<Sum>i\<in>UNIV. \<bar>apply_bfun x i\<bar>\<^sup>2) \<le> (\<Squnion>xa. \<bar>apply_bfun x xa\<bar>) * CARD('s)"
    apply auto
    by (simp add: mult.commute)
qed

end

definition "least_arg_max f P = (LEAST x. is_arg_max f P x)"

locale MDP_ord = MDP_finite_type A K r l
  for A and
    K :: "'s :: finite \<times> 'a :: {finite, wellorder} \<Rightarrow> 's pmf"
    and r l
begin

sublocale MDP_PI_finite A K r l "\<lambda>v s. least_arg_max (\<lambda>a. L\<^sub>a a v s) (\<lambda>a. a \<in> A s)"
  apply unfold_locales
  unfolding least_arg_max_def
  using Sup_att unfolding  max_L_ex_def has_arg_max_def
  by (auto intro: LeastI)

end
end
