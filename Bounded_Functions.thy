(* Author: Maximilian Schäffeler, adapted from HOL-Analysis.Bounded_Continuous_Function *)

section \<open>Bounded Functions\<close>

theory Bounded_Functions
  imports
    "HOL.Topological_Spaces"
    "HOL-Analysis.Uniform_Limit"
    "HOL-Probability.Probability"
begin

subsection \<open>Definition\<close>

definition\<^marker>\<open>tag important\<close> "bfun = {f. bounded (range f)}"

typedef (overloaded) ('a, 'b) bfun ("(_ \<Rightarrow>\<^sub>b _)" [22] 21) =
  "bfun::('a \<Rightarrow> 'b :: metric_space) set"
  morphisms apply_bfun Bfun
  unfolding bounded_def bfun_def
  by fastforce

declare [[coercion "apply_bfun :: ('a \<Rightarrow>\<^sub>b ('b :: metric_space)) \<Rightarrow> 'a \<Rightarrow> 'b"]]

setup_lifting type_definition_bfun

lemma bounded_apply_bfun[intro, simp]: "bounded (range (apply_bfun x))"
  using apply_bfun by (auto simp: bfun_def)

lemma bfun_eqI: "(\<And>x. apply_bfun f x = apply_bfun g x) \<Longrightarrow> f = g"
  by transfer auto

lemma bfunE:
  assumes "f \<in> bfun"
  obtains g where "f = apply_bfun g"
  by (blast intro: apply_bfun_cases assms)

lemma const_bfun: "(\<lambda>x. b) \<in> bfun"
  by (auto simp: bfun_def image_def)

lift_definition const_bfun::"'b \<Rightarrow> ('a \<Rightarrow>\<^sub>b ('b :: metric_space))" is "\<lambda>c _. c"
  by (rule const_bfun)

instantiation bfun :: (type, metric_space) metric_space
begin

lift_definition\<^marker>\<open>tag important\<close> dist_bfun :: "('a \<Rightarrow>\<^sub>b 'b) \<Rightarrow> ('a \<Rightarrow>\<^sub>b 'b) \<Rightarrow> real"
  is "\<lambda>f g. (SUP x. dist (f x) (g x))" .

definition uniformity_bfun :: "(('a \<Rightarrow>\<^sub>b 'b) \<times> 'a \<Rightarrow>\<^sub>b 'b) filter"
  where "uniformity_bfun = (INF e\<in>{0 <..}. principal {(x, y). dist x y < e})"

definition open_bfun :: "('a \<Rightarrow>\<^sub>b 'b) set \<Rightarrow> bool"
  where "open_bfun S = (\<forall>x\<in>S. \<forall>\<^sub>F (x', y) in uniformity. x' = x \<longrightarrow> y \<in> S)"

lemma bounded_dist_le_SUP_dist:
  "bounded (range f) \<Longrightarrow> bounded (range g) \<Longrightarrow> dist (f x) (g x) \<le> (SUP x. dist (f x) (g x))"
  by (auto intro!: cSUP_upper bounded_imp_bdd_above bounded_dist_comp)

lemma dist_bounded:
  fixes f g :: "'a \<Rightarrow>\<^sub>b 'b"
  shows "dist (f x) (g x) \<le> dist f g"
  by transfer (auto intro!: bounded_dist_le_SUP_dist simp: bfun_def)

lemma dist_bound:
  fixes f g :: "'a \<Rightarrow>\<^sub>b ('b :: metric_space)"
  assumes "\<And>x. dist (f x) (g x) \<le> b"
  shows "dist f g \<le> b"
  using assms
  by transfer (auto intro!: cSUP_least)

lemma dist_fun_lt_imp_dist_val_lt:
  fixes f g :: "'a \<Rightarrow>\<^sub>b 'b"
  assumes "dist f g < e"
  shows "dist (f x) (g x) < e"
  using dist_bounded assms by (rule le_less_trans)

instance
proof
  fix f g h :: "'a \<Rightarrow>\<^sub>b 'b"
  show "dist f g = 0 \<longleftrightarrow> f = g"
  proof
    have "\<And>x. dist (f x) (g x) \<le> dist f g"
      by (rule dist_bounded)
    also assume "dist f g = 0"
    finally show "f = g"
      by (auto simp: apply_bfun_inject[symmetric])
  qed (auto simp: dist_bfun_def intro!: cSup_eq)
  show "dist f g \<le> dist f h + dist g h"
  proof (rule dist_bound)
    fix x
    have "dist (f x) (g x) \<le> dist (f x) (h x) + dist (g x) (h x)"
      by (rule dist_triangle2)
    also have "dist (f x) (h x) \<le> dist f h"
      by (rule dist_bounded)
    also have "dist (g x) (h x) \<le> dist g h"
      by (rule dist_bounded)
    finally show "dist (f x) (g x) \<le> dist f h + dist g h"
      by simp
  qed
qed (rule open_bfun_def uniformity_bfun_def)+

end

lift_definition PiC::"'a set \<Rightarrow> ('a \<Rightarrow> ('b :: metric_space) set) \<Rightarrow> ('a \<Rightarrow>\<^sub>b 'b) set"
  is "\<lambda>I X. Pi I X \<inter> bfun"
  by auto

lemma mem_PiC_iff: "x \<in> PiC I X \<longleftrightarrow> apply_bfun x \<in> Pi I X"
  by transfer simp

lemmas mem_PiCD = mem_PiC_iff[THEN iffD1]
  and mem_PiCI = mem_PiC_iff[THEN iffD2]

lemma tendsto_bfun_uniform_limit:
  fixes f::"'i \<Rightarrow> 'a \<Rightarrow>\<^sub>b ('b :: metric_space)"
  assumes "(f \<longlongrightarrow> l) F"
  shows "uniform_limit UNIV f l F"
proof (rule uniform_limitI)
  fix e::real assume "e > 0"
  from tendstoD[OF assms this] have "\<forall>\<^sub>F x in F. dist (f x) l < e" .
  then show "\<forall>\<^sub>F n in F. \<forall>x\<in>UNIV. dist ((f n) x) (l x) < e"
    by eventually_elim (auto simp: dist_fun_lt_imp_dist_val_lt)
qed

lemma uniform_limit_tendsto_bfun:
  fixes f::"'i \<Rightarrow> 'a \<Rightarrow>\<^sub>b ('b :: metric_space)"
    and l::"'a \<Rightarrow>\<^sub>b 'b"
  assumes "uniform_limit UNIV f l F"
  shows "(f \<longlongrightarrow> l) F"
proof (rule tendstoI)
  fix e::real assume "e > 0"
  then have "e / 2 > 0" by simp
  from uniform_limitD[OF assms this]
  have "\<forall>\<^sub>F i in F. \<forall>x. dist (f i x) (l x) < e / 2" by simp
  then have "\<forall>\<^sub>F x in F. dist (f x) l \<le> e / 2"
    by eventually_elim (blast intro: dist_bound less_imp_le)
  then show "\<forall>\<^sub>F x in F. dist (f x) l < e"
    by eventually_elim (use \<open>0 < e\<close> in auto)
qed

subsection\<^marker>\<open>tag unimportant\<close> \<open>Supremum norm for a normed vector space\<close>

instantiation\<^marker>\<open>tag unimportant\<close> bfun :: (type, real_normed_vector) real_vector
begin

lemma uminus_cont: "f \<in> bfun \<Longrightarrow> (\<lambda>x. - f x) \<in> bfun" for f::"'a \<Rightarrow> 'b"
  by (auto simp: bfun_def)

lemma plus_cont: "f \<in> bfun \<Longrightarrow> g \<in> bfun \<Longrightarrow> (\<lambda>x. f x + g x) \<in> bfun" for f g::"'a \<Rightarrow> 'b"
  by (auto simp: bfun_def bounded_plus_comp)

lemma minus_cont: "f \<in> bfun \<Longrightarrow> g \<in> bfun \<Longrightarrow> (\<lambda>x. f x - g x) \<in> bfun" for f g::"'a \<Rightarrow> 'b"
  by (auto simp: bfun_def bounded_minus_comp)

lemma scaleR_cont: "f \<in> bfun \<Longrightarrow> (\<lambda>x. a *\<^sub>R f x) \<in> bfun" for f :: "'a \<Rightarrow> 'b"
  by (auto simp: bfun_def bounded_scaleR_comp)


lemma bfun_normI: "continuous_on UNIV f \<Longrightarrow> (\<And>x. norm (f x) \<le> b) \<Longrightarrow> f \<in> bfun"
  by (auto simp: bfun_def intro: boundedI)

lift_definition uminus_bfun::"('a \<Rightarrow>\<^sub>b 'b) \<Rightarrow> ('a \<Rightarrow>\<^sub>b 'b)" is "\<lambda>f x. - f x"
  by (rule uminus_cont)

lift_definition plus_bfun::"('a \<Rightarrow>\<^sub>b 'b) \<Rightarrow> ('a \<Rightarrow>\<^sub>b 'b) \<Rightarrow> 'a \<Rightarrow>\<^sub>b 'b"  is "\<lambda>f g x. f x + g x"
  by (rule plus_cont)

lift_definition minus_bfun::"('a \<Rightarrow>\<^sub>b 'b) \<Rightarrow> ('a \<Rightarrow>\<^sub>b 'b) \<Rightarrow> 'a \<Rightarrow>\<^sub>b 'b"  is "\<lambda>f g x. f x - g x"
  by (rule minus_cont)

lift_definition zero_bfun::"'a \<Rightarrow>\<^sub>b 'b" is "\<lambda>_. 0"
  by (rule const_bfun)

lemma const_bfun_0_eq_0[simp]: "const_bfun 0 = 0"
  by transfer simp

lift_definition scaleR_bfun::"real \<Rightarrow> ('a \<Rightarrow>\<^sub>b 'b) \<Rightarrow> 'a \<Rightarrow>\<^sub>b 'b"  is "\<lambda>r g x. r *\<^sub>R g x"
  by (rule scaleR_cont)

lemmas [simp] =
  const_bfun.rep_eq
  uminus_bfun.rep_eq
  plus_bfun.rep_eq
  minus_bfun.rep_eq
  zero_bfun.rep_eq
  scaleR_bfun.rep_eq

instance
  by standard (auto intro!: bfun_eqI simp: algebra_simps)
end

lemma scaleR_cont': "f \<in> bfun \<Longrightarrow> (\<lambda>x. a * f x) \<in> bfun" for f :: "'a \<Rightarrow> real"
  using scaleR_cont[of f a] by auto

lemma bfun_norm_le_SUP_norm:
  "f \<in> bfun \<Longrightarrow> norm (f x) \<le> (SUP x. norm (f x))"
  by (auto intro!: cSUP_upper bounded_imp_bdd_above simp: bfun_def bounded_norm_comp)


instantiation\<^marker>\<open>tag unimportant\<close> bfun :: (type, real_normed_vector) real_normed_vector
begin


definition norm_bfun :: "('a, 'b) bfun \<Rightarrow> real"
  where "norm_bfun f = dist f 0"

definition "sgn (f::('a,'b) bfun) = f /\<^sub>R norm f"

instance
proof
  fix a :: real
  fix f g :: "('a, 'b) bfun"
  show "dist f g = norm (f - g)"
    unfolding norm_bfun_def
    by transfer (simp add: dist_norm)
  show "norm (f + g) \<le> norm f + norm g"
    unfolding norm_bfun_def
    by transfer
      (auto intro!: cSUP_least norm_triangle_le add_mono bfun_norm_le_SUP_norm simp: dist_norm)
  show "norm (a *\<^sub>R f) = \<bar>a\<bar> * norm f"
    unfolding norm_bfun_def
    apply transfer
    by (rule trans[OF _ continuous_at_Sup_mono[symmetric]])
      (auto intro!: monoI mult_left_mono continuous_intros bounded_imp_bdd_above
        simp: bounded_norm_comp bfun_def image_comp)
qed (auto simp: norm_bfun_def sgn_bfun_def)
end

lemma norm_bfun_def': "norm f = (\<Squnion>x. norm ((f :: 'a \<Rightarrow>\<^sub>b 'b :: real_normed_vector) x))"
  by (metis (no_types, lifting) Inf.INF_cong dist_bfun.rep_eq norm_conv_dist zero_bfun.rep_eq)


lemma norm_le_norm_bfun: "norm (apply_bfun f x) \<le> norm f"
  unfolding norm_bfun_def dist_bfun_def
  by (simp add: apply_bfun bfun_norm_le_SUP_norm)

lemma abs_le_norm_bfun: "abs (apply_bfun f x) \<le> norm f"
  using norm_le_norm_bfun real_norm_def
  by metis

lemma le_norm_bfun: "(apply_bfun f x) \<le> norm f"
  by (metis norm_le_norm_bfun abs_of_nonneg le_cases norm_ge_zero order_trans real_norm_def)

subsection \<open>Complete Space\<close>

lemma tendsto_add: "P \<longlonglongrightarrow> (L :: 'a :: real_normed_vector) \<Longrightarrow> (\<lambda>n. P n + c) \<longlonglongrightarrow> L + c"
proof (subst tendsto_dist_iff)
  fix P :: "nat \<Rightarrow> 'a" fix L c
  assume "P \<longlonglongrightarrow> L"
  have aux: "(\<lambda>n. dist (P n) L) \<longlonglongrightarrow> 0"
    using \<open>P \<longlonglongrightarrow> L\<close> tendsto_dist_iff by auto
  show "(\<lambda>x. dist (P x + c) (L + c)) \<longlonglongrightarrow> 0"
    apply (subst tendsto_0_le[OF aux, where ?K = 1])
    by auto
qed

lemma lim_add: "convergent P \<Longrightarrow> lim (\<lambda>n. P n + (c :: 'a ::real_normed_vector)) = lim P + c"
  apply (simp add:  convergent_LIMSEQ_iff)
  using Bounded_Functions.tendsto_add limI by blast

thm tendsto_eq_intros tendsto_intros

lemma complete_bfun: 
  "Cauchy (X :: nat \<Rightarrow> ('a,  'b :: {complete_space, real_normed_vector}) bfun) \<Longrightarrow> convergent X"
proof -
  fix f :: "nat \<Rightarrow> ('a,  'b) bfun"
  assume cauchy_f: "Cauchy f"
  let ?f = "\<lambda>x. lim (\<lambda>n. f n x)"

  have cauchy_fx: "\<forall>x. Cauchy (\<lambda>n. f n x)"
    by (meson cauchy_f Cauchy_def dist_fun_lt_imp_dist_val_lt)
  hence conv_fx: "\<forall>x. convergent (\<lambda>n. f n x)"
    using Cauchy_convergent by blast

  have lim_f_bfun: "?f \<in> bfun"
  proof -
    have "\<exists>b. \<forall>x. norm (lim (\<lambda>n. f n x)) \<le> b"
    proof -
      obtain N b where dist_N: "\<forall>x. \<forall>n \<ge> N. \<forall>m \<ge> N. dist (f n x) (f m x) < b"
        by (metis Cauchy_iff cauchy_f dist_fun_lt_imp_dist_val_lt dist_norm zero_less_numeral)
      then have "\<And>x. norm (lim (\<lambda>n. f n x)) \<le> b + norm (f N x)"
      proof
        fix x
        have "(\<lambda>n. f n x) \<longlonglongrightarrow> ?f x"
          using conv_fx convergent_LIMSEQ_iff by blast
        hence tendsto_f_N: "(\<lambda>n. f (n + N) x) \<longlonglongrightarrow> ?f x"
          using LIMSEQ_ignore_initial_segment
          by auto
        hence tendsto_f_dist: "(\<lambda>n. dist (f (n + N) x) (f N x)) \<longlonglongrightarrow> dist (?f x) (f N x)"
          by (auto intro: tendsto_dist)
        have "\<forall>n. dist (f (n + N) x) (f N x) \<le> b"
          by (auto intro!: less_imp_le simp: dist_N)
        hence "dist (?f x) (f N x) \<le> b"
          by (metis (no_types, lifting) tendsto_f_dist convergentI limI lim_le)
        thus "norm (?f x) \<le> b + norm (f N x)"
          by (metis (full_types) diff_le_eq dist_norm norm_triangle_ineq2 order_trans)
      qed
      thus ?thesis
        by (meson add_le_cancel_left norm_le_norm_bfun order_trans)
    qed
    thus ?thesis
      by (auto intro: boundedI simp: bfun_def)
  qed

  hence bfun_lim_f_inv: "apply_bfun (Bfun ?f) = ?f"
    using bfun.Bfun_inverse by blast

  have "f \<longlonglongrightarrow> Bfun ?f"
  proof -
    have "\<And>e. e > 0 \<Longrightarrow> \<exists>N. \<forall>n \<ge> N. dist (Bfun ?f) (f n) < e"
    proof -
      fix e :: real
      assume "e > 0"
      then obtain N where dist_N: "\<forall>n \<ge> N. \<forall>m \<ge> N. dist (f n) (f m) < 0.5 * e"
        by (meson Cauchy_def cauchy_f divide_pos_pos zero_less_mult_iff zero_less_numeral)

      have "\<forall>n x. dist (?f x) (f (n + N) x) \<le> 0.5 * e"
      proof safe
        fix n x
        have "(\<lambda>m. f m x) \<longlonglongrightarrow> ?f x"
          using conv_fx convergent_LIMSEQ_iff by blast
        hence tendsto_f_N: "(\<lambda>m. f (m + N) x) \<longlonglongrightarrow> ?f x"
          using LIMSEQ_ignore_initial_segment
          by auto
        hence tendsto_f_dist: 
          "(\<lambda>m. dist (f (m + N) x) (f (n + N) x)) \<longlonglongrightarrow> dist (?f x) (f (n + N) x)"
          by (simp add: tendsto_dist)
        have "\<forall>m. dist (f (m + N) x) (f (n + N) x) \<le> 0.5 * e"
          by (meson dist_N dist_fun_lt_imp_dist_val_lt le_add2 less_imp_le)
        thus "dist (?f x) (f (n + N) x) \<le> 0.5 * e"
          by (metis (no_types, lifting) tendsto_f_dist convergentI limI lim_le)
      qed

      hence "\<forall>n. (SUP x. dist (?f x) (f (n + N) x)) \<le> 0.5 * e"
        by (fastforce intro!: cSUP_least)
      hence aux: "\<forall>n. dist (Bfun ?f) (f (n + N)) \<le> 0.5 * e"
        unfolding dist_bfun_def
        by (simp add: bfun_lim_f_inv)
      have "0.5 * e < e"  by (simp add: \<open>0 < e\<close>)
      hence "\<forall>n. dist (Bfun ?f) (f (n + N)) < e"
        using aux le_less_trans by blast
      thus "\<exists>N. \<forall>n\<ge>N. dist (Bfun ?f) (f n) < e"
        by (metis add.commute less_eqE)
    qed
    thus ?thesis
      by (simp add: dist_commute metric_LIMSEQ_I)
  qed
  thus "convergent f"
    unfolding convergent_def by blast
qed

lemma norm_bounded:
  fixes f :: "('a, 'b::real_normed_vector) bfun"
  shows "norm (apply_bfun f x) \<le> norm f"
  using dist_bounded[of f x 0]
  by (simp add: dist_norm)

lemma norm_bound:
  fixes f :: "('a, 'b::real_normed_vector) bfun"
  assumes "\<And>x. norm (apply_bfun f x) \<le> b"
  shows "norm f \<le> b"
  using dist_bound[of f 0 b] assms
  by (simp add: dist_norm)

lemma bfun_bounded_norm_range: "bounded (range (\<lambda>s. norm (apply_bfun v s)))"
proof -
  obtain b where "\<forall>s. norm (v s) \<le> b"
    by (meson norm_bounded)
  thus ?thesis
    by (simp add: bounded_norm_comp)
qed

instance bfun :: (type, banach) banach
  apply standard
  using complete_bfun by blast

lemma norm_le_imp_bfun[intro]: "(\<forall>x. norm (f x) \<le> b) \<Longrightarrow> f \<in> bfun"
  unfolding bfun_def
  apply auto
  by (metis bounded_iff rangeE)

lemma bfun_prob_space_integrable: 
  assumes "prob_space S" "v \<in> borel_measurable S" 
  shows "(v :: 'a \<Rightarrow> 'b :: {second_countable_topology, banach}) \<in> bfun \<Longrightarrow> integrable S v"
  apply (intro finite_measure.integrable_const_bound[where B = "norm (Bfun v)"])
  using prob_space.finite_measure assms apply blast
  by (metis (lifting) assms Bounded_Functions.norm_bounded apply_bfun_inverse bfunE eventuallyI)+

lemma bfun_integral_bound: "(v :: 'a \<Rightarrow> 'c :: {euclidean_space}) \<in> bfun \<Longrightarrow>
      (\<lambda>S. \<integral>x. v x \<partial>(S :: 'a pmf)) \<in> bfun"
proof -
  assume "v \<in> bfun"
  then obtain b where bH: "\<forall>x. norm (v x) \<le> b"
    using bfun_norm_le_SUP_norm by fast
  
  have "\<forall>S :: 'a pmf. (\<integral>x. norm (v x) \<partial>S) \<le> b"
    apply (subst prob_space.integral_le_const[OF _ bfun_prob_space_integrable])
    using \<open>v \<in> bfun\<close> bfun_def bounded_norm_comp bfun_def bH
    by (auto intro!: prob_space.integral_le_const prob_space_measure_pmf simp add: bfun_def)
  hence "\<forall>S :: 'a pmf. norm (\<integral>x. (v x) \<partial>S) \<le> b"
    using integral_norm_bound order_trans by blast
  thus ?thesis unfolding bfun_def by (auto intro: boundedI)
qed

lemma scale_bfun[intro!]: "f \<in> bfun \<Longrightarrow> (\<lambda>x. (k::real) * f x) \<in> bfun"
  using scaleR_cont[of f k] by auto


lemma bfun_spec[intro]: "f \<in> bfun \<Longrightarrow> (\<lambda>x. f (g x)) \<in> bfun"
  unfolding bfun_def bounded_def by auto

lemma apply_bfun_bfun[simp]: "apply_bfun f \<in> bfun"
  using apply_bfun .

lemma bfun_integral_bound'[intro]: "(v :: 'a \<Rightarrow> 'c :: {euclidean_space}) \<in> bfun \<Longrightarrow>
      (\<lambda>S. \<integral>x. v x \<partial>((F S) :: 'a pmf)) \<in> bfun"
  apply (subst bfun_spec[of _ F])
  using bfun_integral_bound
  by auto


lift_definition bfun_comp :: "('a \<Rightarrow> 'b) \<Rightarrow> ('b \<Rightarrow>\<^sub>b 'c::metric_space) \<Rightarrow> ('a \<Rightarrow>\<^sub>b 'c)" is
"\<lambda>g bf x. bf (g x)"
  by auto
end
