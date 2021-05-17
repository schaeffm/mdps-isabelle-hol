(* Author: Maximilian Schäffeler *)

theory Util imports
  "HOL-Library.Omega_Words_Fun" Bounded_Functions
begin

lemma bounded_range_iff: "bounded (range v) \<longleftrightarrow> (\<exists>b. \<forall>x. norm (v x) \<le> b)"
  unfolding bounded_iff
  by auto

(* counterpart to nn_integral_stream_space *)
lemma (in prob_space) integral_stream_space:
  fixes f :: "'a stream \<Rightarrow> ('b :: {banach, second_countable_topology,real_normed_vector})"
  assumes int_f: "integrable (stream_space M) f"
  assumes [measurable]: "f \<in> borel_measurable (stream_space M)"
  shows "(\<integral>X. f X \<partial>stream_space M) = (\<integral>x. (\<integral>X. f (x ## X) \<partial>stream_space M) \<partial>M)"
proof -
  interpret S: sequence_space M ..
  interpret P: pair_sigma_finite M "\<Pi>\<^sub>M i::nat\<in>UNIV. M" ..

  interpret P': pair_sigma_finite "\<Pi>\<^sub>M i::nat\<in>UNIV. M" M ..

  obtain i where "has_bochner_integral (stream_space M) f i"
    using int_f
    using integrable.cases by blast
  have "integrable S.S (\<lambda>X. f (to_stream X))"
    using int_f
    by (metis integrable_distr measurable_to_stream stream_space_eq_distr)
  hence aux: "integrable (distr (M \<Otimes>\<^sub>M Pi\<^sub>M UNIV (\<lambda>i. M)) (Pi\<^sub>M UNIV (\<lambda>i. M)) 
    (\<lambda>(x, y). case_nat x y)) (\<lambda>X. f (to_stream X))"
    by (auto simp: S.PiM_iter)
  hence "integrable (distr (M \<Otimes>\<^sub>M Pi\<^sub>M UNIV (\<lambda>i. M)) (Pi\<^sub>M UNIV (\<lambda>i. M)) (\<lambda>(x, y). case_nat x y)) 
    (\<lambda>X. f (to_stream X)) \<longleftrightarrow> 
    integrable (M \<Otimes>\<^sub>M S.S) (\<lambda>X. f (to_stream ((\<lambda>(s, \<omega>). case_nat s \<omega>) X)))"
    by (auto simp: integrable_distr_eq)
  hence "integrable (M \<Otimes>\<^sub>M S.S) (\<lambda>X. f (to_stream ((\<lambda>(s, \<omega>). case_nat s \<omega>) X)))"
    using aux by auto
  hence aux': "integrable (M \<Otimes>\<^sub>M (Pi\<^sub>M UNIV (\<lambda>i. M))) 
    (\<lambda>X. f (to_stream ((\<lambda>(s, \<omega>). case_nat s \<omega>) X)))"
    by auto
  hence aux'': "integrable (M \<Otimes>\<^sub>M (Pi\<^sub>M UNIV (\<lambda>i. M))) 
    (\<lambda>X. f (to_stream ((\<lambda>(s, \<omega>). case_nat s \<omega>) X))) = 
      integrable (M \<Otimes>\<^sub>M Pi\<^sub>M UNIV (\<lambda>i. M)) (\<lambda>(x, X). f (to_stream (case_nat x X)))"
    by (fastforce intro!: integrable_cong)
  hence aux''': "integrable (M \<Otimes>\<^sub>M Pi\<^sub>M UNIV (\<lambda>i. M)) (\<lambda>(x, X). f (to_stream (case_nat x X)))"
    using aux' by auto

  have "(\<integral>X. f X \<partial>stream_space M) = (\<integral>X. f (to_stream X) \<partial>S.S)"
    apply (subst stream_space_eq_distr)
    by (simp add: integral_distr)
  also have "\<dots> = (\<integral>X. f (to_stream ((\<lambda>(s, \<omega>). case_nat s \<omega>) X)) \<partial>(M \<Otimes>\<^sub>M S.S))"
    apply (subst S.PiM_iter[symmetric])
    by (simp add: integral_distr)
  also have "\<dots> = (\<integral>x. \<integral>X. f (to_stream ((\<lambda>(s, \<omega>). case_nat s \<omega>) (x, X)))\<partial>S.S  \<partial>M)"
    using int_f
    apply (subst pair_sigma_finite.integral_fst)
    using aux''' case_prod_conv
      apply (auto simp add: P.pair_sigma_finite_axioms split: prod.split)
    by (metis (no_types, lifting) case_prod_conv old.prod.exhaust)
  also have "\<dots> = (\<integral>x. \<integral>X. f (x ## to_stream X) \<partial>S.S \<partial>M)"
    by (auto intro!: integral_cong simp: to_stream_nat_case)
  also have "\<dots> = (\<integral>x. \<integral>X. f (x ## X) \<partial>stream_space M \<partial>M)"
    apply (subst stream_space_eq_distr)
    apply (subst Bochner_Integration.integral_cong[where ?N = M])    
    by (auto simp: integral_distr)
  finally show ?thesis .
qed

lemma SUP_add_le: 
  assumes "X \<noteq> {}" "bounded (B ` X)" "bounded (A' ` X)" 
  shows "(\<Squnion>c \<in> X. (B :: 'a \<Rightarrow> real) c + A' c) \<le> (\<Squnion>b \<in> X. B b) + (\<Squnion>a \<in> X. A' a)"
  apply (intro cSUP_least)
  using assms by (auto simp: add_mono bounded_has_Sup(1))

lemma le_SUP_diff':
  assumes a1: "X \<noteq> {}" 
    and a2: "bounded (B ` X)" 
    and a3: "bounded (A' ` X)" 
    and a4: "(\<Squnion>a \<in> X. (A' :: 'a \<Rightarrow> real) a) \<le> (\<Squnion>b \<in> X. B b)"
  shows  "(\<Squnion>b \<in> X. B b) - (\<Squnion>a \<in> X. (A' :: 'a \<Rightarrow> real) a) \<le> (\<Squnion>c \<in> X. B c - A' c)"
proof -
  have "bounded ((\<lambda>x. (B x - A' x)) ` X)"
    using a2 a3 bounded_minus_comp by blast
  have "\<forall>e > 0. (\<Squnion>b \<in> X. B b) - (\<Squnion>a \<in> X. A' a) - e \<le> (\<Squnion>c \<in> X. B c - A' c)"
  proof safe
    fix e :: real
    assume "e > 0"
    then obtain z where "(\<Squnion>b \<in> X. B b) - e\<le> B z" "z \<in> X"
      apply (subst less_cSupE[where ?y = "\<Squnion> (B ` X) - e", where ?X = "B`X"]) apply auto
      using a1 apply blast
      by force
    hence " ((\<Squnion>a \<in> X. A' a) \<le> B z + e)"
      using a4
      by force
    hence "A' z \<le> B z + e"
      using \<open>z \<in> X\<close> a3 bounded_has_Sup(1) by fastforce
    hence "-e \<le> B z - A' z"
      by linarith
    thus "(\<Squnion>b \<in> X. B b) - (\<Squnion>a \<in> X. A' a) -e \<le> (\<Squnion>c \<in> X. B c - A' c)"
      apply (subst cSUP_upper2[where x = z])
         apply (auto simp: \<open>z\<in>X\<close>\<open>bounded ((\<lambda>x. B x - A' x) ` X)\<close> bounded_imp_bdd_above)
      using \<open>\<Squnion> (B ` X) - e \<le> B z\<close> \<open>z \<in> X\<close> a3 bounded_has_Sup(1) by fastforce
  qed
  thus ?thesis
    by (subst field_le_epsilon) auto
qed

lemma le_SUP_diff:
  assumes 
    a1: "X \<noteq> {}" and 
    a2: "bounded (B ` X)" and 
    a3: "bounded (A' ` X)" and 
    a4: "(\<Squnion>a \<in> X. (A' :: 'a \<Rightarrow> real) a) \<le> (\<Squnion>b \<in> X. B b)"
  shows  "0 \<le> (\<Squnion>c \<in> X. B c - A' c)"
proof -
  have "bounded ((\<lambda>x. (B x - A' x)) ` X)"
    using a2 a3 bounded_minus_comp by blast
  have "\<forall>e > 0. -e \<le> (\<Squnion>c \<in> X. B c - A' c)"
  proof safe
    fix e :: real
    assume "e > 0"
    hence "(\<Squnion>b \<in> X. B b) - e < (\<Squnion>b \<in> X. B b)"
      by linarith
    then obtain z where "(\<Squnion>b \<in> X. B b) - e\<le> B z" "z \<in> X"
      apply (subst less_cSupE[where ?y = "\<Squnion> (B ` X) - e", where ?X = "B`X"]) apply auto
      using a1 by fastforce+
    hence " ((\<Squnion>a \<in> X. A' a) \<le> B z + e)"
      using a4 by force
    hence "A' z \<le> B z + e"
      using \<open>z \<in> X\<close> a3 bounded_has_Sup(1) by fastforce
    hence "-e \<le> B z - A' z"
      by linarith
    thus "-e \<le> (\<Squnion>c \<in> X. B c - A' c)"
      apply (subst cSUP_upper2)
      by (auto simp: \<open>z\<in>X\<close>\<open>bounded ((\<lambda>x. B x - A' x) ` X)\<close> bounded_imp_bdd_above)
  qed
  thus ?thesis
    by (subst field_le_epsilon) auto
qed

lemma integrable_bfun_prob_space[simp]: 
  "integrable (measure_pmf P) (\<lambda>t. apply_bfun f (F t) :: real)"
proof -
  obtain b where "\<forall>t. \<bar>f (F t)\<bar> \<le> b"
    by (metis Bounded_Functions.norm_bounded real_norm_def)
  hence "(\<integral>\<^sup>+ x. ennreal \<bar>f (F x)\<bar> \<partial>measure_pmf P) < \<infinity>"
    apply (subst le_less_trans[where ?y = "\<integral>\<^sup>+ x. ennreal b \<partial>measure_pmf P"])
    using nn_integral_mono ennreal_leI apply metis
    by auto
  then show ?thesis
    by (simp add: integrable_iff_bounded)
qed

lemma bounded_SUP_mul[simp]: 
  "X \<noteq> {} \<Longrightarrow> 0 \<le> l \<Longrightarrow> bounded (f ` X) \<Longrightarrow> (\<Squnion>x \<in> X. (l :: real) * f x) = (l * (\<Squnion>x \<in> X. f x))" 
proof -
  assume "X \<noteq> {} "" bounded (f ` X)" "0 \<le> l"
  have "(\<Squnion>x \<in> X. ereal l * ereal (f x)) = (l * (\<Squnion>x \<in> X. ereal (f x)))"
    by (simp add: Sup_ereal_mult_left' \<open>0 \<le> l\<close> \<open>X \<noteq> {}\<close>)
  obtain b where "\<forall>a \<in>X. \<bar>f a\<bar> \<le> b"
    using \<open>bounded (f ` X)\<close> bounded_real by auto
  have "\<forall>a \<in>X. \<bar>ereal (f a)\<bar> \<le> b"
    by (simp add: \<open>\<forall>a\<in>X. \<bar>f a\<bar> \<le> b\<close>)
  hence sup_leb: "(\<Squnion>a\<in>X. \<bar>ereal (f a)\<bar>)\<le> b"
    by (simp add: SUP_least)
  have "(\<Squnion>a\<in>X. ereal (f a)) \<le> (\<Squnion>a\<in>X. \<bar>ereal (f a)\<bar>)"
    by (auto intro: Complete_Lattices.SUP_mono')
  moreover have "-(\<Squnion>a\<in>X. ereal (f a)) \<le> (\<Squnion>a\<in>X. \<bar>ereal (f a)\<bar>)"
    apply (subst ereal_INF_uminus_eq[symmetric])
    apply (subst Inf_less_eq)
    using \<open>X \<noteq> {}\<close> 
    by (auto simp: Inf_less_eq intro: cSUP_upper2)
  ultimately have "\<bar>(\<Squnion>a\<in>X. ereal (f a))\<bar> \<le> (\<Squnion>a\<in>X. \<bar>ereal (f a)\<bar>)"
    by (auto intro: ereal_abs_leI)
  hence "\<bar>\<Squnion>a\<in>X. ereal (f a)\<bar> \<le> b"
    using sup_leb by auto
  hence "\<bar>\<Squnion>a\<in>X. ereal (f a)\<bar> \<noteq> \<infinity>"
    by auto
  hence "(\<Squnion>x \<in> X. ereal (f x)) = ereal (\<Squnion>x \<in> X. (f x))"
    using ereal_SUP by metis
  hence "(\<Squnion>x \<in> X. ereal (l * f x)) = ereal (l * (\<Squnion>x \<in> X. f x))"
    using \<open>(\<Squnion>x\<in>X. ereal l * ereal (f x)) = ereal l * (\<Squnion>x\<in>X. ereal (f x))\<close> by auto
  hence "ereal (\<Squnion>x \<in> X. l * f x) = ereal (l * (\<Squnion>x \<in> X. f x))"
    by (simp add: ereal_SUP)
  thus ?thesis
    by auto
qed

lemma abs_cSUP_le[intro]: 
  "X \<noteq> {} \<Longrightarrow> bounded (F ` X) \<Longrightarrow> \<bar>\<Squnion>x \<in> X. (F x) :: real\<bar> \<le> (\<Squnion>x \<in> X. \<bar>F x\<bar>)"
  using bounded_imp_bdd_above
  apply (auto intro!: cSup_abs_le cSUP_upper2)
  by (metis bounded_norm_comp image_cong real_norm_def)

instantiation bfun :: (type, one) one begin

lift_definition one_bfun :: "'s \<Rightarrow>\<^sub>b real" is "\<lambda>x. 1"
  using const_bfun .

instance
  by standard
end

lemma bounded_integrable: 
  assumes "bounded (range v)" "v \<in> borel_measurable (measure_pmf p)" 
  shows "integrable (measure_pmf p) (v :: 'c \<Rightarrow> real)"
  using assms
  by (auto simp: bounded_iff AE_measure_pmf_iff intro!: measure_pmf.integrable_const_bound)

lemma bounded_apply_bfun: 
  assumes "bounded ((F :: 'c \<Rightarrow> 'd \<Rightarrow>\<^sub>b 'b::real_normed_vector) ` S)"
  shows "bounded ((\<lambda>b. apply_bfun (F b) x) ` S)"
proof -
  obtain b where "\<forall>x\<in>S. norm (F x) \<le> b"
    by (meson assms bounded_pos image_eqI)
  thus "bounded ((\<lambda>b. (F b) x) ` S)"
    by (fastforce intro: norm_le_norm_bfun dual_order.trans boundedI[of _ b])
qed

lemma bounded_apply_blinfun: 
  assumes "bounded ((F :: 'c \<Rightarrow> 'd::real_normed_vector \<Rightarrow>\<^sub>L 'b::real_normed_vector) ` S)"
  shows "bounded ((\<lambda>b. blinfun_apply (F b) x) ` S)"
proof -
  obtain b where "\<forall>x\<in>S. norm (F x) \<le> b"
    by (meson \<open>bounded (F ` S)\<close> bounded_pos image_eqI)
  thus "bounded ((\<lambda>b. (F b) x) ` S)"
    by (auto simp: mult_right_mono mult.commute[of _ b] 
        intro!: boundedI[of _ "norm x * b"] dual_order.trans[OF _ norm_blinfun])
qed

lemma prefix_cons: 
  "Omega_Words_Fun.prefix (Suc n) seq = seq 0#Omega_Words_Fun.prefix n (\<lambda>n. seq (Suc n))"
  by (metis map_upt_Suc subsequence_def)

lemma restrict_Suc: "restrict y {0..<Suc i} (Suc n) = (restrict (\<lambda>n. y (Suc n)) {0..<i}) n"
  by auto

lemma prefix_restrict: "Omega_Words_Fun.prefix i (restrict y {0..<i}) = Omega_Words_Fun.prefix i y"
  apply (induction i arbitrary: y)
   apply simp
  apply (simp only: restrict_Suc prefix_cons)
  by auto

lemma prefix_measurable[measurable]: 
  "Omega_Words_Fun.prefix i \<in> Pi\<^sub>M {0..<i} 
  (\<lambda>_. count_space (UNIV :: ('s ::countable \<times> 'a::countable) set)) \<rightarrow>\<^sub>M count_space UNIV"
proof (induction i)
  case 0
  then show ?case by simp
next
  case (Suc i)
  have aux: "(\<lambda>w. (restrict w {0..<i}, w i)) \<in> Pi\<^sub>M {0..<Suc i} (\<lambda>_. count_space UNIV) \<rightarrow>\<^sub>M 
    Pi\<^sub>M {0..<i} (\<lambda>_. count_space UNIV) \<Otimes>\<^sub>M (count_space UNIV)"
    by auto
  have aux': "(\<lambda>(w,wi). Omega_Words_Fun.prefix i (restrict w {0..<i})@[wi]) \<in> Pi\<^sub>M {0..<i} 
    (\<lambda>_. count_space (UNIV :: ('s \<times> 'a) set)) \<Otimes>\<^sub>M (count_space UNIV) \<rightarrow>\<^sub>M count_space UNIV"
    apply (subst measurable_pair_swap_iff)
    apply measurable
    by (auto intro: measurable_pair_measure_countable1 simp: Suc prefix_restrict)
  have f_eq: "\<And>w. Omega_Words_Fun.prefix i (restrict w {0..<i}) @ [w i] = 
    (\<lambda>(w,wi). Omega_Words_Fun.prefix i w @[wi]) ((restrict w {0..<i}), w i)"
    by auto
  show ?case
    apply simp
    apply (subst prefix_restrict[symmetric])
    apply (subst f_eq)
    apply (rule measurable_compose[where N= "Pi\<^sub>M {0..<i} _ \<Otimes>\<^sub>M _"])
    using aux aux'
    by (auto simp: prefix_restrict)
qed

declare one_bfun.rep_eq [simp]

lemma norm_bfun_one[simp]: "norm (1 :: 'a \<Rightarrow>\<^sub>b real) = 1"
  unfolding norm_bfun_def' by auto

lemma bfun_tendsto_apply_bfun:
  assumes h: "(F :: (nat \<Rightarrow> 'a \<Rightarrow>\<^sub>b real)) \<longlonglongrightarrow> (y :: 'a \<Rightarrow>\<^sub>b real)"
  shows "(\<lambda>n. F n x) \<longlonglongrightarrow> y x"
proof -
  have aux: "(\<lambda>n. dist (F n) y) \<longlonglongrightarrow> 0"
    using h
    using tendsto_dist_iff by blast
  have "\<And>n. dist (F n x) (y x) \<le> dist (F n) y"
    unfolding dist_bfun_def
    using Bounded_Continuous_Function.bounded_dist_le_SUP_dist by fastforce
  hence "\<And>n. norm (dist (F n x) (y x)) \<le> norm(dist (F n) y)"
    by auto
  hence "(\<lambda>n. dist (F n x) (y x)) \<longlonglongrightarrow> 0"
    apply (subst Lim_transform_bound[OF _ aux])
    by auto
  thus ?thesis  
    using tendsto_dist_iff by blast
qed

definition "is_contraction C \<equiv> \<exists>l. 0 \<le> l \<and> l < 1 \<and> (\<forall>v u. dist (C v) (C u) \<le> l * dist v u)"

lemma banach':
  fixes C :: "'b :: complete_space \<Rightarrow> 'b"
  assumes "is_contraction C"
  shows "\<exists>!v. C v = v" "\<And>v. (\<lambda>n. (C ^^ n) v) \<longlonglongrightarrow> (THE v. C v = v)"
  using assms
  unfolding is_contraction_def
  using banach_fix_type apply blast
proof -
  obtain v where "C v = v" "\<forall>v'. C v' = v' \<longrightarrow> v' = v" 
    by (metis assms is_contraction_def banach_fix_type)
  obtain l where "(\<forall>v u. dist (C v) (C u) \<le> l * dist v u)" "0 \<le> l" "l < 1"
    using assms is_contraction_def by blast
  have "\<And>n v0. dist ((C ^^ n) v0) v \<le> l ^ n * dist v0 v"
  proof -
    fix n v0
    show "dist ((C ^^ n) v0) v \<le> l ^ n * dist v0 v"
    proof (induction n)
      case 0
      then show ?case by simp
    next
      case (Suc n)
      fix n
      assume a1: "dist ((C ^^ n) v0) v \<le> l ^ n * dist v0 v"
      have "\<forall>r f ra rb. (r::real) \<le> f (rb::real) \<or> (\<exists>r ra. \<not> f r \<le> f ra \<and> r \<le> ra) \<or> \<not> ra \<le> rb \<or> 
        \<not> r \<le> f ra"
        using order_subst1 by fastforce
      then have "dist (C ((C ^^ n) v0)) v \<le> l * (l ^ n * dist v0 v)"
        using a1 by (metis \<open>0 \<le> l\<close> \<open>C v = v\<close> \<open>\<forall>v u. dist (C v) (C u) \<le> l * dist v u\<close> 
            ordered_comm_semiring_class.comm_mult_left_mono)
      then show "dist ((C ^^ Suc n) v0) v \<le> l ^ Suc n * dist v0 v"
        by simp
    qed
  qed
  have "(\<lambda>n. l ^ n) \<longlonglongrightarrow> 0"
    by (simp add: LIMSEQ_realpow_zero \<open>0 \<le> l\<close> \<open>l < 1\<close>)
  hence k:  "\<And>v0. (\<lambda>n. l ^ n * dist v0 v) \<longlonglongrightarrow> 0"
    by (simp add: tendsto_mult_left_zero)
  have "\<And>v0. (\<lambda>n. dist ((C ^^ n) v0) v) \<longlonglongrightarrow> 0"
  proof -
    fix v0
    show "(\<lambda>n. dist ((C ^^ n) v0) v) \<longlonglongrightarrow> 0"
      apply (subst Limits.tendsto_0_le[where ?K = 1, where ?f = "(\<lambda>n. l ^ n * dist v0 v)"])
      using k \<open>\<And>n. dist ((C ^^ n) v0) v \<le> l ^ n * dist v0 v\<close> order_trans abs_ge_self
      by (fastforce intro!: eventuallyI)+
  qed
  hence "\<And>v0. (\<lambda>n. (C ^^ n) v0) \<longlonglongrightarrow> v"
    using tendsto_dist_iff by blast
  thus "\<And>v0. (\<lambda>n. (C ^^ n) v0) \<longlonglongrightarrow> (THE v. C v = v)" 
    by (metis (mono_tags, lifting) \<open>C v = v\<close> \<open>\<forall>v'. C v' = v' \<longrightarrow> v' = v\<close> theI')
qed


lemma banach_seq:
  fixes C :: "'b \<Rightarrow> 'b :: {metric_space, banach}"
  assumes "uniform_space_class.complete S" "S \<noteq> {}" 
  assumes "0 \<le> l" "l < 1" "C ` S \<subseteq> S"
  assumes "\<forall>x\<in>S. \<forall>y\<in>S. dist (C x) (C y) \<le> l * dist x y"
  assumes v0: "v0 \<in> S"
  shows "(\<lambda>n. (C ^^ n) v0) \<longlonglongrightarrow> (THE v. v \<in> S \<and> C v = v)"
  using assms
proof -
  obtain v where "v \<in> S" "C v = v" "\<forall>v' \<in> S. C v' = v' \<longrightarrow> v' = v"
    using banach_fix[OF assms(1-6)] by meson
  have "\<And>n v0. v0 \<in> S \<Longrightarrow> dist ((C ^^ n) v0) v \<le> l ^ n * dist v0 v"
  proof -
    fix n v0
    assume "v0 \<in> S"
    then show "dist ((C ^^ n) v0) v \<le> l ^ n * dist v0 v"
    proof (induction n)
      case 0
      then show ?case by simp
    next
      case (Suc n)
      have "(C ^^ n) ` S \<subseteq> S"
        apply (induction n arbitrary: v0) using Suc assms
         apply simp using assms(5)
        by (simp add: image_subset_iff)
      then have "dist (C ((C ^^ n) v0)) v \<le> l * (l ^ n * dist v0 v)"
        apply (auto simp: image_subset_iff )
        apply (subst \<open>C v = v\<close>[symmetric])
        using Suc.IH[OF Suc.prems] assms(3) assms(6) 
        by (meson Suc.prems \<open>v \<in> S\<close> mult_left_mono order_trans)
      thus ?case
        by auto
    qed
  qed
  have "(\<lambda>n. l ^ n) \<longlonglongrightarrow> 0"
    by (simp add: LIMSEQ_realpow_zero \<open>0 \<le> l\<close> \<open>l < 1\<close>)
  hence k:  "\<And>v0. (\<lambda>n. l ^ n * dist v0 v) \<longlonglongrightarrow> 0"
    by (simp add: tendsto_mult_left_zero)
  have "\<And>v0. v0 \<in> S \<Longrightarrow> (\<lambda>n. dist ((C ^^ n) v0) v) \<longlonglongrightarrow> 0"
  proof -
    fix v0 assume "v0 \<in> S"
    show "(\<lambda>n. dist ((C ^^ n) v0) v) \<longlonglongrightarrow> 0"
      apply (subst Limits.tendsto_0_le[where ?K = 1, where ?f = "(\<lambda>n. l ^ n * dist v0 v)"])
      using \<open>(\<lambda>n. l ^ n) \<longlonglongrightarrow> 0\<close> tendsto_mult_right apply fastforce
       apply auto
      apply eventually_elim
      by (simp add: \<open>\<And>v0 n. v0 \<in> S \<Longrightarrow> dist ((C ^^ n) v0) v \<le> l ^ n * dist v0 v\<close> \<open>v0 \<in> S\<close> assms(3))
  qed
  hence "(\<lambda>n. (C ^^ n) v0) \<longlonglongrightarrow> v"
    using tendsto_dist_iff v0 by blast
  thus "(\<lambda>n. (C ^^ n) v0) \<longlonglongrightarrow> (THE v. v \<in> S \<and> C v = v)"
    by (metis (mono_tags, lifting) \<open>C v = v\<close> 
        \<open>\<And>thesis. (\<And>v. \<lbrakk>v \<in> S; C v = v; \<forall>v'\<in>S. C v' = v' \<longrightarrow> v' = v\<rbrakk> \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> 
        \<open>v \<in> S\<close> the_equality)
qed


lemma eq_onpI: "P x \<Longrightarrow> eq_onp P x x"
by(simp add: eq_onp_def)
end