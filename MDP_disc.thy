(* Author: Maximilian Schäffeler *)

theory MDP_disc
  imports Util MDP_cont "HOL-Library.Omega_Words_Fun"
begin
no_notation Omega_Words_Fun.build (infixr  \<open>##\<close> 65)

section \<open>Markov Decision Processes\<close>
locale discrete_MDP =
  fixes A :: "'s::countable \<Rightarrow> 'a::countable set" \<comment> \<open>enabled actions\<close>
    and K :: "'s \<times> 'a \<Rightarrow> 's pmf" \<comment> \<open>MDP kernel, transition probabilities\<close>
  assumes
    A_ne: "\<And>s. A s \<noteq> {}" \<comment> \<open>set of enabled actions is nonempty\<close>
begin

subsection \<open>Policies\<close>
text \<open>Type synonym for decision rules.\<close>
type_synonym ('c, 'd) dec = "'c \<Rightarrow> 'd pmf"

definition is_dec :: "('s, 'a) dec \<Rightarrow> bool" where
  "is_dec d \<equiv> \<forall>s. d s \<subseteq> A s"

abbreviation "D\<^sub>R \<equiv> {d. is_dec d}"

definition is_dec_det :: "('s \<Rightarrow> 'a) \<Rightarrow> bool" where
  "is_dec_det d \<equiv> \<forall>s. d s \<in> A s"

abbreviation "D\<^sub>D \<equiv> {d. is_dec_det d}"

definition "mk_dec_det d s = return_pmf (d s)"

lemma is_dec_mk_dec_det_iff [simp]: "is_dec (mk_dec_det d) \<longleftrightarrow> is_dec_det d"
  by (simp add: is_dec_def is_dec_det_def mk_dec_det_def)

lemma D_det_to_MR[intro]: "is_dec_det d \<Longrightarrow> is_dec (mk_dec_det d)"
  by simp

text \<open>
Due to the assumption @{thm A_ne}, a deterministic decision rule always exists.
It immediately follows via @{thm is_dec_mk_dec_det_iff} that a randomized decision rule also exists.
\<close>

lemma SOME_is_dec_det: "is_dec_det (\<lambda>s. SOME a. a \<in> A s)"
  using A_ne by (simp add: is_dec_det_def some_in_eq)

lemma ex_dec_det [simp]: "\<exists>d. is_dec_det d"
  using SOME_is_dec_det by blast

lemma D_det_ne [simp]: "D\<^sub>D \<noteq> {}"
  by simp

lemma D\<^sub>R_ne [simp]: "D\<^sub>R \<noteq> {}"
  using D_det_ne D_det_to_MR by blast

lemma ex_dec[intro, simp]: "\<exists>d. is_dec d"
  using ex_dec_det by blast

text \<open>Type synonym for policies.\<close>
type_synonym ('c, 'd) pol = "('c \<times> 'd) list \<Rightarrow> ('c, 'd) dec"


text \<open>A policy assigns a decision rule to each observed past.\<close>
definition is_policy :: "('s, 'a) pol \<Rightarrow> bool" where
  "is_policy p \<equiv> \<forall>hs. is_dec (p hs)"

abbreviation "\<Pi>\<^sub>H\<^sub>R \<equiv> {p. is_policy p}"

text \<open>Deterministic policies\<close>
definition "is_deterministic p \<equiv> is_policy p \<and> (\<forall>h s. \<exists>a. p h s = return_pmf a)"

definition "mk_det p h s \<equiv> return_pmf (p h s)"

abbreviation "\<Pi>\<^sub>H\<^sub>D \<equiv> {p. \<forall>h. p h \<in> D\<^sub>D}"

text \<open>Markovian policies\<close>
definition "is_markovian p \<equiv> is_policy p \<and> (\<forall>h h'. length h = length h' \<longrightarrow> p h = p h')"

definition mk_markovian :: "(nat \<Rightarrow> ('s, 'a) dec) \<Rightarrow> ('s, 'a) pol" where
  "mk_markovian p \<equiv> (\<lambda>h. p (length h))"

lemma is_markovian_mk_iff[simp]: "is_markovian (mk_markovian p) \<longleftrightarrow> (\<forall>n. is_dec (p n))"
  unfolding is_markovian_def mk_markovian_def is_policy_def
  by (metis (mono_tags, hide_lams) Ex_list_of_length)

lemma is_markovian_mk[intro]: "\<forall>n. is_dec (p n) \<Longrightarrow> is_markovian (mk_markovian p)"
  unfolding is_markovian_def mk_markovian_def is_policy_def
  by auto

lemma mk_markovian_nil [simp]: "mk_markovian p [] = p 0"
  unfolding mk_markovian_def by auto

definition "mk_markovian_det p \<equiv> (\<lambda>h s. return_pmf (p (length h) s))"

abbreviation "\<Pi>\<^sub>M\<^sub>D \<equiv> {p. \<forall>n. p n \<in> D\<^sub>D}"
abbreviation "\<Pi>\<^sub>M\<^sub>R \<equiv> {p. \<forall>n. p n \<in> D\<^sub>R}"

lemma \<Pi>\<^sub>M\<^sub>R_imp_policies[intro]: "p \<in> \<Pi>\<^sub>M\<^sub>R \<Longrightarrow> mk_markovian p \<in> \<Pi>\<^sub>H\<^sub>R"
  unfolding is_policy_def mk_markovian_def by auto

lemma \<Pi>\<^sub>M\<^sub>D_MR_iff[simp]: "(\<lambda>n. mk_dec_det (p n)) \<in> \<Pi>\<^sub>M\<^sub>R \<longleftrightarrow> p \<in> \<Pi>\<^sub>M\<^sub>D"
  by auto

lemma \<Pi>\<^sub>M\<^sub>D_to_MR[intro]: "p \<in> \<Pi>\<^sub>M\<^sub>D \<Longrightarrow> (\<lambda>n. mk_dec_det (p n)) \<in> \<Pi>\<^sub>M\<^sub>R"
  by simp

lemma \<Pi>\<^sub>M\<^sub>D_ne[simp]: "\<Pi>\<^sub>M\<^sub>D \<noteq> {}"
  by (auto simp: someI_ex[OF ex_dec_det] intro: exI[of _ "\<lambda>n. (SOME d. is_dec_det d)"])

lemma \<Pi>\<^sub>M\<^sub>R_ne[simp]: "\<Pi>\<^sub>M\<^sub>R \<noteq> {}"
  using \<Pi>\<^sub>M\<^sub>D_ne by fast

lemma policies_ne[simp, intro]: "\<Pi>\<^sub>H\<^sub>R \<noteq> {}"
  using \<Pi>\<^sub>M\<^sub>R_ne is_policy_def by auto


text \<open>Stationary policies\<close>
definition "is_stationary p \<equiv> is_policy p \<and> (\<forall>h h'. p h = p h')"

lemma is_stationary_const_iff[simp]: "is_stationary (\<lambda>_. d) = is_dec d"
  unfolding is_stationary_def is_policy_def by simp

lemma is_stationary_const[intro]: "is_dec d \<Longrightarrow> is_stationary (\<lambda>_. d)"
  by simp

abbreviation "mk_stationary p \<equiv> mk_markovian (\<lambda>_. p)"
abbreviation "mk_stationary_det d \<equiv> mk_markovian (\<lambda>_. mk_dec_det d)"

subsubsection \<open>Successor Policy\<close>
text \<open>
After taking the first step in the MDP, we will know which state and which action got selected 
during the initial epoch. To obtain a policy that acts as if the current epoch was the initial one, 
we prepend the observed state-action pair to the history. The result is again a policy, 
i.e. it satisfies @{const is_policy}.
\<close>
definition "\<pi>_Suc p sa h = p (sa#h)"

lemma is_policy_\<pi>_Suc [intro]: "is_policy p \<Longrightarrow> is_policy (\<pi>_Suc p sa)"
  unfolding is_policy_def \<pi>_Suc_def by force

lemma Suc_mk_markovian[simp]: "\<pi>_Suc (mk_markovian p) x = mk_markovian (\<lambda>n. p (Suc n))"
  unfolding \<pi>_Suc_def mk_markovian_def by auto

section \<open>Stream Space of the MDP\<close>
subsection \<open>K0\<close>
text \<open>
If we fix a decision rule @{term d} and an initial distribution of states @{term "S0"}, 
we obtain a distribution over state-action pairs in the following way:
First, the initial state @{term "s"} is sampled from @{term S0}, 
then an action @{term a} is selected from @{term "d s"}.
\<close>

definition "K0 d S0 = do {
  s \<leftarrow> S0; 
  a \<leftarrow> d s;
  return_pmf (s,a)
}" 

notation K0 ("K\<^sub>0")

lemma K0_iff: "K0 d S0 = S0 \<bind> (\<lambda>s. map_pmf (\<lambda>a. (s,a)) (d s))"
  by (simp add: K0_def map_pmf_def)

lemma vimage_pair[simp]: "Pair x -` {p} = (if x = fst p then {snd p} else {})"
  by auto

lemma pmf_K0 [simp]: "pmf (K0 d S0) (s,a) = pmf S0 s * pmf (d s) a"
  unfolding K0_iff pmf_bind
  apply (subst integral_measure_pmf[where A = "{s}"])
  by (auto simp add: pmf_map pmf.rep_eq split: if_splits)

lemma set_pmf_K0: "set_pmf (K0 p S0) = {(s,a). s \<in> S0 \<and> a \<in> p s}"
  by (auto simp add: K0_def)

lemma fst_K0[simp]: "map_pmf fst (K0 p S0) = S0"
  unfolding K0_def
  by (simp add: map_bind_pmf map_pmf_comp bind_return_pmf')

abbreviation "S \<equiv> stream_space (count_space UNIV)"

text \<open>We inherit the trace space from MDPs with continuous state-action spaces\<close>
interpretation MDP_cont: MDP_cont.discrete_MDP "count_space UNIV" "count_space UNIV" A K
proof standard
  show "(\<lambda>x. measure_pmf (K x)) \<in> 
    count_space UNIV \<Otimes>\<^sub>M count_space UNIV \<rightarrow>\<^sub>M prob_algebra (count_space UNIV)"
    apply (intro measurable_prob_algebraI)
    apply (simp add: prob_space_measure_pmf)
    by (measurable, simp add: measurable_pair_measure_countable1)
  show "\<exists>\<delta>\<in>count_space UNIV \<rightarrow>\<^sub>M count_space UNIV. \<forall>s. \<delta> s \<in> A s"
    by (auto simp: A_ne some_in_eq intro: bexI[of _ "\<lambda>s. SOME a. a \<in> A s"])
qed (auto simp: A_ne)

lemma count_space_M[simp]: "MDP_cont.M = count_space UNIV"
  by (auto simp: pair_measure_countable)

lemma space_M[simp]: "space MDP_cont.M = UNIV"
  by (auto simp: MDP_cont.space_lim_stream)

text \<open>We reuse the stream space provided by @{const MDP_cont.lim_stream}\<close>
definition T :: "('s, 'a) pol \<Rightarrow> 's pmf \<Rightarrow> ('s \<times> 'a) stream measure"
  where "T p = MDP_cont.lim_stream (\<lambda>n (h,s). p (Omega_Words_Fun.prefix n h) s)"

lemma sets_T[measurable_cong]: 
  "sets (T p x) = sets S"
  by (auto simp: T_def MDP_cont.sets_lim_stream)

lemma space_stream_space_ne[simp]: "space S \<noteq> {}"
  by (auto simp: space_stream_space)

lemma space_T[simp]: "space (T p S0) = space S"
  by (simp add: MDP_cont.space_lim_stream T_def space_stream_space)

lemma is_policy_MDP_cont[intro]: 
  fixes p :: "('s \<times> 'a) list \<Rightarrow> 's \<Rightarrow> 'a pmf"
  shows "MDP_cont.is_policy (\<lambda>n (h,s). p (Omega_Words_Fun.prefix n h) s)"
  unfolding is_policy_def is_dec_def MDP_cont.is_policy_def MDP_cont.is_dec_def
  using prefix_measurable measurable_pair_swap_iff
  by (auto simp: prob_space_measure_pmf
      intro: measurable_pair_measure_countable1 measurable_prob_algebraI)

lemma prob_space_T[intro, simp]: "prob_space (T p x)"
  by (auto simp add: T_def prob_space_measure_pmf space_prob_algebra)

lemma T_subprob[simp]: 
  "T p S0 \<in> space (subprob_algebra S)"
  by (metis prob_space.M_in_subprob prob_space_T sets_T subprob_algebra_cong)

lemma T_subprob_space [simp]: "subprob_space (T p S0)"
  by (auto intro: prob_space_imp_subprob_space)

lemma K0_MDP_cont_eq: 
  "MDP_cont.K0 (\<lambda>x (h,s). measure_pmf (p (Omega_Words_Fun.prefix x h) s)) (measure_pmf S0) = 
    K0 (p []) S0"
  unfolding MDP_cont.K0_def K0_def MDP_cont.K'_def map_pmf_def
  by (simp add: measure_pmf_bind return_pmf.rep_eq)

subsection \<open>Decomposition of the Stream Space\<close>
text \<open>
The distribution of traces/walks the MDP allows should intuitively satisfy the following rule:

\<^enum> select the initial state @{term s} from @{term S0}
\<^enum> pass it to the decision rule @{term "p []"} to determine a distribution over actions
\<^enum> select the action @{term a}
\<^item> finally pass the state-action pair @{term "(s,a)"} to the kernel @{term K} to get a new 
  distribution over states @{term s0'}

Then the iteration repeats with the updated policy @{term "\<pi>_Suc p (s,a)"}.

The result carries over from @{thm MDP_cont.lim_stream_eq}.
\<close>

lemma T_eq:
  shows "T p S0 = do {
    sa \<leftarrow> measure_pmf (K0 (p []) S0);
    \<omega> \<leftarrow> T (\<pi>_Suc p sa) (K sa);
    return S (sa ## \<omega>)
  }"
  unfolding T_def
  apply (subst MDP_cont.lim_stream_eq)
  subgoal by auto
  subgoal by (simp add: space_prob_algebra prob_space_measure_pmf)
  by (simp add: \<pi>_Suc_def MDP_cont.Suc_policy_def prefix_cons K0_MDP_cont_eq prod.case_distrib)

lemma T_eq_distr:
  shows "T p S0 = measure_pmf (K0 (p []) S0) \<bind> (\<lambda>sa. distr (T (\<pi>_Suc p sa) (K sa)) S ((##) sa))"
  by (simp add: T_eq[symmetric] bind_return_distr'[symmetric])

text \<open>
The iteration rule lets us nicely decompose integrals (expected values) over functions on traces of 
the MDP.
\<close>
lemma integral_T:
  fixes f :: "('s \<times> 'a) stream \<Rightarrow> real"
  assumes f_bounded: "\<And>x. \<bar>f x\<bar> \<le> B"
  assumes f: "f \<in> borel_measurable S"
  shows "(\<integral>t. f t \<partial>T p x) = \<integral>sa. \<integral>t'. f (sa##t') \<partial>T (\<pi>_Suc p sa) (K sa) \<partial>K0 (p []) x"
  apply (subst T_eq_distr)
  apply (subst integral_bind[OF f f_bounded, where B' = 1])
  subgoal
    by (auto intro!: prob_space_imp_subprob_space prob_space.prob_space_distr 
        simp: space_subprob_algebra)
  subgoal by auto
  subgoal by (auto intro!: prob_space.emeasure_le_1 prob_space.prob_space_distr)
  by (auto simp: f integral_distr intro: Bochner_Integration.integral_cong)

lemma nn_integral_T:
  assumes f: "f \<in> borel_measurable S"
  shows "(\<integral>\<^sup>+t. f t \<partial>T p x) = (\<integral>\<^sup>+sa. \<integral>\<^sup>+ t'. f (sa##t') \<partial>T (\<pi>_Suc p sa) (K sa) \<partial>K0 (p []) x)"
  apply (subst T_eq_distr)
  apply (subst nn_integral_bind[OF f])
  by (auto intro!: prob_space_imp_subprob_space prob_space.prob_space_distr 
      simp: f nn_integral_distr space_subprob_algebra)

subsection \<open>A Denotational View on the Stochastic Process\<close>
text \<open>
Many definitions on MDPs do not rely on the individual traces but only on the distribution 
of states and actions at each epoch.

We define this view on the trace space as the repeated iteration of @{const K0} and @{term K}.
It conincides with the definition of @{const T}.
\<close>

primrec Pn :: "('s, 'a) pol \<Rightarrow> 's pmf \<Rightarrow> nat \<Rightarrow> ('s \<times> 'a) pmf" where
  "Pn p S0 0 = K0 (p []) S0"
| "Pn p S0 (Suc n) = K0 (p []) S0 \<bind> (\<lambda>sa. Pn (\<pi>_Suc p sa) (K sa) n)"
declare Pn.simps(2)[simp del]

lemma Pn_eq_T:
  shows "measure_pmf (Pn p S0 n) = distr (T p S0) (count_space UNIV) (\<lambda>t. t !! n)"
proof (induction n arbitrary: p S0)
  case (0 p S0)
  then show ?case
    apply (subst T_eq)
    apply (subst distr_bind[where K = S])
    subgoal by (auto intro!: prob_space_imp_subprob_space subprob_space.bind_in_space)[1]
    subgoal by simp
    subgoal by simp
    apply (subst bind_cong[OF refl, where g = "return (count_space UNIV)"])
    apply (subst distr_bind[where K = S])
    by (auto intro!: bind_const' 
        simp: distr_return bind_return'' space_stream_space subprob_space_return_ne)
next
  case (Suc n)
  show ?case
    apply (simp only: Pn.simps measure_pmf_bind T_eq[of p])
    apply (subst distr_bind[where K = S])
    subgoal by (auto intro!: prob_space_imp_subprob_space subprob_space.bind_in_space)[1]
    subgoal by simp
    subgoal by simp
    apply (intro bind_cong[OF refl])
    apply (subst Suc)
    apply (subst distr_bind[where K = S])
    by (auto simp add: subprob_space_return_ne distr_return space_stream_space bind_return_distr')
qed

text \<open>
The definition of @{const Pn} also allows us to easily prove that only enabled actions can occur in
the traces of the MDP.
\<close>

lemma Pn_in_A: "is_policy p \<Longrightarrow> (s, a) \<in> Pn p S0 n \<Longrightarrow> a \<in> A s"
proof (induction n arbitrary: S0 p)
  case 0
  then show ?case 
    using 0 unfolding is_policy_def is_dec_def
    by (auto simp: K0_def)
next
  case (Suc n)
  then show ?case
    by (auto simp: Pn.simps(2) K0_def)
qed

lemma T_in_A:
  assumes "is_policy p"
  shows "AE t in T p S0. snd (t !! n) \<in> A (fst (t !! n))"
proof -
  have aux: "AE t in distr (T p S0) (count_space UNIV) (\<lambda>t. t !! n). snd t \<in> A (fst t)"
    using assms Pn_eq_T[symmetric]
    by (auto simp: Pn_in_A intro!: AE_pmfI cong: AE_cong_simp)
  show ?thesis
    by (auto intro!: AE_distrD[OF _ aux])
qed

subsection \<open>Xn\<close>
text \<open>Alongside @{const Pn}, we also define the state and action distributions as projections.\<close>

definition "Xn p S0 n = map_pmf fst (Pn p S0 n)"

lemma X0 [simp]: "Xn p S0 0 = S0"
  using fst_K0 Xn_def by auto

lemma Xn_Suc: "Xn p S0 (Suc n) = Pn p S0 n \<bind> K"
proof (induction n arbitrary: p S0)
  case 0
  then show ?case
    by (simp add: Pn.simps(2) Xn_def map_bind_pmf)
next
  case (Suc n)
  then show ?case
    by (simp add: Pn.simps(2) Xn_def map_bind_pmf bind_assoc_pmf)
qed

lemma Pn_markovian_eq_Xn_bind: "Pn (mk_markovian p) S0 n = K0 (p n) (Xn (mk_markovian p) S0 n)"
proof (induction n arbitrary: p S0)
  case 0
  then show ?case 
    unfolding Xn_def by auto
next
  case (Suc n)
  then show ?case
    unfolding Xn_def K0_def
    by (auto intro!: bind_pmf_cong simp: Pn.simps(2) map_bind_pmf Suc bind_assoc_pmf)
qed

lemma Xn_Suc': "Xn p S0 (Suc n) = K0 (p []) S0 \<bind> (\<lambda>sa. Xn (\<pi>_Suc p sa) (K sa) n)"
  unfolding Xn_def by (auto simp: Pn.simps(2) map_bind_pmf)

lemma set_pmf_X0 [simp]: "set_pmf (Xn p S0 0) = S0"
  using X0 by auto

lemma set_pmf_PSuc: "set_pmf (Pn (mk_markovian p) S0 n) = 
  {(s, a). s \<in> set_pmf (Xn (mk_markovian p) S0 n) \<and> a \<in> p n s}"
  using set_pmf_K0 Pn_markovian_eq_Xn_bind
  by auto

subsection \<open>The Conditional Distribution of Actions\<close>
text \<open>
Actions are selected wrt. the whole history of state-action pairs encountered so far.
The following definition defines the expected action selection when only the current state is given.\<close>
definition "Y_cond_X p S0 n x = map_pmf snd (cond_pmf (Pn p S0 n) {(s,a). s = x})"

lemma prob_K0_X [simp]: "measure_pmf.prob (K0 p S0) {(s, a). s = x} = pmf S0 x"
  unfolding K0_iff
  apply (subst measure_pmf_bind)
  apply (subst measure_pmf.measure_bind[of _ _ "count_space UNIV"])
  apply (simp add: measure_pmf_in_subprob_algebra)
  apply simp
  apply (subst integral_measure_pmf_real[of "{x}"])
  by (auto split: if_splits)

lemma prob_Pn_X[simp]: "measure_pmf.prob (Pn p S0 n) {(s, a). s = x} = pmf (Xn p S0 n) x"
proof (induction n arbitrary: p S0)
  case 0
  then show ?case
    by auto
next
  case (Suc n)
  show ?case
    apply (subst Xn_Suc')
    apply (subst Pn.simps(2))
    apply (subst measure_pmf_bind)
    using Suc unfolding K0_def
    by (simp add: measure_pmf.measure_bind[of _ _ "count_space UNIV"] 
        measure_pmf_in_subprob_algebra pmf_bind)
qed

lemma pmf_Pn_pair:
  assumes "sa \<in> set_pmf (Pn p S0 n)"
  shows "pmf (Pn p S0 n) sa = pmf (Y_cond_X p S0 n (fst sa)) (snd sa) * pmf (Xn p S0 n) (fst sa)"
proof -
  have aux: "set_pmf (Pn p S0 n) \<inter> {(s, a). s = fst sa} \<noteq> {}"
    using Xn_def assms by auto
  have aux': "({(s, a). s = fst sa} \<inter> snd -` {snd sa}) = {sa}"
    by auto
  show ?thesis
    using assms
    unfolding Y_cond_X_def pmf_map cond_pmf.rep_eq[OF aux]
    by (auto simp: Xn_def pmf_eq_0_set_pmf measure_pmf.emeasure_eq_measure aux' measure_pmf_single)
qed

lemma pmf_Pn:
  assumes "x \<in> set_pmf (Xn p S0 n)"
  shows "pmf (Pn p S0 n) (x,a) = pmf (Y_cond_X p S0 n x) a * pmf (Xn p S0 n) x"
proof -
  have aux: "set_pmf (Pn p S0 n) \<inter> {(s, a). s = x} \<noteq> {}"
    using Xn_def assms by auto
  have aux': "({(s, a). s = x} \<inter> snd -` {a}) = {(x, a)}"
    by auto
  show ?thesis
    using assms
    unfolding Y_cond_X_def cond_pmf.rep_eq[OF aux] pmf_map
    by (auto simp: pmf_eq_0_set_pmf measure_pmf.emeasure_eq_measure aux' measure_pmf_single)
qed

lemma pmf_Y_cond_X:
  assumes "x \<in> set_pmf (Xn p S0 n)"
  shows "pmf (Y_cond_X p S0 n x) a = pmf (Pn p S0 n) (x,a) / pmf (Xn p S0 n) x"
proof -
  have aux: "set_pmf (Pn p S0 n) \<inter> {(s, a). s = x} \<noteq> {}"
    using Xn_def assms by auto
  have aux': "({(s, a). s = x} \<inter> snd -` {a}) = {(x, a)}"
    by auto
  show ?thesis
    using assms aux'
    unfolding Y_cond_X_def
    by (auto simp: cond_pmf.rep_eq[OF aux] pmf_map pmf_eq_0_set_pmf measure_pmf.emeasure_eq_measure 
        measure_pmf_single)
qed

lemma Y_cond_X_0[simp]:
  assumes "x \<in> set_pmf S0"
  shows "Y_cond_X p S0 0 x = p [] x"
  by (auto intro: pmf_eqI simp: assms pmf_Y_cond_X pmf_eq_0_set_pmf)

(* eqn 5.5.3 in Puterman *)
lemma Y_cond_X_markovian[simp]:
  assumes h: "x \<in> Xn (mk_markovian p) S0 n"
  shows "Y_cond_X (mk_markovian p) S0 n x = p n x"
  by (auto intro!: pmf_eqI simp: pmf_Y_cond_X h Pn_markovian_eq_Xn_bind pmf_eq_0_set_pmf)

lemma Pn_eq_Xn_Y_cond: "Pn p S0 n = Xn p S0 n \<bind> (\<lambda>x. map_pmf (\<lambda>a. (x, a)) (Y_cond_X p S0 n x))"
proof (induction n)
  case 0
  then show ?case 
    by (auto simp: K0_iff intro: bind_pmf_cong)
next
  case (Suc n)
  show ?case
  proof (intro pmf_eqI; safe)
    fix a :: 's 
    fix b :: 'a
    have aux': "pmf (Xn p S0 (Suc n) \<bind> (\<lambda>x. map_pmf (Pair x) (Y_cond_X p S0 (Suc n) x))) (a,b) 
      = measure_pmf.expectation (Pn p S0 (Suc n)) (\<lambda>x. 
          if fst x = a then pmf (Y_cond_X p S0 (Suc n) a) b else 0)"
      by (auto intro!: Bochner_Integration.integral_cong[OF refl] 
          simp: Xn_def bind_map_pmf pmf_map pmf_bind measure_pmf_single)
    also have "\<dots> = measure_pmf.expectation (Pn p S0 (Suc n))
     (\<lambda>x. indicator {(s',a'). s' = a} x * (pmf (Pn p S0 (Suc n)) (a, b) / pmf (Xn p S0 (Suc n)) a))"
      apply (intro Bochner_Integration.integral_cong_AE)
      apply (auto simp add: Xn_def pmf_Pn_pair pmf_Y_cond_X pmf_eq_0_set_pmf intro!: AE_pmfI)
      by (metis Xn_def fst_conv mult_eq_0_iff pmf_Pn_pair pmf_Y_cond_X pmf_eq_0_set_pmf)
    also have "\<dots> = measure_pmf.prob (Pn p S0 (Suc n)) {(s',a'). s' = a} * 
      pmf (Pn p S0 (Suc n)) (a, b) / pmf (Xn p S0 (Suc n)) a"
      by auto
    also have "\<dots> = pmf (Pn p S0 (Suc n)) (a,b)"
      using prob_Pn_X Xn_def pmf_Pn_pair pmf_eq_0_set_pmf by fastforce
    finally show "pmf (Pn p S0 (Suc n)) (a, b) = pmf (Xn p S0 (Suc n) \<bind> 
      (\<lambda>x. map_pmf (Pair x) (Y_cond_X p S0 (Suc n) x))) (a, b)"
      by auto
  qed
qed

lemma Pn_eq_Xn_Y_cond': 
  "Pn p S0 n = Xn p S0 n \<bind> (\<lambda>s. Y_cond_X p S0 n s \<bind> (\<lambda>a. return_pmf (s,a)))"
  by (metis K0_def K0_iff Pn_eq_Xn_Y_cond)

lemma Pn_markovian_Suc: "Pn (mk_markovian p) S0 (Suc n) = 
  Pn (mk_markovian p) S0 n \<bind> (\<lambda>sa. K0 (p (Suc n)) (K sa))"
proof (induction n arbitrary: S0 p)
  case 0
  then show ?case
    by (auto intro: bind_pmf_cong simp: Pn.simps(2) \<pi>_Suc_def)
next
  case (Suc n)
  show ?case
    by (auto simp add: Suc bind_assoc_pmf Pn.simps(2)[of _ S0] intro: bind_pmf_cong)
qed

subsection \<open>Yn\<close>
text \<open>The distribution of actions.\<close>
definition "Yn p S0 n = map_pmf snd (Pn p S0 n)"

lemma Y0: "Yn p S0 0 = S0 \<bind> p []"
  by (simp add: Yn_def K0_iff map_bind_pmf map_pmf_comp)

text \<open>
For markovian policies, the decision rules at each epoch are independent of each other,
hence we may express @{const Yn} solely in terms of @{const Xn} and the current decision rule.
\<close>

lemma Yn_markovian: "Yn (mk_markovian p) S0 n = Xn (mk_markovian p) S0 n \<bind> p n"
proof (induction n arbitrary: p S0) 
  case 0
  then show ?case
    by (auto simp: Y0)
next
  case (Suc n)
  then show ?case
    by (simp add: Xn_def Yn_def map_bind_pmf Suc Pn.simps(2) bind_assoc_pmf)
qed

subsection \<open>Restriction to Markovian Policies\<close>
abbreviation "as_markovian p S0 n x \<equiv> 
  if x \<in> (Xn p S0 n) then Y_cond_X p S0 n x else return_pmf (SOME a. a \<in> A x)"

text \<open>
For states which cannot occur we choose an arbitrary enabled action, as in this case we cannot make
any statements about @{const Y_cond_X} (a distribution conditioned on an event with probability 0).
\<close>

lemma is_\<Pi>\<^sub>M\<^sub>R_as_markovian:
  assumes p: "is_policy p" 
  shows "as_markovian p S0 \<in> \<Pi>\<^sub>M\<^sub>R"
proof -
  have aux: "\<And>hs s. s \<in> set_pmf (Xn p S0 hs) \<Longrightarrow> set_pmf ((Pn p S0 hs)) \<inter> {(s', a). s' = s} \<noteq> {}"
    by (simp add: measure_pmf_zero_iff[symmetric] pmf_eq_0_set_pmf)
  thus ?thesis
    using assms A_ne Pn_in_A
    unfolding is_dec_def Y_cond_X_def
    by (auto simp: some_in_eq)
qed

lemma is_policy_as_markovian: "is_policy p \<Longrightarrow> is_policy (mk_markovian (as_markovian p S0))"
  using is_\<Pi>\<^sub>M\<^sub>R_as_markovian \<Pi>\<^sub>M\<^sub>R_imp_policies by auto

theorem Pn_as_markovian_eq: "Pn (mk_markovian (as_markovian p S0)) S0 = Pn p S0"
proof 
  fix n show "Pn (mk_markovian (as_markovian p S0)) S0 n = Pn p S0 n"
  proof (induction n)
    case 0
    thus ?case
      by (auto intro!: map_pmf_cong bind_pmf_cong simp: K0_def)
  next
    case (Suc n)
    have "\<And>x. x \<in> Xn p S0 (Suc n) \<Longrightarrow> 
      Y_cond_X (mk_markovian (as_markovian p S0)) S0 (Suc n) x = Y_cond_X p S0 (Suc n) x"
      by (auto simp: Suc.IH Xn_Suc)
    moreover have "Xn (mk_markovian (as_markovian p S0)) S0 (Suc n) = Xn p S0 (Suc n)"
      by (simp add: Xn_Suc Suc.IH)
    ultimately show "Pn (mk_markovian (as_markovian p S0)) S0 (Suc n) = Pn p S0 (Suc n)"
      by (auto intro: bind_pmf_cong simp: Pn_eq_Xn_Y_cond)
  qed
qed

section \<open>MDPs without Initial Distribution\<close>
text \<open>
From now on, we assume a known, deterministic initial state.
All results from the previous discussion carry over as we arXn_Suce now in the special case
where we the initial state is of the form @{term "return_pmf s"}.
\<close>
definition "\<T> p s \<equiv> T p (return_pmf s)"

lemma \<T>_eq_return_distr: "\<T> p s =
  measure_pmf (p [] s) \<bind> (\<lambda>a.
    distr (T (\<pi>_Suc p (s,a)) (K (s,a))) S ((##) (s,a)))"
  unfolding \<T>_def
  apply (subst T_eq_distr)
  unfolding K0_iff
  by (fastforce intro!: bind_distr subprob_space.subprob_space_distr 
      simp: map_pmf_rep_eq space_subprob_algebra bind_return_pmf)+

lemma \<T>_eq_return:
  shows "\<T> p s = do {
    y \<leftarrow> measure_pmf (p [] s);
    \<omega> \<leftarrow> T (\<pi>_Suc p (s,y)) (K (s,y)); 
    return S ((s,y) ## \<omega>)
  }"
  apply (subst \<T>_eq_return_distr)
  by (auto simp add: bind_return_distr' prob_space.not_empty intro!: bind_cong)

lemma \<T>_return:
  shows "T p S0 = measure_pmf S0 \<bind> \<T> p"
  apply (subst T_eq_distr)
  unfolding K0_iff 
  apply (subst measure_pmf_bind)
  apply (subst bind_assoc[where N = "count_space UNIV", where R  = S])
  apply measurable[1]
   apply (auto intro!: prob_space_imp_subprob_space prob_space.prob_space_distr 
      simp: space_subprob_algebra)[1]
  apply (auto simp add: prob_space.not_empty map_pmf_rep_eq intro!: bind_cong)
  apply (subst bind_distr[where K  = S])
  by (auto intro!: prob_space_imp_subprob_space prob_space.prob_space_distr 
      simp: space_subprob_algebra \<T>_eq_return_distr)

lemma \<T>_return_eq:
  shows
    "\<T> p s \<equiv> do {
  a \<leftarrow> measure_pmf (p [] s);
  s' \<leftarrow> measure_pmf (K (s,a));
  w \<leftarrow> T (\<pi>_Suc p (s,a)) (return_pmf s');
  return S ((s,a)##w)
}"
  apply (subst \<T>_eq_return)
  apply (subst \<T>_return)
  apply (subst bind_assoc[of _ _ S _ S])
  by (auto simp add: \<T>_def)

lemma \<T>_eq:
  shows "\<T> p s = do {
  a \<leftarrow> measure_pmf (p [] s);
  s' \<leftarrow> measure_pmf (K (s,a));
  w \<leftarrow> \<T> (\<pi>_Suc p (s,a)) s';
  return S ((s,a)##w)
}"
  apply (subst \<T>_return_eq)
  by (simp add: \<T>_def)

lemma \<T>_prob_space[intro]: "prob_space (\<T> p s)"
  by (metis \<T>_def prob_space_T)

lemma \<T>_sets[measurable_cong]: 
  "sets (\<T> p s) = sets S"
  by (simp add: \<T>_def sets_T)

lemma measurable_ident_Suc'[measurable]: 
  "(\<lambda>x. x) \<in> \<T> (\<pi>_Suc p sa) s' \<rightarrow>\<^sub>M S"
  by (simp add: \<T>_def)

lemma nn_integral_\<T>: 
  fixes f :: "('s \<times> 'a) stream \<Rightarrow> real"
  assumes f[measurable]: "f \<in> borel_measurable S"
  shows "(\<integral>\<^sup>+t. f t \<partial>\<T> p s) 
    = \<integral>\<^sup>+a. \<integral>\<^sup>+s'. \<integral>\<^sup>+t'. f ((s,a)##t') \<partial>\<T> (\<pi>_Suc p (s,a)) s' \<partial>K (s,a) \<partial>p [] s"
  unfolding \<T>_def
  apply (subst nn_integral_T)
  apply (simp; fail)
  apply (subst \<T>_return)
  unfolding K0_def
  by (auto simp: \<T>_def nn_integral_bind[of _ S])

lemma integral_\<T>: 
  fixes f :: "('s \<times> 'a) stream \<Rightarrow> real"
  assumes f_bounded: "\<And>x. \<bar>f x\<bar> \<le> B"
  assumes f[measurable]: "f \<in> borel_measurable S"
  shows "(\<integral>t. f t \<partial>\<T> p s) 
    = \<integral>a. \<integral>s'. \<integral>t'. f ((s,a)##t') \<partial>\<T> (\<pi>_Suc p (s,a)) s' \<partial>K (s,a) \<partial>p [] s"
  unfolding \<T>_def
  apply (subst integral_T[OF f_bounded f])
  unfolding K0_iff
  apply (subst bind_return_pmf)
  apply (subst \<T>_return)
  apply (subst integral_map_pmf)
  apply (intro Bochner_Integration.integral_cong[OF refl])
  apply (subst integral_bind[OF _ f_bounded, where B' = 1, where K = S])
  by (auto simp: \<T>_def intro: prob_space.emeasure_le_1)

lemma integrable_\<T>_bounded[intro]:
  fixes f :: "('s \<times> 'a) stream \<Rightarrow> 'd :: {second_countable_topology,banach}"
  assumes f[measurable]: "f \<in> borel_measurable S"
  assumes b: "bounded (range f)"
  shows "integrable (\<T> p s) f"
  apply (intro finite_measure.integrable_const_bound[of _ _ "\<Squnion>range (norm \<circ> f)"])
  using b
  by (auto simp: prob_space.finite_measure \<T>_prob_space bounded_iff 
      intro!: AE_I2 cSUP_upper bounded_imp_bdd_above)+

definition "Pn' p s = Pn p (return_pmf s)"
definition "Xn' p s = Xn p (return_pmf s)"
definition "Yn' p s = Yn p (return_pmf s)"
definition "K0' d s \<equiv> map_pmf (\<lambda>a. (s, a)) (d s)"

definition "K_st d s \<equiv> d s \<bind> (\<lambda>a. K (s,a))"

lemma pmf_K_st: "pmf (K_st d s) t = \<integral>a. pmf (K(s, a)) t \<partial>d s"
  unfolding K_st_def
  apply (subst pmf_bind)
  by auto

text \<open>
@{const K_st} defines the distribution over the successor states for a given decision rule and state.
It is mostly useful for markovian policies, as the information which action was selected is lost.\<close>

lemma P0'[simp]: "Pn' p s 0 = K0' (p []) s"
  by (simp add: Pn'_def K0'_def K0_iff bind_return_pmf)

lemma X0'[simp]: "Xn' p s 0 = return_pmf s"
  using X0 Xn'_def by auto

lemma Pn_return_pmf: "S0 \<bind> (\<lambda>s'. Pn p (return_pmf s') n) = Pn p S0 n"
  apply (induction n arbitrary: p S0)
  by (auto intro: bind_pmf_cong simp add: Pn.simps(2) K0_def bind_assoc_pmf bind_return_pmf)

lemma PSuc': "Pn' p s (Suc n) = K0' (p []) s \<bind> (\<lambda>sa. K sa \<bind> (\<lambda>s'. Pn' (\<pi>_Suc p sa) s' n))"
  unfolding Pn'_def
  by (auto intro!: bind_pmf_cong 
      simp: Pn.simps(2) Pn_return_pmf K0_iff K0'_def bind_return_pmf map_bind_pmf bind_map_pmf)

lemma PSuc'_markovian: 
  "Pn' (mk_markovian p) s (Suc n) = K_st (p 0) s \<bind> (\<lambda>s'. Pn' (mk_markovian (p \<circ> Suc)) s' n)"
  unfolding PSuc'
  by (auto simp: bind_map_pmf bind_assoc_pmf comp_def K0'_def K_st_def intro!: bind_pmf_cong)

lemma Xn'_Suc: "Xn' p s (Suc n) = Pn' p s n \<bind> K"
  by (auto simp: Xn_Suc Xn'_def Pn'_def)

lemma Xn'_Pn': "Xn' p s n = map_pmf fst (Pn' p s n)"
  by (simp add: Xn_def Xn'_def Pn'_def)

lemma Suc_Xn': "Xn' p s (Suc n) = p [] s \<bind> (\<lambda>a. K (s,a) \<bind> (\<lambda>s'. Xn' (\<pi>_Suc p (s,a)) s' n))"
  by (auto simp: Xn'_Pn' map_bind_pmf bind_map_pmf PSuc' K0'_def)

lemma Suc_Xn'_markovian: 
  "Xn' (mk_markovian p) s (Suc n) = K_st (p 0) s \<bind> (\<lambda>s'. Xn' (mk_markovian (\<lambda>n. p (Suc n))) s' n)"
  by (auto simp: K_st_def bind_assoc_pmf Suc_Xn')

lemma Xn'_split: "Xn' (mk_markovian p) s (n + m) = 
  Xn' (mk_markovian p) s n \<bind> (\<lambda>s. Xn' (mk_markovian (\<lambda>i. p (i + n))) s m)"
  apply (induction n arbitrary: p s)
  by (auto intro!: bind_pmf_cong simp add: bind_assoc_pmf bind_return_pmf Suc_Xn')

lemma Yn'_markovian: "Yn' (mk_markovian p) s n = Xn' (mk_markovian p) s n \<bind> p n"
  unfolding Yn'_def Xn'_def Yn_markovian by simp

lemma Pn'_markovian_eq_Xn'_bind: "Pn' (mk_markovian p) s n = Xn' (mk_markovian p) s n \<bind> K0' (p n)"
  unfolding Xn'_def Pn'_def K0'_def K0_iff Pn_markovian_eq_Xn_bind by simp

lemma Pn'_eq_\<T>: "measure_pmf (Pn' p s n) = distr (\<T> p s) (count_space UNIV) (\<lambda>t. t !! n)"
  by (auto simp: \<T>_def Pn'_def Pn_eq_T)
end
end