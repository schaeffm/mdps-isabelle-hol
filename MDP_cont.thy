(* Author: Maximilian Schäffeler, adapted from Markov_Models.Discrete_Time_Markov_Process *)

section \<open>Discrete-time Markov Decision Processes\<close>

text \<open>
  In this file we construct discrete-time Markov decision processes, 
  e.g. with arbitrary state spaces.
  Proofs and definitions are adapted from Markov_Models.Discrete_Time_Markov_Process.
\<close>

theory MDP_cont
  imports "HOL-Probability.Probability"
begin

lemma Ionescu_Tulcea_C_eq:
  assumes "\<And>i h. h \<in> space (PiM {0..<i} N) \<Longrightarrow> P i h = P' i h"
  assumes h: "Ionescu_Tulcea P N" "Ionescu_Tulcea P' N"
  shows "Ionescu_Tulcea.C P N 0 n (\<lambda>x. undefined) = Ionescu_Tulcea.C P' N 0 n (\<lambda>x. undefined)"
proof (induction n)
  case 0
  then show ?case using h by (auto simp: Ionescu_Tulcea.C_def)
next
  case (Suc n)
  have aux: "space (PiM {0..<0 + n} N) = space (rec_nat (\<lambda>n. return (Pi\<^sub>M {0..<n} N)) 
    (\<lambda>m ma n \<omega>. ma n \<omega> \<bind> Ionescu_Tulcea.eP P' N (n + m)) n 0 (\<lambda>x. undefined))"
    apply (subst Ionescu_Tulcea.space_C[symmetric, where P = P', where x = "(\<lambda>x. undefined)"])
    using h Ionescu_Tulcea.space_C by (auto simp add: Ionescu_Tulcea.C_def)  
  have "\<And>i h. h \<in> space (PiM {0..<i} N) \<Longrightarrow> Ionescu_Tulcea.eP P N i h = Ionescu_Tulcea.eP P' N i h"
    by (auto simp add: Ionescu_Tulcea.eP_def assms)
  then show ?case 
    using Suc.IH h
    using aux[symmetric]
    by (auto intro!: bind_cong simp: Ionescu_Tulcea.C_def)
qed

lemma Ionescu_Tulcea_CI_eq:
  assumes "\<And>i h. h \<in> space (PiM {0..<i} N) \<Longrightarrow> P i h = P' i h"
  assumes h: "Ionescu_Tulcea P N" "Ionescu_Tulcea P' N"
  shows "Ionescu_Tulcea.CI P N = Ionescu_Tulcea.CI P' N"
proof -
  have "\<And>J. Ionescu_Tulcea.CI P N J = Ionescu_Tulcea.CI P' N J"
    apply (subst Ionescu_Tulcea.CI_def[OF h(1)])
    apply (subst Ionescu_Tulcea.CI_def[OF h(2)])
    using assms by (auto intro!: distr_cong Ionescu_Tulcea_C_eq)
  thus ?thesis by auto
qed

lemma measure_eqI_PiM_sequence:
  fixes M :: "nat \<Rightarrow> 'a measure"
  assumes *[simp]: "sets P = PiM UNIV M" "sets Q = PiM UNIV M"
  assumes eq: "\<And>A n. (\<And>i. A i \<in> sets (M i)) \<Longrightarrow>
    P (prod_emb UNIV M {..n} (Pi\<^sub>E {..n} A)) = Q (prod_emb UNIV M {..n} (Pi\<^sub>E {..n} A))"
  assumes A: "finite_measure P"
  shows "P = Q"
proof (rule measure_eqI_PiM_infinite[OF * _ A])
  fix J :: "nat set" and F'
  assume J: "finite J" "\<And>i. i \<in> J \<Longrightarrow> F' i \<in> sets (M i)"

  define n where "n = (if J = {} then 0 else Max J)"
  define F where "F i = (if i \<in> J then F' i else space (M i))" for i
  then have F[simp, measurable]: "F i \<in> sets (M i)" for i
    using J by auto
  have emb_eq: "prod_emb UNIV M J (Pi\<^sub>E J F') = prod_emb UNIV M {..n} (Pi\<^sub>E {..n} F)"
  proof cases
    assume "J = {}" then show ?thesis
      by (auto simp add: n_def F_def[abs_def] prod_emb_def PiE_def)
  next
    assume "J \<noteq> {}" then show ?thesis
      by (auto simp: prod_emb_def PiE_iff F_def n_def less_Suc_eq_le \<open>finite J\<close> split: if_split_asm)
  qed

  show "emeasure P (prod_emb UNIV M J (Pi\<^sub>E J F')) = emeasure Q (prod_emb UNIV M J (Pi\<^sub>E J F'))"
    unfolding emb_eq by (rule eq) fact
qed

lemma distr_cong_simp:
  "M = K \<Longrightarrow> sets N = sets L \<Longrightarrow> (\<And>x. x \<in> space M =simp=> f x = g x) \<Longrightarrow> distr M N f = distr K L g"
  unfolding simp_implies_def by (rule distr_cong)

subsection \<open>Definition and Basic Properties\<close>

locale discrete_MDP =
  fixes Ms :: "'s measure"
    and Ma :: "'a measure"
    and A :: "'s \<Rightarrow> 'a set"
    and K :: "'s \<times> 'a \<Rightarrow> 's measure"
    (* The valid actions are measurable subsets of all actions *)
  assumes A_s: "\<And>s. A s \<in> sets Ma"
    (* There always exists a valid action *)
  assumes A_ne: "\<And>s. A s \<noteq> {}"
    (* Assume the existence of at least 1 policy *)
  assumes ex_pol: "\<exists>\<delta> \<in> Ms \<rightarrow>\<^sub>M Ma. \<forall>s. \<delta> s \<in> A s"
    (* The kernel maps a state-action pair to a distribution over states *)
  assumes K[measurable]: "K \<in> Ms \<Otimes>\<^sub>M Ma \<rightarrow>\<^sub>M prob_algebra Ms"
begin

lemma space_prodI[intro]: "x \<in> space A' \<Longrightarrow> y \<in> space B \<Longrightarrow> (x,y) \<in> space (A' \<Otimes>\<^sub>M B)"
  by (auto simp add: space_pair_measure)

abbreviation "M \<equiv> Ms \<Otimes>\<^sub>M Ma"
abbreviation "Ma_A s \<equiv> restrict_space Ma (A s)"

lemma space_ma[intro]: "s \<in> space Ms \<Longrightarrow> a \<in> space Ma \<Longrightarrow> (s,a) \<in> space M"
  by (simp add: space_pair_measure)

lemma space_x0[simp]: "x0 \<in> space (prob_algebra Ms) \<Longrightarrow> space x0 = space Ms"
  by (metis (mono_tags, lifting) space_prob_algebra mem_Collect_eq sets_eq_imp_space_eq)

lemma A_subs_Ma: "A s \<subseteq> space Ma"
  by (simp add: A_s sets.sets_into_space)

lemma space_Ma_A_subset: "s \<in> space Ms \<Longrightarrow> space (Ma_A s) \<subseteq> A s"
  by (simp add: space_restrict_space)

lemma K_restrict [measurable]: "K \<in> (Ms \<Otimes>\<^sub>M Ma_A s) \<rightarrow>\<^sub>M prob_algebra Ms"
  apply measurable
  by (metis measurable_id measurable_pair_iff measurable_restrict_space2_iff)

lemma measurable_K_act[measurable, intro]: "s \<in> space Ms \<Longrightarrow> (\<lambda>a. K (s, a)) \<in> Ma \<rightarrow>\<^sub>M prob_algebra Ms"
  by measurable

lemma measurable_K_st[measurable, intro]: "a \<in> space Ma \<Longrightarrow> (\<lambda>s. K (s, a)) \<in> Ms \<rightarrow>\<^sub>M prob_algebra Ms"
  by measurable

lemma space_K[simp]: "sa \<in> space M \<Longrightarrow> space (K sa) = space Ms"
  using K unfolding prob_algebra_def measurable_restrict_space2_iff
  by (auto dest: subprob_measurableD)

lemma space_K2[simp]: "s \<in> space Ms \<Longrightarrow> a \<in> space Ma \<Longrightarrow> space (K (s, a)) = space Ms"
  by (simp add: space_pair_measure)

lemma space_K_E: "s' \<in> space (K (s,a)) \<Longrightarrow> s \<in> space Ms \<Longrightarrow> a \<in> space Ma \<Longrightarrow> s' \<in> space Ms"
  by auto

lemma sets_K: "sa \<in> space M \<Longrightarrow> sets (K sa) = sets Ms"
  using K unfolding prob_algebra_def unfolding measurable_restrict_space2_iff
  by (auto dest: subprob_measurableD)

lemma sets_K'[measurable_cong]: "s \<in> space Ms \<Longrightarrow> a \<in> space Ma \<Longrightarrow> sets (K (s,a)) = sets Ms"
  by (simp add: sets_K space_pair_measure)

lemma prob_space_K[intro]: "sa \<in> space M \<Longrightarrow> prob_space (K sa)"
  using measurable_space[OF K] by (simp add: space_prob_algebra)

lemma prob_space_K2[intro]: "s \<in> space Ms \<Longrightarrow> a \<in> space Ma \<Longrightarrow> prob_space (K (s,a))"
  using prob_space_K by (simp add: space_pair_measure)

lemma K_in_space [intro]: "m \<in> space M \<Longrightarrow> K m \<in> space (prob_algebra Ms)"
  by (meson K measurable_space)

subsection \<open>Policies\<close>
  (* This section represents our own developments. *)

type_synonym ('c, 'd) pol = "nat \<Rightarrow> ((nat \<Rightarrow> 'c \<times> 'd) \<times> 'c) \<Rightarrow> 'd measure"

(* History of i steps *)
abbreviation "H i \<equiv> Pi\<^sub>M {0..<i} (\<lambda>_. M)"
  (* + current state *)
abbreviation "Hs i \<equiv>  H i \<Otimes>\<^sub>M Ms"

lemma space_H1: "j < (i :: nat)  \<Longrightarrow> \<omega> \<in> space (H i) \<Longrightarrow> \<omega> j \<in> space M"
  apply (simp add: space_PiM)
  using PiE_def by auto

lemma space_case_nat[intro]: 
  assumes "\<omega> \<in> space (H i)" "s \<in> space Ms"  
  shows "case_nat s (fst \<circ> \<omega>) i \<in> space Ms"
  apply (cases i)
  using assms apply auto
  by (metis assms(1) lessI measurable_fst measurable_space space_H1)

lemma undefined_in_H0: "(\<lambda>_. undefined) \<in> space (H (0 :: nat))"
  by auto

lemma sets_K_Suc[measurable_cong]: "h \<in> space (H (Suc n)) \<Longrightarrow> sets (K (h n)) = sets Ms"
  using sets_K space_H1 by blast

text\<open>A decision rule is a function from states to distributions over enabled actions.\<close>
definition "is_dec0 d \<equiv> d \<in> Ms \<rightarrow>\<^sub>M prob_algebra Ma "

definition "is_dec (t :: nat) d \<equiv> (d \<in> Hs t \<rightarrow>\<^sub>M prob_algebra Ma) "

lemma "is_dec0 d \<Longrightarrow> is_dec t (\<lambda>(_,s). d s)"
  unfolding is_dec0_def is_dec_def by auto

text\<open>A policy is a function from histories to valid decision rules.\<close>
definition is_policy :: "('s, 'a) pol \<Rightarrow> bool" where
  "is_policy p \<equiv> \<forall>i. is_dec i (p i)"

(* selects the next action without history *)
abbreviation p0 :: "('s, 'a) pol \<Rightarrow> 's \<Rightarrow> 'a measure" where
  "p0 p s \<equiv> p (0 ::nat) (\<lambda>_. undefined, s)"

context
  fixes p assumes p[simp]: "is_policy p"
begin

lemma is_policyD[measurable]: "p i \<in> Hs i \<rightarrow>\<^sub>M prob_algebra Ma"
  using p unfolding is_policy_def is_dec_def by auto

lemma space_policy[simp]: "hs \<in> space (Hs i) \<Longrightarrow> space (p i hs) = space Ma"
  using K is_policyD unfolding prob_algebra_def measurable_restrict_space2_iff
  by (auto dest: subprob_measurableD)

lemma space_policy'[simp]: "h \<in> space (H i) \<Longrightarrow> s \<in> space Ms \<Longrightarrow> space (p i (h,s)) = space Ma"
  using space_policy 
  by (simp add: space_pair_measure)

lemma space_policyI[intro]: 
  assumes "s \<in> space Ms" "h \<in> space (H i)" "a \<in> space Ma"
  shows "a \<in> space (p i (h,s))"
  using space_policy assms 
  by (auto simp: space_pair_measure)

lemma sets_policy[simp]: "hs \<in> space (Hs i) \<Longrightarrow> sets (p i hs) = sets Ma"
  using p K is_policyD
  unfolding prob_algebra_def measurable_restrict_space2_iff
  by (auto dest: subprob_measurableD)

lemma sets_policy'[measurable_cong, simp]: 
  "h \<in> space (H i) \<Longrightarrow> s \<in> space Ms \<Longrightarrow> sets (p i (h,s)) = sets Ma"
  using sets_policy 
  by (auto simp: space_pair_measure)

lemma sets_policy''[measurable_cong, simp]: 
  "h \<in> space ((Pi\<^sub>M {} (\<lambda>_. M))) \<Longrightarrow> s \<in> space Ms \<Longrightarrow> sets (p 0 (h,s)) = sets Ma"
  using sets_policy 
  by (auto simp: space_pair_measure)

lemma policy_prob_space: "hs \<in> space (Hs i) \<Longrightarrow> prob_space (p i hs)"
proof -
  assume h: "hs \<in> space (Hs i)"
  hence "p i hs \<in> space (prob_algebra Ma)" 
    using p by (auto intro: measurable_space)
  thus "prob_space (p i hs)"
    unfolding prob_algebra_def by (simp add: space_restrict_space)
qed

lemma policy_prob_space': "h \<in> space (H i) \<Longrightarrow> s \<in> space Ms \<Longrightarrow> prob_space (p i (h,s))"
  using policy_prob_space by (simp add: space_pair_measure)

lemma prob_space_p0: "x \<in> space Ms \<Longrightarrow> prob_space (p0 p x)"
  by (simp add: policy_prob_space')

lemma p0_sets[measurable_cong]: "x \<in> space Ms \<Longrightarrow> sets (p 0 (\<lambda>_. undefined,x)) = sets Ma"
  using subprob_measurableD(2) measurable_prob_algebraD by simp

lemma space_p0[simp]: "s \<in> space Ms \<Longrightarrow> space (p0 p s) = space Ma"
  by auto

lemma return_policy_prob_algebra [measurable]: 
  "h \<in> space (H n) \<Longrightarrow> x \<in> space Ms \<Longrightarrow> (\<lambda>a. return M (x, a)) \<in> p n (h, x) \<rightarrow>\<^sub>M prob_algebra M"
  by measurable
end

subsection \<open>Successor Policy\<close>
text \<open>To shift the policy by one step, we provide a single state-action pair as history\<close>
definition "Suc_policy p sa = (\<lambda>i (h, s). p (Suc i) (\<lambda>i'. case_nat sa h i', s))"

lemma p_as_Suc_policy: "p (Suc i) (h, s) = Suc_policy p ((h 0)) i (\<lambda>i. h (Suc i), s)"
  unfolding Suc_policy_def apply auto
  by (metis old.nat.exhaust old.nat.simps(4) old.nat.simps(5))

lemma is_policy_Suc_policy[intro]:
  assumes s: "sa \<in> space M" and p: "is_policy p"
  shows "is_policy (Suc_policy p sa)"
proof -
  have "\<And>i. p i \<in> Pi\<^sub>M {0..<i} (\<lambda>_. M) \<Otimes>\<^sub>M Ms \<rightarrow>\<^sub>M prob_algebra Ma"
    using is_policyD p by blast
  hence 2: "\<And>i. Suc_policy p sa i \<in> Pi\<^sub>M {0..<i} (\<lambda>_. M) \<Otimes>\<^sub>M Ms \<rightarrow>\<^sub>M prob_algebra Ma"
    unfolding Suc_policy_def using p s
    using p s 
    apply measurable
     apply (intro measurable_PiM_single)
    using s space_H1
    by (fastforce split: nat.splits simp: space_PiM space_pair_measure)+
  thus ?thesis unfolding is_policy_def is_dec_def
    using 2 by blast
qed

lemma Suc_policy_measurable_step[measurable]: 
  assumes "is_policy p"
  shows "(\<lambda>x. Suc_policy p (fst (fst x)) n (snd (fst x), snd x)) \<in> 
    (M \<Otimes>\<^sub>M Pi\<^sub>M {0..<n} (\<lambda>_. M)) \<Otimes>\<^sub>M Ms \<rightarrow>\<^sub>M prob_algebra Ma"
  unfolding Suc_policy_def
  using assms 
  apply measurable 
  by (auto 
      intro: measurable_PiM_single' 
      simp:  space_pair_measure PiE_iff space_PiM extensional_def 
      split: nat.split)

subsection \<open>K'\<close>
text\<open>@{term "K'"} takes 
  a policy, 
  a distribution over 's, 
  the epoch,
  and a history, 
  produces a distribution over the next state-action pair.\<close>
definition K' :: "('s, 'a) pol \<Rightarrow> 's measure \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> ('s \<times> 'a)) \<Rightarrow> ('s \<times> 'a) measure"
  where
    "K' p s0 n \<omega> = do {
    s \<leftarrow> case_nat s0 (K \<circ> \<omega>) n;
    a \<leftarrow> p n (\<omega>, s);
    return M (s, a)
}"

lemma prob_space_K': 
  assumes p: "is_policy p" and x: "x0 \<in> space (prob_algebra Ms)" and h: "h \<in> space (H n)" 
  shows "prob_space (K' p x0 n h)"
  unfolding K'_def
proof (intro prob_space.prob_space_bind[where S = M])
  show "prob_space (case n of 0 \<Rightarrow> x0 | Suc x \<Rightarrow> (K \<circ> h) x)"
    using x h space_H1 by (auto split: nat.splits simp: space_prob_algebra)
next
  show "AE x in case n of 0 \<Rightarrow> x0 | Suc x \<Rightarrow> (K \<circ> h) x. 
    prob_space (p n (h, x) \<bind> (\<lambda>a. return M (x, a)))"
  proof (cases n)
    case 0
    then have h': "h \<in> space (Pi\<^sub>M {0..<0} (\<lambda>_. M))"
      using h by auto
    show ?thesis 
      using 0 p h x sets_policy'
      by (fastforce intro: prob_space.prob_space_bind[where S=M] 
          policy_prob_space prob_space_return 
          cong: measurable_cong_sets)
  next
    case (Suc nat)
    then show ?thesis
      using p h x sets_policy' policy_prob_space
      apply (auto intro!: AE_I2 prob_space.prob_space_bind measurable_prob_algebraD 
          prob_space_return)
      using space_H1 space_K apply blast
      using h space_H1 space_K apply (metis lessI space_policy' space_prodI)
      using return_policy_prob_algebra space_H1 space_K by blast
  qed
next
  show "(\<lambda>s. p n (h, s) \<bind> (\<lambda>a. return M (s, a))) \<in> 
    (case n of 0 \<Rightarrow> x0 | Suc x \<Rightarrow> (K \<circ> h) x) \<rightarrow>\<^sub>M subprob_algebra M"
  proof (intro measurable_bind[where N = Ma])
    show " (\<lambda>x. p n (h, x)) \<in> (case n of 0 \<Rightarrow> x0 | Suc x \<Rightarrow> (K \<circ> h) x) \<rightarrow>\<^sub>M subprob_algebra Ma"
      using p h x 
      by (auto split: nat.splits intro!: measurable_prob_algebraD simp: space_prob_algebra)
  next
    show "(\<lambda>s. return M (fst s, snd s)) \<in> 
      (case n of 0 \<Rightarrow> x0 | Suc x \<Rightarrow> (K \<circ> h) x) \<Otimes>\<^sub>M Ma \<rightarrow>\<^sub>M subprob_algebra M"
      using h x sets_K_Suc
      by (auto split: nat.splits simp: sets_K space_prob_algebra cong: measurable_cong_sets)
  qed
qed

lemma measurable_K'[measurable]:
  assumes p: "is_policy p" and x: "x \<in> space (prob_algebra Ms)" 
  shows "K' p x i \<in> H i \<rightarrow>\<^sub>M prob_algebra M"
proof -
  fix i
  show "K' p x i \<in> Pi\<^sub>M {0..<i} (\<lambda>_. M) \<rightarrow>\<^sub>M prob_algebra M"
    unfolding K'_def
  proof (intro measurable_bind_prob_space2[where N = Ms])
    show "(\<lambda>xa. case i of 0 \<Rightarrow> x | Suc x \<Rightarrow> (K \<circ> xa) x) \<in> Pi\<^sub>M {0..<i} (\<lambda>_. M) \<rightarrow>\<^sub>M prob_algebra Ms"
      apply measurable
      using x by auto
  next 
    show "(\<lambda>(\<omega>, y). p i (\<omega>, y) \<bind> (\<lambda>a. return M (y, a))) \<in> 
      Pi\<^sub>M {0..<i} (\<lambda>_. M) \<Otimes>\<^sub>M Ms \<rightarrow>\<^sub>M prob_algebra M"
      using x p by auto
  qed
qed

subsection \<open>K0\<close>
text \<open>@{term "K0"} produces the initial state-action distribution from a state distribution
 and a policy.\<close>
definition "K0 p s0 = K' p s0 0 (\<lambda>_. undefined)"

lemma K0_def':
  "K0 p s0 = do {
    s \<leftarrow> s0;
    a \<leftarrow> p0 p s;
    return M (s, a)}"
  unfolding K0_def K'_def by auto

lemma K0_prob[measurable]: "is_policy p \<Longrightarrow> K0 p \<in> prob_algebra Ms \<rightarrow>\<^sub>M prob_algebra M"
  unfolding K0_def' 
  by measurable

lemma prob_space_K0: "is_policy p \<Longrightarrow> x0 \<in> space (prob_algebra Ms) \<Longrightarrow> prob_space (K0 p x0)"
  by (simp add: K0_def prob_space_K')

lemma space_K0[simp]: "is_policy p \<Longrightarrow> s \<in> space (prob_algebra Ms) \<Longrightarrow> space (K0 p s) = space M"
  by (meson K0_prob measurable_prob_algebraD sets_eq_imp_space_eq sets_kernel)

lemma sets_K0[measurable_cong]:
  assumes "is_policy p" "s \<in> space (prob_algebra Ms)" 
  shows "sets (K0 p s) = sets M"
  using assms by (meson K0_prob measurable_prob_algebraD subprob_measurableD(2))

lemma K0_return_eq_p0: 
  assumes "is_policy p" "s \<in> space Ms" 
  shows "K0 p (return Ms s) = p0 p s \<bind> (\<lambda>a. return M (s,a))"
  unfolding K0_def'
  apply (subst bind_return[where N = M])
  using assms measurable_prob_algebraD 
  by measurable

lemma M_ne_policy[intro]: "is_policy p \<Longrightarrow> s \<in> space (prob_algebra Ms) \<Longrightarrow> space M \<noteq> {}"
  using space_K0 prob_space.not_empty prob_space_K0
  by force

subsection \<open>Sequence Space of the MDP\<close>
text\<open>We can instantiate @{const Ionescu_Tulcea} with @{const K'}.\<close>
lemma IT_K': "is_policy p \<Longrightarrow> x \<in> space (prob_algebra Ms) \<Longrightarrow> Ionescu_Tulcea (K' p x) (\<lambda>_. M)"
  unfolding Ionescu_Tulcea_def using measurable_K' prob_space_K'
  by (fast dest: measurable_prob_algebraD)

definition lim_sequence :: "('s, 'a) pol \<Rightarrow> 's measure \<Rightarrow> (nat \<Rightarrow> ('s \<times> 'a)) measure"
  where
    "lim_sequence p x = projective_family.lim UNIV (Ionescu_Tulcea.CI (K' p x) (\<lambda>_. M)) (\<lambda>_. M)"

lemma
  assumes x: "x \<in> space (prob_algebra Ms)" and p: "is_policy p"
  shows space_lim_sequence: "space (lim_sequence p x) = space (\<Pi>\<^sub>M i\<in>UNIV. M)"
    and sets_lim_sequence[measurable_cong]: "sets (lim_sequence p x) = sets (\<Pi>\<^sub>M i\<in>UNIV. M)"
    and emeasure_lim_sequence_emb: "\<And>J X. finite J \<Longrightarrow> X \<in> sets (\<Pi>\<^sub>M j\<in>J. M) \<Longrightarrow>
      emeasure (lim_sequence p x) (prod_emb UNIV (\<lambda>_. M) J X) =
      emeasure (Ionescu_Tulcea.CI (K' p x) (\<lambda>_. M) J) X"
    and emeasure_lim_sequence_emb_I0o: "\<And>n X. X \<in> sets (\<Pi>\<^sub>M i \<in> {0..<n}. M) \<Longrightarrow>
      emeasure (lim_sequence p x) (prod_emb UNIV (\<lambda>_. M) {0..<n} X) =
      emeasure (Ionescu_Tulcea.C (K' p x) (\<lambda>_. M) 0 n (\<lambda>x. undefined)) X"
proof -
  interpret Ionescu_Tulcea "K' p x" "\<lambda>_. M"
    using IT_K'[OF p x] .
  show "space (lim_sequence p x) = space (\<Pi>\<^sub>M i\<in>UNIV. M)"
    unfolding lim_sequence_def by simp
  show "sets (lim_sequence p x) = sets (\<Pi>\<^sub>M i\<in>UNIV. M)"
    unfolding lim_sequence_def by simp

  { fix J :: "nat set" and X assume "finite J" "X \<in> sets (\<Pi>\<^sub>M j\<in>J. M)"
    then show "emeasure (lim_sequence p x) (PF.emb UNIV J X) = emeasure (CI J) X"
      unfolding lim_sequence_def by (rule lim) }
  note emb = this

  have up_to_I0o[simp]: "up_to {0..<n} = n" for n
    unfolding up_to_def by (rule Least_equality) auto

  { fix n :: nat and X assume "X \<in> sets (\<Pi>\<^sub>M j\<in>{0..<n}. M)"
    thus "emeasure (lim_sequence p x) (PF.emb UNIV {0..<n} X) = emeasure (C 0 n (\<lambda>x. undefined)) X"
      by (simp add: space_C emb CI_def space_PiM distr_id2 sets_C cong: distr_cong_simp) }
qed

lemma lim_sequence_prob_space: 
  assumes "is_policy p" "s \<in> space (prob_algebra Ms)" 
  shows "prob_space (lim_sequence p s)"
  using assms proof -
  assume p: "is_policy p"
  fix s assume [simp]: "s \<in> space (prob_algebra Ms)"
  interpret Ionescu_Tulcea "K' p s" "\<lambda>_. M"
    using IT_K' p by simp
  have sp: 
    "space (lim_sequence p s) = prod_emb UNIV (\<lambda>_. M) {} (\<Pi>\<^sub>E j\<in>{}. space M)" 
    "space (CI {}) = {} \<rightarrow>\<^sub>E space M"
    by (auto simp: p space_lim_sequence space_PiM prod_emb_def PF.space_P)
  show "prob_space (lim_sequence p s)"
    apply standard
    using PF.prob_space_P[THEN prob_space.emeasure_space_1, of "{}"]
    by (simp add: p sp emeasure_lim_sequence_emb del: PiE_empty_domain)
qed

subsection \<open>Measurablility of lim sequence\<close>
lemma lim_sequence[measurable]: 
  assumes p: "is_policy p"  
  shows "lim_sequence p \<in> prob_algebra Ms \<rightarrow>\<^sub>M prob_algebra (\<Pi>\<^sub>M i\<in>UNIV. M)"
proof (intro measurable_prob_algebra_generated[OF sets_PiM Int_stable_prod_algebra 
      prod_algebra_sets_into_space])
  show "\<And>a. a \<in> space (prob_algebra Ms) \<Longrightarrow> prob_space (lim_sequence p a)"
    using lim_sequence_prob_space p by blast
next
  fix a assume [simp]: "a \<in> space (prob_algebra Ms)"
  show "sets (lim_sequence p a) = sets (Pi\<^sub>M UNIV (\<lambda>i. M))"
    by (simp add: p sets_lim_sequence)
next
  fix X :: "(nat \<Rightarrow> 's \<times> 'a) set" assume "X \<in> prod_algebra UNIV (\<lambda>i. M)"
  then obtain J :: "nat set" and F where J: "J \<noteq> {}" "finite J" "F \<in> J \<rightarrow> sets M"
    and X: "X = prod_emb UNIV (\<lambda>_. M) J (Pi\<^sub>E J F)"
    unfolding prod_algebra_def by auto
  then have Pi_F: "finite J" "Pi\<^sub>E J F \<in> sets (Pi\<^sub>M J (\<lambda>_. M))"
    by (auto intro: sets_PiM_I_finite)

  define n where "n = (LEAST n. \<forall>i\<ge>n. i \<notin> J)"
  have J_le_n: "J \<subseteq> {0..<n}"
    unfolding n_def
    using \<open>finite J\<close>
    apply -
    apply (rule LeastI2[of _ "Suc (Max J)"])
     apply (auto simp: Suc_le_eq not_le[symmetric])
    done

  have C: "(\<lambda>x. Ionescu_Tulcea.C (K' p x) (\<lambda>_. M) 0 n (\<lambda>x. undefined)) \<in> 
    prob_algebra Ms \<rightarrow>\<^sub>M subprob_algebra (Pi\<^sub>M {0..<n} (\<lambda>_. M))"
    apply (induction n)
     apply (subst measurable_cong)
      apply (rule Ionescu_Tulcea.C.simps(1)[OF IT_K', where p1 = p, OF p])
      apply assumption
     apply (rule measurable_compose[OF _ return_measurable])
     apply simp
    apply (subst measurable_cong)
     apply (rule Ionescu_Tulcea.C.simps[OF IT_K', where p1 = p, OF p])
     apply assumption
    apply (rule measurable_bind')
     apply assumption
    apply (subst measurable_cong)
  proof -
    fix n :: nat and w assume "w \<in> space (prob_algebra Ms \<Otimes>\<^sub>M Pi\<^sub>M {0..<n} (\<lambda>_. M))"
    then show "(case w of (x, xa) \<Rightarrow> Ionescu_Tulcea.eP (K' p x) (\<lambda>_. M) (0 + n) xa) =
      (case w of (x, xa) \<Rightarrow> distr (K' p x n xa) (\<Pi>\<^sub>M i\<in>{0..<Suc n}. M) (fun_upd xa n))"
      by (auto simp: p space_pair_measure Ionescu_Tulcea.eP_def[OF IT_K'] split: prod.split)
  next
    fix n 
    show "(\<lambda>w. case w of (x, xa) \<Rightarrow> distr (K' p x n xa) (Pi\<^sub>M {0..<Suc n} (\<lambda>i. M)) (fun_upd xa n))
        \<in> prob_algebra Ms \<Otimes>\<^sub>M Pi\<^sub>M {0..<n} (\<lambda>_. M) \<rightarrow>\<^sub>M subprob_algebra (Pi\<^sub>M {0..<Suc n} (\<lambda>_. M))"
      unfolding K'_def
      apply measurable
      apply (rule measurable_distr2[where M=M])
       apply (rule measurable_PiM_single')
        apply (simp add: split_beta')
      subgoal
        for i by (cases "i = n") auto
      subgoal 
        by (auto simp: split_beta' PiE_iff extensional_def Pi_iff space_pair_measure space_PiM)
      apply (rule measurable_bind[where N = Ms])
      using measurable_prob_algebraD apply measurable
       apply (simp; fail)
      using measurable_prob_algebraD p by measurable
  qed

  have "(\<lambda>a. emeasure (lim_sequence p a) X) \<in> borel_measurable (prob_algebra Ms) \<longleftrightarrow>
    (\<lambda>a. emeasure (Ionescu_Tulcea.CI (K' p a) (\<lambda>_. M) J) (Pi\<^sub>E J F)) \<in> 
      borel_measurable (prob_algebra Ms)"
    unfolding X using J Pi_F by (intro p measurable_cong emeasure_lim_sequence_emb) auto
  also have "\<dots>"
    apply (intro measurable_compose[OF _ measurable_emeasure_subprob_algebra[OF Pi_F(2)]])
    apply (subst measurable_cong)
     apply (subst Ionescu_Tulcea.CI_def[OF IT_K', of p, OF p])
      apply assumption
     apply (subst Ionescu_Tulcea.up_to_def[OF IT_K', of p, OF p])
    unfolding n_def[symmetric]
    using C measurable_compose[OF _ measurable_distr[OF measurable_restrict_subset[OF J_le_n]]]
    by blast+
  finally show "(\<lambda>a. emeasure (lim_sequence p a) X) \<in> borel_measurable (prob_algebra Ms)" .
qed

lemma lim_sequence_aux[measurable]: 
  assumes p: "is_policy p"
  assumes f : "\<And>x. x \<in> space M \<Longrightarrow> is_policy (f x)" 
  assumes f': "\<And>n. (\<lambda>x. f (fst (fst x)) n (snd (fst x), snd x)) \<in> 
    (M \<Otimes>\<^sub>M Pi\<^sub>M {0..<n} (\<lambda>_. M)) \<Otimes>\<^sub>M Ms \<rightarrow>\<^sub>M prob_algebra Ma"
  assumes gm: "g \<in> M \<rightarrow>\<^sub>M prob_algebra Ms"
  shows "(\<lambda>x. lim_sequence (f x) (g x)) \<in> M \<rightarrow>\<^sub>M prob_algebra (Pi\<^sub>M UNIV (\<lambda>_. M))"
proof (intro measurable_prob_algebra_generated
    [OF sets_PiM Int_stable_prod_algebra prod_algebra_sets_into_space])
  fix a assume a[simp]: "a \<in> space M"
  have g: "\<And>x. x \<in> space M \<Longrightarrow> g x \<in> space (prob_algebra Ms)"
    by (meson gm measurable_space)
  interpret Ionescu_Tulcea "K' (f a) (g a)" "\<lambda>_. M"
    using IT_K' p
    using f[OF \<open>a \<in> space M\<close>] g by measurable
  have p': "is_policy (f a)"
    using \<open>a \<in> space M\<close> p f by auto
  have sp: 
    "space (lim_sequence (f a) (g a)) = prod_emb UNIV (\<lambda>_. M) {} (\<Pi>\<^sub>E j\<in>{}. space M)" 
    "space (CI {}) = {} \<rightarrow>\<^sub>E space M"
    using g a p' by (auto simp: space_lim_sequence p' space_PiM prod_emb_def PF.space_P)
  show "prob_space (lim_sequence (f a) (g a))"
    apply standard
    using PF.prob_space_P[THEN prob_space.emeasure_space_1, of "{}"]
    apply (simp add: p' p sp emeasure_lim_sequence_emb del: PiE_empty_domain)
    apply (subst emeasure_lim_sequence_emb)
    using g a p' apply auto
    by (metis sets.top space_PiM_empty)
  show "sets (lim_sequence (f a) (g a)) = sets (Pi\<^sub>M UNIV (\<lambda>i. M))"
    by (simp add: lim_sequence_def)
next
  fix X :: "(nat \<Rightarrow> 's \<times> 'a) set" assume "X \<in> prod_algebra UNIV (\<lambda>i. M)"
  then obtain J :: "nat set" and F where J: "J \<noteq> {}" "finite J" "F \<in> J \<rightarrow> sets M"
    and X: "X = prod_emb UNIV (\<lambda>_. M) J (Pi\<^sub>E J F)"
    unfolding prod_algebra_def by auto
  then have Pi_F: "finite J" "Pi\<^sub>E J F \<in> sets (Pi\<^sub>M J (\<lambda>_. M))"
    by (auto intro: sets_PiM_I_finite)

  define n where "n = (LEAST n. \<forall>i\<ge>n. i \<notin> J)"
  have J_le_n: "J \<subseteq> {0..<n}"
    unfolding n_def
    using \<open>finite J\<close>
    apply -
    apply (rule LeastI2[of _ "Suc (Max J)"])
    by (auto simp: Suc_le_eq not_le[symmetric])

  have g: "\<And>x. x \<in> space M \<Longrightarrow> g x \<in> space (prob_algebra Ms)"
    by (meson gm measurable_space)

  have C: "(\<lambda>x. Ionescu_Tulcea.C (K' (f x) (g x)) (\<lambda>_. M) 0 n (\<lambda>x. undefined)) \<in> 
    M \<rightarrow>\<^sub>M subprob_algebra (Pi\<^sub>M {0..<n} (\<lambda>_. M))"
    apply (induction n)
     apply (subst measurable_cong)
      apply (rule Ionescu_Tulcea.C.simps[OF IT_K'])
       apply (simp add: f)
    using g apply auto[1]
     apply (rule measurable_compose[OF _ return_measurable])
     apply simp
    apply (subst measurable_cong)
     apply (rule Ionescu_Tulcea.C.simps[OF IT_K'])
      apply (simp add: f)
    using g apply auto[1]
    apply (rule measurable_bind')
     apply assumption
    apply (subst measurable_cong)
  proof -
    fix n :: nat and w assume "w \<in> space (M \<Otimes>\<^sub>M Pi\<^sub>M {0..<n} (\<lambda>_. M))"
    then show "(case w of (x, xa) \<Rightarrow> Ionescu_Tulcea.eP (K' (f x) (g x)) (\<lambda>_. M) (0 + n) xa) =
      (case w of (x, xa) \<Rightarrow> distr (K' (f x) (g x) n xa) (\<Pi>\<^sub>M i\<in>{0..<Suc n}. M) (fun_upd xa n))"
      by (auto simp: IT_K' Ionescu_Tulcea.eP_def f g space_ma p space_pair_measure 
          Ionescu_Tulcea.eP_def[OF IT_K'])
  next
    fix n 
    show "(\<lambda>w. case w of (x, xa) \<Rightarrow> distr ((K' (f x) (g x)) n xa) (Pi\<^sub>M {0..<Suc n} (\<lambda>i. M)) 
      (fun_upd xa n)) \<in> M \<Otimes>\<^sub>M Pi\<^sub>M {0..<n} (\<lambda>_. M) \<rightarrow>\<^sub>M subprob_algebra (Pi\<^sub>M {0..<Suc n} (\<lambda>_. M))"
      unfolding K'_def
      apply measurable
      apply (rule measurable_distr2[where M=M])
       apply (rule measurable_PiM_single')
        apply (simp add: split_beta')
      subgoal for i by (cases "i = n") auto
      subgoal by (auto simp: split_beta' PiE_iff extensional_def Pi_iff space_pair_measure space_PiM)
      apply (intro measurable_bind[where N = Ms])
       apply (subst measurable_pair_swap_iff)
      subgoal
        apply (cases n) apply auto apply measurable
        using measurable_snd'' measurable_fst''
         apply (simp add: measurable_snd'' gm measurable_prob_algebraD)
        apply (rule measurable_prob_algebraD)
        by measurable
      unfolding Suc_policy_def
      apply (intro measurable_bind[where N = Ma])
       apply (intro measurable_prob_algebraD)
      using f' by auto
  qed

  have p': "\<And>a. a \<in> space M \<Longrightarrow> is_policy (f a)"
    using f by auto
  have "(\<lambda>a. emeasure (lim_sequence (f a) (g a)) X) \<in> borel_measurable M \<longleftrightarrow>
    (\<lambda>a. emeasure (Ionescu_Tulcea.CI (K' (f a) (g a)) (\<lambda>_. M) J) (Pi\<^sub>E J F)) \<in> borel_measurable M"
    unfolding X using J Pi_F
    apply (intro p p' measurable_cong emeasure_lim_sequence_emb)
    by (auto simp add: g f K space_pair_measure)
  also have "..."
    apply (intro measurable_compose[OF _ measurable_emeasure_subprob_algebra[OF Pi_F(2)]])
    apply (subst measurable_cong[where g = "(\<lambda>w. distr (Ionescu_Tulcea.C (K' (f w) (g w)) 
      (\<lambda>_. M) 0 n (\<lambda>x. undefined)) (Pi\<^sub>M J (\<lambda>_. M)) (\<lambda>f. restrict f J))"])
     apply (subst Ionescu_Tulcea.CI_def[OF IT_K'])
    using f g p' apply auto 
  proof -
    fix w
    assume "w \<in> space M"
    show "distr (Ionescu_Tulcea.C (K' (f w) (g w)) (\<lambda>_. M) 0 (Ionescu_Tulcea.up_to J) 
      (\<lambda>x. undefined)) (Pi\<^sub>M J (\<lambda>_. M)) (\<lambda>f. restrict f J) =
         distr (Ionescu_Tulcea.C (K' (f w) (g w)) (\<lambda>_. M) 0 n (\<lambda>x. undefined)) 
          (Pi\<^sub>M J (\<lambda>_. M)) (\<lambda>f. restrict f J)"
      apply (subst Ionescu_Tulcea.up_to_def[OF IT_K'[where p = "Suc_policy p w", where x = "K w"]])
      using p' using \<open>w \<in> space M\<close>
      using p apply blast
       apply (simp add: \<open>w \<in> space M\<close> prob_space_K sets_K space_prob_algebra)
      unfolding n_def[symmetric]
      by (rule refl)
  next
    show "(\<lambda>w. distr (Ionescu_Tulcea.C (K' (f w) (g w)) (\<lambda>_. M) 0 n (\<lambda>x. undefined)) (Pi\<^sub>M J (\<lambda>_. M)) 
      (\<lambda>f. restrict f J)) \<in> M \<rightarrow>\<^sub>M subprob_algebra (Pi\<^sub>M J (\<lambda>_. M))"
      apply (rule measurable_compose[OF _ measurable_distr[OF measurable_restrict_subset[OF J_le_n]]])
      using C by blast qed
  thus "(\<lambda>a. emeasure (lim_sequence (f a) (g a)) X) \<in> borel_measurable M"
    using calculation by blast
qed

lemma lim_sequence_Suc_return[measurable]: 
  assumes p: "is_policy p"
  assumes s: "s \<in> space Ms"
  shows "(\<lambda>x. lim_sequence (Suc_policy p (s, snd x)) (return Ms (fst x))) \<in> 
    M \<rightarrow>\<^sub>M prob_algebra (Pi\<^sub>M UNIV (\<lambda>_. M))"
  apply (intro lim_sequence_aux[OF p])
    apply (meson is_policy_Suc_policy measurable_snd measurable_space p s space_ma)
  using p
  unfolding Suc_policy_def
   apply measurable
    apply simp
    apply (rule measurable_compose[where f= fst, where N = "(M \<Otimes>\<^sub>M Pi\<^sub>M {0..<_} (\<lambda>_. M))"])
     apply measurable
  by (auto intro: measurable_PiM_single' 
      simp: s space_pair_measure space_PiM PiE_iff extensional_def split: nat.split)

lemma lim_sequence_Suc_K[measurable]: 
  assumes p: "is_policy p"
  shows "(\<lambda>x. lim_sequence (Suc_policy p x) (K x)) \<in> M \<rightarrow>\<^sub>M prob_algebra (Pi\<^sub>M UNIV (\<lambda>_. M))"
  apply (intro lim_sequence_aux[OF p])
  using p apply blast
  using p by measurable

subsection \<open>Iteration Rule\<close>
lemma step_C:
  assumes x: "x \<in> space (prob_algebra Ms)" and p: "is_policy p"
  shows "Ionescu_Tulcea.C (K' p x) (\<lambda>_. M) 0 1 (\<lambda>_. undefined) \<bind> 
    Ionescu_Tulcea.C (K' p x) (\<lambda>_. M) 1 n =
    K0 p x \<bind> (\<lambda>xa. Ionescu_Tulcea.C (K' p x) (\<lambda>_. M) 1 n (case_nat xa (\<lambda>_. undefined)))"
proof -
  interpret Ionescu_Tulcea "K' p x" "\<lambda>_. M"
    using IT_K'[OF p x] .

  have [simp]: "space (K0 p x) \<noteq> {}"
    using space_K0[OF p x] x by auto

  have [simp]: "((\<lambda>_. undefined)(0 := x::('s \<times> 'a))) = case_nat x (\<lambda>_. undefined)" for x
    by (auto simp: fun_eq_iff split: nat.split)

  have "C 0 1 (\<lambda>_. undefined) \<bind> C 1 n = eP 0 (\<lambda>_. undefined) \<bind> C 1 n"
    using measurable_eP[of 0] measurable_C[of 1 n, measurable del]
    by (simp add: bind_return[where N="Pi\<^sub>M {0} (\<lambda>_. M)"])
  also have "\<dots> = K0 p x \<bind> (\<lambda>xa. C 1 n (case_nat xa (\<lambda>_. undefined)))"
    using measurable_C[of 1 n, measurable del] x[THEN sets_K0[OF p]]
    unfolding eP_def
    apply measurable
    apply (subst bind_distr[where K = "Pi\<^sub>M {0..<Suc n} (\<lambda>_. M)"])
       apply simp
       apply measurable
       apply (simp add: measurable_ident_sets sets_P)
      apply (metis measurable_C One_nat_def plus_1_eq_Suc)
     apply (simp add: prob_space.not_empty prob_space_P)
    apply auto using p x unfolding K'_def K0_def by auto
  finally show 
    "C 0 1 (\<lambda>_. undefined) \<bind> C 1 n = K0 p x \<bind> (\<lambda>xa. C 1 n (case_nat xa (\<lambda>_. undefined)))" .
qed

lemma lim_sequence_eq:
  assumes x: "x \<in> space (prob_algebra Ms)" assumes p: "is_policy p"
  shows "lim_sequence p x = 
    K0 p x \<bind> (\<lambda>y. distr (lim_sequence (Suc_policy p y) (K y)) (\<Pi>\<^sub>M _\<in>UNIV. M) (case_nat y))"
    (is "_ = ?B p x")
proof (rule measure_eqI_PiM_infinite)
  show "sets (lim_sequence p x) = sets (\<Pi>\<^sub>M j\<in>UNIV. M)"
    using x p by (rule sets_lim_sequence)
  have [simp]: "space (K' p x 0 (\<lambda>n. undefined)) \<noteq> {}"
    using p
    using IT_K' Ionescu_Tulcea.non_empty Ionescu_Tulcea.space_P x by fastforce
  show "sets (?B p x) = sets (Pi\<^sub>M UNIV (\<lambda>j. M))"
    using p x M_ne_policy space_K0 by auto

  interpret lim_sequence: prob_space "lim_sequence p x"
    using lim_sequence x p by (auto simp: measurable_restrict_space2_iff prob_algebra_def)
  show "finite_measure (lim_sequence p x)"
    by (rule lim_sequence.finite_measure)

  interpret Ionescu_Tulcea "K' p x" "\<lambda>_. M"
    using  IT_K'[OF p x] .

  let ?U = "\<lambda>_::nat. undefined :: ('s \<times> 'a)"

  fix J :: "nat set" and F'
  assume J: "finite J" "\<And>i. i \<in> J \<Longrightarrow> F' i \<in> sets M"

  define n where "n = (if J = {} then 0 else Max J)"
  define F where "F i = (if i \<in> J then F' i else space M)" for i
  then have F[simp, measurable]: "F i \<in> sets M" for i
    using J by auto
  have emb_eq: "PF.emb UNIV J (Pi\<^sub>E J F') = PF.emb UNIV {0..<Suc n} (Pi\<^sub>E {0..<Suc n} F)"
  proof cases
    assume "J = {}" then show ?thesis
      by (auto simp add: n_def F_def[abs_def] prod_emb_def PiE_def)
  next
    assume "J \<noteq> {}" then show ?thesis
      by (auto simp: prod_emb_def PiE_iff F_def n_def less_Suc_eq_le \<open>finite J\<close> split: if_split_asm)
  qed

  have "emeasure (lim_sequence p x) (PF.emb UNIV J (Pi\<^sub>E J F')) = 
    emeasure (C 0 (Suc n) ?U) (Pi\<^sub>E {0..<Suc n} F)"
    using x p unfolding emb_eq 
    by (rule emeasure_lim_sequence_emb_I0o) (auto intro!: sets_PiM_I_finite)
  also have "C 0 (Suc n) ?U = K0 p x \<bind> (\<lambda>y. C 1 n (case_nat y ?U))"
    using split_C[of ?U 0 "Suc 0" n] step_C[OF x p] by simp
  also have "emeasure (K0 p x \<bind> (\<lambda>y. C 1 n (case_nat y ?U))) (Pi\<^sub>E {0..<Suc n} F) =
    (\<integral>\<^sup>+y. C 1 n (case_nat y ?U) (Pi\<^sub>E {0..<Suc n} F) \<partial>K0 p x)"
    using measurable_C[of 1 n, measurable del] sets_K0[OF p x] F x p
    apply (intro emeasure_bind[OF  _ measurable_compose[OF _ measurable_C]])
    using non_empty space_K0 apply blast
    by (auto cong: measurable_cong_sets intro!: measurable_PiM_single' split: nat.split_asm)
  also have "\<dots> = (\<integral>\<^sup>+y. distr (lim_sequence (Suc_policy p y) (K y)) 
    (Pi\<^sub>M UNIV (\<lambda>j. M)) (case_nat y) (PF.emb UNIV J (Pi\<^sub>E J F')) \<partial>K0 p x)"
  proof (intro nn_integral_cong)
    fix y assume "y \<in> space (K0 p x)"
    then have y: "y \<in> space M"
      using x p
      using space_K0 by blast
    then interpret y: Ionescu_Tulcea "K' (Suc_policy p y) (K y)" "\<lambda>_. M"
      apply (intro IT_K')
       apply (metis  is_policy_Suc_policy p)
      by (meson K measurable_space)
    have "fst y \<in> space Ms"
      by (meson measurable_fst measurable_space y)
    let ?y = "case_nat y"
    have [simp]: "?y ?U \<in> space (Pi\<^sub>M {0} (\<lambda>i. M))"
      using y by (auto simp: space_PiM PiE_iff extensional_def split: nat.split)
    have yM[measurable]: "?y \<in> Pi\<^sub>M {0..<m} (\<lambda>_. M) \<rightarrow>\<^sub>M Pi\<^sub>M {0..<Suc m} (\<lambda>i. M)" for m
      using y 
      apply (intro measurable_PiM_single') 
      by(auto simp: space_PiM PiE_iff extensional_def split: nat.split)
    have y': "?y ?U \<in> space (Pi\<^sub>M {0..<1} (\<lambda>i. M))"
      by (simp add: space_PiM PiE_def y extensional_def split: nat.split)

    have eq1: "?y -` Pi\<^sub>E {0..<Suc n} F \<inter> space (Pi\<^sub>M {0..<n} (\<lambda>_. M)) =
        (if y \<in> F 0 then Pi\<^sub>E {0..<n} (F\<circ>Suc) else {})"
      unfolding set_eq_iff using y sets.sets_into_space[OF F]
      by (auto simp: space_PiM PiE_iff extensional_def Ball_def split: nat.split nat.split_asm)

    have eq2: "?y -` PF.emb UNIV {0..<Suc n} (Pi\<^sub>E {0..<Suc n} F) \<inter> space (Pi\<^sub>M UNIV (\<lambda>_. M)) =
        (if y \<in> F 0 then PF.emb UNIV {0..<n} (Pi\<^sub>E {0..<n} (F\<circ>Suc)) else {})"
      unfolding set_eq_iff using y sets.sets_into_space[OF F]
      by (auto simp: space_PiM PiE_iff prod_emb_def extensional_def Ball_def split: nat.splits)

    let ?I = "indicator (F 0) y"    
    have "fst y \<in> space Ms"
      using y by (meson measurable_fst measurable_space)
    have "C 1 n (?y ?U) = distr (y.C 0 n ?U) (\<Pi>\<^sub>M i\<in>{0..<Suc n}. M) ?y"
    proof (induction n)
      case (Suc m)

      have "C 1 (Suc m) (?y ?U) = distr (y.C 0 m ?U) (Pi\<^sub>M {0..<Suc m} (\<lambda>i. M)) ?y \<bind> eP (Suc m)"
        using Suc by simp
      also have "\<dots> = y.C 0 m ?U \<bind> (\<lambda>x. eP (Suc m) (?y x))"
        apply (intro bind_distr[where K="Pi\<^sub>M {0..<Suc (Suc m)} (\<lambda>_. M)"]) 
        by (simp_all add: y y.space_C y.sets_C cong: measurable_cong_sets)
      also have "\<dots> = y.C 0 m ?U \<bind> (\<lambda>x. distr (y.eP m x) (Pi\<^sub>M {0..<Suc (Suc m)} (\<lambda>i. M)) ?y)"
      proof (intro bind_cong refl)
        fix \<omega>' assume \<omega>': "\<omega>' \<in> space (y.C 0 m ?U)"
        moreover have "K' p x (Suc m) (?y \<omega>') = K' (Suc_policy p y) (K y) m \<omega>'"
          unfolding K'_def Suc_policy_def apply simp by (auto split: nat.splits)
        ultimately show "eP (Suc m) (?y \<omega>') = distr (y.eP m \<omega>') (Pi\<^sub>M {0..<Suc (Suc m)} (\<lambda>i. M)) ?y"
          unfolding eP_def y.eP_def
          apply (subst distr_distr)
          by  (auto simp: y.space_C y.sets_P split: nat.split cong: measurable_cong_sets
              intro!: distr_cong measurable_fun_upd[where J="{0..<m}"])
      qed
      also have "\<dots> = distr (y.C 0 m ?U \<bind> y.eP m) (Pi\<^sub>M {0..<Suc (Suc m)} (\<lambda>i. M)) ?y"
        apply (intro distr_bind[symmetric, OF _ _ yM]) 
        by (auto simp: y.space_C y.sets_C cong: measurable_cong_sets)
      finally show ?case
        by simp
    qed (use y in \<open>simp add: PiM_empty distr_return\<close>)
    then have "C 1 n (case_nat y ?U) (Pi\<^sub>E {0..<Suc n} F) =
      (distr (y.C 0 n ?U) (\<Pi>\<^sub>M i\<in>{0..<Suc n}. M) ?y) (Pi\<^sub>E {0..<Suc n} F)" by simp
    also have "\<dots> = ?I * y.C 0 n ?U (Pi\<^sub>E {0..<n} (F \<circ> Suc))"
      by (subst emeasure_distr) (auto simp: y.sets_C y.space_C eq1 cong: measurable_cong_sets)
    also have 
      "\<dots> = ?I * lim_sequence (Suc_policy p y) (K y) (PF.emb UNIV {0..<n} (Pi\<^sub>E {0..<n} (F \<circ> Suc)))"
      using y sets_PiM_I_finite
      apply (subst emeasure_lim_sequence_emb_I0o)
      by (auto simp add:  p sets_PiM_I_finite)
    also have "\<dots> = distr (lim_sequence (Suc_policy p y) (K y)) (Pi\<^sub>M UNIV (\<lambda>j. M)) ?y
      (PF.emb UNIV {0..<Suc n} (Pi\<^sub>E {0..<Suc n} F))"
      using y 
      apply (subst emeasure_distr) 
        apply (simp_all add: eq2 space_lim_sequence)
       apply measurable
       apply (simp add: lim_sequence_def measurable_ident_sets)
      using eq2 apply (subst space_lim_sequence)
        apply (meson K measurable_space)
       apply (metis is_policy_Suc_policy p)
      by auto
    finally show "emeasure (C 1 n (case_nat y (\<lambda>_. undefined))) (Pi\<^sub>E {0..<Suc n} F) = 
      emeasure (distr (lim_sequence (Suc_policy p y) (K y)) (Pi\<^sub>M UNIV (\<lambda>j. M)) (case_nat y)) 
        (y.PF.emb UNIV J (Pi\<^sub>E J F'))"
      unfolding emb_eq .
  qed
  also have "\<dots> = emeasure (K0 p x \<bind> (\<lambda>y. distr (lim_sequence (Suc_policy p y) (K y)) 
    (Pi\<^sub>M UNIV (\<lambda>j. M)) (case_nat y))) (PF.emb UNIV J (Pi\<^sub>E J F'))"
    using J
    apply (subst emeasure_bind[where N="PiM UNIV (\<lambda>_. M)"])
    using non_empty p x space_K0 apply blast
      apply auto
    using sets_K0[OF \<open>is_policy p\<close> \<open>x \<in> space (prob_algebra Ms)\<close>] measurable_cong_sets
    apply (auto simp: sets_K x cong: measurable_cong_sets
        intro!: measurable_distr2[OF _ measurable_prob_algebraD[OF lim_sequence]])
    apply (intro measurable_distr2[where M = "PiM UNIV (\<lambda>_. M)"])
    using lim_sequence_Suc_K measurable_prob_algebraD p by measurable
  finally show "emeasure (lim_sequence p x) (PF.emb UNIV J (Pi\<^sub>E J F')) = 
    emeasure (K0 p x \<bind> (\<lambda>y. distr (lim_sequence (Suc_policy p y) (K y)) (Pi\<^sub>M UNIV (\<lambda>j. M))
      (case_nat y))) (PF.emb UNIV J (Pi\<^sub>E J F'))".
qed


lemma AE_lim_sequence:
  assumes p: "is_policy p" 
    and x[simp]: "x \<in> space (prob_algebra Ms)" and P[measurable]: "Measurable.pred (\<Pi>\<^sub>M i\<in>UNIV. M) P"
  shows "(AE \<omega> in lim_sequence p x. P \<omega>) \<longleftrightarrow>  
    (AE y in K0 p x. AE \<omega> in lim_sequence (Suc_policy p y) (K y). P (case_nat y \<omega>))"
proof -
  have aux: "lim_sequence p x = K0 p x \<bind> (\<lambda>sa. distr (lim_sequence (Suc_policy p sa) (K sa)) 
    (Pi\<^sub>M UNIV (\<lambda>j. M)) (case_nat sa))"
    using lim_sequence_eq[OF x p] by simp
  show ?thesis
    using p 
    apply (subst aux)
    apply (subst AE_bind)
      apply (rule measurable_prob_algebraD)
      apply measurable
          apply blast
    using x apply measurable
       apply (simp add: measurable_ident_sets p sets_K0)
      apply (intro measurable_split_replace)
      apply (rule measurable_Pair_compose_split[of _ "prob_algebra Ms", where g="\<lambda>_. x"])
        apply measurable
      apply (simp add: measurable_ident_sets sets_K0[OF p x])
     apply measurable
    apply (intro AE_cong)
    apply (subst AE_distr_iff)
    using x apply auto
    apply measurable
    by (metis K is_policy_Suc_policy measurable_ident_sets measurable_space p sets_lim_sequence)
qed

subsection \<open>Stream Space of the MDP\<close>
definition lim_stream :: "('s, 'a) pol \<Rightarrow> 's measure \<Rightarrow> ('s \<times> 'a) stream measure"
  where
    "lim_stream p x = distr (lim_sequence p x) (stream_space M) to_stream"

lemma space_lim_stream: "space (lim_stream p x) = streams (space M)"
  unfolding lim_stream_def by (simp add: space_stream_space)

lemma sets_lim_stream[measurable_cong]: "sets (lim_stream p x) = sets (stream_space M)"
  unfolding lim_stream_def by simp

lemma lim_stream[measurable]: 
  assumes "is_policy p" 
  shows "lim_stream p \<in> prob_algebra Ms \<rightarrow>\<^sub>M prob_algebra (stream_space M)"
  unfolding lim_stream_def[abs_def] 
  apply (intro measurable_distr_prob_space2[OF lim_sequence]) 
  using assms by auto

lemma lim_stream_Suc[measurable]:
  assumes p: "is_policy p"
  shows "(\<lambda>xa. lim_stream (Suc_policy p xa) (K xa)) \<in> M \<rightarrow>\<^sub>M prob_algebra (stream_space M)"
  unfolding lim_stream_def[abs_def] 
  apply (intro measurable_distr_prob_space2[OF lim_sequence_Suc_K]) 
  using p by auto

lemma space_stream_space_M_ne: "x \<in> space M \<Longrightarrow> space (stream_space M) \<noteq> {}"
  using sconst_streams[of x "space M"] by (auto simp: space_stream_space)

lemma prob_space_lim_stream[intro]: 
  assumes "is_policy p" "x \<in> space (prob_algebra Ms)" 
  shows "prob_space (lim_stream p x)"
  by (metis (no_types, lifting) space_prob_algebra measurable_space assms lim_stream mem_Collect_eq)

lemma prob_space_step: 
  assumes "is_policy p" "x \<in> space M"
  shows "prob_space (lim_stream (Suc_policy p x) (K x))"
  by (auto simp: assms K_in_space is_policy_Suc_policy)

lemma lim_stream_eq:
  assumes p: "is_policy p"
  assumes x: "x \<in> space (prob_algebra Ms)"
  shows "lim_stream p x = do {
    y \<leftarrow> K0 p x;
    \<omega> \<leftarrow> lim_stream (Suc_policy p y) (K y); 
    return (stream_space M) (y ## \<omega>)
  }"
  unfolding lim_stream_def lim_sequence_eq[OF x p]
proof (subst distr_bind[OF _ _ measurable_to_stream])
  show "(\<lambda>y. distr (lim_sequence (Suc_policy p y) (K y)) (Pi\<^sub>M UNIV (\<lambda>j. M)) (case_nat y)) \<in> 
    K0 p x \<rightarrow>\<^sub>M subprob_algebra (Pi\<^sub>M UNIV (\<lambda>i. M))"
    apply (intro measurable_prob_algebraD measurable_distr_prob_space2[where M="Pi\<^sub>M UNIV (\<lambda>j. M)"])
    using lim_sequence_Suc_K[OF p] sets_K0[OF p x] measurable_cong_sets 
     apply blast
    apply (subst measurable_cong_sets)
    using \<open>sets (K0 p x) = sets M\<close> 
    by auto
next 
  show "space (K0 p x) \<noteq> {}"
    using x p prob_space.not_empty prob_space_K0
    by blast
next 
  show "K0 p x \<bind> (\<lambda>x. distr (distr (lim_sequence (Suc_policy p x) (K x)) (Pi\<^sub>M UNIV (\<lambda>j. M)) 
    (case_nat x)) (stream_space M) to_stream) = K0 p x \<bind> (\<lambda>y. distr (lim_sequence (Suc_policy p y)
      (K y)) (stream_space M) to_stream \<bind> (\<lambda>\<omega>. return (stream_space M) (y ## \<omega>)))"
  proof (intro bind_cong refl, subst distr_distr)
    show "to_stream \<in> Pi\<^sub>M UNIV (\<lambda>j. M) \<rightarrow>\<^sub>M stream_space M"
      by measurable
  next 
    show "\<And>xa. xa \<in> space (K0 p x) \<Longrightarrow> 
      case_nat xa \<in> lim_sequence (Suc_policy p xa) (K xa) \<rightarrow>\<^sub>M Pi\<^sub>M UNIV (\<lambda>j. M)"
      apply measurable 
      using p x
      by (auto intro!: measurable_ident_sets sets_lim_sequence intro: measurable_space)
  next 
    show "\<And>xa. xa \<in> space (K0 p x) \<Longrightarrow>
      distr (lim_sequence (Suc_policy p xa) (K xa)) (stream_space M) (to_stream \<circ> case_nat xa) =
      distr (lim_sequence (Suc_policy p xa) (K xa)) (stream_space M) to_stream \<bind> 
        (\<lambda>\<omega>. return (stream_space M) (xa ## \<omega>))"
      using p x apply simp
      apply (subst bind_return_distr')
        apply (simp add: p space_stream_space_M_ne x)
       apply (auto simp: sets_lim_sequence x cong: measurable_cong_sets intro!: distr_cong)[1]
      apply (subst distr_distr)
        apply measurable
       apply (auto intro!: measurable_ident_sets sets_lim_sequence intro: measurable_space)[1]
      by (auto simp: to_stream_nat_case intro!: distr_cong)
  qed
qed

lemma lim_stream_Suc_policy_K0[measurable]: 
  assumes "is_policy p" "x \<in> space (prob_algebra Ms)" 
  shows "(\<lambda>x. lim_stream (Suc_policy p x) (K x)) \<in> K0 p x \<rightarrow>\<^sub>M prob_algebra (stream_space M)"
  by (auto simp: assms sets_K0 cong: measurable_cong_sets)

lemma AE_lim_stream:
  assumes p[simp]: "is_policy p" 
    and x[simp]: "x \<in> space (prob_algebra Ms)" 
    and P[measurable]: "Measurable.pred (stream_space M) P"
  shows "(AE \<omega> in lim_stream p x. P \<omega>) \<longleftrightarrow> 
    (AE y in K0 p x. AE \<omega> in lim_stream (Suc_policy p y) (K y). P (y ## \<omega>))"
  unfolding lim_stream_eq[OF p x]
  apply (subst AE_bind[where B = "stream_space M"])
    apply (intro measurable_bind[where N = "stream_space M"])
  using p x apply measurable[1] using measurable_prob_algebraD apply measurable[1]
    apply measurable
     apply (intro measurable_ident_sets) 
  using sets_K0 apply auto[1]
    apply measurable
  apply (intro AE_cong)
  apply (subst AE_bind[where B = "stream_space M"])
  using P apply measurable
    apply (simp add: measurable_ident_sets sets_lim_stream)
  by (auto simp add: lim_stream_def stream_space_Stream intro!: AE_cong AE_return)

lemma emeasure_lim_stream:
  assumes p: "is_policy p"
  assumes x[measurable, simp]: "x \<in> space (prob_algebra Ms)" 
    and A[measurable, simp]: "A' \<in> sets (stream_space M)"
  shows "lim_stream p x A' = (\<integral>\<^sup>+y. emeasure (lim_stream (Suc_policy p y) (K y))
    (((##) y) -` A' \<inter> space (stream_space M)) \<partial>K0 p x)"
  apply (subst lim_stream_eq[OF p x])
  apply (subst emeasure_bind[OF _ _ A])
  using M_ne_policy p space_K0 x apply blast
  using p x measurable_prob_algebraD apply measurable
    apply (simp add: measurable_ident_sets p sets_K0)
   apply measurable
  using p apply (auto simp: sets_K0 intro: measurable_ident_sets)[1]
   apply measurable
  apply (intro nn_integral_cong)
  apply (subst bind_return_distr')
    apply (metis p space_K0 space_lim_stream space_stream_space space_stream_space_M_ne x)
  using measurable_ident_sets sets_lim_stream space_lim_stream p
  by (auto simp: space_stream_space emeasure_distr cong: measurable_cong_sets)

lemma measurable_return_Suc[measurable]: 
  assumes "is_policy p" "x \<in>space (prob_algebra Ms)"
  shows "(\<lambda>(ya, y). return (stream_space M) (ya ## y)) \<in> 
    K0 p x \<Otimes>\<^sub>M stream_space M \<rightarrow>\<^sub>M prob_algebra (stream_space M)"
  apply measurable
   apply (intro measurable_ident_sets)
  using sets_K0 assms
  by auto

lemma measurable_ident_Suc[measurable]: 
  "(\<lambda>x. x) \<in> lim_stream (Suc_policy p x) (K x) \<rightarrow>\<^sub>M stream_space M"
  by (simp add: measurable_ident_sets sets_lim_stream)


subsection \<open>Integral decomposition of the trace space\<close>

lemma integral_lim_stream:
  fixes f :: "('s \<times> 'a) stream \<Rightarrow> real"
  assumes p[simp]: "is_policy p"
  assumes x[simp]: "x \<in> space (prob_algebra Ms)"
  assumes f_bounded: "\<And>x. \<bar>f x\<bar> \<le> B"
  assumes f: "f \<in> borel_measurable (stream_space M)"
  shows "(\<integral>t. f t \<partial>lim_stream p x) = 
    (\<integral>sa. \<integral>t'. f (sa##t') \<partial>lim_stream (Suc_policy p sa) (K sa) \<partial>K0 p x)"
  apply (subst lim_stream_eq[OF p x], subst integral_bind[OF f f_bounded, where B' = 1])
  subgoal
    apply (intro measurable_prob_algebraD)
    using  p x apply measurable
     apply (simp add: measurable_ident_sets sets_K0)
    using p x measurable_return_Suc by measurable
  subgoal  by (simp add: prob_space.finite_measure prob_space_K0)
  subgoal 
    apply (intro AE_I2)
    apply auto
    apply (intro 
        subprob_space.emeasure_space_le_1 prob_space_imp_subprob_space prob_space.prob_space_bind)
      apply (meson p prob_space_step)
     apply (intro AE_I2)
     apply (simp add: prob_space_return space_lim_stream space_stream_space)
    by measurable
  subgoal
    apply (intro Bochner_Integration.integral_cong[OF refl])
    apply (subst integral_bind[OF f f_bounded, where B' = 1])
       apply measurable[1]
      apply (auto simp add:prob_space.finite_measure prob_space_step; fail)
     apply (intro AE_I2)
     apply (simp add: space_lim_stream space_stream_space)
     apply (simp add: prob_space.measure_le_1 prob_space_return space_stream_space)
    apply (intro Bochner_Integration.integral_cong[OF refl])
    apply (subst integral_return)
      apply (simp add: space_lim_stream space_stream_space)
    using f by auto
  done

lemma nn_integral_lim_stream: 
  assumes p: "is_policy p"
  assumes x: "x \<in> space (prob_algebra Ms)"
  assumes f: "f \<in> borel_measurable (stream_space M)"
  shows "(\<integral>\<^sup>+t. f t \<partial>lim_stream p x) = 
    (\<integral>\<^sup>+sa. \<integral>\<^sup>+ t'. f (sa##t') \<partial>lim_stream (Suc_policy p sa) (K sa) \<partial>K0 p x)"
  apply (subst lim_stream_eq[OF p x])
  apply (subst nn_integral_bind[where B = "stream_space M"])
  using f apply simp
  subgoal 
    apply (intro measurable_bind[where N = "stream_space M"])
     apply (rule measurable_prob_algebraD)
    using p x lim_stream_Suc 
     apply measurable
     apply (simp add: measurable_ident_sets p sets_K0 x)
    apply (rule measurable_prob_algebraD)
    using return_measurable
    apply measurable
     apply (rule measurable_ident_sets)
    using p x by (auto simp: measurable_ident_sets sets_K0)
  apply (intro nn_integral_cong)
  apply (subst nn_integral_bind[where B = "stream_space M"])
  using f apply simp
  subgoal
    apply measurable
     apply (simp add: p x)
    by (simp add: measurable_ident_sets sets_lim_stream)
  apply auto
  using nn_integral_return
  apply (intro nn_integral_cong)
  apply (intro nn_integral_return)
  by (auto simp add: p f x space_stream_space space_lim_stream)

subsection \<open>Limit stream without initial distribution\<close>
lemma lim_stream_eq_return:
  assumes p: "is_policy p"
  assumes x: "x \<in> space Ms"
  shows "lim_stream p (return Ms x) = do {
    y \<leftarrow> p0 p x;
    \<omega> \<leftarrow> lim_stream (Suc_policy p (x,y)) (K (x,y)); 
    return (stream_space M) ((x,y) ## \<omega>)
  }"
  apply (subst lim_stream_eq)
  using p x apply auto
   apply (meson measurable_return_prob_space measurable_space)
  unfolding K0_def'
  apply (subst bind_return[where N = M])
    apply auto
  subgoal apply (intro measurable_bind[where N = Ma])
     apply (intro measurable_prob_algebraD)
    by auto
  apply (subst bind_assoc[where N = M, where R = "stream_space M"])
  subgoal using measurable_prob_algebraD return_measurable apply measurable
    by (simp add: measurable_ident_sets)
  subgoal
    apply (intro measurable_bind[where N = "stream_space M"])
    using measurable_prob_algebraD by measurable
  apply (intro bind_cong)
   apply blast
  apply (intro bind_return[where N = "stream_space M"])
  using \<open>\<lbrakk>is_policy p; x \<in> space Ms\<rbrakk> \<Longrightarrow> (\<lambda>y. lim_stream (Suc_policy p y) (K y) \<bind> 
    (\<lambda>\<omega>. return (stream_space M) (y ## \<omega>))) \<in> M \<rightarrow>\<^sub>M subprob_algebra (stream_space M)\<close> 
  by (simp_all add: space_prodI)

lemma "s0 \<in> space (prob_algebra Ms) \<Longrightarrow> sets s0 = sets Ms"
  by (auto simp add: space_prob_algebra)

lemma lim_stream_return:
  assumes s0: "s0 \<in> space (prob_algebra Ms)"
  assumes p: "is_policy p"
  shows "lim_stream p s0 = s0 \<bind> (\<lambda>s. lim_stream p (return Ms s))"
  apply (subst lim_stream_eq)
  using p apply blast
  using s0 apply blast
  unfolding K0_def'
  apply (subst bind_assoc[where N = "M", where R = "stream_space M"])
  subgoal apply measurable
    using p measurable_prob_algebraD apply measurable
    using s0 space_prob_algebra measurable_ident_sets
     apply (simp add: measurable_ident_sets space_prob_algebra)
    using return_measurable
    apply measurable
  proof -
    have "sets s0 = sets Ms"
      using s0
      by (auto simp add: space_prob_algebra)
    then show "(\<lambda>x. x) \<in> s0 \<Otimes>\<^sub>M Ma \<rightarrow>\<^sub>M Ms \<Otimes>\<^sub>M Ma " 
      apply (intro measurable_ident_sets)
      using s0  by measurable
  next show "snd \<in> s0 \<Otimes>\<^sub>M Ma \<rightarrow>\<^sub>M Ma" by auto
  qed
  subgoal 
    apply (intro measurable_bind[where N="stream_space M"])
     apply auto
    apply (intro measurable_prob_algebraD)
    using p by measurable
  apply (intro bind_cong)
   apply blast
  apply (subst lim_stream_eq[of p])
  subgoal using p by auto
  subgoal
    by (metis measurable_return_prob_space measurable_space s0 space_x0)
  unfolding K0_def'
  apply (subst bind_return[where N = M])
    apply auto
   apply (intro measurable_bind[where N = Ma])
    apply auto
   apply (intro measurable_prob_algebraD)
  using p s0 by auto

lemma [measurable]: 
  assumes "is_policy p" "s \<in> space Ms" 
  shows "(\<lambda>a. return M (s, a)) \<in> p0 p s \<rightarrow>\<^sub>M subprob_algebra M"
  using assms apply measurable
  by (simp add: assms measurable_ident_sets p0_sets)

lemma lim_stream_return_eq:
  assumes s : "s\<in> space Ms"
  assumes p: "is_policy p"
  shows
    "lim_stream p (return Ms s) = do {
  a \<leftarrow> p0 p s;
  s' \<leftarrow> K (s,a);
  w \<leftarrow> lim_stream (Suc_policy p (s,a)) (return Ms s');
  return (stream_space M) ((s,a)##w)}"
  apply (subst lim_stream_eq)
    apply fact
   apply (meson s measurable_return_prob_space measurable_space)
  unfolding K0_def'
  apply (subst bind_return[where N = M])
  subgoal apply (intro measurable_bind[where N = Ma]) 
     apply (intro measurable_prob_algebraD)
    using p by auto
   apply fact
  apply (subst bind_assoc[where N = M, where R = "stream_space M"])
  subgoal
    using s p apply measurable
    by (simp add: measurable_ident_sets p s)
  subgoal
    using p measurable_prob_algebraD
    by measurable
  apply (rule bind_cong)
   apply blast
  apply (subst bind_return[where N = "stream_space M"])
  subgoal using p measurable_prob_algebraD by measurable
  subgoal using s p
    by (simp add: space_prodI)
  apply (subst lim_stream_return)
    apply (metis measurable_K_act measurable_space p s space_policy' undefined_in_H0)
  using p s \<open>\<And>x. x \<in> space (p0 p s) \<Longrightarrow> (s, x) \<in> space M\<close> apply blast
  apply (subst bind_assoc[where N = "stream_space M", where R = "stream_space M"])
  subgoal using p s measurable_prob_algebraD apply measurable
    using \<open>\<And>x. x \<in> space (p0 p s) \<Longrightarrow> (s, x) \<in> space M\<close> p apply blast
    using \<open>\<And>x. x \<in> space (p0 p s) \<Longrightarrow> (s, x) \<in> space M\<close>
    by (metis measurable_return1 measurable_return_prob_space return_sets_cong sets_K)
  subgoal  using p s apply measurable apply auto
    using \<open>\<And>x. x \<in> space (p0 p s) \<Longrightarrow> (s, x) \<in> space M\<close> by blast
  by auto

definition "lim_stream' p s \<equiv> lim_stream p (return Ms s)"

lemma space_lim_stream': "space (lim_stream' p x) = streams (space M)"
  unfolding lim_stream'_def space_lim_stream ..

lemma lim_stream'_Suc_measurable[measurable]:
  assumes p: "is_policy p"
  assumes s: "s\<in>space Ms"
  shows "(\<lambda>(y,x). lim_stream' (Suc_policy p (s, x)) y) \<in> M  \<rightarrow>\<^sub>M prob_algebra (stream_space M)"
  unfolding lim_stream'_def lim_stream_def
  using p s by measurable

lemma lim_stream'_eq:
  assumes "is_policy p"
  assumes "s \<in> space Ms"
  shows "lim_stream' p s = do {
  a \<leftarrow> p0 p s;
  s' \<leftarrow> K (s,a);
  w \<leftarrow> lim_stream' (Suc_policy p (s,a)) s';
  return (stream_space M) ((s,a)##w)
}"
  unfolding lim_stream'_def
  using lim_stream_return_eq assms
  by auto

lemma lim_stream'_prob_space[intro]: "is_policy p \<Longrightarrow> s \<in> space Ms \<Longrightarrow> prob_space (lim_stream' p s)"
  by (metis lim_stream'_def measurable_return_prob_space measurable_space prob_space_lim_stream)

lemma lim_stream'_sets[measurable_cong]: 
  assumes "is_policy p" "s \<in> space Ms" 
  shows "sets (lim_stream' p s) = sets (stream_space M)"
  by (simp add: lim_stream'_def sets_lim_stream)

lemma nn_integral_lim_stream': 
  fixes f :: "('s \<times> 'a) stream \<Rightarrow> real" 
  assumes p: "is_policy p"
  assumes s: "s \<in> space Ms"
  assumes f[measurable]: "f \<in> borel_measurable (stream_space M)"
  shows "(\<integral>\<^sup>+t. f t \<partial>lim_stream' p s) = 
    (\<integral>\<^sup>+a. \<integral>\<^sup>+s'. \<integral>\<^sup>+t'. f ((s,a)##t') \<partial>lim_stream' (Suc_policy p (s,a)) s' \<partial>K (s,a) \<partial>p0 p s)"
  apply (subst lim_stream'_eq[OF p s])
  apply (subst nn_integral_bind[where B = "(stream_space M)"])
    apply measurable[1]
  using s p measurable_prob_algebraD apply measurable
    apply (simp add: measurable_ident_sets p p0_sets s)
  using s p  apply measurable
    apply (intro measurable_ident_sets)
    apply (simp add: p p0_sets s)
  using s p apply measurable
    apply (intro measurable_ident_sets)
    apply (simp add: p p0_sets s)
   apply measurable
  apply (intro nn_integral_cong)
  apply (subst nn_integral_bind[where B = "stream_space M"])
  using p s
    apply (auto simp: sets_K' intro!: measurable_prob_algebraD cong: measurable_cong_sets)
  apply (intro nn_integral_cong)
  apply (subst nn_integral_bind[where B = "stream_space M"])
    apply measurable
    apply (auto simp: lim_stream'_def measurable_ident_sets sets_lim_stream)
  apply (intro nn_integral_cong)
  apply (subst nn_integral_return)
  by (auto simp add: lim_stream'_def p s space_lim_stream space_ma space_stream_space)

lemma integral_lim_stream': 
  fixes f :: "('s \<times> 'a) stream \<Rightarrow> real" 
  assumes p[simp]: "is_policy p"
  assumes s[simp]: "s \<in> space Ms"
  assumes f_bounded: "\<And>x. \<bar>f x\<bar> \<le> B"
  assumes f[measurable]: "f \<in> borel_measurable (stream_space M)"
  shows "(\<integral>t. f t \<partial>lim_stream' p s) = 
    (\<integral>a. \<integral>s'. \<integral>t'. f ((s,a)##t') \<partial>lim_stream' (Suc_policy p (s,a)) s' \<partial>K (s,a) \<partial>p0 p s)"
  apply (subst lim_stream'_eq[OF p s], subst integral_bind[OF f, of B _ _ 1])
  using f_bounded apply blast
  subgoal 
    using measurable_prob_algebraD 
    by (measurable, simp add: measurable_ident_sets p0_sets)
  subgoal 
    using prob_space.finite_measure prob_space_p0 p s 
    by blast
  subgoal 
    apply simp
    apply (intro AE_I2 subprob_space.emeasure_space_le_1 subprob_space_bind 
        prob_space_imp_subprob_space)
     apply (simp add: prob_space_K2)
  proof  (intro measurable_bind[where N = "stream_space M"])
    fix x :: 'a
    assume a2: "x \<in> space (p0 p s)"
    obtain ss :: 
      "('s \<Rightarrow> ('s \<times> 'a) stream measure) \<Rightarrow> ('s \<Rightarrow> ('s \<times> 'a) stream measure) \<Rightarrow> 's measure \<Rightarrow> 's" 
      where f3: "\<forall>x1 x2 x3. (\<exists>v4. v4 \<in> space x3 \<and> x2 v4 \<noteq> x1 v4) = 
        (ss x1 x2 x3 \<in> space x3 \<and> x2 (ss x1 x2 x3) \<noteq> x1 (ss x1 x2 x3))"
      by moura
    have "return Ms \<in> K (s, x) \<rightarrow>\<^sub>M prob_algebra Ms"
      using a2 p s space_policy'
      by (metis measurable_return1 measurable_return_prob_space return_sets_cong sets_K' space_p0)
    then have "(\<lambda>sa. lim_stream (Suc_policy p (s, x)) (return Ms sa)) \<in> 
      K (s, x) \<rightarrow>\<^sub>M prob_algebra (stream_space M)"
      using a2 p is_policy_Suc_policy
      by (metis lim_stream measurable_compose_rev s space_ma space_policy' undefined_in_H0)
    then show "lim_stream' (Suc_policy p (s, x)) \<in> K (s, x) \<rightarrow>\<^sub>M subprob_algebra (stream_space M)"
      using f3 by (meson lim_stream'_def measurable_cong measurable_prob_algebraD)
  next
    show "\<And>x. x \<in> space (p0 p s) \<Longrightarrow> (\<lambda>s'. return (stream_space M) ((s, x) ## snd s')) \<in> 
      K (s, x) \<Otimes>\<^sub>M stream_space M \<rightarrow>\<^sub>M subprob_algebra (stream_space M)"
      using measurable_prob_algebraD p s by auto
  qed
  apply (intro Bochner_Integration.integral_cong[OF refl])
  apply (subst integral_bind[OF f f_bounded, where B' = 1])
     apply (auto simp: intro!:  measurable_prob_algebraD)[1]
  subgoal
    apply measurable
    by (auto simp add: measurable_ident_sets sets_K')
    apply (simp add: prob_space.finite_measure prob_space_K2; fail)
   apply simp
   apply (intro AE_I2 subprob_space.emeasure_space_le_1 subprob_space_bind)
    apply (intro prob_space_imp_subprob_space)
    apply (simp add: is_policy_Suc_policy lim_stream'_prob_space space_ma)
   apply auto apply measurable
  using s apply blast
   apply (simp add: is_policy_Suc_policy lim_stream'_sets measurable_ident_sets space_ma)
  apply (intro Bochner_Integration.integral_cong[OF refl])
  apply (subst integral_bind[OF f f_bounded, where B' = 1])
     apply measurable
      apply auto[1]
     apply (auto simp: is_policy_Suc_policy lim_stream'_prob_space prob_space.finite_measure space_ma)
  using indicator_leI apply fastforce
  apply (intro Bochner_Integration.integral_cong[OF refl])
  by (simp add: integral_return lim_stream'_def space_lim_stream space_ma space_stream_space)

lemma measurable_ident_Suc'[measurable]: 
  "(\<lambda>x. x) \<in> lim_stream' (Suc_policy p sa) s' \<rightarrow>\<^sub>M stream_space M"
  by (simp add: lim_stream'_def)

lemma p_eq_K'_eq:
  assumes p: "is_policy p" "is_policy p'"
  assumes s0: "s0 \<in> space (prob_algebra Ms)"
  assumes p_eq: "\<And>i hs. hs \<in> space (Hs i) \<Longrightarrow> p i hs = p' i hs"
  assumes h: "h \<in> space (H i)" 
  shows "K' p s0 i h = K' p' s0 i h"
  unfolding K'_def
  apply (intro bind_cong[OF refl])
  apply (intro bind_cong)
   apply (auto split: nat.splits)
  using s0 p p_eq h
   apply (simp add: space_prodI)
  apply (intro p_eq)
  apply (simp add: space_pair_measure)
  using h space_H1 space_K by blast

lemma policy_eq_imp_lim_stream_eq: "is_policy p \<Longrightarrow> is_policy p' \<Longrightarrow> s0 \<in> space (prob_algebra Ms) 
  \<Longrightarrow> \<forall>i. \<forall>hs \<in> space (Hs i). p i hs = p' i hs 
  \<Longrightarrow> lim_stream p s0 = lim_stream p' s0"
  unfolding lim_stream_def lim_sequence_def
  apply (intro distr_cong)
    apply (subst Ionescu_Tulcea_CI_eq[where P' = "(K' p' s0)"])
       apply (intro p_eq_K'_eq)
  using IT_K' by auto

end
end