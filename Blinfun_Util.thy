(* Author: Maximilian Schäffeler *)

theory Blinfun_Util
  imports "HOL-Analysis.Bounded_Linear_Function"
begin

overloading
  blinfunpow \<equiv> "compow :: nat \<Rightarrow> ('a::real_normed_vector \<Rightarrow>\<^sub>L 'a) \<Rightarrow> ('a \<Rightarrow>\<^sub>L 'a)"
begin

primrec blinfunpow :: "nat \<Rightarrow> ('a::real_normed_vector \<Rightarrow>\<^sub>L 'a) \<Rightarrow> ('a \<Rightarrow>\<^sub>L 'a)"
  where
    "blinfunpow 0 f = id_blinfun"
  | "blinfunpow (Suc n) f = f o\<^sub>L blinfunpow n f"

end

lemma blinfun_compose_id[simp]:
  "id_blinfun o\<^sub>L f = f"
  "f o\<^sub>L id_blinfun = f"
  by (auto intro!: blinfun_eqI)

lemma blinfun_compose_assoc: "F o\<^sub>L G o\<^sub>L H = F o\<^sub>L (G o\<^sub>L H)"
  using blinfun_apply_inject by fastforce

lemma blinfunpow_assoc: "(F::'a::real_normed_vector \<Rightarrow>\<^sub>L 'a) ^^ (Suc n) =(F ^^n) o\<^sub>L F"
  apply (induction n) using blinfun_compose_assoc 
   apply simp 
  by (metis blinfun_compose_assoc blinfunpow.simps(2))


lemma lim_blinfun_apply: "convergent X \<Longrightarrow> (\<lambda>n. blinfun_apply (X n) u) \<longlonglongrightarrow> lim X u"  
  apply (subst Limits.bounded_bilinear.tendsto[where prod = blinfun_apply])
  using blinfun.bounded_bilinear_axioms
  by (auto simp: convergent_LIMSEQ_iff)

lemma bounded_pow_blinfun[intro]: 
  assumes "bounded (range (F::nat \<Rightarrow> 'a::real_normed_vector \<Rightarrow>\<^sub>L 'a))"
  shows "bounded (range (\<lambda>t. (F t)^^(Suc n)))"
using assms proof -
  assume "bounded (range F)"
  then obtain b where bh: "\<forall>x. norm (F x) \<le> b"
    by (meson bounded_pos le_cases order_trans rangeI)
  hence "\<forall>x. norm ((F x)^^(Suc n)) \<le> b^(Suc n)"
    apply (induction n)
    using bh
    by (auto intro!: order.trans[OF norm_blinfun_compose] simp add: mult_mono')
  thus ?thesis
    by (auto intro!: boundedI)
qed


lemma blincomp_scaleR_right: "(a *\<^sub>R (F :: 'a :: real_normed_vector \<Rightarrow>\<^sub>L 'a)) ^^ t = a^t *\<^sub>R F^^t"
  apply (induction t arbitrary: a F) 
  by (auto intro!: blinfun_eqI simp: blinfun.scaleR_left blinfun.scaleR_right)

(* C.3 *)
lemma inv_one_sub_Q:
  fixes Q :: "'a :: banach \<Rightarrow>\<^sub>L 'a"
  assumes onorm_le: "norm (id_blinfun - Q) < 1"
  shows "(Q o\<^sub>L (\<Sum>i. (id_blinfun - Q)^^i)) = id_blinfun" 
  and "(\<Sum>i. (id_blinfun - Q)^^i) o\<^sub>L Q = id_blinfun"
proof -
  obtain b where bh: "b < 1"  "norm (id_blinfun - Q) < b"
    using onorm_le using dense by blast
  have "0 < b" using bh
    by (meson le_less_trans norm_imp_pos_and_ge)
  have norm_le_aux: "\<And>n. norm ((id_blinfun - Q)^^Suc n) \<le> b^(Suc n)"
  proof -
    fix n
    show "norm ((id_blinfun - Q)^^Suc n) \<le> b^(Suc n)"
    proof (induction n)
      case 0
      then show ?case using bh by simp
    next
      case (Suc n)
      then show ?case
      proof -
        have "norm ((id_blinfun - Q) ^^ Suc (Suc n)) \<le> norm (id_blinfun - Q) * norm((id_blinfun - Q) ^^ Suc n)"
          using norm_blinfun_compose bh \<open>0<b\<close> less_eq_real_def by auto
        also have "\<dots> \<le> b^(Suc (Suc n))"
          using Suc.IH \<open>0 < b\<close> bh by (auto simp: mult_mono')
        finally show ?thesis .
      qed
    qed 
  qed
  have "\<And>n. (Q o\<^sub>L (\<Sum>i\<le>n. (id_blinfun - Q)^^i)) = (id_blinfun - (id_blinfun - Q)^^(Suc n))"
  proof -
    fix n
    show "(Q o\<^sub>L (\<Sum>i\<le>n. (id_blinfun - Q)^^i) ) = (id_blinfun - (id_blinfun - Q)^^(Suc n))"
      apply (induction n) 
      by (auto simp: bounded_bilinear.diff_left bounded_bilinear.add_right 
          bounded_bilinear_blinfun_compose)
  qed
  hence "\<And>n. norm (id_blinfun - (Q o\<^sub>L (\<Sum>i\<le>n. (id_blinfun - Q)^^i))) \<le> b^Suc n"
    using norm_le_aux by auto
  hence l2: "(\<lambda>n. (id_blinfun - (Q o\<^sub>L (\<Sum>i\<le>n. (id_blinfun - Q)^^i)))) \<longlonglongrightarrow> 0"
    apply (subst Lim_transform_bound[where g="\<lambda>n. b^Suc n"])
    using \<open>0 < b\<close> bh by (auto intro!: tendsto_eq_intros)
  have "summable (\<lambda>n. (id_blinfun - Q)^^n)"
    using local.onorm_le norm_blinfun_compose by (force intro!: summable_ratio_test)
  hence "(\<lambda>n. \<Sum>i\<le>n.  (id_blinfun - Q)^^i) \<longlonglongrightarrow> (\<Sum>i. (id_blinfun - Q)^^i)"
    using summable_LIMSEQ' by blast
  hence "(\<lambda>n. Q o\<^sub>L (\<Sum>i\<le>n. (id_blinfun - Q)^^i)) \<longlonglongrightarrow> (Q o\<^sub>L (\<Sum>i. (id_blinfun - Q)^^i))"
    apply (subst Limits.bounded_bilinear.tendsto[where prod = "(o\<^sub>L)"])
    using bounded_bilinear_blinfun_compose by auto   
  hence "(\<lambda>n. id_blinfun - (Q o\<^sub>L (\<Sum>i\<le>n. (id_blinfun - Q)^^i))) \<longlonglongrightarrow> 
    id_blinfun - (Q o\<^sub>L (\<Sum>i. (id_blinfun - Q)^^i))"
    by (subst Limits.tendsto_diff) auto
  thus "(Q o\<^sub>L (\<Sum>i. (id_blinfun - Q)^^i)) = id_blinfun"
    using LIMSEQ_unique l2 by fastforce
next 
  obtain b where bh: "b < 1"  "norm (id_blinfun - Q) < b"
    using onorm_le using dense by blast
  have "0 < b" using bh
    by (meson le_less_trans norm_imp_pos_and_ge)
  have norm_le_aux: "\<And>n. norm ((id_blinfun - Q)^^Suc n) \<le> b^(Suc n)"
  proof -
    fix n
    show "norm ((id_blinfun - Q)^^Suc n) \<le> b^(Suc n)"
    proof (induction n)
      case 0
      then show ?case using bh by simp
    next
      case (Suc n)
      then show ?case
      proof -
        have "norm ((id_blinfun - Q) ^^ Suc (Suc n)) \<le> 
          norm (id_blinfun - Q) * norm((id_blinfun - Q) ^^ Suc n)"
          using norm_blinfun_compose bh \<open>0<b\<close> less_eq_real_def by auto
        also have "\<dots> \<le> b^(Suc (Suc n))"
          using Suc.IH \<open>0 < b\<close> bh by (auto simp: mult_mono')
        finally show ?thesis .
      qed
    qed 
  qed
  have "\<And>n. ((\<Sum>i\<le>n. (id_blinfun - Q)^^i) o\<^sub>L Q) = (id_blinfun - (id_blinfun - Q)^^(Suc n))"
  proof -
    fix n
    show "((\<Sum>i\<le>n. (id_blinfun - Q)^^i) o\<^sub>L Q) = (id_blinfun - (id_blinfun - Q)^^(Suc n))"
    proof (induction n)
      case 0
      then show ?case by simp
    next
      case (Suc n)
      have "sum ((^^) (id_blinfun - Q)) {..Suc n} o\<^sub>L Q = 
        (sum ((^^) (id_blinfun - Q)) {..n} o\<^sub>L Q) + ((id_blinfun - Q) ^^Suc n o\<^sub>L Q)"
        by (simp add: bounded_bilinear.add_left bounded_bilinear_blinfun_compose)
      also have "\<dots> = id_blinfun - (((id_blinfun - Q)^^(Suc n) o\<^sub>L id_blinfun) - 
        ((id_blinfun - Q) ^^Suc n o\<^sub>L Q))"
        using Suc.IH by auto
      also have "\<dots> = id_blinfun - (((id_blinfun - Q)^^(Suc n) o\<^sub>L (id_blinfun - Q)))"
        by (metis (no_types, lifting) add_cancel_right_left blinfun_compose_zero(1) 
            bounded_bilinear.prod_diff_prod bounded_bilinear_blinfun_compose diff_add_cancel)
      also have "\<dots> = id_blinfun - (((id_blinfun - Q)^^(Suc (Suc n))))"
        by (metis blinfunpow_assoc)
      finally show ?case
        by auto
    qed
  qed
  hence "\<And>n. norm (id_blinfun - ((\<Sum>i\<le>n. (id_blinfun - Q)^^i) o\<^sub>L Q)) \<le> b^Suc n"
    using norm_le_aux by auto
  hence l2: "(\<lambda>n. id_blinfun - ((\<Sum>i\<le>n. (id_blinfun - Q)^^i) o\<^sub>L Q)) \<longlonglongrightarrow> 0"
    apply (subst Lim_transform_bound[where g="\<lambda>n. b^Suc n"])
    using \<open>0 < b\<close> bh by (auto intro!: tendsto_eq_intros)
  have "summable (\<lambda>n. (id_blinfun - Q)^^n)"
    using local.onorm_le norm_blinfun_compose by (force intro!: summable_ratio_test)
  hence "(\<lambda>n. \<Sum>i\<le>n.  (id_blinfun - Q)^^i) \<longlonglongrightarrow> (\<Sum>i. (id_blinfun - Q)^^i)"
    using summable_LIMSEQ' by blast
  hence "(\<lambda>n. (\<Sum>i\<le>n. (id_blinfun - Q)^^i) o\<^sub>L Q) \<longlonglongrightarrow> ((\<Sum>i. (id_blinfun - Q)^^i) o\<^sub>L Q)"
    apply (subst Limits.bounded_bilinear.tendsto[where prod = "(o\<^sub>L)"])
    using bounded_bilinear_blinfun_compose by auto   
  hence "(\<lambda>n. id_blinfun - ((\<Sum>i\<le>n. (id_blinfun - Q)^^i) o\<^sub>L Q)) \<longlonglongrightarrow> 
    id_blinfun - ((\<Sum>i. (id_blinfun - Q)^^i) o\<^sub>L Q)"
    by (subst Limits.tendsto_diff) auto
  thus "((\<Sum>i. (id_blinfun - Q)^^i) o\<^sub>L Q) = id_blinfun"
    using LIMSEQ_unique l2 by fastforce
qed


(* C.4 *)
lemma inv_norm_le:
  fixes Q :: "'a :: banach \<Rightarrow>\<^sub>L 'a"
  assumes "norm Q  < 1"
  shows "(id_blinfun-Q) o\<^sub>L (\<Sum>i. Q^^i) = id_blinfun"
    "(\<Sum>i. Q^^i) o\<^sub>L (id_blinfun-Q) = id_blinfun"
  using inv_one_sub_Q[of "id_blinfun - Q"] assms
  by auto


lemma banach_blinfun:
  fixes C :: "'b :: {real_normed_vector, complete_space} \<Rightarrow>\<^sub>L 'b"
  assumes "norm C < 1"
  shows "\<exists>!v. C v = v" "\<And>v. (\<lambda>n. (C ^^ n) v) \<longlonglongrightarrow> (THE v. C v = v)"
  using assms
proof -
  obtain v where "C v = v" "\<forall>v'. C v' = v' \<longrightarrow> v' = v"
    using assms banach_fix_type[of "norm C" "blinfun_apply C"]
    by (metis blinfun.zero_right less_irrefl mult.left_neutral mult_less_le_imp_less 
        norm_blinfun norm_conv_dist norm_ge_zero zero_less_dist_iff)
  obtain l where "(\<forall>v u. norm (C (v - u)) \<le> l * dist v u)" "0 \<le> l" "l < 1"
    by (metis assms dist_norm norm_blinfun norm_imp_pos_and_ge)
  hence "(\<forall>v u. dist (C v) (C u) \<le> l * dist v u)"
    by (simp add: blinfun.diff_right dist_norm)
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
      have  "\<forall>r f ra rb. (r::real) \<le> f (rb::real) \<or> (\<exists>r ra. \<not> f r \<le> f ra \<and> r \<le> ra) \<or> \<not> ra \<le> rb \<or> 
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
    by (auto simp add: tendsto_mult_left_zero)
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
next
  show "norm C < 1 \<Longrightarrow> \<exists>!v. blinfun_apply C v = v"
    using assms banach_fix_type[of "norm C" "blinfun_apply C"]
    by (metis blinfun.diff_right dist_norm norm_blinfun norm_ge_zero)
qed
end