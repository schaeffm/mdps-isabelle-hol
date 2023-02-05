theory Splitting_Methods_Matrix
  imports 
    Splitting_Methods 
    Blinfun_Matrix
begin

definition "is_splitting_mat X Q R \<longleftrightarrow>
  X = Q - R \<and> invertible Q \<and> 0 \<le> matrix_inv Q \<and> 0 \<le> R"

lemma is_splitting_blin_mat: "is_splitting_blin X Q R \<longleftrightarrow> 
  is_splitting_mat (blinfun_to_matrix X) (blinfun_to_matrix Q) (blinfun_to_matrix R)"
proof -
  have "X = Q - R \<longleftrightarrow>  blinfun_to_matrix X = blinfun_to_matrix Q - blinfun_to_matrix R"
    using matrix_to_blinfun_inv blinfun_to_matrix_diff by metis
  moreover have "invertible\<^sub>L Q \<longleftrightarrow> invertible (blinfun_to_matrix Q)"
    using blinfun_to_matrix_inverse(1) invertible_invertible\<^sub>L_I(1) by auto
  moreover have "invertible\<^sub>L Q \<Longrightarrow> nonneg_blinfun (inv\<^sub>L Q) \<longleftrightarrow> 0 \<le> matrix_inv (blinfun_to_matrix Q)"
    by (metis nonneg_blinfun_iff blinfun_to_matrix_inverse(2))
  moreover have "nonneg_blinfun R \<longleftrightarrow> 0 \<le> blinfun_to_matrix R"
    by (simp add: nonneg_blinfun_iff)
  ultimately show ?thesis
    unfolding is_splitting_blin_def is_splitting_mat_def
    by auto
qed

context MDP_ord begin

sublocale MDP_att_\<L> using MDP_att_\<L>_axioms.

subsection \<open>Gauss Seidel Splitting\<close>
subsubsection \<open>Definition of Upper and Lower Triangular Matrices\<close>
definition "P_dec d \<equiv> blinfun_to_matrix (\<P>\<^sub>1 (mk_dec_det d))"
definition "P_upper d \<equiv> (\<chi> i j. if i \<le> j then P_dec d $ i $ j else 0)"
definition "P_lower d \<equiv> (\<chi> i j. if j < i then P_dec d $ i $ j else 0)"

definition "\<P>\<^sub>U d = matrix_to_blinfun (P_upper d)"
definition "\<P>\<^sub>L d = matrix_to_blinfun (P_lower d)"

lemma P_dec_elem: "P_dec d $ i $ j = pmf (K (i, d i)) j"
  unfolding blinfun_to_matrix_def matrix_def \<P>\<^sub>1.rep_eq K_st_def  P_dec_def push_exp.rep_eq vec_lambda_beta
  by (subst pmf_expectation_bind[of "{d i}"]) 
    (auto split: if_splits simp: mk_dec_det_def axis_def vec_lambda_inverse integral_measure_pmf[of "{j}"])  

lemma nonneg_\<P>\<^sub>U: "nonneg_blinfun (\<P>\<^sub>U d)"
  unfolding \<P>\<^sub>U_def blinfun_to_matrix_inv P_upper_def P_dec_elem 
  by (auto simp: nonneg_blinfun_iff Finite_Cartesian_Product.less_eq_vec_def)

lemma nonneg_P_dec: "0 \<le> P_dec d"
  by (simp add: Finite_Cartesian_Product.less_eq_vec_def P_dec_elem)

lemma nonneg_P_upper: "0 \<le> P_upper d"
  using nonneg_P_dec 
  by (simp add: Finite_Cartesian_Product.less_eq_vec_def P_upper_def)

lemma nonneg_P_lower: "0 \<le> P_lower d"
  using nonneg_P_dec 
  by (simp add: Finite_Cartesian_Product.less_eq_vec_def P_lower_def)

lemma nonneg_\<P>\<^sub>L: "nonneg_blinfun (\<P>\<^sub>L d)"
  unfolding \<P>\<^sub>L_def Finite_Cartesian_Product.less_eq_vec_def blinfun_to_matrix_inv P_lower_def P_dec_elem 
  by (auto simp: nonneg_blinfun_iff Finite_Cartesian_Product.less_eq_vec_def)

lemma nonneg_\<P>\<^sub>1: "nonneg_blinfun (\<P>\<^sub>1 d)"
  using \<P>\<^sub>1_nonneg.

lemma norm_\<P>\<^sub>L_le: "norm (\<P>\<^sub>L d) \<le> norm (\<P>\<^sub>1 (mk_dec_det d))"
  using nonneg_\<P>\<^sub>1 \<P>\<^sub>L_def nonneg_\<P>\<^sub>L
  by (intro matrix_le_norm_mono) (auto simp: blinfun_to_matrix_diff less_eq_vec_def nonneg_blinfun_iff  P_dec_def P_lower_def)

lemma norm_\<P>\<^sub>L_le_one: "norm (\<P>\<^sub>L d) \<le> 1"
  using norm_\<P>\<^sub>L_le norm_\<P>\<^sub>1 by auto

lemma norm_\<P>\<^sub>L_less_one: "norm (l *\<^sub>R \<P>\<^sub>L d) < 1"
  using order.strict_trans1[OF mult_left_le disc_lt_one] zero_le_disc norm_\<P>\<^sub>L_le_one
  by auto

lemma matrix_to_blinfun_le: "(M :: real ^ _ ^ _) \<le> N \<Longrightarrow> blinfun_le (matrix_to_blinfun M) (matrix_to_blinfun N)"
  by (simp add: blinfun_le_def nonneg_blinfun_iff matrix_to_blinfun_diff[symmetric])

lemma \<P>\<^sub>L_le_\<P>\<^sub>1: "0 \<le> v \<Longrightarrow> \<P>\<^sub>L d v \<le> \<P>\<^sub>1 (mk_dec_det d) v"
proof -
  assume "0 \<le> v"
  moreover have "P_lower d \<le> P_dec d"
    using nonneg_P_dec
    by (auto simp: P_lower_def less_eq_vec_def)
  ultimately show ?thesis
    unfolding P_dec_def \<P>\<^sub>L_def
    by (metis blinfun_le_iff matrix_to_blinfun_le matrix_to_blinfun_inv)
qed

lemma \<P>\<^sub>U_le_\<P>\<^sub>1: "0 \<le> v \<Longrightarrow> \<P>\<^sub>U d v \<le> \<P>\<^sub>1 (mk_dec_det d) v"
proof -
  assume "0 \<le> v"
  moreover have "P_upper d \<le> P_dec d"
    using nonneg_P_dec
    by (auto simp: P_upper_def less_eq_vec_def)
  ultimately show ?thesis
    unfolding P_dec_def \<P>\<^sub>U_def
    by (metis blinfun_le_iff matrix_to_blinfun_inv matrix_to_blinfun_le)
qed

lemma row_P_upper_indep: "d s = d' s \<Longrightarrow> row s (P_upper d) = row s (P_upper d')"
  unfolding row_def P_dec_elem P_upper_def
  by auto

lemma row_P_lower_indep: "d s = d' s \<Longrightarrow> row s (P_lower d) = row s (P_lower d')"
  unfolding row_def P_dec_elem P_lower_def
  by auto

lemma triangular_mat_P_upper: "upper_triangular_mat (P_upper d)"
  unfolding upper_triangular_mat_def P_upper_def
  by auto

lemma slt_P_lower: "strict_lower_triangular_mat (P_lower d)"
  unfolding strict_lower_triangular_mat_def P_lower_def
  by auto

lemma lt_P_lower: "lower_triangular_mat (P_lower d)"
  unfolding lower_triangular_mat_def P_lower_def
  by auto


subsubsection \<open>Gauss Seidel is a Regular Splitting\<close>
definition "Q_GS d = id_blinfun - l *\<^sub>R \<P>\<^sub>L d"
definition "R_GS d = l *\<^sub>R \<P>\<^sub>U d"

lemma splitting_gauss: "is_splitting_blin (id_blinfun - l *\<^sub>R \<P>\<^sub>1 (mk_dec_det d)) (Q_GS d) (R_GS d)"
  unfolding is_splitting_blin_def
proof safe
  show "nonneg_blinfun (R_GS d)"
    unfolding R_GS_def \<P>\<^sub>U_def blinfun_to_matrix_scaleR Finite_Cartesian_Product.less_eq_vec_def blinfun_to_matrix_inv
    using nonneg_P_upper 
    by (simp add: blinfun_to_matrix_scaleR nonneg_blinfun_iff scaleR_nonneg_nonneg)
next
  have "\<P>\<^sub>L d + \<P>\<^sub>U d = \<P>\<^sub>1 (mk_dec_det d)" for d
  proof -
    have "\<P>\<^sub>L d + \<P>\<^sub>U d  = matrix_to_blinfun (\<chi> i j. ((blinfun_to_matrix (\<P>\<^sub>1 (mk_dec_det d)))) $ i $ j)"
      unfolding \<P>\<^sub>L_def \<P>\<^sub>U_def P_lower_def P_upper_def P_dec_def matrix_to_blinfun_add[symmetric]
      by (auto simp: vec_eq_iff intro!: arg_cong[of _ _ matrix_to_blinfun])
    also have "\<dots> = (\<P>\<^sub>1 (mk_dec_det d))"
      by (simp add: matrix_to_blinfun_inv)
    finally show "\<P>\<^sub>L d + \<P>\<^sub>U d = \<P>\<^sub>1 (mk_dec_det d)".
  qed
  thus "id_blinfun - l *\<^sub>R \<P>\<^sub>1 (mk_dec_det d) = Q_GS d - R_GS d"
    unfolding Q_GS_def R_GS_def
    by (auto simp: algebra_simps scaleR_add_right[symmetric] simp del: scaleR_add_right)
next
  have n_le: "norm (l *\<^sub>R \<P>\<^sub>L d) < 1"
    using mult_left_le[OF norm_\<P>\<^sub>L_le_one[of d] zero_le_disc] order.strict_trans1
    by (auto intro: disc_lt_one)
  thus "invertible\<^sub>L (Q_GS d)"
    by (simp add: Q_GS_def invertible\<^sub>L_inf_sum)
  have "inv\<^sub>L (Q_GS d) = (\<Sum>i. (l *\<^sub>R \<P>\<^sub>L d) ^^ i)"
    using inv\<^sub>L_inf_sum n_le unfolding Q_GS_def
    by blast
  hence *: "blinfun_to_matrix (inv\<^sub>L (Q_GS d)) $ i $ j = (\<Sum>k. blinfun_to_matrix ((l *\<^sub>R \<P>\<^sub>L d) ^^ k) $ i $ j)" for i j
    using summable_inv_Q[of "Q_GS d"] norm_\<P>\<^sub>L_less_one 
    unfolding Q_GS_def
    by (subst bounded_linear.suminf[symmetric]) 
      (auto intro!: bounded_linear_compose[OF bounded_linear_vec_nth] bounded_linear_compose[OF bounded_linear_blinfun_to_matrix])
  have "0 \<le> l^i *\<^sub>R matpow (P_lower d) i" for i
    using nonneg_matpow[OF nonneg_P_lower] 
    by (meson scaleR_nonneg_nonneg zero_le_disc zero_le_power)
  have "0 \<le> (\<Sum>k. blinfun_to_matrix ((l *\<^sub>R \<P>\<^sub>L d) ^^ k) $ i $ j)" for i j
  proof (intro suminf_nonneg)
    show "summable (\<lambda>k. blinfun_to_matrix ((l *\<^sub>R \<P>\<^sub>L d) ^^ k) $ i $ j)"
      using summable_inv_Q[of "Q_GS d"] norm_\<P>\<^sub>L_less_one 
      unfolding Q_GS_def 
      by (fastforce
          simp: 
          blinfun_to_matrix_matpow nonneg_matrix_nonneg blincomp_scaleR_right blinfun_to_matrix_scaleR
          intro:
          bounded_linear.summable[of _ "\<lambda>i. (l *\<^sub>R \<P>\<^sub>L d) ^^ i"] 
          bounded_linear_compose[OF bounded_linear_vec_nth] 
          bounded_linear_compose[OF bounded_linear_blinfun_to_matrix])
    show "\<And>n. 0 \<le> blinfun_to_matrix ((l *\<^sub>R \<P>\<^sub>L d) ^^ n) $ i $ j"
      using nonneg_matpow[OF nonneg_P_lower]
      by (auto simp: \<P>\<^sub>L_def nonneg_matrix_nonneg blinfun_to_matrix_scaleR matpow_scaleR blinfun_to_matrix_matpow)
  qed
  thus "nonneg_blinfun (inv\<^sub>L (Q_GS d))"
    by (simp add: * nonneg_blinfun_iff Finite_Cartesian_Product.less_eq_vec_def)
qed

abbreviation "r_det\<^sub>b d \<equiv> r_dec\<^sub>b (mk_dec_det d) "
abbreviation "r_vec d \<equiv> \<chi> i. r_dec\<^sub>b (mk_dec_det d) i"

abbreviation "Q_mat d \<equiv> blinfun_to_matrix (Q_GS d)"
abbreviation "R_mat d \<equiv> blinfun_to_matrix (R_GS d)"

lemma Q_mat_def: "Q_mat d = mat 1 - l *\<^sub>R P_lower d"
  unfolding Q_GS_def
  by (simp add: \<P>\<^sub>L_def blinfun_to_matrix_diff blinfun_to_matrix_id blinfun_to_matrix_scaleR)

lemma R_mat_def: "R_mat d = l *\<^sub>R P_upper d"
  unfolding R_GS_def
  by (simp add: \<P>\<^sub>U_def blinfun_to_matrix_scaleR)

lemma triangular_mat_R: "upper_triangular_mat (R_mat d)"
  using triangular_mat_P_upper
  unfolding upper_triangular_mat_def R_mat_def
  by auto

definition "GS_inv d v \<equiv> matrix_inv (Q_mat d) *v (r_vec d + R_mat d *v v)"

text \<open>@{term Q_mat} can be expressed as an infinite sum of @{const P_lower}. 
  It is therefore lower triangular.\<close>
lemma inv_Q_mat_suminf: "matrix_inv (Q_mat d) = (\<Sum>k. (matpow (l *\<^sub>R (P_lower d)) k))"
proof -
  have "matrix_inv (Q_mat d) = blinfun_to_matrix (inv\<^sub>L (Q_GS d))"
    using blinfun_to_matrix_inverse(2) is_splitting_blin_def splitting_gauss
    by metis
  also have "\<dots> = blinfun_to_matrix (\<Sum>i. (l *\<^sub>R \<P>\<^sub>L d)^^i)"
    using norm_\<P>\<^sub>L_less_one 
    by (auto simp: Q_GS_def inv\<^sub>L_inf_sum)
  also have "\<dots> = (\<Sum>k. (blinfun_to_matrix ((l *\<^sub>R \<P>\<^sub>L d)^^k)))"
    using summable_inv_Q[of "Q_GS d"] norm_\<P>\<^sub>L_less_one bounded_linear_blinfun_to_matrix
    unfolding Q_GS_def row_def
    by (subst bounded_linear.suminf) auto
  also have "\<dots> = (\<Sum>k. (matpow (l *\<^sub>R (P_lower d)) k))"
    by (simp add: blinfun_to_matrix_scaleR blinfun_to_matrix_matpow \<P>\<^sub>L_def)
  finally show ?thesis.
qed

lemma lt_Q_inv: "lower_triangular_mat (matrix_inv (Q_mat d))"
  unfolding inv_Q_mat_suminf
  using summable_inv_Q[of "Q_GS d"] norm_\<P>\<^sub>L_less_one summable_blinfun_to_matrix[of "\<lambda>i.  (l *\<^sub>R \<P>\<^sub>L d)^^i"]
  by (intro lower_triangular_suminf lower_triangular_pow) 
    (auto simp: lower_triangular_mat_def P_lower_def Q_GS_def blinfun_to_matrix_scaleR blinfun_to_matrix_matpow \<P>\<^sub>L_def)

text \<open>Each row of the matrix @{term "Q_mat d"} only depends on @{term d}'s actions in lower states.\<close>

lemma inv_Q_mat_indep:
  assumes "\<And>i. i \<le> s \<Longrightarrow> d i = d' i" "i \<le> s"
  shows  "row i (matrix_inv (Q_mat d)) = row i (matrix_inv (Q_mat d'))"
proof -
  have "row i (matrix_inv (Q_mat d)) = row i (blinfun_to_matrix (inv\<^sub>L (Q_GS d)))"
    using blinfun_to_matrix_inverse(2) is_splitting_blin_def splitting_gauss
    by metis
  also have "\<dots> = row i (blinfun_to_matrix (\<Sum>i. (l *\<^sub>R \<P>\<^sub>L d)^^i))"
    using norm_\<P>\<^sub>L_less_one
    by (auto simp: Q_GS_def inv\<^sub>L_inf_sum)
  also have "\<dots> = (\<Sum>k. row i (blinfun_to_matrix ((l *\<^sub>R \<P>\<^sub>L d)^^k)))"
    using summable_inv_Q[of "Q_GS d"] norm_\<P>\<^sub>L_less_one
    unfolding Q_GS_def row_def
    by (subst bounded_linear.suminf[OF bounded_linear_compose[OF _ bounded_linear_blinfun_to_matrix]]) auto
  also have "\<dots> = (\<Sum>k. row i (matpow (l *\<^sub>R (P_lower d)) k))"
    by (simp add: blinfun_to_matrix_matpow blinfun_to_matrix_scaleR \<P>\<^sub>L_def)
  also have "\<dots> = (\<Sum>k. l^k *\<^sub>R row i (matpow ((P_lower d)) k))"
    by (subst matpow_scaleR) (auto simp: row_def scaleR_vec_def) 
  also have "\<dots> = (\<Sum>k. l^k *\<^sub>R row i (matpow ((P_lower d')) k))"
    using assms 
    by (subst lower_triangular_pow_eq[of "P_lower d'"]) (auto simp: P_dec_elem lt_P_lower row_P_lower_indep[of d' _ d])
  also have "\<dots> = (\<Sum>k. row i (matpow (l *\<^sub>R (P_lower d')) k))"
    by (subst matpow_scaleR) (auto simp: row_def scaleR_vec_def)
  also have "\<dots> = (\<Sum>k. row i (blinfun_to_matrix ((l *\<^sub>R \<P>\<^sub>L d')^^k)))"
    by (simp add: \<P>\<^sub>L_def blinfun_to_matrix_matpow blinfun_to_matrix_scaleR)
  also have "\<dots> = row i (blinfun_to_matrix (\<Sum>i. (l *\<^sub>R \<P>\<^sub>L d')^^i))"
    using summable_inv_Q[of "Q_GS d'"] norm_\<P>\<^sub>L_less_one 
    unfolding Q_GS_def row_def
    by (auto intro!: bounded_linear.suminf[symmetric] 
        bounded_linear_compose[OF _ bounded_linear_blinfun_to_matrix])
  also have "\<dots> = row i (blinfun_to_matrix (inv\<^sub>L (Q_GS d')))"
    by (metis Q_GS_def inv\<^sub>L_inf_sum norm_\<P>\<^sub>L_less_one)
  also have "\<dots> = row i (matrix_inv (Q_mat d'))"
    by (metis blinfun_to_matrix_inverse(2) is_splitting_blin_def splitting_gauss)
  finally show ?thesis.
qed

text \<open>As a result, also @{term GS_inv} is independent of lower actions.\<close>
lemma GS_indep_high_states:
  assumes "\<And>s'. s' \<le> s \<Longrightarrow> d s' = d' s'"
  shows "GS_inv d v $ s = GS_inv d' v $ s"
proof -
  have "row i (P_upper d) = row i (P_upper d')" if "i \<le> s" for i
    using assms that row_P_upper_indep by blast
  hence R_eq_upto_s: "row i (R_mat d) = row i (R_mat d')" if "i \<le> s" for i
    using that
    by (simp add: row_def R_mat_def)

  have Qr_eq: "(matrix_inv (Q_mat d) *v r_vec d) $ s = (matrix_inv (Q_mat d') *v r_vec d') $ s"
  proof -
    have "(matrix_inv (Q_mat d) *v r_vec d) $ s = (\<Sum>j\<in>UNIV. matrix_inv (Q_mat d) $ s $ j * r_vec d $ j)"    
      unfolding matrix_vector_mult_def 
      by simp
    also have "\<dots> = (\<Sum>j\<in>UNIV. if s < j then 0 else matrix_inv (Q_mat d) $ s $ j * r_vec d $ j)"
      using lt_Q_inv
      by (auto intro!: sum.cong simp: lower_triangular_mat_def)
    also have "\<dots> = (\<Sum>j\<in>UNIV. if s < j then 0 else matrix_inv (Q_mat d') $ s $ j * r_vec d $ j)"
      using inv_Q_mat_indep assms
      by (fastforce intro!: sum.cong simp: row_def)
    also have "\<dots> = (matrix_inv (Q_mat d') *v r_vec d') $ s"
      using lt_Q_inv 
      by (auto simp: matrix_vector_mult_def assms lower_triangular_mat_def intro!: sum.cong)
    finally show ?thesis.
  qed

  have QR_eq: "row s (matrix_inv (Q_mat d) ** R_mat d) = row s (matrix_inv (Q_mat d') ** R_mat d')"
  proof - 
    have "matrix_inv (Q_mat d) $ s $ k * R_mat d $ k $ j = matrix_inv (Q_mat d') $ s $ k * R_mat d' $ k $ j" for k j
    proof - 
      have "matrix_inv (Q_mat d) $ s $ k * R_mat d $ k $ j = 
          (if s < k then 0 else matrix_inv (Q_mat d) $ s $ k * R_mat d $ k $ j)"
        using lower_triangular_mat_def lt_Q_inv by auto
      also have "\<dots> = (if s < k then 0 else matrix_inv (Q_mat d') $ s $ k * R_mat d $ k $ j)"
        by (metis (no_types, lifting) Finite_Cartesian_Product.row_def assms inv_Q_mat_indep order_refl vec_lambda_eta)
      also have "\<dots> = (if s < k \<or> j < k then 0 else (matrix_inv (Q_mat d') $ s $ k * R_mat d $ k $ j))"
        using triangular_mat_R
        unfolding upper_triangular_mat_def
        by (auto split: if_splits)
      also have "\<dots> = (if s < k \<or> j < k then 0 else (matrix_inv (Q_mat d') $ s $ k * R_mat d' $ k $ j))"
        using R_eq_upto_s
        by (auto simp: row_def)
      also have "\<dots> = matrix_inv (Q_mat d') $ s $ k * R_mat d' $ k $ j"
        by (metis lower_triangular_mat_def lt_Q_inv mult_not_zero triangular_mat_R upper_triangular_mat_def)
      finally show ?thesis.
    qed
    thus ?thesis
      unfolding row_def matrix_matrix_mult_def
      by auto
  qed
  show ?thesis
    using QR_eq Qr_eq
    by (auto simp add: GS_inv_def vec.add row_def matrix_vector_mul_assoc matrix_vector_mult_code')
qed

text \<open>This recursive definition mimics the computation of the GS iteration.\<close>
lemma GS_inv_rec: "GS_inv d v = r_vec d + l *\<^sub>R (P_upper d *v v + P_lower d *v (GS_inv d v))"
proof -
  have "Q_mat d *v (GS_inv d v) = r_vec d + R_mat d *v v"
    using splitting_gauss[of d] blinfun_to_matrix_inverse(1)
    unfolding GS_inv_def matrix_vector_mul_assoc is_splitting_blin_def
    by (subst matrix_inv(2)) auto
  thus ?thesis 
    unfolding Q_mat_def R_mat_def
    by (auto simp: algebra_simps scaleR_matrix_vector_assoc)
qed

lemma is_am_GS_inv_extend:
  assumes "\<And>s. s < k \<Longrightarrow> is_arg_max (\<lambda>d. GS_inv d v $ s) (\<lambda>d. d \<in> D\<^sub>D) d"
    and "is_arg_max (\<lambda>a. GS_inv (d (k := a)) v $ k) (\<lambda>a. a \<in> A k) a"
    and "s \<le> k"
    and "d \<in> D\<^sub>D"
  shows "is_arg_max (\<lambda>d. GS_inv d v $ s) (\<lambda>d. d \<in> D\<^sub>D) (d (k := a))"
proof -
  have am_k: "is_arg_max (\<lambda>d. GS_inv d v $ k) (\<lambda>d. d \<in> D\<^sub>D) (d (k := a))"
  proof (rule is_arg_max_linorderI)
    fix y
    assume "y \<in> D\<^sub>D"
    have "GS_inv y v $ k = (r_vec y + l *\<^sub>R (P_upper y *v v + P_lower y *v (GS_inv y v))) $ k"
      using GS_inv_rec by auto
    also have "\<dots> = r (k, y k) + l * ((P_upper y *v v) $ k + (P_lower y *v GS_inv y v) $ k)"
      by auto
    also have "\<dots> \<le> r (k, (d(k := y k)) k) + l * ((P_upper (d(k := y k)) *v v) $ k + (P_lower (d(k := y k)) *v GS_inv (d(k := y k)) v) $ k)"
    proof (rule add_mono, goal_cases)
      case 2
      thus ?case
      proof (intro mult_left_mono add_mono, goal_cases)
        case 1
        thus ?case
          by (auto simp: matrix_vector_mult_def P_dec_elem fun_upd_same P_upper_def cong: if_cong)
      next
        case 2
        thus ?case 
        proof -
          have "(P_lower y *v GS_inv y v) $ k = (P_lower (d(k := y k)) *v GS_inv y v) $ k"
            unfolding matrix_vector_mult_def
            by (auto simp: P_dec_elem fun_upd_same P_lower_def cong: if_cong)
          also have "\<dots> = (\<Sum>j\<in>UNIV. (if j < k then pmf (K (k, y k)) j  * GS_inv y v $ j  else 0))"
            by (auto simp: matrix_vector_mult_def P_dec_elem P_lower_def intro!: sum.cong)
          also have "\<dots> \<le> (\<Sum>j\<in>UNIV. (if j < k then pmf (K (k, y k)) j  * GS_inv d v $ j  else 0))"
            using assms \<open>y\<in>D\<^sub>D\<close>
            by (fastforce intro!: sum_mono mult_left_mono)
          also have "\<dots> =  (\<Sum>j\<in>UNIV. (if j < k then pmf (K (k, y k)) j  * GS_inv (d(k := y k)) v $ j else 0))"  
            using GS_indep_high_states[of _ "d(k := y k)" d, symmetric]
            by (fastforce intro!: sum.cong dest: leD)
          also have "\<dots> =  (P_lower (d(k := y k)) *v GS_inv (d(k := y k)) v) $ k"
            unfolding matrix_vector_mult_def P_lower_def P_dec_elem
            by (fastforce intro!: sum.cong)
          finally show ?thesis.
        qed
      qed auto
    qed auto
    also have "\<dots> = (r_vec (d(k := y k)) + l *\<^sub>R ((P_upper (d(k := y k)) *v v) + (P_lower (d(k := y k)) *v GS_inv (d(k := y k)) v))) $ k"
      by auto
    also have "\<dots> = GS_inv (d(k := y k)) v $ k"
      using GS_inv_rec by presburger
    also have "\<dots> \<le> GS_inv (d(k := a)) v $ k"
      using is_arg_max_linorderD(2)[OF assms(2)] \<open>y \<in> D\<^sub>D\<close> is_dec_det_def
      by blast
    finally show "GS_inv y v $ k \<le> GS_inv (d(k := a)) v $ k".
  next
    show "d(k := a) \<in> D\<^sub>D"
      using assms
      by (auto simp: is_dec_det_def is_arg_max_linorder)
  qed
  show ?thesis
  proof (cases "s < k")
    case True
    thus ?thesis
      using am_k assms(1)[OF True] GS_indep_high_states[of s "d (k := a)" d]
      by fastforce
  next
    case False
    thus ?thesis
      using assms am_k
      by auto
  qed
qed


lemma is_arg_max_GS_le: 
  "\<exists>d. \<forall>s\<le>k. is_arg_max (\<lambda>d. GS_inv d v $ s) (\<lambda>d. d \<in> D\<^sub>D) d"
proof (induction k rule: less_induct)
  case (less x)
  show ?case
  proof (cases "\<exists>y. y < x")
    case True
    define y where "y = Max {y. y < x}"  
    have "y < x"
      using Max_in
      by (simp add: True y_def)
    obtain d_opt where d_opt: "is_arg_max (\<lambda>d. GS_inv d v $ s) (\<lambda>d. d \<in> D\<^sub>D) d_opt" if "s \<le> y" for s
      using \<open>y < x\<close> less by blast

    define d_act where d_act: "d_act a = d_opt(x := a)" for a
    have le_y: "a < x \<Longrightarrow> a \<le> y" for a
      by (simp add: y_def)
    have 1: "GS_inv d v = r_vec d + l *\<^sub>R (P_upper d *v v + P_lower d *v (GS_inv d v))" for d
    proof -
      have "Q_mat d *v (GS_inv d v) = (R_mat d *v v + r_vec d)"
        unfolding GS_inv_def
        using splitting_gauss[unfolded is_splitting_blin_def]
        by (auto simp: matrix_vector_mul_assoc matrix_inv_right[OF blinfun_to_matrix_inverse(1)])
      thus ?thesis
        unfolding Q_mat_def R_mat_def
        by (auto simp: scaleR_matrix_vector_assoc algebra_simps)
    qed
    have "(\<Squnion>d \<in> D\<^sub>D. GS_inv d v $ x) = (\<Squnion>d \<in> D\<^sub>D. (r_vec d + l *\<^sub>R (P_upper d *v v + P_lower d *v (GS_inv d v))) $ x)"
      using 1 by auto
    also have "\<dots> = (\<Squnion>a \<in> A x. (r_vec (d_act a) + l *\<^sub>R (P_upper (d_act a) *v v + P_lower (d_act a) *v (GS_inv (d_act a) v))) $ x)"
    proof (rule antisym, rule cSUP_mono, goal_cases)
      case (3 n)
      moreover have "(P_upper n *v v) $ x \<le> (P_upper (d_opt(x := n x)) *v v) $ x"
        unfolding P_upper_def matrix_vector_mult_def
        by (auto simp: P_dec_elem cong: if_cong)
      moreover 
      {
        have "\<And>j. j < x \<Longrightarrow> GS_inv n v $ j \<le> GS_inv (d_opt(x := n x)) v $ j"
          using d_opt[OF le_y] 3
          by (subst GS_indep_high_states[of _ "d_opt(x := n x)" d_opt]) (auto simp: is_arg_max_linorder)
        hence "(P_lower n *v GS_inv n v) $ x \<le> (P_lower (d_opt(x := n x)) *v GS_inv (d_opt(x := n x)) v) $ x"
          unfolding matrix_vector_mult_def P_lower_def P_dec_elem
          by (fastforce intro!: mult_left_mono sum_mono)
      }
      ultimately show ?case
        unfolding d_act
        by (auto intro!: bexI[of _ "n x"] mult_left_mono add_mono simp: is_dec_det_def)
    next
      case 4
      then show ?case
      proof (rule cSUP_mono, goal_cases)
        case (3 n)
        then show ?case 
          using d_opt
          by (fastforce simp: d_act is_dec_det_def is_arg_max_linorder intro!: bexI[of _ "d_act n"])
      qed (auto simp: A_ne)
    qed auto
    also have "\<dots> = (\<Squnion>a \<in> A x. GS_inv (d_act a) v $ x)"
      using 1 by auto
    finally have *: "(\<Squnion>d \<in> D\<^sub>D. GS_inv d v $ x) = (\<Squnion>a \<in> A x. GS_inv (d_act a) v $ x)".
    then obtain a_opt where a_opt: "is_arg_max (\<lambda>a. GS_inv (d_act a) v $ x) (\<lambda>a. a \<in> A x) a_opt"
      by (metis A_ne finite finite_is_arg_max)
    hence "(\<Squnion>d \<in> D\<^sub>D. GS_inv d v $ x) = GS_inv (d_act a_opt) v $ x"
      by (metis * arg_max_SUP)
    hence am_a_opt: "is_arg_max (\<lambda>d. GS_inv d v $ x) (\<lambda>d. d \<in> D\<^sub>D) (d_act a_opt)"
      using a_opt d_opt d_act unfolding is_dec_det_def
      by (fastforce intro!: SUP_is_arg_max)
    hence "is_arg_max (\<lambda>d. GS_inv d v $ x') (\<lambda>d. d \<in> D\<^sub>D) (d_act a_opt)" if "x' < x" for x'
    proof -
      have "s' \<le> x' \<Longrightarrow> d_act a_opt s' = d_opt s'" for s'
        using d_act that is_arg_max_linorderD[OF d_opt[OF le_y[OF that]]]
        by auto
      thus ?thesis
        using am_a_opt is_arg_max_linorderD[OF d_opt[OF le_y[OF that]]]
        by (auto simp: GS_indep_high_states[of _ "d_act a_opt" d_opt])
    qed
    thus ?thesis
      by (metis am_a_opt antisym_conv1)
  next
    case False
    thus ?thesis
      using finite_is_arg_max[OF finite_D\<^sub>D]
      by (metis D_det_ne order_le_imp_less_or_eq)
  qed
qed

lemma ex_is_arg_max_GS: 
  "\<exists>d. \<forall>s. is_arg_max (\<lambda>d. GS_inv d v $ s) (\<lambda>d. d \<in> D\<^sub>D) d"
  using is_arg_max_GS_le[of "Max UNIV"]  
  by auto

function GS_rec_fun where
  "GS_rec_fun v s = (\<Squnion>a \<in> A s. r (s, a) + l * (
  (\<Sum>s' < s. pmf (K (s,a)) s' * (GS_rec_fun v s')) + 
  (\<Sum>s' \<in> {s'. s \<le> s'}. pmf (K (s,a)) s' * v s')))"
  by auto
termination
proof (relation "{(x,y). snd x < snd y}", rule wfI_min, goal_cases)
  case (1 x Q)
  assume " x \<in> Q"
  hence *: "{u. \<exists>a. (a, u) \<in> Q} \<noteq> {}"
    by (metis (mono_tags, lifting) \<open>x\<in>Q\<close> prod.collapse Collect_empty_eq)
  hence "\<exists>a x. (a,x)\<in>Q \<and> x = Min (snd ` Q)"
    by (auto simp: image_iff) (metis (mono_tags, lifting) equals0D Min_in[OF finite] prod.collapse image_iff)
  then obtain x where "x \<in> Q" "snd x = Min {snd x| x. x \<in> Q}"
    by (metis Setcompr_eq_image snd_conv)
  thus ?case
    using *
    by (intro bexI[of _ x]) auto
qed auto

declare GS_rec_fun.simps[simp del] 

definition "GS_rec_elem v s a = r (s, a) + l * (
  (\<Sum>s' < s. pmf (K (s,a)) s' * (GS_rec_fun v s')) + 
  (\<Sum>s' \<in> {s'. s \<le> s'}. pmf (K (s,a)) s' * v s'))"

lemma GS_rec_fun_elem: "GS_rec_fun v s = (\<Squnion>a \<in> A s. GS_rec_elem v s a)"
  unfolding GS_rec_elem_def
  using GS_rec_fun.simps 
  by blast

definition "GS_rec v = (\<chi> s. GS_rec_fun (vec_nth v) s)"

lemma GS_rec_def': "GS_rec v $ s = (\<Squnion>a \<in> A s. r (s, a) + l * (
  (\<Sum>s' < s. pmf (K (s,a)) s' * (GS_rec v $ s')) + 
  (\<Sum>s' \<in> {s'. s \<le> s'}. pmf (K (s,a)) s' * v $ s')))"
  unfolding GS_rec_def
  by (auto simp: GS_rec_fun.simps[of _ s])

lemma GS_rec_eq: "GS_rec v $ s = (\<Squnion>a \<in> A s. r (s, a) + l * (
  (P_lower (d(s := a)) *v (GS_rec v)) $ s + (P_upper (d(s := a)) *v v) $ s))"
  unfolding GS_rec_def'[of v s] P_lower_def P_upper_def P_dec_elem matrix_vector_mult_def
  by (auto simp: if_distrib[where f = "\<lambda>x. x * _ $ _"] sum.If_cases lessThan_def)
definition "GS_rec_step d v \<equiv> r_vec d + l *\<^sub>R (P_lower d *v GS_rec v + P_upper d *v v)"

lemma GS_rec_eq': "GS_rec v $ s = (\<Squnion>a \<in> A s. GS_rec_step (d(s:= a)) v $ s)"
  using GS_rec_eq GS_rec_step_def by auto

lemma GS_rec_eq_vec:
  "GS_rec v $ s = (\<Squnion>d\<in>D\<^sub>D. GS_rec_step d v $ s)"
proof -
  obtain d where d: "is_arg_max (\<lambda>d. GS_rec_step d v $ s) (\<lambda>d. d \<in>D\<^sub>D) d"
    using finite_is_arg_max[OF finite, of "D\<^sub>D" ] ex_dec_det
    by (metis D_det_ne)
  have "GS_rec v $ s = GS_rec_step d v $ s"
    unfolding GS_rec_eq'[of _ _ d]
  proof (intro antisym cSUP_least)
    show "\<And>x. x \<in> A s \<Longrightarrow> GS_rec_step (d(s := x)) v $ s \<le> GS_rec_step d v $ s"
      using A_ne d
      by (intro is_arg_max_linorderD[OF d]) (auto simp: is_dec_det_def is_arg_max_linorder)
    show "GS_rec_step d v $ s \<le> (\<Squnion>a\<in>A s. GS_rec_step (d(s := a)) v $ s)"
      using d unfolding is_arg_max_linorder is_dec_det_def fun_upd_triv
      by (auto intro!: cSUP_upper2[of _ _ "d s"])
  qed (auto simp: A_ne)
  thus ?thesis
    using d
    by (subst arg_max_SUP[symmetric]) auto
qed


lift_definition GS_rec_fun\<^sub>b :: "('s \<Rightarrow>\<^sub>b real) \<Rightarrow> ('s \<Rightarrow>\<^sub>b real)" is GS_rec_fun
  by auto

definition "GS_rec_fun_inner (v :: 's \<Rightarrow>\<^sub>b real) s a \<equiv> r (s, a) + l * (
  (\<Sum>s' < s. pmf (K (s,a)) s' * (GS_rec_fun\<^sub>b v s')) + 
  (\<Sum>s' \<in> {s'. s \<le> s'}. pmf (K (s,a)) s' * v s'))"

definition GS_rec_iter where
  "GS_rec_iter v s = (\<Squnion>a \<in> A s. r (s, a) + l *
  (\<Sum>s' \<in> UNIV. pmf (K (s,a)) s' * v s'))"

lemma GS_rec_fun_eq_GS_iter:
  assumes "\<forall>s' < s. v_next s' = GS_rec_fun v s'" "\<forall>s' \<in> {s'. s \<le> s'}. v_next s' = v s'"
  shows "GS_rec_fun v s = GS_rec_iter v_next s"
proof -
  have "{s'. s' < s} \<union> {s'. s \<le> s'} = UNIV"
    by auto
  hence *: "(\<Sum>s'<s. f s') + (\<Sum>s'\<in>Collect ((\<le>) s). f s') = (\<Sum>s' \<in> UNIV. f s')" for f :: "'s \<Rightarrow> real"
    by (subst sum.union_disjoint[symmetric]) (auto simp add: lessThan_def)
  have "GS_rec_fun v s = (\<Squnion>a\<in>A s. r (s, a) + l * ((\<Sum>s'<s. pmf (K (s, a)) s' * v_next s') + (\<Sum>s'\<in>Collect ((\<le>) s). pmf (K (s, a)) s' * v s')))"
    using assms 
    by (subst GS_rec_fun.simps) auto
  also have "\<dots> = (\<Squnion>a\<in>A s. r (s, a) + l * ((\<Sum>s'<s. pmf (K (s, a)) s' * v_next s') + (\<Sum>s'\<in>Collect ((\<le>) s). pmf (K (s, a)) s' * v_next s')))"
    using assms
    by auto
  also have "\<dots> = GS_rec_iter v_next s"
    by (auto simp: * GS_rec_iter_def)
  finally show ?thesis .
qed

lemma foldl_upd_notin: "x \<notin> set X \<Longrightarrow> foldl (\<lambda>f y. f(y := g f y)) c X x = c x"
  by (induction X arbitrary: c) auto

lemma foldl_upd_notin': "x \<notin> set Y \<Longrightarrow> foldl (\<lambda>f y. f(y := g f y)) c (X@Y) x = foldl (\<lambda>f y. f(y := g f y)) c X x"
  by (induction X arbitrary: x c Y) (auto simp add: foldl_upd_notin)

lemma sorted_list_of_set_split:
  assumes "finite X"
  shows "sorted_list_of_set X = sorted_list_of_set {x \<in> X. x < y} @ sorted_list_of_set {x \<in> X. y \<le> x}"
  using assms
proof (induction "card X" arbitrary: X)
  case (Suc n X)
  have "sorted_list_of_set X = Min X # sorted_list_of_set (X - {Min X})"
    using Suc by (auto intro: sorted_list_of_set_nonempty)
  also have "\<dots> = Min X # sorted_list_of_set {x \<in> (X - {Min X}). x < y} @ sorted_list_of_set {x \<in> (X - {Min X}). y \<le> x}"
    using Suc card.remove[OF Suc(3) Min_in] card.empty
    by (fastforce simp: Suc(1))+
  also have "\<dots> = sorted_list_of_set ({x \<in> X. x < y}) @ sorted_list_of_set {x \<in> X. y \<le> x}"
  proof (cases "Min X < y")
    case True
    hence Min_eq: "Min X = Min {x \<in> X. x < y}"
      using True Suc Min_in
      by (subst eq_Min_iff) fastforce+
    have "{x \<in> (X - {Min X}). x < y} = {x \<in> X. x < y} - {Min {x \<in> X. x < y}}"
      using Min_eq by auto
    hence "Min X # sorted_list_of_set {x \<in> (X - {Min X}). x < y} = 
      Min {x \<in> X. x < y} # sorted_list_of_set ({x \<in> X. x < y} - {Min {x \<in> X. x < y}})"
      using Min_eq by auto
    also have "\<dots> = sorted_list_of_set ({x \<in> X. x < y})"
      using Suc True Min_in Min_eq
      by (subst sorted_list_of_set_nonempty[symmetric]) fastforce+
    finally have "Min X # sorted_list_of_set {x \<in> (X - {Min X}). x < y} = sorted_list_of_set ({x \<in> X. x < y})".
    hence "Min X # sorted_list_of_set {x \<in> (X - {Min X}). x < y} @ sorted_list_of_set {x \<in> (X - {Min X}). y \<le> x} = 
      sorted_list_of_set ({x \<in> X. x < y}) @ sorted_list_of_set {x \<in> (X - {Min X}). y \<le> x}"
      by auto
    then show ?thesis
      using True
      by (auto simp: append_Cons[symmetric] simp del: append_Cons dest!: leD intro: arg_cong)
  next
    case False
    have Min_eq: "Min X = Min {x \<in> X. y \<le> x}"
      using False Suc Min_in
      by (subst eq_Min_iff) (fastforce simp: linorder_class.not_less)+
    have 2: "{x \<in> (X - {Min X}). y \<le> x} = {x \<in> X. y \<le> x} - {Min {x \<in> X. y \<le> x}}"
      using Min_eq by auto
    have "x \<in> X \<Longrightarrow> \<not> x < y" for x
      using False Min_less_iff Suc(3) by blast
    hence "{x \<in> X. x < y} = {}" 
      by auto
    hence "Min X # sorted_list_of_set {x \<in> X - {Min X}. x < y} @ sorted_list_of_set {x \<in> X - {Min X}. y \<le> x} =
      Min X # sorted_list_of_set {x \<in> X - {Min X}. y \<le> x}"
      using Suc by auto
    also have "\<dots> = Min {x \<in> X. y \<le> x} # sorted_list_of_set ({x \<in> X. y \<le> x} - {Min {x \<in> X. y \<le> x}})"
      using Min_eq 2
      by auto
    also have "\<dots> = sorted_list_of_set ({x \<in> X. y \<le> x})"      
      using Suc False Min_in Min_eq
      by (subst sorted_list_of_set_nonempty[symmetric]) fastforce+
    also have "\<dots> = sorted_list_of_set ({x \<in> X. x < y})@ sorted_list_of_set ({x \<in> X. y \<le> x})"
      by (simp add: \<open>{x \<in> X. x < y} = {}\<close>)
    finally show ?thesis.
  qed
  finally show ?case.
qed auto

lemma sorted_list_of_set_split':
  assumes "finite X"
  shows "sorted_list_of_set X = sorted_list_of_set {x \<in> X. x \<le> y} @ sorted_list_of_set {x \<in> X. y < x}"
  using sorted_list_of_set_split[of X]
proof (cases "\<exists>x \<in> X. y < x")
  case True
  hence "{x \<in> X. x \<le> y} = {x \<in> X. x < Min {x \<in> X. y < x}}"
    using assms True by (subst Min_gr_iff) auto
  moreover have "{x \<in> X. y < x} = {x \<in> X. Min {x \<in> X. y < x} \<le>  x}"
    using assms True
    by (subst Min_le_iff) auto
  ultimately show ?thesis
    using sorted_list_of_set_split[OF assms, of "Min {x \<in> X. y < x}"]
    by auto
next
  case False
  hence *: "{x \<in> X. y < x} = {}" "{x \<in> X. x \<le> y} = X"
    by (auto simp add:linorder_class.not_less)
  thus ?thesis
    using False
    by (auto simp: *)
qed

lemma GS_rec_fun_code: "GS_rec_fun v s = foldl (\<lambda>v s. v(s := GS_rec_iter v s)) v (sorted_list_of_set {..s}) s"
proof (induction s rule: less_induct)
  case (less s)
  have "foldl (\<lambda>v s. v(s := GS_rec_iter v s)) v (sorted_list_of_set {..s}) s
    = foldl (\<lambda>v s. v(s := GS_rec_iter v s)) v (sorted_list_of_set {x \<in> {..s}. x < s} @ sorted_list_of_set {x \<in> {..s}. s \<le> x}) s"
    by (subst sorted_list_of_set_split[of _ s]) auto
  also have "\<dots> = foldl (\<lambda>v s. v(s := GS_rec_iter v s)) v (sorted_list_of_set {..<s} @ sorted_list_of_set {s}) s"
  proof -
    have "{x \<in> {..s}. x <s} = {..<s}" "{x \<in> {..s}. s \<le> x} = {s}"
      by auto
    thus ?thesis by auto
  qed
  also have "\<dots> =  GS_rec_iter (foldl (\<lambda>v s. v(s := GS_rec_iter v s)) v (sorted_list_of_set {..<s})) s"
    by auto
  also have "\<dots> = GS_rec_fun v s"
  proof (intro GS_rec_fun_eq_GS_iter[symmetric], safe, goal_cases)
    case (1 s')
    assume "s' < s"
    hence *: "(Collect ((<) s')) \<noteq> {}" 
      by auto
    hence "{x \<in> {..<s}. x < Min (Collect ((<) s'))} = {..s'}"
      using leI 1
      by (auto simp add: Min_gr_iff[OF finite])
    moreover have "{x \<in> {..<s}. Min (Collect ((<) s')) \<le> x} = {s'<..<s}"
      using *
      by (auto simp add: Min_le_iff[OF finite])
    ultimately have "foldl (\<lambda>v s. v(s := GS_rec_iter v s)) v (sorted_list_of_set {..<s}) s' 
  = foldl (\<lambda>v s. v(s := GS_rec_iter v s)) v (sorted_list_of_set {..s'} @ sorted_list_of_set {s'<..<s}) s'"
      by (subst sorted_list_of_set_split[of _ "Min{s. s' < s}"]) auto
    also have "\<dots> =  GS_rec_fun v s'"
      using "1" less.IH by (subst foldl_upd_notin') fastforce+
    finally show ?case.
  qed (auto intro: foldl_upd_notin)
  finally show ?case
    by metis
qed

lemma GS_rec_fun_code': "GS_rec_fun v s = foldl (\<lambda>v s. v(s := GS_rec_iter v s)) v (sorted_list_of_set UNIV) s"
proof (cases "s = Max UNIV")
  case True
  then show ?thesis 
    by (auto simp: GS_rec_fun_code atMost_def)
next
  case False
  hence *: "(Collect ((<) s)) \<noteq> {}"
    by (auto simp: not_le eq_Max_iff[OF finite])
  hence "{x. x < Min (Collect ((<) s))} = {..s}"
    by (auto simp: Min_less_iff[OF finite *] intro: leI)
  then show ?thesis
    unfolding sorted_list_of_set_split[of UNIV "Min{s'. s < s'}", OF finite] GS_rec_fun_code 
    by (subst foldl_upd_notin'[of s]) auto
qed

lemma GS_rec_fun_code'': "GS_rec_fun v = foldl (\<lambda>v s. v(s := GS_rec_iter v s)) v (sorted_list_of_set UNIV)"
  using GS_rec_fun_code' by auto

lemma GS_rec_eq_elem: "GS_rec v $ s = GS_rec_fun (vec_nth v) s"
  unfolding GS_rec_def
  by auto



lemma GS_rec_step_elem: "GS_rec_step d v $ s = r (s, d s) + 
  l * ((\<Sum>s' < s. pmf (K (s, d s)) s' * GS_rec v $ s') + 
  (\<Sum>s' \<in> {s'. s \<le> s'}. pmf (K (s, d s)) s' * v $ s'))"
  unfolding GS_rec_step_def P_upper_def P_lower_def lessThan_def P_dec_elem matrix_vector_mult_def
  by (auto simp: sum.If_cases algebra_simps if_distrib[of "\<lambda>x. _ $ _ * x"])

lemma is_arg_max_GS_rec_step_act:
  assumes "d \<in>D\<^sub>D" "is_arg_max (\<lambda>a. GS_rec_step (d'(s := a)) v $ s) (\<lambda>a. a \<in>A s) a" 
  shows "is_arg_max (\<lambda>d. GS_rec_step d v $ s) (\<lambda>d. d \<in>D\<^sub>D) (d(s := a))"
  using assms
  unfolding GS_rec_step_elem is_arg_max_linorder is_dec_det_def
  by auto

lemma is_arg_max_GS_rec_step_act':
  assumes "d \<in>D\<^sub>D" "is_arg_max (\<lambda>a. GS_rec_step (d'(s := a)) v $ s) (\<lambda>a. a \<in>A s) (d s)" 
  shows "is_arg_max (\<lambda>d. GS_rec_step d v $ s) (\<lambda>d. d \<in>D\<^sub>D) d"
  using is_arg_max_GS_rec_step_act[OF assms]
  by fastforce

lemma
  is_arg_max_GS_rec: 
  assumes "\<And>s. is_arg_max (\<lambda>d. GS_rec_step d v $ s) (\<lambda>d. d \<in> D\<^sub>D) d"
  shows "GS_rec v = GS_rec_step d v"
  using arg_max_SUP[OF assms]
  by (auto simp: vec_eq_iff GS_rec_eq_vec )

lemma
  is_arg_max_GS_rec': 
  assumes "is_arg_max (\<lambda>d. GS_rec_step d v $ s) (\<lambda>d. d \<in> D\<^sub>D) d"
  shows "GS_rec v $ s = GS_rec_step d v $ s"
  using assms 
  by (auto simp: GS_rec_eq_vec arg_max_SUP[symmetric])

lemma
  GS_rec_eq_GS_inv: 
  assumes "\<And>s. is_arg_max (\<lambda>d. GS_rec_step d v $ s) (\<lambda>d. d \<in> D\<^sub>D) d"
  shows "GS_rec v = GS_inv d v"
proof -
  have "GS_rec v = GS_rec_step d v"
    using is_arg_max_GS_rec[OF assms] 
    by auto
  hence "GS_rec v = r_vec d + R_mat d *v v + (l *\<^sub>R P_lower d) *v GS_rec v"
    unfolding R_mat_def GS_rec_step_def
    by (auto simp: scaleR_matrix_vector_assoc algebra_simps)
  hence "Q_mat d *v GS_rec v = r_vec d + R_mat d *v v"
    unfolding Q_mat_def
    by (metis add_diff_cancel matrix_vector_mul_lid matrix_vector_mult_diff_rdistrib)
  hence "(matrix_inv (Q_mat d) ** Q_mat d) *v GS_rec v = matrix_inv (Q_mat d) *v (r_vec d + R_mat d *v v)"
    by (metis matrix_vector_mul_assoc)
  thus "GS_rec v = GS_inv d v" 
    using splitting_gauss
    unfolding GS_inv_def is_splitting_blin_def
    by (subst (asm) matrix_inv_left) (fastforce intro: blinfun_to_matrix_inverse(1))+
qed


lemma
  GS_rec_step_eq_GS_inv: 
  assumes "\<And>s. is_arg_max (\<lambda>d. GS_rec_step d v $ s) (\<lambda>d. d \<in> D\<^sub>D) d"
  shows "GS_rec_step d v = GS_inv d v"
  using GS_rec_eq_GS_inv[OF assms] is_arg_max_GS_rec[OF assms]
  by auto

lemma strict_lower_triangular_mat_mult:
  assumes "strict_lower_triangular_mat M" "\<And>i. i < j \<Longrightarrow> v $ i = v' $ i"
  shows "(M *v v) $ j = (M *v v') $ j"
proof -
  have "(M *v v) $ j = (\<Sum>i\<in>UNIV. (if j \<le> i then 0 else  M $ j $ i * v $ i))"
    using assms unfolding strict_lower_triangular_mat_def
    by (auto simp: matrix_vector_mult_def intro!: sum.cong)
  also have "\<dots> = (\<Sum>i\<in>UNIV. (if j \<le> i then 0 else  M $ j $ i * v' $ i))"
    using assms
    by (auto intro!: sum.cong)
  also have "\<dots> = (M *v v') $ j"
    using assms unfolding strict_lower_triangular_mat_def
    by (auto simp: matrix_vector_mult_def intro!: sum.cong)
  finally show ?thesis.
qed

lemma Q_mat_invertible: "invertible (Q_mat d)"
  by (meson blinfun_to_matrix_inverse(1) is_splitting_blin_def splitting_gauss)

lemma GS_eq_GS_inv:
  assumes "\<And>s. s \<le> k \<Longrightarrow> is_arg_max (\<lambda>d. GS_rec_step d v $ s) (\<lambda>d. d \<in> D\<^sub>D) d"
  assumes "s \<le> k"
  shows "GS_rec_step d v $ s = GS_inv d v $ s"
proof -
  have *: "GS_rec v $ s = GS_rec_step d v $ s" if "s \<le> k" for s
    using assms is_arg_max_GS_rec' that by presburger
  hence "GS_rec v $ s = (r_vec d + R_mat d *v v + (l *\<^sub>R P_lower d) *v GS_rec v) $ s" 
    if "s \<le> k" for s
    unfolding R_mat_def GS_rec_step_def using that
    by (simp add: scaleR_matrix_vector_assoc pth_6)
  hence "(Q_mat d *v GS_rec v) $ s = (r_vec d + R_mat d *v v) $ s" if "s \<le> k" for s
    unfolding Q_mat_def using that
    by (simp add: matrix_vector_mult_diff_rdistrib)
  hence "(matrix_inv (Q_mat d) *v (Q_mat d *v GS_rec v)) $ s = 
    (matrix_inv (Q_mat d) *v ((r_vec d + R_mat d *v v))) $ s"
    using assms lt_Q_inv by (auto intro: lower_triangular_mat_mult)
  thus "GS_rec_step d v $ s = GS_inv d v $ s"
    unfolding GS_inv_def
    using matrix_inv_left[OF Q_mat_invertible] assms  *
    by (auto simp: matrix_vector_mul_assoc)
qed

lemma is_arg_max_GS_imp_splitting':
  assumes "\<And>s. s \<le> k \<Longrightarrow> is_arg_max (\<lambda>d. GS_rec_step d v $ s) (\<lambda>d. d \<in> D\<^sub>D) d"
  assumes "s \<le> k"
  shows "is_arg_max (\<lambda>d. GS_inv d v $ s) (\<lambda>d. d \<in> D\<^sub>D) d"
  using assms
proof (induction k arbitrary: s rule: less_induct)
  case (less x)
  have d: "d \<in> D\<^sub>D"
    using assms(1) is_arg_max_linorderD by fast
  have "is_arg_max (\<lambda>a. GS_inv (d(s := a)) v $ s) (\<lambda>a. a \<in> A s) (d s)" if "s \<le> x" for s
  proof -
    have "is_arg_max (\<lambda>a. GS_rec_step (d(s := a)) v $ s) (\<lambda>a. a \<in> A s) (d s)"
      using less(2)[OF that]
      unfolding is_dec_det_def is_arg_max_linorder
      by simp
    hence *: "is_arg_max (\<lambda>a. r (s, a) + l * ((P_lower (d(s := a)) *v GS_rec v) $ s + 
      (P_upper (d(s := a)) *v v) $ s)) (\<lambda>a. a \<in> A s) (d s)"
      unfolding GS_rec_step_def
      by auto
    have "is_arg_max (\<lambda>a. r (s, a) + l * ((P_lower (d(s := a)) *v GS_inv (d(s := a)) v) $ s + 
      (P_upper (d(s := a)) *v v) $ s)) (\<lambda>a. a \<in> A s) (d s)"
    proof -
      have "((P_lower (d(s := a)) *v GS_rec v) $ s = (P_lower (d(s := a)) *v GS_rec_step d v) $ s)" for a
        using is_arg_max_GS_rec' less(2) that
        by (auto intro!: lower_triangular_mat_mult[OF lt_P_lower])
      moreover have "((P_lower (d(s := a)) *v GS_rec_step d v) $ s) = (P_lower (d(s := a)) *v GS_inv d v) $ s" for a      
        using less(2) that GS_eq_GS_inv
        by (fastforce intro!: lower_triangular_mat_mult[OF lt_P_lower])
      moreover have "(P_lower (d(s := a)) *v GS_inv d v) $ s = (P_lower (d(s := a)) *v GS_inv (d(s := a)) v) $ s" for a
        using GS_indep_high_states[of _ d "d(s := a)"] 
        by (fastforce intro!: strict_lower_triangular_mat_mult[OF slt_P_lower] dest!: leD)
      ultimately show ?thesis
        using *
        by auto
    qed
    hence "is_arg_max (\<lambda>a. ((r_vec (d(s := a)) + 
      l *\<^sub>R ((P_lower (d(s := a)) *v GS_inv (d(s := a)) v) + 
      (P_upper (d(s := a)) *v v))) $ s)) (\<lambda>a. a \<in> A s) (d s)"
      by auto
    hence **: "is_arg_max (\<lambda>a. ((r_vec (d(s := a)) + R_mat (d(s := a)) *v v) + 
      ((l *\<^sub>R P_lower (d(s := a))) *v GS_inv (d(s := a)) v) ) $ s) (\<lambda>a. a \<in> A s) (d s)"
      unfolding R_mat_def
      by (auto simp: algebra_simps  scaleR_matrix_vector_assoc)
    show ?thesis
    proof- 
      have "(r_vec d + R_mat d *v v) = Q_mat d *v (GS_inv d v)" for d v
        unfolding GS_inv_def
        by (simp add: Q_mat_invertible matrix_inv_right matrix_vector_mul_assoc)
      hence "((r_vec d + R_mat d *v v) + ((l *\<^sub>R P_lower d)) *v GS_inv d v) = GS_inv d v" for d
        unfolding Q_mat_def 
        by (auto simp: matrix_vector_mult_diff_rdistrib)
      thus ?thesis 
        using **
        by presburger
    qed
  qed
  thus ?case
    using less d
    by (fastforce intro!: is_am_GS_inv_extend[of x v d "d x" s, unfolded fun_upd_triv])
qed

lemma is_am_GS_rec_step_indep:
  assumes "d s = d' s"
  assumes "is_arg_max (\<lambda>d. GS_rec_step d v $ s) (\<lambda>d. d \<in> D\<^sub>D) d"
  shows "GS_rec v $ s = GS_rec_step d' v $ s"
proof -
  have "GS_rec v $ s = GS_rec_step d v $ s"
    using is_arg_max_GS_rec' assms(2) by blast
  moreover have "GS_rec_step d v $ s = GS_rec_step d' v $ s"
    using GS_rec_step_elem assms(1) by fastforce
  ultimately show ?thesis by auto
qed

lemma is_am_GS_rec_step_indep':
  assumes "d s = d' s"
  assumes "is_arg_max (\<lambda>d. GS_rec_step d v $ s) (\<lambda>d. d \<in> D\<^sub>D) d"
  shows "GS_rec v $ s = GS_rec_step d' v $ s"
proof -
  have "GS_rec v $ s = GS_rec_step d v $ s"
    using is_arg_max_GS_rec' assms(2) by blast
  moreover have "GS_rec_step d v $ s = GS_rec_step d' v $ s"
    using GS_rec_step_elem assms(1) by fastforce
  ultimately show ?thesis by auto
qed

lemma is_arg_max_GS_imp_splitting'':
  assumes "\<And>s. s \<le> k \<Longrightarrow> is_arg_max (\<lambda>d. GS_inv d v $ s) (\<lambda>d. d \<in> D\<^sub>D) d"
  assumes "s \<le> k"
  shows "is_arg_max (\<lambda>d. GS_rec_step d v $ s) (\<lambda>d. d \<in> D\<^sub>D) d \<and> GS_inv d v $ s = GS_rec v $ s"
  using assms
proof (induction k arbitrary: s rule: less_induct)
  case (less x)
  have d[simp]: "d \<in> D\<^sub>D" using assms unfolding is_arg_max_linorder by blast

  have "is_arg_max (\<lambda>a. GS_rec_step (d(s := a)) v $ s) (\<lambda>a. a \<in> A s) (d s)" if "s \<le> x" for s
  proof -
    have "is_arg_max (\<lambda>a. GS_inv (d(s := a)) v $ s) (\<lambda>a. a \<in> A s) (d s)"
      using less(2)[OF that] 
      unfolding is_dec_det_def is_arg_max_linorder
      by auto
    hence *: "is_arg_max (\<lambda>a. (r_vec (d(s := a)) + l *\<^sub>R (P_lower (d(s := a)) *v (GS_inv (d(s := a)) v) + 
      P_upper (d(s := a)) *v v)) $ s) (\<lambda>a. a \<in> A s) (d s)"
      by (subst (asm) GS_inv_rec) (auto simp: add.commute)

    hence *: "is_arg_max (\<lambda>a. (r_vec (d(s := a)) + l *\<^sub>R (P_lower (d(s := a)) *v (GS_inv d v) + P_upper (d(s := a)) *v v)) $ s) (\<lambda>a. a \<in> A s) (d s)"
    proof -
      have "(P_lower (d(s := a)) *v (GS_inv (d(s := a)) v)) $ s = (P_lower (d(s := a)) *v (GS_inv d v)) $ s" for a
        using GS_indep_high_states[of _ "d(s := a)" d v]
        by (rule strict_lower_triangular_mat_mult[OF slt_P_lower]) (metis array_rules(4) leD)
      thus ?thesis using * by auto
    qed
    thus "is_arg_max (\<lambda>a. GS_rec_step (d(s := a)) v $ s) (\<lambda>a. a \<in> A s) (d s)"
    proof -
      have "(P_lower (d(s := a)) *v (GS_inv d v)) $ s = (P_lower (d(s := a)) *v (GS_rec v)) $ s" for a
        using less(1) less(2)that
        by (intro strict_lower_triangular_mat_mult[OF slt_P_lower]) force
      thus ?thesis 
        using *
        unfolding GS_rec_step_def
        by auto
    qed
  qed
  hence *: "\<And>s. s \<le> x \<Longrightarrow> is_arg_max (\<lambda>d. GS_rec_step d v $ s) (\<lambda>d. d \<in> D\<^sub>D) d"
    using d
    by (intro is_arg_max_GS_rec_step_act'[of d d]) auto
  moreover have "GS_inv d v $ s = GS_rec v $ s" if "s \<le> x" for s
  proof -
    have "GS_rec v $ s = GS_rec_step d v $ s"
      using *[OF that]
      by (auto simp: is_arg_max_GS_rec')
    thus ?thesis
      using * GS_eq_GS_inv that by presburger
  qed
  ultimately show ?case using less by blast
qed

lemma is_arg_max_GS_imp_splitting''':
  assumes "\<And>s. s \<le> k \<Longrightarrow> is_arg_max (\<lambda>d. GS_inv d v $ s) (\<lambda>d. d \<in> D\<^sub>D) d"
  assumes "s \<le> k"
  shows "is_arg_max (\<lambda>d. GS_rec_step d v $ s) (\<lambda>d. d \<in> D\<^sub>D) d"
  using assms  is_arg_max_GS_imp_splitting'' by blast

lemma is_arg_max_GS_imp_splitting:
  assumes "\<And>s. is_arg_max (\<lambda>d. GS_rec_step d v $ s) (\<lambda>d. d \<in> D\<^sub>D) d"
  shows "is_arg_max (\<lambda>d. GS_inv d v $ k) (\<lambda>d. d \<in> D\<^sub>D) d"
  using assms is_arg_max_GS_imp_splitting'[of "Max UNIV"]
  by (simp add: is_arg_max_linorder)

lemma is_arg_max_gs_iff:
  assumes "d \<in> D\<^sub>D" 
  shows " (\<forall>s \<le> k. is_arg_max (\<lambda>d. GS_inv d v $ s) (\<lambda>d. d \<in> D\<^sub>D) d) \<longleftrightarrow>
    (\<forall>s \<le> k. is_arg_max (\<lambda>d. GS_rec_step d v $ s) (\<lambda>d. d \<in> D\<^sub>D) d)"
  using is_arg_max_GS_imp_splitting' is_arg_max_GS_imp_splitting''  
  by meson

lemma GS_opt_indep_high:
  assumes "(\<And>s'. s' < s \<Longrightarrow> is_arg_max (\<lambda>d. GS_rec_step d v $ s') is_dec_det d)" "s' < s" "a \<in> A s"
  shows "is_arg_max (\<lambda>d. GS_rec_step d v $ s') is_dec_det (d(s := a))"
proof (rule is_arg_max_linorderI)
  fix y
  assume "is_dec_det y"
  hence "GS_rec_step y v $ s' \<le> r (s', d s') + l * (P_lower d *v GS_rec v) $ s' + l * (P_upper d *v v) $ s'"
    using is_arg_max_linorderD[OF assms(1)]
    by (auto simp: GS_rec_step_def algebra_simps assms(2))
  also have "\<dots> = r (s', (d(s := a)) s') + l * (P_lower (d(s := a)) *v GS_rec v) $ s' + l * (P_upper (d(s := a)) *v v) $ s'"
  proof -
    have "(P_lower d *v GS_rec v) $ s' = (P_lower (d(s := a)) *v GS_rec v) $ s'"
      using assms
      by (fastforce simp: matrix_vector_mult_def P_lower_def P_dec_elem intro!: sum.cong)
    moreover have "(P_upper d *v v) $ s' = (P_upper (d(s := a)) *v v) $ s'"
      using assms
      by (fastforce simp: matrix_vector_mult_def P_upper_def P_dec_elem intro!: sum.cong)
    ultimately show ?thesis
      using assms(2) by force
  qed
  also have "\<dots> = GS_rec_step (d(s := a)) v $ s'"
    by (auto simp: GS_rec_step_def algebra_simps)
  finally show "GS_rec_step y v $ s' \<le> GS_rec_step (d(s := a)) v $ s'".
next
  show "is_dec_det (d(s := a))"
    using is_arg_max_linorderD[OF assms(1)[OF assms(2)]] assms(3) is_dec_det_def 
    by fastforce
qed

lemma mult_mat_vec_nth: "(X *v x) $ i = scalar_product (row i X) x"
  by (simp add: matrix_vector_mult_def row_def scalar_product_def)

lemma ext_GS_opt_le:
  assumes "(\<And>s'. s' < s \<Longrightarrow> is_arg_max (\<lambda>d. GS_rec_step d v $ s') (\<lambda>d. d \<in> D\<^sub>D) d)"
    and "is_arg_max (\<lambda>a. GS_rec_step (d(s := a)) v $ s) (\<lambda>a. a \<in> A s) a" "s' \<le> s"
    and "d \<in> D\<^sub>D"
  shows "is_arg_max (\<lambda>d. GS_rec_step d v $ s') (\<lambda>d. d \<in> D\<^sub>D) (d(s := a))"
  using assms is_arg_max_GS_rec_step_act is_arg_max_linorderD(1)
  by (cases "s = s'") (auto intro!: GS_opt_indep_high)

lemma ex_GS_opt_le:
  shows "\<exists>d. (\<forall>s' \<le> s. is_arg_max (\<lambda>d. GS_rec_step d v $ s') (\<lambda>d. d \<in> D\<^sub>D) d)"
proof (induction s rule: less_induct)
  case (less x)
  show ?case
  proof (cases "\<exists>y. y < x")
    case True
    hence "{y. y < x} \<noteq> {}" 
      by auto
    have 1: "\<And>y. y \<le> Max {y. y < x} \<longleftrightarrow> y < x"
      using True
      by (auto simp: Max_ge_iff[OF finite])
    obtain d where d: "is_arg_max (\<lambda>d. GS_rec_step d v $ s') (\<lambda>d. d \<in> D\<^sub>D) d" if "s'< x" for s'
      using less[of "Max {y. y < x}"] 1
      by auto
    obtain a where a: "is_arg_max (\<lambda>a. GS_rec_step (d(x := a)) v $ x) (\<lambda>a. a \<in> A x) a"
      using finite_is_arg_max[OF finite A_ne] by fastforce
    hence d': "is_arg_max (\<lambda>d. GS_rec_step d v $ s') (\<lambda>d. d \<in> D\<^sub>D) (d(x := a))" if "s' < x" for s'
      using d GS_opt_indep_high that is_arg_max_linorderD(1)[OF a]
      by simp
    have d': "is_arg_max (\<lambda>d. GS_rec_step d v $ s') (\<lambda>d. d \<in> D\<^sub>D) (d(x := a))" if "s' \<le> x" for s'
      using  that a is_arg_max_linorderD[OF d] True
      by (fastforce intro!: ext_GS_opt_le[OF d])
    thus ?thesis
      by blast
  next
    case False
    define d where "d y = (SOME a. a \<in> A y)" for y
    obtain a where a: "is_arg_max (\<lambda>a. GS_rec_step (d(x := a)) v $ x) (\<lambda>a. a \<in> A x) a"
      using finite_is_arg_max[OF finite A_ne]
      by fastforce
    have 1: "y \<le> x \<Longrightarrow> y = x" for y
      using False
      by (meson le_neq_trans)
    have "is_arg_max (\<lambda>d. GS_rec_step d v $ x) (\<lambda>d. d \<in> D\<^sub>D) (d(x := a))"
      using False a SOME_is_dec_det unfolding d_def
      by (fastforce intro!: is_arg_max_GS_rec_step_act)
    then show ?thesis
      using 1
      by blast
  qed
qed

lemma ex_GS_opt:
  shows "\<exists>d. \<forall>s. is_arg_max (\<lambda>d. GS_rec_step d v $ s) (\<lambda>d. d \<in> D\<^sub>D) d"
  using ex_GS_opt_le[of "Max UNIV"]
  by auto

lemma GS_rec_eq_GS_inv': "GS_rec v $ s = (\<Squnion>d\<in>D\<^sub>D. GS_inv d v $ s)"
proof -
  obtain d where d: "(\<And>s. is_arg_max (\<lambda>d. GS_rec_step d v $ s) (\<lambda>d. d \<in> D\<^sub>D) d)"
    using ex_GS_opt by blast
  have "(\<Squnion>d\<in>D\<^sub>D. GS_rec_step d v $ s) = GS_rec_step d v $ s"
    using d is_arg_max_GS_rec GS_rec_eq_vec
    by metis
  have "(\<Squnion>d\<in>D\<^sub>D. GS_inv d v $ s) = GS_inv d v $ s"
    using is_arg_max_GS_imp_splitting[OF d]
    by (subst arg_max_SUP[symmetric]) auto
  thus ?thesis
    using GS_rec_eq_GS_inv d 
    by presburger
qed

lemma GS_rec_fun_eq_GS_inv: "GS_rec_fun v s = (\<Squnion>d\<in>D\<^sub>D. GS_inv d (vec_lambda v) $ s)"
  using GS_rec_eq_GS_inv'[of "vec_lambda v"]
  unfolding GS_rec_def
  by (auto simp: vec_lambda_inverse)


lemma invertible_Q_GS: "invertible\<^sub>L (Q_GS d)" for d
  by (simp add: Q_mat_invertible invertible_invertible\<^sub>L_I(1))

lemma ex_opt_blinfun: "\<exists>d. \<forall>s. is_arg_max (\<lambda>d. ((inv\<^sub>L (Q_GS d)) (r_det\<^sub>b d + (R_GS d) v)) s) is_dec_det d"
proof -
  have "GS_inv d (vec_lambda v) $ s = inv\<^sub>L (Q_GS d) (r_det\<^sub>b d + R_GS d v) s" for d s
    unfolding GS_inv_def plus_bfun_def
    by (simp add: invertible_Q_GS blinfun_to_matrix_mult' blinfun_to_matrix_inverse(2)[symmetric] apply_bfun_inverse)
  moreover obtain d where "is_arg_max (\<lambda>d. GS_inv d (vec_lambda v) $ s) is_dec_det d" for s
    using ex_GS_opt[of "vec_lambda v"] is_arg_max_GS_imp_splitting
    by auto
  ultimately show ?thesis 
    by auto
qed


lemma GS_inv_blinfun_to_matrix: "((inv\<^sub>L (Q_GS d)) (r_det\<^sub>b d + R_GS d v)) = Bfun (vec_nth (GS_inv d (vec_lambda v)))"
  unfolding GS_inv_def plus_bfun_def
  by (auto simp: invertible_Q_GS blinfun_to_matrix_inverse(2)[symmetric] blinfun_to_matrix_mult'' apply_bfun_inverse )

lemma norm_GS_QR_le_disc: "norm (inv\<^sub>L (Q_GS d) o\<^sub>L R_GS d) \<le> l"
proof -
  have "norm (inv\<^sub>L (Q_GS d) o\<^sub>L R_GS d) \<le> norm (inv\<^sub>L ((\<lambda>_. id_blinfun) d) o\<^sub>L (l *\<^sub>R \<P>\<^sub>1 (mk_dec_det d))) "
  proof (rule norm_splitting_le[of "mk_dec_det d"], goal_cases)
    case 1
    then show ?case 
      unfolding is_splitting_blin_def
      using nonneg_id_blinfun zero_le_disc nonneg_\<P>\<^sub>1
      by force
  next
    case 3
    then show ?case
      unfolding R_mat_def P_upper_def Finite_Cartesian_Product.less_eq_vec_def R_GS_def
      by (auto simp: blinfun_to_matrix_scaleR nonneg_matrix_nonneg \<P>\<^sub>U_le_\<P>\<^sub>1 blinfun_le_iff scaleR_blinfun.rep_eq scaleR_left_mono)
  qed (auto simp: splitting_gauss blinfun_le_iff)
  also have "\<dots> = norm ((l *\<^sub>R \<P>\<^sub>1 (mk_dec_det d)))"
    by auto
  also have "\<dots> \<le> l"
    by auto
  finally show ?thesis.
qed

sublocale GS: MDP_QR A K r l Q_GS R_GS
  rewrites "GS.\<L>\<^sub>b_split = GS_rec_fun\<^sub>b"
proof -
  have "(\<Squnion>d\<in>D\<^sub>D. norm (inv\<^sub>L (Q_GS d) o\<^sub>L R_GS d)) < 1"
    using norm_GS_QR_le_disc ex_dec_det
    by (fastforce intro: le_less_trans[of _ l 1] intro!: cSUP_least)
  thus "MDP_QR A K r l Q_GS R_GS"
    by unfold_locales (auto simp: splitting_gauss ex_opt_blinfun)
  thus "MDP_QR.\<L>\<^sub>b_split A r Q_GS R_GS = GS_rec_fun\<^sub>b"
    by (fastforce simp: MDP_QR.\<L>\<^sub>b_split.rep_eq MDP_QR.\<L>_split_def GS_rec_fun\<^sub>b.rep_eq GS_rec_fun_eq_GS_inv GS_inv_blinfun_to_matrix)
qed

abbreviation "gs_measure \<equiv> (\<lambda>(eps, v).
    if v = \<nu>\<^sub>b_opt \<or> l = 0
    then 0
    else nat (ceiling (log (1/l) (dist v \<nu>\<^sub>b_opt) - log (1/l) (eps * (1-l) / (8 * l)))))"

lemma dist_\<L>\<^sub>b_split_lt_dist_opt: "dist v (GS_rec_fun\<^sub>b v) \<le> 2 * dist v \<nu>\<^sub>b_opt"
proof -
  have le1: "dist v (GS_rec_fun\<^sub>b v) \<le> dist v \<nu>\<^sub>b_opt + dist (GS_rec_fun\<^sub>b v) \<nu>\<^sub>b_opt"
    by (simp add: dist_triangle dist_commute)
  have le2: "dist (GS_rec_fun\<^sub>b v) \<nu>\<^sub>b_opt \<le> GS.QR_disc * dist v \<nu>\<^sub>b_opt"
    using GS.\<L>\<^sub>b_split_contraction GS.\<L>\<^sub>b_split_fix
    by (metis (no_types, lifting))
  show ?thesis
    using mult_right_mono[of GS.QR_disc 1] GS.QR_contraction
    by (fastforce intro!: order.trans[OF le2] order.trans[OF le1])
qed

lemma GS_QR_disc_le_disc: "GS.QR_disc \<le> l"
  using norm_GS_QR_le_disc ex_dec_det
  by (fastforce intro!: cSUP_least)

lemma gs_rel_dec: 
  assumes "l \<noteq> 0" "GS_rec_fun\<^sub>b v \<noteq> \<nu>\<^sub>b_opt"
  shows "\<lceil>log (1 / l) (dist (GS_rec_fun\<^sub>b v) \<nu>\<^sub>b_opt) - c\<rceil> < \<lceil>log (1 / l) (dist v \<nu>\<^sub>b_opt) - c\<rceil>"
proof -
  have "log (1 / l) (dist (GS_rec_fun\<^sub>b v) \<nu>\<^sub>b_opt) - c \<le> log (1 / l) (l * dist v \<nu>\<^sub>b_opt) - c"
    using GS.\<L>\<^sub>b_split_contraction[of _ "\<nu>\<^sub>b_opt"] GS.QR_contraction norm_GS_QR_le_disc disc_lt_one GS_QR_disc_le_disc
    by (fastforce simp: assms less_le intro!: log_le order.trans[OF GS.\<L>\<^sub>b_split_contraction[of v "\<nu>\<^sub>b_opt", simplified]] mult_right_mono)
  also have "\<dots> = log (1 / l) l + log (1/l) (dist v \<nu>\<^sub>b_opt) - c"
    using assms disc_lt_one 
    by (auto simp: less_le intro!: log_mult)
  also have "\<dots> = -(log (1 / l) (1/l)) + (log (1/l) (dist v \<nu>\<^sub>b_opt)) - c"
    using assms disc_lt_one
    by (subst log_inverse[symmetric]) (auto simp: less_le right_inverse_eq)
  also have "\<dots> = (log (1/l) (dist v \<nu>\<^sub>b_opt)) - 1 - c"
    using assms order.strict_implies_not_eq[OF disc_lt_one]
    by (auto intro!: log_eq_one neq_le_trans)
  finally have "log (1 / l) (dist (GS_rec_fun\<^sub>b v) \<nu>\<^sub>b_opt) - c \<le> log (1 / l) (dist v \<nu>\<^sub>b_opt) - 1 - c" .
  thus ?thesis
    by linarith
qed

function gs_iteration :: "real \<Rightarrow> ('s \<Rightarrow>\<^sub>b real) \<Rightarrow> ('s \<Rightarrow>\<^sub>b real)" where
  "gs_iteration eps v =
  (if 2 * l * dist v (GS_rec_fun\<^sub>b v) < eps * (1-l) \<or> eps \<le> 0 then GS_rec_fun\<^sub>b v else gs_iteration eps (GS_rec_fun\<^sub>b v))"
  by auto
termination
proof (cases "l = 0"; relation "Wellfounded.measure gs_measure")
  case False
  fix eps v
  assume h: "\<not> (2 * l * dist v (GS_rec_fun\<^sub>b v) < eps * (1 - l) \<or> eps \<le> 0)"
  show "((eps, GS_rec_fun\<^sub>b v), eps, v) \<in> Wellfounded.measure gs_measure"
  proof -
    have gt_zero[simp]: "l \<noteq> 0" "eps > 0" and dist_ge: "eps * (1 - l) \<le> dist v (GS_rec_fun\<^sub>b v) * (2 * l)"
      using h
      by (auto simp: algebra_simps)
    have v_not_opt: "v \<noteq> \<nu>\<^sub>b_opt"
      using h
      by auto
    have "log (1 / l) (eps * (1 - l) / (8 * l)) < log (1 / l) (dist v \<nu>\<^sub>b_opt)"
    proof (intro log_less)
      show "1 < 1 / l"
        by (auto intro!: mult_imp_less_div_pos intro: neq_le_trans)
      show "0 < eps * (1 - l) / (8 * l)" 
        by (auto intro!: mult_imp_less_div_pos intro: neq_le_trans)
      show "eps * (1 - l) / (8 * l) < dist v \<nu>\<^sub>b_opt" 
        using dist_pos_lt[OF v_not_opt] dist_\<L>\<^sub>b_split_lt_dist_opt[of v] gt_zero zero_le_disc 
          mult_strict_left_mono[of "dist v (GS_rec_fun\<^sub>b v)" "(4 * dist v \<nu>\<^sub>b_opt)" l]
        by (intro mult_imp_div_pos_less le_less_trans[OF dist_ge]) argo+
    qed
    thus ?thesis
      using gs_rel_dec h
      by auto
  qed
qed auto


lemma THE_fix_GS_rec_fun\<^sub>b: "(THE v. GS_rec_fun\<^sub>b v = v) = \<nu>\<^sub>b_opt"
  using GS.\<L>\<^sub>b_lim(1) GS.\<L>\<^sub>b_split_fix
  by blast+

text \<open>
The distance between an estimate for the value and the optimal value can be bounded with respect to 
the distance between the estimate and the result of applying it to @{const \<L>\<^sub>b}
\<close>
lemma contraction_\<L>_split_dist: "(1 - l) * dist v \<nu>\<^sub>b_opt \<le> dist v (GS_rec_fun\<^sub>b v)"
  using GS_QR_disc_le_disc 
  by (fastforce 
      simp: THE_fix_GS_rec_fun\<^sub>b 
      intro: order.trans[OF _ contraction_dist, of _ l] order.trans[OF GS.\<L>\<^sub>b_split_contraction] mult_right_mono)+

lemma dist_\<L>\<^sub>b_split_opt_eps:
  assumes "eps > 0" "2 * l * dist v (GS_rec_fun\<^sub>b v) < eps * (1-l)"
  shows "dist (GS_rec_fun\<^sub>b v) \<nu>\<^sub>b_opt < eps / 2"
proof -
  have "dist v \<nu>\<^sub>b_opt \<le> dist v (GS_rec_fun\<^sub>b v) / (1 - l)"
    using contraction_\<L>_split_dist
    by (simp add: mult.commute pos_le_divide_eq)
  hence "2 * l * dist v \<nu>\<^sub>b_opt \<le> 2 * l * (dist v (GS_rec_fun\<^sub>b v) / (1 - l))"
    using contraction_\<L>_dist assms mult_le_cancel_left_pos[of "2 * l"]
    by (fastforce intro!: mult_left_mono[of _ _ "2 * l"])
  hence "2 * l * dist v \<nu>\<^sub>b_opt < eps"
    by (auto simp: assms(2) pos_divide_less_eq intro: order.strict_trans1)
  hence "dist v \<nu>\<^sub>b_opt * l < eps / 2"
    by argo
  hence *: "l * dist v \<nu>\<^sub>b_opt < eps / 2"
    by (auto simp: algebra_simps)
  show "dist (GS_rec_fun\<^sub>b v) \<nu>\<^sub>b_opt < eps / 2"
    using GS.\<L>\<^sub>b_split_contraction[of v \<nu>\<^sub>b_opt] order.trans mult_right_mono[OF GS_QR_disc_le_disc zero_le_dist]
    by (fastforce intro!: le_less_trans[OF _ *])
qed
end

context MDP_ord 
begin       

lemma is_am_GS_inv_extend':
  assumes "(\<And>s. s < x \<Longrightarrow> is_arg_max (\<lambda>d. GS_inv d v $ s) (\<lambda>d. d \<in> D\<^sub>D) d)"
  assumes "is_arg_max (\<lambda>d. GS_rec_step d v $ x) (\<lambda>d. d \<in> D\<^sub>D) (d(x := a))"
  assumes "s \<le> x" "d \<in> D\<^sub>D"
  shows "is_arg_max (\<lambda>d. GS_inv d v $ s) (\<lambda>d. d \<in> D\<^sub>D) (d(x := a))"
proof -
  have a: "a \<in> A x" using assms(2) unfolding is_arg_max_linorder is_dec_det_def by (auto split: if_splits)
  have *: "\<exists>y. y < x \<Longrightarrow> s\<le>Max {y. y < x} \<longleftrightarrow> s < x" for x s :: 's
    by (auto simp: linorder_class.Max_ge_iff[OF finite])
  have "(\<And>s. s < x \<Longrightarrow> is_arg_max (\<lambda>d. GS_rec_step d v $ s) (\<lambda>d. d \<in> D\<^sub>D) d)"
    using is_arg_max_gs_iff[OF assms(4), of "Max {y. y < x}"] assms(1)
    by (cases "\<exists>y. y < x") (auto simp: *)
  hence "(\<And>s. s < x \<Longrightarrow> is_arg_max (\<lambda>d. GS_rec_step d v $ s) (\<lambda>d. d \<in> D\<^sub>D) (d(x := a)))"
    using GS_opt_indep_high a by auto
  hence "(\<And>s. s \<le> x \<Longrightarrow> is_arg_max (\<lambda>d. GS_rec_step d v $ s) (\<lambda>d. d \<in> D\<^sub>D) (d(x := a)))"
    using assms(2) antisym_conv1 by blast
  thus ?thesis
    using is_arg_max_gs_iff[of "d(x := a)" s] assms(4) assms a 
    by (intro is_arg_max_GS_imp_splitting') auto
qed

definition "opt_policy_gs' d v s = (LEAST a. is_arg_max (\<lambda>a. GS_rec_step (d(s := a)) v $ s) (\<lambda>a. a \<in> A s) a)"

definition "GS_iter a v s = r (s, a) + l * (\<Sum>s' \<in> UNIV. pmf (K(s,a)) s' * v $ s')"

definition "GS_iter_max v s = (\<Squnion>a \<in> A s. GS_iter a v s)"

lemma GS_rec_eq_iter:
  assumes "\<And>s. s < k \<Longrightarrow> v' $ s = GS_rec v $ s" "\<And>s. k \<le> s \<Longrightarrow> v' $ s = v $ s"
  shows "GS_rec_step (d(k := a)) v $ k = GS_iter a v' k"
proof -
  have "(P_lower d *v GS_rec v) $ k = (P_lower d *v v') $ k" for d
    using slt_P_lower assms
    by (auto intro!: strict_lower_triangular_mat_mult)
  moreover have "(P_upper d *v v) $ k = (P_upper d *v v') $ k" for d
    unfolding P_upper_def using assms
    by (auto simp: matrix_vector_mult_def if_distrib[of "\<lambda>x. x * _ $ _"] cong: if_cong)
  moreover have "P_lower d + P_upper d = P_dec d" for d
    by (auto simp: P_lower_def P_upper_def Finite_Cartesian_Product.vec_eq_iff)
  ultimately show ?thesis
    unfolding vector_add_component[symmetric] matrix_vector_mult_diff_rdistrib[symmetric] GS_rec_step_def
      matrix_vector_mult_def P_dec_elem P_lower_def P_upper_def GS_iter_def
    by (fastforce simp: sum.distrib[symmetric] intro!: sum.cong)
qed

lemma GS_rec_eq_iter_max:
  assumes "\<And>s. s < k \<Longrightarrow> v' $ s = GS_rec v $ s" "\<And>s. k \<le> s \<Longrightarrow> v' $ s = v $ s"
  shows "GS_rec v $ k = GS_iter_max v' k"
  using GS_rec_eq_iter[OF assms] GS_rec_eq'[of _ _ undefined] GS_iter_max_def 
  by auto

definition "GS_iter_arg_max v s = (LEAST a. is_arg_max (\<lambda>a. GS_iter a v s) (\<lambda>a. a \<in> A s) a)"

definition "GS_rec_am_code v d s = foldl (\<lambda>vd s. vd(s := (GS_iter_max (\<chi> s. fst (vd s)) s,
  GS_iter_arg_max (\<chi> s. fst (vd s)) s))) (\<lambda>s. (v $ s, d s)) (sorted_list_of_set {..s}) s"
definition "GS_rec_am_code' v d s = foldl (\<lambda>vd s. vd(s := (GS_iter_max (\<chi> s. fst (vd s)) s,
  GS_iter_arg_max (\<chi> s. fst (vd s)) s))) (\<lambda>s. (v $ s, d s)) (sorted_list_of_set UNIV) s"

lemma GS_rec_am_code': "GS_rec_am_code = GS_rec_am_code'"
proof -
  have *: "sorted_list_of_set UNIV = sorted_list_of_set{..s} @ sorted_list_of_set{s<..}" for s :: 's
    using sorted_list_of_set_split'[OF finite, of UNIV s]
    by (auto simp: atMost_def greaterThan_def)
  have "GS_rec_am_code v d s = GS_rec_am_code' v d s" for v d s
    unfolding GS_rec_am_code_def GS_rec_am_code'_def *[of s]
    by (fastforce intro!: foldl_upd_notin'[symmetric])
  thus ?thesis 
    by blast
qed

lemma opt_policy_gs'_eq_GS_iter:
  assumes "\<And>s. s < k \<Longrightarrow> v' $ s = GS_rec v $ s" "\<And>s. k \<le> s \<Longrightarrow> v' $ s = v $ s"
  shows "opt_policy_gs' d v k = GS_iter_arg_max v' k"
  unfolding opt_policy_gs'_def GS_iter_arg_max_def
  by (subst GS_rec_eq_iter[OF assms, of k d]) auto

lemma opt_policy_gs'_eq_GS_iter':
  "opt_policy_gs' d v k = GS_iter_arg_max (\<chi> s. if s < k then GS_rec v $ s else v $ s) k"
  using opt_policy_gs'_eq_GS_iter
  by (simp add: leD)

lemma opt_policy_gs'_is_dec_det: "opt_policy_gs' d v \<in> D\<^sub>D"
  unfolding opt_policy_gs'_def is_dec_det_def
  by (auto intro: LeastI2_ex[OF finite_is_arg_max[OF finite A_ne]])
  
lemma opt_policy_gs'_is_arg_max: "is_arg_max (\<lambda>d. GS_inv d v $ s) (\<lambda>d. d \<in> D\<^sub>D) (opt_policy_gs' d v)"
proof (induction arbitrary: d rule: less_induct)
  case (less x)
  have "s < x \<Longrightarrow> is_arg_max (\<lambda>d. GS_inv d v $ s) (\<lambda>d. d \<in> D\<^sub>D) (opt_policy_gs' d v)" for d s
    using less
    by auto
  hence *:"s < x \<Longrightarrow> is_arg_max (\<lambda>d. GS_rec_step d v $ s) (\<lambda>d. d \<in> D\<^sub>D) (opt_policy_gs' d v)" for d s
    by (intro is_arg_max_GS_imp_splitting''') auto
  have "is_arg_max (\<lambda>a. GS_rec_step (d(x := a)) v $ x) (\<lambda>a. a \<in> A x) (opt_policy_gs' d v x)" for d
    unfolding opt_policy_gs'_def
    using finite_is_arg_max[OF _ A_ne]
    by (auto intro: LeastI_ex)
  hence "is_arg_max (\<lambda>d. GS_rec_step d v $ x) (\<lambda>d. d \<in> D\<^sub>D) (opt_policy_gs' d v)" for d
    using opt_policy_gs'_is_dec_det
    by (intro is_arg_max_GS_rec_step_act') auto
  hence "s \<le> x \<Longrightarrow> is_arg_max (\<lambda>d. GS_rec_step d v $ s) (\<lambda>d. d \<in> D\<^sub>D) (opt_policy_gs' d v)" for d s
    using *
    by (auto simp: order.order_iff_strict)
  hence "s \<le> x \<Longrightarrow> is_arg_max (\<lambda>d. GS_inv d v $ s) (\<lambda>d. d \<in> D\<^sub>D) (opt_policy_gs' d v)" for d s
    using is_arg_max_GS_imp_splitting'
    by blast
  thus ?case
    by blast
qed

lemma "GS_rec_am_code v d s = (GS_rec v $ s, opt_policy_gs' d v s)"
proof (induction s arbitrary: d rule: less_induct)
  case (less x)
  show ?case 
  proof (cases "\<exists>x'. x' < x")
    case True
    let ?f = "(\<lambda>vd s. vd(s := (GS_iter_max (\<chi> s. fst (vd s)) s,  GS_iter_arg_max (\<chi> s. fst (vd s)) s)))"
    define x' where "x' = Max {x'. x' < x}"
    let ?old = "(foldl ?f (\<lambda>s. (v $ s, d s)) (sorted_list_of_set {..x'}))"
    have 1: "s < x \<Longrightarrow> (s \<notin> set (sorted_list_of_set {s' \<in> {..x'}. s < s'}))" for s :: 's
      by auto
    have "s < x \<Longrightarrow> foldl ?f (\<lambda>s. (v $ s, d s)) (sorted_list_of_set {..x'}) s = 
      foldl ?f (\<lambda>s. (v $ s, d s)) (sorted_list_of_set {s' \<in> {..x'}. s' \<le> s} @ sorted_list_of_set {s' \<in> {..x'}. s < s'}) s" for s
      by (subst sorted_list_of_set_split'[symmetric, OF finite]) blast
    hence "s < x \<Longrightarrow> foldl ?f (\<lambda>s. (v $ s, d s)) (sorted_list_of_set {..x'}) s = 
      foldl ?f (\<lambda>s. (v $ s, d s)) (sorted_list_of_set {s' \<in> {..x'}. s' \<le> s}) s" for s
      using foldl_upd_notin'[OF 1]
      by fastforce
    hence 1: "s < x \<Longrightarrow> foldl ?f (\<lambda>s. (v $ s, d s)) (sorted_list_of_set {..x'}) s = 
      foldl ?f (\<lambda>s. (v $ s, d s)) (sorted_list_of_set {..s}) s" for s
      unfolding x'_def
      using True
      by (auto simp: atMost_def Max_ge_iff[OF finite]) meson
    have fst_IH: "fst (?old s) = GS_rec v $ s" if "s < x" for s
      using 1[OF that] less[unfolded GS_rec_am_code_def] that
      by auto
    have fst_IH': "fst (?old s) = v $ s" if "x \<le> s" for s 
      using True that
      by (subst foldl_upd_notin) (auto simp: x'_def  Max_ge_iff)
    have fst_IH'': "fst (?old s) = (if s < x then GS_rec v $ s else v $ s)" for s
      using fst_IH fst_IH' by auto
    have "foldl ?f (\<lambda>s. (v $ s, d s)) (sorted_list_of_set {..x}) = 
      foldl ?f (\<lambda>s. (v $ s, d s)) (sorted_list_of_set {..x'} @ sorted_list_of_set {x})"
    proof -
      have *: "{x'. x' < x} \<noteq> {}" using True by auto
      hence **: "{..x'} = {y \<in> {..x}. y < x}" "{x} = {y \<in> {..x}. x \<le> y}"
        by (auto simp: x'_def Max_ge_iff[OF finite *])
      show ?thesis
        unfolding ** sorted_list_of_set_split[symmetric, OF finite] by auto
    qed
    also have "\<dots>  = ?f (foldl ?f (\<lambda>s. (v $ s, d s)) (sorted_list_of_set {..x'})) x"
      by auto
    also have "\<dots> = (?old (x := (GS_rec v $ x, GS_iter_arg_max (\<chi> s. fst (?old s)) x)))"
    proof (subst GS_rec_eq_iter_max[of _ "(\<chi> s. fst (?old s))"], goal_cases)
      case (1 s)
      then show ?case 
        using fst_IH by auto 
    next
      case (2 s)
      then show ?case
        unfolding vec_lambda_inverse[OF UNIV_I]
        using True
        by (subst foldl_upd_notin) (auto simp: x'_def Max_ge_iff[OF finite])
    qed auto
    also have "\<dots> = (?old (x := (GS_rec v $ x, opt_policy_gs' d v x)))"
      by (auto simp: fst_IH'' opt_policy_gs'_eq_GS_iter')
    finally have "foldl ?f (\<lambda>s. (v $ s, d s)) (sorted_list_of_set {..x}) = 
      (?old (x := (GS_rec v $ x, opt_policy_gs' d v x)))".
    thus ?thesis    
      unfolding GS_rec_am_code_def
      by auto
  next
    case False
    hence "{..x} = {x}"
      by (auto simp: not_less antisym)
    thus ?thesis
      unfolding GS_rec_am_code_def
      using opt_policy_gs'_eq_GS_iter[of x v] GS_rec_eq_iter_max[of x v] False 
      by fastforce
  qed
qed

lemma GS_rec_am_code_eq: "GS_rec_am_code v d s = (GS_rec v $ s, opt_policy_gs' d v s)"
proof (induction s arbitrary: d rule: less_induct)
  case (less x)
  show ?case 
  proof (cases "\<exists>x'. x' < x")
    case True
    let ?f = "(\<lambda>vd s. vd(s := (GS_iter_max (\<chi> s. fst (vd s)) s,  GS_iter_arg_max (\<chi> s. fst (vd s)) s)))"
    define x' where "x' = Max {x'. x' < x}"
    let ?old = "(foldl ?f (\<lambda>s. (v $ s, d s)) (sorted_list_of_set {..x'}))"
    have 1: "s < x \<Longrightarrow> (s \<notin> set (sorted_list_of_set {s' \<in> {..x'}. s < s'}))" for s :: 's
      by auto
    have "s < x \<Longrightarrow> foldl ?f (\<lambda>s. (v $ s, d s)) (sorted_list_of_set {..x'}) s = 
      foldl ?f (\<lambda>s. (v $ s, d s)) (sorted_list_of_set {s' \<in> {..x'}. s' \<le> s} @ sorted_list_of_set {s' \<in> {..x'}. s < s'}) s" for s
      by (subst sorted_list_of_set_split'[symmetric, OF finite]) blast
    hence "s < x \<Longrightarrow> foldl ?f (\<lambda>s. (v $ s, d s)) (sorted_list_of_set {..x'}) s = 
      foldl ?f (\<lambda>s. (v $ s, d s)) (sorted_list_of_set {s' \<in> {..x'}. s' \<le> s}) s" for s
      using foldl_upd_notin'[OF 1]
      by fastforce
    hence 1: "s < x \<Longrightarrow> foldl ?f (\<lambda>s. (v $ s, d s)) (sorted_list_of_set {..x'}) s = 
      foldl ?f (\<lambda>s. (v $ s, d s)) (sorted_list_of_set {..s}) s" for s
      unfolding x'_def
      using True
      by (auto simp: atMost_def Max_ge_iff[OF finite]) meson
    have fst_IH: "fst (?old s) = GS_rec v $ s" if "s < x" for s
      unfolding 1[OF that] less[unfolded GS_rec_am_code_def, OF that]
      by auto
    have fst_IH': "fst (?old s) = v $ s" if "x \<le> s" for s
      using True that
      by (subst foldl_upd_notin) (auto simp: x'_def atMost_def Max_ge_iff[OF finite])
    have fst_IH'': "fst (?old s) = (if s < x then GS_rec v $ s else v $ s)" for s
      using fst_IH fst_IH' by auto
    have "foldl ?f (\<lambda>s. (v $ s, d s)) (sorted_list_of_set {..x}) = foldl ?f (\<lambda>s. (v $ s, d s)) (sorted_list_of_set {..x'} @ sorted_list_of_set {x})"
    proof -
      have *: "{x'. x' < x} \<noteq> {}" using True by auto
      hence 1: "{..x'} = {y \<in> {..x}. y < x}"
        by (auto simp: x'_def Max_ge_iff[OF finite *])
      have 2: "{x} = {y \<in> {..x}. x \<le> y}"
        by auto
      thus ?thesis
        unfolding 1 2 sorted_list_of_set_split[symmetric, OF finite] by auto
    qed
    also have "\<dots>  = ?f (foldl ?f (\<lambda>s. (v $ s, d s)) (sorted_list_of_set {..x'})) x"
      by auto
    also have "\<dots> = (?old (x := (GS_rec v $ x, GS_iter_arg_max (\<chi> s. fst (?old s)) x)))"
    proof (subst GS_rec_eq_iter_max[of _ "(\<chi> s. fst (?old s))"], goal_cases)
      case (2 s)
      then show ?case
        unfolding vec_lambda_inverse[OF UNIV_I]
        using True
        by (subst foldl_upd_notin) (auto simp: x'_def Max_ge_iff[OF finite])
    qed (auto simp: fst_IH)
    also have "\<dots> = (?old (x := (GS_rec v $ x, opt_policy_gs' d v x)))"
      by (auto simp: fst_IH'' opt_policy_gs'_eq_GS_iter')
    finally have "foldl ?f (\<lambda>s. (v $ s, d s)) (sorted_list_of_set {..x}) = 
      (?old (x := (GS_rec v $ x, opt_policy_gs' d v x)))".
    thus ?thesis    
      unfolding GS_rec_am_code_def
      by auto
  next
    case (False)
    hence "{..x} = {x}"
      by (auto simp: not_less antisym)
    hence *: "(sorted_list_of_set {..x}) = [x]"
      by auto
    show ?thesis
      unfolding GS_rec_am_code_def
      using opt_policy_gs'_eq_GS_iter[of x v] GS_rec_eq_iter_max[of x v] False 
      by (fastforce simp: *)
  qed
qed

definition GS_rec_iter_arg_max where
  "GS_rec_iter_arg_max v s = (LEAST a. is_arg_max (\<lambda>a. r (s, a) + 
    l * (\<Sum>s' \<in> UNIV. pmf (K (s,a)) s' * v s')) (\<lambda>a. a \<in> A s) a)"

definition "opt_policy_gs v s = (LEAST a. is_arg_max (\<lambda>a. GS_rec_fun_inner v s a) (\<lambda>a. a \<in> A s) a)"

lemma opt_policy_gs_eq': "opt_policy_gs v = opt_policy_gs' d (vec_lambda v)"
  unfolding opt_policy_gs_def opt_policy_gs'_def GS_rec_fun_inner_def GS_rec_step_elem
  by (auto simp: GS_rec_fun\<^sub>b.rep_eq GS_rec_def vec_lambda_inverse)

declare gs_iteration.simps[simp del]

lemma gs_iteration_error: 
  assumes "eps > 0"
  shows "dist (gs_iteration eps v) \<nu>\<^sub>b_opt < eps / 2"
  using assms dist_\<L>\<^sub>b_split_opt_eps gs_iteration.simps
  by (induction eps v rule: gs_iteration.induct) auto


lemma GS_rec_fun_inner_vec: "GS_rec_fun_inner v s a = GS_rec_step (d(s := a)) (vec_lambda v) $ s"
  unfolding GS_rec_step_elem
  by (auto simp: GS_rec_fun_inner_def GS_rec_def GS_rec_fun\<^sub>b.rep_eq vec_lambda_inverse)

lemma find_policy_error_bound_gs:
  assumes "eps > 0" "2 * l * dist v (GS_rec_fun\<^sub>b v) < eps * (1-l)"
  shows "dist (\<nu>\<^sub>b (mk_stationary_det (opt_policy_gs (GS_rec_fun\<^sub>b v)))) \<nu>\<^sub>b_opt < eps"
proof (rule GS.find_policy_QR_error_bound[OF assms(1)])
  have "2 * GS.QR_disc * dist v (GS_rec_fun\<^sub>b v) \<le> 2 * l * dist v (GS_rec_fun\<^sub>b v)"
    using GS_QR_disc_le_disc
    by (auto intro!: mult_right_mono)
  also have "\<dots> <  eps * (1-l)" using assms by auto
  also have "\<dots> \<le> eps * (1 - GS.QR_disc)" 
    using assms GS_QR_disc_le_disc
    by (auto intro!: mult_left_mono)
  finally show "2 * GS.QR_disc * dist v (GS_rec_fun\<^sub>b v) < eps * (1 - GS.QR_disc)".
next
  obtain d where d: "is_dec_det d"
    using ex_dec_det by blast
  show "is_arg_max (\<lambda>d. (GS.L_split d (GS_rec_fun\<^sub>b v)) s) (\<lambda>d. d \<in> D\<^sub>D) (opt_policy_gs (GS_rec_fun\<^sub>b v))" for s
    unfolding opt_policy_gs_eq'[of _ d] GS_inv_blinfun_to_matrix 
    using opt_policy_gs'_is_arg_max
    by simp
qed

definition "vi_gs_policy eps v = opt_policy_gs (gs_iteration eps v)"

lemma vi_gs_policy_opt:
  assumes "0 < eps"
  shows "dist (\<nu>\<^sub>b (mk_stationary_det (vi_gs_policy eps v))) \<nu>\<^sub>b_opt < eps"
  unfolding vi_gs_policy_def 
  using assms
proof (induction eps v rule: gs_iteration.induct)
  case (1 v)
  then show ?case
    using find_policy_error_bound_gs
    by (subst gs_iteration.simps) auto
qed

lemma GS_rec_iter_eq_iter_max: "GS_rec_iter v = GS_iter_max (vec_lambda v)"
  unfolding GS_rec_iter_def GS_iter_max_def GS_iter_def 
  by auto
end
end