theory CountableSum
  imports "BoundedDioid" "Set_More"
begin

definition path_seq :: "'weight::bounded_dioid set \<Rightarrow> nat \<Rightarrow> 'weight" where
  "path_seq W \<equiv> if W = {} then (\<lambda>_. 0) else SOME f. \<forall>l. l \<in> W \<longleftrightarrow> (\<exists>i. f i = l)"

lemma path_seq_empty[simp]: "path_seq {} i = 0"
  unfolding path_seq_def by simp

lemma countable_set_exists_seq: "countable W \<Longrightarrow> W \<noteq> {} \<Longrightarrow> \<exists>f::(nat\<Rightarrow>'weight). \<forall>l. l \<in> W \<longleftrightarrow> (\<exists>i. f i = l)"
  by (rule exI[of _ "from_nat_into W"])
     (meson from_nat_into from_nat_into_to_nat_on)

lemma path_seq_of_countable_set:
  assumes "countable W"
  assumes "W \<noteq> {}"
  shows "l \<in> W \<longleftrightarrow> (\<exists>i. path_seq W i = l)"
  unfolding path_seq_def
  apply (simp add: assms(2))
  using someI_ex[OF countable_set_exists_seq[OF assms]] 
  by blast

lemma path_seq_elem_exists_index:
  assumes "countable W"
  assumes "w \<in> W"
  shows "\<exists>i. path_seq W i = w"
  using path_seq_of_countable_set[OF assms(1)] assms(2) by blast

lemma path_seq_in_set:
  assumes "countable W"
  assumes "W \<noteq> {}"
  shows "path_seq W i \<in> W"
  using path_seq_of_countable_set[OF assms] by fast

lemma path_seq_notin_set_zero:
  assumes "countable W"
  assumes "path_seq W i \<notin> W"
  shows "path_seq W i = 0"
  using assms
  apply (cases "W={}", simp)
  using path_seq_in_set[OF assms(1)]
  by simp

definition SumInf :: "'weight::bounded_dioid set \<Rightarrow> 'weight" ("\<^bold>\<Sum>") where
  "\<^bold>\<Sum> W = suminf (path_seq W)"

lemma countable_obtain_seq:
  assumes "countable W"
  obtains f::"'a \<Rightarrow> nat" where "\<forall>x\<in>W. \<forall>y\<in>W. f x = f y \<longrightarrow> x = y"
  using assms unfolding countable_def inj_on_def by presburger

lemma countable_SumInf_exists_sumseq_bound:
  fixes W :: "'weight::bounded_dioid set"
  assumes "countable W"
  shows "\<exists>f N. \<forall>n\<ge>N. \<^bold>\<Sum> W = sum_seq f n \<and> {f i | i. i < N} \<subseteq> W"
proof (cases "W = {}")
  case True
  then show ?thesis 
    unfolding SumInf_def path_seq_def
    by simp (rule exI[of _ "\<lambda>i. 0"], auto)
next
  case False
  then show ?thesis
  proof -
    obtain f :: "nat \<Rightarrow> 'weight" and C :: "nat set" where f_bij:"bij_betw f C W" 
      using countableE_bij[OF assms(1)] by blast
    then have f_inj:"\<forall>x\<in>C. \<forall>y\<in>C. f x = f y \<longrightarrow> x = y" and f_img:"f ` C = W" 
      unfolding bij_betw_def inj_on_def by blast+
    from f_img have "\<And>l. (l \<in> W) \<longleftrightarrow> (\<exists>i\<in>C. f i = l)" by blast
    then have path_seq_to_f:"\<And>l. (\<exists>i. path_seq W i = l) \<longleftrightarrow> (\<exists>i\<in>C. f i = l)" 
      using path_seq_of_countable_set[OF assms(1) False] by presburger
    then have "\<forall>i. \<exists>i'. (path_seq W) i = f i'" by metis
    then have "\<exists>h. \<forall>i. (path_seq W) i = f (h i)" by metis
    then obtain h where "\<And>i. (path_seq W) i = (f o h) i" by force
    then have path_seq_fh:"(path_seq W) = (f o h)" by fast
    obtain N where "\<forall>n\<ge>N. sum_seq (f o h) n = suminf (f o h)" by (fact sumseq_suminf_obtain_bound)
    then have "\<forall>n\<ge>N. \<^bold>\<Sum> W = sum_seq (f o h) n"
      unfolding SumInf_def using path_seq_fh by simp
    then show ?thesis 
      using path_seq_in_set[OF assms False] path_seq_fh by auto
  qed
qed

lemma countable_SumInf_obtains_sumseq_bound:
  assumes "countable W"
  obtains f and N where "\<forall>n\<ge>N. \<^bold>\<Sum> W = sum_seq f n" and "{f i | i. i < N} \<subseteq> W"
  using countable_SumInf_exists_sumseq_bound[OF assms] by fast

lemma countable_suminf_obtains_sumseq:
  assumes "countable W"
  obtains f and n where "\<^bold>\<Sum> W = sum_seq f n" and "{f i | i. i < n} \<subseteq> W"
  using countable_SumInf_exists_sumseq_bound[OF assms] by fast

lemma SumInf_exists_finite_subset:
  fixes W :: "'weight::bounded_dioid set"
  assumes "countable W"
  shows "\<exists>W'. W' \<subseteq> W \<and> finite W' \<and> \<^bold>\<Sum> W = \<Sum> W'"
proof -
  obtain f and n where sumW:"\<^bold>\<Sum> W = sum_seq f n" and subsetW:"{f i | i. i < n} \<subseteq> W"
    by (fact countable_suminf_obtains_sumseq[OF assms])
  have fin:"finite (f ` {i. i < n})" by blast
  obtain W' where W'_def:"W' = {f i | i. i < n}" by blast
  then have "W' \<subseteq> W" and "finite W'" and "\<Sum> W' = sum_seq f n" 
    using subsetW fin sum_seq_to_sum[of f n] by auto
  then show ?thesis using sumW by metis
qed

lemma SumInf_obtains_finite_subset:
  fixes W :: "'weight::bounded_dioid set"
  assumes "countable W"
  obtains W' where "W' \<subseteq> W" and "finite W'" and "\<^bold>\<Sum> W = \<Sum> W'"
  using SumInf_exists_finite_subset[OF assms] by blast

lemma countable_SumInf_elem:
  fixes W :: "'weight::bounded_dioid set"
  assumes "countable W"
  assumes "w \<in> W"
  shows "\<^bold>\<Sum> W \<le> w"
proof -
  obtain i where "path_seq W i = w" 
    using path_seq_elem_exists_index[OF assms] by blast
  then show ?thesis 
    unfolding SumInf_def using suminf_elem[of "path_seq W" i] by blast
qed

lemma finite_sum_less_eq:
  assumes "finite W" and "\<^bold>\<Sum> W = \<Sum> W'"
  shows "\<Sum> W' \<le> \<Sum> W"
  using assms(2) countable_SumInf_elem[OF countable_finite[OF assms(1)]]
        sum_greater_elem[OF _ assms(1)]
  by presburger

lemma finite_SumInf_is_sum:
  assumes "finite W"
  shows "\<^bold>\<Sum> W = \<Sum> W"
proof -
  obtain W' where subset:"W' \<subseteq> W" and fin:"finite W'" and eq:"\<^bold>\<Sum> W = \<Sum> W'" 
    by (fact SumInf_obtains_finite_subset[OF countable_finite[OF assms(1)]])
  have "\<And>w. w \<in> W \<Longrightarrow> \<Sum> W' \<le> w" 
    using eq countable_SumInf_elem[OF countable_finite[OF assms(1)]] by presburger
  then have "\<Sum> W' \<le> \<Sum> W" using sum_greater_elem assms fin by blast
  moreover have "\<Sum> W \<le> \<Sum> W'" by (fact sum_superset_less_eq[OF subset assms])
  ultimately have "\<Sum> W' = \<Sum> W" by fastforce
  then show ?thesis using eq by argo
qed

lemma singleton_SumInf[simp]: "\<^bold>\<Sum> {w} = w"
  using finite_SumInf_is_sum[of "{w}"] by simp

lemma SumInf_empty[simp]: "\<^bold>\<Sum> {} = 0"
  unfolding SumInf_def using suminf_finite[of "{}", simplified] path_seq_empty by blast

lemma SumInf_is_zero_if_subset_singleton_zero[simp]: "X \<subseteq> {0} \<Longrightarrow> \<^bold>\<Sum> X = 0"
  using subset_singletonD by fastforce

lemma SumInf_mono: 
  assumes "A \<subseteq> B"
  assumes "countable B"
  shows "\<^bold>\<Sum> A \<ge> \<^bold>\<Sum> B"
proof -
  obtain A' where subsetA:"A' \<subseteq> A" and finA:"finite A'" and eqA:"\<^bold>\<Sum> A = \<Sum> A'" 
    by (fact SumInf_obtains_finite_subset[OF countable_subset[OF assms]])
  obtain B' where subsetB:"B' \<subseteq> B" and finB:"finite B'" and eqB:"\<^bold>\<Sum> B = \<Sum> B'" 
    by (fact SumInf_obtains_finite_subset[OF assms(2)])
  have "A' \<subseteq> B" using subsetA assms(1) by fast
  then have "\<And>a. a \<in> A' \<Longrightarrow> \<Sum> B' \<le> a" 
    using countable_SumInf_elem[OF assms(2)] eqB by auto
  then have "\<Sum> B' \<le> \<Sum> A'" using sum_greater_elem[of A' "\<Sum> B'"] finA finB by fastforce
  then show ?thesis using eqA eqB by argo
qed

lemma SumInf_bounded_if_set_bounded:
  assumes countableX: "countable W"
  assumes inf_d: "\<forall>w \<in> W. w \<ge> d"
  shows "\<^bold>\<Sum> W \<ge> d"
proof -
  obtain W' where subset:"W' \<subseteq> W" and fin:"finite W'" and eq:"\<^bold>\<Sum> W = \<Sum> W'"
    by (fact SumInf_obtains_finite_subset[OF countableX])
  have "\<forall>w \<in> W'. w \<ge> d" using subset inf_d by blast
  then have "\<Sum> W' \<ge> d" using fin
    unfolding BoundedDioid.less_eq_def
    apply (induct rule: finite_induct[OF fin], simp_all)
    subgoal for w F
      using add.assoc[of d w "\<Sum> F"] by simp
    done
  then show ?thesis using eq by argo
qed

lemma SumInf_left_distr: 
  assumes "countable W"
  shows "w1 * \<^bold>\<Sum> W = \<^bold>\<Sum> {w1 * w2 | w2. w2 \<in> W}"
proof -
  have sumInf_left_distr1: "w1 * \<^bold>\<Sum> W \<le> \<^bold>\<Sum> {w1 * w2 | w2. w2 \<in> W}"
    using SumInf_bounded_if_set_bounded countable_f_on_set[of W "\<lambda>w2. w1 * w2"] assms
    by (force simp add: countable_SumInf_elem idempotent_semiring_ord_class.mult_isol)
  have countable_D_img: "countable {w1 * w2 | w2. w2 \<in> W}"
    using assms countable_f_on_set by blast
  obtain W' where subset:"W' \<subseteq> W" and fin:"finite W'" and eq:"\<^bold>\<Sum> W = \<Sum> W'"
    by (fact SumInf_obtains_finite_subset[OF assms(1)])

  have finite_D'_img: "finite {w1 * w2 | w2. w2 \<in> W'}"
    by (simp add: fin)

  from fin have sumInf_left_distr2: "w1 * \<Sum> W' \<ge> \<Sum> {w1 * w2 | w2. w2 \<in> W'}"
  proof (induction)
    case empty
    then show ?case
      by force
  next
    case (insert w W')
    have Sum_insert: "\<Sum> (insert w W') = w + \<Sum>W'"
      using insert.hyps(1) by simp
    have Sum_insert_img: "\<Sum> {w1 * w2 |w2. w2 \<in> insert w W'} = w1 * w + \<Sum>{w1 * w2 |w2. w2 \<in> W'}"
      by (metis Setcompr_eq_image finite_imageI image_insert insert.hyps(1) idempotent_comm_monoid_add_class.idem_sum_insert)
    show ?case
      unfolding Sum_insert_img Sum_insert using insert by (simp add: meet.le_infI2 semiring_class.distrib_left)
  qed

  have "\<^bold>\<Sum> {w1 * w2 | w2. w2 \<in> W} \<le> \<Sum> {w1 * w2 | w2. w2 \<in> W'}"
    using Collect_mono[of "\<lambda>w2w1. \<exists>w2. w2w1 = w1 * w2 \<and> w2 \<in> W'" "\<lambda>w2w1. \<exists>w2. w2w1 = w1 * w2 \<and> w2 \<in> W"] 
      SumInf_mono[of "{w1 * w2 | w2. w2 \<in> W'}" "{w1 * w2 | w2. w2 \<in> W}"] subset 
      countable_D_img unfolding finite_SumInf_is_sum[OF finite_D'_img,symmetric] by fastforce

  then have "w1 * \<^bold>\<Sum> W \<ge> \<^bold>\<Sum> {w1 * w2 | w2. w2 \<in> W}"
    using sumInf_left_distr2 eq by auto 
  then show ?thesis
    using sumInf_left_distr1 by auto
qed

lemma SumInf_left_distr1:
  assumes "countable {f x |x. P x}"
  shows  "w * \<^bold>\<Sum> {f x |x. P x} = \<^bold>\<Sum> {w * f x |x. P x}"
proof -
  have "w * \<^bold>\<Sum> {f x |x. P x} = \<^bold>\<Sum> {w * fx |fx. fx \<in> {f x|x. P x}}"
    using assms SumInf_left_distr[of "{f x|x y. P x}" w] by auto
  also
  have "... = \<^bold>\<Sum> {w * f x |x. P x}"
    by (rule arg_cong[of _ _ "\<^bold>\<Sum>"]) auto
  finally show ?thesis
    by auto
qed

lemma SumInf_left_distr2:
  assumes "countable {f x y |x y. P x y}"
  shows  "w * \<^bold>\<Sum> {f x y |x y. P x y } = \<^bold>\<Sum> {w * f x y |x y. P x y}"
proof -
  have "w * \<^bold>\<Sum> {f x y |x y. P x y } = \<^bold>\<Sum> {w * fxy |fxy. fxy \<in> {f x y |x y. P x y }}"
    using assms SumInf_left_distr[of "{f x y |x y. P x y}" w] by auto
  also
  have "... = \<^bold>\<Sum> {w * f x y |x y. P x y}"
    by (rule arg_cong[of _ _ "\<^bold>\<Sum>"]) auto
  finally show ?thesis
    by auto
qed

lemma SumInf_right_distr: 
  assumes "countable W"
  shows "\<^bold>\<Sum> W * w1 = \<^bold>\<Sum> {w2 * w1 | w2. w2 \<in> W}"
proof -
  have sumInf_right_distr1: "\<^bold>\<Sum> W * w1 \<le> \<^bold>\<Sum> {w2 * w1 | w2. w2 \<in> W}"
    using SumInf_bounded_if_set_bounded countable_f_on_set[of W "\<lambda>w2. w2 * w1"] assms
    by (force simp add: countable_SumInf_elem idempotent_semiring_ord_class.mult_isor)

  have countable_D_img: "countable {w2 * w1 | w2. w2 \<in> W}"
    using assms countable_f_on_set by fastforce 
  obtain W' where subset:"W' \<subseteq> W" and fin:"finite W'" and eq:"\<^bold>\<Sum> W = \<Sum> W'"
    by (fact SumInf_obtains_finite_subset[OF assms(1)])

  have finite_D'_img: "finite {w2 * w1 | w2. w2 \<in> W'}"
    by (simp add: fin)

  from fin have sumInf_right_distr2: "\<Sum> W' * w1 \<ge> \<Sum> {w2 * w1 | w2. w2 \<in> W'}"
  proof (induction)
    case empty
    then show ?case
      by force
  next
    case (insert w W')
    have Sum_insert: "\<Sum> (insert w W') = w + \<Sum>W'"
      using insert.hyps(1) by simp
    have Sum_insert_img: "\<Sum> {w2 * w1 |w2. w2 \<in> insert w W'} = w * w1 + \<Sum>{w2 * w1 |w2. w2 \<in> W'}"
      by (metis Setcompr_eq_image finite_imageI image_insert insert.hyps(1) idempotent_comm_monoid_add_class.idem_sum_insert)
    show ?case
      unfolding Sum_insert_img Sum_insert using insert by (simp add: meet.le_infI2 semiring_class.distrib_right)
  qed

  have "\<^bold>\<Sum> {w2 * w1 | w2. w2 \<in> W} \<le> \<Sum> {w2 * w1 | w2. w2 \<in> W'}"
    using Collect_mono[of "\<lambda>w2w1. \<exists>w2. w2w1 = w2 * w1 \<and> w2 \<in> W'" "\<lambda>w2w1. \<exists>w2. w2w1 = w2 * w1 \<and> w2 \<in> W"] 
      SumInf_mono[of "{w2 * w1 | w2. w2 \<in> W'}" "{w2 * w1 | w2. w2 \<in> W}"] subset 
      countable_D_img unfolding finite_SumInf_is_sum[OF finite_D'_img,symmetric] by fastforce

  then have "\<^bold>\<Sum> W * w1 \<ge> \<^bold>\<Sum> {w2 * w1 | w2. w2 \<in> W}"
    using sumInf_right_distr2 eq by auto 
  then show ?thesis
    using sumInf_right_distr1 by auto
qed

lemma SumInf_right_distr1:
  assumes "countable {f x |x. P x}"
  shows  "\<^bold>\<Sum> {f x|x y. P x} * w = \<^bold>\<Sum> {f x * w |x. P x}"
proof -
  have "\<^bold>\<Sum> {f x |x. P x} * w = \<^bold>\<Sum> {z * w |z. z \<in> {f x|x. P x}}"
    using assms SumInf_right_distr[of "{f x |x . P x}" w] by auto
  also
  have "... = \<^bold>\<Sum> {f x * w |x. P x}"
    by (rule arg_cong[of _ _ "\<^bold>\<Sum>"]) auto
  finally show ?thesis
    by auto
qed

lemma SumInf_right_distr2:
  assumes "countable {f x y |x y. P x y }"
  shows  "\<^bold>\<Sum> {f x y |x y. P x y } * w = \<^bold>\<Sum> {f x y * w |x y. P x y}"
proof -
  have "\<^bold>\<Sum> {f x y |x y. P x y } * w = \<^bold>\<Sum> {fxy * w |fxy. fxy \<in> {f x y |x y. P x y }}"
    using assms SumInf_right_distr[of "{f x y |x y. P x y}" w] by auto
  also
  have "... = \<^bold>\<Sum> {f x y * w |x y. P x y}"
    by (rule arg_cong[of _ _ "\<^bold>\<Sum>"]) auto
  finally show ?thesis
    by auto
qed

lemma SumInf_of_SumInf_countable1:
  assumes "countable {y. Q y}"
  assumes "\<And>y. Q y \<Longrightarrow> countable {(x, y)| x. P x y}"
  shows "countable {\<^bold>\<Sum> {f x y |x. P x y} |y. Q y}"
  using countable_image[of "{y. Q y}" "\<lambda>y. \<^bold>\<Sum> {f x y |x. P x y}", OF assms(1)]
  by (simp add: image_Collect)

lemma SumInf_of_SumInf_countable2:
  assumes "countable {y. Q y}"
  assumes "\<And>y. Q y \<Longrightarrow> countable {(x, y)| x. P x y}"
  shows "countable {f x y |x y. P x y \<and> Q y}"
proof -
  have "countable (\<Union>((\<lambda>y. {(x,y)|x. P x y}) ` {y. Q y}))"
    using assms(1) assms(2) by blast
  moreover
  have "(\<Union>y\<in>{y. Q y}. {(x, y) |x. P x y}) = {(x, y) |x y. P x y \<and> Q y}"
    by auto
  ultimately
  have "countable {(x, y) |x y. P x y \<and> Q y}"
    by auto
  then show "countable {f x y |x y. P x y \<and> Q y}"
    using countable_image[of "{(x, y) |x y. P x y \<and> Q y}" "\<lambda>(x, y). f x y"]
      Collect_cong[of "\<lambda>fxy. \<exists>x y. P x y \<and> Q y \<and> fxy = f x y" "\<lambda>fxy. \<exists>x y. fxy = f x y \<and> P x y \<and> Q y "]
    unfolding image_def by fastforce
qed

lemma countable_image_prod:
  assumes "countable {(x, y)| x. P x y}"
  shows "countable {f x y |x. P x y}"
  using assms countable_image[of "{(x, y) |x . P x y}" "\<lambda>(x, y). f x y"]
    Collect_cong[of "\<lambda>fxy. \<exists>x. P x y \<and> fxy = f x y" "\<lambda>fxy. \<exists>x. fxy = f x y \<and> P x y"]
  unfolding image_def by fastforce

lemma SumInf_of_SumInf_geq:
  assumes "countable {y. Q y}"
  assumes "\<And>y. Q y \<Longrightarrow> countable {(x, y)| x. P x y}"
  shows "\<^bold>\<Sum> {\<^bold>\<Sum> {f x y| x. P x y} |y. Q y} \<ge> \<^bold>\<Sum> {f x y | x y. P x y \<and> Q y}"
proof (rule SumInf_bounded_if_set_bounded)
  show "countable {\<^bold>\<Sum> {f x y |x. P x y} |y. Q y}"
    using SumInf_of_SumInf_countable1 assms by blast
  have count: "countable {f x y |x y. P x y \<and> Q y}"
    using  SumInf_of_SumInf_countable2 assms by auto

  have "\<And>y. Q y \<Longrightarrow> \<^bold>\<Sum> {f x y |x y. P x y \<and> Q y} \<le> \<^bold>\<Sum> {f x y |x. P x y}"
  proof -
    fix y
    assume Qy: "Q y"
    show "\<^bold>\<Sum> {f x y |x y. P x y \<and> Q y} \<le> \<^bold>\<Sum> {f x y |x. P x y}"
      using count Collect_mono_iff[of "\<lambda>fxy. \<exists>x. fxy = f x y \<and> P x y" "\<lambda>fxy. \<exists>x y. fxy = f x y \<and> P x y \<and> Q y"]
            SumInf_mono Qy by auto
  qed
  then show "\<forall>fxy\<in>{\<^bold>\<Sum> {f x y |x. P x y} |y. Q y}. \<^bold>\<Sum> {f x y |x y. P x y \<and> Q y} \<le> fxy"
    by auto
qed

lemma SumInf_of_SumInf_leq:
  assumes "countable {y. Q y}"
  assumes "\<And>y. Q y \<Longrightarrow> countable {(x, y)| x. P x y} "
  shows "\<^bold>\<Sum> {\<^bold>\<Sum> {f x y| x. P x y} |y. Q y} \<le> \<^bold>\<Sum> {f x y | x y. P x y \<and> Q y}"
proof (rule SumInf_bounded_if_set_bounded)
  show count: "countable {f x y |x y. P x y \<and> Q y}"
    using SumInf_of_SumInf_countable2 assms by blast

  have count2: "countable {\<^bold>\<Sum> {f x y |x. P x y} |y. Q y}"
    using SumInf_of_SumInf_countable1 assms by blast

  have "\<And>x y. P x y \<Longrightarrow> Q y \<Longrightarrow> \<^bold>\<Sum> {\<^bold>\<Sum> {f x y |x. P x y} |y. Q y} \<le> f x y"
  proof -
    fix x y 
    assume Pxy: "P x y"
    assume Qy: "Q y"
    have "countable {f x y |x. P x y}"
      using Qy assms(2)[of y] countable_image_prod by fastforce
    then have "\<^bold>\<Sum> {f x y |x. P x y} \<le> f x y"
      using Pxy countable_SumInf_elem by auto
    then show "\<^bold>\<Sum> {\<^bold>\<Sum> {f x y |x. P x y} |y. Q y} \<le> f x y"
      using countable_SumInf_elem dual_order.trans Qy count2 by blast
  qed
  then show "\<forall>fxy\<in>{f x y |x y. P x y \<and> Q y}. \<^bold>\<Sum> {\<^bold>\<Sum> {f x y |x. P x y} |y. Q y} \<le> fxy"
    by auto
qed

lemma SumInf_of_SumInf:
  assumes "countable {y. Q y}"
  assumes "\<And>y. Q y \<Longrightarrow> countable {(x, y)| x. P x y} "
  shows "\<^bold>\<Sum> {\<^bold>\<Sum> {f x y| x. P x y} |y. Q y} = \<^bold>\<Sum> {f x y | x y. P x y \<and> Q y}"
  using SumInf_of_SumInf_geq[of Q P f] SumInf_of_SumInf_leq[of Q P f] assms(1,2) by auto

lemma SumInf_of_SumInf_fst_arg:
  assumes "countable {y. Q y}"
      and "\<And>y. Q y \<Longrightarrow> countable {(w, y)| w. P w y} "
    shows "\<^bold>\<Sum> {\<^bold>\<Sum> {w. P w y} |y. Q y} = \<^bold>\<Sum> {w | w y. P w y \<and> Q y}"
  using SumInf_of_SumInf[of _ _ "\<lambda>x y. x"] assms by auto

lemma SumInf_of_SumInf_right_distr:
  assumes "countable {y. Q y}"
      and "\<And>y. Q y \<Longrightarrow> countable {(x, y) |x. P x y}"
    shows "\<^bold>\<Sum> {\<^bold>\<Sum> {f x y| x. P x y} * g y |y. Q y} = \<^bold>\<Sum> {f x y * g y | x y. P x y \<and> Q y}"
proof -
  have eql: "\<forall>y. {f x y * g y |x. P x y} = {fxy * g y |fxy. \<exists>x. fxy = f x y \<and> P x y}"
    by auto
  have "\<And>y. Q y \<Longrightarrow> countable {f x y |x. P x y}"
    using assms(2) countable_f_on_P_Q_set2[of P f "\<lambda>x y. True", simplified] countable_image_prod setcompr_eq_image by fast
  then have "\<And>y. Q y \<Longrightarrow> \<^bold>\<Sum> {f x y |x. P x y} * g y = \<^bold>\<Sum> {fxy * g y |fxy. fxy \<in> {f x y |x. P x y}}"
    using SumInf_right_distr[of "{f x _ |x. P x _}" "g _"] by simp
  then have "\<^bold>\<Sum> {\<^bold>\<Sum> {f x y| x. P x y} * g y |y. Q y} = \<^bold>\<Sum> {\<^bold>\<Sum> {fxy * g y |fxy. fxy \<in> {f x y |x. P x y}} |y. Q y}"
    by (simp add: setcompr_eq_image)
  also have "... =  \<^bold>\<Sum> {f x y * g y | x y. P x y \<and> Q y}"
    using eql SumInf_of_SumInf[of Q P "\<lambda>x y. f x y * g y"] assms by auto
  finally show ?thesis .
qed

lemma SumInf_of_SumInf_left_distr:
  assumes "countable {y. Q y}"
      and "\<And>y. Q y \<Longrightarrow> countable {(x, y) |x. P x y}"
    shows "\<^bold>\<Sum> {g y * \<^bold>\<Sum> {f x y| x. P x y} |y. Q y} = \<^bold>\<Sum> {g y * f x y | x y. P x y \<and> Q y}"
proof -
  have eql: "\<forall>y. {g y * f x y |x. P x y} = {g y * fxy |fxy. \<exists>x. fxy = f x y \<and> P x y}"
    by auto
  have "\<And>y. Q y \<Longrightarrow> countable {f x y |x. P x y}"
    using assms(2) countable_f_on_P_Q_set2[of P f "\<lambda>x y. True", simplified] countable_image_prod setcompr_eq_image by fast
  then have "\<And>y. Q y \<Longrightarrow> g y * \<^bold>\<Sum> {f x y |x. P x y} = \<^bold>\<Sum> {g y * fxy |fxy. fxy \<in> {f x y |x. P x y}}"
    using SumInf_left_distr[of "{f x _ |x. P x _}" "g _"] by simp
  then have "\<^bold>\<Sum> {g y * \<^bold>\<Sum> {f x y| x. P x y} |y. Q y} = \<^bold>\<Sum> {\<^bold>\<Sum> {g y * fxy |fxy. fxy \<in> {f x y |x. P x y}} |y. Q y}"
    by (simp add: setcompr_eq_image)
  also have "... =  \<^bold>\<Sum> {g y * f x y | x y. P x y \<and> Q y}"
    using eql SumInf_of_SumInf[of Q P "\<lambda>x y. g y * f x y"] assms by auto
  finally show ?thesis .
qed

lemma SumInf_of_SumInf_right_distr_simple:
 assumes "countable {d. P d}"
     and "countable {d. Q d}"
   shows "\<^bold>\<Sum> {\<^bold>\<Sum> {d. P d} * d' |d'. Q d'} = \<^bold>\<Sum> {d * d' | d d'. P d \<and> Q d'}"
  using SumInf_of_SumInf_right_distr[of Q "\<lambda>x y. P x" "\<lambda>x y. x" "\<lambda>x. x", OF assms(2)] countable_setcompr[OF assms(1)]
  by fastforce

lemma SumInf_bounded_by_SumInf_if_members_bounded:
  assumes "countable X"
  assumes "countable Y"
  assumes "\<forall>y \<in> Y. \<exists>x \<in> X. x \<le> y"
  shows "\<^bold>\<Sum> X \<le> \<^bold>\<Sum> Y"
  by (meson assms SumInf_bounded_if_set_bounded assms dual_order.trans countable_SumInf_elem)

lemma SumInf_mult_isor:
  assumes "countable {w . X w}"
  assumes "w \<le> w'"
  shows "\<^bold>\<Sum> {w * w''| w''. X w''} \<le> \<^bold>\<Sum> {w' * w''| w''. X w''}"
  by (rule SumInf_bounded_by_SumInf_if_members_bounded)
     (use assms idempotent_semiring_ord_class.mult_isor countable_setcompr[of X] in auto)

lemma SumInf_mono_wrt_img_of_set: 
  assumes "countable {x. P x}"
  assumes "\<forall>x. P x \<longrightarrow> f x \<le> g x"
  shows "\<^bold>\<Sum> {f x| x. P x} \<le> \<^bold>\<Sum> {g x| x. P x}"
  by (rule SumInf_bounded_by_SumInf_if_members_bounded)
     (use assms countable_setcompr[of P] in auto)

lemma SumInf_insert_0:
  assumes "countable W"
  shows "\<^bold>\<Sum> W = \<^bold>\<Sum> (insert 0 W)"
proof (cases "W = {}")
  case True
  then show ?thesis by simp
next
  case False
  have "countable (insert 0 W)" using assms by blast
  then have "\<^bold>\<Sum> W \<le> \<^bold>\<Sum> (insert 0 W)"
    using SumInf_bounded_by_SumInf_if_members_bounded[OF assms] False by fastforce
  moreover have "\<^bold>\<Sum> W \<ge> \<^bold>\<Sum> (insert 0 W)"
    using SumInf_mono[of W "insert 0 W"] assms by auto
  ultimately show ?thesis by simp
qed

lemma SumInf_equal_with_0:
  assumes "countable X"
  assumes "X \<union> {0} = Y \<union> {0}"
  shows "\<^bold>\<Sum> X = \<^bold>\<Sum> Y"
proof -
  have "countable Y" using assms
    by (metis countable_Un_iff countable_empty countable_insert)
  then show ?thesis using assms SumInf_insert_0[of X] SumInf_insert_0[of Y] by simp
qed

lemma SumInf_union:
  assumes "countable (X \<union> Y)" 
  shows "\<^bold>\<Sum>(X \<union> Y) = \<^bold>\<Sum> X + \<^bold>\<Sum> Y"
proof -
  have cX: "countable X" using assms by simp
  have cY: "countable Y" using assms by simp
  obtain X' where X': "X' \<subseteq> X" "finite X'" "\<^bold>\<Sum> X = \<Sum> X'"
    by (fact SumInf_obtains_finite_subset[OF cX])
  obtain Y' where Y': "Y' \<subseteq> Y" "finite Y'" "\<^bold>\<Sum> Y = \<Sum> Y'"
    by (fact SumInf_obtains_finite_subset[OF cY])
  have finU: "finite (X' \<union> Y')" using X'(2) Y'(2) by simp
  then have A:"\<^bold>\<Sum> X + \<^bold>\<Sum> Y = \<Sum>(X' \<union> Y')"
    using X'(3) Y'(3) idem_sum_union by metis
  have sub: "X' \<union> Y' \<subseteq> X \<union> Y" using X'(1) Y'(1) by blast
  have U_leq: "\<^bold>\<Sum>(X \<union> Y) \<le> \<^bold>\<Sum> X + \<^bold>\<Sum> Y"
    using SumInf_mono[OF sub assms] A finite_SumInf_is_sum[OF finU] by order
  
  obtain W where W: "W \<subseteq> X \<union> Y" "finite W" "\<^bold>\<Sum>(X \<union> Y) = \<Sum> W"
    by (fact SumInf_obtains_finite_subset[OF assms])
  then have A: "W = (W \<inter> X) \<union> (W \<inter> Y)" by auto
  have f:"finite ((W \<inter> X) \<union> (W \<inter> Y))" using A W(2) by blast
  have leqX: "\<^bold>\<Sum> X \<le> \<Sum>(W \<inter> X)"
    using SumInf_mono[OF _ cX, of "W \<inter> X"] finite_SumInf_is_sum[of "W \<inter> X"] by fastforce
  have leqY: "\<^bold>\<Sum> Y \<le> \<Sum>(W \<inter> Y)"
    using SumInf_mono[OF _ cY, of "W \<inter> Y"] finite_SumInf_is_sum[of "W \<inter> Y"] by fastforce
  have "\<Sum> W = \<Sum>(W \<inter> X) + \<Sum>(W \<inter> Y)"
    using A idem_sum_union[OF f] by presburger
  then have U_geq: "\<^bold>\<Sum>(X \<union> Y) \<ge> \<^bold>\<Sum> X + \<^bold>\<Sum> Y"
    unfolding W(3) using leqX leqY by (metis meet.inf_mono)

  show ?thesis using U_leq U_geq by order
qed

lemma SumInf_union_0:
  assumes "countable X"
  assumes "Y \<subseteq> {0}"
  shows "\<^bold>\<Sum>(X \<union> Y) = \<^bold>\<Sum> X"
proof -
  have cY: "countable Y" using countable_subset[OF assms(2)] by blast
  show ?thesis using SumInf_union assms(1) cY assms(2) by force
qed

lemma SumInf_split_Qor0:
  assumes "countable {x. P x}"
  assumes "(\<And>x. \<not> Q x \<Longrightarrow> f x = 0)"
  assumes "(\<And>x. Q x \<Longrightarrow> f x = g x)"
  shows "\<^bold>\<Sum> {f x| x. P x} = \<^bold>\<Sum> {g x| x. P x \<and> Q x}"
proof -
  have "{f x| x. P x} \<union> {0} = {g x| x. P x \<and> Q x} \<union> {0}" using assms by force
  then show ?thesis 
    using SumInf_equal_with_0[OF countable_setcompr[OF assms(1), of f]] by simp
qed

lemma SumInf_if_1_0_right_is_sum:
  assumes "countable {a. P a}"
  shows "\<^bold>\<Sum>{f a * (if Q a then 1 else 0) | a. P a} = \<^bold>\<Sum>{f a | a. P a \<and> Q a}"
  using SumInf_split_Qor0[OF assms, of Q "\<lambda>a. f a * (if Q a then 1 else 0)" "\<lambda>a. f a"]
  by force

lemma SumInf_if_1_0_left_is_sum:
  assumes "countable {a. P a}"
  shows "\<^bold>\<Sum>{(if Q a then 1 else 0) * f a | a. P a} = \<^bold>\<Sum>{f a | a. P a \<and> Q a}"
  using SumInf_split_Qor0[OF assms, of Q "\<lambda>a. (if Q a then 1 else 0) * f a" "\<lambda>a. f a"]
  by force

lemma SumInf_if_1_0_both_is_sum:
  assumes "countable {a. P a}"
  shows "\<^bold>\<Sum>{(if Q1 a then 1 else 0) * f a * (if Q2 a then 1 else 0) | a. P a} = \<^bold>\<Sum>{f a | a. P a \<and> Q1 a \<and> Q2 a}" (is "?A = ?B")
proof -
  have c:"countable {a. P a \<and> Q1 a}" using countable_subset[OF _ assms, of "{a. P a \<and> Q1 a}"] by blast
  have "?A = \<^bold>\<Sum> {f a * (if Q2 a then 1 else 0) |a. P a \<and> Q1 a}"
    using SumInf_if_1_0_left_is_sum[OF assms, of Q1 "\<lambda>a. f a * (if Q2 a then 1 else 0)"]
    unfolding mult.assoc by blast
  then show ?thesis
    using SumInf_if_1_0_right_is_sum[OF c, of f Q2] by presburger
qed
  
end
