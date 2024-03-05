theory CountableSum
  imports "BoundedDioid" "Set_More"
begin


definition path_seq :: "'weight::bounded_idempotent_semiring set \<Rightarrow> nat \<Rightarrow> 'weight" where
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


definition SumInf :: "'weight::bounded_idempotent_semiring set \<Rightarrow> 'weight" ("\<^bold>\<Sum>") where
  "\<^bold>\<Sum> W = suminf (path_seq W)"


lemma countable_obtain_seq:
  assumes "countable W"
  obtains f::"'a \<Rightarrow> nat" where "\<forall>x\<in>W. \<forall>y\<in>W. f x = f y \<longrightarrow> x = y"
  using assms unfolding countable_def inj_on_def by presburger

lemma countable_SumInf_exists_sumseq_bound:
  fixes W :: "'weight::bounded_idempotent_semiring set"
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
  fixes W :: "'weight::bounded_idempotent_semiring set"
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
  fixes W :: "'weight::bounded_idempotent_semiring set"
  assumes "countable W"
  obtains W' where "W' \<subseteq> W" and "finite W'" and "\<^bold>\<Sum> W = \<Sum> W'"
  using SumInf_exists_finite_subset[OF assms] by blast

lemma countable_SumInf_elem:
  fixes W :: "'weight::bounded_idempotent_semiring set"
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

lemma SumInf_empty[simp]: "\<^bold>\<Sum> {} = 0"
  unfolding SumInf_def using suminf_finite[of "{}", simplified] path_seq_empty by blast

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
  assumes countableX: "countable X"
  assumes inf_d: "\<forall>x \<in> X. x \<ge> d"
  shows "\<^bold>\<Sum> X \<ge> d"
proof -
  obtain W' where subset:"W' \<subseteq> X" and fin:"finite W'" and eq:"\<^bold>\<Sum> X = \<Sum> W'"
    by (fact SumInf_obtains_finite_subset[OF countableX])
  have "\<forall>x \<in> W'. x \<ge> d" using subset inf_d by blast
  then have "\<Sum> W' \<ge> d" using fin
    unfolding BoundedDioid.less_eq_def
    apply (induct rule: finite_induct[OF fin], simp_all)
    subgoal for x F
      using add.assoc[of d x "\<Sum> F"] by simp
    done
  then show ?thesis using eq by argo
qed

lemma SumInf_left_distr: 
  assumes "countable D"
  shows "d1 * \<^bold>\<Sum> D = \<^bold>\<Sum> {d1 * d2 | d2. d2 \<in> D}"
proof -
  have sumInf_left_distr1: "d1 * \<^bold>\<Sum> D \<le> \<^bold>\<Sum> {d1 * d2 | d2. d2 \<in> D}"
    using SumInf_bounded_if_set_bounded countable_f_on_set[of D "\<lambda>d2. d1 * d2"] assms
    by (force simp add: countable_SumInf_elem idempotent_semiring_ord_class.mult_isol)
  have countable_D_img: "countable {d1 * d2 | d2. d2 \<in> D}"
    using assms countable_f_on_set by blast
  obtain D' where subset:"D' \<subseteq> D" and fin:"finite D'" and eq:"\<^bold>\<Sum> D = \<Sum> D'"
    by (fact SumInf_obtains_finite_subset[OF assms(1)])

  have finite_D'_img: "finite {d1 * d2 | d2. d2 \<in> D'}"
    by (simp add: fin)

  from fin have sumInf_left_distr2: "d1 * \<Sum> D' \<ge> \<Sum> {d1 * d2 | d2. d2 \<in> D'}" (* extract lemma? *)
  proof (induction)
    case empty
    then show ?case
      by force
  next
    case (insert d D')
    have Sum_insert: "\<Sum> (insert d D') = d + \<Sum>D'"
      using insert.hyps(1) by simp
    have Sum_insert_img: "\<Sum> {d1 * d2 |d2. d2 \<in> insert d D'} = d1 * d + \<Sum>{d1 * d2 |d2. d2 \<in> D'}"
      by (metis Setcompr_eq_image finite_imageI image_insert insert.hyps(1) idempotent_comm_monoid_add_class.idem_sum_insert)
    show ?case
      unfolding Sum_insert_img Sum_insert using insert by (simp add: meet.le_infI2 semiring_class.distrib_left)
  qed

  have "\<^bold>\<Sum> {d1 * d2 | d2. d2 \<in> D} \<le> \<Sum> {d1 * d2 | d2. d2 \<in> D'}"
    using Collect_mono[of "\<lambda>d2d1. \<exists>d2. d2d1 = d1 * d2 \<and> d2 \<in> D'" "\<lambda>d2d1. \<exists>d2. d2d1 = d1 * d2 \<and> d2 \<in> D"] 
      SumInf_mono[of "{d1 * d2 | d2. d2 \<in> D'}" "{d1 * d2 | d2. d2 \<in> D}"] subset 
      countable_D_img unfolding finite_SumInf_is_sum[OF finite_D'_img,symmetric] by fastforce

  then have "d1 * \<^bold>\<Sum> D \<ge> \<^bold>\<Sum> {d1 * d2 | d2. d2 \<in> D}"
    using sumInf_left_distr2 eq by auto 
  then show ?thesis
    using sumInf_left_distr1 by auto
qed

lemma SumInf_right_distr: 
  assumes "countable D"
  shows "\<^bold>\<Sum> D * d1 = \<^bold>\<Sum> {d2 * d1 | d2. d2 \<in> D}"
proof -
  have sumInf_right_distr1: "\<^bold>\<Sum> D * d1 \<le> \<^bold>\<Sum> {d2 * d1 | d2. d2 \<in> D}"
    using SumInf_bounded_if_set_bounded countable_f_on_set[of D "\<lambda>d2. d2 * d1"] assms
    by (force simp add: countable_SumInf_elem idempotent_semiring_ord_class.mult_isor)

  have countable_D_img: "countable {d2 * d1 | d2. d2 \<in> D}"
    using assms countable_f_on_set by fastforce 
  obtain D' where subset:"D' \<subseteq> D" and fin:"finite D'" and eq:"\<^bold>\<Sum> D = \<Sum> D'"
    by (fact SumInf_obtains_finite_subset[OF assms(1)])

  have finite_D'_img: "finite {d2 * d1 | d2. d2 \<in> D'}"
    by (simp add: fin)

  from fin have sumInf_right_distr2: "\<Sum> D' * d1 \<ge> \<Sum> {d2 * d1 | d2. d2 \<in> D'}" (* extract lemma? *)
  proof (induction)
    case empty
    then show ?case
      by force
  next
    case (insert d D')
    have Sum_insert: "\<Sum> (insert d D') = d + \<Sum>D'"
      using insert.hyps(1) by simp
    have Sum_insert_img: "\<Sum> {d2 * d1 |d2. d2 \<in> insert d D'} = d * d1 + \<Sum>{d2 * d1 |d2. d2 \<in> D'}"
      by (metis Setcompr_eq_image finite_imageI image_insert insert.hyps(1) idempotent_comm_monoid_add_class.idem_sum_insert)
    show ?case
      unfolding Sum_insert_img Sum_insert using insert by (simp add: meet.le_infI2 semiring_class.distrib_right)
  qed

  have "\<^bold>\<Sum> {d2 * d1 | d2. d2 \<in> D} \<le> \<Sum> {d2 * d1 | d2. d2 \<in> D'}"
    using Collect_mono[of "\<lambda>d2d1. \<exists>d2. d2d1 = d2 * d1 \<and> d2 \<in> D'" "\<lambda>d2d1. \<exists>d2. d2d1 = d2 * d1 \<and> d2 \<in> D"] 
      SumInf_mono[of "{d2 * d1 | d2. d2 \<in> D'}" "{d2 * d1 | d2. d2 \<in> D}"] subset 
      countable_D_img unfolding finite_SumInf_is_sum[OF finite_D'_img,symmetric] by fastforce

  then have "\<^bold>\<Sum> D * d1 \<ge> \<^bold>\<Sum> {d2 * d1 | d2. d2 \<in> D}"
    using sumInf_right_distr2 eq by auto 
  then show ?thesis
    using sumInf_right_distr1 by auto
qed

lemma SumInf_of_SumInf_countable1:
  assumes "countable {d'. Q d'}"
  assumes "\<And>d'. Q d' \<Longrightarrow> countable {(d, d')| d. P d d'}"
  shows "countable {\<^bold>\<Sum> {f d d' |d. P d d'} |d'. Q d'}"
  using countable_image[of "{d'. Q d'}" "\<lambda>d'. \<^bold>\<Sum> {f d d' |d. P d d'}", OF assms(1)]
  by (simp add: image_Collect)

lemma SumInf_of_SumInf_countable2:
  assumes "countable {d'. Q d'}"
  assumes "\<And>d'. Q d' \<Longrightarrow> countable {(d, d')| d. P d d'}"
  shows "countable {f d d' |d d'. P d d' \<and> Q d'}"
proof -
  have "countable (\<Union>((\<lambda>d'. {(d,d')|d. P d d'}) ` {d'. Q d'}))"
    using assms(1) assms(2) by blast
  moreover
  have "(\<Union>d'\<in>{d'. Q d'}. {(d, d') |d. P d d'}) = {(d, d') |d d'. P d d' \<and> Q d'}"
    by auto
  ultimately
  have "countable {(d, d') |d d'. P d d' \<and> Q d'}"
    by auto
  then show "countable {f d d' |d d'. P d d' \<and> Q d'}"
    using countable_image[of "{(d, d') |d d'. P d d' \<and> Q d'}" "\<lambda>(d, d'). f d d'"]
      Collect_cong[of "\<lambda>fdd'. \<exists>d d'. P d d' \<and> Q d' \<and> fdd' = f d d'" "\<lambda>fdd'. \<exists>d d'. fdd' = f d d' \<and> P d d' \<and> Q d' "]
    unfolding image_def by fastforce
qed

lemma countable_image_prod:
  assumes "countable {(d, d')| d. P d d'}"
  shows "countable {f d d' |d. P d d'}"
  using assms countable_image[of "{(d, d') |d . P d d'}" "\<lambda>(d, d'). f d d'"]
    Collect_cong[of "\<lambda>fdd'. \<exists>d. P d d' \<and> fdd' = f d d'" "\<lambda>fdd'. \<exists>d. fdd' = f d d' \<and> P d d'"]
  unfolding image_def by fastforce

lemma SumInf_of_SumInf_geq: (* Are the assumptions reasonable? *)
  assumes "countable {d'. Q d'}"
  assumes "\<And>d'. Q d' \<Longrightarrow> countable {(d, d')| d. P d d'}"
  shows "\<^bold>\<Sum> {\<^bold>\<Sum> {f d d'| d. P d d'} |d'. Q d'} \<ge> \<^bold>\<Sum> {f d d' | d d'. P d d' \<and> Q d'}"
proof (rule SumInf_bounded_if_set_bounded)
  show "countable {\<^bold>\<Sum> {f d d' |d. P d d'} |d'. Q d'}"
    using SumInf_of_SumInf_countable1 assms by blast
  have count: "countable {f d d' |d d'. P d d' \<and> Q d'}"
    using  SumInf_of_SumInf_countable2 assms by auto

  have "\<And>d'. Q d' \<Longrightarrow> \<^bold>\<Sum> {f d d' |d d'. P d d' \<and> Q d'} \<le> \<^bold>\<Sum> {f d d' |d. P d d'}"
  proof -
    fix d'
    assume Qd': "Q d'"
    show "\<^bold>\<Sum> {f d d' |d d'. P d d' \<and> Q d'} \<le> \<^bold>\<Sum> {f d d' |d. P d d'}"
      using count Collect_mono_iff[of "\<lambda>fdd'. \<exists>d. fdd' = f d d' \<and> P d d'" "\<lambda>fdd'. \<exists>d d'. fdd' = f d d' \<and> P d d' \<and> Q d'"]
            SumInf_mono Qd' by auto
  qed
  then show "\<forall>fdd'\<in>{\<^bold>\<Sum> {f d d' |d. P d d'} |d'. Q d'}. \<^bold>\<Sum> {f d d' |d d'. P d d' \<and> Q d'} \<le> fdd'"
    by auto
qed

lemma SumInf_of_SumInf_leq: (* Are the assumptions reasonable? *)
  assumes "countable {d'. Q d'}"
  assumes "\<And>d'. Q d' \<Longrightarrow> countable {(d, d')| d. P d d'} "
  shows "\<^bold>\<Sum> {\<^bold>\<Sum> {f d d'| d. P d d'} |d'. Q d'} \<le> \<^bold>\<Sum> {f d d' | d d'. P d d' \<and> Q d'}"
proof (rule SumInf_bounded_if_set_bounded)
  show count: "countable {f d d' |d d'. P d d' \<and> Q d'}"
    using SumInf_of_SumInf_countable2 assms by blast

  have count2: "countable {\<^bold>\<Sum> {f d d' |d. P d d'} |d'. Q d'}"
    using SumInf_of_SumInf_countable1 assms by blast

  have "\<And>d d'. P d d' \<Longrightarrow> Q d' \<Longrightarrow> \<^bold>\<Sum> {\<^bold>\<Sum> {f d d' |d. P d d'} |d'. Q d'} \<le> f d d'"
  proof -
    fix d d' 
    assume Pdd': "P d d'"
    assume Qd': "Q d'"
    have "countable {f d d' |d. P d d'}"
      using Qd' assms(2)[of d'] countable_image_prod by fastforce
    then have "\<^bold>\<Sum> {f d d' |d. P d d'} \<le> f d d'"
      using Pdd' countable_SumInf_elem by auto
    then show "\<^bold>\<Sum> {\<^bold>\<Sum> {f d d' |d. P d d'} |d'. Q d'} \<le> f d d'"
      using countable_SumInf_elem dual_order.trans Qd' count2 by blast
  qed
  then show "\<forall>fdd'\<in>{f d d' |d d'. P d d' \<and> Q d'}. \<^bold>\<Sum> {\<^bold>\<Sum> {f d d' |d. P d d'} |d'. Q d'} \<le> fdd'"
    by auto
qed

lemma SumInf_of_SumInf: (* Are the assumptions reasonable? *)
  assumes "countable {d'. Q d'}"
  assumes "\<And>d'. Q d' \<Longrightarrow> countable {(d, d')| d. P d d'} "
  shows "\<^bold>\<Sum> {\<^bold>\<Sum> {f d d'| d. P d d'} |d'. Q d'} = \<^bold>\<Sum> {f d d' | d d'. P d d' \<and> Q d'}"
  using SumInf_of_SumInf_geq[of Q P f] SumInf_of_SumInf_leq[of Q P f] assms(1,2) by auto


lemma SumInf_of_SumInf_fst_arg: (* not used... *)
  assumes "countable {d'. Q d'}"
      and "\<And>d'. Q d' \<Longrightarrow> countable {(d, d')| d. P d d'} "
    shows "\<^bold>\<Sum> {\<^bold>\<Sum> {d. P d d'} |d'. Q d'} = \<^bold>\<Sum> {d | d d'. P d d' \<and> Q d'}"
  using SumInf_of_SumInf[of _ _ "\<lambda>x y. x"] assms by auto

lemma SumInf_of_SumInf_right_distr:
  assumes "countable {d'. Q d'}"
      and "\<And>d'. Q d' \<Longrightarrow> countable {(d, d') |d. P d d'}"
    shows "\<^bold>\<Sum> {\<^bold>\<Sum> {f d d'| d. P d d'} * g d' |d'. Q d'} = \<^bold>\<Sum> {f d d' * g d' | d d'. P d d' \<and> Q d'}"
proof -
  have eql: "\<forall>d'. {f d d' * g d' |d. P d d'} = {d1 * g d' |d1. \<exists>d. d1 = f d d' \<and> P d d'}"
    by auto
  have "\<And>d'. Q d' \<Longrightarrow> countable {f d d' |d. P d d'}"
    using assms(2) countable_f_on_P_Q_set2[of P f "\<lambda>x y. True", simplified] countable_image_prod setcompr_eq_image by fast
  then have "\<And>d'. Q d' \<Longrightarrow> \<^bold>\<Sum> {f d d' |d. P d d'} * g d' = \<^bold>\<Sum> {d2 * g d' |d2. d2 \<in> {f d d' |d. P d d'}}"
    using SumInf_right_distr[of "{f d _ |d. P d _}" "g _"] by simp
  then have "\<^bold>\<Sum> {\<^bold>\<Sum> {f d d'| d. P d d'} * g d' |d'. Q d'} = \<^bold>\<Sum> {\<^bold>\<Sum> {d1 * g d' |d1. d1 \<in> {f d d' |d. P d d'}} |d'. Q d'}"
    by (simp add: setcompr_eq_image)
  also have "... =  \<^bold>\<Sum> {f d d' * g d' | d d'. P d d' \<and> Q d'}"
    using eql SumInf_of_SumInf[of Q P "\<lambda>d d'. f d d' * g d'"] assms by auto
  finally show ?thesis .
qed

lemma SumInf_of_SumInf_left_distr:
  assumes "countable {d'. Q d'}"
      and "\<And>d'. Q d' \<Longrightarrow> countable {(d, d') |d. P d d'}"
    shows "\<^bold>\<Sum> {g d' * \<^bold>\<Sum> {f d d'| d. P d d'} |d'. Q d'} = \<^bold>\<Sum> {g d' * f d d' | d d'. P d d' \<and> Q d'}"
proof -
  have eql: "\<forall>d'. {g d' * f d d' |d. P d d'} = {g d' * d1 |d1. \<exists>d. d1 = f d d' \<and> P d d'}"
    by auto
  have "\<And>d'. Q d' \<Longrightarrow> countable {f d d' |d. P d d'}"
    using assms(2) countable_f_on_P_Q_set2[of P f "\<lambda>x y. True", simplified] countable_image_prod setcompr_eq_image by fast
  then have "\<And>d'. Q d' \<Longrightarrow> g d' * \<^bold>\<Sum> {f d d' |d. P d d'} = \<^bold>\<Sum> {g d' * d2 |d2. d2 \<in> {f d d' |d. P d d'}}"
    using SumInf_left_distr[of "{f d _ |d. P d _}" "g _"] by simp
  then have "\<^bold>\<Sum> {g d' * \<^bold>\<Sum> {f d d'| d. P d d'} |d'. Q d'} = \<^bold>\<Sum> {\<^bold>\<Sum> {g d' * d1 |d1. d1 \<in> {f d d' |d. P d d'}} |d'. Q d'}"
    by (simp add: setcompr_eq_image)
  also have "... =  \<^bold>\<Sum> {g d' * f d d' | d d'. P d d' \<and> Q d'}"
    using eql SumInf_of_SumInf[of Q P "\<lambda>d d'. g d' * f d d'"] assms by auto
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
  assumes "countable {d . X d}"
  assumes "d \<le> (d' :: 'weight::bounded_idempotent_semiring)"
  shows "\<^bold>\<Sum> {d * d''| d''. X d''} \<le> \<^bold>\<Sum> {d' * d''| d''. X d''}"
  by (rule SumInf_bounded_by_SumInf_if_members_bounded)
     (use assms idempotent_semiring_ord_class.mult_isor countable_setcompr[of X] in auto)

lemma SumInf_mono_wrt_img_of_set: 
  assumes "countable {x. X x}"
  assumes "\<forall>t. X t \<longrightarrow> f t \<le> g t"
  shows "\<^bold>\<Sum> {f t| t. X t} \<le> \<^bold>\<Sum> {g t| t. X t}"
  by (rule SumInf_bounded_by_SumInf_if_members_bounded)
     (use assms countable_setcompr[of X] in auto)

lemma SumInf_insert_0:
  assumes "countable X"
  shows "\<^bold>\<Sum> X = \<^bold>\<Sum> (insert 0 X)"
proof (cases "X = {}")
  case True
  then show ?thesis by simp
next
  case False
  have "countable (insert 0 X)" using assms by blast
  then have "\<^bold>\<Sum> X \<le> \<^bold>\<Sum> (insert 0 X)"
    using SumInf_bounded_by_SumInf_if_members_bounded[OF assms] False by fastforce
  moreover have "\<^bold>\<Sum> X \<ge> \<^bold>\<Sum> (insert 0 X)"
    using SumInf_mono[of X "insert 0 X"] assms by auto
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

lemma SumInf_split_Qor0:
  assumes "countable {d. P d}"
  assumes "(\<And>t. \<not> Q t \<Longrightarrow> f t = 0)"
  assumes "(\<And>t. Q t \<Longrightarrow> f t = g t)"
  shows "\<^bold>\<Sum> {f t| t. P t} = \<^bold>\<Sum> {g t| t. P t \<and> Q t}"
proof -
  have "{f t| t. P t} \<union> {0} = {g t| t. P t \<and> Q t} \<union> {0}" using assms by force
  then show ?thesis 
    using SumInf_equal_with_0[OF countable_setcompr[OF assms(1), of f]] by simp
qed



end