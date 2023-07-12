theory MonoidLTS
  imports "LTS" "MonoidClosure" "BoundedDioid" "HOL-Library.Countable_Set"
begin

\<comment> \<open>If the @{typ 'label} of a LTS is a monoid, we can express the monoid product of labels over a path.\<close>
locale monoidLTS = LTS transition_relation 
  for transition_relation :: "('state::countable, 'label::monoid_mult) transition set" +
  assumes ts_countable: "countable transition_relation"
begin
definition l_step_relp  :: "'state \<Rightarrow> 'label \<Rightarrow> 'state \<Rightarrow> bool" ("(_)/ \<Midarrow> (_)/ \<Rightarrow> (_)/" [70,70,80] 80) where
  "c \<Midarrow>l\<Rightarrow> c' \<longleftrightarrow> (c, l, c') \<in> transition_relation"
abbreviation monoid_star_relp :: "'state \<Rightarrow> 'label \<Rightarrow> 'state \<Rightarrow> bool" ("(_)/ \<Midarrow> (_)/ \<Rightarrow>\<^sup>* (_)/" [90,90,100] 100) where
  "c \<Midarrow>l\<Rightarrow>\<^sup>* c' \<equiv> (monoid_rtranclp l_step_relp) c l c'"
definition monoid_star :: "('state \<times> 'label \<times> 'state) set" where
  "monoid_star = {(c,l,c'). c \<Midarrow>l\<Rightarrow>\<^sup>* c'}"

lemma star_to_closure: "c \<Midarrow>l\<Rightarrow>\<^sup>* c' \<Longrightarrow> (c, l, c') \<in> monoid_rtrancl transition_relation"
  unfolding l_step_relp_def monoid_rtrancl_def by simp

definition monoid_star_witness :: "'state \<Rightarrow> 'label \<Rightarrow> 'state \<Rightarrow> ('state \<times> ('state \<times> 'label \<times> 'state) list)" where
  "monoid_star_witness c l c' = (SOME trace. fst trace = c \<and> is_trace c (snd trace) c' \<and> trace_weight (snd trace) = l \<and> (snd trace) \<in> lists transition_relation)"
abbreviation monoid_star_witness_tuple :: "'state \<times> 'label \<times> 'state \<Rightarrow> ('state \<times> ('state \<times> 'label \<times> 'state) list)" where
  "monoid_star_witness_tuple \<equiv> (\<lambda>(c,l,c'). monoid_star_witness c l c')"
lemma monoid_star_witness_unfold:
  assumes "c \<Midarrow>l\<Rightarrow>\<^sup>* c'"
  assumes "trace = monoid_star_witness c l c'"
  shows "fst trace = c \<and> is_trace c (snd trace) c' \<and> trace_weight (snd trace) = l \<and> (snd trace) \<in> lists transition_relation"
  using monoid_rtrancl_exists_trace[OF star_to_closure[OF assms(1)]] assms(2)
  unfolding monoid_star_witness_def
  by simp (rule someI_ex, simp)

lemma countable_monoid_star_witness: "countable {monoid_star_witness c l c' | c l c'. c \<Midarrow>l\<Rightarrow>\<^sup>* c'}"
proof -
  have subset: "{monoid_star_witness c l c' | c l c'. c \<Midarrow>l\<Rightarrow>\<^sup>* c'} \<subseteq> (UNIV::'state set) \<times> (lists transition_relation)"
  proof
    fix x
    assume assms: "x \<in> {monoid_star_witness c l c' |c l c'. c \<Midarrow> l \<Rightarrow>\<^sup>* c'}"
    have "fst x \<in> (UNIV::'state set)" by fast
    moreover have "snd x \<in> lists transition_relation" using assms monoid_star_witness_unfold by blast
    ultimately show "x \<in> UNIV \<times> lists transition_relation" by (simp add: mem_Times_iff)
  qed
  have "countable ((UNIV::'state set) \<times> (lists transition_relation))"
    using ts_countable by blast
  then show ?thesis using countable_subset[OF subset] by blast
qed

lemma monoid_star_witness_inj_aux:
  assumes "c \<Midarrow> l \<Rightarrow>\<^sup>* c'"
    and "c1 \<Midarrow> l1 \<Rightarrow>\<^sup>* c1'"
    and "monoid_star_witness c l c' = monoid_star_witness c1 l1 c1'"
  shows "c = c1 \<and> l = l1 \<and> c' = c1'"
  using monoid_star_witness_unfold[OF assms(1)] monoid_star_witness_unfold[OF assms(2)] 
        assms(3) is_trace_inj 
  by (cases "snd (monoid_star_witness c l c') \<noteq> []", fastforce) auto
lemma monoid_star_witness_inj: "inj_on monoid_star_witness_tuple monoid_star"
  unfolding monoid_star_def inj_on_def using monoid_star_witness_inj_aux by simp
lemma monoid_star_witness_bij_betw: 
  "bij_betw monoid_star_witness_tuple monoid_star (monoid_star_witness_tuple` monoid_star)"
  unfolding bij_betw_def using monoid_star_witness_inj by blast

lemma countable_monoid_star: "countable monoid_star"
proof -
  have subset:"(monoid_star_witness_tuple` monoid_star) \<subseteq> {monoid_star_witness c l c' | c l c'. c \<Midarrow>l\<Rightarrow>\<^sup>* c'}"
    unfolding monoid_star_def by fast
  then have "countable (monoid_star_witness_tuple` monoid_star)"
    using countable_subset[OF subset countable_monoid_star_witness] by blast
  then show ?thesis using monoid_star_witness_bij_betw countableI_bij2 by fast
qed

lemma countable_f_on_set:"countable X \<Longrightarrow> countable {f x | x. x \<in> X}"
  by (simp add: setcompr_eq_image)

lemma countable_star_f_p: "countable {f (c,l,c') | c l c'. c \<Midarrow>l\<Rightarrow>\<^sup>* c' \<and> P c c'}"
proof -
  have subset:"{(c,l,c') | c l c'. c \<Midarrow>l\<Rightarrow>\<^sup>* c' \<and> P c c'} \<subseteq> monoid_star" unfolding monoid_star_def  by blast
  have "countable {(c,l,c') | c l c'. c \<Midarrow>l\<Rightarrow>\<^sup>* c' \<and> P c c'}" 
    using countable_subset[OF subset countable_monoid_star] by blast
  then show ?thesis using countable_f_on_set by fastforce
qed

lemma monoid_star_is_monoid_rtrancl[simp]: "monoid_star = monoid_rtrancl transition_relation"
  unfolding monoid_star_def l_step_relp_def monoid_rtrancl_def by simp
end

(*
lemma monoidLTS_monoid_star_mono:
  "mono monoidLTS.monoid_star"
  using monoidLTS.monoid_star_is_monoid_rtrancl monoid_rtrancl_is_mono unfolding mono_def
  by simp
*)



\<comment> \<open>If the @{typ 'label} of a LTS is a dioid with additive and multiplicative identities, 
    we can express the meet-over-all-paths value as a generalization of pre-star and post-star.\<close>
locale dioidLTS = monoidLTS transition_relation
  for transition_relation :: "('state::countable, 'label::bounded_idempotent_semiring) transition set"
begin

definition path_seq :: "'label set \<Rightarrow> nat \<Rightarrow> 'label" where
  "path_seq W \<equiv> if W = {} then (\<lambda>_. 0) else SOME f. \<forall>l. l \<in> W \<longleftrightarrow> (\<exists>i. f i = l)"

lemma path_seq_empty[simp]: "path_seq {} i = 0"
  unfolding path_seq_def by simp

lemma countable_set_exists_seq: "countable W \<Longrightarrow> W \<noteq> {} \<Longrightarrow> \<exists>f::(nat\<Rightarrow>'label). \<forall>l. l \<in> W \<longleftrightarrow> (\<exists>i. f i = l)"
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


definition SumInf :: "'label set \<Rightarrow> 'label" ("\<^bold>\<Sum>") where
  "\<^bold>\<Sum> W = suminf (path_seq W)"

lemma countable_obtain_seq:
  assumes "countable W"
  obtains f::"'a \<Rightarrow> nat" where "\<forall>x\<in>W. \<forall>y\<in>W. f x = f y \<longrightarrow> x = y"
  using assms unfolding countable_def inj_on_def by presburger

lemma countable_suminf_exists_sumseq_bound:
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
    obtain f :: "nat \<Rightarrow> 'label" and C :: "nat set" where f_bij:"bij_betw f C W" 
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

lemma countable_suminf_obtains_sumseq_bound:
  assumes "countable W"
  obtains f and N where "\<forall>n\<ge>N. \<^bold>\<Sum> W = sum_seq f n" and "{f i | i. i < N} \<subseteq> W"
  using countable_suminf_exists_sumseq_bound[OF assms] by fast

lemma countable_suminf_obtains_sumseq:
  assumes "countable W"
  obtains f and n where "\<^bold>\<Sum> W = sum_seq f n" and "{f i | i. i < n} \<subseteq> W"
  using countable_suminf_exists_sumseq_bound[OF assms] by fast

lemma suminf_exists_finite_subset:
  fixes W :: "'label set"
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

lemma suminf_obtains_finite_subset:
  fixes W :: "'label set"
  assumes "countable W"
  obtains W' where "W' \<subseteq> W" and "finite W'" and "\<^bold>\<Sum> W = \<Sum> W'"
  using suminf_exists_finite_subset[OF assms] by blast

lemma countable_suminf_elem:
  fixes W :: "'label set"
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
  assumes "finite W" and "finite W'" and "\<^bold>\<Sum> W = \<Sum> W'"
  shows "\<Sum> W' \<le> \<Sum> W"
  using assms(3) countable_suminf_elem[OF countable_finite[OF assms(1)]]
        sum_greater_elem[OF _ assms(1,2)]
  by presburger

lemma SumInf_empty[simp]: "\<^bold>\<Sum> {} = 0"
  unfolding SumInf_def using suminf_finite[of "{}", simplified] path_seq_empty by blast

lemma finite_suminf_is_sum:
  assumes "finite W"
  shows "\<^bold>\<Sum> W = \<Sum> W"
proof -
  obtain W' where subset:"W' \<subseteq> W" and fin:"finite W'" and eq:"\<^bold>\<Sum> W = \<Sum> W'" 
    by (fact suminf_obtains_finite_subset[OF countable_finite[OF assms(1)]])
  have "\<And>w. w \<in> W \<Longrightarrow> \<Sum> W' \<le> w" 
    using eq countable_suminf_elem[OF countable_finite[OF assms(1)]] by presburger
  then have "\<Sum> W' \<le> \<Sum> W" using sum_greater_elem assms fin by blast
  moreover have "\<Sum> W \<le> \<Sum> W'" by (fact sum_superset_less_eq[OF subset assms])
  ultimately have "\<Sum> W' = \<Sum> W" by fastforce
  then show ?thesis using eq by argo
qed

lemma singleton_sum[simp]: "\<^bold>\<Sum> {w} = w"
  using finite_suminf_is_sum by simp

lemma sum_mono: 
  assumes "countable A" and "countable B"
  assumes "A \<subseteq> B"
  shows "\<^bold>\<Sum> A \<ge> \<^bold>\<Sum> B"
proof -
  obtain A' where subsetA:"A' \<subseteq> A" and finA:"finite A'" and eqA:"\<^bold>\<Sum> A = \<Sum> A'" 
    by (fact suminf_obtains_finite_subset[OF assms(1)])
  obtain B' where subsetB:"B' \<subseteq> B" and finB:"finite B'" and eqB:"\<^bold>\<Sum> B = \<Sum> B'" 
    by (fact suminf_obtains_finite_subset[OF assms(2)])
  have "A' \<subseteq> B" using subsetA assms(3) by fast
  then have "\<And>a. a \<in> A' \<Longrightarrow> \<Sum> B' \<le> a" 
    using countable_suminf_elem[OF assms(2)] eqB by auto
  then have "\<Sum> B' \<le> \<Sum> A'" using sum_greater_elem[of A' B'] finA finB by fastforce
  then show ?thesis using eqA eqB by argo
qed

lemma Suminf_bounded_if_set_bounded:
  assumes countableX: "countable X"
  assumes inf_d: "\<forall>x \<in> X. x \<ge> d"
  shows "\<^bold>\<Sum> X \<ge> d"
proof -
  obtain W' where subset:"W' \<subseteq> X" and fin:"finite W'" and eq:"\<^bold>\<Sum> X = \<Sum> W'"
    by (fact suminf_obtains_finite_subset[OF countableX])
  have "\<forall>x \<in> W'. x \<ge> d" using subset inf_d by blast
  then have "\<Sum> W' \<ge> d" using fin
    unfolding BoundedDioid.less_eq_def
    apply (induct rule: finite_induct[OF fin], simp_all)
    subgoal for x F
      using add.assoc[of d x "\<Sum> F"] by simp
    done
  then show ?thesis using eq by argo
qed

lemma sum_insert[simp]:
  assumes "finite (D' ::'label set)"
  shows "\<Sum> (insert d D') = d + \<Sum> D'"
  using assms
proof (induction)
  case empty
  then show ?case 
    by auto
next
  case (insert d' D')
  then show ?case
    apply auto
    by (metis (no_types, lifting) comm_monoid_add_class.sum.insert_if comm_monoid_add_class.sum.insert_remove finite.insertI meet.inf.absorb2 meet.inf_le1)
qed

lemma Suminf_left_distr: 
  assumes "countable D"
  shows "d1 * \<^bold>\<Sum> D = \<^bold>\<Sum> {d1 * d2 | d2. d2 \<in> D}"
proof -
  have "d1 * \<^bold>\<Sum> D \<le> \<^bold>\<Sum> {d1 * d2 | d2. d2 \<in> D}"
    apply (rule Suminf_bounded_if_set_bounded)
    apply auto
    using assms countable_f_on_set apply blast
    by (simp add: assms countable_suminf_elem idempotent_semiring_ord_class.mult_isol)
  have "countable {d1 * d2 | d2. d2 \<in> D}"
    using assms countable_f_on_set by blast
  obtain D' where subset:"D' \<subseteq> D" and fin:"finite D'" and eq:"\<^bold>\<Sum> D = \<Sum> D'"
    by (fact suminf_obtains_finite_subset[OF assms(1)])

  have "finite {d1 * d2 | d2. d2 \<in> D'}"
    by (simp add: fin)

  from fin have "d1 * \<Sum> D' \<ge> \<Sum> {d1 * d2 | d2. d2 \<in> D'}" (* extract lemma? *)
  proof (induction)
    case empty
    then show ?case
      by force
  next
    case (insert d D')
    
    have fff2: "\<Sum> (insert d D') = d + \<Sum>D'"
      using insert.hyps(1) by simp

    have h1: "finite {d1 * d2 |d2. d2 \<in> D'}"
      by (simp add: insert.hyps(1))
    
    have fff: "\<Sum> {d1 * d2 |d2. d2 \<in> insert d D'} = d1 * d + \<Sum>{d1 * d2 |d2. d2 \<in> D'}"
      by (metis Setcompr_eq_image finite_imageI image_insert insert.hyps(1) sum_insert)
  
    show ?case
      unfolding fff fff2
      
      using insert
      by (simp add: meet.le_infI2 semiring_class.distrib_left)
  qed

  have "\<^bold>\<Sum> {d1 * d2 | d2. d2 \<in> D} \<le> \<Sum> {d1 * d2 | d2. d2 \<in> D'}"
    by (smt (verit, best) Collect_mono \<open>countable {d1 * d2 |d2. d2 \<in> D}\<close> \<open>finite {d1 * d2 |d2. d2 \<in> D'}\<close> basic_trans_rules(31) countable_subset finite_suminf_is_sum local.sum_mono subset)

  then have "d1 * \<^bold>\<Sum> D \<ge> \<^bold>\<Sum> {d1 * d2 | d2. d2 \<in> D}"
    using \<open>\<Sum> {d1 * d2 |d2. d2 \<in> D'} \<le> d1 * \<Sum> D'\<close> eq by auto 
  show ?thesis
    using \<open>\<^bold>\<Sum> {d1 * d2 |d2. d2 \<in> D} \<le> d1 * \<^bold>\<Sum> D\<close> \<open>d1 * \<^bold>\<Sum> D \<le> \<^bold>\<Sum> {d1 * d2 |d2. d2 \<in> D}\<close> by auto
qed

lemma Suminf_right_distr: 
  assumes "countable D"
  shows "\<^bold>\<Sum> D * d1 = \<^bold>\<Sum> {d2 * d1 | d2. d2 \<in> D}"
proof -
  have "\<^bold>\<Sum> D * d1 \<le> \<^bold>\<Sum> {d2 * d1 | d2. d2 \<in> D}"
    apply (rule Suminf_bounded_if_set_bounded)
    apply auto
    using assms countable_f_on_set
    apply fastforce
    by (simp add: assms countable_suminf_elem idempotent_semiring_ord_class.mult_isor)

  have "countable {d2 * d1 | d2. d2 \<in> D}"
    using assms countable_f_on_set by fastforce 
  obtain D' where subset:"D' \<subseteq> D" and fin:"finite D'" and eq:"\<^bold>\<Sum> D = \<Sum> D'"
    by (fact suminf_obtains_finite_subset[OF assms(1)])

  have "finite {d2 * d1 | d2. d2 \<in> D'}"
    by (simp add: fin)

  from fin have "\<Sum> D' * d1 \<ge> \<Sum> {d2 * d1 | d2. d2 \<in> D'}" (* extract lemma? *)
  proof (induction)
    case empty
    then show ?case
      by force
  next
    case (insert d D')
    
    have fff2: "\<Sum> (insert d D') = d + \<Sum>D'"
      using insert.hyps(1) by simp

    have h1: "finite {d2 * d1 |d2. d2 \<in> D'}"
      by (simp add: insert.hyps(1))
    
    have fff: "\<Sum> {d2 * d1 |d2. d2 \<in> insert d D'} = d * d1 + \<Sum>{d2 * d1 |d2. d2 \<in> D'}"
      by (metis Setcompr_eq_image finite_imageI image_insert insert.hyps(1) sum_insert)
    
    show ?case
      unfolding fff fff2
      using insert
      by (simp add: meet.le_infI2 semiring_class.distrib_right)
  qed

  have "\<^bold>\<Sum> {d2 * d1 | d2. d2 \<in> D} \<le> \<Sum> {d2 * d1 | d2. d2 \<in> D'}"
    by (smt (verit, best) Collect_mono \<open>countable {d2 * d1 |d2. d2 \<in> D}\<close> \<open>finite {d2 * d1 |d2. d2 \<in> D'}\<close> basic_trans_rules(31) countable_subset finite_suminf_is_sum local.sum_mono subset)

  then have "\<^bold>\<Sum> D * d1 \<ge> \<^bold>\<Sum> {d2 * d1 | d2. d2 \<in> D}"
    using \<open>\<Sum> {d2 * d1 |d2. d2 \<in> D'} \<le>  \<Sum> D' * d1\<close> eq by auto 
  show ?thesis
    using \<open>\<^bold>\<Sum> {d2 * d1 |d2. d2 \<in> D} \<le> \<^bold>\<Sum> D * d1\<close> \<open>\<^bold>\<Sum> D * d1 \<le> \<^bold>\<Sum> {d2 * d1 |d2. d2 \<in> D}\<close> by auto
qed

lemma Suminf_of_Suminf1:
  assumes "countable {d. Q d}"
  assumes "\<And>d. Q d \<Longrightarrow> countable {(d, d')| d d'. P d d'}"
  shows "\<^bold>\<Sum> {\<^bold>\<Sum> {f d d'| d. P d d'} |d'. Q d'} \<ge> \<^bold>\<Sum> {f d d' | d d'. P d d' \<and> Q d'}"
  apply (rule Suminf_bounded_if_set_bounded)
  subgoal
    apply (subgoal_tac "countable {(d, d') |d d'. P d d' \<and> Q d'}")
    subgoal
      using countable_image[of "{(d, d') |d d'. P d d' \<and> Q d'}" "\<lambda>(d, d'). f d d'"]
      apply (simp add: assms(1) setcompr_eq_image)
      done
    subgoal
      using Collect_mono_iff assms(2) countable_subset apply fastforce
      done
    done
  subgoal
    apply auto
    subgoal for d'
      apply (subgoal_tac "countable {f d d' |d d'. P d d' \<and> Q d'} \<and> countable {f d d' |d. P d d'}")
      subgoal 
        apply auto
        apply (smt (verit, del_insts) Collect_mono_iff local.sum_mono)
        done
      subgoal
        apply rule
        subgoal
          apply (subgoal_tac "countable {(d, d') |d d'. P d d' \<and> Q d'}")
          subgoal
            using countable_image[of "{(d, d') |d d'. P d d' \<and> Q d'}" "\<lambda>(d, d'). f d d'"]
            unfolding image_def
            apply auto
            apply (smt (verit, best) Collect_cong)
            done
          subgoal
            using Collect_mono_iff assms(2) countable_subset apply fastforce
            done
          done
        subgoal
          using assms(2)[of d'] 
          apply -
          apply (rule countable_subset[of _ "{f d d' |d d'. P d d'}"])
          subgoal
            apply auto
            done
          subgoal
            using countable_image[of "{(d, d') |d d'. P d d'}" "\<lambda>(d, d'). f d d'"]
            unfolding image_def
            apply auto
            apply (smt (verit, best) Collect_cong)
            done
          done
        done
      done
    done
  done

lemma Suminf_of_Suminf2: (* Are the assumptions reasonable? *)
  assumes "countable {d. Q d}"
  assumes "\<And>d. Q d \<Longrightarrow> countable {(d, d')| d d'. P d d'} "
  shows "\<^bold>\<Sum> {\<^bold>\<Sum> {f d d'| d. P d d'} |d'. Q d'} \<le> \<^bold>\<Sum> {f d d' | d d'. P d d' \<and> Q d'}"
  apply (rule Suminf_bounded_if_set_bounded)
  subgoal
    apply (subgoal_tac "countable {(d, d') |d d'. P d d' \<and> Q d'}")
    subgoal
      using countable_image[of "{(d, d') |d d'. P d d' \<and> Q d'}" "\<lambda>(d, d'). f d d'"]
      apply (smt (verit) Collect_mono countable_subset mem_Collect_eq pair_imageI setcompr_eq_image)
      done
    subgoal
      using Collect_mono_iff assms(2) countable_subset apply fastforce
      done
    done
  subgoal
    apply auto
    subgoal for d d'
      apply (subgoal_tac "\<^bold>\<Sum> {f d d' |d. P d d'} \<le> f d d'")
      subgoal
        apply (subgoal_tac "countable {f d d' |d. P d d'} \<and> countable {\<^bold>\<Sum> {f d d' |d. P d d'} |d'. Q d'}")
        subgoal
          apply auto
          using countable_suminf_elem dual_order.trans apply blast
          done
        subgoal
          apply auto
          subgoal
            using Collect_mono_iff assms countable_subset
            apply (smt (verit, best) \<open>countable {f d d' |d d'. P d d' \<and> Q d'}\<close>) 
            done
          subgoal
            using assms countable_image[of "{d. Q d}"]
            apply (simp add: setcompr_eq_image)
            done
          done
        done
      subgoal
        apply (smt (verit, del_insts) Collect_mono \<open>countable {f d d' |d d'. P d d' \<and> Q d'}\<close> countable_subset countable_suminf_elem mem_Collect_eq)
        done
      done
    done
  done

lemma union_inter:
  assumes "countable A" and "countable B"
  shows "\<^bold>\<Sum> (A \<union> B) + \<^bold>\<Sum> (A \<inter> B) = \<^bold>\<Sum> A + \<^bold>\<Sum> B"
  \<comment> \<open>The reversed orientation looks more natural, but LOOPS as a simprule!\<close>
proof -
  obtain A' where subsetA:"A' \<subseteq> A" and finA:"finite A'" and eqA:"\<^bold>\<Sum> A = \<Sum> A'" 
    by (fact suminf_obtains_finite_subset[OF assms(1)])
  obtain B' where subsetB:"B' \<subseteq> B" and finB:"finite B'" and eqB:"\<^bold>\<Sum> B = \<Sum> B'" 
    by (fact suminf_obtains_finite_subset[OF assms(2)])
  have "\<Sum> A' \<le> \<Sum> A" using finite_sum_less_eq[OF _ finA eqA] assms(1) 
    oops


definition weight_pre_star :: "('state \<Rightarrow> 'label) \<Rightarrow> ('state \<Rightarrow> 'label)" where
  "weight_pre_star C c = \<^bold>\<Sum>{l*(C c') | l c'. c \<Midarrow>l\<Rightarrow>\<^sup>* c'}"
definition weight_post_star :: "('state \<Rightarrow> 'label) \<Rightarrow> ('state \<Rightarrow> 'label)" where
  "weight_post_star C c = \<^bold>\<Sum>{(C c')*l | c' l. c' \<Midarrow>l\<Rightarrow>\<^sup>* c}"
end


end