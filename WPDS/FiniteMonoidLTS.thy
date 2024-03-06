theory FiniteMonoidLTS 
  imports "MonoidLTS" "Saturation" "FinFunWellFounded" "FinFunAddUpdate"
begin

locale finite_monoidLTS = monoidLTS transition_relation 
  for transition_relation :: "('state::finite, 'weight::monoid_mult) transition set" +
  assumes ts_finite: "finite transition_relation"
begin
sublocale countable_monoidLTS by (standard, fact countable_finite[OF ts_finite])
end

locale finite_dioidLTS = finite_monoidLTS transition_relation + dioidLTS transition_relation
  for transition_relation :: "('state::finite, 'weight::bounded_idempotent_semiring) transition set"
begin
sublocale countable_dioidLTS ..

inductive weight_reach_rule :: "('state::finite \<Rightarrow>f 'weight::bounded_idempotent_semiring) saturation_rule" where
    add_state: "(p,d,q) \<in> transition_relation \<Longrightarrow> S $ q + (S $ p * d) \<noteq> S $ q 
                \<Longrightarrow> weight_reach_rule S S(q $+= S $ p * d)"

lemma finite_weight_reach_rule_set: "finite {S'. weight_reach_rule S S'}"
  unfolding weight_reach_rule.simps
  using finite_f_P_on_set[OF ts_finite, of "\<lambda>pdq. S(snd(snd pdq) $+= S $ (fst pdq) * (fst (snd pdq)))" "\<lambda>(p,d,q). S $ q + S $ p * d \<noteq> S $ q"]
  apply simp
  by (smt (verit) Collect_cong)

lemma weight_reach_rule_elim2:
  assumes "weight_reach_rule S S'"
  shows "\<exists>p d q. S' = S(q $+= (S$p * d)) \<and> (p,d,q) \<in> transition_relation \<and> S $ q + (S$p * d) \<noteq> S $ q"
  using assms unfolding weight_reach_rule.simps[of S S'] by presburger

lemma weight_reach_rule_less: "weight_reach_rule S S' \<Longrightarrow> S' < S"
  unfolding weight_reach_rule.simps by (auto simp: add.commute finfun_add_update_less)
lemma weight_reach_rule_less_eq: "weight_reach_rule S S' \<Longrightarrow> S' \<le> S"
  using weight_reach_rule_less by fastforce
lemma weight_reach_star_less_eq: "weight_reach_rule\<^sup>*\<^sup>* S S' \<Longrightarrow> S' \<le> S"
  apply (induct rule: rtranclp.induct, simp)
  using weight_reach_rule_less by fastforce

lemma weight_reach_saturation_exi: "\<exists>S'. saturation weight_reach_rule S S'"
  using wfp_class_saturation_exi[of weight_reach_rule S] weight_reach_rule_less by fast

lemma saturated_weight_reach_rule_transition:
  assumes "saturated weight_reach_rule S"
  assumes "(p,d,q) \<in> transition_relation"
  shows "S $ q + (S $ p * d) = S $ q"
  using assms unfolding saturated_def using weight_reach_rule.intros by blast

lemma saturated_weight_reach_rule_leq:
  assumes "saturated weight_reach_rule S"
  assumes "(p,d,q) \<in> transition_relation"
  shows "(S $ p * d) \<ge> S $ q"
  using saturated_weight_reach_rule_transition[OF assms]
  by (simp add: meet.inf.orderI)

lemma weight_reach_saturated_1:
  assumes "saturated weight_reach_rule S"
  assumes "c \<Midarrow>l\<Rightarrow>\<^sup>* c'"
  shows "S$c' \<le> S$c * l"
  using assms(2)
  apply (induct, simp)
  subgoal for a w b l c
    unfolding l_step_relp_def
    using saturated_weight_reach_rule_leq[OF assms(1), of b l c] mult.assoc order.trans
          idempotent_semiring_ord_class.mult_isor[of "S$b" "S$a * w" l]
    by metis
  done

lemma weight_reach_saturated_le: 
  assumes "saturated weight_reach_rule S'"
  assumes "S' \<le> S"
  shows "S'$c' \<le> \<^bold>\<Sum>{S$c * l |c l. c \<Midarrow>l\<Rightarrow>\<^sup>* c'}"
proof -
  have "\<And>c l. c \<Midarrow> l \<Rightarrow>\<^sup>* c' \<Longrightarrow> S' $ c' \<le> S $ c * l"
    subgoal for c l
      using weight_reach_saturated_1[OF assms(1), of c l c'] assms(2)[unfolded less_eq_finfun_def]
            idempotent_semiring_ord_class.mult_isor[of "S' $ c" "S $ c" l]
      by simp
    done
  then show ?thesis
    using weight_reach_saturated_1[OF assms(1), of _ _ c']
          SumInf_bounded_if_set_bounded[OF countable_star_f_c_l[of "\<lambda>c l. S$c * l" c'], of "S'$c'"]
          assms(2)
    by blast
qed  

definition sound_wrt where
  "sound_wrt S' S \<longleftrightarrow> (\<forall>c'. \<^bold>\<Sum>{S $ c * l |c l. c \<Midarrow>l\<Rightarrow>\<^sup>* c'} \<le> S'$c')"

lemma sound_wrt_relf: "sound_wrt S S"
unfolding sound_wrt_def
proof
  fix c'
  have "countable {S $ c * l |c l. c \<Midarrow> l \<Rightarrow>\<^sup>* c'}" 
    using countable_star_f_c_l by fast
  moreover have "S $ c' \<in> {S $ c * l |c l. c \<Midarrow> l \<Rightarrow>\<^sup>* c'}"
    by force
  ultimately show "\<^bold>\<Sum> {S $ c * l |c l. c \<Midarrow> l \<Rightarrow>\<^sup>* c'} \<le> S $ c'" 
    using countable_SumInf_elem by blast
qed

lemma sound_wrt_Sum_leq:
  assumes "sound_wrt S' S"
  shows "\<^bold>\<Sum> {S $ c * l |c l. c \<Midarrow> l \<Rightarrow>\<^sup>* c'} \<le> \<^bold>\<Sum> {S' $ c * l |c l. c \<Midarrow> l \<Rightarrow>\<^sup>* c'}"
proof -
  have nisse2: "\<And>u. countable {S $ c\<^sub>a * l\<^sub>a |c\<^sub>a l\<^sub>a. c\<^sub>a \<Midarrow> l\<^sub>a \<Rightarrow>\<^sup>* u}"
    by (simp add: countable_star_f_c_l)

  have nisse3': "\<And>d'. countable {(d, d') |d. (case d of (c\<^sub>a, l\<^sub>a) \<Rightarrow> \<lambda>(c, l). c\<^sub>a \<Midarrow> l\<^sub>a \<Rightarrow>\<^sup>* c) d'}"
    by (auto simp add: countable_star_f_c_l)
  then have nisse3: "(\<And>d'. case d' of (c, l) \<Rightarrow> c \<Midarrow> l \<Rightarrow>\<^sup>* c' \<Longrightarrow>
            countable {(d, d') |d. (case d of (c\<^sub>a, l\<^sub>a) \<Rightarrow> \<lambda>(c, l). c\<^sub>a \<Midarrow> l\<^sub>a \<Rightarrow>\<^sup>* c) d'})"
    by auto

  have "\<^bold>\<Sum> {S $ c * l |c l. c \<Midarrow> l \<Rightarrow>\<^sup>* c'} = \<^bold>\<Sum> {S $ c\<^sub>a * l\<^sub>a  * l |c\<^sub>a l\<^sub>a c l. c\<^sub>a \<Midarrow> l\<^sub>a \<Rightarrow>\<^sup>* c \<and> c \<Midarrow> l \<Rightarrow>\<^sup>* c'}"
    apply (rule arg_cong[of _ _ " \<^bold>\<Sum> "])
    apply (auto simp add: mult.assoc)
    apply (metis monoid_rtranclp.monoid_rtrancl_refl mult.right_neutral)
    apply (metis monoid_rtranclp_trans)
    done
  moreover
  have "... = \<^bold>\<Sum> {S $ c\<^sub>a * l\<^sub>a  * l |c\<^sub>a l\<^sub>a c l. c \<Midarrow> l \<Rightarrow>\<^sup>* c' \<and> c\<^sub>a \<Midarrow> l\<^sub>a \<Rightarrow>\<^sup>* c}"
    by meson
  moreover
  have "... = \<^bold>\<Sum> {\<^bold>\<Sum> {(S $ c\<^sub>a * l\<^sub>a) * l |c\<^sub>a l\<^sub>a. c\<^sub>a \<Midarrow> l\<^sub>a \<Rightarrow>\<^sup>* c} |c l. c \<Midarrow> l \<Rightarrow>\<^sup>* c'}"
    using SumInf_of_SumInf[of "\<lambda>(c, l). c \<Midarrow> l \<Rightarrow>\<^sup>* c'" "\<lambda>(c\<^sub>a, l\<^sub>a) (c, l). c\<^sub>a \<Midarrow> l\<^sub>a \<Rightarrow>\<^sup>* c"
        "\<lambda>(c\<^sub>a, l\<^sub>a) (c, l). S $ c\<^sub>a * l\<^sub>a * l"
        ]
    using countable_monoid_star_variant2 nisse3

    apply auto
    apply meson
    done
  moreover
  have "... = \<^bold>\<Sum> {\<^bold>\<Sum> {S $ c\<^sub>a * l\<^sub>a |c\<^sub>a l\<^sub>a. c\<^sub>a \<Midarrow> l\<^sub>a \<Rightarrow>\<^sup>* c} * l |c l. c \<Midarrow> l \<Rightarrow>\<^sup>* c'}"
    apply (rule arg_cong[of _ _ " \<^bold>\<Sum> "])
    unfolding SumInf_right_distr[of "{S $ c\<^sub>a * l\<^sub>a |c\<^sub>a l\<^sub>a. c\<^sub>a \<Midarrow> l\<^sub>a \<Rightarrow>\<^sup>* _}" ,OF nisse2]
    apply auto
     apply (smt (verit, ccfv_threshold) Collect_cong)
    apply (smt (verit, ccfv_threshold) Collect_cong)
    done
  moreover
  have "... \<le> \<^bold>\<Sum> {S' $ c * l |c l. c \<Midarrow> l \<Rightarrow>\<^sup>* c'}"
    using assms unfolding sound_wrt_def
    using SumInf_mono_wrt_img_of_set[of "\<lambda>(c, l). c \<Midarrow> l \<Rightarrow>\<^sup>* c'" "\<lambda>(c,l). \<^bold>\<Sum> {S $ c\<^sub>a * l\<^sub>a |c\<^sub>a l\<^sub>a. c\<^sub>a \<Midarrow> l\<^sub>a \<Rightarrow>\<^sup>* c} * l"
        "\<lambda>(c, l). S' $ c * l"]
    by (auto simp add: countable_monoid_star_variant2 idempotent_semiring_ord_class.mult_isol_var)
  ultimately
  show "\<^bold>\<Sum> {S $ c * l |c l. c \<Midarrow> l \<Rightarrow>\<^sup>* c'} \<le> \<^bold>\<Sum> {S' $ c * l |c l. c \<Midarrow> l \<Rightarrow>\<^sup>* c'}"
    by metis
qed

lemma weight_reach_rule_preserves_sound_wrt: 
  assumes "sound_wrt S' S"
  assumes "weight_reach_rule S' S''"
  shows "sound_wrt S'' S"
  using assms(2,1)
proof (induction)
  case (add_state p d q S')
  show ?case
    unfolding sound_wrt_def
  proof
    fix c'
    show "\<^bold>\<Sum> {S $ c * l |c l. c \<Midarrow> l \<Rightarrow>\<^sup>* c'} \<le> S'(q $+= S' $ p * d) $ c'"
    proof (cases "c' = q")
      case True
      have "countable {S $ c * l |c l. c \<Midarrow> l \<Rightarrow>\<^sup>* c'}"
        using countable_star_f_c_l by fast
      have cn: "countable {S' $ c * l |c l. c \<Midarrow> l \<Rightarrow>\<^sup>* c'}"
        by (simp add: countable_star_f_c_l)
      have "\<^bold>\<Sum> {S $ c * l |c l. c \<Midarrow> l \<Rightarrow>\<^sup>* c'} \<le> \<^bold>\<Sum> {S' $ c * l |c l. c \<Midarrow> l \<Rightarrow>\<^sup>* c'}"
        using sound_wrt_Sum_leq add_state by auto
      moreover
      have "p \<Midarrow> d \<Rightarrow>\<^sup>* c'"
        using True add_state(1)
        by (metis l_step_relp_def monoid_rtranclp.monoid_rtrancl_into_rtrancl monoid_rtranclp.monoid_rtrancl_refl mult_1)
      then have "\<^bold>\<Sum> {S' $ c * l |c l. c \<Midarrow> l \<Rightarrow>\<^sup>* c'} \<le> S' $ p * d"
        using countable_SumInf_elem cn by blast
      ultimately
      have "\<^bold>\<Sum> {S $ c * l |c l. c \<Midarrow> l \<Rightarrow>\<^sup>* c'} \<le> S' $ p * d"
        unfolding sound_wrt_def using order_trans by blast
      then have "\<^bold>\<Sum> {S $ c * l |c l. c \<Midarrow> l \<Rightarrow>\<^sup>* c'} \<le> S'$ c' + S' $ p * d"
        using add_state unfolding sound_wrt_def by auto
      from  this show ?thesis 
        unfolding True[symmetric]
        by auto
    next
      case False
      then show ?thesis
        using add_state(1,2) using add_state unfolding sound_wrt_def by auto
    qed
  qed
qed

lemma sound_wrt_weight_reach_rule: 
  assumes "weight_reach_rule\<^sup>*\<^sup>* S S'"
  shows "sound_wrt S' S"
 using assms
proof (induct)
  case base
  then show ?case
    using sound_wrt_relf by auto
next
  case (step S' S'')
  then show ?case
    using weight_reach_rule_preserves_sound_wrt
    by auto
qed

lemma weight_reach_star_le: 
  assumes "weight_reach_rule\<^sup>*\<^sup>* S S'"
  shows "\<^bold>\<Sum>{S $ c * l |c l. c \<Midarrow>l\<Rightarrow>\<^sup>* c'} \<le> S'$c'"
  using sound_wrt_weight_reach_rule assms unfolding sound_wrt_def apply auto
  done

theorem weight_reach_saturation_correct: 
  assumes "saturation weight_reach_rule S S'"
  shows "S'$c' = \<^bold>\<Sum>{S $ c * l |c l. c \<Midarrow>l\<Rightarrow>\<^sup>* c'}"
  using assms unfolding saturation_def
  using weight_reach_saturated_le[of S' S c'] 
        weight_reach_star_le[of S S' c'] 
        weight_reach_star_less_eq[of S S']
  by fastforce


lemma weight_reach_distrib:
  "\<Sum>{\<^bold>\<Sum>{S $ c * l |c l. c \<Midarrow>l\<Rightarrow>\<^sup>* c'} * C' c' |c'. c' \<in> X} = \<^bold>\<Sum>{S $ c * l * C' c' |c l c'. c \<Midarrow> l \<Rightarrow>\<^sup>* c' \<and> c' \<in> X}"
proof -
  have "countable {c'. c' \<in> X}" by blast
  moreover have "\<And>c'. c' \<in> X \<Longrightarrow> countable {((c, l), c') |c l. c \<Midarrow> l \<Rightarrow>\<^sup>* c'}" using countable_star_f_c_l by fast
  ultimately have distr:"\<^bold>\<Sum>{\<^bold>\<Sum>{S $ c * l |c l. c \<Midarrow>l\<Rightarrow>\<^sup>* c'} * C' c' |c'. c' \<in> X} = \<^bold>\<Sum>{S $ c * l * C' c' |c l c'. c \<Midarrow> l \<Rightarrow>\<^sup>* c' \<and> c' \<in> X}"
    using SumInf_of_SumInf_right_distr[of "\<lambda>c'. c' \<in> X" "\<lambda>cl c'. (fst cl) \<Midarrow>(snd cl)\<Rightarrow>\<^sup>* c'" "\<lambda>cl c'. S $ (fst cl) * (snd cl)" "\<lambda>c'. C' c'", simplified]
    by blast
  have f:"finite {\<^bold>\<Sum>{S $ c * l |c l. c \<Midarrow>l\<Rightarrow>\<^sup>* c'} * C' c' |c'. c' \<in> X}" by simp
  show ?thesis using finite_SumInf_is_sum[OF f] distr by argo
qed

theorem weight_reach_saturation_sum_correct: 
  assumes "saturation weight_reach_rule S S'"
  shows "weight_reach (($)S) C' = \<Sum>{S'$c' * (C' c') | c'. True}"
  unfolding weight_reach_def
  using weight_reach_distrib[of S C' UNIV] weight_reach_saturation_correct[OF assms]
  by simp

end

section \<open>Weight reach code\<close>

definition weight_reach_step where "weight_reach_step ts S = update_wts S (\<Union>(p,d,q)\<in>ts. {(q,S $ p * d)})"

definition "weight_reach_loop ts = while_option (\<lambda>s. weight_reach_step ts s \<noteq> s) (weight_reach_step ts)"
definition "weight_reach_exec ts = the o weight_reach_loop ts"

context finite_dioidLTS begin

lemma weight_reach_step_decreasing: "weight_reach_step transition_relation S \<le> S"
  unfolding weight_reach_step_def 
  using update_wts_less_eq[of "\<Union>(p,d,q)\<in>transition_relation. {(q,S $ p * d)}" S] ts_finite
  by fast

lemma weight_reach_exec_terminates: 
  fixes ts :: "('ctr_loc \<times> 'label \<times> 'ctr_loc) \<Rightarrow>f 'weight"
  shows "\<exists>t. weight_reach_loop transition_relation S = Some t"
  unfolding weight_reach_loop_def 
  using wf_rel_while_option_Some[OF wf_less_finfun, 
                                 of "\<lambda>S. weight_reach_step transition_relation S \<le> S" 
                                    "(\<lambda>S. weight_reach_step transition_relation S \<noteq> S)" "weight_reach_step transition_relation" S]
        weight_reach_step_decreasing 
  by fastforce


lemma aux2: "S $ a + \<Sum> {S(q $+= S $ p * d) |p d q. (p, d, q) \<in> transition_relation \<and> S $ q + S $ p * d \<noteq> S $ q} $ a =
       \<Sum> {f $ a |f. f \<in> insert S {S(q $+= S $ p * d) |p d q. (p, d, q) \<in> transition_relation \<and> S $ q + S $ p * d \<noteq> S $ q}}" (is "?A = ?B")
proof - 
  have f1: "finite {S(q $+= S $ p * d) |p d q. (p, d, q) \<in> transition_relation \<and> S $ q + S $ p * d \<noteq> S $ q}" 
    using finite_weight_reach_rule_set[unfolded weight_reach_rule.simps] by force
  have f2: "finite (insert S {S(q $+= S $ p * d) |p d q. (p, d, q) \<in> transition_relation \<and> S $ q + S $ p * d \<noteq> S $ q})" 
    using finite_weight_reach_rule_set[unfolded weight_reach_rule.simps] by force
  have "?A = \<Sum> (insert S {S(q $+= S $ p * d) |p d q. (p, d, q) \<in> transition_relation \<and> S $ q + S $ p * d \<noteq> S $ q}) $ a"
    unfolding add_finfun_apply[symmetric] idem_sum_insert[OF f1, of S, symmetric]
    apply (rule arg_cong[of _ _ "\<lambda>s. \<Sum>s $ a"])
    by blast
  moreover have "... = ?B"
    using sum_finfun_apply[OF f2, of a] by blast
  ultimately show ?thesis by argo
qed
lemma aux3: "S $ a + \<Sum> {S(q $+= S $ p * d) |p d q. (p, d, q) \<in> transition_relation \<and> S $ q + S $ p * d \<noteq> S $ q} $ a =
       \<Sum> {f $ a |f. f \<in> insert S {S(q $+= S $ p * d) |p d q. (p, d, q) \<in> transition_relation}}" (is "?A = ?B")
proof - 
  have f1: "finite {S(q $+= S $ p * d) |p d q. (p, d, q) \<in> transition_relation \<and> S $ q + S $ p * d \<noteq> S $ q}" 
    using finite_weight_reach_rule_set[unfolded weight_reach_rule.simps] by force
  have f2: "finite (insert S {S(q $+= S $ p * d) |p d q. (p, d, q) \<in> transition_relation})" 
    using finite_f_P_on_set[OF ts_finite, of "\<lambda>pdq. S(snd (snd pdq) $+= S $ (fst pdq) * (fst (snd pdq)))" "\<lambda>x. True"] by simp
  have "?A = \<Sum> (insert S {S(q $+= S $ p * d) |p d q. (p, d, q) \<in> transition_relation}) $ a"
    unfolding add_finfun_apply[symmetric] idem_sum_insert[OF f1, of S, symmetric]
    apply (rule arg_cong[of _ _ "\<lambda>s. \<Sum>s $ a"])
    by fastforce
  moreover have "... = ?B"
    using sum_finfun_apply[OF f2, of a] by blast
  ultimately show ?thesis by argo
qed

lemma aux: "S $ a + \<Sum> {b. (a, b) \<in> (\<Union>(p, d, q)\<in>transition_relation. {(q, S $ p * d)})} = 
            S $ a + \<Sum> {S(q $+= S $ p * d) |p d q. (p, d, q) \<in> transition_relation \<and> S $ q + S $ p * d \<noteq> S $ q} $ a" (is "?A = ?B")
  sorry

lemma weight_reach_step_to_weight_reach_rule: "weight_reach_step transition_relation S = S + \<Sum> {S'. weight_reach_rule S S'}"
  apply (rule finfun_ext, simp)
  subgoal for a
    unfolding weight_reach_step_def 
    using update_wts_sum[of "\<Union>(p,d,q)\<in>transition_relation. {(q,S $ p * d)}" S a] ts_finite aux
    unfolding weight_reach_rule.simps by force
  done

lemma weight_reach_rule_exists_t_d:
  assumes "weight_reach_rule S S'"
  shows "\<exists>t d. S' = S(t $+= d) \<and> S $ t + d \<noteq> S $ t"
  using assms weight_reach_rule.simps by fast

lemma weight_reach_rule_sum_not_eq:
  assumes "weight_reach_rule S S'"
  shows "S + \<Sum> {S'. weight_reach_rule S S'} \<noteq> S"
proof (cases "{S'. weight_reach_rule S S'} = {}")
  case True
  then show ?thesis using assms by blast
next
  case False
  have le:"\<Sum> {S'. weight_reach_rule S S'} \<le> S" 
    using sum_smaller_elem[of "{S'. weight_reach_rule S S'}" S, OF _ finite_weight_reach_rule_set[of S] False]
    using weight_reach_rule_less_eq[of S] by blast
  have le':"\<Sum> {S'. weight_reach_rule S S'} \<le> S'"
    unfolding BoundedDioid.idempotent_ab_semigroup_add_ord_class.less_eq_def 
    using idem_sum_elem[OF finite_weight_reach_rule_set[of S], of S'] assms by (simp add: add.commute)
  obtain t d where "S' = S(t $+= d)" and "S' $ t \<noteq> S $ t"
    using assms finfun_upd_apply_same  weight_reach_rule_exists_t_d by force
  then have "S + S' \<noteq> S" using add_finfun_add_update_idem by metis
  then show ?thesis 
    using le le' unfolding BoundedDioid.idempotent_ab_semigroup_add_ord_class.less_eq_def
    using add.commute by metis
qed

lemma weight_reach_rule_weight_reach_step: "weight_reach_rule\<^sup>*\<^sup>* S (weight_reach_step transition_relation S)"
  
  sorry
(*  unfolding pre_star_step_to_pre_star_rule_sum using pre_star_rule_sum.intros[of ts] by fastforce*)
lemma weight_reach_rule_weight_reach_step_k: "weight_reach_rule\<^sup>*\<^sup>* S ((weight_reach_step transition_relation ^^ k) S)"
  by (induct k) (auto elim!: rtranclp_trans intro: weight_reach_rule_weight_reach_step)

lemma saturation_weight_reach_exec: "saturation weight_reach_rule S (weight_reach_exec transition_relation S)"
proof -
  from weight_reach_exec_terminates obtain t where t: "weight_reach_loop transition_relation S = Some t" by blast
  obtain k where k: "t = (weight_reach_step transition_relation ^^ k) S" and eq: "weight_reach_step transition_relation  t = t"
    using while_option_stop2[OF t[unfolded weight_reach_loop_def]] by auto
  have "t = t + \<Sum> {ts. weight_reach_rule t ts}" 
    using eq weight_reach_step_to_weight_reach_rule by force
  then have "\<And>ts. \<not> weight_reach_rule t ts" 
    using weight_reach_rule_sum_not_eq by metis
  then show ?thesis
    unfolding saturation_def saturated_def weight_reach_exec_def o_apply t
    by (simp_all add: weight_reach_rule_weight_reach_step_k k)
qed

lemma weight_reach_saturation_exec_correct:
  assumes "saturation weight_reach_rule S1 S2"
  shows "weight_reach_exec transition_relation S1 = S2"
  using assms
  
  unfolding weight_reach_rule.simps
  apply simp
  oops

end


end