theory FiniteMonoidLTS 
  imports "MonoidLTS" "Saturation" "FinFunWellFounded" "FinFunAddUpdate" "FinFunSumSaturation"
begin


section \<open>Locale: finite_monoidLTS\<close>

locale finite_monoidLTS = monoidLTS transition_relation 
  for transition_relation :: "('state::finite, 'weight::monoid_mult) transition set" +
  assumes ts_finite: "finite transition_relation"
begin
sublocale countable_monoidLTS by (standard, fact countable_finite[OF ts_finite])
end


section \<open>Locale: finite_dioidLTS\<close>

locale finite_dioidLTS = finite_monoidLTS transition_relation + dioidLTS transition_relation
  for transition_relation :: "('state::finite, 'weight::bounded_dioid) transition set"
begin
sublocale countable_dioidLTS ..

inductive weight_reach_rule :: "('state::finite \<Rightarrow>f 'weight::bounded_dioid) saturation_rule" where
    add_state: "(p,d,q) \<in> transition_relation \<Longrightarrow> S $ q + (S $ p * d) \<noteq> S $ q 
                \<Longrightarrow> weight_reach_rule S S(q $+= S $ p * d)"

lemma finite_weight_reach_rule_set: "finite {S'. weight_reach_rule S S'}"
proof -
  have "finite {S(q $+= S $ p * d) |p d q. S $ q + S $ p * d \<noteq> S $ q \<and> (p, d, q) \<in> transition_relation}"
    unfolding weight_reach_rule.simps
    using finite_f_P_on_set[OF ts_finite, of "\<lambda>pdq. S(snd(snd pdq) $+= S $ (fst pdq) * (fst (snd pdq)))" "\<lambda>(p,d,q). S $ q + S $ p * d \<noteq> S $ q"]
    by simp
  then have "finite {S(q $+= S $ p * d) |p d q. (p, d, q) \<in> transition_relation \<and> S $ q + S $ p * d \<noteq> S $ q}"
    by (rule back_subst[of finite]) auto
  then show ?thesis
    by (auto simp add: weight_reach_rule.simps)
qed

lemma weight_reach_rule_elim2:
  assumes "weight_reach_rule S S'"
  shows "\<exists>p d q. S' = S(q $+= (S$p * d)) \<and> (p,d,q) \<in> transition_relation \<and> S $ q + (S$p * d) \<noteq> S $ q"
  using assms unfolding weight_reach_rule.simps[of S S'] by presburger

lemma weight_reach_rule_less: "weight_reach_rule S S' \<Longrightarrow> S' < S"
  unfolding weight_reach_rule.simps by (auto simp: add.commute finfun_add_update_less)

lemma weight_reach_rule_less_eq: "weight_reach_rule S S' \<Longrightarrow> S' \<le> S"
  using weight_reach_rule_less by fastforce

lemma weight_reach_star_less_eq: "weight_reach_rule\<^sup>*\<^sup>* S S' \<Longrightarrow> S' \<le> S"
  by (induct rule: rtranclp.induct) (use weight_reach_rule_less in fastforce)+ 

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
  have "\<^bold>\<Sum> {S $ c * l |c l. c \<Midarrow> l \<Rightarrow>\<^sup>* c'} = \<^bold>\<Sum> {S $ c\<^sub>a * l\<^sub>a  * l |c\<^sub>a l\<^sub>a c l. c\<^sub>a \<Midarrow> l\<^sub>a \<Rightarrow>\<^sup>* c \<and> c \<Midarrow> l \<Rightarrow>\<^sup>* c'}"
    apply (rule arg_cong[of _ _ " \<^bold>\<Sum> "])
    using monoid_rtranclp.monoid_rtrancl_refl[of  l_step_relp] monoid_rtranclp_trans[of l_step_relp]
    by (force simp add: mult.assoc)
  moreover
  have "... = \<^bold>\<Sum> {\<^bold>\<Sum> {(S $ c\<^sub>a * l\<^sub>a) * l |c\<^sub>a l\<^sub>a. c\<^sub>a \<Midarrow> l\<^sub>a \<Rightarrow>\<^sup>* c} |c l. c \<Midarrow> l \<Rightarrow>\<^sup>* c'}"
    using SumInf_of_SumInf[of "\<lambda>(c, l). c \<Midarrow> l \<Rightarrow>\<^sup>* c'" "\<lambda>(c\<^sub>a, l\<^sub>a) (c, l). c\<^sub>a \<Midarrow> l\<^sub>a \<Rightarrow>\<^sup>* c"
        "\<lambda>(c\<^sub>a, l\<^sub>a) (c, l). S $ c\<^sub>a * l\<^sub>a * l"
        ]
    using countable_monoid_star_variant2 countable_star_f_c_l by force
  moreover
  have "... = \<^bold>\<Sum> {\<^bold>\<Sum> {S $ c\<^sub>a * l\<^sub>a |c\<^sub>a l\<^sub>a. c\<^sub>a \<Midarrow> l\<^sub>a \<Rightarrow>\<^sup>* c} * l |c l. c \<Midarrow> l \<Rightarrow>\<^sup>* c'}"
    apply (rule arg_cong[of _ _ " \<^bold>\<Sum> "])
    using SumInf_right_distr2[of "\<lambda>c\<^sub>a l\<^sub>a. S $ c\<^sub>a * l\<^sub>a "]
    apply (auto simp add: countable_star_f_c_l)
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
      from this show ?thesis 
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
  using sound_wrt_weight_reach_rule assms unfolding sound_wrt_def by auto

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

lemma weight_reach_step_to_weight_reach_rule: "weight_reach_step transition_relation S = S + \<Sum> {S'. weight_reach_rule S S'}" (is "?A = ?B")
proof -
  have f1:"finite (\<Union>(p, d, q)\<in>transition_relation. {(q, S $ p * d)})" using ts_finite by fast
  have "?A = S + \<Sum> {S(q $+= S $ p * d) |p d q. (p, d, q) \<in> transition_relation}"
    unfolding weight_reach_step_def update_wts_sum_finfun[OF f1, of S] 
    by (rule arg_cong[of _ _ "\<lambda>X. S + \<Sum> X"]) blast
  moreover have "... = S + \<Sum> {S(q $+= S $ p * d) |p d q. (p, d, q) \<in> transition_relation \<and> S $ q + S $ p * d \<noteq> S $ q}" (is "S + \<Sum>?X = S + \<Sum>?Y")
  proof -
    have f1: "finite ?X"
      using finite_f_P_on_set[OF ts_finite, of "\<lambda>pdq. S(snd (snd pdq) $+= S $ (fst pdq) * (fst (snd pdq)))" "\<lambda>x. True"] by simp
    have f2: "finite ?Y" 
      using finite_weight_reach_rule_set[unfolded weight_reach_rule.simps] by force
    have f3: "finite (insert S ?X)" using f1 by fastforce
    have f4: "finite (insert S ?Y)" using f2 by fastforce
    show ?thesis
      unfolding idem_sum_insert[OF f1, of S, symmetric] idem_sum_insert[OF f2, of S, symmetric]
      apply (rule finfun_ext)
      subgoal for a
        unfolding sum_finfun_apply[OF f3, of a] sum_finfun_apply[OF f4, of a]
        by (rule arg_cong[of _ _ \<Sum>]) fastforce
      done
  qed
  ultimately show ?thesis unfolding weight_reach_rule.simps by presburger
qed

inductive non_strict_weight_reach_rule :: "('state::finite \<Rightarrow>f 'weight::bounded_dioid) saturation_rule" where
    "(p,d,q) \<in> transition_relation \<Longrightarrow> non_strict_weight_reach_rule S S(q $+= S $ p * d)"

lemma weight_reach_rule_is_non_equal_pure: "weight_reach_rule = strict_rule non_strict_weight_reach_rule"
proof -
  { fix S S'
    have "(strict_rule non_strict_weight_reach_rule) S S' = weight_reach_rule S S'"
      unfolding strict_rule.simps non_strict_weight_reach_rule.simps weight_reach_rule.simps
      apply safe
       apply fastforce
      by (metis finfun_upd_apply_same)
  } then show ?thesis by presburger
qed

lemma pure_weight_reach_rule_less_eq: "non_strict_weight_reach_rule ts ts' \<Longrightarrow> ts' \<le> ts"
  unfolding non_strict_weight_reach_rule.simps using finfun_add_update_less_eq by fast

lemma pure_weight_reach_rule_mono: "ts\<^sub>3 \<le> ts\<^sub>1 \<Longrightarrow> non_strict_weight_reach_rule ts\<^sub>1 ts\<^sub>2 \<Longrightarrow> \<exists>ts'. non_strict_weight_reach_rule ts\<^sub>3 ts' \<and> ts' \<le> ts\<^sub>2"
  unfolding non_strict_weight_reach_rule.simps 
  by simp (metis add_finfun_apply finfun_add_update_same_mono idempotent_ab_semigroup_add_ord_class.order_prop idempotent_semiring_ord_class.mult_isor)

lemma weight_reach_exec_is_step_exec: 
  "weight_reach_exec transition_relation = step_saturation.step_exec (weight_reach_step transition_relation)"
  unfolding weight_reach_exec_def step_saturation.step_exec_def
            weight_reach_loop_def step_saturation.step_loop_def 
  by auto

lemma saturation_weight_reach_exec:
  "saturation weight_reach_rule S (weight_reach_exec transition_relation S)"
  unfolding weight_reach_rule_is_non_equal_pure weight_reach_exec_is_step_exec
  using sum_saturation_step_exec[of non_strict_weight_reach_rule "weight_reach_step transition_relation" S]
        pure_weight_reach_rule_less_eq pure_weight_reach_rule_mono weight_reach_step_decreasing 
        weight_reach_step_to_weight_reach_rule finite_weight_reach_rule_set 
  unfolding weight_reach_rule_is_non_equal_pure by fast

end

end
