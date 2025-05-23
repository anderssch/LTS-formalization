theory FinFunSumSaturation
  imports "Saturation" "FinFunAddUpdate"
begin

inductive strict_rule :: "'t saturation_rule \<Rightarrow> 't saturation_rule" for rule where
  rule_to_strict_rule: "rule ts ts' \<Longrightarrow> ts \<noteq> ts' \<Longrightarrow> strict_rule rule ts ts'"

inductive weak_rule :: "'t::idempotent_ab_semigroup_add_ord saturation_rule \<Rightarrow> 't saturation_rule" for rule where
  rule_to_weak_rule: "rule ts ts'' \<Longrightarrow> ts'' \<le> ts' \<Longrightarrow> ts' < ts \<Longrightarrow> weak_rule rule ts ts'"

lemma rule_star_eq_strict_rule_star: "rule\<^sup>*\<^sup>* = (strict_rule rule)\<^sup>*\<^sup>*"
  unfolding eq_iff
  apply safe
  using mono_rtranclp[of rule "(strict_rule rule)\<^sup>*\<^sup>*", simplified]
        r_into_rtranclp[of "strict_rule rule", OF rule_to_strict_rule[of rule]]
   apply blast
  subgoal for x y
    apply (induct rule: rtranclp_induct, simp)
    by (metis rtranclp.rtrancl_into_rtrancl strict_rule.cases)
  done

lemma weak_rule_mono: "rule \<le> rule' \<Longrightarrow> weak_rule rule \<le> weak_rule rule'"
  by safe (metis rev_predicate2D weak_rule.simps)
lemma weak_star_mono: "rule \<le> rule' \<Longrightarrow> (weak_rule rule)\<^sup>*\<^sup>* \<le> (weak_rule rule')\<^sup>*\<^sup>*"
  by (fact rtranclp_mono[OF weak_rule_mono])


section \<open>Locale: rule_saturation\<close>
locale rule_saturation =
  fixes rule :: "'t::idempotent_ab_semigroup_add_ord saturation_rule"
  assumes rule_less_eq: "rule ts ts' \<Longrightarrow> ts' \<le> ts"
  assumes rule_mono: "ts\<^sub>3 \<le> ts\<^sub>1 \<Longrightarrow> rule ts\<^sub>1 ts\<^sub>2 \<Longrightarrow> \<exists>ts'. rule ts\<^sub>3 ts' \<and> ts' \<le> ts\<^sub>2"
begin

lemma rule_star_less_eq: "rule\<^sup>*\<^sup>* ts ts' \<Longrightarrow> ts' \<le> ts"
  apply (induct rule: rtranclp_induct, simp)
  using rule_less_eq by fastforce

lemma rule_exists_addition: "rule ts ts' \<Longrightarrow> \<exists>a. ts' = ts + a"
  using order_prop rule_less_eq add.commute by metis

lemma weak_rule_exists_addition: "weak_rule rule a b \<Longrightarrow> \<exists>c. b = a + c"
  unfolding weak_rule.simps by (metis meet.inf.absorb4) 

lemma rule_add_extend: 
  assumes "rule ts\<^sub>1 ts\<^sub>2"
  shows "\<exists>ts'. rule (ts + ts\<^sub>1) (ts + ts') \<and> ts' \<le> ts\<^sub>2"
proof -
  obtain ts' where ts': "rule (ts + ts\<^sub>1) ts'" "ts' \<le> ts\<^sub>2"
    using rule_mono[of "ts + ts\<^sub>1" ts\<^sub>1 ts\<^sub>2] assms by auto
  then have "rule (ts + ts\<^sub>1) (ts + ts')" 
    using rule_less_eq[OF ts'(1)] meet.inf.absorb2 by fastforce
  then show ?thesis using ts'(2) by blast
qed

lemma strict_rule_less: "strict_rule rule a b \<Longrightarrow> b < a"
  using rule_less_eq by (metis strict_rule.simps order_le_imp_less_or_eq)

lemma strict_rule_less_eq: "strict_rule rule a b \<Longrightarrow> b \<le> a"
  using strict_rule_less by fastforce

lemma strict_rule_star_less_eq: "(strict_rule rule)\<^sup>*\<^sup>* ts ts' \<Longrightarrow> ts' \<le> ts"
  apply (induct rule: rtranclp_induct, simp)
  using strict_rule_less_eq by fastforce

lemma eq_some_strict_not_exists:
  "ts = ts + Eps (strict_rule rule ts) \<Longrightarrow> \<not> Ex (strict_rule rule ts)"
  using strict_rule_less[OF someI[of "strict_rule rule ts"]]
        less_eq_def[of ts "Eps (strict_rule rule ts)"]
  by force

lemma weak_rule_less: "weak_rule rule ts ts' \<Longrightarrow> ts' < ts"
  using weak_rule.simps by blast

lemma weak_rule_less_eq: "weak_rule rule ts ts' \<Longrightarrow> ts' \<le> ts"
  using weak_rule_less  by fastforce

lemma weak_rule_star_less_eq: "(weak_rule rule)\<^sup>*\<^sup>* ts ts' \<Longrightarrow> ts' \<le> ts"
  apply (induct rule: rtranclp_induct, simp)
  using weak_rule_less_eq by fastforce

lemma weak_rule_intro: "strict_rule rule ts ts' \<Longrightarrow> weak_rule rule ts ts'"
  using rule_to_weak_rule[of rule ts ts'] strict_rule.cases[of rule ts ts'] order_refl
  by (metis strict_rule_less)
lemma strict_le_weak: "strict_rule rule \<le> weak_rule rule"
  using weak_rule_intro by blast
lemma strict_star_le_weak_star: "(strict_rule rule)\<^sup>*\<^sup>* \<le> (weak_rule rule)\<^sup>*\<^sup>*"
  by (fact rtranclp_mono[OF strict_le_weak])
lemma weak_rule_star_intro: "(strict_rule rule)\<^sup>*\<^sup>* ts ts' \<Longrightarrow> (weak_rule rule)\<^sup>*\<^sup>* ts ts'"
  using strict_star_le_weak_star by blast
lemma rule_to_weak_rule_star: "rule \<le> (weak_rule rule)\<^sup>*\<^sup>*"
  using r_into_rtranclp[of rule] rule_star_eq_strict_rule_star[of rule] strict_star_le_weak_star
  by auto
lemma rule_star_to_weak_rule_star: "rule\<^sup>*\<^sup>* \<le> (weak_rule rule)\<^sup>*\<^sup>*"
  using rule_star_eq_strict_rule_star strict_star_le_weak_star by metis

lemma weak_rule_star_to_strict_rule_star:
  assumes "(weak_rule rule)\<^sup>*\<^sup>* ts ts'"
  shows "\<exists>ts''. (strict_rule rule)\<^sup>*\<^sup>* ts ts'' \<and> ts'' \<le> ts'"
  using assms
proof (induction rule: rtranclp_induct)
  case base
  then show ?case by blast
next
  case (step ts\<^sub>1 ts\<^sub>2)
  obtain ts'' where ts'': "rule ts\<^sub>1 ts''" "ts'' \<le> ts\<^sub>2"
    using step(2) weak_rule.simps by blast
  obtain ts\<^sub>3 where ts3: "(strict_rule rule)\<^sup>*\<^sup>* ts ts\<^sub>3" "ts\<^sub>3 \<le> ts\<^sub>1"
    using step(3) by blast
  obtain ts\<^sub>4 where ts4: "rule ts\<^sub>3 ts\<^sub>4" "ts\<^sub>4 \<le> ts''"
    using rule_mono[of ts\<^sub>3 ts\<^sub>1 ts''] ts3(2) ts''(1) by fast
  have "ts\<^sub>4 \<le> ts\<^sub>2" using ts4(2) ts''(2) by fastforce
  show ?case
  proof (cases "ts\<^sub>3 = ts\<^sub>4")
    case True
    then show ?thesis using \<open>ts\<^sub>4 \<le> ts\<^sub>2\<close> ts3(1) by blast
  next
    case False
    then have "strict_rule rule ts\<^sub>3 ts\<^sub>4"
      using ts4(1) strict_rule.intros by metis
    then show ?thesis using \<open>ts\<^sub>4 \<le> ts\<^sub>2\<close> rtranclp.rtrancl_into_rtrancl[OF ts3(1)]
      by blast
  qed
qed

lemma weak_rule_step_mono:
  assumes "ts\<^sub>2 \<le> ts\<^sub>1"
  assumes "weak_rule rule ts\<^sub>1 ts\<^sub>3"
  shows "(weak_rule rule)\<^sup>*\<^sup>* ts\<^sub>2 (ts\<^sub>2 + ts\<^sub>3)"
proof -
  obtain a\<^sub>3 where ts3: "ts\<^sub>3 = ts\<^sub>1 + a\<^sub>3" 
    using weak_rule_exists_addition[OF assms(2)] by fast
  obtain ts' where ts': "rule ts\<^sub>1 ts'" "ts' \<le> ts\<^sub>3"
    using assms(2) weak_rule.simps by blast
  obtain ts\<^sub>4 where ts4: "rule ts\<^sub>2 ts\<^sub>4" "ts\<^sub>4 \<le> ts'"
    using rule_mono assms(1) ts'(1) by blast
  have eq: "ts\<^sub>2 + a\<^sub>3 = ts\<^sub>2 + ts\<^sub>3" unfolding ts3
    using assms(1)[unfolded less_eq_def, symmetric] by (metis meet.inf_assoc)
  show ?thesis proof (cases "ts\<^sub>2 = ts\<^sub>2 + a\<^sub>3")
    case True
    then show ?thesis using eq unfolding ts3 by simp
  next
    case False
    then have le:"ts\<^sub>2 + a\<^sub>3 < ts\<^sub>2" by (simp add: order_le_neq_trans)
    have "weak_rule rule ts\<^sub>2 (ts\<^sub>2 + a\<^sub>3)"
      using weak_rule.intros[of rule, OF ts4(1) _ le]
            ts4(2) ts'(2)[unfolded ts3] rule_less_eq[OF ts4(1)] 
      by fastforce
    then show ?thesis using eq unfolding ts3 by auto
  qed
qed

lemma weak_rule_step_mono':
  assumes "(weak_rule rule)\<^sup>*\<^sup>* ts\<^sub>1 ts\<^sub>2"
  assumes "weak_rule rule ts\<^sub>1 ts\<^sub>3"
  shows "(weak_rule rule)\<^sup>*\<^sup>* ts\<^sub>1 (ts\<^sub>2 + ts\<^sub>3)"
  using rtranclp_trans[of "weak_rule rule" ts\<^sub>1 ts\<^sub>2 "ts\<^sub>2 + ts\<^sub>3", OF assms(1)]
  using assms(2) weak_rule_star_less_eq[OF assms(1)] weak_rule_step_mono by simp

lemma weak_rule_add_extend:
  assumes "weak_rule rule ts\<^sub>1 ts\<^sub>2"
  assumes "ts + ts\<^sub>1 \<noteq> ts + ts\<^sub>2"
  shows "weak_rule rule (ts + ts\<^sub>1) (ts + ts\<^sub>2)"
proof -
  obtain ts' where ts': "rule ts\<^sub>1 ts'" "ts' \<le> ts\<^sub>2" (*"ts\<^sub>1 \<noteq> ts\<^sub>2"*)
    by (metis assms(1) weak_rule.simps)
  obtain ts'' where ts'': "rule (ts + ts\<^sub>1) (ts + ts'')" "ts'' \<le> ts'"
    using ts'(1) rule_add_extend by blast
  have "ts + ts\<^sub>2 < ts + ts\<^sub>1" using assms(2) weak_rule_less[OF assms(1)]
    by (simp add: meet.inf.strict_order_iff meet.inf_commute meet.inf_left_commute)
  then show ?thesis                                                                                                  
    using rule_to_weak_rule[of rule "ts + ts\<^sub>1" "ts + ts''" "ts + ts\<^sub>2", OF ts''(1)]
    using order.trans[OF ts''(2) ts'(2)] meet.inf_mono by blast
qed

lemma weak_rule_add_mono:
  assumes "(weak_rule rule)\<^sup>*\<^sup>* ts (ts + ts\<^sub>1)"
  assumes "(weak_rule rule) ts\<^sub>1 ts\<^sub>2"
  shows "(weak_rule rule)\<^sup>*\<^sup>* ts (ts + ts\<^sub>2)"
proof (cases "ts + ts\<^sub>1 = ts + ts\<^sub>2")
  case True
  then show ?thesis using assms(1) by simp
next
  case False
  then have "(weak_rule rule) (ts + ts\<^sub>1) (ts + ts\<^sub>2)" 
    using assms(2) weak_rule_add_extend by blast
  then show ?thesis using assms(1) by simp
qed

lemma weak_rule_add_star_mono:
  assumes "(weak_rule rule)\<^sup>*\<^sup>* ts\<^sub>1 ts\<^sub>2"
  assumes "(weak_rule rule)\<^sup>*\<^sup>* ts (ts + ts\<^sub>1)"
  shows "(weak_rule rule)\<^sup>*\<^sup>* ts (ts + ts\<^sub>2)"
  using assms(1,2)
  by (induct rule: rtranclp_induct, simp_all add: weak_rule_add_mono)

lemma weak_rule_star_mono:
  assumes "(weak_rule rule)\<^sup>*\<^sup>* ts\<^sub>1 ts\<^sub>2"
  assumes "(weak_rule rule)\<^sup>*\<^sup>* ts\<^sub>1 ts\<^sub>3"
  shows "(weak_rule rule)\<^sup>*\<^sup>* ts\<^sub>2 (ts\<^sub>2 + ts\<^sub>3)"
    using assms(2,1)
proof (induction rule: converse_rtranclp_induct)
  case base
  then show ?case by (metis meet.inf.orderE weak_rule_star_less_eq rtranclp.simps)
next
  case (step ts\<^sub>1' ts\<^sub>3')
  show ?case using weak_rule_add_star_mono[OF step(2) weak_rule_step_mono[OF weak_rule_star_less_eq[OF step(4)] step(1)]] 
    by blast
qed

lemma saturated_non_equal_to_weak:
  "saturated (strict_rule rule) ts \<Longrightarrow> saturated (weak_rule rule) ts"
  unfolding saturated_def strict_rule.simps weak_rule.simps by force

lemma saturated_weak_to_non_equal:
  "saturated (weak_rule rule) ts \<Longrightarrow> saturated (strict_rule rule) ts"
  unfolding saturated_def strict_rule.simps weak_rule.simps 
  by (meson dual_order.order_iff_strict rule_less_eq)

lemma saturated_weak_rule_star_less_eq:
  assumes "(weak_rule rule)\<^sup>*\<^sup>* ts\<^sub>1 ts\<^sub>2"
  assumes "(weak_rule rule)\<^sup>*\<^sup>* ts\<^sub>1 ts\<^sub>3"
  assumes "saturated (weak_rule rule) ts\<^sub>3"
  shows "ts\<^sub>3 \<le> ts\<^sub>2"
  using weak_rule_star_mono[OF assms(2,1)] assms(3)[unfolded saturated_def]
  unfolding idempotent_ab_semigroup_add_ord_class.less_eq_def
  using converse_rtranclpE[of "weak_rule rule" ts\<^sub>3 "ts\<^sub>3 + ts\<^sub>2"] by metis

context 
  fixes rule'
  assumes weak_star_intro: "(strict_rule rule')\<^sup>*\<^sup>* ts ts' \<Longrightarrow> (weak_rule rule)\<^sup>*\<^sup>* ts ts'"
  assumes preserves_saturated: "saturated (strict_rule rule') ts \<Longrightarrow> saturated (strict_rule rule) ts"
begin

lemma preserves_saturation:
  assumes "saturation (strict_rule rule') ts ts'"
  shows "saturation (strict_rule rule) ts ts'"
proof -
  have star':"(strict_rule rule')\<^sup>*\<^sup>* ts ts'" using assms unfolding saturation_def by argo
  have sat:"saturated (weak_rule rule) ts'" 
    using assms unfolding saturation_def using preserves_saturated[THEN saturated_non_equal_to_weak] by simp
  have weak:"(weak_rule rule)\<^sup>*\<^sup>* ts ts'" using weak_star_intro[OF star'] by fast
  obtain ts\<^sub>3 where rule:"(strict_rule rule)\<^sup>*\<^sup>* ts ts\<^sub>3" and leq:"ts\<^sub>3 \<le> ts'" 
    using weak_rule_star_to_strict_rule_star[OF weak] by blast
  have "ts' \<le> ts\<^sub>3" using saturated_weak_rule_star_less_eq[OF weak_rule_star_intro[OF rule] weak sat] by simp
  then have "ts' = ts\<^sub>3" using leq by auto                                                     
  then have "(strict_rule rule)\<^sup>*\<^sup>* ts ts'" using rule by fast
  then show ?thesis using assms preserves_saturated unfolding saturation_def by simp
qed

end

lemma saturation_non_equal_is_weak:
  "saturation (strict_rule rule) ts ts' \<longleftrightarrow> saturation (weak_rule rule) ts ts'"
proof
  show "saturation (strict_rule rule) ts ts' \<Longrightarrow> saturation (weak_rule rule) ts ts'"
    unfolding saturation_def using saturated_non_equal_to_weak weak_rule_star_intro by auto
  assume assm: "saturation (weak_rule rule) ts ts'"
  have star:"(weak_rule rule)\<^sup>*\<^sup>* ts ts'" using assm unfolding saturation_def by argo
  have satW:"saturated (weak_rule rule) ts'" using assm unfolding saturation_def by blast
  then have sat:"saturated (strict_rule rule) ts'" using saturated_weak_to_non_equal by blast
  obtain ts'' where ts'': "(strict_rule rule)\<^sup>*\<^sup>* ts ts''" "ts'' \<le> ts'"
    using weak_rule_star_to_strict_rule_star[OF star] by blast
  then show "saturation (strict_rule rule) ts ts'" unfolding saturation_def using sat
    using saturated_weak_rule_star_less_eq[OF weak_rule_star_intro[OF ts''(1)] star satW] by simp
qed

end


section \<open>Locale: add_saturation\<close>

locale add_saturation = rule_saturation rule
  for rule :: "'t::idempotent_comm_monoid_add_ord saturation_rule" +
  assumes finite_rule_set: "finite {ts'. strict_rule rule ts ts'}"
begin

lemma strict_rule_subset_not_fixp:
  assumes "X \<subseteq> {ts'. strict_rule rule ts ts'}"
  assumes "X \<noteq> {}"
  shows "ts + \<Sum>X \<noteq> ts"
proof -
  have finite_X: "finite X" by (fact finite_subset[OF assms(1) finite_rule_set])
  obtain ts' where ts'_X:"ts'\<in>X" and ts'_rule:"strict_rule rule ts ts'" using assms by blast
  have le:"\<Sum>X \<le> ts" 
    using assms sum_smaller_elem[of X ts] finite_X strict_rule_less_eq by blast
  have le':"\<Sum>X \<le> ts'"
    unfolding BoundedDioid.idempotent_ab_semigroup_add_ord_class.less_eq_def 
    using idem_sum_elem[OF finite_X, of ts'] ts'_X by (simp add: add.commute)
  obtain a where "ts' = ts + a" and "ts' \<noteq> ts"
    using ts'_rule[unfolded strict_rule.simps[of rule]] strict_rule_less_eq[OF ts'_rule] 
          order_prop[of ts' ts] add.commute 
    by metis
  then have "ts + ts' \<noteq> ts" by simp
  then show ?thesis 
    using le le' unfolding less_eq_def using add.commute 
    by metis
qed

lemma sum_fixp_implies_rule_fixp:
  assumes "ts + \<Sum>{ts'. strict_rule rule ts ts'} = ts"
  assumes "rule ts ts'"
  shows "ts = ts'" 
proof -
  have "{ts'. strict_rule rule ts ts'} = {}" 
    using assms(1,2) using strict_rule_subset_not_fixp by blast
  then show ?thesis using assms(2)
    unfolding strict_rule.simps by simp
qed

lemma weak_star_subset_sum:
  assumes "X \<subseteq> {ts'. strict_rule rule ts ts'}"
  shows "(weak_rule rule)\<^sup>*\<^sup>* ts (ts + \<Sum>X)"
proof -
  have "finite X" by (fact finite_subset[OF assms finite_rule_set])
  then show ?thesis using assms
  proof (induct rule: finite_induct)
    case empty
    then show ?case by simp
  next
    case (insert x F)
    then have A:"(weak_rule rule)\<^sup>*\<^sup>* ts (ts + \<Sum> F)" and B: "(strict_rule rule) ts x" by auto
    have "(weak_rule rule)\<^sup>*\<^sup>* ts (ts + \<Sum> F + x)"
      using weak_rule_step_mono'[OF A weak_rule_intro[OF B]] by blast
    then show ?case       
      by (simp add: insert.hyps(1) meet.inf_commute meet.inf_left_commute)
  qed
qed

end


section \<open>Locale: step_saturation\<close>

locale step_saturation = 
  fixes step::"('a::finite \<Rightarrow>f 'b::bounded_dioid) \<Rightarrow> ('a \<Rightarrow>f 'b)"
begin

definition "step_loop = while_option (\<lambda>s. step s \<noteq> s) (step)"

definition "step_exec = the o step_loop"

definition "step_rule ts ts' \<equiv> step ts = ts'"

end


section \<open>Locale: decreasing_step_saturation\<close>

locale decreasing_step_saturation = step_saturation step
  for step::"('a::finite \<Rightarrow>f 'b::bounded_dioid) \<Rightarrow> ('a \<Rightarrow>f 'b)" +
  assumes step_decreasing: "step S \<le> S"
begin

lemma step_exec_terminates: 
  shows "\<exists>t. step_loop S = Some t"
  unfolding step_loop_def 
  using wf_rel_while_option_Some[OF wf_less_finfun, of "\<lambda>S. step S \<le> S" "(\<lambda>S. step S \<noteq> S)" step S]
        step_decreasing
  by fastforce

lemma step_rule_star_step: "(strict_rule step_rule)\<^sup>*\<^sup>* S (step S)"
  unfolding step_rule_def strict_rule.simps by (cases "S = step S") auto

lemma weak_rule_star_step_k: "(strict_rule step_rule)\<^sup>*\<^sup>* S ((step ^^ k) S)"
  by (induct k) (auto elim!: rtranclp_trans intro: step_rule_star_step)

lemma saturation_step_exec': "saturation (strict_rule step_rule) S (step_exec S)"
proof -
  from step_exec_terminates obtain t where t: "step_loop S = Some t" by blast
  obtain k where k: "t = (step ^^ k) S" and eq: "step t = t"
    using while_option_stop2[OF t[unfolded step_loop_def]] by auto
  have "\<And>ts. \<not> (strict_rule step_rule) t ts" 
    using eq unfolding strict_rule.simps step_rule_def by presburger
  then show ?thesis
    unfolding saturation_def saturated_def step_exec_def o_apply t
    by (simp_all add: weak_rule_star_step_k k)
qed

lemma step_exec_less_eq: "step_exec S \<le> S"
  unfolding step_exec_def using step_exec_terminates[of S]
  apply safe
  apply simp
  unfolding step_loop_def
  subgoal for t
    apply (rule while_option_rule[of _ "(\<lambda>s. step s \<noteq> s)" step S t])
    using step_decreasing dual_order.trans
    by auto
  done

lemma step_exec_fixp_to_step_fixp: "step_exec S = S \<Longrightarrow> step S = S"
  using step_exec_terminates while_option_stop[of "\<lambda>s. step s \<noteq> s" step S]
  unfolding step_exec_def step_loop_def by force

lemma step_exec_fixp_to_step_fixp': "S \<le> step_exec S \<Longrightarrow> S = step S"
  using step_exec_less_eq[of S] step_exec_fixp_to_step_fixp by simp

end

section \<open>Locale: subset_step_saturation\<close>

locale subset_step_saturation = add_saturation rule
  for step::"('a::finite \<Rightarrow>f 'b::bounded_dioid) \<Rightarrow> ('a::finite \<Rightarrow>f 'b::bounded_dioid)"
  and rule :: "('a::finite \<Rightarrow>f 'b::bounded_dioid) saturation_rule" +
  assumes step_done: "\<not> Ex (strict_rule rule ts) \<Longrightarrow> step ts = ts"
  assumes step_is_subset: "Ex (strict_rule rule ts) \<Longrightarrow> \<exists>X \<subseteq> {ts'. strict_rule rule ts ts'}. step ts = ts + \<Sum>X \<and> X \<noteq> {}"
begin
sublocale decreasing_step_saturation step
proof 
  fix ts
  show "step ts \<le> ts"
  proof (cases "Ex (strict_rule rule ts)")
    case True
    then show ?thesis using step_is_subset by fastforce
  next
    case False
    then show ?thesis using step_done by simp
  qed
qed

lemma weak_star_step: "(weak_rule rule)\<^sup>*\<^sup>* ts (step ts)"
proof (cases "Ex (strict_rule rule ts)")
  case True
  then obtain X where "step ts = ts + \<Sum> X" "X\<subseteq>{ts'. strict_rule rule ts ts'}"
    using step_is_subset by blast
  then show ?thesis
    using weak_star_subset_sum by presburger
next
  case False
  then show ?thesis using step_done by simp
qed

lemma weak_star_intro: "(strict_rule step_rule)\<^sup>*\<^sup>* ts ts' \<Longrightarrow> (weak_rule rule)\<^sup>*\<^sup>* ts ts'"
  apply (induct rule: rtranclp_induct, simp)
  unfolding step_rule_def strict_rule.simps using weak_star_step rtranclp_trans 
  by metis

lemma exists_strict_step_not_fixp: "Ex (strict_rule rule ts) \<Longrightarrow> step ts \<noteq> ts"
proof -
  assume "Ex (strict_rule rule ts)"
  then obtain X where "step ts = ts + \<Sum> X" "X\<subseteq>{ts'. strict_rule rule ts ts'}" "X \<noteq> {}"
    using step_is_subset by blast
  then show ?thesis 
    using strict_rule_subset_not_fixp by presburger
qed

lemma preserves_saturated: "saturated (strict_rule step_rule) ts \<Longrightarrow> saturated (strict_rule rule) ts"
  unfolding saturated_def step_rule_def strict_rule.simps using exists_strict_step_not_fixp[of ts]
  by (cases "Ex (strict_rule rule ts)") (auto simp add: strict_rule.simps)

lemma saturation_step_exec: "saturation (strict_rule rule) S (step_exec S)"
  using preserves_saturation[OF weak_star_intro preserves_saturated] saturation_step_exec'
  by blast
end


section \<open>Locale: single_step_saturation\<close>

lemma some_subset: "Ex P \<Longrightarrow> {Eps P} \<subseteq> {x. P x}"
  using some_eq_imp by force

locale single_step_saturation = add_saturation rule
  for step::"('a::finite \<Rightarrow>f 'b::bounded_dioid) \<Rightarrow> ('a::finite \<Rightarrow>f 'b::bounded_dioid)"
  and rule :: "('a::finite \<Rightarrow>f 'b::bounded_dioid) saturation_rule" +
  assumes step_is_single_step: "step ts = ts + (if Ex (strict_rule rule ts) then Eps (strict_rule rule ts) else 0)"
begin
sublocale subset_step_saturation step rule 
proof
  fix ts
  show "\<not> Ex (strict_rule rule ts) \<Longrightarrow> step ts = ts" 
    using step_is_single_step by auto
  show "Ex (strict_rule rule ts) \<Longrightarrow> \<exists>X\<subseteq>{ts'. strict_rule rule ts ts'}. step ts = ts + \<Sum> X \<and> X \<noteq> {}"
    unfolding step_is_single_step using some_subset[of "strict_rule rule ts"] by auto
qed
lemmas saturation_step_exec = saturation_step_exec
end

section \<open>Locale: sum_saturation\<close>

locale sum_saturation = add_saturation rule
  for step::"('a::finite \<Rightarrow>f 'b::bounded_dioid) \<Rightarrow> ('a \<Rightarrow>f 'b)"
  and rule :: "('a \<Rightarrow>f 'b) saturation_rule" +
  assumes step_is_sum: "step ts = ts + \<Sum>{ts'. strict_rule rule ts ts'}"
begin
sublocale subset_step_saturation step rule by standard (auto simp add: step_is_sum)
lemmas weak_star_step = weak_star_step
lemmas saturation_step_exec = saturation_step_exec
end

lemma sum_saturation_step_exec:
  assumes "\<And>ts ts'. rule ts ts' \<Longrightarrow> ts' \<le> ts"
  assumes "\<And>ts\<^sub>3 ts\<^sub>1 ts\<^sub>2. ts\<^sub>3 \<le> ts\<^sub>1 \<Longrightarrow> rule ts\<^sub>1 ts\<^sub>2 \<Longrightarrow> \<exists>ts'. rule ts\<^sub>3 ts' \<and> ts' \<le> ts\<^sub>2"
  assumes "\<And>ts. step ts = ts + \<Sum>{ts'. strict_rule rule ts ts'}"
  assumes "\<And>ts. finite {ts'. strict_rule rule ts ts'}"
  shows "saturation (strict_rule rule) ts (step_saturation.step_exec step ts)"
  using sum_saturation.saturation_step_exec[of step rule ts]
  unfolding sum_saturation_def add_saturation_def rule_saturation_def
            sum_saturation_axioms_def add_saturation_axioms_def
  using assms by auto


section \<open>Locale: par_saturation\<close>

locale par_saturation = add_saturation rule
  for step::"('a::finite \<Rightarrow>f 'b::bounded_dioid) \<Rightarrow> ('a::finite \<Rightarrow>f 'b::bounded_dioid)"
  and rule :: "('a::finite \<Rightarrow>f 'b::bounded_dioid) saturation_rule"
  and step_partition::"(('a::finite \<Rightarrow>f 'b::bounded_dioid) \<Rightarrow> ('a::finite \<Rightarrow>f 'b::bounded_dioid)) set" +
  assumes step_is_partition_saturation: "step ts = ts + (\<Sum>step\<^sub>i\<in>step_partition. step_saturation.step_exec step\<^sub>i ts)"
  assumes partitions_are_rules: "\<forall>step\<^sub>i\<in>step_partition. (weak_rule rule)\<^sup>*\<^sup>* ts (step\<^sub>i ts)" (* more general than: rule ts (step\<^sub>i ts) *)
  assumes partitions_cover_rules: "ts = ts + (\<Sum>step\<^sub>i\<in>step_partition. step\<^sub>i ts) \<Longrightarrow> ts = ts + \<Sum>{ts'. strict_rule rule ts ts'}"
  assumes finite_step_partition: "finite step_partition"
begin
sublocale decreasing_step_saturation step by standard (simp add: step_is_partition_saturation)

lemma step\<^sub>i_is_decreasing: "step\<^sub>i\<in>step_partition \<Longrightarrow> decreasing_step_saturation step\<^sub>i"
  apply standard
  using partitions_are_rules weak_rule_star_less_eq 
  by blast

lemma step_partition_to_rule: 
  assumes "step\<^sub>i\<in>step_partition"
  assumes "strict_rule (step_saturation.step_rule step\<^sub>i) ts ts'"
  shows "(weak_rule rule)\<^sup>*\<^sup>* ts ts'"
proof -
  have "(weak_rule rule)\<^sup>*\<^sup>* ts (step\<^sub>i ts)" using assms(1) partitions_are_rules by blast
  then show ?thesis using assms(2)[unfolded strict_rule.simps] unfolding step_saturation.step_rule_def
    using weak_rule_star_to_strict_rule_star by simp
qed
lemma step_partition_to_rule_star: "(strict_rule (step_saturation.step_rule step\<^sub>i))\<^sup>*\<^sup>* ts ts' \<Longrightarrow> step\<^sub>i\<in>step_partition \<Longrightarrow> (weak_rule rule)\<^sup>*\<^sup>* ts ts'"
  apply (induct rule: rtranclp_induct, simp)
  using step_partition_to_rule[of step\<^sub>i]
  by fastforce

lemma weak_star_step: "(weak_rule rule)\<^sup>*\<^sup>* ts (step ts)"
  unfolding step_is_partition_saturation
proof (induct rule: finite_subset_induct'[OF finite_step_partition, of step_partition, simplified])
  case 1
  then show ?case by simp
next
  case (2 step step_partition)
  have "(weak_rule rule)\<^sup>*\<^sup>* ts (step_saturation.step_exec step ts)" 
    using decreasing_step_saturation.saturation_step_exec'[OF step\<^sub>i_is_decreasing]
    unfolding saturation_def using step_partition_to_rule_star 2(2)
    by blast
  then have B:"(weak_rule rule)\<^sup>*\<^sup>* ts (ts + (step_saturation.step_exec step ts))"
    by (simp add: weak_rule_add_star_mono)
  have C:"(weak_rule rule)\<^sup>*\<^sup>* ts (ts + (\<Sum>step\<^sub>i\<in>step_partition. step_saturation.step_exec step\<^sub>i ts))"
    using 2(5) by fastforce
  show ?case using weak_rule_star_mono[OF B C] 2(1,4) B by (simp add: add.assoc add.left_commute)
qed

lemma weak_star_intro: "(strict_rule step_rule)\<^sup>*\<^sup>* ts ts' \<Longrightarrow> (weak_rule rule)\<^sup>*\<^sup>* ts ts'"
  apply (induct rule: rtranclp_induct, simp)
  unfolding step_rule_def strict_rule.simps using weak_star_step rtranclp_trans 
  by metis

lemma exec_fixp_to_step_fixp: "ts \<le> (\<Sum>step\<^sub>i\<in>step_partition. step_saturation.step_exec step\<^sub>i ts) \<Longrightarrow> ts \<le> (\<Sum>step\<^sub>i\<in>step_partition. step\<^sub>i ts)"
  using decreasing_step_saturation.step_exec_fixp_to_step_fixp'[OF step\<^sub>i_is_decreasing, of _ ts]
proof (induct rule: finite_induct[OF finite_step_partition])
  case 1
  then show ?case by simp
next
  case (2 step step_partition)
  then have "ts \<le> (\<Sum>step\<^sub>i\<in>step_partition. step\<^sub>i ts)" by (simp add: order_class.order_eq_iff)
  have "ts \<le> step ts" using 2(1,2,4) 2(5)[of step] by simp
  then show ?case using 2 by simp
qed

lemma preserves_saturated: "saturated (strict_rule step_rule) ts \<Longrightarrow> saturated (strict_rule rule) ts"
  unfolding saturated_def step_rule_def strict_rule.simps 
  unfolding step_is_partition_saturation
  using partitions_cover_rules exec_fixp_to_step_fixp[unfolded less_eq_def] sum_fixp_implies_rule_fixp
  by metis

lemma saturation_step_exec: "saturation (strict_rule rule) S (step_exec S)"
  using rule_saturation.preserves_saturation[unfolded rule_saturation_def, of rule step_rule]
        rule_less_eq rule_mono weak_star_intro preserves_saturated saturation_step_exec'
  by auto
end


end
