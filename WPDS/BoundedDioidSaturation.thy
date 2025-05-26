theory BoundedDioidSaturation
  imports "Saturation"
begin

inductive strict_rule :: "'t saturation_rule \<Rightarrow> 't saturation_rule" for rule where
  rule_to_strict_rule: "rule s s' \<Longrightarrow> s \<noteq> s' \<Longrightarrow> strict_rule rule s s'"

inductive weak_rule :: "'t::idempotent_ab_semigroup_add_ord saturation_rule \<Rightarrow> 't saturation_rule" for rule where
  rule_to_weak_rule: "rule s s'' \<Longrightarrow> s'' \<le> s' \<Longrightarrow> s' < s \<Longrightarrow> weak_rule rule s s'"

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
  assumes rule_less_eq: "rule s s' \<Longrightarrow> s' \<le> s"
  assumes rule_mono: "s\<^sub>3 \<le> s\<^sub>1 \<Longrightarrow> rule s\<^sub>1 s\<^sub>2 \<Longrightarrow> \<exists>s'. rule s\<^sub>3 s' \<and> s' \<le> s\<^sub>2"
begin

lemma rule_star_less_eq: "rule\<^sup>*\<^sup>* s s' \<Longrightarrow> s' \<le> s"
  apply (induct rule: rtranclp_induct, simp)
  using rule_less_eq by fastforce

lemma rule_exists_addition: "rule s s' \<Longrightarrow> \<exists>a. s' = s + a"
  using order_prop rule_less_eq add.commute by metis

lemma weak_rule_exists_addition: "weak_rule rule a b \<Longrightarrow> \<exists>c. b = a + c"
  unfolding weak_rule.simps by (metis meet.inf.absorb4) 

lemma rule_add_extend: 
  assumes "rule s\<^sub>1 s\<^sub>2"
  shows "\<exists>s'. rule (s + s\<^sub>1) (s + s') \<and> s' \<le> s\<^sub>2"
proof -
  obtain s' where s': "rule (s + s\<^sub>1) s'" "s' \<le> s\<^sub>2"
    using rule_mono[of "s + s\<^sub>1" s\<^sub>1 s\<^sub>2] assms by auto
  then have "rule (s + s\<^sub>1) (s + s')" 
    using rule_less_eq[OF s'(1)] meet.inf.absorb2 by fastforce
  then show ?thesis using s'(2) by blast
qed

lemma strict_rule_less: "strict_rule rule a b \<Longrightarrow> b < a"
  using rule_less_eq by (metis strict_rule.simps order_le_imp_less_or_eq)

lemma strict_rule_less_eq: "strict_rule rule a b \<Longrightarrow> b \<le> a"
  using strict_rule_less by fastforce

lemma strict_rule_star_less_eq: "(strict_rule rule)\<^sup>*\<^sup>* s s' \<Longrightarrow> s' \<le> s"
  apply (induct rule: rtranclp_induct, simp)
  using strict_rule_less_eq by fastforce

lemma eq_some_strict_not_exists:
  "s = s + Eps (strict_rule rule s) \<Longrightarrow> \<not> Ex (strict_rule rule s)"
  using strict_rule_less[OF someI[of "strict_rule rule s"]]
        less_eq_def[of s "Eps (strict_rule rule s)"]
  by force

lemma weak_rule_less: "weak_rule rule s s' \<Longrightarrow> s' < s"
  using weak_rule.simps by blast

lemma weak_rule_less_eq: "weak_rule rule s s' \<Longrightarrow> s' \<le> s"
  using weak_rule_less  by fastforce

lemma weak_rule_star_less_eq: "(weak_rule rule)\<^sup>*\<^sup>* s s' \<Longrightarrow> s' \<le> s"
  apply (induct rule: rtranclp_induct, simp)
  using weak_rule_less_eq by fastforce

lemma weak_rule_intro: "strict_rule rule s s' \<Longrightarrow> weak_rule rule s s'"
  using rule_to_weak_rule[of rule s s'] strict_rule.cases[of rule s s'] order_refl
  by (metis strict_rule_less)
lemma strict_le_weak: "strict_rule rule \<le> weak_rule rule"
  using weak_rule_intro by blast
lemma strict_star_le_weak_star: "(strict_rule rule)\<^sup>*\<^sup>* \<le> (weak_rule rule)\<^sup>*\<^sup>*"
  by (fact rtranclp_mono[OF strict_le_weak])
lemma weak_rule_star_intro: "(strict_rule rule)\<^sup>*\<^sup>* s s' \<Longrightarrow> (weak_rule rule)\<^sup>*\<^sup>* s s'"
  using strict_star_le_weak_star by blast
lemma rule_to_weak_rule_star: "rule \<le> (weak_rule rule)\<^sup>*\<^sup>*"
  using r_into_rtranclp[of rule] rule_star_eq_strict_rule_star[of rule] strict_star_le_weak_star
  by auto
lemma rule_star_to_weak_rule_star: "rule\<^sup>*\<^sup>* \<le> (weak_rule rule)\<^sup>*\<^sup>*"
  using rule_star_eq_strict_rule_star strict_star_le_weak_star by metis

lemma weak_rule_star_to_strict_rule_star:
  assumes "(weak_rule rule)\<^sup>*\<^sup>* s s'"
  shows "\<exists>s''. (strict_rule rule)\<^sup>*\<^sup>* s s'' \<and> s'' \<le> s'"
  using assms
proof (induction rule: rtranclp_induct)
  case base
  then show ?case by blast
next
  case (step s\<^sub>1 s\<^sub>2)
  obtain s'' where s'': "rule s\<^sub>1 s''" "s'' \<le> s\<^sub>2"
    using step(2) weak_rule.simps by blast
  obtain s\<^sub>3 where s3: "(strict_rule rule)\<^sup>*\<^sup>* s s\<^sub>3" "s\<^sub>3 \<le> s\<^sub>1"
    using step(3) by blast
  obtain s\<^sub>4 where s4: "rule s\<^sub>3 s\<^sub>4" "s\<^sub>4 \<le> s''"
    using rule_mono[of s\<^sub>3 s\<^sub>1 s''] s3(2) s''(1) by fast
  have "s\<^sub>4 \<le> s\<^sub>2" using s4(2) s''(2) by fastforce
  show ?case
  proof (cases "s\<^sub>3 = s\<^sub>4")
    case True
    then show ?thesis using \<open>s\<^sub>4 \<le> s\<^sub>2\<close> s3(1) by blast
  next
    case False
    then have "strict_rule rule s\<^sub>3 s\<^sub>4"
      using s4(1) strict_rule.intros by metis
    then show ?thesis using \<open>s\<^sub>4 \<le> s\<^sub>2\<close> rtranclp.rtrancl_into_rtrancl[OF s3(1)]
      by blast
  qed
qed

lemma weak_rule_step_mono:
  assumes "s\<^sub>2 \<le> s\<^sub>1"
  assumes "weak_rule rule s\<^sub>1 s\<^sub>3"
  shows "(weak_rule rule)\<^sup>*\<^sup>* s\<^sub>2 (s\<^sub>2 + s\<^sub>3)"
proof -
  obtain a\<^sub>3 where s3: "s\<^sub>3 = s\<^sub>1 + a\<^sub>3" 
    using weak_rule_exists_addition[OF assms(2)] by fast
  obtain s' where s': "rule s\<^sub>1 s'" "s' \<le> s\<^sub>3"
    using assms(2) weak_rule.simps by blast
  obtain s\<^sub>4 where s4: "rule s\<^sub>2 s\<^sub>4" "s\<^sub>4 \<le> s'"
    using rule_mono assms(1) s'(1) by blast
  have eq: "s\<^sub>2 + a\<^sub>3 = s\<^sub>2 + s\<^sub>3" unfolding s3
    using assms(1)[unfolded less_eq_def, symmetric] by (metis meet.inf_assoc)
  show ?thesis proof (cases "s\<^sub>2 = s\<^sub>2 + a\<^sub>3")
    case True
    then show ?thesis using eq unfolding s3 by simp
  next
    case False
    then have le:"s\<^sub>2 + a\<^sub>3 < s\<^sub>2" by (simp add: order_le_neq_trans)
    have "weak_rule rule s\<^sub>2 (s\<^sub>2 + a\<^sub>3)"
      using weak_rule.intros[of rule, OF s4(1) _ le]
            s4(2) s'(2)[unfolded s3] rule_less_eq[OF s4(1)] 
      by fastforce
    then show ?thesis using eq unfolding s3 by auto
  qed
qed

lemma weak_rule_step_mono':
  assumes "(weak_rule rule)\<^sup>*\<^sup>* s\<^sub>1 s\<^sub>2"
  assumes "weak_rule rule s\<^sub>1 s\<^sub>3"
  shows "(weak_rule rule)\<^sup>*\<^sup>* s\<^sub>1 (s\<^sub>2 + s\<^sub>3)"
  using rtranclp_trans[of "weak_rule rule" s\<^sub>1 s\<^sub>2 "s\<^sub>2 + s\<^sub>3", OF assms(1)]
  using assms(2) weak_rule_star_less_eq[OF assms(1)] weak_rule_step_mono by simp

lemma weak_rule_add_extend:
  assumes "weak_rule rule s\<^sub>1 s\<^sub>2"
  assumes "s + s\<^sub>1 \<noteq> s + s\<^sub>2"
  shows "weak_rule rule (s + s\<^sub>1) (s + s\<^sub>2)"
proof -
  obtain s' where s': "rule s\<^sub>1 s'" "s' \<le> s\<^sub>2" (*"s\<^sub>1 \<noteq> s\<^sub>2"*)
    by (metis assms(1) weak_rule.simps)
  obtain s'' where s'': "rule (s + s\<^sub>1) (s + s'')" "s'' \<le> s'"
    using s'(1) rule_add_extend by blast
  have "s + s\<^sub>2 < s + s\<^sub>1" using assms(2) weak_rule_less[OF assms(1)]
    by (simp add: meet.inf.strict_order_iff meet.inf_commute meet.inf_left_commute)
  then show ?thesis                                                                                                  
    using rule_to_weak_rule[of rule "s + s\<^sub>1" "s + s''" "s + s\<^sub>2", OF s''(1)]
    using order.trans[OF s''(2) s'(2)] meet.inf_mono by blast
qed

lemma weak_rule_add_mono:
  assumes "(weak_rule rule)\<^sup>*\<^sup>* s (s + s\<^sub>1)"
  assumes "(weak_rule rule) s\<^sub>1 s\<^sub>2"
  shows "(weak_rule rule)\<^sup>*\<^sup>* s (s + s\<^sub>2)"
proof (cases "s + s\<^sub>1 = s + s\<^sub>2")
  case True
  then show ?thesis using assms(1) by simp
next
  case False
  then have "(weak_rule rule) (s + s\<^sub>1) (s + s\<^sub>2)" 
    using assms(2) weak_rule_add_extend by blast
  then show ?thesis using assms(1) by simp
qed

lemma weak_rule_add_star_mono:
  assumes "(weak_rule rule)\<^sup>*\<^sup>* s\<^sub>1 s\<^sub>2"
  assumes "(weak_rule rule)\<^sup>*\<^sup>* s (s + s\<^sub>1)"
  shows "(weak_rule rule)\<^sup>*\<^sup>* s (s + s\<^sub>2)"
  using assms(1,2)
  by (induct rule: rtranclp_induct, simp_all add: weak_rule_add_mono)

lemma weak_rule_star_mono:
  assumes "(weak_rule rule)\<^sup>*\<^sup>* s\<^sub>1 s\<^sub>2"
  assumes "(weak_rule rule)\<^sup>*\<^sup>* s\<^sub>1 s\<^sub>3"
  shows "(weak_rule rule)\<^sup>*\<^sup>* s\<^sub>2 (s\<^sub>2 + s\<^sub>3)"
    using assms(2,1)
proof (induction rule: converse_rtranclp_induct)
  case base
  then show ?case by (metis meet.inf.orderE weak_rule_star_less_eq rtranclp.simps)
next
  case (step s\<^sub>1' s\<^sub>3')
  show ?case using weak_rule_add_star_mono[OF step(2) weak_rule_step_mono[OF weak_rule_star_less_eq[OF step(4)] step(1)]] 
    by blast
qed

lemma saturated_non_equal_to_weak:
  "saturated (strict_rule rule) s \<Longrightarrow> saturated (weak_rule rule) s"
  unfolding saturated_def strict_rule.simps weak_rule.simps by force

lemma saturated_weak_to_non_equal:
  "saturated (weak_rule rule) s \<Longrightarrow> saturated (strict_rule rule) s"
  unfolding saturated_def strict_rule.simps weak_rule.simps 
  by (meson dual_order.order_iff_strict rule_less_eq)

lemma saturated_weak_rule_star_less_eq:
  assumes "(weak_rule rule)\<^sup>*\<^sup>* s\<^sub>1 s\<^sub>2"
  assumes "(weak_rule rule)\<^sup>*\<^sup>* s\<^sub>1 s\<^sub>3"
  assumes "saturated (weak_rule rule) s\<^sub>3"
  shows "s\<^sub>3 \<le> s\<^sub>2"
  using weak_rule_star_mono[OF assms(2,1)] assms(3)[unfolded saturated_def]
  unfolding idempotent_ab_semigroup_add_ord_class.less_eq_def
  using converse_rtranclpE[of "weak_rule rule" s\<^sub>3 "s\<^sub>3 + s\<^sub>2"] by metis

context 
  fixes rule'
  assumes weak_star_intro: "(strict_rule rule')\<^sup>*\<^sup>* s s' \<Longrightarrow> (weak_rule rule)\<^sup>*\<^sup>* s s'"
  assumes preserves_saturated: "saturated (strict_rule rule') s \<Longrightarrow> saturated (strict_rule rule) s"
begin

lemma preserves_saturation:
  assumes "saturation (strict_rule rule') s s'"
  shows "saturation (strict_rule rule) s s'"
proof -
  have star':"(strict_rule rule')\<^sup>*\<^sup>* s s'" using assms unfolding saturation_def by argo
  have sat:"saturated (weak_rule rule) s'" 
    using assms unfolding saturation_def using preserves_saturated[THEN saturated_non_equal_to_weak] by simp
  have weak:"(weak_rule rule)\<^sup>*\<^sup>* s s'" using weak_star_intro[OF star'] by fast
  obtain s\<^sub>3 where rule:"(strict_rule rule)\<^sup>*\<^sup>* s s\<^sub>3" and leq:"s\<^sub>3 \<le> s'" 
    using weak_rule_star_to_strict_rule_star[OF weak] by blast
  have "s' \<le> s\<^sub>3" using saturated_weak_rule_star_less_eq[OF weak_rule_star_intro[OF rule] weak sat] by simp
  then have "s' = s\<^sub>3" using leq by auto                                                     
  then have "(strict_rule rule)\<^sup>*\<^sup>* s s'" using rule by fast
  then show ?thesis using assms preserves_saturated unfolding saturation_def by simp
qed

end

lemma saturation_strict_is_weak:
  "saturation (strict_rule rule) s s' \<longleftrightarrow> saturation (weak_rule rule) s s'"
proof
  show "saturation (strict_rule rule) s s' \<Longrightarrow> saturation (weak_rule rule) s s'"
    unfolding saturation_def using saturated_non_equal_to_weak weak_rule_star_intro by auto
  assume assm: "saturation (weak_rule rule) s s'"
  have star:"(weak_rule rule)\<^sup>*\<^sup>* s s'" using assm unfolding saturation_def by argo
  have satW:"saturated (weak_rule rule) s'" using assm unfolding saturation_def by blast
  then have sat:"saturated (strict_rule rule) s'" using saturated_weak_to_non_equal by blast
  obtain s'' where s'': "(strict_rule rule)\<^sup>*\<^sup>* s s''" "s'' \<le> s'"
    using weak_rule_star_to_strict_rule_star[OF star] by blast
  then show "saturation (strict_rule rule) s s'" unfolding saturation_def using sat
    using saturated_weak_rule_star_less_eq[OF weak_rule_star_intro[OF s''(1)] star satW] by simp
qed

end


section \<open>Locale: add_saturation\<close>

locale add_saturation = rule_saturation rule
  for rule :: "'t::idempotent_comm_monoid_add_ord saturation_rule" +
  assumes finite_rule_set: "finite {s'. strict_rule rule s s'}"
begin

lemma strict_rule_subset_not_fixp:
  assumes "X \<subseteq> {s'. strict_rule rule s s'}"
  assumes "X \<noteq> {}"
  shows "s + \<Sum>X \<noteq> s"
proof -
  have finite_X: "finite X" by (fact finite_subset[OF assms(1) finite_rule_set])
  obtain s' where s'_X:"s'\<in>X" and s'_rule:"strict_rule rule s s'" using assms by blast
  have le:"\<Sum>X \<le> s" 
    using assms sum_smaller_elem[of X s] finite_X strict_rule_less_eq by blast
  have le':"\<Sum>X \<le> s'"
    unfolding BoundedDioid.idempotent_ab_semigroup_add_ord_class.less_eq_def 
    using idem_sum_elem[OF finite_X, of s'] s'_X by (simp add: add.commute)
  obtain a where "s' = s + a" and "s' \<noteq> s"
    using s'_rule[unfolded strict_rule.simps[of rule]] strict_rule_less_eq[OF s'_rule] 
          order_prop[of s' s] add.commute 
    by metis
  then have "s + s' \<noteq> s" by simp
  then show ?thesis 
    using le le' unfolding less_eq_def using add.commute 
    by metis
qed

lemma sum_fixp_implies_rule_fixp:
  assumes "s + \<Sum>{s'. strict_rule rule s s'} = s"
  assumes "rule s s'"
  shows "s = s'" 
proof -
  have "{s'. strict_rule rule s s'} = {}" 
    using assms(1,2) using strict_rule_subset_not_fixp by blast
  then show ?thesis using assms(2)
    unfolding strict_rule.simps by simp
qed

lemma weak_star_subset_sum:
  assumes "X \<subseteq> {s'. strict_rule rule s s'}"
  shows "(weak_rule rule)\<^sup>*\<^sup>* s (s + \<Sum>X)"
proof -
  have "finite X" by (fact finite_subset[OF assms finite_rule_set])
  then show ?thesis using assms
  proof (induct rule: finite_induct)
    case empty
    then show ?case by simp
  next
    case (insert x F)
    then have A:"(weak_rule rule)\<^sup>*\<^sup>* s (s + \<Sum> F)" and B: "(strict_rule rule) s x" by auto
    have "(weak_rule rule)\<^sup>*\<^sup>* s (s + \<Sum> F + x)"
      using weak_rule_step_mono'[OF A weak_rule_intro[OF B]] by blast
    then show ?case       
      by (simp add: insert.hyps(1) meet.inf_commute meet.inf_left_commute)
  qed
qed
end

lemmas add_saturation_unfold = add_saturation.finite_rule_set rule_saturation.rule_less_eq[OF add_saturation.axioms(1)] rule_saturation.rule_mono[OF add_saturation.axioms(1)]


section \<open>Locale: step_saturation\<close>

locale step_saturation = 
  fixes step::"'a::bounded_dioid \<Rightarrow> 'a"
begin

definition "step_loop = while_option (\<lambda>s. step s \<noteq> s) step"

definition "saturation_exec = the o step_loop"

definition "step_rule s s' \<equiv> step s = s' \<and> s \<noteq> s'"

lemma step_rule_is_strict: "step_rule = strict_rule step_rule" 
  unfolding step_rule_def strict_rule.simps by presburger
end


section \<open>Locale: decreasing_step_saturation\<close>

locale decreasing_step_saturation = step_saturation step
  for step::"'a::bounded_dioid \<Rightarrow> 'a" +
  assumes step_decreasing: "step s \<le> s"
begin

lemma saturation_exec_terminates: 
  shows "\<exists>t. step_loop s = Some t"
  unfolding step_loop_def 
  using wf_rel_while_option_Some[OF wf_less_wfp, of "\<lambda>s. step s \<le> s" "(\<lambda>s. step s \<noteq> s)" step s]
        step_decreasing
  by fastforce

lemma step_rule_star_step: "step_rule\<^sup>*\<^sup>* s (step s)"
  unfolding step_rule_def by (cases "s = step s") auto

lemma weak_rule_star_step_k: "step_rule\<^sup>*\<^sup>* s ((step ^^ k) s)"
  by (induct k) (auto elim!: rtranclp_trans intro: step_rule_star_step)

lemma saturation_exec_correct': "saturation step_rule s (saturation_exec s)"
proof -
  from saturation_exec_terminates obtain t where t: "step_loop s = Some t" by blast
  obtain k where k: "t = (step ^^ k) s" and eq: "step t = t"
    using while_option_stop2[OF t[unfolded step_loop_def]] by auto
  have "\<And>s. \<not> step_rule t s" 
    using eq unfolding strict_rule.simps step_rule_def by presburger
  then show ?thesis
    unfolding saturation_def saturated_def saturation_exec_def o_apply t
    by (simp_all add: weak_rule_star_step_k k)
qed

lemma saturation_exec_less_eq: "saturation_exec s \<le> s"
  unfolding saturation_exec_def using saturation_exec_terminates[of s]
  apply safe
  apply simp
  unfolding step_loop_def
  subgoal for t
    apply (rule while_option_rule[of _ "(\<lambda>s. step s \<noteq> s)" step s t])
    using step_decreasing dual_order.trans
    by auto
  done

lemma saturation_exec_fixp_to_step_fixp: "saturation_exec s = s \<Longrightarrow> step s = s"
  using saturation_exec_terminates while_option_stop[of "\<lambda>s. step s \<noteq> s" step s]
  unfolding saturation_exec_def step_loop_def by force

lemma saturation_exec_fixp_to_step_fixp': "s \<le> saturation_exec s \<Longrightarrow> s = step s"
  using saturation_exec_less_eq[of s] saturation_exec_fixp_to_step_fixp by simp

end

section \<open>Locale: subset_step_saturation\<close>

locale subset_step_saturation = add_saturation rule
  for step::"'a::bounded_dioid \<Rightarrow> 'a"
  and rule :: "'a saturation_rule" +
  assumes step_done: "\<not> Ex (strict_rule rule s) \<Longrightarrow> step s = s"
  assumes step_is_subset: "Ex (strict_rule rule s) \<Longrightarrow> \<exists>X \<subseteq> {s'. strict_rule rule s s'}. step s = s + \<Sum>X \<and> X \<noteq> {}"
begin
sublocale decreasing_step_saturation step
proof 
  fix s
  show "step s \<le> s"
  proof (cases "Ex (strict_rule rule s)")
    case True
    then show ?thesis using step_is_subset by fastforce
  next
    case False
    then show ?thesis using step_done by simp
  qed
qed

lemma weak_star_step: "(weak_rule rule)\<^sup>*\<^sup>* s (step s)"
proof (cases "Ex (strict_rule rule s)")
  case True
  then obtain X where "step s = s + \<Sum> X" "X\<subseteq>{s'. strict_rule rule s s'}"
    using step_is_subset by blast
  then show ?thesis
    using weak_star_subset_sum by presburger
next
  case False
  then show ?thesis using step_done by simp
qed

lemma weak_star_intro: "step_rule\<^sup>*\<^sup>* s s' \<Longrightarrow> (weak_rule rule)\<^sup>*\<^sup>* s s'"
  apply (induct rule: rtranclp_induct, simp)
  unfolding step_rule_def strict_rule.simps using weak_star_step rtranclp_trans 
  by metis

lemma exists_strict_step_not_fixp: "Ex (strict_rule rule s) \<Longrightarrow> step s \<noteq> s"
proof -
  assume "Ex (strict_rule rule s)"
  then obtain X where "step s = s + \<Sum> X" "X\<subseteq>{s'. strict_rule rule s s'}" "X \<noteq> {}"
    using step_is_subset by blast
  then show ?thesis 
    using strict_rule_subset_not_fixp by presburger
qed

lemma preserves_saturated: "saturated step_rule s \<Longrightarrow> saturated (strict_rule rule) s"
  unfolding saturated_def step_rule_def strict_rule.simps using exists_strict_step_not_fixp[of s]
  by (cases "Ex (strict_rule rule s)") (auto simp add: strict_rule.simps)

lemma saturation_exec_correct: "saturation (strict_rule rule) s (saturation_exec s)"
  using preserves_saturation[OF weak_star_intro preserves_saturated] 
        saturation_exec_correct'[unfolded] step_rule_is_strict
  by metis
end


section \<open>Locale: single_step_saturation\<close>

lemma some_subset: "Ex P \<Longrightarrow> {Eps P} \<subseteq> {x. P x}"
  using some_eq_imp by force

locale single_step_saturation = add_saturation rule
  for step::"'a::bounded_dioid \<Rightarrow> 'a"
  and rule :: "'a saturation_rule" +
  assumes step_is_single_step: "step s = s + (if Ex (strict_rule rule s) then Eps (strict_rule rule s) else 0)"
begin
sublocale subset_step_saturation step rule 
proof
  fix s
  show "\<not> Ex (strict_rule rule s) \<Longrightarrow> step s = s" 
    using step_is_single_step by auto
  show "Ex (strict_rule rule s) \<Longrightarrow> \<exists>X\<subseteq>{s'. strict_rule rule s s'}. step s = s + \<Sum> X \<and> X \<noteq> {}"
    unfolding step_is_single_step using some_subset[of "strict_rule rule s"] by auto
qed
lemmas saturation_exec_correct = saturation_exec_correct
end

section \<open>Locale: sum_saturation\<close>

locale sum_saturation = add_saturation rule
  for step::"'a::bounded_dioid \<Rightarrow> 'a"
  and rule :: "'a saturation_rule" +
  assumes step_is_sum: "step s = s + \<Sum>{s'. strict_rule rule s s'}"
begin
sublocale subset_step_saturation step rule by standard (auto simp add: step_is_sum)
lemmas weak_star_step = weak_star_step
lemmas saturation_exec_correct = saturation_exec_correct
end

lemma sum_saturation_exec_correct:
  assumes "\<And>s s'. rule s s' \<Longrightarrow> s' \<le> s"
  assumes "\<And>s\<^sub>3 s\<^sub>1 s\<^sub>2. s\<^sub>3 \<le> s\<^sub>1 \<Longrightarrow> rule s\<^sub>1 s\<^sub>2 \<Longrightarrow> \<exists>s'. rule s\<^sub>3 s' \<and> s' \<le> s\<^sub>2"
  assumes "\<And>s. step s = s + \<Sum>{s'. strict_rule rule s s'}"
  assumes "\<And>s. finite {s'. strict_rule rule s s'}"
  shows "saturation (strict_rule rule) s (step_saturation.saturation_exec step s)"
  using sum_saturation.saturation_exec_correct[of step rule s]
  unfolding sum_saturation_def add_saturation_def rule_saturation_def
            sum_saturation_axioms_def add_saturation_axioms_def
  using assms by auto


section \<open>Locale: par_saturation\<close>

locale par_saturation = add_saturation rule
  for step::"'a::bounded_dioid \<Rightarrow> 'a"
  and rule :: "'a saturation_rule"
  and step_partition::"('a \<Rightarrow> 'a) set" +
  assumes step_is_partition_saturation: "step s = s + (\<Sum>step\<^sub>i\<in>step_partition. step_saturation.saturation_exec step\<^sub>i s)"
  assumes partitions_are_rules: "\<forall>step\<^sub>i\<in>step_partition. (weak_rule rule)\<^sup>*\<^sup>* s (step\<^sub>i s)" (* more general than: rule s (step\<^sub>i s) *)
  assumes partitions_cover_rules: "s = s + (\<Sum>step\<^sub>i\<in>step_partition. step\<^sub>i s) \<Longrightarrow> s = s + \<Sum>{s'. strict_rule rule s s'}"
  assumes finite_step_partition: "finite step_partition"
begin
sublocale decreasing_step_saturation step by standard (simp add: step_is_partition_saturation)

lemma step\<^sub>i_is_decreasing: "step\<^sub>i\<in>step_partition \<Longrightarrow> decreasing_step_saturation step\<^sub>i"
  apply standard
  using partitions_are_rules weak_rule_star_less_eq 
  by blast

lemma step_partition_to_rule: 
  assumes "step\<^sub>i\<in>step_partition"
  assumes "(step_saturation.step_rule step\<^sub>i) s s'"
  shows "(weak_rule rule)\<^sup>*\<^sup>* s s'"
proof -
  have "(weak_rule rule)\<^sup>*\<^sup>* s (step\<^sub>i s)" using assms(1) partitions_are_rules by blast
  then show ?thesis using assms(2) step_rule_is_strict[unfolded strict_rule.simps] unfolding step_saturation.step_rule_def
    using weak_rule_star_to_strict_rule_star by simp
qed
lemma step_partition_to_rule_star: "(step_saturation.step_rule step\<^sub>i)\<^sup>*\<^sup>* s s' \<Longrightarrow> step\<^sub>i\<in>step_partition \<Longrightarrow> (weak_rule rule)\<^sup>*\<^sup>* s s'"
  apply (induct rule: rtranclp_induct, simp)
  using step_partition_to_rule[of step\<^sub>i]
  by fastforce

lemma weak_star_step: "(weak_rule rule)\<^sup>*\<^sup>* s (step s)"
  unfolding step_is_partition_saturation
proof (induct rule: finite_subset_induct'[OF finite_step_partition, of step_partition, simplified])
  case 1
  then show ?case by simp
next
  case (2 step step_partition)
  have "(weak_rule rule)\<^sup>*\<^sup>* s (step_saturation.saturation_exec step s)" 
    using decreasing_step_saturation.saturation_exec_correct'[OF step\<^sub>i_is_decreasing]
    unfolding saturation_def using step_partition_to_rule_star 2(2)
    by blast
  then have B:"(weak_rule rule)\<^sup>*\<^sup>* s (s + (step_saturation.saturation_exec step s))"
    by (simp add: weak_rule_add_star_mono)
  have C:"(weak_rule rule)\<^sup>*\<^sup>* s (s + (\<Sum>step\<^sub>i\<in>step_partition. step_saturation.saturation_exec step\<^sub>i s))"
    using 2(5) by fastforce
  show ?case using weak_rule_star_mono[OF B C] 2(1,4) B by (simp add: add.assoc add.left_commute)
qed

lemma weak_star_intro: "step_rule\<^sup>*\<^sup>* s s' \<Longrightarrow> (weak_rule rule)\<^sup>*\<^sup>* s s'"
  apply (induct rule: rtranclp_induct, simp)
  unfolding step_rule_def strict_rule.simps using weak_star_step rtranclp_trans 
  by metis

lemma exec_fixp_to_step_fixp: "s \<le> (\<Sum>step\<^sub>i\<in>step_partition. step_saturation.saturation_exec step\<^sub>i s) \<Longrightarrow> s \<le> (\<Sum>step\<^sub>i\<in>step_partition. step\<^sub>i s)"
  using decreasing_step_saturation.saturation_exec_fixp_to_step_fixp'[OF step\<^sub>i_is_decreasing, of _ s]
proof (induct rule: finite_induct[OF finite_step_partition])
  case 1
  then show ?case by simp
next
  case (2 step step_partition)
  then have "s \<le> (\<Sum>step\<^sub>i\<in>step_partition. step\<^sub>i s)" by (simp add: order_class.order_eq_iff)
  have "s \<le> step s" using 2(1,2,4) 2(5)[of step] by simp
  then show ?case using 2 by simp
qed

lemma preserves_saturated: "saturated step_rule s \<Longrightarrow> saturated (strict_rule rule) s"
  unfolding saturated_def step_rule_def strict_rule.simps 
  unfolding step_is_partition_saturation
  using partitions_cover_rules exec_fixp_to_step_fixp[unfolded less_eq_def] sum_fixp_implies_rule_fixp
  by metis

lemma saturation_saturation_exec: "saturation (strict_rule rule) s (saturation_exec s)"
  using rule_saturation.preserves_saturation[unfolded rule_saturation_def, of rule step_rule]
        rule_less_eq rule_mono weak_star_intro preserves_saturated saturation_exec_correct'
        step_rule_is_strict
  by auto
end


end
