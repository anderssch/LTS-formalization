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

lemma weight_reach_rule_elim2:
  assumes "weight_reach_rule S S'"
  shows "\<exists>p d q. S' = S(q $+= (S$p * d)) \<and> (p,d,q) \<in> transition_relation \<and> S $ q + (S$p * d) \<noteq> S $ q"
  using assms unfolding weight_reach_rule.simps[of S S'] by presburger

lemma weight_reach_rule_less: "weight_reach_rule S S' \<Longrightarrow> S' < S"
  unfolding weight_reach_rule.simps by (auto simp: add.commute finfun_add_update_less)

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
  sorry

lemma sound_wrt_preserves_sound_wrt: 
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
    have z: "\<^bold>\<Sum> {S $ c * l |c l. c \<Midarrow> l \<Rightarrow>\<^sup>* c'} \<le> S' $ c'"
      using add_state unfolding sound_wrt_def by auto
    then show "\<^bold>\<Sum> {S $ c * l |c l. c \<Midarrow> l \<Rightarrow>\<^sup>* c'} \<le> S'(q $+= S' $ p * d) $ c'"
    proof (cases "c' = q")
      case True
      have "countable {S $ c * l |c l. c \<Midarrow> l \<Rightarrow>\<^sup>* c'}"
        sorry
      have " p \<Midarrow> d \<Rightarrow>\<^sup>* c'"
        sorry
      then have "\<^bold>\<Sum> {l |c l. c \<Midarrow> l \<Rightarrow>\<^sup>* c'} \<le> d"
        using countable_SumInf_elem countable_l_c by blast
      
      then have "\<^bold>\<Sum> {S $ c * l |c l. c \<Midarrow> l \<Rightarrow>\<^sup>* c'} \<le> S' $ p * d"
        using add_state unfolding True[symmetric] 
        sorry
      then have "\<^bold>\<Sum> {S $ c * l |c l. c \<Midarrow> l \<Rightarrow>\<^sup>* c'} \<le> S'$ c' + S' $ p * d"
        unfolding True[symmetric]
        using add_state(1,2)
        using z 
        by auto
      from  this show ?thesis 
        unfolding True[symmetric]
        by auto
       
    next
      case False
      then show ?thesis
        using add_state(1,2) using z by auto 
    qed
  qed
qed

lemma Anders: 
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
    using sound_wrt_preserves_sound_wrt
    by auto
qed

lemma weight_reach_star_le: 
  assumes "weight_reach_rule\<^sup>*\<^sup>* S S'"
  shows "\<^bold>\<Sum>{S $ c * l |c l. c \<Midarrow>l\<Rightarrow>\<^sup>* c'} \<le> S'$c'"
  using Anders assms unfolding sound_wrt_def apply auto
  done

theorem weight_reach_saturation_correct: 
  assumes "saturation weight_reach_rule S S'"
  shows "S'$c' = \<^bold>\<Sum>{S $ c * l |c l. c \<Midarrow>l\<Rightarrow>\<^sup>* c'}"
  using assms unfolding saturation_def
  using weight_reach_saturated_le[of S' S c'] 
        weight_reach_star_le[of S S' c'] 
        weight_reach_star_less_eq[of S S']
  by fastforce


(*lemma weight_reach_saturation_correct':
  assumes "saturation (weight_reach_rule ts) S S'"
  shows "weight_reach (\<lambda>c. S $ c) (\<lambda>c. S $ c) = \<Sum>{S'$c|c. True} "

lemma weight_reach_saturated_1:
  assumes "saturated (weight_reach_rule ts) S"
  assumes "c \<Midarrow>l\<Rightarrow>\<^sup>* c'"
  shows "S $ c' \<le> l"
  using assms 
  sorry
(* accepts_if_saturated_monoid_star_relp_final[OF assms(1)]
    accepts_K0_iff[of finals "fst c'" "snd c'"] by simp (metis prod.collapse)*)

lemma weight_reach_saturated_sum_le:
  assumes "saturated (weight_reach_rule ts) S"
  shows "S $ c' \<le> \<^bold>\<Sum>{l |c l. c \<Midarrow>l\<Rightarrow>\<^sup>* c'}"
  using weight_reach_saturated_1[OF assms, of _ _ c']
  using SumInf_bounded_if_set_bounded[of "{l |c l. monoid_rtranclp (monoidLTS.l_step_relp ts) c l c'}" "S$c'", OF countable_l_c]
  by blast
*)


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

end