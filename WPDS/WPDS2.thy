theory WPDS2
  imports "LTS" "Saturation" "FinFunWellFounded" "WAutomaton"
begin

datatype 'label operation = pop | swap 'label | push 'label 'label
\<comment> \<open>WPDS has a @{typ "'weight::bounded_idempotent_semiring"} on the rule.\<close>
type_synonym ('ctr_loc, 'label, 'weight) rule = "('ctr_loc \<times> 'label) \<times> 'weight \<times> ('ctr_loc \<times> 'label operation)"
type_synonym ('ctr_loc, 'label) conf = "'ctr_loc \<times> 'label list"

locale WPDS =
  fixes \<Delta> :: "('ctr_loc::countable, 'label::finite, 'weight::bounded_idempotent_semiring) rule set"
  assumes finite_rules: "finite \<Delta>"
begin

primrec lbl :: "'label operation \<Rightarrow> 'label list" where
  "lbl pop = []"
| "lbl (swap \<gamma>) = [\<gamma>]" 
| "lbl (push \<gamma>  \<gamma>') = [\<gamma>, \<gamma>']"

definition is_rule :: "'ctr_loc \<times> 'label \<Rightarrow> 'weight \<Rightarrow> 'ctr_loc \<times> 'label operation \<Rightarrow> bool" ("((_)/ \<midarrow> (_)/ \<hookrightarrow> (_)/ )" [70,70,80] 80) where
  "p\<gamma> \<midarrow>d\<hookrightarrow> p'w \<equiv> (p\<gamma>,d,p'w) \<in> \<Delta>"

inductive_set transition_rel :: "(('ctr_loc, 'label) conf \<times> 'weight \<times> ('ctr_loc, 'label) conf) set" where
  "(p, \<gamma>) \<midarrow>d\<hookrightarrow> (p', w) \<Longrightarrow> ((p, \<gamma>#w'), d, (p', (lbl w)@w')) \<in> transition_rel"
lemma countable_transition_rel: "countable transition_rel"
proof -
  have transition_rel_subset: "transition_rel \<subseteq> (UNIV \<times> {d | c d c'. (c,d,c') \<in> transition_rel} \<times> UNIV)" 
    by fast
  have countable_confs: "countable (UNIV::('ctr_loc, 'label) conf set)"
    by blast
  have "\<And>c d c'. (c,d,c') \<in> transition_rel \<Longrightarrow> \<exists>p\<gamma> p'w. (p\<gamma>,d,p'w) \<in> \<Delta>"
    by (auto simp add: transition_rel.simps is_rule_def, blast)
  then have weights_subset: "{d | c d c'. (c,d,c') \<in> transition_rel} \<subseteq> {d | p\<gamma> d p'w. (p\<gamma>,d,p'w) \<in> \<Delta>}" 
    by blast
  have "finite {d | p\<gamma> d p'w. (p\<gamma>,d,p'w) \<in> \<Delta>}"
    using finite_rules finite_image_set[of "\<lambda>x. x \<in> \<Delta>" "\<lambda>(p,d,q). d", simplified] by simp
  then have "finite {d | c d c'. (c,d,c') \<in> transition_rel}" 
    using finite_subset[OF weights_subset] by blast
  then have "countable {d | c d c'. (c,d,c') \<in> transition_rel}" 
    using countable_finite by blast
  then show "countable transition_rel" 
    using countable_confs countable_subset[OF transition_rel_subset] by blast
qed
interpretation dioidLTS transition_rel proof
  show "countable transition_rel" by (fact countable_transition_rel)
qed

notation step_relp (infix "\<Rightarrow>" 80)
notation step_starp (infix "\<Rightarrow>\<^sup>*" 80)
notation l_step_relp ("(_)/ \<Midarrow> (_)/ \<Rightarrow> (_)/" [70,70,80] 80)
notation monoid_star_relp ("(_)/ \<Midarrow> (_)/ \<Rightarrow>\<^sup>* (_)/" [90,90,100] 100) 

lemma step_relp_def2:
  "(p, \<gamma>w') \<Midarrow>d\<Rightarrow> (p',ww') \<longleftrightarrow> (\<exists>\<gamma> w' w. \<gamma>w' = \<gamma>#w' \<and> ww' = (lbl w)@w' \<and> (p, \<gamma>) \<midarrow>d\<hookrightarrow> (p', w))"
  by (meson l_step_relp_def transition_rel.simps)
end


locale WPDS_with_W_automata = WPDS \<Delta>
  for \<Delta> :: "('ctr_loc::enum, 'label::finite, 'weight::bounded_idempotent_semiring) rule set"
    +
  fixes finals :: "('ctr_loc::enum) set"
begin

interpretation dioidLTS transition_rel proof
  show "countable transition_rel" by (fact countable_transition_rel)
qed 
notation step_relp (infix "\<Rightarrow>" 80)
notation step_starp (infix "\<Rightarrow>\<^sup>*" 80)
notation l_step_relp ("(_)/ \<Midarrow> (_)/ \<Rightarrow> (_)/" [70,70,80] 80)
notation monoid_star_relp ("(_)/ \<Midarrow> (_)/ \<Rightarrow>\<^sup>* (_)/" [90,90,100] 100) 

lemma Suminf_mono: 
  assumes "(X::'weight set) \<subseteq> Y"
  shows "\<^bold>\<Sum> X \<ge> \<^bold>\<Sum> Y"
  sorry

lemma Suminf_mult_isor: 
  assumes "d \<le> (d' :: 'weight)"
  shows "\<^bold>\<Sum> {d * d''| d''. X d''} \<le> \<^bold>\<Sum> {d' * d''| d''. X d''}"
  sorry

lemma Suminf_bigger2: 
  assumes "\<forall>t. X t \<longrightarrow> f t \<le> g t"
  shows "\<^bold>\<Sum> {f t| t. X t} \<le> \<^bold>\<Sum> {g t| t. X t}"
  sorry

lemma geq_Suminf_if_member:
  assumes "d \<in> W "
  shows "d \<ge> \<^bold>\<Sum>W"
  sorry

\<comment> \<open>Generalization of PDS_with_P_automata.accepts that computes the meet-over-all-paths in the W-automaton.\<close>
definition accepts :: "('ctr_loc, 'label, 'weight) w_transitions \<Rightarrow> ('ctr_loc, 'label) conf \<Rightarrow> 'weight" where
  "accepts ts \<equiv> \<lambda>(p,w). (\<^bold>\<Sum>{d | d q. q \<in> finals \<and> (p,(w,d),q) \<in> monoid_rtrancl (wts_to_monoidLTS ts)})"


\<comment> \<open>Weighted pre-star rule updates the finfun of transition weights.\<close>
inductive pre_star_rule :: "('ctr_loc, 'label, 'weight) w_transitions saturation_rule" where
  add_trans: "((p, \<gamma>) \<midarrow>d\<hookrightarrow> (p', w))
      \<Longrightarrow> (p', (lbl w, d'), q) \<in> monoid_rtrancl (wts_to_monoidLTS ts)
      \<Longrightarrow> (ts $ (p, \<gamma>, q)) = d''
      \<Longrightarrow> (d'' + (d * d')) \<noteq> d''
      \<Longrightarrow> pre_star_rule ts ts((p, \<gamma>, q) $:= d'' + (d * d'))"

definition pre_star1 :: "('ctr_loc, 'label, 'weight) w_transitions \<Rightarrow> (('ctr_loc, 'label) transition \<times> 'weight) set" where
  "pre_star1 wts =
    (\<Union>((p, \<gamma>), d, (p', w)) \<in> \<Delta>.
        \<Union>(q,d') \<in> monoidLTS_reach (wts_to_monoidLTS wts) (p') (lbl w).
            {((p, \<gamma>, q), d * d')})"

definition "pre_star_loop = while_option (\<lambda>s. update_wts s (pre_star1 s) \<noteq> s) (\<lambda>s. update_wts s (pre_star1 s))"
definition "pre_star_exec = the o pre_star_loop"
definition "pre_star_exec_check A = (if A={} then pre_star_loop (ts_to_wts A) else None)"

definition "accept_pre_star_exec_check A c = (if A={} then Some (accepts (pre_star_exec (ts_to_wts A)) c) else None)"

theorem pre_star_rule_correct:
  assumes "saturation pre_star_rule (ts_to_wts {}) A"
  shows "accepts A = weight_pre_star (accepts (ts_to_wts {}))"
  using assms
  apply simp
    \<comment> \<open>TODO\<close>
  oops

lemma pre_star_rule_less_aux:
  fixes ts::"(('ctr_loc, 'label, 'weight::bounded_idempotent_semiring) w_transitions)"
  assumes "ts $ (p, \<gamma>, q) + d * d' \<noteq> ts $ (p, \<gamma>, q)"
  assumes "ts' = ts((p, \<gamma>, q) $:= ts $ (p, \<gamma>, q) + d * d')"
  shows "ts > ts'"
proof -
  from assms(1) have "ts $ (p, \<gamma>, q) > ts $ (p, \<gamma>, q) + d * d'" 
    by (simp add: meet.inf.strict_order_iff add.commute add.left_commute)
  then have "ts $ (p, \<gamma>, q) > ts' $ (p, \<gamma>, q)" using assms(2) by simp
  then show ?thesis using assms(2) finfun_update_greater[of ts' "(p, \<gamma>, q)" ts] by blast
qed

lemma pre_star_rule_less:
  assumes "pre_star_rule A B"
  shows "A > B"
  using assms by (auto simp add:pre_star_rule.simps pre_star_rule_less_aux)

lemma pre_star_rule_less_eq:
  assumes "pre_star_rule A B"
  shows "A \<ge> B"
  using pre_star_rule_less[OF assms(1)] by simp

lemma pre_star_saturation_exi:
  shows "\<exists>ts'. saturation pre_star_rule ts ts'"
  by (rule wfp_class_saturation_exi[of pre_star_rule ts])
     (simp add: pre_star_rule_less)

lemma saturation_rtranclp_pre_star_rule_incr: "pre_star_rule\<^sup>*\<^sup>* A B \<Longrightarrow> A \<ge> B"
proof (induction rule: rtranclp_induct)
  case base
  then show ?case by auto
next
  case (step y z)
  then show ?case
    using pre_star_rule_less by fastforce
qed

lemma monoid_star_pop:
  assumes "(p, (lbl w, d), q) \<in> monoid_rtrancl (wts_to_monoidLTS ts)"
      and "w = pop"
    shows "p = q \<and> d = 1"
  using assms monoid_star_w0
  by (auto simp add: one_list_def mstar_wts_empty_one) fastforce

lemma monoid_star_swap:
  assumes "(p, (lbl w, d), q) \<in> monoid_rtrancl (wts_to_monoidLTS ts)"
      and "w = swap l"
    shows "ts $ (p,l,q) = d"
  using assms monoid_star_w1 by fastforce

lemma monoid_star_push:
  assumes "(p, (lbl w, d), q) \<in> monoid_rtrancl (wts_to_monoidLTS ts)"
      and "w = push l l'"
    shows "\<exists>q'. ts $ (p,l,q') * ts $ (q',l',q) = d"
  using assms monoid_star_w2 by fastforce

lemma pre_star_rule_cases:
  assumes "(p, (lbl w, d), q) \<in> monoid_rtrancl (wts_to_monoidLTS ts)"
  shows "(w = pop \<and> q = p \<and> d = 1) \<or>                          
         (\<exists>l. w = swap l \<and> ts $ (p,l,q) = d) \<or> 
         (\<exists>l l'. w = push l l' \<and> (\<exists>q'. ts $ (p,l,q') * ts $ (q',l',q) = d))"
proof (cases rule: operation.exhaust[of w])
  case pop
  then show ?thesis using monoid_star_pop[OF assms(1)] by simp
next
  case (swap l)
  then show ?thesis using monoid_star_swap[OF assms(1)] by simp
next
  case (push l l')
  then show ?thesis using monoid_star_push[OF assms(1)] by simp
qed

lemma pre_star_rule_exhaust:
  assumes "(p, (lbl w, d), q) \<in> monoid_rtrancl (wts_to_monoidLTS ts)"
  obtains        "q = p" "d = 1" "w = pop"
    | l    where "ts $ (p,l,q) = d" "w = swap l"
    | l l' q' where "ts $ (p,l,q') * ts $ (q',l',q) = d" "w = push l l'"
  using pre_star_rule_cases[OF assms(1)] by blast

lemma pre_star_rule_update_spec:
  assumes "pre_star_rule A A'"
      and "A $ (p,\<gamma>,q) \<noteq> A' $ (p,\<gamma>,q)"
    shows "\<exists>d d' p' w.
              A' $ (p,\<gamma>,q) = A $ (p, \<gamma>, q) + d * d' \<and>
              (p, \<gamma>) \<midarrow>d\<hookrightarrow> (p', w) \<and>
              (p', (lbl w, d'), q) \<in> monoid_rtrancl (wts_to_monoidLTS A) \<and>
              A $ (p, \<gamma>, q) + d * d' \<noteq> A $ (p, \<gamma>, q)"
  using assms unfolding pre_star_rule.simps
  apply safe
  subgoal for p' \<gamma>' _ _ _ _ q'
    by (cases "(p,\<gamma>,q) = (p', \<gamma>',q')", auto)
  done

abbreviation push_seq_weight :: "('ctr_loc * 'label list) \<Rightarrow> 'ctr_loc \<Rightarrow> 'weight" ("\<^bold>\<Sigma>_\<Rightarrow>\<^sup>*_") where
  "(\<^bold>\<Sigma>pw\<Rightarrow>\<^sup>*p') \<equiv> \<^bold>\<Sum>{d'. pw \<Midarrow>d'\<Rightarrow>\<^sup>* (p',[])}"

definition sound :: "(('ctr_loc, 'label, 'weight) w_transitions) \<Rightarrow> bool" where
  "sound A \<longleftrightarrow> (\<forall>p p' \<gamma> d. (p, ([\<gamma>],d), p') \<in> (wts_to_monoidLTS A) \<longrightarrow> d \<ge> \<^bold>\<Sigma>(p,[\<gamma>])\<Rightarrow>\<^sup>*p')"

lemma sound_intro:
  assumes "\<And>p p' \<gamma> d. (p, ([\<gamma>], d), p') \<in> wts_to_monoidLTS A \<Longrightarrow> (\<^bold>\<Sigma>(p, [\<gamma>])\<Rightarrow>\<^sup>*p') \<le> d"
  shows "sound A"
  unfolding sound_def using assms by auto

lemma monoid_star_intros_step':
  assumes "(p,w,q) \<in> wts_to_monoidLTS A"
  shows "(p,w,q) \<in> monoid_rtrancl (wts_to_monoidLTS A)"
  using monoid_rtrancl.intros(2)[of p 1 p "(wts_to_monoidLTS A)" w q] assms by fastforce

lemma monoid_star_intros_step:
  assumes "pwq \<in> wts_to_monoidLTS A"
  shows "pwq \<in> monoid_rtrancl (wts_to_monoidLTS A)"
  using assms monoid_star_intros_step' by (cases pwq) auto

lemma monoid_rtrancl_wts_to_monoidLTS_cases_rev':
  assumes "(p\<^sub>1, w\<^sub>1\<^sub>3d\<^sub>1\<^sub>3, p\<^sub>3) \<in> monoid_rtrancl (wts_to_monoidLTS ts)"
  shows "\<exists>d\<^sub>1\<^sub>3. w\<^sub>1\<^sub>3d\<^sub>1\<^sub>3 = ([],d\<^sub>1\<^sub>3) \<or>
           (\<exists>p\<^sub>2 d\<^sub>2\<^sub>3 \<gamma>\<^sub>1\<^sub>2 w\<^sub>2\<^sub>3 d\<^sub>1\<^sub>2.
               w\<^sub>1\<^sub>3d\<^sub>1\<^sub>3 = (\<gamma>\<^sub>1\<^sub>2#w\<^sub>2\<^sub>3,d\<^sub>1\<^sub>3) \<and>
               (p\<^sub>1, ([\<gamma>\<^sub>1\<^sub>2], d\<^sub>1\<^sub>2), p\<^sub>2) \<in> wts_to_monoidLTS ts \<and>
               (p\<^sub>2, (w\<^sub>2\<^sub>3, d\<^sub>2\<^sub>3), p\<^sub>3) \<in> monoid_rtrancl (wts_to_monoidLTS ts) \<and>
               d\<^sub>1\<^sub>3 = d\<^sub>1\<^sub>2 * d\<^sub>2\<^sub>3)"
  using assms
proof (induction rule: monoid_rtrancl.induct)
  case (monoid_rtrancl_refl)
  then show ?case
    by (simp add: one_list_def one_prod_def)
next
  case (monoid_rtrancl_into_rtrancl p\<^sub>1 w\<^sub>1\<^sub>3d\<^sub>1\<^sub>3 p\<^sub>3 w\<^sub>3\<^sub>4d\<^sub>3\<^sub>4 p\<^sub>4)
  show ?case
  proof (cases "(fst w\<^sub>1\<^sub>3d\<^sub>1\<^sub>3)")
    case (Cons \<gamma>\<^sub>1\<^sub>2 w\<^sub>2\<^sub>3)
    define d\<^sub>1\<^sub>3 where "d\<^sub>1\<^sub>3 = (snd w\<^sub>1\<^sub>3d\<^sub>1\<^sub>3)"
    define w\<^sub>3\<^sub>4 where "w\<^sub>3\<^sub>4 = fst w\<^sub>3\<^sub>4d\<^sub>3\<^sub>4"
    define d\<^sub>3\<^sub>4 where "d\<^sub>3\<^sub>4 = snd w\<^sub>3\<^sub>4d\<^sub>3\<^sub>4"
    define w\<^sub>2\<^sub>4 where "w\<^sub>2\<^sub>4 = w\<^sub>2\<^sub>3 @ w\<^sub>3\<^sub>4"

    have w24_tl: "w\<^sub>2\<^sub>4 = tl (fst (w\<^sub>1\<^sub>3d\<^sub>1\<^sub>3 * w\<^sub>3\<^sub>4d\<^sub>3\<^sub>4))"
      by (simp add: local.Cons mult_prod_def times_list_def w\<^sub>2\<^sub>4_def w\<^sub>3\<^sub>4_def)

    have "w\<^sub>1\<^sub>3d\<^sub>1\<^sub>3 = (\<gamma>\<^sub>1\<^sub>2 # w\<^sub>2\<^sub>3, d\<^sub>1\<^sub>3)"
      using Cons by (metis d\<^sub>1\<^sub>3_def surjective_pairing) 

    then have "\<exists>d\<^sub>1\<^sub>3. w\<^sub>1\<^sub>3d\<^sub>1\<^sub>3 = ([], d\<^sub>1\<^sub>3) \<or>
                (\<exists>p\<^sub>2 d\<^sub>2\<^sub>3 \<gamma>\<^sub>1\<^sub>2 w\<^sub>2\<^sub>3 d\<^sub>1\<^sub>2.
                   w\<^sub>1\<^sub>3d\<^sub>1\<^sub>3 = (\<gamma>\<^sub>1\<^sub>2 # w\<^sub>2\<^sub>3, d\<^sub>1\<^sub>3) \<and>
                   (p\<^sub>1, ([\<gamma>\<^sub>1\<^sub>2], d\<^sub>1\<^sub>2), p\<^sub>2) \<in> wts_to_monoidLTS ts \<and> 
                   (p\<^sub>2, (w\<^sub>2\<^sub>3, d\<^sub>2\<^sub>3), p\<^sub>3) \<in> monoid_rtrancl (wts_to_monoidLTS ts) \<and> 
                   d\<^sub>1\<^sub>3 = d\<^sub>1\<^sub>2 * d\<^sub>2\<^sub>3)"
      using monoid_rtrancl_into_rtrancl.IH by auto
    then obtain p\<^sub>2 d\<^sub>2\<^sub>3 \<gamma>\<^sub>1\<^sub>2 w\<^sub>2\<^sub>3 d\<^sub>1\<^sub>2 where props:
      "((w\<^sub>1\<^sub>3d\<^sub>1\<^sub>3 = (\<gamma>\<^sub>1\<^sub>2 # w\<^sub>2\<^sub>3, d\<^sub>1\<^sub>3) \<and>
       (p\<^sub>1, ([\<gamma>\<^sub>1\<^sub>2], d\<^sub>1\<^sub>2), p\<^sub>2) \<in> wts_to_monoidLTS ts \<and> 
       (p\<^sub>2, (w\<^sub>2\<^sub>3, d\<^sub>2\<^sub>3), p\<^sub>3) \<in> monoid_rtrancl (wts_to_monoidLTS ts) \<and> 
       d\<^sub>1\<^sub>3 = d\<^sub>1\<^sub>2 * d\<^sub>2\<^sub>3))"
      using d\<^sub>1\<^sub>3_def Cons by auto

    define d\<^sub>2\<^sub>4 where "d\<^sub>2\<^sub>4 = d\<^sub>2\<^sub>3 * d\<^sub>3\<^sub>4"

    have "(p\<^sub>2, (w\<^sub>2\<^sub>4, d\<^sub>2\<^sub>4), p\<^sub>4) \<in> monoid_rtrancl (wts_to_monoidLTS ts)"
      by (smt (verit) d\<^sub>2\<^sub>4_def d\<^sub>3\<^sub>4_def fst_conv list.sel(3) local.Cons monoid_rtrancl.simps 
          monoid_rtrancl_into_rtrancl.hyps(2) mult_prod_def props snd_conv times_list_def w\<^sub>2\<^sub>4_def 
          w\<^sub>3\<^sub>4_def)
    moreover
    define d\<^sub>1\<^sub>4 where "d\<^sub>1\<^sub>4 = d\<^sub>1\<^sub>2 * d\<^sub>2\<^sub>4"
    moreover
    have "(p\<^sub>1, ([\<gamma>\<^sub>1\<^sub>2], d\<^sub>1\<^sub>2), p\<^sub>2) \<in> wts_to_monoidLTS ts"
      using props by fastforce
    ultimately
    show ?thesis
      by (smt (verit) w24_tl props d\<^sub>1\<^sub>3_def d\<^sub>2\<^sub>4_def d\<^sub>3\<^sub>4_def fst_conv hd_append  list.exhaust_sel
          list.sel(1) list.simps(3) mult.assoc mult_prod_def times_list_def)
  next
    case Nil
    then show ?thesis
      by (metis monoid_rtrancl.monoid_rtrancl_refl monoid_rtrancl_into_rtrancl.hyps(1)
          monoid_rtrancl_into_rtrancl.hyps(2) monoid_rtrancl_into_rtrancl.prems monoid_star_w0
          mstar_wts_empty_one mult.right_neutral mult_1 one_list_def one_prod_def prod.exhaust_sel
          wts_label_exist)
  qed
qed

lemma monoid_rtrancl_wts_to_monoidLTS_cases_rev:
  assumes "(p, (\<gamma>#w,d), p') \<in> monoid_rtrancl (wts_to_monoidLTS ts)"
  shows "\<exists>d' s d''.
           (p, ([\<gamma>], d'), s) \<in> wts_to_monoidLTS ts \<and>
           (s, (w, d''), p') \<in> monoid_rtrancl (wts_to_monoidLTS ts) \<and>
           d = d' * d''"
  using assms monoid_rtrancl_wts_to_monoidLTS_cases_rev' by fastforce

(* We are not using this induction. But it could be useful. *)
lemma wts_to_monoidLTS_induct_reverse:
  assumes "(p, wd, p') \<in> monoid_rtrancl (wts_to_monoidLTS ts)"
  assumes "(\<And>a. P a 1 a)"
  assumes "(\<And>p wd p' l p''.
             (p, wd, p') \<in> (wts_to_monoidLTS ts) \<Longrightarrow> 
             P p' l p'' \<Longrightarrow> 
             (p', l, p'') \<in> monoid_rtrancl (wts_to_monoidLTS ts) \<Longrightarrow>
             P p (wd * l) p'')"
  shows "P p wd p'"
  using assms monoid_rtrancl_induct_rev[of p wd] by metis

lemma monoid_star_nonempty:
  assumes "(p, w, p') \<in> monoid_rtrancl (wts_to_monoidLTS ts)"
  assumes "fst w \<noteq> []"
  shows "\<exists>pi d1 d2. (snd w) = d1 * d2 \<and> 
                    (pi, (tl (fst w), d2), p') \<in> monoid_rtrancl (wts_to_monoidLTS ts) \<and> 
                    (p, ([hd (fst w)], d1), pi) \<in> wts_to_monoidLTS ts"
  by (metis assms list.collapse monoid_rtrancl_wts_to_monoidLTS_cases_rev surjective_pairing)

lemma sum_distr: 
  "d1 * \<^bold>\<Sum> D = \<^bold>\<Sum> {d1 * d2 | d2. d2 \<in> D}"
  sorry

lemma sum_of_sums:
  "\<^bold>\<Sum> {\<^bold>\<Sum> {d. P d d'} |d'. Q d'} = \<^bold>\<Sum> {d | d d'. P d d' \<and> Q d'}"
  sorry

lemma sum_of_sums2:
  "\<^bold>\<Sum> {\<^bold>\<Sum> {f d d'| d. P d d'} |d'. Q d'} = \<^bold>\<Sum> {f d d' | d d'. P d d' \<and> Q d'}"
  sorry

lemma sum_of_sums_mult:
  "\<^bold>\<Sum> {\<^bold>\<Sum> {d. P d} * d' |d'. Q d'} = \<^bold>\<Sum> {d * d' | d d'. P d \<and> Q d'}"
  sorry

lemma sum_of_sums_mult2:
  "\<^bold>\<Sum> {\<^bold>\<Sum> {f d d'| d. P d d'} * g d' |d'. Q d'} = \<^bold>\<Sum> {f d d' * g d' | d d'. P d d' \<and> Q d'}"
  sorry

lemmas monoid_star_relp_induct [consumes 1, case_names monoid_star_refl monoid_star_into_rtrancl] = 
  MonoidClosure.monoid_rtranclp.induct[of l_step_relp ] (* "(_,_)" _ "(_,_)" *)

lemmas monoid_star_relp_induct_rev [consumes 1, case_names monoid_star_refl monoid_star_into_rtrancl] = 
  MonoidClosure.monoid_rtranclp_induct_rev[of l_step_relp ] (*"(_,_)" _ "(_,_)" *)

lemma step_rule_aux:
  assumes "(p, \<gamma>) \<midarrow>d\<hookrightarrow> (p', w)"
  assumes "c \<Midarrow>d'\<Rightarrow>\<^sup>* (p, \<gamma> # w')"
  shows "c \<Midarrow>(d' * d)\<Rightarrow>\<^sup>* (p', lbl w @ w')"
  using assms by (meson monoid_rtranclp.simps step_relp_def2)

lemma step_relp_append:
  assumes "(p,w) \<Midarrow>d'\<Rightarrow>\<^sup>* (p',w')"
  shows "(p, w @ v) \<Midarrow>d'\<Rightarrow>\<^sup>* (p', w' @ v)"
  using MonoidClosure.monoid_rtranclp.induct[of "\<lambda>a b c. a\<Midarrow>b\<Rightarrow>c" "(p,w)" d' "(p',w')"  
      "\<lambda>(p,w) d' (p',w'). (p,w @ v) \<Midarrow>d'\<Rightarrow>\<^sup>* (p', w' @ v)", OF assms(1)]
        step_rule_aux step_relp_def2 by fastforce

lemma step_relp_append2:
  assumes "(p, u) \<Midarrow> d''' \<Rightarrow>\<^sup>* (p'', [])"
  assumes "v = u @ w"
  shows "(p, v) \<Midarrow> d''' \<Rightarrow>\<^sup>* (p'', w)"
  using assms step_relp_append self_append_conv2 by fastforce

lemma step_relp_seq:
  assumes "(p, a) \<Midarrow>d1\<Rightarrow>\<^sup>* (pi, [])"
  assumes "(pi, w) \<Midarrow>d'\<Rightarrow>\<^sup>* (p', [])"
  shows "(p, a @ w) \<Midarrow>(d1 * d')\<Rightarrow>\<^sup>* (p', [])"
proof -
  have "(p, a @ w) \<Midarrow> d1 \<Rightarrow>\<^sup>* (pi, w)"
    using assms(1) using step_relp_append by fastforce
  show ?thesis
    by (meson \<open>(p, a @ w) \<Midarrow> d1 \<Rightarrow>\<^sup>* (pi, w)\<close> assms(2) monoid_rtranclp_trans)
qed

lemma monoid_star_relp_if_l_step_relp:
  assumes "(p,w) \<Midarrow>d\<Rightarrow> (p',[])"
  shows "(p,w) \<Midarrow>d\<Rightarrow>\<^sup>* (p',[])"
  by (metis assms monoid_rtranclp.monoid_rtrancl_into_rtrancl monoid_rtranclp.monoid_rtrancl_refl 
      mult_1)

lemma push_seq_weight_if_monoid_star_relp:
  assumes "(p,w) \<Midarrow>d\<Rightarrow>\<^sup>* (p',[])"
  shows "\<^bold>\<Sigma>(p, w)\<Rightarrow>\<^sup>*p' \<le> d"
  by (simp add: assms geq_Suminf_if_member)

lemma push_seq_weight_if_l_step_relp:
  assumes "(p,w) \<Midarrow>d\<Rightarrow> (p',[])"
  shows "\<^bold>\<Sigma>(p, w)\<Rightarrow>\<^sup>*p' \<le> d"
  by (simp add: assms monoid_star_relp_if_l_step_relp push_seq_weight_if_monoid_star_relp)

lemma push_seq_weight_trans:
  assumes "\<^bold>\<Sigma>(p'', w')\<Rightarrow>\<^sup>*pi \<le> d1"
  assumes "\<^bold>\<Sigma>(pi, w'')\<Rightarrow>\<^sup>*p2 \<le> d2"
  shows "\<^bold>\<Sigma>(p'', w'@w'')\<Rightarrow>\<^sup>*p2 \<le> d1 * d2"
proof -
  have "(\<^bold>\<Sigma>(p'',w'@w'') \<Rightarrow>\<^sup>* p2) \<le> \<^bold>\<Sum>{d1' * d2'| d1'  d2'. (p'',w') \<Midarrow>d1'\<Rightarrow>\<^sup>* (pi,[]) \<and> (pi,w'') \<Midarrow>d2'\<Rightarrow>\<^sup>* (p2,[])}"
    by (smt (verit, ccfv_threshold) Collect_mono_iff Suminf_mono append_Cons append_self_conv2 step_relp_seq)
  also have "... \<le> (\<^bold>\<Sigma>(p'',w') \<Rightarrow>\<^sup>* pi) * (\<^bold>\<Sigma>(pi,w'') \<Rightarrow>\<^sup>* p2)"
    by (simp add: sum_distr sum_of_sums_mult)
  also have "... \<le> d1 * d2"
    using assms BoundedDioid.mult_isol_var by auto
  finally 
  show ?thesis
    by auto
qed

lemma push_seq_weight_trans_push:
  assumes "\<^bold>\<Sigma>(p'', [\<mu>'])\<Rightarrow>\<^sup>*pi \<le> d1"
  assumes "\<^bold>\<Sigma>(pi, [\<mu>''])\<Rightarrow>\<^sup>*p2 \<le> d2"
  shows "\<^bold>\<Sigma>(p'', [\<mu>', \<mu>''])\<Rightarrow>\<^sup>*p2 \<le> d1 * d2"
  using assms push_seq_weight_trans[of p'' "[\<mu>']" pi d1 "[\<mu>'']" p2 d2] by auto

lemma monoid_star_relp_push_seq_weight_trans:
  assumes "(p1, w) \<Midarrow>d\<Rightarrow>\<^sup>* (p'', w')"
  assumes "\<^bold>\<Sigma>(p'', w')\<Rightarrow>\<^sup>*p2 \<le> d'"
  shows "\<^bold>\<Sigma>(p1, w)\<Rightarrow>\<^sup>*p2 \<le> d * d'"
proof -
  have "\<^bold>\<Sigma> (p1, w) \<Rightarrow>\<^sup>* p2 \<le> \<^bold>\<Sum>{d * d'| d'. (p1, w) \<Midarrow>d\<Rightarrow>\<^sup>* (p'',w') \<and> (p'',w') \<Midarrow>d'\<Rightarrow>\<^sup>* (p2,[])}"
    using Collect_mono_iff Suminf_mono monoid_rtranclp_trans by smt
  also have "... \<le> \<^bold>\<Sum>{d * d'| d'. (p'',w') \<Midarrow>d'\<Rightarrow>\<^sup>* (p2,[])}"
    using \<open>(p1, w) \<Midarrow> d \<Rightarrow>\<^sup>* (p'', w')\<close> by fastforce
  also have "... \<le> d * \<^bold>\<Sigma>(p'',w') \<Rightarrow>\<^sup>* p2"
    by (simp add: sum_distr)
  also have "... \<le> d * d'"
    using assms by (simp add: assms BoundedDioid.mult_isol)
  finally 
  show ?thesis
    by auto
qed

lemma push_seq_weight_trans_Cons:
  assumes "\<^bold>\<Sigma>(p, [\<gamma>])\<Rightarrow>\<^sup>*pi \<le> d1"
  assumes "\<^bold>\<Sigma>(pi, w)\<Rightarrow>\<^sup>*p' \<le> d2"
  shows "\<^bold>\<Sigma>(p, \<gamma> # w)\<Rightarrow>\<^sup>*p' \<le> d1 * d2"
  using assms push_seq_weight_trans[of p "[\<gamma>]" pi d1 w p' d2] by auto

lemma sound_elim2:
  assumes "sound A"
  assumes "(p, (w,d), p') \<in> monoid_rtrancl (wts_to_monoidLTS A)"
  shows "d \<ge> \<^bold>\<Sigma>(p,w) \<Rightarrow>\<^sup>* p'"
  using assms(2) 
proof (induction w arbitrary: d p)
  case Nil
  then have "d = 1"
    by (simp add: mstar_wts_empty_one)
  have "(p, []) \<Midarrow>1\<Rightarrow>\<^sup>* (p', [])"
    using Nil monoid_star_pop by fastforce
  have "d \<ge> \<^bold>\<Sigma>(p, []) \<Rightarrow>\<^sup>* p'" 
    by (simp add: \<open>(p, []) \<Midarrow> 1 \<Rightarrow>\<^sup>* (p', [])\<close> \<open>d = 1\<close> geq_Suminf_if_member)
  then show ?case .
next
  case (Cons \<gamma> w)
  from Cons(2) have
    "\<exists>pi d1 d2. d = d1 * d2 
                \<and> (pi, (w, d2), p') \<in> monoid_rtrancl (wts_to_monoidLTS A)
                \<and> (p, ([\<gamma>], d1), pi) \<in> (wts_to_monoidLTS A)"
    unfolding monoid_star_is_monoid_rtrancl
    using monoid_star_nonempty by fastforce
  then obtain pi d1 d2 where obt:
    "d = d1 * d2"
    "(pi, (w, d2), p') \<in> monoid_rtrancl (wts_to_monoidLTS A)"
    "(p, ([\<gamma>], d1), pi) \<in> wts_to_monoidLTS A"
    by blast
  then have d2l: "d2 \<ge> \<^bold>\<Sigma>(pi, w) \<Rightarrow>\<^sup>* p'"
    using Cons(1)[of pi d2] by auto

  have "d1 \<ge> (\<^bold>\<Sigma> (p, [\<gamma>]) \<Rightarrow>\<^sup>* pi)"
    using assms(1) obt(3) sound_def by blast
  then have "\<^bold>\<Sigma> (p, \<gamma> # w) \<Rightarrow>\<^sup>* p' \<le>  d1 * d2"
    using d2l push_seq_weight_trans_Cons by auto
  also have "... = d" 
    using \<open>d = d1 * d2\<close> by fast 
  finally show ?case .
qed

lemma sound_def2:
  "sound A \<longleftrightarrow> (\<forall>p p' w d. (p, (w,d), p') \<in> monoid_rtrancl (wts_to_monoidLTS A) \<longrightarrow> d \<ge> \<^bold>\<Sigma>(p,w) \<Rightarrow>\<^sup>* p')"
proof
  assume "sound A"
  then show "\<forall>p p' w d. (p, (w, d), p') \<in> monoid_rtrancl (wts_to_monoidLTS A) \<longrightarrow> (\<^bold>\<Sigma>(p, w)\<Rightarrow>\<^sup>*p') \<le> d"
    using sound_elim2 by blast
next
  assume "\<forall>p p' w d. (p, (w, d), p') \<in> monoid_rtrancl (wts_to_monoidLTS A) \<longrightarrow> (\<^bold>\<Sigma>(p, w)\<Rightarrow>\<^sup>*p') \<le> d"
  then show "sound A"
    using monoid_star_intros_step unfolding sound_def by blast
qed

lemma pre_star_rule_sound:
  assumes "sound A"
  assumes "pre_star_rule A A'"
  shows "sound A'"
proof -
  obtain p' \<gamma>' d p'' w' d' q d'' where ps:
    "(p',\<gamma>') \<midarrow>d\<hookrightarrow> (p'',w')"
    "d'' + d * d' \<noteq> d''" 
    "(p'',(lbl w', d'),q) \<in> monoid_rtrancl (wts_to_monoidLTS A)" 
    "A' = A((p', \<gamma>', q) $:= d'' + d * d')" 
    "A $ (p', \<gamma>', q) = d''" 
    using assms(2) pre_star_rule.cases by metis
  show "sound A'"
  proof (rule sound_intro)
    fix p1 p2 \<mu> l
    assume a: "(p1, ([\<mu>], l), p2) \<in> wts_to_monoidLTS A'"      
    show "l \<ge> \<^bold>\<Sigma> (p1, [\<mu>]) \<Rightarrow>\<^sup>* p2"
    proof (cases "p1 = p' \<and> \<mu> = \<gamma>' \<and> p2 = q")
      case True
      then have True': "p1 = p'" "\<mu> = \<gamma>'" "p2 = q"
        by auto
      have ldd': "l = d'' + d * d'"
        using a unfolding ps(4) True' unfolding wts_to_monoidLTS_def by auto
      have d''_geq: "d'' \<ge> \<^bold>\<Sigma> (p1,[\<mu>]) \<Rightarrow>\<^sup>* p2"
        using ps(5) assms(1) True unfolding sound_def wts_to_monoidLTS_def by force
      have p1_to_p''1: "(p1, [\<mu>]) \<Midarrow>d\<Rightarrow> (p'', lbl w')"
        using ps(1) True step_relp_def2 by auto
      show ?thesis
      proof (rule pre_star_rule_exhaust[OF ps(3)[unfolded True'[symmetric]]])
        assume "p2 = p''"
        assume "d' = 1"
        assume "w' = pop"
        from p1_to_p''1 have "(p1, [\<mu>]) \<Midarrow>d * d'\<Rightarrow> (p2,[])"
          using \<open>d' = 1\<close> \<open>w' = pop\<close> \<open>p2 = p''\<close> by auto
        then have "d * d' \<ge> \<^bold>\<Sigma> (p1, [\<mu>]) \<Rightarrow>\<^sup>* p2"
          using push_seq_weight_if_l_step_relp[of p1 "[\<mu>]" "d * d'" p2] by auto
        then show "l \<ge> \<^bold>\<Sigma> (p1, [\<mu>]) \<Rightarrow>\<^sup>* p2"
          using d''_geq ldd' by auto
      next
        fix \<mu>'
        assume "A $ (p'', \<mu>', p2) = d'"
        assume w'_swap: "w' = swap \<mu>'"
        from ps(3) have "(p'', ([\<mu>'],d'), p2) \<in> monoid_rtrancl (wts_to_monoidLTS A)"
          using True'(3) \<open>w' = swap \<mu>'\<close> by force
        then have p''_to_p2: "d' \<ge> \<^bold>\<Sigma> (p'',[\<mu>']) \<Rightarrow>\<^sup>* p2"
          using assms(1) sound_elim2 by force
        from p1_to_p''1 have "(p1, [\<mu>]) \<Midarrow>d\<Rightarrow>\<^sup>* (p'',[\<mu>'])"
          unfolding True' w'_swap using monoid_rtranclp.monoid_rtrancl_into_rtrancl by fastforce
        then have "\<^bold>\<Sigma> (p1, [\<mu>]) \<Rightarrow>\<^sup>* p2 \<le> d * d'"
          using p''_to_p2 monoid_star_relp_push_seq_weight_trans by auto
        then show "l \<ge> \<^bold>\<Sigma> (p1, [\<mu>]) \<Rightarrow>\<^sup>* p2"
          using d''_geq ldd' by auto
      next
        fix \<mu>' \<mu>'' pi
        assume edge_weights: "A $ (p'', \<mu>', pi) * A $ (pi, \<mu>'', p2) = d'"
        assume "w' = push \<mu>' \<mu>''"
        define d1 where "d1 = A $ (p'', \<mu>', pi)"
        define d2 where "d2 = A $ (pi, \<mu>'', p2)"
        have "d' = d1 * d2"
          using d1_def d2_def edge_weights by auto

        from p1_to_p''1 have "(p1,[\<mu>]) \<Midarrow>d\<Rightarrow>\<^sup>* (p'',[\<mu>',\<mu>''])"
          using \<open>w' = push \<mu>' \<mu>''\<close> monoid_rtranclp.monoid_rtrancl_into_rtrancl by fastforce
        moreover
        have "d1 \<ge> \<^bold>\<Sigma>(p'',[\<mu>']) \<Rightarrow>\<^sup>* pi"
          using d1_def assms(1) sound_def by (force simp add: wts_to_monoidLTS_def)
        moreover
        have "d2 \<ge> \<^bold>\<Sigma>(pi,[\<mu>'']) \<Rightarrow>\<^sup>* p2"
          using d2_def assms(1) sound_def by (force simp add: wts_to_monoidLTS_def)
        ultimately
        have "d * d1 * d2 \<ge> \<^bold>\<Sigma> (p1, [\<mu>]) \<Rightarrow>\<^sup>* p2"
          by (simp add: mult.assoc push_seq_weight_trans_push monoid_star_relp_push_seq_weight_trans)
        then show "l \<ge> \<^bold>\<Sigma> (p1, [\<mu>]) \<Rightarrow>\<^sup>* p2"
          using d''_geq ldd' by (simp add: \<open>d' = d1 * d2\<close> mult.assoc) 
      qed
    next
      case False
      then have "(p1, ([\<mu>], l), p2) \<in> wts_to_monoidLTS A"
        using ps(4) a unfolding wts_to_monoidLTS_def by auto
      then show ?thesis
        using assms unfolding sound_def by auto
    qed
  qed
qed

lemma pre_star_rule_rtranclp_sound:
  assumes "sound A"
  assumes "pre_star_rule\<^sup>*\<^sup>* A A'"
  shows "sound A'"
  using assms(2,1)
proof (induction)
  case base
  then show ?case
    .
next
  case (step A' A'')
  then show ?case
    using pre_star_rule_sound by blast
qed

lemma accept_is_one_if_final_empty:
  assumes "p \<in> finals"
  shows "accepts A (p,[]) = 1"
proof -
  have "{d | d q. q \<in> finals \<and> (p,([],d),q) \<in> monoid_rtrancl (wts_to_monoidLTS A)} = {1}"
    by (smt (verit, ccfv_threshold) Collect_cong assms monoid_rtrancl.simps
        monoid_star_is_monoid_rtrancl mstar_wts_empty_one one_list_def one_prod_def singleton_conv)
  then show ?thesis
    by (simp add: accepts_def)
qed

lemma accept_is_zero_if_nonfinal_empty:
  assumes "p \<notin> finals"
  shows "accepts A (p,[]) = 0"
proof -
  have "{d | d q. q \<in> finals \<and> (p,([],d),q) \<in> monoid_rtrancl (wts_to_monoidLTS A)} = {}"
    by (smt (verit, del_insts) Collect_empty_eq lbl.simps(1) monoid_star_pop assms)
  then show ?thesis
    by (smt (verit, ccfv_threshold) Collect_cong accepts_def old.prod.case SumInf_empty)
qed

lemma zero_weight_if_nonrefl_path_in_K0:
  "(p,wd,q) \<in> monoid_rtrancl (wts_to_monoidLTS (K$ 0)) \<Longrightarrow> p \<noteq> q \<Longrightarrow> snd wd = 0"
  apply (induct rule: monoid_rtrancl_induct_rev, simp)
  subgoal for a w b c w'
    apply (cases "b \<noteq> c")
     apply (simp add: mult_prod_def)
    unfolding wts_to_monoidLTS_def
    apply simp
    by (metis mult_prod_def mult_zero_left snd_conv)
  done

lemma zero_weight_if_nonempty_word_in_K0:
  "(p,wd,q) \<in> monoid_rtrancl (wts_to_monoidLTS (K$ 0)) \<Longrightarrow> fst wd \<noteq> [] \<Longrightarrow> snd wd = 0"
  apply (induct rule: monoid_rtrancl_induct_rev, simp add: one_list_def one_prod_def)
  subgoal for a w b c w'
    apply (cases "fst w' \<noteq> []")
     apply (simp add: mult_prod_def)
    unfolding wts_to_monoidLTS_def
    apply simp
    by (metis mult_prod_def mult_zero_left snd_conv)
  done

lemma Suminf_is_zero_if_subset_singleton_zero: "X \<subseteq> {0} \<Longrightarrow> \<^bold>\<Sum> X = 0"
  using subset_singletonD by fastforce

lemma accepts_K0_is_zero_if_nonfinal:
  assumes "p \<notin> finals"
  shows "accepts (K$ 0) (p,w) = 0"
proof -
  have "{uuu :: 'weight. \<exists>q. q \<in> finals \<and> (p, (w, uuu), q) \<in> monoid_rtrancl (wts_to_monoidLTS (K$ 0))} \<subseteq> {0}"
    using zero_weight_if_nonrefl_path_in_K0[of p "(w,_)" _] assms by auto
  then show ?thesis
    unfolding accepts_def using Suminf_is_zero_if_subset_singleton_zero by auto
qed

lemma accepts_K0_is_zero_if_nonempty:
  assumes "w \<noteq> []"
  shows "accepts (K$ 0) (p,w) = 0"
proof -
  have "{uuu :: 'weight. \<exists>q. q \<in> finals \<and> (p, (w, uuu), q) \<in> monoid_rtrancl (wts_to_monoidLTS (K$ 0))} \<subseteq> {0}"
    using zero_weight_if_nonempty_word_in_K0[of p "(w,_)" _] assms by auto
  then show ?thesis
    unfolding accepts_def using Suminf_is_zero_if_subset_singleton_zero by auto
qed

lemma accepts_empty_iff: "accepts A (p,[]) = (if p\<in>finals then 1 else 0)"
  by (simp add: accept_is_one_if_final_empty accept_is_zero_if_nonfinal_empty)

lemma accepts_K0_iff: "accepts (K$ 0) (p,w) = (if p\<in>finals \<and> w = [] then 1 else 0)"
  by (metis accept_is_one_if_final_empty accepts_K0_is_zero_if_nonfinal accepts_K0_is_zero_if_nonempty)

lemma sound_empty: "sound (K$ 0)"
  by (simp add: sound_def wts_to_monoidLTS_def)

lemma lemma_3_2_w_alternative:
  assumes soundA': "sound A'"
  shows "accepts A' pv \<ge> weight_pre_star (accepts (K$ 0)) pv"
proof -
  obtain p v where pv_split: "pv = (p, v)"
    by (cases pv)
  have "weight_pre_star (accepts (K$ 0)) (p,v) = \<^bold>\<Sum>{d' * accepts (K$ 0) (q,w)| d' q w. (p,v) \<Midarrow>d'\<Rightarrow>\<^sup>* (q,w)}"
    by (simp add: weight_pre_star_def)
  also have "... = \<^bold>\<Sum>{d' * (if q\<in>finals \<and> w=[] then 1 else 0)| d' q w. (p,v) \<Midarrow>d'\<Rightarrow>\<^sup>* (q,w)}"
    using accepts_K0_iff by presburger
  also have "... \<le> \<^bold>\<Sum>{d' |d' q. q \<in> finals \<and> (p,v) \<Midarrow>d'\<Rightarrow>\<^sup>* (q,[])}"
    by (smt (verit) Collect_mono_iff Suminf_mono mult.right_neutral)
  also have "... = \<^bold>\<Sum>{(\<^bold>\<Sigma> (p,v) \<Rightarrow>\<^sup>* q) | q. q \<in> finals}"
    using sum_of_sums_mult2[of "\<lambda>d q. d" "\<lambda>d q. (p,v) \<Midarrow>d\<Rightarrow>\<^sup>* (q,[])" "\<lambda>q. 1" "\<lambda>q. q \<in> finals"]
    apply auto
    by (smt (verit) Collect_cong Orderings.order_eq_iff)
  also have "... \<le> \<^bold>\<Sum>{\<^bold>\<Sigma>(p,v) \<Rightarrow>\<^sup>* q |d q. q \<in> finals \<and> (p, (v, d), q) \<in> monoid_rtrancl (wts_to_monoidLTS A')}" 
    by (smt (verit) Collect_mono_iff Suminf_mono) 
  also have "... \<le> \<^bold>\<Sum>{d |d q. q \<in> finals \<and> (p, (v, d), q) \<in> monoid_rtrancl (wts_to_monoidLTS A')}" 
    using Suminf_bigger2[of 
        "\<lambda>(d, q). q \<in> finals \<and> (p, (v, d), q) \<in> monoid_rtrancl (wts_to_monoidLTS A')"
        "\<lambda>(d, q). \<^bold>\<Sigma> (p,v) \<Rightarrow>\<^sup>* q"
        "\<lambda>(d, q). d"
        ]
    using soundA' sound_def2 by force
  also have "... = accepts A' (p,v)"
    unfolding accepts_def by (simp split: prod.split)
  finally show ?thesis
    unfolding pv_split by auto
qed

lemma accepts_lte_accepts_K0':
  shows "accepts A' (p,v) \<le> accepts (K$ 0) (p,v)"
proof (cases "p \<in> finals \<and> v = []")
  case True
  then have "accepts (K$ 0) (p,v) = 1"
    using accepts_K0_iff by auto
  also have "... \<ge> accepts A' (p,v)"
    unfolding accepts_def
    using True accepts_def accept_is_one_if_final_empty by force
  finally show ?thesis 
    by auto
next
  case False
  then have "p \<notin> finals \<or> v \<noteq> []"
    by auto
  then show ?thesis
  proof
    assume "p \<notin> finals"
    then have "accepts (K$ 0) (p,v) = 0"
      using accepts_K0_iff by auto
    also have "... \<ge> accepts A' (p,v)"
      by simp
    finally show ?thesis 
      by auto
  next
    assume "v \<noteq> []"
    then have "accepts (K$ 0) (p,v) = 0"
      using accepts_K0_iff by auto
    also have "... \<ge> accepts A' (p,v)"
       by simp
    finally show ?thesis 
      by auto
  qed
qed

lemma accepts_lte_accepts_K0:
  shows "accepts A' \<le> accepts (K$ 0)"
  using accepts_lte_accepts_K0' by (simp add: le_fun_def)

lemma weight_pre_star_mono:
  assumes "X \<le> Y"
  shows "weight_pre_star X c \<le> weight_pre_star Y c"
proof -
  have "\<forall>c. X c \<le> Y c"
    using assms by (simp add: le_funD)
  then have XY: "\<forall>l c'. l * X c' \<le> l * Y c'"
    by (simp add: idempotent_semiring_ord_class.mult_isol)

  have "weight_pre_star X c = \<^bold>\<Sum> {l * X c' |l c'. c \<Midarrow> l \<Rightarrow>\<^sup>* c'}"
    unfolding weight_pre_star_def by auto
  also
  have "... \<le> \<^bold>\<Sum> {l * Y c' |l c'. c \<Midarrow> l \<Rightarrow>\<^sup>* c'}"
    using Suminf_bigger2[of "\<lambda>(l, c'). c \<Midarrow> l \<Rightarrow>\<^sup>* c'" "\<lambda>(l, c). l * X c" "\<lambda>(l, c). l * Y c"] XY by auto
  also 
  have "... \<le> weight_pre_star Y c"
    unfolding weight_pre_star_def by auto
  finally
  show ?thesis 
    by auto
qed

lemma weight_pre_star_accepts_lt_weight_pre_star_accepts_K0:
  "weight_pre_star (accepts A') c \<le> weight_pre_star (accepts (K$ 0)) c"
  using weight_pre_star_mono[OF accepts_lte_accepts_K0] by auto

(* Begin superfluous lemmas *)

lemma lemma_3_2_w_alternative_BONUS:
  assumes soundA': "sound A'"
  shows "accepts A' (p,v) \<ge> weight_pre_star (accepts A) (p,v)"
proof -
  have "weight_pre_star (accepts A) (p,v) \<le> weight_pre_star (accepts (K$ 0)) (p, v)"
    using weight_pre_star_accepts_lt_weight_pre_star_accepts_K0 by auto
  also have "... \<le> accepts A' (p, v)"
    using lemma_3_2_w_alternative soundA' by auto
  finally show ?thesis
    by auto
qed
lemma lemma_3_2_w_alternative': 
  assumes "pre_star_rule (K$ 0) A"
  shows "accepts A pv \<ge> weight_pre_star (accepts (K$ 0)) pv"
  using lemma_3_2_w_alternative[OF pre_star_rule_sound[OF sound_empty assms]] by auto

lemma lemma_3_2_w_alternative''':
  assumes "pre_star_rule\<^sup>*\<^sup>* (K$ 0) A'"
  shows "accepts A' (p,v) \<ge> weight_pre_star (accepts (K$ 0)) (p,v)"
  using pre_star_rule_rtranclp_sound assms lemma_3_2_w_alternative sound_empty by blast

lemma lemma_3_2_w_alternative'_BONUS: 
  assumes soundA': "sound A'"
  assumes "pre_star_rule A' A''"
  shows "accepts A'' (p,v) \<ge> weight_pre_star (accepts A) (p,v)"
proof -
  have sA'': "sound A''"
    using pre_star_rule_sound soundA' assms(2) by auto
  have "weight_pre_star (accepts A) (p, v) \<le> weight_pre_star (accepts (K$ 0)) (p, v)"
    using weight_pre_star_accepts_lt_weight_pre_star_accepts_K0 by auto
  also have "... \<le> accepts A'' (p,v)"
    using lemma_3_2_w_alternative sA'' by auto
  finally show "accepts A'' (p,v) \<ge> weight_pre_star (accepts A) (p,v)"
    by auto
qed

lemma weight_pre_star_leq':
   "X c \<ge> weight_pre_star X c"
proof -
  have "weight_pre_star X c = \<^bold>\<Sum> {l * X c' |l c'. c \<Midarrow> l \<Rightarrow>\<^sup>* c'}"
    unfolding weight_pre_star_def by auto
  also have "... \<le> \<^bold>\<Sum> {l * X c |l. c \<Midarrow> l \<Rightarrow>\<^sup>* c}"
    by (smt (verit) Collect_mono Suminf_mono)
  also have "... \<le> \<^bold>\<Sum> {1 * X c}"
    by (smt (verit, del_insts) bot.extremum insert_subsetI Suminf_mono mem_Collect_eq 
        monoid_rtranclp.monoid_rtrancl_refl)
  also have "... \<le> 1 * X c" 
    by simp
  also have "... \<le> X c" 
    by simp
  finally show ?thesis 
    by auto
qed

lemma weight_pre_star_leq: (* Nice. But we don't use it. *)
  "X \<ge> weight_pre_star X"
  by (simp add: le_fun_def weight_pre_star_leq')

lemma weight_pre_star_dom_fixedpoint':
  "weight_pre_star (weight_pre_star C) c = (weight_pre_star C) c"
proof -
  have "weight_pre_star (weight_pre_star C) c =
          \<^bold>\<Sum> {l * \<^bold>\<Sum> {l' * C c'' |l' c''. c' \<Midarrow> l' \<Rightarrow>\<^sup>* c''} |l c'. c \<Midarrow> l \<Rightarrow>\<^sup>* c'}"
    unfolding weight_pre_star_def by meson
  also
  have "... =  \<^bold>\<Sum> {\<^bold>\<Sum> {l * l' * C c'' |l' c''. c' \<Midarrow> l' \<Rightarrow>\<^sup>* c''} |l c'. c \<Midarrow> l \<Rightarrow>\<^sup>* c'}"
  proof -
    {
      fix l c'
      have "l * \<^bold>\<Sum> {l' * C c'' |l' c''. c' \<Midarrow> l' \<Rightarrow>\<^sup>* c''} =
              \<^bold>\<Sum> {l * l' * C c'' |l' c''. c' \<Midarrow> l' \<Rightarrow>\<^sup>* c''}"
        using sum_distr[of l "{l' * C c'' |l' c''. c' \<Midarrow> l' \<Rightarrow>\<^sup>* c''}"]
         mult.assoc by (smt (verit) Collect_cong mem_Collect_eq)
    }
    then show ?thesis
      by auto
  qed
  also
  have "... = \<^bold>\<Sum> {l * l' * C c'' |l' c'' l c'. c' \<Midarrow> l' \<Rightarrow>\<^sup>* c'' \<and> c \<Midarrow> l \<Rightarrow>\<^sup>* c'}"
    using sum_of_sums2[of
        "\<lambda>(l',c'') (l,c'). l * l' * C c''"
        "\<lambda>(l',c'') (l,c').  c' \<Midarrow> l' \<Rightarrow>\<^sup>* c''"
        "\<lambda>(l,c'). c \<Midarrow> l \<Rightarrow>\<^sup>* c'"] by auto
  also
  have "... = \<^bold>\<Sum> {l * l' * C c'' |l' c'' l c'. c \<Midarrow> l \<Rightarrow>\<^sup>* c' \<and> c' \<Midarrow> l' \<Rightarrow>\<^sup>* c''}"
    by meson
  also
  have "... = \<^bold>\<Sum> {l'' * C c'' |l'' c''. c \<Midarrow> l'' \<Rightarrow>\<^sup>* c''}"
    by (smt (verit, ccfv_threshold) Collect_cong monoid_rtranclp.monoid_rtrancl_refl monoid_rtranclp_trans mult_1)
  also
  have "... = (weight_pre_star C) c"
    by (simp add: weight_pre_star_def)
  finally
  show "?thesis"
    .
qed

lemma weight_pre_star_dom_fixedpoint: (* Nice. But we don't use it. *)
  "weight_pre_star (weight_pre_star C) = (weight_pre_star C)"
  using weight_pre_star_dom_fixedpoint' by auto

lemma lemma_3_2_w_alternative'''_BONUS:
  assumes soundA': "sound A'"
  assumes "pre_star_rule\<^sup>*\<^sup>* A' A''"
  shows "accepts A'' (p,v) \<ge> weight_pre_star (accepts A) (p,v)"
proof -
  have sA'': "sound A''"
    using pre_star_rule_rtranclp_sound soundA' assms(2) by auto
  have "weight_pre_star (accepts A) (p, v) \<le> weight_pre_star (accepts (K$ 0)) (p, v)"
    using weight_pre_star_accepts_lt_weight_pre_star_accepts_K0 by auto
  also have "... \<le> accepts A'' (p,v)"
    using lemma_3_2_w_alternative sA'' by auto
  finally show "accepts A'' (p,v) \<ge> weight_pre_star (accepts A) (p,v)"
    by auto
qed

(* End superfluous lemmas *)

lemma step_relp_NISSE:
  "(p, \<gamma>w') \<Midarrow>d\<Rightarrow> (p',ww') \<Longrightarrow> (\<exists>\<gamma> w' w. \<gamma>w' = \<gamma>#w' \<and> ww' = (lbl w)@w' \<and> (p, \<gamma>) \<midarrow>d\<hookrightarrow> (p', w))"
  by (meson step_relp_def2)


lemma nicenicenice:
  assumes "saturated pre_star_rule A"
  assumes "((p, \<gamma>) \<midarrow>d\<hookrightarrow> (p', w))"
  assumes "(p', (lbl w, d'), q) \<in> monoid_rtrancl (wts_to_monoidLTS A)"
  assumes "(A $ (p, \<gamma>, q)) = d''"
  shows "(d'' + (d * d')) = d''"
  using assms unfolding saturated_def using pre_star_rule.intros by blast

lemma nicenicenice''':
  assumes "saturated pre_star_rule A"
  assumes "((p, \<gamma>) \<midarrow>d\<hookrightarrow> (p', w))"
  assumes "(p', (lbl w, d'), q) \<in> monoid_rtrancl (wts_to_monoidLTS A)"
  assumes "(A $ (p, \<gamma>, q)) = d''"
  shows "d * d' \<ge> d''"
  by (metis assms meet.inf.absorb_iff2 meet.inf_commute nicenicenice)

lemma nicenicenice''''':
  assumes "saturated pre_star_rule A"
  assumes "((p, \<gamma>) \<midarrow>d\<hookrightarrow> (p', w))"
  assumes "(p', (lbl w, d'), q) \<in> monoid_rtrancl (wts_to_monoidLTS A)"
  shows "d * d' \<ge> (A $ (p, \<gamma>, q))"
  by (metis assms meet.inf.absorb_iff2 meet.inf_commute nicenicenice)

lemma nicenicenice0:
  assumes "saturated pre_star_rule A"
  assumes "((p, \<gamma>) \<midarrow>d\<hookrightarrow> (p', w))"
  assumes "(p', (lbl w, d'), q) \<in> monoid_rtrancl (wts_to_monoidLTS A)"
  assumes "(A $ (p, \<gamma>, q)) = 0"
  shows "d * d' = 0"
  using assms unfolding saturated_def using pre_star_rule.intros
  using meet.inf_eq_top_iff by blast 


lemma "(b :: 'weight) \<ge> a \<Longrightarrow> c \<ge> a \<Longrightarrow> d \<ge> a \<Longrightarrow> b + c + d \<ge> a"
  by simp

lemma sum_AAA:
  assumes inf_d: "\<forall>x \<in> X. x \<ge> d"
  shows "\<^bold>\<Sum> X \<ge> d"
proof -
  have countableX:"countable X" sorry 
      \<comment> \<open>TODO: This should be in assumption. How do we easily show that all the sets we deal with are countable? \<close>

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

lemma nicenicenice'''':
  assumes "saturated pre_star_rule A"
  assumes "((p, \<gamma>) \<midarrow>d\<hookrightarrow> (p', w))"
  assumes "(A $ (p, \<gamma>, q)) = d''"
  shows "d * \<^bold>\<Sum>{d'. (p', (lbl w, d'), q) \<in> monoid_rtrancl (wts_to_monoidLTS A)} \<ge> d''"
proof -
  have "\<forall>dd\<in>{d'| d'. (p', (lbl w, d'), q) \<in> monoid_rtrancl (wts_to_monoidLTS A)}. d * dd \<ge> d''"
    using assms(1) assms(2,3) nicenicenice''' by force 
  then show ?thesis
    by (smt (verit, del_insts) mem_Collect_eq sum_AAA sum_distr)
qed

lemma nicenicenice'''''':
  assumes "saturated pre_star_rule A"
  assumes "(A $ (p, \<gamma>, q)) = d''"
  shows "\<^bold>\<Sum>{d * d'| d d' p' w. ((p, \<gamma>) \<midarrow>d\<hookrightarrow> (p', w)) \<and> (p', (lbl w, d'), q) \<in> monoid_rtrancl (wts_to_monoidLTS A)} \<ge> d''"
proof -
  have "\<forall>dd\<in>{d * d'| d d' p' w. ((p, \<gamma>) \<midarrow>d\<hookrightarrow> (p', w)) \<and> (p', (lbl w, d'), q) \<in> monoid_rtrancl (wts_to_monoidLTS A)}. dd \<ge> d''"
    using assms(1) assms(2) nicenicenice''' by force
  then show ?thesis
    by (smt (verit) dual_order.order_iff_strict empty_iff less_eq_zero less_le_not_le sum_AAA SumInf_empty)
qed

lemma
  assumes "(a ::'weight) \<le> (b :: 'weight)"
  assumes "\<not>(a\<ge>b)"
  shows "a < b"
  using assms(1) assms(2) less_le_not_le by blast

lemma "(a :: 'weight) \<le> 0"
  by simp

lemma 
  assumes "(p\<^sub>1,(\<gamma>\<^sub>1\<^sub>2 # w\<^sub>2\<^sub>3,d\<^sub>1\<^sub>3),p\<^sub>3) \<in> monoid_rtrancl (wts_to_monoidLTS A)"
  shows "\<exists>p\<^sub>2 d\<^sub>1\<^sub>2 d\<^sub>2\<^sub>3. (p\<^sub>1, ([\<gamma>\<^sub>1\<^sub>2],d\<^sub>1\<^sub>2), p\<^sub>2) \<in> (wts_to_monoidLTS A) \<and>
                    (p\<^sub>2,(w\<^sub>2\<^sub>3,d\<^sub>2\<^sub>3),p\<^sub>3) \<in> monoid_rtrancl (wts_to_monoidLTS A) \<and> d\<^sub>1\<^sub>3 = d\<^sub>1\<^sub>2*d\<^sub>2\<^sub>3"
  using assms monoid_rtrancl_wts_to_monoidLTS_cases_rev by fastforce

(* Proof adapted from monoid_rtrancl_list_embed_ts_append_split *)
lemma monoid_rtrancl_wts_to_monoidLTS_append_split:
  assumes "(p, (d'@l,d), p') \<in> monoid_rtrancl (wts_to_monoidLTS A)"
  shows "\<exists>d'' s d'''.
           (p, (d',d''), s) \<in> monoid_rtrancl (wts_to_monoidLTS A) \<and>
           (s, (l,d'''), p') \<in> monoid_rtrancl (wts_to_monoidLTS A) \<and>
           d = d'' * d'''"
using assms proof(induction d' arbitrary: p d)
  case Nil
  then show ?case
    by (metis eq_Nil_appendI monoid_rtrancl.monoid_rtrancl_refl mult_1 one_list_def one_prod_def) 
next
  case (Cons a u1)
  then have "\<exists>du0 q du1. (p, ([a],du0), q) \<in> (wts_to_monoidLTS A) \<and> 
                         (q, ( u1 @ l,du1), p') \<in> monoid_rtrancl (wts_to_monoidLTS A) \<and> 
                         d = du0 * du1"
    using monoid_rtrancl_wts_to_monoidLTS_cases_rev by fastforce
  then obtain q du0 du1 where e:
    "(p, ([a],du0), q) \<in> (wts_to_monoidLTS A)" 
    "(q, (u1 @ l,du1), p') \<in> monoid_rtrancl (wts_to_monoidLTS A)" 
    "d = du0 * du1"
    by auto

  have "\<exists>d'' s d'''. (q, (u1, d''), s) \<in> monoid_rtrancl (wts_to_monoidLTS A) \<and> 
                     (s, (l, d'''), p') \<in> monoid_rtrancl (wts_to_monoidLTS A) \<and> 
                     du1 = d'' * d'''"
     using Cons.IH[OF e(2)] .
  then obtain d'' s d''' where
    "(q, (u1,d''), s) \<in> monoid_rtrancl (wts_to_monoidLTS A)"
    "(s, (l,d'''), p') \<in> monoid_rtrancl (wts_to_monoidLTS A)" 
    "du1 = d'' * d'''"
    by auto
  then have "(p, (a # u1, du0 * d''), s) \<in> monoid_rtrancl (wts_to_monoidLTS A)"
    by (smt (verit, del_insts) append_Cons 
        append_Nil e(1) fst_conv monoid_rtrancl_into_rtrancl_rev mult_prod_def snd_conv 
        times_list_def)
  then show ?case
    by (metis (no_types, lifting) \<open>(s, (l, d'''), p') \<in> monoid_rtrancl (wts_to_monoidLTS A)\<close> 
        \<open>du1 = d'' * d'''\<close> e(3)  mult.assoc)   
qed

lemma the_lemma_that:
  assumes "A $ (p\<^sub>1, \<gamma>\<^sub>1\<^sub>2, p\<^sub>2) \<le> D\<^sub>1\<^sub>2"
  assumes "(p\<^sub>2, (w\<^sub>2\<^sub>3, d\<^sub>2\<^sub>3), p\<^sub>3) \<in> monoid_rtrancl (wts_to_monoidLTS A)"
  shows "\<exists>D\<^sub>1\<^sub>3. (p\<^sub>1, (\<gamma>\<^sub>1\<^sub>2 # w\<^sub>2\<^sub>3, D\<^sub>1\<^sub>3), p\<^sub>3) \<in> monoid_rtrancl (wts_to_monoidLTS A) \<and> D\<^sub>1\<^sub>3 \<le> D\<^sub>1\<^sub>2 * d\<^sub>2\<^sub>3"
proof -
  define d\<^sub>1\<^sub>2 where "d\<^sub>1\<^sub>2 = A $ (p\<^sub>1, \<gamma>\<^sub>1\<^sub>2, p\<^sub>2)"

  have e: "(p\<^sub>1, ([\<gamma>\<^sub>1\<^sub>2], d\<^sub>1\<^sub>2), p\<^sub>2) \<in> (wts_to_monoidLTS A)"
    using assms(1) d\<^sub>1\<^sub>2_def wts_to_monoidLTS_def by fastforce

  have "(p\<^sub>1, ([\<gamma>\<^sub>1\<^sub>2], d\<^sub>1\<^sub>2) * (w\<^sub>2\<^sub>3, d\<^sub>2\<^sub>3), p\<^sub>3) \<in> monoid_rtrancl (wts_to_monoidLTS A)"
    using monoid_rtrancl_into_rtrancl_rev[OF _ assms(2), of p\<^sub>1 "([\<gamma>\<^sub>1\<^sub>2],_)", OF e] .
  then have "(p\<^sub>1, (\<gamma>\<^sub>1\<^sub>2#w\<^sub>2\<^sub>3, d\<^sub>1\<^sub>2 * d\<^sub>2\<^sub>3), p\<^sub>3) \<in> monoid_rtrancl (wts_to_monoidLTS A)"
    by (simp add: mult_prod_def times_list_def)
  then show ?thesis
    using assms(1) d\<^sub>1\<^sub>2_def idempotent_semiring_ord_class.mult_isol_var by blast
qed

lemma c''_weak: (* Dette er Mortens tegning. *)
  assumes "(p', \<gamma>) \<midarrow>d\<hookrightarrow> (p'', u1)"
      and "saturated pre_star_rule A"
      and "(p'',((lbl u1) @ w1,d'),q) \<in> monoid_rtrancl (wts_to_monoidLTS A)"
    shows "(\<exists>D. (p',(\<gamma> # w1, D), q) \<in> monoid_rtrancl (wts_to_monoidLTS A) \<and> D \<le> d*d') \<or> 
             (\<nexists>D. (p',(\<gamma> # w1, D), q) \<in> monoid_rtrancl (wts_to_monoidLTS A))"
proof -
  obtain q1 d1 d2 where e:
    "(p'', ((lbl u1),d1), q1) \<in> monoid_rtrancl (wts_to_monoidLTS A)"
    "(q1,(w1,d2),q) \<in> monoid_rtrancl (wts_to_monoidLTS A)"
    "d' = d1*d2"
    using monoid_rtrancl_wts_to_monoidLTS_append_split[OF assms(3)] by auto

  show ?thesis
  proof (cases "\<nexists>D. (p',(\<gamma> # w1, D), q) \<in> monoid_rtrancl (wts_to_monoidLTS A)")
    case True
    then show ?thesis
      by auto
  next
    case False
    have "A $ (p', \<gamma>, q1) \<le> d * d1"
      using nicenicenice'''''[OF assms(2) assms(1) e(1)] by auto
    then have "\<exists>D. (p', (\<gamma>#w1,D),q) \<in> monoid_rtrancl (wts_to_monoidLTS A) \<and> D \<le> d*d1*d2"
      using the_lemma_that e(2) False by (metis dual_order.eq_iff less_eq_zero mult_not_zero)
    then show ?thesis
      by (simp add: e(3) mult.assoc)
  qed
qed

lemma c''_SHORT: (* Dette er Mortens tegning. *)
  assumes "(p', \<gamma>) \<midarrow>d\<hookrightarrow> (p'', u1)"
    and "saturated pre_star_rule A"
    and "(p'',((lbl u1),d'),q) \<in> monoid_rtrancl (wts_to_monoidLTS A)"
    (*      and "q \<in> finals" (*Er denne linje nødvendig? *) *)
  shows "\<exists>D. (p',([\<gamma>], D), q) \<in> monoid_rtrancl (wts_to_monoidLTS A) \<and> D \<le> d*d'" (* A phrasing from the wts perspective would also be possible and maybe better? *)
proof -
  have e:
    "(p'', ((lbl u1),d'), q) \<in> monoid_rtrancl (wts_to_monoidLTS A)"
    using monoid_rtrancl_wts_to_monoidLTS_append_split using assms(3) by auto

  have "A $ (p', \<gamma>, q) \<le> d * d'"
    using nicenicenice'''''[OF assms(2) assms(1) e(1)] by auto
  then have "\<exists>D. (p', ([\<gamma>],D),q) \<in> monoid_rtrancl (wts_to_monoidLTS A) \<and> D \<le> d*d'"
    using the_lemma_that using e monoid_rtrancl_wts_to_monoidLTS_refl by fastforce
  then show ?thesis
    by (simp add: mult.assoc)
qed

lemma c'': (* Dette er Mortens tegning. *) (* Change this one to rely on c''_SHORT *)
  assumes "(p', \<gamma>) \<midarrow>d\<hookrightarrow> (p'', u1)"
    and "saturated pre_star_rule A"
    and "(p'',((lbl u1) @ w1,d'),q) \<in> monoid_rtrancl (wts_to_monoidLTS A)"
    (*      and "q \<in> finals" (*Er denne linje nødvendig? *) *)
  shows "\<exists>D. (p',(\<gamma> # w1, D), q) \<in> monoid_rtrancl (wts_to_monoidLTS A) \<and> D \<le> d*d'"
proof -
  obtain q1 d1 d2 where e:
    "(p'', ((lbl u1),d1), q1) \<in> monoid_rtrancl (wts_to_monoidLTS A)"
    "(q1,(w1,d2),q) \<in> monoid_rtrancl (wts_to_monoidLTS A)"
    "d' = d1*d2"
    using monoid_rtrancl_wts_to_monoidLTS_append_split[OF assms(3)] by auto


  have "A $ (p', \<gamma>, q1) \<le> d * d1"
    using nicenicenice'''''[OF assms(2) assms(1) e(1)] by auto
  then have "\<exists>D. (p', (\<gamma>#w1,D),q) \<in> monoid_rtrancl (wts_to_monoidLTS A) \<and> D \<le> d*d1*d2"
    using the_lemma_that e(2) by metis
  then show ?thesis
    by (simp add: e(3) mult.assoc)
qed

lemma c''bububub: (* lkjjlkjkl. *)
  assumes "(p', \<gamma>) \<midarrow>d\<hookrightarrow> (p'', u1)"
    and "saturated pre_star_rule A"
  shows "accepts A (p',(\<gamma> # w1)) \<le> d * accepts A (p'', (lbl u1) @ w1)"
proof -
  have X: "\<^bold>\<Sum> {d' | d' q. q \<in> finals \<and> (p', (\<gamma> # w1, d'), q) \<in> monoid_rtrancl (wts_to_monoidLTS A)} \<le>
         \<^bold>\<Sum> {d * d'| d' q. q \<in> finals \<and> (p'', (lbl u1 @ w1, d'), q) \<in> monoid_rtrancl (wts_to_monoidLTS A)}"
    using c''[OF assms(1) assms(2), of w1 ] using mem_Collect_eq order_trans_rules(23) sum_AAA geq_Suminf_if_member
    by (smt (verit, ccfv_threshold)) 
  also have Y: "... \<le> d * \<^bold>\<Sum> {d' | d' q. q \<in> finals \<and> (p'', (lbl u1 @ w1, d'), q) \<in> monoid_rtrancl (wts_to_monoidLTS A)}"
    by (simp add: sum_distr)

  show ?thesis
    using Y accepts_def calculation by force
qed

lemma c''bubububjdfkjdkf: (* lkjjlkjkl. *)
  assumes "(p', w) \<Midarrow>d\<Rightarrow> (p'', u)"
      and "saturated pre_star_rule A"
    shows "accepts A (p',w) \<le> d * accepts A (p'', u)"
  using assms(1) assms(2) c''bububub step_relp_NISSE by blast

lemma c'_attempt2:
  assumes "saturated pre_star_rule A"
  assumes "c \<Midarrow>l\<Rightarrow>\<^sup>* c'" and "fst c' \<in> finals" and "snd c' = []"
  shows "accepts A c \<le> l"
  using assms(2,3,4)
proof (induction rule: monoid_star_relp_induct_rev)
  case (monoid_star_refl c)
  then show ?case
    by (metis dual_order.eq_iff accept_is_one_if_final_empty prod.exhaust_sel)
next
  case (monoid_star_into_rtrancl p'w d p''u c d')
  then have 2: "accepts A p''u \<le> d'" (* 2 *)
    by auto
  define p' where "p' = fst p'w"
  define w where "w = snd p'w"
  define p'' where "p'' = fst p''u"
  define u where "u = snd p''u"
  have p''u_split: "p''u = (p'',u)"
    using p''_def u_def by auto
  have p'w_split: "p'w = (p',w)"
    using p'_def w_def by auto

  show ?case
    using "2" assms(1) c''bubububjdfkjdkf idempotent_semiring_ord_class.mult_isol 
      monoid_star_into_rtrancl.hyps(1) order_trans p''u_split p'w_split by blast
qed

lemma c':
  assumes "saturated pre_star_rule A"
  assumes "c \<Midarrow>l\<Rightarrow>\<^sup>* c'" and "fst c' \<in> finals" and "snd c' = []"
  shows "accepts A c \<le> l"
  using assms(2,3,4)
proof (induction rule: monoid_star_relp_induct_rev)
  case (monoid_star_refl c)
  then show ?case
    by (metis dual_order.eq_iff accept_is_one_if_final_empty prod.exhaust_sel)
next
  case (monoid_star_into_rtrancl p'w d p''u c d')
  then have 2: "accepts A p''u \<le> d'" (* 2 *)
    by auto
  define p' where "p' = fst p'w"
  define w where "w = snd p'w"
  define p'' where "p'' = fst p''u"
  define u where "u = snd p''u"
  have p''u_split: "p''u = (p'',u)"
    using p''_def u_def by auto
  have p'w_split: "p'w = (p',w)"
    using p'_def w_def by auto

  from monoid_star_into_rtrancl(1) obtain \<gamma> u1 w1 where 3: (* 3 *)
     "w = \<gamma>#w1"
     "u = (lbl u1)@w1"
     "(p',\<gamma>) \<midarrow>d\<hookrightarrow> (p'',u1)"
    using p''u_split p'w_split step_relp_NISSE by blast
 
  have "\<^bold>\<Sum> {d' | d' q. q \<in> finals \<and> (p', (\<gamma> # w1, d'), q) \<in> monoid_rtrancl (wts_to_monoidLTS A)} \<le>
         \<^bold>\<Sum> {d * d'| d' q. q \<in> finals \<and> (p'', (lbl u1 @ w1, d'), q) \<in> monoid_rtrancl (wts_to_monoidLTS A)}"
    using c''[OF 3(3) assms(1), of w1 ] using mem_Collect_eq order_trans_rules(23) sum_AAA geq_Suminf_if_member
    by (smt (verit, ccfv_threshold))
  also have "... \<le> d * \<^bold>\<Sum> {d' | d' q. q \<in> finals \<and> (p'', (lbl u1 @ w1, d'), q) \<in> monoid_rtrancl (wts_to_monoidLTS A)}"
    by (simp add: sum_distr)

  also have "... \<le> d * d'"
    using 2 unfolding p''u_split 3(2) accepts_def using BoundedDioid.mult_isol by auto

  finally show ?case
    unfolding p'w_split 3(1)
    unfolding accepts_def by simp
qed

lemma c:
  assumes "saturated pre_star_rule A"
  assumes "c \<Midarrow>l\<Rightarrow>\<^sup>* c'" and "c' = (p,[])" and "p \<in> finals"
  shows "accepts A c \<le> l"
  using c' assms by simp 

lemma b:
  assumes "saturated pre_star_rule A"
  assumes "c \<Midarrow>l\<Rightarrow>\<^sup>* c'"
  shows "accepts A c \<le> l * accepts (K$ 0) c'"
  using assms c[OF assms(1)] accepts_K0_iff[of "fst c'" "snd c'"] 
  by simp (metis prod.collapse)

lemma
  assumes "saturated pre_star_rule A"
  shows "accepts A c \<le> weight_pre_star (accepts (K$ 0)) c"
  unfolding weight_pre_star_def
  using sum_AAA[of "{l * accepts (K$ 0) c' |l c'. c \<Midarrow> l \<Rightarrow>\<^sup>* c'}" "accepts A c"] b[OF assms]
  by blast

end

end
