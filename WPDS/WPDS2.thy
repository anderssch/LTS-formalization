theory WPDS2
  imports "LTS" "Saturation" "FinFunWellFounded" "WAutomaton"
begin

datatype 'label operation = pop | swap 'label | push 'label 'label
\<comment> \<open>WPDS has a @{typ "'weight::bounded_idempotent_semiring"} on the rule.\<close>
type_synonym ('ctr_loc, 'label, 'weight) rule = "('ctr_loc \<times> 'label) \<times> 'weight \<times> ('ctr_loc \<times> 'label operation)"
type_synonym ('ctr_loc, 'label) conf = "'ctr_loc \<times> 'label list"

locale WPDS =
  fixes \<Delta> :: "('ctr_loc::enum, 'label::finite, 'weight::bounded_idempotent_semiring) rule set"
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

lemma step_relp_elim2:
  "(p, \<gamma>w') \<Midarrow>d\<Rightarrow> (p',ww') \<Longrightarrow> (\<exists>\<gamma> w' w. \<gamma>w' = \<gamma>#w' \<and> ww' = (lbl w)@w' \<and> (p, \<gamma>) \<midarrow>d\<hookrightarrow> (p', w))"
  by (meson step_relp_def2)

end


lemma WPDS_transition_rel_mono:
  assumes "finite Y"
  assumes "X \<subseteq> Y"
  assumes "((a,b),c,(d,e)) \<in> WPDS.transition_rel X"
  shows "((a,b),c,(d,e)) \<in> WPDS.transition_rel Y"
proof -
  have WPDSx:"WPDS X" unfolding WPDS_def using finite_subset[OF assms(2,1)] by simp
  have WPDSy:"WPDS Y" unfolding WPDS_def using assms(1) by simp
  have "\<And>a b c d e. WPDS.is_rule X (a, b) c (d, e) \<Longrightarrow> WPDS.is_rule Y (a, b) c (d, e)"
    using assms(2) unfolding WPDS.is_rule_def[OF WPDSy] WPDS.is_rule_def[OF WPDSx] by blast
  then show ?thesis 
    using assms(3) WPDS.transition_rel.intros[OF WPDSy]
    by (cases rule: WPDS.transition_rel.cases[OF WPDSx assms(3)]) force
qed

lemma WPDS_LTS_mono:
  assumes "finite Y"
  assumes "X \<subseteq> Y"
  shows "monoid_rtrancl (WPDS.transition_rel X) \<subseteq> monoid_rtrancl (WPDS.transition_rel Y)"
  using WPDS_transition_rel_mono[OF assms] 
  apply safe
  subgoal for a b c d e
    using mono_monoid_rtrancl[of "WPDS.transition_rel X" "WPDS.transition_rel Y" "(a,b)" c "(d,e)"]
    by fast
  done


\<comment> \<open>Generalization of PDS_with_P_automata.accepts that computes the meet-over-all-paths in the W-automaton.\<close>
definition (in dioidLTS) accepts :: "('ctr_loc, 'label, 'weight) w_transitions \<Rightarrow> 'ctr_loc set \<Rightarrow> ('ctr_loc, 'label) conf \<Rightarrow> 'weight" where
  "accepts ts finals \<equiv> \<lambda>(p,w). (\<^bold>\<Sum>{d | d q. q \<in> finals \<and> (p,(w,d),q) \<in> monoid_rtrancl (wts_to_monoidLTS ts)})"

context WPDS
begin

interpretation dioidLTS transition_rel proof
  show "countable transition_rel" by (fact countable_transition_rel)
qed 
notation step_relp (infix "\<Rightarrow>" 80)
notation step_starp (infix "\<Rightarrow>\<^sup>*" 80)
notation l_step_relp ("(_)/ \<Midarrow> (_)/ \<Rightarrow> (_)/" [70,70,80] 80)
notation monoid_star_relp ("(_)/ \<Midarrow> (_)/ \<Rightarrow>\<^sup>* (_)/" [90,90,100] 100) 

(*
\<comment> \<open>Generalization of PDS_with_P_automata.accepts that computes the meet-over-all-paths in the W-automaton.\<close>
definition accepts :: "('ctr_loc, 'label, 'weight) w_transitions \<Rightarrow> ('ctr_loc, 'label) conf \<Rightarrow> 'weight" where
  "accepts ts \<equiv> \<lambda>(p,w). (\<^bold>\<Sum>{d | d q. q \<in> finals \<and> (p,(w,d),q) \<in> monoid_rtrancl (wts_to_monoidLTS ts)})"
*)
lemma accepts_def2:
  "accepts ts finals (p,w) = (\<^bold>\<Sum>{d | d q. q \<in> finals \<and> (p,(w,d),q) \<in> monoid_rtrancl (wts_to_monoidLTS ts)})"
  using accepts_def[of ts finals] by auto

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
  shows "accepts A finals = weight_pre_star (accepts (ts_to_wts {}) finals)"
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
  by (metis finfun_upd_apply_other finfun_upd_apply_same prod.inject)

abbreviation (input) push_seq_weight :: "('ctr_loc * 'label list) \<Rightarrow> 'ctr_loc \<Rightarrow> 'weight" ("\<^bold>\<Sigma>_\<Rightarrow>\<^sup>*_") where
  "(\<^bold>\<Sigma>pw\<Rightarrow>\<^sup>*p') \<equiv> \<^bold>\<Sum>{d'. pw \<Midarrow>d'\<Rightarrow>\<^sup>* (p',[])}"

lemma push_seq_weight_def2:
  "(\<^bold>\<Sigma>pw\<Rightarrow>\<^sup>*p') = \<^bold>\<Sum> {d |d. pw \<Midarrow> d \<Rightarrow>\<^sup>* (p', [])}"
  by auto

lemma countable_monoid_star_all_triple: "countable {(d', q, w). (p, v) \<Midarrow> d' \<Rightarrow>\<^sup>* (q, w)}"
  by (auto simp: dissect_set countable_monoid_star_variant1)

lemma countable_push_seq_weight:
  "countable {d |d. pw \<Midarrow> d \<Rightarrow>\<^sup>* (p', [])}"
  using countable_star_f_p9 .

lemma countable_push_seq_weight_variant1: "countable {(d', q). (p, v) \<Midarrow> d' \<Rightarrow>\<^sup>* (q, [])}"
proof -
  have "countable {(l, c'). (p, v) \<Midarrow> l \<Rightarrow>\<^sup>* c'}"
    using countable_monoid_star_all(3)[of "(p,v)"]
    by auto
  then have "countable ((\<lambda>(l, c'). (l, fst c')) ` ({(l, c'). snd c' = []} \<inter> {(l, c'). (p, v) \<Midarrow> l \<Rightarrow>\<^sup>* c'}))"
    by auto
  then show ?thesis
    unfolding image_def Int_def using Collect_mono_iff countable_subset by fastforce
qed

lemmas countable_monoid_star_all = 
  countable_monoid_star_all countable_push_seq_weight countable_monoid_star_all_triple 
  countable_push_seq_weight_variant1

lemma countable_push_seq_weight2: (* maybe not a good name *)
  "countable {d'| d' q. P q d' \<and> (p, v) \<Midarrow> d' \<Rightarrow>\<^sup>* (q, [])}"
  unfolding setcompr_eq_image2 by (auto simp add: dissect_set countable_monoid_star_all)

lemma countable_push_seq_weight3: (* maybe not a good name *)
  "countable {f d' q w| d' q w. (p, v) \<Midarrow> d' \<Rightarrow>\<^sup>* (q, w)}"
  by (auto simp add: dissect_set countable_monoid_star_all)

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
    define w\<^sub>1\<^sub>3 where "w\<^sub>1\<^sub>3 = (fst w\<^sub>1\<^sub>3d\<^sub>1\<^sub>3)"
    define d\<^sub>1\<^sub>3 where "d\<^sub>1\<^sub>3 = (snd w\<^sub>1\<^sub>3d\<^sub>1\<^sub>3)"
    define w\<^sub>3\<^sub>4 where "w\<^sub>3\<^sub>4 = fst w\<^sub>3\<^sub>4d\<^sub>3\<^sub>4"
    define d\<^sub>3\<^sub>4 where "d\<^sub>3\<^sub>4 = snd w\<^sub>3\<^sub>4d\<^sub>3\<^sub>4"
    define w\<^sub>2\<^sub>4 where "w\<^sub>2\<^sub>4 = w\<^sub>2\<^sub>3 @ w\<^sub>3\<^sub>4"
    have w\<^sub>3\<^sub>4d\<^sub>3\<^sub>4_split: "w\<^sub>3\<^sub>4d\<^sub>3\<^sub>4 = (w\<^sub>3\<^sub>4,d\<^sub>3\<^sub>4)"
      by (simp add: d\<^sub>3\<^sub>4_def w\<^sub>3\<^sub>4_def)

    have w24_tl: "w\<^sub>2\<^sub>4 = tl (fst (w\<^sub>1\<^sub>3d\<^sub>1\<^sub>3 * w\<^sub>3\<^sub>4d\<^sub>3\<^sub>4))"
      by (simp add: local.Cons mult_prod_def times_list_def w\<^sub>2\<^sub>4_def w\<^sub>3\<^sub>4_def)

    have "w\<^sub>1\<^sub>3d\<^sub>1\<^sub>3 = (\<gamma>\<^sub>1\<^sub>2 # w\<^sub>2\<^sub>3, d\<^sub>1\<^sub>3)"
      using Cons by (metis d\<^sub>1\<^sub>3_def surjective_pairing) 

    then have "(\<exists>p\<^sub>2 d\<^sub>2\<^sub>3 d\<^sub>1\<^sub>2.
                   w\<^sub>1\<^sub>3d\<^sub>1\<^sub>3 = (\<gamma>\<^sub>1\<^sub>2 # w\<^sub>2\<^sub>3, d\<^sub>1\<^sub>3) \<and>
                   (p\<^sub>1, ([\<gamma>\<^sub>1\<^sub>2], d\<^sub>1\<^sub>2), p\<^sub>2) \<in> wts_to_monoidLTS ts \<and> 
                   (p\<^sub>2, (w\<^sub>2\<^sub>3, d\<^sub>2\<^sub>3), p\<^sub>3) \<in> monoid_rtrancl (wts_to_monoidLTS ts) \<and> 
                   d\<^sub>1\<^sub>3 = d\<^sub>1\<^sub>2 * d\<^sub>2\<^sub>3)"
      using monoid_rtrancl_into_rtrancl.IH by auto
    then obtain p\<^sub>2 d\<^sub>2\<^sub>3 d\<^sub>1\<^sub>2 where p\<^sub>2_d\<^sub>2\<^sub>3_d\<^sub>1\<^sub>2_p:
      "w\<^sub>1\<^sub>3d\<^sub>1\<^sub>3 = (\<gamma>\<^sub>1\<^sub>2 # w\<^sub>2\<^sub>3, d\<^sub>1\<^sub>3)"
      "(p\<^sub>1, ([\<gamma>\<^sub>1\<^sub>2], d\<^sub>1\<^sub>2), p\<^sub>2) \<in> wts_to_monoidLTS ts"
      "(p\<^sub>2, (w\<^sub>2\<^sub>3, d\<^sub>2\<^sub>3), p\<^sub>3) \<in> monoid_rtrancl (wts_to_monoidLTS ts)"
      "d\<^sub>1\<^sub>3 = d\<^sub>1\<^sub>2 * d\<^sub>2\<^sub>3"
      using d\<^sub>1\<^sub>3_def Cons by auto

    define d\<^sub>2\<^sub>4 where "d\<^sub>2\<^sub>4 = d\<^sub>2\<^sub>3 * d\<^sub>3\<^sub>4"

    have "(p\<^sub>2, (w\<^sub>2\<^sub>4, d\<^sub>2\<^sub>4), p\<^sub>4) \<in> monoid_rtrancl (wts_to_monoidLTS ts)"
      using local.Cons monoid_rtrancl_into_rtrancl.hyps(2)  w\<^sub>3\<^sub>4d\<^sub>3\<^sub>4_split d\<^sub>2\<^sub>4_def p\<^sub>2_d\<^sub>2\<^sub>3_d\<^sub>1\<^sub>2_p(3)
        monoid_rtrancl.monoid_rtrancl_into_rtrancl[of p\<^sub>2 "(w\<^sub>2\<^sub>3, d\<^sub>2\<^sub>3)" p\<^sub>3 "wts_to_monoidLTS ts" "(w\<^sub>3\<^sub>4, d\<^sub>3\<^sub>4)" p\<^sub>4]
      unfolding w\<^sub>1\<^sub>3_def[symmetric] w\<^sub>2\<^sub>4_def by (simp add: mult_prod_def times_list_def)
    moreover
    define d\<^sub>1\<^sub>4 where "d\<^sub>1\<^sub>4 = d\<^sub>1\<^sub>2 * d\<^sub>2\<^sub>4"
    moreover
    have "(p\<^sub>1, ([\<gamma>\<^sub>1\<^sub>2], d\<^sub>1\<^sub>2), p\<^sub>2) \<in> wts_to_monoidLTS ts"
      using p\<^sub>2_d\<^sub>2\<^sub>3_d\<^sub>1\<^sub>2_p by fastforce
    moreover
    have "w\<^sub>1\<^sub>3d\<^sub>1\<^sub>3 * w\<^sub>3\<^sub>4d\<^sub>3\<^sub>4 = (\<gamma>\<^sub>1\<^sub>2 # w\<^sub>2\<^sub>4, d\<^sub>1\<^sub>4)"
      by (metis append_Cons d\<^sub>1\<^sub>3_def d\<^sub>1\<^sub>4_def d\<^sub>2\<^sub>4_def d\<^sub>3\<^sub>4_def local.Cons mult.assoc mult_prod_def 
          p\<^sub>2_d\<^sub>2\<^sub>3_d\<^sub>1\<^sub>2_p(4) times_list_def w\<^sub>2\<^sub>4_def w\<^sub>3\<^sub>4_def)
    ultimately show ?thesis
      by metis
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
  shows "(\<^bold>\<Sigma>(p, w)\<Rightarrow>\<^sup>*p') \<le> d"
  using countable_SumInf_elem[of "{d'. (p, w) \<Midarrow> d' \<Rightarrow>\<^sup>* (p', [])}" d] 
    assms by (auto simp add: countable_monoid_star_all)

lemma push_seq_weight_if_l_step_relp:
  assumes "(p,w) \<Midarrow>d\<Rightarrow> (p',[])"
  shows "(\<^bold>\<Sigma>(p, w)\<Rightarrow>\<^sup>*p') \<le> d"
  by (simp add: assms monoid_star_relp_if_l_step_relp push_seq_weight_if_monoid_star_relp)

lemma push_seq_weight_trans:
  assumes "(\<^bold>\<Sigma>(p'', w')\<Rightarrow>\<^sup>*pi) \<le> d1"
  assumes "(\<^bold>\<Sigma>(pi, w'')\<Rightarrow>\<^sup>*p2) \<le> d2"
  shows "(\<^bold>\<Sigma>(p'', w'@w'')\<Rightarrow>\<^sup>*p2) \<le> d1 * d2"
proof -
  have "(\<^bold>\<Sigma>(p'',w'@w'') \<Rightarrow>\<^sup>* p2) \<le> \<^bold>\<Sum>{d1' * d2'| d1'  d2'. (p'',w') \<Midarrow>d1'\<Rightarrow>\<^sup>* (pi,[]) \<and> (pi,w'') \<Midarrow>d2'\<Rightarrow>\<^sup>* (p2,[])}"
    using SumInf_mono[of "{d1' * d2' |d1' d2'. (p'', w') \<Midarrow> d1' \<Rightarrow>\<^sup>* (pi, []) \<and> (pi, w'') \<Midarrow> d2' \<Rightarrow>\<^sup>* (p2, [])}" 
        "{d'. (p'', w' @ w'') \<Midarrow> d' \<Rightarrow>\<^sup>* (p2, [])}"]
      step_relp_seq by (force simp add: countable_monoid_star_all dissect_set)
  also have "... \<le> (\<^bold>\<Sigma>(p'',w') \<Rightarrow>\<^sup>* pi) * (\<^bold>\<Sigma>(pi,w'') \<Rightarrow>\<^sup>* p2)"
    using SumInf_left_distr[of "{d'. (pi, w'') \<Midarrow> d' \<Rightarrow>\<^sup>* (p2, [])}" "\<^bold>\<Sum> {d'. (p'', w') \<Midarrow> d' \<Rightarrow>\<^sup>* (pi, [])}"] 
      SumInf_of_SumInf_right_distr_simple by (force simp add: countable_monoid_star_all dissect_set)
  also have "... \<le> d1 * d2"
    using assms BoundedDioid.mult_isol_var by auto
  finally 
  show ?thesis
    by auto
qed

lemma push_seq_weight_trans_push:
  assumes "(\<^bold>\<Sigma>(p'', [\<mu>'])\<Rightarrow>\<^sup>*pi) \<le> d1"
  assumes "(\<^bold>\<Sigma>(pi, [\<mu>''])\<Rightarrow>\<^sup>*p2) \<le> d2"
  shows "(\<^bold>\<Sigma>(p'', [\<mu>', \<mu>''])\<Rightarrow>\<^sup>*p2) \<le> d1 * d2"
  using assms push_seq_weight_trans[of p'' "[\<mu>']" pi d1 "[\<mu>'']" p2 d2] by auto

lemma monoid_star_relp_push_seq_weight_trans:
  assumes "(p1, w) \<Midarrow>d\<Rightarrow>\<^sup>* (p'', w')"
  assumes "(\<^bold>\<Sigma>(p'', w')\<Rightarrow>\<^sup>*p2) \<le> d'"
  shows "(\<^bold>\<Sigma>(p1, w)\<Rightarrow>\<^sup>*p2) \<le> d * d'"
proof -
  have "(\<^bold>\<Sigma> (p1, w) \<Rightarrow>\<^sup>* p2) \<le> \<^bold>\<Sum>{d * d'| d'. (p1, w) \<Midarrow>d\<Rightarrow>\<^sup>* (p'',w') \<and> (p'',w') \<Midarrow>d'\<Rightarrow>\<^sup>* (p2,[])}"
    using SumInf_mono[of "{d * d' |d'. (p1, w) \<Midarrow> d \<Rightarrow>\<^sup>* (p'', w') \<and> (p'', w') \<Midarrow> d' \<Rightarrow>\<^sup>* (p2, [])}" 
        "{d'. (p1, w) \<Midarrow> d' \<Rightarrow>\<^sup>* (p2, [])}"]
    monoid_rtranclp_trans by (force simp add: countable_monoid_star_all dissect_set)
  also have "... \<le> \<^bold>\<Sum>{d * d'| d'. (p'',w') \<Midarrow>d'\<Rightarrow>\<^sup>* (p2,[])}"
    using \<open>(p1, w) \<Midarrow> d \<Rightarrow>\<^sup>* (p'', w')\<close> by fastforce
  also have "... \<le> d * \<^bold>\<Sigma>(p'',w') \<Rightarrow>\<^sup>* p2"
    by (simp add: SumInf_left_distr countable_monoid_star_all dissect_set)
  also have "... \<le> d * d'"
    using assms by (simp add: assms BoundedDioid.mult_isol)
  finally 
  show ?thesis
    by auto
qed

lemma push_seq_weight_trans_Cons:
  assumes "(\<^bold>\<Sigma>(p, [\<gamma>])\<Rightarrow>\<^sup>*pi) \<le> d1"
  assumes "(\<^bold>\<Sigma>(pi, w)\<Rightarrow>\<^sup>*p') \<le> d2"
  shows "(\<^bold>\<Sigma>(p, \<gamma> # w)\<Rightarrow>\<^sup>*p') \<le> d1 * d2"
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
    using countable_SumInf_elem  \<open>(p, []) \<Midarrow> 1 \<Rightarrow>\<^sup>* (p', [])\<close> \<open>d = 1\<close> 
    by (simp add: countable_monoid_star_all dissect_set)
  then show ?case .
next
  case (Cons \<gamma> w)
  from Cons(2) have
    "\<exists>pi d1 d2. d = d1 * d2 
                \<and> (pi, (w, d2), p') \<in> monoid_rtrancl (wts_to_monoidLTS A)
                \<and> (p, ([\<gamma>], d1), pi) \<in> (wts_to_monoidLTS A)"
    unfolding monoid_star_is_monoid_rtrancl
    using monoid_star_nonempty by fastforce
  then obtain pi d1 d2 where pi_d1_d2_p:
    "d = d1 * d2"
    "(pi, (w, d2), p') \<in> monoid_rtrancl (wts_to_monoidLTS A)"
    "(p, ([\<gamma>], d1), pi) \<in> wts_to_monoidLTS A"
    by blast
  then have d2l: "d2 \<ge> \<^bold>\<Sigma>(pi, w) \<Rightarrow>\<^sup>* p'"
    using Cons(1)[of pi d2] by auto

  have "d1 \<ge> (\<^bold>\<Sigma> (p, [\<gamma>]) \<Rightarrow>\<^sup>* pi)"
    using assms(1) pi_d1_d2_p(3) sound_def by blast
  then have "(\<^bold>\<Sigma> (p, \<gamma> # w) \<Rightarrow>\<^sup>* p') \<le>  d1 * d2"
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
    assume p1_\<mu>_l_p2: "(p1, ([\<mu>], l), p2) \<in> wts_to_monoidLTS A'"
    show "l \<ge> \<^bold>\<Sigma> (p1, [\<mu>]) \<Rightarrow>\<^sup>* p2"
    proof (cases "p1 = p' \<and> \<mu> = \<gamma>' \<and> p2 = q")
      case True
      then have True': "p1 = p'" "\<mu> = \<gamma>'" "p2 = q"
        by auto
      have l_eql: "l = d'' + d * d'"
        using p1_\<mu>_l_p2 unfolding ps(4) True' unfolding wts_to_monoidLTS_def by auto
      have d''_geq: "d'' \<ge> \<^bold>\<Sigma> (p1,[\<mu>]) \<Rightarrow>\<^sup>* p2"
        using ps(5) assms(1) True unfolding sound_def wts_to_monoidLTS_def by force
      have p1_to_p'': "(p1, [\<mu>]) \<Midarrow>d\<Rightarrow> (p'', lbl w')"
        using ps(1) True step_relp_def2 by auto
      show ?thesis
      proof (rule pre_star_rule_exhaust[OF ps(3)[unfolded True'[symmetric]]])
        assume "p2 = p''"
        assume "d' = 1"
        assume "w' = pop"
        from p1_to_p'' have "(p1, [\<mu>]) \<Midarrow>d * d'\<Rightarrow> (p2,[])"
          using \<open>d' = 1\<close> \<open>w' = pop\<close> \<open>p2 = p''\<close> by auto
        then have "d * d' \<ge> \<^bold>\<Sigma> (p1, [\<mu>]) \<Rightarrow>\<^sup>* p2"
          using push_seq_weight_if_l_step_relp[of p1 "[\<mu>]" "d * d'" p2] by auto
        then show "l \<ge> \<^bold>\<Sigma> (p1, [\<mu>]) \<Rightarrow>\<^sup>* p2"
          using d''_geq l_eql by auto
      next
        fix \<mu>'
        assume "A $ (p'', \<mu>', p2) = d'"
        assume w'_swap: "w' = swap \<mu>'"
        from ps(3) have "(p'', ([\<mu>'],d'), p2) \<in> monoid_rtrancl (wts_to_monoidLTS A)"
          using True'(3) \<open>w' = swap \<mu>'\<close> by force
        then have p''_to_p2: "d' \<ge> \<^bold>\<Sigma> (p'',[\<mu>']) \<Rightarrow>\<^sup>* p2"
          using assms(1) sound_elim2 by force
        from p1_to_p'' have "(p1, [\<mu>]) \<Midarrow>d\<Rightarrow>\<^sup>* (p'',[\<mu>'])"
          unfolding True' w'_swap using monoid_rtranclp.monoid_rtrancl_into_rtrancl by fastforce
        then have "(\<^bold>\<Sigma> (p1, [\<mu>]) \<Rightarrow>\<^sup>* p2) \<le> d * d'"
          using p''_to_p2 monoid_star_relp_push_seq_weight_trans by auto
        then show "l \<ge> \<^bold>\<Sigma> (p1, [\<mu>]) \<Rightarrow>\<^sup>* p2"
          using d''_geq l_eql by auto
      next
        fix \<mu>' \<mu>'' pi
        assume edge_weights: "A $ (p'', \<mu>', pi) * A $ (pi, \<mu>'', p2) = d'"
        assume "w' = push \<mu>' \<mu>''"
        define d1 where "d1 = A $ (p'', \<mu>', pi)"
        define d2 where "d2 = A $ (pi, \<mu>'', p2)"
        have "d' = d1 * d2"
          using d1_def d2_def edge_weights by auto

        from p1_to_p'' have "(p1,[\<mu>]) \<Midarrow>d\<Rightarrow>\<^sup>* (p'',[\<mu>',\<mu>''])"
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
          using d''_geq l_eql by (simp add: \<open>d' = d1 * d2\<close> mult.assoc) 
      qed
    next
      case False
      then have "(p1, ([\<mu>], l), p2) \<in> wts_to_monoidLTS A"
        using ps(4) p1_\<mu>_l_p2 unfolding wts_to_monoidLTS_def by auto
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
  shows "accepts A finals (p,[]) = 1"
proof -
  have "{d | d q. q \<in> finals \<and> (p,([],d),q) \<in> monoid_rtrancl (wts_to_monoidLTS A)} = {1}"
    using Collect_cong[of "\<lambda>d. \<exists>q. q \<in> finals \<and> (p, ([], d), q) \<in> monoid_rtrancl (wts_to_monoidLTS A)" "\<lambda>d. d = 1"]
      assms monoid_rtrancl_wts_to_monoidLTS_refl mstar_wts_empty_one by force
  then show ?thesis
    by (simp add: accepts_def)
qed

lemma accept_is_zero_if_nonfinal_empty:
  fixes A::"('ctr_loc \<times> 'label \<times> 'ctr_loc) \<Rightarrow>f 'weight"
  assumes "p \<notin> finals"
  shows "accepts A finals (p,[]) = 0"
proof -
  have "{d | d q. q \<in> finals \<and> (p,([],d),q) \<in> monoid_rtrancl (wts_to_monoidLTS A)} = {}"
    using assms monoid_star_pop[of p pop _ _ A] by fastforce
  then show ?thesis
    unfolding accepts_def2 using SumInf_empty 
      Collect_cong[of "\<lambda>d. \<exists>q. q \<in> finals \<and> (p, ([], d), q) \<in> monoid_rtrancl (wts_to_monoidLTS A)"
        "\<lambda>d. \<exists>q. q \<in> finals \<and> (p, ([], d), q) \<in> monoid_rtrancl (wts_to_monoidLTS A)"] by metis
qed

lemma zero_weight_if_nonrefl_path_in_K0:
  "(p,wd,q) \<in> monoid_rtrancl (wts_to_monoidLTS (K$ 0)) \<Longrightarrow> p \<noteq> q \<Longrightarrow> snd wd = 0"
proof (induct rule: monoid_rtrancl_induct_rev)
  case (monoid_rtrancl_refl p)
  then show ?case by auto
next
  case (monoid_rtrancl_into_rtrancl p w p' q wd')
  show ?case 
  proof (cases "p' \<noteq> q")
    case True
    then show ?thesis
      using monoid_rtrancl_into_rtrancl by (simp add: mult_prod_def)
  next
    case False
    then show ?thesis
      by (metis finfun_const_apply monoid_rtrancl_into_rtrancl.hyps(1) mult_prod_def mult_zero_left 
          snd_conv wts_label_d')
  qed
qed

lemma zero_weight_if_nonempty_word_in_K0:
  "(p,wd,q) \<in> monoid_rtrancl (wts_to_monoidLTS (K$ 0)) \<Longrightarrow> fst wd \<noteq> [] \<Longrightarrow> snd wd = 0"
proof (induct rule: monoid_rtrancl_induct_rev)
  case (monoid_rtrancl_refl p)
  then show ?case 
    by (simp add: one_list_def one_prod_def)
next
  case (monoid_rtrancl_into_rtrancl p w p' q wd')
  show ?case 
  proof (cases "fst wd' \<noteq> []")
    case True
    then show ?thesis
      using monoid_rtrancl_into_rtrancl by (simp add: mult_prod_def)
  next
    case False
    then show ?thesis
      by (metis finfun_const_apply monoid_rtrancl_into_rtrancl.hyps(1) mult_prod_def mult_zero_left 
          snd_conv wts_label_d')
  qed
qed

lemma SumInf_is_zero_if_subset_singleton_zero[simp]: "X \<subseteq> {0} \<Longrightarrow> \<^bold>\<Sum> X = 0"
  using subset_singletonD by fastforce

lemma accepts_K0_is_zero_if_nonfinal:
  assumes "p \<notin> finals"
  shows "accepts (K$ 0) finals (p,w) = 0"
proof -
  have "{d :: 'weight. \<exists>q. q \<in> finals \<and> (p, (w, d), q) \<in> monoid_rtrancl (wts_to_monoidLTS (K$ 0))} \<subseteq> {0}"
    using zero_weight_if_nonrefl_path_in_K0[of p "(w,_)" _] assms by auto
  then show ?thesis
    unfolding accepts_def by auto
qed

lemma accepts_K0_is_zero_if_nonempty:
  assumes "w \<noteq> []"
  shows "accepts (K$ 0) finals (p,w) = 0"
proof -
  have "{d :: 'weight. \<exists>q. q \<in> finals \<and> (p, (w, d), q) \<in> monoid_rtrancl (wts_to_monoidLTS (K$ 0))} \<subseteq> {0}"
    using zero_weight_if_nonempty_word_in_K0[of p "(w,_)" _] assms by auto
  then show ?thesis
    unfolding accepts_def by auto
qed

lemma accepts_empty_iff: 
  fixes A::"('ctr_loc \<times> 'label \<times> 'ctr_loc) \<Rightarrow>f 'weight"
  shows "accepts A finals (p,[]) = (if p\<in>finals then 1 else 0)"
  by (simp add: accept_is_one_if_final_empty accept_is_zero_if_nonfinal_empty)

lemma accepts_K0_iff[simp]: "accepts (K$ 0) finals (p,w) = (if p\<in>finals \<and> w = [] then 1 else 0)"
  by (metis accept_is_one_if_final_empty accepts_K0_is_zero_if_nonfinal accepts_K0_is_zero_if_nonempty)

lemma sound_empty: "sound (K$ 0)"
  by (simp add: sound_def wts_to_monoidLTS_def)

lemma countable_monoid_rtrancl_wts_to_monoidLTS:
 fixes A::"(('ctr_loc, 'label, 'weight::bounded_idempotent_semiring) w_transitions)"
 shows "countable (monoid_rtrancl (wts_to_monoidLTS A))"
  by (metis countable_wts monoidLTS.countable_monoid_star monoidLTS.intro monoidLTS.monoid_star_is_monoid_rtrancl)

lemma countable_monoid_rtrancl_wts_to_monoidLTS_pair:
  fixes A :: "(('ctr_loc, 'label, 'weight::bounded_idempotent_semiring) w_transitions)"
  shows "countable {(d, q). (p, (w, d), q) \<in> monoid_rtrancl (wts_to_monoidLTS A)}"
proof -
  have "(monoid_rtrancl (wts_to_monoidLTS A) \<inter> {(p', (w', d), q) |p' w' d q. p' = p \<and> w' = w})
           = {(p, (w, d), q) |d q. (p, (w, d), q) \<in> monoid_rtrancl (wts_to_monoidLTS A)}"
    by auto
  then have A: "countable {(p, (w, d), q)| d q. (p, (w, d), q) \<in> monoid_rtrancl (wts_to_monoidLTS A)}"
    using countable_Int1[OF countable_monoid_rtrancl_wts_to_monoidLTS[of A], of "{(p', (w', d), q) | p' w' d q. p' = p \<and> w' = w}"]
    by auto
  have "((\<lambda>(p, (w, d), q). (d, q)) ` {(p, (w, d), q) |d q. (p, (w, d), q) \<in> monoid_rtrancl (wts_to_monoidLTS A)})
           = {(d, q). (p, (w, d), q) \<in> monoid_rtrancl (wts_to_monoidLTS A)}"
    unfolding image_def by auto
  then show ?thesis
    using countable_image[of "{(p, (w, d), q) |d q. (p, (w, d), q) \<in> monoid_rtrancl (wts_to_monoidLTS A)}"
      "\<lambda>(p, (w, d), q). (d, q)", OF A]
    by auto
qed

lemmas countable_monoid_rtrancl_wts_to_monoidLTS_all =
  countable_monoid_rtrancl_wts_to_monoidLTS
  countable_monoid_rtrancl_wts_to_monoidLTS_pair

lemma countable_monoid_rtrancl_wts_to_monoidLTS_P: 
  fixes A::"(('ctr_loc, 'label, 'weight::bounded_idempotent_semiring) w_transitions)"
  shows "countable {f d q |d q. P d q \<and> (p, (w, d), q) \<in> monoid_rtrancl (wts_to_monoidLTS A)}"
  using countable_monoid_rtrancl_wts_to_monoidLTS_all by (simp add: dissect_set)

(*lemma countable_f_finals: "countable {f q| q. q \<in> finals}"
  by (simp add: dissect_set)*)

lemma lemma_3_2_w_alternative:
  assumes soundA': "sound A'"
  shows "accepts A' finals pv \<ge> weight_pre_star (accepts (K$ 0) finals) pv"
proof -
  obtain p v where pv_split: "pv = (p, v)"
    by (cases pv) 
  have "weight_pre_star (accepts (K$ 0) finals) (p,v) = \<^bold>\<Sum>{d' * accepts (K$ 0) finals (q,w)| d' q w. (p,v) \<Midarrow>d'\<Rightarrow>\<^sup>* (q,w)}"
    by (simp add: weight_pre_star_def)
  also have "... = \<^bold>\<Sum>{d' * (if q\<in>finals \<and> w=[] then 1 else 0)| d' q w. (p,v) \<Midarrow>d'\<Rightarrow>\<^sup>* (q,w)}"
    by simp
  also have "... \<le> \<^bold>\<Sum>{d' |d' q. q \<in> finals \<and> (p,v) \<Midarrow>d'\<Rightarrow>\<^sup>* (q,[])}"
    using SumInf_mono[of "{d' |d' q. q \<in> finals \<and> (p,v) \<Midarrow>d'\<Rightarrow>\<^sup>* (q,[])}" 
        "{d' * (if q\<in>finals \<and> w=[] then 1 else 0)| d' q w. (p,v) \<Midarrow>d'\<Rightarrow>\<^sup>* (q,w)}"]
      countable_push_seq_weight2 by (fastforce simp add: countable_monoid_star_all dissect_set)
  also have "... = \<^bold>\<Sum>{(\<^bold>\<Sigma> (p,v) \<Rightarrow>\<^sup>* q) | q. q \<in> finals}"
    using SumInf_of_SumInf_right_distr[of "\<lambda>q. q \<in> finals" "\<lambda>d q. (p,v) \<Midarrow>d\<Rightarrow>\<^sup>* (q,[])" "\<lambda>d q. d" "\<lambda>q. 1", 
                                       OF _ countable_star_f_p9, symmetric]
    unfolding push_seq_weight_def2[symmetric] mult.right_neutral 
    using Collect_cong[of "\<lambda>d. \<exists>d'. (p, v) \<Midarrow> d \<Rightarrow>\<^sup>* (d', []) \<and> d' \<in> finals"
        "\<lambda>d'. \<exists>q. q \<in> finals \<and> (p, v) \<Midarrow> d' \<Rightarrow>\<^sup>* (q, [])"]
    by fastforce
  also have "... \<le> \<^bold>\<Sum>{\<^bold>\<Sigma>(p,v) \<Rightarrow>\<^sup>* q |d q. q \<in> finals \<and> (p, (v, d), q) \<in> monoid_rtrancl (wts_to_monoidLTS A')}" 
    using SumInf_mono[of "{pvq. \<exists>d q. pvq = (\<^bold>\<Sigma>(p, v)\<Rightarrow>\<^sup>*q) \<and> q \<in> finals \<and> (p, (v, d), q) \<in> monoid_rtrancl (wts_to_monoidLTS A')}" 
        "{\<^bold>\<Sigma>(p, v)\<Rightarrow>\<^sup>*q |q. q \<in> finals}"] by (force simp add: countable_monoid_rtrancl_wts_to_monoidLTS_all dissect_set)
  also have "... \<le> \<^bold>\<Sum>{d |d q. q \<in> finals \<and> (p, (v, d), q) \<in> monoid_rtrancl (wts_to_monoidLTS A')}" 
    using SumInf_mono_wrt_img_of_set[of 
        "\<lambda>(d, q). q \<in> finals \<and> (p, (v, d), q) \<in> monoid_rtrancl (wts_to_monoidLTS A')"
        "\<lambda>(d, q). \<^bold>\<Sigma> (p,v) \<Rightarrow>\<^sup>* q"
        "\<lambda>(d, q). d"
        ]
    using soundA' sound_def2 countable_monoid_rtrancl_wts_to_monoidLTS by (force simp add: countable_monoid_rtrancl_wts_to_monoidLTS_all dissect_set)
  also have "... = accepts A' finals (p,v)"
    unfolding accepts_def by (simp split: prod.split)
  finally show ?thesis
    unfolding pv_split by auto
qed

lemma lemma_3_2_w_alternative': 
  assumes "pre_star_rule (K$ 0) A"
  shows "accepts A finals pv \<ge> weight_pre_star (accepts (K$ 0) finals) pv"
  using lemma_3_2_w_alternative[OF pre_star_rule_sound[OF sound_empty assms]] by auto

lemma lemma_3_2_w_alternative''':
  assumes "pre_star_rule\<^sup>*\<^sup>* (K$ 0) A'"
  shows "accepts A' finals (p,v) \<ge> weight_pre_star (accepts (K$ 0) finals) (p,v)"
  using pre_star_rule_rtranclp_sound assms lemma_3_2_w_alternative sound_empty by blast


(* Begin superfluous lemmas *)

lemma accepts_lte_accepts_K0':
  shows "accepts A' finals (p,v) \<le> accepts (K$ 0) finals (p,v)"
proof (cases "p \<in> finals \<and> v = []")
  case True
  then have "accepts (K$ 0) finals (p,v) = 1"
    by auto
  also have "... \<ge> accepts A' finals (p,v)"
    unfolding accepts_def
    using True accepts_def[of A' finals] accept_is_one_if_final_empty[of p finals A'] by force
  finally show ?thesis 
    by auto
next
  case False
  then have "p \<notin> finals \<or> v \<noteq> []"
    by auto
  then show ?thesis
  proof
    assume "p \<notin> finals"
    then have "accepts (K$ 0) finals (p,v) = 0"
      by auto
    also have "... \<ge> accepts A' finals (p,v)"
      by simp
    finally show ?thesis 
      by auto
  next
    assume "v \<noteq> []"
    then have "accepts (K$ 0) finals (p,v) = 0"
      by auto
    also have "... \<ge> accepts A' finals (p,v)"
       by simp
    finally show ?thesis 
      by auto
  qed
qed

lemma accepts_lte_accepts_K0:
  shows "accepts A' finals \<le> accepts (K$ 0) finals"
  unfolding le_fun_def using accepts_lte_accepts_K0' by fast

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
    using SumInf_mono_wrt_img_of_set[of "\<lambda>(l, c'). c \<Midarrow> l \<Rightarrow>\<^sup>* c'" "\<lambda>(l, c). l * X c" "\<lambda>(l, c). l * Y c"] 
      XY  Collect_mono_iff countable_subset by (simp add: countable_monoid_star_all dissect_set)
  also 
  have "... \<le> weight_pre_star Y c"
    unfolding weight_pre_star_def by auto
  finally
  show ?thesis 
    by auto
qed

lemma weight_pre_star_accepts_lt_weight_pre_star_accepts_K0:
  "weight_pre_star (accepts A' finals) c \<le> weight_pre_star (accepts (K$ 0) finals) c"
  using weight_pre_star_mono[OF accepts_lte_accepts_K0] by auto

lemma lemma_3_2_w_alternative_BONUS:
  assumes soundA': "sound A'"
  shows "accepts A' finals (p,v) \<ge> weight_pre_star (accepts A finals) (p,v)"
proof -
  have "weight_pre_star (accepts A finals) (p,v) \<le> weight_pre_star (accepts (K$ 0) finals) (p, v)"
    using weight_pre_star_accepts_lt_weight_pre_star_accepts_K0 by auto
  also have "... \<le> accepts A' finals (p, v)"
    using lemma_3_2_w_alternative soundA' by auto
  finally show ?thesis
    by auto
qed

lemma lemma_3_2_w_alternative'_BONUS: 
  assumes soundA': "sound A'"
  assumes "pre_star_rule A' A''"
  shows "accepts A'' finals (p,v) \<ge> weight_pre_star (accepts A finals) (p,v)"
proof -
  have soundA'': "sound A''"
    using pre_star_rule_sound soundA' assms(2) by auto
  have "weight_pre_star (accepts A finals) (p, v) \<le> weight_pre_star (accepts (K$ 0) finals) (p, v)"
    using weight_pre_star_accepts_lt_weight_pre_star_accepts_K0 by auto
  also have "... \<le> accepts A'' finals (p,v)"
    using lemma_3_2_w_alternative soundA'' by auto
  finally show "accepts A'' finals (p,v) \<ge> weight_pre_star (accepts A finals) (p,v)"
    by auto
qed

lemma weight_pre_star_leq':
   "X c \<ge> weight_pre_star X c"
proof -
  have "weight_pre_star X c = \<^bold>\<Sum> {l * X c' |l c'. c \<Midarrow> l \<Rightarrow>\<^sup>* c'}"
    unfolding weight_pre_star_def by auto
  also have "... \<le> \<^bold>\<Sum> {l * X c |l. c \<Midarrow> l \<Rightarrow>\<^sup>* c}"
    using SumInf_mono[of "{l * X c |l. c \<Midarrow> l \<Rightarrow>\<^sup>* c}" "{l * X c' |l c'. c \<Midarrow> l \<Rightarrow>\<^sup>* c'}" ] 
    by (fastforce simp add: countable_monoid_star_all dissect_set)
  also have "... \<le> \<^bold>\<Sum> {1 * X c}"
    using SumInf_mono[of "{1 * X c}" "{l * X c |l. c \<Midarrow> l \<Rightarrow>\<^sup>* c}"] by (fastforce simp add: countable_monoid_star_all dissect_set)
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
      have count: "countable {l' * C c'' |l' c''. c' \<Midarrow> l' \<Rightarrow>\<^sup>* c''}"
        by (simp add: countable_monoid_star_all dissect_set)
      then have "l * \<^bold>\<Sum> {l' * C c'' |l' c''. c' \<Midarrow> l' \<Rightarrow>\<^sup>* c''} =
              \<^bold>\<Sum> {l * l' * C c'' |l' c''. c' \<Midarrow> l' \<Rightarrow>\<^sup>* c''}"
        unfolding SumInf_left_distr[of "{l' * C c'' |l' c''. c' \<Midarrow> l' \<Rightarrow>\<^sup>* c''}" l, OF count]
        using mult.assoc 
          mem_Collect_eq[of _ "\<lambda>x. \<exists>l' c''. x = l' * C c'' \<and> c' \<Midarrow> l' \<Rightarrow>\<^sup>* c''"]
        by (metis (no_types, lifting))
    }
    then show ?thesis
      by auto
  qed
  also
  have "... = \<^bold>\<Sum> {l * l' * C c'' |l' c'' l c'. c' \<Midarrow> l' \<Rightarrow>\<^sup>* c'' \<and> c \<Midarrow> l \<Rightarrow>\<^sup>* c'}"
    using SumInf_of_SumInf[of
        "\<lambda>(l,c'). c \<Midarrow> l \<Rightarrow>\<^sup>* c'"        
        "\<lambda>(l',c'') (l,c').  c' \<Midarrow> l' \<Rightarrow>\<^sup>* c''"        
        "\<lambda>(l',c'') (l,c'). l * l' * C c''", 
        OF countable_monoid_star_variant1] 
          countable_push_seq_weight3
    by force
  also
  have "... = \<^bold>\<Sum> {l * l' * C c'' |l' c'' l c'. c \<Midarrow> l \<Rightarrow>\<^sup>* c' \<and> c' \<Midarrow> l' \<Rightarrow>\<^sup>* c''}"
    by meson
  also
  have "... = \<^bold>\<Sum> {l'' * C c'' |l'' c''. c \<Midarrow> l'' \<Rightarrow>\<^sup>* c''}"
    using Collect_cong[of "\<lambda>x. \<exists>l' c'' l c'. x= l * l' * C c'' \<and> c \<Midarrow> l \<Rightarrow>\<^sup>* c' \<and> c' \<Midarrow> l' \<Rightarrow>\<^sup>* c''"
        "\<lambda>x. \<exists>l'' c''. x= l'' * C c'' \<and> c \<Midarrow> l'' \<Rightarrow>\<^sup>* c''"]
    using monoid_rtranclp.monoid_rtrancl_refl[of l_step_relp] monoid_rtranclp_trans[of l_step_relp] 
      mult_1 by (metis (no_types, lifting))
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
  shows "accepts A'' finals (p,v) \<ge> weight_pre_star (accepts A finals) (p,v)"
proof -
  have sound_A'': "sound A''"
    using pre_star_rule_rtranclp_sound soundA' assms(2) by auto
  have "weight_pre_star (accepts A finals) (p, v) \<le> weight_pre_star (accepts (K$ 0) finals) (p, v)"
    using weight_pre_star_accepts_lt_weight_pre_star_accepts_K0 by auto
  also have "... \<le> accepts A'' finals (p,v)"
    using lemma_3_2_w_alternative sound_A'' by auto
  finally show "accepts A'' finals (p,v) \<ge> weight_pre_star (accepts A finals) (p,v)"
    by auto
qed

(* End superfluous lemmas *)

lemma saturated_pre_star_rule_transition:
  assumes "saturated pre_star_rule A"
  assumes "((p, \<gamma>) \<midarrow>d\<hookrightarrow> (p', w))"
  assumes "(p', (lbl w, d'), q) \<in> monoid_rtrancl (wts_to_monoidLTS A)"
  assumes "(A $ (p, \<gamma>, q)) = d''"
  shows "(d'' + (d * d')) = d''"
  using assms unfolding saturated_def using pre_star_rule.intros by blast

lemma saturated_pre_star_rule_transition_leq:
  assumes "saturated pre_star_rule A"
  assumes "((p, \<gamma>) \<midarrow>d\<hookrightarrow> (p', w))"
  assumes "(p', (lbl w, d'), q) \<in> monoid_rtrancl (wts_to_monoidLTS A)"
  shows "d * d' \<ge> (A $ (p, \<gamma>, q))"
  by (metis assms meet.inf.absorb_iff2 meet.inf_commute saturated_pre_star_rule_transition)

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
  then obtain q du0 du1 where q_du0_du1_p:
    "(p, ([a],du0), q) \<in> (wts_to_monoidLTS A)" 
    "(q, (u1 @ l,du1), p') \<in> monoid_rtrancl (wts_to_monoidLTS A)" 
    "d = du0 * du1"
    by auto

  have "\<exists>d'' s d'''. (q, (u1, d''), s) \<in> monoid_rtrancl (wts_to_monoidLTS A) \<and> 
                     (s, (l, d'''), p') \<in> monoid_rtrancl (wts_to_monoidLTS A) \<and> 
                     du1 = d'' * d'''"
     using Cons.IH[OF q_du0_du1_p(2)] .
  then obtain d'' s d''' where
    "(q, (u1,d''), s) \<in> monoid_rtrancl (wts_to_monoidLTS A)"
    "(s, (l,d'''), p') \<in> monoid_rtrancl (wts_to_monoidLTS A)" 
    "du1 = d'' * d'''"
    by auto
  from this(1) have "(p, (a # u1, du0 * d''), s) \<in> monoid_rtrancl (wts_to_monoidLTS A)"
    using q_du0_du1_p(1) monoid_rtrancl_into_rtrancl_rev[of p "([a], du0)" q "wts_to_monoidLTS A" "(u1, d'')" s]
    by (simp add: mult_prod_def times_list_def)
  then show ?case
    by (metis (no_types, lifting) \<open>(s, (l, d'''), p') \<in> monoid_rtrancl (wts_to_monoidLTS A)\<close> 
        \<open>du1 = d'' * d'''\<close> q_du0_du1_p(3)  mult.assoc)   
qed

lemma merge_edge_and_monoid_rtrancl_wts_to_monoidLTS:
  assumes "A $ (p\<^sub>1, \<gamma>\<^sub>1\<^sub>2, p\<^sub>2) \<le> D\<^sub>1\<^sub>2"
  assumes "(p\<^sub>2, (w\<^sub>2\<^sub>3, d\<^sub>2\<^sub>3), p\<^sub>3) \<in> monoid_rtrancl (wts_to_monoidLTS A)"
  shows "\<exists>D\<^sub>1\<^sub>3. (p\<^sub>1, (\<gamma>\<^sub>1\<^sub>2 # w\<^sub>2\<^sub>3, D\<^sub>1\<^sub>3), p\<^sub>3) \<in> monoid_rtrancl (wts_to_monoidLTS A) \<and> D\<^sub>1\<^sub>3 \<le> D\<^sub>1\<^sub>2 * d\<^sub>2\<^sub>3"
proof -
  define d\<^sub>1\<^sub>2 where "d\<^sub>1\<^sub>2 = A $ (p\<^sub>1, \<gamma>\<^sub>1\<^sub>2, p\<^sub>2)"

  have p\<^sub>1_to_p\<^sub>2: "(p\<^sub>1, ([\<gamma>\<^sub>1\<^sub>2], d\<^sub>1\<^sub>2), p\<^sub>2) \<in> (wts_to_monoidLTS A)"
    using assms(1) d\<^sub>1\<^sub>2_def wts_to_monoidLTS_def by fastforce

  have "(p\<^sub>1, ([\<gamma>\<^sub>1\<^sub>2], d\<^sub>1\<^sub>2) * (w\<^sub>2\<^sub>3, d\<^sub>2\<^sub>3), p\<^sub>3) \<in> monoid_rtrancl (wts_to_monoidLTS A)"
    using monoid_rtrancl_into_rtrancl_rev[OF _ assms(2), of p\<^sub>1 "([\<gamma>\<^sub>1\<^sub>2],_)", OF p\<^sub>1_to_p\<^sub>2] .
  then have "(p\<^sub>1, (\<gamma>\<^sub>1\<^sub>2#w\<^sub>2\<^sub>3, d\<^sub>1\<^sub>2 * d\<^sub>2\<^sub>3), p\<^sub>3) \<in> monoid_rtrancl (wts_to_monoidLTS A)"
    by (simp add: mult_prod_def times_list_def)
  then show ?thesis
    using assms(1) d\<^sub>1\<^sub>2_def idempotent_semiring_ord_class.mult_isol_var by blast
qed

lemma monoid_rtrancl_wts_to_monoidLTS_if_saturated_is_rule':
  assumes "(p', \<gamma>) \<midarrow>d\<hookrightarrow> (p'', u1)"
    and "saturated pre_star_rule A"
    and e: "(p'',((lbl u1),d'),q) \<in> monoid_rtrancl (wts_to_monoidLTS A)"
  shows "\<exists>D. (p',([\<gamma>], D), q) \<in> monoid_rtrancl (wts_to_monoidLTS A) \<and> D \<le> d*d'"
proof -
  have "A $ (p', \<gamma>, q) \<le> d * d'"
    using saturated_pre_star_rule_transition_leq[OF assms(2) assms(1) e(1)] by auto
  then have "\<exists>D. (p', ([\<gamma>],D),q) \<in> monoid_rtrancl (wts_to_monoidLTS A) \<and> D \<le> d*d'"
    using merge_edge_and_monoid_rtrancl_wts_to_monoidLTS e monoid_rtrancl_wts_to_monoidLTS_refl 
    by fastforce
  then show ?thesis
    by (simp add: mult.assoc)
qed

lemma monoid_rtrancl_wts_to_monoidLTS_if_saturated_is_rule:
  assumes "(p', \<gamma>) \<midarrow>d\<hookrightarrow> (p'', u1)"
    and "saturated pre_star_rule A"
    and "(p'',((lbl u1) @ w1,d'),q) \<in> monoid_rtrancl (wts_to_monoidLTS A)"
  shows "\<exists>D. (p',(\<gamma> # w1, D), q) \<in> monoid_rtrancl (wts_to_monoidLTS A) \<and> D \<le> d*d'"
proof -
  obtain q1 d1 d2 where e:
    "(p'', ((lbl u1),d1), q1) \<in> monoid_rtrancl (wts_to_monoidLTS A)"
    "(q1,(w1,d2),q) \<in> monoid_rtrancl (wts_to_monoidLTS A)"
    "d' = d1*d2"
    using monoid_rtrancl_wts_to_monoidLTS_append_split[OF assms(3)] by auto

  have "A $ (p', \<gamma>, q1) \<le> d * d1"
    using monoid_rtrancl_wts_to_monoidLTS_if_saturated_is_rule'[OF assms(1,2) e(1)] monoid_star_swap
    by force
  then have "\<exists>D. (p', (\<gamma>#w1,D),q) \<in> monoid_rtrancl (wts_to_monoidLTS A) \<and> D \<le> d*d1*d2"
    using merge_edge_and_monoid_rtrancl_wts_to_monoidLTS e(2) by metis
  then show ?thesis
    by (simp add: e(3) mult.assoc)
qed


lemma accepts_if_is_rule:
  assumes "(p', \<gamma>) \<midarrow>d\<hookrightarrow> (p'', u1)"
    and "saturated pre_star_rule A"
  shows "accepts A finals (p',(\<gamma> # w1)) \<le> d * accepts A finals (p'', (lbl u1) @ w1)"
proof -
  have "\<^bold>\<Sum> {d' | d' q. q \<in> finals \<and> (p', (\<gamma> # w1, d'), q) \<in> monoid_rtrancl (wts_to_monoidLTS A)} \<le>
         \<^bold>\<Sum> {d * d'| d' q. q \<in> finals \<and> (p'', (lbl u1 @ w1, d'), q) \<in> monoid_rtrancl (wts_to_monoidLTS A)}"
    using monoid_rtrancl_wts_to_monoidLTS_if_saturated_is_rule[OF assms(1) assms(2), of w1 ]
      SumInf_bounded_by_SumInf_if_members_bounded[of
        "{d' | d' q. q \<in> finals \<and> (p', (\<gamma> # w1, d'), q) \<in> monoid_rtrancl (wts_to_monoidLTS A)}"
        "{d * d'| d' q. q \<in> finals \<and> (p'', (lbl u1 @ w1, d'), q) \<in> monoid_rtrancl (wts_to_monoidLTS A)}"]
    using countable_monoid_rtrancl_wts_to_monoidLTS_P by fastforce
  also have "... \<le> d * \<^bold>\<Sum> {d' | d' q. q \<in> finals \<and> (p'', (lbl u1 @ w1, d'), q) \<in> monoid_rtrancl (wts_to_monoidLTS A)}"
    using SumInf_left_distr[of "{is_d'. \<exists>d' q. is_d' = d' \<and> q \<in> finals \<and> (p'', (lbl u1 @ w1, d'), q) \<in> monoid_rtrancl (wts_to_monoidLTS A)}" d] 
      countable_monoid_rtrancl_wts_to_monoidLTS_P by fastforce
  finally show ?thesis
    using accepts_def[of A finals] by force
qed

lemma accepts_if_saturated_monoid_star_relp:
  assumes "(p', w) \<Midarrow>d\<Rightarrow> (p'', u)"
      and "saturated pre_star_rule A"
    shows "accepts A finals (p',w) \<le> d * accepts A finals (p'', u)"
  using assms(1) assms(2) accepts_if_is_rule[of _ _ _ _ _ A finals] step_relp_elim2 by blast

lemma accepts_if_saturated_monoid_star_relp_final':
  assumes "saturated pre_star_rule A"
  assumes "c \<Midarrow>l\<Rightarrow>\<^sup>* c'" and "fst c' \<in> finals" and "snd c' = []"
  shows "accepts A finals c \<le> l"
  using assms(2,3,4)
proof (induction rule: monoid_star_relp_induct_rev)
  case (monoid_star_refl c)
  then show ?case
    by (metis dual_order.eq_iff accept_is_one_if_final_empty prod.exhaust_sel)
next
  case (monoid_star_into_rtrancl p'w d p''u c d')
  then have accpt: "accepts A finals p''u \<le> d'"
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
    using accpt assms(1) accepts_if_saturated_monoid_star_relp idempotent_semiring_ord_class.mult_isol 
      monoid_star_into_rtrancl.hyps(1) order_trans p''u_split p'w_split by blast
qed

lemma accepts_if_saturated_monoid_star_relp_final:
  assumes "saturated pre_star_rule A"
  assumes "c \<Midarrow>l\<Rightarrow>\<^sup>* (p,[])" and "p \<in> finals"
  shows "accepts A finals c \<le> l"
  using accepts_if_saturated_monoid_star_relp_final' assms by simp 

lemma lemma_3_1_w':
  assumes "saturated pre_star_rule A"
  assumes "c \<Midarrow>l\<Rightarrow>\<^sup>* c'"
  shows "accepts A finals c \<le> l * accepts (K$ 0) finals c'"
  using assms accepts_if_saturated_monoid_star_relp_final[OF assms(1)] 
    accepts_K0_iff[of finals "fst c'" "snd c'"] by simp (metis prod.collapse)

lemma lemma_3_1_w:
  assumes "saturated pre_star_rule A"
  shows "accepts A finals c \<le> weight_pre_star (accepts (K$ 0) finals) c"
  unfolding weight_pre_star_def
  using SumInf_bounded_if_set_bounded[of "{l * accepts (K$ 0) finals c' |l c'. c \<Midarrow> l \<Rightarrow>\<^sup>* c'}" "accepts A finals c"]
    lemma_3_1_w'[OF assms] by (fastforce simp add: dissect_set countable_monoid_star_all)

theorem correctness:
  assumes "saturation pre_star_rule (K$ 0) A"
  shows "accepts A finals (p,v) = weight_pre_star (accepts (K$ 0) finals) (p,v)"
  using assms lemma_3_2_w_alternative''' lemma_3_1_w  saturation_def dual_order.eq_iff by metis

theorem correctness':
  assumes "saturation pre_star_rule (K$ 0) A"
  shows "accepts A finals c = weight_pre_star (accepts (K$ 0) finals) c"
  using assms lemma_3_2_w_alternative''' lemma_3_1_w  saturation_def dual_order.eq_iff by (metis prod.exhaust)

end


datatype ('ctr_loc, 'noninit) state =
  is_Init: Init (the_Ctr_Loc: 'ctr_loc) (* p \<in> P *)
  | is_Noninit: Noninit (the_St: 'noninit) (* q \<in> Q \<and> q \<notin> P *)

lemma finitely_many_states:
  assumes "finite (UNIV :: 'ctr_loc set)"
  assumes "finite (UNIV :: 'noninit set)"
  shows "finite (UNIV :: ('ctr_loc, 'noninit) state set)"
proof -
  define Init' :: "'ctr_loc \<Rightarrow> ('ctr_loc, 'noninit) state" where
    "Init' = Init"
  define Noninit' :: "'noninit \<Rightarrow> ('ctr_loc, 'noninit) state" where
    "Noninit' = Noninit"
  have split: "UNIV = (Init' ` UNIV) \<union> (Noninit' ` UNIV)"
    unfolding Init'_def Noninit'_def
  proof (rule; rule; rule)
    fix x :: "('ctr_loc, 'noninit) state"
    assume "x \<in> UNIV"
    moreover
    assume "x \<notin> range Noninit"
    ultimately
    show "x \<in> range Init"
      by (metis range_eqI state.exhaust)
  qed
  have "finite (Init' ` (UNIV:: 'ctr_loc set))"
    using assms by auto
  moreover
  have "finite (Noninit' ` (UNIV:: 'noninit set))"
    using assms by auto
  ultimately show "finite (UNIV :: ('ctr_loc, 'noninit) state set)"
    unfolding split by auto
qed

instantiation state :: (finite, finite) finite begin
  instance by standard (simp add: finitely_many_states)
end

lemma UNIV_state: "UNIV = Init ` UNIV \<union> Noninit ` UNIV"
proof -
  have "x \<in> range Init" if "x \<notin> range Noninit" for x :: "('a,'b) state"
    using that by (cases x) simp_all
  then show ?thesis by auto
qed

instantiation state :: (enum, enum) enum begin
  definition "enum_class.enum = map Init enum_class.enum @ map Noninit enum_class.enum"
  definition "enum_class.enum_all P \<longleftrightarrow> enum_class.enum_all (\<lambda>x. P (Init x)) \<and> enum_class.enum_all (\<lambda>x. P (Noninit x))"
  definition "enum_class.enum_ex P \<longleftrightarrow> enum_class.enum_ex (\<lambda>x. P (Init x)) \<or> enum_class.enum_ex (\<lambda>x. P (Noninit x))"
  instance proof 
  qed (simp_all only: enum_state_def enum_all_state_def enum_ex_state_def UNIV_state,
       auto simp add: enum_UNIV distinct_map enum_distinct inj_def) 
end

locale WPDS_with_W_automata = WPDS \<Delta>
  for \<Delta> :: "('ctr_loc::enum, 'label::finite, 'weight::bounded_idempotent_semiring) rule set"
  and ts :: "(('ctr_loc, 'noninit::enum) state, 'label, 'weight::bounded_idempotent_semiring) w_transitions"
  +
  assumes no_transition_to_init: "is_Init q \<Longrightarrow> ts $ (p, \<gamma>, q) = 0"
begin

interpretation dioidLTS transition_rel proof
  show "countable transition_rel" by (fact countable_transition_rel)
qed

notation step_relp (infix "\<Rightarrow>" 80)
notation step_starp (infix "\<Rightarrow>\<^sup>*" 80)
notation l_step_relp ("(_)/ \<Midarrow> (_)/ \<Rightarrow> (_)/" [70,70,80] 80)
notation monoid_star_relp ("(_)/ \<Midarrow> (_)/ \<Rightarrow>\<^sup>* (_)/" [90,90,100] 100) 

definition init_rules :: "(('ctr_loc, 'noninit) state, 'label::finite, 'weight::bounded_idempotent_semiring) rule set" where 
  "init_rules = {((Init p, \<gamma>), d, (Init p', w)) | p \<gamma> d p' w. (p,\<gamma>) \<midarrow>d\<hookrightarrow> (p',w)}"
definition pop_ts_rules :: "(('ctr_loc, 'noninit) state, 'label::finite, 'weight::bounded_idempotent_semiring) rule set" where 
  "pop_ts_rules = {((p,\<gamma>), d, (q, pop)) | p \<gamma> d q. ts $ (p,\<gamma>,q) = d}"

definition augmented_WPDS_rules :: "(('ctr_loc, 'noninit) state, 'label::finite, 'weight::bounded_idempotent_semiring) rule set" where 
 "augmented_WPDS_rules = init_rules \<union> pop_ts_rules"

lemma finite_init_rules: "finite init_rules" 
  unfolding init_rules_def is_rule_def
  using finite_f_on_set[OF finite_rules, of "\<lambda>x. (case x of ((p, \<gamma>), d, p', w) \<Rightarrow> ((Init p, \<gamma>), d, Init p', w))"]
  by force
lemma finite_pop_ts: "finite pop_ts_rules" 
proof -
  have f:"finite {t | t d. ts $ t = d}" by simp
  show ?thesis unfolding pop_ts_rules_def
    using finite_image_set[OF f, of "\<lambda>x. (case x of (p, \<gamma>, q) \<Rightarrow> ((p, \<gamma>), ts $ x, q, pop))"] by force
qed
lemma finite_augmented_WPDS_rules: "finite augmented_WPDS_rules"
  unfolding augmented_WPDS_rules_def
proof safe
  show "finite init_rules" by (fact finite_init_rules)
next 
  show "finite pop_ts_rules" by (fact finite_pop_ts)
qed
lemma countable_monoid_augmented: "countable (monoid_rtrancl (WPDS.transition_rel augmented_WPDS_rules))"
  by (fact countable_monoid_rtrancl[OF WPDS.countable_transition_rel[unfolded WPDS_def, OF finite_augmented_WPDS_rules]])

interpretation augmented_WPDS: WPDS augmented_WPDS_rules
  unfolding WPDS_def WPDS_def by (fact finite_augmented_WPDS_rules)


lemma W_automaton_instance[simp]: "W_automaton ts" 
  unfolding W_automaton_def monoidLTS_def using countable_wts[of ts] by blast
lemma WPDS_instance[simp]:"WPDS augmented_WPDS_rules"
  by (simp add: WPDS_def finite_augmented_WPDS_rules)
lemma monoidLTS_instance[simp]: "monoidLTS (WPDS.transition_rel augmented_WPDS_rules)"
  by (simp add: monoidLTS_def WPDS.countable_transition_rel[of augmented_WPDS_rules] WPDS_def finite_augmented_WPDS_rules)
lemma dioidLTS_instance[simp]: "dioidLTS (WPDS.transition_rel augmented_WPDS_rules)"
  by (simp add: dioidLTS_def)

definition augmented_rules_reach_empty where
  "augmented_rules_reach_empty finals p w d = (\<exists>p' \<in> finals. ((Init p, w), d, (p',[])) \<in> monoidLTS.monoid_star (WPDS.transition_rel augmented_WPDS_rules))"

definition reach_conf_in_W_automaton where
  "reach_conf_in_W_automaton finals p w d = (\<exists>l p' w'. (p, w) \<Midarrow>l\<Rightarrow>\<^sup>* (p', w') \<and> d = l * accepts ts finals (Init p',w'))"

lemma reach_conf_in_W_automaton_unfold:
  "\<^bold>\<Sum>{d. reach_conf_in_W_automaton finals p w d} = 
   \<^bold>\<Sum>{l * d | d l p' w' q. q \<in> finals \<and> (Init p', (w', d), q) \<in> monoid_rtrancl (wts_to_monoidLTS ts) \<and> (p, w) \<Midarrow> l \<Rightarrow>\<^sup>* (p', w')}"
proof -
  have c: "\<And>l p' w'. countable {(d, (l, (p', w'))) |d. \<exists>q. q \<in> finals \<and> (Init p', (w', d), q) \<in> monoid_rtrancl (wts_to_monoidLTS ts)}"
    subgoal for l p' w'
    using countable_f_on_P_Q_set2[of "\<lambda>d q. (Init p', (w', d), q) \<in> monoid_rtrancl (wts_to_monoidLTS ts)" "\<lambda>d q. d" "\<lambda>d q. q \<in> finals"]
    using countable_subset[OF _ countable_f_on_set[OF countable_monoid_rtrancl[OF countable_wts[of ts]], 
                                                   of "\<lambda>x. (snd (fst (snd x)), snd (snd x))", simplified],
                           of "{(d, q). (Init p', (w', d), q) \<in> monoid_rtrancl (wts_to_monoidLTS ts)}"]
    by (auto simp add: dissect_set) done
  have 
    "\<^bold>\<Sum>{d. reach_conf_in_W_automaton finals p w d} =
     \<^bold>\<Sum> {l * \<^bold>\<Sum> {d. \<exists>q. q \<in> finals \<and> (Init p', (w', d), q) \<in> monoid_rtrancl (wts_to_monoidLTS ts)} | l p' w'. (p, w) \<Midarrow> l \<Rightarrow>\<^sup>* (p', w')}"
    unfolding reach_conf_in_W_automaton_def accepts_def by simp meson
  moreover have 
    "\<^bold>\<Sum> {l * \<^bold>\<Sum> {d. \<exists>q. q \<in> finals \<and> (Init p', (w', d), q) \<in> monoid_rtrancl (wts_to_monoidLTS ts)} | l p' w'. (p, w) \<Midarrow> l \<Rightarrow>\<^sup>* (p', w')} = 
     \<^bold>\<Sum> {l * d | d l p' w' q. q \<in> finals \<and> (Init p', (w', d), q) \<in> monoid_rtrancl (wts_to_monoidLTS ts) \<and> (p, w) \<Midarrow> l \<Rightarrow>\<^sup>* (p', w')}"
    using SumInf_of_SumInf_left_distr[
        of "\<lambda>(l,p',w'). (p, w) \<Midarrow> l \<Rightarrow>\<^sup>* (p', w')" 
           "\<lambda>d (l,p',w'). \<exists>q. q \<in> finals \<and> (Init p', (w', d), q) \<in> monoid_rtrancl (wts_to_monoidLTS ts)"
           "\<lambda>(l,p',w'). l"
           "\<lambda>d (l,p',w'). d", simplified]
    by (auto simp add: countable_monoid_star_variant1 c) meson
  ultimately show ?thesis by argo
qed

lemma ts_subset_aug_rules: 
  "monoid_rtrancl (WPDS.transition_rel pop_ts_rules) 
   \<subseteq> monoid_rtrancl (WPDS.transition_rel augmented_WPDS_rules)"
  using WPDS_LTS_mono[OF finite_augmented_WPDS_rules, of pop_ts_rules] 
  unfolding augmented_WPDS_rules_def by blast

lemma ts_to_pop_rule:
  assumes "(p, ([l], d), q) \<in> wts_to_monoidLTS ts"
  shows "((p, l#w), d, q, w) \<in> WPDS.transition_rel pop_ts_rules"
  using WAutomaton.wts_label_d[OF assms]
        WPDS.transition_rel.simps[unfolded WPDS_def, OF finite_pop_ts]
        WPDS.is_rule_def[unfolded WPDS_def, OF finite_pop_ts]
  unfolding pop_ts_rules_def by simp

lemma wts_to_monoidLTS_only_single_w:
  assumes "(p, (w, d), q') \<in> wts_to_monoidLTS ts"
  shows "w = [hd w]"
  using assms unfolding wts_to_monoidLTS_def by auto

lemma ts_to_pop_rule_step:
  assumes "(p, (w, d), q') \<in> wts_to_monoidLTS ts"
  assumes "((q', w'), d', q, []) \<in> monoid_rtrancl (WPDS.transition_rel pop_ts_rules)"
  shows "((p, w@w'), d*d', q, []) \<in> monoid_rtrancl (WPDS.transition_rel pop_ts_rules)"
proof -
  have a1:"(p, ([hd w], d), q') \<in> wts_to_monoidLTS ts" 
    using assms(1) unfolding wts_to_monoidLTS_def by auto
  have "hd w # w' = w @ w'"
    using wts_to_monoidLTS_only_single_w[OF assms(1)] by simp
  then show ?thesis
    using monoid_rtrancl_into_rtrancl_rev[OF ts_to_pop_rule[OF a1] assms(2)] assms(2) by argo
qed

lemma augmented_rules_1_base:
  assumes "(p, (w, d), q) \<in> monoid_rtrancl (wts_to_monoidLTS ts)"
  shows "((p, w), d, q, []) \<in> monoid_rtrancl (WPDS.transition_rel augmented_WPDS_rules)"
proof -
  { fix wd
    assume "(p, wd, q) \<in> monoid_rtrancl (wts_to_monoidLTS ts)"
    then have "((p, fst wd), snd wd, q, []) \<in> monoid_rtrancl (WPDS.transition_rel pop_ts_rules)"
      apply (induct rule: monoid_rtrancl_induct_rev)
       apply (simp add: one_list_def one_prod_def)
      using ts_to_pop_rule_step
      by (simp add: mult_prod_def times_list_def)
  }
  then show ?thesis using assms using ts_subset_aug_rules by auto
qed

lemma rule_to_init_rule:
  assumes "(p, w) \<Midarrow>d\<Rightarrow> (p', w')"
  shows "((Init p, w), d, Init p', w') \<in> WPDS.transition_rel init_rules"
  using assms unfolding init_rules_def l_step_relp_def transition_rel.simps[of p w d p' w']
  by (auto simp add: WPDS.is_rule_def[unfolded WPDS_def, OF finite_init_rules, unfolded init_rules_def]
                     WPDS.transition_rel.simps[unfolded WPDS_def, OF finite_init_rules, unfolded init_rules_def])
lemma init_rule_to_rule:
  assumes "((Init p, w), d, Init p', w') \<in> WPDS.transition_rel init_rules"
  shows "(p, w) \<Midarrow>d\<Rightarrow> (p', w')"
  using assms unfolding init_rules_def l_step_relp_def transition_rel.simps[of p w d p' w']
  by (auto simp add: WPDS.is_rule_def[unfolded WPDS_def, OF finite_init_rules, unfolded init_rules_def] 
                     WPDS.transition_rel.simps[unfolded WPDS_def, OF finite_init_rules, unfolded init_rules_def])
lemma rule_aug_rule: "(p, w) \<Midarrow>d\<Rightarrow> (p', w') \<longleftrightarrow> ((Init p, w), d, Init p', w') \<in> WPDS.transition_rel init_rules"
  using rule_to_init_rule init_rule_to_rule by blast

lemma augmented_rules_1_step:
  fixes d::'weight
  assumes "(p, w) \<Midarrow>d\<Rightarrow> (p', w')"
  assumes "((Init p', w'), d' * d\<^sub>2, q, []) \<in> monoid_rtrancl (WPDS.transition_rel augmented_WPDS_rules)"
  shows "((Init p, w), d * d' * d\<^sub>2, q, []) \<in> monoid_rtrancl (WPDS.transition_rel augmented_WPDS_rules)"
proof -
  have "((Init p, w), d, Init p', w') \<in> WPDS.transition_rel augmented_WPDS_rules"
    using rule_to_init_rule[OF assms(1)]
    using WPDS_transition_rel_mono[OF finite_augmented_WPDS_rules, of init_rules]
    unfolding augmented_WPDS_rules_def by blast
  then show ?thesis
    using assms(2) monoid_rtrancl_into_rtrancl_rev[of "(Init p, w)" d "(Init p', w')" "WPDS.transition_rel augmented_WPDS_rules" "d' * d\<^sub>2" "(q, [])"]
    by (simp add: mult.assoc)
qed

lemma wpds_lts_induct_rev [consumes 1, case_names wpds_lts_base wpds_lts_step]:
  assumes "(p, w) \<Midarrow>d\<Rightarrow>\<^sup>* (p', w')"
  assumes "(\<And>p w. P p w 1 p w)"
  assumes "\<And>p w d p' w' d' p'' w''. (p, w) \<Midarrow>d\<Rightarrow> (p', w') \<Longrightarrow> P p' w' d' p'' w'' \<Longrightarrow> (p', w') \<Midarrow>d'\<Rightarrow>\<^sup>* (p'', w'') \<Longrightarrow> 
              P p w (d * d') p'' w''"
  shows "P p w d p' w'"
  using monoid_rtranclp_induct_rev[of l_step_relp "(p, w)" d "(p', w')" "\<lambda>pw d pw'. P (fst pw) (snd pw) d (fst pw') (snd pw')"] assms by force

lemma augmented_rules_1:
  assumes "(Init p', (w', d\<^sub>2), q) \<in> monoid_rtrancl (wts_to_monoidLTS ts)"
  assumes "(p, w) \<Midarrow>d\<^sub>1\<Rightarrow>\<^sup>* (p', w')"
  shows "((Init p, w), d\<^sub>1 * d\<^sub>2, q, []) \<in> monoid_rtrancl (WPDS.transition_rel augmented_WPDS_rules)"
  using assms(2,1)
  by (induct rule: wpds_lts_induct_rev)
     (simp_all add: augmented_rules_1_base augmented_rules_1_step)

lemma init_rule_is_Init:
  assumes "((p, w), d, p', w') \<in> WPDS.transition_rel init_rules"
  shows "is_Init p" and "is_Init p'"
  using assms unfolding init_rules_def l_step_relp_def
  by (auto simp add: WPDS.is_rule_def[unfolded WPDS_def, OF finite_init_rules, unfolded init_rules_def] 
                     WPDS.transition_rel.simps[unfolded WPDS_def, OF finite_init_rules, unfolded init_rules_def])

lemma init_rule_closure_is_Init:
  assumes "((p, w), d, p', w') \<in> monoid_rtrancl (WPDS.transition_rel init_rules)"
      and "is_Init p" 
  shows "is_Init p'"
  using assms
  by (cases "(p,w) = (p',w')", simp)
     (induct "(p,w)" d "(p',w')" rule: monoid_rtrancl.induct, auto simp add: init_rule_is_Init(2))

lemma aug_rules_to_init_from_init:
  assumes "((p, w), d, p', w') \<in> WPDS.transition_rel augmented_WPDS_rules"
      and "is_Init p'" and "d \<noteq> 0"
    shows "is_Init p"
  using assms(1) 
  unfolding WPDS.transition_rel.simps[unfolded WPDS_def, OF finite_augmented_WPDS_rules]
            WPDS.is_rule_def[unfolded WPDS_def, OF finite_augmented_WPDS_rules]
  unfolding augmented_WPDS_rules_def init_rules_def l_step_relp_def pop_ts_rules_def
  using no_transition_to_init[OF assms(2)] assms(3)
  by fastforce

lemma aug_rules_closure_to_init_from_init:
  assumes "((p, w), d, p', w') \<in> monoid_rtrancl (WPDS.transition_rel augmented_WPDS_rules)"
      and "is_Init p'" and "d \<noteq> 0"
    shows "is_Init p"
  using assms aug_rules_to_init_from_init
  by (induct rule: monoid_rtrancl_pair_induct_rev, simp) fastforce

lemma wpds_lts_init_induct_rev [consumes 1, case_names wpds_lts_base wpds_lts_step]:
  assumes "((Init p, w), d, Init p', w') \<in> monoid_rtrancl (WPDS.transition_rel init_rules)"
  assumes "(\<And>p w. P p w 1 p w)"
  assumes "\<And>p w d p' w' d' p'' w''. 
              ((Init p, w), d, (Init p', w')) \<in> WPDS.transition_rel init_rules \<Longrightarrow> 
              P p' w' d' p'' w'' \<Longrightarrow> 
              ((Init p', w'), d', (Init p'', w'')) \<in> monoid_rtrancl (WPDS.transition_rel init_rules) \<Longrightarrow> 
              P p w (d * d') p'' w''"
  shows "P p w d p' w'"
proof -
  { 
    fix p w d p' w' d' p'' w''
    assume a:"((p, w), d, p', w') \<in> WPDS.transition_rel init_rules"
       and b:"P (the_Ctr_Loc p') w' d' (the_Ctr_Loc p'') w''"
       and c:"((p', w'), d', p'', w'') \<in> monoid_rtrancl (WPDS.transition_rel init_rules)"
    then have ip':"is_Init p'" using init_rule_is_Init(2)[OF a] by blast
    then have ip'':"is_Init p''" using init_rule_closure_is_Init[OF c] by simp
    have  "P (the_Ctr_Loc p) w (d * d') (the_Ctr_Loc p'') w''"
      using state.collapse(1)[OF init_rule_is_Init(1)[OF a]] state.collapse(1)[OF ip'] state.collapse(1)[OF ip''] 
            assms(3) a b c
      by metis
  }
  then show ?thesis
    using monoid_rtrancl_induct_rev[of "(Init p, w)" d "(Init p', w')" "WPDS.transition_rel init_rules"
                                       "\<lambda>pw d pw'. P (the_Ctr_Loc (fst pw)) (snd pw) d (the_Ctr_Loc (fst pw')) (snd pw')", OF assms(1)]
    by (auto simp add: assms(2))
qed

lemma aug_to_init_rule:
  assumes "((Init p, w), d, Init p', w') \<in> WPDS.transition_rel augmented_WPDS_rules" and "d \<noteq> 0"
  shows "((Init p, w), d, Init p', w') \<in> WPDS.transition_rel init_rules"
  using assms 
  unfolding WPDS.transition_rel.simps[unfolded WPDS_def, OF finite_augmented_WPDS_rules]
            WPDS.is_rule_def[unfolded WPDS_def, OF finite_augmented_WPDS_rules]
            WPDS.transition_rel.simps[unfolded WPDS_def, OF finite_init_rules]
            WPDS.is_rule_def[unfolded WPDS_def, OF finite_init_rules]
  unfolding augmented_WPDS_rules_def pop_ts_rules_def
  using no_transition_to_init by simp

lemma aug_to_init_rule_closure:
  assumes "((p, w), d, p', w') \<in> monoid_rtrancl (WPDS.transition_rel augmented_WPDS_rules)" 
      and "d \<noteq> 0" and "is_Init p" and "is_Init p'"
  shows "((p, w), d, p', w') \<in> monoid_rtrancl (WPDS.transition_rel init_rules)"
  using assms
  apply (induct rule: monoid_rtrancl_pair_induct_rev, simp)
  subgoal for p w d p' w' d' p'' w''
    using aug_to_init_rule[of "the_Ctr_Loc p" w d "the_Ctr_Loc p'" w']
          aug_rules_closure_to_init_from_init[of p' w' d' p'' w'']
    using monoid_rtrancl_into_rtrancl_rev[of "(p,w)" d "(p',w')" "WPDS.transition_rel init_rules" d' "(p'',w'')"]
    by force
  done

lemma augmented_rules_2_a':
  assumes "((Init p, w), d, Init p', w') \<in> monoid_rtrancl (WPDS.transition_rel init_rules)"
  shows "(p,w) \<Midarrow>d\<Rightarrow>\<^sup>* (p',w')"
  using assms
  apply (induct rule: wpds_lts_init_induct_rev, simp)
  subgoal for p w d p' w' d' p'' w''
    using monoid_rtrancl_into_rtrancl_rev[of "(p, w)" d "(p', w')" transition_rel d' "(p'', w'')"] 
          init_rule_to_rule[of p w d p' w']
    unfolding l_step_relp_def monoid_rtrancl_def
    by fast
  done

lemma augmented_rules_2_a:
  assumes "((Init p, w), d, Init p', w') \<in> monoid_rtrancl (WPDS.transition_rel augmented_WPDS_rules)"
  assumes "d \<noteq> 0"
  shows "(p,w) \<Midarrow>d\<Rightarrow>\<^sup>* (p',w')"
  using assms aug_to_init_rule_closure augmented_rules_2_a' by force

lemma pop_to_ts:
  assumes "((p, a#w), d, p', w') \<in> WPDS.transition_rel pop_ts_rules"
  shows "(p, ([a], d), p') \<in> wts_to_monoidLTS ts" and "w = w'"
  using assms
  using WPDS.transition_rel.simps[unfolded WPDS_def, OF finite_pop_ts]
        WPDS.is_rule_def[unfolded WPDS_def, OF finite_pop_ts]
  unfolding pop_ts_rules_def wts_to_monoidLTS_def by auto

lemma pop_to_ts_closure:
  assumes "((p, w), d, q, []) \<in> monoid_rtrancl (WPDS.transition_rel pop_ts_rules)"
  shows "(p, (w, d), q) \<in> monoid_rtrancl (wts_to_monoidLTS ts)"
  using assms
proof (induct w arbitrary: p d)
  case Nil
  have "d = 1 \<and> p = q"
    by (cases rule: monoid_rtrancl_cases_rev[OF Nil])
       (auto simp add: WPDS.transition_rel.simps[unfolded WPDS_def, OF finite_pop_ts]
                       WPDS.is_rule_def[unfolded WPDS_def, OF finite_pop_ts])
  then show ?case using monoid_rtrancl_refl[of q "wts_to_monoidLTS ts", unfolded one_prod_def one_list_def] by blast
next
  case (Cons a w)
  then show ?case
    apply (cases rule: monoid_rtrancl_cases_rev[of "(p,a#w)" d "(q,[])" "WPDS.transition_rel pop_ts_rules"], simp_all) 
    using pop_to_ts[of p a w] monoid_rtrancl_into_rtrancl_rev[of p "([a],_)" _ "wts_to_monoidLTS ts" "(w,_)" q, unfolded mult_prod_def times_list_def]
    by fastforce
qed

lemma aug_to_pop_rule:
  assumes "((p, w), d, p', w') \<in> WPDS.transition_rel augmented_WPDS_rules" 
      and "d \<noteq> 0" and "is_Noninit p"
  shows "((p, w), d, p', w') \<in> WPDS.transition_rel pop_ts_rules" and "is_Noninit p'"
  using assms aug_rules_to_init_from_init[of p w d p' w']
  unfolding WPDS.transition_rel.simps[unfolded WPDS_def, OF finite_augmented_WPDS_rules]
            WPDS.is_rule_def[unfolded WPDS_def, OF finite_augmented_WPDS_rules]
            WPDS.transition_rel.simps[unfolded WPDS_def, OF finite_pop_ts]
            WPDS.is_rule_def[unfolded WPDS_def, OF finite_pop_ts]
  unfolding augmented_WPDS_rules_def init_rules_def 
  using state.exhaust_disc by auto

lemma aug_to_pop_rule':
  assumes "((p, w), d, p', w') \<in> WPDS.transition_rel augmented_WPDS_rules" 
      and "d \<noteq> 0" and "is_Noninit p'"
  shows "((p, w), d, p', w') \<in> WPDS.transition_rel pop_ts_rules"
  using assms aug_rules_to_init_from_init[of p w d p' w']
  unfolding WPDS.transition_rel.simps[unfolded WPDS_def, OF finite_augmented_WPDS_rules]
            WPDS.is_rule_def[unfolded WPDS_def, OF finite_augmented_WPDS_rules]
            WPDS.transition_rel.simps[unfolded WPDS_def, OF finite_pop_ts]
            WPDS.is_rule_def[unfolded WPDS_def, OF finite_pop_ts]
  unfolding augmented_WPDS_rules_def init_rules_def 
  using state.exhaust_disc by auto

lemma aug_to_pop_rule_closure:
  assumes "((p, w), d, p', w') \<in> monoid_rtrancl (WPDS.transition_rel augmented_WPDS_rules)"
      and "d \<noteq> 0" and "is_Noninit p"
  shows "((p, w), d, p', w') \<in> monoid_rtrancl (WPDS.transition_rel pop_ts_rules)"
  using assms
  apply (induct rule: monoid_rtrancl_pair_induct_rev, simp)
  subgoal for p w d p' w' d' p'' w''
    using aug_to_pop_rule[of p w d p' w']
          monoid_rtrancl_into_rtrancl_rev[of "(p,w)" d "(p',w')" "WPDS.transition_rel pop_ts_rules" d' "(p'',w'')"]
    by fastforce
  done

lemma augmented_rules_2_b:
  assumes "((p, w), d, p', w') \<in> WPDS.transition_rel augmented_WPDS_rules"
  assumes "((p', w'), d', q, []) \<in> monoid_rtrancl (WPDS.transition_rel augmented_WPDS_rules)"
  assumes "d \<noteq> 0" and "d' \<noteq> 0" and "is_Noninit p'"
    shows "(p, (w, d*d'), q) \<in> monoid_rtrancl (wts_to_monoidLTS ts)"
proof -
  obtain a where a_def:"a#w' = w" using aug_to_pop_rule'[OF assms(1,3,5)]
    unfolding WPDS.transition_rel.simps[unfolded WPDS_def, OF finite_pop_ts]
              WPDS.is_rule_def[unfolded WPDS_def, OF finite_pop_ts]
    unfolding pop_ts_rules_def by force
  then have A:"((p, a#w'), d, p', w') \<in> WPDS.transition_rel pop_ts_rules" 
    using aug_to_pop_rule'[OF assms(1,3,5)] by fastforce
  then have "(p, ([a], d), p') \<in> wts_to_monoidLTS ts" using pop_to_ts(1) by fast
  then have "(p, ([a], d) * (w', d'), q) \<in> monoid_rtrancl (wts_to_monoidLTS ts)"
    using monoid_rtrancl_into_rtrancl_rev[OF _ pop_to_ts_closure[OF aug_to_pop_rule_closure[OF assms(2,4,5)]]]
    by simp
  then show ?thesis by (simp add: mult_prod_def times_list_def a_def)
qed

lemma d_mult_not_zero: assumes "(d::'weight) * d' \<noteq> 0" shows "d \<noteq> 0" and "d' \<noteq> 0"
  using assms by auto

lemma augmented_rules_2_split:
  assumes "((Init p, w), d, Init p', w') \<in> monoid_rtrancl (WPDS.transition_rel augmented_WPDS_rules)"
  assumes "((Init p', w'), d', Noninit p'', w'') \<in> WPDS.transition_rel augmented_WPDS_rules"
  assumes "((Noninit p'', w''), d'', q, []) \<in> monoid_rtrancl (WPDS.transition_rel augmented_WPDS_rules)"
  assumes "d \<noteq> 0" and "d' \<noteq> 0" and "d'' \<noteq> 0" and "q \<in> finals"
  shows "\<exists>d\<^sub>2 d\<^sub>1 p' w' q. d * d' * d'' = d\<^sub>1 * d\<^sub>2 \<and> q \<in> finals \<and> (Init p', (w', d\<^sub>2), q) \<in> monoid_rtrancl (wts_to_monoidLTS ts) \<and> (p, w) \<Midarrow>d\<^sub>1\<Rightarrow>\<^sup>* (p', w')"
  using augmented_rules_2_a[OF assms(1,4)] augmented_rules_2_b[OF assms(2,3,5,6)]
  apply simp
  apply (rule exI[of _ "d' * d''"])
  apply (rule exI[of _ d])
  apply (simp add: ac_simps(4))
  apply (rule exI[of _ p'])
  apply (rule exI[of _ w'])
  apply (rule exI[of _ q])
  by (simp add: assms(7))

lemma augmented_rules_2_init_noninit_split:
  assumes "((p\<^sub>1, w\<^sub>1), d\<^sub>1, p\<^sub>2, w\<^sub>2) \<in> monoid_rtrancl (WPDS.transition_rel augmented_WPDS_rules)"
      and "is_Init p\<^sub>1" and "is_Noninit p\<^sub>2"
  shows "\<exists>d p' w' d' p'' w'' d''. d\<^sub>1 = d * d' * d'' \<and>
          ((p\<^sub>1, w\<^sub>1), d, Init p', w') \<in> monoid_rtrancl (WPDS.transition_rel augmented_WPDS_rules) \<and>
          ((Init p', w'), d', Noninit p'', w'') \<in> WPDS.transition_rel augmented_WPDS_rules \<and>
          ((Noninit p'', w''), d'', p\<^sub>2, w\<^sub>2) \<in> monoid_rtrancl (WPDS.transition_rel augmented_WPDS_rules)"
  using assms
  apply (induct rule: monoid_rtrancl_pair_induct_rev)
    using state.exhaust_disc
     apply fast
    subgoal for p w d p' w' d' p'' w''
      apply (cases "is_Init p'")
       apply simp
       apply safe
      subgoal for da p'a w'a d'a p''a w''a d''
        apply (rule exI[of _ "d * da"])
        apply (rule exI[of _ p'a])
        apply (rule exI[of _ w'a])
        apply (rule exI[of _ d'a])
        apply (rule exI[of _ p''a])
        apply (rule exI[of _ w''a])
        apply (rule exI[of _ d''])
        by (simp add: ac_simps(4) monoid_rtrancl_into_rtrancl_rev)
      using state.exhaust_disc[of p' "is_Noninit p'"]
      apply simp
      apply (rule exI[of _ 1])
      apply (rule exI[of _ "the_Ctr_Loc p"])
      apply (rule exI[of _ w])
      apply (rule exI[of _ d])
      apply (rule exI[of _ "the_St p'"])
      apply (rule exI[of _ w'])
      apply (rule exI[of _ d'])
      by auto
    done

lemma augmented_rules_2:
  assumes "((Init p, w), d, q, []) \<in> monoid_rtrancl (WPDS.transition_rel augmented_WPDS_rules)"
  assumes "d \<noteq> 0"
  assumes "q \<in> finals"
  shows "\<exists>d\<^sub>2 d\<^sub>1 p' w' q. d = d\<^sub>1 * d\<^sub>2 \<and> q \<in> finals \<and> (Init p', (w', d\<^sub>2), q) \<in> monoid_rtrancl (wts_to_monoidLTS ts) \<and> (p, w) \<Midarrow>d\<^sub>1\<Rightarrow>\<^sup>* (p', w')"
proof (cases "is_Init q")
  case True
  then show ?thesis
  using assms augmented_rules_2_a[of p w d "the_Ctr_Loc q" "[]"] monoid_rtrancl_refl[of q "wts_to_monoidLTS ts"]
  apply (simp add: one_prod_def one_list_def)
  apply (rule exI[of _ 1])
  apply (rule exI[of _ d], simp)
  apply (rule exI[of _ "the_Ctr_Loc q"])
  apply (rule exI[of _ "[]"])
  apply (rule exI[of _ "q"])
  by simp
next
  case False
  then have q_noninit:"is_Noninit q" using state.exhaust_disc by fast
  obtain d1 p' w' d' p'' w'' d'' where 
      "d = d1 * d' * d'' \<and>
       ((Init p, w), d1, Init p', w') \<in> monoid_rtrancl (WPDS.transition_rel augmented_WPDS_rules) \<and>
       ((Init p', w'), d', Noninit p'', w'') \<in> WPDS.transition_rel augmented_WPDS_rules \<and>
       ((Noninit p'', w''), d'', q, []) \<in> monoid_rtrancl (WPDS.transition_rel augmented_WPDS_rules)"
    using augmented_rules_2_init_noninit_split[OF assms(1) _ q_noninit, simplified] by fast
  then show ?thesis 
    using augmented_rules_2_split[of p w d1 p' w' d' p'' w'' d'' q] assms(2,3) by fastforce
qed

lemma exists_d_monoid_wts:
  assumes "w = [] \<longrightarrow> p = q"
  shows "\<exists>d. (p, (w, d), q) \<in> monoid_rtrancl (wts_to_monoidLTS ts)"
proof (cases "w = []")
  case True
  then show ?thesis using assms True
    using monoid_rtrancl_refl[of q "(wts_to_monoidLTS ts)", unfolded one_prod_def one_list_def]
    by blast
next
  case False
  then show ?thesis
  proof (induct w)
    case Nil
    then show ?case by simp
  next
    case (Cons a w')
    then show ?case
    proof (cases "w' = []")
      case True
      then show ?thesis
        using monoid_rtrancl_refl[of q "(wts_to_monoidLTS ts)", unfolded one_prod_def one_list_def]
              monoid_rtrancl_into_rtrancl_rev[of p "([a], ts $ (p, a, q))" q "wts_to_monoidLTS ts" "([],1)" q]
        unfolding mult_prod_def times_list_def wts_to_monoidLTS_def
        using exI[of _ "ts $ (p, a, q)"]
        by simp
    next
      case False
      then show ?thesis using Cons(1)[OF False]
        using monoid_rtrancl_into_rtrancl_rev[of p "([a], ts $ (p, a, p))" p "wts_to_monoidLTS ts" "(w',_)" q]
        unfolding mult_prod_def times_list_def wts_to_monoidLTS_def
        by auto
    qed
  qed
qed

lemma wpds_on_empty_stack:
  assumes "((p, []), 0, q, []) \<in> monoid_rtrancl (WPDS.transition_rel augmented_WPDS_rules)"
  shows "p = q"
  using assms
  by (cases rule: monoid_rtrancl_cases_rev[OF assms])
     (auto simp add: WPDS.transition_rel.simps[unfolded WPDS_def, OF finite_augmented_WPDS_rules])

lemma augmented_rules_2_d0:
  assumes "((Init p, w), 0, q, []) \<in> monoid_rtrancl (WPDS.transition_rel augmented_WPDS_rules)"
  assumes "q \<in> finals"
  shows "\<exists>d\<^sub>2 d\<^sub>1 p' w' q. q \<in> finals \<and> (Init p', (w', d\<^sub>2), q) \<in> monoid_rtrancl (wts_to_monoidLTS ts) \<and> (p, w) \<Midarrow>d\<^sub>1\<Rightarrow>\<^sup>* (p', w')"
  using exists_d_monoid_wts[of w "Init p" q] assms wpds_on_empty_stack 
  by (cases "w = [] \<longrightarrow> Init p = q") blast+

lemma augmented_rules_equal:
  "\<^bold>\<Sum> {d | d p'. p' \<in> finals \<and> ((Init p, w), d, p', []) \<in> monoid_rtrancl (WPDS.transition_rel augmented_WPDS_rules)} =
   \<^bold>\<Sum> {l * d | d l p' w' q. q \<in> finals \<and> (Init p', (w', d), q) \<in> monoid_rtrancl (wts_to_monoidLTS ts) \<and> (p, w) \<Midarrow> l \<Rightarrow>\<^sup>* (p', w')}" (is "\<^bold>\<Sum>?X = \<^bold>\<Sum>?Y")
proof - 
  have "countable {(x, y). ((Init p, w), x, y, []) \<in> monoid_rtrancl (WPDS.transition_rel augmented_WPDS_rules)}"
    using countable_subset[OF _ countable_f_on_set[OF countable_monoid_augmented, of "\<lambda>((_,_), x, y, _). (x, y)", simplified], 
                           of "{(x, y). ((Init p, w), x, y, []) \<in> monoid_rtrancl (WPDS.transition_rel augmented_WPDS_rules)}"]
    by fast
  then have cX:"countable ?X"
    using countable_f_on_P_Q_set2[of "\<lambda>d p'. ((Init p, w), d, p', []) \<in> monoid_rtrancl (WPDS.transition_rel augmented_WPDS_rules)" "\<lambda>d p'. d" "\<lambda>d p'. p' \<in> finals"]
    by blast
  obtain f::"('ctr_loc, 'noninit) state \<times> ('label list \<times> 'weight) \<times> ('ctr_loc, 'noninit) state \<Rightarrow> nat" 
    where f_inj:"inj_on f (monoid_rtrancl (wts_to_monoidLTS ts))"
    using countableE[OF countable_monoid_rtrancl[OF countable_wts[of ts]]] by fastforce
  then have f_inj':"\<And>x y z x' y' z'. (x, y, z) \<in> monoid_rtrancl (wts_to_monoidLTS ts) \<Longrightarrow> (x', y', z') \<in> monoid_rtrancl (wts_to_monoidLTS ts) \<Longrightarrow> f (x, y, z) = f (x', y', z') \<Longrightarrow> (x, y, z) = (x', y', z')"
    unfolding inj_on_def by blast
  have "countable {(x, y, z). (Init x, y, z) \<in> monoid_rtrancl (wts_to_monoidLTS ts)}"
    apply(rule countableI'[of "\<lambda>(x,y,z). f (Init x, y, z)"])
    unfolding inj_on_def
    using f_inj' by fast
  then have y1:"countable {(d,p',w'). \<exists>q. q \<in> finals \<and> (Init p', (w', d), q) \<in> monoid_rtrancl (wts_to_monoidLTS ts)}"
    using countable_f_on_P_Q_set3[of "\<lambda>p' w'd q. (Init p', w'd, q) \<in> monoid_rtrancl (wts_to_monoidLTS ts)" "\<lambda>p' w'd q. (p', w'd)" "\<lambda>p' w'd q. q \<in> finals"]
          countable_3_to_3_permutation
    by (fastforce simp add: dissect_set)
  have y2:"countable {(l,p',w'). (p, w) \<Midarrow> l \<Rightarrow>\<^sup>* (p', w')}"
    using countable_monoid_rtrancl[OF countable_transition_rel] 
    unfolding l_step_relp_def monoid_rtrancl_def
    using countable_3_to_2[of "monoid_rtranclp (\<lambda>x xa xb. (x, xa, xb) \<in> transition_rel)" "(p,w)"]
    by fastforce
  have cY:"countable ?Y"
    using countable_subset[OF _ countable_setcompr[OF countable_prod3[OF y1 y2], of "\<lambda>(d,l). l*d"], of ?Y]
    by fastforce
  have imp1:"\<And>y. \<exists>d\<^sub>2 d\<^sub>1. y = d\<^sub>1 * d\<^sub>2 \<and> (\<exists>p' w' q. q \<in> finals \<and> (Init p', (w', d\<^sub>2), q) \<in> monoid_rtrancl (wts_to_monoidLTS ts) \<and> (p, w) \<Midarrow> d\<^sub>1 \<Rightarrow>\<^sup>* (p', w')) \<Longrightarrow>
          \<exists>x. (\<exists>q. q \<in> finals \<and> ((Init p, w), x, q, []) \<in> monoid_rtrancl (WPDS.transition_rel augmented_WPDS_rules)) \<and> x \<le> y"
    using augmented_rules_1 by fast
  have imp2:"\<And>y. \<exists>q. q \<in> finals \<and> ((Init p, w), y, q, []) \<in> monoid_rtrancl (WPDS.transition_rel augmented_WPDS_rules) \<Longrightarrow>
          \<exists>x. (\<exists>d\<^sub>2 d\<^sub>1. x = d\<^sub>1 * d\<^sub>2 \<and> (\<exists>p' w' q. q \<in> finals \<and> (Init p', (w', d\<^sub>2), q) \<in> monoid_rtrancl (wts_to_monoidLTS ts) \<and> (p, w) \<Midarrow> d\<^sub>1 \<Rightarrow>\<^sup>* (p', w'))) \<and> x \<le> y"
    using augmented_rules_2 augmented_rules_2_d0 by fastforce
  then show ?thesis
    using SumInf_bounded_by_SumInf_if_members_bounded[OF cX cY] imp1
          SumInf_bounded_by_SumInf_if_members_bounded[OF cY cX] imp2
    by force
qed

lemma augmented_rules_match_W_automaton:
  "\<^bold>\<Sum>{d. augmented_rules_reach_empty finals p w d} = \<^bold>\<Sum>{d. reach_conf_in_W_automaton finals p w d}"
  using augmented_rules_equal reach_conf_in_W_automaton_unfold unfolding augmented_rules_reach_empty_def accepts_def
  by (simp add: monoidLTS.monoid_star_is_monoid_rtrancl[OF monoidLTS_instance]) meson

lemma unfold_pre_star_accepts_empty_automaton:
  "dioidLTS.weight_pre_star augmented_WPDS.transition_rel (accepts (K$ 0) finals) (Init p, w) =
   \<^bold>\<Sum>{d. augmented_rules_reach_empty finals p w d}"
proof -
  have "countable {d. monoid_rtranclp (monoidLTS.l_step_relp (WPDS.transition_rel augmented_WPDS_rules)) (Init p, w) (fst d) (snd d)}"
    using monoidLTS.countable_monoid_star_variant1[OF monoidLTS_instance, of "(Init p, w)"]
    by (metis (no_types, lifting) Collect_cong case_prod_beta)
  moreover have "\<And>(a::('ctr_loc, 'noninit) state) (b::'label list) d::'weight. a \<notin> finals \<or> b \<noteq> [] \<Longrightarrow> d * accepts (K$ 0) finals (a,b) = 0" 
    using WPDS.accepts_K0_iff[OF WPDS_instance, of finals] by fastforce
  moreover have "\<And>(a::('ctr_loc, 'noninit) state) (b::'label list) d::'weight. a \<in> finals \<and> b = [] \<Longrightarrow> d * accepts (K$ 0) finals (a,b) = d"
    using WPDS.accepts_K0_iff[OF WPDS_instance, of finals] by auto
  ultimately have 
     "\<^bold>\<Sum> {a * accepts (K$ 0) finals (aa, b) |a aa b.
          monoid_rtranclp (monoidLTS.l_step_relp (WPDS.transition_rel augmented_WPDS_rules)) (Init p, w) a (aa, b)} =
      \<^bold>\<Sum> {l |l a b. a \<in> finals \<and> b = [] \<and> monoid_rtranclp (monoidLTS.l_step_relp (WPDS.transition_rel augmented_WPDS_rules)) (Init p, w) l (a,b)}"
    using SumInf_split_Qor0[of "\<lambda>t. monoid_rtranclp (monoidLTS.l_step_relp (WPDS.transition_rel augmented_WPDS_rules)) (Init p, w) (fst t) (snd t)"
                               "\<lambda>t. (fst (snd t)) \<in> finals \<and> (snd (snd t)) = []"
                               "\<lambda>t. fst t * accepts (K$ 0) finals (snd t)"
                               "\<lambda>t. fst t"]
    by (safe, simp, meson)
  then show ?thesis 
    unfolding dioidLTS.weight_pre_star_def[OF dioidLTS_instance]
              augmented_rules_reach_empty_def monoidLTS.monoid_star_def[OF monoidLTS_instance]
    by simp metis
qed

abbreviation accepts_ts :: "('ctr_loc, 'noninit) state set \<Rightarrow> ('ctr_loc,'label) conf \<Rightarrow> 'weight" where
  "accepts_ts finals \<equiv> (\<lambda>(p,w). accepts ts finals (Init p, w))"

lemma augmented_rules_correct:
  "dioidLTS.weight_pre_star augmented_WPDS.transition_rel (accepts (K$ 0) finals) (Init p, w) = weight_pre_star (accepts_ts finals) (p, w)"
  using unfold_pre_star_accepts_empty_automaton augmented_rules_match_W_automaton[of finals p w]
  unfolding weight_pre_star_def reach_conf_in_W_automaton_def by simp meson

lemma pre_star_correctness: 
  assumes "saturation (augmented_WPDS.pre_star_rule) (K$ 0) A"
  shows "accepts A finals (Init p, w) = weight_pre_star (accepts_ts finals) (p,w)"
  using assms augmented_rules_correct augmented_WPDS.correctness by simp


definition intersw :: "('state, ('label list \<times> 'weight)) transition set \<Rightarrow> ('state, ('label list \<times> 'weight)) transition set \<Rightarrow> ('state \<times> 'state, ('label list \<times> 'weight)) transition set" where
  "intersw ts1 ts2 = {((p1, q1), (\<alpha>,dp * dq), (p2, q2))| p1 q1 \<alpha> dp dq p2 q2. (p1, (\<alpha>,dp), p2) \<in> ts1 \<and> (q1, (\<alpha>,dq), q2) \<in> ts2}"

(* Lav produkt med finfun istedet. *)


lemma zero_one_path:
  assumes "\<forall>(p1, (w,dp), p2) \<in> wts_to_monoidLTS ts1. dp = 1 \<or> dp = 0"
  assumes "(p1, (\<alpha>#w1',1), p2) \<in> monoid_rtrancl (wts_to_monoidLTS ts1)"
  shows "\<exists>p'. (p1, ([\<alpha>],1), p') \<in> wts_to_monoidLTS ts1 \<and> (p', (w1',1), p2) \<in> monoid_rtrancl (wts_to_monoidLTS ts1)"
  using assms
proof (induction w1' arbitrary: \<alpha> p1)
  case Nil
  then show ?case
    by (metis (no_types, lifting) monoid_rtrancl_wts_to_monoidLTS_cases_rev mstar_wts_empty_one mult.right_neutral)
next
  case (Cons \<alpha>' w1')
  obtain p1' d1 d2 where "(p1, ([\<alpha>], d1), p1') \<in> (wts_to_monoidLTS ts1)"
                         "(p1', (\<alpha>'#w1', d2), p2) \<in> monoid_rtrancl (wts_to_monoidLTS ts1)"
                         "1 = d1 * d2"
    using Cons(3) by (meson monoid_rtrancl_wts_to_monoidLTS_cases_rev)
  have "d1 = 1"
    using Cons.prems(1) \<open>(p1, ([\<alpha>], d1), p1') \<in> wts_to_monoidLTS ts1\<close> \<open>1 = d1 * d2\<close> by fastforce
  have "d2 = 1"
    using \<open>1 = d1 * d2\<close> \<open>d1 = 1\<close> by force
  have "(p1', (\<alpha>' # w1', 1), p2) \<in> monoid_rtrancl (wts_to_monoidLTS ts1)"
    using \<open>(p1', (\<alpha>' # w1', d2), p2) \<in> monoid_rtrancl (wts_to_monoidLTS ts1)\<close> \<open>d2 = 1\<close> by force
  then show ?case
    using \<open>(p1, ([\<alpha>], d1), p1') \<in> wts_to_monoidLTS ts1\<close> \<open>d1 = 1\<close> by blast
qed

lemma wtrans_star_inter1_1:
  assumes "(p1, (w,1), p2) \<in> monoid_rtrancl (wts_to_monoidLTS ts1)"
  assumes "(q1, (w,d), q2) \<in> monoid_rtrancl (wts_to_monoidLTS ts2)"
  assumes "\<forall>(p1, (w,dp), p2) \<in> wts_to_monoidLTS ts1. dp = 1 \<or> dp = 0"
  shows "((p1,q1), (w,d), (p2,q2)) \<in> monoid_rtrancl (intersw (wts_to_monoidLTS ts1) (wts_to_monoidLTS ts2))"
  using assms(1,2)
proof (induction w arbitrary: p1 q1 d)
  case (Cons \<alpha> w1')
  obtain p' where p'_p: "(p1, ([\<alpha>],1), p') \<in> wts_to_monoidLTS ts1 \<and> (p', (w1',1), p2) \<in> monoid_rtrancl (wts_to_monoidLTS ts1)"
    using Cons(2) using monoid_rtrancl_wts_to_monoidLTS_cases_rev by (meson assms(3) zero_one_path)
  obtain q' dq1q' dq'q2 where q'_p: "(q1, ([\<alpha>],dq1q'), q') \<in> wts_to_monoidLTS ts2 \<and> (q', (w1',dq'q2), q2) \<in> monoid_rtrancl (wts_to_monoidLTS ts2) \<and> d = dq1q' * dq'q2"
    using Cons(3) using monoid_rtrancl_wts_to_monoidLTS_cases_rev[of q1 \<alpha> w1' d q2 ts2] by meson
  have ind: "((p', q'), (w1', 1 * dq'q2), (p2, q2)) \<in> monoid_rtrancl (intersw (wts_to_monoidLTS ts1) (wts_to_monoidLTS ts2))"
  proof -
    have "Suc (length w1') = length (\<alpha>#w1')"
      by auto
    moreover
    have "(p', (w1',1), p2) \<in> monoid_rtrancl (wts_to_monoidLTS ts1)"
      using p'_p by simp
    moreover
    have "(q', (w1',dq'q2), q2) \<in> monoid_rtrancl (wts_to_monoidLTS ts2)"
      using q'_p by simp
    ultimately
    have "((p', q'), (w1', dq'q2), (p2, q2)) \<in> monoid_rtrancl (intersw (wts_to_monoidLTS ts1) (wts_to_monoidLTS ts2))"
      using Cons(1) using Cons(1) by auto
    then show "((p', q'), (w1', 1 * dq'q2), (p2, q2)) \<in> monoid_rtrancl (intersw (wts_to_monoidLTS ts1) (wts_to_monoidLTS ts2))"
      by auto
  qed
  moreover
  have "((p1, q1), ([\<alpha>], 1 * dq1q'), (p', q')) \<in> (intersw (wts_to_monoidLTS ts1) (wts_to_monoidLTS ts2))"
    using p'_p q'_p unfolding intersw_def by force
  ultimately
  have "((p1, q1), (\<alpha>#w1', (1 * dq1q') * (1 * dq'q2)), (p2, q2)) \<in> monoid_rtrancl (intersw (wts_to_monoidLTS ts1) (wts_to_monoidLTS ts2))"
    using monoid_rtrancl_into_rtrancl_rev[of "(p1,q1)" "([\<alpha>], 1 * dq1q')" "(p', q')"
        "intersw (wts_to_monoidLTS ts1) (wts_to_monoidLTS ts2)"
        "(w1', 1 * dq'q2)"
        "(p2, q2)"
        ]
    by (simp add: mult_prod_def times_list_def)
  moreover
  have "length ((\<alpha>#w1')) > 0"
    by auto
  moreover
  have "hd ((\<alpha>#w1')) = \<alpha>"
    by auto
  ultimately
  show ?case
    by (simp add: q'_p)
next
  case Nil
  then show ?case
    by (metis fst_conv monoid_rtrancl.monoid_rtrancl_refl monoid_star_w0 mstar_wts_empty_one one_list_def one_prod_def)
qed

lemma the_XY_lemma:
  assumes "(p1, (w,X), p2) \<in> monoid_rtrancl (wts_to_monoidLTS ts1)"
  assumes "(q1, (w,Y), q2) \<in> monoid_rtrancl (wts_to_monoidLTS ts2)"
  shows "\<exists>XY. ((p1,q1), (w,XY), (p2,q2)) \<in> monoid_rtrancl (intersw (wts_to_monoidLTS ts1) (wts_to_monoidLTS ts2))"
  sorry

lemma wtrans_star_inter1_0:
  assumes "(p1, (w,0), p2) \<in> monoid_rtrancl (wts_to_monoidLTS ts1)"
  assumes "(q1, (w,d), q2) \<in> monoid_rtrancl (wts_to_monoidLTS ts2)"
  assumes "\<forall>(p1, (w,dp), p2) \<in> wts_to_monoidLTS ts1. dp = 1 \<or> dp = 0"
  shows "((p1,q1), (w,0), (p2,q2)) \<in> monoid_rtrancl (intersw (wts_to_monoidLTS ts1) (wts_to_monoidLTS ts2))"
  using assms(1,2)
proof (induction w arbitrary: p1 q1 d)
  case (Cons \<alpha> w1')
  then have "(\<exists>p' d'. (p1, ([\<alpha>], 0), p') \<in> wts_to_monoidLTS ts1 \<and> (p', (w1',d'), p2) \<in> monoid_rtrancl (wts_to_monoidLTS ts1)) 
           \<or> (\<exists>p' d'. (p1, ([\<alpha>], d'), p') \<in> wts_to_monoidLTS ts1 \<and> (p', (w1',0), p2) \<in> monoid_rtrancl (wts_to_monoidLTS ts1))"
    sorry
  then show ?case
  proof 
    assume "(\<exists>p' d'. (p1, ([\<alpha>], 0), p') \<in> wts_to_monoidLTS ts1 \<and> (p', (w1',d'), p2) \<in> monoid_rtrancl (wts_to_monoidLTS ts1))"
    then obtain p' d' where
      "(p1, ([\<alpha>], 0), p') \<in> wts_to_monoidLTS ts1"
      "(p', (w1',d'), p2) \<in> monoid_rtrancl (wts_to_monoidLTS ts1)"     
      by auto
    moreover
    have "\<exists>q' X Y. (q1, ([\<alpha>], X), q') \<in> wts_to_monoidLTS ts2 \<and> (q', (w1', Y), q2) \<in> monoid_rtrancl (wts_to_monoidLTS ts2)"
      using Cons(3)
      using monoid_rtrancl_wts_to_monoidLTS_cases_rev by fastforce
    then obtain q' X Y where "(q1, ([\<alpha>], X), q') \<in> wts_to_monoidLTS ts2" "(q', (w1', Y), q2) \<in> monoid_rtrancl (wts_to_monoidLTS ts2)"
      by auto
    ultimately
    have START: "((p1,q1), ([\<alpha>], 0), (p',q')) \<in> intersw (wts_to_monoidLTS ts1) (wts_to_monoidLTS ts2)"
      unfolding intersw_def apply auto
      apply (rule exI[of _ 0])
      apply (rule exI[of _ X])
      apply auto
      done
    have "\<exists>XY. ((p',q'), (w1', XY), (p2,q2)) \<in> monoid_rtrancl (intersw (wts_to_monoidLTS ts1) (wts_to_monoidLTS ts2))"
      using the_XY_lemma[of p' w1' _ p2 ts1 q' _ q2 ts2]
        Cons
      using \<open>(p', (w1', d'), p2) \<in> monoid_rtrancl (wts_to_monoidLTS ts1)\<close> \<open>(q', (w1', Y), q2) \<in> monoid_rtrancl (wts_to_monoidLTS ts2)\<close> monoid_star_intros_step by blast
    then obtain XY where END: "((p',q'), (w1', XY), (p2,q2)) \<in> monoid_rtrancl (intersw (wts_to_monoidLTS ts1) (wts_to_monoidLTS ts2))"
      by blast
    have "((p1, q1), ([\<alpha>]*w1', 0*XY), (p2, q2)) \<in> monoid_rtrancl (intersw (wts_to_monoidLTS ts1) (wts_to_monoidLTS ts2))"
      using START END
      by (smt (verit, del_insts) fst_conv monoid_rtrancl_into_rtrancl_rev mult_prod_def snd_conv)
    then have "((p1, q1), ([\<alpha>]*w1', 0), (p2, q2)) \<in> monoid_rtrancl (intersw (wts_to_monoidLTS ts1) (wts_to_monoidLTS ts2))"
      by force
    then show ?thesis
      by (simp add: times_list_def)
  next
    assume "(\<exists>p' d. (p1, ([\<alpha>], d), p') \<in> wts_to_monoidLTS ts1 \<and> (p', (w1',0), p2) \<in> monoid_rtrancl (wts_to_monoidLTS ts1))"
    then obtain p' d' where
      "(p1, ([\<alpha>], d'), p') \<in> wts_to_monoidLTS ts1"
      "(p', (w1',0), p2) \<in> monoid_rtrancl (wts_to_monoidLTS ts1)"     
      by auto
    moreover
    have "\<exists>q' X Y. (q1, ([\<alpha>], X), q') \<in> wts_to_monoidLTS ts2 \<and> (q', (w1', Y), q2) \<in> monoid_rtrancl (wts_to_monoidLTS ts2)"
      using Cons(3)
      using monoid_rtrancl_wts_to_monoidLTS_cases_rev by fastforce
    then obtain q' X Y where "(q1, ([\<alpha>], X), q') \<in> wts_to_monoidLTS ts2" "(q', (w1', Y), q2) \<in> monoid_rtrancl (wts_to_monoidLTS ts2)"
      by auto
    ultimately
    have START: "\<exists>XY. ((p1,q1), ([\<alpha>], XY), (p',q')) \<in> intersw (wts_to_monoidLTS ts1) (wts_to_monoidLTS ts2)"
      unfolding intersw_def by auto
    have "\<exists>XY. ((p',q'), (w1', XY), (p2,q2)) \<in> monoid_rtrancl (intersw (wts_to_monoidLTS ts1) (wts_to_monoidLTS ts2))"
      using the_XY_lemma[of p' w1' _ p2 ts1 q' _ q2 ts2] Cons 
      sorry
    then obtain XY where END: "((p',q'), (w1', XY), (p2,q2)) \<in> monoid_rtrancl (intersw (wts_to_monoidLTS ts1) (wts_to_monoidLTS ts2))"
      by blast
    have "((p1, q1), ([\<alpha>]*w1', XY*0), (p2, q2)) \<in> monoid_rtrancl (intersw (wts_to_monoidLTS ts1) (wts_to_monoidLTS ts2))"
      using START END
      sorry
    then have "((p1, q1), ([\<alpha>]*w1', 0), (p2, q2)) \<in> monoid_rtrancl (intersw (wts_to_monoidLTS ts1) (wts_to_monoidLTS ts2))"
      by force
    then show ?thesis
      by (simp add: times_list_def)
  qed
next
  case Nil
  then show ?case
    by (metis fst_conv monoid_rtrancl.monoid_rtrancl_refl monoid_star_w0 mstar_wts_empty_one one_list_def one_prod_def)
qed

lemma inters_trans_star1_1:
  assumes "(p1q1, wd, p2q2) \<in> monoid_rtrancl (intersw (wts_to_monoidLTS ts1) (wts_to_monoidLTS ts2))"
  assumes "\<forall>(p1, (w,dp), p2) \<in> wts_to_monoidLTS ts1. dp = 1 \<or> dp = 0"
  assumes "snd wd\<noteq>0"
  shows "(fst p1q1, (fst wd,1), fst p2q2) \<in> monoid_rtrancl (wts_to_monoidLTS ts1)"
  using assms 
proof (induction rule: monoid_rtrancl.induct)
  case (monoid_rtrancl_refl pq)
  then show ?case
    using monoid_rtrancl.intros(1) by (metis (no_types, lifting) fst_conv one_prod_def)
next
  case (monoid_rtrancl_into_rtrancl pq1 wd12 pq2 wd23 pq3)
  define p1 where "p1 = fst pq1"
  define q1 where "q1 = snd pq1"
  define p2 where "p2 = fst pq2"
  define q2 where "q2 = snd pq2"
  define p3 where "p3 = fst pq3"
  define q3 where "q3 = snd pq3"
  define w12 where "w12 = fst wd12"
  define d12 where "d12 = snd wd12"
  define w23 where "w23 = fst wd23"
  define d23 where "d23 = snd wd23"
  have pq1_eq: "pq1 = (p1, q1)"
    unfolding p1_def q1_def by auto
  have pq2_eq: "pq2 = (p2, q2)"
    unfolding p2_def q2_def by auto
  have pq3_eq: "pq3 = (p3, q3)"
    unfolding p3_def q3_def by auto
  have wd12_eq: "wd12 = (w12,d12)"
    unfolding w12_def d12_def by auto
  have wd23_eq: "wd23 = (w23,d23)"
    unfolding w23_def d23_def by auto
  have pq2_eq: "pq2 = (p2, q2)"
    unfolding p2_def q2_def by auto
  have pq3_eq: "pq3 = (p3, q3)"
    unfolding p3_def q3_def by auto
  have wd12_eq: "wd12 = (w12,d12)"
    unfolding w12_def d12_def by auto
  have wd23_eq: "wd23 = (w23,d23)"
    unfolding w23_def d23_def by auto

  note indu = monoid_rtrancl_into_rtrancl[
      unfolded 
      p1_def[symmetric]
      q1_def[symmetric]
      p2_def[symmetric]
      q2_def[symmetric]
      p3_def[symmetric]
      q3_def[symmetric]
      w12_def[symmetric]
      d12_def[symmetric]
      pq1_eq
      pq2_eq
      pq3_eq
      wd12_eq
      wd23_eq
      ]
    
  have "d12 \<noteq> 0"
    using indu
    by (metis (no_types, lifting) mult_prod_def mult_zero_left snd_conv)
  have "d23 \<noteq> 0"
    using indu
    by (metis (no_types, lifting) mult_prod_def mult_zero_right snd_conv)

  have "snd (w12, d12) \<noteq> 0"
    using \<open>d12 \<noteq> 0\<close> by force

  have "(fst (p1, q1), (fst (w12, d12), 1), fst (p2, q2)) \<in> monoid_rtrancl (wts_to_monoidLTS ts1)"
    using indu \<open>snd (w12, d12) \<noteq> 0\<close> by fastforce

  then have "(p1, (w12, 1), p2) \<in> monoid_rtrancl (wts_to_monoidLTS ts1)"
    using indu by auto
  from indu(2) have "\<exists>d23p d23q. (p2, (w23, d23p), p3) \<in> (wts_to_monoidLTS ts1) \<and> (q2, (w23, d23q), q3) \<in> (wts_to_monoidLTS ts2)
                     \<and> d23p * d23q = d23"
    unfolding intersw_def by auto
  then obtain d23p d23q where
    "(p2, (w23, d23p), p3) \<in> (wts_to_monoidLTS ts1)"
    "(q2, (w23, d23q), q3) \<in> (wts_to_monoidLTS ts2)"
    "d23p * d23q = d23"
    by blast
  have "(p2, (w23, 1), p3) \<in> wts_to_monoidLTS ts1"
    using indu(2) \<open>d23 \<noteq> 0\<close> indu(4)
    using \<open>(p2, (w23, d23p), p3) \<in> wts_to_monoidLTS ts1\<close> \<open>d23p * d23q = d23\<close> by fastforce
  then
  have "(p1, (w12 * w23, 1), p3) \<in> monoid_rtrancl (wts_to_monoidLTS ts1)"
    using \<open>(fst (p1, q1), (fst (w12, d12), 1), fst (p2, q2)) \<in> monoid_rtrancl (wts_to_monoidLTS ts1)\<close>
    apply auto
    by (smt (verit, del_insts) fst_conv monoid_rtrancl.monoid_rtrancl_into_rtrancl mult.right_neutral mult_prod_def snd_conv)

  have "(p1, (w12, 1) * (w23, 1), p3) \<in> monoid_rtrancl (wts_to_monoidLTS ts1)"
    by (simp add: \<open>(p1, (w12 * w23, 1), p3) \<in> monoid_rtrancl (wts_to_monoidLTS ts1)\<close> mult_prod_def)
  then show ?case
    unfolding p1_def p3_def w12_def[symmetric] d12_def[symmetric] wd12_eq wd23_eq wd23_eq
    by (simp add: mult_prod_def)
qed

lemma inters_trans_star2_1:
  assumes "(p1q1, wd, p2q2) \<in> monoid_rtrancl (intersw (wts_to_monoidLTS ts1) (wts_to_monoidLTS ts2))"
  assumes "\<forall>(p1, (w,dp), p2) \<in> wts_to_monoidLTS ts1. dp = 1 \<or> dp = 0"
  assumes "snd wd\<noteq>0"
  shows "(snd p1q1, (fst wd,snd wd), snd p2q2) \<in> monoid_rtrancl (wts_to_monoidLTS ts2)"
  using assms
proof (induction rule: monoid_rtrancl.induct)
  case (monoid_rtrancl_refl pq)
  then show ?case
    using monoid_rtrancl.intros(1) by auto 
next
  case (monoid_rtrancl_into_rtrancl pq1 wd12 pq2 wd23 pq3)
  define p1 where "p1 = fst pq1"
  define q1 where "q1 = snd pq1"
  define p2 where "p2 = fst pq2"
  define q2 where "q2 = snd pq2"
  define p3 where "p3 = fst pq3"
  define q3 where "q3 = snd pq3"
  define w12 where "w12 = fst wd12"
  define d12 where "d12 = snd wd12"
  define w23 where "w23 = fst wd23"
  define d23 where "d23 = snd wd23"
  have pq1_eq: "pq1 = (p1, q1)"
    unfolding p1_def q1_def by auto
  have pq2_eq: "pq2 = (p2, q2)"
    unfolding p2_def q2_def by auto
  have pq3_eq: "pq3 = (p3, q3)"
    unfolding p3_def q3_def by auto
  have wd12_eq: "wd12 = (w12,d12)"
    unfolding w12_def d12_def by auto
  have wd23_eq: "wd23 = (w23,d23)"
    unfolding w23_def d23_def by auto
  have pq2_eq: "pq2 = (p2, q2)"
    unfolding p2_def q2_def by auto
  have pq3_eq: "pq3 = (p3, q3)"
    unfolding p3_def q3_def by auto
  have wd12_eq: "wd12 = (w12,d12)"
    unfolding w12_def d12_def by auto
  have wd23_eq: "wd23 = (w23,d23)"
    unfolding w23_def d23_def by auto

  note indu = monoid_rtrancl_into_rtrancl[
      unfolded 
      p1_def[symmetric]
      q1_def[symmetric]
      p2_def[symmetric]
      q2_def[symmetric]
      p3_def[symmetric]
      q3_def[symmetric]
      w12_def[symmetric]
      d12_def[symmetric]
      pq1_eq
      pq2_eq
      pq3_eq
      wd12_eq
      wd23_eq
      ]
    
  have "d12 \<noteq> 0"
    using indu
    by (metis (no_types, lifting) mult_prod_def mult_zero_left snd_conv)
  have "d23 \<noteq> 0"
    using indu
    by (metis (no_types, lifting) mult_prod_def mult_zero_right snd_conv)

  have "snd (w12, d12) \<noteq> 0"
    using \<open>d12 \<noteq> 0\<close> by force

  have "(snd (p1, q1), (fst (w12, d12), snd (w12, d12)), snd (p2, q2)) \<in> monoid_rtrancl (wts_to_monoidLTS ts2)"
    using indu \<open>snd (w12, d12) \<noteq> 0\<close> by blast

  then have "(q1, (w12, d12), q2) \<in> monoid_rtrancl (wts_to_monoidLTS ts2)"
    using indu by auto
  from indu(2) have "\<exists>d23p d23q. (p2, (w23, d23p), p3) \<in> (wts_to_monoidLTS ts1) \<and> (q2, (w23, d23q), q3) \<in> (wts_to_monoidLTS ts2)
                     \<and> d23p * d23q = d23"
    unfolding intersw_def by auto
  then obtain d23p d23q where f:
    "(p2, (w23, d23p), p3) \<in> (wts_to_monoidLTS ts1)"
    "(q2, (w23, d23q), q3) \<in> (wts_to_monoidLTS ts2)"
    "d23p * d23q = d23"
    by blast
  have "(p2, (w23, 1), p3) \<in> wts_to_monoidLTS ts1"
    using indu(2) \<open>d23 \<noteq> 0\<close> indu(4)
    using \<open>(p2, (w23, d23p), p3) \<in> wts_to_monoidLTS ts1\<close> \<open>d23p * d23q = d23\<close> by fastforce
  then
  have "(q1, (w12 * w23, d12 * d23), q3) \<in> monoid_rtrancl (wts_to_monoidLTS ts2)"
    using \<open>(snd (p1, q1), (fst (w12, d12), snd (w12, d12)), snd (p2, q2)) \<in> monoid_rtrancl (wts_to_monoidLTS ts2)\<close>
    apply auto
    by (smt (verit) f fst_conv monoid_rtrancl.simps mult_1 mult_prod_def snd_conv wts_label_d wts_label_exist)

  have "(q1, (w12, d12) * (w23, d23), q3) \<in> monoid_rtrancl (wts_to_monoidLTS ts2)"
    by (simp add: \<open>(q1, (w12 * w23, d12 * d23), q3) \<in> monoid_rtrancl (wts_to_monoidLTS ts2)\<close> mult_prod_def)
  then show ?case
    unfolding p1_def p3_def w12_def[symmetric] d12_def[symmetric] wd12_eq wd23_eq wd23_eq
    by (simp add: q1_def q3_def)
qed

lemma the_X_lemma:
  assumes "(p1q2, wd, p2q2) \<in> monoid_rtrancl (intersw (wts_to_monoidLTS ts1) (wts_to_monoidLTS ts2))"
  assumes "\<forall>(p1, (w,dp), p2) \<in> wts_to_monoidLTS ts1. dp = 1 \<or> dp = 0"
  shows "\<exists>X. (fst p1q2, (fst wd,X), fst p2q2) \<in> monoid_rtrancl (wts_to_monoidLTS ts1)"
  using assms 
proof (induction rule: monoid_rtrancl.induct)
  case (monoid_rtrancl_refl a)
  then show ?case
    by (metis (no_types, opaque_lifting) eq_fst_iff monoid_rtrancl.monoid_rtrancl_refl)
next
  case (monoid_rtrancl_into_rtrancl a w b l c)
  then show ?case
    apply (induction a)
    subgoal for a ab
      apply auto
      subgoal for Y
        apply (induction b)
        subgoal for a' b
          apply auto
          unfolding mult_prod_def
          apply auto
          unfolding intersw_def
          apply auto
          apply (induction w)
          apply auto
          unfolding mult_prod_def
          subgoal for aa bb \<alpha>\<alpha> ddpp ddqq pp22 qq22
            apply (rule exI[of _ "Y*ddpp"])
            by (smt (verit, del_insts) fst_conv monoid_rtrancl.monoid_rtrancl_into_rtrancl mult_prod_def snd_conv)
          done
        done
      done
    done
qed

lemma the_Y_lemma:
  assumes "(p1q2, wd, p2q2) \<in> monoid_rtrancl (intersw (wts_to_monoidLTS ts1) (wts_to_monoidLTS ts2))"
  assumes "\<forall>(p1, (w,dp), p2) \<in> wts_to_monoidLTS ts1. dp = 1 \<or> dp = 0"
  shows "\<exists>X. (snd p1q2, (fst wd,X), snd p2q2) \<in> monoid_rtrancl (wts_to_monoidLTS ts2)"
  using assms
proof (induction rule: monoid_rtrancl.induct)
  case (monoid_rtrancl_refl a)
  then show ?case
    by (metis (no_types, opaque_lifting) eq_fst_iff monoid_rtrancl.monoid_rtrancl_refl)
next
  case (monoid_rtrancl_into_rtrancl a w b l c)
  then show ?case
    apply (induction a)
    subgoal for a ab
      apply auto
      subgoal for Y
        apply (induction b)
        subgoal for a' b
          apply auto
          unfolding mult_prod_def
          apply auto
          unfolding intersw_def
          apply auto
          apply (induction w)
          apply auto
          unfolding mult_prod_def
          subgoal for aa bb \<alpha>\<alpha> ddpp ddqq pp22 qq22
            apply (rule exI[of _ "Y*ddqq"])
            by (smt (verit, del_insts) fst_conv monoid_rtrancl.monoid_rtrancl_into_rtrancl mult_prod_def snd_conv)
          done
        done
      done
    done
qed

lemma inters_trans_star__0:
  assumes "(p1q2, wd, p2q2) \<in> monoid_rtrancl (intersw (wts_to_monoidLTS ts1) (wts_to_monoidLTS ts2))"
  assumes "\<forall>(p1, (w,dp), p2) \<in> wts_to_monoidLTS ts1. dp = 1 \<or> dp = 0"
  assumes "snd wd=0"
  shows "(fst p1q2, (fst wd,0), fst p2q2) \<in> monoid_rtrancl (wts_to_monoidLTS ts1) \<or>
         (snd p1q2, (fst wd,0), snd p2q2) \<in> monoid_rtrancl (wts_to_monoidLTS ts2)"
  using assms 
proof (induction rule: monoid_rtrancl.induct)
  case (monoid_rtrancl_refl pq)
  from this(2) show ?case
    using monoid_rtrancl.intros(1) prod.collapse
    by (metis (no_types, lifting))
next
  case (monoid_rtrancl_into_rtrancl pq1 wd12 pq2 wd23 pq3)
  define p1 where "p1 = fst pq1"
  define q1 where "q1 = snd pq1"
  define p2 where "p2 = fst pq2"
  define q2 where "q2 = snd pq2"
  define p3 where "p3 = fst pq3"
  define q3 where "q3 = snd pq3"
  define w12 where "w12 = fst wd12"
  define d12 where "d12 = snd wd12"
  define w23 where "w23 = fst wd23"
  define d23 where "d23 = snd wd23"
  have pq1_eq: "pq1 = (p1, q1)"
    unfolding p1_def q1_def by auto
  have pq2_eq: "pq2 = (p2, q2)"
    unfolding p2_def q2_def by auto
  have pq3_eq: "pq3 = (p3, q3)"
    unfolding p3_def q3_def by auto
  have wd12_eq: "wd12 = (w12,d12)"
    unfolding w12_def d12_def by auto
  have wd23_eq: "wd23 = (w23,d23)"
    unfolding w23_def d23_def by auto
  have pq2_eq: "pq2 = (p2, q2)"
    unfolding p2_def q2_def by auto
  have pq3_eq: "pq3 = (p3, q3)"
    unfolding p3_def q3_def by auto
  have wd12_eq: "wd12 = (w12,d12)"
    unfolding w12_def d12_def by auto
  have wd23_eq: "wd23 = (w23,d23)"
    unfolding w23_def d23_def by auto

  note indu = monoid_rtrancl_into_rtrancl[
      unfolded 
      p1_def[symmetric]
      q1_def[symmetric]
      p2_def[symmetric]
      q2_def[symmetric]
      p3_def[symmetric]
      q3_def[symmetric]
      w12_def[symmetric]
      d12_def[symmetric]
      pq1_eq
      pq2_eq
      pq3_eq
      wd12_eq
      wd23_eq
      ]
  show ?case
  proof (cases "d12 = 0")
    case True
    then have "(fst (p1, q1), (fst (w12, d12), 0), fst (p2, q2)) \<in> monoid_rtrancl (wts_to_monoidLTS ts1) \<or>
    (snd (p1, q1), (fst (w12, d12), 0), snd (p2, q2)) \<in> monoid_rtrancl (wts_to_monoidLTS ts2)"
      using indu by auto
    then show ?thesis
    proof
      assume "(fst (p1, q1), (fst (w12, d12), 0), fst (p2, q2)) \<in> monoid_rtrancl (wts_to_monoidLTS ts1)"
      then have "(p1, (w12, 0), p2) \<in> monoid_rtrancl (wts_to_monoidLTS ts1)"
        by auto
      moreover
      have "\<exists>X. (p2, (w23, X), p3) \<in> monoid_rtrancl (wts_to_monoidLTS ts1)"
        using indu the_X_lemma
        by (smt (verit) lambda_one monoid_rtrancl.monoid_rtrancl_into_rtrancl monoid_rtrancl.monoid_rtrancl_refl p2_def p3_def pq2_eq pq3_eq w23_def wd23_eq) 
      ultimately
      have "(p1, ((w12 * w23), 0), p3) \<in> monoid_rtrancl (wts_to_monoidLTS ts1)"
        by (metis (no_types, lifting) True d12_def fst_conv lambda_zero monoid_rtrancl_rtrancl_into_rtrancl mult_prod_def wd12_eq)
      then have "(fst pq1, (fst (wd12 * wd23), 0), fst pq3) \<in> monoid_rtrancl (wts_to_monoidLTS ts1)"
        by (simp add: mult_prod_def p1_def p3_def w12_def w23_def)
      then show ?thesis
        by blast
    next
      assume "(snd (p1, q1), (fst (w12, d12), 0), snd (p2, q2)) \<in> monoid_rtrancl (wts_to_monoidLTS ts2)"
      then have "(q1, (w12, 0), q2) \<in> monoid_rtrancl (wts_to_monoidLTS ts2)"
        by auto
      moreover
      have "\<exists>X. (q2, (w23, X), q3) \<in> monoid_rtrancl (wts_to_monoidLTS ts2)"
        using indu the_Y_lemma
        by (smt (verit, del_insts) lambda_one monoid_rtrancl.monoid_rtrancl_into_rtrancl monoid_rtrancl.monoid_rtrancl_refl pq2_eq pq3_eq q2_def q3_def w23_def wd23_eq)
      ultimately
      have "(q1, ((w12 * w23), 0), q3) \<in> monoid_rtrancl (wts_to_monoidLTS ts2)"
        by (metis (no_types, lifting) True d12_def fst_conv lambda_zero monoid_rtrancl_rtrancl_into_rtrancl mult_prod_def wd12_eq)
      then have "(snd pq1, (fst (wd12 * wd23), 0), snd pq3) \<in> monoid_rtrancl (wts_to_monoidLTS ts2)"
        by (simp add: mult_prod_def q1_def q3_def w12_def w23_def)
      then show ?thesis
        by blast
    qed
  next
    case False
    note outer_outer_False = False
    obtain d23p d23q where d23p_d23q_p: "(p2, (w23, d23p), p3) \<in> wts_to_monoidLTS ts1"
      "(q2, (w23, d23q), q3) \<in> wts_to_monoidLTS ts2"
      "d23 = d23p * d23q"
      using indu(2) unfolding intersw_def by auto
    
    have d13zero: "d12 * d23 = 0"
      by (metis indu(5) mult_prod_def snd_conv)
    have d23_split: "d23 = d23p * d23q"
      using \<open>d23 = d23p * d23q\<close> .
    have d23p01: "d23p = 1 \<or> d23p = 0"
      using \<open>(p2, (w23, d23p), p3) \<in> wts_to_monoidLTS ts1\<close> indu(4) by fastforce (* By the corresponding edge being in ts1*)
    show ?thesis
    proof (cases "d23p = 0")
      case True
      have "(p2, (w23, 0), p3) \<in> monoid_rtrancl (wts_to_monoidLTS ts1)"
        using True d23p_d23q_p(1) monoid_star_intros_step by blast
      have "\<exists>X. (p1, (w12, X), p2) \<in> monoid_rtrancl (wts_to_monoidLTS ts1)"
        using indu(4) monoid_rtrancl_into_rtrancl.hyps(1) p1_def p2_def the_X_lemma w12_def by blast
      have "(p1, (w12 * w23, 0), p3) \<in> monoid_rtrancl (wts_to_monoidLTS ts1)"
        using d23p_d23q_p(1) indu(2)
        by (metis (no_types, lifting) True \<open>\<exists>X. (p1, (w12, X), p2) \<in> monoid_rtrancl (wts_to_monoidLTS ts1)\<close> d23_def d23_split fst_conv lambda_zero monoid_rtrancl.simps mult_prod_def mult_zero_right wd23_eq)
      then have "(fst pq1, (fst (wd12 * wd23), 0), fst pq3) \<in> monoid_rtrancl (wts_to_monoidLTS ts1)"
        unfolding p1_def w12_def w23_def p3_def mult_prod_def by auto
      then show ?thesis
        by auto
    next
      case False
      note outer_False = False
      show ?thesis
      proof (cases "d23q = 0")
        case True
        have "(q2, (w23, 0), q3) \<in> monoid_rtrancl (wts_to_monoidLTS ts2)"
          using True d23p_d23q_p(2) monoid_star_intros_step by blast
        have "\<exists>X. (q1, (w12, X), q2) \<in> monoid_rtrancl (wts_to_monoidLTS ts2)"
          using assms(2) indu(1) inters_trans_star2_1 outer_outer_False by fastforce
        have "(q1, (w12 * w23, 0), q3) \<in> monoid_rtrancl (wts_to_monoidLTS ts2)"
          using d23p_d23q_p indu
          by (metis (no_types, lifting) True \<open>\<exists>X. (q1, (w12, X), q2) \<in> monoid_rtrancl (wts_to_monoidLTS ts2)\<close> d23_def d23_split fst_conv monoid_rtrancl.simps mult_prod_def mult_zero_right wd23_eq)
        then have "(snd pq1, (fst (wd12 * wd23), 0), snd pq3) \<in> monoid_rtrancl (wts_to_monoidLTS ts2)"
          unfolding q1_def w12_def w23_def q3_def mult_prod_def by auto
        then show ?thesis
          by auto
      next
        case False
        have "d23p = 1"
          using d23p01 outer_False by auto
        then show ?thesis
          using outer_False outer_outer_False d23_split False
            d13zero
          by (smt (verit, del_insts) d12_def d23_def indu(1) indu(2) inters_trans_star2_1 lambda_one monoid_rtrancl.monoid_rtrancl_into_rtrancl monoid_rtrancl.monoid_rtrancl_refl monoid_rtrancl_into_rtrancl.prems(1) monoid_rtrancl_into_rtrancl.prems(2) monoid_rtrancl_rtrancl_into_rtrancl pq1_eq pq3_eq prod.collapse w23_def wd12_eq wd23_eq) 
          (* Wow... Er det fordi 0=1 eller noget? *)
      qed
    qed
  qed
qed

end

end
