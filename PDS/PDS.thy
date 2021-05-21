theory PDS imports "../LTS" begin


section \<open>PDS\<close>

datatype 'label operation = pop | swap 'label | push 'label 'label
type_synonym ('ctr_loc, 'label) rule = "('ctr_loc \<times> 'label) \<times> ('ctr_loc \<times> 'label operation)"
type_synonym ('ctr_loc, 'label) conf = "'ctr_loc \<times> 'label list"


text \<open>We define push down systems.\<close>

locale PDS =
  (* 'ctr_loc is the type of control locations *)
  fixes P_locs :: "'ctr_loc::finite set" 
    and \<Delta> :: "('ctr_loc, 'label::finite) rule set"
    and c0 :: "('ctr_loc, 'label) conf"
  assumes \<Delta>_subset: "\<Delta> \<subseteq> (P_locs \<times> UNIV) \<times> (P_locs \<times> UNIV)"
begin

lemma finite_P_locs: "finite P_locs"
  by simp

fun config_wf :: "('ctr_loc, 'label) conf \<Rightarrow> bool" where
  "config_wf (c, l) \<longleftrightarrow> c \<in> P_locs"

primrec op_labels :: "'label operation \<Rightarrow> 'label list" where
  "op_labels pop = []"
| "op_labels (swap \<gamma>) = [\<gamma>]" 
| "op_labels (push \<gamma>  \<gamma>') = [\<gamma>, \<gamma>']"

definition is_rule :: "'ctr_loc \<times> 'label \<Rightarrow> 'ctr_loc \<times> 'label operation \<Rightarrow> bool" (infix "\<hookrightarrow>" 80) where
  "p\<gamma> \<hookrightarrow> p'w \<equiv> (p\<gamma>,p'w) \<in> \<Delta>"

inductive_set transition_rel :: "(('ctr_loc, 'label) conf \<times> 'label \<times> ('ctr_loc, 'label) conf) set" where
  "(p, \<gamma>) \<hookrightarrow> (p', w) \<Longrightarrow> ((p, \<gamma>#w'), \<gamma>, (p', (op_labels w)@w')) \<in> transition_rel"

interpretation LTS_init transition_rel c0 .

notation step_relp (infix "\<Rightarrow>" 80)
notation step_starp (infix "\<Rightarrow>\<^sup>*" 80)

lemma step_relp_def2:
  "(p, \<gamma>w') \<Rightarrow> (p',ww') \<longleftrightarrow> (\<exists>\<gamma> w' w. \<gamma>w' = \<gamma>#w' \<and> ww' = (op_labels w)@w' \<and> (p, \<gamma>) \<hookrightarrow> (p', w))"
  by (metis (no_types, lifting) PDS.transition_rel.intros PDS_axioms step_relp_def transition_rel.cases)



lemma step_relp'_P_locs1:
  assumes "(q1, x) \<Rightarrow> (q2, y)"
  shows "q1 \<in> P_locs"
proof -
  from assms have "\<exists>\<gamma> w. (q1, \<gamma>) \<hookrightarrow> (q2, w)"
    by (metis PDS.transition_rel.cases PDS_axioms step_relp_def)
  then show "?thesis"
    using \<Delta>_subset unfolding is_rule_def
    by auto
qed

lemma step_relp'_P_locs2:
  assumes "(q1, x) \<Rightarrow> (q2, y)"
  shows "q2 \<in> P_locs"
proof -
  from assms have "\<exists>\<gamma> w. (q1, \<gamma>) \<hookrightarrow> (q2, w)"
    by (metis PDS.transition_rel.cases PDS_axioms step_relp_def)
  then show "?thesis"
    using \<Delta>_subset unfolding is_rule_def
    by auto
qed

end


section \<open>PDS with P automaton\<close>

locale PDS_with_P_automaton = PDS P_locs \<Delta>
  for P_locs :: "'ctr_loc::finite set" and \<Delta> :: "('ctr_loc, 'label::finite) rule set"
    +
  fixes Q_locs :: "'ctr_loc set" 
    and trans :: "('ctr_loc, 'label) transition set" 
    and F_locs :: "'ctr_loc set"
  assumes "P_locs \<subseteq> Q_locs"
    and "trans \<subseteq> Q_locs \<times> UNIV \<times> Q_locs"
    and "F_locs \<subseteq> Q_locs"
begin

interpretation LTS_init transition_rel c0 .
notation step_relp (infix "\<Rightarrow>" 80)
notation step_starp (infix "\<Rightarrow>\<^sup>*" 80)

definition accepts :: "('ctr_loc, 'label) transition set \<Rightarrow> ('ctr_loc , 'label) conf \<Rightarrow> bool" where
  "accepts ts \<equiv> \<lambda>(p,w). (\<exists>q \<in> F_locs. (p,w,q) \<in> LTS.transition_star ts)"
  (* Here acceptance is defined for any p, but in the paper p has to be in P_locs *)

lemma accepts_mono[mono]: "mono accepts" (* Hmm.. what does this actually mean? *)
proof (rule, rule)
  fix c :: "('ctr_loc, 'label) conf"
  fix ts ts' :: "('ctr_loc, 'label) transition set"
  assume accepts_xa: "accepts ts c"
  assume tsts': "ts \<subseteq> ts'"
  obtain p l where pl_p: "c = (p,l)"
    by (cases c)
  obtain q where q_p:  "q \<in> F_locs \<and> (p, l, q) \<in> LTS.transition_star ts"
    using accepts_xa unfolding pl_p accepts_def by auto
  then have "(p, l, q) \<in> LTS.transition_star ts'"
    using tsts' LTS_transition_star_mono monoD by blast 
  then have "accepts ts' (p,l)"
    unfolding accepts_def using q_p by auto
  then show "accepts ts' c"
    unfolding pl_p .
qed

lemma accepts_cons: "(p, \<gamma>, q) \<in> ts \<Longrightarrow> accepts ts (q, w) \<Longrightarrow> accepts ts (p, \<gamma> # w)"
  using LTS.transition_star.transition_star_step accepts_def PDS_with_P_automaton_axioms by fastforce

lemma accepts_unfold: "accepts ts (p, \<gamma> # w) \<Longrightarrow> \<exists>q. (p, \<gamma>, q) \<in> ts \<and> accepts ts (q, w)"
  using LTS.transition_star_cons accepts_def case_prod_conv by force 

lemma accepts_unfoldn: "accepts ts (p, w' @ w) \<Longrightarrow> \<exists>q. (p, w', q) \<in> LTS.transition_star ts \<and> accepts ts (q, w)"
proof (induct w' arbitrary: p w)
  case Nil
  then show ?case by (metis LTS.transition_star.transition_star_refl append_Nil)
next
  case (Cons a w')
  then show ?case by (metis LTS.transition_star.transition_star_step accepts_unfold append_Cons)
qed

lemma accepts_append: "(p, w', q) \<in> LTS.transition_star ts \<Longrightarrow> accepts ts (q, w) \<Longrightarrow> accepts ts (p, w' @ w)"
proof (induct w' arbitrary: w p q)
  case Nil
  then show ?case 
    by (metis LTS.transition_star_empty append_Nil)
next
  case (Cons a w')
  then show ?case 
    by (metis LTS.transition_star_cons accepts_cons append_Cons)
qed

definition language :: "('ctr_loc, 'label) transition set \<Rightarrow> ('ctr_loc, 'label) conf set" where
  "language ts = {c. accepts ts c}"


subsection \<open>pre star\<close>

inductive saturation_rule :: "('ctr_loc, 'label) transition set \<Rightarrow> ('ctr_loc, 'label) transition set \<Rightarrow> bool" where (* TODO: p' should also be in P_locs I guess... *)
  add_trans: "(p, \<gamma>) \<hookrightarrow> (p', w) \<Longrightarrow> p \<in> P_locs \<Longrightarrow> (p', op_labels w, q) \<in> LTS.transition_star ts \<Longrightarrow> (p, \<gamma>, q) \<notin> ts \<Longrightarrow> saturation_rule ts (ts \<union> {(p, \<gamma>, q)})"

lemma saturation_rule_mono:
  "saturation_rule ts ts' \<Longrightarrow> ts \<subset> ts'"
  unfolding saturation_rule.simps by auto

definition saturated :: "('ctr_loc, 'label) transition set \<Rightarrow> bool" where
  "saturated ts \<longleftrightarrow> (\<nexists>ts'. saturation_rule ts ts')"

definition saturation :: "('ctr_loc, 'label) transition set \<Rightarrow> ('ctr_loc, 'label) transition set \<Rightarrow> bool" where
  "saturation ts ts' \<longleftrightarrow> saturation_rule\<^sup>*\<^sup>* ts ts' \<and> saturated ts'"

lemma saturation_rule_card_Suc: "saturation_rule ts ts' \<Longrightarrow> card ts' = Suc (card ts)"
  unfolding saturation_rule.simps by auto

lemma no_infinite: 
(* Maybe lazy lists are better? *)
  assumes "\<forall>i :: nat. saturation_rule (tts i) (tts (Suc i))"
  shows "False"
proof -
  define f where "f i = card (tts i)" for i
  have f_Suc: "\<forall>i. f i < f (Suc i)"
    by (metis saturation_rule_card_Suc assms f_def lessI)
  have "\<forall>i. \<exists>j. f j > i"
  proof 
    fix i
    show "\<exists>j. i < f j"
    proof(induction i)
      case 0
      then show ?case 
        by (metis f_Suc neq0_conv)
    next
      case (Suc i)
      then show ?case
        by (metis Suc_lessI f_Suc)
    qed
  qed
  then have "\<exists>j. f j > card (UNIV :: ('ctr_loc \<times> 'label \<times> 'ctr_loc) set)"
    by auto
  then show False
    by (metis card_seteq f_def finite_UNIV le_eq_less_or_eq nat_neq_iff subset_UNIV)
qed

lemma saturation_termination: 
(* Maybe lazy lists are better? *)
  "\<not>(\<exists>tts. (\<forall>i :: nat. saturation_rule (tts i) (tts (Suc i))))"
  using no_infinite by presburger

lemma saturation_exi: "\<exists>ts'. saturation ts ts'"
proof (rule ccontr) (* TODO: it would be nice to avoid ccontr *)
  assume a: "\<nexists>ts'. saturation ts ts'"
  define g where "g ts = (SOME ts'. saturation_rule ts ts')" for ts
  define tts where "tts i = (g ^^ i) ts" for i
  have "\<forall>i :: nat. saturation_rule\<^sup>*\<^sup>* ts (tts i) \<and> saturation_rule (tts i) (tts (Suc i))"
  proof 
    fix i
    show "saturation_rule\<^sup>*\<^sup>* ts (tts i) \<and> saturation_rule (tts i) (tts (Suc i))"
    proof (induction i)
      case 0
      have "saturation_rule ts (g ts)"
        by (metis g_def a rtranclp.rtrancl_refl saturation_def saturated_def someI)
      then show ?case
        using tts_def a saturation_def by auto 
    next
      case (Suc i)
      then have sat_Suc: "saturation_rule\<^sup>*\<^sup>* ts (tts (Suc i))"
        by fastforce
      then have "saturation_rule (g ((g ^^ i) ts)) (g (g ((g ^^ i) ts)))"
        by (metis Suc.IH tts_def g_def a r_into_rtranclp rtranclp_trans saturation_def saturated_def someI)
      then have "saturation_rule (tts (Suc i)) (tts (Suc (Suc i)))"
        unfolding tts_def by simp
      then show ?case
        using sat_Suc by auto
    qed
  qed
  then have "\<forall>i. saturation_rule (tts i) (tts (Suc i))"
    by auto
  then show False
    using no_infinite by auto
qed

(*

TODO: Prove that saturations are unique?

*)

lemma saturation_rule_incr: "saturation_rule A B \<Longrightarrow> A \<subseteq> B"
proof(induction rule: saturation_rule.inducts)
  case (add_trans p \<gamma> p' w q rel)
  then show ?case 
    by auto
qed

lemma saturation_rtranclp_rule_incr: "saturation_rule\<^sup>*\<^sup>* A B \<Longrightarrow> A \<subseteq> B"
proof (induction rule: rtranclp_induct)
  case base
  then show ?case by auto
next
  case (step y z)
  then show ?case
    using saturation_rule_incr by auto
qed

lemma pre_star'_incr_transition_star:
  "saturation_rule\<^sup>*\<^sup>* A A' \<Longrightarrow> LTS.transition_star A \<subseteq> LTS.transition_star A'"
  using mono_def LTS_transition_star_mono saturation_rtranclp_rule_incr by metis

lemma pre_star_lim'_incr_transition_star:
  "saturation A A' \<Longrightarrow> LTS.transition_star A \<subseteq> LTS.transition_star A'"
  by (simp add: pre_star'_incr_transition_star saturation_def)

lemma lemma_3_1:
  assumes "p'w \<Rightarrow>\<^sup>* pv"
    and "pv \<in> language A"
    and "saturation A A'"
  shows "accepts A' p'w"
  using assms
proof (induct rule: converse_rtranclp_induct)
  case base
  then have "\<exists>q \<in> F_locs. (fst pv, snd pv, q) \<in> LTS.transition_star A'"
    unfolding language_def using pre_star_lim'_incr_transition_star accepts_def by fastforce 
  then show ?case
    unfolding accepts_def by auto
next
  case (step p'w p''u) 
  define p' where "p' = fst p'w"
  define w  where "w = snd p'w"
  define p'' where "p'' = fst p''u"
  define u  where "u = snd p''u"
  have p'w_def: "p'w = (p', w)"
    using p'_def w_def by auto
  have p''u_def: "p''u = (p'', u)"
    using p''_def u_def by auto

  then have "accepts A' (p'', u)" 
    using step unfolding p''u_def by auto
  then obtain q where q_p: "q \<in> F_locs \<and> (p'', u, q) \<in> LTS.transition_star A'"
    unfolding accepts_def using p''_def u_def by auto
  then have "(p'', u, q) \<in> LTS.transition_star A'"
    by auto
  have "\<exists>\<gamma> w1 u1. w=\<gamma>#w1 \<and> u=op_labels u1@w1 \<and> (p', \<gamma>) \<hookrightarrow> (p'', u1)"
  proof -
    from step(1) obtain \<gamma> w1 where w_exp: "w=\<gamma>#w1"
      unfolding p''u_def p'w_def using list.exhaust by (meson LTS.step_relp_def transition_rel.cases) 
    from step(1) have "\<exists>u1. u=op_labels u1@w1 \<and> (p', \<gamma>) \<hookrightarrow> (p'', u1)" 
      unfolding step_relp_def p''u_def p'w_def w_exp using transition_rel.cases by force 
    then show "\<exists>\<gamma> w1 u1. w=\<gamma>#w1 \<and> u=op_labels u1@w1 \<and> (p', \<gamma>) \<hookrightarrow> (p'', u1)"
      using w_exp by auto
  qed
  then obtain \<gamma> w1 u1 where \<gamma>_w1_u1_p: "w=\<gamma>#w1 \<and> u=op_labels u1@w1 \<and> (p', \<gamma>) \<hookrightarrow> (p'', u1)"
    by blast

  have p'_P_locs: "p' \<in> P_locs"
    using p''u_def p'w_def step.hyps(1) step_relp'_P_locs1 by auto

  have "\<exists>q1. (p'', op_labels u1, q1) \<in> LTS.transition_star A' \<and> (q1, w1, q) \<in> LTS.transition_star A'"
    using q_p \<gamma>_w1_u1_p LTS.transition_star_split by auto

  then obtain q1 where q1_p: "(p'', op_labels u1, q1) \<in> LTS.transition_star A' \<and> (q1, w1, q) \<in> LTS.transition_star A'"
    by auto

  then have in_A': "(p', \<gamma>, q1) \<in> A'"
    using \<gamma>_w1_u1_p 
    using add_trans[of p' \<gamma> p'' u1 q1 A'] 
    using step.prems(2)
    using saturated_def
    using saturation_def[of ]
    using step.prems
    using p'_P_locs
    by blast

  then have "(p', \<gamma>#w1, q) \<in> LTS.transition_star A'"
    using in_A' transition_star_step q1_p
    by (meson LTS.transition_star.transition_star_step)
  then have t_in_A': "(p', w, q) \<in> LTS.transition_star A'"
    using \<gamma>_w1_u1_p by blast

  from q_p t_in_A' have "q \<in> F_locs \<and> (p', w, q) \<in> LTS.transition_star A'"
    using p'_def w_def by auto
  then show ?case
    unfolding accepts_def p'w_def using q_p by auto 
qed

lemma lemma_3_2_base: 
  "(p, w, q) \<in> LTS.transition_star rel \<Longrightarrow> \<exists>p' w'. (p, w) \<Rightarrow>\<^sup>* (p', w') \<and> (p', w', q) \<in> LTS.transition_star rel"
  by auto

lemma saturation_rule_mono': "t \<in> LTS.transition_star rel \<Longrightarrow> saturation_rule rel rel' \<Longrightarrow> t \<in> LTS.transition_star (rel')"
  using pre_star'_incr_transition_star by blast

lemma lemma_3_2_b_aux:
 (* Lemma from discussion with Morten 2 *)
  assumes "(p, w, ss, q) \<in> LTS.transition_star_states A"
  assumes "\<nexists>q \<gamma> q'. (q, \<gamma>, q') \<in> A \<and> q' \<in> P_locs"
  assumes "q \<in> P_locs"
  shows "w = [] \<and> p = q \<and> ss=[p]"
  using assms 
proof(induction rule: LTS.transition_star_states.induct[OF assms(1)])
  case (1 p)
  then show ?case by auto
next
  case (2 p \<gamma> q' w ss q)
  then show ?case by auto
qed

lemma lemma_3_2_b:
 (* The natural langauge formulation of this in the thesis is quite strange. *)
  assumes "(p, w, q) \<in> LTS.transition_star A"
  assumes "\<nexists>q \<gamma> q'. (q, \<gamma>, q') \<in> A \<and> q' \<in> P_locs"
  assumes "q \<in> P_locs"
  shows "w = [] \<and> p = q"
  using assms(2,3)
proof(induction rule: LTS.transition_star.induct[of p w q A,OF assms(1)]) (* Strange induction. Why "OF"? *)
  case (1 p)
  show ?case by auto
next
  case (2 p \<gamma> q' w q)
  then show ?case by blast
qed


lemma lemma_3_2_a'_Aux:
  assumes "(ss, w) \<in> LTS.path_with_word Ai"
  assumes "0 = count (transitions_of (ss, w)) (p1, \<gamma>, q')"
  assumes "Ai = Aiminus1 \<union> {(p1, \<gamma>, q')}"
  shows "(ss, w) \<in> LTS.path_with_word Aiminus1"
  using assms
proof (induction rule: LTS.path_with_word.induct[OF assms(1)])
  case (1 s)
  then show ?case
    by (simp add: LTS.path_with_word.path_with_word_refl)
next
  case (2 s' ss w s l)
  from 2(5) have "0 = count (transitions_of (s' # ss, w)) (p1, \<gamma>, q')"
    using count_next_0 by auto
  then have x: "(s' # ss, w) \<in> LTS.path_with_word Aiminus1"
    using 2 by auto
  have "(s, l, s') \<in> Aiminus1"
    using 2(2,5) assms(3) by force
  then show ?case 
    using x by (simp add: LTS.path_with_word.path_with_word_step) 
qed

lemma lemma_3_2_a'_Aux_3:
 (* This proof is a bit messy. *)
  assumes "(p, w, ss ,q) \<in> LTS.transition_star_states Ai"
  assumes "0 = count (transitions_of' (p, w, ss, q)) (p1, \<gamma>, q')"
  assumes "Ai = Aiminus1 \<union> {(p1, \<gamma>, q')}"
  shows "(p, w, ss, q) \<in> LTS.transition_star_states Aiminus1"
  using assms
proof (induction arbitrary: p rule: LTS.transition_star_states.induct[OF assms(1)])
  case (1 p)
  then show ?case
    by (metis LTS.transition_star_states.simps list.distinct(1))
next
  case (2 p' \<gamma>' q'' w ss q)
  have p_is_p': "p' = p"
    by (meson "2.prems"(1) LTS.transition_star_states.cases list.inject)
  { 
    assume a: "length ss > 0" 
    have not_found: "(p, \<gamma>', hd ss) \<noteq> (p1, \<gamma>, q')"
      using LTS.transition_star_states.cases count_next_hd list.sel(1) transitions_of'.simps
      using 2(4) 2(5) by (metis a hd_Cons_tl length_greater_0_conv) 
    have hdAI: "(p, \<gamma>', hd ss) \<in> Ai"
      by (metis "2.hyps"(1) "2.hyps"(2) LTS.transition_star_states.cases list.sel(1) p_is_p')
    have t: "(p, \<gamma>', hd ss) \<in> Aiminus1"
      using 2 hdAI not_found by force 
    have "(p, \<gamma>' # w, p' # ss, q) \<in> LTS.transition_star_states (Aiminus1 \<union> {(p1, \<gamma>, q')})"
      using "2.prems"(1) assms(3) by fastforce
    have ss_hd_tl: "hd ss # tl ss = ss"
      using a hd_Cons_tl by blast
    moreover
    have "(hd ss, w, ss, q) \<in> LTS.transition_star_states Ai"
      using ss_hd_tl "2.hyps"(2) using LTS.transition_star_states.cases
      by (metis list.sel(1))
    ultimately have "(hd ss, w, ss, q) \<in> LTS.transition_star_states Aiminus1"
      using ss_hd_tl using "2.IH" "2.prems"(2) not_found assms(3) p_is_p' count_transitions_of'_tails by (metis) 
    from this t have ?case
      using LTS.transition_star_states.intros(2)[of p \<gamma>' "hd ss" Aiminus1 w ss q] using p_is_p' by auto
  }
  moreover
  { 
    assume "length ss = 0"
    then have ?case
      using "2.hyps"(2) LTS.transition_star_states.cases by force
  }
  ultimately show ?case
    by auto
qed

lemma split_at_first_t:
  assumes "(p, w, ss, q) \<in> LTS.transition_star_states Ai"
  assumes "Suc j' = count (transitions_of' (p, w, ss, q)) (p1, \<gamma>, q')"
  assumes "(p1, \<gamma>, q') \<notin> Aiminus1"
  assumes "Ai = Aiminus1 \<union> {(p1, \<gamma>, q')}"
  shows "\<exists>u v u_ss v_ss. ss = u_ss @ v_ss \<and> w = u @ [\<gamma>] @ v \<and> (p, u, u_ss, p1) \<in> LTS.transition_star_states Aiminus1 \<and> (p1, [\<gamma>], q') \<in> LTS.transition_star Ai \<and> (q', v, v_ss, q) \<in> LTS.transition_star_states Ai"
  using assms
proof(induction arbitrary: p rule: LTS.transition_star_states.induct[OF assms(1)])
  case (1 p_add p)
  from 1(2) have "False"
    using count_empty_zero by auto
  then show ?case
    by auto
next
  case (2 p_add \<gamma>' q'_add w ss q p)
  then have p_add_p: "p_add = p"
    by (meson LTS.transition_star_states.cases list.inject)
  from p_add_p have f2_1: "(p, \<gamma>', q'_add) \<in> Ai"
    using 2(1) by auto
  from p_add_p have f2_4: "(p, \<gamma>' # w, p # ss, q) \<in> LTS.transition_star_states Ai"
    using 2(4) by auto  
  from p_add_p have f2_5: "Suc j' = count (transitions_of' (p, \<gamma>' # w, p # ss, q)) (p1, \<gamma>, q')"
    using 2(5) by auto
  note f2 = f2_1 2(2) 2(3) f2_4 f2_5 2(6) 2(7)
  show ?case
  proof(cases "(p, \<gamma>', q'_add) = (p1, \<gamma>, q')")
    case True
    define u :: "'b list" where "u = []"
    define u_ss :: "'a list" where "u_ss = [p]"
    define v where "v = w"
    define v_ss where "v_ss = ss"
    have "(p, u, u_ss, p1) \<in> LTS.transition_star_states Aiminus1"
      using f2 unfolding u_def u_ss_def using LTS.transition_star_states.intros
      using True by fastforce 
    have "(p1, [\<gamma>], q') \<in> LTS.transition_star Ai"
      using f2_1
      by (metis LTS.transition_star.transition_star_refl LTS.transition_star.transition_star_step True) 
    have "(q', v, v_ss, q) \<in> LTS.transition_star_states Ai"
      using f2(2)
      using True v_def v_ss_def by blast
    show ?thesis
      by (metis (no_types, lifting) Pair_inject True \<open>(p, u, u_ss, p1) \<in> LTS.transition_star_states Aiminus1\<close> \<open>(p1, [\<gamma>], q') \<in> LTS.transition_star Ai\<close> \<open>(q', v, v_ss, q) \<in> LTS.transition_star_states Ai\<close> append_Cons p_add_p self_append_conv2 u_def u_ss_def v_def v_ss_def)
  next
    case False
    have "hd ss = q'_add"
      by (metis LTS.transition_star_states.cases f2(2) list.sel(1))
    from this False have g: "Suc j' = count (transitions_of' (q'_add, w, ss, q)) (p1, \<gamma>, q')"
      using f2(5) by (cases ss) auto
    have "\<exists>u_ih v_ih u_ss_ih v_ss_ih. ss = u_ss_ih @ v_ss_ih \<and> w = u_ih @ [\<gamma>] @ v_ih \<and> (q'_add, u_ih, u_ss_ih, p1) \<in> LTS.transition_star_states Aiminus1 \<and> (p1, [\<gamma>], q') \<in> LTS.transition_star Ai \<and> (q', v_ih, v_ss_ih, q) \<in> LTS.transition_star_states Ai"
      using f2(3)[of q'_add, OF f2(2) g f2(6) f2(7)] .
    then obtain u_ih v_ih u_ss_ih v_ss_ih where ppp:
      "ss = u_ss_ih @ v_ss_ih" 
      "w = u_ih @ [\<gamma>] @ v_ih"
      "(q'_add, u_ih, u_ss_ih, p1) \<in> LTS.transition_star_states Aiminus1" 
      "(p1, [\<gamma>], q') \<in> LTS.transition_star Ai" 
      "(q', v_ih, v_ss_ih, q) \<in> LTS.transition_star_states Ai"
      by metis
    define v where "v = v_ih"
    define v_ss where "v_ss = v_ss_ih"
    define u where "u = \<gamma>' # u_ih"
    define u_ss where "u_ss = p # u_ss_ih"
    have "p_add # ss = u_ss @ v_ss"
      by (simp add: p_add_p ppp(1) u_ss_def v_ss_def)
    have "\<gamma>' # w = u @ [\<gamma>] @ v"
      using ppp(2) u_def v_def by auto
    have "(p, u, u_ss, p1) \<in> LTS.transition_star_states Aiminus1"
      using False LTS.transition_star_states.transition_star_states_step f2(7) f2_1 ppp(3) u_def u_ss_def by fastforce
    have "(p1, [\<gamma>], q') \<in> LTS.transition_star Ai"
      by (simp add: ppp(4))
    have "(q', v, v_ss, q) \<in> LTS.transition_star_states Ai"
      by (simp add: ppp(5) v_def v_ss_def)
    show ?thesis
      apply (rule_tac x=u in exI)
      apply (rule_tac x=v in exI)
      apply (rule_tac x=u_ss in exI)
      apply (rule_tac x=v_ss in exI)
      using \<open>(p, u, u_ss, p1) \<in> LTS.transition_star_states Aiminus1\<close> \<open>(q', v, v_ss, q) \<in> LTS.transition_star_states Ai\<close> \<open>\<gamma>' # w = u @ [\<gamma>] @ v\<close> \<open>p_add # ss = u_ss @ v_ss\<close> ppp(4) by blast
  qed
qed

lemma transition_star_states_mono:
  assumes "(p, w, ss, q) \<in> LTS.transition_star_states A1"
  assumes "A1 \<subseteq> A2"
  shows "(p, w, ss, q) \<in> LTS.transition_star_states A2"
  using assms 
proof (induction rule: LTS.transition_star_states.induct[OF assms(1)])
  case (1 p)
  then show ?case
    by (simp add: LTS.transition_star_states.transition_star_states_refl)
next
  case (2 p \<gamma> q' w ss q)
  then show ?case
    by (meson LTS.transition_star_states.transition_star_states_step in_mono)
qed

lemma transition_star_states_append:
  assumes "(p2, w2, w2_ss, q') \<in> LTS.transition_star_states Ai"
  assumes "(q', v, v_ss, q) \<in> LTS.transition_star_states Ai"
  shows "(p2, w2 @ v, w2_ss @ tl v_ss, q) \<in> LTS.transition_star_states Ai"
using assms proof (induction rule: LTS.transition_star_states.induct[OF assms(1)])
  case (1 p)
  then show ?case
    by (smt (verit, best) LTS.transition_star_states.cases append_Cons append_Nil list.sel(3))
next
  case (2 p \<gamma> q' w ss q)
  then show ?case
    using LTS.transition_star_states.transition_star_states_step by fastforce 
qed

lemma step_relp_append_aux:
  assumes "pu \<Rightarrow>\<^sup>* p1y"
  shows "(fst pu, snd pu @ v) \<Rightarrow>\<^sup>* (fst p1y, snd p1y @ v)"
  using assms 
proof (induction rule: rtranclp_induct)
  case base
  then show ?case by auto
next
  case (step p'w p1y)
  define p where "p = fst pu"
  define u where "u = snd pu"
  define p' where "p' = fst p'w"
  define w where "w = snd p'w"
  define p1 where "p1 = fst p1y"
  define y where "y = snd p1y"
  have step_1: "(p,u) \<Rightarrow>\<^sup>* (p',w)"
    by (simp add: p'_def p_def step.hyps(1) u_def w_def)
  have step_2: "(p',w) \<Rightarrow> (p1,y)"
    by (simp add: p'_def p1_def step.hyps(2) w_def y_def)
  have step_3: "(p, u @ v) \<Rightarrow>\<^sup>* (p', w @ v)"
    by (simp add: p'_def p_def step.IH u_def w_def)

  note step' = step_1 step_2 step_3

  from step'(2) have "\<exists>\<gamma> w' wa. w = \<gamma> # w' \<and> y = op_labels wa @ w' \<and> (p', \<gamma>) \<hookrightarrow> (p1, wa)"
    using step_relp_def2[of p' w p1 y] by auto
  then obtain \<gamma> w' wa where \<gamma>_w'_wa_p: " w = \<gamma> # w' \<and> y = op_labels wa @ w' \<and> (p', \<gamma>) \<hookrightarrow> (p1, wa)"
    by metis
  then have "(p, u @ v) \<Rightarrow>\<^sup>* (p1, y @ v)"
    by (metis (no_types, lifting) PDS.step_relp_def2 PDS_axioms append.assoc append_Cons rtranclp.simps step_3)
  then show ?case
    by (simp add: p1_def p_def u_def y_def)
qed

lemma step_relp_append:
  assumes "(p, u) \<Rightarrow>\<^sup>* (p1, y)"
  shows "(p, u @ v) \<Rightarrow>\<^sup>* (p1, y @ v)"
  using assms step_relp_append_aux by auto

lemma step_relp_append_empty:
  assumes "(p, u) \<Rightarrow>\<^sup>* (p1, [])"
  shows "(p, u @ v) \<Rightarrow>\<^sup>* (p1, v)"
  using step_relp_append[OF assms] by auto

lemma count_combine_transition_star_states:
  assumes "ss = u_ss @ v_ss \<and> w = u @ [\<gamma>] @ v"
  assumes "t = (p1, \<gamma>, q')"
  assumes "(p, u, u_ss, p1) \<in> LTS.transition_star_states A"
  assumes "(q', v, v_ss, q) \<in> LTS.transition_star_states B"
  shows "count (transitions_of' (p, w, ss, q)) t = count (transitions_of' (p, u, u_ss, p1)) t + 1 + count (transitions_of' (q', v, v_ss, q)) t"
proof -
  have v_ss_non_empt: "v_ss \<noteq> []"
    using LTS.transition_star_states.cases assms by force

  have u_ss_l: "length u_ss = Suc (length u)"
    using assms transition_star_states_length by metis

  have p1_u_ss:  "p1 = last u_ss"
    using assms
    using transition_star_states_last by metis

  have q'_v_ss: "q' = hd v_ss"
    using assms transition_star_states_hd by metis

  have one: "(if p1 = last u_ss \<and> q' = hd v_ss then 1 else 0) = 1"
    using p1_u_ss q'_v_ss by auto

  from count_append_transition_star_states_\<gamma>[of u_ss u v_ss p q \<gamma> q' v q p1 ] show ?thesis
    using assms(1) assms(2) assms(3) by (auto simp add: assms(3) one u_ss_l v_ss_non_empt)
qed
  

lemma lemma_3_2_a':
  assumes "\<nexists>q \<gamma> q'. (q, \<gamma>, q') \<in> A \<and> q' \<in> P_locs"
  assumes "saturation_rule\<^sup>*\<^sup>* A A'"
  assumes "(p, w, ss, q) \<in> LTS.transition_star_states A'"
  shows "\<exists>p' w' ss'. (p', w', ss', q) \<in> LTS.transition_star_states A \<and> (p, w) \<Rightarrow>\<^sup>* (p', w')"
  using assms(2) assms(1,3) 
proof (induction arbitrary: p q w ss rule: rtranclp_induct)
  case base
  then show ?case
    by auto
next
  case (step Aiminus1 Ai)

  from step(2) obtain p1 \<gamma> p2 w2 q' where p1_\<gamma>_p2_w2_q'_p:
    "Ai = Aiminus1 \<union> {(p1, \<gamma>, q')}" 
    "(p1, \<gamma>) \<hookrightarrow> (p2, w2)"
    "(p2, op_labels w2, q') \<in> LTS.transition_star Aiminus1"
    "(p1, \<gamma>, q') \<notin> Aiminus1"
    "p1 \<in> P_locs"
    by (meson saturation_rule.cases)

  note ss_p = step(5)

  define t where "t = (p1, \<gamma>, q')"
  define j where "j = count (transitions_of' (p, w, ss, q)) t"

  from j_def ss_p show ?case
  proof (induction j arbitrary: p q w ss)
    case 0
    have "(p, w, ss, q) \<in> LTS.transition_star_states Aiminus1"
      using lemma_3_2_a'_Aux_3
       p1_\<gamma>_p2_w2_q'_p(1) t_def 0 by fastforce
    then show ?case
      using step.IH step.prems(1) by metis
  next
    case (Suc j')
    have "\<exists>u v u_ss v_ss. ss = u_ss@v_ss \<and> w = u@[\<gamma>]@v \<and> (p,u,u_ss,p1) \<in> LTS.transition_star_states Aiminus1 \<and> (p1,[\<gamma>],q') \<in> LTS.transition_star Ai \<and> (q',v,v_ss,q) \<in> LTS.transition_star_states Ai"
      apply (rule split_at_first_t[of p w ss q Ai j' p1 \<gamma> q' Aiminus1])
      using Suc(2,3) t_def  p1_\<gamma>_p2_w2_q'_p(1,4) t_def by auto
    then obtain u v u_ss v_ss where u_v_u_ss_v_ss_p:
      "ss = u_ss@v_ss \<and> w = u@[\<gamma>]@v" 
      "(p,u,u_ss,p1) \<in> LTS.transition_star_states Aiminus1" 
      "(p1,[\<gamma>],q') \<in> LTS.transition_star Ai" 
      "(q',v,v_ss,q) \<in> LTS.transition_star_states Ai"
      by blast
    have II: "p1 \<in> P_locs"
      using p1_\<gamma>_p2_w2_q'_p by auto
    have "\<exists>p'' w'' ss''. (p'', w'', ss'', p1) \<in> LTS.transition_star_states A \<and> (p, u) \<Rightarrow>\<^sup>* (p'', w'')"
      using Suc(1)[of p u _ p1]
      using \<open>(p, u, u_ss, p1) \<in> LTS.transition_star_states Aiminus1\<close> step.IH step.prems(1) by blast 
    then obtain p'' w'' ss'' where "(p'', w'', ss'', p1) \<in> LTS.transition_star_states A" "(p, u) \<Rightarrow>\<^sup>* (p'', w'')"
      by blast
    from this lemma_3_2_b_aux  this(1) II have VIII: "(p, u) \<Rightarrow>\<^sup>* (p1, [])"
      using step.prems(1) by metis

    note IX = p1_\<gamma>_p2_w2_q'_p(2)
    note III = p1_\<gamma>_p2_w2_q'_p(3)
    from III have III_2: "\<exists>w2_ss. (p2, op_labels w2, w2_ss, q') \<in> LTS.transition_star_states Aiminus1"
      using LTS.transition_star_transition_star_states[of p2 "op_labels w2" q' Aiminus1] by auto
    then obtain w2_ss where III_2: "(p2, op_labels w2, w2_ss, q') \<in> LTS.transition_star_states Aiminus1"
      by blast

    from III have V: "(p2, op_labels w2, w2_ss, q') \<in> LTS.transition_star_states Aiminus1" "(q', v, v_ss, q) \<in> LTS.transition_star_states Ai"
      using III_2 \<open>(q', v, v_ss, q) \<in> LTS.transition_star_states Ai\<close> by auto

    define w2v where "w2v = op_labels w2 @ v"
    define w2v_ss where "w2v_ss = w2_ss @ tl v_ss"

    from V(1) have "(p2, op_labels w2, w2_ss, q') \<in> LTS.transition_star_states Ai"
      using transition_star_states_mono p1_\<gamma>_p2_w2_q'_p(1) by (metis Un_iff subsetI) 
    then have V_merged: "(p2, w2v, w2v_ss, q) \<in> LTS.transition_star_states Ai"
      using V(2) unfolding w2v_def w2v_ss_def using transition_star_states_append
      by metis

    have j'_count: "j' = count (transitions_of' (p2, w2v, w2v_ss, q)) t"
    proof -
      have "Suc j' = count (transitions_of' (p, u, u_ss, p1)) t + 1 + count (transitions_of' (q', v, v_ss, q)) t"
        using u_v_u_ss_v_ss_p(2) u_v_u_ss_v_ss_p(4)
        using count_combine_transition_star_states Suc(2) u_v_u_ss_v_ss_p(1) t_def by force
      then have "j' = count (transitions_of' (p, u, u_ss, p1)) t + count (transitions_of' (q', v, v_ss, q)) t"
        by auto
      then have "j' = 0 + count (transitions_of' (q', v, v_ss, q)) t"
        using avoid_count_zero
        by (metis p1_\<gamma>_p2_w2_q'_p(4) t_def u_v_u_ss_v_ss_p(2))
      then have xx: "j' = count (transitions_of' (p2, op_labels w2, w2_ss, q')) t  + count (transitions_of' (q', v, v_ss, q)) t"
        using V avoid_count_zero p1_\<gamma>_p2_w2_q'_p(4) t_def by fastforce 
      then show "j' = count (transitions_of' (p2, w2v, w2v_ss, q)) t"
      proof -
        have l_w2_ss: "length w2_ss = Suc (length (op_labels w2))" 
          by (meson III_2 transition_star_states_length)
        have v_ss_non_empty: "v_ss \<noteq> []"
          using LTS.transition_star_states.cases V(2) by force
        have last_hd: "last w2_ss = hd v_ss"
          by (metis III_2 transition_star_states_last V(2) transition_star_states_hd)
        have "count (transitions_of' ((p2, op_labels w2, w2_ss, q') @@\<acute> (q', v, v_ss, q))) (p1, \<gamma>, q')
          = count (transitions_of' (p2, w2v, w2v_ss, q))  (p1, \<gamma>, q')"
          by (simp add: w2v_def w2v_ss_def)
        then have "count (transitions_of' (p2, w2v, w2v_ss, q))  (p1, \<gamma>, q') = count (transitions_of' (p2, op_labels w2, w2_ss, q'))  (p1, \<gamma>, q') + count (transitions_of' (q', v, v_ss, q))  (p1, \<gamma>, q')"
          using count_append_transition_star_states[of w2_ss "op_labels w2" v_ss p2 q' q' v q p1 \<gamma> q' ]
          by (simp add: l_w2_ss v_ss_non_empty last_hd) 
        then have "count (transitions_of' (p2, w2v, w2v_ss, q)) t = count (transitions_of' (p2, op_labels w2, w2_ss, q')) t + count (transitions_of' (q', v, v_ss, q)) t"
          using t_def by auto
        then show ?thesis
          using xx by auto
      qed
    qed
    
    have "\<exists>p' w' ss'. (p', w', ss', q) \<in> LTS.transition_star_states A \<and> (p2, w2v) \<Rightarrow>\<^sup>* (p', w')"
      using Suc(1) using j'_count V_merged by auto
    then obtain p' w' ss' where p'_w'_ss'_p: "(p', w', ss', q) \<in> LTS.transition_star_states A" "(p2, w2v) \<Rightarrow>\<^sup>* (p', w')"
      by blast

    note X = p'_w'_ss'_p(2)

    from VIII IX X have
      "(p,w) = (p,u@[\<gamma>]@v)"
      "(p,u@[\<gamma>]@v) \<Rightarrow>\<^sup>* (p1,\<gamma>#v)"
      "(p1,\<gamma>#v) \<Rightarrow> (p2, w2v)"
      "(p2, w2v) \<Rightarrow>\<^sup>* (p', w')"
      subgoal
        using \<open>ss = u_ss @ v_ss \<and> w = u @ [\<gamma>] @ v\<close> apply blast
        done
      subgoal
        using VIII step_relp_append_empty apply auto
        done
      subgoal
        apply (metis IX LTS.step_relp_def transition_rel.intros w2v_def)
        done
      subgoal
        apply (simp add: X)
        done
      done

    have "(p, w) \<Rightarrow>\<^sup>* (p', w')"
      using X \<open>(p, u @ [\<gamma>] @ v) \<Rightarrow>\<^sup>* (p1, \<gamma> # v)\<close> \<open>(p, w) = (p, u @ [\<gamma>] @ v)\<close> \<open>(p1, \<gamma> # v) \<Rightarrow> (p2, w2v)\<close> by auto

    then have "(p', w', ss', q) \<in> LTS.transition_star_states A \<and> (p, w) \<Rightarrow>\<^sup>* (p', w')"
      using p'_w'_ss'_p(1) by auto
    then show ?case
      by metis
  qed
qed 

find_theorems transition_star transition_star_states

lemma lemma_3_2_a'':
  assumes "\<nexists>q \<gamma> q'. (q, \<gamma>, q') \<in> A \<and> q' \<in> P_locs"
  assumes "saturation_rule\<^sup>*\<^sup>* A A'"
  assumes "(p, w, q) \<in> LTS.transition_star A'"
  shows "\<exists>p' w' ss'. (p', w', q) \<in> LTS.transition_star A \<and> (p, w) \<Rightarrow>\<^sup>* (p', w')"
  using lemma_3_2_a' assms
  by (meson LTS.transition_star_states_transition_star LTS.transition_star_transition_star_states)

lemma lemma_3_2_a:
  assumes "\<nexists>q \<gamma> q'. (q, \<gamma>, q') \<in> A \<and> q' \<in> P_locs"
  assumes "saturation A A'"
  assumes "(p, w, q) \<in> LTS.transition_star A'"
  shows "\<exists>p' w'. (p', w', q) \<in> LTS.transition_star A \<and> (p, w) \<Rightarrow>\<^sup>* (p', w')"
  using assms lemma_3_2_a'' saturation_def by auto 
  

lemmas lemma_3_2 = lemma_3_2_a lemma_3_2_b

theorem theorem_3_2:
  assumes "\<nexists>q \<gamma> q'. (q, \<gamma>, q') \<in> A \<and> q' \<in> P_locs"
  assumes "saturation A A'"
  shows "{c. accepts A' c} = pre_star (language A)"
proof (rule; rule)

  fix c :: "'ctr_loc \<times> 'label list"
  define p where "p = fst c"
  define w where "w = snd c"
  assume "c \<in> pre_star (language A)"
  then have "(p,w) \<in> pre_star (language A)"
    unfolding p_def w_def by auto
  then have "\<exists>p' w'. (p',w') \<in> language A \<and> (p,w) \<Rightarrow>\<^sup>* (p',w')"
    unfolding pre_star_def by force
  then obtain p' w' where "(p',w') \<in> language A \<and> (p,w) \<Rightarrow>\<^sup>* (p',w')"
    by auto
  then have "\<exists>q \<in> F_locs. (p, w, q) \<in> LTS.transition_star A'"
    using lemma_3_1 assms(2) unfolding accepts_def by force
  then have "accepts A' (p,w)"
    unfolding accepts_def by auto
  then show "c \<in> {c. accepts A' c}"
    using p_def w_def by auto
next
  fix c :: "'ctr_loc \<times> 'label list"
  assume c_a: "c \<in> {w. accepts A' w}"
  define p where "p = fst c"
  define w where "w = snd c"
  from p_def w_def c_a have "accepts A' (p,w)"
    by auto
  then have "\<exists>q \<in> F_locs. (p, w, q) \<in> LTS.transition_star A'"
    unfolding accepts_def by auto
  then obtain q where q_p: "q \<in> F_locs" "(p, w, q) \<in> LTS.transition_star A'"
    by auto
  then have "\<exists>p' w'. (p,w) \<Rightarrow>\<^sup>* (p',w') \<and> (p', w', q) \<in> LTS.transition_star A"
    using lemma_3_2_a assms(1) assms(2) by metis
  then obtain p' w' where p'_w'_p: "(p,w) \<Rightarrow>\<^sup>* (p',w')" "(p', w', q) \<in> LTS.transition_star A"
    by auto
  then have "(p', w') \<in> language A"
    unfolding language_def unfolding accepts_def using q_p(1) by auto
  then have "(p,w) \<in> pre_star (language A)"
    unfolding pre_star_def using p'_w'_p(1) by auto
  then show "c \<in> pre_star (language A)"
    unfolding p_def w_def by auto
qed




 (*  I think there is a challenge here.
     In the proof he looks at << p \<midarrow>w\<rightarrow>*_i q >> as if it were a path. But there can be
     several paths like that. So I need to fix one.

     Hack: Make a different case distinction, namely on whether there is a
     << p \<midarrow>w\<rightarrow>*_(i-1) q >>
     Case True
       Then by induction
     Case False
       Any path uses t. In particular the one we know exists does.
       But what then, hmmm.... not sure. And what does "uses t" even mean.

  *)

end

end