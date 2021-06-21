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
(*    and c0 :: "('ctr_loc, 'label) conf" *)
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

interpretation LTS transition_rel .

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

type_synonym ('ctr_loc, 'label) sat_rule = "('ctr_loc, 'label) transition set \<Rightarrow> ('ctr_loc, 'label) transition set \<Rightarrow> bool"

datatype ('ctr_loc, 'label) ctr_loc =
  Ctr_Loc 'ctr_loc
  | Ctr_Loc_Ext 'ctr_loc 'label

find_theorems "finite UNIV"
find_theorems class.finite

instantiation  ctr_loc :: (finite, finite) finite begin

(* Man kunne vise at der ikke er en injection
   fra nat til vores type. *)

instance 
  apply standard
  apply (rule Finite_Set.finite.finite_UNIV)
  sorry
end

locale PDS_with_P_automaton = PDS P_locs \<Delta>
  for P_locs :: "'ctr_loc::finite set" and \<Delta> :: "('ctr_loc, 'label::finite) rule set"
    +
  fixes Q_locs :: "'ctr_loc set" 
(*    and trans :: "('ctr_loc, 'label) transition set" *)
    and F_locs :: "'ctr_loc set"
  assumes "P_locs \<subseteq> Q_locs"
(*    and "trans \<subseteq> Q_locs \<times> UNIV \<times> Q_locs" *)
    and "F_locs \<subseteq> Q_locs"
begin

interpretation LTS transition_rel .
notation step_relp (infix "\<Rightarrow>" 80)
notation step_starp (infix "\<Rightarrow>\<^sup>*" 80)

definition accepts :: "('ctr_loc, 'label) transition set \<Rightarrow> ('ctr_loc , 'label) conf \<Rightarrow> bool" where
  "accepts ts \<equiv> \<lambda>(p,w). (\<exists>q \<in> F_locs. (p,w,q) \<in> LTS.transition_star ts)"
  (* Here acceptance is defined for any p, but in the paper p has to be in P_locs *)

definition accepts_\<epsilon> :: "('ctr_loc, 'label option) transition set \<Rightarrow> ('ctr_loc , 'label) conf \<Rightarrow> bool" where
  "accepts_\<epsilon> ts \<equiv> \<lambda>(p,w). (\<exists>q \<in> F_locs. (p,w,q) \<in> LTS_\<epsilon>.transition_star_\<epsilon> ts)"

inductive epsilon_exp where
  "epsilon_exp [] []"
| "epsilon_exp ls ls' \<Longrightarrow> epsilon_exp (l#ls) (l#ls')"
| "epsilon_exp ls ls' \<Longrightarrow> epsilon_exp ls (epsilon#ls')"

definition accepts_epsilon :: "('ctr_loc, 'label) transition set \<Rightarrow> ('ctr_loc , 'label) conf \<Rightarrow> bool" where
  "accepts_epsilon ts \<equiv> \<lambda>(p,w). (\<exists>q \<in> F_locs. (p,w,q) \<in> LTS.transition_star ts)"

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


subsection \<open>Saturations\<close>

definition saturated :: "('ctr_loc, 'label) sat_rule \<Rightarrow> ('ctr_loc, 'label) transition set \<Rightarrow> bool" where
  "saturated rule ts \<longleftrightarrow> (\<nexists>ts'. rule ts ts')"

definition saturation :: "('ctr_loc, 'label) sat_rule \<Rightarrow> ('ctr_loc, 'label) transition set \<Rightarrow> ('ctr_loc, 'label) transition set \<Rightarrow> bool" where
  "saturation rule ts ts' \<longleftrightarrow> rule\<^sup>*\<^sup>* ts ts' \<and> saturated rule ts'"

subsection \<open>Pre*\<close>

inductive pre_star_rule :: "('ctr_loc, 'label) transition set \<Rightarrow> ('ctr_loc, 'label) transition set \<Rightarrow> bool" where (* TODO: p' should also be in P_locs I guess... *)
  add_trans: "(p, \<gamma>) \<hookrightarrow> (p', w) \<Longrightarrow> p \<in> P_locs \<Longrightarrow> (p', op_labels w, q) \<in> LTS.transition_star ts \<Longrightarrow> (p, \<gamma>, q) \<notin> ts \<Longrightarrow> pre_star_rule ts (ts \<union> {(p, \<gamma>, q)})"

lemma pre_star_rule_mono:
  "pre_star_rule ts ts' \<Longrightarrow> ts \<subset> ts'"
  unfolding pre_star_rule.simps by auto

lemma pre_star_rule_card_Suc: "pre_star_rule ts ts' \<Longrightarrow> card ts' = Suc (card ts)"
  unfolding pre_star_rule.simps by auto

lemma no_infinite: 
(* Maybe lazy lists are better? *)
  assumes "\<forall>i :: nat. pre_star_rule (tts i) (tts (Suc i))"
  shows "False"
proof -
  define f where "f i = card (tts i)" for i
  have f_Suc: "\<forall>i. f i < f (Suc i)"
    by (metis pre_star_rule_card_Suc assms f_def lessI)
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
  "\<not>(\<exists>tts. (\<forall>i :: nat. pre_star_rule (tts i) (tts (Suc i))))"
  using no_infinite by presburger

lemma saturation_exi: "\<exists>ts'. saturation pre_star_rule ts ts'"
proof (rule ccontr) (* TODO: it would be nice to avoid ccontr *)
  assume a: "\<nexists>ts'. saturation pre_star_rule ts ts'"
  define g where "g ts = (SOME ts'. pre_star_rule ts ts')" for ts
  define tts where "tts i = (g ^^ i) ts" for i
  have "\<forall>i :: nat. pre_star_rule\<^sup>*\<^sup>* ts (tts i) \<and> pre_star_rule (tts i) (tts (Suc i))"
  proof 
    fix i
    show "pre_star_rule\<^sup>*\<^sup>* ts (tts i) \<and> pre_star_rule (tts i) (tts (Suc i))"
    proof (induction i)
      case 0
      have "pre_star_rule ts (g ts)"
        by (metis g_def a rtranclp.rtrancl_refl saturation_def saturated_def someI)
      then show ?case
        using tts_def a saturation_def by auto 
    next
      case (Suc i)
      then have sat_Suc: "pre_star_rule\<^sup>*\<^sup>* ts (tts (Suc i))"
        by fastforce
      then have "pre_star_rule (g ((g ^^ i) ts)) (g (g ((g ^^ i) ts)))"
        by (metis Suc.IH tts_def g_def a r_into_rtranclp rtranclp_trans saturation_def saturated_def someI)
      then have "pre_star_rule (tts (Suc i)) (tts (Suc (Suc i)))"
        unfolding tts_def by simp
      then show ?case
        using sat_Suc by auto
    qed
  qed
  then have "\<forall>i. pre_star_rule (tts i) (tts (Suc i))"
    by auto
  then show False
    using no_infinite by auto
qed

(*

TODO: Prove that saturations are unique?

*)

lemma pre_star_rule_incr: "pre_star_rule A B \<Longrightarrow> A \<subseteq> B"
proof(induction rule: pre_star_rule.inducts)
  case (add_trans p \<gamma> p' w q rel)
  then show ?case 
    by auto
qed

lemma saturation_rtranclp_rule_incr: "pre_star_rule\<^sup>*\<^sup>* A B \<Longrightarrow> A \<subseteq> B"
proof (induction rule: rtranclp_induct)
  case base
  then show ?case by auto
next
  case (step y z)
  then show ?case
    using pre_star_rule_incr by auto
qed

lemma pre_star'_incr_transition_star:
  "pre_star_rule\<^sup>*\<^sup>* A A' \<Longrightarrow> LTS.transition_star A \<subseteq> LTS.transition_star A'"
  using mono_def LTS_transition_star_mono saturation_rtranclp_rule_incr by metis

lemma pre_star_lim'_incr_transition_star:
  "saturation pre_star_rule A A' \<Longrightarrow> LTS.transition_star A \<subseteq> LTS.transition_star A'"
  by (simp add: pre_star'_incr_transition_star saturation_def)

lemma lemma_3_1:
  assumes "p'w \<Rightarrow>\<^sup>* pv"
    and "pv \<in> language A"
    and "saturation pre_star_rule A A'"
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
    by force


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

lemma pre_star_rule_mono': "t \<in> LTS.transition_star rel \<Longrightarrow> pre_star_rule rel rel' \<Longrightarrow> t \<in> LTS.transition_star (rel')"
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

lemma lemma_3_2_a':
  assumes "\<nexists>q \<gamma> q'. (q, \<gamma>, q') \<in> A \<and> q' \<in> P_locs"
  assumes "pre_star_rule\<^sup>*\<^sup>* A A'"
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
    by (meson pre_star_rule.cases)

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
  assumes "pre_star_rule\<^sup>*\<^sup>* A A'"
  assumes "(p, w, q) \<in> LTS.transition_star A'"
  shows "\<exists>p' w' ss'. (p', w', q) \<in> LTS.transition_star A \<and> (p, w) \<Rightarrow>\<^sup>* (p', w')"
  using lemma_3_2_a' assms
  by (meson LTS.transition_star_states_transition_star LTS.transition_star_transition_star_states)

lemma lemma_3_2_a:
  assumes "\<nexists>q \<gamma> q'. (q, \<gamma>, q') \<in> A \<and> q' \<in> P_locs"
  assumes "saturation pre_star_rule A A'"
  assumes "(p, w, q) \<in> LTS.transition_star A'"
  shows "\<exists>p' w'. (p', w', q) \<in> LTS.transition_star A \<and> (p, w) \<Rightarrow>\<^sup>* (p', w')"
  using assms lemma_3_2_a'' saturation_def by auto 
  

lemmas lemma_3_2 = lemma_3_2_a lemma_3_2_b

theorem theorem_3_2:
  assumes "\<nexists>q \<gamma> q'. (q, \<gamma>, q') \<in> A \<and> q' \<in> P_locs"
  assumes "saturation pre_star_rule A A'"
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

end


