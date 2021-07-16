theory PDS imports "../LTS" begin


section \<open>PDS\<close>

datatype 'label operation = pop | swap 'label | push 'label 'label
type_synonym ('ctr_loc, 'label) rule = "('ctr_loc \<times> 'label) \<times> ('ctr_loc \<times> 'label operation)"
type_synonym ('ctr_loc, 'label) conf = "'ctr_loc \<times> 'label list"


text \<open>We define push down systems.\<close>

locale PDS =
  (* 'ctr_loc is the type of control locations *)
  fixes \<Delta> :: "('ctr_loc, 'label::finite) rule set"
  
begin

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
  by (metis (no_types, lifting) PDS.transition_rel.intros step_relp_def transition_rel.cases)

end


section \<open>PDS with P automaton\<close>

type_synonym ('ctr_loc, 'label) sat_rule = "('ctr_loc, 'label) transition set \<Rightarrow> ('ctr_loc, 'label) transition set \<Rightarrow> bool"

datatype ('ctr_loc, 'state, 'label) state =
  is_Ctr_Loc: Ctr_Loc (the_Ctr_Loc: 'ctr_loc) (* p \<in> P *)
  | is_State: Ctr_Loc_St (the_St: 'state) (* q \<in> Q \<and> q \<notin> P *)
  | is_Ctr_Ext: Ctr_Loc_Ext (the_Ext_Ctr_Loc: 'ctr_loc) (the_Ext_Label: 'label) (* q\<^sub>p\<^sub>\<gamma> *)


find_theorems "finite UNIV"
find_theorems class.finite

lemma finite_ctr_locs:
  assumes "finite (UNIV :: 'ctr_loc set)"
  assumes "finite (UNIV :: 'state set)"
  assumes "finite (UNIV :: 'label set)"
  shows "finite (UNIV :: ('ctr_loc, 'state, 'label) state set)"
proof -
  define Ctr_Loc_Ext' :: "('ctr_loc * 'label) \<Rightarrow> ('ctr_loc, 'state, 'label) state" where 
    "Ctr_Loc_Ext' == \<lambda>(c :: 'ctr_loc, l:: 'label). Ctr_Loc_Ext c l"
  define Ctr_Loc' :: "'ctr_loc \<Rightarrow> ('ctr_loc, 'state, 'label) state" where
    "Ctr_Loc' = Ctr_Loc"
  define Ctr_Loc_St' :: "'state \<Rightarrow> ('ctr_loc, 'state, 'label) state" where
    "Ctr_Loc_St' = Ctr_Loc_St"

  have split: "UNIV = (Ctr_Loc' ` UNIV) \<union> (Ctr_Loc_St' ` UNIV) \<union> (Ctr_Loc_Ext' ` (UNIV :: (('ctr_loc * 'label) set)))"
    unfolding Ctr_Loc'_def Ctr_Loc_St'_def
  proof (rule; rule; rule; rule)
    fix x :: "('ctr_loc, 'state, 'label) state"
    assume "x \<in> UNIV"
    moreover
    assume "x \<notin> range Ctr_Loc_Ext'"
    moreover
    assume "x \<notin> range Ctr_Loc_St"
    ultimately
    show "x \<in> range Ctr_Loc"
      by (metis Ctr_Loc_Ext'_def prod.simps(2) range_eqI state.exhaust)
  qed

  have "finite (Ctr_Loc' ` (UNIV:: 'ctr_loc set))"
    using assms by auto
  moreover
  have "finite (Ctr_Loc_St' ` (UNIV:: 'state set))"
    using assms by auto
  moreover
  have "finite (UNIV :: (('ctr_loc * 'label) set))"
    using assms by (simp add: finite_Prod_UNIV)
  then have "finite (Ctr_Loc_Ext' ` (UNIV :: (('ctr_loc * 'label) set)))"
    by auto
  ultimately
  show "finite (UNIV :: ('ctr_loc, 'state, 'label) state set)"
    unfolding split by auto
qed

instantiation state :: (finite, finite, finite) finite begin

instance by standard (simp add: finite_ctr_locs)

end


locale PDS_with_P_automaton = PDS \<Delta>
  for \<Delta> :: "('ctr_loc::finite, 'label::finite) rule set"
    +
  fixes F_locs :: "('ctr_loc, 'state::finite, 'label) state set"
  assumes "\<not>(\<exists>f\<in>F_locs. is_Ctr_Ext f)"
begin

definition P_locs :: "('ctr_loc, 'state, 'label) state set" where 
  "P_locs = {q. is_Ctr_Loc q}"

definition Old_Aut_states :: "('ctr_loc, 'state, 'label) state set" where
  "Old_Aut_states = {q. is_State q}"

definition New_Aut_states :: "('ctr_loc, 'state, 'label) state set" where
  "New_Aut_states = {q. is_Ctr_Ext q}"

interpretation LTS transition_rel .
notation step_relp (infix "\<Rightarrow>" 80)
notation step_starp (infix "\<Rightarrow>\<^sup>*" 80)

definition accepts :: "(('ctr_loc, 'state, 'label) state, 'label) transition set \<Rightarrow> ('ctr_loc , 'label) conf \<Rightarrow> bool" where
  "accepts ts \<equiv> \<lambda>(p,w). (\<exists>q \<in> F_locs. (Ctr_Loc p,w,q) \<in> LTS.transition_star ts)"

definition accepts_\<epsilon> :: "(('ctr_loc, 'state, 'label) state, 'label option) transition set \<Rightarrow> ('ctr_loc, 'label) conf \<Rightarrow> bool" where
  "accepts_\<epsilon> ts \<equiv> \<lambda>(p,w). (\<exists>q \<in> F_locs. (Ctr_Loc p,w,q) \<in> LTS_\<epsilon>.transition_star_\<epsilon> ts)"

abbreviation \<epsilon> :: "'label option" where
  "\<epsilon> == None"

lemma accepts_mono[mono]: "mono accepts" (* Hmm.. what does this actually mean? *)
proof (rule, rule)
  fix c :: "('ctr_loc, 'label) conf"
  fix ts ts' :: "(('ctr_loc, 'state, 'label) state, 'label) transition set"
  assume accepts_xa: "accepts ts c"
  assume tsts': "ts \<subseteq> ts'"
  obtain p l where pl_p: "c = (p,l)"
    by (cases c)
  obtain q where q_p:  "q \<in> F_locs \<and> (Ctr_Loc p, l, q) \<in> LTS.transition_star ts"
    using accepts_xa unfolding pl_p accepts_def by auto
  then have "(Ctr_Loc p, l, q) \<in> LTS.transition_star ts'"
    using tsts' LTS_transition_star_mono monoD by blast 
  then have "accepts ts' (p,l)"
    unfolding accepts_def using q_p by auto
  then show "accepts ts' c"
    unfolding pl_p .
qed

lemma accepts_cons: "(Ctr_Loc p, \<gamma>, Ctr_Loc p') \<in> ts \<Longrightarrow> accepts ts (p', w) \<Longrightarrow> accepts ts (p, \<gamma> # w)"
  using LTS.transition_star.transition_star_step accepts_def by fastforce 

definition language :: "(('ctr_loc, 'state, 'label) state, 'label) transition set \<Rightarrow> ('ctr_loc, 'label) conf set" where
  "language ts = {c. accepts ts c}"

definition language_\<epsilon> :: "(('ctr_loc, 'state, 'label) state, 'label option) transition set \<Rightarrow> ('ctr_loc, 'label) conf set" where
  "language_\<epsilon> ts = {c. accepts_\<epsilon> ts c}"


subsection \<open>Saturations\<close>

(* We use 'l for supporting both 'label and 'label option. We use 'c for supporting both 'ctr_loc and ('ctr_loc, 'label) ctr_loc *)
definition saturated :: "('c, 'l) sat_rule \<Rightarrow> ('c, 'l) transition set \<Rightarrow> bool" where
  "saturated rule ts \<longleftrightarrow> (\<nexists>ts'. rule ts ts')"

definition saturation :: "('c, 'l) sat_rule \<Rightarrow> ('c, 'l) transition set \<Rightarrow> ('c, 'l) transition set \<Rightarrow> bool" where
  "saturation rule ts ts' \<longleftrightarrow> rule\<^sup>*\<^sup>* ts ts' \<and> saturated rule ts'"

subsection \<open>Saturation rules\<close>

inductive pre_star_rule :: "(('ctr_loc, 'state, 'label) state, 'label) transition set \<Rightarrow> (('ctr_loc, 'state, 'label) state, 'label) transition set \<Rightarrow> bool" where 
  add_trans: "(p, \<gamma>) \<hookrightarrow> (p', w) \<Longrightarrow> (Ctr_Loc p', op_labels w, q) \<in> LTS.transition_star ts \<Longrightarrow> (Ctr_Loc p, \<gamma>, q) \<notin> ts \<Longrightarrow> pre_star_rule ts (ts \<union> {(Ctr_Loc p, \<gamma>, q)})"

inductive post_star_rules :: "(('ctr_loc, 'state, 'label) state, 'label option) transition set \<Rightarrow> (('ctr_loc, 'state, 'label) state, 'label option) transition set \<Rightarrow> bool" where
  add_trans_pop: "(p, \<gamma>) \<hookrightarrow> (p', pop) \<Longrightarrow> (Ctr_Loc p, [\<gamma>], q) \<in> LTS_\<epsilon>.transition_star_\<epsilon> ts \<Longrightarrow> (Ctr_Loc p', \<epsilon>, q) \<notin> ts \<Longrightarrow> post_star_rules ts (ts \<union> {(Ctr_Loc p', \<epsilon>, q)})"
| add_trans_swap: "(p, \<gamma>) \<hookrightarrow> (p', swap \<gamma>') \<Longrightarrow> (Ctr_Loc p, [\<gamma>], q) \<in> LTS_\<epsilon>.transition_star_\<epsilon> ts \<Longrightarrow> (Ctr_Loc p', Some \<gamma>', q) \<notin> ts \<Longrightarrow> post_star_rules ts (ts \<union> {(Ctr_Loc p', Some \<gamma>', q)})"
| add_trans_push_1: "(p, \<gamma>) \<hookrightarrow> (p', push \<gamma>' \<gamma>'') \<Longrightarrow> (Ctr_Loc p, [\<gamma>], q) \<in> LTS_\<epsilon>.transition_star_\<epsilon> ts \<Longrightarrow> (Ctr_Loc p', Some \<gamma>', Ctr_Loc_Ext p' \<gamma>') \<notin> ts \<Longrightarrow> post_star_rules ts (ts \<union> {(Ctr_Loc p', Some \<gamma>', Ctr_Loc_Ext p' \<gamma>')})"
| add_trans_push_2: "(p, \<gamma>) \<hookrightarrow> (p', push \<gamma>' \<gamma>'') \<Longrightarrow> (Ctr_Loc p, [\<gamma>], q) \<in> LTS_\<epsilon>.transition_star_\<epsilon> ts \<Longrightarrow> (Ctr_Loc_Ext p' \<gamma>', Some \<gamma>'', q) \<notin> ts \<Longrightarrow> (Ctr_Loc p', Some \<gamma>', Ctr_Loc_Ext p' \<gamma>') \<in> ts \<Longrightarrow> post_star_rules ts (ts \<union> {(Ctr_Loc_Ext p' \<gamma>', Some \<gamma>'', q)})"

lemma pre_star_rule_mono:
  "pre_star_rule ts ts' \<Longrightarrow> ts \<subset> ts'"
  unfolding pre_star_rule.simps by auto

lemma post_star_rules_mono:
  "post_star_rules ts ts' \<Longrightarrow> ts \<subset> ts'"
proof(induction rule: post_star_rules.induct)
  case (add_trans_pop p \<gamma> p' q ts)
  then show ?case by auto
next
  case (add_trans_swap p \<gamma> p' \<gamma>' q ts)
  then show ?case by auto
next
  case (add_trans_push_1 p \<gamma> p' \<gamma>' \<gamma>'' q ts)
  then show ?case by auto
next
  case (add_trans_push_2 p \<gamma> p' \<gamma>' \<gamma>'' q ts)
  then show ?case by auto
qed

lemma pre_star_rule_card_Suc: "pre_star_rule ts ts' \<Longrightarrow> card ts' = Suc (card ts)"
  unfolding pre_star_rule.simps by auto

lemma post_star_rules_card_Suc: "post_star_rules ts ts' \<Longrightarrow> card ts' = Suc (card ts)"
proof(induction rule: post_star_rules.induct)
  case (add_trans_pop p \<gamma> p' q ts)
  then show ?case by auto
next
  case (add_trans_swap p \<gamma> p' \<gamma>' q ts)
  then show ?case by auto
next
  case (add_trans_push_1 p \<gamma> p' \<gamma>' \<gamma>'' q ts)
  then show ?case by auto
next
  case (add_trans_push_2 p \<gamma> p' \<gamma>' \<gamma>'' q ts)
  then show ?case by auto
qed

lemma no_infinite: 
  (* Maybe lazy lists are better? *)
  assumes "\<And>ts ts' :: ('c ::finite, 'l::finite) transition set. rule ts ts' \<Longrightarrow> card ts' = Suc (card ts)"
  assumes "\<forall>i :: nat. rule (tts i) (tts (Suc i))"
  shows "False"
proof -
  define f where "f i = card (tts i)" for i
  have f_Suc: "\<forall>i. f i < f (Suc i)"
    using assms f_def lessI by metis
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
  then have "\<exists>j. f j > card (UNIV :: ('c, 'l) transition set)"
    by auto
  then show False
    by (metis card_seteq f_def finite_UNIV le_eq_less_or_eq nat_neq_iff subset_UNIV)
qed

lemma saturation_termination:
  assumes "\<And>ts ts' :: ('c ::finite, 'l::finite) transition set. rule ts ts' \<Longrightarrow> card ts' = Suc (card ts)"
  shows "\<not>(\<exists>tts. (\<forall>i :: nat. rule (tts i) (tts (Suc i))))"
  using assms no_infinite by blast 

lemma pre_star_saturation_termination: 
  (* Maybe lazy lists are better? *)
  "\<not>(\<exists>tts. (\<forall>i :: nat. pre_star_rule (tts i) (tts (Suc i))))"
  using no_infinite pre_star_rule_card_Suc by blast 

lemma post_star_saturation_termination: 
  (* Maybe lazy lists are better? *)
  "\<not>(\<exists>tts. (\<forall>i :: nat. post_star_rules (tts i) (tts (Suc i))))"
  using no_infinite post_star_rules_card_Suc by blast

lemma saturation_exi: 
  assumes "\<And>ts ts' :: ('c ::finite, 'l::finite) transition set. rule ts ts' \<Longrightarrow> card ts' = Suc (card ts)"
  shows "\<exists>ts'. saturation rule ts ts'"
proof (rule ccontr) (* TODO: it would be nice to avoid ccontr *)
  assume a: "\<nexists>ts'. saturation rule ts ts'"
  define g where "g ts = (SOME ts'. rule ts ts')" for ts
  define tts where "tts i = (g ^^ i) ts" for i
  have "\<forall>i :: nat. rule\<^sup>*\<^sup>* ts (tts i) \<and> rule (tts i) (tts (Suc i))"
  proof 
    fix i
    show "rule\<^sup>*\<^sup>* ts (tts i) \<and> rule (tts i) (tts (Suc i))"
    proof (induction i)
      case 0
      have "rule ts (g ts)"
        by (metis g_def a rtranclp.rtrancl_refl saturation_def saturated_def someI)
      then show ?case
        using tts_def a saturation_def by auto 
    next
      case (Suc i)
      then have sat_Suc: "rule\<^sup>*\<^sup>* ts (tts (Suc i))"
        by fastforce
      then have "rule (g ((g ^^ i) ts)) (g (g ((g ^^ i) ts)))"
        by (metis Suc.IH tts_def g_def a r_into_rtranclp rtranclp_trans saturation_def saturated_def someI)
      then have "rule (tts (Suc i)) (tts (Suc (Suc i)))"
        unfolding tts_def by simp
      then show ?case
        using sat_Suc by auto
    qed
  qed
  then have "\<forall>i. rule (tts i) (tts (Suc i))"
    by auto
  then show False
    using no_infinite assms by auto
qed

lemma pre_star_saturation_exi: 
  shows "\<exists>ts'. saturation pre_star_rule ts ts'"
  using pre_star_rule_card_Suc saturation_exi by blast

lemma post_star_saturation_exi: 
  shows "\<exists>ts'. saturation post_star_rules ts ts'"
  using post_star_rules_card_Suc saturation_exi by blast

(*

TODO: Prove that saturations are unique?

*)

lemma pre_star_rule_incr: "pre_star_rule A B \<Longrightarrow> A \<subseteq> B"
proof(induction rule: pre_star_rule.inducts)
  case (add_trans p \<gamma> p' w q rel)
  then show ?case 
    by auto
qed

lemma post_star_rules_incr: "post_star_rules A B \<Longrightarrow> A \<subseteq> B"
proof(induction rule: post_star_rules.inducts)
  case (add_trans_pop p \<gamma> p' q ts)
  then show ?case
    by auto
next
  case (add_trans_swap p \<gamma> p' \<gamma>' q ts)
  then show ?case 
    by auto
next
  case (add_trans_push_1 p \<gamma> p' \<gamma>' \<gamma>'' q ts)
  then show ?case 
    by auto
next
  case (add_trans_push_2 p \<gamma> p' \<gamma>' \<gamma>'' q ts)
  then show ?case 
    by auto
qed

lemma saturation_rtranclp_pre_star_rule_incr: "pre_star_rule\<^sup>*\<^sup>* A B \<Longrightarrow> A \<subseteq> B"
proof (induction rule: rtranclp_induct)
  case base
  then show ?case by auto
next
  case (step y z)
  then show ?case
    using pre_star_rule_incr by auto
qed


lemma saturation_rtranclp_post_star_rule_incr: "post_star_rules\<^sup>*\<^sup>* A B \<Longrightarrow> A \<subseteq> B"
proof (induction rule: rtranclp_induct)
  case base
  then show ?case by auto
next
  case (step y z)
  then show ?case
    using post_star_rules_incr by auto
qed

lemma pre_star'_incr_transition_star:
  "pre_star_rule\<^sup>*\<^sup>* A A' \<Longrightarrow> LTS.transition_star A \<subseteq> LTS.transition_star A'"
  using mono_def LTS_transition_star_mono saturation_rtranclp_pre_star_rule_incr by metis

lemma post_star'_incr_transition_star:
  "post_star_rules\<^sup>*\<^sup>* A A' \<Longrightarrow> LTS.transition_star A \<subseteq> LTS.transition_star A'"
  using mono_def LTS_transition_star_mono saturation_rtranclp_post_star_rule_incr by metis

lemma post_star'_incr_transition_star_\<epsilon>:
  "post_star_rules\<^sup>*\<^sup>* A A' \<Longrightarrow> LTS_\<epsilon>.transition_star_\<epsilon> A \<subseteq> LTS_\<epsilon>.transition_star_\<epsilon> A'"
  using mono_def LTS_\<epsilon>_transition_star_\<epsilon>_mono saturation_rtranclp_post_star_rule_incr by metis

lemma pre_star_lim'_incr_transition_star:
  "saturation pre_star_rule A A' \<Longrightarrow> LTS.transition_star A \<subseteq> LTS.transition_star A'"
  by (simp add: pre_star'_incr_transition_star saturation_def)

lemma post_star_lim'_incr_transition_star:
  "saturation post_star_rules A A' \<Longrightarrow> LTS.transition_star A \<subseteq> LTS.transition_star A'"
  by (simp add: post_star'_incr_transition_star saturation_def)

lemma post_star_lim'_incr_transition_star_\<epsilon>:
  "saturation post_star_rules A A' \<Longrightarrow> LTS_\<epsilon>.transition_star_\<epsilon> A \<subseteq> LTS_\<epsilon>.transition_star_\<epsilon> A'"
  by (simp add: post_star'_incr_transition_star_\<epsilon> saturation_def)




(* Do I need to do these for \<epsilon> also? *)


subsection \<open>Pre* lemmas\<close>

lemma  lemma_3_1:
  assumes "p'w \<Rightarrow>\<^sup>* pv"
    and "pv \<in> language A"
    and "saturation pre_star_rule A A'"
  shows "accepts A' p'w"
  using assms
proof (induct rule: converse_rtranclp_induct)
  case base
  then have "\<exists>q \<in> F_locs. (Ctr_Loc (fst pv), snd pv, q) \<in> LTS.transition_star A'"
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
  then obtain q where q_p: "q \<in> F_locs \<and> (Ctr_Loc p'', u, q) \<in> LTS.transition_star A'"
    unfolding accepts_def using p''_def u_def by auto
  have "\<exists>\<gamma> w1 u1. w=\<gamma>#w1 \<and> u=op_labels u1@w1 \<and> (p', \<gamma>) \<hookrightarrow> (p'', u1)"
    using p''u_def p'w_def step.hyps(1) step_relp_def2 by auto
  then obtain \<gamma> w1 u1 where \<gamma>_w1_u1_p: "w=\<gamma>#w1 \<and> u=op_labels u1@w1 \<and> (p', \<gamma>) \<hookrightarrow> (p'', u1)"
    by blast

  have "\<exists>q1. (Ctr_Loc p'', op_labels u1, q1) \<in> LTS.transition_star A' \<and> (q1, w1, q) \<in> LTS.transition_star A'"
    using q_p \<gamma>_w1_u1_p LTS.transition_star_split by auto

  then obtain q1 where q1_p: "(Ctr_Loc p'', op_labels u1, q1) \<in> LTS.transition_star A' \<and> (q1, w1, q) \<in> LTS.transition_star A'"
    by auto

  then have in_A': "(Ctr_Loc p', \<gamma>, q1) \<in> A'"
    using \<gamma>_w1_u1_p 
    using add_trans[of p' \<gamma> p'' u1 q1 A'] 
    using step.prems(2)
    using saturated_def
    using saturation_def[of ]
    using step.prems
    by metis

  then have "(Ctr_Loc p', \<gamma>#w1, q) \<in> LTS.transition_star A'"
    using in_A' transition_star_step q1_p
    by (meson LTS.transition_star.transition_star_step)
  then have t_in_A': "(Ctr_Loc p', w, q) \<in> LTS.transition_star A'"
    using \<gamma>_w1_u1_p by blast

  from q_p t_in_A' have "q \<in> F_locs \<and> (Ctr_Loc p', w, q) \<in> LTS.transition_star A'"
    using p'_def w_def by auto
  then show ?case
    unfolding accepts_def p'w_def using q_p by auto 
qed

lemma lemma_3_2_base: 
  "(Ctr_Loc p, w, q) \<in> LTS.transition_star rel \<Longrightarrow> \<exists>p' w'. (p, w) \<Rightarrow>\<^sup>* (p', w') \<and> (Ctr_Loc p', w',  q) \<in> LTS.transition_star rel"
  by auto

lemma pre_star_rule_mono': "t \<in> LTS.transition_star rel \<Longrightarrow> pre_star_rule rel rel' \<Longrightarrow> t \<in> LTS.transition_star (rel')"
  using pre_star'_incr_transition_star by blast



lemma lemma_3_2_b_aux':
  (* Lemma from discussion with Morten 2 *)
  assumes "(p, w, ss, q) \<in> LTS.transition_star_states A"
  assumes "\<nexists>q \<gamma> q'. (q, \<gamma>, Ctr_Loc q') \<in> A"
  assumes "q \<in> P_locs"
  shows "w = [] \<and> p = q \<and> ss=[p]"
  using assms 
proof(induction rule: LTS.transition_star_states.induct[OF assms(1)])
  case (1 p)
  then show ?case by auto
next
  case (2 p \<gamma> q' w ss q)
  then show ?case
    by (metis P_locs_def is_Ctr_Loc_def mem_Collect_eq)
qed

lemma lemma_3_2_b_aux:
  (* Lemma from discussion with Morten 2 *)
  fixes A :: "(('ctr_loc, 'state, 'label) state, 'label) transition set"
  assumes "(p, w, ss, Ctr_Loc q) \<in> LTS.transition_star_states A"
  assumes "\<nexists>q \<gamma> q'. (q, \<gamma>, Ctr_Loc q') \<in> A"
  shows "w = [] \<and> p = Ctr_Loc q \<and> ss=[p]"
proof -
  have "Ctr_Loc q \<in> P_locs"
    unfolding P_locs_def by auto
  moreover
  have "\<nexists>q \<gamma> q'. (q, \<gamma>, q') \<in> A \<and> q' \<in> P_locs"
    using assms(2) unfolding P_locs_def by (metis is_Ctr_Loc_def mem_Collect_eq) 
  ultimately 
  show ?thesis
    using lemma_3_2_b_aux' assms(1) assms(2) by blast
qed


lemma lemma_3_2_b':
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

lemma lemma_3_2_b:
  (* The natural langauge formulation of this in the thesis is quite strange. *)
  fixes A :: "(('ctr_loc, 'state, 'label) state, 'label) transition set"
  assumes "(p, w, Ctr_Loc q) \<in> LTS.transition_star A"
  assumes "\<nexists>q \<gamma> q'. (q, \<gamma>, Ctr_Loc q') \<in> A"
  shows "w = [] \<and> p = Ctr_Loc q"
proof -
  have "Ctr_Loc q \<in> P_locs"
    unfolding P_locs_def by auto
  moreover
  have "\<nexists>q \<gamma> q'. (q, \<gamma>, q') \<in> A \<and> q' \<in> P_locs"
    using assms(2) unfolding P_locs_def by (metis is_Ctr_Loc_def mem_Collect_eq) 
  ultimately 
  show ?thesis
    using lemma_3_2_b' assms(1) by blast
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
    by (metis (no_types, lifting) PDS.step_relp_def2 append.assoc append_Cons rtranclp.simps step_3)
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
  assumes "\<nexists>q \<gamma> q'. (q, \<gamma>, Ctr_Loc q') \<in> A"
  assumes "pre_star_rule\<^sup>*\<^sup>* A A'"
  assumes "(Ctr_Loc p, w, ss, q) \<in> LTS.transition_star_states A'"
  shows "\<exists>p' w' ss'. (Ctr_Loc p', w', ss', q) \<in> LTS.transition_star_states A \<and> (p, w) \<Rightarrow>\<^sup>* (p', w')"
  using assms(2) assms(1,3) 
proof (induction arbitrary: p q w ss rule: rtranclp_induct)
  case base
  then show ?case
    by auto
next
  case (step Aiminus1 Ai)

  from step(2) obtain p1 \<gamma> p2 w2 q' where p1_\<gamma>_p2_w2_q'_p:
    "Ai = Aiminus1 \<union> {(Ctr_Loc p1, \<gamma>, q')}" 
    "(p1, \<gamma>) \<hookrightarrow> (p2, w2)"
    "(Ctr_Loc p2, op_labels w2, q') \<in> LTS.transition_star Aiminus1"
    "(Ctr_Loc p1, \<gamma>, q') \<notin> Aiminus1"
    by (meson pre_star_rule.cases)

  have "Ctr_Loc p1 \<in> P_locs"
    unfolding P_locs_def by auto

  note ss_p = step(5)

  define t :: "(('ctr_loc, 'state, 'label) state, 'label) transition"
    where "t = (Ctr_Loc p1, \<gamma>, q')"
  define j where "j = count (transitions_of' (Ctr_Loc p, w, ss, q)) t"

  from j_def ss_p show ?case
  proof (induction j arbitrary: p q w ss)
    case 0
    have "(Ctr_Loc p, w, ss, q) \<in> LTS.transition_star_states Aiminus1"
      using lemma_3_2_a'_Aux_3
        p1_\<gamma>_p2_w2_q'_p(1) t_def 0 by fastforce
    then show ?case
      using step.IH step.prems(1) by metis
  next
    case (Suc j')
    have "\<exists>u v u_ss v_ss. ss = u_ss@v_ss \<and> w = u@[\<gamma>]@v \<and> (Ctr_Loc p,u,u_ss, Ctr_Loc p1) \<in> LTS.transition_star_states Aiminus1 \<and> (Ctr_Loc p1,[\<gamma>],q') \<in> LTS.transition_star Ai \<and> (q',v,v_ss,q) \<in> LTS.transition_star_states Ai"
      apply (rule split_at_first_t[of "Ctr_Loc p" w ss q Ai j' "Ctr_Loc p1" \<gamma> q' Aiminus1])
      using Suc(2,3) t_def  p1_\<gamma>_p2_w2_q'_p(1,4) t_def by auto
    then obtain u v u_ss v_ss where u_v_u_ss_v_ss_p:
      "ss = u_ss@v_ss \<and> w = u@[\<gamma>]@v" 
      "(Ctr_Loc p,u,u_ss, Ctr_Loc p1) \<in> LTS.transition_star_states Aiminus1" 
      "(Ctr_Loc p1,[\<gamma>],q') \<in> LTS.transition_star Ai" 
      "(q',v,v_ss,q) \<in> LTS.transition_star_states Ai"
      by blast
    have II: "Ctr_Loc p1 \<in> P_locs"
      unfolding P_locs_def by auto
    have "\<exists>p'' w'' ss''. (Ctr_Loc p'', w'', ss'', Ctr_Loc p1) \<in> LTS.transition_star_states A \<and> (p, u) \<Rightarrow>\<^sup>* (p'', w'')"
      using Suc(1)[of p u _ "Ctr_Loc p1"]
      using \<open>(Ctr_Loc p, u, u_ss, Ctr_Loc p1) \<in> LTS.transition_star_states Aiminus1\<close> step.IH step.prems(1) by blast 
    then obtain p'' w'' ss'' where "(Ctr_Loc p'', w'', ss'', Ctr_Loc p1) \<in> LTS.transition_star_states A" "(p, u) \<Rightarrow>\<^sup>* (p'', w'')"
      by blast
    from this this(1) II have VIII: "(p, u) \<Rightarrow>\<^sup>* (p1, [])"
      using step.prems(1) lemma_3_2_b_aux' by blast 

    note IX = p1_\<gamma>_p2_w2_q'_p(2)
    note III = p1_\<gamma>_p2_w2_q'_p(3)
    from III have III_2: "\<exists>w2_ss. (Ctr_Loc p2, op_labels w2, w2_ss, q') \<in> LTS.transition_star_states Aiminus1"
      using LTS.transition_star_transition_star_states[of "Ctr_Loc p2" "op_labels w2" q' Aiminus1] by auto
    then obtain w2_ss where III_2: "(Ctr_Loc p2, op_labels w2, w2_ss, q') \<in> LTS.transition_star_states Aiminus1"
      by blast

    from III have V: "(Ctr_Loc p2, op_labels w2, w2_ss, q') \<in> LTS.transition_star_states Aiminus1" "(q', v, v_ss, q) \<in> LTS.transition_star_states Ai"
      using III_2 \<open>(q', v, v_ss, q) \<in> LTS.transition_star_states Ai\<close> by auto

    define w2v where "w2v = op_labels w2 @ v"
    define w2v_ss where "w2v_ss = w2_ss @ tl v_ss"

    from V(1) have "(Ctr_Loc p2, op_labels w2, w2_ss, q') \<in> LTS.transition_star_states Ai"
      using transition_star_states_mono p1_\<gamma>_p2_w2_q'_p(1) using Un_iff subsetI by (metis (no_types, hide_lams))
    then have V_merged: "(Ctr_Loc p2, w2v, w2v_ss, q) \<in> LTS.transition_star_states Ai"
      using V(2) unfolding w2v_def w2v_ss_def by (meson LTS.transition_star_states_append)

    have j'_count: "j' = count (transitions_of' (Ctr_Loc p2, w2v, w2v_ss, q)) t"
    proof -
      have "Suc j' = count (transitions_of' (Ctr_Loc p, u, u_ss, Ctr_Loc p1)) t + 1 + count (transitions_of' (q', v, v_ss, q)) t"
        using u_v_u_ss_v_ss_p(2) u_v_u_ss_v_ss_p(4)
        using count_combine_transition_star_states Suc(2) u_v_u_ss_v_ss_p(1) t_def by force
      then have "j' = count (transitions_of' (Ctr_Loc p, u, u_ss, Ctr_Loc p1)) t + count (transitions_of' (q', v, v_ss, q)) t"
        by auto
      then have "j' = 0 + count (transitions_of' (q', v, v_ss, q)) t"
        using avoid_count_zero
        by (metis p1_\<gamma>_p2_w2_q'_p(4) t_def u_v_u_ss_v_ss_p(2))
      then have xx: "j' = count (transitions_of' (Ctr_Loc p2, op_labels w2, w2_ss, q')) t  + count (transitions_of' (q', v, v_ss, q)) t"
        using V avoid_count_zero p1_\<gamma>_p2_w2_q'_p(4) t_def by fastforce 
      then show "j' = count (transitions_of' (Ctr_Loc p2, w2v, w2v_ss, q)) t"
      proof -
        have l_w2_ss: "length w2_ss = Suc (length (op_labels w2))" 
          by (meson III_2 LTS.transition_star_states_length)
        have v_ss_non_empty: "v_ss \<noteq> []"
          using LTS.transition_star_states.cases V(2) by force
        have last_hd: "last w2_ss = hd v_ss"
          by (metis III_2 LTS.transition_star_states_last V(2) LTS.transition_star_states_hd)
        have "count (transitions_of' ((Ctr_Loc p2, op_labels w2, w2_ss, q') @@\<acute> (q', v, v_ss, q))) (Ctr_Loc p1, \<gamma>, q')
          = count (transitions_of' (Ctr_Loc p2, w2v, w2v_ss, q)) (Ctr_Loc p1, \<gamma>, q')"
          by (simp add: w2v_def w2v_ss_def)
        then have "count (transitions_of' (Ctr_Loc p2, w2v, w2v_ss, q))  (Ctr_Loc p1, \<gamma>, q') = count (transitions_of' (Ctr_Loc p2, op_labels w2, w2_ss, q')) (Ctr_Loc p1, \<gamma>, q') + count (transitions_of' (q', v, v_ss, q)) (Ctr_Loc p1, \<gamma>, q')"
          using count_append_transition_star_states[of w2_ss "op_labels w2" v_ss "Ctr_Loc p2" q' q' v q "Ctr_Loc p1" \<gamma> q']
          by (simp add: l_w2_ss v_ss_non_empty last_hd) 
        then have "count (transitions_of' (Ctr_Loc p2, w2v, w2v_ss, q)) t = count (transitions_of' (Ctr_Loc p2, op_labels w2, w2_ss, q')) t + count (transitions_of' (q', v, v_ss, q)) t"
          using t_def by auto
        then show ?thesis
          using xx by auto
      qed
    qed

    have "\<exists>p' w' ss'. (Ctr_Loc p', w', ss', q) \<in> LTS.transition_star_states A \<and> (p2, w2v) \<Rightarrow>\<^sup>* (p', w')"
      using Suc(1) using j'_count V_merged by auto
    then obtain p' w' ss' where p'_w'_ss'_p: "(Ctr_Loc p', w', ss', q) \<in> LTS.transition_star_states A" "(p2, w2v) \<Rightarrow>\<^sup>* (p', w')"
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

    then have "(Ctr_Loc p', w', ss', q) \<in> LTS.transition_star_states A \<and> (p, w) \<Rightarrow>\<^sup>* (p', w')"
      using p'_w'_ss'_p(1) by auto
    then show ?case
      by metis
  qed
qed 

lemma lemma_3_2_a'':
  assumes "\<nexists>q \<gamma> q'. (q, \<gamma>, Ctr_Loc q') \<in> A"
  assumes "pre_star_rule\<^sup>*\<^sup>* A A'"
  assumes "(Ctr_Loc p, w, q) \<in> LTS.transition_star A'"
  shows "\<exists>p' w' ss'. (Ctr_Loc p', w', q) \<in> LTS.transition_star A \<and> (p, w) \<Rightarrow>\<^sup>* (p', w')"
  using lemma_3_2_a' assms
  by (meson LTS.transition_star_states_transition_star LTS.transition_star_transition_star_states)

lemma lemma_3_2_a:
  assumes "\<nexists>q \<gamma> q'. (q, \<gamma>, Ctr_Loc q') \<in> A"
  assumes "saturation pre_star_rule A A'"
  assumes "(Ctr_Loc p, w, q) \<in> LTS.transition_star A'"
  shows "\<exists>p' w'. (Ctr_Loc p', w', q) \<in> LTS.transition_star A \<and> (p, w) \<Rightarrow>\<^sup>* (p', w')"
  using assms lemma_3_2_a'' saturation_def by metis 

lemmas lemma_3_2 = lemma_3_2_a lemma_3_2_b

theorem theorem_3_2:
  assumes "\<nexists>q \<gamma> q'. (q, \<gamma>, Ctr_Loc q') \<in> A"
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
  then have "\<exists>q \<in> F_locs. (Ctr_Loc p, w, q) \<in> LTS.transition_star A'"
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
  then have "\<exists>q \<in> F_locs. (Ctr_Loc p, w, q) \<in> LTS.transition_star A'"
    unfolding accepts_def by auto
  then obtain q where q_p: "q \<in> F_locs" "(Ctr_Loc p, w, q) \<in> LTS.transition_star A'"
    by auto
  then have "\<exists>p' w'. (p,w) \<Rightarrow>\<^sup>* (p',w') \<and> (Ctr_Loc p', w', q) \<in> LTS.transition_star A"
    using lemma_3_2_a assms(1) assms(2) by metis
  then obtain p' w' where p'_w'_p: "(p,w) \<Rightarrow>\<^sup>* (p',w')" "(Ctr_Loc p', w', q) \<in> LTS.transition_star A"
    by auto
  then have "(p', w') \<in> language A"
    unfolding language_def unfolding accepts_def using q_p(1) by auto
  then have "(p,w) \<in> pre_star (language A)"
    unfolding pre_star_def using p'_w'_p(1) by auto
  then show "c \<in> pre_star (language A)"
    unfolding p_def w_def by auto
qed


subsection \<open>Post* lemmas\<close>

lemma lemma_3_3':
  assumes "pv \<Rightarrow>\<^sup>* p'w"
    and "(fst pv, snd pv) \<in> language_\<epsilon> A"
    and "saturation post_star_rules A A'"
  shows "accepts_\<epsilon> A' (fst p'w, snd p'w)"
  using assms
proof (induct arbitrary: pv rule: rtranclp_induct)
  case base
  show ?case
    unfolding accepts_\<epsilon>_def
    by (smt (verit, del_insts) Collect_case_prodD accepts_\<epsilon>_def assms(2) assms(3) language_\<epsilon>_def post_star_lim'_incr_transition_star_\<epsilon> prod.case_eq_if subsetD) 
next
  case (step p''u p'w)
  define p' where "p' = fst p'w"
  define w  where "w = snd p'w"
  define p'' where "p'' = fst p''u"
  define u  where "u = snd p''u"
  have p'w_def: "p'w = (p', w)"
    using p'_def w_def by auto
  have p''u_def: "p''u = (p'', u)"
    using p''_def u_def by auto

  then have "accepts_\<epsilon> A' (p'', u)"
    using assms(2) p''_def step.hyps(3) step.prems(2) u_def by metis
  then obtain q where q_p: "q \<in> F_locs \<and> (Ctr_Loc p'', u, q) \<in> LTS_\<epsilon>.transition_star_\<epsilon> A'"
    by (smt (verit, ccfv_threshold) accepts_\<epsilon>_def case_prod_conv)
  then obtain u_\<epsilon> where II: "q \<in> F_locs" "LTS_\<epsilon>.\<epsilon>_exp u_\<epsilon> u" "(Ctr_Loc p'', u_\<epsilon>, q) \<in> LTS.transition_star A'"
    using LTS_\<epsilon>.epsilon_lemma3[of "Ctr_Loc p''" u q A'] by auto
  have "\<exists>\<gamma> u1 w1. u=\<gamma>#u1 \<and> w=op_labels w1@u1 \<and> (p'', \<gamma>) \<hookrightarrow> (p', w1)"
    using p''u_def p'w_def step.hyps(2) step_relp_def2 by auto
  then obtain \<gamma> u1 w1 where III: "u=\<gamma>#u1" " w=op_labels w1@u1" "(p'', \<gamma>) \<hookrightarrow> (p', w1)"
    by blast

  have p'_P_locs: "Ctr_Loc p' \<in> P_locs"
    unfolding P_locs_def by auto
  have p''_P_locs: "Ctr_Loc p'' \<in> P_locs"
    unfolding P_locs_def by auto

  have "\<exists>\<gamma>_\<epsilon> u1_\<epsilon>. LTS_\<epsilon>.\<epsilon>_exp \<gamma>_\<epsilon> [\<gamma>] \<and> LTS_\<epsilon>.\<epsilon>_exp u1_\<epsilon> u1 \<and> (Ctr_Loc p'', \<gamma>_\<epsilon>@u1_\<epsilon>, q) \<in> LTS.transition_star A'"
  proof -
    have "\<exists>\<gamma>_\<epsilon> u1_\<epsilon>. LTS_\<epsilon>.\<epsilon>_exp \<gamma>_\<epsilon> [\<gamma>] \<and> LTS_\<epsilon>.\<epsilon>_exp u1_\<epsilon> u1 \<and> u_\<epsilon> = \<gamma>_\<epsilon> @ u1_\<epsilon>" 
      using LTS_\<epsilon>.\<epsilon>_exp_split'[of u_\<epsilon> \<gamma> u1] II(2) III(1) by auto
    then obtain \<gamma>_\<epsilon> u1_\<epsilon> where "LTS_\<epsilon>.\<epsilon>_exp \<gamma>_\<epsilon> [\<gamma>] \<and> LTS_\<epsilon>.\<epsilon>_exp u1_\<epsilon> u1 \<and> u_\<epsilon> = \<gamma>_\<epsilon> @ u1_\<epsilon>" 
      by auto
    then have "(Ctr_Loc p'', \<gamma>_\<epsilon>@u1_\<epsilon> , q) \<in> LTS.transition_star A'"
      using II(3) by auto
    then show ?thesis
      using \<open>LTS_\<epsilon>.\<epsilon>_exp \<gamma>_\<epsilon> [\<gamma>] \<and> LTS_\<epsilon>.\<epsilon>_exp u1_\<epsilon> u1 \<and> u_\<epsilon> = \<gamma>_\<epsilon> @ u1_\<epsilon>\<close> by blast
  qed
  then obtain \<gamma>_\<epsilon> u1_\<epsilon> where iii: "LTS_\<epsilon>.\<epsilon>_exp \<gamma>_\<epsilon> [\<gamma>]" and iv: "LTS_\<epsilon>.\<epsilon>_exp u1_\<epsilon> u1" "(Ctr_Loc p'', \<gamma>_\<epsilon>@u1_\<epsilon>, q) \<in> LTS.transition_star A'"
    by blast
  then have VI: "\<exists>q1. (Ctr_Loc p'', \<gamma>_\<epsilon>, q1) \<in> LTS.transition_star A' \<and> (q1, u1_\<epsilon>, q) \<in> LTS.transition_star A'"
    by (simp add: LTS.transition_star_split)
  then obtain q1 where VI: "(Ctr_Loc p'', \<gamma>_\<epsilon>, q1) \<in> LTS.transition_star A'" "(q1, u1_\<epsilon>, q) \<in> LTS.transition_star A'"
    by blast

  then have VI_2: "(Ctr_Loc p'', [\<gamma>], q1) \<in> LTS_\<epsilon>.transition_star_\<epsilon> A'" "(q1, u1, q) \<in> LTS_\<epsilon>.transition_star_\<epsilon> A'"
     apply (meson LTS_\<epsilon>.epsilon_lemma3 iii)
    apply (meson LTS_\<epsilon>.epsilon_lemma3 VI(2) iv(1))
    done

  show ?case
  proof (cases w1)
    case pop
    then have r: "(p'', \<gamma>) \<hookrightarrow> (p', pop)"
      using III(3) by blast
    then have "(Ctr_Loc p', \<epsilon>, q1) \<in> A'"
      using VI_2(1) add_trans_pop assms saturated_def saturation_def p'_P_locs by metis
    then have "(Ctr_Loc p', w, q) \<in> LTS_\<epsilon>.transition_star_\<epsilon> A'"
      using III(2)  VI_2(2) pop LTS_\<epsilon>.transition_star_\<epsilon>.transition_star_\<epsilon>_step_\<epsilon> by fastforce
    then have "accepts_\<epsilon> A' (p', w)"
      unfolding accepts_\<epsilon>_def
      using II(1) by blast
    then show ?thesis
      using p'_def w_def by force
  next
    case (swap \<gamma>')
    then have r: "(p'', \<gamma>) \<hookrightarrow> (p', swap \<gamma>')"
      using III(3) by blast
    then have "(Ctr_Loc p', Some \<gamma>', q1) \<in> A'"
      by (metis VI_2(1) add_trans_swap assms(3) saturated_def saturation_def)
    have "(Ctr_Loc p', w, q) \<in> LTS_\<epsilon>.transition_star_\<epsilon> A'"
      using III(2) LTS_\<epsilon>.transition_star_\<epsilon>.transition_star_\<epsilon>_step_\<gamma> VI_2(2) append_Cons append_self_conv2 op_labels.simps(3) swap
      using \<open>(Ctr_Loc p', Some \<gamma>', q1) \<in> A'\<close> by fastforce
    then have "accepts_\<epsilon> A' (p', w)"
      unfolding accepts_\<epsilon>_def
      using II(1) by blast
    then show ?thesis
      using p'_def w_def by force
  next
    case (push \<gamma>' \<gamma>'')
    then have r: "(p'', \<gamma>) \<hookrightarrow> (p', push \<gamma>' \<gamma>'')"
      using III(3) by blast
    from this VI_2 iii post_star_rules.intros(3)[OF this, of q1 A', OF VI_2(1)] have "(Ctr_Loc p', Some \<gamma>', Ctr_Loc_Ext p' \<gamma>') \<in> A'"
      using assms(3) by (meson saturated_def saturation_def) 
    from this r VI_2 iii post_star_rules.intros(4)[OF r, of q1 A', OF VI_2(1)] have "(Ctr_Loc_Ext p' \<gamma>', Some \<gamma>'', q1) \<in> A'"
      using assms(3) using saturated_def saturation_def
      by metis
    have "(Ctr_Loc p', [\<gamma>'], Ctr_Loc_Ext p' \<gamma>') \<in> LTS_\<epsilon>.transition_star_\<epsilon> A' \<and> (Ctr_Loc_Ext p' \<gamma>', [\<gamma>''], q1) \<in> LTS_\<epsilon>.transition_star_\<epsilon> A' \<and> (q1, u1, q) \<in> LTS_\<epsilon>.transition_star_\<epsilon> A'"
      by (metis LTS_\<epsilon>.transition_star_\<epsilon>.simps VI_2(2) \<open>(Ctr_Loc p', Some \<gamma>', Ctr_Loc_Ext p' \<gamma>') \<in> A'\<close> \<open>(Ctr_Loc_Ext p' \<gamma>', Some \<gamma>'', q1) \<in> A'\<close>)
    have "(Ctr_Loc p', w, q) \<in> LTS_\<epsilon>.transition_star_\<epsilon> A'"
      by (smt (z3) III(2) LTS_\<epsilon>.transition_star_\<epsilon>.transition_star_\<epsilon>_step_\<gamma> VI_2(2) \<open>(Ctr_Loc p', Some \<gamma>', Ctr_Loc_Ext p' \<gamma>') \<in> A'\<close> \<open>(Ctr_Loc_Ext p' \<gamma>', Some \<gamma>'', q1) \<in> A'\<close> append_Cons append_self_conv2 op_labels.simps(3) push)
    then have "accepts_\<epsilon> A' (p', w)"
      unfolding accepts_\<epsilon>_def
      using II(1) by blast
    then show ?thesis
      using p'_def w_def by force

  qed
qed

lemma lemma_3_3:
  assumes "(p,v) \<Rightarrow>\<^sup>* (p',w)"
    and "(p, v) \<in> language_\<epsilon> A"
    and "saturation post_star_rules A A'"
  shows "accepts_\<epsilon> A' (p', w)"
  using assms lemma_3_3' by force

thm lemma_3_2_a'
term LTS_\<epsilon>.remove_\<epsilon>

lemma aux'''': (* Can this be phrased better? *)
  assumes "(p, w, ss, q) \<in> LTS.transition_star_states Ai"
  assumes "t = hd (transition_list' (p, w, ss, q))"
  assumes "transition_list' (p, w, ss, q) \<noteq> []"
  assumes "t = (p1, \<gamma>, q1)"
  shows "p = p1"
  using assms proof (induction rule: LTS.transition_star_states.inducts[OF assms(1)])
  case (1 p)
  then show ?case
    by auto 
next
  case (2 p \<gamma> q' w ss q)
  then show ?case
    by (metis LTS.transition_star_states.simps Pair_inject list.sel(1) transition_list'.simps transition_list.simps(1))
qed

lemma transition_list_Cons':
  assumes "length ss = Suc (length w)"
  assumes "hd (transition_list (ss, w)) = (p, \<gamma>, q)"
  assumes "transition_list (ss, w) \<noteq> []"
  shows "\<exists>w' ss'. w = \<gamma> # w' \<and> ss = p # q # ss'"
  using assms
  apply (cases ss; cases w)
  subgoal
    apply auto
    done
  subgoal
    apply auto
    done
  subgoal
    apply auto
    done
  subgoal for aa lista aaa listaa
    apply (cases lista; cases listaa)
    subgoal
      apply auto
      done
    subgoal
      apply auto
      done
    subgoal for ab listb
      apply auto
      done
    subgoal for ab listb aab listab
      apply auto
      done
    done
  done

lemma transition_list_Cons:
  assumes "(p, w, ss, q) \<in> LTS.transition_star_states Ai"
  assumes "hd (transition_list (ss, w)) = (p, \<gamma>, q1)"
  assumes "transition_list (ss, w) \<noteq> []"
  shows "\<exists>w' ss'. w = \<gamma> # w' \<and> ss = p # q1 # ss'"
  using assms transition_list_Cons' by (metis LTS.transition_star_states_length) 

lemma xxxxxxxxxx:
  assumes "(ss, w) \<in> LTS.path_with_word A"
  assumes "\<nexists>q \<gamma> q'. (q, \<gamma>, Ctr_Loc q') \<in> A"
  assumes "t = (Ctr_Loc p1, \<gamma>, q1)"
  shows "count (transitions_of (ss, w)) t = 0 \<or> ((hd (transition_list (ss, w)) = t \<and> count (transitions_of (ss, w)) t = 1))"
  using assms
proof (induction rule: LTS.path_with_word.induct[OF assms(1)])
  case (1 s)
  then show ?case
    by simp
next
  case (2 s' ss w s l)
  then have "count (transitions_of (s' # ss, w)) t = 0 \<or>
    (hd (transition_list (s' # ss, w)) = t \<and> count (transitions_of (s' # ss, w)) t = 1)"
    by auto
  then show ?case
  proof
    assume a: "count (transitions_of (s' # ss, w)) t = 0"
    show ?case
    proof (cases "s = Ctr_Loc p1 \<and> l = \<gamma> \<and> q1 = s'")
      case True
      then have "hd (transition_list (s # s' # ss, l # w)) = t \<and> count (transitions_of (s # s' # ss, l # w)) t = 1"
        using 2 a by simp
      then show ?thesis
        by auto
    next
      case False
      then have "count (transitions_of (s # s' # ss, l # w)) t = 0"
        using 2 a by auto
      then show ?thesis
        by auto
    qed
  next 
    assume "hd (transition_list (s' # ss, w)) = t \<and> count (transitions_of (s' # ss, w)) t = 1"
    then have False
      using 2
      by (smt (z3) LTS.path_with_word.simps Pair_inject list.sel(1) transition_list.simps(1) transitions_of.simps(2) zero_multiset.rep_eq zero_neq_one)
    then show ?case
      by auto
  qed
qed

lemma xxxxxxxxxxxxxxx:
  assumes "(ss, w) \<in> LTS.path_with_word A"
  assumes "\<nexists>q \<gamma> q'. (q, \<gamma>, Ctr_Loc q') \<in> A"
  assumes "count (transitions_of (ss, w)) t > 0"
  assumes "t = (Ctr_Loc p1, \<gamma>, q1)"
  shows "hd (transition_list (ss, w)) = t \<and> count (transitions_of (ss, w)) t = 1"
  using xxxxxxxxxx assms by (metis not_gr_zero)

lemma help''''':
  assumes "hd (transition_list (ss, w)) = t"
  assumes "transition_list (ss, w) \<noteq> []"
  assumes "t = (p1, \<gamma>, q1)"
  shows  "([p1, q1], [\<gamma>]) @\<acute> (tl ss, tl w) = (ss, w)"
  using assms apply simp
  apply (cases ss; cases w)
     apply auto
  subgoal
    apply (metis hd_Cons_tl transition_list.simps(2) transition_list.simps(4))
    done
  subgoal
    apply (metis (no_types, hide_lams) hd_Cons_tl list.sel(1) prod.inject transition_list.simps(1) transition_list.simps(2))
    done
  subgoal
    apply (metis (no_types, lifting) Pair_inject list.collapse list.sel(1) transition_list.simps(1) transition_list.simps(2))
    done
  subgoal
    apply (metis (no_types, lifting) Pair_inject list.collapse list.sel(1) transition_list.simps(1) transition_list.simps(2))
    done
  done

find_theorems pre_star_rule P_locs

lemma agagagagagaga:
  assumes "(p, w, qq) \<in> LTS.transition_star Aiminus1"
  assumes "w \<noteq> []"
  assumes "\<nexists>q \<gamma> q'. (q, \<gamma>, Ctr_Loc q') \<in> Aiminus1"
  shows "qq \<notin> P_locs"
  using assms
proof (induction rule: LTS.transition_star.induct[OF assms(1)])
  case (1 p)
  then show ?case
    by blast
next
  case (2 p \<gamma> q' w q)
  then show ?case
    by (metis LTS.transition_star_empty P_locs_def is_Ctr_Loc_def mem_Collect_eq)
qed


lemma agagagagagaga'''':
  assumes "(p, [\<gamma>], qq) \<in> LTS_\<epsilon>.transition_star_\<epsilon> Aiminus1"
  assumes "(p', \<epsilon>, qq) \<notin> Aiminus1"
  assumes "\<nexists>q \<gamma> q'. (q, \<gamma>, Ctr_Loc q') \<in> Aiminus1"
  shows "qq \<notin> P_locs"
proof -
  have "\<exists>w. LTS_\<epsilon>.\<epsilon>_exp w [\<gamma>] \<and> (p, w, qq) \<in> LTS.transition_star Aiminus1 \<and> w \<noteq> []"
    by (metis (no_types, hide_lams) LTS_\<epsilon>.\<epsilon>_exp_def LTS_\<epsilon>.\<epsilon>_exp_split' LTS_\<epsilon>.epsilon_lemma3 append_Cons append_Nil assms(1) list.distinct(1) list.exhaust)
  then obtain w where "LTS_\<epsilon>.\<epsilon>_exp w [\<gamma>] \<and> (p, w, qq) \<in> LTS.transition_star Aiminus1 \<and> w \<noteq> []"
    by blast
  then show ?thesis
    using agagagagagaga[of p w qq Aiminus1] assms(3) by auto
qed

lemma agagagagagaga''''''''':
  assumes "post_star_rules\<^sup>*\<^sup>* A Ai"
  assumes "\<nexists>q \<gamma> q'. (q, \<gamma>, Ctr_Loc q') \<in> A"
  shows "\<nexists>q \<gamma> q'. (q, \<gamma>, Ctr_Loc q') \<in> Ai"
using assms 
proof (induction rule: rtranclp_induct)
  case base
  then show ?case by auto
next
  case (step Aiminus1 Ai)
  then have ind: "\<nexists>q \<gamma> q'. (q, \<gamma>, Ctr_Loc q') \<in> Aiminus1"
    by auto
  from step(2) show ?case
  proof (cases rule: post_star_rules.cases)
    case (add_trans_pop p \<gamma> p' q)
    have "q \<notin> P_locs"
      using add_trans_pop ind agagagagagaga'''' by blast 
    then have "\<nexists>qq. q = Ctr_Loc qq"
      by (simp add: P_locs_def is_Ctr_Loc_def)
    then show ?thesis
      using ind local.add_trans_pop(1) by auto
  next
    case (add_trans_swap p \<gamma> p' \<gamma>' q)
    have "q \<notin> P_locs"
      using add_trans_swap ind agagagagagaga'''' by (metis P_locs_def is_Ctr_Loc_def mem_Collect_eq)
    then have "\<nexists>qq. q = Ctr_Loc qq"
      by (simp add: P_locs_def is_Ctr_Loc_def)
    then show ?thesis
      using ind local.add_trans_swap(1) by auto
  next
    case (add_trans_push_1 p \<gamma> p' \<gamma>' \<gamma>'' q)
    have "q \<notin> P_locs"
      using add_trans_push_1 ind agagagagagaga''''  by (metis P_locs_def is_Ctr_Loc_def mem_Collect_eq)
    then have "\<nexists>qq. q = Ctr_Loc qq"
      by (simp add: P_locs_def is_Ctr_Loc_def)
    then show ?thesis
      using ind local.add_trans_push_1(1) by auto
  next
    case (add_trans_push_2 p \<gamma> p' \<gamma>' \<gamma>'' q)
    have "q \<notin> P_locs"
      using add_trans_push_2 ind agagagagagaga''''  by (metis P_locs_def is_Ctr_Loc_def mem_Collect_eq)
    then have "\<nexists>qq. q = Ctr_Loc qq"
      by (simp add: P_locs_def is_Ctr_Loc_def)
    then show ?thesis
      using ind local.add_trans_push_2(1) by auto
  qed
qed

lemma lemma_3_4'_Aux_Aux:
  assumes "(p''', w, q) \<in> LTS_\<epsilon>.transition_star_\<epsilon> Aiminus1"
  assumes "p''' \<noteq> q"
  assumes "\<nexists>p \<gamma>. (p, \<gamma>, q') \<in> Aiminus1"
  shows "q' \<noteq> q"
  using assms 
proof (induction rule: LTS_\<epsilon>.transition_star_\<epsilon>.induct[OF assms(1)])
  case (1 p)
  then show ?case
    by blast 
next
  case (2 p \<gamma> q' w q)
  then show ?case
    by blast 
next
  case (3 p q' w q)
  then show ?case
    by blast
qed


lemma lemma_3_4'_Aux:
  assumes "post_star_rules\<^sup>*\<^sup>* A A'"
  assumes "\<forall>a b c. (a, b, c) \<in> A \<longrightarrow> a \<notin> New_Aut_states \<and> c \<notin> New_Aut_states"
  assumes "(Ctr_Loc p', Some \<gamma>', Ctr_Loc_Ext p' \<gamma>') \<notin> A'"
  shows "\<nexists>p \<gamma>. (p, \<gamma>, Ctr_Loc_Ext p' \<gamma>') \<in> A'"
  using assms 
proof (induction rule: rtranclp_induct)
  case base
  then show ?case 
    unfolding New_Aut_states_def is_Ctr_Ext_def by blast
next
  case (step Aiminus1 Ai)
  from step(2) show ?case
  proof (cases rule: post_star_rules.cases)
    case (add_trans_pop p''' \<gamma>'' p'' q)
    then have "(Ctr_Loc p', Some \<gamma>', Ctr_Loc_Ext p' \<gamma>') \<notin> Ai"
      using step.prems(2) by blast
    then have nin: "\<nexists>p \<gamma>. (p, \<gamma>, Ctr_Loc_Ext p' \<gamma>') \<in> Aiminus1"
      using local.add_trans_pop(1) step.IH step.prems(1) by fastforce
    then have "Ctr_Loc_Ext p' \<gamma>' \<noteq> q"
      using add_trans_pop(4) lemma_3_4'_Aux_Aux
      by (metis local.add_trans_pop(3) state.distinct(3))
    then have "\<nexists>p \<gamma>. (p, \<gamma>, Ctr_Loc_Ext p' \<gamma>') = (Ctr_Loc p'', \<epsilon>, q)"
      by auto
    then show ?thesis
      using nin add_trans_pop(1) by auto
  next
    case (add_trans_swap p'''' \<gamma>'' p'' \<gamma>''' q)
    then have "(Ctr_Loc p', Some \<gamma>', Ctr_Loc_Ext p' \<gamma>') \<notin> Ai"
      using step.prems(2) by blast
    then have nin: "\<nexists>p \<gamma>. (p, \<gamma>, Ctr_Loc_Ext p' \<gamma>') \<in> Aiminus1"
      using local.add_trans_swap(1) step.IH step.prems(1) by fastforce
    then have "Ctr_Loc_Ext p' \<gamma>' \<noteq> q"
      by (metis state.distinct(4) lemma_3_4'_Aux_Aux local.add_trans_swap(3)) 
    then have "\<nexists>p \<gamma>. (p, \<gamma>, Ctr_Loc_Ext p' \<gamma>') = (Ctr_Loc p'', Some \<gamma>''', q)"
      by auto
    then show ?thesis
      using nin add_trans_swap(1) by auto
  next
    case (add_trans_push_1 p'''' \<gamma>'' p'' \<gamma>''' \<gamma>''''' q)
    then have "(Ctr_Loc p', Some \<gamma>', Ctr_Loc_Ext p' \<gamma>') \<notin> Ai"
      using step.prems(2) by blast
    then show ?thesis
      using add_trans_push_1(1)
      using Un_iff state.inject(2) prod.inject singleton_iff step.IH step.prems(1) by blast 
  next
    case (add_trans_push_2 p'''' \<gamma>'' p'' \<gamma>''' \<gamma>'''' q)
    then have "(Ctr_Loc p', Some \<gamma>', Ctr_Loc_Ext p' \<gamma>') \<notin> Ai"
      using step.prems(2) by blast
    then have nin: "\<nexists>p \<gamma>. (p, \<gamma>, Ctr_Loc_Ext p' \<gamma>') \<in> Aiminus1"
      using local.add_trans_push_2(1) step.IH step.prems(1) by fastforce
    then have "Ctr_Loc_Ext p' \<gamma>' \<noteq> q"
      by (metis state.disc(1,3) lemma_3_4'_Aux_Aux local.add_trans_push_2(3))
    then have "\<nexists>p \<gamma>. (p, \<gamma>, Ctr_Loc_Ext p' \<gamma>') = (Ctr_Loc p'', \<epsilon>, q)"
      by auto
    then show ?thesis
      using nin add_trans_push_2(1) by auto
  qed
qed


lemma lemma_3_4'_Aux_Aux2:
  assumes "post_star_rules\<^sup>*\<^sup>* A A'"
  assumes "\<forall>a b c. (a, b, c) \<in> A \<longrightarrow> a \<notin> New_Aut_states \<and> c \<notin> New_Aut_states"
  assumes "(Ctr_Loc p', Some \<gamma>', Ctr_Loc_Ext p' \<gamma>') \<notin> A'"
  shows "\<nexists>p \<gamma>. (Ctr_Loc_Ext p' \<gamma>', \<gamma>, p) \<in> A'"
  using assms 
proof (induction rule: rtranclp_induct) (* I copy-pasted this prove from above and blindly adjusted it. So it may be a mess. *)
  case base
  then show ?case 
    unfolding New_Aut_states_def is_Ctr_Ext_def by blast
next
  case (step Aiminus1 Ai)
  from step(2) show ?case
  proof (cases rule: post_star_rules.cases)
    case (add_trans_pop p''' \<gamma>'' p'' q)
    then have "(Ctr_Loc p', Some \<gamma>', Ctr_Loc_Ext p' \<gamma>') \<notin> Ai"
      using step.prems(2) by blast
    then have nin: "\<nexists>p \<gamma>. (Ctr_Loc_Ext p' \<gamma>', \<gamma>, p) \<in> Aiminus1"
      using local.add_trans_pop(1) step.IH step.prems(1) by fastforce
    then have "Ctr_Loc_Ext p' \<gamma>' \<noteq> q"
      using add_trans_pop(4) lemma_3_4'_Aux_Aux[of "Ctr_Loc p'''" "[\<gamma>'']" q Aiminus1 "Ctr_Loc_Ext p' \<gamma>'"]
      using PDS_with_P_automaton.lemma_3_4'_Aux local.add_trans_pop(1) step.hyps(1) step.prems(1) step.prems(2)
      using UnI1 local.add_trans_pop(3) by blast 
    then have "\<nexists>p \<gamma>. (p, \<gamma>, Ctr_Loc_Ext p' \<gamma>') = (Ctr_Loc p'', \<epsilon>, q)"
      by auto
    then show ?thesis
      using nin add_trans_pop(1) by auto
  next
    case (add_trans_swap p'''' \<gamma>'' p'' \<gamma>''' q)
    then have "(Ctr_Loc p', Some \<gamma>', Ctr_Loc_Ext p' \<gamma>') \<notin> Ai"
      using step.prems(2) by blast
    then have nin: "\<nexists>p \<gamma>. (Ctr_Loc_Ext p' \<gamma>', \<gamma>, p) \<in> Aiminus1"
      using local.add_trans_swap(1) step.IH step.prems(1) by fastforce
    then have "Ctr_Loc_Ext p' \<gamma>' \<noteq> q"
      using lemma_3_4'_Aux_Aux local.add_trans_swap(3)
      using PDS_with_P_automaton.lemma_3_4'_Aux  UnCI local.add_trans_swap(1) step.hyps(1) step.prems(1) step.prems(2)
      by (metis state.simps(7))
    then have "\<nexists>p \<gamma>. (p, \<gamma>, Ctr_Loc_Ext p' \<gamma>') = (Ctr_Loc p'', Some \<gamma>''', q)"
      by auto
    then show ?thesis
      using nin add_trans_swap(1) by auto
  next
    case (add_trans_push_1 p'''' \<gamma>'' p'' \<gamma>''' \<gamma>''''' q)
    then have "(Ctr_Loc p', Some \<gamma>', Ctr_Loc_Ext p' \<gamma>') \<notin> Ai"
      using step.prems(2) by blast
    then show ?thesis
      using add_trans_push_1(1)
      using Un_iff state.inject prod.inject singleton_iff step.IH step.prems(1) by blast 
  next
    case (add_trans_push_2 p'''' \<gamma>'' p'' \<gamma>''' \<gamma>'''' q)
    then have "(Ctr_Loc p', Some \<gamma>', Ctr_Loc_Ext p' \<gamma>') \<notin> Ai"
      using step.prems(2) by blast
    then have nin: "\<nexists>p \<gamma>. (Ctr_Loc_Ext p' \<gamma>', \<gamma>, p) \<in> Aiminus1"
      using local.add_trans_push_2(1) step.IH step.prems(1) by fastforce
    then have "Ctr_Loc_Ext p' \<gamma>' \<noteq> q"
      using state.disc(3) lemma_3_4'_Aux_Aux local.add_trans_push_2(3)
      using PDS_with_P_automaton.lemma_3_4'_Aux UnCI local.add_trans_push_2(1) step.hyps(1) step.prems(1) step.prems(2) by (metis state.discI(1))
    then have "\<nexists>p \<gamma>. (Ctr_Loc_Ext p' \<gamma>', \<gamma>, p) = (Ctr_Loc p'', \<epsilon>, q)"
      by auto
    then show ?thesis
      using nin add_trans_push_2(1)
      using local.add_trans_push_2 step.prems(2) by auto 
  qed
qed

lemma lemma_3_4_Aux_Aux2:
  assumes "(ss, w) \<in> LTS.path_with_word Ai"
  assumes "\<nexists>p \<gamma>. (Ctr_Loc_Ext p1 \<gamma>1, \<gamma>, p) \<in> Ai"
  assumes "p = p1"
  assumes "hd (transition_list (ss, w)) = t \<and> count (transitions_of (ss, w)) t = 1"
  assumes "t = (Ctr_Loc p1, Some \<gamma>1, Ctr_Loc_Ext p1 \<gamma>1)"
  shows "ss = [Ctr_Loc p1, Ctr_Loc_Ext p1 \<gamma>1] \<and> w = [Some \<gamma>1]"
  using assms 
proof (induction rule: LTS.path_with_word.induct[OF assms(1)])
  case (1 s)
  then show ?case
    by force
next
  case (2 s' ss w s l)
  then show ?case
    by (metis LTS.path_with_word.simps Pair_inject list.distinct(1) list.sel(1) transition_list.simps(1))
qed

lemma lemma_3_4':
  assumes "post_star_rules\<^sup>*\<^sup>* A A'"
  assumes "\<nexists>q \<gamma> q'. (q, \<gamma>, Ctr_Loc q') \<in> A"
  assumes "\<forall>a b c. (a, b, c) \<in> A \<longrightarrow> a \<notin> New_Aut_states \<and> c \<notin> New_Aut_states"
  assumes "(Ctr_Loc p, w, ss, q) \<in> LTS.transition_star_states A'"
  shows "(\<not>is_Ctr_Ext q \<longrightarrow> (\<exists>p' w'. (Ctr_Loc p', w', q) \<in> LTS_\<epsilon>.transition_star_\<epsilon> A \<and> (p',w') \<Rightarrow>\<^sup>* (p, LTS_\<epsilon>.remove_\<epsilon> w))) \<and>
         (is_Ctr_Ext q \<longrightarrow> (the_Ext_Ctr_Loc q, [the_Ext_Label q]) \<Rightarrow>\<^sup>* (p, LTS_\<epsilon>.remove_\<epsilon> w))"
  using assms
proof (induction arbitrary: p q w ss rule: rtranclp_induct)
  case base
  {
    assume ctr_loc: "is_Ctr_Loc q \<or> is_State q"
    then have "(Ctr_Loc p, LTS_\<epsilon>.remove_\<epsilon> w, q) \<in> LTS_\<epsilon>.transition_star_\<epsilon> A"
      using base using LTS_\<epsilon>.transition_star_states_transition_star_\<epsilon> by metis
    then have "\<exists>p' w'. (p', w', q) \<in> LTS_\<epsilon>.transition_star_\<epsilon> A"
      by auto
    then have ?case
      using ctr_loc
      using \<open>(Ctr_Loc p, LTS_\<epsilon>.remove_\<epsilon> w, q) \<in> LTS_\<epsilon>.transition_star_\<epsilon> A\<close> by blast
  }
  moreover
  {
    assume "is_Ctr_Ext q"
    then have ?case
    proof (cases w)
      case Nil
      then have False using base
        using LTS.transition_star_empty LTS.transition_star_states_transition_star \<open>is_Ctr_Ext q\<close>
        by (metis state.disc(7))
      then show ?thesis
        by metis
    next
      case (Cons \<gamma> w_rest)
      then have a: "(Ctr_Loc p, \<gamma>#w_rest, ss, q) \<in> LTS.transition_star_states A"
        using base Cons by blast
      then have "\<exists>s \<gamma>'. (s, \<gamma>', q) \<in> A"
        using LTS.xxxxxxx by metis
      then have False
        using \<open>is_Ctr_Ext q\<close> base.prems(2) New_Aut_states_def by blast
      then show ?thesis
        by auto
    qed
  }
  ultimately
  show ?case
   by (meson state.exhaust_disc)
next
  case (step Aiminus1 Ai)
  from step(2) have "\<exists>p1 \<gamma> p2 w2 q1. Ai = Aiminus1 \<union> {(p1, \<gamma>, q1)} \<and> (p1, \<gamma>, q1) \<notin> Aiminus1"
    by (cases rule: post_star_rules.cases) auto
  then obtain p1 \<gamma> q1 where p1_\<gamma>_p2_w2_q'_p:
    "Ai = Aiminus1 \<union> {(p1, \<gamma>, q1)}" 
    "(p1, \<gamma>, q1) \<notin> Aiminus1"
    by auto
      (* Bemærk! I 3.2 beviset obtainede jeg nogle flere ting!!!!! *)

  define t where "t = (p1, \<gamma>, q1)"
  define j where "j = count (transitions_of' (Ctr_Loc p, w, ss, q)) t"

  note ss_p = step(6)

  from j_def ss_p show ?case
  proof (induction j arbitrary: p q w ss)
    case 0
    then have "(Ctr_Loc p, w, ss, q) \<in> LTS.transition_star_states Aiminus1"
      using lemma_3_2_a'_Aux_3 p1_\<gamma>_p2_w2_q'_p(1) t_def by fastforce
    then show ?case
      using step by auto
  next
    case (Suc j)
    from step(2) show ?case
    proof (cases rule: post_star_rules.cases)
      case (add_trans_pop p2 \<gamma>2 p1 q1) (* p1 shadows p1. q1 shadows q1. A bit brave... *)
      note III = add_trans_pop(3)
      note VI = add_trans_pop(2)
      have t_def: "t = (Ctr_Loc p1, \<epsilon>, q1)"
        using local.add_trans_pop(1) local.add_trans_pop p1_\<gamma>_p2_w2_q'_p(1) t_def by blast
      have init_Ai: "\<nexists>q \<gamma> q'. (q, \<gamma>, Ctr_Loc q') \<in> Ai"
        using step(1,2) step(4)
        using agagagagagaga'''''''''
        by (meson r_into_rtranclp)
      have ttt''': "hd (transition_list (ss, w)) = t \<and> count (transitions_of (ss, w)) t = 1"
      proof -
        have "(ss, w) \<in> LTS.path_with_word Ai"
          using Suc(3) LTS.askdjfklasjflksa by metis
        moreover 
        have "\<nexists>q \<gamma> q'. (q, \<gamma>, Ctr_Loc q') \<in> Ai"
          using init_Ai by auto
        moreover 
        have "0 < count (transitions_of (ss, w)) t"
          by (metis Suc.prems(1) transitions_of'.simps zero_less_Suc)
        moreover 
        have "t = (Ctr_Loc p1, \<epsilon>, q1)"
          using t_def by auto
        moreover 
        have "Ctr_Loc p1 \<in> P_locs"
          by (simp add: P_locs_def)
        ultimately
        show "hd (transition_list (ss, w)) = t \<and> count (transitions_of (ss, w)) t = 1"
          using xxxxxxxxxxxxxxx[of ss w Ai t p1 \<epsilon> q1] by auto
      qed

      have "transition_list (ss, w) \<noteq> []"
        by (metis LTS.askdjfklasjflksa LTS.path_with_word.simps Suc.prems(1) Suc.prems(2) count_empty less_not_refl2 list.distinct(1) transition_list.simps(1) transitions_of'.simps transitions_of.simps(2) zero_less_Suc)
      then have ttt'': "([Ctr_Loc p1,q1], [\<epsilon>]) @\<acute> (tl ss,  tl w) = (ss, w)"
        using  ttt''' t_def help''''' by metis
      then have ttt': "(Ctr_Loc p1, [\<epsilon>], [Ctr_Loc p1,q1], q1) @@\<acute> (q1, tl w, tl ss, q) = (Ctr_Loc p1, w, ss, q)"
        by auto
      have VII: "p = p1"
      proof -
        have "(Ctr_Loc p, w, ss, q) \<in> LTS.transition_star_states Ai"
          using Suc.prems(2) by blast
        moreover
        have "t = hd (transition_list' (Ctr_Loc p, w, ss, q))"
          using \<open>hd (transition_list (ss, w)) = t \<and> count (transitions_of (ss, w)) t = 1\<close> by fastforce
        moreover
        have "transition_list' (Ctr_Loc p, w, ss, q) \<noteq> []"
          by (simp add: \<open>transition_list (ss, w) \<noteq> []\<close>)
        moreover
        have "t = (Ctr_Loc p1, \<epsilon>, q1)"
          using t_def by auto
        ultimately
        show "p = p1"
          using aux''''[of "Ctr_Loc p" w ss q Ai t "Ctr_Loc p1" \<epsilon> q1] 
          by auto
      qed
      have "j=0"
        using Suc(2) \<open>hd (transition_list (ss, w)) = t \<and> count (transitions_of (ss, w)) t = 1\<close> by force
      have "(Ctr_Loc p1, [\<epsilon>], [Ctr_Loc p1, q1], q1) \<in> LTS.transition_star_states Ai"
      proof -
        have "(Ctr_Loc p1, \<epsilon>, q1) \<in> Ai"
          using local.add_trans_pop(1) by auto
        moreover
        have "(Ctr_Loc p1, \<epsilon>, q1) \<notin> Aiminus1"
          by (simp add: local.add_trans_pop)
        ultimately
        show "(Ctr_Loc p1, [\<epsilon>], [Ctr_Loc p1, q1], q1) \<in> LTS.transition_star_states Ai"
          by (meson LTS.transition_star_states.transition_star_states_refl LTS.transition_star_states.transition_star_states_step)
      qed
      have "(q1, tl w, tl ss, q) \<in> LTS.transition_star_states Aiminus1"
      proof -
        from Suc(3) have "(ss, w) \<in> LTS.path_with_word Ai"
          by (meson LTS.askdjfklasjflksa)
        then have one: "(tl ss, tl w) \<in> LTS.path_with_word Ai"
          by (metis LTS.path_with_word.simps \<open>transition_list (ss, w) \<noteq> []\<close> list.sel(3) transition_list.simps(2))
        have two: "0 = count (transitions_of (tl ss, tl w)) (Ctr_Loc p1, \<epsilon>, q1)"
        proof -
          from ttt''' show "0 = count (transitions_of (tl ss, tl w)) (Ctr_Loc p1, \<epsilon>, q1)"
            using count_append_path_with_word[of "[Ctr_Loc p1]" "[\<epsilon>]" "tl ss" "tl w" "Ctr_Loc p1" \<epsilon> q1] t_def
            by (smt (z3) LTS.transition_star_states_last One_nat_def Suc.prems(2) VII \<open>(Ctr_Loc p1, [\<epsilon>], [Ctr_Loc p1, q1], q1) \<in> LTS.transition_star_states Ai\<close> \<open>transition_list (ss, w) \<noteq> []\<close> count_append_path_with_word count_next_hd length_Suc_conv list.sel(1) list.sel(3) list.size(3) one_is_add transition_list.simps(2) transition_list_Cons ttt'')
        qed
        have three: "Ai = Aiminus1 \<union> {(Ctr_Loc p1, \<epsilon>, q1)}"
          using local.add_trans_pop(1) by auto
        from ttt''' one two three lemma_3_2_a'_Aux[OF one, of "Ctr_Loc p1" \<epsilon> q1 Aiminus1] have "(tl ss, tl w) \<in> LTS.path_with_word Aiminus1"
          by auto
        moreover
        have "hd (tl ss) = q1"
          using Suc.prems(2) VII \<open>transition_list (ss, w) \<noteq> []\<close> t_def transition_list_Cons ttt''' by fastforce
        moreover
        have "last ss = q"
          by (metis LTS.transition_star_states_last Suc.prems(2))
        ultimately
        show "(q1, tl w, tl ss, q) \<in> LTS.transition_star_states Aiminus1"
          by (metis (no_types, lifting) LTS.askdjfklasjflksa LTS.askdjfklasjflksa2 LTS.path_with_word_not_empty Suc.prems(2) last_ConsR list.collapse)
      qed
      have "w = \<epsilon> # (tl w)"
        by (metis Suc(3) VII \<open>transition_list (ss, w) \<noteq> []\<close> list.distinct(1) list.exhaust_sel list.sel(1) t_def transition_list_Cons ttt''')
      then have w_tl_\<epsilon>: "LTS_\<epsilon>.remove_\<epsilon> w = LTS_\<epsilon>.remove_\<epsilon> (tl w)"
        by (metis LTS_\<epsilon>.remove_\<epsilon>_def removeAll.simps(2))

      have "\<exists>\<gamma>2'. LTS_\<epsilon>.\<epsilon>_exp \<gamma>2' [\<gamma>2] \<and> (Ctr_Loc p2, \<gamma>2', q1) \<in> LTS.transition_star Aiminus1"
        using add_trans_pop
        by (simp add: LTS_\<epsilon>.epsilon_lemma2) 
      then obtain \<gamma>2' where "LTS_\<epsilon>.\<epsilon>_exp \<gamma>2' [\<gamma>2] \<and> (Ctr_Loc p2, \<gamma>2', q1) \<in> LTS.transition_star Aiminus1"
        by blast
      then have "\<exists>ss2. (Ctr_Loc p2, \<gamma>2', ss2, q1) \<in> LTS.transition_star_states Aiminus1"
        by (simp add: LTS.transition_star_transition_star_states)
      then obtain ss2 where IIII_1: "(Ctr_Loc p2, \<gamma>2', ss2, q1) \<in> LTS.transition_star_states Aiminus1"
        by blast
      have IIII_2: "(q1, tl w, tl ss, q) \<in> LTS.transition_star_states Aiminus1"
        using ttt' Suc(3) Suc(2) \<open>j=0\<close>
        using \<open>(q1, tl w, tl ss, q) \<in> LTS.transition_star_states Aiminus1\<close> by blast
      have IIII: "(Ctr_Loc p2, \<gamma>2' @ tl w, ss2 @ (tl (tl ss)), q) \<in> LTS.transition_star_states Aiminus1"
        using IIII_1 IIII_2 by (meson LTS.transition_star_states_append)

      from Suc(1)[of p2 "\<gamma>2' @ tl w" "ss2 @ (tl (tl ss))" q]
      have V: "(\<not>is_Ctr_Ext q \<longrightarrow>
     (\<exists>p' w'. (Ctr_Loc p', w', q) \<in> LTS_\<epsilon>.transition_star_\<epsilon> A \<and> (p', w') \<Rightarrow>\<^sup>* (p2, LTS_\<epsilon>.remove_\<epsilon> (\<gamma>2' @ tl w)))) \<and>
    (is_Ctr_Ext q \<longrightarrow> (the_Ext_Ctr_Loc q, [the_Ext_Label q]) \<Rightarrow>\<^sup>* (p2, LTS_\<epsilon>.remove_\<epsilon> (\<gamma>2' @ tl w)))"
        using IIII
        using step.IH step.prems(1) step.prems(2) by blast

      have "\<not>is_Ctr_Ext q \<or> is_Ctr_Ext q"
        using state.exhaust_disc by blast
      then show ?thesis
      proof
        assume ctr_q: "\<not>is_Ctr_Ext q"
        then have "\<exists>p' w'. (Ctr_Loc p', w', q) \<in> LTS_\<epsilon>.transition_star_\<epsilon> A \<and> (p', w') \<Rightarrow>\<^sup>* (p2, LTS_\<epsilon>.remove_\<epsilon> (\<gamma>2' @ tl w))"
          using V by auto
        then obtain p' w' where
          VIII:"(Ctr_Loc p', w', q) \<in> LTS_\<epsilon>.transition_star_\<epsilon> A" and gu: "(p', w') \<Rightarrow>\<^sup>* (p2, LTS_\<epsilon>.remove_\<epsilon> (\<gamma>2' @ tl w))"
          by blast
        then have "(p',w') \<Rightarrow>\<^sup>* (p2, LTS_\<epsilon>.remove_\<epsilon> (\<gamma>2' @ tl w)) \<and> 
                   (p2, LTS_\<epsilon>.remove_\<epsilon> (\<gamma>2' @ tl w)) \<Rightarrow>\<^sup>* (p, LTS_\<epsilon>.remove_\<epsilon> (tl w))"
        proof -
          have \<gamma>2'_\<gamma>2: "LTS_\<epsilon>.remove_\<epsilon> \<gamma>2' = [\<gamma>2]"
            by (metis LTS_\<epsilon>.\<epsilon>_exp_def LTS_\<epsilon>.remove_\<epsilon>_def \<open>LTS_\<epsilon>.\<epsilon>_exp \<gamma>2' [\<gamma>2] \<and> (Ctr_Loc p2, \<gamma>2', q1) \<in> LTS.transition_star Aiminus1\<close>)
          have "(p',w') \<Rightarrow>\<^sup>* (p2, LTS_\<epsilon>.remove_\<epsilon> (\<gamma>2' @ tl w))"
            using gu by auto
          moreover
          have one: "(p2, \<gamma>2) \<hookrightarrow> (p, pop)"
            using VI VII by auto 
          from gu have two: "(p', w') \<Rightarrow>\<^sup>* (p2, \<gamma>2 # (LTS_\<epsilon>.remove_\<epsilon> (tl w)))"
            using \<gamma>2'_\<gamma>2
            by (metis Cons_eq_appendI LTS_\<epsilon>.remove_\<epsilon>_append_dist self_append_conv2) 
          from one two have "(p2,  \<gamma>2 # (LTS_\<epsilon>.remove_\<epsilon> (tl w))) \<Rightarrow>\<^sup>* (p, LTS_\<epsilon>.remove_\<epsilon> (tl w))"
            using  VIII
            by (metis PDS.transition_rel.intros append_self_conv2 op_labels.simps(1) r_into_rtranclp step_relp_def) (* VII *) 
          then have "(p2, LTS_\<epsilon>.remove_\<epsilon> (\<gamma>2' @ tl w)) \<Rightarrow>\<^sup>* (p, LTS_\<epsilon>.remove_\<epsilon> (tl w))"
            by (simp add: LTS_\<epsilon>.remove_\<epsilon>_append_dist \<gamma>2'_\<gamma>2)
          ultimately
          show "(p',w') \<Rightarrow>\<^sup>* (p2, LTS_\<epsilon>.remove_\<epsilon> (\<gamma>2' @ tl w)) \<and> 
                (p2, LTS_\<epsilon>.remove_\<epsilon> (\<gamma>2' @ tl w)) \<Rightarrow>\<^sup>* (p, LTS_\<epsilon>.remove_\<epsilon> (tl w))"
            by auto
        qed
        then have "(p',w') \<Rightarrow>\<^sup>* (p, LTS_\<epsilon>.remove_\<epsilon> (tl w)) \<and> (Ctr_Loc p', w', q) \<in> LTS_\<epsilon>.transition_star_\<epsilon> A"
          using VIII by force
        then have "\<exists>p' w'. (Ctr_Loc p', w', q) \<in> LTS_\<epsilon>.transition_star_\<epsilon> A \<and> (p', w') \<Rightarrow>\<^sup>* (p, LTS_\<epsilon>.remove_\<epsilon> w)"
          using w_tl_\<epsilon> by auto
        then show ?thesis
          using ctr_q \<open>p = p1\<close> by blast 
      next
        assume "is_Ctr_Ext q"
        from V have "(the_Ext_Ctr_Loc q, [the_Ext_Label q]) \<Rightarrow>\<^sup>* (p2, \<gamma>2#(LTS_\<epsilon>.remove_\<epsilon> w))"
          by (metis LTS_\<epsilon>.\<epsilon>_exp_def LTS_\<epsilon>.remove_\<epsilon>_append_dist LTS_\<epsilon>.remove_\<epsilon>_def \<open>LTS_\<epsilon>.\<epsilon>_exp \<gamma>2' [\<gamma>2] \<and> (Ctr_Loc p2, \<gamma>2', q1) \<in> LTS.transition_star Aiminus1\<close> \<open>is_Ctr_Ext q\<close> append_Cons append_self_conv2 w_tl_\<epsilon>)
          
        then have "(the_Ext_Ctr_Loc q, [the_Ext_Label q]) \<Rightarrow>\<^sup>* (p1, LTS_\<epsilon>.remove_\<epsilon> w)"
          using VI by (metis append_Nil op_labels.simps(1) rtranclp.simps step_relp_def2) 
        then have "(the_Ext_Ctr_Loc q, [the_Ext_Label q]) \<Rightarrow>\<^sup>* (p, LTS_\<epsilon>.remove_\<epsilon> w)"
          using VII by auto
        then show ?thesis
          using \<open>is_Ctr_Ext q\<close> by blast
      qed
    next
      case (add_trans_swap p2 \<gamma>2 p1 \<gamma>' q1) (* Copied and ajusted from previous case *)
      note III = add_trans_swap(3)
      note VI = add_trans_swap(2)
      have t_def: "t = (Ctr_Loc p1, Some \<gamma>', q1)"
        using local.add_trans_swap(1) local.add_trans_swap p1_\<gamma>_p2_w2_q'_p(1) t_def by blast
      have init_Ai: "\<nexists>q \<gamma> q'. (q, \<gamma>, Ctr_Loc q') \<in> Ai"
        using step(1,2) step(4)
        using agagagagagaga'''''''''
        by (meson r_into_rtranclp)
      have ttt''': "hd (transition_list (ss, w)) = t \<and> count (transitions_of (ss, w)) t = 1"
      proof -
        have "(ss, w) \<in> LTS.path_with_word Ai"
          using Suc(3) LTS.askdjfklasjflksa by metis
        moreover 
        have "\<nexists>q \<gamma> q'. (q, \<gamma>, Ctr_Loc q') \<in> Ai"
          using init_Ai by auto
        moreover 
        have "0 < count (transitions_of (ss, w)) t"
          by (metis Suc.prems(1) transitions_of'.simps zero_less_Suc)
        moreover 
        have "t = (Ctr_Loc p1, Some \<gamma>', q1)"
          using t_def
          by auto
        moreover 
        have "Ctr_Loc p1 \<in> P_locs"
          using P_locs_def by force
        ultimately
        show "hd (transition_list (ss, w)) = t \<and> count (transitions_of (ss, w)) t = 1"
          using xxxxxxxxxxxxxxx[of ss w Ai t p1 _ q1] by auto
      qed

      have "transition_list (ss, w) \<noteq> []"
        by (metis LTS.askdjfklasjflksa LTS.path_with_word.simps Suc.prems(1) Suc.prems(2) count_empty less_not_refl2 list.distinct(1) transition_list.simps(1) transitions_of'.simps transitions_of.simps(2) zero_less_Suc)
      then have ttt'': "([Ctr_Loc p1,q1], [Some \<gamma>']) @\<acute> (tl ss,  tl w) = (ss, w)"
        using  ttt''' t_def help''''' by metis
      then have ttt': "(Ctr_Loc p1, [Some \<gamma>'], [Ctr_Loc p1,q1], q1) @@\<acute> (q1, tl w, tl ss, q) = (Ctr_Loc p1, w, ss, q)"
        by auto
      have VII: "p = p1"
      proof -
        have "(Ctr_Loc p, w, ss, q) \<in> LTS.transition_star_states Ai"
          using Suc.prems(2) by blast
        moreover
        have "t = hd (transition_list' (Ctr_Loc p, w, ss, q))"
          using \<open>hd (transition_list (ss, w)) = t \<and> count (transitions_of (ss, w)) t = 1\<close> by fastforce
        moreover
        have "transition_list' (Ctr_Loc p, w, ss, q) \<noteq> []"
          by (simp add: \<open>transition_list (ss, w) \<noteq> []\<close>)
        moreover
        have "t = (Ctr_Loc p1, Some \<gamma>', q1)"
          using t_def by auto
        ultimately
        show "p = p1"
          using aux''''[of "Ctr_Loc p" w ss q Ai t "Ctr_Loc p1" _ q1]
          by blast
      qed
      have "j=0"
        using Suc(2) \<open>hd (transition_list (ss, w)) = t \<and> count (transitions_of (ss, w)) t = 1\<close> by force
      have "(Ctr_Loc p1, [Some \<gamma>'], [Ctr_Loc p1, q1], q1) \<in> LTS.transition_star_states Ai"
      proof -
        have "(Ctr_Loc p1, Some \<gamma>', q1) \<in> Ai"
          using local.add_trans_swap(1) by auto
        moreover
        have "(Ctr_Loc p1, Some \<gamma>', q1) \<notin> Aiminus1"
          using local.add_trans_swap(4) by blast
        ultimately
        show "(Ctr_Loc p1, [Some \<gamma>'], [Ctr_Loc p1, q1], q1) \<in> LTS.transition_star_states Ai"
          by (meson LTS.transition_star_states.transition_star_states_refl LTS.transition_star_states.transition_star_states_step)
      qed
      have "(q1, tl w, tl ss, q) \<in> LTS.transition_star_states Aiminus1"
      proof -
        from Suc(3) have "(ss, w) \<in> LTS.path_with_word Ai"
          by (meson LTS.askdjfklasjflksa)
        then have one: "(tl ss, tl w) \<in> LTS.path_with_word Ai"
          by (metis LTS.path_with_word.simps \<open>transition_list (ss, w) \<noteq> []\<close> list.sel(3) transition_list.simps(2))
        have two: "0 = count (transitions_of (tl ss, tl w)) (Ctr_Loc p1, Some \<gamma>', q1)"
        proof -
          from ttt''' show "0 = count (transitions_of (tl ss, tl w)) (Ctr_Loc p1, Some \<gamma>', q1)"
            using count_append_path_with_word[of "[Ctr_Loc p1]" _ "tl ss" "tl w" "Ctr_Loc p1" _ q1] t_def
            by (smt (z3) LTS.transition_star_states_last One_nat_def Suc.prems(2) VII \<open>(Ctr_Loc p1, [Some \<gamma>'], [Ctr_Loc p1, q1], q1) \<in> LTS.transition_star_states Ai\<close> \<open>transition_list (ss, w) \<noteq> []\<close> count_append_path_with_word count_next_hd length_Suc_conv list.sel(1) list.sel(3) list.size(3) one_is_add transition_list.simps(2) transition_list_Cons ttt'')
        qed
        have three: "Ai = Aiminus1 \<union> {(Ctr_Loc p1, Some \<gamma>', q1)}"
          using local.add_trans_swap(1) by auto 
        from ttt''' one two three lemma_3_2_a'_Aux[OF one, of "Ctr_Loc p1" _ q1 Aiminus1] have "(tl ss, tl w) \<in> LTS.path_with_word Aiminus1"
          by auto
        moreover
        have "hd (tl ss) = q1"
          using Suc.prems(2) VII \<open>transition_list (ss, w) \<noteq> []\<close> t_def transition_list_Cons ttt''' by fastforce
        moreover
        have "last ss = q"
          by (metis LTS.transition_star_states_last Suc.prems(2))
        ultimately
        show "(q1, tl w, tl ss, q) \<in> LTS.transition_star_states Aiminus1"
          by (metis (no_types, lifting) LTS.askdjfklasjflksa LTS.askdjfklasjflksa2 LTS.path_with_word_not_empty Suc.prems(2) last_ConsR list.collapse)
      qed
      have "w = Some \<gamma>' # (tl w)"
        by (metis Suc(3) VII \<open>transition_list (ss, w) \<noteq> []\<close> list.distinct(1) list.exhaust_sel list.sel(1) t_def transition_list_Cons ttt''')
      then have w_tl_\<epsilon>: "LTS_\<epsilon>.remove_\<epsilon> w = LTS_\<epsilon>.remove_\<epsilon> (Some \<gamma>'#tl w)"
        using LTS_\<epsilon>.remove_\<epsilon>_def removeAll.simps(2)
        by presburger 
      have "\<exists>\<gamma>2'. LTS_\<epsilon>.\<epsilon>_exp \<gamma>2' [\<gamma>2] \<and> (Ctr_Loc p2, \<gamma>2', q1) \<in> LTS.transition_star Aiminus1"
        using add_trans_swap by (simp add: LTS_\<epsilon>.epsilon_lemma2) 
      then obtain \<gamma>2' where "LTS_\<epsilon>.\<epsilon>_exp \<gamma>2' [\<gamma>2] \<and> (Ctr_Loc p2, \<gamma>2', q1) \<in> LTS.transition_star Aiminus1"
        by blast
      then have "\<exists>ss2. (Ctr_Loc p2, \<gamma>2', ss2, q1) \<in> LTS.transition_star_states Aiminus1"
        by (simp add: LTS.transition_star_transition_star_states)
      then obtain ss2 where IIII_1: "(Ctr_Loc p2, \<gamma>2', ss2, q1) \<in> LTS.transition_star_states Aiminus1"
        by blast
      have IIII_2: "(q1, tl w, tl ss, q) \<in> LTS.transition_star_states Aiminus1"
        using ttt' Suc(3) Suc(2) \<open>j=0\<close>
        using \<open>(q1, tl w, tl ss, q) \<in> LTS.transition_star_states Aiminus1\<close> by blast
      have IIII: "(Ctr_Loc p2, \<gamma>2' @ tl w, ss2 @ (tl (tl ss)), q) \<in> LTS.transition_star_states Aiminus1"
        using IIII_1 IIII_2 by (meson LTS.transition_star_states_append)

      from Suc(1)[of p2 "\<gamma>2' @ tl w" "ss2 @ (tl (tl ss))" q]
      have V: "(\<not>is_Ctr_Ext q \<longrightarrow>
     (\<exists>p' w'. (Ctr_Loc p', w', q) \<in> LTS_\<epsilon>.transition_star_\<epsilon> A \<and> (p', w') \<Rightarrow>\<^sup>* (p2, LTS_\<epsilon>.remove_\<epsilon> (\<gamma>2' @ tl w)))) \<and>
    (is_Ctr_Ext q \<longrightarrow> (the_Ext_Ctr_Loc q, [the_Ext_Label q]) \<Rightarrow>\<^sup>* (p2, LTS_\<epsilon>.remove_\<epsilon> (\<gamma>2' @ tl w)))"
        using IIII
        using step.IH step.prems(1) step.prems(2) by blast

      have "\<not>is_Ctr_Ext q \<or> is_Ctr_Ext q"
        using state.exhaust_disc by blast
      then show ?thesis
      proof
        assume ctr_q: "\<not>is_Ctr_Ext q"
        then have "\<exists>p' w'. (Ctr_Loc p', w', q) \<in> LTS_\<epsilon>.transition_star_\<epsilon> A \<and> (p', w') \<Rightarrow>\<^sup>* (p2, LTS_\<epsilon>.remove_\<epsilon> (\<gamma>2' @ tl w))"
          using V by auto
        then obtain p' w' where
          VIII:"(Ctr_Loc p', w', q) \<in> LTS_\<epsilon>.transition_star_\<epsilon> A" and gu: "(p', w') \<Rightarrow>\<^sup>* (p2, LTS_\<epsilon>.remove_\<epsilon> (\<gamma>2' @ tl w))"
          by blast
        then have "(p',w') \<Rightarrow>\<^sup>* (p2, LTS_\<epsilon>.remove_\<epsilon> (\<gamma>2' @ tl w)) \<and> 
                   (p2, LTS_\<epsilon>.remove_\<epsilon> (\<gamma>2' @ tl w)) \<Rightarrow>\<^sup>* (p, \<gamma>' # LTS_\<epsilon>.remove_\<epsilon> (tl w))"
        proof -
          have \<gamma>2'_\<gamma>2: "LTS_\<epsilon>.remove_\<epsilon> \<gamma>2' = [\<gamma>2]"
            by (metis LTS_\<epsilon>.\<epsilon>_exp_def LTS_\<epsilon>.remove_\<epsilon>_def \<open>LTS_\<epsilon>.\<epsilon>_exp \<gamma>2' [\<gamma>2] \<and> (Ctr_Loc p2, \<gamma>2', q1) \<in> LTS.transition_star Aiminus1\<close>)
          have "(p',w') \<Rightarrow>\<^sup>* (p2, LTS_\<epsilon>.remove_\<epsilon> (\<gamma>2' @ tl w))"
            using gu by auto
          moreover
          have one: "(p2, \<gamma>2) \<hookrightarrow> (p, swap \<gamma>')"
            using VI VII by auto 
          from gu have two: "(p', w') \<Rightarrow>\<^sup>* (p2, \<gamma>2 # (LTS_\<epsilon>.remove_\<epsilon> (tl w)))"
            using \<gamma>2'_\<gamma>2
            by (metis Cons_eq_appendI LTS_\<epsilon>.remove_\<epsilon>_append_dist self_append_conv2) 
          from one two have "(p2,  \<gamma>2 # (LTS_\<epsilon>.remove_\<epsilon> (tl w))) \<Rightarrow>\<^sup>* (p, \<gamma>' # LTS_\<epsilon>.remove_\<epsilon> (tl w))"
            using  VIII
            using PDS.transition_rel.intros append_self_conv2 op_labels.simps(1) r_into_rtranclp step_relp_def
            by fastforce
          then have "(p2, LTS_\<epsilon>.remove_\<epsilon> (\<gamma>2' @ tl w)) \<Rightarrow>\<^sup>* (p, \<gamma>' # LTS_\<epsilon>.remove_\<epsilon> (tl w))"
            by (simp add: LTS_\<epsilon>.remove_\<epsilon>_append_dist \<gamma>2'_\<gamma>2)
          ultimately
          show "(p',w') \<Rightarrow>\<^sup>* (p2, LTS_\<epsilon>.remove_\<epsilon> (\<gamma>2' @ tl w)) \<and> 
                (p2, LTS_\<epsilon>.remove_\<epsilon> (\<gamma>2' @ tl w)) \<Rightarrow>\<^sup>* (p, \<gamma>' # LTS_\<epsilon>.remove_\<epsilon> (tl w))"
            by auto
        qed
        then have "(p',w') \<Rightarrow>\<^sup>* (p, \<gamma>' # LTS_\<epsilon>.remove_\<epsilon> (tl w)) \<and> (Ctr_Loc p', w', q) \<in> LTS_\<epsilon>.transition_star_\<epsilon> A"
          using VIII by force
        then have "\<exists>p' w'. (Ctr_Loc p', w', q) \<in> LTS_\<epsilon>.transition_star_\<epsilon> A \<and> (p', w') \<Rightarrow>\<^sup>* (p, LTS_\<epsilon>.remove_\<epsilon> w)"
          using LTS_\<epsilon>.ffffffff by (metis \<open>w = Some \<gamma>' # tl w\<close>) 
        then show ?thesis
          using ctr_q \<open>p = p1\<close> by blast 
      next
        assume "is_Ctr_Ext q"
        from V this have "(the_Ext_Ctr_Loc q, [the_Ext_Label q]) \<Rightarrow>\<^sup>* (p2, LTS_\<epsilon>.remove_\<epsilon> (\<gamma>2' @ tl w))"
          by auto
        then have "(the_Ext_Ctr_Loc q, [the_Ext_Label q]) \<Rightarrow>\<^sup>* (p2, \<gamma>2#(LTS_\<epsilon>.remove_\<epsilon> (tl w)))"
          by (metis LTS_\<epsilon>.\<epsilon>_exp_def LTS_\<epsilon>.remove_\<epsilon>_append_dist LTS_\<epsilon>.remove_\<epsilon>_def \<open>LTS_\<epsilon>.\<epsilon>_exp \<gamma>2' [\<gamma>2] \<and> (Ctr_Loc p2, \<gamma>2', q1) \<in> LTS.transition_star Aiminus1\<close> append_Cons append_self_conv2)
        then have "(the_Ext_Ctr_Loc q, [the_Ext_Label q]) \<Rightarrow>\<^sup>* (p1, \<gamma>' # LTS_\<epsilon>.remove_\<epsilon> (tl w))"
          using VI
          by (metis (no_types, hide_lams) append_Cons append_Nil op_labels.simps(2) rtranclp.rtrancl_into_rtrancl step_relp_def2)
        then have "(the_Ext_Ctr_Loc q, [the_Ext_Label q]) \<Rightarrow>\<^sup>* (p, \<gamma>' # LTS_\<epsilon>.remove_\<epsilon> (tl w))"
          using VII by auto
        then show ?thesis
          using \<open>is_Ctr_Ext q\<close>
          by (metis LTS_\<epsilon>.ffffffff w_tl_\<epsilon>)
      qed
    next
      case (add_trans_push_1 p2 \<gamma>2 p1 \<gamma>1 \<gamma>'' q1')
      then have t_def: "t = (Ctr_Loc p1, Some \<gamma>1, Ctr_Loc_Ext p1 \<gamma>1)"
        using local.add_trans_pop(1) local.add_trans_pop p1_\<gamma>_p2_w2_q'_p(1) t_def by blast
      have init_Ai: "\<nexists>q \<gamma> q'. (q, \<gamma>, Ctr_Loc q') \<in> Ai"
        using step(1,2) step(4)
        using agagagagagaga'''''''''
        by (meson r_into_rtranclp)
      have ttt''': "hd (transition_list (ss, w)) = t \<and> count (transitions_of (ss, w)) t = 1"
      proof -
        have "(ss, w) \<in> LTS.path_with_word Ai"
          using Suc(3) LTS.askdjfklasjflksa by metis
        moreover 
        have "\<nexists>q \<gamma> q'. (q, \<gamma>, Ctr_Loc q') \<in> Ai"
          using init_Ai by auto
        moreover 
        have "0 < count (transitions_of (ss, w)) t"
          by (metis Suc.prems(1) transitions_of'.simps zero_less_Suc)
        moreover 
        have "t = (Ctr_Loc p1, Some \<gamma>1, Ctr_Loc_Ext p1 \<gamma>1)"
          using t_def by auto
        moreover 
        have "Ctr_Loc p1 \<in> P_locs"
          using P_locs_def by fastforce
        ultimately
        show "hd (transition_list (ss, w)) = t \<and> count (transitions_of (ss, w)) t = 1"
          using xxxxxxxxxxxxxxx[of ss w Ai t] by auto
      qed
      have "transition_list (ss, w) \<noteq> []"
        by (metis LTS.askdjfklasjflksa LTS.path_with_word.simps Suc.prems(1) Suc.prems(2) count_empty less_not_refl2 list.distinct(1) transition_list.simps(1) transitions_of'.simps transitions_of.simps(2) zero_less_Suc)

      have VII: "p = p1"
      proof -
        have "(Ctr_Loc p, w, ss, q) \<in> LTS.transition_star_states Ai"
          using Suc.prems(2) by blast
        moreover
        have "t = hd (transition_list' (Ctr_Loc p, w, ss, q))"
          using \<open>hd (transition_list (ss, w)) = t \<and> count (transitions_of (ss, w)) t = 1\<close> by fastforce
        moreover
        have "transition_list' (Ctr_Loc p, w, ss, q) \<noteq> []"
          by (simp add: \<open>transition_list (ss, w) \<noteq> []\<close>)
        moreover
        have "t = (Ctr_Loc p1, Some \<gamma>1, Ctr_Loc_Ext p1 \<gamma>1)"
          using t_def by auto
        ultimately
        show "p = p1"
          using aux''''[of "Ctr_Loc p" w ss q Ai t "Ctr_Loc p1" "Some \<gamma>1" "Ctr_Loc_Ext p1 \<gamma>1"] 
          by auto
      qed
      from add_trans_push_1(4) have "\<nexists>p \<gamma>. (Ctr_Loc_Ext p1 \<gamma>1, \<gamma>, p) \<in> Aiminus1"
        using lemma_3_4'_Aux_Aux2[OF step(1) assms(3) add_trans_push_1(4)]
        by auto
      then have "\<nexists>p \<gamma>. (Ctr_Loc_Ext p1 \<gamma>1, \<gamma>, p) \<in> Ai"
        using local.add_trans_push_1(1) by blast
      then have ss_w_short: "ss = [Ctr_Loc p1, Ctr_Loc_Ext p1 \<gamma>1] \<and> w = [Some \<gamma>1]"
        using Suc.prems(2) VII \<open>hd (transition_list (ss, w)) = t \<and> count (transitions_of (ss, w)) t = 1\<close> t_def
        using lemma_3_4_Aux_Aux2
        by (metis LTS.askdjfklasjflksa)
      then have q_ext: "q = Ctr_Loc_Ext p1 \<gamma>1"
        using LTS.transition_star_states_last Suc.prems(2) by fastforce
      have "(p1, [\<gamma>1]) \<Rightarrow>\<^sup>* (p, LTS_\<epsilon>.remove_\<epsilon> w)"
        using ss_w_short unfolding LTS_\<epsilon>.remove_\<epsilon>_def apply auto
        using VII by force
      thm Suc(1)
      have "(the_Ext_Ctr_Loc q, [the_Ext_Label q]) \<Rightarrow>\<^sup>* (p, LTS_\<epsilon>.remove_\<epsilon> w)"
        by (simp add: \<open>(p1, [\<gamma>1]) \<Rightarrow>\<^sup>* (p, LTS_\<epsilon>.remove_\<epsilon> w)\<close> q_ext)
      then show ?thesis
        using q_ext by auto
    next
      case (add_trans_push_2 p2 \<gamma>2 p1 \<gamma>1 \<gamma>'' q') (* Copied and adjusted from previous case *)
      note IX = add_trans_push_2(3)
      note XIII = add_trans_push_2(2)
      have t_def: "t = (Ctr_Loc_Ext p1 \<gamma>1, Some \<gamma>'', q')"
        using local.add_trans_swap(1) local.add_trans_push_2 p1_\<gamma>_p2_w2_q'_p(1) t_def by blast
      have init_Ai: "\<nexists>q \<gamma> q'. (q, \<gamma>, Ctr_Loc q') \<in> Ai"
        using step(1,2) step(4)
        using agagagagagaga'''''''''
        by (meson r_into_rtranclp)

      from Suc(3) Suc(2) split_at_first_t[of "Ctr_Loc p" w ss q Ai j "Ctr_Loc_Ext p1 \<gamma>1" "Some \<gamma>''" q' Aiminus1] t_def
      have "\<exists>u v u_ss v_ss.
              ss = u_ss @ v_ss \<and>
              w = u @ [Some \<gamma>''] @ v \<and>
              (Ctr_Loc p, u, u_ss, Ctr_Loc_Ext p1 \<gamma>1) \<in> LTS.transition_star_states Aiminus1 \<and>
              (Ctr_Loc_Ext p1 \<gamma>1, [Some \<gamma>''], q') \<in> LTS.transition_star Ai \<and> (q', v, v_ss, q) \<in> LTS.transition_star_states Ai"
        using local.add_trans_push_2(1) local.add_trans_push_2(4) by blast
      then obtain u v u_ss v_ss where
           aaa: "ss = u_ss @ v_ss" and
           bbb: "w = u @ [Some \<gamma>''] @ v" and
           X_1: "(Ctr_Loc p, u, u_ss, Ctr_Loc_Ext p1 \<gamma>1) \<in> LTS.transition_star_states Aiminus1" and
           ccc: "(Ctr_Loc_Ext p1 \<gamma>1, [Some \<gamma>''], q') \<in> LTS.transition_star Ai" and
           ddd: "(q', v, v_ss, q) \<in> LTS.transition_star_states Ai"
        by auto
      from step(3)[of p u u_ss "Ctr_Loc_Ext p1 \<gamma>1"] X_1 have
        "(\<not>is_Ctr_Ext (Ctr_Loc_Ext p1 \<gamma>1) \<longrightarrow>
           (\<exists>p' w'. (Ctr_Loc p', w', Ctr_Loc_Ext p1 \<gamma>1) \<in> LTS_\<epsilon>.transition_star_\<epsilon> A \<and> (p', w') \<Rightarrow>\<^sup>* (p, LTS_\<epsilon>.remove_\<epsilon> u))) \<and>
         (is_Ctr_Ext (Ctr_Loc_Ext p1 \<gamma>1) \<longrightarrow> 
           (the_Ext_Ctr_Loc (Ctr_Loc_Ext p1 \<gamma>1), [the_Ext_Label (Ctr_Loc_Ext p1 \<gamma>1)]) \<Rightarrow>\<^sup>* (p, LTS_\<epsilon>.remove_\<epsilon> u))"
        using step.prems(1) step.prems(2) by auto 
      then have "(the_Ext_Ctr_Loc (Ctr_Loc_Ext p1 \<gamma>1), [the_Ext_Label (Ctr_Loc_Ext p1 \<gamma>1)]) \<Rightarrow>\<^sup>* (p, LTS_\<epsilon>.remove_\<epsilon> u)"
        by auto
      then have "(p1, [\<gamma>1]) \<Rightarrow>\<^sup>* (p, LTS_\<epsilon>.remove_\<epsilon> u)"
        by auto
      term \<gamma>2
      from IX have "\<exists>\<gamma>2\<epsilon> \<gamma>2ss. LTS_\<epsilon>.\<epsilon>_exp \<gamma>2\<epsilon> [\<gamma>2] \<and> (Ctr_Loc p2, \<gamma>2\<epsilon>, \<gamma>2ss, q') \<in> LTS.transition_star_states Aiminus1"
        by (meson LTS.transition_star_transition_star_states LTS_\<epsilon>.epsilon_lemma2)
      then obtain \<gamma>2\<epsilon> \<gamma>2ss where XI_1: "LTS_\<epsilon>.\<epsilon>_exp \<gamma>2\<epsilon> [\<gamma>2] \<and> (Ctr_Loc p2, \<gamma>2\<epsilon>, \<gamma>2ss, q') \<in> LTS.transition_star_states Aiminus1"
        by blast
      have "(q', v, v_ss, q) \<in> LTS.transition_star_states Ai"
        by (simp add: \<open>(q', v, v_ss, q) \<in> LTS.transition_star_states Ai\<close>)
      have inddd:
        "(\<not>is_Ctr_Ext q \<longrightarrow> (\<exists>p' w'. (Ctr_Loc p', w', q) \<in> LTS_\<epsilon>.transition_star_\<epsilon> A \<and> (p', w') \<Rightarrow>\<^sup>* (p2, LTS_\<epsilon>.remove_\<epsilon> (\<gamma>2\<epsilon> @ v)))) \<and>
         (is_Ctr_Ext q \<longrightarrow> (the_Ext_Ctr_Loc q, [the_Ext_Label q]) \<Rightarrow>\<^sup>* (p2, LTS_\<epsilon>.remove_\<epsilon> (\<gamma>2\<epsilon> @ v)))"
      proof -
        have one: "length \<gamma>2ss = Suc (length \<gamma>2\<epsilon>)"
          by (meson LTS.transition_star_states_length XI_1)
          
        have two: "v_ss \<noteq> []"
          by (metis LTS.transition_star_states.simps \<open>(q', v, v_ss, q) \<in> LTS.transition_star_states Ai\<close> list.distinct(1))
          
        have three: "last \<gamma>2ss = hd v_ss"
          by (metis LTS.transition_star_states_hd LTS.transition_star_states_last XI_1 \<open>(q', v, v_ss, q) \<in> LTS.transition_star_states Ai\<close>)


        have cv: "j = count (transitions_of ((v_ss, v))) t"
        proof -

          have a1: "Ctr_Loc_Ext p1 \<gamma>1 = last u_ss"
            by (meson LTS.transition_star_states_last X_1)
          have a2: "q' = hd v_ss"
            by (meson LTS.transition_star_states_hd ddd)
          have a4: "Some \<gamma>'' # v = [Some \<gamma>''] @ v"
            by auto
          have a5: "Ctr_Loc_Ext p1 \<gamma>1 = last u_ss \<and> q' = hd v_ss"
            using a1 a2 by blast

          have "count (transitions_of' (((Ctr_Loc p, u, u_ss, Ctr_Loc_Ext p1 \<gamma>1), Some \<gamma>'') @@\<^sup>\<gamma> (q', v, v_ss, q)))
                (Ctr_Loc_Ext p1 \<gamma>1, Some \<gamma>'', q') =
                count (transitions_of' (Ctr_Loc p, u, u_ss, Ctr_Loc_Ext p1 \<gamma>1)) (Ctr_Loc_Ext p1 \<gamma>1, Some \<gamma>'', q') +
                (if Ctr_Loc_Ext p1 \<gamma>1 = last u_ss \<and> q' = hd v_ss \<and> Some \<gamma>'' = Some \<gamma>'' then 1 else 0) +
                count (transitions_of' (q', v, v_ss, q)) (Ctr_Loc_Ext p1 \<gamma>1, Some \<gamma>'', q')"
            using count_append_transition_star_states_\<gamma>[of u_ss u v_ss "Ctr_Loc p" "Ctr_Loc_Ext p1 \<gamma>1" "Some \<gamma>''" q' v q "Ctr_Loc_Ext p1 \<gamma>1" "Some \<gamma>''" q'] t_def aaa bbb X_1
            by (meson LTS.transition_star_states_length two)
          then have a3: "count (transitions_of (u_ss @ v_ss, u @ Some \<gamma>'' # v)) (last u_ss, Some \<gamma>'', hd v_ss) = Suc (count (transitions_of (u_ss, u)) (last u_ss, Some \<gamma>'', hd v_ss) + count (transitions_of (v_ss, v)) (last u_ss, Some \<gamma>'', hd v_ss))"
            using a1 a2 by auto
          have "j = count (transitions_of' ((q',v, v_ss, q))) t"
            using a3 a2 a1 a4 by (smt (z3) One_nat_def Suc.prems(1) Suc_inject X_1 aaa add_Suc_right add_Suc_shift avoid_count_zero bbb counting local.add_trans_push_2(4) plus_1_eq_Suc same_append_eq t_def transitions_of'.simps)
          show "j = count (transitions_of ((v_ss, v))) t"
            using \<open>j = count (transitions_of' (q', v, v_ss, q)) t\<close> by force
        qed
        have "(Ctr_Loc p2, \<gamma>2\<epsilon>, \<gamma>2ss, q') \<in> LTS.transition_star_states Aiminus1"
          using XI_1 by blast
        then have c\<gamma>2: "count (transitions_of (\<gamma>2ss, \<gamma>2\<epsilon>)) t = 0"
          using avoid_count_zero local.add_trans_push_2(4) t_def by fastforce
        have "j = count (transitions_of ((\<gamma>2ss, \<gamma>2\<epsilon>) @\<acute> (v_ss, v))) t"
          using LTS.count_append_path_with_word[of \<gamma>2ss \<gamma>2\<epsilon> v_ss v "Ctr_Loc_Ext p1 \<gamma>1" "Some \<gamma>''" q'] t_def
            c\<gamma>2 cv one two three
          by force 

        have "j = count (transitions_of' (Ctr_Loc p2, \<gamma>2\<epsilon> @ v, \<gamma>2ss @ tl v_ss, q)) t"
          by (simp add: \<open>j = count (transitions_of ((\<gamma>2ss, \<gamma>2\<epsilon>) @\<acute> (v_ss, v))) t\<close>)

        have "(\<gamma>2ss, \<gamma>2\<epsilon>) \<in> LTS.path_with_word Aiminus1"
          by (meson LTS.askdjfklasjflksa \<open>(Ctr_Loc p2, \<gamma>2\<epsilon>, \<gamma>2ss, q') \<in> LTS.transition_star_states Aiminus1\<close>)
        then have gugugu: "(\<gamma>2ss, \<gamma>2\<epsilon>) \<in> LTS.path_with_word Ai"
          using add_trans_push_2(1) 
          path_with_word_mono'[of \<gamma>2ss \<gamma>2\<epsilon> Aiminus1 Ai] by auto

        have gugugu3: "last \<gamma>2ss = hd v_ss"
          using three by blast
        have gugugu2: "(v_ss, v) \<in> LTS.path_with_word Ai"
          by (meson LTS.askdjfklasjflksa \<open>(q', v, v_ss, q) \<in> LTS.transition_star_states Ai\<close>)
        have "(\<gamma>2ss, \<gamma>2\<epsilon>) @\<acute> (v_ss, v) \<in> LTS.path_with_word Ai"
          using gugugu gugugu2 LTS.append_path_with_word_path_with_word gugugu3
          by auto

        have "(\<gamma>2ss @ tl v_ss, \<gamma>2\<epsilon> @ v) \<in> LTS.path_with_word Ai"
          using \<open>(\<gamma>2ss, \<gamma>2\<epsilon>) @\<acute> (v_ss, v) \<in> LTS.path_with_word Ai\<close> by auto


        have "(Ctr_Loc p2, \<gamma>2\<epsilon> @ v, \<gamma>2ss @ tl v_ss, q) \<in> LTS.transition_star_states Ai"
          by (metis (no_types, lifting) LTS.askdjfklasjflksa2 LTS.transition_star_states_append LTS.transition_star_states_hd XI_1 \<open>(q', v, v_ss, q) \<in> LTS.transition_star_states Ai\<close> gugugu three)
          
        from this Suc(1)[of p2 "\<gamma>2\<epsilon> @ v" "\<gamma>2ss @ tl v_ss" q]
        show
          "(\<not>is_Ctr_Ext q \<longrightarrow> (\<exists>p' w'. (Ctr_Loc p', w', q) \<in> LTS_\<epsilon>.transition_star_\<epsilon> A \<and> (p', w') \<Rightarrow>\<^sup>* (p2, LTS_\<epsilon>.remove_\<epsilon> (\<gamma>2\<epsilon> @ v)))) \<and>
           (is_Ctr_Ext q \<longrightarrow> (the_Ext_Ctr_Loc q, [the_Ext_Label q]) \<Rightarrow>\<^sup>* (p2, LTS_\<epsilon>.remove_\<epsilon> (\<gamma>2\<epsilon> @ v)))"
          using \<open>j = count (transitions_of' (Ctr_Loc p2, \<gamma>2\<epsilon> @ v, \<gamma>2ss @ tl v_ss, q)) t\<close> by fastforce
      qed

      show ?thesis
      proof (cases "is_Ctr_Loc q \<or> is_State q")
        case True
        have "(\<exists>p' w'. (Ctr_Loc p', w', q) \<in> LTS_\<epsilon>.transition_star_\<epsilon> A \<and> (p', w') \<Rightarrow>\<^sup>* (p2, LTS_\<epsilon>.remove_\<epsilon> (\<gamma>2\<epsilon> @ v)))"
          using True \<open>(\<not>is_Ctr_Ext q \<longrightarrow> (\<exists>p' w'. (Ctr_Loc p', w', q) \<in> LTS_\<epsilon>.transition_star_\<epsilon> A \<and> (p', w') \<Rightarrow>\<^sup>* (p2, LTS_\<epsilon>.remove_\<epsilon> (\<gamma>2\<epsilon> @ v)))) \<and> (is_Ctr_Ext q \<longrightarrow> (the_Ext_Ctr_Loc q, [the_Ext_Label q]) \<Rightarrow>\<^sup>* (p2, LTS_\<epsilon>.remove_\<epsilon> (\<gamma>2\<epsilon> @ v)))\<close> by fastforce
        then obtain p' w' where "(Ctr_Loc p', w', q) \<in> LTS_\<epsilon>.transition_star_\<epsilon> A \<and> (p', w') \<Rightarrow>\<^sup>* (p2, LTS_\<epsilon>.remove_\<epsilon> (\<gamma>2\<epsilon> @ v))"
          by auto
        then have "(p', w') \<Rightarrow>\<^sup>* (p2, LTS_\<epsilon>.remove_\<epsilon> (\<gamma>2\<epsilon> @ v))"
          by auto
        have "(p2, LTS_\<epsilon>.remove_\<epsilon> (\<gamma>2\<epsilon> @ v)) \<Rightarrow>\<^sup>* (p1, \<gamma>1#\<gamma>''#LTS_\<epsilon>.remove_\<epsilon> v)"
        proof -
          have "\<gamma>2 #(LTS_\<epsilon>.remove_\<epsilon> v) = LTS_\<epsilon>.remove_\<epsilon> (\<gamma>2\<epsilon> @ v)"
            using XI_1
            by (metis LTS_\<epsilon>.\<epsilon>_exp_def LTS_\<epsilon>.remove_\<epsilon>_append_dist LTS_\<epsilon>.remove_\<epsilon>_def append_Cons self_append_conv2) 
          moreover
          from XIII have "(p2, \<gamma>2 #(LTS_\<epsilon>.remove_\<epsilon> v)) \<Rightarrow>\<^sup>* (p1, \<gamma>1#\<gamma>''#LTS_\<epsilon>.remove_\<epsilon> v)"
            by (metis PDS.transition_rel.intros append_Cons append_Nil op_labels.simps(3) r_into_rtranclp step_relp_def)
          ultimately
          show "(p2, LTS_\<epsilon>.remove_\<epsilon> (\<gamma>2\<epsilon> @ v)) \<Rightarrow>\<^sup>* (p1, \<gamma>1#\<gamma>''#LTS_\<epsilon>.remove_\<epsilon> v)"
            by auto
        qed
        have "(p1, \<gamma>1#\<gamma>''#LTS_\<epsilon>.remove_\<epsilon> v) \<Rightarrow>\<^sup>* (p, (LTS_\<epsilon>.remove_\<epsilon> u) @ (\<gamma>''#LTS_\<epsilon>.remove_\<epsilon> v))"
          by (metis \<open>(p1, [\<gamma>1]) \<Rightarrow>\<^sup>* (p, LTS_\<epsilon>.remove_\<epsilon> u)\<close> append_Cons append_Nil step_relp_append)
        have "(p, (LTS_\<epsilon>.remove_\<epsilon> u) @ (\<gamma>''#LTS_\<epsilon>.remove_\<epsilon> v)) = (p, LTS_\<epsilon>.remove_\<epsilon> w)"
          by (metis (no_types, lifting) Cons_eq_append_conv LTS_\<epsilon>.ffffffff LTS_\<epsilon>.remove_\<epsilon>_append_dist \<open>w = u @ [Some \<gamma>''] @ v\<close> hd_Cons_tl list.inject list.sel(1) list.simps(3) self_append_conv2)
          
        show ?thesis
          using True \<open>(p, LTS_\<epsilon>.remove_\<epsilon> u @ \<gamma>'' # LTS_\<epsilon>.remove_\<epsilon> v) = (p, LTS_\<epsilon>.remove_\<epsilon> w)\<close> \<open>(p1, \<gamma>1 # \<gamma>'' # LTS_\<epsilon>.remove_\<epsilon> v) \<Rightarrow>\<^sup>* (p, LTS_\<epsilon>.remove_\<epsilon> u @ \<gamma>'' # LTS_\<epsilon>.remove_\<epsilon> v)\<close> \<open>(p2, LTS_\<epsilon>.remove_\<epsilon> (\<gamma>2\<epsilon> @ v)) \<Rightarrow>\<^sup>* (p1, \<gamma>1 # \<gamma>'' # LTS_\<epsilon>.remove_\<epsilon> v)\<close> \<open>\<exists>p' w'. (Ctr_Loc p', w', q) \<in> LTS_\<epsilon>.transition_star_\<epsilon> A \<and> (p', w') \<Rightarrow>\<^sup>* (p2, LTS_\<epsilon>.remove_\<epsilon> (\<gamma>2\<epsilon> @ v))\<close> by fastforce
      next
        case False
        then have "(the_Ext_Ctr_Loc q, [the_Ext_Label q]) \<Rightarrow>\<^sup>* (p2, LTS_\<epsilon>.remove_\<epsilon> (\<gamma>2\<epsilon> @ v))"
          using inddd state.exhaust_disc
          by blast
        have "(p2, LTS_\<epsilon>.remove_\<epsilon> (\<gamma>2\<epsilon> @ v))  \<Rightarrow>\<^sup>* (p1, \<gamma>1 # \<gamma>'' # LTS_\<epsilon>.remove_\<epsilon> v)"
          by (metis (mono_tags, hide_lams) LTS_\<epsilon>.\<epsilon>_exp_def LTS_\<epsilon>.remove_\<epsilon>_append_dist LTS_\<epsilon>.remove_\<epsilon>_def XIII XI_1 append_Cons append_Nil op_labels.simps(3) r_into_rtranclp step_relp_def2)
          
        have "(p1, \<gamma>1 # \<gamma>'' # LTS_\<epsilon>.remove_\<epsilon> v) \<Rightarrow>\<^sup>* (p, LTS_\<epsilon>.remove_\<epsilon> u @ \<gamma>'' # LTS_\<epsilon>.remove_\<epsilon> v)"
          by (metis \<open>(p1, [\<gamma>1]) \<Rightarrow>\<^sup>* (p, LTS_\<epsilon>.remove_\<epsilon> u)\<close> append_Cons append_Nil step_relp_append)
          
        have "(p, LTS_\<epsilon>.remove_\<epsilon> u @ \<gamma>'' # LTS_\<epsilon>.remove_\<epsilon> v) = (p, LTS_\<epsilon>.remove_\<epsilon> w)"
          by (metis LTS_\<epsilon>.ffffffff LTS_\<epsilon>.remove_\<epsilon>_append_dist append_Cons append_Nil bbb hd_Cons_tl list.distinct(1) list.inject)
          
        show ?thesis
          using False \<open>(p, LTS_\<epsilon>.remove_\<epsilon> u @ \<gamma>'' # LTS_\<epsilon>.remove_\<epsilon> v) = (p, LTS_\<epsilon>.remove_\<epsilon> w)\<close> \<open>(p1, \<gamma>1 # \<gamma>'' # LTS_\<epsilon>.remove_\<epsilon> v) \<Rightarrow>\<^sup>* (p, LTS_\<epsilon>.remove_\<epsilon> u @ \<gamma>'' # LTS_\<epsilon>.remove_\<epsilon> v)\<close> \<open>(p2, LTS_\<epsilon>.remove_\<epsilon> (\<gamma>2\<epsilon> @ v)) \<Rightarrow>\<^sup>* (p1, \<gamma>1 # \<gamma>'' # LTS_\<epsilon>.remove_\<epsilon> v)\<close> \<open>(the_Ext_Ctr_Loc q, [the_Ext_Label q]) \<Rightarrow>\<^sup>* (p2, LTS_\<epsilon>.remove_\<epsilon> (\<gamma>2\<epsilon> @ v))\<close>
          by (metis (no_types, lifting) inddd rtranclp_trans) 

      qed
    qed
  qed
qed

lemma lemma_3_4'':
  assumes "post_star_rules\<^sup>*\<^sup>* A A'"
  assumes "\<nexists>q \<gamma> q'. (q, \<gamma>, Ctr_Loc q') \<in> A"
  assumes "\<forall>a b c. (a, b, c) \<in> A \<longrightarrow> a \<notin> New_Aut_states \<and> c \<notin> New_Aut_states"
  assumes "(Ctr_Loc p, w, q) \<in> LTS.transition_star A'"
  shows "(\<not>is_Ctr_Ext q \<longrightarrow> (\<exists>p' w'. (Ctr_Loc p', w', q) \<in> LTS_\<epsilon>.transition_star_\<epsilon> A \<and> (p',w') \<Rightarrow>\<^sup>* (p, LTS_\<epsilon>.remove_\<epsilon> w))) \<and>
         (is_Ctr_Ext q \<longrightarrow> (the_Ext_Ctr_Loc q, [the_Ext_Label q]) \<Rightarrow>\<^sup>* (p, LTS_\<epsilon>.remove_\<epsilon> w))"
  using lemma_3_4' assms by (metis LTS.transition_star_transition_star_states) 

lemma lemma_3_4:
  assumes "saturation post_star_rules A A'"
  assumes "\<nexists>q \<gamma> q'. (q, \<gamma>, Ctr_Loc q') \<in> A"
  assumes "\<forall>a b c. (a, b, c) \<in> A \<longrightarrow> a \<notin> New_Aut_states \<and> c \<notin> New_Aut_states"
  assumes "(Ctr_Loc p, w, q) \<in> LTS.transition_star A'"
  shows "(\<not>is_Ctr_Ext q \<longrightarrow> (\<exists>p' w'. (Ctr_Loc p', w', q) \<in> LTS_\<epsilon>.transition_star_\<epsilon> A \<and> (p',w') \<Rightarrow>\<^sup>* (p, LTS_\<epsilon>.remove_\<epsilon> w))) \<and>
         (is_Ctr_Ext q \<longrightarrow> (the_Ext_Ctr_Loc q, [the_Ext_Label q]) \<Rightarrow>\<^sup>* (p, LTS_\<epsilon>.remove_\<epsilon> w))"
  using lemma_3_4'' assms saturation_def by metis 


theorem theorem_3_3:
  assumes "saturation post_star_rules A A'"
  assumes "\<nexists>q \<gamma> q'. (q, \<gamma>, Ctr_Loc q') \<in> A"
  assumes "\<forall>a b c. (a, b, c) \<in> A \<longrightarrow> a \<notin> New_Aut_states \<and> c \<notin> New_Aut_states"
  shows "{c. accepts_\<epsilon> A' c} = post_star (language_\<epsilon> A)"
proof (rule; rule)
  fix c :: "('ctr_loc, 'label) conf"
  define p where "p = fst c"
  define w where "w = snd c"
  assume "c \<in> post_star (language_\<epsilon> A)"
  then obtain p' w' where "(p', w') \<Rightarrow>\<^sup>* (p, w) \<and> (p', w') \<in> language_\<epsilon> A"
    by (smt (verit, ccfv_SIG) LTS.post_star_def mem_Collect_eq p_def prod.collapse w_def)
  then have "accepts_\<epsilon> A' (p, w)"
    using lemma_3_3[of p' w' p w A A'] assms(1) by auto 
  then have "accepts_\<epsilon> A' c"
    unfolding p_def w_def by auto
  then show "c \<in> {c. accepts_\<epsilon> A' c}"
    by auto
next
  fix c :: "('ctr_loc, 'label) conf"
  define p where "p = fst c"
  define w where "w = snd c"
  assume "c \<in>  {c. accepts_\<epsilon> A' c}"
  then have "accepts_\<epsilon> A' (p,w)"
    unfolding p_def w_def by auto
  then obtain q where q_p: "q\<in>F_locs" "(Ctr_Loc p, w, q) \<in> LTS_\<epsilon>.transition_star_\<epsilon> A'" 
    unfolding accepts_\<epsilon>_def by auto
  then obtain w' where w'_def: "LTS_\<epsilon>.\<epsilon>_exp w' w \<and> (Ctr_Loc p, w', q) \<in> LTS.transition_star A'"
    by (meson LTS_\<epsilon>.epsilon_lemma3)
  then have ttt: "(Ctr_Loc p, w', q) \<in> LTS.transition_star A'"
    by auto
  have "\<not> is_Ctr_Ext q"
    using q_p(2) sorry
  then obtain p' w'a where "(Ctr_Loc p', w'a, q) \<in> LTS_\<epsilon>.transition_star_\<epsilon> A \<and> (p', w'a) \<Rightarrow>\<^sup>* (p, LTS_\<epsilon>.remove_\<epsilon> w')"
    using lemma_3_4[OF assms(1) assms(2) assms(3) ttt] by auto
  then have "(Ctr_Loc p', w'a, q) \<in> LTS_\<epsilon>.transition_star_\<epsilon> A \<and> (p', w'a) \<Rightarrow>\<^sup>* (p, w)"
    using w'_def by (metis LTS_\<epsilon>.\<epsilon>_exp_def LTS_\<epsilon>.remove_\<epsilon>_def \<open>LTS_\<epsilon>.\<epsilon>_exp w' w \<and> (Ctr_Loc p, w', q) \<in> LTS.transition_star A'\<close>)
  then have "(p,w) \<in> post_star (language_\<epsilon> A)"
    using \<open>q \<in> F_locs\<close> unfolding LTS.post_star_def accepts_\<epsilon>_def language_\<epsilon>_def by fastforce
  then show "c \<in> post_star (language_\<epsilon> A)"
    unfolding p_def w_def by auto
qed






end


