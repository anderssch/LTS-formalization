theory PDS imports "LTS" "HOL-Library.While_Combinator" begin



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


section \<open>PDS with P automata\<close>

type_synonym ('ctr_loc, 'label) sat_rule = "('ctr_loc, 'label) transition set \<Rightarrow> ('ctr_loc, 'label) transition set \<Rightarrow> bool"

datatype ('ctr_loc, 'noninitial, 'label) state =
  is_Initial: Initial (the_Ctr_Loc: 'ctr_loc) (* p \<in> P *)
  | is_Noninitial: Noninitial (the_St: 'noninitial) (* q \<in> Q \<and> q \<notin> P *)
  | is_New_Noninitial: New_Noninitial (the_New_Ctr_Loc: 'ctr_loc) (the_New_Label: 'label) (* q\<^sub>p\<^sub>\<gamma> *)

lemma finite_ctr_locs:
  assumes "finite (UNIV :: 'ctr_loc set)"
  assumes "finite (UNIV :: 'noninitial set)"
  assumes "finite (UNIV :: 'label set)"
  shows "finite (UNIV :: ('ctr_loc, 'noninitial, 'label) state set)"
proof -
  define New_Aut_State' :: "('ctr_loc * 'label) \<Rightarrow> ('ctr_loc, 'noninitial, 'label) state" where 
    "New_Aut_State' == \<lambda>(c :: 'ctr_loc, l:: 'label). New_Noninitial c l"
  define Ctr_Loc' :: "'ctr_loc \<Rightarrow> ('ctr_loc, 'noninitial, 'label) state" where
    "Ctr_Loc' = Initial"
  define Aut_State' :: "'noninitial \<Rightarrow> ('ctr_loc, 'noninitial, 'label) state" where
    "Aut_State' = Noninitial"

  have split: "UNIV = (Ctr_Loc' ` UNIV) \<union> (Aut_State' ` UNIV) \<union> (New_Aut_State' ` (UNIV :: (('ctr_loc * 'label) set)))"
    unfolding Ctr_Loc'_def Aut_State'_def
  proof (rule; rule; rule; rule)
    fix x :: "('ctr_loc, 'noninitial, 'label) state"
    assume "x \<in> UNIV"
    moreover
    assume "x \<notin> range New_Aut_State'"
    moreover
    assume "x \<notin> range Noninitial"
    ultimately
    show "x \<in> range Initial"
      by (metis New_Aut_State'_def prod.simps(2) range_eqI state.exhaust)
  qed

  have "finite (Ctr_Loc' ` (UNIV:: 'ctr_loc set))"
    using assms by auto
  moreover
  have "finite (Aut_State' ` (UNIV:: 'noninitial set))"
    using assms by auto
  moreover
  have "finite (UNIV :: (('ctr_loc * 'label) set))"
    using assms by (simp add: finite_Prod_UNIV)
  then have "finite (New_Aut_State' ` (UNIV :: (('ctr_loc * 'label) set)))"
    by auto
  ultimately
  show "finite (UNIV :: ('ctr_loc, 'noninitial, 'label) state set)"
    unfolding split by auto
qed

instantiation state :: (finite, finite, finite) finite begin

instance by standard (simp add: finite_ctr_locs)

end


locale PDS_with_P_automata = PDS \<Delta>
  for \<Delta> :: "('ctr_loc::enum, 'label::finite) rule set"
    +
  fixes final_initials :: "('ctr_loc::enum) set"
  fixes final_noninitials :: "('noninitial::finite) set"
begin

(* Corresponds to Schwoon's F *)
definition finals :: "('ctr_loc, 'noninitial::finite, 'label) state set" where
  "finals = Initial ` final_initials \<union> Noninitial ` final_noninitials"

lemma F_not_Ext: "\<not>(\<exists>f\<in>finals. is_New_Noninitial f)"
  using finals_def by fastforce

(* Corresponds to Schwoon's P *)
definition initials :: "('ctr_loc, 'noninitial, 'label) state set" where 
  "initials = {q. is_Initial q}"

lemma initials_code[code]: "initials = set (map Initial Enum.enum)"
  by (auto simp: initials_def is_Initial_def simp flip: UNIV_enum)

definition Old_Aut_states :: "('ctr_loc, 'noninitial, 'label) state set" where
  "Old_Aut_states = {q. is_Noninitial q}"

definition New_Aut_states :: "('ctr_loc, 'noninitial, 'label) state set" where
  "New_Aut_states = {q. is_New_Noninitial q}"

sublocale LTS transition_rel .
notation step_relp (infix "\<Rightarrow>" 80)
notation step_starp (infix "\<Rightarrow>\<^sup>*" 80)

definition accepts :: "(('ctr_loc, 'noninitial, 'label) state, 'label) transition set \<Rightarrow> ('ctr_loc, 'label) conf \<Rightarrow> bool" where
  "accepts ts \<equiv> \<lambda>(p,w). (\<exists>q \<in> finals. (Initial p,w,q) \<in> LTS.transition_star ts)"

lemma accepts_accepts_aut: "accepts ts (p, w) \<longleftrightarrow> P_Automaton.accepts_aut ts finals initials (Initial p) w"
  unfolding accepts_def P_Automaton.accepts_aut_def initials_def by auto

definition accepts_\<epsilon> :: "(('ctr_loc, 'noninitial, 'label) state, 'label option) transition set \<Rightarrow> ('ctr_loc, 'label) conf \<Rightarrow> bool" where
  "accepts_\<epsilon> ts \<equiv> \<lambda>(p,w). (\<exists>q \<in> finals. (Initial p,w,q) \<in> LTS_\<epsilon>.transition_star_\<epsilon> ts)"

(* TODO: Make a lemma similar to accepts_accepts_aut but for the epsilon versions. *)

abbreviation \<epsilon> :: "'label option" where
  "\<epsilon> == None"

lemma accepts_mono[mono]: "mono accepts" (* Hmm.. what does this actually mean? *)
proof (rule, rule)
  fix c :: "('ctr_loc, 'label) conf"
  fix ts ts' :: "(('ctr_loc, 'noninitial, 'label) state, 'label) transition set"
  assume accepts_xa: "accepts ts c"
  assume tsts': "ts \<subseteq> ts'"
  obtain p l where pl_p: "c = (p,l)"
    by (cases c)
  obtain q where q_p:  "q \<in> finals \<and> (Initial p, l, q) \<in> LTS.transition_star ts"
    using accepts_xa unfolding pl_p accepts_def by auto
  then have "(Initial p, l, q) \<in> LTS.transition_star ts'"
    using tsts' LTS_transition_star_mono monoD by blast 
  then have "accepts ts' (p,l)"
    unfolding accepts_def using q_p by auto
  then show "accepts ts' c"
    unfolding pl_p .
qed

lemma accepts_cons: "(Initial p, \<gamma>, Initial p') \<in> ts \<Longrightarrow> accepts ts (p', w) \<Longrightarrow> accepts ts (p, \<gamma> # w)"
  using LTS.transition_star.transition_star_step accepts_def by fastforce 

definition language :: "(('ctr_loc, 'noninitial, 'label) state, 'label) transition set \<Rightarrow> ('ctr_loc, 'label) conf set" where
  "language ts = {c. accepts ts c}"

lemma language_language_aut: "language ts = (\<lambda>(s,w). (the_Ctr_Loc s, w)) ` (P_Automaton.language_aut ts finals initials)"
  unfolding language_def P_Automaton.language_aut_def
  by (auto simp: initials_def accepts_def P_Automaton.accepts_aut_def image_iff intro!: exI[of _ "Initial _"])

lemma language_aut_language: "P_Automaton.language_aut ts finals initials = apfst Initial ` language ts"
  unfolding language_language_aut
  by (auto 0 3 simp: P_Automaton.language_aut_def P_Automaton.accepts_aut_def initials_def image_iff)

definition language_\<epsilon> :: "(('ctr_loc, 'noninitial, 'label) state, 'label option) transition set \<Rightarrow> ('ctr_loc, 'label) conf set" where
  "language_\<epsilon> ts = {c. accepts_\<epsilon> ts c}"


subsection \<open>Saturations\<close>

(* We use 'l for supporting both 'label and 'label option. We use 'c for supporting both 'ctr_loc and ('ctr_loc, 'label) ctr_loc *)
definition saturated :: "('c, 'l) sat_rule \<Rightarrow> ('c, 'l) transition set \<Rightarrow> bool" where
  "saturated rule ts \<longleftrightarrow> (\<nexists>ts'. rule ts ts')"

definition saturation :: "('c, 'l) sat_rule \<Rightarrow> ('c, 'l) transition set \<Rightarrow> ('c, 'l) transition set \<Rightarrow> bool" where
  "saturation rule ts ts' \<longleftrightarrow> rule\<^sup>*\<^sup>* ts ts' \<and> saturated rule ts'"

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


subsection \<open>Saturation rules\<close>

inductive pre_star_rule :: "(('ctr_loc, 'noninitial, 'label) state, 'label) transition set \<Rightarrow> (('ctr_loc, 'noninitial, 'label) state, 'label) transition set \<Rightarrow> bool" where 
  add_trans: "(p, \<gamma>) \<hookrightarrow> (p', w) \<Longrightarrow> (Initial p', op_labels w, q) \<in> LTS.transition_star ts \<Longrightarrow>
    (Initial p, \<gamma>, q) \<notin> ts \<Longrightarrow> pre_star_rule ts (ts \<union> {(Initial p, \<gamma>, q)})"

definition pre_star_step :: "(('ctr_loc, 'noninitial, 'label) state, 'label) transition set \<Rightarrow> (('ctr_loc, 'noninitial, 'label) state, 'label) transition set" where
  "pre_star_step ts =
    (\<Union>((p, \<gamma>), (p', w)) \<in> \<Delta>. \<Union>q \<in> LTS.transition_star_exec ts (Initial p') (op_labels w). {(Initial p, \<gamma>, q)})"

lemma pre_star_step_mono: "mono pre_star_step"
  unfolding pre_star_step_def
  by (auto simp: mono_def LTS.transition_star_code[symmetric] elim!: bexI[rotated]
    LTS_transition_star_mono[THEN monoD, THEN subsetD])

lemma pre_star_rule_pre_star_step:
  assumes "X \<subseteq> pre_star_step ts"
  shows "pre_star_rule\<^sup>*\<^sup>* ts (ts \<union> X)"
proof -
  have "finite X"
    by simp
  from this assms show ?thesis
  proof (induct X arbitrary: ts rule: finite_induct)
    case (insert x F)
    then obtain p \<gamma> p' w q where *: "(p, \<gamma>) \<hookrightarrow> (p', w)" 
      "(Initial p', op_labels w, q) \<in> LTS.transition_star ts" and x:
      "x = (Initial p, \<gamma>, q)"
      by (auto simp: pre_star_step_def is_rule_def LTS.transition_star_code)
    with insert show ?case
    proof (cases "(Initial p, \<gamma>, q) \<in> ts")
      case False
      with insert(1,2,4) x show ?thesis
        by (intro converse_rtranclp_into_rtranclp[of pre_star_rule, OF add_trans[OF * False]])
          (auto intro!: insert(3)[of "insert x ts", simplified x Un_insert_left]
            intro: pre_star_step_mono[THEN monoD, THEN set_mp, of ts])
    qed (simp add: insert_absorb)
  qed simp
qed

lemma pre_star_rule_pre_star_steps: "pre_star_rule\<^sup>*\<^sup>* ts (((\<lambda>s. s \<union> pre_star_step s) ^^ k) ts)"
  by (induct k) (auto elim!: rtranclp_trans intro: pre_star_rule_pre_star_step)

definition "pre_star_loop = while_option (\<lambda>s. s \<union> pre_star_step s \<noteq> s) (\<lambda>s. s \<union> pre_star_step s)"
definition "pre_star_exec = the o pre_star_loop"
definition "pre_star_exec_check A = (if initials \<subseteq> LTS.sources A then pre_star_loop A else None)"

definition "accept_pre_star_exec_check A c = (if initials \<subseteq> LTS.sources A then Some (accepts (pre_star_exec A) c) else None)"

lemma while_option_finite_subset_Some: fixes C :: "'a set"
  assumes "mono f" and "!!X. X \<subseteq> C \<Longrightarrow> f X \<subseteq> C" and "finite C" and X: "X \<subseteq> C" "X \<subseteq> f X"
  shows "\<exists>P. while_option (\<lambda>A. f A \<noteq> A) f X = Some P"
proof(rule measure_while_option_Some[where
    f= "%A::'a set. card C - card A" and P= "%A. A \<subseteq> C \<and> A \<subseteq> f A" and s= X])
  fix A assume A: "A \<subseteq> C \<and> A \<subseteq> f A" "f A \<noteq> A"
  show "(f A \<subseteq> C \<and> f A \<subseteq> f (f A)) \<and> card C - card (f A) < card C - card A"
    (is "?L \<and> ?R")
  proof
    show ?L by(metis A(1) assms(2) monoD[OF \<open>mono f\<close>])
    show ?R by (metis A assms(2,3) card_seteq diff_less_mono2 equalityI linorder_le_less_linear rev_finite_subset)
  qed
qed (simp add: X)

lemma pre_star_exec_terminates: "\<exists>t. pre_star_loop s = Some t"
  unfolding pre_star_loop_def
  by (rule while_option_finite_subset_Some[where C=UNIV])
    (auto simp: mono_def dest: pre_star_step_mono[THEN monoD])

lemma pre_star_exec_code[code]:
  "pre_star_exec s = (let s' = pre_star_step s in if s' \<subseteq> s then s else pre_star_exec (s \<union> s'))"
  unfolding pre_star_exec_def pre_star_loop_def o_apply
  by (subst while_option_unfold)(auto simp: Let_def)

lemma saturation_pre_star_exec: "saturation pre_star_rule ts (pre_star_exec ts)"
proof -
  from pre_star_exec_terminates obtain t where t: "pre_star_loop ts = Some t"
    by blast
  obtain k where k: "t = ((\<lambda>s. s \<union> pre_star_step s) ^^ k) ts" and le: "pre_star_step t \<subseteq> t"
    using while_option_stop2[OF t[unfolded pre_star_loop_def]] by auto
  have "(\<Union>{us. pre_star_rule t us}) - t \<subseteq> pre_star_step t"
    by (auto simp: pre_star_step_def LTS.transition_star_code[symmetric] prod.splits is_rule_def
      pre_star_rule.simps)
  from subset_trans[OF this le] show ?thesis
    unfolding saturation_def saturated_def pre_star_exec_def o_apply k t
    by (auto 9 0 simp: pre_star_rule_pre_star_steps subset_eq pre_star_rule.simps)
qed

inductive post_star_rules :: "(('ctr_loc, 'noninitial, 'label) state, 'label option) transition set \<Rightarrow> (('ctr_loc, 'noninitial, 'label) state, 'label option) transition set \<Rightarrow> bool" where
  add_trans_pop: "(p, \<gamma>) \<hookrightarrow> (p', pop) \<Longrightarrow> (Initial p, [\<gamma>], q) \<in> LTS_\<epsilon>.transition_star_\<epsilon> ts \<Longrightarrow> (Initial p', \<epsilon>, q) \<notin> ts \<Longrightarrow> post_star_rules ts (ts \<union> {(Initial p', \<epsilon>, q)})"
| add_trans_swap: "(p, \<gamma>) \<hookrightarrow> (p', swap \<gamma>') \<Longrightarrow> (Initial p, [\<gamma>], q) \<in> LTS_\<epsilon>.transition_star_\<epsilon> ts \<Longrightarrow> (Initial p', Some \<gamma>', q) \<notin> ts \<Longrightarrow> post_star_rules ts (ts \<union> {(Initial p', Some \<gamma>', q)})"
| add_trans_push_1: "(p, \<gamma>) \<hookrightarrow> (p', push \<gamma>' \<gamma>'') \<Longrightarrow> (Initial p, [\<gamma>], q) \<in> LTS_\<epsilon>.transition_star_\<epsilon> ts \<Longrightarrow> (Initial p', Some \<gamma>', New_Noninitial p' \<gamma>') \<notin> ts \<Longrightarrow> post_star_rules ts (ts \<union> {(Initial p', Some \<gamma>', New_Noninitial p' \<gamma>')})"
| add_trans_push_2: "(p, \<gamma>) \<hookrightarrow> (p', push \<gamma>' \<gamma>'') \<Longrightarrow> (Initial p, [\<gamma>], q) \<in> LTS_\<epsilon>.transition_star_\<epsilon> ts \<Longrightarrow> (New_Noninitial p' \<gamma>', Some \<gamma>'', q) \<notin> ts \<Longrightarrow> (Initial p', Some \<gamma>', New_Noninitial p' \<gamma>') \<in> ts \<Longrightarrow> post_star_rules ts (ts \<union> {(New_Noninitial p' \<gamma>', Some \<gamma>'', q)})"

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


lemma pre_star_saturation_termination: 
  (* Maybe lazy lists are better? *)
  "\<not>(\<exists>tts. (\<forall>i :: nat. pre_star_rule (tts i) (tts (Suc i))))"
  using no_infinite pre_star_rule_card_Suc by blast 

lemma post_star_saturation_termination: 
  (* Maybe lazy lists are better? *)
  "\<not>(\<exists>tts. (\<forall>i :: nat. post_star_rules (tts i) (tts (Suc i))))"
  using no_infinite post_star_rules_card_Suc by blast

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


subsection \<open>Pre* lemmas\<close>

lemma initials_sources_iff_Ctr_Loc_sources:
  "initials \<subseteq> LTS.sources A \<longleftrightarrow> (\<nexists>q \<gamma> q'. (q, \<gamma>, Initial q') \<in> A)"
proof 
  assume "initials \<subseteq> LTS.sources A"
  then show "\<nexists>q \<gamma> q'. (q, \<gamma>, Initial q') \<in> A"
    by (simp add: Collect_mono_iff LTS.sources_def initials_def)
next
  assume "\<nexists>q \<gamma> q'. (q, \<gamma>, Initial q') \<in> A"
  show "initials \<subseteq> LTS.sources A"
    by (metis LTS.sources_def2 initials_def \<open>\<nexists>q \<gamma> q'. (q, \<gamma>, Initial q') \<in> A\<close> mem_Collect_eq state.collapse(1) subsetI)
qed

lemma lemma_3_1:
  assumes "p'w \<Rightarrow>\<^sup>* pv"
  assumes "pv \<in> language A"
  assumes "saturation pre_star_rule A A'"
  shows "accepts A' p'w"
  using assms
proof (induct rule: converse_rtranclp_induct)
  case base
  define p where "p = fst pv"
  define v where "v = snd pv"
  from base have "\<exists>q \<in> finals. (Initial p, v, q) \<in> LTS.transition_star A'"
    unfolding language_def p_def v_def using pre_star_lim'_incr_transition_star accepts_def by fastforce 
  then show ?case
    unfolding accepts_def p_def v_def by auto
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
    using step by auto
  then obtain q where q_p: "q \<in> finals \<and> (Initial p'', u, q) \<in> LTS.transition_star A'"
    unfolding accepts_def by auto
  have "\<exists>\<gamma> w1 u1. w=\<gamma>#w1 \<and> u=op_labels u1@w1 \<and> (p', \<gamma>) \<hookrightarrow> (p'', u1)"
    using p''u_def p'w_def step.hyps(1) step_relp_def2 by auto
  then obtain \<gamma> w1 u1 where \<gamma>_w1_u1_p: "w=\<gamma>#w1 \<and> u=op_labels u1@w1 \<and> (p', \<gamma>) \<hookrightarrow> (p'', u1)"
    by blast

  then have "\<exists>q1. (Initial p'', op_labels u1, q1) \<in> LTS.transition_star A' \<and> (q1, w1, q) \<in> LTS.transition_star A'"
    using q_p LTS.transition_star_split by auto

  then obtain q1 where q1_p: "(Initial p'', op_labels u1, q1) \<in> LTS.transition_star A' \<and> (q1, w1, q) \<in> LTS.transition_star A'"
    by auto

  then have in_A': "(Initial p', \<gamma>, q1) \<in> A'"
    using \<gamma>_w1_u1_p add_trans[of p' \<gamma> p'' u1 q1 A'] saturated_def saturation_def step.prems by metis

  then have "(Initial p', \<gamma>#w1, q) \<in> LTS.transition_star A'"
    using LTS.transition_star.transition_star_step q1_p by meson
  then have t_in_A': "(Initial p', w, q) \<in> LTS.transition_star A'"
    using \<gamma>_w1_u1_p by blast

  from q_p t_in_A' have "q \<in> finals \<and> (Initial p', w, q) \<in> LTS.transition_star A'"
    by auto
  then show ?case
    unfolding accepts_def p'w_def by auto 
qed

lemma word_into_init_empty_states:
  fixes A :: "(('ctr_loc, 'noninitial, 'label) state, 'label) transition set"
  assumes "(p, w, ss, Initial q) \<in> LTS.transition_star_states A"
  assumes "initials \<subseteq> LTS.sources A"
  shows "w = [] \<and> p = Initial q \<and> ss=[p]"
proof -
  define q1 :: "('ctr_loc, 'noninitial, 'label) state" where 
    "q1 = Initial q"
  have q1_path: "(p, w, ss, q1) \<in> LTS.transition_star_states A"
    by (simp add: assms(1) q1_def)
  moreover
  have "q1 \<in> initials"
    by (simp add: initials_def q1_def)
  ultimately
  have "w = [] \<and> p = q1 \<and> ss=[p]"
  proof(induction rule: LTS.transition_star_states.induct[OF q1_path])
    case (1 p)
    then show ?case by auto
  next
    case (2 p \<gamma> q' w ss q)
    have "\<nexists>q \<gamma> q'. (q, \<gamma>, Initial q') \<in> A"
      using assms(2) unfolding initials_def LTS.sources_def by (simp add: Collect_mono_iff) 
    then show ?case
      using 2 assms(2) by (metis initials_def is_Initial_def mem_Collect_eq)
  qed
  then show ?thesis
    using q1_def by fastforce
qed

(* This corresponds to and slightly generalizes Schwoon's lemma 3.2(b) *)
lemma word_into_init_empty:
  fixes A :: "(('ctr_loc, 'noninitial, 'label) state, 'label) transition set"
  assumes "(p, w, Initial q) \<in> LTS.transition_star A"
  assumes "initials \<subseteq> LTS.sources A"
  shows "w = [] \<and> p = Initial q"
  using assms word_into_init_empty_states LTS.transition_star_transition_star_states by metis

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
  assumes "initials \<subseteq> LTS.sources A"
  assumes "pre_star_rule\<^sup>*\<^sup>* A A'"
  assumes "(Initial p, w, q) \<in> LTS.transition_star A'"
  shows "\<exists>p' w'. (Initial p', w', q) \<in> LTS.transition_star A \<and> (p, w) \<Rightarrow>\<^sup>* (p', w')"
  using assms(2) assms(3)
proof (induction arbitrary: p q w rule: rtranclp_induct)
  case base
  then have "(Initial p, w, q) \<in> LTS.transition_star A \<and> (p, w) \<Rightarrow>\<^sup>* (p, w)"
    by auto
  then show ?case
    by auto
next
  case (step Aiminus1 Ai)

  from step(2) obtain p1 \<gamma> p2 w2 q' where p1_\<gamma>_p2_w2_q'_p:
    "Ai = Aiminus1 \<union> {(Initial p1, \<gamma>, q')}"
    "(p1, \<gamma>) \<hookrightarrow> (p2, w2)"
    "(Initial p2, op_labels w2, q') \<in> LTS.transition_star Aiminus1"
    "(Initial p1, \<gamma>, q') \<notin> Aiminus1"
    by (meson pre_star_rule.cases)

  define t :: "(('ctr_loc, 'noninitial, 'label) state, 'label) transition"
    where "t = (Initial p1, \<gamma>, q')"

  obtain ss where ss_p: "(Initial p, w, ss, q) \<in> LTS.transition_star_states Ai"
    using step(4) LTS.transition_star_transition_star_states by metis

  define j where "j = count (transitions_of' (Initial p, w, ss, q)) t"

  from j_def ss_p show ?case
  proof (induction j arbitrary: p q w ss)
    case 0
    then have "(Initial p, w, q) \<in> LTS.transition_star Aiminus1"
      using count_zero_remove_transition_star_states_transition_star p1_\<gamma>_p2_w2_q'_p(1) t_def by metis
    then show ?case
      using step.IH by metis
  next
    case (Suc j')
    have "\<exists>u v u_ss v_ss.
            ss = u_ss@v_ss \<and> w = u@[\<gamma>]@v \<and>
            (Initial p,u,u_ss, Initial p1) \<in> LTS.transition_star_states Aiminus1 \<and>
            (Initial p1,[\<gamma>],q') \<in> LTS.transition_star Ai \<and>
            (q',v,v_ss,q) \<in> LTS.transition_star_states Ai \<and>
            (Initial p, w, ss, q) = ((Initial p, u, u_ss, Initial p1), \<gamma>) @@\<^sup>\<gamma> (q', v, v_ss, q)"
      using split_at_first_t[of "Initial p" w ss q Ai j' "Initial p1" \<gamma> q' Aiminus1]
      using Suc(2,3) t_def  p1_\<gamma>_p2_w2_q'_p(1,4) t_def by auto
    then obtain u v u_ss v_ss where u_v_u_ss_v_ss_p:
      "ss = u_ss@v_ss \<and> w = u@[\<gamma>]@v"
      "(Initial p,u,u_ss, Initial p1) \<in> LTS.transition_star_states Aiminus1"
      "(Initial p1,[\<gamma>],q') \<in> LTS.transition_star Ai"
      "(q',v,v_ss,q) \<in> LTS.transition_star_states Ai"
      "(Initial p, w, ss, q) = ((Initial p, u, u_ss, Initial p1), \<gamma>) @@\<^sup>\<gamma> (q', v, v_ss, q)"
      by blast
    from this(2) have "\<exists>p'' w''. (Initial p'', w'', Initial p1) \<in> LTS.transition_star A \<and> (p, u) \<Rightarrow>\<^sup>* (p'', w'')"
      using Suc(1)[of p u _ "Initial p1"] step.IH step.prems(1)
      by (meson LTS.transition_star_states_transition_star LTS.transition_star_transition_star_states) 
    from this this(1) have VIII: "(p, u) \<Rightarrow>\<^sup>* (p1, [])"
      using word_into_init_empty assms(1) by blast

    note IX = p1_\<gamma>_p2_w2_q'_p(2)
    note III = p1_\<gamma>_p2_w2_q'_p(3)
    from III have III_2: "\<exists>w2_ss. (Initial p2, op_labels w2, w2_ss, q') \<in> LTS.transition_star_states Aiminus1"
      using LTS.transition_star_transition_star_states[of "Initial p2" "op_labels w2" q' Aiminus1] by auto
    then obtain w2_ss where III_2: "(Initial p2, op_labels w2, w2_ss, q') \<in> LTS.transition_star_states Aiminus1"
      by blast

    from III have V: 
      "(Initial p2, op_labels w2, w2_ss, q') \<in> LTS.transition_star_states Aiminus1" 
      "(q', v, v_ss, q) \<in> LTS.transition_star_states Ai"
      using III_2 \<open>(q', v, v_ss, q) \<in> LTS.transition_star_states Ai\<close> by auto

    define w2v where "w2v = op_labels w2 @ v"
    define w2v_ss where "w2v_ss = w2_ss @ tl v_ss"

    from V(1) have "(Initial p2, op_labels w2, w2_ss, q') \<in> LTS.transition_star_states Ai"
      using transition_star_states_mono p1_\<gamma>_p2_w2_q'_p(1) using Un_iff subsetI by (metis (no_types))
    then have V_merged: "(Initial p2, w2v, w2v_ss, q) \<in> LTS.transition_star_states Ai"
      using V(2) unfolding w2v_def w2v_ss_def by (meson LTS.transition_star_states_append)

    have j'_count: "j' = count (transitions_of' (Initial p2, w2v, w2v_ss, q)) t"
    proof -
      define countts where
        "countts == \<lambda>x. count (transitions_of' x) t"

      have "countts (Initial p, w, ss, q) = Suc j' "
        using Suc.prems(1) countts_def by force
      moreover
      have "countts (Initial p, u, u_ss, Initial p1) = 0"
        using LTS.avoid_count_zero countts_def p1_\<gamma>_p2_w2_q'_p(4) t_def u_v_u_ss_v_ss_p(2) by fastforce
      moreover
      from u_v_u_ss_v_ss_p(5) have "countts (Initial p, w, ss, q) = countts (Initial p, u, u_ss, Initial p1) + 1 + countts (q', v, v_ss, q)"
        using count_combine_transition_star_states countts_def t_def u_v_u_ss_v_ss_p(2) u_v_u_ss_v_ss_p(4) by fastforce
      ultimately
      have "Suc j' = 0 + 1 + countts (q', v, v_ss, q)"
        by auto
      then have "j' = countts (q', v, v_ss, q)"
        by auto
      moreover
      have "countts (Initial p2, op_labels w2, w2_ss, q') = 0"
        using III_2 LTS.avoid_count_zero countts_def p1_\<gamma>_p2_w2_q'_p(4) t_def by fastforce
      moreover
      have "(Initial p2, w2v, w2v_ss, q) = (Initial p2, op_labels w2, w2_ss, q') @@\<acute> (q', v, v_ss, q)"
        using w2v_def w2v_ss_def by auto
      then have "countts (Initial p2, w2v, w2v_ss, q) = countts (Initial p2, op_labels w2, w2_ss, q') + countts (q', v, v_ss, q)"
        using \<open>(Initial p2, op_labels w2, w2_ss, q') \<in> LTS.transition_star_states Ai\<close> count_append_transition_star_states countts_def t_def u_v_u_ss_v_ss_p(4) by fastforce
      ultimately
      show ?thesis
        by (simp add: countts_def)
    qed

    have "\<exists>p' w'. (Initial p', w', q) \<in> LTS.transition_star A \<and> (p2, w2v) \<Rightarrow>\<^sup>* (p', w')"
      using Suc(1) using j'_count V_merged by auto
    then obtain p' w' where p'_w'_p: "(Initial p', w', q) \<in> LTS.transition_star A" "(p2, w2v) \<Rightarrow>\<^sup>* (p', w')"
      by blast

    note X = p'_w'_p(2)

    have "(p,w) = (p,u@[\<gamma>]@v)"
      using \<open>ss = u_ss @ v_ss \<and> w = u @ [\<gamma>] @ v\<close> by blast

    have "(p,u@[\<gamma>]@v) \<Rightarrow>\<^sup>* (p1,\<gamma>#v)"
      using VIII step_relp_append_empty by auto

    from X have "(p1,\<gamma>#v) \<Rightarrow> (p2, w2v)"
      by (metis IX LTS.step_relp_def transition_rel.intros w2v_def)

    from X have
      "(p2, w2v) \<Rightarrow>\<^sup>* (p', w')"
      by simp

    have "(p, w) \<Rightarrow>\<^sup>* (p', w')"
      using X \<open>(p, u @ [\<gamma>] @ v) \<Rightarrow>\<^sup>* (p1, \<gamma> # v)\<close> \<open>(p, w) = (p, u @ [\<gamma>] @ v)\<close> \<open>(p1, \<gamma> # v) \<Rightarrow> (p2, w2v)\<close> by auto

    then have "(Initial p', w', q) \<in> LTS.transition_star A \<and> (p, w) \<Rightarrow>\<^sup>* (p', w')"
      using p'_w'_p(1) by auto
    then show ?case
      by metis
  qed
qed 

lemma lemma_3_2_a:
  assumes "initials \<subseteq> LTS.sources A"
  assumes "saturation pre_star_rule A A'"
  assumes "(Initial p, w, q) \<in> LTS.transition_star A'"
  shows "\<exists>p' w'. (Initial p', w', q) \<in> LTS.transition_star A \<and> (p, w) \<Rightarrow>\<^sup>* (p', w')"
  using assms lemma_3_2_a' saturation_def by metis

lemmas lemma_3_2 = lemma_3_2_a word_into_init_empty

theorem theorem_3_2_on_the_fly:
  assumes "initials \<subseteq> LTS.sources A"
  assumes "pre_star_rule\<^sup>*\<^sup>* A A'"
  shows "{c. accepts A' c} \<subseteq> pre_star (language A)"
proof
  fix c :: "'ctr_loc \<times> 'label list"
  assume c_a: "c \<in> {w. accepts A' w}"
  define p where "p = fst c"
  define w where "w = snd c"
  from p_def w_def c_a have "accepts A' (p,w)"
    by auto
  then have "\<exists>q \<in> finals. (Initial p, w, q) \<in> LTS.transition_star A'"
    unfolding accepts_def by auto
  then obtain q where q_p: "q \<in> finals" "(Initial p, w, q) \<in> LTS.transition_star A'"
    by auto
  then have "\<exists>p' w'. (p,w) \<Rightarrow>\<^sup>* (p',w') \<and> (Initial p', w', q) \<in> LTS.transition_star A"
    using lemma_3_2_a' assms(1) assms(2) by metis
  then obtain p' w' where p'_w'_p: "(p,w) \<Rightarrow>\<^sup>* (p',w')" "(Initial p', w', q) \<in> LTS.transition_star A"
    by auto
  then have "(p', w') \<in> language A"
    unfolding language_def unfolding accepts_def using q_p(1) by auto
  then have "(p,w) \<in> pre_star (language A)"
    unfolding pre_star_def using p'_w'_p(1) by auto
  then show "c \<in> pre_star (language A)"
    unfolding p_def w_def by auto
qed

\<comment> \<open>Corresponds to Schwoon's theorem 3.2\<close>
theorem pre_star_rules_correct:
  assumes "initials \<subseteq> LTS.sources A"
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
  then have "\<exists>q \<in> finals. (Initial p, w, q) \<in> LTS.transition_star A'"
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
  then have "\<exists>q \<in> finals. (Initial p, w, q) \<in> LTS.transition_star A'"
    unfolding accepts_def by auto
  then obtain q where q_p: "q \<in> finals" "(Initial p, w, q) \<in> LTS.transition_star A'"
    by auto
  then have "\<exists>p' w'. (p,w) \<Rightarrow>\<^sup>* (p',w') \<and> (Initial p', w', q) \<in> LTS.transition_star A"
    using lemma_3_2_a assms(1) assms(2) by metis
  then obtain p' w' where p'_w'_p: "(p,w) \<Rightarrow>\<^sup>* (p',w')" "(Initial p', w', q) \<in> LTS.transition_star A"
    by auto
  then have "(p', w') \<in> language A"
    unfolding language_def unfolding accepts_def using q_p(1) by auto
  then have "(p,w) \<in> pre_star (language A)"
    unfolding pre_star_def using p'_w'_p(1) by auto
  then show "c \<in> pre_star (language A)"
    unfolding p_def w_def by auto
qed

\<comment> \<open>Corresponds to Schwoon's theorem 3.2\<close>
theorem pre_star_rules_language_correct:
  assumes "initials \<subseteq> LTS.sources A"
  assumes "saturation pre_star_rule A A'"
  shows "language A' = pre_star (language A)"
  using assms(1) assms(2) language_def pre_star_rules_correct by auto

theorem pre_star_exec_correct:
  assumes "initials \<subseteq> LTS.sources A"
  shows "{c. accepts (pre_star_exec A) c} = pre_star (language A)"
  using pre_star_rules_correct[of A "pre_star_exec A"] saturation_pre_star_exec[of A] using assms by auto

theorem pre_star_exec_language_correct:
  assumes "initials \<subseteq> LTS.sources A"
  shows "language (pre_star_exec A) = pre_star (language A)"
  using pre_star_rules_language_correct[of A "pre_star_exec A"] saturation_pre_star_exec[of A] using assms by auto

theorem pre_star_exec_check_correct:
  assumes "pre_star_exec_check A \<noteq> None"
  shows "{c. accepts (the (pre_star_exec_check A)) c} = pre_star (language A)"
  using pre_star_exec_correct assms unfolding pre_star_exec_check_def apply auto
  using pre_star_exec_def apply fastforce
  using pre_star_exec_def apply fastforce
   apply (metis option.discI subsetD)
  apply (metis option.discI subsetD)
  done

theorem pre_star_exec_check_language_correct:
  assumes "pre_star_exec_check A \<noteq> None"
  shows "language (the (pre_star_exec_check A)) = pre_star (language A)"
  using pre_star_exec_check_correct assms unfolding language_def by auto

theorem accept_pre_star_exec_correct_True:
  assumes "initials \<subseteq> LTS.sources A"
  assumes "accepts (pre_star_exec A) c"
  shows "c \<in> pre_star (language A)"
  using pre_star_exec_correct assms(1) assms(2) by blast

theorem accept_pre_star_exec_correct_False:
  assumes "initials \<subseteq> LTS.sources A"
  assumes "\<not>accepts (pre_star_exec A) c"
  shows "c \<notin> pre_star (language A)"
  using pre_star_exec_correct assms(1) assms(2) by blast

theorem accept_pre_star_exec_correct_Some_True:
  assumes "accept_pre_star_exec_check A c = Some True"
  shows "c \<in> pre_star (language A)"
proof -
  have "initials \<subseteq> LTS.sources A"
    using assms unfolding accept_pre_star_exec_check_def
    apply auto
    by (meson in_mono option.distinct(1)) 
  moreover
  have "accepts (pre_star_exec A) c"
    using assms
    using accept_pre_star_exec_check_def calculation by auto
  ultimately
  show "c \<in> pre_star (language A)"
    using accept_pre_star_exec_correct_True by auto
qed

theorem accept_pre_star_exec_correct_Some_False:
  assumes "accept_pre_star_exec_check A c = Some False"
  shows "c \<notin> pre_star (language A)"
proof -
  have "initials \<subseteq> LTS.sources A"
    using assms unfolding accept_pre_star_exec_check_def
    apply auto
    by (meson in_mono option.distinct(1)) 
  moreover
  have "\<not>accepts (pre_star_exec A) c"
    using assms
    using accept_pre_star_exec_check_def calculation by auto
  ultimately
  show "c \<notin> pre_star (language A)"
    using accept_pre_star_exec_correct_False by auto
qed

theorem accept_pre_star_exec_correct_None:
  assumes "accept_pre_star_exec_check A c = None"
  shows "\<not>initials \<subseteq> LTS.sources A"
  using assms unfolding accept_pre_star_exec_check_def by auto


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
    using assms post_star_lim'_incr_transition_star_\<epsilon>
    by (auto simp: language_\<epsilon>_def accepts_\<epsilon>_def)
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
  then have "\<exists>q. q \<in> finals \<and> (Initial p'', u, q) \<in> LTS_\<epsilon>.transition_star_\<epsilon> A'"
    by (auto simp: accepts_\<epsilon>_def)
  then obtain q where q_p: "q \<in> finals \<and> (Initial p'', u, q) \<in> LTS_\<epsilon>.transition_star_\<epsilon> A'"
    by metis
  then have "\<exists>u_\<epsilon>. q \<in> finals \<and> LTS_\<epsilon>.\<epsilon>_exp u_\<epsilon> u \<and> (Initial p'', u_\<epsilon>, q) \<in> LTS.transition_star A'"
    using LTS_\<epsilon>.transition_star_\<epsilon>_iff_\<epsilon>_exp_transition_star[of "Initial p''" u q A'] by auto
  then obtain u_\<epsilon> where II: "q \<in> finals" "LTS_\<epsilon>.\<epsilon>_exp u_\<epsilon> u" "(Initial p'', u_\<epsilon>, q) \<in> LTS.transition_star A'"
    by blast
  have "\<exists>\<gamma> u1 w1. u=\<gamma>#u1 \<and> w=op_labels w1@u1 \<and> (p'', \<gamma>) \<hookrightarrow> (p', w1)"
    using p''u_def p'w_def step.hyps(2) step_relp_def2 by auto
  then obtain \<gamma> u1 w1 where III: "u=\<gamma>#u1" "w=op_labels w1@u1" "(p'', \<gamma>) \<hookrightarrow> (p', w1)"
    by blast

  have p'_initials: "Initial p' \<in> initials"
    unfolding initials_def by auto
  have p''_initials: "Initial p'' \<in> initials"
    unfolding initials_def by auto

  have "\<exists>\<gamma>_\<epsilon> u1_\<epsilon>. LTS_\<epsilon>.\<epsilon>_exp \<gamma>_\<epsilon> [\<gamma>] \<and> LTS_\<epsilon>.\<epsilon>_exp u1_\<epsilon> u1 \<and> (Initial p'', \<gamma>_\<epsilon>@u1_\<epsilon>, q) \<in> LTS.transition_star A'"
  proof -
    have "\<exists>\<gamma>_\<epsilon> u1_\<epsilon>. LTS_\<epsilon>.\<epsilon>_exp \<gamma>_\<epsilon> [\<gamma>] \<and> LTS_\<epsilon>.\<epsilon>_exp u1_\<epsilon> u1 \<and> u_\<epsilon> = \<gamma>_\<epsilon> @ u1_\<epsilon>" 
      using LTS_\<epsilon>.\<epsilon>_exp_split'[of u_\<epsilon> \<gamma> u1] II(2) III(1) by auto
    then obtain \<gamma>_\<epsilon> u1_\<epsilon> where "LTS_\<epsilon>.\<epsilon>_exp \<gamma>_\<epsilon> [\<gamma>] \<and> LTS_\<epsilon>.\<epsilon>_exp u1_\<epsilon> u1 \<and> u_\<epsilon> = \<gamma>_\<epsilon> @ u1_\<epsilon>" 
      by auto
    then have "(Initial p'', \<gamma>_\<epsilon>@u1_\<epsilon> , q) \<in> LTS.transition_star A'"
      using II(3) by auto
    then show ?thesis
      using \<open>LTS_\<epsilon>.\<epsilon>_exp \<gamma>_\<epsilon> [\<gamma>] \<and> LTS_\<epsilon>.\<epsilon>_exp u1_\<epsilon> u1 \<and> u_\<epsilon> = \<gamma>_\<epsilon> @ u1_\<epsilon>\<close> by blast
  qed
  then obtain \<gamma>_\<epsilon> u1_\<epsilon> where iii: "LTS_\<epsilon>.\<epsilon>_exp \<gamma>_\<epsilon> [\<gamma>]" and iv: "LTS_\<epsilon>.\<epsilon>_exp u1_\<epsilon> u1" "(Initial p'', \<gamma>_\<epsilon>@u1_\<epsilon>, q) \<in> LTS.transition_star A'"
    by blast
  then have VI: "\<exists>q1. (Initial p'', \<gamma>_\<epsilon>, q1) \<in> LTS.transition_star A' \<and> (q1, u1_\<epsilon>, q) \<in> LTS.transition_star A'"
    by (simp add: LTS.transition_star_split)
  then obtain q1 where VI: "(Initial p'', \<gamma>_\<epsilon>, q1) \<in> LTS.transition_star A'" "(q1, u1_\<epsilon>, q) \<in> LTS.transition_star A'"
    by blast

  then have VI_2: "(Initial p'', [\<gamma>], q1) \<in> LTS_\<epsilon>.transition_star_\<epsilon> A'" "(q1, u1, q) \<in> LTS_\<epsilon>.transition_star_\<epsilon> A'"
    by (meson LTS_\<epsilon>.transition_star_\<epsilon>_iff_\<epsilon>_exp_transition_star iii VI(2) iv(1))+

  show ?case
  proof (cases w1)
    case pop
    then have r: "(p'', \<gamma>) \<hookrightarrow> (p', pop)"
      using III(3) by blast
    then have "(Initial p', \<epsilon>, q1) \<in> A'"
      using VI_2(1) add_trans_pop assms saturated_def saturation_def p'_initials by metis
    then have "(Initial p', w, q) \<in> LTS_\<epsilon>.transition_star_\<epsilon> A'"
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
    then have "(Initial p', Some \<gamma>', q1) \<in> A'"
      by (metis VI_2(1) add_trans_swap assms(3) saturated_def saturation_def)
    have "(Initial p', w, q) \<in> LTS_\<epsilon>.transition_star_\<epsilon> A'"
      using III(2) LTS_\<epsilon>.transition_star_\<epsilon>.transition_star_\<epsilon>_step_\<gamma> VI_2(2) append_Cons append_self_conv2 op_labels.simps(3) swap
      using \<open>(Initial p', Some \<gamma>', q1) \<in> A'\<close> by fastforce
    then have "accepts_\<epsilon> A' (p', w)"
      unfolding accepts_\<epsilon>_def
      using II(1) by blast
    then show ?thesis
      using p'_def w_def by force
  next
    case (push \<gamma>' \<gamma>'')
    then have r: "(p'', \<gamma>) \<hookrightarrow> (p', push \<gamma>' \<gamma>'')"
      using III(3) by blast
    from this VI_2 iii post_star_rules.intros(3)[OF this, of q1 A', OF VI_2(1)] have "(Initial p', Some \<gamma>', New_Noninitial p' \<gamma>') \<in> A'"
      using assms(3) by (meson saturated_def saturation_def) 
    from this r VI_2 iii post_star_rules.intros(4)[OF r, of q1 A', OF VI_2(1)] have "(New_Noninitial p' \<gamma>', Some \<gamma>'', q1) \<in> A'"
      using assms(3) using saturated_def saturation_def
      by metis
    have "(Initial p', [\<gamma>'], New_Noninitial p' \<gamma>') \<in> LTS_\<epsilon>.transition_star_\<epsilon> A' \<and> (New_Noninitial p' \<gamma>', [\<gamma>''], q1) \<in> LTS_\<epsilon>.transition_star_\<epsilon> A' \<and> (q1, u1, q) \<in> LTS_\<epsilon>.transition_star_\<epsilon> A'"
      by (metis LTS_\<epsilon>.transition_star_\<epsilon>.simps VI_2(2) \<open>(Initial p', Some \<gamma>', New_Noninitial p' \<gamma>') \<in> A'\<close> \<open>(New_Noninitial p' \<gamma>', Some \<gamma>'', q1) \<in> A'\<close>)
    have "(Initial p', w, q) \<in> LTS_\<epsilon>.transition_star_\<epsilon> A'"
       using III(2) VI_2(2) \<open>(Initial p', Some \<gamma>', New_Noninitial p' \<gamma>') \<in> A'\<close> \<open>(New_Noninitial p' \<gamma>', Some \<gamma>'', q1) \<in> A'\<close> push LTS_\<epsilon>.append_edge_edge_transition_star_\<epsilon> by auto
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

lemma init_only_hd:
  assumes "(ss, w) \<in> LTS.path_with_word A"
  assumes "initials \<subseteq> LTS.sources A"
  assumes "count (transitions_of (ss, w)) t > 0"
  assumes "t = (Initial p1, \<gamma>, q1)"
  shows "hd (transition_list (ss, w)) = t \<and> count (transitions_of (ss, w)) t = 1"
  using assms LTS.source_only_hd by (metis LTS.sources_def2 initials_sources_iff_Ctr_Loc_sources)

lemma no_edge_to_Ctr_Loc_avoid_Ctr_Loc:
  assumes "(p, w, qq) \<in> LTS.transition_star Aiminus1"
  assumes "w \<noteq> []"
  assumes "initials \<subseteq> LTS.sources Aiminus1"
  shows "qq \<notin> initials"
  using assms LTS.no_end_in_source by (metis subset_iff)

lemma no_edge_to_Ctr_Loc_avoid_Ctr_Loc_\<epsilon>:
  assumes "(p, [\<gamma>], qq) \<in> LTS_\<epsilon>.transition_star_\<epsilon> Aiminus1"
  assumes "initials \<subseteq> LTS.sources Aiminus1"
  shows "qq \<notin> initials"
  using assms LTS_\<epsilon>.no_edge_to_source_\<epsilon> by (metis subset_iff)

lemma no_edge_to_Ctr_Loc_post_star_rules':
  assumes "post_star_rules\<^sup>*\<^sup>* A Ai"
  assumes "\<nexists>q \<gamma> q'. (q, \<gamma>, Initial q') \<in> A"
  shows "\<nexists>q \<gamma> q'. (q, \<gamma>, Initial q') \<in> Ai"
using assms 
proof (induction rule: rtranclp_induct)
  case base
  then show ?case by auto
next
  case (step Aiminus1 Ai)
  then have ind: "\<nexists>q \<gamma> q'. (q, \<gamma>, Initial q') \<in> Aiminus1"
    by auto
  from step(2) show ?case
  proof (cases rule: post_star_rules.cases)
    case (add_trans_pop p \<gamma> p' q)
    have "q \<notin> initials"
      using ind no_edge_to_Ctr_Loc_avoid_Ctr_Loc_\<epsilon> initials_sources_iff_Ctr_Loc_sources by (metis local.add_trans_pop(3))
    then have "\<nexists>qq. q = Initial qq"
      by (simp add: initials_def is_Initial_def)
    then show ?thesis
      using ind local.add_trans_pop(1) by auto
  next
    case (add_trans_swap p \<gamma> p' \<gamma>' q)
    have "q \<notin> initials"
      using add_trans_swap ind no_edge_to_Ctr_Loc_avoid_Ctr_Loc_\<epsilon> initials_sources_iff_Ctr_Loc_sources by metis
    then have "\<nexists>qq. q = Initial qq"
      by (simp add: initials_def is_Initial_def)
    then show ?thesis
      using ind local.add_trans_swap(1) by auto
  next
    case (add_trans_push_1 p \<gamma> p' \<gamma>' \<gamma>'' q)
    have "q \<notin> initials"
      using add_trans_push_1 ind no_edge_to_Ctr_Loc_avoid_Ctr_Loc_\<epsilon> initials_sources_iff_Ctr_Loc_sources by metis
    then have "\<nexists>qq. q = Initial qq"
      by (simp add: initials_def is_Initial_def)
    then show ?thesis
      using ind local.add_trans_push_1(1) by auto
  next
    case (add_trans_push_2 p \<gamma> p' \<gamma>' \<gamma>'' q)
    have "q \<notin> initials"
      using add_trans_push_2 ind no_edge_to_Ctr_Loc_avoid_Ctr_Loc_\<epsilon> initials_sources_iff_Ctr_Loc_sources by metis
    then have "\<nexists>qq. q = Initial qq"
      by (simp add: initials_def is_Initial_def)
    then show ?thesis
      using ind local.add_trans_push_2(1) by auto
  qed
qed

lemma no_edge_to_Ctr_Loc_post_star_rules:
  assumes "post_star_rules\<^sup>*\<^sup>* A Ai"
  assumes "initials \<subseteq> LTS.sources A"
  shows "initials \<subseteq> LTS.sources Ai"
  using assms no_edge_to_Ctr_Loc_post_star_rules' initials_sources_iff_Ctr_Loc_sources by metis

lemma lemma_3_4'_Aux:
  assumes "post_star_rules\<^sup>*\<^sup>* A A'"
  assumes "\<forall>p \<gamma> q. (p, \<gamma>, q) \<in> A \<longrightarrow> p \<notin> New_Aut_states \<and> q \<notin> New_Aut_states"
  assumes "(Initial p', Some \<gamma>', New_Noninitial p' \<gamma>') \<notin> A'"
  shows "\<nexists>p \<gamma>. (p, \<gamma>, New_Noninitial p' \<gamma>') \<in> A'"
  using assms 
proof (induction rule: rtranclp_induct)
  case base
  then show ?case 
    unfolding New_Aut_states_def is_New_Noninitial_def by blast
next
  case (step Aiminus1 Ai)
  from step(2) show ?case
  proof (cases rule: post_star_rules.cases)
    case (add_trans_pop p''' \<gamma>'' p'' q)
    then have "(Initial p', Some \<gamma>', New_Noninitial p' \<gamma>') \<notin> Ai"
      using step.prems(2) by blast
    then have nin: "\<nexists>p \<gamma>. (p, \<gamma>, New_Noninitial p' \<gamma>') \<in> Aiminus1"
      using local.add_trans_pop(1) step.IH step.prems(1) by fastforce
    then have "New_Noninitial p' \<gamma>' \<noteq> q"
      using add_trans_pop(4) LTS_\<epsilon>.transition_star_not_to_source_\<epsilon> LTS.sources_def2
      by (metis local.add_trans_pop(3) state.distinct(3))
    then have "\<nexists>p \<gamma>. (p, \<gamma>, New_Noninitial p' \<gamma>') = (Initial p'', \<epsilon>, q)"
      by auto
    then show ?thesis
      using nin add_trans_pop(1) by auto
  next
    case (add_trans_swap p'''' \<gamma>'' p'' \<gamma>''' q)
    then have "(Initial p', Some \<gamma>', New_Noninitial p' \<gamma>') \<notin> Ai"
      using step.prems(2) by blast
    then have nin: "\<nexists>p \<gamma>. (p, \<gamma>, New_Noninitial p' \<gamma>') \<in> Aiminus1"
      using local.add_trans_swap(1) step.IH step.prems(1) by fastforce
    then have "New_Noninitial p' \<gamma>' \<noteq> q"
      using LTS.sources_def2 by (metis state.distinct(4) LTS_\<epsilon>.transition_star_not_to_source_\<epsilon> local.add_trans_swap(3)) 
    then have "\<nexists>p \<gamma>. (p, \<gamma>, New_Noninitial p' \<gamma>') = (Initial p'', Some \<gamma>''', q)"
      by auto
    then show ?thesis
      using nin add_trans_swap(1) by auto
  next
    case (add_trans_push_1 p'''' \<gamma>'' p'' \<gamma>''' \<gamma>''''' q)
    then have "(Initial p', Some \<gamma>', New_Noninitial p' \<gamma>') \<notin> Ai"
      using step.prems(2) by blast
    then show ?thesis
      using add_trans_push_1(1)
      using Un_iff state.inject(2) prod.inject singleton_iff step.IH step.prems(1) by blast 
  next
    case (add_trans_push_2 p'''' \<gamma>'' p'' \<gamma>''' \<gamma>'''' q)
    then have "(Initial p', Some \<gamma>', New_Noninitial p' \<gamma>') \<notin> Ai"
      using step.prems(2) by blast
    then have nin: "\<nexists>p \<gamma>. (p, \<gamma>, New_Noninitial p' \<gamma>') \<in> Aiminus1"
      using local.add_trans_push_2(1) step.IH step.prems(1) by fastforce
    then have "New_Noninitial p' \<gamma>' \<noteq> q"
      using LTS.sources_def2 by (metis state.disc(1,3) LTS_\<epsilon>.transition_star_not_to_source_\<epsilon> local.add_trans_push_2(3))
    then have "\<nexists>p \<gamma>. (p, \<gamma>, New_Noninitial p' \<gamma>') = (Initial p'', \<epsilon>, q)"
      by auto
    then show ?thesis
      using nin add_trans_push_2(1) by auto
  qed
qed


lemma lemma_3_4'_Aux_Aux2:
  assumes "post_star_rules\<^sup>*\<^sup>* A A'"
  assumes "\<forall>p \<gamma> q. (p, \<gamma>, q) \<in> A \<longrightarrow> p \<notin> New_Aut_states \<and> q \<notin> New_Aut_states"
  assumes "(Initial p', Some \<gamma>', New_Noninitial p' \<gamma>') \<notin> A'"
  shows "\<nexists>p \<gamma>. (New_Noninitial p' \<gamma>', \<gamma>, p) \<in> A'"
  using assms 
proof (induction rule: rtranclp_induct) (* I copy-pasted this proof from above and blindly adjusted it. So it may be a mess. *)
  case base
  then show ?case
    unfolding New_Aut_states_def is_New_Noninitial_def by blast
next
  case (step Aiminus1 Ai)
  from step(2) show ?case
  proof (cases rule: post_star_rules.cases)
    case (add_trans_pop p''' \<gamma>'' p'' q)
    then have "(Initial p', Some \<gamma>', New_Noninitial p' \<gamma>') \<notin> Ai"
      using step.prems(2) by blast
    then have nin: "\<nexists>p \<gamma>. (New_Noninitial p' \<gamma>', \<gamma>, p) \<in> Aiminus1"
      using local.add_trans_pop(1) step.IH step.prems(1) by fastforce
    then have "New_Noninitial p' \<gamma>' \<noteq> q"
      using add_trans_pop(4) LTS_\<epsilon>.transition_star_not_to_source_\<epsilon>[of "Initial p'''" "[\<gamma>'']" q Aiminus1 "New_Noninitial p' \<gamma>'"]
      using lemma_3_4'_Aux local.add_trans_pop(1) step.hyps(1) step.prems(1) step.prems(2)
      using UnI1 local.add_trans_pop(3) LTS.sources_def2 by (metis (full_types) state.distinct(3))
    then have "\<nexists>p \<gamma>. (p, \<gamma>, New_Noninitial p' \<gamma>') = (Initial p'', \<epsilon>, q)"
      by auto
    then show ?thesis
      using nin add_trans_pop(1) by auto
  next
    case (add_trans_swap p'''' \<gamma>'' p'' \<gamma>''' q)
    then have "(Initial p', Some \<gamma>', New_Noninitial p' \<gamma>') \<notin> Ai"
      using step.prems(2) by blast
    then have nin: "\<nexists>p \<gamma>. (New_Noninitial p' \<gamma>', \<gamma>, p) \<in> Aiminus1"
      using local.add_trans_swap(1) step.IH step.prems(1) by fastforce
    then have "New_Noninitial p' \<gamma>' \<noteq> q"
      using LTS_\<epsilon>.transition_star_not_to_source_\<epsilon>[of "Initial p''''" "[\<gamma>'']" q Aiminus1] local.add_trans_swap(3)
      using lemma_3_4'_Aux[of _ Aiminus1 p' \<gamma>']  UnCI local.add_trans_swap(1) step.hyps(1) step.prems(1) step.prems(2)
       state.simps(7) LTS.sources_def2
      by metis
    then have "\<nexists>p \<gamma>. (p, \<gamma>, New_Noninitial p' \<gamma>') = (Initial p'', Some \<gamma>''', q)"
      by auto
    then show ?thesis
      using nin add_trans_swap(1) by auto
  next
    case (add_trans_push_1 p'''' \<gamma>'' p'' \<gamma>''' \<gamma>''''' q)
    then have "(Initial p', Some \<gamma>', New_Noninitial p' \<gamma>') \<notin> Ai"
      using step.prems(2) by blast
    then show ?thesis
      using add_trans_push_1(1)
      using Un_iff state.inject prod.inject singleton_iff step.IH step.prems(1) by blast 
  next
    case (add_trans_push_2 p'''' \<gamma>'' p'' \<gamma>''' \<gamma>'''' q)
    then have "(Initial p', Some \<gamma>', New_Noninitial p' \<gamma>') \<notin> Ai"
      using step.prems(2) by blast
    then have nin: "\<nexists>p \<gamma>. (New_Noninitial p' \<gamma>', \<gamma>, p) \<in> Aiminus1"
      using local.add_trans_push_2(1) step.IH step.prems(1) by fastforce
    then have "New_Noninitial p' \<gamma>' \<noteq> q"
      using state.disc(3) LTS_\<epsilon>.transition_star_not_to_source_\<epsilon>[of "Initial p''''" "[\<gamma>'']" q Aiminus1  "New_Noninitial p' \<gamma>'"] local.add_trans_push_2(3)
      using lemma_3_4'_Aux[of _ Aiminus1 p' \<gamma>'] UnCI local.add_trans_push_2(1) step.hyps(1) step.prems(1) step.prems(2)
        LTS.sources_def2 state.disc(1)
      by metis
    then have "\<nexists>p \<gamma>. (New_Noninitial p' \<gamma>', \<gamma>, p) = (Initial p'', \<epsilon>, q)"
      by auto
    then show ?thesis
      using nin add_trans_push_2(1)
      using local.add_trans_push_2 step.prems(2) by auto 
  qed
qed

lemma lemma_3_4':
  assumes "post_star_rules\<^sup>*\<^sup>* A A'"
  assumes "initials \<subseteq> LTS.sources A"
  assumes "\<forall>p \<gamma> q. (p, \<gamma>, q) \<in> A \<longrightarrow> p \<notin> New_Aut_states \<and> q \<notin> New_Aut_states"
  assumes "(Initial p, w, ss, q) \<in> LTS.transition_star_states A'"
  shows "(\<not>is_New_Noninitial q \<longrightarrow> (\<exists>p' w'. (Initial p', w', q) \<in> LTS_\<epsilon>.transition_star_\<epsilon> A \<and> (p',w') \<Rightarrow>\<^sup>* (p, LTS_\<epsilon>.remove_\<epsilon> w))) \<and>
         (is_New_Noninitial q \<longrightarrow> (the_New_Ctr_Loc q, [the_New_Label q]) \<Rightarrow>\<^sup>* (p, LTS_\<epsilon>.remove_\<epsilon> w))"
  using assms
proof (induction arbitrary: p q w ss rule: rtranclp_induct)
  case base
  {
    assume ctr_loc: "is_Initial q \<or> is_Noninitial q"
    then have "(Initial p, LTS_\<epsilon>.remove_\<epsilon> w, q) \<in> LTS_\<epsilon>.transition_star_\<epsilon> A"
      using base using LTS_\<epsilon>.transition_star_states_transition_star_\<epsilon> by metis
    then have "\<exists>p' w'. (p', w', q) \<in> LTS_\<epsilon>.transition_star_\<epsilon> A"
      by auto
    then have ?case
      using ctr_loc
      using \<open>(Initial p, LTS_\<epsilon>.remove_\<epsilon> w, q) \<in> LTS_\<epsilon>.transition_star_\<epsilon> A\<close> by blast
  }
  moreover
  {
    assume "is_New_Noninitial q"
    then have ?case
    proof (cases w)
      case Nil
      then have False using base
        using LTS.transition_star_empty LTS.transition_star_states_transition_star \<open>is_New_Noninitial q\<close>
        by (metis state.disc(7))
      then show ?thesis
        by metis
    next
      case (Cons \<gamma> w_rest)
      then have a: "(Initial p, \<gamma>#w_rest, ss, q) \<in> LTS.transition_star_states A"
        using base Cons by blast
      then have "\<exists>s \<gamma>'. (s, \<gamma>', q) \<in> A"
        using LTS.transition_star_states_transition_relation by metis
      then have False
        using \<open>is_New_Noninitial q\<close> base.prems(2) New_Aut_states_def by blast
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
  define j where "j = count (transitions_of' (Initial p, w, ss, q)) t"

  note ss_p = step(6)

  from j_def ss_p show ?case
  proof (induction j arbitrary: p q w ss)
    case 0
    then have "(Initial p, w, ss, q) \<in> LTS.transition_star_states Aiminus1"
      using count_zero_remove_path_with_word_transition_star_states p1_\<gamma>_p2_w2_q'_p(1) t_def
      by metis
    then show ?case
      using step by auto
  next
    case (Suc j)
    from step(2) show ?case
    proof (cases rule: post_star_rules.cases)
      case (add_trans_pop p2 \<gamma>2 p1 q1) (* p1 shadows p1. q1 shadows q1. A bit brave... *)
      note III = add_trans_pop(3)
      note VI = add_trans_pop(2)
      have t_def: "t = (Initial p1, \<epsilon>, q1)"
        using local.add_trans_pop(1) local.add_trans_pop p1_\<gamma>_p2_w2_q'_p(1) t_def by blast
      have init_Ai: "initials \<subseteq> LTS.sources Ai"
        using step(1,2) step(4)
        using no_edge_to_Ctr_Loc_post_star_rules 
        using r_into_rtranclp by (metis)
      have ttt''': "hd (transition_list (ss, w)) = t \<and> count (transitions_of (ss, w)) t = 1"
      proof -
        have "(ss, w) \<in> LTS.path_with_word Ai"
          using Suc(3) LTS.transition_star_states_path_with_word by metis
        moreover 
        have "initials \<subseteq> LTS.sources Ai"
          using init_Ai by auto
        moreover 
        have "0 < count (transitions_of (ss, w)) t"
          by (metis Suc.prems(1) transitions_of'.simps zero_less_Suc)
        moreover 
        have "t = (Initial p1, \<epsilon>, q1)"
          using t_def by auto
        moreover 
        have "Initial p1 \<in> initials"
          by (simp add: initials_def)
        ultimately
        show "hd (transition_list (ss, w)) = t \<and> count (transitions_of (ss, w)) t = 1"
          using init_only_hd[of ss w Ai t p1 \<epsilon> q1] by auto
      qed

      have "transition_list (ss, w) \<noteq> []"
        by (metis LTS.transition_star_states_path_with_word LTS.path_with_word.simps Suc.prems(1) Suc.prems(2) count_empty less_not_refl2 list.distinct(1) transition_list.simps(1) transitions_of'.simps transitions_of.simps(2) zero_less_Suc)
      then have ttt'': "([Initial p1,q1], [\<epsilon>]) @\<acute> (tl ss,  tl w) = (ss, w)"
        using  ttt''' t_def hd_transition_list_append_path_with_word by metis
      then have ttt': "(Initial p1, [\<epsilon>], [Initial p1,q1], q1) @@\<acute> (q1, tl w, tl ss, q) = (Initial p1, w, ss, q)"
        by auto
      have VII: "p = p1"
      proof -
        have "(Initial p, w, ss, q) \<in> LTS.transition_star_states Ai"
          using Suc.prems(2) by blast
        moreover
        have "t = hd (transition_list' (Initial p, w, ss, q))"
          using \<open>hd (transition_list (ss, w)) = t \<and> count (transitions_of (ss, w)) t = 1\<close> by fastforce
        moreover
        have "transition_list' (Initial p, w, ss, q) \<noteq> []"
          by (simp add: \<open>transition_list (ss, w) \<noteq> []\<close>)
        moreover
        have "t = (Initial p1, \<epsilon>, q1)"
          using t_def by auto
        ultimately
        show "p = p1"
          using LTS.hd_is_hd by fastforce
      qed
      have "j=0"
        using Suc(2) \<open>hd (transition_list (ss, w)) = t \<and> count (transitions_of (ss, w)) t = 1\<close> by force
      have "(Initial p1, [\<epsilon>], [Initial p1, q1], q1) \<in> LTS.transition_star_states Ai"
      proof -
        have "(Initial p1, \<epsilon>, q1) \<in> Ai"
          using local.add_trans_pop(1) by auto
        moreover
        have "(Initial p1, \<epsilon>, q1) \<notin> Aiminus1"
          by (simp add: local.add_trans_pop)
        ultimately
        show "(Initial p1, [\<epsilon>], [Initial p1, q1], q1) \<in> LTS.transition_star_states Ai"
          by (meson LTS.transition_star_states.transition_star_states_refl LTS.transition_star_states.transition_star_states_step)
      qed
      have "(q1, tl w, tl ss, q) \<in> LTS.transition_star_states Aiminus1"
      proof -
        from Suc(3) have "(ss, w) \<in> LTS.path_with_word Ai"
          by (meson LTS.transition_star_states_path_with_word)
        then have one: "(tl ss, tl w) \<in> LTS.path_with_word Ai"
          by (metis LTS.path_with_word.simps \<open>transition_list (ss, w) \<noteq> []\<close> list.sel(3) transition_list.simps(2))
        from ttt''' have two: "0 = count (transitions_of (tl ss, tl w)) (Initial p1, \<epsilon>, q1)"
          using count_append_path_with_word_\<gamma>[of "[hd ss]" "[]" "tl ss" "hd w" "tl w" "Initial p1" \<epsilon> q1, simplified]
            \<open>(Initial p1, [\<epsilon>], [Initial p1, q1], q1) \<in> LTS.transition_star_states Ai\<close> \<open>transition_list (ss, w) \<noteq> []\<close>
            Suc.prems(2) VII LTS.transition_list_Cons[of "Initial p" w ss q Ai \<epsilon> q1]
          by (auto simp: t_def)
        have three: "Ai = Aiminus1 \<union> {(Initial p1, \<epsilon>, q1)}"
          using local.add_trans_pop(1) by auto
        from ttt''' one two three count_zero_remove_path_with_word[OF one, of "Initial p1" \<epsilon> q1 Aiminus1] have "(tl ss, tl w) \<in> LTS.path_with_word Aiminus1"
          by auto
        moreover
        have "hd (tl ss) = q1"
          using Suc.prems(2) VII \<open>transition_list (ss, w) \<noteq> []\<close> t_def LTS.transition_list_Cons ttt''' by fastforce
        moreover
        have "last ss = q"
          by (metis LTS.transition_star_states_last Suc.prems(2))
        ultimately
        show "(q1, tl w, tl ss, q) \<in> LTS.transition_star_states Aiminus1"
          by (metis (no_types, lifting) LTS.transition_star_states_path_with_word LTS.path_with_word_transition_star_states LTS.path_with_word_not_empty Suc.prems(2) last_ConsR list.collapse)
      qed
      have "w = \<epsilon> # (tl w)"
        by (metis Suc(3) VII \<open>transition_list (ss, w) \<noteq> []\<close> list.distinct(1) list.exhaust_sel list.sel(1) t_def LTS.transition_list_Cons ttt''')
      then have w_tl_\<epsilon>: "LTS_\<epsilon>.remove_\<epsilon> w = LTS_\<epsilon>.remove_\<epsilon> (tl w)"
        by (metis LTS_\<epsilon>.remove_\<epsilon>_def removeAll.simps(2))

      have "\<exists>\<gamma>2'. LTS_\<epsilon>.\<epsilon>_exp \<gamma>2' [\<gamma>2] \<and> (Initial p2, \<gamma>2', q1) \<in> LTS.transition_star Aiminus1"
        using add_trans_pop
        by (simp add: LTS_\<epsilon>.transition_star_\<epsilon>_\<epsilon>_exp_transition_star) 
      then obtain \<gamma>2' where "LTS_\<epsilon>.\<epsilon>_exp \<gamma>2' [\<gamma>2] \<and> (Initial p2, \<gamma>2', q1) \<in> LTS.transition_star Aiminus1"
        by blast
      then have "\<exists>ss2. (Initial p2, \<gamma>2', ss2, q1) \<in> LTS.transition_star_states Aiminus1"
        by (simp add: LTS.transition_star_transition_star_states)
      then obtain ss2 where IIII_1: "(Initial p2, \<gamma>2', ss2, q1) \<in> LTS.transition_star_states Aiminus1"
        by blast
      have IIII_2: "(q1, tl w, tl ss, q) \<in> LTS.transition_star_states Aiminus1"
        using ttt' Suc(3) Suc(2) \<open>j=0\<close>
        using \<open>(q1, tl w, tl ss, q) \<in> LTS.transition_star_states Aiminus1\<close> by blast
      have IIII: "(Initial p2, \<gamma>2' @ tl w, ss2 @ (tl (tl ss)), q) \<in> LTS.transition_star_states Aiminus1"
        using IIII_1 IIII_2 by (meson LTS.transition_star_states_append)

      from Suc(1)[of p2 "\<gamma>2' @ tl w" "ss2 @ (tl (tl ss))" q]
      have V: "(\<not>is_New_Noninitial q \<longrightarrow>
     (\<exists>p' w'. (Initial p', w', q) \<in> LTS_\<epsilon>.transition_star_\<epsilon> A \<and> (p', w') \<Rightarrow>\<^sup>* (p2, LTS_\<epsilon>.remove_\<epsilon> (\<gamma>2' @ tl w)))) \<and>
    (is_New_Noninitial q \<longrightarrow> (the_New_Ctr_Loc q, [the_New_Label q]) \<Rightarrow>\<^sup>* (p2, LTS_\<epsilon>.remove_\<epsilon> (\<gamma>2' @ tl w)))"
        using IIII
        using step.IH step.prems(1) step.prems(2) by blast

      have "\<not>is_New_Noninitial q \<or> is_New_Noninitial q"
        using state.exhaust_disc by blast
      then show ?thesis
      proof
        assume ctr_q: "\<not>is_New_Noninitial q"
        then have "\<exists>p' w'. (Initial p', w', q) \<in> LTS_\<epsilon>.transition_star_\<epsilon> A \<and> (p', w') \<Rightarrow>\<^sup>* (p2, LTS_\<epsilon>.remove_\<epsilon> (\<gamma>2' @ tl w))"
          using V by auto
        then obtain p' w' where
          VIII:"(Initial p', w', q) \<in> LTS_\<epsilon>.transition_star_\<epsilon> A" and gu: "(p', w') \<Rightarrow>\<^sup>* (p2, LTS_\<epsilon>.remove_\<epsilon> (\<gamma>2' @ tl w))"
          by blast
        then have "(p',w') \<Rightarrow>\<^sup>* (p2, LTS_\<epsilon>.remove_\<epsilon> (\<gamma>2' @ tl w)) \<and> 
                   (p2, LTS_\<epsilon>.remove_\<epsilon> (\<gamma>2' @ tl w)) \<Rightarrow>\<^sup>* (p, LTS_\<epsilon>.remove_\<epsilon> (tl w))"
        proof -
          have \<gamma>2'_\<gamma>2: "LTS_\<epsilon>.remove_\<epsilon> \<gamma>2' = [\<gamma>2]"
            by (metis LTS_\<epsilon>.\<epsilon>_exp_def LTS_\<epsilon>.remove_\<epsilon>_def \<open>LTS_\<epsilon>.\<epsilon>_exp \<gamma>2' [\<gamma>2] \<and> (Initial p2, \<gamma>2', q1) \<in> LTS.transition_star Aiminus1\<close>)
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
        then have "(p',w') \<Rightarrow>\<^sup>* (p, LTS_\<epsilon>.remove_\<epsilon> (tl w)) \<and> (Initial p', w', q) \<in> LTS_\<epsilon>.transition_star_\<epsilon> A"
          using VIII by force
        then have "\<exists>p' w'. (Initial p', w', q) \<in> LTS_\<epsilon>.transition_star_\<epsilon> A \<and> (p', w') \<Rightarrow>\<^sup>* (p, LTS_\<epsilon>.remove_\<epsilon> w)"
          using w_tl_\<epsilon> by auto
        then show ?thesis
          using ctr_q \<open>p = p1\<close> by blast 
      next
        assume "is_New_Noninitial q"
        from V have "(the_New_Ctr_Loc q, [the_New_Label q]) \<Rightarrow>\<^sup>* (p2, \<gamma>2#(LTS_\<epsilon>.remove_\<epsilon> w))"
          by (metis LTS_\<epsilon>.\<epsilon>_exp_def LTS_\<epsilon>.remove_\<epsilon>_append_dist LTS_\<epsilon>.remove_\<epsilon>_def \<open>LTS_\<epsilon>.\<epsilon>_exp \<gamma>2' [\<gamma>2] \<and> (Initial p2, \<gamma>2', q1) \<in> LTS.transition_star Aiminus1\<close> \<open>is_New_Noninitial q\<close> append_Cons append_self_conv2 w_tl_\<epsilon>)
          
        then have "(the_New_Ctr_Loc q, [the_New_Label q]) \<Rightarrow>\<^sup>* (p1, LTS_\<epsilon>.remove_\<epsilon> w)"
          using VI by (metis append_Nil op_labels.simps(1) rtranclp.simps step_relp_def2) 
        then have "(the_New_Ctr_Loc q, [the_New_Label q]) \<Rightarrow>\<^sup>* (p, LTS_\<epsilon>.remove_\<epsilon> w)"
          using VII by auto
        then show ?thesis
          using \<open>is_New_Noninitial q\<close> by blast
      qed
    next
      case (add_trans_swap p2 \<gamma>2 p1 \<gamma>' q1) (* Copied and ajusted from previous case *)
      note III = add_trans_swap(3)
      note VI = add_trans_swap(2)
      have t_def: "t = (Initial p1, Some \<gamma>', q1)"
        using local.add_trans_swap(1) local.add_trans_swap p1_\<gamma>_p2_w2_q'_p(1) t_def by blast
      have init_Ai: "initials \<subseteq> LTS.sources Ai"
        using step(1,2) step(4)
        using no_edge_to_Ctr_Loc_post_star_rules
        by (meson r_into_rtranclp)
      have ttt''': "hd (transition_list (ss, w)) = t \<and> count (transitions_of (ss, w)) t = 1"
      proof -
        have "(ss, w) \<in> LTS.path_with_word Ai"
          using Suc(3) LTS.transition_star_states_path_with_word by metis
        moreover 
        have "initials \<subseteq> LTS.sources Ai"
          using init_Ai by auto
        moreover 
        have "0 < count (transitions_of (ss, w)) t"
          by (metis Suc.prems(1) transitions_of'.simps zero_less_Suc)
        moreover 
        have "t = (Initial p1, Some \<gamma>', q1)"
          using t_def
          by auto
        moreover 
        have "Initial p1 \<in> initials"
          using initials_def by force
        ultimately
        show "hd (transition_list (ss, w)) = t \<and> count (transitions_of (ss, w)) t = 1"
          using init_only_hd[of ss w Ai t p1 _ q1] by auto
      qed

      have "transition_list (ss, w) \<noteq> []"
        by (metis LTS.transition_star_states_path_with_word LTS.path_with_word.simps Suc.prems(1) Suc.prems(2) count_empty less_not_refl2 list.distinct(1) transition_list.simps(1) transitions_of'.simps transitions_of.simps(2) zero_less_Suc)
      then have ttt'': "([Initial p1,q1], [Some \<gamma>']) @\<acute> (tl ss,  tl w) = (ss, w)"
        using  ttt''' t_def hd_transition_list_append_path_with_word by metis
      then have ttt': "(Initial p1, [Some \<gamma>'], [Initial p1,q1], q1) @@\<acute> (q1, tl w, tl ss, q) = (Initial p1, w, ss, q)"
        by auto
      have VII: "p = p1"
      proof -
        have "(Initial p, w, ss, q) \<in> LTS.transition_star_states Ai"
          using Suc.prems(2) by blast
        moreover
        have "t = hd (transition_list' (Initial p, w, ss, q))"
          using \<open>hd (transition_list (ss, w)) = t \<and> count (transitions_of (ss, w)) t = 1\<close> by fastforce
        moreover
        have "transition_list' (Initial p, w, ss, q) \<noteq> []"
          by (simp add: \<open>transition_list (ss, w) \<noteq> []\<close>)
        moreover
        have "t = (Initial p1, Some \<gamma>', q1)"
          using t_def by auto
        ultimately
        show "p = p1"
          using LTS.hd_is_hd by fastforce
      qed
      have "j=0"
        using Suc(2) \<open>hd (transition_list (ss, w)) = t \<and> count (transitions_of (ss, w)) t = 1\<close> by force
      have "(Initial p1, [Some \<gamma>'], [Initial p1, q1], q1) \<in> LTS.transition_star_states Ai"
      proof -
        have "(Initial p1, Some \<gamma>', q1) \<in> Ai"
          using local.add_trans_swap(1) by auto
        moreover
        have "(Initial p1, Some \<gamma>', q1) \<notin> Aiminus1"
          using local.add_trans_swap(4) by blast
        ultimately
        show "(Initial p1, [Some \<gamma>'], [Initial p1, q1], q1) \<in> LTS.transition_star_states Ai"
          by (meson LTS.transition_star_states.transition_star_states_refl LTS.transition_star_states.transition_star_states_step)
      qed
      have "(q1, tl w, tl ss, q) \<in> LTS.transition_star_states Aiminus1"
      proof -
        from Suc(3) have "(ss, w) \<in> LTS.path_with_word Ai"
          by (meson LTS.transition_star_states_path_with_word)
        then have one: "(tl ss, tl w) \<in> LTS.path_with_word Ai"
          by (metis LTS.path_with_word.simps \<open>transition_list (ss, w) \<noteq> []\<close> list.sel(3) transition_list.simps(2))
        from ttt''' have two: "0 = count (transitions_of (tl ss, tl w)) (Initial p1, Some \<gamma>', q1)"
          using count_append_path_with_word_\<gamma>[of "[hd ss]" "[]" "tl ss" "hd w" "tl w" "Initial p1" "Some \<gamma>'" q1, simplified]
            \<open>(Initial p1, [Some \<gamma>'], [Initial p1, q1], q1) \<in> LTS.transition_star_states Ai\<close> \<open>transition_list (ss, w) \<noteq> []\<close>
            Suc.prems(2) VII LTS.transition_list_Cons[of "Initial p" w ss q Ai "Some \<gamma>'" q1]
          by (auto simp: t_def)
        have three: "Ai = Aiminus1 \<union> {(Initial p1, Some \<gamma>', q1)}"
          using local.add_trans_swap(1) by auto 
        from ttt''' one two three count_zero_remove_path_with_word[OF one, of "Initial p1" _ q1 Aiminus1] have "(tl ss, tl w) \<in> LTS.path_with_word Aiminus1"
          by auto
        moreover
        have "hd (tl ss) = q1"
          using Suc.prems(2) VII \<open>transition_list (ss, w) \<noteq> []\<close> t_def LTS.transition_list_Cons ttt''' by fastforce
        moreover
        have "last ss = q"
          by (metis LTS.transition_star_states_last Suc.prems(2))
        ultimately
        show "(q1, tl w, tl ss, q) \<in> LTS.transition_star_states Aiminus1"
          by (metis (no_types, lifting) LTS.transition_star_states_path_with_word LTS.path_with_word_transition_star_states LTS.path_with_word_not_empty Suc.prems(2) last_ConsR list.collapse)
      qed
      have "w = Some \<gamma>' # (tl w)"
        by (metis Suc(3) VII \<open>transition_list (ss, w) \<noteq> []\<close> list.distinct(1) list.exhaust_sel list.sel(1) t_def LTS.transition_list_Cons ttt''')
      then have w_tl_\<epsilon>: "LTS_\<epsilon>.remove_\<epsilon> w = LTS_\<epsilon>.remove_\<epsilon> (Some \<gamma>'#tl w)"
        using LTS_\<epsilon>.remove_\<epsilon>_def removeAll.simps(2)
        by presburger 
      have "\<exists>\<gamma>2'. LTS_\<epsilon>.\<epsilon>_exp \<gamma>2' [\<gamma>2] \<and> (Initial p2, \<gamma>2', q1) \<in> LTS.transition_star Aiminus1"
        using add_trans_swap by (simp add: LTS_\<epsilon>.transition_star_\<epsilon>_\<epsilon>_exp_transition_star) 
      then obtain \<gamma>2' where "LTS_\<epsilon>.\<epsilon>_exp \<gamma>2' [\<gamma>2] \<and> (Initial p2, \<gamma>2', q1) \<in> LTS.transition_star Aiminus1"
        by blast
      then have "\<exists>ss2. (Initial p2, \<gamma>2', ss2, q1) \<in> LTS.transition_star_states Aiminus1"
        by (simp add: LTS.transition_star_transition_star_states)
      then obtain ss2 where IIII_1: "(Initial p2, \<gamma>2', ss2, q1) \<in> LTS.transition_star_states Aiminus1"
        by blast
      have IIII_2: "(q1, tl w, tl ss, q) \<in> LTS.transition_star_states Aiminus1"
        using ttt' Suc(3) Suc(2) \<open>j=0\<close>
        using \<open>(q1, tl w, tl ss, q) \<in> LTS.transition_star_states Aiminus1\<close> by blast
      have IIII: "(Initial p2, \<gamma>2' @ tl w, ss2 @ (tl (tl ss)), q) \<in> LTS.transition_star_states Aiminus1"
        using IIII_1 IIII_2 by (meson LTS.transition_star_states_append)

      from Suc(1)[of p2 "\<gamma>2' @ tl w" "ss2 @ (tl (tl ss))" q]
      have V: "(\<not>is_New_Noninitial q \<longrightarrow>
     (\<exists>p' w'. (Initial p', w', q) \<in> LTS_\<epsilon>.transition_star_\<epsilon> A \<and> (p', w') \<Rightarrow>\<^sup>* (p2, LTS_\<epsilon>.remove_\<epsilon> (\<gamma>2' @ tl w)))) \<and>
    (is_New_Noninitial q \<longrightarrow> (the_New_Ctr_Loc q, [the_New_Label q]) \<Rightarrow>\<^sup>* (p2, LTS_\<epsilon>.remove_\<epsilon> (\<gamma>2' @ tl w)))"
        using IIII
        using step.IH step.prems(1) step.prems(2) by blast

      have "\<not>is_New_Noninitial q \<or> is_New_Noninitial q"
        using state.exhaust_disc by blast
      then show ?thesis
      proof
        assume ctr_q: "\<not>is_New_Noninitial q"
        then have "\<exists>p' w'. (Initial p', w', q) \<in> LTS_\<epsilon>.transition_star_\<epsilon> A \<and> (p', w') \<Rightarrow>\<^sup>* (p2, LTS_\<epsilon>.remove_\<epsilon> (\<gamma>2' @ tl w))"
          using V by auto
        then obtain p' w' where
          VIII:"(Initial p', w', q) \<in> LTS_\<epsilon>.transition_star_\<epsilon> A" and gu: "(p', w') \<Rightarrow>\<^sup>* (p2, LTS_\<epsilon>.remove_\<epsilon> (\<gamma>2' @ tl w))"
          by blast
        then have "(p',w') \<Rightarrow>\<^sup>* (p2, LTS_\<epsilon>.remove_\<epsilon> (\<gamma>2' @ tl w)) \<and> 
                   (p2, LTS_\<epsilon>.remove_\<epsilon> (\<gamma>2' @ tl w)) \<Rightarrow>\<^sup>* (p, \<gamma>' # LTS_\<epsilon>.remove_\<epsilon> (tl w))"
        proof -
          have \<gamma>2'_\<gamma>2: "LTS_\<epsilon>.remove_\<epsilon> \<gamma>2' = [\<gamma>2]"
            by (metis LTS_\<epsilon>.\<epsilon>_exp_def LTS_\<epsilon>.remove_\<epsilon>_def \<open>LTS_\<epsilon>.\<epsilon>_exp \<gamma>2' [\<gamma>2] \<and> (Initial p2, \<gamma>2', q1) \<in> LTS.transition_star Aiminus1\<close>)
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
        then have "(p',w') \<Rightarrow>\<^sup>* (p, \<gamma>' # LTS_\<epsilon>.remove_\<epsilon> (tl w)) \<and> (Initial p', w', q) \<in> LTS_\<epsilon>.transition_star_\<epsilon> A"
          using VIII by force
        then have "\<exists>p' w'. (Initial p', w', q) \<in> LTS_\<epsilon>.transition_star_\<epsilon> A \<and> (p', w') \<Rightarrow>\<^sup>* (p, LTS_\<epsilon>.remove_\<epsilon> w)"
          using LTS_\<epsilon>.remove_\<epsilon>_Cons_tl by (metis \<open>w = Some \<gamma>' # tl w\<close>) 
        then show ?thesis
          using ctr_q \<open>p = p1\<close> by blast 
      next
        assume "is_New_Noninitial q"
        from V this have "(the_New_Ctr_Loc q, [the_New_Label q]) \<Rightarrow>\<^sup>* (p2, LTS_\<epsilon>.remove_\<epsilon> (\<gamma>2' @ tl w))"
          by auto
        then have "(the_New_Ctr_Loc q, [the_New_Label q]) \<Rightarrow>\<^sup>* (p2, \<gamma>2#(LTS_\<epsilon>.remove_\<epsilon> (tl w)))"
          by (metis LTS_\<epsilon>.\<epsilon>_exp_def LTS_\<epsilon>.remove_\<epsilon>_append_dist LTS_\<epsilon>.remove_\<epsilon>_def \<open>LTS_\<epsilon>.\<epsilon>_exp \<gamma>2' [\<gamma>2] \<and> (Initial p2, \<gamma>2', q1) \<in> LTS.transition_star Aiminus1\<close> append_Cons append_self_conv2)
        then have "(the_New_Ctr_Loc q, [the_New_Label q]) \<Rightarrow>\<^sup>* (p1, \<gamma>' # LTS_\<epsilon>.remove_\<epsilon> (tl w))"
          using VI
          by (metis (no_types) append_Cons append_Nil op_labels.simps(2) rtranclp.rtrancl_into_rtrancl step_relp_def2)
        then have "(the_New_Ctr_Loc q, [the_New_Label q]) \<Rightarrow>\<^sup>* (p, \<gamma>' # LTS_\<epsilon>.remove_\<epsilon> (tl w))"
          using VII by auto
        then show ?thesis
          using \<open>is_New_Noninitial q\<close>
          by (metis LTS_\<epsilon>.remove_\<epsilon>_Cons_tl w_tl_\<epsilon>)
      qed
    next
      case (add_trans_push_1 p2 \<gamma>2 p1 \<gamma>1 \<gamma>'' q1')
      then have t_def: "t = (Initial p1, Some \<gamma>1, New_Noninitial p1 \<gamma>1)"
        using local.add_trans_pop(1) local.add_trans_pop p1_\<gamma>_p2_w2_q'_p(1) t_def by blast
      have init_Ai: "initials \<subseteq> LTS.sources Ai"
        using step(1,2) step(4)
        using no_edge_to_Ctr_Loc_post_star_rules
        by (meson r_into_rtranclp)
      have ttt''': "hd (transition_list (ss, w)) = t \<and> count (transitions_of (ss, w)) t = 1"
      proof -
        have "(ss, w) \<in> LTS.path_with_word Ai"
          using Suc(3) LTS.transition_star_states_path_with_word by metis
        moreover 
        have  "initials \<subseteq> LTS.sources Ai"
          using init_Ai by auto
        moreover 
        have "0 < count (transitions_of (ss, w)) t"
          by (metis Suc.prems(1) transitions_of'.simps zero_less_Suc)
        moreover 
        have "t = (Initial p1, Some \<gamma>1, New_Noninitial p1 \<gamma>1)"
          using t_def by auto
        moreover 
        have "Initial p1 \<in> initials"
          using initials_def by fastforce
        ultimately
        show "hd (transition_list (ss, w)) = t \<and> count (transitions_of (ss, w)) t = 1"
          using init_only_hd[of ss w Ai t] by auto
      qed
      have "transition_list (ss, w) \<noteq> []"
        by (metis LTS.transition_star_states_path_with_word LTS.path_with_word.simps Suc.prems(1) Suc.prems(2) count_empty less_not_refl2 list.distinct(1) transition_list.simps(1) transitions_of'.simps transitions_of.simps(2) zero_less_Suc)

      have VII: "p = p1"
      proof -
        have "(Initial p, w, ss, q) \<in> LTS.transition_star_states Ai"
          using Suc.prems(2) by blast
        moreover
        have "t = hd (transition_list' (Initial p, w, ss, q))"
          using \<open>hd (transition_list (ss, w)) = t \<and> count (transitions_of (ss, w)) t = 1\<close> by fastforce
        moreover
        have "transition_list' (Initial p, w, ss, q) \<noteq> []"
          by (simp add: \<open>transition_list (ss, w) \<noteq> []\<close>)
        moreover
        have "t = (Initial p1, Some \<gamma>1, New_Noninitial p1 \<gamma>1)"
          using t_def by auto
        ultimately
        show "p = p1"
          using LTS.hd_is_hd by fastforce
      qed
      from add_trans_push_1(4) have "\<nexists>p \<gamma>. (New_Noninitial p1 \<gamma>1, \<gamma>, p) \<in> Aiminus1"
        using lemma_3_4'_Aux_Aux2[OF step(1) assms(3) add_trans_push_1(4)]
        by auto
      then have "\<nexists>p \<gamma>. (New_Noninitial p1 \<gamma>1, \<gamma>, p) \<in> Ai"
        using local.add_trans_push_1(1) by blast
      then have ss_w_short: "ss = [Initial p1, New_Noninitial p1 \<gamma>1] \<and> w = [Some \<gamma>1]"
        using Suc.prems(2) VII \<open>hd (transition_list (ss, w)) = t \<and> count (transitions_of (ss, w)) t = 1\<close> t_def
        using LTS.nothing_after_zink[of "Initial p1" "New_Noninitial p1 \<gamma>1" "tl (tl ss)" "Some \<gamma>1" "tl w" Ai] \<open>transition_list (ss, w) \<noteq> []\<close>
        LTS.transition_star_states_path_with_word[of "Initial p" w ss q Ai]
        LTS.transition_list_Cons[of "Initial p" w ss q Ai]
        by (auto simp: LTS.zinks_def2)
      then have q_ext: "q = New_Noninitial p1 \<gamma>1"
        using LTS.transition_star_states_last Suc.prems(2) by fastforce
      have "(p1, [\<gamma>1]) \<Rightarrow>\<^sup>* (p, LTS_\<epsilon>.remove_\<epsilon> w)"
        using ss_w_short unfolding LTS_\<epsilon>.remove_\<epsilon>_def
        using VII by force
      thm Suc(1)
      have "(the_New_Ctr_Loc q, [the_New_Label q]) \<Rightarrow>\<^sup>* (p, LTS_\<epsilon>.remove_\<epsilon> w)"
        by (simp add: \<open>(p1, [\<gamma>1]) \<Rightarrow>\<^sup>* (p, LTS_\<epsilon>.remove_\<epsilon> w)\<close> q_ext)
      then show ?thesis
        using q_ext by auto
    next
      case (add_trans_push_2 p2 \<gamma>2 p1 \<gamma>1 \<gamma>'' q') (* Copied and adjusted from previous case *)
      note IX = add_trans_push_2(3)
      note XIII = add_trans_push_2(2)
      have t_def: "t = (New_Noninitial p1 \<gamma>1, Some \<gamma>'', q')"
        using local.add_trans_swap(1) local.add_trans_push_2 p1_\<gamma>_p2_w2_q'_p(1) t_def by blast
      have init_Ai: "initials \<subseteq> LTS.sources Ai"
        using step(1,2) step(4)
        using no_edge_to_Ctr_Loc_post_star_rules
        by (meson r_into_rtranclp)

      from Suc(3) Suc(2) split_at_first_t[of "Initial p" w ss q Ai j "New_Noninitial p1 \<gamma>1" "Some \<gamma>''" q' Aiminus1] t_def
      have "\<exists>u v u_ss v_ss.
              ss = u_ss @ v_ss \<and>
              w = u @ [Some \<gamma>''] @ v \<and>
              (Initial p, u, u_ss, New_Noninitial p1 \<gamma>1) \<in> LTS.transition_star_states Aiminus1 \<and>
              (New_Noninitial p1 \<gamma>1, [Some \<gamma>''], q') \<in> LTS.transition_star Ai \<and> (q', v, v_ss, q) \<in> LTS.transition_star_states Ai"
        using local.add_trans_push_2(1) local.add_trans_push_2(4) by blast
      then obtain u v u_ss v_ss where
           aaa: "ss = u_ss @ v_ss" and
           bbb: "w = u @ [Some \<gamma>''] @ v" and
           X_1: "(Initial p, u, u_ss, New_Noninitial p1 \<gamma>1) \<in> LTS.transition_star_states Aiminus1" and
           ccc: "(New_Noninitial p1 \<gamma>1, [Some \<gamma>''], q') \<in> LTS.transition_star Ai" and
           ddd: "(q', v, v_ss, q) \<in> LTS.transition_star_states Ai"
        by auto
      from step(3)[of p u u_ss "New_Noninitial p1 \<gamma>1"] X_1 have
        "(\<not>is_New_Noninitial (New_Noninitial p1 \<gamma>1) \<longrightarrow>
           (\<exists>p' w'. (Initial p', w', New_Noninitial p1 \<gamma>1) \<in> LTS_\<epsilon>.transition_star_\<epsilon> A \<and> (p', w') \<Rightarrow>\<^sup>* (p, LTS_\<epsilon>.remove_\<epsilon> u))) \<and>
         (is_New_Noninitial (New_Noninitial p1 \<gamma>1) \<longrightarrow> 
           (the_New_Ctr_Loc (New_Noninitial p1 \<gamma>1), [the_New_Label (New_Noninitial p1 \<gamma>1)]) \<Rightarrow>\<^sup>* (p, LTS_\<epsilon>.remove_\<epsilon> u))"
        using step.prems(1) step.prems(2) by auto 
      then have "(the_New_Ctr_Loc (New_Noninitial p1 \<gamma>1), [the_New_Label (New_Noninitial p1 \<gamma>1)]) \<Rightarrow>\<^sup>* (p, LTS_\<epsilon>.remove_\<epsilon> u)"
        by auto
      then have "(p1, [\<gamma>1]) \<Rightarrow>\<^sup>* (p, LTS_\<epsilon>.remove_\<epsilon> u)"
        by auto
      term \<gamma>2
      from IX have "\<exists>\<gamma>2\<epsilon> \<gamma>2ss. LTS_\<epsilon>.\<epsilon>_exp \<gamma>2\<epsilon> [\<gamma>2] \<and> (Initial p2, \<gamma>2\<epsilon>, \<gamma>2ss, q') \<in> LTS.transition_star_states Aiminus1"
        by (meson LTS.transition_star_transition_star_states LTS_\<epsilon>.transition_star_\<epsilon>_\<epsilon>_exp_transition_star)
      then obtain \<gamma>2\<epsilon> \<gamma>2ss where XI_1: "LTS_\<epsilon>.\<epsilon>_exp \<gamma>2\<epsilon> [\<gamma>2] \<and> (Initial p2, \<gamma>2\<epsilon>, \<gamma>2ss, q') \<in> LTS.transition_star_states Aiminus1"
        by blast
      have "(q', v, v_ss, q) \<in> LTS.transition_star_states Ai"
        by (simp add: \<open>(q', v, v_ss, q) \<in> LTS.transition_star_states Ai\<close>)
      have inddd:
        "(\<not>is_New_Noninitial q \<longrightarrow> (\<exists>p' w'. (Initial p', w', q) \<in> LTS_\<epsilon>.transition_star_\<epsilon> A \<and> (p', w') \<Rightarrow>\<^sup>* (p2, LTS_\<epsilon>.remove_\<epsilon> (\<gamma>2\<epsilon> @ v)))) \<and>
         (is_New_Noninitial q \<longrightarrow> (the_New_Ctr_Loc q, [the_New_Label q]) \<Rightarrow>\<^sup>* (p2, LTS_\<epsilon>.remove_\<epsilon> (\<gamma>2\<epsilon> @ v)))"
      proof -
        have one: "length \<gamma>2ss = Suc (length \<gamma>2\<epsilon>)"
          by (meson LTS.transition_star_states_length XI_1)
          
        have two: "v_ss \<noteq> []"
          by (metis LTS.transition_star_states.simps \<open>(q', v, v_ss, q) \<in> LTS.transition_star_states Ai\<close> list.distinct(1))
          
        have three: "last \<gamma>2ss = hd v_ss"
          by (metis LTS.transition_star_states_hd LTS.transition_star_states_last XI_1 \<open>(q', v, v_ss, q) \<in> LTS.transition_star_states Ai\<close>)


        have cv: "j = count (transitions_of ((v_ss, v))) t"
        proof -

          have a1: "New_Noninitial p1 \<gamma>1 = last u_ss"
            by (meson LTS.transition_star_states_last X_1)
          have a2: "q' = hd v_ss"
            by (meson LTS.transition_star_states_hd ddd)
          have a4: "Some \<gamma>'' # v = [Some \<gamma>''] @ v"
            by auto
          have a5: "New_Noninitial p1 \<gamma>1 = last u_ss \<and> q' = hd v_ss"
            using a1 a2 by blast

          have "count (transitions_of' (((Initial p, u, u_ss, New_Noninitial p1 \<gamma>1), Some \<gamma>'') @@\<^sup>\<gamma> (q', v, v_ss, q)))
                (New_Noninitial p1 \<gamma>1, Some \<gamma>'', q') =
                count (transitions_of' (Initial p, u, u_ss, New_Noninitial p1 \<gamma>1)) (New_Noninitial p1 \<gamma>1, Some \<gamma>'', q') +
                (if New_Noninitial p1 \<gamma>1 = last u_ss \<and> q' = hd v_ss \<and> Some \<gamma>'' = Some \<gamma>'' then 1 else 0) +
                count (transitions_of' (q', v, v_ss, q)) (New_Noninitial p1 \<gamma>1, Some \<gamma>'', q')"
            using count_append_transition_star_states_\<gamma>_length[of u_ss u v_ss "Initial p" "New_Noninitial p1 \<gamma>1" "Some \<gamma>''" q' v q "New_Noninitial p1 \<gamma>1" "Some \<gamma>''" q'] t_def aaa bbb X_1
            by (meson LTS.transition_star_states_length two)
          then have a3: "count (transitions_of (u_ss @ v_ss, u @ Some \<gamma>'' # v)) (last u_ss, Some \<gamma>'', hd v_ss) = Suc (count (transitions_of (u_ss, u)) (last u_ss, Some \<gamma>'', hd v_ss) + count (transitions_of (v_ss, v)) (last u_ss, Some \<gamma>'', hd v_ss))"
            using a1 a2 by auto
          have "j = count (transitions_of' ((q',v, v_ss, q))) t"
            using a1 a2 a3 X_1 aaa bbb add_trans_push_2(4) Suc(2)
              LTS.avoid_count_zero[of "Initial p" u u_ss "New_Noninitial p1 \<gamma>1" Aiminus1 "New_Noninitial p1 \<gamma>1" "Some \<gamma>''" q']
            by (auto simp: t_def)
          show "j = count (transitions_of ((v_ss, v))) t"
            using \<open>j = count (transitions_of' (q', v, v_ss, q)) t\<close> by force
        qed
        have "(Initial p2, \<gamma>2\<epsilon>, \<gamma>2ss, q') \<in> LTS.transition_star_states Aiminus1"
          using XI_1 by blast
        then have c\<gamma>2: "count (transitions_of (\<gamma>2ss, \<gamma>2\<epsilon>)) t = 0"
          using LTS.avoid_count_zero local.add_trans_push_2(4) t_def by fastforce
        have "j = count (transitions_of ((\<gamma>2ss, \<gamma>2\<epsilon>) @\<acute> (v_ss, v))) t"
          using LTS.count_append_path_with_word[of \<gamma>2ss \<gamma>2\<epsilon> v_ss v "New_Noninitial p1 \<gamma>1" "Some \<gamma>''" q'] t_def
            c\<gamma>2 cv one two three
          by force 

        have "j = count (transitions_of' (Initial p2, \<gamma>2\<epsilon> @ v, \<gamma>2ss @ tl v_ss, q)) t"
          by (simp add: \<open>j = count (transitions_of ((\<gamma>2ss, \<gamma>2\<epsilon>) @\<acute> (v_ss, v))) t\<close>)

        have "(\<gamma>2ss, \<gamma>2\<epsilon>) \<in> LTS.path_with_word Aiminus1"
          by (meson LTS.transition_star_states_path_with_word \<open>(Initial p2, \<gamma>2\<epsilon>, \<gamma>2ss, q') \<in> LTS.transition_star_states Aiminus1\<close>)
        then have gugugu: "(\<gamma>2ss, \<gamma>2\<epsilon>) \<in> LTS.path_with_word Ai"
          using add_trans_push_2(1) 
          path_with_word_mono'[of \<gamma>2ss \<gamma>2\<epsilon> Aiminus1 Ai] by auto

        have gugugu3: "last \<gamma>2ss = hd v_ss"
          using three by blast
        have gugugu2: "(v_ss, v) \<in> LTS.path_with_word Ai"
          by (meson LTS.transition_star_states_path_with_word \<open>(q', v, v_ss, q) \<in> LTS.transition_star_states Ai\<close>)
        have "(\<gamma>2ss, \<gamma>2\<epsilon>) @\<acute> (v_ss, v) \<in> LTS.path_with_word Ai"
          using gugugu gugugu2 LTS.append_path_with_word_path_with_word gugugu3
          by auto

        have "(\<gamma>2ss @ tl v_ss, \<gamma>2\<epsilon> @ v) \<in> LTS.path_with_word Ai"
          using \<open>(\<gamma>2ss, \<gamma>2\<epsilon>) @\<acute> (v_ss, v) \<in> LTS.path_with_word Ai\<close> by auto


        have "(Initial p2, \<gamma>2\<epsilon> @ v, \<gamma>2ss @ tl v_ss, q) \<in> LTS.transition_star_states Ai"
          by (metis (no_types, lifting) LTS.path_with_word_transition_star_states LTS.transition_star_states_append LTS.transition_star_states_hd XI_1 \<open>(q', v, v_ss, q) \<in> LTS.transition_star_states Ai\<close> gugugu three)
          
        from this Suc(1)[of p2 "\<gamma>2\<epsilon> @ v" "\<gamma>2ss @ tl v_ss" q]
        show
          "(\<not>is_New_Noninitial q \<longrightarrow> (\<exists>p' w'. (Initial p', w', q) \<in> LTS_\<epsilon>.transition_star_\<epsilon> A \<and> (p', w') \<Rightarrow>\<^sup>* (p2, LTS_\<epsilon>.remove_\<epsilon> (\<gamma>2\<epsilon> @ v)))) \<and>
           (is_New_Noninitial q \<longrightarrow> (the_New_Ctr_Loc q, [the_New_Label q]) \<Rightarrow>\<^sup>* (p2, LTS_\<epsilon>.remove_\<epsilon> (\<gamma>2\<epsilon> @ v)))"
          using \<open>j = count (transitions_of' (Initial p2, \<gamma>2\<epsilon> @ v, \<gamma>2ss @ tl v_ss, q)) t\<close> by fastforce
      qed

      show ?thesis
      proof (cases "is_Initial q \<or> is_Noninitial q")
        case True
        have "(\<exists>p' w'. (Initial p', w', q) \<in> LTS_\<epsilon>.transition_star_\<epsilon> A \<and> (p', w') \<Rightarrow>\<^sup>* (p2, LTS_\<epsilon>.remove_\<epsilon> (\<gamma>2\<epsilon> @ v)))"
          using True \<open>(\<not>is_New_Noninitial q \<longrightarrow> (\<exists>p' w'. (Initial p', w', q) \<in> LTS_\<epsilon>.transition_star_\<epsilon> A \<and> (p', w') \<Rightarrow>\<^sup>* (p2, LTS_\<epsilon>.remove_\<epsilon> (\<gamma>2\<epsilon> @ v)))) \<and> (is_New_Noninitial q \<longrightarrow> (the_New_Ctr_Loc q, [the_New_Label q]) \<Rightarrow>\<^sup>* (p2, LTS_\<epsilon>.remove_\<epsilon> (\<gamma>2\<epsilon> @ v)))\<close> by fastforce
        then obtain p' w' where "(Initial p', w', q) \<in> LTS_\<epsilon>.transition_star_\<epsilon> A \<and> (p', w') \<Rightarrow>\<^sup>* (p2, LTS_\<epsilon>.remove_\<epsilon> (\<gamma>2\<epsilon> @ v))"
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
          by (metis (no_types, lifting) Cons_eq_append_conv LTS_\<epsilon>.remove_\<epsilon>_Cons_tl LTS_\<epsilon>.remove_\<epsilon>_append_dist \<open>w = u @ [Some \<gamma>''] @ v\<close> hd_Cons_tl list.inject list.sel(1) list.simps(3) self_append_conv2)
          
        show ?thesis
          using True \<open>(p, LTS_\<epsilon>.remove_\<epsilon> u @ \<gamma>'' # LTS_\<epsilon>.remove_\<epsilon> v) = (p, LTS_\<epsilon>.remove_\<epsilon> w)\<close> \<open>(p1, \<gamma>1 # \<gamma>'' # LTS_\<epsilon>.remove_\<epsilon> v) \<Rightarrow>\<^sup>* (p, LTS_\<epsilon>.remove_\<epsilon> u @ \<gamma>'' # LTS_\<epsilon>.remove_\<epsilon> v)\<close> \<open>(p2, LTS_\<epsilon>.remove_\<epsilon> (\<gamma>2\<epsilon> @ v)) \<Rightarrow>\<^sup>* (p1, \<gamma>1 # \<gamma>'' # LTS_\<epsilon>.remove_\<epsilon> v)\<close> \<open>\<exists>p' w'. (Initial p', w', q) \<in> LTS_\<epsilon>.transition_star_\<epsilon> A \<and> (p', w') \<Rightarrow>\<^sup>* (p2, LTS_\<epsilon>.remove_\<epsilon> (\<gamma>2\<epsilon> @ v))\<close> by fastforce
      next
        case False
        then have "(the_New_Ctr_Loc q, [the_New_Label q]) \<Rightarrow>\<^sup>* (p2, LTS_\<epsilon>.remove_\<epsilon> (\<gamma>2\<epsilon> @ v))"
          using inddd state.exhaust_disc
          by blast
        have "(p2, LTS_\<epsilon>.remove_\<epsilon> (\<gamma>2\<epsilon> @ v))  \<Rightarrow>\<^sup>* (p1, \<gamma>1 # \<gamma>'' # LTS_\<epsilon>.remove_\<epsilon> v)"
          by (metis (mono_tags) LTS_\<epsilon>.\<epsilon>_exp_def LTS_\<epsilon>.remove_\<epsilon>_append_dist LTS_\<epsilon>.remove_\<epsilon>_def XIII XI_1 append_Cons append_Nil op_labels.simps(3) r_into_rtranclp step_relp_def2)
          
        have "(p1, \<gamma>1 # \<gamma>'' # LTS_\<epsilon>.remove_\<epsilon> v) \<Rightarrow>\<^sup>* (p, LTS_\<epsilon>.remove_\<epsilon> u @ \<gamma>'' # LTS_\<epsilon>.remove_\<epsilon> v)"
          by (metis \<open>(p1, [\<gamma>1]) \<Rightarrow>\<^sup>* (p, LTS_\<epsilon>.remove_\<epsilon> u)\<close> append_Cons append_Nil step_relp_append)
          
        have "(p, LTS_\<epsilon>.remove_\<epsilon> u @ \<gamma>'' # LTS_\<epsilon>.remove_\<epsilon> v) = (p, LTS_\<epsilon>.remove_\<epsilon> w)"
          by (metis LTS_\<epsilon>.remove_\<epsilon>_Cons_tl LTS_\<epsilon>.remove_\<epsilon>_append_dist append_Cons append_Nil bbb hd_Cons_tl list.distinct(1) list.inject)
          
        show ?thesis
          using False \<open>(p, LTS_\<epsilon>.remove_\<epsilon> u @ \<gamma>'' # LTS_\<epsilon>.remove_\<epsilon> v) = (p, LTS_\<epsilon>.remove_\<epsilon> w)\<close> \<open>(p1, \<gamma>1 # \<gamma>'' # LTS_\<epsilon>.remove_\<epsilon> v) \<Rightarrow>\<^sup>* (p, LTS_\<epsilon>.remove_\<epsilon> u @ \<gamma>'' # LTS_\<epsilon>.remove_\<epsilon> v)\<close> \<open>(p2, LTS_\<epsilon>.remove_\<epsilon> (\<gamma>2\<epsilon> @ v)) \<Rightarrow>\<^sup>* (p1, \<gamma>1 # \<gamma>'' # LTS_\<epsilon>.remove_\<epsilon> v)\<close> \<open>(the_New_Ctr_Loc q, [the_New_Label q]) \<Rightarrow>\<^sup>* (p2, LTS_\<epsilon>.remove_\<epsilon> (\<gamma>2\<epsilon> @ v))\<close>
          by (metis (no_types, lifting) inddd rtranclp_trans) 
      qed
    qed
  qed
qed

lemma lemma_3_4'':
  assumes "post_star_rules\<^sup>*\<^sup>* A A'"
  assumes "initials \<subseteq> LTS.sources A"
  assumes "\<forall>p \<gamma> q. (p, \<gamma>, q) \<in> A \<longrightarrow> p \<notin> New_Aut_states \<and> q \<notin> New_Aut_states"
  assumes "(Initial p, w, q) \<in> LTS.transition_star A'"
  shows "(\<not>is_New_Noninitial q \<longrightarrow> (\<exists>p' w'. (Initial p', w', q) \<in> LTS_\<epsilon>.transition_star_\<epsilon> A \<and> (p',w') \<Rightarrow>\<^sup>* (p, LTS_\<epsilon>.remove_\<epsilon> w))) \<and>
         (is_New_Noninitial q \<longrightarrow> (the_New_Ctr_Loc q, [the_New_Label q]) \<Rightarrow>\<^sup>* (p, LTS_\<epsilon>.remove_\<epsilon> w))"
  using lemma_3_4' assms by (metis LTS.transition_star_transition_star_states) 

lemma lemma_3_4:
  assumes "saturation post_star_rules A A'"
  assumes "initials \<subseteq> LTS.sources A"
  assumes "\<forall>p \<gamma> q. (p, \<gamma>, q) \<in> A \<longrightarrow> p \<notin> New_Aut_states \<and> q \<notin> New_Aut_states"
  assumes "(Initial p, w, q) \<in> LTS.transition_star A'"
  shows "(\<not>is_New_Noninitial q \<longrightarrow> (\<exists>p' w'. (Initial p', w', q) \<in> LTS_\<epsilon>.transition_star_\<epsilon> A \<and> (p',w') \<Rightarrow>\<^sup>* (p, LTS_\<epsilon>.remove_\<epsilon> w))) \<and>
         (is_New_Noninitial q \<longrightarrow> (the_New_Ctr_Loc q, [the_New_Label q]) \<Rightarrow>\<^sup>* (p, LTS_\<epsilon>.remove_\<epsilon> w))"
  using lemma_3_4'' assms saturation_def by metis

theorem theorem_3_3_on_the_fly:
  assumes "post_star_rules\<^sup>*\<^sup>* A A'"
  assumes "initials \<subseteq> LTS.sources A"
  assumes "\<forall>p \<gamma> q. (p, \<gamma>, q) \<in> A \<longrightarrow> p \<notin> New_Aut_states \<and> q \<notin> New_Aut_states"
  shows "{c. accepts_\<epsilon> A' c} \<subseteq> post_star (language_\<epsilon> A)"
proof
  fix c :: "('ctr_loc, 'label) conf"
  define p where "p = fst c"
  define w where "w = snd c"
  assume "c \<in>  {c. accepts_\<epsilon> A' c}"
  then have "accepts_\<epsilon> A' (p,w)"
    unfolding p_def w_def by auto
  then obtain q where q_p: "q \<in> finals" "(Initial p, w, q) \<in> LTS_\<epsilon>.transition_star_\<epsilon> A'" 
    unfolding accepts_\<epsilon>_def by auto
  then obtain w' where w'_def: "LTS_\<epsilon>.\<epsilon>_exp w' w \<and> (Initial p, w', q) \<in> LTS.transition_star A'"
    by (meson LTS_\<epsilon>.transition_star_\<epsilon>_iff_\<epsilon>_exp_transition_star)
  then have ttt: "(Initial p, w', q) \<in> LTS.transition_star A'"
    by auto
  have "\<not> is_New_Noninitial q"
    using F_not_Ext q_p(1) by blast
  then obtain p' w'a where "(Initial p', w'a, q) \<in> LTS_\<epsilon>.transition_star_\<epsilon> A \<and> (p', w'a) \<Rightarrow>\<^sup>* (p, LTS_\<epsilon>.remove_\<epsilon> w')"
    using lemma_3_4''[OF assms(1) assms(2) assms(3) ttt] by auto
  then have "(Initial p', w'a, q) \<in> LTS_\<epsilon>.transition_star_\<epsilon> A \<and> (p', w'a) \<Rightarrow>\<^sup>* (p, w)"
    using w'_def by (metis LTS_\<epsilon>.\<epsilon>_exp_def LTS_\<epsilon>.remove_\<epsilon>_def \<open>LTS_\<epsilon>.\<epsilon>_exp w' w \<and> (Initial p, w', q) \<in> LTS.transition_star A'\<close>)
  then have "(p,w) \<in> post_star (language_\<epsilon> A)"
    using \<open>q \<in> finals\<close> unfolding LTS.post_star_def accepts_\<epsilon>_def language_\<epsilon>_def by fastforce
  then show "c \<in> post_star (language_\<epsilon> A)"
    unfolding p_def w_def by auto
qed

\<comment> \<open>Corresponds to Schwoon's theorem 3.3\<close>
theorem post_star_rules_correct:
  assumes "saturation post_star_rules A A'"
  assumes  "initials \<subseteq> LTS.sources A"
  assumes "\<forall>p \<gamma> q. (p, \<gamma>, q) \<in> A \<longrightarrow> p \<notin> New_Aut_states \<and> q \<notin> New_Aut_states"
  shows "{c. accepts_\<epsilon> A' c} = post_star (language_\<epsilon> A)"
proof (rule; rule)
  fix c :: "('ctr_loc, 'label) conf"
  define p where "p = fst c"
  define w where "w = snd c"
  assume "c \<in> post_star (language_\<epsilon> A)"
  then obtain p' w' where "(p', w') \<Rightarrow>\<^sup>* (p, w) \<and> (p', w') \<in> language_\<epsilon> A"
    by (auto simp: post_star_def p_def w_def)
  then have "accepts_\<epsilon> A' (p, w)"
    using lemma_3_3[of p' w' p w A A'] assms(1) by auto 
  then have "accepts_\<epsilon> A' c"
    unfolding p_def w_def by auto
  then show "c \<in> {c. accepts_\<epsilon> A' c}"
    by auto
next
  fix c :: "('ctr_loc, 'label) conf" (* This proof is the same as theorem_3_3_on_the_fly *)
  define p where "p = fst c"
  define w where "w = snd c"
  assume "c \<in>  {c. accepts_\<epsilon> A' c}"
  then have "accepts_\<epsilon> A' (p,w)"
    unfolding p_def w_def by auto
  then obtain q where q_p: "q \<in> finals" "(Initial p, w, q) \<in> LTS_\<epsilon>.transition_star_\<epsilon> A'" 
    unfolding accepts_\<epsilon>_def by auto
  then obtain w' where w'_def: "LTS_\<epsilon>.\<epsilon>_exp w' w \<and> (Initial p, w', q) \<in> LTS.transition_star A'"
    by (meson LTS_\<epsilon>.transition_star_\<epsilon>_iff_\<epsilon>_exp_transition_star)
  then have ttt: "(Initial p, w', q) \<in> LTS.transition_star A'"
    by auto
  have "\<not> is_New_Noninitial q"
    using F_not_Ext q_p(1) by blast
  then obtain p' w'a where "(Initial p', w'a, q) \<in> LTS_\<epsilon>.transition_star_\<epsilon> A \<and> (p', w'a) \<Rightarrow>\<^sup>* (p, LTS_\<epsilon>.remove_\<epsilon> w')"
    using lemma_3_4[OF assms(1) assms(2) assms(3) ttt] by auto
  then have "(Initial p', w'a, q) \<in> LTS_\<epsilon>.transition_star_\<epsilon> A \<and> (p', w'a) \<Rightarrow>\<^sup>* (p, w)"
    using w'_def by (metis LTS_\<epsilon>.\<epsilon>_exp_def LTS_\<epsilon>.remove_\<epsilon>_def \<open>LTS_\<epsilon>.\<epsilon>_exp w' w \<and> (Initial p, w', q) \<in> LTS.transition_star A'\<close>)
  then have "(p,w) \<in> post_star (language_\<epsilon> A)"
    using \<open>q \<in> finals\<close> unfolding LTS.post_star_def accepts_\<epsilon>_def language_\<epsilon>_def by fastforce
  then show "c \<in> post_star (language_\<epsilon> A)"
    unfolding p_def w_def by auto
qed

\<comment> \<open>Corresponds to Schwoon's theorem 3.3\<close>
theorem post_star_rules_language_correct:
  assumes "saturation post_star_rules A A'"
  assumes "initials \<subseteq> LTS.sources A"
  assumes "\<forall>p \<gamma> q. (p, \<gamma>, q) \<in> A \<longrightarrow> p \<notin> New_Aut_states \<and> q \<notin> New_Aut_states"
  shows "language_\<epsilon> A' = post_star (language_\<epsilon> A)"
  using assms(1) assms(2) assms(3) language_\<epsilon>_def post_star_rules_correct by presburger

end

subsection \<open>Intersection Automata\<close>

definition accepts_inters :: "(('ctr_loc, 'noninitial, 'label) state * ('ctr_loc, 'noninitial, 'label) state, 'label) transition set \<Rightarrow> (('ctr_loc, 'noninitial, 'label) state * ('ctr_loc, 'noninitial, 'label) state) set \<Rightarrow> ('ctr_loc, 'label) conf \<Rightarrow> bool" where
  "accepts_inters ts finals \<equiv> \<lambda>(p,w). (\<exists>qq \<in> finals. ((Initial p, Initial p),w,qq) \<in> LTS.transition_star ts)"

lemma accepts_inters_accepts_aut_inters:
  assumes "ts12 = inters ts1 ts2"
  assumes "finals12 = inters_finals finals1 finals2"
  shows "accepts_inters ts12 finals12 (p,w) \<longleftrightarrow> Intersection_P_Automaton.accepts_aut_inters ts1 finals1 PDS_with_P_automata.initials ts2 finals2 (Initial p) w"
  by (simp add: Intersection_P_Automaton.accepts_aut_inters_def PDS_with_P_automata.initials_def P_Automaton.accepts_aut_def accepts_inters_def assms)

definition language_inters :: "(('ctr_loc, 'noninitial, 'label) state * ('ctr_loc, 'noninitial, 'label) state, 'label) transition set \<Rightarrow>  (('ctr_loc, 'noninitial, 'label) state * ('ctr_loc, 'noninitial, 'label) state) set \<Rightarrow> ('ctr_loc, 'label) conf set" where
  "language_inters ts finals = {c. accepts_inters ts finals c}"

lemma language_inters_language_aut_inters:
  assumes "ts12 = inters ts1 ts2"
  assumes "finals12 = inters_finals finals1 finals2"
  shows "(\<lambda>(p,w). (Initial p, w)) ` language_inters ts12 finals12 = Intersection_P_Automaton.language_aut_inters ts1 finals1 PDS_with_P_automata.initials ts2 finals2"
  using assms
  by (auto simp: Intersection_P_Automaton.language_aut_inters_def
    Intersection_P_Automaton.inters_accept_iff
    accepts_inters_accepts_aut_inters language_inters_def is_Initial_def
    PDS_with_P_automata.initials_def P_Automaton.accepts_aut_def image_iff)

thm Intersection_P_Automaton.transition_star_inter

thm Intersection_P_Automaton.inters_transition_star1

thm Intersection_P_Automaton.inters_transition_star

thm Intersection_P_Automaton.inters_transition_star_iff

thm Intersection_P_Automaton.inters_accept_iff

term PDS_with_P_automata.accepts

term PDS_with_P_automata.finals

lemma inters_accept_iff: 
  assumes "ts12 = inters ts1 ts2"
  assumes "finals12 = inters_finals (PDS_with_P_automata.finals final_initialss1 final_noninitials1) (PDS_with_P_automata.finals final_initialss2 final_noninitials2)"
  shows
  "accepts_inters ts12 finals12 (p,w) \<longleftrightarrow> 
     PDS_with_P_automata.accepts final_initialss1 final_noninitials1 ts1 (p,w) \<and> 
     PDS_with_P_automata.accepts final_initialss2 final_noninitials2 ts2 (p,w)"
  using accepts_inters_accepts_aut_inters Intersection_P_Automaton.inters_accept_iff assms
  by (simp add: Intersection_P_Automaton.inters_accept_iff accepts_inters_accepts_aut_inters PDS_with_P_automata.accepts_accepts_aut) 

lemma inters_language:
  assumes "ts12 = inters ts1 ts2"
  assumes "finals12 = inters_finals (PDS_with_P_automata.finals final_initialss1 final_noninitials1) (PDS_with_P_automata.finals final_initialss2 final_noninitials2)"
  shows "language_inters ts12 finals12 = PDS_with_P_automata.language final_initialss1 final_noninitials1 ts1 \<inter> PDS_with_P_automata.language final_initialss2 final_noninitials2 ts2"
  using assms by (auto simp add: PDS_with_P_automata.language_def inters_accept_iff language_inters_def)


subsection \<open>Intersection \<epsilon>-Automata\<close>

context PDS_with_P_automata begin

interpretation LTS transition_rel .
notation step_relp (infix "\<Rightarrow>" 80)
notation step_starp (infix "\<Rightarrow>\<^sup>*" 80)

(* TODO: Many lemmas here have moved into LTS. So they should NOT be repeated here! *)

definition accepts_\<epsilon>_inters :: "(('ctr_loc, 'noninitial, 'label) state * ('ctr_loc, 'noninitial, 'label) state, 'label option) transition set \<Rightarrow> ('ctr_loc, 'label) conf \<Rightarrow> bool" where
  "accepts_\<epsilon>_inters ts \<equiv> \<lambda>(p,w). (\<exists>q1 \<in> finals. \<exists>q2 \<in> finals. ((Initial p, Initial p),w,(q1,q2)) \<in> LTS_\<epsilon>.transition_star_\<epsilon> ts)"

definition language_\<epsilon>_inters :: "(('ctr_loc, 'noninitial, 'label) state * ('ctr_loc, 'noninitial, 'label) state, 'label option) transition set \<Rightarrow> ('ctr_loc, 'label) conf set" where
  "language_\<epsilon>_inters ts = {c. accepts_\<epsilon>_inters ts c}"

lemma transition_star_transition_star_\<epsilon>_inter:
  assumes "LTS_\<epsilon>.\<epsilon>_exp w1 w"
  assumes  "LTS_\<epsilon>.\<epsilon>_exp w2 w"
  assumes "(p1, w1, p2) \<in> LTS.transition_star ts1"
  assumes "(q1, w2, q2) \<in> LTS.transition_star ts2"
  shows "((p1,q1), w :: 'label list, (p2,q2)) \<in> LTS_\<epsilon>.transition_star_\<epsilon> (inters_\<epsilon> ts1 ts2)"
  using assms
proof (induction "length w1 + length w2" arbitrary: w1 w2 w p1 q1 rule: less_induct)
  case less
  then show ?case
  proof (cases "\<exists>\<alpha> w1' w2' \<beta>. w1=Some \<alpha>#w1' \<and> w2=Some \<beta>#w2'")
    case True
    from True obtain \<alpha> \<beta> w1' w2' where True'':
      "w1=Some \<alpha>#w1'"
      "w2=Some \<beta>#w2'"
      by auto
    have "\<alpha> = \<beta>"
      by (metis True''(1) True''(2) LTS_\<epsilon>.\<epsilon>_exp_Some_hd less.prems(1) less.prems(2))
    then have True':   
      "w1=Some \<alpha>#w1'"
      "w2=Some \<alpha>#w2'"
      using True'' by auto
    define w' where "w' = tl w"
    obtain p' where p'_p: "(p1, Some \<alpha>, p') \<in> ts1 \<and> (p', w1', p2) \<in> LTS.transition_star ts1"
      using less True'(1) by (metis LTS_\<epsilon>.transition_star_cons_\<epsilon>)
    obtain q' where q'_p: "(q1, Some \<alpha>, q') \<in> ts2 \<and>(q', w2', q2) \<in> LTS.transition_star ts2"
      using less True'(2) by (metis LTS_\<epsilon>.transition_star_cons_\<epsilon>) 
    have ind: "((p', q'), w', p2, q2) \<in> LTS_\<epsilon>.transition_star_\<epsilon> (inters_\<epsilon> ts1 ts2)"
    proof -
      have "length w1' + length w2' < length w1 + length w2"
        using True'(1) True'(2) by simp
      moreover
      have "LTS_\<epsilon>.\<epsilon>_exp w1' w'"
        by (metis (no_types) LTS_\<epsilon>.\<epsilon>_exp_def less(2) True'(1) list.map(2) list.sel(3) option.simps(3) removeAll.simps(2) w'_def)
      moreover
      have "LTS_\<epsilon>.\<epsilon>_exp w2' w'"
        by (metis (no_types) LTS_\<epsilon>.\<epsilon>_exp_def less(3) True'(2) list.map(2) list.sel(3) option.simps(3) removeAll.simps(2) w'_def)
      moreover
      have "(p', w1', p2) \<in> LTS.transition_star ts1"
        using p'_p by simp
      moreover
      have "(q', w2', q2) \<in> LTS.transition_star ts2"
        using q'_p by simp
      ultimately
      show "((p', q'), w', p2, q2) \<in> LTS_\<epsilon>.transition_star_\<epsilon> (inters_\<epsilon> ts1 ts2)"
        using less(1)[of w1' w2' w' p' q'] by auto
    qed
    moreover
    have "((p1, q1), Some \<alpha>, (p', q')) \<in> (inters_\<epsilon> ts1 ts2)"
      by (simp add: inters_\<epsilon>_def p'_p q'_p)
    ultimately
    have "((p1, q1), \<alpha>#w', p2, q2) \<in> LTS_\<epsilon>.transition_star_\<epsilon> (inters_\<epsilon> ts1 ts2)"
      by (meson LTS_\<epsilon>.transition_star_\<epsilon>.transition_star_\<epsilon>_step_\<gamma>)
    moreover
    have "length w > 0"
      using less(3) True' LTS_\<epsilon>.\<epsilon>_exp_Some_length by metis
    moreover
    have "hd w = \<alpha>"
      using less(3) True' LTS_\<epsilon>.\<epsilon>_exp_Some_hd by metis
    ultimately
    show ?thesis
      using w'_def by force
  next
    case False
    note False_outer_outer_outer_outer = False
    show ?thesis 
    proof (cases "w1 = [] \<and> w2 = []")
      term replicate
      case True
      then have same: "p1 = p2 \<and> q1 = q2"
        by (metis LTS.transition_star_empty less.prems(3) less.prems(4))
      have "w = []"
        using True less(2) LTS_\<epsilon>.exp_empty_empty by auto
      then show ?thesis
        using less True
        by (simp add: LTS_\<epsilon>.transition_star_\<epsilon>.transition_star_\<epsilon>_refl same)
    next
      case False
      note False_outer_outer_outer = False
      show ?thesis
      proof (cases "\<exists>w1'. w1=\<epsilon>#w1'")
        case True (* Adapted from above... maybe they can be merged....... *)
        then obtain w1' where True':
          "w1=\<epsilon>#w1'"
          by auto
        obtain p' where p'_p: "(p1, \<epsilon>, p') \<in> ts1 \<and> (p', w1', p2) \<in> LTS.transition_star ts1"
          using less True'(1) by (metis LTS_\<epsilon>.transition_star_cons_\<epsilon>)
        have q'_p: " (q1, w2, q2) \<in> LTS.transition_star ts2"
          using less by (metis) 
        have ind: "((p', q1), w, p2, q2) \<in> LTS_\<epsilon>.transition_star_\<epsilon> (inters_\<epsilon> ts1 ts2)"
        proof -
          have "length w1' + length w2 < length w1 + length w2"
            using True'(1) by simp
          moreover
          have "LTS_\<epsilon>.\<epsilon>_exp w1' w"
            by (metis (no_types) LTS_\<epsilon>.\<epsilon>_exp_def less(2) True'(1) removeAll.simps(2))
          moreover
          have "LTS_\<epsilon>.\<epsilon>_exp w2 w"
            by (metis (no_types) less(3))
          moreover
          have "(p', w1', p2) \<in> LTS.transition_star ts1"
            using p'_p by simp
          moreover
          have "(q1, w2, q2) \<in> LTS.transition_star ts2"
            using q'_p by simp
          ultimately
          show "((p', q1), w, p2, q2) \<in> LTS_\<epsilon>.transition_star_\<epsilon> (inters_\<epsilon> ts1 ts2)"
            using less(1)[of w1' w2 w p' q1] by auto
        qed
        moreover
        have "((p1, q1), \<epsilon>, (p', q1)) \<in> (inters_\<epsilon> ts1 ts2)"
          by (simp add: inters_\<epsilon>_def p'_p q'_p)
        ultimately
        have "((p1, q1), w, p2, q2) \<in> LTS_\<epsilon>.transition_star_\<epsilon> (inters_\<epsilon> ts1 ts2)"
          using LTS_\<epsilon>.transition_star_\<epsilon>.simps by fastforce
        then
        show ?thesis
           by force
      next
        case False
        note False_outer_outer = False
        then show ?thesis
        proof (cases "\<exists>w2'. w2 = \<epsilon> # w2'")
          case True (* Adapted from above... maybe they can be merged....... *)
          then obtain w2' where True':
            "w2=\<epsilon>#w2'"
            by auto
          have p'_p: "(p1, w1, p2) \<in> LTS.transition_star ts1"
            using less by (metis)
          obtain q' where q'_p: "(q1, \<epsilon>, q') \<in> ts2 \<and>(q', w2', q2) \<in> LTS.transition_star ts2"
            using less True'(1) by (metis LTS_\<epsilon>.transition_star_cons_\<epsilon>) 
          have ind: "((p1, q'), w, p2, q2) \<in> LTS_\<epsilon>.transition_star_\<epsilon> (inters_\<epsilon> ts1 ts2)"
          proof -
            have "length w1 + length w2' < length w1 + length w2"
              using True'(1) True'(1) by simp
            moreover
            have "LTS_\<epsilon>.\<epsilon>_exp w1 w"
              by (metis (no_types) less(2))
            moreover
            have "LTS_\<epsilon>.\<epsilon>_exp w2' w"
              by (metis (no_types) LTS_\<epsilon>.\<epsilon>_exp_def less(3) True'(1) removeAll.simps(2))
            moreover
            have "(p1, w1, p2) \<in> LTS.transition_star ts1"
              using p'_p by simp
            moreover
            have "(q', w2', q2) \<in> LTS.transition_star ts2"
              using q'_p by simp
            ultimately
            show "((p1, q'), w, p2, q2) \<in> LTS_\<epsilon>.transition_star_\<epsilon> (inters_\<epsilon> ts1 ts2)"
              using less(1)[of w1 w2' w p1 q'] by auto
          qed
          moreover
          have "((p1, q1), \<epsilon>, (p1, q')) \<in> (inters_\<epsilon> ts1 ts2)"
            by (simp add: inters_\<epsilon>_def p'_p q'_p)
          ultimately
          have "((p1, q1), w, p2, q2) \<in> LTS_\<epsilon>.transition_star_\<epsilon> (inters_\<epsilon> ts1 ts2)"
            using LTS_\<epsilon>.transition_star_\<epsilon>.simps by fastforce
          then
          show ?thesis
            by force
        next
          case False
          then have "(w1 = [] \<and> (\<exists>\<alpha> w2'. w2 = Some \<alpha> # w2')) \<or> ((\<exists>\<alpha> w1'. w1 = Some \<alpha> # w1') \<and> w2 = [])"
            using False_outer_outer False_outer_outer_outer False_outer_outer_outer_outer
            by (metis neq_Nil_conv option.exhaust_sel)
          then show ?thesis
            by (metis LTS_\<epsilon>.\<epsilon>_exp_def LTS_\<epsilon>.\<epsilon>_exp_Some_length less.prems(1) less.prems(2) less_numeral_extra(3) list.simps(8) list.size(3) removeAll.simps(1))
        qed
      qed
    qed
  qed
qed

lemma transition_star_\<epsilon>_inter:
  assumes "(p1, w :: 'label list, p2) \<in> LTS_\<epsilon>.transition_star_\<epsilon> ts1"
  assumes "(q1, w, q2) \<in> LTS_\<epsilon>.transition_star_\<epsilon> ts2"
  shows "((p1, q1), w, (p2, q2)) \<in> LTS_\<epsilon>.transition_star_\<epsilon> (inters_\<epsilon> ts1 ts2)"
proof -
  have "\<exists>w1'. LTS_\<epsilon>.\<epsilon>_exp w1' w \<and> (p1, w1', p2) \<in> LTS.transition_star ts1"
    using assms by (simp add: LTS_\<epsilon>.transition_star_\<epsilon>_\<epsilon>_exp_transition_star)
  then obtain w1' where "LTS_\<epsilon>.\<epsilon>_exp w1' w \<and> (p1, w1', p2) \<in> LTS.transition_star ts1"
    by auto
  moreover
  have "\<exists>w2'. LTS_\<epsilon>.\<epsilon>_exp w2' w \<and> (q1, w2', q2) \<in> LTS.transition_star ts2"
    using assms by (simp add: LTS_\<epsilon>.transition_star_\<epsilon>_\<epsilon>_exp_transition_star)
  then obtain w2' where "LTS_\<epsilon>.\<epsilon>_exp w2' w \<and> (q1, w2', q2) \<in> LTS.transition_star ts2"
    by auto
  ultimately
  show ?thesis
    using transition_star_transition_star_\<epsilon>_inter by metis
qed

lemma inters_transition_star_\<epsilon>1:
  assumes "(p1q2, w :: 'label list, p2q2) \<in> LTS_\<epsilon>.transition_star_\<epsilon> (inters_\<epsilon> ts1 ts2)"
  shows "(fst p1q2, w, fst p2q2) \<in> LTS_\<epsilon>.transition_star_\<epsilon> ts1"
  using assms 
proof (induction rule: LTS_\<epsilon>.transition_star_\<epsilon>.induct[OF assms(1)])
  case (1 p)
  then show ?case
    by (simp add: LTS_\<epsilon>.transition_star_\<epsilon>.transition_star_\<epsilon>_refl) 
next
  case (2 p \<gamma> q' w q)
  then have ind: "(fst q', w, fst q) \<in> LTS_\<epsilon>.transition_star_\<epsilon> ts1"
    by auto
  from 2(1) have "(p, Some \<gamma>, q') \<in> 
                     {((p1, q1), \<alpha>, p2, q2) |p1 q1 \<alpha> p2 q2. (p1, \<alpha>, p2) \<in> ts1 \<and> (q1, \<alpha>, q2) \<in> ts2} \<union> 
                     {((p1, q1), \<epsilon>, p2, q1) |p1 p2 q1. (p1, \<epsilon>, p2) \<in> ts1} \<union>
                     {((p1, q1), \<epsilon>, p1, q2) |p1 q1 q2. (q1, \<epsilon>, q2) \<in> ts1}"
    unfolding inters_\<epsilon>_def by auto
  moreover                
  {
    assume "(p, Some \<gamma>, q') \<in> {((p1, q1), \<alpha>, p2, q2) |p1 q1 \<alpha> p2 q2. (p1, \<alpha>, p2) \<in> ts1 \<and> (q1, \<alpha>, q2) \<in> ts2}"
    then have "\<exists>p1 q1. p = (p1, q1) \<and> (\<exists>p2 q2. q' = (p2, q2) \<and> (p1, Some \<gamma>, p2) \<in> ts1 \<and> (q1, Some \<gamma>, q2) \<in> ts2)"
      by simp
    then obtain p1 q1 where "p = (p1, q1) \<and> (\<exists>p2 q2. q' = (p2, q2) \<and> (p1, Some \<gamma>, p2) \<in> ts1 \<and> (q1, Some \<gamma>, q2) \<in> ts2)"
      by auto
    then have ?case
      using LTS_\<epsilon>.transition_star_\<epsilon>.transition_star_\<epsilon>_step_\<gamma> ind by fastforce
  }
  moreover
  {
    assume "(p, Some \<gamma>, q') \<in> {((p1, q1), \<epsilon>, p2, q1) |p1 p2 q1. (p1, \<epsilon>, p2) \<in> ts1}"
    then have ?case
      by auto
  }
  moreover
  {
    assume "(p, Some \<gamma>, q') \<in> {((p1, q1), \<epsilon>, p1, q2) |p1 q1 q2. (q1, \<epsilon>, q2) \<in> ts1}"
    then have ?case
      by auto
  }  
  ultimately 
  show ?case 
    by auto
next
  case (3 p q' w q)
  then have ind: "(fst q', w, fst q) \<in> LTS_\<epsilon>.transition_star_\<epsilon> ts1"
    by auto
  from 3(1) have "(p, \<epsilon>, q') \<in>
                     {((p1, q1), \<alpha>, (p2, q2)) | p1 q1 \<alpha> p2 q2. (p1, \<alpha>, p2) \<in> ts1 \<and> (q1, \<alpha>, q2) \<in> ts2} \<union>
                     {((p1, q1), \<epsilon>, (p2, q1)) | p1 p2 q1. (p1, \<epsilon>, p2) \<in> ts1} \<union>
                     {((p1, q1), \<epsilon>, (p1, q2)) | p1 q1 q2. (q1, \<epsilon>, q2) \<in> ts2}"
    unfolding inters_\<epsilon>_def by auto
  moreover                
  {
    assume "(p, \<epsilon>, q') \<in> {((p1, q1), \<alpha>, p2, q2) |p1 q1 \<alpha> p2 q2. (p1, \<alpha>, p2) \<in> ts1 \<and> (q1, \<alpha>, q2) \<in> ts2}"
    then have "\<exists>p1 q1. p = (p1, q1) \<and> (\<exists>p2 q2. q' = (p2, q2) \<and> (p1, \<epsilon>, p2) \<in> ts1 \<and> (q1, \<epsilon>, q2) \<in> ts2)"
      by simp
    then obtain p1 q1 where "p = (p1, q1) \<and> (\<exists>p2 q2. q' = (p2, q2) \<and> (p1, \<epsilon>, p2) \<in> ts1 \<and> (q1, \<epsilon>, q2) \<in> ts2)"
      by auto
    then have ?case
      using LTS_\<epsilon>.transition_star_\<epsilon>.transition_star_\<epsilon>_step_\<epsilon> ind by fastforce
  }
  moreover
  {
    assume "(p, \<epsilon>, q') \<in> {((p1, q1), \<epsilon>, p2, q1) |p1 p2 q1. (p1, \<epsilon>, p2) \<in> ts1}"
    then have "\<exists>p1 p2 q1. p = (p1, q1) \<and> q' = (p2, q1) \<and> (p1, \<epsilon>, p2) \<in> ts1"
      by auto
    then obtain p1 p2 q1 where "p = (p1, q1) \<and> q' = (p2, q1) \<and> (p1, \<epsilon>, p2) \<in> ts1"
      by auto
    then have ?case
      using LTS_\<epsilon>.transition_star_\<epsilon>.transition_star_\<epsilon>_step_\<epsilon> ind by fastforce
  }
  moreover
  {
    assume "(p, \<epsilon>, q') \<in> {((p1, q1), \<epsilon>, p1, q2) |p1 q1 q2. (q1, \<epsilon>, q2) \<in> ts2}"
    then have "\<exists>p1 q1 q2. p = (p1, q1) \<and> q' = (p1, q2) \<and> (q1, \<epsilon>, q2) \<in> ts2"
      by auto
    then obtain p1 q1 q2 where "p = (p1, q1) \<and> q' = (p1, q2) \<and> (q1, \<epsilon>, q2) \<in> ts2"
      by auto
    then have ?case
      using LTS_\<epsilon>.transition_star_\<epsilon>.transition_star_\<epsilon>_step_\<epsilon> ind by fastforce
  }  
  ultimately 
  show ?case 
    by auto
qed

lemma inters_transition_star_\<epsilon>:
  assumes "(p1q2, w :: 'label list, p2q2) \<in> LTS_\<epsilon>.transition_star_\<epsilon> (inters_\<epsilon> ts1 ts2)"
  shows "(snd p1q2, w, snd p2q2) \<in> LTS_\<epsilon>.transition_star_\<epsilon> ts2"
  using assms 
proof (induction rule: LTS_\<epsilon>.transition_star_\<epsilon>.induct[OF assms(1)])
  case (1 p)
  then show ?case
    by (simp add: LTS_\<epsilon>.transition_star_\<epsilon>.transition_star_\<epsilon>_refl) 
next
  case (2 p \<gamma> q' w q)
  then have ind: "(snd q', w, snd q) \<in> LTS_\<epsilon>.transition_star_\<epsilon> ts2"
    by auto
  from 2(1) have "(p, Some \<gamma>, q') \<in> 
                     {((p1, q1), \<alpha>, p2, q2) |p1 q1 \<alpha> p2 q2. (p1, \<alpha>, p2) \<in> ts1 \<and> (q1, \<alpha>, q2) \<in> ts2} \<union> 
                     {((p1, q1), \<epsilon>, p2, q1) |p1 p2 q1. (p1, \<epsilon>, p2) \<in> ts1} \<union>
                     {((p1, q1), \<epsilon>, p1, q2) |p1 q1 q2. (q1, \<epsilon>, q2) \<in> ts2}"
    unfolding inters_\<epsilon>_def by auto
  moreover                
  {
    assume "(p, Some \<gamma>, q') \<in> {((p1, q1), \<alpha>, p2, q2) |p1 q1 \<alpha> p2 q2. (p1, \<alpha>, p2) \<in> ts1 \<and> (q1, \<alpha>, q2) \<in> ts2}"
    then have "\<exists>p1 q1. p = (p1, q1) \<and> (\<exists>p2 q2. q' = (p2, q2) \<and> (p1, Some \<gamma>, p2) \<in> ts1 \<and> (q1, Some \<gamma>, q2) \<in> ts2)"
      by simp
    then obtain p1 q1 where "p = (p1, q1) \<and> (\<exists>p2 q2. q' = (p2, q2) \<and> (p1, Some \<gamma>, p2) \<in> ts1 \<and> (q1, Some \<gamma>, q2) \<in> ts2)"
      by auto
    then have ?case
      using LTS_\<epsilon>.transition_star_\<epsilon>.transition_star_\<epsilon>_step_\<gamma> ind by fastforce
  }
  moreover
  {
    assume "(p, Some \<gamma>, q') \<in> {((p1, q1), \<epsilon>, p2, q1) |p1 p2 q1. (p1, \<epsilon>, p2) \<in> ts1}"
    then have ?case
      by auto
  }
  moreover
  {
    assume "(p, Some \<gamma>, q') \<in> {((p1, q1), \<epsilon>, p1, q2) |p1 q1 q2. (q1, \<epsilon>, q2) \<in> ts2}"
    then have ?case
      by auto
  }  
  ultimately 
  show ?case 
    by auto
next
  case (3 p q' w q)
  then have ind: "(snd q', w, snd q) \<in> LTS_\<epsilon>.transition_star_\<epsilon> ts2"
    by auto
  from 3(1) have "(p, \<epsilon>, q') \<in>
                     {((p1, q1), \<alpha>, (p2, q2)) | p1 q1 \<alpha> p2 q2. (p1, \<alpha>, p2) \<in> ts1 \<and> (q1, \<alpha>, q2) \<in> ts2} \<union>
                     {((p1, q1), \<epsilon>, (p2, q1)) | p1 p2 q1. (p1, \<epsilon>, p2) \<in> ts1} \<union>
                     {((p1, q1), \<epsilon>, (p1, q2)) | p1 q1 q2. (q1, \<epsilon>, q2) \<in> ts2}"
    unfolding inters_\<epsilon>_def by auto
  moreover                
  {
    assume "(p, \<epsilon>, q') \<in> {((p1, q1), \<alpha>, p2, q2) |p1 q1 \<alpha> p2 q2. (p1, \<alpha>, p2) \<in> ts1 \<and> (q1, \<alpha>, q2) \<in> ts2}"
    then have "\<exists>p1 q1. p = (p1, q1) \<and> (\<exists>p2 q2. q' = (p2, q2) \<and> (p1, \<epsilon>, p2) \<in> ts1 \<and> (q1, \<epsilon>, q2) \<in> ts2)"
      by simp
    then obtain p1 q1 where "p = (p1, q1) \<and> (\<exists>p2 q2. q' = (p2, q2) \<and> (p1, \<epsilon>, p2) \<in> ts1 \<and> (q1, \<epsilon>, q2) \<in> ts2)"
      by auto
    then have ?case
      using LTS_\<epsilon>.transition_star_\<epsilon>.transition_star_\<epsilon>_step_\<epsilon> ind by fastforce
  }
  moreover
  {
    assume "(p, \<epsilon>, q') \<in> {((p1, q1), \<epsilon>, p2, q1) |p1 p2 q1. (p1, \<epsilon>, p2) \<in> ts1}"
    then have "\<exists>p1 p2 q1. p = (p1, q1) \<and> q' = (p2, q1) \<and> (p1, \<epsilon>, p2) \<in> ts1"
      by auto
    then obtain p1 p2 q1 where "p = (p1, q1) \<and> q' = (p2, q1) \<and> (p1, \<epsilon>, p2) \<in> ts1"
      by auto
    then have ?case
      using LTS_\<epsilon>.transition_star_\<epsilon>.transition_star_\<epsilon>_step_\<epsilon> ind by fastforce
  }
  moreover
  {
    assume "(p, \<epsilon>, q') \<in> {((p1, q1), \<epsilon>, p1, q2) |p1 q1 q2. (q1, \<epsilon>, q2) \<in> ts2}"
    then have "\<exists>p1 q1 q2. p = (p1, q1) \<and> q' = (p1, q2) \<and> (q1, \<epsilon>, q2) \<in> ts2"
      by auto
    then obtain p1 q1 q2 where "p = (p1, q1) \<and> q' = (p1, q2) \<and> (q1, \<epsilon>, q2) \<in> ts2"
      by auto
    then have ?case
      using LTS_\<epsilon>.transition_star_\<epsilon>.transition_star_\<epsilon>_step_\<epsilon> ind by fastforce
  }
  ultimately
  show ?case
    by auto
qed

lemma inters_transition_star_\<epsilon>_iff:
  "((p1,q2), w :: 'label list, (p2,q2)) \<in> LTS_\<epsilon>.transition_star_\<epsilon> (inters_\<epsilon> ts1 ts2) \<longleftrightarrow> (p1, w, p2) \<in> LTS_\<epsilon>.transition_star_\<epsilon> ts1 \<and> (q2, w, q2) \<in> LTS_\<epsilon>.transition_star_\<epsilon> ts2"
  by (metis fst_conv inters_transition_star_\<epsilon> inters_transition_star_\<epsilon>1 snd_conv transition_star_\<epsilon>_inter)

lemma inters_\<epsilon>_accept_\<epsilon>_iff: "accepts_\<epsilon>_inters (inters_\<epsilon> ts1 ts2) c \<longleftrightarrow> accepts_\<epsilon> ts1 c \<and> accepts_\<epsilon> ts2 c"
proof
  assume "accepts_\<epsilon>_inters (inters_\<epsilon> ts1 ts2) c"
  then show "accepts_\<epsilon> ts1 c \<and> accepts_\<epsilon> ts2 c"
    using accepts_\<epsilon>_def accepts_\<epsilon>_inters_def inters_transition_star_\<epsilon> inters_transition_star_\<epsilon>1 by fastforce
next
  assume a: "accepts_\<epsilon> ts1 c \<and> accepts_\<epsilon> ts2 c"
  define p where "p = fst c"
  define w where "w = snd c"

  from a have "accepts_\<epsilon> ts1 (p,w) \<and> accepts_\<epsilon> ts2 (p,w)"
    using p_def w_def by auto


  then have "(\<exists>q\<in>finals. (Initial p, w, q) \<in> LTS_\<epsilon>.transition_star_\<epsilon> ts1) \<and> (\<exists>q\<in>finals. (Initial p, w, q) \<in> LTS_\<epsilon>.transition_star_\<epsilon> ts2)" 
    unfolding accepts_\<epsilon>_def by auto
  then show "accepts_\<epsilon>_inters (inters_\<epsilon> ts1 ts2) c"
    using accepts_\<epsilon>_inters_def p_def transition_star_\<epsilon>_inter w_def by fastforce
qed

lemma inters_\<epsilon>_language_\<epsilon>: "language_\<epsilon>_inters (inters_\<epsilon> ts1 ts2) = language_\<epsilon> ts1 \<inter> language_\<epsilon> ts2"
  unfolding language_\<epsilon>_inters_def language_\<epsilon>_def using inters_\<epsilon>_accept_\<epsilon>_iff by auto


subsection \<open>Dual search\<close>

lemma dual1: "post_star (language_\<epsilon> A1) \<inter> pre_star (language A2) = {c. \<exists>c1 \<in> language_\<epsilon> A1. \<exists>c2 \<in> language A2. c1 \<Rightarrow>\<^sup>* c \<and> c \<Rightarrow>\<^sup>* c2}"
proof -
  have "post_star (language_\<epsilon> A1) \<inter> pre_star (language A2) = {c. c \<in> post_star (language_\<epsilon> A1) \<and> c \<in> pre_star (language A2)}"
    by auto
  moreover
  have "... = {c. (\<exists>c1 \<in> language_\<epsilon> A1. c1 \<Rightarrow>\<^sup>* c) \<and> (\<exists>c2 \<in> language A2. c \<Rightarrow>\<^sup>* c2)}"
    unfolding post_star_def pre_star_def by auto
  moreover
  have "... = {c. \<exists>c1 \<in> language_\<epsilon> A1. \<exists>c2 \<in> language A2. c1 \<Rightarrow>\<^sup>* c \<and> c \<Rightarrow>\<^sup>* c2}"
    by auto
  ultimately
  show ?thesis by metis
qed

lemma dual2: "post_star (language_\<epsilon> A1) \<inter> pre_star (language A2) \<noteq> {} \<longleftrightarrow> (\<exists>c1 \<in> language_\<epsilon> A1. \<exists>c2 \<in> language A2. c1 \<Rightarrow>\<^sup>* c2)"
proof (rule)
  assume "post_star (language_\<epsilon> A1) \<inter> pre_star (language A2) \<noteq> {}"
  then show "\<exists>c1\<in>language_\<epsilon> A1. \<exists>c2\<in>language A2. c1 \<Rightarrow>\<^sup>* c2"
    by (auto simp: pre_star_def post_star_def intro: rtranclp_trans)
next
  assume "\<exists>c1\<in>language_\<epsilon> A1. \<exists>c2\<in>language A2. c1 \<Rightarrow>\<^sup>* c2"
  then show "post_star (language_\<epsilon> A1) \<inter> pre_star (language A2) \<noteq> {}"
    using dual1 by auto
qed

lemma LTS_\<epsilon>_of_LTS_Some: "(p, Some \<gamma>, q') \<in> LTS_\<epsilon>_of_LTS A2' \<longleftrightarrow> (p, \<gamma>, q') \<in> A2'"
  unfolding LTS_\<epsilon>_of_LTS_def \<epsilon>_edge_of_edge_def by (auto simp add: rev_image_eqI)

lemma LTS_\<epsilon>_of_LTS_None: "(p, None, q') \<notin> LTS_\<epsilon>_of_LTS A2'"
  unfolding LTS_\<epsilon>_of_LTS_def \<epsilon>_edge_of_edge_def by (auto)

lemma transition_star_\<epsilon>_LTS_\<epsilon>_of_LTS_transition_star:
  assumes "(p,w,q) \<in> LTS_\<epsilon>.transition_star_\<epsilon> (LTS_\<epsilon>_of_LTS A2')"
  shows "(p,w,q) \<in> LTS.transition_star A2'"
  using assms
proof (induction rule: LTS_\<epsilon>.transition_star_\<epsilon>.induct[OF assms(1)] )
  case (1 p)
  then show ?case
    by (simp add: LTS.transition_star.transition_star_refl)
next
  case (2 p \<gamma> q' w q)
  moreover
  have "(p, \<gamma>, q') \<in> A2'"
    using 2(1) using LTS_\<epsilon>_of_LTS_Some by metis
  moreover
  have "(q', w, q) \<in> LTS.transition_star A2'"
    using "2.IH" 2(2) by auto
  ultimately show ?case
    by (meson LTS.transition_star.transition_star_step)
next
  case (3 p q' w q)
  then show ?case
    using LTS_\<epsilon>_of_LTS_None by fastforce
qed

lemma transition_star_transition_star_\<epsilon>_LTS_\<epsilon>_of_LTS:
  assumes "(p,w,q) \<in> LTS.transition_star A2'"
  shows "(p,w,q) \<in> LTS_\<epsilon>.transition_star_\<epsilon> (LTS_\<epsilon>_of_LTS A2')"
  using assms
proof (induction rule: LTS.transition_star.induct[OF assms(1)])
  case (1 p)
  then show ?case
    by (simp add: LTS_\<epsilon>.transition_star_\<epsilon>.transition_star_\<epsilon>_refl)
next
  case (2 p \<gamma> q' w q)
  then show ?case
    by (meson LTS_\<epsilon>.transition_star_\<epsilon>.transition_star_\<epsilon>_step_\<gamma> LTS_\<epsilon>_of_LTS_Some)
qed


lemma accepts_\<epsilon>_LTS_\<epsilon>_of_LTS_iff_accepts: "accepts_\<epsilon> (LTS_\<epsilon>_of_LTS A2') (p, w) \<longleftrightarrow> accepts A2' (p, w)"
  using accepts_\<epsilon>_def accepts_def transition_star_\<epsilon>_LTS_\<epsilon>_of_LTS_transition_star transition_star_transition_star_\<epsilon>_LTS_\<epsilon>_of_LTS by fastforce

lemma language_\<epsilon>_LTS_\<epsilon>_of_LTS_is_language: "language_\<epsilon> (LTS_\<epsilon>_of_LTS A2') = language A2'"
  unfolding language_\<epsilon>_def language_def using accepts_\<epsilon>_LTS_\<epsilon>_of_LTS_iff_accepts by auto

theorem dual3_on_the_fly:
  assumes "initials \<subseteq> LTS.sources A1"
  assumes "initials \<subseteq> LTS.sources A2"
  assumes "\<forall>p \<gamma> q. (p, \<gamma>, q) \<in> A1 \<longrightarrow> p \<notin> New_Aut_states \<and> q \<notin> New_Aut_states"
  assumes "\<forall>p \<gamma> q. (p, \<gamma>, q) \<in> A2 \<longrightarrow> p \<notin> New_Aut_states \<and> q \<notin> New_Aut_states"
  assumes "post_star_rules\<^sup>*\<^sup>* A1 A1'"
  assumes "pre_star_rule\<^sup>*\<^sup>* A2 A2'"
  assumes "language_\<epsilon>_inters (inters_\<epsilon> A1' (LTS_\<epsilon>_of_LTS A2')) \<noteq> {}"
  shows "\<exists>c1 \<in> language_\<epsilon> A1. \<exists>c2 \<in> language A2. c1 \<Rightarrow>\<^sup>* c2"
proof -
  have "{c. accepts_\<epsilon> A1' c} \<subseteq> post_star (language_\<epsilon> A1)"
    using theorem_3_3_on_the_fly[of A1 A1'] assms by auto
  then have A1'_correct: "language_\<epsilon> A1' \<subseteq> post_star (language_\<epsilon> A1)"
    unfolding language_\<epsilon>_def by auto

  have "{c. accepts A2' c} \<subseteq> pre_star (language A2)" 
    using theorem_3_2_on_the_fly[of A2 A2'] assms by auto
  then have A2'_correct: "language A2' \<subseteq> pre_star (language A2)" 
    unfolding language_def by auto

  have "language_\<epsilon>_inters (inters_\<epsilon> A1' (LTS_\<epsilon>_of_LTS A2')) = language_\<epsilon> A1' \<inter> language_\<epsilon> (LTS_\<epsilon>_of_LTS A2')"
    using inters_\<epsilon>_language_\<epsilon>[of A1' "(LTS_\<epsilon>_of_LTS A2')"] by auto
  moreover
  have "... = language_\<epsilon> A1' \<inter> language A2'"
    using language_\<epsilon>_LTS_\<epsilon>_of_LTS_is_language by auto
  moreover
  have "... \<subseteq> post_star (language_\<epsilon> A1) \<inter> pre_star (language A2)"
    using A1'_correct A2'_correct by auto
  ultimately
  have inters_correct: "language_\<epsilon>_inters (inters_\<epsilon> A1' (LTS_\<epsilon>_of_LTS A2')) \<subseteq> post_star (language_\<epsilon> A1) \<inter> pre_star (language A2)"
    by metis

  from assms(7) have "post_star (language_\<epsilon> A1) \<inter> pre_star (language A2) \<noteq> {}"
    using inters_correct by auto
  then show "\<exists>c1\<in>language_\<epsilon> A1. \<exists>c2\<in>language A2. c1 \<Rightarrow>\<^sup>* c2"
    using dual2 by auto

qed

theorem dual3:
  assumes "initials \<subseteq> LTS.sources A1"
  assumes "initials \<subseteq> LTS.sources A2"
  assumes "\<forall>p \<gamma> q. (p, \<gamma>, q) \<in> A1 \<longrightarrow> p \<notin> New_Aut_states \<and> q \<notin> New_Aut_states"
  assumes "\<forall>p \<gamma> q. (p, \<gamma>, q) \<in> A2 \<longrightarrow> p \<notin> New_Aut_states \<and> q \<notin> New_Aut_states"
  assumes "saturation post_star_rules A1 A1'"
  assumes "saturation pre_star_rule A2 A2'"
  shows "language_\<epsilon>_inters (inters_\<epsilon> A1' (LTS_\<epsilon>_of_LTS A2')) \<noteq> {} \<longleftrightarrow> (\<exists>c1 \<in> language_\<epsilon> A1. \<exists>c2 \<in> language A2. c1 \<Rightarrow>\<^sup>* c2)"
proof -
  have "{c. accepts_\<epsilon> A1' c} = post_star (language_\<epsilon> A1)"
    using post_star_rules_correct[of A1 A1'] assms by auto
  then have A1'_correct: "language_\<epsilon> A1' = post_star (language_\<epsilon> A1)"
    unfolding language_\<epsilon>_def by auto

  have "{c. accepts A2' c} = pre_star (language A2)" 
    using pre_star_rules_correct[of A2 A2'] assms by auto
  then have A2'_correct: "language A2' = pre_star (language A2)" 
    unfolding language_def by auto

  have "language_\<epsilon>_inters (inters_\<epsilon> A1' (LTS_\<epsilon>_of_LTS A2')) = language_\<epsilon> A1' \<inter> language_\<epsilon> (LTS_\<epsilon>_of_LTS A2')"
    using inters_\<epsilon>_language_\<epsilon>[of A1' "(LTS_\<epsilon>_of_LTS A2')"] by auto
  moreover
  have "... = language_\<epsilon> A1' \<inter> language A2'"
    using language_\<epsilon>_LTS_\<epsilon>_of_LTS_is_language by auto
  moreover
  have "... = post_star (language_\<epsilon> A1) \<inter> pre_star (language A2)"
    using A1'_correct A2'_correct by auto
  ultimately
  have inters_correct: "language_\<epsilon>_inters (inters_\<epsilon> A1' (LTS_\<epsilon>_of_LTS A2')) = post_star (language_\<epsilon> A1) \<inter> pre_star (language A2)"
    by metis

  show ?thesis
  proof 
    assume "language_\<epsilon>_inters (inters_\<epsilon> A1' (LTS_\<epsilon>_of_LTS A2')) \<noteq> {}"
    then have "post_star (language_\<epsilon> A1) \<inter> pre_star (language A2) \<noteq> {}"
      using inters_correct by auto
    then show "\<exists>c1\<in>language_\<epsilon> A1. \<exists>c2\<in>language A2. c1 \<Rightarrow>\<^sup>* c2"
      using dual2 by auto
  next
    assume "\<exists>c1\<in>language_\<epsilon> A1. \<exists>c2\<in>language A2. c1 \<Rightarrow>\<^sup>* c2"
    then have "post_star (language_\<epsilon> A1) \<inter> pre_star (language A2) \<noteq> {}"
      using dual2 by auto
    then show "language_\<epsilon>_inters (inters_\<epsilon> A1' (LTS_\<epsilon>_of_LTS A2')) \<noteq> {}"
      using inters_correct by auto
  qed
qed

theorem dual4_on_the_fly:
  assumes "initials \<subseteq> LTS.sources A1"
  assumes "initials \<subseteq> LTS.sources A2"
  assumes "\<forall>p \<gamma> q. (p, \<gamma>, q) \<in> A1 \<longrightarrow> p \<notin> New_Aut_states \<and> q \<notin> New_Aut_states"
  assumes "\<forall>p \<gamma> q. (p, \<gamma>, q) \<in> A2 \<longrightarrow> p \<notin> New_Aut_states \<and> q \<notin> New_Aut_states"
  assumes "language_\<epsilon> A1 = {c1}"
  assumes "language A2 = {c2}"
  assumes "post_star_rules\<^sup>*\<^sup>* A1 A1'"
  assumes "pre_star_rule\<^sup>*\<^sup>* A2 A2'"
  assumes "language_\<epsilon>_inters (inters_\<epsilon> A1' (LTS_\<epsilon>_of_LTS A2')) \<noteq> {}"
  shows "c1 \<Rightarrow>\<^sup>* c2"
  using dual3_on_the_fly[OF assms(1,2,3,4) assms(7,8,9)] assms(5,6) by auto

theorem dual4:
  assumes "initials \<subseteq> LTS.sources A1"
  assumes "initials \<subseteq> LTS.sources A2"
  assumes "\<forall>p \<gamma> q. (p, \<gamma>, q) \<in> A1 \<longrightarrow> p \<notin> New_Aut_states \<and> q \<notin> New_Aut_states"
  assumes "\<forall>p \<gamma> q. (p, \<gamma>, q) \<in> A2 \<longrightarrow> p \<notin> New_Aut_states \<and> q \<notin> New_Aut_states"
  assumes "language_\<epsilon> A1 = {c1}"
  assumes "language A2 = {c2}"
  assumes "saturation post_star_rules A1 A1'"
  assumes "saturation pre_star_rule A2 A2'"
  shows "language_\<epsilon>_inters (inters_\<epsilon> A1' (LTS_\<epsilon>_of_LTS A2')) \<noteq> {} \<longleftrightarrow> c1 \<Rightarrow>\<^sup>* c2"
  using assms dual3 by auto

end

end
