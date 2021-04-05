theory PDS imports Main Nested_Multisets_Ordinals.Multiset_More begin


section \<open>LTS\<close>

type_synonym ('state, 'label) transition = "'state * 'label * 'state"

locale LTS =
  fixes transition_relation :: "('state, 'label) transition set"
begin

text \<open>More definitions.\<close>

definition step_relp  :: "'state \<Rightarrow> 'state \<Rightarrow> bool" (infix "\<Rightarrow>" 80) where
  "c \<Rightarrow> c' \<equiv> \<exists>l. (c, l, c') \<in> transition_relation"

abbreviation step_starp (infix "\<Rightarrow>\<^sup>*" 80) where
  "c \<Rightarrow>\<^sup>* c' == step_relp\<^sup>*\<^sup>* c c'"

definition step_rel :: "'state rel" where 
  "step_rel \<equiv> {(c, c'). step_relp c c'}"

definition step_star :: "'state rel" where 
  "step_star \<equiv> {(c, c'). step_starp c c'}"

abbreviation
  step_star_trans ("(_\<Rightarrow>\<^sup>*_\<Rightarrow>\<^sup>*_)" 80) where 
  "c \<Rightarrow>\<^sup>* c' \<Rightarrow>\<^sup>* c'' \<equiv> (c \<Rightarrow>\<^sup>* c') \<and> (c' \<Rightarrow>\<^sup>* c'')"

(* For a set of states C, post*(C) is the set of all states reachable from C. *)
definition post_star :: "'state set \<Rightarrow> 'state set" where
  "post_star C \<equiv> {c'. \<exists>c \<in> C. c \<Rightarrow>\<^sup>* c'}"

(* And pre*(C) is the set of all states that can reach a state in C. *)
definition pre_star :: "'state set \<Rightarrow> 'state set" where
  "pre_star C \<equiv> {c'. \<exists>c \<in> C. c' \<Rightarrow>\<^sup>* c}"

(* Paths as defined in the thesis: *)
inductive_set path :: "'state list set" where
  "[s] \<in> path"
| "(s'#ss) \<in> path \<Longrightarrow> (s,l,s') \<in> transition_relation \<Longrightarrow> s#s'#ss \<in> path"


(* Labeled paths as defined in the thesis *)
inductive_set lpath :: "('state * 'label list * 'state) set" where
  lpath_refl[iff]: "(p, [], p) \<in> lpath"
| lpath_step: "(p,\<gamma>,q') \<in> transition_relation \<Longrightarrow> (q',w,q) \<in> lpath
                           \<Longrightarrow> (p, \<gamma>#w, q) \<in> lpath"

inductive_cases lpath_empty [elim]: "(p, [], q) \<in> lpath"
inductive_cases lpath_cons: "(p, \<gamma>#w, q) \<in> lpath"

inductive_set path_with_word where
  path_with_word_refl''[iff]: "(p,[],[p],p) \<in> path_with_word"
| lpath_step: "(p,\<gamma>,q') \<in> transition_relation \<Longrightarrow> (q',w,ss,q) \<in> path_with_word
                           \<Longrightarrow> (p, \<gamma>#w, p#ss, q) \<in> path_with_word"

inductive_set path_with_word''' :: "('state list * 'label list) set" where
  path_with_word_refl[iff]: "([s],[]) \<in> path_with_word'''"
| path_with_word_step: "(s'#ss, w) \<in> path_with_word''' \<Longrightarrow> (s,l,s') \<in> transition_relation \<Longrightarrow> (s#s'#ss,l#w) \<in> path_with_word'''" 

inductive transition_of :: "('state, 'label) transition \<Rightarrow> 'state list * 'label list \<Rightarrow> bool" where
  "transition_of (s1,\<gamma>,s2) (s1#s2#ss, \<gamma>#w)"
| "transition_of (s1,\<gamma>,s2) (ss, w) \<Longrightarrow> transition_of (s1,\<gamma>,s2) (s#ss, \<mu>#w)"

definition path_with_word' where
  "path_with_word' == {(p,w,ss,q) | p w ss q. (ss,w) \<in> path_with_word''' \<and> p = hd ss \<and> q = last ss}"

lemma path_with_word_induct_non_empty_word: "(x10, x20, x30, x40) \<in> path_with_word \<Longrightarrow> x20 \<noteq> [] \<Longrightarrow>
(\<And>p \<gamma> q'. (p, \<gamma>, q') \<in> transition_relation \<Longrightarrow> P p [\<gamma>] [p, q'] q') \<Longrightarrow>
(\<And>p \<gamma> q' w ss q. (p, \<gamma>, q') \<in> transition_relation \<Longrightarrow> w \<noteq> [] \<Longrightarrow> (q', w, ss, q) \<in> path_with_word \<Longrightarrow> P q' w ss q \<Longrightarrow> P p (\<gamma> # w) (p # ss) q) \<Longrightarrow> P x10 x20 x30 x40"
proof (induction rule: path_with_word.induct)
  case (path_with_word_refl'' p)
  then show ?case by auto
next
  case (lpath_step p \<gamma> q' w ss q)
  then show ?case
    by (smt (verit, ccfv_SIG) list.distinct(1) path_with_word.cases)
qed
                                                  
lemma path_with_word_not_empty[simp]: "\<not>([],w) \<in> path_with_word'''"
  using path_with_word'''.cases by force
  

lemma lpath_path_with_word''':
  assumes "(p, w, q) \<in> lpath"
  shows "\<exists>ss. hd ss = p \<and> last ss = q \<and> (ss, w) \<in> path_with_word'''"
  using assms
proof (induction rule: lpath.inducts)
  case (lpath_refl p)
  then show ?case
    by (meson LTS.path_with_word'''.path_with_word_refl last.simps list.sel(1))
next
  case (lpath_step p \<gamma> q' w q)
  then show ?case
    by (metis LTS.path_with_word'''.simps hd_Cons_tl last_ConsR list.discI list.sel(1))
qed

lemma lpath_path_with_word':
  assumes "(p, w, q) \<in> lpath"
  shows "\<exists>ss. (p, w, ss, q) \<in> path_with_word'"
  using assms lpath_path_with_word''' unfolding path_with_word'_def by force

lemma lpath_path_with_word:
  assumes "(p, w, q) \<in> lpath"
  shows "\<exists>ss. (p, w, ss, q) \<in> path_with_word"
  using assms 
proof (induction rule: lpath.induct)
  case (lpath_refl p)
  then show ?case by auto
next
  case (lpath_step p \<gamma> q' w q)
  then show ?case
    by (meson LTS.path_with_word.lpath_step)
qed

lemma path_with_word'''_lpath:
  assumes "(ss, w) \<in> path_with_word'''"
  assumes "length ss \<noteq> 0"
  shows "(hd ss, w, last ss) \<in> lpath"
  using assms
proof (induction rule: path_with_word'''.inducts)
  case (path_with_word_refl s)
  show ?case
    by simp 
next
  case (path_with_word_step s' ss w s l)
  then show ?case
    using LTS.lpath.lpath_step by fastforce
qed

lemma path_with_word_lpath_Cons:
  assumes "(s1#ss@[s2], w) \<in> path_with_word'''"
  shows "(s1, w, s2) \<in> lpath"
  using assms path_with_word'''_lpath by force 

lemma path_with_word_lpath_Singleton:
  assumes "([s2], w) \<in> path_with_word'''"
  shows "(s2, [], s2) \<in> lpath"
  using assms path_with_word'''_lpath by force



(* TODO: Prove correspondences between path and lpath. *)


lemma lpath_split:
  assumes "(p'', u1 @ w1, q) \<in> lpath"
  shows "\<exists>q1. (p'', u1, q1) \<in> lpath \<and> (q1, w1, q) \<in> lpath"
using assms proof(induction u1 arbitrary: p'')
  case Nil
  then show ?case by auto
next
  case (Cons a u1)
  then show ?case
    by (metis LTS.lpath.lpath_step LTS.lpath_cons append_Cons)
qed

end

fun transitions_of :: "'state list * 'label list \<Rightarrow> ('state, 'label) transition multiset" where
  "transitions_of (s1#s2#ss, \<gamma>#w) = {# (s1, \<gamma>, s2) #} + transitions_of (s2#ss, w)"
| "transitions_of ([s1],_) = {#}"
| "transitions_of ([],_) = {#}"
| "transitions_of (_,[]) = {#}"

fun transitions_of' where
  "transitions_of' (p,w,ss,q) = transitions_of (ss, w)"

lemma LTS_lpath_mono:
  "mono LTS.lpath"
proof (rule, rule)
  fix pwq :: "'a \<times> 'b list \<times> 'a"
  fix ts ts' :: "('a, 'b) transition set"
  assume sub: "ts \<subseteq> ts'"
  assume awb_ts: "pwq \<in> LTS.lpath ts"
  then obtain p w q where pwq_p: "pwq = (p, w, q)"
    using prod_cases3 by blast
  then have "(p, w, q) \<in> LTS.lpath ts"
    using awb_ts by auto
  then have "(p, w, q) \<in>  LTS.lpath ts'"
  proof(induction w arbitrary: p)
    case Nil
    then show ?case
      by (metis LTS.lpath.lpath_refl LTS.lpath_empty)
  next
    case (Cons \<gamma> w)
    then show ?case
      by (meson LTS.lpath.simps LTS.lpath_cons sub subsetD)
  qed
  then show "pwq \<in> LTS.lpath ts'"
    unfolding pwq_p .
qed

section\<open>LTS init\<close>

locale LTS_init = LTS transition_relation for transition_relation :: "('state, 'label) transition set" +
  fixes r :: 'state
begin

abbreviation initial where "initial == (\<lambda>r'. r' = r)"

end

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
  "x \<hookrightarrow> y \<equiv> (x,y) \<in> \<Delta>"

inductive_set transition_rel :: "(('ctr_loc, 'label) conf \<times> 'label \<times> ('ctr_loc, 'label) conf) set" where
  "(p, \<gamma>) \<hookrightarrow> (p', w) \<Longrightarrow> ((p, \<gamma>#w'), \<gamma>, (p', (op_labels w)@w')) \<in> transition_rel"

interpretation LTS_init transition_rel c0 .

(* BEGIN "IMPORT NOTATION" *)
abbreviation step_relp' (infix "\<Rightarrow>" 80) where
  "c \<Rightarrow> c' \<equiv> step_relp c c'"

abbreviation step_starp' (infix "\<Rightarrow>\<^sup>*" 80) where
  "step_starp' == step_relp\<^sup>*\<^sup>*"
(* END "IMPORT NOTATION" *)

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

definition accepts :: "('ctr_loc \<times> 'label \<times> 'ctr_loc) set \<Rightarrow> 'ctr_loc \<times> 'label list \<Rightarrow> bool" where
  "accepts ts \<equiv> \<lambda>(p,w). (\<exists>q \<in> F_locs. (p,w,q) \<in> LTS.lpath ts)"
  (* Here acceptance is defined for any p, but in the paper p has to be in P_locs *)

lemma accepts_mono[mono]: "mono accepts" (* Hmm.. what does this actually mean? *)
proof (rule, rule)
  fix c :: "('ctr_loc, 'label) conf"
  fix ts ts' :: "('ctr_loc, 'label) transition set"
  assume accepts_xa: "accepts ts c"
  assume tsts': "ts \<subseteq> ts'"
  obtain p l where pl_p: "c = (p,l)"
    by (cases c)
  obtain q where q_p:  "q \<in> F_locs \<and> (p, l, q) \<in> LTS.lpath ts"
    using accepts_xa unfolding pl_p accepts_def by auto
  then have "(p, l, q) \<in> LTS.lpath ts'"
    using tsts' LTS_lpath_mono monoD by blast 
  then have "accepts ts' (p,l)"
    unfolding accepts_def using q_p by auto
  then show "accepts ts' c"
    unfolding pl_p .
qed

lemma accepts_cons: "(p, \<gamma>, q) \<in> ts \<Longrightarrow> accepts ts (q, w) \<Longrightarrow> accepts ts (p, \<gamma> # w)"
  using LTS.lpath.lpath_step accepts_def PDS_with_P_automaton_axioms by fastforce

lemma accepts_unfold: "accepts ts (p, \<gamma> # w) \<Longrightarrow> \<exists>q. (p, \<gamma>, q) \<in> ts \<and> accepts ts (q, w)"
  using LTS.lpath_cons accepts_def case_prod_conv by force 

lemma accepts_unfoldn: "accepts ts (p, w' @ w) \<Longrightarrow> \<exists>q. (p, w', q) \<in> LTS.lpath ts \<and> accepts ts (q, w)"
proof (induct w' arbitrary: p w)
  case Nil
  then show ?case by (metis LTS.lpath.lpath_refl append_Nil)
next
  case (Cons a w')
  then show ?case by (metis LTS.lpath.lpath_step accepts_unfold append_Cons)
qed

lemma accepts_append: "(p, w', q) \<in> LTS.lpath ts \<Longrightarrow> accepts ts (q, w) \<Longrightarrow> accepts ts (p, w' @ w)"
proof (induct w' arbitrary: w p q)
  case Nil
  then show ?case 
    by (metis LTS.lpath_empty append_Nil)
next
  case (Cons a w')
  then show ?case 
    by (metis LTS.lpath_cons accepts_cons append_Cons)
qed

definition language :: "('ctr_loc, 'label) transition set \<Rightarrow> ('ctr_loc, 'label) conf set" where
  "language ts = {c. accepts ts c}"


subsection \<open>pre star\<close>

inductive saturation_rule :: "('ctr_loc, 'label) transition set \<Rightarrow> ('ctr_loc, 'label) transition set \<Rightarrow> bool" where (* TODO: p' should also be in P_locs I guess... *)
  add_trans: "(p, \<gamma>) \<hookrightarrow> (p', w) \<Longrightarrow> p \<in> P_locs \<Longrightarrow> (p', op_labels w, q) \<in> LTS.lpath ts \<Longrightarrow> (p, \<gamma>, q) \<notin> ts \<Longrightarrow> saturation_rule ts (ts \<union> {(p, \<gamma>, q)})"

lemma saturation_rule_mono:
  "saturation_rule ts ts' \<Longrightarrow> ts \<subset> ts'"
  unfolding saturation_rule.simps by auto

definition saturated :: "('ctr_loc, 'label) transition set \<Rightarrow> bool" where
  "saturated ts \<longleftrightarrow> (\<nexists>ts'. saturation_rule ts ts')"

definition saturation :: "('ctr_loc, 'label) transition set \<Rightarrow> ('ctr_loc, 'label) transition set \<Rightarrow> bool" where
  "saturation ts ts' \<longleftrightarrow> saturation_rule\<^sup>*\<^sup>* ts ts' \<and> saturated ts'"

lemma saturation_rule_card_Suc: "saturation_rule ts ts' \<Longrightarrow> card ts' = Suc (card ts)"
  unfolding saturation_rule.simps by auto

lemma no_infinite: (* Maybe lazy lists are better? *)
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

lemma saturation_termination: (* Maybe lazy lists are better? *)
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

TODO: Prove that saturations are unique. (Priority 2)

TODO: Prove more theorems from the book. (Priority 1)

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

lemma pre_star'_incr_lpath:
  "saturation_rule\<^sup>*\<^sup>* A A' \<Longrightarrow> LTS.lpath A \<subseteq> LTS.lpath A'"
  using mono_def LTS_lpath_mono saturation_rtranclp_rule_incr by metis

lemma pre_star_lim'_incr_lpath:
  "saturation A A' \<Longrightarrow> LTS.lpath A \<subseteq> LTS.lpath A'"
  by (simp add: pre_star'_incr_lpath saturation_def)

lemma lemma_3_1:
  assumes "p'w \<Rightarrow>\<^sup>* pv"
    and "pv \<in> language A"
    and "saturation A A'"
  shows "accepts A' p'w"
  using assms
proof (induct rule: converse_rtranclp_induct)
  case base
  then have "\<exists>q \<in> F_locs. (fst pv, snd pv, q) \<in> LTS.lpath A'"
    unfolding language_def using pre_star_lim'_incr_lpath accepts_def by fastforce 
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
  then obtain q where q_p: "q \<in> F_locs \<and> (p'', u, q) \<in> LTS.lpath A'"
    unfolding accepts_def using p''_def u_def by auto
  then have "(p'', u, q) \<in> LTS.lpath A'"
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

  have ffff: "p' \<in> P_locs"
    using p''u_def p'w_def step.hyps(1) step_relp'_P_locs1 by auto

  have "\<exists>q1. (p'', op_labels u1, q1) \<in> LTS.lpath A' \<and> (q1, w1, q) \<in> LTS.lpath A'"
    using q_p \<gamma>_w1_u1_p LTS.lpath_split by auto

  then obtain q1 where q1_p: "(p'', op_labels u1, q1) \<in> LTS.lpath A' \<and> (q1, w1, q) \<in> LTS.lpath A'"
    by auto

  then have in_A': "(p', \<gamma>, q1) \<in> A'"
    using \<gamma>_w1_u1_p 
    using add_trans[of p' \<gamma> p'' u1 q1 A'] 
    using step.prems(2)
    using saturated_def
    using saturation_def[of ]
    using step.prems
    using ffff
    by blast
    


  then have "(p', \<gamma>#w1, q) \<in> LTS.lpath A'"
    using in_A' lpath_step q1_p
    by (meson LTS.lpath.lpath_step)
  then have t_in_A': "(p', w, q) \<in> LTS.lpath A'"
    using \<gamma>_w1_u1_p by blast

  from q_p t_in_A' have "q \<in> F_locs \<and> (p', w, q) \<in> LTS.lpath A'"
    using p'_def w_def by auto
  then show ?case
    unfolding accepts_def p'w_def using q_p by auto 
qed

lemma lemma_3_2_base: 
  "(p, w, q) \<in> LTS.lpath rel \<Longrightarrow> \<exists>p' w'. (p, w) \<Rightarrow>\<^sup>* (p', w') \<and> (p', w', q) \<in> LTS.lpath rel"
  by auto

lemma saturation_rule_mono': "t \<in> LTS.lpath rel \<Longrightarrow> saturation_rule rel rel' \<Longrightarrow> t \<in> LTS.lpath (rel')"
  using pre_star'_incr_lpath by blast

lemma lemma_3_2_b_aux': (* Morten's lemma *)
  assumes "(p, w, q) \<in> LTS.lpath A"
  assumes "\<nexists>q \<gamma> q'. (q, \<gamma>, q') \<in> A \<and> q' \<in> P_locs"
  assumes "q \<in> P_locs"
  shows "w = [] \<and> p = q"
  using assms(2,3)
proof(induction rule: LTS.lpath.induct[of p w q A,OF assms(1)]) (* Strange induction. Why "OF"? *)
  case (1 p)
  show ?case by auto
next
  case (2 p \<gamma> q' w q)
  then show ?case by blast
qed

lemma lemma_3_2_b_aux''': (* Morten's lemma 3*) (* Should this say something about ss also? *)
  assumes "(p, w, ss, q) \<in> LTS.path_with_word A"
  assumes "\<nexists>q \<gamma> q'. (q, \<gamma>, q') \<in> A \<and> q' \<in> P_locs"
  assumes "q \<in> P_locs"
  shows "w = [] \<and> p = q"
  using assms 
proof(induction rule: LTS.path_with_word.induct[OF assms(1)])
  case (1 p)
  then show ?case by auto
next
  case (2 p \<gamma> q' w ss q)
  then show ?case by auto
qed

lemma count_next_0:
  assumes "count (transitions_of (s # s' # ss, l # w)) (p1, \<gamma>, q') = 0"
  shows "count (transitions_of (s' # ss, w)) (p1, \<gamma>, q') = 0"
  using assms by (cases "s = p1 \<and> l = \<gamma> \<and> s' = q'") auto




lemma count_next_hd:
  assumes "count (transitions_of (s # s' # ss, l # w)) (p1, \<gamma>, q') = 0"
  shows "(s, l, s') \<noteq> (p1, \<gamma>, q')"
  using assms by auto
  

lemma lemma_3_2_a'_Aux:
  assumes "(ss, w) \<in> LTS.path_with_word''' Ai"
  assumes "0 = count (transitions_of (ss, w)) (p1, \<gamma>, q')"
  assumes "Ai = Aiminus1 \<union> {(p1, \<gamma>, q')}"
  shows "(ss, w) \<in> LTS.path_with_word''' Aiminus1"
  using assms
proof (induction rule: LTS.path_with_word'''.induct[OF assms(1)])
  case (1 s)
  then show ?case
    by (simp add: LTS.path_with_word'''.path_with_word_refl)
next
  case (2 s' ss w s l)
  from 2(5) have "0 = count (transitions_of (s' # ss, w)) (p1, \<gamma>, q')"
    using count_next_0 by auto
  then have x: "(s' # ss, w) \<in> LTS.path_with_word''' Aiminus1"
    using 2 by auto
  have "(s, l, s') \<in> Aiminus1"
    using 2(2,5) assms(3) by force
  then show ?case 
    using x by (simp add: LTS.path_with_word'''.path_with_word_step) 
qed

lemma lemma_3_2_a'_Aux_2:
  assumes "(p, w, ss ,q) \<in> LTS.path_with_word' Ai"
  assumes "0 = count (transitions_of' (p, w, ss, q)) (p1, \<gamma>, q')"
  assumes "Ai = Aiminus1 \<union> {(p1, \<gamma>, q')}"
  shows "(p, w, ss, q) \<in> LTS.path_with_word' Aiminus1"
  using assms apply auto
  unfolding LTS.path_with_word'_def
  apply auto
  using lemma_3_2_a'_Aux[of ss w _ p1 \<gamma> q' _] assms(2) assms(3)
  apply auto
  done

lemma count_empty_zero: "count (transitions_of' (p, [], [p_add], p_add)) (p1, \<gamma>, q') = 0"
  by simp

lemma ajskdlfjsla:
  assumes "(p, \<gamma>', q'_add) \<noteq> (p1, \<gamma>, q')"
  shows "count (transitions_of' (p, \<gamma>' # w, p # q'_add # ss_rest, q)) (p1, \<gamma>, q') = count (transitions_of' (q'_add, w, q'_add # ss_rest, q)) (p1, \<gamma>, q')"
  apply (cases w)
  subgoal
    using assms
    apply auto
    done
  subgoal 
    using assms 
    apply -
    apply auto
    done
  done

lemma lemma_3_2_a'_Aux_3: (* This proof is a mess. Better start over. *)
  assumes "(p, w, ss ,q) \<in> LTS.path_with_word Ai"
  assumes "0 = count (transitions_of' (p, w, ss, q)) (p1, \<gamma>, q')"
  assumes "Ai = Aiminus1 \<union> {(p1, \<gamma>, q')}"
  shows "(p, w, ss, q) \<in> LTS.path_with_word Aiminus1"
  using assms
proof (induction arbitrary: p rule: LTS.path_with_word.induct[OF assms(1)])
  case (1 p)
  then show ?case
    by (metis LTS.path_with_word.simps list.distinct(1))
next
  case (2 p' \<gamma>' q'' w ss q)
  have ppp: "p' = p"
    by (meson "2.prems"(1) LTS.path_with_word.cases list.inject)
  { 
    assume a: "length ss > 0" 
    have xxx: "(p, \<gamma>', hd ss) \<noteq> (p1, \<gamma>, q')"
      using LTS.path_with_word.cases count_next_hd list.sel(1) transitions_of'.simps
      using 2(4) 2(5) by (metis a hd_Cons_tl length_greater_0_conv) 
    have hdAI: "(p, \<gamma>', hd ss) \<in> Ai"
      by (metis "2.hyps"(1) "2.hyps"(2) LTS.path_with_word.cases list.sel(1) ppp)
    have t: "(p, \<gamma>', hd ss) \<in> Aiminus1"
      using 2 hdAI xxx by force 
    have "(p, \<gamma>' # w, p' # ss, q) \<in> LTS.path_with_word (Aiminus1 \<union> {(p1, \<gamma>, q')})"
      using "2.prems"(1) assms(3) by fastforce
    have f7: "hd ss # tl ss = ss"
      using a hd_Cons_tl by blast
    moreover
    have "(hd ss, w, ss, q) \<in> LTS.path_with_word Ai"
      using f7 "2.hyps"(2) using LTS.path_with_word.cases
      by (metis list.sel(1))
    ultimately have "(hd ss, w, ss, q) \<in> LTS.path_with_word Aiminus1"
      using f7 using "2.IH" "2.prems"(2) xxx ajskdlfjsla assms(3) by (smt (z3) ppp)
    from this t have ?case
      using LTS.path_with_word.intros(2)[of p \<gamma>' "hd ss" Aiminus1 w ss q] using ppp by auto
  }
  moreover
  { 
    assume "length ss = 0"
    then have ?case
      using "2.hyps"(2) LTS.path_with_word.cases by force
  }
  ultimately show ?case
    by auto
qed


lemma guuggugugugugugugugugu:
  assumes "(p, w, ss, q) \<in> LTS.path_with_word Ai"
  assumes "Suc j' = count (transitions_of' (p, w, ss, q)) (p1, \<gamma>, q')"
  assumes "(p1, \<gamma>, q') \<notin> Aiminus1"
  assumes "Ai = Aiminus1 \<union> {(p1, \<gamma>, q')}"
  shows "\<exists>u v u_ss v_ss. ss = u_ss @ v_ss \<and> w = u @ [\<gamma>] @ v \<and> (p, u, u_ss, p1) \<in> LTS.path_with_word Aiminus1 \<and> (p1, [\<gamma>], q') \<in> LTS.lpath Ai \<and> (q', v, v_ss, q) \<in> LTS.path_with_word Ai"
  using assms
proof(induction arbitrary: p rule: LTS.path_with_word.induct[OF assms(1)])
  case (1 p_add p)
  from 1(2) have "False"
    using count_empty_zero by auto
  then show ?case
    by auto
next
  case (2 p_add \<gamma>' q'_add w ss q p)
  then have p_add_p: "p_add = p"
    by (meson LTS.path_with_word.cases list.inject)
  from p_add_p have f2_1: "(p, \<gamma>', q'_add) \<in> Ai"
    using 2(1) by auto
  from p_add_p have f2_4: "(p, \<gamma>' # w, p # ss, q) \<in> LTS.path_with_word Ai"
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
    have "(p, u, u_ss, p1) \<in> LTS.path_with_word Aiminus1"
      using f2 unfolding u_def u_ss_def using LTS.path_with_word.intros
      using True by fastforce 
    have "(p1, [\<gamma>], q') \<in> LTS.lpath Ai"
      using f2_1
      by (metis LTS.lpath.lpath_refl LTS.lpath.lpath_step True) 
    have "(q', v, v_ss, q) \<in> LTS.path_with_word Ai"
      using f2(2)
      using True v_def v_ss_def by blast
    show ?thesis
      by (metis (no_types, lifting) Pair_inject True \<open>(p, u, u_ss, p1) \<in> LTS.path_with_word Aiminus1\<close> \<open>(p1, [\<gamma>], q') \<in> LTS.lpath Ai\<close> \<open>(q', v, v_ss, q) \<in> LTS.path_with_word Ai\<close> append_Cons p_add_p self_append_conv2 u_def u_ss_def v_def v_ss_def)
  next
    case False
    have "hd ss = q'_add"
      by (metis LTS.path_with_word.cases f2(2) list.sel(1))
    from this False have g: "Suc j' = count (transitions_of' (q'_add, w, ss, q)) (p1, \<gamma>, q')"
      using f2(5)  
      apply (cases ss)
      using ajskdlfjsla
       apply auto
      done
    have "\<exists>u_ih v_ih u_ss_ih v_ss_ih. ss = u_ss_ih @ v_ss_ih \<and> w = u_ih @ [\<gamma>] @ v_ih \<and> (q'_add, u_ih, u_ss_ih, p1) \<in> LTS.path_with_word Aiminus1 \<and> (p1, [\<gamma>], q') \<in> LTS.lpath Ai \<and> (q', v_ih, v_ss_ih, q) \<in> LTS.path_with_word Ai"
      using f2(3)[of q'_add, OF f2(2) g f2(6) f2(7)] .
    then obtain u_ih v_ih u_ss_ih v_ss_ih where ppp:
      "ss = u_ss_ih @ v_ss_ih" 
      "w = u_ih @ [\<gamma>] @ v_ih"
      "(q'_add, u_ih, u_ss_ih, p1) \<in> LTS.path_with_word Aiminus1" 
      "(p1, [\<gamma>], q') \<in> LTS.lpath Ai" 
      "(q', v_ih, v_ss_ih, q) \<in> LTS.path_with_word Ai"
      by metis
    define v where "v = v_ih"
    define v_ss where "v_ss = v_ss_ih"
    define u where "u = \<gamma>' # u_ih"
    define u_ss where "u_ss = p # u_ss_ih"
    have "p_add # ss = u_ss @ v_ss"
      by (simp add: p_add_p ppp(1) u_ss_def v_ss_def)
    have "\<gamma>' # w = u @ [\<gamma>] @ v"
      using ppp(2) u_def v_def by auto
    have "(p, u, u_ss, p1) \<in> LTS.path_with_word Aiminus1"
      using False LTS.path_with_word.lpath_step f2(7) f2_1 ppp(3) u_def u_ss_def by fastforce
    have "(p1, [\<gamma>], q') \<in> LTS.lpath Ai"
      by (simp add: ppp(4))
    have "(q', v, v_ss, q) \<in> LTS.path_with_word Ai"
      by (simp add: ppp(5) v_def v_ss_def)
    show ?thesis
      apply (rule_tac x=u in exI)
      apply (rule_tac x=v in exI)
      apply (rule_tac x=u_ss in exI)
      apply (rule_tac x=v_ss in exI)
      using \<open>(p, u, u_ss, p1) \<in> LTS.path_with_word Aiminus1\<close> \<open>(q', v, v_ss, q) \<in> LTS.path_with_word Ai\<close> \<open>\<gamma>' # w = u @ [\<gamma>] @ v\<close> \<open>p_add # ss = u_ss @ v_ss\<close> ppp(4) by blast
  qed
qed


(*


  case (1 p'' \<gamma>'' q'')
  then show ?case
    apply (cases "(p'', \<gamma>'', q'') = (p1, \<gamma>, q')")
    subgoal
      apply (rule_tac x="[]" in exI)
      apply (rule_tac x="[]" in exI)
      apply (rule_tac x="[p'']" in exI)
      apply (rule_tac x="[q'']" in exI)
      apply rule
      subgoal
        apply auto 
        done
      subgoal
        apply rule
        subgoal
          apply auto
          done
        subgoal
          apply rule
          subgoal
            apply (simp add: LTS.path_with_word.path_with_word_refl'')
            done
          subgoal
            apply rule
            subgoal
              apply (metis LTS.lpath.lpath_refl LTS.lpath.lpath_step)
              done
            subgoal
              apply (simp add: LTS.path_with_word.path_with_word_refl'')
              done
            done
          done
        done
      done
    subgoal
      apply (subgoal_tac "(p'', \<gamma>'', q'') \<in> Aiminus1")
      subgoal

        apply (rule_tac x="[]" in exI)
        apply (rule_tac x="[]" in exI)
        apply (rule_tac x="[]" in exI)
        apply (rule_tac x="[]" in exI)
        sorry
      subgoal
        apply blast
        done
    done
  
next
  case (2 p \<gamma> q' w ss q)
  then show ?case sorry
qed *)


lemma lemma_3_2_a':
  assumes "\<nexists>q \<gamma> q'. (q, \<gamma>, q') \<in> A \<and> q' \<in> P_locs"
  assumes "saturation_rule\<^sup>*\<^sup>* A A'"
  assumes "(p, w, ss, q) \<in> LTS.path_with_word A'"
  shows "\<exists>p' w' ss'. (p', w', ss', q) \<in> LTS.path_with_word A \<and> (p, w) \<Rightarrow>\<^sup>* (p', w')"
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
    "(p2, op_labels w2, q') \<in> LTS.lpath Aiminus1"
    "(p1, \<gamma>, q') \<notin> Aiminus1"
    "p1 \<in> P_locs"
    by (meson saturation_rule.cases)

  note ss_p = step(5)

  define t where "t = (p1, \<gamma>, q')"
  define j where "j = count (transitions_of' (p, w, ss, q)) t"

  from j_def ss_p show ?case
  proof (induction j arbitrary: p q w ss)
    case 0
    have "(p, w, ss, q) \<in> LTS.path_with_word Aiminus1"
      using lemma_3_2_a'_Aux_3
       p1_\<gamma>_p2_w2_q'_p(1) t_def 0 by fastforce
    then show ?case
      using step.IH step.prems(1) by metis
  next
    case (Suc j')
    have "\<exists>u v u_ss v_ss. ss = u_ss@v_ss \<and> w = u@[\<gamma>]@v \<and> (p,u,u_ss,p1) \<in> LTS.path_with_word Aiminus1 \<and> (p1,[\<gamma>],q') \<in> LTS.lpath Ai \<and> (q',v,v_ss,q) \<in> LTS.path_with_word Ai"
      apply (rule guuggugugugugugugugugu[of p w ss q Ai j' p1 \<gamma> q' Aiminus1])
      using Suc(2,3) t_def  p1_\<gamma>_p2_w2_q'_p(1,4) t_def by auto
    then obtain u v u_ss v_ss where
      "ss = u_ss@v_ss \<and> w = u@[\<gamma>]@v" 
      "(p,u,u_ss,p1) \<in> LTS.path_with_word Aiminus1" 
      "(p1,[\<gamma>],q') \<in> LTS.lpath Ai" 
      "(q',v,v_ss,q) \<in> LTS.path_with_word Ai"
      by blast
    have II: "p1 \<in> P_locs"
      using p1_\<gamma>_p2_w2_q'_p by auto
    have "\<exists>p'' w'' ss''. (p'', w'', ss'', p1) \<in> LTS.path_with_word A \<and> (p, u) \<Rightarrow>\<^sup>* (p'', w'')"
      using Suc(1)[of p u _ p1]
      using \<open>(p, u, u_ss, p1) \<in> LTS.path_with_word Aiminus1\<close> step.IH step.prems(1) by blast 
    then obtain p'' w'' ss'' where "(p'', w'', ss'', p1) \<in> LTS.path_with_word A" "(p, u) \<Rightarrow>\<^sup>* (p'', w'')"
      by blast
    from this lemma_3_2_b_aux'''  this(1) II have VIII: "(p, u) \<Rightarrow>\<^sup>* (p1, [])"
      using step.prems(1) by metis

    note IX = p1_\<gamma>_p2_w2_q'_p(2)
    note III = p1_\<gamma>_p2_w2_q'_p(3)
    from III have III_2: "\<exists>w2_ss. (p2, op_labels w2, w2_ss, q') \<in> LTS.path_with_word Aiminus1"
      using LTS.lpath_path_with_word[of p2 "op_labels w2" q' Aiminus1] by auto
    then obtain w2_ss where III_2: "(p2, op_labels w2, w2_ss, q') \<in> LTS.path_with_word Aiminus1"
      by blast

    from III have V: "(p2, op_labels w2, w2_ss, q') \<in> LTS.path_with_word Aiminus1 \<and> (q', v, v_ss, q) \<in> LTS.path_with_word Ai"
      using III_2 \<open>(q', v, v_ss, q) \<in> LTS.path_with_word Ai\<close> by auto

    define w2v where "w2v = op_labels w2 @ v"
    define w2v_ss where "w2v_ss = w2_ss @ tl v_ss"

    then have V_merged: "(p2, w2v, w2v_ss, q) \<in> LTS.path_with_word Ai"

      sorry

    have j'_gug: "j' = count (transitions_of' (p2, w2v, w2v_ss, q)) t"
      sorry
    
    have "\<exists>p' w' ss'. (p', w', ss', q) \<in> LTS.path_with_word A \<and> (p2, w2v) \<Rightarrow>\<^sup>* (p', w')"
      using Suc(1) using j'_gug V_merged by auto
    then obtain p' w' ss' where p'_w'_ss'_p: "(p', w', ss', q) \<in> LTS.path_with_word A" "(p2, w2v) \<Rightarrow>\<^sup>* (p', w')"
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
        sorry
      subgoal
        apply (metis IX LTS.step_relp_def transition_rel.intros w2v_def)
        done
      subgoal
        apply (simp add: X)
        done
      done

    have "(p, w) \<Rightarrow>\<^sup>* (p', w')"
      using X \<open>(p, u @ [\<gamma>] @ v) \<Rightarrow>\<^sup>* (p1, \<gamma> # v)\<close> \<open>(p, w) = (p, u @ [\<gamma>] @ v)\<close> \<open>(p1, \<gamma> # v) \<Rightarrow> (p2, w2v)\<close> by auto

    then have "(p', w', ss', q) \<in> LTS.path_with_word A \<and> (p, w) \<Rightarrow>\<^sup>* (p', w')"
      using p'_w'_ss'_p(1) by auto
    then show ?case
      by metis

  qed
qed 
  




(*
  (* Old proof *)
  from step(2) obtain p1 \<gamma> p2 w2 q' where p1_\<gamma>_p2_w2_q'_p:
                       "Ai = Aiminus1 \<union> {(p1, \<gamma>, q')}" 
                       "(p1, \<gamma>) \<hookrightarrow> (p2, w2)"
                       "(p2, op_labels w2, q') \<in> LTS.lpath Aiminus1"
    by (meson saturation_rule.cases)

  from step(5) obtain ss where ss_p: "hd ss = p" "last ss = q" "(ss, w) \<in> LTS.path_with_word Ai"
    using LTS.lpath_path_with_word[of p w q Ai]
    by auto

  define t where "t = (p1, \<gamma>, q')"
  define j where "j = count (transitions_of (ss, w)) t"

  from j_def ss_p show ?case
  proof (induction j arbitrary: q w ss)
    case 0
    have "(ss, w) \<in> LTS.path_with_word Aiminus1"
      using 0 p1_\<gamma>_p2_w2_q'_p 
      using lemma_3_2_a'_Aux
      using t_def by fastforce
    then have "(p, w, q) \<in> LTS.lpath Aiminus1"
      using LTS.path_with_word_lpath[of ss w Aiminus1] LTS.path_with_word_not_empty 0 by blast
    then show ?case
      using step.IH step.prems(1) by metis
  next
    case (Suc j')
    then have "j = Suc j'"
      sorry
    have "\<exists>u v u_ss v_ss. ss = u_ss @ v_ss \<and> w = u@[\<gamma>]@v \<and> last u_ss = p1 \<and> hd v_ss = q' \<and> (u_ss,u) \<in> LTS.path_with_word Aiminus1 \<and> (p1,[\<gamma>], q') \<in> LTS.lpath Ai \<and> (v_ss,v) \<in> LTS.path_with_word Ai"
      using Suc    
      sorry
    then obtain u v u_ss v_ss where guguguggu:
      "ss = u_ss @ v_ss"
      "w = u@[\<gamma>]@v"
      "last u_ss = p1" 
      "hd v_ss = q'"
      "(u_ss,u) \<in> LTS.path_with_word Aiminus1"
      "(p1,[\<gamma>], q') \<in> LTS.lpath Ai"
      "(v_ss,v) \<in> LTS.path_with_word Ai"
      by blast
    have "hd u_ss = p"
      by (metis LTS.path_with_word_not_empty Suc.prems(2) \<open>(u_ss, u) \<in> LTS.path_with_word Aiminus1\<close> \<open>ss = u_ss @ v_ss\<close> hd_append2)
    have "last v_ss = q"
      by (metis LTS.path_with_word_not_empty Suc.prems(3) \<open>(v_ss, v) \<in> LTS.path_with_word Ai\<close> \<open>ss = u_ss @ v_ss\<close> last_append)
    have u_v_p: "w = u@[\<gamma>]@v" "(p,u,p1) \<in> LTS.lpath Aiminus1" "(p1,[\<gamma>], q') \<in> LTS.lpath Ai" "(q', v, q) \<in> LTS.lpath Ai"
         apply (simp add: \<open>w = u @ [\<gamma>] @ v\<close>)
      using LTS.path_with_word_lpath LTS.path_with_word_not_empty \<open>(u_ss, u) \<in> LTS.path_with_word Aiminus1\<close> \<open>hd u_ss = p\<close> \<open>last u_ss = p1\<close> apply blast
       apply (simp add: \<open>(p1, [\<gamma>], q') \<in> LTS.lpath Ai\<close>)
      using LTS.path_with_word_lpath LTS.path_with_word_not_empty \<open>(v_ss, v) \<in> LTS.path_with_word Ai\<close> \<open>hd v_ss = q'\<close> \<open>last v_ss = q\<close> apply blast
      done
      
    have II: "p1 \<in> P_locs"
      sorry
    have "\<exists>p'' w''. (p'', w'', p1) \<in> LTS.lpath A \<and> (p, u) \<Rightarrow>\<^sup>* (p'', w'')"
      using Suc(1)[of _ u p1] sorry
    then obtain p'' w'' where p''_w'': "(p'', w'', p1) \<in> LTS.lpath A" "(p, u) \<Rightarrow>\<^sup>* (p'', w'')"
      by blast
    from this lemma_3_2_b_aux'[OF p''_w''(1) assms(1) II] have VIII: "(p, u) \<Rightarrow>\<^sup>* (p1, [])"
      by auto
    note IX = p1_\<gamma>_p2_w2_q'_p(2)
    note III = p1_\<gamma>_p2_w2_q'_p(3)
    from III have III_2: "\<exists>w2_ss. hd w2_ss = p2 \<and> last w2_ss = q' \<and> (w2_ss, op_labels w2) \<in> LTS.path_with_word Aiminus1"
      using LTS.lpath_path_with_word[of p2 "op_labels w2" q' Aiminus1] by auto
    then obtain w2_ss where w2_ss_p:
      "hd w2_ss = p2" "last w2_ss = q'" "(w2_ss, op_labels w2) \<in> LTS.path_with_word Aiminus1"
      by blast
    from III u_v_p(4) have V: "(p2, op_labels w2, q') \<in> LTS.lpath Aiminus1 \<and> (q', v, q) \<in> LTS.lpath Ai"
      sorry
    have V_2: "(w2_ss @ tl v_ss, (op_labels w2) @ v) \<in> LTS.path_with_word Ai"
      using w2_ss_p(3) guguguggu(7) 
      sorry
    
    then show ?case 
      sorry
  qed
qed
*)

    (* I think there is a challenge here.
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