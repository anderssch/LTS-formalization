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
inductive_set path :: "'state list set" where (* But actually the thesis does not have empty paths *)
  "[s] \<in> path"
| "(s'#ss) \<in> path \<Longrightarrow> (s,l,s') \<in> transition_relation \<Longrightarrow> s#s'#ss \<in> path"


(* Labeled paths as defined in the thesis *)
inductive_set lpath :: "('state * 'label list * 'state) set" where
  lpath_refl[iff]: "(p, [], p) \<in> lpath"
| lpath_step: "(p,\<gamma>,q') \<in> transition_relation \<Longrightarrow> (q',w,q) \<in> lpath
                           \<Longrightarrow> (p, \<gamma>#w, q) \<in> lpath"

inductive_cases lpath_empty [elim]: "(p, [], q) \<in> lpath"
inductive_cases lpath_cons: "(p, \<gamma>#w, q) \<in> lpath"

inductive_set path_with_word :: "('state list * 'label list) set" where
  path_with_word_refl[iff]: "([s],[]) \<in> path_with_word"
| path_with_word_step: "(s'#ss, w) \<in> path_with_word \<Longrightarrow> (s,l,s') \<in> transition_relation \<Longrightarrow> (s#s'#ss,l#w) \<in> path_with_word"

inductive transition_of :: "('state, 'label) transition \<Rightarrow> 'state list * 'label list \<Rightarrow> bool" where
  "transition_of (s1,\<gamma>,s2) (s1#s2#ss, \<gamma>#w)"
| "transition_of (s1,\<gamma>,s2) (ss, w) \<Longrightarrow> transition_of (s1,\<gamma>,s2) (s#ss, \<mu>#w)"


                                                  
lemma path_with_word_not_empty[simp]: "\<not>([],w) \<in> path_with_word"
  using path_with_word.cases by force
  

lemma lpath_path_with_word:
  assumes "(p, w, q) \<in> lpath"
  shows "\<exists>ss. hd ss = p \<and> last ss = q \<and> (ss, w) \<in> path_with_word"
  using assms
proof (induction rule: lpath.inducts)
  case (lpath_refl p)
  then show ?case
    by (meson LTS.path_with_word.path_with_word_refl last.simps list.sel(1))
next
  case (lpath_step p \<gamma> q' w q)
  then show ?case
    by (metis LTS.path_with_word.simps hd_Cons_tl last_ConsR list.discI list.sel(1))
qed

lemma path_with_word_lpath:
  assumes "(ss, w) \<in> path_with_word"
  assumes "length ss \<noteq> 0"
  shows "(hd ss, w, last ss) \<in> lpath"
  using assms
proof (induction rule: path_with_word.inducts)
  case (path_with_word_refl s)
  show ?case
    by simp 
next
  case (path_with_word_step s' ss w s l)
  then show ?case
    using LTS.lpath.lpath_step by fastforce
qed

lemma path_with_word_lpath_Cons:
  assumes "(s1#ss@[s2], w) \<in> path_with_word"
  shows "(s1, w, s2) \<in> lpath"
  using assms path_with_word_lpath by force 

lemma path_with_word_lpath_Singleton:
  assumes "([s2], w) \<in> path_with_word"
  shows "(s2, [], s2) \<in> lpath"
  using assms path_with_word_lpath by force



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
    by (metis lpath_step append_Cons lpath_cons)
qed

end

fun transitions_of :: "'state list * 'label list \<Rightarrow> ('state, 'label) transition multiset" where
  "transitions_of (s1#s2#ss, \<gamma>#w) = {# (s1, \<gamma>, s2) #} + transitions_of (s2#ss, w)"
| "transitions_of ([s1],_) = {#}"
| "transitions_of ([],_) = {#}"
| "transitions_of (_,[]) = {#}"

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

lemma finite_P_locs: "finite P_locs"
  by simp  

interpretation LTS_init transition_rel c0 .

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

(* BEGIN "IMPORT NOTATION" *)
abbreviation step_relp' (infix "\<Rightarrow>" 80) where
  "c \<Rightarrow> c' \<equiv> step_relp c c'"

abbreviation step_starp' (infix "\<Rightarrow>\<^sup>*" 80) where
  "step_starp' == step_relp\<^sup>*\<^sup>*"
(* END "IMPORT NOTATION" *)

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

inductive saturation_rule :: "('ctr_loc, 'label) transition set \<Rightarrow> ('ctr_loc, 'label) transition set \<Rightarrow> bool" where
  add_trans: "(p, \<gamma>) \<hookrightarrow> (p', w) \<Longrightarrow> (p', op_labels w, q) \<in> LTS.lpath ts \<Longrightarrow> (p, \<gamma>, q) \<notin> ts \<Longrightarrow> saturation_rule ts (ts \<union> {(p, \<gamma>, q)})"

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
  assumes "(p',w) \<Rightarrow>\<^sup>* (p,v)"
    and "(p,v) \<in> language A"
    and "saturation A A'"
  shows "accepts A' (p',w)"
  using assms
proof (induct rule: converse_rtranclp_induct)
  case base
  then have "\<exists>q \<in> F_locs. (p, v, q) \<in> LTS.lpath A'"
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

  have "accepts A' (p'', u)" 
    using step unfolding p''_def u_def by auto
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

  have "\<exists>q1. (p'', op_labels u1, q1) \<in> LTS.lpath A' \<and> (q1, w1, q) \<in> LTS.lpath A'"
    using q_p \<gamma>_w1_u1_p LTS.lpath_split by auto

  then obtain q1 where q1_p: "(p'', op_labels u1, q1) \<in> LTS.lpath A' \<and> (q1, w1, q) \<in> LTS.lpath A'"
    by auto

  then have in_A': "(p', \<gamma>, q1) \<in> A'"
    using \<gamma>_w1_u1_p add_trans step.prems(2)
    using saturated_def saturation_def by blast

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

lemma count_next_0:
  assumes "count (transitions_of (s # s' # ss, l # w)) (p1, \<gamma>, q') = 0"
  shows "count (transitions_of (s' # ss, w)) (p1, \<gamma>, q') = 0"
  using assms by (cases "s = p1 \<and> l = \<gamma> \<and> s' = q'") auto

lemma count_next_hd:
  assumes "count (transitions_of (s # s' # ss, l # w)) (p1, \<gamma>, q') = 0"
  shows "(s, l, s') \<noteq> (p1, \<gamma>, q')"
  using assms by auto
  

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


lemma lemma_3_2_a':
  assumes "\<nexists>q \<gamma> q'. (q, \<gamma>, q') \<in> A \<and> q' \<in> P_locs"
  assumes "saturation_rule\<^sup>*\<^sup>* A A'"
  assumes "(p, w, q) \<in> LTS.lpath A'"
  shows "\<exists>p' w'. (p', w', q) \<in> LTS.lpath A \<and> (p, w) \<Rightarrow>\<^sup>* (p', w')"
  using assms(2) assms(1,3) 
proof (induction arbitrary: q w rule: rtranclp_induct )
  case base
  then show ?case
    by auto
next
  case (step Aiminus1 Ai)
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
    have "\<exists>u v. w = u@[\<gamma>]@v \<and> (p,u,p1) \<in> LTS.lpath Aiminus1 \<and> (p1,[\<gamma>], q') \<in> LTS.lpath Ai \<and> (q', v, q) \<in> LTS.lpath Ai"
      using Suc    
      sorry
    then obtain u v where u_v_p: "w = u@[\<gamma>]@v" "(p,u,p1) \<in> LTS.lpath Aiminus1" "(p1,[\<gamma>], q') \<in> LTS.lpath Ai" "(q', v, q) \<in> LTS.lpath Ai"
      by blast
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
    from III u_v_p(4) have V: "(p2, op_labels w2, q') \<in> LTS.lpath Aiminus1 \<and> (q', v, q) \<in> LTS.lpath Ai"
      sorry
    
    then show ?case 
      sorry
  qed
qed


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