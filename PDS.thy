theory PDS imports Transition_Systems_and_Automata.Transition_System_Construction begin


section \<open>LTS\<close>

type_synonym ('state, 'label) transition = "'state * 'label * 'state"

locale LTS =
  fixes transition_relation :: "('state, 'label) transition set"
begin

text \<open>We define execution and what it means to be enabled.\<close>

fun execute :: "('state, 'label) transition \<Rightarrow> 'state \<Rightarrow> 'state" where 
  "execute (s, l, s') s'' = s'"

fun enabled :: "('state, 'label) transition \<Rightarrow> 'state \<Rightarrow> bool" where
  "enabled (s, l, s') s'' \<longleftrightarrow> (s, l, s') \<in> transition_relation \<and> s = s''"

text \<open>We interpret transition_system_initial.\<close>

interpretation transition_system execute enabled .

text \<open>More definitions.\<close>

abbreviation step_starp (infix "\<Rightarrow>\<^sup>*" 80) where
  "step_starp == reachablep" (* Morten/Stefan terminology *) 

definition step_relp  :: "'state \<Rightarrow> 'state \<Rightarrow> bool" (infix "\<Rightarrow>" 80) where
  "c \<Rightarrow> c' \<equiv> c' \<in> successors c"

lemma "step_relp\<^sup>*\<^sup>* c c' \<longleftrightarrow> reachablep c c'"
  apply rule
  subgoal
    apply (induction rule: rtranclp_induct)
     apply blast
    apply (meson reachable_successors reachable_trans reachablep_reachable_eq step_relp_def subsetD)
    done
  subgoal
    apply (induction rule: reachablep.induct)
     apply simp
    apply (metis (mono_tags, lifting) mem_Collect_eq rtranclp.rtrancl_into_rtrancl step_relp_def)
    done
  done

definition step_rel :: "'state rel" where 
  "step_rel \<equiv> {(c, c'). step_relp c c'}"

definition step_star :: "'state rel" where 
  "step_star \<equiv> {(c, c'). step_starp c c'}"

abbreviation
  step_star_trans ("(_\<Rightarrow>\<^sup>*_\<Rightarrow>\<^sup>*_)" 80) where 
  "c \<Rightarrow>\<^sup>* c' \<Rightarrow>\<^sup>* c'' \<equiv> (c \<Rightarrow>\<^sup>* c') \<and> (c' \<Rightarrow>\<^sup>* c'')"

(* For a set of configurations C, post*(C) is the set of all configurations reachable from C. *)
definition pds_post_star :: "'state set \<Rightarrow> 'state set" where
  "pds_post_star C \<equiv> {c'. \<exists>c \<in> C. c \<Rightarrow>\<^sup>* c'}"

(* And pre*(C) is the set of all configurations that can reach a configuration in C. *)
definition pds_pre_star :: "'state set \<Rightarrow> 'state set" where
  "pds_pre_star C \<equiv> {c'. \<exists>c \<in> C. c' \<Rightarrow>\<^sup>* c}"

(* Paths as defined in the thesis: *)
inductive_set spath :: "'state list set" where
  "[] \<in> spath"
| "[s] \<in> spath"
| "(s'#ss) \<in> spath \<Longrightarrow> (s,l,s') \<in> transition_relation \<Longrightarrow> (s#s'#ss) \<in> spath"

(* Labeled paths as defined in the thesis *)
inductive_set lspath :: "('state * 'label list * 'state) set" where
  transition_star_refl[iff]: "(p, [], p) \<in> lspath"
| transition_star_step: "\<lbrakk>(p,\<gamma>,q') \<in> transition_relation; (q',w,q) \<in> lspath\<rbrakk>
                           \<Longrightarrow> (p, \<gamma>#w, q) \<in> lspath"

inductive_cases lspath_empty [elim]: "(p, [], q) \<in> lspath"
inductive_cases lspath_cons: "(p, \<gamma>#w, q) \<in> lspath"

(* TODO: Prove correspondences between spath, path and lspath.
   "Lift" path's theorem to spath and lspath
 *)

abbreviation transition_star :: "('state \<times> 'label list \<times> 'state) set" where (* Morten terminology -- but I dropped the transition set *)
  "transition_star \<equiv> lspath"

lemmas transition_star_empty = lspath_empty
lemmas transition_star_cons = lspath_cons

end

section\<open>LTS init\<close>

locale LTS_init = LTS transition_relation for transition_relation :: "('state, 'label) transition set" +
  fixes r :: 'state
begin

abbreviation initial where "initial == (\<lambda>r'. r' = r)"

interpretation ts: transition_system execute enabled .

interpretation tsi: transition_system_initial execute enabled initial .

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

interpretation LTS_init transition_rel c0 .
interpretation transition_system execute enabled .
interpretation transition_system_initial execute enabled initial .

lemma finite_P_locs: "finite P_locs"
  by simp  

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
interpretation transition_system execute enabled .
interpretation transition_system_initial execute enabled initial .

(* BEGIN "IMPORT NOTATION" *)
abbreviation step_starp_notation (infix "\<Rightarrow>\<^sup>*" 80) where
  "step_starp_notation == reachablep"
(* END "IMPORT NOTATION" *)

fun accepts :: "('ctr_loc \<times> 'label \<times> 'ctr_loc) set \<Rightarrow> 'ctr_loc \<times> 'label list \<Rightarrow> bool" where
  "accepts ts (p,l) \<longleftrightarrow> (\<exists>q \<in> F_locs. (p,l,q) \<in> LTS.lspath ts)"
  (* Here acceptance is defined for any p, but in the paper p has to be in P_locs *)

lemma LTS_lspath_mono: (* Move *)
  "mono LTS.lspath"
proof (rule, rule)
  fix pwq :: "'a \<times> 'b list \<times> 'a"
  fix ts ts' :: "('a, 'b) transition set"
  assume sub: "ts \<subseteq> ts'"
  assume awb_ts: "pwq \<in> LTS.lspath ts"
  then obtain p w q where pwq_p: "pwq = (p, w, q)"
    using prod_cases3 by blast
  then have "(p, w, q) \<in> LTS.lspath ts"
    using awb_ts by auto
  then have "(p, w, q) \<in>  LTS.lspath ts'"
  proof(induction w arbitrary: p)
    case Nil
    then show ?case
      by (metis LTS.lspath.transition_star_refl LTS.transition_star_empty)
  next
    case (Cons \<gamma> w)
    then show ?case
      by (meson LTS.lspath.simps LTS.transition_star_cons sub subsetD)
  qed
  then show "pwq \<in> LTS.lspath ts'"
    unfolding pwq_p .
qed

lemma accepts_mono[mono]: "mono accepts" (* Hmm.. what does this actually mean? *)
proof (rule, rule)
  fix c :: "('ctr_loc, 'label) conf"
  fix ts ts' :: "('ctr_loc, 'label) transition set"
  assume accepts_xa: "accepts ts c"
  assume tsts': "ts \<subseteq> ts'"
  obtain p l where pl_p: "c = (p,l)"
    by (cases c)
  obtain q where q_p:  "q \<in> F_locs \<and> (p, l, q) \<in> LTS.lspath ts"
    using accepts_xa unfolding pl_p accepts.simps by auto
  then have "(p, l, q) \<in> LTS.lspath ts'"
    using tsts' LTS_lspath_mono monoD by blast 
  then have "accepts ts' (p,l)"
    unfolding accepts.simps using q_p by auto
  then show "accepts ts' c"
    unfolding pl_p .
qed

lemma accepts_cons: "(p, \<gamma>, q) \<in> ts \<Longrightarrow> accepts ts (q, w) \<Longrightarrow> accepts ts (p, \<gamma> # w)"
  by (meson LTS.lspath.transition_star_step PDS_with_P_automaton.accepts.simps PDS_with_P_automaton_axioms)


lemma accepts_unfold: "accepts ts (p, \<gamma> # w) \<Longrightarrow> \<exists>q. (p, \<gamma>, q) \<in> ts \<and> accepts ts (q, w)"
  by (meson LTS.transition_star_cons accepts.simps)

lemma accepts_unfoldn: "accepts ts (p, w' @ w) \<Longrightarrow> \<exists>q. (p, w', q) \<in> LTS.transition_star ts \<and> accepts ts (q, w)"
proof (induct w' arbitrary: p w)
  case Nil
  then show ?case by (metis LTS.lspath.transition_star_refl append_Nil)
next
  case (Cons a w')
  then show ?case by (metis LTS.lspath.transition_star_step accepts_unfold append_Cons)
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

(* pre_star_step' *)
inductive saturation_rule :: "('ctr_loc, 'label) transition set \<Rightarrow> ('ctr_loc, 'label) transition set \<Rightarrow> bool" where
  add_trans: "(p, \<gamma>) \<hookrightarrow> (p', w) \<Longrightarrow> (p', op_labels w, q) \<in> LTS.transition_star ts \<Longrightarrow> (p', \<gamma>, q) \<notin> ts \<Longrightarrow> saturation_rule ts (ts \<union> {(p', \<gamma>, q)})"

abbreviation "pre_star' \<equiv> saturation_rule\<^sup>*\<^sup>*" 

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

lemma pre_star'_incr_transition_star:
  "pre_star' A A' \<Longrightarrow> LTS.transition_star A \<subseteq> LTS.transition_star A'"
  using mono_def LTS_lspath_mono saturation_rtranclp_rule_incr by metis
  
lemma pre_star_lim'_incr_transition_star:
  "saturation A A' \<Longrightarrow> LTS.transition_star A \<subseteq> LTS.transition_star A'"
  by (simp add: pre_star'_incr_transition_star saturation_def)

lemma lemma_3_1':
  assumes "(p',w) \<Rightarrow>\<^sup>* (p,v)"
      and "(p,v) \<in> language A"
      and "pre_star_lim' A A'"
    shows "accepts A' (p',w)"
  using assms 
proof(induction)
  case reflexive
  then show ?case sorry
next
  case (execute q a)
  then show ?case sorry
qed

find_theorems reachablep


  




end