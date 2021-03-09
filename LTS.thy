theory LTS imports Transition_Systems_and_Automata.Transition_System_Construction begin


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
  "step_starp == reachablep"  (* Morten/Stefan terminology *) 

definition step_relp  :: "'state \<Rightarrow> 'state \<Rightarrow> bool" (infix "\<Rightarrow>" 80) where
  "c \<Rightarrow> c' \<equiv> c' \<in> successors c"

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

(* lemma transition_star_mono[mono]: "mono transition_star" *) (* Not possible with my definition of transition_star *)

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
  fixes P_locs :: "'ctr_loc set" 
    and \<Gamma> :: "'label set"
    and \<Delta> :: "('ctr_loc, 'label) rule set"
    and c0 :: "('ctr_loc, 'label) conf"
  assumes "\<Delta> \<subseteq> (P_locs \<times> UNIV) \<times> (P_locs \<times> UNIV)"
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

end

section \<open>PDS with P automaton\<close>

locale PDS_with_P_automaton = PDS P_locs \<Gamma>
  for P_locs :: "'ctr_loc set" 
    and \<Gamma> :: "'label set"
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

interpretation autom: LTS trans .

fun accepts :: "('ctr_loc, 'label) conf \<Rightarrow> bool" where
  "accepts (p,l) \<longleftrightarrow> (\<exists>q \<in> F_locs. (p,l,q) \<in> autom.lspath)" 
(* Here acceptance is defined for any p, but in the paper p has to be in P_locs *)

(* Potentially useful lemmas. *)

(* lemma accepts_mono[mono]: "mono accepts" *) (* Not possible with my definition of transition_star *)

lemma accepts_cons: "(p, \<gamma>, q) \<in> trans \<Longrightarrow> accepts (q, w) \<Longrightarrow> accepts (p, \<gamma> # w)"
  by (meson accepts.simps autom.lspath.intros(2))

lemma accepts_unfold: "accepts (p, \<gamma> # w) \<Longrightarrow> \<exists>q. (p, \<gamma>, q) \<in> trans \<and> accepts (q, w)"
  by (meson accepts.simps autom.transition_star_cons)

lemma accepts_unfoldn: "accepts (p, w' @ w) \<Longrightarrow> \<exists>q. (p, w', q) \<in> autom.transition_star \<and> accepts (q, w)"
  apply (induct w' arbitrary: p w)
   apply auto[1]
  apply (metis accepts_unfold append_Cons autom.lspath.transition_star_step)
  done

lemma accepts_append: "\<lbrakk>(p, w', q) \<in> autom.transition_star; accepts (q, w)\<rbrakk> \<Longrightarrow> accepts (p, w' @ w)"
  apply (induct w' arbitrary: w p q)
   apply auto[1]
  apply (metis LTS.transition_star_cons accepts_cons append_Cons)
  done

definition language :: "('ctr_loc, 'label) conf set" where
  "language = {c. accepts c}"

subsection \<open>pre star\<close>

inductive saturation_rule :: "('ctr_loc, 'label) transition set \<Rightarrow> ('ctr_loc, 'label) transition set \<Rightarrow> bool" where
  "(p, \<gamma>) \<hookrightarrow> (p', w) \<Longrightarrow> (p', w, q) \<in> "

  



    











end