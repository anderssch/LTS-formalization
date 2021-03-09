theory LTS imports Transition_Systems_and_Automata.Transition_System_Construction begin

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

interpretation ts: transition_system execute enabled .


find_theorems execute

text \<open>We "open" the interpretation.\<close>

abbreviation successors :: "'state \<Rightarrow> 'state set" where
   "successors == ts.successors"

abbreviation path :: "('state, 'label) transition list \<Rightarrow> 'state \<Rightarrow> bool" where 
  "path s p == ts.path s p" (* s is a path from p. *)

abbreviation run :: "('state, 'label) transition stream \<Rightarrow> 'state \<Rightarrow> bool" where 
  "run == ts.run"

abbreviation reachable :: "'state \<Rightarrow> 'state set" where
  "reachable == ts.reachable"

abbreviation reachablep :: "'state \<Rightarrow> 'state \<Rightarrow> bool" where
  "reachablep == ts.reachablep"

text \<open>More definitions.\<close>

(* Paths as defined in the thesis: *)
inductive_set spath :: "'state list set" where
  "[] \<in> spath"
| "[s] \<in> spath"
| "(s'#ss) \<in> spath \<Longrightarrow> (s,l,s') \<in> transition_relation \<Longrightarrow> (s#s'#ss) \<in> spath"

(* Labeled paths as defined in the thesis *)
inductive_set lspath :: "('state * 'label list * 'state) set" where
  transition_star_refl[iff]: "(p, [], p) \<in> lspath"
| transition_star_step: "\<lbrakk>(p,\<gamma>,q') \<in> t; (q',w,q) \<in> lspath\<rbrakk>
                           \<Longrightarrow> (p, \<gamma>#w, q) \<in> lspath"

(* TODO: Prove correspondences between spath, path and lspath.
   "Lift" path's theorem to spath and lspath
 *)

abbreviation transition_star :: "('state \<times> 'label list \<times> 'state) set" where (* Morten terminology -- but I dropped the transition set *)
  "transition_star \<equiv> lspath"

(* lemma transition_star_mono[mono]: "mono transition_star" *) (* Not possible with my definition of transition_star *)

end

locale LTS_init = LTS transition_relation for transition_relation :: "('state, 'label) transition set" +
  fixes r :: 'state
begin

text \<open>We interpret transition_system_initial.\<close>

interpretation ts: transition_system_initial execute enabled "\<lambda>r'. r' = r" .

text \<open>We "open" the interpretation.\<close>

abbreviation nodes :: "'state set" where
  "nodes == ts.nodes"

end

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

text \<open>We interpret LTS.\<close>

interpretation pds: LTS_init transition_rel c0 .
(* Det er måske lidt problematisk at P_locs ikke bliver sendt der ind. *)

text \<open>We "open" the interpretation.\<close>

abbreviation pds_execute :: "(('ctr_loc, 'label) conf, 'label) transition \<Rightarrow> ('ctr_loc, 'label) conf \<Rightarrow> ('ctr_loc, 'label) conf" where
  "pds_execute == pds.execute"

abbreviation pds_enabled :: "(('ctr_loc, 'label) conf, 'label) transition \<Rightarrow> ('ctr_loc, 'label) conf \<Rightarrow> bool" where
  "pds_enabled == pds.enabled"

abbreviation pds_successors :: "('ctr_loc, 'label) conf \<Rightarrow> ('ctr_loc, 'label) conf set" where
  "pds_successors == pds.successors"

abbreviation "pds_step == pds_successors" (* Morten/Stefan terminology *)

abbreviation pds_path :: "(('ctr_loc, 'label) conf, 'label) transition list \<Rightarrow> ('ctr_loc, 'label) conf \<Rightarrow> bool" where
  "pds_path == pds.path"

abbreviation pds_run :: "(('ctr_loc, 'label) conf, 'label) transition stream \<Rightarrow> ('ctr_loc, 'label) conf \<Rightarrow> bool" where
  "pds_run == pds.run"

abbreviation pds_reachable :: "('ctr_loc, 'label) conf \<Rightarrow> ('ctr_loc, 'label) conf set" where
  "pds_reachable == pds.reachable"

abbreviation pds_reachablep :: "('ctr_loc, 'label) conf \<Rightarrow> ('ctr_loc, 'label) conf \<Rightarrow> bool" (infix "\<Rightarrow>\<^sup>*" 80) where
  "c \<Rightarrow>\<^sup>* c' == pds.reachablep c c'"


abbreviation pds_nodes :: "('ctr_loc, 'label) conf set" where
  "pds_nodes == pds.nodes"

definition pds_step_relp  :: "('ctr_loc, 'label) conf \<Rightarrow> ('ctr_loc, 'label) conf \<Rightarrow> bool" (infix "\<Rightarrow>" 80) where
  "c \<Rightarrow> c' \<equiv> c' \<in> pds_successors c"

definition psd_spath :: " ('ctr_loc, 'label) conf list set" where
  "psd_spath \<equiv> pds.spath"

definition psd_lspath :: "(('ctr_loc, 'label) conf \<times> 'label list \<times> ('ctr_loc, 'label) conf) set" where
  "psd_lspath \<equiv> pds.lspath"


text \<open>More definitions\<close>

abbreviation "pds_step_starp == pds_reachablep" (* Morten/Stefan terminology *) (* TODO: copy into LTS *)

definition pds_step_rel :: "('ctr_loc, 'label) conf rel" where (* TODO: copy into LTS *)
  "pds_step_rel \<equiv> {(c, c'). pds_step_relp c c'}"

definition pds_step_star :: "('ctr_loc, 'label) conf rel" where (* TODO: copy into LTS *)
  "pds_step_star \<equiv> {(c, c'). pds_step_starp c c'}"

abbreviation
  pds_step_star_trans ("(_\<Rightarrow>\<^sup>*_\<Rightarrow>\<^sup>*_)" 80) where (* TODO: copy into LTS *)
  "c \<Rightarrow>\<^sup>* c' \<Rightarrow>\<^sup>* c'' \<equiv> (c \<Rightarrow>\<^sup>* c') \<and> (c' \<Rightarrow>\<^sup>* c'')"

(* For a set of configurations C, post*(C) is the set of all configurations reachable from C. *) (* TODO: copy into LTS *)
definition pds_post_star :: "('ctr_loc, 'label) conf set \<Rightarrow> ('ctr_loc, 'label) conf set" where
  "pds_post_star C \<equiv> {c'. \<exists>c \<in> C. c \<Rightarrow>\<^sup>* c'}"

(* And pre*(C) is the set of all configurations that can reach a configuration in C. *)  (* TODO: copy into LTS *)
definition pds_pre_star :: "('ctr_loc, 'label) conf set \<Rightarrow> ('ctr_loc, 'label) conf set" where
  "pds_pre_star C \<equiv> {c'. \<exists>c \<in> C. c' \<Rightarrow>\<^sup>* c}"

end

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

interpretation autom: LTS trans .


text \<open>We "open" the interpretation.\<close>
abbreviation autom_execute :: "('ctr_loc, 'label) transition \<Rightarrow> 'ctr_loc \<Rightarrow> 'ctr_loc" where 
  "autom_execute \<equiv> autom.execute"

abbreviation autom_enabled :: "('ctr_loc, 'label) transition \<Rightarrow> 'ctr_loc \<Rightarrow> bool" where 
  "autom_enabled  \<equiv> autom.enabled"

abbreviation autom_successors :: "'ctr_loc \<Rightarrow> 'ctr_loc set" where 
   "autom_successors \<equiv> autom.successors"

abbreviation autom_path :: "('ctr_loc, 'label) transition list \<Rightarrow> 'ctr_loc \<Rightarrow> bool" where
  "autom_path \<equiv> autom.path"

abbreviation autom_run  :: "('ctr_loc, 'label) transition stream \<Rightarrow> 'ctr_loc \<Rightarrow> bool" where
  "autom_run \<equiv> autom.run"

abbreviation autom_reachable :: "'ctr_loc \<Rightarrow> 'ctr_loc set" where
  "autom_reachable \<equiv> autom.reachable"

abbreviation autom_reachablep :: "'ctr_loc \<Rightarrow> 'ctr_loc \<Rightarrow> bool" where 
  "autom_reachablep \<equiv> autom.reachablep"

abbreviation autom_spath :: "'ctr_loc list set" where
  "autom_spath \<equiv> autom.spath"

abbreviation autom_lspath :: "('ctr_loc * 'label list * 'ctr_loc) set" where
  "autom_lspath \<equiv> autom.lspath"

abbreviation autom_transition_star :: "('ctr_loc \<times> 'label list \<times> 'ctr_loc) set" where 
  "autom_transition_star \<equiv> autom.transition_star"

text \<open>More definitions\<close>

fun accepts :: "('ctr_loc, 'label) conf \<Rightarrow> bool" where
  "accepts (p,l) \<longleftrightarrow> (\<exists>q \<in> F_locs. (p,l,q) \<in> autom_lspath)" 
(* Here acceptance is defined for any p, but in the paper p has to be in P_locs *)

(* Potentially useful lemmas. *)

(* lemma accepts_mono[mono]: "mono accepts" *) (* Not possible with my definition of transition_star *)

lemma accepts_cons: "(p, \<gamma>, q) \<in> trans \<Longrightarrow> accepts (q, w) \<Longrightarrow> accepts (p, \<gamma> # w)"
  by (meson accepts.simps autom.lspath.intros(2))

lemma accepts_unfold: "accepts (p, \<gamma> # w) \<Longrightarrow> \<exists>q. (p, \<gamma>, q) \<in> trans \<and> accepts (q, w)"
proof -
  assume "accepts (p, \<gamma> # w)"
  then obtain q where "q \<in> F_locs \<and> (p,\<gamma> # w,q) \<in> autom_lspath"
    by auto
  find_theorems autom_lspath

  have "(p, \<gamma>, q') \<in> trans \<and> accepts (q', w)"
  
  show "\<exists>q. (p, \<gamma>, q) \<in> trans \<and> accepts (q, w)"
    sorry
qed












end