theory morten_pds imports Main
begin

(* This is a formalization of pushdown systems. We follow the definitions, algorithms and proofs in:
   PhD Thesis: "Model-Checking Pushdown Systems", Stefan Schwoon, http://www.lsv.fr/Publis/PAPERS/PDF/schwoon-phd02.pdf  *)

(* Note: This is a first attempt, and is definitely 'work-in-progress'. *)

typedecl state
typedecl label

(* Define the states and labels to be fixed but arbitrary sets.
   Would it be better to have them as parameters? E.g. if we want to prove something about a specific construction of a PDS. *)
consts P_states :: "state set"
consts \<Gamma> :: "label set"
datatype operation = pop | swap "label" | push "label" "label"
type_synonym rule = "(state \<times> label) \<times> (state \<times> operation)"
consts \<Delta> :: "rule set"
definition \<P> where (* This is the PDS *)
  "\<P> = (P_states, \<Gamma>, \<Delta>)"

(* An aside on the push operation: 
   push is here defined as Schwoon does it, where it replaces the top label with a word of length 2.
   In the tool, we define push as just appending one label in top. 
   (In Schwoon's terms, for the rule \<langle>p,\<gamma>\<rangle> \<hookrightarrow> \<langle>p', \<gamma>\<^sub>1 \<gamma>\<^sub>2\<rangle> we require that \<gamma> = \<gamma>\<^sub>2.)
   I believe this restriction could potentially simplify the post* algorithm, though I have not actually worked out the details. 
 *)

primrec op_labels :: "operation \<Rightarrow> label list" where
  "op_labels pop = []"
| "op_labels (swap \<gamma>) = [\<gamma>]" 
| "op_labels (push \<gamma>  \<gamma>') = [\<gamma>, \<gamma>']"

type_synonym conf = "state \<times> label list" (* A configuration consists of a state and a label stack *)

definition is_rule :: "state \<times> label \<Rightarrow> state \<times> operation \<Rightarrow> bool" (infix "\<hookrightarrow>" 80) where
  "is_rule x y \<equiv> (x,y) \<in> \<Delta>"

primrec step' :: "label list \<Rightarrow> state \<Rightarrow> conf set" where
  "step' [] p = {}"
| "step' (\<gamma>#w') p = {(p', (op_labels w)@w') | p' w. (p,\<gamma>) \<hookrightarrow> (p', w)}"

(* Defines the immediate successors of a configuration in the PDS. *)
definition step :: "conf \<Rightarrow> conf set" where
  "step \<equiv> \<lambda>(p,w). step' w p"

definition step_relp :: "conf \<Rightarrow> conf \<Rightarrow> bool" where
  "step_relp c c' \<equiv> c' \<in> step c"
definition step_rel :: "conf rel" where
  "step_rel \<equiv> {(c, c'). step_relp c c'}"
definition step_starp  :: "state \<times> label list \<Rightarrow> state \<times> label list \<Rightarrow> bool" (infix "\<Rightarrow>\<^sup>*" 80) where
  "step_starp \<equiv> step_relp\<^sup>*\<^sup>*"
definition step_star :: "conf rel" where
  "step_star \<equiv> {(c, c'). step_starp c c'}"
abbreviation
  step_star_trans ("(_\<Rightarrow>\<^sup>*_\<Rightarrow>\<^sup>*_)" 80) where
  "c \<Rightarrow>\<^sup>* c' \<Rightarrow>\<^sup>* c'' \<equiv> (c \<Rightarrow>\<^sup>* c') \<and> (c' \<Rightarrow>\<^sup>* c'')"

(* For a set of configurations C, post*(C) is the set of all configurations reachable from C. *)
definition post_star :: "conf set \<Rightarrow> conf set" where
  "post_star C \<equiv> {c'. \<exists>c \<in> C. c \<Rightarrow>\<^sup>* c'}"
(* And pre*(C) is the set of all configurations that can reach a configuration in C. *)
definition pre_star :: "conf set \<Rightarrow> conf set" where
  "pre_star C \<equiv> {c'. \<exists>c \<in> C. c' \<Rightarrow>\<^sup>* c}"


(* For computing pre* and post*, we need to define a \<P>-automaton, which defines a regular set of configurations in the PDS \<P>. 
   A \<P>-automaton is an NFA with multiple initial and final states. The initial states are exactly the states in \<P>.
   The label alphabet is the same as in \<P>. 
 *)
consts QnotP :: "state set"
definition Q where
  "Q = QnotP \<union> P_states"
consts F :: "state \<Rightarrow> bool"
type_synonym transition = "state \<times> label \<times> state"

(* This defines a specific (but arbitrary) \<P>-automaton. 
   However, the pre* and post* procedures build up the automaton, so maybe this is not useful. *)
consts my_rel :: "transition set" ("\<rightarrow>") 
definition \<A> where
  "\<A> = (Q, \<Gamma>, \<rightarrow>, P_states, F)"

(* For any given set of transitions, this defines the set of tuples (p,w,q) such that there is a w-path from p to q. *)
inductive_set transition_star :: "transition set \<Rightarrow> (state \<times> label list \<times> state) set"
  for t :: "transition set" where
  transition_star_refl[iff]: "(p, [], p) \<in> (transition_star t)"
| transition_star_step: "\<lbrakk>(p,\<gamma>,q') \<in> t; (q',w,q) \<in> (transition_star t)\<rbrakk>
                           \<Longrightarrow> (p, \<gamma>#w, q) \<in> (transition_star t)"
inductive_cases transition_star_empty [elim]: "(p, [], q) \<in> (transition_star t)"
inductive_cases transition_star_cons: "(p, \<gamma>#w, q) \<in> (transition_star t)"

lemma transition_star_mono[mono]: "mono transition_star"
  unfolding mono_def
  apply clarsimp
  subgoal for x y p w q
    by (induct w arbitrary: p; blast intro: transition_star_step elim: transition_star_cons)
  done

(* A configuration (p,w) in \<P> is accepted by the \<P>-automaton, if there is an accepting w-path starting from p. *)
definition accepts :: "transition set \<Rightarrow> conf \<Rightarrow> bool" where
  "accepts ts \<equiv> \<lambda>(p,w). \<exists>q \<in> Q. F q \<and> (p,w,q)\<in>(transition_star ts)"


(* Potentially useful lemmas. *)

lemma accepts_mono[mono]: "mono accepts"
  using transition_star_mono
  unfolding mono_def accepts_def
  by blast

lemma accepts_cons: "\<lbrakk>(p, \<gamma>, q) \<in> ts; accepts ts (q, w)\<rbrakk> \<Longrightarrow> accepts ts (p, \<gamma> # w)"
  unfolding accepts_def
  using transition_star_step by auto

lemma accepts_unfold: "\<lbrakk>accepts ts (p, \<gamma> # w)\<rbrakk> \<Longrightarrow> \<exists>q. (p, \<gamma>, q) \<in> ts \<and> accepts ts (q, w)"
  unfolding accepts_def
  by (induct w; blast elim: transition_star_cons) 
lemma accepts_unfoldn: "\<lbrakk>accepts ts (p, w' @ w)\<rbrakk> \<Longrightarrow> \<exists>q. (p, w', q) \<in> transition_star ts \<and> accepts ts (q, w)"
  unfolding accepts_def
  by (induct w' arbitrary: p w, fastforce)
     (simp, blast intro: transition_star_step elim: transition_star_cons)

lemma accepts_append: "\<lbrakk>(p, w', q) \<in> transition_star ts; accepts ts (q, w)\<rbrakk> \<Longrightarrow> accepts ts (p, w' @ w)"
  unfolding accepts_def
  using transition_star_step
  by (induct w' arbitrary: w p q, fastforce)
     (clarsimp, metis (no_types, lifting) list.discI list.inject transition_star.cases)

(*
fun accept_fun :: "conf \<Rightarrow> bool" where
  "accept_fun (p, []) = F p"
| "accept_fun (p, \<gamma>#w) = (\<exists>q \<in> Q. (p, \<gamma>, q) \<in> rel \<and> accept_fun (q, w))"
*)
definition language :: "transition set \<Rightarrow> conf set" where
  "language ts = {c. accepts ts c}"


end