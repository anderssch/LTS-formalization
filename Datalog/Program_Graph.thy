theory Program_Graph imports "../PDS/LTS" begin

                                                                                  
section \<open>Actions\<close>

datatype (fv_arith: 'v) arith =
  Integer int
  | Var 'v
  | Arith_Op "'v arith" "int \<Rightarrow> int \<Rightarrow> int" "'v arith"
  | Minus "'v arith"

datatype (fv_boolean: 'v) boolean =
  true
  | false
  | Rel_Op "'v arith" "int \<Rightarrow> int \<Rightarrow> bool" "'v arith"
  | Bool_Op "'v boolean" "bool \<Rightarrow> bool \<Rightarrow> bool" "'v boolean"
  | Neg "'v boolean"

datatype 'v action =
  Asg 'v "'v arith" ("_ ::= _" [1000, 61] 61)
  | Bool "'v boolean"
  | Skip


section \<open>Memories\<close>

type_synonym 'v memory = "'v \<Rightarrow> int"


section \<open>Semantics\<close>

fun sem_arith :: "'v arith \<Rightarrow> 'v memory \<Rightarrow> int" where
  "sem_arith (Integer n) \<sigma> = n"
| "sem_arith (Var x) \<sigma> = \<sigma> x"
| "sem_arith (Arith_Op a1 op a2) \<sigma> = op (sem_arith a1 \<sigma>) (sem_arith a2 \<sigma>)"
| "sem_arith (Minus a) \<sigma> = - (sem_arith a \<sigma>)"

fun sem_bool :: "'v boolean \<Rightarrow> 'v memory \<Rightarrow> bool" where
  "sem_bool true \<sigma> = True"
| "sem_bool false \<sigma> = False"
| "sem_bool (Rel_Op a1 op a2) \<sigma> = op (sem_arith a1 \<sigma>) (sem_arith a2 \<sigma>)"
| "sem_bool (Bool_Op b1 op b2) \<sigma> = op (sem_bool b1 \<sigma>) (sem_bool b2 \<sigma>)"
| "sem_bool (Neg b) \<sigma> = (\<not>(sem_bool b \<sigma>))"

fun sem_action :: "'v action \<Rightarrow> 'v memory \<rightharpoonup> 'v memory" where
  "sem_action (x ::= a) \<sigma> = Some (\<sigma>(x := sem_arith a \<sigma>))"
| "sem_action (Bool b) \<sigma> = (if sem_bool b \<sigma> then Some \<sigma> else None)"
| "sem_action Skip \<sigma> = Some \<sigma>"


section \<open>Program Graphs\<close>

type_synonym ('n,'v) edge = "'n * 'v action * 'n"

type_synonym ('n,'v) program_graph = "(('n,'v) edge set \<times> 'n \<times> 'n)"

term "LTS.path_with_word :: ('n,'v) edge set \<Rightarrow> ('n list \<times> 'v action list) set"

section \<open>Execution Sequences\<close>

type_synonym ('n,'v) config = "'n * 'v memory"

fun initial_config_of where
  "initial_config_of (n,\<sigma>) (es,start,end) \<longleftrightarrow> n = start"

fun final_config_of where
  "final_config_of (n,\<sigma>) (es,start,end) \<longleftrightarrow> n = end"

inductive exe_step :: "('n,'v) program_graph \<Rightarrow> ('n,'v) config \<Rightarrow> 'v action \<Rightarrow> ('n,'v) config \<Rightarrow> bool" where
  "(q1, a, q2) \<in> es \<Longrightarrow> sem_action a \<sigma> = Some \<sigma>' \<Longrightarrow> exe_step (es,start,end) (q1,\<sigma>) a (q2,\<sigma>')"


section \<open>Reaching Definitions\<close>

type_synonym ('n,'v) triple = "'v * 'n option * 'n"

type_synonym ('n,'v) analysis_assignment = "'n \<Rightarrow> ('n,'v) triple set"


subsection \<open>What is defined on a path\<close>

fun def_action :: "'v action \<Rightarrow> 'v set" where
  "def_action (x ::= a) = {x}"
| "def_action (Bool b) = {}"
| "def_action Skip = {}"

abbreviation def_edge :: "('n,'v) edge \<Rightarrow> 'v set" where
  "def_edge == \<lambda>(q1, a, q2). def_action a"

definition triple_of :: "'v \<Rightarrow> ('n,'v) edge \<Rightarrow> ('n,'v) triple" where
  "triple_of == (\<lambda>x (q1, a, q2). (x, Some q1, q2))"

definition def_var :: "('n,'v) edge list \<Rightarrow> 'v \<Rightarrow> 'n \<Rightarrow> ('n,'v) triple" where
  "def_var \<pi> x start = (if (\<exists>e \<in> set \<pi>. x \<in> def_edge e)
                        then (triple_of x (last (filter (\<lambda>e. x \<in> def_edge e) \<pi>)))
                        else (x, None, start))"

definition def_path :: "('n list \<times> 'v action list) \<Rightarrow> 'n \<Rightarrow> ('n,'v) triple set" where
  "def_path \<pi> start = ((\<lambda>x. def_var (LTS.transition_list \<pi>) x start) ` UNIV)"

fun summarizes :: "('n,'v) analysis_assignment \<Rightarrow> ('n,'v) program_graph \<Rightarrow> bool" where
  "summarizes RD (es,start,end) \<longleftrightarrow> (\<forall>\<pi>. \<pi> \<in> LTS.path_with_word es \<longrightarrow> LTS.get_start \<pi> = start \<longrightarrow> def_path \<pi> start \<subseteq> RD (LTS.get_end \<pi>))"

(*
definition summarizes2 :: "('n,'v) analysis_assignment \<Rightarrow> ('n,'v) program_graph \<Rightarrow> bool" where
  "summarizes2 RD pg \<longleftrightarrow> (\<forall>\<pi> a b c. \<pi> \<in> LTS.path_with_word pg \<longrightarrow> LTS.get_start \<pi> = Start \<longrightarrow> (a, b, c) \<in> def_path \<pi> \<longrightarrow> (a, b, c) \<in> RD (LTS.get_end \<pi>))"
*) 

section \<open>Datalog programs and their solutions\<close>

datatype ('x,'e) identifier = DLVar 'x | DLElement 'e

datatype ('p,'x,'e) righthand = 
  Eql "('x,'e) identifier" "('x,'e) identifier" ("_ \<^bold>= _" [61, 61] 61)
  | Neql "('x,'e) identifier" "('x,'e) identifier" ("_ \<^bold>\<noteq> _" [61, 61] 61)
  | PosRh 'p "('x,'e) identifier list"
  | NegRh 'p "('x,'e) identifier list" ("\<^bold>\<not> _ _" [61, 61] 61)

datatype ('p,'x,'e) clause = Cls 'p "('x,'e) identifier list" "('p,'x,'e) righthand list" (* Why not righthand set? *)

type_synonym ('p,'x,'e) dl_program = "('p,'x,'e) clause set"

type_synonym ('x,'e) var_val = "'x \<Rightarrow> 'e"

type_synonym ('p,'e) pred_val = "'p \<Rightarrow> 'e list set"

type_synonym ('p,'x,'e) lefthand = "'p * ('x,'e) identifier list"

fun eval_id :: "('x,'e) var_val \<Rightarrow> ('x,'e) identifier \<Rightarrow> 'e" where
  "eval_id \<sigma> (DLVar x) = \<sigma> x"
| "eval_id \<sigma> (DLElement e) = e"

fun meaning_rh :: "('p,'x,'e) righthand \<Rightarrow> ('p,'e) pred_val \<Rightarrow> ('x,'e) var_val \<Rightarrow> bool" where
  "meaning_rh (a \<^bold>= a') \<rho> \<sigma> \<longleftrightarrow> eval_id \<sigma> a = eval_id  \<sigma> a'"
| "meaning_rh (a \<^bold>\<noteq> a') \<rho> \<sigma> \<longleftrightarrow> eval_id \<sigma> a \<noteq> eval_id \<sigma> a'"
| "meaning_rh (PosRh p ids) \<rho> \<sigma> \<longleftrightarrow> map (eval_id \<sigma>) ids \<in> \<rho> p"
| "meaning_rh (\<^bold>\<not> p ids) \<rho> \<sigma> \<longleftrightarrow> \<not> map (eval_id \<sigma>) ids \<in> \<rho> p"

fun meaning_lh :: "('p,'x,'e) lefthand \<Rightarrow> ('p,'e) pred_val \<Rightarrow> ('x,'e) var_val \<Rightarrow> bool" where
  "meaning_lh (p,ids) \<rho> \<sigma> \<longleftrightarrow> map (eval_id \<sigma>) ids \<in> \<rho> p"

fun meaning_cls :: "('p,'x,'e) clause \<Rightarrow> ('p,'e) pred_val \<Rightarrow> ('x,'e) var_val \<Rightarrow> bool" where
  "meaning_cls (Cls p ids rhs) \<rho> \<sigma> \<longleftrightarrow> ((\<forall>rh\<in>set rhs. meaning_rh rh \<rho> \<sigma>) \<longrightarrow> meaning_lh (p,ids) \<rho> \<sigma>)"

fun solves_rh :: "('p,'e) pred_val \<Rightarrow> ('p,'x,'e) righthand \<Rightarrow> bool" where (* Not in the book *)
  "solves_rh \<rho> rh \<longleftrightarrow> (\<forall>\<sigma>. meaning_rh rh \<rho> \<sigma>)"

definition solves_cls :: "('p,'e) pred_val \<Rightarrow> ('p,'x,'e) clause \<Rightarrow> bool" where
  "solves_cls \<rho> c \<longleftrightarrow> (\<forall>\<sigma>. meaning_cls c \<rho> \<sigma>)"

definition solves_program :: "('p,'e) pred_val \<Rightarrow> ('p,'x,'e) dl_program \<Rightarrow> bool" where
  "solves_program \<rho> dl \<longleftrightarrow> (\<forall>c \<in> dl. solves_cls \<rho> c)"


section \<open>Queries (not in the book?)\<close>

type_synonym ('p,'x,'e) query = "'p * ('x,'e) identifier list"

fun meaning_query :: "('p,'x,'e) query \<Rightarrow> ('p,'e) pred_val \<Rightarrow> ('x,'e) var_val \<Rightarrow> bool" where
  "meaning_query (p,ids) \<rho> \<sigma> \<longleftrightarrow> map (eval_id \<sigma>) ids \<in> \<rho> p"

fun solves_query :: "('p,'e) pred_val \<Rightarrow> ('p,'x,'e) query \<Rightarrow> bool" where
  "solves_query \<rho> (p,ids) \<longleftrightarrow> (\<forall>\<sigma>. meaning_query (p,ids) \<rho> \<sigma>)"


section \<open>Substitutions (not in the book?)\<close>

type_synonym ('x,'e) subst = "'x \<Rightarrow> ('x,'e) identifier"

fun subst_id :: "('x,'e) subst \<Rightarrow> ('x,'e) identifier \<Rightarrow> ('x,'e) identifier" where
  "subst_id \<sigma> (DLVar x) = \<sigma> x"
| "subst_id \<sigma> (DLElement e) = (DLElement e)"

fun subst_rh :: "('x,'e) subst \<Rightarrow> ('p,'x,'e) righthand \<Rightarrow>  ('p,'x,'e) righthand" where
  "subst_rh \<sigma> (a \<^bold>= a') = (subst_id \<sigma> a \<^bold>= subst_id \<sigma> a')"
| "subst_rh \<sigma> (a \<^bold>\<noteq> a') = (subst_id \<sigma> a \<^bold>\<noteq> subst_id \<sigma> a')"
| "subst_rh \<sigma> (PosRh p ids) = (PosRh p (map (subst_id \<sigma>) ids))"
| "subst_rh \<sigma> (\<^bold>\<not> p ids) = (\<^bold>\<not> p (map (subst_id \<sigma>) ids))"

fun subst_cls :: "('x,'e) subst \<Rightarrow> ('p,'x,'e) clause \<Rightarrow> ('p,'x,'e) clause" where
  "subst_cls \<sigma> (Cls p ids rhs) = Cls p (map (subst_id \<sigma>) ids) (map (subst_rh \<sigma>) rhs)"

definition compose :: "('x,'e) subst \<Rightarrow> ('x,'e) var_val \<Rightarrow> ('x,'e) var_val" where
  "compose \<mu> \<sigma> x = eval_id \<sigma> (\<mu> x)"


section \<open>Datalog lemmas\<close>

lemma solves_cls_iff_solves_rh: "solves_cls \<rho> (Cls p ids []) \<longleftrightarrow> solves_rh \<rho> (PosRh p ids)"
  using solves_cls_def by force

lemma solves_fact_query:
  assumes "solves_cls \<rho> (Cls p args [])"
  shows "solves_query \<rho> (p, args)"
  using assms unfolding solves_cls_def by auto

lemma resolution_last_rh:
  assumes "solves_cls \<rho> (Cls p args (rhs@[rh]))"
  assumes "solves_rh \<rho> rh"
  shows "solves_cls \<rho> (Cls p args (rhs))"
  using assms unfolding solves_cls_def by auto

lemma resolution_last_rh_query:
  assumes "solves_cls \<rho> (Cls p args (rhs@[PosRh p ids]))"
  assumes "solves_query \<rho> (p, ids)"
  shows "solves_cls \<rho> (Cls p args (rhs))"
  using assms by (force simp add: solves_cls_def)

lemma resolution_only_rh_query:
  assumes "solves_cls \<rho> (Cls p ids [PosRh p' ids'])"
  assumes "solves_query \<rho> (p', ids')"
  shows "solves_query \<rho> (p, ids)"
proof -
  from assms(2) have "\<forall>\<sigma>. meaning_rh (PosRh p' ids') \<rho> \<sigma>"
    by fastforce
  then have "solves_cls \<rho> (Cls p ids [])"
    using assms(1)
    by (metis self_append_conv2 solves_rh.elims(3) resolution_last_rh)
  then show "solves_query \<rho> (p, ids)"
    by (meson solves_fact_query)
qed

lemma resolution_all_rhs:
  assumes "solves_cls \<rho> (Cls p ids rhs)"
  assumes "\<forall>rh \<in> set rhs. solves_rh \<rho> rh"
  shows "solves_query \<rho> (p, ids)"
  using assms
  by (metis (full_types) meaning_cls.simps meaning_lh.simps meaning_query.simps solves_cls_def solves_query.elims(1) solves_rh.elims(2))

lemma substitution_lemma_lh: "meaning_lh (p, ids) \<rho> (compose \<mu> \<sigma>) \<longleftrightarrow> (meaning_lh (p, map (subst_id \<mu>) ids) \<rho> \<sigma>)"
proof
  assume "meaning_lh (p, ids) \<rho> (compose \<mu> \<sigma>)"
  then have "map (eval_id (compose \<mu> \<sigma>)) ids \<in> \<rho> p"
    by auto
  then have "map (eval_id \<sigma> \<circ> subst_id \<mu>) ids \<in> \<rho> p"
    by (smt (verit, ccfv_SIG) compose_def comp_apply eval_id.elims eval_id.simps(2) map_eq_conv subst_id.simps(1) subst_id.simps(2))
  then show "meaning_lh (p, map (subst_id \<mu>) ids) \<rho> \<sigma>"
    by auto
next
  assume "meaning_lh (p, map (subst_id \<mu>) ids) \<rho> \<sigma>"
  then have "map (eval_id \<sigma> \<circ> subst_id \<mu>) ids \<in> \<rho> p"
    by auto
  then have "map (eval_id (compose \<mu> \<sigma>)) ids \<in> \<rho> p"
    by (smt (verit, ccfv_threshold) compose_def comp_apply eval_id.elims eval_id.simps(2) map_eq_conv subst_id.simps(1) subst_id.simps(2))
  then show "meaning_lh (p, ids) \<rho> (compose \<mu> \<sigma>)"
    by auto
qed

lemma substitution_lemma_rh:"meaning_rh rh \<rho> (compose \<mu> \<sigma>) = meaning_rh (subst_rh \<mu> rh) \<rho> \<sigma>"
proof (induction rh)
  case (Eql x1 x2)
  then show ?case
    by (smt (verit) compose_def eval_id.elims eval_id.simps(2) meaning_rh.simps(1) subst_id.simps(1) subst_id.simps(2) subst_rh.simps(1)) 
next
  case (Neql x1 x2)
  then show ?case
    by (smt (verit, ccfv_threshold) compose_def eval_id.elims eval_id.simps(2) meaning_rh.simps(2) subst_id.simps(1) subst_id.simps(2) subst_rh.simps(2)) 
next
  case (PosRh x1 x2)
  have "map (eval_id (compose \<mu> \<sigma>)) x2 \<in> \<rho> x1 \<Longrightarrow> map (eval_id \<sigma> \<circ> subst_id \<mu>) x2 \<in> \<rho> x1"
    by (smt (verit) compose_def comp_apply eval_id.elims eval_id.simps(2) map_eq_conv subst_id.simps(1) subst_id.simps(2))
  moreover
  have "map (eval_id \<sigma> \<circ> subst_id \<mu>) x2 \<in> \<rho> x1 \<Longrightarrow> map (eval_id (compose \<mu> \<sigma>)) x2 \<in> \<rho> x1"
    by (smt (verit) compose_def comp_apply eval_id.elims eval_id.simps(2) map_eq_conv subst_id.simps(1) subst_id.simps(2))
  ultimately
  show ?case
    by auto
next
  case (NegRh x1 x2)
  have "map (eval_id (compose \<mu> \<sigma>)) x2 \<in> \<rho> x1 \<Longrightarrow> map (eval_id \<sigma> \<circ> subst_id \<mu>) x2 \<in> \<rho> x1"
    by (smt (verit, best) compose_def comp_apply eval_id.elims eval_id.simps(2) map_eq_conv subst_id.simps(1) subst_id.simps(2))
  moreover
  have "map (eval_id \<sigma> \<circ> subst_id \<mu>) x2 \<in> \<rho> x1 \<Longrightarrow> map (eval_id (compose \<mu> \<sigma>)) x2 \<in> \<rho> x1"
    by (smt (verit) compose_def comp_apply eval_id.elims eval_id.simps(2) map_eq_conv subst_id.simps(1) subst_id.simps(2))
  ultimately
  show ?case
    by auto
qed

lemma substitution_lemma_rhs: "(\<forall>rh\<in>set rhs. meaning_rh rh \<rho> (compose \<mu> \<sigma>)) \<longleftrightarrow> (\<forall>rh\<in>set (map (subst_rh \<mu>) rhs). meaning_rh rh \<rho> \<sigma>)"
  by (simp add: substitution_lemma_rh) 

lemma substitution_lemma_cls:
  "meaning_cls c \<rho> (compose \<mu> \<sigma>) \<longleftrightarrow> meaning_cls (subst_cls \<mu> c) \<rho> \<sigma>"
proof (induction c)
  case (Cls p ids rhs)
  have a: "(\<forall>rh\<in>set rhs. meaning_rh rh \<rho> (compose \<mu> \<sigma>)) \<longleftrightarrow> (\<forall>rh\<in>set (map (subst_rh \<mu>) rhs). meaning_rh rh \<rho> \<sigma>)"
    using substitution_lemma_rhs by blast
  have b: "meaning_lh (p, ids) \<rho> (compose \<mu> \<sigma>) \<longleftrightarrow> (meaning_lh (p, map (subst_id \<mu>) ids) \<rho> \<sigma>)"
    using substitution_lemma_lh by metis
  show ?case
    unfolding meaning_cls.simps
    using a b by auto
qed

lemma substitution_rule:
  assumes "solves_cls \<rho> c"
  shows "solves_cls \<rho> (subst_cls (\<mu>::('x,'e) subst) c)"
proof -
  show ?thesis
    unfolding solves_cls_def
  proof
    fix \<sigma> :: "'x \<Rightarrow> 'e"
    term "\<mu> :: 'x \<Rightarrow> ('x, 'e) identifier"
    from assms have "meaning_cls c \<rho> (compose \<mu> \<sigma>)"
      using solves_cls_def by auto
    then show "meaning_cls (subst_cls \<mu> c) \<rho> \<sigma>"
      using substitution_lemma_cls by blast
  qed
qed


section \<open>Stratification\<close>
type_synonym 'p strat = "'p \<Rightarrow> nat"
(* Maybe it should also mention the arity *)

fun rnk :: "'p strat \<Rightarrow> ('p,'x,'e) righthand \<Rightarrow> nat" where
  "rnk s (a \<^bold>= a') = 0"
| "rnk s (a \<^bold>\<noteq> a') = 0"
| "rnk s (PosRh p ids) = s p"
| "rnk s (\<^bold>\<not> p ids) = 1 + s p"

fun strat_wf_cls :: "'p strat \<Rightarrow> ('p,'x,'e) clause \<Rightarrow> bool" where
  "strat_wf_cls s (Cls p ids rhs) \<longleftrightarrow> (\<forall>rh \<in> set rhs. s p \<ge> rnk s rh)"

definition strat_wf :: "'p strat \<Rightarrow> ('p,'x,'e) dl_program \<Rightarrow> bool" where
  "strat_wf s dl \<longleftrightarrow> (\<forall>c \<in> dl. strat_wf_cls s c)"

fun pred_val_mod_strata :: "('p,'e) pred_val \<Rightarrow> 'p strat \<Rightarrow> nat \<Rightarrow> ('p,'e) pred_val"  ("_ \\_\\ _" 0) where 
  "(\<sigma> \\s\\ n) p = (if s p \<le> n then \<sigma> p else {})"

fun dl_program_mod_strata :: "('p,'x,'e) dl_program \<Rightarrow> 'p strat \<Rightarrow> nat \<Rightarrow> ('p,'x,'e) dl_program"  ("_ --_-- _" 0) where 
  "(dl -- s -- n) = {(Cls p ids rhs)| p ids rhs . (Cls p ids rhs) \<in> dl \<and> s(p) \<le> n}"

definition lt :: "('p,'e) pred_val \<Rightarrow> 'p strat \<Rightarrow> ('p,'e) pred_val \<Rightarrow> bool" ("_ \<sqsubset>_\<sqsubset> _") where
  "(\<rho> \<sqsubset>s\<sqsubset> \<rho>') \<longleftrightarrow> (\<exists>p. \<rho> p \<subset> \<rho>' p \<and>
                       (\<forall>p'. s p' = s p \<longrightarrow> \<rho>(p') \<subseteq> \<rho>'(p')) \<and>
                       (\<forall>p'. s p' < s p \<longrightarrow> \<rho>(p') = \<rho>'(p')))"

definition lte :: "('p,'e) pred_val \<Rightarrow> 'p strat \<Rightarrow> ('p,'e) pred_val \<Rightarrow> bool" ("_ \<sqsubseteq>_\<sqsubseteq> _") where
  "(\<rho> \<sqsubseteq>s\<sqsubseteq> \<rho>') \<longleftrightarrow> \<rho> = \<rho>' \<or> (\<rho> \<sqsubset>s\<sqsubset> \<rho>')"

definition least_solution :: "('p,'e) pred_val \<Rightarrow> ('p,'x,'e) dl_program \<Rightarrow> 'p strat \<Rightarrow> bool" where
  "least_solution \<sigma> dl s \<longleftrightarrow> solves_program \<sigma> dl \<and>
                             (\<forall>\<sigma>'. solves_program \<sigma>' dl \<longrightarrow> (\<sigma> \<sqsubseteq>s\<sqsubseteq> \<sigma>'))"

definition minimal_solution :: "('p,'e) pred_val \<Rightarrow> ('p,'x,'e) dl_program \<Rightarrow> 'p strat \<Rightarrow> bool" where
  "minimal_solution \<sigma> dl s \<longleftrightarrow> solves_program \<sigma> dl \<and>
                               (\<nexists>\<sigma>'. solves_program \<sigma>' dl \<and> (\<sigma>' \<sqsubset>s\<sqsubset> \<sigma>))"

(* René se her *)
(* Her er linket til det vi så på på nettet https://www.physicsforums.com/threads/difference-between-least-minimal-element.380114/ *)
lemma least_is_minimal:
  assumes "strat_wf s dl"
  shows "least_solution \<sigma> dl s \<longleftrightarrow> minimal_solution \<sigma> dl s"
  sorry (* Because \<sqsubset>s\<sqsubset> is a partial order with a least solution *)

(*
  Noter fra møde:
  Lattice

Partielt ordnet mængde

mængden:
  L løsningerne til datalog dl

ordning:
  \<sqsubseteq>


ordningen er partiel

for alle a \in L, b \in L.
  exists lub(a,b)
  exists glb(a,b)
*)


(*
lemma
  assumes "strat_wf s dl"
  shows "\<exists>\<sigma>. minimal_solution \<sigma> dl s"
  sorry

lemma unique_minimal:
  assumes "strat_wf s dl"
  assumes "least_solution \<sigma> dl s"
  assumes "least_solution \<sigma>' dl s"
  shows "\<sigma> = \<sigma>'"
  sorry
*)

lemma an_antisymmetry_lamma:
  assumes "\<forall>a b. r a b \<and> r b a \<longrightarrow> a = b"
  assumes "r y x \<and> x \<noteq> y"
  shows "\<not>r x y"
  using assms
  by blast 

lemma downward_strat:
  assumes "n > m"
  assumes "strat_wf s (dl --s-- n)"
  shows "strat_wf s (dl --s-- m)"
  using assms unfolding strat_wf_def by fastforce

lemma downward_strat2:
  assumes "strat_wf s dl"
  shows "strat_wf s (dl --s-- m)"
  using assms unfolding strat_wf_def by auto

lemma downward_solves:
  assumes "n > m"
  assumes "solves_program \<sigma> (dl --s-- n)"
  assumes "strat_wf s dl"
  shows "solves_program (\<sigma> \\s\\ m) (dl --s-- m)"
  unfolding solves_program_def
proof
  fix c
  assume a: "c \<in> (dl --s-- m)"
  then obtain p ids rhs where c_def: "c = Cls p ids rhs"
    by (cases c) auto

  have "c \<in> (dl --s-- n)"
    using a assms(1) by auto

  have "strat_wf s (dl --s-- m)"
    using assms(3) downward_strat2 by blast

  have "solves_cls (\<sigma> \\s\\ m) (Cls p ids rhs)"
    unfolding solves_cls_def
  proof 
    fix \<eta>
    have mm: "meaning_cls (Cls p ids rhs) \<sigma> \<eta>"
      using \<open>c \<in> (dl --s-- n)\<close> assms(2) c_def solves_cls_def solves_program_def by blast
    have "s p \<le> m"
      using \<open>c \<in> (dl --s-- m)\<close> c_def by fastforce
    moreover
    have "\<forall>rh \<in> set rhs. rnk s rh \<le> m"
      using \<open>c \<in> (dl --s-- m)\<close> assms(2) c_def dual_order.trans strat_wf_def
      by (metis (no_types, lifting) \<open>strat_wf s (dl --s-- m)\<close> calculation strat_wf_cls.simps)
    ultimately
    show "meaning_cls (Cls p ids rhs) (\<sigma> \\s\\ m) \<eta>"
      apply auto
      subgoal
        using mm
        apply auto
        subgoal for rh
          apply (cases rh)
             apply auto
           apply fastforce
          apply fastforce
          done
        done
      done
  qed
  then show "solves_cls (\<sigma> \\s\\ m) c"
    using c_def by auto
qed

lemma downward_solves2:
  assumes "solves_program \<sigma> dl"
  assumes "strat_wf s dl"
  shows "solves_program (\<sigma> \\s\\ m) (dl --s-- m)"
  unfolding solves_program_def
proof
  fix c
  assume "c \<in> (dl --s-- m)"
  then obtain p ids rhs where c_def: "c = Cls p ids rhs"
    by (cases c) auto
  
  have "solves_cls (\<sigma> \\s\\ m) (Cls p ids rhs)"
    unfolding solves_cls_def
  proof 
    fix \<eta>
    have mm: "meaning_cls (Cls p ids rhs) \<sigma> \<eta>"
      by (smt (verit) \<open>c \<in> (dl --s-- m)\<close> assms(1) c_def dl_program_mod_strata.simps mem_Collect_eq solves_cls_def solves_program_def)
    have "s p \<le> m"
      using \<open>c \<in> (dl --s-- m)\<close> c_def by fastforce
    moreover
    have "\<forall>rh \<in> set rhs. rnk s rh \<le> m"
      using \<open>c \<in> (dl --s-- m)\<close> assms(2) c_def dual_order.trans strat_wf_def by fastforce
    ultimately
    show "meaning_cls (Cls p ids rhs) (\<sigma> \\s\\ m) \<eta>"
      apply auto
      subgoal
        using mm
        apply auto
        subgoal for rh
          apply (cases rh)
             apply auto
           apply fastforce
          apply fastforce
          done
        done
      done
  qed
  then show "solves_cls (\<sigma> \\s\\ m) c"
    using c_def by auto
qed
  

lemma downward_solution:
  assumes "n > m"
  assumes "strat_wf s dl"
  assumes "least_solution \<sigma> (dl --s-- n) s"
  shows "least_solution (\<sigma> \\s\\ m) (dl --s-- m) s"
proof (rule ccontr)
  assume a: "\<not> least_solution (\<sigma> \\s\\ m) (dl --s-- m) s"
  have strrr: "strat_wf s (dl --s-- m)"
    using assms(2) downward_strat2 by auto
  have strrrr: "strat_wf s (dl --s-- n)"
    using assms(2) downward_strat2 by auto
  from a have "\<not> minimal_solution  (\<sigma> \\s\\ m) (dl --s-- m) s"
    using least_is_minimal[of s] strrr by metis
  moreover 
  have "solves_program (\<sigma> \\s\\ m) (dl --s-- m)"
    using assms(1,3) assms(2) downward_solves least_solution_def by blast
  ultimately
  have "(\<exists>\<sigma>'. solves_program \<sigma>' (dl --s-- m) \<and> (\<sigma>' \<sqsubset>s\<sqsubset> (\<sigma> \\s\\ m)))"
    unfolding minimal_solution_def by auto
  then obtain \<sigma>' where tt: "solves_program \<sigma>' (dl --s-- m)" and ttt: "(\<sigma>' \<sqsubset>s\<sqsubset> (\<sigma> \\s\\ m))"
    by auto
  then have "\<exists>p. \<sigma>' p \<subset> (\<sigma> \\s\\ m) p \<and> 
                    (\<forall>p'. s p' = s p \<longrightarrow> \<sigma>' p' \<subseteq> (\<sigma> \\s\\ m) p') \<and> 
                    (\<forall>p'. s p' < s p \<longrightarrow> \<sigma>' p' = (\<sigma> \\s\\ m) p')"
    unfolding lt_def by auto
  then obtain p where a: "\<sigma>' p \<subset> (\<sigma> \\s\\ m) p" and
                      b:"(\<forall>p'. s p' = s p \<longrightarrow> \<sigma>' p' \<subseteq> (\<sigma> \\s\\ m) p')" and
                      c:"(\<forall>p'. s p' < s p \<longrightarrow> \<sigma>' p' = (\<sigma> \\s\\ m) p')"
    by auto
  define \<sigma>'' where "\<sigma>'' == \<lambda>p. (if s p \<le> m then \<sigma>' p else UNIV)"

  have "\<sigma>'' p \<subset> \<sigma> p"
    using a
    by (metis \<sigma>''_def empty_iff leD pred_val_mod_strata.simps subsetI) 
  moreover
  have "(\<forall>p'. s p' = s p \<longrightarrow> \<sigma>'' p' \<subseteq> \<sigma> p')"
    using b
    by (metis \<sigma>''_def calculation pred_val_mod_strata.simps top.extremum_strict)
  moreover
  have "(\<forall>p'. s p' < s p \<longrightarrow> \<sigma>'' p' = \<sigma> p')"
    using \<sigma>''_def c calculation(1) by force
  ultimately
  have "(\<sigma>'' \<sqsubset>s\<sqsubset> \<sigma>)"
    by (metis lt_def)
  moreover
  have "solves_program \<sigma>'' (dl --s-- n)"
    unfolding solves_program_def
  proof
    fix c
    assume a: "c \<in> (dl --s-- n)"
    then obtain p ids rhs where c_def: "c = Cls p ids rhs"
      by (cases c) auto

    have "solves_cls \<sigma>'' (Cls p ids rhs)"
      unfolding solves_cls_def
    proof
      fix \<eta>
      
      show "meaning_cls (Cls p ids rhs) \<sigma>'' \<eta>"
      proof (cases "s p \<le> m")
        case True
        then have "c \<in> (dl --s-- m)"
          using a c_def by auto
        then have gugu: "meaning_cls (Cls p ids rhs) \<sigma>' \<eta>"
          using tt c_def solves_cls_def solves_program_def by blast
        from gugu show ?thesis
          apply -
          unfolding \<sigma>''_def
          apply auto
          subgoal for rh
            apply (cases rh)
               apply fastforce
              apply fastforce
             apply (smt (verit, ccfv_threshold) \<open>c \<in> (dl --s-- n)\<close> c_def dual_order.trans meaning_rh.simps(3) rnk.simps(3) strat_wf_cls.simps strat_wf_def strrrr)
            apply (smt (z3) UNIV_I meaning_rh.simps(4))
            done
          done
      next
        case False
        then show ?thesis
          by (simp add: \<sigma>''_def)
      qed
    qed
    then show "solves_cls \<sigma>'' c"
      using c_def by blast
  qed
  ultimately
  have "\<not>minimal_solution \<sigma> (dl --s-- n) s"
    unfolding minimal_solution_def by auto
  then have "\<not>least_solution \<sigma> (dl --s-- n) s" 
    using least_is_minimal[of s "(dl --s-- n)" \<sigma>] strrrr by auto
  then show "False"
    using assms(3) by auto
qed

lemma downward_solution2:
  assumes "strat_wf s dl"
  assumes "least_solution \<sigma> dl s"
  shows "least_solution (\<sigma> \\s\\ m) (dl --s-- m) s"
proof (rule ccontr)
  assume a: "\<not> least_solution (\<sigma> \\s\\ m) (dl --s-- m) s"
  have strrr: "strat_wf s (dl --s-- m)"
    using assms(1) downward_strat2 by auto
  from a have "\<not> minimal_solution  (\<sigma> \\s\\ m) (dl --s-- m) s"
    using least_is_minimal[of s] strrr by metis
  moreover 
  have "solves_program (\<sigma> \\s\\ m) (dl --s-- m)"
    using assms(1) assms(2) downward_solves2 least_solution_def by blast
  ultimately
  have "(\<exists>\<sigma>'. solves_program \<sigma>' (dl --s-- m) \<and> (\<sigma>' \<sqsubset>s\<sqsubset> (\<sigma> \\s\\ m)))"
    unfolding minimal_solution_def by auto
  then obtain \<sigma>' where tt: "solves_program \<sigma>' (dl --s-- m)" and ttt: "(\<sigma>' \<sqsubset>s\<sqsubset> (\<sigma> \\s\\ m))"
    by auto
  then have "\<exists>p. \<sigma>' p \<subset> (\<sigma> \\s\\ m) p \<and> 
                    (\<forall>p'. s p' = s p \<longrightarrow> \<sigma>' p' \<subseteq> (\<sigma> \\s\\ m) p') \<and> 
                    (\<forall>p'. s p' < s p \<longrightarrow> \<sigma>' p' = (\<sigma> \\s\\ m) p')"
    unfolding lt_def by auto
  then obtain p where a: "\<sigma>' p \<subset> (\<sigma> \\s\\ m) p" and
                      b:"(\<forall>p'. s p' = s p \<longrightarrow> \<sigma>' p' \<subseteq> (\<sigma> \\s\\ m) p')" and
                      c:"(\<forall>p'. s p' < s p \<longrightarrow> \<sigma>' p' = (\<sigma> \\s\\ m) p')"
    by auto
  define \<sigma>'' where "\<sigma>'' == \<lambda>p. (if s p \<le> m then \<sigma>' p else UNIV)"

  have "\<sigma>'' p \<subset> \<sigma> p"
    using a
    by (metis \<sigma>''_def empty_iff leD pred_val_mod_strata.simps subsetI) 
  moreover
  have "(\<forall>p'. s p' = s p \<longrightarrow> \<sigma>'' p' \<subseteq> \<sigma> p')"
    using b
    by (metis \<sigma>''_def calculation pred_val_mod_strata.simps top.extremum_strict)
  moreover
  have "(\<forall>p'. s p' < s p \<longrightarrow> \<sigma>'' p' = \<sigma> p')"
    using \<sigma>''_def c calculation(1) by force
  ultimately
  have "(\<sigma>'' \<sqsubset>s\<sqsubset> \<sigma>)"
    by (metis lt_def)
  moreover
  have "solves_program \<sigma>'' dl"
    unfolding solves_program_def
  proof
    fix c
    assume a: "c \<in> dl"
    then obtain p ids rhs where c_def: "c = Cls p ids rhs"
      by (cases c) auto

    have "solves_cls \<sigma>'' (Cls p ids rhs)"
      unfolding solves_cls_def
    proof
      fix \<eta>
      show "meaning_cls (Cls p ids rhs) \<sigma>'' \<eta>"
      proof (cases "s p \<le> m")
        case True
        then have "c \<in> (dl --s-- m)"
          using a c_def by auto
        then have gugu: "meaning_cls (Cls p ids rhs) \<sigma>' \<eta>"
          using tt c_def solves_cls_def solves_program_def by blast
        from gugu show ?thesis
          apply -
          unfolding \<sigma>''_def
          apply auto
          subgoal for rh
            apply (cases rh)
               apply fastforce
              apply fastforce
            using \<open>c \<in> dl\<close> c_def dual_order.trans meaning_rh.simps(3) rnk.simps(3) strat_wf_cls.simps strat_wf_def
            apply (smt (verit, ccfv_SIG) assms(1))
             apply (smt (z3) UNIV_I meaning_rh.simps(4))
            done
          done
      next
        case False
        then show ?thesis
          by (simp add: \<sigma>''_def)
      qed
    qed
    then show "solves_cls \<sigma>'' c"
      using c_def by blast
  qed
  ultimately
  have "\<not>minimal_solution \<sigma> dl s"
    unfolding minimal_solution_def by auto
  then have "\<not>least_solution \<sigma> dl s" 
    using least_is_minimal[of s "dl" \<sigma>] assms(1) by simp 
  then show "False"
    using assms(2) by auto
qed


section \<open>Reaching Definitions in Datalog\<close>

datatype ('n,'v) RD_elem =
  RD_Node 'n
  | RD_Var 'v
  | Questionmark

datatype RD_var =
   the_\<u>
   | the_\<v>
   | the_\<w>

datatype RD_pred =
   the_RD1
   | the_VAR

abbreviation Encode_Node :: "'n \<Rightarrow> (RD_var, ('n, 'v) RD_elem) identifier" where
  "Encode_Node n == DLElement (RD_Node n)"

fun Encode_Node_Q :: "'n option \<Rightarrow> (RD_var, ('n, 'v) RD_elem) identifier" where
  "Encode_Node_Q (Some n) = DLElement (RD_Node n)"
| "Encode_Node_Q None = DLElement Questionmark"

abbreviation Encode_Var :: "'v \<Rightarrow> (RD_var, ('n, 'v) RD_elem) identifier" where
  "Encode_Var v == DLElement (RD_Var v)"

abbreviation RD1_Cls :: "(RD_var, 'e) identifier list \<Rightarrow> (RD_pred, RD_var, 'e) righthand list \<Rightarrow> (RD_pred, RD_var, 'e) clause" ("RD1\<langle>_\<rangle> :- _ .") where 
   "RD1\<langle>args\<rangle> :- ls. \<equiv> Cls the_RD1 args ls"

abbreviation VAR_Cls :: "'v \<Rightarrow> (RD_pred, RD_var, ('n, 'v) RD_elem) clause" ("VAR\<langle>_\<rangle> :-.") where
   "VAR\<langle>x\<rangle> :-. == Cls the_VAR [Encode_Var x] []"

abbreviation RD1_Query :: "(RD_var, 'e) identifier list \<Rightarrow> (RD_pred, RD_var, 'e) query" ("RD1\<langle>_\<rangle>.") where 
   "RD1\<langle>args\<rangle>. \<equiv> (the_RD1, args)"

abbreviation VAR_Query :: "'v \<Rightarrow> (RD_pred, RD_var, ('n, 'v) RD_elem) query" ("VAR\<langle>_\<rangle>.") where 
   "VAR\<langle>x\<rangle>. \<equiv> (the_VAR, [Encode_Var x])"


abbreviation "RD1 == PosRh the_RD1"
abbreviation "VAR == PosRh the_VAR"

abbreviation \<u> :: "(RD_var, 'a) identifier" where
  "\<u> == DLVar the_\<u>"

abbreviation \<v> :: "(RD_var, 'a) identifier" where
  "\<v> == DLVar the_\<v>"

abbreviation \<w> :: "(RD_var, 'a) identifier" where
   "\<w> == DLVar the_\<w>"

fun ana_edge :: "('n, 'v) edge \<Rightarrow> (RD_pred, RD_var, ('n,'v) RD_elem) clause set" where
  "ana_edge (q\<^sub>o, x ::= a, q\<^sub>s) =
     {
        RD1\<langle>[Encode_Node q\<^sub>s, \<u>, \<v>, \<w>]\<rangle> :-
          [
            RD1[Encode_Node q\<^sub>o, \<u>, \<v>, \<w>],
            \<u> \<^bold>\<noteq> (Encode_Var x)
          ].
        ,
        RD1\<langle>[Encode_Node q\<^sub>s, Encode_Var x, Encode_Node q\<^sub>o, Encode_Node q\<^sub>s]\<rangle> :- [].
     }"
| "ana_edge (q\<^sub>o, Bool b, q\<^sub>s) =
     {
       RD1\<langle>[Encode_Node q\<^sub>s, \<u>, \<v>, \<w>]\<rangle> :-
         [
           RD1[Encode_Node q\<^sub>o, \<u>, \<v>, \<w>]
         ].
     }"
| "ana_edge (q\<^sub>o, Skip, q\<^sub>s) =
     {
       RD1\<langle>[Encode_Node q\<^sub>s, \<u>, \<v>, \<w>]\<rangle> :-
         [
           RD1[Encode_Node q\<^sub>o, \<u>, \<v>, \<w>]
         ].
     }"

definition ana_entry_node :: "'n \<Rightarrow> (RD_pred, RD_var, ('n,'v) RD_elem) clause set" where
  "ana_entry_node start = 
     {
       RD1\<langle>[Encode_Node start, \<u>, DLElement Questionmark, Encode_Node start]\<rangle> :-
         [
           VAR[\<u>]
         ].
     }"


fun ana_pg :: "('n, 'v) program_graph \<Rightarrow> (RD_pred, RD_var, ('n,'v) RD_elem) clause set" where
  "ana_pg (es,start,end) = \<Union>(ana_edge ` es) \<union> ana_entry_node start"

(* This makes VAR(x) true for the variables in the pg. This is not expanded so much on in the book. *)
definition var_contraints :: "(RD_pred, RD_var, ('n,'v) RD_elem) clause set" where
  "var_contraints = VAR_Cls ` UNIV"
(* Only makes sense if UNIV is finite. Alternatively I could calculate what variables are in
   the program and map VAR_Cls onto that set. *)


(* Jeg skal på en eller anden måde trylle datalog programmet om til en analysis assignment.
   Eller definere hvad det betyder for programmet at det er en analysis assignment.
   Eller definere hvad det betyder at \<rho> er en analysis assignment.
 *)

type_synonym ('n,'v) quadruple = "'n *'v * 'n option * 'n"

fun summarizes_dl :: "(RD_pred,('n,'v) RD_elem) pred_val \<Rightarrow> ('n,'v) program_graph \<Rightarrow> bool" where
  "summarizes_dl \<rho> (es,start,end) \<longleftrightarrow> (\<forall>\<pi> x q1 q2. \<pi> \<in> LTS.path_with_word es \<longrightarrow> LTS.get_start \<pi> = start \<longrightarrow> (x,q1,q2) \<in> def_path \<pi> start \<longrightarrow> 
     solves_query \<rho> (RD1\<langle>[Encode_Node (LTS.get_end \<pi>), Encode_Var x, Encode_Node_Q q1, Encode_Node q2]\<rangle>.))"

lemma def_var_x: "fst (def_var ts x start) = x"
  unfolding def_var_def by (simp add: case_prod_beta triple_of_def)

lemma last_def_transition:
  assumes "length ss = length w"
  assumes "x \<in> def_action l"
  assumes "(x, q1, q2) \<in> def_path (ss @ [s, s'], w @ [l]) start"
  shows "Some s = q1 \<and> s' = q2"
proof -
  obtain xa where xa_p: "(x, q1, q2) = def_var (transition_list (ss @ [s], w) @ [(s, l, s')]) xa start"
    by (metis (no_types, lifting) assms(1) assms(3) def_path_def imageE transition_list_reversed_simp)
  show ?thesis
  proof (cases "xa = x")
    case True
    then show ?thesis 
      using assms xa_p unfolding def_var_def triple_of_def by auto
  next
    case False
    then show ?thesis
      by (metis xa_p def_var_x fst_conv)
  qed
qed

lemma not_last_def_transition:
  assumes "length ss = length w"
  assumes "x \<notin> def_action l"
  assumes "(x, q1, q2) \<in> def_path (ss @ [s, s'], w @ [l]) start"
  shows "(x, q1, q2) \<in> def_path (ss @ [s], w) start"
proof -
  obtain y where y_p: "(x, q1, q2) = def_var (transition_list (ss @ [s], w) @ [(s, l, s')]) y start"
    by (metis (no_types, lifting) assms(1) assms(3) def_path_def imageE transition_list_reversed_simp)
  have " (x, q1, q2) \<in> range (\<lambda>x. def_var (transition_list (ss @ [s], w)) x start)"
  proof (cases "y = x")
    case True
    then show ?thesis 
      using assms y_p unfolding def_var_def triple_of_def by auto
  next
    case False
    then show ?thesis
      by (metis y_p def_var_x fst_conv)
  qed
  then show ?thesis
    by (simp add: def_path_def)
qed

lemma RD_sound': 
  assumes "(ss,w) \<in> LTS.path_with_word es"
  assumes "solves_program \<rho> (var_contraints \<union> ana_pg (es, start, end))"
  assumes "LTS.get_start (ss,w) = start"
  assumes "(x,q1,q2) \<in> def_path (ss,w) start"
  shows "solves_query \<rho> RD1\<langle>[Encode_Node (LTS.get_end (ss,w)), Encode_Var x, Encode_Node_Q q1, Encode_Node q2]\<rangle>."
  using assms 
proof (induction rule: LTS.path_with_word_induct_reverse[OF assms(1)])
  case (1 s)
  have "VAR\<langle>x\<rangle> :-. \<in> var_contraints"
    unfolding var_contraints_def by auto
  from assms(2) this have "solves_cls \<rho> (VAR\<langle>x\<rangle> :-.)"
    unfolding solves_program_def by auto  
  then have "\<forall>y. meaning_cls (VAR\<langle>x\<rangle> :-.) \<rho> y"
    unfolding solves_cls_def by auto
  then have x_sat: "[RD_Var x] \<in> \<rho> the_VAR"
    by auto

  have "RD1\<langle>[Encode_Node start, \<u>, DLElement Questionmark, Encode_Node start]\<rangle> :-
         [
           VAR[\<u>]
         ]. \<in> ana_pg (es, start, end)"
    by (simp add: ana_entry_node_def)
  then have "(solves_cls \<rho> (RD1\<langle>[Encode_Node start, \<u>, DLElement Questionmark, Encode_Node start]\<rangle> :-
         [
           VAR[\<u>]
         ].))"
    using assms(2) unfolding solves_program_def by auto 
   then have "\<forall>y. meaning_cls (RD1\<langle>[Encode_Node start, \<u>, DLElement Questionmark, Encode_Node start]\<rangle> :-
         [
           VAR[\<u>]
         ].) \<rho> y"
     unfolding solves_cls_def by metis
   then have "meaning_cls (RD1\<langle>[Encode_Node start, \<u>, DLElement Questionmark, Encode_Node start]\<rangle> :-
         [
           VAR[\<u>]
         ].) \<rho> (\<lambda>v. RD_Var x)"
     by presburger
   then have "[RD_Var x] \<in> \<rho> the_VAR \<longrightarrow> [RD_Node start, RD_Var x, Questionmark, RD_Node start] \<in> \<rho> the_RD1"
     by simp
   then have "[RD_Node start, RD_Var x, Questionmark, RD_Node start] \<in> \<rho> the_RD1"
     using x_sat by auto

   from this 1 show ?case
    unfolding LTS.LTS.get_end_def def_path_def def_var_def LTS.get_start_def by auto
next
  case (2 ss s w l s')
  from 2(1) have len: "length ss = length w"
    using LTS.path_with_word_length by force
  show ?case 
  proof(cases "x \<in> def_action l")
    case True
    then have sq: "Some s = q1 \<and> s' = q2" using 2(7)
      (* otherwise (x, q1, q2) would have been "overwritten" by (x, s, s') *)
      using last_def_transition[of ss w x l q1 q2 s s'] len by auto
    from True have "\<exists>e. (s,x ::= e,s') \<in> es"
      using "2.hyps"(2) by (cases l) auto
    then have "RD1\<langle>[Encode_Node q2, Encode_Var x, Encode_Node_Q q1, Encode_Node q2]\<rangle> :- []. \<in> ana_pg (es, start, end)"
      using True ana_pg.simps sq by fastforce
    then have "solves_cls \<rho> (RD1\<langle>[Encode_Node q2, Encode_Var x, Encode_Node_Q q1, Encode_Node q2]\<rangle> :- [].)"
      using 2(5) unfolding solves_program_def by auto
    then have "solves_query \<rho> RD1\<langle>[Encode_Node q2, Encode_Var x, Encode_Node_Q q1, Encode_Node q2]\<rangle>."
      using solves_fact_query by metis 
    then show ?thesis
      by (simp add: LTS.get_end_def sq)
  next
    case False
    then have x_is_def: "(x, q1, q2) \<in> def_path (ss @ [s], w) start" using 2(7)
      using not_last_def_transition len by force
    then have "solves_query \<rho> (RD1\<langle>[Encode_Node (LTS.get_end (ss @ [s], w)), Encode_Var x, Encode_Node_Q q1, Encode_Node q2]\<rangle>.)"
    proof -
      have "(ss @ [s], w) \<in> LTS.path_with_word es"
        using 2(1) by auto
      moreover
      have "solves_program \<rho> (var_contraints \<union> ana_pg (es,start,end))"
        using 2(5) by auto
      moreover
      have "LTS.get_start (ss @ [s], w) = start"
        using 2(6)
        by (metis append_self_conv2 fst_conv LTS.get_start_def hd_append2 list.sel(1)) 
      moreover
      have "(x, q1, q2) \<in> def_path (ss @ [s], w) start"
        using x_is_def by auto
      ultimately
      show "solves_query \<rho> (the_RD1, [Encode_Node (LTS.get_end (ss @ [s], w)), Encode_Var x, Encode_Node_Q q1, Encode_Node q2])"
        using 2(3) by auto
    qed
    then have ind: "solves_query \<rho> (RD1\<langle>[Encode_Node s, Encode_Var x, Encode_Node_Q q1, Encode_Node q2]\<rangle>.)"
      by (simp add: LTS.get_end_def)
    define \<sigma> where "\<sigma> = undefined(the_\<u> := Encode_Var x, the_\<v> := Encode_Node_Q q1, the_\<w> := Encode_Node q2)"
    show ?thesis
    proof (cases l)
      case (Asg y e)
      have xy: "x \<noteq> y"
        using False Asg by auto
      then have xy': "solves_rh \<rho> (Encode_Var x \<^bold>\<noteq> Encode_Var y)"
        by auto
      have "(s, y ::= e, s') \<in> es"
        using "2.hyps"(2) Asg by auto
      then have "RD1\<langle>[Encode_Node s', \<u>, \<v>, \<w>]\<rangle> :-
          [
            RD1[Encode_Node s, \<u>, \<v>, \<w>],
            \<u> \<^bold>\<noteq> (Encode_Var y)
          ]. \<in> ana_pg (es,start,end)"
        unfolding ana_pg.simps by force
      from this False have "solves_cls \<rho> (RD1\<langle>[Encode_Node s', \<u>, \<v>, \<w>]\<rangle> :-
          [
            RD1[Encode_Node s, \<u>, \<v>, \<w>],
            \<u> \<^bold>\<noteq> (Encode_Var y)
          ].)"
        by (meson "2.prems"(2) UnCI solves_program_def)
      moreover have "subst_cls \<sigma> (RD1\<langle>[Encode_Node s', \<u>, \<v>, \<w>]\<rangle> :-
          [
            RD1[Encode_Node s, \<u>, \<v>, \<w>],
            \<u> \<^bold>\<noteq> (Encode_Var y)
          ].) = RD1\<langle>[Encode_Node s', Encode_Var x, Encode_Node_Q q1, Encode_Node q2]\<rangle> :- [RD1 [Encode_Node s,  Encode_Var x, Encode_Node_Q q1, Encode_Node q2], Encode_Var x \<^bold>\<noteq> Encode_Var y] ."
        unfolding \<sigma>_def by auto
      ultimately
      have "solves_cls \<rho> (RD1\<langle>[Encode_Node s', Encode_Var x, Encode_Node_Q q1, Encode_Node q2]\<rangle> :- [RD1 [Encode_Node s,  Encode_Var x, Encode_Node_Q q1, Encode_Node q2], Encode_Var x \<^bold>\<noteq> Encode_Var y] .)"
        unfolding solves_cls_def by (metis substitution_lemma_cls)
      then have "solves_cls \<rho> RD1\<langle>[Encode_Node s', Encode_Var x, Encode_Node_Q q1, Encode_Node q2]\<rangle> :- [RD1 [Encode_Node s,  Encode_Var x, Encode_Node_Q q1, Encode_Node q2]] ."
        using xy' resolution_last_rh by (metis (no_types, lifting) Cons_eq_append_conv) 
      then have "solves_cls \<rho> RD1\<langle>[Encode_Node s', Encode_Var x, Encode_Node_Q q1, Encode_Node q2]\<rangle> :- []."
        using ind using resolution_last_rh_query[of \<rho> the_RD1 ] by (metis append.left_neutral) 
      then have "solves_query \<rho> (RD1\<langle>[Encode_Node s', Encode_Var x, Encode_Node_Q q1, Encode_Node q2]\<rangle>.)"
        using solves_fact_query by metis
      then show ?thesis
        by (simp add: LTS.get_end_def)
    next
      case (Bool b)
      have "(s, Bool b, s') \<in> es"
        using "2.hyps"(2) Bool by auto
      then have "RD1\<langle>[Encode_Node s', \<u>, \<v>, \<w>]\<rangle> :-
         [
           RD1[Encode_Node s, \<u>, \<v>, \<w>]
         ]. \<in> ana_pg (es,start,end)"
        unfolding ana_pg.simps by force
      then have "solves_cls \<rho> (RD1\<langle>[Encode_Node s', \<u>, \<v>, \<w>]\<rangle> :- [RD1[Encode_Node s, \<u>, \<v>, \<w>]].)"
        by (meson "2.prems"(2) UnCI solves_program_def)
      moreover have "subst_cls \<sigma> (RD1\<langle>[Encode_Node s', \<u>, \<v>, \<w>]\<rangle> :- [RD1[Encode_Node s, \<u>, \<v>, \<w>]].) =
                     RD1\<langle>[Encode_Node s', Encode_Var x, Encode_Node_Q q1, Encode_Node q2]\<rangle> :- [RD1[Encode_Node s, Encode_Var x, Encode_Node_Q q1, Encode_Node q2]]."
        unfolding \<sigma>_def by auto
      ultimately have "solves_cls \<rho> (RD1\<langle>[Encode_Node s', Encode_Var x, Encode_Node_Q q1, Encode_Node q2]\<rangle> :- [RD1[Encode_Node s, Encode_Var x, Encode_Node_Q q1, Encode_Node q2]].)"
        by (metis substitution_rule)
      then have "solves_query \<rho> (the_RD1, [Encode_Node s', Encode_Var x, Encode_Node_Q q1, Encode_Node q2])"
        using ind
        by (meson resolution_only_rh_query)
      then show ?thesis
        by (simp add: LTS.get_end_def)
    next
      case Skip
      have "(s, Skip, s') \<in> es"
        using "2.hyps"(2) Skip by auto
      then have "RD1\<langle>[Encode_Node s', \<u>, \<v>, \<w>]\<rangle> :-
         [
           RD1[Encode_Node s, \<u>, \<v>, \<w>]
         ]. \<in> ana_pg (es,start,end)"
        unfolding ana_pg.simps by force
      then have "solves_cls \<rho> (RD1\<langle>[Encode_Node s', \<u>, \<v>, \<w>]\<rangle> :- [RD1 [Encode_Node s, \<u>, \<v>, \<w>]] .)"
        by (meson "2.prems"(2) UnCI solves_program_def)
      moreover
      have "subst_cls \<sigma> (RD1\<langle>[Encode_Node s', \<u>, \<v>, \<w>]\<rangle> :- [RD1 [Encode_Node s, \<u>, \<v>, \<w>]] .) =
            RD1\<langle>[Encode_Node s', Encode_Var x, Encode_Node_Q q1, Encode_Node q2]\<rangle>  :- [RD1 [Encode_Node s, Encode_Var x, Encode_Node_Q q1, Encode_Node q2]]."
        unfolding \<sigma>_def by auto
      ultimately 
      have "solves_cls \<rho> RD1\<langle>[Encode_Node s', Encode_Var x, Encode_Node_Q q1, Encode_Node q2]\<rangle>  :- [RD1 [Encode_Node s, Encode_Var x, Encode_Node_Q q1, Encode_Node q2]]."
        by (metis substitution_rule)
      from resolution_only_rh_query[OF this ind] have "solves_query \<rho> (the_RD1, [Encode_Node s', Encode_Var x, Encode_Node_Q q1, Encode_Node q2])"
        .
      then show ?thesis
        by (simp add: LTS.get_end_def)
    qed
  qed
qed

lemma RD_sound:
  assumes "solves_program \<rho> (var_contraints \<union> ana_pg pg)"
  shows "summarizes_dl \<rho> pg"
  using assms RD_sound' by (cases pg) force 


section \<open>Bitvector framework\<close>

datatype BV_pred =
   the_BV
   | the_kill
   | the_gen

datatype BV_var =
   the_\<uu>

abbreviation "BV == PosRh the_BV"
abbreviation "kill == PosRh the_kill"
abbreviation NegRh_kill ("\<^bold>\<not>kill") where
  "\<^bold>\<not>kill \<equiv> NegRh the_kill"
abbreviation "gen == PosRh the_gen"

fun s_BV :: "BV_pred \<Rightarrow> nat" where 
  "s_BV the_kill = 0"
| "s_BV the_gen = 0"
| "s_BV the_BV = 1"

abbreviation BV_Cls :: "(BV_var, 'e) identifier list \<Rightarrow> (BV_pred, BV_var, 'e) righthand list \<Rightarrow> (BV_pred, BV_var, 'e) clause" ("BV\<langle>_\<rangle> :- _ .") where 
   "BV\<langle>args\<rangle> :- ls. \<equiv> Cls the_BV args ls"

abbreviation kill_Cls :: "(BV_var, 'e) identifier list \<Rightarrow> (BV_pred, BV_var, 'e) righthand list \<Rightarrow> (BV_pred, BV_var, 'e) clause" ("kill\<langle>_\<rangle> :- _ .") where 
   "kill\<langle>args\<rangle> :- ls. \<equiv> Cls the_kill args ls"

abbreviation genn_Cls :: "(BV_var, 'e) identifier list \<Rightarrow> (BV_pred, BV_var, 'e) righthand list \<Rightarrow> (BV_pred, BV_var, 'e) clause" ("gen\<langle>_\<rangle> :- _ .") where 
   "gen\<langle>args\<rangle> :- ls. \<equiv> Cls the_gen args ls"

abbreviation BV_Query :: "(BV_var, 'e) identifier list \<Rightarrow> (BV_pred, BV_var, 'e) query" ("BV\<langle>_\<rangle>.") where 
   "BV\<langle>args\<rangle>. \<equiv> (the_BV, args)"

datatype ('n,'v,'elem) BV_elem =
  BV_Node 'n
  | BV_Elem 'elem
  | BV_Action "'v action"

abbreviation \<uu> :: "(BV_var, 'a) identifier" where
  "\<uu> == DLVar the_\<uu>"

abbreviation Encode_Node_BV :: "'n \<Rightarrow> (BV_var, ('n, 'v, 'elem) BV_elem) identifier" where
  "Encode_Node_BV n == DLElement (BV_Node n)"

abbreviation Encode_Elem_BV :: "'elem \<Rightarrow> (BV_var, ('n, 'v, 'elem) BV_elem) identifier" where
  "Encode_Elem_BV e == DLElement (BV_Elem e)"

abbreviation Encode_Action_BV :: "'v action \<Rightarrow> (BV_var, ('n, 'v, 'elem) BV_elem) identifier" where
  "Encode_Action_BV \<alpha> == DLElement (BV_Action \<alpha>)"

locale analysis_BV =
  fixes pg :: "('n,'v) program_graph"
  fixes kill_set :: "('n,'v) edge \<Rightarrow> 'd set"
  fixes gen_set :: "('n,'v) edge \<Rightarrow> 'd set"
  fixes d_init :: "'d set"
begin

definition edge_set where 
  "edge_set = fst pg"

definition start where
  "start = fst (snd pg)"

definition "end" where
  "end = snd (snd pg)"


definition "S_hat" :: "('n,'v) edge \<Rightarrow> 'd set \<Rightarrow> 'd set" where
  "S_hat e R = (R - kill_set e) \<union> gen_set e"

lemma S_hat_mono:
  assumes "d1 \<subseteq> d2"
  shows "S_hat e d1 \<subseteq> S_hat e d2"
  using assms unfolding S_hat_def by auto

fun S_hat_edge_list :: "('n,'v) edge list \<Rightarrow> 'd set \<Rightarrow> 'd set" where
  "S_hat_edge_list [] R = R" |
  "S_hat_edge_list (e # \<pi>) R = S_hat_edge_list \<pi> (S_hat e R)"

lemma S_hat_edge_list_def2:
  "S_hat_edge_list \<pi> R = foldl (\<lambda>a b. S_hat b a) R \<pi>"
proof (induction \<pi> arbitrary: R)
  case Nil
  then show ?case
    by simp
next
  case (Cons a \<pi>)
  then show ?case
    by simp
qed

lemma S_hat_edge_list_append[simp]:
  "S_hat_edge_list (xs @ ys) R = S_hat_edge_list ys (S_hat_edge_list xs R)"
  unfolding S_hat_edge_list_def2 foldl_append by auto

lemma S_hat_edge_list_mono:
  assumes "d1 \<subseteq> d2"
  shows "S_hat_edge_list \<pi> d1 \<subseteq> S_hat_edge_list \<pi> d2"
proof(induction \<pi> rule: List.rev_induct)
  case Nil
  then show ?case
    using assms by auto
next
  case (snoc x xs)
  then show ?case
    using assms by (simp add: S_hat_mono)
qed

definition S_hat_path :: "('n list \<times> 'v action list) \<Rightarrow> 'd set \<Rightarrow> 'd set" where
  "S_hat_path \<pi> = S_hat_edge_list (LTS.transition_list \<pi>)"

lemma S_hat_path_mono:
  assumes "d1 \<subseteq> d2"
  shows "S_hat_path \<pi> d1 \<subseteq> S_hat_path \<pi> d2"
  unfolding S_hat_path_def using assms S_hat_edge_list_mono by auto

fun ana_kill_BV :: "(('n, 'v) edge * 'd) \<Rightarrow> (BV_pred, BV_var, ('n, 'v, 'd) BV_elem) clause set" where
  "ana_kill_BV ((q\<^sub>o, \<alpha>, q\<^sub>s), d) =
   (
   if d \<in> kill_set (q\<^sub>o, \<alpha>, q\<^sub>s) then
     {kill\<langle>[Encode_Node_BV q\<^sub>o, Encode_Action_BV \<alpha>, Encode_Node_BV q\<^sub>s, Encode_Elem_BV d]\<rangle> :- [].}
   else
     {}
   )"

fun ana_gen_BV :: "(('n, 'v) edge \<times> 'd) \<Rightarrow> (BV_pred, BV_var, ('n, 'v, 'd) BV_elem) clause set" where
  "ana_gen_BV ((q\<^sub>o, \<alpha>, q\<^sub>s), d) =
   (
   if d \<in> gen_set (q\<^sub>o, \<alpha>, q\<^sub>s) then
     {gen\<langle>[Encode_Node_BV q\<^sub>o, Encode_Action_BV \<alpha>, Encode_Node_BV q\<^sub>s, Encode_Elem_BV d]\<rangle> :- [].}
   else
     {}
   )"

definition ana_init_BV :: "'d \<Rightarrow> (BV_pred, BV_var, ('n, 'v, 'd) BV_elem) clause set" where
  "ana_init_BV d = 
     {
       BV\<langle>[Encode_Node_BV start, Encode_Elem_BV d]\<rangle> :- [].
     }"

fun ana_edge_BV :: "('n, 'v) edge \<Rightarrow> (BV_pred, BV_var, ('n, 'v, 'd) BV_elem) clause set" where
  "ana_edge_BV (q\<^sub>o, \<alpha>, q\<^sub>s) =
     {
        BV\<langle>[Encode_Node_BV q\<^sub>s, \<uu>]\<rangle> :-
          [
            BV[Encode_Node_BV q\<^sub>o, \<uu>],
            \<^bold>\<not>kill[Encode_Node_BV q\<^sub>o, Encode_Action_BV \<alpha>, Encode_Node_BV q\<^sub>s, \<uu>]
          ].
        ,
        BV\<langle>[Encode_Node_BV q\<^sub>s, \<uu>]\<rangle> :- [gen[Encode_Node_BV q\<^sub>o, Encode_Action_BV \<alpha>, Encode_Node_BV q\<^sub>s, \<uu>]].
     }"

definition ana_pg_BV :: "(BV_pred, BV_var, ('n, 'v, 'd) BV_elem) clause set" where
  "ana_pg_BV = \<Union>(ana_edge_BV ` edge_set) 
               \<union> \<Union>(ana_init_BV ` d_init)
               \<union> \<Union>(ana_kill_BV ` (edge_set \<times> UNIV))
               \<union> \<Union>(ana_gen_BV ` (edge_set \<times> UNIV))"

fun summarizes_dl_BV :: "(BV_pred, ('n, 'v, 'd) BV_elem) pred_val \<Rightarrow> bool" where
  "summarizes_dl_BV \<rho> \<longleftrightarrow> (\<forall>\<pi> d. \<pi> \<in> LTS.path_with_word edge_set \<longrightarrow> LTS.get_start \<pi> = start \<longrightarrow> d \<in> S_hat_path \<pi> d_init \<longrightarrow> 
     solves_query \<rho> (BV\<langle>[Encode_Node_BV (LTS.get_end \<pi>), Encode_Elem_BV d]\<rangle>.))"

lemma S_hat_path_append:
  assumes "length qs = length w"                               
  shows "S_hat_path (qs @ [qnminus1, qn], w @ [l]) d_init =
    S_hat (qnminus1, l, qn) (S_hat_path (qs @ [qnminus1], w) d_init)"
proof -
  have "S_hat_path (qs @ [qnminus1, qn], w @ [l]) d_init = S_hat_edge_list (transition_list (qs @ [qnminus1, qn], w @ [l])) d_init"
    unfolding S_hat_path_def by auto
  moreover
  have "S_hat_edge_list (transition_list (qs @ [qnminus1, qn], w @ [l])) d_init =
        S_hat_edge_list (transition_list (qs @ [qnminus1], w) @ [(qnminus1, l, qn)]) d_init"
    using transition_list_reversed_simp[of qs w] assms
    by auto
  moreover
  have "... = S_hat_edge_list [(qnminus1, l, qn)] (S_hat_edge_list (transition_list (qs @ [qnminus1], w)) d_init)"
    using S_hat_edge_list_append[of "transition_list (qs @ [qnminus1], w)" " [(qnminus1, l, qn)]" d_init]
    by auto
  moreover
  have "... = S_hat (qnminus1, l, qn) (S_hat_path (qs @ [qnminus1], w) d_init)"
    unfolding S_hat_path_def by auto
  ultimately show ?thesis
    by blast
qed

lemma ana_pg_BV_stratified: "strat_wf s_BV ana_pg_BV"
  unfolding ana_pg_BV_def
  apply auto
  unfolding strat_wf_def
  apply auto
  unfolding ana_init_BV_def
    apply auto
  subgoal for x a aa b ba
    apply (cases "ba \<in> kill_set (a, aa, b)")
    subgoal
      apply auto
      done
    subgoal
      apply auto
      done
    done
  subgoal for x a aa b ba
    apply (cases "ba \<in> gen_set (a, aa, b)")
    subgoal
      apply auto
      done
    subgoal
      apply auto
      done
    done
  done

lemma not_kill:
  assumes "d \<notin> kill_set(q\<^sub>o, \<alpha>, q\<^sub>s)"
  assumes "least_solution \<sigma> ana_pg_BV s_BV"
  shows "[BV_Node q\<^sub>o, BV_Action \<alpha>, BV_Node q\<^sub>s, BV_Elem d] \<notin> \<sigma> the_kill"
proof (rule ccontr)
  assume "\<not> [BV_Node q\<^sub>o, BV_Action \<alpha>, BV_Node q\<^sub>s, BV_Elem d] \<notin> \<sigma> the_kill"
  then have a: "[BV_Node q\<^sub>o, BV_Action \<alpha>, BV_Node q\<^sub>s, BV_Elem d] \<in> \<sigma> the_kill"
    by auto
  have "least_solution (\<sigma> \\s_BV\\ 0) (ana_pg_BV --s_BV-- 0) s_BV"
    using downward_solution2[of s_BV ana_pg_BV \<sigma> 0] assms(2)
    using ana_pg_BV_stratified by linarith
  then have "minimal_solution (\<sigma> \\s_BV\\ 0) (ana_pg_BV --s_BV-- 0) s_BV"
    using least_is_minimal[of s_BV "ana_pg_BV --s_BV-- 0" "(\<sigma> \\s_BV\\ 0)"]
    using ana_pg_BV_stratified downward_strat2 by blast
  moreover
  define \<sigma>' where "\<sigma>' = (\<lambda>p. (if p = the_kill then ((\<sigma> \\s_BV\\ 0) the_kill) - {[BV_Node q\<^sub>o, BV_Action \<alpha>, BV_Node q\<^sub>s, BV_Elem d]} else (\<sigma> \\s_BV\\ 0) p))"

  have "solves_program \<sigma>' (ana_pg_BV --s_BV-- 0)"
    unfolding solves_program_def
  proof
    fix c
    assume a: "c \<in> (ana_pg_BV --s_BV-- 0)"
    then obtain p ids rhs where c_def: "c = Cls p ids rhs"
      by (cases c) auto

    have "solves_cls \<sigma>' (Cls p ids rhs)"
      unfolding solves_cls_def
    proof
      fix \<eta>
      have rhs_is: "rhs = []"
        using a
        apply auto
        unfolding ana_pg_BV_def
        apply auto
        using ana_init_BV_def apply auto[1]
         apply (metis c_def clause.inject equals0D insertE)
        apply (metis c_def clause.inject empty_iff singletonD)
        done
      show "meaning_cls (Cls p ids rhs) \<sigma>' \<eta>"
      proof (cases "p = the_kill \<and> ids = [Encode_Node_BV q\<^sub>o, Encode_Action_BV \<alpha>, Encode_Node_BV q\<^sub>s, Encode_Elem_BV d]")
        case True
        then show ?thesis
          using a c_def assms(1) rhs_is
          apply auto
          unfolding ana_pg_BV_def
          apply auto
            apply (auto simp add: analysis_BV.ana_init_BV_def)
           apply (metis (no_types, lifting) BV_elem.inject(1) BV_elem.inject(2) BV_elem.inject(3) clause.inject equals0D identifier.inject(2) list.inject singletonD)
          apply (meson BV_pred.distinct(5) clause.inject empty_iff singletonD)
          done
      next
        case False
        have "meaning_cls (Cls p ids rhs) (\<sigma> \\s_BV\\ 0) \<eta>"
          using \<open>least_solution (\<sigma> \s_BV\ 0) (ana_pg_BV --s_BV-- 0) s_BV\<close> a c_def least_solution_def solves_cls_def solves_program_def by blast
        moreover
        have "rhs = []"
          using rhs_is by auto
        ultimately
        show ?thesis
          using False unfolding \<sigma>'_def
          using a c_def
          apply auto
          unfolding ana_pg_BV_def
             apply auto
                     apply (auto simp add: analysis_BV.ana_init_BV_def)
                 apply (metis clause.inject equals0D eval_id.simps(2) list.inject singletonD)
                apply (meson BV_pred.distinct(5) clause.inject empty_iff singletonD)
               apply (metis clause.inject equals0D eval_id.simps(2) list.inject singletonD)
              apply (meson BV_pred.distinct(5) clause.inject empty_iff singletonD)
             apply (metis clause.inject equals0D eval_id.simps(2) list.inject singletonD)
            apply (meson BV_pred.distinct(5) clause.inject empty_iff singletonD)
           apply (metis (no_types, lifting) clause.inject equals0D eval_id.simps(2) list.inject singletonD)
          apply (meson BV_pred.distinct(5) clause.inject empty_iff singletonD)
          done
      qed
    qed
    then show "solves_cls \<sigma>' c"
      using c_def by blast
  qed
  moreover
  have "\<sigma>' \<sqsubset>s_BV\<sqsubset> (\<sigma> \\s_BV\\ 0)"
  proof -
    have "\<sigma>' the_kill \<subset> (\<sigma> \\s_BV\\ 0) the_kill"
      unfolding \<sigma>'_def using a by auto
    moreover
    have "\<forall>p'. s_BV p' = s_BV the_kill \<longrightarrow> \<sigma>' p' \<subseteq> (\<sigma> \\s_BV\\ 0) p'"
      unfolding \<sigma>'_def by auto
    moreover
    have "\<forall>p'. s_BV p' < s_BV the_kill \<longrightarrow> \<sigma>' p' = (\<sigma> \\s_BV\\ 0) p'"
      unfolding \<sigma>'_def by auto
    ultimately
    show "\<sigma>' \<sqsubset>s_BV\<sqsubset> (\<sigma> \\s_BV\\ 0)"
      unfolding lt_def  by auto
  qed
  ultimately
  show False
    unfolding minimal_solution_def by auto
qed

lemma sound_BV': 
  assumes "(ss,w) \<in> LTS.path_with_word edge_set"
  assumes "least_solution \<rho> ana_pg_BV s_BV"
  assumes "LTS.get_start (ss,w) = start"
  assumes "d \<in> S_hat_path (ss,w) d_init"
  shows "solves_query \<rho> BV\<langle>[Encode_Node_BV (LTS.get_end (ss,w)), Encode_Elem_BV d]\<rangle>."
  using assms 
proof (induction arbitrary: d rule: LTS.path_with_word_induct_reverse[OF assms(1)])
  case (1 s)
  have assms_2: "solves_program \<rho> ana_pg_BV"
    using assms(2) unfolding least_solution_def by auto

  from 1(1,3) have start_end: "LTS.get_end ([s], []) = start"
    using LTS.singleton_path_start_end[of s edge_set, OF 1(1)] by (metis LTS.get_end_def prod.sel(1))

  from 1 have "S_hat_path ([s], []) d_init = d_init"
    unfolding S_hat_path_def by auto
  then have "d \<in> d_init"
    using 1(4) by auto
  moreover
  from assms_2 have "\<forall>d \<in> d_init. solves_cls \<rho> (BV\<langle>[Encode_Node_BV start, Encode_Elem_BV d]\<rangle> :- [].)"
    unfolding ana_pg_BV_def ana_init_BV_def solves_program_def by auto
  ultimately have "solves_cls \<rho> (BV\<langle>[Encode_Node_BV start, Encode_Elem_BV d]\<rangle> :- [].)"
    by auto
  then show ?case
    using start_end solves_fact_query by metis
next
  case (2 qs qnminus1 w l qn)
  have "S_hat_path (qs @ [qnminus1], w) d_init \<subseteq>
        {d. solves_query \<rho> BV\<langle>[Encode_Node_BV (LTS.get_end (qs @ [qnminus1], w)), Encode_Elem_BV d]\<rangle>.}"
    using 2
    by (metis (no_types, lifting) LTS.get_start_def hd_append2 list.sel(1) mem_Collect_eq prod.sel(1) self_append_conv2 subsetI) 
  then have f: "S_hat (qnminus1, l, qn) (S_hat_path (qs @ [qnminus1], w) d_init) \<subseteq>
             S_hat (qnminus1, l, qn) {d. solves_query \<rho> BV\<langle>[Encode_Node_BV (LTS.get_end (qs @ [qnminus1], w)), Encode_Elem_BV d]\<rangle>.}"
    by (simp add: S_hat_mono)

  have "length qs = length w"
    using 2(1) LTS.path_with_word_lengths by metis
  then have "S_hat_path (qs @ [qnminus1, qn], w @ [l]) d_init = S_hat (qnminus1, l, qn) (S_hat_path (qs @ [qnminus1], w) d_init)"
    using S_hat_path_append[of qs w] by auto
  moreover 
  have "... = S_hat (qnminus1, l, qn) (S_hat_path (qs @ [qnminus1], w) d_init)"
    by simp
  moreover 
  have "... \<subseteq> S_hat (qnminus1, l, qn) {d. solves_query \<rho> BV\<langle>[Encode_Node_BV qnminus1, Encode_Elem_BV d]\<rangle>.}"
    by (metis f LTS.get_end_def last_snoc prod.sel(1))
  ultimately 
  have "S_hat_path (qs @ [qnminus1, qn], w @ [l]) d_init \<subseteq> S_hat (qnminus1, l, qn) {d. solves_query \<rho> BV\<langle>[Encode_Node_BV qnminus1, Encode_Elem_BV d]\<rangle>.}"
    by auto
  then have "d \<in> S_hat (qnminus1, l, qn) {d. solves_query \<rho> BV\<langle>[Encode_Node_BV qnminus1, Encode_Elem_BV d]\<rangle>.}"
    using 2(7) by auto
  then have "  d \<in>
                 ({d. solves_query \<rho> BV\<langle>[Encode_Node_BV qnminus1, Encode_Elem_BV d]\<rangle>.} -
                  kill_set (qnminus1, l, qn))
             \<or> d \<in>
                  gen_set (qnminus1, l, qn)"
    unfolding S_hat_def by auto
  then have "solves_query \<rho> BV\<langle>[Encode_Node_BV qn, Encode_Elem_BV d]\<rangle>."
  proof
    assume a: "d \<in> {d. solves_query \<rho> BV\<langle>[Encode_Node_BV qnminus1, Encode_Elem_BV d]\<rangle>.} -
         kill_set (qnminus1, l, qn)"
    from a have a_1: "solves_query \<rho> BV\<langle>[Encode_Node_BV qnminus1, Encode_Elem_BV d]\<rangle>."
      by auto
    moreover
    have e_in_pg: "(qnminus1, l, qn) \<in> edge_set"
      using "2.hyps"(2) by blast

    have "\<forall>c \<in> ana_edge_BV (qnminus1, l, qn). solves_cls \<rho> c"
      using 2(5) e_in_pg unfolding ana_pg_BV_def solves_program_def least_solution_def by blast
    then have "solves_cls \<rho> BV\<langle>[Encode_Node_BV qn, \<uu>]\<rangle> :- [BV[Encode_Node_BV qnminus1,  \<uu>], \<^bold>\<not>kill[Encode_Node_BV qnminus1, Encode_Action_BV l, Encode_Node_BV qn, \<uu>]]."
      by auto
    then have "solves_cls \<rho> BV\<langle>[Encode_Node_BV qn, Encode_Elem_BV d]\<rangle> :- [BV[Encode_Node_BV qnminus1, Encode_Elem_BV d], \<^bold>\<not>kill[Encode_Node_BV qnminus1, Encode_Action_BV l, Encode_Node_BV qn, Encode_Elem_BV d]]."
      using substitution_rule[of \<rho> _ "\<lambda>u. Encode_Elem_BV d"]
      by force
    moreover
    from a have a_2: "d \<notin> kill_set (qnminus1, l, qn)"
      by auto
    have "\<forall>c\<in>\<Union>(ana_kill_BV ` (edge_set \<times> UNIV)). solves_cls \<rho> c"
      using 2(5) unfolding ana_pg_BV_def solves_program_def least_solution_def by auto
    then have "\<forall>c\<in>ana_kill_BV ((qnminus1, l, qn),d). solves_cls \<rho> c"
      using e_in_pg by blast
    have "[BV_Node qnminus1, BV_Action l, BV_Node qn, BV_Elem d] \<notin> \<rho> the_kill"
      using a_2 not_kill[of d qnminus1 l qn \<rho>] 2(5) by auto
    then have "solves_rh \<rho> (\<^bold>\<not>kill[Encode_Node_BV qnminus1, Encode_Action_BV l, Encode_Node_BV qn, Encode_Elem_BV d])" (* Could maybe be phrased better *)
      by auto
    ultimately
    show "solves_query \<rho> BV\<langle>[Encode_Node_BV qn, Encode_Elem_BV d]\<rangle>."
      by (metis append.left_neutral append_Cons resolution_last_rh resolution_only_rh_query)
  next
    assume a: "d \<in> gen_set (qnminus1, l, qn)"
    have e_in_pg: "(qnminus1, l, qn) \<in> edge_set"
      using "2.hyps"(2) by blast

    have "\<forall>c \<in> ana_edge_BV (qnminus1, l, qn). solves_cls \<rho> c"
      using 2(5) e_in_pg unfolding ana_pg_BV_def solves_program_def least_solution_def by blast
    then have "solves_cls \<rho> BV\<langle>[Encode_Node_BV qn, \<uu>]\<rangle> :- [gen[Encode_Node_BV qnminus1, Encode_Action_BV l, Encode_Node_BV qn, \<uu>]]."
      by auto
    then have "solves_cls \<rho> BV\<langle>[Encode_Node_BV qn, Encode_Elem_BV d]\<rangle> :- [gen[Encode_Node_BV qnminus1, Encode_Action_BV l, Encode_Node_BV qn, Encode_Elem_BV d]]."
      using substitution_rule[of \<rho> _ "\<lambda>u. Encode_Elem_BV d" ]
      by force
    moreover
    have "\<forall>c\<in>\<Union>(ana_gen_BV ` (edge_set \<times> UNIV)). solves_cls \<rho> c"
      using 2(5) unfolding ana_pg_BV_def solves_program_def least_solution_def by auto
    then have "\<forall>c\<in>ana_gen_BV ((qnminus1, l, qn),d). solves_cls \<rho> c"
      using e_in_pg by blast
    then have "solves_cls \<rho> gen\<langle>[Encode_Node_BV qnminus1, Encode_Action_BV l, Encode_Node_BV qn, Encode_Elem_BV d]\<rangle> :- []."
      using a
      by auto
    ultimately
    show "solves_query \<rho> BV\<langle>[Encode_Node_BV qn, Encode_Elem_BV d]\<rangle>."
      by (meson resolution_only_rh_query solves_fact_query)
  qed
  then show ?case
    by (simp add: LTS.get_end_def) 
qed

lemma sound_BV:
  assumes "least_solution \<rho> ana_pg_BV s_BV"
  shows "summarizes_dl_BV \<rho>"
  using sound_BV' assms unfolding summarizes_dl_BV.simps by (cases pg) fastforce

end


section \<open>Reaching definitions revisited\<close>

locale analysis_RD =
  fixes pg :: "('n,'v) program_graph"
begin

definition edge_set where
  "edge_set = fst pg"

definition start where
  "start = fst (snd pg)"

definition "end" where
  "end = snd (snd pg)"

fun kill_set_RD :: "('n,'v) edge \<Rightarrow> ('n,'v) triple set" where
  "kill_set_RD (q\<^sub>o, x ::= a, q\<^sub>s) = {x} \<times> UNIV \<times> UNIV"
| "kill_set_RD (q\<^sub>o, Bool b, q\<^sub>s) = {}"
| "kill_set_RD (v, Skip, vc) = {}"

fun gen_set_RD :: "('n,'v) edge \<Rightarrow> ('n,'v) triple set" where
  "gen_set_RD (q\<^sub>o, x ::= a, q\<^sub>s) = {x} \<times> {Some q\<^sub>o} \<times> {q\<^sub>s}"
| "gen_set_RD (q\<^sub>o, Bool b, q\<^sub>s) = {}"
| "gen_set_RD (v, Skip, vc) = {} "

definition d_init_RD :: " ('n,'v) triple set" where
  "d_init_RD = (UNIV \<times> {None} \<times> {start})"

interpretation interp: analysis_BV pg kill_set_RD gen_set_RD d_init_RD .

lemma def_var_def_edge_S_hat:
  assumes "def_var \<pi> x start \<in> R"
  assumes "x \<notin> def_edge t"
  shows "def_var \<pi> x start \<in> interp.S_hat t R"
proof -
  define q1 where "q1 = fst t"
  define \<alpha> where "\<alpha> = fst (snd t)"
  define q2 where "q2 = snd (snd t)"
  have t_def: "t = (q1, \<alpha>, q2)"
    by (simp add: \<alpha>_def q1_def q2_def)

  from assms(2) have assms_2: "x \<notin> def_edge (q1, \<alpha>, q2)"
    unfolding t_def by auto

  have "def_var \<pi> x start \<in> interp.S_hat (q1, \<alpha>, q2) R"
  proof (cases \<alpha>)
    case (Asg y exp)
    then show ?thesis
      by (metis (no_types, lifting) DiffI Un_iff assms(1) assms_2 def_action.simps(1) def_var_x interp.S_hat_def kill_set_RD.simps(1) mem_Sigma_iff old.prod.case prod.collapse)
  next
    case (Bool b)
    then show ?thesis
      by (simp add: analysis_BV.S_hat_def assms(1))
  next
    case Skip
    then show ?thesis
      by (simp add: analysis_BV.S_hat_def assms(1))
  qed
  then show ?thesis
    unfolding t_def by auto
qed

lemma def_var_S_hat_edge_list: "(def_var \<pi>) x start \<in> interp.S_hat_edge_list \<pi> d_init_RD"
proof (induction \<pi> rule: rev_induct)
  case Nil
  then show ?case
    unfolding def_var_def d_init_RD_def by auto
next
  case (snoc t \<pi>)
  then show ?case
  proof (cases "x \<in> def_edge t")
    case True
    then have "def_var (\<pi> @[t]) x start = def_var [t] x start"
      by (simp add: def_var_def)
    moreover
    have "interp.S_hat_edge_list (\<pi> @ [t]) d_init_RD = interp.S_hat t (interp.S_hat_edge_list \<pi> d_init_RD)"
      unfolding interp.S_hat_edge_list_def2 by simp
    moreover
    obtain q1 \<alpha> q2 where t_split: "t = (q1, \<alpha>, q2)"
      using prod_cases3 by blast
    moreover
    have "def_var [t] x start \<in> interp.S_hat t (interp.S_hat_edge_list \<pi> d_init_RD)"
      unfolding interp.S_hat_def def_var_def triple_of_def using True t_split by (cases \<alpha>) auto
    ultimately
    show ?thesis by auto
  next
    case False
    obtain q1 \<alpha> q2 where t_split: "t = (q1, \<alpha>, q2)"
      using prod_cases3 by blast
    from False have "def_var (\<pi> @ [t]) x start = def_var \<pi> x start"
      by (simp add: def_var_def)
    moreover
    from snoc.IH have "def_var \<pi> x start \<in> interp.S_hat t (interp.S_hat_edge_list \<pi> d_init_RD)"
      by (simp add: False def_var_def_edge_S_hat)
    then have "def_var \<pi> x start \<in> interp.S_hat_edge_list (\<pi> @ [t]) d_init_RD"
      unfolding interp.S_hat_edge_list_def2 by simp
    ultimately
    show ?thesis
      using snoc by auto
  qed
qed

lemma last_overwrites:
  "def_var (\<pi> @ [(q1, x ::= exp, q2)]) x start = (x, Some q1, q2)"
proof -
  have "x \<in> def_edge (q1, x ::= exp, q2)"
    by auto
  then have "\<exists>e\<in>set (\<pi> @ [(q1, x ::= exp, q2)]). x \<in> def_edge e"
    by auto
  have "def_var (\<pi> @ [(q1, x ::= exp, q2)]) x start = triple_of x (last (filter (\<lambda>e. x \<in> def_edge e) (\<pi> @ [(q1, x ::= exp, q2)])))"
    unfolding def_var_def by auto
  also
  have "... = triple_of x (q1, x ::= exp, q2)"
    by auto
  also
  have "... = (x, Some q1, q2)"
    unfolding triple_of_def by auto
  finally
  show ?thesis
    .
qed

lemma S_hat_edge_list_last: "interp.S_hat_edge_list (\<pi> @ [a]) d_init_RD = interp.S_hat a (interp.S_hat_edge_list \<pi> d_init_RD)"
  using interp.S_hat_edge_list_def2 foldl_conv_foldr by simp

lemma gugugug: "(x,q1,q2) \<in> interp.S_hat_edge_list \<pi> d_init_RD \<Longrightarrow> (x,q1,q2) = (def_var \<pi>) x start"
proof (induction \<pi> rule: rev_induct)
case Nil
  then show ?case
    by (metis append_is_Nil_conv d_init_RD_def def_var_def in_set_conv_decomp interp.S_hat_edge_list.simps(1) list.distinct(1) mem_Sigma_iff singletonD)
next
  case (snoc a \<pi>)
  
  from snoc(2) have "(x, q1, q2) \<in> interp.S_hat a (interp.S_hat_edge_list \<pi> d_init_RD)"
    using S_hat_edge_list_last by blast     

  then have "(x, q1, q2) \<in> interp.S_hat_edge_list \<pi> d_init_RD - kill_set_RD a \<or> (x, q1, q2) \<in> gen_set_RD a"
    unfolding interp.S_hat_def by auto
  then show ?case
  proof
    assume a: "(x, q1, q2) \<in> interp.S_hat_edge_list \<pi> d_init_RD - kill_set_RD a"
    then have "(x, q1, q2) = def_var \<pi> x start"
      using snoc by auto
    moreover
    from a have "(x, q1, q2) \<notin> kill_set_RD a"
      by auto
    then have "def_var (\<pi> @ [a]) x start = def_var \<pi> x start"
    proof -
      assume a: "(x, q1, q2) \<notin> kill_set_RD a"
      then have "x \<notin> def_edge a"
        apply (cases a)
        apply auto
        subgoal for q1' c q2'
          apply (cases c)
          subgoal for y exp 
            apply(subgoal_tac "x\<noteq>y")
             apply auto
            done
          subgoal
            apply auto
            done
          subgoal 
            apply auto
            done
          done
        done
      then show ?thesis
        by (simp add: def_var_def)
    qed
    ultimately
    show ?case
      by auto
  next
    assume "(x, q1, q2) \<in> gen_set_RD a"
    then have "\<exists>exp theq1. a = (theq1, x ::= exp, q2) \<and> q1 = Some theq1"
      apply (cases a)
      subgoal for q1' a' q2'
        apply (cases a')
        subgoal for y exp
          apply auto
          done
        subgoal
          apply auto
          done
        subgoal 
          apply auto
          done
        done
      done
    then obtain exp theq1 where exp_theq1_p: "a = (theq1, x ::= exp, q2) \<and> q1 = Some theq1"
      by auto
    then have "(x, q1, q2) = def_var (\<pi> @ [(theq1, x ::= exp, q2)]) x start"
      using last_overwrites[of \<pi> theq1 x exp q2] by auto
    then show ?case
      using exp_theq1_p by auto
  qed
qed

lemma def_var_UNIV_S_hat_edge_list: "(\<lambda>x. def_var \<pi> x start) ` UNIV = interp.S_hat_edge_list \<pi> d_init_RD"
proof (rule; rule)
  fix x
  assume "x \<in> range (\<lambda>x. def_var \<pi> x start)"
  then show "x \<in> interp.S_hat_edge_list \<pi> d_init_RD"
    using def_var_S_hat_edge_list by blast
next
  fix x
  assume "x \<in> interp.S_hat_edge_list \<pi> d_init_RD"
  then show "x \<in> range (\<lambda>x. def_var \<pi> x start)"
    by (metis (no_types, lifting) analysis_RD.gugugug prod.collapse range_eqI)
qed

lemma def_path_S_hat_path: "def_path \<pi> start = interp.S_hat_path \<pi> d_init_RD"
  using analysis_BV.S_hat_path_def def_path_def def_var_UNIV_S_hat_edge_list by metis

fun summarizes_RD :: "(BV_pred, ('n,'v,('n,'v) triple) BV_elem) pred_val \<Rightarrow> bool" where
  "summarizes_RD \<rho> \<longleftrightarrow> (\<forall>\<pi> d. \<pi> \<in> LTS.path_with_word edge_set \<longrightarrow> LTS.get_start \<pi> = start \<longrightarrow> d \<in> def_path \<pi> start \<longrightarrow>
     solves_query \<rho> (BV\<langle>[Encode_Node_BV (LTS.get_end \<pi>), Encode_Elem_BV d]\<rangle>.))"

lemma RD_sound_again: 
  assumes "least_solution \<rho> (interp.ana_pg_BV) s_BV"
  shows "summarizes_RD \<rho>"
  using assms def_path_S_hat_path interp.sound_BV unfolding interp.summarizes_dl_BV.simps summarizes_RD.simps
  using edge_set_def in_mono interp.edge_set_def interp.start_def start_def by fastforce 

end




section \<open>Backwards analysis\<close>

locale analysis_BV_backwards =
  fixes pg :: "('n,'v) program_graph"
  fixes kill_set :: "('n,'v) edge \<Rightarrow> 'd set"
  fixes gen_set :: "('n,'v) edge \<Rightarrow> 'd set"
  fixes d_init :: "'d set"
begin

definition edge_set where
  "edge_set = fst pg"

definition start where
  "start = fst (snd pg)"

definition "end" where
  "end = snd (snd pg)"

definition pg_rev :: "('n,'v) program_graph" where
  "pg_rev = (rev_edge ` edge_set, end, start)"

definition "S_hat" :: "('n,'v) edge \<Rightarrow> 'd set \<Rightarrow> 'd set" where
  "S_hat e R = (R - kill_set e) \<union> gen_set e"

lemma S_hat_mono:
  assumes "d1 \<subseteq> d2"
  shows "S_hat e d1 \<subseteq> S_hat e d2"
  using assms unfolding S_hat_def by auto

fun S_hat_edge_list :: "('n,'v) edge list \<Rightarrow> 'd set \<Rightarrow> 'd set" where
  "S_hat_edge_list [] R = R" |
  "S_hat_edge_list (e # \<pi>) R = S_hat e (S_hat_edge_list \<pi> R)"

lemma S_hat_edge_list_def2:
  "S_hat_edge_list \<pi> R = foldr S_hat \<pi> R"
proof (induction \<pi> arbitrary: R)
  case Nil
  then show ?case
    by simp
next
  case (Cons a \<pi>)
  then show ?case
    by simp
qed

lemma S_hat_edge_list_append[simp]:
  "S_hat_edge_list (xs @ ys) R = S_hat_edge_list xs (S_hat_edge_list ys R)"
  unfolding S_hat_edge_list_def2 foldl_append by auto

lemma S_hat_edge_list_mono:
  assumes "d1 \<subseteq> d2"
  shows "S_hat_edge_list \<pi> d1 \<subseteq> S_hat_edge_list \<pi> d2"
proof(induction \<pi>)
  case Nil
  then show ?case
    using assms by auto
next
  case (Cons x xs)
  then show ?case
    using assms by (simp add: S_hat_mono)
qed

definition S_hat_path :: "('n list \<times> 'v action list) \<Rightarrow> 'd set \<Rightarrow> 'd set" where
  "S_hat_path \<pi> = S_hat_edge_list (LTS.transition_list \<pi>)"

definition summarizes_dl_BV :: "(BV_pred, ('n, 'v, 'd) BV_elem) pred_val \<Rightarrow> bool" where
  "summarizes_dl_BV \<rho> \<longleftrightarrow> (\<forall>\<pi> d. \<pi> \<in> LTS.path_with_word edge_set \<longrightarrow> LTS.get_end \<pi> = end \<longrightarrow> d \<in> S_hat_path \<pi> d_init \<longrightarrow> 
     solves_query \<rho> (BV\<langle>[Encode_Node_BV (LTS.get_start \<pi>), Encode_Elem_BV d]\<rangle>.))"

(* \<rho> \<Turnstile> BV(\<pi>\<^sub>0,d). *)

interpretation fa: analysis_BV pg_rev "\<lambda>e. (kill_set (rev_edge e))" "(\<lambda>e. gen_set (rev_edge e))" d_init .

abbreviation ana_pg_BV where
  "ana_pg_BV == fa.ana_pg_BV"

lemma rev_end_is_start:
  assumes "ss \<noteq> []"
  assumes "LTS.get_end (ss, w) = end"
  shows "LTS.get_start (rev ss, rev w) = fa.start"
  using assms
  unfolding LTS.get_end_def LTS.get_start_def fa.start_def pg_rev_def analysis_BV.start_def
  by (simp add: hd_rev)

lemma S_hat_edge_list_forward_backward:
   "S_hat_edge_list ss d_init = fa.S_hat_edge_list (rev_edge_list ss) d_init"
proof (induction ss)
  case Nil
  then show ?case
    unfolding rev_edge_list_def by auto
next
  case (Cons a ss)
  show ?case
    unfolding rev_edge_list_def
    unfolding fa.S_hat_edge_list_def2
    unfolding foldl_conv_foldr
    apply simp
    unfolding foldr_conv_foldl
    unfolding fa.S_hat_edge_list_def2[symmetric]
    unfolding rev_edge_list_def[symmetric]
    unfolding fa.S_hat_def
    apply (simp only: rev_edge_rev_edge_id)
    unfolding S_hat_def
    using Cons
    apply metis
    done
qed

lemma S_hat_path_forwards_backwards:
  assumes "(ss,w) \<in> LTS.path_with_word edge_set"
  shows "S_hat_path (ss, w) d_init = fa.S_hat_path (rev ss, rev w) d_init"
  using S_hat_edge_list_forward_backward unfolding S_hat_path_def fa.S_hat_path_def
  by (metis transition_list_rev_edge_list assms)

(* Maybe I need a better way to swap Start and End *)
(* And also there is a problem in my current graph reversal. I need to map rev_node
   onto the graph. I think that that will solve the "better way to swap Start and End problem"
   I did that :-D
 *)
lemma summarizes_dl_BV_forwards_backwards':
  assumes "(ss,w) \<in> LTS.path_with_word edge_set"
  assumes "LTS.get_end (ss,w) = end"
  assumes "d \<in> S_hat_path (ss,w) d_init"
  assumes "fa.summarizes_dl_BV \<rho>"
  shows "solves_query \<rho> BV\<langle>[Encode_Node_BV (LTS.get_start (ss,w)), Encode_Elem_BV d]\<rangle>."
proof -
  have rev_in_edge_set: "(rev (ss), rev (w)) \<in> LTS.path_with_word fa.edge_set"
    using assms(1) rev_path_in_rev_pg[of ss w] fa.edge_set_def pg_rev_def by auto 
  moreover
  have "LTS.get_start (rev (ss), rev (w)) = fa.start"
    using assms(1,2) rev_end_is_start by (metis LTS.path_with_word_not_empty)
  moreover
  have "d \<in> fa.S_hat_path (rev (ss), rev (w)) d_init"
    using assms(3)
    using assms(1) S_hat_path_forwards_backwards by auto
  ultimately
  have "solves_query \<rho> BV\<langle>[Encode_Node_BV (LTS.get_end (rev (ss), rev (w))), Encode_Elem_BV d]\<rangle>."
    using assms(4) fa.summarizes_dl_BV.simps by blast
  then show ?thesis
    by (metis LTS.get_end_def LTS.get_start_def LTS.path_with_word_not_empty rev_in_edge_set fst_conv hd_rev rev_rev_ident)
qed

lemma summarizes_dl_BV_forwards_backwards:
  assumes "fa.summarizes_dl_BV \<rho>"
  shows "summarizes_dl_BV \<rho>"
  unfolding summarizes_dl_BV_def
proof(rule; rule ; rule ;rule ;rule)
  fix \<pi> d
  assume "\<pi> \<in> LTS.path_with_word edge_set"
  moreover
  assume "LTS.get_end \<pi> = end"
  moreover
  assume "d \<in> S_hat_path \<pi> d_init"
  ultimately
  show "solves_query \<rho> BV\<langle>[Encode_Node_BV (LTS.get_start \<pi>), Encode_Elem_BV d]\<rangle>."
    using summarizes_dl_BV_forwards_backwards'[of "fst \<pi>" "snd \<pi>" d \<rho>] using assms by auto
qed

lemma sound_rev_BV:
  assumes "least_solution \<rho> fa.ana_pg_BV s_BV"
  shows "summarizes_dl_BV \<rho>"
  using assms fa.sound_BV[of \<rho>] summarizes_dl_BV_forwards_backwards by metis

end


section \<open>Live Variables Analysis\<close>

(* definition def_var :: "('n,'v) edge list \<Rightarrow> 'v \<Rightarrow> 'n \<Rightarrow> ('n,'v) triple" where *)

fun use_action :: "'v action \<Rightarrow> 'v set" where
  "use_action (x ::= a) = fv_arith a"
| "use_action (Bool b) = fv_boolean b"
| "use_action Skip = {}"

fun use_edge :: "('n,'v) edge \<Rightarrow> 'v set" where
  "use_edge (q1, \<alpha>, q2) = use_action \<alpha>"

definition use_var :: "('n,'v) edge list \<Rightarrow> 'v \<Rightarrow> bool" where
  "use_var \<pi> x = (\<exists>\<pi>1 \<pi>2 e. \<pi> = \<pi>1 @ [e] @ \<pi>2 \<and> x \<in> use_edge e \<and> (\<not>(\<exists>e' \<in> set \<pi>1. x \<in> def_edge e')))"

definition use_path where
  "use_path \<pi> = {x. use_var (LTS.transition_list \<pi>) x}"

locale analysis_LV =
  fixes pg :: "('n,'v) program_graph"
begin

definition edge_set where 
  "edge_set = fst pg"

definition start where
  "start = fst (snd pg)"

definition "end" where
  "end = snd (snd pg)"

fun kill_set_LV :: "('n,'v) edge \<Rightarrow> 'v set" where
  "kill_set_LV (q\<^sub>o, x ::= a, q\<^sub>s) = {x}"
| "kill_set_LV (q\<^sub>o, Bool b, q\<^sub>s) = {}"
| "kill_set_LV (v, Skip, vc) = {}"

fun gen_set_LV :: "('n,'v) edge \<Rightarrow> 'v set" where
  "gen_set_LV (q\<^sub>o, x ::= a, q\<^sub>s) = fv_arith a"
| "gen_set_LV (q\<^sub>o, Bool b, q\<^sub>s) = fv_boolean b"
| "gen_set_LV (v, Skip, vc) = {}"

definition d_init_LV :: "'v set" where
  "d_init_LV = {}"

interpretation interpb: analysis_BV_backwards pg kill_set_LV gen_set_LV d_init_LV .

thm interpb.sound_rev_BV

lemma use_var_S_hat_edge_list: 
  assumes "use_var \<pi> x"
  shows "x \<in> interpb.S_hat_edge_list \<pi> d_init_LV"
  using assms
proof (induction \<pi>)
  case Nil
  then have False 
    unfolding use_var_def by auto
  then show ?case
    by metis
next
  case (Cons a \<pi>)
  note Cons_inner = Cons
  from Cons(2) have "\<exists>\<pi>1 \<pi>2 e. a # \<pi> = \<pi>1 @ [e] @ \<pi>2 \<and> x \<in> use_edge e \<and> \<not> (\<exists>e'\<in>set \<pi>1. x \<in> def_edge e')"
    unfolding use_var_def by auto
  then obtain \<pi>1 \<pi>2 e where \<pi>1_\<pi>2_e_p:
    "a # \<pi> = \<pi>1 @ [e] @ \<pi>2"
    "x \<in> use_edge e"
    "\<not>(\<exists>e'\<in>set \<pi>1. x \<in> def_edge e')"
    by auto
  then show ?case
  proof (cases \<pi>1)
    case Nil
    have "a = e"
      using \<pi>1_\<pi>2_e_p(1) Nil by auto
    then have x_used_a: "x \<in> use_edge a"
      using \<pi>1_\<pi>2_e_p(2) by auto
    obtain p \<alpha> q where a_split: "a = (p, \<alpha>, q)"
      by (cases a)
    show ?thesis
      using x_used_a interpb.S_hat_def a_split by (cases \<alpha>) auto
  next
    case (Cons hd_\<pi>1 tl_\<pi>1)
    obtain p \<alpha> q where e_split: "e = (p, \<alpha>, q)"
      by (cases e)
    have "(\<pi> = tl_\<pi>1 @ (p, \<alpha>, q) # \<pi>2) \<and> x \<in> use_action \<alpha> \<and> (\<forall>e'\<in>set tl_\<pi>1. x \<notin> def_edge e')"
      using Cons \<pi>1_\<pi>2_e_p e_split by auto
    then have "use_var \<pi> x"
      unfolding use_var_def by force
    then have x_in_S_hat_\<pi>: "x \<in> interpb.S_hat_edge_list \<pi> d_init_LV"
      using Cons_inner by auto
    have "a \<in> set \<pi>1"
      using \<pi>1_\<pi>2_e_p(1) Cons(1) by auto
    then have x_not_def_a: "\<not>x \<in> def_edge a"
      using \<pi>1_\<pi>2_e_p(3) by auto

    obtain p' \<alpha>' q' where a_split: "a = (p', \<alpha>', q')"
      by (cases a)

    show ?thesis
    proof (cases "x \<in> kill_set_LV a")
      case True
      show ?thesis
        using True a_split x_not_def_a by (cases \<alpha>'; force)
    next
      case False
      then show ?thesis
        by (simp add: analysis_BV_backwards.S_hat_def x_in_S_hat_\<pi>)
    qed
  qed
qed


lemma S_hat_edge_list_use_var:
  assumes "x \<in> interpb.S_hat_edge_list \<pi> d_init_LV"
  shows "use_var \<pi> x"
  using assms 
proof (induction \<pi>)
  case Nil
  then have False
    using d_init_LV_def by auto
  then show ?case
     by metis
next
  case (Cons a \<pi>)
  from Cons(2) have "x \<in> interpb.S_hat_edge_list \<pi> d_init_LV - kill_set_LV a \<union> gen_set_LV a"
    unfolding interpb.S_hat_edge_list.simps unfolding interpb.S_hat_def by auto
  then show ?case
  proof
    assume a: "x \<in> interpb.S_hat_edge_list \<pi> d_init_LV - kill_set_LV a"
    then have "x \<in> interpb.S_hat_edge_list \<pi> d_init_LV"
      by auto
    then have "use_var \<pi> x"
      using Cons by auto
    then have "\<exists>\<pi>1 \<pi>2 e. \<pi> = \<pi>1 @ [e] @ \<pi>2 \<and> x \<in> use_edge e \<and> \<not>(\<exists>e'\<in>set \<pi>1. x \<in> def_edge e')"
      unfolding use_var_def by auto
    then obtain \<pi>1 \<pi>2 e where \<pi>1_\<pi>2_e_p:
      "\<pi> = \<pi>1 @ [e] @ \<pi>2"
      "x \<in> use_edge e"
      "\<not>(\<exists>e'\<in>set \<pi>1. x \<in> def_edge e')"
      by auto
    obtain q1 \<alpha> q2 where a_split: "a =(q1, \<alpha>, q2)"
      by (cases a) auto
    from a have "x \<notin> kill_set_LV a"
      by auto
    then have x_not_killed: "x \<notin> kill_set_LV (q1, \<alpha>, q2)"
      using a_split by auto
    have "use_var ((q1, \<alpha>, q2) # \<pi>) x"
    proof (cases \<alpha>)
      case (Asg y exp)
      then have "x \<notin> kill_set_LV (q1, y ::= exp, q2)"
        using x_not_killed by auto
      then have x_not_y: "x \<noteq> y"
        by auto
      have "(q1, y ::= exp, q2) # \<pi> = ((q1, y ::= exp, q2) # \<pi>1) @ [e] @ \<pi>2"
        using \<pi>1_\<pi>2_e_p by force
      moreover
      have "\<not> (\<exists>e'\<in>set ((q1, y ::= exp, q2) # \<pi>1). x \<in> def_edge e')"
        using \<pi>1_\<pi>2_e_p x_not_y by force
      ultimately
      have "use_var ((q1, y ::= exp, q2) # \<pi>) x"
        unfolding use_var_def using \<pi>1_\<pi>2_e_p x_not_y by metis
      then show ?thesis
        by (simp add: Asg)
    next
      case (Bool b)
      have "(q1, Bool b, q2) # \<pi> = ((q1, Bool b, q2) # \<pi>1) @ [e] @ \<pi>2"
        using \<pi>1_\<pi>2_e_p unfolding use_var_def by auto
      moreover
      have "\<not> (\<exists>e'\<in>set ((q1, Bool b, q2) # \<pi>1). x \<in> def_edge e')"
        using \<pi>1_\<pi>2_e_p unfolding use_var_def by auto
      ultimately
      have "use_var ((q1, Bool b, q2) # \<pi>) x"
        unfolding use_var_def using \<pi>1_\<pi>2_e_p by metis
      then show ?thesis
        using Bool by auto
    next
      case Skip
      have "(q1, Skip, q2) # \<pi> = ((q1, Skip, q2) # \<pi>1) @ [e] @ \<pi>2"
        using \<pi>1_\<pi>2_e_p unfolding use_var_def by auto
      moreover
      have "\<not> (\<exists>e'\<in>set ((q1, Skip, q2) # \<pi>1). x \<in> def_edge e')"
        using \<pi>1_\<pi>2_e_p unfolding use_var_def by auto
      ultimately
      have "use_var ((q1, Skip, q2) # \<pi>) x"
        unfolding use_var_def using \<pi>1_\<pi>2_e_p by metis
      then show ?thesis
        using Skip by auto
    qed
    then show "use_var (a # \<pi>) x"
      using a_split by auto
  next
    assume a: "x \<in> gen_set_LV a"
    obtain p \<alpha> q where a_split: "a = (p, \<alpha>, q)"
      by (cases a)
    have "use_var ((p, \<alpha>, q) # \<pi>) x"
      using a a_split unfolding use_var_def by (cases \<alpha>; force)
    then show "use_var (a # \<pi>) x"
      using a_split by auto
  qed
qed

lemma use_var_UNIV_S_hat_edge_list: "{x. use_var \<pi> x} = interpb.S_hat_edge_list \<pi> d_init_LV"
  using use_var_S_hat_edge_list S_hat_edge_list_use_var by auto
  
lemma use_path_S_hat_path: "use_path \<pi> = interpb.S_hat_path \<pi> d_init_LV"
  by (simp add: use_var_UNIV_S_hat_edge_list interpb.S_hat_path_def use_path_def)

definition summarizes_LV :: "(BV_pred, ('n,'v,'v) BV_elem) pred_val \<Rightarrow> bool" where
  "summarizes_LV \<rho> \<longleftrightarrow> (\<forall>\<pi> d. \<pi> \<in> LTS.path_with_word edge_set \<longrightarrow> LTS.get_end \<pi> = end \<longrightarrow> d \<in> use_path \<pi> \<longrightarrow>
     solves_query \<rho> (BV\<langle>[Encode_Node_BV (LTS.get_start \<pi>), Encode_Elem_BV d]\<rangle>.))"

lemma LV_sound:
  assumes "least_solution \<rho> (interpb.ana_pg_BV) s_BV"
  shows "summarizes_LV \<rho>"
proof -
  from assms have "interpb.summarizes_dl_BV \<rho>"
    using interpb.sound_rev_BV[of \<rho>] by auto
  then show ?thesis
    unfolding summarizes_LV_def interpb.summarizes_dl_BV_def interpb.edge_set_def edge_set_def
      interpb.end_def end_def use_path_S_hat_path by blast
qed
end




end
