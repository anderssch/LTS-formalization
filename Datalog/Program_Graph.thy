theory Program_Graph imports "../LTS" begin


section \<open>Actions\<close>

datatype 'v arith =
  Integer int
  | Var 'v
  | Arith_Op "'v arith" "int \<Rightarrow> int \<Rightarrow> int" "'v arith"
  | Minus "'v arith"

datatype 'v boolean =
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

datatype 'n node =
  Start
  | End
  | Node 'n

type_synonym ('n,'v) edge = "'n node * 'v action * 'n node"

type_synonym ('n,'v) program_graph = "('n,'v) edge set"

term "LTS.path_with_word :: ('n,'v) program_graph \<Rightarrow> ('n node list \<times> 'v action list) set"

section \<open>Execution Sequences\<close>

type_synonym ('n,'v) config = "'n node * 'v memory"

fun initial_config where
  "initial_config (n,\<sigma>) \<longleftrightarrow> n = Start"

fun final_config where
  "final_config (n,\<sigma>) \<longleftrightarrow> n = End"

inductive exe_step :: "('n,'v) program_graph \<Rightarrow> ('n,'v) config \<Rightarrow> 'v action \<Rightarrow> ('n,'v) config \<Rightarrow> bool" where
  "(q1, a, q2) \<in> pg \<Longrightarrow> sem_action a \<sigma> = Some \<sigma>' \<Longrightarrow> exe_step pg (q1,\<sigma>) a (q2,\<sigma>')"


section \<open>Reaching Definitions\<close>

type_synonym ('n,'v) triple = "'v * 'n node option * 'n node"

type_synonym ('n,'v) analysis_assignment = "'n node \<Rightarrow> ('n,'v) triple set"


subsection \<open>What is defined on a path\<close>

fun def_action :: "'v action \<Rightarrow> 'v set" where
  "def_action (x ::= a) = {x}"
| "def_action (Bool b) = {}"
| "def_action Skip = {}"

abbreviation def_edge :: "('n,'v) edge \<Rightarrow> 'v set" where
  "def_edge == \<lambda>(q1, a, q2). def_action a"

definition triple_of :: "'v \<Rightarrow> ('n,'v) edge \<Rightarrow> ('n,'v) triple" where
  "triple_of == (\<lambda>x (q1, a, q2). (x, Some q1, q2))"

definition def_var :: "('n,'v) edge list \<Rightarrow> 'v \<Rightarrow> ('n,'v) triple" where
  "def_var \<pi> x = (if (filter (\<lambda>e. x \<in> def_edge e) \<pi>) = []
                    then (x, None, Start)
                    else (triple_of x (last (filter (\<lambda>e. x \<in> def_edge e) \<pi>))))"

definition def_path :: "('n node list \<times> 'v action list) \<Rightarrow> ('n,'v) triple set" where
  "def_path \<pi> = (def_var (LTS.transition_list \<pi>) ` UNIV)"

definition summarizes :: "('n,'v) analysis_assignment \<Rightarrow> ('n,'v) program_graph \<Rightarrow> bool" where
  "summarizes RD pg \<longleftrightarrow> (\<forall>\<pi>. \<pi> \<in> LTS.path_with_word pg \<longrightarrow> LTS.get_start \<pi> = Start \<longrightarrow> def_path \<pi> \<subseteq> RD (LTS.get_end \<pi>))"

definition summarizes2 :: "('n,'v) analysis_assignment \<Rightarrow> ('n,'v) program_graph \<Rightarrow> bool" where
  "summarizes2 RD pg \<longleftrightarrow> (\<forall>\<pi> a b c. \<pi> \<in> LTS.path_with_word pg \<longrightarrow> LTS.get_start \<pi> = Start \<longrightarrow> (a, b, c) \<in> def_path \<pi> \<longrightarrow> (a, b, c) \<in> RD (LTS.get_end \<pi>))"
  

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


section \<open>Reaching Definitions in Datalog\<close>

datatype ('n,'v) RD_elem =
  RD_Node "'n node"
  | RD_Var 'v
  | Questionmark

datatype RD_var =
   the_\<u>
   | the_\<v>
   | the_\<w>

datatype RD_pred =
   the_RD1
   | the_VAR

abbreviation Encode_Node :: "'n node \<Rightarrow> (RD_var, ('n, 'v) RD_elem) identifier" where
  "Encode_Node n == DLElement (RD_Node n)"

fun Encode_Node_Q :: "'n node option \<Rightarrow> (RD_var, ('n, 'v) RD_elem) identifier" where
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

definition ana_entry_node :: "(RD_pred, RD_var, ('n,'v) RD_elem) clause set" where
  "ana_entry_node = 
     {
       RD1\<langle>[Encode_Node Start, \<u>, DLElement Questionmark, Encode_Node Start]\<rangle> :-
         [
           VAR[\<u>]
         ].
     }"


definition ana_pg :: "('n, 'v) program_graph \<Rightarrow> (RD_pred, RD_var, ('n,'v) RD_elem) clause set" where
  "ana_pg pg = \<Union>(ana_edge ` pg) \<union> ana_entry_node"

(* This makes VAR(x) true for the variables in the pg. This is not expanded so much on in the book. *)
definition var_contraints :: "(RD_pred, RD_var, ('n,'v) RD_elem) clause set" where
  "var_contraints = VAR_Cls ` UNIV"
(* Only makes sense if UNIV is finite. Alternatively I could calculate what variables are in
   the program and map VAR_Cls onto that set. *)


(* Jeg skal på en eller anden måde trylle datalog programmet om til en analysis assignment.
   Eller definere hvad det betyder for programmet at det er en analysis assignment.
   Eller definere hvad det betyder at \<rho> er en analysis assignment.
 *)

type_synonym ('n,'v) quadruple = "'n node *'v * 'n node option * 'n node"

definition summarizes_dl :: "(RD_pred,('n,'v) RD_elem) pred_val \<Rightarrow> ('n,'v) program_graph \<Rightarrow> bool" where
  "summarizes_dl \<rho> pg \<longleftrightarrow> (\<forall>\<pi> x q1 q2. \<pi> \<in> LTS.path_with_word pg \<longrightarrow> LTS.get_start \<pi> = Start \<longrightarrow> (x,q1,q2) \<in> def_path \<pi> \<longrightarrow> 
     solves_query \<rho> (RD1\<langle>[Encode_Node (LTS.get_end \<pi>), Encode_Var x, Encode_Node_Q q1, Encode_Node q2]\<rangle>.))"

lemma def_var_x: "fst (def_var ts x) = x"
  unfolding def_var_def by (simp add: case_prod_beta triple_of_def)

lemma last_def_transition:
  assumes "length ss = length w"
  assumes "x \<in> def_action l"
  assumes "(x, q1, q2) \<in> def_path (ss @ [s, s'], w @ [l])"
  shows "Some s = q1 \<and> s' = q2"
proof -
  obtain xa where xa_p: "(x, q1, q2) = def_var (transition_list (ss @ [s], w) @ [(s, l, s')]) xa"
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
  assumes "(x, q1, q2) \<in> def_path (ss @ [s, s'], w @ [l])"
  shows "(x, q1, q2) \<in> def_path (ss @ [s], w)"
proof -
  obtain y where y_p: "(x, q1, q2) = def_var (transition_list (ss @ [s], w) @ [(s, l, s')]) y"
    by (metis (no_types, lifting) assms(1) assms(3) def_path_def imageE transition_list_reversed_simp)
  have " (x, q1, q2) \<in> range (def_var (transition_list (ss @ [s], w)))"
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
  assumes "(ss,w) \<in> LTS.path_with_word pg"
  assumes "solves_program \<rho> (var_contraints \<union> ana_pg pg)"
  assumes "LTS.get_start (ss,w) = Start"
  assumes "(x,q1,q2) \<in> def_path (ss,w)"
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

  have "RD1\<langle>[Encode_Node Start, \<u>, DLElement Questionmark, Encode_Node Start]\<rangle> :-
         [
           VAR[\<u>]
         ]. \<in> ana_pg pg"
    unfolding ana_pg_def ana_entry_node_def by auto
  then have "(solves_cls \<rho> (RD1\<langle>[Encode_Node Start, \<u>, DLElement Questionmark, Encode_Node Start]\<rangle> :-
         [
           VAR[\<u>]
         ].))"
    using assms(2) unfolding solves_program_def by auto 
   then have "\<forall>y. meaning_cls (RD1\<langle>[Encode_Node Start, \<u>, DLElement Questionmark, Encode_Node Start]\<rangle> :-
         [
           VAR[\<u>]
         ].) \<rho> y"
     unfolding solves_cls_def by metis
   then have "meaning_cls (RD1\<langle>[Encode_Node Start, \<u>, DLElement Questionmark, Encode_Node Start]\<rangle> :-
         [
           VAR[\<u>]
         ].) \<rho> (\<lambda>v. RD_Var x)"
     by presburger
   then have "[RD_Var x] \<in> \<rho> the_VAR \<longrightarrow> [RD_Node Start, RD_Var x, Questionmark, RD_Node Start] \<in> \<rho> the_RD1"
     by simp
   then have "[RD_Node Start, RD_Var x, Questionmark, RD_Node Start] \<in> \<rho> the_RD1"
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
    from True have "\<exists>e. (s,x ::= e,s') \<in> pg"
      using "2.hyps"(2) by (cases l) auto
    then have "RD1\<langle>[Encode_Node q2, Encode_Var x, Encode_Node_Q q1, Encode_Node q2]\<rangle> :- []. \<in> ana_pg pg"
      using True ana_pg_def sq by fastforce
    then have "solves_cls \<rho> (RD1\<langle>[Encode_Node q2, Encode_Var x, Encode_Node_Q q1, Encode_Node q2]\<rangle> :- [].)"
      using 2(5) unfolding solves_program_def by auto
    then have "solves_query \<rho> RD1\<langle>[Encode_Node q2, Encode_Var x, Encode_Node_Q q1, Encode_Node q2]\<rangle>."
      using solves_fact_query by metis 
    then show ?thesis
      by (simp add: LTS.get_end_def sq)
  next
    case False
    then have x_is_def: "(x, q1, q2) \<in> def_path (ss @ [s], w)" using 2(7)
      using not_last_def_transition len by force
    then have "solves_query \<rho> (RD1\<langle>[Encode_Node (LTS.get_end (ss @ [s], w)), Encode_Var x, Encode_Node_Q q1, Encode_Node q2]\<rangle>.)"
    proof -
      have "(ss @ [s], w) \<in> LTS.path_with_word pg"
        using 2(1) by auto
      moreover
      have "solves_program \<rho> (var_contraints \<union> ana_pg pg)"
        using 2(5) by auto
      moreover
      have "LTS.get_start (ss @ [s], w) = Start"
        using 2(6)
        by (metis append_self_conv2 fst_conv LTS.get_start_def hd_append2 list.sel(1)) 
      moreover
      have "(x, q1, q2) \<in> def_path (ss @ [s], w)"
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
      have "(s, y ::= e, s') \<in> pg"
        using "2.hyps"(2) Asg by auto
      then have "RD1\<langle>[Encode_Node s', \<u>, \<v>, \<w>]\<rangle> :-
          [
            RD1[Encode_Node s, \<u>, \<v>, \<w>],
            \<u> \<^bold>\<noteq> (Encode_Var y)
          ]. \<in> ana_pg pg"
        unfolding ana_pg_def by force
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
      have "(s, Bool b, s') \<in> pg"
        using "2.hyps"(2) Bool by auto
      then have "RD1\<langle>[Encode_Node s', \<u>, \<v>, \<w>]\<rangle> :-
         [
           RD1[Encode_Node s, \<u>, \<v>, \<w>]
         ]. \<in> ana_pg pg"
        unfolding ana_pg_def by force
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
      have "(s, Skip, s') \<in> pg"
        using "2.hyps"(2) Skip by auto
      then have "RD1\<langle>[Encode_Node s', \<u>, \<v>, \<w>]\<rangle> :-
         [
           RD1[Encode_Node s, \<u>, \<v>, \<w>]
         ]. \<in> ana_pg pg"
        unfolding ana_pg_def by force
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
  using assms RD_sound' unfolding summarizes_dl_def by fastforce 


section \<open>Bitvector framework\<close>

datatype BV_pred =
   the_BV
   | the_notkill
   | the_gen

datatype BV_var =
   the_\<uu>

abbreviation "BV == PosRh the_BV"
abbreviation "notkill == PosRh the_notkill"
abbreviation "gen == PosRh the_gen"

abbreviation BV_Cls :: "(BV_var, 'e) identifier list \<Rightarrow> (BV_pred, BV_var, 'e) righthand list \<Rightarrow> (BV_pred, BV_var, 'e) clause" ("BV\<langle>_\<rangle> :- _ .") where 
   "BV\<langle>args\<rangle> :- ls. \<equiv> Cls the_BV args ls"

abbreviation not_kill_Cls :: "(BV_var, 'e) identifier list \<Rightarrow> (BV_pred, BV_var, 'e) righthand list \<Rightarrow> (BV_pred, BV_var, 'e) clause" ("notkill\<langle>_\<rangle> :- _ .") where 
   "notkill\<langle>args\<rangle> :- ls. \<equiv> Cls the_notkill args ls"

abbreviation genn_Cls :: "(BV_var, 'e) identifier list \<Rightarrow> (BV_pred, BV_var, 'e) righthand list \<Rightarrow> (BV_pred, BV_var, 'e) clause" ("gen\<langle>_\<rangle> :- _ .") where 
   "gen\<langle>args\<rangle> :- ls. \<equiv> Cls the_gen args ls"

abbreviation BV_Query :: "(BV_var, 'e) identifier list \<Rightarrow> (BV_pred, BV_var, 'e) query" ("BV\<langle>_\<rangle>.") where 
   "BV\<langle>args\<rangle>. \<equiv> (the_BV, args)"

datatype ('n,'v,'elem) BV_elem =
  BV_Node "'n node"
  | BV_Elem 'elem
  | BV_Action "'v action"

abbreviation \<uu> :: "(BV_var, 'a) identifier" where
  "\<uu> == DLVar the_\<uu>"

abbreviation Encode_Node_BV :: "'n node \<Rightarrow> (BV_var, ('n, 'v, 'elem) BV_elem) identifier" where
  "Encode_Node_BV n == DLElement (BV_Node n)"

abbreviation Encode_Elem_BV :: "'elem \<Rightarrow> (BV_var, ('n, 'v, 'elem) BV_elem) identifier" where
  "Encode_Elem_BV e == DLElement (BV_Elem e)"

abbreviation Encode_Action_BV :: "'v action \<Rightarrow> (BV_var, ('n, 'v, 'elem) BV_elem) identifier" where
  "Encode_Action_BV \<alpha> == DLElement (BV_Action \<alpha>)"

locale analysis_BV =
  fixes kill_set :: "('n,'v) edge \<Rightarrow> 'd set"
  fixes gen_set :: "('n,'v) edge \<Rightarrow> 'd set"
  fixes d_init :: "'d set"
begin

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

definition S_hat_path :: "('n node list \<times> 'v action list) \<Rightarrow> 'd set \<Rightarrow> 'd set" where
  "S_hat_path \<pi> = S_hat_edge_list (LTS.transition_list \<pi>)"

lemma S_hat_path_mono:
  assumes "d1 \<subseteq> d2"
  shows "S_hat_path \<pi> d1 \<subseteq> S_hat_path \<pi> d2"
  unfolding S_hat_path_def using assms S_hat_edge_list_mono by auto

fun ana_kill_BV :: "(('n, 'v) edge * 'd) \<Rightarrow> (BV_pred, BV_var, ('n, 'v, 'd) BV_elem) clause set" where
  "ana_kill_BV ((q\<^sub>o, \<alpha>, q\<^sub>s), d) =
   (
   if d \<notin> kill_set (q\<^sub>o, \<alpha>, q\<^sub>s) then
     {notkill\<langle>[Encode_Node_BV q\<^sub>o, Encode_Action_BV \<alpha>, Encode_Node_BV q\<^sub>s, Encode_Elem_BV d]\<rangle> :- [].}
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
       BV\<langle>[Encode_Node_BV Start, Encode_Elem_BV d]\<rangle> :- [].
     }"

fun ana_edge_BV :: "('n, 'v) edge \<Rightarrow> (BV_pred, BV_var, ('n, 'v, 'd) BV_elem) clause set" where
  "ana_edge_BV (q\<^sub>o, \<alpha>, q\<^sub>s) =
     {
        BV\<langle>[Encode_Node_BV q\<^sub>s, \<uu>]\<rangle> :-
          [
            BV[Encode_Node_BV q\<^sub>o, \<uu>],
            notkill[Encode_Node_BV q\<^sub>o, Encode_Action_BV \<alpha>, Encode_Node_BV q\<^sub>s, \<uu>]
          ].
        ,
        BV\<langle>[Encode_Node_BV q\<^sub>s, \<uu>]\<rangle> :- [gen[Encode_Node_BV q\<^sub>o, Encode_Action_BV \<alpha>, Encode_Node_BV q\<^sub>s, \<uu>]].
     }"

definition ana_pg_BV :: "('n, 'v) program_graph \<Rightarrow> (BV_pred, BV_var, ('n, 'v, 'd) BV_elem) clause set" where
  "ana_pg_BV pg = \<Union>(ana_edge_BV ` pg) 
                  \<union> \<Union>(ana_init_BV ` d_init)
                  \<union> \<Union>(ana_kill_BV ` (pg \<times> UNIV))
                  \<union> \<Union>(ana_gen_BV ` (pg \<times> UNIV))"

definition summarizes_dl_BV :: "(BV_pred, ('n, 'v, 'd) BV_elem) pred_val \<Rightarrow> ('n, 'v) program_graph \<Rightarrow> bool" where
  "summarizes_dl_BV \<rho> pg \<longleftrightarrow> (\<forall>\<pi> d. \<pi> \<in> LTS.path_with_word pg \<longrightarrow> LTS.get_start \<pi> = Start \<longrightarrow> d \<in> S_hat_path \<pi> d_init \<longrightarrow> 
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

lemma sound_BV': 
  assumes "(ss,w) \<in> LTS.path_with_word pg"
  assumes "solves_program \<rho> (ana_pg_BV pg)"
  assumes "LTS.get_start (ss,w) = Start"
  assumes "d \<in> S_hat_path (ss,w) d_init"
  shows "solves_query \<rho> BV\<langle>[Encode_Node_BV (LTS.get_end (ss,w)), Encode_Elem_BV d]\<rangle>."
  using assms 
proof (induction arbitrary: d rule: LTS.path_with_word_induct_reverse[OF assms(1)])
  case (1 s)
  from 1(1,3) have start_end: "LTS.get_end ([s], []) = Start"
    using LTS.singleton_path_start_end[of s pg, OF 1(1)] by (metis LTS.get_end_def prod.sel(1))

  from 1 have "S_hat_path ([s], []) d_init = d_init"
    unfolding S_hat_path_def by auto
  then have "d \<in> d_init"
    using 1(4) by auto
  moreover
  from 1(2) have "\<forall>d \<in> d_init. solves_cls \<rho> (BV\<langle>[Encode_Node_BV Start, Encode_Elem_BV d]\<rangle> :- [].)"
    unfolding ana_pg_BV_def ana_init_BV_def solves_program_def by auto
  ultimately have "solves_cls \<rho> (BV\<langle>[Encode_Node_BV Start, Encode_Elem_BV d]\<rangle> :- [].)"
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
  moreover have "... = S_hat (qnminus1, l, qn) (S_hat_path (qs @ [qnminus1], w) d_init)"
    by simp
  moreover have "... \<subseteq> S_hat (qnminus1, l, qn) {d. solves_query \<rho> BV\<langle>[Encode_Node_BV qnminus1, Encode_Elem_BV d]\<rangle>.}"
    by (metis f LTS.get_end_def last_snoc prod.sel(1))
  ultimately have "S_hat_path (qs @ [qnminus1, qn], w @ [l]) d_init \<subseteq> S_hat (qnminus1, l, qn) {d. solves_query \<rho> BV\<langle>[Encode_Node_BV qnminus1, Encode_Elem_BV d]\<rangle>.}"
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
    have e_in_pg: "(qnminus1, l, qn) \<in> pg"
      using "2.hyps"(2) by blast

    have "\<forall>c \<in> ana_edge_BV (qnminus1, l, qn). solves_cls \<rho> c"
      using 2(5) e_in_pg unfolding ana_pg_BV_def solves_program_def by blast
    then have "solves_cls \<rho> BV\<langle>[Encode_Node_BV qn, \<uu>]\<rangle> :- [BV[Encode_Node_BV qnminus1,  \<uu>], notkill[Encode_Node_BV qnminus1, Encode_Action_BV l, Encode_Node_BV qn, \<uu>]]."
      by auto
    then have "solves_cls \<rho> BV\<langle>[Encode_Node_BV qn, Encode_Elem_BV d]\<rangle> :- [BV[Encode_Node_BV qnminus1, Encode_Elem_BV d], notkill[Encode_Node_BV qnminus1, Encode_Action_BV l, Encode_Node_BV qn, Encode_Elem_BV d]]."
      using substitution_rule[of \<rho> _ "\<lambda>u. Encode_Elem_BV d"]
      by force
    moreover
    from a have a_2:  "d \<notin> kill_set (qnminus1, l, qn)"
      by auto
    have "\<forall>c\<in>\<Union>(ana_kill_BV ` (pg \<times> UNIV)). solves_cls \<rho> c"
      using 2(5) unfolding ana_pg_BV_def solves_program_def by auto
    then have "\<forall>c\<in>ana_kill_BV ((qnminus1, l, qn),d). solves_cls \<rho> c"
      using e_in_pg by blast
    then have "solves_cls \<rho> notkill\<langle>[Encode_Node_BV qnminus1, Encode_Action_BV l, Encode_Node_BV qn, Encode_Elem_BV d]\<rangle> :- []."
      using a_2 by auto
    ultimately
    show "solves_query \<rho> BV\<langle>[Encode_Node_BV qn, Encode_Elem_BV d]\<rangle>."
      by (metis a_1 append.left_neutral append_Cons solves_cls_iff_solves_rh resolution_last_rh resolution_only_rh_query)
  next
    assume a: "d \<in> gen_set (qnminus1, l, qn)"
    have e_in_pg: "(qnminus1, l, qn) \<in> pg"
      using "2.hyps"(2) by blast

    have "\<forall>c \<in> ana_edge_BV (qnminus1, l, qn). solves_cls \<rho> c"
      using 2(5) e_in_pg unfolding ana_pg_BV_def solves_program_def by blast
    then have "solves_cls \<rho> BV\<langle>[Encode_Node_BV qn, \<uu>]\<rangle> :- [gen[Encode_Node_BV qnminus1, Encode_Action_BV l, Encode_Node_BV qn, \<uu>]]."
      by auto
    then have "solves_cls \<rho> BV\<langle>[Encode_Node_BV qn, Encode_Elem_BV d]\<rangle> :- [gen[Encode_Node_BV qnminus1, Encode_Action_BV l, Encode_Node_BV qn, Encode_Elem_BV d]]."
      using substitution_rule[of \<rho> _ "\<lambda>u. Encode_Elem_BV d" ]
      by force
    moreover
    have "\<forall>c\<in>\<Union>(ana_gen_BV ` (pg \<times> UNIV)). solves_cls \<rho> c"
      using 2(5) unfolding ana_pg_BV_def solves_program_def by auto
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
  assumes "solves_program \<rho> (ana_pg_BV pg)"
  shows "summarizes_dl_BV \<rho> pg"
  using sound_BV' assms unfolding summarizes_dl_BV_def by fastforce

end


section \<open>Reaching definitions revisited\<close>

fun kill_set_RD :: "('n,'v) edge \<Rightarrow> ('n,'v) triple set" where
  "kill_set_RD (q\<^sub>o, x ::= a, q\<^sub>s) = {x} \<times> UNIV \<times> UNIV"
| "kill_set_RD (q\<^sub>o, Bool b, q\<^sub>s) = {}"
| "kill_set_RD (v, Skip, vc) = {}"

fun gen_set_RD :: "('n,'v) edge \<Rightarrow> ('n,'v) triple set" where
  "gen_set_RD (q\<^sub>o, x ::= a, q\<^sub>s) = {x} \<times> {Some q\<^sub>o} \<times> {q\<^sub>s}"
| "gen_set_RD (q\<^sub>o, Bool b, q\<^sub>s) = {}"
| "gen_set_RD (v, Skip, vc) = {} "

definition d_init_RD :: "('n,'v) triple set" where
  "d_init_RD = (UNIV \<times> {None} \<times> {Start})"

interpretation interp: analysis_BV kill_set_RD gen_set_RD d_init_RD .

lemma def_var_def_edge_S_hat:
  assumes "def_var \<pi> x \<in> R"
  assumes "x \<notin> def_edge t"
  shows "def_var \<pi> x \<in> interp.S_hat t R"
proof -
  define q1 where "q1 = fst t"
  define \<alpha> where "\<alpha> = fst (snd t)"
  define q2 where "q2 = snd (snd t)"
  have t_def: "t = (q1, \<alpha>, q2)"
    by (simp add: \<alpha>_def q1_def q2_def)

  from assms(2) have assms_2: "x \<notin> def_edge (q1, \<alpha>, q2)"
    unfolding t_def by auto

  have "def_var \<pi> x \<in> interp.S_hat (q1, \<alpha>, q2) R"
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

lemma def_var_S_hat_edge_list: "(def_var \<pi>) x \<in> interp.S_hat_edge_list \<pi> d_init_RD"
proof (induction \<pi> rule: rev_induct)
  case Nil
  then show ?case
    unfolding def_var_def d_init_RD_def by auto
next
  case (snoc t \<pi>)
  then show ?case
  proof (cases "x \<in> def_edge t")
    case True
    then have "def_var (\<pi> @[t]) x = def_var [t] x"
      by (simp add: def_var_def)
    moreover
    have "interp.S_hat_edge_list (\<pi> @ [t]) d_init_RD = interp.S_hat t (interp.S_hat_edge_list \<pi> d_init_RD)"
      unfolding interp.S_hat_edge_list_def2 by simp
    moreover
    obtain q1 \<alpha> q2 where t_split: "t = (q1, \<alpha>, q2)"
      using prod_cases3 by blast
    moreover
    have "def_var [t] x \<in> interp.S_hat t (interp.S_hat_edge_list \<pi> d_init_RD)"
      unfolding interp.S_hat_def def_var_def triple_of_def using True t_split by (cases \<alpha>) auto
    ultimately
    show ?thesis by auto
  next
    case False
    obtain q1 \<alpha> q2 where t_split: "t = (q1, \<alpha>, q2)"
      using prod_cases3 by blast
    from False have "def_var (\<pi> @ [t]) x = def_var \<pi> x"
      by (simp add: def_var_def)
    moreover
    from snoc.IH have "def_var \<pi> x \<in> interp.S_hat t (interp.S_hat_edge_list \<pi> d_init_RD)"
      by (simp add: False def_var_def_edge_S_hat)
    then have "def_var \<pi> x \<in> interp.S_hat_edge_list (\<pi> @ [t]) d_init_RD"
      unfolding interp.S_hat_edge_list_def2 by simp
    ultimately
    show ?thesis
      using snoc by auto
  qed
qed

lemma def_var_UNIV_S_hat_edge_list: "(def_var \<pi>) ` UNIV \<subseteq> interp.S_hat_edge_list \<pi> d_init_RD"
  using def_var_S_hat_edge_list by force

lemma def_path_S_hat_path: "def_path \<pi> \<subseteq> interp.S_hat_path \<pi> d_init_RD"
  by (simp add: analysis_BV.S_hat_path_def def_path_def def_var_UNIV_S_hat_edge_list)

definition summarizes_RD :: "(BV_pred, ('n,'v,('n,'v) triple) BV_elem) pred_val \<Rightarrow> ('n,'v) program_graph \<Rightarrow> bool" where
  "summarizes_RD \<rho> pg \<longleftrightarrow> (\<forall>\<pi> d. \<pi> \<in> LTS.path_with_word pg \<longrightarrow> LTS.get_start \<pi> = Start \<longrightarrow> d \<in> def_path \<pi> \<longrightarrow>
     solves_query \<rho> (BV\<langle>[Encode_Node_BV (LTS.get_end \<pi>), Encode_Elem_BV d]\<rangle>.))"

lemma RD_sound_again: 
  assumes "solves_program \<rho> (interp.ana_pg_BV pg)"
  shows "summarizes_RD \<rho> pg"
  using assms def_path_S_hat_path interp.sound_BV unfolding interp.summarizes_dl_BV_def summarizes_RD_def by force


locale analysis_BV_backwards =
  fixes kill_set :: "('n,'v) edge \<Rightarrow> 'd set"
  fixes gen_set :: "('n,'v) edge \<Rightarrow> 'd set"
  fixes d_init :: "'d set"
begin

(* "URGENT TODO:" Define what summarizes means here. *)


fun swap_start_end :: "'n node \<Rightarrow> 'n node" where
  "swap_start_end Start = End" |
  "swap_start_end End = Start" |
  "swap_start_end (Node n) = Node n"

definition rev_edge :: "('n,'v) edge \<Rightarrow> ('n,'v) edge" where
  "rev_edge = (\<lambda>(q\<^sub>s,\<alpha>,q\<^sub>o). (swap_start_end q\<^sub>o, \<alpha>, swap_start_end q\<^sub>s))"

fun rev_path_with_word :: "'n node list * 'v action list \<Rightarrow> 'n node list * 'v action list" where
  "rev_path_with_word (es,ls) = (map swap_start_end (rev es), rev ls)"

definition rev_graph :: "('n,'v) program_graph \<Rightarrow> ('n,'v) program_graph" where
  "rev_graph pg = rev_edge ` pg"

definition "S_hat" :: "('n,'v) edge \<Rightarrow> 'd set \<Rightarrow> 'd set" where
  "S_hat e R = (R - kill_set (rev_edge e)) \<union> gen_set (rev_edge e)"

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

definition S_hat_path :: "('n node list \<times> 'v action list) \<Rightarrow> 'd set \<Rightarrow> 'd set" where
  "S_hat_path \<pi> = S_hat_edge_list (LTS.transition_list \<pi>)"

definition summarizes_dl_BV :: "(BV_pred, ('n, 'v, 'd) BV_elem) pred_val \<Rightarrow> ('n, 'v) program_graph \<Rightarrow> bool" where
  "summarizes_dl_BV \<rho> pg \<longleftrightarrow> (\<forall>\<pi> d. \<pi> \<in> LTS.path_with_word pg \<longrightarrow> LTS.get_end \<pi> = End \<longrightarrow> d \<in> S_hat_path \<pi> d_init \<longrightarrow> 
     solves_query \<rho> (BV\<langle>[Encode_Node_BV (LTS.get_start \<pi>), Encode_Elem_BV d]\<rangle>.))"

interpretation fa: analysis_BV kill_set gen_set d_init .

term LTS.path_with_word

term rev

(* Maybe I need a better way to swap Start and End *)
(* And also there is a problem in my current graph reversal. I need to map rev_node
   onto the graph. I think that that will solve the "better way to swap Start and End problem"
 *)
lemma xxx:
  assumes "(ss,w) \<in> LTS.path_with_word pg"
  assumes "LTS.get_end (ss,w) = End"
  assumes "d \<in> S_hat_path (ss,w) d_init"
  assumes "fa.summarizes_dl_BV \<rho> (rev_graph pg)"
  shows "solves_query \<rho> BV\<langle>[Encode_Node_BV (LTS.get_start (ss,w)), Encode_Elem_BV d]\<rangle>."
  using assms
proof (induction arbitrary: d rule: LTS.path_with_word_induct_reverse[OF assms(1)])
  case (1 s)

  have a: "rev_path_with_word ([End], []) \<in> LTS.path_with_word (rev_graph pg)"
    apply auto
    by (simp add: LTS.path_with_word.path_with_word_refl)
  
  have b: "LTS.get_start (rev_path_with_word ([End], [])) = Start"
    (* Her går det vist galt!!!!! *)
    sorry
  
  have c: "d \<in> fa.S_hat_path (rev_path_with_word ([End], [])) d_init"
    sorry
  
  have d: "rev_path_with_word ([End], []) = ([Start], [])"
    sorry
  
  have x: "\<And>\<pi> d. \<pi> \<in> LTS.path_with_word (rev_graph pg) \<Longrightarrow> LTS.get_start \<pi> = Start \<Longrightarrow> d \<in> fa.S_hat_path \<pi> d_init \<Longrightarrow> solves_query \<rho> BV\<langle>[Encode_Node_BV (LTS.get_end \<pi>), Encode_Elem_BV d]\<rangle>."
    using 1(4) unfolding fa.summarizes_dl_BV_def by auto
  have t: "rev_path_with_word ([End], []) \<in> LTS.path_with_word (rev_graph pg) \<Longrightarrow>
  LTS.get_start (rev_path_with_word ([End], [])) = Start \<Longrightarrow>
  d \<in> fa.S_hat_path (rev_path_with_word ([End], [])) d_init \<Longrightarrow> solves_query \<rho> BV\<langle>[Encode_Node_BV (LTS.get_end (rev_path_with_word ([End], []))), Encode_Elem_BV d]\<rangle>."
    using x[of "rev_path_with_word ([End], [])" d] by auto
  
  have "solves_query \<rho> BV\<langle>[Encode_Node_BV (LTS.get_end ([Start], [])), Encode_Elem_BV d]\<rangle>."
    using t[OF a b c] using d by (simp add: LTS.get_end_def) 
  moreover
  have "s = End"
    by (metis "1"(2) LTS.get_end_def last_ConsL prod.sel(1))
  ultimately
  show ?case
    by auto
next
  case (2 ss s w l s')
  then show ?case sorry
qed

lemma 
  assumes "fa.summarizes_dl_BV \<rho> (rev_graph pg)"
  shows "summarizes_dl_BV \<rho> pg"
  using assms unfolding summarizes_dl_BV_def
  using xxx
  by fastforce

lemma sound_rev_BV:
  undefined
  using fa.sound_BV[of _ "rev_graph _"]
  oops


end

end
