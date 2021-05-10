theory Program_Graph imports "../Morten/LTS" begin


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
(* For program graphs there are some reachability requirements on Start and End, 
   but we ignore them for now. *)

definition get_start :: "('n node list \<times> 'v action list) \<Rightarrow> 'n node" where
  "get_start \<pi> = hd (fst \<pi>)"
(* TODO: Make a better path representation. *)

definition get_end :: "('n node list \<times> 'v action list) \<Rightarrow> 'n node" where
  "get_end \<pi> = last (fst \<pi>)"

term "LTS.path_with_word :: ('n,'v) program_graph \<Rightarrow> ('n node list \<times> 'v action list) set"

term transitions_of

definition transition_list_of :: "'a list \<times> 'b list \<Rightarrow> ('a \<times> 'b \<times> 'a) list" where
  "transition_list_of = undefined"


section \<open>Execution Sequences\<close>

type_synonym ('n,'v) config = "'n node * 'v memory"

fun initial_config where
  "initial_config (n,\<sigma>) \<longleftrightarrow> n = Start"

fun final_config where
  "final_config (n,\<sigma>) \<longleftrightarrow> n = End"

inductive exe_step :: "('n,'v) program_graph \<Rightarrow> ('n,'v) config \<Rightarrow> 'v action \<Rightarrow> ('n,'v) config \<Rightarrow> bool" where
  "(q1, a, q2) \<in> pg \<Longrightarrow> sem_action a \<sigma> = Some \<sigma>' \<Longrightarrow> exe_step pg (q1,\<sigma>) a (q2,\<sigma>')"

(* Define datalog syntax *)
(* Construct the clauses as on page 162 *)

(* Definition 2.5: 
   What does it mean for an assignment to summarize a set of paths.
   Well, what is an assignment even for datalog.

*)


section \<open>Reaching Definitions\<close>

type_synonym ('n,'v) triple = "'v * 'n node option * 'n node"
(* Kan dette modelleres smartere? *)

type_synonym ('n,'v) analysis_assignment = "'n node \<Rightarrow> ('n,'v) triple set"



subsection \<open>What is defined on a path\<close>

fun def_action :: "'v action \<Rightarrow> 'v set" where
  "def_action (x ::= a) = {x}"
| "def_action (Bool b) = {}"
| "def_action Skip = {}"

abbreviation def_edge :: "('n,'v) edge \<Rightarrow> 'v set" where
  "def_edge == \<lambda>(q1, a, q2). def_action a"

abbreviation triple_of :: "'v \<Rightarrow> ('n,'v) edge \<Rightarrow> ('n,'v) triple" where
  "triple_of == (\<lambda>x (q1, a, q2). (x, Some q1, q2))"

definition def_var :: "('n,'v) edge list \<Rightarrow> 'v \<Rightarrow> ('n,'v) triple" where
  "def_var \<pi> x = (if (filter (\<lambda>e. x \<in> def_edge e) \<pi>) = []
                    then (x, None, Start) 
                    else (triple_of x (last (filter (\<lambda>e. x \<in> def_edge e) \<pi>))))"

definition def_path :: "('n node list \<times> 'v action list) \<Rightarrow> ('n,'v) triple set" where
  "def_path \<pi> = (def_var (transition_list_of \<pi>) ` UNIV)"
(* Giver vel kun mening med et fixed og endeligt univers af variable.
   Eller hvad?
*)

definition summarizes :: "('n,'v) analysis_assignment \<Rightarrow> ('n,'v) program_graph \<Rightarrow> bool" where
  "summarizes RD pg \<longleftrightarrow> (\<forall>\<pi>. \<pi> \<in> LTS.path_with_word pg \<longrightarrow> get_start \<pi> = Start \<longrightarrow> def_path \<pi> \<subseteq> RD (get_end \<pi>))"
(* Empty path? *)

definition summarizes2 :: "('n,'v) analysis_assignment \<Rightarrow> ('n,'v) program_graph \<Rightarrow> bool" where
  "summarizes2 RD pg \<longleftrightarrow> (\<forall>\<pi> a b c. \<pi> \<in> LTS.path_with_word pg \<longrightarrow> get_start \<pi> = Start \<longrightarrow> (a, b, c) \<in> def_path \<pi> \<longrightarrow> (a, b, c) \<in> RD (get_end \<pi>))"
  

section \<open>Datalog programs and their solutions\<close>

datatype ('x,'e) identifier = DLVar 'x | DLElement 'e

datatype ('p,'x,'e) righthand = 
  Eql "('x,'e) identifier" "('x,'e) identifier" ("_ \<^bold>= _" [1000, 61] 61)
  | Neql "('x,'e) identifier" "('x,'e) identifier" ("_ \<^bold>\<noteq> _" [1000, 61] 61)
  | PosRh 'p "('x,'e) identifier list"
  | NegRh 'p "('x,'e) identifier list"

datatype ('p,'x,'e) clause = Cls 'p "('x,'e) identifier list" "('p,'x,'e) righthand list" (* Why not righthand set? *)

type_synonym ('p,'x,'e) dl_program = "('p,'x,'e) clause set" (* Set or list? *)

type_synonym ('x,'e) var_val = "'x \<Rightarrow> 'e"

type_synonym ('p,'e) pred_val = "'p \<Rightarrow> 'e list set"

fun eval_id :: "('x,'e) var_val \<Rightarrow> ('x,'e) identifier \<Rightarrow> 'e" where
  "eval_id \<sigma> (DLVar x) = \<sigma> x"
| "eval_id \<sigma> (DLElement e) = e"

fun meaning_rh :: "('p,'x,'e) righthand \<Rightarrow> ('p,'e) pred_val \<Rightarrow> ('x,'e) var_val \<Rightarrow> bool" where
  "meaning_rh (a \<^bold>= a') \<rho> \<sigma> \<longleftrightarrow> eval_id \<sigma> a = eval_id  \<sigma> a'"
| "meaning_rh (a \<^bold>\<noteq> a') \<rho> \<sigma> \<longleftrightarrow> eval_id \<sigma> a \<noteq> eval_id \<sigma> a'"
| "meaning_rh (PosRh p ids) \<rho> \<sigma> \<longleftrightarrow> map (eval_id \<sigma>) ids \<in> \<rho> p"
| "meaning_rh (NegRh p ids) \<rho> \<sigma> \<longleftrightarrow> \<not> map (eval_id \<sigma>) ids \<in> \<rho> p"

fun meaning_cls :: "('p,'x,'e) clause \<Rightarrow> ('p,'e) pred_val \<Rightarrow> ('x,'e) var_val \<Rightarrow> bool" where
  "meaning_cls (Cls p ids rhs) \<rho> \<sigma> \<longleftrightarrow> ((\<forall>rh\<in>set rhs. meaning_rh rh \<rho> \<sigma>) \<longrightarrow> map (eval_id \<sigma>) ids \<in> \<rho> p)"

definition solves_cls :: "('p,'e) pred_val \<Rightarrow> ('p,'x,'e) clause \<Rightarrow> bool" where
  "solves_cls \<rho> c \<longleftrightarrow> (\<forall>\<sigma>. meaning_cls c \<rho> \<sigma>)"

fun solves_program :: "('p,'e) pred_val \<Rightarrow> ('p,'x,'e) dl_program \<Rightarrow> bool" where
  "solves_program \<rho> dl \<longleftrightarrow> (\<forall>c \<in> dl. solves_cls \<rho> c)"


section \<open>Queries (not in the book?)\<close>

type_synonym ('p,'x,'e) query = "'p * ('x,'e) identifier list"

fun solves_query :: "('p,'e) pred_val \<Rightarrow> ('p,'x,'e) query \<Rightarrow> bool" where
  "solves_query \<rho> (p,ids) \<longleftrightarrow> (\<forall>\<sigma>. map (eval_id \<sigma>) ids \<in> \<rho> p)" (* Is this correct?!?!?!?! *)


section \<open>Reaching Definitions in Datalog\<close>

datatype ('n,'v) RD_elem =
  RD_Node "'n node"
  | RD_Var 'v
  | Questionmark

datatype RD_var =
   the_\<uu>
   | the_\<v>
   | the_\<w>

datatype RD_pred =
   the_RD1
   | the_VAR

abbreviation Encode_Node :: "'n node \<Rightarrow> ('x, ('n, 'v) RD_elem) identifier" where (* 'x could also be RD_var... *)
  "Encode_Node n == DLElement (RD_Node n)"

fun Encode_Node_Q :: "'n node option \<Rightarrow> ('x, ('n, 'v) RD_elem) identifier" where
  "Encode_Node_Q (Some n) = DLElement (RD_Node n)"
| "Encode_Node_Q None = DLElement Questionmark"

abbreviation Encode_Var :: "'v \<Rightarrow> ('x, ('n, 'v) RD_elem) identifier" where
  "Encode_Var v == DLElement (RD_Var v)"

abbreviation RD1_Cls :: "('x, 'e) identifier list \<Rightarrow> (RD_pred, 'x, 'e) righthand list \<Rightarrow> (RD_pred, 'x, 'e) clause" ("RD1\<langle>_\<rangle> <- _ ") where 
   "RD1\<langle>args\<rangle> <- ls \<equiv> Cls the_RD1 args ls"

abbreviation "RD1 == PosRh the_RD1"
abbreviation "VAR == PosRh the_VAR"

abbreviation \<uu> :: "(RD_var, 'a) identifier" where
  "\<uu> == DLVar the_\<uu>"

abbreviation \<v> :: "(RD_var, 'a) identifier" where
  "\<v> == DLVar the_\<v>"

abbreviation \<w> :: "(RD_var, 'a) identifier" where
   "\<w> == DLVar the_\<w>"

fun ana_edge :: "('n, 'v) edge \<Rightarrow> (RD_pred, RD_var, ('n,'v) RD_elem) clause set" where
  "ana_edge (q\<^sub>s, x ::= a,q\<^sub>o) =
     {
        RD1\<langle>[Encode_Node q\<^sub>s, \<uu>, \<v>, \<w>]\<rangle> <-
          [
            RD1[Encode_Node q\<^sub>o, \<uu>, \<v>, \<w>],
            \<uu> \<^bold>\<noteq> (Encode_Var x)
          ]
        ,
        RD1\<langle>[Encode_Node q\<^sub>s, Encode_Var x, Encode_Node q\<^sub>o, Encode_Node q\<^sub>s]\<rangle> <- []
     }"
| "ana_edge (q\<^sub>s, Bool b, q\<^sub>o) =
     {
       RD1\<langle>[Encode_Node q\<^sub>s, \<uu>, \<v>, \<w>]\<rangle> <-
         [
           RD1[Encode_Node q\<^sub>o, \<uu>, \<v>, \<w>]
         ]
     }"
| "ana_edge (q\<^sub>s, Skip, q\<^sub>o) =
     {
       RD1\<langle>[Encode_Node q\<^sub>s, \<uu>, \<v>, \<w>]\<rangle> <-
         [
           RD1[Encode_Node q\<^sub>o, \<uu>, \<v>, \<w>]
         ]
     }"

definition ana_entry_node :: "(RD_pred, RD_var, ('n,'v) RD_elem) clause set" where
  "ana_entry_node = 
     {
       RD1\<langle>[Encode_Node Start, \<uu>, DLElement Questionmark, Encode_Node End]\<rangle> <-
         [
           VAR[\<uu>]
         ]
     }"


definition ana_pg :: "('n, 'v) program_graph \<Rightarrow> (RD_pred, RD_var, ('n,'v) RD_elem) clause set" where
  "ana_pg pg = \<Union>(ana_edge ` pg) \<union> ana_entry_node"

(* Jeg skal på en eller anden måde trylle datalog programmet om til en analysis assignment.
   Eller definere hvad det betyder for programmet at det er en analysis assignment.
   Eller definere hvad det betyder at \<rho> er en analysis assignment.
 *)

type_synonym ('n,'v) quadruple = "'n node *'v * 'n node option * 'n node"

abbreviation solves_query_RD :: "('p,'e) pred_val \<Rightarrow> ('p, RD_var,'e) query \<Rightarrow> bool" where
  "solves_query_RD == solves_query"

definition summarizes_dl :: "(RD_pred,('n,'v) RD_elem) pred_val \<Rightarrow> ('n,'v) program_graph \<Rightarrow> bool" where
  "summarizes_dl \<rho> pg \<longleftrightarrow> (\<forall>\<pi> x q1 q2. \<pi> \<in> LTS.path_with_word pg \<longrightarrow> get_start \<pi> = Start \<longrightarrow> (x,q1,q2) \<in> def_path \<pi> \<longrightarrow> 
     solves_query_RD \<rho> (the_RD1,[Encode_Node (get_end \<pi>), Encode_Var x, Encode_Node_Q q1, Encode_Node q2]))"
(* The warning is because summarizes_dl does not fix the type of datalog variables...
   It can be done by adding a type annotation to solves_query.
 *)

lemma RD_sound': (* TODO: We also need \<rho> to make VAR(x) true for the variables in the pg. *)
  assumes "solves_program \<rho> (ana_pg pg)"
  assumes "\<pi> \<in> LTS.path_with_word pg"
  assumes "get_start \<pi> = Start"
  assumes "(x,q1,q2) \<in> def_path \<pi>"
  shows "solves_query_RD \<rho> (the_RD1,[Encode_Node (get_end \<pi>), Encode_Var x, Encode_Node_Q q1, Encode_Node q2])"
  using assms apply (induction \<pi>)
  sorry

lemma RD_sound: (* TODO: We also need \<rho> to make VAR(x) true for the variables in the pg. *)
  assumes "solves_program \<rho> (ana_pg pg)"
  shows "summarizes_dl \<rho> pg"
  using assms RD_sound' unfolding summarizes_dl_def by metis


(* 
TODO:
We need to define least solutions.
We need a lemma that exploits that we are looking at least solutions. 
*)
