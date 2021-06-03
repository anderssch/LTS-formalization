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
(* For program graphs there are some reachability requirements on Start and End, 
   but we ignore them for now. *)

definition get_start :: "('n node list \<times> 'v action list) \<Rightarrow> 'n node" where
  "get_start \<pi> = hd (fst \<pi>)"
(* TODO: Make a better path representation. *)

definition get_end :: "('n node list \<times> 'v action list) \<Rightarrow> 'n node" where
  "get_end \<pi> = last (fst \<pi>)"

term "LTS.path_with_word :: ('n,'v) program_graph \<Rightarrow> ('n node list \<times> 'v action list) set"


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

definition triple_of :: "'v \<Rightarrow> ('n,'v) edge \<Rightarrow> ('n,'v) triple" where
  "triple_of == (\<lambda>x (q1, a, q2). (x, Some q1, q2))"

definition def_var :: "('n,'v) edge list \<Rightarrow> 'v \<Rightarrow> ('n,'v) triple" where
  "def_var \<pi> x = (if (filter (\<lambda>e. x \<in> def_edge e) \<pi>) = []
                    then (x, None, Start)
                    else (triple_of x (last (filter (\<lambda>e. x \<in> def_edge e) \<pi>))))"

definition def_path :: "('n node list \<times> 'v action list) \<Rightarrow> ('n,'v) triple set" where
  "def_path \<pi> = (def_var (LTS.transition_list \<pi>) ` UNIV)"
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

type_synonym ('p,'x,'e) lefthand = "'p * ('x,'e) identifier list"

fun eval_id :: "('x,'e) var_val \<Rightarrow> ('x,'e) identifier \<Rightarrow> 'e" where
  "eval_id \<sigma> (DLVar x) = \<sigma> x"
| "eval_id \<sigma> (DLElement e) = e"

fun meaning_rh :: "('p,'x,'e) righthand \<Rightarrow> ('p,'e) pred_val \<Rightarrow> ('x,'e) var_val \<Rightarrow> bool" where
  "meaning_rh (a \<^bold>= a') \<rho> \<sigma> \<longleftrightarrow> eval_id \<sigma> a = eval_id  \<sigma> a'"
| "meaning_rh (a \<^bold>\<noteq> a') \<rho> \<sigma> \<longleftrightarrow> eval_id \<sigma> a \<noteq> eval_id \<sigma> a'"
| "meaning_rh (PosRh p ids) \<rho> \<sigma> \<longleftrightarrow> map (eval_id \<sigma>) ids \<in> \<rho> p"
| "meaning_rh (NegRh p ids) \<rho> \<sigma> \<longleftrightarrow> \<not> map (eval_id \<sigma>) ids \<in> \<rho> p"

fun meaning_lh :: "('p,'x,'e) lefthand \<Rightarrow> ('p,'e) pred_val \<Rightarrow> ('x,'e) var_val \<Rightarrow> bool" where
  "meaning_lh (p,ids) \<rho> \<sigma> \<longleftrightarrow> map (eval_id \<sigma>) ids \<in> \<rho> p"

fun meaning_cls :: "('p,'x,'e) clause \<Rightarrow> ('p,'e) pred_val \<Rightarrow> ('x,'e) var_val \<Rightarrow> bool" where
  "meaning_cls (Cls p ids rhs) \<rho> \<sigma> \<longleftrightarrow> ((\<forall>rh\<in>set rhs. meaning_rh rh \<rho> \<sigma>) \<longrightarrow> meaning_lh (p,ids) \<rho> \<sigma>)"

definition solves_cls :: "('p,'e) pred_val \<Rightarrow> ('p,'x,'e) clause \<Rightarrow> bool" where
  "solves_cls \<rho> c \<longleftrightarrow> (\<forall>\<sigma>. meaning_cls c \<rho> \<sigma>)"

definition solves_program :: "('p,'e) pred_val \<Rightarrow> ('p,'x,'e) dl_program \<Rightarrow> bool" where
  "solves_program \<rho> dl \<longleftrightarrow> (\<forall>c \<in> dl. solves_cls \<rho> c)"


section \<open>Queries (not in the book?)\<close>

type_synonym ('p,'x,'e) query = "'p * ('x,'e) identifier list"

fun meaning_query :: "('p,'x,'e) query \<Rightarrow> ('p,'e) pred_val \<Rightarrow> ('x,'e) var_val \<Rightarrow> bool" where
  "meaning_query (p,ids) \<rho> \<sigma> \<longleftrightarrow> map (eval_id \<sigma>) ids \<in> \<rho> p"

definition solves_query :: "('p,'e) pred_val \<Rightarrow> ('p,'x,'e) query \<Rightarrow> bool" where
  "solves_query \<rho> = (\<lambda>(p,ids). (\<forall>\<sigma>. meaning_query (p,ids) \<rho> \<sigma>))" (* Is this correct?!?!?!?! *)


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

abbreviation Encode_Node :: "'n node \<Rightarrow> (RD_var, ('n, 'v) RD_elem) identifier" where (* 'x could also be RD_var... *)
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

abbreviation \<uu> :: "(RD_var, 'a) identifier" where
  "\<uu> == DLVar the_\<uu>"

abbreviation \<v> :: "(RD_var, 'a) identifier" where
  "\<v> == DLVar the_\<v>"

abbreviation \<w> :: "(RD_var, 'a) identifier" where
   "\<w> == DLVar the_\<w>"

fun ana_edge :: "('n, 'v) edge \<Rightarrow> (RD_pred, RD_var, ('n,'v) RD_elem) clause set" where
  "ana_edge (q\<^sub>o, x ::= a, q\<^sub>s) =
     {
        RD1\<langle>[Encode_Node q\<^sub>s, \<uu>, \<v>, \<w>]\<rangle> :-
          [
            RD1[Encode_Node q\<^sub>o, \<uu>, \<v>, \<w>],
            \<uu> \<^bold>\<noteq> (Encode_Var x)
          ].
        ,
        RD1\<langle>[Encode_Node q\<^sub>s, Encode_Var x, Encode_Node q\<^sub>o, Encode_Node q\<^sub>s]\<rangle> :- [].
     }"
| "ana_edge (q\<^sub>o, Bool b, q\<^sub>s) =
     {
       RD1\<langle>[Encode_Node q\<^sub>s, \<uu>, \<v>, \<w>]\<rangle> :-
         [
           RD1[Encode_Node q\<^sub>o, \<uu>, \<v>, \<w>]
         ].
     }"
| "ana_edge (q\<^sub>o, Skip, q\<^sub>s) =
     {
       RD1\<langle>[Encode_Node q\<^sub>s, \<uu>, \<v>, \<w>]\<rangle> :-
         [
           RD1[Encode_Node q\<^sub>o, \<uu>, \<v>, \<w>]
         ].
     }"

definition ana_entry_node :: "(RD_pred, RD_var, ('n,'v) RD_elem) clause set" where
  "ana_entry_node = 
     {
       RD1\<langle>[Encode_Node Start, \<uu>, DLElement Questionmark, Encode_Node Start]\<rangle> :-
         [
           VAR[\<uu>]
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

abbreviation solves_query_RD :: "('p,'e) pred_val \<Rightarrow> ('p, RD_var,'e) query \<Rightarrow> bool" where
  "solves_query_RD == solves_query"

definition summarizes_dl :: "(RD_pred,('n,'v) RD_elem) pred_val \<Rightarrow> ('n,'v) program_graph \<Rightarrow> bool" where
  "summarizes_dl \<rho> pg \<longleftrightarrow> (\<forall>\<pi> x q1 q2. \<pi> \<in> LTS.path_with_word pg \<longrightarrow> get_start \<pi> = Start \<longrightarrow> (x,q1,q2) \<in> def_path \<pi> \<longrightarrow> 
     solves_query_RD \<rho> (the_RD1,[Encode_Node (get_end \<pi>), Encode_Var x, Encode_Node_Q q1, Encode_Node q2]))"
(* The warning is because summarizes_dl does not fix the type of datalog variables...
   It can be done by adding a type annotation to solves_query.
 *)

thm LTS.path_with_word.induct

lemma def_var_x: "fst (def_var ts x) = x"
  unfolding def_var_def
  apply auto
  by (simp add: case_prod_beta triple_of_def)

lemma transition_list_reversed_simp:
  assumes "length ss = length w"
  shows "transition_list (ss @ [s, s'], w @ [l]) = (transition_list (ss@[s],w)) @ [(s,l,s')]"
  using assms
proof (induction ss arbitrary: w)
  case Nil
  then show ?case
    by auto 
next
  case (Cons a ss)
  define w' where "w' = tl w"
  define l' where "l' = hd w"
  have w_split: "l' # w' = w"
    by (metis Cons.prems l'_def length_0_conv list.distinct(1) list.exhaust_sel w'_def)
  then have "length ss = length w'"
    using Cons.prems by force
  then have "transition_list (ss @ [s, s'], w' @ [l]) = transition_list (ss @ [s], w') @ [(s, l, s')]"
    using  Cons(1)[of w'] by auto
  then have "transition_list (a # ss @ [s, s'], l' # w' @ [l]) = transition_list (a # ss @ [s], l' # w') @ [(s, l, s')]"
    by (cases ss) auto 
  then show ?case
    using w_split by auto
qed

lemma last_def_transition:
  assumes "length ss = length w"
  assumes "x \<in> def_action l"
  assumes "(x, q1, q2) \<in> def_path (ss @ [s, s'], w @ [l])"
  shows "Some s = q1 \<and> s' = q2"
  using assms
  apply auto
  subgoal
    unfolding def_path_def
    apply (simp add: transition_list_reversed_simp[of ss w, OF assms(1)])
    apply auto
    subgoal for xa
      apply (cases "xa=x")
      subgoal
        apply auto
        unfolding def_var_def
        apply auto
        unfolding triple_of_def
        apply auto
        done
      subgoal
        apply (metis def_var_x fst_conv)
        done
      done
    done
  subgoal
    unfolding def_path_def
    apply (simp add: transition_list_reversed_simp[of ss w, OF assms(1)])
    apply auto
    subgoal for xa
      apply (cases "xa=x")
      subgoal
        apply auto
        unfolding def_var_def
        apply auto
        unfolding triple_of_def
        apply auto
        done
      subgoal
        apply (metis def_var_x fst_conv)
        done
      done
    done
  done
 
lemma not_last_def_transition:
  assumes "length ss = length w"
  assumes "x \<notin> def_action l"
  assumes "(x, q1, q2) \<in> def_path (ss @ [s, s'], w @ [l])"
  shows "(x, q1, q2) \<in> def_path (ss @ [s], w)"
  using assms
  unfolding def_path_def
  apply (simp add: transition_list_reversed_simp[of ss w, OF assms(1)])
  apply auto
  subgoal for xa
    apply (cases "xa=x")
    subgoal
      apply auto
      unfolding def_var_def
      apply auto
      done
    subgoal
      apply (metis def_var_x fst_conv)
      done
    done
  done


lemma a_simple_inference:
  assumes "solves_cls \<rho> (Cls p args [])"
  shows "solves_query_RD \<rho> (p, args)"
  using assms unfolding solves_query_def solves_cls_def by auto

lemma (* TODO: I think there is a better approach than this. *)
  assumes "solves_cls \<rho> RD1\<langle>[Encode_Node s', \<uu>, \<v>, \<w>]\<rangle> :- [RD1 [Encode_Node s, \<uu>, \<v>, \<w>], \<uu> \<^bold>\<noteq> Encode_Var y] ."
  assumes "x \<noteq> y"
  assumes "solves_query_RD \<rho> RD1\<langle>[Encode_Node s, Encode_Var x, Encode_Node_Q q1, Encode_Node q2]\<rangle>."
  shows "solves_query_RD \<rho> RD1\<langle>[Encode_Node s', Encode_Var x, Encode_Node_Q q1, Encode_Node q2]\<rangle>."
proof -
  {
    fix \<sigma> :: "RD_var \<Rightarrow> ('a, 'b) RD_elem"
    assume a1: "\<sigma> the_\<uu> = RD_Var x"
    assume a2: "\<sigma> the_\<w> = RD_Node q2"
    assume a3: "(q1 = None \<longrightarrow> \<sigma> the_\<uu> = Questionmark) \<and> ((\<exists>q1'. q1 = Some q1') \<longrightarrow> \<sigma> the_\<uu> = (RD_Node (the q1)))"
    have "meaning_rh (RD1 [Encode_Node s, \<uu>, \<v>, \<w>]) \<rho> \<sigma>"
      sorry
    moreover
    have "meaning_rh (\<uu> \<^bold>\<noteq> Encode_Var y) \<rho> \<sigma>"
      sorry
    ultimately
    have "meaning_lh (the_RD1, [Encode_Node s', \<uu>, \<v>, \<w>]) \<rho> \<sigma>"
      using assms(1)
      unfolding solves_cls_def by auto
    then have "meaning_lh (the_RD1,[Encode_Node s', Encode_Var x, Encode_Node_Q q1, Encode_Node q2]) \<rho> \<sigma>"
      apply auto
      using a1 a2 a3 by auto 
  }
   
 show ?thesis
   unfolding solves_query_def sorry
qed
    

(* Ville det ikke være bedre hvis paths var lister af transitions?????????? *)
(* Det er nok godt med et bevis på papir først :-D *)
lemma RD_sound': 
  assumes "(ss,w) \<in> LTS.path_with_word pg"
  assumes "(solves_program :: (RD_pred,('n, 'v) RD_elem) pred_val \<Rightarrow> (RD_pred,RD_var,('n, 'v) RD_elem) dl_program \<Rightarrow> bool) \<rho> (var_contraints \<union> ana_pg pg)"
  assumes "get_start (ss,w) = Start"
  assumes "(x,q1,q2) \<in> def_path (ss,w)"
  shows "solves_query_RD \<rho> (the_RD1,[Encode_Node (get_end (ss,w)), Encode_Var x, Encode_Node_Q q1, Encode_Node q2])"
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

  have "RD1\<langle>[Encode_Node Start, \<uu>, DLElement Questionmark, Encode_Node Start]\<rangle> :-
         [
           VAR[\<uu>]
         ]. \<in> ana_pg pg"
    unfolding ana_pg_def ana_entry_node_def by auto
  then have "(solves_cls \<rho> (RD1\<langle>[Encode_Node Start, \<uu>, DLElement Questionmark, Encode_Node Start]\<rangle> :-
         [
           VAR[\<uu>]
         ].))"
    using assms(2) unfolding solves_program_def by auto 
   then have "\<forall>y. meaning_cls (RD1\<langle>[Encode_Node Start, \<uu>, DLElement Questionmark, Encode_Node Start]\<rangle> :-
         [
           VAR[\<uu>]
         ].) \<rho> y"
     unfolding solves_cls_def by metis
   then have "meaning_cls (RD1\<langle>[Encode_Node Start, \<uu>, DLElement Questionmark, Encode_Node Start]\<rangle> :-
         [
           VAR[\<uu>]
         ].) \<rho> (\<lambda>v. RD_Var x)"
     by presburger
   then have "[RD_Var x] \<in> \<rho> the_VAR \<longrightarrow> [RD_Node Start, RD_Var x, Questionmark, RD_Node Start] \<in> \<rho> the_RD1"
     by simp
   then have "[RD_Node Start, RD_Var x, Questionmark, RD_Node Start] \<in> \<rho> the_RD1"
     using x_sat by auto

   from this 1 show ?case
     unfolding solves_query_def
    apply auto
    unfolding solves_cls_def
    unfolding get_end_def
    unfolding def_path_def
    apply auto
    unfolding def_var_def
    apply auto
    unfolding get_start_def
    apply auto
    done
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
      using a_simple_inference by force
    then show ?thesis
      by (simp add: get_end_def sq)
  next
    case False
    then have x_is_def: "(x, q1, q2) \<in> def_path (ss @ [s], w)" using 2(7)
      using not_last_def_transition len by force
    then have "solves_query_RD \<rho> (RD1\<langle>[Encode_Node (get_end (ss @ [s], w)), Encode_Var x, Encode_Node_Q q1, Encode_Node q2]\<rangle>.)"
    proof -
      have "(ss @ [s], w) \<in> LTS.path_with_word pg"
        using 2(1) by auto
      moreover
      have "solves_program \<rho> (var_contraints \<union> ana_pg pg)"
        using 2(5) by auto
      moreover
      have "get_start (ss @ [s], w) = Start"
        using 2(6)
        by (metis append_self_conv2 fst_conv get_start_def hd_append2 list.sel(1)) 
      moreover
      have "(x, q1, q2) \<in> def_path (ss @ [s], w)"
        using x_is_def by auto
      ultimately
      show "solves_query_RD \<rho> (the_RD1, [Encode_Node (get_end (ss @ [s], w)), Encode_Var x, Encode_Node_Q q1, Encode_Node q2])"
        using 2(3) by auto
    qed
    then have ind: "solves_query_RD \<rho> (RD1\<langle>[Encode_Node s, Encode_Var x, Encode_Node_Q q1, Encode_Node q2]\<rangle>.)"
      by (simp add: get_end_def)
    show ?thesis
    proof (cases l)
      case (Asg y e)
      have xy: "x \<noteq> y"
        using False Asg by auto
      have "(s, y ::= e, s') \<in> pg"
        using "2.hyps"(2) Asg by auto
      then have "RD1\<langle>[Encode_Node s', \<uu>, \<v>, \<w>]\<rangle> :-
          [
            RD1[Encode_Node s, \<uu>, \<v>, \<w>],
            \<uu> \<^bold>\<noteq> (Encode_Var y)
          ]. \<in> ana_pg pg"
        unfolding ana_pg_def by force
      from this False have "solves_cls \<rho> (RD1\<langle>[Encode_Node s', \<uu>, \<v>, \<w>]\<rangle> :-
          [
            RD1[Encode_Node s, \<uu>, \<v>, \<w>],
            \<uu> \<^bold>\<noteq> (Encode_Var y)
          ].)"
        by (meson "2.prems"(2) UnCI solves_program_def)
      from this xy ind have "solves_query_RD \<rho> (RD1\<langle>[Encode_Node s', Encode_Var x, Encode_Node_Q q1, Encode_Node q2]\<rangle>.)"
        sorry
      then show ?thesis
        by (simp add: get_end_def)
    next
      case (Bool b)
      have "(s, Bool b, s') \<in> pg"
        using "2.hyps"(2) Bool by auto
      then have "RD1\<langle>[Encode_Node s', \<uu>, \<v>, \<w>]\<rangle> :-
         [
           RD1[Encode_Node s, \<uu>, \<v>, \<w>]
         ]. \<in> ana_pg pg"
        unfolding ana_pg_def by force
      then have "solves_cls \<rho> (RD1\<langle>[Encode_Node s', \<uu>, \<v>, \<w>]\<rangle> :- [RD1[Encode_Node s, \<uu>, \<v>, \<w>]].)"
        by (meson "2.prems"(2) UnCI solves_program_def)
      then have "solves_query_RD \<rho> (the_RD1, [Encode_Node s', Encode_Var x, Encode_Node_Q q1, Encode_Node q2])"
        using ind sorry
      then show ?thesis
        by (simp add: get_end_def)
    next
      case Skip
      have "(s, Skip, s') \<in> pg"
        using "2.hyps"(2) Skip by auto
      then have "RD1\<langle>[Encode_Node s', \<uu>, \<v>, \<w>]\<rangle> :-
         [
           RD1[Encode_Node s, \<uu>, \<v>, \<w>]
         ]. \<in> ana_pg pg"
        unfolding ana_pg_def by force
      then have "solves_cls \<rho> (RD1\<langle>[Encode_Node s', \<uu>, \<v>, \<w>]\<rangle> :- [RD1 [Encode_Node s, \<uu>, \<v>, \<w>]] .)"
        by (meson "2.prems"(2) UnCI solves_program_def)
      then have "solves_query_RD \<rho> (the_RD1, [Encode_Node s', Encode_Var x, Encode_Node_Q q1, Encode_Node q2])"
        using ind sorry
      then show ?thesis
        by (simp add: get_end_def)
    qed
  qed
qed

lemma RD_sound:
  assumes "solves_program \<rho> (var_contraints \<union> ana_pg pg)"
  shows "summarizes_dl \<rho> pg"
  using assms RD_sound' unfolding summarizes_dl_def by fastforce 


(* 
TODO:
We need to define least solutions.
We need a lemma that exploits that we are looking at least solutions. 
*)
