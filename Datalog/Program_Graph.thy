theory Program_Graph imports "../PDS/LTS" begin


section \<open>Actions\<close>

datatype (fv_arith: 'v) arith =
  Integer int
  | Arith_Var 'v
  | Arith_Op "'v arith" "int \<Rightarrow> int \<Rightarrow> int" "'v arith"
  | Minus "'v arith"
(* Typical notation: a *)

datatype (fv_boolean: 'v) boolean =
  true
  | false
  | Rel_Op "'v arith" "int \<Rightarrow> int \<Rightarrow> bool" "'v arith"
  | Bool_Op "'v boolean" "bool \<Rightarrow> bool \<Rightarrow> bool" "'v boolean"
  | Neg "'v boolean"
(* Typical notation: b *)

datatype 'v action =
  Asg 'v "'v arith" ("_ ::= _" [1000, 61] 61)
  | Bool "'v boolean"
  | Skip
(* Typical notation: \<alpha> *)


section \<open>Memories\<close>

type_synonym 'v memory = "'v \<Rightarrow> int"
(* Typical notation: \<sigma> *)


section \<open>Semantics\<close>

fun sem_arith :: "'v arith \<Rightarrow> 'v memory \<Rightarrow> int" where
  "sem_arith (Integer n) \<sigma> = n"
| "sem_arith (Arith_Var x) \<sigma> = \<sigma> x"
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

type_synonym ('n,'v) edge = "'n \<times> 'v action \<times> 'n"

type_synonym ('n,'v) program_graph = "(('n,'v) edge set \<times> 'n \<times> 'n)"

term "LTS.path_with_word :: ('n,'v) edge set \<Rightarrow> ('n list \<times> 'v action list) set"

section \<open>Execution Sequences\<close>

type_synonym ('n,'v) config = "'n * 'v memory"

fun initial_config_of :: "('n,'v) config \<Rightarrow> ('n,'v) program_graph \<Rightarrow> bool" where
  "initial_config_of (q,\<sigma>) (es,start,end) \<longleftrightarrow> q = start"

fun final_config_of :: "('n,'v) config \<Rightarrow> ('n,'v) program_graph \<Rightarrow> bool" where
  "final_config_of (q,\<sigma>) (es,start,end) \<longleftrightarrow> q = end"

inductive exe_step :: "('n,'v) program_graph \<Rightarrow> ('n,'v) config \<Rightarrow> 'v action \<Rightarrow> ('n,'v) config \<Rightarrow> bool" where
  "(q1, \<alpha>, q2) \<in> es \<Longrightarrow> sem_action \<alpha> \<sigma> = Some \<sigma>' \<Longrightarrow> exe_step (es,start,end) (q1,\<sigma>) \<alpha> (q2,\<sigma>')"


section \<open>Reaching Definitions\<close>

type_synonym ('n,'v) triple = "'v * 'n option * 'n"

type_synonym ('n,'v) analysis_assignment = "'n \<Rightarrow> ('n,'v) triple set"


subsection \<open>What is defined on a path\<close>

fun def_action :: "'v action \<Rightarrow> 'v set" where
  "def_action (x ::= a) = {x}"
| "def_action (Bool b) = {}"
| "def_action Skip = {}"

abbreviation def_edge :: "('n,'v) edge \<Rightarrow> 'v set" where
  "def_edge == \<lambda>(q1, \<alpha>, q2). def_action \<alpha>"

definition triple_of :: "'v \<Rightarrow> ('n,'v) edge \<Rightarrow> ('n,'v) triple" where
  "triple_of == (\<lambda>x (q1, \<alpha>, q2). (x, Some q1, q2))"

definition def_var :: "('n,'v) edge list \<Rightarrow> 'v \<Rightarrow> 'n \<Rightarrow> ('n,'v) triple" where
  "def_var \<pi> x start = (if (\<exists>e \<in> set \<pi>. x \<in> def_edge e)
                        then (triple_of x (last (filter (\<lambda>e. x \<in> def_edge e) \<pi>)))
                        else (x, None, start))"

definition def_path :: "('n list \<times> 'v action list) \<Rightarrow> 'n \<Rightarrow> ('n,'v) triple set" where
  "def_path \<pi> start = ((\<lambda>x. def_var (LTS.transition_list \<pi>) x start) ` UNIV)"

(*
fun summarizes_RD :: "('n,'v) analysis_assignment \<Rightarrow> ('n,'v) program_graph \<Rightarrow> bool" where
  "summarizes_RD RD (es,start,end) \<longleftrightarrow> (\<forall>\<pi>. \<pi> \<in> LTS.path_with_word es \<longrightarrow> LTS.get_start \<pi> = start \<longrightarrow> def_path \<pi> start \<subseteq> RD (LTS.get_end \<pi>))"
*)


section \<open>Datalog programs and their solutions\<close>

datatype (vars_id: 'x,'e) identifier = is_Var: Var 'x | is_Cst: Cst (the_Cst: 'e)

datatype (preds_rh: 'p,'x,'e) righthand = 
  Eql "('x,'e) identifier" "('x,'e) identifier" ("_ \<^bold>= _" [61, 61] 61)
  | Neql "('x,'e) identifier" "('x,'e) identifier" ("_ \<^bold>\<noteq> _" [61, 61] 61)
  | PosRh 'p "('x,'e) identifier list"
  | NegRh 'p "('x,'e) identifier list" ("\<^bold>\<not> _ _" [61, 61] 61)

datatype (preds_cls: 'p, 'x,'e) clause = Cls 'p "('x,'e) identifier list" (the_rhs: "('p,'x,'e) righthand list") (* Why not righthand set? *)

fun the_lh where
  "the_lh (Cls p ids rhs) = (p,ids)"

type_synonym ('p,'x,'e) dl_program = "('p,'x,'e) clause set"

definition "preds_dl dl = \<Union>{preds_cls c| c. c \<in> dl}"

lemma preds_dl_union[simp]: "preds_dl (dl1 \<union> dl2) = preds_dl dl1 \<union> preds_dl dl2"
  unfolding preds_dl_def by auto

type_synonym ('x,'e) var_val = "'x \<Rightarrow> 'e"

type_synonym ('p,'e) pred_val = "'p \<Rightarrow> 'e list set"

type_synonym ('p,'x,'e) lefthand = "'p * ('x,'e) identifier list"

fun preds_lh :: "('p,'x,'e) lefthand \<Rightarrow> 'p set" where 
  "preds_lh (p,ids) = {p}"

fun the_lhs :: "('p, 'x,'e) clause \<Rightarrow> ('p,'x,'e) lefthand" where
  "the_lhs (Cls p ids rhs) = (p,ids)"

fun eval_id :: "('x,'e) identifier \<Rightarrow> ('x,'e) var_val \<Rightarrow> 'e" ("\<lbrakk>_\<rbrakk>\<^sub>i\<^sub>d") where
  "\<lbrakk>Var x\<rbrakk>\<^sub>i\<^sub>d \<sigma> = \<sigma> x"
| "\<lbrakk>Cst e\<rbrakk>\<^sub>i\<^sub>d \<sigma> = e"

fun eval_ids :: "('x,'e) identifier list \<Rightarrow> ('x,'e) var_val \<Rightarrow> 'e list" ("\<lbrakk>_\<rbrakk>\<^sub>i\<^sub>d\<^sub>s") where
  "\<lbrakk>ids\<rbrakk>\<^sub>i\<^sub>d\<^sub>s \<sigma> = map (\<lambda>a. \<lbrakk>a\<rbrakk>\<^sub>i\<^sub>d \<sigma>) ids"

fun meaning_rh :: "('p,'x,'e) righthand \<Rightarrow> ('p,'e) pred_val \<Rightarrow> ('x,'e) var_val \<Rightarrow> bool" ("\<lbrakk>_\<rbrakk>\<^sub>r\<^sub>h") where
  "\<lbrakk>a \<^bold>= a'\<rbrakk>\<^sub>r\<^sub>h \<rho> \<sigma> \<longleftrightarrow> \<lbrakk>a\<rbrakk>\<^sub>i\<^sub>d \<sigma> = \<lbrakk>a'\<rbrakk>\<^sub>i\<^sub>d \<sigma>"
| "\<lbrakk>a \<^bold>\<noteq> a'\<rbrakk>\<^sub>r\<^sub>h \<rho> \<sigma> \<longleftrightarrow> \<lbrakk>a\<rbrakk>\<^sub>i\<^sub>d \<sigma>  \<noteq> \<lbrakk>a'\<rbrakk>\<^sub>i\<^sub>d \<sigma>"
| "\<lbrakk>PosRh p ids\<rbrakk>\<^sub>r\<^sub>h \<rho> \<sigma> \<longleftrightarrow> \<lbrakk>ids\<rbrakk>\<^sub>i\<^sub>d\<^sub>s \<sigma> \<in> \<rho> p"
| "\<lbrakk>\<^bold>\<not> p ids\<rbrakk>\<^sub>r\<^sub>h \<rho> \<sigma> \<longleftrightarrow> \<not> \<lbrakk>ids\<rbrakk>\<^sub>i\<^sub>d\<^sub>s \<sigma> \<in> \<rho> p"

fun meaning_rhs :: "('p,'x,'e) righthand list \<Rightarrow> ('p,'e) pred_val \<Rightarrow> ('x,'e) var_val \<Rightarrow> bool" ("\<lbrakk>_\<rbrakk>\<^sub>r\<^sub>h\<^sub>s") where
  "\<lbrakk>rhs\<rbrakk>\<^sub>r\<^sub>h\<^sub>s \<rho> \<sigma> \<longleftrightarrow> (\<forall>rh \<in> set rhs. \<lbrakk>rh\<rbrakk>\<^sub>r\<^sub>h \<rho> \<sigma>)"

fun meaning_lh :: "('p,'x,'e) lefthand \<Rightarrow> ('p,'e) pred_val \<Rightarrow> ('x,'e) var_val \<Rightarrow> bool" ("\<lbrakk>_\<rbrakk>\<^sub>l\<^sub>h") where
  "\<lbrakk>(p,ids)\<rbrakk>\<^sub>l\<^sub>h \<rho> \<sigma> \<longleftrightarrow> \<lbrakk>ids\<rbrakk>\<^sub>i\<^sub>d\<^sub>s \<sigma> \<in> \<rho> p"

fun meaning_cls :: "('p,'x,'e) clause \<Rightarrow> ('p,'e) pred_val \<Rightarrow> ('x,'e) var_val \<Rightarrow> bool" ("\<lbrakk>_\<rbrakk>\<^sub>c\<^sub>l\<^sub>s") where
  "\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho> \<sigma> \<longleftrightarrow> (\<lbrakk>rhs\<rbrakk>\<^sub>r\<^sub>h\<^sub>s \<rho> \<sigma> \<longrightarrow> \<lbrakk>(p,ids)\<rbrakk>\<^sub>l\<^sub>h \<rho> \<sigma>)" (* use meaning_rhs *)

fun solves_rh :: "('p,'e) pred_val \<Rightarrow> ('p,'x,'e) righthand \<Rightarrow> bool" (infix "\<Turnstile>\<^sub>r\<^sub>h" 91) where (* Not in the book *)
  "\<rho> \<Turnstile>\<^sub>r\<^sub>h rh \<longleftrightarrow> (\<forall>\<sigma>. \<lbrakk>rh\<rbrakk>\<^sub>r\<^sub>h \<rho> \<sigma>)"

definition solves_cls :: "('p,'e) pred_val \<Rightarrow> ('p,'x,'e) clause \<Rightarrow> bool" (infix "\<Turnstile>\<^sub>c\<^sub>l\<^sub>s" 91) where
  "\<rho> \<Turnstile>\<^sub>c\<^sub>l\<^sub>s c \<longleftrightarrow> (\<forall>\<sigma>. \<lbrakk>c\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho> \<sigma>)"

definition solves_program :: "('p,'e) pred_val \<Rightarrow> ('p,'x,'e) dl_program \<Rightarrow> bool" (infix "\<Turnstile>\<^sub>d\<^sub>l" 91) where
  "\<rho> \<Turnstile>\<^sub>d\<^sub>l dl \<longleftrightarrow> (\<forall>c \<in> dl. \<rho> \<Turnstile>\<^sub>c\<^sub>l\<^sub>s c)"


section \<open>Facts (not in the book?)\<close> (* TODO: get rid of these*)

type_synonym ('p,'x,'e) fact = "'p * ('x,'e) identifier list" (* The fact type is the same as the lh type... *)

fun meaning_fact :: "('p,'x,'e) fact \<Rightarrow> ('p,'e) pred_val \<Rightarrow> ('x,'e) var_val \<Rightarrow> bool" ("\<lbrakk>_\<rbrakk>\<^sub>f") where
  "\<lbrakk>(p,ids)\<rbrakk>\<^sub>f \<rho> \<sigma> \<longleftrightarrow> \<lbrakk>ids\<rbrakk>\<^sub>i\<^sub>d\<^sub>s \<sigma> \<in> \<rho> p"

fun solves_fact :: "('p,'e) pred_val \<Rightarrow> ('p,'x,'e) fact \<Rightarrow> bool" (infix "\<Turnstile>\<^sub>f" 91) where
  "\<rho> \<Turnstile>\<^sub>f (p,ids) \<longleftrightarrow> (\<forall>\<sigma>. \<lbrakk>(p,ids)\<rbrakk>\<^sub>f \<rho> \<sigma>)"

section \<open>Substitutions (not in the book?)\<close>

type_synonym ('x,'e) subst = "'x \<Rightarrow> ('x,'e) identifier"

fun subst_id :: "('x,'e) identifier \<Rightarrow> ('x,'e) subst \<Rightarrow> ('x,'e) identifier" (infix "\<cdot>\<^sub>i\<^sub>d" 70) where
  "(Var x) \<cdot>\<^sub>i\<^sub>d \<eta>  = \<eta> x"
| "(Cst e) \<cdot>\<^sub>i\<^sub>d \<eta> = (Cst e)"

fun subst_ids :: "('x,'e) identifier list \<Rightarrow> ('x,'e) subst \<Rightarrow> ('x,'e) identifier list" (infix "\<cdot>\<^sub>i\<^sub>d\<^sub>s" 50) where
  "ids \<cdot>\<^sub>i\<^sub>d\<^sub>s \<eta> = map (\<lambda>a. a \<cdot>\<^sub>i\<^sub>d \<eta>) ids"

fun subst_rh :: "('p,'x,'e) righthand \<Rightarrow> ('x,'e) subst \<Rightarrow> ('p,'x,'e) righthand" (infix "\<cdot>\<^sub>r\<^sub>h" 50) where
  "(a \<^bold>= a') \<cdot>\<^sub>r\<^sub>h \<eta> = (a \<cdot>\<^sub>i\<^sub>d \<eta> \<^bold>= a' \<cdot>\<^sub>i\<^sub>d \<eta>)"
| "(a \<^bold>\<noteq> a') \<cdot>\<^sub>r\<^sub>h \<eta> = (a \<cdot>\<^sub>i\<^sub>d \<eta> \<^bold>\<noteq> a' \<cdot>\<^sub>i\<^sub>d \<eta>)"
| "(PosRh p ids) \<cdot>\<^sub>r\<^sub>h \<eta> = (PosRh p (ids \<cdot>\<^sub>i\<^sub>d\<^sub>s \<eta>))"
| "(\<^bold>\<not> p ids) \<cdot>\<^sub>r\<^sub>h \<eta> = (\<^bold>\<not> p ( ids \<cdot>\<^sub>i\<^sub>d\<^sub>s \<eta>))"

fun subst_rhs :: "('p,'x,'e) righthand list \<Rightarrow> ('x,'e) subst \<Rightarrow> ('p,'x,'e) righthand list" (infix "\<cdot>\<^sub>r\<^sub>h\<^sub>s" 50) where
  "rhs \<cdot>\<^sub>r\<^sub>h\<^sub>s \<eta> = map (\<lambda>a. a \<cdot>\<^sub>r\<^sub>h \<eta>) rhs"

fun subst_lh :: "('p,'x,'e) lefthand \<Rightarrow> ('x,'e) subst \<Rightarrow> ('p,'x,'e) lefthand" (infix "\<cdot>\<^sub>l\<^sub>h" 50) where
  "(p,ids) \<cdot>\<^sub>l\<^sub>h \<eta> = (p, ids \<cdot>\<^sub>i\<^sub>d\<^sub>s \<eta>)"

fun subst_cls :: "('p,'x,'e) clause \<Rightarrow> ('x,'e) subst \<Rightarrow> ('p,'x,'e) clause" (infix "\<cdot>\<^sub>c\<^sub>l\<^sub>s" 50) where
  "(Cls p ids rhs) \<cdot>\<^sub>c\<^sub>l\<^sub>s \<eta>  = Cls p (ids \<cdot>\<^sub>i\<^sub>d\<^sub>s \<eta>) (rhs \<cdot>\<^sub>r\<^sub>h\<^sub>s \<eta>)"

fun subst_fact :: "('p,'x,'e) fact \<Rightarrow> ('x,'e) subst \<Rightarrow> ('p,'x,'e) fact" (infix "\<cdot>\<^sub>q" 50) where
  "(p,ids) \<cdot>\<^sub>q \<eta>  = (p, (ids \<cdot>\<^sub>i\<^sub>d\<^sub>s \<eta>))"

definition compose :: "('x,'e) subst \<Rightarrow> ('x,'e) var_val \<Rightarrow> ('x,'e) var_val" (infix "\<circ>\<^sub>s\<^sub>v" 50) where
  "(\<eta> \<circ>\<^sub>s\<^sub>v \<sigma>) x = \<lbrakk>(\<eta> x)\<rbrakk>\<^sub>i\<^sub>d \<sigma>"

section \<open>Substiting variable valuations (not in the book?)\<close>

fun substv_id :: "('x,'e) identifier \<Rightarrow> ('x,'e) var_val \<Rightarrow> ('x,'e) identifier" (infix "\<cdot>\<^sub>v\<^sub>i\<^sub>d" 70) where
  "(Var x) \<cdot>\<^sub>v\<^sub>i\<^sub>d \<sigma> = Cst (\<sigma> x)"
| "(Cst e) \<cdot>\<^sub>v\<^sub>i\<^sub>d \<sigma> = (Cst e)"

fun substv_ids :: "('x,'e) identifier list \<Rightarrow> ('x,'e) var_val \<Rightarrow> ('x,'e) identifier list" (infix "\<cdot>\<^sub>v\<^sub>i\<^sub>d\<^sub>s" 50) where
  "rhs \<cdot>\<^sub>v\<^sub>i\<^sub>d\<^sub>s \<sigma> = map (\<lambda>a. a \<cdot>\<^sub>v\<^sub>i\<^sub>d \<sigma>) rhs"

fun substv_rh :: "('p,'x,'e) righthand \<Rightarrow> ('x,'e) var_val \<Rightarrow> ('p,'x,'e) righthand" (infix "\<cdot>\<^sub>v\<^sub>r\<^sub>h" 50) where
  "(a \<^bold>= a') \<cdot>\<^sub>v\<^sub>r\<^sub>h \<sigma> = (a \<cdot>\<^sub>v\<^sub>i\<^sub>d \<sigma> \<^bold>= a' \<cdot>\<^sub>v\<^sub>i\<^sub>d \<sigma>)"
| "(a \<^bold>\<noteq> a') \<cdot>\<^sub>v\<^sub>r\<^sub>h \<sigma> = (a \<cdot>\<^sub>v\<^sub>i\<^sub>d \<sigma> \<^bold>\<noteq> a' \<cdot>\<^sub>v\<^sub>i\<^sub>d \<sigma>)"
| "(PosRh p ids) \<cdot>\<^sub>v\<^sub>r\<^sub>h \<sigma> = (PosRh p (ids \<cdot>\<^sub>v\<^sub>i\<^sub>d\<^sub>s \<sigma>))"
| "(\<^bold>\<not> p ids) \<cdot>\<^sub>v\<^sub>r\<^sub>h \<sigma> = (\<^bold>\<not> p (ids \<cdot>\<^sub>v\<^sub>i\<^sub>d\<^sub>s \<sigma>))"

definition substv_rhs :: "('p,'x,'e) righthand list \<Rightarrow> ('x,'e) var_val \<Rightarrow> ('p,'x,'e) righthand list" (infix "\<cdot>\<^sub>v\<^sub>r\<^sub>h\<^sub>s" 50) where
  "rhs \<cdot>\<^sub>v\<^sub>r\<^sub>h\<^sub>s \<sigma> = map (\<lambda>a. a \<cdot>\<^sub>v\<^sub>r\<^sub>h \<sigma>) rhs"

fun substv_lh :: "('p,'x,'e) lefthand \<Rightarrow> ('x,'e) var_val \<Rightarrow> ('p,'x,'e) lefthand" (infix "\<cdot>\<^sub>v\<^sub>l\<^sub>h" 50) where
  "(p,ids) \<cdot>\<^sub>v\<^sub>l\<^sub>h \<sigma> = (p,  ids \<cdot>\<^sub>v\<^sub>i\<^sub>d\<^sub>s \<sigma>)"

fun substv_cls :: "('p,'x,'e) clause \<Rightarrow> ('x,'e) var_val \<Rightarrow> ('p,'x,'e) clause" (infix "\<cdot>\<^sub>v\<^sub>c\<^sub>l\<^sub>s" 50) where
  "(Cls p ids rhs) \<cdot>\<^sub>v\<^sub>c\<^sub>l\<^sub>s \<sigma>  = Cls p (ids \<cdot>\<^sub>v\<^sub>i\<^sub>d\<^sub>s \<sigma>) (rhs \<cdot>\<^sub>v\<^sub>r\<^sub>h\<^sub>s \<sigma>)"

fun substv_fact :: "('p,'x,'e) fact \<Rightarrow> ('x,'e) var_val \<Rightarrow> ('p,'x,'e) fact" (infix "\<cdot>\<^sub>v\<^sub>q" 50) where
  "(p,ids) \<cdot>\<^sub>v\<^sub>q \<sigma>  = (p,  ids \<cdot>\<^sub>v\<^sub>i\<^sub>d\<^sub>s \<sigma>)"


section \<open>Datalog lemmas\<close>

subsection \<open>Solve facts\<close>

lemma solves_fact_iff_solves_lh: "\<rho> \<Turnstile>\<^sub>c\<^sub>l\<^sub>s Cls p ids [] \<longleftrightarrow> \<rho> \<Turnstile>\<^sub>r\<^sub>h PosRh p ids"
  using solves_cls_def by force

lemma solves_fact_fact:
  assumes "\<rho> \<Turnstile>\<^sub>c\<^sub>l\<^sub>s Cls p args []"
  shows "\<rho> \<Turnstile>\<^sub>f (p, args)"
  using assms unfolding solves_cls_def by auto

lemmas solve_facts = solves_fact_iff_solves_lh solves_fact_fact

subsection \<open>Resolution\<close>

subsubsection \<open>Of last right hand\<close>

lemma resolution_last_from_cls_rh_to_cls:
  assumes "\<rho> \<Turnstile>\<^sub>c\<^sub>l\<^sub>s Cls p args (rhs @ [rh])"
  assumes "\<rho> \<Turnstile>\<^sub>r\<^sub>h rh"
  shows "\<rho> \<Turnstile>\<^sub>c\<^sub>l\<^sub>s Cls p args rhs"
  using assms unfolding solves_cls_def by auto

lemma resolution_last_from_cls_fact_to_cls:
  assumes "\<rho> \<Turnstile>\<^sub>c\<^sub>l\<^sub>s Cls p args (rhs @ [PosRh p ids])"
  assumes "\<rho> \<Turnstile>\<^sub>f (p, ids)"
  shows "\<rho> \<Turnstile>\<^sub>c\<^sub>l\<^sub>s Cls p args rhs"
  using assms by (force simp add: solves_cls_def)

lemmas resolution_last = resolution_last_from_cls_rh_to_cls resolution_last_from_cls_fact_to_cls


subsubsection \<open>Of only right hand\<close>

lemma resolution_only_from_cls_fact_to_fact:
  assumes "\<rho> \<Turnstile>\<^sub>c\<^sub>l\<^sub>s Cls p ids [PosRh p' ids']"
  assumes "\<rho> \<Turnstile>\<^sub>f (p', ids')"
  shows "\<rho> \<Turnstile>\<^sub>f (p, ids)"
  using assms
proof -
  from assms(2) have "\<forall>\<sigma>. \<lbrakk>PosRh p' ids'\<rbrakk>\<^sub>r\<^sub>h \<rho> \<sigma>"
    by fastforce
  then have "\<rho> \<Turnstile>\<^sub>c\<^sub>l\<^sub>s Cls p ids []"
    using assms(1) self_append_conv2 solves_rh.elims(3) resolution_last_from_cls_rh_to_cls by metis 
  then show "\<rho> \<Turnstile>\<^sub>f (p, ids)"
    by (meson solves_fact_fact)
qed

lemma resolution_only_from_cls_cls_to_cls:
  assumes "\<rho> \<Turnstile>\<^sub>c\<^sub>l\<^sub>s Cls p ids [PosRh p' ids']"
  assumes "\<rho> \<Turnstile>\<^sub>c\<^sub>l\<^sub>s Cls p' ids' []"
  shows "\<rho> \<Turnstile>\<^sub>c\<^sub>l\<^sub>s Cls p ids []"
  by (metis append_self_conv2 assms resolution_last_from_cls_rh_to_cls solves_fact_iff_solves_lh)

lemmas resolution_only = resolution_only_from_cls_fact_to_fact resolution_only_from_cls_cls_to_cls

subsubsection \<open>Of all right hands\<close>

lemma resolution_all_from_cls_rhs_to_fact:
  assumes "\<rho> \<Turnstile>\<^sub>c\<^sub>l\<^sub>s Cls p ids rhs"
  assumes "\<forall>rh\<in>set rhs. \<rho> \<Turnstile>\<^sub>r\<^sub>h rh"
  shows "\<rho> \<Turnstile>\<^sub>f (p, ids)"
  using assms unfolding solves_cls_def meaning_fact.simps by force

lemmas resolution_all = resolution_all_from_cls_rhs_to_fact

lemmas resolution = resolution_last resolution_only resolution_all

subsection \<open>Substitution\<close>

lemma substitution_lemma_id: "\<lbrakk>a\<rbrakk>\<^sub>i\<^sub>d (\<eta> \<circ>\<^sub>s\<^sub>v \<sigma>) = \<lbrakk>a \<cdot>\<^sub>i\<^sub>d \<eta>\<rbrakk>\<^sub>i\<^sub>d \<sigma>"
  by (cases a) (auto simp add: compose_def)

lemma substitution_lemma_ids: "\<lbrakk>ids\<rbrakk>\<^sub>i\<^sub>d\<^sub>s (\<eta> \<circ>\<^sub>s\<^sub>v \<sigma>) = \<lbrakk>ids \<cdot>\<^sub>i\<^sub>d\<^sub>s \<eta>\<rbrakk>\<^sub>i\<^sub>d\<^sub>s \<sigma>"
  using substitution_lemma_id by auto

lemma substitution_lemma_lh: "\<lbrakk>(p, ids)\<rbrakk>\<^sub>l\<^sub>h \<rho> (\<eta> \<circ>\<^sub>s\<^sub>v \<sigma>) \<longleftrightarrow> \<lbrakk>(p, ids \<cdot>\<^sub>i\<^sub>d\<^sub>s \<eta> )\<rbrakk>\<^sub>l\<^sub>h \<rho> \<sigma>"
  by (metis meaning_lh.simps substitution_lemma_ids)

lemma substitution_lemma_rh:"\<lbrakk>rh\<rbrakk>\<^sub>r\<^sub>h \<rho> (\<eta> \<circ>\<^sub>s\<^sub>v \<sigma>) \<longleftrightarrow> \<lbrakk>rh \<cdot>\<^sub>r\<^sub>h \<eta>\<rbrakk>\<^sub>r\<^sub>h \<rho> \<sigma>"
proof (induction rh)
  case (Eql a a')
  then show ?case
    by (simp add: substitution_lemma_id)
next
  case (Neql a a')
  then show ?case
    by (simp add: substitution_lemma_id)
next
  case (PosRh p ids)
  then show ?case
    using substitution_lemma_lh by fastforce
next
  case (NegRh p ids)
  then show ?case
    using substitution_lemma_lh by fastforce
qed

lemma substitution_lemma_rhs: "\<lbrakk>rhs\<rbrakk>\<^sub>r\<^sub>h\<^sub>s \<rho> (\<eta> \<circ>\<^sub>s\<^sub>v \<sigma>) \<longleftrightarrow> \<lbrakk>rhs \<cdot>\<^sub>r\<^sub>h\<^sub>s \<eta>\<rbrakk>\<^sub>r\<^sub>h\<^sub>s \<rho> \<sigma>"
  by (simp add: substitution_lemma_rh) 

lemma substitution_lemma_cls:
  "\<lbrakk>c\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho> (\<eta> \<circ>\<^sub>s\<^sub>v \<sigma>) = \<lbrakk>c \<cdot>\<^sub>c\<^sub>l\<^sub>s \<eta>\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho> \<sigma>"
proof (induction c)
  case (Cls p ids rhs)
  have a: "\<lbrakk>rhs\<rbrakk>\<^sub>r\<^sub>h\<^sub>s \<rho> (\<eta> \<circ>\<^sub>s\<^sub>v \<sigma>) = \<lbrakk>rhs \<cdot>\<^sub>r\<^sub>h\<^sub>s \<eta>\<rbrakk>\<^sub>r\<^sub>h\<^sub>s \<rho> \<sigma>"
    using substitution_lemma_rhs by blast
  have b: "\<lbrakk>(p, ids)\<rbrakk>\<^sub>l\<^sub>h \<rho> (\<eta> \<circ>\<^sub>s\<^sub>v \<sigma>) = \<lbrakk>(p, ids \<cdot>\<^sub>i\<^sub>d\<^sub>s \<eta>)\<rbrakk>\<^sub>l\<^sub>h \<rho> \<sigma>"
    using substitution_lemma_lh by metis
  show ?case
    unfolding meaning_cls.simps using a b by auto
qed

lemma substitution_rule:
  assumes "\<rho> \<Turnstile>\<^sub>c\<^sub>l\<^sub>s c"
  shows "\<rho> \<Turnstile>\<^sub>c\<^sub>l\<^sub>s (c \<cdot>\<^sub>c\<^sub>l\<^sub>s (\<eta>::('x,'e) subst))"
proof -
  show ?thesis
    unfolding solves_cls_def
  proof
    fix \<sigma> :: "'x \<Rightarrow> 'e"
    from assms have "\<lbrakk>c\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho> (\<eta> \<circ>\<^sub>s\<^sub>v \<sigma>)"
      using solves_cls_def by auto
    then show "\<lbrakk>c \<cdot>\<^sub>c\<^sub>l\<^sub>s \<eta> \<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho> \<sigma>"
      using substitution_lemma_cls by blast
  qed
qed


section \<open>Stratification and solutions to stratified datalog programs\<close>

type_synonym 'p strat = "'p \<Rightarrow> nat"

fun rnk :: "'p strat \<Rightarrow> ('p,'x,'e) righthand \<Rightarrow> nat" where
  "rnk s (a \<^bold>= a') = 0"
| "rnk s (a \<^bold>\<noteq> a') = 0"
| "rnk s (PosRh p ids) = s p"
| "rnk s (\<^bold>\<not> p ids) = 1 + s p"

fun strat_wf_cls :: "'p strat \<Rightarrow> ('p,'x,'e) clause \<Rightarrow> bool" where
  "strat_wf_cls s (Cls p ids rhs) \<longleftrightarrow> (\<forall>rh \<in> set rhs. s p \<ge> rnk s rh)"

definition strat_wf :: "'p strat \<Rightarrow> ('p,'x,'e) dl_program \<Rightarrow> bool" where
  "strat_wf s dl \<longleftrightarrow> (\<forall>c \<in> dl. strat_wf_cls s c)"

definition max_strata :: "'p strat \<Rightarrow> ('p,'x,'e) dl_program \<Rightarrow> nat" where
  "max_strata s dl = Max {s p | p ids rhs. Cls p ids rhs \<in> dl}"

fun pred_val_mod_strata :: "('p,'e) pred_val \<Rightarrow> 'p strat \<Rightarrow> nat \<Rightarrow> ('p,'e) pred_val" ("_ \\_\\ _" 0) where 
  "(\<rho> \\s\\ n) p = (if s p \<le> n then \<rho> p else {})"

fun dl_program_mod_strata :: "('p,'x,'e) dl_program \<Rightarrow> 'p strat \<Rightarrow> nat \<Rightarrow> ('p,'x,'e) dl_program" ("_ --_-- _" 0) where 
  "(dl -- s -- n) = {(Cls p ids rhs)| p ids rhs . (Cls p ids rhs) \<in> dl \<and> s p \<le> n}"

fun dl_program_on_strata :: "('p,'x,'e) dl_program \<Rightarrow> 'p strat \<Rightarrow> nat \<Rightarrow> ('p,'x,'e) dl_program" ("_ ==_== _" 0) where 
  "(dl == s == n) = {(Cls p ids rhs)| p ids rhs . (Cls p ids rhs) \<in> dl \<and> s p = n}"

definition lt :: "('p,'e) pred_val \<Rightarrow> 'p strat \<Rightarrow> ('p,'e) pred_val \<Rightarrow> bool" ("_ \<sqsubset>_\<sqsubset> _") where
  "(\<rho> \<sqsubset>s\<sqsubset> \<rho>') \<longleftrightarrow> (\<exists>p. \<rho> p \<subset> \<rho>' p \<and>
                       (\<forall>p'. s p' = s p \<longrightarrow> \<rho> p' \<subseteq> \<rho>' p') \<and>
                       (\<forall>p'. s p' < s p \<longrightarrow> \<rho> p' = \<rho>' p'))"

definition lte :: "('p,'e) pred_val \<Rightarrow> 'p strat \<Rightarrow> ('p,'e) pred_val \<Rightarrow> bool" ("_ \<sqsubseteq>_\<sqsubseteq> _") where
  "(\<rho> \<sqsubseteq>s\<sqsubseteq> \<rho>') \<longleftrightarrow> \<rho> = \<rho>' \<or> (\<rho> \<sqsubset>s\<sqsubset> \<rho>')"

definition least_solution :: "('p,'e) pred_val \<Rightarrow> ('p,'x,'e) dl_program \<Rightarrow> 'p strat \<Rightarrow> bool" ("_ \<Turnstile>\<^sub>l\<^sub>s\<^sub>t") where
  "\<rho> \<Turnstile>\<^sub>l\<^sub>s\<^sub>t dl s \<longleftrightarrow> (\<rho> \<Turnstile>\<^sub>d\<^sub>l dl \<and> (\<forall>\<rho>'. \<rho>' \<Turnstile>\<^sub>d\<^sub>l dl \<longrightarrow> \<rho> \<sqsubseteq>s\<sqsubseteq> \<rho>'))"

definition minimal_solution :: "('p,'e) pred_val \<Rightarrow> ('p,'x,'e) dl_program \<Rightarrow> 'p strat \<Rightarrow> bool"  ("_ \<Turnstile>\<^sub>m\<^sub>i\<^sub>n") where
  "\<rho> \<Turnstile>\<^sub>m\<^sub>i\<^sub>n dl s \<longleftrightarrow> (\<rho> \<Turnstile>\<^sub>d\<^sub>l dl \<and> (\<nexists>\<rho>'. \<rho>' \<Turnstile>\<^sub>d\<^sub>l dl \<and> \<rho>' \<sqsubset>s\<sqsubset> \<rho>))"

lemma lte_def2:
  "(\<rho> \<sqsubseteq>s\<sqsubseteq> \<rho>') \<longleftrightarrow> \<rho> \<noteq> \<rho>' \<longrightarrow> (\<rho> \<sqsubset>s\<sqsubset> \<rho>')"
  unfolding lte_def by auto


subsection \<open>Solving lower strata\<close>

lemma strat_wf_mod_if_strat_wf_mod:
  assumes "n > m"
  assumes "strat_wf s (dl --s-- n)"
  shows "strat_wf s (dl --s-- m)"
  using assms unfolding strat_wf_def by fastforce

lemma strat_wf_mod_if_strat_wf:
  assumes "strat_wf s dl"
  shows "strat_wf s (dl --s-- n)"
  using assms unfolding strat_wf_def by auto

lemma meaning_mod_m_iff_meaning_rh:
  assumes "rnk s rh \<le> n"
  shows "\<lbrakk>rh\<rbrakk>\<^sub>r\<^sub>h (\<rho> \\s\\ n) \<sigma> \<longleftrightarrow> \<lbrakk>rh\<rbrakk>\<^sub>r\<^sub>h \<rho> \<sigma>"
  using assms equals0D meaning_rh.elims(3) pred_val_mod_strata.simps by fastforce

lemma meaning_mod_m_iff_meaning_lh:
  assumes "s p \<le> m"
  shows "\<lbrakk>(p, ids)\<rbrakk>\<^sub>l\<^sub>h (\<rho> \\s\\ m) \<sigma> \<longleftrightarrow> \<lbrakk>(p, ids)\<rbrakk>\<^sub>l\<^sub>h \<rho> \<sigma>"
  using assms by auto

lemma meaning_mod_m_iff_meaning_cls:
  assumes "strat_wf_cls s (Cls p ids rhs)"
  assumes "s p \<le> m"
  shows "\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s (\<rho> \\s\\ m) \<sigma> \<longleftrightarrow> \<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho> \<sigma>"
proof -
  have p_leq_m: "s p \<le> m"
    using assms by fastforce
  have rh_leq_m: "\<forall>rh \<in> set rhs. rnk s rh \<le> m"
    using assms assms(2) dual_order.trans by (metis (no_types, lifting) p_leq_m strat_wf_cls.simps)

  show "\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s (\<rho> \\s\\ m) \<sigma> \<longleftrightarrow> \<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho> \<sigma>"
    using meaning_mod_m_iff_meaning_rh[of s _ m \<rho> \<sigma>] p_leq_m rh_leq_m assms(2) by force
qed

lemma solves_mod_m_iff_solves_cls:
  assumes "strat_wf_cls s (Cls p ids rhs)"
  assumes "s p \<le> m"
  shows "(\<rho> \\s\\ m) \<Turnstile>\<^sub>c\<^sub>l\<^sub>s Cls p ids rhs \<longleftrightarrow> \<rho> \<Turnstile>\<^sub>c\<^sub>l\<^sub>s Cls p ids rhs"
  by (meson assms meaning_mod_m_iff_meaning_cls solves_cls_def)
                                          
lemma downward_mod_solves:
  assumes "n > m"
  assumes "\<rho> \<Turnstile>\<^sub>d\<^sub>l (dl --s-- n)"
  assumes "strat_wf s dl"
  shows "(\<rho> \\s\\ m) \<Turnstile>\<^sub>d\<^sub>l (dl --s-- m)"
  unfolding solves_program_def
proof
  fix c
  assume a: "c \<in> (dl --s-- m)"
  obtain p ids rhs where c_split: "c = Cls p ids rhs"
    by (cases c) auto

  have "m < n"
    using assms(1) by blast
  moreover
  have "strat_wf_cls s (Cls p ids rhs)"
    using a assms(3) c_split strat_wf_mod_if_strat_wf strat_wf_def by blast
  moreover
  have "s p \<le> m"
    using a c_split by force
  moreover
  have "\<rho> \<Turnstile>\<^sub>c\<^sub>l\<^sub>s Cls p ids rhs"
    using c_split assms a unfolding solves_program_def by force  
  ultimately
  show "(\<rho> \\s\\ m) \<Turnstile>\<^sub>c\<^sub>l\<^sub>s c"
    using c_split by (simp add: solves_mod_m_iff_solves_cls)
qed

lemma downward_solves:
  assumes "\<rho> \<Turnstile>\<^sub>d\<^sub>l dl"
  assumes "strat_wf s dl"
  shows "(\<rho> \\s\\ m) \<Turnstile>\<^sub>d\<^sub>l (dl --s-- m)"
  unfolding solves_program_def
proof
  fix c
  assume a: "c \<in> (dl --s-- m)"
  then obtain p ids rhs where c_def: "c = Cls p ids rhs"
    by (cases c) auto

  have "\<rho> \<Turnstile>\<^sub>c\<^sub>l\<^sub>s c"
    using \<open>c \<in> (dl --s-- m)\<close> assms(1) solves_program_def by auto

  have "(\<rho> \\s\\ m) \<Turnstile>\<^sub>c\<^sub>l\<^sub>s Cls p ids rhs"
    using \<open>\<rho> \<Turnstile>\<^sub>c\<^sub>l\<^sub>s c\<close> a assms(2) c_def solves_mod_m_iff_solves_cls strat_wf_def by fastforce
  then show "(\<rho> \\s\\ m) \<Turnstile>\<^sub>c\<^sub>l\<^sub>s c"
    using c_def by auto
qed

subsection \<open>Least solutions\<close>

subsubsection \<open>Existence of least solutions\<close>

definition Inter' :: "('a \<Rightarrow> 'b set) set \<Rightarrow> 'a \<Rightarrow> 'b set" ("\<^bold>\<Inter>") where 
  "(\<^bold>\<Inter> \<rho>s) = (\<lambda>p. \<Inter>{m. \<exists>\<rho> \<in> \<rho>s. m = \<rho> p})"

lemma member_Inter':
  assumes "\<forall>p\<in>ps. y \<in> p x"
  shows "y \<in> (\<^bold>\<Inter> ps) x"
  by (smt (verit, best) Inter'_def assms mem_Collect_eq mem_simps(11))

lemma member_if_member_Inter':
  assumes "y \<in> (\<^bold>\<Inter> ps) x"
  assumes "p\<in>ps"
  shows "y \<in> p x"
  by (smt (verit, best) Inter'_def assms mem_Collect_eq mem_simps(11))

lemma member_Inter'_iff:
  "(\<forall>p\<in>ps. y \<in> p x) \<longleftrightarrow> y \<in> (\<^bold>\<Inter> ps) x"
  by (smt (verit, best) Inter'_def mem_Collect_eq mem_simps(11))

lemma intersection_valuation_subset_valuation:
  assumes "P \<rho>"
  shows "\<^bold>\<Inter> {\<rho>'. P  \<rho>'} p \<subseteq> \<rho> p"
  by (metis (mono_tags, lifting) CollectI Inf_lower Inter'_def assms)

fun solve_pg where
  "solve_pg s dl 0 = (\<^bold>\<Inter> {\<rho>'. \<rho>' \<Turnstile>\<^sub>d\<^sub>l (dl ==s== 0)})"
| "solve_pg s dl (Suc n) = (\<^bold>\<Inter> {\<rho>'. \<rho>' \<Turnstile>\<^sub>d\<^sub>l (dl ==s== Suc n) \<and> (\<rho>' \\s\\ n) = solve_pg s dl n})"

definition least_rank_p_st :: "('p \<Rightarrow> bool) \<Rightarrow> 'p \<Rightarrow> ('p \<Rightarrow> nat) \<Rightarrow> bool" where 
  "least_rank_p_st P p s \<longleftrightarrow> P p \<and> (\<forall>p'. P p' \<longrightarrow> s p \<le> s p')"

lemma least_rank_p_st_exists:
  assumes "P p"
  shows "\<exists>p''. least_rank_p_st P p'' s"
  using assms
proof (induction "s p" arbitrary: p rule: less_induct)
  case less
  then show ?case
  proof (cases "\<exists>p''. s p'' < s p \<and> P p''")
    case True
    then show ?thesis
      using less by auto
  next
    case False
    then show ?thesis
      by (metis least_rank_p_st_def less.prems linorder_not_le)
  qed
qed

lemma below_least_rank_p_st:
  assumes "least_rank_p_st P p'' s"
  assumes "s p < s p''"
  shows "\<not>P p"
  using assms 
proof (induction "s p''")
  case 0
  then show ?case by auto
next
  case (Suc n)
  then show ?case
    by (metis least_rank_p_st_def linorder_not_le)
qed

lemma solves_leq:
  assumes "\<rho> \<Turnstile>\<^sub>d\<^sub>l (dl --s-- m)"
  assumes "n \<le> m"
  shows "\<rho> \<Turnstile>\<^sub>d\<^sub>l (dl --s-- n)"
  using assms unfolding solves_program_def by auto

lemma solves_Suc:
  assumes "\<rho> \<Turnstile>\<^sub>d\<^sub>l (dl --s-- Suc n)"
  shows "\<rho> \<Turnstile>\<^sub>d\<^sub>l (dl --s-- n)"
  by (meson assms lessI less_imp_le_nat solves_leq)

lemma solve_pg_0_subset:
  assumes "\<rho> \<Turnstile>\<^sub>d\<^sub>l (dl --s-- 0)"
  shows "(solve_pg s dl 0) p \<subseteq> \<rho> p"
  using assms by (auto simp add: Inter'_def)

lemma solve_pg_Suc_subset:
  assumes "\<rho> \<Turnstile>\<^sub>d\<^sub>l (dl ==s== Suc n)"
  assumes "(\<rho> \\s\\ n) = solve_pg s dl n"
  shows "(solve_pg s dl (Suc n)) p \<subseteq> \<rho> p"
  using assms by (force simp add: Inter'_def)

lemma solve_pg_0_empty:
  assumes "s p > 0"
  shows "(solve_pg s dl 0) p = {}"
proof -
  define \<rho>'' :: "'a \<Rightarrow> 'b list set" where "\<rho>'' = (solve_pg s dl 0)"
  define \<rho>' :: "'a \<Rightarrow> 'b list set" where "\<rho>' = (\<lambda>p. if s p = 0 then UNIV else {})"
  have "\<rho>' \<Turnstile>\<^sub>d\<^sub>l (dl ==s== 0)"
    unfolding solves_program_def solves_cls_def 
  proof (rule, rule)
    fix c \<sigma>
    assume c_dl0: "c \<in> (dl ==s== 0)"
    obtain p' ids rhs where c_split: "c = Cls p' ids rhs"
      by (cases c) auto
    then have sp'0: "s p' = 0" 
      using c_dl0 by auto
    have "\<lbrakk>Cls p' ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho>' \<sigma>"
      unfolding meaning_cls.simps
    proof (rule) 
      assume "\<lbrakk>rhs\<rbrakk>\<^sub>r\<^sub>h\<^sub>s \<rho>' \<sigma>"
      show "\<lbrakk>(p', ids)\<rbrakk>\<^sub>l\<^sub>h \<rho>' \<sigma>"
        using \<rho>'_def sp'0 by force
    qed
    then show "\<lbrakk>c\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho>' \<sigma>"
      unfolding c_split by auto
  qed
  have "\<rho>'' p \<subseteq> \<rho>' p"
    using \<open>\<rho>' \<Turnstile>\<^sub>d\<^sub>l (dl ==s== 0)\<close> \<rho>''_def solve_pg_0_subset by fastforce
  then have "\<rho>'' p = {}"
    unfolding \<rho>'_def using assms(1) by simp
  then show ?thesis 
    unfolding \<rho>''_def by auto
qed

lemma solve_pg_Suc_empty:
  assumes "s p > n"
  shows "(solve_pg s dl n) p = {}"
  using assms proof (induction n arbitrary: p)
  case 0
  then show ?case
    using solve_pg_0_empty by metis
next
  case (Suc n)
  define \<rho>'' :: "'a \<Rightarrow> 'b list set" where 
    "\<rho>'' = (solve_pg s dl (Suc n))"
  define \<rho>' :: "'a \<Rightarrow> 'b list set" where 
    "\<rho>' = (\<lambda>p. if s p < Suc n then (solve_pg s dl n) p else if s p = Suc n then UNIV else {})"

  have \<rho>'_solves: "\<rho>' \<Turnstile>\<^sub>d\<^sub>l (dl ==s== Suc n)"
    unfolding solves_program_def solves_cls_def 
  proof (rule, rule)
    fix c \<sigma>
    assume c_dlSucn: "c \<in> (dl ==s== Suc n)"
    obtain p' ids rhs where c_split: "c = Cls p' ids rhs"
      by (cases c) auto
    then have sp'Sucn: "s p' = Suc n" 
      using c_dlSucn by auto
    have "\<lbrakk>Cls p' ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho>' \<sigma>"
      unfolding meaning_cls.simps
    proof (rule)
      assume "\<lbrakk>rhs\<rbrakk>\<^sub>r\<^sub>h\<^sub>s \<rho>' \<sigma>"
      show "\<lbrakk>(p', ids)\<rbrakk>\<^sub>l\<^sub>h \<rho>' \<sigma>"
        using \<rho>'_def sp'Sucn by auto[]
    qed
    then show "\<lbrakk>c\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho>' \<sigma>"
      unfolding c_split by auto
  qed
  have "\<forall>p. (\<rho>' \\s\\ n) p = (solve_pg s dl n) p"
    using Suc by (auto simp add: \<rho>'_def)
  then have "\<rho>'' p \<subseteq> \<rho>' p"
    using solve_pg_Suc_subset[of \<rho>' dl s n  p] \<rho>'_solves \<rho>''_def by force
  then have "\<rho>'' p = {}"
    unfolding \<rho>'_def using assms(1) Suc by simp
  then show ?case
    unfolding \<rho>''_def by auto
qed

lemma exi_sol_n: "\<exists>\<rho>'. \<rho>' \<Turnstile>\<^sub>d\<^sub>l (dl ==s== Suc m) \<and> (\<rho>' \\s\\ m) = solve_pg s dl m"
proof -
  define \<rho>' where 
    "\<rho>' = (\<lambda>p. (if s p < Suc m then (solve_pg s dl m) p else if s p = Suc m then UNIV else {}))"

  have "\<rho>' \<Turnstile>\<^sub>d\<^sub>l (dl ==s== Suc m)"
    unfolding \<rho>'_def solves_cls_def solves_program_def by fastforce
  moreover
  have "\<forall>p. (\<rho>' \\s\\ m) p = solve_pg s dl m p"
    unfolding \<rho>'_def using solve_pg_Suc_empty[of m s _ dl] by auto
  ultimately
  show ?thesis 
    by force
qed

lemma solve_pg_agree_above:
  assumes "s p \<le> m"
  shows "(solve_pg s dl m) p = (solve_pg s dl (s p)) p"
  using assms 
proof (induction m)
  case 0
  then show ?case
    by force
next
  case (Suc m)
  show ?case
  proof (cases "s p = Suc m")
    case True
    then show ?thesis by auto
  next
    case False
    then have s_p: "s p \<le> m"
      using Suc by auto
    then have solve_pg_sp_m: "(solve_pg s dl (s p)) p = (solve_pg s dl m) p"
      using Suc by auto
    have \<rho>'_solve_pg: "\<forall>\<rho>'. \<rho>' \<Turnstile>\<^sub>d\<^sub>l (dl ==s== Suc m) \<and> (\<rho>' \\s\\ m) = solve_pg s dl m \<longrightarrow> \<rho>' p = solve_pg s dl m p"
      by (metis pred_val_mod_strata.simps s_p)
    have "\<^bold>\<Inter> {\<rho>'. \<rho>' \<Turnstile>\<^sub>d\<^sub>l (dl ==s== Suc m) \<and> (\<rho>' \\s\\ m) = solve_pg s dl m} p = solve_pg s dl (s p) p"
    proof (rule; rule)
      fix x 
      assume "x \<in> \<^bold>\<Inter> {\<rho>'. \<rho>' \<Turnstile>\<^sub>d\<^sub>l (dl ==s== Suc m) \<and> (\<rho>' \\s\\ m) = solve_pg s dl m} p"
      then show "x \<in> solve_pg s dl (s p) p"
        by (metis (mono_tags) CollectI \<rho>'_solve_pg exi_sol_n member_if_member_Inter' solve_pg_sp_m)
    next
      fix x
      assume "x \<in> solve_pg s dl (s p) p"
      then show "x \<in> \<^bold>\<Inter> {\<rho>'. \<rho>' \<Turnstile>\<^sub>d\<^sub>l (dl ==s== Suc m) \<and> (\<rho>' \\s\\ m) = solve_pg s dl m} p"
        by (simp add: \<rho>'_solve_pg member_Inter' solve_pg_sp_m)
    qed
    then show ?thesis
      by simp
  qed
qed

lemma solve_pg_two_agree_above:
  assumes "s p \<le> n"
  assumes "s p \<le> m"
  shows "(solve_pg s dl m) p = (solve_pg s dl n) p"
  using assms solve_pg_agree_above by metis

lemma pos_rhs_strata_leq_clause_strata:
  assumes "strat_wf s dl"
  assumes "Cls p ids rhs \<in> dl"
  assumes "PosRh p' ids' \<in> set rhs"
  shows "s p' \<le> s p"
  using assms unfolding strat_wf_def by fastforce

lemma neg_rhs_strata_less_clause_strata:
  assumes "strat_wf s dl"
  assumes "Cls p ids rhs \<in> dl"
  assumes "\<^bold>\<not> p' ids' \<in> set rhs"
  shows "s p' < s p"
  using assms unfolding strat_wf_def by fastforce

lemma solve_pg_two_agree_above_on_rh:
  assumes "strat_wf s dl"
  assumes "Cls p ids rhs \<in> dl"
  assumes "s p \<le> n"
  assumes "s p \<le> m"
  assumes "rh \<in> set rhs"
  shows "\<lbrakk>rh\<rbrakk>\<^sub>r\<^sub>h (solve_pg s dl m) \<sigma> \<longleftrightarrow> \<lbrakk>rh\<rbrakk>\<^sub>r\<^sub>h (solve_pg s dl n) \<sigma>"
proof (cases rh)
  case (Eql a a')
  then show ?thesis
    using assms by auto
next
  case (Neql a a')
  then show ?thesis 
    using assms by auto
next
  case (PosRh p' ids')
  then have "s p' \<le> m"
    using assms pos_rhs_strata_leq_clause_strata by fastforce
  moreover
  from PosRh have "s p' \<le> n"
    using assms pos_rhs_strata_leq_clause_strata by fastforce
  ultimately
  have "solve_pg s dl m p' = solve_pg s dl n p'"
    using solve_pg_two_agree_above[of s p' n m dl] by force
  then show ?thesis
    by (simp add: PosRh)
next
  case (NegRh p' ids)
  then have "s p' < m"
    using assms neg_rhs_strata_less_clause_strata by fastforce
  moreover
  from NegRh have "s p' < n"
    using assms neg_rhs_strata_less_clause_strata by fastforce
  ultimately
  have "solve_pg s dl m p' = solve_pg s dl n p'"
    using solve_pg_two_agree_above[of s p' n m dl] by force
  then show ?thesis
    by (simp add: NegRh)
qed

lemma solve_pg_two_agree_above_on_lh:
  assumes "s p \<le> n"
  assumes "s p \<le> m"
  shows "\<lbrakk>(p,ids)\<rbrakk>\<^sub>l\<^sub>h (solve_pg s dl m) \<sigma> \<longleftrightarrow> \<lbrakk>(p,ids)\<rbrakk>\<^sub>l\<^sub>h (solve_pg s dl n) \<sigma>"
  by (metis assms meaning_lh.simps solve_pg_two_agree_above)

lemma solve_pg_two_agree_above_on_cls:
  assumes "strat_wf s dl"
  assumes "Cls p ids rhs \<in> dl"
  assumes "s p \<le> n"
  assumes "s p \<le> m"
  shows "\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s (solve_pg s dl n) \<sigma> \<longleftrightarrow> \<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s (solve_pg s dl m) \<sigma>"
  by (meson assms meaning_rhs.simps meaning_cls.simps solve_pg_two_agree_above_on_rh solve_pg_two_agree_above_on_lh)

lemma solve_pg_two_agree_above_on_cls_Suc:
  assumes "strat_wf s dl"
  assumes "Cls p ids rhs \<in> dl"
  assumes "s p \<le> n"
  shows "\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s (solve_pg s dl (Suc n)) \<sigma> \<longleftrightarrow> \<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s (solve_pg s dl n) \<sigma>"
  using solve_pg_two_agree_above_on_cls[OF assms(1,2,3), of "Suc n" \<sigma>] assms(3) by auto

lemma strata0_no_neg':
  assumes "strat_wf s dl"
  assumes "Cls p ids rhs \<in> dl"
  assumes "s p = 0"
  assumes "rh \<in> set rhs"
  shows "\<nexists>p' ids. rh = \<^bold>\<not> p' ids"
  by (metis One_nat_def add_eq_0_iff_both_eq_0 assms bot_nat_0.extremum_uniqueI bot_nat_0.not_eq_extremum rnk.simps(4) strat_wf_cls.simps strat_wf_def zero_less_Suc)

lemma strataSuc_less_neg':
  assumes "strat_wf s dl"
  assumes "Cls p ids rhs \<in> dl"
  assumes "s p = Suc n"
  assumes "\<^bold>\<not> p' ids' \<in> set rhs"
  shows "s p' \<le> n"
  using assms unfolding strat_wf_def by force

lemma strata0_no_neg:
  assumes "strat_wf s dl"
  assumes "Cls p ids rhs \<in> (dl --s-- 0)"
  assumes "rh \<in> set rhs"
  shows "\<nexists>p' ids. rh = \<^bold>\<not> p ids"
  using assms strata0_no_neg' by fastforce 

lemma strataSuc_less_neg:
  assumes "strat_wf s dl"
  assumes "Cls p ids rhs \<in> (dl --s-- Suc n)"
  assumes "\<^bold>\<not> p' ids' \<in> set rhs"
  shows "s p' \<le> n"
  using assms neg_rhs_strata_less_clause_strata by fastforce

lemma all_meaning_rh_if_solve_pg_0:
  assumes "strat_wf s dl"
  assumes "\<lbrakk>rh\<rbrakk>\<^sub>r\<^sub>h (solve_pg s dl 0) \<sigma>"
  assumes "\<rho> \<Turnstile>\<^sub>d\<^sub>l (dl --s-- 0)"
  assumes "rh \<in> set rhs"
  assumes "Cls p ids rhs \<in> (dl --s-- 0)"
  shows "\<lbrakk>rh\<rbrakk>\<^sub>r\<^sub>h \<rho> \<sigma>"
proof (cases rh)
  case (Eql a1 a2)
  then show ?thesis
    using assms by auto
next
  case (Neql a1 a2)
  then show ?thesis
    using assms by auto
next
  case (PosRh p ids)
  then show ?thesis
    using assms meaning_rh.simps(3) solve_pg_0_subset by fastforce
next
  case (NegRh p ids)
  then show ?thesis
    using assms strata0_no_neg' by fastforce
qed

lemma all_meaning_rh_if_solve_pg_Suc:
  assumes "strat_wf s dl"
  assumes "\<lbrakk>rh\<rbrakk>\<^sub>r\<^sub>h (solve_pg s dl (Suc n)) \<sigma>"
  assumes "\<rho> \<Turnstile>\<^sub>d\<^sub>l (dl ==s== Suc n)"
  assumes "(\<rho> \\s\\ n) = solve_pg s dl n"
  assumes "rh \<in> set rhs"
  assumes "Cls p ids rhs \<in> (dl --s-- Suc n)"
  shows "\<lbrakk>rh\<rbrakk>\<^sub>r\<^sub>h \<rho> \<sigma>"
proof (cases rh)
  case (Eql a a')
  then show ?thesis
    using assms(2) by auto
next
  case (Neql a a')
  then show ?thesis
    using assms(2) by force
next
  case (PosRh p' ids')
  then show ?thesis
    using assms solve_pg_Suc_subset by fastforce
next
  case (NegRh p' ids')
  then have "s p' \<le> n"
    using strataSuc_less_neg[OF assms(1) assms(6), of p'] assms(5) by auto
  then have "\<lbrakk>rh\<rbrakk>\<^sub>r\<^sub>h (solve_pg s dl n) \<sigma>"
    by (metis NegRh assms(2) le_imp_less_Suc less_imp_le_nat meaning_rh.simps(4) solve_pg_two_agree_above)
  then have "\<lbrakk>rh\<rbrakk>\<^sub>r\<^sub>h (\<rho> \\s\\ n) \<sigma>"
    using assms(4) by presburger
  then show ?thesis
    by (simp add: NegRh \<open>s p' \<le> n\<close>)
qed

lemma solve_pg_0_if_all_meaning_lh:
  assumes "\<forall>\<rho>'. \<rho>' \<Turnstile>\<^sub>d\<^sub>l (dl --s-- 0) \<longrightarrow> \<lbrakk>(p, ids)\<rbrakk>\<^sub>l\<^sub>h \<rho>' \<sigma>"
  shows "\<lbrakk>(p, ids)\<rbrakk>\<^sub>l\<^sub>h (solve_pg s dl 0) \<sigma>"
  using assms by (auto simp add: Inter'_def)

lemma all_meaning_lh_if_solve_pg_0:
  assumes "\<lbrakk>(p, ids)\<rbrakk>\<^sub>l\<^sub>h (solve_pg s dl 0) \<sigma>"
  shows "\<forall>\<rho>'. \<rho>' \<Turnstile>\<^sub>d\<^sub>l (dl --s-- 0) \<longrightarrow> \<lbrakk>(p, ids)\<rbrakk>\<^sub>l\<^sub>h \<rho>' \<sigma>"
  using assms by (auto simp add: Inter'_def)

lemma solve_pg_0_iff_all_meaning_lh:
  "\<lbrakk>(p, ids)\<rbrakk>\<^sub>l\<^sub>h (solve_pg s dl 0) \<sigma> \<longleftrightarrow> (\<forall>\<rho>'. \<rho>' \<Turnstile>\<^sub>d\<^sub>l (dl --s-- 0) \<longrightarrow> \<lbrakk>(p, ids)\<rbrakk>\<^sub>l\<^sub>h \<rho>' \<sigma>)"
  using solve_pg_0_if_all_meaning_lh all_meaning_lh_if_solve_pg_0 by metis

lemma solve_pg_Suc_if_all_meaning_lh:
  assumes "\<forall>\<rho>'. \<rho>' \<Turnstile>\<^sub>d\<^sub>l (dl ==s== Suc n) \<longrightarrow> (\<rho>' \\s\\ n) = solve_pg s dl n \<longrightarrow> \<lbrakk>(p, ids)\<rbrakk>\<^sub>l\<^sub>h \<rho>' \<sigma>"
  shows "\<lbrakk>(p, ids)\<rbrakk>\<^sub>l\<^sub>h (solve_pg s dl (Suc n)) \<sigma>"
  using assms by (auto simp add: Inter'_def)

lemma all_meaning_if_solve_pg_Suc_lh:
  assumes "\<lbrakk>(p, ids)\<rbrakk>\<^sub>l\<^sub>h (solve_pg s dl (Suc n)) \<sigma>"
  shows "\<forall>\<rho>'. \<rho>' \<Turnstile>\<^sub>d\<^sub>l (dl ==s== Suc n) \<longrightarrow> (\<rho>' \\s\\ n) = solve_pg s dl n \<longrightarrow> \<lbrakk>(p, ids)\<rbrakk>\<^sub>l\<^sub>h \<rho>' \<sigma>"
  using assms by (auto simp add: Inter'_def)

lemma solve_pg_Suc_iff_all_meaning_lh:
  "(\<lbrakk>(p, ids)\<rbrakk>\<^sub>l\<^sub>h (solve_pg s dl (Suc n)) \<sigma>) \<longleftrightarrow> (\<forall>\<rho>'. \<rho>' \<Turnstile>\<^sub>d\<^sub>l (dl ==s== Suc n) \<longrightarrow> (\<rho>' \\s\\ n) = solve_pg s dl n \<longrightarrow> \<lbrakk>(p, ids)\<rbrakk>\<^sub>l\<^sub>h \<rho>' \<sigma>)"
  by (auto simp add: Inter'_def)

lemma solve_pg_0_meaning_cls':
  assumes "strat_wf s dl"
  assumes "Cls p ids rhs \<in> (dl --s-- 0)"
  shows "\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s (solve_pg s dl 0) \<sigma>"
  unfolding meaning_cls.simps
proof
  define \<rho>'' :: "'a \<Rightarrow> 'c list set" where "\<rho>'' = (solve_pg s dl 0)"
  assume "\<lbrakk>rhs\<rbrakk>\<^sub>r\<^sub>h\<^sub>s (solve_pg s dl 0) \<sigma>"
  then have "\<forall>\<rho>'. \<rho>' \<Turnstile>\<^sub>d\<^sub>l (dl --s-- 0) \<longrightarrow> (\<forall>rh\<in>set rhs. \<lbrakk>rh\<rbrakk>\<^sub>r\<^sub>h \<rho>' \<sigma>)"
    using all_meaning_rh_if_solve_pg_0[OF assms(1), of _ \<sigma> _ rhs p ids, OF _ _ _ assms(2)] 
    by auto
  then have "\<forall>\<rho>'. \<rho>' \<Turnstile>\<^sub>d\<^sub>l (dl --s-- 0) \<longrightarrow> \<lbrakk>(p, ids)\<rbrakk>\<^sub>l\<^sub>h  \<rho>' \<sigma>"
    by (metis assms(2) meaning_cls.simps solves_cls_def solves_program_def meaning_rhs.simps)
  then show "\<lbrakk>(p, ids)\<rbrakk>\<^sub>l\<^sub>h (solve_pg s dl 0) \<sigma>"
    using solve_pg_0_if_all_meaning_lh by auto
qed

lemma solve_pg_Suc_meaning_cls':
  assumes "strat_wf s dl"
  assumes "Cls p ids rhs \<in> (dl --s-- n)"
  shows "\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s (solve_pg s dl n) \<sigma>"
  unfolding meaning_cls.simps
  using assms
proof (induction n)
  case 0
  then show ?case
    using solve_pg_0_meaning_cls' unfolding meaning_cls.simps by metis 
next
  case (Suc n)
  have leq_n: "s p \<le> Suc n"
    using Suc.prems(2) by auto

  have cls_in: "Cls p ids rhs \<in> dl"
    using assms(2) by force

  show ?case
  proof (cases "s p = Suc n")
    case True
    have cls_in_Suc: "Cls p ids rhs \<in> (dl ==s== Suc n)"
      by (simp add: True cls_in)
    show ?thesis
    proof
      define \<rho>'' :: "'a \<Rightarrow> 'c list set" where "\<rho>'' = (solve_pg s dl (Suc n))"
      assume "\<lbrakk>rhs\<rbrakk>\<^sub>r\<^sub>h\<^sub>s (solve_pg s dl (Suc n)) \<sigma>"
      then have "\<forall>\<rho>'. \<rho>' \<Turnstile>\<^sub>d\<^sub>l (dl ==s== Suc n) \<longrightarrow> (\<rho>' \\s\\ n) = solve_pg s dl n \<longrightarrow> (\<forall>rh\<in>set rhs. \<lbrakk>rh\<rbrakk>\<^sub>r\<^sub>h \<rho>' \<sigma>)"
        using all_meaning_rh_if_solve_pg_Suc[OF assms(1) _ _ _ _ Suc(3), of _ \<sigma>] 
        by auto
      then have "\<forall>\<rho>'. \<rho>' \<Turnstile>\<^sub>d\<^sub>l (dl ==s== Suc n) \<longrightarrow> (\<rho>' \\s\\ n) = solve_pg s dl n \<longrightarrow> \<lbrakk>(p, ids)\<rbrakk>\<^sub>l\<^sub>h \<rho>' \<sigma>"
        using meaning_cls.simps solves_cls_def solves_program_def cls_in_Suc meaning_rhs.simps by metis
      then show "\<lbrakk>(p, ids)\<rbrakk>\<^sub>l\<^sub>h (solve_pg s dl (Suc n)) \<sigma>"
        using solve_pg_Suc_if_all_meaning_lh[of dl s n p ids \<sigma>] by auto
    qed
  next
    case False
    then have False': "s p < Suc n"
      using leq_n by auto
    then have s_p_n: "s p \<le> n"
      by auto
    then have "Cls p ids rhs \<in> (dl --s-- n)"
      by (simp add: cls_in)
    then have "(\<forall>rh\<in>set rhs. \<lbrakk>rh\<rbrakk>\<^sub>r\<^sub>h (solve_pg s dl n) \<sigma>) \<longrightarrow> \<lbrakk>(p, ids)\<rbrakk>\<^sub>l\<^sub>h (solve_pg s dl n) \<sigma>"
      using Suc by auto
    then show ?thesis
      using False' meaning_cls.simps solve_pg_two_agree_above_on_cls_Suc assms cls_in s_p_n meaning_rhs.simps by metis
  qed
qed

lemma solve_pg_0_meaning_cls:
  assumes "strat_wf s dl"
  assumes "c \<in> (dl --s-- 0)"
  shows "\<lbrakk>c\<rbrakk>\<^sub>c\<^sub>l\<^sub>s (solve_pg s dl 0) \<sigma>"
  using assms solve_pg_0_meaning_cls'[of s dl _ _ _ \<sigma>] by (cases c) auto

lemma solve_pg_Suc_meaning_cls:
  assumes "strat_wf s dl"
  assumes "c \<in> (dl --s-- (Suc n))"
  shows "\<lbrakk>c\<rbrakk>\<^sub>c\<^sub>l\<^sub>s (solve_pg s dl (Suc n)) \<sigma>"
  using assms solve_pg_Suc_meaning_cls'[of s dl] by (cases c) metis

lemma solve_pg_0_solves_cls:
  assumes "strat_wf s dl"
  assumes "c \<in> (dl --s-- 0)"
  shows "(solve_pg s dl 0) \<Turnstile>\<^sub>c\<^sub>l\<^sub>s c"
  unfolding solves_cls_def using solve_pg_0_meaning_cls assms by blast

lemma solve_pg_Suc_solves_cls:
  assumes "strat_wf s dl"
  assumes "c \<in> (dl --s-- Suc n)"
  shows "(solve_pg s dl (Suc n)) \<Turnstile>\<^sub>c\<^sub>l\<^sub>s c"
  unfolding solves_cls_def using solve_pg_Suc_meaning_cls assms by blast

lemma solve_pg_0_solves_dl:
  assumes "strat_wf s dl"
  shows "(solve_pg s dl 0) \<Turnstile>\<^sub>d\<^sub>l (dl --s-- 0)"
proof -
  have "\<forall>c \<in> (dl --s-- 0). (solve_pg s dl 0) \<Turnstile>\<^sub>c\<^sub>l\<^sub>s c"
    using assms solve_pg_0_solves_cls[of s dl] by auto
  then show "(solve_pg s dl 0) \<Turnstile>\<^sub>d\<^sub>l (dl --s-- 0)"
    using solves_program_def by blast
qed

lemma solve_pg_Suc_solves_dl:
  assumes "strat_wf s dl"
  shows "(solve_pg s dl (Suc n)) \<Turnstile>\<^sub>d\<^sub>l (dl --s-- (Suc n))"
proof -
  have "\<forall>c \<in> (dl --s-- Suc n). (solve_pg s dl (Suc n)) \<Turnstile>\<^sub>c\<^sub>l\<^sub>s c"
    using assms solve_pg_Suc_solves_cls[of s dl] by auto
  then show "(solve_pg s dl (Suc n)) \<Turnstile>\<^sub>d\<^sub>l (dl --s-- Suc n)"
    using solves_program_def by blast
qed

lemma disjE3:
  assumes major: "P \<or> Q \<or> Z"
    and minorP: "P \<Longrightarrow> R"
    and minorQ: "Q \<Longrightarrow> R"
    and minorZ: "Z \<Longrightarrow> R"
  shows R
  using assms by auto

lemma solve_pg_0_below_solution:
  assumes "\<rho> \<Turnstile>\<^sub>d\<^sub>l (dl --s-- 0)"
  shows "(solve_pg s dl 0) \<sqsubseteq>s\<sqsubseteq> \<rho>"
proof -
  define \<rho>'' :: "'a \<Rightarrow> 'b list set" where "\<rho>'' = solve_pg s dl 0"

  have "\<rho>'' \<noteq> \<rho> \<longrightarrow> \<rho>'' \<sqsubset>s\<sqsubset> \<rho>"
  proof 
    assume "\<rho>'' \<noteq> \<rho>"
    have \<rho>''_subs_\<rho>: "\<forall>p. \<rho>'' p \<subseteq> \<rho> p"
      using solve_pg_0_subset unfolding \<rho>''_def using assms(1) by force
    have "\<forall>p. s p > 0 \<longrightarrow> \<rho>'' p = {}"
      using solve_pg_0_empty \<rho>''_def by metis
    have "\<exists>p. least_rank_p_st (\<lambda>p. \<rho>'' p \<noteq> \<rho> p) p s"
      by (meson \<open>\<rho>'' \<noteq> \<rho>\<close> ext least_rank_p_st_exists)
    then obtain p where p_p: "least_rank_p_st (\<lambda>p. \<rho>'' p \<noteq> \<rho> p) p s"
      by auto
    have "\<rho>'' p \<subset> \<rho> p"
      by (metis (mono_tags, lifting) \<rho>''_subs_\<rho> p_p least_rank_p_st_def psubsetI)
    moreover
    have "\<forall>p'. s p' = s p \<longrightarrow> \<rho>'' p' \<subseteq> \<rho> p'"
      using \<rho>''_subs_\<rho> by auto
    moreover
    have "\<forall>p'. s p' < s p \<longrightarrow> \<rho>'' p' = \<rho> p'"
      using below_least_rank_p_st[OF p_p] by auto
    ultimately
    show "\<rho>'' \<sqsubset>s\<sqsubset> \<rho>"
      unfolding lt_def by auto
  qed
  then show ?thesis
    using \<rho>''_def lte_def by auto
qed

lemma least_disagreement_proper_subset:
  assumes "\<rho>''n \<sqsubset>s\<sqsubset> \<rho>"
  assumes "least_rank_p_st (\<lambda>p. \<rho>''n p \<noteq> \<rho> p) p s"
  shows "\<rho>''n p \<subset> \<rho> p"
proof -
  from assms obtain p'' where p''_p:
    "\<rho>''n p'' \<subset> \<rho> p''"
    "(\<forall>p'. s p' = s p'' \<longrightarrow> \<rho>''n p' \<subseteq> \<rho> p')"
    "(\<forall>p'. s p' < s p'' \<longrightarrow> \<rho>''n p' = \<rho> p')"
    unfolding lt_def by auto
  moreover
  from p''_p have "s p'' = s p"
    by (metis (mono_tags, lifting) antisym_conv2 assms(2) least_rank_p_st_def)
  ultimately
  show ?thesis
    by (metis (mono_tags, lifting) assms(2) least_rank_p_st_def psubsetI)
qed

lemma subset_on_least_disagreement:
  assumes "\<rho>''n \<sqsubset>s\<sqsubset> \<rho>"
  assumes "least_rank_p_st (\<lambda>p. \<rho>''n p \<noteq> \<rho> p) p s"
  assumes "s p' = s p"
  shows "\<rho>''n p' \<subseteq> \<rho> p'"
proof -
  from assms obtain p'' where p''_p:
    "\<rho>''n p'' \<subset> \<rho> p''"
    "(\<forall>p'. s p' = s p'' \<longrightarrow> \<rho>''n p' \<subseteq> \<rho> p')"
    "(\<forall>p'. s p' < s p'' \<longrightarrow> \<rho>''n p' = \<rho> p')"
    unfolding lt_def by auto
  moreover
  from p''_p have "s p'' = s p"
    by (metis (mono_tags, lifting) antisym_conv2 assms(2) least_rank_p_st_def)
  ultimately
  show ?thesis
    using assms by metis
qed

lemma equal_below_least_disagreement:
  assumes "\<rho>''n \<sqsubset>s\<sqsubset> \<rho>"
  assumes "least_rank_p_st (\<lambda>p. \<rho>''n p \<noteq> \<rho> p) p s"
  assumes "s p' < s p"
  shows "\<rho>''n p' = \<rho> p'"
proof -
  from assms obtain p'' where p''_p:
    "\<rho>''n p'' \<subset> \<rho> p''"
    "(\<forall>p'. s p' = s p'' \<longrightarrow> \<rho>''n p' \<subseteq> \<rho> p')"
    "(\<forall>p'. s p' < s p'' \<longrightarrow> \<rho>''n p' = \<rho> p')"
    unfolding lt_def by auto
  moreover
  from p''_p have "s p'' = s p"
    by (metis (mono_tags, lifting) antisym_conv2 assms(2) least_rank_p_st_def)
  ultimately
  show ?thesis
    using assms by metis
qed

lemma solution_on_subset_solution_below:
  "(dl ==s== n) \<subseteq> (dl --s-- n)"
  by fastforce

lemma solves_program_mono:
  assumes "dl2 \<subseteq> dl1"
  assumes "\<rho> \<Turnstile>\<^sub>d\<^sub>l dl1"
  shows "\<rho> \<Turnstile>\<^sub>d\<^sub>l dl2"
  by (meson assms in_mono solves_program_def)

lemma solution_on_if_solution_below:
  assumes "\<rho> \<Turnstile>\<^sub>d\<^sub>l (dl --s-- n)"
  shows  "\<rho> \<Turnstile>\<^sub>d\<^sub>l (dl ==s== n)"
  by (meson assms solves_program_mono solution_on_subset_solution_below)

lemma solve_pg_Suc_subset_solution:
  assumes "\<rho> \<Turnstile>\<^sub>d\<^sub>l (dl --s-- Suc n)"
  assumes "(\<rho> \\s\\ n) = solve_pg s dl n"
  shows "solve_pg s dl (Suc n) p \<subseteq> \<rho> p"
  by (meson assms solution_on_if_solution_below solve_pg_Suc_subset)

lemma solve_pg_subset_solution:
  assumes "m > n"
  assumes "\<rho> \<Turnstile>\<^sub>d\<^sub>l (dl --s-- m)"
  assumes "(\<rho> \\s\\ n) = solve_pg s dl n"
  shows "solve_pg s dl (Suc n) p \<subseteq> \<rho> p"
  by (meson Suc_leI assms solve_pg_Suc_subset_solution solves_leq)

lemma below_least_disagreement:
  assumes "least_rank_p_st (\<lambda>p. \<rho>' p \<noteq> \<rho> p) p s"
  assumes "s p' < s p"
  shows "\<rho>' p' = \<rho> p'"
  using assms below_least_rank_p_st by fastforce

definition agree_below_eq :: "('p,'e) pred_val \<Rightarrow> ('p,'e) pred_val \<Rightarrow> nat \<Rightarrow> 'p strat \<Rightarrow> bool"  where
  "agree_below_eq \<rho> \<rho>' n s \<longleftrightarrow> (\<forall>p. s p \<le> n \<longrightarrow> \<rho> p = \<rho>' p)"

definition agree_below :: "('p,'e) pred_val \<Rightarrow> ('p,'e) pred_val \<Rightarrow> nat \<Rightarrow> 'p strat \<Rightarrow> bool"  where
  "agree_below \<rho> \<rho>' n s \<longleftrightarrow> (\<forall>p. s p < n \<longrightarrow> \<rho> p = \<rho>' p)"

definition agree_above :: "('p,'e) pred_val \<Rightarrow> ('p,'e) pred_val \<Rightarrow> nat \<Rightarrow> 'p strat \<Rightarrow> bool"  where
  "agree_above \<rho> \<rho>' n s \<longleftrightarrow> (\<forall>p. s p > n \<longrightarrow> \<rho> p = \<rho>' p)"

definition agree_above_eq :: "('p,'e) pred_val \<Rightarrow> ('p,'e) pred_val \<Rightarrow> nat \<Rightarrow> 'p strat \<Rightarrow> bool" where
  "agree_above_eq \<rho> \<rho>' n s \<longleftrightarrow> (\<forall>p. s p \<ge> n \<longrightarrow> \<rho> p = \<rho>' p)"

lemma agree_below_trans:
  assumes "agree_below_eq \<rho> \<rho>' n s"
  assumes "agree_below_eq \<rho>' \<rho>'' n s"
  shows "agree_below_eq \<rho> \<rho>'' n s"
  using assms unfolding agree_below_eq_def by auto

lemma agree_below_ajskldfjaslkfjdslkf:
  assumes "l \<le> n"
  assumes "agree_below_eq \<rho> \<rho>' n s"
  shows "agree_below_eq \<rho> \<rho>' l s"
  using assms unfolding agree_below_eq_def by auto

lemma agree_below_trans':
  assumes "agree_below_eq \<rho> \<rho>' n s"
  assumes "agree_below_eq \<rho>' \<rho>'' m s"
  assumes "l \<le> n"
  assumes "l \<le> m"
  shows "agree_below_eq \<rho> \<rho>'' l s"
  using assms unfolding agree_below_eq_def by auto

lemma agree_below_eq_least_disagreement:
  assumes "least_rank_p_st (\<lambda>p. \<rho>' p \<noteq> \<rho> p) p s"
  assumes "n < s p"
  shows "agree_below_eq \<rho>' \<rho> n s"
  using agree_below_eq_def assms(1) assms(2) below_least_rank_p_st by fastforce

lemma agree_below_least_disagreement:
  assumes "least_rank_p_st (\<lambda>p. \<rho>' p \<noteq> \<rho> p) p s"
  shows "agree_below \<rho>' \<rho> (s p) s"
  using agree_below_def assms below_least_rank_p_st by fastforce

lemma asjkdfla:
  assumes "agree_below_eq \<rho> \<rho>' n s"
  assumes "agree_above \<rho> \<rho>' n s"
  shows "\<rho> = \<rho>'"
  by (metis agree_above_def agree_below_eq_def assms ext le_eq_less_or_eq nat_le_linear)

lemma asjkdflaasjdfkla:
  assumes "agree_below \<rho> \<rho>' n s"
  assumes "agree_above_eq \<rho> \<rho>' n s"
  shows "\<rho> = \<rho>'"
  by (metis agree_above_eq_def agree_below_def assms ext le_eq_less_or_eq nat_le_linear)
  

lemma asjkdflaasjdfklaasdf:
  assumes "agree_below_eq \<rho> \<rho>' n s"
  assumes "agree_above_eq \<rho> \<rho>' n s"
  shows "\<rho> = \<rho>'"
  by (meson agree_above_def agree_above_eq_def asjkdfla assms less_imp_le_nat)

lemma asdfasdfsafsdfasddddd:
  "agree_below_eq \<rho> (\<rho> \\s\\ n) n s"
  by (simp add: agree_below_eq_def)

lemma asdfasdfsafsdfasdddddffff:
  assumes "m \<le> n"
  shows "agree_below_eq \<rho> (\<rho> \\s\\ n) m s"
  using agree_below_ajskldfjaslkfjdslkf asdfasdfsafsdfasddddd assms by blast

lemma agree_below_eq_solve_pg:
  assumes "l \<le> m"
  assumes "l \<le> n"
  shows "agree_below_eq (solve_pg s dl n) (solve_pg s dl m) l s"
  by (smt (verit, best) agree_below_eq_def assms le_trans solve_pg_agree_above)

lemma solve_pg_below_solution: (* I can look in my notes to improve this one *)
  assumes "\<rho> \<Turnstile>\<^sub>d\<^sub>l (dl --s-- n)"
  shows "(solve_pg s dl n) \<sqsubseteq>s\<sqsubseteq> \<rho>"
  using assms
proof (induction n arbitrary: \<rho>)
  case 0
  then show ?case
    using solve_pg_0_below_solution by blast
next
  case (Suc n)
  define \<rho>''n :: "'a \<Rightarrow> 'b list set" where "\<rho>''n = solve_pg s dl n"
  define \<rho>''n1 :: "'a \<Rightarrow> 'b list set" where "\<rho>''n1 = solve_pg s dl (Suc n)"

  have A: "\<rho>''n \<sqsubseteq>s\<sqsubseteq> \<rho>"
    using Suc.IH Suc.prems \<rho>''n_def solves_Suc by blast

  have B': "agree_below_eq \<rho>''n1 \<rho>''n n s"
    unfolding \<rho>''n_def \<rho>''n1_def using agree_below_eq_solve_pg using le_Suc_eq by blast

  have "\<rho>''n1 \<sqsubseteq>s\<sqsubseteq> \<rho>"
    unfolding lte_def2
  proof
    assume f: "\<rho>''n1 \<noteq> \<rho>"
    then have "\<exists>p. least_rank_p_st (\<lambda>p. \<rho>''n1 p \<noteq> \<rho> p) p s"
      using least_rank_p_st_exists[of "(\<lambda>p. \<rho>''n1 p \<noteq> \<rho> p)"] by force
    then obtain p where p_p: "least_rank_p_st (\<lambda>p. \<rho>''n1 p \<noteq> \<rho> p) p s"
      by blast
    then have dis: "\<rho>''n1 p \<noteq> \<rho> p"
      unfolding least_rank_p_st_def by auto
    from p_p have agg: "agree_below \<rho>''n1 \<rho> (s p) s"
      by (simp add: agree_below_least_disagreement)

    define i where "i = s p"
    have "i < Suc n \<or> Suc n \<le> i"
      by auto
    then show "\<rho>''n1 \<sqsubset>s\<sqsubset> \<rho>"
    proof (rule disjE)
      assume "i < Suc n"
      then have "s p \<le> n"
        unfolding i_def by auto
      then have "\<rho>''n p \<noteq> \<rho> p"
        by (metis B' agree_below_eq_def dis)

      have "\<rho>''n \<sqsubset>s\<sqsubset> \<rho>"
        by (metis A \<open>\<rho>''n p \<noteq> \<rho> p\<close> lte_def)
      moreover
      have "\<forall>p'. \<rho>''n p' \<noteq> \<rho> p' \<longrightarrow> s p \<le> s p'"
        by (metis B' \<open>s p \<le> n\<close> agg agree_below_def agree_below_eq_def le_trans linorder_le_cases linorder_le_less_linear)
      then have "least_rank_p_st (\<lambda>p. \<rho>''n p \<noteq> \<rho> p) p s"
          using \<open>\<rho>''n p \<noteq> \<rho> p\<close> unfolding least_rank_p_st_def by auto
      ultimately
      have "\<rho>''n p \<subset> \<rho> p \<and>
           (\<forall>p'. s p' = s p \<longrightarrow> \<rho>''n(p') \<subseteq> \<rho>(p')) \<and>
           (\<forall>p'. s p' < s p \<longrightarrow> \<rho>''n(p') = \<rho>(p'))"
        using least_disagreement_proper_subset[of \<rho>''n s \<rho> p] subset_on_least_disagreement[of \<rho>''n s \<rho> p] 
          equal_below_least_disagreement[of \<rho>''n s \<rho> p] by metis
      then have "\<rho>''n1 p \<subset> \<rho> p \<and>
           (\<forall>p'. s p' = s p \<longrightarrow> \<rho>''n1(p') \<subseteq> \<rho>(p')) \<and>
           (\<forall>p'. s p' < s p \<longrightarrow> \<rho>''n1(p') = \<rho>(p'))"
        using B' \<open>s p \<le> n\<close> by (simp add: agree_below_eq_def) 
      then show "\<rho>''n1 \<sqsubset>s\<sqsubset> \<rho>"
        unfolding lt_def by auto
    next
      assume "Suc n \<le> i"
      have "\<rho> \<Turnstile>\<^sub>d\<^sub>l (dl --s-- Suc n)"
        using Suc.prems by auto
      moreover
      {
        have "agree_below_eq \<rho>''n \<rho>''n1 n s"
          by (metis B' agree_below_eq_def)
        moreover
        have "agree_below_eq \<rho>''n1 \<rho> n s"
          using \<open>Suc n \<le> i\<close> agree_below_eq_least_disagreement i_def p_p by fastforce
        moreover
        have "agree_below_eq \<rho> (\<rho> \\s\\ n) n s"
          by (simp add: asdfasdfsafsdfasddddd)
        ultimately
        have "agree_below_eq \<rho>''n (\<rho> \\s\\ n) n s"
          using agree_below_trans by metis
        moreover
        have two: "agree_above \<rho>''n (\<rho> \\s\\ n) n s"
          using \<rho>''n_def by (simp add: agree_above_def solve_pg_Suc_empty)
        ultimately
        have "(\<rho> \\s\\ n) = \<rho>''n"
           using asjkdfla by blast
        then have "(\<rho> \\s\\ n) = (solve_pg s dl n)"
          using \<rho>''n_def by metis
      }
      ultimately
      have "\<rho> \<in> {\<rho>'. \<rho>' \<Turnstile>\<^sub>d\<^sub>l (dl --s-- Suc n) \<and> (\<rho>' \\s\\ n) = solve_pg s dl n}"
        by auto
      then have "\<rho>''n1 p \<subseteq> \<rho> p"
        using solve_pg_subset_solution
        using \<rho>''n1_def by fastforce 
      then have "\<rho>''n1 p \<subset> \<rho> p"
        using dis by auto
      moreover
      have "\<forall>p'. s p' = s p \<longrightarrow> \<rho>''n1 p' \<subseteq> \<rho> p'"
        using \<open>\<rho> \<in> {\<rho>'. \<rho>' \<Turnstile>\<^sub>d\<^sub>l (dl --s-- Suc n) \<and> (\<rho>' \s\ n) = solve_pg s dl n}\<close> \<rho>''n1_def solve_pg_subset_solution by fastforce
      moreover
      have "\<forall>p'. s p' < s p \<longrightarrow> \<rho>''n1 p' = \<rho> p'"
        using below_least_rank_p_st p_p by fastforce
      ultimately
      show "\<rho>''n1 \<sqsubset>s\<sqsubset> \<rho>"
        unfolding lt_def by auto
    qed
  qed
  then show ?case
    unfolding \<rho>''n1_def by auto
qed

lemma solve_pg_0_least_solution:
  assumes "strat_wf s dl"
  shows "(solve_pg s dl 0) \<Turnstile>\<^sub>l\<^sub>s\<^sub>t (dl --s-- 0) s"
  using assms least_solution_def solve_pg_0_below_solution solve_pg_0_solves_dl by blast 

lemma solve_pg_Suc_least_solution:
  assumes "strat_wf s dl"
  shows "(solve_pg s dl (Suc n)) \<Turnstile>\<^sub>l\<^sub>s\<^sub>t (dl --s-- (Suc n)) s"
  using assms least_solution_def solve_pg_Suc_solves_dl solve_pg_below_solution by blast (* Man kunne styrke dette til least og ikke kun "slår \<rho>". Nok en god idé tbh. Meh. Du har nogle beviser på papir som nok er bedre *)

lemma solve_pg_least_solution':
  assumes "strat_wf s dl"
  shows "(solve_pg s dl n) \<Turnstile>\<^sub>l\<^sub>s\<^sub>t (dl --s-- n) s"
  using assms solve_pg_0_least_solution solve_pg_Suc_least_solution by (cases n) auto

lemma strata_less_eq_max_strata:
  assumes "finite dl"
  assumes "Cls p ids rhs \<in> dl"
  shows "s p \<le> max_strata s dl"
proof -
  have "s p \<in> {s p | p ids rhs. Cls p ids rhs \<in> dl}"
    using assms(2) by auto
  moreover
  have "{s p | p ids rhs. Cls p ids rhs \<in> dl} = (\<lambda>c. (case c of Cls p ids rhs \<Rightarrow> s p)) ` dl"
    unfolding image_def by (metis (mono_tags, lifting) clause.case the_lhs.cases)
  then have "finite {s p | p ids rhs. Cls p ids rhs \<in> dl}"
    by (simp add: assms(1))
  ultimately
  show ?thesis
    unfolding max_strata_def using Max.coboundedI by auto
qed

lemma finite_max_strata:
  assumes "finite dl"
  shows "(dl --s-- (max_strata s dl)) = dl"
proof (rule; rule)
  fix c
  assume "c \<in> (dl --s-- max_strata s dl)"
  then show "c \<in> dl"
    by auto
next
  fix c
  assume c_in_dl: "c \<in> dl"
  then obtain p ids rhs where c_split: "c = Cls p ids rhs"
    by (cases c) auto
  then have c_in_dl': "Cls p ids rhs \<in> dl"
    using c_in_dl by auto
  then have "s p \<le> max_strata s dl"
    using strata_less_eq_max_strata assms by metis
  then have "Cls p ids rhs \<in> (dl --s-- max_strata s dl)"
    using c_in_dl' by auto
  then show "c \<in> (dl --s-- max_strata s dl)"
    unfolding c_split by auto
qed 

lemma solve_pg_least_solution:
  assumes "finite dl"
  assumes "strat_wf s dl"
  shows "(solve_pg s dl (max_strata s dl)) \<Turnstile>\<^sub>l\<^sub>s\<^sub>t dl s"
proof -
  have "(solve_pg s dl (max_strata s dl)) \<Turnstile>\<^sub>l\<^sub>s\<^sub>t (dl --s-- (max_strata s dl)) s"
    using solve_pg_least_solution' assms by auto
  then show ?thesis
    using finite_max_strata assms by metis
qed


subsubsection \<open>Equality of least and minimal solution\<close>

lemma least_is_minimal:
  assumes "finite dl"
  assumes "strat_wf s dl"
  shows "\<rho> \<Turnstile>\<^sub>l\<^sub>s\<^sub>t dl s \<longleftrightarrow> \<rho> \<Turnstile>\<^sub>m\<^sub>i\<^sub>n dl s"
proof
  assume "\<rho> \<Turnstile>\<^sub>l\<^sub>s\<^sub>t dl s"
  then have \<sigma>_least: "\<rho> \<Turnstile>\<^sub>d\<^sub>l dl" "(\<forall>\<sigma>'. \<sigma>' \<Turnstile>\<^sub>d\<^sub>l dl \<longrightarrow> \<rho> \<sqsubseteq>s\<sqsubseteq> \<sigma>')"
    unfolding least_solution_def by auto
  then have "(\<nexists>\<rho>'. \<rho>' \<Turnstile>\<^sub>d\<^sub>l dl \<and> \<rho>' \<sqsubset>s\<sqsubset> \<rho>)"
    by (metis (full_types) \<open>\<forall>\<rho>'. \<rho>' \<Turnstile>\<^sub>d\<^sub>l dl \<longrightarrow> \<rho> \<sqsubseteq>s\<sqsubseteq> \<rho>'\<close> lt_def lte_def nat_neq_iff psubsetE)
  then show "\<rho> \<Turnstile>\<^sub>m\<^sub>i\<^sub>n dl s"
    unfolding minimal_solution_def using \<sigma>_least by metis
next
  assume min: "\<rho> \<Turnstile>\<^sub>m\<^sub>i\<^sub>n dl s"
  have "\<exists>\<rho>'. \<rho>' \<Turnstile>\<^sub>l\<^sub>s\<^sub>t dl s"
    using solve_pg_least_solution assms by metis
  then show "\<rho> \<Turnstile>\<^sub>l\<^sub>s\<^sub>t dl s"
    by (metis min least_solution_def lte_def minimal_solution_def)
qed


subsubsection \<open>Least solution on lower strata\<close>

lemma below_subset:
  "(dl --s-- n) \<subseteq> dl"
  by auto

lemma finite_below_finite:
  assumes "finite dl"
  shows "finite (dl --s-- n)"
  using assms finite_subset below_subset by metis

lemma downward_least_solution:
  assumes "finite dl"
  assumes "n > m"
  assumes "strat_wf s dl"
  assumes "\<rho> \<Turnstile>\<^sub>l\<^sub>s\<^sub>t (dl --s-- n) s"
  shows "(\<rho> \\s\\ m) \<Turnstile>\<^sub>l\<^sub>s\<^sub>t (dl --s-- m) s"
proof (rule ccontr)
  assume a: "\<not> (\<rho> \\s\\ m) \<Turnstile>\<^sub>l\<^sub>s\<^sub>t (dl --s-- m) s"
  have strrr: "strat_wf s (dl --s-- m)"
    using assms strat_wf_mod_if_strat_wf by auto
  have strrrr: "strat_wf s (dl --s-- n)"
    using assms strat_wf_mod_if_strat_wf by auto
  from a have "\<not> (\<rho> \\s\\ m) \<Turnstile>\<^sub>m\<^sub>i\<^sub>n (dl --s-- m) s"
    using least_is_minimal strrr assms(1) finite_below_finite by metis
  moreover 
  have "(\<rho> \\s\\ m) \<Turnstile>\<^sub>d\<^sub>l (dl --s-- m)"
    using assms downward_mod_solves least_solution_def by blast
  ultimately
  have "(\<exists>\<sigma>'. \<sigma>' \<Turnstile>\<^sub>d\<^sub>l (dl --s-- m) \<and> (\<sigma>' \<sqsubset>s\<sqsubset> (\<rho> \\s\\ m)))"
    unfolding minimal_solution_def by auto
  then obtain \<rho>' where tt: "\<rho>' \<Turnstile>\<^sub>d\<^sub>l (dl --s-- m)" and ttt: "(\<rho>' \<sqsubset>s\<sqsubset> (\<rho> \\s\\ m))"
    by auto
  then have "\<exists>p. \<rho>' p \<subset> (\<rho> \\s\\ m) p \<and> 
                    (\<forall>p'. s p' = s p \<longrightarrow> \<rho>' p' \<subseteq> (\<rho> \\s\\ m) p') \<and> 
                    (\<forall>p'. s p' < s p \<longrightarrow> \<rho>' p' = (\<rho> \\s\\ m) p')"
    unfolding lt_def by auto
  then obtain p where a: "\<rho>' p \<subset> (\<rho> \\s\\ m) p" and
    b:"(\<forall>p'. s p' = s p \<longrightarrow> \<rho>' p' \<subseteq> (\<rho> \\s\\ m) p')" and
    c:"(\<forall>p'. s p' < s p \<longrightarrow> \<rho>' p' = (\<rho> \\s\\ m) p')"
    by auto
  define \<rho>'' where "\<rho>'' == \<lambda>p. (if s p \<le> m then \<rho>' p else UNIV)"

  have "\<rho>'' p \<subset> \<rho> p"
    using a
    by (metis \<rho>''_def empty_iff leD pred_val_mod_strata.simps subsetI) 
  moreover
  have "(\<forall>p'. s p' = s p \<longrightarrow> \<rho>'' p' \<subseteq> \<rho> p')"
    using b
    by (metis \<rho>''_def calculation pred_val_mod_strata.simps top.extremum_strict)
  moreover
  have "(\<forall>p'. s p' < s p \<longrightarrow> \<rho>'' p' = \<rho> p')"
    using \<rho>''_def c calculation(1) by force
  ultimately
  have "(\<rho>'' \<sqsubset>s\<sqsubset> \<rho>)"
    by (metis lt_def)
  moreover
  have "\<rho>'' \<Turnstile>\<^sub>d\<^sub>l (dl --s-- n)"
    unfolding solves_program_def
  proof
    fix c
    assume a: "c \<in> (dl --s-- n)"
    then obtain p ids rhs where c_def: "c = Cls p ids rhs"
      by (cases c) auto

    have "\<rho>'' \<Turnstile>\<^sub>c\<^sub>l\<^sub>s Cls p ids rhs"
      unfolding solves_cls_def
    proof
      fix \<sigma>

      show "\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho>'' \<sigma>"
      proof (cases "s p \<le> m")
        case True
        then have "c \<in> (dl --s-- m)"
          using a c_def by auto
        then have gugu: "\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho>' \<sigma>"
          using tt c_def solves_cls_def solves_program_def by blast
        from gugu show ?thesis
          apply -
          unfolding \<rho>''_def
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
          by (simp add: \<rho>''_def)
      qed
    qed
    then show "\<rho>'' \<Turnstile>\<^sub>c\<^sub>l\<^sub>s c"
      using c_def by blast
  qed
  ultimately
  have "\<not>\<rho> \<Turnstile>\<^sub>m\<^sub>i\<^sub>n (dl --s-- n) s"
    unfolding minimal_solution_def by auto
  then have "\<not>\<rho> \<Turnstile>\<^sub>l\<^sub>s\<^sub>t (dl --s-- n) s" 
    using least_is_minimal strrrr finite_below_finite assms by metis
  then show "False"
    using assms by auto
qed

lemma downward_least_solution2:
  assumes "finite dl"
  assumes "strat_wf s dl"
  assumes "\<rho> \<Turnstile>\<^sub>l\<^sub>s\<^sub>t dl s"
  shows "(\<rho> \\s\\ m) \<Turnstile>\<^sub>l\<^sub>s\<^sub>t (dl --s-- m) s"
proof (rule ccontr)
  assume a: "\<not> (\<rho> \\s\\ m) \<Turnstile>\<^sub>l\<^sub>s\<^sub>t (dl --s-- m) s"
  have strrr: "strat_wf s (dl --s-- m)"
    using assms strat_wf_mod_if_strat_wf by auto
  from a have "\<not> (\<rho> \\s\\ m) \<Turnstile>\<^sub>m\<^sub>i\<^sub>n (dl --s-- m) s"
    using least_is_minimal strrr finite_below_finite assms by metis  
  moreover 
  have "(\<rho> \\s\\ m) \<Turnstile>\<^sub>d\<^sub>l (dl --s-- m)"
    using assms downward_solves least_solution_def by blast
  ultimately
  have "\<exists>\<rho>'. \<rho>' \<Turnstile>\<^sub>d\<^sub>l (dl --s-- m) \<and> \<rho>' \<sqsubset>s\<sqsubset> \<rho> \\s\\ m"
    unfolding minimal_solution_def by auto
  then obtain \<rho>' where tt: "\<rho>' \<Turnstile>\<^sub>d\<^sub>l (dl --s-- m)" and ttt: "(\<rho>' \<sqsubset>s\<sqsubset> (\<rho> \\s\\ m))"
    by auto
  then have "\<exists>p. \<rho>' p \<subset> (\<rho> \\s\\ m) p \<and> 
                    (\<forall>p'. s p' = s p \<longrightarrow> \<rho>' p' \<subseteq> (\<rho> \\s\\ m) p') \<and> 
                    (\<forall>p'. s p' < s p \<longrightarrow> \<rho>' p' = (\<rho> \\s\\ m) p')"
    unfolding lt_def by auto
  then obtain p where a: "\<rho>' p \<subset> (\<rho> \\s\\ m) p" and
    b:"(\<forall>p'. s p' = s p \<longrightarrow> \<rho>' p' \<subseteq> (\<rho> \\s\\ m) p')" and
    c:"(\<forall>p'. s p' < s p \<longrightarrow> \<rho>' p' = (\<rho> \\s\\ m) p')"
    by auto
  define \<rho>'' where "\<rho>'' == \<lambda>p. (if s p \<le> m then \<rho>' p else UNIV)"

  have "\<rho>'' p \<subset> \<rho> p"
    using a
    by (metis \<rho>''_def empty_iff leD pred_val_mod_strata.simps subsetI) 
  moreover
  have "(\<forall>p'. s p' = s p \<longrightarrow> \<rho>'' p' \<subseteq> \<rho> p')"
    using b
    by (metis \<rho>''_def calculation pred_val_mod_strata.simps top.extremum_strict)
  moreover
  have "(\<forall>p'. s p' < s p \<longrightarrow> \<rho>'' p' = \<rho> p')"
    using \<rho>''_def c calculation(1) by force
  ultimately
  have "(\<rho>'' \<sqsubset>s\<sqsubset> \<rho>)"
    by (metis lt_def)
  moreover
  have "\<rho>'' \<Turnstile>\<^sub>d\<^sub>l dl"
    unfolding solves_program_def
  proof
    fix c
    assume a: "c \<in> dl"
    then obtain p ids rhs where c_def: "c = Cls p ids rhs"
      by (cases c) auto

    have "\<rho>'' \<Turnstile>\<^sub>c\<^sub>l\<^sub>s Cls p ids rhs"
      unfolding solves_cls_def
    proof
      fix \<eta>
      show "\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho>'' \<eta>"
      proof (cases "s p \<le> m")
        case True
        then have "c \<in> (dl --s-- m)"
          using a c_def by auto
        then have gugu: "\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho>' \<eta>"
          using tt c_def solves_cls_def solves_program_def by blast
        from gugu show ?thesis
          apply -
          unfolding \<rho>''_def
          apply auto
          subgoal for rh
            apply (cases rh)
               apply fastforce
              apply fastforce
            using \<open>c \<in> dl\<close> c_def dual_order.trans meaning_rh.simps(3) rnk.simps(3) strat_wf_cls.simps strat_wf_def
             apply (smt (verit, ccfv_SIG) assms)
            apply (smt (z3) UNIV_I meaning_rh.simps(4))
            done
          done
      next
        case False
        then show ?thesis
          by (simp add: \<rho>''_def)
      qed
    qed
    then show "\<rho>'' \<Turnstile>\<^sub>c\<^sub>l\<^sub>s c"
      using c_def by blast
  qed
  ultimately
  have "\<not> \<rho> \<Turnstile>\<^sub>m\<^sub>i\<^sub>n dl s"
    unfolding minimal_solution_def by auto
  then have "\<not>\<rho> \<Turnstile>\<^sub>l\<^sub>s\<^sub>t dl s" 
    using least_is_minimal[OF assms(1) assms(2)] by metis
  then show "False"
    using assms by auto
qed

subsection \<open>Negation\<close>

lemma iiiiiii3:
  "\<lbrakk>ids'\<rbrakk>\<^sub>i\<^sub>d\<^sub>s \<sigma>' = \<lbrakk>ids\<rbrakk>\<^sub>i\<^sub>d\<^sub>s \<sigma> \<longleftrightarrow> (ids' \<cdot>\<^sub>v\<^sub>i\<^sub>d\<^sub>s \<sigma>') = (ids \<cdot>\<^sub>v\<^sub>i\<^sub>d\<^sub>s \<sigma>)"
  apply (induction ids' arbitrary: ids)
  apply auto
  apply (metis (no_types, opaque_lifting) eval_id.simps(1) eval_id.simps(2) substv_id.elims)
  apply blast
  apply (smt (verit, del_insts) eval_id.simps(1) eval_id.simps(2) substv_id.elims)
  done

definition agree_var_val :: "'x set \<Rightarrow> ('x, 'e) var_val \<Rightarrow> ('x, 'e) var_val \<Rightarrow> bool " where
  "agree_var_val xs \<sigma> \<sigma>' \<longleftrightarrow> (\<forall>x \<in> xs. \<sigma> x = \<sigma>' x)"

fun vars_ids :: "('a, 'b) identifier list \<Rightarrow> 'a set" where
  "vars_ids ids = \<Union>(vars_id ` set ids)"

fun vars_lh :: "('p,'x,'e) lefthand \<Rightarrow> 'x set" where
  "vars_lh (p,ids) = vars_ids ids"

(* 
  Jeg tror ikke nedenstående er generelt nok.
  For se på følgende eksempel:
    Program:
      p(Y) :- q(Y).
      q(a).

    Antag:
    \<lbrakk>p(X)\<rbrakk> \<rho> [X \<turnstile>> a]

    Vis:
    \<lbrakk>q(X)\<rbrakk> \<rho> [X \<turnstile>> a]
    
  Til dette kan vi ikke bruge lemma'et.
  Så det må være noget med at sige at der skal findes en
  højreside som  


  Her er en "fed" ide:
  Der findes en clause som har en substitution instans og denne clause's rhs er sand under \<sigma>'.
  
  Hvordan beviser jeg at den findes? Jeg "unifier" den med p(ids).
  Lad os kalde den "unifiede" clause c'.
  Så finder jeg de resterende variable i rhs(c') og instantierer dem sådan at højresiden bliver sand.

  Meeen hvad med følgende eksempel:
    Program:
      p(Y) :- q(Y,X).
      q(a,Z).

    Antag:
    \<lbrakk>p(X)\<rbrakk> \<rho> [X \<turnstile>> a]

    Vis:
    \<exists>t. \<lbrakk>q(X,t)\<rbrakk> \<rho> [X \<turnstile>> a]

    Det tror jeg godt min idé kan klare. Så måske er den fin nok.


 *)

(*
fun get_unifier :: "" where
  "get_unifier (p,ids) (p',ids') = undefined"

lemma uuuuuuuuh_aaa2:
  assumes "finite dl"
  assumes "least_solution \<rho> dl s"
  assumes "strat_wf s dl"
  assumes "\<lbrakk>PosRh p ids\<rbrakk>\<^sub>r\<^sub>h \<rho> \<sigma>"
  assumes "\<forall>c \<in> (dl --s-- s p). vars_lh (the_ls c) \<subseteq> vars_rhs (the_rhs c)"
  shows "\<exists>c \<in> (dl --s-- s p). \<exists>\<sigma>'. ((the_lh c) \<cdot>\<^sub>v\<^sub>l\<^sub>h \<sigma>') = ((p,ids) \<cdot>\<^sub>v\<^sub>l\<^sub>h \<sigma>) \<and> (\<lbrakk>the_rhs c\<rbrakk>\<^sub>r\<^sub>h\<^sub>s \<rho> \<sigma>')"
  (* We can strengthen it to say that \<sigma>' and \<sigma> agree on the variables in ids! NO WE CANT DO THAT.... *)
proof (rule ccontr)
  assume "\<not>(\<exists>c \<in> (dl --s-- s p). \<exists>\<sigma>'. ((the_lh c) \<cdot>\<^sub>v\<^sub>l\<^sub>h \<sigma>') = ((p,ids) \<cdot>\<^sub>v\<^sub>l\<^sub>h \<sigma>) \<and> (\<lbrakk>the_rhs c\<rbrakk>\<^sub>r\<^sub>h\<^sub>s \<rho> \<sigma>'))"
  then have a: "\<forall>c \<in> (dl --s-- s p). \<forall>\<sigma>'. ((the_lh c) \<cdot>\<^sub>v\<^sub>l\<^sub>h \<sigma>') = ((p,ids) \<cdot>\<^sub>v\<^sub>l\<^sub>h \<sigma>) \<longrightarrow> \<not>(\<lbrakk>the_rhs c\<rbrakk>\<^sub>r\<^sub>h\<^sub>s \<rho> \<sigma>')"
    by metis

  define \<rho>' where "\<rho>' = (\<rho> \\s\\ s p)"
  define dl' where "dl' = (dl --s-- s p)"

  have \<rho>'_least: "least_solution \<rho>' dl' s"
    using downward_solves[of \<rho> dl s] assms downward_least_solution2 unfolding \<rho>'_def dl'_def by blast
  moreover
  have no_match: "\<forall>c \<in> dl'. \<forall>\<sigma>'. ((the_lh c) \<cdot>\<^sub>v\<^sub>l\<^sub>h \<sigma>') = ((p,ids) \<cdot>\<^sub>v\<^sub>l\<^sub>h \<sigma>) \<longrightarrow> \<not>(\<lbrakk>the_rhs c\<rbrakk>\<^sub>r\<^sub>h\<^sub>s \<rho>' \<sigma>')"
    using a
    unfolding dl'_def \<rho>'_def
    apply auto
    subgoal for idsa rhs \<sigma>'
      apply (erule allE[of _ "Cls p idsa rhs"])
      apply auto
      apply (erule allE[of _ \<sigma>'])
      apply auto
      subgoal for rh
        apply (rule bexI[of _ rh])
        subgoal
          apply auto
          apply (meson assms(3) meaning_mod_m_iff_meaning_rh strat_wf_cls.simps strat_wf_def)
          done
        subgoal
          apply auto
          done
        done
      done
    done

  define \<rho>'' where "\<rho>'' = (\<lambda>p'. if p' = p then \<rho>' p - {\<lbrakk>ids\<rbrakk>\<^sub>i\<^sub>d\<^sub>s \<sigma>} else \<rho>' p')"

  have "\<rho>'' \<Turnstile>\<^sub>d\<^sub>l dl'"
    unfolding solves_program_def
  proof
    fix c
    assume c_dl': "c \<in> dl'"
    obtain p' ids' rhs' where c_split: "c = Cls p' ids' rhs'"
      by (cases c)
    show "\<rho>'' \<Turnstile>\<^sub>c\<^sub>l\<^sub>s c"
      unfolding solves_cls_def
    proof
      fix \<sigma>'
      have "\<lbrakk>Cls p' ids' rhs'\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho>'' \<sigma>'"
        unfolding meaning_cls.simps
      proof
        assume a: "\<lbrakk>rhs'\<rbrakk>\<^sub>r\<^sub>h\<^sub>s \<rho>'' \<sigma>'"
        moreover
        have "\<forall>rh' \<in> set rhs'. s p' \<ge> rnk s rh'"
          using assms(3) below_subset c_dl' c_split dl'_def strat_wf_def by fastforce
        ultimately 
        have rhs'_true: "\<lbrakk>rhs'\<rbrakk>\<^sub>r\<^sub>h\<^sub>s \<rho>' \<sigma>'" (* The only difference is that \<rho>' makes p(ids\<sigma>) true, but \<rho>'' makes it false.
                                      That atom can only occur as a positive literal rhs'.
                                      Therefore some other literal in rhs' must have made rhs' true
                                      and that literal must still be true when we change from \<rho>'' to \<rho>'. *)
          
          apply (induction rhs')
           apply simp
          subgoal for a rhs'
            apply (induction a)
            subgoal
              apply simp
              done
            subgoal
              apply auto
              done
            subgoal for p'' ids''
              unfolding \<rho>''_def
              apply (cases "p'' = p")
              subgoal
                apply auto
                done
              subgoal
                apply auto
                done
              done
            subgoal for p'' ids''
              apply (subgoal_tac "p'' \<noteq> p")
              subgoal
                apply (simp add: \<rho>''_def)
                done
              subgoal
                apply auto
                using c_dl' c_split clause.inject dl'_def dl_program_mod_strata.simps mem_Collect_eq not_less_eq_eq apply auto
                done
              done
            done
          done
        have "\<lbrakk>(p',ids')\<rbrakk>\<^sub>l\<^sub>h \<rho>' \<sigma>'"
          by (metis rhs'_true c_split c_dl' \<rho>'_least clause.inject least_solution_def meaning_cls.elims(2) solves_cls_def solves_program_def)
        moreover
        have "((p', ids') \<cdot>\<^sub>v\<^sub>l\<^sub>h \<sigma>') \<noteq> ((p, ids) \<cdot>\<^sub>v\<^sub>l\<^sub>h \<sigma>)"
          using no_match rhs'_true c_split c_dl' by fastforce
        ultimately
        show "\<lbrakk>(p', ids')\<rbrakk>\<^sub>l\<^sub>h \<rho>'' \<sigma>'"
          using  \<rho>''_def iiiiiii3 by auto
      qed
      then show "\<lbrakk>c\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho>'' \<sigma>'"
        unfolding c_split by auto
    qed
  qed
  moreover
  have "\<rho>'' \<sqsubset>s\<sqsubset> \<rho>'"
  proof -
    have "\<rho>'' p \<subset> \<rho>' p"
      unfolding \<rho>'_def
      using DiffD2 \<open>\<lbrakk>PosRh p ids\<rbrakk>\<^sub>r\<^sub>h \<rho> \<sigma>\<close> \<rho>''_def \<rho>'_def by auto
    moreover
    have "\<forall>p'. s p' = s p \<longrightarrow> \<rho>'' p' \<subseteq> \<rho>' p'"
      unfolding \<rho>'_def
      by (simp add: \<rho>''_def \<rho>'_def)
    moreover
    have "\<forall>p'. s p' < s p \<longrightarrow> \<rho>'' p' = \<rho>' p'"
      using \<rho>''_def by force
    ultimately
    show "\<rho>'' \<sqsubset>s\<sqsubset> \<rho>'"
      unfolding lt_def by auto
  qed
  ultimately
  show "False"
    by (metis assms(1,3) dl'_def finite_below_finite least_is_minimal minimal_solution_def strat_wf_mod_if_strat_wf)
qed
*)

lemma uuuuuuuuh_aaa:
  assumes "finite dl"
  assumes "\<rho> \<Turnstile>\<^sub>l\<^sub>s\<^sub>t dl s"
  assumes "strat_wf s dl"
  assumes "\<lbrakk>PosRh p ids\<rbrakk>\<^sub>r\<^sub>h \<rho> \<sigma>"
  shows "\<exists>c \<in> (dl --s-- s p). \<exists>\<sigma>'. ((the_lh c) \<cdot>\<^sub>v\<^sub>l\<^sub>h \<sigma>') = ((p,ids) \<cdot>\<^sub>v\<^sub>l\<^sub>h \<sigma>) \<and> (\<lbrakk>the_rhs c\<rbrakk>\<^sub>r\<^sub>h\<^sub>s \<rho> \<sigma>')"
  (* We can strengthen it to say that \<sigma>' and \<sigma> agree on the variables in ids! NO WE CANT DO THAT.... *)
proof (rule ccontr)
  assume "\<not>(\<exists>c \<in> (dl --s-- s p). \<exists>\<sigma>'. ((the_lh c) \<cdot>\<^sub>v\<^sub>l\<^sub>h \<sigma>') = ((p,ids) \<cdot>\<^sub>v\<^sub>l\<^sub>h \<sigma>) \<and> (\<lbrakk>the_rhs c\<rbrakk>\<^sub>r\<^sub>h\<^sub>s \<rho> \<sigma>'))"
  then have a: "\<forall>c \<in> (dl --s-- s p). \<forall>\<sigma>'. ((the_lh c) \<cdot>\<^sub>v\<^sub>l\<^sub>h \<sigma>') = ((p,ids) \<cdot>\<^sub>v\<^sub>l\<^sub>h \<sigma>) \<longrightarrow> \<not>(\<lbrakk>the_rhs c\<rbrakk>\<^sub>r\<^sub>h\<^sub>s \<rho> \<sigma>')"
    by metis

  define \<rho>' where "\<rho>' = (\<rho> \\s\\ s p)"
  define dl' where "dl' = (dl --s-- s p)"

  have \<rho>'_least: "\<rho>' \<Turnstile>\<^sub>l\<^sub>s\<^sub>t dl' s"
    using downward_solves[of \<rho> dl s] assms downward_least_solution2 unfolding \<rho>'_def dl'_def by blast
  moreover
  have no_match: "\<forall>c \<in> dl'. \<forall>\<sigma>'. ((the_lh c) \<cdot>\<^sub>v\<^sub>l\<^sub>h \<sigma>') = ((p,ids) \<cdot>\<^sub>v\<^sub>l\<^sub>h \<sigma>) \<longrightarrow> \<not>(\<lbrakk>the_rhs c\<rbrakk>\<^sub>r\<^sub>h\<^sub>s \<rho>' \<sigma>')"
    using a
    unfolding dl'_def \<rho>'_def
    apply auto
    subgoal for idsa rhs \<sigma>'
      apply (erule allE[of _ "Cls p idsa rhs"])
      apply auto
      apply (erule allE[of _ \<sigma>'])
      apply auto
      subgoal for rh
        apply (rule bexI[of _ rh])
        subgoal
          apply auto
          apply (meson assms(3) meaning_mod_m_iff_meaning_rh strat_wf_cls.simps strat_wf_def)
          done
        subgoal
          apply auto
          done
        done
      done
    done

  define \<rho>'' where "\<rho>'' = (\<lambda>p'. if p' = p then \<rho>' p - {\<lbrakk>ids\<rbrakk>\<^sub>i\<^sub>d\<^sub>s \<sigma>} else \<rho>' p')"

  have "\<rho>'' \<Turnstile>\<^sub>d\<^sub>l dl'"
    unfolding solves_program_def
  proof
    fix c
    assume c_dl': "c \<in> dl'"
    obtain p' ids' rhs' where c_split: "c = Cls p' ids' rhs'"
      by (cases c)
    show "\<rho>'' \<Turnstile>\<^sub>c\<^sub>l\<^sub>s c"
      unfolding solves_cls_def
    proof
      fix \<sigma>'
      have "\<lbrakk>Cls p' ids' rhs'\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho>'' \<sigma>'"
        unfolding meaning_cls.simps
      proof
        assume a: "\<lbrakk>rhs'\<rbrakk>\<^sub>r\<^sub>h\<^sub>s \<rho>'' \<sigma>'"
        moreover
        have "\<forall>rh' \<in> set rhs'. s p' \<ge> rnk s rh'"
          using assms(3) below_subset c_dl' c_split dl'_def strat_wf_def by fastforce
        ultimately 
        have rhs'_true: "\<lbrakk>rhs'\<rbrakk>\<^sub>r\<^sub>h\<^sub>s \<rho>' \<sigma>'" (* The only difference is that \<rho>' makes p(ids\<sigma>) true, but \<rho>'' makes it false.
                                      That atom can only occur as a positive literal rhs'.
                                      Therefore some other literal in rhs' must have made rhs' true
                                      and that literal must still be true when we change from \<rho>'' to \<rho>'. *)
          
          apply (induction rhs')
           apply simp
          subgoal for a rhs'
            apply (induction a)
            subgoal
              apply simp
              done
            subgoal
              apply auto
              done
            subgoal for p'' ids''
              unfolding \<rho>''_def
              apply (cases "p'' = p")
              subgoal
                apply auto
                done
              subgoal
                apply auto
                done
              done
            subgoal for p'' ids''
              apply (subgoal_tac "p'' \<noteq> p")
              subgoal
                apply (simp add: \<rho>''_def)
                done
              subgoal
                apply auto
                using c_dl' c_split clause.inject dl'_def dl_program_mod_strata.simps mem_Collect_eq not_less_eq_eq apply auto
                done
              done
            done
          done
        have "\<lbrakk>(p',ids')\<rbrakk>\<^sub>l\<^sub>h \<rho>' \<sigma>'"
          by (metis rhs'_true c_split c_dl' \<rho>'_least clause.inject least_solution_def meaning_cls.elims(2) solves_cls_def solves_program_def)
        moreover
        have "((p', ids') \<cdot>\<^sub>v\<^sub>l\<^sub>h \<sigma>') \<noteq> ((p, ids) \<cdot>\<^sub>v\<^sub>l\<^sub>h \<sigma>)"
          using no_match rhs'_true c_split c_dl' by fastforce
        ultimately
        show "\<lbrakk>(p', ids')\<rbrakk>\<^sub>l\<^sub>h \<rho>'' \<sigma>'"
          using  \<rho>''_def iiiiiii3 by auto
      qed
      then show "\<lbrakk>c\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho>'' \<sigma>'"
        unfolding c_split by auto
    qed
  qed
  moreover
  have "\<rho>'' \<sqsubset>s\<sqsubset> \<rho>'"
  proof -
    have "\<rho>'' p \<subset> \<rho>' p"
      unfolding \<rho>'_def
      using DiffD2 \<open>\<lbrakk>PosRh p ids\<rbrakk>\<^sub>r\<^sub>h \<rho> \<sigma>\<close> \<rho>''_def \<rho>'_def by auto
    moreover
    have "\<forall>p'. s p' = s p \<longrightarrow> \<rho>'' p' \<subseteq> \<rho>' p'"
      unfolding \<rho>'_def
      by (simp add: \<rho>''_def \<rho>'_def)
    moreover
    have "\<forall>p'. s p' < s p \<longrightarrow> \<rho>'' p' = \<rho>' p'"
      using \<rho>''_def by force
    ultimately
    show "\<rho>'' \<sqsubset>s\<sqsubset> \<rho>'"
      unfolding lt_def by auto
  qed
  ultimately
  show "False"
    by (metis assms(1,3) dl'_def finite_below_finite least_is_minimal minimal_solution_def strat_wf_mod_if_strat_wf)
qed

lemma meaning_neg_rh:
  assumes "finite dl"
  assumes "\<rho> \<Turnstile>\<^sub>l\<^sub>s\<^sub>t dl s"
  assumes "strat_wf s dl"
  assumes "\<forall>c \<in> (dl --s-- s p). \<forall>\<sigma>'. ((the_lh c) \<cdot>\<^sub>v\<^sub>l\<^sub>h \<sigma>') = ((p,ids) \<cdot>\<^sub>v\<^sub>l\<^sub>h \<sigma>) \<longrightarrow> \<not>(\<lbrakk>the_rhs c\<rbrakk>\<^sub>r\<^sub>h\<^sub>s \<rho> \<sigma>')"
  shows "\<lbrakk>\<^bold>\<not> p ids\<rbrakk>\<^sub>r\<^sub>h \<rho> \<sigma>"
  by (metis assms meaning_rh.simps(3,4) uuuuuuuuh_aaa)

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
  the_RD
  | the_VAR
(* Cst\<^sub>R\<^sub>D\<^sub>N *)
abbreviation Cst\<^sub>R\<^sub>D\<^sub>N :: "'n \<Rightarrow> (RD_var, ('n, 'v) RD_elem) identifier" where
  "Cst\<^sub>R\<^sub>D\<^sub>N q == Cst (RD_Node q)"

fun Cst\<^sub>R\<^sub>D\<^sub>N_Q :: "'n option \<Rightarrow> (RD_var, ('n, 'v) RD_elem) identifier" where
  "Cst\<^sub>R\<^sub>D\<^sub>N_Q (Some q) = Cst (RD_Node q)"
| "Cst\<^sub>R\<^sub>D\<^sub>N_Q None = Cst Questionmark"

abbreviation Cst\<^sub>R\<^sub>D\<^sub>V :: "'v \<Rightarrow> (RD_var, ('n, 'v) RD_elem) identifier" where
  "Cst\<^sub>R\<^sub>D\<^sub>V v == Cst (RD_Var v)"

abbreviation RD_Cls :: "(RD_var, ('n, 'v) RD_elem) identifier list \<Rightarrow> (RD_pred, RD_var, ('n, 'v) RD_elem) righthand list \<Rightarrow> (RD_pred, RD_var, ('n, 'v) RD_elem) clause" ("RD\<langle>_\<rangle> :- _ .") where 
  "RD\<langle>args\<rangle> :- ls. \<equiv> Cls the_RD args ls"

abbreviation VAR_Cls :: "'v \<Rightarrow> (RD_pred, RD_var, ('n, 'v) RD_elem) clause" ("VAR\<langle>_\<rangle> :-.") where
  "VAR\<langle>x\<rangle> :-. == Cls the_VAR [Cst\<^sub>R\<^sub>D\<^sub>V x] []"

abbreviation RD_Fact :: "(RD_var, ('n, 'v) RD_elem) identifier list \<Rightarrow> (RD_pred, RD_var, ('n, 'v) RD_elem) fact" ("RD\<langle>_\<rangle>.") where 
  "RD\<langle>args\<rangle>. \<equiv> (the_RD, args)"

abbreviation VAR_Fact :: "'v \<Rightarrow> (RD_pred, RD_var, ('n, 'v) RD_elem) fact" ("VAR\<langle>_\<rangle>.") where 
  "VAR\<langle>x\<rangle>. \<equiv> (the_VAR, [Cst\<^sub>R\<^sub>D\<^sub>V x])"


abbreviation "RD == PosRh the_RD"
abbreviation "VAR == PosRh the_VAR"

abbreviation \<u> :: "(RD_var, 'a) identifier" where
  "\<u> == Var the_\<u>"

abbreviation \<v> :: "(RD_var, 'a) identifier" where
  "\<v> == Var the_\<v>"

abbreviation \<w> :: "(RD_var, 'a) identifier" where
  "\<w> == Var the_\<w>"

fun ana_edge :: "('n, 'v) edge \<Rightarrow> (RD_pred, RD_var, ('n,'v) RD_elem) clause set" where
  "ana_edge (q\<^sub>o, x ::= a, q\<^sub>s) =
     {
        RD\<langle>[Cst\<^sub>R\<^sub>D\<^sub>N q\<^sub>s, \<u>, \<v>, \<w>]\<rangle> :-
          [
            RD[Cst\<^sub>R\<^sub>D\<^sub>N q\<^sub>o, \<u>, \<v>, \<w>],
            \<u> \<^bold>\<noteq> (Cst\<^sub>R\<^sub>D\<^sub>V x)
          ].
        ,
        RD\<langle>[Cst\<^sub>R\<^sub>D\<^sub>N q\<^sub>s, Cst\<^sub>R\<^sub>D\<^sub>V x, Cst\<^sub>R\<^sub>D\<^sub>N q\<^sub>o, Cst\<^sub>R\<^sub>D\<^sub>N q\<^sub>s]\<rangle> :- [].
     }"
| "ana_edge (q\<^sub>o, Bool b, q\<^sub>s) =
     {
       RD\<langle>[Cst\<^sub>R\<^sub>D\<^sub>N q\<^sub>s, \<u>, \<v>, \<w>]\<rangle> :-
         [
           RD[Cst\<^sub>R\<^sub>D\<^sub>N q\<^sub>o, \<u>, \<v>, \<w>]
         ].
     }"
| "ana_edge (q\<^sub>o, Skip, q\<^sub>s) =
     {
       RD\<langle>[Cst\<^sub>R\<^sub>D\<^sub>N q\<^sub>s, \<u>, \<v>, \<w>]\<rangle> :-
         [
           RD[Cst\<^sub>R\<^sub>D\<^sub>N q\<^sub>o, \<u>, \<v>, \<w>]
         ].
     }"

definition ana_entry_node :: "'n \<Rightarrow> (RD_pred, RD_var, ('n,'v) RD_elem) clause set" where
  "ana_entry_node start = 
     {
       RD\<langle>[Cst\<^sub>R\<^sub>D\<^sub>N start, \<u>, Cst Questionmark, Cst\<^sub>R\<^sub>D\<^sub>N start]\<rangle> :-
         [
           VAR[\<u>]
         ].
     }"


fun ana_RD :: "('n, 'v) program_graph \<Rightarrow> (RD_pred, RD_var, ('n,'v) RD_elem) clause set" where
  "ana_RD (es,start,end) = \<Union>(ana_edge ` es) \<union> ana_entry_node start"

definition var_contraints :: "(RD_pred, RD_var, ('n,'v) RD_elem) clause set" where
  "var_contraints = VAR_Cls ` UNIV"

type_synonym ('n,'v) quadruple = "'n *'v * 'n option * 'n"

fun summarizes_RD :: "(RD_pred,('n,'v) RD_elem) pred_val \<Rightarrow> ('n,'v) program_graph \<Rightarrow> bool" where
  "summarizes_RD \<rho> (es, start, end) =
    (\<forall>\<pi> x q1 q2.
       \<pi> \<in> LTS.path_with_word es \<longrightarrow>
       LTS.get_start \<pi> = start \<longrightarrow>
       (x, q1, q2) \<in> def_path \<pi> start \<longrightarrow> 
       \<rho> \<Turnstile>\<^sub>f RD\<langle>[Cst\<^sub>R\<^sub>D\<^sub>N (LTS.get_end \<pi>), Cst\<^sub>R\<^sub>D\<^sub>V x, Cst\<^sub>R\<^sub>D\<^sub>N_Q q1, Cst\<^sub>R\<^sub>D\<^sub>N q2]\<rangle>.)"

lemma def_var_x: "fst (def_var ts x start) = x"
  unfolding def_var_def by (simp add: case_prod_beta triple_of_def)

lemma last_def_transition:
  assumes "length ss = length w"
  assumes "x \<in> def_action \<alpha>"
  assumes "(x, q1, q2) \<in> def_path (ss @ [s, s'], w @ [\<alpha>]) start"
  shows "Some s = q1 \<and> s' = q2"
proof -
  obtain y where y_p: "(x, q1, q2) = def_var (transition_list (ss @ [s], w) @ [(s, \<alpha>, s')]) y start"
    by (metis (no_types, lifting) assms(1) assms(3) def_path_def imageE transition_list_reversed_simp)
  show ?thesis
  proof (cases "y = x")
    case True
    then show ?thesis 
      using assms y_p unfolding def_var_def triple_of_def by auto
  next
    case False
    then show ?thesis
      by (metis y_p def_var_x fst_conv)
  qed
qed

lemma not_last_def_transition:
  assumes "length ss = length w"
  assumes "x \<notin> def_action \<alpha>"
  assumes "(x, q1, q2) \<in> def_path (ss @ [s, s'], w @ [\<alpha>]) start"
  shows "(x, q1, q2) \<in> def_path (ss @ [s], w) start"
proof -
  obtain y where y_p: "(x, q1, q2) = def_var (transition_list (ss @ [s], w) @ [(s, \<alpha>, s')]) y start"
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
  assumes "\<rho> \<Turnstile>\<^sub>d\<^sub>l (var_contraints \<union> ana_RD (es, start, end))"
  assumes "LTS.get_start (ss,w) = start"
  assumes "(x,q1,q2) \<in> def_path (ss,w) start"
  shows "\<rho> \<Turnstile>\<^sub>f RD\<langle>[Cst\<^sub>R\<^sub>D\<^sub>N (LTS.get_end (ss, w)), Cst\<^sub>R\<^sub>D\<^sub>V x, Cst\<^sub>R\<^sub>D\<^sub>N_Q q1, Cst\<^sub>R\<^sub>D\<^sub>N q2]\<rangle>."
  using assms 
proof (induction rule: LTS.path_with_word_induct_reverse[OF assms(1)])
  case (1 s)
  have "VAR\<langle>x\<rangle> :-. \<in> var_contraints"
    unfolding var_contraints_def by auto
  from assms(2) this have "\<rho> \<Turnstile>\<^sub>c\<^sub>l\<^sub>s VAR\<langle>x\<rangle> :-."
    unfolding solves_program_def by auto  
  then have "\<forall>y. \<lbrakk>(VAR\<langle>x\<rangle> :-.)\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho> y"
    unfolding solves_cls_def by auto
  then have x_sat: "[RD_Var x] \<in> \<rho> the_VAR"
    by auto

  have "RD\<langle>[Cst\<^sub>R\<^sub>D\<^sub>N start, \<u>, Cst Questionmark, Cst\<^sub>R\<^sub>D\<^sub>N start]\<rangle> :-
         [
           VAR[\<u>]
         ]. \<in> ana_RD (es, start, end)"
    by (simp add: ana_entry_node_def)
  then have "\<rho> \<Turnstile>\<^sub>c\<^sub>l\<^sub>s RD\<langle>[Cst\<^sub>R\<^sub>D\<^sub>N start, \<u>, Cst Questionmark, Cst\<^sub>R\<^sub>D\<^sub>N start]\<rangle> :- [VAR [\<u>]] ."
    using assms(2) unfolding solves_program_def by auto 
  then have "\<forall>\<sigma>. \<lbrakk>RD\<langle>[Cst\<^sub>R\<^sub>D\<^sub>N start, \<u>, Cst Questionmark, Cst\<^sub>R\<^sub>D\<^sub>N start]\<rangle> :- [VAR [\<u>]] .\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho> \<sigma>"
    unfolding solves_cls_def by metis
  then have "\<lbrakk>RD\<langle>[Cst\<^sub>R\<^sub>D\<^sub>N start, \<u>, Cst Questionmark, Cst\<^sub>R\<^sub>D\<^sub>N start]\<rangle> :- [VAR [\<u>]] .\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho> (\<lambda>v. RD_Var x)"
    by presburger
  then have "[RD_Var x] \<in> \<rho> the_VAR \<longrightarrow> [RD_Node start, RD_Var x, Questionmark, RD_Node start] \<in> \<rho> the_RD"
    by simp
  then have "[RD_Node start, RD_Var x, Questionmark, RD_Node start] \<in> \<rho> the_RD"
    using x_sat by auto

  from this 1 show ?case
    unfolding LTS.LTS.get_end_def def_path_def def_var_def LTS.get_start_def by auto
next
  case (2 ss s w \<alpha> s')
  from 2(1) have len: "length ss = length w"
    using LTS.path_with_word_length by force
  show ?case 
  proof(cases "x \<in> def_action \<alpha>")
    case True
    then have sq: "Some s = q1 \<and> s' = q2" using 2(7)
      using last_def_transition[of ss w x \<alpha> q1 q2 s s'] len by auto
    from True have "\<exists>e. (s,x ::= e,s') \<in> es"
      using "2.hyps"(2) by (cases \<alpha>) auto
    then have "RD\<langle>[Cst\<^sub>R\<^sub>D\<^sub>N q2, Cst\<^sub>R\<^sub>D\<^sub>V x, Cst\<^sub>R\<^sub>D\<^sub>N_Q q1, Cst\<^sub>R\<^sub>D\<^sub>N q2]\<rangle> :- []. \<in> ana_RD (es, start, end)"
      using True ana_RD.simps sq by fastforce
    then have "\<rho> \<Turnstile>\<^sub>c\<^sub>l\<^sub>s RD\<langle>[Cst\<^sub>R\<^sub>D\<^sub>N q2, Cst\<^sub>R\<^sub>D\<^sub>V x, Cst\<^sub>R\<^sub>D\<^sub>N_Q q1, Cst\<^sub>R\<^sub>D\<^sub>N q2]\<rangle> :- [] ."
      using 2(5) unfolding solves_program_def by auto
    then have "\<rho> \<Turnstile>\<^sub>f RD\<langle>[Cst\<^sub>R\<^sub>D\<^sub>N q2, Cst\<^sub>R\<^sub>D\<^sub>V x, Cst\<^sub>R\<^sub>D\<^sub>N_Q q1, Cst\<^sub>R\<^sub>D\<^sub>N q2]\<rangle>."
      using solves_fact_fact by metis 
    then show ?thesis
      by (simp add: LTS.get_end_def sq)
  next
    case False
    then have x_is_def: "(x, q1, q2) \<in> def_path (ss @ [s], w) start" using 2(7)
      using not_last_def_transition len by force
    then have "\<rho> \<Turnstile>\<^sub>f RD\<langle>[Cst\<^sub>R\<^sub>D\<^sub>N (LTS.get_end (ss @ [s], w)), Cst\<^sub>R\<^sub>D\<^sub>V x, Cst\<^sub>R\<^sub>D\<^sub>N_Q q1, Cst\<^sub>R\<^sub>D\<^sub>N q2]\<rangle>."
    proof -
      have "(ss @ [s], w) \<in> LTS.path_with_word es"
        using 2(1) by auto
      moreover
      have "\<rho> \<Turnstile>\<^sub>d\<^sub>l (var_contraints \<union> ana_RD (es, start, end))"
        using 2(5) by auto
      moreover
      have "LTS.get_start (ss @ [s], w) = start"
        using 2(6)
        by (metis append_self_conv2 fst_conv LTS.get_start_def hd_append2 list.sel(1)) 
      moreover
      have "(x, q1, q2) \<in> def_path (ss @ [s], w) start"
        using x_is_def by auto
      ultimately
      show "\<rho> \<Turnstile>\<^sub>f RD\<langle>[Cst\<^sub>R\<^sub>D\<^sub>N (LTS.get_end (ss @ [s], w)), Cst\<^sub>R\<^sub>D\<^sub>V x, Cst\<^sub>R\<^sub>D\<^sub>N_Q q1, Cst\<^sub>R\<^sub>D\<^sub>N q2]\<rangle>."
        using 2(3) by auto
    qed
    then have ind: "\<rho> \<Turnstile>\<^sub>f RD\<langle>[Cst\<^sub>R\<^sub>D\<^sub>N s, Cst\<^sub>R\<^sub>D\<^sub>V x, Cst\<^sub>R\<^sub>D\<^sub>N_Q q1, Cst\<^sub>R\<^sub>D\<^sub>N q2]\<rangle>."
      by (simp add: LTS.get_end_def)
    define \<mu> where "\<mu> = undefined(the_\<u> := Cst\<^sub>R\<^sub>D\<^sub>V x, the_\<v> := Cst\<^sub>R\<^sub>D\<^sub>N_Q q1, the_\<w> := Cst\<^sub>R\<^sub>D\<^sub>N q2)"
    show ?thesis
    proof (cases \<alpha>)
      case (Asg y e)
      have xy: "x \<noteq> y"
        using False Asg by auto
      then have xy': "\<rho> \<Turnstile>\<^sub>r\<^sub>h (Cst\<^sub>R\<^sub>D\<^sub>V x \<^bold>\<noteq> Cst\<^sub>R\<^sub>D\<^sub>V y)"
        by auto
      have "(s, y ::= e, s') \<in> es"
        using "2.hyps"(2) Asg by auto
      then have "RD\<langle>[Cst\<^sub>R\<^sub>D\<^sub>N s', \<u>, \<v>, \<w>]\<rangle> :-
          [
            RD[Cst\<^sub>R\<^sub>D\<^sub>N s, \<u>, \<v>, \<w>],
            \<u> \<^bold>\<noteq> (Cst\<^sub>R\<^sub>D\<^sub>V y)
          ]. \<in> ana_RD (es,start,end)"
        unfolding ana_RD.simps by force
      from this False have "\<rho> \<Turnstile>\<^sub>c\<^sub>l\<^sub>s RD\<langle>[Cst\<^sub>R\<^sub>D\<^sub>N s', \<u>, \<v>, \<w>]\<rangle> :- [RD [Cst\<^sub>R\<^sub>D\<^sub>N s, \<u>, \<v>, \<w>], \<u> \<^bold>\<noteq> Cst\<^sub>R\<^sub>D\<^sub>V y] ."
        by (meson "2.prems"(2) UnCI solves_program_def)
      moreover have "(RD\<langle>[Cst\<^sub>R\<^sub>D\<^sub>N s', \<u>, \<v>, \<w>]\<rangle> :-
          [
            RD[Cst\<^sub>R\<^sub>D\<^sub>N s, \<u>, \<v>, \<w>],
            \<u> \<^bold>\<noteq> (Cst\<^sub>R\<^sub>D\<^sub>V y)
          ].) \<cdot>\<^sub>c\<^sub>l\<^sub>s \<mu> = RD\<langle>[Cst\<^sub>R\<^sub>D\<^sub>N s', Cst\<^sub>R\<^sub>D\<^sub>V x, Cst\<^sub>R\<^sub>D\<^sub>N_Q q1, Cst\<^sub>R\<^sub>D\<^sub>N q2]\<rangle> :- [RD [Cst\<^sub>R\<^sub>D\<^sub>N s,  Cst\<^sub>R\<^sub>D\<^sub>V x, Cst\<^sub>R\<^sub>D\<^sub>N_Q q1, Cst\<^sub>R\<^sub>D\<^sub>N q2], Cst\<^sub>R\<^sub>D\<^sub>V x \<^bold>\<noteq> Cst\<^sub>R\<^sub>D\<^sub>V y] ."
        unfolding \<mu>_def by auto
      ultimately
      have "\<rho> \<Turnstile>\<^sub>c\<^sub>l\<^sub>s RD\<langle>[Cst\<^sub>R\<^sub>D\<^sub>N s', Cst\<^sub>R\<^sub>D\<^sub>V x, Cst\<^sub>R\<^sub>D\<^sub>N_Q q1, Cst\<^sub>R\<^sub>D\<^sub>N q2]\<rangle>
                    :- [RD [Cst\<^sub>R\<^sub>D\<^sub>N s, Cst\<^sub>R\<^sub>D\<^sub>V x, Cst\<^sub>R\<^sub>D\<^sub>N_Q q1, Cst\<^sub>R\<^sub>D\<^sub>N q2], Cst\<^sub>R\<^sub>D\<^sub>V x \<^bold>\<noteq> Cst\<^sub>R\<^sub>D\<^sub>V y] ."
        unfolding solves_cls_def by (metis substitution_lemma_cls)
      then have "\<rho> \<Turnstile>\<^sub>c\<^sub>l\<^sub>s RD\<langle>[Cst\<^sub>R\<^sub>D\<^sub>N s', Cst\<^sub>R\<^sub>D\<^sub>V x, Cst\<^sub>R\<^sub>D\<^sub>N_Q q1, Cst\<^sub>R\<^sub>D\<^sub>N q2]\<rangle> 
                         :- [RD [Cst\<^sub>R\<^sub>D\<^sub>N s, Cst\<^sub>R\<^sub>D\<^sub>V x, Cst\<^sub>R\<^sub>D\<^sub>N_Q q1, Cst\<^sub>R\<^sub>D\<^sub>N q2]] ."
        using xy' by (simp add: resolution_last_from_cls_rh_to_cls)
      then have "\<rho> \<Turnstile>\<^sub>c\<^sub>l\<^sub>s RD\<langle>[Cst\<^sub>R\<^sub>D\<^sub>N s', Cst\<^sub>R\<^sub>D\<^sub>V x, Cst\<^sub>R\<^sub>D\<^sub>N_Q q1, Cst\<^sub>R\<^sub>D\<^sub>N q2]\<rangle> :- [] ."
        using ind using resolution_last_from_cls_fact_to_cls[of \<rho> the_RD ] by (metis append.left_neutral) 
      then have "\<rho> \<Turnstile>\<^sub>f RD\<langle>[Cst\<^sub>R\<^sub>D\<^sub>N s', Cst\<^sub>R\<^sub>D\<^sub>V x, Cst\<^sub>R\<^sub>D\<^sub>N_Q q1, Cst\<^sub>R\<^sub>D\<^sub>N q2]\<rangle>."
        using solves_fact_fact by metis
      then show ?thesis
        by (simp add: LTS.get_end_def)
    next
      case (Bool b)
      have "(s, Bool b, s') \<in> es"
        using "2.hyps"(2) Bool by auto
      then have "RD\<langle>[Cst\<^sub>R\<^sub>D\<^sub>N s', \<u>, \<v>, \<w>]\<rangle> :-
         [
           RD[Cst\<^sub>R\<^sub>D\<^sub>N s, \<u>, \<v>, \<w>]
         ]. \<in> ana_RD (es,start,end)"
        unfolding ana_RD.simps by force
      then have "\<rho> \<Turnstile>\<^sub>c\<^sub>l\<^sub>s RD\<langle>[Cst\<^sub>R\<^sub>D\<^sub>N s', \<u>, \<v>, \<w>]\<rangle> :- [RD [Cst\<^sub>R\<^sub>D\<^sub>N s, \<u>, \<v>, \<w>]] ."
        by (meson "2.prems"(2) UnCI solves_program_def)
      moreover have "(RD\<langle>[Cst\<^sub>R\<^sub>D\<^sub>N s', \<u>, \<v>, \<w>]\<rangle> :- [RD[Cst\<^sub>R\<^sub>D\<^sub>N s, \<u>, \<v>, \<w>]].) \<cdot>\<^sub>c\<^sub>l\<^sub>s \<mu> =
                     RD\<langle>[Cst\<^sub>R\<^sub>D\<^sub>N s', Cst\<^sub>R\<^sub>D\<^sub>V x, Cst\<^sub>R\<^sub>D\<^sub>N_Q q1, Cst\<^sub>R\<^sub>D\<^sub>N q2]\<rangle> :- [RD[Cst\<^sub>R\<^sub>D\<^sub>N s, Cst\<^sub>R\<^sub>D\<^sub>V x, Cst\<^sub>R\<^sub>D\<^sub>N_Q q1, Cst\<^sub>R\<^sub>D\<^sub>N q2]]."
        unfolding \<mu>_def by auto
      ultimately have "\<rho> \<Turnstile>\<^sub>c\<^sub>l\<^sub>s RD\<langle>[Cst\<^sub>R\<^sub>D\<^sub>N s', Cst\<^sub>R\<^sub>D\<^sub>V x, Cst\<^sub>R\<^sub>D\<^sub>N_Q q1, Cst\<^sub>R\<^sub>D\<^sub>N q2]\<rangle> 
                               :- [RD [Cst\<^sub>R\<^sub>D\<^sub>N s, Cst\<^sub>R\<^sub>D\<^sub>V x, Cst\<^sub>R\<^sub>D\<^sub>N_Q q1, Cst\<^sub>R\<^sub>D\<^sub>N q2]] ."
        by (metis substitution_rule)
      then have "\<rho> \<Turnstile>\<^sub>f RD\<langle>[Cst\<^sub>R\<^sub>D\<^sub>N s', Cst\<^sub>R\<^sub>D\<^sub>V x, Cst\<^sub>R\<^sub>D\<^sub>N_Q q1, Cst\<^sub>R\<^sub>D\<^sub>N q2]\<rangle>."
        using ind
        by (meson resolution_only)
      then show ?thesis
        by (simp add: LTS.get_end_def)
    next
      case Skip
      have "(s, Skip, s') \<in> es"
        using "2.hyps"(2) Skip by auto
      then have "RD\<langle>[Cst\<^sub>R\<^sub>D\<^sub>N s', \<u>, \<v>, \<w>]\<rangle> :-
         [
           RD[Cst\<^sub>R\<^sub>D\<^sub>N s, \<u>, \<v>, \<w>]
         ]. \<in> ana_RD (es,start,end)"
        unfolding ana_RD.simps by force
      then have "\<rho> \<Turnstile>\<^sub>c\<^sub>l\<^sub>s RD\<langle>[Cst\<^sub>R\<^sub>D\<^sub>N s', \<u>, \<v>, \<w>]\<rangle> :- [RD [Cst\<^sub>R\<^sub>D\<^sub>N s, \<u>, \<v>, \<w>]] ."
        by (meson "2.prems"(2) UnCI solves_program_def)
      moreover
      have "(RD\<langle>[Cst\<^sub>R\<^sub>D\<^sub>N s', \<u>, \<v>, \<w>]\<rangle> :- [RD [Cst\<^sub>R\<^sub>D\<^sub>N s, \<u>, \<v>, \<w>]] .) \<cdot>\<^sub>c\<^sub>l\<^sub>s \<mu> =
            RD\<langle>[Cst\<^sub>R\<^sub>D\<^sub>N s', Cst\<^sub>R\<^sub>D\<^sub>V x, Cst\<^sub>R\<^sub>D\<^sub>N_Q q1, Cst\<^sub>R\<^sub>D\<^sub>N q2]\<rangle>  :- [RD [Cst\<^sub>R\<^sub>D\<^sub>N s, Cst\<^sub>R\<^sub>D\<^sub>V x, Cst\<^sub>R\<^sub>D\<^sub>N_Q q1, Cst\<^sub>R\<^sub>D\<^sub>N q2]]."
        unfolding \<mu>_def by auto
      ultimately 
      have "\<rho> \<Turnstile>\<^sub>c\<^sub>l\<^sub>s RD\<langle>[Cst\<^sub>R\<^sub>D\<^sub>N s', Cst\<^sub>R\<^sub>D\<^sub>V x, Cst\<^sub>R\<^sub>D\<^sub>N_Q q1, Cst\<^sub>R\<^sub>D\<^sub>N q2]\<rangle> 
                    :- [RD [Cst\<^sub>R\<^sub>D\<^sub>N s, Cst\<^sub>R\<^sub>D\<^sub>V x, Cst\<^sub>R\<^sub>D\<^sub>N_Q q1, Cst\<^sub>R\<^sub>D\<^sub>N q2]] ."
        by (metis substitution_rule)
      from resolution_only_from_cls_fact_to_fact[OF this ind] have "\<rho> \<Turnstile>\<^sub>f RD\<langle>[Cst\<^sub>R\<^sub>D\<^sub>N s', Cst\<^sub>R\<^sub>D\<^sub>V x, Cst\<^sub>R\<^sub>D\<^sub>N_Q q1, Cst\<^sub>R\<^sub>D\<^sub>N q2]\<rangle>."
        .
      then show ?thesis
        by (simp add: LTS.get_end_def)
    qed
  qed
qed

lemma RD_sound:
  assumes "\<rho> \<Turnstile>\<^sub>d\<^sub>l (var_contraints \<union> ana_RD pg)"
  shows "summarizes_RD \<rho> pg"
  using assms RD_sound' by (cases pg) force 


section \<open>Bitvector framework\<close>

datatype BV_pred =
  the_BV
  | the_kill
  | the_gen
  | the_CBV
  | the_init

datatype BV_var =
  the_\<uu>

abbreviation "BV == PosRh the_BV"
abbreviation "CBV == PosRh the_CBV"
abbreviation NegRh_BV ("\<^bold>\<not>BV") where
  "\<^bold>\<not>BV \<equiv> NegRh the_BV"
abbreviation "kill == PosRh the_kill"
abbreviation NegRh_kill ("\<^bold>\<not>kill") where
  "\<^bold>\<not>kill \<equiv> NegRh the_kill"
abbreviation "gen == PosRh the_gen"
abbreviation "init == PosRh the_init"

fun s_BV :: "BV_pred \<Rightarrow> nat" where 
  "s_BV the_kill = 0"
| "s_BV the_gen = 0"
| "s_BV the_init = 0"
| "s_BV the_BV = 1"
| "s_BV the_CBV = 2"

datatype ('n,'v,'elem) BV_elem =
  Node (the_node: 'n)
  | is_bv_elem: Elem (the_bv_elem: 'elem)
  | BV_Action "'v action"

abbreviation BV_Cls :: "(BV_var, ('n,'v,'elem) BV_elem) identifier list \<Rightarrow> (BV_pred, BV_var, ('n,'v,'elem) BV_elem) righthand list \<Rightarrow> (BV_pred, BV_var, ('n,'v,'elem) BV_elem) clause" ("BV\<langle>_\<rangle> :- _ .") where 
   "BV\<langle>args\<rangle> :- ls. \<equiv> Cls the_BV args ls"

abbreviation CBV_Cls :: "(BV_var, ('n,'v,'elem) BV_elem) identifier list \<Rightarrow> (BV_pred, BV_var, ('n,'v,'elem) BV_elem) righthand list \<Rightarrow> (BV_pred, BV_var, ('n,'v,'elem) BV_elem) clause" ("CBV\<langle>_\<rangle> :- _ .") where
  "CBV\<langle>args\<rangle> :- ls. \<equiv> Cls the_CBV args ls"

abbreviation init_Cls :: "(BV_var, ('n,'v,'elem) BV_elem) identifier list \<Rightarrow> (BV_pred, BV_var, ('n,'v,'elem) BV_elem) righthand list \<Rightarrow> (BV_pred, BV_var, ('n,'v,'elem) BV_elem) clause" ("init\<langle>_\<rangle> :- _ .") where 
  "init\<langle>args\<rangle> :- ls. \<equiv> Cls the_init args ls"

abbreviation kill_Cls :: "(BV_var, ('n,'v,'elem) BV_elem) identifier list \<Rightarrow> (BV_pred, BV_var, ('n,'v,'elem) BV_elem) righthand list \<Rightarrow> (BV_pred, BV_var, ('n,'v,'elem) BV_elem) clause" ("kill\<langle>_\<rangle> :- _ .") where 
  "kill\<langle>args\<rangle> :- ls. \<equiv> Cls the_kill args ls"

abbreviation gen_Cls :: "(BV_var, ('n,'v,'elem) BV_elem) identifier list \<Rightarrow> (BV_pred, BV_var, ('n,'v,'elem) BV_elem) righthand list \<Rightarrow> (BV_pred, BV_var, ('n,'v,'elem) BV_elem) clause" ("gen\<langle>_\<rangle> :- _ .") where 
  "gen\<langle>args\<rangle> :- ls. \<equiv> Cls the_gen args ls"

abbreviation BV_Fact :: "(BV_var, ('n,'v,'elem) BV_elem) identifier list \<Rightarrow> (BV_pred, BV_var, ('n,'v,'elem) BV_elem) fact" ("BV\<langle>_\<rangle>.") where  
  "BV\<langle>args\<rangle>. \<equiv> (the_BV, args)"

abbreviation CBV_Fact :: "(BV_var, ('n,'v,'elem) BV_elem) identifier list \<Rightarrow> (BV_pred, BV_var, ('n,'v,'elem) BV_elem) fact" ("CBV\<langle>_\<rangle>.") where 
  "CBV\<langle>args\<rangle>. \<equiv> (the_CBV, args)"

abbreviation init_Fact :: "(BV_var, ('n,'v,'elem) BV_elem) identifier list \<Rightarrow> (BV_pred, BV_var, ('n,'v,'elem) BV_elem) fact" ("init\<langle>_\<rangle>.") where (* is this needed? *)
  "init\<langle>args\<rangle>. \<equiv> (the_init, args)"

abbreviation \<uu> :: "(BV_var, 'a) identifier" where
  "\<uu> == Var the_\<uu>"

abbreviation Cst\<^sub>N :: "'n \<Rightarrow> (BV_var, ('n, 'v, 'elem) BV_elem) identifier" where
  "Cst\<^sub>N q == Cst (Node q)"

abbreviation Decode_Node :: "(BV_var, ('n, 'v, 'elem) BV_elem) identifier \<Rightarrow> 'n" where
  "Decode_Node ident == the_node (the_Cst ident)"

abbreviation Cst\<^sub>E :: "'elem \<Rightarrow> (BV_var, ('n, 'v, 'elem) BV_elem) identifier" where
  "Cst\<^sub>E e == Cst (Elem e)"

abbreviation Decode_Elem :: "(BV_var, ('n, 'v, 'elem) BV_elem) identifier \<Rightarrow> 'elem" where
  "Decode_Elem ident == the_bv_elem (the_Cst ident)"

abbreviation Cst\<^sub>A :: "'v action \<Rightarrow> (BV_var, ('n, 'v, 'elem) BV_elem) identifier" where
  "Cst\<^sub>A \<alpha> == Cst (BV_Action \<alpha>)"


section \<open>Forward may-analysis\<close>

locale analysis_BV_forward_may =
  fixes pg :: "('n::finite,'v) program_graph"
  fixes analysis_dom :: "'d set"
  fixes kill_set :: "('n,'v) edge \<Rightarrow> 'd set"
  fixes gen_set :: "('n,'v) edge \<Rightarrow> 'd set"
  fixes d_init :: "'d set"
  assumes "finite (fst pg)"
  assumes "finite analysis_dom"
  assumes "d_init \<subseteq> analysis_dom"
  assumes "\<forall>e. gen_set e \<subseteq> analysis_dom" (* Could be limited to just the edges in pg *)
  assumes "\<forall>e. kill_set e \<subseteq> analysis_dom"
begin

lemma finite_d_init: "finite d_init"
  by (meson analysis_BV_forward_may_axioms analysis_BV_forward_may_def finite_subset)

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

fun ana_kill_BV_edge_d :: "('n, 'v) edge \<Rightarrow> 'd \<Rightarrow> (BV_pred, BV_var, ('n, 'v, 'd) BV_elem) clause" where
  "ana_kill_BV_edge_d (q\<^sub>o, \<alpha>, q\<^sub>s) d = kill\<langle>[Cst\<^sub>N q\<^sub>o, Cst\<^sub>A \<alpha>, Cst\<^sub>N q\<^sub>s, Cst\<^sub>E d]\<rangle> :- []."

definition ana_kill_BV_edge :: "('n, 'v) edge \<Rightarrow> (BV_pred, BV_var, ('n, 'v, 'd) BV_elem) clause set" where
  "ana_kill_BV_edge e = ana_kill_BV_edge_d e ` (kill_set e \<inter> analysis_dom)"

fun ana_gen_BV_edge_d :: "('n, 'v) edge \<Rightarrow> 'd \<Rightarrow> (BV_pred, BV_var, ('n, 'v, 'd) BV_elem) clause" where
  "ana_gen_BV_edge_d (q\<^sub>o, \<alpha>, q\<^sub>s) d = gen\<langle>[Cst\<^sub>N q\<^sub>o, Cst\<^sub>A \<alpha>, Cst\<^sub>N q\<^sub>s, Cst\<^sub>E d]\<rangle> :- []."

definition ana_gen_BV_edge :: "('n, 'v) edge \<Rightarrow> (BV_pred, BV_var, ('n, 'v, 'd) BV_elem) clause set" where
  "ana_gen_BV_edge e = ana_gen_BV_edge_d e ` (gen_set e \<inter> analysis_dom)"

definition ana_init_BV :: "'d \<Rightarrow> (BV_pred, BV_var, ('n, 'v, 'd) BV_elem) clause set" where
  "ana_init_BV d =
     {
       init\<langle>[Cst\<^sub>E d]\<rangle> :- [].
     }"

definition ana_entry_node_BV :: "(BV_pred, BV_var, ('n,'v, 'd) BV_elem) clause set" where (* This should be a clause, not clause set. *)
  "ana_entry_node_BV = 
     {
       BV\<langle>[Cst\<^sub>N start,\<uu>]\<rangle> :-
         [
           init[\<uu>]
         ].
     }"

fun ana_edge_BV :: "('n, 'v) edge \<Rightarrow> (BV_pred, BV_var, ('n, 'v, 'd) BV_elem) clause set" where
  "ana_edge_BV (q\<^sub>o, \<alpha>, q\<^sub>s) =
     {
        BV\<langle>[Cst\<^sub>N q\<^sub>s, \<uu>]\<rangle> :-
          [
            BV[Cst\<^sub>N q\<^sub>o, \<uu>],
            \<^bold>\<not>kill[Cst\<^sub>N q\<^sub>o, Cst\<^sub>A \<alpha>, Cst\<^sub>N q\<^sub>s, \<uu>]
          ].
        ,
        BV\<langle>[Cst\<^sub>N q\<^sub>s, \<uu>]\<rangle> :- [gen[Cst\<^sub>N q\<^sub>o, Cst\<^sub>A \<alpha>, Cst\<^sub>N q\<^sub>s, \<uu>]].
     }"

definition ana_CBV :: "'n \<Rightarrow> (BV_pred, BV_var, ('n, 'v, 'd) BV_elem) clause" where
  "ana_CBV q = CBV\<langle>[Cst\<^sub>N q,\<uu>]\<rangle> :- [\<^bold>\<not>BV[Cst\<^sub>N q,\<uu>], init[\<uu>]]."

lemma ana_CBV_meta_var:
  assumes "\<rho> \<Turnstile>\<^sub>c\<^sub>l\<^sub>s CBV\<langle>[Cst\<^sub>N q,\<uu>]\<rangle> :- [\<^bold>\<not>BV[Cst\<^sub>N q,\<uu>], init[\<uu>]]."
  shows "\<rho> \<Turnstile>\<^sub>c\<^sub>l\<^sub>s CBV\<langle>[Cst\<^sub>N q,v]\<rangle> :- [\<^bold>\<not>BV[Cst\<^sub>N q,v], init[v]]."
proof -
  define \<mu> where "\<mu> = Var(the_\<uu> := v)"
  have "\<rho> \<Turnstile>\<^sub>c\<^sub>l\<^sub>s ((CBV\<langle>[Cst\<^sub>N q,\<uu>]\<rangle> :- [\<^bold>\<not>BV[Cst\<^sub>N q,\<uu>], init[\<uu>]].) \<cdot>\<^sub>c\<^sub>l\<^sub>s \<mu>)"
    using assms substitution_rule by blast
  then show ?thesis
    unfolding \<mu>_def by auto
qed

definition ana_pg_fw_may :: "(BV_pred, BV_var, ('n, 'v, 'd) BV_elem) clause set" where
  "ana_pg_fw_may = \<Union>(ana_edge_BV ` edge_set)
               \<union> \<Union>(ana_init_BV ` d_init)
               \<union> \<Union>(ana_kill_BV_edge ` edge_set)
               \<union> \<Union>(ana_gen_BV_edge ` edge_set)
               \<union> ana_CBV ` UNIV
               \<union> ana_entry_node_BV"

lemma ana_entry_node_BV_meta_var:
  assumes "\<rho> \<Turnstile>\<^sub>c\<^sub>l\<^sub>s BV\<langle>[Cst\<^sub>N start,\<uu>]\<rangle> :- [init[\<uu>]]."
  shows "\<rho> \<Turnstile>\<^sub>c\<^sub>l\<^sub>s BV\<langle>[Cst\<^sub>N start,u]\<rangle> :- [init[u]]."
proof -
  define \<mu> where "\<mu> = Var(the_\<uu> := u)"
  have "\<rho> \<Turnstile>\<^sub>c\<^sub>l\<^sub>s ((BV\<langle>[Cst\<^sub>N start,\<uu>]\<rangle> :- [init[\<uu>]].) \<cdot>\<^sub>c\<^sub>l\<^sub>s \<mu>)"
    using assms substitution_rule by blast
  then show ?thesis
    unfolding \<mu>_def by auto
qed

fun summarizes_fw_may :: "(BV_pred, ('n, 'v, 'd) BV_elem) pred_val \<Rightarrow> bool" where
  "summarizes_fw_may \<rho> \<longleftrightarrow> 
     (\<forall>\<pi> d. \<pi> \<in> LTS.path_with_word edge_set \<longrightarrow> LTS.get_start \<pi> = start \<longrightarrow> d \<in> S_hat_path \<pi> d_init \<longrightarrow> 
        \<rho> \<Turnstile>\<^sub>f (BV\<langle>[Cst\<^sub>N (LTS.get_end \<pi>), Cst\<^sub>E d]\<rangle>.))"

lemma S_hat_path_append:
  assumes "length qs = length w"                               
  shows "S_hat_path (qs @ [qnminus1, qn], w @ [\<alpha>]) d_init =
    S_hat (qnminus1, \<alpha>, qn) (S_hat_path (qs @ [qnminus1], w) d_init)"
proof -
  have "S_hat_path (qs @ [qnminus1, qn], w @ [\<alpha>]) d_init = S_hat_edge_list (transition_list (qs @ [qnminus1, qn], w @ [\<alpha>])) d_init"
    unfolding S_hat_path_def by auto
  moreover
  have "S_hat_edge_list (transition_list (qs @ [qnminus1, qn], w @ [\<alpha>])) d_init =
        S_hat_edge_list (transition_list (qs @ [qnminus1], w) @ [(qnminus1, \<alpha>, qn)]) d_init"
    using transition_list_reversed_simp[of qs w] assms
    by auto
  moreover
  have "... = S_hat_edge_list [(qnminus1, \<alpha>, qn)] (S_hat_edge_list (transition_list (qs @ [qnminus1], w)) d_init)"
    using S_hat_edge_list_append[of "transition_list (qs @ [qnminus1], w)" " [(qnminus1, \<alpha>, qn)]" d_init]
    by auto
  moreover
  have "... = S_hat (qnminus1, \<alpha>, qn) (S_hat_path (qs @ [qnminus1], w) d_init)"
    unfolding S_hat_path_def by auto
  ultimately show ?thesis
    by blast
qed

lemma ana_pg_fw_may_stratified: "strat_wf s_BV ana_pg_fw_may"
  unfolding ana_pg_fw_may_def
  apply auto
  unfolding strat_wf_def
  apply auto
  unfolding ana_init_BV_def
     apply auto
  subgoal
    unfolding ana_kill_BV_edge_def
    apply auto
    done
  subgoal 
    unfolding ana_gen_BV_edge_def
    apply auto
    done
  subgoal
    unfolding ana_CBV_def
    apply auto
    done
  subgoal 
    unfolding ana_entry_node_BV_def
    apply auto
    done
  done

lemma finite_ana_init_BV:
  "finite (ana_init_BV x)"
  using ana_init_BV_def by force

lemma finite_ana_init_BV_edgeset: "finite (\<Union> (ana_edge_BV ` edge_set))"
  by (smt (verit, best) analysis_BV_forward_may.ana_edge_BV.elims analysis_BV_forward_may_axioms analysis_BV_forward_may_def edge_set_def finite.emptyI finite.intros(2) finite_UN)

lemma ana_pg_fw_may_finite: "finite ana_pg_fw_may"
  unfolding ana_pg_fw_may_def
  apply auto
  using finite_ana_init_BV_edgeset apply blast
  using finite_d_init finite_ana_init_BV apply blast
   apply (metis analysis_BV_forward_may.ana_kill_BV_edge_def analysis_BV_forward_may_axioms analysis_BV_forward_may_def edge_set_def finite_Int finite_UN finite_imageI)
  apply (metis analysis_BV_forward_may.ana_gen_BV_edge_def analysis_BV_forward_may_axioms analysis_BV_forward_may_def edge_set_def finite_Int finite_UN finite_imageI)
  apply (simp add: ana_entry_node_BV_def)
  done


fun vars_fact :: "('p,'x,'e) fact \<Rightarrow> 'x set" where
  "vars_fact (p,ids) = vars_ids ids"

lemma not_kill:
  fixes \<rho> :: "(BV_pred, ('n, 'v, 'd) BV_elem) pred_val"
  assumes "d \<notin> kill_set(q\<^sub>o, \<alpha>, q\<^sub>s)"
  assumes "\<rho> \<Turnstile>\<^sub>l\<^sub>s\<^sub>t ana_pg_fw_may s_BV"
  shows "[Node q\<^sub>o, BV_Action \<alpha>, Node q\<^sub>s, Elem d] \<notin> \<rho> the_kill"
proof -
  have "\<forall>\<sigma>. \<lbrakk>\<^bold>\<not>kill [Cst\<^sub>N q\<^sub>o, Cst\<^sub>A \<alpha>, Cst\<^sub>N q\<^sub>s, Cst\<^sub>E d]\<rbrakk>\<^sub>r\<^sub>h \<rho> \<sigma>"
  proof
    fix \<sigma>
    have "finite ana_pg_fw_may"
      by (simp add: ana_pg_fw_may_finite)
    moreover
    have "\<rho> \<Turnstile>\<^sub>l\<^sub>s\<^sub>t ana_pg_fw_may s_BV"
      using assms(2) by blast
    moreover
    have "strat_wf s_BV ana_pg_fw_may"
      by (simp add: ana_pg_fw_may_stratified)
    moreover
    have "\<forall>c\<in>ana_pg_fw_may --s_BV-- s_BV the_kill. 
           \<forall>\<sigma>'. 
             (the_lh c \<cdot>\<^sub>v\<^sub>l\<^sub>h \<sigma>') = ((the_kill, [Cst\<^sub>N q\<^sub>o, Cst\<^sub>A \<alpha>, Cst\<^sub>N q\<^sub>s, Cst\<^sub>E d]) \<cdot>\<^sub>v\<^sub>l\<^sub>h \<sigma>) 
               \<longrightarrow> \<not> \<lbrakk>the_rhs c\<rbrakk>\<^sub>r\<^sub>h\<^sub>s \<rho> \<sigma>'"
    proof (rule, rule, rule)
      fix c \<sigma>'
      assume c_dl: "c \<in> (ana_pg_fw_may --s_BV-- s_BV the_kill)"
      assume "(the_lh c \<cdot>\<^sub>v\<^sub>l\<^sub>h \<sigma>') = ((the_kill, [Cst\<^sub>N q\<^sub>o, Cst\<^sub>A \<alpha>, Cst\<^sub>N q\<^sub>s, Cst\<^sub>E d]) \<cdot>\<^sub>v\<^sub>l\<^sub>h \<sigma>)"
      moreover
      from c_dl have "c \<in> (ana_pg_fw_may --s_BV-- 0)"
        by auto
      ultimately
      show "\<not> \<lbrakk>the_rhs c\<rbrakk>\<^sub>r\<^sub>h\<^sub>s \<rho> \<sigma>'"
        unfolding ana_pg_fw_may_def ana_init_BV_def ana_kill_BV_edge_def ana_gen_BV_edge_def ana_CBV_def ana_entry_node_BV_def assms(1) apply auto 
        using assms(1) apply fastforce
        done
    qed
    ultimately
    show "\<lbrakk>\<^bold>\<not>kill [Cst\<^sub>N q\<^sub>o, Cst\<^sub>A \<alpha>, Cst\<^sub>N q\<^sub>s, Cst\<^sub>E d]\<rbrakk>\<^sub>r\<^sub>h \<rho> \<sigma>"
      using meaning_neg_rh[of ana_pg_fw_may \<rho> s_BV the_kill "[Cst\<^sub>N q\<^sub>o, Cst\<^sub>A \<alpha>, Cst\<^sub>N q\<^sub>s, Cst\<^sub>E d]" \<sigma>]
      by auto
  qed
  then show ?thesis
    by auto
qed

lemma the_funny_invariant':
  "d \<in> S_hat_edge_list \<pi> d_init \<Longrightarrow> d \<in> analysis_dom"
proof(induction \<pi> rule: List.rev_induct)
  case Nil
  then show ?case
    by (metis S_hat_edge_list.simps(1) analysis_BV_forward_may_axioms analysis_BV_forward_may_def subsetD)
next
  case (snoc x xs)
  then show ?case
    apply auto
    unfolding S_hat_def
    apply auto
    by (meson analysis_BV_forward_may_axioms analysis_BV_forward_may_def subsetD)
qed

lemma the_funny_invariant:
  "d \<in> S_hat_path (ss,w) d_init \<Longrightarrow> d \<in> analysis_dom"
  using S_hat_path_def the_funny_invariant' by auto

lemma sound_ana_pg_fw_may': 
  assumes "(ss,w) \<in> LTS.path_with_word edge_set"
  assumes "\<rho> \<Turnstile>\<^sub>l\<^sub>s\<^sub>t ana_pg_fw_may s_BV"
  assumes "LTS.get_start (ss,w) = start"
  assumes "d \<in> S_hat_path (ss,w) d_init"
  shows "\<rho> \<Turnstile>\<^sub>f BV\<langle>[Cst\<^sub>N (LTS.get_end (ss, w)), Cst\<^sub>E d]\<rangle>."
  using assms 
proof (induction arbitrary: d rule: LTS.path_with_word_induct_reverse[OF assms(1)])
  case (1 s)
  have assms_2: "\<rho> \<Turnstile>\<^sub>d\<^sub>l ana_pg_fw_may"
    using assms(2) unfolding least_solution_def by auto

  from 1(1,3) have start_end: "LTS.get_end ([s], []) = start"
    using LTS.singleton_path_start_end[of s edge_set, OF 1(1)] by (metis LTS.get_end_def prod.sel(1))

  from 1 have "S_hat_path ([s], []) d_init = d_init"
    unfolding S_hat_path_def by auto
  then have "d \<in> d_init"
    using 1(4) by auto
  moreover
  from assms_2 have "\<forall>d\<in>d_init. \<rho> \<Turnstile>\<^sub>c\<^sub>l\<^sub>s init\<langle>[Cst\<^sub>E d]\<rangle> :- [] ."
    unfolding ana_pg_fw_may_def ana_init_BV_def solves_program_def by auto
  moreover
  have "\<rho> \<Turnstile>\<^sub>c\<^sub>l\<^sub>s BV\<langle>[Cst\<^sub>N start, \<uu>]\<rangle> :- [init[\<uu>]]."
    by (metis Un_insert_right ana_entry_node_BV_def analysis_BV_forward_may.ana_pg_fw_may_def analysis_BV_forward_may_axioms assms_2 insertI1 solves_program_def)
  then have "\<rho> \<Turnstile>\<^sub>c\<^sub>l\<^sub>s BV\<langle>[Cst\<^sub>N start, Cst\<^sub>E d]\<rangle> :- [init[Cst\<^sub>E d]]."
    using ana_entry_node_BV_meta_var by blast
  ultimately have "\<rho> \<Turnstile>\<^sub>c\<^sub>l\<^sub>s BV\<langle>[Cst\<^sub>N start, Cst\<^sub>E d]\<rangle> :- [] ."
    using resolution_only_from_cls_cls_to_cls by metis
  then show ?case
    using start_end solves_fact_fact by metis
next
  case (2 qs qnminus1 w \<alpha> qn)
  have "S_hat_path (qs @ [qnminus1], w) d_init \<subseteq>
        {d. \<rho> \<Turnstile>\<^sub>f BV\<langle>[Cst\<^sub>N (LTS.get_end (qs @ [qnminus1], w)), Cst\<^sub>E d]\<rangle>.}"
    using 2
    by (metis (no_types, lifting) LTS.get_start_def hd_append2 list.sel(1) mem_Collect_eq prod.sel(1) self_append_conv2 subsetI) 
  then have f: "S_hat (qnminus1, \<alpha>, qn) (S_hat_path (qs @ [qnminus1], w) d_init) \<subseteq>
             S_hat (qnminus1, \<alpha>, qn) {d. \<rho> \<Turnstile>\<^sub>f BV\<langle>[Cst\<^sub>N (LTS.get_end (qs @ [qnminus1], w)), Cst\<^sub>E d]\<rangle>.}"
    by (simp add: S_hat_mono)
  have "length qs = length w"
    using 2(1) LTS.path_with_word_lengths by metis
  then have "S_hat_path (qs @ [qnminus1, qn], w @ [\<alpha>]) d_init = S_hat (qnminus1, \<alpha>, qn) (S_hat_path (qs @ [qnminus1], w) d_init)"
    using S_hat_path_append[of qs w] by auto
  moreover 
  have "... = S_hat (qnminus1, \<alpha>, qn) (S_hat_path (qs @ [qnminus1], w) d_init)"
    by simp
  moreover 
  have "... \<subseteq> S_hat (qnminus1, \<alpha>, qn) {d. \<rho> \<Turnstile>\<^sub>f BV\<langle>[Cst\<^sub>N qnminus1, Cst\<^sub>E d]\<rangle>.}"
    by (metis f LTS.get_end_def last_snoc prod.sel(1))
  ultimately 
  have "S_hat_path (qs @ [qnminus1, qn], w @ [\<alpha>]) d_init \<subseteq> S_hat (qnminus1, \<alpha>, qn) {d. \<rho> \<Turnstile>\<^sub>f BV\<langle>[Cst\<^sub>N qnminus1, Cst\<^sub>E d]\<rangle>.}"
    by auto
  then have "d \<in> S_hat (qnminus1, \<alpha>, qn) {d. \<rho> \<Turnstile>\<^sub>f BV\<langle>[Cst\<^sub>N qnminus1, Cst\<^sub>E d]\<rangle>.}"
    using 2(7) by auto
  then have "  d \<in> {d. \<rho> \<Turnstile>\<^sub>f BV\<langle>[Cst\<^sub>N qnminus1, Cst\<^sub>E d]\<rangle>.} - kill_set (qnminus1, \<alpha>, qn)
             \<or> d \<in> gen_set (qnminus1, \<alpha>, qn)"
    unfolding S_hat_def by auto
  then have "\<rho> \<Turnstile>\<^sub>f BV\<langle>[Cst\<^sub>N qn, Cst\<^sub>E d]\<rangle>."
  proof
    assume a: "d \<in> {d. \<rho> \<Turnstile>\<^sub>f BV\<langle>[Cst\<^sub>N qnminus1, Cst\<^sub>E d]\<rangle>.} - kill_set (qnminus1, \<alpha>, qn)"
    from a have a_1: "\<rho> \<Turnstile>\<^sub>f BV\<langle>[Cst\<^sub>N qnminus1, Cst\<^sub>E d]\<rangle>."
      by auto
    moreover
    have e_in_pg: "(qnminus1, \<alpha>, qn) \<in> edge_set"
      using "2.hyps"(2) by blast

    have "\<forall>c\<in>ana_edge_BV (qnminus1, \<alpha>, qn). \<rho> \<Turnstile>\<^sub>c\<^sub>l\<^sub>s c"
      using 2(5) e_in_pg unfolding ana_pg_fw_may_def solves_program_def least_solution_def by blast
    then have "\<rho> \<Turnstile>\<^sub>c\<^sub>l\<^sub>s BV\<langle>[Cst\<^sub>N qn, \<uu>]\<rangle> :- [BV [Cst\<^sub>N qnminus1, \<uu>], \<^bold>\<not>kill [Cst\<^sub>N qnminus1, Cst\<^sub>A \<alpha>, Cst\<^sub>N qn, \<uu>]] ."
      by auto
    then have "\<rho> \<Turnstile>\<^sub>c\<^sub>l\<^sub>s BV\<langle>[Cst\<^sub>N qn, Cst\<^sub>E d]\<rangle> 
                       :- [BV [Cst\<^sub>N qnminus1, Cst\<^sub>E d],
                          \<^bold>\<not>kill [Cst\<^sub>N qnminus1, Cst\<^sub>A \<alpha>, Cst\<^sub>N qn, Cst\<^sub>E d]]."
      using substitution_rule[of \<rho> _ "\<lambda>u. Cst\<^sub>E d"]
      by force
    moreover
    from a have a_2: "d \<notin> kill_set (qnminus1, \<alpha>, qn)"
      by auto
    have "[Node qnminus1, BV_Action \<alpha>, Node qn, Elem d] \<notin> \<rho> the_kill"
      using a_2 not_kill[of d qnminus1 \<alpha> qn \<rho>] 2(5) by auto
    then have "\<rho> \<Turnstile>\<^sub>r\<^sub>h \<^bold>\<not>kill [Cst\<^sub>N qnminus1, Cst\<^sub>A \<alpha>, Cst\<^sub>N qn, Cst\<^sub>E d]" (* Could maybe be phrased better *)
      by auto
    ultimately
    show "\<rho> \<Turnstile>\<^sub>f BV\<langle>[Cst\<^sub>N qn, Cst\<^sub>E d]\<rangle>."
      using resolution_only_from_cls_fact_to_fact by (metis (no_types, lifting) Cons_eq_appendI resolution_last_from_cls_rh_to_cls resolution_only_from_cls_fact_to_fact self_append_conv2)

  next
    assume a: "d \<in> gen_set (qnminus1, \<alpha>, qn)"
    have e_in_pg: "(qnminus1, \<alpha>, qn) \<in> edge_set"
      using "2.hyps"(2) by blast

    have "\<forall>c\<in>ana_edge_BV (qnminus1, \<alpha>, qn). \<rho> \<Turnstile>\<^sub>c\<^sub>l\<^sub>s c"
      using 2(5) e_in_pg unfolding ana_pg_fw_may_def solves_program_def least_solution_def by blast
    then have "\<rho> \<Turnstile>\<^sub>c\<^sub>l\<^sub>s BV\<langle>[Cst\<^sub>N qn, \<uu>]\<rangle> :- [gen [Cst\<^sub>N qnminus1, Cst\<^sub>A \<alpha>, Cst\<^sub>N qn, \<uu>]] ."
      by auto
    then have "\<rho> \<Turnstile>\<^sub>c\<^sub>l\<^sub>s BV\<langle>[Cst\<^sub>N qn, Cst\<^sub>E d]\<rangle> :- [gen [Cst\<^sub>N qnminus1, Cst\<^sub>A \<alpha>, Cst\<^sub>N qn, Cst\<^sub>E d]] ."
      using substitution_rule[of \<rho> _ "\<lambda>u. Cst\<^sub>E d" ]
      by force
    moreover
    have dan: "d \<in> analysis_dom"
      using "2.prems"(4) the_funny_invariant by blast
    have "\<forall>c\<in>\<Union>(ana_gen_BV_edge ` edge_set). \<rho> \<Turnstile>\<^sub>c\<^sub>l\<^sub>s c"
      using 2(5) unfolding ana_pg_fw_may_def solves_program_def least_solution_def by auto
    then have "\<rho> \<Turnstile>\<^sub>c\<^sub>l\<^sub>s (ana_gen_BV_edge_d (qnminus1, \<alpha>, qn) d)"
      using e_in_pg a ana_gen_BV_edge_def dan by auto
    then have "\<rho> \<Turnstile>\<^sub>c\<^sub>l\<^sub>s gen\<langle>[Cst\<^sub>N qnminus1, Cst\<^sub>A \<alpha>, Cst\<^sub>N qn, Cst\<^sub>E d]\<rangle> :- [] ."
      by auto
    ultimately
    show "\<rho> \<Turnstile>\<^sub>f BV\<langle>[Cst\<^sub>N qn, Cst\<^sub>E d]\<rangle>."
      by (meson resolution_only_from_cls_fact_to_fact solves_fact_fact)
  qed
  then show ?case
    by (simp add: LTS.get_end_def)
qed

lemma sound_ana_pg_fw_may:
  assumes "\<rho> \<Turnstile>\<^sub>l\<^sub>s\<^sub>t ana_pg_fw_may s_BV"
  shows "summarizes_fw_may \<rho>"
  using sound_ana_pg_fw_may' assms unfolding summarizes_fw_may.simps by (cases pg) fastforce

end


section \<open>Reaching definitions revisited\<close>

locale analysis_RD =
  fixes pg :: "('n::finite,'v::finite) program_graph"
  assumes "finite (fst pg)"
begin

definition edge_set where
  "edge_set = fst pg"

definition start where
  "start = fst (snd pg)"

definition "end" where
  "end = snd (snd pg)"

definition analysis_dom_RD :: "('n,'v) triple set" where
  "analysis_dom_RD = UNIV \<times> UNIV \<times> UNIV"

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


lemma finite_analysis_dom_RD: "finite analysis_dom_RD"
  by auto

lemma d_init_RD_subset_analysis_dom_RD:
  "d_init_RD \<subseteq> analysis_dom_RD"
  unfolding d_init_RD_def analysis_dom_RD_def by auto

lemma gen_RD_subset_analysis_dom: "gen_set_RD e \<subseteq> analysis_dom_RD"
  unfolding analysis_dom_RD_def by auto

lemma kill_RD_subset_analysis_dom: "kill_set_RD e \<subseteq> analysis_dom_RD"
  unfolding analysis_dom_RD_def by auto


interpretation interp: analysis_BV_forward_may pg analysis_dom_RD kill_set_RD gen_set_RD d_init_RD 
  using analysis_BV_forward_may_def analysis_RD_axioms analysis_RD_def
  using d_init_RD_subset_analysis_dom_RD finite_analysis_dom_RD gen_RD_subset_analysis_dom kill_RD_subset_analysis_dom
  by blast 

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
      by (simp add: interp.S_hat_def assms(1))
  next
    case Skip
    then show ?thesis
      by (simp add: interp.S_hat_def assms(1))
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

lemma S_hat_edge_list_last: "interp.S_hat_edge_list (\<pi> @ [e]) d_init_RD = interp.S_hat e (interp.S_hat_edge_list \<pi> d_init_RD)"
  using interp.S_hat_edge_list_def2 foldl_conv_foldr by simp

lemma def_var_if_S_hat: "(x,q1,q2) \<in> interp.S_hat_edge_list \<pi> d_init_RD \<Longrightarrow> (x,q1,q2) = (def_var \<pi>) x start"
proof (induction \<pi> rule: rev_induct)
  case Nil
  then show ?case
    by (metis append_is_Nil_conv d_init_RD_def def_var_def in_set_conv_decomp interp.S_hat_edge_list.simps(1) list.distinct(1) mem_Sigma_iff singletonD)
next
  case (snoc e \<pi>)

  from snoc(2) have "(x, q1, q2) \<in> interp.S_hat e (interp.S_hat_edge_list \<pi> d_init_RD)"
    using S_hat_edge_list_last by blast     

  then have "(x, q1, q2) \<in> interp.S_hat_edge_list \<pi> d_init_RD - kill_set_RD e \<or> (x, q1, q2) \<in> gen_set_RD e"
    unfolding interp.S_hat_def by auto
  then show ?case
  proof
    assume a: "(x, q1, q2) \<in> interp.S_hat_edge_list \<pi> d_init_RD - kill_set_RD e"
    then have "(x, q1, q2) = def_var \<pi> x start"
      using snoc by auto
    moreover
    from a have "(x, q1, q2) \<notin> kill_set_RD e"
      by auto
    then have "def_var (\<pi> @ [e]) x start = def_var \<pi> x start"
    proof -
      assume a: "(x, q1, q2) \<notin> kill_set_RD e"
      then have "x \<notin> def_edge e"
        apply (cases e)
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
    assume "(x, q1, q2) \<in> gen_set_RD e"
    then have "\<exists>exp theq1. e = (theq1, x ::= exp, q2) \<and> q1 = Some theq1"
      apply (cases e)
      subgoal for q1' e' q2'
        apply (cases e')
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
    then obtain exp theq1 where exp_theq1_p: "e = (theq1, x ::= exp, q2) \<and> q1 = Some theq1"
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
    by (metis def_var_if_S_hat prod.collapse range_eqI)
qed

lemma def_path_S_hat_path: "def_path \<pi> start = interp.S_hat_path \<pi> d_init_RD"
  using interp.S_hat_path_def def_path_def def_var_UNIV_S_hat_edge_list by metis

fun summarizes_RD :: "(BV_pred, ('n,'v,('n,'v) triple) BV_elem) pred_val \<Rightarrow> bool" where
  "summarizes_RD \<rho> \<longleftrightarrow> (\<forall>\<pi> d. \<pi> \<in> LTS.path_with_word edge_set \<longrightarrow> LTS.get_start \<pi> = start \<longrightarrow> d \<in> def_path \<pi> start \<longrightarrow> 
                        \<rho> \<Turnstile>\<^sub>f BV\<langle>[Cst\<^sub>N (LTS.get_end \<pi>), Cst\<^sub>E d]\<rangle>.)"

lemma RD_sound_again: 
  assumes "\<rho> \<Turnstile>\<^sub>l\<^sub>s\<^sub>t (interp.ana_pg_fw_may) s_BV"
  shows "summarizes_RD \<rho>"
  using assms def_path_S_hat_path interp.sound_ana_pg_fw_may unfolding interp.summarizes_fw_may.simps summarizes_RD.simps
  using edge_set_def in_mono interp.edge_set_def interp.start_def start_def by fastforce 

end


section \<open>Backward may-analysis\<close>

thm Program_Graph.analysis_BV_forward_may.edge_set.cong 

locale analysis_BV_backward_may =
  fixes pg :: "('n::finite,'v) program_graph"
  fixes analysis_dom :: "'d set"
  fixes kill_set :: "('n,'v) edge \<Rightarrow> 'd set"
  fixes gen_set :: "('n,'v) edge \<Rightarrow> 'd set"
  fixes d_init :: "'d set"
  assumes "finite (fst pg)"
  assumes "finite analysis_dom"
  assumes "d_init \<subseteq> analysis_dom"
  assumes "\<forall>e. gen_set e \<subseteq> analysis_dom" (* Could be limited to just the edges in pg *)
  assumes "\<forall>e. kill_set e \<subseteq> analysis_dom"
begin

lemma finite_d_init: "finite d_init"
  by (meson analysis_BV_backward_may_axioms analysis_BV_backward_may_def finite_subset)

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

definition summarizes_bw_may :: "(BV_pred, ('n, 'v, 'd) BV_elem) pred_val \<Rightarrow> bool" where
  "summarizes_bw_may \<rho> \<longleftrightarrow> (\<forall>\<pi> d. \<pi> \<in> LTS.path_with_word edge_set \<longrightarrow> LTS.get_end \<pi> = end \<longrightarrow> d \<in> S_hat_path \<pi> d_init \<longrightarrow> 
                             \<rho> \<Turnstile>\<^sub>f BV\<langle>[Cst\<^sub>N (LTS.get_start \<pi>), Cst\<^sub>E d]\<rangle>.)"

lemma finite_pg_rev: "finite (fst pg_rev)"
  by (metis analysis_BV_backward_may_axioms analysis_BV_backward_may_def edge_set_def finite_imageI fst_conv pg_rev_def)

lemma new_gen_subs_analysis_dom: "(kill_set (rev_edge e)) \<subseteq> analysis_dom"
  by (meson analysis_BV_backward_may_axioms analysis_BV_backward_may_def)

lemma new_kill_subs_analysis_dom: "(gen_set (rev_edge e)) \<subseteq> analysis_dom"
  by (meson analysis_BV_backward_may_axioms analysis_BV_backward_may_def)

interpretation fa: analysis_BV_forward_may pg_rev analysis_dom "\<lambda>e. (kill_set (rev_edge e))" "(\<lambda>e. gen_set (rev_edge e))" d_init
  using analysis_BV_forward_may_def finite_pg_rev by (metis analysis_BV_backward_may_axioms analysis_BV_backward_may_def) 

abbreviation ana_pg_bw_may where
  "ana_pg_bw_may == fa.ana_pg_fw_may"

lemma rev_end_is_start:
  assumes "ss \<noteq> []"
  assumes "LTS.get_end (ss, w) = end"
  shows "LTS.get_start (rev ss, rev w) = fa.start"
  using assms
  unfolding LTS.get_end_def LTS.get_start_def fa.start_def pg_rev_def fa.start_def
  using hd_rev by (metis fa.start_def fst_conv pg_rev_def snd_conv) 

lemma S_hat_edge_list_forward_backward:
  "S_hat_edge_list ss d_init = fa.S_hat_edge_list (rev_edge_list ss) d_init"
proof (induction ss)
  case Nil
  then show ?case
    unfolding rev_edge_list_def by auto
next
  case (Cons e es)
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

lemma S_hat_path_forward_backward:
  assumes "(ss,w) \<in> LTS.path_with_word edge_set"
  shows "S_hat_path (ss, w) d_init = fa.S_hat_path (rev ss, rev w) d_init"
  using S_hat_edge_list_forward_backward unfolding S_hat_path_def fa.S_hat_path_def
  by (metis transition_list_rev_edge_list assms)

lemma summarizes_bw_may_forward_backward':
  assumes "(ss,w) \<in> LTS.path_with_word edge_set"
  assumes "LTS.get_end (ss,w) = end"
  assumes "d \<in> S_hat_path (ss,w) d_init"
  assumes "fa.summarizes_fw_may \<rho>"
  shows "\<rho> \<Turnstile>\<^sub>f BV\<langle>[Cst\<^sub>N (LTS.get_start (ss, w)), Cst\<^sub>E d]\<rangle>."
proof -
  have rev_in_edge_set: "(rev ss, rev w) \<in> LTS.path_with_word fa.edge_set"
    using assms(1) rev_path_in_rev_pg[of ss w] fa.edge_set_def pg_rev_def by auto 
  moreover
  have "LTS.get_start (rev ss, rev w) = fa.start"
    using assms(1,2) rev_end_is_start by (metis LTS.path_with_word_not_empty)
  moreover
  have "d \<in> fa.S_hat_path (rev ss, rev w) d_init"
    using assms(3)
    using assms(1) S_hat_path_forward_backward by auto
  ultimately
  have "\<rho> \<Turnstile>\<^sub>f BV\<langle>[Cst\<^sub>N (LTS.get_end (rev ss, rev w)), Cst\<^sub>E d]\<rangle>."
    using assms(4) fa.summarizes_fw_may.simps by blast
  then show ?thesis
    by (metis LTS.get_end_def LTS.get_start_def fst_conv hd_rev rev_rev_ident)
qed

lemma summarizes_dl_BV_forward_backward:
  assumes "fa.summarizes_fw_may \<rho>"
  shows "summarizes_bw_may \<rho>"
  unfolding summarizes_bw_may_def
proof(rule; rule ; rule ;rule ;rule)
  fix \<pi> d
  assume "\<pi> \<in> LTS.path_with_word edge_set"
  moreover
  assume "LTS.get_end \<pi> = end"
  moreover
  assume "d \<in> S_hat_path \<pi> d_init"
  ultimately
  show "\<rho> \<Turnstile>\<^sub>f BV\<langle>[Cst\<^sub>N (LTS.get_start \<pi>), Cst\<^sub>E d]\<rangle>."
    using summarizes_bw_may_forward_backward'[of "fst \<pi>" "snd \<pi>" d \<rho>] using assms by auto
qed

lemma sound_rev_BV:
  assumes "\<rho> \<Turnstile>\<^sub>l\<^sub>s\<^sub>t ana_pg_bw_may s_BV"
  shows "summarizes_bw_may \<rho>"
  using assms fa.sound_ana_pg_fw_may[of \<rho>] summarizes_dl_BV_forward_backward by metis

end


section \<open>Live Variables Analysis\<close>

fun use_action :: "'v action \<Rightarrow> 'v set" where
  "use_action (x ::= a) = fv_arith a"
| "use_action (Bool b) = fv_boolean b"
| "use_action Skip = {}"

fun use_edge :: "('n,'v) edge \<Rightarrow> 'v set" where
  "use_edge (q1, \<alpha>, q2) = use_action \<alpha>"

definition use_edge_list :: "('n,'v) edge list \<Rightarrow> 'v \<Rightarrow> bool" where
  "use_edge_list \<pi> x = (\<exists>\<pi>1 \<pi>2 e. \<pi> = \<pi>1 @ [e] @ \<pi>2 \<and> x \<in> use_edge e \<and> (\<not>(\<exists>e' \<in> set \<pi>1. x \<in> def_edge e')))"

definition use_path :: "'n list \<times> 'v action list \<Rightarrow> 'v set" where
  "use_path \<pi> = {x. use_edge_list (LTS.transition_list \<pi>) x}"

locale analysis_LV =
  fixes pg :: "('n::finite,'v::finite) program_graph"
  assumes "finite (fst pg)"
begin

definition edge_set where 
  "edge_set = fst pg"

definition start where
  "start = fst (snd pg)"

definition "end" where
  "end = snd (snd pg)"

definition analysis_dom_LV :: "'v set" where
  "analysis_dom_LV = UNIV"

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

interpretation interpb: analysis_BV_backward_may pg analysis_dom_LV kill_set_LV gen_set_LV d_init_LV
  using analysis_BV_backward_may.intro analysis_LV_axioms analysis_LV_def
  by (metis (mono_tags) analysis_dom_LV_def finite_UNIV subset_UNIV)

lemma use_edge_list_S_hat_edge_list: 
  assumes "use_edge_list \<pi> x"
  shows "x \<in> interpb.S_hat_edge_list \<pi> d_init_LV"
  using assms
proof (induction \<pi>)
  case Nil
  then have False 
    unfolding use_edge_list_def by auto
  then show ?case
    by metis
next
  case (Cons e \<pi>)
  note Cons_inner = Cons
  from Cons(2) have "\<exists>\<pi>1 \<pi>2 e'. e # \<pi> = \<pi>1 @ [e'] @ \<pi>2 \<and> x \<in> use_edge e' \<and> \<not> (\<exists>e''\<in>set \<pi>1. x \<in> def_edge e'')"
    unfolding use_edge_list_def by auto
  then obtain \<pi>1 \<pi>2 e' where \<pi>1_\<pi>2_e'_p:
    "e # \<pi> = \<pi>1 @ [e'] @ \<pi>2"
    "x \<in> use_edge e'"
    "\<not>(\<exists>e''\<in>set \<pi>1. x \<in> def_edge e'')"
    by auto
  then show ?case
  proof (cases \<pi>1)
    case Nil
    have "e = e'"
      using \<pi>1_\<pi>2_e'_p(1) Nil by auto
    then have x_used_a: "x \<in> use_edge e"
      using \<pi>1_\<pi>2_e'_p(2) by auto
    obtain p \<alpha> q where a_split: "e = (p, \<alpha>, q)"
      by (cases e)
    show ?thesis
      using x_used_a interpb.S_hat_def a_split by (cases \<alpha>) auto
  next
    case (Cons hd_\<pi>1 tl_\<pi>1)
    obtain p \<alpha> q where e_split: "e' = (p, \<alpha>, q)"
      by (cases e')
    have "(\<pi> = tl_\<pi>1 @ (p, \<alpha>, q) # \<pi>2) \<and> x \<in> use_action \<alpha> \<and> (\<forall>e'\<in>set tl_\<pi>1. x \<notin> def_edge e')"
      using Cons \<pi>1_\<pi>2_e'_p e_split by auto
    then have "use_edge_list \<pi> x"
      unfolding use_edge_list_def by force
    then have x_in_S_hat_\<pi>: "x \<in> interpb.S_hat_edge_list \<pi> d_init_LV"
      using Cons_inner by auto
    have "e \<in> set \<pi>1"
      using \<pi>1_\<pi>2_e'_p(1) Cons(1) by auto
    then have x_not_def_a: "\<not>x \<in> def_edge e"
      using \<pi>1_\<pi>2_e'_p(3) by auto

    obtain p' \<alpha>' q' where a_split: "e = (p', \<alpha>', q')"
      by (cases e)

    show ?thesis
    proof (cases "x \<in> kill_set_LV e")
      case True
      show ?thesis
        using True a_split x_not_def_a by (cases \<alpha>'; force)
    next
      case False
      then show ?thesis
        by (simp add: interpb.S_hat_def x_in_S_hat_\<pi>)
    qed
  qed
qed

lemma S_hat_edge_list_use_edge_list:
  assumes "x \<in> interpb.S_hat_edge_list \<pi> d_init_LV"
  shows "use_edge_list \<pi> x"
  using assms 
proof (induction \<pi>)
  case Nil
  then have False
    using d_init_LV_def by auto
  then show ?case
    by metis
next
  case (Cons e \<pi>)
  from Cons(2) have "x \<in> interpb.S_hat_edge_list \<pi> d_init_LV - kill_set_LV e \<union> gen_set_LV e"
    unfolding interpb.S_hat_edge_list.simps unfolding interpb.S_hat_def by auto
  then show ?case
  proof
    assume a: "x \<in> interpb.S_hat_edge_list \<pi> d_init_LV - kill_set_LV e"
    then have "x \<in> interpb.S_hat_edge_list \<pi> d_init_LV"
      by auto
    then have "use_edge_list \<pi> x"
      using Cons by auto
    then have "\<exists>\<pi>1 \<pi>2 e'. \<pi> = \<pi>1 @ [e'] @ \<pi>2 \<and> x \<in> use_edge e' \<and> \<not>(\<exists>e''\<in>set \<pi>1. x \<in> def_edge e'')"
      unfolding use_edge_list_def by auto
    then obtain \<pi>1 \<pi>2 e' where \<pi>1_\<pi>2_e'_p:
      "\<pi> = \<pi>1 @ [e'] @ \<pi>2"
      "x \<in> use_edge e'"
      "\<not>(\<exists>e''\<in>set \<pi>1. x \<in> def_edge e'')"
      by auto
    obtain q1 \<alpha> q2 where a_split: "e = (q1, \<alpha>, q2)"
      by (cases e) auto
    from a have "x \<notin> kill_set_LV e"
      by auto
    then have x_not_killed: "x \<notin> kill_set_LV (q1, \<alpha>, q2)"
      using a_split by auto
    have "use_edge_list ((q1, \<alpha>, q2) # \<pi>) x"
    proof (cases \<alpha>)
      case (Asg y exp)
      then have "x \<notin> kill_set_LV (q1, y ::= exp, q2)"
        using x_not_killed by auto
      then have x_not_y: "x \<noteq> y"
        by auto
      have "(q1, y ::= exp, q2) # \<pi> = ((q1, y ::= exp, q2) # \<pi>1) @ [e'] @ \<pi>2"
        using \<pi>1_\<pi>2_e'_p by force
      moreover
      have "\<not> (\<exists>e'\<in>set ((q1, y ::= exp, q2) # \<pi>1). x \<in> def_edge e')"
        using \<pi>1_\<pi>2_e'_p x_not_y by force
      ultimately
      have "use_edge_list ((q1, y ::= exp, q2) # \<pi>) x"
        unfolding use_edge_list_def using \<pi>1_\<pi>2_e'_p x_not_y by metis
      then show ?thesis
        by (simp add: Asg)
    next
      case (Bool b)
      have "(q1, Bool b, q2) # \<pi> = ((q1, Bool b, q2) # \<pi>1) @ [e'] @ \<pi>2"
        using \<pi>1_\<pi>2_e'_p unfolding use_edge_list_def by auto
      moreover
      have "\<not> (\<exists>e'\<in>set ((q1, Bool b, q2) # \<pi>1). x \<in> def_edge e')"
        using \<pi>1_\<pi>2_e'_p unfolding use_edge_list_def by auto
      ultimately
      have "use_edge_list ((q1, Bool b, q2) # \<pi>) x"
        unfolding use_edge_list_def using \<pi>1_\<pi>2_e'_p by metis
      then show ?thesis
        using Bool by auto
    next
      case Skip
      have "(q1, Skip, q2) # \<pi> = ((q1, Skip, q2) # \<pi>1) @ [e'] @ \<pi>2"
        using \<pi>1_\<pi>2_e'_p unfolding use_edge_list_def by auto
      moreover
      have "\<not> (\<exists>e'\<in>set ((q1, Skip, q2) # \<pi>1). x \<in> def_edge e')"
        using \<pi>1_\<pi>2_e'_p unfolding use_edge_list_def by auto
      ultimately
      have "use_edge_list ((q1, Skip, q2) # \<pi>) x"
        unfolding use_edge_list_def using \<pi>1_\<pi>2_e'_p by metis
      then show ?thesis
        using Skip by auto
    qed
    then show "use_edge_list (e # \<pi>) x"
      using a_split by auto
  next
    assume a: "x \<in> gen_set_LV e"
    obtain p \<alpha> q where a_split: "e = (p, \<alpha>, q)"
      by (cases e)
    have "use_edge_list ((p, \<alpha>, q) # \<pi>) x"
      using a a_split unfolding use_edge_list_def by (cases \<alpha>; force)
    then show "use_edge_list (e # \<pi>) x"
      using a_split by auto
  qed
qed

lemma use_edge_list_UNIV_S_hat_edge_list: "{x. use_edge_list \<pi> x} = interpb.S_hat_edge_list \<pi> d_init_LV"
  using use_edge_list_S_hat_edge_list S_hat_edge_list_use_edge_list by auto

lemma use_path_S_hat_path: "use_path \<pi> = interpb.S_hat_path \<pi> d_init_LV"
  by (simp add: use_edge_list_UNIV_S_hat_edge_list interpb.S_hat_path_def use_path_def)

definition summarizes_LV :: "(BV_pred, ('n,'v,'v) BV_elem) pred_val \<Rightarrow> bool" where
  "summarizes_LV \<rho> \<longleftrightarrow> (\<forall>\<pi> d. \<pi> \<in> LTS.path_with_word edge_set \<longrightarrow> LTS.get_end \<pi> = end \<longrightarrow> d \<in> use_path \<pi> \<longrightarrow> 
                         \<rho> \<Turnstile>\<^sub>f BV\<langle>[Cst\<^sub>N (LTS.get_start \<pi>), Cst\<^sub>E d]\<rangle>.)"

lemma LV_sound:
  assumes "\<rho> \<Turnstile>\<^sub>l\<^sub>s\<^sub>t (interpb.ana_pg_bw_may) s_BV"
  shows "summarizes_LV \<rho>"
proof -
  from assms have "interpb.summarizes_bw_may \<rho>"
    using interpb.sound_rev_BV[of \<rho>] by auto
  then show ?thesis
    unfolding summarizes_LV_def interpb.summarizes_bw_may_def interpb.edge_set_def edge_set_def
      interpb.end_def end_def use_path_S_hat_path by blast
qed
end


section \<open>Forward must-analysis\<close>
                                            
locale analysis_BV_forward_must =
  fixes pg :: "('n::finite,'v) program_graph"
  fixes analysis_dom :: "'d set"
  fixes kill_set :: "('n,'v) edge \<Rightarrow> 'd set"
  fixes gen_set :: "('n,'v) edge \<Rightarrow> 'd set"
  fixes d_init :: "'d set"
  assumes "finite (fst pg)"
  assumes "finite analysis_dom"
  assumes "d_init \<subseteq> analysis_dom"
begin

lemma finite_d_init: "finite d_init"
  by (meson analysis_BV_forward_must_axioms analysis_BV_forward_must_def finite_subset)

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

fun summarizes_fw_must :: "(BV_pred, ('n, 'v, 'd) BV_elem) pred_val \<Rightarrow> bool" where
   "summarizes_fw_must \<rho> \<longleftrightarrow>
     (\<forall>\<pi>_end d.
         \<rho> \<Turnstile>\<^sub>f CBV\<langle>[\<pi>_end, d]\<rangle>. \<longrightarrow>
          (\<forall>\<pi>. \<pi> \<in> LTS.path_with_word edge_set \<longrightarrow> LTS.get_start \<pi> = start \<longrightarrow> LTS.get_end \<pi> = Decode_Node \<pi>_end \<longrightarrow> (Decode_Elem d) \<in> S_hat_path \<pi> d_init))"



interpretation a_may: analysis_BV_forward_may pg analysis_dom "\<lambda>e. analysis_dom - (kill_set e)" "(\<lambda>e. analysis_dom - gen_set e)" "analysis_dom - d_init"
  using analysis_BV_forward_may.intro analysis_BV_forward_must_axioms analysis_BV_forward_must_def
  by (metis Diff_subset)

abbreviation ana_pg_fw_must where (* Copy paste *)
  "ana_pg_fw_must == a_may.ana_pg_fw_may"

lemma opposite_lemma:
  assumes "d \<in> analysis_dom"
  assumes "\<not>d \<in> a_may.S_hat_edge_list \<pi> (analysis_dom - d_init)"
  shows "d \<in> S_hat_edge_list \<pi> d_init"
  using assms proof (induction \<pi> rule: List.rev_induct)
  case Nil
  then show ?case
    by auto
next
  case (snoc x xs)
  then show ?case
    unfolding a_may.S_hat_edge_list_def2
    by (simp add: S_hat_def a_may.S_hat_def)
qed

lemma opposite_lemma2:
  assumes "d \<in> analysis_dom"
  assumes "\<not>d \<in> a_may.S_hat_path \<pi> (analysis_dom - d_init)"
  shows "d \<in> S_hat_path \<pi> d_init"
  using S_hat_path_def a_may.S_hat_path_def assms opposite_lemma
  by (metis a_may.the_funny_invariant preds_lh.cases) 

lemma the_CBV_only_ana_CBV: "the_CBV \<notin> preds_dl (ana_pg_fw_must - (a_may.ana_CBV ` UNIV))"
  unfolding a_may.ana_pg_fw_may_def
  apply simp
  apply (simp only: Un_Diff)
  apply simp
  apply (rule)
  subgoal
    unfolding preds_dl_def
    apply auto
    done
  apply (rule)
  subgoal
    unfolding preds_dl_def a_may.ana_init_BV_def
    apply auto
    done
  apply (rule)
  subgoal
    unfolding preds_dl_def
    apply auto
    subgoal for c a aa b
      unfolding a_may.ana_kill_BV_edge_def
      apply auto
      done
    done
  subgoal
    unfolding preds_dl_def
    apply auto
    subgoal for c a aa b
      unfolding a_may.ana_gen_BV_edge_def
      apply auto
      done
    subgoal for c
      unfolding a_may.ana_entry_node_BV_def
      apply auto
      done
    done
  done    

lemma agree_off_rh:
  assumes "\<forall>p. p \<noteq> p' \<longrightarrow> \<rho>' p = \<rho> p"
  assumes "p' \<notin> preds_rh rh"
  shows "\<lbrakk>rh\<rbrakk>\<^sub>r\<^sub>h \<rho>' \<sigma> \<longleftrightarrow> \<lbrakk>rh\<rbrakk>\<^sub>r\<^sub>h \<rho> \<sigma>"
  using assms proof (cases rh)
  case (Eql a a')
  then show ?thesis
    by auto 
next
  case (Neql a a')
  then show ?thesis 
    by auto 
next
  case (PosRh p ids)
  then show ?thesis
    using assms by auto 
next
  case (NegRh p ids)
  then show ?thesis 
    using assms by auto 
qed

lemma agree_off_lh:
  assumes "\<forall>p. p \<noteq> p' \<longrightarrow> \<rho>' p = \<rho> p"
  assumes "p' \<notin> preds_lh lh"
  shows "\<lbrakk>lh\<rbrakk>\<^sub>l\<^sub>h \<rho>' \<sigma> \<longleftrightarrow> \<lbrakk>lh\<rbrakk>\<^sub>l\<^sub>h \<rho> \<sigma>"
proof (cases lh)
  case (Pair p ids)
  then show ?thesis
    using assms by auto
qed

lemma agree_off_cls:
  assumes "\<forall>p. p \<noteq> p' \<longrightarrow> \<rho>' p = \<rho> p"
  assumes "p' \<notin> preds_cls c"
  shows " \<lbrakk>c\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho>' \<sigma> \<longleftrightarrow> \<lbrakk>c\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho> \<sigma>"
proof (cases c)
  case (Cls p ids rhs)
  then show ?thesis
    apply auto
    apply (metis (no_types, lifting) agree_off_rh assms clause.set_intros(2))
    using assms apply force
    apply (metis (full_types) agree_off_rh assms clause.set_intros(2))
    using assms apply fastforce
    done
qed

lemma agree_off_solves_cls:
  assumes "\<forall>p. p \<noteq> p' \<longrightarrow> \<rho>' p = \<rho> p"
  assumes "p' \<notin> preds_cls c"
  shows "\<rho>' \<Turnstile>\<^sub>c\<^sub>l\<^sub>s c \<longleftrightarrow> \<rho> \<Turnstile>\<^sub>c\<^sub>l\<^sub>s c"
proof (cases c)
  case (Cls p ids rhs)
  then show ?thesis
    by (metis (mono_tags, opaque_lifting) agree_off_cls assms solves_cls_def)
qed

lemma agree_off_dl:
  assumes "\<forall>p. p \<noteq> p' \<longrightarrow> \<rho>' p = \<rho> p"
  assumes "p' \<notin> preds_dl dl"
  shows "\<rho>' \<Turnstile>\<^sub>d\<^sub>l dl \<longleftrightarrow> \<rho> \<Turnstile>\<^sub>d\<^sub>l dl"
proof 
  assume "\<rho>' \<Turnstile>\<^sub>d\<^sub>l dl"
  then show "\<rho> \<Turnstile>\<^sub>d\<^sub>l dl"
    unfolding solves_program_def apply auto
    using assms
    by (smt (verit, ccfv_SIG) agree_off_solves_cls insert_iff mem_Collect_eq mem_simps(9) preds_dl_def)
next 
  assume "\<rho> \<Turnstile>\<^sub>d\<^sub>l dl"
  then show "\<rho>' \<Turnstile>\<^sub>d\<^sub>l dl"
    unfolding solves_program_def apply auto
    using assms
    by (smt (verit, ccfv_SIG) agree_off_solves_cls insert_iff mem_Collect_eq mem_simps(9) preds_dl_def)
qed

lemma not_CBV:
  assumes "[Node q, Elem d] \<in> \<rho> the_CBV"
  assumes "\<rho> \<Turnstile>\<^sub>l\<^sub>s\<^sub>t ana_pg_fw_must s_BV"
  assumes a: "[Node q, Elem d] \<in> \<rho> the_BV"                  
  shows False
proof -
  have fin: "finite ana_pg_fw_must"
    using a_may.ana_pg_fw_may_finite by auto

  have "\<rho> \<Turnstile>\<^sub>l\<^sub>s\<^sub>t ana_pg_fw_must s_BV"
    using assms(2) by force
  then have "\<rho> \<Turnstile>\<^sub>m\<^sub>i\<^sub>n ana_pg_fw_must s_BV"
    using a_may.ana_pg_fw_may_stratified least_is_minimal[of ana_pg_fw_must s_BV \<rho>] fin by auto
  then have \<rho>_sol: "\<rho> \<Turnstile>\<^sub>d\<^sub>l ana_pg_fw_must"
    using assms(2) least_solution_def by blast


  define \<rho>' where  "\<rho>' = (\<lambda>p. (if p = the_CBV then (\<rho> the_CBV) - {[Node q, Elem d]} else \<rho> p))"

  have CBV_solves: "\<rho>' \<Turnstile>\<^sub>c\<^sub>l\<^sub>s CBV\<langle>[Cst\<^sub>N q, \<uu>]\<rangle> :- [\<^bold>\<not>BV [Cst\<^sub>N q, \<uu>], init[\<uu>]] ."
    unfolding solves_cls_def
  proof 
    fix \<sigma>
    show "\<lbrakk>CBV\<langle>[Cst\<^sub>N q, \<uu>]\<rangle> :- [\<^bold>\<not>BV [Cst\<^sub>N q, \<uu>], init[\<uu>]].\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho>' \<sigma>"
    proof (cases "\<sigma> the_\<uu> = Elem d")
      case True
      then have "\<not> \<lbrakk>\<^bold>\<not>BV [Cst\<^sub>N q, \<uu>]\<rbrakk>\<^sub>r\<^sub>h \<rho>' \<sigma>"
        unfolding \<rho>'_def using a by auto
      then show ?thesis
        unfolding meaning_cls.simps by auto
    next
      case False
      then have "\<lbrakk>\<^bold>\<not>BV [Cst\<^sub>N q, \<uu>]\<rbrakk>\<^sub>r\<^sub>h \<rho>' \<sigma> \<longleftrightarrow> \<lbrakk>\<^bold>\<not>BV [Cst\<^sub>N q, \<uu>]\<rbrakk>\<^sub>r\<^sub>h \<rho> \<sigma>"
        by (simp add: \<rho>'_def)
      moreover
      from False have "\<lbrakk>CBV\<langle>[Cst\<^sub>N q, \<uu>]\<rangle>.\<rbrakk>\<^sub>l\<^sub>h \<rho>' \<sigma> \<longleftrightarrow> \<lbrakk>CBV\<langle>[Cst\<^sub>N q, \<uu>]\<rangle>.\<rbrakk>\<^sub>l\<^sub>h \<rho> \<sigma>"
        unfolding \<rho>'_def by auto
      moreover
      have "\<lbrakk>init\<langle>[Cst\<^sub>N q, \<uu>]\<rangle>.\<rbrakk>\<^sub>l\<^sub>h \<rho>' \<sigma> \<longleftrightarrow> \<lbrakk>init\<langle>[Cst\<^sub>N q, \<uu>]\<rangle>.\<rbrakk>\<^sub>l\<^sub>h \<rho> \<sigma>"
        using \<rho>'_def by force
      moreover
      have "(\<forall>rh\<in>set [\<^bold>\<not>BV [Cst\<^sub>N q, \<uu>], init[\<uu>]]. \<lbrakk>rh\<rbrakk>\<^sub>r\<^sub>h \<rho> \<sigma>) \<longrightarrow> \<lbrakk>CBV\<langle>[Cst\<^sub>N q, \<uu>]\<rangle>.\<rbrakk>\<^sub>l\<^sub>h \<rho> \<sigma>"
      proof -
        have "CBV\<langle>[Cst\<^sub>N q, \<uu>]\<rangle> :- [\<^bold>\<not>BV [Cst\<^sub>N q, \<uu>], init[\<uu>]] . \<in> ana_pg_fw_must"
          unfolding a_may.ana_pg_fw_may_def a_may.ana_CBV_def by auto
        then have "\<rho> \<Turnstile>\<^sub>c\<^sub>l\<^sub>s CBV\<langle>[Cst\<^sub>N q, \<uu>]\<rangle> :- [\<^bold>\<not>BV [Cst\<^sub>N q, \<uu>], init [\<uu>]] ."
          using assms(2) unfolding least_solution_def
          unfolding solves_program_def
          by auto
        then show "(\<forall>rh\<in>set [\<^bold>\<not>BV [Cst\<^sub>N q, \<uu>], init[\<uu>]]. \<lbrakk>rh\<rbrakk>\<^sub>r\<^sub>h \<rho> \<sigma>) \<longrightarrow> \<lbrakk>CBV\<langle>[Cst\<^sub>N q, \<uu>]\<rangle>.\<rbrakk>\<^sub>l\<^sub>h \<rho> \<sigma>"
          unfolding solves_cls_def meaning_cls.simps by auto
      qed
      ultimately
      show ?thesis
        using Diff_iff \<rho>'_def empty_iff meaning_cls.simps meaning_rh.simps(3) set_ConsD set_empty2 by auto
    qed
  qed

  have \<rho>'_off_the_CBV: "\<forall>p. p \<noteq> the_CBV \<longrightarrow> \<rho>' p = \<rho> p"
    unfolding \<rho>'_def by auto
  
  have "\<rho> \<Turnstile>\<^sub>d\<^sub>l (ana_pg_fw_must - {a_may.ana_CBV q})"
    using assms(2) unfolding least_solution_def solves_program_def by auto
  have "\<rho>' \<Turnstile>\<^sub>d\<^sub>l (ana_pg_fw_must - {a_may.ana_CBV q})"
    unfolding solves_program_def
  proof 
    fix c
    assume a: "c \<in> ana_pg_fw_must - {a_may.ana_CBV q}"
    then obtain p ids rhs where c_def: "c = Cls p ids rhs"
      by (cases c) auto

    from a have a': "c \<in> \<Union> (a_may.ana_edge_BV ` a_may.edge_set) \<or> 
          c \<in> \<Union> (a_may.ana_init_BV ` (analysis_dom - d_init)) \<or>
          c \<in> \<Union> (a_may.ana_kill_BV_edge ` a_may.edge_set) \<or>
          c \<in> \<Union> (a_may.ana_gen_BV_edge ` a_may.edge_set) \<or>
          c \<in> range a_may.ana_CBV - {a_may.ana_CBV q} \<or>
          c \<in> a_may.ana_entry_node_BV"
      unfolding a_may.ana_pg_fw_may_def by auto

    have "\<rho>' \<Turnstile>\<^sub>c\<^sub>l\<^sub>s Cls p ids rhs"
      unfolding solves_cls_def
    proof (rule)
      fix \<sigma>' :: "BV_var \<Rightarrow> ('n, 'v, 'd) BV_elem"
      { 
        assume b: "Cls p ids rhs \<in> \<Union> (a_may.ana_edge_BV ` a_may.edge_set)"
        from a c_def have "\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho> \<sigma>'"
          using \<rho>_sol unfolding solves_program_def solves_cls_def by blast
        from b have "\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho>' \<sigma>'"
          apply auto
          using \<open>\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho> \<sigma>'\<close>
           apply auto
          using \<rho>'_def apply auto
          done
      }
      moreover
      {
        assume b: "Cls p ids rhs \<in> \<Union> (a_may.ana_init_BV ` (analysis_dom - d_init))"
        from a c_def have "\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho> \<sigma>'"
          using \<rho>_sol unfolding solves_program_def solves_cls_def by blast
        from b have "\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho>' \<sigma>'"
          apply auto
          using \<open>\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho> \<sigma>'\<close>
          apply auto
          using \<rho>'_def apply auto
          using a_may.ana_init_BV_def apply auto
          done
      }
      moreover
      {
        assume b: "Cls p ids rhs \<in> \<Union> (a_may.ana_kill_BV_edge ` a_may.edge_set)"
        from a c_def have "\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho> \<sigma>'"
          using \<rho>_sol unfolding solves_program_def solves_cls_def by blast
        from b have "\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho>' \<sigma>'"
          apply auto
          using \<open>\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho> \<sigma>'\<close>
          apply auto
          using \<rho>'_def apply auto
           apply (simp add: a_may.ana_kill_BV_edge_def image_iff)
          apply (simp add: a_may.ana_kill_BV_edge_def image_iff)
          done
      }
      moreover
      {
        assume b: "Cls p ids rhs \<in> \<Union> (a_may.ana_gen_BV_edge ` a_may.edge_set)"
        from a c_def have "\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho> \<sigma>'"
          using \<rho>_sol unfolding solves_program_def solves_cls_def by blast
        from b have "\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho>' \<sigma>'"
          apply auto
          using \<open>\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho> \<sigma>'\<close>
          apply auto
          using \<rho>'_def apply auto
           apply (simp add: a_may.ana_gen_BV_edge_def image_iff)+
          done
      }
      moreover
      {
        assume "Cls p ids rhs \<in> range a_may.ana_CBV - {a_may.ana_CBV q}"
        then have "\<exists>q'. p = the_CBV \<and> ids = [Cst\<^sub>N q', \<uu>] \<and> q' \<noteq> q"
          unfolding a_may.ana_CBV_def by auto
        then obtain q' where yah: "p = the_CBV \<and> ids = [Cst\<^sub>N q', \<uu>] \<and> q' \<noteq> q"
          by auto
        have "\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho>' \<sigma>'"
        proof (cases "\<sigma>' the_\<uu> = Elem d")
          case True
          then have "p = the_CBV \<and> ids = [Cst\<^sub>N q', \<uu>] \<and> \<sigma>' the_\<uu> = Elem d"
            using yah by auto
          then have p_def: "p = the_CBV"
            by auto
          from yah have ids_def: "ids = [Cst\<^sub>N q', \<uu>]"
            by auto
          from True have \<eta>v: "\<sigma>' the_\<uu> = Elem d"
            by auto

          have rhs_def: "rhs = [\<^bold>\<not>BV [Cst\<^sub>N q', \<uu>],init[\<uu>]]"
            using a c_def apply auto unfolding a_may.ana_pg_fw_may_def
            apply auto
            unfolding a_may.ana_CBV_def
                    apply auto
            using p_def apply auto
            using a_may.ana_init_BV_def  apply auto[1]
            using a_may.ana_init_BV_def apply blast
            using \<open>Cls p ids rhs \<in> range a_may.ana_CBV - {a_may.ana_CBV q}\<close> \<open>p = the_CBV \<and> ids = [Cst\<^sub>N q', \<uu>] \<and> \<sigma>' the_\<uu> = Elem d\<close> a_may.ana_CBV_def apply force
            using a_may.ana_kill_BV_edge_def apply auto[1]
                apply (simp add: a_may.ana_gen_BV_edge_def image_iff)
               apply (simp add: a_may.ana_gen_BV_edge_def image_iff)
            using ids_def apply fastforce
            using a_may.ana_entry_node_BV_def apply blast
            using a_may.ana_entry_node_BV_def apply blast
            done
          have "\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho> \<sigma>'"
            by (metis \<open>\<rho> \<Turnstile>\<^sub>d\<^sub>l (ana_pg_fw_must - {a_may.ana_CBV q})\<close> a c_def solves_cls_def solves_program_def)
          then show ?thesis
            apply -
            unfolding p_def ids_def rhs_def
            unfolding meaning_cls.simps
            apply simp
            unfolding \<eta>v
            apply clarify
            unfolding \<rho>'_def
            apply auto
            using assms(3) by blast
        next
          case False
          then have False': "\<sigma>' the_\<uu> \<noteq> Elem d"
            by auto
          from yah have p_def: "p = the_CBV"
            by auto
          from yah have ids_def: "ids = [Cst\<^sub>N q', \<uu>]"
            by auto
          have rhs_def: "rhs = [\<^bold>\<not>BV [Cst\<^sub>N q', \<uu>],init[\<uu>]]"
            using a c_def apply auto unfolding a_may.ana_pg_fw_may_def
            apply auto
            unfolding a_may.ana_CBV_def
                    apply auto
            using p_def apply auto
            using a_may.ana_init_BV_def  apply auto[1]
            using a_may.ana_init_BV_def apply blast
            using a_may.ana_kill_BV_edge_def apply auto[1]
            using a_may.ana_kill_BV_edge_def apply auto[1]
                apply (simp add: a_may.ana_gen_BV_edge_def image_iff)
               apply (simp add: a_may.ana_gen_BV_edge_def image_iff)
            using yah apply force
            using a_may.ana_entry_node_BV_def apply blast
            using a_may.ana_entry_node_BV_def apply blast
            done

          have "\<lbrakk>CBV\<langle>[Cst\<^sub>N q', \<uu>]\<rangle> :- [\<^bold>\<not>BV [Cst\<^sub>N q', \<uu>], init [\<uu>]] .\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho> \<sigma>'"
            using \<open>Cls p ids rhs \<in> range a_may.ana_CBV - {a_may.ana_CBV q}\<close>
            unfolding p_def[symmetric] rhs_def[symmetric] 
            unfolding ids_def[symmetric]
            using assms(1)
            unfolding least_solution_def
            unfolding a_may.ana_pg_fw_may_def
            by (metis \<open>\<rho> \<Turnstile>\<^sub>d\<^sub>l (ana_pg_fw_must - {a_may.ana_CBV q})\<close> a c_def solves_cls_def solves_program_def)
          then have "\<lbrakk>CBV\<langle>[Cst\<^sub>N q', \<uu>]\<rangle> :- [\<^bold>\<not>BV [Cst\<^sub>N q', \<uu>], init [\<uu>]] .\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho>' \<sigma>'"
            unfolding \<rho>'_def 
            apply auto
            using False'
            apply blast
            done
          then show ?thesis
            unfolding p_def ids_def rhs_def by auto
        qed
      }
      moreover
      {
        assume b: "Cls p ids rhs \<in> a_may.ana_entry_node_BV"
        from a c_def have "\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho> \<sigma>'"
          using assms(1)
          unfolding least_solution_def solves_program_def solves_cls_def
          by (metis \<open>\<rho> \<Turnstile>\<^sub>d\<^sub>l (ana_pg_fw_must - {a_may.ana_CBV q})\<close> solves_cls_def solves_program_def)
        from b have "\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho>' \<sigma>'"
          apply auto
          using \<open>\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho> \<sigma>'\<close>
          apply auto
          using \<rho>'_def apply auto
          using a_may.ana_entry_node_BV_def apply fastforce
          using a_may.ana_entry_node_BV_def apply blast   
          done
      }
      ultimately
      show "\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho>' \<sigma>'"
        using a' using c_def by metis
    qed
    then show "\<rho>' \<Turnstile>\<^sub>c\<^sub>l\<^sub>s c"
      unfolding c_def by auto
  qed
  then have "\<rho>' \<Turnstile>\<^sub>d\<^sub>l ana_pg_fw_must"
    using CBV_solves unfolding a_may.ana_CBV_def solves_program_def
    by auto
  moreover
  have "\<rho>' \<sqsubset>s_BV\<sqsubset> \<rho>"
  proof -
    have "\<rho>' the_CBV \<subset> \<rho> the_CBV"
      using Diff_iff \<rho>'_def assms(1) by fastforce
    moreover
    have "\<forall>p'. s_BV p' = s_BV the_CBV \<longrightarrow> \<rho>' p' \<subseteq> \<rho> p'"
      by (simp add: \<rho>'_def)
    moreover
    have "\<forall>p'. s_BV p' < s_BV the_CBV \<longrightarrow> \<rho>' p' = \<rho> p'"
      by (metis \<rho>'_off_the_CBV nat_neq_iff)
    ultimately
    show "\<rho>' \<sqsubset>s_BV\<sqsubset> \<rho>"
      unfolding lt_def by blast
  qed
  ultimately
  show "False"
    using \<open>\<rho> \<Turnstile>\<^sub>m\<^sub>i\<^sub>n ana_pg_fw_must s_BV\<close> minimal_solution_def
    by blast 
qed

lemma not_CBV2:
  assumes "\<rho> \<Turnstile>\<^sub>l\<^sub>s\<^sub>t ana_pg_fw_must s_BV"
  assumes "\<rho> \<Turnstile>\<^sub>f CBV\<langle>[Cst\<^sub>N q, Cst\<^sub>E d]\<rangle>."
  assumes "\<rho> \<Turnstile>\<^sub>f BV\<langle>[Cst\<^sub>N q, Cst\<^sub>E d]\<rangle>."
  shows "False"
proof -
  have "[Node q, Elem d] \<in> \<rho> the_CBV"
    using assms(2)
    unfolding solves_fact.simps
    unfolding meaning_fact.simps
    by auto
  moreover
  have "[Node q, Elem d] \<in> \<rho> the_BV"
    using assms(3)
    unfolding solves_fact.simps
    unfolding meaning_fact.simps
    by auto
  ultimately
  show "False"
    using not_CBV[of q d \<rho>] assms(1) by auto
qed

thm analysis_BV_forward_may.not_kill

lemma not_init_node:
  assumes "\<rho> \<Turnstile>\<^sub>l\<^sub>s\<^sub>t ana_pg_fw_must s_BV"
  shows "\<not>\<rho> \<Turnstile>\<^sub>f init\<langle>[Cst\<^sub>N q]\<rangle>."
proof -
  have "\<forall>\<sigma>. \<lbrakk>\<^bold>\<not> the_init [Cst\<^sub>N q]\<rbrakk>\<^sub>r\<^sub>h \<rho> \<sigma>"
  proof 
    fix \<sigma> 
    have "finite ana_pg_fw_must"
      using a_may.ana_pg_fw_may_finite by auto
    moreover
    have "\<rho> \<Turnstile>\<^sub>l\<^sub>s\<^sub>t ana_pg_fw_must s_BV"
      using assms by blast
    moreover
    have "strat_wf s_BV ana_pg_fw_must"
      using a_may.ana_pg_fw_may_stratified by blast
    moreover
    have "\<forall>c\<in>ana_pg_fw_must --s_BV-- s_BV the_init. 
            \<forall>\<sigma>'. (the_lh c \<cdot>\<^sub>v\<^sub>l\<^sub>h \<sigma>') = (init\<langle>[Cst\<^sub>N q]\<rangle>. \<cdot>\<^sub>v\<^sub>l\<^sub>h \<sigma>) \<longrightarrow> \<not> \<lbrakk>the_rhs c\<rbrakk>\<^sub>r\<^sub>h\<^sub>s \<rho> \<sigma>'"
    proof (rule, rule, rule)
      fix c \<sigma>'
      assume "(the_lh c \<cdot>\<^sub>v\<^sub>l\<^sub>h \<sigma>') = (init\<langle>[Cst\<^sub>N q]\<rangle>. \<cdot>\<^sub>v\<^sub>l\<^sub>h \<sigma>)"
      moreover
      assume "c \<in> (ana_pg_fw_must --s_BV-- s_BV the_init)"
      then have "c \<in> (ana_pg_fw_must --s_BV-- 0)"
        by auto
      ultimately
      show "\<not> \<lbrakk>the_rhs c\<rbrakk>\<^sub>r\<^sub>h\<^sub>s \<rho> \<sigma>'"
        unfolding a_may.ana_pg_fw_may_def a_may.ana_init_BV_def a_may.ana_kill_BV_edge_def a_may.ana_gen_BV_edge_def a_may.ana_CBV_def a_may.ana_entry_node_BV_def
        by auto
    qed
    ultimately
    show "\<lbrakk>\<^bold>\<not> the_init [Cst\<^sub>N q]\<rbrakk>\<^sub>r\<^sub>h \<rho> \<sigma>"
      using meaning_neg_rh[of ana_pg_fw_must \<rho> s_BV the_init "[Cst\<^sub>N q]" \<sigma>] by auto
  qed
  then show ?thesis
    by auto
qed

lemma not_init_action: (* Copy paste adapt from not_init_node. They are kind of special cases of meaning_neg_rh because *)
  assumes "\<rho> \<Turnstile>\<^sub>l\<^sub>s\<^sub>t ana_pg_fw_must s_BV"
  shows "\<not>\<rho> \<Turnstile>\<^sub>f init\<langle>[Cst\<^sub>A q]\<rangle>."
proof -
  have "\<forall>\<sigma>. \<lbrakk>\<^bold>\<not> the_init [Cst\<^sub>A q]\<rbrakk>\<^sub>r\<^sub>h \<rho> \<sigma>"
  proof 
    fix \<sigma> 
    have "finite ana_pg_fw_must"
      using a_may.ana_pg_fw_may_finite by blast
    moreover
    have "\<rho> \<Turnstile>\<^sub>l\<^sub>s\<^sub>t ana_pg_fw_must s_BV"
      using assms by blast
    moreover
    have "strat_wf s_BV ana_pg_fw_must"
      using a_may.ana_pg_fw_may_stratified by blast
    moreover
    have "\<forall>c\<in>ana_pg_fw_must --s_BV-- s_BV the_init. 
            \<forall>\<sigma>'. (the_lh c \<cdot>\<^sub>v\<^sub>l\<^sub>h \<sigma>') = (init\<langle>[Cst\<^sub>A q]\<rangle>. \<cdot>\<^sub>v\<^sub>l\<^sub>h \<sigma>) \<longrightarrow> \<not> \<lbrakk>the_rhs c\<rbrakk>\<^sub>r\<^sub>h\<^sub>s \<rho> \<sigma>'"
    proof (rule, rule, rule)
      fix c \<sigma>'
      assume "(the_lh c \<cdot>\<^sub>v\<^sub>l\<^sub>h \<sigma>') = (init\<langle>[Cst\<^sub>A q]\<rangle>. \<cdot>\<^sub>v\<^sub>l\<^sub>h \<sigma>)"
      moreover
      assume "c \<in> (ana_pg_fw_must --s_BV-- s_BV the_init)"
      then have "c \<in> (ana_pg_fw_must --s_BV-- 0)"
        by auto
      ultimately
      show "\<not> \<lbrakk>the_rhs c\<rbrakk>\<^sub>r\<^sub>h\<^sub>s \<rho> \<sigma>'"
        unfolding a_may.ana_pg_fw_may_def a_may.ana_init_BV_def a_may.ana_kill_BV_edge_def a_may.ana_gen_BV_edge_def a_may.ana_CBV_def a_may.ana_entry_node_BV_def
        by auto
    qed
    ultimately
    show " \<lbrakk>\<^bold>\<not> the_init [Cst\<^sub>A q]\<rbrakk>\<^sub>r\<^sub>h \<rho> \<sigma>"
      using meaning_neg_rh[of ana_pg_fw_must \<rho> s_BV the_init "[Cst\<^sub>A q]" \<sigma>] by auto
  qed
  then show ?thesis
    by auto
qed

lemma is_Cst_if_init:
  assumes "\<rho> \<Turnstile>\<^sub>l\<^sub>s\<^sub>t ana_pg_fw_must s_BV"
  assumes "\<rho> \<Turnstile>\<^sub>f init\<langle>[d]\<rangle>."
  shows "is_Cst d"
proof (cases d)
  case (Var x)
  then have "\<rho> \<Turnstile>\<^sub>f init\<langle>[Var x]\<rangle>."
    using Var assms(2) by auto
  then have "\<rho> \<Turnstile>\<^sub>f init\<langle>[Cst\<^sub>N undefined]\<rangle>."
    by auto
  then have "False"
    using assms(1) not_init_node by blast
  then show ?thesis 
    by metis
next
  case (Cst e)
  then show ?thesis 
    by auto
qed

lemma is_bv_elem_if_init:
  assumes "\<rho> \<Turnstile>\<^sub>l\<^sub>s\<^sub>t ana_pg_fw_must s_BV"
  assumes "\<rho> \<Turnstile>\<^sub>f init\<langle>[Cst d]\<rangle>."
  shows "is_bv_elem d"
proof (cases "d")
  case (Node x1)
  then show ?thesis
    using assms(1) assms(2) not_init_node by blast
next
  case (Elem x2)
  then show ?thesis
    by simp
next
  case (BV_Action x3)
  then show ?thesis
    using assms(1) assms(2) not_init_action by blast
qed

lemma in_analysis_dom_if_init': (* init, like kill and gen doesn't have righthandsides, so we could make a lemma like uuuuuuuuh_aaa for this case??? *)
  assumes "\<rho> \<Turnstile>\<^sub>l\<^sub>s\<^sub>t ana_pg_fw_must s_BV"
  assumes "\<rho> \<Turnstile>\<^sub>f init\<langle>[Cst\<^sub>E d]\<rangle>."
  shows "d \<in> analysis_dom"
proof -
  have "\<forall>\<sigma> :: BV_var \<Rightarrow> ('n, 'v, 'd) BV_elem. d \<in> analysis_dom"
  proof
    fix \<sigma>
    have "finite ana_pg_fw_must"
      using a_may.ana_pg_fw_may_finite by blast
    moreover
    have "\<rho> \<Turnstile>\<^sub>l\<^sub>s\<^sub>t ana_pg_fw_must s_BV"
      using assms(1) by blast
    moreover
    have "strat_wf s_BV ana_pg_fw_must"
      using a_may.ana_pg_fw_may_stratified by blast
    moreover
    have "\<lbrakk>init [Cst\<^sub>E d]\<rbrakk>\<^sub>r\<^sub>h \<rho> \<sigma>"
      using assms(2) by auto
    ultimately
    have "\<exists>c\<in>ana_pg_fw_must --s_BV-- s_BV the_init. \<exists>\<sigma>'. (the_lh c \<cdot>\<^sub>v\<^sub>l\<^sub>h \<sigma>') = (init\<langle>[Cst\<^sub>E d]\<rangle>. \<cdot>\<^sub>v\<^sub>l\<^sub>h \<sigma>) \<and> \<lbrakk>the_rhs c\<rbrakk>\<^sub>r\<^sub>h\<^sub>s \<rho> \<sigma>'"
      using uuuuuuuuh_aaa[of ana_pg_fw_must \<rho> s_BV the_init "[Cst\<^sub>E d]" \<sigma>] by auto
    then have "d \<in> analysis_dom - d_init"
      unfolding a_may.ana_pg_fw_may_def a_may.ana_init_BV_def a_may.ana_kill_BV_edge_def a_may.ana_gen_BV_edge_def a_may.ana_CBV_def
        a_may.ana_entry_node_BV_def
      by auto
    then show "d \<in> analysis_dom"
      by blast
  qed
  then show "d \<in> analysis_dom"
    by metis
qed

lemma in_analysis_dom_if_init:
  assumes "\<rho> \<Turnstile>\<^sub>l\<^sub>s\<^sub>t ana_pg_fw_must s_BV"
  assumes "\<rho> \<Turnstile>\<^sub>f init\<langle>[d]\<rangle>."
  shows "Decode_Elem d \<in> analysis_dom"
proof -
  have "is_Cst d"
    using assms(1) assms(2) is_Cst_if_init by blast
  then obtain d' where "d = Cst d'"
    by (meson is_Cst_def)
  then obtain d'' where "d' = Elem d''"
    using is_bv_elem_if_init[OF assms(1)] assms(2)
    apply (cases d')
    apply auto
    using assms(1) assms(2) not_init_node apply blast
    using assms(1) assms(2) not_init_action apply blast
    done

  show ?thesis
    using \<open>d = Cst d'\<close> \<open>d' = Elem d''\<close> assms(1) assms(2) in_analysis_dom_if_init' by auto
qed

thm not_init_action

(*
lemma init_if_CBV':
  assumes "least_solution \<rho> ana_pg_BV s_BV"
  assumes "\<lbrakk>CBV\<langle>[\<pi>_end, d]\<rangle>.\<rbrakk>\<^sub>f \<rho> \<sigma>"
  shows "\<lbrakk>init\<langle>[d]\<rangle>.\<rbrakk>\<^sub>f \<rho> \<sigma>"
(* Okay, det kan da godt være men hvad hvis du man var i en situation hvor d'et i CBV og d'et i init havde forskellige variable.
   I det tilfælde skal man måske sige "der er en renaming".

 *)
proof -

  thm uuuuuuuuh_aaa[of ana_pg_BV \<rho> s_BV the_CBV "[\<pi>_end, d]" \<sigma>]
*)

lemma init_if_CBV:
  assumes "\<rho> \<Turnstile>\<^sub>l\<^sub>s\<^sub>t ana_pg_fw_must s_BV"
  assumes "\<rho> \<Turnstile>\<^sub>f CBV\<langle>[\<pi>_end, d]\<rangle>."
  shows "\<rho> \<Turnstile>\<^sub>f init\<langle>[d]\<rangle>."
proof (rule ccontr) (* Proof copy paste and adapted from not_init_action *)
  assume asm: "\<not> \<rho> \<Turnstile>\<^sub>f init\<langle>[d]\<rangle>."
  then have "\<exists>\<sigma>. \<not>[\<lbrakk>d\<rbrakk>\<^sub>i\<^sub>d \<sigma>] \<in> \<rho> the_init"
    by auto
  then obtain \<sigma> where asm': "\<not>[\<lbrakk>d\<rbrakk>\<^sub>i\<^sub>d \<sigma>] \<in> \<rho> the_init"
    by auto

  have "finite ana_pg_fw_must"
    using a_may.ana_pg_fw_may_finite by auto
  then have "\<rho> \<Turnstile>\<^sub>l\<^sub>s\<^sub>t ana_pg_fw_must s_BV"
    using downward_least_solution2[of ana_pg_fw_must s_BV \<rho> 2] assms(2)
    using a_may.ana_pg_fw_may_stratified assms(1) by blast 
  then have "\<rho> \<Turnstile>\<^sub>m\<^sub>i\<^sub>n ana_pg_fw_must s_BV"
    using least_is_minimal[of]
    using strat_wf_mod_if_strat_wf \<open>finite ana_pg_fw_must\<close> finite_below_finite
    by (smt (verit) a_may.ana_pg_fw_may_stratified) 
  moreover

  define \<rho>' where "\<rho>' = (\<lambda>p. (if p = the_CBV then (\<rho> the_CBV) - {[\<lbrakk>\<pi>_end\<rbrakk>\<^sub>i\<^sub>d \<sigma>, \<lbrakk>d\<rbrakk>\<^sub>i\<^sub>d \<sigma>]} else \<rho> p))"

  have "\<rho>' \<Turnstile>\<^sub>d\<^sub>l ana_pg_fw_must"
    unfolding solves_program_def
  proof
    fix c
    assume a: "c \<in> ana_pg_fw_must
"
    then obtain p ids rhs where c_def: "c = Cls p ids rhs"
      by (cases c) auto

    from a have a': "c \<in> \<Union> (a_may.ana_edge_BV ` a_may.edge_set) \<or> 
          c \<in> \<Union> (a_may.ana_init_BV ` (analysis_dom - d_init)) \<or>
          c \<in> \<Union> (a_may.ana_kill_BV_edge ` a_may.edge_set) \<or>
          c \<in> \<Union> (a_may.ana_gen_BV_edge ` a_may.edge_set) \<or>
          c \<in> a_may.ana_CBV ` UNIV \<or>
          c \<in> a_may.ana_entry_node_BV"
      unfolding a_may.ana_pg_fw_may_def by auto

    have "\<rho>' \<Turnstile>\<^sub>c\<^sub>l\<^sub>s Cls p ids rhs"
      unfolding solves_cls_def
    proof (rule)
      fix \<sigma>' :: "BV_var \<Rightarrow> ('n, 'v, 'd) BV_elem"
      { 
        assume b: "Cls p ids rhs \<in> \<Union> (a_may.ana_edge_BV ` a_may.edge_set)"
        from a c_def have "\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho> \<sigma>'"
          using assms(1)
          unfolding least_solution_def solves_program_def solves_cls_def by metis
        from b have "\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho>' \<sigma>'"
          apply auto
          using \<open>\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho> \<sigma>'\<close>
           apply auto
          using \<rho>'_def apply auto
          done
      }
      moreover
      {
        assume b: "Cls p ids rhs \<in> \<Union> (a_may.ana_init_BV ` (analysis_dom - d_init))"
        from a c_def have "\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho> \<sigma>'"
          using assms(1)
          unfolding least_solution_def solves_program_def solves_cls_def by metis
        from b have "\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho>' \<sigma>'"
          apply auto
          using \<open>\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho> \<sigma>'\<close>
          apply auto
          using \<rho>'_def apply auto
          using a_may.ana_init_BV_def apply auto
          done
      }
      moreover
      {
        assume b: "Cls p ids rhs \<in> \<Union> (a_may.ana_kill_BV_edge ` a_may.edge_set)"
        from a c_def have "\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho> \<sigma>'"
          using assms(1)
          unfolding least_solution_def solves_program_def solves_cls_def by metis
        from b have "\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho>' \<sigma>'"
          apply auto
          using \<open>\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho> \<sigma>'\<close>
          apply auto
          using \<rho>'_def apply auto
           apply (simp add: a_may.ana_kill_BV_edge_def image_iff)
          apply (simp add: a_may.ana_kill_BV_edge_def image_iff)
          done
      }
      moreover
      {
        assume b: "Cls p ids rhs \<in> \<Union> (a_may.ana_gen_BV_edge ` a_may.edge_set)"
        from a c_def have "\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho> \<sigma>'"
          using assms(1)
          unfolding least_solution_def solves_program_def solves_cls_def by metis
        from b have "\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho>' \<sigma>'"
          apply auto
          using \<open>\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho> \<sigma>'\<close>
          apply auto
          using \<rho>'_def apply auto
           apply (simp add: a_may.ana_gen_BV_edge_def image_iff)+
          done
      }
      moreover
      {
        assume "Cls p ids rhs \<in> a_may.ana_CBV ` UNIV"
        then have "\<exists>q'. p = the_CBV \<and> ids = [Cst\<^sub>N q', \<uu>]"
          unfolding a_may.ana_CBV_def by blast
        then obtain q' where yah: "p = the_CBV \<and> ids = [Cst\<^sub>N q', \<uu>]"
          by auto
        have "\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho>' \<sigma>'"
        proof (cases "\<sigma>' the_\<uu> = \<lbrakk>d\<rbrakk>\<^sub>i\<^sub>d \<sigma>")
          case True
          then have "p = the_CBV \<and> ids = [Cst\<^sub>N q', \<uu>] \<and> \<sigma>' the_\<uu> = \<lbrakk>d\<rbrakk>\<^sub>i\<^sub>d \<sigma>"
            using yah by auto
          then have p_def: "p = the_CBV"
            by auto
          from yah have ids_def: "ids = [Cst\<^sub>N q', \<uu>]"
            by auto
          from True have \<eta>v: "\<sigma>' the_\<uu> = \<lbrakk>d\<rbrakk>\<^sub>i\<^sub>d \<sigma>"
            by auto

          have rhs_def: "rhs = [\<^bold>\<not>BV [Cst\<^sub>N q', \<uu>],init[\<uu>]]"
            using a c_def apply auto unfolding a_may.ana_pg_fw_may_def
            apply auto
            unfolding a_may.ana_CBV_def
                    apply auto
            using p_def apply auto
            using a_may.ana_init_BV_def  apply auto[1]
              apply (simp add: a_may.ana_kill_BV_edge_def image_iff)
             apply (simp add: a_may.ana_gen_BV_edge_def image_iff)
            using ids_def apply fastforce
            using a_may.ana_entry_node_BV_def apply blast
            done
          show ?thesis
            unfolding p_def ids_def rhs_def
            unfolding meaning_cls.simps
            apply simp
            unfolding \<eta>v
            apply clarify
            unfolding \<rho>'_def
            apply auto
            using asm'
            apply auto
            done
        next
          case False
          then have False': "\<not>\<sigma>' the_\<uu> = \<lbrakk>d\<rbrakk>\<^sub>i\<^sub>d \<sigma>"
            by auto
          from yah have p_def: "p = the_CBV"
            by auto
          from yah have ids_def: "ids = [Cst\<^sub>N q', \<uu>]"
            by auto
          have rhs_def: "rhs = [\<^bold>\<not>BV [Cst\<^sub>N q', \<uu>],init[\<uu>]]"
            using a c_def apply auto unfolding a_may.ana_pg_fw_may_def
            apply auto
            unfolding a_may.ana_CBV_def
                    apply auto
            using p_def apply auto
            using a_may.ana_init_BV_def  apply auto[1]
              apply (simp add: a_may.ana_kill_BV_edge_def image_iff)
             apply (simp add: a_may.ana_gen_BV_edge_def image_iff)
            using ids_def apply force
            using a_may.ana_entry_node_BV_def apply blast
            done

          have "\<lbrakk>CBV\<langle>[Cst\<^sub>N q', \<uu>]\<rangle> :- [\<^bold>\<not>BV [Cst\<^sub>N q', \<uu>], init [\<uu>]] .\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho> \<sigma>'"
            using \<open>Cls p ids rhs \<in> a_may.ana_CBV ` UNIV\<close>
            unfolding p_def[symmetric] rhs_def[symmetric] 
            unfolding ids_def[symmetric]
            using assms(1)
            unfolding least_solution_def
            unfolding a_may.ana_pg_fw_may_def
            apply (metis a a_may.ana_pg_fw_may_def c_def solves_cls_def solves_program_def)
            done
          then have "\<lbrakk>CBV\<langle>[Cst\<^sub>N q', \<uu>]\<rangle> :- [\<^bold>\<not>BV [Cst\<^sub>N q', \<uu>], init [\<uu>]] .\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho>' \<sigma>'"
            unfolding \<rho>'_def 
            apply auto
            using False'
            by blast
          then show ?thesis
            unfolding p_def ids_def rhs_def by auto
        qed
      }
      moreover
      {
        assume b: "Cls p ids rhs \<in> a_may.ana_entry_node_BV"
        from a c_def have "\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho> \<sigma>'"
          using assms(1)
          unfolding least_solution_def solves_program_def solves_cls_def by metis
        from b have "\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho>' \<sigma>'"
          apply auto
          using \<open>\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho> \<sigma>'\<close>
          apply auto
          using \<rho>'_def apply auto
          using a_may.ana_entry_node_BV_def apply fastforce
          using a_may.ana_entry_node_BV_def apply blast   
          done
      }
      ultimately
      show "\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho>' \<sigma>'"
        using a' using c_def by metis
    qed
    then show "\<rho>' \<Turnstile>\<^sub>c\<^sub>l\<^sub>s c"
      unfolding c_def by auto
  qed

  moreover
  have "[\<lbrakk>\<pi>_end\<rbrakk>\<^sub>i\<^sub>d \<sigma>, \<lbrakk>d\<rbrakk>\<^sub>i\<^sub>d \<sigma>] \<in> \<rho> the_CBV"
    using assms(2)
    unfolding solves_fact.simps
    apply auto
    done
  have "\<rho>' \<sqsubset>s_BV\<sqsubset> \<rho>"
  proof -
    have "\<rho>' the_CBV \<subset> \<rho> the_CBV"
      unfolding \<rho>'_def
      using \<open>[\<lbrakk>\<pi>_end\<rbrakk>\<^sub>i\<^sub>d \<sigma>, \<lbrakk>d\<rbrakk>\<^sub>i\<^sub>d \<sigma>] \<in> \<rho> the_CBV\<close> by auto 
    moreover
    have "\<forall>p'. s_BV p' = s_BV the_CBV \<longrightarrow> \<rho>' p' \<subseteq> \<rho> p'"
      unfolding \<rho>'_def by auto
    moreover
    have "\<forall>p'. s_BV p' < s_BV the_CBV \<longrightarrow> \<rho>' p' = \<rho> p'"
      unfolding \<rho>'_def by auto
    ultimately
    show "\<rho>' \<sqsubset>s_BV\<sqsubset> \<rho>"
      apply -
      unfolding lt_def
      apply (rule_tac x=the_CBV in exI)
      apply metis
      done
  qed
  ultimately
  show False
    unfolding minimal_solution_def using assms(1) by auto
qed

lemma is_Cst_if_CBV:
  assumes "\<rho> \<Turnstile>\<^sub>l\<^sub>s\<^sub>t ana_pg_fw_must s_BV"
  assumes "\<rho> \<Turnstile>\<^sub>f CBV\<langle>[\<pi>, d]\<rangle>."
  shows "is_Cst d"
  using is_Cst_if_init init_if_CBV assms by metis

lemma not_CBV_action: (* Copy paste adapt from not_init_node *)
  assumes "\<rho> \<Turnstile>\<^sub>l\<^sub>s\<^sub>t ana_pg_fw_must s_BV"
  shows "\<not>\<rho> \<Turnstile>\<^sub>f CBV\<langle>[Cst\<^sub>A q,d]\<rangle>."
proof
  assume asm_2: "\<rho> \<Turnstile>\<^sub>f CBV\<langle>[Cst\<^sub>A q,d]\<rangle>."
  then have "[BV_Action q, the_Cst d] \<in> \<rho> the_CBV"
    using is_Cst_if_CBV[OF assms(1)] by (cases d) auto

  have "finite ana_pg_fw_must"
    using a_may.ana_pg_fw_may_finite by auto
  then have "\<rho> \<Turnstile>\<^sub>l\<^sub>s\<^sub>t ana_pg_fw_must s_BV"
    using downward_least_solution2[of ana_pg_fw_must s_BV \<rho> 0] asm_2
    using a_may.ana_pg_fw_may_stratified assms(1) by blast 
  then have "\<rho> \<Turnstile>\<^sub>m\<^sub>i\<^sub>n ana_pg_fw_must s_BV"
    using least_is_minimal[of]
    using strat_wf_mod_if_strat_wf \<open>finite ana_pg_fw_must\<close> finite_below_finite
    by (smt (verit) a_may.ana_pg_fw_may_stratified) 
  moreover

  define \<rho>' where "\<rho>' = (\<lambda>p. (if p = the_CBV then (\<rho> the_CBV) - {[BV_Action q, the_Cst d]} else \<rho> p))"

  have "\<rho>' \<Turnstile>\<^sub>d\<^sub>l ana_pg_fw_must"
    unfolding solves_program_def
  proof
    fix c
    assume a: "c \<in> ana_pg_fw_must"
    then obtain p ids rhs where c_def: "c = Cls p ids rhs"
      by (cases c) auto

    from a have a': "c \<in> \<Union> (a_may.ana_edge_BV ` a_may.edge_set) \<or> 
          c \<in> \<Union> (a_may.ana_init_BV ` (analysis_dom - d_init)) \<or>
          c \<in> \<Union> (a_may.ana_kill_BV_edge ` a_may.edge_set) \<or>
          c \<in> \<Union> (a_may.ana_gen_BV_edge ` a_may.edge_set) \<or>
          c \<in> a_may.ana_CBV ` UNIV \<or>
          c \<in> a_may.ana_entry_node_BV"
      unfolding a_may.ana_pg_fw_may_def by auto

    have "\<rho>' \<Turnstile>\<^sub>c\<^sub>l\<^sub>s Cls p ids rhs"
      unfolding solves_cls_def
    proof (rule)
      fix \<sigma>' :: "BV_var \<Rightarrow> ('n, 'v, 'd) BV_elem"
      { 
        assume b: "Cls p ids rhs \<in> \<Union> (a_may.ana_edge_BV ` a_may.edge_set)"
        from a c_def have "\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho> \<sigma>'"
          using assms(1)
          unfolding least_solution_def solves_program_def solves_cls_def by metis
        from b have "\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho>' \<sigma>'"
          apply auto
          using \<open>\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho> \<sigma>'\<close>
           apply auto
          using \<rho>'_def apply auto
          done
      }
      moreover
      {
        assume b: "Cls p ids rhs \<in> \<Union> (a_may.ana_init_BV ` (analysis_dom - d_init))"
        from a c_def have "\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho> \<sigma>'"
          using assms(1)
          unfolding least_solution_def solves_program_def solves_cls_def by metis
        from b have "\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho>' \<sigma>'"
          apply auto
          using \<open>\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho> \<sigma>'\<close>
          apply auto
          using \<rho>'_def apply auto
          using a_may.ana_init_BV_def apply auto
          done
      }
      moreover
      {
        assume b: "Cls p ids rhs \<in> \<Union> (a_may.ana_kill_BV_edge ` a_may.edge_set)"
        from a c_def have "\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho> \<sigma>'"
          using assms(1)
          unfolding least_solution_def solves_program_def solves_cls_def by metis
        from b have "\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho>' \<sigma>'"
          apply auto
          using \<open>\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho> \<sigma>'\<close>
          apply auto
          using \<rho>'_def apply auto
           apply (simp add: a_may.ana_kill_BV_edge_def image_iff)
          apply (simp add: a_may.ana_kill_BV_edge_def image_iff)
          done
      }
      moreover
      {
        assume b: "Cls p ids rhs \<in> \<Union> (a_may.ana_gen_BV_edge ` a_may.edge_set)"
        from a c_def have "\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho> \<sigma>'"
          using assms(1)
          unfolding least_solution_def solves_program_def solves_cls_def by metis
        from b have "\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho>' \<sigma>'"
          apply auto
          using \<open>\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho> \<sigma>'\<close>
          apply auto
          using \<rho>'_def apply auto
           apply (simp add: a_may.ana_gen_BV_edge_def image_iff)+
          done
      }
      moreover
      {
        assume "Cls p ids rhs \<in> a_may.ana_CBV ` UNIV"
        then have "\<exists>q'. p = the_CBV \<and> ids = [Cst\<^sub>N q', \<uu>]"
          unfolding a_may.ana_CBV_def by blast
        then obtain q' where yah: "p = the_CBV \<and> ids = [Cst\<^sub>N q', \<uu>]"
          by auto
        have "\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho>' \<sigma>'"
        proof (cases "\<sigma>' the_\<uu> = the_Cst d")
          case True
          then have "p = the_CBV \<and> ids = [Cst\<^sub>N q', \<uu>] \<and> \<sigma>' the_\<uu> = the_Cst d"
            using yah by auto
          then have p_def: "p = the_CBV"
            by auto
          from yah have ids_def: "ids = [Cst\<^sub>N q', \<uu>]"
            by auto
          from True have \<eta>v: "\<sigma>' the_\<uu> = the_Cst d"
            by auto

          have rhs_def: "rhs = [\<^bold>\<not>BV [Cst\<^sub>N q', \<uu>],init[\<uu>]]"
            using a c_def apply auto unfolding a_may.ana_pg_fw_may_def
            apply auto
            unfolding a_may.ana_CBV_def
                    apply auto
            using p_def apply auto
            using a_may.ana_init_BV_def  apply auto[1]
              apply (simp add: a_may.ana_kill_BV_edge_def image_iff)
             apply (simp add: a_may.ana_gen_BV_edge_def image_iff)
            using a_may.ana_entry_node_BV_def
            using ids_def apply force
            using a_may.ana_entry_node_BV_def apply blast
            done
          have "\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho> \<sigma>'"
            using a assms c_def least_solution_def solves_cls_def solves_program_def by blast
          then show ?thesis
            unfolding p_def ids_def rhs_def
            unfolding meaning_cls.simps
            apply simp
            unfolding \<eta>v
            apply clarify
            unfolding \<rho>'_def
            apply auto
            done
        next
          case False
          then have False': "\<not>\<sigma>' the_\<uu> = the_Cst d"
            by auto
          from yah have p_def: "p = the_CBV"
            by auto
          from yah have ids_def: "ids = [Cst\<^sub>N q', \<uu>]"
            by auto
          have rhs_def: "rhs = [\<^bold>\<not>BV [Cst\<^sub>N q', \<uu>],init[\<uu>]]"
            using a c_def apply auto unfolding a_may.ana_pg_fw_may_def
            apply auto
            unfolding a_may.ana_CBV_def
                    apply auto
            using p_def apply auto
            using a_may.ana_init_BV_def  apply auto[1]
              apply (simp add: a_may.ana_kill_BV_edge_def image_iff)
             apply (simp add: a_may.ana_gen_BV_edge_def image_iff)
            using a_may.ana_entry_node_BV_def
            using ids_def apply force
            using a_may.ana_entry_node_BV_def apply blast 
            done

          have "\<lbrakk>CBV\<langle>[Cst\<^sub>N q', \<uu>]\<rangle> :- [\<^bold>\<not>BV [Cst\<^sub>N q', \<uu>], init [\<uu>]] .\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho> \<sigma>'"
            using \<open>Cls p ids rhs \<in> a_may.ana_CBV ` UNIV\<close>
            unfolding p_def[symmetric] rhs_def[symmetric] 
            unfolding ids_def[symmetric]
            using assms(1)
            unfolding least_solution_def
            unfolding a_may.ana_pg_fw_may_def
            by (meson Un_iff solves_cls_def solves_program_def)
          then have "\<lbrakk>CBV\<langle>[Cst\<^sub>N q', \<uu>]\<rangle> :- [\<^bold>\<not>BV [Cst\<^sub>N q', \<uu>], init [\<uu>]] .\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho>' \<sigma>'"
            unfolding \<rho>'_def 
            apply auto
            done
          then show ?thesis
            unfolding p_def ids_def rhs_def by auto
        qed
      }
      moreover
      {
        assume b: "Cls p ids rhs \<in> a_may.ana_entry_node_BV"
        from a c_def have "\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho> \<sigma>'"
          using assms(1)
          unfolding least_solution_def solves_program_def solves_cls_def by metis
        from b have "\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho>' \<sigma>'"
          apply auto
          using \<open>\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho> \<sigma>'\<close>
          apply auto
          using \<rho>'_def apply auto
          using a_may.ana_entry_node_BV_def apply fastforce
          using a_may.ana_entry_node_BV_def apply blast   
          done
      }
      ultimately
      show "\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho>' \<sigma>'"
        using a' using c_def by metis
    qed
    then show "\<rho>' \<Turnstile>\<^sub>c\<^sub>l\<^sub>s c"
      unfolding c_def by auto
  qed
  moreover
  have "\<rho>' \<sqsubset>s_BV\<sqsubset> \<rho>"
  proof -
    have "\<rho>' the_CBV \<subset> \<rho> the_CBV"
      unfolding \<rho>'_def using \<open>[BV_Action q, identifier.the_Cst d] \<in> \<rho> the_CBV\<close> by auto
    moreover
    have "\<forall>p'. s_BV p' = s_BV the_kill \<longrightarrow> \<rho>' p' \<subseteq> \<rho>  p'"
      unfolding \<rho>'_def by auto
    moreover
    have "\<forall>p'. s_BV p' < s_BV the_kill \<longrightarrow> \<rho>' p' = \<rho> p'"
      unfolding \<rho>'_def by auto
    ultimately
    show "\<rho>' \<sqsubset>s_BV\<sqsubset> \<rho>"
      unfolding lt_def by (metis \<rho>'_def dual_order.refl order_less_irrefl psubset_imp_subset) 
  qed
  ultimately
  show False
    unfolding minimal_solution_def by auto
qed

lemma is_encode_elem_if_CBV_right_arg:
  assumes "\<rho> \<Turnstile>\<^sub>l\<^sub>s\<^sub>t ana_pg_fw_must s_BV"
  assumes "\<rho> \<Turnstile>\<^sub>f CBV\<langle>[\<pi>_end, d]\<rangle>."
  shows "\<exists>d'. d = Cst\<^sub>E d'"
proof -
  have "\<rho> \<Turnstile>\<^sub>f init\<langle>[d]\<rangle>."
    using assms(1) assms(2) init_if_CBV[of \<rho> \<pi>_end d] by fastforce
  show ?thesis
    by (metis BV_elem.exhaust \<open>\<rho> \<Turnstile>\<^sub>f init\<langle>[d]\<rangle>.\<close> assms(1) is_Cst_def not_init_action is_Cst_if_init not_init_node)
qed

lemma not_CBV_elem: (* Copy paste adapt from not_init_node *)
  assumes "\<rho> \<Turnstile>\<^sub>l\<^sub>s\<^sub>t ana_pg_fw_must s_BV"
  shows "\<not>\<rho> \<Turnstile>\<^sub>f CBV\<langle>[Cst\<^sub>E q,d]\<rangle>."
proof
  assume asm_2: "\<rho> \<Turnstile>\<^sub>f CBV\<langle>[Cst\<^sub>E q,d]\<rangle>."
  then have "[Elem q, the_Cst d] \<in> \<rho> the_CBV"
    using is_Cst_if_CBV[OF assms(1)] by (cases d) auto

  have "finite ana_pg_fw_must"
    using a_may.ana_pg_fw_may_finite by auto
  then have "\<rho> \<Turnstile>\<^sub>l\<^sub>s\<^sub>t ana_pg_fw_must s_BV"
    using downward_least_solution2[of ana_pg_fw_must s_BV \<rho> 0] asm_2
    using a_may.ana_pg_fw_may_stratified assms(1) by blast 
  then have "\<rho> \<Turnstile>\<^sub>m\<^sub>i\<^sub>n ana_pg_fw_must s_BV"
    using least_is_minimal[of]
    using strat_wf_mod_if_strat_wf  \<open>finite ana_pg_fw_must\<close> finite_below_finite
    by (smt (verit) a_may.ana_pg_fw_may_stratified) 
  moreover

  define \<rho>' where "\<rho>' = (\<lambda>p. (if p = the_CBV then (\<rho> the_CBV) - {[Elem q, the_Cst d]} else \<rho> p))"

  have "\<rho>' \<Turnstile>\<^sub>d\<^sub>l ana_pg_fw_must"
    unfolding solves_program_def
  proof
    fix c
    assume a: "c \<in> ana_pg_fw_must"
    then obtain p ids rhs where c_def: "c = Cls p ids rhs"
      by (cases c) auto

    from a have a': "c \<in> \<Union> (a_may.ana_edge_BV ` a_may.edge_set) \<or> 
          c \<in> \<Union> (a_may.ana_init_BV ` (analysis_dom - d_init)) \<or>
          c \<in> \<Union> (a_may.ana_kill_BV_edge ` a_may.edge_set) \<or>
          c \<in> \<Union> (a_may.ana_gen_BV_edge ` a_may.edge_set) \<or>
          c \<in> a_may.ana_CBV ` UNIV \<or>
          c \<in> a_may.ana_entry_node_BV"
      unfolding a_may.ana_pg_fw_may_def by auto

    have "\<rho>' \<Turnstile>\<^sub>c\<^sub>l\<^sub>s Cls p ids rhs"
      unfolding solves_cls_def
    proof (rule)
      fix \<sigma>' :: "BV_var \<Rightarrow> ('n, 'v, 'd) BV_elem"
      { 
        assume b: "Cls p ids rhs \<in> \<Union> (a_may.ana_edge_BV ` a_may.edge_set)"
        from a c_def have "\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho> \<sigma>'"
          using assms(1)
          unfolding least_solution_def solves_program_def solves_cls_def by metis
        from b have "\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho>' \<sigma>'"
          apply auto
          using \<open>\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho> \<sigma>'\<close>
           apply auto
          using \<rho>'_def apply auto
          done
      }
      moreover
      {
        assume b: "Cls p ids rhs \<in> \<Union> (a_may.ana_init_BV ` (analysis_dom - d_init))"
        from a c_def have "\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho> \<sigma>'"
          using assms(1)
          unfolding least_solution_def solves_program_def solves_cls_def by metis
        from b have "\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho>' \<sigma>'"
          apply auto
          using \<open>\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho> \<sigma>'\<close>
          apply auto
          using \<rho>'_def apply auto
          using a_may.ana_init_BV_def apply auto
          done
      }
      moreover
      {
        assume b: "Cls p ids rhs \<in> \<Union> (a_may.ana_kill_BV_edge ` a_may.edge_set)"
        from a c_def have "\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho> \<sigma>'"
          using assms(1)
          unfolding least_solution_def solves_program_def solves_cls_def by metis
        from b have "\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho>' \<sigma>'"
          apply auto
          using \<open>\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho> \<sigma>'\<close>
          apply auto
          using \<rho>'_def apply auto
           apply (simp add: a_may.ana_kill_BV_edge_def image_iff)
          apply (simp add: a_may.ana_kill_BV_edge_def image_iff)
          done
      }
      moreover
      {
        assume b: "Cls p ids rhs \<in> \<Union> (a_may.ana_gen_BV_edge ` a_may.edge_set)"
        from a c_def have "\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho> \<sigma>'"
          using assms(1)
          unfolding least_solution_def solves_program_def solves_cls_def by metis
        from b have "\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho>' \<sigma>'"
          apply auto
          using \<open>\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho> \<sigma>'\<close>
          apply auto
          using \<rho>'_def apply auto
           apply (simp add: a_may.ana_gen_BV_edge_def image_iff)+
          done
      }
      moreover
      {
        assume "Cls p ids rhs \<in> a_may.ana_CBV ` UNIV"
        then have "\<exists>q'. p = the_CBV \<and> ids = [Cst\<^sub>N q', \<uu>]"
          unfolding a_may.ana_CBV_def by blast
        then obtain q' where yah: "p = the_CBV \<and> ids = [Cst\<^sub>N q', \<uu>]"
          by auto
        have "\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho>' \<sigma>'"
        proof (cases "\<sigma>' the_\<uu> = the_Cst d")
          case True
          then have "p = the_CBV \<and> ids = [Cst\<^sub>N q', \<uu>] \<and> \<sigma>' the_\<uu> = the_Cst d"
            using yah by auto
          then have p_def: "p = the_CBV"
            by auto
          from yah have ids_def: "ids = [Cst\<^sub>N q', \<uu>]"
            by auto
          from True have \<eta>v: "\<sigma>' the_\<uu> = the_Cst d"
            by auto

          have rhs_def: "rhs = [\<^bold>\<not>BV [Cst\<^sub>N q', \<uu>],init[\<uu>]]"
            using a c_def apply auto unfolding a_may.ana_pg_fw_may_def
            apply auto
            unfolding a_may.ana_CBV_def
                    apply auto
            using p_def apply auto
            using a_may.ana_init_BV_def  apply auto[1]
              apply (simp add: a_may.ana_kill_BV_edge_def image_iff)
             apply (simp add: a_may.ana_gen_BV_edge_def image_iff)
            using a_may.ana_entry_node_BV_def
            using ids_def apply force
            using a_may.ana_entry_node_BV_def apply blast
            done
          have "\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho> \<sigma>'"
            using a assms c_def least_solution_def solves_cls_def solves_program_def by blast
          then show ?thesis
            unfolding p_def ids_def rhs_def
            unfolding meaning_cls.simps
            apply simp
            unfolding \<eta>v
            apply clarify
            unfolding \<rho>'_def
            apply auto
            done
        next
          case False
          then have False': "\<not>\<sigma>' the_\<uu> = the_Cst d"
            by auto
          from yah have p_def: "p = the_CBV"
            by auto
          from yah have ids_def: "ids = [Cst\<^sub>N q', \<uu>]"
            by auto
          have rhs_def: "rhs = [\<^bold>\<not>BV [Cst\<^sub>N q', \<uu>],init[\<uu>]]"
            using a c_def apply auto unfolding a_may.ana_pg_fw_may_def
            apply auto
            unfolding a_may.ana_CBV_def
                    apply auto
            using p_def apply auto
            using a_may.ana_init_BV_def  apply auto[1]
              apply (simp add: a_may.ana_kill_BV_edge_def image_iff)
             apply (simp add: a_may.ana_gen_BV_edge_def image_iff)
            using a_may.ana_entry_node_BV_def
            using ids_def apply force
            using a_may.ana_entry_node_BV_def apply blast 
            done

          have "\<lbrakk>CBV\<langle>[Cst\<^sub>N q', \<uu>]\<rangle> :- [\<^bold>\<not>BV [Cst\<^sub>N q', \<uu>], init [\<uu>]] .\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho> \<sigma>'"
            using \<open>Cls p ids rhs \<in> a_may.ana_CBV ` UNIV\<close>
            unfolding p_def[symmetric] rhs_def[symmetric] 
            unfolding ids_def[symmetric]
            using assms(1)
            unfolding least_solution_def
            unfolding a_may.ana_pg_fw_may_def
            by (meson Un_iff solves_cls_def solves_program_def)
          then have "\<lbrakk>CBV\<langle>[Cst\<^sub>N q', \<uu>]\<rangle> :- [\<^bold>\<not>BV [Cst\<^sub>N q', \<uu>], init [\<uu>]] .\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho>' \<sigma>'"
            unfolding \<rho>'_def 
            apply auto
            done
          then show ?thesis
            unfolding p_def ids_def rhs_def by auto
        qed
      }
      moreover
      {
        assume b: "Cls p ids rhs \<in> a_may.ana_entry_node_BV"
        from a c_def have "\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho> \<sigma>'"
          using assms(1)
          unfolding least_solution_def solves_program_def solves_cls_def by metis
        from b have "\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho>' \<sigma>'"
          apply auto
          using \<open>\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho> \<sigma>'\<close>
          apply auto
          using \<rho>'_def apply auto
          using a_may.ana_entry_node_BV_def apply fastforce
          using a_may.ana_entry_node_BV_def apply blast   
          done
      }
      ultimately
      show "\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho>' \<sigma>'"
        using a' using c_def by metis
    qed
    then show "\<rho>' \<Turnstile>\<^sub>c\<^sub>l\<^sub>s c"
      unfolding c_def by auto
  qed
  moreover
  have "\<rho>' \<sqsubset>s_BV\<sqsubset> \<rho>"
  proof -
    have "\<rho>' the_CBV \<subset> \<rho> the_CBV"
      unfolding \<rho>'_def using \<open>[Elem q, identifier.the_Cst d] \<in> \<rho> the_CBV\<close> by auto
    moreover
    have "\<forall>p'. s_BV p' = s_BV the_kill \<longrightarrow> \<rho>' p' \<subseteq> \<rho>  p'"
      unfolding \<rho>'_def by auto
    moreover
    have "\<forall>p'. s_BV p' < s_BV the_kill \<longrightarrow> \<rho>' p' = \<rho> p'"
      unfolding \<rho>'_def by auto
    ultimately
    show "\<rho>' \<sqsubset>s_BV\<sqsubset> \<rho>"
      unfolding lt_def by (metis \<rho>'_def dual_order.refl order_less_irrefl psubset_imp_subset) 
  qed
  ultimately
  show False
    unfolding minimal_solution_def by auto
qed

thm not_CBV_action
thm not_CBV_elem

lemma is_Cst_if_CBV_left_arg:
  assumes "\<rho> \<Turnstile>\<^sub>l\<^sub>s\<^sub>t ana_pg_fw_must s_BV"
  assumes "\<rho> \<Turnstile>\<^sub>f CBV\<langle>[q,d]\<rangle>."
  shows "is_Cst q"
proof (cases q)
  case (Var x)
  obtain d' where "d = Cst\<^sub>E d'"
    using assms is_encode_elem_if_CBV_right_arg by blast 

  then have "\<rho> \<Turnstile>\<^sub>f CBV\<langle>[Var x, Cst\<^sub>E d']\<rangle>."
    using Var assms(2) by auto
  then have "\<forall>\<sigma>. \<lbrakk>CBV\<langle>[Var x, Cst\<^sub>E d']\<rangle>.\<rbrakk>\<^sub>f \<rho> \<sigma>"
    unfolding solves_fact.simps by auto
  have "\<rho> \<Turnstile>\<^sub>f CBV\<langle>[Cst\<^sub>E undefined,Cst\<^sub>E d']\<rangle>."
    unfolding solves_fact.simps 
  proof 
    fix \<sigma> :: "BV_var \<Rightarrow> ('n, 'v, 'd) BV_elem"
    define \<sigma>' where "\<sigma>' = (\<lambda>y. if y = x then Elem undefined else \<sigma> y)"
    have "\<lbrakk>CBV\<langle>[Var x, Cst\<^sub>E d']\<rangle>.\<rbrakk>\<^sub>f \<rho> \<sigma>'"
      using \<open>\<forall>\<sigma>. \<lbrakk>CBV\<langle>[Var x, Cst\<^sub>E d']\<rangle>.\<rbrakk>\<^sub>f \<rho> \<sigma>\<close> by blast
    then show "\<lbrakk>CBV\<langle>[Cst\<^sub>E undefined, Cst\<^sub>E d']\<rangle>.\<rbrakk>\<^sub>f \<rho> \<sigma>"
      apply auto
      unfolding \<sigma>'_def
      apply auto
      done
  qed
  then have "False"
    using assms(1) not_CBV_elem by blast
  then show ?thesis 
    by metis
next
  case (Cst e)
  then show ?thesis 
    by auto
qed

lemma is_encode_node_if_CBV_left_arg:
  assumes "\<rho> \<Turnstile>\<^sub>l\<^sub>s\<^sub>t ana_pg_fw_must s_BV"
  assumes "\<rho> \<Turnstile>\<^sub>f CBV\<langle>[q, d]\<rangle>."
  shows "\<exists>q'. q = Cst\<^sub>N q'"
proof -
  show ?thesis
    apply (cases q)
    subgoal for x
      using 
        is_Cst_if_CBV_left_arg[OF assms(1), OF assms(2)]
      apply auto
      done
    subgoal for q''
      apply (cases q'')
      subgoal for q'''
        apply simp
        done
      subgoal for d'
        using not_CBV_elem[OF assms(1), of d' d]
          assms(2)
        apply auto
        done
      subgoal for \<alpha>
        using not_CBV_action[OF assms(1), of \<alpha> d]
          assms(2)
        apply auto
        done
      done
    done
qed

lemma in_analysis_dom_if_CBV:
  assumes "\<rho> \<Turnstile>\<^sub>l\<^sub>s\<^sub>t ana_pg_fw_must s_BV"
  assumes "\<rho> \<Turnstile>\<^sub>f CBV\<langle>[\<pi>_end, d]\<rangle>."
  shows "Decode_Elem d \<in> analysis_dom"
  using init_if_CBV
  using assms in_analysis_dom_if_init by blast

lemma sound_BV_must':
  assumes "\<rho> \<Turnstile>\<^sub>l\<^sub>s\<^sub>t ana_pg_fw_must s_BV"
  assumes "\<rho> \<Turnstile>\<^sub>f CBV\<langle>[\<pi>_end, d]\<rangle>."
  assumes "\<pi> \<in> LTS.path_with_word edge_set"
  assumes "LTS.get_start \<pi> = start"
  assumes "LTS.get_end \<pi> = Decode_Node \<pi>_end"
  shows "Decode_Elem d \<in> S_hat_path \<pi> d_init"
proof -
  have d_ana: "Decode_Elem d \<in> analysis_dom"
    using assms(1) assms(2) in_analysis_dom_if_CBV by auto

  have \<pi>e: "\<pi>_end = Cst\<^sub>N (LTS.get_end \<pi>)"
    by (smt (verit, best) BV_elem.collapse(1) BV_elem.collapse(3) BV_elem.disc(6) BV_elem.distinct(1) BV_elem.distinct(3) BV_elem.expand assms(1) assms(2) assms(5) identifier.sel(2) is_bv_elem_def is_encode_node_if_CBV_left_arg)

  have d_encdec: "d = Cst\<^sub>E (Decode_Elem d)"
    by (metis BV_elem.sel(2) assms(1) assms(2) identifier.sel(2) is_encode_elem_if_CBV_right_arg)

  have m: "\<not> \<rho> \<Turnstile>\<^sub>f BV\<langle>[Cst\<^sub>N (LTS.get_end \<pi>), d]\<rangle>."
    using not_CBV2[OF assms(1), of "(LTS.get_end \<pi>)" "Decode_Elem d"] assms(2) \<pi>e d_encdec by force
  have "\<not>Decode_Elem d \<in> a_may.S_hat_path \<pi> (analysis_dom - d_init)"
    using a_may.sound_ana_pg_fw_may assms(1)
    unfolding a_may.summarizes_fw_may.simps
     a_may.edge_set_def a_may.start_def assms(2) assms(4) assms(5) edge_set_def m start_def
    by (metis assms(3) assms(4) d_encdec edge_set_def m start_def)
  then show "Decode_Elem d \<in> S_hat_path \<pi> d_init"
    using opposite_lemma2
    using assms(1)
    using \<open>Decode_Elem d \<in> analysis_dom\<close> by blast 
qed

lemma sound_CBV:
  assumes "\<rho> \<Turnstile>\<^sub>l\<^sub>s\<^sub>t ana_pg_fw_must s_BV"
  shows "summarizes_fw_must \<rho>"
  using assms unfolding summarizes_fw_must.simps using sound_BV_must' by auto

end

section \<open>TODO: Available expressions\<close>

typ "'v boolean"

fun ae_arith :: "'v arith \<Rightarrow> 'v arith set" where
  "ae_arith (Integer i) = {}"
| "ae_arith (Arith_Var v) = {}"
| "ae_arith (Arith_Op a1 opr a2) = ae_arith a1 \<union> ae_arith a1 \<union> {Arith_Op a1 opr a2}"
| "ae_arith (Minus a) = ae_arith a"

lemma finite_ae_arith: "finite (ae_arith a)"
  apply (induction a)
     apply auto
  done

fun ae_boolean :: "'v boolean \<Rightarrow> 'v arith set" where
  "ae_boolean true = {}"
| "ae_boolean false = {}"
| "ae_boolean (Rel_Op a1 opr a2) = ae_arith a1 \<union> ae_arith a2"
| "ae_boolean (Bool_Op b1 opr b2) = ae_boolean b1 \<union> ae_boolean b2"
| "ae_boolean (Neg b) = ae_boolean b"

lemma finite_ae_boolean: "finite (ae_boolean b)"
  apply (induction b)
  using finite_ae_arith
      apply auto
  done

fun aexp_action :: "'v action \<Rightarrow> 'v arith set" where (* Maybe avexp would be a better name. *)
  "aexp_action (x ::= a) = ae_arith a"
| "aexp_action (Bool b) = ae_boolean b"
| "aexp_action Skip = {}"

lemma finite_aexp_action: "finite (aexp_action \<alpha>)"
  apply (cases \<alpha>)
  using finite_ae_arith finite_ae_boolean
    apply auto
  done

fun aexp_edge :: "('n,'v) edge \<Rightarrow> 'v arith set" where
  "aexp_edge (q1, \<alpha>, q2) = aexp_action \<alpha>"

lemma finite_aexp_edge: "finite (aexp_edge (q1, \<alpha>, q2))"
  using finite_aexp_action 
  apply auto
  done

fun aexp_pg :: "('n,'v) program_graph \<Rightarrow> 'v arith set" where
  "aexp_pg pg = \<Union>(aexp_edge ` (fst pg))"

definition aexp_edge_list :: "('n,'v) edge list \<Rightarrow> 'v arith \<Rightarrow> bool" where
  "aexp_edge_list \<pi> a = (\<exists>\<pi>1 \<pi>2 e. \<pi> = \<pi>1 @ [e] @ \<pi>2 \<and> a \<in> aexp_edge e \<and> (\<forall>e' \<in> set \<pi>2. fv_arith a \<inter> def_edge e' = {}))"

definition aexp_path :: "'n list \<times> 'v action list \<Rightarrow> 'v arith set" where
  "aexp_path \<pi> = {a. aexp_edge_list (LTS.transition_list \<pi>) a}"

locale analysis_AE =
  fixes pg :: "('n::finite,'v::finite) program_graph"
  assumes "finite (fst pg)"
begin

definition edge_set where 
  "edge_set = fst pg"

definition start where
  "start = fst (snd pg)"

definition "end" where
  "end = snd (snd pg)"

definition analysis_dom_AE :: "'v arith set" where
  "analysis_dom_AE = aexp_pg pg"

lemma finite_analysis_dom_AE: "finite analysis_dom_AE"
  unfolding analysis_dom_AE_def
  apply auto
  by (metis aexp_edge.elims analysis_AE_axioms analysis_AE_def finite_UN_I finite_aexp_action)

fun kill_set_AE :: "('n,'v) edge \<Rightarrow> 'v arith set" where
  "kill_set_AE (q\<^sub>o, x ::= a, q\<^sub>s) = {a'. x \<in> fv_arith a'}"
| "kill_set_AE (q\<^sub>o, Bool b, q\<^sub>s) = {}"
| "kill_set_AE (v, Skip, vc) = {}"

fun gen_set_AE :: "('n,'v) edge \<Rightarrow> 'v arith set" where
  "gen_set_AE (q\<^sub>o, x ::= a, q\<^sub>s) = {a'. a' \<in> ae_arith a \<and> x \<notin> fv_arith a'}"
| "gen_set_AE (q\<^sub>o, Bool b, q\<^sub>s) = ae_boolean b"
| "gen_set_AE (v, Skip, vc) = {}"

definition d_init_AE :: "'v arith set" where
  "d_init_AE = {}"

(* Problem: 'v arith  er ikke en endelig type. *)

interpretation interpb: analysis_BV_forward_must pg analysis_dom_AE kill_set_AE gen_set_AE d_init_AE
  using analysis_BV_forward_must.intro analysis_AE_axioms analysis_AE_def
  by (metis d_init_AE_def empty_iff finite_analysis_dom_AE subsetI) 

lemma aexp_edge_list_S_hat_edge_list: 
  assumes "aexp_edge_list \<pi> a"
  shows "a \<in> interpb.S_hat_edge_list \<pi> d_init_AE"
  using assms oops (* TODO: *)

end

section \<open>Backward must-analysis\<close>

locale analysis_BV_backward_must =
  fixes pg :: "('n::finite,'v) program_graph"
  fixes analysis_dom :: "'d set"
  fixes kill_set :: "('n,'v) edge \<Rightarrow> 'd set"
  fixes gen_set :: "('n,'v) edge \<Rightarrow> 'd set"
  fixes d_init :: "'d set"
  assumes "finite (fst pg)"
  assumes "finite analysis_dom"
  assumes "d_init \<subseteq> analysis_dom"
begin

lemma finite_d_init: "finite d_init"
  by (meson analysis_BV_backward_must_axioms analysis_BV_backward_must_def finite_subset)

definition edge_set where (* Copy paste *)
  "edge_set = fst pg"

definition start where (* Copy paste *)
  "start = fst (snd pg)"

definition "end" where (* Copy paste *)
  "end = snd (snd pg)"

definition pg_rev :: "('n,'v) program_graph" where (* Copy paste *)
  "pg_rev = (rev_edge ` edge_set, end, start)"

definition "S_hat" :: "('n,'v) edge \<Rightarrow> 'd set \<Rightarrow> 'd set" where (* Copy paste *)
  "S_hat e R = (R - kill_set e) \<union> gen_set e"

lemma S_hat_mono: (* Copy paste *)
  assumes "d1 \<subseteq> d2"
  shows "S_hat e d1 \<subseteq> S_hat e d2"
  using assms unfolding S_hat_def by auto

fun S_hat_edge_list :: "('n,'v) edge list \<Rightarrow> 'd set \<Rightarrow> 'd set" where (* Copy paste *)
  "S_hat_edge_list [] R = R" |
  "S_hat_edge_list (e # \<pi>) R = S_hat e (S_hat_edge_list \<pi> R)"

lemma S_hat_edge_list_def2: (* Copy paste *)
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

lemma S_hat_edge_list_append[simp]: (* Copy paste *)
  "S_hat_edge_list (xs @ ys) R = S_hat_edge_list xs (S_hat_edge_list ys R)"
  unfolding S_hat_edge_list_def2 foldl_append by auto

lemma S_hat_edge_list_mono: (* Copy paste *)
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

definition S_hat_path :: "('n list \<times> 'v action list) \<Rightarrow> 'd set \<Rightarrow> 'd set" where (* Copy paste *)
  "S_hat_path \<pi> = S_hat_edge_list (LTS.transition_list \<pi>)"

fun summarizes_bw_must :: "(BV_pred, ('n, 'v, 'd) BV_elem) pred_val \<Rightarrow> bool" where (* Ny *)
   "summarizes_bw_must \<rho> \<longleftrightarrow>
     (\<forall>\<pi>_start d.
         \<rho> \<Turnstile>\<^sub>f CBV\<langle>[\<pi>_start, d]\<rangle>. \<longrightarrow>
          (\<forall>\<pi>. \<pi> \<in> LTS.path_with_word edge_set \<longrightarrow> LTS.get_end \<pi> = end \<longrightarrow> LTS.get_start \<pi> = Decode_Node \<pi>_start \<longrightarrow> Decode_Elem d \<in> S_hat_path \<pi> d_init))"

lemma finite_pg_rev: "finite (fst pg_rev)" (* Copy paste *)
  by (metis analysis_BV_backward_must_axioms analysis_BV_backward_must_def edge_set_def finite_imageI fst_conv pg_rev_def)

interpretation fa: analysis_BV_forward_must pg_rev analysis_dom "\<lambda>e. (kill_set (rev_edge e))" "(\<lambda>e. gen_set (rev_edge e))" d_init
  using analysis_BV_forward_must_def finite_pg_rev
  by (metis analysis_BV_backward_must_axioms analysis_BV_backward_must_def) 

abbreviation ana_pg_bw_must where (* Copy paste *)
  "ana_pg_bw_must == fa.ana_pg_fw_must"

lemma rev_end_is_start: (* Copy paste *)
  assumes "ss \<noteq> []"
  assumes "LTS.get_end (ss, w) = end"
  shows "LTS.get_start (rev ss, rev w) = fa.start"
  using assms
  unfolding LTS.get_end_def LTS.get_start_def fa.start_def pg_rev_def fa.start_def
  using hd_rev by (metis fa.start_def fst_conv pg_rev_def snd_conv) 

lemma S_hat_edge_list_forward_backward: (* Copy paste *)
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

lemma S_hat_path_forward_backward: (* Copy paste *)
  assumes "(ss,w) \<in> LTS.path_with_word edge_set"
  shows "S_hat_path (ss, w) d_init = fa.S_hat_path (rev ss, rev w) d_init"
  using S_hat_edge_list_forward_backward unfolding S_hat_path_def fa.S_hat_path_def
  by (metis transition_list_rev_edge_list assms)

lemma summarizes_fw_must_forward_backward':
  assumes "fa.summarizes_fw_must \<rho>"
  assumes "\<rho> \<Turnstile>\<^sub>f CBV\<langle>[\<pi>_start, d]\<rangle>."
  assumes "\<pi> \<in> LTS.path_with_word edge_set"
  assumes "LTS.get_end \<pi> = end"
  assumes "LTS.get_start \<pi> = Decode_Node \<pi>_start"
  shows "Decode_Elem d \<in> S_hat_path \<pi> d_init"
  using LTS.get_end_def LTS.get_start_def S_hat_path_forward_backward 
    analysis_BV_backward_must_axioms assms fa.start_def fa.summarizes_fw_must.simps fst_conv 
    hd_rev last_rev pg_rev_def rev_path_in_rev_pg snd_conv fa.edge_set_def prod.collapse 
  by (metis (no_types, lifting))
    (* TODO? Expand proof into something coherent? *)

lemma summarizes_bw_must_forward_backward: (* Copy paste statement by adapted proof *)
  assumes "fa.summarizes_fw_must \<rho>"
  shows "summarizes_bw_must \<rho>"
  unfolding summarizes_bw_must.simps
proof(rule; rule ; rule ;rule ;rule; rule; rule)
  fix \<pi>_start d \<pi>
  assume "\<rho> \<Turnstile>\<^sub>f CBV\<langle>[\<pi>_start, d]\<rangle>."
  moreover
  assume "\<pi> \<in> LTS.path_with_word edge_set"
  moreover
  assume "LTS.get_end \<pi> = end"
  moreover
  assume "LTS.get_start \<pi> = Decode_Node \<pi>_start"
  ultimately
  show "Decode_Elem d \<in> S_hat_path \<pi> d_init"
    by (metis assms summarizes_fw_must_forward_backward')
qed

lemma sound_rev_BV:
  assumes "\<rho> \<Turnstile>\<^sub>l\<^sub>s\<^sub>t ana_pg_bw_must s_BV"
  shows "summarizes_bw_must \<rho>"
  using assms fa.sound_CBV[of \<rho>] summarizes_bw_must_forward_backward by metis

(* 

Plan:
Forstå hvordan du 

FORWARD MAY:
fun summarizes_dl_BV :: "(BV_pred, ('n, 'v, 'd) BV_elem) pred_val \<Rightarrow> bool" where
  "summarizes_dl_BV \<rho> \<longleftrightarrow> 
     (\<forall>\<pi> d. \<pi> \<in> LTS.path_with_word edge_set \<longrightarrow> LTS.get_start \<pi> = start \<longrightarrow> d \<in> S_hat_path \<pi> d_init \<longrightarrow> 
        \<rho> \<Turnstile>\<^sub>f (BV\<langle>[Cst\<^sub>N (LTS.get_end \<pi>), Cst\<^sub>E d]\<rangle>.))"


BACKWARD MAY:
definition summarizes_dl_BV :: "(BV_pred, ('n, 'v, 'd) BV_elem) pred_val \<Rightarrow> bool" where
  "summarizes_dl_BV \<rho> \<longleftrightarrow> 
     (\<forall>\<pi> d. \<pi> \<in> LTS.path_with_word edge_set \<longrightarrow> LTS.get_end \<pi> = end \<longrightarrow> d \<in> S_hat_path \<pi> d_init \<longrightarrow> 
                             \<rho> \<Turnstile>\<^sub>f BV\<langle>[Cst\<^sub>N (LTS.get_start \<pi>), Cst\<^sub>E d]\<rangle>.)"

FORWARD MUST:
fun summarizes_dl_BV_must :: "(BV_pred, ('n, 'v, 'd) BV_elem) pred_val \<Rightarrow> bool" where
  "summarizes_dl_BV_must \<rho> \<longleftrightarrow>
     (\<forall>\<pi>_end d.
        \<rho> \<Turnstile>\<^sub>f CBV\<langle>[Cst\<^sub>N \<pi>_end, Cst\<^sub>E d]\<rangle>. \<longrightarrow>
          (\<forall>\<pi>. \<pi> \<in> LTS.path_with_word edge_set \<longrightarrow> LTS.get_start \<pi> = start \<longrightarrow> LTS.get_end \<pi> = \<pi>_end \<longrightarrow> d \<in> S_hat_path \<pi> d_init))"

BACKWARD MUST:
fun summarizes_dl_BV_must :: "(BV_pred, ('n, 'v, 'd) BV_elem) pred_val \<Rightarrow> bool" where
  "summarizes_dl_BV_must \<rho> \<longleftrightarrow>
     (\<forall>\<pi>_start d.
        \<rho> \<Turnstile>\<^sub>f CBV\<langle>[Cst\<^sub>N \<pi>_start, Cst\<^sub>E d]\<rangle>. \<longrightarrow>
          (\<forall>\<pi>. \<pi> \<in> LTS.path_with_word edge_set \<longrightarrow> LTS.get_end \<pi> = end \<longrightarrow> LTS.get_start \<pi> = \<pi>_start \<longrightarrow> d \<in> S_hat_path \<pi> d_init))"

MAY  betyder \<Turnstile> på højresiden og BV.
MUST betyder \<Turnstile> på venstresiden og CBV.

Forward betyder at vi bruger kravet LTS.get_start \<pi> = start, og at vi har slutknuden i vores prædikat.
Backward betyder at vi bruger kravet LTS.get_end \<pi> = end, og at vi har start knuden i vores prædikat.

*)

end

section \<open>TODO: Very Busy Expressions\<close>

end