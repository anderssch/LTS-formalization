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

type_synonym ('n,'v) program_graph = "('n,'v) edge set \<times> 'n \<times> 'n"

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

type_synonym ('n,'v) def = "'v * 'n option * 'n"

type_synonym ('n,'v) analysis_assignment = "'n \<Rightarrow> ('n,'v) def set"


subsection \<open>What is defined on a path\<close>

fun def_action :: "'v action \<Rightarrow> 'v set" where
  "def_action (x ::= a) = {x}"
| "def_action (Bool b) = {}"
| "def_action Skip = {}"

abbreviation def_edge :: "('n,'v) edge \<Rightarrow> 'v set" where
  "def_edge == \<lambda>(q1, \<alpha>, q2). def_action \<alpha>"

definition def_of :: "'v \<Rightarrow> ('n,'v) edge \<Rightarrow> ('n,'v) def" where
  "def_of == (\<lambda>x (q1, \<alpha>, q2). (x, Some q1, q2))"

definition def_var :: "('n,'v) edge list \<Rightarrow> 'v \<Rightarrow> 'n \<Rightarrow> ('n,'v) def" where
  "def_var \<pi> x start = (if (\<exists>e \<in> set \<pi>. x \<in> def_edge e)
                        then (def_of x (last (filter (\<lambda>e. x \<in> def_edge e) \<pi>)))
                        else (x, None, start))"

definition def_path :: "('n list \<times> 'v action list) \<Rightarrow> 'n \<Rightarrow> ('n,'v) def set" where
  "def_path \<pi> start = ((\<lambda>x. def_var (LTS.transition_list \<pi>) x start) ` UNIV)"

(*
fun summarizes_RD :: "('n,'v) analysis_assignment \<Rightarrow> ('n,'v) program_graph \<Rightarrow> bool" where
  "summarizes_RD RD (es,start,end) \<longleftrightarrow> (\<forall>\<pi>. \<pi> \<in> LTS.path_with_word es \<longrightarrow> LTS.get_start \<pi> = start \<longrightarrow> def_path \<pi> start \<subseteq> RD (LTS.get_end \<pi>))"
*)


section \<open>Datalog programs and their solutions\<close>

datatype (vars_id: 'x,'c) id = is_Var: Var 'x | is_Cst: Cst (the_Cst: 'c)

datatype (preds_rh: 'p,'x,'c) rh = 
  Eql "('x,'c) id" "('x,'c) id" ("_ \<^bold>= _" [61, 61] 61)
  | Neql "('x,'c) id" "('x,'c) id" ("_ \<^bold>\<noteq> _" [61, 61] 61)
  | PosLit 'p "('x,'c) id list" ("\<^bold>+ _ _" [61, 61] 61)
  | NegLit 'p "('x,'c) id list" ("\<^bold>\<not> _ _" [61, 61] 61)

datatype (preds_cls: 'p, 'x,'c) clause = Cls 'p "('x,'c) id list" (the_rhs: "('p,'x,'c) rh list") (* Why not rh set? *)

fun the_lh where
  "the_lh (Cls p ids rhs) = (p,ids)"

type_synonym ('p,'x,'c) dl_program = "('p,'x,'c) clause set"

definition "preds_dl dl = \<Union>{preds_cls c| c. c \<in> dl}"

lemma preds_dl_union[simp]: "preds_dl (dl1 \<union> dl2) = preds_dl dl1 \<union> preds_dl dl2"
  unfolding preds_dl_def by auto

type_synonym ('x,'c) var_val = "'x \<Rightarrow> 'c"

type_synonym ('p,'c) pred_val = "'p \<Rightarrow> 'c list set"

type_synonym ('p,'x,'c) lh = "'p * ('x,'c) id list"

fun preds_lh :: "('p,'x,'c) lh \<Rightarrow> 'p set" where 
  "preds_lh (p,ids) = {p}"

fun the_lhs :: "('p, 'x,'c) clause \<Rightarrow> ('p,'x,'c) lh" where
  "the_lhs (Cls p ids rhs) = (p,ids)"

fun eval_id :: "('x,'c) id \<Rightarrow> ('x,'c) var_val \<Rightarrow> 'c" ("\<lbrakk>_\<rbrakk>\<^sub>i\<^sub>d") where
  "\<lbrakk>Var x\<rbrakk>\<^sub>i\<^sub>d \<sigma> = \<sigma> x"
| "\<lbrakk>Cst c\<rbrakk>\<^sub>i\<^sub>d \<sigma> = c"

fun eval_ids :: "('x,'c) id list \<Rightarrow> ('x,'c) var_val \<Rightarrow> 'c list" ("\<lbrakk>_\<rbrakk>\<^sub>i\<^sub>d\<^sub>s") where
  "\<lbrakk>ids\<rbrakk>\<^sub>i\<^sub>d\<^sub>s \<sigma> = map (\<lambda>a. \<lbrakk>a\<rbrakk>\<^sub>i\<^sub>d \<sigma>) ids"

fun meaning_rh :: "('p,'x,'c) rh \<Rightarrow> ('p,'c) pred_val \<Rightarrow> ('x,'c) var_val \<Rightarrow> bool" ("\<lbrakk>_\<rbrakk>\<^sub>r\<^sub>h") where
  "\<lbrakk>a \<^bold>= a'\<rbrakk>\<^sub>r\<^sub>h \<rho> \<sigma> \<longleftrightarrow> \<lbrakk>a\<rbrakk>\<^sub>i\<^sub>d \<sigma> = \<lbrakk>a'\<rbrakk>\<^sub>i\<^sub>d \<sigma>"
| "\<lbrakk>a \<^bold>\<noteq> a'\<rbrakk>\<^sub>r\<^sub>h \<rho> \<sigma> \<longleftrightarrow> \<lbrakk>a\<rbrakk>\<^sub>i\<^sub>d \<sigma>  \<noteq> \<lbrakk>a'\<rbrakk>\<^sub>i\<^sub>d \<sigma>"
| "\<lbrakk>\<^bold>+ p ids\<rbrakk>\<^sub>r\<^sub>h \<rho> \<sigma> \<longleftrightarrow> \<lbrakk>ids\<rbrakk>\<^sub>i\<^sub>d\<^sub>s \<sigma> \<in> \<rho> p"
| "\<lbrakk>\<^bold>\<not> p ids\<rbrakk>\<^sub>r\<^sub>h \<rho> \<sigma> \<longleftrightarrow> \<not> \<lbrakk>ids\<rbrakk>\<^sub>i\<^sub>d\<^sub>s \<sigma> \<in> \<rho> p"

fun meaning_rhs :: "('p,'x,'c) rh list \<Rightarrow> ('p,'c) pred_val \<Rightarrow> ('x,'c) var_val \<Rightarrow> bool" ("\<lbrakk>_\<rbrakk>\<^sub>r\<^sub>h\<^sub>s") where
  "\<lbrakk>rhs\<rbrakk>\<^sub>r\<^sub>h\<^sub>s \<rho> \<sigma> \<longleftrightarrow> (\<forall>rh \<in> set rhs. \<lbrakk>rh\<rbrakk>\<^sub>r\<^sub>h \<rho> \<sigma>)"

fun meaning_lh :: "('p,'x,'c) lh \<Rightarrow> ('p,'c) pred_val \<Rightarrow> ('x,'c) var_val \<Rightarrow> bool" ("\<lbrakk>_\<rbrakk>\<^sub>l\<^sub>h") where
  "\<lbrakk>(p,ids)\<rbrakk>\<^sub>l\<^sub>h \<rho> \<sigma> \<longleftrightarrow> \<lbrakk>ids\<rbrakk>\<^sub>i\<^sub>d\<^sub>s \<sigma> \<in> \<rho> p"

fun meaning_cls :: "('p,'x,'c) clause \<Rightarrow> ('p,'c) pred_val \<Rightarrow> ('x,'c) var_val \<Rightarrow> bool" ("\<lbrakk>_\<rbrakk>\<^sub>c\<^sub>l\<^sub>s") where
  "\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho> \<sigma> \<longleftrightarrow> (\<lbrakk>rhs\<rbrakk>\<^sub>r\<^sub>h\<^sub>s \<rho> \<sigma> \<longrightarrow> \<lbrakk>(p,ids)\<rbrakk>\<^sub>l\<^sub>h \<rho> \<sigma>)" (* use meaning_rhs *)

fun solves_lh :: "('p,'c) pred_val \<Rightarrow> ('p,'x,'c) lh \<Rightarrow> bool" (infix "\<Turnstile>\<^sub>l\<^sub>h" 91) where
  "\<rho> \<Turnstile>\<^sub>l\<^sub>h (p,ids) \<longleftrightarrow> (\<forall>\<sigma>. \<lbrakk>(p,ids)\<rbrakk>\<^sub>l\<^sub>h \<rho> \<sigma>)"

fun solves_rh :: "('p,'c) pred_val \<Rightarrow> ('p,'x,'c) rh \<Rightarrow> bool" (infix "\<Turnstile>\<^sub>r\<^sub>h" 91) where (* Not in the book *)
  "\<rho> \<Turnstile>\<^sub>r\<^sub>h rh \<longleftrightarrow> (\<forall>\<sigma>. \<lbrakk>rh\<rbrakk>\<^sub>r\<^sub>h \<rho> \<sigma>)"

definition solves_cls :: "('p,'c) pred_val \<Rightarrow> ('p,'x,'c) clause \<Rightarrow> bool" (infix "\<Turnstile>\<^sub>c\<^sub>l\<^sub>s" 91) where
  "\<rho> \<Turnstile>\<^sub>c\<^sub>l\<^sub>s c \<longleftrightarrow> (\<forall>\<sigma>. \<lbrakk>c\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho> \<sigma>)"

definition solves_program :: "('p,'c) pred_val \<Rightarrow> ('p,'x,'c) dl_program \<Rightarrow> bool" (infix "\<Turnstile>\<^sub>d\<^sub>l" 91) where
  "\<rho> \<Turnstile>\<^sub>d\<^sub>l dl \<longleftrightarrow> (\<forall>c \<in> dl. \<rho> \<Turnstile>\<^sub>c\<^sub>l\<^sub>s c)"

(*
section \<open>Facts (not in the book?)\<close> (* TODO: get rid of these*)

type_synonym ('p,'x,'c) lh = "'p * ('x,'c) id list" (* The lh type is the same as the lh type... *)

fun meaning_lh :: "('p,'x,'c) lh \<Rightarrow> ('p,'c) pred_val \<Rightarrow> ('x,'c) var_val \<Rightarrow> bool" ("\<lbrakk>_\<rbrakk>\<^sub>f") where
  "\<lbrakk>(p,ids)\<rbrakk>\<^sub>f \<rho> \<sigma> \<longleftrightarrow> \<lbrakk>ids\<rbrakk>\<^sub>i\<^sub>d\<^sub>s \<sigma> \<in> \<rho> p"

fun solves_lh :: "('p,'c) pred_val \<Rightarrow> ('p,'x,'c) lh \<Rightarrow> bool" (infix "\<Turnstile>\<^sub>l\<^sub>h" 91) where
  "\<rho> \<Turnstile>\<^sub>l\<^sub>h (p,ids) \<longleftrightarrow> (\<forall>\<sigma>. \<lbrakk>(p,ids)\<rbrakk>\<^sub>f \<rho> \<sigma>)"
*)


section \<open>Substitutions (not in the book?)\<close>

type_synonym ('x,'c) subst = "'x \<Rightarrow> ('x,'c) id"

fun subst_id :: "('x,'c) id \<Rightarrow> ('x,'c) subst \<Rightarrow> ('x,'c) id" (infix "\<cdot>\<^sub>i\<^sub>d" 70) where
  "(Var x) \<cdot>\<^sub>i\<^sub>d \<eta>  = \<eta> x"
| "(Cst e) \<cdot>\<^sub>i\<^sub>d \<eta> = (Cst e)"

fun subst_ids :: "('x,'c) id list \<Rightarrow> ('x,'c) subst \<Rightarrow> ('x,'c) id list" (infix "\<cdot>\<^sub>i\<^sub>d\<^sub>s" 50) where
  "ids \<cdot>\<^sub>i\<^sub>d\<^sub>s \<eta> = map (\<lambda>a. a \<cdot>\<^sub>i\<^sub>d \<eta>) ids"

fun subst_rh :: "('p,'x,'c) rh \<Rightarrow> ('x,'c) subst \<Rightarrow> ('p,'x,'c) rh" (infix "\<cdot>\<^sub>r\<^sub>h" 50) where
  "(a \<^bold>= a') \<cdot>\<^sub>r\<^sub>h \<eta> = (a \<cdot>\<^sub>i\<^sub>d \<eta> \<^bold>= a' \<cdot>\<^sub>i\<^sub>d \<eta>)"
| "(a \<^bold>\<noteq> a') \<cdot>\<^sub>r\<^sub>h \<eta> = (a \<cdot>\<^sub>i\<^sub>d \<eta> \<^bold>\<noteq> a' \<cdot>\<^sub>i\<^sub>d \<eta>)"
| "(\<^bold>+ p ids) \<cdot>\<^sub>r\<^sub>h \<eta> = (\<^bold>+ p (ids \<cdot>\<^sub>i\<^sub>d\<^sub>s \<eta>))"
| "(\<^bold>\<not> p ids) \<cdot>\<^sub>r\<^sub>h \<eta> = (\<^bold>\<not> p ( ids \<cdot>\<^sub>i\<^sub>d\<^sub>s \<eta>))"

fun subst_rhs :: "('p,'x,'c) rh list \<Rightarrow> ('x,'c) subst \<Rightarrow> ('p,'x,'c) rh list" (infix "\<cdot>\<^sub>r\<^sub>h\<^sub>s" 50) where
  "rhs \<cdot>\<^sub>r\<^sub>h\<^sub>s \<eta> = map (\<lambda>a. a \<cdot>\<^sub>r\<^sub>h \<eta>) rhs"

fun subst_lh :: "('p,'x,'c) lh \<Rightarrow> ('x,'c) subst \<Rightarrow> ('p,'x,'c) lh" (infix "\<cdot>\<^sub>l\<^sub>h" 50) where
  "(p,ids) \<cdot>\<^sub>l\<^sub>h \<eta> = (p, ids \<cdot>\<^sub>i\<^sub>d\<^sub>s \<eta>)"

fun subst_cls :: "('p,'x,'c) clause \<Rightarrow> ('x,'c) subst \<Rightarrow> ('p,'x,'c) clause" (infix "\<cdot>\<^sub>c\<^sub>l\<^sub>s" 50) where
  "(Cls p ids rhs) \<cdot>\<^sub>c\<^sub>l\<^sub>s \<eta>  = Cls p (ids \<cdot>\<^sub>i\<^sub>d\<^sub>s \<eta>) (rhs \<cdot>\<^sub>r\<^sub>h\<^sub>s \<eta>)"

definition compose :: "('x,'c) subst \<Rightarrow> ('x,'c) var_val \<Rightarrow> ('x,'c) var_val" (infix "\<circ>\<^sub>s\<^sub>v" 50) where
  "(\<eta> \<circ>\<^sub>s\<^sub>v \<sigma>) x = \<lbrakk>(\<eta> x)\<rbrakk>\<^sub>i\<^sub>d \<sigma>"

section \<open>Substiting variable valuations (not in the book?)\<close>

fun substv_id :: "('x,'c) id \<Rightarrow> ('x,'c) var_val \<Rightarrow> ('x,'c) id" (infix "\<cdot>\<^sub>v\<^sub>i\<^sub>d" 70) where
  "(Var x) \<cdot>\<^sub>v\<^sub>i\<^sub>d \<sigma> = Cst (\<sigma> x)"
| "(Cst e) \<cdot>\<^sub>v\<^sub>i\<^sub>d \<sigma> = (Cst e)"

fun substv_ids :: "('x,'c) id list \<Rightarrow> ('x,'c) var_val \<Rightarrow> ('x,'c) id list" (infix "\<cdot>\<^sub>v\<^sub>i\<^sub>d\<^sub>s" 50) where
  "rhs \<cdot>\<^sub>v\<^sub>i\<^sub>d\<^sub>s \<sigma> = map (\<lambda>a. a \<cdot>\<^sub>v\<^sub>i\<^sub>d \<sigma>) rhs"

fun substv_rh :: "('p,'x,'c) rh \<Rightarrow> ('x,'c) var_val \<Rightarrow> ('p,'x,'c) rh" (infix "\<cdot>\<^sub>v\<^sub>r\<^sub>h" 50) where
  "(a \<^bold>= a') \<cdot>\<^sub>v\<^sub>r\<^sub>h \<sigma> = (a \<cdot>\<^sub>v\<^sub>i\<^sub>d \<sigma> \<^bold>= a' \<cdot>\<^sub>v\<^sub>i\<^sub>d \<sigma>)"
| "(a \<^bold>\<noteq> a') \<cdot>\<^sub>v\<^sub>r\<^sub>h \<sigma> = (a \<cdot>\<^sub>v\<^sub>i\<^sub>d \<sigma> \<^bold>\<noteq> a' \<cdot>\<^sub>v\<^sub>i\<^sub>d \<sigma>)"
| "(\<^bold>+ p ids) \<cdot>\<^sub>v\<^sub>r\<^sub>h \<sigma> = (\<^bold>+ p (ids \<cdot>\<^sub>v\<^sub>i\<^sub>d\<^sub>s \<sigma>))"
| "(\<^bold>\<not> p ids) \<cdot>\<^sub>v\<^sub>r\<^sub>h \<sigma> = (\<^bold>\<not> p (ids \<cdot>\<^sub>v\<^sub>i\<^sub>d\<^sub>s \<sigma>))"

definition substv_rhs :: "('p,'x,'c) rh list \<Rightarrow> ('x,'c) var_val \<Rightarrow> ('p,'x,'c) rh list" (infix "\<cdot>\<^sub>v\<^sub>r\<^sub>h\<^sub>s" 50) where
  "rhs \<cdot>\<^sub>v\<^sub>r\<^sub>h\<^sub>s \<sigma> = map (\<lambda>a. a \<cdot>\<^sub>v\<^sub>r\<^sub>h \<sigma>) rhs"

fun substv_lh :: "('p,'x,'c) lh \<Rightarrow> ('x,'c) var_val \<Rightarrow> ('p,'x,'c) lh" (infix "\<cdot>\<^sub>v\<^sub>l\<^sub>h" 50) where
  "(p,ids) \<cdot>\<^sub>v\<^sub>l\<^sub>h \<sigma> = (p,  ids \<cdot>\<^sub>v\<^sub>i\<^sub>d\<^sub>s \<sigma>)"

fun substv_cls :: "('p,'x,'c) clause \<Rightarrow> ('x,'c) var_val \<Rightarrow> ('p,'x,'c) clause" (infix "\<cdot>\<^sub>v\<^sub>c\<^sub>l\<^sub>s" 50) where
  "(Cls p ids rhs) \<cdot>\<^sub>v\<^sub>c\<^sub>l\<^sub>s \<sigma>  = Cls p (ids \<cdot>\<^sub>v\<^sub>i\<^sub>d\<^sub>s \<sigma>) (rhs \<cdot>\<^sub>v\<^sub>r\<^sub>h\<^sub>s \<sigma>)"


section \<open>Datalog lemmas\<close>

subsection \<open>Solve lhs\<close>

lemma solves_lh_iff_solves_lh: "\<rho> \<Turnstile>\<^sub>c\<^sub>l\<^sub>s Cls p ids [] \<longleftrightarrow> \<rho> \<Turnstile>\<^sub>r\<^sub>h (\<^bold>+ p ids)"
  using solves_cls_def by force

lemma solves_lh_lh:
  assumes "\<rho> \<Turnstile>\<^sub>c\<^sub>l\<^sub>s Cls p args []"
  shows "\<rho> \<Turnstile>\<^sub>l\<^sub>h (p, args)"
  using assms unfolding solves_cls_def by auto

lemmas solve_lhs = solves_lh_iff_solves_lh solves_lh_lh

subsection \<open>Propositional inferences\<close>

subsubsection \<open>Of last right hand\<close>

lemma prop_inf_last_from_cls_rh_to_cls:
  assumes "\<rho> \<Turnstile>\<^sub>c\<^sub>l\<^sub>s Cls p args (rhs @ [rh])"
  assumes "\<rho> \<Turnstile>\<^sub>r\<^sub>h rh"
  shows "\<rho> \<Turnstile>\<^sub>c\<^sub>l\<^sub>s Cls p args rhs"
  using assms unfolding solves_cls_def by auto

lemma prop_inf_last_from_cls_lh_to_cls:
  assumes "\<rho> \<Turnstile>\<^sub>c\<^sub>l\<^sub>s Cls p args (rhs @ [\<^bold>+ p ids])"
  assumes "\<rho> \<Turnstile>\<^sub>l\<^sub>h (p, ids)"
  shows "\<rho> \<Turnstile>\<^sub>c\<^sub>l\<^sub>s Cls p args rhs"
  using assms by (force simp add: solves_cls_def)

lemmas prop_inf_last = prop_inf_last_from_cls_rh_to_cls prop_inf_last_from_cls_lh_to_cls


subsubsection \<open>Of only right hand\<close>

lemma modus_ponens_rh:
  assumes "\<rho> \<Turnstile>\<^sub>c\<^sub>l\<^sub>s Cls p ids [\<^bold>+ p' ids']"
  assumes "\<rho> \<Turnstile>\<^sub>l\<^sub>h (p', ids')"
  shows "\<rho> \<Turnstile>\<^sub>l\<^sub>h (p, ids)"
  using assms
proof -
  from assms(2) have "\<forall>\<sigma>. \<lbrakk>\<^bold>+ p' ids'\<rbrakk>\<^sub>r\<^sub>h \<rho> \<sigma>"
    by fastforce
  then have "\<rho> \<Turnstile>\<^sub>c\<^sub>l\<^sub>s Cls p ids []"
    using assms(1) self_append_conv2 solves_rh.elims(3) prop_inf_last_from_cls_rh_to_cls by metis 
  then show "\<rho> \<Turnstile>\<^sub>l\<^sub>h (p, ids)"
    by (meson solves_lh_lh)
qed

lemma prop_inf_only_from_cls_cls_to_cls:
  assumes "\<rho> \<Turnstile>\<^sub>c\<^sub>l\<^sub>s Cls p ids [\<^bold>+ p' ids']"
  assumes "\<rho> \<Turnstile>\<^sub>c\<^sub>l\<^sub>s Cls p' ids' []"
  shows "\<rho> \<Turnstile>\<^sub>c\<^sub>l\<^sub>s Cls p ids []"
  by (metis append_self_conv2 assms prop_inf_last_from_cls_rh_to_cls solves_lh_iff_solves_lh)

lemmas prop_inf_only = modus_ponens_rh prop_inf_only_from_cls_cls_to_cls


subsubsection \<open>Of all right hands\<close>

lemma modus_ponens:
  assumes "\<rho> \<Turnstile>\<^sub>c\<^sub>l\<^sub>s Cls p ids rhs"
  assumes "\<forall>rh\<in>set rhs. \<rho> \<Turnstile>\<^sub>r\<^sub>h rh"
  shows "\<rho> \<Turnstile>\<^sub>l\<^sub>h (p, ids)"
  using assms unfolding solves_cls_def meaning_lh.simps by force

lemmas prop_inf_all = modus_ponens

lemmas prop_inf = prop_inf_last prop_inf_only prop_inf_all

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
  case (PosLit p ids)
  then show ?case
    using substitution_lemma_lh by fastforce
next
  case (NegLit p ids)
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

lemma substitution_lemma:
  assumes "\<rho> \<Turnstile>\<^sub>c\<^sub>l\<^sub>s c"
  shows "\<rho> \<Turnstile>\<^sub>c\<^sub>l\<^sub>s (c \<cdot>\<^sub>c\<^sub>l\<^sub>s (\<eta>::('x,'c) subst))"
proof -
  show ?thesis
    unfolding solves_cls_def
  proof
    fix \<sigma> :: "'x \<Rightarrow> 'c"
    from assms have "\<lbrakk>c\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho> (\<eta> \<circ>\<^sub>s\<^sub>v \<sigma>)"
      using solves_cls_def by auto
    then show "\<lbrakk>c \<cdot>\<^sub>c\<^sub>l\<^sub>s \<eta> \<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho> \<sigma>"
      using substitution_lemma_cls by blast
  qed
qed


section \<open>Stratification and solutions to stratified datalog programs\<close>

type_synonym 'p strat = "'p \<Rightarrow> nat"

fun rnk :: "'p strat \<Rightarrow> ('p,'x,'c) rh \<Rightarrow> nat" where
  "rnk s (a \<^bold>= a') = 0"
| "rnk s (a \<^bold>\<noteq> a') = 0"
| "rnk s (\<^bold>+ p ids) = s p"
| "rnk s (\<^bold>\<not> p ids) = 1 + s p"

fun strat_wf_cls :: "'p strat \<Rightarrow> ('p,'x,'c) clause \<Rightarrow> bool" where
  "strat_wf_cls s (Cls p ids rhs) \<longleftrightarrow> (\<forall>rh \<in> set rhs. s p \<ge> rnk s rh)"

definition strat_wf :: "'p strat \<Rightarrow> ('p,'x,'c) dl_program \<Rightarrow> bool" where
  "strat_wf s dl \<longleftrightarrow> (\<forall>c \<in> dl. strat_wf_cls s c)"

definition max_strata :: "'p strat \<Rightarrow> ('p,'x,'c) dl_program \<Rightarrow> nat" where
  "max_strata s dl = Max {s p | p ids rhs. Cls p ids rhs \<in> dl}"

fun pred_val_mod_strata :: "('p,'c) pred_val \<Rightarrow> 'p strat \<Rightarrow> nat \<Rightarrow> ('p,'c) pred_val" ("_ \\_\\ _" 0) where 
  "(\<rho> \\s\\ n) p = (if s p \<le> n then \<rho> p else {})"

fun dl_program_mod_strata :: "('p,'x,'c) dl_program \<Rightarrow> 'p strat \<Rightarrow> nat \<Rightarrow> ('p,'x,'c) dl_program" ("_ --_-- _" 0) where 
  "(dl -- s -- n) = {(Cls p ids rhs)| p ids rhs . (Cls p ids rhs) \<in> dl \<and> s p \<le> n}"

fun dl_program_on_strata :: "('p,'x,'c) dl_program \<Rightarrow> 'p strat \<Rightarrow> nat \<Rightarrow> ('p,'x,'c) dl_program" ("_ ==_== _" 0) where 
  "(dl == s == n) = {(Cls p ids rhs)| p ids rhs . (Cls p ids rhs) \<in> dl \<and> s p = n}"

definition lt :: "('p,'c) pred_val \<Rightarrow> 'p strat \<Rightarrow> ('p,'c) pred_val \<Rightarrow> bool" ("_ \<sqsubset>_\<sqsubset> _") where
  "(\<rho> \<sqsubset>s\<sqsubset> \<rho>') \<longleftrightarrow> (\<exists>p. \<rho> p \<subset> \<rho>' p \<and>
                       (\<forall>p'. s p' = s p \<longrightarrow> \<rho> p' \<subseteq> \<rho>' p') \<and>
                       (\<forall>p'. s p' < s p \<longrightarrow> \<rho> p' = \<rho>' p'))"

definition lte :: "('p,'c) pred_val \<Rightarrow> 'p strat \<Rightarrow> ('p,'c) pred_val \<Rightarrow> bool" ("_ \<sqsubseteq>_\<sqsubseteq> _") where
  "(\<rho> \<sqsubseteq>s\<sqsubseteq> \<rho>') \<longleftrightarrow> \<rho> = \<rho>' \<or> (\<rho> \<sqsubset>s\<sqsubset> \<rho>')"

definition least_solution :: "('p,'c) pred_val \<Rightarrow> ('p,'x,'c) dl_program \<Rightarrow> 'p strat \<Rightarrow> bool" ("_ \<Turnstile>\<^sub>l\<^sub>s\<^sub>t") where
  "\<rho> \<Turnstile>\<^sub>l\<^sub>s\<^sub>t dl s \<longleftrightarrow> \<rho> \<Turnstile>\<^sub>d\<^sub>l dl \<and> (\<forall>\<rho>'. \<rho>' \<Turnstile>\<^sub>d\<^sub>l dl \<longrightarrow> \<rho> \<sqsubseteq>s\<sqsubseteq> \<rho>')"

definition minimal_solution :: "('p,'c) pred_val \<Rightarrow> ('p,'x,'c) dl_program \<Rightarrow> 'p strat \<Rightarrow> bool"  ("_ \<Turnstile>\<^sub>m\<^sub>i\<^sub>n") where
  "\<rho> \<Turnstile>\<^sub>m\<^sub>i\<^sub>n dl s \<longleftrightarrow> \<rho> \<Turnstile>\<^sub>d\<^sub>l dl \<and> (\<nexists>\<rho>'. \<rho>' \<Turnstile>\<^sub>d\<^sub>l dl \<and> \<rho>' \<sqsubset>s\<sqsubset> \<rho>)"

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
  "(\<^bold>\<Inter> \<rho>s) = (\<lambda>p. \<Inter>{\<rho> p | \<rho>. \<rho> \<in> \<rho>s})"

lemma Inter'_def2: "(\<^bold>\<Inter> \<rho>s) = (\<lambda>p. \<Inter>{m. \<exists>\<rho> \<in> \<rho>s. m = \<rho> p})"
  apply rule
  apply (smt (verit, best) Collect_cong Inter'_def)
  done

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
  using assms by (force simp add: Inter'_def2)

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

lemma exi_sol_n: 
  "\<exists>\<rho>'. \<rho>' \<Turnstile>\<^sub>d\<^sub>l (dl ==s== Suc m) \<and> (\<rho>' \\s\\ m) = solve_pg s dl m"
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
  assumes "\<^bold>+ p' ids' \<in> set rhs"
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
  case (PosLit p' ids')
  then have "s p' \<le> m"
    using assms pos_rhs_strata_leq_clause_strata by fastforce
  moreover
  from PosLit have "s p' \<le> n"
    using assms pos_rhs_strata_leq_clause_strata by fastforce
  ultimately
  have "solve_pg s dl m p' = solve_pg s dl n p'"
    using solve_pg_two_agree_above[of s p' n m dl] by force
  then show ?thesis
    by (simp add: PosLit)
next
  case (NegLit p' ids)
  then have "s p' < m"
    using assms neg_rhs_strata_less_clause_strata by fastforce
  moreover
  from NegLit have "s p' < n"
    using assms neg_rhs_strata_less_clause_strata by fastforce
  ultimately
  have "solve_pg s dl m p' = solve_pg s dl n p'"
    using solve_pg_two_agree_above[of s p' n m dl] by force
  then show ?thesis
    by (simp add: NegLit)
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
  case (PosLit p ids)
  then show ?thesis
    using assms meaning_rh.simps(3) solve_pg_0_subset by fastforce
next
  case (NegLit p ids)
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
  case (PosLit p' ids')
  then show ?thesis
    using assms solve_pg_Suc_subset by fastforce
next
  case (NegLit p' ids')
  then have "s p' \<le> n"
    using strataSuc_less_neg[OF assms(1) assms(6), of p'] assms(5) by auto
  then have "\<lbrakk>rh\<rbrakk>\<^sub>r\<^sub>h (solve_pg s dl n) \<sigma>"
    by (metis NegLit assms(2) le_imp_less_Suc less_imp_le_nat meaning_rh.simps(4) solve_pg_two_agree_above)
  then have "\<lbrakk>rh\<rbrakk>\<^sub>r\<^sub>h (\<rho> \\s\\ n) \<sigma>"
    using assms(4) by presburger
  then show ?thesis
    by (simp add: NegLit \<open>s p' \<le> n\<close>)
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

lemma all_meaning_if_solve_pg_Suc_lh: (* Is this one used at all? *)
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

lemma solve_pg_meaning_cls':
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

lemma solve_pg_meaning_cls:
  assumes "strat_wf s dl"
  assumes "c \<in> (dl --s-- n)"
  shows "\<lbrakk>c\<rbrakk>\<^sub>c\<^sub>l\<^sub>s (solve_pg s dl n) \<sigma>"
  using assms solve_pg_meaning_cls'[of s dl] by (cases c) metis

lemma solve_pg_solves_cls:
  assumes "strat_wf s dl"
  assumes "c \<in> (dl --s-- n)"
  shows "solve_pg s dl n \<Turnstile>\<^sub>c\<^sub>l\<^sub>s c"
  unfolding solves_cls_def using solve_pg_meaning_cls assms by blast

lemma solve_pg_solves_dl:
  assumes "strat_wf s dl"
  shows "solve_pg s dl n \<Turnstile>\<^sub>d\<^sub>l (dl --s-- n)"
proof -
  have "\<forall>c \<in> (dl --s-- n). (solve_pg s dl n) \<Turnstile>\<^sub>c\<^sub>l\<^sub>s c"
    using assms solve_pg_solves_cls[of s dl] by auto
  then show "solve_pg s dl n \<Turnstile>\<^sub>d\<^sub>l (dl --s-- n)"
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
    have "\<exists>p. least_rank_p_st (\<lambda>p. \<rho>'' p \<noteq> \<rho> p) p s"
      by (meson \<open>\<rho>'' \<noteq> \<rho>\<close> ext least_rank_p_st_exists)
    then obtain p where p_p: "least_rank_p_st (\<lambda>p. \<rho>'' p \<noteq> \<rho> p) p s"
      by auto
    then have "\<rho>'' p \<subset> \<rho> p"
      by (metis (mono_tags, lifting) \<rho>''_subs_\<rho> least_rank_p_st_def psubsetI)
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

definition agree_below_eq :: "('p,'c) pred_val \<Rightarrow> ('p,'c) pred_val \<Rightarrow> nat \<Rightarrow> 'p strat \<Rightarrow> bool"  where
  "agree_below_eq \<rho> \<rho>' n s \<longleftrightarrow> (\<forall>p. s p \<le> n \<longrightarrow> \<rho> p = \<rho>' p)"

definition agree_below :: "('p,'c) pred_val \<Rightarrow> ('p,'c) pred_val \<Rightarrow> nat \<Rightarrow> 'p strat \<Rightarrow> bool"  where
  "agree_below \<rho> \<rho>' n s \<longleftrightarrow> (\<forall>p. s p < n \<longrightarrow> \<rho> p = \<rho>' p)"

definition agree_above :: "('p,'c) pred_val \<Rightarrow> ('p,'c) pred_val \<Rightarrow> nat \<Rightarrow> 'p strat \<Rightarrow> bool"  where
  "agree_above \<rho> \<rho>' n s \<longleftrightarrow> (\<forall>p. s p > n \<longrightarrow> \<rho> p = \<rho>' p)"

definition agree_above_eq :: "('p,'c) pred_val \<Rightarrow> ('p,'c) pred_val \<Rightarrow> nat \<Rightarrow> 'p strat \<Rightarrow> bool" where
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
           (\<forall>p'. s p' = s p \<longrightarrow> \<rho>''n p' \<subseteq> \<rho> p') \<and>
           (\<forall>p'. s p' < s p \<longrightarrow> \<rho>''n p' = \<rho> p')"
        using least_disagreement_proper_subset[of \<rho>''n s \<rho> p] subset_on_least_disagreement[of \<rho>''n s \<rho> p] 
          equal_below_least_disagreement[of \<rho>''n s \<rho> p] by metis
      then have "\<rho>''n1 p \<subset> \<rho> p \<and>
           (\<forall>p'. s p' = s p \<longrightarrow> \<rho>''n1 p' \<subseteq> \<rho> p') \<and>
           (\<forall>p'. s p' < s p \<longrightarrow> \<rho>''n1 p' = \<rho> p')"
        using B' \<open>s p \<le> n\<close> by (simp add: agree_below_eq_def)
      then show "\<rho>''n1 \<sqsubset>s\<sqsubset> \<rho>"
        unfolding lt_def by auto
    next
      assume "Suc n \<le> i"
      have "\<rho> \<Turnstile>\<^sub>d\<^sub>l (dl --s-- Suc n)"
        using Suc.prems by auto
      moreover
      have "(\<rho> \\s\\ n) = (solve_pg s dl n)"
      proof -
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
        have "agree_above \<rho>''n (\<rho> \\s\\ n) n s"
          using \<rho>''n_def by (simp add: agree_above_def solve_pg_Suc_empty)
        ultimately
        have "(\<rho> \\s\\ n) = \<rho>''n"
           using asjkdfla by blast
        then show "(\<rho> \\s\\ n) = (solve_pg s dl n)"
          using \<rho>''n_def by metis
      qed
      ultimately
      have "\<rho> \<Turnstile>\<^sub>d\<^sub>l (dl --s-- Suc n) \<and> (\<rho> \\s\\ n) = solve_pg s dl n"
        by auto
      then have "\<rho>''n1 p \<subseteq> \<rho> p"
        using solve_pg_subset_solution[of n "Suc n" \<rho> dl s p]
        using \<rho>''n1_def by fastforce 
      then have "\<rho>''n1 p \<subset> \<rho> p"
        using dis by auto
      moreover
      have "\<forall>p'. s p' = s p \<longrightarrow> \<rho>''n1 p' \<subseteq> \<rho> p'"
        using \<open>\<rho> \<Turnstile>\<^sub>d\<^sub>l (dl --s-- Suc n) \<and> (\<rho> \s\ n) = solve_pg s dl n\<close> \<rho>''n1_def solve_pg_subset_solution by fastforce
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

lemma solve_pg_least_solution':
  assumes "strat_wf s dl"
  shows "(solve_pg s dl n) \<Turnstile>\<^sub>l\<^sub>s\<^sub>t (dl --s-- n) s"
  using assms least_solution_def solve_pg_below_solution solve_pg_solves_dl by blast 

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

lemma exi_least_solution:
  assumes "finite dl"
  assumes "strat_wf s dl"
  shows "\<exists>\<rho>. \<rho> \<Turnstile>\<^sub>l\<^sub>s\<^sub>t dl s"
  using assms solve_pg_least_solution by metis


subsubsection \<open>Equality of least and minimal solution\<close>

lemma least_iff_minimal:
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
  have s_dl_m: "strat_wf s (dl --s-- m)"
    using assms strat_wf_mod_if_strat_wf by auto
  have strrrr: "strat_wf s (dl --s-- n)"
    using assms strat_wf_mod_if_strat_wf by auto
  from a have "\<not> (\<rho> \\s\\ m) \<Turnstile>\<^sub>m\<^sub>i\<^sub>n (dl --s-- m) s"
    using least_iff_minimal s_dl_m assms(1) finite_below_finite by metis
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
    b:"\<forall>p'. s p' = s p \<longrightarrow> \<rho>' p' \<subseteq> (\<rho> \\s\\ m) p'" and
    c:"\<forall>p'. s p' < s p \<longrightarrow> \<rho>' p' = (\<rho> \\s\\ m) p'"
    by auto
  define \<rho>'' where "\<rho>'' == \<lambda>p. if s p \<le> m then \<rho>' p else UNIV"

  have "s p \<le> m"
    using a by auto
  then have "\<rho>'' p \<subset> \<rho> p"
    unfolding \<rho>''_def using a by auto
  moreover
  have "\<forall>p'. s p' = s p \<longrightarrow> \<rho>'' p' \<subseteq> \<rho> p'"
    using b
    by (metis \<rho>''_def calculation pred_val_mod_strata.simps top.extremum_strict)
  moreover
  have "\<forall>p'. s p' < s p \<longrightarrow> \<rho>'' p' = \<rho> p'"
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
        then have "\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho>' \<sigma>"
          using tt c_def solves_cls_def solves_program_def by blast
        
        show ?thesis
          unfolding meaning_cls.simps
        proof
          assume "\<lbrakk>rhs\<rbrakk>\<^sub>r\<^sub>h\<^sub>s \<rho>'' \<sigma>"
          have "\<lbrakk>rhs\<rbrakk>\<^sub>r\<^sub>h\<^sub>s \<rho>' \<sigma>"
            unfolding meaning_rhs.simps
          proof
            fix rh
            assume "rh \<in> set rhs"
            then have "\<lbrakk>rh\<rbrakk>\<^sub>r\<^sub>h \<rho>'' \<sigma>"
              using \<open>\<lbrakk>rhs\<rbrakk>\<^sub>r\<^sub>h\<^sub>s \<rho>'' \<sigma>\<close> by force
            then show "\<lbrakk>rh\<rbrakk>\<^sub>r\<^sub>h \<rho>' \<sigma>"
            proof (cases rh)
              case (Eql a a')
              then show ?thesis
                using \<open>\<lbrakk>rh\<rbrakk>\<^sub>r\<^sub>h \<rho>'' \<sigma>\<close> by auto
            next
              case (Neql a a')
              then show ?thesis
                using \<open>\<lbrakk>rh\<rbrakk>\<^sub>r\<^sub>h \<rho>'' \<sigma>\<close> by auto
            next
              case (PosLit p ids)
              then show ?thesis
                using \<open>\<lbrakk>rh\<rbrakk>\<^sub>r\<^sub>h \<rho>'' \<sigma>\<close> \<open>c \<in> (dl --s-- m)\<close> \<open>rh \<in> set rhs\<close> \<rho>''_def assms(3) c_def 
                  pos_rhs_strata_leq_clause_strata by fastforce
            next
              case (NegLit p ids)
              then show ?thesis
                using \<open>\<lbrakk>rh\<rbrakk>\<^sub>r\<^sub>h \<rho>'' \<sigma>\<close> \<open>c \<in> (dl --s-- m)\<close> \<open>rh \<in> set rhs\<close> \<rho>''_def c_def 
                  neg_rhs_strata_less_clause_strata s_dl_m by fastforce
            qed
          qed
          then have "\<lbrakk>(p, ids)\<rbrakk>\<^sub>l\<^sub>h \<rho>' \<sigma>"
            using \<open>\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho>' \<sigma>\<close> by force
          then show  "\<lbrakk>(p, ids)\<rbrakk>\<^sub>l\<^sub>h \<rho>'' \<sigma>"
            using \<rho>''_def by force
        qed
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
    using least_iff_minimal strrrr finite_below_finite assms by metis
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
    using least_iff_minimal strrr finite_below_finite assms by metis  
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
      fix \<sigma>
      show "\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho>'' \<sigma>"
      proof (cases "s p \<le> m")
        case True
        then have "c \<in> (dl --s-- m)"
          using a c_def by auto
        then have "\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho>' \<sigma>"
          using tt c_def solves_cls_def solves_program_def by blast
        
        show ?thesis
          unfolding meaning_cls.simps
        proof
          assume "\<lbrakk>rhs\<rbrakk>\<^sub>r\<^sub>h\<^sub>s \<rho>'' \<sigma>"
          have "\<lbrakk>rhs\<rbrakk>\<^sub>r\<^sub>h\<^sub>s \<rho>' \<sigma>"
            unfolding meaning_rhs.simps
          proof
            fix rh
            assume "rh \<in> set rhs"
            then have "\<lbrakk>rh\<rbrakk>\<^sub>r\<^sub>h \<rho>'' \<sigma>"
              using \<open>\<lbrakk>rhs\<rbrakk>\<^sub>r\<^sub>h\<^sub>s \<rho>'' \<sigma>\<close> by force
            then show "\<lbrakk>rh\<rbrakk>\<^sub>r\<^sub>h \<rho>' \<sigma>"
            proof (cases rh)
              case (Eql a a')
              then show ?thesis
                using \<open>\<lbrakk>rh\<rbrakk>\<^sub>r\<^sub>h \<rho>'' \<sigma>\<close> by auto
            next
              case (Neql a a')
              then show ?thesis
                using \<open>\<lbrakk>rh\<rbrakk>\<^sub>r\<^sub>h \<rho>'' \<sigma>\<close> by auto
            next
              case (PosLit p ids)
              then show ?thesis
                using \<open>\<lbrakk>rh\<rbrakk>\<^sub>r\<^sub>h \<rho>'' \<sigma>\<close> \<open>c \<in> (dl --s-- m)\<close> \<open>rh \<in> set rhs\<close> \<rho>''_def c_def 
                  pos_rhs_strata_leq_clause_strata strrr by fastforce 
            next
              case (NegLit p ids)
              then show ?thesis
                using \<open>\<lbrakk>rh\<rbrakk>\<^sub>r\<^sub>h \<rho>'' \<sigma>\<close> \<open>c \<in> (dl --s-- m)\<close> \<open>rh \<in> set rhs\<close> \<rho>''_def c_def 
                  by (metis (full_types, opaque_lifting) UNIV_I meaning_rh.simps(4)) 
            qed
          qed
          then have "\<lbrakk>(p, ids)\<rbrakk>\<^sub>l\<^sub>h \<rho>' \<sigma>"
            using \<open>\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho>' \<sigma>\<close> by force
          then show  "\<lbrakk>(p, ids)\<rbrakk>\<^sub>l\<^sub>h \<rho>'' \<sigma>"
            using \<rho>''_def by force
        qed
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
    using least_iff_minimal[OF assms(1) assms(2)] by metis
  then show "False"
    using assms by auto
qed

subsection \<open>Negation\<close>

lemma eval_id_is_substv_id:
  "\<lbrakk>ids'\<rbrakk>\<^sub>i\<^sub>d \<sigma>' = \<lbrakk>ids\<rbrakk>\<^sub>i\<^sub>d \<sigma> \<longleftrightarrow> (ids' \<cdot>\<^sub>v\<^sub>i\<^sub>d \<sigma>') = (ids \<cdot>\<^sub>v\<^sub>i\<^sub>d \<sigma>)"
  by (cases ids'; cases ids) auto

lemma eval_ids_is_substv_ids:
  "\<lbrakk>ids'\<rbrakk>\<^sub>i\<^sub>d\<^sub>s \<sigma>' = \<lbrakk>ids\<rbrakk>\<^sub>i\<^sub>d\<^sub>s \<sigma> \<longleftrightarrow> (ids' \<cdot>\<^sub>v\<^sub>i\<^sub>d\<^sub>s \<sigma>') = (ids \<cdot>\<^sub>v\<^sub>i\<^sub>d\<^sub>s \<sigma>)"
proof (induction ids' arbitrary: ids)
  case Nil
  then show ?case 
    by auto
next
  case (Cons a ids')
  note Cons_outer = Cons
  show ?case
  proof (cases ids)
    case Nil
    then show ?thesis
      using Cons_outer by auto
  next
    case (Cons a list)
    then show ?thesis
      using eval_id_is_substv_id Cons_outer by force
  qed
qed

definition agree_var_val :: "'x set \<Rightarrow> ('x, 'c) var_val \<Rightarrow> ('x, 'c) var_val \<Rightarrow> bool " where
  "agree_var_val xs \<sigma> \<sigma>' \<longleftrightarrow> (\<forall>x \<in> xs. \<sigma> x = \<sigma>' x)"

fun vars_ids :: "('a, 'b) id list \<Rightarrow> 'a set" where
  "vars_ids ids = \<Union>(vars_id ` set ids)"

fun vars_lh :: "('p,'x,'c) lh \<Rightarrow> 'x set" where
  "vars_lh (p,ids) = vars_ids ids"

definition lh_consequence :: "('p, 'c) pred_val \<Rightarrow> ('p, 'x, 'c) clause \<Rightarrow> ('p, 'x, 'c) lh \<Rightarrow> bool" where
  "lh_consequence \<rho> c lh \<longleftrightarrow> (\<exists>\<sigma>'. ((the_lh c) \<cdot>\<^sub>v\<^sub>l\<^sub>h \<sigma>') = lh \<and> \<lbrakk>the_rhs c\<rbrakk>\<^sub>r\<^sub>h\<^sub>s \<rho> \<sigma>')"

lemma hjklasdfhkljfdfsdhjkljhbhjbfjksdfajkh:
  assumes "c \<in> (dl --s-- s p)"
  assumes "strat_wf s dl"
  assumes "rh \<in> set (the_rhs c)"
  shows "\<lbrakk>rh\<rbrakk>\<^sub>r\<^sub>h \<rho> \<sigma>' \<longleftrightarrow> \<lbrakk>rh\<rbrakk>\<^sub>r\<^sub>h (\<rho> \\s\\ s p) \<sigma>'"
proof (cases rh)
  case (Eql a a')
  then show ?thesis 
    by auto
next
  case (Neql a a')
  then show ?thesis 
    by auto
next
  case (PosLit p' ids)
  show ?thesis
  proof
    assume "\<lbrakk>rh\<rbrakk>\<^sub>r\<^sub>h \<rho> \<sigma>'"
    then show "\<lbrakk>rh\<rbrakk>\<^sub>r\<^sub>h (\<rho> \\s\\ s p) \<sigma>'"
      using PosLit assms pos_rhs_strata_leq_clause_strata by fastforce
  next
    assume "\<lbrakk>rh\<rbrakk>\<^sub>r\<^sub>h (\<rho> \\s\\ s p) \<sigma>'"
    then show "\<lbrakk>rh\<rbrakk>\<^sub>r\<^sub>h \<rho> \<sigma>'"
      by (metis PosLit equals0D meaning_rh.simps(3) pred_val_mod_strata.simps)
  qed
next
  case (NegLit p' ids)
  show ?thesis
  proof
    assume "\<lbrakk>rh\<rbrakk>\<^sub>r\<^sub>h \<rho> \<sigma>'"
    then show "\<lbrakk>rh\<rbrakk>\<^sub>r\<^sub>h (\<rho> \\s\\ s p) \<sigma>'"
      using NegLit assms by fastforce
  next
    assume "\<lbrakk>rh\<rbrakk>\<^sub>r\<^sub>h (\<rho> \\s\\ s p) \<sigma>'"
    then show "\<lbrakk>rh\<rbrakk>\<^sub>r\<^sub>h \<rho> \<sigma>'"
      using NegLit assms(1) assms(2) assms(3) neg_rhs_strata_less_clause_strata by fastforce
  qed
qed

lemma hjklasdfhkljfdfsdhjkljhbhjbfjksdfajkh2:
  assumes "c \<in> (dl --s-- s p)"
  assumes "strat_wf s dl"
  shows "\<lbrakk>the_rhs c\<rbrakk>\<^sub>r\<^sub>h\<^sub>s \<rho> \<sigma>' \<longleftrightarrow> \<lbrakk>the_rhs c\<rbrakk>\<^sub>r\<^sub>h\<^sub>s (\<rho> \\s\\ s p) \<sigma>'"
  by (meson assms(1) assms(2) hjklasdfhkljfdfsdhjkljhbhjbfjksdfajkh meaning_rhs.simps)

lemma add_to_rhs_ajsdfjsakldfjklasjfjkldfajl: (* TODO: is this a kind of monotonicity? *)
  assumes "\<lbrakk>rhs'\<rbrakk>\<^sub>r\<^sub>h\<^sub>s \<rho>'' \<sigma>'"
  assumes "strat_wf s dl"
  assumes \<rho>''_def: "\<rho>'' = (\<lambda>p'. if p' = p then \<rho>' p - {\<lbrakk>ids\<rbrakk>\<^sub>i\<^sub>d\<^sub>s \<sigma>} else \<rho>' p')"
  assumes c_dl': "Cls p' ids' rhs' \<in> (dl --s-- s p)"
  shows "\<lbrakk>rhs'\<rbrakk>\<^sub>r\<^sub>h\<^sub>s \<rho>' \<sigma>'"
proof -
(* The only difference is that \<rho>' makes p(ids\<sigma>) true, but \<rho>'' makes it false.
   That atom can not occur as a negative literal in rhs'.
   But on all other possible literals \<rho>'' and \<rho>' agree and so they must agree on the rest of rhs'.
 *)

  have "\<forall>rh' \<in> set rhs'. rnk s rh' \<le> s p'"
    using assms(2) c_dl' in_mono strat_wf_cls.simps strat_wf_def by fastforce

  show ?thesis
    unfolding meaning_rhs.simps
  proof
    fix rh
    assume "rh \<in> set rhs'"
    show "\<lbrakk>rh\<rbrakk>\<^sub>r\<^sub>h \<rho>' \<sigma>'"
    proof (cases rh)
      case (Eql a a')
      then show ?thesis
        using \<open>rh \<in> set rhs'\<close> assms(1) by auto
    next
      case (Neql a a')
      then show ?thesis
        using \<open>rh \<in> set rhs'\<close> assms(1) by auto
    next
      case (PosLit p'' ids'')
      then show ?thesis
        by (metis Diff_iff \<open>rh \<in> set rhs'\<close> \<rho>''_def assms(1) meaning_rh.simps(3) meaning_rhs.elims(2))
    next
      case (NegLit p'' ids'')
      have "p'' \<noteq> p"
        using NegLit One_nat_def \<open>\<forall>rh'\<in>set rhs'. rnk s rh' \<le> s p'\<close> \<open>rh \<in> set rhs'\<close> c_dl' by fastforce
      then show ?thesis
        using NegLit  \<open>rh \<in> set rhs'\<close> \<rho>''_def assms(1) by auto
    qed
  qed
qed

lemma meaning_PosLit_least':
  assumes "finite dl"
  assumes "\<rho> \<Turnstile>\<^sub>l\<^sub>s\<^sub>t dl s"
  assumes "strat_wf s dl"
  assumes "\<lbrakk>\<^bold>+ p ids\<rbrakk>\<^sub>r\<^sub>h \<rho> \<sigma>"
  shows "\<exists>c \<in> dl. lh_consequence \<rho> c ((p,ids) \<cdot>\<^sub>v\<^sub>l\<^sub>h \<sigma>)"
proof (rule ccontr)
  assume "\<not>(\<exists>c \<in> dl. lh_consequence \<rho> c ((p,ids) \<cdot>\<^sub>v\<^sub>l\<^sub>h \<sigma>))"
  then have "\<not>(\<exists>c \<in> dl. \<exists>\<sigma>'. ((the_lh c) \<cdot>\<^sub>v\<^sub>l\<^sub>h \<sigma>') = ((p,ids) \<cdot>\<^sub>v\<^sub>l\<^sub>h \<sigma>) \<and> (\<lbrakk>the_rhs c\<rbrakk>\<^sub>r\<^sub>h\<^sub>s \<rho> \<sigma>'))"
    unfolding lh_consequence_def by auto
  then have a: "\<forall>c \<in> dl. \<forall>\<sigma>'. ((the_lh c) \<cdot>\<^sub>v\<^sub>l\<^sub>h \<sigma>') = ((p,ids) \<cdot>\<^sub>v\<^sub>l\<^sub>h \<sigma>) \<longrightarrow> \<not>(\<lbrakk>the_rhs c\<rbrakk>\<^sub>r\<^sub>h\<^sub>s \<rho> \<sigma>')"
    by metis

  define \<rho>' where "\<rho>' = (\<rho> \\s\\ s p)"
  define dl' where "dl' = (dl --s-- s p)"

  have \<rho>'_least: "\<rho>' \<Turnstile>\<^sub>l\<^sub>s\<^sub>t dl' s"
    using downward_solves[of \<rho> dl s] assms downward_least_solution2 unfolding \<rho>'_def dl'_def by blast
  moreover
  have no_match: "\<forall>c \<in> dl'. \<forall>\<sigma>'. ((the_lh c) \<cdot>\<^sub>v\<^sub>l\<^sub>h \<sigma>') = ((p,ids) \<cdot>\<^sub>v\<^sub>l\<^sub>h \<sigma>) \<longrightarrow> \<not>(\<lbrakk>the_rhs c\<rbrakk>\<^sub>r\<^sub>h\<^sub>s \<rho>' \<sigma>')"
    using a
    unfolding dl'_def \<rho>'_def
    by (meson assms(3) below_subset hjklasdfhkljfdfsdhjkljhbhjbfjksdfajkh2 in_mono)

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
        then have rhs'_true: "\<lbrakk>rhs'\<rbrakk>\<^sub>r\<^sub>h\<^sub>s \<rho>' \<sigma>'" 
          using add_to_rhs_ajsdfjsakldfjklasjfjkldfajl[of rhs' \<rho>'' \<sigma>' s dl p \<rho>']
            \<rho>''_def assms(3) c_dl' c_split dl'_def by blast
        have "\<lbrakk>(p',ids')\<rbrakk>\<^sub>l\<^sub>h \<rho>' \<sigma>'"
          by (metis rhs'_true c_split c_dl' \<rho>'_least clause.inject least_solution_def meaning_cls.elims(2) solves_cls_def solves_program_def)
        moreover
        have "((p', ids') \<cdot>\<^sub>v\<^sub>l\<^sub>h \<sigma>') \<noteq> ((p, ids) \<cdot>\<^sub>v\<^sub>l\<^sub>h \<sigma>)"
          using no_match rhs'_true c_split c_dl' by fastforce
        ultimately
        show "\<lbrakk>(p', ids')\<rbrakk>\<^sub>l\<^sub>h \<rho>'' \<sigma>'"
          using  \<rho>''_def eval_ids_is_substv_ids by auto
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
      using DiffD2 \<open>\<lbrakk>\<^bold>+ p ids\<rbrakk>\<^sub>r\<^sub>h \<rho> \<sigma>\<close> \<rho>''_def \<rho>'_def by auto
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
    by (metis assms(1,3) dl'_def finite_below_finite least_iff_minimal minimal_solution_def strat_wf_mod_if_strat_wf)
qed

lemma meaning_PosLit_least:
  assumes "finite dl"
  assumes "\<rho> \<Turnstile>\<^sub>l\<^sub>s\<^sub>t dl s"
  assumes "strat_wf s dl"
  shows "\<lbrakk>\<^bold>+ p ids\<rbrakk>\<^sub>r\<^sub>h \<rho> \<sigma> \<longleftrightarrow> (\<exists>c \<in> dl. lh_consequence \<rho> c ((p,ids) \<cdot>\<^sub>v\<^sub>l\<^sub>h \<sigma>))"
proof
  assume "\<lbrakk>\<^bold>+ p ids\<rbrakk>\<^sub>r\<^sub>h \<rho> \<sigma>"
  then show "\<exists>c \<in> dl. lh_consequence \<rho> c ((p,ids) \<cdot>\<^sub>v\<^sub>l\<^sub>h \<sigma>)"
    by (meson assms(1) assms(2) assms(3) meaning_PosLit_least')
next
  assume "\<exists>c \<in> dl. lh_consequence \<rho> c ((p,ids) \<cdot>\<^sub>v\<^sub>l\<^sub>h \<sigma>)"
  then show "\<lbrakk>\<^bold>+ p ids\<rbrakk>\<^sub>r\<^sub>h \<rho> \<sigma>"
    unfolding lh_consequence_def
    using assms(2) eval_ids_is_substv_ids least_solution_def meaning_cls.simps meaning_lh.simps solves_cls_def 
      solves_program_def clause.exhaust clause.sel(3) meaning_rh.simps(3) 
      prod.inject substv_lh.simps the_lh.simps by metis
qed

lemma solves_PosLit_least:
  assumes "finite dl"
  assumes "\<rho> \<Turnstile>\<^sub>l\<^sub>s\<^sub>t dl s"
  assumes "strat_wf s dl"
  assumes "\<forall>a \<in> set ids. is_Cst a"
  shows "\<rho> \<Turnstile>\<^sub>r\<^sub>h (\<^bold>+ p ids) \<longleftrightarrow> (\<exists>c \<in> dl. lh_consequence \<rho> c (p,ids))"
proof -
  have "\<forall>\<sigma>. ((p, ids) \<cdot>\<^sub>v\<^sub>l\<^sub>h \<sigma>) = (p, ids)"
    using assms(4) by (induction ids) (auto simp add: is_Cst_def)
  then show ?thesis
    by (metis assms(1) assms(2) assms(3) meaning_PosLit_least solves_rh.simps)
qed

lemma meaning_NegLit_least:
  assumes "finite dl"
  assumes "\<rho> \<Turnstile>\<^sub>l\<^sub>s\<^sub>t dl s"
  assumes "strat_wf s dl"
  shows "\<lbrakk>\<^bold>\<not> p ids\<rbrakk>\<^sub>r\<^sub>h \<rho> \<sigma> \<longleftrightarrow> (\<not>(\<exists>c \<in> dl. lh_consequence \<rho> c ((p,ids) \<cdot>\<^sub>v\<^sub>l\<^sub>h \<sigma>)))"
  by (metis assms(1) assms(2) assms(3) meaning_PosLit_least meaning_rh.simps(3) meaning_rh.simps(4))

lemma solves_NegLit_least:
  assumes "finite dl"
  assumes "\<rho> \<Turnstile>\<^sub>l\<^sub>s\<^sub>t dl s"
  assumes "strat_wf s dl"
  assumes "\<forall>a \<in> set ids. is_Cst a"
  shows "\<rho> \<Turnstile>\<^sub>r\<^sub>h (\<^bold>\<not> p ids) \<longleftrightarrow> \<not>(\<exists>c \<in> dl. lh_consequence \<rho> c (p,ids))"
proof -
  have "\<forall>\<sigma>. ((p, ids) \<cdot>\<^sub>v\<^sub>l\<^sub>h \<sigma>) = (p, ids)"
    using assms(4) by (induction ids) (auto simp add: is_Cst_def)
  then show ?thesis
    by (metis assms(1) assms(2) assms(3) meaning_NegLit_least solves_rh.simps)
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
  the_RD
  | the_VAR

abbreviation Cst\<^sub>R\<^sub>D\<^sub>N :: "'n \<Rightarrow> (RD_var, ('n, 'v) RD_elem) id" where
  "Cst\<^sub>R\<^sub>D\<^sub>N q == Cst (RD_Node q)"

fun Cst\<^sub>R\<^sub>D\<^sub>N_Q :: "'n option \<Rightarrow> (RD_var, ('n, 'v) RD_elem) id" where
  "Cst\<^sub>R\<^sub>D\<^sub>N_Q (Some q) = Cst (RD_Node q)"
| "Cst\<^sub>R\<^sub>D\<^sub>N_Q None = Cst Questionmark"

abbreviation Cst\<^sub>R\<^sub>D\<^sub>V :: "'v \<Rightarrow> (RD_var, ('n, 'v) RD_elem) id" where
  "Cst\<^sub>R\<^sub>D\<^sub>V v == Cst (RD_Var v)"

abbreviation RD_Cls :: "(RD_var, ('n, 'v) RD_elem) id list \<Rightarrow> (RD_pred, RD_var, ('n, 'v) RD_elem) rh list \<Rightarrow> (RD_pred, RD_var, ('n, 'v) RD_elem) clause" ("RD\<langle>_\<rangle> :- _ .") where 
  "RD\<langle>args\<rangle> :- ls. \<equiv> Cls the_RD args ls"

abbreviation VAR_Cls :: "'v \<Rightarrow> (RD_pred, RD_var, ('n, 'v) RD_elem) clause" ("VAR\<langle>_\<rangle> :-.") where
  "VAR\<langle>x\<rangle> :-. == Cls the_VAR [Cst\<^sub>R\<^sub>D\<^sub>V x] []"

abbreviation RD_Fact :: "(RD_var, ('n, 'v) RD_elem) id list \<Rightarrow> (RD_pred, RD_var, ('n, 'v) RD_elem) lh" ("RD\<langle>_\<rangle>.") where 
  "RD\<langle>args\<rangle>. \<equiv> (the_RD, args)"

abbreviation VAR_Fact :: "'v \<Rightarrow> (RD_pred, RD_var, ('n, 'v) RD_elem) lh" ("VAR\<langle>_\<rangle>.") where 
  "VAR\<langle>x\<rangle>. \<equiv> (the_VAR, [Cst\<^sub>R\<^sub>D\<^sub>V x])"


abbreviation "RD == PosLit the_RD"
abbreviation "VAR == PosLit the_VAR"

abbreviation \<u> :: "(RD_var, 'a) id" where
  "\<u> == Var the_\<u>"

abbreviation \<v> :: "(RD_var, 'a) id" where
  "\<v> == Var the_\<v>"

abbreviation \<w> :: "(RD_var, 'a) id" where
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
       \<pi> \<in> LTS.path_with_word_from es start \<longrightarrow>
       (x, q1, q2) \<in> def_path \<pi> start \<longrightarrow> 
       \<rho> \<Turnstile>\<^sub>l\<^sub>h RD\<langle>[Cst\<^sub>R\<^sub>D\<^sub>N (LTS.get_end \<pi>), Cst\<^sub>R\<^sub>D\<^sub>V x, Cst\<^sub>R\<^sub>D\<^sub>N_Q q1, Cst\<^sub>R\<^sub>D\<^sub>N q2]\<rangle>.)"

lemma def_var_x: "fst (def_var ts x start) = x"
  unfolding def_var_def by (simp add: case_prod_beta def_of_def)

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
      using assms y_p unfolding def_var_def def_of_def by auto
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
      using assms y_p unfolding def_var_def def_of_def by auto
  next
    case False
    then show ?thesis
      by (metis y_p def_var_x fst_conv)
  qed
  then show ?thesis
    by (simp add: def_path_def)
qed

theorem RD_sound': 
  assumes "(ss,w) \<in> LTS.path_with_word_from es start"
  assumes "(x,q1,q2) \<in> def_path (ss,w) start"
  assumes "\<rho> \<Turnstile>\<^sub>d\<^sub>l (var_contraints \<union> ana_RD (es, start, end))"
  shows "\<rho> \<Turnstile>\<^sub>l\<^sub>h RD\<langle>[Cst\<^sub>R\<^sub>D\<^sub>N (LTS.get_end (ss, w)), Cst\<^sub>R\<^sub>D\<^sub>V x, Cst\<^sub>R\<^sub>D\<^sub>N_Q q1, Cst\<^sub>R\<^sub>D\<^sub>N q2]\<rangle>."
  using assms 
proof (induction rule: LTS.path_with_word_from_induct_reverse[OF assms(1)])
  case (1 s)
  have "VAR\<langle>x\<rangle> :-. \<in> var_contraints"
    unfolding var_contraints_def by auto
  from assms(3) this have "\<rho> \<Turnstile>\<^sub>c\<^sub>l\<^sub>s VAR\<langle>x\<rangle> :-."
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
    using assms(3) unfolding solves_program_def by auto 
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
    then have sq: "Some s = q1 \<and> s' = q2" using 2(5)
      using last_def_transition[of ss w x \<alpha> q1 q2 s s'] len by auto
    from True have "\<exists>e. (s,x ::= e,s') \<in> es"
      using "2.hyps"(2) by (cases \<alpha>) auto
    then have "RD\<langle>[Cst\<^sub>R\<^sub>D\<^sub>N q2, Cst\<^sub>R\<^sub>D\<^sub>V x, Cst\<^sub>R\<^sub>D\<^sub>N_Q q1, Cst\<^sub>R\<^sub>D\<^sub>N q2]\<rangle> :- []. \<in> ana_RD (es, start, end)"
      using True ana_RD.simps sq by fastforce
    then have "\<rho> \<Turnstile>\<^sub>c\<^sub>l\<^sub>s RD\<langle>[Cst\<^sub>R\<^sub>D\<^sub>N q2, Cst\<^sub>R\<^sub>D\<^sub>V x, Cst\<^sub>R\<^sub>D\<^sub>N_Q q1, Cst\<^sub>R\<^sub>D\<^sub>N q2]\<rangle> :- [] ."
      using 2(6) unfolding solves_program_def by auto
    then have "\<rho> \<Turnstile>\<^sub>l\<^sub>h RD\<langle>[Cst\<^sub>R\<^sub>D\<^sub>N q2, Cst\<^sub>R\<^sub>D\<^sub>V x, Cst\<^sub>R\<^sub>D\<^sub>N_Q q1, Cst\<^sub>R\<^sub>D\<^sub>N q2]\<rangle>."
      using solves_lh_lh by metis 
    then show ?thesis
      by (simp add: LTS.get_end_def sq)
  next
    case False
    then have x_is_def: "(x, q1, q2) \<in> def_path (ss @ [s], w) start" using 2(5)
      using not_last_def_transition len by force
    then have "\<rho> \<Turnstile>\<^sub>l\<^sub>h RD\<langle>[Cst\<^sub>R\<^sub>D\<^sub>N (LTS.get_end (ss @ [s], w)), Cst\<^sub>R\<^sub>D\<^sub>V x, Cst\<^sub>R\<^sub>D\<^sub>N_Q q1, Cst\<^sub>R\<^sub>D\<^sub>N q2]\<rangle>."
    proof -
      have "(ss @ [s], w) \<in> LTS.path_with_word es"
        using 2(1) by auto
      moreover
      have "\<rho> \<Turnstile>\<^sub>d\<^sub>l (var_contraints \<union> ana_RD (es, start, end))"
        using 2(6) by auto
      moreover
      have "LTS.get_start (ss @ [s], w) = start"
        using "2.hyps"(1) by auto
      moreover
      have "(x, q1, q2) \<in> def_path (ss @ [s], w) start"
        using x_is_def by auto
      ultimately
      show "\<rho> \<Turnstile>\<^sub>l\<^sub>h RD\<langle>[Cst\<^sub>R\<^sub>D\<^sub>N (LTS.get_end (ss @ [s], w)), Cst\<^sub>R\<^sub>D\<^sub>V x, Cst\<^sub>R\<^sub>D\<^sub>N_Q q1, Cst\<^sub>R\<^sub>D\<^sub>N q2]\<rangle>."
        using 2(3) by auto
    qed
    then have ind: "\<rho> \<Turnstile>\<^sub>l\<^sub>h RD\<langle>[Cst\<^sub>R\<^sub>D\<^sub>N s, Cst\<^sub>R\<^sub>D\<^sub>V x, Cst\<^sub>R\<^sub>D\<^sub>N_Q q1, Cst\<^sub>R\<^sub>D\<^sub>N q2]\<rangle>."
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
        by (meson "2.prems"(3) UnCI solves_program_def)
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
        using xy' by (simp add: prop_inf_last_from_cls_rh_to_cls)
      then have "\<rho> \<Turnstile>\<^sub>c\<^sub>l\<^sub>s RD\<langle>[Cst\<^sub>R\<^sub>D\<^sub>N s', Cst\<^sub>R\<^sub>D\<^sub>V x, Cst\<^sub>R\<^sub>D\<^sub>N_Q q1, Cst\<^sub>R\<^sub>D\<^sub>N q2]\<rangle> :- [] ."
        using ind using prop_inf_last_from_cls_lh_to_cls[of \<rho> the_RD ] by (metis append.left_neutral) 
      then have "\<rho> \<Turnstile>\<^sub>l\<^sub>h RD\<langle>[Cst\<^sub>R\<^sub>D\<^sub>N s', Cst\<^sub>R\<^sub>D\<^sub>V x, Cst\<^sub>R\<^sub>D\<^sub>N_Q q1, Cst\<^sub>R\<^sub>D\<^sub>N q2]\<rangle>."
        using solves_lh_lh by metis
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
        by (meson "2.prems"(3) UnCI solves_program_def)
      moreover have "(RD\<langle>[Cst\<^sub>R\<^sub>D\<^sub>N s', \<u>, \<v>, \<w>]\<rangle> :- [RD[Cst\<^sub>R\<^sub>D\<^sub>N s, \<u>, \<v>, \<w>]].) \<cdot>\<^sub>c\<^sub>l\<^sub>s \<mu> =
                     RD\<langle>[Cst\<^sub>R\<^sub>D\<^sub>N s', Cst\<^sub>R\<^sub>D\<^sub>V x, Cst\<^sub>R\<^sub>D\<^sub>N_Q q1, Cst\<^sub>R\<^sub>D\<^sub>N q2]\<rangle> :- [RD[Cst\<^sub>R\<^sub>D\<^sub>N s, Cst\<^sub>R\<^sub>D\<^sub>V x, Cst\<^sub>R\<^sub>D\<^sub>N_Q q1, Cst\<^sub>R\<^sub>D\<^sub>N q2]]."
        unfolding \<mu>_def by auto
      ultimately have "\<rho> \<Turnstile>\<^sub>c\<^sub>l\<^sub>s RD\<langle>[Cst\<^sub>R\<^sub>D\<^sub>N s', Cst\<^sub>R\<^sub>D\<^sub>V x, Cst\<^sub>R\<^sub>D\<^sub>N_Q q1, Cst\<^sub>R\<^sub>D\<^sub>N q2]\<rangle> 
                               :- [RD [Cst\<^sub>R\<^sub>D\<^sub>N s, Cst\<^sub>R\<^sub>D\<^sub>V x, Cst\<^sub>R\<^sub>D\<^sub>N_Q q1, Cst\<^sub>R\<^sub>D\<^sub>N q2]] ."
        by (metis substitution_lemma)
      then have "\<rho> \<Turnstile>\<^sub>l\<^sub>h RD\<langle>[Cst\<^sub>R\<^sub>D\<^sub>N s', Cst\<^sub>R\<^sub>D\<^sub>V x, Cst\<^sub>R\<^sub>D\<^sub>N_Q q1, Cst\<^sub>R\<^sub>D\<^sub>N q2]\<rangle>."
        using ind
        by (meson prop_inf_only)
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
        by (meson "2.prems"(3) UnCI solves_program_def)
      moreover
      have "(RD\<langle>[Cst\<^sub>R\<^sub>D\<^sub>N s', \<u>, \<v>, \<w>]\<rangle> :- [RD [Cst\<^sub>R\<^sub>D\<^sub>N s, \<u>, \<v>, \<w>]] .) \<cdot>\<^sub>c\<^sub>l\<^sub>s \<mu> =
            RD\<langle>[Cst\<^sub>R\<^sub>D\<^sub>N s', Cst\<^sub>R\<^sub>D\<^sub>V x, Cst\<^sub>R\<^sub>D\<^sub>N_Q q1, Cst\<^sub>R\<^sub>D\<^sub>N q2]\<rangle>  :- [RD [Cst\<^sub>R\<^sub>D\<^sub>N s, Cst\<^sub>R\<^sub>D\<^sub>V x, Cst\<^sub>R\<^sub>D\<^sub>N_Q q1, Cst\<^sub>R\<^sub>D\<^sub>N q2]]."
        unfolding \<mu>_def by auto
      ultimately 
      have "\<rho> \<Turnstile>\<^sub>c\<^sub>l\<^sub>s RD\<langle>[Cst\<^sub>R\<^sub>D\<^sub>N s', Cst\<^sub>R\<^sub>D\<^sub>V x, Cst\<^sub>R\<^sub>D\<^sub>N_Q q1, Cst\<^sub>R\<^sub>D\<^sub>N q2]\<rangle> 
                    :- [RD [Cst\<^sub>R\<^sub>D\<^sub>N s, Cst\<^sub>R\<^sub>D\<^sub>V x, Cst\<^sub>R\<^sub>D\<^sub>N_Q q1, Cst\<^sub>R\<^sub>D\<^sub>N q2]] ."
        by (metis substitution_lemma)
      from modus_ponens_rh[OF this ind] have "\<rho> \<Turnstile>\<^sub>l\<^sub>h RD\<langle>[Cst\<^sub>R\<^sub>D\<^sub>N s', Cst\<^sub>R\<^sub>D\<^sub>V x, Cst\<^sub>R\<^sub>D\<^sub>N_Q q1, Cst\<^sub>R\<^sub>D\<^sub>N q2]\<rangle>."
        .
      then show ?thesis
        by (simp add: LTS.get_end_def)
    qed
  qed
qed

theorem RD_sound:
  assumes "\<rho> \<Turnstile>\<^sub>d\<^sub>l (var_contraints \<union> ana_RD pg)"
  shows "summarizes_RD \<rho> pg"
  using assms RD_sound' by (cases pg) force 


section \<open>Bit-Vector Framework\<close>

datatype pred =
  the_BV
  | the_kill
  | the_gen
  | the_CBV
  | the_init
  | the_anadom

datatype var =
  the_\<uu>

abbreviation "BV == PosLit the_BV"
abbreviation "CBV == PosLit the_CBV"
abbreviation NegLit_BV ("\<^bold>\<not>BV") where
  "\<^bold>\<not>BV \<equiv> NegLit the_BV"
abbreviation "kill == PosLit the_kill"
abbreviation NegLit_kill ("\<^bold>\<not>kill") where
  "\<^bold>\<not>kill \<equiv> NegLit the_kill"
abbreviation "gen == PosLit the_gen"
abbreviation "init == PosLit the_init"
abbreviation "anadom == PosLit the_anadom"

fun s_BV :: "pred \<Rightarrow> nat" where 
  "s_BV the_kill = 0"
| "s_BV the_gen = 0"
| "s_BV the_init = 0"
| "s_BV the_anadom = 0"
| "s_BV the_BV = 1"
| "s_BV the_CBV = 2"

datatype ('n,'v,'d) cst =
  Node (the_node: 'n)
  | is_elem: Elem (the_elem: 'd)
  | Action "'v action"

abbreviation BV_Cls :: "(var, ('n,'v,'d) cst) id list \<Rightarrow> (pred, var, ('n,'v,'d) cst) rh list \<Rightarrow> (pred, var, ('n,'v,'d) cst) clause" ("BV\<langle>_\<rangle> :- _ .") where 
   "BV\<langle>args\<rangle> :- ls. \<equiv> Cls the_BV args ls"

abbreviation CBV_Cls :: "(var, ('n,'v,'d) cst) id list \<Rightarrow> (pred, var, ('n,'v,'d) cst) rh list \<Rightarrow> (pred, var, ('n,'v,'d) cst) clause" ("CBV\<langle>_\<rangle> :- _ .") where
  "CBV\<langle>args\<rangle> :- ls. \<equiv> Cls the_CBV args ls"

abbreviation init_Cls :: "(var, ('n,'v,'d) cst) id list \<Rightarrow> (pred, var, ('n,'v,'d) cst) rh list \<Rightarrow> (pred, var, ('n,'v,'d) cst) clause" ("init\<langle>_\<rangle> :- _ .") where 
  "init\<langle>args\<rangle> :- ls. \<equiv> Cls the_init args ls"

abbreviation anadom_Cls :: "(var, ('n,'v,'d) cst) id list \<Rightarrow> (pred, var, ('n,'v,'d) cst) rh list \<Rightarrow> (pred, var, ('n,'v,'d) cst) clause" ("anadom\<langle>_\<rangle> :- _ .") where 
  "anadom\<langle>args\<rangle> :- ls. \<equiv> Cls the_anadom args ls"

abbreviation kill_Cls :: "(var, ('n,'v,'d) cst) id list \<Rightarrow> (pred, var, ('n,'v,'d) cst) rh list \<Rightarrow> (pred, var, ('n,'v,'d) cst) clause" ("kill\<langle>_\<rangle> :- _ .") where 
  "kill\<langle>args\<rangle> :- ls. \<equiv> Cls the_kill args ls"

abbreviation gen_Cls :: "(var, ('n,'v,'d) cst) id list \<Rightarrow> (pred, var, ('n,'v,'d) cst) rh list \<Rightarrow> (pred, var, ('n,'v,'d) cst) clause" ("gen\<langle>_\<rangle> :- _ .") where 
  "gen\<langle>args\<rangle> :- ls. \<equiv> Cls the_gen args ls"

abbreviation BV_Fact :: "(var, ('n,'v,'d) cst) id list \<Rightarrow> (pred, var, ('n,'v,'d) cst) lh" ("BV\<langle>_\<rangle>.") where  
  "BV\<langle>args\<rangle>. \<equiv> (the_BV, args)"

abbreviation CBV_Fact :: "(var, ('n,'v,'d) cst) id list \<Rightarrow> (pred, var, ('n,'v,'d) cst) lh" ("CBV\<langle>_\<rangle>.") where 
  "CBV\<langle>args\<rangle>. \<equiv> (the_CBV, args)"

abbreviation init_Fact :: "(var, ('n,'v,'d) cst) id list \<Rightarrow> (pred, var, ('n,'v,'d) cst) lh" ("init\<langle>_\<rangle>.") where (* is this needed? *)
  "init\<langle>args\<rangle>. \<equiv> (the_init, args)"

abbreviation dom_Fact :: "(var, ('n,'v,'d) cst) id list \<Rightarrow> (pred, var, ('n,'v,'d) cst) lh" ("anadom\<langle>_\<rangle>.") where (* is this needed? *)
  "anadom\<langle>args\<rangle>. \<equiv> (the_anadom, args)"

abbreviation \<uu> :: "(var, 'a) id" where
  "\<uu> == Var the_\<uu>"

abbreviation Cst\<^sub>N :: "'n \<Rightarrow> (var, ('n, 'v, 'd) cst) id" where
  "Cst\<^sub>N q == Cst (Node q)"

abbreviation Decode_Node :: "(var, ('n, 'v, 'd) cst) id \<Rightarrow> 'n" where
  "Decode_Node ident == the_node (the_Cst ident)"

abbreviation Cst\<^sub>E :: "'d \<Rightarrow> (var, ('n, 'v, 'd) cst) id" where
  "Cst\<^sub>E e == Cst (Elem e)"

abbreviation Decode_Elem :: "(var, ('n, 'v, 'd) cst) id \<Rightarrow> 'd" where
  "Decode_Elem ident == the_elem (the_Cst ident)"

abbreviation Cst\<^sub>A :: "'v action \<Rightarrow> (var, ('n, 'v, 'd) cst) id" where
  "Cst\<^sub>A \<alpha> == Cst (Action \<alpha>)"


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

interpretation lts: LTS edge_set
  .

definition "S_hat" :: "('n,'v) edge \<Rightarrow> 'd set \<Rightarrow> 'd set" ("Ŝ\<^sub>E\<lbrakk>_\<rbrakk> _") where
  "Ŝ\<^sub>E\<lbrakk>e\<rbrakk> R = (R - kill_set e) \<union> gen_set e"

lemma S_hat_mono:
  assumes "d1 \<subseteq> d2"
  shows "Ŝ\<^sub>E\<lbrakk>e\<rbrakk> d1 \<subseteq> Ŝ\<^sub>E\<lbrakk>e\<rbrakk> d2"
  using assms unfolding S_hat_def by auto

fun S_hat_edge_list :: "('n,'v) edge list \<Rightarrow> 'd set \<Rightarrow> 'd set" ("Ŝ\<^sub>E\<^sub>s\<lbrakk>_\<rbrakk> _") where
  "Ŝ\<^sub>E\<^sub>s\<lbrakk>[]\<rbrakk> R = R" |
  "Ŝ\<^sub>E\<^sub>s\<lbrakk>e # \<pi>\<rbrakk> R = Ŝ\<^sub>E\<^sub>s\<lbrakk>\<pi>\<rbrakk> (Ŝ\<^sub>E\<lbrakk>e\<rbrakk> R)"

lemma S_hat_edge_list_def2:
  "Ŝ\<^sub>E\<^sub>s\<lbrakk>\<pi>\<rbrakk> R = foldl (\<lambda>a b. Ŝ\<^sub>E\<lbrakk>b\<rbrakk> a) R \<pi>"
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
  "Ŝ\<^sub>E\<^sub>s\<lbrakk>xs @ ys\<rbrakk> R = Ŝ\<^sub>E\<^sub>s\<lbrakk>ys\<rbrakk> (Ŝ\<^sub>E\<^sub>s\<lbrakk>xs\<rbrakk> R)"
  unfolding S_hat_edge_list_def2 foldl_append by auto

lemma S_hat_edge_list_mono:
  assumes "R1 \<subseteq> R2"
  shows "Ŝ\<^sub>E\<^sub>s\<lbrakk>\<pi>\<rbrakk> R1 \<subseteq> Ŝ\<^sub>E\<^sub>s\<lbrakk>\<pi>\<rbrakk> R2"
proof(induction \<pi> rule: List.rev_induct)
  case Nil
  then show ?case
    using assms by auto
next
  case (snoc x xs)
  then show ?case
    using assms by (simp add: S_hat_mono)
qed

definition S_hat_path :: "('n list \<times> 'v action list) \<Rightarrow> 'd set \<Rightarrow> 'd set" ("Ŝ\<^sub>P\<lbrakk>_\<rbrakk> _") where
  "Ŝ\<^sub>P\<lbrakk>\<pi>\<rbrakk> R = Ŝ\<^sub>E\<^sub>s\<lbrakk>LTS.transition_list \<pi>\<rbrakk> R"

lemma S_hat_path_mono:
  assumes "R1 \<subseteq> R2"
  shows "Ŝ\<^sub>P\<lbrakk>\<pi>\<rbrakk> R1 \<subseteq> Ŝ\<^sub>P\<lbrakk>\<pi>\<rbrakk> R2"
  unfolding S_hat_path_def using assms S_hat_edge_list_mono by auto

fun ana_kill_BV_edge_d :: "('n, 'v) edge \<Rightarrow> 'd \<Rightarrow> (pred, var, ('n, 'v, 'd) cst) clause" where
  "ana_kill_BV_edge_d (q\<^sub>o, \<alpha>, q\<^sub>s) d = kill\<langle>[Cst\<^sub>N q\<^sub>o, Cst\<^sub>A \<alpha>, Cst\<^sub>N q\<^sub>s, Cst\<^sub>E d]\<rangle> :- []."

definition ana_kill_BV_edge :: "('n, 'v) edge \<Rightarrow> (pred, var, ('n, 'v, 'd) cst) clause set" where
  "ana_kill_BV_edge e = ana_kill_BV_edge_d e ` (kill_set e)"

lemma killana: "kill_set e = kill_set e \<inter> analysis_dom"
  by (meson analysis_BV_forward_may_axioms analysis_BV_forward_may_def inf.orderE)

fun ana_gen_BV_edge_d :: "('n, 'v) edge \<Rightarrow> 'd \<Rightarrow> (pred, var, ('n, 'v, 'd) cst) clause" where
  "ana_gen_BV_edge_d (q\<^sub>o, \<alpha>, q\<^sub>s) d = gen\<langle>[Cst\<^sub>N q\<^sub>o, Cst\<^sub>A \<alpha>, Cst\<^sub>N q\<^sub>s, Cst\<^sub>E d]\<rangle> :- []."

definition ana_gen_BV_edge :: "('n, 'v) edge \<Rightarrow> (pred, var, ('n, 'v, 'd) cst) clause set" where
  "ana_gen_BV_edge e = ana_gen_BV_edge_d e ` (gen_set e)"

lemma genana: "gen_set e = gen_set e \<inter> analysis_dom"
  by (meson analysis_BV_forward_may_axioms analysis_BV_forward_may_def inf.orderE)

definition ana_init_BV :: "'d \<Rightarrow> (pred, var, ('n, 'v, 'd) cst) clause" where
  "ana_init_BV d = init\<langle>[Cst\<^sub>E d]\<rangle> :- []."

definition ana_anadom_BV :: "'d \<Rightarrow> (pred, var, ('n, 'v, 'd) cst) clause" where
  "ana_anadom_BV d = anadom\<langle>[Cst\<^sub>E d]\<rangle> :- []."

definition ana_entry_node_BV :: "(pred, var, ('n,'v, 'd) cst) clause" where (* This should be a clause, not clause set. *)
  "ana_entry_node_BV = BV\<langle>[Cst\<^sub>N start,\<uu>]\<rangle> :- [init[\<uu>]]."

fun ana_edge_BV :: "('n, 'v) edge \<Rightarrow> (pred, var, ('n, 'v, 'd) cst) clause set" where
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

definition ana_CBV :: "'n \<Rightarrow> (pred, var, ('n, 'v, 'd) cst) clause" where
  "ana_CBV q = CBV\<langle>[Cst\<^sub>N q,\<uu>]\<rangle> :- [\<^bold>\<not>BV[Cst\<^sub>N q,\<uu>], anadom[\<uu>]]."

lemma ana_CBV_meta_var:
  assumes "\<rho> \<Turnstile>\<^sub>c\<^sub>l\<^sub>s CBV\<langle>[Cst\<^sub>N q,\<uu>]\<rangle> :- [\<^bold>\<not>BV[Cst\<^sub>N q,\<uu>], anadom[\<uu>]]."
  shows "\<rho> \<Turnstile>\<^sub>c\<^sub>l\<^sub>s CBV\<langle>[Cst\<^sub>N q,v]\<rangle> :- [\<^bold>\<not>BV[Cst\<^sub>N q,v], anadom[v]]."
proof -
  define \<mu> where "\<mu> = Var(the_\<uu> := v)"
  have "\<rho> \<Turnstile>\<^sub>c\<^sub>l\<^sub>s ((CBV\<langle>[Cst\<^sub>N q,\<uu>]\<rangle> :- [\<^bold>\<not>BV[Cst\<^sub>N q,\<uu>], anadom[\<uu>]].) \<cdot>\<^sub>c\<^sub>l\<^sub>s \<mu>)"
    using assms substitution_lemma by blast
  then show ?thesis
    unfolding \<mu>_def by auto
qed

definition ana_pg_fw_may :: "(pred, var, ('n, 'v, 'd) cst) clause set" where
  "ana_pg_fw_may = \<Union>(ana_edge_BV ` edge_set)
               \<union> ana_init_BV ` d_init
               \<union> ana_anadom_BV ` analysis_dom
               \<union> \<Union>(ana_kill_BV_edge ` edge_set)
               \<union> \<Union>(ana_gen_BV_edge ` edge_set)
               \<union> ana_CBV ` UNIV
               \<union> {ana_entry_node_BV}"

lemma ana_entry_node_BV_meta_var:
  assumes "\<rho> \<Turnstile>\<^sub>c\<^sub>l\<^sub>s BV\<langle>[Cst\<^sub>N start,\<uu>]\<rangle> :- [init[\<uu>]]."
  shows "\<rho> \<Turnstile>\<^sub>c\<^sub>l\<^sub>s BV\<langle>[Cst\<^sub>N start,u]\<rangle> :- [init[u]]."
proof -
  define \<mu> where "\<mu> = Var(the_\<uu> := u)"
  have "\<rho> \<Turnstile>\<^sub>c\<^sub>l\<^sub>s ((BV\<langle>[Cst\<^sub>N start,\<uu>]\<rangle> :- [init[\<uu>]].) \<cdot>\<^sub>c\<^sub>l\<^sub>s \<mu>)"
    using assms substitution_lemma by blast
  then show ?thesis
    unfolding \<mu>_def by auto
qed

definition summarizes_fw_may :: "(pred, ('n, 'v, 'd) cst) pred_val \<Rightarrow> bool" where
  "summarizes_fw_may \<rho> \<longleftrightarrow> 
     (\<forall>\<pi> d. \<pi> \<in> lts.path_with_word_from start \<longrightarrow> d \<in> Ŝ\<^sub>P\<lbrakk>\<pi>\<rbrakk> d_init \<longrightarrow> 
        \<rho> \<Turnstile>\<^sub>l\<^sub>h (BV\<langle>[Cst\<^sub>N (LTS.get_end \<pi>), Cst\<^sub>E d]\<rangle>.))"

lemma S_hat_path_append:
  assumes "length qs = length w"                               
  shows "Ŝ\<^sub>P\<lbrakk>(qs @ [qnminus1, qn], w @ [\<alpha>])\<rbrakk> d_init =
    Ŝ\<^sub>E\<lbrakk>(qnminus1, \<alpha>, qn)\<rbrakk> (Ŝ\<^sub>P\<lbrakk>(qs @ [qnminus1], w)\<rbrakk> d_init)"
proof -
  have "Ŝ\<^sub>P\<lbrakk> (qs @ [qnminus1, qn], w @ [\<alpha>])\<rbrakk> d_init = Ŝ\<^sub>E\<^sub>s\<lbrakk>(transition_list (qs @ [qnminus1, qn], w @ [\<alpha>]))\<rbrakk> d_init"
    unfolding S_hat_path_def by auto
  moreover
  have "Ŝ\<^sub>E\<^sub>s\<lbrakk>(transition_list (qs @ [qnminus1, qn], w @ [\<alpha>]))\<rbrakk> d_init =
        Ŝ\<^sub>E\<^sub>s\<lbrakk>(transition_list (qs @ [qnminus1], w) @ [(qnminus1, \<alpha>, qn)])\<rbrakk> d_init"
    using transition_list_reversed_simp[of qs w] assms
    by auto
  moreover
  have "... = Ŝ\<^sub>E\<^sub>s\<lbrakk>[(qnminus1, \<alpha>, qn)]\<rbrakk> (S_hat_edge_list (transition_list (qs @ [qnminus1], w)) d_init)"
    using S_hat_edge_list_append[of "transition_list (qs @ [qnminus1], w)" " [(qnminus1, \<alpha>, qn)]" d_init]
    by auto
  moreover
  have "... = Ŝ\<^sub>E\<lbrakk>(qnminus1, \<alpha>, qn)\<rbrakk> (Ŝ\<^sub>P\<lbrakk> (qs @ [qnminus1], w)\<rbrakk> d_init)"
    unfolding S_hat_path_def by auto
  ultimately show ?thesis
    by blast
qed

lemma ana_pg_fw_may_stratified: "strat_wf s_BV ana_pg_fw_may"
  unfolding ana_pg_fw_may_def strat_wf_def ana_init_BV_def ana_anadom_BV_def ana_gen_BV_edge_def 
    ana_CBV_def ana_entry_node_BV_def  ana_kill_BV_edge_def by auto

lemma finite_ana_edge_BV_edgeset: "finite (\<Union> (ana_edge_BV ` edge_set))"
  by (smt (verit, best) analysis_BV_forward_may.ana_edge_BV.elims analysis_BV_forward_may_axioms analysis_BV_forward_may_def edge_set_def finite.emptyI finite.intros(2) finite_UN)

lemma finite_ana_kill_BV_edgeset: "finite (\<Union> (ana_kill_BV_edge ` edge_set))"
  by (metis ana_kill_BV_edge_def analysis_BV_forward_may_axioms analysis_BV_forward_may_def edge_set_def finite_Int finite_UN finite_imageI killana)

lemma finite_ana_gen_BV_edgeset: "finite (\<Union> (ana_gen_BV_edge ` edge_set))"
  by (metis ana_gen_BV_edge_def analysis_BV_forward_may_axioms analysis_BV_forward_may_def edge_set_def finite_UN finite_imageI rev_finite_subset)

lemma finite_ana_anadom_BV_edgeset: "finite (ana_anadom_BV ` analysis_dom)"
  using analysis_BV_forward_may_axioms analysis_BV_forward_may_def by blast

lemma ana_pg_fw_may_finite: "finite ana_pg_fw_may"
  unfolding ana_pg_fw_may_def using finite_ana_edge_BV_edgeset finite_d_init
    finite_ana_anadom_BV_edgeset finite_ana_kill_BV_edgeset finite_ana_gen_BV_edgeset by auto

fun vars_lh :: "('p,'x,'e) lh \<Rightarrow> 'x set" where
  "vars_lh (p,ids) = vars_ids ids"

lemma not_kill:
  fixes \<rho> :: "(pred, ('n, 'v, 'd) cst) pred_val"
  assumes "d \<notin> kill_set(q\<^sub>o, \<alpha>, q\<^sub>s)"
  assumes "\<rho> \<Turnstile>\<^sub>l\<^sub>s\<^sub>t ana_pg_fw_may s_BV"
  shows "\<rho> \<Turnstile>\<^sub>r\<^sub>h \<^bold>\<not>kill[Cst\<^sub>N q\<^sub>o, Cst\<^sub>A \<alpha>, Cst\<^sub>N q\<^sub>s, Cst\<^sub>E d]"
proof -
  have "finite ana_pg_fw_may"
    by (simp add: ana_pg_fw_may_finite)
  moreover
  have "\<rho> \<Turnstile>\<^sub>l\<^sub>s\<^sub>t ana_pg_fw_may s_BV"
    using assms(2) by blast
  moreover
  have "strat_wf s_BV ana_pg_fw_may"
    by (simp add: ana_pg_fw_may_stratified)
  moreover
  have "\<forall>c\<in>ana_pg_fw_may. 
           \<forall>\<sigma>'. 
             (the_lh c \<cdot>\<^sub>v\<^sub>l\<^sub>h \<sigma>') = ((the_kill, [Cst\<^sub>N q\<^sub>o, Cst\<^sub>A \<alpha>, Cst\<^sub>N q\<^sub>s, Cst\<^sub>E d])) 
               \<longrightarrow> \<not> \<lbrakk>the_rhs c\<rbrakk>\<^sub>r\<^sub>h\<^sub>s \<rho> \<sigma>'"
  proof (rule, rule, rule)
    fix c \<sigma>'
    assume c_dl: "c \<in> (ana_pg_fw_may)"
    assume "(the_lh c \<cdot>\<^sub>v\<^sub>l\<^sub>h \<sigma>') = ((the_kill, [Cst\<^sub>N q\<^sub>o, Cst\<^sub>A \<alpha>, Cst\<^sub>N q\<^sub>s, Cst\<^sub>E d]))"
    moreover
    from c_dl have "c \<in> (ana_pg_fw_may)"
      by auto
    ultimately
    show "\<not> \<lbrakk>the_rhs c\<rbrakk>\<^sub>r\<^sub>h\<^sub>s \<rho> \<sigma>'"
      unfolding ana_pg_fw_may_def ana_init_BV_def ana_anadom_BV_def ana_kill_BV_edge_def 
        ana_gen_BV_edge_def ana_CBV_def ana_entry_node_BV_def using assms(1) by fastforce
  qed
  then have "\<not> (\<exists>c\<in>ana_pg_fw_may.
                  lh_consequence \<rho> c (the_kill, [Cst\<^sub>N q\<^sub>o, Cst\<^sub>A \<alpha>, Cst\<^sub>N q\<^sub>s, Cst\<^sub>E d]))"
    using lh_consequence_def by metis
  ultimately
  show "\<rho> \<Turnstile>\<^sub>r\<^sub>h \<^bold>\<not>kill [Cst\<^sub>N q\<^sub>o, Cst\<^sub>A \<alpha>, Cst\<^sub>N q\<^sub>s, Cst\<^sub>E d]"
    using solves_NegLit_least[of ana_pg_fw_may \<rho> s_BV "[Cst\<^sub>N q\<^sub>o, Cst\<^sub>A \<alpha>, Cst\<^sub>N q\<^sub>s, Cst\<^sub>E d]" the_kill] by auto
qed

lemma the_funny_invariant':
  "d \<in> Ŝ\<^sub>E\<^sub>s\<lbrakk>\<pi>\<rbrakk> d_init \<Longrightarrow> d \<in> analysis_dom"
proof(induction \<pi> rule: List.rev_induct)
  case Nil
  then show ?case
    by (metis S_hat_edge_list.simps(1) analysis_BV_forward_may_axioms analysis_BV_forward_may_def subsetD)
next
  case (snoc e \<pi>)
  have "gen_set e \<inter> analysis_dom \<subseteq> analysis_dom"
    by fastforce
  then show ?case
    using S_hat_def genana snoc by auto
qed

lemma the_funny_invariant:
  "d \<in> Ŝ\<^sub>P\<lbrakk>(ss,w)\<rbrakk> d_init \<Longrightarrow> d \<in> analysis_dom"
  using S_hat_path_def the_funny_invariant' by auto

lemma S_hat_path_last:
  assumes "length qs = length w"
  shows "Ŝ\<^sub>P\<lbrakk>(qs @ [qnminus1, qn], w @ [\<alpha>])\<rbrakk> d_init = Ŝ\<^sub>E\<lbrakk>(qnminus1, \<alpha>, qn)\<rbrakk> (Ŝ\<^sub>P\<lbrakk>(qs @ [qnminus1], w)\<rbrakk> d_init)"
  using assms transition_list_reversed_simp unfolding S_hat_path_def by force

lemma gen_sound:
  assumes "d \<in> gen_set (q, \<alpha>, q')"
  assumes "(q, \<alpha>, q') \<in> edge_set"
  assumes "\<rho> \<Turnstile>\<^sub>l\<^sub>s\<^sub>t ana_pg_fw_may s_BV"
  shows "\<rho> \<Turnstile>\<^sub>c\<^sub>l\<^sub>s gen\<langle>[Cst\<^sub>N q, Cst\<^sub>A \<alpha>, Cst\<^sub>N q', Cst\<^sub>E d]\<rangle> :- [] ."
proof -
  have "gen\<langle>[Cst\<^sub>N q, Cst\<^sub>A \<alpha>, Cst\<^sub>N q', Cst\<^sub>E d]\<rangle> :- [] . \<in> ana_pg_fw_may"
    using assms(1,2) unfolding ana_pg_fw_may_def ana_gen_BV_edge_def by fastforce
  then show "?thesis"
    using \<open>gen\<langle>[Cst\<^sub>N q, Cst\<^sub>A \<alpha>, Cst\<^sub>N q', Cst\<^sub>E d]\<rangle> :- [] . \<in> ana_pg_fw_may\<close> assms(3) 
      least_solution_def solves_program_def by blast
qed

lemma sound_ana_pg_fw_may':
  assumes "(ss,w) \<in> lts.path_with_word_from start"
  assumes "d \<in> Ŝ\<^sub>P\<lbrakk>(ss,w)\<rbrakk> d_init"
  assumes "\<rho> \<Turnstile>\<^sub>l\<^sub>s\<^sub>t ana_pg_fw_may s_BV"
  shows "\<rho> \<Turnstile>\<^sub>l\<^sub>h BV\<langle>[Cst\<^sub>N (LTS.get_end (ss, w)), Cst\<^sub>E d]\<rangle>."
  using assms 
proof (induction rule: LTS.path_with_word_from_induct_reverse[OF assms(1)])
  case (1 s)
  have assms_2: "\<rho> \<Turnstile>\<^sub>d\<^sub>l ana_pg_fw_may"
    using assms(3) unfolding least_solution_def by auto

  from 1(1) have start_end: "LTS.get_end ([s], []) = start"
    by (simp add: LTS.get_end_def LTS.get_start_def)

  from 1 have "Ŝ\<^sub>P\<lbrakk>([s], [])\<rbrakk> d_init = d_init"
    unfolding S_hat_path_def by auto
  then have "d \<in> d_init"
    using 1(2) by auto
  then have "\<rho> \<Turnstile>\<^sub>c\<^sub>l\<^sub>s init\<langle>[Cst\<^sub>E d]\<rangle> :- [] ."
    using assms_2 unfolding ana_pg_fw_may_def ana_init_BV_def solves_program_def by auto
  moreover
  have "\<rho> \<Turnstile>\<^sub>c\<^sub>l\<^sub>s BV\<langle>[Cst\<^sub>N start, \<uu>]\<rangle> :- [init[\<uu>]]."
    by (metis Un_insert_right ana_entry_node_BV_def analysis_BV_forward_may.ana_pg_fw_may_def 
        analysis_BV_forward_may_axioms assms_2 insertI1 solves_program_def)
  then have "\<rho> \<Turnstile>\<^sub>c\<^sub>l\<^sub>s BV\<langle>[Cst\<^sub>N start, Cst\<^sub>E d]\<rangle> :- [init[Cst\<^sub>E d]]."
    using ana_entry_node_BV_meta_var by blast
  ultimately have "\<rho> \<Turnstile>\<^sub>c\<^sub>l\<^sub>s BV\<langle>[Cst\<^sub>N start, Cst\<^sub>E d]\<rangle> :- [] ."
    using prop_inf_only_from_cls_cls_to_cls by metis
  then show ?case
    using start_end solves_lh_lh by metis
next
  case (2 qs qnminus1 w \<alpha> qn)
  then have len: "length qs = length w"
    using lts.path_with_word_lengths by blast
  
  have "d \<in> Ŝ\<^sub>E\<lbrakk>(qnminus1, \<alpha>, qn)\<rbrakk> (Ŝ\<^sub>P\<lbrakk>(qs @ [qnminus1], w)\<rbrakk> d_init)"
    using "2.prems"(2) S_hat_path_last len by blast
  then have "d \<in> (Ŝ\<^sub>P\<lbrakk>(qs @ [qnminus1], w)\<rbrakk> d_init) - kill_set (qnminus1, \<alpha>, qn) \<or> d \<in> gen_set (qnminus1, \<alpha>, qn)"
    unfolding S_hat_def by simp
  then show ?case
  proof 
    assume dSnotkill: "d \<in> (Ŝ\<^sub>P\<lbrakk>(qs @ [qnminus1], w)\<rbrakk> d_init) - kill_set (qnminus1, \<alpha>, qn)"
    then have "\<rho> \<Turnstile>\<^sub>l\<^sub>h BV\<langle>[Cst\<^sub>N qnminus1, Cst\<^sub>E d]\<rangle>."
      using 2(1,3,6) by (auto simp add: LTS.get_end_def)
    moreover
    from dSnotkill have "\<rho> \<Turnstile>\<^sub>r\<^sub>h \<^bold>\<not>kill [Cst\<^sub>N qnminus1, Cst\<^sub>A \<alpha>, Cst\<^sub>N qn, Cst\<^sub>E d]"
      using not_kill[of d qnminus1 \<alpha> qn \<rho>] 2(6) by auto
    moreover
    have "\<rho> \<Turnstile>\<^sub>c\<^sub>l\<^sub>s BV\<langle>[Cst\<^sub>N qn, \<uu>]\<rangle> :- [BV [Cst\<^sub>N qnminus1, \<uu>], \<^bold>\<not>kill [Cst\<^sub>N qnminus1, Cst\<^sub>A \<alpha>, Cst\<^sub>N qn, \<uu>]] ."
      using 2(6) "2.hyps"(2) by (force simp add: ana_pg_fw_may_def solves_program_def least_solution_def)
    then have "\<rho> \<Turnstile>\<^sub>c\<^sub>l\<^sub>s BV\<langle>[Cst\<^sub>N qn, Cst\<^sub>E d]\<rangle> :- [BV [Cst\<^sub>N qnminus1, Cst\<^sub>E d], \<^bold>\<not>kill [Cst\<^sub>N qnminus1, Cst\<^sub>A \<alpha>, Cst\<^sub>N qn, Cst\<^sub>E d]]."
      using substitution_lemma[of \<rho> _ "\<lambda>u. Cst\<^sub>E d"] by force
    ultimately 
    have "\<rho> \<Turnstile>\<^sub>l\<^sub>h BV\<langle>[Cst\<^sub>N qn, Cst\<^sub>E d]\<rangle>."
      by (metis (no_types, lifting) Cons_eq_appendI prop_inf_last_from_cls_rh_to_cls modus_ponens_rh self_append_conv2)
    then show "?case"
      by (auto simp add: LTS.get_end_def)
  next
    assume d_gen: "d \<in> gen_set (qnminus1, \<alpha>, qn)"

    have "\<forall>c\<in>ana_edge_BV (qnminus1, \<alpha>, qn). \<rho> \<Turnstile>\<^sub>c\<^sub>l\<^sub>s c"
      using 2(6) "2.hyps"(2) unfolding ana_pg_fw_may_def solves_program_def least_solution_def by blast
    then have "\<rho> \<Turnstile>\<^sub>c\<^sub>l\<^sub>s BV\<langle>[Cst\<^sub>N qn, \<uu>]\<rangle> :- [gen [Cst\<^sub>N qnminus1, Cst\<^sub>A \<alpha>, Cst\<^sub>N qn, \<uu>]] ."
      by auto
    then have "\<rho> \<Turnstile>\<^sub>c\<^sub>l\<^sub>s BV\<langle>[Cst\<^sub>N qn, Cst\<^sub>E d]\<rangle> :- [gen [Cst\<^sub>N qnminus1, Cst\<^sub>A \<alpha>, Cst\<^sub>N qn, Cst\<^sub>E d]] ."
      using substitution_lemma[of \<rho> _ "\<lambda>u. Cst\<^sub>E d" ]
      by force
    moreover
    have "\<rho> \<Turnstile>\<^sub>c\<^sub>l\<^sub>s gen\<langle>[Cst\<^sub>N qnminus1, Cst\<^sub>A \<alpha>, Cst\<^sub>N qn, Cst\<^sub>E d]\<rangle> :- [] ."
      using d_gen "2.hyps"(2) 2(6) gen_sound by auto
    ultimately
    have "\<rho> \<Turnstile>\<^sub>l\<^sub>h BV\<langle>[Cst\<^sub>N qn, Cst\<^sub>E d]\<rangle>."
      by (meson modus_ponens_rh solves_lh_lh)
    then show ?case
      by (auto simp add: LTS.get_end_def)
  qed
qed

theorem sound_ana_pg_fw_may:
  assumes "\<rho> \<Turnstile>\<^sub>l\<^sub>s\<^sub>t ana_pg_fw_may s_BV"
  shows "summarizes_fw_may \<rho>"
  using sound_ana_pg_fw_may' assms unfolding summarizes_fw_may_def by (cases pg) fastforce

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

definition analysis_dom_RD :: "('n,'v) def set" where
  "analysis_dom_RD = UNIV \<times> UNIV \<times> UNIV"

fun kill_set_RD :: "('n,'v) edge \<Rightarrow> ('n,'v) def set" where
  "kill_set_RD (q\<^sub>o, x ::= a, q\<^sub>s) = {x} \<times> UNIV \<times> UNIV"
| "kill_set_RD (q\<^sub>o, Bool b, q\<^sub>s) = {}"
| "kill_set_RD (v, Skip, vc) = {}"

fun gen_set_RD :: "('n,'v) edge \<Rightarrow> ('n,'v) def set" where
  "gen_set_RD (q\<^sub>o, x ::= a, q\<^sub>s) = {x} \<times> {Some q\<^sub>o} \<times> {q\<^sub>s}"
| "gen_set_RD (q\<^sub>o, Bool b, q\<^sub>s) = {}"
| "gen_set_RD (v, Skip, vc) = {} "

definition d_init_RD :: " ('n,'v) def set" where
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

interpretation fw_may: analysis_BV_forward_may pg analysis_dom_RD kill_set_RD gen_set_RD d_init_RD 
  using analysis_BV_forward_may_def analysis_RD_axioms analysis_RD_def
  using d_init_RD_subset_analysis_dom_RD finite_analysis_dom_RD gen_RD_subset_analysis_dom kill_RD_subset_analysis_dom
  by blast 

lemma def_var_def_edge_S_hat:
  assumes "def_var \<pi> x start \<in> R"
  assumes "x \<notin> def_edge t"
  shows "def_var \<pi> x start \<in> fw_may.S_hat t R"
proof -
  define q1 where "q1 = fst t"
  define \<alpha> where "\<alpha> = fst (snd t)"
  define q2 where "q2 = snd (snd t)"
  have t_def: "t = (q1, \<alpha>, q2)"
    by (simp add: \<alpha>_def q1_def q2_def)

  from assms(2) have assms_2: "x \<notin> def_edge (q1, \<alpha>, q2)"
    unfolding t_def by auto

  have "def_var \<pi> x start \<in> fw_may.S_hat (q1, \<alpha>, q2) R"
  proof (cases \<alpha>)
    case (Asg y exp)
    then show ?thesis
      by (metis (no_types, lifting) DiffI Un_iff assms(1) assms_2 def_action.simps(1) def_var_x fw_may.S_hat_def kill_set_RD.simps(1) mem_Sigma_iff old.prod.case prod.collapse)
  next
    case (Bool b)
    then show ?thesis
      by (simp add: fw_may.S_hat_def assms(1))
  next
    case Skip
    then show ?thesis
      by (simp add: fw_may.S_hat_def assms(1))
  qed
  then show ?thesis
    unfolding t_def by auto
qed

lemma def_var_S_hat_edge_list: "(def_var \<pi>) x start \<in> fw_may.S_hat_edge_list \<pi> d_init_RD"
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
    have "fw_may.S_hat_edge_list (\<pi> @ [t]) d_init_RD = fw_may.S_hat t (fw_may.S_hat_edge_list \<pi> d_init_RD)"
      unfolding fw_may.S_hat_edge_list_def2 by simp
    moreover
    obtain q1 \<alpha> q2 where t_split: "t = (q1, \<alpha>, q2)"
      using prod_cases3 by blast
    moreover
    have "def_var [t] x start \<in> fw_may.S_hat t (fw_may.S_hat_edge_list \<pi> d_init_RD)"
      unfolding fw_may.S_hat_def def_var_def def_of_def using True t_split by (cases \<alpha>) auto
    ultimately
    show ?thesis by auto
  next
    case False
    obtain q1 \<alpha> q2 where t_split: "t = (q1, \<alpha>, q2)"
      using prod_cases3 by blast
    from False have "def_var (\<pi> @ [t]) x start = def_var \<pi> x start"
      by (simp add: def_var_def)
    moreover
    from snoc.IH have "def_var \<pi> x start \<in> fw_may.S_hat t (fw_may.S_hat_edge_list \<pi> d_init_RD)"
      by (simp add: False def_var_def_edge_S_hat)
    then have "def_var \<pi> x start \<in> fw_may.S_hat_edge_list (\<pi> @ [t]) d_init_RD"
      unfolding fw_may.S_hat_edge_list_def2 by simp
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
  have "def_var (\<pi> @ [(q1, x ::= exp, q2)]) x start = def_of x (last (filter (\<lambda>e. x \<in> def_edge e) (\<pi> @ [(q1, x ::= exp, q2)])))"
    unfolding def_var_def by auto
  also
  have "... = def_of x (q1, x ::= exp, q2)"
    by auto
  also
  have "... = (x, Some q1, q2)"
    unfolding def_of_def by auto
  finally
  show ?thesis
    .
qed

lemma S_hat_edge_list_last: "fw_may.S_hat_edge_list (\<pi> @ [e]) d_init_RD = fw_may.S_hat e (fw_may.S_hat_edge_list \<pi> d_init_RD)"
  using fw_may.S_hat_edge_list_def2 foldl_conv_foldr by simp

lemma def_var_if_S_hat: "(x,q1,q2) \<in> fw_may.S_hat_edge_list \<pi> d_init_RD \<Longrightarrow> (x,q1,q2) = (def_var \<pi>) x start"
proof (induction \<pi> rule: rev_induct)
  case Nil
  then show ?case
    by (metis append_is_Nil_conv d_init_RD_def def_var_def in_set_conv_decomp fw_may.S_hat_edge_list.simps(1) list.distinct(1) mem_Sigma_iff singletonD)
next
  case (snoc e \<pi>)

  from snoc(2) have "(x, q1, q2) \<in> fw_may.S_hat e (fw_may.S_hat_edge_list \<pi> d_init_RD)"
    using S_hat_edge_list_last by blast     

  then have "(x, q1, q2) \<in> fw_may.S_hat_edge_list \<pi> d_init_RD - kill_set_RD e \<or> (x, q1, q2) \<in> gen_set_RD e"
    unfolding fw_may.S_hat_def by auto
  then show ?case
  proof
    assume a: "(x, q1, q2) \<in> fw_may.S_hat_edge_list \<pi> d_init_RD - kill_set_RD e"
    then have "(x, q1, q2) = def_var \<pi> x start"
      using snoc by auto
    moreover
    from a have "(x, q1, q2) \<notin> kill_set_RD e"
      by auto
    then have "def_var (\<pi> @ [e]) x start = def_var \<pi> x start"
    proof -
      assume a: "(x, q1, q2) \<notin> kill_set_RD e"
      obtain q q' \<alpha> where "e = (q, \<alpha>, q')"
        by (cases e) auto
      then have "x \<notin> def_edge e"
        using a by (cases \<alpha>) auto
      then show ?thesis
        by (simp add: def_var_def)
    qed
    ultimately
    show ?case
      by auto
  next
    assume a: "(x, q1, q2) \<in> gen_set_RD e"
    obtain q q' \<alpha> where "e = (q, \<alpha>, q')"
      by (cases e) auto
    then have "\<exists>exp theq1. e = (theq1, x ::= exp, q2) \<and> q1 = Some theq1"
      using a by (cases \<alpha>) auto
    then obtain exp theq1 where exp_theq1_p: "e = (theq1, x ::= exp, q2) \<and> q1 = Some theq1"
      by auto
    then have "(x, q1, q2) = def_var (\<pi> @ [(theq1, x ::= exp, q2)]) x start"
      using last_overwrites[of \<pi> theq1 x exp q2] by auto
    then show ?case
      using exp_theq1_p by auto
  qed
qed

lemma def_var_UNIV_S_hat_edge_list: "(\<lambda>x. def_var \<pi> x start) ` UNIV = fw_may.S_hat_edge_list \<pi> d_init_RD"
proof (rule; rule)
  fix x
  assume "x \<in> range (\<lambda>x. def_var \<pi> x start)"
  then show "x \<in> fw_may.S_hat_edge_list \<pi> d_init_RD"
    using def_var_S_hat_edge_list by blast
next
  fix x
  assume "x \<in> fw_may.S_hat_edge_list \<pi> d_init_RD"
  then show "x \<in> range (\<lambda>x. def_var \<pi> x start)"
    by (metis def_var_if_S_hat prod.collapse range_eqI)
qed

lemma def_path_S_hat_path: "def_path \<pi> start = fw_may.S_hat_path \<pi> d_init_RD"
  using fw_may.S_hat_path_def def_path_def def_var_UNIV_S_hat_edge_list by metis

definition summarizes_RD :: "(pred, ('n,'v,('n,'v) def) cst) pred_val \<Rightarrow> bool" where
  "summarizes_RD \<rho> \<longleftrightarrow> (\<forall>\<pi> d. \<pi> \<in> LTS.path_with_word edge_set \<longrightarrow> LTS.get_start \<pi> = start \<longrightarrow> d \<in> def_path \<pi> start \<longrightarrow> 
                        \<rho> \<Turnstile>\<^sub>l\<^sub>h BV\<langle>[Cst\<^sub>N (LTS.get_end \<pi>), Cst\<^sub>E d]\<rangle>.)"

theorem RD_sound_again: 
  assumes "\<rho> \<Turnstile>\<^sub>l\<^sub>s\<^sub>t fw_may.ana_pg_fw_may s_BV"
  shows "summarizes_RD \<rho>"
  using assms def_path_S_hat_path fw_may.sound_ana_pg_fw_may unfolding fw_may.summarizes_fw_may_def summarizes_RD.simps
  using edge_set_def in_mono fw_may.edge_set_def fw_may.start_def start_def summarizes_RD_def by fastforce 

end


section \<open>Backward may-analysis\<close>

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

definition S_hat :: "('n,'v) edge \<Rightarrow> 'd set \<Rightarrow> 'd set" ("Ŝ\<^sub>E\<lbrakk>_\<rbrakk> _") where
  "Ŝ\<^sub>E\<lbrakk>e\<rbrakk> R = (R - kill_set e) \<union> gen_set e"

lemma S_hat_mono:
  assumes "R1 \<subseteq> R2"
  shows "Ŝ\<^sub>E\<lbrakk>e\<rbrakk> R1 \<subseteq> Ŝ\<^sub>E\<lbrakk>e\<rbrakk> R2"
  using assms unfolding S_hat_def by auto

fun S_hat_edge_list :: "('n,'v) edge list \<Rightarrow> 'd set \<Rightarrow> 'd set" ("Ŝ\<^sub>E\<^sub>s\<lbrakk>_\<rbrakk> _") where
  "Ŝ\<^sub>E\<^sub>s\<lbrakk>[]\<rbrakk> R = R" |
  "Ŝ\<^sub>E\<^sub>s\<lbrakk>(e # \<pi>)\<rbrakk> R = Ŝ\<^sub>E\<lbrakk>e\<rbrakk> (Ŝ\<^sub>E\<^sub>s\<lbrakk>\<pi>\<rbrakk> R)"

lemma S_hat_edge_list_def2:
  "Ŝ\<^sub>E\<^sub>s\<lbrakk>\<pi>\<rbrakk> R = foldr S_hat \<pi> R"
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
  "Ŝ\<^sub>E\<^sub>s\<lbrakk>(xs @ ys)\<rbrakk> R = Ŝ\<^sub>E\<^sub>s\<lbrakk>xs\<rbrakk> (Ŝ\<^sub>E\<^sub>s\<lbrakk>ys\<rbrakk> R)"
  unfolding S_hat_edge_list_def2 foldl_append by auto

lemma S_hat_edge_list_mono:
  assumes "d1 \<subseteq> d2"
  shows "Ŝ\<^sub>E\<^sub>s\<lbrakk>\<pi>\<rbrakk> d1 \<subseteq> Ŝ\<^sub>E\<^sub>s\<lbrakk>\<pi>\<rbrakk> d2"
proof(induction \<pi>)
  case Nil
  then show ?case
    using assms by auto
next
  case (Cons x xs)
  then show ?case
    using assms by (simp add: S_hat_mono)
qed

definition S_hat_path :: "('n list \<times> 'v action list) \<Rightarrow> 'd set \<Rightarrow> 'd set" ("Ŝ\<^sub>P\<lbrakk>_\<rbrakk> _") where
  "Ŝ\<^sub>P\<lbrakk>\<pi>\<rbrakk> R = Ŝ\<^sub>E\<^sub>s\<lbrakk>(LTS.transition_list \<pi>)\<rbrakk> R"

definition summarizes_bw_may :: "(pred, ('n, 'v, 'd) cst) pred_val \<Rightarrow> bool" where
  "summarizes_bw_may \<rho> \<longleftrightarrow> (\<forall>\<pi> d. \<pi> \<in> LTS.path_with_word edge_set \<longrightarrow> LTS.get_end \<pi> = end \<longrightarrow> d \<in> Ŝ\<^sub>P\<lbrakk>\<pi>\<rbrakk> d_init \<longrightarrow> 
                             \<rho> \<Turnstile>\<^sub>l\<^sub>h BV\<langle>[Cst\<^sub>N (LTS.get_start \<pi>), Cst\<^sub>E d]\<rangle>.)"

lemma finite_pg_rev: "finite (fst pg_rev)"
  by (metis analysis_BV_backward_may_axioms analysis_BV_backward_may_def edge_set_def finite_imageI fst_conv pg_rev_def)

lemma new_gen_subs_analysis_dom: "(kill_set (rev_edge e)) \<subseteq> analysis_dom"
  by (meson analysis_BV_backward_may_axioms analysis_BV_backward_may_def)

lemma new_kill_subs_analysis_dom: "(gen_set (rev_edge e)) \<subseteq> analysis_dom"
  by (meson analysis_BV_backward_may_axioms analysis_BV_backward_may_def)

interpretation fw_may: analysis_BV_forward_may pg_rev analysis_dom "\<lambda>e. (kill_set (rev_edge e))" "(\<lambda>e. gen_set (rev_edge e))" d_init
  using analysis_BV_forward_may_def finite_pg_rev by (metis analysis_BV_backward_may_axioms analysis_BV_backward_may_def) 

abbreviation ana_pg_bw_may where
  "ana_pg_bw_may == fw_may.ana_pg_fw_may"

lemma rev_end_is_start:
  assumes "ss \<noteq> []"
  assumes "LTS.get_end (ss, w) = end"
  shows "LTS.get_start (rev ss, rev w) = fw_may.start"
  using assms
  unfolding LTS.get_end_def LTS.get_start_def fw_may.start_def pg_rev_def fw_may.start_def
  using hd_rev by (metis fw_may.start_def fst_conv pg_rev_def snd_conv) 

(*  "Ŝ\<^sub>E\<^sub>s\<lbrakk>ss\<rbrakk> d_init = Ŝ\<^sub>E\<^sub>s\<^sub>F\<^sub>W \<lbrakk>rev_edge_list ss\<rbrakk> d_init" *)

lemma S_hat_edge_list_forward_backward:
  "Ŝ\<^sub>E\<^sub>s\<lbrakk>ss\<rbrakk> d_init = fw_may.S_hat_edge_list (rev_edge_list ss) d_init"
proof (induction ss)
  case Nil
  then show ?case
    unfolding rev_edge_list_def by auto
next
  case (Cons e es)
  have "Ŝ\<^sub>E\<^sub>s\<lbrakk>e # es\<rbrakk> d_init = Ŝ\<^sub>E\<lbrakk>e\<rbrakk> Ŝ\<^sub>E\<^sub>s\<lbrakk>es\<rbrakk> d_init"
    by simp
  also 
  have "... = fw_may.S_hat (rev_edge e) (foldr fw_may.S_hat (map rev_edge es) d_init)"
    unfolding foldr_conv_foldl fw_may.S_hat_edge_list_def2[symmetric]
    unfolding rev_edge_list_def[symmetric] fw_may.S_hat_def S_hat_def
    using Cons by simp
  also
  have "... = fw_may.S_hat_edge_list (rev_edge_list (e # es)) d_init"
    unfolding rev_edge_list_def fw_may.S_hat_edge_list_def2 foldl_conv_foldr
    by simp
  finally
  show ?case
    by metis
qed

lemma S_hat_path_forward_backward:
  assumes "(ss,w) \<in> LTS.path_with_word edge_set"
  shows "Ŝ\<^sub>P\<lbrakk>(ss, w)\<rbrakk> d_init = fw_may.S_hat_path (rev ss, rev w) d_init"
  using S_hat_edge_list_forward_backward unfolding S_hat_path_def fw_may.S_hat_path_def
  by (metis transition_list_rev_edge_list assms)

lemma summarizes_bw_may_forward_backward':
  assumes "(ss,w) \<in> LTS.path_with_word edge_set"
  assumes "LTS.get_end (ss,w) = end"
  assumes "d \<in> Ŝ\<^sub>P\<lbrakk>(ss,w)\<rbrakk> d_init"
  assumes "fw_may.summarizes_fw_may \<rho>"
  shows "\<rho> \<Turnstile>\<^sub>l\<^sub>h BV\<langle>[Cst\<^sub>N (LTS.get_start (ss, w)), Cst\<^sub>E d]\<rangle>."
proof -
  have rev_in_edge_set: "(rev ss, rev w) \<in> LTS.path_with_word fw_may.edge_set"
    using assms(1) rev_path_in_rev_pg[of ss w] fw_may.edge_set_def pg_rev_def by auto 
  moreover
  have "LTS.get_start (rev ss, rev w) = fw_may.start"
    using assms(1,2) rev_end_is_start by (metis LTS.path_with_word_not_empty)
  moreover
  have "d \<in> fw_may.S_hat_path (rev ss, rev w) d_init"
    using assms(3)
    using assms(1) S_hat_path_forward_backward by auto
  ultimately
  have "\<rho> \<Turnstile>\<^sub>l\<^sub>h BV\<langle>[Cst\<^sub>N (LTS.get_end (rev ss, rev w)), Cst\<^sub>E d]\<rangle>."
    using assms(4) fw_may.summarizes_fw_may_def by blast
  then show ?thesis
    by (metis LTS.get_end_def LTS.get_start_def fst_conv hd_rev rev_rev_ident)
qed

lemma summarizes_dl_BV_forward_backward:
  assumes "fw_may.summarizes_fw_may \<rho>"
  shows "summarizes_bw_may \<rho>"
  unfolding summarizes_bw_may_def
proof(rule; rule ; rule ;rule ;rule)
  fix \<pi> d
  assume "\<pi> \<in> LTS.path_with_word edge_set"
  moreover
  assume "LTS.get_end \<pi> = end"
  moreover
  assume "d \<in> Ŝ\<^sub>P\<lbrakk>\<pi>\<rbrakk> d_init"
  ultimately
  show "\<rho> \<Turnstile>\<^sub>l\<^sub>h BV\<langle>[Cst\<^sub>N (LTS.get_start \<pi>), Cst\<^sub>E d]\<rangle>."
    using summarizes_bw_may_forward_backward'[of "fst \<pi>" "snd \<pi>" d \<rho>] using assms by auto
qed

theorem sound_ana_pg_bw_may:
  assumes "\<rho> \<Turnstile>\<^sub>l\<^sub>s\<^sub>t ana_pg_bw_may s_BV"
  shows "summarizes_bw_may \<rho>"
  using assms fw_may.sound_ana_pg_fw_may[of \<rho>] summarizes_dl_BV_forward_backward by metis

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

interpretation bw_may: analysis_BV_backward_may pg analysis_dom_LV kill_set_LV gen_set_LV d_init_LV
  using analysis_BV_backward_may.intro analysis_LV_axioms analysis_LV_def
  by (metis (mono_tags) analysis_dom_LV_def finite_UNIV subset_UNIV)

lemma use_edge_list_S_hat_edge_list: 
  assumes "use_edge_list \<pi> x"
  shows "x \<in> bw_may.S_hat_edge_list \<pi> d_init_LV"
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
      using x_used_a bw_may.S_hat_def a_split by (cases \<alpha>) auto
  next
    case (Cons hd_\<pi>1 tl_\<pi>1)
    obtain p \<alpha> q where e_split: "e' = (p, \<alpha>, q)"
      by (cases e')
    have "(\<pi> = tl_\<pi>1 @ (p, \<alpha>, q) # \<pi>2) \<and> x \<in> use_action \<alpha> \<and> (\<forall>e'\<in>set tl_\<pi>1. x \<notin> def_edge e')"
      using Cons \<pi>1_\<pi>2_e'_p e_split by auto
    then have "use_edge_list \<pi> x"
      unfolding use_edge_list_def by force
    then have x_in_S_hat_\<pi>: "x \<in> bw_may.S_hat_edge_list \<pi> d_init_LV"
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
        by (simp add: bw_may.S_hat_def x_in_S_hat_\<pi>)
    qed
  qed
qed

lemma S_hat_edge_list_use_edge_list:
  assumes "x \<in> bw_may.S_hat_edge_list \<pi> d_init_LV"
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
  from Cons(2) have "x \<in> bw_may.S_hat_edge_list \<pi> d_init_LV - kill_set_LV e \<union> gen_set_LV e"
    unfolding bw_may.S_hat_edge_list.simps unfolding bw_may.S_hat_def by auto
  then show ?case
  proof
    assume a: "x \<in> bw_may.S_hat_edge_list \<pi> d_init_LV - kill_set_LV e"
    then have "x \<in> bw_may.S_hat_edge_list \<pi> d_init_LV"
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

lemma use_edge_list_UNIV_S_hat_edge_list: "{x. use_edge_list \<pi> x} = bw_may.S_hat_edge_list \<pi> d_init_LV"
  using use_edge_list_S_hat_edge_list S_hat_edge_list_use_edge_list by auto

lemma use_path_S_hat_path: "use_path \<pi> = bw_may.S_hat_path \<pi> d_init_LV"
  by (simp add: use_edge_list_UNIV_S_hat_edge_list bw_may.S_hat_path_def use_path_def)

definition summarizes_LV :: "(pred, ('n,'v,'v) cst) pred_val \<Rightarrow> bool" where
  "summarizes_LV \<rho> \<longleftrightarrow> (\<forall>\<pi> d. \<pi> \<in> LTS.path_with_word edge_set \<longrightarrow> LTS.get_end \<pi> = end \<longrightarrow> d \<in> use_path \<pi> \<longrightarrow> 
                         \<rho> \<Turnstile>\<^sub>l\<^sub>h BV\<langle>[Cst\<^sub>N (LTS.get_start \<pi>), Cst\<^sub>E d]\<rangle>.)"

theorem LV_sound:
  assumes "\<rho> \<Turnstile>\<^sub>l\<^sub>s\<^sub>t bw_may.ana_pg_bw_may s_BV"
  shows "summarizes_LV \<rho>"
proof -
  from assms have "bw_may.summarizes_bw_may \<rho>"
    using bw_may.sound_ana_pg_bw_may[of \<rho>] by auto
  then show ?thesis
    unfolding summarizes_LV_def bw_may.summarizes_bw_may_def bw_may.edge_set_def edge_set_def
      bw_may.end_def end_def use_path_S_hat_path by blast
qed

end


section \<open>Reachable Nodes\<close>

fun nodes_on_edge :: "('n,'v) edge \<Rightarrow> 'n set" where
  "nodes_on_edge (q1, \<alpha>, q2) = {q1, q2}"

definition node_on_edge_list :: "('n,'v) edge list \<Rightarrow> 'n \<Rightarrow> bool" where
  "node_on_edge_list \<pi> q = (\<exists>\<pi>1 \<pi>2 e. \<pi> = \<pi>1 @ [e] @ \<pi>2 \<and> q \<in> nodes_on_edge e)"

definition nodes_on_path :: "'n list \<times> 'v action list \<Rightarrow> 'n set" where
  "nodes_on_path \<pi> = {q. node_on_edge_list (LTS.transition_list \<pi>) q}"

locale analysis_RN =
  fixes pg :: "('n::finite,'v::finite) program_graph"
  assumes "finite (fst pg)"
begin

definition edge_set where 
  "edge_set = fst pg"

definition start where
  "start = fst (snd pg)"

definition "end" where
  "end = snd (snd pg)"

definition analysis_dom_RN :: "'n set" where
  "analysis_dom_RN = UNIV"

fun kill_set_RN :: "('n,'v) edge \<Rightarrow> 'n set" where
  "kill_set_RN (q\<^sub>o, \<alpha>, q\<^sub>s) = {}"

fun gen_set_RN :: "('n,'v) edge \<Rightarrow> 'n set" where
  "gen_set_RN (q\<^sub>o, \<alpha>, q\<^sub>s) = {q\<^sub>o}"

definition d_init_RN :: "'n set" where
  "d_init_RN = {end}"

interpretation bw_may: analysis_BV_backward_may pg analysis_dom_RN kill_set_RN gen_set_RN d_init_RN
  using analysis_BV_backward_may.intro analysis_RN_axioms analysis_RN_def
  by (metis (mono_tags) analysis_dom_RN_def finite_UNIV subset_UNIV)

(* ADVARSEL:
   Denne egenskab tror jeg kun gælder for
   stier gennem grafen. For vi skal sikre at hver kants
   snd snd svarer til den næstes fst.
   Men den antagelse har jeg ikke.

   Eller man kunne snyde og lave definitionen af node_on_edge_list
   om til kun at samle den ene knude op og så den allersidste seperat.
 *)
term "LTS.path_with_word edge_set"
thm LTS.path_with_word.induct

lemma node_on_edge_list_S_hat_edge_list:
  assumes "ts \<in> LTS.transition_list_path edge_set"
  assumes "trans_tl (last ts) = end"
  assumes "node_on_edge_list ts q"
  shows "q \<in> bw_may.S_hat_edge_list ts d_init_RN"
  using assms
proof (induction rule: LTS.transition_list_path.induct[OF assms(1)])
  case (1 q' l q'')
  then show ?case
    by (simp add: d_init_RN_def Cons_eq_append_conv bw_may.S_hat_def node_on_edge_list_def)
next
  case (2 q' l q'' l' q''' ts)
  from 2(6) obtain \<pi>1 \<pi>2 e where 
    "(q', l, q'') # (q'', l', q''') # ts = \<pi>1 @ [e] @ \<pi>2"
    "q \<in> nodes_on_edge e"
    unfolding node_on_edge_list_def by auto
  then have "e = (q', l, q'') \<or> e \<in> set ((q'', l', q''') # ts)"
    by (metis (no_types, lifting) append_Cons hd_append in_set_conv_decomp list.sel(1) list.sel(3) tl_append2)
  then show ?case
  proof 
    assume "e = (q', l, q'')"
    then have "q = q' \<or> q = q''"
      using \<open>q \<in> nodes_on_edge e\<close> by auto
    then show ?case
    proof 
      assume "q = q'"
      then show ?case
        unfolding bw_may.S_hat_edge_list.simps bw_may.S_hat_def by auto
    next
      assume a: "q = q''"
      have "q \<in> bw_may.S_hat_edge_list ((q'', l', q''') # ts) d_init_RN"
        using "2.IH" "2.hyps"(2) "2.prems"(2) a node_on_edge_list_def by fastforce
      then show ?case
        unfolding bw_may.S_hat_edge_list.simps bw_may.S_hat_def using a by auto
    qed
  next
    assume a: "e \<in> set ((q'', l', q''') # ts)"
    then have "q \<in> bw_may.S_hat_edge_list ((q'', l', q''') # ts) d_init_RN"
      by (metis "2.IH" "2.hyps"(2) "2.prems"(2) \<open>q \<in> nodes_on_edge e\<close> append_Cons append_Nil in_set_conv_decomp last.simps list.distinct(1) node_on_edge_list_def)
    then show ?case
      unfolding bw_may.S_hat_edge_list.simps bw_may.S_hat_def by auto
  qed
qed

 
lemma S_hat_edge_list_node_on_edge_list:
  assumes "\<pi> \<noteq> []"
  assumes "trans_tl (last \<pi>) = end"
  assumes "q \<in> bw_may.S_hat_edge_list \<pi> d_init_RN"
  shows "node_on_edge_list \<pi> q"
  using assms 
proof (induction \<pi>)
  case Nil
  then show ?case
    by auto
next
  case (Cons e \<pi>)
  from Cons(4) have 
    "q \<in> bw_may.S_hat_edge_list \<pi> d_init_RN - kill_set_RN e \<or>
     q \<in> gen_set_RN e"
    using bw_may.S_hat_def by auto
  then show ?case
  proof 
    assume q_Shat: "q \<in> bw_may.S_hat_edge_list \<pi> d_init_RN - kill_set_RN e"
    have "\<pi> \<noteq> [] \<or> \<pi> = []"
      by auto
    then show ?thesis
    proof
      assume "\<pi> \<noteq> []"
      then show "node_on_edge_list (e # \<pi>) q"
        using Cons(1,3)
        by (metis Diff_iff q_Shat append_Cons last.simps node_on_edge_list_def)
    next
      assume "\<pi> = []"
      then show "node_on_edge_list (e # \<pi>) q"
        using d_init_RN_def q_Shat
        by (metis Cons.prems(2) Diff_empty append.left_neutral append_Cons bw_may.S_hat_edge_list.simps(1) insertI1 insert_commute kill_set_RN.elims last_ConsL nodes_on_edge.elims node_on_edge_list_def singleton_iff trans_tl.simps)   
 qed
  next
    assume "q \<in> gen_set_RN e"
    then show ?thesis
      unfolding node_on_edge_list_def
      by (metis append.left_neutral append_Cons empty_iff gen_set_RN.elims insert_iff nodes_on_edge.simps)
  qed
qed

lemma node_on_edge_list_UNIV_S_hat_edge_list:
  assumes "\<pi> \<in> LTS.transition_list_path edge_set"
  assumes "\<pi> \<noteq> []"
  assumes "trans_tl (last \<pi>) = end"
  shows "{q. node_on_edge_list \<pi> q} = bw_may.S_hat_edge_list \<pi> d_init_RN"
  using assms node_on_edge_list_S_hat_edge_list S_hat_edge_list_node_on_edge_list by auto

lemma yxyxyxyxyx:
  assumes "(ss, w) \<in> LTS.path_with_word edge_set"
  assumes "w = []"
  shows "\<exists>l. ss = [l]"
using assms proof (induction rule: LTS.path_with_word.induct[OF assms(1)])
  case (1 s)
  then show ?case
    by auto
next
  case (2 s' ss w s l)
  then show ?case
    by auto
qed

lemma yxyxyxyxyxyxyxyxyx:
  assumes "(ss, []) \<in> LTS.path_with_word edge_set"
  shows "\<exists>l. ss = [l]"
  using yxyxyxyxyx assms by auto

lemma yzyzyzyzyzyzzyzyz:
  assumes "(ss,w) \<in> LTS.path_with_word edge_set"
  assumes "w \<noteq> []"
  shows "last (transition_list (s # ss, l # w)) = last (transition_list (ss, w))"
  using assms proof (induction rule: LTS.path_with_word.induct[OF assms(1)])
  case (1 s')
  then show ?case
    by auto
next
  case (2 s'' ss w s' l)
  then show ?case
    by auto
qed

lemma xxxx:
  assumes "(ss,w) \<in> LTS.path_with_word edge_set"
  assumes "w \<noteq> []"
  assumes "last ss = end"
  shows "trans_tl (last (LTS.transition_list (ss,w))) = end"
using assms proof (induction rule: LTS.path_with_word.induct[OF assms(1)])
  case (1 s)
  then show ?case
    by auto
next
  case (2 s' ss w s l)
  show ?case
  proof (cases "w = []")
    case True
    then have "ss = []"
      using 2 yxyxyxyxyxyxyxyxyx by auto
    then show ?thesis
      using True 2 
      by auto
  next
    case False
    from 2 have "(s' # ss, w) \<in> LTS.path_with_word edge_set"
      by auto
    moreover
    have "w \<noteq> []"
      using False by auto
    moreover
    have "last (s' # ss) = end"
      using 2 by auto
    ultimately
    have "trans_tl (last (transition_list (s' # ss, w))) = end"
      using 2 by auto
    moreover
    have "last (transition_list (s' # ss, w)) =
        last (transition_list (s # s' # ss, l # w))"
      using yzyzyzyzyzyzzyzyz[of "s' # ss" w s l] \<open>w \<noteq> []\<close>
      using \<open>(s' # ss, w) \<in> LTS.path_with_word edge_set\<close> by auto
    ultimately
    show ?thesis
      by auto
  qed
qed

lemma yzxyzxyxzyxyxzyzxxyzyzx:
  assumes "(ss,w) \<in> LTS.path_with_word edge_set"
  assumes "w \<noteq> []"
  shows "transition_list (ss,w) \<noteq> []"
using assms proof (induction rule: LTS.path_with_word.induct[OF assms(1)])
  case (1 s)
  then show ?case by auto
next
  case (2 s' ss w s l)
  then show ?case
    by auto
qed

lemma yzxyzxyxzyxyxzyzxxyzyzx2:
  assumes "\<pi> \<in> LTS.path_with_word edge_set"
  assumes "snd \<pi> \<noteq> []"
  shows "transition_list \<pi> \<noteq> []"
  using assms yzxyzxyxzyxyxzyzxxyzyzx by (cases \<pi>) auto

lemma yuzzyuzyuzyzyuzyzyuzzyuzyuzuy:
  assumes "(ss, w) \<in> LTS.path_with_word edge_set"
  assumes "w \<noteq> []"
  shows "\<exists>s' s'' ss'. ss = s' # s'' # ss'"
using assms 
proof (induction rule: LTS.path_with_word.induct[OF assms(1)])
  case (1 s)
  then show ?case 
    by auto
next
  case (2 s' ss w s l)
  then show ?case 
    by auto
qed

lemma ryryryryryyryryryryryryr:
  assumes "(ss', w) \<in> LTS.path_with_word edge_set"
  assumes "ss' = s' # ss"
  assumes "w = []"
  shows "ss = []"
using assms 
proof (induction rule: LTS.path_with_word.induct[OF assms(1)])
  case (1 s)
  then show ?case 
    by auto
next
  case (2 s' ss w s l)
  then show ?case 
    by auto
qed

lemma uyuxyuuyxzuyxzuyxuyyu:
  assumes "(ss,w) \<in> LTS.path_with_word edge_set"
  assumes "w \<noteq> []"
  shows "transition_list (ss,w) \<in> LTS.transition_list_path edge_set"
  using assms 
proof (induction rule: LTS.path_with_word.induct[OF assms(1)])
  case (1 s)
  then show ?case
    by auto
next
  case (2 s' ss w s l)
  then show ?case
  proof (cases "w = []")
    case True
    then have s_empt: "ss = []"
      using 2(1) ryryryryryyryryryryryryr by auto

    from 2 have " [(s, l, s')] \<in> LTS.transition_list_path edge_set"
      using LTS.transition_list_path.intros(1)[of s l s' edge_set] by auto
    then show ?thesis
      using True s_empt by auto
  next
    case False
    then obtain l' w' where w_eql:"w = l' # w'"
      by (cases w) auto
    obtain s'' ss' where ss_eql: "ss = s'' # ss'"
      using 2(1) False yuzzyuzyuzyzyuzyzyuzzyuzyuzuy[of "s' #ss" w] by auto
    have "(s, l, s') \<in> edge_set"
      using 2 by auto
    moreover
    have "(s', l', s'') # transition_list (s'' # ss', w') \<in> LTS.transition_list_path edge_set"
      using 2 w_eql ss_eql by auto
    ultimately
    have "(s, l, s') # (s', l', s'') # transition_list (s'' # ss', w')
            \<in> LTS.transition_list_path edge_set"
      by (rule LTS.transition_list_path.intros(2)[of s l s'])
    then show ?thesis
      unfolding ss_eql w_eql by simp
  qed
qed

lemma nodes_on_path_S_hat_path:
  assumes "\<pi> \<in> LTS.path_with_word edge_set"
  assumes "snd \<pi> \<noteq> []"
  assumes "last (fst \<pi>) = end"
  shows "nodes_on_path \<pi> = bw_may.S_hat_path \<pi> d_init_RN"
proof -
  have "trans_tl (last (LTS.transition_list \<pi>)) = end"
    using assms(1,2,3) xxxx[of "fst \<pi>" "snd \<pi>"] by auto
  moreover
  have "LTS.transition_list \<pi> \<noteq> []"
    using assms(1,2) yzxyzxyxzyxyxzyzxxyzyzx2 using assms by auto
  moreover
  have "(LTS.transition_list \<pi>) \<in> LTS.transition_list_path edge_set"
    using assms(1) assms(2) uyuxyuuyxzuyxzuyxuyyu[of "fst \<pi>" "snd \<pi>"] 
    by auto
  ultimately
  show ?thesis
    by (simp add: bw_may.S_hat_path_def node_on_edge_list_UNIV_S_hat_edge_list nodes_on_path_def)
qed

definition summarizes_RN where
  "summarizes_RN \<rho> \<longleftrightarrow> (\<forall>\<pi> d. \<pi> \<in> LTS.path_with_word edge_set \<longrightarrow> LTS.get_end \<pi> = end \<longrightarrow> d \<in> nodes_on_path \<pi> \<longrightarrow> 
                         \<rho> \<Turnstile>\<^sub>l\<^sub>h BV\<langle>[Cst\<^sub>N (LTS.get_start \<pi>), Cst\<^sub>E d]\<rangle>.)"

theorem RN_sound:
  assumes "\<rho> \<Turnstile>\<^sub>l\<^sub>s\<^sub>t bw_may.ana_pg_bw_may s_BV"
  shows "summarizes_RN \<rho>"
proof -
  from assms have "bw_may.summarizes_bw_may \<rho>"
    using bw_may.sound_ana_pg_bw_may[of \<rho>] by auto
  then show ?thesis
    unfolding summarizes_RN_def bw_may.summarizes_bw_may_def bw_may.edge_set_def 
      bw_may.end_def using nodes_on_path_S_hat_path
    by (metis LTS.get_end_def Nil_is_append_conv edge_set_def end_def 
        list.discI mem_Collect_eq node_on_edge_list_def nodes_on_path_def 
        prod.exhaust_sel transition_list.simps(2) yxyxyxyxyx)
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

definition S_hat :: "('n,'v) edge \<Rightarrow> 'd set \<Rightarrow> 'd set" ("Ŝ\<^sub>E\<lbrakk>_\<rbrakk> _") where
  "Ŝ\<^sub>E\<lbrakk>e\<rbrakk> R = (R - kill_set e) \<union> gen_set e"

lemma S_hat_mono:
  assumes "R1 \<subseteq> R2"
  shows "Ŝ\<^sub>E\<lbrakk>e\<rbrakk> R1 \<subseteq> Ŝ\<^sub>E\<lbrakk>e\<rbrakk> R2"
  using assms unfolding S_hat_def by auto

fun S_hat_edge_list :: "('n,'v) edge list \<Rightarrow> 'd set \<Rightarrow> 'd set" ("Ŝ\<^sub>E\<^sub>s\<lbrakk>_\<rbrakk> _") where
  "Ŝ\<^sub>E\<^sub>s\<lbrakk>[]\<rbrakk> R = R" |
  "Ŝ\<^sub>E\<^sub>s\<lbrakk>(e # \<pi>)\<rbrakk> R = Ŝ\<^sub>E\<^sub>s\<lbrakk>\<pi>\<rbrakk> (Ŝ\<^sub>E\<lbrakk>e\<rbrakk> R)"

lemma S_hat_edge_list_def2:
  "Ŝ\<^sub>E\<^sub>s\<lbrakk>\<pi>\<rbrakk> R = foldl (\<lambda>a b. Ŝ\<^sub>E\<lbrakk>b\<rbrakk> a) R \<pi>"
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
  "Ŝ\<^sub>E\<^sub>s\<lbrakk>(xs @ ys)\<rbrakk> R = Ŝ\<^sub>E\<^sub>s\<lbrakk>ys\<rbrakk> (Ŝ\<^sub>E\<^sub>s\<lbrakk>xs\<rbrakk> R)"
  unfolding S_hat_edge_list_def2 foldl_append by auto

lemma S_hat_edge_list_mono:
  assumes "R1 \<subseteq> R2"
  shows "Ŝ\<^sub>E\<^sub>s\<lbrakk>\<pi>\<rbrakk> R1 \<subseteq> Ŝ\<^sub>E\<^sub>s\<lbrakk>\<pi>\<rbrakk> R2"
proof(induction \<pi> rule: List.rev_induct)
  case Nil
  then show ?case
    using assms by auto
next
  case (snoc x xs)
  then show ?case
    using assms by (simp add: S_hat_mono)
qed

definition S_hat_path :: "('n list \<times> 'v action list) \<Rightarrow> 'd set \<Rightarrow> 'd set" ("Ŝ\<^sub>P\<lbrakk>_\<rbrakk> _") where
  "Ŝ\<^sub>P\<lbrakk>\<pi>\<rbrakk> R = Ŝ\<^sub>E\<^sub>s\<lbrakk>LTS.transition_list \<pi>\<rbrakk> R"

lemma S_hat_path_mono:
  assumes "R1 \<subseteq> R2"
  shows "Ŝ\<^sub>P\<lbrakk>\<pi>\<rbrakk> R1 \<subseteq> Ŝ\<^sub>P\<lbrakk>\<pi>\<rbrakk> R2"
  unfolding S_hat_path_def using assms S_hat_edge_list_mono by auto

definition summarizes_fw_must :: "(pred, ('n, 'v, 'd) cst) pred_val \<Rightarrow> bool" where
   "summarizes_fw_must \<rho> \<longleftrightarrow>
     (\<forall>\<pi>_end d.
         \<rho> \<Turnstile>\<^sub>l\<^sub>h CBV\<langle>[\<pi>_end, d]\<rangle>. \<longrightarrow>
          (\<forall>\<pi>. \<pi> \<in> LTS.path_with_word edge_set \<longrightarrow> LTS.get_start \<pi> = start \<longrightarrow> LTS.get_end \<pi> = Decode_Node \<pi>_end \<longrightarrow> (Decode_Elem d) \<in> Ŝ\<^sub>P\<lbrakk>\<pi>\<rbrakk> d_init))"

interpretation fw_may: analysis_BV_forward_may pg analysis_dom "\<lambda>e. analysis_dom - (kill_set e)" "(\<lambda>e. analysis_dom - gen_set e)" "analysis_dom - d_init"
  using analysis_BV_forward_may.intro analysis_BV_forward_must_axioms analysis_BV_forward_must_def
  by (metis Diff_subset)

abbreviation ana_pg_fw_must where (* Copy paste *)
  "ana_pg_fw_must == fw_may.ana_pg_fw_may"

lemma opposite_lemma:
  assumes "d \<in> analysis_dom"
  assumes "\<not>d \<in> fw_may.S_hat_edge_list \<pi> (analysis_dom - d_init)"
  shows "d \<in> Ŝ\<^sub>E\<^sub>s\<lbrakk>\<pi>\<rbrakk> d_init"
  using assms proof (induction \<pi> rule: List.rev_induct)
  case Nil
  then show ?case
    by auto
next
  case (snoc x xs)
  then show ?case
    unfolding fw_may.S_hat_edge_list_def2
    by (simp add: S_hat_def fw_may.S_hat_def)
qed

lemma opposite_lemma2:
  assumes "d \<in> analysis_dom"
  assumes "\<not>d \<in> fw_may.S_hat_path \<pi> (analysis_dom - d_init)"
  shows "d \<in> Ŝ\<^sub>P\<lbrakk>\<pi>\<rbrakk> d_init"
  using S_hat_path_def fw_may.S_hat_path_def assms opposite_lemma by metis

lemma the_CBV_only_ana_CBV: "the_CBV \<notin> preds_dl (ana_pg_fw_must - (fw_may.ana_CBV ` UNIV))"
  unfolding fw_may.ana_pg_fw_may_def preds_dl_def preds_dl_def fw_may.ana_init_BV_def
    preds_dl_def fw_may.ana_anadom_BV_def preds_dl_def fw_may.ana_kill_BV_edge_def preds_dl_def
    fw_may.ana_gen_BV_edge_def fw_may.ana_entry_node_BV_def by auto 

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
  case (PosLit p ids)
  then show ?thesis
    using assms by auto 
next
  case (NegLit p ids)
  then show ?thesis 
    using assms by auto 
qed

definition preds_rhs where
  "preds_rhs rhs = \<Union>(preds_rh ` set rhs)"

lemma dkfjdfk: "preds_cls (Cls p ids rhs) = {p} \<union> preds_rhs rhs"
  sorry

lemma agree_off_rhs:
  assumes "\<forall>p. p \<noteq> p' \<longrightarrow> \<rho>' p = \<rho> p"
  assumes "p' \<notin> preds_rhs rhs"
  shows "\<lbrakk>rhs\<rbrakk>\<^sub>r\<^sub>h\<^sub>s \<rho>' \<sigma> \<longleftrightarrow> \<lbrakk>rhs\<rbrakk>\<^sub>r\<^sub>h\<^sub>s \<rho> \<sigma>"
  using assms agree_off_rh[of p' \<rho>' \<rho> _ \<sigma>] unfolding preds_rhs_def by auto

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
  shows "\<lbrakk>c\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho>' \<sigma> \<longleftrightarrow> \<lbrakk>c\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho> \<sigma>"
proof (cases c)
  case (Cls p ids rhs)
  show ?thesis
  proof
    assume "\<lbrakk>c\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho>' \<sigma>"
    show "\<lbrakk>c\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho> \<sigma>"
      unfolding Cls meaning_cls.simps
    proof
      assume "\<lbrakk>rhs\<rbrakk>\<^sub>r\<^sub>h\<^sub>s \<rho> \<sigma>"
      then have "\<lbrakk>rhs\<rbrakk>\<^sub>r\<^sub>h\<^sub>s \<rho>' \<sigma>"
        using agree_off_rhs
        by (metis Cls assms(1) assms(2) clause.simps(6) insert_iff preds_rhs_def)
      then show"\<lbrakk>(p, ids)\<rbrakk>\<^sub>l\<^sub>h \<rho> \<sigma>"
        using Cls \<open>\<lbrakk>c\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho>' \<sigma>\<close> assms(1) assms(2) by auto
    qed
  next
    assume "\<lbrakk>c\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho> \<sigma>"
    show "\<lbrakk>c\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho>' \<sigma>"
    unfolding Cls meaning_cls.simps
    proof
      assume "\<lbrakk>rhs\<rbrakk>\<^sub>r\<^sub>h\<^sub>s \<rho>' \<sigma>"
      then have "\<lbrakk>rhs\<rbrakk>\<^sub>r\<^sub>h\<^sub>s \<rho> \<sigma>"
        using agree_off_rhs
        by (metis Cls assms(1) assms(2) clause.simps(6) insert_iff preds_rhs_def)
      then show"\<lbrakk>(p, ids)\<rbrakk>\<^sub>l\<^sub>h \<rho>' \<sigma>"
        using Cls \<open>\<lbrakk>c\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho> \<sigma>\<close> assms(1) assms(2) by auto
    qed
  qed
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
  show "\<rho> \<Turnstile>\<^sub>d\<^sub>l dl"
    unfolding solves_program_def
  proof
    fix c
    assume "c \<in> dl"
    have "p' \<notin> preds_cls c"
      using \<open>c \<in> dl\<close> assms(2) preds_dl_def by fastforce
    show "\<rho> \<Turnstile>\<^sub>c\<^sub>l\<^sub>s c"
      by (metis \<open>\<rho>' \<Turnstile>\<^sub>d\<^sub>l dl\<close> \<open>c \<in> dl\<close> \<open>p' \<notin> preds_cls c\<close> agree_off_solves_cls assms(1) 
          solves_program_def)
  qed
next 
  assume "\<rho> \<Turnstile>\<^sub>d\<^sub>l dl"
  show "\<rho>' \<Turnstile>\<^sub>d\<^sub>l dl"
    unfolding solves_program_def
  proof
    fix c
    assume "c \<in> dl"
    have "p' \<notin> preds_cls c"
      using \<open>c \<in> dl\<close> assms(2) preds_dl_def by fastforce
    show "\<rho>' \<Turnstile>\<^sub>c\<^sub>l\<^sub>s c"
      by (metis \<open>\<rho> \<Turnstile>\<^sub>d\<^sub>l dl\<close> \<open>c \<in> dl\<close> \<open>p' \<notin> preds_cls c\<close> agree_off_solves_cls assms(1) 
          solves_program_def)
  qed
qed

lemma not_CBV:
  assumes "[Node q, Elem d] \<in> \<rho> the_CBV"
  assumes "\<rho> \<Turnstile>\<^sub>l\<^sub>s\<^sub>t ana_pg_fw_must s_BV"
  assumes a: "[Node q, Elem d] \<in> \<rho> the_BV"                  
  shows False
proof -
  have fin: "finite ana_pg_fw_must"
    using fw_may.ana_pg_fw_may_finite by auto

  have "\<rho> \<Turnstile>\<^sub>l\<^sub>s\<^sub>t ana_pg_fw_must s_BV"
    using assms(2) by force
  then have "\<rho> \<Turnstile>\<^sub>m\<^sub>i\<^sub>n ana_pg_fw_must s_BV"
    using fw_may.ana_pg_fw_may_stratified least_iff_minimal[of ana_pg_fw_must s_BV \<rho>] fin by auto
  then have \<rho>_sol: "\<rho> \<Turnstile>\<^sub>d\<^sub>l ana_pg_fw_must"
    using assms(2) least_solution_def by blast


  define \<rho>' where  "\<rho>' = (\<lambda>p. (if p = the_CBV then (\<rho> the_CBV) - {[Node q, Elem d]} else \<rho> p))"

  have CBV_solves: "\<rho>' \<Turnstile>\<^sub>c\<^sub>l\<^sub>s CBV\<langle>[Cst\<^sub>N q, \<uu>]\<rangle> :- [\<^bold>\<not>BV [Cst\<^sub>N q, \<uu>], anadom[\<uu>]] ."
    unfolding solves_cls_def
  proof 
    fix \<sigma>
    show "\<lbrakk>CBV\<langle>[Cst\<^sub>N q, \<uu>]\<rangle> :- [\<^bold>\<not>BV [Cst\<^sub>N q, \<uu>], anadom[\<uu>]].\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho>' \<sigma>"
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
      have "(\<forall>rh\<in>set [\<^bold>\<not>BV [Cst\<^sub>N q, \<uu>], anadom[\<uu>]]. \<lbrakk>rh\<rbrakk>\<^sub>r\<^sub>h \<rho> \<sigma>) \<longrightarrow> \<lbrakk>CBV\<langle>[Cst\<^sub>N q, \<uu>]\<rangle>.\<rbrakk>\<^sub>l\<^sub>h \<rho> \<sigma>"
      proof -
        have "CBV\<langle>[Cst\<^sub>N q, \<uu>]\<rangle> :- [\<^bold>\<not>BV [Cst\<^sub>N q, \<uu>], anadom[\<uu>]] . \<in> ana_pg_fw_must"
          unfolding fw_may.ana_pg_fw_may_def fw_may.ana_CBV_def by auto
        then have "\<rho> \<Turnstile>\<^sub>c\<^sub>l\<^sub>s CBV\<langle>[Cst\<^sub>N q, \<uu>]\<rangle> :- [\<^bold>\<not>BV [Cst\<^sub>N q, \<uu>], anadom[\<uu>]] ."
          using assms(2) unfolding least_solution_def
          unfolding solves_program_def
          by auto
        then show "(\<forall>rh\<in>set [\<^bold>\<not>BV [Cst\<^sub>N q, \<uu>], anadom[\<uu>]]. \<lbrakk>rh\<rbrakk>\<^sub>r\<^sub>h \<rho> \<sigma>) \<longrightarrow> \<lbrakk>CBV\<langle>[Cst\<^sub>N q, \<uu>]\<rangle>.\<rbrakk>\<^sub>l\<^sub>h \<rho> \<sigma>"
          unfolding solves_cls_def meaning_cls.simps by auto
      qed
      ultimately
      show ?thesis
        using Diff_iff \<rho>'_def empty_iff meaning_cls.simps meaning_rh.simps(3) set_ConsD set_empty2 by auto
    qed
  qed

  have \<rho>'_off_the_CBV: "\<forall>p. p \<noteq> the_CBV \<longrightarrow> \<rho>' p = \<rho> p"
    unfolding \<rho>'_def by auto
  
  have "\<rho> \<Turnstile>\<^sub>d\<^sub>l (ana_pg_fw_must - {fw_may.ana_CBV q})"
    using assms(2) unfolding least_solution_def solves_program_def by auto
  have "\<rho>' \<Turnstile>\<^sub>d\<^sub>l (ana_pg_fw_must - {fw_may.ana_CBV q})"
    unfolding solves_program_def
  proof 
    fix c
    assume a: "c \<in> ana_pg_fw_must - {fw_may.ana_CBV q}"
    then obtain p ids rhs where c_def: "c = Cls p ids rhs"
      by (cases c) auto

    from a have a': "c \<in> \<Union> (fw_may.ana_edge_BV ` fw_may.edge_set) \<or> 
          c \<in> (fw_may.ana_init_BV ` (analysis_dom - d_init)) \<or>
          c \<in> (fw_may.ana_anadom_BV ` (analysis_dom)) \<or>
          c \<in> \<Union> (fw_may.ana_kill_BV_edge ` fw_may.edge_set) \<or>
          c \<in> \<Union> (fw_may.ana_gen_BV_edge ` fw_may.edge_set) \<or>
          c \<in> range fw_may.ana_CBV - {fw_may.ana_CBV q} \<or>
          c \<in> {fw_may.ana_entry_node_BV}"
      unfolding fw_may.ana_pg_fw_may_def by auto

    have "\<rho>' \<Turnstile>\<^sub>c\<^sub>l\<^sub>s Cls p ids rhs"
      unfolding solves_cls_def
    proof (rule)
      fix \<sigma>' :: "var \<Rightarrow> ('n, 'v, 'd) cst"
      { 
        assume b: "Cls p ids rhs \<in> \<Union> (fw_may.ana_edge_BV ` fw_may.edge_set)"
        from a c_def have "\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho> \<sigma>'"
          using \<rho>_sol unfolding solves_program_def solves_cls_def by blast
        from b have "\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho>' \<sigma>'"
          using \<open>\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho> \<sigma>'\<close> \<rho>'_def by auto
      }
      moreover
      {
        assume b: "Cls p ids rhs \<in> (fw_may.ana_init_BV ` (analysis_dom - d_init))"
        from a c_def have "\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho> \<sigma>'"
          using \<rho>_sol unfolding solves_program_def solves_cls_def by blast
        from b have "\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho>' \<sigma>'"
          using \<open>\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho> \<sigma>'\<close>
           \<rho>'_def  fw_may.ana_init_BV_def by auto
      }
      moreover
      {
        assume b: "Cls p ids rhs \<in> (fw_may.ana_anadom_BV ` analysis_dom)"
        from a c_def have "\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho> \<sigma>'"
          using \<rho>_sol unfolding solves_program_def solves_cls_def by blast
        from b have "\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho>' \<sigma>'"
          using \<open>\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho> \<sigma>'\<close> \<rho>'_def fw_may.ana_anadom_BV_def by auto
      }
      moreover
      {
        assume b: "Cls p ids rhs \<in> \<Union> (fw_may.ana_kill_BV_edge ` fw_may.edge_set)"
        from a c_def have "\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho> \<sigma>'"
          using \<rho>_sol unfolding solves_program_def solves_cls_def by blast
        from b have "\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho>' \<sigma>'"
          using \<open>\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho> \<sigma>'\<close> \<rho>'_def fw_may.ana_kill_BV_edge_def by auto
      }
      moreover
      {
        assume b: "Cls p ids rhs \<in> \<Union> (fw_may.ana_gen_BV_edge ` fw_may.edge_set)"
        from a c_def have "\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho> \<sigma>'"
          using \<rho>_sol unfolding solves_program_def solves_cls_def by blast
        from b have "\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho>' \<sigma>'"
          using \<open>\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho> \<sigma>'\<close> \<rho>'_def fw_may.ana_gen_BV_edge_def by auto
      }
      moreover
      {
        assume "Cls p ids rhs \<in> range fw_may.ana_CBV - {fw_may.ana_CBV q}"
        then have "\<exists>q'. p = the_CBV \<and> ids = [Cst\<^sub>N q', \<uu>] \<and> q' \<noteq> q"
          unfolding fw_may.ana_CBV_def by auto
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

          have rhs_def: "rhs = [\<^bold>\<not>BV [Cst\<^sub>N q', \<uu>],anadom[\<uu>]]"
            using a c_def fw_may.ana_pg_fw_may_def fw_may.ana_CBV_def p_def 
              fw_may.ana_entry_node_BV_def fw_may.ana_init_BV_def fw_may.ana_anadom_BV_def
              fw_may.ana_CBV_def ids_def fw_may.ana_CBV_def fw_may.ana_CBV_def
              \<open>Cls p ids rhs \<in> range fw_may.ana_CBV - {fw_may.ana_CBV q}\<close> fw_may.ana_CBV_def yah 
            by force
          have "\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho> \<sigma>'"
            by (metis \<open>\<rho> \<Turnstile>\<^sub>d\<^sub>l (ana_pg_fw_must - {fw_may.ana_CBV q})\<close> a c_def solves_cls_def solves_program_def)
          then show ?thesis
            unfolding p_def ids_def rhs_def meaning_cls.simps \<eta>v \<rho>'_def using assms(3) by force
        next
          case False
          then have False': "\<sigma>' the_\<uu> \<noteq> Elem d"
            by auto
          from yah have p_def: "p = the_CBV"
            by auto
          from yah have ids_def: "ids = [Cst\<^sub>N q', \<uu>]"
            by auto
          have rhs_def: "rhs = [\<^bold>\<not>BV [Cst\<^sub>N q', \<uu>],anadom[\<uu>]]"
            using a c_def fw_may.ana_pg_fw_may_def fw_may.ana_CBV_def p_def 
              fw_may.ana_entry_node_BV_def fw_may.ana_init_BV_def fw_may.ana_anadom_BV_def
              fw_may.ana_CBV_def ids_def fw_may.ana_CBV_def fw_may.ana_CBV_def
              \<open>Cls p ids rhs \<in> range fw_may.ana_CBV - {fw_may.ana_CBV q}\<close> fw_may.ana_CBV_def yah 
            by force
          have "\<lbrakk>CBV\<langle>[Cst\<^sub>N q', \<uu>]\<rangle> :- [\<^bold>\<not>BV[Cst\<^sub>N q', \<uu>], anadom[\<uu>]] .\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho> \<sigma>'"
            using \<open>Cls p ids rhs \<in> range fw_may.ana_CBV - {fw_may.ana_CBV q}\<close>
            unfolding p_def[symmetric] rhs_def[symmetric] 
            unfolding ids_def[symmetric]
            using assms(1)
            unfolding least_solution_def
            unfolding fw_may.ana_pg_fw_may_def
            by (metis \<open>\<rho> \<Turnstile>\<^sub>d\<^sub>l (ana_pg_fw_must - {fw_may.ana_CBV q})\<close> a c_def solves_cls_def solves_program_def)
          then have "\<lbrakk>CBV\<langle>[Cst\<^sub>N q', \<uu>]\<rangle> :- [\<^bold>\<not>BV[Cst\<^sub>N q', \<uu>], anadom[\<uu>]] .\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho>' \<sigma>'"
            unfolding \<rho>'_def using False' by force
          then show ?thesis
            unfolding p_def ids_def rhs_def by auto
        qed
      }
      moreover
      {
        assume b: "Cls p ids rhs \<in> {fw_may.ana_entry_node_BV}"
        from a c_def have "\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho> \<sigma>'"
          using assms(1)
          unfolding least_solution_def solves_program_def solves_cls_def
          by (metis \<open>\<rho> \<Turnstile>\<^sub>d\<^sub>l (ana_pg_fw_must - {fw_may.ana_CBV q})\<close> solves_cls_def solves_program_def)
        from b have "\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho>' \<sigma>'"
          using \<open>\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho> \<sigma>'\<close> \<rho>'_def fw_may.ana_entry_node_BV_def by fastforce
      }
      ultimately
      show "\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho>' \<sigma>'"
        using a' using c_def by metis
    qed
    then show "\<rho>' \<Turnstile>\<^sub>c\<^sub>l\<^sub>s c"
      unfolding c_def by auto
  qed
  then have "\<rho>' \<Turnstile>\<^sub>d\<^sub>l ana_pg_fw_must"
    using CBV_solves unfolding fw_may.ana_CBV_def solves_program_def
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
  assumes "\<rho> \<Turnstile>\<^sub>l\<^sub>h CBV\<langle>[Cst\<^sub>N q, Cst\<^sub>E d]\<rangle>."
  assumes "\<rho> \<Turnstile>\<^sub>l\<^sub>h BV\<langle>[Cst\<^sub>N q, Cst\<^sub>E d]\<rangle>."
  shows "False"
proof -
  have "[Node q, Elem d] \<in> \<rho> the_CBV"
    using assms(2)
    unfolding solves_lh.simps
    unfolding meaning_lh.simps
    by auto
  moreover
  have "[Node q, Elem d] \<in> \<rho> the_BV"
    using assms(3)
    unfolding solves_lh.simps
    unfolding meaning_lh.simps
    by auto
  ultimately
  show "False"
    using not_CBV[of q d \<rho>] assms(1) by auto
qed

thm analysis_BV_forward_may.not_kill

lemma not_init_node:
  assumes "\<rho> \<Turnstile>\<^sub>l\<^sub>s\<^sub>t ana_pg_fw_must s_BV"
  shows "\<not>\<rho> \<Turnstile>\<^sub>l\<^sub>h init\<langle>[Cst\<^sub>N q]\<rangle>."
proof -
  have "finite ana_pg_fw_must"
    using fw_may.ana_pg_fw_may_finite by auto
  moreover
  have "\<rho> \<Turnstile>\<^sub>l\<^sub>s\<^sub>t ana_pg_fw_must s_BV"
    using assms by blast
  moreover
  have "strat_wf s_BV ana_pg_fw_must"
    using fw_may.ana_pg_fw_may_stratified by blast
  moreover
  have "\<forall>c\<in>ana_pg_fw_must. 
            \<forall>\<sigma>'. (the_lh c \<cdot>\<^sub>v\<^sub>l\<^sub>h \<sigma>') = (init\<langle>[Cst\<^sub>N q]\<rangle>.) \<longrightarrow> \<not> \<lbrakk>the_rhs c\<rbrakk>\<^sub>r\<^sub>h\<^sub>s \<rho> \<sigma>'"
  proof (rule, rule, rule)
    fix c :: "(pred, var, ('n, 'v, 'd) cst) clause"
    fix \<sigma>'
    assume "(the_lh c \<cdot>\<^sub>v\<^sub>l\<^sub>h \<sigma>') = (init\<langle>[Cst\<^sub>N q]\<rangle>.)"
    moreover
    assume "c \<in> ana_pg_fw_must "
    then have "c \<in> ana_pg_fw_must"
      by auto
    ultimately
    show "\<not> \<lbrakk>the_rhs c\<rbrakk>\<^sub>r\<^sub>h\<^sub>s \<rho> \<sigma>'"
      unfolding fw_may.ana_pg_fw_may_def fw_may.ana_init_BV_def fw_may.ana_anadom_BV_def fw_may.ana_kill_BV_edge_def fw_may.ana_gen_BV_edge_def fw_may.ana_CBV_def fw_may.ana_entry_node_BV_def
      by auto
  qed
  then have "(\<not> (\<exists>c\<in>ana_pg_fw_must. \<exists>\<sigma>'. lh_consequence \<rho> c (init\<langle>[Cst\<^sub>N q]\<rangle>.)))"
    unfolding lh_consequence_def by metis
  ultimately
  have "\<rho> \<Turnstile>\<^sub>r\<^sub>h ( \<^bold>\<not> the_init [Cst\<^sub>N q])"
    using solves_NegLit_least[of ana_pg_fw_must \<rho> s_BV] by auto
  then show ?thesis
    by auto
qed

lemma not_anadom_node:
  assumes "\<rho> \<Turnstile>\<^sub>l\<^sub>s\<^sub>t ana_pg_fw_must s_BV"
  shows "\<not>\<rho> \<Turnstile>\<^sub>l\<^sub>h anadom\<langle>[Cst\<^sub>N q]\<rangle>."
proof -
  have "finite ana_pg_fw_must"
    using fw_may.ana_pg_fw_may_finite by auto
  moreover
  have "\<rho> \<Turnstile>\<^sub>l\<^sub>s\<^sub>t ana_pg_fw_must s_BV"
    using assms by blast
  moreover
  have "strat_wf s_BV ana_pg_fw_must"
    using fw_may.ana_pg_fw_may_stratified by blast
  moreover
  have "\<forall>c\<in>ana_pg_fw_must. 
            \<forall>\<sigma>'. (the_lh c \<cdot>\<^sub>v\<^sub>l\<^sub>h \<sigma>') = (anadom\<langle>[Cst\<^sub>N q]\<rangle>.) \<longrightarrow> \<not> \<lbrakk>the_rhs c\<rbrakk>\<^sub>r\<^sub>h\<^sub>s \<rho> \<sigma>'"
  proof (rule, rule, rule)
    fix c :: "(pred, var, ('n, 'v, 'd) cst) clause"
    fix \<sigma>'
    assume "(the_lh c \<cdot>\<^sub>v\<^sub>l\<^sub>h \<sigma>') = (anadom\<langle>[Cst\<^sub>N q]\<rangle>.)"
    moreover
    assume "c \<in> ana_pg_fw_must"
    then have "c \<in> ana_pg_fw_must"
      by auto
    ultimately
    show "\<not> \<lbrakk>the_rhs c\<rbrakk>\<^sub>r\<^sub>h\<^sub>s \<rho> \<sigma>'"
      unfolding fw_may.ana_pg_fw_may_def fw_may.ana_init_BV_def fw_may.ana_anadom_BV_def fw_may.ana_kill_BV_edge_def fw_may.ana_gen_BV_edge_def fw_may.ana_CBV_def fw_may.ana_entry_node_BV_def
      by auto
  qed
  then have "(\<not> (\<exists>c\<in>ana_pg_fw_must. lh_consequence \<rho> c anadom\<langle>[Cst\<^sub>N q]\<rangle>.))"
    unfolding lh_consequence_def by metis
  ultimately
  have "\<rho> \<Turnstile>\<^sub>r\<^sub>h ( \<^bold>\<not> the_anadom [Cst\<^sub>N q])"
    using solves_NegLit_least[of ana_pg_fw_must \<rho> s_BV "[Cst\<^sub>N q]" the_anadom] by auto

  then show ?thesis
    by auto
qed

lemma not_init_action: (* Copy paste adapt from not_init_node. They are kind of special cases of meaning_NegLit_least because *)
  assumes "\<rho> \<Turnstile>\<^sub>l\<^sub>s\<^sub>t ana_pg_fw_must s_BV"
  shows "\<not>\<rho> \<Turnstile>\<^sub>l\<^sub>h init\<langle>[Cst\<^sub>A q]\<rangle>."
proof -
  have "finite ana_pg_fw_must"
    using fw_may.ana_pg_fw_may_finite by blast
  moreover
  have "\<rho> \<Turnstile>\<^sub>l\<^sub>s\<^sub>t ana_pg_fw_must s_BV"
    using assms by blast
  moreover
  have "strat_wf s_BV ana_pg_fw_must"
    using fw_may.ana_pg_fw_may_stratified by blast
  moreover
  have "\<forall>c\<in>ana_pg_fw_must. 
            \<forall>\<sigma>'. (the_lh c \<cdot>\<^sub>v\<^sub>l\<^sub>h \<sigma>') = (init\<langle>[Cst\<^sub>A q]\<rangle>.) \<longrightarrow> \<not> \<lbrakk>the_rhs c\<rbrakk>\<^sub>r\<^sub>h\<^sub>s \<rho> \<sigma>'"
  proof (rule, rule, rule)
    fix c :: "(pred, var, ('n, 'v, 'd) cst) clause"
    fix \<sigma>'
    assume "(the_lh c \<cdot>\<^sub>v\<^sub>l\<^sub>h \<sigma>') = (init\<langle>[Cst\<^sub>A q]\<rangle>.)"
    moreover
    assume "c \<in> ana_pg_fw_must"
    then have "c \<in> ana_pg_fw_must"
      by auto
    ultimately
    show "\<not> \<lbrakk>the_rhs c\<rbrakk>\<^sub>r\<^sub>h\<^sub>s \<rho> \<sigma>'"
      unfolding fw_may.ana_pg_fw_may_def fw_may.ana_init_BV_def fw_may.ana_anadom_BV_def fw_may.ana_kill_BV_edge_def fw_may.ana_gen_BV_edge_def fw_may.ana_CBV_def fw_may.ana_entry_node_BV_def
      by auto
  qed
  then have "(\<not> (\<exists>c\<in>ana_pg_fw_must. lh_consequence \<rho> c init\<langle>[Cst\<^sub>A q]\<rangle>.))"
    unfolding lh_consequence_def by metis
  ultimately
  have "\<rho> \<Turnstile>\<^sub>r\<^sub>h ( \<^bold>\<not> the_init [Cst\<^sub>A q])"
    using solves_NegLit_least[of ana_pg_fw_must \<rho> s_BV "[Cst\<^sub>A q]" the_init] by auto
  then show ?thesis
    by auto
qed

lemma not_anadom_action: (* Copy paste adapt from not_init_node. They are kind of special cases of meaning_NegLit_least because *)
  assumes "\<rho> \<Turnstile>\<^sub>l\<^sub>s\<^sub>t ana_pg_fw_must s_BV"
  shows "\<not>\<rho> \<Turnstile>\<^sub>l\<^sub>h anadom\<langle>[Cst\<^sub>A q]\<rangle>."
proof -
  have "finite ana_pg_fw_must"
    using fw_may.ana_pg_fw_may_finite by blast
  moreover
  have "\<rho> \<Turnstile>\<^sub>l\<^sub>s\<^sub>t ana_pg_fw_must s_BV"
    using assms by blast
  moreover
  have "strat_wf s_BV ana_pg_fw_must"
    using fw_may.ana_pg_fw_may_stratified by blast
  moreover
  have "\<forall>c\<in>ana_pg_fw_must . 
            \<forall>\<sigma>'. (the_lh c \<cdot>\<^sub>v\<^sub>l\<^sub>h \<sigma>') = (anadom\<langle>[Cst\<^sub>A q]\<rangle>.) \<longrightarrow> \<not> \<lbrakk>the_rhs c\<rbrakk>\<^sub>r\<^sub>h\<^sub>s \<rho> \<sigma>'"
  proof (rule, rule, rule)
    fix c :: "(pred, var, ('n, 'v, 'd) cst) clause"
    fix \<sigma>'
    assume "(the_lh c \<cdot>\<^sub>v\<^sub>l\<^sub>h \<sigma>') = (anadom\<langle>[Cst\<^sub>A q]\<rangle>.)"
    moreover
    assume "c \<in> (ana_pg_fw_must)"
    then have "c \<in> (ana_pg_fw_must)"
      by auto
    ultimately
    show "\<not> \<lbrakk>the_rhs c\<rbrakk>\<^sub>r\<^sub>h\<^sub>s \<rho> \<sigma>'"
      unfolding fw_may.ana_pg_fw_may_def fw_may.ana_init_BV_def fw_may.ana_anadom_BV_def fw_may.ana_kill_BV_edge_def fw_may.ana_gen_BV_edge_def fw_may.ana_CBV_def fw_may.ana_entry_node_BV_def
      by auto
  qed
  then have "(\<not> (\<exists>c\<in>ana_pg_fw_must. lh_consequence \<rho> c anadom\<langle>[Cst\<^sub>A q]\<rangle>.))"
    unfolding lh_consequence_def by metis
  ultimately
  have "\<rho> \<Turnstile>\<^sub>r\<^sub>h (\<^bold>\<not> the_anadom [Cst\<^sub>A q])"
    using solves_NegLit_least[of ana_pg_fw_must \<rho> s_BV "[Cst\<^sub>A q]" the_anadom] by auto

  then show ?thesis
    by auto
qed

lemma is_Cst_if_init:
  assumes "\<rho> \<Turnstile>\<^sub>l\<^sub>s\<^sub>t ana_pg_fw_must s_BV"
  assumes "\<rho> \<Turnstile>\<^sub>l\<^sub>h init\<langle>[d]\<rangle>."
  shows "is_Cst d"
proof (cases d)
  case (Var x)
  then have "\<rho> \<Turnstile>\<^sub>l\<^sub>h init\<langle>[Var x]\<rangle>."
    using Var assms(2) by auto
  then have "\<rho> \<Turnstile>\<^sub>l\<^sub>h init\<langle>[Cst\<^sub>N undefined]\<rangle>."
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

lemma is_Cst_if_anadom:
  assumes "\<rho> \<Turnstile>\<^sub>l\<^sub>s\<^sub>t ana_pg_fw_must s_BV"
  assumes "\<rho> \<Turnstile>\<^sub>l\<^sub>h anadom\<langle>[d]\<rangle>."
  shows "is_Cst d"
proof (cases d)
  case (Var x)
  then have "\<rho> \<Turnstile>\<^sub>l\<^sub>h anadom\<langle>[Var x]\<rangle>."
    using Var assms(2) by auto
  then have "\<rho> \<Turnstile>\<^sub>l\<^sub>h anadom\<langle>[Cst\<^sub>N undefined]\<rangle>."
    by auto
  then have "False"
    using assms(1) not_anadom_node by blast
  then show ?thesis 
    by metis
next
  case (Cst e)
  then show ?thesis 
    by auto
qed

lemma is_elem_if_init:
  assumes "\<rho> \<Turnstile>\<^sub>l\<^sub>s\<^sub>t ana_pg_fw_must s_BV"
  assumes "\<rho> \<Turnstile>\<^sub>l\<^sub>h init\<langle>[Cst d]\<rangle>."
  shows "is_elem d"
proof (cases "d")
  case (Node x1)
  then show ?thesis
    using assms(1) assms(2) not_init_node by blast
next
  case (Elem x2)
  then show ?thesis
    by simp
next
  case (Action x3)
  then show ?thesis
    using assms(1) assms(2) not_init_action by blast
qed

lemma in_analysis_dom_if_init': (* init, like kill and gen doesn't have rhsides, so we could make a lemma like uuuuuuuuh_aaa for this case??? *)
  assumes "\<rho> \<Turnstile>\<^sub>l\<^sub>s\<^sub>t ana_pg_fw_must s_BV"
  assumes "\<rho> \<Turnstile>\<^sub>l\<^sub>h init\<langle>[Cst\<^sub>E d]\<rangle>."
  shows "d \<in> analysis_dom"
proof -
  have "finite ana_pg_fw_must"
    using fw_may.ana_pg_fw_may_finite by blast
  moreover
  have "\<rho> \<Turnstile>\<^sub>l\<^sub>s\<^sub>t ana_pg_fw_must s_BV"
    using assms(1) by blast
  moreover
  have "strat_wf s_BV ana_pg_fw_must"
    using fw_may.ana_pg_fw_may_stratified by blast
  moreover
  have "\<rho> \<Turnstile>\<^sub>r\<^sub>h init [Cst\<^sub>E d]"
    using assms(2) by auto
  ultimately
  have "(\<exists>c\<in>ana_pg_fw_must. lh_consequence \<rho> c init\<langle>[Cst\<^sub>E d]\<rangle>.)"
    using solves_PosLit_least[of ana_pg_fw_must \<rho> s_BV "[Cst\<^sub>E d]" the_init] by auto
  then have "d \<in> analysis_dom - d_init"
    unfolding lh_consequence_def fw_may.ana_pg_fw_may_def fw_may.ana_init_BV_def  
      fw_may.ana_anadom_BV_def fw_may.ana_kill_BV_edge_def fw_may.ana_gen_BV_edge_def 
      fw_may.ana_CBV_def fw_may.ana_entry_node_BV_def by auto
  then show "d \<in> analysis_dom"
    by blast
qed

lemma in_analysis_dom_if_anadom': (* init, like kill and gen doesn't have rhsides, so we could make a lemma like uuuuuuuuh_aaa for this case??? *)
  assumes "\<rho> \<Turnstile>\<^sub>l\<^sub>s\<^sub>t ana_pg_fw_must s_BV"
  assumes "\<rho> \<Turnstile>\<^sub>l\<^sub>h anadom\<langle>[Cst\<^sub>E d]\<rangle>."
  shows "d \<in> analysis_dom"
proof -
  have "finite ana_pg_fw_must"
    using fw_may.ana_pg_fw_may_finite by blast
  moreover
  have "\<rho> \<Turnstile>\<^sub>l\<^sub>s\<^sub>t ana_pg_fw_must s_BV"
    using assms(1) by blast
  moreover
  have "strat_wf s_BV ana_pg_fw_must"
    using fw_may.ana_pg_fw_may_stratified by blast
  moreover
  have "\<rho> \<Turnstile>\<^sub>r\<^sub>h anadom [Cst\<^sub>E d]"
    using assms(2) by auto
  ultimately
  have "(\<exists>c\<in>ana_pg_fw_must. lh_consequence \<rho> c anadom\<langle>[Cst\<^sub>E d]\<rangle>.)"
    using solves_PosLit_least[of ana_pg_fw_must \<rho> s_BV "[Cst\<^sub>E d]" the_anadom] by auto
  then show "d \<in> analysis_dom"
    unfolding lh_consequence_def fw_may.ana_pg_fw_may_def fw_may.ana_init_BV_def  
      fw_may.ana_anadom_BV_def fw_may.ana_kill_BV_edge_def fw_may.ana_gen_BV_edge_def 
      fw_may.ana_CBV_def fw_may.ana_entry_node_BV_def by auto
qed

lemma in_analysis_dom_if_init:
  assumes "\<rho> \<Turnstile>\<^sub>l\<^sub>s\<^sub>t ana_pg_fw_must s_BV"
  assumes "\<rho> \<Turnstile>\<^sub>l\<^sub>h init\<langle>[d]\<rangle>."
  shows "Decode_Elem d \<in> analysis_dom"
proof -
  have "is_Cst d"
    using assms(1) assms(2) is_Cst_if_init by blast
  then obtain d' where "d = Cst d'"
    by (meson is_Cst_def)
  then obtain d'' where "d' = Elem d''"
    using is_elem_if_init not_init_node assms(1) assms(2) not_init_action by (cases d') auto
  show ?thesis
    using \<open>d = Cst d'\<close> \<open>d' = Elem d''\<close> assms(1) assms(2) in_analysis_dom_if_init' by auto
qed

lemma in_analysis_dom_if_anadom:
  assumes "\<rho> \<Turnstile>\<^sub>l\<^sub>s\<^sub>t ana_pg_fw_must s_BV"
  assumes "\<rho> \<Turnstile>\<^sub>l\<^sub>h anadom\<langle>[d]\<rangle>."
  shows "Decode_Elem d \<in> analysis_dom"
proof -
  have "is_Cst d"
    using assms(1) assms(2) is_Cst_if_anadom by blast
  then obtain d' where "d = Cst d'"
    by (meson is_Cst_def)
  then obtain d'' where "d' = Elem d''"
    using is_elem_if_init assms(1) assms(2) not_anadom_node not_anadom_action by (cases d') auto
  show ?thesis
    using \<open>d = Cst d'\<close> \<open>d' = Elem d''\<close> assms(1) assms(2) in_analysis_dom_if_anadom' by auto
qed

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

lemma anadom_if_CBV:
  assumes "\<rho> \<Turnstile>\<^sub>l\<^sub>s\<^sub>t ana_pg_fw_must s_BV"
  assumes "\<rho> \<Turnstile>\<^sub>l\<^sub>h CBV\<langle>[\<pi>_end, d]\<rangle>."
  shows "\<rho> \<Turnstile>\<^sub>l\<^sub>h anadom\<langle>[d]\<rangle>."
proof (rule ccontr) (* Proof copy paste and adapted from not_init_action *)
  assume asm: "\<not> \<rho> \<Turnstile>\<^sub>l\<^sub>h anadom\<langle>[d]\<rangle>."
  then have "\<exists>\<sigma>. \<not>[\<lbrakk>d\<rbrakk>\<^sub>i\<^sub>d \<sigma>] \<in> \<rho> the_anadom"
    by auto
  then obtain \<sigma> where asm': "\<not>[\<lbrakk>d\<rbrakk>\<^sub>i\<^sub>d \<sigma>] \<in> \<rho> the_anadom"
    by auto

  have "finite ana_pg_fw_must"
    using fw_may.ana_pg_fw_may_finite by auto
  then have "\<rho> \<Turnstile>\<^sub>l\<^sub>s\<^sub>t ana_pg_fw_must s_BV"
    using downward_least_solution2[of ana_pg_fw_must s_BV \<rho> 2] assms(2)
    using fw_may.ana_pg_fw_may_stratified assms(1) by blast 
  then have "\<rho> \<Turnstile>\<^sub>m\<^sub>i\<^sub>n ana_pg_fw_must s_BV"
    using least_iff_minimal[of]
    using strat_wf_mod_if_strat_wf \<open>finite ana_pg_fw_must\<close> finite_below_finite
    by (smt (verit) fw_may.ana_pg_fw_may_stratified) 
  moreover

  define \<rho>' where "\<rho>' = (\<lambda>p. (if p = the_CBV then (\<rho> the_CBV) - {[\<lbrakk>\<pi>_end\<rbrakk>\<^sub>i\<^sub>d \<sigma>, \<lbrakk>d\<rbrakk>\<^sub>i\<^sub>d \<sigma>]} else \<rho> p))"

  have "\<rho>' \<Turnstile>\<^sub>d\<^sub>l ana_pg_fw_must"
    unfolding solves_program_def
  proof
    fix c
    assume a: "c \<in> ana_pg_fw_must"
    then obtain p ids rhs where c_def: "c = Cls p ids rhs"
      by (cases c) auto

    term fw_may.ana_anadom_BV

    from a have a': "c \<in> \<Union> (fw_may.ana_edge_BV ` fw_may.edge_set) \<or> 
          c \<in> (fw_may.ana_init_BV ` (analysis_dom - d_init)) \<or>
          c \<in> (fw_may.ana_anadom_BV ` analysis_dom) \<or>
          c \<in> \<Union> (fw_may.ana_kill_BV_edge ` fw_may.edge_set) \<or>
          c \<in> \<Union> (fw_may.ana_gen_BV_edge ` fw_may.edge_set) \<or>
          c \<in> fw_may.ana_CBV ` UNIV \<or>
          c \<in> {fw_may.ana_entry_node_BV}"
      unfolding fw_may.ana_pg_fw_may_def by auto

    have "\<rho>' \<Turnstile>\<^sub>c\<^sub>l\<^sub>s Cls p ids rhs"
      unfolding solves_cls_def
    proof (rule)
      fix \<sigma>' :: "var \<Rightarrow> ('n, 'v, 'd) cst"
      { 
        assume b: "Cls p ids rhs \<in> \<Union> (fw_may.ana_edge_BV ` fw_may.edge_set)"
        from a c_def have "\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho> \<sigma>'"
          using assms(1)
          unfolding least_solution_def solves_program_def solves_cls_def by metis
        from b have "\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho>' \<sigma>'"
          using \<open>\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho> \<sigma>'\<close> \<rho>'_def by auto
      }
      moreover
      {
        assume b: "Cls p ids rhs \<in> (fw_may.ana_init_BV ` (analysis_dom - d_init))"
        from a c_def have "\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho> \<sigma>'"
          using assms(1)
          unfolding least_solution_def solves_program_def solves_cls_def by metis
        from b have "\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho>' \<sigma>'"
          using \<open>\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho> \<sigma>'\<close> \<rho>'_def fw_may.ana_init_BV_def by auto
      }
      moreover
      {
        assume b: "Cls p ids rhs \<in> (fw_may.ana_anadom_BV ` analysis_dom)"
        from a c_def have "\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho> \<sigma>'"
          using assms(1)
          unfolding least_solution_def solves_program_def solves_cls_def by metis
        from b have "\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho>' \<sigma>'"
          using \<open>\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho> \<sigma>'\<close> \<rho>'_def fw_may.ana_anadom_BV_def by auto
      }
      moreover
      {
        assume b: "Cls p ids rhs \<in> \<Union> (fw_may.ana_kill_BV_edge ` fw_may.edge_set)"
        from a c_def have "\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho> \<sigma>'"
          using assms(1)
          unfolding least_solution_def solves_program_def solves_cls_def by metis
        from b have "\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho>' \<sigma>'"
          using fw_may.ana_kill_BV_edge_def fw_may.ana_kill_BV_edge_def \<open>\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho> \<sigma>'\<close>
            \<rho>'_def by auto
      }
      moreover
      {
        assume b: "Cls p ids rhs \<in> \<Union> (fw_may.ana_gen_BV_edge ` fw_may.edge_set)"
        from a c_def have "\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho> \<sigma>'"
          using assms(1)
          unfolding least_solution_def solves_program_def solves_cls_def by metis
        from b have "\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho>' \<sigma>'"
          using fw_may.ana_gen_BV_edge_def \<open>\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho> \<sigma>'\<close> \<rho>'_def by auto
      }
      moreover
      {
        assume "Cls p ids rhs \<in> fw_may.ana_CBV ` UNIV"
        then have "\<exists>q'. p = the_CBV \<and> ids = [Cst\<^sub>N q', \<uu>]"
          unfolding fw_may.ana_CBV_def by blast
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

          have rhs_def: "rhs = [\<^bold>\<not>BV [Cst\<^sub>N q', \<uu>],anadom[\<uu>]]"
            using a c_def fw_may.ana_pg_fw_may_def fw_may.ana_kill_BV_edge_def
              fw_may.ana_gen_BV_edge_def fw_may.ana_CBV_def p_def fw_may.ana_init_BV_def 
              fw_may.ana_anadom_BV_def ids_def fw_may.ana_entry_node_BV_def by auto
          show ?thesis
            using p_def ids_def rhs_def meaning_cls.simps \<eta>v \<rho>'_def asm' by auto
        next
          case False
          then have False': "\<not>\<sigma>' the_\<uu> = \<lbrakk>d\<rbrakk>\<^sub>i\<^sub>d \<sigma>"
            by auto
          from yah have p_def: "p = the_CBV"
            by auto
          from yah have ids_def: "ids = [Cst\<^sub>N q', \<uu>]"
            by auto
          have rhs_def: "rhs = [\<^bold>\<not>BV[Cst\<^sub>N q', \<uu>],anadom[\<uu>]]"
            using a c_def fw_may.ana_pg_fw_may_def fw_may.ana_CBV_def p_def fw_may.ana_init_BV_def 
              fw_may.ana_anadom_BV_def fw_may.ana_kill_BV_edge_def  fw_may.ana_gen_BV_edge_def 
              ids_def fw_may.ana_entry_node_BV_def by auto

          have "\<lbrakk>CBV\<langle>[Cst\<^sub>N q', \<uu>]\<rangle> :- [\<^bold>\<not>BV[Cst\<^sub>N q', \<uu>], anadom[\<uu>]] .\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho> \<sigma>'"
            using \<open>Cls p ids rhs \<in> fw_may.ana_CBV ` UNIV\<close>  p_def rhs_def ids_def assms(1)
              least_solution_def fw_may.ana_pg_fw_may_def a c_def solves_cls_def solves_program_def
            by metis
          then have "\<lbrakk>CBV\<langle>[Cst\<^sub>N q', \<uu>]\<rangle> :- [\<^bold>\<not>BV[Cst\<^sub>N q', \<uu>], anadom[\<uu>]] .\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho>' \<sigma>'"
            unfolding \<rho>'_def using False' by force
          then show ?thesis
            unfolding p_def ids_def rhs_def by auto
        qed
      }
      moreover
      {
        assume b: "Cls p ids rhs \<in> {fw_may.ana_entry_node_BV}"
        from a c_def have "\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho> \<sigma>'"
          using assms(1)
          unfolding least_solution_def solves_program_def solves_cls_def by metis
        from b have "\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho>' \<sigma>'"
          using \<open>\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho> \<sigma>'\<close> \<rho>'_def  fw_may.ana_entry_node_BV_def by fastforce
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
    using assms(2) unfolding solves_lh.simps by auto
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
      unfolding lt_def by metis
  qed
  ultimately
  show False
    unfolding minimal_solution_def using assms(1) by auto
qed

lemma is_Cst_if_CBV:
  assumes "\<rho> \<Turnstile>\<^sub>l\<^sub>s\<^sub>t ana_pg_fw_must s_BV"
  assumes "\<rho> \<Turnstile>\<^sub>l\<^sub>h CBV\<langle>[\<pi>, d]\<rangle>."
  shows "is_Cst d"
  using is_Cst_if_anadom anadom_if_CBV assms by metis

lemma not_CBV_action: (* Copy paste adapt from not_init_node *)
  assumes "\<rho> \<Turnstile>\<^sub>l\<^sub>s\<^sub>t ana_pg_fw_must s_BV"
  shows "\<not>\<rho> \<Turnstile>\<^sub>l\<^sub>h CBV\<langle>[Cst\<^sub>A q,d]\<rangle>."
proof
  assume asm_2: "\<rho> \<Turnstile>\<^sub>l\<^sub>h CBV\<langle>[Cst\<^sub>A q,d]\<rangle>."
  then have "[Action q, the_Cst d] \<in> \<rho> the_CBV"
    using is_Cst_if_CBV[OF assms(1)] by (cases d) auto

  have "finite ana_pg_fw_must"
    using fw_may.ana_pg_fw_may_finite by auto
  then have "\<rho> \<Turnstile>\<^sub>l\<^sub>s\<^sub>t ana_pg_fw_must s_BV"
    using downward_least_solution2[of ana_pg_fw_must s_BV \<rho> 0] asm_2
    using fw_may.ana_pg_fw_may_stratified assms(1) by blast 
  then have "\<rho> \<Turnstile>\<^sub>m\<^sub>i\<^sub>n ana_pg_fw_must s_BV"
    using least_iff_minimal[of]
    using strat_wf_mod_if_strat_wf \<open>finite ana_pg_fw_must\<close> finite_below_finite
    by (smt (verit) fw_may.ana_pg_fw_may_stratified) 
  moreover

  define \<rho>' where "\<rho>' = (\<lambda>p. (if p = the_CBV then (\<rho> the_CBV) - {[Action q, the_Cst d]} else \<rho> p))"

  have "\<rho>' \<Turnstile>\<^sub>d\<^sub>l ana_pg_fw_must"
    unfolding solves_program_def
  proof
    fix c
    assume a: "c \<in> ana_pg_fw_must"
    then obtain p ids rhs where c_def: "c = Cls p ids rhs"
      by (cases c) auto

    from a have a': "c \<in> \<Union> (fw_may.ana_edge_BV ` fw_may.edge_set) \<or> 
          c \<in> (fw_may.ana_init_BV ` (analysis_dom - d_init)) \<or>
          c \<in> (fw_may.ana_anadom_BV ` analysis_dom) \<or>
          c \<in> \<Union> (fw_may.ana_kill_BV_edge ` fw_may.edge_set) \<or>
          c \<in> \<Union> (fw_may.ana_gen_BV_edge ` fw_may.edge_set) \<or>
          c \<in> fw_may.ana_CBV ` UNIV \<or>
          c \<in> {fw_may.ana_entry_node_BV}"
      unfolding fw_may.ana_pg_fw_may_def by auto

    have "\<rho>' \<Turnstile>\<^sub>c\<^sub>l\<^sub>s Cls p ids rhs"
      unfolding solves_cls_def
    proof (rule)
      fix \<sigma>' :: "var \<Rightarrow> ('n, 'v, 'd) cst"
      { 
        assume b: "Cls p ids rhs \<in> \<Union> (fw_may.ana_edge_BV ` fw_may.edge_set)"
        from a c_def have "\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho> \<sigma>'"
          using assms(1)
          unfolding least_solution_def solves_program_def solves_cls_def by metis
        from b have "\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho>' \<sigma>'"
          using \<open>\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho> \<sigma>'\<close> \<rho>'_def by auto
      }
      moreover
      {
        assume b: "Cls p ids rhs \<in> (fw_may.ana_init_BV ` (analysis_dom - d_init))"
        from a c_def have "\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho> \<sigma>'"
          using assms(1)
          unfolding least_solution_def solves_program_def solves_cls_def by metis
        from b have "\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho>' \<sigma>'"
          using \<open>\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho> \<sigma>'\<close> \<rho>'_def fw_may.ana_init_BV_def by auto
      }
      moreover
      {
        assume b: "Cls p ids rhs \<in> (fw_may.ana_anadom_BV ` analysis_dom)"
        from a c_def have "\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho> \<sigma>'"
          using assms(1)
          unfolding least_solution_def solves_program_def solves_cls_def by metis
        from b have "\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho>' \<sigma>'"
          using \<open>\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho> \<sigma>'\<close> \<rho>'_def fw_may.ana_anadom_BV_def by auto
      }
      moreover
      {
        assume b: "Cls p ids rhs \<in> \<Union> (fw_may.ana_kill_BV_edge ` fw_may.edge_set)"
        from a c_def have "\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho> \<sigma>'"
          using assms(1)
          unfolding least_solution_def solves_program_def solves_cls_def by metis
        from b have "\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho>' \<sigma>'"
          using \<open>\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho> \<sigma>'\<close> \<rho>'_def fw_may.ana_kill_BV_edge_def 
            fw_may.ana_kill_BV_edge_def by auto
      }
      moreover
      {
        assume b: "Cls p ids rhs \<in> \<Union> (fw_may.ana_gen_BV_edge ` fw_may.edge_set)"
        from a c_def have "\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho> \<sigma>'"
          using assms(1)
          unfolding least_solution_def solves_program_def solves_cls_def by metis
        from b have "\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho>' \<sigma>'"
          using \<open>\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho> \<sigma>'\<close> fw_may.ana_gen_BV_edge_def \<rho>'_def by auto
      }
      moreover
      {
        assume "Cls p ids rhs \<in> fw_may.ana_CBV ` UNIV"
        then have "\<exists>q'. p = the_CBV \<and> ids = [Cst\<^sub>N q', \<uu>]"
          unfolding fw_may.ana_CBV_def by blast
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

          have rhs_def: "rhs = [\<^bold>\<not>BV [Cst\<^sub>N q', \<uu>],anadom[\<uu>]]"
            using a c_def fw_may.ana_pg_fw_may_def fw_may.ana_CBV_def p_def fw_may.ana_init_BV_def  
             fw_may.ana_anadom_BV_def fw_may.ana_kill_BV_edge_def fw_may.ana_gen_BV_edge_def image_iff
             fw_may.ana_entry_node_BV_def ids_def by auto
          have "\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho> \<sigma>'"
            using a assms c_def least_solution_def solves_cls_def solves_program_def by blast
          then show ?thesis
            unfolding p_def ids_def rhs_def meaning_cls.simps \<eta>v \<rho>'_def by auto
        next
          case False
          then have False': "\<not>\<sigma>' the_\<uu> = the_Cst d"
            by auto
          from yah have p_def: "p = the_CBV"
            by auto
          from yah have ids_def: "ids = [Cst\<^sub>N q', \<uu>]"
            by auto
          have rhs_def: "rhs = [\<^bold>\<not>BV [Cst\<^sub>N q', \<uu>],anadom[\<uu>]]"
            using a c_def fw_may.ana_pg_fw_may_def fw_may.ana_CBV_def p_def fw_may.ana_init_BV_def 
              fw_may.ana_anadom_BV_def fw_may.ana_kill_BV_edge_def fw_may.ana_gen_BV_edge_def 
              fw_may.ana_entry_node_BV_def ids_def by auto 

          have "\<lbrakk>CBV\<langle>[Cst\<^sub>N q', \<uu>]\<rangle> :- [\<^bold>\<not>BV [Cst\<^sub>N q', \<uu>], anadom [\<uu>]] .\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho> \<sigma>'"
            using \<open>Cls p ids rhs \<in> fw_may.ana_CBV ` UNIV\<close>
            unfolding p_def[symmetric] rhs_def[symmetric] 
            unfolding ids_def[symmetric]
            using assms(1)
            unfolding least_solution_def
            unfolding fw_may.ana_pg_fw_may_def
            by (meson Un_iff solves_cls_def solves_program_def)
          then have "\<lbrakk>CBV\<langle>[Cst\<^sub>N q', \<uu>]\<rangle> :- [\<^bold>\<not>BV [Cst\<^sub>N q', \<uu>], anadom [\<uu>]] .\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho>' \<sigma>'"
            unfolding \<rho>'_def 
            by auto
          then show ?thesis
            unfolding p_def ids_def rhs_def by auto
        qed
      }
      moreover
      {
        assume b: "Cls p ids rhs \<in> {fw_may.ana_entry_node_BV}"
        from a c_def have "\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho> \<sigma>'"
          using assms(1)
          unfolding least_solution_def solves_program_def solves_cls_def by metis
        from b have "\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho>' \<sigma>'"
          using \<open>\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho> \<sigma>'\<close> \<rho>'_def fw_may.ana_entry_node_BV_def by fastforce
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
      unfolding \<rho>'_def using \<open>[Action q, id.the_Cst d] \<in> \<rho> the_CBV\<close> by auto
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
  assumes "\<rho> \<Turnstile>\<^sub>l\<^sub>h CBV\<langle>[\<pi>_end, d]\<rangle>."
  shows "\<exists>d'. d = Cst\<^sub>E d'"
proof -
  have "\<rho> \<Turnstile>\<^sub>l\<^sub>h anadom\<langle>[d]\<rangle>."
    using assms(1) assms(2) anadom_if_CBV[of \<rho> \<pi>_end d] by fastforce
  thm not_init_action
  show ?thesis

    by (metis cst.exhaust \<open>\<rho> \<Turnstile>\<^sub>l\<^sub>h anadom\<langle>[d]\<rangle>.\<close> assms(1) is_Cst_def not_anadom_action is_Cst_if_anadom not_anadom_node)
qed

lemma not_Ccst: (* Copy paste adapt from not_init_node *)
  assumes "\<rho> \<Turnstile>\<^sub>l\<^sub>s\<^sub>t ana_pg_fw_must s_BV"
  shows "\<not>\<rho> \<Turnstile>\<^sub>l\<^sub>h CBV\<langle>[Cst\<^sub>E q,d]\<rangle>."
proof
  assume asm_2: "\<rho> \<Turnstile>\<^sub>l\<^sub>h CBV\<langle>[Cst\<^sub>E q,d]\<rangle>."
  then have "[Elem q, the_Cst d] \<in> \<rho> the_CBV"
    using is_Cst_if_CBV[OF assms(1)] by (cases d) auto

  have "finite ana_pg_fw_must"
    using fw_may.ana_pg_fw_may_finite by auto
  then have "\<rho> \<Turnstile>\<^sub>l\<^sub>s\<^sub>t ana_pg_fw_must s_BV"
    using downward_least_solution2[of ana_pg_fw_must s_BV \<rho> 0] asm_2
    using fw_may.ana_pg_fw_may_stratified assms(1) by blast 
  then have "\<rho> \<Turnstile>\<^sub>m\<^sub>i\<^sub>n ana_pg_fw_must s_BV"
    using least_iff_minimal[of]
    using strat_wf_mod_if_strat_wf  \<open>finite ana_pg_fw_must\<close> finite_below_finite
    by (smt (verit) fw_may.ana_pg_fw_may_stratified) 
  moreover

  define \<rho>' where "\<rho>' = (\<lambda>p. (if p = the_CBV then (\<rho> the_CBV) - {[Elem q, the_Cst d]} else \<rho> p))"

  have "\<rho>' \<Turnstile>\<^sub>d\<^sub>l ana_pg_fw_must"
    unfolding solves_program_def
  proof
    fix c
    assume a: "c \<in> ana_pg_fw_must"
    then obtain p ids rhs where c_def: "c = Cls p ids rhs"
      by (cases c) auto

    from a have a': "c \<in> \<Union> (fw_may.ana_edge_BV ` fw_may.edge_set) \<or> 
          c \<in> (fw_may.ana_init_BV ` (analysis_dom - d_init)) \<or>
          c \<in> (fw_may.ana_anadom_BV ` (analysis_dom)) \<or>
          c \<in> \<Union> (fw_may.ana_kill_BV_edge ` fw_may.edge_set) \<or>
          c \<in> \<Union> (fw_may.ana_gen_BV_edge ` fw_may.edge_set) \<or>
          c \<in> fw_may.ana_CBV ` UNIV \<or>
          c \<in> {fw_may.ana_entry_node_BV}"
      unfolding fw_may.ana_pg_fw_may_def by auto

    have "\<rho>' \<Turnstile>\<^sub>c\<^sub>l\<^sub>s Cls p ids rhs"
      unfolding solves_cls_def
    proof (rule)
      fix \<sigma>' :: "var \<Rightarrow> ('n, 'v, 'd) cst"
      { 
        assume b: "Cls p ids rhs \<in> \<Union> (fw_may.ana_edge_BV ` fw_may.edge_set)"
        from a c_def have "\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho> \<sigma>'"
          using assms(1)
          unfolding least_solution_def solves_program_def solves_cls_def by metis
        from b have "\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho>' \<sigma>'"
          using \<open>\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho> \<sigma>'\<close> \<rho>'_def by auto
      }
      moreover
      {
        assume b: "Cls p ids rhs \<in> (fw_may.ana_init_BV ` (analysis_dom - d_init))"
        from a c_def have "\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho> \<sigma>'"
          using assms(1)
          unfolding least_solution_def solves_program_def solves_cls_def by metis
        from b have "\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho>' \<sigma>'"
          using \<open>\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho> \<sigma>'\<close> \<rho>'_def fw_may.ana_init_BV_def by auto
      }
      moreover
      {
        assume b: "Cls p ids rhs \<in> (fw_may.ana_anadom_BV ` analysis_dom)"
        from a c_def have "\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho> \<sigma>'"
          using assms(1)
          unfolding least_solution_def solves_program_def solves_cls_def by metis
        from b have "\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho>' \<sigma>'"
          using \<open>\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho> \<sigma>'\<close> \<rho>'_def fw_may.ana_anadom_BV_def by auto
      }
      moreover
      {
        assume b: "Cls p ids rhs \<in> \<Union> (fw_may.ana_kill_BV_edge ` fw_may.edge_set)"
        from a c_def have "\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho> \<sigma>'"
          using assms(1)
          unfolding least_solution_def solves_program_def solves_cls_def by metis
        from b have "\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho>' \<sigma>'"
          using \<open>\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho> \<sigma>'\<close> \<rho>'_def fw_may.ana_kill_BV_edge_def 
            fw_may.ana_kill_BV_edge_def by auto
      }
      moreover
      {
        assume b: "Cls p ids rhs \<in> \<Union> (fw_may.ana_gen_BV_edge ` fw_may.edge_set)"
        from a c_def have "\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho> \<sigma>'"
          using assms(1)
          unfolding least_solution_def solves_program_def solves_cls_def by metis
        from b have "\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho>' \<sigma>'"
          using \<open>\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho> \<sigma>'\<close> \<rho>'_def fw_may.ana_gen_BV_edge_def by auto
      }
      moreover
      {
        assume "Cls p ids rhs \<in> fw_may.ana_CBV ` UNIV"
        then have "\<exists>q'. p = the_CBV \<and> ids = [Cst\<^sub>N q', \<uu>]"
          unfolding fw_may.ana_CBV_def by blast
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

          have rhs_def: "rhs = [\<^bold>\<not>BV [Cst\<^sub>N q', \<uu>],anadom[\<uu>]]"
            using a c_def  fw_may.ana_pg_fw_may_def fw_may.ana_CBV_def p_def fw_may.ana_init_BV_def  
              fw_may.ana_anadom_BV_def fw_may.ana_kill_BV_edge_def fw_may.ana_gen_BV_edge_def 
              fw_may.ana_entry_node_BV_def ids_def by auto
          have "\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho> \<sigma>'"
            using a assms c_def least_solution_def solves_cls_def solves_program_def by blast
          then show ?thesis
            unfolding p_def ids_def rhs_def meaning_cls.simps \<eta>v \<rho>'_def by auto
        next
          case False
          then have False': "\<not>\<sigma>' the_\<uu> = the_Cst d"
            by auto
          from yah have p_def: "p = the_CBV"
            by auto
          from yah have ids_def: "ids = [Cst\<^sub>N q', \<uu>]"
            by auto
          have rhs_def: "rhs = [\<^bold>\<not>BV [Cst\<^sub>N q', \<uu>],anadom[\<uu>]]"
            using a c_def  fw_may.ana_pg_fw_may_def fw_may.ana_CBV_def p_def fw_may.ana_init_BV_def  
             fw_may.ana_anadom_BV_def fw_may.ana_kill_BV_edge_def fw_may.ana_gen_BV_edge_def 
             fw_may.ana_entry_node_BV_def ids_def by auto

          have "\<lbrakk>CBV\<langle>[Cst\<^sub>N q', \<uu>]\<rangle> :- [\<^bold>\<not>BV [Cst\<^sub>N q', \<uu>], anadom[\<uu>]] .\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho> \<sigma>'"
            using \<open>Cls p ids rhs \<in> fw_may.ana_CBV ` UNIV\<close>
            unfolding p_def[symmetric] rhs_def[symmetric] 
            unfolding ids_def[symmetric]
            using assms(1)
            unfolding least_solution_def
            unfolding fw_may.ana_pg_fw_may_def
            by (meson Un_iff solves_cls_def solves_program_def)
          then have "\<lbrakk>CBV\<langle>[Cst\<^sub>N q', \<uu>]\<rangle> :- [\<^bold>\<not>BV [Cst\<^sub>N q', \<uu>], anadom[\<uu>]] .\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho>' \<sigma>'"
            unfolding \<rho>'_def by auto
          then show ?thesis
            unfolding p_def ids_def rhs_def by auto
        qed
      }
      moreover
      {
        assume b: "Cls p ids rhs \<in> {fw_may.ana_entry_node_BV}"
        from a c_def have "\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho> \<sigma>'"
          using assms(1)
          unfolding least_solution_def solves_program_def solves_cls_def by metis
        from b have "\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho>' \<sigma>'"
          using \<open>\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho> \<sigma>'\<close> \<rho>'_def fw_may.ana_entry_node_BV_def by fastforce  
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
      unfolding \<rho>'_def using \<open>[Elem q, id.the_Cst d] \<in> \<rho> the_CBV\<close> by auto
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
thm not_Ccst

lemma is_Cst_if_CBV_left_arg:
  assumes "\<rho> \<Turnstile>\<^sub>l\<^sub>s\<^sub>t ana_pg_fw_must s_BV"
  assumes "\<rho> \<Turnstile>\<^sub>l\<^sub>h CBV\<langle>[q,d]\<rangle>."
  shows "is_Cst q"
proof (cases q)
  case (Var x)
  obtain d' where "d = Cst\<^sub>E d'"
    using assms is_encode_elem_if_CBV_right_arg by blast 

  then have "\<rho> \<Turnstile>\<^sub>l\<^sub>h CBV\<langle>[Var x, Cst\<^sub>E d']\<rangle>."
    using Var assms(2) by auto
  then have "\<forall>\<sigma>. \<lbrakk>CBV\<langle>[Var x, Cst\<^sub>E d']\<rangle>.\<rbrakk>\<^sub>l\<^sub>h \<rho> \<sigma>"
    unfolding solves_lh.simps by auto
  have "\<rho> \<Turnstile>\<^sub>l\<^sub>h CBV\<langle>[Cst\<^sub>E undefined,Cst\<^sub>E d']\<rangle>."
    unfolding solves_lh.simps 
  proof 
    fix \<sigma> :: "var \<Rightarrow> ('n, 'v, 'd) cst"
    define \<sigma>' where "\<sigma>' = (\<lambda>y. if y = x then Elem undefined else \<sigma> y)"
    have "\<lbrakk>CBV\<langle>[Var x, Cst\<^sub>E d']\<rangle>.\<rbrakk>\<^sub>l\<^sub>h \<rho> \<sigma>'"
      using \<open>\<forall>\<sigma>. \<lbrakk>CBV\<langle>[Var x, Cst\<^sub>E d']\<rangle>.\<rbrakk>\<^sub>l\<^sub>h \<rho> \<sigma>\<close> by blast
    then show "\<lbrakk>CBV\<langle>[Cst\<^sub>E undefined, Cst\<^sub>E d']\<rangle>.\<rbrakk>\<^sub>l\<^sub>h \<rho> \<sigma>"
      unfolding \<sigma>'_def by auto
  qed
  then have "False"
    using assms(1) not_Ccst by blast
  then show ?thesis 
    by metis
next
  case (Cst e)
  then show ?thesis 
    by auto
qed

lemma is_encode_node_if_CBV_left_arg:
  assumes "\<rho> \<Turnstile>\<^sub>l\<^sub>s\<^sub>t ana_pg_fw_must s_BV"
  assumes "\<rho> \<Turnstile>\<^sub>l\<^sub>h CBV\<langle>[q, d]\<rangle>."
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
        using not_Ccst[OF assms(1), of d' d]
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
  assumes "\<rho> \<Turnstile>\<^sub>l\<^sub>h CBV\<langle>[\<pi>_end, d]\<rangle>."
  shows "Decode_Elem d \<in> analysis_dom"
  using anadom_if_CBV
  using assms in_analysis_dom_if_anadom by blast
(* Note -- many of those similar init lemmas are not used anymore. *)

lemma sound_ana_pg_fw_must':
  assumes "\<rho> \<Turnstile>\<^sub>l\<^sub>s\<^sub>t ana_pg_fw_must s_BV"
  assumes "\<rho> \<Turnstile>\<^sub>l\<^sub>h CBV\<langle>[\<pi>_end, d]\<rangle>."
  assumes "\<pi> \<in> LTS.path_with_word edge_set"
  assumes "LTS.get_start \<pi> = start"
  assumes "LTS.get_end \<pi> = Decode_Node \<pi>_end"
  shows "Decode_Elem d \<in> Ŝ\<^sub>P\<lbrakk>\<pi>\<rbrakk> d_init"
proof -
  have d_ana: "Decode_Elem d \<in> analysis_dom"
    using assms(1) assms(2) in_analysis_dom_if_CBV by auto

  have \<pi>e: "\<pi>_end = Cst\<^sub>N (LTS.get_end \<pi>)"
    by (smt (verit, best) cst.collapse(1) cst.collapse(3) cst.disc(6) cst.distinct(1) cst.distinct(3) 
        cst.expand assms(1) assms(2) assms(5) id.sel(2) is_elem_def is_encode_node_if_CBV_left_arg)

  have d_encdec: "d = Cst\<^sub>E (Decode_Elem d)"
    by (metis cst.sel(2) assms(1) assms(2) id.sel(2) is_encode_elem_if_CBV_right_arg)

  have m: "\<not> \<rho> \<Turnstile>\<^sub>l\<^sub>h BV\<langle>[Cst\<^sub>N (LTS.get_end \<pi>), d]\<rangle>."
    using not_CBV2[OF assms(1), of "(LTS.get_end \<pi>)" "Decode_Elem d"] assms(2) \<pi>e d_encdec by force
  have "\<not>Decode_Elem d \<in> fw_may.S_hat_path \<pi> (analysis_dom - d_init)"
    using fw_may.sound_ana_pg_fw_may assms(1)
    unfolding fw_may.summarizes_fw_may_def
     fw_may.edge_set_def fw_may.start_def assms(2) assms(4) assms(5) edge_set_def m start_def
    using assms(3) assms(4) d_encdec edge_set_def m start_def by (metis (mono_tags) mem_Collect_eq) 
  then show "Decode_Elem d \<in> Ŝ\<^sub>P\<lbrakk>\<pi>\<rbrakk> d_init"
    using opposite_lemma2
    using assms(1)
    using d_ana by blast 
qed

theorem sound_ana_pg_fw_must:
  assumes "\<rho> \<Turnstile>\<^sub>l\<^sub>s\<^sub>t ana_pg_fw_must s_BV"
  shows "summarizes_fw_must \<rho>"
  using assms unfolding summarizes_fw_must_def using sound_ana_pg_fw_must' by auto

end

section \<open>Available Expressions\<close>

fun ae_arith :: "'v arith \<Rightarrow> 'v arith set" where
  "ae_arith (Integer i) = {}"
| "ae_arith (Arith_Var v) = {}"
| "ae_arith (Arith_Op a1 opr a2) = ae_arith a1 \<union> ae_arith a1 \<union> {Arith_Op a1 opr a2}"
| "ae_arith (Minus a) = ae_arith a"

lemma finite_ae_arith: "finite (ae_arith a)"
  by (induction a) auto

fun ae_boolean :: "'v boolean \<Rightarrow> 'v arith set" where
  "ae_boolean true = {}"
| "ae_boolean false = {}"
| "ae_boolean (Rel_Op a1 opr a2) = ae_arith a1 \<union> ae_arith a2"
| "ae_boolean (Bool_Op b1 opr b2) = ae_boolean b1 \<union> ae_boolean b2"
| "ae_boolean (Neg b) = ae_boolean b"

lemma finite_ae_boolean: "finite (ae_boolean b)"
  using finite_ae_arith by (induction b) auto

fun aexp_action :: "'v action \<Rightarrow> 'v arith set" where
  "aexp_action (x ::= a) = ae_arith a"
| "aexp_action (Bool b) = ae_boolean b"
| "aexp_action Skip = {}"

lemma finite_aexp_action: "finite (aexp_action \<alpha>)"
  using finite_ae_arith finite_ae_boolean by (cases \<alpha>) auto

fun aexp_edge :: "('n,'v) edge \<Rightarrow> 'v arith set" where
  "aexp_edge (q1, \<alpha>, q2) = aexp_action \<alpha>"

lemma finite_aexp_edge: "finite (aexp_edge (q1, \<alpha>, q2))"
  using finite_aexp_action by auto

fun aexp_pg :: "('n,'v) program_graph \<Rightarrow> 'v arith set" where
  "aexp_pg pg = \<Union>(aexp_edge ` (fst pg))"

definition aexp_edge_list :: "('n,'v) edge list \<Rightarrow> 'v arith \<Rightarrow> bool" where
  "aexp_edge_list \<pi> a = (\<exists>\<pi>1 \<pi>2 e. \<pi> = \<pi>1 @ [e] @ \<pi>2 \<and> a \<in> aexp_edge e \<and> (\<forall>e' \<in> set ([e] @ \<pi>2). fv_arith a \<inter> def_edge e' = {}))"

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

interpretation fw_must: analysis_BV_forward_must pg analysis_dom_AE kill_set_AE gen_set_AE d_init_AE
  using analysis_BV_forward_must.intro analysis_AE_axioms analysis_AE_def
  by (metis d_init_AE_def empty_iff finite_analysis_dom_AE subsetI) 

lemma aexp_edge_list_S_hat_edge_list: 
  assumes "a \<in> aexp_edge (q, \<alpha>, q')"
  assumes "fv_arith a \<inter> def_edge (q, \<alpha>, q') = {}"
  shows "a \<in> fw_must.S_hat (q, \<alpha>, q') R"
  using assms unfolding fw_must.S_hat_def by (cases \<alpha>) auto

lemma empty_inter_fv_arith_def_edge:
  assumes "aexp_edge_list (\<pi> @ [e]) a"
  shows "fv_arith a \<inter> def_edge e = {}"
proof -
  from assms(1) obtain \<pi>1 \<pi>2 e' where \<pi>1_\<pi>2_e'_p:
    "\<pi> @ [e] = \<pi>1 @ [e'] @ \<pi>2" 
    "a \<in> aexp_edge e'"
    "(\<forall>e''\<in>set ([e'] @ \<pi>2). fv_arith a \<inter> def_edge e'' = {})"
    unfolding aexp_edge_list_def by auto
  from this(1) have "e \<in> set ([e'] @ \<pi>2)"
    by (metis append_is_Nil_conv last_appendR last_in_set snoc_eq_iff_butlast) 
  then show "fv_arith a \<inter> def_edge e = {}"
    using \<pi>1_\<pi>2_e'_p(3) by auto
qed

lemma aexp_edge_list_append_singleton:
  assumes "aexp_edge_list (\<pi> @ [e]) a"
  shows "aexp_edge_list \<pi> a \<or> a \<in> aexp_edge e"
proof -
  from assms(1) obtain \<pi>1 \<pi>2 e' where \<pi>1_\<pi>2_e'_p:
    "\<pi> @ [e] = \<pi>1 @ [e'] @ \<pi>2" 
    "a \<in> aexp_edge e'"
    "(\<forall>e''\<in>set ([e'] @ \<pi>2). fv_arith a \<inter> def_edge e'' = {})"
    unfolding aexp_edge_list_def by auto
  from this(1) have "e \<in> set ([e'] @ \<pi>2)"
    by (metis append_is_Nil_conv last_appendR last_in_set snoc_eq_iff_butlast)
  then have "e = e' \<or> e \<in> set \<pi>2"
    by auto
  then show ?thesis
  proof
    assume "e = e'"
    then have "a \<in> aexp_edge e"
      using \<pi>1_\<pi>2_e'_p by auto
    then show ?thesis 
      by auto
  next
    assume "e \<in> set \<pi>2"
    have "\<pi> = \<pi>1 @ [e'] @ (butlast \<pi>2)"
      by (metis \<open>e \<in> set \<pi>2\<close> \<pi>1_\<pi>2_e'_p(1) append_is_Nil_conv butlast_append butlast_snoc in_set_conv_decomp_first)
    moreover
    have "a \<in> aexp_edge e'"
      by (simp add: \<pi>1_\<pi>2_e'_p(2))
    moreover
    have "(\<forall>e''\<in>set ([e'] @ butlast \<pi>2). fv_arith a \<inter> def_edge e'' = {})"
      by (metis \<pi>1_\<pi>2_e'_p(3) butlast.simps(1) butlast_append in_set_butlastD)
    ultimately
    have "aexp_edge_list \<pi> a"
      unfolding aexp_edge_list_def by blast
    then show ?thesis
      by auto
  qed
qed

lemma gen_set_AE_subset_aexp_edge:
  assumes "a \<in> gen_set_AE e"
  shows "a \<in> aexp_edge e"
  using assms
  apply (cases e)
  apply auto
  subgoal for q \<alpha> q'
    apply (cases \<alpha>)
      apply auto
    done
  done

lemma empty_inter_fv_arith_def_edge':
  assumes "a \<in> gen_set_AE e"
  shows "fv_arith a \<inter> def_edge e = {}"
  using assms
  apply (cases e)
  apply auto
  subgoal for q \<alpha> q'
    apply (cases \<alpha>)
      apply auto
    done
  done

lemma empty_inter_fv_arith_def_edge'':
  assumes "a \<notin> kill_set_AE e"
  shows "fv_arith a \<inter> def_edge e = {}"
  using assms
  apply (cases e)
  apply auto
  subgoal for q \<alpha> q'
    apply (cases \<alpha>)
      apply auto
    done
  done


lemma S_hat_edge_list_aexp_edge_list: 
  assumes "a \<in> fw_must.S_hat_edge_list \<pi> d_init_AE"
  shows "aexp_edge_list \<pi> a"
  using assms 
proof (induction \<pi> rule: rev_induct)
  case Nil
  then show ?case 
    unfolding d_init_AE_def by auto
next
  case (snoc e \<pi>)
  from snoc(2) have "a \<in> (fw_must.S_hat_edge_list \<pi> d_init_AE - kill_set_AE e) \<or> a \<in> gen_set_AE e"
    using fw_must.S_hat_def by auto
  then show ?case
  proof 
    assume a_S_hat: "a \<in> fw_must.S_hat_edge_list \<pi> d_init_AE - kill_set_AE e"
    then have "aexp_edge_list \<pi> a"
      using snoc by auto
    moreover
    from a_S_hat have "a \<notin> kill_set_AE e"
      by auto
    then have "fv_arith a \<inter> def_edge e = {}"
      using empty_inter_fv_arith_def_edge'' by auto
    ultimately show "aexp_edge_list (\<pi> @ [e]) a"
      unfolding aexp_edge_list_def by force
  next
    assume a_gen: "a \<in> gen_set_AE e"
    then have "a \<in> aexp_edge e"
      using gen_set_AE_subset_aexp_edge by auto
    moreover
    from a_gen have "(fv_arith a \<inter> def_edge e = {})"
      using empty_inter_fv_arith_def_edge' by auto
    ultimately
    show "aexp_edge_list (\<pi> @ [e]) a"
      unfolding aexp_edge_list_def
      by (metis append_Nil2 empty_iff empty_set insert_iff list.set(2)) 
  qed
qed

lemma aexp_edge_list_S_hat_edge_list': 
  assumes "aexp_edge_list \<pi> a"
  shows "a \<in> fw_must.S_hat_edge_list \<pi> d_init_AE"
  using assms
proof (induction \<pi> rule: rev_induct)
  case Nil
  then have False 
    unfolding aexp_edge_list_def by auto
  then show ?case
    by metis
next
  case (snoc e \<pi>)
  have fva: "fv_arith a \<inter> def_edge e = {}"
    using snoc(2) empty_inter_fv_arith_def_edge by metis

  have "aexp_edge_list \<pi> a \<or> a \<in> aexp_edge e"
    using snoc(2)
    by (simp add: aexp_edge_list_append_singleton)
  then show ?case
  proof
    assume "aexp_edge_list \<pi> a"
    then have "a \<in> fw_must.S_hat_edge_list \<pi> d_init_AE"
      using snoc by auto
    moreover
    have "a \<notin> kill_set_AE e"
      using fva apply (cases e) subgoal for q \<alpha> q' 
        apply (cases \<alpha>)
          apply auto
        done (* extract lemma *)
      done
    ultimately
    show ?case
      using fw_must.S_hat_def by auto
  next
    assume "a \<in> aexp_edge e"
    then have "a \<in> gen_set_AE e"
      using fva
      apply (cases e) subgoal for q \<alpha> q' 
        apply (cases \<alpha>)
          apply auto
        done (* extract lemma *)
      done
    then show ?case
      using fw_must.S_hat_def by auto
  qed
qed

lemma aexp_edge_list_S_hat_edge_list_iff: 
  "aexp_edge_list \<pi> a \<longleftrightarrow> a \<in> fw_must.S_hat_edge_list \<pi> d_init_AE"
  using S_hat_edge_list_aexp_edge_list aexp_edge_list_S_hat_edge_list' by blast

lemma aexp_path_S_hat_path_iff: 
  "a \<in> aexp_path \<pi> \<longleftrightarrow> a \<in> fw_must.S_hat_path \<pi> d_init_AE"
  using S_hat_edge_list_aexp_edge_list aexp_edge_list_S_hat_edge_list' aexp_path_def fw_must.S_hat_path_def by blast

definition summarizes_AE :: "(pred, ('n, 'a, 'v arith) cst) pred_val \<Rightarrow> bool" where
   "summarizes_AE \<rho> \<longleftrightarrow>
     (\<forall>\<pi>_end d.
         \<rho> \<Turnstile>\<^sub>l\<^sub>h CBV\<langle>[\<pi>_end, d]\<rangle>. \<longrightarrow>
          (\<forall>\<pi>. \<pi> \<in> LTS.path_with_word edge_set \<longrightarrow> LTS.get_start \<pi> = start \<longrightarrow> LTS.get_end \<pi> = Decode_Node \<pi>_end \<longrightarrow> (Decode_Elem d) \<in> aexp_path \<pi> ))"

theorem AE_sound:
  assumes "\<rho> \<Turnstile>\<^sub>l\<^sub>s\<^sub>t (fw_must.ana_pg_fw_must) s_BV"
  shows "summarizes_AE \<rho>"
proof -
  from assms have "fw_must.summarizes_fw_must \<rho>"
    using fw_must.sound_ana_pg_fw_must by auto
  then show ?thesis
    unfolding summarizes_AE_def fw_must.summarizes_fw_must_def fw_must.edge_set_def edge_set_def
      fw_must.end_def end_def aexp_path_S_hat_path_iff fw_must.start_def start_def by force
qed

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

definition S_hat :: "('n,'v) edge \<Rightarrow> 'd set \<Rightarrow> 'd set" ("Ŝ\<^sub>E\<lbrakk>_\<rbrakk> _") where (* Copy paste *)
  "Ŝ\<^sub>E\<lbrakk>e\<rbrakk> R = (R - kill_set e) \<union> gen_set e"

lemma S_hat_mono: (* Copy paste *)
  assumes "R1 \<subseteq> R2"
  shows "Ŝ\<^sub>E\<lbrakk>e\<rbrakk> R1 \<subseteq> Ŝ\<^sub>E\<lbrakk>e\<rbrakk> R2"
  using assms unfolding S_hat_def by auto

fun S_hat_edge_list :: "('n,'v) edge list \<Rightarrow> 'd set \<Rightarrow> 'd set" ("Ŝ\<^sub>E\<^sub>s\<lbrakk>_\<rbrakk> _") where (* Copy paste *)
  "Ŝ\<^sub>E\<^sub>s\<lbrakk>[]\<rbrakk> R = R" |
  "Ŝ\<^sub>E\<^sub>s\<lbrakk>(e # \<pi>)\<rbrakk> R = Ŝ\<^sub>E\<lbrakk>e\<rbrakk> (Ŝ\<^sub>E\<^sub>s\<lbrakk>\<pi>\<rbrakk> R)"

lemma S_hat_edge_list_def2: (* Copy paste *)
  "Ŝ\<^sub>E\<^sub>s\<lbrakk>\<pi>\<rbrakk> R = foldr S_hat \<pi> R"
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
  "Ŝ\<^sub>E\<^sub>s\<lbrakk>xs @ ys\<rbrakk> R = Ŝ\<^sub>E\<^sub>s\<lbrakk>xs\<rbrakk> (Ŝ\<^sub>E\<^sub>s\<lbrakk>ys\<rbrakk> R)"
  unfolding S_hat_edge_list_def2 foldl_append by auto

lemma S_hat_edge_list_mono: (* Copy paste *)
  assumes "R1 \<subseteq> R2"
  shows "Ŝ\<^sub>E\<^sub>s\<lbrakk>\<pi>\<rbrakk> R1 \<subseteq> Ŝ\<^sub>E\<^sub>s\<lbrakk>\<pi>\<rbrakk> R2"
proof(induction \<pi>)
  case Nil
  then show ?case
    using assms by auto
next
  case (Cons x xs)
  then show ?case
    using assms by (simp add: S_hat_mono)
qed

definition S_hat_path :: "('n list \<times> 'v action list) \<Rightarrow> 'd set \<Rightarrow> 'd set" ("Ŝ\<^sub>P\<lbrakk>_\<rbrakk> _") where (* Copy paste *)
  "Ŝ\<^sub>P\<lbrakk>\<pi>\<rbrakk> R = Ŝ\<^sub>E\<^sub>s\<lbrakk>LTS.transition_list \<pi>\<rbrakk> R"

definition summarizes_bw_must :: "(pred, ('n, 'v, 'd) cst) pred_val \<Rightarrow> bool" where (* Ny *)
   "summarizes_bw_must \<rho> \<longleftrightarrow>
     (\<forall>\<pi>_start d.
         \<rho> \<Turnstile>\<^sub>l\<^sub>h CBV\<langle>[\<pi>_start, d]\<rangle>. \<longrightarrow>
          (\<forall>\<pi>. \<pi> \<in> LTS.path_with_word edge_set \<longrightarrow> LTS.get_end \<pi> = end \<longrightarrow> LTS.get_start \<pi> = Decode_Node \<pi>_start \<longrightarrow> Decode_Elem d \<in> Ŝ\<^sub>P\<lbrakk>\<pi>\<rbrakk> d_init))"

lemma finite_pg_rev: "finite (fst pg_rev)" (* Copy paste *)
  by (metis analysis_BV_backward_must_axioms analysis_BV_backward_must_def edge_set_def finite_imageI fst_conv pg_rev_def)

interpretation fw_must: analysis_BV_forward_must pg_rev analysis_dom "\<lambda>e. (kill_set (rev_edge e))" "(\<lambda>e. gen_set (rev_edge e))" d_init
  using analysis_BV_forward_must_def finite_pg_rev
  by (metis analysis_BV_backward_must_axioms analysis_BV_backward_must_def) 

abbreviation ana_pg_bw_must where (* Copy paste *)
  "ana_pg_bw_must == fw_must.ana_pg_fw_must"

lemma rev_end_is_start: (* Copy paste *)
  assumes "ss \<noteq> []"
  assumes "LTS.get_end (ss, w) = end"
  shows "LTS.get_start (rev ss, rev w) = fw_must.start"
  using assms
  unfolding LTS.get_end_def LTS.get_start_def fw_must.start_def pg_rev_def fw_must.start_def
  using hd_rev by (metis fw_must.start_def fst_conv pg_rev_def snd_conv) 

lemma S_hat_edge_list_forward_backward: (* Copy paste *)
  "Ŝ\<^sub>E\<^sub>s\<lbrakk>ss\<rbrakk> d_init = fw_must.S_hat_edge_list (rev_edge_list ss) d_init"
proof (induction ss)
  case Nil
  then show ?case
    unfolding rev_edge_list_def by auto
next
  case (Cons a ss)
  show ?case
    unfolding rev_edge_list_def
    unfolding fw_must.S_hat_edge_list_def2
    unfolding foldl_conv_foldr
    apply simp
    unfolding foldr_conv_foldl
    unfolding fw_must.S_hat_edge_list_def2[symmetric]
    unfolding rev_edge_list_def[symmetric]
    unfolding fw_must.S_hat_def
    apply (simp only: rev_edge_rev_edge_id)
    unfolding S_hat_def
    using Cons
    apply metis
    done
qed

lemma S_hat_path_forward_backward: (* Copy paste *)
  assumes "(ss,w) \<in> LTS.path_with_word edge_set"
  shows "Ŝ\<^sub>P\<lbrakk>(ss, w)\<rbrakk> d_init = fw_must.S_hat_path (rev ss, rev w) d_init"
  using S_hat_edge_list_forward_backward unfolding S_hat_path_def fw_must.S_hat_path_def
  by (metis transition_list_rev_edge_list assms)

lemma summarizes_fw_must_forward_backward':
  assumes "fw_must.summarizes_fw_must \<rho>"
  assumes "\<rho> \<Turnstile>\<^sub>l\<^sub>h CBV\<langle>[\<pi>_start, d]\<rangle>."
  assumes "\<pi> \<in> LTS.path_with_word edge_set"
  assumes "LTS.get_end \<pi> = end"
  assumes "LTS.get_start \<pi> = Decode_Node \<pi>_start"
  shows "Decode_Elem d \<in> Ŝ\<^sub>P\<lbrakk>\<pi>\<rbrakk> d_init"
  using LTS.get_end_def LTS.get_start_def S_hat_path_forward_backward 
    analysis_BV_backward_must_axioms assms fw_must.start_def fw_must.summarizes_fw_must_def fst_conv 
    hd_rev last_rev pg_rev_def rev_path_in_rev_pg snd_conv fw_must.edge_set_def prod.collapse 
  by (metis (no_types, lifting))
    (* TODO? Expand proof into something coherent? *)

lemma summarizes_bw_must_forward_backward: (* Copy paste statement by adapted proof *)
  assumes "fw_must.summarizes_fw_must \<rho>"
  shows "summarizes_bw_must \<rho>"
  unfolding summarizes_bw_must_def
proof(rule; rule ; rule ;rule ;rule; rule; rule)
  fix \<pi>_start d \<pi>
  assume "\<rho> \<Turnstile>\<^sub>l\<^sub>h CBV\<langle>[\<pi>_start, d]\<rangle>."
  moreover
  assume "\<pi> \<in> LTS.path_with_word edge_set"
  moreover
  assume "LTS.get_end \<pi> = end"
  moreover
  assume "LTS.get_start \<pi> = Decode_Node \<pi>_start"
  ultimately
  show "Decode_Elem d \<in> Ŝ\<^sub>P\<lbrakk>\<pi>\<rbrakk> d_init"
    by (metis assms summarizes_fw_must_forward_backward')
qed

theorem sound_ana_pg_bw_must:
  assumes "\<rho> \<Turnstile>\<^sub>l\<^sub>s\<^sub>t ana_pg_bw_must s_BV"
  shows "summarizes_bw_must \<rho>"
  using assms fw_must.sound_ana_pg_fw_must[of \<rho>] summarizes_bw_must_forward_backward by metis



(* 

Plan:
Forstå hvordan du 

FORWARD MAY:
fun summarizes_dl_BV :: "(pred, ('n, 'v, 'd) cst) pred_val \<Rightarrow> bool" where
  "summarizes_dl_BV \<rho> \<longleftrightarrow> 
     (\<forall>\<pi> d. \<pi> \<in> LTS.path_with_word edge_set \<longrightarrow> LTS.get_start \<pi> = start \<longrightarrow> d \<in> Ŝ\<^sub>P\<lbrakk> \<pi> d_init \<longrightarrow> 
        \<rho> \<Turnstile>\<^sub>l\<^sub>h (BV\<langle>[Cst\<^sub>N (LTS.get_end \<pi>), Cst\<^sub>E d]\<rangle>.))"


BACKWARD MAY:
definition summarizes_dl_BV :: "(pred, ('n, 'v, 'd) cst) pred_val \<Rightarrow> bool" where
  "summarizes_dl_BV \<rho> \<longleftrightarrow> 
     (\<forall>\<pi> d. \<pi> \<in> LTS.path_with_word edge_set \<longrightarrow> LTS.get_end \<pi> = end \<longrightarrow> d \<in> Ŝ\<^sub>P\<lbrakk> \<pi> d_init \<longrightarrow> 
                             \<rho> \<Turnstile>\<^sub>l\<^sub>h BV\<langle>[Cst\<^sub>N (LTS.get_start \<pi>), Cst\<^sub>E d]\<rangle>.)"

FORWARD MUST:
fun summarizes_dl_BV_must :: "(pred, ('n, 'v, 'd) cst) pred_val \<Rightarrow> bool" where
  "summarizes_dl_BV_must \<rho> \<longleftrightarrow>
     (\<forall>\<pi>_end d.
        \<rho> \<Turnstile>\<^sub>l\<^sub>h CBV\<langle>[Cst\<^sub>N \<pi>_end, Cst\<^sub>E d]\<rangle>. \<longrightarrow>
          (\<forall>\<pi>. \<pi> \<in> LTS.path_with_word edge_set \<longrightarrow> LTS.get_start \<pi> = start \<longrightarrow> LTS.get_end \<pi> = \<pi>_end \<longrightarrow> d \<in> Ŝ\<^sub>P\<lbrakk> \<pi> d_init))"

BACKWARD MUST:
fun summarizes_dl_BV_must :: "(pred, ('n, 'v, 'd) cst) pred_val \<Rightarrow> bool" where
  "summarizes_dl_BV_must \<rho> \<longleftrightarrow>
     (\<forall>\<pi>_start d.
        \<rho> \<Turnstile>\<^sub>l\<^sub>h CBV\<langle>[Cst\<^sub>N \<pi>_start, Cst\<^sub>E d]\<rangle>. \<longrightarrow>
          (\<forall>\<pi>. \<pi> \<in> LTS.path_with_word edge_set \<longrightarrow> LTS.get_end \<pi> = end \<longrightarrow> LTS.get_start \<pi> = \<pi>_start \<longrightarrow> d \<in> Ŝ\<^sub>P\<lbrakk> \<pi> d_init))"

MAY  betyder \<Turnstile> på højresiden og BV.
MUST betyder \<Turnstile> på venstresiden og CBV.

Forward betyder at vi bruger kravet LTS.get_start \<pi> = start, og at vi har slutknuden i vores prædikat.
Backward betyder at vi bruger kravet LTS.get_end \<pi> = end, og at vi har start knuden i vores prædikat.

*)

end

section \<open>Very Busy Expressions\<close>

definition vbexp_edge_list :: "('n,'v) edge list \<Rightarrow> 'v arith \<Rightarrow> bool" where
  "vbexp_edge_list \<pi> a = (\<exists>\<pi>1 \<pi>2 e. \<pi> = \<pi>1 @ [e] @ \<pi>2 \<and> a \<in> aexp_edge e \<and> (\<forall>e' \<in> set \<pi>1. fv_arith a \<inter> def_edge e' = {}))"

definition vbexp_path :: "'n list \<times> 'v action list \<Rightarrow> 'v arith set" where
  "vbexp_path \<pi> = {a. vbexp_edge_list (LTS.transition_list \<pi>) a}"

locale analysis_VB =
  fixes pg :: "('n::finite,'v::finite) program_graph"
  assumes "finite (fst pg)"
begin

definition edge_set where 
  "edge_set = fst pg"

definition start where
  "start = fst (snd pg)"

definition "end" where
  "end = snd (snd pg)"

definition analysis_dom_VB :: "'v arith set" where
  "analysis_dom_VB = aexp_pg pg"

lemma finite_analysis_dom_VB: "finite analysis_dom_VB"
  unfolding analysis_dom_VB_def
  apply auto
  by (metis aexp_edge.elims analysis_VB_axioms analysis_VB_def finite_UN_I finite_aexp_action)

fun kill_set_VB :: "('n,'v) edge \<Rightarrow> 'v arith set" where
  "kill_set_VB (q\<^sub>o, x ::= a, q\<^sub>s) = {a'. x \<in> fv_arith a'}"
| "kill_set_VB (q\<^sub>o, Bool b, q\<^sub>s) = {}"
| "kill_set_VB (v, Skip, vc) = {}"

fun gen_set_VB :: "('n,'v) edge \<Rightarrow> 'v arith set" where
  "gen_set_VB (q\<^sub>o, x ::= a, q\<^sub>s) = ae_arith a"
| "gen_set_VB (q\<^sub>o, Bool b, q\<^sub>s) = ae_boolean b"
| "gen_set_VB (v, Skip, vc) = {}"

definition d_init_VB :: "'v arith set" where
  "d_init_VB = {}"

interpretation bw_must: analysis_BV_backward_must pg analysis_dom_VB kill_set_VB gen_set_VB d_init_VB
  using analysis_VB_axioms analysis_VB_def
  by (metis analysis_BV_backward_must.intro bot.extremum d_init_VB_def finite_analysis_dom_VB)

(* aexp_edge_list_S_hat_edge_list *)

find_theorems name: aexp_edge_list_S_hat_edge_list

find_theorems bw_must.S_hat_edge_list "(#)" 

lemma aexp_edge_list_S_hat_edge_list: 
  assumes "a \<in> aexp_edge (q, \<alpha>, q')"
  assumes "fv_arith a \<inter> def_edge (q, \<alpha>, q') = {}"
  shows "a \<in> bw_must.S_hat (q, \<alpha>, q') R"
  using assms unfolding bw_must.S_hat_def by (cases \<alpha>) auto

lemma empty_inter_fv_arith_def_edge:
  assumes "vbexp_edge_list (e # \<pi>) a"
  shows "fv_arith a \<inter> def_edge e = {} \<or> a \<in> aexp_edge e"
proof -
  from assms(1) obtain \<pi>1 \<pi>2 e' where \<pi>1_\<pi>2_e'_p:
    "e # \<pi> = \<pi>1 @ [e'] @ \<pi>2"
    "a \<in> aexp_edge e'"
    "(\<forall>e''\<in>set \<pi>1. fv_arith a \<inter> def_edge e'' = {})"
    unfolding vbexp_edge_list_def by auto
  from this(1) have "e \<in> set (\<pi>1 @ [e'])"
    by (metis append_self_conv2 hd_append2 list.sel(1) list.set_sel(1) snoc_eq_iff_butlast) 
  then have "e \<in> set \<pi>1 \<or> e = e'"
    by auto
  then show "fv_arith a \<inter> def_edge e = {} \<or> a \<in> aexp_edge e"
  proof
    assume "e \<in> set \<pi>1"
    then have "fv_arith a \<inter> def_edge e = {}" 
      using \<pi>1_\<pi>2_e'_p(3) by auto
    then show "fv_arith a \<inter> def_edge e = {} \<or> a \<in> aexp_edge e" 
       by auto
  next
    assume "e = e'"
    then have "a \<in> aexp_edge e"
      using \<pi>1_\<pi>2_e'_p(2) by auto 
    then show "fv_arith a \<inter> def_edge e = {}  \<or> a \<in> aexp_edge e"
      by auto 
  qed
qed

lemma vbexp_edge_list_append_singleton:
  assumes "vbexp_edge_list (e # \<pi>) a"
  shows "vbexp_edge_list \<pi> a \<or> a \<in> aexp_edge e"
proof -
  from assms(1) obtain \<pi>1 \<pi>2 e' where \<pi>1_\<pi>2_e'_p:
    "e # \<pi> = \<pi>1 @ [e'] @ \<pi>2"
    "a \<in> aexp_edge e'"
    "(\<forall>e''\<in>set \<pi>1. fv_arith a \<inter> def_edge e'' = {})"
    unfolding vbexp_edge_list_def by auto
  from this(1) have "e \<in> set (\<pi>1 @ [e'])"
    by (metis append_assoc hd_append2 list.sel(1) list.set_sel(1) snoc_eq_iff_butlast)
  then have "e = e' \<or> e \<in> set \<pi>1"
    by auto
  then show ?thesis
  proof
    assume "e = e'"
    then have "a \<in> aexp_edge e"
      using \<pi>1_\<pi>2_e'_p by auto
    then show ?thesis 
      by auto
  next
    assume "e \<in> set \<pi>1"
    then have "\<pi> = tl \<pi>1 @ [e'] @ \<pi>2"
      using \<pi>1_\<pi>2_e'_p by (metis equals0D list.sel(3) set_empty tl_append2) 
    moreover
    have "a \<in> aexp_edge e'"
      by (simp add: \<pi>1_\<pi>2_e'_p(2))
    moreover
    have "(\<forall>e''\<in> set (tl \<pi>1). fv_arith a \<inter> def_edge e'' = {})"
      by (metis \<pi>1_\<pi>2_e'_p(3) list.set_sel(2) tl_Nil)
    ultimately
    have "vbexp_edge_list \<pi> a"
      unfolding vbexp_edge_list_def by metis
    then show ?thesis
      by auto
  qed
qed

lemma gen_set_AE_subset_aexp_edge:
  assumes "a \<in> gen_set_VB e"
  shows "a \<in> aexp_edge e"
  using assms
  apply (cases e)
  apply auto
  subgoal for q \<alpha> q'
    apply (cases \<alpha>)
      apply auto
    done
  done

lemma empty_inter_fv_arith_def_edge'':
  assumes "a \<notin> kill_set_VB e"
  shows "fv_arith a \<inter> def_edge e = {}"
  using assms
  apply (cases e)
  apply auto
  subgoal for q \<alpha> q'
    apply (cases \<alpha>)
      apply auto
    done
  done


lemma S_hat_edge_list_aexp_edge_list: 
  assumes "a \<in> bw_must.S_hat_edge_list \<pi> d_init_VB"
  shows "vbexp_edge_list \<pi> a"
  using assms
proof (induction \<pi>)
  case Nil
  then show ?case 
    unfolding d_init_VB_def by auto
next
  case (Cons e \<pi>)
  from Cons(2) have "a \<in> (bw_must.S_hat_edge_list \<pi> d_init_VB - kill_set_VB e) \<or> a \<in> gen_set_VB e"
    using bw_must.S_hat_def by auto
  then show ?case
  proof 
    assume a_S_hat: "a \<in> bw_must.S_hat_edge_list \<pi> d_init_VB - kill_set_VB e"
    then have "vbexp_edge_list \<pi> a"
      using Cons by auto
    moreover
    from a_S_hat have "a \<notin> kill_set_VB e"
      by auto
    then have "fv_arith a \<inter> def_edge e = {}"
      using empty_inter_fv_arith_def_edge'' by auto
    ultimately show "vbexp_edge_list (e # \<pi>) a"
      unfolding vbexp_edge_list_def by (metis Cons_eq_appendI set_ConsD)
  next
    assume a_gen: "a \<in> gen_set_VB e"
    then have "a \<in> aexp_edge e"
      using gen_set_AE_subset_aexp_edge by auto
    then show "vbexp_edge_list (e # \<pi>) a"
      unfolding vbexp_edge_list_def by (metis append_Cons append_Nil empty_iff empty_set)
  qed
qed

lemma aexp_edge_list_S_hat_edge_list': 
  assumes "vbexp_edge_list \<pi> a"
  shows "a \<in> bw_must.S_hat_edge_list \<pi> d_init_VB"
  using assms
proof (induction \<pi>)
  case Nil
  then have False 
    unfolding vbexp_edge_list_def by auto
  then show ?case
    by metis
next
  case (Cons e \<pi>)
  have fva: "fv_arith a \<inter> def_edge e = {} \<or> a \<in> aexp_edge e"
    using Cons(2) empty_inter_fv_arith_def_edge by force

  have "vbexp_edge_list \<pi> a \<or> a \<in> aexp_edge e"
    using Cons(2)
    by (simp add: vbexp_edge_list_append_singleton)
  then show ?case
  proof
    assume "vbexp_edge_list \<pi> a"
    then have "a \<in> bw_must.S_hat_edge_list \<pi> d_init_VB"
      using Cons by auto
    moreover
    have "a \<notin> kill_set_VB e \<or> a \<in> gen_set_VB e"
      using fva apply (cases e) subgoal for q \<alpha> q' 
        apply (cases \<alpha>)
          apply auto
        done (* extract lemma *)
      done
    ultimately
    show ?case
      using bw_must.S_hat_def by auto
  next
    assume "a \<in> aexp_edge e"
    then have "a \<in> gen_set_VB e"
      using fva
      apply (cases e) subgoal for q \<alpha> q' 
        apply (cases \<alpha>)
          apply auto
        done (* extract lemma *)
      done
    then show ?case
      using bw_must.S_hat_def by auto
  qed
qed

lemma vbexp_edge_list_S_hat_edge_list_iff: 
  "vbexp_edge_list \<pi> a \<longleftrightarrow> a \<in> bw_must.S_hat_edge_list \<pi> d_init_VB"
  using S_hat_edge_list_aexp_edge_list aexp_edge_list_S_hat_edge_list' by blast

lemma vbexp_path_S_hat_path_iff: 
  "a \<in> vbexp_path \<pi> \<longleftrightarrow> a \<in> bw_must.S_hat_path \<pi> d_init_VB"
  by (simp add: bw_must.S_hat_path_def vbexp_edge_list_S_hat_edge_list_iff vbexp_path_def)

definition summarizes_VB where
  "summarizes_VB \<rho> \<longleftrightarrow>
     (\<forall>\<pi>_start d.
         \<rho> \<Turnstile>\<^sub>l\<^sub>h CBV\<langle>[\<pi>_start, d]\<rangle>. \<longrightarrow>
          (\<forall>\<pi>. \<pi> \<in> LTS.path_with_word bw_must.edge_set \<longrightarrow> LTS.get_end \<pi> = bw_must.end \<longrightarrow> LTS.get_start \<pi> = Decode_Node \<pi>_start \<longrightarrow> Decode_Elem d \<in> bw_must.S_hat_path \<pi> d_init_VB))"

theorem BV_sound:
  assumes "\<rho> \<Turnstile>\<^sub>l\<^sub>s\<^sub>t (bw_must.ana_pg_bw_must) s_BV"
  shows "summarizes_VB \<rho>"
proof -
  from assms have "bw_must.summarizes_bw_must \<rho>"
    using bw_must.sound_ana_pg_bw_must by auto
  then show ?thesis
    unfolding summarizes_VB_def bw_must.summarizes_bw_must_def bw_must.edge_set_def edge_set_def
      bw_must.end_def end_def vbexp_path_S_hat_path_iff bw_must.start_def start_def by force
qed

end