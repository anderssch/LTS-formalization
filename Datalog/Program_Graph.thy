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

type_synonym ('n,'v) edge = "'n \<times> 'v action \<times> 'n"

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

datatype (preds_rh: 'p,'x,'e) righthand = 
  Eql "('x,'e) identifier" "('x,'e) identifier" ("_ \<^bold>= _" [61, 61] 61)
  | Neql "('x,'e) identifier" "('x,'e) identifier" ("_ \<^bold>\<noteq> _" [61, 61] 61)
  | PosRh 'p "('x,'e) identifier list"
  | NegRh 'p "('x,'e) identifier list" ("\<^bold>\<not> _ _" [61, 61] 61)

datatype (preds_cls: 'p, 'x,'e) clause = Cls 'p "('x,'e) identifier list" "('p,'x,'e) righthand list" (* Why not righthand set? *)

type_synonym ('p,'x,'e) dl_program = "('p,'x,'e) clause set"

definition "preds_dl dl = \<Union>{preds_cls c| c. c \<in> dl}"

lemma preds_dl_union[simp]: "preds_dl (dl1 \<union> dl2) = preds_dl dl1 \<union> preds_dl dl2"
  unfolding preds_dl_def by auto

type_synonym ('x,'e) var_val = "'x \<Rightarrow> 'e"

type_synonym ('p,'e) pred_val = "'p \<Rightarrow> 'e list set"

type_synonym ('p,'x,'e) lefthand = "'p * ('x,'e) identifier list"

fun preds_lh where "preds_lh (p,ids) = {p}"

fun eval_id :: "('x,'e) identifier \<Rightarrow> ('x,'e) var_val \<Rightarrow> 'e" ("\<lbrakk>_\<rbrakk>\<^sub>i\<^sub>d") where
  "\<lbrakk>DLVar x\<rbrakk>\<^sub>i\<^sub>d \<sigma> = \<sigma> x"
| "\<lbrakk>DLElement e\<rbrakk>\<^sub>i\<^sub>d \<sigma> = e"

fun meaning_rh :: "('p,'x,'e) righthand \<Rightarrow> ('p,'e) pred_val \<Rightarrow> ('x,'e) var_val \<Rightarrow> bool" ("\<lbrakk>_\<rbrakk>\<^sub>r\<^sub>h") where
  "\<lbrakk>a \<^bold>= a'\<rbrakk>\<^sub>r\<^sub>h \<rho> \<sigma> \<longleftrightarrow> \<lbrakk>a\<rbrakk>\<^sub>i\<^sub>d \<sigma> = \<lbrakk>a'\<rbrakk>\<^sub>i\<^sub>d \<sigma>"
| "\<lbrakk>a \<^bold>\<noteq> a'\<rbrakk>\<^sub>r\<^sub>h \<rho> \<sigma> \<longleftrightarrow> \<lbrakk>a\<rbrakk>\<^sub>i\<^sub>d \<sigma>  \<noteq> \<lbrakk>a'\<rbrakk>\<^sub>i\<^sub>d \<sigma>"
| "\<lbrakk>PosRh p ids\<rbrakk>\<^sub>r\<^sub>h \<rho> \<sigma> \<longleftrightarrow> map (\<lambda>a. \<lbrakk>a\<rbrakk>\<^sub>i\<^sub>d \<sigma>) ids \<in> \<rho> p"
| "\<lbrakk>\<^bold>\<not> p ids\<rbrakk>\<^sub>r\<^sub>h \<rho> \<sigma> \<longleftrightarrow> \<not> map (\<lambda>a. \<lbrakk>a\<rbrakk>\<^sub>i\<^sub>d \<sigma>) ids \<in> \<rho> p"

fun meaning_lh :: "('p,'x,'e) lefthand \<Rightarrow> ('p,'e) pred_val \<Rightarrow> ('x,'e) var_val \<Rightarrow> bool" ("\<lbrakk>_\<rbrakk>\<^sub>l\<^sub>h") where
  "\<lbrakk>(p,ids)\<rbrakk>\<^sub>l\<^sub>h \<rho> \<sigma> \<longleftrightarrow> map (\<lambda>a. \<lbrakk>a\<rbrakk>\<^sub>i\<^sub>d \<sigma>) ids \<in> \<rho> p"

fun meaning_cls :: "('p,'x,'e) clause \<Rightarrow> ('p,'e) pred_val \<Rightarrow> ('x,'e) var_val \<Rightarrow> bool" ("\<lbrakk>_\<rbrakk>\<^sub>c\<^sub>l\<^sub>s") where
  "\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho> \<sigma> \<longleftrightarrow> ((\<forall>rh\<in>set rhs. \<lbrakk>rh\<rbrakk>\<^sub>r\<^sub>h \<rho> \<sigma>) \<longrightarrow> \<lbrakk>(p,ids)\<rbrakk>\<^sub>l\<^sub>h \<rho> \<sigma>)"

fun solves_rh :: "('p,'e) pred_val \<Rightarrow> ('p,'x,'e) righthand \<Rightarrow> bool" (infix "\<Turnstile>\<^sub>r\<^sub>h" 91) where (* Not in the book *)
  "\<rho> \<Turnstile>\<^sub>r\<^sub>h rh \<longleftrightarrow> (\<forall>\<sigma>. \<lbrakk>rh\<rbrakk>\<^sub>r\<^sub>h \<rho> \<sigma>)"

definition solves_cls :: "('p,'e) pred_val \<Rightarrow> ('p,'x,'e) clause \<Rightarrow> bool" (infix "\<Turnstile>\<^sub>c\<^sub>l\<^sub>s" 91) where
  "\<rho> \<Turnstile>\<^sub>c\<^sub>l\<^sub>s c \<longleftrightarrow> (\<forall>\<sigma>. \<lbrakk>c\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho> \<sigma>)"

definition solves_program :: "('p,'e) pred_val \<Rightarrow> ('p,'x,'e) dl_program \<Rightarrow> bool" (infix "\<Turnstile>\<^sub>d\<^sub>l" 91) where
  "\<rho> \<Turnstile>\<^sub>d\<^sub>l dl \<longleftrightarrow> (\<forall>c \<in> dl. \<rho> \<Turnstile>\<^sub>c\<^sub>l\<^sub>s c)"


section \<open>Queries (not in the book?)\<close>

type_synonym ('p,'x,'e) query = "'p * ('x,'e) identifier list"

fun meaning_query :: "('p,'x,'e) query \<Rightarrow> ('p,'e) pred_val \<Rightarrow> ('x,'e) var_val \<Rightarrow> bool" ("\<lbrakk>_\<rbrakk>\<^sub>q") where
  "\<lbrakk>(p,ids)\<rbrakk>\<^sub>q \<rho> \<sigma> \<longleftrightarrow> map (\<lambda>a. \<lbrakk>a\<rbrakk>\<^sub>i\<^sub>d \<sigma>) ids \<in> \<rho> p"

fun solves_query :: "('p,'e) pred_val \<Rightarrow> ('p,'x,'e) query \<Rightarrow> bool" (infix "\<Turnstile>\<^sub>q" 91) where
  "\<rho> \<Turnstile>\<^sub>q (p,ids) \<longleftrightarrow> (\<forall>\<sigma>. \<lbrakk>(p,ids)\<rbrakk>\<^sub>q \<rho> \<sigma>)"


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
  "compose \<mu> \<sigma> x = \<lbrakk>(\<mu> x)\<rbrakk>\<^sub>i\<^sub>d \<sigma>"


section \<open>Datalog lemmas\<close>

lemma solves_cls_iff_solves_rh: "\<rho> \<Turnstile>\<^sub>c\<^sub>l\<^sub>s Cls p ids [] \<longleftrightarrow> \<rho> \<Turnstile>\<^sub>r\<^sub>h PosRh p ids"
  using solves_cls_def by force

lemma solves_fact_query:
  assumes "\<rho> \<Turnstile>\<^sub>c\<^sub>l\<^sub>s Cls p args []"
  shows "\<rho> \<Turnstile>\<^sub>q (p, args)"
  using assms unfolding solves_cls_def by auto

lemma resolution_last_rh:
  assumes "\<rho> \<Turnstile>\<^sub>c\<^sub>l\<^sub>s Cls p args (rhs @ [rh])"
  assumes "\<rho> \<Turnstile>\<^sub>r\<^sub>h rh"
  shows "\<rho> \<Turnstile>\<^sub>c\<^sub>l\<^sub>s Cls p args rhs"
  using assms unfolding solves_cls_def by auto

lemma resolution_last_rh_query:
  assumes "\<rho> \<Turnstile>\<^sub>c\<^sub>l\<^sub>s Cls p args (rhs @ [PosRh p ids])"
  assumes "\<rho> \<Turnstile>\<^sub>q (p, ids)"
  shows "\<rho> \<Turnstile>\<^sub>c\<^sub>l\<^sub>s Cls p args rhs"
  using assms by (force simp add: solves_cls_def)

lemma resolution_only_rh_query:
  assumes "\<rho> \<Turnstile>\<^sub>c\<^sub>l\<^sub>s Cls p ids [PosRh p' ids']"
  assumes "\<rho> \<Turnstile>\<^sub>q (p', ids')"
  shows "\<rho> \<Turnstile>\<^sub>q (p, ids)"
  using assms
proof -
  from assms(2) have "\<forall>\<sigma>. \<lbrakk>PosRh p' ids'\<rbrakk>\<^sub>r\<^sub>h \<rho> \<sigma>"
    by fastforce
  then have "\<rho> \<Turnstile>\<^sub>c\<^sub>l\<^sub>s Cls p ids []"
    using assms(1)
    by (metis self_append_conv2 solves_rh.elims(3) resolution_last_rh)
  then show "\<rho> \<Turnstile>\<^sub>q (p, ids)"
    by (meson solves_fact_query)
qed

lemma resolution_all_rhs:
  assumes "\<rho> \<Turnstile>\<^sub>c\<^sub>l\<^sub>s Cls p ids rhs"
  assumes "\<forall>rh\<in>set rhs. \<rho> \<Turnstile>\<^sub>r\<^sub>h rh"
  shows "\<rho> \<Turnstile>\<^sub>q (p, ids)"
  using assms
  by (metis (full_types) meaning_cls.simps meaning_lh.simps meaning_query.simps solves_cls_def solves_query.elims(1) solves_rh.elims(2))

lemma substitution_lemma_id: "\<lbrakk>a\<rbrakk>\<^sub>i\<^sub>d (compose \<mu> \<sigma>) = \<lbrakk>subst_id \<mu> a\<rbrakk>\<^sub>i\<^sub>d \<sigma>"
  by (cases a) (auto simp add: compose_def)

lemma substitution_lemma_ids: "map (\<lambda>a. \<lbrakk>a\<rbrakk>\<^sub>i\<^sub>d (compose \<mu> \<sigma>)) ids = map ((\<lambda>a. \<lbrakk>a\<rbrakk>\<^sub>i\<^sub>d \<sigma>) \<circ> subst_id \<mu>) ids"
  using substitution_lemma_id by auto

lemma substitution_lemma_lh: "\<lbrakk>(p, ids)\<rbrakk>\<^sub>l\<^sub>h \<rho> (compose \<mu> \<sigma>) \<longleftrightarrow> \<lbrakk>(p, map (subst_id \<mu>) ids)\<rbrakk>\<^sub>l\<^sub>h \<rho> \<sigma>"
 by (simp add: substitution_lemma_ids)


lemma substitution_lemma_rh:"\<lbrakk>rh\<rbrakk>\<^sub>r\<^sub>h \<rho> (compose \<mu> \<sigma>) \<longleftrightarrow> \<lbrakk>subst_rh \<mu> rh\<rbrakk>\<^sub>r\<^sub>h \<rho> \<sigma>"
proof (induction rh)
  case (Eql x1 x2)
  then show ?case
    by (simp add: substitution_lemma_id)
next
  case (Neql x1 x2)
  then show ?case
    by (simp add: substitution_lemma_id)
next
  case (PosRh x1 x2)
  then show ?case
    using substitution_lemma_lh by fastforce
next
  case (NegRh x1 x2)
  then show ?case
    using substitution_lemma_lh by fastforce
qed

lemma substitution_lemma_rhs: "(\<forall>rh\<in>set rhs. \<lbrakk>rh\<rbrakk>\<^sub>r\<^sub>h \<rho> (compose \<mu> \<sigma>)) \<longleftrightarrow> (\<forall>rh\<in>set (map (subst_rh \<mu>) rhs). \<lbrakk>rh\<rbrakk>\<^sub>r\<^sub>h \<rho> \<sigma>)"
  by (simp add: substitution_lemma_rh) 

lemma substitution_lemma_cls:
  "meaning_cls c \<rho> (compose \<mu> \<sigma>) \<longleftrightarrow> meaning_cls (subst_cls \<mu> c) \<rho> \<sigma>"
proof (induction c)
  case (Cls p ids rhs)
  have a: "(\<forall>rh\<in>set rhs. \<lbrakk>rh\<rbrakk>\<^sub>r\<^sub>h \<rho> (compose \<mu> \<sigma>)) = (\<forall>rh\<in>set (map (subst_rh \<mu>) rhs). \<lbrakk>rh\<rbrakk>\<^sub>r\<^sub>h \<rho> \<sigma>)"
    using substitution_lemma_rhs by blast
  have b: "\<lbrakk>(p, ids)\<rbrakk>\<^sub>l\<^sub>h \<rho> (compose \<mu> \<sigma>) = \<lbrakk>(p, map (subst_id \<mu>) ids)\<rbrakk>\<^sub>l\<^sub>h \<rho> \<sigma>"
    using substitution_lemma_lh by metis
  show ?case
    unfolding meaning_cls.simps
    using a b by auto
qed

lemma substitution_rule:
  assumes "\<rho> \<Turnstile>\<^sub>c\<^sub>l\<^sub>s c"
  shows "\<rho> \<Turnstile>\<^sub>c\<^sub>l\<^sub>s subst_cls (\<mu>::('x,'e) subst) c"
proof -
  show ?thesis
    unfolding solves_cls_def
  proof
    fix \<sigma> :: "'x \<Rightarrow> 'e"
    term "\<mu> :: 'x \<Rightarrow> ('x, 'e) identifier"
    from assms have "\<lbrakk>c\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho> (compose \<mu> \<sigma>)"
      using solves_cls_def by auto
    then show "\<lbrakk>subst_cls \<mu> c\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho> \<sigma>"
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

definition max_strata :: "'p strat \<Rightarrow> ('p,'x,'e) dl_program \<Rightarrow> nat" where
  "max_strata s dl = Max {s p | p ids rhs. Cls p ids rhs \<in> dl}"

fun pred_val_mod_strata :: "('p,'e) pred_val \<Rightarrow> 'p strat \<Rightarrow> nat \<Rightarrow> ('p,'e) pred_val"  ("_ \\_\\ _" 0) where 
  "(\<sigma> \\s\\ n) p = (if s p \<le> n then \<sigma> p else {})"

fun dl_program_mod_strata :: "('p,'x,'e) dl_program \<Rightarrow> 'p strat \<Rightarrow> nat \<Rightarrow> ('p,'x,'e) dl_program"  ("_ --_-- _" 0) where 
  "(dl -- s -- n) = {(Cls p ids rhs)| p ids rhs . (Cls p ids rhs) \<in> dl \<and> s p \<le> n}"

fun dl_program_on_strata :: "('p,'x,'e) dl_program \<Rightarrow> 'p strat \<Rightarrow> nat \<Rightarrow> ('p,'x,'e) dl_program"  ("_ ==_== _" 0) where 
  "(dl == s == n) = {(Cls p ids rhs)| p ids rhs . (Cls p ids rhs) \<in> dl \<and> s p = n}"

definition lt :: "('p,'e) pred_val \<Rightarrow> 'p strat \<Rightarrow> ('p,'e) pred_val \<Rightarrow> bool" ("_ \<sqsubset>_\<sqsubset> _") where
  "(\<rho> \<sqsubset>s\<sqsubset> \<rho>') \<longleftrightarrow> (\<exists>p. \<rho> p \<subset> \<rho>' p \<and>
                       (\<forall>p'. s p' = s p \<longrightarrow> \<rho> p' \<subseteq> \<rho>' p') \<and>
                       (\<forall>p'. s p' < s p \<longrightarrow> \<rho> p' = \<rho>' p'))"

definition lte :: "('p,'e) pred_val \<Rightarrow> 'p strat \<Rightarrow> ('p,'e) pred_val \<Rightarrow> bool" ("_ \<sqsubseteq>_\<sqsubseteq> _") where
  "(\<rho> \<sqsubseteq>s\<sqsubseteq> \<rho>') \<longleftrightarrow> \<rho> = \<rho>' \<or> (\<rho> \<sqsubset>s\<sqsubset> \<rho>')"

definition least_solution :: "('p,'e) pred_val \<Rightarrow> ('p,'x,'e) dl_program \<Rightarrow> 'p strat \<Rightarrow> bool" where
  "least_solution \<sigma> dl s \<longleftrightarrow> (\<sigma> \<Turnstile>\<^sub>d\<^sub>l dl \<and> (\<forall>\<sigma>'. \<sigma>' \<Turnstile>\<^sub>d\<^sub>l dl \<longrightarrow> \<sigma> \<sqsubseteq>s\<sqsubseteq> \<sigma>'))"

definition minimal_solution :: "('p,'e) pred_val \<Rightarrow> ('p,'x,'e) dl_program \<Rightarrow> 'p strat \<Rightarrow> bool" where
  "minimal_solution \<sigma> dl s \<longleftrightarrow> (\<sigma> \<Turnstile>\<^sub>d\<^sub>l dl \<and> (\<nexists>\<sigma>'. \<sigma>' \<Turnstile>\<^sub>d\<^sub>l dl \<and> \<sigma>' \<sqsubset>s\<sqsubset> \<sigma>))"

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
  assumes "\<sigma> \<Turnstile>\<^sub>d\<^sub>l (dl --s-- n)"
  assumes "strat_wf s dl"
  shows " (\<sigma> \\s\\ m) \<Turnstile>\<^sub>d\<^sub>l (dl --s-- m)"
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

  have "(\<sigma> \\s\\ m) \<Turnstile>\<^sub>c\<^sub>l\<^sub>s Cls p ids rhs"
    unfolding solves_cls_def
  proof 
    fix \<eta>
    have mm: "\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<sigma> \<eta>"
      using \<open>c \<in> (dl --s-- n)\<close> assms(2) c_def solves_cls_def solves_program_def by blast
    have "s p \<le> m"
      using \<open>c \<in> (dl --s-- m)\<close> c_def by fastforce
    moreover
    have "\<forall>rh \<in> set rhs. rnk s rh \<le> m"
      using \<open>c \<in> (dl --s-- m)\<close> assms(2) c_def dual_order.trans strat_wf_def
      by (metis (no_types, lifting) \<open>strat_wf s (dl --s-- m)\<close> calculation strat_wf_cls.simps)
    ultimately
    show "\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s (\<sigma> \\s\\ m) \<eta>"
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
  then show "(\<sigma> \\s\\ m) \<Turnstile>\<^sub>c\<^sub>l\<^sub>s c"
    using c_def by auto
qed

lemma downward_solves2:
  assumes "\<sigma> \<Turnstile>\<^sub>d\<^sub>l dl"
  assumes "strat_wf s dl"
  shows "(\<sigma> \\s\\ m) \<Turnstile>\<^sub>d\<^sub>l (dl --s-- m)"
  unfolding solves_program_def
proof
  fix c
  assume "c \<in> (dl --s-- m)"
  then obtain p ids rhs where c_def: "c = Cls p ids rhs"
    by (cases c) auto

  have "\<sigma> \<Turnstile>\<^sub>c\<^sub>l\<^sub>s c"
    using \<open>c \<in> (dl --s-- m)\<close> assms(1) solves_program_def by auto
  
  have "(\<sigma> \\s\\ m) \<Turnstile>\<^sub>c\<^sub>l\<^sub>s Cls p ids rhs"
    unfolding solves_cls_def
  proof 
    fix \<eta>
    have mm: "\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<sigma> \<eta>"
      using  \<open>\<sigma> \<Turnstile>\<^sub>c\<^sub>l\<^sub>s c\<close> c_def by (simp add: solves_cls_def)
    have "s p \<le> m"
      using \<open>c \<in> (dl --s-- m)\<close> c_def by fastforce
    moreover
    have "\<forall>rh \<in> set rhs. rnk s rh \<le> m"
      using \<open>c \<in> (dl --s-- m)\<close> assms(2) c_def dual_order.trans strat_wf_def by fastforce
    ultimately
    show "\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s (\<sigma> \\s\\ m) \<eta>"
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
  then show "(\<sigma> \\s\\ m) \<Turnstile>\<^sub>c\<^sub>l\<^sub>s c"
    using c_def by auto
qed



definition Inter' ("\<^bold>\<Inter>") where 
  "(\<^bold>\<Inter> \<rho>s) = (\<lambda>p. \<Inter>{m. \<exists>\<rho> \<in> \<rho>s. m = \<rho> p})"

fun solve_pg where
  "solve_pg s dl 0 = (\<^bold>\<Inter> {\<rho>'. \<rho>' \<Turnstile>\<^sub>d\<^sub>l (dl ==s== 0)})"
| "solve_pg s dl (Suc n) = (\<^bold>\<Inter> {\<rho>'. \<rho>' \<Turnstile>\<^sub>d\<^sub>l (dl ==s== Suc n) \<and> (\<rho>' \\s\\ n) = solve_pg s dl n})"

definition least_rank_p_st :: "('p \<Rightarrow> bool) \<Rightarrow> 'p \<Rightarrow> ('p \<Rightarrow> nat)  \<Rightarrow> bool" where 
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
      unfolding least_rank_p_st_def
      apply -
      apply (rule_tac x=p in exI)
      using less(2)
      apply -
      using linorder_le_less_linear by blast
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

lemma solve_pg_0_empty: (* Can be generalized from 0 to n and Inter' to solve_pg. ARE YOU REALLY SURE ABOUT THAT? *)
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
      assume "\<forall>rh\<in>set rhs. \<lbrakk>rh\<rbrakk>\<^sub>r\<^sub>h \<rho>' \<sigma>"
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
  define \<rho>'' :: "'a \<Rightarrow> 'b list set" where "\<rho>'' = (solve_pg s dl (Suc n))"
  define \<rho>' :: "'a \<Rightarrow> 'b list set" where "\<rho>' = (\<lambda>p. if s p < Suc n then (solve_pg s dl n) p else if s p = Suc n then UNIV else {})"

  have "\<rho>' \<Turnstile>\<^sub>d\<^sub>l (dl ==s== Suc n)"
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
      assume "\<forall>rh\<in>set rhs. \<lbrakk>rh\<rbrakk>\<^sub>r\<^sub>h \<rho>' \<sigma>"
      show "\<lbrakk>(p', ids)\<rbrakk>\<^sub>l\<^sub>h \<rho>' \<sigma>"
        using \<rho>'_def sp'Sucn
        by auto[]
    qed
    then show "\<lbrakk>c\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho>' \<sigma>"
      unfolding c_split by auto
  qed
  have "\<forall>p. (\<rho>' \\s\\ n) p = (solve_pg s dl n) p"
    apply auto
    apply (simp add: \<rho>'_def)+
    using Suc  by auto
  have "\<rho>'' p \<subseteq> \<rho>' p"
    using solve_pg_Suc_subset[of \<rho>' dl s n  p] \<open>\<rho>' \<Turnstile>\<^sub>d\<^sub>l (dl ==s== Suc n)\<close> \<rho>''_def \<open>\<forall>p. (\<rho>' \s\ n) p = (solve_pg s dl n) p\<close> by force
  then have "\<rho>'' p = {}"
    unfolding \<rho>'_def using assms(1) Suc by simp
  then show ?case
    unfolding \<rho>''_def by auto
qed

lemma exi_sol_n: "\<exists>\<rho>'. \<rho>' \<Turnstile>\<^sub>d\<^sub>l (dl ==s== Suc m) \<and> (\<rho>' \\s\\ m) = solve_pg s dl m"
proof -
  define \<rho>' where "\<rho>' = (\<lambda>p. (if s p < Suc m then (solve_pg s dl m) p else if s p = Suc m then UNIV else {}))"

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
  using assms proof (induction m)
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
    then have "(solve_pg s dl (s p)) p = (solve_pg s dl m) p"
      using Suc by auto

    have "\<forall>\<rho>'. \<rho>' \<Turnstile>\<^sub>d\<^sub>l (dl ==s== Suc m) \<and> (\<rho>' \\s\\ m) = solve_pg s dl m \<longrightarrow> \<rho>' p = solve_pg s dl m p"
      by (metis pred_val_mod_strata.simps s_p)
    then have "\<^bold>\<Inter> {\<rho>'. \<rho>' \<Turnstile>\<^sub>d\<^sub>l (dl ==s== Suc m) \<and> (\<rho>' \\s\\ m) = solve_pg s dl m} p = solve_pg s dl (s p) p"
      unfolding Inter'_def apply auto
       apply (metis \<open>solve_pg s dl (s p) p = solve_pg s dl m p\<close> dl_program_on_strata.elims exi_sol_n)
      using \<open>solve_pg s dl (s p) p = solve_pg s dl m p\<close> by blast
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

lemma uiohvaryuibweafbyvuib:
  assumes "s p \<le> n"
  assumes "s p \<le> m"
  shows "\<lbrakk>(p,ids)\<rbrakk>\<^sub>l\<^sub>h (solve_pg s dl m) \<sigma> \<longleftrightarrow> \<lbrakk>(p,ids)\<rbrakk>\<^sub>l\<^sub>h (solve_pg s dl n) \<sigma>"
  by (metis assms less_imp_le_nat meaning_lh.simps solve_pg_two_agree_above)

lemma uiaerhuivrsaivrfhweaof:
  assumes "strat_wf s dl"
  assumes "Cls p ids rhs \<in> dl"
  assumes "s p \<le> n"
  assumes "s p \<le> m"
  shows "\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s (solve_pg s dl n) \<sigma> \<longleftrightarrow> \<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s (solve_pg s dl m) \<sigma>"
  by (meson assms meaning_cls.simps solve_pg_two_agree_above_on_rh uiohvaryuibweafbyvuib)

lemma uiaerhuivrsaivrfhweaof_Suc:
  assumes "strat_wf s dl"
  assumes "Cls p ids rhs \<in> dl"
  assumes "s p \<le> n"
  shows "\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s (solve_pg s dl (Suc n)) \<sigma> \<longleftrightarrow> \<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s (solve_pg s dl n) \<sigma>"
  using uiaerhuivrsaivrfhweaof[OF assms(1,2,3), of "Suc n" \<sigma>] assms(3) by auto

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
  using assms
  apply (cases rh)
     apply auto
  subgoal for p ids
    unfolding Inter'_def
    apply auto
    done
  subgoal for p ids
    unfolding Inter'_def
    apply auto
    apply (meson strata0_no_neg')
    done
  done

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

lemma solve_pg_Suc_if_all_meaning_lh:
  assumes "\<forall>\<rho>'. \<rho>' \<Turnstile>\<^sub>d\<^sub>l (dl ==s== Suc n) \<longrightarrow> (\<rho>' \\s\\ n) = solve_pg s dl n \<longrightarrow> \<lbrakk>(p, ids)\<rbrakk>\<^sub>l\<^sub>h \<rho>' \<sigma>"
  shows "\<lbrakk>(p, ids)\<rbrakk>\<^sub>l\<^sub>h (solve_pg s dl (Suc n)) \<sigma>"
  using assms by (auto simp add: Inter'_def)

lemma solve_pg_0_meaning_cls':
  assumes "strat_wf s dl"
  assumes "Cls p ids rhs \<in> (dl --s-- 0)"
  shows "\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s (solve_pg s dl 0) \<sigma>"
  unfolding meaning_cls.simps
proof
  define \<rho>'' :: "'a \<Rightarrow> 'c list set" where "\<rho>'' = (solve_pg s dl 0)"
  assume "\<forall>rh\<in>set rhs. \<lbrakk>rh\<rbrakk>\<^sub>r\<^sub>h (solve_pg s dl 0) \<sigma>"
  then have "\<forall>\<rho>'. \<rho>' \<Turnstile>\<^sub>d\<^sub>l (dl --s-- 0) \<longrightarrow> (\<forall>rh\<in>set rhs. \<lbrakk>rh\<rbrakk>\<^sub>r\<^sub>h \<rho>' \<sigma>)"
    using all_meaning_rh_if_solve_pg_0[OF assms(1), of _ \<sigma> _ rhs p ids, OF _ _ _ assms(2)] 
    by auto
  then have "\<forall>\<rho>'. \<rho>' \<Turnstile>\<^sub>d\<^sub>l (dl --s-- 0) \<longrightarrow> \<lbrakk>(p, ids)\<rbrakk>\<^sub>l\<^sub>h  \<rho>' \<sigma>"
    by (metis assms(2) meaning_cls.simps solves_cls_def solves_program_def)
  then show "\<lbrakk>(p, ids)\<rbrakk>\<^sub>l\<^sub>h (solve_pg s dl 0) \<sigma>"
    using solve_pg_0_if_all_meaning_lh by auto
qed

(* For clauses under Suc n er (solve_pg s dl (Suc n)) og (solve_pg s dl n) enige  *)

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
      assume "\<forall>rh\<in>set rhs. \<lbrakk>rh\<rbrakk>\<^sub>r\<^sub>h (solve_pg s dl (Suc n)) \<sigma>"
      then have "\<forall>\<rho>'. \<rho>' \<Turnstile>\<^sub>d\<^sub>l (dl ==s== Suc n) \<longrightarrow> (\<rho>' \\s\\ n) = solve_pg s dl n \<longrightarrow> (\<forall>rh\<in>set rhs. \<lbrakk>rh\<rbrakk>\<^sub>r\<^sub>h \<rho>' \<sigma>)"
        using all_meaning_rh_if_solve_pg_Suc[OF assms(1) _ _ _ _ Suc(3), of _ \<sigma>] 
        by auto
      then have "\<forall>\<rho>'. \<rho>' \<Turnstile>\<^sub>d\<^sub>l (dl ==s== Suc n) \<longrightarrow> (\<rho>' \\s\\ n) = solve_pg s dl n \<longrightarrow> \<lbrakk>(p, ids)\<rbrakk>\<^sub>l\<^sub>h \<rho>' \<sigma>"
        using meaning_cls.simps solves_cls_def solves_program_def cls_in_Suc by metis
      then show "\<lbrakk>(p, ids)\<rbrakk>\<^sub>l\<^sub>h (solve_pg s dl (Suc n)) \<sigma>"
        using solve_pg_Suc_if_all_meaning_lh[of dl s n p ids \<sigma>] by auto
    qed
  next
    case False
    then have False': "s p < Suc n"
      using leq_n by auto
    then have "s p \<le> n"
      by auto
    then have "Cls p ids rhs \<in> (dl --s-- n)"
      by (simp add: cls_in)
    then have "(\<forall>rh\<in>set rhs. \<lbrakk>rh\<rbrakk>\<^sub>r\<^sub>h (solve_pg s dl n) \<sigma>) \<longrightarrow> \<lbrakk>(p, ids)\<rbrakk>\<^sub>l\<^sub>h (solve_pg s dl n) \<sigma>"
      using Suc by auto
    find_theorems n
    then show ?thesis (* For clauses under Suc n er (solve_pg s dl (Suc n)) og (solve_pg s dl n) enige  *)
      unfolding meaning_cls.simps[symmetric] using False' using uiaerhuivrsaivrfhweaof_Suc[OF assms(1) cls_in \<open>s p \<le> n\<close>] by metis
  qed
qed

lemma solve_pg_0_meaning_cls:
  assumes "strat_wf s dl"
  assumes "c \<in> (dl --s-- 0)"
  shows "\<lbrakk>c\<rbrakk>\<^sub>c\<^sub>l\<^sub>s (solve_pg s dl 0) \<sigma>"
  using assms solve_pg_0_meaning_cls'[of s dl _ _ _ \<sigma>] 
  by (cases c) auto

lemma solve_pg_Suc_meaning_cls:
  assumes "strat_wf s dl"
  assumes "c \<in> (dl --s-- (Suc n))"
  shows "\<lbrakk>c\<rbrakk>\<^sub>c\<^sub>l\<^sub>s (solve_pg s dl (Suc n)) \<sigma>"
  using assms solve_pg_Suc_meaning_cls'[of s dl] by (cases c) metis

lemma solve_pg_0_models_cls:
  assumes "strat_wf s dl"
  assumes "c \<in> (dl --s-- 0)"
  shows "(solve_pg s dl 0) \<Turnstile>\<^sub>c\<^sub>l\<^sub>s c"
  unfolding solves_cls_def using solve_pg_0_meaning_cls assms by blast

lemma solve_pg_Suc_models_cls:
  assumes "strat_wf s dl"
  assumes "c \<in> (dl --s-- Suc n)"
  shows "(solve_pg s dl (Suc n)) \<Turnstile>\<^sub>c\<^sub>l\<^sub>s c"
  unfolding solves_cls_def using solve_pg_Suc_meaning_cls assms by blast

lemma solve_pg_0_solves_dl:
  assumes "strat_wf s dl"
  shows "(solve_pg s dl 0) \<Turnstile>\<^sub>d\<^sub>l (dl --s-- 0)"
proof -
  have "\<forall>c \<in> (dl --s-- 0). (solve_pg s dl 0) \<Turnstile>\<^sub>c\<^sub>l\<^sub>s c"
    using assms solve_pg_0_models_cls[of s dl] by auto
  then show "(solve_pg s dl 0) \<Turnstile>\<^sub>d\<^sub>l (dl --s-- 0)"
    using solves_program_def by blast
qed

lemma solve_pg_Suc_solves_dl:
  assumes "strat_wf s dl"
  shows "(solve_pg s dl (Suc n)) \<Turnstile>\<^sub>d\<^sub>l (dl --s-- (Suc n))"
proof -
  have "\<forall>c \<in> (dl --s-- Suc n). (solve_pg s dl (Suc n)) \<Turnstile>\<^sub>c\<^sub>l\<^sub>s c"
    using assms solve_pg_Suc_models_cls[of s dl] by auto
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


lemma solve_pg_subset: 
  assumes "\<rho> \<Turnstile>\<^sub>d\<^sub>l (dl --s-- n)"
  shows "(solve_pg s dl n) p \<subseteq> \<rho> p"
using assms proof (induction n)
  case 0
  then show ?case
    using solve_pg_0_subset by metis
next
  case (Suc n)
  then have "\<rho> \<Turnstile>\<^sub>d\<^sub>l (dl --s-- n)"
    using solves_Suc by auto
  then have "solve_pg s dl n p \<subseteq> \<rho> p"
    using Suc by auto
  
  then show ?case oops

lemma solve_pg_0_below_model:
  assumes "\<rho> \<Turnstile>\<^sub>d\<^sub>l (dl --s-- 0)"
  shows "(solve_pg s dl 0) \<sqsubseteq>s\<sqsubseteq> \<rho>"
proof -
  define \<rho>'' :: "'a \<Rightarrow> 'b list set" where "\<rho>'' = solve_pg s dl 0"

  have "\<rho>'' \<noteq> \<rho> \<longrightarrow> \<rho>'' \<sqsubset>s\<sqsubset> \<rho>"
  proof 
    assume "\<rho>'' \<noteq> \<rho>"
    have "\<forall>p. \<rho>'' p \<subseteq> \<rho> p"
      using solve_pg_0_subset unfolding \<rho>''_def using assms(1) by force
    have "\<forall>p. s p > 0 \<longrightarrow> \<rho>'' p = {}"
      by (metis solve_pg_0_empty \<rho>''_def) (* Can be generalized to n! Should probably be a lemma. *)
    have "\<exists>p. least_rank_p_st (\<lambda>p. \<rho>'' p \<noteq> \<rho> p) p s"
      by (meson \<open>\<rho>'' \<noteq> \<rho>\<close> ext least_rank_p_st_exists)
    then obtain p where p_p: "least_rank_p_st (\<lambda>p. \<rho>'' p \<noteq> \<rho> p) p s"
      by auto
    have "\<rho>'' p \<subset> \<rho> p"
      by (metis (mono_tags, lifting) \<open>\<forall>p. \<rho>'' p \<subseteq> \<rho> p\<close> \<open>least_rank_p_st (\<lambda>p. \<rho>'' p \<noteq> \<rho> p) p s\<close> least_rank_p_st_def psubsetI)
    moreover
    have "\<forall>p'. s p' = s p \<longrightarrow> \<rho>'' p' \<subseteq> \<rho> p'"
      using \<open>\<forall>p. \<rho>'' p \<subseteq> \<rho> p\<close> by auto
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

(*
lemma 
  assumes "n \<le> m"
  assumes "(solve_pg s dl n) \<sqsubset>s\<sqsubset> \<rho>"
  shows "(solve_pg s dl m) \<sqsubset>s\<sqsubset> \<rho>"
proof -
  obtain p where p_p:
    "solve_pg s dl n p \<subset> \<rho> p"
    "(\<forall>p'. s p' = s p \<longrightarrow> solve_pg s dl n p' \<subseteq> \<rho> p')"
    "(\<forall>p'. s p' < s p \<longrightarrow> solve_pg s dl n p' = \<rho> p')"
    using assms unfolding lt_def by auto

  have "s p \<le> n"
    using p_p(1) sorry

  have "solve_pg s dl m p \<subset> \<rho> p"
    by (metis \<open>s p \<le> n\<close> assms(1) dual_order.trans p_p(1) solve_pg_agree_above)
  moreover
  have "(\<forall>p'. s p' = s p \<longrightarrow> solve_pg s dl m p' \<subseteq> \<rho> p')"
    by (metis \<open>s p \<le> n\<close> assms(1) dual_order.trans p_p(2) solve_pg_two_agree_above)
  moreover
  have "(\<forall>p'. s p' < s p \<longrightarrow> solve_pg s dl m p' = \<rho> p')"
    by (metis \<open>s p \<le> n\<close> assms(1) less_or_eq_imp_le order_trans p_p(3) solve_pg_agree_above)
  ultimately
  show "solve_pg s dl m \<sqsubset>s\<sqsubset> \<rho>"
    unfolding lt_def by auto
  oops
*)


(*
lemma gugugugugug123111342:
  assumes "\<forall>q. rnk q \<le> rnk p \<longrightarrow> (solve_pg s dl n) q = \<rho> q"
  assumes "(solve_pg s dl n) p \<subset> \<rho> q"
  assumes "n \<le> m"
  shows "\<rho> \<sqsubset>s\<sqsubset> (solve_pg s dl m)"
proof -
  show "\<rho> \<sqsubset>s\<sqsubset> (solve_pg s dl m)"
    unfolding 
qed
*)

lemma asdfsaddbvbfbfjfj1:
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

lemma asdfsaddbvbfbfjfj2:
  assumes "\<rho>''n \<sqsubset>s\<sqsubset> \<rho>"
  assumes "least_rank_p_st (\<lambda>p. \<rho>''n p \<noteq> \<rho> p) p s"
  shows "\<forall>p'. s p' = s p \<longrightarrow> \<rho>''n p' \<subseteq> \<rho> p'"
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
    by (metis (mono_tags, lifting))
qed

lemma asdfsaddbvbfbfjfj3:
  assumes "\<rho>''n \<sqsubset>s\<sqsubset> \<rho>"
  assumes "least_rank_p_st (\<lambda>p. \<rho>''n p \<noteq> \<rho> p) p s"
  shows "(\<forall>p'. s p' < s p \<longrightarrow> \<rho>''n p' = \<rho> p')"
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
    by metis
qed

lemma huafuihauihluihlfaw:
  assumes "P \<rho>"
  shows "\<^bold>\<Inter> {\<rho>'. P  \<rho>'} p \<subseteq> \<rho> p"
  by (metis (mono_tags, lifting) CollectI Inf_lower Inter'_def assms)

lemma jklaeasfdfsjlfsdajl:
  "(dl ==s== n) \<subseteq> (dl --s-- n)"
  by fastforce

lemma fiofihawfhiofkndd:
  assumes "dl2 \<subseteq> dl1"
  assumes "\<rho> \<Turnstile>\<^sub>d\<^sub>l dl1"
  shows "\<rho> \<Turnstile>\<^sub>d\<^sub>l dl2"
  by (meson assms(1) assms(2) in_mono solves_program_def)

lemma uhasfhfusdiafsdahu:
  assumes "\<rho> \<Turnstile>\<^sub>d\<^sub>l (dl --s-- n)"
  shows  "\<rho> \<Turnstile>\<^sub>d\<^sub>l (dl ==s== n)"
  by (meson assms fiofihawfhiofkndd jklaeasfdfsjlfsdajl)

lemma jklakjlfdjhkasdfjhkfjfd: (* Kan "Suc n" genereliseres *)
  assumes "\<rho> \<Turnstile>\<^sub>d\<^sub>l (dl --s-- Suc n)"
  assumes "(\<rho> \\s\\ n) = solve_pg s dl n"
  shows "solve_pg s dl (Suc n) p \<subseteq> \<rho> p"
  unfolding solve_pg.simps
  apply (rule huafuihauihluihlfaw)
  using assms uhasfhfusdiafsdahu by auto

lemma solve_pg_below_model:
  assumes "\<rho> \<Turnstile>\<^sub>d\<^sub>l (dl --s-- n)"
  shows "(solve_pg s dl n) \<sqsubseteq>s\<sqsubseteq> \<rho>"
  using assms
proof (induction n arbitrary: \<rho>)
  case 0
  then show ?case
    using solve_pg_0_below_model by blast
next
  case (Suc n)
  define \<rho>''n :: "'a \<Rightarrow> 'b list set" where "\<rho>''n = solve_pg s dl n"
  define \<rho>''n1 :: "'a \<Rightarrow> 'b list set" where "\<rho>''n1 = solve_pg s dl (Suc n)"

  have A: "\<rho>''n \<sqsubseteq>s\<sqsubseteq> \<rho>"
    using Suc.IH Suc.prems \<rho>''n_def solves_Suc by blast

  have B: "\<forall>p. s p \<le> n \<longrightarrow> \<rho>''n1 p = \<rho>''n p"
    using solve_pg_two_agree_above[of s _ "n" "Suc n" dl]
    unfolding \<rho>''n_def \<rho>''n1_def by auto

  have "\<rho>''n1 \<sqsubseteq>s\<sqsubseteq> \<rho>"
  proof (cases "\<rho>''n1 = \<rho>") (* Change to \<noteq> \<longrightarrow> \<sqsubset> structure *)
    case True
    then show ?thesis
      by (simp add: lte_def)
  next
    case False
    then have "\<exists>p. least_rank_p_st (\<lambda>p. \<rho>''n1 p \<noteq> \<rho> p) p s"
      using least_rank_p_st_exists[of "(\<lambda>p. \<rho>''n1 p \<noteq> \<rho> p)"] by force
    then obtain p where p_p: "least_rank_p_st (\<lambda>p. \<rho>''n1 p \<noteq> \<rho> p) p s"
      by blast
    then have dis: "\<rho>''n1 p \<noteq> \<rho> p"
      unfolding least_rank_p_st_def by auto
    define i where "i = s p"
    have "i < Suc n \<or> Suc n \<le> i"
      by auto
    then show ?thesis
    proof (rule disjE)
      assume "i < Suc n"
      then have "s p \<le> n"
        unfolding i_def by auto
      then have "\<rho>''n p \<noteq> \<rho> p"
        using dis B by auto

      have "\<rho>''n \<sqsubset>s\<sqsubset> \<rho>"
        by (metis A \<open>\<rho>''n p \<noteq> \<rho> p\<close> lte_def)
      moreover
      have "least_rank_p_st (\<lambda>p. \<rho>''n p \<noteq> \<rho> p) p s"
      proof -
        have "\<rho>''n p \<noteq> \<rho> p"
          by (simp add: \<open>\<rho>''n p \<noteq> \<rho> p\<close>)
        moreover
        have "\<forall>p'. \<rho>''n p' \<noteq> \<rho> p' \<longrightarrow> s p \<le> s p'"
          by (metis (mono_tags, lifting) B \<open>s p \<le> n\<close> le_trans least_rank_p_st_def nle_le p_p)
        ultimately
        show "least_rank_p_st (\<lambda>p. \<rho>''n p \<noteq> \<rho> p) p s"
          unfolding least_rank_p_st_def by auto
      qed
      ultimately
      have "\<rho>''n p \<subset> \<rho> p \<and>
           (\<forall>p'. s p' = s p \<longrightarrow> \<rho>''n(p') \<subseteq> \<rho>(p')) \<and>
           (\<forall>p'. s p' < s p \<longrightarrow> \<rho>''n(p') = \<rho>(p'))"
        using asdfsaddbvbfbfjfj1[of \<rho>''n s \<rho> p] asdfsaddbvbfbfjfj2[of \<rho>''n s \<rho> p] asdfsaddbvbfbfjfj3[of \<rho>''n s \<rho> p] by metis
      then have "\<rho>''n1 p \<subset> \<rho> p \<and>
           (\<forall>p'. s p' = s p \<longrightarrow> \<rho>''n1(p') \<subseteq> \<rho>(p')) \<and>
           (\<forall>p'. s p' < s p \<longrightarrow> \<rho>''n1(p') = \<rho>(p'))"
        using B \<open>s p \<le> n\<close> by auto
      then have "\<rho>''n1 \<sqsubset>s\<sqsubset> \<rho>"
        unfolding lt_def by auto
      then show "\<rho>''n1 \<sqsubseteq>s\<sqsubseteq> \<rho>"
        by (simp add: lte_def)
    next
      assume "Suc n \<le> i"
      have "\<rho> \<Turnstile>\<^sub>d\<^sub>l (dl --s-- Suc n)"
        using Suc.prems by auto
      moreover
      have "\<forall>p'. (\<rho> \\s\\ n) p' = (solve_pg s dl n) p'"
      proof
        fix p'
        show "(\<rho> \\s\\ n) p' = (solve_pg s dl n) p'"
        proof (cases "s p' \<le> n")
          case True
          then show ?thesis
            using B \<open>Suc n \<le> i\<close> \<rho>''n_def below_least_rank_p_st i_def p_p by fastforce
        next
          case False
          then show ?thesis
            by (metis exi_sol_n pred_val_mod_strata.simps)
        qed
      qed
      ultimately
      have "\<rho> \<in> {\<rho>'. \<rho>' \<Turnstile>\<^sub>d\<^sub>l (dl --s-- Suc n) \<and> (\<rho>' \\s\\ n) = solve_pg s dl n}"
        by auto
      then have "\<rho>''n1 p \<subseteq> \<rho> p"
        using jklakjlfdjhkasdfjhkfjfd
        using \<rho>''n1_def by fastforce 
      then have "\<rho>''n1 p \<subset> \<rho> p"
        using dis by auto
      moreover
      have "\<forall>p'. s p' = s p \<longrightarrow> \<rho>''n1 p' \<subseteq> \<rho> p'"
        using \<open>\<rho> \<in> {\<rho>'. \<rho>' \<Turnstile>\<^sub>d\<^sub>l (dl --s-- Suc n) \<and> (\<rho>' \s\ n) = solve_pg s dl n}\<close> \<rho>''n1_def jklakjlfdjhkasdfjhkfjfd by fastforce
      moreover
      have "\<forall>p'. s p' < s p \<longrightarrow> \<rho>''n1 p' = \<rho> p'"
        using below_least_rank_p_st p_p by fastforce
      ultimately
      have "\<rho>''n1 \<sqsubset>s\<sqsubset> \<rho>"
        unfolding lt_def by auto
      then show "\<rho>''n1 \<sqsubseteq>s\<sqsubseteq> \<rho>"
        unfolding lte_def by auto
    qed
  qed
  then show ?case
    unfolding \<rho>''n1_def by auto
qed

lemma solve_pg_0_least_solution:
  assumes "strat_wf s dl"
  shows "least_solution (solve_pg s dl 0) (dl --s-- 0) s"
  using assms least_solution_def solve_pg_0_below_model solve_pg_0_solves_dl by blast 

lemma solve_pg_Suc_least_solution:
  assumes "strat_wf s dl"
  shows "least_solution (solve_pg s dl (Suc n)) (dl --s-- (Suc n)) s"
  using assms least_solution_def solve_pg_Suc_solves_dl solve_pg_below_model by blast (* Man kunne styrke dette til least og ikke kun "slår \<rho>". Nok en god idé tbh. Meh. Du har nogle beviser på papir som nok er bedre *)

lemma solve_pg_least_solution':
  assumes "strat_wf s dl"
  shows "least_solution (solve_pg s dl n) (dl --s-- n) s"
  using assms solve_pg_0_least_solution solve_pg_Suc_least_solution by (cases n) auto

find_theorems Max "(\<le>)"


find_theorems finite name: induct

lemma finite_max_strata:
  assumes "finite dl"
  shows "(dl --s-- (max_strata s dl)) = dl"
  unfolding max_strata_def  apply auto
  subgoal for c
    apply (cases c)
    subgoal for p ids rhs
      apply (rule exI[of _ p])
      apply (rule exI[of _ ids])
      apply (rule exI[of _ rhs])
      apply auto
      using assms 
      apply -
      apply (rule Lattices_Big.linorder_class.Max.coboundedI[of "{s p |p. \<exists>ids rhs. Cls p ids rhs \<in> dl}" "s p"])
       apply auto
      apply (subgoal_tac " {s p |p. \<exists>ids rhs. Cls p ids rhs \<in> dl} = (\<lambda>c. (case c of Cls p ids rhs \<Rightarrow> s p)) ` dl")
       apply simp
      unfolding image_def 
      apply auto
      subgoal for pa idsa rhsa
        apply (rule bexI[of _ "Cls pa idsa rhsa"])
         apply auto
        done
      subgoal for c'
        apply (cases c')
        apply auto
        done
      done
    done
  done      

lemma solve_pg_least_solution:
  assumes "finite dl"
  assumes "strat_wf s dl"
  shows "least_solution (solve_pg s dl (max_strata s dl)) dl s"
proof -
  have "least_solution (solve_pg s dl (max_strata s dl)) (dl --s-- (max_strata s dl)) s"
    using solve_pg_least_solution' assms by auto
  then show ?thesis
    using finite_max_strata assms by metis
qed

  

(* René se her *)
(* Her er linket til det vi så på på nettet https://www.physicsforums.com/threads/difference-between-least-minimal-element.380114/ *)
(* En god bog: Priestly *)
lemma least_is_minimal:
  assumes "finite dl"
  assumes "strat_wf s dl"
  shows "least_solution \<sigma> dl s \<longleftrightarrow> minimal_solution \<sigma> dl s"
proof
  assume "least_solution \<sigma> dl s"
  then have \<sigma>_least: "\<sigma> \<Turnstile>\<^sub>d\<^sub>l dl" "(\<forall>\<sigma>'. \<sigma>' \<Turnstile>\<^sub>d\<^sub>l dl \<longrightarrow> \<sigma> \<sqsubseteq>s\<sqsubseteq> \<sigma>')"
    unfolding least_solution_def by auto
  then have "(\<nexists>\<sigma>'. \<sigma>' \<Turnstile>\<^sub>d\<^sub>l dl \<and> \<sigma>' \<sqsubset>s\<sqsubset> \<sigma>)"
    by (metis (full_types) \<open>\<forall>\<sigma>'. \<sigma>' \<Turnstile>\<^sub>d\<^sub>l dl \<longrightarrow> \<sigma> \<sqsubseteq>s\<sqsubseteq> \<sigma>'\<close> lt_def lte_def nat_neq_iff psubsetE)
  then show "minimal_solution \<sigma> dl s"
    unfolding minimal_solution_def using \<sigma>_least by metis
next
  assume "minimal_solution \<sigma> dl s"

  have "\<exists>\<sigma>'. least_solution \<sigma>' dl s"
    using solve_pg_least_solution assms by metis

  show "least_solution \<sigma> dl s"
    by (metis \<open>\<exists>\<sigma>'. least_solution \<sigma>' dl s\<close> \<open>minimal_solution \<sigma> dl s\<close> least_solution_def lte_def minimal_solution_def)
qed

lemma jklsakljaeafdsjkhdfsdfhjka:
  "(dl --s-- n) \<subseteq> dl"
  by auto

lemma xxasjkdfaskl:
  assumes "finite dl"
  shows "finite (dl --s-- n)"
  using assms finite_subset jklsakljaeafdsjkhdfsdfhjka by metis
  

lemma downward_solution:
  assumes "finite dl"
  assumes "n > m"
  assumes "strat_wf s dl"
  assumes "least_solution \<sigma> (dl --s-- n) s"
  shows "least_solution (\<sigma> \\s\\ m) (dl --s-- m) s"
proof (rule ccontr)
  assume a: "\<not> least_solution (\<sigma> \\s\\ m) (dl --s-- m) s"
  have strrr: "strat_wf s (dl --s-- m)"
    using assms downward_strat2 by auto
  have strrrr: "strat_wf s (dl --s-- n)"
    using assms downward_strat2 by auto
  from a have "\<not> minimal_solution  (\<sigma> \\s\\ m) (dl --s-- m) s"
    using least_is_minimal strrr assms(1) xxasjkdfaskl by metis
  moreover 
  have "(\<sigma> \\s\\ m) \<Turnstile>\<^sub>d\<^sub>l (dl --s-- m)"
    using assms downward_solves least_solution_def by blast
  ultimately
  have "(\<exists>\<sigma>'. \<sigma>' \<Turnstile>\<^sub>d\<^sub>l (dl --s-- m) \<and> (\<sigma>' \<sqsubset>s\<sqsubset> (\<sigma> \\s\\ m)))"
    unfolding minimal_solution_def by auto
  then obtain \<sigma>' where tt: "\<sigma>' \<Turnstile>\<^sub>d\<^sub>l (dl --s-- m)" and ttt: "(\<sigma>' \<sqsubset>s\<sqsubset> (\<sigma> \\s\\ m))"
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
  have "\<sigma>'' \<Turnstile>\<^sub>d\<^sub>l (dl --s-- n)"
    unfolding solves_program_def
  proof
    fix c
    assume a: "c \<in> (dl --s-- n)"
    then obtain p ids rhs where c_def: "c = Cls p ids rhs"
      by (cases c) auto

    have "\<sigma>'' \<Turnstile>\<^sub>c\<^sub>l\<^sub>s Cls p ids rhs"
      unfolding solves_cls_def
    proof
      fix \<eta>
      
      show "\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<sigma>'' \<eta>"
      proof (cases "s p \<le> m")
        case True
        then have "c \<in> (dl --s-- m)"
          using a c_def by auto
        then have gugu: "\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<sigma>' \<eta>"
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
    then show " \<sigma>'' \<Turnstile>\<^sub>c\<^sub>l\<^sub>s c"
      using c_def by blast
  qed
  ultimately
  have "\<not>minimal_solution \<sigma> (dl --s-- n) s"
    unfolding minimal_solution_def by auto
  then have "\<not>least_solution \<sigma> (dl --s-- n) s" 
    using least_is_minimal strrrr xxasjkdfaskl assms by metis
  then show "False"
    using assms by auto
qed

lemma downward_solution2:
  assumes "finite dl"
  assumes "strat_wf s dl"
  assumes "least_solution \<sigma> dl s"
  shows "least_solution (\<sigma> \\s\\ m) (dl --s-- m) s"
proof (rule ccontr)
  assume a: "\<not> least_solution (\<sigma> \\s\\ m) (dl --s-- m) s"
  have strrr: "strat_wf s (dl --s-- m)"
    using assms downward_strat2 by auto
  from a have "\<not> minimal_solution  (\<sigma> \\s\\ m) (dl --s-- m) s"
    using least_is_minimal strrr xxasjkdfaskl assms by metis  
  moreover 
  have "(\<sigma> \\s\\ m) \<Turnstile>\<^sub>d\<^sub>l (dl --s-- m)"
    using assms downward_solves2 least_solution_def by blast
  ultimately
  have "\<exists>\<sigma>'. \<sigma>' \<Turnstile>\<^sub>d\<^sub>l (dl --s-- m) \<and> \<sigma>' \<sqsubset>s\<sqsubset> \<sigma> \\s\\ m"
    unfolding minimal_solution_def by auto
  then obtain \<sigma>' where tt: "\<sigma>' \<Turnstile>\<^sub>d\<^sub>l (dl --s-- m)" and ttt: "(\<sigma>' \<sqsubset>s\<sqsubset> (\<sigma> \\s\\ m))"
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
  have "\<sigma>'' \<Turnstile>\<^sub>d\<^sub>l dl"
    unfolding solves_program_def
  proof
    fix c
    assume a: "c \<in> dl"
    then obtain p ids rhs where c_def: "c = Cls p ids rhs"
      by (cases c) auto

    have "\<sigma>'' \<Turnstile>\<^sub>c\<^sub>l\<^sub>s Cls p ids rhs"
      unfolding solves_cls_def
    proof
      fix \<eta>
      show "\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<sigma>'' \<eta>"
      proof (cases "s p \<le> m")
        case True
        then have "c \<in> (dl --s-- m)"
          using a c_def by auto
        then have gugu: "\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<sigma>' \<eta>"
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
            apply (smt (verit, ccfv_SIG) assms)
             apply (smt (z3) UNIV_I meaning_rh.simps(4))
            done
          done
      next
        case False
        then show ?thesis
          by (simp add: \<sigma>''_def)
      qed
    qed
    then show "\<sigma>'' \<Turnstile>\<^sub>c\<^sub>l\<^sub>s c"
      using c_def by blast
  qed
  ultimately
  have "\<not>minimal_solution \<sigma> dl s"
    unfolding minimal_solution_def by auto
  then have "\<not>least_solution \<sigma> dl s" 
    (* using least_is_minimal assms  *) (* This funny metis proof is not really what I intended..... *)
    by (metis \<open>\<forall>p'. s p' < s p \<longrightarrow> \<sigma>'' p' = \<sigma> p'\<close> \<open>\<sigma>'' \<Turnstile>\<^sub>d\<^sub>l dl\<close> \<open>\<sigma>'' p \<subset> \<sigma> p\<close> leD least_solution_def linorder_neq_iff lt_def lte_def psubset_imp_subset)
  then show "False"
    using assms by auto
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
  "summarizes_dl \<rho> (es, start, end) =
    (\<forall>\<pi> x q1 q2.
    \<pi> \<in> LTS.path_with_word es \<longrightarrow>
    LTS.get_start \<pi> = start \<longrightarrow>
    (x, q1, q2) \<in> def_path \<pi> start \<longrightarrow> 
    \<rho> \<Turnstile>\<^sub>q RD1\<langle>[Encode_Node (LTS.get_end \<pi>), Encode_Var x, Encode_Node_Q q1, Encode_Node q2]\<rangle>.)"

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
  shows "\<rho> \<Turnstile>\<^sub>q RD1\<langle>[Encode_Node (LTS.get_end (ss, w)), Encode_Var x, Encode_Node_Q q1, Encode_Node q2]\<rangle>."
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
  then have "\<rho> \<Turnstile>\<^sub>c\<^sub>l\<^sub>s RD1\<langle>[Encode_Node start, \<u>, DLElement Questionmark, Encode_Node start]\<rangle> :- [VAR [\<u>]] ."
    using assms(2) unfolding solves_program_def by auto 
   then have "\<forall>\<sigma>. \<lbrakk>RD1\<langle>[Encode_Node start, \<u>, DLElement Questionmark, Encode_Node start]\<rangle> :- [VAR [\<u>]] .\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho> \<sigma>"
     unfolding solves_cls_def by metis
   then have "\<lbrakk>RD1\<langle>[Encode_Node start, \<u>, DLElement Questionmark, Encode_Node start]\<rangle> :- [VAR [\<u>]] .\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho> (\<lambda>v. RD_Var x)"
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
    then have "\<rho> \<Turnstile>\<^sub>c\<^sub>l\<^sub>s RD1\<langle>[Encode_Node q2, Encode_Var x, Encode_Node_Q q1, Encode_Node q2]\<rangle> :- [] ."
      using 2(5) unfolding solves_program_def by auto
    then have "\<rho> \<Turnstile>\<^sub>q RD1\<langle>[Encode_Node q2, Encode_Var x, Encode_Node_Q q1, Encode_Node q2]\<rangle>."
      using solves_fact_query by metis 
    then show ?thesis
      by (simp add: LTS.get_end_def sq)
  next
    case False
    then have x_is_def: "(x, q1, q2) \<in> def_path (ss @ [s], w) start" using 2(7)
      using not_last_def_transition len by force
    then have "\<rho> \<Turnstile>\<^sub>q RD1\<langle>[Encode_Node (LTS.get_end (ss @ [s], w)), Encode_Var x, Encode_Node_Q q1, Encode_Node q2]\<rangle>."
    proof -
      have "(ss @ [s], w) \<in> LTS.path_with_word es"
        using 2(1) by auto
      moreover
      have "\<rho> \<Turnstile>\<^sub>d\<^sub>l (var_contraints \<union> ana_pg (es, start, end))"
        using 2(5) by auto
      moreover
      have "LTS.get_start (ss @ [s], w) = start"
        using 2(6)
        by (metis append_self_conv2 fst_conv LTS.get_start_def hd_append2 list.sel(1)) 
      moreover
      have "(x, q1, q2) \<in> def_path (ss @ [s], w) start"
        using x_is_def by auto
      ultimately
      show "\<rho> \<Turnstile>\<^sub>q RD1\<langle>[Encode_Node (LTS.get_end (ss @ [s], w)), Encode_Var x, Encode_Node_Q q1, Encode_Node q2]\<rangle>."
        using 2(3) by auto
    qed
    then have ind: "\<rho> \<Turnstile>\<^sub>q RD1\<langle>[Encode_Node s, Encode_Var x, Encode_Node_Q q1, Encode_Node q2]\<rangle>."
      by (simp add: LTS.get_end_def)
    define \<sigma> where "\<sigma> = undefined(the_\<u> := Encode_Var x, the_\<v> := Encode_Node_Q q1, the_\<w> := Encode_Node q2)"
    show ?thesis
    proof (cases l)
      case (Asg y e)
      have xy: "x \<noteq> y"
        using False Asg by auto
      then have xy': "\<rho> \<Turnstile>\<^sub>r\<^sub>h (Encode_Var x \<^bold>\<noteq> Encode_Var y)"
        by auto
      have "(s, y ::= e, s') \<in> es"
        using "2.hyps"(2) Asg by auto
      then have "RD1\<langle>[Encode_Node s', \<u>, \<v>, \<w>]\<rangle> :-
          [
            RD1[Encode_Node s, \<u>, \<v>, \<w>],
            \<u> \<^bold>\<noteq> (Encode_Var y)
          ]. \<in> ana_pg (es,start,end)"
        unfolding ana_pg.simps by force
      from this False have "\<rho> \<Turnstile>\<^sub>c\<^sub>l\<^sub>s RD1\<langle>[Encode_Node s', \<u>, \<v>, \<w>]\<rangle> :- [RD1 [Encode_Node s, \<u>, \<v>, \<w>], \<u> \<^bold>\<noteq> Encode_Var y] ."
        by (meson "2.prems"(2) UnCI solves_program_def)
      moreover have "subst_cls \<sigma> (RD1\<langle>[Encode_Node s', \<u>, \<v>, \<w>]\<rangle> :-
          [
            RD1[Encode_Node s, \<u>, \<v>, \<w>],
            \<u> \<^bold>\<noteq> (Encode_Var y)
          ].) = RD1\<langle>[Encode_Node s', Encode_Var x, Encode_Node_Q q1, Encode_Node q2]\<rangle> :- [RD1 [Encode_Node s,  Encode_Var x, Encode_Node_Q q1, Encode_Node q2], Encode_Var x \<^bold>\<noteq> Encode_Var y] ."
        unfolding \<sigma>_def by auto
      ultimately
      have "\<rho> \<Turnstile>\<^sub>c\<^sub>l\<^sub>s RD1\<langle>[Encode_Node s', Encode_Var x, Encode_Node_Q q1, Encode_Node q2]\<rangle>
                    :- [RD1 [Encode_Node s, Encode_Var x, Encode_Node_Q q1, Encode_Node q2], Encode_Var x \<^bold>\<noteq> Encode_Var y] ."
        unfolding solves_cls_def by (metis substitution_lemma_cls)
      then have "\<rho> \<Turnstile>\<^sub>c\<^sub>l\<^sub>s RD1\<langle>[Encode_Node s', Encode_Var x, Encode_Node_Q q1, Encode_Node q2]\<rangle> 
                         :- [RD1 [Encode_Node s, Encode_Var x, Encode_Node_Q q1, Encode_Node q2]] ."
        using xy' resolution_last_rh by (metis (no_types, lifting) Cons_eq_append_conv) 
      then have "\<rho> \<Turnstile>\<^sub>c\<^sub>l\<^sub>s RD1\<langle>[Encode_Node s', Encode_Var x, Encode_Node_Q q1, Encode_Node q2]\<rangle> :- [] ."
        using ind using resolution_last_rh_query[of \<rho> the_RD1 ] by (metis append.left_neutral) 
      then have "\<rho> \<Turnstile>\<^sub>q RD1\<langle>[Encode_Node s', Encode_Var x, Encode_Node_Q q1, Encode_Node q2]\<rangle>."
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
      then have "\<rho> \<Turnstile>\<^sub>c\<^sub>l\<^sub>s RD1\<langle>[Encode_Node s', \<u>, \<v>, \<w>]\<rangle> :- [RD1 [Encode_Node s, \<u>, \<v>, \<w>]] ."
        by (meson "2.prems"(2) UnCI solves_program_def)
      moreover have "subst_cls \<sigma> (RD1\<langle>[Encode_Node s', \<u>, \<v>, \<w>]\<rangle> :- [RD1[Encode_Node s, \<u>, \<v>, \<w>]].) =
                     RD1\<langle>[Encode_Node s', Encode_Var x, Encode_Node_Q q1, Encode_Node q2]\<rangle> :- [RD1[Encode_Node s, Encode_Var x, Encode_Node_Q q1, Encode_Node q2]]."
        unfolding \<sigma>_def by auto
      ultimately have "\<rho> \<Turnstile>\<^sub>c\<^sub>l\<^sub>s RD1\<langle>[Encode_Node s', Encode_Var x, Encode_Node_Q q1, Encode_Node q2]\<rangle> 
                               :- [RD1 [Encode_Node s, Encode_Var x, Encode_Node_Q q1, Encode_Node q2]] ."
        by (metis substitution_rule)
      then have "\<rho> \<Turnstile>\<^sub>q RD1\<langle>[Encode_Node s', Encode_Var x, Encode_Node_Q q1, Encode_Node q2]\<rangle>."
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
      then have "\<rho> \<Turnstile>\<^sub>c\<^sub>l\<^sub>s RD1\<langle>[Encode_Node s', \<u>, \<v>, \<w>]\<rangle> :- [RD1 [Encode_Node s, \<u>, \<v>, \<w>]] ."
        by (meson "2.prems"(2) UnCI solves_program_def)
      moreover
      have "subst_cls \<sigma> (RD1\<langle>[Encode_Node s', \<u>, \<v>, \<w>]\<rangle> :- [RD1 [Encode_Node s, \<u>, \<v>, \<w>]] .) =
            RD1\<langle>[Encode_Node s', Encode_Var x, Encode_Node_Q q1, Encode_Node q2]\<rangle>  :- [RD1 [Encode_Node s, Encode_Var x, Encode_Node_Q q1, Encode_Node q2]]."
        unfolding \<sigma>_def by auto
      ultimately 
      have "\<rho> \<Turnstile>\<^sub>c\<^sub>l\<^sub>s RD1\<langle>[Encode_Node s', Encode_Var x, Encode_Node_Q q1, Encode_Node q2]\<rangle> 
                    :- [RD1 [Encode_Node s, Encode_Var x, Encode_Node_Q q1, Encode_Node q2]] ."
        by (metis substitution_rule)
      from resolution_only_rh_query[OF this ind] have "\<rho> \<Turnstile>\<^sub>q RD1\<langle>[Encode_Node s', Encode_Var x, Encode_Node_Q q1, Encode_Node q2]\<rangle>."
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
   | the_CBV

datatype BV_var =
   the_\<uu> | the_\<vv>

abbreviation "BV == PosRh the_BV"
abbreviation NegRh_BV ("\<^bold>\<not>BV") where
  "\<^bold>\<not>BV \<equiv> NegRh the_BV"
abbreviation "kill == PosRh the_kill"
abbreviation NegRh_kill ("\<^bold>\<not>kill") where
  "\<^bold>\<not>kill \<equiv> NegRh the_kill"
abbreviation "gen == PosRh the_gen"

fun s_BV :: "BV_pred \<Rightarrow> nat" where 
  "s_BV the_kill = 0"
| "s_BV the_gen = 0"
| "s_BV the_BV = 1"
| "s_BV the_CBV = 2"

abbreviation BV_Cls :: "(BV_var, 'e) identifier list \<Rightarrow> (BV_pred, BV_var, 'e) righthand list \<Rightarrow> (BV_pred, BV_var, 'e) clause" ("BV\<langle>_\<rangle> :- _ .") where 
  "BV\<langle>args\<rangle> :- ls. \<equiv> Cls the_BV args ls"

abbreviation CBV_Cls :: "(BV_var, 'e) identifier list \<Rightarrow> (BV_pred, BV_var, 'e) righthand list \<Rightarrow> (BV_pred, BV_var, 'e) clause" ("CBV\<langle>_\<rangle> :- _ .") where
  "CBV\<langle>args\<rangle> :- ls. \<equiv> Cls the_CBV args ls"

abbreviation kill_Cls :: "(BV_var, 'e) identifier list \<Rightarrow> (BV_pred, BV_var, 'e) righthand list \<Rightarrow> (BV_pred, BV_var, 'e) clause" ("kill\<langle>_\<rangle> :- _ .") where 
  "kill\<langle>args\<rangle> :- ls. \<equiv> Cls the_kill args ls"

abbreviation genn_Cls :: "(BV_var, 'e) identifier list \<Rightarrow> (BV_pred, BV_var, 'e) righthand list \<Rightarrow> (BV_pred, BV_var, 'e) clause" ("gen\<langle>_\<rangle> :- _ .") where 
  "gen\<langle>args\<rangle> :- ls. \<equiv> Cls the_gen args ls"

abbreviation BV_Query :: "(BV_var, 'e) identifier list \<Rightarrow> (BV_pred, BV_var, 'e) query" ("BV\<langle>_\<rangle>.") where 
  "BV\<langle>args\<rangle>. \<equiv> (the_BV, args)"

abbreviation CBV_Query :: "(BV_var, 'e) identifier list \<Rightarrow> (BV_pred, BV_var, 'e) query" ("CBV\<langle>_\<rangle>.") where 
  "CBV\<langle>args\<rangle>. \<equiv> (the_CBV, args)"

datatype ('n,'v,'elem) BV_elem =
  BV_Node 'n
  | BV_Elem 'elem
  | BV_Action "'v action"

abbreviation \<uu> :: "(BV_var, 'a) identifier" where
  "\<uu> == DLVar the_\<uu>"

abbreviation \<vv> :: "(BV_var, 'a) identifier" where
  "\<vv> == DLVar the_\<vv>"

abbreviation Encode_Node_BV :: "'n \<Rightarrow> (BV_var, ('n, 'v, 'elem) BV_elem) identifier" where
  "Encode_Node_BV n == DLElement (BV_Node n)"

abbreviation Encode_Elem_BV :: "'elem \<Rightarrow> (BV_var, ('n, 'v, 'elem) BV_elem) identifier" where
  "Encode_Elem_BV e == DLElement (BV_Elem e)"

abbreviation Encode_Action_BV :: "'v action \<Rightarrow> (BV_var, ('n, 'v, 'elem) BV_elem) identifier" where
  "Encode_Action_BV \<alpha> == DLElement (BV_Action \<alpha>)"


section \<open>Forwards may-analysis\<close>

locale analysis_BV_forward_may =
  fixes pg :: "('n,'v) program_graph"
  fixes kill_set :: "('n,'v) edge \<Rightarrow> 'd::finite set"
  fixes gen_set :: "('n,'v) edge \<Rightarrow> 'd set"
  fixes d_init :: "'d set"
  assumes "finite (fst pg)"
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

fun ana_kill_BV :: "(('n, 'v) edge \<times> 'd) \<Rightarrow> (BV_pred, BV_var, ('n, 'v, 'd) BV_elem) clause set" where
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

definition ana_CBV :: "(BV_pred, BV_var, ('n, 'v, 'd) BV_elem) clause" where
  "ana_CBV = (CBV\<langle>[\<uu>,\<vv>]\<rangle> :- [\<^bold>\<not>BV [\<uu>,\<vv>]].)"

definition ana_pg_BV :: "(BV_pred, BV_var, ('n, 'v, 'd) BV_elem) clause set" where
  "ana_pg_BV = \<Union>(ana_edge_BV ` edge_set) 
               \<union> \<Union>(ana_init_BV ` d_init)
               \<union> \<Union>(ana_kill_BV ` (edge_set \<times> UNIV))
               \<union> \<Union>(ana_gen_BV ` (edge_set \<times> UNIV))
               \<union> {ana_CBV}"

fun summarizes_dl_BV :: "(BV_pred, ('n, 'v, 'd) BV_elem) pred_val \<Rightarrow> bool" where
  "summarizes_dl_BV \<rho> \<longleftrightarrow> 
     (\<forall>\<pi> d. \<pi> \<in> LTS.path_with_word edge_set \<longrightarrow> LTS.get_start \<pi> = start \<longrightarrow> d \<in> S_hat_path \<pi> d_init \<longrightarrow> 
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
  subgoal
    unfolding ana_CBV_def
    apply auto
    done
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

lemma jklfdsjkla1: "finite (\<Union> (ana_edge_BV ` edge_set))"
  by (smt (verit, best) analysis_BV_forward_may.ana_edge_BV.elims analysis_BV_forward_may_axioms analysis_BV_forward_may_def edge_set_def finite.emptyI finite.intros(2) finite_UN)


lemma jklfdsjkla2:
  assumes "x \<in> d_init"
  shows "finite (ana_init_BV x)"
  using assms using ana_init_BV_def by force

lemma jklfdsjkla3: "finite (\<Union> (ana_kill_BV ` (edge_set \<times> X)))"
  by (smt (verit, del_insts) analysis_BV_forward_may.ana_kill_BV.elims analysis_BV_forward_may_axioms analysis_BV_forward_may_def edge_set_def finite.emptyI finite.insertI finite_SigmaI finite_UN finite_code)


lemma jklfdsjkla4: "finite (\<Union> (ana_gen_BV ` (edge_set \<times> X)))"
   by (smt (verit, best) ana_gen_BV.elims analysis_BV_forward_may_axioms analysis_BV_forward_may_def edge_set_def finite.emptyI finite.insertI finite_SigmaI finite_UN finite_code)

lemma ana_pg_BV_finite: "finite ana_pg_BV"
  using jklfdsjkla1 jklfdsjkla2 jklfdsjkla3 jklfdsjkla4 unfolding ana_pg_BV_def by auto
    
lemma not_kill:
  assumes "d \<notin> kill_set(q\<^sub>o, \<alpha>, q\<^sub>s)"
  assumes "least_solution \<sigma> ana_pg_BV s_BV"
  shows "[BV_Node q\<^sub>o, BV_Action \<alpha>, BV_Node q\<^sub>s, BV_Elem d] \<notin> \<sigma> the_kill"
proof (rule)
  assume a: "[BV_Node q\<^sub>o, BV_Action \<alpha>, BV_Node q\<^sub>s, BV_Elem d] \<in> \<sigma> the_kill"
  have "finite ana_pg_BV"
    using ana_pg_BV_finite by auto
 
  then have "least_solution (\<sigma> \\s_BV\\ 0) (ana_pg_BV --s_BV-- 0) s_BV"
    using downward_solution2[of ana_pg_BV s_BV \<sigma> 0] assms(2) using ana_pg_BV_stratified by linarith
  then have "minimal_solution (\<sigma> \\s_BV\\ 0) (ana_pg_BV --s_BV-- 0) s_BV"
    using least_is_minimal[of]
    using ana_pg_BV_stratified downward_strat2 by (smt (verit) \<open>finite ana_pg_BV\<close> xxasjkdfaskl) 
  moreover
  define \<sigma>' where "\<sigma>' = (\<lambda>p. (if p = the_kill then ((\<sigma> \\s_BV\\ 0) the_kill) - {[BV_Node q\<^sub>o, BV_Action \<alpha>, BV_Node q\<^sub>s, BV_Elem d]} else (\<sigma> \\s_BV\\ 0) p))"

  have "\<sigma>' \<Turnstile>\<^sub>d\<^sub>l (ana_pg_BV --s_BV-- 0)"
    unfolding solves_program_def
  proof
    fix c
    assume a: "c \<in> (ana_pg_BV --s_BV-- 0)"
    then obtain p ids rhs where c_def: "c = Cls p ids rhs"
      by (cases c) auto

    have "\<sigma>' \<Turnstile>\<^sub>c\<^sub>l\<^sub>s Cls p ids rhs"
      unfolding solves_cls_def
    proof
      fix \<eta>
      have rhs_is: "rhs = []"
        using a
        apply auto
        unfolding ana_pg_BV_def
        apply auto
        using ana_init_BV_def
        unfolding ana_CBV_def
           apply auto
         apply (metis c_def clause.inject equals0D insertE)
        apply (metis c_def clause.inject empty_iff singletonD)
        done
      show "\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<sigma>' \<eta>"
      proof (cases "p = the_kill \<and> ids = [Encode_Node_BV q\<^sub>o, Encode_Action_BV \<alpha>, Encode_Node_BV q\<^sub>s, Encode_Elem_BV d]")
        case True
        then show ?thesis
          using a c_def assms(1) rhs_is
          apply auto
          unfolding ana_pg_BV_def
          apply auto
          unfolding ana_CBV_def 
             apply (auto simp add: ana_init_BV_def)
           apply (metis (no_types, lifting) BV_elem.inject(1) BV_elem.inject(2) BV_elem.inject(3) clause.inject equals0D identifier.inject(2) list.inject singletonD)
          apply (meson BV_pred.distinct clause.inject empty_iff singletonD)
          done
      next
        case False
        have "\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s (\<sigma> \\s_BV\\ 0) \<eta>"
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
                         apply (auto simp add: ana_init_BV_def ana_CBV_def)
                 apply (metis clause.inject equals0D eval_id.simps(2) list.inject singletonD)
                apply (meson BV_pred.distinct clause.inject empty_iff singletonD)
               apply (metis clause.inject equals0D eval_id.simps(2) list.inject singletonD)
              apply (meson BV_pred.distinct clause.inject empty_iff singletonD)
             apply (metis clause.inject equals0D eval_id.simps(2) list.inject singletonD)
            apply (meson BV_pred.distinct clause.inject empty_iff singletonD)
           apply (metis (no_types, lifting) clause.inject equals0D eval_id.simps(2) list.inject singletonD)
          apply (meson BV_pred.distinct clause.inject empty_iff singletonD)
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
  shows "\<rho> \<Turnstile>\<^sub>q BV\<langle>[Encode_Node_BV (LTS.get_end (ss, w)), Encode_Elem_BV d]\<rangle>."
  using assms 
proof (induction arbitrary: d rule: LTS.path_with_word_induct_reverse[OF assms(1)])
  case (1 s)
  have assms_2: "\<rho> \<Turnstile>\<^sub>d\<^sub>l ana_pg_BV"
    using assms(2) unfolding least_solution_def by auto

  from 1(1,3) have start_end: "LTS.get_end ([s], []) = start"
    using LTS.singleton_path_start_end[of s edge_set, OF 1(1)] by (metis LTS.get_end_def prod.sel(1))

  from 1 have "S_hat_path ([s], []) d_init = d_init"
    unfolding S_hat_path_def by auto
  then have "d \<in> d_init"
    using 1(4) by auto
  moreover
  from assms_2 have "\<forall>d\<in>d_init. \<rho> \<Turnstile>\<^sub>c\<^sub>l\<^sub>s BV\<langle>[Encode_Node_BV start, Encode_Elem_BV d]\<rangle> :- [] ."
    unfolding ana_pg_BV_def ana_init_BV_def solves_program_def by auto
  ultimately have "\<rho> \<Turnstile>\<^sub>c\<^sub>l\<^sub>s BV\<langle>[Encode_Node_BV start, Encode_Elem_BV d]\<rangle> :- [] ."
    by auto
  then show ?case
    using start_end solves_fact_query by metis
next
  case (2 qs qnminus1 w l qn)
  have "S_hat_path (qs @ [qnminus1], w) d_init \<subseteq>
        {d. \<rho> \<Turnstile>\<^sub>q BV\<langle>[Encode_Node_BV (LTS.get_end (qs @ [qnminus1], w)), Encode_Elem_BV d]\<rangle>.}"
    using 2
    by (metis (no_types, lifting) LTS.get_start_def hd_append2 list.sel(1) mem_Collect_eq prod.sel(1) self_append_conv2 subsetI) 
  then have f: "S_hat (qnminus1, l, qn) (S_hat_path (qs @ [qnminus1], w) d_init) \<subseteq>
             S_hat (qnminus1, l, qn) {d. \<rho> \<Turnstile>\<^sub>q BV\<langle>[Encode_Node_BV (LTS.get_end (qs @ [qnminus1], w)), Encode_Elem_BV d]\<rangle>.}"
    by (simp add: S_hat_mono)

  have "length qs = length w"
    using 2(1) LTS.path_with_word_lengths by metis
  then have "S_hat_path (qs @ [qnminus1, qn], w @ [l]) d_init = S_hat (qnminus1, l, qn) (S_hat_path (qs @ [qnminus1], w) d_init)"
    using S_hat_path_append[of qs w] by auto
  moreover 
  have "... = S_hat (qnminus1, l, qn) (S_hat_path (qs @ [qnminus1], w) d_init)"
    by simp
  moreover 
  have "... \<subseteq> S_hat (qnminus1, l, qn) {d. \<rho> \<Turnstile>\<^sub>q BV\<langle>[Encode_Node_BV qnminus1, Encode_Elem_BV d]\<rangle>.}"
    by (metis f LTS.get_end_def last_snoc prod.sel(1))
  ultimately 
  have "S_hat_path (qs @ [qnminus1, qn], w @ [l]) d_init \<subseteq> S_hat (qnminus1, l, qn) {d. \<rho> \<Turnstile>\<^sub>q BV\<langle>[Encode_Node_BV qnminus1, Encode_Elem_BV d]\<rangle>.}"
    by auto
  then have "d \<in> S_hat (qnminus1, l, qn) {d. solves_query \<rho> BV\<langle>[Encode_Node_BV qnminus1, Encode_Elem_BV d]\<rangle>.}"
    using 2(7) by auto
  then have "  d \<in> {d. \<rho> \<Turnstile>\<^sub>q BV\<langle>[Encode_Node_BV qnminus1, Encode_Elem_BV d]\<rangle>.} - kill_set (qnminus1, l, qn)
             \<or> d \<in> gen_set (qnminus1, l, qn)"
    unfolding S_hat_def by auto
  then have "\<rho> \<Turnstile>\<^sub>q BV\<langle>[Encode_Node_BV qn, Encode_Elem_BV d]\<rangle>."
  proof
    assume a: "d \<in> {d. \<rho> \<Turnstile>\<^sub>q BV\<langle>[Encode_Node_BV qnminus1, Encode_Elem_BV d]\<rangle>.} - kill_set (qnminus1, l, qn)"
    from a have a_1: "\<rho> \<Turnstile>\<^sub>q BV\<langle>[Encode_Node_BV qnminus1, Encode_Elem_BV d]\<rangle>."
      by auto
    moreover
    have e_in_pg: "(qnminus1, l, qn) \<in> edge_set"
      using "2.hyps"(2) by blast

    have "\<forall>c\<in>ana_edge_BV (qnminus1, l, qn). \<rho> \<Turnstile>\<^sub>c\<^sub>l\<^sub>s c"
      using 2(5) e_in_pg unfolding ana_pg_BV_def solves_program_def least_solution_def by blast
    then have "\<rho> \<Turnstile>\<^sub>c\<^sub>l\<^sub>s BV\<langle>[Encode_Node_BV qn, \<uu>]\<rangle> :- [BV [Encode_Node_BV qnminus1, \<uu>], \<^bold>\<not>kill [Encode_Node_BV qnminus1, Encode_Action_BV l, Encode_Node_BV qn, \<uu>]] ."
      by auto
    then have "\<rho> \<Turnstile>\<^sub>c\<^sub>l\<^sub>s BV\<langle>[Encode_Node_BV qn, Encode_Elem_BV d]\<rangle> 
                       :- [BV [Encode_Node_BV qnminus1, Encode_Elem_BV d],
                          \<^bold>\<not>kill [Encode_Node_BV qnminus1, Encode_Action_BV l, Encode_Node_BV qn, Encode_Elem_BV d]]."
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
    then have "\<rho> \<Turnstile>\<^sub>r\<^sub>h \<^bold>\<not>kill [Encode_Node_BV qnminus1, Encode_Action_BV l, Encode_Node_BV qn, Encode_Elem_BV d]" (* Could maybe be phrased better *)
      by auto
    ultimately
    show "\<rho> \<Turnstile>\<^sub>q BV\<langle>[Encode_Node_BV qn, Encode_Elem_BV d]\<rangle>."
      by (metis append.left_neutral append_Cons resolution_last_rh resolution_only_rh_query)
  next
    assume a: "d \<in> gen_set (qnminus1, l, qn)"
    have e_in_pg: "(qnminus1, l, qn) \<in> edge_set"
      using "2.hyps"(2) by blast

    have "\<forall>c\<in>ana_edge_BV (qnminus1, l, qn). \<rho> \<Turnstile>\<^sub>c\<^sub>l\<^sub>s c"
      using 2(5) e_in_pg unfolding ana_pg_BV_def solves_program_def least_solution_def by blast
    then have "\<rho> \<Turnstile>\<^sub>c\<^sub>l\<^sub>s BV\<langle>[Encode_Node_BV qn, \<uu>]\<rangle> :- [gen [Encode_Node_BV qnminus1, Encode_Action_BV l, Encode_Node_BV qn, \<uu>]] ."
      by auto
    then have "\<rho> \<Turnstile>\<^sub>c\<^sub>l\<^sub>s BV\<langle>[Encode_Node_BV qn, Encode_Elem_BV d]\<rangle> :- [gen [Encode_Node_BV qnminus1, Encode_Action_BV l, Encode_Node_BV qn, Encode_Elem_BV d]] ."
      using substitution_rule[of \<rho> _ "\<lambda>u. Encode_Elem_BV d" ]
      by force
    moreover
    have "\<forall>c\<in>\<Union>(ana_gen_BV ` (edge_set \<times> UNIV)). solves_cls \<rho> c"
      using 2(5) unfolding ana_pg_BV_def solves_program_def least_solution_def by auto
    then have "\<forall>c\<in>ana_gen_BV ((qnminus1, l, qn),d). solves_cls \<rho> c"
      using e_in_pg by blast
    then have "\<rho> \<Turnstile>\<^sub>c\<^sub>l\<^sub>s gen\<langle>[Encode_Node_BV qnminus1, Encode_Action_BV l, Encode_Node_BV qn, Encode_Elem_BV d]\<rangle> :- [] ."
      using a
      by auto
    ultimately
    show "\<rho> \<Turnstile>\<^sub>q BV\<langle>[Encode_Node_BV qn, Encode_Elem_BV d]\<rangle>."
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
  fixes pg :: "('n::finite,'v::finite) program_graph"
  assumes "finite (fst pg)"
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

interpretation interp: analysis_BV_forward_may pg kill_set_RD gen_set_RD d_init_RD 
  using analysis_BV_forward_may_def analysis_RD_axioms analysis_RD_def by blast 

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
    by (metis gugugug preds_lh.cases range_eqI)
qed

lemma def_path_S_hat_path: "def_path \<pi> start = interp.S_hat_path \<pi> d_init_RD"
  using interp.S_hat_path_def def_path_def def_var_UNIV_S_hat_edge_list by metis

fun summarizes_RD :: "(BV_pred, ('n,'v,('n,'v) triple) BV_elem) pred_val \<Rightarrow> bool" where
  "summarizes_RD \<rho> \<longleftrightarrow> (\<forall>\<pi> d. \<pi> \<in> LTS.path_with_word edge_set \<longrightarrow> LTS.get_start \<pi> = start \<longrightarrow> d \<in> def_path \<pi> start \<longrightarrow> 
                        \<rho> \<Turnstile>\<^sub>q BV\<langle>[Encode_Node_BV (LTS.get_end \<pi>), Encode_Elem_BV d]\<rangle>.)"

lemma RD_sound_again: 
  assumes "least_solution \<rho> (interp.ana_pg_BV) s_BV"
  shows "summarizes_RD \<rho>"
  using assms def_path_S_hat_path interp.sound_BV unfolding interp.summarizes_dl_BV.simps summarizes_RD.simps
  using edge_set_def in_mono interp.edge_set_def interp.start_def start_def by fastforce 

end


section \<open>Backwards may-analysis\<close>

locale analysis_BV_backwards_may =
  fixes pg :: "('n,'v) program_graph"
  fixes kill_set :: "('n,'v) edge \<Rightarrow> 'd::finite set"
  fixes gen_set :: "('n,'v) edge \<Rightarrow> 'd set"
  fixes d_init :: "'d set"
  assumes "finite (fst pg)"
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
                             \<rho> \<Turnstile>\<^sub>q BV\<langle>[Encode_Node_BV (LTS.get_start \<pi>), Encode_Elem_BV d]\<rangle>.)"

thm summarizes_dl_BV_def[of \<rho>]

lemma finite_pg_rev: "finite (fst pg_rev)"
  by (metis analysis_BV_backwards_may_axioms analysis_BV_backwards_may_def edge_set_def finite_imageI fst_conv pg_rev_def)

interpretation fa: analysis_BV_forward_may pg_rev "\<lambda>e. (kill_set (rev_edge e))" "(\<lambda>e. gen_set (rev_edge e))" d_init
  using analysis_BV_forward_may_def finite_pg_rev by metis

abbreviation ana_pg_BV where
  "ana_pg_BV == fa.ana_pg_BV"

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
  shows "\<rho> \<Turnstile>\<^sub>q BV\<langle>[Encode_Node_BV (LTS.get_start (ss, w)), Encode_Elem_BV d]\<rangle>."
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
  have "\<rho> \<Turnstile>\<^sub>q BV\<langle>[Encode_Node_BV (LTS.get_end (rev ss, rev w)), Encode_Elem_BV d]\<rangle>."
    using assms(4) fa.summarizes_dl_BV.simps by blast
  then show ?thesis
    by (metis LTS.get_end_def LTS.get_start_def fst_conv hd_rev rev_rev_ident)
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
  show "\<rho> \<Turnstile>\<^sub>q BV\<langle>[Encode_Node_BV (LTS.get_start \<pi>), Encode_Elem_BV d]\<rangle>."
    using summarizes_dl_BV_forwards_backwards'[of "fst \<pi>" "snd \<pi>" d \<rho>] using assms by auto
qed

lemma sound_rev_BV:
  assumes "least_solution \<rho> fa.ana_pg_BV s_BV"
  shows "summarizes_dl_BV \<rho>"
  using assms fa.sound_BV[of \<rho>] summarizes_dl_BV_forwards_backwards by metis

end


section \<open>Live Variables Analysis\<close>


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
  fixes pg :: "('n::finite,'v::finite) program_graph"
  assumes "finite (fst pg)"
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

interpretation interpb: analysis_BV_backwards_may pg kill_set_LV gen_set_LV d_init_LV
  using analysis_BV_backwards_may.intro analysis_LV_axioms analysis_LV_def by blast


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
        by (simp add: interpb.S_hat_def x_in_S_hat_\<pi>)
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
    obtain q1 \<alpha> q2 where a_split: "a = (q1, \<alpha>, q2)"
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
                         \<rho> \<Turnstile>\<^sub>q BV\<langle>[Encode_Node_BV (LTS.get_start \<pi>), Encode_Elem_BV d]\<rangle>.)"

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


section \<open>Forward must-analysis\<close>

locale analysis_BV_forwards_must =
  fixes pg :: "('n,'v) program_graph"
  fixes kill_set :: "('n,'v) edge \<Rightarrow> 'd::finite set" (* Is it OK to insists 'd finite? *)
  fixes gen_set :: "('n,'v) edge \<Rightarrow> 'd set"
  fixes d_init :: "'d set"
  assumes "finite (fst pg)"
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

fun summarizes_dl_BV_must :: "(BV_pred, ('n, 'v, 'd) BV_elem) pred_val \<Rightarrow> bool" where
  "summarizes_dl_BV_must \<rho> \<longleftrightarrow>
     (\<forall>\<pi>_end d.
        \<rho> \<Turnstile>\<^sub>q CBV\<langle>[Encode_Node_BV \<pi>_end, Encode_Elem_BV d]\<rangle>. \<longrightarrow>
          (\<forall>\<pi>. \<pi> \<in> LTS.path_with_word edge_set \<longrightarrow> LTS.get_start \<pi> = start \<longrightarrow> LTS.get_end \<pi> = \<pi>_end \<longrightarrow> d \<in> S_hat_path \<pi> d_init))"

interpretation a_may: analysis_BV_forward_may pg "\<lambda>e. UNIV - (kill_set e)" "(\<lambda>e. UNIV - gen_set e)" "UNIV - d_init"
  using analysis_BV_forward_may.intro analysis_BV_forwards_must_axioms analysis_BV_forwards_must_def by blast

lemma opposite_lemma:
  assumes "\<not>d \<in> a_may.S_hat_edge_list \<pi> (UNIV - d_init)"
  shows "d \<in> S_hat_edge_list \<pi> d_init"
  using assms proof (induction \<pi> rule: List.rev_induct)
  case Nil
  then show ?case by simp 
next
  case (snoc x xs)
  then show ?case
    unfolding a_may.S_hat_edge_list_def2
    by (simp add: S_hat_def a_may.S_hat_def)
qed

lemma opposite_lemma2:
  assumes "\<not>d \<in> a_may.S_hat_path \<pi> (UNIV - d_init)"
  shows "d \<in> S_hat_path \<pi> d_init"
  by (metis S_hat_path_def a_may.S_hat_path_def assms opposite_lemma)

lemma the_CBV_only_ana_CBV: "the_CBV \<notin> preds_dl (a_may.ana_pg_BV - {a_may.ana_CBV})"
  unfolding a_may.ana_pg_BV_def
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
    subgoal for c a aa b y
      apply (cases "y \<notin> kill_set (a, aa, b)")
       apply auto
      done
    done
  subgoal
    unfolding preds_dl_def
    apply auto
    subgoal for c a aa b y
      apply (cases "y \<notin> gen_set (a, aa, b)")
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
  assumes "[BV_Node q, BV_Elem d] \<in> \<rho> the_CBV"
  assumes "least_solution \<rho> a_may.ana_pg_BV s_BV"
  assumes a: "[BV_Node q, BV_Elem d] \<in> \<rho> the_BV"                  
  shows False
proof -
  have fin: "finite a_may.ana_pg_BV"
    using a_may.ana_pg_BV_finite by auto

  have "least_solution \<rho> a_may.ana_pg_BV s_BV"
    using assms(2) by force
  then have "minimal_solution \<rho> a_may.ana_pg_BV s_BV"
    using a_may.ana_pg_BV_stratified least_is_minimal[of a_may.ana_pg_BV s_BV \<rho>] fin by auto

  define \<rho>' where  "\<rho>' = (\<lambda>p. (if p = the_CBV then (\<rho> the_CBV) - {[BV_Node q, BV_Elem d]} else \<rho> p))"

  have CBV_solves: "\<rho>' \<Turnstile>\<^sub>c\<^sub>l\<^sub>s CBV\<langle>[\<uu>, \<vv>]\<rangle> :- [\<^bold>\<not>BV [\<uu>, \<vv>]] ."
    unfolding solves_cls_def
  proof 
    fix \<sigma>
    show "\<lbrakk>CBV\<langle>[\<uu>, \<vv>]\<rangle> :- [\<^bold>\<not>BV [\<uu>, \<vv>]] .\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho>' \<sigma>"
    proof (cases "\<sigma> the_\<uu> = BV_Node q \<and> \<sigma> the_\<vv> = BV_Elem d")
      case True
      then have "\<not> \<lbrakk>\<^bold>\<not>BV [\<uu>, \<vv>]\<rbrakk>\<^sub>r\<^sub>h \<rho>' \<sigma>"
        unfolding \<rho>'_def using a by auto
      then show ?thesis
        unfolding meaning_cls.simps by auto
    next
      case False
      then have "\<lbrakk>\<^bold>\<not>BV [\<uu>, \<vv>]\<rbrakk>\<^sub>r\<^sub>h \<rho>' \<sigma> \<longleftrightarrow> \<lbrakk>\<^bold>\<not>BV [\<uu>, \<vv>]\<rbrakk>\<^sub>r\<^sub>h \<rho> \<sigma>"
        by (simp add: \<rho>'_def)
      moreover
      from False have "\<lbrakk>CBV\<langle>[\<uu>, \<vv>]\<rangle>.\<rbrakk>\<^sub>l\<^sub>h \<rho>' \<sigma> \<longleftrightarrow> \<lbrakk>CBV\<langle>[\<uu>, \<vv>]\<rangle>.\<rbrakk>\<^sub>l\<^sub>h \<rho> \<sigma>"
        unfolding \<rho>'_def by auto
      moreover
      have "(\<forall>rh\<in>set [\<^bold>\<not>BV [\<uu>, \<vv>]]. \<lbrakk>rh\<rbrakk>\<^sub>r\<^sub>h \<rho> \<sigma>) \<longrightarrow> \<lbrakk>CBV\<langle>[\<uu>, \<vv>]\<rangle>.\<rbrakk>\<^sub>l\<^sub>h \<rho> \<sigma>"
      proof -
        have "CBV\<langle>[\<uu>, \<vv>]\<rangle> :- [\<^bold>\<not>BV [\<uu>, \<vv>]] . \<in> a_may.ana_pg_BV"
          unfolding a_may.ana_pg_BV_def a_may.ana_CBV_def by auto
        then have "solves_cls \<rho> (CBV\<langle>[\<uu>,\<vv>]\<rangle> :- [\<^bold>\<not>BV [\<uu>,\<vv>]].)"
          using assms(2) unfolding least_solution_def
          unfolding solves_program_def
          by auto
        then show "(\<forall>rh\<in>set [\<^bold>\<not>BV [\<uu>, \<vv>]]. \<lbrakk>rh\<rbrakk>\<^sub>r\<^sub>h \<rho> \<sigma>) \<longrightarrow> \<lbrakk>CBV\<langle>[\<uu>, \<vv>]\<rangle>.\<rbrakk>\<^sub>l\<^sub>h \<rho> \<sigma>"
          unfolding solves_cls_def meaning_cls.simps by auto
      qed
      ultimately
      show ?thesis 
        unfolding meaning_cls.simps by auto
    qed
  qed

  have \<rho>'_off_the_CBV: "\<forall>p. p \<noteq> the_CBV \<longrightarrow> \<rho>' p = \<rho> p"
    unfolding \<rho>'_def by auto
  moreover
  have "\<rho> \<Turnstile>\<^sub>d\<^sub>l (a_may.ana_pg_BV - {a_may.ana_CBV})"
    using assms(2) unfolding least_solution_def solves_program_def by auto
  moreover
  have "the_CBV \<notin> preds_dl (a_may.ana_pg_BV - {a_may.ana_CBV})"
    using the_CBV_only_ana_CBV .
  ultimately
  have "\<rho>' \<Turnstile>\<^sub>d\<^sub>l (a_may.ana_pg_BV - {a_may.ana_CBV})"
    by (simp add: agree_off_dl)
  then have "\<rho>' \<Turnstile>\<^sub>d\<^sub>l a_may.ana_pg_BV"
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
    using \<open>minimal_solution \<rho> a_may.ana_pg_BV s_BV\<close> minimal_solution_def
     by blast 
qed

lemma not_CBV2:
  assumes "least_solution \<rho> a_may.ana_pg_BV s_BV"
  assumes "\<rho> \<Turnstile>\<^sub>q CBV\<langle>[Encode_Node_BV q, Encode_Elem_BV d]\<rangle>."
  assumes "\<rho> \<Turnstile>\<^sub>q BV\<langle>[Encode_Node_BV q, Encode_Elem_BV d]\<rangle>."
  shows "False"
proof -
  have "[BV_Node q, BV_Elem d] \<in> \<rho> the_CBV"
    using assms(2)
    unfolding solves_query.simps
    unfolding meaning_query.simps
    by auto
  moreover
  have "[BV_Node q, BV_Elem d] \<in> \<rho> the_BV"
    using assms(3)
    unfolding solves_query.simps
    unfolding meaning_query.simps
    by auto
  ultimately
  show "False"
    using not_CBV[of q d \<rho>] assms(1) by auto
qed

lemma sound_BV_must':
  assumes "least_solution \<rho> a_may.ana_pg_BV s_BV"
  assumes "\<rho> \<Turnstile>\<^sub>q CBV\<langle>[Encode_Node_BV (LTS.get_end \<pi>), Encode_Elem_BV d]\<rangle>."
  assumes "\<pi> \<in> LTS.path_with_word edge_set"
  assumes "LTS.get_start \<pi> = start"
  shows "d \<in> S_hat_path \<pi> d_init"
proof -
  have m: "\<not> \<rho> \<Turnstile>\<^sub>q BV\<langle>[Encode_Node_BV (LTS.get_end \<pi>), Encode_Elem_BV d]\<rangle>."
    using assms(1,2) not_CBV2 by force
  have "\<not>d \<in> a_may.S_hat_path \<pi> (UNIV - d_init)"
    using a_may.sound_BV[of \<rho>, OF assms(1)]
    unfolding a_may.summarizes_dl_BV.simps
    apply -
    apply (erule_tac x=\<pi> in allE)
    apply (erule_tac x=d in allE)
    by (metis a_may.edge_set_def a_may.start_def assms(3,4) edge_set_def m start_def)
  then show "d \<in> S_hat_path \<pi> d_init"
    using opposite_lemma2 by auto
qed

lemma sound_CBV:
  assumes "least_solution \<rho> a_may.ana_pg_BV s_BV"
  shows "summarizes_dl_BV_must \<rho>"
  using assms unfolding summarizes_dl_BV_must.simps using sound_BV_must' by auto

end

section \<open>TODO: Canonical example of forwards must\<close>

end