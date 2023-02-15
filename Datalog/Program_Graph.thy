theory Program_Graph imports "../LTS/LTS" Datalog begin


section \<open>Actions\<close>

datatype (fv_arith: 'v) arith =
  Integer int
  | Arith_Var 'v
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


subsection \<open>Types\<close>

type_synonym ('n,'v) edge = "'n \<times> 'v action \<times> 'n"

type_synonym ('n,'v) program_graph = "('n,'v) edge set \<times> 'n \<times> 'n"

type_synonym ('n,'v) config = "'n * 'v memory"


subsection \<open>Program Graph Locale\<close>

locale program_graph = 
  fixes pg :: "('n,'v) program_graph"
begin

definition edge_set where 
  "edge_set = fst pg"

definition start where
  "start = fst (snd pg)"

definition "end" where
  "end = snd (snd pg)"


subsubsection \<open>Execution Sequences\<close>

fun initial_config_of :: "('n,'v) config \<Rightarrow> bool" where
  "initial_config_of (q,\<sigma>) \<longleftrightarrow> q = start"

fun final_config_of :: "('n,'v) config \<Rightarrow> bool" where
  "final_config_of (q,\<sigma>) \<longleftrightarrow> q = end"

inductive exe_step :: "('n,'v) config \<Rightarrow> 'v action \<Rightarrow> ('n,'v) config \<Rightarrow> bool" where
  "(q1, \<alpha>, q2) \<in> edge_set \<Longrightarrow> sem_action \<alpha> \<sigma> = Some \<sigma>' \<Longrightarrow> exe_step (q1,\<sigma>) \<alpha> (q2,\<sigma>')"

end


subsection \<open>Finite Program Graph Locale\<close>

locale finite_program_graph = program_graph pg
  for pg :: "('n,'v) program_graph"
begin



end

end
