theory WExInstances
  imports WExSetup
begin

(* Define rules of PDS, and the two P-automata *)
(*definition wpds_rules :: "(ctr_loc, label, nat_inf) w_rule set" where
  "wpds_rules = {
  ((p1, y), fin 1,(p1, push x y)),
  ((p1, x), fin 2,(p2, swap y)),
  ((p2, x), fin 3,(p3, pop)),
  ((p3, y), fin 4,(p2, swap x))}"*)
definition pds_rules :: "(ctr_loc, label) rule set" where
  "pds_rules = {
  ((p1, B), (p1, push A B)),
  ((p1, A), (p2, swap B)),
  ((p2, A), (p3, pop)),
  ((p3, B), (p2, swap A))}"
definition W :: "(ctr_loc, label) rule \<Rightarrow> nat_inf" where
  "W rule = (K$ infinity)
    (((p1, B), (p1, push A B)) $:= fin 1)
    (((p1, A), (p2, swap B))   $:= fin 2)
    (((p2, A), (p3, pop))      $:= fin 3)
    (((p3, B), (p2, swap A))   $:= fin 4) $ rule"

definition initial_automaton :: "((ctr_loc, state) WPDS.state, label) transition set" where
  "initial_automaton = {
  ((Init p1, B, Noninit qf)),
  ((Init p2, B, Noninit qf)),
  ((Init p2, A, Init p2)),
  ((Init p3, A, Noninit qf))}"
definition "initial_finals = {Noninit qf}"

definition final_automaton :: "((ctr_loc, state) WPDS.state, label) transition set" where
  "final_automaton = {
  ((Init p2, B, Noninit q1)),
  ((Init p3, A, Noninit q1)),
  ((Noninit q1, B, Noninit q2))}"
definition "final_finals = {Noninit q2}"

(* Query specific part END *)



definition pds_rules_900 :: "(ctr_loc, label) rule set" where
  "pds_rules_900 = {
  ((p0, A), (p0, push A A)),
  ((p1, B), (p0, push A B))}"
definition pds_rules_900_W :: "(ctr_loc, label) rule => nat_inf" where
  "pds_rules_900_W rule = (K$ infinity)
  (((p0, A), (p0, push A A)) $:= fin 2)
  (((p1, B), (p0, push A B)) $:= fin 2)
 $ rule"
definition initial_100_automaton :: "((ctr_loc, state) WPDS.state, label) transition set" where
  "initial_100_automaton = {
  ((Init p0, A, Noninit q2)),
  ((Init p1, A, Noninit q3))}"
definition initial_100_finals where "initial_100_finals = {Noninit q3}"
definition final_100_automaton :: "((ctr_loc, state) WPDS.state, label) transition set" where
  "final_100_automaton = {
  ((Init p0, B, Noninit q2)),
  ((Noninit q2, B, Noninit q2))}"
definition final_100_finals where "final_100_finals = {}"

value "thing2 pds_rules_900 pds_rules_900_W initial_100_automaton final_100_automaton initial_100_finals final_100_finals"

(*lemma "wpds_rules = w_rules pds_rules W"
  unfolding pds_rules_def W_def wpds_rules_def w_rules_def by eval*)


term "thing2 pds_rules W initial_automaton final_automaton initial_finals final_finals"


lemma[code_unfold]: "finite pds_rules"
  by simp
  (*unfolding pds_rules_def
  by simp
 
value "finite pds_rules"*)

(* The check function agrees with the encoded answer (Some True) 
   and therefore the proof succeeds as expected. *)


term "($\<circ>)"
thm finfun_comp2_const



definition "thing3 == run_WPDS_reach pds_rules W initial_automaton final_automaton initial_finals final_finals"


(*export_code thing3 in SML module_name WPDS_Example*)


value "thing3"


lemma
  "thing3 = Some (fin 3)" 
  by eval

lemma
  "thing3 = Some (fin 5)"
  by eval


end