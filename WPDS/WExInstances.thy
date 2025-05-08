theory WExInstances
  imports WExSetup
begin

(* Define rules of PDS, and the two P-automata *)

definition pds_rules :: "(ctr_loc, label, nat_inf) w_rule list" where
  "pds_rules = [
  ((p1, B), fin 1, (p1, push A B)),
  ((p1, A), fin 2, (p2, swap B)),
  ((p2, A), fin 3, (p3, pop)),
  ((p3, B), fin 4, (p2, swap A))]"
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


definition pds_rules_900 :: "(ctr_loc, label, nat_inf) w_rule list" where
  "pds_rules_900 = [
  ((p0, A), fin 2, (p0, push A A)),
  ((p1, B), fin 2, (p0, push A B))]"
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

value "run_WPDS_reach pds_rules_900 initial_100_automaton final_100_automaton initial_100_finals final_100_finals"

definition "ex3 == run_WPDS_reach pds_rules initial_automaton final_automaton initial_finals final_finals"

lemma
  "ex3 = Some (fin 3)"
  by eval

lemma
  "(ex3 = Some (fin 5)) \<longleftrightarrow> False"
  by eval

end
