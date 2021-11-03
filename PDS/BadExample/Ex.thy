theory Ex
  imports PDS.PDS_Code
begin

(* Query specific part START *)

(* List all control locations (in PDS), labels, and non-initial states in both P-automata *)
datatype ctr_loc = p1 | p2 | p3
definition ctr_loc_list where "ctr_loc_list = [p1,p2,p3]"
datatype label = x | y 
definition label_list where "label_list = [x,y]"
datatype state = q1 | q2 | qf
definition state_list where "state_list = [q1,q2,qf]"

(* Define rules of PDS, and the two P-automata *)
definition pds_rules :: "(ctr_loc, label) rule set" where
  "pds_rules = {
  ((p1, y), (p1, push x y)),
  ((p1, x), (p2, swap y)),
  ((p2, x), (p3, pop)),
  ((p3, y), (p2, swap x))}"
definition initial_automaton :: "((ctr_loc, state, label) PDS.state, label) transition set" where
  "initial_automaton = {
  ((Ctr_Loc p1, y, Ctr_Loc_St qf)),
  ((Ctr_Loc p2, y, Ctr_Loc_St qf)),
  ((Ctr_Loc p2, x, Ctr_Loc p2)),
  ((Ctr_Loc p3, x, Ctr_Loc_St qf))}"
definition final_automaton :: "((ctr_loc, state, label) PDS.state, label) transition set" where
  "final_automaton = {
  ((Ctr_Loc p2, y, Ctr_Loc_St q1)),
  ((Ctr_Loc p3, x, Ctr_Loc_St q1)),
  ((Ctr_Loc_St q1, y, Ctr_Loc_St q2))}"

definition final_ctr_loc where "final_ctr_loc = {}"
definition final_ctr_loc_st where "final_ctr_loc_st = {q2}"
definition initial_ctr_loc where "initial_ctr_loc = {}"
definition initial_ctr_loc_st where "initial_ctr_loc_st = {qf}"
(* Query specific part END *)


derive linorder ctr_loc
derive linorder label
instantiation ctr_loc :: finite begin
  instance by (standard, rule finite_subset[of _ "set ctr_loc_list"]) (auto intro: ctr_loc.exhaust simp: ctr_loc_list_def)
end
instantiation label :: finite begin
  instance by (standard, rule finite_subset[of _ "set label_list"]) (auto intro: label.exhaust simp: label_list_def)
end
instantiation state :: finite begin
  instance by (standard, rule finite_subset[of _ "set state_list"]) (auto intro: state.exhaust simp: state_list_def)
end
instantiation ctr_loc :: enum begin
definition "enum_ctr_loc = ctr_loc_list"
definition "enum_all_ctr_loc P = list_all P ctr_loc_list"
definition "enum_ex_ctr_loc P = list_ex P ctr_loc_list"
instance apply standard
     apply (auto simp: enum_ctr_loc_def enum_all_ctr_loc_def enum_ex_ctr_loc_def ctr_loc_list_def)
  subgoal for x by (cases x; simp)
  subgoal for P x by (cases x; simp)
  subgoal for P x by (cases x; simp)
  done
end

lemma
  "check pds_rules initial_automaton initial_ctr_loc initial_ctr_loc_st
                   final_automaton   final_ctr_loc   final_ctr_loc_st   = Some False"
  by eval

end