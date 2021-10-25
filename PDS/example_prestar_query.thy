theory example_prestar_query
  imports PDS "Deriving.Derive"
begin

global_interpretation pds: PDS_with_P_automaton \<Delta> F_ctr_loc F_ctr_loc_st
  for \<Delta> :: "('ctr_loc::{enum, linorder}, 'label::{finite, linorder}) rule set"
  and F_ctr_loc :: "('ctr_loc) set"
  and F_ctr_loc_st :: "('state::finite) set"
  defines pre_star = "PDS_with_P_automaton.pre_star_exec \<Delta>"
  and pre_star_check = "PDS_with_P_automaton.pre_star_exec_check \<Delta>"
  and accepts = "PDS_with_P_automaton.accepts F_ctr_loc F_ctr_loc_st"
  and accepts_pre_star_check = "PDS_with_P_automaton.accept_pre_star_exec_check \<Delta> F_ctr_loc F_ctr_loc_st"
  .

export_code pre_star in SML


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

(* TODO: A ctr_loc might be final (F) in initial_automaton but not in final_automaton. This cannot be expressed currently. *)
definition F_ctr_loc where "F_ctr_loc = {}"
definition F_ctr_loc_st where "F_ctr_loc_st = {q2,qf}"

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
   apply (metis ctr_loc.exhaust)+
  done
end


(* Can we return this value to terminal? *)
value "pds.accepts_inters F_ctr_loc F_ctr_loc_st (inters initial_automaton (pre_star pds_rules final_automaton)) (p2, [x,x,y])" \<comment> \<open>True\<close>

(* We don't want to specify the conf (p2, [x,x,y]), we want something like the following: *)
(* TODO: Define inters_non_empty to compute whether the intersection is non-empty. *)
(* value "pds.inters_non_empty F_ctr_loc F_ctr_loc_st (inters initial_automaton (pre_star pds_rules final_automaton))" \<comment> \<open>Should evaluate to: True\<close> *)


(* For post* something like this should work: *)
(* value "pds.accepts_inters F_ctr_loc F_ctr_loc_st (inters (post_star pds_rules initial_automaton) final_automaton) (p2, [x,x,y])" \<comment> \<open>True\<close> *)
(* value "pds.inters_non_empty F_ctr_loc F_ctr_loc_st (inters (post_star pds_rules initial_automaton) final_automaton)" \<comment> \<open>True\<close> *)
(* but post* is not priority now. *)

end