theory PDS_Code
  imports PDS (*"Containers.RBT_Set2"*) "Deriving.Derive"
begin

(*derive linorder operation*)


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

datatype ctr_loc = p0 | p1 | p2
datatype label = \<gamma>0 | \<gamma>1 | \<gamma>2
datatype state = s1 | s2
derive linorder ctr_loc
derive linorder label
derive linorder state
instantiation ctr_loc :: finite begin
instance by (standard, rule finite_subset[of _ "{p0,p1,p2}"]) (auto intro: ctr_loc.exhaust)
end
instantiation ctr_loc :: enum begin
definition "enum_ctr_loc = [p0,p1,p2]"
definition "enum_all_ctr_loc P = list_all P [p0,p1,p2]"
definition "enum_ex_ctr_loc P = list_ex P [p0,p1,p2]"
instance apply standard
     apply (auto simp: enum_ctr_loc_def enum_all_ctr_loc_def enum_ex_ctr_loc_def)
   apply (metis ctr_loc.exhaust)+
  done
end
instantiation label :: finite begin
instance by (standard, rule finite_subset[of _ "{\<gamma>0, \<gamma>1, \<gamma>2}"]) (auto intro: label.exhaust)
end
instantiation state :: finite begin
instance by (standard, rule finite_subset[of _ "{s1,s2}"]) (auto intro: state.exhaust)
end

text \<open>Example from https://doi.org/10.1007/10722167_20, Figure 1\<close>

definition \<Delta> :: "(ctr_loc, label) rule set" where
  "\<Delta> = {
  ((p0, \<gamma>0), (p1, push \<gamma>1 \<gamma>0)),
  ((p1, \<gamma>1), (p2, push \<gamma>2 \<gamma>0)),
  ((p2, \<gamma>2), (p0, swap \<gamma>1)),
  ((p0, \<gamma>1), (p0, pop))}"

definition \<P> :: "((ctr_loc, state, label) PDS.state, label) transition set" where
  "\<P> = {
  ((Ctr_Loc p0, \<gamma>0, Ctr_Loc_St s1)),
  ((Ctr_Loc_St s1, \<gamma>0, Ctr_Loc_St s2))}"

value "pre_star \<Delta> \<P>"

thm pds.theorem_3_2_exec_check

(* value "pre_star_check \<Delta> \<P>" *)

thm pds.theorem_3_2_exec

value "(Ctr_Loc p0, [\<gamma>0, \<gamma>0], Ctr_Loc_St s2) \<in> LTS.transition_star (pre_star \<Delta> \<P>)" \<comment> \<open>True\<close>
value "(Ctr_Loc p0, [\<gamma>0, \<gamma>1], Ctr_Loc_St s2) \<in> LTS.transition_star (pre_star \<Delta> \<P>)" \<comment> \<open>False\<close>
value "accepts {} {s2} (pre_star \<Delta> \<P>) (p0, [\<gamma>0, \<gamma>0])" \<comment> \<open>True\<close>
value "accepts {} {s1} (pre_star \<Delta> \<P>) (p0, [\<gamma>0, \<gamma>0])" \<comment> \<open>False\<close>
value "accepts {} {s2} (pre_star \<Delta> \<P>) (p0, [\<gamma>0, \<gamma>1])" \<comment> \<open>False\<close>

thm pds.accept_pre_star_correct_True
thm pds.accept_pre_star_correct_False


value "accepts_pre_star_check \<Delta> {} {s2} \<P> (p0, [\<gamma>0, \<gamma>0])" \<comment> \<open>Some True\<close>
value "accepts_pre_star_check \<Delta> {} {s1} \<P> (p0, [\<gamma>0, \<gamma>0])" \<comment> \<open>Some False\<close>
value "accepts_pre_star_check \<Delta> {} {s2} \<P> (p0, [\<gamma>0, \<gamma>1])" \<comment> \<open>None @AS: wrong example to get None, need to modify \<P>?\<close>

thm pds.accept_pre_star_correct_Some_True
thm pds.accept_pre_star_correct_Some_False
thm pds.accept_pre_star_correct_None

value "pds.accepts_inters {p0, p1, p2} {s1,s2} (inters (pre_star \<Delta> \<P>) (pre_star \<Delta> \<P>)) (p0, [\<gamma>0, \<gamma>0])"

(*
datatype ctr_loc = q
datatype label =
    m0 | m1 | m2 | m3 | m4 | m5 | m6 | m7 | m8
  | s0 | s1 | s2 | s3 | s4 | s5
  | main0 | main1
  | up0 | down0 | right0

derive linorder ctr_loc
derive linorder label

instantiation ctr_loc :: finite begin
instance
  by (standard, rule finite_subset[of _ "{q}"])
    (auto intro: ctr_loc.exhaust)
end
instantiation label :: finite begin
instance
  by (standard, rule finite_subset[of _ "{m0,m1,m2,m3,m4,m5,m6,m7,m8,s0,s1,s2,s3,s4,s5,main0,main1,up0,down0,right0}"])
    (auto intro: label.exhaust)
end

definition plotter where
  "plotter = {
              \<comment> \<open>procedure m\<close>
              ((q, m0), (q, swap m3)),              ((q, m0), (q, swap m7)),
              ((q, m3), (q, push s0 m4)),           ((q, m4), (q, push right0 m5)),
              ((q, m5), (q, swap m1)),              ((q, m5), (q, swap m6)),
              ((q, m6), (q, push m0 m1)),           ((q, m7), (q, push up0 m8)),
              ((q, m8), (q, push m0 m2)),           ((q, m2), (q, push down0 m1)),
              ((q, m1), (q, pop)),

              \<comment> \<open>procedure s\<close>
              ((q, s0), (q, swap s2)),              ((q, s0), (q, swap s3)),
              ((q, s2), (q, push up0 s4)),          ((q, s3), (q, pop)),
              ((q, s4), (q, push m0 s5)),           ((q, s5), (q, push down0 s1)),
              ((q, s1), (q, pop)),

              \<comment> \<open>procedure main\<close>
              ((q, main0), (q, push s0 main1)),     ((q, main1), (q, pop)),

              \<comment> \<open>procedures up, right, down\<close>
              ((q, up0), (q, pop)),                 ((q, down0), (q, pop)),
              ((q, right0), (q, pop))}"

term pre_star
value "pre_star plotter {}"
*)

end