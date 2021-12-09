theory Ex
  imports PDS.PDS_Code
begin

fun before where
  "before [] x y = False"
| "before (z # zs) x y = (y \<noteq> z \<and> (x = z \<or> before zs x y))"

lemma before_irrefl: "before xs x x \<Longrightarrow> False"
  by (induct xs) auto

lemma before_trans: "before xs x y \<Longrightarrow> before xs y z \<Longrightarrow> before xs x z"
  by (induct xs) auto

lemma before_asym: "before xs x y \<Longrightarrow> before xs y x \<Longrightarrow> False"
  by (induct xs) auto

lemma before_total_on: "x \<in> set xs \<Longrightarrow> y \<in> set xs \<Longrightarrow> before xs x y \<or> before xs y x \<or> x = y"
  by (induct xs) auto

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
  ((Ctr_Loc p1, y, Aut_State qf)),
  ((Ctr_Loc p2, y, Aut_State qf)),
  ((Ctr_Loc p2, x, Ctr_Loc p2)),
  ((Ctr_Loc p3, x, Aut_State qf))}"
definition final_automaton :: "((ctr_loc, state, label) PDS.state, label) transition set" where
  "final_automaton = {
  ((Ctr_Loc p2, y, Aut_State q1)),
  ((Ctr_Loc p3, x, Aut_State q1)),
  ((Aut_State q1, y, Aut_State q2))}"

definition final_ctr_loc where "final_ctr_loc = {}"
definition final_ctr_loc_st where "final_ctr_loc_st = {q2}"
definition initial_ctr_loc where "initial_ctr_loc = {}"
definition initial_ctr_loc_st where "initial_ctr_loc_st = {qf}"
(* Query specific part END *)

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

instantiation ctr_loc :: linorder begin
definition less_ctr_loc :: "ctr_loc \<Rightarrow> ctr_loc \<Rightarrow> bool" where
  "less_ctr_loc = before Enum.enum"
definition less_eq_ctr_loc :: "ctr_loc \<Rightarrow> ctr_loc \<Rightarrow> bool" where
  "less_eq_ctr_loc = sup (=) (<)"
instance
  using before_total_on[of _ "Enum.enum :: ctr_loc list"]
  by intro_classes
    (auto simp: less_eq_ctr_loc_def less_ctr_loc_def enum_UNIV
        dest: before_irrefl before_asym intro: before_trans)
end

lemma set_label_list: "set label_list = UNIV"
  apply (auto simp: label_list_def)
  subgoal for x by (cases x; simp)
  done
instantiation label :: linorder begin
definition less_label :: "label \<Rightarrow> label \<Rightarrow> bool" where
  "less_label = before label_list"
definition less_eq_label :: "label \<Rightarrow> label \<Rightarrow> bool" where
  "less_eq_label a b = (a = b \<or> a < b)"
instance
  using before_total_on[of _ "label_list"]
  by intro_classes
    (auto simp: less_eq_label_def less_label_def set_label_list
        dest: before_irrefl before_asym intro: before_trans)
end

lemma
  "check pds_rules initial_automaton initial_ctr_loc initial_ctr_loc_st
                   final_automaton   final_ctr_loc   final_ctr_loc_st   = Some False"
  by eval

end