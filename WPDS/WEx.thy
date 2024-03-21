theory WEx
  imports WPDS_Code
begin

(* Query specific part START *)
abbreviation(input) ctr_locN :: nat where "ctr_locN \<equiv> 3"
abbreviation(input) labelN :: nat where "labelN \<equiv> 2"
abbreviation(input) stateN :: nat where "stateN \<equiv> 3"
typedef ctr_loc = "{0 ..< ctr_locN}" by (auto intro!: exI[of _ 0])
typedef label = "{0 ..< labelN}" by (auto intro!: exI[of _ 0])
typedef state = "{0 ..< stateN}" by (auto intro!: exI[of _ 0])
setup_lifting type_definition_ctr_loc
setup_lifting type_definition_label
setup_lifting type_definition_state

lift_definition p1 :: ctr_loc is 0 by auto
lift_definition p2 :: ctr_loc is 1 by auto
lift_definition p3 :: ctr_loc is 2 by auto
lift_definition x :: label is 0 by auto
lift_definition y :: label is 1 by auto
lift_definition q1 :: state is 0 by auto
lift_definition q2 :: state is 1 by auto
lift_definition qf :: state is 2 by auto

(* Define rules of PDS, and the two P-automata *)
definition pds_rules :: "(ctr_loc, label, nat_inf) rule set" where
  "pds_rules = {
  ((p1, y), fin 1,(p1, push x y)),
  ((p1, x), fin 2,(p2, swap y)),
  ((p2, x), fin 3,(p3, pop)),
  ((p3, y), fin 4,(p2, swap x))}"

definition initial_automaton :: "((ctr_loc, state) WPDS2.state, label) transition set" where
  "initial_automaton = {
  ((Init p1, y, Noninit qf)),
  ((Init p2, y, Noninit qf)),
  ((Init p2, x, Init p2)),
  ((Init p3, x, Noninit qf))}"

definition final_automaton :: "((ctr_loc, state) WPDS2.state, label) transition set" where
  "final_automaton = {
  ((Init p2, y, Noninit q1)),
  ((Init p3, x, Noninit q1)),
  ((Noninit q1, y, Noninit q2))}"

definition final_ctr_loc where "final_ctr_loc = {}"
definition final_ctr_loc_st where "final_ctr_loc_st = {q2}"
definition initial_ctr_loc where "initial_ctr_loc = {}"
definition initial_ctr_loc_st where "initial_ctr_loc_st = {qf}"
(* Query specific part END *)

instantiation ctr_loc :: finite begin
instance by (standard, rule finite_surj[of "{0 ..< ctr_locN}" _ Abs_ctr_loc])
  (simp, metis Rep_ctr_loc Rep_ctr_loc_inverse imageI subsetI)
end
instantiation label :: finite begin
instance by (standard, rule finite_surj[of "{0 ..< labelN}" _ Abs_label])
  (simp, metis Rep_label Rep_label_inverse imageI subsetI)
end
instantiation state :: finite begin
instance by (standard, rule finite_surj[of "{0 ..< stateN}" _ Abs_state])
  (simp, metis Rep_state Rep_state_inverse imageI subsetI)
end

lift_definition (code_dt) ctr_loc_list :: "ctr_loc list" is "[0 ..< ctr_locN]" by (auto simp: list.pred_set)
lift_definition (code_dt) state_list :: "state list" is "[0 ..< stateN]" by (auto simp: list.pred_set)

instantiation ctr_loc :: enum begin
definition "enum_ctr_loc = ctr_loc_list"
definition "enum_all_ctr_loc P = list_all P ctr_loc_list"
definition "enum_ex_ctr_loc P = list_ex P ctr_loc_list"
instance by (standard, auto simp: enum_ctr_loc_def enum_all_ctr_loc_def enum_ex_ctr_loc_def
       ctr_loc_list_def image_iff distinct_map inj_on_def Abs_ctr_loc_inject
       list.pred_map list.pred_set list_ex_iff) (metis Abs_ctr_loc_cases)+
end

instantiation ctr_loc :: linorder begin
lift_definition less_ctr_loc :: "ctr_loc \<Rightarrow> ctr_loc \<Rightarrow> bool" is "(<)" .
lift_definition less_eq_ctr_loc :: "ctr_loc \<Rightarrow> ctr_loc \<Rightarrow> bool" is "(\<le>)" .
instance by (standard; transfer) auto
end

instantiation ctr_loc :: equal begin
lift_definition equal_ctr_loc :: "ctr_loc \<Rightarrow> ctr_loc \<Rightarrow> bool" is "(=)" .
instance by (standard; transfer) auto
end


lemma UNIV_members: "UNIV = {p1,p2,p3}"
  apply auto
  subgoal for x
    apply (cases x)
    apply auto
    apply (metis One_nat_def Suc_leI less_2_cases linorder_neqE_nat linorder_not_less numeral_3_eq_3 numerals(2) p1_def p2_def p3.abs_eq)
    done
  done

lemma UNIV_3: "card {p1,p2,p3} = 3"
  by (metis Suc_1 card.empty card_2_iff card_3_iff eval_nat_numeral(3) insert_absorb2 insert_not_empty numeral_1_eq_Suc_0 numerals(1) p1.rep_eq p2.rep_eq p3.rep_eq)

instantiation ctr_loc :: card_UNIV begin
definition "card_UNIV_ctr_loc = Phantom(ctr_loc) ctr_locN"
definition "finite_UNIV_ctr_loc = Phantom(ctr_loc) True"
instance apply standard
   apply auto
   apply (simp add: finite_UNIV_ctr_loc_def)
  apply (simp add: card_UNIV_ctr_loc_def)
  using UNIV_3 UNIV_members
  apply auto
  done
end

lift_definition (code_dt) label_list :: "label list" is "[0 ..< labelN]" by (auto simp: list.pred_set)
instantiation label :: enum begin
definition "enum_label = label_list"
definition "enum_all_label P = list_all P label_list"
definition "enum_ex_label P = list_ex P label_list"
instance by (standard, auto simp: enum_label_def enum_all_label_def enum_ex_label_def
       label_list_def image_iff distinct_map inj_on_def Abs_label_inject
       list.pred_map list.pred_set list_ex_iff) (metis Abs_label_cases)+
end

instantiation label :: linorder begin
lift_definition less_label :: "label \<Rightarrow> label \<Rightarrow> bool" is "(<)" .
lift_definition less_eq_label :: "label \<Rightarrow> label \<Rightarrow> bool" is "(\<le>)" .
instance by (standard; transfer) auto
end

instantiation label :: equal begin
lift_definition equal_label :: "label \<Rightarrow> label \<Rightarrow> bool" is "(=)" .
instance by (standard; transfer) auto
end

instantiation label :: card_UNIV begin
definition "card_UNIV_label == Phantom(label) labelN"
definition "finite_UNIV_label == Phantom(label) True"

instance apply standard sorry
end 

instantiation state :: equal begin
lift_definition equal_state :: "state \<Rightarrow> state \<Rightarrow> bool" is "(=)" .
instance by (standard; transfer) auto
end

instantiation state :: card_UNIV begin
definition "card_UNIV_state == Phantom(state) stateN"
definition "finite_UNIV_state == Phantom(state) True"

instance apply standard sorry
end 

instantiation WEx.state :: enum begin
definition "enum_state == state_list"
definition "enum_all_state P == list_all P state_list"
definition "enum_ex_state P == list_ex P state_list"

instance by (standard, auto simp: enum_state_def enum_all_state_def enum_ex_state_def
       state_list_def image_iff distinct_map inj_on_def Abs_state_inject
       list.pred_map list.pred_set list_ex_iff) (metis Abs_state_cases)+
end 



term "thing2 pds_rules initial_automaton final_automaton final_ctr_loc initial_ctr_loc"




(* The check function agrees with the encoded answer (Some True) 
   and therefore the proof succeeds as expected. *)

definition "thing3 == thing2 pds_rules initial_automaton final_automaton initial_ctr_loc final_ctr_loc = Some (fin 20)"

export_code thing3 in Haskell (* nat_inf :: enum is not a reasonable requirement *)

lemma
  "thing2 pds_rules initial_automaton final_automaton initial_ctr_loc final_ctr_loc = Some (fin 20)"
  by code_simp

lemma
  "thing2 pds_rules initial_automaton final_automaton initial_ctr_loc final_ctr_loc = Some (fin 20)"
  by eval (* nat_inf :: enum is not a reasonable requirement *)

end