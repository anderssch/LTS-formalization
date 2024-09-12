theory PDS_Code
  imports PDS "Deriving.Derive"
begin

global_interpretation pds: PDS_with_P_automata \<Delta> F_ctr_loc F_ctr_loc_st
  for \<Delta> :: "('ctr_loc::{enum, linorder}, 'label::{finite, linorder}) rule set"
    and F_ctr_loc :: "('ctr_loc) set"
    and F_ctr_loc_st :: "('state::finite) set"
  defines pre_star = "PDS_with_P_automata.pre_star_exec \<Delta>"
(*
  Input: 
    * Pushdown Automaton
    * P-Automaton
  Output:
    * P-Automaton (The pre_star automaton of the input)
*)
    and pre_star_check = "PDS_with_P_automata.pre_star_exec_check \<Delta>"
(*
  Input:
    * Pushdown Automaton
    * P-Automaton
  Output
    * P-Automaton option <-- (If inits \<subseteq> LTS.srcs A the pre_star automaton. Else None)
*)
    and inits = "PDS_with_P_automata.inits"
(*
  Input:
    * No input
  Output:
    * Set of P-Automaton states
*)
    and finals = "PDS_with_P_automata.finals F_ctr_loc F_ctr_loc_st"
(*
  Input:
    * Set of final ctr_loc states
    * Set of final non-initial states
  Output:
    * Set of P-Automaton states
*)
    and accepts = "PDS_with_P_automata.accepts F_ctr_loc F_ctr_loc_st"
(*
  Input:
    * Set of final ctr_loc states
    * Set of final non-initial states
    * P-automaton
    * Configuration
  Output:
    * Boolean
*)
    and language = "PDS_with_P_automata.lang F_ctr_loc F_ctr_loc_st"
    and step_starp = "rtranclp (LTS.step_relp (PDS.transition_rel \<Delta>))"
(*
  Input:
    * Pushdown Automaton
    * Configuration
    * Configuration
  Output:
    * Bool
*)
    and accepts_pre_star_check = "PDS_with_P_automata.accept_pre_star_exec_check \<Delta> F_ctr_loc F_ctr_loc_st"
  .

term step_starp
term language


global_interpretation inter: Intersection_P_Automaton
  initial_automaton Init "finals initial_F_ctr_loc initial_F_ctr_loc_st"
  "pre_star \<Delta> final_automaton" "finals final_F_ctr_loc final_F_ctr_loc_st"
  for \<Delta> :: "('ctr_loc::{enum, linorder}, 'label::{finite, linorder}) rule set"
  and initial_automaton :: "(('ctr_loc, 'state::finite, 'label) state, 'label) transition set"
  and initial_F_ctr_loc :: "'ctr_loc set"
  and initial_F_ctr_loc_st :: "'state set"
  and final_automaton :: "(('ctr_loc, 'state, 'label) state, 'label) transition set"
  and final_F_ctr_loc :: "'ctr_loc set"
  and final_F_ctr_loc_st :: "'state set"
  defines nonempty_inter = "P_Automaton.nonempty
    (inters initial_automaton (pre_star \<Delta> final_automaton))
    ((\<lambda>p. (Init p, Init p)))
    (inters_finals (finals initial_F_ctr_loc initial_F_ctr_loc_st)
                   (finals final_F_ctr_loc final_F_ctr_loc_st))"
  .

definition "check \<Delta> I IF IF_st F FF FF_st =
  (if pds.inits \<subseteq> LTS.srcs F then Some (nonempty_inter \<Delta> I IF IF_st F FF FF_st) else None)"

lemma check_None: "check \<Delta> I IF IF_st F FF FF_st = None \<longleftrightarrow> \<not> (inits \<subseteq> LTS.srcs F)"
  unfolding check_def by auto

lemma check_Some: "check \<Delta> I IF IF_st F FF FF_st = Some b \<longleftrightarrow>
  (inits \<subseteq> LTS.srcs F \<and> b = (\<exists>p w p' w'.
     (p, w) \<in> language IF IF_st I \<and>
     (p', w') \<in> language FF FF_st F \<and>
     step_starp \<Delta> (p, w) (p', w')))"
  unfolding check_def nonempty_inter_def P_Automaton.nonempty_def
    inter.lang_aut_alt inter.inters_lang
    pds.lang_aut_lang
  by (auto 0 5 simp: pds.pre_star_exec_lang_correct pds.pre_star_def image_iff
    elim!: bexI[rotated])

declare P_Automaton.mark.simps[code]

export_code check in SML

end
