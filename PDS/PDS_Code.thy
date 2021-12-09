theory PDS_Code
  imports PDS "Deriving.Derive"
begin

global_interpretation pds: PDS_with_P_automata \<Delta> F_ctr_loc F_ctr_loc_st
  for \<Delta> :: "('ctr_loc::{enum, linorder}, 'label::{finite, linorder}) rule set"
  and F_ctr_loc :: "('ctr_loc) set"
  and F_ctr_loc_st :: "('state::finite) set"
  defines pre_star = "PDS_with_P_automata.pre_star_exec \<Delta>"
  and pre_star_check = "PDS_with_P_automata.pre_star_exec_check \<Delta>"
  and accepts = "PDS_with_P_automata.accepts F_ctr_loc F_ctr_loc_st"
  and accepts_pre_star_check = "PDS_with_P_automata.accept_pre_star_exec_check \<Delta> F_ctr_loc F_ctr_loc_st"
  .

global_interpretation inter: Intersection_P_Automaton
  initial_automaton "pds.finals initial_F_ctr_loc initial_F_ctr_loc_st" pds.initials
  "pre_star \<Delta> final_automaton" "pds.finals final_F_ctr_loc final_F_ctr_loc_st"
  for \<Delta> :: "('ctr_loc::{enum, linorder}, 'label::{finite, linorder}) rule set"
  and initial_automaton :: "(('ctr_loc, 'state::finite, 'label) state, 'label) transition set"
  and initial_F_ctr_loc :: "'ctr_loc set"
  and initial_F_ctr_loc_st :: "'state set"
  and final_automaton :: "(('ctr_loc, 'state, 'label) state, 'label) transition set"
  and final_F_ctr_loc :: "'ctr_loc set"
  and final_F_ctr_loc_st :: "'state set"
  defines nonempty = "P_Automaton.nonempty
    (inters initial_automaton (pre_star \<Delta> final_automaton))
    (inters_finals (pds.finals initial_F_ctr_loc initial_F_ctr_loc_st)
                   (pds.finals final_F_ctr_loc final_F_ctr_loc_st))
    ((\<lambda>x. (x,x)) ` pds.initials)"
  .

definition "check \<Delta> I IF IF_st F FF FF_st =
  (if pds.initials \<subseteq> LTS.sources F then Some (nonempty \<Delta> I IF IF_st F FF FF_st) else None)"

lemma check_None: "check \<Delta> I IF IF_st F FF FF_st = None \<longleftrightarrow> \<not> (pds.initials \<subseteq> LTS.sources F)"
  unfolding check_def by auto

lemma check_Some: "check \<Delta> I IF IF_st F FF FF_st = Some b \<longleftrightarrow>
  (pds.initials \<subseteq> LTS.sources F \<and> b = (\<exists>p w p' w'.
     (p, w) \<in> pds.language IF IF_st I \<and>
     (p', w') \<in> pds.language FF FF_st F \<and>
     pds.step_starp \<Delta> (p, w) (p', w')))"
  unfolding check_def nonempty_def P_Automaton.nonempty_def
    inter.language_aut_alt inter.inters_language
    pds.language_aut_language
  by (auto 0 5 simp: pds.pre_star_exec_language_correct pds.pre_star_def image_iff
    elim!: bexI[rotated])

declare P_Automaton.mark.simps[code]

export_code check in SML

end
