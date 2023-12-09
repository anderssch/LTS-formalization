theory WPDS_Code
  imports WPDS2 "Deriving.Derive"
begin

term WPDS_with_W_automata


definition "checking ts \<longleftrightarrow> (\<forall>q. is_Init q \<longrightarrow> (\<forall>p \<gamma>. ts $ (p, \<gamma>, q) = 0))"

global_interpretation wpds: WPDS_with_W_automata \<Delta> ts
  for \<Delta> :: "('ctr_loc::enum, 'label::finite, 'weight::bounded_idempotent_semiring) rule set"
  and ts :: "(('ctr_loc, 'noninit::enum) state \<times> 'label \<times> ('ctr_loc, 'noninit) state) \<Rightarrow>f 'weight"
  defines pre_star = "WPDS_with_W_automata.pre_star_exec' \<Delta>"
(* 
  Input:
     * A weighted pushdown system
     * A W-Automaton (with initial and non-initial states)
   Output:
     * A W-Automaton
 *)
    and pre_star_check = "if checking ts then Some (WPDS_with_W_automata.pre_star_exec' \<Delta> ts) else None"
(*
  Input:
     * A weighted pushdown system
     * A W-Automaton (with initial and non-initial states)
  Output:
     * A W-Automaton (with initial and non-initial states)
*)
    and inits = inits_set
(*
  Input:
    * No input
  Output:
    * Set of W-Automaton states
*)
    and accepts = "WPDS_with_W_automata.accepts_ts"
(*
  Input:
    * A W-Automaton
    * A set of final W-Automaton states
    * A configuration
  Output
    * A weight
*)
    and step_starp = "if checking ts then Some (WPDS_with_W_automata.pre_star_exec' \<Delta> ts) else None"
(*
  Input:
    * Pushdown Automaton
    * Configuration
    * Configuration
  Output:
    * Bool
*)
    and l_step_starp = "WPDS_with_W_automata.l_step_relp'"
(*
  Input:
    * Pushdown Automaton
    * Configuration
    * Weight
    * Configuration
  Output:
    * Bool
*)
    and accepts_pre_star_check = "if checking ts then Some (WPDS_with_W_automata.accept_pre_star_exec0' \<Delta> ts) else None"

term accepts_pre_star_check

(* TODO: CHECK IF THE TYPE OF accepts_pre_star_check IS OK *)
 


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
