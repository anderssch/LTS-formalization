theory WPDS_Code
  imports WPDS "Deriving.Derive" "Pushdown_Systems.P_Automata"
begin

section \<open>Locale: WPDS_Code\<close>
locale WPDS_Code =
  fixes ts :: "(('ctr_loc::enum, 'noninit::enum) state, 'label::finite, 'weight::bounded_dioid) w_transitions"
begin

definition "checking \<longleftrightarrow> (\<forall>q. is_Init q \<longrightarrow> (\<forall>p \<gamma>. ts $ (p, \<gamma>, q) = 0))"

lemma checking_implies: "checking \<Longrightarrow> WPDS_with_W_automata (set \<Delta>) ts"
  unfolding checking_def WPDS_with_W_automata_def finite_WPDS_def WPDS_with_W_automata_axioms_def 
  by blast

definition "lbl = WPDS.lbl"

definition "augmented_WPDS_rules = WPDS_with_W_automata_no_assms.\<Delta>\<^sub>t\<^sub>s\<^sub>0"

definition "pre_star_exec' = WPDS_with_W_automata_no_assms.pre_star_exec'"

definition "accept_pre_star_exec0' = WPDS_with_W_automata_no_assms.accept_pre_star_exec0'"

context fixes finals :: "('ctr_loc, 'noninit) state set" begin
abbreviation accepts ("\<L>(_)" [1000] 1000) where "\<L>(ts') \<equiv> dioidLTS.accepts ts' finals"
lemma pre_star_exec_correctness:
  assumes "checking"
  shows "\<L>(WPDS_with_W_automata_no_assms.pre_star_exec' (set \<Delta>) ts) (Init p, w) =
         dioidLTS.weight_pre_star (WPDS.transition_rel (set \<Delta>)) (\<lambda>(p, w). \<L>(ts) (Init p, w)) (p, w)"
  using WPDS_with_W_automata.pre_star_exec_correctness[of "set \<Delta>" ts _ p w] checking_implies[OF assms]
  by blast
end
end

section \<open>Various code generation lemmas\<close>

definition run_WPDS_reach' ::
   "('ctr_loc::enum, 'label::finite, 'weight::bounded_dioid) w_rule list \<Rightarrow> 
    (('ctr_loc, 'noninit::enum) state, 'label, 'weight) w_transitions \<Rightarrow>
    (('ctr_loc, 'noninit) state, 'label, 'weight) w_transitions \<Rightarrow>
    ('ctr_loc, 'noninit) state set \<Rightarrow> 
    ('ctr_loc, 'noninit) state set \<Rightarrow> 'weight option" where
   "run_WPDS_reach' \<Delta> ts ts' finals finals' = (if WPDS_Code.checking ts'
            then Some (weight_reach_sum_exec \<lbrakk>ts \<inter>\<^sub>w (pre_star_exec (set \<Delta>) ts')\<rbrakk>\<^sub>w {(p, p) |p. p \<in> inits_set} (finals \<times> finals')) 
            else None)"

definition run_WPDS_reach ::
   "('ctr_loc::enum, 'label::finite, 'weight::bounded_dioid) w_rule list \<Rightarrow> 
    (('ctr_loc, 'noninit::enum) state, 'label) transition set \<Rightarrow>
    (('ctr_loc, 'noninit::enum) state, 'label) transition set \<Rightarrow>
    ('ctr_loc, 'noninit) state set \<Rightarrow> 
    ('ctr_loc, 'noninit) state set \<Rightarrow> 'weight option" where
 "run_WPDS_reach \<Delta> ts ts' = run_WPDS_reach' \<Delta> (ts_to_wts ts) (ts_to_wts ts')"

declare WPDS_Code.checking_def[code]
declare WPDS_Code.accept_pre_star_exec0'_def[code]
declare WPDS.lbl.simps[code]
declare WPDS.accept_pre_star_exec0_def[code]
declare Enum.enum_class.UNIV_enum[code]


context
  fixes \<Delta> :: "('ctr_loc::enum, 'label::finite, 'weight::bounded_dioid) w_rule list"
begin

interpretation finite_WPDS "(set \<Delta>)" 
  using finite_WPDS_def by auto

interpretation countable_dioidLTS transition_rel apply standard
  using countable_transition_rel .

lemma weight_reach_set'_lang_aut_is_weight_reach'_accepts_full:
  fixes ts :: "(('ctr_loc, 'noninit::enum) state, 'label) transition set"
  fixes ts' :: "(('ctr_loc, 'noninit) state, 'label) transition set"
  assumes "finite ts"
  assumes "finite ts'"
  shows "weight_reach_set (P_Automaton.lang_aut ts Init finals) (P_Automaton.lang_aut ts' Init finals') =
         weight_reach (accepts_full (ts_to_wts ts) finals) (accepts_full (ts_to_wts ts') finals')"
  unfolding lang_aut_is_accepts_full[OF assms(1)] lang_aut_is_accepts_full[OF assms(2)]
  using weight_reach_set_is_weight_reach by blast

lemma WPDS_reach_exec_correct:
  fixes ts :: "(('ctr_loc, 'noninit::enum) state, 'label) transition set"
  fixes ts' :: "(('ctr_loc, 'noninit) state, 'label) transition set"
  assumes "run_WPDS_reach \<Delta> ts ts' finals finals' = Some w"
  shows "w = (weight_reach_set (P_Automaton.lang_aut ts Init finals) (P_Automaton.lang_aut ts' Init finals'))"
proof -
  have "WPDS_Code.checking ((ts_to_wts ts')::(('ctr_loc, 'noninit) state, 'label, 'weight::bounded_dioid) w_transitions)"
    using assms unfolding run_WPDS_reach_def run_WPDS_reach'_def
    by (metis (no_types, lifting) option.distinct(1))
  then have "weight_reach_sum_exec \<lbrakk>(ts_to_wts ts) \<inter>\<^sub>w (WPDS_with_W_automata_no_assms.pre_star_exec' (set \<Delta>) (ts_to_wts ts'))\<rbrakk>\<^sub>w {(p, p) |p. p \<in> inits_set} (finals \<times> finals')
        = weight_reach (accepts_full (ts_to_wts ts) finals) (accepts_full (ts_to_wts ts') finals')"
    using WPDS_weight_reach'_is_weight_reach_sum_exec[of "ts_to_wts ts" "ts_to_wts ts'" inits_set finals finals', OF binary_aut_ts_to_wts[of ts]]
    unfolding inits_set_def mem_Collect_eq WPDS_Code.checking_def
    by simp
  then show ?thesis
    unfolding weight_reach_set'_lang_aut_is_weight_reach'_accepts_full[of ts ts' finals finals', unfolded finite_code, simplified]
    using assms unfolding run_WPDS_reach_def run_WPDS_reach'_def
    by (metis (lifting) option.distinct(1) option.inject)
qed
end

end
