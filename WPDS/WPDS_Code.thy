theory WPDS_Code
  imports WPDS "Deriving.Derive" "P_Automata"
begin

section \<open>Locale: WPDS_Code\<close>
locale WPDS_Code =
  fixes \<Delta> :: "('ctr_loc::enum, 'label::enum) rule set"
    and W :: "('ctr_loc, 'label) rule \<Rightarrow> 'weight::bounded_idempotent_semiring"
    and ts :: "(('ctr_loc, 'noninit::enum) state, 'label, 'weight::bounded_idempotent_semiring) w_transitions"
begin

definition "wrules = w_rules \<Delta> W"

definition "checking \<longleftrightarrow> (finite \<Delta> \<and> (\<forall>q. is_Init q \<longrightarrow> (\<forall>p \<gamma>. ts $ (p, \<gamma>, q) = 0)))"

lemma checking_implies: "checking \<Longrightarrow> WPDS_with_W_automata wrules ts"
  unfolding checking_def WPDS_with_W_automata_def finite_WPDS_def WPDS_with_W_automata_axioms_def 
  using finite_w_rules unfolding wrules_def by blast


definition "lbl = WPDS.lbl"

definition "augmented_WPDS_rules = WPDS_with_W_automata_no_assms.augmented_WPDS_rules"
definition "pre_star_exec' = WPDS_with_W_automata_no_assms.pre_star_exec'"
definition "accept_pre_star_exec0' = WPDS_with_W_automata_no_assms.accept_pre_star_exec0'"
declare accept_pre_star_exec0'_def[code]

lemma pre_star_exec_correctness:
  assumes "checking"
  shows "dioidLTS.accepts (WPDS_with_W_automata_no_assms.pre_star_exec' (w_rules \<Delta> W) ts) finals (Init p, w) =
         dioidLTS.weight_pre_star (WPDS.transition_rel wrules) (\<lambda>(p, w). dioidLTS.accepts ts finals (Init p, w)) (p, w)"
  using WPDS_with_W_automata.pre_star_exec_correctness[of "wrules" ts finals p w] checking_implies[OF assms]
  unfolding wrules_def by blast

end

section \<open>Various code generation lemmas\<close>

definition run_WPDS_reach' ::
   "('ctr_loc::{enum,card_UNIV}, 'label::enum) rule set \<Rightarrow> 
    (('ctr_loc, 'label) rule \<Rightarrow> 'weight::bounded_idempotent_semiring) \<Rightarrow> 
    (('ctr_loc, 'noninit::{enum,card_UNIV}) state, 'label) transition \<Rightarrow>f 'weight \<Rightarrow>
    (('ctr_loc, 'noninit) state, 'label) transition \<Rightarrow>f 'weight \<Rightarrow>
    ('ctr_loc, 'noninit) state set \<Rightarrow> 
    ('ctr_loc, 'noninit) state set \<Rightarrow> 'weight option" where
   "run_WPDS_reach' \<Delta> W ts ts' finals finals' = (if WPDS_Code.checking \<Delta> ts'
            then Some (weight_reach_sum_exec (wts_to_weightLTS (intersff ts (WPDS_with_W_automata_no_assms.pre_star_exec' (w_rules \<Delta> W) ts'))) {(p, p) |p. p \<in> inits_set} (finals \<times> finals')) 
            else None)"
definition "run_WPDS_reach \<Delta> W ts ts' = run_WPDS_reach' \<Delta> W (ts_to_wts ts) (ts_to_wts ts')"

declare WPDS_Code.checking_def[code]
declare WPDS.lbl.simps[code]
declare WPDS.accept_pre_star_exec0_def[code]
declare Enum.enum_class.UNIV_enum[code]

lemma not_in_trans_star_implies_accepts_0:
  fixes ts :: "('s :: enum, 'label::enum) transition set"
  assumes "finite ts"
  assumes "\<forall>q\<in>finals. (p, w, q) \<notin> LTS.trans_star ts"
  shows "dioidLTS.accepts (ts_to_wts ts) finals (p, w) = (0::'weight::bounded_idempotent_semiring)"
  using assms(2)
proof (induct w arbitrary: p)
  case Nil
  then show ?case by (simp add: dioidLTS.dioidLTS_accepts_code_Nil) (metis LTS.trans_star.trans_star_refl)
next
  case (Cons a w)
  have f:"finite {ts_to_wts ts $ (p, a, q) * dioidLTS.accepts (ts_to_wts ts) finals (q, w) |q. ts_to_wts ts $ (p, a, q) \<noteq> 0}"
    by fastforce
  have A:"{ts_to_wts ts $ (p, a, x) * dioidLTS.accepts (ts_to_wts ts) finals (x, w) |x. ts_to_wts ts $ (p, a, x) \<noteq> 0 \<and> (p, a, x) \<notin> ts} = {}"
    using ts_to_wts_not_member_is_0[OF assms(1)] by blast
  have "\<And>p'. \<forall>q\<in>finals. (p, a # w, q) \<notin> LTS.trans_star ts \<Longrightarrow> (p, a, p') \<in> ts \<Longrightarrow> \<forall>q\<in>finals. (p', w, q) \<notin> LTS.trans_star ts"
    by (meson LTS.trans_star.trans_star_step)
  then have "\<And>p'. (p, a, p') \<in> ts \<Longrightarrow> dioidLTS.accepts (ts_to_wts ts) finals (p', w) = (0::'weight::bounded_idempotent_semiring)"
    using Cons by blast
  then have "\<And>p'. (p, a, p') \<in> ts \<Longrightarrow> ts_to_wts ts $ (p, a, p') * dioidLTS.accepts (ts_to_wts ts) finals (p', w) = (0::'weight::bounded_idempotent_semiring)"
    using mult_zero_right by fastforce
  then have B:"{ts_to_wts ts $ (p, a, x) * dioidLTS.accepts (ts_to_wts ts) finals (x, w) |x. ts_to_wts ts $ (p, a, x) \<noteq> 0 \<and> (p, a, x) \<in> ts} \<subseteq> {0::'weight::bounded_idempotent_semiring}"
    by blast
  show ?case
    apply (simp add: dioidLTS.dioidLTS_accepts_code_Cons)
    unfolding sum_split_f_P[OF f, of "\<lambda>q. (p, a, q) \<in> ts"] A
    using B sum_subset_singleton_0_is_0
    by simp
qed

lemma lang_aut_is_accepts_full_new:
  fixes ts :: "(('ctr_loc::enum, 'noninit::enum) state, 'label::enum) transition set"
  assumes "finite ts"
  shows "accepts_full (ts_to_wts ts) finals pv = (if pv \<in> P_Automaton.lang_aut ts Init finals then 1 else 0)"
  unfolding accepts_full_def P_Automaton.lang_aut_def P_Automaton.accepts_aut_def inits_set_def 
  apply simp
  apply safe
  subgoal for p w q
    using monoid_rtrancl_one_if_trans_star[of "Init p" w q ts, OF _ assms]
          accepts_1_if_monoid_rtrancl_1[of ts "Init p" w q finals, OF assms]
    by blast
  using not_in_trans_star_implies_accepts_0[OF assms] by blast

lemma weight_reach_set'_lang_aut_is_weight_reach'_accepts_full:
  fixes ts :: "(('ctr_loc::enum, 'noninit::enum) state, 'label::enum) transition set"
  fixes ts' :: "(('ctr_loc, 'noninit) state, 'label) transition set"
  assumes "finite ts"
  assumes "finite ts'"
  shows "WPDS.weight_reach_set' (w_rules \<Delta> W) (P_Automaton.lang_aut ts Init finals) (P_Automaton.lang_aut ts' Init finals') =
         WPDS.weight_reach' (w_rules \<Delta> W) (accepts_full (ts_to_wts ts) finals) (accepts_full (ts_to_wts ts') finals')"
proof -
  have fin_w_rules: "finite (w_rules \<Delta> W)"
    by (simp add: finite_w_rules)
  show ?thesis
    unfolding lang_aut_is_accepts_full_new[OF assms(1)] lang_aut_is_accepts_full_new[OF assms(2)]
    using finite_WPDS.weight_reach_set'_is_weight_reach'[of "w_rules \<Delta> W" "P_Automaton.lang_aut ts Init finals" 
        "P_Automaton.lang_aut ts' Init finals'", unfolded finite_WPDS_def, OF fin_w_rules]
    by blast
qed

lemma WPDS_reach_exec_correct:
  fixes ts :: "(('ctr_loc :: {card_UNIV,enum}, 'noninit::{card_UNIV,enum}) state, 'label::enum) transition set"
  fixes ts' :: "(('ctr_loc, 'noninit) state, 'label) transition set"
  fixes W :: "('ctr_loc, 'label) rule \<Rightarrow> 'weight::bounded_idempotent_semiring"
  assumes "run_WPDS_reach \<Delta> W ts ts' finals finals' = Some w"
  shows "w = (WPDS.weight_reach_set' (w_rules \<Delta> W) (P_Automaton.lang_aut ts Init finals) (P_Automaton.lang_aut ts' Init finals'))"
  using assms big_good_correctness_code[of "ts_to_wts ts" "w_rules \<Delta> W" "ts_to_wts ts'" inits_set finals finals', OF binary_aut_ts_to_wts[of ts]]
    weight_reach_set'_lang_aut_is_weight_reach'_accepts_full[of ts ts' \<Delta> W finals finals'] unfolding WPDS_Code.checking_def
  run_WPDS_reach'_def  inits_set_def mem_Collect_eq run_WPDS_reach_def
   finite_code by (metis (no_types, lifting) WPDS_Code.checking_def assms(1) run_WPDS_reach'_def finite_w_rules option.distinct(1) option.inject run_WPDS_reach_def) 

end
