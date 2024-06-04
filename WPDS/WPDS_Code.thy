theory WPDS_Code
  imports WPDS "Deriving.Derive" "P_Automata"
begin

term dioidLTS.accepts

fun accepts_code :: "('state \<times> 'label \<times> 'state) \<Rightarrow>f 'weight::bounded_idempotent_semiring \<Rightarrow> 'state set \<Rightarrow> ('state \<times> 'label list) \<Rightarrow> 'weight"  where
    "accepts_code ts finals (p,[]) = (if p \<in> finals then 1 else 0)"
 |  "accepts_code ts finals (p,(y#w)) = (\<Sum>{(ts $ (p,y,q) * (accepts_code ts finals (q,w))) | q. ts $ (p,y,q) \<noteq> 0})"

lemma accepts_code_correct[code]:
  fixes ts :: "('state \<times> ('label::finite) \<times> ('state::enum)) \<Rightarrow>f 'weight::bounded_idempotent_semiring"
  fixes finals :: "'state set"
  shows "dioidLTS.accepts ts finals (p,w) = accepts_code ts finals (p,w)"      
proof (induction w arbitrary: p)
  case Nil
  then show ?case
    unfolding accepts_code.simps using finite_WPDS.accepts_empty_iff[of "{}" ts]
    unfolding finite_WPDS_def by auto
next
  case (Cons a w)
  have "finite ({d * dioidLTS.accepts ts finals (q1, w) |q1 d. (p, ([a], d), q1) \<in> wts_to_monoidLTS ts})"
    unfolding wts_to_monoidLTS_def
    using finite_f_on_set[of UNIV "\<lambda>q. ts $ (p, a, q) * dioidLTS.accepts ts finals (q, w)"]
    by simp
  then have
    "\<Sum> {d * dioidLTS.accepts ts finals (q1, w) |q1 d. (p, ([a], d), q1) \<in> wts_to_monoidLTS ts} = 
     \<^bold>\<Sum> {d * dioidLTS.accepts ts finals (q1, w) |q1 d. (p, ([a], d), q1) \<in> wts_to_monoidLTS ts}"
    using finite_SumInf_is_sum[of "{d * dioidLTS.accepts ts finals (q1, w) |q1 d. (p, ([a], d), q1) \<in> wts_to_monoidLTS ts}"]
    by auto
  moreover
  have "\<Sum> {d * dioidLTS.accepts ts finals (q1, w) |q1 d. (p, ([a], d), q1) \<in> wts_to_monoidLTS ts} =
        \<Sum> {ts $ (p, a, q) * accepts_code ts finals (q, w) |q. True}"
    by (metis (no_types, opaque_lifting) local.Cons wts_label_d wts_to_monoidLTS_exists)
  moreover
  have "\<Sum> {ts $ (p, a, q) * accepts_code ts finals (q, w) |q. ts $ (p, a, q) \<noteq> 0} = 
                      \<Sum> {ts $ (p, a, q) * accepts_code ts finals (q, w) |q. True}"
    using sum_mult_not0_is_sum[of "\<lambda>q. True" "\<lambda>q. ts $ (p, a, q)" "\<lambda>q. accepts_code ts finals (q, w)"]
    by auto
  ultimately
  show ?case
    unfolding dioidLTS.accepts_step_distrib by auto
qed

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

thm WPDS_with_W_automata.pre_star_exec_correctness
lemma pre_star_exec_correctness:
  assumes "checking"
  shows "dioidLTS.accepts (WPDS_with_W_automata_no_assms.pre_star_exec' (w_rules \<Delta> W) ts) finals (Init p, w) =
         dioidLTS.weight_pre_star (WPDS.transition_rel wrules) (\<lambda>(p, w). dioidLTS.accepts ts finals (Init p, w)) (p, w)"
  using WPDS_with_W_automata.pre_star_exec_correctness[of "wrules" ts finals p w] checking_implies[OF assms]
  unfolding wrules_def by blast

(*
lemma augmented_WPDS_rules_code2[code]: "checking \<Delta> ts \<Longrightarrow> WPDS_with_W_automata_no_assms.augmented_WPDS_rules \<Delta> ts = (\<Union>((p, \<gamma>), d, (p', w)) \<in> \<Delta>. {((Init p, \<gamma>), d, (Init p', w))}) \<union> {((p,\<gamma>), d, (q, pop)) | p \<gamma> d q. ts $ (p,\<gamma>,q) = d}"
  *)


end

section \<open>Various code generation lemmas\<close>

(*global_interpretation wpds: WPDS_Code \<Delta> ts
  for \<Delta> :: "('ctr_loc::{enum,card_UNIV}, 'label::finite, 'weight::bounded_idempotent_semiring) rule set"
  and ts :: "(('ctr_loc, 'noninit::{enum,card_UNIV}) state, 'label) transition \<Rightarrow>f 'weight"
  defines pre_star = "WPDS_with_W_automata.pre_star_exec' \<Delta>"
  .
*)


(*definition "checking ts \<longleftrightarrow> (\<forall>q. is_Init q \<longrightarrow> (\<forall>p \<gamma>. ts $ (p, \<gamma>, q) = 0))"*)

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


(* declare accepts_def[code]*)
(* declare accepts_pre_star_check_def[code]*)
declare WPDS_Code.checking_def[code]
(*declare run_WPDS_reach_def[code]*)

(*lemma accepts_pre_star_check_code[code]: 
  "accepts_pre_star_check \<Delta> ts finals (p, w) = (if wpds.checking \<Delta> ts then Some (accepts_code (WPDS_Code.pre_star_exec' \<Delta> ts) finals (p, w)) else None)"
  unfolding accepts_pre_star_check_def accepts_code_correct[of "(wpds.pre_star_exec' \<Delta> ts)" finals p w, symmetric]
  unfolding wpds.accept_pre_star_exec0'_def WPDS_Code.pre_star_exec'_def
  using WPDS_with_W_automata_no_assms.accept_pre_star_exec0'_unfold[of \<Delta> ts]
  by simp  
*)


declare WPDS.lbl.simps[code]
declare WPDS.accept_pre_star_exec0_def[code]
declare Enum.enum_class.UNIV_enum[code]


lemma accepts_1_if_monoid_rtrancl_1:
  fixes ts :: "('s :: enum, 'l::finite) transition set"
  assumes "finite ts"
  assumes "(p, (v, 1 :: 'weight), q) \<in> monoid_rtrancl (wts_to_monoidLTS (ts_to_wts ts))"
  assumes "q \<in> finals"
  shows "dioidLTS.accepts (ts_to_wts ts) finals (p, v) = (1::'weight::bounded_idempotent_semiring)"
proof -
  have "\<And>q d. q \<in> finals \<Longrightarrow> (p, (v, d), q) \<in> monoid_rtrancl (wts_to_monoidLTS (ts_to_wts ts)) \<Longrightarrow> d = (1::'weight) \<or> d = 0"
    by (simp add: binary_aut_path_binary ts_to_wts_bin)
  then have "{d. \<exists>q. q \<in> finals \<and> (p, (v, d), q) \<in> monoid_rtrancl (wts_to_monoidLTS (ts_to_wts ts))} \<subseteq> {1 ::'weight, 0}"
    by blast
  moreover
  have "(p, (v, 1 :: 'weight), q) \<in> monoid_rtrancl (wts_to_monoidLTS (ts_to_wts ts))"
    using assms(2) by auto
  then have "(1 :: 'weight) \<in> {d. \<exists>q. q \<in> finals \<and> (p, (v, d), q) \<in> monoid_rtrancl (wts_to_monoidLTS (ts_to_wts ts))}"
    using assms by auto
  ultimately
  have "{d. \<exists>q. q \<in> finals \<and> (p, (v, d), q) \<in> monoid_rtrancl (wts_to_monoidLTS (ts_to_wts ts))} = {1 :: 'weight, 0} \<or> {d. \<exists>q. q \<in> finals \<and> (p, (v, d), q) \<in> monoid_rtrancl (wts_to_monoidLTS (ts_to_wts ts))} = {1 :: 'weight}"
    by blast
  moreover
  have "finite {1::'weight, 0}"
    by auto
  moreover
  have "\<Sum> {1::'weight, 0} = (1::'weight)"
    by (simp add: finite_SumInf_is_sum)
  ultimately
  have "\<^bold>\<Sum> {d. \<exists>q.  q \<in> finals \<and> (p, (v, d), q) \<in> monoid_rtrancl (wts_to_monoidLTS (ts_to_wts ts))} = (1::'weight)"
    by (auto simp add: finite_SumInf_is_sum)
  then show ?thesis
    by (simp add: WPDS.accepts_def2)
qed

lemma not_in_trans_star_implies_accepts_0:
  fixes ts :: "('s :: enum, 'label::enum) transition set"
  assumes "finite ts"
  shows "\<forall>q\<in>finals. (p, w, q) \<notin> LTS.trans_star ts \<Longrightarrow> dioidLTS.accepts (ts_to_wts ts) finals (p, w) = (0::'weight::bounded_idempotent_semiring)"
unfolding accepts_code_correct[of "ts_to_wts ts"]
proof (induct w arbitrary: p)
  case Nil
  then show ?case by simp (metis LTS.trans_star.trans_star_refl)
next
  case (Cons a w)
  have f:"finite {ts_to_wts ts $ (p, a, q) * accepts_code (ts_to_wts ts) finals (q, w) |q. ts_to_wts ts $ (p, a, q) \<noteq> 0}"
    by fastforce
  have A:"{ts_to_wts ts $ (p, a, x) * accepts_code (ts_to_wts ts) finals (x, w) |x. ts_to_wts ts $ (p, a, x) \<noteq> 0 \<and> (p, a, x) \<notin> ts} = {}"
    using ts_to_wts_not_member_is_0[OF assms] by blast
  have "\<And>p'. \<forall>q\<in>finals. (p, a # w, q) \<notin> LTS.trans_star ts \<Longrightarrow> (p, a, p') \<in> ts \<Longrightarrow> \<forall>q\<in>finals. (p', w, q) \<notin> LTS.trans_star ts"
    by (meson LTS.trans_star.trans_star_step)
  then have "\<And>p'. (p, a, p') \<in> ts \<Longrightarrow> accepts_code (ts_to_wts ts) finals (p', w) = (0::'weight::bounded_idempotent_semiring)"
    using Cons by blast
  then have "\<And>p'. (p, a, p') \<in> ts \<Longrightarrow> ts_to_wts ts $ (p, a, p') * accepts_code (ts_to_wts ts) finals (p', w) = (0::'weight::bounded_idempotent_semiring)"
    using mult_zero_right by fastforce
  then have B:"{ts_to_wts ts $ (p, a, x) * accepts_code (ts_to_wts ts) finals (x, w) |x. ts_to_wts ts $ (p, a, x) \<noteq> 0 \<and> (p, a, x) \<in> ts} \<subseteq> {0::'weight::bounded_idempotent_semiring}"
    by blast
  show ?case
    apply simp
    unfolding sum_split_f_P[OF f, of "\<lambda>q. (p, a, q) \<in> ts"] A
    using B sum_subset_singleton_0_is_0
    by simp
qed

lemma lang_aut_is_accepts_full_new:
  fixes ts :: "(('ctr_loc::enum, 'noninit::enum) state, 'label::enum) transition set"
  assumes "finite ts"
  shows "accepts_full (ts_to_wts ts) inits_set finals pv = (if pv \<in> P_Automaton.lang_aut ts Init finals then 1 else 0)"
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
  shows "(WPDS.weight_reach_set' :: _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> 'weight::bounded_idempotent_semiring) (w_rules \<Delta> W) (P_Automaton.lang_aut ts Init finals) (P_Automaton.lang_aut ts' Init finals') =
         WPDS.weight_reach' (w_rules \<Delta> W) (accepts_full (ts_to_wts ts) inits_set finals) (accepts_full (ts_to_wts ts') inits_set finals')"
proof -
  have bats: "binary_aut (ts_to_wts ts)"
    by (simp add: binary_aut_ts_to_wts)
  have bats': "binary_aut (ts_to_wts ts')"
    by (simp add: binary_aut_ts_to_wts)
  have c: "finite (w_rules \<Delta> W)"
    by (simp add: finite_w_rules)
  show ?thesis
    unfolding lang_aut_is_accepts_full_new[OF assms(1)] lang_aut_is_accepts_full_new[OF assms(2)]
    using finite_WPDS.weight_reach_set'_is_weight_reach'[of "w_rules \<Delta> W" "P_Automaton.lang_aut ts Init finals" 
        "P_Automaton.lang_aut ts' Init finals'", unfolded finite_WPDS_def, OF c]  
    by blast
qed

lemma WPDS_reach_exec_correct:
  fixes ts :: "(('ctr_loc :: {card_UNIV,enum}, 'noninit::{card_UNIV,enum}) state, 'label::enum) transition set"
  fixes ts' :: "(('ctr_loc, 'noninit) state, 'label) transition set"
  assumes "run_WPDS_reach \<Delta> W ts ts' finals finals' = Some (w :: 'weight::bounded_idempotent_semiring)"
  shows "w = (WPDS.weight_reach_set' (w_rules \<Delta> W) (P_Automaton.lang_aut ts Init finals) (P_Automaton.lang_aut ts' Init finals'))"
  using assms big_good_correctness_code[of "ts_to_wts ts" "w_rules \<Delta> W" "ts_to_wts ts'" inits_set finals finals', OF binary_aut_ts_to_wts[of ts]]
    weight_reach_set'_lang_aut_is_weight_reach'_accepts_full[of ts ts' \<Delta> W finals finals'] unfolding WPDS_Code.checking_def
  run_WPDS_reach'_def  inits_set_def mem_Collect_eq run_WPDS_reach_def
   finite_code by (metis (no_types, lifting) WPDS_Code.checking_def assms(1) run_WPDS_reach'_def finite_w_rules option.distinct(1) option.inject run_WPDS_reach_def) 

(*

(* TODO: ADAPT THE FOLLOWING TO DO WEIGHTED INTERSECTION:  *)
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

*)

end
