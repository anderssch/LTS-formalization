theory WPDS_Code
  imports WPDS2 "Deriving.Derive"
begin

lemma countable_cong: "countable a \<Longrightarrow> a = b \<Longrightarrow> countable b"
  using back_subst[of countable] by blast

lemma rev_countable_subset: "countable B \<Longrightarrow> A \<subseteq> B \<Longrightarrow> countable A"
  using countable_subset .

lemma accepts_step_distrib:
  fixes ts :: "('state :: enum \<times> 'label :: finite \<times> 'state) \<Rightarrow>f 'weight::bounded_idempotent_semiring"
  fixes finals :: "'state set"
  shows "\<^bold>\<Sum>{d * (dioidLTS.accepts ts finals (q1,w))| q1 d. (p,([a],d),q1) \<in> wts_to_monoidLTS ts} = dioidLTS.accepts ts finals (p,a#w)"
proof -
  have "finite (wts_to_monoidLTS ts)"
    by (simp add: WPDS.finite_wts)
  then have "finite {(p, ([a], d), q1) | d q1. (p, ([a], d), q1) \<in> wts_to_monoidLTS ts}"
    by (rule rev_finite_subset) auto
  then have "finite ((\<lambda>(p, (a, d), q1). (q1, d)) ` {(p, ([a], d), q1) |d q1. (p, ([a], d), q1) \<in> wts_to_monoidLTS ts})"
    using finite_imageI by auto
  then have "finite {(q1, d) | q1 d. (p, ([a], d), q1) \<in> wts_to_monoidLTS ts}"
    by (rule back_subst[of finite]) (auto simp add: image_def)
  then have count1: "countable {(q1, d) | q1 d. (p, ([a], d), q1) \<in> wts_to_monoidLTS ts}"
    using countable_finite by auto

  have count2:
    "(\<And>q1 :: 'state. \<And>d :: 'weight.
         countable {((a, b), (q1, d)) |a b. a \<in> finals \<and> ((q1, (w, b), a) \<in> monoid_rtrancl (wts_to_monoidLTS ts))})"
  proof -
    fix q1 :: 'state
    fix d :: 'weight
    have "countable (monoid_rtrancl (wts_to_monoidLTS ts))"
      using countable_monoid_rtrancl countable_wts by blast
    then have "countable {(q1, (w, b), a) |a b. a \<in> finals \<and> (q1, (w, b), a) \<in> monoid_rtrancl (wts_to_monoidLTS ts)}"
      by (rule rev_countable_subset) auto
    then have "countable ((\<lambda>(q1, (w, b), a). ((a, b), (q1, d))) ` {(q1, (w, b), a) |a b. a \<in> finals \<and> (q1, (w, b), a) \<in> monoid_rtrancl (wts_to_monoidLTS ts)})"
      using countable_image by fastforce
    then show "countable {((a, b), (q1, d)) |a b. a \<in> finals \<and> ((q1, (w, b), a) \<in> monoid_rtrancl (wts_to_monoidLTS ts))}"
      by (rule rev_countable_subset) (auto simp add: image_def)
  qed

  have "\<^bold>\<Sum>{d * (dioidLTS.accepts ts finals (q,w))| q d. (p,([a],d),q) \<in> wts_to_monoidLTS ts} =
        \<^bold>\<Sum> {d * (\<^bold>\<Sum> {u | q u. q \<in> finals \<and> (q1, (w, u), q) \<in> monoid_rtrancl (wts_to_monoidLTS ts)}) |q1 d. (p, ([a], d), q1) \<in> wts_to_monoidLTS ts}"
    unfolding dioidLTS.accepts_def by auto
  also
  have "... = \<^bold>\<Sum> {d * u | q u q1 d. q \<in> finals \<and> (q1, (w, u), q) \<in> monoid_rtrancl (wts_to_monoidLTS ts) \<and> (p, ([a], d), q1) \<in> wts_to_monoidLTS ts}"
    using SumInf_of_SumInf_left_distr[of "\<lambda>(q1,d). (p, ([a], d), q1) \<in> wts_to_monoidLTS ts" "\<lambda>(q,u) (q1,d). q \<in> finals \<and> (q1, (w, u), q) \<in> monoid_rtrancl (wts_to_monoidLTS ts)"
    "\<lambda>(q1,d). d" "\<lambda>(q,u) (q1,d). u",simplified] count1 count2 by auto
  also
  have "... = \<^bold>\<Sum> {d * u | q u q1 d. q \<in> finals \<and> (p, ([a], d), q1) \<in> wts_to_monoidLTS ts \<and> (q1, (w, u), q) \<in> monoid_rtrancl (wts_to_monoidLTS ts)}"
    by meson
  also
  have "... = (\<^bold>\<Sum> {d' | d' q. q \<in> finals \<and> (p, (a # w, d'), q) \<in> monoid_rtrancl (wts_to_monoidLTS ts)})"
    apply (rule arg_cong[of _ _ "\<^bold>\<Sum>"])
    using monoid_rtrancl_intros_Cons mstar_wts_cons apply fastforce
    done
  also
  have "... = dioidLTS.accepts ts finals (p,a#w)"
    unfolding dioidLTS.accepts_def by auto

  finally show ?thesis 
    by auto
qed



fun accepts_code :: "('state \<times> 'label \<times> 'state) \<Rightarrow>f 'weight::bounded_idempotent_semiring \<Rightarrow> 'state set \<Rightarrow> ('state \<times> 'label list) \<Rightarrow> 'weight"  where
    "accepts_code ts finals (p,[]) = (if p \<in> finals then 1 else 0)"
 |  "accepts_code ts finals (p,(y#w)) = (\<Sum>{(ts $ (p,y,q) * (accepts_code ts finals (q,w))) | q. ts $ (p,y,q) \<noteq> 0})"

lemma accepts_code_correct[code]:
  fixes ts :: "('state \<times> ('label::finite) \<times> ('state::enum)) \<Rightarrow>f 'weight::bounded_idempotent_semiring"
  fixes finals :: "'state set"
  shows"dioidLTS.accepts ts finals (p,w) = accepts_code ts finals (p,w)"      
proof (induction w arbitrary: p)
  case Nil
  then show ?case
    unfolding accepts_code.simps using WPDS2.finite_WPDS.accepts_empty_iff[of "{}" ts]
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
    unfolding accepts_step_distrib by auto
qed


locale WPDS_Code =
  fixes \<Delta> :: "('ctr_loc::enum, 'label::finite, 'weight::bounded_idempotent_semiring) rule set"
    and ts :: "(('ctr_loc, 'noninit::enum) state, 'label, 'weight::bounded_idempotent_semiring) w_transitions"
begin
definition "checking rules A \<longleftrightarrow> (finite rules \<and> (\<forall>q. is_Init q \<longrightarrow> (\<forall>p \<gamma>. A $ (p, \<gamma>, q) = 0)))"
lemma checking_implies: "checking \<Delta> ts \<Longrightarrow> WPDS_with_W_automata \<Delta> ts"
  unfolding checking_def WPDS_with_W_automata_def finite_WPDS_def WPDS_with_W_automata_axioms_def by blast


definition "lbl = WPDS.lbl"

definition "augmented_WPDS_rules = WPDS_with_W_automata_no_assms.augmented_WPDS_rules"
definition "pre_star_exec' = WPDS_with_W_automata_no_assms.pre_star_exec'"
definition "accept_pre_star_exec0' = WPDS_with_W_automata_no_assms.accept_pre_star_exec0'"
declare accept_pre_star_exec0'_def[code]

thm WPDS_with_W_automata.pre_star_exec_correctness
lemma pre_star_exec_correctness:
  assumes "checking \<Delta> ts"
  shows "dioidLTS.accepts (WPDS_with_W_automata_no_assms.pre_star_exec' \<Delta> ts) finals (Init p, w) =
         dioidLTS.weight_pre_star (WPDS.transition_rel \<Delta>) (\<lambda>(p, w). dioidLTS.accepts ts finals (Init p, w)) (p, w)"
  using WPDS_with_W_automata.pre_star_exec_correctness[of \<Delta> ts finals p w] checking_implies[OF assms] by blast

(*
lemma augmented_WPDS_rules_code2[code]: "checking \<Delta> ts \<Longrightarrow> WPDS_with_W_automata_no_assms.augmented_WPDS_rules \<Delta> ts = (\<Union>((p, \<gamma>), d, (p', w)) \<in> \<Delta>. {((Init p, \<gamma>), d, (Init p', w))}) \<union> {((p,\<gamma>), d, (q, pop)) | p \<gamma> d q. ts $ (p,\<gamma>,q) = d}"
  *)


end

(*global_interpretation wpds: WPDS_Code \<Delta> ts
  for \<Delta> :: "('ctr_loc::{enum,card_UNIV}, 'label::finite, 'weight::bounded_idempotent_semiring) rule set"
  and ts :: "(('ctr_loc, 'noninit::{enum,card_UNIV}) state, 'label) transition \<Rightarrow>f 'weight"
  defines pre_star = "WPDS_with_W_automata.pre_star_exec' \<Delta>"
  .
*)


(*definition "checking ts \<longleftrightarrow> (\<forall>q. is_Init q \<longrightarrow> (\<forall>p \<gamma>. ts $ (p, \<gamma>, q) = 0))"*)

global_interpretation wpds: WPDS_Code \<Delta> ts
  for \<Delta> :: "('ctr_loc::{enum,card_UNIV}, 'label::finite, 'weight::bounded_idempotent_semiring) rule set"
  and ts :: "(('ctr_loc, 'noninit::{enum,card_UNIV}) state, 'label) transition \<Rightarrow>f 'weight"
defines pre_star = "WPDS_with_W_automata_no_assms.pre_star_exec' \<Delta>"
(* 
  Input:
     * A weighted pushdown system
     * A W-Automaton (with initial and non-initial states)
   Output:
     * A W-Automaton
 *)
    and pre_star_check = "if WPDS_Code.checking \<Delta> ts then Some (WPDS_Code.pre_star_exec' \<Delta> ts) else None"
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
    and step_starp = "if WPDS_Code.checking \<Delta> ts then Some (WPDS_Code.pre_star_exec' \<Delta> ts) else None"
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
    and accepts_pre_star_check = "\<lambda>finals pv. if WPDS_Code.checking \<Delta> ts then Some (WPDS_Code.accept_pre_star_exec0' \<Delta> ts finals pv) else None"
(*
  Input
    * Pushdown Automaton
    * W-Automaton
    * Set of final states
    * Configuration
    * Weight
*)
  .


declare accepts_def[code]
declare accepts_pre_star_check_def[code]

thm WPDS_Code.accept_pre_star_exec0'_def

(*lemma accepts_pre_star_check_code[code]: 
  "accepts_pre_star_check \<Delta> ts finals (p, w) = (if wpds.checking \<Delta> ts then Some (accepts_code (WPDS_Code.pre_star_exec' \<Delta> ts) finals (p, w)) else None)"
  unfolding accepts_pre_star_check_def accepts_code_correct[of "(wpds.pre_star_exec' \<Delta> ts)" finals p w, symmetric]
  unfolding wpds.accept_pre_star_exec0'_def WPDS_Code.pre_star_exec'_def
  using WPDS_with_W_automata_no_assms.accept_pre_star_exec0'_unfold[of \<Delta> ts]
  by simp  
*)

instantiation state :: ("{enum,finite_UNIV}","{enum,finite_UNIV}") finite_UNIV begin

definition finite_UNIV_a :: "('a,bool) phantom" where "finite_UNIV_a == finite_UNIV"
definition finite_UNIV_b :: "('b,bool) phantom" where "finite_UNIV_b == finite_UNIV"

definition UNIV_a :: "'a set" where "UNIV_a == UNIV"
definition UNIV_b :: "'b set" where "UNIV_b == UNIV"

definition finite_UNIV_state :: "(('a, 'b) state, bool) phantom" where
  "finite_UNIV_state  == Phantom(('a, 'b) state) (finite UNIV_a \<and> finite UNIV_b)"

instance
  by standard (simp add: UNIV_a_def UNIV_b_def finite_UNIV_state_def)
end

instantiation state :: ("{enum,card_UNIV}","{enum,card_UNIV}") card_UNIV begin

definition card_UNIV_a :: "'a card_UNIV" where "card_UNIV_a == card_UNIV"
definition card_UNIV_b :: "'b card_UNIV" where "card_UNIV_b == card_UNIV"

definition UNIV_a' :: "'a set" where "UNIV_a' == UNIV"
definition UNIV_b' :: "'b set" where "UNIV_b' == UNIV"

definition card_UNIV_state :: "(('a, 'b) state) card_UNIV" where
  "card_UNIV_state == Phantom(('a, 'b) state) (if (finite UNIV_a' \<and> finite UNIV_b') then CARD('a) + CARD('b) else 0)"

instance 
  by standard (simp add: card_UNIV_state_def UNIV_a'_def UNIV_b'_def finite_card_states)
end

instantiation operation :: (enum) enum begin

definition enum_a :: "'a list" where "enum_a = enum_class.enum"
definition enum_all_a :: "('a \<Rightarrow> bool) \<Rightarrow> bool" where
  "enum_all_a = enum_class.enum_all"
definition enum_ex_a :: "('a \<Rightarrow> bool) \<Rightarrow> bool" where
  "enum_ex_a = enum_class.enum_ex"

find_consts "'x list \<Rightarrow> 'y list \<Rightarrow> ('x * 'y) list"

definition enum_operation :: "'a operation list" where
  "enum_operation = pop # map swap enum_a @ map (\<lambda>(x,y). push x y) (List.product enum_a enum_a)"

definition enum_all_operation :: "('a operation \<Rightarrow> bool) \<Rightarrow> bool" where
  "enum_all_operation P \<equiv> P pop \<and> enum_all_a (\<lambda>x. P (swap x)) \<and> enum_all_a (\<lambda>x. enum_all_a (\<lambda>y. P (push x y)))"

definition enum_ex_operation :: "('a operation \<Rightarrow> bool) \<Rightarrow> bool" where
  "enum_ex_operation P \<equiv> P pop \<or> enum_ex_a (\<lambda>x. P (swap x)) \<or> enum_ex_a (\<lambda>x. enum_ex_a (\<lambda>y. P (push x y)))"

instance proof
  have swap_enum: "\<forall>x. swap x \<in> swap ` set enum_a"
    unfolding local.enum_a_def using UNIV_enum by auto

  show "(UNIV :: 'a operation set) = set enum_class.enum"
  proof
    show "(UNIV :: 'a operation set) \<subseteq> set enum_class.enum"
    proof 
      fix x :: "'a operation"
      show "x \<in> set enum_class.enum"
        unfolding enum_operation_def using swap_enum by (induction x) auto
    qed
  next
    show "set enum_class.enum \<subseteq> (UNIV :: 'a operation set)"
      by auto
  qed

  have "distinct (map swap local.enum_a)"
    using distinct_map inj_on_def unfolding enum_a_def using enum_distinct by force
  moreover
  have "distinct (map (\<lambda>(x, y). push x y) (List.product local.enum_a local.enum_a))"
    using distinct_map distinct_product enum_distinct unfolding enum_a_def 
    by (force simp add: inj_on_def)
  ultimately
  show "distinct (enum_class.enum :: 'a operation list)"
    unfolding enum_operation_def by auto

  show "\<And>P :: 'a operation \<Rightarrow> bool. enum_class.enum_all P = Ball UNIV P"
  proof -
    fix P :: "'a operation \<Rightarrow> bool"
    show "enum_class.enum_all P = Ball UNIV P"
    proof 
      assume "enum_class.enum_all P"
      moreover 
      have "\<And>x. P pop \<Longrightarrow> \<forall>x. P (swap x) \<Longrightarrow> \<forall>x y. P (push x y) \<Longrightarrow> P x"
        by (metis operation.exhaust)
      ultimately show "Ball UNIV P"
        unfolding enum_all_operation_def local.enum_all_a_def by auto
    next
      assume "Ball UNIV P"
      then show "enum_class.enum_all P"
        unfolding enum_all_operation_def local.enum_all_a_def by auto
    qed
  qed
  show "\<And>P :: 'a operation \<Rightarrow> bool. enum_class.enum_ex P = Bex UNIV P"
  proof
    fix P :: "'a operation \<Rightarrow> bool"
    assume "enum_class.enum_ex P"
    then show "Bex UNIV P"
      unfolding enum_ex_operation_def local.enum_ex_a_def by auto
  next
    fix P :: "'a operation \<Rightarrow> bool"
    assume "Bex UNIV P"
    then show "enum_class.enum_ex P"
      unfolding enum_ex_operation_def local.enum_ex_a_def enum_class.enum_ex
      by (metis operation.exhaust)
  qed
qed
end

declare WPDS.lbl.simps[code]
declare WPDS_with_W_automata_no_assms.augmented_WPDS_rules_def[code]
declare WPDS_with_W_automata_no_assms.init_rules_def[code]
declare WPDS_with_W_automata_no_assms.pop_ts_rules_def[code]
declare WPDS.accept_pre_star_exec0_def[code]

export_code accepts_pre_star_check in Haskell (*SML gives depency cycle.*)


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

end
