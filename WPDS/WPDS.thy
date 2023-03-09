theory WPDS 
  imports "LTS" "Saturation" "FinFunWellQuasiOrder" "ProdDioid" "Kleene_Algebra.Dioid_Models"
begin

\<comment> \<open>Preliminary definition of reflexive and transitive closure over a relation labelled with a monoid, 
    (and transitive closure over a semigroup-labelled relation)\<close>
inductive_set monoid_rtrancl :: "('a \<times> 'b::monoid_mult \<times> 'a) set \<Rightarrow> ('a \<times> 'b \<times> 'a) set"
 for r :: "('a \<times> 'b \<times> 'a) set" where
    monoid_rtrancl_refl [intro!, Pure.intro!, simp]: "(a, 1, a) \<in> monoid_rtrancl r"
  | monoid_rtrancl_into_rtrancl [Pure.intro]: "(a, w, b) \<in> monoid_rtrancl r \<Longrightarrow> (b, l, c) \<in> r \<Longrightarrow> (a, w*l,c) \<in> monoid_rtrancl r"
inductive_cases monoid_rtrancl_empty [elim]: "(p, 1, q) \<in> monoid_rtrancl r"
inductive_cases monoid_rtrancl_extend: "(p, w*l, q) \<in> monoid_rtrancl r"

inductive_set semigroup_trancl :: "('a \<times> 'b::semigroup_mult \<times> 'a) set \<Rightarrow> ('a \<times> 'b \<times> 'a) set"
 for r :: "('a \<times> 'b \<times> 'a) set" where
    semigroup_trancl_refl [intro!, Pure.intro!, simp]: "(a, l, b) \<in> r \<Longrightarrow> (a, l, b) \<in> semigroup_trancl r"
  | semigroup_trancl_into_rtrancl [Pure.intro]: "(a, w, b) \<in> semigroup_trancl r \<Longrightarrow> (b, l, c) \<in> r \<Longrightarrow> (a, w*l,c) \<in> semigroup_trancl r"


\<comment> \<open>If the @{typ 'label} of a LTS is a monoid, we can express the monoid product of labels over a path.\<close>
locale monoidLTS = LTS transition_relation 
  for transition_relation :: "('state, 'label::monoid_mult) transition set"
begin
definition l_step_relp  :: "'state \<Rightarrow> 'label \<Rightarrow> 'state \<Rightarrow> bool" ("(_)/ \<Midarrow> (_)/ \<Rightarrow> (_)/" [70,70,80] 80) where
  "c \<Midarrow>l\<Rightarrow> c' \<longleftrightarrow> (c, l, c') \<in> transition_relation"
abbreviation monoid_star_relp :: "'state \<Rightarrow> 'label \<Rightarrow> 'state \<Rightarrow> bool" ("(_)/ \<Midarrow> (_)/ \<Rightarrow>\<^sup>* (_)/" [90,90,100] 100) where
  "c \<Midarrow>l\<Rightarrow>\<^sup>* c' \<equiv> (monoid_rtranclp l_step_relp) c l c'"
definition monoid_star :: "('state \<times> 'label \<times> 'state) set" where
  "monoid_star = {(c,l,c'). c \<Midarrow>l\<Rightarrow>\<^sup>* c'}"
end

\<comment> \<open>If the @{typ 'label} of a LTS is a dioid with additive and multiplicative identities, 
    we can express the meet-over-all-paths value as a generalization of pre-star and post-star.\<close>
locale dioidLTS = monoidLTS transition_relation 
  for transition_relation :: "('state, 'label::dioid_one_zero) transition set"
begin

definition weight_pre_star :: "('state \<Rightarrow> 'label) \<Rightarrow> ('state \<Rightarrow> 'label)" where
  "weight_pre_star C c = \<Sum>{l*(C c') | l c'. c \<Midarrow>l\<Rightarrow>\<^sup>* c'}"
definition weight_post_star :: "('state \<Rightarrow> 'label) \<Rightarrow> ('state \<Rightarrow> 'label)" where
  "weight_post_star C c = \<Sum>{(C c')*l | c' l. c' \<Midarrow>l\<Rightarrow>\<^sup>* c}"
end


datatype 'label operation = pop | swap 'label | push 'label 'label
\<comment> \<open>WPDS has a @{typ "'weight::dioid_one_zero"} on the rule.\<close>
type_synonym ('ctr_loc, 'label, 'weight) rule = "('ctr_loc \<times> 'label) \<times> 'weight \<times> ('ctr_loc \<times> 'label operation)"
type_synonym ('ctr_loc, 'label) conf = "'ctr_loc \<times> 'label list"

locale WPDS =
  fixes \<Delta> :: "('ctr_loc, 'label::finite, 'weight::dioid_one_zero) rule set"
begin

primrec lbl :: "'label operation \<Rightarrow> 'label list" where
  "lbl pop = []"
| "lbl (swap \<gamma>) = [\<gamma>]" 
| "lbl (push \<gamma>  \<gamma>') = [\<gamma>, \<gamma>']"

definition is_rule :: "'ctr_loc \<times> 'label \<Rightarrow> 'weight \<Rightarrow> 'ctr_loc \<times> 'label operation \<Rightarrow> bool" ("((_)/ \<midarrow> (_)/ \<hookrightarrow> (_)/ )" [70,70,80] 80) where
  "p\<gamma> \<midarrow>d\<hookrightarrow> p'w \<equiv> (p\<gamma>,d,p'w) \<in> \<Delta>"

inductive_set transition_rel :: "(('ctr_loc, 'label) conf \<times> 'weight \<times> ('ctr_loc, 'label) conf) set" where
  "(p, \<gamma>) \<midarrow>d\<hookrightarrow> (p', w) \<Longrightarrow> ((p, \<gamma>#w'), d, (p', (lbl w)@w')) \<in> transition_rel"

(* 
definition lang :: "('state, 'label) transition set \<Rightarrow> (('ctr_loc, 'label) conf \<Rightarrow> 'weight)"
*)

interpretation dioidLTS transition_rel .

notation step_relp (infix "\<Rightarrow>" 80)
notation step_starp (infix "\<Rightarrow>\<^sup>*" 80)
notation l_step_relp ("(_)/ \<Midarrow> (_)/ \<Rightarrow> (_)/" [70,70,80] 80)
notation monoid_star_relp ("(_)/ \<Midarrow> (_)/ \<Rightarrow>\<^sup>* (_)/" [90,90,100] 100) 

lemma step_relp_def2:
  "(p, \<gamma>w') \<Midarrow>d\<Rightarrow> (p',ww') \<longleftrightarrow> (\<exists>\<gamma> w' w. \<gamma>w' = \<gamma>#w' \<and> ww' = (lbl w)@w' \<and> (p, \<gamma>) \<midarrow>d\<hookrightarrow> (p', w))"
  by (meson monoidLTS.l_step_relp_def transition_rel.simps)
end


datatype ('ctr_loc, 'noninit, 'label) state =
  is_Init: Init (the_Ctr_Loc: 'ctr_loc) (* p \<in> P *)
  | is_Noninit: Noninit (the_St: 'noninit) (* q \<in> Q \<and> q \<notin> P *)
  | is_Isolated: Isolated (the_Ctr_Loc: 'ctr_loc) (the_Label: 'label) (* q\<^sub>p\<^sub>\<gamma> *)

lemma finitely_many_states:
  assumes "finite (UNIV :: 'ctr_loc set)"
  assumes "finite (UNIV :: 'noninit set)"
  assumes "finite (UNIV :: 'label set)"
  shows "finite (UNIV :: ('ctr_loc, 'noninit, 'label) state set)"
proof -
  define Isolated' :: "('ctr_loc * 'label) \<Rightarrow> ('ctr_loc, 'noninit, 'label) state" where 
    "Isolated' == \<lambda>(c :: 'ctr_loc, l:: 'label). Isolated c l"
  define Init' :: "'ctr_loc \<Rightarrow> ('ctr_loc, 'noninit, 'label) state" where
    "Init' = Init"
  define Noninit' :: "'noninit \<Rightarrow> ('ctr_loc, 'noninit, 'label) state" where
    "Noninit' = Noninit"

  have split: "UNIV = (Init' ` UNIV) \<union> (Noninit' ` UNIV) \<union> (Isolated' ` (UNIV :: (('ctr_loc * 'label) set)))"
    unfolding Init'_def Noninit'_def
  proof (rule; rule; rule; rule)
    fix x :: "('ctr_loc, 'noninit, 'label) state"
    assume "x \<in> UNIV"
    moreover
    assume "x \<notin> range Isolated'"
    moreover
    assume "x \<notin> range Noninit"
    ultimately
    show "x \<in> range Init"
      by (metis Isolated'_def prod.simps(2) range_eqI state.exhaust)
  qed

  have "finite (Init' ` (UNIV:: 'ctr_loc set))"
    using assms by auto
  moreover
  have "finite (Noninit' ` (UNIV:: 'noninit set))"
    using assms by auto
  moreover
  have "finite (UNIV :: (('ctr_loc * 'label) set))"
    using assms by (simp add: finite_Prod_UNIV)
  then have "finite (Isolated' ` (UNIV :: (('ctr_loc * 'label) set)))"
    by auto
  ultimately
  show "finite (UNIV :: ('ctr_loc, 'noninit, 'label) state set)"
    unfolding split by auto
qed

instantiation state :: (finite, finite, finite) finite begin
  instance by standard (simp add: finitely_many_states)
end


\<comment> \<open>For the semantics of a weighted automaton, labels are lifted to the list-monoid and paired with a weight\<close>
type_synonym ('label, 'weight) wautomaton_label = "('label list \<times> 'weight)" 
\<comment> \<open>Weighted automata transitions are modelled as a @{term finfun} from transitions to their weight, 
    where @{term "0::('weight::dioid_one_zero)"} is the default value, indicating no transition.\<close>
type_synonym ('state, 'label, 'weight) w_transitions = "('state, 'label) transition \<Rightarrow>f 'weight" 

type_synonym ('state, 'label, 'weight) w_transition_set = "('state, ('label list \<times> 'weight)) transition set"

\<comment> \<open>Embed a weighted automata into a monoidLTS. All non-zero transitions are added. The label is lifted to the list-monoid.\<close>
definition wts_to_monoidLTS :: "(('state, 'label, 'weight::{dioid_one_zero,wqo}) w_transitions) \<Rightarrow> ('state, ('label list \<times> 'weight)) transition set" where
  "wts_to_monoidLTS ts = {(p, ([l],d), q) | p l d q. ts $ (p,l,q) = d \<and> d \<noteq> 0}"

locale W_automata = monoidLTS "wts_to_monoidLTS transition_relation"
  for transition_relation :: "('state::finite, 'label, 'weight::{dioid_one_zero,wqo}) w_transitions" +
  fixes initials :: "'state set" and finals :: "'state set"
begin
interpretation monoidLTS "wts_to_monoidLTS transition_relation" .

end

\<comment> \<open>The weighted version of the @{term LTS.reach} function. 
    Computes a set of pairs of a state and the weight to reach the state.
    Note that the @{term wts_to_monoidLTS} embedding ensures that all labels @{term \<gamma>'} of 
    transitions in @{term ts} are of lists length 1.\<close>
context fixes ts :: "('state, 'label list \<times> 'weight::monoid_mult) transition set" begin
fun monoidLTS_reach where
  "monoidLTS_reach p [] = {(p,1)}"
| "monoidLTS_reach p (\<gamma>#w) = (\<Union>(q',d) \<in> (\<Union>(p',(\<gamma>',d),q') \<in> ts. if p' = p \<and> \<gamma>' = [\<gamma>] then {(q',d)} else {}).
      {(q,d*d') | q d'. (q,d') \<in> monoidLTS_reach q' w})"
end


locale WPDS_with_W_automata = WPDS \<Delta>
  for \<Delta> :: "('ctr_loc::enum, 'label::finite, 'weight::{dioid_one_zero,wqo}) rule set"
    +
  fixes final_inits :: "('ctr_loc::enum) set"
  fixes final_noninits :: "('noninit::finite) set"
begin

(* Corresponds to Schwoon's F *)
definition finals :: "('ctr_loc, 'noninit::finite, 'label) state set" where
  "finals = Init ` final_inits \<union> Noninit ` final_noninits"

lemma F_not_Ext: "\<not>(\<exists>f\<in>finals. is_Isolated f)"
  using finals_def by fastforce

(* Corresponds to Schwoon's P *)
definition inits :: "('ctr_loc, 'noninit, 'label) state set" where 
  "inits = {q. is_Init q}"

lemma inits_code[code]: "inits = set (map Init Enum.enum)"
  by (auto simp: inits_def is_Init_def simp flip: UNIV_enum)

definition noninits :: "('ctr_loc, 'noninit, 'label) state set" where
  "noninits = {q. is_Noninit q}"

definition isols :: "('ctr_loc, 'noninit, 'label) state set" where
  "isols = {q. is_Isolated q}"

interpretation dioidLTS transition_rel .
notation step_relp (infix "\<Rightarrow>" 80)
notation step_starp (infix "\<Rightarrow>\<^sup>*" 80)
notation l_step_relp ("(_)/ \<Midarrow> (_)/ \<Rightarrow> (_)/" [70,70,80] 80)
notation monoid_star_relp ("(_)/ \<Midarrow> (_)/ \<Rightarrow>\<^sup>* (_)/" [90,90,100] 100) 

\<comment> \<open>Generalization of @{term PDS_with_P_automata.accepts} that computes the meet-over-all-paths in the W-automaton.\<close>
definition accepts :: "(('ctr_loc, 'noninit, 'label) state, 'label, 'weight) w_transitions \<Rightarrow> ('ctr_loc, 'label) conf \<Rightarrow> 'weight" where
  "accepts ts \<equiv> \<lambda>(p,w). (\<Sum>{d | d q. q \<in> finals \<and> (Init p,(w,d),q) \<in> monoidLTS.monoid_star (wts_to_monoidLTS ts)})"

\<comment> \<open>Weighted pre-star rule updates the finfun of transition weights.\<close>
inductive pre_star_rule :: "(('ctr_loc, 'noninit, 'label) state, 'label, 'weight) w_transitions saturation_rule" where 
  add_trans: "((p, \<gamma>) \<midarrow>d\<hookrightarrow> (p', w)) 
      \<Longrightarrow> (Init p', (lbl w, d'), q) \<in> monoidLTS.monoid_star (wts_to_monoidLTS ts)
      \<Longrightarrow> (ts $ (Init p, \<gamma>, q)) = d''
      \<Longrightarrow> (d'' + (d * d')) \<noteq> d'' 
      \<Longrightarrow> pre_star_rule ts ts((Init p, \<gamma>, q) $:= d'' + (d * d'))"

(* from: https://stackoverflow.com/questions/28633353/converting-a-set-to-a-list-in-isabelle *)
definition set_to_list :: "'a set \<Rightarrow> 'a list"
  where "set_to_list s = (SOME l. set l = s)"
lemma  set_set_to_list:
   "finite s \<Longrightarrow> set (set_to_list s) = s"
  unfolding set_to_list_def by (metis (mono_tags) finite_list some_eq_ex)
(* end from *)

\<comment> \<open>For the executable pre-star, the saturation rule computes a set of new transition weights, 
    that are updated using the dioid's plus operator to combine with the existing value.\<close>
fun update_wts :: "('a \<Rightarrow>f 'b::semigroup_add) \<Rightarrow> ('a \<times> 'b) list \<Rightarrow> ('a \<Rightarrow>f 'b)" where
  "update_wts f [] = f" |
  "update_wts f ((a,b)#xs) = update_wts f(a $:= (f$a) + b) xs"

definition update_wts_set :: "('a \<Rightarrow>f 'b::ab_semigroup_add) \<Rightarrow> ('a \<times> 'b) set \<Rightarrow> ('a \<Rightarrow>f 'b)" where
  "update_wts_set f s = update_wts f (set_to_list s)"

definition pre_star1 :: "(('ctr_loc, 'noninit, 'label) state, 'label, 'weight) w_transitions \<Rightarrow> ((('ctr_loc, 'noninit, 'label) state, 'label) transition \<times> 'weight) set" where
  "pre_star1 wts =
    (\<Union>((p, \<gamma>), d, (p', w)) \<in> \<Delta>. 
        \<Union>(q,d') \<in> monoidLTS_reach (wts_to_monoidLTS wts) (Init p') (lbl w). 
            {((Init p, \<gamma>, q), d * d')})"

\<comment> \<open>A weighted automaton is initialized with weights 1 (neutral element along paths) on existing transitions, 
    and a default weight of 0 (neutral element for combining paths) for non-existing transitions.\<close>
definition ts_to_wts :: "('state, 'label) transition set \<Rightarrow> ('state, 'label, 'weight::{dioid_one_zero,wqo}) w_transitions" where
  "ts_to_wts ts = update_wts_set (K$ 0) {(t,1) | t. t \<in> ts}"
definition wts_to_ts :: "('state, 'label, 'weight::{dioid_one_zero,wqo}) w_transitions \<Rightarrow> ('state, 'label) transition set" where
  "wts_to_ts wts = {t | t. wts $ t \<noteq> 0}"

definition "pre_star_loop = while_option (\<lambda>s. update_wts_set s (pre_star1 s) \<noteq> s) (\<lambda>s. update_wts_set s (pre_star1 s))"
definition "pre_star_exec = the o pre_star_loop"
definition "pre_star_exec_check A = (if inits \<subseteq> LTS.srcs A then pre_star_loop (ts_to_wts A) else None)"

definition "accept_pre_star_exec_check A c = (if inits \<subseteq> LTS.srcs A then Some (accepts (pre_star_exec (ts_to_wts A)) c) else None)"

theorem pre_star_rule_correct:
  assumes "inits \<subseteq> LTS.srcs (wts_to_monoidLTS A)"
  assumes "saturation pre_star_rule A A'"
  shows "accepts A' = weight_pre_star (accepts A)"
  
  oops



thm less_finfun_def less_eq_finfun_def less_eq_def
lemma pre_star_saturation_exi:
  shows "\<exists>ts'::((('ctr_loc, 'noninit::finite, 'label::finite) state, 'label, 'weight::{dioid_one_zero,wqo}) w_transitions). 
            saturation pre_star_rule ts ts'"
  apply (rule wqo_class_saturation_exi[of pre_star_rule ts])
  subgoal for ts ts'
    apply (induct rule: pre_star_rule.induct)
    subgoal for p \<gamma> d p' w  d' q ts d''
      unfolding less_finfun_def less_eq_finfun_def
      apply simp
      apply safe
      subgoal for p'' \<gamma>'' q''
        apply (cases "(Init p, \<gamma>, q) = (p'', \<gamma>'', q'')")
         defer
         apply auto[1]
        apply simp
        oops
  
  

lemma lemma_3_1_w:
  assumes "p'w \<Midarrow>d\<Rightarrow>\<^sup>* pv"
  assumes "accepts A pv = d'"
  assumes "saturation pre_star_rule A A'"
  shows "accepts A' p'w \<le> d * d'"
  using assms
  sorry

lemma lemma_3_2_a'_w:
(* assumes "inits \<subseteq> LTS.srcs A"*)
  assumes "pre_star_rule\<^sup>*\<^sup>* A A'"
  assumes "(Init p, (w,d), q) \<in> monoidLTS.monoid_star (wts_to_monoidLTS A')"
  shows "\<exists>p' w'. (Init p', (w',d'), q) \<in> monoidLTS.monoid_star (wts_to_monoidLTS A) \<and> (p, w) \<Midarrow>d''\<Rightarrow>\<^sup>* (p', w') \<and> d'' * d' \<le> d"
(* Maybe assume d'=1 *)
  sorry

lemma lemma_3_2_a_w:
(* assumes "inits \<subseteq> LTS.srcs A" *)
  assumes "saturation pre_star_rule A A'"
  assumes "(Init p, (w,d), q) \<in> monoidLTS.monoid_star (wts_to_monoidLTS A')"
  shows "\<exists>p' w'. (Init p', (w',d'), q) \<in> monoidLTS.monoid_star (wts_to_monoidLTS A) \<and> (p, w) \<Midarrow>d''\<Rightarrow>\<^sup>* (p', w') \<and> d'' * d' \<le> d"
  using assms lemma_3_2_a'_w saturation_def by metis

\<comment> \<open>Corresponds to one direction of Schwoon's theorem 3.2\<close>
theorem pre_star_rule_subset_pre_star_lang:
(*  assumes "inits \<subseteq> LTS.srcs A"*)
  assumes "pre_star_rule\<^sup>*\<^sup>* A A'"
  shows "\<forall>c. weight_pre_star (accepts A) c \<le> accepts A' c"
proof
  fix c :: "'ctr_loc \<times> 'label list"
  define d where "d = accepts A' c"
  define p where "p = fst c"
  define w where "w = snd c"
  from p_def w_def d_def have "d = accepts A' (p,w)"
    by auto
  then have "\<exists>q \<in> finals. (Init p, (w,d), q) \<in> monoidLTS.monoid_star (wts_to_monoidLTS A')"
    unfolding accepts_def sorry
  (*by auto
  then obtain q where q_p: "q \<in> finals" "(Init p, w, q) \<in> LTS.trans_star A'"
    by auto
  then have "\<exists>p' w'. (p,w) \<Rightarrow>\<^sup>* (p',w') \<and> (Init p', w', q) \<in> LTS.trans_star A"
    using lemma_3_2_a'_w assms(1) assms(2) by metis
  then obtain p' w' where p'_w'_p: "(p,w) \<Rightarrow>\<^sup>* (p',w')" "(Init p', w', q) \<in> LTS.trans_star A"
    by auto
  then have "(p', w') \<in> lang A"
    unfolding lang_def unfolding accepts_def using q_p(1) by auto
  then have "(p,w) \<in> pre_star (lang A)"
    unfolding pre_star_def using p'_w'_p(1) by auto*)
  then show "weight_pre_star (accepts A) c \<le> d"
    unfolding p_def w_def sorry (* by auto*)
qed

\<comment> \<open>Corresponds to Schwoon's theorem 3.2\<close>
theorem pre_star_rule_accepts_correct:
(*  assumes "inits \<subseteq> LTS.srcs A" *)
  assumes "saturation pre_star_rule A A'"
  shows "\<forall>c. weight_pre_star (accepts A) c = accepts A' c"
  unfolding order_eq_iff
proof (rule; rule)
  fix c :: "'ctr_loc \<times> 'label list"
  define p where "p = fst c"
  define w where "w = snd c"
  define d where "d = weight_pre_star (accepts A) c"
  then have "d = weight_pre_star (accepts A) (p,w)"
    unfolding p_def w_def d_def by auto
  then have "\<exists>d' p' w'. d \<le> d' * accepts A (p',w') \<and> (p,w) \<Midarrow>d'\<Rightarrow>\<^sup>* (p',w')" (* \<Sum>{l*(C (p',w')) | l  (p',w'). (p,w) \<Midarrow>l\<Rightarrow>\<^sup>*  (p',w')} *)
    unfolding weight_pre_star_def by force
  then obtain p' w' d' where "d \<le> d' * accepts A (p',w') \<and> (p,w) \<Midarrow>d'\<Rightarrow>\<^sup>* (p',w')"
    by auto
thm lemma_3_1_w[of "(p,w)" d' "(p',w')"]
  have "accepts A' (p, w) \<le> d' \<cdot> d'" sorry
  then have "\<exists>q \<in> finals. (Init p, w, q) \<in> monoidLTS.monoid_star (wts_to_monoidLTS A')"
    using lemma_3_1 assms(2) unfolding accepts_def by force
  then have "accepts A' (p,w) \<le> d"
    unfolding accepts_def by auto
  then show "(accepts A') c \<le> d"
    using p_def w_def sorry (* by auto*)
next
  fix c :: "'ctr_loc \<times> 'label list"
  show "weight_pre_star (accepts A) c \<le> accepts A' c"
    using pre_star_rule_subset_pre_star_lang assms unfolding saturation_def by blast
qed


\<comment> \<open>Example of a theorem that should hold... 
    We still need to define intersection of weighted automata to state the final correctness theorem.\<close>
theorem "accept_pre_star_exec_check A c = Some (weight_pre_star (accepts (ts_to_wts A)) c)"
  
  oops

end


end