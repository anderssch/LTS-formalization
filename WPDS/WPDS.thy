theory WPDS 
  imports "LTS" "Saturation" "ReverseWellQuasiOrder" "FinFunWellQuasiOrder" "ProdDioid" "Kleene_Algebra.Dioid_Models"
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

lemma monoid_star_is_monoid_rtrancl[simp]: "monoidLTS.monoid_star = monoid_rtrancl"
  unfolding monoidLTS.monoid_star_def monoidLTS.l_step_relp_def monoid_rtrancl_def by simp

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

(* A final trace gives a list of pop_seqs followed by a list of automata transitions, where only the first has non-trivial weight.*)
type_synonym ('ctr_loc, 'noninit, 'label) final_trace = "('ctr_loc, 'label) trace \<times> ('label \<times> 'noninit) list"

\<comment> \<open>Embed a weighted automata into a monoidLTS. All non-zero transitions are added. The label is lifted to the list-monoid.\<close>
definition wts_to_monoidLTS :: "(('state, 'label, 'weight::{dioid_one_zero,reverse_wqo}) w_transitions) \<Rightarrow> ('state, ('label list \<times> 'weight)) transition set" where
  "wts_to_monoidLTS ts = {(p, ([l],d), q) | p l d q. ts $ (p,l,q) = d \<and> d \<noteq> 0}"

locale W_automata = monoidLTS "wts_to_monoidLTS transition_relation"
  for transition_relation :: "('state::finite, 'label, 'weight::{dioid_one_zero,reverse_wqo}) w_transitions" +
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
  for \<Delta> :: "('ctr_loc::enum, 'label::finite, 'weight::{dioid_one_zero,reverse_wqo}) rule set"
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

definition pop_seq :: "'ctr_loc \<Rightarrow> 'label \<Rightarrow> 'ctr_loc \<Rightarrow> 'weight" where
  "pop_seq p \<gamma> p' = \<Sum>{d. (p,[\<gamma>]) \<Midarrow>d\<Rightarrow>\<^sup>* (p',[])}"

lemma "(pop_seq p \<gamma> p') \<le> \<Sum>{d. (p,\<gamma>#w) \<Midarrow>d\<Rightarrow>\<^sup>* (p',w)}"
  using step_relp_def2[of p "\<gamma>#w" _ p' w]
  apply simp
  unfolding pop_seq_def
  apply auto
  oops

lemma "(pop_seq p \<gamma> p') * (pop_seq p' \<gamma>' p'') \<le> \<Sum>{d. (p,[\<gamma>,\<gamma>']) \<Midarrow>d\<Rightarrow>\<^sup>* (p'',[])}"
  unfolding pop_seq_def
  apply simp
  oops


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
definition ts_to_wts :: "('state, 'label) transition set \<Rightarrow> ('state, 'label, 'weight::{dioid_one_zero,reverse_wqo}) w_transitions" where
  "ts_to_wts ts = update_wts_set (K$ 0) {(t,1) | t. t \<in> ts}"
definition wts_to_ts :: "('state, 'label, 'weight::{dioid_one_zero,reverse_wqo}) w_transitions \<Rightarrow> ('state, 'label) transition set" where
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

lemma finfun_update_less:
  assumes "ts $ a < ts' $ a"
  assumes "ts(a $:= d) = ts'"
  shows "ts < ts'"
  using assms unfolding less_finfun_def less_eq_finfun_def
  apply (simp, safe)
  subgoal for a'
    apply (cases "a = a'")
    using order_less_imp_le by (blast, simp)
  using dual_order.strict_iff_not by blast

lemma pre_star_saturation_less:
  fixes ts::"((('ctr_loc, 'noninit::finite, 'label::finite) state, 'label, 'weight::{dioid_one_zero,reverse_wqo}) w_transitions)"
  assumes "ts $ (Init p, \<gamma>, q) + d \<cdot> d' \<noteq> ts $ (Init p, \<gamma>, q)"
  assumes "ts' = ts((Init p, \<gamma>, q) $:= ts $ (Init p, \<gamma>, q) + d \<cdot> d')"
  shows "ts < ts'"
proof -
  from assms(1) have "ts $ (Init p, \<gamma>, q) < ts $ (Init p, \<gamma>, q) + d \<cdot> d'" 
    by (simp add: join.sup.strict_order_iff join.sup_commute join.sup_left_commute)
  then have "ts $ (Init p, \<gamma>, q) < ts' $ (Init p, \<gamma>, q)" using assms(2) by simp
  then show ?thesis using assms(2) finfun_update_less[of ts "(Init p, \<gamma>, q)" ts'] by blast
qed

lemma pre_star_saturation_exi:
  fixes ts ::"(('ctr_loc, 'noninit::finite, 'label::finite) state, 'label, 'weight::{dioid_one_zero,reverse_wqo}) w_transitions"
  shows "\<exists>ts'. saturation pre_star_rule ts ts'"
  by (rule reverse_wqo_class_saturation_exi[of pre_star_rule ts])
     (auto simp add:pre_star_rule.simps pre_star_saturation_less)


lemma wts_label_exist: "(p, w, q) \<in> wts_to_monoidLTS ts \<Longrightarrow> \<exists>l. fst w = [l]"
  unfolding wts_to_monoidLTS_def by fastforce

lemma wts_label_size: "(p, w, q) \<in> wts_to_monoidLTS ts \<Longrightarrow> size (fst w) = 1"
  unfolding wts_to_monoidLTS_def by fastforce

lemma wts_label_not_empty: "(p, w, q) \<in> wts_to_monoidLTS ts \<Longrightarrow> fst w \<noteq> []"
  unfolding wts_to_monoidLTS_def by force

lemma wts_label_d: "(p, ([l],d), q) \<in> wts_to_monoidLTS ts \<Longrightarrow> ts $ (p,l,q) = d"
  unfolding wts_to_monoidLTS_def by blast

lemma wts_label_d': "(p, w, q) \<in> wts_to_monoidLTS ts \<Longrightarrow> ts $ (p, hd(fst w), q) = snd w"
  unfolding wts_to_monoidLTS_def by auto

lemma mstar_wts_one: "(p, w, q) \<in> monoid_rtrancl (wts_to_monoidLTS ts) \<Longrightarrow> fst w = 1 \<Longrightarrow> snd w = 1"
proof (induct rule: monoid_rtrancl.induct)
  case (monoid_rtrancl_refl a)
  then show ?case by (simp add: one_prod_def)
next
  case (monoid_rtrancl_into_rtrancl a w b l c)
  from \<open>(b, l, c) \<in> wts_to_monoidLTS ts\<close> have "fst l \<noteq> []" using wts_label_not_empty by fast
  then have \<open>fst (w \<cdot> l) \<noteq> []\<close> by (simp add: mult_prod_def times_list_def)
  then show ?case by (simp add: monoid_rtrancl_into_rtrancl.prems one_list_def)
qed
lemma mstar_wts_empty_one: "(p, ([],d), q) \<in> monoid_rtrancl (wts_to_monoidLTS ts) \<Longrightarrow> d = 1"
  using mstar_wts_one by (simp add: one_list_def, fastforce)

lemma monoid_star_pop':
  assumes "(p, w, q) \<in> monoid_rtrancl (wts_to_monoidLTS ts)"
  assumes "fst w = []"
  shows " p = q"
  using assms
proof (induct rule: monoid_rtrancl.induct)
  case (monoid_rtrancl_refl a)
  then show ?case by simp
next
  case (monoid_rtrancl_into_rtrancl a w b l c)
  from \<open>(b, l, c) \<in> wts_to_monoidLTS ts\<close> have "fst l \<noteq> []" using wts_label_not_empty by fast
  then have \<open>fst (w \<cdot> l) \<noteq> []\<close> by (simp add: mult_prod_def times_list_def)
  then show ?case by (simp add: monoid_rtrancl_into_rtrancl.prems)
qed
lemma monoid_star_pop:
  assumes "(Init p, (lbl w, d), q) \<in> monoidLTS.monoid_star (wts_to_monoidLTS ts)"
  assumes "w = pop"
  shows   "q = Init p \<and> d = 1"
  using assms monoid_star_pop' by (auto simp add: one_list_def mstar_wts_empty_one) fastforce

lemma monoid_star_swap':
  assumes "(p, w, q) \<in> monoid_rtrancl (wts_to_monoidLTS ts)"
  assumes "fst w = [l]"
  shows "ts $ (p,l,q) = snd w"
  using assms
proof (induct rule: monoid_rtrancl.induct)
  case (monoid_rtrancl_refl a)
  then show ?case by (simp add: one_prod_def one_list_def)
next
  case (monoid_rtrancl_into_rtrancl a w b w' c)
  then have "fst w = []" 
    by (simp add: mult_prod_def times_list_def append_eq_Cons_conv wts_label_not_empty[of b w' c ts])
  then show ?case 
    using monoid_rtrancl_into_rtrancl.hyps monoid_rtrancl_into_rtrancl.prems
          monoid_star_pop'[of a w b ts] mstar_wts_one[of a w b ts] wts_label_d'[of b w' c ts]
    by (simp add: mult_prod_def one_list_def times_list_def)
qed
lemma monoid_star_swap:
  assumes "(Init p, (lbl w, d), q) \<in> monoidLTS.monoid_star (wts_to_monoidLTS ts)"
  assumes "w = swap l"
  shows "ts $ (Init p,l,q) = d"
  using assms monoid_star_swap' by fastforce

lemma monoid_star_push':
  assumes "(p, w, q) \<in> monoid_rtrancl (wts_to_monoidLTS ts)"
  assumes "fst w = [l,l']"
  shows "\<exists>q'. ts $ (p,l,q') * ts $ (q',l',q) = snd w"
  using assms
proof (induct rule: monoid_rtrancl.induct)
  case (monoid_rtrancl_refl a)
  then show ?case by (simp add: one_prod_def one_list_def)
next
  case (monoid_rtrancl_into_rtrancl a w b w' c)
  then have "fst w = [l] \<and> fst w' = [l']" 
    using wts_label_exist[of b w' c ts] 
    by (auto simp add: times_list_def mult_prod_def)
  then show ?case 
    using monoid_rtrancl_into_rtrancl.hyps monoid_rtrancl_into_rtrancl.prems 
          monoid_star_swap'[of a w b ts l] monoid_star_swap'[of b w' c ts l'] wts_label_d'[of b w' c ts]    
    by (simp add: mult_prod_def) metis
qed
lemma monoid_star_push:
  assumes "(Init p, (lbl w, d), q) \<in> monoidLTS.monoid_star (wts_to_monoidLTS ts)"
  assumes "w = push l l'"
  shows "\<exists>q'. ts $ (Init p,l,q') * ts $ (q',l',q) = d"
  using assms monoid_star_push' by fastforce

lemma pre_star_rule_cases:
  assumes "(Init p, (lbl w, d), q) \<in> monoidLTS.monoid_star (wts_to_monoidLTS ts)"
  shows "(w = pop \<and> q = Init p \<and> d = 1) \<or>                          
         (\<exists>l. w = swap l \<and> ts $ (Init p,l,q) = d) \<or> 
         (\<exists>l l'. w = push l l' \<and> (\<exists>q'. ts $ (Init p,l,q') * ts $ (q',l',q) = d))"
proof (cases rule: operation.exhaust[of w])
  case pop
  then show ?thesis using monoid_star_pop[OF assms(1)] by simp
next
  case (swap l)
  then show ?thesis using monoid_star_swap[OF assms(1)] by simp
next
  case (push l l')
  then show ?thesis using monoid_star_push[OF assms(1)] by simp
qed
lemma pre_star_rule_exhaust:
  assumes "(Init p, (lbl w, d), q) \<in> monoidLTS.monoid_star (wts_to_monoidLTS ts)"
  assumes "q = Init p \<and> d = 1 \<Longrightarrow> P"
  assumes "\<And>l. ts $ (Init p,l,q) = d \<Longrightarrow> P"
  assumes "\<And>l l'. \<exists>q'. ts $ (Init p,l,q') * ts $ (q',l',q) = d \<Longrightarrow> P"
  shows "P"
  using pre_star_rule_cases[OF assms(1)] assms(2,3,4) by blast

lemma pre_star_rule_update_is_Init:
  assumes "pre_star_rule A A'"
      and "A $ (p,\<gamma>,q) \<noteq> A' $ (p,\<gamma>,q)"
    shows "is_Init p"
  using assms unfolding pre_star_rule.simps
  apply safe
  subgoal for p' by (cases "p = Init p'", auto)
  done
lemma pre_star_rule_update_inits:
  assumes "pre_star_rule A A'"
      and "A $ (p,\<gamma>,q) \<noteq> A' $ (p,\<gamma>,q)"
    shows "p \<in> inits"
  using pre_star_rule_update_is_Init[OF assms] unfolding inits_def by simp

lemma pre_star_rule_update_spec':
  assumes "pre_star_rule A A'"
      and "A $ (Init p,\<gamma>,q) \<noteq> A' $ (Init p,\<gamma>,q)"
    shows "\<exists>d d' p' w. A' $ (Init p,\<gamma>,q) = A $ (Init p, \<gamma>, q) + d \<cdot> d' \<and> (p, \<gamma>) \<midarrow>d\<hookrightarrow> (p', w) \<and> (Init p', (lbl w, d'), q) \<in> monoid_rtrancl (wts_to_monoidLTS A) \<and> A $ (Init p, \<gamma>, q) + d \<cdot> d' \<noteq> A $ (Init p, \<gamma>, q)"
  using assms unfolding pre_star_rule.simps
  apply safe
  subgoal for p' \<gamma>' _ _ _ _ q'
    by (cases "(p,\<gamma>,q) = (p', \<gamma>',q')", auto)
  done
lemma pre_star_rule_update_spec:
  assumes "pre_star_rule A A'"
      and "A $ (p,\<gamma>,q) \<noteq> A' $ (p,\<gamma>,q)"
    shows "\<exists>d d' p' w. A' $ (p,\<gamma>,q) = A $ (p, \<gamma>, q) + d \<cdot> d' \<and> (the_Ctr_Loc p, \<gamma>) \<midarrow>d\<hookrightarrow> (p', w) \<and> (Init p', (lbl w, d'), q) \<in> monoid_rtrancl (wts_to_monoidLTS A) \<and> A $ (p, \<gamma>, q) + d \<cdot> d' \<noteq> A $ (p, \<gamma>, q)"
  using assms pre_star_rule_update_is_Init[OF assms]
        pre_star_rule_update_spec'[OF assms(1), of "the_Ctr_Loc p" \<gamma> q]
  by simp

lemma inits_not_noninits: "p \<in> inits \<Longrightarrow> p \<in> noninits \<Longrightarrow> False"
  unfolding inits_def noninits_def by auto

lemma not_inits_is_noninits: "isols = {} \<Longrightarrow> p \<notin> inits \<Longrightarrow> p \<in> noninits"
  unfolding inits_def noninits_def isols_def using state.exhaust_disc by auto

definition pre_star_precondition :: "(('ctr_loc, 'noninit, 'label) state, 'label, 'weight) w_transitions \<Rightarrow> bool" where
  "pre_star_precondition A \<equiv> (inits \<subseteq> LTS.srcs (wts_to_monoidLTS A) \<and> isols = {})"
definition pre_star_invariant :: "(('ctr_loc, 'noninit, 'label) state, 'label, 'weight) w_transitions \<Rightarrow> bool" where
  "pre_star_invariant A \<equiv> (isols = {})"
 
lemma q_not_inits:
  assumes "pre_star_precondition A"
  assumes "A $ (p,\<gamma>,q) \<noteq> 0"
  shows "q \<notin> inits"
  using assms unfolding pre_star_precondition_def LTS.srcs_def wts_to_monoidLTS_def by auto

lemma q_noninits:
  assumes "pre_star_precondition A"
  assumes "A $ (p,\<gamma>,q) \<noteq> 0"
  shows "q \<in> noninits"
  using q_not_inits[OF assms] assms(1) not_inits_is_noninits 
  unfolding pre_star_precondition_def by presburger

lemma 
  assumes "pre_star_precondition A"
      and "pre_star_rule A A'"
      and "A' $ (p,\<gamma>,q) \<noteq> 0"
      and "p \<in> noninits"
    shows "q \<in> noninits"
proof -
  have "A $ (p,\<gamma>,q) = A' $ (p,\<gamma>,q)" using pre_star_rule_update_inits[OF assms(2)] assms(4) unfolding inits_def noninits_def by blast
  then show ?thesis using assms(1,3) q_noninits by metis
qed

lemma 
  assumes "pre_star_precondition A"
  assumes "pre_star_rule A A'"
  shows   "A' $ (p,\<gamma>,q) \<noteq> 0 \<and> A' $ (p,\<gamma>,q) \<noteq> 1 \<Longrightarrow> p \<in> inits"
  using assms
  oops

lemma
  assumes "inits \<subseteq> LTS.srcs (wts_to_monoidLTS A)"
  shows   "accepts A (Noninit q, w) = 1"
  using assms
  oops

lemma 
  assumes "inits \<subseteq> LTS.srcs (wts_to_monoidLTS A)"
  shows   "A $ (Init p, \<gamma>, Init p') \<le> pop_seq p \<gamma> p'"
  using assms
  oops

definition word_of_trace :: "('ctr_loc, 'label) trace \<Rightarrow> 'label list" where
  "word_of_trace t = map (fst) (snd t)"
fun trace_to_pops :: "('ctr_loc, 'label) trace \<Rightarrow> ('ctr_loc \<times> 'label \<times> 'ctr_loc) list" where
  "trace_to_pops (p,[]) = []"
| "trace_to_pops (p,((\<gamma>,p')#xs)) = (p,\<gamma>,p')#(trace_to_pops (p',xs))"

definition trace_pop_seq_sum :: "('ctr_loc, 'label) trace \<Rightarrow> 'weight" where
  "trace_pop_seq_sum t = foldr (\<lambda>(p,\<gamma>,p') d. pop_seq p \<gamma> p' * d) (trace_to_pops t) 1"

fun is_final_trace :: "('ctr_loc, 'noninit, 'label) final_trace \<Rightarrow> bool" where
  "is_final_trace (pops,[]) = (Init (last pops) \<in> finals)"
| "is_final_trace (_,t) = (Noninit (snd (List.last t)) \<in> finals)"

definition word_of_final_trace :: "('ctr_loc, 'noninit, 'label) final_trace \<Rightarrow> 'label list" where
  "word_of_final_trace ft = (word_of_trace (fst ft)) @ map (fst) (snd ft)"

definition final_trace_accepts :: "('ctr_loc, 'noninit, 'label) final_trace \<Rightarrow> 'ctr_loc \<Rightarrow> 'label list \<Rightarrow> bool" where
  "final_trace_accepts t p w \<equiv> is_final_trace t \<and> first (fst t) = p \<and> word_of_final_trace t = w" 

fun noninit_trace_weight :: "'ctr_loc \<Rightarrow> ('label \<times> 'noninit) list \<Rightarrow> 'weight" where 
  "noninit_trace_weight p [] = 1"
| "noninit_trace_weight p ((\<gamma>,q)#qs) = 1" (* weight_of (p,\<gamma>,q)" *)

definition final_trace_weight_sum :: "('ctr_loc, 'noninit, 'label) final_trace \<Rightarrow> 'weight" where
  "final_trace_weight_sum ft = trace_pop_seq_sum (fst ft) * (noninit_trace_weight (last (fst ft)) (snd ft))"


lemma "accepts A (p,w) = \<Sigma>{final_trace_weight_sum t | t::(('ctr_loc, 'noninit, 'label) final_trace). final_trace_accepts t p w}"
  
  (* Not quite enough... Need to look at path from (last t) to a final state *)
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