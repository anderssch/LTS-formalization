theory WAutomaton
  imports "LTS" "Saturation" "ReverseWellQuasiOrder" "FinFunWellFounded" "MonoidLTS" "Kleene_Algebra.Dioid_models" "Set_More"
begin

\<comment> \<open>For the semantics of a weighted automaton, labels are lifted to the list-monoid and paired with a weight\<close>
type_synonym ('label, 'weight) wautomaton_label = "('label list \<times> 'weight)" 

\<comment> \<open>Weighted automata transitions are modelled as a @{term finfun} from transitions to their weight, 
    where @{term "0::('weight::bounded_idempotent_semiring)"} is the default value, indicating no transition.\<close>
type_synonym ('state, 'label, 'weight) w_transitions = "('state, 'label) transition \<Rightarrow>f 'weight" 

type_synonym ('state, 'label, 'weight) w_transition_set = "('state, ('label list \<times> 'weight)) transition set"


\<comment> \<open>Embed a weighted automaton into a monoidLTS. All non-zero transitions are added. The label is lifted to the list-monoid.\<close>
definition wts_to_monoidLTS :: "('state, 'label, 'weight::bounded_idempotent_semiring) w_transitions \<Rightarrow> ('state, ('label list \<times> 'weight)) transition set" where
  "wts_to_monoidLTS ts = {(p, ([l],d), q) | p l d q. ts $ (p,l,q) = d}"

lemma finite_wts: 
  assumes "finfun_default A = 0"
  shows "finite (wts_to_monoidLTS A)"
  unfolding wts_to_monoidLTS_def
  oops
(* proof -
  have "finite {x. A $ x \<noteq> 0}" 
    using finite_finfun_default[of A] assms by simp
  then show "finite {(p, ([l],d), q) | p l d q. A $ (p,l,q) = d \<and> d \<noteq> 0}"
    using finite_image_set[of "\<lambda>x. A $ x \<noteq> 0" "\<lambda>(p,l,q). (p, ([l], A $ (p,l,q)), q)"] by simp
qed
*)

lemma countable_wts: 
  fixes A :: "(('state::countable, 'label::finite, 'weight::bounded_idempotent_semiring) w_transitions)"
  shows "countable (wts_to_monoidLTS A)"
proof -
  have count1: "countable (UNIV :: ('state \<times> 'label \<times> 'state) set)"
    by blast
  have "{(p, ([l], d), q)| p l d q. A $ (p, l, q) = d} = (\<lambda>(p, l, q). (p, ([l], A $ (p, l, q)), q)) ` UNIV"
    unfolding image_def by auto
  then have "countable {(p, ([l], d), q)| p l d q. A $ (p, l, q) = d}"
    using count1 by auto
  then show ?thesis
    unfolding wts_to_monoidLTS_def by auto
qed

lemma monoid_rtrancl_wts_to_monoidLTS_refl:
  "(p, ([], 1), p) \<in> monoid_rtrancl (wts_to_monoidLTS A)"
  by (metis monoid_rtrancl_refl one_list_def one_prod_def)

locale W_automaton = monoidLTS "wts_to_monoidLTS transition_relation"
  for transition_relation :: "('state::finite, 'label, 'weight::bounded_idempotent_semiring) w_transitions" +
  fixes initials :: "'state set" and finals :: "'state set"
begin
interpretation monoidLTS "wts_to_monoidLTS transition_relation" ..
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

lemma finite_monoidLTS_reach:
  assumes "finite ts"
  shows "finite (monoidLTS_reach p w)"
proof (induct rule: monoidLTS_reach.induct)
  case (1 p)
  then show ?case by simp
next
  case (2 p \<gamma> w)
  then show ?case using assms
    by (fastforce simp: dissect_set)
qed

end

lemma monoid_star_imp_exec: "(p,w,q) \<in> monoid_rtrancl (wts_to_monoidLTS ts) \<Longrightarrow> (q, snd w) \<in> monoidLTS_reach (wts_to_monoidLTS ts) p (fst w)"
  apply (induct rule: monoid_rtrancl_induct_rev)
  apply (force simp add: one_prod_def one_list_def)
  by (fastforce simp add: mult_prod_def times_list_def wts_to_monoidLTS_def)

lemma monoidLTS_reach_imp: "(q, d) \<in> monoidLTS_reach (wts_to_monoidLTS ts) p w \<Longrightarrow> (p,(w,d),q) \<in> monoid_rtrancl (wts_to_monoidLTS ts)"
  apply (induct p w arbitrary: d rule: monoidLTS_reach.induct[of _ "wts_to_monoidLTS ts"])
   apply (simp add: monoid_rtrancl_refl[of q "wts_to_monoidLTS ts", unfolded one_prod_def one_list_def])
  subgoal for p \<gamma> w'
    apply auto[1]
    subgoal for _ _ _ _ q' d d'
      using monoid_rtrancl_into_rtrancl_rev[of p "([\<gamma>],d)" q' "wts_to_monoidLTS ts" "(w',d')" q]
      apply (auto simp add: mult_prod_def times_list_def wts_to_monoidLTS_def)
      by (metis empty_iff singleton_iff fst_eqD snd_eqD)
    done
  done
lemma monoid_star_code[code_unfold]: "(p,(w,d),q) \<in> monoid_rtrancl (wts_to_monoidLTS ts) \<longleftrightarrow> (q,d) \<in> monoidLTS_reach (wts_to_monoidLTS ts) p w"
  using monoidLTS_reach_imp monoid_star_imp_exec by fastforce


context fixes ts :: "('state, 'label list \<times> 'weight::idempotent_semiring) transition set" begin
fun monoidLTS_reach_not0 where
  "monoidLTS_reach_not0 p [] = {(p,1)}"
| "monoidLTS_reach_not0 p (\<gamma>#w) = (\<Union>(q',d) \<in> (\<Union>(p',(\<gamma>',d),q') \<in> ts. if p' = p \<and> \<gamma>' = [\<gamma>] \<and> d \<noteq> 0 then {(q',d)} else {}).
      {(q,d*d') | q d'. (q,d') \<in> monoidLTS_reach_not0 q' w})"

lemma finite_monoidLTS_reach_not0:
  assumes "finite ts"
  shows "finite (monoidLTS_reach_not0 p w)"
proof (induct rule: monoidLTS_reach_not0.induct)
  case (1 p)
  then show ?case by simp
next
  case (2 p \<gamma> w)
  then show ?case using assms by (fastforce simp: dissect_set)
qed
end


lemma monoid_star_n0_imp_exec: "(p,w,q) \<in> monoid_rtrancl (wts_to_monoidLTS ts) \<Longrightarrow> snd w = 0 \<or> (q, snd w) \<in> monoidLTS_reach_not0 (wts_to_monoidLTS ts) p (fst w)"
proof (induct rule: monoid_rtrancl_induct_rev)
  case (monoid_rtrancl_refl a)
  then show ?case by (force simp add: one_prod_def one_list_def)
next
  case (monoid_rtrancl_into_rtrancl p w p' q w')
  then obtain l where l:"[l] = fst w" unfolding wts_to_monoidLTS_def by force
  then have lw': "l # fst w' = fst (w * w')" unfolding mult_prod_def times_list_def by fastforce
  define d where "d = snd w"
  define d' where "d' = snd w'"
  have dd': "d * d' = snd (w * w')" using d_def d'_def unfolding mult_prod_def by fastforce
  have w: "w = ([l], d)" using l d_def by simp
  show ?case
  proof (cases "d * d' = 0")
    case True
    then show ?thesis unfolding mult_prod_def dd' by simp
  next
    case False
    then have d0:"d \<noteq> 0" and "d' \<noteq> 0" by auto
    then have "(q, d') \<in> monoidLTS_reach_not0 (wts_to_monoidLTS ts) p' (fst w')"
      using monoid_rtrancl_into_rtrancl(2) d'_def by blast
    then have "(q, d * d') \<in> monoidLTS_reach_not0 (wts_to_monoidLTS ts) p (l # fst w')"
      using monoid_rtrancl_into_rtrancl(1) False w d0 by fastforce
    then show ?thesis using lw' dd' by argo
  qed
qed

lemma monoidLTS_reach_n0_cons_exists:
  assumes "(q, d) \<in> monoidLTS_reach_not0 (wts_to_monoidLTS ts) p (\<gamma> # w)"
  shows "\<exists>p' d' d''. (p, ([\<gamma>], d'), p') \<in> wts_to_monoidLTS ts \<and> (q, d'') \<in> monoidLTS_reach_not0 (wts_to_monoidLTS ts) p' w \<and> d' \<noteq> 0 \<and> d = d' * d''"
  using assms by (simp, safe) (metis empty_iff prod.inject singletonD)

lemma monoidLTS_reach_n0_imp: "(q, d) \<in> monoidLTS_reach_not0 (wts_to_monoidLTS ts) p w \<Longrightarrow> (p,(w,d),q) \<in> monoid_rtrancl (wts_to_monoidLTS ts)"
proof (induct p w arbitrary: d rule: monoidLTS_reach_not0.induct[of _ "wts_to_monoidLTS ts"])
  case (1 p d)
  then show ?case by (simp add: monoid_rtrancl_refl[of p "wts_to_monoidLTS ts", unfolded one_prod_def one_list_def])
next
  case (2 p \<gamma> w d)
  from 2(2) obtain p' d' d''
    where *:"(p, ([\<gamma>], d'), p') \<in> wts_to_monoidLTS ts"
            "(q, d'') \<in> monoidLTS_reach_not0 (wts_to_monoidLTS ts) p' w"
            "d = d' * d''" and "d' \<noteq> 0" using monoidLTS_reach_n0_cons_exists by meson
  then have "(p', d') \<in> (\<Union>(p', (\<gamma>', d), q')\<in>wts_to_monoidLTS ts. if p' = p \<and> \<gamma>' = [\<gamma>] \<and> d \<noteq> 0 then {(q', d)} else {})"
    by fastforce
  then show ?case 
    using * 2(1) monoid_rtrancl_into_rtrancl_rev[of p "([\<gamma>],d')" p' "wts_to_monoidLTS ts" "(w,d'')" q]
    unfolding mult_prod_def times_list_def by auto
qed

lemma monoid_star_n0_code[code_unfold]: "d \<noteq> 0 \<Longrightarrow> (p,(w,d),q) \<in> monoid_rtrancl (wts_to_monoidLTS ts) \<longleftrightarrow> (q,d) \<in> monoidLTS_reach_not0 (wts_to_monoidLTS ts) p w"
  using monoidLTS_reach_n0_imp monoid_star_n0_imp_exec by fastforce


\<comment> \<open>Auxiliary lemmas for WAutomaton and monoidLTS\<close>
lemma wts_label_exist: "(p, w, q) \<in> wts_to_monoidLTS ts \<Longrightarrow> \<exists>l. fst w = [l]"
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
  then have "fst (w * l) \<noteq> []" by (simp add: mult_prod_def times_list_def)
  then show ?case by (simp add: monoid_rtrancl_into_rtrancl.prems one_list_def)
qed
lemma mstar_wts_empty_one: "(p, ([],d), q) \<in> monoid_rtrancl (wts_to_monoidLTS ts) \<Longrightarrow> d = 1"
  using mstar_wts_one by (simp add: one_list_def, fastforce)

lemma wts_to_monoidLTS_exists: (* TODO: rename *)
  assumes "w23 = [l]"
  shows "\<exists>dp23. (p2, (w23, dp23), p3) \<in> wts_to_monoidLTS ts1"
  using assms wts_to_monoidLTS_def by fastforce

lemma wts_to_monoidLTS_exists_iff:
  "(\<exists>dp23. (p2, (w23, dp23), p3) \<in> wts_to_monoidLTS ts1) \<longleftrightarrow> (\<exists>l. w23 = [l])"
  using wts_label_exist wts_to_monoidLTS_exists by fastforce



\<comment> \<open>Unfold monoid_closure of transitions for 0, 1 and 2 transitions\<close>
  
lemma monoid_star_w0:
  assumes "(p, w, q) \<in> monoid_rtrancl (wts_to_monoidLTS ts)"
  assumes "fst w = []"
  shows "p = q"
  using assms
proof (induct rule: monoid_rtrancl.induct)
  case (monoid_rtrancl_refl a)
  then show ?case by simp
next
  case (monoid_rtrancl_into_rtrancl a w b l c)
  from \<open>(b, l, c) \<in> wts_to_monoidLTS ts\<close> have "fst l \<noteq> []" using wts_label_not_empty by fast
  then have "fst (w * l) \<noteq> []" by (simp add: mult_prod_def times_list_def)
  then show ?case by (simp add: monoid_rtrancl_into_rtrancl.prems)
qed

lemma monoid_star_w1:
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
          monoid_star_w0[of a w b ts] mstar_wts_one[of a w b ts] wts_label_d'[of b w' c ts]
    by (simp add: mult_prod_def one_list_def times_list_def)
qed

lemma monoid_star_w2:
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
          monoid_star_w1[of a w b ts l] monoid_star_w1[of b w' c ts l'] wts_label_d'[of b w' c ts]    
    by (simp add: mult_prod_def) metis
qed

lemma mstar_wts_cons:
  assumes "(p, (l # w, d), q) \<in> monoid_rtrancl (wts_to_monoidLTS ts)"
  shows   "\<exists>d' p' d''. d = d' * d'' \<and> (p, ([l], d'), p') \<in> wts_to_monoidLTS ts \<and> (p', (w, d''), q) \<in> monoid_rtrancl (wts_to_monoidLTS ts)"
  using assms monoid_rtrancl_simps_rev[of p "(l#w, d)" q "wts_to_monoidLTS ts", unfolded mult_prod_def times_list_def one_prod_def one_list_def, simplified]
  apply (simp, safe, simp)
  subgoal for l' d' p' w' d''
    apply (rule exI[of _ d'], rule exI[of _ p'], rule exI[of _ d''])
    unfolding wts_to_monoidLTS_def by force
  done

lemma finite_mstar_wts_weights:
  assumes "finite (wts_to_monoidLTS ts)"
  shows   "finite {d. \<exists>p q. (p, (w, d), q) \<in> monoid_rtrancl (wts_to_monoidLTS ts)}"
proof (induct w)
  case Nil
  then show ?case
    using finite_subset[of "{d. \<exists>p q. (p, ([], d), q) \<in> monoid_rtrancl (wts_to_monoidLTS ts)}" "{1}"]
          mstar_wts_empty_one[of _ _ _ ts] by fast
next
  case (Cons l w)
  have f1:"finite {(p, ([l], d), q) |p d q. (p, ([l], d), q) \<in> wts_to_monoidLTS ts}"
    using finite_subset[OF _ assms, of "{(p, ([l], d), q)| p d q. (p, ([l], d), q) \<in> wts_to_monoidLTS ts}"]
    by blast
  have "finite {d. \<exists>p q. (p, ([l], d), q) \<in> wts_to_monoidLTS ts}"
    unfolding setcompr_eq_image3[of "\<lambda>p d q. d" "\<lambda>p d q. (p, ([l], d), q) \<in> wts_to_monoidLTS ts", simplified]
    apply (rule finite_imageI)
    using f1[unfolded setcompr_eq_image3[of "\<lambda>p d q. (p, ([l], d), q)" "\<lambda>p d q. (p, ([l], d), q) \<in> wts_to_monoidLTS ts", simplified]]
    apply (rule finite_imageD)
    unfolding inj_on_def by fastforce
  then have "finite {d * d' |d d'. (\<exists>p q. (p, ([l], d), q) \<in> wts_to_monoidLTS ts) \<and> (\<exists>p q. (p, (w, d'), q) \<in> monoid_rtrancl (wts_to_monoidLTS ts))}"
    using finite_image_set2 Cons by fast
  moreover have "{d. \<exists>p q. (p, (l # w, d), q) \<in> monoid_rtrancl (wts_to_monoidLTS ts)} 
              \<subseteq> {d * d' |d d'. (\<exists>p q. (p, ([l], d), q) \<in> wts_to_monoidLTS ts) \<and> (\<exists>p q. (p, (w, d'), q) \<in> monoid_rtrancl (wts_to_monoidLTS ts))}"
    apply safe
    subgoal for d p q
      using mstar_wts_cons by fast
    done
  ultimately show ?case using finite_subset by fast
qed



\<comment> \<open>For the executable pre-star, the saturation rule computes a set of new transition weights, 
    that are updated using the dioid's plus operator to combine with the existing value.\<close>
definition finfun_update_plus :: "'a \<Rightarrow> 'b \<Rightarrow> ('a \<Rightarrow>f 'b::idempotent_ab_semigroup_add) \<Rightarrow> ('a \<Rightarrow>f 'b)" where
  "finfun_update_plus a b f = f(a $:= (f$a) + b)"

definition finfun_update_plus_pair :: "('a \<times> 'b) \<Rightarrow> ('a \<Rightarrow>f 'b::idempotent_ab_semigroup_add) \<Rightarrow> ('a \<Rightarrow>f 'b)" where
  "finfun_update_plus_pair p = finfun_update_plus (fst p) (snd p)"

definition update_wts :: "('a \<Rightarrow>f 'b::idempotent_comm_monoid_add) \<Rightarrow> ('a \<times> 'b) set \<Rightarrow> ('a \<Rightarrow>f 'b)" where
  "update_wts = Finite_Set.fold finfun_update_plus_pair"

lemma finfun_update_plus_apply: "finfun_update_plus a b f $ a = f $ a + b"
  unfolding finfun_update_plus_def by simp
lemma finfun_update_plus_apply_other: "a \<noteq> x \<Longrightarrow> finfun_update_plus x b f $ a = f $ a"
  unfolding finfun_update_plus_def by simp
lemma finfun_update_plus_pair_apply: "finfun_update_plus_pair (a,b) f $ a = f $ a + b"
  unfolding finfun_update_plus_pair_def using finfun_update_plus_apply by force
lemma finfun_update_plus_pair_apply_other: "a \<noteq> x \<Longrightarrow> finfun_update_plus_pair (x,b) f $ a = f $ a"
  unfolding finfun_update_plus_pair_def using finfun_update_plus_apply_other by fastforce

lemma finfun_update_plus_commute: "finfun_update_plus a b \<circ> finfun_update_plus a' b' = finfun_update_plus a' b' \<circ> finfun_update_plus a b"
  apply (cases "a = a'")
  unfolding finfun_update_plus_def
   apply (simp add: comp_def add.commute add.left_commute)
  using FinFun.finfun_comp_aux.upd_commute by fastforce

lemma finfun_update_plus_idem: "finfun_update_plus a b \<circ> finfun_update_plus a b = finfun_update_plus a b"
  unfolding finfun_update_plus_def comp_def using finfun_upd_apply_same
  by (simp add: add.commute idempotent_ab_semigroup_add_class.add_left_idem)

lemma finfun_update_plus_pair_idem: "comp_fun_idem finfun_update_plus_pair"
  apply standard
  subgoal for x y
    unfolding finfun_update_plus_pair_def using finfun_update_plus_commute by fast
  subgoal for x
    unfolding finfun_update_plus_pair_def using finfun_update_plus_idem by fast
  done
lemma finfun_update_plus_pair_idem_on_UNIV: "comp_fun_idem_on UNIV finfun_update_plus_pair"
  using finfun_update_plus_pair_idem by (simp add: comp_fun_idem_def')

lemma update_wts_insert:
  assumes "finite S"
  shows "update_wts f (insert x S) = finfun_update_plus_pair x (update_wts f S)"
  unfolding update_wts_def
  using assms comp_fun_idem_on.fold_insert_idem[OF finfun_update_plus_pair_idem_on_UNIV]
  by blast

lemma sum_insert_fresh:
  fixes S::"('a \<times> 'b::idempotent_comm_monoid_add) set"
  assumes "finite S"
      and "(x,y) \<notin> S"
    shows "\<Sum> {b. (x, b) \<in> S} + y = \<Sum> {b. (x, b) \<in> insert (x,y) S}"
proof -
  have "finite {b. (x, b) \<in> S}" using assms(1) by (induct S, auto)
  moreover have "y \<notin> {b. (x, b) \<in> S}" using assms(2) by simp
  ultimately have "\<Sum> {b. (x, b) \<in> S} + y = \<Sum> (insert y {b. (x, b) \<in> S})" 
    by (simp add: add.commute)
  moreover have "{b. (x, b) \<in> insert (x,y) S} = insert y {b. (x, b) \<in> S}" by blast
  ultimately show ?thesis by simp
qed

lemma finfun_update_plus_pair_insert:
  fixes S::"('a \<times> 'b::idempotent_comm_monoid_add) set"
  assumes "finite S"          
  assumes "(x,y) \<notin> S"
  assumes "f' $ a = f $ a + \<Sum> {b. (a, b) \<in> S}"
  shows "finfun_update_plus_pair (x,y) f' $ a = f $ a + \<Sum> {b. (a, b) \<in> insert (x,y) S}"
proof (cases "a = x")
  case True
  then have "finfun_update_plus_pair (x,y) f' $ a = f $ x + \<Sum> {b. (x, b) \<in> S} + y"
    using finfun_update_plus_pair_apply[of x y f'] assms(3) by simp
  moreover have "f $ a + \<Sum> {b. (x, b) \<in> S} + y = f $ a + \<Sum> {b. (x, b) \<in> insert (x,y) S}" 
    using sum_insert_fresh[OF assms(1,2)] by (simp add: ab_semigroup_add_class.add_ac(1))
  ultimately show ?thesis using \<open>a = x\<close> by simp
next
  case False
  then show ?thesis using assms(3) finfun_update_plus_pair_apply_other[OF \<open>a \<noteq> x\<close>, of y f'] by simp
qed

lemma update_wts_step:
  assumes "finite S"
  assumes "x \<notin> S"
  assumes "update_wts f S $ a = f $ a + \<Sum> {b. (a, b) \<in> S}" 
  shows   "update_wts f (insert x S) $ a = f $ a + \<Sum> {b. (a, b) \<in> insert x S}"
  using update_wts_insert[OF assms(1)] assms(2,3) 
        finfun_update_plus_pair_insert[OF assms(1), of "fst x" "snd x"] by simp

theorem update_wts_sum:
  assumes "finite S"
  shows "(update_wts f S) $ a = f $ a + \<Sum>{b. (a,b) \<in> S}"
  using assms
  apply (induct S, simp add: update_wts_def)
  subgoal for x F
    using update_wts_step[of F x] by auto
  done

lemma update_wts_empty: "update_wts f {} = f"
  by (rule finfun_ext) (simp add: update_wts_sum[of "{}" f])

lemma update_wts_less_eq:
  fixes S::"('a \<times> 'b::idempotent_comm_monoid_add_ord) set"
  assumes "finite S"
  shows "(update_wts f S) \<le> f"
  unfolding less_eq_finfun_def using update_wts_sum[OF assms, of f] by simp

lemma sum_snd_insert: 
  fixes S::"('a \<times> 'b::idempotent_comm_monoid_add) set"
  assumes "finite S"
  shows "\<Sum> {b. b = y \<or> (x, b) \<in> S} = y + \<Sum> {b. (x, b) \<in> S}"
proof -
  have "{b. (x, b) \<in> S} = snd ` (S \<inter> ({x} \<times> UNIV))" by force
  then have "finite {b. (x, b) \<in> S}" using assms by simp
  moreover have "insert y {b. (x, b) \<in> S} = {b. b = y \<or> (x, b) \<in> S}" by fast
  ultimately show "\<Sum> {b. b = y \<or> (x, b) \<in> S} = y + \<Sum> {b. (x, b) \<in> S}"
    using idem_sum_insert[of "{b. (x, b) \<in> S}" y] by argo
qed

lemma update_wts_insert_unfold:
  fixes S::"('a \<times> 'b::idempotent_comm_monoid_add) set"
  assumes "finite S"
  shows "update_wts f (insert (x,y) S) = update_wts f(x $:= f $ x + y) S"
  apply (rule finfun_ext)
  subgoal for a
    unfolding update_wts_sum[OF assms, of "f(x $:= f $ x + y)" a] 
              update_wts_sum[of "(insert (x,y) S)" f a, simplified, OF assms]
proof (cases "a = x")
  case True
  show "f $ a + \<Sum> {b. a = x \<and> b = y \<or> (a, b) \<in> S} = f(x $:= f $ x + y) $ a + \<Sum> {b. (a, b) \<in> S}" 
    using sum_snd_insert[OF assms] True by (simp add: ac_simps(1))
next
  case False
  then show "f $ a + \<Sum> {b. a = x \<and> b = y \<or> (a, b) \<in> S} = f(x $:= f $ x + y) $ a + \<Sum> {b. (a, b) \<in> S}"
    by simp
qed done

lemma update_wts_insert_absorb:
  fixes S::"('a \<times> 'b::idempotent_comm_monoid_add) set"
  assumes "finite S"
  assumes "f $ x = f $ x + y"
  shows "update_wts f (insert (x,y) S) = update_wts f S"
  using update_wts_insert_unfold[OF assms(1)] assms(2) by simp

lemma sum_snd_with_zeros:
  fixes A B :: "('a \<times> 'b::idempotent_comm_monoid_add) set"
  assumes "A \<subseteq> B"
      and "B \<subseteq> A \<union> {u. \<exists>q. u = (q, 0)}"
      and "finite A"
    shows "\<Sum> {b. (a, b) \<in> A} = \<Sum> {b. (a, b) \<in> B}"
proof -
  obtain C where C:"C \<subseteq> {u. \<exists>q. u = (q, 0)}" and BAC:"B = A \<union> C" 
    using exists_set_between[OF assms(1,2)] by blast
  then have "\<Sum> {b. (a, b) \<in> A} = \<Sum> {b. (a, b) \<in> A \<union> C}"
  proof (cases "(a,0) \<in> C")
    case True
    then have "{b. (a, b) \<in> ({(a, 0)} \<union> A)} = {b. (a, b) \<in> A \<union> C}"
      using C by blast
    moreover have "\<Sum> {b. (a, b) \<in> A} = \<Sum> {b. (a, b) \<in> ({(a, 0)} \<union> A)}"
      using assms sum_snd_insert[OF assms(3), of 0 a] by simp
    ultimately show ?thesis by argo
  next
    case False
    then have "{b. (a, b) \<in> A} = {b. (a, b) \<in> A \<union> C}"
      using C by blast
    then show ?thesis by argo
  qed
  then show ?thesis using BAC by presburger
qed


\<comment> \<open>A weighted automaton is initialized with weights 1 (neutral element along paths) on existing transitions, 
    and a default weight of 0 (neutral element for combining paths) for non-existing transitions.\<close>
definition ts_to_wts :: "('state, 'label) transition set \<Rightarrow> ('state, 'label, 'weight::bounded_idempotent_semiring) w_transitions" where
  "ts_to_wts ts = update_wts (K$ 0) {(t,1) | t. t \<in> ts}"
definition wts_to_ts :: "('state, 'label, 'weight::bounded_idempotent_semiring) w_transitions \<Rightarrow> ('state, 'label) transition set" where
  "wts_to_ts wts = {t | t. wts $ t \<noteq> 0}"

lemma empty_ts_to_wts[simp]: "ts_to_wts {} = (K$ 0)" 
  unfolding ts_to_wts_def update_wts_def by simp
lemma empty_wts_to_ts[simp]: "wts_to_ts (K$ 0) = {}"
  unfolding wts_to_ts_def by simp



end