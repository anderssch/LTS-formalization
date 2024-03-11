theory WAutomaton
  imports "LTS" "Saturation" "ReverseWellQuasiOrder" "FinFunWellFounded" "FinFunAddUpdate" "MonoidLTS" "Kleene_Algebra.Dioid_models" "Set_More"
begin

declare times_list_def[simp]

\<comment> \<open>For the semantics of a weighted automaton, labels are lifted to the list-monoid and paired with a weight\<close>
type_synonym ('label, 'weight) wautomaton_label = "('label list \<times> 'weight)" 

\<comment> \<open>Weighted automata transitions are modelled as a @{term finfun} from transitions to their weight, 
    where @{term "0::('weight::bounded_idempotent_semiring)"} is the default value, indicating no transition.\<close>
type_synonym ('state, 'label, 'weight) w_transitions = "('state, 'label) transition \<Rightarrow>f 'weight" 

type_synonym ('state, 'label, 'weight) w_transition_set = "('state, ('label list \<times> 'weight)) transition set"


\<comment> \<open>Embed a weighted automaton into a monoidLTS. All non-zero transitions are added. The label is lifted to the list-monoid.\<close>
definition wts_to_monoidLTS :: "('state, 'label, 'weight::bounded_idempotent_semiring) w_transitions \<Rightarrow> ('state, ('label list \<times> 'weight)) transition set" where
  "wts_to_monoidLTS ts = {(p, ([l],d), q) | p l d q. ts $ (p,l,q) = d}"

definition wts_to_weightLTS :: "('state::finite, 'label::finite, 'weight::bounded_idempotent_semiring) w_transitions \<Rightarrow> ('state, 'weight) transition set" where
  "wts_to_weightLTS ts = {(p, d, q) | p l d q. ts $ (p,l,q) = d}"

lemma "finite (wts_to_weightLTS ts)" oops (* THIS should be true!! *)

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
  by (fastforce simp add: wts_to_monoidLTS_def)

lemma monoidLTS_reach_imp: "(q, d) \<in> monoidLTS_reach (wts_to_monoidLTS ts) p w \<Longrightarrow> (p,(w,d),q) \<in> monoid_rtrancl (wts_to_monoidLTS ts)"
  apply (induct p w arbitrary: d rule: monoidLTS_reach.induct[of _ "wts_to_monoidLTS ts"])
   apply (simp add: monoid_rtrancl_refl[of q "wts_to_monoidLTS ts", unfolded one_prod_def one_list_def])
  subgoal for p \<gamma> w'
    apply auto[1]
    subgoal for _ _ _ _ q' d d'
      using monoid_rtrancl_into_rtrancl_rev[of p "([\<gamma>],d)" q' "wts_to_monoidLTS ts" "(w',d')" q]
      apply (auto simp add: wts_to_monoidLTS_def)
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
  then have "fst (w * l) \<noteq> []" by simp
  then show ?case
    using monoid_rtrancl_into_rtrancl.prems by (simp add: monoid_rtrancl_into_rtrancl.prems one_list_def)
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
  then have "fst (w * l) \<noteq> []" by simp
  then show ?case using monoid_rtrancl_into_rtrancl.prems by simp
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
    by (simp add: append_eq_Cons_conv wts_label_not_empty[of b w' c ts])
  then show ?case 
    using monoid_rtrancl_into_rtrancl.hyps monoid_rtrancl_into_rtrancl.prems
          monoid_star_w0[of a w b ts] mstar_wts_one[of a w b ts] wts_label_d'[of b w' c ts]
    by (simp add: one_list_def)
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
    using wts_label_exist[of b w' c ts] by auto
  then show ?case 
    using monoid_rtrancl_into_rtrancl.hyps monoid_rtrancl_into_rtrancl.prems 
          monoid_star_w1[of a w b ts l] monoid_star_w1[of b w' c ts l'] wts_label_d'[of b w' c ts]    
    by simp metis
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

lemma monoid_rtrancl_intros_Cons:
  assumes "(p, ([a], d), q1) \<in> wts_to_monoidLTS ts"
  assumes "(q1, (w, u), q) \<in> monoid_rtrancl (wts_to_monoidLTS ts)"
  shows "(p, (a # w, d*u), q) \<in> monoid_rtrancl (wts_to_monoidLTS ts)"
  using append_Nil assms(1) assms(2) fst_conv monoid_rtrancl_simps_rev by fastforce

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


lemma monoid_star_intros_step':
  assumes "(p,w,q) \<in> wts_to_monoidLTS A"
  shows "(p,w,q) \<in> monoid_rtrancl (wts_to_monoidLTS A)"
  using monoid_rtrancl.intros(2)[of p 1 p "(wts_to_monoidLTS A)" w q] assms
  by (metis monoid_rtrancl.simps mult_1)

lemma monoid_star_intros_step:
  assumes "pwq \<in> wts_to_monoidLTS A"
  shows "pwq \<in> monoid_rtrancl (wts_to_monoidLTS A)"
  using assms monoid_star_intros_step' by (cases pwq) auto

lemma monoid_rtrancl_wts_to_monoidLTS_cases_rev':
  assumes "(p\<^sub>1, w\<^sub>1\<^sub>3d\<^sub>1\<^sub>3, p\<^sub>3) \<in> monoid_rtrancl (wts_to_monoidLTS ts)"
  shows "\<exists>d\<^sub>1\<^sub>3. w\<^sub>1\<^sub>3d\<^sub>1\<^sub>3 = ([],d\<^sub>1\<^sub>3) \<or>
           (\<exists>p\<^sub>2 d\<^sub>2\<^sub>3 \<gamma>\<^sub>1\<^sub>2 w\<^sub>2\<^sub>3 d\<^sub>1\<^sub>2.
               w\<^sub>1\<^sub>3d\<^sub>1\<^sub>3 = (\<gamma>\<^sub>1\<^sub>2#w\<^sub>2\<^sub>3,d\<^sub>1\<^sub>3) \<and>
               (p\<^sub>1, ([\<gamma>\<^sub>1\<^sub>2], d\<^sub>1\<^sub>2), p\<^sub>2) \<in> wts_to_monoidLTS ts \<and>
               (p\<^sub>2, (w\<^sub>2\<^sub>3, d\<^sub>2\<^sub>3), p\<^sub>3) \<in> monoid_rtrancl (wts_to_monoidLTS ts) \<and>
               d\<^sub>1\<^sub>3 = d\<^sub>1\<^sub>2 * d\<^sub>2\<^sub>3)"
  using assms
proof (induction rule: monoid_rtrancl.induct)
  case (monoid_rtrancl_refl)
  then show ?case
    by (simp add: one_list_def one_prod_def)
next
  case (monoid_rtrancl_into_rtrancl p\<^sub>1 w\<^sub>1\<^sub>3d\<^sub>1\<^sub>3 p\<^sub>3 w\<^sub>3\<^sub>4d\<^sub>3\<^sub>4 p\<^sub>4)
  show ?case
  proof (cases "(fst w\<^sub>1\<^sub>3d\<^sub>1\<^sub>3)")
    case (Cons \<gamma>\<^sub>1\<^sub>2 w\<^sub>2\<^sub>3)
    define w\<^sub>1\<^sub>3 where "w\<^sub>1\<^sub>3 = (fst w\<^sub>1\<^sub>3d\<^sub>1\<^sub>3)"
    define d\<^sub>1\<^sub>3 where "d\<^sub>1\<^sub>3 = (snd w\<^sub>1\<^sub>3d\<^sub>1\<^sub>3)"
    define w\<^sub>3\<^sub>4 where "w\<^sub>3\<^sub>4 = fst w\<^sub>3\<^sub>4d\<^sub>3\<^sub>4"
    define d\<^sub>3\<^sub>4 where "d\<^sub>3\<^sub>4 = snd w\<^sub>3\<^sub>4d\<^sub>3\<^sub>4"
    define w\<^sub>2\<^sub>4 where "w\<^sub>2\<^sub>4 = w\<^sub>2\<^sub>3 @ w\<^sub>3\<^sub>4"
    have w\<^sub>3\<^sub>4d\<^sub>3\<^sub>4_split: "w\<^sub>3\<^sub>4d\<^sub>3\<^sub>4 = (w\<^sub>3\<^sub>4,d\<^sub>3\<^sub>4)"
      by (simp add: d\<^sub>3\<^sub>4_def w\<^sub>3\<^sub>4_def)

    have w24_tl: "w\<^sub>2\<^sub>4 = tl (fst (w\<^sub>1\<^sub>3d\<^sub>1\<^sub>3 * w\<^sub>3\<^sub>4d\<^sub>3\<^sub>4))"
      by (simp add: local.Cons w\<^sub>2\<^sub>4_def w\<^sub>3\<^sub>4_def)

    have "w\<^sub>1\<^sub>3d\<^sub>1\<^sub>3 = (\<gamma>\<^sub>1\<^sub>2 # w\<^sub>2\<^sub>3, d\<^sub>1\<^sub>3)"
      using Cons by (metis d\<^sub>1\<^sub>3_def surjective_pairing) 

    then have "(\<exists>p\<^sub>2 d\<^sub>2\<^sub>3 d\<^sub>1\<^sub>2.
                   w\<^sub>1\<^sub>3d\<^sub>1\<^sub>3 = (\<gamma>\<^sub>1\<^sub>2 # w\<^sub>2\<^sub>3, d\<^sub>1\<^sub>3) \<and>
                   (p\<^sub>1, ([\<gamma>\<^sub>1\<^sub>2], d\<^sub>1\<^sub>2), p\<^sub>2) \<in> wts_to_monoidLTS ts \<and> 
                   (p\<^sub>2, (w\<^sub>2\<^sub>3, d\<^sub>2\<^sub>3), p\<^sub>3) \<in> monoid_rtrancl (wts_to_monoidLTS ts) \<and> 
                   d\<^sub>1\<^sub>3 = d\<^sub>1\<^sub>2 * d\<^sub>2\<^sub>3)"
      using monoid_rtrancl_into_rtrancl.IH by auto
    then obtain p\<^sub>2 d\<^sub>2\<^sub>3 d\<^sub>1\<^sub>2 where p\<^sub>2_d\<^sub>2\<^sub>3_d\<^sub>1\<^sub>2_p:
      "w\<^sub>1\<^sub>3d\<^sub>1\<^sub>3 = (\<gamma>\<^sub>1\<^sub>2 # w\<^sub>2\<^sub>3, d\<^sub>1\<^sub>3)"
      "(p\<^sub>1, ([\<gamma>\<^sub>1\<^sub>2], d\<^sub>1\<^sub>2), p\<^sub>2) \<in> wts_to_monoidLTS ts"
      "(p\<^sub>2, (w\<^sub>2\<^sub>3, d\<^sub>2\<^sub>3), p\<^sub>3) \<in> monoid_rtrancl (wts_to_monoidLTS ts)"
      "d\<^sub>1\<^sub>3 = d\<^sub>1\<^sub>2 * d\<^sub>2\<^sub>3"
      using d\<^sub>1\<^sub>3_def Cons by auto

    define d\<^sub>2\<^sub>4 where "d\<^sub>2\<^sub>4 = d\<^sub>2\<^sub>3 * d\<^sub>3\<^sub>4"

    have "(p\<^sub>2, (w\<^sub>2\<^sub>4, d\<^sub>2\<^sub>4), p\<^sub>4) \<in> monoid_rtrancl (wts_to_monoidLTS ts)"
      using local.Cons monoid_rtrancl_into_rtrancl.hyps(2)  w\<^sub>3\<^sub>4d\<^sub>3\<^sub>4_split d\<^sub>2\<^sub>4_def p\<^sub>2_d\<^sub>2\<^sub>3_d\<^sub>1\<^sub>2_p(3)
        monoid_rtrancl.monoid_rtrancl_into_rtrancl[of p\<^sub>2 "(w\<^sub>2\<^sub>3, d\<^sub>2\<^sub>3)" p\<^sub>3 "wts_to_monoidLTS ts" "(w\<^sub>3\<^sub>4, d\<^sub>3\<^sub>4)" p\<^sub>4]
      unfolding w\<^sub>1\<^sub>3_def[symmetric] w\<^sub>2\<^sub>4_def by simp
    moreover
    define d\<^sub>1\<^sub>4 where "d\<^sub>1\<^sub>4 = d\<^sub>1\<^sub>2 * d\<^sub>2\<^sub>4"
    moreover
    have "(p\<^sub>1, ([\<gamma>\<^sub>1\<^sub>2], d\<^sub>1\<^sub>2), p\<^sub>2) \<in> wts_to_monoidLTS ts"
      using p\<^sub>2_d\<^sub>2\<^sub>3_d\<^sub>1\<^sub>2_p by fastforce
    moreover
    have "w\<^sub>1\<^sub>3d\<^sub>1\<^sub>3 * w\<^sub>3\<^sub>4d\<^sub>3\<^sub>4 = (\<gamma>\<^sub>1\<^sub>2 # w\<^sub>2\<^sub>4, d\<^sub>1\<^sub>4)"
      by (metis append_Cons d\<^sub>1\<^sub>3_def d\<^sub>1\<^sub>4_def d\<^sub>2\<^sub>4_def d\<^sub>3\<^sub>4_def local.Cons mult.assoc mult_prod_def
          p\<^sub>2_d\<^sub>2\<^sub>3_d\<^sub>1\<^sub>2_p(4) times_list_def w\<^sub>2\<^sub>4_def w\<^sub>3\<^sub>4_def)
    ultimately show ?thesis
      by metis
  next
    case Nil
    then show ?thesis
      by (metis monoid_rtrancl.monoid_rtrancl_refl monoid_rtrancl_into_rtrancl.hyps(1)
          monoid_rtrancl_into_rtrancl.hyps(2) monoid_rtrancl_into_rtrancl.prems monoid_star_w0
          mstar_wts_empty_one mult.right_neutral mult_1 one_list_def one_prod_def prod.exhaust_sel
          wts_label_exist)
  qed
qed

lemma monoid_rtrancl_wts_to_monoidLTS_cases_rev:
  assumes "(p, (\<gamma>#w,d), p') \<in> monoid_rtrancl (wts_to_monoidLTS ts)"
  shows "\<exists>d' s d''.
           (p, ([\<gamma>], d'), s) \<in> wts_to_monoidLTS ts \<and>
           (s, (w, d''), p') \<in> monoid_rtrancl (wts_to_monoidLTS ts) \<and>
           d = d' * d''"
  using assms monoid_rtrancl_wts_to_monoidLTS_cases_rev' by fastforce

lemma wts_to_monoidLTS_induct[consumes 1, case_names base step]:
  assumes "(p, (w, d), p') \<in> monoid_rtrancl (wts_to_monoidLTS ts)"
  assumes "(\<And>p. P p [] 1 p)"
  assumes "(\<And>p w d p' w' d' p''. 
             (p, (w, d), p') \<in> monoid_rtrancl (wts_to_monoidLTS ts) \<Longrightarrow> 
             P p w d p' \<Longrightarrow> 
            (p', (w', d'), p'') \<in> wts_to_monoidLTS ts \<Longrightarrow> 
            P p (w @ w') (d * d') p'')"
  shows "P p w d p'"
  using monoid_rtrancl_pair_weight_induct[of p w d p' "wts_to_monoidLTS ts" P] assms
  by (simp add: one_list_def)

lemma wts_to_monoidLTS_pair_induct[consumes 1, case_names base step]:
  assumes "((p,q), (w, d), (p',q')) \<in> monoid_rtrancl (wts_to_monoidLTS ts)"
  assumes "(\<And>p q. P p q [] 1 p q)"
  assumes "(\<And>p q w d p' q' w' d' p'' q''. 
             ((p,q), (w, d), (p',q')) \<in> monoid_rtrancl (wts_to_monoidLTS ts) \<Longrightarrow> 
             P p q w d p' q' \<Longrightarrow> 
            ((p',q'), (w', d'), (p'',q'')) \<in> wts_to_monoidLTS ts \<Longrightarrow> 
            P p q (w @ w') (d * d') p'' q'')"
  shows "P p q w d p' q'"
  using wts_to_monoidLTS_induct[of
      "(p,q)" w d "(p',q')"
      ts
      "\<lambda>x y z a. P (fst x) (snd x) y z (fst a) (snd a)"]
    assms by auto

(* We are not using this induction. But it could be useful. *)
lemma wts_to_monoidLTS_induct_reverse:
  assumes "(p, (w,d), p') \<in> monoid_rtrancl (wts_to_monoidLTS ts)"
  assumes "(\<And>a. P a [] 1 a)"
  assumes "(\<And>p w d p' l d' p''.
             (p, (w,d), p') \<in> (wts_to_monoidLTS ts) \<Longrightarrow> 
             P p' l d' p'' \<Longrightarrow>
             (p', (l,d'), p'') \<in> monoid_rtrancl (wts_to_monoidLTS ts) \<Longrightarrow>
             P p (w @ l) (d*d') p'')"
  shows "P p w d p'"
  using assms monoid_rtrancl_induct_rev[of p "(w,d)" p' "(wts_to_monoidLTS ts)" "\<lambda>x y z. P x (fst y) (snd y) z"]
  by (simp add: one_list_def one_prod_def)

lemma monoid_star_nonempty:
  assumes "(p, w, p') \<in> monoid_rtrancl (wts_to_monoidLTS ts)"
  assumes "fst w \<noteq> []"
  shows "\<exists>pi d1 d2. (snd w) = d1 * d2 \<and> 
                    (pi, (tl (fst w), d2), p') \<in> monoid_rtrancl (wts_to_monoidLTS ts) \<and> 
                    (p, ([hd (fst w)], d1), pi) \<in> wts_to_monoidLTS ts"
  by (metis assms list.collapse monoid_rtrancl_wts_to_monoidLTS_cases_rev surjective_pairing)




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