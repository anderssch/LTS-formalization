theory WAutomaton
  imports "LTS" "Saturation" "FinFunWellFounded" "FinFunAddUpdate" "MonoidLTS" "Kleene_Algebra.Dioid_Models" "Set_More" "FinFunOf"
begin

section \<open>Basic datatypes and definitions\<close>

declare times_list_def[simp]

\<comment> \<open>For the semantics of a weighted automaton, labels are lifted to the list-monoid and paired with a weight\<close>
type_synonym ('label, 'weight) wautomaton_label = "('label list \<times> 'weight)" 

\<comment> \<open>Weighted automata transitions are modelled as a @{term finfun} from transitions to their weight, 
    where @{term "0::('weight::bounded_idempotent_semiring)"} is the default value, indicating no transition.\<close>
type_synonym ('state, 'label, 'weight) w_transitions = "('state, 'label) transition \<Rightarrow>f 'weight"

type_synonym ('state, 'label, 'weight) w_transition_set = "('state, ('label list \<times> 'weight)) transition set"


\<comment> \<open>Embed a weighted automaton into a monoidLTS. All non-zero transitions are added. The label is lifted to the list-monoid.\<close>
definition wts_to_monoidLTS :: "('state, 'label, 'weight::bounded_idempotent_semiring) w_transitions \<Rightarrow> ('state, ('label list \<times> 'weight)) transition set" where
  "wts_to_monoidLTS ts = {(p, ([\<gamma>],d), q) | p \<gamma> d q. ts $ (p,\<gamma>,q) = d}"

lemma wts_to_monoidLTS_code[code]: "wts_to_monoidLTS ts = (\<Union>(p,\<gamma>,q). {(p, ([\<gamma>], ts $ (p,\<gamma>,q)), q)})"
  unfolding wts_to_monoidLTS_def by blast

definition wts_to_weightLTS :: "('state, 'label, 'weight::bounded_idempotent_semiring) w_transitions \<Rightarrow> ('state, 'weight) transition set" where
  "wts_to_weightLTS ts = {(p, d, q) | p \<gamma> d q. ts $ (p,\<gamma>,q) = d}"

lemma wts_to_weightLTS_code[code]: "wts_to_weightLTS ts = (\<Union>(p,\<gamma>,q). {(p, (ts $ (p,\<gamma>,q)), q)})"
  unfolding wts_to_weightLTS_def by blast

lemma finite_wts: 
  fixes wts::"('state::enum, 'label::finite, 'weight::bounded_idempotent_semiring) w_transitions"
  shows "finite (wts_to_monoidLTS wts)"
proof -
  have "range (\<lambda>t. (fst t, ([fst (snd t)], wts $ t), snd (snd t))) = {t. \<exists>p \<gamma> q. t = (p, ([\<gamma>], wts $ (p, \<gamma>, q)), q)}"
    by force
  then have "finite {t. \<exists>p \<gamma> q. t = (p, ([\<gamma>], wts $ (p, \<gamma>, q)), q)}"
    using finite_imageI[of UNIV "(\<lambda>t. (fst t, ([fst (snd t)], wts $ t), snd (snd t)))"] by simp
  then show ?thesis unfolding wts_to_monoidLTS_def by presburger
qed

lemma wts_monoidLTS_to_weightLTS: "(p, (w, d), p') \<in> wts_to_monoidLTS ts \<Longrightarrow> (p, d, p') \<in> wts_to_weightLTS ts"
  unfolding wts_to_monoidLTS_def wts_to_weightLTS_def by blast

lemma wts_monoidLTS_star_to_weightLTS_star:
  "(p, (w,d), q) \<in> monoid_rtrancl (wts_to_monoidLTS ts) \<Longrightarrow> (p, d, q) \<in> monoid_rtrancl (wts_to_weightLTS ts)"
  apply (induct rule: monoid_rtrancl_pair_weight_induct, simp)
  subgoal for p w d p' w' d' p''
    using monoid_rtrancl_into_rtrancl[of p d p' "wts_to_weightLTS ts" d' p''] wts_monoidLTS_to_weightLTS[of p' w' d' p'' ts]
    by blast
  done
lemma wts_weightLTS_to_monoidLTS: "(p, d, p') \<in> wts_to_weightLTS ts \<Longrightarrow> \<exists>w. (p, (w,d), p') \<in> wts_to_monoidLTS ts"
  unfolding wts_to_monoidLTS_def wts_to_weightLTS_def by blast
lemma wts_weightLTS_star_to_monoidLTS_star:
  "(p, d, q) \<in> monoid_rtrancl (wts_to_weightLTS ts) \<Longrightarrow> \<exists>w. (p, (w,d), q) \<in> monoid_rtrancl (wts_to_monoidLTS ts)"
  apply (induct rule: monoid_rtrancl.induct)
   apply (rule exI[of _ 1])
   apply (metis one_prod_def monoid_rtrancl_refl)
  apply safe
  subgoal for p d p' d' p'' w
    using wts_weightLTS_to_monoidLTS[of p' d' p'' ts]
    apply simp
    apply safe
    subgoal for w'
      using monoid_rtrancl_into_rtrancl[of p "(w,d)" p' "wts_to_monoidLTS ts" "(w',d')" p'']
      by auto
    done
  done


lemma "finite (wts_to_weightLTS ts)" oops (* THIS should be true!! *)

lemma finite_wts: 
  assumes "finfun_default A = 0"
  shows "finite (wts_to_monoidLTS A)"
  unfolding wts_to_monoidLTS_def
  oops
(* proof -
  have "finite {x. A $ x \<noteq> 0}" 
    using finite_finfun_default[of A] assms by simp
  then show "finite {(p, ([\<gamma>],d), q) | p \<gamma> d q. A $ (p,\<gamma>,q) = d \<and> d \<noteq> 0}"
    using finite_image_set[of "\<lambda>x. A $ x \<noteq> 0" "\<lambda>(p,\<gamma>,q). (p, ([\<gamma>], A $ (p,\<gamma>,q)), q)"] by simp
qed
*)

lemma countable_wts: 
  fixes A :: "(('state::countable, 'label::finite, 'weight::bounded_idempotent_semiring) w_transitions)"
  shows "countable (wts_to_monoidLTS A)"
proof -
  have count1: "countable (UNIV :: ('state \<times> 'label \<times> 'state) set)"
    by blast
  have "{(p, ([\<gamma>], d), q)| p \<gamma> d q. A $ (p, \<gamma>, q) = d} = (\<lambda>(p, \<gamma>, q). (p, ([\<gamma>], A $ (p, \<gamma>, q)), q)) ` UNIV"
    unfolding image_def by auto
  then have "countable {(p, ([\<gamma>], d), q)| p \<gamma> d q. A $ (p, \<gamma>, q) = d}"
    using count1 by auto
  then show ?thesis
    unfolding wts_to_monoidLTS_def by auto
qed

lemma monoid_rtrancl_wts_to_monoidLTS_refl:
  "(p, ([], 1), p) \<in> monoid_rtrancl (wts_to_monoidLTS A)"
  by (metis monoid_rtrancl_refl one_list_def one_prod_def)

lemma wts_to_monoidLTS_mono': "ts \<le> ts' \<Longrightarrow> (p, (w, d), q) \<in> wts_to_monoidLTS ts \<Longrightarrow> \<exists>d'. (p, (w, d'), q) \<in> wts_to_monoidLTS ts' \<and> d \<le> d'"
  unfolding less_eq_finfun_def wts_to_monoidLTS_def by blast

lemma wts_to_monoidLTS_mono: "ts' \<le> ts \<Longrightarrow> (p, (w, d), q) \<in> wts_to_monoidLTS ts \<Longrightarrow> \<exists>d'. (p, (w, d'), q) \<in> wts_to_monoidLTS ts' \<and> d' \<le> d"
  unfolding less_eq_finfun_def wts_to_monoidLTS_def by blast

lemma wts_monoid_rtrancl_mono: 
  assumes "ts' \<le> ts"
  assumes "(p, (w, d), q) \<in> monoid_rtrancl (wts_to_monoidLTS ts)"
  shows "\<exists>d'. (p, (w, d'), q) \<in> monoid_rtrancl (wts_to_monoidLTS ts') \<and> d' \<le> d"
proof (induction rule: monoid_rtrancl_pair_weight_induct[OF assms(2)])
  case (1 p)
  then show ?case 
    by (rule exI[of _ "1"]) 
       (simp add: monoid_rtrancl_refl[of _ "wts_to_monoidLTS ts'", unfolded one_prod_def])
next
  case (2 p w d p' w' d' p'')
  obtain da da' 
    where da:"(p, (w, da), p') \<in> monoid_rtrancl (wts_to_monoidLTS ts')" "da \<le> d" 
     and da':"(p', (w', da'), p'') \<in> wts_to_monoidLTS ts'" "da' \<le> d'" 
    using 2(3) wts_to_monoidLTS_mono[OF assms(1) 2(2)] by blast
  show ?case
    apply (rule exI[of _ "da * da'"])
    using da(2) da'(2) monoid_rtrancl_into_rtrancl[OF da(1) da'(1)]
    by (simp add: idempotent_semiring_ord_class.mult_isol_var)
qed


section \<open>Locale: W_automaton\<close>

locale W_automaton = monoidLTS "wts_to_monoidLTS transition_relation"
  for transition_relation :: "('state::finite, 'label, 'weight::bounded_idempotent_semiring) w_transitions"
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

section \<open>Reachability and Paths\<close>

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
  then obtain \<gamma> where \<gamma>:"[\<gamma>] = fst w" unfolding wts_to_monoidLTS_def by force
  then have lw': "\<gamma> # fst w' = fst (w * w')" unfolding mult_prod_def times_list_def by fastforce
  define d where "d = snd w"
  define d' where "d' = snd w'"
  have dd': "d * d' = snd (w * w')" using d_def d'_def unfolding mult_prod_def by fastforce
  have w: "w = ([\<gamma>], d)" using \<gamma> d_def by simp
  show ?case
  proof (cases "d * d' = 0")
    case True
    then show ?thesis unfolding mult_prod_def dd' by simp
  next
    case False
    then have d0:"d \<noteq> 0" and "d' \<noteq> 0" by auto
    then have "(q, d') \<in> monoidLTS_reach_not0 (wts_to_monoidLTS ts) p' (fst w')"
      using monoid_rtrancl_into_rtrancl(2) d'_def by blast
    then have "(q, d * d') \<in> monoidLTS_reach_not0 (wts_to_monoidLTS ts) p (\<gamma> # fst w')"
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
lemma wts_label_exist: "(p, w, q) \<in> wts_to_monoidLTS ts \<Longrightarrow> \<exists>\<gamma>. fst w = [\<gamma>]"
  unfolding wts_to_monoidLTS_def by fastforce

lemma wts_label_not_empty: "(p, w, q) \<in> wts_to_monoidLTS ts \<Longrightarrow> fst w \<noteq> []"
  unfolding wts_to_monoidLTS_def by force

lemma wts_label_d: "(p, ([\<gamma>],d), q) \<in> wts_to_monoidLTS ts \<Longrightarrow> ts $ (p,\<gamma>,q) = d"
  unfolding wts_to_monoidLTS_def by blast

lemma wts_label_d': "(p, w, q) \<in> wts_to_monoidLTS ts \<Longrightarrow> ts $ (p, hd(fst w), q) = snd w"
  unfolding wts_to_monoidLTS_def by auto

lemma mstar_wts_one: "(p, w, q) \<in> monoid_rtrancl (wts_to_monoidLTS ts) \<Longrightarrow> fst w = 1 \<Longrightarrow> snd w = 1"
proof (induct rule: monoid_rtrancl.induct)
  case (monoid_rtrancl_refl a)
  then show ?case by (simp add: one_prod_def)
next
  case (monoid_rtrancl_into_rtrancl p w p' \<gamma> q)
  from \<open>(p', \<gamma>, q) \<in> wts_to_monoidLTS ts\<close> have "fst \<gamma> \<noteq> []" using wts_label_not_empty by fast
  then have "fst (w * \<gamma>) \<noteq> []" by simp
  then show ?case
    using monoid_rtrancl_into_rtrancl.prems by (simp add: monoid_rtrancl_into_rtrancl.prems one_list_def)
qed
lemma mstar_wts_empty_one: "(p, ([],d), q) \<in> monoid_rtrancl (wts_to_monoidLTS ts) \<Longrightarrow> d = 1"
  using mstar_wts_one by (simp add: one_list_def, fastforce)

lemma wts_to_monoidLTS_exists: (* TODO: rename *)
  assumes "w23 = [\<gamma>]"
  shows "\<exists>dp23. (p2, (w23, dp23), p3) \<in> wts_to_monoidLTS ts1"
  using assms wts_to_monoidLTS_def by fastforce

lemma wts_to_monoidLTS_exists_iff:
  "(\<exists>dp23. (p2, (w23, dp23), p3) \<in> wts_to_monoidLTS ts1) \<longleftrightarrow> (\<exists>\<gamma>. w23 = [\<gamma>])"
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
  case (monoid_rtrancl_into_rtrancl p w p' \<gamma> q)
  from \<open>(p', \<gamma>, q) \<in> wts_to_monoidLTS ts\<close> have "fst \<gamma> \<noteq> []" using wts_label_not_empty by fast
  then have "fst (w * \<gamma>) \<noteq> []" by simp
  then show ?case using monoid_rtrancl_into_rtrancl.prems by simp
qed

lemma monoid_star_w1:
  assumes "(p, w, q) \<in> monoid_rtrancl (wts_to_monoidLTS ts)"
  assumes "fst w = [\<gamma>]"
  shows "ts $ (p,\<gamma>,q) = snd w"
  using assms
proof (induct rule: monoid_rtrancl.induct)
  case (monoid_rtrancl_refl a)
  then show ?case by (simp add: one_prod_def one_list_def)
next
  case (monoid_rtrancl_into_rtrancl p w p' w' q)
  then have "fst w = []" 
    by (simp add: append_eq_Cons_conv wts_label_not_empty[of p' w' q ts])
  then show ?case 
    using monoid_rtrancl_into_rtrancl.hyps monoid_rtrancl_into_rtrancl.prems
          monoid_star_w0[of p w p' ts] mstar_wts_one[of p w p' ts] wts_label_d'[of p' w' q ts]
    by (simp add: one_list_def)
qed

lemma monoid_star_w2:
  assumes "(p, w, q) \<in> monoid_rtrancl (wts_to_monoidLTS ts)"
  assumes "fst w = [\<gamma>,\<gamma>']"
  shows "\<exists>q'. ts $ (p,\<gamma>,q') * ts $ (q',\<gamma>',q) = snd w"
  using assms
proof (induct rule: monoid_rtrancl.induct)
  case (monoid_rtrancl_refl a)
  then show ?case by (simp add: one_prod_def one_list_def)
next
  case (monoid_rtrancl_into_rtrancl p w p' w' q)
  then have "fst w = [\<gamma>] \<and> fst w' = [\<gamma>']" 
    using wts_label_exist[of p' w' q ts] by auto
  then show ?case 
    using monoid_rtrancl_into_rtrancl.hyps monoid_rtrancl_into_rtrancl.prems 
          monoid_star_w1[of p w p' ts \<gamma>] monoid_star_w1[of p' w' q ts \<gamma>'] wts_label_d'[of p' w' q ts]    
    by simp metis
qed

lemma mstar_wts_cons:
  assumes "(p, (\<gamma>#w, d), q) \<in> monoid_rtrancl (wts_to_monoidLTS ts)"
  shows   "\<exists>d' p' d''. d = d' * d'' \<and> (p, ([\<gamma>], d'), p') \<in> wts_to_monoidLTS ts \<and> (p', (w, d''), q) \<in> monoid_rtrancl (wts_to_monoidLTS ts)"
  using assms monoid_rtrancl_simps_rev[of p "(\<gamma>#w, d)" q "wts_to_monoidLTS ts", unfolded mult_prod_def times_list_def one_prod_def one_list_def, simplified]
  apply (simp, safe, simp)
  subgoal for \<gamma>' d' p' w' d''
    apply (rule exI[of _ d'], rule exI[of _ p'], rule exI[of _ d''])
    unfolding wts_to_monoidLTS_def by force
  done

lemma monoid_rtrancl_intros_Cons:
  assumes "(p, ([\<gamma>], d), q1) \<in> wts_to_monoidLTS ts"
  assumes "(q1, (w, u), q) \<in> monoid_rtrancl (wts_to_monoidLTS ts)"
  shows "(p, (\<gamma> # w, d*u), q) \<in> monoid_rtrancl (wts_to_monoidLTS ts)"
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
  case (Cons \<gamma> w)
  have f1:"finite {(p, ([\<gamma>], d), q) |p d q. (p, ([\<gamma>], d), q) \<in> wts_to_monoidLTS ts}"
    using finite_subset[OF _ assms, of "{(p, ([\<gamma>], d), q)| p d q. (p, ([\<gamma>], d), q) \<in> wts_to_monoidLTS ts}"]
    by blast
  have "finite {d. \<exists>p q. (p, ([\<gamma>], d), q) \<in> wts_to_monoidLTS ts}"
    unfolding setcompr_eq_image3[of "\<lambda>p d q. d" "\<lambda>p d q. (p, ([\<gamma>], d), q) \<in> wts_to_monoidLTS ts", simplified]
    apply (rule finite_imageI)
    using f1[unfolded setcompr_eq_image3[of "\<lambda>p d q. (p, ([\<gamma>], d), q)" "\<lambda>p d q. (p, ([\<gamma>], d), q) \<in> wts_to_monoidLTS ts", simplified]]
    apply (rule finite_imageD)
    unfolding inj_on_def by fastforce
  then have "finite {d * d' |d d'. (\<exists>p q. (p, ([\<gamma>], d), q) \<in> wts_to_monoidLTS ts) \<and> (\<exists>p q. (p, (w, d'), q) \<in> monoid_rtrancl (wts_to_monoidLTS ts))}"
    using finite_image_set2 Cons by fast
  moreover have "{d. \<exists>p q. (p, (\<gamma> # w, d), q) \<in> monoid_rtrancl (wts_to_monoidLTS ts)} 
              \<subseteq> {d * d' |d d'. (\<exists>p q. (p, ([\<gamma>], d), q) \<in> wts_to_monoidLTS ts) \<and> (\<exists>p q. (p, (w, d'), q) \<in> monoid_rtrancl (wts_to_monoidLTS ts))}"
    using mstar_wts_cons by fast
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
  assumes "(p, (\<gamma>#w,d), p'') \<in> monoid_rtrancl (wts_to_monoidLTS ts)"
  shows "\<exists>d' p' d''.
           (p, ([\<gamma>], d'), p') \<in> wts_to_monoidLTS ts \<and>
           (p', (w, d''), p'') \<in> monoid_rtrancl (wts_to_monoidLTS ts) \<and>
           d = d' * d''"
  using assms monoid_rtrancl_wts_to_monoidLTS_cases_rev' by fastforce

(* Proof adapted from monoid_rtrancl_list_embed_ts_append_split *)
lemma monoid_rtrancl_wts_to_monoidLTS_append_split:
  assumes "(p\<^sub>1, (w\<^sub>1\<^sub>3@w\<^sub>3\<^sub>4,d\<^sub>1\<^sub>4), p\<^sub>4) \<in> monoid_rtrancl (wts_to_monoidLTS A)"
  shows "\<exists>d\<^sub>1\<^sub>3 p\<^sub>3 d\<^sub>3\<^sub>4.
           (p\<^sub>1, (w\<^sub>1\<^sub>3,d\<^sub>1\<^sub>3), p\<^sub>3) \<in> monoid_rtrancl (wts_to_monoidLTS A) \<and>
           (p\<^sub>3, (w\<^sub>3\<^sub>4,d\<^sub>3\<^sub>4), p\<^sub>4) \<in> monoid_rtrancl (wts_to_monoidLTS A) \<and>
           d\<^sub>1\<^sub>4 = d\<^sub>1\<^sub>3 * d\<^sub>3\<^sub>4"
using assms proof(induction w\<^sub>1\<^sub>3 arbitrary: p\<^sub>1 d\<^sub>1\<^sub>4)
  case Nil
  then show ?case
    by (metis eq_Nil_appendI monoid_rtrancl.monoid_rtrancl_refl mult_1 one_list_def one_prod_def) 
next
  case (Cons \<gamma>\<^sub>1\<^sub>2 w\<^sub>2\<^sub>3)
  then have "\<exists>d\<^sub>1\<^sub>2 p\<^sub>2 d\<^sub>2\<^sub>4. (p\<^sub>1, ([\<gamma>\<^sub>1\<^sub>2],d\<^sub>1\<^sub>2), p\<^sub>2) \<in> (wts_to_monoidLTS A) \<and>
                         (p\<^sub>2, (w\<^sub>2\<^sub>3 @ w\<^sub>3\<^sub>4,d\<^sub>2\<^sub>4), p\<^sub>4) \<in> monoid_rtrancl (wts_to_monoidLTS A) \<and>
                         d\<^sub>1\<^sub>4 = d\<^sub>1\<^sub>2 * d\<^sub>2\<^sub>4"
    using monoid_rtrancl_wts_to_monoidLTS_cases_rev by fastforce

  then obtain p\<^sub>2 d\<^sub>1\<^sub>2 d\<^sub>2\<^sub>4 where q_du0_du1_p:
    "(p\<^sub>1, ([\<gamma>\<^sub>1\<^sub>2],d\<^sub>1\<^sub>2), p\<^sub>2) \<in> (wts_to_monoidLTS A)" 
    "(p\<^sub>2, (w\<^sub>2\<^sub>3 @ w\<^sub>3\<^sub>4,d\<^sub>2\<^sub>4), p\<^sub>4) \<in> monoid_rtrancl (wts_to_monoidLTS A)" 
    "d\<^sub>1\<^sub>4 = d\<^sub>1\<^sub>2 * d\<^sub>2\<^sub>4"
    by auto

  have "\<exists>d\<^sub>2\<^sub>3 p\<^sub>3 d\<^sub>3\<^sub>4. (p\<^sub>2, (w\<^sub>2\<^sub>3, d\<^sub>2\<^sub>3), p\<^sub>3) \<in> monoid_rtrancl (wts_to_monoidLTS A) \<and> 
                     (p\<^sub>3, (w\<^sub>3\<^sub>4, d\<^sub>3\<^sub>4), p\<^sub>4) \<in> monoid_rtrancl (wts_to_monoidLTS A) \<and> 
                     d\<^sub>2\<^sub>4 = d\<^sub>2\<^sub>3 * d\<^sub>3\<^sub>4"
     using Cons.IH[OF q_du0_du1_p(2)] .
  then obtain d\<^sub>2\<^sub>3 p\<^sub>3 d\<^sub>3\<^sub>4 where
    "(p\<^sub>2, (w\<^sub>2\<^sub>3,d\<^sub>2\<^sub>3), p\<^sub>3) \<in> monoid_rtrancl (wts_to_monoidLTS A)"
    "(p\<^sub>3, (w\<^sub>3\<^sub>4,d\<^sub>3\<^sub>4), p\<^sub>4) \<in> monoid_rtrancl (wts_to_monoidLTS A)" 
    "d\<^sub>2\<^sub>4 = d\<^sub>2\<^sub>3 * d\<^sub>3\<^sub>4"
    by auto
  from this(1) have "(p\<^sub>1, (\<gamma>\<^sub>1\<^sub>2 # w\<^sub>2\<^sub>3, d\<^sub>1\<^sub>2 * d\<^sub>2\<^sub>3), p\<^sub>3) \<in> monoid_rtrancl (wts_to_monoidLTS A)"
    using q_du0_du1_p(1) monoid_rtrancl_into_rtrancl_rev[of p\<^sub>1 "([\<gamma>\<^sub>1\<^sub>2], d\<^sub>1\<^sub>2)" p\<^sub>2 "wts_to_monoidLTS A" "(w\<^sub>2\<^sub>3, d\<^sub>2\<^sub>3)" p\<^sub>3]
    by simp
  then show ?case
    using  \<open>(p\<^sub>3, (w\<^sub>3\<^sub>4, d\<^sub>3\<^sub>4), p\<^sub>4) \<in> monoid_rtrancl (wts_to_monoidLTS A)\<close> \<open>d\<^sub>2\<^sub>4 = d\<^sub>2\<^sub>3 * d\<^sub>3\<^sub>4\<close> q_du0_du1_p(3) 
    by (metis (no_types, lifting) mult.assoc)   
qed

lemma merge_edge_and_monoid_rtrancl_wts_to_monoidLTS:
  assumes "A $ (p\<^sub>1, \<gamma>\<^sub>1\<^sub>2, p\<^sub>2) \<le> D\<^sub>1\<^sub>2"
  assumes "(p\<^sub>2, (w\<^sub>2\<^sub>3, d\<^sub>2\<^sub>3), p\<^sub>3) \<in> monoid_rtrancl (wts_to_monoidLTS A)"
  shows "\<exists>D\<^sub>1\<^sub>3. (p\<^sub>1, (\<gamma>\<^sub>1\<^sub>2 # w\<^sub>2\<^sub>3, D\<^sub>1\<^sub>3), p\<^sub>3) \<in> monoid_rtrancl (wts_to_monoidLTS A) \<and> D\<^sub>1\<^sub>3 \<le> D\<^sub>1\<^sub>2 * d\<^sub>2\<^sub>3"
proof -
  define d\<^sub>1\<^sub>2 where "d\<^sub>1\<^sub>2 = A $ (p\<^sub>1, \<gamma>\<^sub>1\<^sub>2, p\<^sub>2)"

  have p\<^sub>1_to_p\<^sub>2: "(p\<^sub>1, ([\<gamma>\<^sub>1\<^sub>2], d\<^sub>1\<^sub>2), p\<^sub>2) \<in> (wts_to_monoidLTS A)"
    using assms(1) d\<^sub>1\<^sub>2_def wts_to_monoidLTS_def by fastforce

  have "(p\<^sub>1, ([\<gamma>\<^sub>1\<^sub>2], d\<^sub>1\<^sub>2) * (w\<^sub>2\<^sub>3, d\<^sub>2\<^sub>3), p\<^sub>3) \<in> monoid_rtrancl (wts_to_monoidLTS A)"
    using monoid_rtrancl_into_rtrancl_rev[OF _ assms(2), of p\<^sub>1 "([\<gamma>\<^sub>1\<^sub>2],_)", OF p\<^sub>1_to_p\<^sub>2] .
  then have "(p\<^sub>1, (\<gamma>\<^sub>1\<^sub>2#w\<^sub>2\<^sub>3, d\<^sub>1\<^sub>2 * d\<^sub>2\<^sub>3), p\<^sub>3) \<in> monoid_rtrancl (wts_to_monoidLTS A)"
    by simp
  then show ?thesis
    using assms(1) d\<^sub>1\<^sub>2_def idempotent_semiring_ord_class.mult_isol_var by blast
qed


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
      "\<lambda>pq y z p'q'. P (fst pq) (snd pq) y z (fst p'q') (snd p'q')"]
    assms by auto

(* We are not using this induction. But it could be useful. *)
lemma wts_to_monoidLTS_induct_reverse:
  assumes "(p, (w,d), p') \<in> monoid_rtrancl (wts_to_monoidLTS ts)"
  assumes "(\<And>p. P p [] 1 p)"
  assumes "(\<And>p w d p' w' d' p''.
             (p, (w,d), p') \<in> (wts_to_monoidLTS ts) \<Longrightarrow> 
             P p' w' d' p'' \<Longrightarrow>
             (p', (w',d'), p'') \<in> monoid_rtrancl (wts_to_monoidLTS ts) \<Longrightarrow>
             P p (w @ w') (d*d') p'')"
  shows "P p w d p'"
  using assms monoid_rtrancl_induct_rev[of p "(w,d)" p' "(wts_to_monoidLTS ts)" "\<lambda>p wd p'. P p (fst wd) (snd wd) p'"]
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

lemma ts_to_wts_1_if_member:
  fixes ts :: "('s, 'l) transition set"
  assumes "finite ts"
  assumes "(p', \<gamma>, p'') \<in> ts"
  shows "ts_to_wts ts $ (p', \<gamma>, p'') = 1"
  by (metis (mono_tags, lifting) assms ts_to_wts_def update_wts_apply_is_1_if_member)

lemma ts_to_wts_1_or_0:
  fixes ts :: "('s, 'l) transition set"
  assumes "finite ts"
  shows "ts_to_wts ts $ (p1, w, p2) = 1 \<or> ts_to_wts ts $ (p1, w, p2) = 0"
 using assms
proof (induction rule: finite_induct)
  case empty
  then show ?case
    by auto
next
  case (insert x F)
  then show ?case
  proof (cases "x =  (p1, w, p2)")
    case True
    then show ?thesis 
      using insert
      by (simp add: ts_to_wts_1_if_member)
  next
    case False
    then show ?thesis 
      using insert update_wts_apply_is_0_if_not_member update_wts_apply_is_1_if_member
      by (metis (mono_tags) finite.insertI ts_to_wts_def)
  qed    
qed

lemma monoid_rtrancl_one_if_trans_star:
  fixes ts :: "('s, 'label) transition set"
  assumes "(p, \<gamma>, q) \<in> LTS.trans_star ts"
  assumes "finite ts"
  shows "(p, (\<gamma>, 1), q) \<in> monoid_rtrancl (wts_to_monoidLTS (ts_to_wts ts))"
  apply (induction rule: LTS.trans_star.induct[OF assms(1)])
  subgoal
    apply (simp add: monoid_rtrancl_wts_to_monoidLTS_refl)
    done
  subgoal 
    apply (metis ts_to_wts_1_if_member assms(2) monoid_rtrancl_intros_Cons mult.right_neutral wts_label_d wts_to_monoidLTS_exists)
    done
  done

lemma ts_to_wts_not_member_is_0:
  fixes ts :: "('state, 'label) transition set"
  assumes "finite ts"
  assumes "(p, \<gamma>, q) \<notin> ts"
  shows "ts_to_wts ts $ (p, \<gamma>, q) = 0"
proof -
  have f: "finite {(t, 1) |t. t \<in> ts}" 
    using assms(1) by (fact finite_f_on_set)
  show ?thesis
    unfolding ts_to_wts_def update_wts_sum[OF f, of "K$ 0" "(p, \<gamma>, q)"] using assms(2) by simp
qed

section \<open>Intersection of WAutomata\<close>

fun fst_trans :: "(('state \<times> 'state), 'label::finite) transition \<Rightarrow> ('state, 'label) transition" where
  "fst_trans ((p1,q1),\<gamma>,(p2,q2)) = (p1,\<gamma>,p2)"

fun snd_trans :: "(('state \<times> 'state), 'label::finite) transition \<Rightarrow> ('state, 'label) transition" where
  "snd_trans ((p1,q1),\<gamma>,(p2,q2)) = (q1,\<gamma>,q2)"

definition fst_weight :: "('state, 'label::finite, 'weight) w_transitions \<Rightarrow> (('state \<times> 'state), 'label, 'weight) w_transitions"
  where "fst_weight = (\<lambda>ts. ts $\<circ> fst_trans)" 

lemma fst_weight_apply:
  fixes p1::"'state::finite"
  fixes q1::"'state::finite"
  shows "(fst_weight ts1) $ ((p1,q1),\<gamma>,(p2,q2)) = ts1 $ (p1,\<gamma>,p2)"
  unfolding fst_weight_def finfun_comp2_def Abs_finfun_inverse_finite_class by auto

definition snd_weight :: "('state, 'label::finite, 'weight) w_transitions \<Rightarrow> (('state \<times> 'state), 'label, 'weight) w_transitions"
  where "snd_weight = (\<lambda>ts. ts $\<circ> snd_trans)"

lemma snd_weight_apply:
  fixes p1::"'state::finite"
  fixes q1::"'state::finite"
  shows "(snd_weight ts2) $ ((p1,q1),\<gamma>,(p2,q2)) = ts2 $ (q1,\<gamma>,q2)"
  unfolding snd_weight_def finfun_comp2_def Abs_finfun_inverse_finite_class by auto

definition pair_weight :: "('state, 'label::finite, 'weight) w_transitions \<Rightarrow> ('state, 'label, 'weight) w_transitions \<Rightarrow> (('state \<times> 'state), 'label, ('weight \<times>'weight)) w_transitions" where
  "pair_weight = (\<lambda>ts1 ts2. finfun_Diag (fst_weight ts1) (snd_weight ts2))"
                                            
lemma finfun_apply_pair_weight_transition:
  fixes p1::"'state::finite" 
  fixes q1::"'state::finite"
  shows "pair_weight ts1 ts2 $ ((p1,q1),\<gamma>,(p2,q2)) = (ts1 $ (p1,\<gamma>,p2),ts2 $ (q1,\<gamma>,q2))"
  unfolding pair_weight_def finfun_Diag_apply by (auto simp add: fst_weight_apply snd_weight_apply)

lemma finfun_apply_pair_weight:
  fixes ts1::"('state::finite, 'label::finite, 'weight) w_transitions"
  fixes ts2::"('state::finite, 'label, 'weight) w_transitions"
  shows "(($) (pair_weight ts1 ts2)) = (\<lambda>t. (ts1 $ (fst_trans t), ts2 $ (snd_trans t)))"
proof (rule HOL.ext)
  fix t 
  show "pair_weight ts1 ts2 $ t = (ts1 $ (fst_trans t), ts2 $ (snd_trans t))"
    using finfun_apply_pair_weight_transition by (cases t) fastforce
qed

definition intersff :: "('state, 'label::finite, 'weight::bounded_idempotent_semiring) w_transitions \<Rightarrow> ('state, 'label, 'weight) w_transitions \<Rightarrow> (('state \<times> 'state), 'label, 'weight) w_transitions" where
  "intersff = (\<lambda>ts1 ts2. (case_prod (*)) \<circ>$ (pair_weight ts1 ts2))"

lemma finfun_apply_intersff_transition:
  fixes p1::"'state::finite"
  fixes q1::"'state::finite"
  shows "intersff ts1 ts2 $ ((p1,q1),\<gamma>,(p2,q2)) = (ts1 $ (p1,\<gamma>,p2)*ts2 $ (q1,\<gamma>,q2))"
  by (auto simp add: fst_weight_apply snd_weight_apply finfun_apply_pair_weight_transition intersff_def)

lemma finfun_apply_intersff:
  fixes ts1::"('state::finite, 'label::finite, 'weight::bounded_idempotent_semiring) w_transitions"
  fixes ts2::"('state::finite, 'label, 'weight) w_transitions"
  shows "(($) (intersff ts1 ts2)) = (\<lambda>t. (ts1 $ (fst_trans t) * ts2 $ (snd_trans t)))"
proof (rule HOL.ext)
  fix t
  show "intersff ts1 ts2 $ t = ts1 $ (fst_trans t) * ts2 $ (snd_trans t)"
    using finfun_apply_intersff_transition by (cases t) force
qed

lemma inftersff_complete_transition_finfun_apply:
  fixes p::"'state::finite"
  fixes p'::"'state::finite"
  assumes "A $ (p, y, q) = d"
  assumes "A' $ (p', y, q') = d'"
  shows "(intersff A A') $ ((p,p'), y, (q,q')) = d * d'"
  using assms finfun_apply_intersff_transition by auto

lemma inftersff_complete_transition:
  fixes p1::"'state::finite"
  fixes q1::"'state::finite"
  assumes "(p1, ([\<alpha>], dp), p') \<in> wts_to_monoidLTS ts1"
  assumes "(q1, ([\<alpha>], dq), q') \<in> wts_to_monoidLTS ts2"
  shows "((p1, q1), ([\<alpha>], dp * dq), (p', q')) \<in> wts_to_monoidLTS (intersff ts1 ts2)"
  using assms finfun_apply_intersff_transition[of ts1 ts2 p1 q1 \<alpha> p' q']
  unfolding wts_to_monoidLTS_def by auto

lemma intersff_sound_transition:
  fixes ts1::"('state::finite, 'label::finite, 'weight::bounded_idempotent_semiring) w_transitions"
  fixes ts2::"('state::finite, 'label, 'weight) w_transitions"
  assumes "((p2, q2), (w23, d23), p3, q3) \<in> wts_to_monoidLTS (intersff ts1 ts2)"
  obtains d23p d23q where
    "(p2, (w23, d23p), p3) \<in> wts_to_monoidLTS ts1"
    "(q2, (w23, d23q), q3) \<in> wts_to_monoidLTS ts2"
    "d23 = d23p * d23q"
proof -
  have "\<exists>d23p d23q. ts1 $ (p2, (hd w23), p3) = d23p \<and>
                    ts2 $ (q2, (hd w23), q3) = d23q \<and>
                    d23 = d23p * d23q"
    using assms finfun_apply_intersff_transition wts_label_d' by fastforce
  then show ?thesis
    by (metis wts_to_monoidLTS_exists_iff assms list.sel(1) that wts_label_d)
qed

definition binary_aut :: "('state, 'label, 'weight::bounded_idempotent_semiring) w_transitions \<Rightarrow> bool" where
  "binary_aut ts1 \<longleftrightarrow> (\<forall>p1 w p2. ts1 $ (p1, w, p2) = 1 \<or> ts1 $ (p1, w, p2) = 0)"

lemma ts_to_wts_bin:
  fixes ts :: "('s, 'l) transition set"
  assumes "finite ts"
  shows "binary_aut (ts_to_wts ts)"
  unfolding binary_aut_def using assms ts_to_wts_1_or_0 by metis

lemma binary_aut_monoid_rtrancl_wts_to_monoidLTS_cases_rev:
  assumes "binary_aut ts1"
  assumes "(p1, (\<alpha>#w1',1), p2) \<in> monoid_rtrancl (wts_to_monoidLTS ts1)"
  shows "\<exists>p'. (p1, ([\<alpha>],1), p') \<in> wts_to_monoidLTS ts1 \<and> (p', (w1',1), p2) \<in> monoid_rtrancl (wts_to_monoidLTS ts1)"
  using assms
proof (induction w1' arbitrary: \<alpha> p1)
  case Nil
  then show ?case
    by (metis monoid_rtrancl_wts_to_monoidLTS_cases_rev mstar_wts_empty_one mult.right_neutral)
next
  case (Cons \<alpha>' w1')
  obtain p1' d1 d2 where p1'_p:
    "(p1, ([\<alpha>], d1), p1') \<in> (wts_to_monoidLTS ts1)"
    "(p1', (\<alpha>'#w1', d2), p2) \<in> monoid_rtrancl (wts_to_monoidLTS ts1)"
    "1 = d1 * d2"
    using Cons(3) by (meson monoid_rtrancl_wts_to_monoidLTS_cases_rev)
  have d1: "d1 = 1"
    using Cons.prems(1) p1'_p(1,3) unfolding binary_aut_def by (metis mult_zero_left wts_label_d)
  then have "d2 = 1"
    using p1'_p(3) by force
  then have "(p1', (\<alpha>' # w1', 1), p2) \<in> monoid_rtrancl (wts_to_monoidLTS ts1)"
    using p1'_p(2) by force
  then show ?case
    using p1'_p(1) d1 by (meson wts_label_d) 
qed

lemma binary_aut_transition_binary:
  assumes "(p1, (w,d), p2) \<in> wts_to_monoidLTS ts1"
  assumes "binary_aut ts1"
  shows "d = 1 \<or> d = 0"
  by (metis assms(1) assms(2) binary_aut_def snd_conv wts_label_d')

lemma binary_aut_path_binary:
  assumes "(p1, (w,d), p2) \<in> monoid_rtrancl (wts_to_monoidLTS ts1)"
  assumes "binary_aut ts1"
  shows "d = 1 \<or> d = 0"
  using assms
proof (induction rule: wts_to_monoidLTS_induct)
  case (base p)
  then show ?case
    by auto 
next
  case (step p w d p' w' d' p'')
  then show ?case
    using binary_aut_transition_binary by fastforce
qed

lemma intersff_complete_exi:
  fixes ts1::"('state::finite, 'label::finite, 'weight::bounded_idempotent_semiring) w_transitions"
  fixes ts2::"('state::finite, 'label, 'weight) w_transitions"
  assumes "(p1, (w,dp), p2) \<in> monoid_rtrancl (wts_to_monoidLTS ts1)"
  assumes "(q1, (w,dq), q2) \<in> monoid_rtrancl (wts_to_monoidLTS ts2)"
  shows "\<exists>d. ((p1,q1), (w,d), (p2,q2)) \<in> monoid_rtrancl (wts_to_monoidLTS (intersff ts1 ts2))"
  using assms 
proof (induction w arbitrary: p1 q1 dp dq)
  case Nil
  then show ?case
    by (metis fst_conv monoid_rtrancl.monoid_rtrancl_refl monoid_star_w0 one_list_def one_prod_def)
next
  case (Cons \<gamma> w)
  obtain p' q' dp1 dp2 dq1 dq2 where pq'_p:
    "(p1, ([\<gamma>], dp1), p') \<in> (wts_to_monoidLTS ts1)" "(p', (w, dp2), p2) \<in> monoid_rtrancl (wts_to_monoidLTS ts1)"
    "(q1, ([\<gamma>], dq1), q') \<in> (wts_to_monoidLTS ts2)" "(q', (w, dq2), q2) \<in> monoid_rtrancl (wts_to_monoidLTS ts2)"
    by (meson Cons.prems(1) Cons.prems(2) monoid_rtrancl_wts_to_monoidLTS_cases_rev)
  then have "ts1 $ (p1, \<gamma>, p') = dp1" "ts2 $ (q1, \<gamma>, q') = dq1"
    by (simp add: wts_label_d)+
  then have "(intersff ts1 ts2) $ ((p1,q1), \<gamma>, (p',q')) = dp1 * dq1"
    using finfun_apply_intersff_transition by blast
  then have pq1_pq1: "((p1,q1), ([\<gamma>], dp1 * dq1), (p',q')) \<in> wts_to_monoidLTS (intersff ts1 ts2)"
    by (simp add: wts_to_monoidLTS_def)
  from pq'_p Cons(1) obtain d2 where d2_p:
    "((p',q'), (w, d2), (p2,q2)) \<in> monoid_rtrancl (wts_to_monoidLTS (intersff ts1 ts2))"
    by blast
  then have "((p1,q1), (\<gamma>#w, (dp1 * dq1)*d2), (p2,q2)) \<in> monoid_rtrancl (wts_to_monoidLTS (intersff ts1 ts2))"
    using monoid_rtrancl_into_rtrancl_rev[of "(p1,q1)" "([\<gamma>],dp1 * dq1)" "(p',q')" "wts_to_monoidLTS (intersff ts1 ts2)" "(w,d2)" "(p2,q2)"]
    using pq1_pq1 by auto
  then show ?case
    by auto
qed

lemma intersff_complete_1:
  fixes p1::"'state::finite"
  fixes q1::"'state::finite"
  assumes "(p1, (w,1), p2) \<in> monoid_rtrancl (wts_to_monoidLTS ts1)"
  assumes "(q1, (w,d), q2) \<in> monoid_rtrancl (wts_to_monoidLTS ts2)"
  assumes "binary_aut ts1"
  shows "((p1,q1), (w,d), (p2,q2)) \<in> monoid_rtrancl (wts_to_monoidLTS (intersff ts1 ts2))"
  using assms(1,2)
proof (induction w arbitrary: p1 q1 d)
  case (Cons \<alpha> w1')
  obtain p' where p'_p: 
    "(p1, ([\<alpha>],1), p') \<in> wts_to_monoidLTS ts1"
    "(p', (w1',1), p2) \<in> monoid_rtrancl (wts_to_monoidLTS ts1)"
    using Cons(2) by (meson assms(3) binary_aut_monoid_rtrancl_wts_to_monoidLTS_cases_rev) 
  obtain q' dq1q' dq'q2 where q'_p: 
    "(q1, ([\<alpha>],dq1q'), q') \<in> wts_to_monoidLTS ts2"
    "(q', (w1',dq'q2), q2) \<in> monoid_rtrancl (wts_to_monoidLTS ts2)"
    "d = dq1q' * dq'q2"
    using Cons(3) using monoid_rtrancl_wts_to_monoidLTS_cases_rev[of q1 \<alpha> w1' d q2 ts2] by meson
  have ind: "((p', q'), (w1', dq'q2), (p2, q2)) \<in> monoid_rtrancl (wts_to_monoidLTS (intersff ts1 ts2))"
    by (simp add: Cons.IH p'_p(2) q'_p(2))
  moreover
  have "((p1, q1), ([\<alpha>], dq1q'), (p', q')) \<in> (wts_to_monoidLTS (intersff ts1 ts2))"
    using p'_p q'_p inftersff_complete_transition by (metis mult_1)
  ultimately
  have "((p1, q1), (\<alpha>#w1', dq1q' * dq'q2), (p2, q2)) \<in> monoid_rtrancl (wts_to_monoidLTS (intersff ts1 ts2))"
    using monoid_rtrancl_into_rtrancl_rev[of "(p1, q1)" " ([\<alpha>], dq1q')" "(p', q')" "wts_to_monoidLTS (intersff ts1 ts2)" "(w1', dq'q2)" "(p2, q2)"]
    by simp
  then show ?case
    by (simp add: q'_p)
next
  case Nil
  then show ?case
    by (metis fst_conv monoid_rtrancl.monoid_rtrancl_refl monoid_star_w0 mstar_wts_empty_one one_list_def one_prod_def)
qed

lemma intersff_complete_0:
  fixes ts1::"('state::finite, 'label::finite, 'weight::bounded_idempotent_semiring) w_transitions"
  fixes ts2::"('state::finite, 'label, 'weight) w_transitions"
  assumes "(p1, (w,0), p2) \<in> monoid_rtrancl (wts_to_monoidLTS ts1)"
  assumes "(q1, (w,d), q2) \<in> monoid_rtrancl (wts_to_monoidLTS ts2)"
  assumes "binary_aut ts1"
  shows "((p1,q1), (w,0), (p2,q2)) \<in> monoid_rtrancl (wts_to_monoidLTS (intersff ts1 ts2))"
  using assms(1,2)
proof (induction w arbitrary: p1 q1 d)
  case (Cons \<alpha> w1')
  then have "(\<exists>p' d'. (p1, ([\<alpha>], 0), p') \<in> wts_to_monoidLTS ts1 \<and> (p', (w1',d'), p2) \<in> monoid_rtrancl (wts_to_monoidLTS ts1)) 
           \<or> (\<exists>p' d'. (p1, ([\<alpha>], d'), p') \<in> wts_to_monoidLTS ts1 \<and> (p', (w1',0), p2) \<in> monoid_rtrancl (wts_to_monoidLTS ts1))"
    by (metis (no_types, lifting) assms(3) monoid_rtrancl_wts_to_monoidLTS_cases_rev mult_1 wts_label_d binary_aut_def)
  then show ?case
  proof 
    assume "(\<exists>p' d'. (p1, ([\<alpha>], 0), p') \<in> wts_to_monoidLTS ts1 \<and> (p', (w1',d'), p2) \<in> monoid_rtrancl (wts_to_monoidLTS ts1))"
    then obtain p' d' where p'_p:
      "(p1, ([\<alpha>], 0), p') \<in> wts_to_monoidLTS ts1"
      "(p', (w1',d'), p2) \<in> monoid_rtrancl (wts_to_monoidLTS ts1)"
      by auto
    moreover
    obtain q' qd1 qd2 where q'_p:
      "(q1, ([\<alpha>], qd1), q') \<in> wts_to_monoidLTS ts2" 
      "(q', (w1', qd2), q2) \<in> monoid_rtrancl (wts_to_monoidLTS ts2)"
      using Cons(3) monoid_rtrancl_wts_to_monoidLTS_cases_rev by fastforce
    ultimately
    have pq1_pq': "((p1,q1), ([\<alpha>], 0), (p',q')) \<in> wts_to_monoidLTS (intersff ts1 ts2)"
      using inftersff_complete_transition by fastforce

    obtain d2 where pq'_pq2: "((p',q'), (w1', d2), (p2,q2)) \<in> monoid_rtrancl (wts_to_monoidLTS (intersff ts1 ts2))"
      using intersff_complete_exi[of p' w1' _ p2 ts1 q' _ q2 ts2] Cons p'_p(2)
        q'_p(2) monoid_star_intros_step by blast
    show ?thesis
      using pq1_pq' pq'_pq2 monoid_rtrancl_into_rtrancl_rev[of "(p1, q1)" "([\<alpha>],0)" "(p', q')" "wts_to_monoidLTS (intersff ts1 ts2)" "(w1', d2)" "(p2, q2)"]
      by simp
  next
    assume "(\<exists>p' d. (p1, ([\<alpha>], d), p') \<in> wts_to_monoidLTS ts1 \<and> (p', (w1',0), p2) \<in> monoid_rtrancl (wts_to_monoidLTS ts1))"
    then obtain p' d' where p'_p:
      "(p1, ([\<alpha>], d'), p') \<in> wts_to_monoidLTS ts1"
      "(p', (w1',0), p2) \<in> monoid_rtrancl (wts_to_monoidLTS ts1)"     
      by auto
    obtain q' X Y where q'_p:
      "(q1, ([\<alpha>], X), q') \<in> wts_to_monoidLTS ts2"
      "(q', (w1', Y), q2) \<in> monoid_rtrancl (wts_to_monoidLTS ts2)"
      using Cons(3) monoid_rtrancl_wts_to_monoidLTS_cases_rev by fastforce
    obtain d1 where d1_p: "((p1,q1), ([\<alpha>], d1), (p',q')) \<in> wts_to_monoidLTS (intersff ts1 ts2)"
      using wts_to_monoidLTS_def by fastforce
    have "((p',q'), (w1', 0), (p2,q2)) \<in> monoid_rtrancl (wts_to_monoidLTS (intersff ts1 ts2))"
      using Cons(1)[of p' q'] p'_p(2) q'_p by blast
    then show ?thesis
      using d1_p monoid_rtrancl_into_rtrancl_rev[of "(p1, q1)" "([\<alpha>],d1)" "(p', q')" "wts_to_monoidLTS (intersff ts1 ts2)" "(w1',0)" "(p2, q2)"]
      by simp
  qed
next
  case Nil
  then show ?case
    by (metis fst_conv monoid_rtrancl.monoid_rtrancl_refl monoid_star_w0 mstar_wts_empty_one one_list_def one_prod_def)
qed

lemma intersff_sound_exi_fst:
  assumes "((p1,q1), (w,d), (p2,q2)) \<in> monoid_rtrancl (wts_to_monoidLTS (intersff ts1 ts2))"
  shows "\<exists>d'. (p1, (w,d'), p2) \<in> monoid_rtrancl (wts_to_monoidLTS ts1)"
  using assms 
proof (induction rule: wts_to_monoidLTS_pair_induct)
  case (base p q)
  then show ?case
    using monoid_rtrancl_wts_to_monoidLTS_refl by force
next
  case (step p1 q1 w12 d12 p2 q2 w23 d23 p3 q3)
  then have "\<exists>d2. (p2, (w23,d2), p3) \<in> wts_to_monoidLTS ts1"
    using wts_label_exist wts_to_monoidLTS_def by fastforce
  then show ?case
    using step(3) monoid_rtrancl.monoid_rtrancl_into_rtrancl[of p1 "(w12, _)" p2 "(wts_to_monoidLTS ts1)" "(w23, _)" p3]
    by auto
qed

lemma intersff_sound_non_zero_fst:
  fixes ts1::"('state::finite, 'label::finite, 'weight::bounded_idempotent_semiring) w_transitions"
  fixes ts2::"('state::finite, 'label, 'weight) w_transitions"
  assumes "((p1,q1), (w,d), (p2,q2)) \<in> monoid_rtrancl (wts_to_monoidLTS (intersff ts1 ts2))"
  assumes "binary_aut ts1"
  assumes "d\<noteq>0"
  shows "(p1, (w,1), p2) \<in> monoid_rtrancl (wts_to_monoidLTS ts1)"
  using assms 
proof (induction rule: wts_to_monoidLTS_pair_induct)
  case (base p q)
  then show ?case
    by (simp add: monoid_rtrancl_wts_to_monoidLTS_refl)
next
  case (step p1 q1 w12 d12 p2 q2 w23 d23 p3 q3)
    
  have d12_non0: "d12 \<noteq> 0"
    using step.prems(2) by force
  have d23_non0: "d23 \<noteq> 0"
    using step.prems(2) by force

  then have "(p1, (w12, 1), p2) \<in> monoid_rtrancl (wts_to_monoidLTS ts1)"
    using d12_non0 step.IH step.prems(1) by blast
  moreover
  have "(intersff ts1 ts2) $ ((p2, q2), hd w23, (p3, q3)) = d23"
    using wts_label_d' step.hyps(2) by fastforce
  then obtain d23p d23q where
    "(p2, (w23, d23p), p3) \<in> (wts_to_monoidLTS ts1)"
    "(q2, (w23, d23q), q3) \<in> (wts_to_monoidLTS ts2)"
    "d23p * d23q = d23"
    by (metis intersff_sound_transition step.hyps(2))
  then have "(p2, (w23, 1), p3) \<in> wts_to_monoidLTS ts1"
    using binary_aut_transition_binary d23_non0 step.prems(1) by force
  ultimately
  show ?case
    using monoid_rtrancl.monoid_rtrancl_into_rtrancl[of p1 "(w12, 1)" p2 "(wts_to_monoidLTS ts1)" "(w23, 1)" p3]
    by auto
qed

lemma intersff_sound_exi_snd:
  assumes "((p1,q1), (w,d), (p2,q2)) \<in> monoid_rtrancl (wts_to_monoidLTS (intersff ts1 ts2))"
  shows "\<exists>d'. (q1, (w,d'), q2) \<in> monoid_rtrancl (wts_to_monoidLTS ts2)"
  using assms
proof (induction rule: wts_to_monoidLTS_pair_induct)
  case (base p q)
  then show ?case
    using monoid_rtrancl_wts_to_monoidLTS_refl by force
next
  case (step p1 q1 w12 d12 p2 q2 w23 d23 p3 q3)
  then have "\<exists>d2. (q2, (w23,d2), q3) \<in> wts_to_monoidLTS ts2"
    using wts_label_exist wts_to_monoidLTS_def by fastforce
  then show ?case
    using step(3) monoid_rtrancl.monoid_rtrancl_into_rtrancl[of q1 "(w12, _)" q2 "(wts_to_monoidLTS ts2)" "(w23, _)" q3]
    by auto
qed

lemma intersff_sound_snd_non_zero:
  fixes ts1::"('state::finite, 'label::finite, 'weight::bounded_idempotent_semiring) w_transitions"
  fixes ts2::"('state::finite, 'label, 'weight) w_transitions"
  assumes "((p1,q1), (w,d), (p2,q2)) \<in> monoid_rtrancl (wts_to_monoidLTS (intersff ts1 ts2))"
  assumes "binary_aut ts1"
  assumes "d\<noteq>0"
  shows "(q1, (w,d), q2) \<in> monoid_rtrancl (wts_to_monoidLTS ts2)"
  using assms
proof (induction rule: wts_to_monoidLTS_pair_induct)
  case (base p q)
  then show ?case
    by (simp add: monoid_rtrancl_wts_to_monoidLTS_refl)
next
  case (step p1 q1 w12 d12 p2 q2 w23 d23 p3 q3)

  have "d12 \<noteq> 0"
    using step.prems(2) by force
  have "d23 \<noteq> 0"
    using mult_not_zero step.prems(2) by blast

  have "(q1, (w12, d12), q2) \<in> monoid_rtrancl (wts_to_monoidLTS ts2)"
    using \<open>d12 \<noteq> 0\<close> by (simp add: step.IH step.prems(1)) 

  obtain d23p d23q where f:
    "(p2, (w23, d23p), p3) \<in> (wts_to_monoidLTS ts1)"
    "(q2, (w23, d23q), q3) \<in> (wts_to_monoidLTS ts2)"
    "d23p * d23q = d23"
    by (metis intersff_sound_transition step.hyps(2))

  have "d23p = 1"
    by (metis \<open>d23 \<noteq> 0\<close> d_mult_not_zero(1) f(1) f(3) binary_aut_transition_binary step.prems(1))
  then have "d23q = d23"
    using f(3) by auto
  then show ?case
    using \<open>(q1, (w12, d12), q2) \<in> monoid_rtrancl (wts_to_monoidLTS ts2)\<close> f(2) 
    using monoid_rtrancl.monoid_rtrancl_into_rtrancl[of q1 "(w12, d12)" q2 "(wts_to_monoidLTS ts2)" "(w23, d23q)" q3] 
    by auto
qed

lemma intersff_sound_zero:
  fixes ts1::"('state::finite, 'label::finite, 'weight::bounded_idempotent_semiring) w_transitions"
  fixes ts2::"('state::finite, 'label, 'weight) w_transitions"
  assumes "((p1,q1), (w,d), (p2,q2)) \<in> monoid_rtrancl (wts_to_monoidLTS (intersff ts1 ts2))"
  assumes "binary_aut ts1"
  assumes "d=0"
  shows "(p1, (w,0), p2) \<in> monoid_rtrancl (wts_to_monoidLTS ts1) \<or>
         (q1, (w,0), q2) \<in> monoid_rtrancl (wts_to_monoidLTS ts2)"
  using assms 
proof (induction rule: wts_to_monoidLTS_pair_induct)
  case (base p q)
  then show ?case
    by (metis monoid_rtrancl_wts_to_monoidLTS_refl)
next
  case (step p1 q1 w12 d12 p2 q2 w23 d23 p3 q3)
  show ?case
  proof (cases "d12 = 0")
    case True
    then have "(p1, (w12, 0), p2) \<in> monoid_rtrancl (wts_to_monoidLTS ts1) \<or>
    (q1, (w12, 0), q2) \<in> monoid_rtrancl (wts_to_monoidLTS ts2)"
      using step.IH step.prems(1) by auto
    then show ?thesis
    proof
      assume "(p1, (w12, 0),p2) \<in> monoid_rtrancl (wts_to_monoidLTS ts1)"
      moreover
      have "\<exists>dp23. (p2, (w23, dp23), p3) \<in> monoid_rtrancl (wts_to_monoidLTS ts1)"
        by (meson intersff_sound_transition monoid_star_intros_step step.hyps(2))
      ultimately
      have "(p1, ((w12 @ w23), 0), p3) \<in> monoid_rtrancl (wts_to_monoidLTS ts1)"
        using monoid_rtrancl_rtrancl_into_rtrancl[of p1 "(w12, 0)" p2 "(wts_to_monoidLTS ts1)" "(w23, _)" p3]
        by auto
      then show ?thesis
        by simp
    next
      assume "(q1, (w12, 0), q2) \<in> monoid_rtrancl (wts_to_monoidLTS ts2)"
      moreover
      have "\<exists>dq23. (q2, (w23, dq23), q3) \<in> monoid_rtrancl (wts_to_monoidLTS ts2)"
        by (meson intersff_sound_transition monoid_star_intros_step step.hyps(2))
      ultimately
      show ?thesis
        using monoid_rtrancl_rtrancl_into_rtrancl[of q1 "(w12, 0)" q2 "(wts_to_monoidLTS ts2)" "(w23, _)" q3]
        by auto
    qed
  next
    case False
    note outer_outer_False = False
    obtain d23p d23q where d23p_d23q_p: "(p2, (w23, d23p), p3) \<in> wts_to_monoidLTS ts1"
      "(q2, (w23, d23q), q3) \<in> wts_to_monoidLTS ts2"
      "d23 = d23p * d23q"
      using intersff_sound_transition step.hyps(2) by blast
    have d13zero: "d12 * d23 = 0"
      using snd_conv using step.prems(2) by blast
    have d23_split: "d23 = d23p * d23q"
      using \<open>d23 = d23p * d23q\<close> .
    have d23p01: "d23p = 1 \<or> d23p = 0"
      using \<open>(p2, (w23, d23p), p3) \<in> wts_to_monoidLTS ts1\<close> using snd_conv wts_label_d' binary_aut_def
      by (metis step.prems(1)) (* By the corresponding edge being in ts1*)
    show ?thesis
    proof (cases "d23p = 0")
      case True
      have "(p2, (w23, 0), p3) \<in> wts_to_monoidLTS ts1"
        using True d23p_d23q_p(1) by blast
      moreover
      have "\<exists>dp12. (p1, (w12, dp12), p2) \<in> monoid_rtrancl (wts_to_monoidLTS ts1)"
        using intersff_sound_non_zero_fst outer_outer_False step by blast
      ultimately
      have "(p1, (w12 @ w23, 0), p3) \<in> monoid_rtrancl (wts_to_monoidLTS ts1)"
        using monoid_rtrancl_into_rtrancl[of p1 "(w12,_)" p2 "(wts_to_monoidLTS ts1)"
            "(w23, d23p)" p3]
        using True by auto
      then have "(p1, ((w12 @ w23), 0), p3) \<in> monoid_rtrancl (wts_to_monoidLTS ts1)"
        by auto
      then show ?thesis
        by simp
    next
      case False
      note outer_False = False
      show ?thesis
      proof (cases "d23q = 0")
        case True
        have "(q2, (w23, 0), q3) \<in> wts_to_monoidLTS ts2"
          using True d23p_d23q_p(2) monoid_star_intros_step by blast
        moreover
        have "\<exists>dq12. (q1, (w12, dq12), q2) \<in> monoid_rtrancl (wts_to_monoidLTS ts2)"
          using assms(2) outer_outer_False intersff_sound_snd_non_zero
            step.hyps(1) by fastforce
        ultimately
        have "(q1, (w12 @ w23, 0), q3) \<in> monoid_rtrancl (wts_to_monoidLTS ts2)"
          using monoid_rtrancl_into_rtrancl[of q1 "(w12,_)" q2 "(wts_to_monoidLTS ts2)"
              "(w23, d23q)" q3]
          using True by auto
        then show ?thesis 
          unfolding times_list_def by metis
      next
        case False
        have d23p_one: "d23p = 1"
          using d23p01 outer_False by auto
        have "(q1, (w12, d12), q2) \<in> monoid_rtrancl (wts_to_monoidLTS ts2)"
          using intersff_sound_snd_non_zero outer_outer_False step.hyps(1)
            step.prems(1) by blast
        moreover
        have "(q2, (w23, d23q), q3) \<in> wts_to_monoidLTS ts2"
          using d23p_d23q_p(2) by fastforce
        ultimately
        have "(q1, (w12 @ w23, d12 * d23q), q3) \<in> monoid_rtrancl (wts_to_monoidLTS ts2)"
          using monoid_rtrancl.intros(2)[of q1 "(w12,_)"] by auto
        then show ?thesis
          using d23p_one d13zero d23_split by force
      qed
    qed
  qed
qed

lemma intersff_sound_and_complete:
  fixes ts1::"('state::finite, 'label::finite, 'weight::bounded_idempotent_semiring) w_transitions"
  fixes ts2::"('state::finite, 'label, 'weight) w_transitions"
  assumes "binary_aut ts1"
  shows "((p1,q1), (w,d), (p2,q2)) \<in> monoid_rtrancl (wts_to_monoidLTS (intersff ts1 ts2)) \<longleftrightarrow>
           (\<exists>dp dq. (p1, (w,dp), p2) \<in> monoid_rtrancl (wts_to_monoidLTS ts1) \<and>
                     (q1, (w,dq), q2) \<in> monoid_rtrancl (wts_to_monoidLTS ts2) \<and> dp * dq = d)"
proof (cases "d = 0")
  case True
  show ?thesis
  proof 
    assume inter: "((p1, q1), (w, d), p2, q2) \<in> monoid_rtrancl (wts_to_monoidLTS (intersff ts1 ts2))"
    then have dis0: "(p1, (w, 0), p2) \<in> monoid_rtrancl (wts_to_monoidLTS ts1) \<or> (q1, (w, 0), q2) \<in> monoid_rtrancl (wts_to_monoidLTS ts2)"
      using True
      using intersff_sound_zero[of p1 q1 w d p2 q2 ts1 ts2] assms by auto
    moreover
    have p1p2: "\<exists>dp. (p1, (w, dp), p2) \<in> monoid_rtrancl (wts_to_monoidLTS ts1)"
      using intersff_sound_exi_fst[of p1 q1 w d p2, OF inter] by auto
    moreover
    have "\<exists>dq. (q1, (w, dq), q2) \<in> monoid_rtrancl (wts_to_monoidLTS ts2)"
      by (meson inter intersff_sound_exi_snd)
    ultimately
    show "\<exists>dp dq. (p1, (w, dp), p2) \<in> monoid_rtrancl (wts_to_monoidLTS ts1) \<and> (q1, (w, dq), q2) \<in> monoid_rtrancl (wts_to_monoidLTS ts2) \<and> dp * dq = d"
      using True mult_not_zero by blast
  next
    assume "\<exists>dp dq. (p1, (w, dp), p2) \<in> monoid_rtrancl (wts_to_monoidLTS ts1) \<and> (q1, (w, dq), q2) \<in> monoid_rtrancl (wts_to_monoidLTS ts2) \<and> dp * dq = d"
    then obtain dp dq where
      "(p1, (w, dp), p2) \<in> monoid_rtrancl (wts_to_monoidLTS ts1)"
      "(q1, (w, dq), q2) \<in> monoid_rtrancl (wts_to_monoidLTS ts2)"
      "dp * dq = d"
      by auto
    then show "((p1, q1), (w, d), p2, q2) \<in> monoid_rtrancl (wts_to_monoidLTS (intersff ts1 ts2))"
      using assms binary_aut_path_binary intersff_complete_0 intersff_complete_1 by fastforce 
  qed
next
  case False
  show ?thesis
  proof 
    assume "((p1, q1), (w, d), p2, q2) \<in> monoid_rtrancl (wts_to_monoidLTS (intersff ts1 ts2))"
    show "\<exists>dp dq. (p1, (w, dp), p2) \<in> monoid_rtrancl (wts_to_monoidLTS ts1) \<and> (q1, (w, dq), q2) \<in> monoid_rtrancl (wts_to_monoidLTS ts2) \<and> dp * dq = d"
      by (meson False \<open>((p1, q1), (w, d), p2, q2) \<in> monoid_rtrancl (wts_to_monoidLTS (intersff ts1 ts2))\<close> assms intersff_sound_non_zero_fst intersff_sound_snd_non_zero mult_1)
  next 
    assume "\<exists>dp dq. (p1, (w, dp), p2) \<in> monoid_rtrancl (wts_to_monoidLTS ts1) \<and> (q1, (w, dq), q2) \<in> monoid_rtrancl (wts_to_monoidLTS ts2) \<and> dp * dq = d"
    then obtain dp dq where
      "(p1, (w, dp), p2) \<in> monoid_rtrancl (wts_to_monoidLTS ts1)"
      "(q1, (w, dq), q2) \<in> monoid_rtrancl (wts_to_monoidLTS ts2)"
      "dp * dq = d"
      by auto
    then show "((p1, q1), (w, d), p2, q2) \<in> monoid_rtrancl (wts_to_monoidLTS (intersff ts1 ts2))"
      using False assms binary_aut_path_binary intersff_complete_1 by fastforce
  qed
qed

lemma intersff_sound:
  fixes ts1::"('state::finite, 'label::finite, 'weight::bounded_idempotent_semiring) w_transitions"
  fixes ts2::"('state::finite, 'label, 'weight) w_transitions"
  assumes "binary_aut ts1"
  assumes "((p1,q1), (w,d), (p2,q2)) \<in> monoid_rtrancl (wts_to_monoidLTS (intersff ts1 ts2))"
  shows "(\<exists>dp dq. (p1, (w,dp), p2) \<in> monoid_rtrancl (wts_to_monoidLTS ts1) \<and>
                  (q1, (w,dq), q2) \<in> monoid_rtrancl (wts_to_monoidLTS ts2) \<and> dp * dq = d)"
  using intersff_sound_and_complete assms by metis

lemma intersff_complete:
  fixes ts1::"('state::finite, 'label::finite, 'weight::bounded_idempotent_semiring) w_transitions"
  fixes ts2::"('state::finite, 'label, 'weight) w_transitions"
  assumes "binary_aut ts1"
  assumes "(p1, (w,dp), p2) \<in> monoid_rtrancl (wts_to_monoidLTS ts1)"
  assumes "(q1, (w,dq), q2) \<in> monoid_rtrancl (wts_to_monoidLTS ts2)"
  shows "((p1,q1), (w,dp * dq), (p2,q2)) \<in> monoid_rtrancl (wts_to_monoidLTS (intersff ts1 ts2))"
  using intersff_sound_and_complete assms by metis

lemma intersff_sound_wts_to_weightLTS:
  fixes ts1::"('state::finite, 'label::finite, 'weight::bounded_idempotent_semiring) w_transitions"
  fixes ts2::"('state::finite, 'label, 'weight) w_transitions"
  assumes "binary_aut ts1"
  assumes "((p1,q1), d, (p2,q2)) \<in> monoid_rtrancl (wts_to_weightLTS (intersff ts1 ts2))"
  shows "(\<exists>dp dq. (p1, dp, p2) \<in> monoid_rtrancl (wts_to_weightLTS ts1) \<and>
         (q1, dq, q2) \<in> monoid_rtrancl (wts_to_weightLTS ts2) \<and> dp * dq = d)"  
  using assms wts_weightLTS_star_to_monoidLTS_star[of "(p1,q1)" d "(p2,q2)" "intersff ts1 ts2"]
        intersff_sound[OF assms(1), of p1 q1 _ d p2 q2 ts2] wts_monoidLTS_star_to_weightLTS_star
  by meson

lemma intersff_sound_wts_to_monoidLTS:
  fixes ts1::"('state::finite, 'label::finite, 'weight::bounded_idempotent_semiring) w_transitions"
  fixes ts2::"('state::finite, 'label, 'weight) w_transitions"
  assumes "binary_aut ts1"
  assumes "((p1,q1), d, (p2,q2)) \<in> monoid_rtrancl (wts_to_weightLTS (intersff ts1 ts2))"
  shows "(\<exists>w dp dq. (p1, (w,dp), p2) \<in> monoid_rtrancl (wts_to_monoidLTS ts1) \<and>
                    (q1, (w,dq), q2) \<in> monoid_rtrancl (wts_to_monoidLTS ts2) \<and> dp * dq = d)"
  using wts_weightLTS_star_to_monoidLTS_star[of "(p1,q1)" d "(p2,q2)" "intersff ts1 ts2"]
        intersff_sound[OF assms(1), of p1 q1 _ d p2 q2 ts2] assms(2)
  by meson

lemma intersff_complete_wts_to_weightLTS:
  fixes ts1::"('state::finite, 'label::finite, 'weight::bounded_idempotent_semiring) w_transitions"
  fixes ts2::"('state::finite, 'label, 'weight) w_transitions"
  assumes "binary_aut ts1"
  assumes "(p1, (w, dp), p2) \<in> monoid_rtrancl (wts_to_monoidLTS ts1)"
  assumes "(q1, (w, dq), q2) \<in> monoid_rtrancl (wts_to_monoidLTS ts2)"
  shows "((p1, q1), dp * dq, (p2, q2)) \<in> monoid_rtrancl (wts_to_weightLTS (intersff ts1 ts2))"
  using intersff_complete[OF assms(1)] assms(2,3)
        wts_monoidLTS_star_to_weightLTS_star[of "(p1,q1)" w "dp * dq" "(p2,q2)" "intersff ts1 ts2"]
  by fast

definition "fst_trans_all = fin_fun_of_fun fst_trans"
definition "snd_trans_all = fin_fun_of_fun snd_trans"

lemma fst_trans_all_is_fst_trans: "fst_trans_all $ t = fst_trans t"
  by (simp add: app_fin_fun_of_fun fst_trans_all_def)

lemma snd_trans_all_is_snd_trans: "snd_trans_all $ t = snd_trans t"
  by (simp add: app_fin_fun_of_fun snd_trans_all_def)

lemma pair_weight_code': "(pair_weight ts1 ts2) $ t = finfun_Diag ((($) ts1) \<circ>$ fst_trans_all) ((($) ts2) \<circ>$ snd_trans_all) $ t"
  by (simp add: fst_trans_all_is_fst_trans snd_trans_all_is_snd_trans finfun_apply_pair_weight)

lemma pair_weight_code[code]: "pair_weight ts1 ts2 = finfun_Diag ((($) ts1) \<circ>$ fst_trans_all) ((($) ts2) \<circ>$ snd_trans_all)"
  using pair_weight_code' by (metis finfun_ext)


end