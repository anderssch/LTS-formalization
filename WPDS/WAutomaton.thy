theory WAutomaton
  imports "Labeled_Transition_Systems.LTS" "Saturation" "FinFunWellFounded" "FinFunAddUpdate" "MonoidLTS" "Kleene_Algebra.Dioid_Models" "Set_More" "FinFunOf"
begin

section \<open>Basic datatypes and definitions\<close>

declare times_list_def[simp]

\<comment> \<open>For the semantics of a weighted automaton, labels are lifted to the list-monoid and paired with a weight\<close>
type_synonym ('label, 'weight) wautomaton_label = "('label list \<times> 'weight)" 

\<comment> \<open>Weighted automata transitions are modelled as a @{term finfun} from transitions to their weight, 
    where @{term "0::('weight::bounded_dioid)"} is the default value, indicating no transition.\<close>
type_synonym ('state, 'label, 'weight) w_transitions = "('state, 'label) transition \<Rightarrow>f 'weight"

type_synonym ('state, 'label, 'weight) w_transition_set = "('state, ('label list \<times> 'weight)) transition set"

\<comment> \<open>Embed a weighted automaton into a monoidLTS. All transitions are added. The label is lifted to the list-monoid.\<close>
definition wts_to_monoidLTS :: "('state, 'label, 'weight::bounded_dioid) w_transitions 
                             \<Rightarrow> ('state, ('label list \<times> 'weight)) transition set" ("\<lbrakk>_\<rbrakk>") where
  "\<lbrakk>ts\<rbrakk> = {(p, ([\<gamma>],d), q) | p \<gamma> d q. ts $ (p,\<gamma>,q) = d}"

lemma wts_to_monoidLTS_code[code]:
  "\<lbrakk>ts\<rbrakk> = (\<Union>(p,\<gamma>,q). {(p, ([\<gamma>], ts $ (p,\<gamma>,q)), q)})"
  unfolding wts_to_monoidLTS_def by blast

definition wts_to_weightLTS :: "('state, 'label, 'weight::bounded_dioid) w_transitions 
                             \<Rightarrow> ('state, 'weight) transition set" ("\<lbrakk>_\<rbrakk>\<^sub>w") where
  "\<lbrakk>ts\<rbrakk>\<^sub>w = {(p, d, q) | p \<gamma> d q. ts $ (p,\<gamma>,q) = d}"

lemma wts_to_weightLTS_code[code]: "\<lbrakk>ts\<rbrakk>\<^sub>w = (\<Union>(p,\<gamma>,q). {(p, (ts $ (p,\<gamma>,q)), q)})"
  unfolding wts_to_weightLTS_def by blast

lemma finite_wts: 
  fixes wts::"('state::enum, 'label::finite, 'weight::bounded_dioid) w_transitions"
  shows "finite \<lbrakk>wts\<rbrakk>"
proof -
  have "range (\<lambda>t. (fst t, ([fst (snd t)], wts $ t), snd (snd t))) = {t. \<exists>p \<gamma> q. t = (p, ([\<gamma>], wts $ (p, \<gamma>, q)), q)}"
    by force
  then have "finite {t. \<exists>p \<gamma> q. t = (p, ([\<gamma>], wts $ (p, \<gamma>, q)), q)}"
    using finite_imageI[of UNIV "(\<lambda>t. (fst t, ([fst (snd t)], wts $ t), snd (snd t)))"] by simp
  then show ?thesis unfolding wts_to_monoidLTS_def by presburger
qed

lemma wts_monoidLTS_to_weightLTS: "(p, (w, d), p') \<in> \<lbrakk>ts\<rbrakk> \<Longrightarrow> (p, d, p') \<in> \<lbrakk>ts\<rbrakk>\<^sub>w"
  unfolding wts_to_monoidLTS_def wts_to_weightLTS_def by blast

lemma wts_monoidLTS_star_to_weightLTS_star:
  "(p, (w,d), q) \<in> \<lbrakk>ts\<rbrakk>\<^sup>\<odot> \<Longrightarrow> (p, d, q) \<in> \<lbrakk>ts\<rbrakk>\<^sub>w\<^sup>\<odot>"
  apply (induct rule: monoid_rtrancl_pair_weight_induct, simp)
  subgoal for p w d p' w' d' p''
    using monoid_rtrancl_into_rtrancl[of p d p' "\<lbrakk>ts\<rbrakk>\<^sub>w" d' p''] wts_monoidLTS_to_weightLTS[of p' w' d' p'' ts]
    by blast
  done

lemma wts_weightLTS_to_monoidLTS: "(p, d, p') \<in> \<lbrakk>ts\<rbrakk>\<^sub>w \<Longrightarrow> \<exists>w. (p, (w,d), p') \<in> \<lbrakk>ts\<rbrakk>"
  unfolding wts_to_monoidLTS_def wts_to_weightLTS_def by blast

lemma wts_weightLTS_star_to_monoidLTS_star:
  "(p, d, q) \<in> \<lbrakk>ts\<rbrakk>\<^sub>w\<^sup>\<odot> \<Longrightarrow> \<exists>w. (p, (w,d), q) \<in> \<lbrakk>ts\<rbrakk>\<^sup>\<odot>"
  apply (induct rule: monoid_rtrancl.induct)
   apply (rule exI[of _ 1])
   apply (metis one_prod_def monoid_rtrancl_refl)
  apply safe
  subgoal for p d p' d' p'' w
    using wts_weightLTS_to_monoidLTS[of p' d' p'' ts]
    apply simp
    apply safe
    subgoal for w'
      using monoid_rtrancl_into_rtrancl[of p "(w,d)" p' "\<lbrakk>ts\<rbrakk>" "(w',d')" p'']
      by auto
    done
  done

lemma countable_wts: 
  fixes A :: "(('state::countable, 'label::finite, 'weight::bounded_dioid) w_transitions)"
  shows "countable \<lbrakk>A\<rbrakk>"
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
  "(p, ([], 1), p) \<in> \<lbrakk>A\<rbrakk>\<^sup>\<odot>"
  by (metis monoid_rtrancl_refl one_list_def one_prod_def)

lemma wts_to_monoidLTS_mono': 
  "ts \<le> ts' \<Longrightarrow> (p, (w, d), q) \<in> \<lbrakk>ts\<rbrakk> \<Longrightarrow> \<exists>d'. (p, (w, d'), q) \<in> \<lbrakk>ts'\<rbrakk> \<and> d \<le> d'"
  unfolding less_eq_finfun_def wts_to_monoidLTS_def by blast

lemma wts_to_monoidLTS_mono: 
  "ts' \<le> ts \<Longrightarrow> (p, (w, d), q) \<in> \<lbrakk>ts\<rbrakk> \<Longrightarrow> \<exists>d'. (p, (w, d'), q) \<in> \<lbrakk>ts'\<rbrakk> \<and> d' \<le> d"
  unfolding less_eq_finfun_def wts_to_monoidLTS_def by blast

lemma wts_monoid_rtrancl_mono: 
  assumes "ts' \<le> ts"
  assumes "(p, (w, d), q) \<in> \<lbrakk>ts\<rbrakk>\<^sup>\<odot>"
  shows "\<exists>d'. (p, (w, d'), q) \<in> \<lbrakk>ts'\<rbrakk>\<^sup>\<odot> \<and> d' \<le> d"
proof (induction rule: monoid_rtrancl_pair_weight_induct[OF assms(2)])
  case (1 p)
  then show ?case 
    by (rule exI[of _ "1"]) 
       (simp add: monoid_rtrancl_refl[of _ "\<lbrakk>ts'\<rbrakk>", unfolded one_prod_def])
next
  case (2 p w d p' w' d' p'')
  obtain da da' 
    where da:"(p, (w, da), p') \<in> \<lbrakk>ts'\<rbrakk>\<^sup>\<odot>" "da \<le> d" 
     and da':"(p', (w', da'), p'') \<in> \<lbrakk>ts'\<rbrakk>" "da' \<le> d'" 
    using 2(3) wts_to_monoidLTS_mono[OF assms(1) 2(2)] by blast
  show ?case
    apply (rule exI[of _ "da * da'"])
    using da(2) da'(2) monoid_rtrancl_into_rtrancl[OF da(1) da'(1)]
    by (simp add: idempotent_semiring_ord_class.mult_isol_var)
qed


section \<open>Locale: W_automaton\<close>

locale W_automaton = monoidLTS "\<lbrakk>transition_relation\<rbrakk>"
  for transition_relation :: "('state::finite, 'label, 'weight::bounded_dioid) w_transitions"
begin
interpretation monoidLTS "\<lbrakk>transition_relation\<rbrakk>" .
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

lemma monoid_star_imp_exec: "(p,w,q) \<in> \<lbrakk>ts\<rbrakk>\<^sup>\<odot> \<Longrightarrow> (q, snd w) \<in> monoidLTS_reach \<lbrakk>ts\<rbrakk> p (fst w)"
  apply (induct rule: monoid_rtrancl_induct_rev)
  apply (force simp add: one_prod_def one_list_def)
  by (fastforce simp add: wts_to_monoidLTS_def)

lemma monoidLTS_reach_imp: "(q, d) \<in> monoidLTS_reach \<lbrakk>ts\<rbrakk> p w \<Longrightarrow> (p,(w,d),q) \<in> \<lbrakk>ts\<rbrakk>\<^sup>\<odot>"
  apply (induct p w arbitrary: d rule: monoidLTS_reach.induct[of _ "\<lbrakk>ts\<rbrakk>"])
   apply (simp add: monoid_rtrancl_refl[of q "\<lbrakk>ts\<rbrakk>", unfolded one_prod_def one_list_def])
  subgoal for p \<gamma> w'
    apply auto[1]
    subgoal for _ _ _ _ q' d d'
      using monoid_rtrancl_into_rtrancl_rev[of p "([\<gamma>],d)" q' "\<lbrakk>ts\<rbrakk>" "(w',d')" q]
      apply (auto simp add: wts_to_monoidLTS_def)
      by (metis empty_iff singleton_iff fst_eqD snd_eqD)
    done
  done

lemma monoid_star_code[code_unfold]: "(p,(w,d),q) \<in> \<lbrakk>ts\<rbrakk>\<^sup>\<odot> \<longleftrightarrow> (q,d) \<in> monoidLTS_reach \<lbrakk>ts\<rbrakk> p w"
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


lemma monoid_star_n0_imp_exec: "(p,w,q) \<in> \<lbrakk>ts\<rbrakk>\<^sup>\<odot> \<Longrightarrow> snd w = 0 \<or> (q, snd w) \<in> monoidLTS_reach_not0 \<lbrakk>ts\<rbrakk> p (fst w)"
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
    then have "(q, d') \<in> monoidLTS_reach_not0 \<lbrakk>ts\<rbrakk> p' (fst w')"
      using monoid_rtrancl_into_rtrancl(2) d'_def by blast
    then have "(q, d * d') \<in> monoidLTS_reach_not0 \<lbrakk>ts\<rbrakk> p (\<gamma> # fst w')"
      using monoid_rtrancl_into_rtrancl(1) False w d0 by fastforce
    then show ?thesis using lw' dd' by argo
  qed
qed

lemma monoidLTS_reach_n0_cons_exists:
  assumes "(q, d) \<in> monoidLTS_reach_not0 \<lbrakk>ts\<rbrakk> p (\<gamma> # w)"
  shows "\<exists>p' d' d''. (p, ([\<gamma>], d'), p') \<in> \<lbrakk>ts\<rbrakk> \<and> (q, d'') \<in> monoidLTS_reach_not0 \<lbrakk>ts\<rbrakk> p' w \<and> d' \<noteq> 0 \<and> d = d' * d''"
  using assms by (simp, safe) (metis empty_iff prod.inject singletonD)

lemma monoidLTS_reach_n0_imp: "(q, d) \<in> monoidLTS_reach_not0 \<lbrakk>ts\<rbrakk> p w \<Longrightarrow> (p,(w,d),q) \<in> \<lbrakk>ts\<rbrakk>\<^sup>\<odot>"
proof (induct p w arbitrary: d rule: monoidLTS_reach_not0.induct[of _ "\<lbrakk>ts\<rbrakk>"])
  case (1 p d)
  then show ?case by (simp add: monoid_rtrancl_refl[of p "\<lbrakk>ts\<rbrakk>", unfolded one_prod_def one_list_def])
next
  case (2 p \<gamma> w d)
  from 2(2) obtain p' d' d''
    where *:"(p, ([\<gamma>], d'), p') \<in> \<lbrakk>ts\<rbrakk>"
            "(q, d'') \<in> monoidLTS_reach_not0 \<lbrakk>ts\<rbrakk> p' w"
            "d = d' * d''" and "d' \<noteq> 0" using monoidLTS_reach_n0_cons_exists by meson
  then have "(p', d') \<in> (\<Union>(p', (\<gamma>', d), q')\<in>\<lbrakk>ts\<rbrakk>. if p' = p \<and> \<gamma>' = [\<gamma>] \<and> d \<noteq> 0 then {(q', d)} else {})"
    by fastforce
  then show ?case 
    using * 2(1) monoid_rtrancl_into_rtrancl_rev[of p "([\<gamma>],d')" p' "\<lbrakk>ts\<rbrakk>" "(w,d'')" q]
    unfolding mult_prod_def times_list_def by auto
qed

lemma monoid_star_n0_code[code_unfold]: "d \<noteq> 0 \<Longrightarrow> (p,(w,d),q) \<in> \<lbrakk>ts\<rbrakk>\<^sup>\<odot> \<longleftrightarrow> (q,d) \<in> monoidLTS_reach_not0 \<lbrakk>ts\<rbrakk> p w"
  using monoidLTS_reach_n0_imp monoid_star_n0_imp_exec by fastforce

\<comment> \<open>Auxiliary lemmas for WAutomaton and monoidLTS\<close>
lemma wts_label_exist: "(p, w, q) \<in> \<lbrakk>ts\<rbrakk> \<Longrightarrow> \<exists>\<gamma>. fst w = [\<gamma>]"
  unfolding wts_to_monoidLTS_def by fastforce

lemma wts_label_not_empty: "(p, w, q) \<in> \<lbrakk>ts\<rbrakk> \<Longrightarrow> fst w \<noteq> []"
  unfolding wts_to_monoidLTS_def by force

lemma wts_label_d: "(p, ([\<gamma>],d), q) \<in> \<lbrakk>ts\<rbrakk> \<Longrightarrow> ts $ (p,\<gamma>,q) = d"
  unfolding wts_to_monoidLTS_def by blast

lemma wts_label_d': "(p, w, q) \<in> \<lbrakk>ts\<rbrakk> \<Longrightarrow> ts $ (p, hd(fst w), q) = snd w"
  unfolding wts_to_monoidLTS_def by auto

lemma mstar_wts_one: "(p, w, q) \<in> \<lbrakk>ts\<rbrakk>\<^sup>\<odot> \<Longrightarrow> fst w = 1 \<Longrightarrow> snd w = 1"
proof (induct rule: monoid_rtrancl.induct)
  case (monoid_rtrancl_refl a)
  then show ?case by (simp add: one_prod_def)
next
  case (monoid_rtrancl_into_rtrancl p w p' \<gamma> q)
  from \<open>(p', \<gamma>, q) \<in> \<lbrakk>ts\<rbrakk>\<close> have "fst \<gamma> \<noteq> []" using wts_label_not_empty by fast
  then have "fst (w * \<gamma>) \<noteq> []" by simp
  then show ?case
    using monoid_rtrancl_into_rtrancl.prems by (simp add: monoid_rtrancl_into_rtrancl.prems one_list_def)
qed

lemma mstar_wts_empty_one: "(p, ([],d), q) \<in> \<lbrakk>ts\<rbrakk>\<^sup>\<odot> \<Longrightarrow> d = 1"
  using mstar_wts_one by (simp add: one_list_def, fastforce)

lemma wts_to_monoidLTS_weight_exists: 
  assumes "w23 = [\<gamma>]"
  shows "\<exists>dp23. (p2, (w23, dp23), p3) \<in> \<lbrakk>ts1\<rbrakk>"
  using assms wts_to_monoidLTS_def by fastforce

lemma wts_to_monoidLTS_exists_iff:
  "(\<exists>dp23. (p2, (w23, dp23), p3) \<in> \<lbrakk>ts1\<rbrakk>) \<longleftrightarrow> (\<exists>\<gamma>. w23 = [\<gamma>])"
  using wts_label_exist wts_to_monoidLTS_weight_exists by fastforce

\<comment> \<open>Unfold monoid_closure of transitions for 0, 1 and 2 transitions\<close>  
lemma monoid_star_w0:
  assumes "(p, w, q) \<in> \<lbrakk>ts\<rbrakk>\<^sup>\<odot>"
  assumes "fst w = []"
  shows "p = q"
  using assms
proof (induct rule: monoid_rtrancl.induct)
  case (monoid_rtrancl_refl a)
  then show ?case by simp
next
  case (monoid_rtrancl_into_rtrancl p w p' \<gamma> q)
  from \<open>(p', \<gamma>, q) \<in> \<lbrakk>ts\<rbrakk>\<close> have "fst \<gamma> \<noteq> []" using wts_label_not_empty by fast
  then have "fst (w * \<gamma>) \<noteq> []" by simp
  then show ?case using monoid_rtrancl_into_rtrancl.prems by simp
qed

lemma monoid_star_w1:
  assumes "(p, w, q) \<in> \<lbrakk>ts\<rbrakk>\<^sup>\<odot>"
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
  assumes "(p, w, q) \<in> \<lbrakk>ts\<rbrakk>\<^sup>\<odot>"
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
  assumes "(p, (\<gamma>#w, d), q) \<in> \<lbrakk>ts\<rbrakk>\<^sup>\<odot>"
  shows   "\<exists>d' p' d''. d = d' * d'' \<and> (p, ([\<gamma>], d'), p') \<in> \<lbrakk>ts\<rbrakk> \<and> (p', (w, d''), q) \<in> \<lbrakk>ts\<rbrakk>\<^sup>\<odot>"
  using assms monoid_rtrancl_simps_rev[of p "(\<gamma>#w, d)" q "\<lbrakk>ts\<rbrakk>", unfolded mult_prod_def times_list_def one_prod_def one_list_def, simplified]
  apply (simp, safe, simp)
  subgoal for \<gamma>' d' p' w' d''
    apply (rule exI[of _ d'], rule exI[of _ p'], rule exI[of _ d''])
    unfolding wts_to_monoidLTS_def by force
  done

lemma monoid_rtrancl_intros_Cons:
  assumes "(p, ([\<gamma>], d), q1) \<in> \<lbrakk>ts\<rbrakk>"
  assumes "(q1, (w, u), q) \<in> \<lbrakk>ts\<rbrakk>\<^sup>\<odot>"
  shows "(p, (\<gamma> # w, d*u), q) \<in> \<lbrakk>ts\<rbrakk>\<^sup>\<odot>"
  using append_Nil assms(1) assms(2) fst_conv monoid_rtrancl_simps_rev by fastforce

lemma finite_mstar_wts_weights:
  assumes "finite \<lbrakk>ts\<rbrakk>"
  shows   "finite {d. \<exists>p q. (p, (w, d), q) \<in> \<lbrakk>ts\<rbrakk>\<^sup>\<odot>}"
proof (induct w)
  case Nil
  then show ?case
    using finite_subset[of "{d. \<exists>p q. (p, ([], d), q) \<in> \<lbrakk>ts\<rbrakk>\<^sup>\<odot>}" "{1}"]
          mstar_wts_empty_one[of _ _ _ ts] by fast
next
  case (Cons \<gamma> w)
  have f1:"finite {(p, ([\<gamma>], d), q) |p d q. (p, ([\<gamma>], d), q) \<in> \<lbrakk>ts\<rbrakk>}"
    using finite_subset[OF _ assms, of "{(p, ([\<gamma>], d), q)| p d q. (p, ([\<gamma>], d), q) \<in> \<lbrakk>ts\<rbrakk>}"]
    by blast
  have "finite {d. \<exists>p q. (p, ([\<gamma>], d), q) \<in> \<lbrakk>ts\<rbrakk>}"
    unfolding setcompr_eq_image3[of "\<lambda>p d q. d" "\<lambda>p d q. (p, ([\<gamma>], d), q) \<in> \<lbrakk>ts\<rbrakk>", simplified]
    apply (rule finite_imageI)
    using f1[unfolded setcompr_eq_image3[of "\<lambda>p d q. (p, ([\<gamma>], d), q)" "\<lambda>p d q. (p, ([\<gamma>], d), q) \<in> \<lbrakk>ts\<rbrakk>", simplified]]
    apply (rule finite_imageD)
    unfolding inj_on_def by fastforce
  then have "finite {d * d' |d d'. (\<exists>p q. (p, ([\<gamma>], d), q) \<in> \<lbrakk>ts\<rbrakk>) \<and> (\<exists>p q. (p, (w, d'), q) \<in> \<lbrakk>ts\<rbrakk>\<^sup>\<odot>)}"
    using finite_image_set2 Cons by fast
  moreover have "{d. \<exists>p q. (p, (\<gamma> # w, d), q) \<in> \<lbrakk>ts\<rbrakk>\<^sup>\<odot>} 
              \<subseteq> {d * d' |d d'. (\<exists>p q. (p, ([\<gamma>], d), q) \<in> \<lbrakk>ts\<rbrakk>) \<and> (\<exists>p q. (p, (w, d'), q) \<in> \<lbrakk>ts\<rbrakk>\<^sup>\<odot>)}"
    using mstar_wts_cons by fast
  ultimately show ?case using finite_subset by fast
qed

lemma monoid_star_intros_step':
  assumes "(p,w,q) \<in> \<lbrakk>A\<rbrakk>"
  shows "(p,w,q) \<in> \<lbrakk>A\<rbrakk>\<^sup>\<odot>"
  using monoid_rtrancl.intros(2)[of p 1 p "\<lbrakk>A\<rbrakk>" w q] assms
  by (metis monoid_rtrancl.simps mult_1)

lemma monoid_star_intros_step:
  assumes "pwq \<in> \<lbrakk>A\<rbrakk>"
  shows "pwq \<in> \<lbrakk>A\<rbrakk>\<^sup>\<odot>"
  using assms monoid_star_intros_step' by (cases pwq) auto

lemma monoid_rtrancl_wts_to_monoidLTS_cases_rev':
  assumes "(p\<^sub>1, w\<^sub>1\<^sub>3d\<^sub>1\<^sub>3, p\<^sub>3) \<in> \<lbrakk>ts\<rbrakk>\<^sup>\<odot>"
  shows "\<exists>d\<^sub>1\<^sub>3. w\<^sub>1\<^sub>3d\<^sub>1\<^sub>3 = ([],d\<^sub>1\<^sub>3) \<or>
           (\<exists>p\<^sub>2 d\<^sub>2\<^sub>3 \<gamma>\<^sub>1\<^sub>2 w\<^sub>2\<^sub>3 d\<^sub>1\<^sub>2.
               w\<^sub>1\<^sub>3d\<^sub>1\<^sub>3 = (\<gamma>\<^sub>1\<^sub>2#w\<^sub>2\<^sub>3,d\<^sub>1\<^sub>3) \<and>
               (p\<^sub>1, ([\<gamma>\<^sub>1\<^sub>2], d\<^sub>1\<^sub>2), p\<^sub>2) \<in> \<lbrakk>ts\<rbrakk> \<and>
               (p\<^sub>2, (w\<^sub>2\<^sub>3, d\<^sub>2\<^sub>3), p\<^sub>3) \<in> \<lbrakk>ts\<rbrakk>\<^sup>\<odot> \<and>
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
                   (p\<^sub>1, ([\<gamma>\<^sub>1\<^sub>2], d\<^sub>1\<^sub>2), p\<^sub>2) \<in> \<lbrakk>ts\<rbrakk> \<and> 
                   (p\<^sub>2, (w\<^sub>2\<^sub>3, d\<^sub>2\<^sub>3), p\<^sub>3) \<in> \<lbrakk>ts\<rbrakk>\<^sup>\<odot> \<and> 
                   d\<^sub>1\<^sub>3 = d\<^sub>1\<^sub>2 * d\<^sub>2\<^sub>3)"
      using monoid_rtrancl_into_rtrancl.IH by auto
    then obtain p\<^sub>2 d\<^sub>2\<^sub>3 d\<^sub>1\<^sub>2 where p\<^sub>2_d\<^sub>2\<^sub>3_d\<^sub>1\<^sub>2_p:
      "w\<^sub>1\<^sub>3d\<^sub>1\<^sub>3 = (\<gamma>\<^sub>1\<^sub>2 # w\<^sub>2\<^sub>3, d\<^sub>1\<^sub>3)"
      "(p\<^sub>1, ([\<gamma>\<^sub>1\<^sub>2], d\<^sub>1\<^sub>2), p\<^sub>2) \<in> \<lbrakk>ts\<rbrakk>"
      "(p\<^sub>2, (w\<^sub>2\<^sub>3, d\<^sub>2\<^sub>3), p\<^sub>3) \<in> \<lbrakk>ts\<rbrakk>\<^sup>\<odot>"
      "d\<^sub>1\<^sub>3 = d\<^sub>1\<^sub>2 * d\<^sub>2\<^sub>3"
      using d\<^sub>1\<^sub>3_def Cons by auto

    define d\<^sub>2\<^sub>4 where "d\<^sub>2\<^sub>4 = d\<^sub>2\<^sub>3 * d\<^sub>3\<^sub>4"

    have "(p\<^sub>2, (w\<^sub>2\<^sub>4, d\<^sub>2\<^sub>4), p\<^sub>4) \<in> \<lbrakk>ts\<rbrakk>\<^sup>\<odot>"
      using local.Cons monoid_rtrancl_into_rtrancl.hyps(2)  w\<^sub>3\<^sub>4d\<^sub>3\<^sub>4_split d\<^sub>2\<^sub>4_def p\<^sub>2_d\<^sub>2\<^sub>3_d\<^sub>1\<^sub>2_p(3)
        monoid_rtrancl.monoid_rtrancl_into_rtrancl[of p\<^sub>2 "(w\<^sub>2\<^sub>3, d\<^sub>2\<^sub>3)" p\<^sub>3 "\<lbrakk>ts\<rbrakk>" "(w\<^sub>3\<^sub>4, d\<^sub>3\<^sub>4)" p\<^sub>4]
      unfolding w\<^sub>1\<^sub>3_def[symmetric] w\<^sub>2\<^sub>4_def by simp
    moreover
    define d\<^sub>1\<^sub>4 where "d\<^sub>1\<^sub>4 = d\<^sub>1\<^sub>2 * d\<^sub>2\<^sub>4"
    moreover
    have "(p\<^sub>1, ([\<gamma>\<^sub>1\<^sub>2], d\<^sub>1\<^sub>2), p\<^sub>2) \<in> \<lbrakk>ts\<rbrakk>"
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
  assumes "(p, (\<gamma>#w,d), p'') \<in> \<lbrakk>ts\<rbrakk>\<^sup>\<odot>"
  shows "\<exists>d' p' d''.
           (p, ([\<gamma>], d'), p') \<in> \<lbrakk>ts\<rbrakk> \<and>
           (p', (w, d''), p'') \<in> \<lbrakk>ts\<rbrakk>\<^sup>\<odot> \<and>
           d = d' * d''"
  using assms monoid_rtrancl_wts_to_monoidLTS_cases_rev' by fastforce

lemma monoid_rtrancl_wts_to_monoidLTS_append_split:
  assumes "(p\<^sub>1, (w\<^sub>1\<^sub>3@w\<^sub>3\<^sub>4,d\<^sub>1\<^sub>4), p\<^sub>4) \<in> \<lbrakk>A\<rbrakk>\<^sup>\<odot>"
  shows "\<exists>d\<^sub>1\<^sub>3 p\<^sub>3 d\<^sub>3\<^sub>4.
           (p\<^sub>1, (w\<^sub>1\<^sub>3,d\<^sub>1\<^sub>3), p\<^sub>3) \<in> \<lbrakk>A\<rbrakk>\<^sup>\<odot> \<and>
           (p\<^sub>3, (w\<^sub>3\<^sub>4,d\<^sub>3\<^sub>4), p\<^sub>4) \<in> \<lbrakk>A\<rbrakk>\<^sup>\<odot> \<and>
           d\<^sub>1\<^sub>4 = d\<^sub>1\<^sub>3 * d\<^sub>3\<^sub>4"
using assms proof(induction w\<^sub>1\<^sub>3 arbitrary: p\<^sub>1 d\<^sub>1\<^sub>4)
  case Nil
  then show ?case
    by (metis eq_Nil_appendI monoid_rtrancl.monoid_rtrancl_refl mult_1 one_list_def one_prod_def) 
next
  case (Cons \<gamma>\<^sub>1\<^sub>2 w\<^sub>2\<^sub>3)
  then have "\<exists>d\<^sub>1\<^sub>2 p\<^sub>2 d\<^sub>2\<^sub>4. (p\<^sub>1, ([\<gamma>\<^sub>1\<^sub>2],d\<^sub>1\<^sub>2), p\<^sub>2) \<in> \<lbrakk>A\<rbrakk> \<and>
                         (p\<^sub>2, (w\<^sub>2\<^sub>3 @ w\<^sub>3\<^sub>4,d\<^sub>2\<^sub>4), p\<^sub>4) \<in> \<lbrakk>A\<rbrakk>\<^sup>\<odot> \<and>
                         d\<^sub>1\<^sub>4 = d\<^sub>1\<^sub>2 * d\<^sub>2\<^sub>4"
    using monoid_rtrancl_wts_to_monoidLTS_cases_rev by fastforce

  then obtain p\<^sub>2 d\<^sub>1\<^sub>2 d\<^sub>2\<^sub>4 where q_du0_du1_p:
    "(p\<^sub>1, ([\<gamma>\<^sub>1\<^sub>2],d\<^sub>1\<^sub>2), p\<^sub>2) \<in> \<lbrakk>A\<rbrakk>" 
    "(p\<^sub>2, (w\<^sub>2\<^sub>3 @ w\<^sub>3\<^sub>4,d\<^sub>2\<^sub>4), p\<^sub>4) \<in> \<lbrakk>A\<rbrakk>\<^sup>\<odot>" 
    "d\<^sub>1\<^sub>4 = d\<^sub>1\<^sub>2 * d\<^sub>2\<^sub>4"
    by auto

  have "\<exists>d\<^sub>2\<^sub>3 p\<^sub>3 d\<^sub>3\<^sub>4. (p\<^sub>2, (w\<^sub>2\<^sub>3, d\<^sub>2\<^sub>3), p\<^sub>3) \<in> \<lbrakk>A\<rbrakk>\<^sup>\<odot> \<and> 
                     (p\<^sub>3, (w\<^sub>3\<^sub>4, d\<^sub>3\<^sub>4), p\<^sub>4) \<in> \<lbrakk>A\<rbrakk>\<^sup>\<odot> \<and> 
                     d\<^sub>2\<^sub>4 = d\<^sub>2\<^sub>3 * d\<^sub>3\<^sub>4"
     using Cons.IH[OF q_du0_du1_p(2)] .
  then obtain d\<^sub>2\<^sub>3 p\<^sub>3 d\<^sub>3\<^sub>4 where
    "(p\<^sub>2, (w\<^sub>2\<^sub>3,d\<^sub>2\<^sub>3), p\<^sub>3) \<in> \<lbrakk>A\<rbrakk>\<^sup>\<odot>"
    "(p\<^sub>3, (w\<^sub>3\<^sub>4,d\<^sub>3\<^sub>4), p\<^sub>4) \<in> \<lbrakk>A\<rbrakk>\<^sup>\<odot>" 
    "d\<^sub>2\<^sub>4 = d\<^sub>2\<^sub>3 * d\<^sub>3\<^sub>4"
    by auto
  from this(1) have "(p\<^sub>1, (\<gamma>\<^sub>1\<^sub>2 # w\<^sub>2\<^sub>3, d\<^sub>1\<^sub>2 * d\<^sub>2\<^sub>3), p\<^sub>3) \<in> \<lbrakk>A\<rbrakk>\<^sup>\<odot>"
    using q_du0_du1_p(1) monoid_rtrancl_into_rtrancl_rev[of p\<^sub>1 "([\<gamma>\<^sub>1\<^sub>2], d\<^sub>1\<^sub>2)" p\<^sub>2 "\<lbrakk>A\<rbrakk>" "(w\<^sub>2\<^sub>3, d\<^sub>2\<^sub>3)" p\<^sub>3]
    by simp
  then show ?case
    using  \<open>(p\<^sub>3, (w\<^sub>3\<^sub>4, d\<^sub>3\<^sub>4), p\<^sub>4) \<in> \<lbrakk>A\<rbrakk>\<^sup>\<odot>\<close> \<open>d\<^sub>2\<^sub>4 = d\<^sub>2\<^sub>3 * d\<^sub>3\<^sub>4\<close> q_du0_du1_p(3) 
    by (metis (no_types, lifting) mult.assoc)   
qed

lemma merge_edge_and_monoid_rtrancl_wts_to_monoidLTS:
  assumes "A $ (p\<^sub>1, \<gamma>\<^sub>1\<^sub>2, p\<^sub>2) \<le> D\<^sub>1\<^sub>2"
  assumes "(p\<^sub>2, (w\<^sub>2\<^sub>3, d\<^sub>2\<^sub>3), p\<^sub>3) \<in> \<lbrakk>A\<rbrakk>\<^sup>\<odot>"
  shows "\<exists>D\<^sub>1\<^sub>3. (p\<^sub>1, (\<gamma>\<^sub>1\<^sub>2 # w\<^sub>2\<^sub>3, D\<^sub>1\<^sub>3), p\<^sub>3) \<in> \<lbrakk>A\<rbrakk>\<^sup>\<odot> \<and> D\<^sub>1\<^sub>3 \<le> D\<^sub>1\<^sub>2 * d\<^sub>2\<^sub>3"
proof -
  define d\<^sub>1\<^sub>2 where "d\<^sub>1\<^sub>2 = A $ (p\<^sub>1, \<gamma>\<^sub>1\<^sub>2, p\<^sub>2)"

  have p\<^sub>1_to_p\<^sub>2: "(p\<^sub>1, ([\<gamma>\<^sub>1\<^sub>2], d\<^sub>1\<^sub>2), p\<^sub>2) \<in> \<lbrakk>A\<rbrakk>"
    using assms(1) d\<^sub>1\<^sub>2_def wts_to_monoidLTS_def by fastforce

  have "(p\<^sub>1, ([\<gamma>\<^sub>1\<^sub>2], d\<^sub>1\<^sub>2) * (w\<^sub>2\<^sub>3, d\<^sub>2\<^sub>3), p\<^sub>3) \<in> \<lbrakk>A\<rbrakk>\<^sup>\<odot>"
    using monoid_rtrancl_into_rtrancl_rev[OF _ assms(2), of p\<^sub>1 "([\<gamma>\<^sub>1\<^sub>2],_)", OF p\<^sub>1_to_p\<^sub>2] .
  then have "(p\<^sub>1, (\<gamma>\<^sub>1\<^sub>2#w\<^sub>2\<^sub>3, d\<^sub>1\<^sub>2 * d\<^sub>2\<^sub>3), p\<^sub>3) \<in> \<lbrakk>A\<rbrakk>\<^sup>\<odot>"
    by simp
  then show ?thesis
    using assms(1) d\<^sub>1\<^sub>2_def idempotent_semiring_ord_class.mult_isol_var by blast
qed

lemma wts_to_monoidLTS_induct[consumes 1, case_names base step]:
  assumes "(p, (w, d), p') \<in> \<lbrakk>ts\<rbrakk>\<^sup>\<odot>"
  assumes "(\<And>p. P p [] 1 p)"
  assumes "(\<And>p w d p' w' d' p''. 
             (p, (w, d), p') \<in> \<lbrakk>ts\<rbrakk>\<^sup>\<odot> \<Longrightarrow> 
             P p w d p' \<Longrightarrow> 
            (p', (w', d'), p'') \<in> \<lbrakk>ts\<rbrakk> \<Longrightarrow> 
            P p (w @ w') (d * d') p'')"
  shows "P p w d p'"
  using monoid_rtrancl_pair_weight_induct[of p w d p' "\<lbrakk>ts\<rbrakk>" P] assms
  by (simp add: one_list_def)

lemma wts_to_monoidLTS_pair_induct[consumes 1, case_names base step]:
  assumes "((p,q), (w, d), (p',q')) \<in> \<lbrakk>ts\<rbrakk>\<^sup>\<odot>"
  assumes "(\<And>p q. P p q [] 1 p q)"
  assumes "(\<And>p q w d p' q' w' d' p'' q''. 
             ((p,q), (w, d), (p',q')) \<in> \<lbrakk>ts\<rbrakk>\<^sup>\<odot> \<Longrightarrow> 
             P p q w d p' q' \<Longrightarrow> 
            ((p',q'), (w', d'), (p'',q'')) \<in> \<lbrakk>ts\<rbrakk> \<Longrightarrow> 
            P p q (w @ w') (d * d') p'' q'')"
  shows "P p q w d p' q'"
  using wts_to_monoidLTS_induct[of
      "(p,q)" w d "(p',q')"
      ts
      "\<lambda>pq y z p'q'. P (fst pq) (snd pq) y z (fst p'q') (snd p'q')"]
    assms by auto

lemma wts_to_monoidLTS_induct_reverse:
  assumes "(p, (w,d), p') \<in> \<lbrakk>ts\<rbrakk>\<^sup>\<odot>"
  assumes "(\<And>p. P p [] 1 p)"
  assumes "(\<And>p w d p' w' d' p''.
             (p, (w,d), p') \<in> \<lbrakk>ts\<rbrakk> \<Longrightarrow> 
             P p' w' d' p'' \<Longrightarrow>
             (p', (w',d'), p'') \<in> \<lbrakk>ts\<rbrakk>\<^sup>\<odot> \<Longrightarrow>
             P p (w @ w') (d*d') p'')"
  shows "P p w d p'"
  using assms monoid_rtrancl_induct_rev[of p "(w,d)" p' "\<lbrakk>ts\<rbrakk>" "\<lambda>p wd p'. P p (fst wd) (snd wd) p'"]
  by (simp add: one_list_def one_prod_def)

lemma monoid_star_nonempty:
  assumes "(p, w, p') \<in> \<lbrakk>ts\<rbrakk>\<^sup>\<odot>"
  assumes "fst w \<noteq> []"
  shows "\<exists>pi d1 d2. (snd w) = d1 * d2 \<and> 
                    (pi, (tl (fst w), d2), p') \<in> \<lbrakk>ts\<rbrakk>\<^sup>\<odot> \<and> 
                    (p, ([hd (fst w)], d1), pi) \<in> \<lbrakk>ts\<rbrakk>"
  by (metis assms list.collapse monoid_rtrancl_wts_to_monoidLTS_cases_rev surjective_pairing)

\<comment> \<open>A weighted automaton is initialized with weights 1 (neutral element along paths) on existing transitions, 
    and a default weight of 0 (neutral element for combining paths) for non-existing transitions.\<close>
definition ts_to_wts :: "('state, 'label) transition set \<Rightarrow> ('state, 'label, 'weight::bounded_dioid) w_transitions" where
  "ts_to_wts ts = update_wts (K$ 0) {(t,1) | t. t \<in> ts}"

definition wts_to_ts :: "('state, 'label, 'weight::bounded_dioid) w_transitions \<Rightarrow> ('state, 'label) transition set" where
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
  shows "(p, (\<gamma>, 1), q) \<in> \<lbrakk>ts_to_wts ts\<rbrakk>\<^sup>\<odot>"
  apply (induction rule: LTS.trans_star.induct[OF assms(1)])
  apply (simp add: monoid_rtrancl_wts_to_monoidLTS_refl)
  by (metis ts_to_wts_1_if_member assms(2) monoid_rtrancl_intros_Cons mult.right_neutral wts_label_d wts_to_monoidLTS_weight_exists)

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

\<comment> \<open>Weighted Intersection\<close>
definition w_inters :: "('state, 'label::finite, 'weight::bounded_dioid) w_transitions \<Rightarrow> ('state, 'label, 'weight) w_transitions 
                     \<Rightarrow> (('state \<times> 'state), 'label, 'weight) w_transitions" ("_\<inter>\<^sub>w_" [1000,1000] 1000) where
  "ts\<^sub>1\<inter>\<^sub>wts\<^sub>2 = (case_prod (*)) \<circ>$ (pair_weight ts\<^sub>1 ts\<^sub>2)"

lemma finfun_apply_w_inters_transition:
  fixes p\<^sub>1::"'state::finite"
  fixes q\<^sub>1::"'state::finite"
  shows "ts\<^sub>1\<inter>\<^sub>wts\<^sub>2 $ ((p\<^sub>1,q\<^sub>1),\<gamma>,(p\<^sub>2,q\<^sub>2)) = (ts\<^sub>1 $ (p\<^sub>1,\<gamma>,p\<^sub>2) * ts\<^sub>2 $ (q\<^sub>1,\<gamma>,q\<^sub>2))"
  by (auto simp add: fst_weight_apply snd_weight_apply finfun_apply_pair_weight_transition w_inters_def)

lemma finfun_apply_w_inters:
  fixes ts\<^sub>1::"('state::finite, 'label::finite, 'weight::bounded_dioid) w_transitions"
  fixes ts\<^sub>2::"('state::finite, 'label, 'weight) w_transitions"
  shows "(($) (ts\<^sub>1\<inter>\<^sub>wts\<^sub>2)) = (\<lambda>t. (ts\<^sub>1 $ (fst_trans t) * ts\<^sub>2 $ (snd_trans t)))"
proof (rule HOL.ext)
  fix t
  show "ts\<^sub>1\<inter>\<^sub>wts\<^sub>2 $ t = ts\<^sub>1 $ (fst_trans t) * ts\<^sub>2 $ (snd_trans t)"
    using finfun_apply_w_inters_transition by (cases t) force
qed

lemma w_inters_complete_transition_finfun_apply:
  fixes p::"'state::finite"
  fixes p'::"'state::finite"
  assumes "A $ (p, y, q) = d"
  assumes "A' $ (p', y, q') = d'"
  shows "A\<inter>\<^sub>wA' $ ((p,p'), y, (q,q')) = d * d'"
  using assms finfun_apply_w_inters_transition by auto

lemma w_inters_complete_transition:
  fixes p::"'state::finite"
  fixes q::"'state::finite"
  assumes "(p, ([\<alpha>], d\<^sub>p), p') \<in> \<lbrakk>ts\<^sub>1\<rbrakk>"
  assumes "(q, ([\<alpha>], d\<^sub>q), q') \<in> \<lbrakk>ts\<^sub>2\<rbrakk>"
  shows "((p, q), ([\<alpha>], d\<^sub>p * d\<^sub>q), (p', q')) \<in> \<lbrakk>ts\<^sub>1\<inter>\<^sub>wts\<^sub>2\<rbrakk>"
  using assms finfun_apply_w_inters_transition[of ts\<^sub>1 ts\<^sub>2 p q \<alpha> p' q']
  unfolding wts_to_monoidLTS_def by auto

lemma w_inters_sound_transition:
  fixes ts\<^sub>1::"('state::finite, 'label::finite, 'weight::bounded_dioid) w_transitions"
  fixes ts\<^sub>2::"('state::finite, 'label, 'weight) w_transitions"
  assumes "((p, q), (w, d), p', q') \<in> \<lbrakk>ts\<^sub>1\<inter>\<^sub>wts\<^sub>2\<rbrakk>"
  obtains d\<^sub>p d\<^sub>q where
    "(p, (w, d\<^sub>p), p') \<in> \<lbrakk>ts\<^sub>1\<rbrakk>"
    "(q, (w, d\<^sub>q), q') \<in> \<lbrakk>ts\<^sub>2\<rbrakk>"
    "d = d\<^sub>p * d\<^sub>q"
proof -
  have "\<exists>d\<^sub>p d\<^sub>q. ts\<^sub>1 $ (p, (hd w), p') = d\<^sub>p \<and>
                    ts\<^sub>2 $ (q, (hd w), q') = d\<^sub>q \<and>
                    d = d\<^sub>p * d\<^sub>q"
    using assms finfun_apply_w_inters_transition wts_label_d' by fastforce
  then show ?thesis
    by (metis wts_to_monoidLTS_exists_iff assms list.sel(1) that wts_label_d)
qed

definition binary_aut :: "('state, 'label, 'weight::bounded_dioid) w_transitions \<Rightarrow> bool" where
  "binary_aut ts \<longleftrightarrow> (\<forall>p\<^sub>1 w p\<^sub>2. ts $ (p\<^sub>1, w, p\<^sub>2) = 1 \<or> ts $ (p\<^sub>1, w, p\<^sub>2) = 0)"

lemma ts_to_wts_bin:
  fixes ts :: "('s, 'l) transition set"
  assumes "finite ts"
  shows "binary_aut (ts_to_wts ts)"
  unfolding binary_aut_def using assms ts_to_wts_1_or_0 by metis

lemma binary_aut_monoid_rtrancl_wts_to_monoidLTS_cases_rev:
  assumes "binary_aut ts"
  assumes "(p\<^sub>1, (\<alpha>#w,1), p\<^sub>2) \<in> \<lbrakk>ts\<rbrakk>\<^sup>\<odot>"
  shows "\<exists>p'. (p\<^sub>1, ([\<alpha>],1), p') \<in> \<lbrakk>ts\<rbrakk> \<and> (p', (w,1), p\<^sub>2) \<in> \<lbrakk>ts\<rbrakk>\<^sup>\<odot>"
  using assms
proof (induction w arbitrary: \<alpha> p\<^sub>1)
  case Nil
  then show ?case
    by (metis monoid_rtrancl_wts_to_monoidLTS_cases_rev mstar_wts_empty_one mult.right_neutral)
next
  case (Cons \<alpha>' w)
  obtain p' d\<^sub>1 d\<^sub>2 where p'_p:
    "(p\<^sub>1, ([\<alpha>], d\<^sub>1), p') \<in> \<lbrakk>ts\<rbrakk>"
    "(p', (\<alpha>'#w, d\<^sub>2), p\<^sub>2) \<in> \<lbrakk>ts\<rbrakk>\<^sup>\<odot>"
    "1 = d\<^sub>1 * d\<^sub>2"
    using Cons(3) by (meson monoid_rtrancl_wts_to_monoidLTS_cases_rev)
  have d1: "d\<^sub>1 = 1"
    using Cons.prems(1) p'_p(1,3) unfolding binary_aut_def by (metis mult_zero_left wts_label_d)
  then have "d\<^sub>2 = 1"
    using p'_p(3) by force
  then have "(p', (\<alpha>' # w, 1), p\<^sub>2) \<in> \<lbrakk>ts\<rbrakk>\<^sup>\<odot>"
    using p'_p(2) by force
  then show ?case
    using p'_p(1) d1 by (meson wts_label_d) 
qed

lemma binary_aut_transition_binary:
  assumes "(p\<^sub>1, (w,d), p\<^sub>2) \<in> \<lbrakk>ts\<rbrakk>"
  assumes "binary_aut ts"
  shows "d = 1 \<or> d = 0"
  by (metis assms(1) assms(2) binary_aut_def snd_conv wts_label_d')

lemma binary_aut_path_binary:
  assumes "(p\<^sub>1, (w,d), p\<^sub>2) \<in> \<lbrakk>ts\<rbrakk>\<^sup>\<odot>"
  assumes "binary_aut ts"
  shows "d = 1 \<or> d = 0"
  using assms 
  by (induction rule: wts_to_monoidLTS_induct)
     (auto dest: binary_aut_transition_binary)

lemma w_inters_complete_exi:
  fixes ts\<^sub>1::"('state::finite, 'label::finite, 'weight::bounded_dioid) w_transitions"
  fixes ts\<^sub>2::"('state::finite, 'label, 'weight) w_transitions"
  assumes "(p\<^sub>1, (w,d\<^sub>p), p\<^sub>2) \<in> \<lbrakk>ts\<^sub>1\<rbrakk>\<^sup>\<odot>"
  assumes "(q\<^sub>1, (w,d\<^sub>q), q\<^sub>2) \<in> \<lbrakk>ts\<^sub>2\<rbrakk>\<^sup>\<odot>"
  shows "\<exists>d. ((p\<^sub>1,q\<^sub>1), (w,d), (p\<^sub>2,q\<^sub>2)) \<in> \<lbrakk>ts\<^sub>1\<inter>\<^sub>wts\<^sub>2\<rbrakk>\<^sup>\<odot>"
  using assms 
proof (induction w arbitrary: p\<^sub>1 q\<^sub>1 d\<^sub>p d\<^sub>q)
  case Nil
  then show ?case
    by (metis fst_conv monoid_rtrancl.monoid_rtrancl_refl monoid_star_w0 one_list_def one_prod_def)
next
  case (Cons \<gamma> w)
  obtain p' q' dp1 dp2 dq1 dq2 where pq'_p:
    "(p\<^sub>1, ([\<gamma>], dp1), p') \<in> \<lbrakk>ts\<^sub>1\<rbrakk>" "(p', (w, dp2), p\<^sub>2) \<in> \<lbrakk>ts\<^sub>1\<rbrakk>\<^sup>\<odot>"
    "(q\<^sub>1, ([\<gamma>], dq1), q') \<in> \<lbrakk>ts\<^sub>2\<rbrakk>" "(q', (w, dq2), q\<^sub>2) \<in> \<lbrakk>ts\<^sub>2\<rbrakk>\<^sup>\<odot>"
    by (meson Cons.prems(1) Cons.prems(2) monoid_rtrancl_wts_to_monoidLTS_cases_rev)
  then have "ts\<^sub>1 $ (p\<^sub>1, \<gamma>, p') = dp1" "ts\<^sub>2 $ (q\<^sub>1, \<gamma>, q') = dq1"
    by (simp add: wts_label_d)+
  then have "ts\<^sub>1\<inter>\<^sub>wts\<^sub>2 $ ((p\<^sub>1,q\<^sub>1), \<gamma>, (p',q')) = dp1 * dq1"
    using finfun_apply_w_inters_transition by blast
  then have pq1_pq1: "((p\<^sub>1,q\<^sub>1), ([\<gamma>], dp1 * dq1), (p',q')) \<in> \<lbrakk>ts\<^sub>1\<inter>\<^sub>wts\<^sub>2\<rbrakk>"
    by (simp add: wts_to_monoidLTS_def)
  from pq'_p Cons(1) obtain d2 where d2_p:
    "((p',q'), (w, d2), (p\<^sub>2,q\<^sub>2)) \<in> \<lbrakk>ts\<^sub>1\<inter>\<^sub>wts\<^sub>2\<rbrakk>\<^sup>\<odot>"
    by blast
  then have "((p\<^sub>1,q\<^sub>1), (\<gamma>#w, (dp1 * dq1)*d2), (p\<^sub>2,q\<^sub>2)) \<in> \<lbrakk>ts\<^sub>1\<inter>\<^sub>wts\<^sub>2\<rbrakk>\<^sup>\<odot>"
    using monoid_rtrancl_into_rtrancl_rev[of "(p\<^sub>1,q\<^sub>1)" "([\<gamma>],dp1 * dq1)" "(p',q')" "\<lbrakk>ts\<^sub>1\<inter>\<^sub>wts\<^sub>2\<rbrakk>" "(w,d2)" "(p\<^sub>2,q\<^sub>2)"]
    using pq1_pq1 by auto
  then show ?case
    by auto
qed

lemma w_inters_complete_1:
  fixes p\<^sub>1::"'state::finite"
  fixes q\<^sub>1::"'state::finite"
  assumes "(p\<^sub>1, (w,1), p\<^sub>2) \<in> \<lbrakk>ts\<^sub>1\<rbrakk>\<^sup>\<odot>"
  assumes "(q\<^sub>1, (w,d), q\<^sub>2) \<in> \<lbrakk>ts\<^sub>2\<rbrakk>\<^sup>\<odot>"
  assumes "binary_aut ts\<^sub>1"
  shows "((p\<^sub>1,q\<^sub>1), (w,d), (p\<^sub>2,q\<^sub>2)) \<in> \<lbrakk>ts\<^sub>1\<inter>\<^sub>wts\<^sub>2\<rbrakk>\<^sup>\<odot>"
  using assms(1,2)
proof (induction w arbitrary: p\<^sub>1 q\<^sub>1 d)
  case (Cons \<alpha> w')
  obtain p' where p'_p: 
    "(p\<^sub>1, ([\<alpha>],1), p') \<in> \<lbrakk>ts\<^sub>1\<rbrakk>"
    "(p', (w',1), p\<^sub>2) \<in> \<lbrakk>ts\<^sub>1\<rbrakk>\<^sup>\<odot>"
    using Cons(2) by (meson assms(3) binary_aut_monoid_rtrancl_wts_to_monoidLTS_cases_rev) 
  obtain q' dq\<^sub>1q' dq'q\<^sub>2 where q'_p: 
    "(q\<^sub>1, ([\<alpha>],dq\<^sub>1q'), q') \<in> \<lbrakk>ts\<^sub>2\<rbrakk>"
    "(q', (w',dq'q\<^sub>2), q\<^sub>2) \<in> \<lbrakk>ts\<^sub>2\<rbrakk>\<^sup>\<odot>"
    "d = dq\<^sub>1q' * dq'q\<^sub>2"
    using Cons(3) using monoid_rtrancl_wts_to_monoidLTS_cases_rev[of q\<^sub>1 \<alpha> w' d q\<^sub>2 ts\<^sub>2] by meson
  have ind: "((p', q'), (w', dq'q\<^sub>2), (p\<^sub>2, q\<^sub>2)) \<in> \<lbrakk>ts\<^sub>1\<inter>\<^sub>wts\<^sub>2\<rbrakk>\<^sup>\<odot>"
    by (simp add: Cons.IH p'_p(2) q'_p(2))
  moreover
  have "((p\<^sub>1, q\<^sub>1), ([\<alpha>], dq\<^sub>1q'), (p', q')) \<in> \<lbrakk>ts\<^sub>1\<inter>\<^sub>wts\<^sub>2\<rbrakk>"
    using p'_p q'_p w_inters_complete_transition by (metis mult_1)
  ultimately
  have "((p\<^sub>1, q\<^sub>1), (\<alpha>#w', dq\<^sub>1q' * dq'q\<^sub>2), (p\<^sub>2, q\<^sub>2)) \<in> \<lbrakk>ts\<^sub>1\<inter>\<^sub>wts\<^sub>2\<rbrakk>\<^sup>\<odot>"
    using monoid_rtrancl_into_rtrancl_rev[of "(p\<^sub>1, q\<^sub>1)" " ([\<alpha>], dq\<^sub>1q')" "(p', q')" "\<lbrakk>ts\<^sub>1\<inter>\<^sub>wts\<^sub>2\<rbrakk>" "(w', dq'q\<^sub>2)" "(p\<^sub>2, q\<^sub>2)"]
    by simp
  then show ?case
    by (simp add: q'_p)
next
  case Nil
  then show ?case
    by (metis fst_conv monoid_rtrancl.monoid_rtrancl_refl monoid_star_w0 mstar_wts_empty_one one_list_def one_prod_def)
qed

lemma w_inters_complete_0:
  fixes ts\<^sub>1::"('state::finite, 'label::finite, 'weight::bounded_dioid) w_transitions"
  fixes ts\<^sub>2::"('state::finite, 'label, 'weight) w_transitions"
  assumes "(p\<^sub>1, (w,0), p\<^sub>2) \<in> \<lbrakk>ts\<^sub>1\<rbrakk>\<^sup>\<odot>"
  assumes "(q\<^sub>1, (w,d), q\<^sub>2) \<in> \<lbrakk>ts\<^sub>2\<rbrakk>\<^sup>\<odot>"
  assumes "binary_aut ts\<^sub>1"
  shows "((p\<^sub>1,q\<^sub>1), (w,0), (p\<^sub>2,q\<^sub>2)) \<in> \<lbrakk>ts\<^sub>1\<inter>\<^sub>wts\<^sub>2\<rbrakk>\<^sup>\<odot>"
  using assms(1,2)
proof (induction w arbitrary: p\<^sub>1 q\<^sub>1 d)
  case (Cons \<alpha> w')
  then have "(\<exists>p' d'. (p\<^sub>1, ([\<alpha>], 0), p') \<in> \<lbrakk>ts\<^sub>1\<rbrakk> \<and> (p', (w',d'), p\<^sub>2) \<in> \<lbrakk>ts\<^sub>1\<rbrakk>\<^sup>\<odot>) 
           \<or> (\<exists>p' d'. (p\<^sub>1, ([\<alpha>], d'), p') \<in> \<lbrakk>ts\<^sub>1\<rbrakk> \<and> (p', (w',0), p\<^sub>2) \<in> \<lbrakk>ts\<^sub>1\<rbrakk>\<^sup>\<odot>)"
    by (metis (no_types, lifting) assms(3) monoid_rtrancl_wts_to_monoidLTS_cases_rev mult_1 wts_label_d binary_aut_def)
  then show ?case
  proof 
    assume "(\<exists>p' d'. (p\<^sub>1, ([\<alpha>], 0), p') \<in> \<lbrakk>ts\<^sub>1\<rbrakk> \<and> (p', (w',d'), p\<^sub>2) \<in> \<lbrakk>ts\<^sub>1\<rbrakk>\<^sup>\<odot>)"
    then obtain p' d' where p'_p:
      "(p\<^sub>1, ([\<alpha>], 0), p') \<in> \<lbrakk>ts\<^sub>1\<rbrakk>"
      "(p', (w',d'), p\<^sub>2) \<in> \<lbrakk>ts\<^sub>1\<rbrakk>\<^sup>\<odot>"
      by auto
    moreover
    obtain q' d\<^sub>q\<^sub>1 d\<^sub>q\<^sub>2 where q'_p:
      "(q\<^sub>1, ([\<alpha>], d\<^sub>q\<^sub>1), q') \<in> \<lbrakk>ts\<^sub>2\<rbrakk>" 
      "(q', (w', d\<^sub>q\<^sub>2), q\<^sub>2) \<in> \<lbrakk>ts\<^sub>2\<rbrakk>\<^sup>\<odot>"
      using Cons(3) monoid_rtrancl_wts_to_monoidLTS_cases_rev by fastforce
    ultimately
    have pq1_pq': "((p\<^sub>1,q\<^sub>1), ([\<alpha>], 0), (p',q')) \<in> \<lbrakk>ts\<^sub>1\<inter>\<^sub>wts\<^sub>2\<rbrakk>"
      using w_inters_complete_transition by fastforce

    obtain d\<^sub>2 where pq'_pq2: "((p',q'), (w', d\<^sub>2), (p\<^sub>2,q\<^sub>2)) \<in> \<lbrakk>ts\<^sub>1\<inter>\<^sub>wts\<^sub>2\<rbrakk>\<^sup>\<odot>"
      using w_inters_complete_exi[of p' w' _ p\<^sub>2 ts\<^sub>1 q' _ q\<^sub>2 ts\<^sub>2] Cons p'_p(2)
        q'_p(2) monoid_star_intros_step by blast
    show ?thesis
      using pq1_pq' pq'_pq2 monoid_rtrancl_into_rtrancl_rev[of "(p\<^sub>1, q\<^sub>1)" "([\<alpha>],0)" "(p', q')" "\<lbrakk>ts\<^sub>1\<inter>\<^sub>wts\<^sub>2\<rbrakk>" "(w', d\<^sub>2)" "(p\<^sub>2, q\<^sub>2)"]
      by simp
  next
    assume "(\<exists>p' d. (p\<^sub>1, ([\<alpha>], d), p') \<in> \<lbrakk>ts\<^sub>1\<rbrakk> \<and> (p', (w',0), p\<^sub>2) \<in> \<lbrakk>ts\<^sub>1\<rbrakk>\<^sup>\<odot>)"
    then obtain p' d' where p'_p:
      "(p\<^sub>1, ([\<alpha>], d'), p') \<in> \<lbrakk>ts\<^sub>1\<rbrakk>"
      "(p', (w',0), p\<^sub>2) \<in> \<lbrakk>ts\<^sub>1\<rbrakk>\<^sup>\<odot>"     
      by auto
    obtain q' X Y where q'_p:
      "(q\<^sub>1, ([\<alpha>], X), q') \<in> \<lbrakk>ts\<^sub>2\<rbrakk>"
      "(q', (w', Y), q\<^sub>2) \<in> \<lbrakk>ts\<^sub>2\<rbrakk>\<^sup>\<odot>"
      using Cons(3) monoid_rtrancl_wts_to_monoidLTS_cases_rev by fastforce
    obtain d\<^sub>1 where d1_p: "((p\<^sub>1,q\<^sub>1), ([\<alpha>], d\<^sub>1), (p',q')) \<in> \<lbrakk>ts\<^sub>1\<inter>\<^sub>wts\<^sub>2\<rbrakk>"
      using wts_to_monoidLTS_def by fastforce
    have "((p',q'), (w', 0), (p\<^sub>2,q\<^sub>2)) \<in> \<lbrakk>ts\<^sub>1\<inter>\<^sub>wts\<^sub>2\<rbrakk>\<^sup>\<odot>"
      using Cons(1)[of p' q'] p'_p(2) q'_p by blast
    then show ?thesis
      using d1_p monoid_rtrancl_into_rtrancl_rev[of "(p\<^sub>1, q\<^sub>1)" "([\<alpha>],d\<^sub>1)" "(p', q')" "\<lbrakk>ts\<^sub>1\<inter>\<^sub>wts\<^sub>2\<rbrakk>" "(w',0)" "(p\<^sub>2, q\<^sub>2)"]
      by simp
  qed
next
  case Nil
  then show ?case
    by (metis fst_conv monoid_rtrancl.monoid_rtrancl_refl monoid_star_w0 mstar_wts_empty_one one_list_def one_prod_def)
qed

lemma w_inters_sound_exi_fst:
  assumes "((p\<^sub>1,q\<^sub>1), (w,d), (p\<^sub>2,q\<^sub>2)) \<in> \<lbrakk>ts\<^sub>1\<inter>\<^sub>wts\<^sub>2\<rbrakk>\<^sup>\<odot>"
  shows "\<exists>d'. (p\<^sub>1, (w,d'), p\<^sub>2) \<in> \<lbrakk>ts\<^sub>1\<rbrakk>\<^sup>\<odot>"
  using assms 
proof (induction rule: wts_to_monoidLTS_pair_induct)
  case (base p q)
  then show ?case
    using monoid_rtrancl_wts_to_monoidLTS_refl by force
next
  case (step p\<^sub>1 q\<^sub>1 w\<^sub>1\<^sub>2 d\<^sub>1\<^sub>2 p\<^sub>2 q\<^sub>2 w\<^sub>2\<^sub>3 d\<^sub>2\<^sub>3 p\<^sub>3 q\<^sub>3)
  then have "\<exists>d\<^sub>2. (p\<^sub>2, (w\<^sub>2\<^sub>3,d\<^sub>2), p\<^sub>3) \<in> \<lbrakk>ts\<^sub>1\<rbrakk>"
    using wts_label_exist wts_to_monoidLTS_def by fastforce
  then show ?case
    using step(3) monoid_rtrancl.monoid_rtrancl_into_rtrancl[of p\<^sub>1 "(w\<^sub>1\<^sub>2, _)" p\<^sub>2 "\<lbrakk>ts\<^sub>1\<rbrakk>" "(w\<^sub>2\<^sub>3, _)" p\<^sub>3]
    by auto
qed

lemma w_inters_sound_non_zero_fst:
  fixes ts\<^sub>1::"('state::finite, 'label::finite, 'weight::bounded_dioid) w_transitions"
  fixes ts\<^sub>2::"('state::finite, 'label, 'weight) w_transitions"
  assumes "((p\<^sub>1,q\<^sub>1), (w,d), (p\<^sub>2,q\<^sub>2)) \<in> \<lbrakk>ts\<^sub>1\<inter>\<^sub>wts\<^sub>2\<rbrakk>\<^sup>\<odot>"
  assumes "binary_aut ts\<^sub>1"
  assumes "d\<noteq>0"
  shows "(p\<^sub>1, (w,1), p\<^sub>2) \<in> \<lbrakk>ts\<^sub>1\<rbrakk>\<^sup>\<odot>"
  using assms 
proof (induction rule: wts_to_monoidLTS_pair_induct)
  case (base p q)
  then show ?case
    by (simp add: monoid_rtrancl_wts_to_monoidLTS_refl)
next
  case (step p\<^sub>1 q\<^sub>1 w\<^sub>1\<^sub>2 d\<^sub>1\<^sub>2 p\<^sub>2 q\<^sub>2 w\<^sub>2\<^sub>3 d\<^sub>2\<^sub>3 p\<^sub>3 q\<^sub>3)
    
  have d12_non0: "d\<^sub>1\<^sub>2 \<noteq> 0"
    using step.prems(2) by force
  have d23_non0: "d\<^sub>2\<^sub>3 \<noteq> 0"
    using step.prems(2) by force

  then have "(p\<^sub>1, (w\<^sub>1\<^sub>2, 1), p\<^sub>2) \<in> \<lbrakk>ts\<^sub>1\<rbrakk>\<^sup>\<odot>"
    using d12_non0 step.IH step.prems(1) by blast
  moreover
  have "ts\<^sub>1\<inter>\<^sub>wts\<^sub>2 $ ((p\<^sub>2, q\<^sub>2), hd w\<^sub>2\<^sub>3, (p\<^sub>3, q\<^sub>3)) = d\<^sub>2\<^sub>3"
    using wts_label_d' step.hyps(2) by fastforce
  then obtain d\<^sub>2\<^sub>3\<^sub>p d\<^sub>2\<^sub>3\<^sub>q where
    "(p\<^sub>2, (w\<^sub>2\<^sub>3, d\<^sub>2\<^sub>3\<^sub>p), p\<^sub>3) \<in> \<lbrakk>ts\<^sub>1\<rbrakk>"
    "(q\<^sub>2, (w\<^sub>2\<^sub>3, d\<^sub>2\<^sub>3\<^sub>q), q\<^sub>3) \<in> \<lbrakk>ts\<^sub>2\<rbrakk>"
    "d\<^sub>2\<^sub>3\<^sub>p * d\<^sub>2\<^sub>3\<^sub>q = d\<^sub>2\<^sub>3"
    by (metis w_inters_sound_transition step.hyps(2))
  then have "(p\<^sub>2, (w\<^sub>2\<^sub>3, 1), p\<^sub>3) \<in> \<lbrakk>ts\<^sub>1\<rbrakk>"
    using binary_aut_transition_binary d23_non0 step.prems(1) by force
  ultimately
  show ?case
    using monoid_rtrancl.monoid_rtrancl_into_rtrancl[of p\<^sub>1 "(w\<^sub>1\<^sub>2, 1)" p\<^sub>2 "\<lbrakk>ts\<^sub>1\<rbrakk>" "(w\<^sub>2\<^sub>3, 1)" p\<^sub>3]
    by auto
qed

lemma w_inters_sound_exi_snd:
  assumes "((p\<^sub>1,q\<^sub>1), (w,d), (p\<^sub>2,q\<^sub>2)) \<in> \<lbrakk>ts\<^sub>1\<inter>\<^sub>wts\<^sub>2\<rbrakk>\<^sup>\<odot>"
  shows "\<exists>d'. (q\<^sub>1, (w,d'), q\<^sub>2) \<in> \<lbrakk>ts\<^sub>2\<rbrakk>\<^sup>\<odot>"
  using assms
proof (induction rule: wts_to_monoidLTS_pair_induct)
  case (base p q)
  then show ?case
    using monoid_rtrancl_wts_to_monoidLTS_refl by force
next
  case (step p\<^sub>1 q\<^sub>1 w\<^sub>1\<^sub>2 d\<^sub>1\<^sub>2 p\<^sub>2 q\<^sub>2 w\<^sub>2\<^sub>3 d\<^sub>2\<^sub>3 p\<^sub>3 q\<^sub>3)
  then have "\<exists>d2. (q\<^sub>2, (w\<^sub>2\<^sub>3,d2), q\<^sub>3) \<in> \<lbrakk>ts\<^sub>2\<rbrakk>"
    using wts_label_exist wts_to_monoidLTS_def by fastforce
  then show ?case
    using step(3) monoid_rtrancl.monoid_rtrancl_into_rtrancl[of q\<^sub>1 "(w\<^sub>1\<^sub>2, _)" q\<^sub>2 "\<lbrakk>ts\<^sub>2\<rbrakk>" "(w\<^sub>2\<^sub>3, _)" q\<^sub>3]
    by auto
qed

lemma w_inters_sound_snd_non_zero:
  fixes ts\<^sub>1::"('state::finite, 'label::finite, 'weight::bounded_dioid) w_transitions"
  fixes ts\<^sub>2::"('state::finite, 'label, 'weight) w_transitions"
  assumes "((p\<^sub>1,q\<^sub>1), (w,d), (p\<^sub>2,q\<^sub>2)) \<in> \<lbrakk>ts\<^sub>1\<inter>\<^sub>wts\<^sub>2\<rbrakk>\<^sup>\<odot>"
  assumes "binary_aut ts\<^sub>1"
  assumes "d\<noteq>0"
  shows "(q\<^sub>1, (w,d), q\<^sub>2) \<in> \<lbrakk>ts\<^sub>2\<rbrakk>\<^sup>\<odot>"
  using assms
proof (induction rule: wts_to_monoidLTS_pair_induct)
  case (base p q)
  then show ?case
    by (simp add: monoid_rtrancl_wts_to_monoidLTS_refl)
next
  case (step p\<^sub>1 q\<^sub>1 w\<^sub>1\<^sub>2 d\<^sub>1\<^sub>2 p\<^sub>2 q\<^sub>2 w\<^sub>2\<^sub>3 d\<^sub>2\<^sub>3 p\<^sub>3 q\<^sub>3)
  have "d\<^sub>1\<^sub>2 \<noteq> 0" using step.prems(2) by force
  then have "(q\<^sub>1, (w\<^sub>1\<^sub>2, d\<^sub>1\<^sub>2), q\<^sub>2) \<in> \<lbrakk>ts\<^sub>2\<rbrakk>\<^sup>\<odot>" by (simp add: step.IH step.prems(1))
  have "d\<^sub>2\<^sub>3 \<noteq> 0" using mult_not_zero step.prems(2) by blast
  obtain d\<^sub>2\<^sub>3\<^sub>p d\<^sub>2\<^sub>3\<^sub>q where f: 
    "(p\<^sub>2, (w\<^sub>2\<^sub>3, d\<^sub>2\<^sub>3\<^sub>p), p\<^sub>3) \<in> \<lbrakk>ts\<^sub>1\<rbrakk>"
    "(q\<^sub>2, (w\<^sub>2\<^sub>3, d\<^sub>2\<^sub>3\<^sub>q), q\<^sub>3) \<in> \<lbrakk>ts\<^sub>2\<rbrakk>"
    "d\<^sub>2\<^sub>3\<^sub>p * d\<^sub>2\<^sub>3\<^sub>q = d\<^sub>2\<^sub>3"
    by (metis w_inters_sound_transition step.hyps(2))
  have "d\<^sub>2\<^sub>3\<^sub>p = 1"
    by (metis \<open>d\<^sub>2\<^sub>3 \<noteq> 0\<close> d_mult_not_zero(1) f(1) f(3) binary_aut_transition_binary step.prems(1))
  then have "d\<^sub>2\<^sub>3\<^sub>q = d\<^sub>2\<^sub>3"
    using f(3) by auto
  then show ?case
    using \<open>(q\<^sub>1, (w\<^sub>1\<^sub>2, d\<^sub>1\<^sub>2), q\<^sub>2) \<in> \<lbrakk>ts\<^sub>2\<rbrakk>\<^sup>\<odot>\<close> f(2) monoid_rtrancl.monoid_rtrancl_into_rtrancl 
    by fastforce
qed

lemma w_inters_sound_zero:
  fixes ts\<^sub>1::"('state::finite, 'label::finite, 'weight::bounded_dioid) w_transitions"
  fixes ts\<^sub>2::"('state::finite, 'label, 'weight) w_transitions"
  assumes "((p\<^sub>1,q\<^sub>1), (w,d), (p\<^sub>2,q\<^sub>2)) \<in> \<lbrakk>ts\<^sub>1\<inter>\<^sub>wts\<^sub>2\<rbrakk>\<^sup>\<odot>"
  assumes "binary_aut ts\<^sub>1"
  assumes "d = 0"
  shows "(p\<^sub>1, (w,0), p\<^sub>2) \<in> \<lbrakk>ts\<^sub>1\<rbrakk>\<^sup>\<odot> \<or>
         (q\<^sub>1, (w,0), q\<^sub>2) \<in> \<lbrakk>ts\<^sub>2\<rbrakk>\<^sup>\<odot>"
  using assms 
proof (induction rule: wts_to_monoidLTS_pair_induct)
  case (base p q)
  then show ?case
    by (metis monoid_rtrancl_wts_to_monoidLTS_refl)
next
  case (step p\<^sub>1 q\<^sub>1 w\<^sub>1\<^sub>2 d\<^sub>1\<^sub>2 p\<^sub>2 q\<^sub>2 w\<^sub>2\<^sub>3 d\<^sub>2\<^sub>3 p\<^sub>3 q\<^sub>3)
  show ?case
  proof (cases "d\<^sub>1\<^sub>2 = 0")
    case True
    then have "(p\<^sub>1, (w\<^sub>1\<^sub>2, 0), p\<^sub>2) \<in> \<lbrakk>ts\<^sub>1\<rbrakk>\<^sup>\<odot> \<or> (q\<^sub>1, (w\<^sub>1\<^sub>2, 0), q\<^sub>2) \<in> \<lbrakk>ts\<^sub>2\<rbrakk>\<^sup>\<odot>"
      using step.IH step.prems(1) by auto
    then show ?thesis
    proof
      assume "(p\<^sub>1, (w\<^sub>1\<^sub>2, 0),p\<^sub>2) \<in> \<lbrakk>ts\<^sub>1\<rbrakk>\<^sup>\<odot>"
      moreover
      have "\<exists>d\<^sub>2\<^sub>3\<^sub>p. (p\<^sub>2, (w\<^sub>2\<^sub>3, d\<^sub>2\<^sub>3\<^sub>p), p\<^sub>3) \<in> \<lbrakk>ts\<^sub>1\<rbrakk>\<^sup>\<odot>"
        by (meson w_inters_sound_transition monoid_star_intros_step step.hyps(2))
      ultimately
      show ?thesis 
        using monoid_rtrancl_rtrancl_into_rtrancl by fastforce
    next
      assume "(q\<^sub>1, (w\<^sub>1\<^sub>2, 0), q\<^sub>2) \<in> \<lbrakk>ts\<^sub>2\<rbrakk>\<^sup>\<odot>"
      moreover
      have "\<exists>d\<^sub>2\<^sub>3\<^sub>q. (q\<^sub>2, (w\<^sub>2\<^sub>3, d\<^sub>2\<^sub>3\<^sub>q), q\<^sub>3) \<in> \<lbrakk>ts\<^sub>2\<rbrakk>\<^sup>\<odot>"
        by (meson w_inters_sound_transition monoid_star_intros_step step.hyps(2))
      ultimately
      show ?thesis
        using monoid_rtrancl_rtrancl_into_rtrancl by fastforce
    qed
  next
    case False
    note outer_False = False
    obtain d\<^sub>2\<^sub>3\<^sub>p d\<^sub>2\<^sub>3\<^sub>q where d23p_d23q_p: 
      "(p\<^sub>2, (w\<^sub>2\<^sub>3, d\<^sub>2\<^sub>3\<^sub>p), p\<^sub>3) \<in> \<lbrakk>ts\<^sub>1\<rbrakk>"
      "(q\<^sub>2, (w\<^sub>2\<^sub>3, d\<^sub>2\<^sub>3\<^sub>q), q\<^sub>3) \<in> \<lbrakk>ts\<^sub>2\<rbrakk>"
      "d\<^sub>2\<^sub>3 = d\<^sub>2\<^sub>3\<^sub>p * d\<^sub>2\<^sub>3\<^sub>q"
      using w_inters_sound_transition step.hyps(2) by blast
    have d13zero: "d\<^sub>1\<^sub>2 * d\<^sub>2\<^sub>3 = 0"
      using snd_conv using step.prems(2) by blast
    have d23p01: "d\<^sub>2\<^sub>3\<^sub>p = 1 \<or> d\<^sub>2\<^sub>3\<^sub>p = 0"
      using d23p_d23q_p(1) snd_conv wts_label_d' binary_aut_def by (metis step.prems(1))
    show ?thesis
    proof (cases "d\<^sub>2\<^sub>3\<^sub>p = 0")
      case True
      have "\<exists>d\<^sub>1\<^sub>2\<^sub>p. (p\<^sub>1, (w\<^sub>1\<^sub>2, d\<^sub>1\<^sub>2\<^sub>p), p\<^sub>2) \<in> \<lbrakk>ts\<^sub>1\<rbrakk>\<^sup>\<odot>"
        using w_inters_sound_non_zero_fst outer_False step by blast
      then show ?thesis 
        using True d23p_d23q_p(1) monoid_rtrancl_into_rtrancl by fastforce
    next
      case False
      have "(q\<^sub>1, (w\<^sub>1\<^sub>2, d\<^sub>1\<^sub>2), q\<^sub>2) \<in> \<lbrakk>ts\<^sub>2\<rbrakk>\<^sup>\<odot>"
        using w_inters_sound_snd_non_zero outer_False step.hyps(1) step.prems(1) by blast
      then show ?thesis
        using False d23p_d23q_p(2,3) d23p01 d13zero monoid_rtrancl.intros(2) by fastforce
    qed
  qed
qed

lemma w_inters_sound_and_complete:
  fixes ts\<^sub>1::"('state::finite, 'label::finite, 'weight::bounded_dioid) w_transitions"
  fixes ts\<^sub>2::"('state::finite, 'label, 'weight) w_transitions"
  assumes "binary_aut ts\<^sub>1"
  shows "((p\<^sub>1,q\<^sub>1), (w,d), (p\<^sub>2,q\<^sub>2)) \<in> \<lbrakk>ts\<^sub>1\<inter>\<^sub>wts\<^sub>2\<rbrakk>\<^sup>\<odot> \<longleftrightarrow>
           (\<exists>d\<^sub>p d\<^sub>q. (p\<^sub>1, (w,d\<^sub>p), p\<^sub>2) \<in> \<lbrakk>ts\<^sub>1\<rbrakk>\<^sup>\<odot> \<and>
                     (q\<^sub>1, (w,d\<^sub>q), q\<^sub>2) \<in> \<lbrakk>ts\<^sub>2\<rbrakk>\<^sup>\<odot> \<and> d\<^sub>p * d\<^sub>q = d)"
proof (cases "d = 0")
  case True
  show ?thesis
  proof 
    assume inter: "((p\<^sub>1, q\<^sub>1), (w, d), p\<^sub>2, q\<^sub>2) \<in> \<lbrakk>ts\<^sub>1\<inter>\<^sub>wts\<^sub>2\<rbrakk>\<^sup>\<odot>"
    then have dis0: "(p\<^sub>1, (w, 0), p\<^sub>2) \<in> \<lbrakk>ts\<^sub>1\<rbrakk>\<^sup>\<odot> \<or> (q\<^sub>1, (w, 0), q\<^sub>2) \<in> \<lbrakk>ts\<^sub>2\<rbrakk>\<^sup>\<odot>"
      using True
      using w_inters_sound_zero[of p\<^sub>1 q\<^sub>1 w d p\<^sub>2 q\<^sub>2 ts\<^sub>1 ts\<^sub>2] assms by auto
    moreover
    have p1p2: "\<exists>d\<^sub>p. (p\<^sub>1, (w, d\<^sub>p), p\<^sub>2) \<in> \<lbrakk>ts\<^sub>1\<rbrakk>\<^sup>\<odot>"
      using w_inters_sound_exi_fst[of p\<^sub>1 q\<^sub>1 w d p\<^sub>2, OF inter] by auto
    moreover
    have "\<exists>d\<^sub>q. (q\<^sub>1, (w, d\<^sub>q), q\<^sub>2) \<in> \<lbrakk>ts\<^sub>2\<rbrakk>\<^sup>\<odot>"
      by (meson inter w_inters_sound_exi_snd)
    ultimately
    show "\<exists>d\<^sub>p d\<^sub>q. (p\<^sub>1, (w, d\<^sub>p), p\<^sub>2) \<in> \<lbrakk>ts\<^sub>1\<rbrakk>\<^sup>\<odot> \<and> (q\<^sub>1, (w, d\<^sub>q), q\<^sub>2) \<in> \<lbrakk>ts\<^sub>2\<rbrakk>\<^sup>\<odot> \<and> d\<^sub>p * d\<^sub>q = d"
      using True mult_not_zero by blast
  next
    assume "\<exists>d\<^sub>p d\<^sub>q. (p\<^sub>1, (w, d\<^sub>p), p\<^sub>2) \<in> \<lbrakk>ts\<^sub>1\<rbrakk>\<^sup>\<odot> \<and> (q\<^sub>1, (w, d\<^sub>q), q\<^sub>2) \<in> \<lbrakk>ts\<^sub>2\<rbrakk>\<^sup>\<odot> \<and> d\<^sub>p * d\<^sub>q = d"
    then obtain d\<^sub>p d\<^sub>q where
      "(p\<^sub>1, (w, d\<^sub>p), p\<^sub>2) \<in> \<lbrakk>ts\<^sub>1\<rbrakk>\<^sup>\<odot>"
      "(q\<^sub>1, (w, d\<^sub>q), q\<^sub>2) \<in> \<lbrakk>ts\<^sub>2\<rbrakk>\<^sup>\<odot>"
      "d\<^sub>p * d\<^sub>q = d"
      by auto
    then show "((p\<^sub>1, q\<^sub>1), (w, d), p\<^sub>2, q\<^sub>2) \<in> \<lbrakk>ts\<^sub>1\<inter>\<^sub>wts\<^sub>2\<rbrakk>\<^sup>\<odot>"
      using assms binary_aut_path_binary w_inters_complete_0 w_inters_complete_1 by fastforce 
  qed
next
  case False
  show ?thesis
  proof 
    assume "((p\<^sub>1, q\<^sub>1), (w, d), p\<^sub>2, q\<^sub>2) \<in> \<lbrakk>ts\<^sub>1\<inter>\<^sub>wts\<^sub>2\<rbrakk>\<^sup>\<odot>"
    show "\<exists>d\<^sub>p d\<^sub>q. (p\<^sub>1, (w, d\<^sub>p), p\<^sub>2) \<in> \<lbrakk>ts\<^sub>1\<rbrakk>\<^sup>\<odot> \<and> (q\<^sub>1, (w, d\<^sub>q), q\<^sub>2) \<in> \<lbrakk>ts\<^sub>2\<rbrakk>\<^sup>\<odot> \<and> d\<^sub>p * d\<^sub>q = d"
      by (meson False \<open>((p\<^sub>1, q\<^sub>1), (w, d), p\<^sub>2, q\<^sub>2) \<in> \<lbrakk>ts\<^sub>1\<inter>\<^sub>wts\<^sub>2\<rbrakk>\<^sup>\<odot>\<close> assms w_inters_sound_non_zero_fst w_inters_sound_snd_non_zero mult_1)
  next 
    assume "\<exists>d\<^sub>p d\<^sub>q. (p\<^sub>1, (w, d\<^sub>p), p\<^sub>2) \<in> \<lbrakk>ts\<^sub>1\<rbrakk>\<^sup>\<odot> \<and> (q\<^sub>1, (w, d\<^sub>q), q\<^sub>2) \<in> \<lbrakk>ts\<^sub>2\<rbrakk>\<^sup>\<odot> \<and> d\<^sub>p * d\<^sub>q = d"
    then obtain d\<^sub>p d\<^sub>q where
      "(p\<^sub>1, (w, d\<^sub>p), p\<^sub>2) \<in> \<lbrakk>ts\<^sub>1\<rbrakk>\<^sup>\<odot>"
      "(q\<^sub>1, (w, d\<^sub>q), q\<^sub>2) \<in> \<lbrakk>ts\<^sub>2\<rbrakk>\<^sup>\<odot>"
      "d\<^sub>p * d\<^sub>q = d"
      by auto
    then show "((p\<^sub>1, q\<^sub>1), (w, d), p\<^sub>2, q\<^sub>2) \<in> \<lbrakk>ts\<^sub>1\<inter>\<^sub>wts\<^sub>2\<rbrakk>\<^sup>\<odot>"
      using False assms binary_aut_path_binary w_inters_complete_1 by fastforce
  qed
qed

lemma w_inters_sound:
  fixes ts\<^sub>1::"('state::finite, 'label::finite, 'weight::bounded_dioid) w_transitions"
  fixes ts\<^sub>2::"('state::finite, 'label, 'weight) w_transitions"
  assumes "binary_aut ts\<^sub>1"
  assumes "((p\<^sub>1,q\<^sub>1), (w,d), (p\<^sub>2,q\<^sub>2)) \<in> \<lbrakk>ts\<^sub>1\<inter>\<^sub>wts\<^sub>2\<rbrakk>\<^sup>\<odot>"
  shows "(\<exists>d\<^sub>p d\<^sub>q. (p\<^sub>1, (w,d\<^sub>p), p\<^sub>2) \<in> \<lbrakk>ts\<^sub>1\<rbrakk>\<^sup>\<odot> \<and>
                  (q\<^sub>1, (w,d\<^sub>q), q\<^sub>2) \<in> \<lbrakk>ts\<^sub>2\<rbrakk>\<^sup>\<odot> \<and> d\<^sub>p * d\<^sub>q = d)"
  using w_inters_sound_and_complete assms by metis

lemma w_inters_complete:
  fixes ts\<^sub>1::"('state::finite, 'label::finite, 'weight::bounded_dioid) w_transitions"
  fixes ts\<^sub>2::"('state::finite, 'label, 'weight) w_transitions"
  assumes "binary_aut ts\<^sub>1"
  assumes "(p\<^sub>1, (w,d\<^sub>p), p\<^sub>2) \<in> \<lbrakk>ts\<^sub>1\<rbrakk>\<^sup>\<odot>"
  assumes "(q\<^sub>1, (w,d\<^sub>q), q\<^sub>2) \<in> \<lbrakk>ts\<^sub>2\<rbrakk>\<^sup>\<odot>"
  shows "((p\<^sub>1,q\<^sub>1), (w, d\<^sub>p * d\<^sub>q), (p\<^sub>2,q\<^sub>2)) \<in> \<lbrakk>ts\<^sub>1\<inter>\<^sub>wts\<^sub>2\<rbrakk>\<^sup>\<odot>"
  using w_inters_sound_and_complete assms by metis

lemma w_inters_sound_wts_to_weightLTS:
  fixes ts\<^sub>1::"('state::finite, 'label::finite, 'weight::bounded_dioid) w_transitions"
  fixes ts\<^sub>2::"('state::finite, 'label, 'weight) w_transitions"
  assumes "binary_aut ts\<^sub>1"
  assumes "((p\<^sub>1,q\<^sub>1), d, (p\<^sub>2,q\<^sub>2)) \<in> \<lbrakk>ts\<^sub>1\<inter>\<^sub>wts\<^sub>2\<rbrakk>\<^sub>w\<^sup>\<odot>"
  shows "(\<exists>d\<^sub>p d\<^sub>q. (p\<^sub>1, d\<^sub>p, p\<^sub>2) \<in> (\<lbrakk>ts\<^sub>1\<rbrakk>\<^sub>w)\<^sup>\<odot> \<and>
         (q\<^sub>1, d\<^sub>q, q\<^sub>2) \<in> (\<lbrakk>ts\<^sub>2\<rbrakk>\<^sub>w)\<^sup>\<odot> \<and> d\<^sub>p * d\<^sub>q = d)"  
  using assms wts_weightLTS_star_to_monoidLTS_star w_inters_sound wts_monoidLTS_star_to_weightLTS_star
  by meson

lemma w_inters_sound_wts_to_monoidLTS:
  fixes ts\<^sub>1::"('state::finite, 'label::finite, 'weight::bounded_dioid) w_transitions"
  fixes ts\<^sub>2::"('state::finite, 'label, 'weight) w_transitions"
  assumes "binary_aut ts\<^sub>1"
  assumes "((p\<^sub>1,q\<^sub>1), d, (p\<^sub>2,q\<^sub>2)) \<in> \<lbrakk>ts\<^sub>1\<inter>\<^sub>wts\<^sub>2\<rbrakk>\<^sub>w\<^sup>\<odot>"
  shows "(\<exists>w d\<^sub>p d\<^sub>q. (p\<^sub>1, (w,d\<^sub>p), p\<^sub>2) \<in> \<lbrakk>ts\<^sub>1\<rbrakk>\<^sup>\<odot> \<and>
                    (q\<^sub>1, (w,d\<^sub>q), q\<^sub>2) \<in> \<lbrakk>ts\<^sub>2\<rbrakk>\<^sup>\<odot> \<and> d\<^sub>p * d\<^sub>q = d)"
  using wts_weightLTS_star_to_monoidLTS_star w_inters_sound[OF assms(1)] assms(2)
  by meson

lemma w_inters_complete_wts_to_weightLTS:
  fixes ts\<^sub>1::"('state::finite, 'label::finite, 'weight::bounded_dioid) w_transitions"
  fixes ts\<^sub>2::"('state::finite, 'label, 'weight) w_transitions"
  assumes "binary_aut ts\<^sub>1"
  assumes "(p\<^sub>1, (w, d\<^sub>p), p\<^sub>2) \<in> \<lbrakk>ts\<^sub>1\<rbrakk>\<^sup>\<odot>"
  assumes "(q\<^sub>1, (w, d\<^sub>q), q\<^sub>2) \<in> \<lbrakk>ts\<^sub>2\<rbrakk>\<^sup>\<odot>"
  shows "((p\<^sub>1, q\<^sub>1), d\<^sub>p * d\<^sub>q, (p\<^sub>2, q\<^sub>2)) \<in> \<lbrakk>ts\<^sub>1\<inter>\<^sub>wts\<^sub>2\<rbrakk>\<^sub>w\<^sup>\<odot>"
  using w_inters_complete[OF assms(1)] assms(2,3) wts_monoidLTS_star_to_weightLTS_star
  by fast

definition "fst_trans_all = fin_fun_of_fun fst_trans"

definition "snd_trans_all = fin_fun_of_fun snd_trans"

lemma fst_trans_all_is_fst_trans: "fst_trans_all $ t = fst_trans t"
  by (simp add: app_fin_fun_of_fun fst_trans_all_def)

lemma snd_trans_all_is_snd_trans: "snd_trans_all $ t = snd_trans t"
  by (simp add: app_fin_fun_of_fun snd_trans_all_def)

lemma pair_weight_code': "(pair_weight ts\<^sub>1 ts\<^sub>2) $ t = finfun_Diag ((($) ts\<^sub>1) \<circ>$ fst_trans_all) ((($) ts\<^sub>2) \<circ>$ snd_trans_all) $ t"
  by (simp add: fst_trans_all_is_fst_trans snd_trans_all_is_snd_trans finfun_apply_pair_weight)

lemma pair_weight_code[code]: "pair_weight ts\<^sub>1 ts\<^sub>2 = finfun_Diag ((($) ts\<^sub>1) \<circ>$ fst_trans_all) ((($) ts\<^sub>2) \<circ>$ snd_trans_all)"
  using pair_weight_code' by (metis finfun_ext)


end