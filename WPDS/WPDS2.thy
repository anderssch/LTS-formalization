theory WPDS2
  imports "LTS" "Saturation" "ReverseWellQuasiOrder" "FinFunWellQuasiOrder" "WAutomaton"
begin

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

interpretation dioidLTS transition_rel .

notation step_relp (infix "\<Rightarrow>" 80)
notation step_starp (infix "\<Rightarrow>\<^sup>*" 80)
notation l_step_relp ("(_)/ \<Midarrow> (_)/ \<Rightarrow> (_)/" [70,70,80] 80)
notation monoid_star_relp ("(_)/ \<Midarrow> (_)/ \<Rightarrow>\<^sup>* (_)/" [90,90,100] 100) 

lemma step_relp_def2:
  "(p, \<gamma>w') \<Midarrow>d\<Rightarrow> (p',ww') \<longleftrightarrow> (\<exists>\<gamma> w' w. \<gamma>w' = \<gamma>#w' \<and> ww' = (lbl w)@w' \<and> (p, \<gamma>) \<midarrow>d\<hookrightarrow> (p', w))"
  by (meson monoidLTS.l_step_relp_def transition_rel.simps)
end


locale WPDS_with_W_automata = WPDS \<Delta>
  for \<Delta> :: "('ctr_loc::enum, 'label::finite, 'weight::{dioid_one_zero,reverse_wqo}) rule set"
    +
  fixes finals :: "('ctr_loc::enum) set"
begin

interpretation dioidLTS transition_rel .
notation step_relp (infix "\<Rightarrow>" 80)
notation step_starp (infix "\<Rightarrow>\<^sup>*" 80)
notation l_step_relp ("(_)/ \<Midarrow> (_)/ \<Rightarrow> (_)/" [70,70,80] 80)
notation monoid_star_relp ("(_)/ \<Midarrow> (_)/ \<Rightarrow>\<^sup>* (_)/" [90,90,100] 100) 

lemma sum_mono: 
  assumes "(X::'weight set) \<subseteq> Y"
  shows "\<^bold>\<Sum> X \<le> \<^bold>\<Sum> Y"
  sorry

lemma sum_bigger: 
  assumes "d \<le> (d' :: 'weight)"
  shows "\<^bold>\<Sum> {d \<cdot> d''| d''. X d''} \<le> \<^bold>\<Sum> {d' \<cdot> d''| d''. X d''}"
  sorry

lemma sum_bigger2: 
  assumes "\<forall>t. X t \<longrightarrow> f t \<le> g t"
  shows "\<^bold>\<Sum> {f t| t. X t} \<le> \<^bold>\<Sum> {g t| t. X t}"
  sorry

lemma sum_in:
  assumes "d \<in> W "
  shows "d \<le> \<^bold>\<Sum>W"
  sorry

lemma sum_empty: "\<^bold>\<Sum>{}=0"
  sorry

\<comment> \<open>Generalization of PDS_with_P_automata.accepts that computes the meet-over-all-paths in the W-automaton.\<close>
definition accepts :: "('ctr_loc, 'label, 'weight) w_transitions \<Rightarrow> ('ctr_loc, 'label) conf \<Rightarrow> 'weight" where
  "accepts ts \<equiv> \<lambda>(p,w). (\<^bold>\<Sum>{d | d q. q \<in> finals \<and> (p,(w,d),q) \<in> monoidLTS.monoid_star (wts_to_monoidLTS ts)})"


\<comment> \<open>Weighted pre-star rule updates the finfun of transition weights.\<close>
inductive pre_star_rule :: "('ctr_loc, 'label, 'weight) w_transitions saturation_rule" where 
  add_trans: "((p, \<gamma>) \<midarrow>d\<hookrightarrow> (p', w)) 
      \<Longrightarrow> (p', (lbl w, d'), q) \<in> monoidLTS.monoid_star (wts_to_monoidLTS ts)
      \<Longrightarrow> (ts $ (p, \<gamma>, q)) = d''
      \<Longrightarrow> (d'' + (d * d')) \<noteq> d'' 
      \<Longrightarrow> pre_star_rule ts ts((p, \<gamma>, q) $:= d'' + (d * d'))"

definition pre_star1 :: "('ctr_loc, 'label, 'weight) w_transitions \<Rightarrow> (('ctr_loc, 'label) transition \<times> 'weight) set" where
  "pre_star1 wts =
    (\<Union>((p, \<gamma>), d, (p', w)) \<in> \<Delta>. 
        \<Union>(q,d') \<in> monoidLTS_reach (wts_to_monoidLTS wts) (p') (lbl w). 
            {((p, \<gamma>, q), d * d')})"

definition "pre_star_loop = while_option (\<lambda>s. update_wts s (pre_star1 s) \<noteq> s) (\<lambda>s. update_wts s (pre_star1 s))"
definition "pre_star_exec = the o pre_star_loop"
definition "pre_star_exec_check A = (if A={} then pre_star_loop (ts_to_wts A) else None)"

definition "accept_pre_star_exec_check A c = (if A={} then Some (accepts (pre_star_exec (ts_to_wts A)) c) else None)"

theorem pre_star_rule_correct:
  assumes "saturation pre_star_rule (ts_to_wts {}) A"
  shows "accepts A = weight_pre_star (accepts (ts_to_wts {}))"
  using assms
  apply simp
    \<comment> \<open>TODO\<close>
  oops

lemma pre_star_rule_less_aux:
  fixes ts::"(('ctr_loc, 'label, 'weight::{dioid_one_zero,reverse_wqo}) w_transitions)"
  assumes "ts $ (p, \<gamma>, q) + d \<cdot> d' \<noteq> ts $ (p, \<gamma>, q)"
  assumes "ts' = ts((p, \<gamma>, q) $:= ts $ (p, \<gamma>, q) + d \<cdot> d')"
  shows "ts < ts'"
proof -
  from assms(1) have "ts $ (p, \<gamma>, q) < ts $ (p, \<gamma>, q) + d \<cdot> d'" 
    by (simp add: join.sup.strict_order_iff join.sup_commute join.sup_left_commute)
  then have "ts $ (p, \<gamma>, q) < ts' $ (p, \<gamma>, q)" using assms(2) by simp
  then show ?thesis using assms(2) finfun_update_less[of ts "(p, \<gamma>, q)" ts'] by blast
qed

lemma pre_star_rule_less:
  assumes "pre_star_rule A B"
  shows "A < B"
  using assms by (auto simp add:pre_star_rule.simps pre_star_rule_less_aux)

lemma pre_star_rule_less_eq:
  assumes "pre_star_rule A B"
  shows "A \<le> B"
  using pre_star_rule_less[OF assms(1)] by simp

lemma pre_star_saturation_exi:
  shows "\<exists>ts'. saturation pre_star_rule ts ts'"
  by (rule reverse_wqo_class_saturation_exi[of pre_star_rule ts])
     (simp add: pre_star_rule_less)

lemma saturation_rtranclp_pre_star_rule_incr: "pre_star_rule\<^sup>*\<^sup>* A B \<Longrightarrow> A \<le> B"
proof (induction rule: rtranclp_induct)
  case base
  then show ?case by auto
next
  case (step y z)
  then show ?case
    using pre_star_rule_less by fastforce
qed


lemma monoid_star_pop:
  assumes "(p, (lbl w, d), q) \<in> monoidLTS.monoid_star (wts_to_monoidLTS ts)"
      and "w = pop"
    shows "p = q \<and> d = 1"
  using assms monoid_star_w0 by (auto simp add: one_list_def mstar_wts_empty_one) fastforce

lemma monoid_star_swap:
  assumes "(p, (lbl w, d), q) \<in> monoidLTS.monoid_star (wts_to_monoidLTS ts)"
      and "w = swap l"
    shows "ts $ (p,l,q) = d"
  using assms monoid_star_w1 by fastforce

lemma monoid_star_push:
  assumes "(p, (lbl w, d), q) \<in> monoidLTS.monoid_star (wts_to_monoidLTS ts)"
      and "w = push l l'"
    shows "\<exists>q'. ts $ (p,l,q') * ts $ (q',l',q) = d"
  using assms monoid_star_w2 by fastforce

lemma pre_star_rule_cases:
  assumes "(p, (lbl w, d), q) \<in> monoidLTS.monoid_star (wts_to_monoidLTS ts)"
  shows "(w = pop \<and> q = p \<and> d = 1) \<or>                          
         (\<exists>l. w = swap l \<and> ts $ (p,l,q) = d) \<or> 
         (\<exists>l l'. w = push l l' \<and> (\<exists>q'. ts $ (p,l,q') * ts $ (q',l',q) = d))"
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
  assumes "(p, (lbl w, d), q) \<in> monoidLTS.monoid_star (wts_to_monoidLTS ts)"
  obtains        "q = p" "d = 1" "w = pop"
    | l    where "ts $ (p,l,q) = d" "w = swap l"
    | l l' q' where "ts $ (p,l,q') * ts $ (q',l',q) = d" "w = push l l'"
using pre_star_rule_cases[OF assms(1)] by blast

lemma pre_star_rule_update_spec:
  assumes "pre_star_rule A A'"
      and "A $ (p,\<gamma>,q) \<noteq> A' $ (p,\<gamma>,q)"
    shows "\<exists>d d' p' w.
              A' $ (p,\<gamma>,q) = A $ (p, \<gamma>, q) + d \<cdot> d' \<and>
              (p, \<gamma>) \<midarrow>d\<hookrightarrow> (p', w) \<and>
              (p', (lbl w, d'), q) \<in> monoid_rtrancl (wts_to_monoidLTS A) \<and>
              A $ (p, \<gamma>, q) + d \<cdot> d' \<noteq> A $ (p, \<gamma>, q)"
  using assms unfolding pre_star_rule.simps
  apply safe
  subgoal for p' \<gamma>' _ _ _ _ q'
    by (cases "(p,\<gamma>,q) = (p', \<gamma>',q')", auto)
  done

definition sound :: "(('ctr_loc, 'label, 'weight) w_transitions) \<Rightarrow> bool" where
  "sound A \<longleftrightarrow> (\<forall>p p' \<gamma> d. (p, ([\<gamma>],d), p') \<in> (wts_to_monoidLTS A) \<longrightarrow> d \<le> \<^bold>\<Sum>{d'. (p,[\<gamma>]) \<Midarrow>d'\<Rightarrow>\<^sup>* (p',[])})"

lemma monoid_star_intros_step':
  assumes "(a,b,c) \<in> wts_to_monoidLTS A"
  shows "(a,b,c) \<in> monoidLTS.monoid_star (wts_to_monoidLTS A)"
proof -
  define w :: "'b list \<times> 'c" where "w = 1"
  define l :: "'b list \<times> 'c" where "l = b"
  have "b = w \<cdot> l"
    by (simp add: l_def w_def)
  have "monoid_rtranclp (monoidLTS.l_step_relp (wts_to_monoidLTS A)) a w a"
    using w_def by force
  have "monoidLTS.l_step_relp (wts_to_monoidLTS A) a b c"
    by (simp add: assms monoidLTS.l_step_relp_def)
  have "monoid_rtranclp (monoidLTS.l_step_relp (wts_to_monoidLTS A)) a b c"
    using assms unfolding monoidLTS.monoid_star_def using monoid_rtranclp.intros(2)[of "(monoidLTS.l_step_relp (wts_to_monoidLTS A))" a w a b c]
    using \<open>b = w \<cdot> l\<close> \<open>monoidLTS.l_step_relp (wts_to_monoidLTS A) a b c\<close> \<open>monoid_rtranclp (monoidLTS.l_step_relp (wts_to_monoidLTS A)) a w a\<close> l_def by fastforce
  then show ?thesis
    unfolding monoidLTS.monoid_star_def by auto
qed

lemma monoid_star_intros_step:
  assumes "a \<in> wts_to_monoidLTS A"
  shows "a \<in> monoidLTS.monoid_star (wts_to_monoidLTS A)"
  using assms monoid_star_intros_step' rev_edge.cases by (cases a) auto

lemma sound_def2'':
  assumes "(\<forall>p p' w d. (p, (w,d), p') \<in> monoidLTS.monoid_star (wts_to_monoidLTS A) \<longrightarrow> d \<le> \<^bold>\<Sum>{d'. (p,w) \<Midarrow>d'\<Rightarrow>\<^sup>* (p',[])})"
  assumes "(p, ([\<gamma>],d), p') \<in> (wts_to_monoidLTS A)"
  shows "d \<le> \<^bold>\<Sum>{d'. (p,[\<gamma>]) \<Midarrow>d'\<Rightarrow>\<^sup>* (p',[])}"
proof -
  have "(p, ([\<gamma>],d), p') \<in> monoidLTS.monoid_star (wts_to_monoidLTS A)"
    using assms(2) monoid_star_intros_step by blast
  then show "d \<le> \<^bold>\<Sum>{d'. (p,[\<gamma>]) \<Midarrow>d'\<Rightarrow>\<^sup>* (p',[])}"
    using assms(1) by auto
qed

lemma baba:
  assumes "(p, ([], d), p') \<in> monoidLTS.monoid_star (wts_to_monoidLTS A)"
  shows "d = 1"
proof -
  from assms have "monoid_rtranclp (monoidLTS.l_step_relp (wts_to_monoidLTS A)) p ([], d) p'"
    unfolding monoidLTS.monoid_star_def by auto
  then show "d = 1"
  proof (cases rule: monoid_rtranclp.cases)
    case monoid_rtrancl_refl
    then show ?thesis
      by (metis assms monoid_star_is_monoid_rtrancl mstar_wts_empty_one)
  next
    case (monoid_rtrancl_into_rtrancl w b l)
    then show ?thesis
      by (metis assms monoid_star_is_monoid_rtrancl mstar_wts_empty_one)
  qed
qed

lemma monoid_rtrancl_hd_tail:
  assumes "(p, wd, p') \<in> monoid_rtrancl (wts_to_monoidLTS ts)"
  assumes "length (fst wd) \<ge> 1"
  shows "\<exists>d' s d''.
           (p, ([hd (fst wd)], d'), s) \<in> wts_to_monoidLTS ts \<and>
           (s, (tl (fst wd), d''), p') \<in> monoid_rtrancl (wts_to_monoidLTS ts) \<and> 
           (snd wd) = d' \<cdot> d''"
using assms proof (induction  rule: monoid_rtrancl.induct)
  case (monoid_rtrancl_refl a)
  then show ?case
    by (simp add: one_list_def one_prod_def)
next
  case (monoid_rtrancl_into_rtrancl p wd p' l p'')
  show ?case
  proof (cases "1 \<le> length (fst wd)")
    case True
    then have "\<exists>d' s d''. (p, ([hd (fst wd)], d'), s) \<in> wts_to_monoidLTS ts \<and> 
                        (s, (tl (fst wd), d''), p') \<in> monoid_rtrancl (wts_to_monoidLTS ts) \<and> 
                        (snd wd) = d' \<cdot> d''"
      using monoid_rtrancl_into_rtrancl.IH by blast
    then obtain d' s d'' where jajajajajaja:
      "(p, ([hd (fst wd)], d'), s) \<in> wts_to_monoidLTS ts"
      "(s, (tl (fst wd), d''), p') \<in> monoid_rtrancl (wts_to_monoidLTS ts)"
      "snd wd = d' \<cdot> d''"
      by auto

    define d1 where "d1 = d'"
    define d2 where "d2 = d'' \<cdot> snd l"
    define s' where "s' = s"

    have "hd (fst (wd \<cdot> l)) = hd (fst (wd)) "
      using \<open>1 \<le> length (fst wd)\<close>
      apply auto
      apply (cases wd)
      apply auto
      apply (cases l)
      apply (auto simp add: mult_prod_def)
      by (metis One_nat_def hd_append list.size(3) not_one_le_zero times_list_def)

    have "(p, ([hd (fst (wd \<cdot> l))], d1), s') \<in> wts_to_monoidLTS ts"
      using jajajajajaja \<open>hd (fst (wd \<cdot> l)) = hd (fst wd)\<close> d1_def s'_def by auto
    moreover
    have "(s', (tl (fst (wd \<cdot> l)), d2), p'') \<in> monoid_rtrancl (wts_to_monoidLTS ts)"

      using monoid_rtrancl.intros(2)[OF jajajajajaja(2) monoid_rtrancl_into_rtrancl(2)] 
      unfolding d2_def
      apply (cases wd)
      apply auto
      apply (cases l)
      apply (auto simp add: mult_prod_def)
      by (metis One_nat_def \<open>1 \<le> length (fst wd)\<close> fst_conv le_antisym less_eq_nat.simps(1) 
          list.size(3) n_not_Suc_n s'_def times_list_def tl_append_if)
    moreover
    have "snd (wd \<cdot> l) = d1 \<cdot> d2"
      by (simp add: jajajajajaja d1_def d2_def mult.assoc mult_prod_def)
    ultimately
    show ?thesis
      by auto
  next
    case False
    then have "length (fst wd) = 0"
      by linarith
    then show ?thesis
      by (metis (no_types, opaque_lifting) length_0_conv list.sel(1) list.sel(3) 
          monoid_rtrancl.monoid_rtrancl_refl monoid_rtrancl_into_rtrancl.hyps(1) 
          monoid_rtrancl_into_rtrancl.hyps(2) monoid_star_w0 mstar_wts_empty_one mult.right_neutral 
          mult_1 mult_prod_def one_list_def prod.collapse wts_label_exist)
  qed
qed


(* We are not using this induction. But it could be useful. *)
lemma wts_to_monoidLTS_induct_reverse:
  assumes "(p, wd, p') \<in> monoid_rtrancl (wts_to_monoidLTS ts)"
  assumes "(\<And>a. P a 1 a)"
  shows "(\<And>p wd p' l p''. (p, wd, p') \<in> (wts_to_monoidLTS ts) \<Longrightarrow> P p' l p'' \<Longrightarrow> (p', l, p'') \<in> monoid_rtrancl (wts_to_monoidLTS ts) \<Longrightarrow> P p (wd \<cdot> l) p'') \<Longrightarrow> P p wd p'"
  using assms
proof (induct "length (fst wd)" arbitrary: p wd p')
  case 0
  then show ?case
    by (metis length_0_conv monoid_star_w0 mstar_wts_one one_list_def one_prod_def prod.collapse)

next
  case (Suc n)
  show ?case
  proof (cases "n = 0")
    case True
    then have "P p' 1 p'"
      using Suc(1)[of "1" p' p'] using Suc by blast
    moreover
    have "(p, wd, p') \<in> wts_to_monoidLTS ts"
      by (smt (verit, best) One_nat_def Suc.hyps(2) Suc.prems(2) True add.commute append_Nil 
          append_eq_append_conv fst_conv list.sel(1) list.size(3) list.size(4) monoid_rtrancl.simps 
          monoid_star_w0 monoid_star_w1 mult_prod_def one_list_def one_neq_zero one_prod_def 
          plus_1_eq_Suc prod.collapse times_list_def wts_label_d' wts_label_exist)
    moreover
    have "(p', 1, p') \<in> monoid_rtrancl (wts_to_monoidLTS ts)"
      by simp
    ultimately
    show ?thesis
      using Suc(3)[of p wd p' 1 p'] by auto
  next
    case False
    define w where "w = fst wd"
    define d where "d = snd wd"
    define w' where "w' = tl w"
    define \<gamma> where "\<gamma> = hd w"

    have w_split: "\<gamma> # w' = w"
      by (metis Suc.hyps(2) \<gamma>_def list.collapse list.size(3) nat.simps(3) w'_def w_def)

    have "\<exists>d' s d''.(p, ([\<gamma>],d'), s) \<in> wts_to_monoidLTS ts \<and>
            (s, (w',d''),p') \<in> monoid_rtrancl (wts_to_monoidLTS ts) \<and>
            d = d' \<cdot> d''"
      using Suc(4) False
      by (smt (verit, ccfv_SIG) Suc.hyps(2) \<gamma>_def d_def le_add1 plus_1_eq_Suc monoid_rtrancl_hd_tail 
          w'_def w_def) 
    then obtain s d' d'' where
      "(p, ([\<gamma>],d'), s) \<in> wts_to_monoidLTS ts"
      "(s, (w',d''),p') \<in> monoid_rtrancl (wts_to_monoidLTS ts)"
      "d = d' \<cdot> d''" by auto

    have "P s (w',d'') p'"
      by (smt (verit, ccfv_SIG) Suc(1) Suc(2) Suc(3) \<open>(s, (w', d''), p') \<in> monoid_rtrancl (wts_to_monoidLTS ts)\<close> assms(2) fst_conv length_Cons nat.inject w_def w_split)

    have "P p (([\<gamma>], d') \<cdot> (w', d'')) p'"
      using Suc(3)[of p "([\<gamma>],d')" s "(w', d'')" p']
      using \<open>(p, ([\<gamma>], d'), s) \<in> wts_to_monoidLTS ts\<close> \<open>(s, (w', d''), p') \<in> monoid_rtrancl (wts_to_monoidLTS ts)\<close> \<open>P s (w', d'') p'\<close> by blast 
    then have "P p (\<gamma> # w', d' \<cdot> d'') p'"
      apply -
      apply (auto simp add: mult_prod_def times_list_def)
      done
    then show ?thesis
      using w_split
      using \<open>d = d' \<cdot> d''\<close> d_def w_def by fastforce
  qed
qed

lemma monoid_star_nonempty:
  assumes "(p, w, p') \<in> monoid_rtrancl (wts_to_monoidLTS ts)"
  assumes "fst w \<noteq> []"
  shows "\<exists>pi d1 d2. (snd w) = d1 \<cdot> d2 \<and> (pi, (tl (fst w), d2), p') \<in> monoid_rtrancl (wts_to_monoidLTS ts) \<and> (p, ([hd (fst w)], d1), pi) \<in> wts_to_monoidLTS ts"
  by (metis One_nat_def Suc_leI assms(1) assms(2) gr0I length_0_conv monoid_rtrancl_hd_tail)


lemma sum_distr: "d1 \<cdot> \<^bold>\<Sum> D = \<^bold>\<Sum> {d1 \<cdot> d2 | d2. d2 \<in> D}"
  sorry


lemma sum_of_sums:
  "\<^bold>\<Sum> {\<^bold>\<Sum> {d. P d d'} |d'. Q d'} = \<^bold>\<Sum> {d | d d'. P d d' \<and> Q d'}"
  sorry

lemma sum_of_sums2:
  "\<^bold>\<Sum> {\<^bold>\<Sum> {f d d'| d. P d d'} |d'. Q d'} = \<^bold>\<Sum> {f d d' | d d'. P d d' \<and> Q d'}"
  sorry

lemma sum_of_sums_mult:
  "\<^bold>\<Sum> {\<^bold>\<Sum> {d. P d} \<cdot> d' |d'. Q d'} = \<^bold>\<Sum> {d \<cdot> d' | d d'. P d \<and> Q d'}"
  sorry

lemma sum_of_sums_mult2:
  "\<^bold>\<Sum> {\<^bold>\<Sum> {f d d'| d. P d d'} \<cdot> g d' |d'. Q d'} = \<^bold>\<Sum> {f d d' \<cdot> g d' | d d'. P d d' \<and> Q d'}"
   sorry 

lemmas monoid_star_relp_induct = 
  MonoidClosure.monoid_rtranclp.induct[of l_step_relp "(_,_)" _ "(_,_)"]

lemma step_rule_aux:
  assumes "(p, \<gamma>) \<midarrow>d\<hookrightarrow> (p', w)"
  assumes "c \<Midarrow>d'\<Rightarrow>\<^sup>* (p, \<gamma> # w')"
  shows "c \<Midarrow>(d'\<cdot>d)\<Rightarrow>\<^sup>* (p', lbl w @ w')"
  using assms
  by (meson WPDS.step_relp_def2 monoid_rtranclp.monoid_rtrancl_into_rtrancl)

lemma step_relp_append:
  assumes "(p,w) \<Midarrow>d'\<Rightarrow>\<^sup>* (p',w')"
  shows "(p, w @ v) \<Midarrow>d'\<Rightarrow>\<^sup>* (p', w' @ v)"
  using MonoidClosure.monoid_rtranclp.induct[of "\<lambda>a b c. a\<Midarrow>b\<Rightarrow>c" "(p,w)" d' "(p',w')"  "\<lambda>(p,w) d' (p',w'). (p,w @ v) \<Midarrow>d'\<Rightarrow>\<^sup>* (p', w' @ v)", OF assms(1)]
        step_rule_aux step_relp_def2 by fastforce

lemma step_relp_append2:
  assumes "(p, u) \<Midarrow> d''' \<Rightarrow>\<^sup>* (p'', [])"
  assumes "v = u @ w"
  shows "(p, v) \<Midarrow> d''' \<Rightarrow>\<^sup>* (p'', w)"
  using assms by (metis WPDS_with_W_automata.step_relp_append self_append_conv2)

lemma step_relp_seq:
  assumes "(p, a) \<Midarrow>d1\<Rightarrow>\<^sup>* (pi, [])"
  assumes "(pi, w) \<Midarrow>d'\<Rightarrow>\<^sup>* (p', [])"
  shows "(p, a @ w) \<Midarrow>(d1 \<cdot> d')\<Rightarrow>\<^sup>* (p', [])"
proof -
  have "(p, a @ w) \<Midarrow> d1 \<Rightarrow>\<^sup>* (pi, w)"
    using assms(1) using step_relp_append by fastforce
  show ?thesis
    by (meson \<open>(p, a @ w) \<Midarrow> d1 \<Rightarrow>\<^sup>* (pi, w)\<close> assms(2) monoid_rtranclp_trans)
qed

lemma sound_def2':
  assumes "sound A"
  assumes "(p, (w,d), p') \<in> monoidLTS.monoid_star (wts_to_monoidLTS A)"
  shows "d \<le> \<^bold>\<Sum>{d'. (p,w) \<Midarrow>d'\<Rightarrow>\<^sup>* (p',[])}"
  using assms(2) 
proof (induction w arbitrary: d p)
  case Nil
  then have "d = 1"
    by (simp add: baba)
  have "(p, []) \<Midarrow> 1 \<Rightarrow>\<^sup>* (p', [])"
    by (metis WPDS.lbl.simps(1) WPDS_with_W_automata.monoid_star_pop local.Nil monoid_rtranclp.simps)
  have "d \<le> \<^bold>\<Sum> {d'. d' = 1 \<and> (p, []) \<Midarrow> 1 \<Rightarrow>\<^sup>* (p', [])}"
  proof -
    have "{d'. d' = 1 \<and> (p, []) \<Midarrow> 1 \<Rightarrow>\<^sup>* (p', [])} = {1}"
      using \<open>(p, []) \<Midarrow> 1 \<Rightarrow>\<^sup>* (p', [])\<close> by blast
    then show "?thesis"
      using \<open>d = 1\<close> by fastforce
  qed
  also
  have "... \<le> \<^bold>\<Sum> {d'. (p, []) \<Midarrow> d' \<Rightarrow>\<^sup>* (p', [])}"
    by (simp add: Collect_mono_iff WPDS_with_W_automata.sum_mono)
  finally 
  show ?case 
    .
next
  case (Cons a w)
  from Cons(2) have
    "\<exists>pi d1 d2. d = d1 \<cdot> d2 
                \<and> (pi, (w, d2), p') \<in> monoidLTS.monoid_star (wts_to_monoidLTS A)
                \<and> (p, ([a], d1), pi) \<in> (wts_to_monoidLTS A)"
    unfolding monoid_star_is_monoid_rtrancl
    using monoid_star_nonempty by fastforce
  then obtain pi d1 d2 where obt:
    "d = d1 \<cdot> d2"
    "(pi, (w, d2), p') \<in> monoidLTS.monoid_star (wts_to_monoidLTS A)"
    "(p, ([a], d1), pi) \<in> wts_to_monoidLTS A"
    by blast
  then have d2l: "d2 \<le> \<^bold>\<Sum> {d'. (pi, w) \<Midarrow> d' \<Rightarrow>\<^sup>* (p', [])}" 
    using Cons(1)[of pi d2] by auto
  have "d = d1 \<cdot> d2"
    using \<open>d = d1 \<cdot> d2\<close> . 
  also have "... \<le> d1 \<cdot> \<^bold>\<Sum> {d'. (pi, w) \<Midarrow> d' \<Rightarrow>\<^sup>* (p', [])}"
    using d2l pre_dioid_class.mult_isol[of d2 "\<^bold>\<Sum> {d'. (pi, w) \<Midarrow> d' \<Rightarrow>\<^sup>* (p', [])}" d1] by auto
  also have "... \<le> \<^bold>\<Sum> {d1 \<cdot> d'| d'. (pi, w) \<Midarrow> d' \<Rightarrow>\<^sup>* (p', [])}"
    using sum_distr[of d1 "{d'. (pi, w) \<Midarrow> d' \<Rightarrow>\<^sup>* (p', [])}"] by auto
  also have "... \<le> \<^bold>\<Sum> {\<^bold>\<Sum> {d. (p, [a]) \<Midarrow> d \<Rightarrow>\<^sup>* (pi, [])} \<cdot> d'| d'.  (pi, w) \<Midarrow> d' \<Rightarrow>\<^sup>* (p', [])}"
    using sum_bigger assms(1) obt(3) sound_def by auto 
  also have "... \<le> \<^bold>\<Sum> {d1 \<cdot> d'| d' d1. (p, [a]) \<Midarrow> d1 \<Rightarrow>\<^sup>* (pi, []) \<and> (pi, w) \<Midarrow> d' \<Rightarrow>\<^sup>* (p', [])}"
    using sum_of_sums_mult[of "\<lambda>d. (p, [a]) \<Midarrow> d \<Rightarrow>\<^sup>* (pi, [])" "\<lambda>d'. (pi, w) \<Midarrow> d' \<Rightarrow>\<^sup>* (p', [])"]
    by (smt (verit, del_insts) Collect_cong Orderings.order_eq_iff)
  also have "... \<le> \<^bold>\<Sum> {d'. (p, a # w) \<Midarrow> d' \<Rightarrow>\<^sup>* (p', [])}"
    by (smt (verit, ccfv_threshold) Collect_mono_iff append_Cons append_self_conv2 local.sum_mono step_relp_seq)
  finally
  show ?case
    .
qed

lemma sound_def2:
  "sound A \<longleftrightarrow> (\<forall>p p' w d. (p, (w,d), p') \<in> monoidLTS.monoid_star (wts_to_monoidLTS A) \<longrightarrow> d \<le> \<^bold>\<Sum>{d'. (p,w) \<Midarrow>d'\<Rightarrow>\<^sup>* (p',[])})"
  using sound_def2'' sound_def2' unfolding sound_def by metis

lemma soundness:
  assumes "sound A"
  assumes "pre_star_rule A A'"
  shows "sound A'"
proof -
  obtain p' \<gamma>' d p'' w' d' q d'' where ps:
    "(p',\<gamma>') \<midarrow>d\<hookrightarrow> (p'',w')"
    "d'' + d \<cdot> d' \<noteq> d''" 
    "(p'',(lbl w', d'),q) \<in> monoidLTS.monoid_star (wts_to_monoidLTS A)" 
    "A' = A((p', \<gamma>', q) $:= d'' + d \<cdot> d')" 
    "A $ (p', \<gamma>', q) = d''" 
    using assms(2) pre_star_rule.cases by metis
  note 2 = ps(3)
  show "sound A'"
    unfolding sound_def
  proof (rule allI, rule allI, rule allI, rule allI, rule impI)
    fix p1 p2 \<mu> l
    assume a: "(p1, ([\<mu>], l), p2) \<in> wts_to_monoidLTS A'"      
    show "l \<le> \<^bold>\<Sum> {d'. (p1, [\<mu>]) \<Midarrow> d' \<Rightarrow>\<^sup>* (p2, [])}"
    proof (cases "p1 = p' \<and> \<mu> = \<gamma>' \<and> p2 = q")
      case True
      then have True1: "p1 = p'" "\<mu> = \<gamma>'" "p2 = q"
        by auto
      have 4: "l = d'' + d \<cdot> d'"
        using a unfolding ps(4) True1 unfolding wts_to_monoidLTS_def by auto
      have 3: "d'' \<le> \<^bold>\<Sum>{d'. (p1,[\<mu>]) \<Midarrow>d'\<Rightarrow>\<^sup>* (p2,[])}"
        using ps(5) using assms(1) unfolding sound_def unfolding wts_to_monoidLTS_def
        using True by force
      have 1: "(p1, [\<mu>]) \<Midarrow>d\<Rightarrow> (p'', lbl w')"
        using ps(1) True step_relp_def2 by auto
      show ?thesis
      proof (rule pre_star_rule_exhaust[OF ps(3)[unfolded True1[symmetric]]])
        assume "p2 = p''"
        assume "d' = 1"
        assume "w' = pop"
        from 2 have "(p'', ([], d'), p2) \<in> monoidLTS.monoid_star (wts_to_monoidLTS A)"
          using True1(3) \<open>w' = pop\<close> by force
        from 1 have "(p1, [\<mu>]) \<Midarrow>d \<cdot> d'\<Rightarrow> (p2,[])"
          using \<open>d' = 1\<close> \<open>w' = pop\<close> \<open>p2 = p''\<close> by auto
        then have "d \<cdot> d' \<le> \<^bold>\<Sum>{d'. (p1, [\<mu>]) \<Midarrow> d'\<Rightarrow>\<^sup>* (p2,[])}"
          by (metis mem_Collect_eq monoid_rtranclp.monoid_rtrancl_into_rtrancl mult_1 sum_in 
              monoid_rtranclp.monoid_rtrancl_refl)
        then show "l \<le> \<^bold>\<Sum> {d'. (p1, [\<mu>]) \<Midarrow>d'\<Rightarrow>\<^sup>* (p2, [])}"
          using 3 4 by auto
      next
        fix \<mu>'
        assume "A $ (p'', \<mu>', p2) = d'"
        assume 5: "w' = swap \<mu>'"
        from 2 have "(p'', ([\<mu>'],d'), p2) \<in> monoidLTS.monoid_star (wts_to_monoidLTS A)"
          using True1(3) \<open>w' = swap \<mu>'\<close> by force
        then have 6: "d' \<le> \<^bold>\<Sum>{d'. (p'',[\<mu>']) \<Midarrow>d'\<Rightarrow>\<^sup>* (p2,[])}"
          using assms(1) unfolding sound_def
          using \<open>A $ (p'', \<mu>', p2) = d'\<close> join.bot.extremum mem_Collect_eq wts_to_monoidLTS_def by fastforce
        from 1 have "(p1, [\<mu>]) \<Midarrow>d\<Rightarrow>\<^sup>* (p'',[\<mu>'])"
          unfolding True1 5 using monoid_rtranclp.monoid_rtrancl_into_rtrancl by fastforce
        have "d \<cdot> d' \<le> d \<cdot> \<^bold>\<Sum>{d'. (p'',[\<mu>']) \<Midarrow>d'\<Rightarrow>\<^sup>* (p2,[])}"
          using 6 by (simp add: assms pre_dioid_class.mult_isol)
        also 
        have "... \<le>  \<^bold>\<Sum>{d \<cdot> d'| d'. (p'',[\<mu>']) \<Midarrow>d'\<Rightarrow>\<^sup>* (p2,[])}"
          by (simp add: sum_distr)
        also
        have "... \<le> \<^bold>\<Sum>{d \<cdot> d'| d'. (p1, [\<mu>]) \<Midarrow>d\<Rightarrow>\<^sup>* (p'',[\<mu>']) \<and> (p'',[\<mu>']) \<Midarrow>d'\<Rightarrow>\<^sup>* (p2,[])}"
          using \<open>(p1, [\<mu>]) \<Midarrow> d \<Rightarrow>\<^sup>* (p'', [\<mu>'])\<close> by fastforce
        also
        have "... \<le> \<^bold>\<Sum>{d'. (p1, [\<mu>]) \<Midarrow>d'\<Rightarrow>\<^sup>* (p2,[])}"
          by (smt (verit, best) Collect_mono_iff WPDS_with_W_automata.sum_mono monoid_rtranclp_trans)
        finally
        show "l \<le> \<^bold>\<Sum> {d'. (p1, [\<mu>]) \<Midarrow>d'\<Rightarrow>\<^sup>* (p2, [])}"
          using 3 4 by auto
      next
        fix \<mu>' \<mu>'' pi
        assume aa: "A $ (p'', \<mu>', pi) \<cdot> A $ (pi, \<mu>'', p2) = d'"
        assume "w' = push \<mu>' \<mu>''"
        define d1 where "d1 = A $ (p'', \<mu>', pi)"
        define d2 where "d2 = A $ (pi, \<mu>'', p2)"
        have "d' = d1 \<cdot> d2"
          using d1_def d2_def aa by auto
        have bb: "d1 \<le> \<^bold>\<Sum>{d'. (p'',[\<mu>']) \<Midarrow>d'\<Rightarrow>\<^sup>* (pi,[])}"
          using d1_def assms(1) sound_def by (force simp add: wts_to_monoidLTS_def)
         
        have cc: "d2 \<le> \<^bold>\<Sum>{d'. (pi,[\<mu>'']) \<Midarrow>d'\<Rightarrow>\<^sup>* (p2,[])}"
          using d2_def assms(1) sound_def  by (force simp add: wts_to_monoidLTS_def)
        have "d' = d1 \<cdot> d2"
          using \<open>d' = d1 \<cdot> d2\<close> .
        also
        have "... \<le> \<^bold>\<Sum>{d'. (p'',[\<mu>']) \<Midarrow>d'\<Rightarrow>\<^sup>* (pi,[])} \<cdot> \<^bold>\<Sum>{d'. (pi,[\<mu>'']) \<Midarrow>d'\<Rightarrow>\<^sup>* (p2,[])}"
          using bb cc Dioid.pre_dioid_class.mult_isol_var by auto
        also
        have "... \<le> \<^bold>\<Sum>{d1' \<cdot> d2'| d1'  d2'. (p'',[\<mu>']) \<Midarrow>d1'\<Rightarrow>\<^sup>* (pi,[]) \<and> (pi,[\<mu>'']) \<Midarrow>d2'\<Rightarrow>\<^sup>* (p2,[])}"
          by (simp add: sum_distr sum_of_sums_mult) 
        also
        have "... \<le> \<^bold>\<Sum>{d'. (p'',[\<mu>',\<mu>'']) \<Midarrow>d'\<Rightarrow>\<^sup>* (p2,[])}"
          by (smt (verit, ccfv_threshold) Collect_mono_iff WPDS_with_W_automata.sum_mono append_Cons 
              append_self_conv2 step_relp_seq)
        finally 
        have 6: "d' \<le> \<^bold>\<Sum>{d'. (p'',[\<mu>',\<mu>'']) \<Midarrow>d'\<Rightarrow>\<^sup>* (p2,[])}"
          .
        from 1 have "(p1,[\<mu>]) \<Midarrow>d\<Rightarrow>\<^sup>* (p'',[\<mu>',\<mu>''])"
          using \<open>w' = push \<mu>' \<mu>''\<close> monoid_rtranclp.monoid_rtrancl_into_rtrancl by fastforce
        have "d \<cdot> d' \<le> d \<cdot> \<^bold>\<Sum>{d'. (p'',[\<mu>',\<mu>'']) \<Midarrow>d'\<Rightarrow>\<^sup>* (p2,[])}"
          using 6 by (simp add: assms pre_dioid_class.mult_isol)
        also 
        have "... \<le> \<^bold>\<Sum>{d \<cdot> d'| d'. (p'',[\<mu>',\<mu>'']) \<Midarrow>d'\<Rightarrow>\<^sup>* (p2,[])}"
          by (simp add: sum_distr)
        also
        have "... \<le> \<^bold>\<Sum>{d \<cdot> d'| d'. (p1, [\<mu>]) \<Midarrow>d\<Rightarrow>\<^sup>* (p'',[\<mu>',\<mu>'']) \<and> (p'',[\<mu>',\<mu>'']) \<Midarrow>d'\<Rightarrow>\<^sup>* (p2,[])}"
          using \<open>(p1, [\<mu>]) \<Midarrow> d \<Rightarrow>\<^sup>* (p'', [\<mu>',\<mu>''])\<close> by fastforce
        also
        have "... \<le> \<^bold>\<Sum>{d'. (p1, [\<mu>]) \<Midarrow>d'\<Rightarrow>\<^sup>* (p2,[])}"
          by (smt (verit, ccfv_SIG) Collect_mono_iff WPDS_with_W_automata.sum_mono 
              monoid_rtranclp_trans)
        finally
        show "l \<le> \<^bold>\<Sum>{d'. (p1, [\<mu>]) \<Midarrow>d'\<Rightarrow>\<^sup>* (p2, [])}"
          using 3 4 by auto
      qed
    next
      case False
      then have "(p1, ([\<mu>], l), p2) \<in> wts_to_monoidLTS A"
        using ps(4) a unfolding wts_to_monoidLTS_def by auto
      then show ?thesis
        using assms unfolding sound_def by auto
    qed
  qed
qed

lemma monoid_rtrancl_split:
  assumes "(p, (v, d), p') \<in> monoid_rtrancl (wts_to_monoidLTS A')"
  obtains u w p'' d''' d' where
    "(p, (u, d'''), p'') \<in> monoid_rtrancl (wts_to_monoidLTS A')"
    "(p'', (w, d'), p') \<in> monoid_rtrancl (wts_to_monoidLTS A')"
    "v = u @ w \<and> \<gamma> \<notin> set w"
    "d = d''' \<cdot> d'"
  by (metis append_is_Nil_conv assms in_set_conv_decomp_first monoid_rtrancl.simps mult.right_neutral one_prod_def times_list_def)

lemma final_empty_accept':
  assumes "p \<in> finals"
  shows "accepts A (p,[]) = 1"
proof -
  have "{d | d q. q \<in> finals \<and> (p,([],d),q) \<in> monoidLTS.monoid_star (wts_to_monoidLTS A)} = {1}"
    by (smt (verit, ccfv_threshold) Collect_cong assms monoid_rtrancl.simps
        monoid_star_is_monoid_rtrancl mstar_wts_empty_one one_list_def one_prod_def singleton_conv)
  then show ?thesis
    by (simp add: WPDS_with_W_automata.accepts_def)
qed

lemma nonfinal_empty_accept':
  assumes "p \<notin> finals"
  shows "accepts A (p,[]) = 0"
proof -
  have "{d | d q. q \<in> finals \<and> (p,([],d),q) \<in> monoidLTS.monoid_star (wts_to_monoidLTS A)} = {}"
    by (smt (verit, del_insts) Collect_empty_eq WPDS.lbl.simps(1) WPDS_with_W_automata.monoid_star_pop assms)
    
  then show ?thesis
    by (smt (verit, ccfv_threshold) Collect_cong accepts_def old.prod.case sum_empty)
qed

lemma accepts_empty_iff: "accepts A (p,[]) = (if p\<in>finals then 1 else 0)"
  by (simp add: final_empty_accept' nonfinal_empty_accept')

lemma lemma_3_1_w_alternative:
  assumes "sound A"
  assumes "pre_star_rule A A'"
  shows "accepts A' pv \<le> weight_pre_star (accepts A) pv"
proof -
  have soundA': "sound A'"
    using soundness[of A A', OF assms] .

  obtain p v where pv_split: 
    "pv = (p, v)"
    by (cases pv)

  obtain pa \<gamma> d p' w d' q d'' where pa_p:
    "A' = A((pa, \<gamma>, q) $:= d'' + d \<cdot> d')"
    "(pa, \<gamma>) \<midarrow> d \<hookrightarrow> (p', w)"
    "(p', (lbl w, d'), q) \<in> monoidLTS.monoid_star (wts_to_monoidLTS A)"
    "A $ (pa, \<gamma>, q) = d''"
    "d'' + d \<cdot> d' \<noteq> d''"
    using pre_star_rule.cases[of A A', OF assms(2)] by metis

  have "accepts A' (p,v) = \<^bold>\<Sum>{d |d q. q \<in> finals \<and> (p, (v, d), q) \<in> monoid_rtrancl (wts_to_monoidLTS A')}" (* 1, 2 *)
    unfolding accepts_def by (simp split: prod.split) 
  also
  have "... \<le> \<^bold>\<Sum>{\<^bold>\<Sum>{d'. (p,v) \<Midarrow>d'\<Rightarrow>\<^sup>* (q,[])} |d q. q \<in> finals \<and> (p, (v, d), q) \<in> monoid_rtrancl (wts_to_monoidLTS A')}" (* 5 *)
    using sum_bigger2[of 
        "\<lambda>(d, q). q \<in> finals \<and> (p, (v, d), q) \<in> monoid_rtrancl (wts_to_monoidLTS A')"
        "\<lambda>(d, q). d"
        "\<lambda>(d, q). \<^bold>\<Sum>{d'. (p,v) \<Midarrow>d'\<Rightarrow>\<^sup>* (q,[])}"
        ]
    using monoid_star_is_monoid_rtrancl soundA' sound_def2 by force
  also
  have "... \<le> \<^bold>\<Sum>{\<^bold>\<Sum>{d'. (p,v) \<Midarrow>d'\<Rightarrow>\<^sup>* (p',[])} | p'. p' \<in> finals}"
    by (smt (verit) Collect_mono_iff WPDS_with_W_automata.sum_mono) (* 6 *)
  also
  have "... = \<^bold>\<Sum>{d' |d' p'. p' \<in> finals \<and> (p,v) \<Midarrow>d'\<Rightarrow>\<^sup>* (p',[])}" (* 7 *)
    using sum_of_sums_mult2[of "\<lambda>d p'. d" "\<lambda>d p'. (p,v) \<Midarrow>d\<Rightarrow>\<^sup>* (p',[])" "\<lambda>p'. 1" "\<lambda>p'. p' \<in> finals"]
    apply auto
    by (smt (verit) Collect_cong Orderings.order_eq_iff)
  also
  have "... \<le> \<^bold>\<Sum>{d' \<cdot> (if p'\<in>finals then 1 else 0)| d' p'. (p,v) \<Midarrow>d'\<Rightarrow>\<^sup>* (p',[])}"
    by (smt (verit) Collect_mono_iff WPDS_with_W_automata.sum_mono mult.right_neutral)
  also
  have "... = \<^bold>\<Sum>{d' \<cdot> accepts A (p',[])| d' p'. (p,v) \<Midarrow>d'\<Rightarrow>\<^sup>* (p',[])}"
    unfolding accepts_empty_iff by auto (* 13 *)
  also
  have "... \<le> \<^bold>\<Sum>{d' \<cdot> accepts A c'| d' c'. (p,v) \<Midarrow>d'\<Rightarrow>\<^sup>* c'}"
    by (smt (verit) Collect_mono_iff WPDS_with_W_automata.sum_mono)
  also
  have "... = weight_pre_star (accepts A) (p,v)"
    by (simp add: weight_pre_star_def) (* 14 *)
  finally
  show ?thesis
    unfolding pv_split by auto
qed

lemma lemma_3_1_w_alternative': 
  assumes "sound A"
  assumes "pre_star_rule A A'"
  shows "accepts A' \<le> weight_pre_star (accepts A)"
  by (simp add: assms le_funI lemma_3_1_w_alternative)

lemma nice_lemma:
   "X c \<le> weight_pre_star X c"
proof -
  have "X c \<le> 1 \<cdot> X c"
    by simp
  have "... \<le> \<^bold>\<Sum> {1 \<cdot> X c}"
    by simp
  also have "... \<le> \<^bold>\<Sum> {l \<cdot> X c |l. c \<Midarrow> l \<Rightarrow>\<^sup>* c}"
    by (smt (verit, del_insts) bot.extremum insert_subsetI local.sum_mono mem_Collect_eq monoid_rtranclp.monoid_rtrancl_refl)
  also have "... \<le> \<^bold>\<Sum> {l \<cdot> X c' |l c'. c \<Midarrow> l \<Rightarrow>\<^sup>* c'}"
    by (smt (verit) Collect_mono WPDS_with_W_automata.sum_mono)
  also have "... = weight_pre_star X c"
    unfolding weight_pre_star_def by auto
  finally
  show ?thesis
    by auto
qed

lemma nice_lemma2:
  "X \<le> weight_pre_star X"
  by (simp add: le_fun_def nice_lemma)

lemma nice_lemma3:
  "weight_pre_star (weight_pre_star (accepts A)) c = (weight_pre_star (accepts A)) c"
proof -
  have "weight_pre_star (weight_pre_star (accepts A)) c = \<^bold>\<Sum> {l \<cdot> \<^bold>\<Sum> {l' \<cdot> accepts A c'' |l' c''. c' \<Midarrow> l' \<Rightarrow>\<^sup>* c''} |l c'. c \<Midarrow> l \<Rightarrow>\<^sup>* c'}"
    unfolding weight_pre_star_def by meson
  also
  have "... =  \<^bold>\<Sum> {\<^bold>\<Sum> {l \<cdot> l' \<cdot> accepts A c'' |l' c''. c' \<Midarrow> l' \<Rightarrow>\<^sup>* c''} |l c'. c \<Midarrow> l \<Rightarrow>\<^sup>* c'}"
  proof -
    {
      fix l c'
      have "l \<cdot> \<^bold>\<Sum> {l' \<cdot> accepts A c'' |l' c''. c' \<Midarrow> l' \<Rightarrow>\<^sup>* c''} = \<^bold>\<Sum> {l \<cdot> l' \<cdot> accepts A c'' |l' c''. c' \<Midarrow> l' \<Rightarrow>\<^sup>* c''}"
        using sum_distr[of l "{l' \<cdot> accepts A c'' |l' c''. c' \<Midarrow> l' \<Rightarrow>\<^sup>* c''}"]
        apply (auto)
        by (metis (no_types, opaque_lifting) mult.assoc)
    }
    then show ?thesis
      by auto
  qed
  also
  have "... = \<^bold>\<Sum> {l \<cdot> l' \<cdot> accepts A c'' |l' c'' l c'. c' \<Midarrow> l' \<Rightarrow>\<^sup>* c'' \<and> c \<Midarrow> l \<Rightarrow>\<^sup>* c'}"
    using sum_of_sums2[of
        "\<lambda>(l',c'') (l,c'). l \<cdot> l' \<cdot> accepts A c''"
        "\<lambda>(l',c'') (l,c').  c' \<Midarrow> l' \<Rightarrow>\<^sup>* c''"
        "\<lambda>(l,c'). c \<Midarrow> l \<Rightarrow>\<^sup>* c'"] by auto
  also
  have "... = \<^bold>\<Sum> {l \<cdot> l' \<cdot> accepts A c'' |l' c'' l c'. c \<Midarrow> l \<Rightarrow>\<^sup>* c' \<and> c' \<Midarrow> l' \<Rightarrow>\<^sup>* c''}"
    by meson
  also
  have "... = \<^bold>\<Sum> {l'' \<cdot> accepts A c'' |l'' c''. c \<Midarrow> l'' \<Rightarrow>\<^sup>* c''}"
    by (smt (verit, ccfv_threshold) Collect_cong monoid_rtranclp.monoid_rtrancl_refl monoid_rtranclp_trans mult_1)
  also
  have "... = (weight_pre_star (accepts A)) c"
    by (simp add: dioidLTS.weight_pre_star_def)
  finally
  show "?thesis"
    .
qed

lemma nice_lemma4:
  "weight_pre_star (weight_pre_star (accepts A)) = (weight_pre_star (accepts A))"
  using nice_lemma3 by auto

lemma weight_pre_star_mono:
  assumes "X \<le> Y"
  shows "weight_pre_star X c \<le> weight_pre_star Y c"
  using assms unfolding weight_pre_star_def
  apply auto
  apply (subgoal_tac "\<forall>a b. X (a,b) \<le> Y (a,b)")
  subgoal
    using sum_bigger2[of "\<lambda>(l, a, b). c \<Midarrow> l \<Rightarrow>\<^sup>* (a, b)" "\<lambda>(l, a, b). l  \<cdot> X (a, b)"
        "\<lambda>(l, a, b). l  \<cdot> Y (a, b)"]
    apply auto
    using pre_dioid_class.mult_isol apply blast
    done
  subgoal
    apply (simp add: le_funD)
    done
  done

lemma lemma_3_1_w_alternative'':
  assumes "sound A"
  assumes "pre_star_rule\<^sup>*\<^sup>* A A'"
  shows "accepts A' \<le> weight_pre_star (accepts A)"
using assms(2,1) proof (induction)
  case base
  then show ?case
    by (simp add: nice_lemma2)
next
  case (step A' A'')
  then have "accepts A'' \<le> weight_pre_star (accepts A')"
    using lemma_3_1_w_alternative'[of A' A'']
    by (smt (verit, best) local.soundness rtranclp_induct) 
  moreover
  from step(3) have "weight_pre_star (accepts A') \<le> weight_pre_star (weight_pre_star (accepts A))"
    by (simp add: le_fun_def step.prems weight_pre_star_mono)
  then have "weight_pre_star (accepts A') \<le> weight_pre_star (accepts A)"
    using nice_lemma4 by auto
  ultimately
  show ?case
    by auto
qed

end

end
