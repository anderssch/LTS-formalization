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


\<comment> \<open>Generalization of PDS_with_P_automata.accepts that computes the meet-over-all-paths in the W-automaton.\<close>
definition accepts :: "('ctr_loc, 'label, 'weight) w_transitions \<Rightarrow> ('ctr_loc, 'label) conf \<Rightarrow> 'weight" where
  "accepts ts \<equiv> \<lambda>(p,w). (\<Sum>{d | d q. q \<in> finals \<and> (p,(w,d),q) \<in> monoidLTS.monoid_star (wts_to_monoidLTS ts)})"


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
  "sound A \<longleftrightarrow> (\<forall>p p' \<gamma> d. (p, ([\<gamma>],d), p') \<in> (wts_to_monoidLTS A) \<longrightarrow> d \<le> \<Sum>{d'. (p,[\<gamma>]) \<Midarrow>d'\<Rightarrow>\<^sup>* (p',[])})"



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
  assumes "(\<forall>p p' w d. (p, (w,d), p') \<in> monoidLTS.monoid_star (wts_to_monoidLTS A) \<longrightarrow> d \<le> \<Sum>{d'. (p,w) \<Midarrow>d'\<Rightarrow>\<^sup>* (p',[])})"
  assumes "(p, ([\<gamma>],d), p') \<in> (wts_to_monoidLTS A)"
  shows "d \<le> \<Sum>{d'. (p,[\<gamma>]) \<Midarrow>d'\<Rightarrow>\<^sup>* (p',[])}"
proof -
  have "(p, ([\<gamma>],d), p') \<in> monoidLTS.monoid_star (wts_to_monoidLTS A)"
    using assms(2) monoid_star_intros_step by blast
  then show "d \<le> \<Sum>{d'. (p,[\<gamma>]) \<Midarrow>d'\<Rightarrow>\<^sup>* (p',[])}"
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

lemma sound_def2':
  assumes "sound A"
  assumes "(p, (w,d), p') \<in> monoidLTS.monoid_star (wts_to_monoidLTS A)"
  shows "d \<le> \<Sum>{d'. (p,w) \<Midarrow>d'\<Rightarrow>\<^sup>* (p',[])}"
  using assms(2) 
proof (induction w arbitrary: d p)
  case Nil
  then have "d = 1"
    by (simp add: baba)
  have "(p, []) \<Midarrow> 1 \<Rightarrow>\<^sup>* (p', [])"
    by (metis WPDS.lbl.simps(1) WPDS_with_W_automata.monoid_star_pop local.Nil monoid_rtranclp.simps)
  have "d \<le> \<Sum> {d'. d' = 1 \<and> (p, []) \<Midarrow> 1 \<Rightarrow>\<^sup>* (p', [])}"
    sorry
  also
  have "... \<le> \<Sum> {d'. (p, []) \<Midarrow> d' \<Rightarrow>\<^sup>* (p', [])}"
    sorry
  finally 
  show ?case 
    .
next
  case (Cons a w)
  from Cons(2) obtain pi d1 d2 where
    "d = d1 \<cdot> d2"
    "(pi, (w, d2), p') \<in> monoidLTS.monoid_star (wts_to_monoidLTS A)"
    "(p, ([a], d1), pi) \<in> (wts_to_monoidLTS A)"
    sorry
  then have d2l: "d2 \<le> \<Sum> {d'. (pi, w) \<Midarrow> d' \<Rightarrow>\<^sup>* (p', [])}" 
    using Cons(1)[of pi d2] by auto
  have "d = d1 \<cdot> d2"
    using \<open>d = d1 \<cdot> d2\<close> . 
  also have "... \<le> d1 \<cdot> \<Sum> {d'. (pi, w) \<Midarrow> d' \<Rightarrow>\<^sup>* (p', [])}"
    using d2l pre_dioid_class.mult_isol[of d2 "\<Sum> {d'. (pi, w) \<Midarrow> d' \<Rightarrow>\<^sup>* (p', [])}" d1]  by auto
  also have "... \<le>  \<Sum> {d1 \<cdot> d'| d'. (pi, w) \<Midarrow> d' \<Rightarrow>\<^sup>* (p', [])}"
    sorry
  also have "... \<le>  \<Sum> {d1 \<cdot> d'| d'. (p, [a]) \<Midarrow> d1 \<Rightarrow>\<^sup>* (pi, []) \<and> (pi, w) \<Midarrow> d' \<Rightarrow>\<^sup>* (p', [])}"
    sorry
  also have "... \<le>  \<Sum> {d'. (p, a # w) \<Midarrow> d' \<Rightarrow>\<^sup>* (p', [])}"
    sorry
  finally
  show ?case
    .
qed

lemma sound_def2:
  "sound A \<longleftrightarrow> (\<forall>p p' w d. (p, (w,d), p') \<in> monoidLTS.monoid_star (wts_to_monoidLTS A) \<longrightarrow> d \<le> \<Sum>{d'. (p,w) \<Midarrow>d'\<Rightarrow>\<^sup>* (p',[])})"
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
    show "l \<le> \<Sum> {d'. (p1, [\<mu>]) \<Midarrow> d' \<Rightarrow>\<^sup>* (p2, [])}"
    proof (cases "p1 = p' \<and> \<mu> = \<gamma>' \<and> p2 = q")
      case True
      then have True1: "p1 = p'" "\<mu> = \<gamma>'" "p2 = q"
        by auto
      have 4: "l = d'' + d \<cdot> d'"
        using a unfolding ps(4) True1 unfolding wts_to_monoidLTS_def by auto
      have 3: "d'' \<le> \<Sum>{d'. (p1,[\<mu>]) \<Midarrow>d'\<Rightarrow>\<^sup>* (p2,[])}"
        using ps(5) using assms(1) unfolding sound_def unfolding wts_to_monoidLTS_def
        apply -
        apply (cases "d'' \<noteq> 0")
        subgoal
          apply (simp add: wts_to_monoidLTS_def)
          using True apply blast
          done
        subgoal
          apply force
          done
        done
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
        then have "d \<cdot> d' \<le> \<Sum>{d'. (p1, [\<mu>]) \<Midarrow> d'\<Rightarrow>\<^sup>* (p2,[])}"
          sorry
        then show "l \<le> \<Sum> {d'. (p1, [\<mu>]) \<Midarrow>d'\<Rightarrow>\<^sup>* (p2, [])}"
          using 3 4 by auto
      next
        fix \<mu>'
        assume "A $ (p'', \<mu>', p2) = d'"
        assume 5: "w' = swap \<mu>'"
        from 2 have "(p'', ([\<mu>'],d'), p2) \<in> monoidLTS.monoid_star (wts_to_monoidLTS A)"
          using True1(3) \<open>w' = swap \<mu>'\<close> by force
        then have 6: "d' \<le> \<Sum>{d'. (p'',[\<mu>']) \<Midarrow>d'\<Rightarrow>\<^sup>* (p2,[])}"
          using assms(1) unfolding sound_def
          using \<open>A $ (p'', \<mu>', p2) = d'\<close> join.bot.extremum mem_Collect_eq wts_to_monoidLTS_def by fastforce
        from 1 have "(p1, [\<mu>]) \<Midarrow>d\<Rightarrow>\<^sup>* (p'',[\<mu>'])"
          unfolding True1 5 using monoid_rtranclp.monoid_rtrancl_into_rtrancl by fastforce
        have "d \<cdot> d' \<le> d \<cdot> \<Sum>{d'. (p'',[\<mu>']) \<Midarrow>d'\<Rightarrow>\<^sup>* (p2,[])}"
          using 6 by (simp add: assms pre_dioid_class.mult_isol)
        also 
        have "... \<le>  \<Sum>{d \<cdot> d'| d'. (p'',[\<mu>']) \<Midarrow>d'\<Rightarrow>\<^sup>* (p2,[])}"
          sorry
        also
        have "... \<le> \<Sum>{d \<cdot> d'| d'. (p1, [\<mu>]) \<Midarrow>d\<Rightarrow>\<^sup>* (p'',[\<mu>']) \<and> (p'',[\<mu>']) \<Midarrow>d'\<Rightarrow>\<^sup>* (p2,[])}"
          using \<open>(p1, [\<mu>]) \<Midarrow> d \<Rightarrow>\<^sup>* (p'', [\<mu>'])\<close> by fastforce
        also
        have "... \<le> \<Sum>{d'. (p1, [\<mu>]) \<Midarrow>d'\<Rightarrow>\<^sup>* (p2,[])}"
          sorry
        finally
        show "l \<le> \<Sum> {d'. (p1, [\<mu>]) \<Midarrow>d'\<Rightarrow>\<^sup>* (p2, [])}"
          using 3 4 by auto
      next
        fix \<mu>' \<mu>'' pi
        assume aa: "A $ (p'', \<mu>', pi) \<cdot> A $ (pi, \<mu>'', p2) = d'"
        assume "w' = push \<mu>' \<mu>''"
        define d1 where "d1 = A $ (p'', \<mu>', pi)"
        define d2 where "d2 = A $ (pi, \<mu>'', p2)"
        have "d' = d1 \<cdot> d2"
          using d1_def d2_def aa by auto
        have bb: "d1 \<le> \<Sum>{d'. (p'',[\<mu>']) \<Midarrow>d'\<Rightarrow>\<^sup>* (pi,[])}"
          using d1_def assms(1) sound_def 
          apply -
          apply (cases "d1 \<noteq> 0")
          subgoal
            apply (simp add: wts_to_monoidLTS_def)
            done
          subgoal
            apply force
            done
          done
        have cc: "d2 \<le> \<Sum>{d'. (pi,[\<mu>'']) \<Midarrow>d'\<Rightarrow>\<^sup>* (p2,[])}"
          using d2_def assms(1) sound_def 
          apply -
          apply (cases "d2 \<noteq> 0")
          subgoal
            apply (simp add: wts_to_monoidLTS_def)
            done
          subgoal
            apply force
            done
          done
        have "d' = d1 \<cdot> d2"
          using \<open>d' = d1 \<cdot> d2\<close> .
        also
        have "... \<le> \<Sum>{d'. (p'',[\<mu>']) \<Midarrow>d'\<Rightarrow>\<^sup>* (pi,[])} \<cdot> \<Sum>{d'. (pi,[\<mu>'']) \<Midarrow>d'\<Rightarrow>\<^sup>* (p2,[])}"
          using bb cc Dioid.pre_dioid_class.mult_isol_var by auto
        also
        have "... \<le> \<Sum>{d1' \<cdot> d2'| d1'  d2'. (p'',[\<mu>']) \<Midarrow>d1'\<Rightarrow>\<^sup>* (pi,[]) \<and> (pi,[\<mu>'']) \<Midarrow>d2'\<Rightarrow>\<^sup>* (p2,[])}"
          sorry
        also
        have "... \<le> \<Sum>{d'. (p'',[\<mu>',\<mu>'']) \<Midarrow>d'\<Rightarrow>\<^sup>* (p2,[])}"
          sorry
        finally 
        have 6: "d' \<le> \<Sum>{d'. (p'',[\<mu>',\<mu>'']) \<Midarrow>d'\<Rightarrow>\<^sup>* (p2,[])}"
          .
        from 1 have "(p1,[\<mu>]) \<Midarrow>d\<Rightarrow>\<^sup>* (p'',[\<mu>',\<mu>''])"
          using \<open>w' = push \<mu>' \<mu>''\<close> monoid_rtranclp.monoid_rtrancl_into_rtrancl by fastforce
        have "d \<cdot> d' \<le> d \<cdot> \<Sum>{d'. (p'',[\<mu>',\<mu>'']) \<Midarrow>d'\<Rightarrow>\<^sup>* (p2,[])}"
          using 6 by (simp add: assms pre_dioid_class.mult_isol)
        also 
        have "... \<le>  \<Sum>{d \<cdot> d'| d'. (p'',[\<mu>',\<mu>'']) \<Midarrow>d'\<Rightarrow>\<^sup>* (p2,[])}"
          sorry
        also
        have "... \<le> \<Sum>{d \<cdot> d'| d'. (p1, [\<mu>]) \<Midarrow>d\<Rightarrow>\<^sup>* (p'',[\<mu>',\<mu>'']) \<and> (p'',[\<mu>',\<mu>'']) \<Midarrow>d'\<Rightarrow>\<^sup>* (p2,[])}"
          using \<open>(p1, [\<mu>]) \<Midarrow> d \<Rightarrow>\<^sup>* (p'', [\<mu>',\<mu>''])\<close> by fastforce
        also
        have "... \<le> \<Sum>{d'. (p1, [\<mu>]) \<Midarrow>d'\<Rightarrow>\<^sup>* (p2,[])}"
          sorry
        finally
        show "l \<le> \<Sum> {d'. (p1, [\<mu>]) \<Midarrow>d'\<Rightarrow>\<^sup>* (p2, [])}"
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

end


end