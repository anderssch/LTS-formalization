theory WPDS
  imports "Labeled_Transition_Systems.LTS" "Saturation" "FinFunWellFounded" "FinFunAddUpdate" "WAutomaton" "FiniteMonoidLTS" "Pushdown_Systems.P_Automata"
begin


section \<open>WPDS definitions and data types\<close>

datatype 'label operation = pop | swap 'label | push 'label 'label

\<comment> \<open>WPDS has a @{typ "'weight::bounded_dioid"} on the rule.\<close>
type_synonym ('ctr_loc, 'label) rule = "('ctr_loc \<times> 'label) \<times> ('ctr_loc \<times> 'label operation)"

type_synonym ('ctr_loc, 'label, 'weight) w_rule = "('ctr_loc \<times> 'label) \<times> 'weight \<times> ('ctr_loc \<times> 'label operation)"

type_synonym ('ctr_loc, 'label) conf = "'ctr_loc \<times> 'label list"

\<comment> \<open>Instantiation: Enumerability of operations\<close>
instance operation :: (finite) finite proof
  have "finite (UNIV::'a::finite set)" by simp
  then have "finite ({pop} \<union> range swap \<union> range (\<lambda>(a::'a,b). push a b))" by simp
  moreover have "(UNIV::'a operation set) = {pop} \<union> range swap \<union> range (\<lambda>(a,b). push a b)"
    by (auto, metis prod.case operation.exhaust rangeI)
  ultimately show "finite (UNIV::'a operation set)" by argo
qed

instantiation operation :: (enum) enum begin

definition enum_a :: "'a list" where 
  "enum_a = enum_class.enum"
definition enum_all_a :: "('a \<Rightarrow> bool) \<Rightarrow> bool" where
  "enum_all_a = enum_class.enum_all"
definition enum_ex_a :: "('a \<Rightarrow> bool) \<Rightarrow> bool" where
  "enum_ex_a = enum_class.enum_ex"
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


section \<open>Locale: dioidLTS -- acceptance\<close>
\<comment> \<open>Generalization of PDS_with_P_automata.accepts that computes the meet-over-all-paths in the W-automaton.\<close>

context dioidLTS begin

definition accepts :: "('ctr_loc, 'label, 'weight) w_transitions \<Rightarrow> 'ctr_loc set \<Rightarrow> ('ctr_loc, 'label) conf \<Rightarrow> 'weight" where
  "accepts ts finals \<equiv> \<lambda>(p,w). (\<^bold>\<Sum>{d | d q. q \<in> finals \<and> (p,(w,d),q) \<in> \<lbrakk>ts\<rbrakk>\<^sup>\<odot>})"

context fixes finals :: "'ctr_loc::finite set" begin
abbreviation accepts' ("\<L> (_)" [1000] 1000) where "\<L>(ts) \<equiv> accepts ts finals"

lemma accepts_step_distrib:
  fixes ts :: "('ctr_loc, 'label::finite, 'weight::bounded_dioid) w_transitions"
  shows "\<^bold>\<Sum>{d * (\<L>(ts) (q1,w))| q1 d. (p,([\<gamma>],d),q1) \<in> \<lbrakk>ts\<rbrakk>} = \<L>(ts) (p,\<gamma>#w)"
proof -
  have "finite \<lbrakk>ts\<rbrakk>"
    by (simp add: finite_wts)
  then have "finite {(p, ([\<gamma>], d), q1) | d q1. (p, ([\<gamma>], d), q1) \<in> \<lbrakk>ts\<rbrakk>}"
    by (rule rev_finite_subset) auto
  then have "finite ((\<lambda>(p, (\<gamma>, d), q1). (q1, d)) ` {(p, ([\<gamma>], d), q1) |d q1. (p, ([\<gamma>], d), q1) \<in> \<lbrakk>ts\<rbrakk>})"
    using finite_imageI by auto
  then have "finite {(q1, d) | q1 d. (p, ([\<gamma>], d), q1) \<in> \<lbrakk>ts\<rbrakk>}"
    by (rule back_subst[of finite]) (auto simp add: image_def)
  then have count1: "countable {(q1, d) | q1 d. (p, ([\<gamma>], d), q1) \<in> \<lbrakk>ts\<rbrakk>}"
    using countable_finite by auto

  have count2:
    "(\<And>q1 :: 'ctr_loc. \<And>d :: 'weight.
         countable {((q, b), (q1, d)) |q b. q \<in> finals \<and> ((q1, (w, b), q) \<in> \<lbrakk>ts\<rbrakk>\<^sup>\<odot>)})"
  proof -
    fix q1 :: 'ctr_loc
    fix d :: 'weight
    have "countable (\<lbrakk>ts\<rbrakk>\<^sup>\<odot>)"
      using countable_monoid_rtrancl countable_wts by blast
    then have "countable {(q1, (w, b), q) |q b. q \<in> finals \<and> (q1, (w, b), q) \<in> \<lbrakk>ts\<rbrakk>\<^sup>\<odot>}"
      by (rule rev_countable_subset) auto
    then have "countable ((\<lambda>(q1, (w, b), q). ((q, b), (q1, d))) ` {(q1, (w, b), q) |q b. q \<in> finals \<and> (q1, (w, b), q) \<in> \<lbrakk>ts\<rbrakk>\<^sup>\<odot>})"
      using countable_image by fastforce
    then show "countable {((a, b), (q1, d)) |a b. a \<in> finals \<and> ((q1, (w, b), a) \<in> \<lbrakk>ts\<rbrakk>\<^sup>\<odot>)}"
      by (rule rev_countable_subset) (auto simp add: image_def)
  qed

  have "\<^bold>\<Sum>{d * (\<L>(ts) (q,w))| q d. (p,([\<gamma>],d),q) \<in> \<lbrakk>ts\<rbrakk>} =
        \<^bold>\<Sum> {d * (\<^bold>\<Sum> {u | q u. q \<in> finals \<and> (q1, (w, u), q) \<in> \<lbrakk>ts\<rbrakk>\<^sup>\<odot>}) |q1 d. (p, ([\<gamma>], d), q1) \<in> \<lbrakk>ts\<rbrakk>}"
    unfolding dioidLTS.accepts_def by auto
  also
  have "... = \<^bold>\<Sum> {d * u | q u q1 d. q \<in> finals \<and> (q1, (w, u), q) \<in> \<lbrakk>ts\<rbrakk>\<^sup>\<odot> \<and> (p, ([\<gamma>], d), q1) \<in> \<lbrakk>ts\<rbrakk>}"
    using SumInf_of_SumInf_left_distr[of "\<lambda>(q1,d). (p, ([\<gamma>], d), q1) \<in> \<lbrakk>ts\<rbrakk>" "\<lambda>(q,u) (q1,d). q \<in> finals \<and> (q1, (w, u), q) \<in> \<lbrakk>ts\<rbrakk>\<^sup>\<odot>"
    "\<lambda>(q1,d). d" "\<lambda>(q,u) (q1,d). u",simplified] count1 count2 by auto
  also
  have "... = \<^bold>\<Sum> {d * u | q u q1 d. q \<in> finals \<and> (p, ([\<gamma>], d), q1) \<in> \<lbrakk>ts\<rbrakk> \<and> (q1, (w, u), q) \<in> \<lbrakk>ts\<rbrakk>\<^sup>\<odot>}"
    by meson
  also
  have "... = (\<^bold>\<Sum> {d' | d' q. q \<in> finals \<and> (p, (\<gamma> # w, d'), q) \<in> \<lbrakk>ts\<rbrakk>\<^sup>\<odot>})"
    apply (rule arg_cong[of _ _ "\<^bold>\<Sum>"])
    using monoid_rtrancl_intros_Cons mstar_wts_cons apply fastforce
    done
  also
  have "... = \<L>(ts) (p,\<gamma>#w)"
    unfolding accepts_def by auto

  finally show ?thesis 
    by auto
qed


lemma accepts_def2:
  "\<L>(ts) (p,w) = (\<^bold>\<Sum>{d | d q. q \<in> finals \<and> (p,(w,d),q) \<in> \<lbrakk>ts\<rbrakk>\<^sup>\<odot>})"
  using accepts_def[of ts] by auto

lemma accept_is_one_if_final_empty:
  assumes "p \<in> finals"
  shows "\<L>(A) (p,[]) = 1"
proof -
  have "{d | d q. q \<in> finals \<and> (p,([],d),q) \<in> \<lbrakk>A\<rbrakk>\<^sup>\<odot>} = {1}"
    using Collect_cong[of "\<lambda>d. \<exists>q. q \<in> finals \<and> (p, ([], d), q) \<in> \<lbrakk>A\<rbrakk>\<^sup>\<odot>" "\<lambda>d. d = 1"]
      assms monoid_rtrancl_wts_to_monoidLTS_refl mstar_wts_empty_one by force
  then show ?thesis
    by (simp add: accepts_def)
qed

lemma accept_is_zero_if_nonfinal_empty:
  fixes A::"('ctr_loc \<times> 'label \<times> 'ctr_loc) \<Rightarrow>f 'weight"
  assumes "p \<notin> finals"
  shows "\<L>(A) (p,[]) = 0"
proof -
  have "{d | d q. q \<in> finals \<and> (p,([],d),q) \<in> \<lbrakk>A\<rbrakk>\<^sup>\<odot>} = {}"
    using assms monoid_star_w0[of p _ _ A] by fastforce
  then show ?thesis
    unfolding accepts_def2 using SumInf_empty 
      Collect_cong[of "\<lambda>d. \<exists>q. q \<in> finals \<and> (p, ([], d), q) \<in> \<lbrakk>A\<rbrakk>\<^sup>\<odot>"
        "\<lambda>d. \<exists>q. q \<in> finals \<and> (p, ([], d), q) \<in> \<lbrakk>A\<rbrakk>\<^sup>\<odot>"] by metis
qed

lemma zero_weight_if_nonrefl_path_in_K0:
  "(p,wd,q) \<in> \<lbrakk>K$ 0\<rbrakk>\<^sup>\<odot>\<Longrightarrow> p \<noteq> q \<Longrightarrow> snd wd = 0"
proof (induct rule: monoid_rtrancl_induct_rev)
  case (monoid_rtrancl_refl p)
  then show ?case by auto
next
  case (monoid_rtrancl_into_rtrancl p w p' q wd')
  show ?case 
  proof (cases "p' \<noteq> q")
    case True
    then show ?thesis
      using monoid_rtrancl_into_rtrancl by simp
  next
    case False
    then show ?thesis
      by (metis finfun_const_apply monoid_rtrancl_into_rtrancl.hyps(1) mult_prod_def mult_zero_left 
          snd_conv wts_label_d')
  qed
qed

lemma zero_weight_if_nonempty_word_in_K0:
  "(p,wd,q) \<in> \<lbrakk>K$ 0\<rbrakk>\<^sup>\<odot>\<Longrightarrow> fst wd \<noteq> [] \<Longrightarrow> snd wd = 0"
proof (induct rule: monoid_rtrancl_induct_rev)
  case (monoid_rtrancl_refl p)
  then show ?case 
    by (simp add: one_list_def one_prod_def)
next
  case (monoid_rtrancl_into_rtrancl p w p' q wd')
  show ?case 
  proof (cases "fst wd' \<noteq> []")
    case True
    then show ?thesis
      using monoid_rtrancl_into_rtrancl by simp
  next
    case False
    then show ?thesis
      by (metis finfun_const_apply monoid_rtrancl_into_rtrancl.hyps(1) mult_prod_def mult_zero_left 
          snd_conv wts_label_d')
  qed
qed

lemma accepts_K0_is_zero_if_nonfinal:
  assumes "p \<notin> finals"
  shows "\<L>(K$ 0) (p,w) = 0"
proof -
  have "{d :: 'weight. \<exists>q. q \<in> finals \<and> (p, (w, d), q) \<in> \<lbrakk>K$ 0\<rbrakk>\<^sup>\<odot>} \<subseteq> {0}"
    using zero_weight_if_nonrefl_path_in_K0[of p "(w,_)" _] assms by auto
  then show ?thesis
    unfolding accepts_def by auto
qed

lemma accepts_K0_is_zero_if_nonempty:
  assumes "w \<noteq> []"
  shows "\<L>(K$ 0) (p,w) = 0"
proof -
  have "{d :: 'weight. \<exists>q. q \<in> finals \<and> (p, (w, d), q) \<in> \<lbrakk>K$ 0\<rbrakk>\<^sup>\<odot>} \<subseteq> {0}"
    using zero_weight_if_nonempty_word_in_K0[of p "(w,_)" _] assms by auto
  then show ?thesis
    unfolding accepts_def by auto
qed

lemma accepts_empty_iff: 
  fixes A::"('ctr_loc \<times> 'label \<times> 'ctr_loc) \<Rightarrow>f 'weight"
  shows "\<L>(A) (p,[]) = (if p\<in>finals then 1 else 0)"
  by (simp add: accept_is_one_if_final_empty accept_is_zero_if_nonfinal_empty)

lemma accepts_K0_iff[simp]: "\<L>(K$ 0) (p,w) = (if p\<in>finals \<and> w = [] then 1 else 0)"
  by (metis accept_is_one_if_final_empty accepts_K0_is_zero_if_nonfinal accepts_K0_is_zero_if_nonempty)

lemma accepts_1_if_monoid_rtrancl_1:
  fixes ts :: "('ctr_loc::finite, 'label::finite) transition set"
  assumes "finite ts"
  assumes "(p, (v, 1 :: 'weight::bounded_dioid), q) \<in> \<lbrakk>ts_to_wts ts\<rbrakk>\<^sup>\<odot>"
  assumes "q \<in> finals"
  shows "\<L>(ts_to_wts ts) (p, v) = (1::'weight)"
proof -
  have "\<And>q d. q \<in> finals \<Longrightarrow> (p, (v, d), q) \<in> \<lbrakk>ts_to_wts ts\<rbrakk>\<^sup>\<odot> \<Longrightarrow> d = (1::'weight) \<or> d = 0"
    by (simp add: binary_aut_path_binary ts_to_wts_bin)
  then have "{d. \<exists>q. q \<in> finals \<and> (p, (v, d), q) \<in> \<lbrakk>ts_to_wts ts\<rbrakk>\<^sup>\<odot>} \<subseteq> {1 ::'weight, 0}"
    by blast
  moreover
  have "(p, (v, 1 :: 'weight), q) \<in> \<lbrakk>ts_to_wts ts\<rbrakk>\<^sup>\<odot>"
    using assms(2) by auto
  then have "(1 :: 'weight) \<in> {d. \<exists>q. q \<in> finals \<and> (p, (v, d), q) \<in> \<lbrakk>ts_to_wts ts\<rbrakk>\<^sup>\<odot>}"
    using assms by auto
  ultimately
  have "{d. \<exists>q. q \<in> finals \<and> (p, (v, d), q) \<in> \<lbrakk>ts_to_wts ts\<rbrakk>\<^sup>\<odot>} = {1 :: 'weight, 0} \<or> {d. \<exists>q. q \<in> finals \<and> (p, (v, d), q) \<in> \<lbrakk>ts_to_wts ts\<rbrakk>\<^sup>\<odot>} = {1 :: 'weight}"
    by blast
  moreover
  have "finite {1::'weight, 0}"
    by auto
  moreover
  have "\<Sum> {1::'weight, 0} = (1::'weight)"
    by (simp add: finite_SumInf_is_sum)
  ultimately
  have "\<^bold>\<Sum> {d. \<exists>q.  q \<in> finals \<and> (p, (v, d), q) \<in> \<lbrakk>ts_to_wts ts\<rbrakk>\<^sup>\<odot>} = (1::'weight)"
    by (auto simp add: finite_SumInf_is_sum)
  then show ?thesis
    by (simp add: dioidLTS.accepts_def2)
qed

subsection \<open>accepts code\<close>
lemma accepts_code_Cons:
  fixes ts :: "('ctr_loc \<times> ('label::finite) \<times> ('ctr_loc::finite)) \<Rightarrow>f 'weight::bounded_dioid"
  shows "\<L> ts (p,(\<gamma>#w)) = (\<Sum>{(ts $ (p,\<gamma>,q) * (\<L> ts (q,w))) | q. ts $ (p,\<gamma>,q) \<noteq> 0})"
proof -
  have "finite ({d * \<L>(ts) (q1, w) |q1 d. (p, ([\<gamma>], d), q1) \<in> \<lbrakk>ts\<rbrakk>})"
    unfolding wts_to_monoidLTS_def
    using finite_f_on_set[of UNIV "\<lambda>q. ts $ (p, \<gamma>, q) * \<L>(ts) (q, w)"]
    by simp
  then have
    "\<Sum> {d * \<L> ts (q1, w) |q1 d. (p, ([\<gamma>], d), q1) \<in> \<lbrakk>ts\<rbrakk>} = 
     \<^bold>\<Sum> {d * \<L> ts (q1, w) |q1 d. (p, ([\<gamma>], d), q1) \<in> \<lbrakk>ts\<rbrakk>}"
    using finite_SumInf_is_sum[of "{d * \<L>(ts) (q1, w) |q1 d. (p, ([\<gamma>], d), q1) \<in> \<lbrakk>ts\<rbrakk>}"]
    by auto
  moreover
  have "\<Sum> {d * \<L>(ts) (q1, w) |q1 d. (p, ([\<gamma>], d), q1) \<in> \<lbrakk>ts\<rbrakk>} =
        \<Sum> {ts $ (p, \<gamma>, q) * \<L>(ts) (q, w) |q. True}"
    by (metis (no_types, opaque_lifting) wts_label_d wts_to_monoidLTS_weight_exists)
  moreover
  have "\<Sum> {ts $ (p, \<gamma>, q) * \<L>(ts) (q, w) |q. ts $ (p, \<gamma>, q) \<noteq> 0} = 
                      \<Sum> {ts $ (p, \<gamma>, q) * \<L> ts (q, w) |q. True}"
    using sum_mult_not0_is_sum[of "\<lambda>q. True" "\<lambda>q. ts $ (p, \<gamma>, q)" "\<lambda>q. \<L>(ts) (q, w)"]
    by auto
  ultimately
  show ?thesis
    unfolding accepts_step_distrib by auto
qed
end
end
declare dioidLTS.accepts_empty_iff[code]
declare dioidLTS.accepts_code_Cons[code]


section \<open>Locale: WPDS\<close>

locale WPDS =
  fixes \<Delta> :: "('ctr_loc::finite, 'label::finite, 'weight::bounded_dioid) w_rule set"
begin

primrec lbl :: "'label operation \<Rightarrow> 'label list" where
  "lbl pop = []"
| "lbl (swap \<gamma>) = [\<gamma>]" 
| "lbl (push \<gamma>  \<gamma>') = [\<gamma>, \<gamma>']"

abbreviation is_rule :: "'ctr_loc \<times> 'label \<Rightarrow> 'weight \<Rightarrow> 'ctr_loc \<times> 'label operation \<Rightarrow> bool" ("((_)/ \<midarrow>(_)/\<hookrightarrow> (_)/ )" [70,70,80] 80) where
  "p\<gamma> \<midarrow>d\<hookrightarrow> p'w \<equiv> (p\<gamma>,d,p'w) \<in> \<Delta>"

inductive_set transition_rel :: "(('ctr_loc, 'label) conf \<times> 'weight \<times> ('ctr_loc, 'label) conf) set" where
  "(p, \<gamma>) \<midarrow>d\<hookrightarrow> (p', w) \<Longrightarrow> ((p, \<gamma>#w'), d, (p', (lbl w)@w')) \<in> transition_rel"


\<comment> \<open>Weighted pre-star rule updates the finfun of transition weights.\<close>
inductive pre_star_rule :: "('ctr_loc, 'label, 'weight) w_transitions saturation_rule" where
  add_trans: "((p, \<gamma>) \<midarrow>d\<hookrightarrow> (p', w))
      \<Longrightarrow> (p', (lbl w, d'), q) \<in> \<lbrakk>ts\<rbrakk>\<^sup>\<odot>
      \<Longrightarrow> (ts $ (p, \<gamma>, q) + (d * d')) \<noteq> ts $ (p, \<gamma>, q)
      \<Longrightarrow> pre_star_rule ts ts((p, \<gamma>, q) $:= ts $ (p, \<gamma>, q) + (d * d'))"

interpretation dioidLTS transition_rel .



notation l_step_relp ("(_)/ \<Midarrow> (_)/ \<Rightarrow> (_)/" [70,70,80] 80)


subsection \<open>Proofs of basic properties\<close>

lemma step_relp_def2:
  "(p, \<gamma>w') \<Midarrow>d\<Rightarrow> (p',ww') \<longleftrightarrow> (\<exists>\<gamma> w' w. \<gamma>w' = \<gamma>#w' \<and> ww' = (lbl w)@w' \<and> (p, \<gamma>) \<midarrow>d\<hookrightarrow> (p', w))"
  by (meson l_step_relp_def transition_rel.simps)

lemma step_relp_elim2:
  "(p, \<gamma>w') \<Midarrow>d\<Rightarrow> (p',ww') \<Longrightarrow> (\<exists>\<gamma> w' w. \<gamma>w' = \<gamma>#w' \<and> ww' = (lbl w)@w' \<and> (p, \<gamma>) \<midarrow>d\<hookrightarrow> (p', w))"
  by (meson step_relp_def2)

lemma monoid_star_pop:
  assumes "(p, (lbl w, d), q) \<in> \<lbrakk>ts\<rbrakk>\<^sup>\<odot>"
      and "w = pop"
    shows "p = q \<and> d = 1"
  using assms monoid_star_w0
  by (auto simp add: one_list_def mstar_wts_empty_one) fastforce

lemma monoid_star_swap:
  assumes "(p, (lbl w, d), q) \<in> \<lbrakk>ts\<rbrakk>\<^sup>\<odot>"
      and "w = swap \<gamma>"
    shows "ts $ (p,\<gamma>,q) = d"
  using assms monoid_star_w1 by fastforce

lemma monoid_star_push:
  assumes "(p, (lbl w, d), q) \<in> \<lbrakk>ts\<rbrakk>\<^sup>\<odot>"
      and "w = push \<gamma> \<gamma>'"
    shows "\<exists>q'. ts $ (p,\<gamma>,q') * ts $ (q',\<gamma>',q) = d"
  using assms monoid_star_w2 by fastforce

lemma pre_star_rule_cases:
  assumes "(p, (lbl w, d), q) \<in> \<lbrakk>ts\<rbrakk>\<^sup>\<odot>"
  shows "(w = pop \<and> q = p \<and> d = 1) \<or>                          
         (\<exists>\<gamma>. w = swap \<gamma> \<and> ts $ (p,\<gamma>,q) = d) \<or> 
         (\<exists>\<gamma> \<gamma>'. w = push \<gamma> \<gamma>' \<and> (\<exists>q'. ts $ (p,\<gamma>,q') * ts $ (q',\<gamma>',q) = d))"
proof (cases rule: operation.exhaust[of w])
  case pop
  then show ?thesis using monoid_star_pop[OF assms(1)] by simp
next
  case (swap \<gamma>)
  then show ?thesis using monoid_star_swap[OF assms(1)] by simp
next
  case (push \<gamma> \<gamma>')
  then show ?thesis using monoid_star_push[OF assms(1)] by simp
qed

lemma pre_star_rule_exhaust:
  assumes "(p, (lbl w, d), q) \<in> \<lbrakk>ts\<rbrakk>\<^sup>\<odot>"
  obtains        "q = p" "d = 1" "w = pop"
    | \<gamma>    where "ts $ (p,\<gamma>,q) = d" "w = swap \<gamma>"
    | \<gamma> \<gamma>' q' where "ts $ (p,\<gamma>,q') * ts $ (q',\<gamma>',q) = d" "w = push \<gamma> \<gamma>'"
  using pre_star_rule_cases[OF assms(1)] by blast

lemma finite_range_lbl: "finite (range lbl)"
proof -
  have sub2:"range lbl \<subseteq> {[]} \<union> {[\<gamma>] |\<gamma>. \<gamma> \<in> UNIV} \<union> {[\<gamma>,\<gamma>'] | \<gamma> \<gamma>'. \<gamma> \<in> UNIV \<and> \<gamma>' \<in> UNIV}"
    apply (rule image_subsetI, simp)
    subgoal for x
      by (cases rule: operation.exhaust[of x], auto)
    done
  have "finite {[\<gamma>] |\<gamma>. \<gamma> \<in> (UNIV::'label set)}"
    unfolding setcompr_eq_image[of "\<lambda>\<gamma>. [\<gamma>]" "\<lambda>\<gamma>. \<gamma> \<in> UNIV"] by simp
  moreover have "finite {[\<gamma>,\<gamma>'] | \<gamma> \<gamma>'. \<gamma> \<in> (UNIV::'label set) \<and> \<gamma>' \<in> (UNIV::'label set)}"
    using finite_image_set2[of "\<lambda>\<gamma>. \<gamma> \<in> UNIV" "\<lambda>\<gamma>. \<gamma> \<in> UNIV" "\<lambda>\<gamma> \<gamma>'. [\<gamma>,\<gamma>']"] by force
  ultimately show ?thesis
    using finite_subset[OF sub2] by blast
qed

lemma pre_star_rule_elim2:
  assumes "pre_star_rule ts ts'"
  shows "\<exists>p \<gamma> d p' w d' q. ts' = ts((p, \<gamma>, q) $:= ts $ (p, \<gamma>, q) + (d * d')) \<and> (p, \<gamma>) \<midarrow>d\<hookrightarrow> (p', w) \<and> 
          (p', (lbl w, d'), q) \<in> \<lbrakk>ts\<rbrakk>\<^sup>\<odot> \<and> ts $ (p, \<gamma>, q) + (d * d') \<noteq> ts $ (p, \<gamma>, q)"
  using assms unfolding pre_star_rule.simps[of ts ts'] by presburger

lemma pre_star_rule_less_eq: "pre_star_rule ts ts' \<Longrightarrow> ts' \<le> ts"
  unfolding less_eq_finfun_def
  unfolding pre_star_rule.simps
  apply simp
  apply safe
  subgoal for p \<gamma> d p' w d' q p'' b c
    by (cases "(p'', b, c) = (p, \<gamma>, q)", auto)
  done

lemma pre_star_rule_less: "pre_star_rule ts ts' \<Longrightarrow> ts' < ts"
  unfolding less_finfun_def
  using pre_star_rule_less_eq[of ts ts'] pre_star_rule.simps finfun_upd_apply_same 
  by (simp, metis)

lemma pre_star_rules_less_eq: "pre_star_rule\<^sup>*\<^sup>* ts ts' \<Longrightarrow> ts' \<le> ts"
  by (induct rule: rtranclp.induct, simp) (fastforce dest: pre_star_rule_less)

end


section \<open>Locale: finite_WPDS -- pre* algorithm\<close>

locale finite_WPDS = WPDS \<Delta>
  for \<Delta> :: "('ctr_loc::finite, 'label::finite, 'weight::bounded_dioid) w_rule set" +
  assumes finite_rules: "finite \<Delta>"
begin

lemma finite_rule_weights: "finite {d | p \<gamma> d p' w. (p, \<gamma>) \<midarrow>d\<hookrightarrow> (p', w)}"
  using finite_rules finite_image_set[of "\<lambda>x. x \<in> \<Delta>" "\<lambda>(p,d,q). d"] by simp

lemma countable_transition_rel: "countable transition_rel"
proof -
  have transition_rel_subset: "transition_rel \<subseteq> (UNIV \<times> {d | c d c'. (c,d,c') \<in> transition_rel} \<times> UNIV)" 
    by fast
  have countable_confs: "countable (UNIV::('ctr_loc, 'label) conf set)"
    by blast
  have "\<And>c d c'. (c,d,c') \<in> transition_rel \<Longrightarrow> \<exists>p\<gamma> p'w. (p\<gamma>,d,p'w) \<in> \<Delta>"
    by (auto simp add: transition_rel.simps, blast)
  then have weights_subset: "{d | c d c'. (c,d,c') \<in> transition_rel} \<subseteq> {d | p\<gamma> d p'w. (p\<gamma>,d,p'w) \<in> \<Delta>}" 
    by blast
  have "finite {d | c d c'. (c,d,c') \<in> transition_rel}" 
    using finite_rule_weights finite_subset[OF weights_subset] by force
  then have "countable {d | c d c'. (c,d,c') \<in> transition_rel}" 
    using countable_finite by blast
  then show "countable transition_rel" 
    using countable_confs countable_subset[OF transition_rel_subset] by blast
qed
interpretation countable_dioidLTS transition_rel proof
  show "countable transition_rel" by (fact countable_transition_rel)
qed

notation step_relp (infix "\<Rightarrow>" 80)
notation step_starp (infix "\<Rightarrow>\<^sup>*" 80)
notation l_step_relp ("(_)/ \<Midarrow> (_)/ \<Rightarrow> (_)/" [70,70,80] 80)
notation monoid_star_relp ("(_)/ \<Midarrow> (_)/ \<Rightarrow>\<^sup>* (_)/" [90,90,100] 100) 

lemma finite_pre_star_rule_set: "finite {ts'. pre_star_rule ts ts'}"
proof -
  have sub:"{ts'. pre_star_rule ts ts'} 
            \<subseteq> {ts((p, \<gamma>, q) $:= ts $ (p, \<gamma>, q) + d * d') | p \<gamma> d p' w d' q. 
                (p, \<gamma>) \<midarrow>d\<hookrightarrow> (p', w) \<and> (p', (lbl w, d'), q) \<in> \<lbrakk>ts\<rbrakk>\<^sup>\<odot>}"
    unfolding pre_star_rule.simps by fast
  have "{d. \<exists>p' w q. (p', (lbl w, d), q) \<in> \<lbrakk>ts\<rbrakk>\<^sup>\<odot>} = {d. \<exists>x. (\<exists>p b. (p, (x, d), b) \<in> \<lbrakk>ts\<rbrakk>\<^sup>\<odot>) \<and> x \<in> range lbl}"
    by fast
  then have fin_d': "finite {d' | p' w d' q. (p', (lbl w, d'), q) \<in> \<lbrakk>ts\<rbrakk>\<^sup>\<odot>}"
    using finite_union_f[OF finite_range_lbl, of "\<lambda>y. fst (snd y)" "\<lambda>x y. (fst y, (x, fst (snd y)), snd (snd y)) \<in> \<lbrakk>ts\<rbrakk>\<^sup>\<odot>"]
    by (simp add: finite_mstar_wts_weights[OF finite_wts[of ts]])
  have fin_dd': "finite {d * d' | p \<gamma> d p' w d' q. (p, \<gamma>) \<midarrow>d\<hookrightarrow> (p', w) \<and> (p', (lbl w, d'), q) \<in> \<lbrakk>ts\<rbrakk>\<^sup>\<odot>}"
    using finite_subset[OF _ finite_image_set2[OF finite_rule_weights fin_d', of "\<lambda>d d'. d * d'"], 
                        of "{d * d' | p \<gamma> d p' w d' q. (p, \<gamma>) \<midarrow>d\<hookrightarrow> (p', w) \<and> (p', (lbl w, d'), q) \<in> \<lbrakk>ts\<rbrakk>\<^sup>\<odot>}"]
    by fast
  have fin_UNIV:"finite {(p,\<gamma>,q). (p,\<gamma>,q) \<in> (UNIV::('ctr_loc \<times> 'label \<times> 'ctr_loc) set)}"
    by simp
  show ?thesis 
    using finite_subset[OF sub] 
          finite_subset[OF _ finite_image_set2[OF fin_UNIV fin_dd', of "\<lambda>t d. ts(t $:= ts $ t + d)"], 
                        of "{ts((p, \<gamma>, q) $:= ts $ (p, \<gamma>, q) + d * d') | p \<gamma> d p' w d' q. 
                            (p, \<gamma>) \<midarrow>d\<hookrightarrow> (p', w) \<and> (p', (lbl w, d'), q) \<in> \<lbrakk>ts\<rbrakk>\<^sup>\<odot>}"]
    by blast
qed


subsection \<open>Pre* correctness\<close>

abbreviation (input) ctr_loc_pred_weight :: "('ctr_loc * 'label list) \<Rightarrow> 'ctr_loc \<Rightarrow> 'weight" ("\<^bold>\<Sigma>_\<Rightarrow>\<^sup>*_") where
  "(\<^bold>\<Sigma>pw\<Rightarrow>\<^sup>*p') \<equiv> \<^bold>\<Sum>{d'. pw \<Midarrow>d'\<Rightarrow>\<^sup>* (p',[])}"

abbreviation (input) ctr_loc_preds_weight :: "('ctr_loc * 'label list) \<Rightarrow> 'ctr_loc set \<Rightarrow> 'weight" ("\<^bold>\<Sigma>\<^sub>s_\<Rightarrow>\<^sup>*_") where
  "(\<^bold>\<Sigma>\<^sub>spw\<Rightarrow>\<^sup>*Q) \<equiv> \<^bold>\<Sum> {l |l q. q \<in> Q \<and> pw \<Midarrow> l \<Rightarrow>\<^sup>* (q, [])}"

lemma push_seq_weight_def2:
  "(\<^bold>\<Sigma>pw\<Rightarrow>\<^sup>*p') = \<^bold>\<Sum> {d |d. pw \<Midarrow> d \<Rightarrow>\<^sup>* (p', [])}"
  by auto

lemma countable_monoid_star_all_triple: "countable {(d', q, w). (p, v) \<Midarrow> d' \<Rightarrow>\<^sup>* (q, w)}"
  by (auto simp: dissect_set countable_monoid_star_variant1)

lemma countable_push_seq_weight:
  "countable {d |d. pw \<Midarrow> d \<Rightarrow>\<^sup>* (p', [])}"
  using countable_star_f_p9 .

lemma countable_push_seq_weight1: "countable {(d', q). (p, v) \<Midarrow> d' \<Rightarrow>\<^sup>* (q, [])}"
proof -
  have "countable {(\<gamma>, c'). (p, v) \<Midarrow> \<gamma> \<Rightarrow>\<^sup>* c'}"
    using countable_monoid_star_all(3)[of "(p,v)"]
    by auto
  then have "countable ((\<lambda>(\<gamma>, c'). (\<gamma>, fst c')) ` ({(\<gamma>, c'). snd c' = []} \<inter> {(\<gamma>, c'). (p, v) \<Midarrow> \<gamma> \<Rightarrow>\<^sup>* c'}))"
    by auto
  then show ?thesis
    unfolding image_def Int_def using Collect_mono_iff countable_subset by fastforce
qed

lemmas countable_monoid_star_all = 
  countable_monoid_star_all countable_push_seq_weight countable_monoid_star_all_triple 
  countable_push_seq_weight1

lemma countable_push_seq_weight2:
  "countable {d'| d' q. P q d' \<and> (p, v) \<Midarrow> d' \<Rightarrow>\<^sup>* (q, [])}"
  unfolding setcompr_eq_image2 by (auto simp add: dissect_set countable_monoid_star_all)

lemma countable_push_seq_weight3:
  "countable {f d' q w| d' q w. (p, v) \<Midarrow> d' \<Rightarrow>\<^sup>* (q, w)}"
  by (auto simp add: dissect_set countable_monoid_star_all)

definition sound :: "(('ctr_loc, 'label, 'weight) w_transitions) \<Rightarrow> bool" where
  "sound A \<longleftrightarrow> (\<forall>p p' \<gamma> d. (p, ([\<gamma>],d), p') \<in> \<lbrakk>A\<rbrakk> \<longrightarrow> d \<ge> \<^bold>\<Sigma>(p,[\<gamma>])\<Rightarrow>\<^sup>*p')"

lemma sound_intro:
  assumes "\<And>p p' \<gamma> d. (p, ([\<gamma>], d), p') \<in> \<lbrakk>A\<rbrakk> \<Longrightarrow> (\<^bold>\<Sigma>(p, [\<gamma>])\<Rightarrow>\<^sup>*p') \<le> d"
  shows "sound A"
  unfolding sound_def using assms by auto

lemmas monoid_star_relp_induct [consumes 1, case_names monoid_star_refl monoid_star_into_rtrancl] = 
  MonoidClosure.monoid_rtranclp.induct[of l_step_relp ]

lemmas monoid_star_relp_induct_rev [consumes 1, case_names monoid_star_refl monoid_star_into_rtrancl] = 
  MonoidClosure.monoid_rtranclp_induct_rev[of l_step_relp ]

lemma step_rule:
  assumes "(p, \<gamma>) \<midarrow>d\<hookrightarrow> (p', w)"
  assumes "c \<Midarrow>d'\<Rightarrow>\<^sup>* (p, \<gamma> # w')"
  shows "c \<Midarrow>(d' * d)\<Rightarrow>\<^sup>* (p', lbl w @ w')"
  using assms by (meson monoid_rtranclp.simps step_relp_def2)

lemma step_relp_append:
  assumes "(p,w) \<Midarrow>d'\<Rightarrow>\<^sup>* (p',w')"
  shows "(p, w @ v) \<Midarrow>d'\<Rightarrow>\<^sup>* (p', w' @ v)"
  using MonoidClosure.monoid_rtranclp.induct[of "\<lambda>pw b c. pw\<Midarrow>b\<Rightarrow>c" "(p,w)" d' "(p',w')"  
      "\<lambda>(p,w) d' (p',w'). (p,w @ v) \<Midarrow>d'\<Rightarrow>\<^sup>* (p', w' @ v)", OF assms(1)]
        step_rule step_relp_def2 by fastforce

lemma step_relp_seq:
  assumes "(p, w) \<Midarrow>d\<Rightarrow>\<^sup>* (p', [])"
  assumes "(p', w') \<Midarrow>d'\<Rightarrow>\<^sup>* (p'', [])"
  shows "(p, w @ w') \<Midarrow>(d * d')\<Rightarrow>\<^sup>* (p'', [])"
proof -
  have "(p, w @ w') \<Midarrow> d \<Rightarrow>\<^sup>* (p', w')"
    using assms(1) using step_relp_append by fastforce
  then show ?thesis
    by (meson assms(2) monoid_rtranclp_trans)
qed

lemma monoid_star_relp_if_l_step_relp:
  assumes "(p,w) \<Midarrow>d\<Rightarrow> (p',[])"
  shows "(p,w) \<Midarrow>d\<Rightarrow>\<^sup>* (p',[])"
  by (fact r_into_monoid_rtranclp[of l_step_relp, OF assms])

lemma push_seq_weight_if_monoid_star_relp:
  assumes "(p,w) \<Midarrow>d\<Rightarrow>\<^sup>* (p',[])"
  shows "(\<^bold>\<Sigma>(p, w)\<Rightarrow>\<^sup>*p') \<le> d"
  using countable_SumInf_elem[of "{d'. (p, w) \<Midarrow> d' \<Rightarrow>\<^sup>* (p', [])}" d] 
    assms by (auto simp add: countable_monoid_star_all)

lemma push_seq_weight_if_l_step_relp:
  assumes "(p,w) \<Midarrow>d\<Rightarrow> (p',[])"
  shows "(\<^bold>\<Sigma>(p, w)\<Rightarrow>\<^sup>*p') \<le> d"
  by (simp add: assms monoid_star_relp_if_l_step_relp push_seq_weight_if_monoid_star_relp)

lemma push_seq_weight_trans:
  assumes "(\<^bold>\<Sigma>(p'', w')\<Rightarrow>\<^sup>*p\<^sub>i) \<le> d1"
  assumes "(\<^bold>\<Sigma>(p\<^sub>i, w'')\<Rightarrow>\<^sup>*p2) \<le> d2"
  shows "(\<^bold>\<Sigma>(p'', w'@w'')\<Rightarrow>\<^sup>*p2) \<le> d1 * d2"
proof -
  have "(\<^bold>\<Sigma>(p'',w'@w'') \<Rightarrow>\<^sup>* p2) \<le> \<^bold>\<Sum>{d1' * d2'| d1'  d2'. (p'',w') \<Midarrow>d1'\<Rightarrow>\<^sup>* (p\<^sub>i,[]) \<and> (p\<^sub>i,w'') \<Midarrow>d2'\<Rightarrow>\<^sup>* (p2,[])}"
    using SumInf_mono[of "{d1' * d2' |d1' d2'. (p'', w') \<Midarrow> d1' \<Rightarrow>\<^sup>* (p\<^sub>i, []) \<and> (p\<^sub>i, w'') \<Midarrow> d2' \<Rightarrow>\<^sup>* (p2, [])}" 
        "{d'. (p'', w' @ w'') \<Midarrow> d' \<Rightarrow>\<^sup>* (p2, [])}"]
      step_relp_seq by (force simp add: countable_monoid_star_all dissect_set)
  also have "... \<le> (\<^bold>\<Sigma>(p'',w') \<Rightarrow>\<^sup>* p\<^sub>i) * (\<^bold>\<Sigma>(p\<^sub>i,w'') \<Rightarrow>\<^sup>* p2)"
    using SumInf_left_distr[of "{d'. (p\<^sub>i, w'') \<Midarrow> d' \<Rightarrow>\<^sup>* (p2, [])}" "\<^bold>\<Sum> {d'. (p'', w') \<Midarrow> d' \<Rightarrow>\<^sup>* (p\<^sub>i, [])}"] 
          SumInf_of_SumInf_right_distr_simple[of "\<lambda>d'. (p'', w') \<Midarrow> d' \<Rightarrow>\<^sup>* (p\<^sub>i, [])"]
    by (simp add: dissect_set countable_monoid_star_all)
  also have "... \<le> d1 * d2"
    using assms BoundedDioid.mult_isol_var by auto
  finally 
  show ?thesis
    by auto
qed

lemma push_seq_weight_trans_push:
  assumes "(\<^bold>\<Sigma>(p'', [\<mu>'])\<Rightarrow>\<^sup>*p\<^sub>i) \<le> d1"
  assumes "(\<^bold>\<Sigma>(p\<^sub>i, [\<mu>''])\<Rightarrow>\<^sup>*p2) \<le> d2"
  shows "(\<^bold>\<Sigma>(p'', [\<mu>', \<mu>''])\<Rightarrow>\<^sup>*p2) \<le> d1 * d2"
  using assms push_seq_weight_trans[of p'' "[\<mu>']" p\<^sub>i d1 "[\<mu>'']" p2 d2] by auto

lemma monoid_star_relp_push_seq_weight_trans:
  assumes "(p1, w) \<Midarrow>d\<Rightarrow>\<^sup>* (p'', w')"
  assumes "(\<^bold>\<Sigma>(p'', w')\<Rightarrow>\<^sup>*p2) \<le> d'"
  shows "(\<^bold>\<Sigma>(p1, w)\<Rightarrow>\<^sup>*p2) \<le> d * d'"
proof -
  have "(\<^bold>\<Sigma> (p1, w) \<Rightarrow>\<^sup>* p2) \<le> \<^bold>\<Sum>{d * d'| d'. (p1, w) \<Midarrow>d\<Rightarrow>\<^sup>* (p'',w') \<and> (p'',w') \<Midarrow>d'\<Rightarrow>\<^sup>* (p2,[])}"
    using SumInf_mono[of "{d * d' |d'. (p1, w) \<Midarrow> d \<Rightarrow>\<^sup>* (p'', w') \<and> (p'', w') \<Midarrow> d' \<Rightarrow>\<^sup>* (p2, [])}" 
        "{d'. (p1, w) \<Midarrow> d' \<Rightarrow>\<^sup>* (p2, [])}"]
    monoid_rtranclp_trans by (force simp add: countable_monoid_star_all dissect_set)
  also have "... \<le> \<^bold>\<Sum>{d * d'| d'. (p'',w') \<Midarrow>d'\<Rightarrow>\<^sup>* (p2,[])}"
    using \<open>(p1, w) \<Midarrow> d \<Rightarrow>\<^sup>* (p'', w')\<close> by fastforce
  also have "... \<le> d * \<^bold>\<Sigma>(p'',w') \<Rightarrow>\<^sup>* p2"
    by (simp add: SumInf_left_distr countable_monoid_star_all dissect_set)
  also have "... \<le> d * d'"
    using assms by (simp add: assms BoundedDioid.mult_isol)
  finally 
  show ?thesis
    by auto
qed

lemma push_seq_weight_trans_Cons:
  assumes "(\<^bold>\<Sigma>(p, [\<gamma>])\<Rightarrow>\<^sup>*p\<^sub>i) \<le> d1"
  assumes "(\<^bold>\<Sigma>(p\<^sub>i, w)\<Rightarrow>\<^sup>*p') \<le> d2"
  shows "(\<^bold>\<Sigma>(p, \<gamma> # w)\<Rightarrow>\<^sup>*p') \<le> d1 * d2"
  using assms push_seq_weight_trans[of p "[\<gamma>]" p\<^sub>i d1 w p' d2] by auto

lemma leq_ctr_loc_pred_weight_if_leq_all_paths:
  assumes "\<forall>d. c \<Midarrow> d \<Rightarrow>\<^sup>* (q, []) \<longrightarrow> X \<le> d"
  shows "X \<le> (\<^bold>\<Sigma>c \<Rightarrow>\<^sup>* q)"
  by (metis (mono_tags, lifting) Collect_mono_iff SumInf_bounded_if_set_bounded assms countable_l_c_c' 
      countable_subset mem_Collect_eq)

lemma leq_ctr_loc_preds_weight_if_leq_ctr_loc_pred_weight:
  assumes "\<forall>q\<in>finals. X \<le> (\<^bold>\<Sigma>c \<Rightarrow>\<^sup>* q)"
  shows "X \<le> (\<^bold>\<Sigma>\<^sub>sc \<Rightarrow>\<^sup>* finals)"
proof -
  have "\<forall>l q. q \<in> finals \<longrightarrow> c \<Midarrow> l \<Rightarrow>\<^sup>* (q, []) \<longrightarrow> X \<le> l"
  proof -
    { 
      fix w :: 'weight and q :: 'ctr_loc
      have "\<forall>p c w. p \<Midarrow> w \<Rightarrow>\<^sup>* (c, []) \<longrightarrow> \<^bold>\<Sum> {w. p \<Midarrow> w \<Rightarrow>\<^sup>* (c, [])} \<le> w"
        by (simp add: push_seq_weight_if_monoid_star_relp)
      then have "c \<Midarrow> w \<Rightarrow>\<^sup>* (q, []) \<longrightarrow> q \<in> finals \<longrightarrow> X \<le> w"
        using assms dual_order.trans by blast 
    }
    then show ?thesis
      by blast
  qed
  then show ?thesis
    by (smt (verit, best) Collect_mono_iff SumInf_bounded_if_set_bounded countable_l_c_c' countable_subset mem_Collect_eq)
qed

lemma ctr_loc_preds_weight_is_ctr_loc_pred_weight:
  "(\<^bold>\<Sigma>\<^sub>s(p,v)\<Rightarrow>\<^sup>*finals) = \<^bold>\<Sum>{(\<^bold>\<Sigma> (p,v) \<Rightarrow>\<^sup>* q) | q. q \<in> finals}"
proof -
  have "(\<^bold>\<Sigma>\<^sub>s(p,v)\<Rightarrow>\<^sup>*finals) = \<^bold>\<Sum> {d' |d' q. q \<in> finals \<and> (p,v) \<Midarrow> d' \<Rightarrow>\<^sup>* (q, [])}"
    by auto
  moreover
  have "... = \<^bold>\<Sum> {uu. \<exists>x y. uu = x \<and> (p, v) \<Midarrow> x \<Rightarrow>\<^sup>* (y, []) \<and> y \<in> finals}"
    by metis
  moreover
  have "... = \<^bold>\<Sum> {\<^bold>\<Sum> {x |x. (p, v) \<Midarrow> x \<Rightarrow>\<^sup>* (y, [])} |y. y \<in> finals}"
    using SumInf_of_SumInf[of "\<lambda>q. q \<in> finals" "%d' q. (p, v) \<Midarrow> d' \<Rightarrow>\<^sup>* (q, [])" "\<lambda>d' q. d'"]
    by (auto simp add: countable_star_f_p9)
  moreover
  have "... = \<^bold>\<Sum> {\<^bold>\<Sum>{d'. (p,v) \<Midarrow>d'\<Rightarrow>\<^sup>* (q,[])} | q. q \<in> finals}"
    by auto
  moreover
  have "... = \<^bold>\<Sum>{(\<^bold>\<Sigma> (p,v) \<Rightarrow>\<^sup>* q) | q. q \<in> finals}"
    by auto
  ultimately show ?thesis
    by auto
qed

lemma sound_elim2:
  assumes "sound A"
  assumes "(p, (w,d), p') \<in> \<lbrakk>A\<rbrakk>\<^sup>\<odot>"
  shows "d \<ge> \<^bold>\<Sigma>(p,w) \<Rightarrow>\<^sup>* p'"
  using assms(2) 
proof (induction w arbitrary: d p)
  case Nil
  then have "d = 1"
    by (simp add: mstar_wts_empty_one)
  have "(p, []) \<Midarrow>1\<Rightarrow>\<^sup>* (p', [])"
    using Nil monoid_star_pop by fastforce
  have "d \<ge> \<^bold>\<Sigma>(p, []) \<Rightarrow>\<^sup>* p'" 
    using countable_SumInf_elem[of "{d'. (p, []) \<Midarrow> d' \<Rightarrow>\<^sup>* (p', [])}" d]
          \<open>(p, []) \<Midarrow> 1 \<Rightarrow>\<^sup>* (p', [])\<close> \<open>d = 1\<close> 
    by (simp add: countable_monoid_star_all dissect_set)
  then show ?case .
next
  case (Cons \<gamma> w)
  from Cons(2) have
    "\<exists>pi d1 d2. d = d1 * d2 
                \<and> (pi, (w, d2), p') \<in> \<lbrakk>A\<rbrakk>\<^sup>\<odot>
                \<and> (p, ([\<gamma>], d1), pi) \<in> \<lbrakk>A\<rbrakk>"
    unfolding monoid_star_is_monoid_rtrancl
    using monoid_star_nonempty by fastforce
  then obtain pi d1 d2 where pi_d1_d2_p:
    "d = d1 * d2"
    "(pi, (w, d2), p') \<in> \<lbrakk>A\<rbrakk>\<^sup>\<odot>"
    "(p, ([\<gamma>], d1), pi) \<in> \<lbrakk>A\<rbrakk>"
    by blast
  then have d2_sound: "d2 \<ge> \<^bold>\<Sigma>(pi, w) \<Rightarrow>\<^sup>* p'"
    using Cons(1)[of pi d2] by auto

  have "d1 \<ge> (\<^bold>\<Sigma> (p, [\<gamma>]) \<Rightarrow>\<^sup>* pi)"
    using assms(1) pi_d1_d2_p(3) sound_def by blast
  then have "(\<^bold>\<Sigma> (p, \<gamma> # w) \<Rightarrow>\<^sup>* p') \<le>  d1 * d2"
    using d2_sound push_seq_weight_trans_Cons by auto
  also have "... = d" 
    using \<open>d = d1 * d2\<close> by fast 
  finally show ?case .
qed

lemma sound_def2:
  "sound A \<longleftrightarrow> (\<forall>p p' w d. (p, (w,d), p') \<in> \<lbrakk>A\<rbrakk>\<^sup>\<odot> \<longrightarrow> d \<ge> \<^bold>\<Sigma>(p,w) \<Rightarrow>\<^sup>* p')"
proof
  assume "sound A"
  then show "\<forall>p p' w d. (p, (w, d), p') \<in> \<lbrakk>A\<rbrakk>\<^sup>\<odot> \<longrightarrow> (\<^bold>\<Sigma>(p, w)\<Rightarrow>\<^sup>*p') \<le> d"
    using sound_elim2 by blast
next
  assume "\<forall>p p' w d. (p, (w, d), p') \<in> \<lbrakk>A\<rbrakk>\<^sup>\<odot> \<longrightarrow> (\<^bold>\<Sigma>(p, w)\<Rightarrow>\<^sup>*p') \<le> d"
  then show "sound A"
    using monoid_star_intros_step unfolding sound_def by blast
qed

lemma pre_star_rule_sound:
  assumes "sound A"
  assumes "pre_star_rule A A'"
  shows "sound A'"
proof -
  obtain p' \<gamma>' d p'' w' d' q d'' where ps:
    "(p',\<gamma>') \<midarrow>d\<hookrightarrow> (p'',w')"
    "d'' + d * d' \<noteq> d''" 
    "(p'',(lbl w', d'),q) \<in> \<lbrakk>A\<rbrakk>\<^sup>\<odot>" 
    "A' = A((p', \<gamma>', q) $:= d'' + d * d')" 
    "A $ (p', \<gamma>', q) = d''" 
    using assms(2) pre_star_rule.cases by metis
  show "sound A'"
  proof (rule sound_intro)
    fix p1 p2 \<mu> D
    assume p1_\<mu>_l_p2: "(p1, ([\<mu>], D), p2) \<in> \<lbrakk>A'\<rbrakk>"
    show "D \<ge> \<^bold>\<Sigma> (p1, [\<mu>]) \<Rightarrow>\<^sup>* p2"
    proof (cases "p1 = p' \<and> \<mu> = \<gamma>' \<and> p2 = q")
      case True
      then have True': "p1 = p'" "\<mu> = \<gamma>'" "p2 = q"
        by auto
      have l_eql: "D = d'' + d * d'"
        using p1_\<mu>_l_p2 unfolding ps(4) True' unfolding wts_to_monoidLTS_def by auto
      have d''_geq: "d'' \<ge> \<^bold>\<Sigma> (p1,[\<mu>]) \<Rightarrow>\<^sup>* p2"
        using ps(5) assms(1) True unfolding sound_def wts_to_monoidLTS_def by force
      have p1_to_p'': "(p1, [\<mu>]) \<Midarrow>d\<Rightarrow> (p'', lbl w')"
        using ps(1) True step_relp_def2 by auto
      show ?thesis
      proof (rule pre_star_rule_exhaust[OF ps(3)[unfolded True'[symmetric]]])
        assume "p2 = p''"
        assume "d' = 1"
        assume "w' = pop"
        from p1_to_p'' have "(p1, [\<mu>]) \<Midarrow>d * d'\<Rightarrow> (p2,[])"
          using \<open>d' = 1\<close> \<open>w' = pop\<close> \<open>p2 = p''\<close> by auto
        then have "d * d' \<ge> \<^bold>\<Sigma> (p1, [\<mu>]) \<Rightarrow>\<^sup>* p2"
          using push_seq_weight_if_l_step_relp[of p1 "[\<mu>]" "d * d'" p2] by auto
        then show "D \<ge> \<^bold>\<Sigma> (p1, [\<mu>]) \<Rightarrow>\<^sup>* p2"
          using d''_geq l_eql by auto
      next
        fix \<mu>'
        assume "A $ (p'', \<mu>', p2) = d'"
        assume w'_swap: "w' = swap \<mu>'"
        from ps(3) have "(p'', ([\<mu>'],d'), p2) \<in> \<lbrakk>A\<rbrakk>\<^sup>\<odot>"
          using True'(3) \<open>w' = swap \<mu>'\<close> by force
        then have p''_to_p2: "d' \<ge> \<^bold>\<Sigma> (p'',[\<mu>']) \<Rightarrow>\<^sup>* p2"
          using assms(1) sound_elim2 by force
        from p1_to_p'' have "(p1, [\<mu>]) \<Midarrow>d\<Rightarrow>\<^sup>* (p'',[\<mu>'])"
          unfolding True' w'_swap using monoid_rtranclp.monoid_rtrancl_into_rtrancl by fastforce
        then have "(\<^bold>\<Sigma> (p1, [\<mu>]) \<Rightarrow>\<^sup>* p2) \<le> d * d'"
          using p''_to_p2 monoid_star_relp_push_seq_weight_trans by auto
        then show "D \<ge> \<^bold>\<Sigma> (p1, [\<mu>]) \<Rightarrow>\<^sup>* p2"
          using d''_geq l_eql by auto
      next
        fix \<mu>' \<mu>'' pi
        assume trans_weights: "A $ (p'', \<mu>', pi) * A $ (pi, \<mu>'', p2) = d'"
        assume "w' = push \<mu>' \<mu>''"
        define d1 where "d1 = A $ (p'', \<mu>', pi)"
        define d2 where "d2 = A $ (pi, \<mu>'', p2)"
        have "d' = d1 * d2"
          using d1_def d2_def trans_weights by auto

        from p1_to_p'' have "(p1,[\<mu>]) \<Midarrow>d\<Rightarrow>\<^sup>* (p'',[\<mu>',\<mu>''])"
          using \<open>w' = push \<mu>' \<mu>''\<close> monoid_rtranclp.monoid_rtrancl_into_rtrancl by fastforce
        moreover
        have "d1 \<ge> \<^bold>\<Sigma>(p'',[\<mu>']) \<Rightarrow>\<^sup>* pi"
          using d1_def assms(1) sound_def by (force simp add: wts_to_monoidLTS_def)
        moreover
        have "d2 \<ge> \<^bold>\<Sigma>(pi,[\<mu>'']) \<Rightarrow>\<^sup>* p2"
          using d2_def assms(1) sound_def by (force simp add: wts_to_monoidLTS_def)
        ultimately
        have "d * d1 * d2 \<ge> \<^bold>\<Sigma> (p1, [\<mu>]) \<Rightarrow>\<^sup>* p2"
          by (simp add: mult.assoc push_seq_weight_trans_push monoid_star_relp_push_seq_weight_trans)
        then show "D \<ge> \<^bold>\<Sigma> (p1, [\<mu>]) \<Rightarrow>\<^sup>* p2"
          using d''_geq l_eql by (simp add: \<open>d' = d1 * d2\<close> mult.assoc) 
      qed
    next
      case False
      then have "(p1, ([\<mu>], D), p2) \<in> \<lbrakk>A\<rbrakk>"
        using ps(4) p1_\<mu>_l_p2 unfolding wts_to_monoidLTS_def by auto
      then show ?thesis
        using assms unfolding sound_def by auto
    qed
  qed
qed

lemma pre_star_rule_rtranclp_sound:
  assumes "sound A"
  assumes "pre_star_rule\<^sup>*\<^sup>* A A'"
  shows "sound A'"
  using assms(2,1)
proof (induction)
  case base
  then show ?case
    .
next
  case (step A' A'')
  then show ?case
    using pre_star_rule_sound by blast
qed

lemma sound_empty: "sound (K$ 0)"
  by (simp add: sound_def wts_to_monoidLTS_def)

lemma countable_monoid_rtrancl_wts_to_monoidLTS:
 fixes A::"(('ctr_loc, 'label, 'weight::bounded_dioid) w_transitions)"
 shows "countable (\<lbrakk>A\<rbrakk>\<^sup>\<odot>)"
  by (metis countable_wts countable_monoidLTS.countable_monoid_star countable_monoidLTS.intro monoidLTS.monoid_star_is_monoid_rtrancl)

lemma countable_monoid_rtrancl_wts_to_monoidLTS_pair:
  fixes A :: "(('ctr_loc, 'label, 'weight::bounded_dioid) w_transitions)"
  shows "countable {(d, q). (p, (w, d), q) \<in> \<lbrakk>A\<rbrakk>\<^sup>\<odot>}"
proof -
  have "(\<lbrakk>A\<rbrakk>\<^sup>\<odot> \<inter> {(p', (w', d), q) |p' w' d q. p' = p \<and> w' = w})
           = {(p, (w, d), q) |d q. (p, (w, d), q) \<in> \<lbrakk>A\<rbrakk>\<^sup>\<odot>}"
    by auto
  then have count_A: "countable {(p, (w, d), q)| d q. (p, (w, d), q) \<in> \<lbrakk>A\<rbrakk>\<^sup>\<odot>}"
    using countable_Int1[OF countable_monoid_rtrancl_wts_to_monoidLTS[of A], of "{(p', (w', d), q) | p' w' d q. p' = p \<and> w' = w}"]
    by auto
  have "((\<lambda>(p, (w, d), q). (d, q)) ` {(p, (w, d), q) |d q. (p, (w, d), q) \<in> \<lbrakk>A\<rbrakk>\<^sup>\<odot>})
           = {(d, q). (p, (w, d), q) \<in> \<lbrakk>A\<rbrakk>\<^sup>\<odot>}"
    unfolding image_def by auto
  then show ?thesis
    using countable_image[of "{(p, (w, d), q) |d q. (p, (w, d), q) \<in> \<lbrakk>A\<rbrakk>\<^sup>\<odot>}"
      "\<lambda>(p, (w, d), q). (d, q)", OF count_A]
    by auto
qed

lemmas countable_monoid_rtrancl_wts_to_monoidLTS_all =
  countable_monoid_rtrancl_wts_to_monoidLTS
  countable_monoid_rtrancl_wts_to_monoidLTS_pair

lemma countable_monoid_rtrancl_wts_to_monoidLTS_P: 
  fixes A::"(('ctr_loc, 'label, 'weight::bounded_dioid) w_transitions)"
  shows "countable {f d q |d q. P d q \<and> (p, (w, d), q) \<in> \<lbrakk>A\<rbrakk>\<^sup>\<odot>}"
  using countable_monoid_rtrancl_wts_to_monoidLTS_all by (simp add: dissect_set)

context fixes finals :: "'ctr_loc::finite set" begin
abbreviation accepts'' ("\<L>(_)" [1000] 1000) where "accepts'' \<equiv> accepts' finals" 

lemma weight_pre_star_K0_is_pred_weight:
   "weight_pre_star \<L>(K$ 0) (p, w) = (\<^bold>\<Sigma>\<^sub>s(p,w)\<Rightarrow>\<^sup>*finals)"
proof -
  have count: "countable {uu. \<exists>q. q \<in> finals \<and> (p, w) \<Midarrow> uu \<Rightarrow>\<^sup>* (q, [])}"
    using Collect_mono_iff countable_l_c_c' countable_subset by fastforce

  have "weight_pre_star \<L>(K$ 0) (p, w) = \<^bold>\<Sum> {l * \<L>(K$ 0) c' |l c'. (p, w) \<Midarrow> l \<Rightarrow>\<^sup>* c'}"
    unfolding weight_pre_star_def ..
  also have "... = \<^bold>\<Sum> {l * \<L>(K$ 0) (q,v) |l q v. (p, w) \<Midarrow> l \<Rightarrow>\<^sup>* (q,v)}"
    by auto
  also have "... = \<^bold>\<Sum> {l * (if q \<in> finals \<and> v = [] then 1 else 0) |l q v. (p, w) \<Midarrow> l \<Rightarrow>\<^sup>* (q, v)}"
    unfolding accepts_K0_iff by auto
  also have "... = \<^bold>\<Sum> ({l * 1 |l q v. q \<in> finals \<and> v = [] \<and> (p, w) \<Midarrow> l \<Rightarrow>\<^sup>* (q, v)} \<union>
                       {l * 0 |l q v. \<not>(q \<in> finals \<and> v = []) \<and> (p, w) \<Midarrow> l \<Rightarrow>\<^sup>* (q, v)})"
    apply -
    apply (rule arg_cong[of _ _ "\<^bold>\<Sum>"])
    apply auto
    done
  also have "... = \<^bold>\<Sum> ({l * 1 |l q v. q \<in> finals \<and> v = [] \<and> (p, w) \<Midarrow> l \<Rightarrow>\<^sup>* (q, v)} \<union>
                       {0 |l q v. \<not>(q \<in> finals \<and> v = []) \<and> (p, w) \<Midarrow> l \<Rightarrow>\<^sup>* (q, v)})"
    apply -
    apply (rule arg_cong[of _ _ "\<^bold>\<Sum>"])
    apply auto
    done
  also have "... = \<^bold>\<Sum> ({l * 1 |l q v. q \<in> finals \<and> v = [] \<and> (p, w) \<Midarrow> l \<Rightarrow>\<^sup>* (q, v)})"
    apply (cases "\<exists>l q v. \<not>(q \<in> finals \<and> v = []) \<and> (p, w) \<Midarrow> l \<Rightarrow>\<^sup>* (q, v)")
    subgoal
      using SumInf_insert_0[OF count]
      apply auto
      done
    subgoal
      apply auto
      apply (smt (verit, best) Collect_empty_eq sup_bot.right_neutral)
      done
    done
  also have "... = (\<^bold>\<Sigma>\<^sub>s(p,w)\<Rightarrow>\<^sup>*finals)"
    by auto
  finally show ?thesis
    by blast
qed

lemma sound_accepts_geq_pred_weight:
  assumes soundA': "sound A'"
  shows "\<L>(A') pv \<ge> (\<^bold>\<Sigma>\<^sub>spv\<Rightarrow>\<^sup>*finals)"
proof -
  obtain p v where pv_split: "pv = (p, v)"
    by (cases pv)   
  have "(\<^bold>\<Sigma>\<^sub>s(p,v)\<Rightarrow>\<^sup>*finals) = \<^bold>\<Sum>{(\<^bold>\<Sigma> (p,v) \<Rightarrow>\<^sup>* q) | q. q \<in> finals}"
    using ctr_loc_preds_weight_is_ctr_loc_pred_weight by blast
  also have "... \<le> \<^bold>\<Sum>{\<^bold>\<Sigma>(p,v) \<Rightarrow>\<^sup>* q |d q. q \<in> finals \<and> (p, (v, d), q) \<in> \<lbrakk>A'\<rbrakk>\<^sup>\<odot>}" 
    using SumInf_mono[of "{pvq. \<exists>d q. pvq = (\<^bold>\<Sigma>(p, v)\<Rightarrow>\<^sup>*q) \<and> q \<in> finals \<and> (p, (v, d), q) \<in> \<lbrakk>A'\<rbrakk>\<^sup>\<odot>}" 
        "{\<^bold>\<Sigma>(p, v)\<Rightarrow>\<^sup>*q |q. q \<in> finals}"] by (force simp add: countable_monoid_rtrancl_wts_to_monoidLTS_all dissect_set)
  also have "... \<le> \<^bold>\<Sum>{d |d q. q \<in> finals \<and> (p, (v, d), q) \<in> \<lbrakk>A'\<rbrakk>\<^sup>\<odot>}" 
    using SumInf_mono_wrt_img_of_set[of 
        "\<lambda>(d, q). q \<in> finals \<and> (p, (v, d), q) \<in> \<lbrakk>A'\<rbrakk>\<^sup>\<odot>"
        "\<lambda>(d, q). \<^bold>\<Sigma> (p,v) \<Rightarrow>\<^sup>* q"
        "\<lambda>(d, q). d"
        ]
    using soundA' sound_def2 countable_monoid_rtrancl_wts_to_monoidLTS 
    by (force simp add: countable_monoid_rtrancl_wts_to_monoidLTS_all dissect_set)
  also have "... = \<L>(A') (p,v)"
    unfolding accepts_def by (simp split: prod.split)
  finally show ?thesis
    unfolding pv_split by auto
qed

lemma rtranclp_pre_star_geq_pred_weight:
  assumes "pre_star_rule\<^sup>*\<^sup>* (K$ 0) A'"
  shows "\<L>(A') (p,w) \<ge> (\<^bold>\<Sigma>\<^sub>s(p,w)\<Rightarrow>\<^sup>*finals)"
  using pre_star_rule_rtranclp_sound[OF sound_empty, of A'] assms sound_accepts_geq_pred_weight 
  by presburger 

lemma saturation_pre_star_geq_pred_weight:
  assumes "saturation pre_star_rule (K$ 0) A"
  shows "\<L>(A) (p,w) \<ge> (\<^bold>\<Sigma>\<^sub>s(p,w)\<Rightarrow>\<^sup>*finals)"
  using assms rtranclp_pre_star_geq_pred_weight unfolding saturation_def by auto

lemma saturated_pre_star_rule_transition:
  assumes "saturated pre_star_rule A"
  assumes "((p, \<gamma>) \<midarrow>d\<hookrightarrow> (p', w))"
  assumes "(p', (lbl w, d'), q) \<in> \<lbrakk>A\<rbrakk>\<^sup>\<odot>"
  assumes "(A $ (p, \<gamma>, q)) = d''"
  shows "(d'' + (d * d')) = d''"
  using assms unfolding saturated_def using pre_star_rule.intros by blast

lemma saturated_pre_star_rule_transition_leq:
  assumes "saturated pre_star_rule A"
  assumes "((p, \<gamma>) \<midarrow>d\<hookrightarrow> (p', w))"
  assumes "(p', (lbl w, d'), q) \<in> \<lbrakk>A\<rbrakk>\<^sup>\<odot>"
  shows "d * d' \<ge> (A $ (p, \<gamma>, q))"
  by (metis assms meet.inf.absorb_iff2 meet.inf_commute saturated_pre_star_rule_transition)

lemma monoid_rtrancl_wts_to_monoidLTS_if_saturated_is_rule':
  assumes "(p', \<gamma>) \<midarrow>d\<hookrightarrow> (p'', u1)"
    and "saturated pre_star_rule A"
    and "(p'',((lbl u1),d'),q) \<in> \<lbrakk>A\<rbrakk>\<^sup>\<odot>"
  shows "\<exists>D. (p',([\<gamma>], D), q) \<in> \<lbrakk>A\<rbrakk>\<^sup>\<odot> \<and> D \<le> d*d'"
proof -
  have "A $ (p', \<gamma>, q) \<le> d * d'"
    using saturated_pre_star_rule_transition_leq[OF assms(2) assms(1) assms(3)] by auto
  then have "\<exists>D. (p', ([\<gamma>],D),q) \<in> \<lbrakk>A\<rbrakk>\<^sup>\<odot> \<and> D \<le> d*d'"
    using merge_edge_and_monoid_rtrancl_wts_to_monoidLTS assms(3) monoid_rtrancl_wts_to_monoidLTS_refl 
    by fastforce
  then show ?thesis
    by (simp add: mult.assoc)
qed

lemma monoid_rtrancl_wts_to_monoidLTS_if_saturated_is_rule:
  assumes "(p', \<gamma>) \<midarrow>d\<hookrightarrow> (p'', u1)"
    and "saturated pre_star_rule A"
    and "(p'',((lbl u1) @ w1,d'),q) \<in> \<lbrakk>A\<rbrakk>\<^sup>\<odot>"
  shows "\<exists>D. (p',(\<gamma> # w1, D), q) \<in> \<lbrakk>A\<rbrakk>\<^sup>\<odot> \<and> D \<le> d*d'"
proof -
  obtain q1 d1 d2 where t:
    "(p'', ((lbl u1),d1), q1) \<in> \<lbrakk>A\<rbrakk>\<^sup>\<odot>"
    "(q1,(w1,d2),q) \<in> \<lbrakk>A\<rbrakk>\<^sup>\<odot>"
    "d' = d1*d2"
    using monoid_rtrancl_wts_to_monoidLTS_append_split[OF assms(3)] by auto

  have "A $ (p', \<gamma>, q1) \<le> d * d1"
    using monoid_rtrancl_wts_to_monoidLTS_if_saturated_is_rule'[OF assms(1,2) t(1)] monoid_star_swap
    by force
  then have "\<exists>D. (p', (\<gamma>#w1,D),q) \<in> \<lbrakk>A\<rbrakk>\<^sup>\<odot> \<and> D \<le> d*d1*d2"
    using merge_edge_and_monoid_rtrancl_wts_to_monoidLTS t(2) by metis
  then show ?thesis
    by (simp add: t(3) mult.assoc)
qed

lemma accepts_if_is_rule:
  assumes "(p', \<gamma>) \<midarrow>d\<hookrightarrow> (p'', u1)"
    and "saturated pre_star_rule A"
  shows "\<L>(A) (p',(\<gamma> # w1)) \<le> d * \<L>(A) (p'', (lbl u1) @ w1)"
proof -
  have "\<^bold>\<Sum> {d' | d' q. q \<in> finals \<and> (p', (\<gamma> # w1, d'), q) \<in> \<lbrakk>A\<rbrakk>\<^sup>\<odot>} \<le>
         \<^bold>\<Sum> {d * d'| d' q. q \<in> finals \<and> (p'', (lbl u1 @ w1, d'), q) \<in> \<lbrakk>A\<rbrakk>\<^sup>\<odot>}"
    using monoid_rtrancl_wts_to_monoidLTS_if_saturated_is_rule[OF assms(1) assms(2), of w1 ]
      SumInf_bounded_by_SumInf_if_members_bounded[of
        "{d' | d' q. q \<in> finals \<and> (p', (\<gamma> # w1, d'), q) \<in> \<lbrakk>A\<rbrakk>\<^sup>\<odot>}"
        "{d * d'| d' q. q \<in> finals \<and> (p'', (lbl u1 @ w1, d'), q) \<in> \<lbrakk>A\<rbrakk>\<^sup>\<odot>}"]
    using countable_monoid_rtrancl_wts_to_monoidLTS_P by fastforce
  also have "... \<le> d * \<^bold>\<Sum> {d' | d' q. q \<in> finals \<and> (p'', (lbl u1 @ w1, d'), q) \<in> \<lbrakk>A\<rbrakk>\<^sup>\<odot>}"
    using SumInf_left_distr[of "{is_d'. \<exists>d' q. is_d' = d' \<and> q \<in> finals \<and> (p'', (lbl u1 @ w1, d'), q) \<in> \<lbrakk>A\<rbrakk>\<^sup>\<odot>}" d] 
      countable_monoid_rtrancl_wts_to_monoidLTS_P by fastforce
  finally show ?thesis
    using accepts_def[of A finals] by force
qed

lemma accepts_if_saturated_monoid_star_relp:
  assumes "(p', w) \<Midarrow>d\<Rightarrow> (p'', u)"
      and "saturated pre_star_rule A"
    shows "\<L>(A) (p',w) \<le> d * \<L>(A) (p'', u)"
  using assms(1) assms(2) accepts_if_is_rule[of _ _ _ _ _ A] step_relp_elim2 by blast

lemma accepts_if_saturated_monoid_star_relp_final':
  assumes "saturated pre_star_rule A"
  assumes "c \<Midarrow>d\<Rightarrow>\<^sup>* c'" and "fst c' \<in> finals" and "snd c' = []"
  shows "\<L>(A) c \<le> d"
  using assms(2,3,4)
proof (induction rule: monoid_star_relp_induct_rev)
  case (monoid_star_refl c)
  then show ?case
    by (metis dual_order.eq_iff accept_is_one_if_final_empty prod.exhaust_sel)
next
  case (monoid_star_into_rtrancl p'w d p''u c d')
  then have accpt: "\<L>(A) p''u \<le> d'"
    by auto
  define p' where "p' = fst p'w"
  define w where "w = snd p'w"
  define p'' where "p'' = fst p''u"
  define u where "u = snd p''u"
  have p''u_split: "p''u = (p'',u)"
    using p''_def u_def by auto
  have p'w_split: "p'w = (p',w)"
    using p'_def w_def by auto

  show ?case
    using accpt assms(1) accepts_if_saturated_monoid_star_relp idempotent_semiring_ord_class.mult_isol 
      monoid_star_into_rtrancl.hyps(1) order_trans p''u_split p'w_split by blast
qed

lemma accepts_if_saturated_monoid_star_relp_final:
  assumes "saturated pre_star_rule A"
  assumes "c \<Midarrow>d\<Rightarrow>\<^sup>* (p,[])" and "p \<in> finals"
  shows "\<L>(A) c \<le> d"
  using accepts_if_saturated_monoid_star_relp_final' assms by simp 

lemma saturated_pre_star_leq_ctr_loc_pred_weight:
  assumes "saturated pre_star_rule A"
  assumes "q \<in> finals"
  shows "\<L>(A) c \<le> \<^bold>\<Sigma>c\<Rightarrow>\<^sup>*q"
proof -
  define X where "X = \<L>(A) c"
  show ?thesis
    using 
      accepts_if_saturated_monoid_star_relp_final[OF assms(1) _ assms(2), of c]  unfolding X_def[symmetric]
    using leq_ctr_loc_pred_weight_if_leq_all_paths by blast
qed

lemma saturated_pre_star_leq_pred_weight:
  assumes "saturated pre_star_rule A"
  shows "\<L>(A) c \<le> (\<^bold>\<Sigma>\<^sub>sc\<Rightarrow>\<^sup>*finals)"
  using saturated_pre_star_leq_ctr_loc_pred_weight[OF assms, of _ c]
  using leq_ctr_loc_preds_weight_if_leq_ctr_loc_pred_weight by auto 

lemma saturation_pre_star_leq_pred_weight':
  assumes "saturation pre_star_rule A A'"
  shows "\<L>(A') c \<le> (\<^bold>\<Sigma>\<^sub>sc\<Rightarrow>\<^sup>*finals)"
  by (metis (no_types, lifting) assms saturated_pre_star_leq_pred_weight saturation_def)

lemma saturation_pre_star_leq_pred_weight:
  assumes "saturation pre_star_rule (K$ 0) A"
  shows "\<L>(A) c \<le> (\<^bold>\<Sigma>\<^sub>sc\<Rightarrow>\<^sup>*finals)"
  by (metis (no_types, lifting) assms saturated_pre_star_leq_pred_weight saturation_def)

theorem correctness:
  assumes "saturation pre_star_rule (K$ 0) A"
  shows "\<L>(A) (p,w) = (\<^bold>\<Sigma>\<^sub>s(p,w)\<Rightarrow>\<^sup>*finals)"
  using saturation_pre_star_leq_pred_weight[of A "(p,w)", OF assms]
    saturation_pre_star_geq_pred_weight[OF assms, of p w] by order 

theorem correctness':
  assumes "saturation pre_star_rule (K$ 0) A"
  shows "\<L>(A) c = weight_pre_star \<L>(K$ 0) c"
  using correctness[OF assms] weight_pre_star_K0_is_pred_weight by (cases c) auto
end

end


section \<open>Pre* code\<close>

\<comment> \<open>Definition of executable pre_star\<close>
definition pre_star_updates :: "('ctr_loc::finite, 'label::finite, 'weight::bounded_dioid) w_rule set \<Rightarrow> ('ctr_loc, 'label, 'weight) w_transitions \<Rightarrow> (('ctr_loc, 'label) transition \<times> 'weight) set" where
  "pre_star_updates \<Delta> wts =
    (\<Union>((p, \<gamma>), d, (p', w)) \<in> \<Delta>.
        \<Union>(q,d') \<in> monoidLTS_reach \<lbrakk>wts\<rbrakk> p' (WPDS.lbl w).
            {((p, \<gamma>, q), d * d')})"

definition pre_star_step :: "('ctr_loc::finite, 'label::finite, 'weight::bounded_dioid) w_rule set \<Rightarrow> ('ctr_loc, 'label, 'weight) w_transitions \<Rightarrow> ('ctr_loc, 'label, 'weight) w_transitions" where
  "pre_star_step \<Delta> wts = update_wts wts (pre_star_updates \<Delta> wts)"

\<comment> \<open>Faster version that does not include 0 weights.\<close>
definition pre_star_updates_not0 :: "('ctr_loc::finite, 'label::finite, 'weight::bounded_dioid) w_rule set \<Rightarrow> ('ctr_loc, 'label, 'weight) w_transitions \<Rightarrow> (('ctr_loc, 'label) transition \<times> 'weight) set" where
  "pre_star_updates_not0 \<Delta> wts =
    (\<Union>((p, \<gamma>), d, (p', w)) \<in> \<Delta>.
        \<Union>(q,d') \<in> monoidLTS_reach_not0 \<lbrakk>wts\<rbrakk> p' (WPDS.lbl w).
            {((p, \<gamma>, q), d * d')})"

definition pre_star_step_not0 :: "('ctr_loc::finite, 'label::finite, 'weight::bounded_dioid) w_rule set \<Rightarrow> ('ctr_loc, 'label, 'weight) w_transitions \<Rightarrow> ('ctr_loc, 'label, 'weight) w_transitions" where
  "pre_star_step_not0 \<Delta> wts = update_wts wts (pre_star_updates_not0 \<Delta> wts)"

section \<open>Locale: WPDS -- Pre* code\<close>
context WPDS begin
\<comment> \<open>Executable version\<close>
definition "pre_star_loop = while_option (\<lambda>s. pre_star_step \<Delta> s \<noteq> s) (pre_star_step \<Delta>)"

definition "pre_star_loop0 = pre_star_loop (ts_to_wts {})"

definition "pre_star_exec = the o pre_star_loop"

definition "pre_star_exec0 = the pre_star_loop0"


\<comment> \<open>Faster executable version (but needs \<^term>\<open>finite \<Delta>\<close> to prove equivalence)\<close>
definition "pre_star_exec_fast = the o while_option (\<lambda>s. pre_star_step_not0 \<Delta> s \<noteq> s) (pre_star_step_not0 \<Delta>)"

definition "pre_star_exec_fast0 = pre_star_exec_fast (ts_to_wts {})"

definition "accept_pre_star_exec0 = dioidLTS.accepts pre_star_exec_fast0"

end

section \<open>Pre* code\<close>

lemma pre_star_exec_code[code]:
  "WPDS.pre_star_exec \<Delta> s = (let s' = pre_star_step \<Delta> s in if s' = s then s else WPDS.pre_star_exec \<Delta> s')"
  unfolding WPDS.pre_star_exec_def WPDS.pre_star_loop_def o_apply Let_def
  by (subst while_option_unfold) simp

lemma pre_star_exec0_code[code]:
  "WPDS.pre_star_exec0 \<Delta> = WPDS.pre_star_exec \<Delta> (ts_to_wts {})"
  unfolding WPDS.pre_star_exec0_def WPDS.pre_star_exec_def WPDS.pre_star_loop0_def
  by simp

lemma pre_star_exec_code_not0[code]:
  "WPDS.pre_star_exec_fast \<Delta> s = (let s' = pre_star_step_not0 \<Delta> s in if s' = s then s else WPDS.pre_star_exec_fast \<Delta> s')"
  unfolding WPDS.pre_star_exec_fast_def o_apply Let_def
  by (subst while_option_unfold) simp

declare WPDS.pre_star_exec_fast0_def[code]


section \<open>finite_WPDS -- Pre* code proofs\<close>

context finite_WPDS
begin
lemma finite_pre_star_updates: "finite (pre_star_updates \<Delta> s)"
  unfolding pre_star_updates_def using finite_monoidLTS_reach[OF finite_wts] finite_rules by fast

lemma finite_update_weight: "finite {d. (t, d) \<in> pre_star_updates \<Delta> ts}"
  using finite_imageI[OF finite_subset[OF _ finite_pre_star_updates[of ts], of "{(t,d)| d. (t, d) \<in> pre_star_updates \<Delta> ts}"], of snd]
  unfolding image_def by fastforce

\<comment> \<open>Faster version that does not include 0 weights.\<close>
lemma finite_pre_star_updates_not0: "finite (pre_star_updates_not0 \<Delta> s)"
  unfolding pre_star_updates_not0_def using finite_monoidLTS_reach_not0[OF finite_wts] finite_rules by fast

lemma pre_star_step_not0_correct': "pre_star_step_not0 \<Delta> wts = pre_star_step \<Delta> wts"
  unfolding pre_star_step_not0_def pre_star_step_def
proof -
  have 1: "pre_star_updates_not0 \<Delta> wts \<subseteq> pre_star_updates \<Delta> wts"
    unfolding pre_star_updates_not0_def pre_star_updates_def
    using monoidLTS_reach_n0_imp monoid_star_code by fast
  have "\<And>p w. monoidLTS_reach \<lbrakk>wts\<rbrakk> p w \<subseteq> {u. \<exists>q. u = (q, 0)} \<union> monoidLTS_reach_not0 \<lbrakk>wts\<rbrakk> p w"
    apply safe unfolding monoid_star_code[symmetric]
    subgoal for _ _ _ d
      using monoid_star_n0_imp_exec by (cases "d = 0", simp) force
    done
  then have 2: "pre_star_updates \<Delta> wts \<subseteq> pre_star_updates_not0 \<Delta> wts \<union> {u. \<exists>q. u = (q, 0)}"
    unfolding pre_star_updates_not0_def pre_star_updates_def
    by fastforce
  show "update_wts wts (pre_star_updates_not0 \<Delta> wts) = update_wts wts (pre_star_updates \<Delta> wts)"
    apply (rule finfun_ext)
    unfolding update_wts_sum[OF finite_pre_star_updates_not0, of wts wts] update_wts_sum[OF finite_pre_star_updates, of wts wts]
    using sum_snd_with_zeros[OF 1 2 finite_pre_star_updates_not0] by presburger
qed

lemma pre_star_step_not0_correct: "pre_star_step \<Delta> = pre_star_step_not0 \<Delta>"
  using pre_star_step_not0_correct' by presburger

lemma pre_star_exec_fast_correct: "pre_star_exec s = pre_star_exec_fast s"
  unfolding pre_star_exec_def pre_star_loop_def pre_star_exec_fast_def pre_star_step_not0_correct
  by simp

lemma pre_star_exec_fast0_correct: "pre_star_exec0 = pre_star_exec_fast0"
  unfolding pre_star_exec0_code pre_star_exec_fast0_def pre_star_exec_fast_correct by simp


\<comment> \<open>Next we show the correspondence between \<^term>\<open>pre_star_step ts\<close> and the sum \<^term>\<open>\<Sum> {ts'. pre_star_rule ts ts'}\<close>\<close>

lemma pre_star_updates_to_rule: "(t, d) \<in> pre_star_updates \<Delta> ts \<Longrightarrow> ts $ t + d \<noteq> ts $ t \<Longrightarrow> pre_star_rule ts ts(t $+= d)"
  unfolding pre_star_updates_def
  using monoid_star_code add_trans
  by fast

lemma pre_star_rule_to_updates: 
  assumes "pre_star_rule ts ts'"
  shows "\<exists>t d. ts' = ts(t $+= d) \<and> (t, d) \<in> pre_star_updates \<Delta> ts \<and> ts $ t + d \<noteq> ts $ t"
proof -
  obtain p \<gamma> d p' w d' q  where *:
    "ts' = ts((p, \<gamma>, q) $:= ts $ (p, \<gamma>, q) + d * d')"
    "(p, \<gamma>) \<midarrow> d \<hookrightarrow> (p', w)"
    "(p', (lbl w, d'), q) \<in> \<lbrakk>ts\<rbrakk>\<^sup>\<odot>"
    "ts $ (p, \<gamma>, q) + d * d' \<noteq> ts $ (p, \<gamma>, q)"
    using assms pre_star_rule.simps by blast
  then have "((p, \<gamma>, q),d*d') \<in> pre_star_updates \<Delta> ts"
    unfolding pre_star_updates_def using monoid_star_code by fast
  then show ?thesis using * by blast
qed

lemma pre_star_step_to_pre_star_rule_sum: 
  "pre_star_step \<Delta> ts = ts + \<Sum> {ts'. pre_star_rule ts ts'}" (is "?A = ?B")
proof -
  have "?A = ts + \<Sum>{ts(t $+= d) |t d. (t, d) \<in> pre_star_updates \<Delta> ts}"
    unfolding pre_star_step_def update_wts_sum_finfun[OF finite_pre_star_updates] by blast
  moreover have "... = ts + \<Sum>{ts(t $+= d) |t d. (t, d) \<in> pre_star_updates \<Delta> ts \<and> ts $ t + d \<noteq> ts $ t}" (is "ts + \<Sum>?X = ts + \<Sum>?Y")
  proof -
    have f1: "finite ?X" using finite_f_on_set[OF finite_pre_star_updates, of "\<lambda>td. ts(fst td $+= snd td)"] by simp
    have f2: "finite ?Y" using finite_subset[OF _ f1, of ?Y] by blast
    have f3: "finite (insert ts ?X)" using f1 by fastforce
    have f4: "finite (insert ts ?Y)" using f2 by fastforce
    show ?thesis
      unfolding idem_sum_insert[OF f1, of ts, symmetric] idem_sum_insert[OF f2, of ts, symmetric]
      apply (rule finfun_ext)
      subgoal for t
        unfolding sum_finfun_apply[OF f3, of t] sum_finfun_apply[OF f4, of t]
        by (rule arg_cong[of _ _ \<Sum>]) fastforce
      done
  qed
  moreover have "... = ts + \<Sum> {ts'. pre_star_rule ts ts'}"
    apply (rule arg_cong[of _ _ "\<lambda>X. ts + \<Sum> X"]) 
    using pre_star_updates_to_rule[of _ _ ts] pre_star_rule_to_updates[of ts]
    by blast
  ultimately show ?thesis by argo
qed

\<comment> \<open>Finally we show that \<^term>\<open>pre_star_exec ts\<close> is the saturation of \<^term>\<open>pre_star_rule\<close> from \<^term>\<open>ts\<close>.\<close>

\<comment> \<open>We need a version of pre_star_rule without the requirement that the next \<^term>\<open>ts\<close> is different.
   This allows proving the mono property below, which does not hold for pre_star_rule,
   since at the fixed point, there will no longer exist such a \<^term>\<open>ts'\<close>.\<close>
inductive non_strict_pre_star_rule :: "('ctr_loc, 'label, 'weight) w_transitions saturation_rule" where
 "((p, \<gamma>) \<midarrow>d\<hookrightarrow> (p', w)) \<Longrightarrow> (p', (lbl w, d'), q) \<in> \<lbrakk>ts\<rbrakk>\<^sup>\<odot> 
  \<Longrightarrow> non_strict_pre_star_rule ts ts((p, \<gamma>, q) $:= ts $ (p, \<gamma>, q) + (d * d'))"

lemma pre_star_rule_is_non_equal_pure: "pre_star_rule ts ts' = strict_rule non_strict_pre_star_rule ts ts'"
  unfolding strict_rule.simps pre_star_rule.simps non_strict_pre_star_rule.simps 
  apply simp
  apply safe
    apply blast
   apply (metis finfun_add_update_apply_same)
  by fastforce

lemma pure_pre_star_rule_less_eq: "non_strict_pre_star_rule ts ts' \<Longrightarrow> ts' \<le> ts" 
  unfolding non_strict_pre_star_rule.simps using finfun_add_update_less_eq by fast

lemma pure_pre_star_rule_mono:
  assumes "ts\<^sub>3 \<le> ts\<^sub>1"
  assumes "non_strict_pre_star_rule ts\<^sub>1 ts\<^sub>2"
  shows "\<exists>ts'. non_strict_pre_star_rule ts\<^sub>3 ts' \<and> ts' \<le> ts\<^sub>2"
proof -
  obtain p \<gamma> d p' w d' q where ts2: 
    "ts\<^sub>2 = ts\<^sub>1((p, \<gamma>, q) $+= d * d')"
    "(p, \<gamma>) \<midarrow>d\<hookrightarrow> (p', w)" 
    "(p', (lbl w, d'), q) \<in> \<lbrakk>ts\<^sub>1\<rbrakk>\<^sup>\<odot>" 
    using assms(2) unfolding non_strict_pre_star_rule.simps by blast
  obtain d'' where d'': "(p', (lbl w, d''), q) \<in> \<lbrakk>ts\<^sub>3\<rbrakk>\<^sup>\<odot>" "d'' \<le> d'"
    using wts_monoid_rtrancl_mono[OF assms(1) ts2(3)] by blast
  have "ts\<^sub>3((p, \<gamma>, q) $+= d * d'') \<le> ts\<^sub>2" unfolding ts2(1) using d''(2) assms(1) 
    by (metis finfun_add_update_same_mono idempotent_semiring_ord_class.subdistl meet.inf.absorb_iff2)
  then show ?thesis
    using non_strict_pre_star_rule.intros[OF ts2(2) d''(1)] by blast
qed

lemma add_saturation_pre_star: "add_saturation non_strict_pre_star_rule"
  apply standard
  using pure_pre_star_rule_less_eq pure_pre_star_rule_mono finite_pre_star_rule_set pre_star_rule_is_non_equal_pure 
  by auto

lemma sum_saturation_pre_star: "sum_saturation (pre_star_step \<Delta>) non_strict_pre_star_rule"
  apply standard
  using add_saturation_unfold[OF add_saturation_pre_star] pre_star_rule_is_non_equal_pure pre_star_step_to_pre_star_rule_sum
  by auto

lemma saturation_pre_star_exec: "saturation pre_star_rule ts (pre_star_exec ts)"
  using sum_saturation.saturation_exec_correct[OF sum_saturation_pre_star]
  unfolding pre_star_rule_is_non_equal_pure pre_star_exec_def step_saturation.saturation_exec_def 
            pre_star_loop_def step_saturation.step_loop_def
  by blast

lemma pre_star_exec0_simp: "pre_star_exec0 = pre_star_exec (K$0)" 
  by (simp add: pre_star_exec0_def pre_star_exec_def pre_star_loop0_def)

lemma saturation_pre_star_exec0: "saturation pre_star_rule (ts_to_wts {}) pre_star_exec0"
  using saturation_pre_star_exec pre_star_exec0_simp by simp


context
  fixes rule_partition
  assumes rule_partition_def: "\<Union>rule_partition = \<Delta>"
  assumes finite_rule_partition: "finite rule_partition"
begin
definition "parallel_pre_star_step ts = ts + (\<Sum>r\<in>rule_partition. WPDS.pre_star_exec_fast r ts)"
definition "parallel_pre_star_exec = step_saturation.saturation_exec parallel_pre_star_step"

lemma r_sub: "r\<in>rule_partition \<Longrightarrow> r \<subseteq> \<Delta>"
  using rule_partition_def by blast
lemma finite_r: "r\<in>rule_partition \<Longrightarrow> finite r"
  by (fact finite_subset[OF r_sub finite_rules])
lemma finite_WPDS_r: "r\<in>rule_partition \<Longrightarrow> finite_WPDS r"
  unfolding finite_WPDS_def by (fact finite_r)

lemma exec_def2:"r\<in>rule_partition \<Longrightarrow> WPDS.pre_star_exec_fast r ts = step_saturation.saturation_exec (pre_star_step r) ts"
  apply (simp add: finite_WPDS.pre_star_exec_fast_correct[symmetric, of r ts, OF finite_WPDS_r])
  unfolding WPDS.pre_star_exec_def WPDS.pre_star_loop_def step_saturation.saturation_exec_def step_saturation.step_loop_def
  by blast
lemma parallel_pre_star_step_def2':
  "ts + (\<Sum>r\<in>rule_partition. WPDS.pre_star_exec_fast r ts) = ts + (\<Sum>step\<^sub>i\<in>{pre_star_step r |r. r \<in> rule_partition}. step_saturation.saturation_exec step\<^sub>i ts)" (is "ts + ?A = ts + ?B")
proof -
  have F:"finite {pre_star_step r |r. r \<in> rule_partition}" using finite_rule_partition by simp
  have "?B = (\<Sum>r \<in> rule_partition. step_saturation.saturation_exec (pre_star_step r) ts)"
    unfolding idem_sum_image[OF finite_rule_partition, of "\<lambda>r. step_saturation.saturation_exec (pre_star_step r) ts", symmetric]
              idem_sum_image[OF F, of "\<lambda>step\<^sub>i. step_saturation.saturation_exec step\<^sub>i ts", symmetric]
    by (rule arg_cong[of _ _ "\<Sum>"]) blast
  moreover have "... = ?A" 
    using exec_def2[of _ ts] by simp
  ultimately show ?thesis by argo
qed
lemma parallel_pre_star_step_def2: "parallel_pre_star_step ts = ts + (\<Sum>step\<^sub>i\<in>{pre_star_step r |r. r \<in> rule_partition}. step_saturation.saturation_exec step\<^sub>i ts)"
  unfolding parallel_pre_star_step_def by (fact parallel_pre_star_step_def2')

lemma non_strict_pre_star_rule_sub_le:
  assumes "r\<in>rule_partition"
  shows "finite_WPDS.non_strict_pre_star_rule r \<le> non_strict_pre_star_rule"
  using r_sub[OF assms(1)] non_strict_pre_star_rule.simps 
        finite_WPDS.non_strict_pre_star_rule.simps[OF finite_WPDS_r[OF assms(1)]]
  by fast

lemma partition_steps_are_rules: "r \<in> rule_partition \<Longrightarrow> (weak_rule non_strict_pre_star_rule)\<^sup>*\<^sup>* ts (pre_star_step r ts)"
  using weak_star_mono[OF non_strict_pre_star_rule_sub_le]
        sum_saturation.weak_star_step[OF finite_WPDS.sum_saturation_pre_star[OF finite_WPDS_r]]
  by blast

lemma pre_star_rule_mono: "r \<subseteq> r' \<Longrightarrow> WPDS.pre_star_rule r \<le> WPDS.pre_star_rule r'"
  unfolding WPDS.pre_star_rule.simps by blast

lemma partition_sum_less_eq_sum: "ts + \<Sum>{pre_star_step r ts |r. r \<in> rule_partition} \<le> ts + \<Sum>{ts'. pre_star_rule ts ts'}"
proof -
  have "finite {Collect (WPDS.pre_star_rule r ts) |r. r \<in> rule_partition}"
    using finite_imageI[OF finite_rule_partition] by (simp add: setcompr_eq_image)
  moreover have "\<Union>{Collect (WPDS.pre_star_rule r ts) |r. r\<in>rule_partition} = Collect (pre_star_rule ts)"
    using rule_partition_def unfolding WPDS.pre_star_rule.simps by blast
  ultimately have eq:"\<Sum> {(\<Sum> x) |x. x \<in> {Collect (WPDS.pre_star_rule r ts) |r. r \<in> rule_partition}} = \<Sum> (Collect (pre_star_rule ts))" 
    using idem_sum_sum finite_pre_star_rule_set by fastforce
  have "ts + \<Sum> {ts + \<Sum> (Collect (WPDS.pre_star_rule r ts)) |r. r \<in> rule_partition} = ts + \<Sum> {\<Sum> (Collect (WPDS.pre_star_rule r ts)) |r. r\<in>rule_partition}"
    using idem_sum_distrib'[OF finite_imageI[OF finite_rule_partition], of ts "\<lambda>r. \<Sum> (Collect (WPDS.pre_star_rule r ts))"]
    by (simp add: image_image setcompr_eq_image)
  moreover have "... \<le> ts + \<Sum> (Collect (pre_star_rule ts))"
    unfolding eq[symmetric] by (simp add: image_image setcompr_eq_image)
  ultimately show ?thesis
    by (simp add: sum_set_image_cong'[OF finite_rule_partition finite_WPDS.pre_star_step_to_pre_star_rule_sum[OF finite_WPDS_r, of _ ts], of id, simplified])
qed

lemma partition_fixp_implies_fixp:
  assumes "ts = ts + (\<Sum>step\<^sub>i\<in>{pre_star_step r |r. r \<in> rule_partition}. step\<^sub>i ts)"
  shows "ts = ts + \<Sum> {ts'. pre_star_rule ts ts'}"
proof -
  have F:"finite {pre_star_step r |r. r \<in> rule_partition}" using finite_rule_partition by simp
  have "(\<Sum>step\<^sub>i\<in>{pre_star_step r |r. r \<in> rule_partition}. step\<^sub>i ts) = \<Sum> {pre_star_step r ts | r. r \<in> rule_partition}"
    unfolding idem_sum_image[OF F, of "\<lambda>step\<^sub>i. step\<^sub>i ts", symmetric]
    by (rule arg_cong[of _ _ "\<Sum>"]) blast
  then have "ts = ts + \<Sum> {pre_star_step r ts | r. r \<in> rule_partition}"
    using assms by argo
  then show ?thesis using partition_sum_less_eq_sum[of ts]
    by (simp add: meet.inf_absorb1)
qed

lemma rule_partition_ok: "par_saturation parallel_pre_star_step non_strict_pre_star_rule {pre_star_step r |r. r\<in>rule_partition}"
  apply standard
  using add_saturation_unfold[OF add_saturation_pre_star] pre_star_rule_is_non_equal_pure 
        finite_rule_partition parallel_pre_star_step_def2 partition_steps_are_rules partition_fixp_implies_fixp 
  by auto

lemma saturation_parallel_pre_star_exec: "saturation pre_star_rule ts (parallel_pre_star_exec ts)"
  using par_saturation.saturation_saturation_exec[OF rule_partition_ok]
  unfolding pre_star_rule_is_non_equal_pure parallel_pre_star_exec_def
  by blast

end


end


section \<open>Pre* on WAutomata\<close>

datatype ('ctr_loc, 'noninit) state =
  is_Init: Init (the_Ctr_Loc: 'ctr_loc)
  | is_Noninit: Noninit (the_St: 'noninit)

definition inits_set :: "('ctr_loc::finite, 'noninit::finite) state set" where 
  "inits_set = {q. is_Init q}"

lemma finite_card_states':
  assumes "finite (X :: 'ctr_loc::finite set)"
  assumes "finite (Y :: 'noninit::finite set)"
  shows "card (Init ` X \<union> Noninit ` Y) = card X + card Y"
  using assms
proof (induction "card X + card Y" arbitrary: X Y)
  case 0
  then show ?case
    by auto
next
  case (Suc n)
  have "X \<noteq> {} \<or> Y \<noteq> {}"
    using Suc.hyps(2) by force
  then show ?case
  proof
    assume "X \<noteq> {}"
    obtain x where "x \<in> X"
      using \<open>X \<noteq> {}\<close> by blast
    define X' where "X' = X - {x}"
    have "card (Init ` X' \<union> Noninit ` Y) = card X' + card Y"
      by (metis Suc.hyps(1) Suc.hyps(2) Suc.prems(1) Suc.prems(2) X'_def \<open>x \<in> X\<close>
          ab_semigroup_add_class.add_ac(1) card_Suc_Diff1 diff_add_inverse finite.emptyI 
          finite_Diff2 finite_Diff_insert plus_1_eq_Suc)
    have "card X = Suc (card X')"
      by (metis Suc.prems(1) X'_def \<open>x \<in> X\<close> card.remove)
    have "Init ` X = {Init x} \<union> Init ` X' "
      using X'_def \<open>x \<in> X\<close> by blast
    have "card (Init ` X \<union> Noninit ` Y) = card ({Init x} \<union> Init ` X' \<union> Noninit ` Y)"
      by (simp add: \<open>Init ` X = {Init x} \<union> Init ` X'\<close>)
    also have "... = Suc (card (Init ` X' \<union> Noninit ` Y))"
      by (smt (verit, del_insts) Diff_empty Diff_insert0 Suc.prems(1) Suc.prems(2) UnE 
          Un_insert_left X'_def card_insert_disjoint finite.insertI finite_Diff2 finite_Un 
          finite_imageI imageE insertCI insert_Diff1 mk_disjoint_insert state.distinct(1) 
          state.inject(1) sup_bot_left)
    also have "... = Suc (card X') + card Y"
      using \<open>card (Init ` X' \<union> Noninit ` Y) = card X' + card Y\<close> by presburger
    also have "... = card X + card Y"
      using \<open>card X = Suc (card X')\<close> by presburger
    finally show ?case
      .
  next
    assume "Y \<noteq> {}"
    obtain y where "y \<in> Y"
      using \<open>Y \<noteq> {}\<close> by blast
    define Y' where "Y' = Y - {y}"
    have "card (Init ` X \<union> Noninit ` Y') = card X + card Y'"
      by (metis (full_types) Suc.hyps(1) Suc.hyps(2) Suc.prems(1) Suc.prems(2) Suc_inject Y'_def
          \<open>y \<in> Y\<close> add.left_commute card.remove finite.emptyI finite_Diff2 finite_insert 
          plus_1_eq_Suc)
    have "card Y = Suc (card Y')"
      by (metis Suc.prems(2) Y'_def \<open>y \<in> Y\<close> card.remove)
    have "Noninit ` Y = {Noninit y} \<union> Noninit ` Y' "
      using Y'_def \<open>y \<in> Y\<close> by blast
    have "card (Init ` X \<union> Noninit ` Y) = card (Init ` X \<union> {Noninit y} \<union> Noninit ` Y')"
      by (simp add: \<open>Noninit ` Y = {Noninit y} \<union> Noninit ` Y'\<close>)
    also have "... = Suc (card (Init ` X \<union> Noninit ` Y'))"
      by (smt (z3) Diff_insert_absorb Suc.prems(1) Suc.prems(2) Un_iff Un_insert_left 
          Un_insert_right Y'_def \<open>y \<in> Y\<close> card_insert_disjoint finite_Un finite_imageI image_iff
          insertE insert_is_Un insert_not_empty mk_disjoint_insert state.distinct(1) state.inject(2) 
          sup_bot.right_neutral)
    also have "... = card X + Suc (card Y')"
      using \<open>card (Init ` X \<union> Noninit ` Y') = card X + card Y'\<close> by presburger
    also have "... = card X + card Y"
      using \<open>card Y = Suc (card Y')\<close> by presburger
    finally show ?case
      .
  qed
qed

lemma finite_card_states:
  assumes "finite (UNIV :: 'ctr_loc::finite set)"
  assumes "finite (UNIV :: 'noninit::finite set)"
  shows "card (UNIV :: ('ctr_loc, 'noninit) state set) = card (UNIV :: 'ctr_loc set) + card (UNIV :: 'noninit set)"
proof -
  define Init' :: "'ctr_loc \<Rightarrow> ('ctr_loc, 'noninit) state" where
    "Init' = Init"
  define Noninit' :: "'noninit \<Rightarrow> ('ctr_loc, 'noninit) state" where
    "Noninit' = Noninit"
  have split: "UNIV = (Init' ` UNIV) \<union> (Noninit' ` UNIV)"
    unfolding Init'_def Noninit'_def
  proof (rule; rule; rule)
    fix x :: "('ctr_loc, 'noninit) state"
    assume "x \<in> UNIV"
    moreover
    assume "x \<notin> range Noninit"
    ultimately
    show "x \<in> range Init"
      by (metis range_eqI state.exhaust)
  qed
  have "CARD(('ctr_loc, 'noninit) state) = card ((Init' ` UNIV) \<union> (Noninit' ` UNIV))"
    using split by auto
  also
  have "... = CARD('ctr_loc) + CARD('noninit)"
    using finite_card_states'[of UNIV UNIV] assms unfolding Init'_def Noninit'_def by auto
  finally
  show ?thesis
    .
qed

lemma UNIV_state: "UNIV = Init ` UNIV \<union> Noninit ` UNIV"
proof -
  have "x \<in> range Init" if "x \<notin> range Noninit" for x :: "('a,'b) state"
    using that by (cases x) simp_all
  then show ?thesis by auto
qed

instance state :: (finite, finite) finite proof
  show "finite (UNIV::('a,'b) state set)" unfolding UNIV_state by fastforce
qed

\<comment> \<open>instantiation: Enumerability of states\<close> 
instantiation state :: (enum, enum) enum begin
definition "enum_class.enum = map Init enum_class.enum @ map Noninit enum_class.enum"

definition "enum_class.enum_all P \<longleftrightarrow> enum_class.enum_all (\<lambda>x. P (Init x)) \<and> enum_class.enum_all (\<lambda>x. P (Noninit x))"

definition "enum_class.enum_ex P \<longleftrightarrow> enum_class.enum_ex (\<lambda>x. P (Init x)) \<or> enum_class.enum_ex (\<lambda>x. P (Noninit x))"

instance proof 
qed (simp_all only: enum_state_def enum_all_state_def enum_ex_state_def UNIV_state,
    auto simp add: enum_UNIV distinct_map enum_distinct inj_def) 
end

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

\<comment> \<open>instantiation: Cardinatily of operations type\<close>
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


section \<open>Locale: WPDS_with_W_automata_no_assms\<close>

locale WPDS_with_W_automata_no_assms = WPDS \<Delta>
  for \<Delta> :: "('ctr_loc::finite, 'label::finite, 'weight::bounded_dioid) w_rule set"
  and ts0 :: "(('ctr_loc, 'noninit::finite) state, 'label, 'weight) w_transitions"
begin 

definition init_rules :: "(('ctr_loc, 'noninit) state, 'label, 'weight) w_rule set" where 
  "init_rules = {((Init p, \<gamma>), d, (Init p', w)) | p \<gamma> d p' w. (p,\<gamma>) \<midarrow>d\<hookrightarrow> (p',w)}"

definition pop_ts0_rules :: "(('ctr_loc, 'noninit) state, 'label, 'weight) w_rule set" where 
  "pop_ts0_rules = {((p,\<gamma>), d, (q, pop)) | p \<gamma> d q. ts0 $ (p,\<gamma>,q) = d}"

definition \<Delta>\<^sub>t\<^sub>s\<^sub>0 :: "(('ctr_loc, 'noninit) state, 'label, 'weight) w_rule set" where 
 "\<Delta>\<^sub>t\<^sub>s\<^sub>0 = init_rules \<union> pop_ts0_rules"

lemma init_rules_def2: "init_rules = (\<Union>((p, \<gamma>), d, (p', w)) \<in> \<Delta>. {((Init p, \<gamma>), d, (Init p', w))})"
  unfolding WPDS_with_W_automata_no_assms.init_rules_def by fast

interpretation augmented_WPDS: WPDS \<Delta>\<^sub>t\<^sub>s\<^sub>0 .

interpretation augmented_dioidLTS: dioidLTS augmented_WPDS.transition_rel .

definition pre_star_exec' where
  "pre_star_exec' = augmented_WPDS.pre_star_exec_fast0"

definition accept_pre_star_exec0' where
  "accept_pre_star_exec0' = augmented_WPDS.accept_pre_star_exec0"

end

section \<open>Code declarations\<close>
declare WPDS_with_W_automata_no_assms.init_rules_def2[code]

lemma pop_ts0_rules_def2[code]: 
  fixes ts :: "(('ctr_loc::enum, 'noninit::enum) state, 'label::enum, 'weight::bounded_dioid) w_transitions"
  shows "WPDS_with_W_automata_no_assms.pop_ts0_rules ts0 = (\<Union>(p, \<gamma>, q) \<in> set Enum.enum. {((p,\<gamma>), ts0 $ (p,\<gamma>,q), (q, pop))})"
  unfolding WPDS_with_W_automata_no_assms.pop_ts0_rules_def using Enum.enum_class.UNIV_enum by blast

declare WPDS_with_W_automata_no_assms.\<Delta>\<^sub>t\<^sub>s\<^sub>0_def[code]
declare WPDS_with_W_automata_no_assms.pre_star_exec'_def[code]
declare WPDS_with_W_automata_no_assms.accept_pre_star_exec0'_def[code]

abbreviation "pre_star_exec \<Delta> ts \<equiv> WPDS_with_W_automata_no_assms.pre_star_exec' \<Delta> ts"


section \<open>Locale: WPDS_with_W_automata\<close>
locale WPDS_with_W_automata = WPDS_with_W_automata_no_assms \<Delta> ts0 + finite_WPDS \<Delta>
  for \<Delta> :: "('ctr_loc::finite, 'label::finite, 'weight::bounded_dioid) w_rule set"
  and ts0 :: "(('ctr_loc, 'noninit::finite) state, 'label, 'weight) w_transitions" +
  assumes no_transition_to_init: "is_Init q \<Longrightarrow> ts0 $ (p, \<gamma>, q) = 0"
begin

interpretation countable_dioidLTS transition_rel proof
  show "countable transition_rel" by (fact countable_transition_rel)
qed

definition "step_relp' = step_relp"

notation step_relp (infix "\<Rightarrow>" 80)
notation step_starp (infix "\<Rightarrow>\<^sup>*" 80)
notation l_step_relp ("(_)/ \<Midarrow> (_)/ \<Rightarrow> (_)/" [70,70,80] 80)

definition "l_step_relp' = l_step_relp"

notation monoid_star_relp ("(_)/ \<Midarrow> (_)/ \<Rightarrow>\<^sup>* (_)/" [90,90,100] 100) 

lemma finite_init_rules: "finite init_rules" 
  unfolding init_rules_def
  using finite_f_on_set[OF finite_rules, of "\<lambda>x. (case x of ((p, \<gamma>), d, p', w) \<Rightarrow> ((Init p, \<gamma>), d, Init p', w))"]
  by force

lemma finite_pop_ts0: "finite pop_ts0_rules" 
proof -
  have f:"finite {t | t d. ts0 $ t = d}" by simp
  show ?thesis unfolding pop_ts0_rules_def
    using finite_image_set[OF f, of "\<lambda>x. (case x of (p, \<gamma>, q) \<Rightarrow> ((p, \<gamma>), ts0 $ x, q, pop))"] by force
qed

lemma finite_\<Delta>\<^sub>t\<^sub>s\<^sub>0: "finite \<Delta>\<^sub>t\<^sub>s\<^sub>0"
  unfolding \<Delta>\<^sub>t\<^sub>s\<^sub>0_def
proof safe
  show "finite init_rules" by (fact finite_init_rules)
next 
  show "finite pop_ts0_rules" by (fact finite_pop_ts0)
qed

lemma countable_monoid_augmented: "countable ((WPDS.transition_rel \<Delta>\<^sub>t\<^sub>s\<^sub>0)\<^sup>\<odot>)"
  by (fact countable_monoid_rtrancl[OF finite_WPDS.countable_transition_rel[unfolded finite_WPDS_def, OF finite_\<Delta>\<^sub>t\<^sub>s\<^sub>0]])

lemma WPDS_instance[simp]:"finite_WPDS \<Delta>\<^sub>t\<^sub>s\<^sub>0"
  by (simp add: finite_WPDS_def finite_\<Delta>\<^sub>t\<^sub>s\<^sub>0)

lemma monoidLTS_instance[simp]: "countable_monoidLTS (WPDS.transition_rel \<Delta>\<^sub>t\<^sub>s\<^sub>0)"
  by (simp add: countable_monoidLTS_def finite_WPDS.countable_transition_rel[of \<Delta>\<^sub>t\<^sub>s\<^sub>0])

lemma dioidLTS_instance[simp]: "countable_dioidLTS (WPDS.transition_rel \<Delta>\<^sub>t\<^sub>s\<^sub>0)"
  by (simp add: countable_dioidLTS_def)

interpretation augmented_WPDS: finite_WPDS \<Delta>\<^sub>t\<^sub>s\<^sub>0 by simp

interpretation augmented_dioidLTS: countable_dioidLTS augmented_WPDS.transition_rel by simp

lemma pre_star_exec'_def2: "pre_star_exec' = augmented_WPDS.pre_star_exec0" 
  unfolding pre_star_exec'_def using augmented_WPDS.pre_star_exec_fast0_correct by presburger

definition augmented_rules_reach_empty where
  "augmented_rules_reach_empty finals p w d = (\<exists>p' \<in> finals. ((Init p, w), d, (p',[])) \<in> monoidLTS.monoid_star (WPDS.transition_rel \<Delta>\<^sub>t\<^sub>s\<^sub>0))"

definition reach_conf_in_W_automaton where
  "reach_conf_in_W_automaton finals p w d = (\<exists>d' p' w'. (p, w) \<Midarrow>d'\<Rightarrow>\<^sup>* (p', w') \<and> d = d' * accepts ts0 finals (Init p',w'))"

lemma reach_conf_in_W_automaton_unfold:
  "\<^bold>\<Sum>{d. reach_conf_in_W_automaton finals p w d} = 
   \<^bold>\<Sum>{d' * d | d d' p' w' q. q \<in> finals \<and> (Init p', (w', d), q) \<in> \<lbrakk>ts0\<rbrakk>\<^sup>\<odot> \<and> (p, w) \<Midarrow> d' \<Rightarrow>\<^sup>* (p', w')}"
proof -
  have c: "\<And>d' p' w'. countable {(d, (d', (p', w'))) |d. \<exists>q. q \<in> finals \<and> (Init p', (w', d), q) \<in> \<lbrakk>ts0\<rbrakk>\<^sup>\<odot>}"
    subgoal for d' p' w'
    using countable_f_on_P_Q_set2[of "\<lambda>d q. (Init p', (w', d), q) \<in> \<lbrakk>ts0\<rbrakk>\<^sup>\<odot>" "\<lambda>d q. d" "\<lambda>d q. q \<in> finals"]
    using countable_subset[OF _ countable_f_on_set[OF countable_monoid_rtrancl[OF countable_wts[of ts0]], 
                                                   of "\<lambda>x. (snd (fst (snd x)), snd (snd x))", simplified],
                           of "{(d, q). (Init p', (w', d), q) \<in> \<lbrakk>ts0\<rbrakk>\<^sup>\<odot>}"]
    by (auto simp add: dissect_set) done
  have 
    "\<^bold>\<Sum>{d. reach_conf_in_W_automaton finals p w d} =
     \<^bold>\<Sum> {d' * \<^bold>\<Sum> {d. \<exists>q. q \<in> finals \<and> (Init p', (w', d), q) \<in> \<lbrakk>ts0\<rbrakk>\<^sup>\<odot>} | d' p' w'. (p, w) \<Midarrow> d' \<Rightarrow>\<^sup>* (p', w')}"
    unfolding reach_conf_in_W_automaton_def accepts_def by simp meson
  moreover have 
    "\<^bold>\<Sum> {d' * \<^bold>\<Sum> {d. \<exists>q. q \<in> finals \<and> (Init p', (w', d), q) \<in> \<lbrakk>ts0\<rbrakk>\<^sup>\<odot>} | d' p' w'. (p, w) \<Midarrow> d' \<Rightarrow>\<^sup>* (p', w')} = 
     \<^bold>\<Sum> {d' * d | d d' p' w' q. q \<in> finals \<and> (Init p', (w', d), q) \<in> \<lbrakk>ts0\<rbrakk>\<^sup>\<odot> \<and> (p, w) \<Midarrow> d' \<Rightarrow>\<^sup>* (p', w')}"
    using SumInf_of_SumInf_left_distr[
        of "\<lambda>(d',p',w'). (p, w) \<Midarrow> d' \<Rightarrow>\<^sup>* (p', w')" 
           "\<lambda>d (d',p',w'). \<exists>q. q \<in> finals \<and> (Init p', (w', d), q) \<in> \<lbrakk>ts0\<rbrakk>\<^sup>\<odot>"
           "\<lambda>(d',p',w'). d'"
           "\<lambda>d (d',p',w'). d", simplified]
    by (auto simp add: countable_monoid_star_variant1 c) meson
  ultimately show ?thesis by argo
qed

lemma WPDS_transition_rel_mono:
  assumes "finite Y" and "X \<subseteq> Y" and "((p,v),d,(q,w)) \<in> WPDS.transition_rel X"
  shows "((p,v),d,(q,w)) \<in> WPDS.transition_rel Y"
proof -
  have "\<And>p v d q w. WPDS.is_rule X (p, v) d (q, w) \<Longrightarrow> WPDS.is_rule Y (p, v) d (q, w)"
    using assms(2) by blast
  then show ?thesis 
    using assms(3) WPDS.transition_rel.intros
    by (cases rule: WPDS.transition_rel.cases[OF assms(3)]) fast
qed

lemma WPDS_LTS_mono:
  assumes "finite Y" and "X \<subseteq> Y"
  shows "(WPDS.transition_rel X)\<^sup>\<odot> \<subseteq> (WPDS.transition_rel Y)\<^sup>\<odot>"
  using WPDS_transition_rel_mono[OF assms] 
  apply safe
  subgoal for p v d q w
    using mono_monoid_rtrancl[of "WPDS.transition_rel X" "WPDS.transition_rel Y" "(p,v)" d "(q,w)"]
    by fast
  done

lemma ts_subset_aug_rules: 
  "(WPDS.transition_rel pop_ts0_rules)\<^sup>\<odot> 
   \<subseteq> (WPDS.transition_rel \<Delta>\<^sub>t\<^sub>s\<^sub>0)\<^sup>\<odot>"
  using WPDS_LTS_mono[OF finite_\<Delta>\<^sub>t\<^sub>s\<^sub>0, of pop_ts0_rules] 
  unfolding \<Delta>\<^sub>t\<^sub>s\<^sub>0_def by blast

lemma ts_to_pop_rule:
  assumes "(p, ([\<gamma>], d), q) \<in> \<lbrakk>ts0\<rbrakk>"
  shows "((p, \<gamma>#w), d, q, w) \<in> WPDS.transition_rel pop_ts0_rules"
  using WAutomaton.wts_label_d[OF assms]
        WPDS.transition_rel.simps[where \<Delta>=pop_ts0_rules]
  unfolding pop_ts0_rules_def by simp

lemma wts_to_monoidLTS_only_single_w:
  assumes "(p, (w, d), q') \<in> \<lbrakk>ts0\<rbrakk>"
  shows "w = [hd w]"
  using assms unfolding wts_to_monoidLTS_def by auto

lemma ts_to_pop_rule_step:
  assumes "(p, (w, d), q') \<in> \<lbrakk>ts0\<rbrakk>"
  assumes "((q', w'), d', q, []) \<in> (WPDS.transition_rel pop_ts0_rules)\<^sup>\<odot>"
  shows "((p, w@w'), d*d', q, []) \<in> (WPDS.transition_rel pop_ts0_rules)\<^sup>\<odot>"
proof -
  have a1:"(p, ([hd w], d), q') \<in> \<lbrakk>ts0\<rbrakk>" 
    using assms(1) unfolding wts_to_monoidLTS_def by auto
  have "hd w # w' = w @ w'"
    using wts_to_monoidLTS_only_single_w[OF assms(1)] by simp
  then show ?thesis
    using monoid_rtrancl_into_rtrancl_rev[OF ts_to_pop_rule[OF a1] assms(2)] assms(2) by argo
qed

lemma augmented_rules_1_base:
  assumes "(p, (w, d), q) \<in> \<lbrakk>ts0\<rbrakk>\<^sup>\<odot>"
  shows "((p, w), d, q, []) \<in> (WPDS.transition_rel \<Delta>\<^sub>t\<^sub>s\<^sub>0)\<^sup>\<odot>"
proof -
  { fix wd
    assume "(p, wd, q) \<in> \<lbrakk>ts0\<rbrakk>\<^sup>\<odot>"
    then have "((p, fst wd), snd wd, q, []) \<in> (WPDS.transition_rel pop_ts0_rules)\<^sup>\<odot>"
      apply (induct rule: monoid_rtrancl_induct_rev)
       apply (simp add: one_list_def one_prod_def)
      using ts_to_pop_rule_step
      by simp
  }
  then show ?thesis using assms using ts_subset_aug_rules by auto
qed

lemma rule_to_init_rule:
  assumes "(p, w) \<Midarrow>d\<Rightarrow> (p', w')"
  shows "((Init p, w), d, Init p', w') \<in> WPDS.transition_rel init_rules"
  using assms unfolding init_rules_def l_step_relp_def transition_rel.simps[of p w d p' w']
  by (auto simp add: WPDS.transition_rel.simps[where \<Delta>=init_rules, unfolded init_rules_def])

lemma init_rule_to_rule:
  assumes "((Init p, w), d, Init p', w') \<in> WPDS.transition_rel init_rules"
  shows "(p, w) \<Midarrow>d\<Rightarrow> (p', w')"
  using assms unfolding init_rules_def l_step_relp_def transition_rel.simps[of p w d p' w']
  by (auto simp add: WPDS.transition_rel.simps[where \<Delta>=init_rules, unfolded init_rules_def])

lemma rule_aug_rule: "(p, w) \<Midarrow>d\<Rightarrow> (p', w') \<longleftrightarrow> ((Init p, w), d, Init p', w') \<in> WPDS.transition_rel init_rules"
  using rule_to_init_rule init_rule_to_rule by blast

lemma augmented_rules_1_step:
  fixes d::'weight
  assumes "(p, w) \<Midarrow>d\<Rightarrow> (p', w')"
  assumes "((Init p', w'), d' * d\<^sub>2, q, []) \<in> (WPDS.transition_rel \<Delta>\<^sub>t\<^sub>s\<^sub>0)\<^sup>\<odot>"
  shows "((Init p, w), d * d' * d\<^sub>2, q, []) \<in> (WPDS.transition_rel \<Delta>\<^sub>t\<^sub>s\<^sub>0)\<^sup>\<odot>"
proof -
  have "((Init p, w), d, Init p', w') \<in> WPDS.transition_rel \<Delta>\<^sub>t\<^sub>s\<^sub>0"
    using rule_to_init_rule[OF assms(1)]
    using WPDS_transition_rel_mono[OF finite_\<Delta>\<^sub>t\<^sub>s\<^sub>0, of init_rules]
    unfolding \<Delta>\<^sub>t\<^sub>s\<^sub>0_def by blast
  then show ?thesis
    using assms(2) monoid_rtrancl_into_rtrancl_rev[of "(Init p, w)" d "(Init p', w')" "WPDS.transition_rel \<Delta>\<^sub>t\<^sub>s\<^sub>0" "d' * d\<^sub>2" "(q, [])"]
    by (simp add: mult.assoc)
qed

lemma wpds_lts_induct_rev [consumes 1, case_names wpds_lts_base wpds_lts_step]:
  assumes "(p, w) \<Midarrow>d\<Rightarrow>\<^sup>* (p', w')"
  assumes "(\<And>p w. P p w 1 p w)"
  assumes "\<And>p w d p' w' d' p'' w''. (p, w) \<Midarrow>d\<Rightarrow> (p', w') \<Longrightarrow> P p' w' d' p'' w'' \<Longrightarrow> (p', w') \<Midarrow>d'\<Rightarrow>\<^sup>* (p'', w'') \<Longrightarrow> 
              P p w (d * d') p'' w''"
  shows "P p w d p' w'"
  using monoid_rtranclp_induct_rev[of l_step_relp "(p, w)" d "(p', w')" "\<lambda>pw d pw'. P (fst pw) (snd pw) d (fst pw') (snd pw')"] assms by force

lemma augmented_rules_1:
  assumes "(Init p', (w', d\<^sub>2), q) \<in> \<lbrakk>ts0\<rbrakk>\<^sup>\<odot>"
  assumes "(p, w) \<Midarrow>d\<^sub>1\<Rightarrow>\<^sup>* (p', w')"
  shows "((Init p, w), d\<^sub>1 * d\<^sub>2, q, []) \<in> (WPDS.transition_rel \<Delta>\<^sub>t\<^sub>s\<^sub>0)\<^sup>\<odot>"
  using assms(2,1)
  by (induct rule: wpds_lts_induct_rev)
     (simp_all add: augmented_rules_1_base augmented_rules_1_step)

lemma init_rule_is_Init:
  assumes "((p, w), d, p', w') \<in> WPDS.transition_rel init_rules"
  shows "is_Init p" and "is_Init p'"
  using assms unfolding init_rules_def l_step_relp_def
  by (auto simp add: WPDS.transition_rel.simps[where \<Delta>=init_rules, unfolded init_rules_def])

lemma init_rule_closure_is_Init:
  assumes "((p, w), d, p', w') \<in> (WPDS.transition_rel init_rules)\<^sup>\<odot>"
      and "is_Init p" 
  shows "is_Init p'"
  using assms
  by (cases "(p,w) = (p',w')", simp)
     (induct "(p,w)" d "(p',w')" rule: monoid_rtrancl.induct, auto simp add: init_rule_is_Init(2))

lemma aug_rules_to_init_from_init:
  assumes "((p, w), d, p', w') \<in> WPDS.transition_rel \<Delta>\<^sub>t\<^sub>s\<^sub>0"
      and "is_Init p'" and "d \<noteq> 0"
    shows "is_Init p"
  using assms(1) 
  unfolding WPDS.transition_rel.simps[where \<Delta>=\<Delta>\<^sub>t\<^sub>s\<^sub>0]
  unfolding \<Delta>\<^sub>t\<^sub>s\<^sub>0_def init_rules_def l_step_relp_def pop_ts0_rules_def
  using no_transition_to_init[OF assms(2)] assms(3)
  by fastforce

lemma aug_rules_closure_to_init_from_init:
  assumes "((p, w), d, p', w') \<in> (WPDS.transition_rel \<Delta>\<^sub>t\<^sub>s\<^sub>0)\<^sup>\<odot>"
      and "is_Init p'" and "d \<noteq> 0"
    shows "is_Init p"
  using assms aug_rules_to_init_from_init
  by (induct rule: monoid_rtrancl_pair_induct_rev, simp) fastforce

lemma wpds_lts_init_induct_rev [consumes 1, case_names wpds_lts_base wpds_lts_step]:
  assumes "((Init p, w), d, Init p', w') \<in> (WPDS.transition_rel init_rules)\<^sup>\<odot>"
  assumes "(\<And>p w. P p w 1 p w)"
  assumes "\<And>p w d p' w' d' p'' w''. 
              ((Init p, w), d, (Init p', w')) \<in> WPDS.transition_rel init_rules \<Longrightarrow> 
              P p' w' d' p'' w'' \<Longrightarrow> 
              ((Init p', w'), d', (Init p'', w'')) \<in> (WPDS.transition_rel init_rules)\<^sup>\<odot> \<Longrightarrow> 
              P p w (d * d') p'' w''"
  shows "P p w d p' w'"
proof -
  { 
    fix p w d p' w' d' p'' w''
    assume a:"((p, w), d, p', w') \<in> WPDS.transition_rel init_rules"
       and b:"P (the_Ctr_Loc p') w' d' (the_Ctr_Loc p'') w''"
       and c:"((p', w'), d', p'', w'') \<in> (WPDS.transition_rel init_rules)\<^sup>\<odot>"
    then have ip':"is_Init p'" using init_rule_is_Init(2)[OF a] by blast
    then have ip'':"is_Init p''" using init_rule_closure_is_Init[OF c] by simp
    have  "P (the_Ctr_Loc p) w (d * d') (the_Ctr_Loc p'') w''"
      using state.collapse(1)[OF init_rule_is_Init(1)[OF a]] state.collapse(1)[OF ip'] state.collapse(1)[OF ip''] 
            assms(3) a b c
      by metis
  }
  then show ?thesis
    using monoid_rtrancl_induct_rev[of "(Init p, w)" d "(Init p', w')" "WPDS.transition_rel init_rules"
                                       "\<lambda>pw d pw'. P (the_Ctr_Loc (fst pw)) (snd pw) d (the_Ctr_Loc (fst pw')) (snd pw')", OF assms(1)]
    by (auto simp add: assms(2))
qed

lemma aug_to_init_rule:
  assumes "((Init p, w), d, Init p', w') \<in> WPDS.transition_rel \<Delta>\<^sub>t\<^sub>s\<^sub>0" and "d \<noteq> 0"
  shows "((Init p, w), d, Init p', w') \<in> WPDS.transition_rel init_rules"
  using assms 
  unfolding WPDS.transition_rel.simps[where \<Delta>=\<Delta>\<^sub>t\<^sub>s\<^sub>0]
            WPDS.transition_rel.simps[where \<Delta>=init_rules]
  unfolding \<Delta>\<^sub>t\<^sub>s\<^sub>0_def pop_ts0_rules_def
  using no_transition_to_init by simp

lemma aug_to_init_rule_closure:
  assumes "((p, w), d, p', w') \<in> (WPDS.transition_rel \<Delta>\<^sub>t\<^sub>s\<^sub>0)\<^sup>\<odot>" 
      and "d \<noteq> 0" and "is_Init p" and "is_Init p'"
  shows "((p, w), d, p', w') \<in> (WPDS.transition_rel init_rules)\<^sup>\<odot>"
  using assms
  apply (induct rule: monoid_rtrancl_pair_induct_rev, simp)
  subgoal for p w d p' w' d' p'' w''
    using aug_to_init_rule[of "the_Ctr_Loc p" w d "the_Ctr_Loc p'" w']
          aug_rules_closure_to_init_from_init[of p' w' d' p'' w'']
    using monoid_rtrancl_into_rtrancl_rev[of "(p,w)" d "(p',w')" "WPDS.transition_rel init_rules" d' "(p'',w'')"]
    by force
  done

lemma augmented_rules_2_a':
  assumes "((Init p, w), d, Init p', w') \<in> (WPDS.transition_rel init_rules)\<^sup>\<odot>"
  shows "(p,w) \<Midarrow>d\<Rightarrow>\<^sup>* (p',w')"
  using assms
  apply (induct rule: wpds_lts_init_induct_rev, simp)
  subgoal for p w d p' w' d' p'' w''
    using monoid_rtrancl_into_rtrancl_rev[of "(p, w)" d "(p', w')" transition_rel d' "(p'', w'')"] 
          init_rule_to_rule[of p w d p' w']
    unfolding l_step_relp_def monoid_rtrancl_def
    by fast
  done

lemma augmented_rules_2_a:
  assumes "((Init p, w), d, Init p', w') \<in> (WPDS.transition_rel \<Delta>\<^sub>t\<^sub>s\<^sub>0)\<^sup>\<odot>"
  assumes "d \<noteq> 0"
  shows "(p,w) \<Midarrow>d\<Rightarrow>\<^sup>* (p',w')"
  using assms aug_to_init_rule_closure augmented_rules_2_a' by force

lemma pop_to_ts:
  assumes "((p, \<gamma>#w), d, p', w') \<in> WPDS.transition_rel pop_ts0_rules"
  shows "(p, ([\<gamma>], d), p') \<in> \<lbrakk>ts0\<rbrakk>" and "w = w'"
  using assms
  using WPDS.transition_rel.simps[where \<Delta>=pop_ts0_rules]
  unfolding pop_ts0_rules_def wts_to_monoidLTS_def by auto

lemma pop_to_ts_closure:
  assumes "((p, w), d, q, []) \<in> (WPDS.transition_rel pop_ts0_rules)\<^sup>\<odot>"
  shows "(p, (w, d), q) \<in> \<lbrakk>ts0\<rbrakk>\<^sup>\<odot>"
  using assms
proof (induct w arbitrary: p d)
  case Nil
  have "d = 1 \<and> p = q"
    by (cases rule: monoid_rtrancl_cases_rev[OF Nil])
       (auto simp add: WPDS.transition_rel.simps[where \<Delta>=pop_ts0_rules])
  then show ?case using monoid_rtrancl_refl[of q "\<lbrakk>ts0\<rbrakk>", unfolded one_prod_def one_list_def] by blast
next
  case (Cons \<gamma> w)
  then show ?case
    apply (cases rule: monoid_rtrancl_cases_rev[of "(p,\<gamma>#w)" d "(q,[])" "WPDS.transition_rel pop_ts0_rules"], simp_all) 
    using pop_to_ts[of p \<gamma> w] monoid_rtrancl_into_rtrancl_rev[of p "([\<gamma>],_)" _ "\<lbrakk>ts0\<rbrakk>" "(w,_)" q]
    by fastforce
qed

lemma aug_to_pop_rule:
  assumes "((p, w), d, p', w') \<in> WPDS.transition_rel \<Delta>\<^sub>t\<^sub>s\<^sub>0" 
      and "d \<noteq> 0" and "is_Noninit p"
  shows "((p, w), d, p', w') \<in> WPDS.transition_rel pop_ts0_rules" and "is_Noninit p'"
  using assms aug_rules_to_init_from_init[of p w d p' w']
  unfolding WPDS.transition_rel.simps[where \<Delta>=\<Delta>\<^sub>t\<^sub>s\<^sub>0]
            WPDS.transition_rel.simps[where \<Delta>=pop_ts0_rules]
  unfolding \<Delta>\<^sub>t\<^sub>s\<^sub>0_def init_rules_def 
  using state.exhaust_disc by auto

lemma aug_to_pop_rule':
  assumes "((p, w), d, p', w') \<in> WPDS.transition_rel \<Delta>\<^sub>t\<^sub>s\<^sub>0" 
      and "d \<noteq> 0" and "is_Noninit p'"
  shows "((p, w), d, p', w') \<in> WPDS.transition_rel pop_ts0_rules"
  using assms aug_rules_to_init_from_init[of p w d p' w']
  unfolding WPDS.transition_rel.simps[where \<Delta>=\<Delta>\<^sub>t\<^sub>s\<^sub>0]
            WPDS.transition_rel.simps[where \<Delta>=pop_ts0_rules]
  unfolding \<Delta>\<^sub>t\<^sub>s\<^sub>0_def init_rules_def 
  using state.exhaust_disc by auto

lemma aug_to_pop_rule_closure:
  assumes "((p, w), d, p', w') \<in> (WPDS.transition_rel \<Delta>\<^sub>t\<^sub>s\<^sub>0)\<^sup>\<odot>"
      and "d \<noteq> 0" and "is_Noninit p"
  shows "((p, w), d, p', w') \<in> (WPDS.transition_rel pop_ts0_rules)\<^sup>\<odot>"
  using assms
  apply (induct rule: monoid_rtrancl_pair_induct_rev, simp)
  subgoal for p w d p' w' d' p'' w''
    using aug_to_pop_rule[of p w d p' w']
          monoid_rtrancl_into_rtrancl_rev[of "(p,w)" d "(p',w')" "WPDS.transition_rel pop_ts0_rules" d' "(p'',w'')"]
    by fastforce
  done

lemma augmented_rules_2_b:
  assumes "((p, w), d, p', w') \<in> WPDS.transition_rel \<Delta>\<^sub>t\<^sub>s\<^sub>0"
  assumes "((p', w'), d', q, []) \<in> (WPDS.transition_rel \<Delta>\<^sub>t\<^sub>s\<^sub>0)\<^sup>\<odot>"
  assumes "d \<noteq> 0" and "d' \<noteq> 0" and "is_Noninit p'"
    shows "(p, (w, d*d'), q) \<in> \<lbrakk>ts0\<rbrakk>\<^sup>\<odot>"
proof -
  obtain \<gamma> where a_def:"\<gamma>#w' = w" using aug_to_pop_rule'[OF assms(1,3,5)]
    unfolding WPDS.transition_rel.simps[where \<Delta>=pop_ts0_rules]
    unfolding pop_ts0_rules_def by force
  then have A:"((p, \<gamma>#w'), d, p', w') \<in> WPDS.transition_rel pop_ts0_rules" 
    using aug_to_pop_rule'[OF assms(1,3,5)] by fastforce
  then have "(p, ([\<gamma>], d), p') \<in> \<lbrakk>ts0\<rbrakk>" using pop_to_ts(1) by fast
  then have "(p, ([\<gamma>], d) * (w', d'), q) \<in> \<lbrakk>ts0\<rbrakk>\<^sup>\<odot>"
    using monoid_rtrancl_into_rtrancl_rev[OF _ pop_to_ts_closure[OF aug_to_pop_rule_closure[OF assms(2,4,5)]]]
    by blast
  then show ?thesis by (simp add: a_def)
qed

lemma augmented_rules_2_split:
  assumes "((Init p, w), d, Init p', w') \<in> (WPDS.transition_rel \<Delta>\<^sub>t\<^sub>s\<^sub>0)\<^sup>\<odot>"
  assumes "((Init p', w'), d', Noninit p'', w'') \<in> WPDS.transition_rel \<Delta>\<^sub>t\<^sub>s\<^sub>0"
  assumes "((Noninit p'', w''), d'', q, []) \<in> (WPDS.transition_rel \<Delta>\<^sub>t\<^sub>s\<^sub>0)\<^sup>\<odot>"
  assumes "d \<noteq> 0" and "d' \<noteq> 0" and "d'' \<noteq> 0" and "q \<in> finals"
  shows "\<exists>d\<^sub>2 d\<^sub>1 p' w' q. d * d' * d'' = d\<^sub>1 * d\<^sub>2 \<and> q \<in> finals \<and> (Init p', (w', d\<^sub>2), q) \<in> \<lbrakk>ts0\<rbrakk>\<^sup>\<odot> \<and> (p, w) \<Midarrow>d\<^sub>1\<Rightarrow>\<^sup>* (p', w')"
  using augmented_rules_2_a[OF assms(1,4)] augmented_rules_2_b[OF assms(2,3,5,6)]
  apply simp
  apply (rule exI[of _ "d' * d''"])
  apply (rule exI[of _ d])
  apply (simp add: ac_simps(4))
  apply (rule exI[of _ p'])
  apply (rule exI[of _ w'])
  apply (rule exI[of _ q])
  by (simp add: assms(7))

lemma augmented_rules_2_init_noninit_split:
  assumes "((p\<^sub>1, w\<^sub>1), d\<^sub>1, p\<^sub>2, w\<^sub>2) \<in> (WPDS.transition_rel \<Delta>\<^sub>t\<^sub>s\<^sub>0)\<^sup>\<odot>"
      and "is_Init p\<^sub>1" and "is_Noninit p\<^sub>2"
  shows "\<exists>d p' w' d' p'' w'' d''. d\<^sub>1 = d * d' * d'' \<and>
          ((p\<^sub>1, w\<^sub>1), d, Init p', w') \<in> (WPDS.transition_rel \<Delta>\<^sub>t\<^sub>s\<^sub>0)\<^sup>\<odot> \<and>
          ((Init p', w'), d', Noninit p'', w'') \<in> WPDS.transition_rel \<Delta>\<^sub>t\<^sub>s\<^sub>0 \<and>
          ((Noninit p'', w''), d'', p\<^sub>2, w\<^sub>2) \<in> (WPDS.transition_rel \<Delta>\<^sub>t\<^sub>s\<^sub>0)\<^sup>\<odot>"
  using assms
  apply (induct rule: monoid_rtrancl_pair_induct_rev)
    using state.exhaust_disc
     apply fast
    subgoal for p w d p' w' d' p'' w''
      apply (cases "is_Init p'")
       apply simp
       apply safe
      subgoal for da p'a w'a d'a p''a w''a d''
        apply (rule exI[of _ "d * da"])
        apply (rule exI[of _ p'a])
        apply (rule exI[of _ w'a])
        apply (rule exI[of _ d'a])
        apply (rule exI[of _ p''a])
        apply (rule exI[of _ w''a])
        apply (rule exI[of _ d''])
        by (simp add: ac_simps(4) monoid_rtrancl_into_rtrancl_rev)
      using state.exhaust_disc[of p' "is_Noninit p'"]
      apply simp
      apply (rule exI[of _ 1])
      apply (rule exI[of _ "the_Ctr_Loc p"])
      apply (rule exI[of _ w])
      apply (rule exI[of _ d])
      apply (rule exI[of _ "the_St p'"])
      apply (rule exI[of _ w'])
      apply (rule exI[of _ d'])
      by auto
    done

lemma augmented_rules_2:
  assumes "((Init p, w), d, q, []) \<in> (WPDS.transition_rel \<Delta>\<^sub>t\<^sub>s\<^sub>0)\<^sup>\<odot>"
  assumes "d \<noteq> 0"
  assumes "q \<in> finals"
  shows "\<exists>d\<^sub>2 d\<^sub>1 p' w' q. d = d\<^sub>1 * d\<^sub>2 \<and> q \<in> finals \<and> (Init p', (w', d\<^sub>2), q) \<in> \<lbrakk>ts0\<rbrakk>\<^sup>\<odot> \<and> (p, w) \<Midarrow>d\<^sub>1\<Rightarrow>\<^sup>* (p', w')"
proof (cases "is_Init q")
  case True
  then show ?thesis
  using assms augmented_rules_2_a[of p w d "the_Ctr_Loc q" "[]"] monoid_rtrancl_refl[of q "\<lbrakk>ts0\<rbrakk>"]
  apply (simp add: one_prod_def one_list_def)
  apply (rule exI[of _ 1])
  apply (rule exI[of _ d], simp)
  apply (rule exI[of _ "the_Ctr_Loc q"])
  apply (rule exI[of _ "[]"])
  apply (rule exI[of _ "q"])
  by simp
next
  case False
  then have q_noninit:"is_Noninit q" using state.exhaust_disc by fast
  obtain d1 p' w' d' p'' w'' d'' where 
      "d = d1 * d' * d'' \<and>
       ((Init p, w), d1, Init p', w') \<in> (WPDS.transition_rel \<Delta>\<^sub>t\<^sub>s\<^sub>0)\<^sup>\<odot> \<and>
       ((Init p', w'), d', Noninit p'', w'') \<in> WPDS.transition_rel \<Delta>\<^sub>t\<^sub>s\<^sub>0 \<and>
       ((Noninit p'', w''), d'', q, []) \<in> (WPDS.transition_rel \<Delta>\<^sub>t\<^sub>s\<^sub>0)\<^sup>\<odot>"
    using augmented_rules_2_init_noninit_split[OF assms(1) _ q_noninit, simplified] by fast
  then show ?thesis 
    using augmented_rules_2_split[of p w d1 p' w' d' p'' w'' d'' q] assms(2,3) by fastforce
qed

lemma exists_d_monoid_wts:
  assumes "w = [] \<longrightarrow> p = q"
  shows "\<exists>d. (p, (w, d), q) \<in> \<lbrakk>ts0\<rbrakk>\<^sup>\<odot>"
proof (cases "w = []")
  case True
  then show ?thesis using assms True
    using monoid_rtrancl_refl[of q "\<lbrakk>ts0\<rbrakk>", unfolded one_prod_def one_list_def]
    by blast
next
  case False
  then show ?thesis
  proof (induct w)
    case Nil
    then show ?case by simp
  next
    case (Cons \<gamma> w')
    then show ?case
    proof (cases "w' = []")
      case True
      then show ?thesis
        using monoid_rtrancl_refl[of q "\<lbrakk>ts0\<rbrakk>", unfolded one_prod_def one_list_def]
              monoid_rtrancl_into_rtrancl_rev[of p "([\<gamma>], ts0 $ (p, \<gamma>, q))" q "\<lbrakk>ts0\<rbrakk>" "([],1)" q]
        unfolding wts_to_monoidLTS_def
        using exI[of _ "ts0 $ (p, \<gamma>, q)"]
        by simp
    next
      case False
      then show ?thesis using Cons(1)[OF False]
        using monoid_rtrancl_into_rtrancl_rev[of p "([\<gamma>], ts0 $ (p, \<gamma>, p))" p "\<lbrakk>ts0\<rbrakk>" "(w',_)" q]
        unfolding wts_to_monoidLTS_def
        by auto
    qed
  qed
qed

lemma wpds_on_empty_stack:
  assumes "((p, []), 0, q, []) \<in> (WPDS.transition_rel \<Delta>\<^sub>t\<^sub>s\<^sub>0)\<^sup>\<odot>"
  shows "p = q"
  using assms
  by (cases rule: monoid_rtrancl_cases_rev[OF assms])
     (auto simp add: WPDS.transition_rel.simps[where \<Delta>=\<Delta>\<^sub>t\<^sub>s\<^sub>0])

lemma augmented_rules_2_d0:
  assumes "((Init p, w), 0, q, []) \<in> (WPDS.transition_rel \<Delta>\<^sub>t\<^sub>s\<^sub>0)\<^sup>\<odot>"
  assumes "q \<in> finals"
  shows "\<exists>d\<^sub>2 d\<^sub>1 p' w' q. q \<in> finals \<and> (Init p', (w', d\<^sub>2), q) \<in> \<lbrakk>ts0\<rbrakk>\<^sup>\<odot> \<and> (p, w) \<Midarrow>d\<^sub>1\<Rightarrow>\<^sup>* (p', w')"
  using exists_d_monoid_wts[of w "Init p" q] assms wpds_on_empty_stack 
  by (cases "w = [] \<longrightarrow> Init p = q") blast+

lemma augmented_rules_equal:
  "\<^bold>\<Sum> {d | d p'. p' \<in> finals \<and> ((Init p, w), d, p', []) \<in> (WPDS.transition_rel \<Delta>\<^sub>t\<^sub>s\<^sub>0)\<^sup>\<odot>} =
   \<^bold>\<Sum> {d' * d | d d' p' w' q. q \<in> finals \<and> (Init p', (w', d), q) \<in> \<lbrakk>ts0\<rbrakk>\<^sup>\<odot> \<and> (p, w) \<Midarrow> d' \<Rightarrow>\<^sup>* (p', w')}" (is "\<^bold>\<Sum>?X = \<^bold>\<Sum>?Y")
proof - 
  have "countable {(x, y). ((Init p, w), x, y, []) \<in> (WPDS.transition_rel \<Delta>\<^sub>t\<^sub>s\<^sub>0)\<^sup>\<odot>}"
    using countable_subset[OF _ countable_f_on_set[OF countable_monoid_augmented, of "\<lambda>((_,_), x, y, _). (x, y)", simplified], 
                           of "{(x, y). ((Init p, w), x, y, []) \<in> (WPDS.transition_rel \<Delta>\<^sub>t\<^sub>s\<^sub>0)\<^sup>\<odot>}"]
    by fast
  then have cX:"countable ?X"
    using countable_f_on_P_Q_set2[of "\<lambda>d p'. ((Init p, w), d, p', []) \<in> (WPDS.transition_rel \<Delta>\<^sub>t\<^sub>s\<^sub>0)\<^sup>\<odot>" "\<lambda>d p'. d" "\<lambda>d p'. p' \<in> finals"]
    by blast
  obtain f::"('ctr_loc, 'noninit) state \<times> ('label list \<times> 'weight) \<times> ('ctr_loc, 'noninit) state \<Rightarrow> nat" 
    where f_inj:"inj_on f (\<lbrakk>ts0\<rbrakk>\<^sup>\<odot>)"
    using countableE[OF countable_monoid_rtrancl[OF countable_wts[of ts0]]] by fastforce
  then have f_inj':"\<And>x y z x' y' z'. (x, y, z) \<in> \<lbrakk>ts0\<rbrakk>\<^sup>\<odot> \<Longrightarrow> (x', y', z') \<in> \<lbrakk>ts0\<rbrakk>\<^sup>\<odot> \<Longrightarrow> f (x, y, z) = f (x', y', z') \<Longrightarrow> (x, y, z) = (x', y', z')"
    unfolding inj_on_def by blast
  have "countable {(x, y, z). (Init x, y, z) \<in> \<lbrakk>ts0\<rbrakk>\<^sup>\<odot>}"
    apply(rule countableI'[of "\<lambda>(x,y,z). f (Init x, y, z)"])
    unfolding inj_on_def
    using f_inj' by fast
  then have y1:"countable {(d,p',w'). \<exists>q. q \<in> finals \<and> (Init p', (w', d), q) \<in> \<lbrakk>ts0\<rbrakk>\<^sup>\<odot>}"
    using countable_f_on_P_Q_set3[of "\<lambda>p' w'd q. (Init p', w'd, q) \<in> \<lbrakk>ts0\<rbrakk>\<^sup>\<odot>" "\<lambda>p' w'd q. (p', w'd)" "\<lambda>p' w'd q. q \<in> finals"]
          countable_3_to_3_permutation
    by (fastforce simp add: dissect_set)
  have y2:"countable {(d',p',w'). (p, w) \<Midarrow> d' \<Rightarrow>\<^sup>* (p', w')}"
    using countable_monoid_rtrancl[OF countable_transition_rel] 
    unfolding l_step_relp_def monoid_rtrancl_def
    using countable_3_to_2[of "(\<lambda>x xa xb. (x, xa, xb) \<in> transition_rel)\<^sup>\<odot>\<^sup>\<odot>" "(p,w)"]
    by fastforce
  have cY:"countable ?Y"
    using countable_subset[OF _ countable_setcompr[OF countable_prod3[OF y1 y2], of "\<lambda>(d,d'). d'*d"], of ?Y]
    by fastforce
  have imp1:"\<And>y. \<exists>d\<^sub>2 d\<^sub>1. y = d\<^sub>1 * d\<^sub>2 \<and> (\<exists>p' w' q. q \<in> finals \<and> (Init p', (w', d\<^sub>2), q) \<in> \<lbrakk>ts0\<rbrakk>\<^sup>\<odot> \<and> (p, w) \<Midarrow> d\<^sub>1 \<Rightarrow>\<^sup>* (p', w')) \<Longrightarrow>
          \<exists>x. (\<exists>q. q \<in> finals \<and> ((Init p, w), x, q, []) \<in> (WPDS.transition_rel \<Delta>\<^sub>t\<^sub>s\<^sub>0)\<^sup>\<odot>) \<and> x \<le> y"
    using augmented_rules_1 by fast
  have imp2:"\<And>y. \<exists>q. q \<in> finals \<and> ((Init p, w), y, q, []) \<in> (WPDS.transition_rel \<Delta>\<^sub>t\<^sub>s\<^sub>0)\<^sup>\<odot> \<Longrightarrow>
          \<exists>x. (\<exists>d\<^sub>2 d\<^sub>1. x = d\<^sub>1 * d\<^sub>2 \<and> (\<exists>p' w' q. q \<in> finals \<and> (Init p', (w', d\<^sub>2), q) \<in> \<lbrakk>ts0\<rbrakk>\<^sup>\<odot> \<and> (p, w) \<Midarrow> d\<^sub>1 \<Rightarrow>\<^sup>* (p', w'))) \<and> x \<le> y"
    using augmented_rules_2 augmented_rules_2_d0 by fastforce
  then show ?thesis
    using SumInf_bounded_by_SumInf_if_members_bounded[OF cX cY] imp1
          SumInf_bounded_by_SumInf_if_members_bounded[OF cY cX] imp2
    by force
qed

lemma augmented_rules_match_W_automaton:
  "\<^bold>\<Sum>{d. augmented_rules_reach_empty finals p w d} = \<^bold>\<Sum>{d. reach_conf_in_W_automaton finals p w d}"
  using augmented_rules_equal reach_conf_in_W_automaton_unfold unfolding augmented_rules_reach_empty_def accepts_def
  by (simp add: monoidLTS.monoid_star_is_monoid_rtrancl) meson

context fixes finals :: "('ctr_loc, 'noninit) state set" begin
abbreviation accepts''' ("\<L> _" [1000] 1000) where "accepts''' \<equiv> accepts' finals"

lemma unfold_pre_star_accepts_empty_automaton:
  "dioidLTS.weight_pre_star augmented_WPDS.transition_rel \<L>(K$ 0) (Init p, w) =
   \<^bold>\<Sum>{d. augmented_rules_reach_empty finals p w d}"
proof -
  have "countable {d. (monoidLTS.l_step_relp (WPDS.transition_rel \<Delta>\<^sub>t\<^sub>s\<^sub>0))\<^sup>\<odot>\<^sup>\<odot> (Init p, w) (fst d) (snd d)}"
    using countable_monoidLTS.countable_monoid_star_variant1[OF monoidLTS_instance, of "(Init p, w)"]
    by (metis (no_types, lifting) Collect_cong case_prod_beta)
  moreover have "\<And>(q::('ctr_loc, 'noninit) state) (b::'label list) d::'weight. q \<notin> finals \<or> b \<noteq> [] \<Longrightarrow> d * \<L>(K$ 0) (q,b) = 0" 
    by fastforce
  ultimately have 
     "\<^bold>\<Sum> {a * \<L>(K$ 0) (aa, b) |a aa b.
          (monoidLTS.l_step_relp (WPDS.transition_rel \<Delta>\<^sub>t\<^sub>s\<^sub>0))\<^sup>\<odot>\<^sup>\<odot> (Init p, w) a (aa, b)} =
      \<^bold>\<Sum> {d' |d' a b. a \<in> finals \<and> b = [] \<and> (monoidLTS.l_step_relp (WPDS.transition_rel \<Delta>\<^sub>t\<^sub>s\<^sub>0))\<^sup>\<odot>\<^sup>\<odot> (Init p, w) d' (a,b)}"
    using SumInf_split_Qor0[of "\<lambda>t. (monoidLTS.l_step_relp (WPDS.transition_rel \<Delta>\<^sub>t\<^sub>s\<^sub>0))\<^sup>\<odot>\<^sup>\<odot> (Init p, w) (fst t) (snd t)"
                               "\<lambda>t. (fst (snd t)) \<in> finals \<and> (snd (snd t)) = []"
                               "\<lambda>t. fst t * \<L>(K$ 0) (snd t)"
                               "\<lambda>t. fst t"]
    by (safe, simp, meson)
  then show ?thesis 
    unfolding dioidLTS.weight_pre_star_def augmented_rules_reach_empty_def monoidLTS.monoid_star_def
    by simp metis
qed

abbreviation language_ts0 :: "('ctr_loc,'label) conf \<Rightarrow> 'weight" where
  "language_ts0 \<equiv> (\<lambda>(p,w). \<L>(ts0) (Init p, w))"

lemma augmented_rules_correct:
  "dioidLTS.weight_pre_star augmented_WPDS.transition_rel \<L>(K$ 0) (Init p, w) = weight_pre_star language_ts0 (p, w)"
  using unfold_pre_star_accepts_empty_automaton augmented_rules_match_W_automaton[of finals p w]
  unfolding weight_pre_star_def reach_conf_in_W_automaton_def by simp meson

lemma pre_star_correctness:
  assumes "saturation augmented_WPDS.pre_star_rule (K$ 0) A"
  shows "\<L>(A) (Init p, w) = weight_pre_star language_ts0 (p, w)"
  using assms augmented_rules_correct augmented_WPDS.correctness' by auto 

abbreviation "pre_star_rule\<^sub>t\<^sub>s\<^sub>0 \<equiv> WPDS.pre_star_rule \<Delta>\<^sub>t\<^sub>s\<^sub>0"
lemma pre_star_correctness':
  assumes "saturation pre_star_rule\<^sub>t\<^sub>s\<^sub>0 (K$ 0) A"
  shows "\<L>(A) (Init p, w) = weight_pre_star language_ts0 (p, w)"
  using assms augmented_rules_correct augmented_WPDS.correctness' \<Delta>\<^sub>t\<^sub>s\<^sub>0_def by auto 

subsection \<open>Code generation 2\<close>

lemma pre_star_exec'_saturation: "saturation augmented_WPDS.pre_star_rule (K$ 0) pre_star_exec'"
  unfolding pre_star_exec'_def2 using augmented_WPDS.saturation_pre_star_exec0 by simp

lemma pre_star_exec_correctness: 
  "\<L>(pre_star_exec') (Init p, w) = weight_pre_star language_ts0 (p,w)"
  using pre_star_correctness pre_star_exec'_saturation by blast
end
end

context
  fixes \<Delta> :: "('ctr_loc::finite, 'label::finite, 'weight::bounded_dioid) w_rule set"
begin
definition pre_star_saturation :: "(('ctr_loc, 'noninit::finite) state, 'label, 'weight) w_transitions \<Rightarrow> (('ctr_loc, 'noninit) state, 'label, 'weight) w_transitions \<Rightarrow> bool" where
  "pre_star_saturation ts0 ts0\<^sub>s\<^sub>a\<^sub>t = saturation (WPDS_with_W_automata.pre_star_rule\<^sub>t\<^sub>s\<^sub>0 \<Delta> ts0) (K$ 0) ts0\<^sub>s\<^sub>a\<^sub>t"

end



section \<open>Weight reach code\<close>

lemma weight_reach_saturation_exec_correct:
  assumes "finite ts"
  shows "saturation (finite_dioidLTS.weight_reach_rule ts) S (weight_reach_exec ts S)"
  using finite_dioidLTS.saturation_weight_reach_exec[unfolded finite_dioidLTS_def finite_monoidLTS_def, OF assms] 
  by simp

definition finfun_sum :: "('a \<Rightarrow>f 'b::bounded_dioid) \<Rightarrow> 'a set \<Rightarrow> 'b" where
  "finfun_sum f finals = \<Sum>{f$s |s. s \<in> finals}"

definition "weight_reach_sum_exec ts inits finals = finfun_sum (weight_reach_exec ts (update_wts (K$ 0) {(p,1) |p. p \<in> inits})) finals"

lemma update_wts_inits_apply:
  fixes inits :: "'state::finite set"
  shows "(update_wts (K$ 0) {(p, 1) |p. p \<in> inits}) $ c = (if c \<in> inits then 1 else 0)"
proof -
  have f:"finite {(p, 1) |p. p \<in> inits}" by simp
  show ?thesis
    using update_wts_sum[OF f, of "K$ 0" c] by fastforce
qed

lemma sum_finals_1_0:
  fixes S :: "('state::finite \<Rightarrow>f 'weight::bounded_dioid)"
  shows "\<Sum> {S $ s * (if s \<in> finals then 1 else 0) |s. True} = \<Sum> {S $ s |s. s \<in> finals}"
  using sum_if_1_0_right_is_sum[of "\<lambda>c. True" "\<lambda>s. S $ s" "\<lambda>s. s \<in> finals"] by simp

lemma weight_reach_saturation_correct:
  assumes "finite ts"
  assumes "saturation (finite_dioidLTS.weight_reach_rule ts) (update_wts (K$ 0) {(p,1) |p. p \<in> inits}) S"
  shows "dioidLTS.weight_reach ts (\<lambda>p. if p \<in> inits then 1 else 0) (\<lambda>p. if p \<in> finals then 1 else 0) = finfun_sum S finals"
  using finite_dioidLTS.weight_reach_saturation_sum_correct'[unfolded finite_dioidLTS_def finite_monoidLTS_def, OF assms, of "\<lambda>p. if p \<in> finals then 1 else 0"]
  unfolding update_wts_inits_apply finfun_sum_def sum_finals_1_0 
  by blast

lemma weight_reach_sum_exec_correct:
  fixes ts :: "('state::finite \<times> 'weight::bounded_dioid \<times> 'state) set"
  assumes "finite ts"
  shows "weight_reach_sum_exec ts inits finals = dioidLTS.weight_reach ts (\<lambda>p. if p \<in> inits then 1 else 0) (\<lambda>p. if p \<in> finals then 1 else 0)"
  unfolding weight_reach_sum_exec_def
  using weight_reach_saturation_correct[OF assms 
          finite_dioidLTS.saturation_weight_reach_exec[unfolded finite_dioidLTS_def finite_monoidLTS_def, OF assms, of "update_wts (K$ 0) {(p, 1) |p. p \<in> inits}"]
        ]
  by force

definition accepts_full :: "(('ctr_loc::finite, 'noninit::finite) state, 'label, 'weight::bounded_dioid) w_transitions \<Rightarrow> ('ctr_loc, 'noninit) state set \<Rightarrow> ('ctr_loc, 'label) conf \<Rightarrow> 'weight" where
  "accepts_full ts finals \<equiv> \<lambda>(p, w). dioidLTS.accepts ts finals (Init p, w)"

lemma finite_wts_to_weightLTS:
  fixes ts :: "('state::finite, 'label::finite, 'weight::bounded_dioid) w_transitions"
  shows "finite \<lbrakk>ts\<rbrakk>\<^sub>w"
proof -
  have "finite ((\<lambda>(p, \<gamma>, q). (p, ts $ (p, \<gamma>, q), q)) ` UNIV)"
    using finite_imageI by auto
  then have "finite {uu. \<exists>p \<gamma> q. uu = (p, ts $ (p, \<gamma>, q), q)}"
    unfolding image_def by (rule rev_finite_subset) auto
  then show ?thesis
    unfolding wts_to_weightLTS_def
    by auto
qed

lemma finite_w_inters:
  fixes ts :: "(('ctr_loc::finite, 'noninit::finite) state, 'label::finite, 'weight::bounded_dioid) w_transitions"
  fixes ts':: "(('ctr_loc, 'noninit) state, 'label, 'weight) w_transitions"
  shows "finite \<lbrakk>ts\<inter>\<^sub>wts'\<rbrakk>\<^sub>w"
  using finite_wts_to_weightLTS by auto

lemma countable_monoid_rtrancl_w_inters:
  fixes ts :: "(('ctr_loc::finite, 'noninit::finite) state, 'label::finite, 'weight::bounded_dioid) w_transitions"
  fixes ts':: "(('ctr_loc, 'noninit) state, 'label, 'weight) w_transitions"
  shows "countable {t|t. t \<in> \<lbrakk>ts\<inter>\<^sub>wts'\<rbrakk>\<^sub>w\<^sup>\<odot>}"
  using countable_monoidLTS.countable_monoid_star[unfolded countable_monoidLTS_def, OF countable_finite[OF finite_w_inters[of ts ts']]]
  unfolding monoidLTS.monoid_star_is_monoid_rtrancl by simp

lemma weight_reach_intersection_correct:    
  fixes ts :: "(('ctr_loc::finite, 'noninit::finite) state, 'label::finite, 'weight::bounded_dioid) w_transitions"
  assumes "binary_aut ts"
  shows "dioidLTS.weight_reach \<lbrakk>ts\<inter>\<^sub>wts'\<rbrakk>\<^sub>w (\<lambda>p. if p \<in> {(q,q)|q. q\<in>inits} then 1 else 0) (\<lambda>p. if p \<in> finals \<times> finals' then 1 else 0) =  
         \<^bold>\<Sum> {dioidLTS.accepts ts finals (p, w) * dioidLTS.accepts ts' finals' (p, w) |p w. p \<in> inits}" (is "?A = ?B")
proof -
  have c1: "countable {y:: ('ctr_loc, 'noninit) state \<times> 'label list. fst y \<in> inits}" 
    by auto
  have c2:"\<And>y:: ('ctr_loc, 'noninit) state \<times> 'label list. fst y \<in> inits \<Longrightarrow> countable {(x, y) |x. snd x \<in> finals' \<and> (fst y, (snd y, fst x), snd x) \<in> \<lbrakk>ts'\<rbrakk>\<^sup>\<odot>}" 
  proof -
    fix y :: "('ctr_loc, 'noninit) state \<times> 'label list"
    have "countable (\<lbrakk>ts'\<rbrakk>\<^sup>\<odot>)"
      by (simp add: countable_monoid_rtrancl countable_wts)
    then have "countable {(y1, (y2, x1), x2) |x1 x2 y1 y2. (y1, (y2, x1), x2) \<in> \<lbrakk>ts'\<rbrakk>\<^sup>\<odot>}"
      by (rule rev_countable_subset) auto
    then have "countable ((\<lambda>(y1, (y2, x1), x2). ((x1,x2), (y1,y2))) ` {(y1, (y2, x1), x2) |x1 x2 y1 y2. (y1, (y2, x1), x2) \<in> \<lbrakk>ts'\<rbrakk>\<^sup>\<odot>})"
      using countable_image by fastforce
    then  show "countable {(x, y) |x. snd x \<in> finals' \<and> (fst y, (snd y, fst x), snd x) \<in> \<lbrakk>ts'\<rbrakk>\<^sup>\<odot>}"
      by (rule rev_countable_subset) (auto simp add: image_def)
  qed
  have c3: "countable {y . fst (snd y) \<in> finals' \<and> (fst (snd (snd y)), (snd (snd (snd y)), fst y), fst (snd y)) \<in> \<lbrakk>ts'\<rbrakk>\<^sup>\<odot> \<and> fst (snd (snd y)) \<in> inits}" 
  proof -
    have "countable (\<lbrakk>ts'\<rbrakk>\<^sup>\<odot>)"
      by (simp add: countable_monoid_rtrancl countable_wts)
    then have "countable {(y31, (y32, y1), y2) | y1 y2 y31 y32 . (y31, (y32, y1), y2) \<in> \<lbrakk>ts'\<rbrakk>\<^sup>\<odot>}"
      by (rule rev_countable_subset) auto
    then have "countable ((\<lambda>(y31, (y32, y1), y2). (y1, y2, (y31,y32))) ` {(y31, (y32, y1), y2) | y1 y2 y31 y32 . (y31, (y32, y1), y2) \<in> \<lbrakk>ts'\<rbrakk>\<^sup>\<odot>})"
      using countable_image by fastforce
    then show "countable {y . fst (snd y) \<in> finals' \<and> (fst (snd (snd y)), (snd (snd (snd y)), fst y), fst (snd y)) \<in> \<lbrakk>ts'\<rbrakk>\<^sup>\<odot> \<and> fst (snd (snd y)) \<in> inits}" 
       by (rule rev_countable_subset) (auto simp add: image_def)
  qed
  have c4:"\<And>y. fst (snd y) \<in> finals' \<and> (fst (snd (snd y)), (snd (snd (snd y)), fst y), fst (snd y)) \<in> \<lbrakk>ts'\<rbrakk>\<^sup>\<odot> \<and> fst (snd (snd y)) \<in> inits \<Longrightarrow>
               countable {(x, y) |x. snd x \<in> finals \<and> (fst (snd (snd y)), (snd (snd (snd y)), fst x), snd x) \<in> \<lbrakk>ts\<rbrakk>\<^sup>\<odot>}" 
  proof -
    fix y :: "'weight \<times> ('ctr_loc, 'noninit) state \<times> ('ctr_loc, 'noninit) state \<times> 'label list"
    have "countable (\<lbrakk>ts\<rbrakk>\<^sup>\<odot>)"
      by (simp add: countable_monoid_rtrancl countable_wts)
    then have "countable {(z1, (z2, x1), x2) |z1 z2 x1 x2. (z1, (z2, x1), x2) \<in> \<lbrakk>ts\<rbrakk>\<^sup>\<odot>}"
      by (rule rev_countable_subset) auto
    then have "countable ((\<lambda>(z1, (z2, x1), x2). ((x1, x2), y)) ` {(z1, (z2, x1), x2) |z1 z2 x1 x2. (z1, (z2, x1), x2) \<in> \<lbrakk>ts\<rbrakk>\<^sup>\<odot>})"
      using countable_image by auto
    then show "countable {(x, y) |x. snd x \<in> finals \<and> (fst (snd (snd y)), (snd (snd (snd y)), fst x), snd x) \<in> \<lbrakk>ts\<rbrakk>\<^sup>\<odot>}"
      by (rule rev_countable_subset) (auto simp add: image_def)
  qed

  have "?A = \<^bold>\<Sum> {d |c d c'. (c, d, c') \<in> \<lbrakk>ts\<inter>\<^sub>wts'\<rbrakk>\<^sub>w\<^sup>\<odot> \<and> c \<in> {(p,p)|p. p\<in>inits} \<and> c' \<in> finals \<times> finals'}"
    unfolding dioidLTS.weight_reach_def monoid_rtranclp_unfold
    using SumInf_if_1_0_both_is_sum[OF countable_monoid_rtrancl_w_inters[of ts ts'], of "\<lambda>clc'. fst clc' \<in> {(p,p)|p. p\<in>inits}" "\<lambda>clc'. fst (snd clc')" "\<lambda>clc'. snd (snd clc') \<in> finals \<times> finals'"]
    by simp
  moreover have "... =  \<^bold>\<Sum>{d * d' |d q d' q' p w. q \<in> finals \<and> (p,(w,d),q) \<in> \<lbrakk>ts\<rbrakk>\<^sup>\<odot> \<and> q' \<in> finals' \<and> (p,(w,d'),q') \<in> \<lbrakk>ts'\<rbrakk>\<^sup>\<odot> \<and> p \<in> inits}"
    apply (rule arg_cong[of _ _ "\<^bold>\<Sum>"])
    using w_inters_sound_wts_to_monoidLTS[OF assms(1)] w_inters_complete_wts_to_weightLTS[OF assms(1)]
    by blast
  moreover have B:"... = ?B"
    unfolding dioidLTS.accepts_def
    using SumInf_of_SumInf_left_distr[OF c1 c2, of "\<lambda>pw. \<^bold>\<Sum>{d | d q. q \<in> finals \<and> (fst pw,(snd pw,d),q) \<in> \<lbrakk>ts\<rbrakk>\<^sup>\<odot>}" "\<lambda>dq pw. fst dq"]
    using SumInf_of_SumInf_right_distr[OF c3 c4, of "\<lambda>dq pw. fst dq" "\<lambda>d'q'pw. fst d'q'pw"]
    by simp
  ultimately show ?thesis by argo
qed

context WPDS begin
interpretation dioidLTS transition_rel .

lemma WPDS_weight_reach'_is_weight_reach_sum_exec:
  fixes ts :: "(('ctr_loc::finite, 'noninit::finite) state, 'label::finite, 'weight::bounded_dioid) w_transitions"
  assumes "binary_aut ts"
      and "finite \<Delta> \<and> (\<forall>q p \<gamma>. is_Init q \<longrightarrow> ts' $ (p, \<gamma>, q) = 0)"
      and "\<And>p. is_Init p \<longleftrightarrow> p \<in> inits"
  shows "weight_reach (accepts_full ts finals) (accepts_full ts' finals') = 
         weight_reach_sum_exec \<lbrakk>ts \<inter>\<^sub>w (WPDS_with_W_automata_no_assms.pre_star_exec' \<Delta> ts')\<rbrakk>\<^sub>w {(p, p) |p. p \<in> inits} (finals \<times> finals')" (is "?A = ?B")
proof -
  have f:"finite \<Delta>" using assms(2) by simp
  have W:"WPDS_with_W_automata \<Delta> ts'" unfolding WPDS_with_W_automata_def finite_WPDS_def WPDS_with_W_automata_axioms_def using assms(2) by blast
  have aux:"\<And>p w. Init p \<in> inits \<Longrightarrow>
    dioidLTS.accepts ts finals (Init p, w) * dioidLTS.weight_pre_star (WPDS.transition_rel \<Delta>) (accepts_full ts' finals') (p, w) =
    dioidLTS.accepts ts finals (Init p, w) * dioidLTS.weight_pre_star (WPDS.transition_rel \<Delta>) (\<lambda>(p, w). dioidLTS.accepts ts' finals' (Init p, w)) (p, w)"
    unfolding accepts_full_def
    by (smt (verit, best) Collect_cong assms(3) dioidLTS.weight_pre_star_def split_cong state.disc(1))
  have "?A = \<^bold>\<Sum>{dioidLTS.accepts ts finals (Init p, w) * dioidLTS.weight_pre_star (WPDS.transition_rel \<Delta>) (accepts_full ts' finals') (p, w) |p w. Init p \<in> inits}" 
    unfolding countable_dioidLTS.weight_reach_to_pre_star[
                unfolded countable_dioidLTS_def countable_monoidLTS_def, 
                OF finite_WPDS.countable_transition_rel[unfolded finite_WPDS_def, OF f],
                of "accepts_full ts finals" "accepts_full ts' finals'"
              ]
    using SumInf_split_Qor0[
            of "\<lambda>c. True" "\<lambda>pw. Init (fst pw) \<in> inits" 
               "\<lambda>c. accepts_full ts finals c * dioidLTS.weight_pre_star (WPDS.transition_rel \<Delta>) (accepts_full ts' finals') c"
               "\<lambda>pw. dioidLTS.accepts ts finals (Init (fst pw), snd pw) * dioidLTS.weight_pre_star (WPDS.transition_rel \<Delta>) (accepts_full ts' finals') pw"
          ]
    unfolding accepts_full_def[of ts]
    using assms(3) by fastforce
  moreover have "... = \<^bold>\<Sum>{dioidLTS.accepts ts finals (Init p, w) * dioidLTS.weight_pre_star (WPDS.transition_rel \<Delta>) (\<lambda>(p, w). dioidLTS.accepts ts' finals' (Init p, w)) (p, w) |p w. Init p \<in> inits}"
    apply (rule arg_cong[of _ _ "\<^bold>\<Sum>"])
    using aux
    apply safe
     apply blast
    by metis
  moreover have "... = \<^bold>\<Sum> {dioidLTS.accepts ts finals (p, w) * dioidLTS.accepts (WPDS_with_W_automata_no_assms.pre_star_exec' \<Delta> ts') finals' (p, w) |p w. p \<in> inits}" 
    apply (rule arg_cong[of _ _ "\<^bold>\<Sum>"])
    apply safe
     apply simp
    subgoal for p w
      using WPDS_with_W_automata.pre_star_exec_correctness[OF W]
      by metis
    apply simp
    subgoal for p w
      apply (rule exI[of _ "the_Ctr_Loc p"])
      using WPDS_with_W_automata.pre_star_exec_correctness[OF W, of finals' "the_Ctr_Loc p"]
      apply (simp add: assms(3)[of p])
      by metis
    done
  moreover have "... = dioidLTS.weight_reach \<lbrakk>ts \<inter>\<^sub>w (WPDS_with_W_automata_no_assms.pre_star_exec' \<Delta> ts')\<rbrakk>\<^sub>w
                        (\<lambda>p. if p \<in> {(q, q) |q. q \<in> inits} then 1 else 0) (\<lambda>p. if p \<in> finals \<times> finals' then 1 else 0)"
    using weight_reach_intersection_correct[OF assms(1), of "WPDS_with_W_automata_no_assms.pre_star_exec' \<Delta> ts'" inits finals finals'] by presburger
  moreover have "... = ?B"
    using weight_reach_sum_exec_correct[OF finite_w_inters, of ts "WPDS_with_W_automata_no_assms.pre_star_exec' \<Delta> ts'" "{(p, p) |p. p \<in> inits}" "finals \<times> finals'"] by argo
  ultimately show ?thesis by argo
qed

lemma binary_aut_ts_to_wts:
  fixes ts :: "(('ctr_loc::finite, 'noninit::finite) state, 'label::finite) transition set"
  shows "binary_aut (ts_to_wts ts)"
proof -
  have f1:"finite ts" by simp
  have f2:"finite {(t,1) | t. t \<in> ts}" using finite_f_on_set[OF f1] by fast
  show ?thesis
    unfolding ts_to_wts_def binary_aut_def update_wts_sum[OF f2]
    apply simp
    apply safe
    subgoal for p1 w p2
      by (cases "(p1, w, p2) \<in> ts", simp_all)
    done
qed
end


lemma not_in_trans_star_implies_accepts_0:
  fixes ts :: "('s :: enum, 'label::finite) transition set"
  assumes "finite ts"
  assumes "\<forall>q\<in>finals. (p, w, q) \<notin> LTS.trans_star ts"
  shows "dioidLTS.accepts (ts_to_wts ts) finals (p, w) = (0::'weight::bounded_dioid)"
  using assms(2)
proof (induct w arbitrary: p)
  case Nil
  then show ?case by (simp add: dioidLTS.accepts_empty_iff) (metis LTS.trans_star.trans_star_refl)
next
  case (Cons a w)
  have f:"finite {ts_to_wts ts $ (p, a, q) * dioidLTS.accepts (ts_to_wts ts) finals (q, w) |q. ts_to_wts ts $ (p, a, q) \<noteq> 0}"
    by fastforce
  have A:"{ts_to_wts ts $ (p, a, x) * dioidLTS.accepts (ts_to_wts ts) finals (x, w) |x. ts_to_wts ts $ (p, a, x) \<noteq> 0 \<and> (p, a, x) \<notin> ts} = {}"
    using ts_to_wts_not_member_is_0[OF assms(1)] by blast
  have "\<And>p'. \<forall>q\<in>finals. (p, a # w, q) \<notin> LTS.trans_star ts \<Longrightarrow> (p, a, p') \<in> ts \<Longrightarrow> \<forall>q\<in>finals. (p', w, q) \<notin> LTS.trans_star ts"
    by (meson LTS.trans_star.trans_star_step)
  then have "\<And>p'. (p, a, p') \<in> ts \<Longrightarrow> dioidLTS.accepts (ts_to_wts ts) finals (p', w) = (0::'weight::bounded_dioid)"
    using Cons by blast
  then have "\<And>p'. (p, a, p') \<in> ts \<Longrightarrow> ts_to_wts ts $ (p, a, p') * dioidLTS.accepts (ts_to_wts ts) finals (p', w) = (0::'weight::bounded_dioid)"
    using mult_zero_right by fastforce
  then have B:"{ts_to_wts ts $ (p, a, x) * dioidLTS.accepts (ts_to_wts ts) finals (x, w) |x. ts_to_wts ts $ (p, a, x) \<noteq> 0 \<and> (p, a, x) \<in> ts} \<subseteq> {0::'weight::bounded_dioid}"
    by blast
  show ?case
    apply (simp add: dioidLTS.accepts_code_Cons)
    unfolding sum_split_f_P[OF f, of "\<lambda>q. (p, a, q) \<in> ts"] A
    using B sum_subset_singleton_0_is_0
    by simp
qed

lemma lang_aut_is_accepts_full:
  fixes ts :: "(('ctr_loc::enum, 'noninit::enum) state, 'label::finite) transition set"
  assumes "finite ts"
  shows "accepts_full (ts_to_wts ts) finals pv = (if pv \<in> P_Automaton.lang_aut ts Init finals then 1 else 0)"
  unfolding accepts_full_def P_Automaton.lang_aut_def P_Automaton.accepts_aut_def inits_set_def 
  apply simp
  apply safe
  subgoal for p w q
    using monoid_rtrancl_one_if_trans_star[of "Init p" w q ts, OF _ assms]
          dioidLTS.accepts_1_if_monoid_rtrancl_1[of ts "Init p" w q finals, OF assms]
    by blast
  using not_in_trans_star_implies_accepts_0[OF assms] by blast


context
  fixes \<Delta> :: "('ctr_loc::enum, 'label::finite, 'weight::bounded_dioid) w_rule set"
  assumes finite_rules: "finite \<Delta>"
begin
interpretation finite_WPDS \<Delta> using finite_WPDS_def finite_rules by auto
interpretation countable_dioidLTS transition_rel apply standard using countable_transition_rel .

lemma pre_star_correctness_full: 
  fixes ts :: "(('ctr_loc, 'noninit::enum) state, 'label) transition set"
  fixes ts' :: "(('ctr_loc, 'noninit) state, 'label) transition set"
  assumes "\<And>p \<gamma> q. is_Init q \<Longrightarrow> (p, \<gamma>, q) \<notin> ts'"
  assumes "pre_star_saturation \<Delta> (ts_to_wts ts') ts'\<^sub>s\<^sub>a\<^sub>t"
  assumes "prod_ts = (ts_to_wts ts) \<inter>\<^sub>w ts'\<^sub>s\<^sub>a\<^sub>t"
  assumes "prod_finals = finals\<times>finals'"
  shows "\<^bold>\<Sum>{d |p w d. d = dioidLTS.accepts prod_ts prod_finals ((p,p),w) \<and> is_Init p}
       = weight_reach_set (P_Automaton.lang_aut ts Init finals) (P_Automaton.lang_aut ts' Init finals')" (is "?A = ?B")
proof -
  have c0:"\<And>y. is_Init (fst y) \<Longrightarrow> countable {(x, y) |x. fst (snd x) \<in> finals \<and> snd (snd x) \<in> finals' \<and> ((fst y, fst y), (snd y, fst x), fst (snd x), snd (snd x)) \<in> \<lbrakk>(ts_to_wts ts)\<inter>\<^sub>wts'\<^sub>s\<^sub>a\<^sub>t\<rbrakk>\<^sup>\<odot>}"
  proof -
    fix y :: "('ctr_loc, 'noninit) state \<times> 'label list"
    have "countable (\<lbrakk>(ts_to_wts ts)\<inter>\<^sub>wts'\<^sub>s\<^sub>a\<^sub>t\<rbrakk>\<^sup>\<odot>)"
      by (simp add: countable_monoid_rtrancl countable_wts)
    then have "countable {(z1, (z2, x1), x2) |z1 z2 x1 x2. (z1, (z2, x1), x2) \<in> \<lbrakk>(ts_to_wts ts)\<inter>\<^sub>wts'\<^sub>s\<^sub>a\<^sub>t\<rbrakk>\<^sup>\<odot>}"
      by (rule rev_countable_subset) auto
    then have "countable ((\<lambda>(z1, (z2, x1), x2). ((x1, x2), y)) ` {(z1, (z2, x1), x2) |z1 z2 x1 x2. (z1, (z2, x1), x2) \<in> \<lbrakk>(ts_to_wts ts)\<inter>\<^sub>wts'\<^sub>s\<^sub>a\<^sub>t\<rbrakk>\<^sup>\<odot>})"
      using countable_image by auto
    then have "countable {((w, q, q'), y) |w q q'. q \<in> finals \<and> q' \<in> finals' \<and> ((fst y, fst y), (snd y, w), q, q') \<in> \<lbrakk>(ts_to_wts ts)\<inter>\<^sub>wts'\<^sub>s\<^sub>a\<^sub>t\<rbrakk>\<^sup>\<odot>}"
      apply (rule rev_countable_subset)
      by force
    then show "countable {(x, y) |x. fst (snd x) \<in> finals \<and> snd (snd x) \<in> finals' \<and> ((fst y, fst y), (snd y, fst x), fst (snd x), snd (snd x)) \<in> \<lbrakk>(ts_to_wts ts)\<inter>\<^sub>wts'\<^sub>s\<^sub>a\<^sub>t\<rbrakk>\<^sup>\<odot>}"
      by simp
  qed
  have c1: "countable {y:: 'ctr_loc \<times> 'label list. True}" 
    by auto
  have c2:"\<And>y:: 'ctr_loc \<times> 'label list. True \<Longrightarrow> countable {(x, y) |x. snd x \<in> finals' \<and> (Init (fst y), (snd y, fst x), snd x) \<in> \<lbrakk>ts'\<^sub>s\<^sub>a\<^sub>t\<rbrakk>\<^sup>\<odot>}" 
  proof -
    fix y :: "'ctr_loc \<times> 'label list"
    have "countable (\<lbrakk>ts'\<^sub>s\<^sub>a\<^sub>t\<rbrakk>\<^sup>\<odot>)"
      by (simp add: countable_monoid_rtrancl countable_wts)
    then have "countable {(y1, (y2, x1), x2) |x1 x2 y1 y2. (y1, (y2, x1), x2) \<in> \<lbrakk>ts'\<^sub>s\<^sub>a\<^sub>t\<rbrakk>\<^sup>\<odot>}"
      by (rule rev_countable_subset) auto
    then have "countable ((\<lambda>(y1, (y2, x1), x2). ((x1,x2), y)) ` {(y1, (y2, x1), x2) |x1 x2 y1 y2. (y1, (y2, x1), x2) \<in> \<lbrakk>ts'\<^sub>s\<^sub>a\<^sub>t\<rbrakk>\<^sup>\<odot>})"
      using countable_image by fastforce
    then show "countable {(x, y) |x. snd x \<in> finals' \<and> (Init (fst y), (snd y, fst x), snd x) \<in> \<lbrakk>ts'\<^sub>s\<^sub>a\<^sub>t\<rbrakk>\<^sup>\<odot>}"
      by (rule rev_countable_subset) (auto simp add: image_def)
  qed
  have c3: "countable {y. fst (snd y) \<in> finals' \<and> (Init (fst (snd (snd y))), (snd (snd (snd y)), fst y), fst (snd y)) \<in> \<lbrakk>ts'\<^sub>s\<^sub>a\<^sub>t\<rbrakk>\<^sup>\<odot>}" 
  proof -
    have "countable (\<lbrakk>ts'\<^sub>s\<^sub>a\<^sub>t\<rbrakk>\<^sup>\<odot>)"
      by (simp add: countable_monoid_rtrancl countable_wts)
    then have "countable {(y31, (y32, y1), y2) | y1 y2 y31 y32 . (y31, (y32, y1), y2) \<in> \<lbrakk>ts'\<^sub>s\<^sub>a\<^sub>t\<rbrakk>\<^sup>\<odot>}"
      by (rule rev_countable_subset) auto
    then have a:"countable ((\<lambda>(y31, (y32, y1), y2). (y1, y2, (the_Ctr_Loc y31,y32))) ` {(y31, (y32, y1), y2) | y1 y2 y31 y32 . (y31, (y32, y1), y2) \<in> \<lbrakk>ts'\<^sub>s\<^sub>a\<^sub>t\<rbrakk>\<^sup>\<odot>})"
      using countable_image by fastforce
    then show "countable {y . fst (snd y) \<in> finals' \<and> (Init (fst (snd (snd y))), (snd (snd (snd y)), fst y), fst (snd y)) \<in> \<lbrakk>ts'\<^sub>s\<^sub>a\<^sub>t\<rbrakk>\<^sup>\<odot>}"
      apply (rule rev_countable_subset)
      apply (simp add: image_def)
      by fastforce
  qed
  have c4:"\<And>y. fst (snd y) \<in> finals' \<and> (Init (fst (snd (snd y))), (snd (snd (snd y)), fst y), fst (snd y)) \<in> \<lbrakk>ts'\<^sub>s\<^sub>a\<^sub>t\<rbrakk>\<^sup>\<odot> \<Longrightarrow>
               countable {(x, y) |x. snd x \<in> finals \<and> (Init (fst (snd (snd y))), (snd (snd (snd y)), fst x), snd x) \<in> \<lbrakk>ts_to_wts ts\<rbrakk>\<^sup>\<odot>}" 
  proof -
    fix y :: "'weight \<times> ('ctr_loc, 'noninit) state \<times> 'ctr_loc \<times> 'label list"
    have "countable (\<lbrakk>ts_to_wts ts\<rbrakk>\<^sup>\<odot>)"
      by (simp add: countable_monoid_rtrancl countable_wts)
    then have "countable {(z1, (z2, x1), x2) |z1 z2 x1 x2. (z1, (z2, x1), x2) \<in> \<lbrakk>ts_to_wts ts\<rbrakk>\<^sup>\<odot>}"
      by (rule rev_countable_subset) auto
    then have "countable ((\<lambda>(z1, (z2, x1), x2). ((x1, x2), y)) ` {(z1, (z2, x1), x2) |z1 z2 x1 x2. (z1, (z2, x1), x2) \<in> \<lbrakk>ts_to_wts ts\<rbrakk>\<^sup>\<odot>})"
      using countable_image by auto
    then show "countable {(x, y) |x. snd x \<in> finals \<and> (Init (fst (snd (snd y))), (snd (snd (snd y)), fst x), snd x) \<in> \<lbrakk>ts_to_wts ts\<rbrakk>\<^sup>\<odot>}"
      by (rule rev_countable_subset) (auto simp add: image_def)
  qed

  from assms(1) have assms1':"\<And>q p \<gamma>. is_Init q \<Longrightarrow> ((ts_to_wts ts')::(('ctr_loc, 'noninit) state, 'label, 'weight) w_transitions) $ (p, \<gamma>, q) = 0"
    by (simp add: ts_to_wts_not_member_is_0)
  have W:"WPDS_with_W_automata \<Delta> (ts_to_wts ts')" by standard (simp add: assms1')
  have prestar:"weight_pre_star (accepts_full (ts_to_wts ts') finals') = accepts_full ts'\<^sub>s\<^sub>a\<^sub>t finals'"
    using WPDS_with_W_automata.pre_star_correctness[OF W assms(2)[unfolded pre_star_saturation_def], of finals']
    unfolding accepts_full_def by simp
  have "?A = \<^bold>\<Sum>{accepts' (finals \<times> finals') (ts_to_wts ts)\<inter>\<^sub>wts'\<^sub>s\<^sub>a\<^sub>t ((p, p), w) |p w. is_Init p}" 
    unfolding assms(3,4) by presburger
  moreover have "... = \<^bold>\<Sum>{d |p w d q q'. ((p, p), (w, d), q, q') \<in> \<lbrakk>(ts_to_wts ts)\<inter>\<^sub>wts'\<^sub>s\<^sub>a\<^sub>t\<rbrakk>\<^sup>\<odot> \<and> q \<in> finals \<and> q' \<in> finals' \<and> is_Init p}"
    unfolding accepts_def
    apply simp
    unfolding SumInf_of_SumInf[of "\<lambda>pw. is_Init (fst pw)"
                              "\<lambda>dq pw. fst (snd dq) \<in> finals \<and> snd (snd dq) \<in> finals' \<and> ((fst pw, fst pw), (snd pw, fst dq), fst (snd dq), snd (snd dq)) \<in> \<lbrakk>(ts_to_wts ts)\<inter>\<^sub>wts'\<^sub>s\<^sub>a\<^sub>t\<rbrakk>\<^sup>\<odot>"
                              "\<lambda>dq pw. fst dq", OF _ c0, simplified]
    apply (rule arg_cong[of _ _ "\<^bold>\<Sum>"])
    by blast
  moreover have "... = \<^bold>\<Sum>{d |p w d q q'. ((Init p, Init p), (w, d), q, q') \<in> \<lbrakk>(ts_to_wts ts)\<inter>\<^sub>wts'\<^sub>s\<^sub>a\<^sub>t\<rbrakk>\<^sup>\<odot> \<and> q \<in> finals \<and> q' \<in> finals'}"
    apply (rule arg_cong[of _ _ "\<^bold>\<Sum>"])
    apply safe
     apply simp
    subgoal for p w d q q'
      apply (rule exI[of _ "the_Ctr_Loc p"])
      by auto
    apply simp
    subgoal for p w d q q'
      apply (rule exI[of _ "Init p"])
      by auto
    done
  moreover have "... = \<^bold>\<Sum> {d * d'| p d q d' q' w. q \<in> finals \<and> (Init p, (w, d), q) \<in> \<lbrakk>ts_to_wts ts\<rbrakk>\<^sup>\<odot> \<and> q' \<in> finals' \<and> (Init p, (w, d'), q') \<in> \<lbrakk>ts'\<^sub>s\<^sub>a\<^sub>t\<rbrakk>\<^sup>\<odot>}"
    apply (rule arg_cong[of _ _ "\<^bold>\<Sum>"])
    using w_inters_sound_and_complete[OF binary_aut_ts_to_wts[of ts], of _ _ _ _ _ _ ts'\<^sub>s\<^sub>a\<^sub>t]
    by fastforce
  moreover have "... = weight_reach (accepts_full (ts_to_wts ts) finals) (accepts_full (ts_to_wts ts') finals')"
    unfolding weight_reach_to_pre_star prestar
    unfolding accepts_def accepts_full_def
    using SumInf_of_SumInf_left_distr[OF c1 c2, of "\<lambda>pw. \<^bold>\<Sum>{d | d q. q \<in> finals \<and> (Init (fst pw),(snd pw,d),q) \<in> \<lbrakk>ts_to_wts ts\<rbrakk>\<^sup>\<odot>}" "\<lambda>dq pw. fst dq"]
    using SumInf_of_SumInf_right_distr[OF c3 c4, of "\<lambda>dq pw. (fst dq)" "\<lambda>d'q'pw. fst d'q'pw"]
    by simp meson
  moreover have "... = ?B"
    unfolding lang_aut_is_accepts_full[unfolded finite_code, simplified] lang_aut_is_accepts_full[unfolded finite_code, simplified]
    using weight_reach_set_is_weight_reach by simp
  ultimately show ?thesis by order
qed
end

end
