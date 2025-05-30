theory MonoidLTS
  imports "Labeled_Transition_Systems.LTS" "MonoidClosure" "CountableSum"
begin


section \<open>Locale: monoidLTS\<close>
\<comment> \<open>If the @{typ 'weight} of a LTS is a monoid, we can express the monoid product of labels over a path.\<close>

locale monoidLTS = LTS transition_relation 
  for transition_relation :: "('state::countable, 'weight::monoid_mult) transition set"
begin

definition l_step_relp  :: "'state \<Rightarrow> 'weight \<Rightarrow> 'state \<Rightarrow> bool" ("(_)/ \<Midarrow> (_)/ \<Rightarrow> (_)/" [70,70,80] 80) where
  "c \<Midarrow>l\<Rightarrow> c' \<longleftrightarrow> (c, l, c') \<in> transition_relation"

abbreviation monoid_star_relp :: "'state \<Rightarrow> 'weight \<Rightarrow> 'state \<Rightarrow> bool" ("(_)/ \<Midarrow> (_)/ \<Rightarrow>\<^sup>* (_)/" [90,90,100] 100) where
  "c \<Midarrow>l\<Rightarrow>\<^sup>* c' \<equiv> l_step_relp\<^sup>\<odot>\<^sup>\<odot> c l c'"

definition monoid_star :: "('state \<times> 'weight \<times> 'state) set" where
  "monoid_star = {(c,l,c'). c \<Midarrow>l\<Rightarrow>\<^sup>* c'}"

lemma monoid_star_is_monoid_rtrancl[simp]: "monoid_star = transition_relation\<^sup>\<odot>"
  unfolding monoid_star_def l_step_relp_def monoid_rtrancl_def by simp

lemma star_to_closure: "c \<Midarrow>l\<Rightarrow>\<^sup>* c' \<Longrightarrow> (c, l, c') \<in> transition_relation\<^sup>\<odot>"
  unfolding l_step_relp_def monoid_rtrancl_def by simp

end

lemma monoid_rtranclp_unfold: "(monoidLTS.l_step_relp ts)\<^sup>\<odot>\<^sup>\<odot> c l c' \<longleftrightarrow> (c, l, c') \<in> ts\<^sup>\<odot>"
  unfolding monoidLTS.l_step_relp_def monoid_rtranclp_monoid_rtrancl_eq by simp


section \<open>Locale: countable_monoidLTS\<close>

locale countable_monoidLTS = monoidLTS +
  assumes ts_countable: "countable transition_relation"
begin

lemma countable_monoid_star: "countable monoid_star"
  using countable_monoid_rtrancl[OF ts_countable] by simp

lemma countable_monoid_star_variant1: "countable {(l, c'). c \<Midarrow> l \<Rightarrow>\<^sup>* c'}"
  using countable_f_on_P_Q_set3[of "\<lambda>c l c'. c \<Midarrow> l \<Rightarrow>\<^sup>* c'" "\<lambda>c l c'. (l, c')" "\<lambda>x y z. x = c"]
    countable_monoid_star monoid_star_def by auto

lemma countable_monoid_star_variant2: "countable {(c, l). c \<Midarrow> l \<Rightarrow>\<^sup>* c'}"
  using countable_f_on_P_Q_set3[of "\<lambda>c l c'. c \<Midarrow> l \<Rightarrow>\<^sup>* c'" "\<lambda>c l c'. (c, l)" "\<lambda>x y z. z = c'"]
    countable_monoid_star monoid_star_def by auto

lemma countable_monoid_star_variant3: "countable {l. c \<Midarrow> l \<Rightarrow>\<^sup>* c'}"
  using countable_f_on_P_Q_set3[of "\<lambda>c l c'. c \<Midarrow> l \<Rightarrow>\<^sup>* c'" "\<lambda>c l c'. l" "\<lambda>x y z. x = c \<and> z = c'"]
    countable_monoid_star monoid_star_def by auto

lemmas countable_monoid_star_all =
  countable_monoid_star
  countable_monoid_star[unfolded monoid_star_def]
  countable_monoid_star_variant1
  countable_monoid_star_variant2
  countable_monoid_star_variant3

lemma countable_star_f_p: "countable {f c l c' | c l c'. c \<Midarrow>l\<Rightarrow>\<^sup>* c' \<and> P c c'}"
  by (auto simp add: dissect_set countable_monoid_star_all)

lemma countable_star_f_p3: "countable {f l c' | l c'. c \<Midarrow>l\<Rightarrow>\<^sup>* c'}"
  by (auto simp add: dissect_set countable_monoid_star_all)

lemma countable_star_f_c_l: "countable {f c l | c l. c \<Midarrow>l\<Rightarrow>\<^sup>* c'}"
  using countable_star_f_p[of "\<lambda>c l c'. f c l" "\<lambda>a b. b = c'"] by presburger

lemma countable_star_f_p6:
  "countable {f c1 d1' c2 c3 d2' c4 |c1 d1' c2 c3 d2' c4. c1 \<Midarrow> d1' \<Rightarrow>\<^sup>* c2 \<and> c3 \<Midarrow> d2' \<Rightarrow>\<^sup>* c4}"
proof -
  have subset: "{((c1, d1', c2),(c3, d2', c4)) |c1 d1' c2 c3 d2' c4. c1 \<Midarrow> d1' \<Rightarrow>\<^sup>* c2 \<and> c3 \<Midarrow> d2' \<Rightarrow>\<^sup>* c4} \<subseteq> monoid_star \<times> monoid_star"
    unfolding monoid_star_def by blast
  then have "countable {((c1, d1', c2),(c3, d2', c4)) |c1 d1' c2 c3 d2' c4. c1 \<Midarrow> d1' \<Rightarrow>\<^sup>* c2 \<and> c3 \<Midarrow> d2' \<Rightarrow>\<^sup>* c4}"
    using countable_SIGMA countable_monoid_star  countable_subset by fastforce
  then have "countable ((\<lambda>((c1, d1', c2),(c3, d2', c4)). f c1 d1' c2 c3 d2' c4) ` {((c1, d1', c2),(c3, d2', c4)) |c1 d1' c2 c3 d2' c4. c1 \<Midarrow> d1' \<Rightarrow>\<^sup>* c2 \<and> c3 \<Midarrow> d2' \<Rightarrow>\<^sup>* c4})"
    using countable_image by force
  then show ?thesis
    using Collect_cong[of "\<lambda>y. \<exists>c1 d1' c2. (c1 \<Midarrow> d1' \<Rightarrow>\<^sup>* c2) \<and> (\<exists>c3 d2' c4. ( c3  \<Midarrow> d2' \<Rightarrow>\<^sup>* c4) \<and> y = f c1 d1' c2 c3 d2' c4)"
        "\<lambda>fd1'd2'. \<exists>c1 d1' c2 c3 d2' c4. fd1'd2' = f c1 d1' c2 c3 d2' c4 \<and> c1 \<Midarrow> d1' \<Rightarrow>\<^sup>* c2 \<and> (c3 \<Midarrow> d2' \<Rightarrow>\<^sup>* c4)"]
    unfolding image_def by fastforce
qed

lemma countable_star_f_p9: "countable {f l | l. c \<Midarrow>l\<Rightarrow>\<^sup>* c'}"
  by (auto simp add: dissect_set countable_monoid_star_all)

lemma countable_l_c_c': "countable {l |c l c'. c \<Midarrow>l\<Rightarrow>\<^sup>* c'}"
  using countable_star_f_p[of "\<lambda>c l c'. l" "\<lambda>c c'. True"] by presburger

lemma countable_l_c: "countable {l |c l. c \<Midarrow>l\<Rightarrow>\<^sup>* c'}"
  using countable_star_f_p[of "\<lambda>c l c'. l" "\<lambda>a b. b = c'"] by presburger

lemma countable_l_c': "countable {l |l c'. c \<Midarrow>l\<Rightarrow>\<^sup>* c'}"
  using countable_star_f_p[of "\<lambda>c l c'. l" "\<lambda>a b. a = c"] by presburger

lemma countable_l: "countable {l |l. c \<Midarrow>l\<Rightarrow>\<^sup>* c'}"
  using countable_star_f_p[of "\<lambda>c l c'. l" "\<lambda>a b. a = c \<and> b = c'"] by presburger

lemma countable_star_tuple: "countable {(c, l, c') | c l c'. c \<Midarrow>l\<Rightarrow>\<^sup>* c'}"
  using countable_star_f_p[of "\<lambda>c l c'. (c, l, c')" "\<lambda>c c'. True"] by presburger

end


section \<open>Locale: dioidLTS\<close>
\<comment> \<open>If the @{typ 'weight} of a LTS is a dioid with additive and multiplicative identities, 
    we can express the meet-over-all-paths value as a generalization of pre-star and post-star.\<close>
locale dioidLTS = monoidLTS transition_relation
  for transition_relation :: "('state::countable, 'weight::bounded_dioid) transition set"
begin

definition weight_pre_star :: "('state \<Rightarrow> 'weight) \<Rightarrow> ('state \<Rightarrow> 'weight)" where
  "weight_pre_star C c = \<^bold>\<Sum>{l*(C c') | l c'. c \<Midarrow>l\<Rightarrow>\<^sup>* c'}"
definition weight_post_star :: "('state \<Rightarrow> 'weight) \<Rightarrow> ('state \<Rightarrow> 'weight)" where
  "weight_post_star C c = \<^bold>\<Sum>{(C c')*l | c' l. c' \<Midarrow>l\<Rightarrow>\<^sup>* c}"
definition weight_reach :: "('state \<Rightarrow> 'weight) \<Rightarrow> ('state \<Rightarrow> 'weight) \<Rightarrow> 'weight" where
  "weight_reach C C' = \<^bold>\<Sum>{(C c) * l * (C' c') | c l c'. c \<Midarrow>l\<Rightarrow>\<^sup>* c'}"

definition weight_reach_set :: "('state set) \<Rightarrow> ('state set) \<Rightarrow> 'weight" where
  "weight_reach_set C C' = \<^bold>\<Sum>{l | c l c'. c \<Midarrow>l\<Rightarrow>\<^sup>* c' \<and> c \<in> C \<and> c' \<in> C'}"

end


section \<open>Locale: countable_dioidLTS\<close>

locale countable_dioidLTS = dioidLTS + countable_monoidLTS 
begin 

lemma weight_reach_to_pre_star: "weight_reach C C' = \<^bold>\<Sum> {(C c) * weight_pre_star C' c |c. True}"
proof -
  have c:"\<And>y. True \<Longrightarrow> countable {(x, y) |x. y \<Midarrow> fst x \<Rightarrow>\<^sup>* snd x}" using countable_star_f_p3 by fastforce
  have "\<^bold>\<Sum> {C y * (a * C' b) |a b y. y \<Midarrow> a \<Rightarrow>\<^sup>* b} = \<^bold>\<Sum> {C c * l * C' c' |c l c'. c \<Midarrow> l \<Rightarrow>\<^sup>* c'}" 
    by (rule arg_cong[of _ _ "\<^bold>\<Sum>"]) (simp add: ac_simps(4), blast)
  then show ?thesis
    unfolding weight_reach_def weight_pre_star_def
    using SumInf_of_SumInf_left_distr[of "\<lambda>c. True" "\<lambda>lc' c. c \<Midarrow> fst lc' \<Rightarrow>\<^sup>* snd lc'" "\<lambda>c. C c" "\<lambda>lc' c. fst lc' * C' (snd lc')", OF countableI_type c, symmetric]
    by simp
qed

lemma weight_reach_to_post_star: "weight_reach C C' = \<^bold>\<Sum> {weight_post_star C c' * (C' c') |c'. True}"
proof -
  have c:"\<And>y. True \<Longrightarrow> countable {(x, y) |x. fst x \<Midarrow> snd x \<Rightarrow>\<^sup>* y}" using countable_star_f_c_l by fastforce
  have "\<^bold>\<Sum> {C y * (a * C' b) |a b y. y \<Midarrow> a \<Rightarrow>\<^sup>* b} = \<^bold>\<Sum> {C c * l * C' c' |c l c'. c \<Midarrow> l \<Rightarrow>\<^sup>* c'}" 
    by (rule arg_cong[of _ _ "\<^bold>\<Sum>"]) (simp add: ac_simps(4), blast)
  then show ?thesis
    unfolding weight_reach_def weight_post_star_def
    using SumInf_of_SumInf_right_distr[of "\<lambda>c. True" "\<lambda>cl c'. fst cl \<Midarrow> snd cl \<Rightarrow>\<^sup>* c'" "\<lambda>cl c'. C (fst cl) * snd cl" "\<lambda>c'. C' c'", OF countableI_type c]
    by simp
qed

lemma weight_reach_set_is_weight_reach:
 "weight_reach_set C C' = weight_reach (\<lambda>c. if c \<in> C then 1 else 0) (\<lambda>c. if c \<in> C' then 1 else 0)"
  unfolding weight_reach_set_def weight_reach_def
  using SumInf_if_1_0_both_is_sum[of _ "\<lambda>clc'. fst clc' \<in> C" "\<lambda>clc'. fst (snd clc')" "\<lambda>clc'. snd (snd clc') \<in> C'"] countable_star_tuple
  by fastforce

end

end