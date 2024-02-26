theory MonoidLTS
  imports "LTS" "MonoidClosure" "CountableSum"
begin

\<comment> \<open>If the @{typ 'weight} of a LTS is a monoid, we can express the monoid product of labels over a path.\<close>
locale monoidLTS = LTS transition_relation 
  for transition_relation :: "('state::countable, 'weight::monoid_mult) transition set"
begin
definition l_step_relp  :: "'state \<Rightarrow> 'weight \<Rightarrow> 'state \<Rightarrow> bool" ("(_)/ \<Midarrow> (_)/ \<Rightarrow> (_)/" [70,70,80] 80) where
  "c \<Midarrow>l\<Rightarrow> c' \<longleftrightarrow> (c, l, c') \<in> transition_relation"
abbreviation monoid_star_relp :: "'state \<Rightarrow> 'weight \<Rightarrow> 'state \<Rightarrow> bool" ("(_)/ \<Midarrow> (_)/ \<Rightarrow>\<^sup>* (_)/" [90,90,100] 100) where
  "c \<Midarrow>l\<Rightarrow>\<^sup>* c' \<equiv> (monoid_rtranclp l_step_relp) c l c'"
definition monoid_star :: "('state \<times> 'weight \<times> 'state) set" where
  "monoid_star = {(c,l,c'). c \<Midarrow>l\<Rightarrow>\<^sup>* c'}"

lemma monoid_star_is_monoid_rtrancl[simp]: "monoid_star = monoid_rtrancl transition_relation"
  unfolding monoid_star_def l_step_relp_def monoid_rtrancl_def by simp
lemma star_to_closure: "c \<Midarrow>l\<Rightarrow>\<^sup>* c' \<Longrightarrow> (c, l, c') \<in> monoid_rtrancl transition_relation"
  unfolding l_step_relp_def monoid_rtrancl_def by simp

end

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
end

(*
lemma monoidLTS_monoid_star_mono:
  "mono monoidLTS.monoid_star"
  using monoidLTS.monoid_star_is_monoid_rtrancl monoid_rtrancl_is_mono unfolding mono_def
  by simp
*)


\<comment> \<open>If the @{typ 'weight} of a LTS is a dioid with additive and multiplicative identities, 
    we can express the meet-over-all-paths value as a generalization of pre-star and post-star.\<close>
locale dioidLTS = monoidLTS transition_relation
  for transition_relation :: "('state::countable, 'weight::bounded_idempotent_semiring) transition set"
begin

definition weight_pre_star :: "('state \<Rightarrow> 'weight) \<Rightarrow> ('state \<Rightarrow> 'weight)" where
  "weight_pre_star C c = \<^bold>\<Sum>{l*(C c') | l c'. c \<Midarrow>l\<Rightarrow>\<^sup>* c'}"
definition weight_post_star :: "('state \<Rightarrow> 'weight) \<Rightarrow> ('state \<Rightarrow> 'weight)" where
  "weight_post_star C c = \<^bold>\<Sum>{(C c')*l | c' l. c' \<Midarrow>l\<Rightarrow>\<^sup>* c}"
definition weight_reach :: "('state \<Rightarrow> 'weight) \<Rightarrow> ('state \<Rightarrow> 'weight) \<Rightarrow> 'weight" where
  "weight_reach C C' = \<^bold>\<Sum>{(C c) * l * (C' c') | c l c'. c \<Midarrow>l\<Rightarrow>\<^sup>* c'}"

end

locale countable_dioidLTS = dioidLTS + countable_monoidLTS 


end