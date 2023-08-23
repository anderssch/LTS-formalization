theory Set_More imports "HOL-Library.Countable_Set" begin

lemma Collect_conj_eq2: "{(x,y). P x y \<and> Q x y} = {(x,y). P x y} \<inter> {(x,y). Q x y}"
  using Collect_conj_eq[of "\<lambda>xy. P (fst xy) (snd xy)" "\<lambda>xy. Q (fst xy) (snd xy)"] by auto

lemma Collect_conj_eq3: "{(x,y,z). P x y z \<and> Q x y z} = {(x,y,z). P x y z} \<inter> {(x,y,z). Q x y z}"
  using Collect_conj_eq[of "\<lambda>xyz. P (fst xyz) (fst (snd xyz)) (snd (snd xyz))"
      "\<lambda>xyz. Q (fst xyz) (fst (snd xyz)) (snd (snd xyz))"] by auto

lemma setcompr_eq_image2: "{f a b |a b. P a b} = (\<lambda>(a,b). f a b) ` {(a,b). P a b}"
  by auto

lemma setcompr_eq_image3: "{f a b c |a b c. P a b c } = (\<lambda>(a,b,c). f a b c) ` {(a,b,c ). P a b c}"
  by (auto split: prod.split simp add: image_def)

lemma setcompr_eq_image4: "{f a b c d |a b c d. P a b c d } = (\<lambda>(a,b,c,d). f a b c d) ` {(a,b,c,d). P a b c d}"
  by (auto split: prod.split simp add: image_def)

lemma setcompr_eq_image5: "{f a b c d e |a b c d e. P a b c d e } = (\<lambda>(a,b,c,d,e). f a b c d e) ` {(a,b,c,d,e). P a b c d e}"
  by (auto split: prod.split simp add: image_def) blast+
  
lemmas dissect_set = 
  Collect_conj_eq Collect_conj_eq2 Collect_conj_eq3
  setcompr_eq_image setcompr_eq_image2 setcompr_eq_image3

lemma countable_setcompr:
  assumes "countable {x . X x}"
  shows "countable {f x | x. X x}"
  by (simp add: assms dissect_set)

lemma countable_f_on_set: "countable X \<Longrightarrow> countable {f x | x. x \<in> X}"
  by (simp add: dissect_set)

lemma countable_f_on_P_Q_set: "countable {x. Q x} \<Longrightarrow> countable {f x | x. P x \<and> Q x}"
  by (simp add: dissect_set)

lemma countable_f_on_P_Q_set2: "countable {(x, y). Q x y} \<Longrightarrow> countable {f x y | x y. P x y \<and> Q x y}"
  by (simp add: dissect_set)

lemma countable_f_on_P_Q_set3: "countable {(x, y, z). Q x y z} \<Longrightarrow> countable {f x y z | x y z. P x y z \<and> Q x y z}"
  by (simp add: dissect_set)


lemma finite_f_on_set: "finite X \<Longrightarrow> finite {f x | x. x \<in> X}"
  by (simp add: dissect_set)

lemma countable_prod: "countable {x. P x} \<Longrightarrow> countable {y. Q y} \<Longrightarrow> countable {(x,y). P x \<and> Q y}"
  by force

lemma countable_prod2: 
  assumes "countable {(x,z). P x z}"
  assumes "countable {(y,z). Q y z}"
  shows "countable {(x,y)| x y z. P x z \<and> Q y z}"
proof -
  obtain f::"'a \<times> 'b \<Rightarrow> nat" where f_inj:"inj_on f {(x, z). P x z}" using countableE[OF assms(1)] by blast
  obtain g::"'c \<times> 'b \<Rightarrow> nat" where g_inj:"inj_on g {(y, z). Q y z}" using countableE[OF assms(2)] by blast
  from f_inj have f_inj':"\<And>a b a' b'. P a b \<Longrightarrow> P a' b' \<Longrightarrow> f (a, b) = f (a', b') \<Longrightarrow> a = a' \<and> b = b'" unfolding inj_on_def by blast
  from g_inj have g_inj':"\<And>a b a' b'. Q a b \<Longrightarrow> Q a' b' \<Longrightarrow> g (a, b) = g (a', b') \<Longrightarrow> a = a' \<and> b = b'" unfolding inj_on_def by blast
  show ?thesis 
    apply (rule countableI'[of "\<lambda>(x,y). (f (x, (SOME z. P x z \<and> Q y z)), g (y, (SOME z. P x z \<and> Q y z)))"])
    unfolding inj_on_def
    apply simp
    apply safe
    subgoal for a b z a' b' z'
      using someI_ex[of "\<lambda>z. P a z \<and> Q b z", OF exI[of "\<lambda>z. P a z \<and> Q b z" z]]
            someI_ex[of "\<lambda>z. P a' z \<and> Q b' z", OF exI[of "\<lambda>z. P a' z \<and> Q b' z" z']]
      using f_inj'[of a "SOME z. P a z \<and> Q b z" a' "SOME z. P a' z \<and> Q b' z"]
      by simp
    subgoal for a b z a' b' z'
      using someI_ex[of "\<lambda>z. P a z \<and> Q b z", OF exI[of "\<lambda>z. P a z \<and> Q b z" z]]
            someI_ex[of "\<lambda>z. P a' z \<and> Q b' z", OF exI[of "\<lambda>z. P a' z \<and> Q b' z" z']]
      using g_inj'[of b "SOME z. P a z \<and> Q b z" b' "SOME z. P a' z \<and> Q b' z"]
      by simp
    done
qed

lemma countable_prod3: 
  assumes "countable {(x,z,u). P x z u}"
  assumes "countable {(y,z,u). Q y z u}"
  shows "countable {(x,y)| x y z u. P x z u \<and> Q y z u}"
  using countable_prod2 assms by fastforce

lemma countable_3_to_2:
  assumes "countable {(a, b, c). X a b c}"
  shows "countable {(b, c). X a b c}"
  using countable_subset[OF _ countable_setcompr[OF assms, of "\<lambda>(a,b,c). (b,c)", simplified], of "{(b, c). X a b c}"]
  by blast

lemma countable_3_to_3_permutation:
  assumes "countable {(a, b, c). X a b c}"
  shows "countable {(c, a, b). X a b c}"  
  using countable_subset[OF _ countable_setcompr[OF assms, of "\<lambda>(a,b,c). (c,a,b)", simplified], of "{(c, a, b). X a b c}"]
  by blast


end