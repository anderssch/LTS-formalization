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

end