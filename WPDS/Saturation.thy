theory Saturation 
  imports Main "Well_Quasi_Orders.Well_Quasi_Orders" ReverseWellQuasiOrder 
begin

subsection \<open>Well-quasi-ordered saturation\<close>

type_synonym 't saturation_rule = "'t \<Rightarrow> 't \<Rightarrow> bool"

definition saturated :: "'t saturation_rule \<Rightarrow> 't \<Rightarrow> bool" where
  "saturated rule val \<longleftrightarrow> (\<nexists>val'. rule val val')"

definition saturation :: "'t saturation_rule \<Rightarrow> 't \<Rightarrow> 't \<Rightarrow> bool" where
  "saturation rule val val' \<longleftrightarrow> rule\<^sup>*\<^sup>* val val' \<and> saturated rule val'"


lemma wqo_no_infinite: 
  assumes "wqo_on P UNIV"
  assumes "\<And>f f'. rule f f' \<Longrightarrow> strict P f' f"
  assumes "\<forall>i :: nat. rule (seq i) (seq (Suc i))"
  shows "False"
proof -
  have decreasing:"\<And>i. strict P (seq (Suc i)) (seq i)" using assms by simp
  have trans: "\<And>a b c. strict P a b \<Longrightarrow> strict P b c \<Longrightarrow> strict P a c" using assms(1) unfolding wqo_on_def transp_on_def by blast
  have "\<exists>i j. i < j \<and> P (seq i) (seq j)" using assms(1) unfolding wqo_on_def almost_full_on_def good_def by simp
  moreover have "\<forall>i j. i < j \<longrightarrow> strict P (seq j) (seq i)"
  proof
    fix i
    show "\<forall>j>i. strict P (seq j) (seq i)"
    proof 
      fix j
      have "i < j \<Longrightarrow> strict P (seq j) (seq i)"
      proof (induction "j")
        case 0
        then show ?case by simp
      next
        case (Suc j)
        then have "i\<noteq>j \<Longrightarrow> strict P (seq (Suc j)) (seq i)" using decreasing trans not_less_less_Suc_eq by blast
        then show ?case by (cases "i=j", auto simp add: decreasing)
      qed
      then show "i < j \<longrightarrow> strict P (seq j) (seq i)" by auto
    qed
  qed
  ultimately show ?thesis by auto
qed

lemma wqo_saturation_termination:
  assumes "wqo_on P UNIV"
  assumes "\<And>f f'. rule f f' \<Longrightarrow> strict P f' f"
  shows "\<not>(\<exists>seq. (\<forall>i :: nat. rule (seq i) (seq (Suc i))))"
  using assms wqo_no_infinite by blast 

lemma wqo_saturation_exi:
  assumes "wqo_on P UNIV"
  assumes "\<And>f f'. rule f f' \<Longrightarrow> strict P f' f"
  shows "\<exists>f'. saturation rule f f'"
proof (rule ccontr)
  assume a: "\<nexists>f'. saturation rule f f'"
  define g where "g f = (SOME f'. rule f f')" for f
  define seq where "seq i = (g ^^ i) f" for i
  have "\<forall>i :: nat. rule\<^sup>*\<^sup>* f (seq i) \<and> rule (seq i) (seq (Suc i))"
  proof 
    fix i
    show "rule\<^sup>*\<^sup>* f (seq i) \<and> rule (seq i) (seq (Suc i))"
      proof (induction i)
    case 0
      have "rule f (g f)" by (metis g_def a rtranclp.rtrancl_refl saturation_def saturated_def someI)
      then show ?case using seq_def a by auto
    next
      case (Suc i)
      then have sat_Suc: "rule\<^sup>*\<^sup>* f (seq (Suc i))" by fastforce
      then have "rule (g ((g ^^ i) f)) (g (g ((g ^^ i) f)))"
        by (metis Suc.IH seq_def g_def a r_into_rtranclp rtranclp_trans saturation_def saturated_def someI)
      then have "rule (seq (Suc i)) (seq (Suc (Suc i)))" unfolding seq_def by simp
      then show ?case using sat_Suc by auto
    qed
  qed
  then have "\<forall>i. rule (seq i) (seq (Suc i))" by auto
  then show False using wqo_no_infinite assms by auto
qed


lemma wqo_class_no_infinite: 
  assumes "\<And>f f' ::('t::wqo). rule f f' \<Longrightarrow> f' < f"
  assumes "\<forall>i :: nat. rule (seq i) (seq (Suc i))"
  shows "False"
using assms wqo_no_infinite[of "(\<le>)"] wqo_on_class less_le_not_le by metis

lemma wqo_class_saturation_termination:
  assumes "\<And>f f' ::('t::wqo). rule f f' \<Longrightarrow> f' < f"
  shows "\<not>(\<exists>seq. (\<forall>i :: nat. rule (seq i) (seq (Suc i))))"
  using assms wqo_class_no_infinite by blast 

lemma wqo_class_saturation_exi:
  assumes "\<And>f f' ::('t::wqo). rule f f' \<Longrightarrow> f' < f"
  shows "\<exists>f'. saturation rule f f'"
using assms wqo_saturation_exi[of "(\<le>)"] wqo_on_class less_le_not_le by metis

lemma reverse_wqo_class_no_infinite: 
  assumes "\<And>f f' ::('t::reverse_wqo). rule f f' \<Longrightarrow> f < f'"
  assumes "\<forall>i :: nat. rule (seq i) (seq (Suc i))"
  shows "False"
  using assms wqo_no_infinite[of "(\<ge>)"] reverse_wqo_on_class less_le_not_le by metis

lemma reverse_wqo_class_saturation_termination:
  assumes "\<And>f f' ::('t::reverse_wqo). rule f f' \<Longrightarrow> f < f'"
  shows "\<not>(\<exists>seq. (\<forall>i :: nat. rule (seq i) (seq (Suc i))))"
  using assms reverse_wqo_class_no_infinite by blast 

lemma reverse_wqo_class_saturation_exi:
  assumes "\<And>f f' ::('t::reverse_wqo). rule f f' \<Longrightarrow> f < f'"
  shows "\<exists>f'. saturation rule f f'"
using assms wqo_saturation_exi[of "(\<ge>)"] reverse_wqo_on_class less_le_not_le by metis


subsection \<open>Set saturation\<close>

lemma finite_card_le_wqo:
  assumes "finite A"
  shows "wqo_on (\<lambda>x y. card x \<ge> card y) A"
proof -
  have "reflp_on (\<lambda>x y. card x \<ge> card y) A" unfolding reflp_on_def by blast
  moreover have "transp_on (\<lambda>x y. card x \<ge> card y) A" unfolding transp_on_def by simp
  ultimately show ?thesis using finite_wqo_on[of "A" "(\<lambda>x y. card x \<ge> card y)"] using assms by simp
qed

lemma no_infinite: 
  assumes "\<And>ts ts' :: 'a::finite set. rule ts ts' \<Longrightarrow> card ts' = Suc (card ts)"
  assumes "\<forall>i :: nat. rule (tts i) (tts (Suc i))"
  shows "False"
using assms wqo_no_infinite[of "\<lambda>x y. card x \<ge> card y" "rule" "tts"] finite_card_le_wqo
  by (metis (mono_tags, lifting) finite_class.finite_UNIV nle_le not_less_eq_eq)

lemma saturation_termination:
  assumes "\<And>ts ts' :: 'a::finite set. rule ts ts' \<Longrightarrow> card ts' = Suc (card ts)"
  shows "\<not>(\<exists>tts. (\<forall>i :: nat. rule (tts i) (tts (Suc i))))"
  using assms no_infinite by blast 

lemma saturation_exi: 
  assumes "\<And>ts ts' :: 'a::finite set. rule ts ts' \<Longrightarrow> card ts' = Suc (card ts)"
  shows "\<exists>ts'. saturation rule ts ts'"
  using assms wqo_saturation_exi[of "\<lambda>x y. card x \<ge> card y" "rule" "ts"] finite_card_le_wqo
  by (metis (mono_tags, lifting) finite_class.finite_UNIV nle_le not_less_eq_eq)

end