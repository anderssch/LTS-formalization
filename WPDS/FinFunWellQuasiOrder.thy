theory FinFunWellQuasiOrder 
  imports "FinFun.FinFun" ReverseWellQuasiOrder 
begin

unbundle finfun_syntax

\<comment> \<open>We show that FinFun from a finite set to a WellQuasiOrder (wqo) set is WellQuasiOrdered, with the forall-relation.
   In other words that @{typ "('a::finite, 'b::wqo) finfun"} is instance of @{class wqo}\<close>

\<comment> \<open>First define the order, and prove that it is a partial @{class order} (and @{class preorder})\<close>
instantiation finfun :: (type, preorder) preorder 
begin
  definition less_eq_finfun_def: "f \<le> g = (\<forall>a. f $ a \<le> g $ a)"
  definition less_finfun_def: "(f::'a \<Rightarrow>f 'b::preorder) < g = (f \<le> g \<and> \<not> g \<le> f)"
  instance proof fix x y z :: "'a \<Rightarrow>f 'b::preorder"
    show "(x < y) = strict (\<le>) x y" unfolding less_eq_finfun_def less_finfun_def using dual_order.strict_iff_not by blast
    show "x \<le> x" unfolding less_eq_finfun_def by simp
    show "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z" unfolding less_eq_finfun_def using order_trans by blast
  qed
end
instantiation finfun :: (type, order) order
begin
  instance proof fix x y z :: "'a \<Rightarrow>f 'b::order"
    show "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y" unfolding less_eq_finfun_def by (simp add: finfun_ext order_class.order_eq_iff)
  qed
end

\<comment> \<open>The proof of wqo goes by induction on the (finite) input domain, 
   so we need to define the set of \<open>finfuns\<close> over given input and output domains.\<close>

inductive_set finfuns :: "'a set \<Rightarrow> 'b set  \<Rightarrow> ('a \<Rightarrow>f 'b) set"
  for A :: "'a set" and B :: "'b set"
where
    Default [simp]: "b \<in> B \<Longrightarrow> (K$ b) \<in> finfuns A B"
  | Assign [simp]: "\<lbrakk>a \<in> A; b \<in> B; f \<in> finfuns A B\<rbrakk> \<Longrightarrow> f(a $:= b) \<in> finfuns A B"

\<comment> \<open>Forall-embedding of a relation \<open>P\<close> onto \<open>finfuns\<close>\<close>
definition finfun_emb where
  "finfun_emb P f g \<equiv> (\<forall>a. P (f $ a) (g $ a))"

\<comment> \<open>The recursive definition covers all possible finfuns.\<close>
lemma finfuns_UNIV: "finfuns UNIV UNIV = UNIV"
  apply (safe, simp_all)
  subgoal for f
    by (induct f rule:finfun_weak_induct, simp_all)
  done

\<comment> \<open>Some auxiliary lemmas\<close>
lemma finfuns_apply_domain: "f \<in> (finfuns A B) \<Longrightarrow> f $ a \<in> B"
  by (erule finfuns.induct, simp) (metis finfun_upd_apply_other finfun_upd_apply_same)
lemma seq_finfuns_apply_domain: "\<forall>i. seq i \<in> (finfuns A B) \<Longrightarrow> (seq i $ a) \<in> B"
  by (meson finfuns_apply_domain)
lemma finfuns_empty_exist_all: 
  "\<lbrakk>f \<in> (finfuns {} B); g \<in> (finfuns {} B); \<exists>a. P (f $ a) (g $ a)\<rbrakk> \<Longrightarrow> \<forall>a. P (f $ a) (g $ a)"
  unfolding finfun_emb_def
  by (cases rule: finfuns.cases, simp, safe, simp)+
lemma seq_finfuns_empty_exist_all: 
  "\<lbrakk>\<forall>i. seq i \<in> finfuns {} B; \<exists>a i j. i < j \<and> (P (seq i $ a) (seq j $ a))\<rbrakk> \<Longrightarrow> \<exists>i j. i < j \<and> (\<forall>a. P (seq i $ a) (seq j $ a))"
  using finfuns_empty_exist_all by metis
lemma finfuns_insert_sub: "finfuns A B \<subseteq> finfuns (insert a A) B"
  by safe (erule finfuns.induct, auto)
lemma finfuns_insert_assign: "\<lbrakk>b \<in> B; f \<in> finfuns A B\<rbrakk> \<Longrightarrow> f(a $:= b) \<in> finfuns (insert a A) B"
  apply (erule finfuns.induct, simp)
  using finfuns_insert_sub[of A B a] by auto

\<comment> \<open>Base case of the induction for the almost-full property\<close>
lemma finfuns_empty_almost_full: 
  assumes "almost_full_on P B"
  shows   "almost_full_on (finfun_emb P) (finfuns {} B)"
  using assms unfolding almost_full_on_def good_def finfun_emb_def
  apply safe
  subgoal for seq
  apply (frule seq_finfuns_empty_exist_all[of seq B P])
  proof 
    fix a
    show "\<lbrakk>\<forall>f\<in>SEQ B. \<exists>i j. i < j \<and> P (f i) (f j); \<forall>i. seq i \<in> finfuns {} B\<rbrakk> \<Longrightarrow> \<exists>i j. i < j \<and> P (seq i $ a) (seq j $ a)"
    using seq_finfuns_apply_domain[of seq "{}" B _ a]
    by auto
  qed
  done

\<comment> \<open>In the step of the induction, we use Dickson's lemma for almost-full relations @{thm almost_full_on_Sigma}
    and a homomorphism from a pair of finfuns to a finfun with larger input domain @{term "insert a A"} using @{thm almost_full_on_hom}.\<close>
definition finfun_step_prod_hom :: "'a \<Rightarrow> ('a \<Rightarrow>f 'b \<times> 'a \<Rightarrow>f 'b) \<Rightarrow> ('a \<Rightarrow>f 'b)" where
  "finfun_step_prod_hom a fg = (snd fg)(a $:= (fst fg)$a)"

lemma finfun_step_hom_prod_le: 
  assumes "x \<in> finfuns {a} B \<times> finfuns A B"
      and "y \<in> finfuns {a} B \<times> finfuns A B"
      and "prod_le (finfun_emb P) (finfun_emb P) x y"
    shows "finfun_emb P (finfun_step_prod_hom a x) (finfun_step_prod_hom a y)"
  using assms
  unfolding finfun_step_prod_hom_def prod_le_def finfun_emb_def
  by (auto simp add: finfun_upd_apply)  

lemma finfun_step_prod_hom_image: "finfun_step_prod_hom a ` (finfuns {a} B \<times> finfuns A B) = finfuns (insert a A) B"
  unfolding finfun_step_prod_hom_def image_def
  apply safe
   apply simp
   apply (cases rule: finfuns.cases, simp_all)
     apply (auto simp add: finfuns_insert_assign)[3]
  subgoal for f
    apply (induct f rule: finfuns.induct, simp_all)
    subgoal for b
      by (metis finfun_upd_triv finfuns.Default)
    subgoal for aa b f
      apply (cases "aa=a", simp_all)
      by (metis finfun_const_apply finfun_update_twice finfuns.Default)
         (metis finfun_update_twist finfuns_insert_assign insert_absorb)
    done
  done

lemma finfuns_insert_prod_almost_full: 
  assumes "almost_full_on (prod_le (finfun_emb P) (finfun_emb P)) (finfuns {a} B \<times> finfuns A B)"
    shows "almost_full_on (finfun_emb P) (finfuns (insert a A) B)"
  using finfun_step_prod_hom_image finfun_step_hom_prod_le assms(1)
        almost_full_on_hom[of "finfuns {a} B \<times> finfuns A B" "prod_le (finfun_emb P) (finfun_emb P)" 
                              "finfun_emb P" "finfun_step_prod_hom a"]
  by metis

\<comment> \<open>For the step, we also need to show that @{term finfuns} over a singleton input set preserves almost-full.
    For any given singleton set, such finfuns are homomorphic to pairs of values (one constant and one for the single distinct input).
    Again we use @{thm almost_full_on_Sigma} and @{thm almost_full_on_hom}\<close>
definition finfun_single_prod_hom :: "'a \<Rightarrow> ('b \<times> 'b) \<Rightarrow> ('a \<Rightarrow>f 'b)" where
  "finfun_single_prod_hom a bb = (K$ fst bb)(a $:= (snd bb))"

lemma finfun_single_hom_prod_le: 
  assumes "x \<in> B \<times> B"
      and "y \<in> B \<times> B"
      and "prod_le P P x y"
    shows "finfun_emb P (finfun_single_prod_hom a x) (finfun_single_prod_hom a y)"
  using assms
  unfolding finfun_single_prod_hom_def prod_le_def finfun_emb_def
  by (auto simp add: finfun_upd_apply)

lemma finfun_single_prod_hom_image: "finfun_single_prod_hom a ` (B \<times> B) = finfuns {a} B"
  unfolding finfun_single_prod_hom_def image_def
  apply safe
   apply simp
  apply (erule finfuns.induct, simp_all)
  by (metis finfun_update_const_same) force

lemma finfuns_single_prod_almost_full: 
  assumes "almost_full_on (prod_le P P) (B \<times> B)"
    shows "almost_full_on (finfun_emb P) (finfuns {a} B)"
  using finfun_single_prod_hom_image finfun_single_hom_prod_le assms(1)
        almost_full_on_hom[of "B \<times> B" "prod_le P P" "finfun_emb P" "finfun_single_prod_hom a"]
  by metis

lemma finfuns_single_almost_full: 
  assumes "almost_full_on P B"
  shows "almost_full_on (finfun_emb P) (finfuns {a} B)"
  using assms finfuns_single_prod_almost_full[OF almost_full_on_Sigma[OF assms(1) assms(1)]] by fast

\<comment> \<open>Use the lemmas for singleton input and @{term "insert a A"} input to prove the induction step.\<close>
lemma finfuns_insert_almost_full:
  assumes "almost_full_on P B"
      and "almost_full_on (finfun_emb P) (finfuns A B)"
    shows "almost_full_on (finfun_emb P) (finfuns (insert a A) B)"
  using finfuns_single_almost_full[of P B a]
        finfuns_insert_prod_almost_full[of P a B]
        almost_full_on_Sigma[of "finfun_emb P" "finfuns {a} B" "finfun_emb P" "finfuns A B"]
        assms 
  by simp

\<comment> \<open>Finfuns of a finite domain preserve the almost-full property (all infinite sequences contain a non-decreasing pair).
    This is the main result in this section, and goes by induction on the finite input domain A.\<close>
lemma finite_finfuns_almost_full:
  assumes "finite A"
      and "almost_full_on P B"
    shows "almost_full_on (finfun_emb P) (finfuns A B)"  
  using assms
proof (induction rule: finite.induct)
  case emptyI
  then show ?case using finfuns_empty_almost_full by fast
next
  case (insertI A a)
  then show ?case using finfuns_insert_almost_full by fast
qed

\<comment> \<open>Transitivity of the @{term finfun_emb} on @{term finfuns}.\<close>
lemma finfuns_transp_on:
  assumes "transp_on P B"
    shows "transp_on (finfun_emb P) (finfuns A B)"
  using assms unfolding finfun_emb_def transp_on_def
  by (meson finfuns_apply_domain)

\<comment> \<open>Combining almost-full and transitivity, we get well-quasi-order.\<close>
lemma finite_finfuns_wqo:
  assumes "finite A"
      and "wqo_on P B"
    shows "wqo_on (finfun_emb P) (finfuns A B)"
  using assms finfuns_transp_on finite_finfuns_almost_full
  unfolding wqo_on_def by blast

\<comment> \<open>Finally make the class instantiation.\<close>
instantiation finfun :: (finite, wqo) wqo
begin
  instance proof fix f :: "(nat \<Rightarrow> ('a::finite \<Rightarrow>f 'b::wqo))"
    have f:"finite (UNIV::('a set))" by simp
    have w:"wqo_on (\<le>) (UNIV::('b::wqo set))" using wqo_on_class .
    have "wqo_on (\<le>) (UNIV::(('a \<Rightarrow>f 'b) set))"
      using finite_finfuns_wqo[OF f w] finfuns_UNIV 
      unfolding finfun_emb_def less_eq_finfun_def by metis
    then show "good (\<le>) f" unfolding wqo_on_def almost_full_on_def less_eq_finfun_def by simp
  qed
end

\<comment> \<open>Finally make the class instantiation.\<close>
instantiation finfun :: (finite, reverse_wqo) reverse_wqo
begin
  instance proof fix f :: "(nat \<Rightarrow> ('a::finite \<Rightarrow>f 'b::reverse_wqo))"
    have f:"finite (UNIV::('a set))" by simp
    have w:"wqo_on (\<ge>) (UNIV::('b::reverse_wqo set))" using reverse_wqo_on_class .
    have "wqo_on (\<ge>) (UNIV::(('a \<Rightarrow>f 'b) set))"
      using finite_finfuns_wqo[OF f w] finfuns_UNIV 
      unfolding finfun_emb_def less_eq_finfun_def by metis
    then show "good (\<ge>) f" unfolding wqo_on_def almost_full_on_def less_eq_finfun_def by simp
  qed
end

\<comment> \<open>Extra lemmas\<close>
lemma finfun_update_less:
  assumes "f $ a < f' $ a"
  assumes "f(a $:= d) = f'"
  shows "f < f'"
  using assms unfolding less_finfun_def less_eq_finfun_def
  apply (simp, safe)
  subgoal for a'
    apply (cases "a = a'")
    using order_less_imp_le by (blast, simp)
  using dual_order.strict_iff_not by blast

lemma less_eq_finfun_elem: 
  fixes x :: "'a \<Rightarrow>f 'weight::preorder"
  assumes "x \<le> y"
  shows "x $ c \<le> y $ c"
  using assms unfolding less_eq_finfun_def by simp

lemma less_eq_finfun_not_zero: 
  fixes x :: "'a \<Rightarrow>f 'weight::bounded_semilattice_sup_bot"
  assumes "x \<le> y"
  assumes "x $ c \<noteq> bot"
  shows "y $ c \<noteq> bot"
  using less_eq_finfun_elem[OF assms(1)] assms(2) bot.extremum_unique
  by metis                                                      

end