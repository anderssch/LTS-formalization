theory FinFunWellFounded
  imports "FinFun.FinFun" ProdDioid
begin

unbundle finfun_syntax

\<comment> \<open>We show that FinFun from a finite set to a WellQuasiOrder (wqo) set is WellQuasiOrdered, with the forall-relation.
   In other words that @{typ "('a::finite, 'b::bounded_idempotent_comm_monoid_add) finfun"} 
   is instance of @{class bounded_idempotent_comm_monoid_add}\<close>
\<comment> \<open>Definitions\<close>
instantiation finfun :: (type, one) one begin 
  definition one_finfun_def: "1 = (K$ 1)" instance .. 
end
instantiation finfun :: (type, zero) zero begin 
  definition zero_finfun_def: "0 = (K$ 0)" instance .. 
end

instantiation finfun :: (type, plus) plus begin
  definition add_finfun_def: "a + b \<equiv> (\<lambda>(x,y). x + y) \<circ>$ ($a, b$)"
instance ..
  lemma add_finfun_apply[simp]: "(f + g) $ x = f $ x + g $ x"
    unfolding add_finfun_def by simp
end

instantiation finfun :: (type, ord) ord begin 
  \<comment> \<open>Note: This conjunctive order produces a partial order, even if the elements have a total order\<close>
  definition less_eq_finfun_def: "f \<le> g = (\<forall>a. f $ a \<le> g $ a)"
  definition less_finfun_def: "(f::'a \<Rightarrow>f 'b) < g = (f \<le> g \<and> \<not> g \<le> f)"
  instance ..
end
\<comment> \<open>First define the order, and prove that it is a partial @{class order} (and @{class preorder})\<close>
instantiation finfun :: (type, preorder) preorder 
begin
  instance proof fix x y z :: "'a \<Rightarrow>f 'b::preorder"
    show "(x < y) = strict (\<le>) x y" unfolding less_eq_finfun_def less_finfun_def using dual_order.strict_iff_not by blast
    show "x \<le> x" unfolding less_eq_finfun_def by simp
    show "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z" unfolding less_eq_finfun_def using order_trans by blast
  qed
lemma less_eq_strict:  "((<)::('a \<Rightarrow>f 'b::preorder \<Rightarrow> 'a \<Rightarrow>f 'b::preorder \<Rightarrow> bool)) = (strict (\<le>))"
  unfolding less_finfun_def by simp
end
instantiation finfun :: (type, order) order
begin
  instance proof fix x y z :: "'a \<Rightarrow>f 'b::order"
    show "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y" unfolding less_eq_finfun_def by (simp add: finfun_ext order_class.order_eq_iff)
  qed
end
instantiation finfun :: (type, semigroup_add) semigroup_add begin
  instance proof fix a b c :: "('a \<Rightarrow>f 'b::semigroup_add)"
    show "a + b + c = a + (b + c)" unfolding add_finfun_def
      by (rule finfun_ext) (simp add: add.assoc)
  qed
end
instantiation finfun :: (type, monoid_add) monoid_add begin
  instance proof fix a :: "('a \<Rightarrow>f 'b::monoid_add)"
    show "0 + a = a" unfolding zero_finfun_def add_finfun_def
      by (rule finfun_ext) simp
    show "a + 0 = a" unfolding zero_finfun_def add_finfun_def
      by (rule finfun_ext) simp
  qed
end
instantiation finfun :: (type, ab_semigroup_add) ab_semigroup_add begin
  instance proof fix a b c :: "('a \<Rightarrow>f 'b::ab_semigroup_add)"
    show "a + b = b + a" unfolding add_finfun_def
      by (rule finfun_ext) (simp add: add.commute) 
  qed
end
instantiation finfun :: (type, comm_monoid_add) comm_monoid_add begin
  instance proof fix a :: "('a \<Rightarrow>f 'b::comm_monoid_add)"
    show "0 + a = a" unfolding zero_finfun_def add_finfun_def
      by (rule finfun_ext) simp
  qed
end
instantiation finfun :: (type, idempotent_ab_semigroup_add) idempotent_ab_semigroup_add begin
  instance proof fix a :: "('a \<Rightarrow>f 'b::idempotent_ab_semigroup_add)"
    show "a + a = a" unfolding add_finfun_def 
      by (rule finfun_ext) simp
  qed
end
instantiation finfun :: (type, idempotent_ab_semigroup_add_ord) idempotent_ab_semigroup_add_ord begin
  instance proof fix a b :: "('a \<Rightarrow>f 'b::idempotent_ab_semigroup_add_ord)"
    have "(a \<le> b) = (\<forall>x. (a + b) $ x = a $ x)"
      unfolding less_eq_finfun_def add_finfun_def less_eq_def by simp
    then show "(a \<le> b) = (a + b = a)" using finfun_ext[of "a + b" a] by fastforce
    show "(a < b) = (a \<le> b \<and> a \<noteq> b)" unfolding less_finfun_def by fastforce
  qed
end
instantiation finfun :: (type, idempotent_comm_monoid_add) idempotent_comm_monoid_add begin instance .. end
instantiation finfun :: (type, idempotent_comm_monoid_add_ord) idempotent_comm_monoid_add_ord begin instance .. end

lemma sum_finfun_apply:
  fixes S :: "('a \<Rightarrow>f 'b::idempotent_comm_monoid_add) set"
  assumes "finite S"
  shows "\<Sum> S $ a = \<Sum> {f $ a |f. f\<in>S}"
proof (induct rule: finite_induct[OF assms])
  case 1
  then show ?case by (simp add: zero_finfun_def)
next
  case (2 x F)
  then have f:"finite {f $ a |f. f \<in> F}" by simp
  have "x $ a + \<Sum> {f $ a |f. f \<in> F} = \<Sum> {f $ a |f. f = x \<or> f \<in> F}"
    unfolding idem_sum_insert[OF f, of "x $ a", symmetric]
    by (rule arg_cong[of _ _ "\<Sum>"]) blast
  then show ?case by (simp add: 2(1,3))
qed

lemma sum_finfun_apply_f_P:
  fixes f :: "'c \<Rightarrow> ('a \<Rightarrow>f 'b::idempotent_comm_monoid_add)"
  assumes "finite {f x |x. P x}"
  shows "\<Sum> {f x |x. P x} $ a = \<Sum> {(f x) $ a |x. P x}"
  unfolding sum_finfun_apply[OF assms, of a]
  by (rule arg_cong[of _ _ \<Sum>]) blast


\<comment> \<open>The proof of wqo goes by induction on the (finite) input domain, 
   so we need to define the set of \<open>finfuns\<close> over a given input domain.\<close>
  

inductive_set finfuns :: "'a set \<Rightarrow> ('a \<Rightarrow>f ('b::zero)) set"
  for A :: "'a set"
where
    Zero [simp]: "finite A \<Longrightarrow> (K$ 0) \<in> finfuns A"
  | Default [simp]: "infinite A \<Longrightarrow> (K$ b) \<in> finfuns A"
  | Assign [simp]: "\<lbrakk>a \<in> A; f \<in> finfuns A\<rbrakk> \<Longrightarrow> f(a $:= b) \<in> finfuns A"

\<comment> \<open>Forall-embedding of a relation \<open>P\<close> onto \<open>finfuns\<close>\<close>
definition finfun_emb where
  "finfun_emb P f g \<equiv> (\<forall>a. P (f $ a) (g $ a))"

\<comment> \<open>Some auxiliary lemmas\<close>
lemma finfuns_empty: "finfuns {} = {(K$ 0)}"
  apply safe
  subgoal for f
    by (induct f rule: finfuns.induct, simp_all)
  by simp
lemma finfuns_single: "((finfuns {a})::('a \<Rightarrow>f 'b::zero) set) = {(K$ 0)(a $:= b) | b. True}"
  apply auto
  subgoal for f
    apply (induct f rule: finfuns.induct, simp_all)
    apply (rule exI[of _ 0])
     apply (simp add: finfun_update_const_same)
    by force
  done

lemma finfuns_empty_exist_all: 
  "\<lbrakk>f \<in> (finfuns {}); g \<in> (finfuns {}); \<exists>a. P (f $ a) (g $ a)\<rbrakk> \<Longrightarrow> \<forall>a. P (f $ a) (g $ a)"
  unfolding finfun_emb_def
  by (cases rule: finfuns.cases, simp, safe, simp)+
lemma finfuns_insert_sub: "finfuns A \<subseteq> finfuns (insert a A)"
  by safe (erule finfuns.induct, auto)
lemma finfuns_insert_assign: "\<lbrakk>f \<in> finfuns A\<rbrakk> \<Longrightarrow> f(a $:= b) \<in> finfuns (insert a A)"
  apply (erule finfuns.induct, simp_all)
  using finfuns_insert_sub[of A a] by auto
lemma finite_finfuns_insert_undo:
  assumes "finite A"
      and "f \<in> finfuns (insert a A)"
    shows "f(a $:= 0) \<in> finfuns A"
  using assms(2)
  apply (induct rule: finfuns.induct)
  using assms(1)
    apply (simp_all add: finfun_update_const_same)
  subgoal for a' f b
    apply safe
     apply simp
    by (metis finfun_update_twist finfuns.Assign insert_Diff insert_Diff_single)
  done

\<comment> \<open>The recursive definition covers all possible finfuns.\<close>
lemma finite_fold_const_finfuns: "finite A \<Longrightarrow> Finite_Set.fold (\<lambda>a f. f(a $:= b)) (K$ 0) A \<in> finfuns A"
  apply (induct A rule: finite_induct)
   apply simp
  subgoal for a A
    using finfuns_insert_sub[of A a]
    by auto
  done

lemma const_in_finfuns: 
  assumes "finite (UNIV::('a set))"
  shows "(K$ b) \<in> finfuns (UNIV::('a set))"
  using finite_fold_const_finfuns[of UNIV, OF assms] 
  by (rule subst[OF fold_finfun_update_finite_univ[of b 0, OF assms]])

lemma finfuns_UNIV: "finfuns (UNIV::('a set)) = UNIV"
  apply (safe, simp_all)
  subgoal for f
    apply (cases "finite (UNIV::('a set))")
    by (induct f rule:finfun_weak_induct, simp_all add: const_in_finfuns)+
  done

lemma wfp_on_spec: "wfp_on P A \<Longrightarrow> (\<And>i. f i \<in> A) \<Longrightarrow> \<exists>i. \<not> P (f (Suc i)) (f i)"
  unfolding wfp_on_def by blast
lemma antisymp_on_spec: "antisymp_on A P \<Longrightarrow> (\<And>a b. a \<in> A \<Longrightarrow> b \<in> A \<Longrightarrow> P a b \<Longrightarrow> P b a \<Longrightarrow> a = b)"
  unfolding antisymp_on_def by fastforce
lemma wfp_onI: "(\<And>f::nat \<Rightarrow> 'a. \<forall>i. f i \<in> A \<Longrightarrow> (\<exists>i. \<not> strict P (f (Suc i)) (f i))) \<Longrightarrow> wfp_on (strict P) A"
  unfolding wfp_on_def by blast

lemma wfp_hom_neg:
  fixes h :: "'a \<Rightarrow> 'b"
  assumes map: "\<And>x y. \<lbrakk>x \<in> A; y \<in> A; \<not> strict P x y\<rbrakk> \<Longrightarrow> \<not> strict Q (h x) (h y)"
    and wfp: "wfp_on (strict P) A"
  shows "wfp_on (strict Q) (h ` A)"
proof (intro wfp_onI)
  fix f :: "nat \<Rightarrow> 'b"
  assume a:"\<forall>i. f i \<in> h ` A"
  then have "\<forall>i. \<exists>x. x \<in> A \<and> f i = h x" by (auto simp: image_def)
  from choice [OF this] obtain g
    where *:"\<forall>i. g i \<in> A \<and> f i = h (g i)" by metis
  show "\<exists>i. \<not> strict Q (f (Suc i)) (f i)"
  proof (rule ccontr, simp)
    assume bad: "\<forall>i. strict Q (f (Suc i)) (f i)"
    { fix i :: nat
      from bad have "strict Q (f (Suc i)) (f i)" by presburger
      with map have "strict P (g (Suc i)) (g i)" using * by auto }
    then have "\<forall>i. strict P (g (Suc i)) (g i)" by simp
    with wfp and * show False by (auto simp: wfp_on_def)
  qed
qed

lemma wfp_map:
  assumes "wfp_on (strict Q) B"
    and "h ` A \<subseteq> B"
  shows "wfp_on (strict (\<lambda>x y. Q (h x) (h y))) A" (is "wfp_on ?P A")
proof (intro wfp_onI)
  fix f
  assume "\<forall>i::nat. f i \<in> A"
  then have "\<And>i. h (f i) \<in> B" using \<open>h ` A \<subseteq> B\<close> by auto
  then show "\<exists>i. \<not> strict Q (h (f (Suc i))) (h (f i))"
    using wfp_on_spec[OF assms(1), of "h \<circ> f"] by force
qed

lemma wfp_neg_map:
  assumes "wfp_on (strict P) B"
      and "h ` A \<subseteq> B"
      and "\<And>x y. x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> \<not> strict P (h x) (h y) \<Longrightarrow> \<not> strict Q x y"
    shows "wfp_on (strict Q) A"
  using wfp_hom_neg[OF _ wfp_map[OF assms(1,2)], where h = id] assms(3) by simp

lemma wfp_on_single: "wfp_on P UNIV \<Longrightarrow> wfp_on P {x}"
  unfolding wfp_on_def by blast

\<comment> \<open>Base case of the induction for the almost-full property\<close>
lemma finfuns_empty_wfp: "wfp_on (strict (finfun_emb P)) ((finfuns {})::('a \<Rightarrow>f 'b::zero) set)"
  unfolding wfp_on_def finfun_emb_def
proof safe
  fix seq :: "nat \<Rightarrow> ('a \<Rightarrow>f 'b)"
  assume "\<forall>i. (seq i) \<in> finfuns {} \<and> (\<forall>a. P (seq (Suc i) $ a) (seq i $ a)) \<and> \<not> (\<forall>a. P (seq i $ a) (seq (Suc i) $ a))"
  then have 
    a:"\<And>i. seq i \<in> finfuns {}" and
    b:"\<And>i. (\<forall>a. P (seq (Suc i) $ a) (seq i $ a))" and
    c:"\<And>i. (\<exists>a. \<not> P (seq i $ a) (seq (Suc i) $ a))" by auto
  then have "\<And>i. \<forall>a. \<not> P (seq i $ a) (seq (Suc i) $ a)"
    subgoal for i using finfuns_empty_exist_all[of "seq i" "seq (Suc i)"] by blast done
  from a have "\<And>i. seq i = (K$ 0)" using finfuns_empty by blast
  then show False using b c by presburger
qed

lemma finfun_antisymp_on:
  assumes "antisymp_on UNIV P"
  shows "antisymp_on (finfuns A) (finfun_emb P)"
  using assms unfolding antisymp_on_def finfun_emb_def
  apply safe
  subgoal for f g
    apply (rule finfun_ext[of f g])
    by blast
  done

definition single_hom :: "'a \<Rightarrow> 'a \<Rightarrow>f 'b \<Rightarrow> 'b::zero" where 
  "single_hom a f = f$a"

lemma single_hom_correct:
  assumes "x \<in> finfuns {a}"
      and "y \<in> finfuns {a}"
      and "\<not> strict P (single_hom a x) (single_hom a y)"
    shows "\<not> strict (finfun_emb P) x y"
  using assms unfolding single_hom_def finfuns_single finfun_emb_def
  apply simp
  apply auto
  subgoal for b b' a'
    by (metis finfun_upd_apply_other finfun_upd_apply_same)
  done

lemma finfuns_single_wfp:
  assumes "wfp_on (strict P) UNIV"
  shows "wfp_on (strict (finfun_emb P)) ((finfuns {a})::('a \<Rightarrow>f 'b::zero) set)"
  using wfp_neg_map[OF assms, of "single_hom a" "finfuns {a}" "finfun_emb P"] 
        single_hom_correct[of _ a _ P]
  by blast

\<comment> \<open>In the step of the induction, we use Dickson's lemma for almost-full relations @{thm almost_full_on_Sigma}
    and a homomorphism from a pair of finfuns to a finfun with larger input domain @{term "insert a A"} using @{thm almost_full_on_hom}.\<close>

definition step_hom :: "'a \<Rightarrow> 'a \<Rightarrow>f 'b::zero \<Rightarrow> ('a \<Rightarrow>f 'b \<times> 'a \<Rightarrow>f 'b)" where 
  "step_hom a f = ((K$0)(a $:= f $ a), f(a $:= 0))"

lemma step_hom_img: 
  assumes "finite A"
    shows "step_hom a ` finfuns (insert a A) \<subseteq> finfuns {a} \<times> finfuns A"
  unfolding step_hom_def
  using finite_finfuns_insert_undo[OF assms] by auto

lemma aux_finfun_update_apply_P:
  assumes"\<And>a'. P (f(a $:= x $ a) $ a') (f(a $:= y $ a) $ a')"
  shows "P (x $ a) (y $ a)"
  using assms[of a] by simp

lemma step_hom_correct:
  assumes "reflp_on UNIV P"
  assumes "\<not> strict (prod_le (finfun_emb P) (finfun_emb P)) (step_hom a x) (step_hom a y)"
    shows "\<not> strict (finfun_emb P) x y"
  using assms unfolding step_hom_def finfuns_single finfun_emb_def prod_le_def reflp_on_def
  apply simp
  apply safe
  subgoal for _ a'
    by (cases "a' = a", simp_all)
  subgoal for _ a'
    by (cases "a' = a", simp_all)
  subgoal for a'
    apply (cases "a' = a")
    using aux_finfun_update_apply_P[of P "K$ 0" a y x]
    apply simp
    by (metis finfun_upd_apply_other)  
  done

lemma finfuns_insert_prod_wfp: 
  assumes "wfp_on (strict (prod_le (finfun_emb P) (finfun_emb P))) (finfuns {a} \<times> finfuns A)"
      and "reflp_on UNIV P"
      and "finite A"
    shows "wfp_on (strict (finfun_emb P)) (finfuns (insert a A))"
  using wfp_neg_map[OF assms(1), of "step_hom a" "(finfuns (insert a A))" "finfun_emb P"] 
        step_hom_correct[OF assms(2), of a]        
        step_hom_img[OF assms(3)]
  by blast

\<comment> \<open>Use the lemmas for singleton input and @{term "insert a A"} input to prove the induction step.\<close>
lemma finfuns_insert_wfp:
  assumes "wfp_on (strict P) UNIV"
      and "wfp_on (strict (finfun_emb P)) (finfuns A)"
      and "antisymp_on UNIV P"
      and "reflp_on UNIV P"
      and "finite A"
    shows "wfp_on (strict (finfun_emb P)) (finfuns (insert a A))"
  using assms finfun_antisymp_on 
  using wfp_on_Sigma[of "finfuns {a}" "finfun_emb P" "finfuns A" "finfun_emb P"]
  using finfuns_single_wfp[of P a]
  using finfuns_insert_prod_wfp[of P a A]
  by blast

\<comment> \<open>Finfuns of a finite domain preserve the almost-full property (all infinite sequences contain a non-decreasing pair).
    This is the main result in this section, and goes by induction on the finite input domain A.\<close>
lemma finite_finfuns_wfp:
  assumes "finite (A::'a set)"
      and "antisymp_on (UNIV::'b::zero set) P"
      and "reflp_on UNIV P"
      and "wfp_on (strict P) UNIV"
    shows "wfp_on (strict (finfun_emb P)) ((finfuns A)::(('a \<Rightarrow>f 'b) set))"  
  using assms
proof (induction rule: finite.induct)
  case emptyI
  then show ?case using finfuns_empty_wfp by fast
next
  case (insertI A a)
  then show ?case using finfuns_insert_wfp by fast    
qed

\<comment> \<open>Transitivity of the @{term finfun_emb} on @{term finfuns}.\<close>
lemma finfuns_transp_on:
  assumes "transp_on UNIV P"
    shows "transp_on (finfuns A) (finfun_emb P)"
  using assms unfolding finfun_emb_def transp_on_def
  by blast

instantiation finfun :: (finite, "{wfp,zero}") wfp
begin
instance proof fix f :: "(nat \<Rightarrow> ('a::finite \<Rightarrow>f 'b::{wfp,zero}))"
    have f:"finite (UNIV::('a set))" by simp
    have a:"antisymp_on (UNIV::('b::{wfp,zero} set)) (\<le>)" by (fact antisymp_on_less_eq)
    have r:"reflp_on (UNIV::('b::{wfp,zero} set)) (\<le>)" unfolding reflp_on_def by simp
    have w:"wfp_on (strict (\<le>)) (UNIV::('b::{wfp,zero} set))" using wfp_on_class .
    have "wfp_on (strict (\<le>)) (UNIV::(('a \<Rightarrow>f 'b) set))"
      using finite_finfuns_wfp[of UNIV "(\<le>)", OF f a r w]
      unfolding finfun_emb_def less_eq_finfun_def by (rule subst[OF finfuns_UNIV])
    then have "wfp_on (<) (UNIV::(('a \<Rightarrow>f 'b) set))" by (simp add: less_eq_strict[symmetric])
    then show "\<nexists>f::(nat \<Rightarrow> ('a::finite \<Rightarrow>f 'b::{wfp,zero})). \<forall>i. f (Suc i) < f i" 
      unfolding wfp_on_def by simp
  qed
end
instantiation finfun :: (finite, bounded_idempotent_comm_monoid_add) bounded_idempotent_comm_monoid_add begin instance .. end

(*
\<comment> \<open>Finally make the class instantiation.\<close>
instantiation finfun :: (finite, bounded_idempotent_comm_monoid_add) bounded_idempotent_comm_monoid_add
begin
  instance proof fix f :: "(nat \<Rightarrow> ('a::finite \<Rightarrow>f 'b::bounded_idempotent_comm_monoid_add))"
    have f:"finite (UNIV::('a set))" by simp
    have w:"wqo_on (\<le>) (UNIV::('b::bounded_idempotent_comm_monoid_add set))" using bounded_idempotent_comm_monoid_add_on_class .
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
*)
\<comment> \<open>Extra lemmas\<close>
lemma finfun_update_less:
  fixes f f' :: "'a \<Rightarrow>f 'weight::preorder"
  assumes "f $ a < f' $ a"
  assumes "f(a $:= d) = f'"
  shows "f < f'"
  using assms unfolding less_finfun_def less_eq_finfun_def
  apply (simp, safe)
  subgoal for a'
    apply (cases "a = a'")
    using order_less_imp_le by (blast, simp)
  using dual_order.strict_iff_not by blast

lemma finfun_update_greater:
  fixes f f' :: "'a \<Rightarrow>f 'weight::preorder"
  assumes "f $ a > f' $ a"
  assumes "f(a $:= d) = f'"
  shows "f > f'"
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

lemma wf_less_finfun: "wf ({(x, y). x < y}::('a::finite \<Rightarrow>f 'weight::bounded_idempotent_semiring \<times> 'a \<Rightarrow>f 'weight) set)"
  unfolding less_finfun_def using wfp_on_class[of UNIV] unfolding wfp_on_UNIV[of "strict (\<le>)"] wfP_def[of "strict (\<le>)"] by blast

end