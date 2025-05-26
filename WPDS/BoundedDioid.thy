theory BoundedDioid
  imports "HOL.Lattices" "HOL.Order_Relation" "HOL.Complete_Lattices" "HOL.Series" 
          "HOL-Library.Extended_Real" "Well_Quasi_Orders.Well_Quasi_Orders" 
begin

class idempotent_ab_semigroup_add = ab_semigroup_add +
  assumes add_idem[simp]: "a + a = a"
begin

lemma add_left_idem [ac_simps]: "x + (x + y) = x + y"
  unfolding add_assoc [symmetric] by simp
end

\<comment> \<open>This class borrows from join_semilattice in AFP theory Kleene_Algebra.Dioid
    (https://www.isa-afp.org/entries/Kleene_Algebra.html)
    but we define the order in the reverse way to follow the definition in [RSJM'05]\<close>
class idempotent_ab_semigroup_add_ord = idempotent_ab_semigroup_add + ord +
  assumes less_eq_def: "x \<le> y \<longleftrightarrow> x + y = x"
  and less_def: "x < y \<longleftrightarrow> x \<le> y \<and> x \<noteq> y"
begin
subclass order proof
  fix x y z :: 'a
  show "x < y \<longleftrightarrow> x \<le> y \<and> \<not> y \<le> x" unfolding less_def less_eq_def using add_commute by auto
  show "x \<le> x" unfolding less_eq_def using add_idem by simp
  show "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z" unfolding less_eq_def using add_assoc by metis
  show "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y" unfolding less_eq_def using add_commute by force
qed

sublocale meet: semilattice_inf "(+)" proof
  fix x y z
  show "x + y \<le> x" unfolding less_eq_def using add_commute add_left_idem by simp
  show "x + y \<le> y" unfolding less_eq_def using add_assoc by force
  show "x \<le> y \<Longrightarrow> x \<le> z \<Longrightarrow> x \<le> y + z" unfolding less_eq_def using add_assoc by metis
qed

lemma add_iso: "x \<le> y \<Longrightarrow> x + z \<le> y + z"
  using meet.inf_mono by blast

lemma order_prop: "x \<le> y \<longleftrightarrow> (\<exists>z. x = z + y)"
proof
  assume "x \<le> y"
  hence "x = x + y" by (simp add: less_eq_def)
  thus "\<exists>z. x = z + y" by auto
next
  assume "\<exists>z. x = z + y"
  then obtain c where "x = c + y" by auto
  hence "x \<le> c + y" by simp
  thus "x \<le> y" by simp
qed

lemma neq_mono: "a \<le> b \<Longrightarrow> c + b \<noteq> c \<Longrightarrow> c + a \<noteq> c"
  by (metis meet.inf.absorb1 meet.inf.coboundedI2)

lemma neq_mono_less: "a \<le> b \<Longrightarrow> c + b \<noteq> c \<Longrightarrow> c + a < c"
  unfolding less_def using neq_mono by simp

lemma add_less_mono: "a \<le> b \<Longrightarrow> c + b < c \<Longrightarrow> c + a < c"
  unfolding less_def using neq_mono by simp
end

\<comment> \<open>Many lemmas and proofs in these classes are heavily inspired from AFP theory Kleene_Algebra.Dioid, 
    but here adapted for the reverse definition of plus_ord
    (https://www.isa-afp.org/entries/Kleene_Algebra.html)\<close>
class idempotent_comm_monoid_add = idempotent_ab_semigroup_add + comm_monoid_add
begin

lemma idem_sum_elem: 
  assumes "finite S"   
  shows "x \<in> S \<Longrightarrow> \<Sum> S = x + \<Sum>S"
  apply (induct rule: finite_induct[OF assms], simp)
  subgoal for x' F
    using add.left_commute[of x' x "\<Sum> F"]
    by (cases "x = x'", simp_all add: ac_simps)
  done

lemma idem_sum_insert[simp]:
  assumes "finite S"   
  shows "\<Sum>(insert x S) = x + \<Sum>S"
  using idem_sum_elem[OF assms] sum.insert_if[OF assms, of id x] by simp

lemma idem_sum_image:
  assumes "finite S"
  shows "\<Sum> (f ` S) = sum f S"
  apply (induct rule: finite_induct[OF assms], simp)
  subgoal for x F
    using idem_sum_insert[of "(f ` F)" "f x"] 
    by fastforce
  done

lemma sum_insert_f:
  assumes "finite S"
  shows  "\<Sum> {f x |x. x \<in> insert s S} = f s + \<Sum> {f x |x. x \<in> S}"
proof -
  have f1:"finite (insert s S)" using assms by simp
  have f2:"finite (f ` S)" using assms by fast
  have u1:"{x. x \<in> insert s S} = insert s S" and u2:"{x. x \<in> S} = S" by auto
  have "\<Sum> (f ` (insert s S)) = f s + \<Sum> (f ` S)"
    unfolding idem_sum_image[of "insert s S" f, OF f1] idem_sum_image[of S f, OF assms]
    using sum.insert_if[of S f s, OF assms] idem_sum_elem[OF f2, of "f s", unfolded idem_sum_image[OF assms]]
    by simp
  then show ?thesis
    unfolding setcompr_eq_image[of f "\<lambda>x. x \<in> insert s S"] setcompr_eq_image[of f "\<lambda>x. x \<in> S"] u1 u2 by blast
qed

lemma sum_set_image_cong:
  assumes "finite S"
  assumes "\<And>s. s \<in> S \<Longrightarrow> f s = g s"
  shows "\<Sum> (f ` S) = \<Sum> (g ` S)"
  using assms(2) by (induct rule: finite_subset_induct'[OF assms(1), of S, simplified]) simp_all
lemma sum_set_image_cong':
  assumes "finite S"
  assumes "\<And>s. s \<in> S \<Longrightarrow> f s = g s"
  shows "\<Sum>{f s |s. s\<in>S} = \<Sum>{g s |s. s\<in>S}"
  using sum_set_image_cong[OF assms, of id, simplified]
        setcompr_eq_image[symmetric, of _ "\<lambda>s. s\<in>S", simplified]
  by metis

lemma idem_sum_const:
  assumes "finite S"
      and "S \<noteq> {}"
    shows "(\<Sum>x\<in>S. y) = y"
  using assms
  apply (induct rule: finite_induct, simp)
  subgoal for x F
    by (cases "F = {}", simp_all)
  done

lemma idem_sum_const':
  assumes "finite S"
      and "S \<noteq> {}"
    shows "\<Sum>{y |x. x\<in>S} = y"
  using idem_sum_const[OF assms, of y] 
  unfolding idem_sum_image[OF assms(1), of "\<lambda>i. y", symmetric] image_def 
  by simp

lemma idem_sum_distrib:
  assumes "finite S"
      and "S \<noteq> {}"
    shows "y + \<Sum> S = \<Sum> {y + x | x. x \<in> S}"
  using sum.distrib[of "\<lambda>x. y" id S, simplified, symmetric] 
  unfolding idem_sum_const[OF assms, of y]
  using idem_sum_image[OF assms(1), of "(+) y"]
  unfolding setcompr_eq_image[of "(+) y"] by simp

lemma idem_sum_distrib':
  assumes "finite S"
    shows "y + \<Sum> S = y + \<Sum> {y + x | x. x \<in> S}"
  apply (cases "S = {}", simp)
  unfolding idem_sum_distrib[OF assms, of y, symmetric] 
  by (simp add: ac_simps)

lemma sum_split:
  assumes "finite {x. P x}"
  shows  "\<Sum> {x. P x} = \<Sum> {x. P x \<and> Q x} + \<Sum> {x. P x \<and> \<not> Q x}"
proof -
  have "{x. P x \<and> Q x} \<inter> {x. P x \<and> \<not> Q x} = {}" by blast
  moreover have "{x. P x \<and> Q x} \<union> {x. P x \<and> \<not> Q x} = {x. P x}" by blast
  ultimately show ?thesis 
    using sum.union_disjoint[of "{x. P x \<and> Q x}" "{x. P x \<and> \<not> Q x}" id, simplified] assms by simp
qed

lemma idem_sum_subset:
  assumes "X \<subseteq> Y"
  assumes "finite Y"
  shows "\<Sum>Y + \<Sum>X = \<Sum>Y"
  using sum.subset_diff[OF assms, of id] add_assoc add_idem by simp

lemma idem_sum_union:
  assumes "finite (A \<union> B)"
  shows "\<Sum>(A \<union> B) = \<Sum>A + \<Sum>B"
  using assms sum.union_inter[of A B "\<lambda>x. x"] idem_sum_subset[OF _ assms(1), of "A \<inter> B"]
  by fastforce

lemma sum_split_f_P:
  assumes "finite {f x |x. P x}"
  shows  "\<Sum> {f x |x. P x} = \<Sum> {f x |x. P x \<and> Q x} + \<Sum> {f x |x. P x \<and> \<not> Q x}"
proof -
  have "{f x |x. P x \<and> Q x} \<union> {f x |x. P x \<and> \<not> Q x} = {f x| x. P x}" by blast
  then show ?thesis 
    using idem_sum_union[of "{f x |x. P x \<and> Q x}" "{f x |x. P x \<and> \<not> Q x}"] assms by argo
qed

lemma sum_subset_singleton_0_is_0:
  assumes "X \<subseteq> {0}"
  shows "\<Sum> X = 0"
  using assms by (cases "X = {0}"; cases "X = {}") auto

lemma idem_sum_sum:
  assumes "finite X"
  assumes "finite (\<Union>X)"
  shows "\<Sum>{(\<Sum>x) |x. x\<in>X} = \<Sum>(\<Union>X)"
  using assms
proof (induct rule: finite_induct)
  case empty
  then show ?case by simp
next
  case (insert x F)
  then show ?case
    using sum_insert_f[OF insert(1), of "\<lambda>x'. \<Sum>x'" x] idem_sum_union[of x "\<Union> F"]
    by force
qed


abbreviation sum_seq :: "(nat \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> 'a" where
  "sum_seq f i \<equiv> sum f {x. x < i}"

lemma sum_prefix_seq_split:
  fixes f :: "nat \<Rightarrow> 'a" 
  shows "n \<le> m \<Longrightarrow> sum_seq f m = sum_seq f n + (sum f {x. n \<le> x \<and> x < m})"
proof -
  have "finite {x. x < n}" by blast
  moreover have "finite {x. n \<le> x \<and> x < m}" by fast
  moreover have "{x. x < n} \<inter> {x. n \<le> x \<and> x < m} = {}" by auto
  ultimately have "sum f ({x. x < n} \<union> {x. n \<le> x \<and> x < m}) = sum_seq f n + sum f {x. n \<le> x \<and> x < m}" 
    using sum.union_disjoint by blast
  moreover assume \<open>n \<le> m\<close>
  then have "{x. x < m} = {x. x < n} \<union> {x. n \<le> x \<and> x < m}" by fastforce
  ultimately show ?thesis by presburger
qed

lemma sum_seq_elem:
  assumes "i < n"
  shows "sum_seq f n + f i = sum_seq f n"
proof -
  have "{x. x < n} = {x. x < n \<and> (x < i \<or> i < x)} \<union> {i}" using assms by fastforce
  then have "sum_seq f n = sum f ({x. x < n \<and> (x < i \<or> i < x)} \<union> {i})" by presburger
  then show ?thesis by (simp add: add_commute add_left_idem)
qed

lemma sum_interval_Suc_transfer: "(\<Sum>x | i \<le> x \<and> x < n. f (Suc x)) = (\<Sum>x | Suc i \<le> x \<and> x < Suc n. f x)"
proof -
  have t_Suc_comp:"(\<lambda>x. f (Suc x)) = f o Suc" by fastforce
  have Suc_inj: "inj_on Suc {x. i \<le> x \<and> x < n}" by simp
  have Suc_interval_img: "Suc ` {x. i \<le> x \<and> x < n} = {x. Suc i \<le> x \<and> x < Suc n}" unfolding image_def using Suc_le_D by blast
  have "Finite_Set.fold ((+) \<circ> (f \<circ> Suc)) 0 {x. i \<le> x \<and> x < n} = Finite_Set.fold ((+) \<circ> f) 0 (Suc ` {x. i \<le> x \<and> x < n})"
    using fold_image[OF Suc_inj, of "(+) \<circ> f" 0, symmetric] comp_assoc[of "(+)" f Suc] by argo
  then show ?thesis unfolding sum.eq_fold using t_Suc_comp Suc_interval_img by argo
qed

definition seq_except :: "(nat \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> 'a)" where
  "seq_except f i j = (if j < i then f j else f (Suc j))"

lemma seq_except_split_sum: 
  assumes "i < Suc n"
  shows "sum_seq (seq_except f i) n = sum_seq f i + sum f {x. Suc i \<le> x \<and> x < Suc n}"
  using sum_prefix_seq_split[of i n "seq_except f i"] assms(1) sum_interval_Suc_transfer
  unfolding seq_except_def by simp

lemma seq_except_same_sum:
  assumes "f i = f j"
      and "i < Suc n"
      and "j < i"
    shows "sum_seq f (Suc n) = sum_seq (seq_except f i) n"
proof -
  have "\<And>x. i \<le> x \<and> x < Suc i \<longleftrightarrow> i = x" by fastforce
  then have "(\<Sum>x | i \<le> x \<and> x < Suc i. f x) = f i" by fastforce
  then have "sum_seq f (Suc n) = sum_seq f i + f i + (\<Sum>x | Suc i \<le> x \<and> x < Suc n. f x)" 
    using assms(2) by (simp add: sum_prefix_seq_split[of "(Suc i)" "Suc n" f] sum_prefix_seq_split[of i "Suc i" f])
  moreover have "sum_seq (seq_except f i) n = sum_seq f i + sum f {x. Suc i \<le> x \<and> x < Suc n}" 
    by (simp add: seq_except_split_sum[OF assms(2), of f])
  ultimately show ?thesis using sum_seq_elem[OF assms(3), of f] assms(1) by argo
qed

lemma seq_except_same_image:
  assumes "f i = f j" and "i < Suc n" and "j < i"
    shows "{f x | x. x < Suc n} = {(seq_except f i) x | x. x < n}"
  unfolding seq_except_def using assms
  apply safe
  subgoal for _ y
    apply (cases "i = y")
    apply auto[1]
    apply (cases "i > y")
    apply auto[1]
    by (rule exI[of _ "y - 1"], auto)
  by auto

lemma not_inj_implies_seq_except:
  assumes "\<not> inj_on f {i. i < Suc n}"
  shows "\<exists>i. sum_seq f (Suc n) = sum_seq (seq_except f i) n \<and> {f x | x. x < Suc n} = {(seq_except f i) x | x. x < n}"
  using assms unfolding inj_on_def
  apply simp
  apply safe
  subgoal for i j
    apply (cases "i < j") 
    by (auto simp add: seq_except_same_sum[of f j i n]   seq_except_same_sum[of f i j n] 
                     seq_except_same_image[of f j i n] seq_except_same_image[of f i j n])
  done

lemma exists_smaller_induct:
  assumes "\<And>f n::nat. \<not> P f n \<Longrightarrow> \<exists>f'. Q f n = Q f' (n-1)"
  assumes "\<And>f. P f 0"
  shows "\<exists>f' n'. n' \<le> n \<and> Q f n = Q f' n' \<and> P f' n'"
  apply (rule ccontr, simp)
  apply (induct n arbitrary: f)
  subgoal for f
    apply (erule allE[of _ f])
    by (auto simp add: assms(2))
  subgoal for n f
    using assms(1)[of f "Suc n"] by fastforce
  done

lemma inj_on_0:
  fixes f :: "nat \<Rightarrow> 'a"
  shows "inj_on f {i. i < 0}" by simp

lemma not_inj_implies_smaller_sumseq:
  fixes f :: "nat \<Rightarrow> 'a"
  assumes "\<not> inj_on f {i. i < n}"
  shows "\<exists>f'. (sum_seq f n, {f i | i. i < n}) = (sum_seq f' (n - 1), {f' i | i. i < n - 1})"
  apply (cases "n = 0", simp)
  using not_inj_implies_seq_except[of f "n - 1"] assms
  apply simp
  apply (erule exE)
  subgoal for i
    apply (rule exI[of _ "seq_except f i"])
    by blast
  done

lemma exists_inj_sum_seq:
  "\<exists>f' n'. n' \<le> n \<and> sum_seq f n = sum_seq f' n' \<and> {f i | i. i < n} = {f' i | i. i < n'} \<and> inj_on f' {i. i < n'}"
  using exists_smaller_induct[of "\<lambda>f n. inj_on f {i. i < n}" "\<lambda>f n. (sum_seq f n, {f i | i. i < n})", 
                              OF not_inj_implies_smaller_sumseq inj_on_0, simplified, of n f]
  by blast

lemma sum_seq_to_sum: \<comment> \<open>Due to idempotency, repeated elements in f does not change the sum.\<close>
  shows "sum_seq f n = \<Sum> {f i | i. i < n}"
proof -
  obtain f' n' where "n' \<le> n" and 
       eq:"sum_seq f n = sum_seq f' n'" and 
       img:"{f i | i. i < n} = {f' i | i. i < n'}" and 
       inj:"inj_on f' {i. i < n'}"
    using exists_inj_sum_seq by blast
  have apply_img:"{f' i | i. i < n'} = f' ` {x. x < n'}" by blast
  then have "sum_seq f' n' = \<Sum> {f' i | i. i < n'}" unfolding sum.eq_fold 
    by (simp add: comp_id[unfolded id_def, of "(+)"] fold_image[OF inj, of "(+)" 0, symmetric])
  then show ?thesis using eq img by argo
qed

end

class idempotent_comm_monoid_add_ord = idempotent_ab_semigroup_add_ord + comm_monoid_add
begin
subclass idempotent_comm_monoid_add ..

sublocale meet: bounded_semilattice_inf_top "(+)" "(\<le>)" "(<)" 0
  by unfold_locales (simp add: local.order_prop)

lemma no_trivial_inverse: "x \<noteq> 0 \<Longrightarrow> \<not>(\<exists>y. x + y = 0)"
  by (metis local.add_0_right local.meet.inf_left_idem)

lemma less_eq_zero: "x \<le> 0" unfolding less_eq_def by simp

lemma less_zero: "x \<noteq> 0 \<Longrightarrow> x < 0" unfolding less_def using less_eq_def by simp

lemma sum_prefix_seq_greater_eq:
  fixes f :: "nat \<Rightarrow> 'a"
  assumes "n \<le> m"
  shows "sum_seq f n \<ge> sum_seq f m"
  apply simp
  using sum_prefix_seq_split[OF assms, of f] by simp

lemma sum_seq_no_antichain: "\<not> antichain_on (\<le>) (sum_seq f) UNIV"
  unfolding less_eq_def
  apply simp
  apply (rule exI, rule exI)
  using sum_prefix_seq_split by auto

lemma "(sum_seq f) (Suc i) \<le> (sum_seq f) i"
  using sum_prefix_seq_greater_eq by auto

lemma sum_seq_elem_ord:
  assumes "i < n"
  shows "sum_seq f n \<le> f i"
  unfolding less_eq_def using sum_seq_elem[OF assms] by presburger

lemma sum_superset_less_eq:
  assumes "B \<subseteq> A" and "finite A"
    shows "\<Sum> A \<le> \<Sum> B"
  unfolding less_eq_def using sum.subset_diff[OF assms, of id] by force

lemma sum_collect_mono:
  assumes "finite {x. Q x}"
  assumes "P \<le> Q"
  shows "\<Sum> (Collect P) \<ge> \<Sum> (Collect Q)"
  using sum_superset_less_eq[OF Collect_mono assms(1)] assms(2) by blast

lemma sum_greater_elem:
  assumes "\<And>a. a \<in> A \<Longrightarrow> b \<le> a"
      and "finite A"
    shows "b \<le> \<Sum> A"
  using assms(1)
  unfolding less_eq_def
  apply (induct rule: finite_induct[OF assms(2)])
  by (simp_all add: local.add.left_commute local.meet.inf_commute)

lemma sum_smaller_elem:
  assumes "\<And>a. a \<in> A \<Longrightarrow> a \<le> b"
      and "finite A"
      and "A \<noteq> {}"
    shows "\<Sum> A \<le> b"
  using assms(1,3)
  unfolding less_eq_def
  apply (induct rule: finite_induct[OF assms(2)])
   apply (simp_all add: local.add.left_commute local.meet.inf_commute)
  by fastforce
end

lemma elem_greater_than_sum:
  fixes P :: "'a::idempotent_comm_monoid_add_ord \<Rightarrow> bool"
  assumes "P x"
  assumes "finite {a. P a}"
  shows "\<Sum>{a. P a} \<le> x"
  using assms idem_sum_elem[OF assms(2), of x] unfolding idempotent_ab_semigroup_add_ord_class.less_eq_def
  by (simp add: add.commute)


\<comment> \<open>An idempotent semiring that follows the definition of [RSJM'05].\<close>
class idempotent_semiring = semiring_0 + monoid_mult + idempotent_ab_semigroup_add
begin
subclass idempotent_comm_monoid_add ..

lemma sum_mult_not0_is_sum:
  assumes "finite {a. P a}"
  shows "\<Sum>{f a * g a | a. P a \<and> f a \<noteq> 0} = \<Sum>{f a * g a | a. P a}"
proof -
  have fnot0:"finite {f a * g a | a. P a \<and> f a \<noteq> 0}" using assms by simp
  have f0:"finite {f a * g a | a. P a \<and> f a = 0}" using assms by simp
  have is0: "\<Sum>{f a * g a | a. P a \<and> f a = 0} = 0" 
    using sum.neutral[of "{f a * g a |a. P a \<and> f a = 0}" id] mult_zero_left
    by fastforce

  have "\<forall>x\<in>{f a * g a |a. P a \<and> f a = 0}. id x = 0"
    using mult_zero_left by fastforce
  then have A:"\<forall>x\<in>{f a * g a |a. P a \<and> f a \<noteq> 0} \<inter> {f a * g a |a. P a \<and> f a = 0}. id x = 0"
    by blast
  have "{f a * g a | a. P a \<and> f a \<noteq> 0} \<union> {f a * g a | a. P a \<and> f a = 0} = {f a * g a | a. P a}" by blast
  then have "\<Sum>{f a * g a | a. P a} = \<Sum>{f a * g a | a. P a \<and> f a \<noteq> 0} + \<Sum>{f a * g a | a. P a \<and> f a = 0}"
    using sum.union_inter_neutral[OF fnot0 f0 A] by simp
  then show ?thesis using is0 by simp
qed

lemma sum_not0_is_sum:
  assumes "finite {a. P a}"
  shows "\<Sum>{f a | a. P a \<and> f a \<noteq> 0} = \<Sum>{f a | a. P a}"
proof -
  have fnot0:"finite {f a | a. P a \<and> f a \<noteq> 0}" using assms by simp
  have f0:"finite {f a | a. P a \<and> f a = 0}" using assms by simp
  have is0: "\<Sum>{f a | a. P a \<and> f a = 0} = 0"
    using sum.neutral[of "{f a |a. P a \<and> f a = 0}" "(\<lambda>x. x)"] by blast
  have u:"{f a | a. P a \<and> f a \<noteq> 0} \<union> {f a | a. P a \<and> f a = 0} = {f a | a. P a}" by blast
  have x0:"\<forall>x\<in>{f a |a. P a \<and> f a \<noteq> 0} \<inter> {f a |a. P a \<and> f a = 0}. x = 0" by blast
  have "\<Sum>{f a | a. P a} = \<Sum>{f a | a. P a \<and> f a \<noteq> 0} + \<Sum>{f a | a. P a \<and> f a = 0}"
    using sum.union_inter_neutral[OF fnot0 f0, of "(\<lambda>x. x)", OF x0]
    unfolding u by argo
  then show ?thesis using is0 by simp
qed

lemma sum_if_1_0_right_is_sum:
  assumes "finite {a. P a}"
  shows "\<Sum>{f a * (if Q a then 1 else 0) | a. P a} = \<Sum>{f a | a. P a \<and> Q a}"
proof -
  have fnot0:"finite {f a * (if Q a then 1 else 0) |a. P a \<and> \<not> Q a}" using assms by simp
  have f0:"finite {f a * (if Q a then 1 else 0) |a. P a \<and> Q a}" using assms by simp
  have is0: "\<Sum> {f a * (if Q a then 1 else 0) |a. P a \<and> \<not> Q a} = 0"
    using sum.neutral[of "{f a * (if Q a then 1 else 0) |a. P a \<and> \<not> Q a}" "(\<lambda>x. x)"] by fastforce
  have u:"{f a * (if Q a then 1 else 0) |a. P a \<and> \<not> Q a} \<union> {f a * (if Q a then 1 else 0) |a. P a \<and> Q a} = {f a * (if Q a then 1 else 0) | a. P a}" by blast
  have a:"\<forall>x\<in>{f a * (if Q a then 1 else 0) |a. P a \<and> \<not> Q a} \<inter> {f a * (if Q a then 1 else 0) |a. P a \<and> Q a}. x = 0"
    by auto
  have eq:"\<Sum>{f a * (if Q a then 1 else 0) | a. P a} = \<Sum> {f a * (if Q a then 1 else 0) |a. P a \<and> Q a}"
    using sum.union_inter_neutral[OF fnot0 f0 a]
    unfolding u is0 by auto
  show ?thesis unfolding eq
    by (rule arg_cong[of _ _ \<Sum>]) auto
qed

lemma sum_if_1_0_left_is_sum:
  assumes "finite {a. P a}"
  shows "\<Sum>{(if Q a then 1 else 0) * f a | a. P a} = \<Sum>{f a | a. P a \<and> Q a}"
proof -
  thm sum.union_inter_neutral
  have fnot0:"finite {(if Q a then 1 else 0) * f a |a. P a \<and> \<not> Q a}" using assms by simp
  have f0:"finite {(if Q a then 1 else 0) * f a |a. P a \<and> Q a}" using assms by simp
  have is0: "\<Sum> {(if Q a then 1 else 0) * f a |a. P a \<and> \<not> Q a} = 0"
    using sum.neutral[of "{(if Q a then 1 else 0) * f a |a. P a \<and> \<not> Q a}" "(\<lambda>x. x)"] by fastforce
  have u:"{(if Q a then 1 else 0) * f a |a. P a \<and> \<not> Q a} \<union> {(if Q a then 1 else 0) * f a |a. P a \<and> Q a} = {(if Q a then 1 else 0) * f a | a. P a}" by blast
  have a:"\<forall>x\<in>{(if Q a then 1 else 0) * f a |a. P a \<and> \<not> Q a} \<inter> {(if Q a then 1 else 0) * f a |a. P a \<and> Q a}. x = 0"
    by auto
  have eq:"\<Sum>{(if Q a then 1 else 0) * f a | a. P a} = \<Sum> {(if Q a then 1 else 0) * f a |a. P a \<and> Q a}"
    using sum.union_inter_neutral[OF fnot0 f0 a]
    unfolding u is0 by auto
  show ?thesis unfolding eq
    by (rule arg_cong[of _ _ \<Sum>]) auto
qed

end

class idempotent_semiring_ord = idempotent_semiring + idempotent_ab_semigroup_add_ord
begin

subclass idempotent_comm_monoid_add_ord ..

lemma mult_isor: "x \<le> y \<Longrightarrow> x * z \<le> y * z"
proof -
  assume "x \<le> y"
  hence "x + y = x"
    by (simp add: less_eq_def)
  hence "(x + y) * z = x * z"
    by simp
  thus "x * z \<le> y * z"
    by (simp add: distrib_right meet.inf.orderI)
qed

lemma subdistl: "z * (x + y) \<le> z * x"
  by (simp add: distrib_left)

lemma mult_isol_equiv_subdistl:
  "(\<forall>x y z. x \<le> y \<longrightarrow> z * x \<le> z * y) \<longleftrightarrow> (\<forall>x y z. z * (x + y) \<le> z * x)"
  by (metis meet.inf_absorb2 local.meet.inf_le1)

lemma subdistl_var: "z * (x + y) \<le> z * x + z * y"
  using local.mult_isol_equiv_subdistl local.subdistl by simp

lemma mult_isol: "x \<le> y \<Longrightarrow> z * x \<le> z * y"
proof -
  assume "x \<le> y"
  hence "x + y = x" by (simp add: less_eq_def)
  also have "z * (x + y) \<le> z * x + z * y" using subdistl_var by blast
  moreover have "z * (x + y) = z * x" by (simp add: calculation)
  ultimately show "z * x \<le> z * y" by auto
qed

lemma mult_isol_var: "u \<le> x \<Longrightarrow> v \<le> y \<Longrightarrow> u * v \<le> x * y"
  by (meson local.dual_order.trans local.mult_isor mult_isol)
end

class wfp = order +
  assumes no_infinite_decending: "\<nexists>f. \<forall>i. (f i) > (f (Suc i))"
begin

lemma strict_le_is_less:"strict (\<le>) = (<)"
  using dual_order.strict_iff_not by presburger

lemma transp_on_less_eq: "transp_on A (\<le>)"
  unfolding transp_on_def by fastforce

lemma qo_on_less_eq: "qo_on (\<le>) A"
  unfolding qo_on_def reflp_on_def using transp_on_less_eq by simp

lemma wfp_on_class: "wfp_on (strict (\<le>)) A"
  unfolding wfp_on_def using no_infinite_decending strict_le_is_less by blast

lemma "irreflp_on A (strict (\<le>))" by (fact irreflp_on_strict)

lemma wfP_strict_class: "wfP (strict (\<le>))" 
  using wfp_on_UNIV wfp_on_class[of UNIV] by blast

lemma no_antichain_on_implies_wqo_on: "(\<nexists>f. antichain_on (\<le>) f A) \<Longrightarrow> wqo_on (\<le>) A"
  using wqo_wf_and_no_antichain_conv[OF qo_on_less_eq] wfp_on_class by simp

lemma no_antichain_on_implies_almost_full_on: "(\<nexists>f. antichain_on (\<le>) f A) \<Longrightarrow> almost_full_on (\<le>) A"
  using no_antichain_on_implies_wqo_on wqo_af_conv[OF qo_on_less_eq] by blast

end

lemma wf_less_wfp: "wf ({(x, y). x < y}::('a::wfp \<times> 'a) set)"
  unfolding less_le_not_le using wfP_strict_class wfp_def[of "strict (\<le>)"] by blast

class bounded_idempotent_comm_monoid_add = wfp + idempotent_comm_monoid_add_ord
begin
subclass order ..

lemma sum_seq_good: "good (\<le>) (sum_seq f)"
  unfolding good_def
proof -
  have A:"\<forall>i. (sum_seq f) (Suc i) \<le> (sum_seq f) i"
    using sum_prefix_seq_greater_eq by auto
  moreover have "\<exists>i. \<not> (sum_seq f) (Suc i) < (sum_seq f) i" 
    using no_infinite_decending by fast
  ultimately have "\<exists>i. sum_seq f (Suc i) = sum_seq f i"
    unfolding less_def by blast
  then show "\<exists>i j. i < j \<and> sum_seq f i \<le> sum_seq f j" 
    apply simp
    apply (erule exE)
    subgoal for i
    apply (rule exI[of _ i])
      apply (rule exI[of _ "Suc i"])
      by simp
    done
qed
end

class bounded_idempotent_comm_monoid_add_topology = discrete_topology + bounded_idempotent_comm_monoid_add
begin
subclass t2_space proof
  fix x y :: 'a
  assume "x \<noteq> y"
  then show "\<exists>U V. open U \<and> open V \<and> x \<in> U \<and> y \<in> V \<and> U \<inter> V = {}"
    by (intro exI[of _ "{_}"]) (auto intro!: open_discrete)
qed
end

\<comment> \<open>For clarity, we here show the unfolded definition of an idempotent_semiring:\<close>
lemma idempotent_semiring_unfolded_definition:
   "class.idempotent_semiring (+) 1 (*) (0::'d) \<longleftrightarrow> 
    (\<forall>a b c::'d::{plus,one,times,zero}.
  \<comment> \<open>\<^term>\<open>(UNIV::'d set, (+), 0)\<close> is a commutative monoid:\<close>
    a + b + c = a + (b + c) \<and> 
    a + b = b + a \<and>    
    0 + a = a \<and> 
  \<comment> \<open>\<^term>\<open>(+)\<close> is idempotent:\<close> 
    a + a = a \<and>
  \<comment> \<open>\<^term>\<open>(UNIV::'d set, (*), 1)\<close> is a monoid:\<close>
    a * b * c = a * (b * c) \<and> 
    1 * a = a \<and> 
    a * 1 = a \<and> 
  \<comment> \<open>\<^term>\<open>(*)\<close> distributes over \<^term>\<open>(+)\<close>:\<close> 
    a * (b + c) = a * b + a * c \<and> 
    (a + b) * c = a * c + b * c \<and>
  \<comment> \<open>\<^term>\<open>0\<close> is an annihilator for \<^term>\<open>(*)\<close>:\<close> 
    0 * a = 0 \<and> 
    a * 0 = 0
  )"
  unfolding class.idempotent_semiring_def class.semiring_0_def
    class.semiring_0_def
    class.idempotent_ab_semigroup_add_def class.idempotent_ab_semigroup_add_axioms_def
    class.ab_semigroup_add_def class.ab_semigroup_add_axioms_def
    class.semigroup_add_def
    class.monoid_mult_def class.monoid_mult_axioms_def
    class.semigroup_mult_def      
    class.comm_monoid_add_def class.comm_monoid_add_axioms_def
    class.mult_zero_def
    class.semiring_def class.semiring_axioms_def
  by (rule iffI, force, blast)

lemma idempotent_semiring_unfolds:
  fixes a b c::"'d::{plus,one,times,zero}"
  assumes "class.idempotent_semiring (+) 1 (*) (0::'d)" 
  shows "a * b * c = a * (b * c)" and "1 * a = a" and "a * 1 = a"
    and "a + b + c = a + (b + c)" and "0 + a = a" and "a + b = b + a"
    and "a + a = a"
    and "a * (b + c) = a * b + a * c" and "(a + b) * c = a * c + b * c"
    and "0 * a = 0" and "a * 0 = 0"
  using idempotent_semiring_unfolded_definition assms by blast+

primrec decreasing_sequence_aux :: "(nat \<Rightarrow> 'a::bounded_idempotent_comm_monoid_add_topology) \<Rightarrow> (nat \<Rightarrow> 'a \<times> nat)" where
  "decreasing_sequence_aux f 0 = (0,0)"
| "decreasing_sequence_aux f (Suc i) = (
    let n = (SOME n. n \<ge> snd (decreasing_sequence_aux f i) \<and> sum f {x. x < n} \<noteq> fst (decreasing_sequence_aux f i)) 
    in (sum f {x. x < n}, n)
  )"

definition decreasing_sequence :: "(nat \<Rightarrow> 'a::bounded_idempotent_comm_monoid_add_topology) \<Rightarrow> (nat \<Rightarrow> 'a)" where
  "decreasing_sequence f i = fst (decreasing_sequence_aux f i)"

lemma decreasing_sequence_aux_some: 
  assumes "\<forall>L N. \<exists>n\<ge>N. sum f {x. x < n} \<noteq> L"
    and "n = (SOME n. snd (decreasing_sequence_aux f i) \<le> n \<and> sum f {x. x < n} \<noteq> fst (decreasing_sequence_aux f i))"
  shows "snd (decreasing_sequence_aux f i) \<le> n \<and> sum f {x. x < n} \<noteq> fst (decreasing_sequence_aux f i)"
  using assms(1)
  apply simp
  apply (erule allE[of _ "fst (decreasing_sequence_aux f i)"])
  apply (erule allE[of _ "snd (decreasing_sequence_aux f i)"])
  using someI_ex assms(2) by simp

lemma divergent_sum_implies_decreasing_sequence:
  assumes "\<forall>L N. \<exists>n\<ge>N. sum f {x. x < n} \<noteq> L"
  shows "decreasing_sequence f i > decreasing_sequence f (Suc i)"
proof -
  have "sum f {x. x < (SOME n. snd (decreasing_sequence_aux f i) \<le> n \<and> sum f {x. x < n} \<noteq> fst (decreasing_sequence_aux f i))}
         \<noteq> fst (decreasing_sequence_aux f i)" 
    using decreasing_sequence_aux_some[OF assms] by blast
  then have non_repeating: "decreasing_sequence f i \<noteq> decreasing_sequence f (Suc i)" 
    unfolding decreasing_sequence_def by simp
  have "snd (decreasing_sequence_aux f i) 
        \<le> (SOME n. snd (decreasing_sequence_aux f i) \<le> n \<and> sum f {x. x < n} \<noteq> fst (decreasing_sequence_aux f i))" 
    using decreasing_sequence_aux_some[OF assms] by blast
  moreover have "fst (decreasing_sequence_aux f i) = sum f {x. x < snd (decreasing_sequence_aux f i)}" 
    by (induct i, auto)
  ultimately have weak_decreasing: "decreasing_sequence f i \<ge> decreasing_sequence f (Suc i)"
    unfolding decreasing_sequence_def using sum_prefix_seq_greater_eq by simp
  show ?thesis using non_repeating weak_decreasing by simp
qed

lemma divergent_sum_implies_infinite_descending:
  assumes "\<exists>f::(nat \<Rightarrow> 'a::bounded_idempotent_comm_monoid_add_topology). \<forall>L N. \<exists>n\<ge>N. sum f {x. x < n} \<noteq> L"
  shows "\<exists>f::(nat \<Rightarrow> 'a::bounded_idempotent_comm_monoid_add_topology). \<forall>i. (f i) > (f (Suc i))"
  using assms
  apply simp
  apply (erule exE)
  subgoal for f
    using divergent_sum_implies_decreasing_sequence[of f] exI[of _ "decreasing_sequence f"] by blast
  done

lemma eventually_stable_sum': 
    "\<forall>f::(nat \<Rightarrow> 'a::bounded_idempotent_comm_monoid_add_topology). \<exists>L N. \<forall>n\<ge>N. sum_seq f n = L"
  apply (rule ccontr, simp)
  apply (drule divergent_sum_implies_infinite_descending) 
  using no_infinite_decending by blast

lemma eventually_stable_sum:
  fixes f :: "nat \<Rightarrow> 'a::bounded_idempotent_comm_monoid_add_topology"
  shows "\<exists>L N. \<forall>n\<ge>N. sum_seq f n = L"
  using eventually_stable_sum' by blast

lemma summable_bounded_dioid:
  fixes f :: "nat \<Rightarrow> 'a::bounded_idempotent_comm_monoid_add_topology"
  shows "summable f"
  unfolding summable_def sums_def lessThan_def
  apply (simp add: tendsto_discrete[of "(\<lambda>n. \<Sum>x | x < n. f x)" _ sequentially] eventually_sequentially)
  by (fact eventually_stable_sum)

lemma stable_sum_is_suminf:
  fixes f :: "nat \<Rightarrow> 'a::bounded_idempotent_comm_monoid_add_topology"
  shows "\<exists>N. \<forall>n\<ge>N. sum_seq f n = suminf f"
  using summable_sums[OF summable_bounded_dioid[of f], unfolded sums_def lessThan_def]
  by (simp add: tendsto_discrete eventually_sequentially)

lemma sumseq_suminf_obtain_bound:
  fixes f :: "nat \<Rightarrow> 'a::bounded_idempotent_comm_monoid_add_topology"
  obtains N where "\<forall>n\<ge>N. sum_seq f n = suminf f"
  using stable_sum_is_suminf[of f] by blast

lemma sumseq_suminf_obtain:
  fixes f :: "nat \<Rightarrow> 'a::bounded_idempotent_comm_monoid_add_topology"
  obtains n where "sum_seq f n = suminf f"
  using stable_sum_is_suminf[of f] by blast

lemma stable_sum_eq_to_suminf_eq:
  fixes f f' :: "nat \<Rightarrow> 'a::bounded_idempotent_comm_monoid_add_topology"
  assumes "\<exists>N. \<forall>n\<ge>N. sum_seq f n = sum_seq f' n"
  shows "suminf f = suminf f'"
  using assms stable_sum_is_suminf[of f] stable_sum_is_suminf[of f']
  apply safe
  subgoal for N Na Nb
    apply (erule allE[of _ "max N (max Na Nb)"])
    by simp
  done

lemma suminf_elem:
  fixes f :: "nat \<Rightarrow> 'a::bounded_idempotent_comm_monoid_add_topology"
  shows "suminf f \<le> f i"
proof -
  obtain N where N_def:"\<forall>n\<ge>N. sum_seq f n = suminf f" 
    by (fact sumseq_suminf_obtain_bound)
  then obtain n where "sum_seq f n = suminf f" and "i < n" 
    by - (erule allE[of _ "max N (Suc i)"], simp)
  then show ?thesis using sum_seq_elem_ord[of i n]
    by metis
qed

lemma seqs_same_elems_exists_map:
  fixes f f' :: "nat \<Rightarrow> 'a::bounded_idempotent_comm_monoid_add_topology"
  assumes "\<And>l. (\<exists>i. f i = l) \<longleftrightarrow> (\<exists>i. f' i = l)"
  shows "\<exists>g. \<forall>i. f i = f' (g i)"
proof -
  have "\<forall>i. \<exists>i'. f i = f' i'"
    apply safe
    subgoal for i
      using assms[of "f i"] by metis
    done
  then show ?thesis by metis
qed

lemma seqs_same_elems_obtain_map:
  fixes f f' :: "nat \<Rightarrow> 'a::bounded_idempotent_comm_monoid_add_topology"
  assumes "\<And>l. (\<exists>i. f i = l) \<longleftrightarrow> (\<exists>i. f' i = l)"
  obtains g where "\<And>i. f i = f' (g i)"
  using seqs_same_elems_exists_map[OF assms] by blast


\<comment> \<open>Definition 5 from [RSJM'05].\<close>
class bounded_dioid = bounded_idempotent_comm_monoid_add_topology + idempotent_semiring_ord
begin
end

lemma discrete_topology_True: "class.discrete_topology (\<lambda>S. True)" by standard auto

lemma idempotent_semiring_with_plus_ord:
  assumes "class.idempotent_semiring (+) 1 (*) (0::'d::{plus,one,times,zero})"
  shows "class.idempotent_comm_monoid_add_ord (+) (\<lambda>a b. a + b = a) (strict (\<lambda>a b. a + b = a)) (0::'d)"
        "class.idempotent_ab_semigroup_add_ord (+) (\<lambda>a b::'d. a + b = a) (strict (\<lambda>a b. a + b = a))"
        "class.order (\<lambda>a b::'d. a + b = a) (strict (\<lambda>a b. a + b = a))"
    apply standard using idempotent_semiring_unfolds[OF assms] 
          apply auto[7]
   apply (metis idempotent_semiring_unfolds(4)[OF assms])
  by (simp add: idempotent_semiring_unfolds(6)[OF assms])

\<comment> \<open>For clarity, we here show how the bounded_dioid extends the definition of idempotent_semiring
   (When instantiated with the plus-order as it should be):\<close>
lemma bounded_dioid_unfolded_definition:
   "class.bounded_dioid (+) (\<lambda>a b::'d. a + b = a) (strict (\<lambda>a b. a + b = a)) 0 (\<lambda>S. True) 1 (*) \<longleftrightarrow>
  \<comment> \<open>An idempotent semiring\<close>
    class.idempotent_semiring (+) 1 (*) (0::'d::{plus,one,times,zero}) \<and>
  \<comment> \<open>where there is no infinite descending chain in the order defined by \<^term>\<open>\<And>a b. a \<le> b \<equiv> a + b = a\<close>\<close>
    (\<nexists>f::nat\<Rightarrow>'d. \<forall>i. (strict (\<lambda>a b. a + b = a)) (f (i + 1)) (f i))"
  unfolding class.bounded_dioid_def
    class.bounded_idempotent_comm_monoid_add_topology_def 
    class.bounded_idempotent_comm_monoid_add_def
    class.wfp_def class.wfp_axioms_def
  by (auto simp add: discrete_topology_True class.idempotent_semiring_ord_def idempotent_semiring_with_plus_ord)

lemma d_mult_not_zero: 
  assumes "(d::'weight::bounded_dioid) * d' \<noteq> 0" 
  shows "d \<noteq> 0" and "d' \<noteq> 0"
  using assms by auto

datatype nat_inf = fin nat | infinity

fun min_inf :: "nat_inf \<Rightarrow> nat_inf \<Rightarrow> nat_inf" where
  "min_inf infinity b = b"
| "min_inf a infinity = a"
| "min_inf (fin a) (fin b) = fin (min a b)"

fun plus_inf :: "nat_inf \<Rightarrow> nat_inf \<Rightarrow> nat_inf" where
  "plus_inf infinity _ = infinity"
| "plus_inf _ infinity = infinity"
| "plus_inf (fin a) (fin b) = fin (a + b)"

fun less_eq_inf :: "nat_inf \<Rightarrow> nat_inf \<Rightarrow> bool" where
  "less_eq_inf _ infinity = True"
| "less_eq_inf infinity _ = False"
| "less_eq_inf (fin a) (fin b) = (a \<le> b)"

fun less_inf :: "nat_inf \<Rightarrow> nat_inf \<Rightarrow> bool" where
  "less_inf infinity _ = False"
| "less_inf _ infinity = True"
| "less_inf (fin a) (fin b) = (a < b)"

interpretation min_plus_nat_inf: bounded_dioid min_inf less_eq_inf less_inf infinity "\<lambda>S. True" "fin 0" "plus_inf"
proof
  fix i :: nat
  fix a b c :: nat_inf
  fix K :: "nat_inf set set"
  show "min_inf (min_inf a b) c = min_inf a (min_inf b c)"
    by (smt (verit) min.assoc min_inf.elims nat_inf.distinct(1) nat_inf.inject)
  show "min_inf a b = min_inf b a"
    by (smt (verit) min.commute min_inf.elims min_inf.simps(1) min_inf.simps(2) nat_inf.inject)
  show "min_inf a a = a"
    by (metis min.idem min_inf.simps(1) min_inf.simps(3) nat_inf.exhaust)
  show "less_eq_inf a b = (min_inf a b = a)" 
    by (smt (verit) less_eq_inf.elims(1) min.absorb1 min.orderI min_inf.elims nat_inf.distinct(1) nat_inf.inject)
  show "less_inf a b = (less_eq_inf a b \<and> a \<noteq> b)"
    by (smt (verit) less_eq_inf.elims(1) less_inf.elims(1) less_inf.simps(1) less_inf.simps(2) nat_inf.inject nat_less_le)
  show "min_inf infinity a = a" by simp
  show "less_inf a b = strict less_eq_inf a b" 
    by (metis \<open>less_inf a b = (less_eq_inf a b \<and> a \<noteq> b)\<close> less_eq_inf.elims(2) less_inf.simps(3) linorder_not_less nat_inf.distinct(1))
  show "less_eq_inf a a"
    using less_eq_inf.elims(3) by blast
  show "less_eq_inf a b \<Longrightarrow> less_eq_inf b c \<Longrightarrow> less_eq_inf a c" 
    by (metis (no_types, lifting) le_trans less_eq_inf.elims(1) less_eq_inf.elims(2) less_eq_inf.simps(1) nat_inf.distinct(1) nat_inf.inject)
  show "less_eq_inf a b \<Longrightarrow> less_eq_inf b a \<Longrightarrow> a = b"
    using \<open>less_inf a b = (less_eq_inf a b \<and> a \<noteq> b)\<close> \<open>less_inf a b = strict less_eq_inf a b\<close> by blast
  show "\<nexists>f::nat\<Rightarrow>nat_inf. \<forall>i. less_inf (f (Suc i)) (f i)"
  proof safe
    fix f :: "nat \<Rightarrow> nat_inf"
    assume A:"\<forall>i. less_inf (f (Suc i)) (f i)"
    then have "\<And>i. f (Suc i) \<noteq> infinity" by (metis less_inf.simps(1))
    then have "\<And>i. \<exists>n. f (Suc i) = fin n" by (meson nat_inf.exhaust)
    then obtain f' :: "nat \<Rightarrow> nat" where "\<And>i. fin (f' i) = f (Suc i)" by metis
    then have "\<forall>i. f' (Suc i) < f' i" using A by (metis less_inf.simps(3))
    then show "False" by (induct "f' i" arbitrary: i rule: nat_less_induct) blast
  qed
  show "True" by blast
  show "True \<Longrightarrow> True \<Longrightarrow> True" by blast
  show "\<forall>S\<in>K. True \<Longrightarrow> True" by blast
  show "True" by blast
  show "plus_inf (plus_inf a b) c = plus_inf a (plus_inf b c)"
    by (smt (verit) add.assoc nat_inf.distinct(1) nat_inf.inject plus_inf.elims)
  show "plus_inf (fin 0) a = a" 
    by (metis add_0 nat_inf.exhaust plus_inf.simps(2) plus_inf.simps(3))
  show "plus_inf a (fin 0) = a" 
    by (metis add.commute add_0 nat_inf.exhaust plus_inf.simps(1) plus_inf.simps(3))
  show "plus_inf infinity a = infinity" by simp
  show "plus_inf a infinity = infinity" using plus_inf.elims by blast
  show "plus_inf (min_inf a b) c = min_inf (plus_inf a c) (plus_inf b c)"
  proof (cases "a \<noteq> infinity \<and> b \<noteq> infinity \<and> c \<noteq> infinity")
    case True
    then obtain a' b' c' where "a = fin a'" "b = fin b'" "c = fin c'" using nat_inf.exhaust by metis
    then show ?thesis by force
  next
    case False
    then show ?thesis 
      by (metis min_inf.simps(1) min_inf.simps(2) nat_inf.exhaust plus_inf.simps(1) plus_inf.simps(2))
  qed
  show "plus_inf a (min_inf b c) = min_inf (plus_inf a b) (plus_inf a c)" 
  proof (cases "a \<noteq> infinity \<and> b \<noteq> infinity \<and> c \<noteq> infinity")
    case True
    then obtain a' b' c' where "a = fin a'" "b = fin b'" "c = fin c'" using nat_inf.exhaust by metis
    then show ?thesis by force
  next
    case False
    then show ?thesis 
      by (metis min_inf.simps(1) min_inf.simps(2) nat_inf.exhaust plus_inf.simps(1) plus_inf.simps(2))
  qed
qed

instantiation nat_inf :: bounded_dioid begin

definition "one_nat_inf == fin 0 :: nat_inf"

definition "times_nat_inf == plus_inf :: nat_inf \<Rightarrow> nat_inf \<Rightarrow> nat_inf"

definition "open_nat_inf == (\<lambda>S. True) :: nat_inf set \<Rightarrow> bool"

definition "zero_nat_inf == infinity :: nat_inf"

definition "less_eq_nat_inf == less_eq_inf :: nat_inf \<Rightarrow> nat_inf \<Rightarrow> bool"

definition "less_nat_inf == less_inf :: nat_inf \<Rightarrow> nat_inf \<Rightarrow> bool"

definition "plus_nat_inf == min_inf :: nat_inf \<Rightarrow> nat_inf \<Rightarrow> nat_inf"

instance proof
  fix i :: nat
  fix a b c :: nat_inf
  fix S T :: "nat_inf set"
  fix K :: "nat_inf set set"
  show "a + b + c = a + (b + c)" unfolding plus_nat_inf_def
    by (smt (verit) min.assoc min_inf.elims nat_inf.distinct(1) nat_inf.inject)
  show "a + b = b + a" unfolding plus_nat_inf_def
    by (smt (verit) min.commute min_inf.elims min_inf.simps(1) min_inf.simps(2) nat_inf.inject)
  show "a + a = a" unfolding plus_nat_inf_def
    by (metis min.idem min_inf.simps(1) min_inf.simps(3) nat_inf.exhaust)
  show "(a \<le> b) = (a + b = a)" unfolding less_eq_nat_inf_def plus_nat_inf_def 
    by (smt (verit) less_eq_inf.elims(1) min.absorb1 min.orderI min_inf.elims nat_inf.distinct(1) nat_inf.inject)
  show "a < b = (a \<le> b \<and> a \<noteq> b)" unfolding less_nat_inf_def less_eq_nat_inf_def
    by (smt (verit) less_eq_inf.elims(1) less_inf.elims(1) less_inf.simps(1) less_inf.simps(2) nat_inf.inject nat_less_le)
  show "0 + a = a" unfolding zero_nat_inf_def plus_nat_inf_def by simp
  show "a < b = strict (\<le>) a b" unfolding less_nat_inf_def less_eq_nat_inf_def
    by (metis \<open>a < b = (a \<le> b \<and> a \<noteq> b)\<close>[unfolded less_nat_inf_def less_eq_nat_inf_def] less_eq_inf.elims(2) less_inf.simps(3) linorder_not_less nat_inf.distinct(1))
  show "a \<le> a" unfolding less_eq_nat_inf_def
    using less_eq_inf.elims(3) by blast
  show "a \<le> b \<Longrightarrow> b \<le> c \<Longrightarrow> a \<le> c" unfolding less_eq_nat_inf_def
    by (metis (no_types, lifting) le_trans less_eq_inf.elims(1) less_eq_inf.elims(2) less_eq_inf.simps(1) nat_inf.distinct(1) nat_inf.inject)
  show "a \<le> b \<Longrightarrow> b \<le> a \<Longrightarrow> a = b" unfolding less_eq_nat_inf_def
    using \<open>a < b = (a \<le> b \<and> a \<noteq> b)\<close>[unfolded less_nat_inf_def less_eq_nat_inf_def] 
          \<open>a < b = strict (\<le>) a b\<close>[unfolded less_nat_inf_def less_eq_nat_inf_def] 
    by blast
  show "\<nexists>f::nat\<Rightarrow>nat_inf. \<forall>i. (f (Suc i)) < (f i)"
  proof safe
    fix f :: "nat \<Rightarrow> nat_inf"
    assume A:"\<forall>i. (f (Suc i)) < (f i)"
    then have "\<And>i. f (Suc i) \<noteq> infinity" unfolding less_nat_inf_def by (metis less_inf.simps(1))
    then have "\<And>i. \<exists>n. f (Suc i) = fin n" by (meson nat_inf.exhaust)
    then obtain f' :: "nat \<Rightarrow> nat" where "\<And>i. fin (f' i) = f (Suc i)" by metis
    then have "\<forall>i. f' (Suc i) < f' i" using A unfolding less_nat_inf_def by (metis less_inf.simps(3))
    then show "False" by (induct "f' i" arbitrary: i rule: nat_less_induct) blast
  qed
  show "open (UNIV::nat_inf set)" unfolding open_nat_inf_def by blast
  show "open S \<Longrightarrow> open T \<Longrightarrow> open (S \<inter> T)" unfolding open_nat_inf_def by blast
  show "\<forall>S\<in>K. open S \<Longrightarrow> open (\<Union> K)" unfolding open_nat_inf_def by blast
  show "open S" unfolding open_nat_inf_def by blast
  show "a * b * c = a * (b * c)" unfolding times_nat_inf_def
    by (smt (verit) add.assoc nat_inf.distinct(1) nat_inf.inject plus_inf.elims)
  show "1 * a = a" unfolding times_nat_inf_def one_nat_inf_def
    by (metis add_0 nat_inf.exhaust plus_inf.simps(2) plus_inf.simps(3))
  show "a * 1 = a" unfolding times_nat_inf_def one_nat_inf_def
    by (metis add.commute add_0 nat_inf.exhaust plus_inf.simps(1) plus_inf.simps(3))
  show "0 * a = 0" unfolding times_nat_inf_def zero_nat_inf_def by simp
  show "a * 0 = 0" unfolding times_nat_inf_def zero_nat_inf_def using plus_inf.elims by blast
  show "(a + b) * c = a * c + b * c" unfolding times_nat_inf_def plus_nat_inf_def
  proof (cases "a \<noteq> infinity \<and> b \<noteq> infinity \<and> c \<noteq> infinity")
    case True
    then obtain a' b' c' where "a = fin a'" "b = fin b'" "c = fin c'" using nat_inf.exhaust by metis
    then show "plus_inf (min_inf a b) c = min_inf (plus_inf a c) (plus_inf b c)" by force
  next
    case False
    then show "plus_inf (min_inf a b) c = min_inf (plus_inf a c) (plus_inf b c)" 
      by (metis min_inf.simps(1) min_inf.simps(2) nat_inf.exhaust plus_inf.simps(1) plus_inf.simps(2))
  qed
  show "a * (b + c) = a * b + a * c " unfolding times_nat_inf_def plus_nat_inf_def
  proof (cases "a \<noteq> infinity \<and> b \<noteq> infinity \<and> c \<noteq> infinity")
    case True
    then obtain a' b' c' where "a = fin a'" "b = fin b'" "c = fin c'" using nat_inf.exhaust by metis
    then show "plus_inf a (min_inf b c) = min_inf (plus_inf a b) (plus_inf a c)" by force
  next
    case False
    then show "plus_inf a (min_inf b c) = min_inf (plus_inf a b) (plus_inf a c)" 
      by (metis min_inf.simps(1) min_inf.simps(2) nat_inf.exhaust plus_inf.simps(1) plus_inf.simps(2))
  qed
qed

end

end
