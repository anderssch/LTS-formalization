theory BoundedDioid
  imports "ReverseWellQuasiOrder"
          "HOL.Lattices" "HOL.Order_Relation" "HOL.Complete_Lattices" "HOL.Series"
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

end

\<comment> \<open>Many lemmas and proofs in these classes are heavily inspired from AFP theory Kleene_Algebra.Dioid, 
    but here adapted for the reverse definition of plus_ord
    (https://www.isa-afp.org/entries/Kleene_Algebra.html)\<close>
class idempotent_comm_monoid_add = idempotent_ab_semigroup_add + comm_monoid_add
class idempotent_comm_monoid_add_ord = idempotent_ab_semigroup_add_ord + comm_monoid_add
begin
subclass idempotent_comm_monoid_add ..
sublocale meet: bounded_semilattice_inf_top "(+)" "(\<le>)" "(<)" 0
  by unfold_locales (simp add: local.order_prop)
lemma no_trivial_inverse: "x \<noteq> 0 \<Longrightarrow> \<not>(\<exists>y. x + y = 0)"
  by (metis local.add_0_right local.meet.inf_left_idem)

lemma less_eq_zero: "x \<le> 0" unfolding less_eq_def by simp
lemma less_zero: "x \<noteq> 0 \<Longrightarrow> x < 0" unfolding less_def using less_eq_def by simp
end

\<comment> \<open>An idempotent semiring that follows the definition of [RSJM'05].\<close>
class idempotent_semiring = semiring_0 + monoid_mult + idempotent_ab_semigroup_add
begin
subclass idempotent_comm_monoid_add ..
end

class idempotent_semiring_ord = idempotent_semiring + idempotent_ab_semigroup_add_ord
begin
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

class bounded_idempotent_comm_monoid_add = discrete_topology + idempotent_comm_monoid_add_ord +
 assumes no_infinite_decending_chains: "almost_full_on (\<le>) UNIV"
begin
subclass wqo proof
  fix f
  show "good (\<le>) f" using no_infinite_decending_chains unfolding almost_full_on_def by simp
qed
subclass t2_space proof
  fix x y :: 'a
  assume "x \<noteq> y"
  then show "\<exists>U V. open U \<and> open V \<and> x \<in> U \<and> y \<in> V \<and> U \<inter> V = {}"
    by (intro exI[of _ "{_}"]) (auto intro!: open_discrete)
qed

lemma transp_on_UNIV: "transp_on (\<le>) UNIV"
  unfolding transp_on_def by fastforce
lemma wqo_on_UNIV: "wqo_on (\<le>) UNIV"
  unfolding wqo_on_def using transp_on_UNIV no_infinite_decending_chains by presburger
lemma wfp_on_UNIV:"wfp_on (<) UNIV"
  using wqo_on_imp_wfp_on[OF wqo_on_UNIV] less_le_not_le[abs_def] by blast
lemma no_antichain_on_UNIV: "\<not> antichain_on (\<le>) f UNIV"
  using almost_full_on_imp_no_antichain_on[OF no_infinite_decending_chains] by blast

\<comment> \<open>A more direct formulation of the no_infinite_decending_chain condition\<close>
lemma no_infinite_decending: "\<nexists>f. \<forall>i. (f i) > (f (Suc i))"
  using wfp_on_UNIV
  unfolding wfp_on_def by blast

end

lemma sum_prefix_seq_split:
  fixes f :: "nat \<Rightarrow> 'a::bounded_idempotent_comm_monoid_add" 
  shows "n \<le> m \<Longrightarrow> sum f {x. x < m} = (sum f {x. x < n}) + (sum f {x. n \<le> x \<and> x < m})"
proof -
  have "finite {x. x < n}" by blast
  moreover have "finite {x. n \<le> x \<and> x < m}" by fast
  moreover have "{x. x < n} \<inter> {x. n \<le> x \<and> x < m} = {}" by auto
  ultimately have "sum f ({x. x < n} \<union> {x. n \<le> x \<and> x < m}) = sum f {x. x < n} + sum f {x. n \<le> x \<and> x < m}" 
    using comm_monoid_add_class.sum.union_disjoint by fast
  moreover assume \<open>n \<le> m\<close>
  then have "{x. x < m} = {x. x < n} \<union> {x. n \<le> x \<and> x < m}" by fastforce
  ultimately show ?thesis by presburger
qed

lemma sum_prefix_seq_greater_eq:
  fixes f :: "nat \<Rightarrow> 'a::bounded_idempotent_comm_monoid_add"
  assumes "n \<le> m"
  shows "sum f {x. x < n} \<ge> sum f {x. x < m}"
  apply simp
  using sum_prefix_seq_split[OF assms, of f] by simp

primrec decreasing_sequence_aux :: "(nat \<Rightarrow> 'a::bounded_idempotent_comm_monoid_add) \<Rightarrow> (nat \<Rightarrow> 'a \<times> nat)" where
  "decreasing_sequence_aux f 0 = (0,0)"
| "decreasing_sequence_aux f (Suc i) = (
    let n = (SOME n. n \<ge> snd (decreasing_sequence_aux f i) \<and> sum f {x. x < n} \<noteq> fst (decreasing_sequence_aux f i)) 
    in (sum f {x. x < n}, n)
  )"
definition decreasing_sequence :: "(nat \<Rightarrow> 'a::bounded_idempotent_comm_monoid_add) \<Rightarrow> (nat \<Rightarrow> 'a)" where
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
  assumes "\<exists>f::(nat \<Rightarrow> 'a::bounded_idempotent_comm_monoid_add). \<forall>L N. \<exists>n\<ge>N. sum f {x. x < n} \<noteq> L"
  shows "\<exists>f::(nat \<Rightarrow> 'a::bounded_idempotent_comm_monoid_add). \<forall>i. (f i) > (f (Suc i))"
  using assms
  apply simp
  apply (erule exE)
  subgoal for f
    using divergent_sum_implies_decreasing_sequence[of f] exI[of _ "decreasing_sequence f"] by blast
  done

lemma eventually_stable_sum': 
    "\<forall>f::(nat \<Rightarrow> 'a::bounded_idempotent_comm_monoid_add). \<exists>L N. \<forall>n\<ge>N. sum f {x. x < n} = L"
  apply (rule ccontr, simp)
  apply (drule divergent_sum_implies_infinite_descending) 
  using no_infinite_decending by blast

lemma eventually_stable_sum:
  fixes f :: "nat \<Rightarrow> 'a::bounded_idempotent_comm_monoid_add"
  shows "\<exists>L N. \<forall>n\<ge>N. (\<Sum>x | x < n. f x) = L"
  using eventually_stable_sum' by blast

lemma summable_bounded_dioid:
  fixes f :: "nat \<Rightarrow> 'a::bounded_idempotent_comm_monoid_add"
  shows "summable f"
  unfolding summable_def sums_def lessThan_def
  apply (simp add: tendsto_discrete[of "(\<lambda>n. \<Sum>x | x < n. f x)" _ sequentially] eventually_sequentially)
  by (fact eventually_stable_sum)



\<comment> \<open>Definition 5 from [RSJM'05].\<close>
class bounded_idempotent_semiring = bounded_idempotent_comm_monoid_add + idempotent_semiring_ord
begin
end


(* TODO *)
lemma Suminf_lower: "x \<in> A \<Longrightarrow> \<Sum>A \<le> x" oops
lemma Suminf_greatest: "(\<And>x. x \<in> A \<Longrightarrow> z \<le> x) \<Longrightarrow> z \<le> \<Sum>A" oops
lemma Suminf_empty [simp]: "\<Sum>{} = 0" oops

class bounded_dioid = Inf + bounded_idempotent_semiring
begin

(* lemma "(\<Sqinter>x\<in>A. x) = b" *)

end


end