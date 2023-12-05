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

lemma idem_sum_insert:
  assumes "finite S"   
  shows "\<Sum>(insert x S) = x + \<Sum>S"
  using idem_sum_elem[OF assms] sum.insert_if[OF assms, of id x] by simp

lemma idem_sum_const:
  assumes "finite S"
      and "S \<noteq> {}"
    shows "(\<Sum>x\<in>S. y) = y"
  using assms
  apply (induct rule: finite_induct, simp)
  subgoal for x F
    by (cases "F = {}", simp_all)
  done

lemma idem_sum_image:
  assumes "finite S"
  shows "\<Sum> (f ` S) = sum f S"
  apply (induct rule: finite_induct[OF assms], simp)
  subgoal for x F
    using idem_sum_insert[of "(f ` F)" "f x"] 
    by fastforce
  done

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
lemma wfP_strict_class: "wfP (strict (\<le>))" using wfp_on_UNIV wfp_on_class[of UNIV] by blast

lemma no_antichain_on_implies_wqo_on: "(\<nexists>f. antichain_on (\<le>) f A) \<Longrightarrow> wqo_on (\<le>) A"
  using wqo_wf_and_no_antichain_conv[OF qo_on_less_eq] wfp_on_class by simp
lemma no_antichain_on_implies_almost_full_on: "(\<nexists>f. antichain_on (\<le>) f A) \<Longrightarrow> almost_full_on (\<le>) A"
  using no_antichain_on_implies_wqo_on wqo_af_conv[OF qo_on_less_eq] by blast
end

class bounded_idempotent_comm_monoid_add = wfp + idempotent_comm_monoid_add_ord
begin

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
(*  assumes no_infinite_decending_chains: "almost_full_on (\<le>) UNIV"*)
begin
subclass t2_space proof
  fix x y :: 'a
  assume "x \<noteq> y"
  then show "\<exists>U V. open U \<and> open V \<and> x \<in> U \<and> y \<in> V \<and> U \<inter> V = {}"
    by (intro exI[of _ "{_}"]) (auto intro!: open_discrete)
qed
end


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



lemma 
  fixes f f' :: "nat \<Rightarrow> 'a::bounded_idempotent_comm_monoid_add_topology"
  assumes "\<And>l. (\<exists>i. f i = l) \<longleftrightarrow> (\<exists>i. f' i = l)"
  shows "suminf f \<le> l \<Longrightarrow> suminf f' \<le> l"
  using assms suminf_elem[of f] suminf_elem[of f']
  unfolding less_eq_def
  oops

lemma 
  fixes f f' :: "nat \<Rightarrow> 'a::bounded_idempotent_comm_monoid_add_topology"
  assumes "\<And>l. (\<exists>i. f i = l) \<longleftrightarrow> (\<exists>i. f' i = l)"
  shows "suminf f = suminf f'"
proof -
  obtain g where "\<And>i. f i = f' (g i)" using seqs_same_elems_obtain_map[OF assms] by blast
  obtain h where "\<And>i. f' i = f (h i)" using seqs_same_elems_obtain_map[of f' f] assms by blast
  show ?thesis 
  using assms suminf_elem 
  apply -
  apply (rule stable_sum_eq_to_suminf_eq)
  using assms eventually_stable_sum[of f] eventually_stable_sum[of f']
  apply simp
  oops


\<comment> \<open>Definition 5 from [RSJM'05].\<close>
class bounded_idempotent_semiring = bounded_idempotent_comm_monoid_add_topology + idempotent_semiring_ord
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