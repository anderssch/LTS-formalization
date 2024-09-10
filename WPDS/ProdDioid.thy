theory ProdDioid 
  imports "BoundedDioid"
begin

\<comment> \<open>Definitions\<close>
instantiation prod :: (one, one) one begin 
  definition one_prod_def: "1 = (1,1)" instance .. 
end
instantiation prod :: (times, times) times begin
  definition mult_prod_def[simp]: "a * b \<equiv> (fst a * fst b, snd a * snd b)"
  instance ..
end
instantiation prod :: (zero, zero) zero begin 
  definition zero_prod_def: "0 = (0,0)" instance .. 
end
instantiation prod :: (plus, plus) plus begin
  definition add_prod_def: "a + b \<equiv> (fst a + fst b, snd a + snd b)"
  instance ..
end
instantiation prod :: (ord, ord) ord begin 
  \<comment> \<open>Note: This conjunctive order produces a partial order, even if the elements have a total order\<close>
  definition less_eq_prod_def: "a \<le> b = (fst a \<le> fst b \<and> snd a \<le> snd b)"
  definition less_prod_def: "a < b = (fst a \<le> fst b \<and> snd a \<le> snd b \<and> a\<noteq>b)"
  instance ..
end
instantiation prod :: (order, order) order begin 
instance proof
  fix x y z :: "('a::order \<times> 'b::order)"
  show "(x < y) = strict (\<le>) x y" 
    using less_le[of "fst x" "fst y"] less_le[of "snd x" "snd y"]
    unfolding less_prod_def less_eq_prod_def by (auto intro: prod_eqI)
  show "x \<le> x" unfolding less_eq_prod_def by simp
  show "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"
    using order_trans[of "fst x" "fst y" "fst z"] order_trans[of "snd x" "snd y" "snd z"]
    unfolding less_eq_prod_def by simp
  show "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y" 
    using order_antisym[of "fst x" "fst y"] order_antisym[of "snd x" "snd y"] 
    unfolding less_eq_prod_def by (auto intro: prod_eqI)
qed
lemma antisymp_on_less_eq: "antisymp_on (A::('a set)) (\<le>)" by simp
lemma prod_le_is_less_eq_prod:
 "(prod_le (\<le>) (\<le>)) = ((\<le>)::('a \<times> 'b) \<Rightarrow> ('a \<times> 'b) \<Rightarrow> bool)"
  unfolding prod_le_def less_eq_prod_def by fastforce
lemma strict_prod_le_is_less_prod:
  "strict (prod_le (\<le>) (\<le>)) a b = ((<)::('a::order \<times> 'b::order) \<Rightarrow> ('a \<times> 'b) \<Rightarrow> bool) a b"
  unfolding prod_le_def less_prod_def by auto
  
end
\<comment> \<open>Instance proofs\<close>
instantiation prod :: (semigroup_mult, semigroup_mult) semigroup_mult begin
  instance proof fix a b c :: "('a::semigroup_mult \<times> 'b::semigroup_mult)"
    show "a * b * c = a * (b * c)" unfolding mult_prod_def by(simp add: mult.assoc) qed
end
instantiation prod :: (monoid_mult, monoid_mult) monoid_mult begin
  instance proof fix a :: "('a::monoid_mult \<times> 'b::monoid_mult)"
      show "1 * a = a" unfolding one_prod_def mult_prod_def by simp
      show "a * 1 = a" unfolding one_prod_def mult_prod_def by simp
  qed
end
instantiation prod :: (semigroup_add, semigroup_add) semigroup_add begin
  instance proof fix a b c :: "('a::semigroup_add \<times> 'b::semigroup_add)"
    show "a + b + c = a + (b + c)" unfolding add_prod_def by(simp add: add.assoc) qed
end
instantiation prod :: (ab_semigroup_add, ab_semigroup_add) ab_semigroup_add begin
  instance proof fix a b c :: "('a::ab_semigroup_add \<times> 'b::ab_semigroup_add)"
    show "a + b = b + a" unfolding add_prod_def by(simp add: add.commute) qed
end
instantiation prod :: (comm_monoid_add, comm_monoid_add) comm_monoid_add begin
  instance proof fix a :: "('a::comm_monoid_add \<times> 'b::comm_monoid_add)"
      show "0 + a = a" unfolding zero_prod_def add_prod_def by simp
  qed
end
instantiation prod :: (idempotent_ab_semigroup_add, idempotent_ab_semigroup_add) idempotent_ab_semigroup_add begin
  instance proof fix a :: "('a::idempotent_ab_semigroup_add \<times> 'b::idempotent_ab_semigroup_add)"
    show "a + a = a" unfolding add_prod_def by simp
  qed
end
instantiation prod :: (idempotent_ab_semigroup_add_ord, idempotent_ab_semigroup_add_ord) idempotent_ab_semigroup_add_ord begin
  instance proof fix a b :: "('a::idempotent_ab_semigroup_add_ord \<times> 'b::idempotent_ab_semigroup_add_ord)"
    show "(a \<le> b) = (a + b = a)" unfolding less_eq_prod_def add_prod_def 
      by (metis fst_conv less_eq_def prod.collapse snd_conv)
    show "(a < b) = (a \<le> b \<and> a \<noteq> b)" unfolding less_prod_def less_eq_prod_def by simp
  qed
end
instantiation prod :: (semiring, semiring) semiring begin
  instance proof fix a b c :: "('a::semiring \<times> 'b::semiring)"
    show "(a + b) * c = a * c + b * c" unfolding add_prod_def mult_prod_def 
      by (simp add: semiring_class.distrib_right)
    show "a * (b + c) = a * b + a * c" unfolding add_prod_def mult_prod_def 
      by (simp add: semiring_class.distrib_left)
  qed
end
instantiation prod :: (semiring_0, semiring_0) semiring_0 begin
  instance proof fix a :: "('a::semiring_0 \<times> 'b::semiring_0)"
    show "0 * a = 0" unfolding mult_prod_def zero_prod_def by simp
    show "a * 0 = 0" unfolding mult_prod_def zero_prod_def by simp
  qed
end
instantiation prod :: (idempotent_comm_monoid_add, idempotent_comm_monoid_add) idempotent_comm_monoid_add begin instance .. end
instantiation prod :: (idempotent_comm_monoid_add_ord, idempotent_comm_monoid_add_ord) idempotent_comm_monoid_add_ord begin instance .. end
instantiation prod :: (idempotent_semiring, idempotent_semiring) idempotent_semiring begin instance .. end
instantiation prod :: (idempotent_semiring_ord, idempotent_semiring_ord) idempotent_semiring_ord begin instance .. end
instantiation prod :: (discrete_topology, discrete_topology) discrete_topology begin
instance proof
    fix A::"('a::discrete_topology \<times> 'b::discrete_topology) set"
    show "open A" unfolding open_prod_def by (auto intro!: open_discrete)
  qed
end

lemma less_not_fst_implies_snd:
  fixes f :: "(nat \<Rightarrow> ('a::bounded_idempotent_comm_monoid_add \<times> 'b::bounded_idempotent_comm_monoid_add))"
  assumes "f (Suc i) < f i"
  assumes "\<not> fst (f (Suc i)) < fst (f i)"
  shows "snd (f (Suc i)) < snd (f i)"
  using assms unfolding less_prod_def less_le
  by (simp add: prod_eq_iff[of "f (Suc i)" "f i"])

lemma antisymp_on_Sigma:
  assumes "antisymp_on A1 P1" and "antisymp_on A2 P2"
  shows "antisymp_on (A1 \<times> A2) (prod_le P1 P2)"
  using assms unfolding antisymp_on_def prod_le_def by simp

lemma finite_infinite_nat_disj:
  assumes "\<forall>i::nat. P i \<or> Q i"
      and "finite {i. P i}"
    shows "infinite {i. Q i}"
  using assms by (metis infinite_nat_iff_unbounded_le linorder_le_cases mem_Collect_eq)

fun increasing_sub_seq where
  "increasing_sub_seq P f 0 = (LEAST j. P (f j) (f (Suc j)))"
| "increasing_sub_seq P f (Suc i) = (LEAST j. j > increasing_sub_seq P f i \<and> P (f j) (f (Suc j)))"

lemma P_least_Suc_least:
  assumes "\<And>i. \<exists>j > i. P (f j) (f (Suc j))"
  shows "P (f (LEAST j. j > i \<and> P (f j) (f (Suc j)))) (f (Suc (LEAST j. j > i \<and> P (f j) (f (Suc j)))))"
  using LeastI_ex[OF assms(1)[of i]] by simp

lemma P_increasing_sub_seq_Suc:
  assumes "\<And>i::nat. \<exists>j > i. P (f j) (f (Suc j))"
  shows "P (f (increasing_sub_seq P f i)) (f (Suc (increasing_sub_seq P f i)))"
proof (cases "i = 0")
  case True
  from assms(1) have "\<exists>j. P (f j) (f (Suc j))" by blast
  then have "P (f (LEAST j. P (f j) (f (Suc j)))) (f (Suc (LEAST j. P (f j) (f (Suc j)))))" 
    using LeastI_ex by meson
  then show ?thesis using True by simp
next
  case False
  then obtain h where h_def:"Suc h = i"
    using not0_implies_Suc by blast
  have "P (f (increasing_sub_seq P f (Suc h))) (f (Suc (increasing_sub_seq P f (Suc h))))"
    using P_least_Suc_least[of P f "increasing_sub_seq P f h", OF assms(1)]
    by simp
  then show ?thesis using h_def by blast
qed

lemma eq_in_between:
  assumes "i < a"
  assumes "\<forall>b. i \<le> b \<and> b < a \<longrightarrow> (f b) = (f (Suc b))"
  shows "f i = f a"
  using assms
  apply (induct "a - i" rule: diff_induct, linarith, fast)
  subgoal for x y
    apply simp
    by (metis Suc_diff_le Suc_mono le_SucI le_eq_less_or_eq less_antisym old.nat.inject)
  done

lemma Suc_i_eq_least_j:
  assumes "\<And>i. \<exists>j > i. P (f j) (f (Suc j))"
  assumes "\<And>i. \<not> P (f i) (f (Suc i)) \<Longrightarrow> (f i) = (f (Suc i))"
  shows "(f (Suc i)) = (f (LEAST j. j > i \<and> P (f j) (f (Suc j))))"
proof (rule LeastI2_wellorder_ex[OF assms(1)[of i]])
  fix a
  assume "i < a \<and> P (f a) (f (Suc a))" "\<forall>b. i < b \<and> P (f b) (f (Suc b)) \<longrightarrow> a \<le> b"
  then have ia:"i < a" and Pa:"P (f a) (f (Suc a))" and "\<forall>b. i < b \<and> P (f b) (f (Suc b)) \<longrightarrow> a \<le> b" by auto
  then have "\<forall>b. i < b \<and> b < a \<longrightarrow> \<not> P (f b) (f (Suc b))" by fastforce
  then have eq_between: "\<forall>b. i < b \<and> b < a \<longrightarrow> (f b) = (f (Suc b))" using assms(2) by presburger
  then show "f (Suc i) = f a" proof (cases "Suc i = a")
    case True
    then show ?thesis by blast
  next
    case False
    then have Suc_ia: "Suc i < a" using ia by fastforce
    show ?thesis using eq_in_between[OF Suc_ia, of f] eq_between by force
  qed
qed

lemma infinitely_often_implies_subsequence_always:
  fixes f :: "nat \<Rightarrow> 'a"
  assumes "infinite {i. P (f i) (f (Suc i))}"
  assumes "\<And>i. \<not> P (f i) (f (Suc i)) \<Longrightarrow> (f i) = (f (Suc i))"
  shows "\<exists>\<phi>::nat\<Rightarrow>nat. \<forall>i. P (f (\<phi> i)) (f (\<phi> (Suc i)))"
  using assms
proof -
  from assms(1) have Pj:"\<And>i. \<exists>j > i. P (f j) (f (Suc j))"
    by (simp add: infinite_nat_iff_unbounded)
  show ?thesis 
    apply (rule exI[of _ "increasing_sub_seq P f"])
    apply safe
    subgoal for i
      using Suc_i_eq_least_j[of P f "(increasing_sub_seq P f i)"] Pj assms(2) P_increasing_sub_seq_Suc[of P f i, OF Pj]
      by fastforce
    done
qed

lemma PnotStrictP:
  assumes "antisymp_on A P" "x \<in> A" "y \<in> A"
          "P x y" "\<not> (strict P) x y"
  shows   "x = y"
  using assms unfolding antisymp_on_def by blast

lemma wfp_on_Sigma:
  assumes "antisymp_on A1 P1" and "antisymp_on A2 P2"
  assumes "wfp_on (strict P1) A1" and "wfp_on (strict P2) A2"
  shows "wfp_on (strict (prod_le P1 P2)) (A1 \<times> A2)" (is "wfp_on ?P ?A")
proof -
  from assms(3)[unfolded wfp_on_def,simplified] 
  have "\<forall>f. \<exists>i. f i \<in> A1 \<longrightarrow> P1 (f (Suc i)) (f i) \<longrightarrow> P1 (f i) (f (Suc i))" by blast
  then have wfp1:"\<forall>f. \<exists>i. f i \<in> A1 \<longrightarrow> f (Suc i) \<in> A1 \<longrightarrow> P1 (f (Suc i)) (f i) \<longrightarrow> (f i) = (f (Suc i))" 
    using assms(1) unfolding antisymp_on_def by blast
  from assms(4)[unfolded wfp_on_def,simplified]
  have "\<forall>f. \<exists>i. P2 (f (Suc i)) (f i) \<longrightarrow> f i \<in> A2 \<longrightarrow> P2 (f i) (f (Suc i))" by blast
  then have wfp2:"\<forall>f. \<exists>i. f i \<in> A2 \<longrightarrow> f (Suc i) \<in> A2 \<longrightarrow> P2 (f (Suc i)) (f i) \<longrightarrow> (f i) = (f (Suc i))" 
    using assms(2) unfolding antisymp_on_def by blast
  show ?thesis
  proof (rule ccontr)
    assume "\<not> wfp_on ?P ?A"
    then obtain f where f: "\<forall>i. f i \<in> ?A" and infinite_descending: "\<forall>i. ?P (f (Suc i)) (f i)"
      by (auto simp: wfp_on_def)
    let ?P1 = "\<lambda>x y. P1 (fst y) (fst x)"
    let ?P2 = "\<lambda>x y. P2 (snd y) (snd x)"
    let ?sP1 = "\<lambda>x y. (strict P1) (fst y) (fst x)"
    let ?sP2 = "\<lambda>x y. (strict P2) (snd y) (snd x)"
    let ?f1 = "\<lambda>i. fst (f i)"
    let ?f2 = "\<lambda>i. snd (f i)"
    from infinite_descending have P1: "\<forall>i. ?P1 (f i) (f (Suc i))" and 
                                  P2: "\<forall>i. ?P2 (f i) (f (Suc i))" and 
                                  sP1P2: "\<forall>i. ?sP1 (f i) (f (Suc i)) \<or> ?sP2 (f i) (f (Suc i))"
      unfolding prod_le_def 
        apply -
      by (erule Meson.all_forward, force)+
    then have "\<forall>i. (strict P1) (?f1 (Suc i)) (?f1 i) \<or> (strict P2) (?f2 (Suc i)) (?f2 i)"
      by simp
    have "\<And>i. fst (f i) \<in> A1" using f
      by (metis SigmaD1 surjective_pairing)
    then have notStrictEq1: "\<And>i. \<not> ?sP1 (f i) (f (Suc i)) \<Longrightarrow> fst (f i) = fst (f (Suc i))"
      using PnotStrictP[OF assms(1)] P1 by simp
    have "\<And>i. snd (f i) \<in> A2" using f
      by (metis SigmaD2 surjective_pairing)
    then have notStrictEq2: "\<And>i. \<not> ?sP2 (f i) (f (Suc i)) \<Longrightarrow> snd (f i) =  snd (f (Suc i))"
      using PnotStrictP[OF assms(2)] P2 by simp
    have "\<exists>\<phi>. (\<forall>i. ?sP1 (f (\<phi> i)) (f (\<phi> (Suc i)))) \<or> (\<forall>i. ?sP2 (f (\<phi> i)) (f (\<phi> (Suc i))))"
    proof (cases "finite {i. ?sP1 (f i) (f (Suc i))}")
      case True
      then have "infinite {i. ?sP2 (f i) (f (Suc i))}" 
        using sP1P2 finite_infinite_nat_disj by presburger
      then show ?thesis using infinitely_often_implies_subsequence_always[of "\<lambda>x y. (strict P2) y x" ?f2, OF _ notStrictEq2]
        by blast
    next
      case False
      then show ?thesis using infinitely_often_implies_subsequence_always[of "\<lambda>x y. (strict P1) y x" ?f1, OF _ notStrictEq1]
        by blast
    qed
    then obtain \<phi> where \<phi>def: "(\<forall>i. ?sP1 (f (\<phi> i)) (f (\<phi> (Suc i)))) \<or> (\<forall>i. ?sP2 (f (\<phi> i)) (f (\<phi> (Suc i))))" 
      by blast
    let ?f' = "\<lambda>i. f (\<phi> i)"
    have "\<exists>f'. (\<forall>i. f' i \<in> ?A) \<and> ((\<forall>i. ?sP1 (f' i) (f' (Suc i))) \<or> (\<forall>i. ?sP2 (f' i) (f' (Suc i))))"
      by (rule exI[of _ ?f']) (simp add: f \<phi>def)
    then obtain f' where 
        f': "\<forall>i. f' i \<in> ?A" and 
        A:"(\<forall>i. ?sP1 (f' i) (f' (Suc i))) \<or> (\<forall>i. ?sP2 (f' i) (f' (Suc i)))" by blast
    let ?f1' = "\<lambda>i. fst (f' i)"
    let ?f2' = "\<lambda>i. snd (f' i)"
    from f' have fst': "\<forall>i. ?f1' i \<in> A1"
      by (simp add: mem_Times_iff) 
    then have B: "\<exists>i. P1 (?f1' (Suc i)) (?f1' i) \<longrightarrow> ?f1' i = ?f1' (Suc i)" 
      using wfp1 by meson
    from f' have snd': "\<forall>i. ?f2' i \<in> A2"
      by (simp add: mem_Times_iff)
    then have C: "\<exists>i. P2 (?f2' (Suc i)) (?f2' i) \<longrightarrow> ?f2' i = ?f2' (Suc i)"
      using wfp2 by meson
    from A B C show "False"
      by metis
  qed
qed

instantiation prod :: (wfp, wfp) wfp begin
  lemma less_eq_exists_symmetric:
    fixes f :: "(nat \<Rightarrow> ('a::wfp \<times> 'b::wfp))"
    shows "\<exists>i. f (Suc i) \<le> f i \<longrightarrow> f i \<le> f (Suc i)"
    using wfp_on_Sigma[OF antisymp_on_less_eq antisymp_on_less_eq wfp_on_class wfp_on_class, 
                       of UNIV UNIV, unfolded wfp_on_def, simplified]
          prod_le_is_less_eq_prod
    by metis
  instance proof
    show "\<nexists>f::(nat \<Rightarrow> ('a \<times> 'b)). \<forall>i. (f i) > (f (Suc i))" 
    proof (rule ccontr, simp)
      assume "\<exists>f::(nat \<Rightarrow> ('a \<times> 'b)). \<forall>i. f (Suc i) < f i"
      then obtain f :: "nat \<Rightarrow> ('a \<times> 'b)" where infinite_descending: "\<forall>i. f (Suc i) < f i" by auto
      from less_eq_exists_symmetric[of f] infinite_descending show "False"
        unfolding less_le using order_antisym by auto
    qed
  qed
end
instantiation prod :: (bounded_idempotent_comm_monoid_add, bounded_idempotent_comm_monoid_add) bounded_idempotent_comm_monoid_add begin instance .. end
instantiation prod :: (bounded_idempotent_semiring, bounded_idempotent_semiring) bounded_idempotent_semiring begin instance .. end

end