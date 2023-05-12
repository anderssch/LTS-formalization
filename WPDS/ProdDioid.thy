theory ProdDioid 
  imports "BoundedDioid"
begin

\<comment> \<open>Definitions\<close>
instantiation prod :: (one, one) one begin 
  definition one_prod_def: "1 = (1,1)" instance .. 
end
instantiation prod :: (times, times) times begin
  definition mult_prod_def: "a * b \<equiv> (fst a * fst b, snd a * snd b)"
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
instantiation prod :: (idempotent_semiring, idempotent_semiring) idempotent_semiring begin instance .. end
instantiation prod :: (idempotent_semiring_ord, idempotent_semiring_ord) idempotent_semiring_ord begin instance .. end
instantiation prod :: (discrete_topology, discrete_topology) discrete_topology begin
instance proof
    fix A::"('a::discrete_topology \<times> 'b::discrete_topology) set"
    show "open A" unfolding open_prod_def by (auto intro!: open_discrete)
  qed
end
instantiation prod :: (bounded_idempotent_comm_monoid_add, bounded_idempotent_comm_monoid_add) bounded_idempotent_comm_monoid_add begin
  instance proof
    show "almost_full_on (\<le>) (UNIV::('a\<times>'b) set)"
      using almost_full_on_Sigma[OF no_infinite_decending_chains no_infinite_decending_chains]
      unfolding prod_le_def less_eq_prod_def by (simp add: case_prod_beta')
  qed
end
instantiation prod :: (bounded_idempotent_semiring, bounded_idempotent_semiring) bounded_idempotent_semiring begin instance .. end

end