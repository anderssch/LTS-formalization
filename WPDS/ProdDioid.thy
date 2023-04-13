theory ProdDioid 
  imports "Kleene_Algebra.Dioid"
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
instantiation prod :: (monoid_add, monoid_add) monoid_add begin
  instance proof fix a :: "('a::monoid_add \<times> 'b::monoid_add)"
      show "0 + a = a" unfolding zero_prod_def add_prod_def by simp
      show "a + 0 = a" unfolding zero_prod_def add_prod_def by simp
  qed
end
instantiation prod :: (ab_semigroup_add, ab_semigroup_add) ab_semigroup_add begin
  instance proof fix a b c :: "('a::ab_semigroup_add \<times> 'b::ab_semigroup_add)"
    show "a + b = b + a" unfolding add_prod_def by(simp add: add.commute) qed
end
instantiation prod :: (plus_ord, plus_ord) plus_ord begin
instance proof fix a b :: "('a::plus_ord \<times> 'b::plus_ord)"
    show "(a \<le> b) = (a + b = b)" unfolding less_eq_prod_def add_prod_def 
      by (metis fst_conv less_eq_def prod.collapse snd_conv)
    show "(a < b) = (a \<le> b \<and> a \<noteq> b)" unfolding less_prod_def less_eq_prod_def by simp
  qed
end
instantiation prod :: (order, order) order begin
instance proof fix a b c :: "('a::order \<times> 'b::order)"
    show "(a < b) = (a \<le> b \<and> \<not> b \<le> a)" unfolding less_prod_def less_eq_prod_def by (meson antisym prod.expand)
    show "a \<le> a" unfolding less_eq_prod_def by simp
    show "a \<le> b \<Longrightarrow> b \<le> c \<Longrightarrow> a \<le> c" unfolding less_eq_prod_def by (metis dual_order.trans)
    show "a \<le> b \<Longrightarrow> b \<le> a \<Longrightarrow> a = b" unfolding less_eq_prod_def by (simp add: order_antisym_conv prod.expand)
  qed
end
instantiation prod :: (semiring, semiring) semiring begin
  instance proof fix a b c :: "('a::semiring \<times> 'b::semiring)"
    show "(a + b) * c = a * c + b * c" unfolding add_prod_def mult_prod_def by simp
    show "a * (b + c) = a * b + a * c" unfolding add_prod_def mult_prod_def 
      by (simp add: semiring_class.distrib_left)
  qed
end
instantiation prod :: (dioid, dioid) dioid  begin
  instance proof fix a b :: "('a::dioid \<times> 'b::dioid)"
    show "a + a = a" unfolding add_prod_def by simp
  qed
end
instantiation prod :: (dioid_one_zero, dioid_one_zero) dioid_one_zero begin
  instance proof
    fix x :: "('a::dioid_one_zero \<times> 'b::dioid_one_zero)"
    show "1 * x = x" unfolding one_prod_def mult_prod_def by simp
    show "x * 1 = x" unfolding one_prod_def mult_prod_def by simp
    show "0 + x = x" unfolding zero_prod_def add_prod_def by simp
    show "0 * x = 0" unfolding zero_prod_def mult_prod_def by simp
    show "x * 0 = 0" unfolding zero_prod_def mult_prod_def by simp
  qed
end

end