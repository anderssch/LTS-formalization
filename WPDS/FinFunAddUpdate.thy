theory FinFunAddUpdate
  imports "FinFunWellFounded"
begin

abbreviation finfun_add_update :: "('a \<Rightarrow>f 'b::idempotent_ab_semigroup_add) \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> ('a \<Rightarrow>f 'b)" ("_'(_ $+= _')" [1000,0,0] 1000) where
  "finfun_add_update f a b \<equiv> f(a $:= (f$a) + b)"

lemma finfun_add_update_apply_same: "f(a $+= b) $ a = f $ a + b" by simp
lemma finfun_add_update_apply_other: "a \<noteq> x \<Longrightarrow> f(x $+= b) $ a = f $ a" by simp


lemma finfun_add_update_same_mono:
  fixes f g :: "('a \<Rightarrow>f 'b::idempotent_comm_monoid_add_ord)"
  assumes "f \<le> g"
  assumes "b \<le> c"
  shows "f(a $+= b) \<le> g(a $+= c)"
  using assms unfolding less_eq_finfun_def
  by (metis finfun_upd_apply_other finfun_upd_apply_same meet.inf_mono)


lemma finfun_add_update_to_zero:
  fixes f :: "'a \<Rightarrow>f 'b::idempotent_comm_monoid_add"
  shows "f(a $+= b) = f + (K$0)(a $:= b)"
  apply (rule finfun_ext)
  subgoal for x
    by (cases "a = x", simp_all)
  done

lemma finfun_add_update_less_eq:
  fixes f :: "('a \<Rightarrow>f 'b::idempotent_comm_monoid_add_ord)"
  shows "f(a $+= b) \<le> f" 
  unfolding finfun_add_update_to_zero by simp

lemma finfun_add_update_less:
  fixes f :: "('a \<Rightarrow>f 'b::idempotent_comm_monoid_add_ord)"
  shows "f $ a + b \<noteq> f $ a \<Longrightarrow> f(a $+= b) < f"
  by (metis finfun_add_update_less_eq finfun_upd_apply_same order_neq_le_trans)

lemma add_finfun_add_update: "(f + g)(a $+= b) = f + g(a $+= b)"
  apply (rule finfun_ext)
  subgoal for x
    by (cases "a = x", simp_all add: ac_simps)
  done

lemma finfun_add_update_commute: "f(a $+= b)(a' $+= b') = f(a' $+= b')(a $+= b)"
  apply (cases "a' = a")
   apply (simp add: comp_def add.commute add.left_commute)
  using FinFun.finfun_comp_aux.upd_commute by fastforce

lemma finfun_add_update_idem: "f(a $+= b)(a $+= b) = f(a $+= b)"
  by (simp add: add.commute add_left_idem)

lemma add_finfun_add_update_idem: "f + f(a $+= b) = f(a $+= b)"
  by (metis add_finfun_add_update add_idem)

lemma finfun_different_add_update_nleq_apply_neq:
  fixes f :: "'a \<Rightarrow>f 'b::idempotent_comm_monoid_add_ord"
  assumes "c \<le> y"
  assumes "\<not> f(a $+= b) \<le> f(x $+= y)" 
  shows "f(a $+= b) $ x + c \<noteq> f(a $+= b) $ x"
  using assms[unfolded less_eq_finfun_def]
  apply safe
  subgoal for d
    using neq_mono[of c y "f $ a + b"] neq_mono[of c y "f $ x"]
    unfolding idempotent_ab_semigroup_add_ord_class.less_eq_def
    apply (cases "a = x")
     apply (cases "d = a", simp add: add.commute add.left_commute, simp)
    apply (cases "d = x", simp add: add.commute add.left_commute)
    by (cases "d = a", simp add: add.commute add.left_commute, simp)
  done


lemma finfun_add_update_update_less_eq:
  fixes f :: "'a \<Rightarrow>f 'b::idempotent_comm_monoid_add_ord"
  assumes "b \<le> c"
  shows "f(x $+= y)(a $+= b) \<le> f(a $+= c)"
  unfolding less_eq_finfun_def
  apply (rule allI)
  subgoal for a'
    using assms unfolding idempotent_ab_semigroup_add_ord_class.less_eq_def
    apply (cases "x = a")
     apply (cases "a' = x", simp add: add.assoc add.left_commute, simp)
    apply (cases "a' = a", simp add: add.assoc add.left_commute)
    by (cases "a' = x", simp add: add.assoc add.left_commute add.commute, simp)
  done

lemma finfun_add_update_neq: "f \<noteq> f(a $+= b) \<Longrightarrow> f $ a \<noteq> f $ a + b" by fastforce
lemma add_finfun_add_update_neq: "f + g \<noteq> f + g(a $+= b) \<Longrightarrow> f $ a + g $ a \<noteq> f $ a + g $ a + b"
  unfolding add_finfun_add_update[symmetric] using finfun_add_update_neq[of "f + g"] by simp

lemma finfun_less_eq_spec: "f \<le> g \<Longrightarrow> f $ a \<le> g $ a"
  unfolding less_eq_finfun_def by simp


end