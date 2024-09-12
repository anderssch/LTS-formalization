theory FinFunAddUpdate
  imports "FinFunWellFounded" "Set_More"
begin

abbreviation finfun_add_update :: "('a \<Rightarrow>f 'b::idempotent_ab_semigroup_add) \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> ('a \<Rightarrow>f 'b)" ("_'(_ $+= _')" [1000,0,0] 1000) where
  "finfun_add_update f a b \<equiv> f(a $:= (f$a) + b)"

lemma finfun_add_update_apply_same: 
  "f(a $+= b) $ a = f $ a + b" by simp

lemma finfun_add_update_apply_other: 
  "a \<noteq> x \<Longrightarrow> f(x $+= b) $ a = f $ a" by simp

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

\<comment> \<open>For the executable pre-star, the saturation rule computes a set of new transition weights, 
    that are updated using the dioid's plus operator to combine with the existing value.\<close>
definition finfun_update_plus_pair :: "('a \<times> 'b) \<Rightarrow> ('a \<Rightarrow>f 'b::idempotent_ab_semigroup_add) \<Rightarrow> ('a \<Rightarrow>f 'b)" where
  "finfun_update_plus_pair p f = f((fst p) $+= (snd p))"

definition update_wts :: "('a \<Rightarrow>f 'b::idempotent_comm_monoid_add) \<Rightarrow> ('a \<times> 'b) set \<Rightarrow> ('a \<Rightarrow>f 'b)" where
  "update_wts = Finite_Set.fold finfun_update_plus_pair"

lemma finfun_update_plus_pair_apply: "finfun_update_plus_pair (a,b) f $ a = f $ a + b"
  unfolding finfun_update_plus_pair_def using finfun_add_update_apply_same by force

lemma finfun_update_plus_pair_apply_other: "a \<noteq> x \<Longrightarrow> finfun_update_plus_pair (x,b) f $ a = f $ a"
  unfolding finfun_update_plus_pair_def using finfun_add_update_apply_other by fastforce

lemma finfun_update_plus_pair_idem: "comp_fun_idem finfun_update_plus_pair"
  apply standard
  subgoal for x y
    unfolding finfun_update_plus_pair_def using finfun_add_update_commute by fastforce
  subgoal for x
    unfolding finfun_update_plus_pair_def using finfun_add_update_idem by fastforce
  done

lemma finfun_update_plus_pair_idem_on_UNIV: "comp_fun_idem_on UNIV finfun_update_plus_pair"
  using finfun_update_plus_pair_idem by (simp add: comp_fun_idem_def')

lemma folding_idem_finfun_update_plus_pair: "folding_idem finfun_update_plus_pair"
  unfolding finfun_update_plus_pair_def
  apply standard
  using finfun_add_update_commute finfun_add_update_idem by fastforce+

lemma (in folding_idem) fold_code:
  shows "Finite_Set.fold f z (set A) = foldr f A z"
  unfolding eq_fold[symmetric]
proof (induct A)
  case Nil
  then show ?case by simp
next
  case (Cons a X)
  then show ?case by fastforce
qed

lemma update_wts_code[code]: "update_wts f (set A) = foldr finfun_update_plus_pair A f"
  using folding_idem.fold_code[OF folding_idem_finfun_update_plus_pair, of f A]
  unfolding update_wts_def by blast

lemma update_wts_insert:
  assumes "finite S"
  shows "update_wts f (insert x S) = finfun_update_plus_pair x (update_wts f S)"
  unfolding update_wts_def
  using assms comp_fun_idem_on.fold_insert_idem[OF finfun_update_plus_pair_idem_on_UNIV]
  by blast

lemma sum_insert_fresh:
  fixes S::"('a \<times> 'b::idempotent_comm_monoid_add) set"
  assumes "finite S"
      and "(x,y) \<notin> S"
    shows "\<Sum> {b. (x, b) \<in> S} + y = \<Sum> {b. (x, b) \<in> insert (x,y) S}"
proof -
  have "finite {b. (x, b) \<in> S}" using assms(1) by (induct S, auto)
  moreover have "y \<notin> {b. (x, b) \<in> S}" using assms(2) by simp
  ultimately have "\<Sum> {b. (x, b) \<in> S} + y = \<Sum> (insert y {b. (x, b) \<in> S})" 
    by (simp add: add.commute)
  moreover have "{b. (x, b) \<in> insert (x,y) S} = insert y {b. (x, b) \<in> S}" by blast
  ultimately show ?thesis by simp
qed

lemma finfun_update_plus_pair_insert:
  fixes S::"('a \<times> 'b::idempotent_comm_monoid_add) set"
  assumes "finite S"          
  assumes "(x,y) \<notin> S"
  assumes "f' $ a = f $ a + \<Sum> {b. (a, b) \<in> S}"
  shows "finfun_update_plus_pair (x,y) f' $ a = f $ a + \<Sum> {b. (a, b) \<in> insert (x,y) S}"
proof (cases "a = x")
  case True
  then have "finfun_update_plus_pair (x,y) f' $ a = f $ x + \<Sum> {b. (x, b) \<in> S} + y"
    using finfun_update_plus_pair_apply[of x y f'] assms(3) by simp
  moreover have "f $ a + \<Sum> {b. (x, b) \<in> S} + y = f $ a + \<Sum> {b. (x, b) \<in> insert (x,y) S}" 
    using sum_insert_fresh[OF assms(1,2)] by (simp add: ab_semigroup_add_class.add_ac(1))
  ultimately show ?thesis using \<open>a = x\<close> by simp
next
  case False
  then show ?thesis using assms(3) finfun_update_plus_pair_apply_other[OF \<open>a \<noteq> x\<close>, of y f'] by simp
qed

lemma update_wts_step:
  assumes "finite S"
  assumes "x \<notin> S"
  assumes "update_wts f S $ a = f $ a + \<Sum> {b. (a, b) \<in> S}" 
  shows   "update_wts f (insert x S) $ a = f $ a + \<Sum> {b. (a, b) \<in> insert x S}"
  using update_wts_insert[OF assms(1)] assms(2,3) 
        finfun_update_plus_pair_insert[OF assms(1), of "fst x" "snd x"] by simp

theorem update_wts_sum:
  assumes "finite S"
  shows "(update_wts f S) $ a = f $ a + \<Sum>{b. (a,b) \<in> S}"
  using assms
  apply (induct S, simp add: update_wts_def)
  subgoal for x F
    using update_wts_step[of F x] by auto
  done

lemma update_wts_empty: "update_wts f {} = f"
  by (rule finfun_ext) (simp add: update_wts_sum[of "{}" f])

lemma update_wts_less_eq:
  fixes S::"('a \<times> 'b::idempotent_comm_monoid_add_ord) set"
  assumes "finite S"
  shows "(update_wts f S) \<le> f"
  unfolding less_eq_finfun_def using update_wts_sum[OF assms, of f] by simp

lemma sum_snd_insert: 
  fixes S::"('a \<times> 'b::idempotent_comm_monoid_add) set"
  assumes "finite S"
  shows "\<Sum> {b. b = y \<or> (x, b) \<in> S} = y + \<Sum> {b. (x, b) \<in> S}"
proof -
  have "{b. (x, b) \<in> S} = snd ` (S \<inter> ({x} \<times> UNIV))" by force
  then have "finite {b. (x, b) \<in> S}" using assms by simp
  moreover have "insert y {b. (x, b) \<in> S} = {b. b = y \<or> (x, b) \<in> S}" by fast
  ultimately show "\<Sum> {b. b = y \<or> (x, b) \<in> S} = y + \<Sum> {b. (x, b) \<in> S}"
    using idem_sum_insert[of "{b. (x, b) \<in> S}" y] by argo
qed

lemma update_wts_insert_unfold:
  fixes S::"('a \<times> 'b::idempotent_comm_monoid_add) set"
  assumes "finite S"
  shows "update_wts f (insert (x,y) S) = update_wts f(x $+= y) S"
  apply (rule finfun_ext)
  subgoal for a
    unfolding update_wts_sum[OF assms, of "f(x $+= y)" a] 
      update_wts_sum[of "(insert (x,y) S)" f a, simplified, OF assms]
  proof (cases "a = x")
    case True
    show "f $ a + \<Sum> {b. a = x \<and> b = y \<or> (a, b) \<in> S} = f(x $+= y) $ a + \<Sum> {b. (a, b) \<in> S}" 
      using sum_snd_insert[OF assms] True by (simp add: ac_simps(1))
  next
    case False
    then show "f $ a + \<Sum> {b. a = x \<and> b = y \<or> (a, b) \<in> S} = f(x $+= y) $ a + \<Sum> {b. (a, b) \<in> S}"
      by simp
  qed 
  done

lemma update_wts_insert_absorb:
  fixes S::"('a \<times> 'b::idempotent_comm_monoid_add) set"
  assumes "finite S"
  assumes "f $ x = f $ x + y"
  shows "update_wts f (insert (x,y) S) = update_wts f S"
  using update_wts_insert_unfold[OF assms(1)] assms(2) by simp

lemma sum_snd_with_zeros:
  fixes A B :: "('a \<times> 'b::idempotent_comm_monoid_add) set"
  assumes "A \<subseteq> B"
      and "B \<subseteq> A \<union> {u. \<exists>q. u = (q, 0)}"
      and "finite A"
    shows "\<Sum> {b. (a, b) \<in> A} = \<Sum> {b. (a, b) \<in> B}"
proof -
  obtain C where C:"C \<subseteq> {u. \<exists>q. u = (q, 0)}" and BAC:"B = A \<union> C" 
    using exists_set_between[OF assms(1,2)] by blast
  then have "\<Sum> {b. (a, b) \<in> A} = \<Sum> {b. (a, b) \<in> A \<union> C}"
  proof (cases "(a,0) \<in> C")
    case True
    then have "{b. (a, b) \<in> ({(a, 0)} \<union> A)} = {b. (a, b) \<in> A \<union> C}"
      using C by blast
    moreover have "\<Sum> {b. (a, b) \<in> A} = \<Sum> {b. (a, b) \<in> ({(a, 0)} \<union> A)}"
      using assms sum_snd_insert[OF assms(3), of 0 a] by simp
    ultimately show ?thesis by argo
  next
    case False
    then have "{b. (a, b) \<in> A} = {b. (a, b) \<in> A \<union> C}"
      using C by blast
    then show ?thesis by argo
  qed
  then show ?thesis using BAC by presburger
qed

lemma update_wts_sum_finfun:
  assumes "finite S"
  shows "update_wts f S = f + \<Sum>{f(a $+= b) |a b. (a,b) \<in> S}"
proof (rule finfun_ext)
  fix a
  have f0:"finite {b. (a, b) \<in> S}" 
    using finite_f_P_on_set[OF assms, of "\<lambda>ab. snd ab" "\<lambda>ab. fst ab = a"] by simp
  have f1:"finite {f(a $+= b) |b. (a, b) \<in> S}" 
    using finite_f_P_on_set[OF assms, of "\<lambda>ab. f(a $+= snd ab)" "\<lambda>ab. fst ab = a"] by simp
  have f2: "finite {f(a $+= b) |a b. (a, b) \<in> S}" 
    using finite_f_P_on_set[OF assms, of "\<lambda>ab. f(fst ab $+= snd ab)" "\<lambda>ab. True"] by simp
  have f3:"finite {f(aa $+= b) $ a |aa b. (aa, b) \<in> S \<and> aa \<noteq> a}" 
    using finite_f_P_on_set[OF assms, of "\<lambda>ab. f(fst ab $+= snd ab) $ a" "\<lambda>ab. fst ab \<noteq> a"]
    by (rule back_subst[of finite]) auto
  have f4:"finite {f(aa $+= b) |aa b. (aa, b) \<in> S \<and> aa \<noteq> a}"
    using finite_f_P_on_set[OF assms, of "\<lambda>ab. f(fst ab $+= snd ab)" "\<lambda>ab. fst ab \<noteq> a"]
    by (rule back_subst[of finite]) auto

  have "update_wts f S $ a = f $ a + \<Sum> {f(a $+= b) |b. (a, b) \<in> S} $ a"
    unfolding update_wts_sum[OF assms, of f a] idem_sum_distrib'[OF f0, of "f $ a"] sum_finfun_apply_f_P[OF f1]
    by fastforce
  moreover have "... = f $ a + \<Sum> {f(aa $+= b) |aa b. (aa, b) \<in> S \<and> aa \<noteq> a} $ a + \<Sum> {f(a $+= b) |b. (a, b) \<in> S} $ a"
  proof (cases "{f(aa $+= b) $ a |aa b. (aa, b) \<in> S \<and> aa \<noteq> a} = {}")
    case True
    show ?thesis
      unfolding sum_finfun_apply_f_P[of "\<lambda>ab. f(fst ab $+= snd ab)" "\<lambda>ab. ab\<in>S \<and> fst ab \<noteq> a" a, simplified, OF f4] True
      by auto
  next
    case False
    have "\<Sum> {f(aa $+= b) $ a |aa b. (aa, b) \<in> S \<and> aa \<noteq> a} = \<Sum> {f $ a |aa b. (aa, b) \<in> S \<and> aa \<noteq> a}"
      by (rule arg_cong[of _ _ \<Sum>]) force
    then show ?thesis 
      unfolding sum_finfun_apply_f_P[of "\<lambda>ab. f(fst ab $+= snd ab)" "\<lambda>ab. ab\<in>S \<and> fst ab \<noteq> a" a, simplified, OF f4]
      using idem_sum_const'[OF f3 False, of "f $ a"] by auto
  qed
  moreover have "... = f $ a + \<Sum> {f(a $+= b) |a b. (a, b) \<in> S} $ a"
    unfolding sum_split_f_P[of "\<lambda>ab. f(fst ab $+= snd ab)" "\<lambda>ab. ab\<in>S" "\<lambda>ab. fst ab \<noteq> a", simplified, OF f2]
    by (simp add: add.assoc)
  ultimately show "update_wts f S $ a = (f + \<Sum> {f(a $+= b) |a b. (a, b) \<in> S}) $ a"
    by fastforce
qed

lemma update_wts_apply_is_1_if_member:
  assumes "finite ts"
  assumes "t' \<in> ts"
  shows "update_wts (K$ 0) {(t, 1) |t. t \<in> ts} $ t' = (1 ::'weight::bounded_dioid)"
  using assms
proof (induction rule: finite_induct)
  case empty
  then show ?case
    by auto
next
  case (insert t'' F)
  show ?case
  proof (cases "t' = t''")
    assume a: "t' = t''"
    have "finfun_update_plus_pair (t'', 1) (update_wts (K$ 0) {(t, 1) |t. t \<in> F}) $ t' = (1 ::'weight) + ((update_wts (K$ 0) {(t, 1) |t. t \<in> F}) $ t')"
      by (simp add: a add.commute finfun_update_plus_pair_apply)
    then have "finfun_update_plus_pair (t'', 1) (update_wts (K$ 0) {(t, 1) |t. t \<in> F}) $ t' = (1 ::'weight)"
      by (smt Collect_cong Groups.add_0 a empty_iff finfun_const_apply finite.emptyI fold_infinite insert.hyps(2) mem_Collect_eq prod.inject update_wts_def update_wts_empty update_wts_sum)
    then have "update_wts (K$ 0) (insert (t'',1) {(t, 1) |t. t \<in> F}) $ t' = (1 ::'weight)"
      by (simp add: insert.hyps(1) update_wts_insert)
    then show "update_wts (K$ 0) {(t, 1) |t. t \<in> insert t'' F} $ t' = (1 ::'weight)"
      by (smt (verit, del_insts) Collect_cong insert_Collect insert_iff)
  next
    assume a: "t' \<noteq> t''"
    then have "t' \<in> F"
      using insert by auto
    then have "update_wts (K$ 0) {(t, 1) |t. t \<in> F} $ t' = (1 ::'weight)"
      using insert a by metis
    then have "finfun_update_plus_pair (t'', 1) (update_wts (K$ 0) {(t, 1) |t. t \<in> F}) $ t' = (1 ::'weight)"
      by (simp add: a finfun_update_plus_pair_apply_other)
    then have "update_wts (K$ 0) (insert (t'',1) {(t, 1) |t. t \<in> F}) $ t' = (1 ::'weight)"
      by (metis (no_types, lifting) insert(3) \<open>t' \<in> F\<close> finite_insert fold_infinite update_wts_def update_wts_insert)
    then show "update_wts (K$ 0) {(t, 1) |t. t \<in> insert t'' F} $ t' = (1 ::'weight)"
      by (smt (verit, ccfv_SIG) Collect_cong insert_Collect insert_iff)
  qed
qed

lemma update_wts_apply_is_0_if_not_member:
  fixes ts :: "'transition set"
  assumes "finite ts"
  assumes "t' \<notin> ts"
  shows "update_wts (K$ 0) {(t, 1) |t. t \<in> ts} $ t' = (0 ::'weight::bounded_dioid)"
  using assms
proof (induction rule: finite_induct)
  case empty
  then show ?case
    by (simp add: update_wts_empty)
next
  case (insert t'' F)
  show ?case
  proof (cases "t' = t''")
    assume a: "t' = t''"
    then show "update_wts (K$ 0) {(t, 1) |t. t \<in> insert t'' F} $ t' = (0 ::'weight)"
      using insert.prems by force
  next
    assume a: "t' \<noteq> t''"
    then have "update_wts (K$ 0) {(t, 1) |t. t \<in> F} $ t' = (0 ::'weight)"
      using insert a by blast
    then have "finfun_update_plus_pair (t'', 1) (update_wts (K$ 0) {(t, 1) |t. t \<in> F}) $ t' = (0 ::'weight)"
      by (simp add: a finfun_update_plus_pair_apply_other)
    then have "update_wts (K$ 0) (insert (t'',1) {(t, 1) |t. t \<in> F}) $ t' = (0 ::'weight)"
      by (simp add: insert.hyps(1) update_wts_insert)
    then show "update_wts (K$ 0) {(t, 1) |t. t \<in> insert t'' F} $ t' = (0 ::'weight)"
      by (smt (verit, ccfv_SIG) Collect_cong insert_Collect insert_iff)
  qed
qed

end
