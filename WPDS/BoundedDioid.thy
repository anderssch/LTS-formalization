theory BoundedDioid
  imports "ProdDioid" "ReverseWellQuasiOrder"
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
class idem_ab_semigroup_add_ord = idempotent_ab_semigroup_add + ord +
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

\<comment> \<open>An idempotent semiring that follows the definition of [RSJM'05].\<close>
class idempotent_semiring = semiring_0 + monoid_mult + idempotent_ab_semigroup_add
begin

end


lemma 
  assumes no_infinite_decending: "\<nexists>f. \<forall>i. (f i) > (f (Suc i))"
  shows "almost_full_on (\<le>) UNIV"
  oops

lemma 
  fixes f::"nat \<Rightarrow> 'a::ord"
  assumes "almost_full_on (\<le>) (UNIV::'a set)"
  shows "\<not> antichain_on (\<le>) f UNIV"
  using almost_full_on_imp_no_antichain_on[OF assms, of f] by simp

class idempotent_semiring_ord = idempotent_semiring + idem_ab_semigroup_add_ord
begin
lemma no_trivial_inverse: "x \<noteq> 0 \<Longrightarrow> \<not>(\<exists>y. x + y = 0)"
  by (metis local.add_0_right local.meet.inf_left_idem)
end

\<comment> \<open>Definition 5 from [RSJM'05].\<close>
class bounded_idempotent_semiring = discrete_topology + idempotent_semiring_ord +
  assumes no_infinite_decending_chains: "almost_full_on (\<le>) UNIV"
begin
subclass wqo proof
  fix f
  show "good (\<le>) f" using no_infinite_decending_chains unfolding almost_full_on_def by simp
qed

subclass t2_space 
proof
  fix x y :: 'a
  assume "x \<noteq> y"
  then show "\<exists>U V. open U \<and> open V \<and> x \<in> U \<and> y \<in> V \<and> U \<inter> V = {}"
    by (intro exI[of _ "{_}"]) (auto intro!: open_discrete)
qed
subclass topological_comm_monoid_add proof
  fix a b :: 'a
  show "((\<lambda>x. fst x + snd x) \<longlongrightarrow> a + b) (nhds a \<times>\<^sub>F nhds b)" using open_discrete
    oops



function seq_sum_aux :: "(nat \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> 'a" where
  "seq_sum_aux f i = f i + seq_sum_aux f (Suc i)"
  by auto

definition seq_sum :: "(nat \<Rightarrow> 'a) \<Rightarrow> 'a" where
  "seq_sum f = seq_sum_aux f 0"

fun plus_seq :: "(nat \<Rightarrow> 'a) \<Rightarrow> (nat \<Rightarrow> 'a)" where
  "plus_seq f 0 = f 0"
| "plus_seq f (Suc i) = (f (Suc i)) + (plus_seq f i)"

lemma 
  assumes "\<forall>a \<in> A. \<forall> b \<in> A. a + b \<in> A"
  assumes "f \<in> SEQ A"
  shows "plus_seq f \<in> SEQ A"
  using assms(2) unfolding SEQ_def
  apply (simp, safe)
  subgoal for i
    apply (induct i, simp)
    subgoal for j
      by (simp add: assms(1))
    done
  done
lemma plus_seq_antimono': "i \<le> j \<Longrightarrow> plus_seq f i \<ge> plus_seq f j"
proof (induct j arbitrary: i)
  case 0
  then show ?case by simp
next
  case (Suc j)
  then show ?case
  proof (cases "i \<le> j")
    case True
    then show ?thesis using Suc(1) meet.le_infI2 by auto
  next
    case False
    then have "i = Suc j" using Suc(2) by simp
    then show ?thesis by blast
  qed
qed
lemma "antimono plus_seq"
  using plus_seq_antimono'
  oops

lemma plus_seq_less: "i < j \<Longrightarrow> plus_seq f i \<ge> plus_seq f j"
  using plus_seq_antimono'[of i j f] by simp

lemma plus_seq_exists_equal: "\<exists>i j. i < j \<and> plus_seq f i = plus_seq f j"
  using local.good[unfolded good_def, of "plus_seq f"]
  apply safe
  subgoal for i j
    using plus_seq_less[of i j f] antisym_conv by blast
  done

lemma plus_seq_terminates: "\<exists>i. \<forall>j. i < j \<longrightarrow> plus_seq f i = plus_seq f j"
  using local.good[unfolded good_def, of "plus_seq f"]
  apply safe
  subgoal for i j
    using plus_seq_less[of i j f] antisym_conv 
   oops



lemma strict_less_eq_is_less: "strict (\<le>) = (<)"
  using less_le_not_le by presburger

lemma "wfp_on (strict (\<le>)) (UNIV::('a set))"
  using wqo_on_imp_wfp_on[OF wqo_on_class]
  apply simp
(* apply assumption *)
  oops

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

thm no_infinite_decending[unfolded less_def less_eq_def, simplified]

lemma "\<exists>i. f i + f (Suc i) = f (Suc i) \<longrightarrow> f i = f (Suc i)"
  using no_infinite_decending[unfolded less_def less_eq_def, simplified] add_commute by metis

end

lemma
  fixes f :: "nat \<Rightarrow> 'a::bounded_idempotent_semiring"
  shows "\<exists>i. \<not> f (Suc i) < f i" 
  using no_infinite_decending by blast

lemma eventually_stable_sum:
  fixes f :: "nat \<Rightarrow> 'a::bounded_idempotent_semiring"
  shows "\<exists>L N. \<forall>n\<ge>N. (\<Sum>x | x < n. f x) = L" 
  using no_infinite_decending
  apply simp
  sorry

lemma summable_bounded_dioid:
  fixes f :: "nat \<Rightarrow> 'a::bounded_idempotent_semiring"
  shows "summable f"
  unfolding summable_def sums_def lessThan_def
  apply (simp add: tendsto_discrete[of "(\<lambda>n. \<Sum>x | x < n. f x)" _ sequentially] eventually_sequentially)
  by (fact eventually_stable_sum)


(* TODO *)
lemma Suminf_lower: "x \<in> A \<Longrightarrow> \<Sum>A \<le> x" oops
lemma Suminf_greatest: "(\<And>x. x \<in> A \<Longrightarrow> z \<le> x) \<Longrightarrow> z \<le> \<Sum>A" oops
lemma Suminf_empty [simp]: "\<Sum>{} = 0" oops

class bounded_dioid = Inf + bounded_idempotent_semiring
begin

(* lemma "(\<Sqinter>x\<in>A. x) = b" *)

end



(*
context dioid_one_zero 
begin
sublocale semilattice_neutr_order "(+)" "0" "(\<ge>)" "(>)" ..
sublocale semilattice_inf "(+)" "(\<ge>)" "(>)" by (rule join.dual_semilattice)
sublocale order_top "(\<ge>)" "(>)" "0" by (standard, simp)
sublocale bounded_semilattice_inf_top "(+)" "(\<ge>)" "(>)" "0" ..
end

context bounded_semilattice_inf_top
begin
(*
sublocale plus_ord "inf" "(\<ge>)" "(>)" proof
  fix x y
  show "(y \<le> x) = (inf x y = y)" by (rule inf.absorb_iff2)
  show "(y < x) = (y \<le> x \<and> x \<noteq> y)" by auto
qed

lemma "x \<ge> inf x y"
  by simp
*)

end


class wqo_bounded_semilattice = bounded_semilattice_inf_top + wqo
context wqo_bounded_semilattice
begin

abbreviation isMinimum :: "'a set \<Rightarrow> 'a \<Rightarrow> bool" where
 "isMinimum A b \<equiv> b \<in> A \<and> (\<forall>a \<in> A. b \<le> a)"
definition minimum :: "'a set \<Rightarrow> 'a" where
 "minimum A \<equiv> THE b. isMinimum A b"
definition supr :: "'a set \<Rightarrow> 'a" where
 "supr A \<equiv> minimum (Above (relation_of (\<le>) A) A)"

abbreviation isMaximum :: "'a set \<Rightarrow> 'a \<Rightarrow> bool" where
 "isMaximum A b \<equiv> b \<in> A \<and> (\<forall>a \<in> A. a \<le> b)"
definition maximum :: "'a set \<Rightarrow> 'a" where
 "maximum A \<equiv> THE b. isMaximum A b"
definition infi :: "'a set \<Rightarrow> 'a" where
 "infi A \<equiv> maximum (Under (relation_of (\<le>) A) A)"

end

class wqo_plus_ord = reverse_wqo + join_semilattice
begin
fun plus_seq :: "(nat \<Rightarrow> 'b::wqo_plus_ord) \<Rightarrow> (nat \<Rightarrow> 'b::wqo_plus_ord)" where
  "plus_seq f 0 = f 0"
| "plus_seq f (Suc i) = (f (Suc i)) + (plus_seq f i)"

lemma 
  assumes "\<forall>a \<in> A. \<forall> b \<in> A. a + b \<in> A"
  assumes "f \<in> SEQ A"
  shows "plus_seq f \<in> SEQ A"
  using assms(2) unfolding SEQ_def
  apply (simp, safe)
  subgoal for i
    apply (induct i, simp)
    subgoal for j
      by (simp add: assms(1))
    done
  done

lemma "good (\<ge>) (plus_seq f)" by (rule reverse_wqo_class.good)
lemma "a \<le> a + b" by simp

lemma plus_seq_mono': "i \<le> j \<Longrightarrow> plus_seq f i \<le> plus_seq f j"
proof (induct j arbitrary: i)
  case 0
  then show ?case by simp
next
  case (Suc j)
  then show ?case
  proof (cases "i \<le> j")
    case True
    then show ?thesis using Suc(1) join_semilattice_class.join.le_supI2 by auto
  next
    case False
    then have "i = Suc j" using Suc(2) by simp
    then show ?thesis by blast
  qed
qed

lemma plus_seq_mono: "mono (plus_seq f)"
  unfolding mono_def monotone_on_def
  apply (simp, safe)
  subgoal for i j
    using plus_seq_mono' by blast
  done

lemma plus_seq_less: "i < j \<Longrightarrow> plus_seq f i \<le> plus_seq f j"
  using plus_seq_mono'[of i j f] by simp

lemma plus_seq_exists_equal: "\<exists>i j. i < j \<and> plus_seq f i = plus_seq f j"
  using reverse_wqo_class.good[unfolded good_def, of "plus_seq f"]
  apply safe
  subgoal for i j
    using plus_seq_mono'[of i j f] by auto
  done

lemma wqo_on_greater_equal:
  fixes A :: "'b::wqo_plus_ord set"
  shows "wqo_on (\<ge>) A"
  using wqo_on_subset[of A UNIV] by simp

lemma
  fixes A :: "'b::wqo_plus_ord set"
  assumes "f \<in> SEQ A"
  shows "\<exists>i j. i < j \<and> plus_seq f i = plus_seq f j"
  oops


end

locale wqo_bounded_semilattice_on = wqo_bounded_semilattice +
  fixes A :: "'b::wqo_bounded_semilattice set"
begin

(*definition is_lub where
  "is_lub A lub = Above (relation_of (\<ge>) A )"
end*)

lemma less_eq_wqo_on: "wqo_on (\<le>) A"
  using wqo_on_subset[of A UNIV] by simp
lemma less_eq_almost_full_on: "almost_full_on (\<le>) A"
  using wqo_on_imp_almost_full_on[OF less_eq_wqo_on] by simp
lemma less_eq_transp_on: "transp_on (\<le>) A"
  using wqo_on_imp_transp_on[OF less_eq_wqo_on] by simp
lemma less_eq_reflp_on: "reflp_on (\<le>) A"
  unfolding reflp_on_def by simp

lemma less_eq_trans_relation_of: "trans (relation_of (\<le>) A)"
  unfolding trans_def relation_of_def by auto
lemma less_eq_refl_on_relation_of: "refl_on A (relation_of (\<le>) A)"
  unfolding refl_on_def relation_of_def by auto
lemma less_eq_antisym_relation_of: "antisym (relation_of (\<le>) A)"
  unfolding antisym_def relation_of_def by auto
lemma less_eq_preorder_on_relation_of: "preorder_on A (relation_of (\<le>) A)"
  unfolding preorder_on_def using less_eq_trans_relation_of less_eq_refl_on_relation_of by blast
lemma less_eq_partial_order_on_relation_of: "partial_order_on A (relation_of (\<le>) A)"
  unfolding partial_order_on_def 
  using less_eq_preorder_on_relation_of less_eq_antisym_relation_of by blast
lemma less_eq_Field_relation_of: "Field (relation_of (\<le>) A) = A"
  by (rule Field_relation_of[OF less_eq_refl_on_relation_of])

lemma Preorder_less_eq: "Preorder (relation_of (\<le>) A)"
  using less_eq_Field_relation_of less_eq_preorder_on_relation_of by simp
lemma Partial_order_less_eq: "Partial_order (relation_of (\<le>) A)"
  using less_eq_Field_relation_of less_eq_partial_order_on_relation_of by simp

lemma "\<forall>f \<in> SEQ A. good (\<le>) f"
  using less_eq_almost_full_on unfolding almost_full_on_def by blast


lemma "inf a b \<le> a" by simp
lemma "inf (inf a b) c \<le> a" using inf_le1 inf.assoc by presburger
lemma "inf a (inf b c) \<le> a" by auto
lemma "inf a (inf b c) \<le> b" by (auto intro: le_infI2)
lemma "inf a (inf b c) \<le> c" by (auto intro: le_infI2)

fun inf_seq :: "(nat \<Rightarrow> 'b) \<Rightarrow> (nat \<Rightarrow> 'b)" where
  "inf_seq f 0 = f 0"
| "inf_seq f (Suc i) = (inf (f (Suc i)) (inf_seq f i))"

lemma "inf_seq f \<in> SEQ A"


lemma "f \<in> SEQ A \<Longrightarrow> \<exists>i j. i < j \<and> (f i) \<le> (f j)"

definition upper_bounds where
  "upper_bounds = Above (relation_of (\<le>) A) A"
definition lower_bounds where
  "lower_bounds = Under (relation_of (\<le>) A) A"
definition supremum :: "'b" where 
  "supremum \<equiv> minim (upper_bounds)"
definition infimum :: "'b" where 
  "infimum \<equiv> maxim (lower_bounds)"

lemma upper_bounds_subset: "upper_bounds \<subseteq> A"
  unfolding upper_bounds_def Above_def by (simp add: less_eq_Field_relation_of)
lemma lower_bounds_subset: "lower_bounds \<subseteq> A"
  unfolding lower_bounds_def Under_def by (simp add: less_eq_Field_relation_of)

lemma "wqo_on (\<le>) upper_bounds"
  by (rule wqo_on_subset[OF upper_bounds_subset less_eq_wqo_on])
lemma "wqo_on (\<le>) lower_bounds"
  by (rule wqo_on_subset[OF lower_bounds_subset less_eq_wqo_on])  



lemma "\<exists>b. isMaxim (lower_bounds) b"
  unfolding lower_bounds_def Under_def
  apply (simp add: less_eq_Field_relation_of)
proof (rule ccontr)

qed
  oops

lemma "\<exists>b. isMinim (upper_bounds) b"
  unfolding upper_bounds_def Above_def
  apply (simp add: less_eq_Field_relation_of)
  oops

end
                             
class bounded_dioid = dioid_one_zero + reverse_wqo
                             
(*
definition "wqo_rel_on A r \<equiv> preorder_on A r \<and> almost_full_on A r"

locale wqo_rel =
  fixes r :: "'a rel"
  assumes WELL: "wqo_on r"
begin

definition isMinim :: "'a set \<Rightarrow> 'a \<Rightarrow> bool"
where "isMinim A b \<equiv> b \<in> A \<and> (\<forall>a \<in> A. (b,a) \<in> r)"

definition minim :: "'a set \<Rightarrow> 'a"
where "minim A \<equiv> THE b. isMinim A b"

definition supr :: "'a set \<Rightarrow> 'a"
where "supr A \<equiv> minim (Above A)"

definition is_lub where
  "is_lub A lib = Above (relation_of (\<ge>) A )"

end
*)

class my_sub_lattice = semilattice_sup + Sup + bot +
  assumes Sup_upper: "x \<in> A \<Longrightarrow> x \<le> Sup A"
      and Sup_least: "(\<And>x. x \<in> A \<Longrightarrow> x \<le> z) \<Longrightarrow> Sup A \<le> z"
      and Sup_empty [simp]: "Sup{} = bot"
begin

subclass bounded_semilattice_sup_bot proof
  oops

end





lemma "wqo_on (\<ge>) (A::'a::reverse_wqo set)"
  using reverse_wqo_on_class wqo_on_subset top_greatest oops

lemma "x \<in> (A::'a::{bounded_dioid} set) \<Longrightarrow> \<exists>f\<in> SEQ A. \<exists>i. f i = x"
  by auto

lemma 
  fixes A::"'a::{bounded_dioid} set"
  assumes "x \<in> A"
  shows "\<exists>f\<in> SEQ A. \<exists>i. f i = x"
  using assms by auto

lemma obtain_seq_i:
  fixes A::"'a set"
  assumes "x \<in> A"
  obtains f i where "f \<in> SEQ A \<and> (f i = x)"
  using assms by fast

lemma 
  fixes A::"'a::{bounded_dioid} set"
  assumes "x \<in> A"
  shows "\<exists>f\<in> SEQ A. \<exists>i. f i = x"
  using assms by auto


definition is_lub :: "'a::{bounded_dioid} set \<Rightarrow> 'a \<Rightarrow> bool" where
  "is_lub A lub \<longleftrightarrow> (\<forall>a \<in> A. a \<le> lub) \<and> (\<forall>ub. (\<forall>a \<in> A. a \<le> ub) \<longrightarrow> lub \<le> ub)"

definition is_witness_set :: "'a::{bounded_dioid} set \<Rightarrow> 'a set \<Rightarrow> bool" where
  "is_witness_set A W \<equiv> finite W \<and> (\<forall>a\<in>A. \<exists>w. w \<subseteq> W \<and> a = \<Sum>w)"

lemma witness_set_exists:
  fixes A::"'a::{bounded_dioid} set"
  shows "\<exists>W. is_witness_set A W"
  
  oops

lemma witness_set_unique_sum:
  fixes A::"'a::{bounded_dioid} set"
  assumes "is_witness_set A W"
  assumes "is_witness_set A W'"
  shows "\<Sum> W = \<Sum> W'"
  oops

definition witness_set:: "'a::{bounded_dioid} set \<Rightarrow> 'a set" where
  "witness_set A = (THE W. is_witness_set A W)"


lemma 
  fixes A::"'a::{bounded_dioid} set"
  shows "\<exists>lub. is_lub A lub"
  unfolding is_lub_def
proof
  have "wqo_on (\<ge>) A" using reverse_wqo_on_class wqo_on_subset top_greatest by blast
  then have "almost_full_on (\<ge>) A" by (rule wqo_on_imp_almost_full_on)
  then have "\<exists>lub. is_lub A lub" unfolding is_lub_def wqo_on_def almost_full_on_def good_def SEQ_def
    apply simp
    apply (rule exI)
    apply safe
    subgoal for a
    apply simp
qed
  apply -
  oops



lemma 
  fixes A::"'a::{bounded_dioid} set"
  assumes "is_lub A sup1"
  assumes "is_lub A sup2"
  shows "sup1 = sup2"
  using assms unfolding is_lub_def
  apply -
  oops

definition lub :: "'a::{bounded_dioid} set \<Rightarrow> 'a" where
  "lub A = (THE sup. is_lub A sup)"

(*
definition bounded_dioid_Sup:: "'a::{bounded_dioid} set \<Rightarrow> 'a" where
  "bounded_dioid_Sup S = \<Sum>(witness_set S)"

lemma "Sup S = bounded_dioid_Sup S"
  oops

context bounded_dioid 
begin
sublocale my_sub_lattice "bounded_dioid_Sup" "(+)" "(\<le>)" "(<)" "0"
proof

qed
end
*)
*)

end