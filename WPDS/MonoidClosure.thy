theory MonoidClosure
  imports "ProdDioid" "Kleene_Algebra.Dioid_Models"
begin

\<comment> \<open>Preliminary definition of reflexive and transitive closure over a relation labelled with a monoid, 
    (and transitive closure over a semigroup-labelled relation)\<close>
inductive_set monoid_rtrancl :: "('a \<times> 'b::monoid_mult \<times> 'a) set \<Rightarrow> ('a \<times> 'b \<times> 'a) set"
 for r :: "('a \<times> 'b \<times> 'a) set" where
    monoid_rtrancl_refl [intro!, Pure.intro!, simp]: "(a, 1, a) \<in> monoid_rtrancl r"
  | monoid_rtrancl_into_rtrancl [Pure.intro]: "(a, w, b) \<in> monoid_rtrancl r \<Longrightarrow> (b, l, c) \<in> r \<Longrightarrow> (a, w*l, c) \<in> monoid_rtrancl r"
inductive_cases monoid_rtrancl_empty [elim]: "(p, 1, q) \<in> monoid_rtrancl r"
inductive_cases monoid_rtrancl_extend: "(p, w*l, q) \<in> monoid_rtrancl r"

inductive_set semigroup_trancl :: "('a \<times> 'b::semigroup_mult \<times> 'a) set \<Rightarrow> ('a \<times> 'b \<times> 'a) set"
 for r :: "('a \<times> 'b \<times> 'a) set" where
    semigroup_trancl_refl [intro!, Pure.intro!, simp]: "(a, l, b) \<in> r \<Longrightarrow> (a, l, b) \<in> semigroup_trancl r"
  | semigroup_trancl_into_rtrancl [Pure.intro]: "(a, w, b) \<in> semigroup_trancl r \<Longrightarrow> (b, l, c) \<in> r \<Longrightarrow> (a, w*l, c) \<in> semigroup_trancl r"

lemma predicate3I[intro]:
  assumes PQ: "\<And>x y z. P x y z \<Longrightarrow> Q x y z"
  shows "P \<le> Q"
  apply (rule le_funI)+
  apply (rule le_boolI)
  by (rule PQ)
lemma predicate3D[dest]:
  "P \<le> Q \<Longrightarrow> P x y z \<Longrightarrow> Q x y z"
  by (erule le_funE)+ (erule le_boolE)

lemma monoid_rtranclp_mono: "r \<le> s \<Longrightarrow> monoid_rtranclp r \<le> monoid_rtranclp s"
  \<comment> \<open>monotonicity of \<open>monoid_rtrancl\<close>\<close>
proof (rule predicate3I)
  show "(monoid_rtranclp s) x y z" if "r \<le> s" "(monoid_rtranclp) r x y z" for x y z
    using \<open>(monoid_rtranclp r) x y z\<close> \<open>r \<le> s\<close>
    by (induction rule: monoid_rtranclp.induct) 
       (blast intro: monoid_rtranclp.monoid_rtrancl_into_rtrancl)+
qed

lemma mono_monoid_rtranclp[mono]: "(\<And>a b c. x a b c \<longrightarrow> y a b c) \<Longrightarrow> (monoid_rtranclp x) a b c \<longrightarrow> (monoid_rtranclp y) a b c"
  using monoid_rtranclp_mono[of x y] by auto
lemmas monoid_rtrancl_mono = monoid_rtranclp_mono [to_set]

lemma mono_monoid_rtrancl[mono]: "(\<And>a b c. (a,b,c) \<in> x \<longrightarrow> (a,b,c) \<in> y) \<Longrightarrow> (a,b,c) \<in> monoid_rtrancl x \<longrightarrow> (a,b,c) \<in> monoid_rtrancl y"
  using monoid_rtrancl_mono[of x y] by auto

lemma monoid_rtrancl_is_mono: "mono monoid_rtrancl"
  unfolding mono_def
  apply safe
  subgoal for x y
    using mono_monoid_rtrancl[of x y] by blast
  done

lemma monoid_rtranclp_trans:
  assumes "monoid_rtranclp r x u y"
  assumes "monoid_rtranclp r y v z"
  shows "monoid_rtranclp r x (u\<cdot>v) z"
  using assms(2,1)
  by (induct, simp_all) (metis (no_types, opaque_lifting) monoid_rtranclp.monoid_rtrancl_into_rtrancl mult.assoc)



(*
primrec reduce_monoid_list :: "'a::monoid_mult list \<Rightarrow> 'a" where
  "reduce_monoid_list [] = 1"
| "reduce_monoid_list (x#xs) = x \<cdot> reduce_monoid_list xs"

lemma reduce_monoid_list_append: "reduce_monoid_list a \<cdot> reduce_monoid_list b = reduce_monoid_list (a \<cdot> b)"
  unfolding times_list_def by (induct a, simp_all add: mult.assoc)

definition list_embed_monoid :: "'b::monoid_mult \<Rightarrow> 'b \<times> 'b list" where
  "list_embed_monoid d = (d,[d])"
definition list_embed_ts :: "('a \<times> 'b::monoid_mult \<times> 'a) set \<Rightarrow> ('a \<times> ('b \<times> 'b list) \<times> 'a) set" where
  "list_embed_ts ts \<equiv> {(p, list_embed_monoid d, q) | p d q. (p,d,q) \<in> ts}"
definition list_embed_correct :: "'a::monoid_mult \<times> 'a list \<Rightarrow> bool" where
  "list_embed_correct w \<equiv> fst w = reduce_monoid_list (snd w)"

lemma reduce_monoid_list_base:
  "(d, l) = 1 \<Longrightarrow> d = reduce_monoid_list l"
  by (simp add: one_list_def one_prod_def)
lemma list_embed_correct_one: "list_embed_correct 1"
  unfolding list_embed_correct_def using reduce_monoid_list_base by force
lemma list_embed_ts_mono[mono]: "mono list_embed_ts"
  unfolding list_embed_ts_def list_embed_monoid_def mono_def by blast

lemma list_embed_correct_elem: "(p, w, q) \<in> list_embed_ts ts \<Longrightarrow> list_embed_correct w"
  unfolding list_embed_ts_def list_embed_monoid_def list_embed_correct_def by auto

lemma list_embed_ts_step:
  assumes "list_embed_correct w"
  assumes "(p, l, q) \<in> list_embed_ts ts"
  shows "list_embed_correct (w\<cdot>l)"
  using assms(1) list_embed_correct_elem[OF assms(2)]
  unfolding list_embed_correct_def mult_prod_def
  by (simp add: reduce_monoid_list_append)

lemma embed_monoid_star_empty:
  assumes "(p, (d,l), q) \<in> monoid_rtrancl {}"
  shows "d = reduce_monoid_list l"
  using assms
  by (rule monoid_rtrancl.cases, simp)
     (auto simp add: reduce_monoid_list_base)

*)

end