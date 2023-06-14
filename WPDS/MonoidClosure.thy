theory MonoidClosure
  imports "ProdDioid" Kleene_Algebra.Dioid_Models
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

lemma "(a,b,c) \<in> r \<Longrightarrow> (a,b,c) \<in> monoid_rtrancl r"
  using monoid_rtrancl_def
  apply -
  oops

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
  shows "monoid_rtranclp r x (u*v) z"
  using assms(2,1)
  by (induct, simp_all) (metis (no_types, opaque_lifting) monoid_rtranclp.monoid_rtrancl_into_rtrancl mult.assoc)


fun is_trace_fn :: "'a \<Rightarrow> ('a \<times> 'b::monoid_mult \<times> 'a) list \<Rightarrow> 'a \<Rightarrow> bool" where
  "is_trace_fn p [] q = (p = q)"
| "is_trace_fn p ((p',l,q')#ts) q = (p = p' \<and> is_trace_fn q' ts q)"

primrec is_trace :: "'a \<Rightarrow> ('a \<times> 'b::monoid_mult \<times> 'a) list \<Rightarrow> 'a \<Rightarrow> bool" where
  "is_trace p [] q = (p = q)"
| "is_trace p (t#ts) q = (p = fst t \<and> is_trace (snd (snd t)) ts q)"
primrec trace_weight :: "('a \<times> 'b::monoid_mult \<times> 'a) list \<Rightarrow> 'b" where
  "trace_weight [] = 1"
| "trace_weight (t#ts) = fst (snd t) * trace_weight ts"

lemma is_trace_append: "is_trace a x b \<and> is_trace b y c \<Longrightarrow> is_trace a (x @ y) c"
  by (induct x arbitrary: a, simp_all)
lemma trace_weight_append: "trace_weight (a @ b) = trace_weight a * trace_weight b"
  by (induct a, simp_all add: mult.assoc[symmetric])

lemma monoid_rtrancl_exists_trace: 
  assumes "(p, w, q) \<in> monoid_rtrancl ts"
  shows "\<exists>l. is_trace p l q \<and> trace_weight l = w \<and> l \<in> lists ts"
  using assms
  apply (induct rule: monoid_rtrancl.induct)
   apply (rule exI[of _ "[]"], simp)
  apply (erule exE)
  subgoal for a w b l c ls
    apply (rule exI[of _ "(ls@[(b,l,c)])"])
    using trace_weight_append[of "ls" "[(b,l,c)]"] is_trace_append[of _ "ls" _ "[(b,l,c)]"] by simp
  done

lemma is_trace_inj: "l \<noteq> [] \<and> is_trace a l b \<and> is_trace p l q \<Longrightarrow> a = p \<and> b = q"
  apply (induct l arbitrary: a p, simp)
  subgoal for a l aa p
    by force
  done
lemma trace_weight_inj: "trace_weight l = a \<and> trace_weight l = b \<Longrightarrow> a = b"
  by (induct l arbitrary: a b, simp_all)

primrec reduce_monoid_list :: "'a::monoid_mult list \<Rightarrow> 'a" where
  "reduce_monoid_list [] = 1"
| "reduce_monoid_list (x#xs) = x * reduce_monoid_list xs"

lemma reduce_monoid_list_append: "reduce_monoid_list a * reduce_monoid_list b = reduce_monoid_list (a * b)"
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
  shows "list_embed_correct (w * l)"
  using assms(1) list_embed_correct_elem[OF assms(2)]
  unfolding list_embed_correct_def mult_prod_def
  by (simp add: reduce_monoid_list_append)

lemma embed_monoid_star_empty:
  assumes "(p, (d,l), q) \<in> monoid_rtrancl {}"
  shows "d = reduce_monoid_list l"
  using assms
  by (rule monoid_rtrancl.cases, simp)
     (auto simp add: reduce_monoid_list_base)

lemma list_embed_ts_project:
  assumes "(p, (d, l), q) \<in> list_embed_ts ts"
  shows "(p, d, q) \<in> ts"
  using assms unfolding list_embed_ts_def
  unfolding list_embed_monoid_def by auto

lemma monoid_rtrancl_if_monoid_rtrancl_list_embed_ts':
  assumes "(p, dl, q) \<in> monoid_rtrancl (list_embed_ts ts)"
  shows "(p, fst dl, q) \<in> monoid_rtrancl ts"
  using assms
proof (induction)
  case (monoid_rtrancl_refl p)
  then show ?case  
    by (simp add: one_prod_def)
next
  case (monoid_rtrancl_into_rtrancl p\<^sub>1 d\<^sub>1\<^sub>2l\<^sub>1\<^sub>2 p\<^sub>2 dl\<^sub>1\<^sub>3 p\<^sub>3)
  obtain d\<^sub>1\<^sub>2 l\<^sub>1\<^sub>2 where d\<^sub>1\<^sub>2l\<^sub>1\<^sub>2_split: "d\<^sub>1\<^sub>2l\<^sub>1\<^sub>2 = (d\<^sub>1\<^sub>2, l\<^sub>1\<^sub>2)"
    by (cases d\<^sub>1\<^sub>2l\<^sub>1\<^sub>2)
  obtain d\<^sub>1\<^sub>3 l\<^sub>1\<^sub>3 where dl\<^sub>1\<^sub>3_split: "dl\<^sub>1\<^sub>3 = (d\<^sub>1\<^sub>3, l\<^sub>1\<^sub>3)"
    by (cases dl\<^sub>1\<^sub>3)
  have d_is: "d\<^sub>1\<^sub>2 * d\<^sub>1\<^sub>3 = fst (d\<^sub>1\<^sub>2l\<^sub>1\<^sub>2 * dl\<^sub>1\<^sub>3)"
    using dl\<^sub>1\<^sub>3_split d\<^sub>1\<^sub>2l\<^sub>1\<^sub>2_split by (simp add: mult_prod_def)
  have "(p\<^sub>2, d\<^sub>1\<^sub>3, p\<^sub>3) \<in> ts" 
    using list_embed_ts_project[of p\<^sub>2 d\<^sub>1\<^sub>3 l\<^sub>1\<^sub>3 p\<^sub>3 ts] dl\<^sub>1\<^sub>3_split monoid_rtrancl_into_rtrancl(2)
    by fastforce
  then have "(p\<^sub>1, d\<^sub>1\<^sub>2 * d\<^sub>1\<^sub>3, p\<^sub>3) \<in> monoid_rtrancl ts"
    using monoid_rtrancl.monoid_rtrancl_into_rtrancl monoid_rtrancl_into_rtrancl d\<^sub>1\<^sub>2l\<^sub>1\<^sub>2_split 
    by fastforce
  then show ?case
    using d_is by metis
qed

lemma monoid_rtrancl_if_monoid_rtrancl_list_embed_ts'':
  assumes "(p, (d,l), q) \<in> monoid_rtrancl (list_embed_ts ts)"
  shows "(p, d, q) \<in> monoid_rtrancl ts"
  using assms monoid_rtrancl_if_monoid_rtrancl_list_embed_ts' by fastforce

lemma monoid_rtrancl_if_monoid_rtrancl_list_embed_ts:
  assumes "(p, (d,l), q) \<in> monoid_rtrancl (list_embed_ts ts)"
  shows "(p, d, q) \<in> monoid_rtrancl ts"
  using assms monoid_rtrancl_if_monoid_rtrancl_list_embed_ts' by fastforce

lemma monoid_rtrancl_list_embed_ts_if_monoid_rtrancl:
  assumes "(p, d, q) \<in> monoid_rtrancl ts"
  shows "\<exists>l. (p, (d,l), q) \<in> monoid_rtrancl (list_embed_ts ts) \<and> reduce_monoid_list l = d"
  using assms
proof (induction)
  case (monoid_rtrancl_refl p)
  then have "(p, (1, []), p) \<in> monoid_rtrancl (list_embed_ts ts) \<and> reduce_monoid_list [] = 1"
    by (metis monoid_rtrancl.monoid_rtrancl_refl one_list_def one_prod_def reduce_monoid_list.simps(1))
  then show ?case  
    by auto
next
  case (monoid_rtrancl_into_rtrancl p d p' l p'')
  then obtain l' where 
    "(p, (d, l'), p') \<in> monoid_rtrancl (list_embed_ts ts)" 
    "reduce_monoid_list l' = d"
    by auto

  have "(p', (l,[l]), p'') \<in> list_embed_ts ts"
    by (simp add: list_embed_monoid_def list_embed_ts_def monoid_rtrancl_into_rtrancl.hyps(2))

  have "(p, (d * l, l' * [l]), p'') \<in> monoid_rtrancl (list_embed_ts ts)"
    by (metis (no_types, lifting) \<open>(p, (d, l'), p') \<in> monoid_rtrancl (list_embed_ts ts)\<close>
        \<open>(p', (l, [l]), p'') \<in> list_embed_ts ts\<close> monoid_rtrancl.monoid_rtrancl_into_rtrancl 
        mult_prod_def prod.sel(1) prod.sel(2))
  moreover
  have "reduce_monoid_list (l' * [l]) = d * l"
    by (metis \<open>reduce_monoid_list l' = d\<close> mult.right_neutral reduce_monoid_list.simps(1) 
        reduce_monoid_list.simps(2) reduce_monoid_list_append)
  ultimately
  show ?case
    by auto
qed

\<comment> \<open>NOTE: (adapted from monoid_star_w0)\<close>
lemma monoid_rtrancl_list_embed_w0:
  assumes "(p, dl, q) \<in> monoid_rtrancl (list_embed_ts ts)"
  assumes "snd dl = []"
  shows "p = q \<and> fst dl = 1"
  using assms
proof (induct rule: monoid_rtrancl.induct)
  case (monoid_rtrancl_refl a)
  then show ?case
    by (simp add: one_prod_def)
next
  case (monoid_rtrancl_into_rtrancl a dl b d'l' c)
  from \<open>(b, d'l', c) \<in> list_embed_ts ts\<close> have "snd d'l' \<noteq> []"
    by (smt (verit, ccfv_SIG) fst_conv list.simps(3) list_embed_monoid_def list_embed_ts_def mem_Collect_eq snd_conv)
  then have \<open>snd (dl * d'l') \<noteq> []\<close> by (simp add: mult_prod_def times_list_def)
  then show ?case by (simp add: monoid_rtrancl_into_rtrancl.prems)
qed

\<comment> \<open>NOTE: (adapted from monoid_rtrancl_wts_to_monoidLTS_cases_rev')\<close>
lemma monoid_rtrancl_list_embed_ts_cases_rev':
  assumes "(p\<^sub>1, d\<^sub>1\<^sub>3l\<^sub>1\<^sub>3, p\<^sub>3) \<in> monoid_rtrancl (list_embed_ts ts)"
  shows "d\<^sub>1\<^sub>3l\<^sub>1\<^sub>3 = (1,[]) \<or> (\<exists>d\<^sub>1\<^sub>3.
           (\<exists>p\<^sub>2 d\<^sub>2\<^sub>3 d\<^sub>1\<^sub>2 l\<^sub>2\<^sub>3 d\<^sub>1\<^sub>2.
               d\<^sub>1\<^sub>3l\<^sub>1\<^sub>3 = (d\<^sub>1\<^sub>3,d\<^sub>1\<^sub>2#l\<^sub>2\<^sub>3) \<and>
               (p\<^sub>1, (d\<^sub>1\<^sub>2, [d\<^sub>1\<^sub>2]), p\<^sub>2) \<in> list_embed_ts ts \<and>
               (p\<^sub>2, (d\<^sub>2\<^sub>3,l\<^sub>2\<^sub>3), p\<^sub>3) \<in> monoid_rtrancl (list_embed_ts ts) \<and>
               d\<^sub>1\<^sub>3 = d\<^sub>1\<^sub>2 * d\<^sub>2\<^sub>3))"
  using assms
proof (induction rule: monoid_rtrancl.induct)
  case (monoid_rtrancl_refl)
  then show ?case
    by (simp add: one_list_def one_prod_def)
next
  case (monoid_rtrancl_into_rtrancl p\<^sub>1 d\<^sub>1\<^sub>3l\<^sub>1\<^sub>3 p\<^sub>3 d\<^sub>3\<^sub>4l\<^sub>3\<^sub>4 p\<^sub>4)
  show ?case
  proof (cases "(snd d\<^sub>1\<^sub>3l\<^sub>1\<^sub>3)")
    case (Cons d\<^sub>1\<^sub>2 l\<^sub>2\<^sub>3)
    define d\<^sub>1\<^sub>3 where "d\<^sub>1\<^sub>3 = fst d\<^sub>1\<^sub>3l\<^sub>1\<^sub>3"
    define l\<^sub>3\<^sub>4 where "l\<^sub>3\<^sub>4 = snd d\<^sub>3\<^sub>4l\<^sub>3\<^sub>4"
    define d\<^sub>3\<^sub>4 where "d\<^sub>3\<^sub>4 = fst d\<^sub>3\<^sub>4l\<^sub>3\<^sub>4"
    define l\<^sub>2\<^sub>4 where "l\<^sub>2\<^sub>4 = l\<^sub>2\<^sub>3 @ l\<^sub>3\<^sub>4"

    have l24_tl: "l\<^sub>2\<^sub>4 = tl (snd (d\<^sub>1\<^sub>3l\<^sub>1\<^sub>3 * d\<^sub>3\<^sub>4l\<^sub>3\<^sub>4))"
      by (simp add: local.Cons mult_prod_def times_list_def l\<^sub>2\<^sub>4_def l\<^sub>3\<^sub>4_def)

    have "d\<^sub>1\<^sub>3l\<^sub>1\<^sub>3 = (d\<^sub>1\<^sub>3,d\<^sub>1\<^sub>2 # l\<^sub>2\<^sub>3)"
      using Cons by (metis d\<^sub>1\<^sub>3_def surjective_pairing) 

    then have "d\<^sub>1\<^sub>3l\<^sub>1\<^sub>3 = (1,[]) \<or> (\<exists>d\<^sub>1\<^sub>3.
                (\<exists>p\<^sub>2 d\<^sub>2\<^sub>3  l\<^sub>2\<^sub>3 d\<^sub>1\<^sub>2.
                   d\<^sub>1\<^sub>3l\<^sub>1\<^sub>3 = (d\<^sub>1\<^sub>3, d\<^sub>1\<^sub>2 # l\<^sub>2\<^sub>3) \<and>
                   (p\<^sub>1, (d\<^sub>1\<^sub>2,[d\<^sub>1\<^sub>2]), p\<^sub>2) \<in> list_embed_ts ts \<and> 
                   (p\<^sub>2, (d\<^sub>2\<^sub>3, l\<^sub>2\<^sub>3), p\<^sub>3) \<in> monoid_rtrancl (list_embed_ts ts) \<and> 
                   d\<^sub>1\<^sub>3 = d\<^sub>1\<^sub>2 * d\<^sub>2\<^sub>3))"
      using monoid_rtrancl_into_rtrancl.IH by auto
    then obtain p\<^sub>2 d\<^sub>2\<^sub>3 l\<^sub>2\<^sub>3 d\<^sub>1\<^sub>2 where props:
      "((d\<^sub>1\<^sub>3l\<^sub>1\<^sub>3 = (d\<^sub>1\<^sub>3,d\<^sub>1\<^sub>2 # l\<^sub>2\<^sub>3) \<and>
       (p\<^sub>1, (d\<^sub>1\<^sub>2,[d\<^sub>1\<^sub>2]), p\<^sub>2) \<in> list_embed_ts ts \<and> 
       (p\<^sub>2, (d\<^sub>2\<^sub>3,l\<^sub>2\<^sub>3), p\<^sub>3) \<in> monoid_rtrancl (list_embed_ts ts) \<and> 
       d\<^sub>1\<^sub>3 = d\<^sub>1\<^sub>2 * d\<^sub>2\<^sub>3))"
      using d\<^sub>1\<^sub>3_def Cons by auto

    define d\<^sub>2\<^sub>4 where "d\<^sub>2\<^sub>4 = d\<^sub>2\<^sub>3 * d\<^sub>3\<^sub>4"

    have "(p\<^sub>2, (d\<^sub>2\<^sub>4,l\<^sub>2\<^sub>4), p\<^sub>4) \<in> monoid_rtrancl (list_embed_ts ts)"
      by (smt (verit) d\<^sub>2\<^sub>4_def d\<^sub>3\<^sub>4_def fst_conv list.sel(3) local.Cons monoid_rtrancl.simps 
          monoid_rtrancl_into_rtrancl.hyps(2) mult_prod_def props snd_conv times_list_def l\<^sub>2\<^sub>4_def 
          l\<^sub>3\<^sub>4_def)
    moreover
    define d\<^sub>1\<^sub>4 where "d\<^sub>1\<^sub>4 = d\<^sub>1\<^sub>2 * d\<^sub>2\<^sub>4"
    moreover
    have "(p\<^sub>1, (d\<^sub>1\<^sub>2,[d\<^sub>1\<^sub>2]), p\<^sub>2) \<in> list_embed_ts ts"
      using props by fastforce
    moreover
    have "d\<^sub>1\<^sub>3l\<^sub>1\<^sub>3 * d\<^sub>3\<^sub>4l\<^sub>3\<^sub>4 = (d\<^sub>1\<^sub>4, d\<^sub>1\<^sub>2 # l\<^sub>2\<^sub>4)"
      by (metis append_Cons d\<^sub>1\<^sub>3_def d\<^sub>1\<^sub>4_def d\<^sub>2\<^sub>4_def d\<^sub>3\<^sub>4_def list.inject local.Cons mult.assoc 
          mult_prod_def props snd_conv times_list_def l\<^sub>2\<^sub>4_def l\<^sub>3\<^sub>4_def)
    ultimately
    show ?thesis
      by auto
  next
    case Nil
    define d\<^sub>1\<^sub>3 where "d\<^sub>1\<^sub>3 = fst d\<^sub>1\<^sub>3l\<^sub>1\<^sub>3"
    define l\<^sub>1\<^sub>3 where "l\<^sub>1\<^sub>3 = snd d\<^sub>1\<^sub>3l\<^sub>1\<^sub>3"
    define d\<^sub>3\<^sub>4 where "d\<^sub>3\<^sub>4 = fst d\<^sub>3\<^sub>4l\<^sub>3\<^sub>4"
    define l\<^sub>3\<^sub>4 where "l\<^sub>3\<^sub>4 = snd d\<^sub>3\<^sub>4l\<^sub>3\<^sub>4"

    define p\<^sub>2 where "p\<^sub>2 = p\<^sub>4"
    define d\<^sub>2\<^sub>4 where "d\<^sub>2\<^sub>4 = (1 :: 'b)"
    define l\<^sub>2\<^sub>4 where "l\<^sub>2\<^sub>4 = (1 :: 'b list)"
    define d\<^sub>1\<^sub>2 where "d\<^sub>1\<^sub>2 = d\<^sub>3\<^sub>4"
    define d\<^sub>1\<^sub>4 where "d\<^sub>1\<^sub>4 = d\<^sub>1\<^sub>2 * d\<^sub>2\<^sub>4"

    have "d\<^sub>1\<^sub>3 = 1"
      using Nil monoid_rtrancl_into_rtrancl(1) d\<^sub>1\<^sub>3_def by (meson monoid_rtrancl_list_embed_w0)
    have "l\<^sub>1\<^sub>3 = 1"
      by (simp add: local.Nil one_list_def l\<^sub>1\<^sub>3_def)
    have "p\<^sub>1 = p\<^sub>3"
      using Nil monoid_rtrancl_into_rtrancl(1) d\<^sub>1\<^sub>3_def by (meson monoid_rtrancl_list_embed_w0)
    have "length l\<^sub>3\<^sub>4 = 1"
      using monoid_rtrancl_into_rtrancl(2) l\<^sub>3\<^sub>4_def
      by (smt (verit, best) One_nat_def Pair_inject length_0_conv length_Suc_conv 
          list_embed_monoid_def list_embed_ts_def mem_Collect_eq sndI)
    have "d\<^sub>1\<^sub>4 = d\<^sub>1\<^sub>2 * d\<^sub>2\<^sub>4"
      using d\<^sub>1\<^sub>4_def by auto
    have "l\<^sub>3\<^sub>4 = [d\<^sub>3\<^sub>4]"
      by (metis One_nat_def \<open>length l\<^sub>3\<^sub>4 = 1\<close> d\<^sub>3\<^sub>4_def length_0_conv length_Suc_conv 
          list_embed_correct_def list_embed_correct_elem monoid_rtrancl_into_rtrancl.hyps(2)
          mult.right_neutral reduce_monoid_list.simps(1) reduce_monoid_list.simps(2) l\<^sub>3\<^sub>4_def)

    have "d\<^sub>1\<^sub>3l\<^sub>1\<^sub>3 * d\<^sub>3\<^sub>4l\<^sub>3\<^sub>4 = (d\<^sub>1\<^sub>4, d\<^sub>1\<^sub>2 # l\<^sub>2\<^sub>4)"
      by (metis \<open>d\<^sub>1\<^sub>3 = 1\<close> \<open>l\<^sub>1\<^sub>3 = 1\<close> \<open>l\<^sub>3\<^sub>4 = [d\<^sub>3\<^sub>4]\<close> d\<^sub>1\<^sub>2_def d\<^sub>1\<^sub>3_def d\<^sub>1\<^sub>4_def d\<^sub>2\<^sub>4_def d\<^sub>3\<^sub>4_def 
          local.Nil mult.right_neutral mult_1 one_prod_def prod.exhaust_sel l\<^sub>1\<^sub>3_def 
          l\<^sub>2\<^sub>4_def l\<^sub>3\<^sub>4_def)

    have "(p\<^sub>1, (d\<^sub>1\<^sub>2, [d\<^sub>1\<^sub>2]), p\<^sub>2) \<in> list_embed_ts ts"
      by (metis \<open>p\<^sub>1 = p\<^sub>3\<close> \<open>l\<^sub>3\<^sub>4 = [d\<^sub>3\<^sub>4]\<close> d\<^sub>1\<^sub>2_def d\<^sub>3\<^sub>4_def monoid_rtrancl_into_rtrancl.hyps(2) p\<^sub>2_def 
          prod.exhaust_sel l\<^sub>3\<^sub>4_def)
    have "(p\<^sub>2, (d\<^sub>2\<^sub>4, l\<^sub>2\<^sub>4), p\<^sub>4) \<in> monoid_rtrancl (list_embed_ts ts)"
      by (metis d\<^sub>2\<^sub>4_def monoid_rtrancl.monoid_rtrancl_refl one_prod_def p\<^sub>2_def l\<^sub>2\<^sub>4_def)

    have "d\<^sub>1\<^sub>3l\<^sub>1\<^sub>3 * d\<^sub>3\<^sub>4l\<^sub>3\<^sub>4 = (1, []) \<or> (\<exists>d\<^sub>1\<^sub>4. 
            (\<exists>p\<^sub>2 d\<^sub>2\<^sub>4 d\<^sub>1\<^sub>2 l\<^sub>2\<^sub>4 d\<^sub>1\<^sub>2.
              d\<^sub>1\<^sub>3l\<^sub>1\<^sub>3 * d\<^sub>3\<^sub>4l\<^sub>3\<^sub>4 = (d\<^sub>1\<^sub>4, d\<^sub>1\<^sub>2 # l\<^sub>2\<^sub>4) \<and>
              (p\<^sub>1, (d\<^sub>1\<^sub>2, [d\<^sub>1\<^sub>2]), p\<^sub>2) \<in> list_embed_ts ts \<and>
              (p\<^sub>2, (d\<^sub>2\<^sub>4, l\<^sub>2\<^sub>4), p\<^sub>4) \<in> monoid_rtrancl (list_embed_ts ts) \<and> d\<^sub>1\<^sub>4 = d\<^sub>1\<^sub>2 * d\<^sub>2\<^sub>4))"
      using \<open>(p\<^sub>1, (d\<^sub>1\<^sub>2, [d\<^sub>1\<^sub>2]), p\<^sub>2) \<in> list_embed_ts ts\<close> 
        \<open>(p\<^sub>2, (d\<^sub>2\<^sub>4, l\<^sub>2\<^sub>4), p\<^sub>4) \<in> monoid_rtrancl (list_embed_ts ts)\<close> 
        \<open>d\<^sub>1\<^sub>3l\<^sub>1\<^sub>3 * d\<^sub>3\<^sub>4l\<^sub>3\<^sub>4 = (d\<^sub>1\<^sub>4, d\<^sub>1\<^sub>2 # l\<^sub>2\<^sub>4)\<close> d\<^sub>1\<^sub>4_def by blast
    then show ?thesis
      . 
  qed
qed

lemma monoid_rtrancl_list_embed_ts_cases_rev:
  assumes "(p, (d,d'#l), p') \<in> monoid_rtrancl (list_embed_ts ts)"
  shows "\<exists>d'' s d'''.
           (p, (d'',[d']), s) \<in> list_embed_ts ts \<and>
           (s, (d''',l), p') \<in> monoid_rtrancl (list_embed_ts ts) \<and>
           d = d'' * d'''"
  using assms monoid_rtrancl_list_embed_ts_cases_rev' by fastforce 

lemma monoid_rtrancl_list_embed_ts_induct_rev:
  assumes "(a, (d, l), b) \<in> monoid_rtrancl (list_embed_ts r)"
  assumes "(\<And>a. P a 1 a)"
  assumes "(\<And>a d b l c d' l'. (a, (d,l), b) \<in> list_embed_ts r \<Longrightarrow> P b d' c \<Longrightarrow> 
              (b, (d',l'), c) \<in> monoid_rtrancl (list_embed_ts r) \<Longrightarrow> P a (d * d') c)"
  shows "P a d b"
  using assms
proof (induction "length l" arbitrary: a b l d)
  case 0
  then show ?case
    by (metis fst_eqD length_0_conv monoid_rtrancl_list_embed_w0 snd_eqD)
next
  case (Suc n)

  obtain d' l' a' l'' d'' where p:
    "(a,(d',l'),a') \<in> (list_embed_ts r)" 
    "(a', (d'', l''), b) \<in> monoid_rtrancl (list_embed_ts r)"
    "n = length l''" 
    "l = l' @ l''" 
    "d = d' * d''"
    using Suc(2) Suc(3)
    by (smt (verit, ccfv_threshold) append_Cons length_Suc_conv monoid_rtrancl_list_embed_ts_cases_rev self_append_conv2)

  have q: "P a' d'' b"
    using Suc(1)[OF p(3) p(2)] Suc(4,5) by auto

  then show ?case 
    using Suc(5)[OF p(1) q p(2)] p by auto
qed

lemma monoid_rtrancl_list_induct_rev [consumes 1, case_names monoid_rtrancl_refl monoid_rtrancl_into_rtrancl]:
  assumes "(a, w, b) \<in> monoid_rtrancl r"
  assumes "(\<And>a. P a 1 a)"
  assumes "(\<And>a w b c w'. (a, w, b) \<in> r \<Longrightarrow> P b w' c \<Longrightarrow> (b, w', c) \<in> monoid_rtrancl r  \<Longrightarrow> 
              P a (w * w') c)"
  shows "P a w b"
  by (smt (verit) assms list_embed_ts_project monoid_rtrancl_if_monoid_rtrancl_list_embed_ts''
      monoid_rtrancl_list_embed_ts_if_monoid_rtrancl monoid_rtrancl_list_embed_ts_induct_rev)

lemma monoid_rtranclp_list_induct_rev [consumes 1, case_names monoid_rtranclp_refl monoid_rtranclp_into_rtrancl]: 
  assumes "monoid_rtranclp r a w b"
  assumes "(\<And>a. P a 1 a)"
  assumes "(\<And>a w b c w'. r a w b \<Longrightarrow> P b w' c \<Longrightarrow> monoid_rtranclp r b w' c \<Longrightarrow> 
              P a (w * w') c)"
  shows "P a w b"
proof -
  define r' where "r' = {(a,w,b). r a w b}"

  have A: "(a, w, b) \<in> monoid_rtrancl r'"
    by (metis (no_types, lifting) \<open>r' \<equiv> {(a, x, y). r a x y}\<close> assms(1) mem_Collect_eq 
        mono_monoid_rtranclp monoid_rtranclp_monoid_rtrancl_eq split_conv)

  have B: "(\<And>a. P a 1 a)"
    using assms(2) by auto
  have C: "(\<And>a w b l c w' l'. (a, w, b) \<in> r' \<Longrightarrow> P b w' c \<Longrightarrow>
           (b, w', c) \<in> monoid_rtrancl r' \<Longrightarrow> P a (w * w') c)"
    by (metis (no_types, lifting) \<open>r' \<equiv> {(a, x, y). r a x y}\<close> assms(3) mem_Collect_eq 
        mono_monoid_rtranclp monoid_rtranclp_monoid_rtrancl_eq split_conv)

  show "P a w b"
    using A B C using monoid_rtrancl_list_induct_rev[of a w b r'] by metis
qed

end
