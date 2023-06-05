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
(*
instantiation list  :: (type) monoid_mult  begin

definition "one_list == []"
definition "times_list == (@)"

instance 
  apply standard
  subgoal for a b c
    by (simp add: times_list_def)
  subgoal for a
    by (simp add: times_list_def one_list_def)
  subgoal for a
    by (simp add: times_list_def one_list_def)
  done
end

*)

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

lemma julemand:
  assumes "(b, (l'', l''l), c) \<in> list_embed_ts ts"
  shows "(b, l'', c) \<in> ts"
  using assms unfolding list_embed_ts_def
  unfolding list_embed_monoid_def by auto

lemma julemand2:
  assumes "(p, dl, q) \<in> monoid_rtrancl (list_embed_ts ts)"
  assumes "dl = (d,l)"
  shows "(p, d, q) \<in> monoid_rtrancl ts"
  using assms
proof (induction arbitrary: d l)
  case (monoid_rtrancl_refl a)
  then show ?case  
    by (simp add: one_prod_def)
next
  case (monoid_rtrancl_into_rtrancl a w b l' c)
  then show ?case
    apply (cases "w")
    subgoal for w' w'l
      apply auto
      apply (cases "l'")
      subgoal for l'' l''l
        apply auto
        apply (subgoal_tac "(b, (l''), c) \<in> ts")
        subgoal
          apply (subgoal_tac "(a, w' * l'', c) \<in> monoid_rtrancl ts")
          subgoal
            apply (subgoal_tac "w' * l'' = d")
            subgoal
              apply auto
              done
            subgoal
              by (simp add: mult_prod_def)
            done
          subgoal
            using monoid_rtrancl.intros(2)[of a w' b ts l'' c]
            apply auto
            done
          done
        subgoal
          using julemand[of b l'' l''l c ts] apply auto
          done
        done
      done
    done
qed

lemma julemand3:
  assumes "(p, (d,l), q) \<in> monoid_rtrancl (list_embed_ts ts)"
  shows "(p, d, q) \<in> monoid_rtrancl ts"
  using assms julemand2 by metis 

lemma julemand4:
  assumes "(p, d, q) \<in> monoid_rtrancl ts"
  shows "\<exists>l. (p, (d,l), q) \<in> monoid_rtrancl (list_embed_ts ts) \<and> reduce_monoid_list l = d"
  using assms
proof (induction)
  case (monoid_rtrancl_refl a)
  then have "(a, (1, []), a) \<in> monoid_rtrancl (list_embed_ts ts) \<and> reduce_monoid_list [] = 1"
    by (metis monoid_rtrancl.monoid_rtrancl_refl one_list_def one_prod_def reduce_monoid_list.simps(1))
  then show ?case  
    by auto
next
  case (monoid_rtrancl_into_rtrancl a w b l c)
  then obtain l' where 
    "(a, (w, l'), b) \<in> monoid_rtrancl (list_embed_ts ts)" 
    "reduce_monoid_list l' = w"
    by auto

  have "(b, (l,[l]), c) \<in> list_embed_ts ts"
    by (simp add: list_embed_monoid_def list_embed_ts_def monoid_rtrancl_into_rtrancl.hyps(2))


  thm monoid_rtrancl_into_rtrancl

  have "(a, (w * l, l' * [l]), c) \<in> monoid_rtrancl (list_embed_ts ts)"
    by (metis (no_types, lifting) \<open>(a, (w, l'), b) \<in> monoid_rtrancl (list_embed_ts ts)\<close>
        \<open>(b, (l, [l]), c) \<in> list_embed_ts ts\<close> monoid_rtrancl.monoid_rtrancl_into_rtrancl 
        mult_prod_def prod.sel(1) prod.sel(2))
  moreover
  have "reduce_monoid_list (l' * [l]) = w * l"
    by (metis \<open>reduce_monoid_list l' = w\<close> mult.right_neutral reduce_monoid_list.simps(1) 
        reduce_monoid_list.simps(2) reduce_monoid_list_append)
  ultimately
  show ?case
    by auto
qed

thm monoid_rtrancl.induct[of a "(w,l)" b "(list_embed_ts r)" P]

\<comment> \<open>Unfold monoid_closure of transitions for 0, 1 and 2 transitions\<close>
lemma monoid_star_w0_COPY:
  assumes "(p, w, q) \<in> monoid_rtrancl (list_embed_ts ts)"
  assumes "snd w = []"
  shows "p = q \<and> fst w = 1" (* Anders added the second conjunct *)
  using assms
proof (induct rule: monoid_rtrancl.induct)
  case (monoid_rtrancl_refl a)
  then show ?case
    by (simp add: one_prod_def)
next
  case (monoid_rtrancl_into_rtrancl a w b l c)
  from \<open>(b, l, c) \<in> list_embed_ts ts\<close> have "snd l \<noteq> []"
    by (smt (verit, ccfv_SIG) fst_conv list.simps(3) list_embed_monoid_def list_embed_ts_def mem_Collect_eq snd_conv)
  then have \<open>snd (w * l) \<noteq> []\<close> by (simp add: mult_prod_def times_list_def)
  then show ?case by (simp add: monoid_rtrancl_into_rtrancl.prems)
qed

lemma monoid_rtrancl_hd_tail'_COPY:
  assumes "(p\<^sub>1, w\<^sub>1\<^sub>3d\<^sub>1\<^sub>3, p\<^sub>3) \<in> monoid_rtrancl (list_embed_ts ts)"
  shows "w\<^sub>1\<^sub>3d\<^sub>1\<^sub>3 = (1,[]) \<or> (\<exists>d\<^sub>1\<^sub>3.
           (\<exists>p\<^sub>2 d\<^sub>2\<^sub>3 \<gamma>\<^sub>1\<^sub>2 w\<^sub>2\<^sub>3 d\<^sub>1\<^sub>2.
               w\<^sub>1\<^sub>3d\<^sub>1\<^sub>3 = (d\<^sub>1\<^sub>3,\<gamma>\<^sub>1\<^sub>2#w\<^sub>2\<^sub>3) \<and>
               (p\<^sub>1, (d\<^sub>1\<^sub>2, [\<gamma>\<^sub>1\<^sub>2]), p\<^sub>2) \<in> list_embed_ts ts \<and>
               (p\<^sub>2, (d\<^sub>2\<^sub>3,w\<^sub>2\<^sub>3), p\<^sub>3) \<in> monoid_rtrancl (list_embed_ts ts) \<and>
               d\<^sub>1\<^sub>3 = d\<^sub>1\<^sub>2 * d\<^sub>2\<^sub>3))"
  using assms
proof (induction rule: monoid_rtrancl.induct)
  case (monoid_rtrancl_refl)
  then show ?case
    by (simp add: one_list_def one_prod_def)
next
  case (monoid_rtrancl_into_rtrancl p\<^sub>1 w\<^sub>1\<^sub>3d\<^sub>1\<^sub>3 p\<^sub>3 w\<^sub>3\<^sub>4d\<^sub>3\<^sub>4 p\<^sub>4) (* p\<^sub>1 \<gamma>\<^sub>1\<^sub>2w\<^sub>2\<^sub>3d\<^sub>1\<^sub>3 p\<^sub>3 p\<^sub>4 w\<^sub>2\<^sub>4 \<gamma>\<^sub>1\<^sub>2 d\<^sub>1\<^sub>4 *)
  show ?case
  proof (cases "(snd w\<^sub>1\<^sub>3d\<^sub>1\<^sub>3)")
    case (Cons \<gamma>\<^sub>1\<^sub>2 w\<^sub>2\<^sub>3)
    define d\<^sub>1\<^sub>3 where "d\<^sub>1\<^sub>3 = (fst w\<^sub>1\<^sub>3d\<^sub>1\<^sub>3)"
    define w\<^sub>3\<^sub>4 where "w\<^sub>3\<^sub>4 = snd w\<^sub>3\<^sub>4d\<^sub>3\<^sub>4"
    define d\<^sub>3\<^sub>4 where "d\<^sub>3\<^sub>4 = fst w\<^sub>3\<^sub>4d\<^sub>3\<^sub>4"
    define w\<^sub>2\<^sub>4 where "w\<^sub>2\<^sub>4 = w\<^sub>2\<^sub>3 @ w\<^sub>3\<^sub>4"

    have w24_tl: "w\<^sub>2\<^sub>4 = tl (snd (w\<^sub>1\<^sub>3d\<^sub>1\<^sub>3 * w\<^sub>3\<^sub>4d\<^sub>3\<^sub>4))"
      by (simp add: local.Cons mult_prod_def times_list_def w\<^sub>2\<^sub>4_def w\<^sub>3\<^sub>4_def)

    have "w\<^sub>1\<^sub>3d\<^sub>1\<^sub>3 = (d\<^sub>1\<^sub>3,\<gamma>\<^sub>1\<^sub>2 # w\<^sub>2\<^sub>3)"
      using Cons by (metis d\<^sub>1\<^sub>3_def surjective_pairing) 

    then have "w\<^sub>1\<^sub>3d\<^sub>1\<^sub>3 = (1,[]) \<or> (\<exists>d\<^sub>1\<^sub>3.
                (\<exists>p\<^sub>2 d\<^sub>2\<^sub>3 \<gamma>\<^sub>1\<^sub>2 w\<^sub>2\<^sub>3 d\<^sub>1\<^sub>2.
                   w\<^sub>1\<^sub>3d\<^sub>1\<^sub>3 = (d\<^sub>1\<^sub>3, \<gamma>\<^sub>1\<^sub>2 # w\<^sub>2\<^sub>3) \<and>
                   (p\<^sub>1, (d\<^sub>1\<^sub>2,[\<gamma>\<^sub>1\<^sub>2]), p\<^sub>2) \<in> list_embed_ts ts \<and> 
                   (p\<^sub>2, (d\<^sub>2\<^sub>3, w\<^sub>2\<^sub>3), p\<^sub>3) \<in> monoid_rtrancl (list_embed_ts ts) \<and> 
                   d\<^sub>1\<^sub>3 = d\<^sub>1\<^sub>2 * d\<^sub>2\<^sub>3))"
      using monoid_rtrancl_into_rtrancl.IH by auto
    then obtain p\<^sub>2 d\<^sub>2\<^sub>3 \<gamma>\<^sub>1\<^sub>2 w\<^sub>2\<^sub>3 d\<^sub>1\<^sub>2 where props:
      "((w\<^sub>1\<^sub>3d\<^sub>1\<^sub>3 = (d\<^sub>1\<^sub>3,\<gamma>\<^sub>1\<^sub>2 # w\<^sub>2\<^sub>3) \<and>
       (p\<^sub>1, (d\<^sub>1\<^sub>2,[\<gamma>\<^sub>1\<^sub>2]), p\<^sub>2) \<in> list_embed_ts ts \<and> 
       (p\<^sub>2, (d\<^sub>2\<^sub>3,w\<^sub>2\<^sub>3), p\<^sub>3) \<in> monoid_rtrancl (list_embed_ts ts) \<and> 
       d\<^sub>1\<^sub>3 = d\<^sub>1\<^sub>2 * d\<^sub>2\<^sub>3))"
      using d\<^sub>1\<^sub>3_def Cons by auto

    define d\<^sub>2\<^sub>4 where "d\<^sub>2\<^sub>4 = d\<^sub>2\<^sub>3 * d\<^sub>3\<^sub>4"

    have "(p\<^sub>2, (d\<^sub>2\<^sub>4,w\<^sub>2\<^sub>4), p\<^sub>4) \<in> monoid_rtrancl (list_embed_ts ts)"
      by (smt (verit) d\<^sub>2\<^sub>4_def d\<^sub>3\<^sub>4_def fst_conv list.sel(3) local.Cons monoid_rtrancl.simps 
          monoid_rtrancl_into_rtrancl.hyps(2) mult_prod_def props snd_conv times_list_def w\<^sub>2\<^sub>4_def 
          w\<^sub>3\<^sub>4_def)
    moreover
    define d\<^sub>1\<^sub>4 where "d\<^sub>1\<^sub>4 = d\<^sub>1\<^sub>2 * d\<^sub>2\<^sub>4"
    moreover
    have "(p\<^sub>1, (d\<^sub>1\<^sub>2,[\<gamma>\<^sub>1\<^sub>2]), p\<^sub>2) \<in> list_embed_ts ts"
      using props by fastforce
    moreover
    have "w\<^sub>1\<^sub>3d\<^sub>1\<^sub>3 * w\<^sub>3\<^sub>4d\<^sub>3\<^sub>4 = (d\<^sub>1\<^sub>4, \<gamma>\<^sub>1\<^sub>2 # w\<^sub>2\<^sub>4)"
      by (metis append_Cons d\<^sub>1\<^sub>3_def d\<^sub>1\<^sub>4_def d\<^sub>2\<^sub>4_def d\<^sub>3\<^sub>4_def list.inject local.Cons mult.assoc 
          mult_prod_def props snd_conv times_list_def w\<^sub>2\<^sub>4_def w\<^sub>3\<^sub>4_def)
    ultimately
    show ?thesis
      by auto
  next
    case Nil
    define d\<^sub>1\<^sub>3 where "d\<^sub>1\<^sub>3 = (fst w\<^sub>1\<^sub>3d\<^sub>1\<^sub>3)"
    define w\<^sub>1\<^sub>3 where "w\<^sub>1\<^sub>3 = (snd w\<^sub>1\<^sub>3d\<^sub>1\<^sub>3)"
    define d\<^sub>3\<^sub>4 where "d\<^sub>3\<^sub>4 = fst w\<^sub>3\<^sub>4d\<^sub>3\<^sub>4"
    define w\<^sub>3\<^sub>4 where "w\<^sub>3\<^sub>4 = snd w\<^sub>3\<^sub>4d\<^sub>3\<^sub>4"

    define p\<^sub>2 :: 'a where "p\<^sub>2 = p\<^sub>4"
    define d\<^sub>2\<^sub>4 :: 'b where "d\<^sub>2\<^sub>4 = 1"
    define \<gamma>\<^sub>1\<^sub>2 :: 'b where "\<gamma>\<^sub>1\<^sub>2 = hd w\<^sub>3\<^sub>4" (* w\<^sub>3\<^sub>4 is a singleton *)
    define w\<^sub>2\<^sub>4 :: "'b list" where "w\<^sub>2\<^sub>4 = 1"
    define d\<^sub>1\<^sub>2 :: 'b where "d\<^sub>1\<^sub>2 = d\<^sub>3\<^sub>4"
    define d\<^sub>1\<^sub>4 :: 'b where "d\<^sub>1\<^sub>4 = d\<^sub>1\<^sub>2 * d\<^sub>2\<^sub>4"

    have "d\<^sub>1\<^sub>3 = 1"
      using Nil monoid_rtrancl_into_rtrancl(1) d\<^sub>1\<^sub>3_def by (meson monoid_star_w0_COPY)
    have "w\<^sub>1\<^sub>3 = 1"
      by (simp add: local.Nil one_list_def w\<^sub>1\<^sub>3_def)
    have "p\<^sub>1 = p\<^sub>3"
      using Nil monoid_rtrancl_into_rtrancl(1) d\<^sub>1\<^sub>3_def by (meson monoid_star_w0_COPY)
    have "length w\<^sub>3\<^sub>4 = 1"
      using monoid_rtrancl_into_rtrancl(2) w\<^sub>3\<^sub>4_def
      by (smt (verit, best) One_nat_def Pair_inject length_0_conv length_Suc_conv 
          list_embed_monoid_def list_embed_ts_def mem_Collect_eq sndI)
    have "w\<^sub>3\<^sub>4 = [d\<^sub>3\<^sub>4]"
      by (metis One_nat_def \<open>length w\<^sub>3\<^sub>4 = 1\<close> d\<^sub>3\<^sub>4_def length_0_conv length_Suc_conv 
          list_embed_correct_def list_embed_correct_elem monoid_rtrancl_into_rtrancl.hyps(2)
          mult.right_neutral reduce_monoid_list.simps(1) reduce_monoid_list.simps(2) w\<^sub>3\<^sub>4_def)

    have "w\<^sub>1\<^sub>3d\<^sub>1\<^sub>3 * w\<^sub>3\<^sub>4d\<^sub>3\<^sub>4 = (d\<^sub>1\<^sub>4, \<gamma>\<^sub>1\<^sub>2 # w\<^sub>2\<^sub>4)"
      by (metis \<gamma>\<^sub>1\<^sub>2_def \<open>d\<^sub>1\<^sub>3 = 1\<close> \<open>w\<^sub>1\<^sub>3 = 1\<close> \<open>w\<^sub>3\<^sub>4 = [d\<^sub>3\<^sub>4]\<close> d\<^sub>1\<^sub>2_def d\<^sub>1\<^sub>3_def d\<^sub>1\<^sub>4_def d\<^sub>2\<^sub>4_def d\<^sub>3\<^sub>4_def 
          list.sel(1) local.Nil mult.right_neutral mult_1 one_prod_def prod.exhaust_sel w\<^sub>1\<^sub>3_def 
          w\<^sub>2\<^sub>4_def w\<^sub>3\<^sub>4_def)
    have "(p\<^sub>1, (d\<^sub>1\<^sub>2, [\<gamma>\<^sub>1\<^sub>2]), p\<^sub>2) \<in> list_embed_ts ts"
      by (metis \<gamma>\<^sub>1\<^sub>2_def \<open>p\<^sub>1 = p\<^sub>3\<close> \<open>w\<^sub>3\<^sub>4 = [d\<^sub>3\<^sub>4]\<close> d\<^sub>1\<^sub>2_def d\<^sub>3\<^sub>4_def list.sel(1) 
          monoid_rtrancl_into_rtrancl.hyps(2) p\<^sub>2_def prod.exhaust_sel w\<^sub>3\<^sub>4_def)
    have "(p\<^sub>2, (d\<^sub>2\<^sub>4, w\<^sub>2\<^sub>4), p\<^sub>4) \<in> monoid_rtrancl (list_embed_ts ts)"
      by (metis d\<^sub>2\<^sub>4_def monoid_rtrancl.monoid_rtrancl_refl one_prod_def p\<^sub>2_def w\<^sub>2\<^sub>4_def)
    have "d\<^sub>1\<^sub>4 = d\<^sub>1\<^sub>2 * d\<^sub>2\<^sub>4"
      using d\<^sub>1\<^sub>4_def by auto

    have
      "\<exists>d\<^sub>1\<^sub>4 p\<^sub>2 d\<^sub>2\<^sub>4 \<gamma>\<^sub>1\<^sub>2 w\<^sub>2\<^sub>4 d\<^sub>1\<^sub>2.
           w\<^sub>1\<^sub>3d\<^sub>1\<^sub>3 * w\<^sub>3\<^sub>4d\<^sub>3\<^sub>4 = (d\<^sub>1\<^sub>4, \<gamma>\<^sub>1\<^sub>2 # w\<^sub>2\<^sub>4) \<and>
           (p\<^sub>1, (d\<^sub>1\<^sub>2, [\<gamma>\<^sub>1\<^sub>2]), p\<^sub>2) \<in> list_embed_ts ts \<and>
           (p\<^sub>2, (d\<^sub>2\<^sub>4, w\<^sub>2\<^sub>4), p\<^sub>4) \<in> monoid_rtrancl (list_embed_ts ts) \<and> d\<^sub>1\<^sub>4 = d\<^sub>1\<^sub>2 * d\<^sub>2\<^sub>4"
      using \<open>(p\<^sub>1, (d\<^sub>1\<^sub>2, [\<gamma>\<^sub>1\<^sub>2]), p\<^sub>2) \<in> list_embed_ts ts\<close> 
        \<open>(p\<^sub>2, (d\<^sub>2\<^sub>4, w\<^sub>2\<^sub>4), p\<^sub>4) \<in> monoid_rtrancl (list_embed_ts ts)\<close> 
        \<open>w\<^sub>1\<^sub>3d\<^sub>1\<^sub>3 * w\<^sub>3\<^sub>4d\<^sub>3\<^sub>4 = (d\<^sub>1\<^sub>4, \<gamma>\<^sub>1\<^sub>2 # w\<^sub>2\<^sub>4)\<close> d\<^sub>1\<^sub>4_def by blast
    then have
      "w\<^sub>1\<^sub>3d\<^sub>1\<^sub>3 * w\<^sub>3\<^sub>4d\<^sub>3\<^sub>4 = (1, []) \<or> (\<exists>d\<^sub>1\<^sub>4. 
         (\<exists>p\<^sub>2 d\<^sub>2\<^sub>4 \<gamma>\<^sub>1\<^sub>2 w\<^sub>2\<^sub>4 d\<^sub>1\<^sub>2.
           w\<^sub>1\<^sub>3d\<^sub>1\<^sub>3 * w\<^sub>3\<^sub>4d\<^sub>3\<^sub>4 = (d\<^sub>1\<^sub>4, \<gamma>\<^sub>1\<^sub>2 # w\<^sub>2\<^sub>4) \<and>
           (p\<^sub>1, (d\<^sub>1\<^sub>2, [\<gamma>\<^sub>1\<^sub>2]), p\<^sub>2) \<in> list_embed_ts ts \<and>
           (p\<^sub>2, (d\<^sub>2\<^sub>4, w\<^sub>2\<^sub>4), p\<^sub>4) \<in> monoid_rtrancl (list_embed_ts ts) \<and> d\<^sub>1\<^sub>4 = d\<^sub>1\<^sub>2 * d\<^sub>2\<^sub>4))"
      by metis
    then show ?thesis
      . 
  qed
qed

lemma monoid_rtrancl_hd_tail_COPY:
  assumes "(p, (d,\<gamma>#w), p') \<in> monoid_rtrancl (list_embed_ts ts)"
  shows "\<exists>d' s d''.
           (p, (d',[\<gamma>]), s) \<in> list_embed_ts ts \<and>
           (s, (d'',w), p') \<in> monoid_rtrancl (list_embed_ts ts) \<and>
           d = d' * d''"
  using assms monoid_rtrancl_hd_tail'_COPY by fastforce 

lemma monoid_rtrancl_list_embed_ts_induct_reverse:
  assumes "(a, (w, l), b) \<in> monoid_rtrancl (list_embed_ts r)"
  assumes "(\<And>a. P a 1 a)"
  assumes "(\<And>a w b l c w' l'. (a, (w,l), b) \<in> list_embed_ts r \<Longrightarrow> P b w' c \<Longrightarrow> (b, (w',l'), c) \<in> monoid_rtrancl (list_embed_ts r) \<Longrightarrow> P a (w * w') c)"
  shows "P a w b"
  using assms
proof (induction "length l" arbitrary: a b l w)
  case 0
  then show ?case
    by (metis fst_eqD length_0_conv monoid_star_w0_COPY snd_eqD)
next
  case (Suc n)

  obtain w' l' a' l'' w'' where p:
    "(a,(w',l'),a') \<in> (list_embed_ts r)" 
    "(a', (w'', l''), b) \<in> monoid_rtrancl (list_embed_ts r)"
    "n = length l''" 
    "l = l' @ l''" 
    "w = w' * w''"
    using Suc(2) Suc(3)
    by (smt (verit, best) Pair_inject add_left_cancel append_Cons append_Nil le_add1 length_Cons 
        list.size(3) monoid_rtrancl_hd_tail'_COPY not_one_le_zero plus_1_eq_Suc)

  have q: "P a' w'' b"
    using Suc(1)[OF p(3) p(2)] Suc(4,5) by auto

  then show ?case 
    using Suc(5)[OF p(1) q p(2)] p by auto
qed

lemma monoid_rtrancl_list_induct_reverse:
  assumes "(a, w, b) \<in> monoid_rtrancl r"
  assumes "(\<And>a. P a 1 a)"
  assumes "(\<And>a w b l c w' l'. (a, w, b) \<in> r \<Longrightarrow> P b w' c \<Longrightarrow> (b, w', c) \<in> monoid_rtrancl r \<Longrightarrow> P a (w * w') c)"
  shows "P a w b"
  by (smt (verit) assms julemand julemand3 julemand4 monoid_rtrancl_list_embed_ts_induct_reverse)

end
