theory LTS imports Main "HOL-Library.Multiset_Order" begin


section \<open>LTS\<close>

type_synonym ('state, 'label) transition = "'state * 'label * 'state"

fun transitions_of :: "'state list * 'label list \<Rightarrow> ('state, 'label) transition multiset" where
  "transitions_of (s1#s2#ss, \<gamma>#w) = {# (s1, \<gamma>, s2) #} + transitions_of (s2#ss, w)"
| "transitions_of ([s1],_) = {#}"
| "transitions_of ([],_) = {#}"
| "transitions_of (_,[]) = {#}"

fun transition_list :: "'state list * 'label list \<Rightarrow> ('state, 'label) transition list" where
  "transition_list (s1#s2#ss, \<gamma>#w) = (s1, \<gamma>, s2) # (transition_list (s2#ss, w))"
| "transition_list ([s1],_) = []"
| "transition_list ([],_) = []"
| "transition_list (_,[]) = []"

fun transitions_of' :: "'state * 'label list * 'state list * 'state \<Rightarrow> ('state, 'label) transition multiset" where
  "transitions_of' (p,w,ss,q) = transitions_of (ss, w)"

fun transition_list_of' where
  "transition_list_of' (p,\<gamma>#w,p'#p''#ss,q) = (p, \<gamma>, p'')#(transition_list_of' (p'',w,p''#ss,q))"
| "transition_list_of' (p, [], _, p'') = []"
| "transition_list_of' (p, _, [], p'') = []" (* Equivalent to the above *)
| "transition_list_of' (v, va # vc, [vf], ve) = []" (* Should not occur *)

fun append_path_with_word :: "('a list \<times> 'b list) \<Rightarrow> ('a list \<times> 'b list) \<Rightarrow> ('a list \<times> 'b list)" (infix "@\<acute>" 65) where (* TODO: rename *)
  "(ss1,w1) @\<acute> (ss2,w2) = (ss1@(tl ss2), w1 @ w2)"

fun append_path_with_word_\<gamma> :: "(('a list \<times> 'b list) * 'b) \<Rightarrow> ('a list \<times> 'b list) \<Rightarrow> ('a list \<times> 'b list)" (infix "@\<^sup>\<gamma>" 65) where (* TODO: rename *)
  "((ss1,w1),\<gamma>) @\<^sup>\<gamma> (ss2,w2) = (ss1@ss2, w1 @ [\<gamma>] @ w2)"

fun append_transition_star_states :: "('a \<times> 'b list \<times> 'a list \<times> 'a) \<Rightarrow> ('a \<times> 'b list \<times> 'a list \<times> 'a) \<Rightarrow> ('a \<times> 'b list \<times> 'a list \<times> 'a)" (infix "@@\<acute>" 65) where (* TODO: rename *)
  "(p1,w1,ss1,q1) @@\<acute> (p2,w2,ss2,q2) = (p1, w1 @ w2, ss1@(tl ss2), q2)"

fun append_transition_star_states_\<gamma> :: "(('a \<times> 'b list \<times> 'a list \<times> 'a) * 'b) \<Rightarrow> ('a \<times> 'b list \<times> 'a list \<times> 'a) \<Rightarrow> ('a \<times> 'b list \<times> 'a list \<times> 'a)" (infix "@@\<^sup>\<gamma>" 65) where (* TODO: rename *)
  "((p1,w1,ss1,q1),\<gamma>) @@\<^sup>\<gamma> (p2,w2,ss2,q2) = (p1, w1 @ [\<gamma>] @ w2, ss1@ss2, q2)"

locale LTS =
  fixes transition_relation :: "('state, 'label) transition set"
begin

text \<open>More definitions.\<close>

definition step_relp  :: "'state \<Rightarrow> 'state \<Rightarrow> bool" (infix "\<Rightarrow>" 80) where
  "c \<Rightarrow> c' \<equiv> \<exists>l. (c, l, c') \<in> transition_relation"

abbreviation step_starp :: "'state \<Rightarrow> 'state \<Rightarrow> bool" (infix "\<Rightarrow>\<^sup>*" 80) where
  "c \<Rightarrow>\<^sup>* c' == step_relp\<^sup>*\<^sup>* c c'"

definition step_rel :: "'state rel" where 
  "step_rel \<equiv> {(c, c'). step_relp c c'}"

definition step_star :: "'state rel" where 
  "step_star \<equiv> {(c, c'). step_starp c c'}"

(* For a set of states C, post*(C) is the set of all states reachable from C. *)
definition post_star :: "'state set \<Rightarrow> 'state set" where
  "post_star C \<equiv> {c'. \<exists>c \<in> C. c \<Rightarrow>\<^sup>* c'}"

(* And pre*(C) is the set of all states that can reach a state in C. *)
definition pre_star :: "'state set \<Rightarrow> 'state set" where
  "pre_star C \<equiv> {c'. \<exists>c \<in> C. c' \<Rightarrow>\<^sup>* c}"

(* Paths as defined in the thesis: *)
inductive_set path :: "'state list set" where
  "[s] \<in> path"
| "(s'#ss) \<in> path \<Longrightarrow> (s,l,s') \<in> transition_relation \<Longrightarrow> s#s'#ss \<in> path"

inductive_set transition_star :: "('state * 'label list * 'state) set" where
  transition_star_refl[iff]: "(p, [], p) \<in> transition_star"
| transition_star_step: "(p,\<gamma>,q') \<in> transition_relation \<Longrightarrow> (q',w,q) \<in> transition_star
                           \<Longrightarrow> (p, \<gamma>#w, q) \<in> transition_star"

(* I could make a notation like p \<Midarrow>w\<Rightarrow>* q *)

inductive_cases transition_star_empty [elim]: "(p, [], q) \<in> transition_star"
inductive_cases transition_star_cons: "(p, \<gamma>#w, q) \<in> transition_star"

inductive_set transition_star_states :: "('state * 'label list * 'state list * 'state) set" where
  transition_star_states_refl[iff]: "(p,[],[p],p) \<in> transition_star_states"
| transition_star_states_step: "(p,\<gamma>,q') \<in> transition_relation \<Longrightarrow> (q',w,ss,q) \<in> transition_star_states
                           \<Longrightarrow> (p, \<gamma>#w, p#ss, q) \<in> transition_star_states"

inductive_set path_with_word :: "('state list * 'label list) set" where
  path_with_word_refl[iff]: "([s],[]) \<in> path_with_word"
| path_with_word_step: "(s'#ss, w) \<in> path_with_word \<Longrightarrow> (s,l,s') \<in> transition_relation \<Longrightarrow> (s#s'#ss,l#w) \<in> path_with_word"


lemma path_with_word_length: (* TODO: move to LTS *)
  assumes "(ss, w) \<in> LTS.path_with_word pg"
  shows "length ss = length w + 1"
  using assms 
proof (induction rule: LTS.path_with_word.induct[OF assms(1)])
  case (1 s)
  then show ?case by auto
next
  case (2 ss s w l s')
  then show ?case by auto
qed

lemma path_with_word_induct_reverse: "(ss, w) \<in> path_with_word \<Longrightarrow>
(\<And>s. P [s] []) \<Longrightarrow>
(\<And>ss s w l s'. (ss @ [s], w) \<in> path_with_word \<Longrightarrow> P (ss @ [s]) w \<Longrightarrow> (s, l, s') \<in> transition_relation \<Longrightarrow> P (ss @ [s, s']) (w @ [l])) \<Longrightarrow>
P ss w"
proof (induction rule: path_with_word.induct)
  case (path_with_word_refl s)
  then show ?case
    by simp
next
  case (path_with_word_step s' ss w s l)
  have "length ss = length w"
    using path_with_word_length
    by (metis One_nat_def add_right_cancel list.size(4) path_with_word_step.hyps(1)) 

  have "(ss = []) \<or> length ss = 1 \<or> length ss \<ge> 2"
    by (metis One_nat_def Suc_1 Suc_leI length_greater_0_conv less_le)
  then show ?case
  proof
    assume tv: "ss = []"

    have Ps: "P [s] []"
      by (simp add: path_with_word_step.prems(1))
    have tr: "(s, l, s') \<in> transition_relation"
      by (simp add: path_with_word_step.hyps(2))
    from tv Ps tr have "P ([s,s']) [l]"
      using path_with_word_step(5)[of "[]" s "[]" l s']
      by auto
    then show "P (s # s' # ss) (l # w)"
      using \<open>length ss = length w\<close> tv by fastforce
  next
    assume "length ss = 1 \<or> 2 \<le> length ss"
    then show ?case
    proof
      assume "length ss = 1"
      then obtain s'' where "ss = [s'']"
        by (metis One_nat_def length_0_conv length_Suc_conv)
      obtain l' where "w = [l']"
        by (metis One_nat_def Suc_length_conv \<open>length ss = 1\<close> \<open>length ss = length w\<close> length_0_conv)
      have "([s] @ [s'], [l]) \<in> path_with_word"
        by (simp add: LTS.path_with_word.path_with_word_step path_with_word_step.hyps(2))
      have "P ([s] @ [s']) [l]"
        by (metis append_Cons append_Nil path_with_word.path_with_word_refl path_with_word_step.hyps(2) path_with_word_step.prems(1) path_with_word_step.prems(2))
      have "P [s, s', s''] [l, l']"
        using path_with_word_step(5)[of "[s]" s' "[l]" l' s'' ]
        using \<open>([s] @ [s'], [l]) \<in> path_with_word\<close> \<open>P ([s] @ [s']) [l]\<close> \<open>ss = [s'']\<close> \<open>w = [l']\<close> path_with_word.cases path_with_word_step.hyps(1) by auto
      then show "P (s # s' # ss) (l # w)"
        by (simp add: \<open>ss = [s'']\<close> \<open>w = [l']\<close>) 
    next
      assume "2 \<le> length ss"
      then show "P (s # s' # ss) (l # w)"
        sorry
    qed
  qed
qed


inductive transition_of :: "('state, 'label) transition \<Rightarrow> 'state list * 'label list \<Rightarrow> bool" where
  "transition_of (s1,\<gamma>,s2) (s1#s2#ss, \<gamma>#w)"
| "transition_of (s1,\<gamma>,s2) (ss, w) \<Longrightarrow> transition_of (s1,\<gamma>,s2) (s#ss, \<mu>#w)"

lemma path_with_word_induct_non_empty_word: "(x10, x20, x30, x40) \<in> transition_star_states \<Longrightarrow> x20 \<noteq> [] \<Longrightarrow>
(\<And>p \<gamma> q'. (p, \<gamma>, q') \<in> transition_relation \<Longrightarrow> P p [\<gamma>] [p, q'] q') \<Longrightarrow>
(\<And>p \<gamma> q' w ss q. (p, \<gamma>, q') \<in> transition_relation \<Longrightarrow> w \<noteq> [] \<Longrightarrow> (q', w, ss, q) \<in> transition_star_states \<Longrightarrow> P q' w ss q \<Longrightarrow> P p (\<gamma> # w) (p # ss) q) \<Longrightarrow> P x10 x20 x30 x40"
proof (induction rule: transition_star_states.induct)
  case (transition_star_states_refl p)
  then show ?case by auto
next
  case (transition_star_states_step p \<gamma> q' w ss q)
  then show ?case
    by (smt (verit, ccfv_SIG) list.distinct(1) transition_star_states.cases)
qed
                                                  
lemma path_with_word_not_empty[simp]: "\<not>([],w) \<in> path_with_word"
  using LTS.path_with_word.cases by blast
  
lemma transition_star_path_with_word:
  assumes "(p, w, q) \<in> transition_star"
  shows "\<exists>ss. hd ss = p \<and> last ss = q \<and> (ss, w) \<in> path_with_word"
  using assms
proof (induction rule: transition_star.inducts)
  case (transition_star_refl p)
  then show ?case
    by (meson LTS.path_with_word.path_with_word_refl last.simps list.sel(1))
next
  case (transition_star_step p \<gamma> q' w q)
  then show ?case
    by (metis LTS.path_with_word.simps hd_Cons_tl last_ConsR list.discI list.sel(1))
qed

lemma transition_star_transition_star_states:
  assumes "(p, w, q) \<in> transition_star"
  shows "\<exists>ss. (p, w, ss, q) \<in> transition_star_states"
  using assms 
proof (induction rule: transition_star.induct)
  case (transition_star_refl p)
  then show ?case by auto
next
  case (transition_star_step p \<gamma> q' w q)
  then show ?case
    by (meson LTS.transition_star_states_step)
qed

lemma transition_star_states_transition_star:
  assumes "(p, w, ss, q) \<in> transition_star_states"
  shows "(p, w, q) \<in> transition_star"
  using assms 
proof (induction rule: transition_star_states.induct)
  case (transition_star_states_refl p)
  then show ?case by auto
next
  case (transition_star_states_step p \<gamma> q' w q)
  then show ?case
    by (meson LTS.transition_star.transition_star_step)
qed

lemma path_with_word_transition_star:
  assumes "(ss, w) \<in> path_with_word"
  assumes "length ss \<noteq> 0"
  shows "(hd ss, w, last ss) \<in> transition_star"
  using assms
proof (induction rule: path_with_word.inducts)
  case (path_with_word_refl s)
  show ?case
    by simp 
next
  case (path_with_word_step s' ss w s l)
  then show ?case
    using LTS.transition_star.transition_star_step by fastforce
qed

lemma path_with_word_transition_star_Cons:
  assumes "(s1#ss@[s2], w) \<in> path_with_word"
  shows "(s1, w, s2) \<in> transition_star"
  using assms path_with_word_transition_star by force 

lemma path_with_word_transition_star_Singleton:
  assumes "([s2], w) \<in> path_with_word"
  shows "(s2, [], s2) \<in> transition_star"
  using assms path_with_word_transition_star by force

lemma transition_star_split:
  assumes "(p'', u1 @ w1, q) \<in> transition_star"
  shows "\<exists>q1. (p'', u1, q1) \<in> transition_star \<and> (q1, w1, q) \<in> transition_star"
using assms proof(induction u1 arbitrary: p'')
  case Nil
  then show ?case by auto
next
  case (Cons a u1)
  then show ?case
    by (metis LTS.transition_star.transition_star_step LTS.transition_star_cons append_Cons)
qed

end

lemma counting:
  "count (transitions_of' ((hdss1,ww1,ss1,lastss1))) (s1, \<gamma>, s2) = count (transitions_of ((ss1,ww1))) (s1, \<gamma>, s2)"
  by force

lemma transition_star_states_length:
  assumes "(p, u, u_ss, p1) \<in> LTS.transition_star_states A"
  shows "length u_ss = Suc (length u)"
  using assms
proof (induction rule: LTS.transition_star_states.induct[OF assms(1)])
  case (1 p)
  then show ?case
    by simp
next
  case (2 p \<gamma> q' w ss q)
  then show ?case
    by simp
qed

lemma transition_star_states_last:
  assumes "(p, u, u_ss, p1) \<in> LTS.transition_star_states A"
  shows "p1 = last u_ss"
  using assms 
proof (induction rule: LTS.transition_star_states.induct[OF assms(1)])
  case (1 p)
  then show ?case
    by simp
next
  case (2 p \<gamma> q' w ss q)
  then show ?case
    using LTS.transition_star_states.cases by force
qed

lemma transition_star_states_hd:
  assumes "(q', v, v_ss, q) \<in> LTS.transition_star_states B"
  shows "q' = hd v_ss"
  using assms 
proof (induction rule: LTS.transition_star_states.induct[OF assms(1)])
  case (1 p)
  then show ?case
    by simp
next
  case (2 p \<gamma> q' w ss q)
  then show ?case
    by force
qed

lemma count_append_path_with_word_\<gamma>:
  assumes "length (ss1) = Suc (length (ww1))"
  assumes "ss2 \<noteq> []"
  shows "count (transitions_of (((ss1,ww1),\<gamma>') @\<^sup>\<gamma> (ss2,ww2))) (s1, \<gamma>, s2) =
         count (transitions_of (ss1,ww1)) (s1, \<gamma>, s2) + (if s1 = last ss1 \<and> s2 = hd ss2 \<and> \<gamma> = \<gamma>' then 1 else 0) + count (transitions_of (ss2,ww2)) (s1, \<gamma>, s2)"
using assms proof (induction ww1 arbitrary: ss1)
  case Nil
  note Nil_outer = Nil
  obtain s where s_p: "ss1 = [s]"
    by (metis Suc_length_conv length_0_conv local.Nil(1))
  then show ?case
  proof (cases ss2)
    case Nil
    then show ?thesis
      using assms by blast
  next
    case (Cons s2' ss2')
    then show ?thesis 
    proof (cases "s1 = s2'")
      case True
      then show ?thesis
        by (simp add: local.Cons s_p)
    next
      case False
      then show ?thesis
        using s_p local.Cons by fastforce
    qed
  qed
next
  case (Cons w ww11)
  obtain s2' ss2' where a: "ss2 = s2' # ss2'"
    by (meson assms list.exhaust)
  obtain s1' ss1' where b: "ss1 = s1' # ss1'"
    by (meson Cons.prems(1) length_Suc_conv)
  show ?case
    using Cons a b by (smt (z3) Suc_length_conv add.assoc append_Cons append_path_with_word_\<gamma>.simps last_ConsR length_Cons list.simps(3) plus_multiset.rep_eq transitions_of.simps(1))
qed

lemma count_append_path_with_word:
  assumes "length (ss1) = Suc (length (ww1))"
  assumes "ss2 \<noteq> []"
  assumes "last ss1 = hd ss2"
  shows "count (transitions_of (((ss1,ww1)) @\<acute> (ss2,ww2))) (s1, \<gamma>, s2) =
         count (transitions_of (ss1,ww1)) (s1, \<gamma>, s2) + count (transitions_of (ss2,ww2)) (s1, \<gamma>, s2)"
using assms proof (induction ww1 arbitrary: ss1)
  case Nil
  note Nil_outer = Nil
  obtain s where s_p: "ss1 = [s]"
    by (metis Suc_length_conv length_0_conv local.Nil(1))
  then show ?case
  proof (cases ss2)
    case Nil
    then show ?thesis
      using assms by blast
  next
    case (Cons s2' ss2')
    then show ?thesis 
    proof (cases "s1 = s2'")
      case True
      then show ?thesis
        using local.Cons s_p
        using Nil_outer(3) by auto 
    next
      case False
      then show ?thesis
        using s_p local.Cons
        using Nil_outer(3) by fastforce
    qed
  qed
next
  case (Cons w ww11)
  obtain s2' ss2' where a: "ss2 = s2' # ss2'"
    by (meson assms list.exhaust)
  obtain s1' ss1' where b: "ss1 = s1' # ss1'"
    by (meson Cons.prems(1) length_Suc_conv)
  show ?case
    using Cons 
    using Suc_length_conv add.assoc append_Cons  last_ConsR  list.simps(3) plus_multiset.rep_eq transitions_of.simps(1) by (smt (z3) append_path_with_word.simps)
qed

lemma count_append_transition_star_states_\<gamma>:
  assumes "length (ss1) = Suc (length (ww1))"
  assumes "ss2 \<noteq> []"
  shows "count (transitions_of' (((hdss1,ww1,ss1,lastss1),\<gamma>') @@\<^sup>\<gamma> (hdss2,ww2,ss2,lastss2))) (s1, \<gamma>, s2) =
         count (transitions_of' (hdss1,ww1,ss1,lastss1)) (s1, \<gamma>, s2) + (if s1 = last ss1 \<and> s2 = hd ss2 \<and> \<gamma> = \<gamma>' then 1 else 0) + count (transitions_of' (hdss2,ww2,ss2,lastss2)) (s1, \<gamma>, s2)"
  using assms count_append_path_with_word_\<gamma> by force

lemma count_append_transition_star_states:
  assumes "length (ss1) = Suc (length (ww1))"
  assumes "ss2 \<noteq> []"
  assumes "last ss1 = hd ss2"
  shows "count (transitions_of' (((hdss1,ww1,ss1,lastss1)) @@\<acute> (hdss2,ww2,ss2,lastss2))) (s1, \<gamma>, s2) =
         count (transitions_of' (hdss1,ww1,ss1,lastss1)) (s1, \<gamma>, s2) + count (transitions_of' (hdss2,ww2,ss2,lastss2)) (s1, \<gamma>, s2)"
  using count_append_path_with_word[OF assms(1) assms(2) assms(3), of ww2 s1 \<gamma> s2] by auto


lemma LTS_transition_star_mono:
  "mono LTS.transition_star"
proof (rule, rule)
  fix pwq :: "'a \<times> 'b list \<times> 'a"
  fix ts ts' :: "('a, 'b) transition set"
  assume sub: "ts \<subseteq> ts'"
  assume awb_ts: "pwq \<in> LTS.transition_star ts"
  then obtain p w q where pwq_p: "pwq = (p, w, q)"
    using prod_cases3 by blast
  then have "(p, w, q) \<in> LTS.transition_star ts"
    using awb_ts by auto
  then have "(p, w, q) \<in>  LTS.transition_star ts'"
  proof(induction w arbitrary: p)
    case Nil
    then show ?case
      by (metis LTS.transition_star.transition_star_refl LTS.transition_star_empty)
  next
    case (Cons \<gamma> w)
    then show ?case
      by (meson LTS.transition_star.simps LTS.transition_star_cons sub subsetD)
  qed
  then show "pwq \<in> LTS.transition_star ts'"
    unfolding pwq_p .
qed

lemma count_next_0:
  assumes "count (transitions_of (s # s' # ss, l # w)) (p1, \<gamma>, q') = 0"
  shows "count (transitions_of (s' # ss, w)) (p1, \<gamma>, q') = 0"
  using assms by (cases "s = p1 \<and> l = \<gamma> \<and> s' = q'") auto

lemma count_next_hd:
  assumes "count (transitions_of (s # s' # ss, l # w)) (p1, \<gamma>, q') = 0"
  shows "(s, l, s') \<noteq> (p1, \<gamma>, q')"
  using assms by auto

lemma count_empty_zero: "count (transitions_of' (p, [], [p_add], p_add)) (p1, \<gamma>, q') = 0"
  by simp

lemma count_transitions_of'_tails:
  assumes "(p, \<gamma>', q'_add) \<noteq> (p1, \<gamma>, q')"
  shows "count (transitions_of' (p, \<gamma>' # w, p # q'_add # ss_rest, q)) (p1, \<gamma>, q') = count (transitions_of' (q'_add, w, q'_add # ss_rest, q)) (p1, \<gamma>, q')"
  using assms by (cases w) auto
  
lemma avoid_count_zero:
  assumes "(p, w, ss, q) \<in> LTS.transition_star_states Aiminus1"
  assumes "(p1, \<gamma>, q') \<notin> Aiminus1"
  assumes "Ai = Aiminus1 \<union> {(p1, \<gamma>, q')}"
  shows "count (transitions_of' (p, w, ss, q)) (p1, \<gamma>, q') = 0"
  using assms
proof(induction arbitrary: p rule: LTS.transition_star_states.induct[OF assms(1)])
  case (1 p_add p)
  then show ?case
    by auto
next
  case (2 p_add \<gamma>' q'_add w ss q p)
  then have p_add_p: "p_add = p"
    by (meson LTS.transition_star_states.cases list.inject)
  show ?case
    by (metis "2.IH" "2.hyps"(1) "2.hyps"(2) LTS.transition_star_states.cases assms(2) assms(3) count_transitions_of'_tails transitions_of'.simps)
qed

section\<open>LTS init\<close>

locale LTS_init = LTS transition_relation for transition_relation :: "('state, 'label) transition set" +
  fixes r :: 'state
begin

abbreviation initial :: "'state \<Rightarrow> bool" where
  "initial == (\<lambda>r'. r' = r)"

end

find_theorems "(@@\<acute>)"

end