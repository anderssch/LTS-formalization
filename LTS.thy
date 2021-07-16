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

fun transition_list' :: "'state * 'label list * 'state list * 'state \<Rightarrow> ('state, 'label) transition list" where
  "transition_list' (p,w,ss,q) = transition_list (ss, w)"

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

lemma path_with_word_length:
  assumes "(ss, w) \<in> path_with_word"
  shows "length ss = length w + 1"
  using assms 
proof (induction rule: LTS.path_with_word.induct[OF assms(1)])
  case (1 s)
  then show ?case by auto
next
  case (2 ss s w l s')
  then show ?case by auto
qed

lemma path_with_word_butlast:
  assumes "(ss, w) \<in> path_with_word"
  assumes "length ss \<ge> 2"
  shows "(butlast ss, butlast w) \<in> path_with_word"
using assms proof (induction rule: path_with_word.induct)
case (path_with_word_refl s)
  then show ?case
    by force
next
  case (path_with_word_step s' ss w s l)
  then show ?case
    by (smt (z3) LTS.path_with_word.path_with_word_step LTS.path_with_word_length One_nat_def Suc_1 Suc_inject Suc_leI Suc_le_mono butlast.simps(2) le_less length_0_conv length_Cons list.distinct(1) list.size(4) path_with_word.path_with_word_refl) 
qed


lemma transition_butlast:
  assumes "(ss, w) \<in> path_with_word"
  assumes "length ss \<ge> 2"
  shows "(last (butlast ss), last w, last ss) \<in> transition_relation"
using assms proof (induction rule: path_with_word.induct)
  case (path_with_word_refl s)
  then show ?case
    by force 
next
  case (path_with_word_step s' ss w s l)
  then show ?case
    by (smt (z3) LTS.path_with_word_length One_nat_def Suc_1 Suc_inject Suc_leI Suc_le_mono butlast.simps(2) last.simps le_less length_0_conv length_Cons list.distinct(1) list.size(4))
qed


lemma path_with_word_induct_reverse: 
  "(ss, w) \<in> path_with_word \<Longrightarrow>
   (\<And>s. P [s] []) \<Longrightarrow>
   (\<And>ss s w l s'. (ss @ [s], w) \<in> path_with_word \<Longrightarrow> P (ss @ [s]) w \<Longrightarrow> (s, l, s') \<in> transition_relation \<Longrightarrow> P (ss @ [s, s']) (w @ [l])) \<Longrightarrow>
   P ss w"
proof (induction "length ss" arbitrary: ss w)
  case 0
  then show ?case
    by (metis LTS.path_with_word_length Suc_eq_plus1 Zero_not_Suc)
next
  case (Suc n)

  show ?case
  proof (cases "n = 0")
    case True
    then show ?thesis
      by (metis LTS.path_with_word_length Suc.hyps(2) Suc.prems(1) Suc.prems(2) Suc_eq_plus1 Suc_inject Suc_length_conv length_0_conv)
  next
    case False
    define ss' where "ss' = butlast (butlast ss)"
    define s where "s = last (butlast ss)"
    define s' where "s' = last ss"
    define w' where "w' = butlast w"
    define l where "l = last w"

    have "length ss \<ge> 2"
      using False Suc.hyps(2) by linarith

    then have s_split: "ss' @ [s, s'] = ss"
      by (metis One_nat_def Suc_1 Suc_le_mono Zero_not_Suc append.assoc append.simps(1) append_Cons append_butlast_last_id le_less length_append_singleton list.size(3) s'_def s_def ss'_def zero_order(3))

    have w_split: "w' @ [l] = w"
      by (metis LTS.path_with_word_length Suc.prems(1) add.commute butlast.simps(2) butlast_append l_def length_0_conv length_Suc_conv list.simps(3) plus_1_eq_Suc s_split snoc_eq_iff_butlast w'_def)

    have ss'w'_path: "(ss' @ [s], w') \<in> path_with_word"
      using Suc(3) path_with_word_butlast
      by (metis (no_types, lifting) \<open>2 \<le> length ss\<close> butlast.simps(2) butlast_append list.simps(3) s_split w'_def)

    have tr: "(s, l, s') \<in> transition_relation"
      using Suc(3) s'_def s_def l_def transition_butlast \<open>2 \<le> length ss\<close> by presburger 

    have nl: "n = length (ss' @ [s])"
      by (metis LTS.path_with_word_length Suc.hyps(2) Suc.prems(1) Suc_eq_plus1 length_append_singleton nat.inject ss'w'_path w_split)

    have "P (ss' @ [s]) w'"
      using Suc(1)[of "ss' @ [s]" w', OF nl ss'w'_path Suc(4)] Suc(5) by metis

    then have "P (ss' @ [s, s']) (w' @ [l])"
      using Suc(5)[of ss' s w' l s'] ss'w'_path tr by auto
    then show ?thesis
      using s_split w_split by auto
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

lemma transition_star_states_append:
  assumes "(p2, w2, w2_ss, q') \<in> transition_star_states"
  assumes "(q', v, v_ss, q) \<in> transition_star_states"
  shows "(p2, w2 @ v, w2_ss @ tl v_ss, q) \<in> transition_star_states"
using assms proof (induction rule: LTS.transition_star_states.induct[OF assms(1)])
  case (1 p)
  then show ?case
    by (smt (verit, best) LTS.transition_star_states.cases append_Cons append_Nil list.sel(3))
next
  case (2 p \<gamma> q' w ss q)
  then show ?case
    using LTS.transition_star_states.transition_star_states_step by fastforce 
qed

lemma transition_star_states_length:
  assumes "(p, u, u_ss, p1) \<in> transition_star_states"
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
  assumes "(p, u, u_ss, p1) \<in> transition_star_states"
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
  assumes "(q', v, v_ss, q) \<in> transition_star_states"
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

lemma xxxxxxx: 
  assumes "(p, \<gamma>#w_rest, ss, q) \<in> transition_star_states"
  shows "\<exists>s \<gamma>'. (s, \<gamma>', q) \<in> transition_relation"
using assms proof (induction w_rest arbitrary: ss p \<gamma>)
  case Nil
  then show ?case
    by (metis LTS.transition_star_empty LTS.transition_star_states_transition_star transition_star_cons)
next
  case (Cons a w_rest)
  then show ?case
    by (meson LTS.transition_star_cons LTS.transition_star_states_transition_star transition_star_transition_star_states)
qed

lemma askdjfklasjflksa:
  assumes "(p, w, ss, q) \<in> transition_star_states"
  shows "(ss,w) \<in> path_with_word"
using assms proof (induction rule: transition_star_states.induct)
  case (transition_star_states_refl p)
  then show ?case by auto
next
  case (transition_star_states_step p \<gamma> q' w ss q)
  then show ?case
    by (metis LTS.transition_star_states.simps path_with_word.path_with_word_step) 
qed

lemma askdjfklasjflksa2:
  assumes "(ss,w) \<in> path_with_word"
  assumes "p = hd ss"
  assumes "q = last ss"
  shows "(p, w, ss, q) \<in> transition_star_states"
using assms proof (induction arbitrary: p q rule: path_with_word.induct)
  case (path_with_word_refl s)
  then show ?case
    by simp
next
  case (path_with_word_step s' ss w s l)
  then show ?case
    using transition_star_states.transition_star_states_step by auto
qed

lemma append_path_with_word_path_with_word:
  assumes "last \<gamma>2ss = hd v_ss"
  assumes "(\<gamma>2ss, \<gamma>2\<epsilon>) \<in> path_with_word"
  assumes "(v_ss, v) \<in> path_with_word"
  shows "(\<gamma>2ss, \<gamma>2\<epsilon>) @\<acute> (v_ss, v) \<in> path_with_word"
  by (metis LTS.askdjfklasjflksa append_path_with_word.simps askdjfklasjflksa2 assms(1) assms(2) assms(3) transition_star_states_append)

definition sources :: "'state set" where
  "sources = {p. \<nexists>q \<gamma>. (q, \<gamma>, p) \<in> transition_relation}"

end


lemma counting:
  "count (transitions_of' ((hdss1,ww1,ss1,lastss1))) (s1, \<gamma>, s2) = count (transitions_of ((ss1,ww1))) (s1, \<gamma>, s2)"
  by force

lemma count_append_path_with_word_\<gamma>:
  assumes "length ss1 = Suc (length ww1)"
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
  obtain s2' ss2' where s2'_ss2'_p: "ss2 = s2' # ss2'"
    by (meson assms list.exhaust)
  obtain s1' ss1' where s1'_ss1'_p: "ss1 = s1' # ss1'"
    by (meson Cons.prems(1) length_Suc_conv)
  show ?case
    using Cons s2'_ss2'_p s1'_ss1'_p by (smt (z3) Suc_length_conv add.assoc append_Cons append_path_with_word_\<gamma>.simps last_ConsR length_Cons list.simps(3) plus_multiset.rep_eq transitions_of.simps(1))
qed

lemma count_append_path_with_word:
  assumes "length ss1 = Suc (length ww1)"
  assumes "ss2 \<noteq> []"
  assumes "last ss1 = hd ss2"
  shows "count (transitions_of (((ss1, ww1)) @\<acute> (ss2, ww2))) (s1, \<gamma>, s2) =
         count (transitions_of (ss1, ww1)) (s1, \<gamma>, s2) + count (transitions_of (ss2, ww2)) (s1, \<gamma>, s2)"
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
  show ?case
    using Cons Suc_length_conv add.assoc append_Cons  last_ConsR  list.simps(3) plus_multiset.rep_eq transitions_of.simps(1) by (smt (z3) append_path_with_word.simps)
qed

lemma count_append_transition_star_states_\<gamma>:
  assumes "length (ss1) = Suc (length (ww1))"
  assumes "ss2 \<noteq> []"
  shows "count (transitions_of' (((hdss1,ww1,ss1,lastss1),\<gamma>') @@\<^sup>\<gamma> (hdss2,ww2,ss2,lastss2))) (s1, \<gamma>, s2) =
         count (transitions_of' (hdss1,ww1,ss1,lastss1)) (s1, \<gamma>, s2) + (if s1 = last ss1 \<and> s2 = hd ss2 \<and> \<gamma> = \<gamma>' then 1 else 0) + count (transitions_of' (hdss2,ww2,ss2,lastss2)) (s1, \<gamma>, s2)"
  using assms count_append_path_with_word_\<gamma> by force

lemma count_append_transition_star_states_\<gamma>_BETTER:
  assumes "(hdss1,ww1,ss1,lastss1) \<in> LTS.transition_star_states A"
  assumes "(hdss2,ww2,ss2,lastss2) \<in> LTS.transition_star_states A"
  shows "count (transitions_of' (((hdss1,ww1,ss1,lastss1),\<gamma>') @@\<^sup>\<gamma> (hdss2,ww2,ss2,lastss2))) (s1, \<gamma>, s2) =
         count (transitions_of' (hdss1,ww1,ss1,lastss1)) (s1, \<gamma>, s2) + (if s1 = last ss1 \<and> s2 = hd ss2 \<and> \<gamma> = \<gamma>' then 1 else 0) + count (transitions_of' (hdss2,ww2,ss2,lastss2)) (s1, \<gamma>, s2)"
proof -
  have "length (ss1) = Suc (length (ww1))"
    by (meson LTS.transition_star_states_length assms(1))
  moreover
  have "ss2 \<noteq> []"
    by (metis LTS.transition_star_states.simps assms(2) list.discI)
  ultimately 
  show ?thesis
    using count_append_transition_star_states_\<gamma> by metis
qed

lemma count_append_transition_star_states:
  assumes "length (ss1) = Suc (length (ww1))"
  assumes "ss2 \<noteq> []"
  assumes "last ss1 = hd ss2"
  shows "count (transitions_of' (((hdss1,ww1,ss1,lastss1)) @@\<acute> (hdss2,ww2,ss2,lastss2))) (s1, \<gamma>, s2) =
         count (transitions_of' (hdss1,ww1,ss1,lastss1)) (s1, \<gamma>, s2) + count (transitions_of' (hdss2,ww2,ss2,lastss2)) (s1, \<gamma>, s2)"
  using count_append_path_with_word[OF assms(1) assms(2) assms(3), of ww2 s1 \<gamma> s2] by auto

lemma count_append_transition_star_statesBETTER:
  assumes "(hdss1,ww1,ss1,lastss1) \<in> LTS.transition_star_states A"
  assumes "(lastss1,ww2,ss2,lastss2) \<in> LTS.transition_star_states A"
  shows "count (transitions_of' (((hdss1,ww1,ss1,lastss1)) @@\<acute> (lastss1,ww2,ss2,lastss2))) (s1, \<gamma>, s2) =
         count (transitions_of' (hdss1,ww1,ss1,lastss1)) (s1, \<gamma>, s2) + count (transitions_of' (lastss1,ww2,ss2,lastss2)) (s1, \<gamma>, s2)"
proof -
  have "length (ss1) = Suc (length (ww1))"
    by (meson LTS.transition_star_states_length assms(1))
  moreover
  have "last ss1 = hd ss2"
    by (metis LTS.transition_star_states_hd LTS.transition_star_states_last assms(1) assms(2))
  moreover
  have "ss2 \<noteq> []"
    by (metis LTS.transition_star_states_length Zero_not_Suc assms(2) list.size(3))
  ultimately
  show ?thesis
    using count_append_transition_star_states assms by auto
qed


lemma LTS_transition_star_mono:
  "mono LTS.transition_star"
proof (rule, rule)
  fix pwq :: "'a \<times> 'b list \<times> 'a"
  fix ts ts' :: "('a, 'b) transition set"
  assume sub: "ts \<subseteq> ts'"
  assume pwq_ts: "pwq \<in> LTS.transition_star ts"
  then obtain p w q where pwq_p: "pwq = (p, w, q)"
    using prod_cases3 by blast
  then have "(p, w, q) \<in> LTS.transition_star ts"
    using pwq_ts by auto
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
    by (metis "2.IH" "2.hyps"(1) "2.hyps"(2) LTS.transition_star_states.cases assms(2) count_transitions_of'_tails transitions_of'.simps)
qed

lemma lemma_3_2_a'_Aux:
  assumes "(ss, w) \<in> LTS.path_with_word Ai"
  assumes "0 = count (transitions_of (ss, w)) (p1, \<gamma>, q')"
  assumes "Ai = Aiminus1 \<union> {(p1, \<gamma>, q')}"
  shows "(ss, w) \<in> LTS.path_with_word Aiminus1"
  using assms
proof (induction rule: LTS.path_with_word.induct[OF assms(1)])
  case (1 s)
  then show ?case
    by (simp add: LTS.path_with_word.path_with_word_refl)
next
  case (2 s' ss w s l)
  from 2(5) have "0 = count (transitions_of (s' # ss, w)) (p1, \<gamma>, q')"
    using count_next_0 by auto
  then have s'_ss_w_Aiminus1: "(s' # ss, w) \<in> LTS.path_with_word Aiminus1"
    using 2 by auto
  have "(s, l, s') \<in> Aiminus1"
    using 2(2,5) assms(3) by force
  then show ?case 
    using s'_ss_w_Aiminus1 by (simp add: LTS.path_with_word.path_with_word_step) 
qed

lemma lemma_3_2_a'_Aux_3:
 (* This proof is a bit messy. *)
  assumes "(p, w, ss ,q) \<in> LTS.transition_star_states Ai"
  assumes "0 = count (transitions_of' (p, w, ss, q)) (p1, \<gamma>, q')"
  assumes "Ai = Aiminus1 \<union> {(p1, \<gamma>, q')}"
  shows "(p, w, ss, q) \<in> LTS.transition_star_states Aiminus1"
  using assms
proof (induction arbitrary: p rule: LTS.transition_star_states.induct[OF assms(1)])
  case (1 p)
  then show ?case
    by (metis LTS.transition_star_states.simps list.distinct(1))
next
  case (2 p' \<gamma>' q'' w ss q)
  have p_is_p': "p' = p"
    by (meson "2.prems"(1) LTS.transition_star_states.cases list.inject)
  { 
    assume len: "length ss > 0" 
    have not_found: "(p, \<gamma>', hd ss) \<noteq> (p1, \<gamma>, q')"
      using LTS.transition_star_states.cases count_next_hd list.sel(1) transitions_of'.simps
      using 2(4) 2(5) by (metis len hd_Cons_tl length_greater_0_conv) 
    have hdAI: "(p, \<gamma>', hd ss) \<in> Ai"
      by (metis "2.hyps"(1) "2.hyps"(2) LTS.transition_star_states.cases list.sel(1) p_is_p')
    have t_Aiminus1: "(p, \<gamma>', hd ss) \<in> Aiminus1"
      using 2 hdAI not_found by force 
    have "(p, \<gamma>' # w, p' # ss, q) \<in> LTS.transition_star_states (Aiminus1 \<union> {(p1, \<gamma>, q')})"
      using "2.prems"(1) assms(3) by fastforce
    have ss_hd_tl: "hd ss # tl ss = ss"
      using len hd_Cons_tl by blast
    moreover
    have "(hd ss, w, ss, q) \<in> LTS.transition_star_states Ai"
      using ss_hd_tl "2.hyps"(2) using LTS.transition_star_states.cases
      by (metis list.sel(1))
    ultimately have "(hd ss, w, ss, q) \<in> LTS.transition_star_states Aiminus1"
      using ss_hd_tl using "2.IH" "2.prems"(2) not_found assms(3) p_is_p' count_transitions_of'_tails by (metis) 
    from this t_Aiminus1 have ?case
      using LTS.transition_star_states.intros(2)[of p \<gamma>' "hd ss" Aiminus1 w ss q] using p_is_p' by auto
  }
  moreover
  { 
    assume "length ss = 0"
    then have ?case
      using "2.hyps"(2) LTS.transition_star_states.cases by force
  }
  ultimately show ?case
    by auto
qed

lemma lemma_3_2_a'_Aux_4:
 (* This proof is a bit messy. *)
  assumes "(p, w, ss ,q) \<in> LTS.transition_star_states Ai"
  assumes "0 = count (transitions_of' (p, w, ss, q)) (p1, \<gamma>, q')"
  assumes "Ai = Aiminus1 \<union> {(p1, \<gamma>, q')}"
  shows "(p, w, q) \<in> LTS.transition_star Aiminus1"
  using assms lemma_3_2_a'_Aux_3 by (metis LTS.transition_star_states_transition_star) 

lemma split_at_first_t:
  assumes "(p, w, ss, q) \<in> LTS.transition_star_states Ai"
  assumes "Suc j' = count (transitions_of' (p, w, ss, q)) (p1, \<gamma>, q')"
  assumes "(p1, \<gamma>, q') \<notin> Aiminus1"
  assumes "Ai = Aiminus1 \<union> {(p1, \<gamma>, q')}"
  shows "\<exists>u v u_ss v_ss. 
           ss = u_ss @ v_ss \<and> 
           w = u @ [\<gamma>] @ v \<and> 
           (p, u, u_ss, p1) \<in> LTS.transition_star_states Aiminus1 \<and> 
           (p1, [\<gamma>], q') \<in> LTS.transition_star Ai \<and> 
           (q', v, v_ss, q) \<in> LTS.transition_star_states Ai \<and>
           (p, w, ss, q) = ((p, u, u_ss, p1),\<gamma>) @@\<^sup>\<gamma> (q', v, v_ss,q)"
  using assms
proof(induction arbitrary: p rule: LTS.transition_star_states.induct[OF assms(1)])
  case (1 p_add p)
  from 1(2) have "False"
    using count_empty_zero by auto
  then show ?case
    by auto
next
  case (2 p_add \<gamma>' q'_add w ss q p)
  then have p_add_p: "p_add = p"
    by (meson LTS.transition_star_states.cases list.inject)
  from p_add_p have p_Ai: "(p, \<gamma>', q'_add) \<in> Ai"
    using 2(1) by auto
  from p_add_p have p_\<gamma>'_w_ss_Ai: "(p, \<gamma>' # w, p # ss, q) \<in> LTS.transition_star_states Ai"
    using 2(4) by auto  
  from p_add_p have count_p_\<gamma>'_w_ss: "Suc j' = count (transitions_of' (p, \<gamma>' # w, p # ss, q)) (p1, \<gamma>, q')"
    using 2(5) by auto
  show ?case
  proof(cases "(p, \<gamma>', q'_add) = (p1, \<gamma>, q')")
    case True
    define u :: "'b list" where "u = []"
    define u_ss :: "'a list" where "u_ss = [p]"
    define v where "v = w"
    define v_ss where "v_ss = ss"
    have "(p, u, u_ss, p1) \<in> LTS.transition_star_states Aiminus1"
      unfolding u_def u_ss_def using LTS.transition_star_states.intros
      using True by fastforce 
    have "(p1, [\<gamma>], q') \<in> LTS.transition_star Ai"
      using p_Ai by (metis LTS.transition_star.transition_star_refl LTS.transition_star.transition_star_step True) 
    have "(q', v, v_ss, q) \<in> LTS.transition_star_states Ai"
      using 2(2) True v_def v_ss_def by blast
    show ?thesis
      using Pair_inject True \<open>(p, u, u_ss, p1) \<in> LTS.transition_star_states Aiminus1\<close> \<open>(p1, [\<gamma>], q') \<in> LTS.transition_star Ai\<close> \<open>(q', v, v_ss, q) \<in> LTS.transition_star_states Ai\<close> append_Cons p_add_p self_append_conv2 u_def u_ss_def v_def v_ss_def
      by (metis (no_types, hide_lams) append_transition_star_states_\<gamma>.simps)
  next
    case False
    have "hd ss = q'_add"
      by (metis LTS.transition_star_states.cases 2(2) list.sel(1))
    from this False have g: "Suc j' = count (transitions_of' (q'_add, w, ss, q)) (p1, \<gamma>, q')"
      using count_p_\<gamma>'_w_ss by (cases ss) auto
    have "\<exists>u_ih v_ih u_ss_ih v_ss_ih. ss = u_ss_ih @ v_ss_ih \<and> w = u_ih @ [\<gamma>] @ v_ih \<and> (q'_add, u_ih, u_ss_ih, p1) \<in> LTS.transition_star_states Aiminus1 \<and> (p1, [\<gamma>], q') \<in> LTS.transition_star Ai \<and> (q', v_ih, v_ss_ih, q) \<in> LTS.transition_star_states Ai"
      using 2(3)[of q'_add, OF 2(2) g 2(6) 2(7)] by auto
    then obtain u_ih v_ih u_ss_ih v_ss_ih where splitting_p:
      "ss = u_ss_ih @ v_ss_ih" 
      "w = u_ih @ [\<gamma>] @ v_ih"
      "(q'_add, u_ih, u_ss_ih, p1) \<in> LTS.transition_star_states Aiminus1" 
      "(p1, [\<gamma>], q') \<in> LTS.transition_star Ai" 
      "(q', v_ih, v_ss_ih, q) \<in> LTS.transition_star_states Ai"
      by metis
    define v where "v = v_ih"
    define v_ss where "v_ss = v_ss_ih"
    define u where "u = \<gamma>' # u_ih"
    define u_ss where "u_ss = p # u_ss_ih"
    have "p_add # ss = u_ss @ v_ss"
      by (simp add: p_add_p splitting_p(1) u_ss_def v_ss_def)
    have "\<gamma>' # w = u @ [\<gamma>] @ v"
      using splitting_p(2) u_def v_def by auto
    have "(p, u, u_ss, p1) \<in> LTS.transition_star_states Aiminus1"
      using False LTS.transition_star_states.transition_star_states_step 2(7) p_Ai splitting_p(3) u_def u_ss_def by fastforce
    have "(p1, [\<gamma>], q') \<in> LTS.transition_star Ai"
      by (simp add: splitting_p(4))
    have "(q', v, v_ss, q) \<in> LTS.transition_star_states Ai"
      by (simp add: splitting_p(5) v_def v_ss_def)
    show ?thesis
      using \<open>(p, u, u_ss, p1) \<in> LTS.transition_star_states Aiminus1\<close> \<open>(q', v, v_ss, q) \<in> LTS.transition_star_states Ai\<close> \<open>\<gamma>' # w = u @ [\<gamma>] @ v\<close> \<open>p_add # ss = u_ss @ v_ss\<close> splitting_p(4)
      by auto
  qed
qed

lemma transition_star_states_mono:
  assumes "(p, w, ss, q) \<in> LTS.transition_star_states A1"
  assumes "A1 \<subseteq> A2"
  shows "(p, w, ss, q) \<in> LTS.transition_star_states A2"
  using assms 
proof (induction rule: LTS.transition_star_states.induct[OF assms(1)])
  case (1 p)
  then show ?case
    by (simp add: LTS.transition_star_states.transition_star_states_refl)
next
  case (2 p \<gamma> q' w ss q)
  then show ?case
    by (meson LTS.transition_star_states.transition_star_states_step in_mono)
qed

lemma count_combine_transition_star_states:
  assumes "ss = u_ss @ v_ss \<and> w = u @ [\<gamma>] @ v"
  assumes "t = (p1, \<gamma>, q')"
  assumes "(p, u, u_ss, p1) \<in> LTS.transition_star_states A"
  assumes "(q', v, v_ss, q) \<in> LTS.transition_star_states B"
  shows "count (transitions_of' (p, w, ss, q)) t = count (transitions_of' (p, u, u_ss, p1)) t + 1 + count (transitions_of' (q', v, v_ss, q)) t"
proof -
  have v_ss_non_empt: "v_ss \<noteq> []"
    using LTS.transition_star_states.cases assms by force

  have u_ss_l: "length u_ss = Suc (length u)"
    using assms LTS.transition_star_states_length by metis

  have p1_u_ss:  "p1 = last u_ss"
    using assms LTS.transition_star_states_last by metis

  have q'_v_ss: "q' = hd v_ss"
    using assms LTS.transition_star_states_hd by metis

  have one: "(if p1 = last u_ss \<and> q' = hd v_ss then 1 else 0) = 1"
    using p1_u_ss q'_v_ss by auto

  from count_append_transition_star_states_\<gamma>[of u_ss u v_ss p q \<gamma> q' v q p1 ] show ?thesis
    using assms(1) assms(2) assms(3) by (auto simp add: assms(3) one u_ss_l v_ss_non_empt)
qed

lemma count_combine_transition_star_states_BETTER:
  assumes "t = (p1, \<gamma>, q')"
  assumes "(p, u, u_ss, p1) \<in> LTS.transition_star_states A"
  assumes "(q', v, v_ss, q) \<in> LTS.transition_star_states B"
  shows "count (transitions_of' (((p, u, u_ss, p1),\<gamma>) @@\<^sup>\<gamma> (q', v, v_ss, q))) t = 
        count (transitions_of' (p, u, u_ss, p1)) t + 1 + count (transitions_of' (q', v, v_ss, q)) t"
  by (metis append_transition_star_states_\<gamma>.simps assms count_combine_transition_star_states)


lemma transition_list_reversed_simp:
  assumes "length ss = length w"
  shows "transition_list (ss @ [s, s'], w @ [l]) = (transition_list (ss@[s],w)) @ [(s,l,s')]"
  using assms
proof (induction ss arbitrary: w)
  case Nil
  then show ?case
    by auto 
next
  case (Cons a ss)
  define w' where "w' = tl w"
  define l' where "l' = hd w"
  have w_split: "l' # w' = w"
    by (metis Cons.prems l'_def length_0_conv list.distinct(1) list.exhaust_sel w'_def)
  then have "length ss = length w'"
    using Cons.prems by force
  then have "transition_list (ss @ [s, s'], w' @ [l]) = transition_list (ss @ [s], w') @ [(s, l, s')]"
    using Cons(1)[of w'] by auto
  then have "transition_list (a # ss @ [s, s'], l' # w' @ [l]) = transition_list (a # ss @ [s], l' # w') @ [(s, l, s')]"
    by (cases ss) auto 
  then show ?case
    using w_split by auto
qed


lemma LTS_transition_star_mono':
  "mono LTS.transition_star_states"
  by (smt (z3) LTS.transition_star_states_def case_prodE mem_Collect_eq monoI subsetI transition_star_states_mono)

lemma path_with_word_mono':
  assumes "(ss, w) \<in> LTS.path_with_word A1"
  assumes "A1 \<subseteq> A2"
  shows "(ss, w) \<in> LTS.path_with_word A2"
  by (meson LTS.askdjfklasjflksa LTS.askdjfklasjflksa2 assms(1) assms(2) transition_star_states_mono)


lemma LTS_path_with_word_mono'':
  "mono LTS.path_with_word"
  by (smt (verit, ccfv_SIG) LTS.path_with_word_def case_prodE mem_Collect_eq monoI subsetI path_with_word_mono')

section \<open>LTS init\<close>

locale LTS_init = LTS transition_relation for transition_relation :: "('state, 'label) transition set" +
  fixes r :: 'state
begin

abbreviation initial :: "'state \<Rightarrow> bool" where
  "initial == (\<lambda>r'. r' = r)"

end

section \<open>LTS with epsilon\<close>

locale LTS_\<epsilon> =  LTS transition_relation for transition_relation :: "('state, 'label option) transition set"
begin

abbreviation \<epsilon> :: "'label option" where
  "\<epsilon> == None"

inductive_set transition_star_\<epsilon> :: "('state * 'label list * 'state) set" where
  transition_star_\<epsilon>_refl[iff]: "(p, [], p) \<in> transition_star_\<epsilon>"
| transition_star_\<epsilon>_step_\<gamma>: "(p, Some \<gamma>, q') \<in> transition_relation \<Longrightarrow> (q',w,q) \<in> transition_star_\<epsilon>
                           \<Longrightarrow> (p, \<gamma>#w, q) \<in> transition_star_\<epsilon>"
| transition_star_\<epsilon>_step_\<epsilon>: "(p, \<epsilon>, q') \<in> transition_relation \<Longrightarrow> (q',w,q) \<in> transition_star_\<epsilon>
                           \<Longrightarrow> (p, w, q) \<in> transition_star_\<epsilon>"

inductive_cases transition_star_\<epsilon>_empty [elim]: "(p, [], q) \<in> transition_star_\<epsilon>"
inductive_cases transition_star_cons_\<epsilon>: "(p, \<gamma>#w, q) \<in> transition_star"

definition remove_\<epsilon> :: "'label option list \<Rightarrow> 'label list" where
  "remove_\<epsilon> w = map the (removeAll \<epsilon> w)"

definition \<epsilon>_exp :: "'label option list \<Rightarrow> 'label list \<Rightarrow> bool" where
  "\<epsilon>_exp w' w \<longleftrightarrow> map the (removeAll \<epsilon> w') = w"

lemma epsilon_lemma:
  assumes "(p, w, q) \<in> transition_star"
  shows "(p, map the (removeAll \<epsilon> w), q) \<in> transition_star_\<epsilon>"
using assms proof (induction rule: transition_star.induct)
  case (transition_star_refl p)
  then show ?case
    by simp
next
  case (transition_star_step p \<gamma> q' w q)
  show ?case
  proof (cases \<gamma>)
    case None
    then show ?thesis 
      using transition_star_step by (simp add: transition_star_\<epsilon>.transition_star_\<epsilon>_step_\<epsilon>)
  next
    case (Some \<gamma>')
    then show ?thesis 
      using transition_star_step by (simp add: transition_star_\<epsilon>.transition_star_\<epsilon>_step_\<gamma>)
  qed
qed

lemma epsilon_lemma2:
  assumes "(p, w, q) \<in> transition_star_\<epsilon>"
  shows "\<exists>w'. \<epsilon>_exp w' w \<and> (p, w', q) \<in> transition_star"
  using assms 
proof (induction rule: transition_star_\<epsilon>.induct)
  case (transition_star_\<epsilon>_refl p)
  then show ?case
    by (metis LTS.transition_star.transition_star_refl \<epsilon>_exp_def list.simps(8) removeAll.simps(1))
next
  case (transition_star_\<epsilon>_step_\<gamma> p \<gamma> q' w q)
  then show ?case
    by (smt (verit, best) LTS.transition_starp.intros(2) LTS.transition_starp_transition_star_eq \<epsilon>_exp_def list.map(2) option.sel option.simps(3) removeAll.simps(2))
next
  case (transition_star_\<epsilon>_step_\<epsilon> p q' w q)
  then show ?case
    by (metis transition_starp.transition_star_step transition_starp_transition_star_eq \<epsilon>_exp_def removeAll.simps(2))
qed

lemma epsilon_lemma3:
  "(p, w, q) \<in> transition_star_\<epsilon> \<longleftrightarrow> (\<exists>w'. \<epsilon>_exp w' w \<and> (p, w', q) \<in> transition_star)"
proof
  assume "(p, w, q) \<in> transition_star_\<epsilon>"
  then show "\<exists>w'. \<epsilon>_exp w' w \<and> (p, w', q) \<in> transition_star"
    using epsilon_lemma2 epsilon_lemma2 epsilon_lemma by auto
next
  assume "\<exists>w'. \<epsilon>_exp w' w \<and> (p, w', q) \<in> transition_star"
  then show "(p, w, q) \<in> transition_star_\<epsilon>"
    using epsilon_lemma2 epsilon_lemma2 epsilon_lemma \<epsilon>_exp_def by auto
qed

lemma \<epsilon>_exp_split':
  assumes "\<epsilon>_exp u_\<epsilon> (\<gamma>1 # u1)"
  shows "\<exists>\<gamma>1_\<epsilon> u1_\<epsilon>. \<epsilon>_exp \<gamma>1_\<epsilon> [\<gamma>1] \<and> \<epsilon>_exp u1_\<epsilon> u1 \<and> u_\<epsilon> = \<gamma>1_\<epsilon> @ u1_\<epsilon>"
  using assms 
proof (induction u_\<epsilon> arbitrary: u1 \<gamma>1)
  case Nil
  then show ?case
    by (metis LTS_\<epsilon>.\<epsilon>_exp_def list.distinct(1) list.simps(8) removeAll.simps(1))
next
  case (Cons a u_\<epsilon>)
  then show ?case
  proof (induction a)
    case None
    then show ?case
      by (smt (verit, ccfv_SIG) LTS_\<epsilon>.\<epsilon>_exp_def append_Cons removeAll.simps(2))
  next
    case (Some \<gamma>1')
    have "\<gamma>1' = \<gamma>1"
      using Some.prems(2) \<epsilon>_exp_def by auto
    have "\<epsilon>_exp u_\<epsilon> u1"
      using Some.prems(2) \<epsilon>_exp_def by force
    show ?case
    proof (cases u1)
      case Nil
      then show ?thesis
        by (metis Some.prems(2) \<epsilon>_exp_def append_Nil2 list.simps(8) removeAll.simps(1))
    next
      case (Cons a list)
      then show ?thesis
        using LTS_\<epsilon>.\<epsilon>_exp_def \<open>\<epsilon>_exp u_\<epsilon> u1\<close> \<open>\<gamma>1' = \<gamma>1\<close> by force
    qed
  qed
qed

lemma remove_\<epsilon>_append_dist:
  "remove_\<epsilon> (w @ w') = remove_\<epsilon> w @ remove_\<epsilon> w'"
proof (induction w)
  case Nil
  then show ?case
    by (simp add: LTS_\<epsilon>.remove_\<epsilon>_def) 
next
  case (Cons a w)
  then show ?case
    by (simp add: LTS_\<epsilon>.remove_\<epsilon>_def)
qed

lemma ffffffff:
  assumes "remove_\<epsilon> w = remove_\<epsilon> (Some \<gamma>' # tl w)"
  shows "\<gamma>' # remove_\<epsilon> (tl w) = remove_\<epsilon> w"
  using assms unfolding remove_\<epsilon>_def by auto


lemma transition_star_states_transition_star_\<epsilon>:
  assumes "(p, w, ss, q) \<in> transition_star_states"
  shows "(p, LTS_\<epsilon>.remove_\<epsilon> w, q) \<in> transition_star_\<epsilon>"
  by (metis LTS_\<epsilon>.epsilon_lemma assms remove_\<epsilon>_def transition_star_states_transition_star)

(* I doubt a bit that this definition is useful *)
inductive_set transition_star_states_\<epsilon> :: "('state * 'label list * 'state list * 'state) set" where
  transition_star_states_\<epsilon>_refl[iff]: "(p,[],[p],p) \<in> transition_star_states_\<epsilon>"
| transition_star_states_\<epsilon>_step_\<gamma>: "(p,Some \<gamma>,q') \<in> transition_relation \<Longrightarrow> (q',w,ss,q) \<in> transition_star_states_\<epsilon>
                           \<Longrightarrow> (p, \<gamma>#w, p#ss, q) \<in> transition_star_states_\<epsilon>"
| transition_star_states_\<epsilon>_step_\<epsilon>: "(p, \<epsilon> ,q') \<in> transition_relation \<Longrightarrow> (q',w,ss,q) \<in> transition_star_states_\<epsilon>
                           \<Longrightarrow> (p, w, p#ss, q) \<in> transition_star_states_\<epsilon>"

(* I doubt a bit that this definition is useful *)
inductive_set path_with_word_\<epsilon> :: "('state list * 'label list) set" where
  path_with_word_\<epsilon>_refl[iff]: "([s],[]) \<in> path_with_word_\<epsilon>"
| path_with_word_\<epsilon>_step_\<gamma>: "(s'#ss, w) \<in> path_with_word_\<epsilon> \<Longrightarrow> (s,Some l,s') \<in> transition_relation \<Longrightarrow> (s#s'#ss,l#w) \<in> path_with_word_\<epsilon>"
| path_with_word_\<epsilon>_step_\<epsilon>: "(s'#ss, w) \<in> path_with_word_\<epsilon> \<Longrightarrow> (s,\<epsilon>,s') \<in> transition_relation \<Longrightarrow> (s#s'#ss,w) \<in> path_with_word_\<epsilon>"

end

lemma LTS_\<epsilon>_transition_star_\<epsilon>_mono:
  "mono LTS_\<epsilon>.transition_star_\<epsilon>"
proof (rule, rule)
  fix pwq :: "'a \<times> 'b list \<times> 'a"
  fix ts ts' :: "('a, 'b option) transition set"
  assume sub: "ts \<subseteq> ts'"
  assume pwq_ts: "pwq \<in> LTS_\<epsilon>.transition_star_\<epsilon> ts"
  then obtain p w q where pwq_p: "pwq = (p, w, q)"
    using prod_cases3 by blast
  then have x: "(p, w, q) \<in> LTS_\<epsilon>.transition_star_\<epsilon> ts"
    using pwq_ts by auto
  then have "(\<exists>w'. LTS_\<epsilon>.\<epsilon>_exp w' w \<and> (p, w', q) \<in> LTS.transition_star ts)"
    using LTS_\<epsilon>.epsilon_lemma3[of p w q ts] by auto
  then have "(\<exists>w'. LTS_\<epsilon>.\<epsilon>_exp w' w \<and> (p, w', q) \<in> LTS.transition_star ts')"
    using LTS_transition_star_mono sub
    using monoD by blast
  then have "(p, w, q) \<in>  LTS_\<epsilon>.transition_star_\<epsilon> ts'"
    using LTS_\<epsilon>.epsilon_lemma3[of p w q ts'] by auto
  then show "pwq \<in> LTS_\<epsilon>.transition_star_\<epsilon> ts'"
    unfolding pwq_p .
qed

end