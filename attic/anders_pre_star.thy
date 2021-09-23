theory anders_pre_star imports anders_saturation anders_pds (* "~~/src/HOL/Hoare/HeapSyntax" *)
begin                      

(* Here we define the saturation rule for pre* (pre_star), and try to prove the correctness of the saturation procedure. *)

(* This is the saturation rule defined on page 32 in http://www.lsv.fr/Publis/PAPERS/PDF/schwoon-phd02.pdf *)
definition pre_star_step :: "transition set \<Rightarrow> transition \<Rightarrow> bool" where
  "pre_star_step rel \<equiv> \<lambda>(p,\<gamma>,q). (\<exists>p' w. (p,\<gamma>) \<hookrightarrow> (p',w) \<and> (p', op_labels w, q) \<in> (transition_star rel))"

inductive pre_star_step' :: "transition set \<Rightarrow> transition set \<Rightarrow> bool" where
  add_trans: "(p,\<gamma>) \<hookrightarrow> (p',w) \<Longrightarrow> (p', op_labels w, q) \<in> transition_star rel \<Longrightarrow> (p, \<gamma>, q) \<notin> rel \<Longrightarrow> pre_star_step' rel (rel \<union> {(p,\<gamma>,q)})"
(* It is wrong to have "op_labels" in all these. *)

definition pre_star' :: "transition set \<Rightarrow> transition set \<Rightarrow> bool" where
  "pre_star' \<equiv> rtranclp pre_star_step'"

definition saturated' :: "transition set \<Rightarrow> bool" where
  "saturated' A \<equiv> \<nexists>B. pre_star_step' A B"

definition pre_star_lim' :: "transition set \<Rightarrow> transition set \<Rightarrow> bool" where
  "pre_star_lim' A B \<equiv> pre_star' A B \<and> saturated' B"


(* Use this rule in the saturation procedure. *)
definition pre_star_rel where
  "pre_star_rel = saturate pre_star_step"


(* This is what we want to prove: *)
theorem "language (pre_star_rel rel) = pre_star (language rel)"
  oops


lemma pre_star_step_mono[simp]: "mono pre_star_step"
  using transition_star_mono unfolding mono_def pre_star_step_def
  by clarsimp (meson subsetD)

lemma rule_pre_star_saturation: 
  "(p,\<gamma>) \<hookrightarrow> (p',w) \<Longrightarrow> (p', op_labels w, q) \<in> (transition_star rel)
   \<Longrightarrow> (p, \<gamma>, q) \<in> start_from init (saturate_step pre_star_step) rel"
  unfolding saturate_step_def start_from_def pre_star_step_def
  by auto

lemma rule_pre_star_rel: "(p,\<gamma>) \<hookrightarrow> (p',w) \<Longrightarrow> (p', op_labels w, q) \<in> (transition_star (pre_star_rel rel)) 
       \<Longrightarrow> (p, \<gamma>, q) \<in> pre_star_rel rel"
  unfolding pre_star_rel_def saturate_def
  using saturate_mono pre_star_step_mono lfp_fixpoint rule_pre_star_saturation
  by blast

(* This is Lemma 3.1 from page 33 in http://www.lsv.fr/Publis/PAPERS/PDF/schwoon-phd02.pdf *)
(* I managed to prove this one. *)
lemma lemma_3_1:
  assumes "(p',w) \<Rightarrow>\<^sup>* (p,v)"
      and "(p,v) \<in> language rel"
    shows "accepts (pre_star_rel rel) (p',w)"
  using assms unfolding step_starp_def
proof (induct rule: converse_rtranclp_induct)
  case base
  then show ?case
    using accepts_mono saturate_subseteq
    unfolding mono_def pre_star_rel_def language_def
    by auto
next
  case (step y z)
  then show ?case 
    unfolding step_relp_def step_def
    using accepts_unfoldn rule_pre_star_rel accepts_cons
    apply clarsimp
    subgoal for p w
      by (induct w; clarsimp) blast
    done
qed


lemma pre_star_step'_incr: "pre_star_step' A B \<Longrightarrow> A \<subseteq> B"
proof(induction rule: pre_star_step'.inducts)
  case (add_trans p \<gamma> p' w q rel)
  then show ?case 
    by auto
qed

lemma pre_star'_incr: "pre_star' A B \<Longrightarrow> A \<subseteq> B"
  unfolding pre_star'_def proof (induction rule: rtranclp_induct)
  case base
  then show ?case by auto
next
  case (step y z)
  then show ?case
    using pre_star_step'_incr by auto
qed

lemma pre_star'_incr_transition_star:
  "pre_star' A A' \<Longrightarrow> transition_star A \<subseteq> transition_star A'"
  using mono_def pre_star'_incr transition_star_mono by blast

lemma pre_star_lim'_incr_transition_star:
  "pre_star_lim' A A' \<Longrightarrow> transition_star A \<subseteq> transition_star A'"
  by (simp add: pre_star'_incr_transition_star pre_star_lim'_def)

lemma step_relp_non_empty: "step_relp (p',w) (p'',u) \<Longrightarrow> w \<noteq> []"
  by (metis case_prod_conv empty_iff step'.simps(1) step_def step_relp_def)

lemma transition_star_split:
  assumes "(p'', u1 @ w1, q) \<in> transition_star A'"
  shows "\<exists>q1. (p'', u1, q1) \<in> transition_star A' \<and> (q1, w1, q) \<in> transition_star A'"
  sorry

lemma lemma_3_1':
  assumes "(p',w) \<Rightarrow>\<^sup>* (p,v)"
      and "(p,v) \<in> language A"
      and "pre_star_lim' A A'"
    shows "accepts A' (p',w)"
  using assms unfolding step_starp_def
proof (induct rule: converse_rtranclp_induct)
  case base
  then have "\<exists>q\<in>Q. F q \<and> (p, v, q) \<in> transition_star A'"
    unfolding language_def accepts_def using pre_star_lim'_incr_transition_star by auto
  then show ?case
    unfolding accepts_def by auto
next
  case (step p'w p''u)
  define p' where "p' = fst p'w"
  define w  where "w = snd p'w"
  define p'' where "p'' = fst p''u"
  define u  where "u = snd p''u"
  have p'w_def: "p'w = (p', w)"
    using p'_def w_def by auto
  have p''u_def: "p''u = (p'', u)"
    using p''_def u_def by auto

  have a: "accepts A' p''u" 
    using step by auto


  then obtain q where q_p: "q \<in> Q \<and> F q \<and> (p'', u, q) \<in> transition_star A'"
    unfolding accepts_def using p''_def u_def by auto

  have e: "\<exists>\<gamma> w1 u1. w=\<gamma>#w1 \<and> u=op_labels u1@w1 \<and> (p', \<gamma>) \<hookrightarrow> (p'', u1)"
  proof -
    from step(1) obtain \<gamma> w1 where w_exp: "w=\<gamma>#w1"
      unfolding p''u_def step_def p'w_def using step_relp_non_empty using list.exhaust by blast 
    from step(1) have "\<exists>u1. u=op_labels u1@w1 \<and> (p', \<gamma>) \<hookrightarrow> (p'', u1)" 
      unfolding step_relp_def p''u_def
        step_def p'w_def w_exp by auto
    then show "\<exists>\<gamma> w1 u1. w=\<gamma>#w1 \<and> u=op_labels u1@w1 \<and> (p', \<gamma>) \<hookrightarrow> (p'', u1)"
      using w_exp by auto
  qed

  then obtain \<gamma> w1 u1 where w_p: "w=\<gamma>#w1" and u_p: "u=op_labels u1@w1" and u_tran: "(p', \<gamma>) \<hookrightarrow> (p'', u1)"
    by blast
  note \<gamma>_w1_u1_p = w_p u_p u_tran

  have "\<exists>q1. (p'', op_labels u1, q1) \<in> transition_star A' \<and> (q1, w1, q) \<in> transition_star A'"
    using q_p unfolding u_p using transition_star_split by auto
  then obtain q1 where q1_p: "(p'', op_labels u1, q1) \<in> transition_star A' \<and> (q1, w1, q) \<in> transition_star A'"
    by blast
    

  have \<gamma>_w1_u1_p_n: "(p', \<gamma>) \<hookrightarrow> (p'', u1)"
    using \<gamma>_w1_u1_p by blast

  then have "(p', \<gamma>#w1, q) \<in> transition_star A'"
    using transition_star_step q1_p
    by (meson add_trans pre_star_lim'_def saturated'_def step.prems(2))  
  then have t_in_A': "(p', w, q) \<in> transition_star A'"
    using \<gamma>_w1_u1_p by blast

  from q_p t_in_A' have "F q \<and> (p', w, q) \<in> transition_star A'"
    using p'_def w_def by auto
  then show ?case
    unfolding accepts_def p'w_def using q_p by auto
qed



(* Lemma 3.2 on page 34 turned out to be harder to prove. 
   Here goes several failed attempts... *)

lemma lemma_3_2_base: 
  "(p, w, q) \<in> transition_star rel \<Longrightarrow> \<exists>p' w'. (p, w) \<Rightarrow>\<^sup>* (p', w') \<and> (p', w', q) \<in> transition_star rel"
  unfolding step_starp_def
  by auto
lemma lemma_3_2_step:
  "\<lbrakk>(p, w, q) \<in> transition_star (start_from rel_0 (saturate_step f) rel)\<rbrakk> 
        \<Longrightarrow> \<exists>p' w'. (p, w) \<Rightarrow>\<^sup>* (p', w') \<and> (p', w', q) \<in> transition_star rel_0"
  unfolding step_starp_def (*saturate_step_def start_from_def*)
  apply -
  oops

lemma "rel \<subseteq> pre_star_rel rel"
  unfolding pre_star_rel_def saturate_def
  apply clarsimp
  apply (induct rule: lfp_ordinal_induct, fact saturate_mono[OF pre_star_step_mono])
  using start_from_subseteq
   apply fast
  apply clarsimp
  nitpick
  oops

lemma pre_star_rel_mono: "t \<in> transition_star rel \<Longrightarrow> t \<in> transition_star (pre_star_rel rel)"
  using transition_star_mono start_from_lfp_subseteq
  unfolding pre_star_rel_def saturate_def
  by (metis in_mono mono_def)

lemma pre_star_rel_induct: "\<lbrakk>P rel_0; \<And>rel. P rel \<Longrightarrow> P (f rel)\<rbrakk> \<Longrightarrow> P (lfp f)"
  apply -
  quickcheck
  oops

lemma "\<lbrakk>(p, w, q) \<in> transition_star (pre_star_saturation rel_0 rel_i); 
        (p, w, q) \<notin> transition_star rel_i\<rbrakk>
         \<Longrightarrow> \<exists>p' w'. (p, w) \<Rightarrow>\<^sup>* (p', w') \<and> (p', w', q) \<in> transition_star rel_0"
  oops

lemma lemma_3_2_b_aux':
  assumes "\<nexists>q \<gamma> q'. (q, \<gamma>, q') \<in> A \<and> q' \<in> P"
  assumes "(p, w, q) \<in> transition_star A"
  assumes "q \<in> P"
  shows "w = [] \<and> p = q"
using assms(2) assms(1,3) proof (induction)
  case (transition_star_refl p)
  then show ?case by auto
next
  case (transition_star_step p \<gamma> q' w q)
  then show ?case by blast
qed

fun start_of' :: "transition \<Rightarrow> state" where (* TODO: rename *)
  "start_of' (q, \<gamma>, q') = q"

fun end_of' :: "transition \<Rightarrow> state" where (* TODO: rename *)
  "end_of' (q, \<gamma>, q') = q'"

fun sym_of' :: "transition \<Rightarrow> label" where (* TODO: rename *)
  "sym_of' (q, \<gamma>, q') = \<gamma>"

fun consecs' :: "'a list \<Rightarrow> ('a * 'a) set" where
  "consecs' [] = {}"
| "consecs' [y] = {}"
| "consecs' (x#y#xs) = {(x,y)} \<union> consecs' (y#xs)"

lemma lemma_3_2_a':
  assumes "\<nexists>q \<gamma> q'. (q, \<gamma>, q') \<in> A \<and> q' \<in> P"
  assumes "pre_star' A A'"
  assumes "(p, w, q) \<in> transition_star A'"
  shows "\<exists>p' w'. (p', w', q) \<in> transition_star A \<and> (p, w) \<Rightarrow>\<^sup>* (p', w')"
  using assms(2) assms(1,3) unfolding pre_star'_def proof (induction rule: rtranclp_induct)
  case base
  then show ?case
    unfolding step_starp_def by auto
next
  case (step Aiminus1 Ai)
  from step(2) obtain p1 \<gamma> p' w q' where p1_\<gamma>_p'_w_q'_p: "
                       Ai = Aiminus1 \<union> {(p1, \<gamma>, q')} \<and> 
                       (p1, \<gamma>) \<hookrightarrow> (p', w) \<and> 
                       (p', op_labels w, q') \<in> transition_star Aiminus1"
    unfolding pre_star_step'.simps by auto
  define t where "t = (p1, \<gamma>, q')"
  (* I think there is a challenge here.
     In the proof he looks at << p \<midarrow>w\<rightarrow>*_i q >> as if it were a path. But there can be
     several paths like that. So I need to fix one.

     Hack: pick the smallest subset of Ai such that p \<midarrow>w\<rightarrow>*_i q \<in> Ai.

  *)
  
  
  

  then show ?case sorry
qed

  

lemma lemma_3_2:
  assumes "(p, w, q) \<in> transition_star (pre_star_rel rel)"
  shows   "\<exists>p' w'. (p, w) \<Rightarrow>\<^sup>* (p', w') \<and> (p', w', q) \<in> transition_star rel" (* \<and> (q \<in> P_states \<longrightarrow> w' = []) *)
  using assms unfolding pre_star_rel_def saturate_def
proof (induct rule: lfp_ordinal_induct)
  case mono
  then show ?case using saturate_mono by force
next
  case (step S)
  then show ?case by (simp add: lemma_3_2_step)
next
  case (union M)
  then show ?case using assms
    apply (rule_tac ?x="p" in exI)
    apply (rule_tac ?x="w" in exI)
    unfolding step_starp_def
    apply clarsimp
    apply (frule pre_star_rel_mono)
    sorry
qed
thm lfp_ordinal_induct[OF saturate_mono[OF pre_star_sat_step_mono]]
thm lfp_induct_set
lemma lemma_3_2':
  assumes "(p, w, q) \<in> transition_star (pre_star_rel rel)"
  shows   "\<exists>p' w'. (p, w) \<Rightarrow>\<^sup>* (p', w') \<and> (p', w', q) \<in> transition_star rel"
  using assms unfolding pre_star_rel_def saturate_def
  apply (induct rule: lfp_ordinal_induct[OF saturate_mono[OF pre_star_sat_step_mono]])
  apply auto
  apply (simp add: lemma_3_2_step)
  using pre_star_rel_mono
  unfolding pre_star_rel_def
  apply clarsimp
  apply (rule_tac ?x="p" in exI)
  apply (rule_tac ?x="w" in exI)
  unfolding step_starp_def
  apply clarsimp
  oops

lemma lemma_3_2_converse:
  assumes "\<And>p' w'. (p, w) \<Rightarrow>\<^sup>* (p', w') \<Longrightarrow> (p', w', q) \<notin> transition_star rel"
  shows   "(p, w, q) \<notin> transition_star (pre_star_rel rel)"
  using assms unfolding pre_star_rel_def saturate_def
  apply (induct rule: lfp_ordinal_induct[OF saturate_mono[OF pre_star_step_mono]])
   apply clarsimp
  unfolding start_from_def saturate_step_def
   apply safe
   apply simp_all
   defer
  subgoal for M
    apply (cases "rel \<in> M")
    apply auto
   apply (insert lemma_3_2_base)
    oops

lemma lemma_3_2'':
  assumes "(p, w, q) \<in> transition_star (pre_star_rel rel)"
  shows   "\<exists>p' w'. (p, w) \<Rightarrow>\<^sup>* (p', w') \<and> (p', w', q) \<in> transition_star rel"
  using assms unfolding pre_star_rel_def
  thm saturate_converse_induct saturate_converse_induct[OF pre_star_sat_step_mono]
  apply (induct rule: saturate_converse_induct[OF pre_star_sat_step_mono transition_star_mono], assumption)
  using lemma_3_2_base
   apply simp
  apply clarsimp
  apply (simp add: lemma_3_2_step)
  using pre_star_rel_mono
  unfolding pre_star_rel_def
  apply clarsimp
  apply (rule_tac ?x="p" in exI)
  apply (rule_tac ?x="w" in exI)
  unfolding step_starp_def
  apply clarsimp
  oops



(* This proof works, if lemma_3_2_converse can be proven. *)
theorem "language (pre_star_rel rel) = pre_star (language rel)"
  using lemma_3_1 lemma_3_2_converse
  unfolding language_def pre_star_def accepts_def
  by blast



lemma mono_temp[mono]: "mono (\<lambda>p x. (\<exists>t. x = t \<and> t \<in> \<rightarrow>) \<or> (\<exists>t. x = t \<and> pre_star_sat_step {x. p x} t))"
  using pre_star_sat_step_mono
  unfolding mono_def
  by clarsimp (metis Collect_mono_iff rev_predicate1D)

(*
(* inductive and inductive_set cannot prove monocity even though the proof is right above here  *)
inductive rel_pre_starp :: "transition \<Rightarrow> bool" where
  rel_pre_starp_refl[iff]: "t \<in> rel \<Longrightarrow> rel_pre_starp t"
| rel_pre_starp_step: "pre_star_sat {t'. rel_pre_starp t'} t \<Longrightarrow> rel_pre_starp t"

*)
lemma fake_mono: "X \<subseteq> Y \<Longrightarrow> pre_star_sat_step X t \<longrightarrow> pre_star_sat_step Y t" 
  oops 
(* If you 'sorry' this lemma, then the inductive set below works... *)


(* I first tried to define the saturation procedure as an inductive set like this.
   But it is not happy about it. *)
inductive_set rel_pre_star :: "transition set \<Rightarrow> transition set" for rel where
  rel_pre_star_refl[iff]: "t \<in> rel \<Longrightarrow> t \<in> (rel_pre_star rel)"
| rel_pre_star_step: "pre_star_sat_step (rel_pre_star rel) t \<Longrightarrow> t \<in> (rel_pre_star rel)"
monos fake_mono


(* Here I tried something similar with the general saturation procedure. *)
lemma f_mono: "A \<subseteq> B \<Longrightarrow> Collect (f A) \<subseteq> Collect (f B)" 
  oops

inductive_set saturate :: "('a set \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> 'a set" 
  for f :: "'a set \<Rightarrow> 'a \<Rightarrow> bool" and S :: "'a set" where
  "t \<in> S \<Longrightarrow> t \<in> saturate f S" |
  "mono f \<Longrightarrow> f (saturate f S) t \<Longrightarrow> t \<in> saturate f S"
monos f_mono
print_theorems


end