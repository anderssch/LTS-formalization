theory morten_pre_star imports morten_saturation morten_pds (* "~~/src/HOL/Hoare/HeapSyntax" *)
begin                      

(* Here we define the saturation rule for pre* (pre_star), and try to prove the correctness of the saturation procedure. *)

(* This is the saturation rule defined on page 32 in http://www.lsv.fr/Publis/PAPERS/PDF/schwoon-phd02.pdf *)
definition pre_star_step :: "transition set \<Rightarrow> transition \<Rightarrow> bool" where
  "pre_star_step rel \<equiv> \<lambda>(p,\<gamma>,q). (\<exists>p' w. (p,\<gamma>) \<hookrightarrow> (p',w) \<and> (p', op_labels w, q) \<in> (transition_star rel))"

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