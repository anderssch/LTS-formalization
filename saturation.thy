theory saturation imports Main "~~/src/HOL/Hoare/HeapSyntax" 
begin

(* Since both pre* and post* are described as saturation procedures, we here define a generalised
   saturation procedure in the hope that we can reuse some proofs. *)

(* Note: I did not manage to complete this... *)

definition saturate_step where
  "saturate_step f S \<equiv> S \<union> Collect (f S)"

definition start_from where
  "start_from init f \<equiv> \<lambda>s. init \<union> f s"

definition saturate where
  "saturate f init \<equiv> lfp (start_from init (saturate_step f))"

(* Some simple lemmas that I think can help us...*)

lemma saturate_step_mono: "mono f \<Longrightarrow> mono (saturate_step f)"
  unfolding saturate_step_def mono_def
  by blast

lemma start_from_mono: "mono f \<Longrightarrow> mono (start_from init f)"
  unfolding start_from_def mono_def
  by blast
lemma start_from_init_mono: "mono (\<lambda>init. start_from init f)"
  unfolding start_from_def mono_def
  using le_fun_def by fastforce
lemma start_from_subseteq: "init \<subseteq> (start_from init f) rel"
  by (simp add: start_from_def)
lemma start_from_lfp_subseteq: "init \<subseteq> lfp (start_from init f)"
  by (metis Un_subset_iff lfp_greatest start_from_def)  


lemma saturate_mono: "mono f \<Longrightarrow> mono (start_from init (saturate_step f))"
  by (simp add: saturate_step_mono start_from_mono)

lemma saturate_subseteq: "init \<subseteq> saturate f init"
  using start_from_lfp_subseteq
  unfolding saturate_def
  by fast



(* From here it is mostly some desperate attempts to define good induction rules on the saturation procedure.
   Not really successful.  *)


lemma mono_f_intersect_implication:
  assumes "mono f"
      and "f (X \<inter> {x. x \<in> X \<longrightarrow> P x}) x"
    shows "f {x \<in> X. P x} x"
proof -
  have "(X \<inter> {x. x \<in> X \<longrightarrow> P x}) \<subseteq> {x \<in> X. P x}" by auto
  thus ?thesis using assms unfolding mono_def by auto
qed



lemma saturate_induct [case_names mono elem base step]:
  fixes f :: "'a set \<Rightarrow> 'a \<Rightarrow> bool"
  assumes mono_f: "mono f"
    and elem: "x \<in> saturate f init"
    and base: "\<And>t. t \<in> init \<Longrightarrow> P t"
    and step: "\<And>t. \<lbrakk>f {x \<in> saturate f init. P x} t\<rbrakk> \<Longrightarrow> P t"
  shows "P x"
  using assms unfolding saturate_def
proof (induct rule: lfp_induct_set[where ?f="start_from init (saturate_step f)"])
  case 1
  then show ?case using elem unfolding saturate_def by simp
next
  case 2
  then show ?case using mono_f saturate_mono by fast
next
  case (3 x)
  then show ?case 
    unfolding saturate_def start_from_def saturate_step_def
    by auto (drule_tac ?X="lfp (\<lambda>s. init \<union> (s \<union> Collect (f s)))" in mono_f_intersect_implication[OF mono_f], blast)
qed

lemma saturate_induct2 [case_names mono elem base step]:
  fixes f :: "'a set \<Rightarrow> 'a \<Rightarrow> bool"
  assumes mono_f: "mono f"
    and elem: "x \<in> saturate f init"
    and base: "\<And>t. t \<in> init \<Longrightarrow> P t"
    and step: "\<And>S t. \<lbrakk>S \<subseteq> saturate f init; f {x \<in> S. P x} t\<rbrakk> \<Longrightarrow> P t"
  shows "P x"
  using assms unfolding saturate_def
  apply (induct rule: lfp_ordinal_induct[OF saturate_mono[OF mono_f]])
  unfolding start_from_def saturate_step_def
   apply auto
  subgoal for S
    apply (cases "x \<in> init", blast)
    oops

(*lemma saturate_converse_induct':
  fixes f :: "'a set \<Rightarrow> 'a \<Rightarrow> bool"
  assumes mono_f: "mono f"
    and mono_g: "mono g"
    and elem: "x \<in> g (saturate f init)"
    and base: "x \<in> g init \<Longrightarrow> P x (g init)"
    and step: "\<And>S. \<lbrakk>x \<in> g (start_from init (saturate_step f) S) \<or> P x (g (start_from init (saturate_step f) S))\<rbrakk>
                     \<Longrightarrow> x \<in> g S \<or> P x (g S)"
  shows "P x (g init)"
using assms 
proof (induct rule: saturate_induct[OF mono_f])
  case elem
  then show ?case sorry
next
  case (base t)
  then show ?case sorry
next
  case (step t)
  then show ?case sorry
qed*)

lemma saturate_converse_induct:
  fixes f :: "'a set \<Rightarrow> 'a \<Rightarrow> bool"
  assumes mono_f: "mono f"
    and mono_g: "mono g"
    and elem: "x \<in> g (saturate f init)"
    and base: "\<And>x. x \<in> g init \<Longrightarrow> P x (g init)"
    and step: "\<And>x S. \<lbrakk>x \<in> g (start_from init (saturate_step f) S) \<or> P x (g (start_from init (saturate_step f) S))\<rbrakk>
                     \<Longrightarrow> x \<in> g S \<or> P x (g S)"
  shows "P x (g init)"
  using assms unfolding saturate_def
proof (induct rule: lfp_ordinal_induct[OF saturate_mono[OF mono_f]])
  case (1 S)
  then show ?case
  proof -
    have "x \<in> g S \<or> P x (g S)" using 1
      by blast
    thus ?case using 1
      apply (cases "x \<in> g S", blast)
      apply (cases "x \<in> g init", blast)
      apply clarsimp
      unfolding start_from_def saturate_step_def mono_def
      apply -
      apply (cases "x \<in> g (Collect (f S))")
       (* apply auto *)
      oops
next
  case (2 M)
  then show ?case oops
qed
thm start_from_def saturate_step_def


lemma "mono f \<Longrightarrow> x \<notin> f X \<Longrightarrow> x \<in> f (X \<union> Y) \<Longrightarrow> x \<in> f Y" unfolding mono_def
  try
  oops

(*
lemma saturate_converse_induct2:
  fixes f :: "'a set \<Rightarrow> 'a \<Rightarrow> bool"
  assumes mono_f: "mono f"
    and mono_g: "mono g"
    and base: "P (g (saturate f init))"
    and step: "\<And>S. \<lbrakk>P (g (start_from init (saturate_step f) S))\<rbrakk> \<Longrightarrow> P (g S)"
  shows "\<exists>x \<in> (g init). P x"
  using assms unfolding saturate_def start_from_def saturate_step_def
  apply -
  oops
*)

(*
definition saturate_step_some where
  "saturate_step_some f S \<equiv> (if (\<exists>t. t \<notin> S \<and> f S t) then insert (SOME t. t \<notin> S \<and> f S t) S else S)"
*)


(* Trying to define it as an algorithm instead... yeah, well, trying... *)
lemma "VARS (S::'a set) S' init 
    {mono f \<and> 
    (\<forall>t. t \<in> init \<longrightarrow> P t) \<and>
    (\<forall>S t. f {x \<in> S. P x} t \<longrightarrow> P t)}
    S:={};
    S':=init;
    WHILE S \<noteq> S' INV {f S x \<or> x \<in> S} DO
      S:=S';
      S':=insert (SOME x. f S x) S
    OD
    {x \<in> S \<longrightarrow> P x}"
  apply vcg_simp
  oops


end