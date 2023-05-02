theory MonoidLTS
  imports "LTS" "MonoidClosure"
begin


\<comment> \<open>If the @{typ 'label} of a LTS is a monoid, we can express the monoid product of labels over a path.\<close>
locale monoidLTS = LTS transition_relation 
  for transition_relation :: "('state, 'label::monoid_mult) transition set"
begin
definition l_step_relp  :: "'state \<Rightarrow> 'label \<Rightarrow> 'state \<Rightarrow> bool" ("(_)/ \<Midarrow> (_)/ \<Rightarrow> (_)/" [70,70,80] 80) where
  "c \<Midarrow>l\<Rightarrow> c' \<longleftrightarrow> (c, l, c') \<in> transition_relation"
abbreviation monoid_star_relp :: "'state \<Rightarrow> 'label \<Rightarrow> 'state \<Rightarrow> bool" ("(_)/ \<Midarrow> (_)/ \<Rightarrow>\<^sup>* (_)/" [90,90,100] 100) where
  "c \<Midarrow>l\<Rightarrow>\<^sup>* c' \<equiv> (monoid_rtranclp l_step_relp) c l c'"
definition monoid_star :: "('state \<times> 'label \<times> 'state) set" where
  "monoid_star = {(c,l,c'). c \<Midarrow>l\<Rightarrow>\<^sup>* c'}"
end

lemma monoid_star_is_monoid_rtrancl[simp]: "monoidLTS.monoid_star = monoid_rtrancl"
  unfolding monoidLTS.monoid_star_def monoidLTS.l_step_relp_def monoid_rtrancl_def by simp

lemma monoidLTS_monoid_star_mono:
  "mono monoidLTS.monoid_star"
  using monoid_star_is_monoid_rtrancl monoid_rtrancl_is_mono
  by simp


\<comment> \<open>If the @{typ 'label} of a LTS is a dioid with additive and multiplicative identities, 
    we can express the meet-over-all-paths value as a generalization of pre-star and post-star.\<close>
locale dioidLTS = monoidLTS transition_relation 
  for transition_relation :: "('state, 'label::dioid_one_zero) transition set"
begin

definition SumInf :: "'weight set \<Rightarrow> 'weight" ("\<^bold>\<Sum>") where
  "\<^bold>\<Sum> W = undefined W"

lemma singleton_sum[simp]: "\<^bold>\<Sum> {w} = w"
  sorry



definition weight_pre_star :: "('state \<Rightarrow> 'label) \<Rightarrow> ('state \<Rightarrow> 'label)" where
  "weight_pre_star C c = \<^bold>\<Sum>{l*(C c') | l c'. c \<Midarrow>l\<Rightarrow>\<^sup>* c'}"
definition weight_post_star :: "('state \<Rightarrow> 'label) \<Rightarrow> ('state \<Rightarrow> 'label)" where
  "weight_post_star C c = \<^bold>\<Sum>{(C c')*l | c' l. c' \<Midarrow>l\<Rightarrow>\<^sup>* c}"
end


end