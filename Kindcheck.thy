theory Kindcheck
imports Type
begin

inductive kinding :: "nat \<Rightarrow> type \<Rightarrow> bool" (infix "\<turnstile>\<^sub>k" 60) where
  k_var [simp]: "x < \<Delta> \<Longrightarrow> \<Delta> \<turnstile>\<^sub>k TyVar x"
| k_arrow [simp]: "\<Delta> \<turnstile>\<^sub>k t\<^sub>1 \<Longrightarrow> \<Delta> \<turnstile>\<^sub>k t\<^sub>2 \<Longrightarrow> \<Delta> \<turnstile>\<^sub>k Arrow t\<^sub>1 t\<^sub>2"
| k_record [simp]: "(\<forall>t \<in> set ts. \<Delta> \<turnstile>\<^sub>k t) \<Longrightarrow> \<Delta> \<turnstile>\<^sub>k Record ts"
| k_variant [simp]: "(\<forall>t \<in> set ts. \<Delta> \<turnstile>\<^sub>k t) \<Longrightarrow> \<Delta> \<turnstile>\<^sub>k Variant ts"
| k_inductive [simp]: "Suc \<Delta> \<turnstile>\<^sub>k t \<Longrightarrow> \<Delta> \<turnstile>\<^sub>k Inductive t"
| k_forall [simp]: "Suc \<Delta> \<turnstile>\<^sub>k t \<Longrightarrow> \<Delta> \<turnstile>\<^sub>k Forall t"

inductive_cases [elim]: "\<Delta> \<turnstile>\<^sub>k TyVar x"
inductive_cases [elim]: "\<Delta> \<turnstile>\<^sub>k Arrow t\<^sub>1 t\<^sub>2"
inductive_cases [elim]: "\<Delta> \<turnstile>\<^sub>k Record ts"
inductive_cases [elim]: "\<Delta> \<turnstile>\<^sub>k Variant ts"
inductive_cases [elim]: "\<Delta> \<turnstile>\<^sub>k Inductive t"
inductive_cases [elim]: "\<Delta> \<turnstile>\<^sub>k Forall t"

lemma [simp]: "\<Delta> \<turnstile>\<^sub>k t \<Longrightarrow> Suc \<Delta> \<turnstile>\<^sub>k incr\<^sub>t\<^sub>t x t"
  by (induction \<Delta> t arbitrary: x rule: kinding.induct) simp_all

lemma [simp]: "Suc \<Delta> \<turnstile>\<^sub>k t \<Longrightarrow> \<Delta> \<turnstile>\<^sub>k t' \<Longrightarrow> x \<le> \<Delta> \<Longrightarrow> \<Delta> \<turnstile>\<^sub>k subst\<^sub>t\<^sub>t x t' t"
  by (induction "Suc \<Delta>" t arbitrary: \<Delta> x t' rule: kinding.induct) simp_all

end