theory Kindcheck
imports Type "../Utilities/Vector"
begin

inductive kinding :: "kind list \<Rightarrow> type \<Rightarrow> kind \<Rightarrow> bool" (infix "\<turnstile>\<^sub>k _ :" 60) where
  k_var [simp]: "lookup \<Delta> x = Some k \<Longrightarrow> \<Delta> \<turnstile>\<^sub>k TyVar x : k"
| k_arrow [simp]: "\<Delta> \<turnstile>\<^sub>k t\<^sub>1 : Star \<Longrightarrow> \<Delta> \<turnstile>\<^sub>k t\<^sub>2 : Star \<Longrightarrow> \<Delta> \<turnstile>\<^sub>k Arrow t\<^sub>1 t\<^sub>2 : Star"
| k_record [simp]: "(\<forall>t \<in> set ts. \<Delta> \<turnstile>\<^sub>k t : Star) \<Longrightarrow> \<Delta> \<turnstile>\<^sub>k Record ts : Star"
| k_variant [simp]: "(\<forall>t \<in> set ts. \<Delta> \<turnstile>\<^sub>k t : Star) \<Longrightarrow> \<Delta> \<turnstile>\<^sub>k Variant ts : Star"
| k_inductive [simp]: "insert_at 0 k \<Delta> \<turnstile>\<^sub>k t : Star \<Longrightarrow> \<Delta> \<turnstile>\<^sub>k Inductive k t : Star"
| k_forall [simp]: "insert_at 0 k \<Delta> \<turnstile>\<^sub>k t : Star \<Longrightarrow> \<Delta> \<turnstile>\<^sub>k Forall k t : Star"

inductive_cases [elim]: "\<Delta> \<turnstile>\<^sub>k TyVar x : k"
inductive_cases [elim]: "\<Delta> \<turnstile>\<^sub>k Arrow t\<^sub>1 t\<^sub>2 : k"
inductive_cases [elim]: "\<Delta> \<turnstile>\<^sub>k Record ts : k"
inductive_cases [elim]: "\<Delta> \<turnstile>\<^sub>k Variant ts : k"
inductive_cases [elim]: "\<Delta> \<turnstile>\<^sub>k Inductive k' t : k"
inductive_cases [elim]: "\<Delta> \<turnstile>\<^sub>k Forall k' t : k"

lemma [simp]: "\<Delta> \<turnstile>\<^sub>k t : k \<Longrightarrow> x \<le> length \<Delta> \<Longrightarrow> insert_at x k' \<Delta> \<turnstile>\<^sub>k incr\<^sub>t\<^sub>t x t : k"
  by (induction \<Delta> t k arbitrary: x rule: kinding.induct) simp_all

lemma [simp]: "insert_at x k' \<Delta> \<turnstile>\<^sub>k t : k \<Longrightarrow> \<Delta> \<turnstile>\<^sub>k t' : k' \<Longrightarrow> x \<le> length \<Delta> \<Longrightarrow> 
    \<Delta> \<turnstile>\<^sub>k subst\<^sub>t\<^sub>t x t' t : k"
  proof (induction "insert_at x k' \<Delta>" t k arbitrary: \<Delta> x t' rule: kinding.induct) 
  case (k_var y k)
    thus ?case by (induction y) auto
  qed simp_all

end