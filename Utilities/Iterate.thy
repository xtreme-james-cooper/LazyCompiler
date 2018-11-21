theory Iterate
imports Main
begin

inductive iter :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool)" for f where
  iter_refl [simp]: "iter f a a"
| iter_step [simp]: "f a b \<Longrightarrow> iter f b c \<Longrightarrow> iter f a c"

lemma [elim]: "iter f a b \<Longrightarrow> iter f b c \<Longrightarrow> iter f a c"
  by (induction a b rule: iter.induct) simp_all

end