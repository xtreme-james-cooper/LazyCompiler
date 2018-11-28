theory Misc
imports Main
begin

primrec map_fst :: "('a \<Rightarrow> 'c) \<Rightarrow> 'a \<times> 'b \<Rightarrow> 'c \<times> 'b" where
  "map_fst f (a, b) = (f a, b)"

primrec index_of :: "'a \<Rightarrow> 'a list \<Rightarrow> nat" where
  "index_of a [] = undefined"
| "index_of a (a' # as) = (if a = a' then 0 else Suc (index_of a as))"

lemma [simp]: "(x::nat) \<ge> y \<Longrightarrow> \<exists>z. x = y + z"
  proof (induction x arbitrary: y)
  case Suc
    thus ?case by (induction y) simp_all
  qed simp_all

lemma [simp]: "(\<forall>x y. f x = f y \<longrightarrow> x = y) \<Longrightarrow> index_of (f a) (map f as) = index_of a as"
  by (induction as) simp_all

end