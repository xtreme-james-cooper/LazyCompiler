theory Misc
imports Main
begin

primrec map_fst :: "('a \<Rightarrow> 'c) \<Rightarrow> 'a \<times> 'b \<Rightarrow> 'c \<times> 'b" where
  "map_fst f (a, b) = (f a, b)"

lemma [simp]: "(x::nat) \<ge> y \<Longrightarrow> \<exists>z. x = y + z"
  proof (induction x arbitrary: y)
  case Suc
    thus ?case by (induction y) simp_all
  qed simp_all

end