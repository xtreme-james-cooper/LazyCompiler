theory Vector
imports Main
begin

fun insert_at :: "nat \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "insert_at 0 a' as = a' # as"
| "insert_at (Suc x) a' [] = undefined"
| "insert_at (Suc x) a' (a # as) = a # insert_at x a' as"

fun lookup :: "nat \<Rightarrow> 'a list \<Rightarrow> 'a option" where
  "lookup x [] = None"
| "lookup 0 (a # as) = Some a"
| "lookup (Suc x) (a # as) = lookup x as"

lemma [simp]: "x \<le> length as \<Longrightarrow> length (insert_at x a as) = Suc (length as)"
  by (induction x a as rule: insert_at.induct) simp_all

lemma [simp]: "x \<le> length as \<Longrightarrow> lookup x (insert_at x a as) = Some a"
  by (induction x a as rule: insert_at.induct) simp_all

lemma [simp]: "x \<le> length as \<Longrightarrow> y < x \<Longrightarrow> lookup y (insert_at x a as) = lookup y as"
  proof (induction x a as arbitrary: y rule: insert_at.induct)
  case 3
    thus ?case by (induction y) simp_all
  qed simp_all

lemma [simp]: "x \<le> length as \<Longrightarrow> x \<le> y \<Longrightarrow> lookup (Suc y) (insert_at x a as) = lookup y as"
  proof (induction x a as arbitrary: y rule: insert_at.induct)
  case 3
    thus ?case by (induction y) simp_all
  qed simp_all

lemma [elim]: "lookup x as = Some a \<Longrightarrow> x < length as"
  by (induction x as rule: lookup.induct) simp_all

end