theory Vector
imports Main
begin

fun insert_at :: "nat \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "insert_at 0 a' [] = a' # []"
| "insert_at 0 a' (a # as) = a' # a # as"
| "insert_at (Suc x) a' [] = undefined"
| "insert_at (Suc x) a' (a # as) = a # insert_at x a' as"

fun lookup :: "nat \<Rightarrow> 'a list \<Rightarrow> 'a option" where
  "lookup x [] = None"
| "lookup 0 (a # as) = Some a"
| "lookup (Suc x) (a # as) = lookup x as"

lemma [simp]: "x \<le> length as \<Longrightarrow> length (insert_at x a as) = Suc (length as)"
  by (induction x a as rule: insert_at.induct) simp_all

lemma [simp]: "x \<le> length as \<Longrightarrow> y \<le> x \<Longrightarrow> 
    insert_at y b (insert_at x a as) = insert_at (Suc x) a (insert_at y b as)"
  proof (induction x a as arbitrary: y rule: insert_at.induct) 
  case 4
    thus ?case by (induction y) simp_all
  qed simp_all

lemma [simp]: "x \<le> length as \<Longrightarrow> lookup x (insert_at x a as) = Some a"
  by (induction x a as rule: insert_at.induct) simp_all

lemma [simp]: "x \<le> length as \<Longrightarrow> y < x \<Longrightarrow> lookup y (insert_at x a as) = lookup y as"
  proof (induction x a as arbitrary: y rule: insert_at.induct)
  case 4
    thus ?case by (induction y) simp_all
  qed simp_all

lemma [simp]: "x \<le> length as \<Longrightarrow> x \<le> y \<Longrightarrow> lookup (Suc y) (insert_at x a as) = lookup y as"
  proof (induction x a as arbitrary: y rule: insert_at.induct)
  case 4
    thus ?case by (induction y) simp_all
  qed simp_all

lemma [simp]: "x \<le> length as \<Longrightarrow> map f (insert_at x a as) = insert_at x (f a) (map f as)"
  by (induction x a as rule: insert_at.induct) simp_all

lemma [simp]: "lookup x (map f as) = map_option f (lookup x as)"
  by (induction x as rule: lookup.induct) simp_all

lemma [elim]: "lookup x as = Some a \<Longrightarrow> x < length as"
  by (induction x as rule: lookup.induct) simp_all

lemma [simp]: "x < length as \<Longrightarrow> \<exists>a. lookup x as = Some a"
  by (induction x as rule: lookup.induct) simp_all

lemma [elim]: "lookup x as = Some a \<Longrightarrow> lookup x (as @ bs) = Some a"
  by (induction x as rule: lookup.induct) simp_all

lemma [simp]: "x \<le> length as \<Longrightarrow> insert_at x a as @ bs = insert_at x a (as @ bs)"
  by (induction x a as rule: insert_at.induct, cases bs) simp_all

end