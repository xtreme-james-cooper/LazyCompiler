theory Vector
imports Main
begin

fun insert_at :: "nat \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "insert_at 0 a' [] = a' # []"
| "insert_at 0 a' (a # as) = a' # a # as"
| "insert_at (Suc x) a' [] = undefined"
| "insert_at (Suc x) a' (a # as) = a # insert_at x a' as"

fun lookup :: "'a list \<Rightarrow> nat \<Rightarrow> 'a option" where
  "lookup [] x = None"
| "lookup (a # as) 0 = Some a"
| "lookup (a # as) (Suc x) = lookup as x"

fun remove :: "'a list \<Rightarrow> nat \<Rightarrow> 'a list" where
  "remove [] x = undefined"
| "remove (a # as) 0 = as"
| "remove (a # as) (Suc x) = a # remove as x"

lemma insert_length [simp]: "x \<le> length as \<Longrightarrow> length (insert_at x a as) = Suc (length as)"
  by (induction x a as rule: insert_at.induct) simp_all

lemma [simp]: "x < length as \<Longrightarrow> length (remove as x) = length as - 1"
  by (induction as x rule: remove.induct) simp_all

lemma [simp]: "x \<le> length as \<Longrightarrow> y \<le> x \<Longrightarrow> 
    insert_at y b (insert_at x a as) = insert_at (Suc x) a (insert_at y b as)"
  proof (induction x a as arbitrary: y rule: insert_at.induct) 
  case 4
    thus ?case by (induction y) simp_all
  qed simp_all

lemma [simp]: "x < length as \<Longrightarrow> y \<le> x \<Longrightarrow> 
    insert_at y a (remove as x) = remove (insert_at y a as) (Suc x)"
  proof (induction as x arbitrary: y rule: remove.induct)
  case (2 a as)
    thus ?case 
      proof (induction y)
      case 0
        thus ?case by (induction as) simp_all
      qed simp_all
  next case 3
    thus ?case by (induction y) simp_all
  qed simp_all

lemma [simp]: "x \<le> length as \<Longrightarrow> lookup (insert_at x a as) x = Some a"
  by (induction x a as rule: insert_at.induct) simp_all

lemma [simp]: "lookup as x = Some a \<Longrightarrow> lookup (insert_at (length as) a' as) x = Some a"
  by (induction as x rule: lookup.induct) simp_all

lemma [elim]: "lookup (insert_at (length as) a' as) x = Some a \<Longrightarrow> x < length as \<Longrightarrow> 
    lookup as x = Some a"
  by (induction as x rule: lookup.induct) fastforce+

lemma [simp]: "x \<le> length as \<Longrightarrow> y < x \<Longrightarrow> lookup (insert_at x a as) y = lookup as y"
  proof (induction x a as arbitrary: y rule: insert_at.induct)
  case 4
    thus ?case by (induction y) simp_all
  qed simp_all

lemma [simp]: "x \<le> length as \<Longrightarrow> x \<le> y \<Longrightarrow> lookup (insert_at x a as) (Suc y) = lookup as y"
  proof (induction x a as arbitrary: y rule: insert_at.induct)
  case 4
    thus ?case by (induction y) simp_all
  qed simp_all

lemma [simp]: "x \<le> length as \<Longrightarrow> map f (insert_at x a as) = insert_at x (f a) (map f as)"
  by (induction x a as rule: insert_at.induct) simp_all

lemma [simp]: "x < length as \<Longrightarrow> map f (remove as x) = remove (map f as) x"
  by (induction as x rule: remove.induct) simp_all

lemma [simp]: "lookup (map f as) x = map_option f (lookup as x)"
  by (induction as x rule: lookup.induct) simp_all

lemma lookup_less_than [elim]: "lookup as x = Some a \<Longrightarrow> x < length as"
  by (induction as x rule: lookup.induct) simp_all

lemma [elim]: "list_all p as \<Longrightarrow> lookup as x = Some a \<Longrightarrow> p a"
  by (induction as x rule: lookup.induct) simp_all

lemma [simp]: "x < length as \<Longrightarrow> lookup (as @ bs) x = lookup as x"
  by (induction as x rule: lookup.induct) simp_all

lemma [simp]: "lookup (as @ bs) (length as + x) = lookup bs x"
  by (induction as "length as + x" rule: lookup.induct) simp_all

lemma [simp]: "x \<le> length as \<Longrightarrow> insert_at x a (as @ bs) = insert_at x a as @ bs"
  by (induction x a as rule: insert_at.induct) (cases bs, simp_all)

end