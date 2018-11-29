theory Index
imports Vector
begin

definition incr :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "incr x y = (if x \<le> y then Suc y else y)"

definition decr :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "decr x y = (if x < y then y - 1 else y)"

definition var_reduce :: "nat \<Rightarrow> nat set \<Rightarrow> nat set" where
  "var_reduce x xs = decr x ` (xs - {x})"

lemma [simp]: "lookup as y = Some a \<Longrightarrow> x \<le> length as \<Longrightarrow> 
    lookup (insert_at x a' as) (incr x y) = Some a"
  by (simp add: incr_def)

lemma [simp]: "lookup (insert_at x a' as) y = Some a \<Longrightarrow> x \<le> length as \<Longrightarrow> x \<noteq> y \<Longrightarrow> 
    lookup as (decr x y) = Some a"
  by (cases y) (auto simp add: decr_def)

lemma [simp]: "x < length as \<Longrightarrow> lookup (remove as x) y = lookup as (incr x y)"
  proof (induction as x arbitrary: y rule: remove.induct)
  case 3
    thus ?case by (induction y) (simp_all add: incr_def)
  qed (simp_all add: incr_def)

lemma [simp]: "x \<ge> length as' \<Longrightarrow> lookup as (x - length as') = lookup (as' @ as) x"
  proof (induction as' arbitrary: x)
  case Cons
    thus ?case by (induction x) simp_all
  qed simp_all

lemma [simp]: "incr 0 x = Suc x"
  by (simp add: incr_def)

lemma [simp]: "incr y x \<noteq> y"
  by (simp add: incr_def)

lemma [simp]: "decr y (incr y x) = x"
  by (simp add: incr_def decr_def)

lemma [simp]: "x \<noteq> y \<Longrightarrow> incr y (decr y x) = x"
  by (auto simp add: incr_def decr_def)

lemma [simp]: "y \<noteq> x \<Longrightarrow> decr (Suc y) (incr y x) = x"
  by (simp add: incr_def decr_def)

lemma [simp]: "y \<le> x \<Longrightarrow> incr y (incr x z) = incr (Suc x) (incr y z)"
  by (simp add: incr_def)

lemma [simp]: "y \<le> x \<Longrightarrow> y \<noteq> z \<Longrightarrow> decr y (incr (Suc x) z) = incr x (decr y z)"
  by (auto simp add: incr_def decr_def)

lemma [simp]: "y \<le> x \<Longrightarrow> incr y (decr x z) = decr (Suc x) (incr y z)"
  by (auto simp add: incr_def decr_def)

lemma [simp]: "y \<notin> xs \<Longrightarrow> (x \<in> decr y ` xs) = (incr y x \<in> xs)"
  proof rule
    assume "x \<in> decr y ` xs"
    then obtain x' where X: "x' \<in> xs \<and> x = decr y x'" by auto
    moreover assume "y \<notin> xs"
    moreover with X have "y \<noteq> x'" by auto
    ultimately show "incr y x \<in> xs" by simp
  next
    assume "incr y x \<in> xs"
    moreover hence "x = decr y (incr y x)" by simp
    ultimately show "x \<in> decr y ` xs" by blast
  qed

lemma [simp]: "(x \<in> var_reduce y xs) = (incr y x \<in> xs)"
  by (simp add: var_reduce_def)

lemma [simp]: "(x \<in> incr y ` xs) = (if x = y then False else decr y x \<in> xs)"
  proof -
    have "(x \<in> (\<lambda>z. incr y z) ` xs) = (if x = y then False else decr y x \<in> xs)" 
      by (cases x) (auto simp add: incr_def decr_def)
    thus "(x \<in> incr y ` xs) = (if x = y then False else decr y x \<in> xs)" by simp
  qed

lemma [simp]: "y \<le> x \<Longrightarrow> var_reduce y (incr (Suc x) ` xs) = incr x ` var_reduce y xs"
  by (auto split: if_splits) (auto simp add: incr_def)

lemma [simp]: "y \<le> x \<Longrightarrow> var_reduce y (insert (Suc x) xs) = insert x (var_reduce y xs)"
  by (auto simp add: incr_def split: if_splits)

lemma [simp]: "y \<le> x \<Longrightarrow> Suc x \<notin> xs \<Longrightarrow> var_reduce y (decr (Suc x) ` xs) = decr x ` var_reduce y xs"
  by (auto simp add: incr_def decr_def split: if_splits)

lemma [simp]: "y \<le> x \<Longrightarrow> var_reduce y (var_reduce (Suc x) xs) = var_reduce x (var_reduce y xs)"
  by auto

lemma [simp]: "var_reduce x (xs \<union> ys) = var_reduce x xs \<union> var_reduce x ys"
  by (auto simp add: var_reduce_def)

lemma [simp]: "var_reduce 0 xs \<inter> (op +) y ` ys = {} \<Longrightarrow> xs \<inter> (op +) (Suc y) ` ys = {}"
  by (auto simp add: var_reduce_def)

end