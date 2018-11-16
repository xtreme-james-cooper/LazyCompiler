theory Index
imports Vector
begin

definition incr :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "incr x y = (if x \<le> y then Suc y else y)"

definition decr :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "decr x y = (if x < y then y - 1 else y)"

lemma [simp]: "lookup y as = Some a \<Longrightarrow> x \<le> length as \<Longrightarrow> 
    lookup (incr x y) (insert_at x a' as) = Some a"
  by (simp add: incr_def)

lemma [simp]: "lookup y (insert_at x a' as) = Some a \<Longrightarrow> x \<le> length as \<Longrightarrow> 
    lookup x' as = Some a' \<Longrightarrow> x \<noteq> y \<Longrightarrow> lookup (decr x y) as = Some a"
  by (cases y) (auto simp add: decr_def)

end