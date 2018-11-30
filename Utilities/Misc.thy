theory Misc
imports Index
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

lemma [simp]: "a \<notin> set as \<Longrightarrow> length (filter (\<lambda>x. x \<noteq> a) as) = length as"
  by (induction as) auto

lemma filter_length: "distinct as \<Longrightarrow> a \<in> set as \<Longrightarrow> 
    length as = Suc (length (filter (\<lambda>x. x \<noteq> a) as))"
  by (induction as) auto

lemma [elim]: "distinct xs \<Longrightarrow> k < length xs \<Longrightarrow> \<forall>x\<in>set xs. x < length xs \<Longrightarrow> k \<in> set xs"
  proof (induction "length xs" arbitrary: k xs)
  case 0
    thus ?case by (cases xs) simp_all
  next case (Suc l)
    then obtain x xs' where X: "xs = x # xs'" by (cases xs) simp_all
    thus ?case 
      proof (cases "x = k")
      case False
        from Suc X have A: "l = length (map (decr x) xs')" by simp 
        from Suc X have B: "distinct (map (decr x) xs')" by simp 
        from Suc X False have C: "decr x k < length (map (decr x) xs')" by simp 
        have "\<forall>y \<in> set (map (decr x) xs'). y < length (map (decr x) xs')" 
          proof
            fix y
            assume "y \<in> set (map (decr x) xs')"
            then obtain z where Z: "z : set xs' \<and> y = decr x z" by auto
            with Suc X have "x \<noteq> z" by auto
            with Suc X Z show "y < length (map (decr x) xs')" by simp
          qed
        with Suc(1) A B C have "decr x k \<in> set (map (decr x) xs')" by fastforce
        with Suc X False show ?thesis by simp
      qed simp_all
  qed

lemma pack_pigeonholes: "distinct xs \<Longrightarrow> k = length xs \<Longrightarrow> \<forall>x \<in> set xs. x < k \<Longrightarrow> set xs = {x. x < k}"
  by auto

end