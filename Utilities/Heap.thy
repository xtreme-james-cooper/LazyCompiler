theory Heap
imports Index
begin

datatype 'a heap = Heap "nat \<Rightarrow> 'a" nat

definition empty\<^sub>h :: "'a heap" where
  "empty\<^sub>h = Heap (\<lambda>x. undefined) 0"

primrec length\<^sub>h :: "'a heap \<Rightarrow> nat" where
  "length\<^sub>h (Heap h n) = n"

primrec lookup\<^sub>h :: "'a heap \<Rightarrow>nat \<Rightarrow> 'a" where
  "lookup\<^sub>h (Heap h n) x = h x"

primrec extend\<^sub>h :: "'a heap \<Rightarrow> 'a \<Rightarrow> 'a heap" where
  "extend\<^sub>h (Heap h n) a = Heap (h(n := a)) (Suc n)"

primrec update\<^sub>h :: "'a heap \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a heap" where
  "update\<^sub>h (Heap h n) x a = Heap (h(x := a)) n"

primrec remove\<^sub>h :: "'a heap \<Rightarrow> nat \<Rightarrow> 'a heap" where
  "remove\<^sub>h (Heap h n) x = Heap (h o incr x) (n - 1)"

primrec map\<^sub>h :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a heap \<Rightarrow> 'b heap" where
  "map\<^sub>h f (Heap h n) = Heap (f o h) n"

lemma [simp]: "length\<^sub>h empty\<^sub>h = 0"
  by (simp add: empty\<^sub>h_def)

lemma [simp]: "length\<^sub>h (extend\<^sub>h h a) = Suc (length\<^sub>h h)"
  by (induction h) simp_all

lemma length\<^sub>h_update\<^sub>h [simp]: "length\<^sub>h (update\<^sub>h h x a) = length\<^sub>h h"
  by (induction h) simp_all

lemma [simp]: "x < length\<^sub>h h \<Longrightarrow> length\<^sub>h (remove\<^sub>h h x) = length\<^sub>h h - 1"
  by (induction h) simp_all

lemma [simp]: "length\<^sub>h (map\<^sub>h f h) = length\<^sub>h h"
  by (induction h) simp_all

lemma [simp]: "lookup\<^sub>h (update\<^sub>h h x a) y = (if x = y then a else lookup\<^sub>h h y)"
  by (induction h) simp_all

lemma [simp]: "lookup\<^sub>h (extend\<^sub>h h a) x = (if x = length\<^sub>h h then a else lookup\<^sub>h h x)"
  by (induction h) simp_all

lemma [simp]: "x < length\<^sub>h h \<Longrightarrow> lookup\<^sub>h (remove\<^sub>h h x) y = lookup\<^sub>h h (incr x y)"
  by (induction h) simp_all

lemma [simp]: "lookup\<^sub>h (map\<^sub>h f h) x = f (lookup\<^sub>h h x)"
  by (induction h) simp_all

end