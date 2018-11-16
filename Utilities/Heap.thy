theory Heap
imports Main
begin

datatype 'a heap = Heap "nat \<Rightarrow> 'a" nat

definition empty\<^sub>h :: "'a heap" where
  "empty\<^sub>h = Heap (\<lambda>x. undefined) 0"

primrec length\<^sub>h :: "'a heap \<Rightarrow> nat" where
  "length\<^sub>h (Heap h n) = n"

primrec lookup\<^sub>h :: "nat \<Rightarrow> 'a heap \<Rightarrow>'a" where
  "lookup\<^sub>h x (Heap h n) = h x"

primrec extend\<^sub>h :: "'a heap \<Rightarrow> 'a \<Rightarrow> 'a heap" where
  "extend\<^sub>h (Heap h n) a = Heap (h(n := a)) (Suc n)"

primrec update\<^sub>h :: "'a heap \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a heap" where
  "update\<^sub>h (Heap h n) x a = Heap (h(x := a)) n"

lemma [simp]: "length\<^sub>h empty\<^sub>h = 0"
  by (simp add: empty\<^sub>h_def)

lemma [simp]: "length\<^sub>h (extend\<^sub>h h a) = Suc (length\<^sub>h h)"
  by (induction h) simp_all

lemma [simp]: "length\<^sub>h (update\<^sub>h h x a) = length\<^sub>h h"
  by (induction h) simp_all

lemma [simp]: "lookup\<^sub>h y (update\<^sub>h h x a) = (if x = y then a else lookup\<^sub>h y h)"
  by (induction h) simp_all

lemma [simp]: "lookup\<^sub>h x (extend\<^sub>h h a) = (if x = length\<^sub>h h then a else lookup\<^sub>h x h)"
  by (induction h) simp_all

end