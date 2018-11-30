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

(* heap-walking *)

(* compute the transitive closure of f over the heap, and return all hit addresses *)

function heap_walk' :: "('a \<Rightarrow> nat set) \<Rightarrow> 'a heap \<Rightarrow> nat set \<Rightarrow> nat set \<Rightarrow> nat set" where
  "finite xs \<Longrightarrow> \<forall>a. finite (f a) \<Longrightarrow> card xs < length\<^sub>h h \<Longrightarrow> heap_walk' f h xs x = (
      let ys = {y \<in> \<Union> (f ` lookup\<^sub>h h ` x). y \<notin> xs \<and> y < length\<^sub>h h}
      in if ys \<noteq> {} then ys \<union> heap_walk' f h (xs \<union> ys) ys else {})"
| "\<not> finite xs \<Longrightarrow> heap_walk' f h xs x = undefined"
| "\<exists>a. \<not> finite (f a) \<Longrightarrow> heap_walk' f h xs x = undefined"
| "card xs \<ge> length\<^sub>h h \<Longrightarrow> heap_walk' f h xs x = undefined"
  by auto fastforce
termination 
  proof (relation "measure (\<lambda>(f, h, xs, x). length\<^sub>h h - card xs)")
    fix xs::"nat set" 
    fix f::"'a \<Rightarrow> nat set" 
    fix h x ys
    assume FX: "finite xs"
    assume FF: "\<forall>a. finite (f a)"
    assume YS: "ys = {y \<in> \<Union> (f ` lookup\<^sub>h h ` x). y \<notin> xs \<and> y < length\<^sub>h h}"
    assume CX: "card xs < length\<^sub>h h"
    assume YC: "ys \<noteq> {}"
    from FF YS have FY: "finite ys" by simp
    from YS have IN: "xs \<inter> ys = {}" by auto
    from FY YC have "card ys > 0" by auto
    with FX YS CX IN show "((f, h, xs \<union> ys, ys), f, h, xs, x) \<in> 
      measure (\<lambda>(f, h, xs, x). length\<^sub>h h - card xs)" by (simp add: card_Un_disjoint)
  qed auto

definition heap_walk :: "('a \<Rightarrow> nat set) \<Rightarrow> 'a heap \<Rightarrow> nat set \<Rightarrow> nat set" where
  "heap_walk f h xs = heap_walk' f h {} {x \<in> xs. x < length\<^sub>h h}"

end