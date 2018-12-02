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
  "heap_walk' f h cs {} = {}"
| "finite cs \<Longrightarrow> \<forall>a. finite (f a) \<Longrightarrow> card cs < length\<^sub>h h \<Longrightarrow> xs \<noteq> {} \<Longrightarrow> heap_walk' f h cs xs = (
      let ys = {y \<in> \<Union> (f ` lookup\<^sub>h h ` xs). y \<notin> cs \<and> y < length\<^sub>h h}
      in xs \<union> heap_walk' f h (cs \<union> ys) ys)"
| "\<not> finite cs \<Longrightarrow> xs \<noteq> {} \<Longrightarrow> heap_walk' f h cs xs = undefined"
| "\<exists>a. \<not> finite (f a) \<Longrightarrow> xs \<noteq> {} \<Longrightarrow> heap_walk' f h cs xs = undefined"
| "card cs \<ge> length\<^sub>h h \<Longrightarrow> xs \<noteq> {} \<Longrightarrow> heap_walk' f h cs xs = undefined"
  by auto fastforce
termination 
  proof (relation "measures [\<lambda>(f, h, cs, xs). length\<^sub>h h - card cs,
                             \<lambda>(f, h, cs, xs). if xs = {} then 0 else 1]")
    fix cs::"nat set" 
    fix f::"'a \<Rightarrow> nat set" 
    fix h xs ys
    assume YS: "ys = {y \<in> \<Union> (f ` lookup\<^sub>h h ` xs). y \<notin> cs \<and> y < length\<^sub>h h}"
    moreover assume "\<forall>a. finite (f a)"
    ultimately have "finite ys" by simp
    moreover assume "finite cs"
    moreover assume "card cs < length\<^sub>h h"
    moreover assume "xs \<noteq> {}"
    moreover from YS have "cs \<inter> ys = {}" by auto
    ultimately show "((f, h, cs \<union> ys, ys), f, h, cs, xs) \<in> 
        measures [\<lambda>(f, h, cs, xs). length\<^sub>h h - card cs, \<lambda>(f, h, cs, xs). if xs = {} then 0 else 1]" 
      by (induction ys) (simp_all add: card_Un_disjoint)
  qed auto

definition heap_walk :: "('a \<Rightarrow> nat set) \<Rightarrow> 'a heap \<Rightarrow> nat set \<Rightarrow> nat set" where
  "heap_walk f h xs = heap_walk' f h {} xs"

lemma walk_subset: "finite cs \<Longrightarrow> \<forall>a. finite (f a) \<Longrightarrow> card cs < length\<^sub>h h \<Longrightarrow> 
    xs \<subseteq> heap_walk' f h cs xs"
  proof (induction f h cs xs rule: heap_walk'.induct)
  case (2 cs f h xs)
    have "xs \<subseteq> (
      let ys = {y \<in> \<Union> (f ` lookup\<^sub>h h ` xs). y \<notin> cs \<and> y < length\<^sub>h h}
      in xs \<union> heap_walk' f h (cs \<union> ys) ys)" by (simp add: Let_def)
    with 2(1, 2, 3, 4) show ?case by simp
  qed simp_all

lemma [simp]: "finite xs \<Longrightarrow> \<forall>a. finite (f a) \<Longrightarrow> \<forall>x \<in> xs. x < length\<^sub>h h \<Longrightarrow> xs \<subseteq> heap_walk f h xs"
  proof (induction xs rule: finite.induct)
  case (insertI xs x)
    moreover hence "card {} < length\<^sub>h h" by simp
    ultimately show ?case by (metis heap_walk_def walk_subset card.empty finite.emptyI)
  qed simp_all

end