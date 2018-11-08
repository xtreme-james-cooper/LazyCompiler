theory Misc
imports Main
begin

fun cons_fst :: "'a \<Rightarrow> 'a list \<times> 'b \<Rightarrow> 'a list \<times> 'b" where
  "cons_fst a ab = (case ab of (as, b) \<Rightarrow> (a # as, b))"

lemma [simp]: "cons_fst f se = (s, e) \<Longrightarrow> \<exists>s'. se = (s', e) \<and> s = f # s'"
  by (auto split: prod.splits)

end