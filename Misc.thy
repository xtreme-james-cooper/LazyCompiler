theory Misc
imports Main
begin

fun cons_fst :: "'a \<Rightarrow> 'a list \<times> 'b \<Rightarrow> 'a list \<times> 'b" where
  "cons_fst a ab = (case ab of (as, b) \<Rightarrow> (a # as, b))"

end