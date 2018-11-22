theory StackConversion
imports EvaluateStack
begin

fun unfold_heap :: "nat list \<Rightarrow> expr heap \<Rightarrow> expr \<Rightarrow> expr" where
  "unfold_heap r h e = foldr Let (map (\<lambda>x. lookup\<^sub>h x h) r) e"

fun unstack :: "nat list list \<Rightarrow> frame list \<Rightarrow> expr \<Rightarrow> expr heap \<Rightarrow> expr" where
  "unstack [] s e h = undefined"
| "unstack (r # rs) [] e h = unfold_heap r h e"
| "unstack (r # rs) (SRef x # s) e h = unstack rs s (unfold_heap r h (Var x)) (update\<^sub>h h x e)"
| "unstack (r # rs) (SApp e\<^sub>2 # s) e h = unstack rs s (unfold_heap r h (App e e\<^sub>2)) h"
| "unstack (r # rs) (SProj l # s) e h = unstack rs s (unfold_heap r h (Proj e l)) h"
| "unstack (r # rs) (SCase t cs # s) e h = unstack rs s (unfold_heap r h (Case e t cs)) h"
| "unstack (r # rs) (SUnfold t # s) e h = unstack rs s (unfold_heap r h (Unfold t e)) h"
| "unstack (r # rs) (STyApp t # s) e h = unstack rs s (unfold_heap r h (TyApp e t)) h"

fun unstack_state :: "nat list list \<Rightarrow> stack_state \<Rightarrow> expr" where
  "unstack_state rs (StackState (Eval e) s h) = unstack rs s e h"
| "unstack_state rs (StackState (Return v) s h) = unstack rs s (devalue v) h"

lemma tc_unstack [elim]: "\<Gamma> \<turnstile>\<^sub>s\<^sub>s s : t \<rightarrow> t' \<Longrightarrow> [],\<Gamma> \<turnstile> e : t \<Longrightarrow> h \<turnstile>\<^sub>h \<Gamma> \<Longrightarrow> 
  distinct (concat rs) \<Longrightarrow> set (concat rs) = {x. x < length\<^sub>h h} \<Longrightarrow> length rs = Suc (length s) \<Longrightarrow>
    [],[] \<turnstile> unstack rs s e h : t'"
  proof (induction rs s e h rule: unstack.induct)
  case 1
    thus ?case by simp
  next case (2 r rs e h)
    hence "rs = []" by fastforce

    from 2 have "\<Gamma> \<turnstile>\<^sub>s\<^sub>s [] : t \<rightarrow> t'" by simp
    from 2 have "[] ,\<Gamma> \<turnstile> e : t" by simp
    from 2 have "h \<turnstile>\<^sub>h \<Gamma>" by simp
    from 2 have "distinct (concat (r # rs))" by simp
    from 2 have "set (concat (r # rs)) = {x. x < length\<^sub>h h}" by simp


    have "[],[] \<turnstile> foldr Let (map (\<lambda>x. lookup\<^sub>h x h) r) e : t'" by simp
    thus ?case by simp
  next case 3
    thus ?case by simp
  next case 4
    thus ?case by simp
  next case 5
    thus ?case by simp
  next case 6
    thus ?case by simp
  next case 7
    thus ?case by simp
  next case 8
    thus ?case by simp
  qed

lemma tc_unstack_state [elim]: "\<Sigma> hastype t \<Longrightarrow> [],[] \<turnstile> unstack_state rs \<Sigma> : t"
  proof (induction rs \<Sigma> rule: unstack_state.induct)
  case 1
    thus ?case using tc_unstack tc_eval_state by blast
  next case 2
    thus ?case using tc_unstack tc_return_state tc_devalue by blast
  qed

end