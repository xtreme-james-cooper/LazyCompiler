theory StackConversion
imports EvaluateStack
begin

abbreviation reshuffle :: "nat \<Rightarrow> expr \<Rightarrow> expr" where
  "reshuffle x e \<equiv> incr\<^sub>e\<^sub>e (Suc x) (subst\<^sub>x\<^sub>e (Suc x) 0 (incr\<^sub>e\<^sub>e 0 e))"

primrec unfold_heap :: "expr heap \<Rightarrow> expr \<Rightarrow> nat list \<Rightarrow> expr" where
  "unfold_heap h e [] = e"
| "unfold_heap h e (x # xs) = unfold_heap h (Let (lookup\<^sub>h h x) (reshuffle x e)) xs"

fun unstack :: "nat list list \<Rightarrow> frame list \<Rightarrow> expr \<Rightarrow> expr heap \<Rightarrow> expr" where
  "unstack [] s e h = e"
| "unstack (r # rs) [] e h = unstack rs [] (unfold_heap h e r) h"
| "unstack (r # rs) (SRef x # s) e h = 
    unstack rs s (Var x) (update\<^sub>h h x (unfold_heap h e r))"
| "unstack (r # rs) (SApp e\<^sub>2 # s) e h = unstack rs s (App (unfold_heap h e r) e\<^sub>2) h"
| "unstack (r # rs) (SProj l # s) e h = unstack rs s (Proj (unfold_heap h e r) l) h"
| "unstack (r # rs) (SCase t cs # s) e h = unstack rs s (Case (unfold_heap h e r) t cs) h"
| "unstack (r # rs) (SUnfold t # s) e h = unstack rs s (Unfold t (unfold_heap h e r)) h"
| "unstack (r # rs) (STyApp t # s) e h = unstack rs s (TyApp (unfold_heap h e r) t) h"

fun unstack_state :: "nat list list \<Rightarrow> stack_state \<Rightarrow> expr" where
  "unstack_state rs (StackState (Eval e) s h) = unstack rs s e h"
| "unstack_state rs (StackState (Return v) s h) = unstack rs s (devalue v) h"

primrec ordering_for_heap :: "nat list \<Rightarrow> expr heap \<Rightarrow> bool" where
  "ordering_for_heap [] h = True"
| "ordering_for_heap (r # rs) h = 
    (r < length\<^sub>h h \<and> free_vars (lookup\<^sub>h h r) \<subseteq> set rs \<and> ordering_for_heap rs h)"

fun ordering_for_stack :: "nat list list \<Rightarrow> frame list \<Rightarrow> bool" where
  "ordering_for_stack [] s = False"
| "ordering_for_stack (rs # rss) [] = (rss = [])"
| "ordering_for_stack (rs # rss) (f # s) = 
    (\<forall>r \<in> set rs. r \<notin> free_vars\<^sub>s\<^sub>s (f # s) \<and> ordering_for_stack rss s)"

fun safe_unfold_order :: "nat list list \<Rightarrow> expr heap \<Rightarrow> frame list \<Rightarrow> type list \<Rightarrow> bool" where
  "safe_unfold_order rss h s \<Gamma> = (distinct (concat rss) \<and> length (concat rss) = length \<Gamma> \<and> h \<turnstile>\<^sub>h \<Gamma> \<and>
    ordering_for_heap (concat rss) h \<and> ordering_for_stack rss s)"

primrec safe_unfold_order\<^sub>\<Sigma> :: "nat list list \<Rightarrow> stack_state \<Rightarrow> bool" where
  "safe_unfold_order\<^sub>\<Sigma> rss (StackState f s h) = (\<forall>\<Gamma>. h \<turnstile>\<^sub>h \<Gamma> \<longrightarrow> safe_unfold_order rss h s \<Gamma>)"

lemma [simp]: "ordering_for_heap xs h \<Longrightarrow> \<forall>x \<in> set xs. x < length\<^sub>h h"
  by (induction xs) simp_all

lemma [simp]: "distinct xs \<Longrightarrow> length xs = length \<Gamma> \<Longrightarrow> h \<turnstile>\<^sub>h \<Gamma> \<Longrightarrow> ordering_for_heap xs h \<Longrightarrow> 
    set xs = {x. x < length \<Gamma>}"
  proof -
    assume "ordering_for_heap xs h"
    hence "\<forall>x \<in> set xs. x < length\<^sub>h h" by simp
    moreover assume "h \<turnstile>\<^sub>h \<Gamma>"
    moreover hence "length\<^sub>h h = length \<Gamma>" by auto
    ultimately have "\<forall>x \<in> set xs. x < length \<Gamma>" by simp
    moreover assume "distinct xs"
    moreover assume "length xs = length \<Gamma>"
    ultimately show "set xs = {x. x < length \<Gamma>}" by (metis pack_pigeonholes)
  qed

lemma [simp]: "ordering_for_heap (ys @ [x] @ xs) h \<Longrightarrow> free_vars (lookup\<^sub>h h x) \<subseteq> set xs"
  by (induction ys) simp_all

lemma [simp]: "ordering_for_heap (ys @ [x] @ xs) h \<Longrightarrow> h \<turnstile>\<^sub>h \<Gamma> \<Longrightarrow> \<exists>t. lookup \<Gamma> x = Some t"
  proof (induction ys) 
  case Nil
    moreover hence "length\<^sub>h h = length \<Gamma>" by auto
    ultimately show ?case by simp
  qed simp_all

lemma tc_unfold_heap' [simp]: "[],\<Gamma> \<turnstile> e : t \<Longrightarrow> distinct (ys @ xs) \<Longrightarrow> 
  length (ys @ xs) = length \<Gamma> \<Longrightarrow> h \<turnstile>\<^sub>h \<Gamma> \<Longrightarrow> ordering_for_heap (ys @ xs) h \<Longrightarrow> 
    free_vars e \<inter> set ys = {} \<Longrightarrow> [],[] \<turnstile> unfold_heap h e xs : t"
  proof (induction xs arbitrary: \<Gamma> e ys)
  case (Cons x xs)
    from Cons obtain tt where T: "lookup \<Gamma> x = Some tt" by fastforce
    with Cons have "[],\<Gamma> \<turnstile> lookup\<^sub>h h x : tt" by simp
    moreover from T obtain \<Gamma>' where "\<Gamma> = insert_at x tt \<Gamma>' \<and> x \<le> length \<Gamma>'" by fastforce
    moreover with Cons(2) have "[],insert_at 0 tt (insert_at x tt \<Gamma>') \<turnstile> incr\<^sub>e\<^sub>e 0 e : t" 
      using tc_incr\<^sub>e\<^sub>e by blast
    ultimately have A: "[],\<Gamma> \<turnstile> Let (lookup\<^sub>h h x) (reshuffle x e) : t" by simp
    from Cons have B: "distinct ((ys @ [x]) @ xs)" by simp
    from Cons have C: "length ((ys @ [x]) @ xs) = length \<Gamma>" by simp
    from Cons have D: "h \<turnstile>\<^sub>h \<Gamma> \<Longrightarrow> ordering_for_heap ((ys @ [x]) @ xs) h" by simp
    from Cons have "free_vars (lookup\<^sub>h h x) \<subseteq> set xs" by simp
    with Cons(3, 7) have "free_vars (Let (lookup\<^sub>h h x) (reshuffle x e)) \<inter> set (ys @ [x]) = {}" 
      by auto
    with Cons A B C D have "[],[] \<turnstile> unfold_heap h (Let (lookup\<^sub>h h x) (reshuffle x e)) xs : t" 
      by blast
    thus ?case by simp
  qed simp_all

lemma [simp]: "[],\<Gamma> \<turnstile> e : t \<Longrightarrow> distinct rs \<Longrightarrow> length rs = length \<Gamma> \<Longrightarrow> h \<turnstile>\<^sub>h \<Gamma> \<Longrightarrow> 
    ordering_for_heap rs h \<Longrightarrow> [],[] \<turnstile> unfold_heap h e rs : t"
  proof -
    assume A: "[],\<Gamma> \<turnstile> e : t"
    assume "distinct rs"
    hence B: "distinct ([] @ rs)" by simp
    assume "length rs = length \<Gamma>"
    hence C: "length ([] @ rs) = length \<Gamma>" by simp
    assume D: "h \<turnstile>\<^sub>h \<Gamma>"
    assume "ordering_for_heap rs h"
    hence E: "ordering_for_heap ([] @ rs) h" by simp
    have "free_vars e \<inter> set [] = {}" by simp
    with A B C D E have "[],[] \<turnstile> unfold_heap h e rs : t" by (metis tc_unfold_heap')
    thus "[],[] \<turnstile> unfold_heap h e rs : t" by simp
  qed

lemma [simp]: "\<Gamma> \<turnstile>\<^sub>s\<^sub>s s : t \<rightarrow> t' \<Longrightarrow> [],\<Gamma> \<turnstile> e : t \<Longrightarrow> safe_unfold_order rs h s \<Gamma> \<Longrightarrow> 
    [],[] \<turnstile> unstack rs s e h : t'"
  proof (induction rs s e h arbitrary: t rule: unstack.induct)
  case (3 r rs x s e h)
    thus ?case by simp
  next case (4 r rs e\<^sub>2 s e h)

    from 4 have "\<Gamma> \<turnstile>\<^sub>s\<^sub>s SApp e\<^sub>2 # s : t \<rightarrow> t'" by simp
    from 4 have "[] ,\<Gamma> \<turnstile> e : t" by simp
    from 4 have "safe_unfold_order (r # rs) h (SApp e\<^sub>2 # s) \<Gamma>" by simp


    have X: "\<Gamma> \<turnstile>\<^sub>s\<^sub>s s : tt \<rightarrow> t'" by simp


    have Y: "[] ,\<Gamma> \<turnstile> App (unfold_heap h e r) e\<^sub>2 : tt" by simp


    have "safe_unfold_order rs h s \<Gamma>" by simp
    with 4 X Y show ?case by simp
  next case (5 r rs l s e h)
    thus ?case by simp
  next case (6 r rs t cs s e h)
    thus ?case by simp
  next case (7 r rs t s e h)
    thus ?case by simp
  next case (8 r rs t s e h)
    thus ?case by simp
  qed auto

lemma tc_unstack_state [elim]: "\<Sigma> hastype t \<Longrightarrow> safe_unfold_order\<^sub>\<Sigma> rs \<Sigma> \<Longrightarrow> 
    [],[] \<turnstile> unstack_state rs \<Sigma> : t"
  by (induction \<Sigma> t rule: typecheck_stack_state.induct) simp_all

end