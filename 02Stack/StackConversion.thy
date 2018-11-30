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
    (free_vars\<^sub>s f \<subseteq> set (concat rss) \<and> ordering_for_stack rss s)"

definition safe_unfold_order :: "nat list list \<Rightarrow> expr \<Rightarrow> expr heap \<Rightarrow> frame list \<Rightarrow> type list \<Rightarrow> 
    bool" where
  "safe_unfold_order rss e h s \<Gamma> = (distinct (concat rss) \<and> free_vars e \<subseteq> set (concat rss) \<and> 
    h \<turnstile>\<^sub>h \<Gamma> \<and> ordering_for_heap (concat rss) h \<and> ordering_for_stack rss s)"

fun safe_unfold_order\<^sub>\<Sigma> :: "nat list list \<Rightarrow> stack_state \<Rightarrow> bool" where
  "safe_unfold_order\<^sub>\<Sigma> rss (StackState (Eval e) s h) = (\<forall>\<Gamma>. h \<turnstile>\<^sub>h \<Gamma> \<longrightarrow> safe_unfold_order rss e h s \<Gamma>)"
| "safe_unfold_order\<^sub>\<Sigma> rss (StackState (Return v) s h) = 
    (\<forall>\<Gamma>. h \<turnstile>\<^sub>h \<Gamma> \<longrightarrow> safe_unfold_order rss (devalue v) h s \<Gamma>)"

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

lemma heap_lookup_freevars [simp]: "ordering_for_heap (ys @ [x] @ xs) h \<Longrightarrow> 
    free_vars (lookup\<^sub>h h x) \<subseteq> set xs"
  by (induction ys) simp_all

lemma [simp]: "ordering_for_heap (ys @ [x] @ xs) h \<Longrightarrow> h \<turnstile>\<^sub>h \<Gamma> \<Longrightarrow> \<exists>t. lookup \<Gamma> x = Some t"
  proof (induction ys) 
  case Nil
    moreover hence "length\<^sub>h h = length \<Gamma>" by auto
    ultimately show ?case by simp
  qed simp_all

lemma [elim]: "ordering_for_heap (as @ bs) h \<Longrightarrow> ordering_for_heap bs h"
  by (induction as) simp_all

lemma tc_unfold_heap' [simp]: "[],\<Gamma> \<turnstile> e : t \<Longrightarrow> free_vars e \<subseteq> set xs \<Longrightarrow> 
    h \<turnstile>\<^sub>h \<Gamma> \<Longrightarrow> ordering_for_heap (ys @ xs) h \<Longrightarrow> [],[] \<turnstile> unfold_heap h e xs : t"
  proof (induction xs arbitrary: \<Gamma> e ys)
  case (Cons x xs)
    from Cons obtain tt where T: "lookup \<Gamma> x = Some tt" by fastforce
    with Cons have "[],\<Gamma> \<turnstile> lookup\<^sub>h h x : tt" by simp
    moreover from T obtain \<Gamma>' where "\<Gamma> = insert_at x tt \<Gamma>' \<and> x \<le> length \<Gamma>'" by fastforce
    moreover with Cons(2) have "[],insert_at 0 tt (insert_at x tt \<Gamma>') \<turnstile> incr\<^sub>e\<^sub>e 0 e : t" 
      using tc_incr\<^sub>e\<^sub>e by blast
    ultimately have A: "[],\<Gamma> \<turnstile> Let (lookup\<^sub>h h x) (reshuffle x e) : t" by simp
    from Cons have C: "free_vars (Let (lookup\<^sub>h h x) (reshuffle x e)) \<subseteq> set xs" by auto
    from Cons have "h \<turnstile>\<^sub>h \<Gamma> \<Longrightarrow> ordering_for_heap ((ys @ [x]) @ xs) h" by simp
    with Cons A C have "[],[] \<turnstile> unfold_heap h (Let (lookup\<^sub>h h x) (reshuffle x e)) xs : t" 
      by blast
    thus ?case by simp
  qed simp_all

lemma [simp]: "[],\<Gamma> \<turnstile> e : t \<Longrightarrow> free_vars e \<subseteq> set rs \<Longrightarrow> h \<turnstile>\<^sub>h \<Gamma> \<Longrightarrow> 
    ordering_for_heap rs h \<Longrightarrow> [],[] \<turnstile> unfold_heap h e rs : t"
  proof -
    assume "ordering_for_heap rs h"
    hence "ordering_for_heap ([] @ rs) h" by simp
    moreover assume "[],\<Gamma> \<turnstile> e : t"
    moreover assume "h \<turnstile>\<^sub>h \<Gamma>"
    moreover assume "free_vars e \<subseteq> set rs" 
    ultimately show "[],[] \<turnstile> unfold_heap h e rs : t" by (metis tc_unfold_heap')
  qed

lemma free_vars_unfold [simp]: "ordering_for_heap (rs @ rss) h \<Longrightarrow> free_vars e \<subseteq> set (rs @ rss) \<Longrightarrow> 
    free_vars (unfold_heap h e rs) \<subseteq> set rss"
  proof (induction rs arbitrary: e)
  case (Cons r rs)
    moreover hence "free_vars (Let (lookup\<^sub>h h r) (reshuffle r e)) \<subseteq> set (rs @ rss)" by auto
    ultimately show ?case by simp
  qed simp_all

lemma tc_unfold_heap'' [simp]: "[],\<Gamma> \<turnstile> e : t \<Longrightarrow> free_vars e \<subseteq> set (xs @ rss) \<Longrightarrow> 
    h \<turnstile>\<^sub>h \<Gamma> \<Longrightarrow> ordering_for_heap (ys @ xs @ rss) h \<Longrightarrow> [],\<Gamma> \<turnstile> unfold_heap h e xs : t"
  proof (induction xs arbitrary: \<Gamma> e ys)
  case (Cons x xs)
    from Cons obtain tt where T: "lookup \<Gamma> x = Some tt" by fastforce
    with Cons have "[],\<Gamma> \<turnstile> lookup\<^sub>h h x : tt" by simp
    moreover from T obtain \<Gamma>' where "\<Gamma> = insert_at x tt \<Gamma>' \<and> x \<le> length \<Gamma>'" by fastforce
    moreover with Cons(2) have "[],insert_at 0 tt (insert_at x tt \<Gamma>') \<turnstile> incr\<^sub>e\<^sub>e 0 e : t" 
      using tc_incr\<^sub>e\<^sub>e by blast
    ultimately have A: "[],\<Gamma> \<turnstile> Let (lookup\<^sub>h h x) (reshuffle x e) : t" by simp
    from Cons have "free_vars (lookup\<^sub>h h x) \<subseteq> set (xs @ rss)" 
      using heap_lookup_freevars by fastforce
    with Cons have C: "free_vars (Let (lookup\<^sub>h h x) (reshuffle x e)) \<subseteq> set (xs @ rss)" by auto
    from Cons have "h \<turnstile>\<^sub>h \<Gamma> \<Longrightarrow> ordering_for_heap ((ys @ [x]) @ (xs @ rss)) h" by simp
    with Cons A C have "[],\<Gamma> \<turnstile> unfold_heap h (Let (lookup\<^sub>h h x) (reshuffle x e)) xs : t" 
      by blast
    thus ?case by simp
  qed simp_all

lemma tc_unfold_heap: "[],\<Gamma> \<turnstile> e : t \<Longrightarrow> free_vars e \<subseteq> set (rs @ rss) \<Longrightarrow> h \<turnstile>\<^sub>h \<Gamma> \<Longrightarrow> 
    ordering_for_heap (rs @ rss) h \<Longrightarrow> [],\<Gamma> \<turnstile> unfold_heap h e rs : t"
  proof -
    assume "ordering_for_heap (rs @ rss) h"
    hence "ordering_for_heap ([] @ rs @ rss) h" by simp
    moreover assume "[],\<Gamma> \<turnstile> e : t"
    moreover assume "free_vars e \<subseteq> set (rs @ rss)"
    moreover assume "h \<turnstile>\<^sub>h \<Gamma>"
    ultimately show "[],\<Gamma> \<turnstile> unfold_heap h e rs : t" by (metis tc_unfold_heap'')
  qed

lemma [simp]: "\<Gamma> \<turnstile>\<^sub>s\<^sub>s s : t \<rightarrow> t' \<Longrightarrow> [],\<Gamma> \<turnstile> e : t \<Longrightarrow> safe_unfold_order rs e h s \<Gamma> \<Longrightarrow> 
    [],[] \<turnstile> unstack rs s e h : t'"
  proof (induction rs s e h arbitrary: t rule: unstack.induct)
  case (3 rs rss x s e h)

have "\<Gamma> \<turnstile>\<^sub>s f : t \<rightarrow> t' \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>s\<^sub>s s : t' \<rightarrow> t'' \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>s\<^sub>s f # s : t \<rightarrow> t''" by simp

    thus ?case by simp
  next case (4 rs rss e\<^sub>2 s e h)
    then obtain t\<^sub>1 t\<^sub>2 where T: "t = Arrow t\<^sub>1 t\<^sub>2 \<and> ([],\<Gamma> \<turnstile> e\<^sub>2 : t\<^sub>1)" and X: "\<Gamma> \<turnstile>\<^sub>s\<^sub>s s : t\<^sub>2 \<rightarrow> t'" 
      by fastforce
    from 4 have A: "free_vars e \<subseteq> set (rs @ concat rss)" by (simp add: safe_unfold_order_def)
    from 4 have B: "ordering_for_heap (rs @ concat rss) h" by (simp add: safe_unfold_order_def)
    with 4(3, 4) A B have Y: "[],\<Gamma> \<turnstile> unfold_heap h e rs : t" 
      by (metis tc_unfold_heap safe_unfold_order_def)
    from A B have Z: "free_vars (unfold_heap h e rs) \<subseteq> set (concat rss)" by (metis free_vars_unfold)
    from 4 have "ordering_for_heap (concat rss) h" by (auto simp add: safe_unfold_order_def)
    with 4 T X Y Z show ?case by (simp add: safe_unfold_order_def)
  next case (5 rs rss l s e h)
    then obtain tt ts where T: "t = Record ts \<and> lookup ts l = Some tt" and X: "\<Gamma> \<turnstile>\<^sub>s\<^sub>s s : tt \<rightarrow> t'" 
      by fastforce
    from 5 have A: "free_vars e \<subseteq> set (rs @ concat rss)" by (simp add: safe_unfold_order_def)
    from 5 have B: "ordering_for_heap (rs @ concat rss) h" by (simp add: safe_unfold_order_def)
    with 5(3, 4) A B have Y: "[],\<Gamma> \<turnstile> unfold_heap h e rs : t" 
      by (metis tc_unfold_heap safe_unfold_order_def)
    from A B have Z: "free_vars (unfold_heap h e rs) \<subseteq> set (concat rss)" by (metis free_vars_unfold)
    from 5 have "ordering_for_heap (concat rss) h" by (auto simp add: safe_unfold_order_def)
    with 5 T X Y Z show ?case by (simp add: safe_unfold_order_def)
  next case (6 rs rss tt cs s e h)
    then obtain ts where T: "t = Variant ts \<and> ([] \<turnstile>\<^sub>k tt : Star) \<and> ([],\<Gamma> \<turnstile>\<^sub>c cs : ts \<rightarrow> tt)" 
                     and X: "\<Gamma> \<turnstile>\<^sub>s\<^sub>s s : tt \<rightarrow> t'" by fastforce
    from 6 have A: "free_vars e \<subseteq> set (rs @ concat rss)" by (simp add: safe_unfold_order_def)
    from 6 have B: "ordering_for_heap (rs @ concat rss) h" by (simp add: safe_unfold_order_def)
    with 6(3, 4) A B have Y: "[],\<Gamma> \<turnstile> unfold_heap h e rs : t" 
      by (metis tc_unfold_heap safe_unfold_order_def)
    from A B have Z: "free_vars (unfold_heap h e rs) \<subseteq> set (concat rss)" by (metis free_vars_unfold)
    from 6 have "ordering_for_heap (concat rss) h" by (auto simp add: safe_unfold_order_def)
    with 6 T X Y Z show ?case by (simp add: safe_unfold_order_def)
  next case (7 rs rss t s e h)

have "\<Gamma> \<turnstile>\<^sub>s f : t \<rightarrow> t' \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>s\<^sub>s s : t' \<rightarrow> t'' \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>s\<^sub>s f # s : t \<rightarrow> t''" by simp

have "[k] \<turnstile>\<^sub>k t : Star \<Longrightarrow> 
    \<Gamma> \<turnstile>\<^sub>s SUnfold t : Inductive k t \<rightarrow> subst\<^sub>t\<^sub>t 0 (Inductive k t) t" by simp

    thus ?case by simp
  next case (8 rs rss t s e h)

have "\<Gamma> \<turnstile>\<^sub>s f : t \<rightarrow> t' \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>s\<^sub>s s : t' \<rightarrow> t'' \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>s\<^sub>s f # s : t \<rightarrow> t''" by simp
have "[] \<turnstile>\<^sub>k t' : k \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>s STyApp t' : Forall k t \<rightarrow> subst\<^sub>t\<^sub>t 0 t' t" by simp

    thus ?case by simp
  qed (auto simp add: safe_unfold_order_def)

lemma tc_unstack_state [elim]: "\<Sigma> hastype t \<Longrightarrow> safe_unfold_order\<^sub>\<Sigma> rs \<Sigma> \<Longrightarrow> 
    [],[] \<turnstile> unstack_state rs \<Sigma> : t"
  by (induction \<Sigma> t rule: typecheck_stack_state.induct) simp_all

end