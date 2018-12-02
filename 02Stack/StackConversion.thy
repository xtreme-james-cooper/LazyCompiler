theory StackConversion
imports EvaluateStack
begin

abbreviation reshuffle :: "nat \<Rightarrow> expr \<Rightarrow> expr" where
  "reshuffle x e \<equiv> incr\<^sub>e\<^sub>e (Suc x) (subst\<^sub>x\<^sub>e (Suc x) 0 (incr\<^sub>e\<^sub>e 0 e))"

primrec unfold_heap :: "expr heap \<Rightarrow> expr \<Rightarrow> nat list \<Rightarrow> expr" where
  "unfold_heap h e [] = e"
| "unfold_heap h e (x # xs) = unfold_heap h (Let (lookup\<^sub>h h x) (reshuffle x e)) xs"

primrec unframe :: "frame \<Rightarrow> expr \<Rightarrow> expr heap \<Rightarrow> expr \<times> expr heap" where
  "unframe (SRef x) e h = (Var x, update\<^sub>h h x e)"
| "unframe (SApp e\<^sub>2) e h = (App e e\<^sub>2, h)"
| "unframe (SProj l) e h = (Proj e l, h)"
| "unframe (SCase t cs) e h = (Case e t cs, h)"
| "unframe (SUnfold t) e h = (Unfold t e, h)"
| "unframe (STyApp t) e h = (TyApp e t, h)"

fun unstack :: "nat list list \<Rightarrow> frame list \<Rightarrow> expr \<Rightarrow> expr heap \<Rightarrow> expr" where
  "unstack [] s e h = e"
| "unstack (r # rs) [] e h = unstack rs [] (unfold_heap h e r) h"
| "unstack (r # rs) (f # s) e h = 
    (case unframe f (unfold_heap h e r) h of (e', h') \<Rightarrow> unstack rs s e' h')"

fun unstack_state :: "nat list list \<Rightarrow> stack_state \<Rightarrow> expr" where
  "unstack_state rs (StackState (Eval e) s h) = unstack rs s e h"
| "unstack_state rs (StackState (Return v) s h) = unstack rs s (devalue v) h"

primrec ordering_for_heap :: "nat list \<Rightarrow> expr heap \<Rightarrow> bool" where
  "ordering_for_heap [] h = True"
| "ordering_for_heap (r # rs) h = 
    (r < length\<^sub>h h \<and> free_vars (lookup\<^sub>h h r) \<subseteq> set rs \<and> ordering_for_heap rs h)"

fun ordering_for_stack :: "expr heap \<Rightarrow> nat list list \<Rightarrow> frame list \<Rightarrow> bool" where
  "ordering_for_stack h [] s = False"
| "ordering_for_stack h (rs # rss) [] = (rss = [])"
| "ordering_for_stack h (rs # rss) (f # s) = ((\<forall>x \<in> free_vars\<^sub>s f. x < length\<^sub>h h) \<and> 
    heap_walk free_vars h (free_vars\<^sub>s f) \<subseteq> set (concat rss) \<and> ordering_for_stack h rss s)"

definition safe_unfold_order :: "nat list list \<Rightarrow> expr \<Rightarrow> expr heap \<Rightarrow> frame list \<Rightarrow> type list \<Rightarrow> bool" where
  "safe_unfold_order rss e h s \<Gamma> = (distinct (concat rss) \<and> free_vars e \<subseteq> set (concat rss) \<and> 
    h \<turnstile>\<^sub>h \<Gamma> \<and> ordering_for_heap (concat rss) h \<and> ordering_for_stack h rss s)"

fun safe_unfold_order\<^sub>\<Sigma> :: "nat list list \<Rightarrow> stack_state \<Rightarrow> bool" where
  "safe_unfold_order\<^sub>\<Sigma> rss (StackState (Eval e) s h) = (\<forall>\<Gamma>. h \<turnstile>\<^sub>h \<Gamma> \<longrightarrow> safe_unfold_order rss e h s \<Gamma>)"
| "safe_unfold_order\<^sub>\<Sigma> rss (StackState (Return v) s h) = 
    (\<forall>\<Gamma>. h \<turnstile>\<^sub>h \<Gamma> \<longrightarrow> safe_unfold_order rss (devalue v) h s \<Gamma>)"

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

lemma [simp]: "[],\<Gamma> \<turnstile> e : t \<Longrightarrow> safe_unfold_order (rs # rss) e h s \<Gamma> \<Longrightarrow> 
    [],\<Gamma> \<turnstile> unfold_heap h e rs : t"
  proof (unfold safe_unfold_order_def)
    assume "distinct (concat (rs # rss)) \<and> free_vars e \<subseteq> set (concat (rs # rss)) \<and> h \<turnstile>\<^sub>h \<Gamma> \<and> 
      ordering_for_heap (concat (rs # rss)) h \<and> ordering_for_stack h (rs # rss) s"
    moreover hence "ordering_for_heap ([] @ rs @ concat rss) h" by simp
    moreover assume "[],\<Gamma> \<turnstile> e : t"
    ultimately show "[],\<Gamma> \<turnstile> unfold_heap h e rs : t" by (metis tc_unfold_heap'' concat.simps(2))
  qed

lemma [simp]: "\<Gamma> \<turnstile>\<^sub>s f : t \<rightarrow> t' \<Longrightarrow> [],\<Gamma> \<turnstile> e : t \<Longrightarrow> unframe f e h = (e', h') \<Longrightarrow> [],\<Gamma> \<turnstile> e' : t'"
  by (induction \<Gamma> f t t' rule: typecheck_frame.induct) auto

lemma [elim]: "safe_unfold_order (rs # rss) e h (f # s) \<Gamma> \<Longrightarrow> 
    unframe f (unfold_heap h e rs) h = (e', h') \<Longrightarrow> safe_unfold_order rss e' h' s \<Gamma>"
  proof (induction f)
  case (SRef x)
    from SRef have E: "e' = Var x" by simp
    from SRef have H: "h' = update\<^sub>h h x (unfold_heap h e rs)" by simp
    from SRef have "distinct (concat (rs # rss))" by (simp add: safe_unfold_order_def)
    from SRef have "free_vars e \<subseteq> set (concat (rs # rss))" by (simp add: safe_unfold_order_def)
    from SRef have "h \<turnstile>\<^sub>h \<Gamma>" by (simp add: safe_unfold_order_def)
    from SRef have "ordering_for_heap (concat (rs # rss)) h" by (simp add: safe_unfold_order_def)
    from SRef have "heap_walk free_vars h {x} \<subseteq> set (concat rss)" by (simp add: safe_unfold_order_def)
    from SRef have "ordering_for_stack h rss s" by (simp add: safe_unfold_order_def)


    have X: "x \<in> set (concat rss)" by (simp add: safe_unfold_order_def)

    have Y: "update\<^sub>h h x (unfold_heap h e rs) \<turnstile>\<^sub>h \<Gamma>" by simp

    have Z: "ordering_for_heap (concat rss) (update\<^sub>h h x (unfold_heap h e rs))" by simp

    have "ordering_for_stack (update\<^sub>h h x (unfold_heap h e rs)) rss s" by simp
    with SRef E H X Y Z show ?case by (simp add: safe_unfold_order_def)
  next case (SApp e\<^sub>2)
    hence X: "free_vars (unfold_heap h e rs) \<subseteq> set (concat rss)" 
      by (metis free_vars_unfold safe_unfold_order_def concat.simps(2))
    from SApp have "heap_walk free_vars h (free_vars e\<^sub>2) \<subseteq> set (concat rss)" 
      by (simp add: safe_unfold_order_def)
    moreover from SApp have "free_vars e\<^sub>2 \<subseteq> heap_walk free_vars h (free_vars e\<^sub>2)" 
      by (simp add: safe_unfold_order_def)
    ultimately have "free_vars e\<^sub>2 \<subseteq>  set (concat rss)" by simp
    with SApp X have "safe_unfold_order rss (App (unfold_heap h e rs) e\<^sub>2) h s \<Gamma>" 
      by (auto simp add: safe_unfold_order_def)
    with SApp show ?case by auto
  next case (SProj l)
    hence "free_vars (unfold_heap h e rs) \<subseteq> set (concat rss)" 
      by (metis free_vars_unfold safe_unfold_order_def concat.simps(2))
    with SProj have "safe_unfold_order rss (Proj (unfold_heap h e rs) l) h s \<Gamma>" 
      by (auto simp add: safe_unfold_order_def)
    with SProj show ?case by auto
  next case (SCase t cs)
    hence X: "free_vars (unfold_heap h e rs) \<subseteq> set (concat rss)" 
      by (metis free_vars_unfold safe_unfold_order_def concat.simps(2))
    from SCase have "heap_walk free_vars h (free_vars\<^sub>c cs) \<subseteq> set (concat rss)" 
      by (simp add: safe_unfold_order_def)
    moreover from SCase have "free_vars\<^sub>c cs \<subseteq> heap_walk free_vars h (free_vars\<^sub>c cs)" 
      by (simp add: safe_unfold_order_def)
    ultimately have "free_vars\<^sub>c cs \<subseteq>  set (concat rss)" by simp
    with SCase X have "safe_unfold_order rss (Case (unfold_heap h e rs) t cs) h s \<Gamma>" 
      by (auto simp add: safe_unfold_order_def)
    with SCase show ?case by auto
  next case (SUnfold t)
    hence "free_vars (unfold_heap h e rs) \<subseteq> set (concat rss)" 
      by (metis free_vars_unfold safe_unfold_order_def concat.simps(2))
    with SUnfold have "safe_unfold_order rss (Unfold t (unfold_heap h e rs)) h s \<Gamma>" 
      by (auto simp add: safe_unfold_order_def)
    with SUnfold show ?case by auto
  next case (STyApp t)
    hence "free_vars (unfold_heap h e rs) \<subseteq> set (concat rss)" 
      by (metis free_vars_unfold safe_unfold_order_def concat.simps(2))
    with STyApp have "safe_unfold_order rss (TyApp (unfold_heap h e rs) t) h s \<Gamma>" 
      by (auto simp add: safe_unfold_order_def)
    with STyApp show ?case by auto
  qed

lemma [simp]: "\<Gamma> \<turnstile>\<^sub>s\<^sub>s s : t \<rightarrow> t' \<Longrightarrow> [],\<Gamma> \<turnstile> e : t \<Longrightarrow> safe_unfold_order rs e h s \<Gamma> \<Longrightarrow> 
    [],[] \<turnstile> unstack rs s e h : t'"
  proof (induction rs s e h arbitrary: t rule: unstack.induct)
  case (3 r rs f s e h)
    then obtain e' h' where EH: "unframe f (unfold_heap h e r) h = (e', h')" by fastforce
    from 3 obtain t'' where F: "\<Gamma> \<turnstile>\<^sub>s f : t \<rightarrow> t''" and S: "\<Gamma> \<turnstile>\<^sub>s\<^sub>s s : t'' \<rightarrow> t'" by fastforce
    from 3 EH have X: "safe_unfold_order rs e' h' s \<Gamma>" by fastforce
    from 3 have "[],\<Gamma> \<turnstile> unfold_heap h e r : t" by simp
    with F EH have "[],\<Gamma> \<turnstile> e' : t''" by simp
    with 3 EH S X show ?case by simp
  qed (auto simp add: safe_unfold_order_def)

lemma tc_unstack_state [elim]: "\<Sigma> hastype t \<Longrightarrow> safe_unfold_order\<^sub>\<Sigma> rs \<Sigma> \<Longrightarrow> 
    [],[] \<turnstile> unstack_state rs \<Sigma> : t"
  by (induction \<Sigma> t rule: typecheck_stack_state.induct) simp_all

end