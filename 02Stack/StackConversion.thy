theory StackConversion
imports EvaluateStack
begin

primrec invert :: "nat list \<Rightarrow> nat list" where
  "invert [] = []"
| "invert (x # xs) = insert_at x 0 (invert xs)"

abbreviation unfold_heap :: "expr heap \<Rightarrow> expr \<Rightarrow> nat list \<Rightarrow> expr" where
  "unfold_heap h e rs \<equiv> 
    fst (foldl (\<lambda>(e, rs) x. (Let (subst\<^sub>x\<^sub>e\<^sub>s (invert rs) (lookup\<^sub>h h x)) e, tl rs)) (e, rs) rs)"

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

abbreviation map_through :: "'a list \<Rightarrow> nat list \<Rightarrow> 'a list" where
  "map_through \<Gamma> \<equiv> map (\<lambda>x. the (lookup \<Gamma> x))"

fun safe_unfold_order' :: "nat list list \<Rightarrow> expr heap \<Rightarrow> frame list \<Rightarrow> bool" where
  "safe_unfold_order' [] h s = True"
| "safe_unfold_order' ([] # rss) h s = safe_unfold_order' rss h (tl s)"
| "safe_unfold_order' ((r # rs) # rss) h s = (
    (free_vars (lookup\<^sub>h h r) \<subseteq> set (rs @ concat rss)) \<and> (r \<notin> free_vars\<^sub>s\<^sub>s s) \<and>
      safe_unfold_order' (rs # rss) h s)"

fun safe_unfold_order :: "nat list list \<Rightarrow> expr heap \<Rightarrow> frame list \<Rightarrow> type list \<Rightarrow> bool" where
  "safe_unfold_order rss h s \<Gamma> = (distinct (concat rss) \<and> length (concat rss) = length \<Gamma> \<and> h \<turnstile>\<^sub>h \<Gamma> \<and>
    length rss = Suc (length s) \<and> (\<forall>r \<in> set (concat rss). r < length \<Gamma>) \<and> 
      safe_unfold_order' rss h s)"

lemma [simp]: "lookup \<Gamma> r = Some tt \<Longrightarrow> insert_at 0 tt (map_through \<Gamma> rs) = map_through \<Gamma> (r # rs)" 
  by (cases "map_through \<Gamma> rs") simp_all

lemma [simp]: "\<Delta>,\<Gamma> \<turnstile> e : t \<Longrightarrow> \<Delta>,map_through \<Gamma> rs \<turnstile> subst\<^sub>x\<^sub>e\<^sub>s (invert rs) e : t"
  apply (induction rs)
  apply simp_all
  by simp

lemma [simp]: "[],map_through \<Gamma> rs \<turnstile> e : t \<Longrightarrow> distinct rs \<Longrightarrow> 
  \<forall>r \<in> set rs. r < length \<Gamma> \<Longrightarrow> h \<turnstile>\<^sub>h \<Gamma> \<Longrightarrow> safe_unfold_order' [rs] h [] \<Longrightarrow>
    [],[] \<turnstile> unfold_heap h e rs : t"
  proof (induction rs arbitrary: e)
  case Nil
    from Nil(1) show ?case by simp
  next case (Cons r rs)
    from Cons have "[],map_through \<Gamma> (r # rs) \<turnstile> e : t" by blast
    from Cons have "distinct (r # rs)" by simp
    from Cons have "\<forall>r\<in>set (r # rs). r < length \<Gamma>" by simp
    then obtain tt where T: "lookup \<Gamma> r = Some tt" by fastforce

    from Cons(5) have "h \<turnstile>\<^sub>h \<Gamma>" by simp
    with T have "[],\<Gamma> \<turnstile> lookup\<^sub>h h r : tt" by (simp add: typecheck_heap_def)

    from Cons have "free_vars (lookup\<^sub>h h r) \<subseteq> set rs" by simp
    from Cons have "safe_unfold_order' [rs] h []" by simp



    have "[],map_through \<Gamma> rs \<turnstile> subst\<^sub>x\<^sub>e\<^sub>s (invert (r # rs)) (lookup\<^sub>h h r) : tt" by simp
    moreover from Cons(2) T have "[],insert_at 0 tt (map_through \<Gamma> rs) \<turnstile> e : t" by simp
    ultimately have A: "[],map_through \<Gamma> rs \<turnstile> Let (subst\<^sub>x\<^sub>e\<^sub>s (invert (r # rs)) (lookup\<^sub>h h r)) e : t" by simp
    from Cons have B: "distinct rs" by simp
    from Cons have C: "\<forall>r\<in>set rs. r < length \<Gamma>" by simp
    from Cons have D: "h \<turnstile>\<^sub>h \<Gamma>" by simp
    from Cons have "safe_unfold_order' [rs] h []" by simp
    with Cons(1) A B C D have 
      "[],[] \<turnstile> unfold_heap h (Let (subst\<^sub>x\<^sub>e\<^sub>s (invert (r # rs)) (lookup\<^sub>h h r)) e) rs : t" by blast
    thus ?case by simp
  qed

lemma tc_unstack [elim]: "map_through \<Gamma> (concat rs) \<turnstile>\<^sub>s\<^sub>s s : t \<rightarrow> t' \<Longrightarrow> 
  \<Delta>,map_through \<Gamma> (concat rs) \<turnstile> e : t \<Longrightarrow> safe_unfold_order rs h s \<Gamma> \<Longrightarrow> 
    \<Delta>,[] \<turnstile> unstack rs s e h : t'"
  proof (induction rs s e h rule: unstack.induct)
  case 1
    thus ?case by auto
  next case (2 rs rss e h)
    hence T: "t = t'" by auto


    from 2 have "distinct rs" by auto
    from 2 have "length rs = length \<Gamma>" by auto
    from 2 have "h \<turnstile>\<^sub>h \<Gamma>" by auto
    from 2 have RSS: "rss = []" by auto
    from 2 have "\<forall>r \<in> set rs. r < length \<Gamma>" by auto
    from 2 have "safe_unfold_order' [rs] h []" by auto


    from 2(3) RSS have "\<Delta>,map_through \<Gamma> rs \<turnstile> e : t" by (metis concat.simps append_Nil2)


    hence "\<Delta>,[] \<turnstile> unfold_heap h e rs : t" by simp
    with T RSS show ?case by simp
  next case (3 r rs x s e h)
    thus ?case by simp
  next case (4 r rs e\<^sub>2 s e h)
    thus ?case by simp
  next case (5 r rs l s e h)
    thus ?case by simp
  next case (6 r rs t cs s e h)
    thus ?case by simp
  next case (7 r rs t s e h)
    thus ?case by simp
  next case (8 r rs t s e h)
    thus ?case by simp
  qed

lemma tc_unstack_state [elim]: "\<Sigma> hastype t \<Longrightarrow> unstack_state rs \<Sigma> = (e, h) \<Longrightarrow> [],[] \<turnstile> e : t"
  proof (induction rs \<Sigma> rule: unstack_state.induct)
  case 1
    thus ?case using tc_unstack tc_eval_state by blast
  next case 2
    thus ?case using tc_unstack tc_return_state tc_devalue by blast
  qed

end