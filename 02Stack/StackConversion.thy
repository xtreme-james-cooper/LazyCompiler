theory StackConversion
imports EvaluateStack
begin

abbreviation unfold_heap :: "expr heap \<Rightarrow> expr \<Rightarrow> nat list \<Rightarrow> expr" where
  "unfold_heap h \<equiv> foldl (\<lambda>e x. Let (lookup\<^sub>h h x) (incr\<^sub>e\<^sub>e x e))"

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
  "map_through \<Gamma> \<equiv> map (the o lookup \<Gamma>)"

fun safe_unfold_order' :: "nat list list \<Rightarrow> nat set \<Rightarrow> expr heap \<Rightarrow> frame list \<Rightarrow> bool" where
  "safe_unfold_order' [] xs h s = True"
| "safe_unfold_order' ([] # rss) xs h s = safe_unfold_order' rss xs h (tl s)"
| "safe_unfold_order' ((r # rs) # rss) xs h s = (
    (\<forall>x. x < length\<^sub>h h \<longrightarrow> x \<notin> xs \<longrightarrow> r \<notin> free_vars (lookup\<^sub>h h x)) \<and> (r \<notin> free_vars\<^sub>s\<^sub>s s) \<and>
      safe_unfold_order' (rs # rss) (insert r xs) h s)"

fun safe_unfold_order :: "nat list list \<Rightarrow> expr heap \<Rightarrow> frame list \<Rightarrow> type list \<Rightarrow> bool" where
  "safe_unfold_order rss h s \<Gamma> = (distinct (concat rss) \<and> length (concat rss) = length \<Gamma> \<and> h \<turnstile>\<^sub>h \<Gamma> \<and>
    length rss = Suc (length s) \<and> (\<forall>r \<in> set (concat rss). r < length \<Gamma>) \<and> 
      safe_unfold_order' rss {} h s)"

lemma [simp]: "[],map_through \<Gamma> rs \<turnstile> e : t \<Longrightarrow> distinct rs \<Longrightarrow> h \<turnstile>\<^sub>h \<Gamma> \<Longrightarrow> length rs = length \<Gamma> \<Longrightarrow> 
  \<forall>i < length rs. rs ! i + i < length \<Gamma> \<Longrightarrow> \<forall>x < length\<^sub>h h. \<forall>r \<in> set rs. r \<notin> free_vars (lookup\<^sub>h h x) \<Longrightarrow> 
    unfold_heap (e, h) rs = (e', h') \<Longrightarrow> [],[] \<turnstile> e' : t"
  proof (induction rs arbitrary: \<Gamma> e h)
  case Nil
    from Nil(7) have "e' = e" by simp
    with Nil(1) show ?case by simp
  next case (Cons r rs)
    from Cons(2) have "[],the (lookup \<Gamma> r) # map_through (remove \<Gamma> r) rs \<turnstile> e : t" by simp
    from Cons(3) have "distinct (r # rs)" by simp
    from Cons(4) have "h \<turnstile>\<^sub>h \<Gamma>" by simp
    from Cons(5) have "Suc (length rs) = length \<Gamma>" by simp
    from Cons(6) have R: "r < length \<Gamma>" by auto
    from Cons(6) have "\<forall>i < Suc (length rs). (r # rs) ! i + i < length \<Gamma>" by simp
    from Cons(7) have "\<forall>x<length\<^sub>h h. \<forall>r\<in>set (r # rs). r \<notin> free_vars (lookup\<^sub>h h x)" by simp



    have X: "[],map_through (remove \<Gamma> r) rs \<turnstile> lookup\<^sub>h h r : the (lookup \<Gamma> r)" by simp
    from Cons(2) have "[],insert_at 0 (the (lookup \<Gamma> r)) (map_through (remove \<Gamma> r) rs) \<turnstile> e : t" 
      by (cases "map_through (remove \<Gamma> r) rs") simp_all
    with X have A: "[],map_through (remove \<Gamma> r) rs \<turnstile> Let (lookup\<^sub>h h r) e : t" by simp
    from Cons have B: "distinct rs" by simp
    from Cons(4, 7) R have C: "map\<^sub>h (decr\<^sub>x\<^sub>e r) (remove\<^sub>h h r) \<turnstile>\<^sub>h remove \<Gamma> r" by simp
    from Cons(5) R have D: "length rs = length (remove \<Gamma> r)" by simp
    from Cons(6) R have E: "\<forall>i<length rs. rs ! i + i < length (remove \<Gamma> r)" by auto


    have F: "\<forall>x<length\<^sub>h (map\<^sub>h (decr\<^sub>x\<^sub>e r) (remove\<^sub>h h r)). \<forall>rr\<in>set rs. 
        rr \<notin> free_vars (lookup\<^sub>h (map\<^sub>h (decr\<^sub>x\<^sub>e r) (remove\<^sub>h h r)) x)" 
      proof (rule, rule, rule)
        fix x rr
        assume X: "x < length\<^sub>h (map\<^sub>h (decr\<^sub>x\<^sub>e r) (remove\<^sub>h h r))"


        assume RS: "rr \<in> set rs"


        from R Cons(4) have R': "r < length\<^sub>h h" by auto


        from X R' have "incr r x < length\<^sub>h h" by (auto simp add: incr_def)
        with Cons(7) have Y: "r \<notin> free_vars (lookup\<^sub>h h (incr r x))" by simp



        have "incr r rr \<notin> free_vars (lookup\<^sub>h h (incr r x))" by simp
        with R' Y show "rr \<notin> free_vars (lookup\<^sub>h (map\<^sub>h (decr\<^sub>x\<^sub>e r) (remove\<^sub>h h r)) x)" by simp
      qed
    from Cons have "unfold_heap (Let (lookup\<^sub>h h r) e, map\<^sub>h (decr\<^sub>x\<^sub>e r) (remove\<^sub>h h r)) rs = (e', h')"
      by simp
    with Cons(1) A B C D E F show ?case by blast
  qed

lemma tc_unstack [elim]: "map_through \<Gamma> (concat rs) \<turnstile>\<^sub>s\<^sub>s s : t \<rightarrow> t' \<Longrightarrow> 
  [],map_through \<Gamma> (concat rs) \<turnstile> e : t \<Longrightarrow> safe_unfold_order rs h s \<Gamma> \<Longrightarrow> 
    unstack rs s (e, h) = (e', h') \<Longrightarrow> [],[] \<turnstile> e' : t'"
  proof (induction rs s "(e, h)" arbitrary: \<Gamma> rule: unstack.induct)
  case 1
    thus ?case by auto
  next case (2 rs rss \<Gamma>)
    hence T: "t = t'" by auto
    moreover from 2 have "[],[] \<turnstile> e' : t" by fastforce
    ultimately show ?case by simp
  next case (3 r rs x s eh)
    thus ?case by simp
  next case (4 r rs e\<^sub>2 s eh)
    thus ?case by simp
  next case (5 r rs l s eh)
    thus ?case by simp
  next case (6 r rs t cs s eh)
    thus ?case by simp
  next case (7 r rs t s eh)
    thus ?case by simp
  next case (8 r rs t s eh)
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