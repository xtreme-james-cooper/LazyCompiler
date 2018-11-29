theory StackConversion
imports EvaluateStack
begin

function invert' :: "nat \<Rightarrow> nat list \<Rightarrow> nat list" where 
  "y < length xs \<Longrightarrow> invert' y xs = index_of y xs # invert' (Suc y) xs"
| "y \<ge> length xs \<Longrightarrow> invert' y xs = []"
  by auto fastforce
termination
  by (relation "measure (\<lambda>(y, xs). length xs - y)") simp_all

definition invert :: "nat list \<Rightarrow> nat list" where
  "invert xs = invert' 0 xs"

primrec unfold_heap :: "expr heap \<Rightarrow> expr \<Rightarrow> nat list \<Rightarrow> expr" where
  "unfold_heap h e [] = e"
| "unfold_heap h e (x # xs) = unfold_heap h (Let (lookup\<^sub>h h x) (incr\<^sub>e\<^sub>e x (subst\<^sub>x\<^sub>e x 0 e))) xs"

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

(*

definition map_through :: "'a list \<Rightarrow> nat list \<Rightarrow> 'a list" where
  "map_through \<Gamma> xs = map (\<lambda>x. the (lookup \<Gamma> x)) xs"

lemma [simp]: "lookup \<Gamma> r = Some tt \<Longrightarrow> insert_at 0 tt (map_through \<Gamma> rs) = map_through \<Gamma> (r # rs)" 
  by (cases "map_through \<Gamma> rs") (simp_all add: map_through_def)

lemma [simp]: "length (invert' x rs) = length rs - x"
  by (induction x rs rule: invert'.induct) simp_all

lemma [simp]: "length (invert rs) = length rs"
  by (simp add: invert_def)

lemma [simp]: "x \<in> set xs \<Longrightarrow> lookup \<Gamma> x = Some a \<Longrightarrow> 
    lookup (map_through \<Gamma> xs) (index_of x xs) = Some a"
  by (induction xs) (auto simp add: map_through_def)

lemma [simp]: "x + y < length rs \<Longrightarrow> \<exists>t. lookup (invert' y rs) x = Some t"
  by (induction y rs rule: invert'.induct) simp_all

lemma [simp]: "lookup \<Gamma> (y + x) = Some t \<Longrightarrow> y + x \<in> set rs \<Longrightarrow> y + x < length rs \<Longrightarrow>
    lookup (map_through \<Gamma> rs) (the (lookup (invert' y rs) x)) = Some t"
  proof (induction y rs arbitrary: x rule: invert'.induct)
  case (1 y rs)
    thus ?case
      proof (induction x)
      case (Suc x)
        moreover then obtain x' where "lookup (invert' (Suc y) rs) x = Some x'" by force
        moreover with Suc have "lookup (map_through \<Gamma> rs) x' = Some t" by force
        ultimately show ?case by simp
      qed simp_all
  qed simp_all

lemma [simp]: "lookup \<Gamma> x = Some t \<Longrightarrow> x \<in> set rs \<Longrightarrow> x < length rs \<Longrightarrow>
    lookup (map_through \<Gamma> rs) (the (lookup (invert rs) x)) = Some t"
  by (unfold invert_def) simp

lemma [simp]: "map Suc (invert' y rs) = invert' (Suc y) (0 # map Suc rs)"
  by (induction y rs rule: invert'.induct) simp_all

lemma [simp]: "extend_var_map (invert rs) = invert (extend_var_map rs)"
  by (simp add: extend_var_map_def invert_def)

lemma [simp]: "map_through (insert_at 0 t \<Gamma>) (extend_var_map rs) = insert_at 0 t (map_through \<Gamma> rs)"
  by (cases "map (\<lambda>x. the (lookup \<Gamma> x)) rs") (auto simp add: extend_var_map_def map_through_def)

lemma [simp]: "var_reduce 0 xs \<subseteq> set rs \<Longrightarrow> xs \<subseteq> set (extend_var_map rs)"
  proof (unfold extend_var_map_def var_reduce_def, rule)
    fix x
    assume "decr 0 ` (xs - {0}) \<subseteq> set rs"
       and "x \<in> xs"
    thus "x \<in> set (0 # map Suc rs)" by (cases x) auto
  qed

lemma [simp]: "\<forall>x \<in> var_reduce 0 xs. x < k \<Longrightarrow> \<forall>x \<in> xs. x < Suc k"
  proof (unfold var_reduce_def, rule)
    fix x
    assume "\<forall>x \<in> decr 0 ` (xs - {0}). x < k"
    hence "\<forall>x \<in> xs - {0}. decr 0 x < k" by simp
    moreover assume "x \<in> xs"
    ultimately have "x \<noteq> 0 \<Longrightarrow> decr 0 x < k" by simp
    thus "x < Suc k" by (cases x) (simp_all add: decr_def)
  qed

lemma [simp]: "\<forall>x \<in> set rs. x < length \<Gamma> \<Longrightarrow> map_through (map f \<Gamma>) rs = map f (map_through \<Gamma> rs)"
  proof (unfold map_through_def)
    assume X: "\<forall>x \<in> set rs. x < length \<Gamma>"
    hence "\<And>x. x \<in> set rs \<Longrightarrow> the (map_option f (lookup \<Gamma> x)) = f (the (lookup \<Gamma> x))"
      proof -
        fix x
        assume "x \<in> set rs"
        with X obtain t where "lookup \<Gamma> x = Some t" by fastforce
        thus "the (map_option f (lookup \<Gamma> x)) = f (the (lookup \<Gamma> x))" by simp
      qed
    thus "map (\<lambda>x. the (lookup (map f \<Gamma>) x)) rs = map f (map (\<lambda>x. the (lookup \<Gamma> x)) rs)" by simp
  qed

lemma [simp]: "\<forall>x\<in>set rs. x < k \<Longrightarrow> \<forall>x\<in>set (extend_var_map rs). x < Suc k"
  by (simp add: extend_var_map_def)

lemma [simp]: "\<Delta>,\<Gamma> \<turnstile>\<^sub>x\<^sub>s xs : ts \<Longrightarrow> set xs \<subseteq> set rs \<Longrightarrow> \<forall>x \<in> set rs. x < length rs \<Longrightarrow> 
    \<Delta>,map_through \<Gamma> rs \<turnstile>\<^sub>x\<^sub>s map (\<lambda>y. the (lookup (invert rs) y)) xs : ts"
  by (induction \<Delta> \<Gamma> xs ts rule: typecheck_xs.induct) simp_all

lemma [simp]: "\<Delta>,\<Gamma> \<turnstile> e : t \<Longrightarrow> free_vars e \<subseteq> set rs \<Longrightarrow> \<forall>x \<in> set rs. x < length \<Gamma> \<Longrightarrow>
    \<forall>x \<in> set rs. x < length rs \<Longrightarrow> \<Delta>,map_through \<Gamma> rs \<turnstile> subst\<^sub>x\<^sub>e\<^sub>s (invert rs) e : t"
  and [simp]: "\<Delta>,\<Gamma> \<turnstile>\<^sub>c c : ts \<rightarrow> t \<Longrightarrow> free_vars\<^sub>c c \<subseteq> set rs \<Longrightarrow> \<forall>x \<in> set rs. x < length \<Gamma> \<Longrightarrow>
    \<forall>x \<in> set rs. x < length rs \<Longrightarrow> 
      \<Delta>,map_through \<Gamma> rs \<turnstile>\<^sub>c map (subst\<^sub>x\<^sub>e\<^sub>s (extend_var_map (invert rs))) c : ts \<rightarrow> t"
  proof (induction \<Delta> \<Gamma> e t arbitrary: rs and rs rule: typecheck_typecheck_cs.inducts)
  case (tc_abs \<Delta> t\<^sub>1 \<Gamma> e t\<^sub>2)
    moreover hence "free_vars e \<subseteq> set (extend_var_map rs)" by simp
    moreover from tc_abs have "\<forall>x\<in>set (extend_var_map rs). x < length (extend_var_map rs)" by simp
    moreover from tc_abs have "\<forall>x\<in>set (extend_var_map rs). x < length (insert_at 0 t\<^sub>1 \<Gamma>)" by simp
    ultimately have "\<Delta> ,map_through (insert_at 0 t\<^sub>1 \<Gamma>) (extend_var_map rs) \<turnstile>
      subst\<^sub>x\<^sub>e\<^sub>s (invert (extend_var_map rs)) e : t\<^sub>2" by blast
    with tc_abs show ?case by simp
  next case (tc_let \<Delta> \<Gamma> e\<^sub>1 t\<^sub>1 e\<^sub>2 t\<^sub>2)
    moreover hence "free_vars e\<^sub>2 \<subseteq> set (extend_var_map rs)" by simp
    moreover from tc_let have "\<forall>x \<in> set (extend_var_map rs). x < length (extend_var_map rs)" by simp
    moreover from tc_let have "\<forall>x \<in> set (extend_var_map rs). x < length (insert_at 0 t\<^sub>1 \<Gamma>)" by simp
    ultimately have "\<Delta>,map_through (insert_at 0 t\<^sub>1 \<Gamma>) (extend_var_map rs) \<turnstile> 
      subst\<^sub>x\<^sub>e\<^sub>s (invert (extend_var_map rs)) e\<^sub>2 : t\<^sub>2 " by blast
    with tc_let show ?case by fastforce
  next case (tcc_cons \<Delta> t' \<Gamma> e t cs ts)
    moreover hence "free_vars e \<subseteq> set (extend_var_map rs)" by simp
    moreover from tcc_cons have "\<forall>x\<in>set (extend_var_map rs). x < length (insert_at 0 t' \<Gamma>)" by simp
    moreover from tcc_cons have "\<forall>x\<in>set (extend_var_map rs). x < length (extend_var_map rs)" by simp
    ultimately have "\<Delta>,map_through (insert_at 0 t' \<Gamma>) (extend_var_map rs) \<turnstile> 
      subst\<^sub>x\<^sub>e\<^sub>s (invert (extend_var_map rs)) e : t" by blast
    with tcc_cons show ?case by simp
  qed fastforce+

*)

lemma tc_unfold_heap' [simp]: "[],\<Gamma> \<turnstile> e : t \<Longrightarrow> distinct (ys @ xs) \<Longrightarrow> 
  length (ys @ xs) = length \<Gamma> \<Longrightarrow> h \<turnstile>\<^sub>h \<Gamma> \<Longrightarrow> ordering_for_heap (ys @ xs) h \<Longrightarrow> 
    free_vars e \<inter> set ys = {} \<Longrightarrow> [],[] \<turnstile> unfold_heap h e xs : t"
  proof (induction xs arbitrary: e ys)
  case Nil
    from Nil have "[],\<Gamma> \<turnstile> e : t" by simp
    from Nil have "distinct ys" by simp
    from Nil have "length ys = length \<Gamma>" by simp
    from Nil have "h \<turnstile>\<^sub>h \<Gamma>" by simp
    from Nil have "ordering_for_heap ys h" by simp
    from Nil have "free_vars e \<inter> set ys = {}" by simp


    have "[],[] \<turnstile> e : t" by simp
    thus ?case by simp
  next case (Cons x xs)
    let ?e\<^sub>1 = "lookup\<^sub>h h x"
    let ?e\<^sub>2 = "incr\<^sub>e\<^sub>e x (subst\<^sub>x\<^sub>e x 0 e)"

    from Cons have "[] ,\<Gamma> \<turnstile> e : t" by simp
    from Cons have "distinct (ys @ x # xs)" by simp
    from Cons have "length (ys @ x # xs) = length \<Gamma>" by simp
    from Cons have "h \<turnstile>\<^sub>h \<Gamma>" by simp
    from Cons have "ordering_for_heap (ys @ x # xs) h" by simp
    from Cons(7) have "free_vars e \<inter> set ys = {}" by simp


    from Cons have A: "[],\<Gamma> \<turnstile> Let ?e\<^sub>1 ?e\<^sub>2 : t" by simp
    from Cons have B: "distinct ((ys @ [x]) @ xs)" by simp
    from Cons have C: "length ((ys @ [x]) @ xs) = length \<Gamma>" by simp
    from Cons have D: "h \<turnstile>\<^sub>h \<Gamma> \<Longrightarrow> ordering_for_heap ((ys @ [x]) @ xs) h" by simp


    have X: "free_vars ?e\<^sub>1 \<inter> set (ys @ [x]) = {}" by simp


    from Cons(7) have "var_reduce 0 (free_vars ?e\<^sub>2) \<inter> set (ys @ [x]) = {}" by auto
    with X have "free_vars (Let ?e\<^sub>1 ?e\<^sub>2) \<inter> set (ys @ [x]) = {}" by auto
    with Cons A B C D have "[],[] \<turnstile> unfold_heap h (Let ?e\<^sub>1 ?e\<^sub>2) xs : t" by blast
    thus ?case by simp
  qed

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
  proof (induction rs s e h rule: unstack.induct)
  case (3 r rs x s e h)
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
  qed auto

lemma tc_unstack_state [elim]: "\<Sigma> hastype t \<Longrightarrow> safe_unfold_order\<^sub>\<Sigma> rs \<Sigma> \<Longrightarrow> 
    [],[] \<turnstile> unstack_state rs \<Sigma> : t"
  by (induction \<Sigma> t rule: typecheck_stack_state.induct) simp_all

end