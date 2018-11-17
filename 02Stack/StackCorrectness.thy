theory StackCorrectness
imports "EvaluateStack" "../01Expression/Evaluate" "../Utilities/Iterate"
begin

inductive unstack :: "nat set \<Rightarrow> frame list \<Rightarrow> expr \<Rightarrow> expr heap \<Rightarrow> nat set \<Rightarrow> frame list \<Rightarrow> expr \<Rightarrow> 
    bool" where
  us_nil [simp]: "unstack xs [] e h xs [] e"
| us_sref [simp]: "unstack xs s (Var x) (update\<^sub>h h x e) xs' s' e' \<Longrightarrow> 
    unstack xs (SRef x # s) e h xs' s' e'"
| us_sapp [simp]: "unstack xs s (App e e\<^sub>2) h xs' s' e' \<Longrightarrow> unstack xs (SApp e\<^sub>2 # s) e h xs' s' e'"
| us_sproj [simp]: "unstack xs s (Proj e l) h xs' s' e' \<Longrightarrow> unstack xs (SProj l # s) e h xs' s' e'"
| us_scase [simp]: "unstack xs s (Case e t cs) h xs' s' e' \<Longrightarrow> 
    unstack xs (SCase t cs # s) e h xs' s' e'"
| us_sunfold [simp]: "unstack xs s (Unfold t e) h xs' s' e' \<Longrightarrow> 
    unstack xs (SUnfold t # s) e h xs' s' e'"
| us_styapp [simp]: "unstack xs s (TyApp e t) h xs' s' e' \<Longrightarrow> unstack xs (STyApp t # s) e h xs' s' e'"
| us_let [simp]: "x \<notin> free_vars\<^sub>s\<^sub>s s \<Longrightarrow> x \<notin> xs \<Longrightarrow> 
    x \<notin> \<Union> ((\<lambda>y. free_vars (lookup\<^sub>h y h)) ` {y. y < length\<^sub>h h \<and> y \<noteq> x \<and> y \<notin> xs}) \<Longrightarrow>
      unstack (insert x xs) s (Let (lookup\<^sub>h x h) (incr\<^sub>e\<^sub>e x (subst\<^sub>x\<^sub>e x 0 e))) h xs' s' e' \<Longrightarrow> 
        unstack xs s e h xs' s' e'"

inductive unstack_state :: "stack_state \<Rightarrow> expr \<Rightarrow> bool" where
  uss_eval [simp]: "unstack {} s e h {x. x < length\<^sub>h h} [] e' \<Longrightarrow> 
    unstack_state (StackState (Eval e) s h) e'"
| uss_return [simp]: "unstack {} s (devalue v) h {x. x < length\<^sub>h h} [] e' \<Longrightarrow> 
    unstack_state (StackState (Return v) s h) e'"

lemma tc_unstack [elim]: "unstack xs s e h {x. x < length\<^sub>h h} [] e' \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>s\<^sub>s s : t \<rightarrow> t' \<Longrightarrow> 
  [],\<Gamma> \<turnstile> e : t \<Longrightarrow> h \<turnstile>\<^sub>h \<Gamma> \<Longrightarrow> free_vars e \<inter> xs = {} \<Longrightarrow> free_vars\<^sub>s\<^sub>s s \<inter> xs = {} \<Longrightarrow> 
    (\<forall>x \<in> xs. \<forall>x \<in> {x. x < length\<^sub>h h}. y \<notin> xs \<longrightarrow> x \<notin> free_vars (lookup\<^sub>h y h)) \<Longrightarrow> [],[] \<turnstile> e' : t'"
  proof (induction xs s e h "{x. x < length\<^sub>h h}" "[] :: frame list" e' arbitrary: \<Gamma> t 
         rule: unstack.induct)
  case (us_nil e h)
    hence L: "length\<^sub>h h = length \<Gamma>" by blast
    from us_nil have "[],\<Gamma> \<turnstile> e : t'" by blast
    moreover from us_nil L have "free_vars e \<inter> {x. x < length \<Gamma>} = {}" by simp
    ultimately show ?case by simp
  next case (us_sref xs s x h e e')
    hence "\<Gamma> \<turnstile>\<^sub>s\<^sub>s s : t \<rightarrow> t' \<Longrightarrow>
      [] ,\<Gamma> \<turnstile> Var x : t \<Longrightarrow>
      update\<^sub>h h x e \<turnstile>\<^sub>h \<Gamma> \<Longrightarrow>
      free_vars (Var x) \<inter> xs = {} \<Longrightarrow>
      free_vars\<^sub>s\<^sub>s s \<inter> xs = {} \<Longrightarrow>
      \<forall>xa\<in>xs. \<forall>xa\<in>{xa. xa < length\<^sub>h (update\<^sub>h h x e)}. y \<notin> xs \<longrightarrow> 
        xa \<notin> free_vars (lookup\<^sub>h y (update\<^sub>h h x e)) \<Longrightarrow> 
      [] ,[] \<turnstile> e' : t'" by (metis length\<^sub>h_update\<^sub>h)
    moreover from us_sref have "\<Gamma> \<turnstile>\<^sub>s\<^sub>s s : t \<rightarrow> t'" by simp


    from us_sref have "unstack xs s (Var x) (update\<^sub>h h x e) {x. x < length\<^sub>h h} [] e'" by simp
    from us_sref have "\<Gamma> \<turnstile>\<^sub>s\<^sub>s SRef x # s : t \<rightarrow> t'" by simp
    from us_sref have "[] ,\<Gamma> \<turnstile> e : t" by simp
    from us_sref have "h \<turnstile>\<^sub>h \<Gamma>" by simp
    from us_sref have "free_vars e \<inter> xs = {}" by simp
    from us_sref have "free_vars\<^sub>s\<^sub>s (SRef x # s) \<inter> xs = {}" by simp
    from us_sref have "\<forall>x\<in>xs. \<forall>x\<in>{x. x < length\<^sub>h h}. y \<notin> xs \<longrightarrow> x \<notin> free_vars (lookup\<^sub>h y h)" by simp


    have "[],[] \<turnstile> e' : t'" by simp
    thus ?case by simp
  next case us_sapp
    thus ?case by simp
  next case us_sproj
    thus ?case by simp
  next case us_scase
    thus ?case by simp
  next case us_sunfold
    thus ?case by simp
  next case us_styapp
    thus ?case by simp
  next case (us_let x s xs h e e')



    have "[],[] \<turnstile> e' : t'" by simp
    thus ?case by simp
  qed

lemma tc_unstack_state [elim]: "unstack_state \<Sigma> e \<Longrightarrow> \<Sigma> hastype t \<Longrightarrow> [],[] \<turnstile> e : t"
  proof (induction \<Sigma> e rule: unstack_state.induct)
  case uss_eval
    thus ?case using tc_unstack tc_eval_state by blast
  next case uss_return
    thus ?case using tc_unstack tc_return_state tc_devalue by blast
  qed

lemma complete: "iter (op \<leadsto>) e e' \<Longrightarrow> 
    \<exists>\<Sigma> \<Sigma>'. iter (op \<leadsto>\<^sub>s) \<Sigma> \<Sigma>' \<and> unstack_state \<Sigma> e \<and> unstack_state \<Sigma>' e'"
  by simp

lemma sound: "iter (op \<leadsto>\<^sub>s) \<Sigma> \<Sigma>' \<Longrightarrow> 
    \<exists>e e'. iter (op \<leadsto>) e e' \<and> unstack_state \<Sigma> e \<and> unstack_state \<Sigma>' e'"
  by simp

theorem correct: "iter (op \<leadsto>) e e' \<Longrightarrow> is_value e' \<Longrightarrow> \<exists>v h. e' = devalue v \<and> 
    iter (op \<leadsto>\<^sub>s) (StackState (Eval e) [] empty\<^sub>h) (StackState (Return v) [] h)"
  by simp

end