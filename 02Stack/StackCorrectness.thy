theory StackCorrectness
imports "EvaluateStack" "../01Expression/Evaluate" "../Utilities/Iterate"
begin

inductive unstack :: "frame list \<Rightarrow> expr \<Rightarrow> expr heap \<Rightarrow> frame list \<Rightarrow> expr \<Rightarrow> expr heap \<Rightarrow> bool" where
  us_nil [simp]: "unstack [] e h [] e h"
| us_sref [simp]: "unstack s (Var x) (update\<^sub>h h x e) s' e' h' \<Longrightarrow> unstack (SRef x # s) e h s' e' h'"
| us_sapp [simp]: "unstack s (App e e\<^sub>2) h s' e' h' \<Longrightarrow> unstack (SApp e\<^sub>2 # s) e h s' e' h'"
| us_sproj [simp]: "unstack s (Proj e l) h s' e' h' \<Longrightarrow> unstack (SProj l # s) e h s' e' h'"
| us_scase [simp]: "unstack s (Case e t cs) h s' e' h' \<Longrightarrow> unstack (SCase t cs # s) e h s' e' h'"
| us_sunfold [simp]: "unstack s (Unfold t e) h s' e' h' \<Longrightarrow> unstack (SUnfold t # s) e h s' e' h'"
| us_styapp [simp]: "unstack s (TyApp e t) h s' e' h' \<Longrightarrow> unstack (STyApp t # s) e h s' e' h'"
| us_let [simp]: "length\<^sub>h h > 0 \<Longrightarrow> unextend\<^sub>h h = (e', h') \<Longrightarrow> 
    unstack s (Let e' e) h' s'' e'' h'' \<Longrightarrow> unstack s e h s'' e'' h''"

inductive unstack_state :: "stack_state \<Rightarrow> expr \<Rightarrow> bool" where
  uss_eval [simp]: "unstack s e h [] e' empty\<^sub>h \<Longrightarrow> unstack_state (StackState (Eval e) s h) e'"
| uss_return [simp]: "unstack s (devalue v) h [] e' empty\<^sub>h \<Longrightarrow> 
    unstack_state (StackState (Return v) s h) e'"

lemma tc_unstack [elim]: "unstack s e h [] e' empty\<^sub>h \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>s\<^sub>s s : t \<rightarrow> t' \<Longrightarrow> [],\<Gamma> \<turnstile> e : t \<Longrightarrow> 
    h \<turnstile>\<^sub>h \<Gamma> \<Longrightarrow> [],[] \<turnstile> e' : t'"
  proof (induction s e h "[] :: frame list" e' "empty\<^sub>h :: expr heap" arbitrary: \<Gamma> t 
         rule: unstack.induct)
  case (us_let h e' h' s e e'')
    from us_let have "unextend\<^sub>h h = (e', h')" by simp
    from us_let have "unstack s (Let e' e) h' [] e'' empty\<^sub>h" by simp
    from us_let have "x\<Gamma> \<turnstile>\<^sub>s\<^sub>s s : xt \<rightarrow> t' \<Longrightarrow> [] ,x\<Gamma> \<turnstile> expr.Let e' e : xt \<Longrightarrow> h' \<turnstile>\<^sub>h x\<Gamma> \<Longrightarrow> [],[] \<turnstile> e'' : t'" by simp
    from us_let have "\<Gamma> \<turnstile>\<^sub>s\<^sub>s s : t \<rightarrow> t'" by simp
    from us_let have "[] ,\<Gamma> \<turnstile> e : t" by simp
    from us_let have "h \<turnstile>\<^sub>h \<Gamma>" by simp



    have "[],[] \<turnstile> e'' : t'" by simp
    thus ?case by fastforce
  qed fastforce+

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