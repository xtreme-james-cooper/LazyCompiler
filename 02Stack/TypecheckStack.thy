theory TypecheckStack
imports Stack "../01Expression/Typecheck"
begin

inductive typecheck_frame :: "type list \<Rightarrow> frame \<Rightarrow> type list \<Rightarrow> type \<Rightarrow> type \<Rightarrow> bool" 
    (infix "\<turnstile>\<^sub>s _ : _,_ \<rightarrow>" 60) where
  tc_sref [simp]: "lookup x \<Gamma> = Some t \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>s SRef x : \<Gamma>,t \<rightarrow> t"
| tc_sapp [simp]: "[],\<Gamma> \<turnstile> e : t' \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>s SApp e : \<Gamma>,Arrow t' t \<rightarrow> t"
| tc_sbind [simp]: "\<Gamma> \<turnstile>\<^sub>s SBind : t' # \<Gamma>,t \<rightarrow> t"
| tc_sproj [simp]: "lookup l ts = Some t \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>s SProj l : \<Gamma>,Record ts \<rightarrow> t"
| tc_scase [simp]: "[],\<Gamma> \<turnstile>\<^sub>c cs : ts \<rightarrow> t \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>s SCase t cs : \<Gamma>,Variant ts \<rightarrow> t"
| tc_sunfold [simp]: "[k] \<turnstile>\<^sub>k t : Star \<Longrightarrow> 
    \<Gamma> \<turnstile>\<^sub>s SUnfold t : \<Gamma>,Inductive k t \<rightarrow> subst\<^sub>t\<^sub>t 0 (Inductive k t) t"
| tc_styapp [simp]: "[] \<turnstile>\<^sub>k t' : k \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>s STyApp t' : \<Gamma>,Forall k t \<rightarrow> subst\<^sub>t\<^sub>t 0 t' t"

inductive_cases [elim]: "\<Gamma> \<turnstile>\<^sub>s SRef x : \<Gamma>',t \<rightarrow> t'"
inductive_cases [elim]: "\<Gamma> \<turnstile>\<^sub>s SApp e : \<Gamma>',t \<rightarrow> t'"
inductive_cases [elim]: "\<Gamma> \<turnstile>\<^sub>s SBind : \<Gamma>',t \<rightarrow> t'"
inductive_cases [elim]: "\<Gamma> \<turnstile>\<^sub>s SProj l : \<Gamma>',t \<rightarrow> t'"
inductive_cases [elim]: "\<Gamma> \<turnstile>\<^sub>s SCase tt cs : \<Gamma>',t \<rightarrow> t'"
inductive_cases [elim]: "\<Gamma> \<turnstile>\<^sub>s SUnfold tt : \<Gamma>',t \<rightarrow> t'"
inductive_cases [elim]: "\<Gamma> \<turnstile>\<^sub>s STyApp tt : \<Gamma>',t \<rightarrow> t'"

inductive typecheck_stack :: "type list \<Rightarrow> frame list \<Rightarrow> type \<Rightarrow> type \<Rightarrow> bool" 
    (infix "\<turnstile>\<^sub>s\<^sub>s _ : _ \<rightarrow>" 60) where
  tcs_nil [simp]: "[] \<turnstile>\<^sub>s\<^sub>s [] : t \<rightarrow> t"
| tcs_cons [simp]: "\<Gamma> \<turnstile>\<^sub>s f : \<Gamma>',t \<rightarrow> t' \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>s\<^sub>s s : t' \<rightarrow> t'' \<Longrightarrow> \<Gamma>' \<turnstile>\<^sub>s\<^sub>s f # s : t \<rightarrow> t''"

inductive_cases [elim]: "\<Gamma> \<turnstile>\<^sub>s\<^sub>s [] : t \<rightarrow> t'"
inductive_cases [elim]: "\<Gamma> \<turnstile>\<^sub>s\<^sub>s f # s : t \<rightarrow> t'"

inductive typecheck_heap :: "expr list \<Rightarrow> type list \<Rightarrow> bool" 
    (infix "\<turnstile>\<^sub>h" 60) where
  tch_nil [simp]: "[] \<turnstile>\<^sub>h []"
| tch_cons [simp]: "[],\<Gamma> \<turnstile> e : t \<Longrightarrow> h \<turnstile>\<^sub>h \<Gamma> \<Longrightarrow> e # h \<turnstile>\<^sub>h t # \<Gamma>"

inductive_cases [elim]: "[] \<turnstile>\<^sub>h \<Gamma>"
inductive_cases [elim]: "e # h \<turnstile>\<^sub>h \<Gamma>"
inductive_cases [elim]: "h \<turnstile>\<^sub>h []"
inductive_cases [elim]: "h \<turnstile>\<^sub>h t # \<Gamma>"

inductive typecheck_stack_state :: "stack_state \<Rightarrow> type \<Rightarrow> bool" (infix "hastype" 60) where
  tc_stack_state [simp]: "\<Gamma> \<turnstile>\<^sub>s\<^sub>s s : t \<rightarrow> t' \<Longrightarrow> [],\<Gamma> \<turnstile> e : t \<Longrightarrow> h \<turnstile>\<^sub>h \<Gamma> \<Longrightarrow> 
    (m = Return \<longrightarrow> is_value e) \<Longrightarrow> StackState m e s h hastype t'"

inductive_cases [elim]: "StackState m e s h hastype t"

lemma [simp]: "h \<turnstile>\<^sub>h \<Gamma> \<Longrightarrow> lookup x \<Gamma> = Some t \<Longrightarrow> [],\<Gamma> \<turnstile> e : t \<Longrightarrow> update_at x e h \<turnstile>\<^sub>h \<Gamma>"
  proof (induction h \<Gamma> arbitrary: x rule: typecheck_heap.induct)
  case (tch_cons \<Gamma> e' t' h)
    thus ?case
      proof (induction x)
      case 0
        thus ?case by simp
      next case (Suc x)
        from Suc have "[] ,\<Gamma> \<turnstile> e' : t'" by simp
        from Suc have "h \<turnstile>\<^sub>h \<Gamma>" by simp
        from Suc have "[] ,\<Gamma> \<turnstile> e : t \<Longrightarrow> update_at x e h \<turnstile>\<^sub>h \<Gamma>" by simp
        from Suc have "lookup x \<Gamma> = Some t" by simp
        from Suc have "[] ,t' # \<Gamma> \<turnstile> e : t" by simp


        have "[],\<Gamma> \<turnstile> e' : t' \<Longrightarrow> update_at x e h \<turnstile>\<^sub>h \<Gamma> \<Longrightarrow> 
              e' # update_at x e h \<turnstile>\<^sub>h t' # \<Gamma>" by simp

        have "e' # update_at x e h \<turnstile>\<^sub>h t' # \<Gamma>" by simp
        thus ?case by simp
      qed
  qed simp_all

lemma [simp]: "\<Gamma> \<turnstile>\<^sub>s\<^sub>s s : t \<rightarrow> t' \<Longrightarrow> [],\<Gamma> \<turnstile> e : t \<Longrightarrow> h \<turnstile>\<^sub>h \<Gamma> \<Longrightarrow> [],[] \<turnstile> unstack e s h : t'"
  proof (induction \<Gamma> s t t' arbitrary: e h rule: typecheck_stack.induct)
  case (tcs_cons \<Gamma> f \<Gamma>' t t' s t'')
    thus ?case
      proof (induction \<Gamma> f \<Gamma>' t t' rule: typecheck_frame.induct)
      case (tc_sbind \<Gamma> t' t) 
        moreover then obtain v h' where "h = v # h' \<and> ([],\<Gamma> \<turnstile> v : t') \<and> (h' \<turnstile>\<^sub>h \<Gamma>)" 
          by fastforce
        moreover from tc_sbind have "[],insert_at 0 t' \<Gamma> \<turnstile> e : t" by (induction \<Gamma>) simp_all
        ultimately show ?case by auto
      qed simp_all
  qed simp_all

lemma [simp]: "\<Sigma> hastype t \<Longrightarrow> [],[] \<turnstile> unstack_state \<Sigma> : t"
  by (induction \<Sigma> t rule: typecheck_stack_state.induct) simp_all

end