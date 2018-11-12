theory Typecheck
imports Stack "../01Expression/Typecheck"
begin

inductive typecheck_frame :: "kind list \<Rightarrow> type list \<Rightarrow> frame \<Rightarrow> type list \<Rightarrow> type \<Rightarrow> type \<Rightarrow> bool" 
    (infix ",_ \<turnstile>\<^sub>s _ : _,_ \<rightarrow>" 60) where
  tc_sapp [simp]: "\<Delta>,\<Gamma> \<turnstile> e : t' \<Longrightarrow> \<Delta>,\<Gamma> \<turnstile>\<^sub>s SApp e : \<Gamma>,Arrow t' t \<rightarrow> t"
| tc_sbind [simp]: "\<Delta>,\<Gamma> \<turnstile>\<^sub>s SBind : t' # \<Gamma>,t \<rightarrow> t"
| tc_sproj [simp]: "lookup l ts = Some t \<Longrightarrow> \<Delta>,\<Gamma> \<turnstile>\<^sub>s SProj l : \<Gamma>,Record ts \<rightarrow> t"
| tc_scase [simp]: "\<Delta>,\<Gamma> \<turnstile>\<^sub>c cs : ts \<rightarrow> t \<Longrightarrow> \<Delta>,\<Gamma> \<turnstile>\<^sub>s SCase t cs : \<Gamma>,Variant ts \<rightarrow> t"
| tc_sunfold [simp]: "insert_at 0 k \<Delta> \<turnstile>\<^sub>k t : Star \<Longrightarrow> 
    \<Delta>,\<Gamma> \<turnstile>\<^sub>s SUnfold t : \<Gamma>,Inductive k t \<rightarrow> subst\<^sub>t\<^sub>t 0 (Inductive k t) t"
| tc_styapp [simp]: "\<Delta> \<turnstile>\<^sub>k t' : k \<Longrightarrow> \<Delta>,\<Gamma> \<turnstile>\<^sub>s STyApp t' : \<Gamma>,Forall k t \<rightarrow> subst\<^sub>t\<^sub>t 0 t' t"

inductive_cases [elim]: "\<Delta>,\<Gamma> \<turnstile>\<^sub>s SApp e : \<Gamma>',t \<rightarrow> t'"
inductive_cases [elim]: "\<Delta>,\<Gamma> \<turnstile>\<^sub>s SBind : \<Gamma>',t \<rightarrow> t'"
inductive_cases [elim]: "\<Delta>,\<Gamma> \<turnstile>\<^sub>s SProj l : \<Gamma>',t \<rightarrow> t'"
inductive_cases [elim]: "\<Delta>,\<Gamma> \<turnstile>\<^sub>s SCase tt cs : \<Gamma>',t \<rightarrow> t'"
inductive_cases [elim]: "\<Delta>,\<Gamma> \<turnstile>\<^sub>s SUnfold tt : \<Gamma>',t \<rightarrow> t'"
inductive_cases [elim]: "\<Delta>,\<Gamma> \<turnstile>\<^sub>s STyApp tt : \<Gamma>',t \<rightarrow> t'"

inductive typecheck_stack :: "kind list \<Rightarrow> frame list \<Rightarrow> type list \<Rightarrow> type \<Rightarrow> type \<Rightarrow> bool" 
    (infix "\<turnstile>\<^sub>s\<^sub>s _ : _,_ \<rightarrow>" 60) where
  tcs_nil [simp]: "\<Delta> \<turnstile>\<^sub>s\<^sub>s [] : [],t \<rightarrow> t"
| tcs_cons [simp]: "\<Delta>,\<Gamma> \<turnstile>\<^sub>s f : \<Gamma>',t \<rightarrow> t' \<Longrightarrow> \<Delta> \<turnstile>\<^sub>s\<^sub>s s : \<Gamma>,t' \<rightarrow> t'' \<Longrightarrow> \<Delta> \<turnstile>\<^sub>s\<^sub>s f # s : \<Gamma>',t \<rightarrow> t''"

inductive_cases [elim]: "\<Delta> \<turnstile>\<^sub>s\<^sub>s [] : \<Gamma>,t \<rightarrow> t'"
inductive_cases [elim]: "\<Delta> \<turnstile>\<^sub>s\<^sub>s f # s : \<Gamma>,t \<rightarrow> t'"

inductive typecheck_heap :: "kind list \<Rightarrow> expr list \<Rightarrow> type list \<Rightarrow> bool" 
    (infix "\<turnstile>\<^sub>h _ :" 60) where
  tch_nil [simp]: "\<Delta> \<turnstile>\<^sub>h [] : []"
| tch_cons [simp]: "\<Delta>,\<Gamma> \<turnstile> e : t \<Longrightarrow> \<Delta> \<turnstile>\<^sub>h h : \<Gamma> \<Longrightarrow> \<Delta> \<turnstile>\<^sub>h e # h : t # \<Gamma>"

inductive_cases [elim]: "\<Delta> \<turnstile>\<^sub>h [] : \<Gamma>"
inductive_cases [elim]: "\<Delta> \<turnstile>\<^sub>h e # h : \<Gamma>"
inductive_cases [elim]: "\<Delta> \<turnstile>\<^sub>h h : []"
inductive_cases [elim]: "\<Delta> \<turnstile>\<^sub>h h : t # \<Gamma>"

inductive typecheck_stack_state :: "stack_state \<Rightarrow> type \<Rightarrow> bool" (infix "hastype" 60) where
  tc_stack_state [simp]: "[] \<turnstile>\<^sub>s\<^sub>s s : \<Gamma>,t \<rightarrow> t' \<Longrightarrow> [],\<Gamma> \<turnstile> e : t \<Longrightarrow> [] \<turnstile>\<^sub>h h : \<Gamma> \<Longrightarrow> 
    (b = Return \<longrightarrow> is_value e) \<Longrightarrow> StackState b e s h hastype t'"

inductive_cases [elim]: "StackState b e s h hastype t"

lemma [simp]: "\<Delta> \<turnstile>\<^sub>s\<^sub>s s : \<Gamma>,t \<rightarrow> t' \<Longrightarrow> \<Delta>,\<Gamma> \<turnstile> e : t \<Longrightarrow> \<Delta> \<turnstile>\<^sub>h h : \<Gamma> \<Longrightarrow> 
    \<Delta>,[] \<turnstile> unstack e s h : t'"
  proof (induction \<Delta> s \<Gamma> t t' arbitrary: e h rule: typecheck_stack.induct)
  case (tcs_cons \<Delta> \<Gamma> f \<Gamma>' t t' s t'')
    thus ?case
      proof (induction \<Delta> \<Gamma> f \<Gamma>' t t' rule: typecheck_frame.induct)
      case (tc_sbind \<Delta> \<Gamma> t' t) 
        then obtain v h' where H: "h = v # h' \<and> (\<Delta>,\<Gamma> \<turnstile> v : t') \<and> (\<Delta> \<turnstile>\<^sub>h h' : \<Gamma>)" by fastforce
        from tc_sbind have "\<Delta>,insert_at 0 t' \<Gamma> \<turnstile> e : t" by (cases \<Gamma>) simp_all
        with tc_sbind H show ?case by auto
      qed simp_all
  qed simp_all

lemma [simp]: "\<Sigma> hastype t \<Longrightarrow> [],[] \<turnstile> unstack_state \<Sigma> : t"
  by (induction \<Sigma> t rule: typecheck_stack_state.induct) simp_all

end