theory TypecheckStack
imports Stack "../01Expression/Typecheck"
begin

inductive typecheck_value :: "kind list \<Rightarrow> type list \<Rightarrow> val \<Rightarrow> type \<Rightarrow> bool" (infix ",_ \<turnstile>\<^sub>v _ :" 60) where
  tc_vabs [simp]: "\<Delta>,insert_at 0 t\<^sub>1 \<Gamma> \<turnstile> e : t\<^sub>2 \<Longrightarrow> \<Delta> \<turnstile>\<^sub>k t\<^sub>1 : Star \<Longrightarrow> \<Delta>,\<Gamma> \<turnstile>\<^sub>v VAbs t\<^sub>1 e : Arrow t\<^sub>1 t\<^sub>2"
| tc_vrec [simp]: "\<Delta>,\<Gamma> \<turnstile>\<^sub>x\<^sub>s fs : ts \<Longrightarrow> \<Delta>,\<Gamma> \<turnstile>\<^sub>v VRec fs : Record ts"
| tc_vinj [simp]: "lookup \<Gamma> x = Some t \<Longrightarrow> lookup ts l = Some t \<Longrightarrow> \<forall>tt \<in> set ts. \<Delta> \<turnstile>\<^sub>k tt : Star \<Longrightarrow> 
    \<Delta>,\<Gamma> \<turnstile>\<^sub>v VInj l ts x : Variant ts"
| tc_vfold [simp]: "lookup \<Gamma> x = Some (subst\<^sub>t\<^sub>t 0 (Inductive k t) t) \<Longrightarrow> 
    insert_at 0 k \<Delta> \<turnstile>\<^sub>k t : Star \<Longrightarrow> \<Delta>,\<Gamma> \<turnstile>\<^sub>v VFold t x : Inductive k t"
| tc_vtyabs [simp]: "insert_at 0 k \<Delta>,map (incr\<^sub>t\<^sub>t 0) \<Gamma> \<turnstile> e : t \<Longrightarrow> \<Delta>,\<Gamma> \<turnstile>\<^sub>v VTyAbs k e : Forall k t"

inductive_cases [elim]: "\<Delta>,\<Gamma> \<turnstile>\<^sub>v VAbs t\<^sub>1 e : t"
inductive_cases [elim]: "\<Delta>,\<Gamma> \<turnstile>\<^sub>v VRec fs : t"
inductive_cases [elim]: "\<Delta>,\<Gamma> \<turnstile>\<^sub>v VInj e ts l : t"
inductive_cases [elim]: "\<Delta>,\<Gamma> \<turnstile>\<^sub>v VFold t' e : t"
inductive_cases [elim]: "\<Delta>,\<Gamma> \<turnstile>\<^sub>v VTyAbs k e : t"

inductive typecheck_frame :: "type list \<Rightarrow> frame \<Rightarrow> type \<Rightarrow> type \<Rightarrow> bool" (infix "\<turnstile>\<^sub>s _ : _ \<rightarrow>" 60) where
  tc_sref [simp]: "lookup \<Gamma> x = Some t \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>s SRef x : t \<rightarrow> t"
| tc_sapp [simp]: "[],\<Gamma> \<turnstile> e : t' \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>s SApp e : Arrow t' t \<rightarrow> t"
| tc_sproj [simp]: "lookup ts l = Some t \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>s SProj l : Record ts \<rightarrow> t"
| tc_scase [simp]: "[],\<Gamma> \<turnstile>\<^sub>c cs : ts \<rightarrow> t \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>s SCase t cs : Variant ts \<rightarrow> t"
| tc_sunfold [simp]: "[k] \<turnstile>\<^sub>k t : Star \<Longrightarrow> 
    \<Gamma> \<turnstile>\<^sub>s SUnfold t : Inductive k t \<rightarrow> subst\<^sub>t\<^sub>t 0 (Inductive k t) t"
| tc_styapp [simp]: "[] \<turnstile>\<^sub>k t' : k \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>s STyApp t' : Forall k t \<rightarrow> subst\<^sub>t\<^sub>t 0 t' t"

inductive_cases [elim]: "\<Gamma> \<turnstile>\<^sub>s SRef x : t \<rightarrow> t'"
inductive_cases [elim]: "\<Gamma> \<turnstile>\<^sub>s SApp e : t \<rightarrow> t'"
inductive_cases [elim]: "\<Gamma> \<turnstile>\<^sub>s SProj l : t \<rightarrow> t'"
inductive_cases [elim]: "\<Gamma> \<turnstile>\<^sub>s SCase tt cs : t \<rightarrow> t'"
inductive_cases [elim]: "\<Gamma> \<turnstile>\<^sub>s SUnfold tt : t \<rightarrow> t'"
inductive_cases [elim]: "\<Gamma> \<turnstile>\<^sub>s STyApp tt : t \<rightarrow> t'"

inductive typecheck_stack :: "type list \<Rightarrow> frame list \<Rightarrow> type \<Rightarrow> type \<Rightarrow> bool" 
    (infix "\<turnstile>\<^sub>s\<^sub>s _ : _ \<rightarrow>" 60) where
  tcs_nil [simp]: "\<Gamma> \<turnstile>\<^sub>s\<^sub>s [] : t \<rightarrow> t"
| tcs_cons [simp]: "\<Gamma> \<turnstile>\<^sub>s f : t \<rightarrow> t' \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>s\<^sub>s s : t' \<rightarrow> t'' \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>s\<^sub>s f # s : t \<rightarrow> t''"

inductive_cases [elim]: "\<Gamma> \<turnstile>\<^sub>s\<^sub>s [] : t \<rightarrow> t'"
inductive_cases [elim]: "\<Gamma> \<turnstile>\<^sub>s\<^sub>s f # s : t \<rightarrow> t'"

definition typecheck_heap :: "expr heap \<Rightarrow> type list \<Rightarrow> bool" (infix "\<turnstile>\<^sub>h" 60) where
  "h \<turnstile>\<^sub>h \<Gamma> = (length\<^sub>h h = length \<Gamma> \<and> (\<forall>i t. lookup \<Gamma> i = Some t \<longrightarrow> [],\<Gamma> \<turnstile> lookup\<^sub>h h i : t))"

inductive typecheck_stack_state :: "stack_state \<Rightarrow> type \<Rightarrow> bool" (infix "hastype" 60) where
  tc_eval_state [simp]: "\<Gamma> \<turnstile>\<^sub>s\<^sub>s s : t \<rightarrow> t' \<Longrightarrow> [],\<Gamma> \<turnstile> e : t \<Longrightarrow> h \<turnstile>\<^sub>h \<Gamma> \<Longrightarrow> 
    StackState (Eval e) s h hastype t'"
| tc_return_state [simp]: "\<Gamma> \<turnstile>\<^sub>s\<^sub>s s : t \<rightarrow> t' \<Longrightarrow> [],\<Gamma> \<turnstile>\<^sub>v v : t \<Longrightarrow> h \<turnstile>\<^sub>h \<Gamma> \<Longrightarrow> 
    StackState (Return v) s h hastype t'"

inductive_cases [elim]: "StackState (Eval e) s h hastype t"
inductive_cases [elim]: "StackState (Return v) s h hastype t"

lemma tc_devalue [simp]: "\<Delta>,\<Gamma> \<turnstile>\<^sub>v v : t \<Longrightarrow> \<Delta>,\<Gamma> \<turnstile> devalue v : t"
  proof (induction \<Delta> \<Gamma> v t rule: typecheck_value.inducts)
  case (tc_vinj \<Gamma> x t ts l \<Delta>)
    hence "lookup \<Gamma> x = Some t" by simp
    moreover from tc_vinj have "lookup ts l = Some t" by simp
    moreover from tc_vinj have "\<forall>tt \<in> set ts. \<Delta> \<turnstile>\<^sub>k tt : Star" by simp
    ultimately show ?case by simp
  qed simp_all

lemma [simp]: "h \<turnstile>\<^sub>h \<Gamma> \<Longrightarrow> lookup \<Gamma> x = Some t \<Longrightarrow> [],\<Gamma> \<turnstile> e : t \<Longrightarrow> update\<^sub>h h x e \<turnstile>\<^sub>h \<Gamma>"
  by (simp add: typecheck_heap_def)

lemma [simp]: "h \<turnstile>\<^sub>h \<Gamma> \<Longrightarrow> [],\<Gamma> \<turnstile> e : t \<Longrightarrow> extend\<^sub>h h e \<turnstile>\<^sub>h insert_at (length\<^sub>h h) t \<Gamma>"
  using lookup_less_than by (unfold typecheck_heap_def) fastforce

lemma [elim]: "h \<turnstile>\<^sub>h \<Gamma> \<Longrightarrow> length\<^sub>h h = length \<Gamma>"
  by (simp add: typecheck_heap_def)

lemma [elim]: "empty\<^sub>h \<turnstile>\<^sub>h \<Gamma> \<Longrightarrow> \<Gamma> = []"
  by (simp add: typecheck_heap_def)

lemma tc_frame_weaken [simp]: "\<Gamma> \<turnstile>\<^sub>s f : t \<rightarrow> t' \<Longrightarrow> insert_at (length \<Gamma>) tt \<Gamma> \<turnstile>\<^sub>s f : t \<rightarrow> t'"
  by (induction \<Gamma> f t t' rule: typecheck_frame.induct) simp_all

lemma tc_stack_weaken [simp]: "\<Gamma> \<turnstile>\<^sub>s\<^sub>s s : t \<rightarrow> t' \<Longrightarrow> insert_at (length \<Gamma>) tt \<Gamma> \<turnstile>\<^sub>s\<^sub>s s : t \<rightarrow> t'"
  proof (induction \<Gamma> s t t' rule: typecheck_stack.induct)
  case (tcs_cons \<Gamma> f t t' s t'')
    hence "insert_at (length \<Gamma>) tt \<Gamma> \<turnstile>\<^sub>s\<^sub>s s : t' \<rightarrow> t''" by simp
    moreover from tcs_cons have "insert_at (length \<Gamma>) tt \<Gamma> \<turnstile>\<^sub>s f : t \<rightarrow> t'" by simp
    ultimately show ?case by simp
  qed simp_all

lemma [simp]: "h \<turnstile>\<^sub>h \<Gamma> \<Longrightarrow> lookup \<Gamma> x = Some t \<Longrightarrow> [],\<Gamma> \<turnstile> lookup\<^sub>h h x : t"
  by (simp add: typecheck_heap_def)

end