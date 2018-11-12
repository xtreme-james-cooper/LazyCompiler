theory EvaluateStack
imports TypecheckStack
begin

inductive evaluate :: "stack_state \<Rightarrow> stack_state \<Rightarrow> bool" (infix "\<leadsto>\<^sub>s" 60) where
  ev_abs [simp]: "StackState Eval (Abs t e) s h \<leadsto>\<^sub>s StackState Return (Abs t e) s h"
| ev_app [simp]: "StackState Eval (App e\<^sub>1 e\<^sub>2) s h \<leadsto>\<^sub>s StackState Eval e\<^sub>1 (SApp e\<^sub>2 # s) h" 
| ev_let [simp]: "StackState Eval (Let e\<^sub>1 e\<^sub>2) s h \<leadsto>\<^sub>s StackState Eval e\<^sub>2' (SBind # s) (e\<^sub>1 # h)"
| ev_rec [simp]: "list_all is_var vs \<Longrightarrow> \<not> is_var e \<Longrightarrow> 
    StackState Eval (Rec (vs @ [e] @ nvs)) s h \<leadsto>\<^sub>s 
      StackState Eval (Rec (map (incr\<^sub>e\<^sub>e 0) vs @ [Var 0] @ map (incr\<^sub>e\<^sub>e 0) nvs)) (SBind # s) (e # h)" 
| ev_rec2 [simp]: "list_all is_var vs \<Longrightarrow> \<not> is_var e \<Longrightarrow> 
    StackState Eval (Rec vs) s h \<leadsto>\<^sub>s StackState Return (Rec vs) s h" 
| ev_proj [simp]: "StackState Eval (Proj e l) s h \<leadsto>\<^sub>s StackState Eval e (SProj l # s) h"
| ev_inj [simp]: "StackState Eval (Inj l ts e) s h \<leadsto>\<^sub>s 
    StackState Return (if is_var e then Inj l ts e else Inj l ts (Var 0)) s h"
| ev_case [simp]: "StackState Eval (Case e t cs) s h \<leadsto>\<^sub>s StackState Eval e (SCase t cs # s) h"
| ev_fold [simp]: "StackState Eval (Fold t e) s h \<leadsto>\<^sub>s 
    StackState Return (if is_var e then Fold t e else Let e (Fold t (Var 0))) s h" 
| ev_unfold [simp]: "StackState Eval (Unfold t e) s h \<leadsto>\<^sub>s StackState Eval e (SUnfold t # s) h"  
| ev_tyabs [simp]: "StackState Eval (TyAbs k e) s h \<leadsto>\<^sub>s StackState Return (TyAbs k e) s h" 
| ev_tyapp [simp]: "StackState Eval (TyApp e t) s h \<leadsto>\<^sub>s StackState Eval e (STyApp t # s) h" 
| ev_tylet [simp]: "StackState Eval (TyLet t e) s h \<leadsto>\<^sub>s StackState Eval (subst\<^sub>t\<^sub>e 0 t e) s h" 
| ret_app [simp]: 
    "StackState Return (Abs t e\<^sub>1) (SApp e\<^sub>2 # s) h \<leadsto>\<^sub>s StackState Eval e\<^sub>1 (SBind # s) (e\<^sub>2 # h)"
| ret_proj [simp]: "lookup l fs = Some e \<Longrightarrow> 
    StackState Return (Rec fs) (SProj l # s) h \<leadsto>\<^sub>s StackState Eval e s h" 
| ret_case [simp]: "lookup l cs = Some e' \<Longrightarrow> 
    StackState Return (Inj l ts e) (SCase t cs # s) h \<leadsto>\<^sub>s StackState Eval e' (SBind # s) (e # h)"
| ret_unfold [simp]: "StackState Return (Fold t e) (SUnfold t # s) h \<leadsto>\<^sub>s StackState Eval e s h" 
| ret_tyapp [simp]: 
    "StackState Return (TyAbs k e) (STyApp t # s) h \<leadsto>\<^sub>s StackState Eval (subst\<^sub>t\<^sub>e 0 t e) s h" 
| ret_app_let [simp]: "StackState Return (Let e\<^sub>1\<^sub>1 e\<^sub>1\<^sub>2) (SApp e\<^sub>2 # s) h \<leadsto>\<^sub>s 
    StackState Eval e\<^sub>1\<^sub>2 (SApp (incr\<^sub>e\<^sub>e 0 e\<^sub>2) # SBind # s) (e\<^sub>1\<^sub>1 # h)"
| ret_proj_let [simp]: "StackState Return (Let e\<^sub>1 e\<^sub>2) (SProj l # s) h \<leadsto>\<^sub>s 
    StackState Eval e\<^sub>2 (SProj l # SBind # s) (e\<^sub>1 # h)" 
| ret_case_let [simp]: "StackState Return (Let e\<^sub>1 e\<^sub>2) (SCase t cs # s) h \<leadsto>\<^sub>s 
    StackState Eval e\<^sub>2 (SCase t (map (incr\<^sub>e\<^sub>e (Suc 0)) cs) # SBind # s) (e\<^sub>1 # h)" 
| ret_unfold_let [simp]: "StackState Return (Let e\<^sub>1 e\<^sub>2) (SUnfold t # s) h \<leadsto>\<^sub>s 
    StackState Eval e\<^sub>2 (SUnfold t # SBind # s) (e\<^sub>1 # h)"
| ret_tyapp_let [simp]: "StackState Return (Let e\<^sub>1 e\<^sub>2) (STyApp t # s) h \<leadsto>\<^sub>s 
    StackState Eval e\<^sub>2 (STyApp t # SBind # s) (e\<^sub>1 # h)" 

primrec is_final :: "stack_state \<Rightarrow> bool" where
  "is_final (StackState m e s h) = (m = Return \<and> s = [])"

theorem progress: "\<Sigma> hastype t \<Longrightarrow> is_final \<Sigma> \<or> (\<exists>\<Sigma>'. \<Sigma> \<leadsto>\<^sub>s \<Sigma>')"
  proof (induction \<Sigma> t rule: typecheck_stack_state.induct)
  case (tc_stack_state \<Gamma> s t t' e h m)
    thus ?case
      proof (induction m)
      case Eval
        thus ?case
          proof (induction e)
          case Var
            thus ?case by simp
          next case Abs
            thus ?case by (metis ev_abs)
          next case App
            thus ?case by (metis ev_app)
          next case Let
            thus ?case by (metis ev_let)
          next case Rec
            thus ?case by (metis ev_app)
          next case Proj
            thus ?case by (metis ev_proj)
          next case Inj 
            thus ?case by (metis ev_inj)
          next case Case
            thus ?case by (metis ev_case)
          next case Fold 
            thus ?case by (metis ev_fold)
          next case Unfold
            thus ?case by (metis ev_unfold)
          next case TyAbs
            thus ?case by (metis ev_tyabs)
          next case TyApp
            thus ?case by (metis ev_tyapp)
          next case TyLet
            thus ?case by (metis ev_tylet)
          qed
      next case Return
        thus ?case
          proof (induction \<Gamma> s t t' rule: typecheck_stack.induct)
          case (tcs_cons \<Gamma> f \<Gamma>' t t' s t'')
            from tcs_cons have "\<Gamma> \<turnstile>\<^sub>s f : \<Gamma>',t \<rightarrow> t'" by simp
            from tcs_cons have "\<Gamma> \<turnstile>\<^sub>s\<^sub>s s : t' \<rightarrow> t''" by simp
            from tcs_cons have "[] ,\<Gamma> \<turnstile> e : t' \<Longrightarrow> h \<turnstile>\<^sub>h \<Gamma> \<Longrightarrow> s = [] \<or> (\<exists>a. StackState Return e s h \<leadsto>\<^sub>s a)" by simp
            from tcs_cons have "[] ,\<Gamma>' \<turnstile> e : t" by simp
            from tcs_cons have "h \<turnstile>\<^sub>h \<Gamma>'" by simp
            from tcs_cons have "is_value e" by simp
        
        
            have "StackState Return e (f # s) h \<leadsto>\<^sub>s \<Sigma>'" by simp
            thus ?case by fastforce
          qed simp_all
      qed
  qed

theorem preservation: "\<Sigma> \<leadsto>\<^sub>s \<Sigma>' \<Longrightarrow> \<Sigma> hastype t \<Longrightarrow> \<Sigma>' hastype t"
  proof (induction \<Sigma> \<Sigma>' rule: evaluate.induct)
  case (ev_app e\<^sub>1 e\<^sub>2 s h)
    then obtain \<Gamma> t\<^sub>1 t\<^sub>2 where "(\<Gamma> \<turnstile>\<^sub>s\<^sub>s s : t\<^sub>2 \<rightarrow> t) \<and> ([],\<Gamma> \<turnstile> e\<^sub>1 : Arrow t\<^sub>1 t\<^sub>2) \<and> 
      ([],\<Gamma> \<turnstile> e\<^sub>2 : t\<^sub>1) \<and> (h \<turnstile>\<^sub>h \<Gamma>)" by fastforce
    moreover hence "\<Gamma> \<turnstile>\<^sub>s\<^sub>s SApp e\<^sub>2 # s : Arrow t\<^sub>1 t\<^sub>2 \<rightarrow> t" by (metis tc_sapp tcs_cons)
    ultimately show ?case by simp
  qed simp_all

end