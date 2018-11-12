theory Evaluate
imports Stack
begin

inductive evaluate :: "stack_state \<Rightarrow> stack_state \<Rightarrow> bool" (infix "\<leadsto>\<^sub>s" 60) where
  ev_app [simp]: "StackState Eval (App e\<^sub>1 e\<^sub>2) s h \<leadsto>\<^sub>s StackState Eval e\<^sub>1 (SApp e\<^sub>2 # s) h" 
| ev_let [simp]: "StackState Eval (Let e\<^sub>1 e\<^sub>2) s h \<leadsto>\<^sub>s StackState Eval e\<^sub>2' (SBind # s) (e\<^sub>1 # h)"
| ev_rec [simp]: "list_all is_var vs \<Longrightarrow> \<not> is_var e \<Longrightarrow> 
    StackState Eval (Rec (vs @ [e] @ nvs)) s h \<leadsto>\<^sub>s 
      StackState Eval (Let e (Rec (map (incr\<^sub>e\<^sub>e 0) vs @ [Var 0] @ map (incr\<^sub>e\<^sub>e 0) nvs))) s h" 
| ev_proj [simp]: "StackState Eval (Proj e l) s h \<leadsto>\<^sub>s StackState Eval e (SProj l # s) h"
| ev_inj [simp]: "\<not> is_var e \<Longrightarrow> StackState Eval (Inj l ts e) s h \<leadsto>\<^sub>s 
    StackState Eval (Let e (Inj l ts (Var 0))) s h"
| ev_case [simp]: "StackState Eval (Case e t cs) s h \<leadsto>\<^sub>s StackState Eval e (SCase t cs # s) h"
| ev_fold [simp]: "\<not> is_var e \<Longrightarrow> 
    StackState Eval (Fold t e) s h \<leadsto>\<^sub>s StackState Eval (Let e (Fold t (Var 0))) s h" 
| ev_unfold [simp]: "StackState Eval (Unfold t e) s h \<leadsto>\<^sub>s StackState Eval e (SUnfold t # s) h"  
| ev_tyapp [simp]: "StackState Eval (TyApp e t) s h \<leadsto>\<^sub>s StackState Eval e (STyApp t # s) h" 
| ev_tylet [simp]: "StackState Eval (TyLet t e) s h \<leadsto>\<^sub>s StackState Eval (subst\<^sub>t\<^sub>e 0 t e) s h" 
| ret_app [simp]: "StackState Return (Abs t e\<^sub>1) (SApp e\<^sub>2 # s) h \<leadsto>\<^sub>s StackState Eval (Let e\<^sub>2 e\<^sub>1) s h"
| ret_app_let [simp]: "StackState Return (Let e\<^sub>1\<^sub>1 e\<^sub>1\<^sub>2) (SApp e\<^sub>2 # s) h \<leadsto>\<^sub>s 
    StackState Eval (Let e\<^sub>1\<^sub>1 (App e\<^sub>1\<^sub>2 (incr\<^sub>e\<^sub>e 0 e\<^sub>2))) s h"
| ret_proj [simp]: "lookup l fs = Some e \<Longrightarrow> 
    StackState Return (Rec fs) (SProj l # s) h \<leadsto>\<^sub>s StackState Eval e s h" 
| ret_proj_let [simp]: 
    "StackState Return (Let e\<^sub>1 e\<^sub>2) (SProj l # s) h \<leadsto>\<^sub>s StackState Eval (Let e\<^sub>1 (Proj e\<^sub>2 l)) s h" 
| ret_case [simp]: "lookup l cs = Some e' \<Longrightarrow> 
    StackState Return (Inj l ts e) (SCase t cs # s) h \<leadsto>\<^sub>s StackState Eval (Let e e') s h"
| ret_case_let [simp]: "StackState Return (Let e\<^sub>1 e\<^sub>2) (SCase t cs # s) h \<leadsto>\<^sub>s 
    StackState Eval (Let e\<^sub>1 (Case e\<^sub>2 t (map (incr\<^sub>e\<^sub>e (Suc 0)) cs))) s h" 
| ret_unfold [simp]: "StackState Return (Fold t e) (SUnfold t # s) h \<leadsto>\<^sub>s StackState Eval e s h" 
| ret_unfold_let [simp]: 
    "StackState Return (Let e\<^sub>1 e\<^sub>2) (SUnfold t # s) h \<leadsto>\<^sub>s StackState Eval (Let e\<^sub>1 (Unfold t e\<^sub>2)) s h"
| ret_tyapp [simp]: 
    "StackState Return (TyAbs k e) (STyApp t # s) h \<leadsto>\<^sub>s StackState Eval (subst\<^sub>t\<^sub>e 0 t e) s h" 
| ret_tyapp_let [simp]: 
    "StackState Return (Let e\<^sub>1 e\<^sub>2) (STyApp t # s) h \<leadsto>\<^sub>s StackState Eval (Let e\<^sub>1 (TyApp e\<^sub>2 t)) s h" 

end