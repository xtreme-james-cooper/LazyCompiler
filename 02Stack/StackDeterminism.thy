theory StackDeterminism
imports StackEvaluate
begin

theorem determinism [elim]: "\<Sigma> \<leadsto>\<^sub>s \<Sigma>' \<Longrightarrow> \<Sigma> \<leadsto>\<^sub>s \<Sigma>'' \<Longrightarrow> \<Sigma>' = \<Sigma>''"
  proof (induction \<Sigma> \<Sigma>' rule: evaluate.induct)
  case (ev_var x s h)
    thus ?case by (induction "StackState (Eval (Var x)) s h" \<Sigma>'' rule: evaluate.induct) simp_all
  next case (ev_abs t e s h)
    thus ?case by (induction "StackState (Eval (Abs t e)) s h" \<Sigma>'' rule: evaluate.induct) simp_all
  next case (ev_app e\<^sub>1 e\<^sub>2 s h)
    thus ?case by (induction "StackState (Eval (App e\<^sub>1 e\<^sub>2)) s h" \<Sigma>'' rule: evaluate.induct) simp_all
  next case (ev_let e\<^sub>1 e\<^sub>2 s h)
    thus ?case by (induction "StackState (Eval (Let e\<^sub>1 e\<^sub>2)) s h" \<Sigma>'' rule: evaluate.induct) simp_all
  next case (ev_rec vs s h)
    thus ?case by (induction "StackState (Eval (Rec vs)) s h" \<Sigma>'' rule: evaluate.induct) simp_all
  next case (ev_proj e l s h)
    thus ?case by (induction "StackState (Eval (Proj e l)) s h" \<Sigma>'' rule: evaluate.induct) simp_all
  next case (ev_inj l ts x s h)
    thus ?case 
      by (induction "StackState (Eval (Inj l ts x)) s h" \<Sigma>'' rule: evaluate.induct) simp_all
  next case (ev_case e t cs s h)
    thus ?case 
      by (induction "StackState (Eval (Case e t cs)) s h" \<Sigma>'' rule: evaluate.induct) simp_all
  next case (ev_fold t x s h)
    thus ?case by (induction "StackState (Eval (Fold t x)) s h" \<Sigma>'' rule: evaluate.induct) simp_all
  next case (ev_unfold t e s h)
    thus ?case 
      by (induction "StackState (Eval (Unfold t e)) s h" \<Sigma>'' rule: evaluate.induct) simp_all
  next case (ev_tyabs k e s h)
    thus ?case by (induction "StackState (Eval (TyAbs k e)) s h" \<Sigma>'' rule: evaluate.induct) simp_all
  next case (ev_tyapp e t s h)
    thus ?case by (induction "StackState (Eval (TyApp e t)) s h" \<Sigma>'' rule: evaluate.induct) simp_all
  next case (ev_tylet t e s h)
    thus ?case by (induction "StackState (Eval (TyLet t e)) s h" \<Sigma>'' rule: evaluate.induct) simp_all
  next case (ret_ref v x s h)
    thus ?case 
      by (induction "StackState (Return v) (SRef x # s) h" \<Sigma>'' rule: evaluate.induct) simp_all
  next case (ret_app t e\<^sub>1 e\<^sub>2 s h)
    thus ?case 
      by (induction "StackState (Return (VAbs t e\<^sub>1)) (SApp e\<^sub>2 # s) h" \<Sigma>'' rule: evaluate.induct) 
         simp_all
  next case (ret_proj xs l x s h)
    with ret_proj(2) show ?case 
      by (induction "StackState (Return (VRec xs)) (SProj l # s) h" \<Sigma>'' rule: evaluate.induct) 
         simp_all
  next case (ret_case cs l e ts x t s h)
    with ret_case(2) show ?case 
      by (induction "StackState (Return (VInj l ts x)) (SCase t cs # s) h" \<Sigma>'' 
          rule: evaluate.induct) 
         simp_all
  next case (ret_unfold t x s h)
    thus ?case 
      by (induction "StackState (Return (VFold t x)) (SUnfold t # s) h" \<Sigma>'' rule: evaluate.induct) 
         simp_all
  next case (ret_tyapp k e t s h)
    thus ?case 
      by (induction "StackState (Return (VTyAbs k e)) (STyApp t # s) h" \<Sigma>'' rule: evaluate.induct) 
         simp_all
  qed 
  
end