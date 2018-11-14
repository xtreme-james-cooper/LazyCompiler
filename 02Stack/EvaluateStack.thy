theory EvaluateStack
imports TypecheckStack
begin

inductive evaluate :: "stack_state \<Rightarrow> stack_state \<Rightarrow> bool" (infix "\<leadsto>\<^sub>s" 60) where
  ev_var [simp]: "StackState (Eval (Var x)) s h \<leadsto>\<^sub>s StackState (Eval (lookup\<^sub>h x h)) (SRef x # s) h"
| ev_abs [simp]: "StackState (Eval (Abs t e)) s h \<leadsto>\<^sub>s StackState (Return (VAbs t e)) s h"
| ev_app [simp]: "StackState (Eval (App e\<^sub>1 e\<^sub>2)) s h \<leadsto>\<^sub>s StackState (Eval e\<^sub>1) (SApp e\<^sub>2 # s) h" 
| ev_let [simp]: "StackState (Eval (Let e\<^sub>1 e\<^sub>2)) s h \<leadsto>\<^sub>s 
    StackState (Eval (subst\<^sub>e\<^sub>e 0 (Var (length\<^sub>h h)) e\<^sub>2)) s (extend\<^sub>h h e\<^sub>1)"
| ev_rec1 [simp]: "list_all is_var vs \<Longrightarrow> \<not> is_var e \<Longrightarrow> 
    StackState (Eval (Rec (vs @ [e] @ nvs))) s h \<leadsto>\<^sub>s 
      StackState (Eval (Rec (vs @ [Var (length\<^sub>h h)] @ nvs))) s (extend\<^sub>h h e)" 
| ev_rec2 [simp]: "list_all is_var vs \<Longrightarrow>
    StackState (Eval (Rec vs)) s h \<leadsto>\<^sub>s StackState (Return (VRec (map devar vs))) s h" 
| ev_proj [simp]: "StackState (Eval (Proj e l)) s h \<leadsto>\<^sub>s StackState (Eval e) (SProj l # s) h"
| ev_inj1 [simp]: "StackState (Eval (Inj l ts (Var x))) s h \<leadsto>\<^sub>s StackState (Return (VInj l ts x)) s h"
| ev_inj2 [simp]: "\<not> is_var e \<Longrightarrow> StackState (Eval (Inj l ts e)) s h \<leadsto>\<^sub>s 
    StackState (Return (VInj l ts (length\<^sub>h h))) s (extend\<^sub>h h e)"
| ev_case [simp]: "StackState (Eval (Case e t cs)) s h \<leadsto>\<^sub>s StackState (Eval e) (SCase t cs # s) h"
| ev_fold1 [simp]: "StackState (Eval (Fold t (Var x))) s h \<leadsto>\<^sub>s StackState (Return (VFold t x)) s h" 
| ev_fold2 [simp]: "\<not> is_var e \<Longrightarrow> 
    StackState (Eval (Fold t e)) s h \<leadsto>\<^sub>s StackState (Return (VFold t (length\<^sub>h h))) s (extend\<^sub>h h e)" 
| ev_unfold [simp]: "StackState (Eval (Unfold t e)) s h \<leadsto>\<^sub>s StackState (Eval e) (SUnfold t # s) h"  
| ev_tyabs [simp]: "StackState (Eval (TyAbs k e)) s h \<leadsto>\<^sub>s StackState (Return (VTyAbs k e)) s h" 
| ev_tyapp [simp]: "StackState (Eval (TyApp e t)) s h \<leadsto>\<^sub>s StackState (Eval e) (STyApp t # s) h" 
| ev_tylet [simp]: "StackState (Eval (TyLet t e)) s h \<leadsto>\<^sub>s StackState (Eval (subst\<^sub>t\<^sub>e 0 t e)) s h" 
| ret_ref [simp]: "StackState (Return v) (SRef x # s) h \<leadsto>\<^sub>s StackState (Return v) s (update\<^sub>h h x e)"
| ret_app [simp]: 
    "StackState (Return (VAbs t e\<^sub>1)) (SApp e\<^sub>2 # s) h \<leadsto>\<^sub>s StackState (Eval e\<^sub>1) s (extend\<^sub>h h e\<^sub>2)"
| ret_proj [simp]: "lookup l xs = Some x \<Longrightarrow> 
    StackState (Return (VRec xs)) (SProj l # s) h \<leadsto>\<^sub>s StackState (Eval (Var x)) s h" 
| ret_case [simp]: "lookup l cs = Some e \<Longrightarrow> 
    StackState (Return (VInj l ts x)) (SCase t cs # s) h \<leadsto>\<^sub>s 
      StackState (Eval e) s (extend\<^sub>h h (Var x))"
| ret_unfold [simp]: 
    "StackState (Return (VFold t e)) (SUnfold t # s) h \<leadsto>\<^sub>s StackState (Eval (Var e)) s h" 
| ret_tyapp [simp]: 
    "StackState (Return (VTyAbs k e)) (STyApp t # s) h \<leadsto>\<^sub>s StackState (Eval (subst\<^sub>t\<^sub>e 0 t e)) s h" 

fun is_final :: "stack_state \<Rightarrow> bool" where
  "is_final (StackState (Return v) [] h) = True"
| "is_final (StackState (Return v) (f # s) h) = False"
| "is_final (StackState (Eval e) s h) = False"

lemma vcanonical_arrow [simp]: "\<Delta>,\<Gamma> \<turnstile>\<^sub>v v : Arrow t\<^sub>1 t\<^sub>2 \<Longrightarrow> \<exists>e. v = VAbs t\<^sub>1 e"
  by (induction \<Gamma> v "Arrow t\<^sub>1 t\<^sub>2" rule: typecheck_value_typecheck_vars.inducts(1)) simp_all

lemma vcanonical_record [simp]: "\<Delta>,\<Gamma> \<turnstile>\<^sub>v v : Record ts \<Longrightarrow> \<exists>vs. v = VRec vs \<and> \<Delta>,\<Gamma> \<turnstile>\<^sub>v\<^sub>s vs : ts"
  by (induction \<Gamma> v "Record ts" rule: typecheck_value_typecheck_vars.inducts(1)) simp_all

lemma vcanonical_variant [simp]: "\<Delta>,\<Gamma> \<turnstile>\<^sub>v v : Variant ts \<Longrightarrow> \<exists>l x. v = VInj l ts x \<and> l < length ts"
  by (induction \<Gamma> v "Variant ts" rule: typecheck_value_typecheck_vars.inducts(1)) auto

lemma vcanonical_inductive [simp]: "\<Delta>,\<Gamma> \<turnstile>\<^sub>v v : Inductive k t \<Longrightarrow> \<exists>x. v = VFold t x"
  by (induction \<Gamma> v "Inductive k t" rule: typecheck_value_typecheck_vars.inducts(1)) auto

lemma vcanonical_forall [simp]: "\<Delta>,\<Gamma> \<turnstile>\<^sub>v v : Forall k t \<Longrightarrow> \<exists>e. v = VTyAbs k e"
  by (induction \<Gamma> v "Forall k t" rule: typecheck_value_typecheck_vars.inducts(1)) auto

lemma lookup_in_tc [simp]: "\<Delta>,\<Gamma> \<turnstile>\<^sub>v\<^sub>s xs : ts \<Longrightarrow> lookup l ts = Some t \<Longrightarrow> \<exists>x. lookup l xs = Some x"
  by (induction l xs arbitrary: ts rule: lookup.induct) auto

lemma "\<Delta>,\<Gamma> \<turnstile> e : t \<Longrightarrow> True"
  and "\<Delta>,\<Gamma> \<turnstile>\<^sub>f fs : ts \<Longrightarrow> True"
  and lookup_in_cs [simp]: "\<Delta>,\<Gamma> \<turnstile>\<^sub>c cs : ts \<rightarrow> t \<Longrightarrow> l < length ts \<Longrightarrow> \<exists>e. lookup l cs = Some e"
  proof (induction \<Delta> \<Gamma> e t and \<Delta> \<Gamma> fs ts and \<Delta> \<Gamma> cs ts t arbitrary: and and l 
         rule: typecheck_typecheck_fs_typecheck_cs.inducts)
  case tcc_cons
    thus ?case by (induction l) simp_all
  qed simp_all

theorem progress: "\<Sigma> hastype t \<Longrightarrow> is_final \<Sigma> \<or> (\<exists>\<Sigma>'. \<Sigma> \<leadsto>\<^sub>s \<Sigma>')"
  proof (induction \<Sigma> t rule: typecheck_stack_state.induct)
  case (tc_eval_state \<Gamma> s t t' e h)
    thus ?case
      proof (induction e)
      case Var
        thus ?case by (metis ev_var)
      next case Abs
        thus ?case by (metis ev_abs)
      next case App
        thus ?case by (metis ev_app)
      next case Let
        thus ?case by (metis ev_let)
      next case Rec
        thus ?case by (metis split_fields ev_rec1 ev_rec2)
      next case Proj
        thus ?case by (metis ev_proj)
      next case (Inj l ts e) 
        thus ?case by (cases e) (meson ev_inj1 ev_inj2 is_var.simps)+
      next case Case
        thus ?case by (metis ev_case)
      next case (Fold tt e)
        thus ?case by (cases e) (meson ev_fold1 ev_fold2 is_var.simps)+
      next case Unfold
        thus ?case by (metis ev_unfold)
      next case TyAbs
        thus ?case by (metis ev_tyabs)
      next case TyApp
        thus ?case by (metis ev_tyapp)
      next case TyLet
        thus ?case by (metis ev_tylet)
      qed
  next case (tc_return_state \<Gamma> s t t' v h)
    thus ?case
      proof (induction \<Gamma> s t t' rule: typecheck_stack.induct)
      case (tcs_cons \<Gamma> f \<Gamma>' t t' s t'')
        thus ?case
          proof (induction \<Gamma> f \<Gamma>' t t' rule: typecheck_frame.induct)
          case tc_sref
            thus ?case by (metis ret_ref)
          next case tc_sapp
            thus ?case by (metis vcanonical_arrow ret_app)
          next case tc_sproj
            thus ?case by (metis vcanonical_record ret_proj lookup_in_tc)
          next case tc_scase
            thus ?case by (metis vcanonical_variant ret_case lookup_in_cs)
          next case tc_sunfold
            thus ?case by (metis vcanonical_inductive ret_unfold)
          next case tc_styapp
            thus ?case by (metis vcanonical_forall ret_tyapp)
          qed
      qed simp_all
  qed

lemma [simp]: "h \<turnstile>\<^sub>h \<Gamma> \<Longrightarrow> lookup x \<Gamma> = Some t \<Longrightarrow> [],\<Gamma> \<turnstile> lookup\<^sub>h x h : t"
  by (induction h \<Gamma> rule: typecheck_heap.induct) simp_all

theorem preservation: "\<Sigma> \<leadsto>\<^sub>s \<Sigma>' \<Longrightarrow> \<Sigma> hastype t \<Longrightarrow> \<Sigma>' hastype t"
  proof (induction \<Sigma> \<Sigma>' rule: evaluate.induct)
  case (ev_var x s h)
    then obtain \<Gamma> tt where "(\<Gamma> \<turnstile>\<^sub>s\<^sub>s s : tt \<rightarrow> t) \<and> (lookup x \<Gamma> = Some tt) \<and> (h \<turnstile>\<^sub>h \<Gamma>)" by blast
    moreover hence "\<Gamma> \<turnstile>\<^sub>s\<^sub>s SRef x # s : tt \<rightarrow> t" by (metis tc_sref tcs_cons)
    ultimately show ?case by simp
  next case (ev_app e\<^sub>1 e\<^sub>2 s h)
    then obtain \<Gamma> t\<^sub>1 t\<^sub>2 where "(\<Gamma> \<turnstile>\<^sub>s\<^sub>s s : t\<^sub>2 \<rightarrow> t) \<and> ([],\<Gamma> \<turnstile> e\<^sub>1 : Arrow t\<^sub>1 t\<^sub>2) \<and> 
      ([],\<Gamma> \<turnstile> e\<^sub>2 : t\<^sub>1) \<and> (h \<turnstile>\<^sub>h \<Gamma>)" by blast
    moreover hence "\<Gamma> \<turnstile>\<^sub>s\<^sub>s SApp e\<^sub>2 # s : Arrow t\<^sub>1 t\<^sub>2 \<rightarrow> t" by (metis tc_sapp tcs_cons)
    ultimately show ?case by simp
  next case (ev_let e\<^sub>1 e\<^sub>2 s h)
    then obtain \<Gamma> t\<^sub>1 t\<^sub>2 where T: "(\<Gamma> \<turnstile>\<^sub>s\<^sub>s s : t\<^sub>2 \<rightarrow> t) \<and> ([],\<Gamma> \<turnstile> e\<^sub>1 : t\<^sub>1) \<and> 
      ([],insert_at 0 t\<^sub>1 \<Gamma> \<turnstile> e\<^sub>2 : t\<^sub>2) \<and> (h \<turnstile>\<^sub>h \<Gamma>)" by blast
    hence L: "length\<^sub>h h = length \<Gamma>" by blast
    from T have X: "insert_at (length \<Gamma>) t\<^sub>1 \<Gamma> \<turnstile>\<^sub>s\<^sub>s s : t\<^sub>2 \<rightarrow> t" by simp
    from T have "[],insert_at (length (insert_at 0 t\<^sub>1 \<Gamma>)) t\<^sub>1 (insert_at 0 t\<^sub>1 \<Gamma>) \<turnstile> e\<^sub>2 : t\<^sub>2" 
      using tc_weaken by blast
    with L have Y: "[],insert_at 0 t\<^sub>1 (insert_at (length\<^sub>h h) t\<^sub>1 \<Gamma>) \<turnstile> e\<^sub>2 : t\<^sub>2" by simp
    from L have "lookup (length\<^sub>h h) (insert_at (length\<^sub>h h) t\<^sub>1 \<Gamma>) = Some t\<^sub>1" by simp
    with T X Y show ?case by simp
  next case ev_rec1 
    thus ?case by metis
  next case ev_rec2  
    thus ?case by metis
  next case ev_proj 
    thus ?case by metis
  next case ev_inj2 
    thus ?case by metis
  next case ev_case 
    thus ?case by metis
  next case ev_fold2 
    thus ?case by metis
  next case ev_unfold 
    thus ?case by metis
  next case ev_tyapp 
    thus ?case by metis
  next case ret_ref 
    thus ?case by metis
  next case ret_app 
    thus ?case by metis
  next case ret_proj 
    thus ?case by metis
  next case ret_case 
    thus ?case by metis
  next case ret_tyapp 
    thus ?case by metis
  qed fastforce+

end