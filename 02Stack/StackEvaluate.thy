theory StackEvaluate
imports StackTypecheck
begin

inductive evaluate :: "stack_state \<Rightarrow> stack_state \<Rightarrow> bool" (infix "\<leadsto>\<^sub>s" 60) where
  ev_var [simp]: "StackState (Eval (Var x)) s h \<leadsto>\<^sub>s StackState (Eval (lookup\<^sub>h h x)) (SRef x # s) h"
| ev_abs [simp]: "StackState (Eval (Abs t e)) s h \<leadsto>\<^sub>s StackState (Return (VAbs t e)) s h"
| ev_app [simp]: "StackState (Eval (App e\<^sub>1 e\<^sub>2)) s h \<leadsto>\<^sub>s StackState (Eval e\<^sub>1) (SApp e\<^sub>2 # s) h" 
| ev_let [simp]: "StackState (Eval (Let e\<^sub>1 e\<^sub>2)) s h \<leadsto>\<^sub>s 
    StackState (Eval (subst\<^sub>x\<^sub>e 0 (length\<^sub>h h) e\<^sub>2)) s (extend\<^sub>h h e\<^sub>1)"
| ev_rec [simp]: "StackState (Eval (Rec vs)) s h \<leadsto>\<^sub>s StackState (Return (VRec vs)) s h" 
| ev_proj [simp]: "StackState (Eval (Proj e l)) s h \<leadsto>\<^sub>s StackState (Eval e) (SProj l # s) h"
| ev_inj [simp]: "StackState (Eval (Inj l ts x)) s h \<leadsto>\<^sub>s StackState (Return (VInj l ts x)) s h"
| ev_case [simp]: "StackState (Eval (Case e t cs)) s h \<leadsto>\<^sub>s StackState (Eval e) (SCase t cs # s) h"
| ev_fold [simp]: "StackState (Eval (Fold t x)) s h \<leadsto>\<^sub>s StackState (Return (VFold t x)) s h" 
| ev_unfold [simp]: "StackState (Eval (Unfold t e)) s h \<leadsto>\<^sub>s StackState (Eval e) (SUnfold t # s) h"  
| ev_tyabs [simp]: "StackState (Eval (TyAbs k e)) s h \<leadsto>\<^sub>s StackState (Return (VTyAbs k e)) s h" 
| ev_tyapp [simp]: "StackState (Eval (TyApp e t)) s h \<leadsto>\<^sub>s StackState (Eval e) (STyApp t # s) h" 
| ev_tylet [simp]: "StackState (Eval (TyLet t e)) s h \<leadsto>\<^sub>s StackState (Eval (subst\<^sub>t\<^sub>e 0 t e)) s h" 
| ret_ref [simp]: 
    "StackState (Return v) (SRef x # s) h \<leadsto>\<^sub>s StackState (Return v) s (update\<^sub>h h x (devalue v))"
| ret_app [simp]: "StackState (Return (VAbs t e\<^sub>1)) (SApp e\<^sub>2 # s) h \<leadsto>\<^sub>s 
    StackState (Eval (subst\<^sub>x\<^sub>e 0 (length\<^sub>h h) e\<^sub>1)) s (extend\<^sub>h h e\<^sub>2)"
| ret_proj [simp]: "lookup xs l = Some x \<Longrightarrow> 
    StackState (Return (VRec xs)) (SProj l # s) h \<leadsto>\<^sub>s StackState (Eval (Var x)) s h" 
| ret_case [simp]: "lookup cs l = Some e \<Longrightarrow> 
    StackState (Return (VInj l ts x)) (SCase t cs # s) h \<leadsto>\<^sub>s StackState (Eval (subst\<^sub>x\<^sub>e 0 x e)) s h"
| ret_unfold [simp]: 
    "StackState (Return (VFold t x)) (SUnfold t # s) h \<leadsto>\<^sub>s StackState (Eval (Var x)) s h" 
| ret_tyapp [simp]: 
    "StackState (Return (VTyAbs k e)) (STyApp t # s) h \<leadsto>\<^sub>s StackState (Eval (subst\<^sub>t\<^sub>e 0 t e)) s h" 

fun is_final :: "stack_state \<Rightarrow> bool" where
  "is_final (StackState (Return v) [] h) = True"
| "is_final (StackState (Return v) (f # s) h) = False"
| "is_final (StackState (Eval e) s h) = False"

lemma vcanonical_arrow [simp]: "\<Delta>,\<Gamma> \<turnstile>\<^sub>v v : Arrow t\<^sub>1 t\<^sub>2 \<Longrightarrow> \<exists>e. v = VAbs t\<^sub>1 e"
  by (induction \<Gamma> v "Arrow t\<^sub>1 t\<^sub>2" rule: typecheck_value.induct) simp_all

lemma vcanonical_record [simp]: "\<Delta>,\<Gamma> \<turnstile>\<^sub>v v : Record ts \<Longrightarrow> \<exists>vs. v = VRec vs \<and> \<Delta>,\<Gamma> \<turnstile>\<^sub>x\<^sub>s vs : ts"
  by (induction \<Gamma> v "Record ts" rule: typecheck_value.induct) simp_all

lemma vcanonical_variant [simp]: "\<Delta>,\<Gamma> \<turnstile>\<^sub>v v : Variant ts \<Longrightarrow> \<exists>l x. v = VInj l ts x \<and> l < length ts"
  by (induction \<Gamma> v "Variant ts" rule: typecheck_value.induct) auto

lemma vcanonical_inductive [simp]: "\<Delta>,\<Gamma> \<turnstile>\<^sub>v v : Inductive k t \<Longrightarrow> \<exists>x. v = VFold t x"
  by (induction \<Gamma> v "Inductive k t" rule: typecheck_value.induct) auto

lemma vcanonical_forall [simp]: "\<Delta>,\<Gamma> \<turnstile>\<^sub>v v : Forall k t \<Longrightarrow> \<exists>e. v = VTyAbs k e"
  by (induction \<Gamma> v "Forall k t" rule: typecheck_value.induct) auto

lemma lookup_in_tc [simp]: "\<Delta>,\<Gamma> \<turnstile>\<^sub>x\<^sub>s xs : ts \<Longrightarrow> lookup ts l = Some t \<Longrightarrow> \<exists>x. lookup xs l = Some x"
  by (induction xs l arbitrary: ts rule: lookup.induct) auto

lemma lookup_in_env [simp]: "\<Delta>,\<Gamma> \<turnstile>\<^sub>x\<^sub>s xs : ts \<Longrightarrow> lookup ts l = Some t \<Longrightarrow> lookup xs l = Some x \<Longrightarrow> 
    lookup \<Gamma> x = Some t"
  by (induction xs l arbitrary: ts rule: lookup.induct) auto

lemma "\<Delta>,\<Gamma> \<turnstile> e : t \<Longrightarrow> True"
  and lookup_in_cs [simp]: "\<Delta>,\<Gamma> \<turnstile>\<^sub>c cs : ts \<rightarrow> t \<Longrightarrow> l < length ts \<Longrightarrow> \<exists>e. lookup cs l = Some e"
  proof (induction \<Delta> \<Gamma> e t and \<Delta> \<Gamma> cs ts t arbitrary: and l rule: typecheck_typecheck_cs.inducts)
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
        thus ?case by (metis ev_rec)
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
  next case (tc_return_state \<Gamma> s t t' v h)
    thus ?case
      proof (induction \<Gamma> s t t' rule: typecheck_stack.induct)
      case (tcs_cons \<Gamma> f t t' s t'')
        thus ?case
          proof (induction \<Gamma> f t t' rule: typecheck_frame.induct)
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

theorem preservation: "\<Sigma> \<leadsto>\<^sub>s \<Sigma>' \<Longrightarrow> \<Sigma> hastype t \<Longrightarrow> \<Sigma>' hastype t"
  proof (induction \<Sigma> \<Sigma>' rule: evaluate.induct)
  case (ev_var x s h)
    then obtain \<Gamma> tt where "(\<Gamma> \<turnstile>\<^sub>s\<^sub>s s : tt \<rightarrow> t) \<and> (lookup \<Gamma> x = Some tt) \<and> (h \<turnstile>\<^sub>h \<Gamma>)" by blast
    moreover hence "\<Gamma> \<turnstile>\<^sub>s\<^sub>s SRef x # s : tt \<rightarrow> t" by (metis tc_sref tcs_cons)
    ultimately show ?case by simp
  next case (ev_app e\<^sub>1 e\<^sub>2 s h)
    then obtain \<Gamma> t\<^sub>1 t\<^sub>2 where "(\<Gamma> \<turnstile>\<^sub>s\<^sub>s s : t\<^sub>2 \<rightarrow> t) \<and> ([],\<Gamma> \<turnstile> e\<^sub>1 : Arrow t\<^sub>1 t\<^sub>2) \<and> 
      ([],\<Gamma> \<turnstile> e\<^sub>2 : t\<^sub>1) \<and> (h \<turnstile>\<^sub>h \<Gamma>)" by blast
    thus ?case by (metis tc_sapp tcs_cons tc_eval_state)
  next case (ev_let e\<^sub>1 e\<^sub>2 s h)
    then obtain \<Gamma> t\<^sub>1 t\<^sub>2 where T: "(\<Gamma> \<turnstile>\<^sub>s\<^sub>s s : t\<^sub>2 \<rightarrow> t) \<and> ([],\<Gamma> \<turnstile> e\<^sub>1 : t\<^sub>1) \<and> 
      ([],insert_at 0 t\<^sub>1 \<Gamma> \<turnstile> e\<^sub>2 : t\<^sub>2) \<and> (h \<turnstile>\<^sub>h \<Gamma>)" by blast
    from T have "[],insert_at (length (insert_at 0 t\<^sub>1 \<Gamma>)) t\<^sub>1 (insert_at 0 t\<^sub>1 \<Gamma>) \<turnstile> e\<^sub>2 : t\<^sub>2" 
      by (metis tc_weaken)
    hence "[],insert_at 0 t\<^sub>1 (insert_at (length \<Gamma>) t\<^sub>1 \<Gamma>) \<turnstile> e\<^sub>2 : t\<^sub>2" by simp
    moreover from T have L: "length\<^sub>h h = length \<Gamma>" by fastforce
    ultimately have X: "[],insert_at (length\<^sub>h h) t\<^sub>1 \<Gamma> \<turnstile> subst\<^sub>x\<^sub>e 0 (length\<^sub>h h) e\<^sub>2 : t\<^sub>2" by simp
    from T L have "insert_at (length\<^sub>h h) t\<^sub>1 \<Gamma> \<turnstile>\<^sub>s\<^sub>s s : t\<^sub>2 \<rightarrow> t" by fastforce 
    with T X show ?case by simp
  next case (ev_proj e l s h)
    then obtain \<Gamma> tt ts where "(\<Gamma> \<turnstile>\<^sub>s\<^sub>s s : tt \<rightarrow> t) \<and> ([],\<Gamma> \<turnstile> e : Record ts) \<and> 
      lookup ts l = Some tt \<and> (h \<turnstile>\<^sub>h \<Gamma>)" by blast
    thus ?case by (metis tc_sproj tcs_cons tc_eval_state)
  next case (ev_case e t' cs s h)
    then obtain \<Gamma> ts where "(\<Gamma> \<turnstile>\<^sub>s\<^sub>s s : t' \<rightarrow> t) \<and> ([],\<Gamma> \<turnstile> e : Variant ts) \<and> ([] \<turnstile>\<^sub>k t' : Star) \<and>
      ([],\<Gamma> \<turnstile>\<^sub>c cs : ts \<rightarrow> t') \<and> (h \<turnstile>\<^sub>h \<Gamma>)" by blast
    thus ?case by (metis tc_scase tcs_cons tc_eval_state)
  next case (ev_unfold tt e s h)
    then obtain \<Gamma> k where T: "(\<Gamma> \<turnstile>\<^sub>s\<^sub>s s : subst\<^sub>t\<^sub>t 0 (Inductive k tt) tt \<rightarrow> t) \<and> 
      ([],\<Gamma> \<turnstile> e : Inductive k tt) \<and> (insert_at 0 k [] \<turnstile>\<^sub>k tt : Star) \<and> (h \<turnstile>\<^sub>h \<Gamma>)" by blast
    moreover hence "[k] \<turnstile>\<^sub>k tt : Star" by simp
    ultimately show ?case by (metis tc_eval_state tcs_cons tc_sunfold)
  next case (ev_tyapp e tt s h)
    then obtain \<Gamma> k t' where "(\<Gamma> \<turnstile>\<^sub>s\<^sub>s s : subst\<^sub>t\<^sub>t 0 tt t' \<rightarrow> t) \<and> ([],\<Gamma> \<turnstile> e : Forall k t') \<and> 
      ([] \<turnstile>\<^sub>k tt : k) \<and> (h \<turnstile>\<^sub>h \<Gamma>)" by blast
    thus ?case by (metis tc_eval_state tcs_cons tc_styapp)
  next case (ret_ref v x s h)
    then obtain \<Gamma> t' where "lookup \<Gamma> x = Some t' \<and> (\<Gamma> \<turnstile>\<^sub>s\<^sub>s s : t' \<rightarrow> t) \<and> ([],\<Gamma> \<turnstile>\<^sub>v v : t') \<and> 
      (h \<turnstile>\<^sub>h \<Gamma>)" by blast
    moreover hence "update\<^sub>h h x (devalue v) \<turnstile>\<^sub>h \<Gamma>" by simp
    ultimately show ?case by (metis tc_return_state)
  next case (ret_app t\<^sub>1 e\<^sub>1 e\<^sub>2 s h)
    then obtain \<Gamma> t\<^sub>2 where T: "([],\<Gamma> \<turnstile> e\<^sub>2 : t\<^sub>1) \<and> (\<Gamma> \<turnstile>\<^sub>s\<^sub>s s : t\<^sub>2 \<rightarrow> t) \<and> 
      ([],insert_at 0 t\<^sub>1 \<Gamma> \<turnstile> e\<^sub>1 : t\<^sub>2) \<and> ([] \<turnstile>\<^sub>k t\<^sub>1 : Star) \<and> (h \<turnstile>\<^sub>h \<Gamma>)" by blast
    from T have L: "length\<^sub>h h = length \<Gamma>" by fastforce
    moreover from T have "[],insert_at (length (insert_at 0 t\<^sub>1 \<Gamma>)) t\<^sub>1 (insert_at 0 t\<^sub>1 \<Gamma>) \<turnstile> e\<^sub>1 : t\<^sub>2" 
      by (metis tc_weaken)
    ultimately have X: "[],insert_at (length\<^sub>h h) t\<^sub>1 \<Gamma> \<turnstile> subst\<^sub>x\<^sub>e 0 (length\<^sub>h h) e\<^sub>1 : t\<^sub>2" by simp
    from T L have "insert_at (length\<^sub>h h) t\<^sub>1 \<Gamma> \<turnstile>\<^sub>s\<^sub>s s : t\<^sub>2 \<rightarrow> t" by fastforce
    with T X show ?case by fastforce
  next case (ret_proj xs l x s h)
    moreover then obtain \<Gamma> ts t' where "(lookup ts l = Some t') \<and> (\<Gamma> \<turnstile>\<^sub>s\<^sub>s s : t' \<rightarrow> t) \<and> 
      ([],\<Gamma> \<turnstile>\<^sub>x\<^sub>s xs : ts) \<and> (h \<turnstile>\<^sub>h \<Gamma>)" by blast
    ultimately show ?case by (metis tc_eval_state tc_var lookup_in_env)
  next case (ret_case cs l e ts x tt s h) 
    then obtain \<Gamma> t' where T: "([],\<Gamma> \<turnstile>\<^sub>c cs : ts \<rightarrow> tt) \<and> (\<Gamma> \<turnstile>\<^sub>s\<^sub>s s : tt \<rightarrow> t) \<and> 
      lookup \<Gamma> x = Some t' \<and> lookup ts l= Some t' \<and> (\<forall>tt \<in> set ts. [] \<turnstile>\<^sub>k tt : Star) \<and> (h \<turnstile>\<^sub>h \<Gamma>)" 
        by blast
    moreover with ret_case have "[],insert_at 0 t' \<Gamma> \<turnstile> e : tt" by auto
    ultimately have "[],\<Gamma> \<turnstile> subst\<^sub>x\<^sub>e 0 x e : tt" by simp
    with T show ?case by (metis tc_eval_state)
  next case (ret_tyapp k e tt s h)
    then obtain \<Gamma> t' where T: "([] \<turnstile>\<^sub>k tt : k) \<and> (\<Gamma> \<turnstile>\<^sub>s\<^sub>s s : subst\<^sub>t\<^sub>t 0 tt t' \<rightarrow> t) \<and> 
      (insert_at 0 k [],map (incr\<^sub>t\<^sub>t 0) \<Gamma> \<turnstile> e : t') \<and> (h \<turnstile>\<^sub>h \<Gamma>)" by blast
    hence "[],map (subst\<^sub>t\<^sub>t 0 tt) (map (incr\<^sub>t\<^sub>t 0) \<Gamma>) \<turnstile> subst\<^sub>t\<^sub>e 0 tt e : subst\<^sub>t\<^sub>t 0 tt t'" 
      using tc_subst\<^sub>t\<^sub>e by blast
    hence "[],\<Gamma> \<turnstile> subst\<^sub>t\<^sub>e 0 tt e : subst\<^sub>t\<^sub>t 0 tt t'" by simp
    with T show ?case by (metis tc_eval_state)
  qed fastforce+

end