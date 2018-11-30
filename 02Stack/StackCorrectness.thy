theory StackCorrectness
imports StackConversion "../01Expression/Evaluate" "../Utilities/Iterate"
begin

lemma complete': "e \<leadsto> e' \<Longrightarrow> unstack_state rs \<Sigma> = e \<Longrightarrow> \<exists>\<Sigma>'. \<Sigma> \<leadsto>\<^sub>s \<Sigma>' \<and> unstack_state rs \<Sigma>' = e'"
  proof (induction e e' rule: evaluate.induct) 
  case (ev_app1 e\<^sub>1 e\<^sub>1' e\<^sub>2)
    thus ?case by simp 
  next case ev_app2 
    thus ?case by simp 
  next case ev_app_let
    thus ?case by simp 
  next case ev_let1
    thus ?case by simp 
  next case ev_let2
    thus ?case by simp 
  next case ev_let3
    thus ?case by simp 
  next case ev_proj1
    thus ?case by simp 
  next case ev_proj2 
    thus ?case by simp 
  next case ev_proj_let
    thus ?case by simp 
  next case ev_case1 
    thus ?case by simp 
  next case ev_case2
    thus ?case by simp 
  next case ev_case_let
    thus ?case by simp 
  next case ev_unfold1
    thus ?case by simp 
  next case ev_unfold2
    thus ?case by simp 
  next case ev_unfold_let
    thus ?case by simp 
  next case ev_tyapp1
    thus ?case by simp 
  next case ev_tyapp2
    thus ?case by simp 
  next case ev_tyapp_let
    thus ?case by simp 
  next case ev_tylet
    thus ?case by simp 
  qed 

lemma complete: "iter (op \<leadsto>) e e' \<Longrightarrow> unstack_state rs \<Sigma> e \<Longrightarrow>
    \<exists>\<Sigma>'. iter (op \<leadsto>\<^sub>s) \<Sigma> \<Sigma>' \<and> unstack_state \<Sigma>' e'"
  proof (induction e e' arbitrary: \<Sigma> rule: iter.induct)
  case iter_refl
    thus ?case by (metis iter.iter_refl)
  next case (iter_step e e' e'')
    then obtain \<Sigma>' where "\<Sigma> \<leadsto>\<^sub>s \<Sigma>' \<and> unstack_state \<Sigma>' e'" by (metis complete')
    moreover with iter_step obtain \<Sigma>'' where "iter (op \<leadsto>\<^sub>s) \<Sigma>' \<Sigma>'' \<and> unstack_state \<Sigma>'' e''" 
      by fastforce
    ultimately have "iter (op \<leadsto>\<^sub>s) \<Sigma> \<Sigma>'' \<and> unstack_state \<Sigma>'' e''" by fastforce
    thus ?case by fastforce
  qed

lemma sound': "\<Sigma> \<leadsto>\<^sub>s \<Sigma>' \<Longrightarrow> unstack_state \<Sigma> e \<Longrightarrow> \<exists>e'. iter (op \<leadsto>) e e' \<and> unstack_state \<Sigma>' e'"
  proof (induction \<Sigma> \<Sigma>' arbitrary: e rule: EvaluateStack.evaluate.induct)
  case (ev_var x s h)
    hence "unstack_state (StackState (Eval (Var x)) s h) e" by simp


have "unstack {} s (Var x) h {..< length\<^sub>h h} [] e \<Longrightarrow> 
    unstack_state (StackState (Eval (Var x)) s h) e" by simp

    have "\<exists>e'. iter op \<leadsto> e e' \<and> unstack_state (StackState (Eval (lookup\<^sub>h x h)) (SRef x # s) h) e'" by simp
    thus ?case by simp
  next case ev_abs 
    thus ?case by simp
  next case ev_app 
    thus ?case by simp
  next case ev_let 
    thus ?case by simp
  next case ev_rec 
    thus ?case by simp
  next case ev_proj 
    thus ?case by simp
  next case ev_inj 
    thus ?case by simp
  next case ev_case 
    thus ?case by simp
  next case ev_fold 
    thus ?case by simp
  next case ev_unfold 
    thus ?case by simp
  next case ev_tyabs 
    thus ?case by simp
  next case ev_tyapp 
    thus ?case by simp
  next case ev_tylet 
    thus ?case by simp
  next case ret_ref 
    thus ?case by simp
  next case ret_app 
    thus ?case by simp
  next case ret_proj 
    thus ?case by simp
  next case ret_case 
    thus ?case by simp
  next case ret_unfold 
    thus ?case by simp
  next case ret_tyapp 
    thus ?case by simp
  qed 

lemma sound: "iter (op \<leadsto>\<^sub>s) \<Sigma> \<Sigma>' \<Longrightarrow> \<exists>rs'. iter (op \<leadsto>) (unstack_state rs \<Sigma>) (unstack_state rs' \<Sigma>')"
  by (induction \<Sigma> \<Sigma>' rule: iter.induct) simp_all

end