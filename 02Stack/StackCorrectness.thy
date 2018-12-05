theory StackCorrectness
imports StackConversion "../01Expression/02SmallStep/SmallStepEvaluate" "../Utilities/Iterate"
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

lemma complete: "iter (op \<leadsto>) e e' \<Longrightarrow> unstack_state rs \<Sigma> = e \<Longrightarrow>
    \<exists>\<Sigma>'. iter (op \<leadsto>\<^sub>s) \<Sigma> \<Sigma>' \<and> unstack_state rs \<Sigma>' = e'"
  proof (induction e e' arbitrary: \<Sigma> rule: iter.induct)
  case iter_refl
    thus ?case by (metis iter.iter_refl)
  next case (iter_step e e' e'')
    then obtain \<Sigma>' where "\<Sigma> \<leadsto>\<^sub>s \<Sigma>' \<and> unstack_state rs \<Sigma>' = e'" by (metis complete')
    moreover with iter_step obtain \<Sigma>'' where "iter (op \<leadsto>\<^sub>s) \<Sigma>' \<Sigma>'' \<and> unstack_state rs \<Sigma>'' = e''" 
      by fastforce
    ultimately have "iter (op \<leadsto>\<^sub>s) \<Sigma> \<Sigma>'' \<and> unstack_state rs \<Sigma>'' = e''" by fastforce
    thus ?case by fastforce
  qed

lemma sound': "\<Sigma> \<leadsto>\<^sub>s \<Sigma>' \<Longrightarrow> unstack_state rs \<Sigma> = e \<Longrightarrow> 
    \<exists>rs' e'. unstack_state rs' \<Sigma>' = e' \<and> (e \<leadsto> e' \<or> e = e')"
  proof (induction \<Sigma> \<Sigma>' arbitrary: e rule: EvaluateStack.evaluate.induct)
  case (ev_var x s h)
    hence "unstack rs s (Var x) h = e" by simp


    have "e \<leadsto> unstack rs' (SRef x # s) (lookup\<^sub>h h x) h \<or> 
      e = unstack rs' (SRef x # s) (lookup\<^sub>h h x) h" by simp
    thus ?case by fastforce
  next case (ev_abs t e\<^sub>1 s h)
    hence "unstack rs s (Abs t e\<^sub>1) h = e" by simp
    thus ?case by fastforce
  next case (ev_app e\<^sub>1 e\<^sub>2 s h)
    hence "unstack ([] # rs) (SApp e\<^sub>2 # s) e\<^sub>1 h = e" by simp
    thus ?case by fastforce
  next case (ev_let e\<^sub>1 e\<^sub>2 s h)
    hence "unstack rs s (Let e\<^sub>1 e\<^sub>2) h = e" by simp


    have "e \<leadsto> unstack rs' s (subst\<^sub>x\<^sub>e 0 (length\<^sub>h h) e\<^sub>2) (extend\<^sub>h h e\<^sub>1) \<or>
      unstack rs' s (subst\<^sub>x\<^sub>e 0 (length\<^sub>h h) e\<^sub>2) (extend\<^sub>h h e\<^sub>1) = e" by simp
    thus ?case by fastforce
  next case (ev_rec xs s h)
    hence "unstack rs s (Rec xs) h = e" by simp
    thus ?case by fastforce
  next case (ev_proj e\<^sub>1 l s h)
    hence "unstack ([] # rs) (SProj l # s) e\<^sub>1 h = e" by simp
    thus ?case by fastforce
  next case (ev_inj l ts x s h)
    hence "unstack rs s (Inj l ts x) h = e" by simp
    thus ?case by fastforce
  next case (ev_case e\<^sub>1 t cs s h)
    hence "unstack ([] # rs) (SCase t cs # s) e\<^sub>1 h = e" by simp
    thus ?case by fastforce
  next case (ev_fold t x s h) 
    hence "unstack rs s (Fold t x) h = e" by simp
    thus ?case by fastforce
  next case (ev_unfold t e\<^sub>1 s h) 
    hence "unstack ([] # rs) (SUnfold t # s) e\<^sub>1 h = e" by simp
    thus ?case by fastforce
  next case (ev_tyabs k e\<^sub>1 s h)
    hence "unstack rs s (TyAbs k e\<^sub>1) h = e" by simp
    thus ?case by fastforce
  next case (ev_tyapp e\<^sub>1 t s h)
    hence "unstack ([] # rs) (STyApp t # s) e\<^sub>1 h = e" by simp
    thus ?case by fastforce
  next case (ev_tylet t e\<^sub>1 s h)
    hence "unstack rs s (TyLet t e\<^sub>1) h = e" by simp

    have "e \<leadsto> unstack rs' s (subst\<^sub>t\<^sub>e 0 t e\<^sub>1) h \<or> e = unstack rs' s (subst\<^sub>t\<^sub>e 0 t e\<^sub>1) h" by simp
    thus ?case by fastforce
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

lemma sound: "iter (op \<leadsto>\<^sub>s) \<Sigma> \<Sigma>' \<Longrightarrow> unstack_state rs \<Sigma> = e \<Longrightarrow> 
    \<exists>rs'. iter (op \<leadsto>) e (unstack_state rs' \<Sigma>')"
  proof (induction \<Sigma> \<Sigma>' arbitrary: e rs rule: iter.induct)
  case (iter_refl \<Sigma>)
    moreover have "iter (op \<leadsto>) (unstack_state rs \<Sigma>) (unstack_state rs \<Sigma>)" by simp
    ultimately show ?case by fastforce
  next case (iter_step \<Sigma> \<Sigma>' \<Sigma>'')
    then obtain rs' e' where "unstack_state rs' \<Sigma>' = e' \<and> (e \<leadsto> e' \<or> e = e')" by (metis sound')
    moreover with iter_step obtain rs'' where "iter (op \<leadsto>) e' (unstack_state rs'' \<Sigma>'')" by fastforce
    ultimately have "iter (op \<leadsto>) e (unstack_state rs'' \<Sigma>'')" by fastforce
    thus ?case by fastforce
  qed

end