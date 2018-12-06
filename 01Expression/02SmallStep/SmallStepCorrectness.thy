theory SmallStepCorrectness
imports SmallStepEvaluate "../01BigStep/BigStepEvaluate" "../../Utilities/Iterate"
begin

lemma [simp]: "iter (op \<leadsto>) e\<^sub>1 e\<^sub>1' \<Longrightarrow> iter (op \<leadsto>) (App e\<^sub>1 e\<^sub>2) (App e\<^sub>1' e\<^sub>2)"
  proof (induction e\<^sub>1 e\<^sub>1' rule: iter.induct)
  case iter_step
    thus ?case by (metis ev_app1 iter.iter_step)
  qed simp_all

theorem completeness: "e \<Down> v \<Longrightarrow> [],[] \<turnstile> e : t \<Longrightarrow> iter (op \<leadsto>) e v"
  proof (induction e v rule: reduce.induct)
  case (red_app e\<^sub>1 t e\<^sub>1' e\<^sub>2 v)
    hence "iter (op \<leadsto>) (App (Abs t e\<^sub>1') e\<^sub>2) v" by argl (metis ev_app2 iter.iter_step)
    moreover from red_app have "iter (op \<leadsto>) (App e\<^sub>1 e\<^sub>2) (App (Abs t e\<^sub>1') e\<^sub>2)" by simp
    ultimately show ?case by auto
  next case (red_app_let e\<^sub>1 e\<^sub>1\<^sub>1 e\<^sub>1\<^sub>2 e\<^sub>2 v)
    hence "is_value e\<^sub>1\<^sub>2" by simp
    with red_app_let have "iter (op \<leadsto>) (App (Let e\<^sub>1\<^sub>1 e\<^sub>1\<^sub>2) e\<^sub>2) v" by argl (metis ev_app_let iter.iter_step)
    moreover from red_app_let have "iter (op \<leadsto>) (App e\<^sub>1 e\<^sub>2) (App (Let e\<^sub>1\<^sub>1 e\<^sub>1\<^sub>2) e\<^sub>2)" by simp
    ultimately show ?case by auto
  next case red_let_0 
    thus ?case by simp
  next case red_let_S 
    thus ?case by simp
  next case red_proj 
    thus ?case by simp
  next case red_proj_let 
    thus ?case by simp
  next case red_case 
    thus ?case by simp
  next case red_case_let 
    thus ?case by simp
  next case red_unfold 
    thus ?case by simp
  next case red_unfold_let 
    thus ?case by simp
  next case red_tyapp 
    thus ?case by simp
  next case red_tyapp_let 
    thus ?case by simp
  next case red_tylet 
    thus ?case by simp
  qed simp_all

theorem soundness: "iter (op \<leadsto>) e v \<Longrightarrow> is_value v \<Longrightarrow> e \<Down> v"
  by simp

end