theory Determinism
imports Evaluate
begin

lemma [elim]: "head_var e = Some x \<Longrightarrow> is_value e \<Longrightarrow> False"
  by (induction e arbitrary: x) (auto split: option.splits nat.splits)

lemma [elim]: "e \<leadsto> e' \<Longrightarrow> is_value e \<Longrightarrow> False"
  by (induction e e' rule: evaluate.induct) auto

lemma [elim]: "e \<leadsto> e' \<Longrightarrow> is_var e \<Longrightarrow> False"
  by (induction e e' rule: evaluate.induct) simp_all

lemma [elim]: "e \<leadsto> e' \<Longrightarrow> head_var e = Some x \<Longrightarrow> False"
  by (induction e e' arbitrary: x rule: evaluate.induct) (auto split: option.splits nat.splits)

lemma [elim]: "list_all is_var vs \<Longrightarrow> list_all is_var vs' \<Longrightarrow> \<not> is_var e \<Longrightarrow> \<not> is_var e' \<Longrightarrow>
    vs @ [e] @ nvs = vs' @ [e'] @ nvs' \<Longrightarrow> vs = vs'"
  proof (induction vs arbitrary: vs')
  case Nil
    thus ?case by (induction vs') simp_all
  next case (Cons v vs)
    thus ?case by (induction vs') simp_all
  qed

theorem determinism [elim]: "e \<leadsto> e' \<Longrightarrow> e \<leadsto> e'' \<Longrightarrow> e' = e''"
  proof (induction e e' arbitrary: e'' rule: evaluate.induct)
  case (ev_app1 e\<^sub>1 e\<^sub>1' e\<^sub>2)
    with ev_app1(3) show ?case
      proof (induction "App e\<^sub>1 e\<^sub>2" e'' rule: evaluate.induct)
      case ev_app2
        hence False by auto
        thus ?case by simp
      next case ev_app_let
        hence False by auto
        thus ?case by simp
      qed simp_all
  next case (ev_app2 t e\<^sub>1 e\<^sub>2)
    thus ?case by (induction "App (Abs t e\<^sub>1) e\<^sub>2" e'' rule: evaluate.induct) auto
  next case (ev_app_let e\<^sub>1\<^sub>2 e\<^sub>1\<^sub>1 e\<^sub>2)
    with ev_app_let(2) show ?case
      proof (induction "App (Let e\<^sub>1\<^sub>1 e\<^sub>1\<^sub>2) e\<^sub>2" e'' rule: evaluate.induct)
      case ev_app1
        hence False by auto
        thus ?case by simp
      qed simp_all
  next case (ev_let1 e\<^sub>2 e\<^sub>2' e\<^sub>1)
    with ev_let1(3) show ?case
      proof (induction "Let e\<^sub>1 e\<^sub>2" e'' rule: evaluate.induct) 
      case ev_let2
        hence False by fast
        thus ?case by simp
      next case ev_let3
        hence False by auto
        thus ?case by simp
      qed simp_all
  next case (ev_let2 e\<^sub>1 e\<^sub>1' e\<^sub>2)
    with ev_let2(4) show ?case
      proof (induction "Let e\<^sub>1 e\<^sub>2" e'' rule: evaluate.induct) 
      case ev_let1
        hence False by fast
        thus ?case by simp
      next case ev_let3
        hence False by auto
        thus ?case by simp
      qed simp_all
  next case (ev_let3 e\<^sub>1 e\<^sub>2)
    with ev_let3(3) show ?case
      proof (induction "Let e\<^sub>1 e\<^sub>2" e'' rule: evaluate.induct) 
      case ev_let1
        hence False by auto
        thus ?case by simp
      next case ev_let2
        hence False by auto
        thus ?case by simp
      qed simp_all
  next case (ev_rec vs e nvs)
    with ev_rec(3) show ?case
      proof (induction "Rec (vs @ [e] @ nvs)" e'' rule: evaluate.induct)
      case (ev_rec vs' e\<^sub>2 nvs')
        hence "vs' = vs" by auto
        with ev_rec show ?case by simp
      qed
  next case (ev_proj1 e e' l)
    with ev_proj1(3) show ?case
      proof (induction "Proj e l" e'' rule: evaluate.induct)
      case ev_proj2
        hence False by auto
        thus ?case by simp
      next case ev_proj_let
        hence False by auto
        thus ?case by simp
      qed simp_all
  next case (ev_proj2 fs l e)
    with ev_proj2(3) show ?case
      proof (induction "Proj (Rec fs) l" e'' rule: evaluate.induct)
      case ev_proj1
        hence False by auto
        thus ?case by simp
      qed simp_all
  next case (ev_proj_let e\<^sub>2 e\<^sub>1 l)
    with ev_proj_let(2) show ?case
      proof (induction "Proj (expr.Let e\<^sub>1 e\<^sub>2) l" e'' rule: evaluate.induct)
      case ev_proj1
        hence False by auto
        thus ?case by simp
      qed simp_all
  next case (ev_inj e l ts)
    with ev_inj(2) show ?case by (induction "Inj l ts e" e'' rule: evaluate.induct) simp_all
  next case (ev_case1 e e' t cs)
    with ev_case1(3) show ?case
      proof (induction "Case e t cs" e'' rule: evaluate.induct)
      case ev_case2
        hence False by auto
        thus ?case by simp
      next case ev_case_let
        hence False by auto
        thus ?case by simp
      qed simp_all
  next case (ev_case2 e l cs e' ts t)
    with ev_case2(3) show ?case
      proof (induction "Case (Inj l ts e) t cs" e'' rule: evaluate.induct)
      case ev_case1
        hence False by auto
        thus ?case by simp
      qed simp_all
  next case (ev_case_let e\<^sub>2 e\<^sub>1 t cs)
    with ev_case_let(2) show ?case
      proof (induction "Case (Let e\<^sub>1 e\<^sub>2) t cs" e'' rule: evaluate.induct)
      case ev_case1
        hence False by auto
        thus ?case by simp
      qed simp_all
  next case (ev_fold e t)
    with ev_fold(2) show ?case by (induction "Fold t e" e'' rule: evaluate.induct) simp_all
  next case (ev_unfold1 e e' t)
    with ev_unfold1(3) show ?case
      proof (induction "Unfold t e" e'' rule: evaluate.induct)
      case ev_unfold2
        hence False by auto
        thus ?case by simp
      next case ev_unfold_let
        hence False by auto
        thus ?case by simp
      qed simp_all
  next case (ev_unfold2 e t)
    with ev_unfold2(2) show ?case
      proof (induction "Unfold t (Fold t e)" e'' rule: evaluate.induct)
      case ev_unfold1
        hence False by auto
        thus ?case by simp
      qed simp_all
  next case (ev_unfold_let e\<^sub>2 e\<^sub>1 t)
    with ev_unfold_let(2) show ?case
      proof (induction "Unfold e\<^sub>1 (Let t e\<^sub>2)" e'' rule: evaluate.induct)
      case ev_unfold1
        hence False by auto
        thus ?case by simp
      qed simp_all
  next case (ev_tyapp1 e e' t)
    with ev_tyapp1(3) show ?case
      proof (induction "TyApp e t" e'' rule: evaluate.induct)
      case ev_tyapp2
        hence False by auto
        thus ?case by simp
      next case ev_tyapp_let
        hence False by auto
        thus ?case by simp
      qed simp_all
  next case (ev_tyapp2 k e t)
    thus ?case
      proof (induction "TyApp (TyAbs k e) t" e'' rule: evaluate.induct)
      case ev_tyapp1
        hence False by auto
        thus ?case by simp
      qed simp_all
  next case (ev_tyapp_let e\<^sub>2 e\<^sub>1 t)
    with ev_tyapp_let(2) show ?case
      proof (induction "TyApp (Let e\<^sub>1 e\<^sub>2) t" e'' rule: evaluate.induct)
      case ev_tyapp1
        hence False by auto
        thus ?case by simp
      qed simp_all
  next case (ev_tylet t e)
    thus ?case by (induction "TyLet t e" e'' rule: evaluate.induct) simp_all
  qed

end