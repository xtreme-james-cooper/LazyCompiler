theory BigStepDeterminism
imports BigStepEvaluate
begin

theorem determinism [elim]: "e \<Down> v \<Longrightarrow> e \<Down> v' \<Longrightarrow> v = v'"
  proof (induction e v arbitrary: v' rule: reduce.induct)
  case (red_var x)
    thus ?case by (induction "Var x" v' rule: reduce.induct) blast+
  next case (red_abs t e)
    thus ?case by (induction "Abs t e" v' rule: reduce.induct) blast+
  next case (red_app e\<^sub>1 _ _ e\<^sub>2)
    with red_app(5) show ?case by (induction "App e\<^sub>1 e\<^sub>2" v' rule: reduce.induct) blast+
  next case (red_app_let e\<^sub>1 _ _ e\<^sub>2)
    with red_app_let(5) show ?case by (induction "App e\<^sub>1 e\<^sub>2" v' rule: reduce.induct) blast+
  next case (red_let_0 _ e\<^sub>2 e\<^sub>1)
    with red_let_0(8) show ?case by (induction "Let e\<^sub>1 e\<^sub>2" v' rule: reduce.induct) blast+
  next case (red_let_S _ e\<^sub>2 e\<^sub>1)
    with red_let_S(4) show ?case by (induction "Let e\<^sub>1 e\<^sub>2" v' rule: reduce.induct) metis+
  next case (red_rec xs)
    thus ?case by (induction "Rec xs" v' rule: reduce.induct) blast+
  next case (red_proj _ l _ e)
    with red_proj(4) show ?case by (induction "Proj e l" v' rule: reduce.induct) fastforce+
  next case (red_proj_let e _ _ l)
    with red_proj_let(5) show ?case by (induction "Proj e l" v' rule: reduce.induct) blast+
  next case (red_inj l ts x)
    thus ?case by (induction "Inj l ts x" v' rule: reduce.induct) blast+
  next case (red_case cs l e' e ts x v t)
    with red_case(6) show ?case 
      proof (induction "Case e t cs" v' rule: reduce.induct)
      case (red_case l\<^sub>2 e'\<^sub>2 ts\<^sub>2 x\<^sub>2 v\<^sub>2)
        from red_case(2, 8) have "l\<^sub>2 = l \<and> ts\<^sub>2 = ts \<and> x\<^sub>2 = x" by blast
        with red_case(1, 4, 5, 9) show ?case by simp
      qed blast+
  next case (red_case_let e e\<^sub>1 e\<^sub>2 t cs v)
    with red_case_let(5) show ?case
      proof (induction "Case e t cs" v' rule: reduce.induct)
      case (red_case_let e\<^sub>1' e\<^sub>2' v')
        from red_case_let(1, 6) have "e\<^sub>1' = e\<^sub>1 \<and> e\<^sub>2' = e\<^sub>2" by blast
        with red_case_let(3, 7) show ?case by simp
      qed blast+
  next case (red_fold t x)
    thus ?case by (induction "Fold t x" v' rule: reduce.induct) blast+
  next case (red_unfold e t)
    with red_unfold(3) show ?case by (induction "Unfold t e" v' rule: reduce.induct) blast+
  next case (red_unfold_let e _ _ t)
    with red_unfold_let(5) show ?case by (induction "Unfold t e" v' rule: reduce.induct) blast+
  next case (red_tyabs k e)
    thus ?case by (induction "TyAbs k e" v' rule: reduce.induct) blast+
  next case (red_tyapp e _ _ t)
    with red_tyapp(5) show ?case by (induction "TyApp e t" v' rule: reduce.induct) blast+
  next case (red_tyapp_let e _ _ t)
    with red_tyapp_let(5) show ?case by (induction "TyApp e t" v' rule: reduce.induct) blast+
  next case (red_tylet t e)
    with red_tylet(3) show ?case by (induction "TyLet t e" v' rule: reduce.induct) blast+
  qed

end