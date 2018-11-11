theory Evaluate
imports Typecheck
begin

inductive evaluate :: "expr \<Rightarrow> expr \<Rightarrow> bool" (infix "\<leadsto>" 60) where
  ev_app1 [simp]: "e\<^sub>1 \<leadsto> e\<^sub>1' \<Longrightarrow> App e\<^sub>1 e\<^sub>2 \<leadsto> App e\<^sub>1' e\<^sub>2" 
| ev_app2 [simp]: "App (Abs t e\<^sub>1) e\<^sub>2 \<leadsto> Let e\<^sub>2 e\<^sub>1"
| ev_let1 [simp]: "e\<^sub>2 \<leadsto> e\<^sub>2' \<Longrightarrow> Let e\<^sub>1 e\<^sub>2 \<leadsto> Let e\<^sub>1 e\<^sub>2'"
| ev_rec [simp]: "list_all is_var vs \<Longrightarrow> \<not> is_var e \<Longrightarrow> 
    Rec (vs @ [e] @ nvs) \<leadsto> Let e (Rec (map (incr\<^sub>e\<^sub>e 0) vs @ [Var 0] @ map (incr\<^sub>e\<^sub>e 0) nvs))" 
| ev_proj1 [simp]: "e \<leadsto> e' \<Longrightarrow> Proj e l \<leadsto> Proj e' l"
| ev_proj2 [simp]: "list_all is_var fs \<Longrightarrow> lookup l fs = Some e \<Longrightarrow> Proj (Rec fs) l \<leadsto> e" 
| ev_inj [simp]: "\<not> is_var e \<Longrightarrow> Inj l ts e \<leadsto> Let e (Inj l ts (Var 0))"
| ev_case1 [simp]: "e \<leadsto> e' \<Longrightarrow> Case e t cs \<leadsto> Case e' t cs"
| ev_case2 [simp]: "is_var e \<Longrightarrow> lookup l cs = Some e' \<Longrightarrow> Case (Inj l ts e) t cs \<leadsto> subst\<^sub>e\<^sub>e 0 e e'"
| ev_fold [simp]: "\<not> is_var e \<Longrightarrow> Fold t e \<leadsto> Let e (Fold t (Var 0))" 
| ev_unfold1 [simp]: "e \<leadsto> e' \<Longrightarrow> Unfold t e \<leadsto> Unfold t e'"  
| ev_unfold2 [simp]: "is_var e \<Longrightarrow> Unfold t (Fold t e) \<leadsto> e" 
| ev_tyapp1 [simp]: "e \<leadsto> e' \<Longrightarrow> TyApp e t \<leadsto> TyApp e' t" 
| ev_tyapp2 [simp]: "TyApp (TyAbs k e) t \<leadsto> subst\<^sub>t\<^sub>e 0 t e" 
| ev_tylet [simp]: "TyLet t e \<leadsto> subst\<^sub>t\<^sub>e 0 t e" 

lemma [elim]: "e \<leadsto> e' \<Longrightarrow> is_value e \<Longrightarrow> False"
  by (induction e e' rule: evaluate.induct) simp_all

lemma [elim]: "e \<leadsto> e' \<Longrightarrow> is_var e \<Longrightarrow> False"
  by (induction e e' rule: evaluate.induct) simp_all

lemma [elim]: "list_all is_var vs \<Longrightarrow> list_all is_var vs' \<Longrightarrow> \<not> is_var e \<Longrightarrow> \<not> is_var e' \<Longrightarrow>
    vs @ [e] @ nvs = vs' @ [e'] @ nvs' \<Longrightarrow> vs = vs'"
  proof (induction vs arbitrary: vs')
  case Nil
    thus ?case by (induction vs') simp_all
  next case (Cons v vs)
    thus ?case by (induction vs') simp_all
  qed

theorem determinacy [elim]: "e \<leadsto> e' \<Longrightarrow> e \<leadsto> e'' \<Longrightarrow> e' = e''"
  proof (induction e e' arbitrary: e'' rule: evaluate.induct)
  case (ev_app1 e\<^sub>1 e\<^sub>1' e\<^sub>2)
    with ev_app1(3) show ?case
      proof (induction "App e\<^sub>1 e\<^sub>2" e'' rule: evaluate.induct)
      case ev_app2
        hence False by auto
        thus ?case by simp
      qed simp_all
  next case (ev_app2 t e\<^sub>1 e\<^sub>2)
    thus ?case by (induction "App (Abs t e\<^sub>1) e\<^sub>2" e'' rule: evaluate.induct) auto
  next case (ev_let1 e\<^sub>2 e\<^sub>2' e\<^sub>1)
    with ev_let1(3) show ?case by (induction "Let e\<^sub>1 e\<^sub>2" e'' rule: evaluate.induct) simp_all
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
      qed simp_all
  next case (ev_proj2 fs l e)
    with ev_proj2(3) show ?case
      proof (induction "Proj (Rec fs) l" e'' rule: evaluate.induct)
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
      qed simp_all
  next case (ev_case2 e l cs e' ts t)
    with ev_case2(3) show ?case
      proof (induction "Case (Inj l ts e) t cs" e'' rule: evaluate.induct)
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
      qed simp_all
  next case (ev_unfold2 e t)
    with ev_unfold2(2) show ?case
      proof (induction "Unfold t (Fold t e)" e'' rule: evaluate.induct)
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
      qed simp_all
  next case (ev_tyapp2 k e t)
    thus ?case
      proof (induction "TyApp (TyAbs k e) t" e'' rule: evaluate.induct)
      case ev_tyapp1
        hence False by auto
        thus ?case by simp
      qed simp_all
  next case (ev_tylet t e)
    thus ?case by (induction "TyLet t e" e'' rule: evaluate.induct) simp_all
  qed

theorem [simp]: "\<Delta>,[] \<turnstile> e : t \<Longrightarrow> unstack_eager e = (s, r) \<Longrightarrow> is_value e \<or> (\<exists>r'. r \<leadsto>\<^sub>\<beta> r')"
    and "\<Delta>,[] \<turnstile>\<^sub>f fs : ts \<Longrightarrow> \<not> is_value_f fs \<Longrightarrow> unstack_eager_f fs = (vs, nvs, s, r) \<Longrightarrow> \<exists>r'. r \<leadsto>\<^sub>\<beta> r'"
    and "\<Delta>,[] \<turnstile>\<^sub>c cs : ts \<rightarrow> t \<Longrightarrow> l < length ts \<Longrightarrow> \<exists>c. lookup l cs = Some c"
  proof (induction \<Delta> "[] :: type list" e t and \<Delta> "[] :: type list" fs ts 
               and \<Delta> "[] :: type list" cs ts t
         arbitrary: s r and vs nvs s r and l
         rule: typecheck_typecheck_fs_typecheck_cs.inducts)
  case (tc_app \<Delta> e\<^sub>1 t\<^sub>1 t\<^sub>2 e\<^sub>2)
    thus ?case
      proof (cases "is_value e\<^sub>1")
      case True note T = True
        with tc_app show ?thesis
          proof (cases "is_value e\<^sub>2")
          case True
            moreover with tc_app T obtain e\<^sub>1' where "r = App (Abs t\<^sub>1 e\<^sub>1') e\<^sub>2" by fastforce
            ultimately show ?thesis using ev_beta by blast
          qed (auto split: prod.splits)
      qed (auto split: prod.splits)
  next case (tc_let \<Delta> e\<^sub>1 t\<^sub>1 e\<^sub>2 t\<^sub>2)
    thus ?case
      proof (cases "is_value e\<^sub>1")
      case True
        moreover with tc_let have "r = Let e\<^sub>1 e\<^sub>2" by simp
        ultimately show ?thesis using ev_let by blast
      qed (auto split: prod.splits)
  next case (tc_proj \<Delta> e ts l t)
    thus ?case 
      proof (cases "is_value e")
      case True
        with tc_proj obtain fs where "r = Proj (Rec fs) l \<and> is_value_f fs \<and> \<Delta>,[] \<turnstile>\<^sub>f fs : ts" 
          by fastforce
        moreover with tc_proj obtain r' where "lookup l fs = Some r'" by fastforce
        ultimately show ?thesis using ev_proj by blast
      qed (auto split: prod.splits)
  next case (tc_case \<Delta> e ts cs t)
    thus ?case
      proof (cases "is_value e")
      case True
        with tc_case obtain l e' where E: "r = Case (Inj l ts e') t cs \<and> is_value e' \<and> 
          l < length ts" by fastforce
        moreover with tc_case obtain r' where "lookup l cs = Some r'" by fastforce
        ultimately show ?thesis using ev_case by blast
      qed (auto split: prod.splits)
  next case (tc_unfold \<Delta> e k t)
    thus ?case
      proof (cases "is_value e")
      case True
        with tc_unfold obtain e' where "r = Unfold t (Fold t e') \<and> is_value e'" by fastforce
        hence "r \<leadsto>\<^sub>\<beta> e'" by simp
        thus ?thesis by blast
      qed (auto split: prod.splits)
  next case (tc_tyapp \<Delta> e k t t')
    thus ?case
      proof (cases "is_value e")
      case True
        with tc_tyapp obtain e' where "e = TyAbs k e'" by fastforce
        with tc_tyapp True have "r \<leadsto>\<^sub>\<beta> subst\<^sub>t\<^sub>e 0 t' e'" by fastforce
        thus ?thesis by fastforce
      qed (auto split: prod.splits)
  next case (tc_tylet \<Delta> t' e t)
    moreover have "TyLet t' e \<leadsto>\<^sub>\<beta> subst\<^sub>t\<^sub>e 0 t' e" by simp
    ultimately show ?case by fastforce
  next case (tcc_cons t' e t fs ts)
    thus ?case by (induction l) simp_all
  qed (auto split: if_splits prod.splits)

theorem progress: "\<Delta>,[] \<turnstile> e : t \<Longrightarrow> is_value e \<or> (\<exists>e'. e \<leadsto> e')"
  proof -
    assume "\<Delta>,[] \<turnstile> e : t"
    moreover obtain s r where S: "unstack_eager e = (s, r)" by fastforce
    ultimately have R: "is_value e \<or> (\<exists>r'. r \<leadsto>\<^sub>\<beta> r')" by simp
    thus "is_value e \<or> (\<exists>e'. e \<leadsto> e')" 
      proof (cases "is_value e")
      case False
        with R S show ?thesis using ev_stack by fastforce
      qed simp_all
  qed

lemma preservation\<^sub>\<beta>: "e \<leadsto>\<^sub>\<beta> e' \<Longrightarrow> \<Delta>,\<Gamma> \<turnstile> e : t \<Longrightarrow> \<Delta>,\<Gamma> \<turnstile> e' : t"
  proof (induction e e' rule: reduce.induct) 
  case (ev_case e l cs e' ts tt)
    then obtain t' where "(\<Delta>,\<Gamma> \<turnstile> e : t') \<and> lookup l ts = Some t' \<and> 
      (\<forall>tt \<in> set ts. \<Delta> \<turnstile>\<^sub>k tt : Star) \<and> (\<Delta>,\<Gamma> \<turnstile>\<^sub>c cs : ts \<rightarrow> t) \<and> t = tt" by fastforce
    moreover with ev_case have "\<Delta>,insert_at 0 t' \<Gamma> \<turnstile> e' : t" by fastforce
    ultimately show ?case by simp
  next case (ev_tbeta k e t')
    then obtain tt where "(insert_at 0 k \<Delta>,map (incr\<^sub>t\<^sub>t 0) \<Gamma> \<turnstile> e : tt) \<and> (\<Delta> \<turnstile>\<^sub>k t' : k) \<and> 
      t = subst\<^sub>t\<^sub>t 0 t' tt" by fastforce
    hence "\<Delta>,map (subst\<^sub>t\<^sub>t 0 t') (map (incr\<^sub>t\<^sub>t 0) \<Gamma>) \<turnstile> subst\<^sub>t\<^sub>e 0 t' e : t" using tc_subst\<^sub>t\<^sub>e by blast
    thus ?case by simp
  qed fastforce+

theorem preservation: "e \<leadsto> e' \<Longrightarrow> \<Delta>,\<Gamma> \<turnstile> e : t \<Longrightarrow> \<Delta>,\<Gamma> \<turnstile> e' : t"
  proof (induction e e' rule: evaluate.induct)
  case (ev_stack e s r r')
    then obtain t' where "(\<Delta>,\<Gamma> \<turnstile>\<^sub>e\<^sub>c s : t' \<rightarrow> t) \<and> \<Delta>,\<Gamma> \<turnstile> r : t'" by fastforce
    moreover with ev_stack have "\<Delta>,\<Gamma> \<turnstile> r' : t'" using preservation\<^sub>\<beta> by simp
    ultimately show ?case by fastforce
  qed

end