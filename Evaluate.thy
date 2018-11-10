theory Evaluate
imports EvaluationContext
begin

inductive reduce :: "expr \<Rightarrow> expr \<Rightarrow> bool" (infix "\<leadsto>\<^sub>\<beta>" 60) where
  ev_beta [simp]: "is_value e\<^sub>2 \<Longrightarrow> App (Abs t e\<^sub>1) e\<^sub>2 \<leadsto>\<^sub>\<beta> subst\<^sub>e\<^sub>e 0 e\<^sub>2 e\<^sub>1" 
| ev_let [simp]: "is_value e\<^sub>1 \<Longrightarrow> Let e\<^sub>1 e\<^sub>2 \<leadsto>\<^sub>\<beta> subst\<^sub>e\<^sub>e 0 e\<^sub>1 e\<^sub>2"
| ev_proj [simp]: "is_value_f fs \<Longrightarrow> lookup l fs = Some e \<Longrightarrow> Proj (Rec fs) l \<leadsto>\<^sub>\<beta> e" 
| ev_case [simp]: "is_value e \<Longrightarrow> lookup l cs = Some e' \<Longrightarrow> Case (Inj l ts e) t cs \<leadsto>\<^sub>\<beta> subst\<^sub>e\<^sub>e 0 e e'" 
| ev_fold [simp]: "is_value e \<Longrightarrow> Unfold t (Fold t e) \<leadsto>\<^sub>\<beta> e" 
| ev_tbeta [simp]: "TyApp (TyAbs k e) t \<leadsto>\<^sub>\<beta> subst\<^sub>t\<^sub>e 0 t e" 
| ev_tlet [simp]: "TyLet t e \<leadsto>\<^sub>\<beta> subst\<^sub>t\<^sub>e 0 t e" 

inductive evaluate :: "expr \<Rightarrow> expr \<Rightarrow> bool" (infix "\<leadsto>" 60) where
  ev_stack [simp]: "unfold e = (s, r) \<Longrightarrow> r \<leadsto>\<^sub>\<beta> r' \<Longrightarrow> e \<leadsto> fold s r'"

inductive_cases [elim]: "e \<leadsto> e'"

theorem [simp]: "\<Delta>,[] \<turnstile> e : t \<Longrightarrow> unfold e = (s, r) \<Longrightarrow> is_value e \<or> (\<exists>r'. r \<leadsto>\<^sub>\<beta> r')"
    and "\<Delta>,[] \<turnstile>\<^sub>f fs : ts \<Longrightarrow> \<not> is_value_f fs \<Longrightarrow> unfold_f fs = (vs, nvs, s, r) \<Longrightarrow> \<exists>r'. r \<leadsto>\<^sub>\<beta> r'"
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
    moreover obtain s r where S: "unfold e = (s, r)" by fastforce
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