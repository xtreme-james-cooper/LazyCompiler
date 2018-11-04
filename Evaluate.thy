theory Evaluate
imports Stack
begin

inductive reduce :: "expr \<Rightarrow> expr \<Rightarrow> bool" (infix "\<leadsto>\<^sub>\<beta>" 60) where
  ev_beta [simp]: "is_value e\<^sub>2 \<Longrightarrow> App (Abs t e\<^sub>1) e\<^sub>2 \<leadsto>\<^sub>\<beta> subst 0 e\<^sub>2 e\<^sub>1" 
| ev_proj [simp]: "is_value_f fs \<Longrightarrow> lookup l fs = Some e \<Longrightarrow> Proj (Rec fs) l \<leadsto>\<^sub>\<beta> e" 
| ev_case [simp]: "is_value e \<Longrightarrow> lookup l cs = Some e' \<Longrightarrow> Case (Inj l ts e) cs \<leadsto>\<^sub>\<beta> subst 0 e e'" 

inductive evaluate :: "expr \<Rightarrow> expr \<Rightarrow> bool" (infix "\<leadsto>" 60) where
  ev_stack [simp]: "unfold e = (s, r) \<Longrightarrow> r \<leadsto>\<^sub>\<beta> r' \<Longrightarrow> e \<leadsto> fold s r'"

inductive_cases [elim]: "e \<leadsto> e'"

theorem [simp]: "[] \<turnstile> e : t \<Longrightarrow> unfold e = (s, r) \<Longrightarrow> is_value e \<or> (\<exists>r'. r \<leadsto>\<^sub>\<beta> r')"
    and "[] \<turnstile>\<^sub>f fs : ts \<Longrightarrow> \<not> is_value_f fs \<Longrightarrow> unfold_f fs = (vs, nvs, s, r) \<Longrightarrow> \<exists>r'. r \<leadsto>\<^sub>\<beta> r'"
    and "[] \<turnstile>\<^sub>c cs : ts \<rightarrow> t \<Longrightarrow> l < length ts \<Longrightarrow> \<exists>c. lookup l cs = Some c"
  proof (induction "[] :: type list" e t and "[] :: type list" fs ts and "[] :: type list" cs ts t
         arbitrary: s r and vs nvs s r and l
         rule: typecheck_typecheck_fs_typecheck_cs.inducts)
  case (tc_app e\<^sub>1 t\<^sub>1 t\<^sub>2 e\<^sub>2)
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
  next case (tc_proj e ts l t)
    thus ?case 
      proof (cases "is_value e")
      case True
        with tc_proj obtain fs where "r = Proj (Rec fs) l \<and> is_value_f fs \<and> [] \<turnstile>\<^sub>f fs : ts" 
          by fastforce
        moreover with tc_proj obtain r' where "lookup l fs = Some r'" by fastforce
        ultimately show ?thesis using ev_proj by blast
      qed (auto split: prod.splits)
  next case (tc_case e ts cs t)
    thus ?case
      proof (cases "is_value e")
      case True
        with tc_case obtain l e' where E: "r = Case (Inj l ts e') cs \<and> is_value e' \<and> l < length ts" 
          by fastforce
        moreover with tc_case obtain r' where "lookup l cs = Some r'" by fastforce
        ultimately show ?thesis using ev_case by blast
      qed (auto split: prod.splits)
  next case (tcc_cons t' e t fs ts)
    thus ?case by (induction l) simp_all
  qed (auto split: if_splits prod.splits)

theorem progress: "[] \<turnstile> e : t \<Longrightarrow> is_value e \<or> (\<exists>e'. e \<leadsto> e')"
  proof -
    assume "[] \<turnstile> e : t"
    moreover obtain s r where S: "unfold e = (s, r)" by fastforce
    ultimately have R: "is_value e \<or> (\<exists>r'. r \<leadsto>\<^sub>\<beta> r')" by simp
    thus "is_value e \<or> (\<exists>e'. e \<leadsto> e')" 
      proof (cases "is_value e")
      case False
        with R S show ?thesis using ev_stack by fastforce
      qed simp_all
  qed

lemma preservation\<^sub>\<beta>: "e \<leadsto>\<^sub>\<beta> e' \<Longrightarrow> \<Gamma> \<turnstile> e : t \<Longrightarrow> \<Gamma> \<turnstile> e' : t"
  proof (induction e e' rule: reduce.induct) 
  case (ev_case e l cs e' ts)
    then obtain t' where "(\<Gamma> \<turnstile> e : t') \<and> lookup l ts = Some t' \<and> \<Gamma> \<turnstile>\<^sub>c cs : ts \<rightarrow> t" by fastforce
    moreover with ev_case have "insert_at 0 t' \<Gamma> \<turnstile> e' : t" by fastforce
    ultimately show ?case by simp
  qed fastforce+

theorem preservation: "e \<leadsto> e' \<Longrightarrow> \<Gamma> \<turnstile> e : t \<Longrightarrow> \<Gamma> \<turnstile> e' : t"
  proof (induction e e' rule: evaluate.induct)
  case (ev_stack e s r r')
    then obtain t' where "(\<Gamma> \<turnstile> s : t' \<rightarrow> t) \<and> \<Gamma> \<turnstile> r : t'" by fastforce
    moreover with ev_stack have "\<Gamma> \<turnstile> r' : t'" using preservation\<^sub>\<beta> by simp
    ultimately show ?case by fastforce
  qed

end