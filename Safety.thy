theory Safety
imports Evaluate
begin

theorem progress: "[] \<turnstile> e : t \<Longrightarrow> is_value e \<or> (\<exists>e'. e \<leadsto> e')"
    and "[] \<turnstile>\<^sub>f fs : ts \<Longrightarrow> \<not> is_value_f fs \<Longrightarrow> unfold_f fs = (vs, nvs, s, r) \<Longrightarrow> \<exists>r'. r \<leadsto>\<^sub>\<beta> r'"
  proof (induction "[] :: type list" e t and "[] :: type list" fs ts arbitrary: and vs nvs s r 
         rule: typecheck_typecheck_fs.inducts)
  case (tc_app e\<^sub>1 t\<^sub>1 t\<^sub>2 e\<^sub>2)
    thus ?case
      proof (cases "is_value e\<^sub>1")
      case True note T = True
        thus ?thesis
          proof (cases "is_value e\<^sub>2")
          case True
            moreover from T True have "unfold (App e\<^sub>1 e\<^sub>2) = ([], App e\<^sub>1 e\<^sub>2)" by simp
            moreover from tc_app T obtain e\<^sub>1' where "e\<^sub>1 = Abs t\<^sub>1 e\<^sub>1'" by fastforce
            ultimately show ?thesis using ev_stack ev_beta by blast
          next case False
            with tc_app obtain s r r' where "unfold e\<^sub>2 = (s, r) \<and> r \<leadsto>\<^sub>\<beta> r' \<and> e\<^sub>2 \<leadsto> fold s r'" 
              by fastforce
            moreover with True False have "unfold (App e\<^sub>1 e\<^sub>2) = (SApp2 e\<^sub>1 # s, r)" by simp
            ultimately show ?thesis using ev_stack by blast
          qed
      next case False
        with tc_app obtain s r r' where "unfold e\<^sub>1 = (s, r) \<and> r \<leadsto>\<^sub>\<beta> r' \<and> e\<^sub>1 \<leadsto> fold s r'" 
          by fastforce
        moreover with False have "unfold (App e\<^sub>1 e\<^sub>2) = (SApp1 e\<^sub>2 # s, r)" by simp
        ultimately show ?thesis using ev_stack by blast
      qed
  next case (tc_rec fs ts)
    thus ?case 
      proof (cases "is_value_f fs")
      case False
        then obtain vs nvs s e where X: "unfold (Rec fs) = (SRec vs nvs # s, e)" 
          by (cases "unfold_f fs") simp_all
        with False tc_rec obtain e' where "e \<leadsto>\<^sub>\<beta> e'" by (cases "unfold_f fs") fastforce+
        with X have "Rec fs \<leadsto> fold (SRec vs nvs # s) e'" using ev_stack by fastforce
        thus ?thesis by fastforce
      qed simp_all
  next case (tc_proj e ts l t)
    thus ?case 
      proof (cases "is_value e")
      case True
        with tc_proj obtain fs where E: "e = Rec fs \<and> is_value_f fs \<and> [] \<turnstile>\<^sub>f fs : ts" by fastforce
        hence X: "unfold (Proj (Rec fs) l) = ([], Proj (Rec fs) l)" by simp
        from tc_proj E obtain e' where "lookup l fs = Some e'" by fastforce
        with E have "Proj (Rec fs) l \<leadsto>\<^sub>\<beta> e'" by simp
        with X E show ?thesis using ev_stack by fastforce
      next case False
        with tc_proj obtain s r r' where "unfold e = (s, r) \<and> r \<leadsto>\<^sub>\<beta> r' \<and> e \<leadsto> fold s r'" 
          by fastforce
        moreover with False have "unfold (Proj e l) = (SProj l # s, r)" by simp
        ultimately show ?thesis using ev_stack by blast
      qed
  next case (tcf_cons e t fs ts l)
    thus ?case
      proof (cases "is_value e")
      case True
        with tcf_cons show ?thesis by (cases "unfold_f fs") simp_all
      qed fastforce+
  qed simp_all

lemma preservation\<^sub>\<beta>: "e \<leadsto>\<^sub>\<beta> e' \<Longrightarrow> \<Gamma> \<turnstile> e : t \<Longrightarrow> \<Gamma> \<turnstile> e' : t"
  by (induction e e' rule: reduce.induct) fastforce+

theorem preservation: "e \<leadsto> e' \<Longrightarrow> \<Gamma> \<turnstile> e : t \<Longrightarrow> \<Gamma> \<turnstile> e' : t"
  proof (induction e e' rule: evaluate.induct)
  case (ev_stack e s r r')
    then obtain t' where "(\<Gamma> \<turnstile> s : t' \<rightarrow> t) \<and> \<Gamma> \<turnstile> r : t'" by fastforce
    moreover with ev_stack have "\<Gamma> \<turnstile> r' : t'" using preservation\<^sub>\<beta> by simp
    ultimately show ?case by fastforce
  qed

end