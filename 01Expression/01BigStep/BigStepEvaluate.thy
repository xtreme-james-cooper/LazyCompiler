theory BigStepEvaluate
imports "../Typecheck"
begin

(*

inductive evaluate :: "expr \<Rightarrow> expr \<Rightarrow> bool" (infix "\<leadsto>" 60) where
  ev_app1 [simp]: "e\<^sub>1 \<leadsto> e\<^sub>1' \<Longrightarrow> App e\<^sub>1 e\<^sub>2 \<leadsto> App e\<^sub>1' e\<^sub>2" 
| ev_app2 [simp]: "App (Abs t e\<^sub>1) e\<^sub>2 \<leadsto> Let e\<^sub>2 e\<^sub>1"
| ev_app_let [simp]: "is_value e\<^sub>1\<^sub>2 \<Longrightarrow> App (Let e\<^sub>1\<^sub>1 e\<^sub>1\<^sub>2) e\<^sub>2 \<leadsto> Let e\<^sub>1\<^sub>1 (App e\<^sub>1\<^sub>2 (incr\<^sub>e\<^sub>e 0 e\<^sub>2))"
| ev_let1 [simp]: "e\<^sub>2 \<leadsto> e\<^sub>2' \<Longrightarrow> Let e\<^sub>1 e\<^sub>2 \<leadsto> Let e\<^sub>1 e\<^sub>2'"
| ev_let2 [simp]: "e\<^sub>1 \<leadsto> e\<^sub>1' \<Longrightarrow> head_var e\<^sub>2 = Some 0 \<Longrightarrow> Let e\<^sub>1 e\<^sub>2 \<leadsto> Let e\<^sub>1' e\<^sub>2"
| ev_let3 [simp]: "is_value e\<^sub>1 \<Longrightarrow> head_var e\<^sub>2 = Some 0 \<Longrightarrow> 
    Let e\<^sub>1 e\<^sub>2 \<leadsto> Let e\<^sub>1 (subst\<^sub>e\<^sub>e 0 (incr\<^sub>e\<^sub>e 0 e\<^sub>1) e\<^sub>2)"
| ev_proj1 [simp]: "e \<leadsto> e' \<Longrightarrow> Proj e l \<leadsto> Proj e' l"
| ev_proj2 [simp]: "lookup fs l = Some x \<Longrightarrow> Proj (Rec fs) l \<leadsto> Var x" 
| ev_proj_let [simp]: "is_value e\<^sub>2 \<Longrightarrow> Proj (Let e\<^sub>1 e\<^sub>2) l \<leadsto> Let e\<^sub>1 (Proj e\<^sub>2 l)" 
| ev_case1 [simp]: "e \<leadsto> e' \<Longrightarrow> Case e t cs \<leadsto> Case e' t cs"
| ev_case2 [simp]: "lookup cs l = Some e \<Longrightarrow> Case (Inj l ts x) t cs \<leadsto> Let (Var x) e"
| ev_case_let [simp]: "is_value e\<^sub>2 \<Longrightarrow> 
    Case (Let e\<^sub>1 e\<^sub>2) t cs \<leadsto> Let e\<^sub>1 (Case e\<^sub>2 t (map (incr\<^sub>e\<^sub>e (Suc 0)) cs))" 
| ev_unfold1 [simp]: "e \<leadsto> e' \<Longrightarrow> Unfold t e \<leadsto> Unfold t e'"  
| ev_unfold2 [simp]: "Unfold t (Fold t e) \<leadsto> Var e" 
| ev_unfold_let [simp]: "is_value e\<^sub>2 \<Longrightarrow> Unfold t (Let e\<^sub>1 e\<^sub>2) \<leadsto> Let e\<^sub>1 (Unfold t e\<^sub>2)" 
| ev_tyapp1 [simp]: "e \<leadsto> e' \<Longrightarrow> TyApp e t \<leadsto> TyApp e' t" 
| ev_tyapp2 [simp]: "TyApp (TyAbs k e) t \<leadsto> subst\<^sub>t\<^sub>e 0 t e" 
| ev_tyapp_let [simp]: "is_value e\<^sub>2 \<Longrightarrow> TyApp (Let e\<^sub>1 e\<^sub>2) t \<leadsto> Let e\<^sub>1 (TyApp e\<^sub>2 t)" 
| ev_tylet [simp]: "TyLet t e \<leadsto> subst\<^sub>t\<^sub>e 0 t e" 

lemma canonical_arrow [simp]: "\<Delta>,\<Gamma> \<turnstile> e : Arrow t\<^sub>1 t\<^sub>2 \<Longrightarrow> is_value e \<Longrightarrow> 
    (\<exists>e'. e = Abs t\<^sub>1 e') \<or> (\<exists>e\<^sub>1 e\<^sub>2. e = Let e\<^sub>1 e\<^sub>2 \<and> is_value e\<^sub>2)"
  by (induction \<Gamma> e "Arrow t\<^sub>1 t\<^sub>2" rule: typecheck_typecheck_cs.inducts(1)) simp_all

lemma canonical_record [simp]: "\<Delta>,\<Gamma> \<turnstile> e : Record ts \<Longrightarrow> is_value e \<Longrightarrow> 
    (\<exists>fs. e = Rec fs \<and> \<Delta>,\<Gamma> \<turnstile>\<^sub>x\<^sub>s fs : ts) \<or> (\<exists>e\<^sub>1 e\<^sub>2. e = Let e\<^sub>1 e\<^sub>2 \<and> is_value e\<^sub>2)"
  by (induction \<Gamma> e "Record ts" rule: typecheck_typecheck_cs.inducts(1)) simp_all

lemma canonical_variant [simp]: "\<Delta>,\<Gamma> \<turnstile> e : Variant ts \<Longrightarrow> is_value e \<Longrightarrow> 
    (\<exists>l e'. e = Inj l ts e' \<and> l < length ts) \<or> (\<exists>e\<^sub>1 e\<^sub>2. e = Let e\<^sub>1 e\<^sub>2 \<and> is_value e\<^sub>2)"
  by (induction \<Gamma> e "Variant ts" rule: typecheck_typecheck_cs.inducts(1)) auto

lemma canonical_inductive [simp]: "\<Delta>,\<Gamma> \<turnstile> e : Inductive k t \<Longrightarrow> is_value e \<Longrightarrow> 
    (\<exists>e'. e = Fold t e') \<or> (\<exists>e\<^sub>1 e\<^sub>2. e = Let e\<^sub>1 e\<^sub>2 \<and> is_value e\<^sub>2)"
  by (induction \<Gamma> e "Inductive k t" rule: typecheck_typecheck_cs.inducts(1)) auto

lemma canonical_forall [simp]: "\<Delta>,\<Gamma> \<turnstile> e : Forall k t \<Longrightarrow> is_value e \<Longrightarrow> 
    (\<exists>e'. e = TyAbs k e') \<or> (\<exists>e\<^sub>1 e\<^sub>2. e = Let e\<^sub>1 e\<^sub>2 \<and> is_value e\<^sub>2)"
  by (induction \<Gamma> e "Forall k t" rule: typecheck_typecheck_cs.inducts(1)) auto

lemma lookup_in_tc [simp]: "\<Delta>,\<Gamma> \<turnstile>\<^sub>x\<^sub>s fs : ts \<Longrightarrow> lookup ts l = Some t \<Longrightarrow> \<exists>e. lookup fs l = Some e"
  by (induction fs l arbitrary: ts rule: lookup.induct) auto

lemma progress': "\<Delta>,\<Gamma> \<turnstile> e : t \<Longrightarrow> 
  is_value e \<or> (\<exists>e'. e \<leadsto> e') \<or> (\<exists>x < length \<Gamma>. head_var e = Some x)"
    and "\<Delta>,\<Gamma> \<turnstile>\<^sub>c cs : ts \<rightarrow> t \<Longrightarrow> l < length ts \<Longrightarrow> \<exists>c. lookup cs l = Some c"
  proof (induction \<Delta> \<Gamma> e t and \<Delta> \<Gamma> cs ts t arbitrary: and l rule: typecheck_typecheck_cs.inducts)
  case tc_var
    thus ?case by (metis lookup_less_than head_var.simps(1))
  next case tc_app
    thus ?case by (metis canonical_arrow ev_app1 ev_app2 ev_app_let head_var.simps(3))
  next case (tc_let \<Delta> \<Gamma> e\<^sub>1 t\<^sub>1 e\<^sub>2 t\<^sub>2)
    thus ?case
      proof (cases "is_value e\<^sub>2")
      case False note F = False
        thus ?thesis
          proof (cases "\<exists>e\<^sub>2'. e\<^sub>2 \<leadsto> e\<^sub>2'")
          case False
            with tc_let F obtain x where X: "x < Suc (length \<Gamma>) \<and> head_var e\<^sub>2 = Some x" by fastforce
            thus ?thesis 
              proof (cases x)
              case 0
                with X show ?thesis
                  proof (cases "is_value e\<^sub>1")
                  case False
                    with tc_let X 0 ev_let2 show ?thesis by fastforce
                  qed (metis ev_let3)
              qed simp_all
          qed (metis ev_let1)
      qed simp_all
  next case tc_proj
    thus ?case 
      by (metis canonical_record ev_proj1 ev_proj2 ev_proj_let lookup_in_tc head_var.simps(6))
  next case tc_case
    thus ?case by (metis canonical_variant ev_case1 ev_case2 ev_case_let head_var.simps(8))
  next case tc_unfold
    thus ?case by (metis canonical_inductive ev_unfold1 ev_unfold2 ev_unfold_let head_var.simps(10))
  next case tc_tyapp
    thus ?case by simp (metis canonical_forall ev_tyapp1 ev_tyapp2 ev_tyapp_let)
  next case tc_tylet
    thus ?case by (metis ev_tylet)
  next case tcc_cons
    thus ?case by (induction l) simp_all
  qed simp_all

theorem progress: "\<Delta>,[] \<turnstile> e : t \<Longrightarrow> is_value e \<or> (\<exists>e'. e \<leadsto> e')"
  using progress' by fastforce

theorem preservation: "e \<leadsto> e' \<Longrightarrow> \<Delta>,\<Gamma> \<turnstile> e : t \<Longrightarrow> \<Delta>,\<Gamma> \<turnstile> e' : t"
  proof (induction e e' arbitrary: \<Delta> \<Gamma> t rule: evaluate.induct) 
  case (ev_proj2 l xs x)
    hence "lookup \<Gamma> x = Some t" by fastforce
    thus ?case by simp
  next case (ev_case2 cs l e ts x t')
    then obtain tt where "(lookup \<Gamma> x = Some tt) \<and> lookup ts l = Some tt \<and> 
      (\<forall>tt \<in> set ts. \<Delta> \<turnstile>\<^sub>k tt : Star) \<and> (\<Delta>,\<Gamma> \<turnstile>\<^sub>c cs : ts \<rightarrow> t') \<and> t' = t" by fastforce
    moreover with ev_case2 have "\<Delta>,insert_at 0 tt \<Gamma> \<turnstile> e : t" by fastforce
    ultimately show ?case by (metis tc_let tc_var)
  next case (ev_tyapp2 k e t')
    then obtain tt where T: "(insert_at 0 k \<Delta>,map (incr\<^sub>t\<^sub>t 0) \<Gamma> \<turnstile> e : tt) \<and> (\<Delta> \<turnstile>\<^sub>k t' : k) \<and> 
      t = subst\<^sub>t\<^sub>t 0 t' tt" by fastforce
    moreover hence "\<Delta>,map (subst\<^sub>t\<^sub>t 0 t') (map (incr\<^sub>t\<^sub>t 0) \<Gamma>) \<turnstile> subst\<^sub>t\<^sub>e 0 t' e : subst\<^sub>t\<^sub>t 0 t' tt" 
      using tc_subst\<^sub>t\<^sub>e by fastforce
    ultimately show ?case by simp
  qed fastforce+

*)

end