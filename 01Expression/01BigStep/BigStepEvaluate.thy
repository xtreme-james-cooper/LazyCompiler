theory BigStepEvaluate
imports "../Typecheck"
begin

inductive reduce :: "expr \<Rightarrow> expr \<Rightarrow> bool" (infix "\<Down>" 60) where
  red_var [simp]: "Var x \<Down> Var x" 
| red_abs [simp]: "Abs t e \<Down> Abs t e"
| red_app [simp]: "e\<^sub>1 \<Down> Abs t e\<^sub>1' \<Longrightarrow> Let e\<^sub>2 e\<^sub>1' \<Down> v \<Longrightarrow> App e\<^sub>1 e\<^sub>2 \<Down> v" 
| red_app_let [simp]: "e\<^sub>1 \<Down> Let e\<^sub>1\<^sub>1 e\<^sub>1\<^sub>2 \<Longrightarrow> Let e\<^sub>1\<^sub>1 (App e\<^sub>1\<^sub>2 (incr\<^sub>e\<^sub>e 0 e\<^sub>2)) \<Down> v \<Longrightarrow> App e\<^sub>1 e\<^sub>2 \<Down> v"
| red_let_0 [simp]: "head_var e\<^sub>2' = Some 0 \<Longrightarrow> e\<^sub>2 \<Down> e\<^sub>2' \<Longrightarrow> e\<^sub>1 \<Down> e\<^sub>1' \<Longrightarrow> 
    Let e\<^sub>1 (subst\<^sub>e\<^sub>e 0 (incr\<^sub>e\<^sub>e 0 e\<^sub>1) e\<^sub>2) \<Down> v \<Longrightarrow> Let e\<^sub>1 e\<^sub>2 \<Down> v"
| red_let_S [simp]: "head_var e\<^sub>2' \<noteq> Some 0 \<Longrightarrow> e\<^sub>2 \<Down> e\<^sub>2' \<Longrightarrow> Let e\<^sub>1 e\<^sub>2 \<Down> Let e\<^sub>1 e\<^sub>2'"
| red_rec [simp]: "Rec xs \<Down> Rec xs"
| red_proj [simp]: "lookup xs l = Some x \<Longrightarrow> e \<Down> Rec xs \<Longrightarrow> Proj e l \<Down> Var x"
| red_proj_let [simp]: "e \<Down> Let e\<^sub>1 e\<^sub>2 \<Longrightarrow> Let e\<^sub>1 (Proj e\<^sub>2 l) \<Down> v \<Longrightarrow> Proj e l \<Down> v" 
| red_inj [simp]: "Inj l ts x \<Down> Inj l ts x"
| red_case [simp]: "lookup cs l = Some e' \<Longrightarrow> e \<Down> Inj l ts x \<Longrightarrow> Let (Var x) e' \<Down> v \<Longrightarrow> 
    Case e t cs \<Down> v"
| red_case_let [simp]: "e \<Down> Let e\<^sub>1 e\<^sub>2 \<Longrightarrow> Let e\<^sub>1 (Case e\<^sub>2 t (map (incr\<^sub>e\<^sub>e (Suc 0)) cs)) \<Down> v \<Longrightarrow> 
    Case e t cs \<Down> v"
| red_fold [simp]: "Fold t x \<Down> Fold t x"
| red_unfold [simp]: "e \<Down> Fold t x \<Longrightarrow> Unfold t e \<Down> Var x"  
| red_unfold_let [simp]: "e \<Down> Let e\<^sub>1 e\<^sub>2 \<Longrightarrow> Let e\<^sub>1 (Unfold t e\<^sub>2) \<Down> v \<Longrightarrow> Unfold t e \<Down> v" 
| red_tyabs [simp]: "TyAbs k e \<Down> TyAbs k e"
| red_tyapp [simp]: "e \<Down> TyAbs k e' \<Longrightarrow> subst\<^sub>t\<^sub>e 0 t e' \<Down> v \<Longrightarrow> TyApp e t \<Down> v" 
| red_tyapp_let [simp]: "e \<Down> Let e\<^sub>1 e\<^sub>2 \<Longrightarrow> Let e\<^sub>1 (TyApp e\<^sub>2 t) \<Down> v \<Longrightarrow> TyApp e t \<Down> v" 
| red_tylet [simp]: "subst\<^sub>t\<^sub>e 0 t e \<Down> v \<Longrightarrow> TyLet t e \<Down> v" 

theorem preservation [elim]: "e \<Down> v \<Longrightarrow> \<Delta>,\<Gamma> \<turnstile> e : t \<Longrightarrow> \<Delta>,\<Gamma> \<turnstile> v : t"
  proof (induction e v arbitrary: \<Gamma> t rule: reduce.induct) 
  case (red_proj xs l x e)
    hence "lookup \<Gamma> x = Some t" by fastforce
    thus ?case by simp
  next case (red_case cs l e' e ts x v tt)
    moreover hence "(\<Delta>,\<Gamma> \<turnstile> e : Variant ts) \<and> (\<Delta>,\<Gamma> \<turnstile>\<^sub>c cs : ts \<rightarrow> t) \<and> (\<Delta> \<turnstile>\<^sub>k t : Star)" by fastforce
    moreover with red_case obtain t' where T: "lookup \<Gamma> x = Some t' \<and> lookup ts l = Some t' \<and> 
      (\<forall>tt \<in> set ts. \<Delta> \<turnstile>\<^sub>k tt : Star)" by blast
    ultimately have "\<Delta>,insert_at 0 t' \<Gamma> \<turnstile> e' : t" by auto
    with red_case T show ?case by (metis tc_let tc_var)
  next case (red_tyapp e k e' tt v)
    then obtain t' k' where T: "t = subst\<^sub>t\<^sub>t 0 tt t' \<and> (\<Delta>,\<Gamma> \<turnstile> e : Forall k' t') \<and> (\<Delta> \<turnstile>\<^sub>k tt : k')" 
      by fastforce
    with red_tyapp have "insert_at 0 k' \<Delta>,map (incr\<^sub>t\<^sub>t 0) \<Gamma> \<turnstile> e' : t'" by fastforce
    with T have "\<Delta>,map (subst\<^sub>t\<^sub>t 0 tt) (map (incr\<^sub>t\<^sub>t 0) \<Gamma>) \<turnstile> subst\<^sub>t\<^sub>e 0 tt e' : subst\<^sub>t\<^sub>t 0 tt t'" 
      by (metis tc_subst\<^sub>t\<^sub>e le0)
    with red_tyapp T show ?case by simp
  qed fastforce+

(* we can't actually do progress because the language is not normalizing *)
(* instead we prove the weaker claim that we get a value _if it's defined at all_ *)

lemma reduce_to_value' [simp]: "e \<Down> v \<Longrightarrow> \<Delta>,\<Gamma> \<turnstile> e : t \<Longrightarrow> 
      is_value v \<or> (\<exists>x < length \<Gamma>. head_var v = Some x)"
  proof (induction e v arbitrary: \<Gamma> rule: reduce.induct)
  case (red_app e\<^sub>1 tt e\<^sub>1' e\<^sub>2 v)
    then obtain t\<^sub>1 where T: "(\<Delta>,\<Gamma> \<turnstile> e\<^sub>1 : Arrow t\<^sub>1 t) \<and> (\<Delta>,\<Gamma> \<turnstile> e\<^sub>2 : t\<^sub>1)" by fastforce
    with red_app have "\<Delta>,\<Gamma> \<turnstile> Abs tt e\<^sub>1' : Arrow t\<^sub>1 t" by fastforce
    with T have "\<Delta>,\<Gamma> \<turnstile> Let e\<^sub>2 e\<^sub>1' : t" by auto
    with red_app show ?case by simp
  next case (red_app_let e\<^sub>1 e\<^sub>1\<^sub>1 e\<^sub>1\<^sub>2 e\<^sub>2 v)
    then obtain t\<^sub>1 where T: "(\<Delta>,\<Gamma> \<turnstile> e\<^sub>1 : Arrow t\<^sub>1 t) \<and> (\<Delta>,\<Gamma> \<turnstile> e\<^sub>2 : t\<^sub>1)" by fastforce
    with red_app_let have "\<Delta>,\<Gamma> \<turnstile> Let e\<^sub>1\<^sub>1 e\<^sub>1\<^sub>2 : Arrow t\<^sub>1 t" by fastforce
    then obtain tt where "(\<Delta>,\<Gamma> \<turnstile> e\<^sub>1\<^sub>1 : tt) \<and> (\<Delta>,insert_at 0 tt \<Gamma> \<turnstile> e\<^sub>1\<^sub>2 : Arrow t\<^sub>1 t)" by fastforce
    with T have "\<Delta>,\<Gamma> \<turnstile> Let e\<^sub>1\<^sub>1 (App e\<^sub>1\<^sub>2 (incr\<^sub>e\<^sub>e 0 e\<^sub>2)) : t" by fastforce
    with red_app_let show ?case by simp
  next case (red_let_0 e\<^sub>2' e\<^sub>2 e\<^sub>1 e\<^sub>1' v)
    hence "\<Delta>,\<Gamma> \<turnstile> Let e\<^sub>1 (subst\<^sub>e\<^sub>e 0 (incr\<^sub>e\<^sub>e 0 e\<^sub>1) e\<^sub>2) : t" by fastforce
    with red_let_0 show ?case by simp
  next case (red_let_S e\<^sub>2' e\<^sub>2 e\<^sub>1)
    from red_let_S have "\<Delta>,\<Gamma> \<turnstile> Let e\<^sub>1 e\<^sub>2 : t" by simp
    then obtain t\<^sub>1 where "(\<Delta>,\<Gamma> \<turnstile> e\<^sub>1 : t\<^sub>1) \<and> (\<Delta>,insert_at 0 t\<^sub>1 \<Gamma> \<turnstile> e\<^sub>2 : t)" by fastforce
    with red_let_S have "is_value e\<^sub>2' \<or> (\<exists>x < length (insert_at 0 t\<^sub>1 \<Gamma>). head_var e\<^sub>2' = Some x)" 
      by blast
    with red_let_S show ?case by (auto split: nat.splits)
  next case (red_proj xs l x e)
    then obtain ts where "(\<Delta>,\<Gamma> \<turnstile> e : Record ts) \<and> lookup ts l = Some t" by fastforce
    with red_proj have "\<Delta>,\<Gamma> \<turnstile> Rec xs : Record ts" by fastforce
    with red_proj show ?case by auto
  next case (red_proj_let e e\<^sub>1 e\<^sub>2 l v)
    then obtain ts where T: "(\<Delta>,\<Gamma> \<turnstile> e : Record ts) \<and> lookup ts l = Some t" by fastforce
    with red_proj_let have "\<Delta>,\<Gamma> \<turnstile> Let e\<^sub>1 e\<^sub>2 : Record ts" by fastforce
    then obtain t\<^sub>1 where "(\<Delta>,\<Gamma> \<turnstile> e\<^sub>1 : t\<^sub>1) \<and> (\<Delta>,insert_at 0 t\<^sub>1 \<Gamma> \<turnstile> e\<^sub>2 : Record ts)" by fastforce
    with T have "\<Delta>,\<Gamma> \<turnstile> Let e\<^sub>1 (Proj e\<^sub>2 l) : t" by fastforce
    with red_proj_let show ?case by simp
  next case (red_case cs l e' e ts x v tt) 
    then obtain ts' where T: "tt = t \<and> (\<Delta>,\<Gamma> \<turnstile> e : Variant ts') \<and> (\<Delta>,\<Gamma> \<turnstile>\<^sub>c cs : ts' \<rightarrow> t) \<and> 
      (\<Delta> \<turnstile>\<^sub>k t : Star)" by fastforce
    with red_case have "\<Delta>,\<Gamma> \<turnstile> Inj l ts x : Variant ts'" by fastforce
    then obtain t' where S: "ts' = ts \<and> lookup \<Gamma> x = Some t' \<and> lookup ts l = Some t' \<and> 
      (\<forall>tt \<in> set ts. \<Delta> \<turnstile>\<^sub>k tt : Star)" by fastforce
    with red_case T have X: "\<Delta>,insert_at 0 t' \<Gamma> \<turnstile> e' : t" by auto
    from S have "\<Delta>,\<Gamma> \<turnstile> Var x : t'" by simp
    with X have "\<Delta>,\<Gamma> \<turnstile> Let (Var x) e' : t" by simp
    with red_case T show ?case by simp
  next case (red_case_let e e\<^sub>1 e\<^sub>2 tt cs v)
    then obtain ts where T: "t = tt \<and> (\<Delta>,\<Gamma> \<turnstile> e : Variant ts) \<and> (\<Delta>,\<Gamma> \<turnstile>\<^sub>c cs : ts \<rightarrow> t) \<and> 
      (\<Delta> \<turnstile>\<^sub>k t : Star)" by fastforce
    with red_case_let have "\<Delta>,\<Gamma> \<turnstile> Let e\<^sub>1 e\<^sub>2 : Variant ts" by fastforce
    then obtain t\<^sub>1 where "(\<Delta>,\<Gamma> \<turnstile> e\<^sub>1 : t\<^sub>1) \<and> (\<Delta>,insert_at 0 t\<^sub>1 \<Gamma> \<turnstile> e\<^sub>2 : Variant ts)" by fastforce
    with T have "\<Delta>,\<Gamma> \<turnstile> Let e\<^sub>1 (Case e\<^sub>2 tt (map (incr\<^sub>e\<^sub>e (Suc 0)) cs)) : t" by fastforce
    with red_case_let show ?case by simp
  next case (red_unfold e tt x) 
    then obtain k where T: "t = subst\<^sub>t\<^sub>t 0 (Inductive k tt) tt \<and> (\<Delta>,\<Gamma> \<turnstile> e : Inductive k tt) \<and> 
      (insert_at 0 k \<Delta> \<turnstile>\<^sub>k tt : Star)" by fastforce
    with red_unfold have "\<Delta>,\<Gamma> \<turnstile> Fold tt x : Inductive k tt" by fastforce
    hence "lookup \<Gamma> x = Some (subst\<^sub>t\<^sub>t 0 (Inductive k tt) tt) \<and> (insert_at 0 k \<Delta> \<turnstile>\<^sub>k tt : Star)" 
      by fastforce
    with T show ?case by auto
  next case (red_unfold_let e e\<^sub>1 e\<^sub>2 tt v)
    then obtain k where T: "t = subst\<^sub>t\<^sub>t 0 (Inductive k tt) tt \<and> (\<Delta>,\<Gamma> \<turnstile> e : Inductive k tt) \<and> 
      (insert_at 0 k \<Delta> \<turnstile>\<^sub>k tt : Star)" by fastforce
    with red_unfold_let have "\<Delta>,\<Gamma> \<turnstile> Let e\<^sub>1 e\<^sub>2 : Inductive k tt" by fastforce
    then obtain t\<^sub>1 where "(\<Delta>,\<Gamma> \<turnstile> e\<^sub>1 : t\<^sub>1) \<and> (\<Delta>,insert_at 0 t\<^sub>1 \<Gamma> \<turnstile> e\<^sub>2 : Inductive k tt)" 
      by fastforce
    with T have "\<Delta>,\<Gamma> \<turnstile> Let e\<^sub>1 (Unfold tt e\<^sub>2) : t" by fastforce
    with red_unfold_let show ?case by simp
  next case (red_tyapp e k e' t' v)
    then obtain tt kk where T: "t = subst\<^sub>t\<^sub>t 0 t' tt \<and> (\<Delta>,\<Gamma> \<turnstile> e : Forall kk tt) \<and> (\<Delta> \<turnstile>\<^sub>k t' : kk)" 
      by fastforce
    with red_tyapp have "\<Delta>,\<Gamma> \<turnstile> TyAbs k e' : Forall kk tt" by fastforce
    hence "kk = k \<and> insert_at 0 k \<Delta>,map (incr\<^sub>t\<^sub>t 0) \<Gamma> \<turnstile> e' : tt" by fastforce
    with T have "\<Delta>,map (subst\<^sub>t\<^sub>t 0 t') (map (incr\<^sub>t\<^sub>t 0) \<Gamma>) \<turnstile> subst\<^sub>t\<^sub>e 0 t' e' : subst\<^sub>t\<^sub>t 0 t' tt" 
      by (metis tc_subst\<^sub>t\<^sub>e le0)
    with red_tyapp T show ?case by simp
  next case (red_tyapp_let e e\<^sub>1 e\<^sub>2 tt v) 
    then obtain t' k where T: "t = subst\<^sub>t\<^sub>t 0 tt t' \<and> (\<Delta>,\<Gamma> \<turnstile> e : Forall k t') \<and> (\<Delta> \<turnstile>\<^sub>k tt : k)" 
      by fastforce
    with red_tyapp_let have "\<Delta>,\<Gamma> \<turnstile> Let e\<^sub>1 e\<^sub>2 : Forall k t'" by fastforce
    then obtain t\<^sub>1 where "(\<Delta>,\<Gamma> \<turnstile> e\<^sub>1 : t\<^sub>1) \<and> (\<Delta>,insert_at 0 t\<^sub>1 \<Gamma> \<turnstile> e\<^sub>2 : Forall k t')" by fastforce
    with T have "\<Delta>,\<Gamma> \<turnstile> Let e\<^sub>1 (TyApp e\<^sub>2 tt) : t" by fastforce
    with red_tyapp_let show ?case by simp
  qed auto

theorem reduce_to_value: "e \<Down> v \<Longrightarrow> \<Delta>,[] \<turnstile> e : t \<Longrightarrow> is_value v"
  using reduce_to_value' by fastforce

end