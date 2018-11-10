theory Typecheck
imports Expression Kindcheck
begin

inductive typecheck :: "kind list \<Rightarrow> type list \<Rightarrow> expr \<Rightarrow> type \<Rightarrow> bool" (infix ",_ \<turnstile> _ :" 60) 
      and typecheck_fs :: "kind list \<Rightarrow> type list \<Rightarrow> expr list \<Rightarrow> type list \<Rightarrow> bool" 
    (infix ",_ \<turnstile>\<^sub>f _ :" 60)
      and typecheck_cs :: "kind list \<Rightarrow> type list \<Rightarrow> expr list \<Rightarrow> type list \<Rightarrow> type \<Rightarrow> bool" 
    (infix ",_ \<turnstile>\<^sub>c _ : _ \<rightarrow>" 60) where
  tc_var [simp]: "lookup x \<Gamma> = Some t \<Longrightarrow> \<Delta>,\<Gamma> \<turnstile> Var x : t"
| tc_abs [simp]: "\<Delta>,insert_at 0 t\<^sub>1 \<Gamma> \<turnstile> e : t\<^sub>2 \<Longrightarrow> \<Delta> \<turnstile>\<^sub>k t\<^sub>1 : Star \<Longrightarrow> \<Delta>,\<Gamma> \<turnstile> Abs t\<^sub>1 e : Arrow t\<^sub>1 t\<^sub>2"
| tc_app [simp]: "\<Delta>,\<Gamma> \<turnstile> e\<^sub>1 : Arrow t\<^sub>1 t\<^sub>2 \<Longrightarrow> \<Delta>,\<Gamma> \<turnstile> e\<^sub>2 : t\<^sub>1 \<Longrightarrow> \<Delta>,\<Gamma> \<turnstile> App e\<^sub>1 e\<^sub>2 : t\<^sub>2"
| tc_let [simp]: "\<Delta>,\<Gamma> \<turnstile> e\<^sub>1 : t\<^sub>1 \<Longrightarrow> \<Delta>,insert_at 0 t\<^sub>1 \<Gamma> \<turnstile> e\<^sub>2 : t\<^sub>2 \<Longrightarrow> \<Delta>,\<Gamma> \<turnstile> Let e\<^sub>1 e\<^sub>2 : t\<^sub>2"
| tc_rec [simp]: "\<Delta>,\<Gamma> \<turnstile>\<^sub>f fs : ts \<Longrightarrow> \<Delta>,\<Gamma> \<turnstile> Rec fs : Record ts"
| tc_proj [simp]: "\<Delta>,\<Gamma> \<turnstile> e : Record ts \<Longrightarrow> lookup l ts = Some t \<Longrightarrow> \<Delta>,\<Gamma> \<turnstile> Proj e l : t"
| tc_inj [simp]: "\<Delta>,\<Gamma> \<turnstile> e : t \<Longrightarrow> lookup l ts = Some t \<Longrightarrow> \<forall>tt \<in> set ts. \<Delta> \<turnstile>\<^sub>k tt : Star \<Longrightarrow> 
    \<Delta>,\<Gamma> \<turnstile> Inj l ts e : Variant ts"
| tc_case [simp]: "\<Delta>,\<Gamma> \<turnstile> e : Variant ts \<Longrightarrow> \<Delta>,\<Gamma> \<turnstile>\<^sub>c cs : ts \<rightarrow> t \<Longrightarrow> \<Delta>,\<Gamma> \<turnstile> Case e t cs : t"
| tc_fold [simp]: "\<Delta>,\<Gamma> \<turnstile> e : subst\<^sub>t\<^sub>t 0 (Inductive k t) t \<Longrightarrow> insert_at 0 k \<Delta> \<turnstile>\<^sub>k t : Star \<Longrightarrow> 
    \<Delta>,\<Gamma> \<turnstile> Fold t e : Inductive k t"
| tc_unfold [simp]: "\<Delta>,\<Gamma> \<turnstile> e : Inductive k t \<Longrightarrow> insert_at 0 k \<Delta> \<turnstile>\<^sub>k t : Star \<Longrightarrow> 
    \<Delta>,\<Gamma> \<turnstile> Unfold t e : subst\<^sub>t\<^sub>t 0 (Inductive k t) t"
| tc_tyabs [simp]: "insert_at 0 k \<Delta>,map (incr\<^sub>t\<^sub>t 0) \<Gamma> \<turnstile> e : t \<Longrightarrow> \<Delta>,\<Gamma> \<turnstile> TyAbs k e : Forall k t"
| tc_tyapp [simp]: "\<Delta>,\<Gamma> \<turnstile> e : Forall k t \<Longrightarrow> \<Delta> \<turnstile>\<^sub>k t' : k \<Longrightarrow> \<Delta>,\<Gamma> \<turnstile> TyApp e t' : subst\<^sub>t\<^sub>t 0 t' t"
| tc_tylet [simp]: "\<Delta>,\<Gamma> \<turnstile> subst\<^sub>t\<^sub>e 0 t' e : t \<Longrightarrow> \<Delta> \<turnstile>\<^sub>k t' : k \<Longrightarrow> \<Delta>,\<Gamma> \<turnstile> TyLet t' e : t"
| tcf_nil [simp]: "\<Delta>,\<Gamma> \<turnstile>\<^sub>f [] : []"
| tcf_cons [simp]: "\<Delta>,\<Gamma> \<turnstile> e : t \<Longrightarrow> \<Delta>,\<Gamma> \<turnstile>\<^sub>f fs : ts \<Longrightarrow> \<Delta>,\<Gamma> \<turnstile>\<^sub>f e # fs : t # ts"
| tcc_nil [simp]: "\<Delta>,\<Gamma> \<turnstile>\<^sub>c [] : [] \<rightarrow> t"
| tcc_cons [simp]: "\<Delta>,insert_at 0 t' \<Gamma> \<turnstile> e : t \<Longrightarrow> \<Delta>,\<Gamma> \<turnstile>\<^sub>c cs : ts \<rightarrow> t \<Longrightarrow> 
    \<Delta>,\<Gamma> \<turnstile>\<^sub>c e # cs : t' # ts \<rightarrow> t"

inductive_cases [elim]: "\<Delta>,\<Gamma> \<turnstile> Var x : t"
inductive_cases [elim]: "\<Delta>,\<Gamma> \<turnstile> Abs t\<^sub>1 e : t"
inductive_cases [elim]: "\<Delta>,\<Gamma> \<turnstile> App e\<^sub>1 e\<^sub>2 : t"
inductive_cases [elim]: "\<Delta>,\<Gamma> \<turnstile> Let e\<^sub>1 e\<^sub>2 : t"
inductive_cases [elim]: "\<Delta>,\<Gamma> \<turnstile> Rec fs : t"
inductive_cases [elim]: "\<Delta>,\<Gamma> \<turnstile> Proj e l : t"
inductive_cases [elim]: "\<Delta>,\<Gamma> \<turnstile> Inj e ts l : t"
inductive_cases [elim]: "\<Delta>,\<Gamma> \<turnstile> Case e tt cs : t"
inductive_cases [elim]: "\<Delta>,\<Gamma> \<turnstile> Fold t' e : t"
inductive_cases [elim]: "\<Delta>,\<Gamma> \<turnstile> Unfold t' e : t"
inductive_cases [elim]: "\<Delta>,\<Gamma> \<turnstile> TyAbs k e : t"
inductive_cases [elim]: "\<Delta>,\<Gamma> \<turnstile> TyApp e t' : t"
inductive_cases [elim]: "\<Delta>,\<Gamma> \<turnstile> TyLet t' e : t"
inductive_cases [elim]: "\<Delta>,\<Gamma> \<turnstile>\<^sub>f [] : ts"
inductive_cases [elim]: "\<Delta>,\<Gamma> \<turnstile>\<^sub>f e # fs : ts"
inductive_cases [elim]: "\<Delta>,\<Gamma> \<turnstile>\<^sub>c [] : ts \<rightarrow> t"
inductive_cases [elim]: "\<Delta>,\<Gamma> \<turnstile>\<^sub>c e # cs : ts \<rightarrow> t"

lemma canonical_arrow [simp]: "\<Delta>,\<Gamma> \<turnstile> e : Arrow t\<^sub>1 t\<^sub>2 \<Longrightarrow> is_value e \<Longrightarrow> \<exists>e'. e = Abs t\<^sub>1 e'"
  by (induction \<Gamma> e "Arrow t\<^sub>1 t\<^sub>2" rule: typecheck_typecheck_fs_typecheck_cs.inducts(1)) simp_all

lemma canonical_record [simp]: "\<Delta>,\<Gamma> \<turnstile> e : Record ts \<Longrightarrow> is_value e \<Longrightarrow> 
    \<exists>fs. e = Rec fs \<and> is_value_f fs \<and> \<Delta>,\<Gamma> \<turnstile>\<^sub>f fs : ts"
  by (induction \<Gamma> e "Record ts" rule: typecheck_typecheck_fs_typecheck_cs.inducts(1)) simp_all

lemma canonical_variant [simp]: "\<Delta>,\<Gamma> \<turnstile> e : Variant ts \<Longrightarrow> is_value e \<Longrightarrow> 
    \<exists>l e'. e = Inj l ts e' \<and> is_value e' \<and> l < length ts"
  by (induction \<Gamma> e "Variant ts" rule: typecheck_typecheck_fs_typecheck_cs.inducts(1)) auto

lemma canonical_inductive [simp]: "\<Delta>,\<Gamma> \<turnstile> e : Inductive k t \<Longrightarrow> is_value e \<Longrightarrow> 
    \<exists>e'. e = Fold t e' \<and> is_value e'"
  by (induction \<Gamma> e "Inductive k t" rule: typecheck_typecheck_fs_typecheck_cs.inducts(1)) auto

lemma canonical_forall [simp]: "\<Delta>,\<Gamma> \<turnstile> e : Forall k t \<Longrightarrow> is_value e \<Longrightarrow> \<exists>e'. e = TyAbs k e'"
  by (induction \<Gamma> e "Forall k t" rule: typecheck_typecheck_fs_typecheck_cs.inducts(1)) auto

lemma [simp]: "\<Delta>,\<Gamma> \<turnstile>\<^sub>f fs : ts \<Longrightarrow> lookup l ts = Some t \<Longrightarrow> \<exists>e. lookup l fs = Some e"
  by (induction l fs arbitrary: ts rule: lookup.induct) auto

lemma typecheck_list_append [simp]: "\<Delta>,\<Gamma> \<turnstile>\<^sub>f vs : vts \<Longrightarrow> \<Delta>,\<Gamma> \<turnstile>\<^sub>f nvs : nvts \<Longrightarrow> 
    \<Delta>,\<Gamma> \<turnstile>\<^sub>f vs @ nvs : vts @ nvts"
  by (induction \<Gamma> vs vts rule: typecheck_typecheck_fs_typecheck_cs.inducts(2)) simp_all

lemma [simp]: "subst\<^sub>t\<^sub>e x t (incr\<^sub>t\<^sub>e x e) = e"
  proof (induction e arbitrary: x t)
  case (Rec es)
    thus ?case by (induction es) simp_all
  next case (Case e t cs)
    thus ?case by (induction cs) simp_all
  qed simp_all

lemma [simp]: "y \<le> x \<Longrightarrow> incr\<^sub>t\<^sub>e y (incr\<^sub>t\<^sub>e x e) = incr\<^sub>t\<^sub>e (Suc x) (incr\<^sub>t\<^sub>e y e)"
  by (induction e arbitrary: x y) simp_all

lemma [simp]: "y \<le> x \<Longrightarrow> incr\<^sub>t\<^sub>e x (subst\<^sub>t\<^sub>e y t e) = subst\<^sub>t\<^sub>e y (incr\<^sub>t\<^sub>t x t) (incr\<^sub>t\<^sub>e (Suc x) e)"
  by (induction e arbitrary: x y t) simp_all

lemma [simp]: "y \<le> x \<Longrightarrow> incr\<^sub>t\<^sub>e y (subst\<^sub>t\<^sub>e x t e) = subst\<^sub>t\<^sub>e (Suc x) (incr\<^sub>t\<^sub>t y t) (incr\<^sub>t\<^sub>e y e)"
  by (induction e arbitrary: x y t) simp_all

lemma [simp]: "y \<le> x \<Longrightarrow> subst\<^sub>t\<^sub>e x t\<^sub>1 (subst\<^sub>t\<^sub>e y t\<^sub>2 e) = 
    subst\<^sub>t\<^sub>e y (subst\<^sub>t\<^sub>t x t\<^sub>1 t\<^sub>2) (subst\<^sub>t\<^sub>e (Suc x) (incr\<^sub>t\<^sub>t y t\<^sub>1) e)"
  by (induction e arbitrary: x y t\<^sub>1 t\<^sub>2) simp_all

lemma [simp]: "incr\<^sub>t\<^sub>e x (incr\<^sub>e\<^sub>e y e) = incr\<^sub>e\<^sub>e y (incr\<^sub>t\<^sub>e x e)"
  by (induction e arbitrary: x y) simp_all

lemma [simp]: "subst\<^sub>t\<^sub>e x t (incr\<^sub>e\<^sub>e y e) = incr\<^sub>e\<^sub>e y (subst\<^sub>t\<^sub>e x t e)"
  by (induction e arbitrary: x y t) simp_all

lemma [simp]: "subst\<^sub>e\<^sub>e x e' (subst\<^sub>t\<^sub>e y t e) = subst\<^sub>t\<^sub>e y t (subst\<^sub>e\<^sub>e x (incr\<^sub>t\<^sub>e y e') e)"
  by (induction e arbitrary: x y t e') simp_all

lemma [simp]: "\<Delta>,\<Gamma> \<turnstile> e : t \<Longrightarrow> x \<le> length \<Delta> \<Longrightarrow> 
    insert_at x k \<Delta>,map (incr\<^sub>t\<^sub>t x) \<Gamma> \<turnstile> incr\<^sub>t\<^sub>e x e : incr\<^sub>t\<^sub>t x t"
  and [simp]: "\<Delta>,\<Gamma> \<turnstile>\<^sub>f fs : ts \<Longrightarrow> x \<le> length \<Delta> \<Longrightarrow> 
    insert_at x k \<Delta>,map (incr\<^sub>t\<^sub>t x) \<Gamma> \<turnstile>\<^sub>f map (incr\<^sub>t\<^sub>e x) fs : map (incr\<^sub>t\<^sub>t x) ts"
  and [simp]: "\<Delta>,\<Gamma> \<turnstile>\<^sub>c cs : ts \<rightarrow> t \<Longrightarrow> x \<le> length \<Delta> \<Longrightarrow> 
    insert_at x k \<Delta>,map (incr\<^sub>t\<^sub>t x) \<Gamma> \<turnstile>\<^sub>c map (incr\<^sub>t\<^sub>e x) cs : map (incr\<^sub>t\<^sub>t x) ts \<rightarrow> incr\<^sub>t\<^sub>t x t "
  proof (induction \<Delta> \<Gamma> e t and \<Delta> \<Gamma> fs ts and \<Delta> \<Gamma> cs ts t arbitrary: x and x and x
         rule: typecheck_typecheck_fs_typecheck_cs.inducts) 
  case (tc_app \<Delta> \<Gamma> e\<^sub>1 t\<^sub>1 t\<^sub>2 e\<^sub>2)
    hence "insert_at x k \<Delta>,map (incr\<^sub>t\<^sub>t x) \<Gamma> \<turnstile> incr\<^sub>t\<^sub>e x e\<^sub>1 : Arrow (incr\<^sub>t\<^sub>t x t\<^sub>1) (incr\<^sub>t\<^sub>t x t\<^sub>2)" by simp
    moreover from tc_app have "insert_at x k \<Delta>,map (incr\<^sub>t\<^sub>t x) \<Gamma> \<turnstile> incr\<^sub>t\<^sub>e x e\<^sub>2 : incr\<^sub>t\<^sub>t x t\<^sub>1" by simp
    ultimately show ?case by simp
  next case (tc_let \<Delta> \<Gamma> e\<^sub>1 t\<^sub>1 e\<^sub>2 t\<^sub>2)
    hence "insert_at x k \<Delta>,insert_at 0 (incr\<^sub>t\<^sub>t x t\<^sub>1) (map (incr\<^sub>t\<^sub>t x) \<Gamma>) \<turnstile> incr\<^sub>t\<^sub>e x e\<^sub>2 : incr\<^sub>t\<^sub>t x t\<^sub>2" 
      by simp
    moreover from tc_let have "insert_at x k \<Delta>,map (incr\<^sub>t\<^sub>t x) \<Gamma> \<turnstile> incr\<^sub>t\<^sub>e x e\<^sub>1 : incr\<^sub>t\<^sub>t x t\<^sub>1" by simp
    ultimately show ?case by simp
  next case (tc_proj \<Delta> \<Gamma> e ts l t)
    hence "insert_at x k \<Delta>,map (incr\<^sub>t\<^sub>t x) \<Gamma> \<turnstile> incr\<^sub>t\<^sub>e x e : Record (map (incr\<^sub>t\<^sub>t x) ts)" by simp
    moreover from tc_proj have "lookup l (map (incr\<^sub>t\<^sub>t x) ts) = Some (incr\<^sub>t\<^sub>t x t)" by simp
    ultimately show ?case by simp
  next case (tc_inj \<Delta> \<Gamma> e t l ts)
    hence "insert_at x k \<Delta>,map (incr\<^sub>t\<^sub>t x) \<Gamma> \<turnstile> incr\<^sub>t\<^sub>e x e : incr\<^sub>t\<^sub>t x t" by simp
    moreover from tc_inj have "lookup l (map (incr\<^sub>t\<^sub>t x) ts) = Some (incr\<^sub>t\<^sub>t x t)" by simp
    moreover from tc_inj have "\<forall>tt \<in> set (map (incr\<^sub>t\<^sub>t x) ts). insert_at x k \<Delta> \<turnstile>\<^sub>k tt : Star" by simp
    ultimately show ?case by simp
  next case (tc_case \<Delta> \<Gamma> e ts cs t)
    hence "insert_at x k \<Delta>,map (incr\<^sub>t\<^sub>t x) \<Gamma> \<turnstile> incr\<^sub>t\<^sub>e x e : Variant (map (incr\<^sub>t\<^sub>t x) ts)" by simp
    moreover from tc_case have "insert_at x k \<Delta>,map (incr\<^sub>t\<^sub>t x) \<Gamma> \<turnstile>\<^sub>c map (incr\<^sub>t\<^sub>e x) cs : 
      map (incr\<^sub>t\<^sub>t x) ts \<rightarrow> incr\<^sub>t\<^sub>t x t" by simp
    ultimately show ?case by simp
  next case (tc_fold \<Delta> \<Gamma> e k' t)
    hence "insert_at x k \<Delta>,map (incr\<^sub>t\<^sub>t x) \<Gamma> \<turnstile> incr\<^sub>t\<^sub>e x e : 
      subst\<^sub>t\<^sub>t 0 (incr\<^sub>t\<^sub>t x (Inductive k' t)) (incr\<^sub>t\<^sub>t (Suc x) t)" by (metis le0 subst_incr_swap)
    with tc_fold show ?case by simp
  next case (tc_unfold \<Delta> \<Gamma> e k' t)
    hence "insert_at x k \<Delta>,map (incr\<^sub>t\<^sub>t x) \<Gamma> \<turnstile> Unfold (incr\<^sub>t\<^sub>t (Suc x) t) (incr\<^sub>t\<^sub>e x e) : 
      subst\<^sub>t\<^sub>t 0 (incr\<^sub>t\<^sub>t x (Inductive k' t)) (incr\<^sub>t\<^sub>t (Suc x) t)" by simp
    hence "insert_at x k \<Delta>,map (incr\<^sub>t\<^sub>t x) \<Gamma> \<turnstile> Unfold (incr\<^sub>t\<^sub>t (Suc x) t) (incr\<^sub>t\<^sub>e x e) : 
      incr\<^sub>t\<^sub>t x (subst\<^sub>t\<^sub>t 0 (Inductive k' t) t)" by (metis le0 subst_incr_swap)
    thus ?case by simp
  next case (tc_tyapp \<Delta> \<Gamma> e k' t t')
    hence "insert_at x k \<Delta>,map (incr\<^sub>t\<^sub>t x) \<Gamma> \<turnstile> incr\<^sub>t\<^sub>e x e : Forall k' (incr\<^sub>t\<^sub>t (Suc x) t)" by simp 
    moreover from tc_tyapp have "insert_at x k \<Delta> \<turnstile>\<^sub>k incr\<^sub>t\<^sub>t x t' : k'" by simp
    ultimately have "insert_at x k \<Delta>,map (incr\<^sub>t\<^sub>t x) \<Gamma> \<turnstile> TyApp (incr\<^sub>t\<^sub>e x e) (incr\<^sub>t\<^sub>t x t') : 
      subst\<^sub>t\<^sub>t 0 (incr\<^sub>t\<^sub>t x t') (incr\<^sub>t\<^sub>t (Suc x) t)"
        by (metis typecheck_typecheck_fs_typecheck_cs.tc_tyapp)
    thus ?case by simp
  next case (tc_tylet \<Delta> \<Gamma> t' e t k')
    hence "insert_at x k \<Delta>,map (incr\<^sub>t\<^sub>t x) \<Gamma> \<turnstile> subst\<^sub>t\<^sub>e 0 (incr\<^sub>t\<^sub>t x t') (incr\<^sub>t\<^sub>e (Suc x) e) : incr\<^sub>t\<^sub>t x t" 
      by simp
    moreover from tc_tylet have "insert_at x k \<Delta> \<turnstile>\<^sub>k incr\<^sub>t\<^sub>t x t' : k'" by simp
    ultimately show ?case by simp
  qed simp_all

lemma tc_subst\<^sub>t\<^sub>e [simp]: "insert_at x k \<Delta>,\<Gamma> \<turnstile> e : t \<Longrightarrow> \<Delta> \<turnstile>\<^sub>k t' : k \<Longrightarrow> x \<le> length \<Delta> \<Longrightarrow> 
    \<Delta>,map (subst\<^sub>t\<^sub>t x t') \<Gamma> \<turnstile> subst\<^sub>t\<^sub>e x t' e : subst\<^sub>t\<^sub>t x t' t"
  and [simp]: "insert_at x k \<Delta>,\<Gamma> \<turnstile>\<^sub>f fs : ts \<Longrightarrow> \<Delta> \<turnstile>\<^sub>k t' : k \<Longrightarrow> x \<le> length \<Delta> \<Longrightarrow> 
    \<Delta>,map (subst\<^sub>t\<^sub>t x t') \<Gamma> \<turnstile>\<^sub>f map (subst\<^sub>t\<^sub>e x t') fs : map (subst\<^sub>t\<^sub>t x t') ts"
  and [simp]: "insert_at x k \<Delta>,\<Gamma> \<turnstile>\<^sub>c cs : ts \<rightarrow> t \<Longrightarrow> \<Delta> \<turnstile>\<^sub>k t' : k \<Longrightarrow> x \<le> length \<Delta> \<Longrightarrow> 
    \<Delta>,map (subst\<^sub>t\<^sub>t x t') \<Gamma> \<turnstile>\<^sub>c map (subst\<^sub>t\<^sub>e x t') cs : map (subst\<^sub>t\<^sub>t x t') ts \<rightarrow> subst\<^sub>t\<^sub>t x t' t "
  proof (induction "insert_at x k \<Delta>" \<Gamma> e t and "insert_at x k \<Delta>" \<Gamma> fs ts and "insert_at x k \<Delta>" \<Gamma> cs ts t 
         arbitrary: \<Delta> x t' and \<Delta> x t' and \<Delta> x t'
         rule: typecheck_typecheck_fs_typecheck_cs.inducts) 
  case (tc_inj \<Gamma> e t l ts)
    moreover hence "\<forall>tt \<in> set (map (subst\<^sub>t\<^sub>t x t') ts). \<Delta> \<turnstile>\<^sub>k tt : Star" by fastforce
    ultimately show ?case by fastforce
  next case (tc_tylet \<Gamma> tt e t k)
    hence "\<Delta>,map (subst\<^sub>t\<^sub>t x t') \<Gamma> \<turnstile> subst\<^sub>t\<^sub>e 0 (subst\<^sub>t\<^sub>t x t' tt) (subst\<^sub>t\<^sub>e (Suc x) (incr\<^sub>t\<^sub>t 0 t') e) : 
      subst\<^sub>t\<^sub>t x t' t" by simp
    moreover from tc_tylet have "\<Delta> \<turnstile>\<^sub>k subst\<^sub>t\<^sub>t x t' tt : k" by simp
    ultimately show ?case by simp
  qed fastforce+

lemma [simp]: "\<Delta>,\<Gamma> \<turnstile> e : t \<Longrightarrow> x \<le> length \<Gamma> \<Longrightarrow> \<Delta>,insert_at x t' \<Gamma> \<turnstile> incr\<^sub>e\<^sub>e x e : t"
  and [simp]: "\<Delta>,\<Gamma> \<turnstile>\<^sub>f fs : ts \<Longrightarrow> x \<le> length \<Gamma> \<Longrightarrow> \<Delta>,insert_at x t' \<Gamma> \<turnstile>\<^sub>f map (incr\<^sub>e\<^sub>e x) fs : ts"
  and [simp]: "\<Delta>,\<Gamma> \<turnstile>\<^sub>c cs : ts \<rightarrow> t \<Longrightarrow> x \<le> length \<Gamma> \<Longrightarrow> 
    \<Delta>,insert_at x t' \<Gamma> \<turnstile>\<^sub>c map (incr\<^sub>e\<^sub>e (Suc x)) cs : ts \<rightarrow> t"
  proof (induction \<Delta> \<Gamma> e t and \<Delta> \<Gamma> fs ts and \<Delta> \<Gamma> cs ts t arbitrary: x t' and x t' and x t'
         rule: typecheck_typecheck_fs_typecheck_cs.inducts) 
  case (tc_app \<Delta> \<Gamma> e\<^sub>1 t\<^sub>1 t\<^sub>2 e\<^sub>2)
    hence "\<Delta>,insert_at x t' \<Gamma> \<turnstile> incr\<^sub>e\<^sub>e x e\<^sub>1 : Arrow t\<^sub>1 t\<^sub>2" by simp
    moreover from tc_app have "\<Delta>,insert_at x t' \<Gamma> \<turnstile> incr\<^sub>e\<^sub>e x e\<^sub>2 : t\<^sub>1" by simp
    ultimately show ?case by simp
  next case (tc_let \<Delta> \<Gamma> e\<^sub>1 t\<^sub>1 e\<^sub>2 t\<^sub>2)
    hence "\<Delta>,insert_at 0 t\<^sub>1 (insert_at x t' \<Gamma>) \<turnstile> incr\<^sub>e\<^sub>e (Suc x) e\<^sub>2 : t\<^sub>2" by simp
    moreover from tc_let have "\<Delta>,insert_at x t' \<Gamma> \<turnstile> incr\<^sub>e\<^sub>e x e\<^sub>1 : t\<^sub>1" by simp
    ultimately show ?case by simp
  next case (tc_proj \<Delta> \<Gamma> e ts l t)
    hence "\<Delta>,insert_at x t' \<Gamma> \<turnstile> incr\<^sub>e\<^sub>e x e : Record ts" by simp
    moreover from tc_proj have "lookup l ts = Some t" by simp
    ultimately show ?case by simp
  next case (tc_inj \<Delta> \<Gamma> e t l ts)
    hence "\<Delta>,insert_at x t' \<Gamma> \<turnstile> incr\<^sub>e\<^sub>e x e : t" by simp
    moreover from tc_inj have "lookup l ts = Some t" by simp
    moreover from tc_inj have "\<forall>tt \<in> set ts. \<Delta> \<turnstile>\<^sub>k tt : Star" by simp
    ultimately show ?case by simp
  next case (tc_case \<Delta> \<Gamma> e ts cs t)
    hence "\<Delta>,insert_at x t' \<Gamma> \<turnstile> incr\<^sub>e\<^sub>e x e : Variant ts " by simp
    moreover from tc_case have "\<Delta>,insert_at x t' \<Gamma> \<turnstile>\<^sub>c map (incr\<^sub>e\<^sub>e (Suc x)) cs : ts \<rightarrow> t" by simp
    ultimately show ?case by simp
  next case (tc_tyapp \<Delta> \<Gamma> e k t tt)
    moreover hence "\<Delta>,insert_at x t' \<Gamma> \<turnstile> incr\<^sub>e\<^sub>e x e : Forall k t" by simp 
    ultimately show ?case by fastforce
  qed simp_all

lemma [simp]: "\<Delta>,insert_at x t' \<Gamma> \<turnstile> e : t \<Longrightarrow> x \<le> length \<Gamma> \<Longrightarrow> \<Delta>,\<Gamma> \<turnstile> e' : t' \<Longrightarrow> 
    \<Delta>,\<Gamma> \<turnstile> subst\<^sub>e\<^sub>e x e' e : t"
  and [simp]: "\<Delta>,insert_at x t' \<Gamma> \<turnstile>\<^sub>f fs : ts \<Longrightarrow> x \<le> length \<Gamma> \<Longrightarrow> \<Delta>,\<Gamma> \<turnstile> e' : t' \<Longrightarrow> 
    \<Delta>,\<Gamma> \<turnstile>\<^sub>f map (subst\<^sub>e\<^sub>e x e') fs : ts"
  and [simp]: "\<Delta>,insert_at x t' \<Gamma> \<turnstile>\<^sub>c fs : ts \<rightarrow> t \<Longrightarrow> x \<le> length \<Gamma> \<Longrightarrow> \<Delta>,\<Gamma> \<turnstile> e' : t' \<Longrightarrow> 
    \<Delta>,\<Gamma> \<turnstile>\<^sub>c map (subst\<^sub>e\<^sub>e (Suc x) (incr\<^sub>e\<^sub>e 0 e')) fs : ts \<rightarrow> t "
  proof (induction \<Delta> "insert_at x t' \<Gamma>" e t and \<Delta> "insert_at x t' \<Gamma>" fs ts 
               and \<Delta> "insert_at x t' \<Gamma>" fs ts t 
         arbitrary: \<Gamma> x e' t' and \<Gamma> x e' t' and \<Gamma> x e' t'
         rule: typecheck_typecheck_fs_typecheck_cs.inducts)
  case (tc_var y t)
    thus ?case by (cases y) auto
  qed fastforce+

lemma [elim]: "\<Delta>,\<Gamma> \<turnstile>\<^sub>f fs : ts \<Longrightarrow> lookup l fs = Some e \<Longrightarrow> lookup l ts = Some t \<Longrightarrow> \<Delta>,\<Gamma> \<turnstile> e : t" 
  by (induction l fs arbitrary: ts rule: lookup.induct) auto

lemma [elim]: "\<Delta>,\<Gamma> \<turnstile>\<^sub>c cs : ts \<rightarrow> t \<Longrightarrow> lookup l cs = Some e \<Longrightarrow> lookup l ts = Some t' \<Longrightarrow> 
    \<Delta>,insert_at 0 t' \<Gamma> \<turnstile> e : t" 
  by (induction l cs arbitrary: ts rule: lookup.induct) auto

end