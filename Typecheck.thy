theory Typecheck
imports Vector Expression
begin

inductive typecheck :: "type list \<Rightarrow> expr \<Rightarrow> type \<Rightarrow> bool" (infix "\<turnstile> _ :" 60) 
      and typecheck_fs :: "type list \<Rightarrow> expr list \<Rightarrow> type list \<Rightarrow> bool" (infix "\<turnstile>\<^sub>f _ :" 60)
      and typecheck_cs :: "type list \<Rightarrow> expr list \<Rightarrow> type list \<Rightarrow> type \<Rightarrow> bool" 
    (infix "\<turnstile>\<^sub>c _ : _ \<rightarrow>" 60) where
  tc_var [simp]: "lookup x \<Gamma> = Some t \<Longrightarrow> \<Gamma> \<turnstile> Var x : t"
| tc_abs [simp]: "t\<^sub>1 # \<Gamma> \<turnstile> e : t\<^sub>2 \<Longrightarrow> \<Gamma> \<turnstile> Abs t\<^sub>1 e : Arrow t\<^sub>1 t\<^sub>2"
| tc_app [simp]: "\<Gamma> \<turnstile> e\<^sub>1 : Arrow t\<^sub>1 t\<^sub>2 \<Longrightarrow> \<Gamma> \<turnstile> e\<^sub>2 : t\<^sub>1 \<Longrightarrow> \<Gamma> \<turnstile> App e\<^sub>1 e\<^sub>2 : t\<^sub>2"
| tc_rec [simp]: "\<Gamma> \<turnstile>\<^sub>f fs : ts \<Longrightarrow> \<Gamma> \<turnstile> Rec fs : Record ts"
| tc_proj [simp]: "\<Gamma> \<turnstile> e : Record ts \<Longrightarrow> lookup l ts = Some t \<Longrightarrow> \<Gamma> \<turnstile> Proj e l : t"
| tc_inj [simp]: "\<Gamma> \<turnstile> e : t \<Longrightarrow> lookup l ts = Some t \<Longrightarrow> \<Gamma> \<turnstile> Inj l ts e : Variant ts"
| tc_case [simp]: "\<Gamma> \<turnstile> e : Variant ts \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>c cs : ts \<rightarrow> t \<Longrightarrow> \<Gamma> \<turnstile> Case e cs : t"
| tcf_nil [simp]: "\<Gamma> \<turnstile>\<^sub>f [] : []"
| tcf_cons [simp]: "\<Gamma> \<turnstile> e : t \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>f fs : ts \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>f e # fs : t # ts"
| tcc_nil [simp]: "\<Gamma> \<turnstile>\<^sub>c [] : [] \<rightarrow> t"
| tcc_cons [simp]: "t' # \<Gamma> \<turnstile> e : t \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>c fs : ts \<rightarrow> t \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>c e # fs : t' # ts \<rightarrow> t"

inductive_cases [elim]: "\<Gamma> \<turnstile> Var x : t"
inductive_cases [elim]: "\<Gamma> \<turnstile> Abs t\<^sub>1 e : t"
inductive_cases [elim]: "\<Gamma> \<turnstile> App e\<^sub>1 e\<^sub>2 : t"
inductive_cases [elim]: "\<Gamma> \<turnstile> Rec fs : t"
inductive_cases [elim]: "\<Gamma> \<turnstile> Proj e l : t"
inductive_cases [elim]: "\<Gamma> \<turnstile> Inj e ts l : t"
inductive_cases [elim]: "\<Gamma> \<turnstile> Case e cs : t"
inductive_cases [elim]: "\<Gamma> \<turnstile>\<^sub>f [] : ts"
inductive_cases [elim]: "\<Gamma> \<turnstile>\<^sub>f e # fs : ts"
inductive_cases [elim]: "\<Gamma> \<turnstile>\<^sub>c [] : ts \<rightarrow> t"
inductive_cases [elim]: "\<Gamma> \<turnstile>\<^sub>c e # cs : ts \<rightarrow> t"

lemma canonical_arrow [simp]: "\<Gamma> \<turnstile> e : Arrow t\<^sub>1 t\<^sub>2 \<Longrightarrow> is_value e \<Longrightarrow> \<exists>e'. e = Abs t\<^sub>1 e'"
  by (induction \<Gamma> e "Arrow t\<^sub>1 t\<^sub>2" rule: typecheck_typecheck_fs_typecheck_cs.inducts(1)) simp_all

lemma canonical_record [simp]: "\<Gamma> \<turnstile> e : Record ts \<Longrightarrow> is_value e \<Longrightarrow> 
    \<exists>fs. e = Rec fs \<and> is_value_f fs"
  by (induction \<Gamma> e "Record ts" rule: typecheck_typecheck_fs_typecheck_cs.inducts(1)) simp_all

lemma canonical_variant [simp]: "\<Gamma> \<turnstile> e : Variant ts \<Longrightarrow> is_value e \<Longrightarrow> 
    \<exists>l e'. e = Inj l ts e' \<and> is_value e' \<and> l < length ts"
  by (induction \<Gamma> e "Variant ts" rule: typecheck_typecheck_fs_typecheck_cs.inducts(1)) auto

lemma [simp]: "\<Gamma> \<turnstile>\<^sub>f fs : ts \<Longrightarrow> lookup l ts = Some t \<Longrightarrow> \<exists>e. lookup l fs = Some e"
  by (induction l fs arbitrary: ts rule: lookup.induct) auto

lemma [simp]: "\<Gamma> \<turnstile>\<^sub>f vs : vts \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>f nvs : nvts \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>f vs @ nvs : vts @ nvts"
  by (induction \<Gamma> vs vts rule: typecheck_typecheck_fs_typecheck_cs.inducts(2)) simp_all

lemma [simp]: "\<Gamma> \<turnstile> e : t \<Longrightarrow> x \<le> length \<Gamma> \<Longrightarrow> insert_at x t' \<Gamma> \<turnstile> incr x e : t"
  and [simp]: "\<Gamma> \<turnstile>\<^sub>f fs : ts \<Longrightarrow> x \<le> length \<Gamma> \<Longrightarrow> insert_at x t' \<Gamma> \<turnstile>\<^sub>f map (incr x) fs : ts"
  and [simp]: "\<Gamma> \<turnstile>\<^sub>c fs : ts \<rightarrow> t \<Longrightarrow> x \<le> length \<Gamma> \<Longrightarrow> 
    insert_at x t' \<Gamma> \<turnstile>\<^sub>c map (incr (Suc x)) fs : ts \<rightarrow> t"
  by (induction \<Gamma> e t and \<Gamma> fs ts and \<Gamma> fs ts t arbitrary: x and x and x 
      rule: typecheck_typecheck_fs_typecheck_cs.inducts) 
     fastforce+

lemma [simp]: "insert_at x t' \<Gamma> \<turnstile> e : t \<Longrightarrow> x \<le> length \<Gamma> \<Longrightarrow> \<Gamma> \<turnstile> e' : t' \<Longrightarrow> \<Gamma> \<turnstile> subst x e' e : t"
  and [simp]: "insert_at x t' \<Gamma> \<turnstile>\<^sub>f fs : ts \<Longrightarrow> x \<le> length \<Gamma> \<Longrightarrow> \<Gamma> \<turnstile> e' : t' \<Longrightarrow> 
    \<Gamma> \<turnstile>\<^sub>f map (subst x e') fs : ts"
  and [simp]: "insert_at x t' \<Gamma> \<turnstile>\<^sub>c fs : ts \<rightarrow> t \<Longrightarrow> x \<le> length \<Gamma> \<Longrightarrow> \<Gamma> \<turnstile> e' : t' \<Longrightarrow> 
    \<Gamma> \<turnstile>\<^sub>c map (subst (Suc x) (incr 0 e')) fs : ts \<rightarrow> t "
  proof (induction "insert_at x t' \<Gamma>" e t and "insert_at x t' \<Gamma>" fs ts and "insert_at x t' \<Gamma>" fs ts t 
         arbitrary: \<Gamma> x e' and \<Gamma> x e' and \<Gamma> x e'
         rule: typecheck_typecheck_fs_typecheck_cs.inducts)
  case (tc_var y t)
    thus ?case by (cases y) auto
  next case (tc_abs t\<^sub>1 e t\<^sub>2)
    moreover hence "insert_at 0 t\<^sub>1 \<Gamma> \<turnstile> incr 0 e' : t'" by (simp del: insert_at.simps(1))
    ultimately show ?case by simp
  next case (tcc_cons tt e t fs ts)
    moreover hence "insert_at 0 tt \<Gamma> \<turnstile> incr 0 e' : t'" by (simp del: insert_at.simps(1))
    ultimately show ?case by simp
  qed fastforce+

lemma [elim]: "\<Gamma> \<turnstile>\<^sub>f fs : ts \<Longrightarrow> lookup l fs = Some e \<Longrightarrow> lookup l ts = Some t \<Longrightarrow> \<Gamma> \<turnstile> e : t" 
  by (induction l fs arbitrary: ts rule: lookup.induct) auto

lemma [elim]: "\<Gamma> \<turnstile>\<^sub>c cs : ts \<rightarrow> t \<Longrightarrow> lookup l cs = Some e \<Longrightarrow> lookup l ts = Some t' \<Longrightarrow> 
    t' # \<Gamma> \<turnstile> e : t" 
  by (induction l cs arbitrary: ts rule: lookup.induct) auto

end