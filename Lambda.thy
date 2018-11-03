theory Lambda
imports Main
begin

fun insert_at :: "nat \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "insert_at 0 a' as = a' # as"
| "insert_at (Suc x) a' [] = undefined"
| "insert_at (Suc x) a' (a # as) = a # insert_at x a' as"

fun lookup :: "nat \<Rightarrow> 'a list \<Rightarrow> 'a option" where
  "lookup x [] = None"
| "lookup 0 (a # as) = Some a"
| "lookup (Suc x) (a # as) = lookup x as"

fun lookup_assoc :: "'k \<Rightarrow> ('k \<times> 'v) list \<Rightarrow> 'v option" where
  "lookup_assoc k [] = None"
| "lookup_assoc k ((k', v) # as) = (if k = k' then Some v else lookup_assoc k as)"

fun keys :: "('k \<times> 'v) list \<Rightarrow> 'k set" where
  "keys [] = {}"
| "keys ((k, v) # as) = insert k (keys as)"

lemma [simp]: "x \<le> length as \<Longrightarrow> length (insert_at x a as) = Suc (length as)"
  by (induction x a as rule: insert_at.induct) simp_all

lemma [simp]: "x \<le> length as \<Longrightarrow> lookup x (insert_at x a as) = Some a"
  by (induction x a as rule: insert_at.induct) simp_all

lemma [simp]: "x \<le> length as \<Longrightarrow> y < x \<Longrightarrow> lookup y (insert_at x a as) = lookup y as"
  proof (induction x a as arbitrary: y rule: insert_at.induct)
  case 3
    thus ?case by (induction y) simp_all
  qed simp_all

lemma [simp]: "x \<le> length as \<Longrightarrow> x \<le> y \<Longrightarrow> lookup (Suc y) (insert_at x a as) = lookup y as"
  proof (induction x a as arbitrary: y rule: insert_at.induct)
  case 3
    thus ?case by (induction y) simp_all
  qed simp_all

lemma [simp]: "keys (as @ bs) = keys as \<union> keys bs"
  by (induction as rule: keys.induct) simp_all

(* syntax *)

typedecl label

datatype type = 
  Base
| Arrow type type
| Record "(label \<times> type) list"

datatype expr = 
  Var nat
| Abs type expr
| App expr expr
| Rec "(label \<times> expr) list"
| Proj expr label

fun incr :: "nat \<Rightarrow> expr \<Rightarrow> expr"
and incr_fs :: "nat \<Rightarrow> (label \<times> expr) list \<Rightarrow> (label \<times> expr) list" where
  "incr x (Var y) = Var (if x \<le> y then Suc y else y)"
| "incr x (Abs t e) = Abs t (incr (Suc x) e)"
| "incr x (App e\<^sub>1 e\<^sub>2) = App (incr x e\<^sub>1) (incr x e\<^sub>2)"
| "incr x (Rec fs) = Rec (incr_fs x fs)"
| "incr x (Proj e l) = Proj (incr x e) l"
| "incr_fs x [] = []"
| "incr_fs x ((l, e) # fs) = (l, incr x e) # incr_fs x fs"

fun subst :: "nat \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr" 
and subst_fs :: "nat \<Rightarrow> expr \<Rightarrow> (label \<times> expr) list \<Rightarrow> (label \<times> expr) list" where
  "subst x e' (Var y) = (if x = y then e' else Var (if x < y then y - 1 else y))"
| "subst x e' (Abs t e) = Abs t (subst (Suc x) (incr 0 e') e)"
| "subst x e' (App e\<^sub>1 e\<^sub>2) = App (subst x e' e\<^sub>1) (subst x e' e\<^sub>2)"
| "subst x e' (Rec fs) = Rec (subst_fs x e' fs)"
| "subst x e' (Proj e l) = Proj (subst x e' e) l"
| "subst_fs x e' [] = []"
| "subst_fs x e' ((l, e) # fs) = (l, subst x e' e) # subst_fs x e' fs"

fun is_value :: "expr \<Rightarrow> bool" 
and is_value_f :: "(label \<times> expr) list \<Rightarrow> bool" where
  "is_value (Var y) = False"
| "is_value (Abs t e) = True"
| "is_value (App e\<^sub>1 e\<^sub>2) = False"
| "is_value (Rec fs) = is_value_f fs"
| "is_value (Proj e l) = False"
| "is_value_f [] = True"
| "is_value_f ((l, e) # fs) = (is_value e \<and> is_value_f fs)"

(* typechecking *)

inductive typecheck :: "type list \<Rightarrow> expr \<Rightarrow> type \<Rightarrow> bool" (infix "\<turnstile> _ :" 60) 
      and typecheck_fs :: "type list \<Rightarrow> (label \<times> expr) list \<Rightarrow> (label \<times> type) list \<Rightarrow> bool" 
        (infix "\<turnstile>\<^sub>f _ :" 60) where
  tc_var [simp]: "lookup x \<Gamma> = Some t \<Longrightarrow> \<Gamma> \<turnstile> Var x : t"
| tc_abs [simp]: "t\<^sub>1 # \<Gamma> \<turnstile> e : t\<^sub>2 \<Longrightarrow> \<Gamma> \<turnstile> Abs t\<^sub>1 e : Arrow t\<^sub>1 t\<^sub>2"
| tc_app [simp]: "\<Gamma> \<turnstile> e\<^sub>1 : Arrow t\<^sub>1 t\<^sub>2 \<Longrightarrow> \<Gamma> \<turnstile> e\<^sub>2 : t\<^sub>1 \<Longrightarrow> \<Gamma> \<turnstile> App e\<^sub>1 e\<^sub>2 : t\<^sub>2"
| tc_rec [simp]: "\<Gamma> \<turnstile>\<^sub>f fs : ts \<Longrightarrow> \<Gamma> \<turnstile> Rec fs : Record ts"
| tc_proj [simp]: "\<Gamma> \<turnstile> e : Record ts \<Longrightarrow> lookup_assoc l ts = Some t \<Longrightarrow> \<Gamma> \<turnstile> Proj e l : t"
| tcf_nil [simp]: "\<Gamma> \<turnstile>\<^sub>f [] : []"
| tcf_cons [simp]: "\<Gamma> \<turnstile> e : t \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>f fs : ts \<Longrightarrow> l \<notin> keys fs \<Longrightarrow> 
    \<Gamma> \<turnstile>\<^sub>f (l, e) # fs : (l, t) # ts"

inductive_cases [elim]: "\<Gamma> \<turnstile> Var x : t"
inductive_cases [elim]: "\<Gamma> \<turnstile> Abs t\<^sub>1 e : t"
inductive_cases [elim]: "\<Gamma> \<turnstile> App e\<^sub>1 e\<^sub>2 : t"
inductive_cases [elim]: "\<Gamma> \<turnstile> Rec fs : t"
inductive_cases [elim]: "\<Gamma> \<turnstile> Proj e l : t"
inductive_cases [elim]: "\<Gamma> \<turnstile>\<^sub>f [] : ts"
inductive_cases [elim]: "\<Gamma> \<turnstile>\<^sub>f (l, e) # fs : ts"

(* evaluation *)

datatype stack = 
  SApp1 expr
| SApp2 expr
| SRec "(label \<times> expr) list" label "(label \<times> expr) list" 
| SProj label

inductive typecheck_stack :: "type list \<Rightarrow> stack list \<Rightarrow> type \<Rightarrow> type \<Rightarrow> bool" 
    (infix "\<turnstile> _ : _ \<rightarrow>" 60) where
  tc_hole [simp]: "\<Gamma> \<turnstile> [] : t \<rightarrow> t"
| tc_sapp1 [simp]: "\<Gamma> \<turnstile> s : t \<rightarrow> Arrow t\<^sub>1 t\<^sub>2 \<Longrightarrow> \<Gamma> \<turnstile> e : t\<^sub>1 \<Longrightarrow> \<Gamma> \<turnstile> SApp1 e # s : t \<rightarrow> t\<^sub>2"
| tc_sapp2 [simp]: "\<Gamma> \<turnstile> e : Arrow t\<^sub>1 t\<^sub>2 \<Longrightarrow> \<Gamma> \<turnstile> s : t \<rightarrow> t\<^sub>1 \<Longrightarrow> \<Gamma> \<turnstile> SApp2 e # s : t \<rightarrow> t\<^sub>2"
| tc_srec [simp]: "\<Gamma> \<turnstile>\<^sub>f vs : vts \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>f nvs : nvts \<Longrightarrow> \<Gamma> \<turnstile> s : t \<rightarrow> t' \<Longrightarrow> 
    keys vs \<inter> keys nvs = {} \<Longrightarrow> l \<notin> keys vs \<Longrightarrow> l \<notin> keys nvs \<Longrightarrow> 
      \<Gamma> \<turnstile> SRec vs l nvs # s : t \<rightarrow> Record (vts @ [(l, t')] @ nvts)"
| tc_sproj [simp]: "\<Gamma> \<turnstile> s : t \<rightarrow> Record ts \<Longrightarrow> lookup_assoc l ts = Some t' \<Longrightarrow> 
    \<Gamma> \<turnstile> SProj l # s : t \<rightarrow> t'"

fun stack_extend :: "stack \<Rightarrow> stack list \<times> expr \<Rightarrow> stack list \<times> expr" where
  "stack_extend s' se = (case se of (s, e) \<Rightarrow> (s' # s, e))"

fun unfold :: "expr \<Rightarrow> stack list \<times> expr" 
and unfold_f :: "(label \<times> expr) list \<Rightarrow> 
      (label \<times> expr) list \<times> label \<times> (label \<times> expr) list \<times> stack list \<times> expr" where
  "unfold (Var y) = ([], Var y)"
| "unfold (Abs t e) = ([], Abs t e)"
| "unfold (App e\<^sub>1 e\<^sub>2) = (
    if is_value e\<^sub>1
    then if is_value e\<^sub>2
         then ([], App e\<^sub>1 e\<^sub>2)
         else stack_extend (SApp2 e\<^sub>1) (unfold e\<^sub>2)
    else stack_extend (SApp1 e\<^sub>2) (unfold e\<^sub>1))"
| "unfold (Rec fs) = (
    if is_value_f fs 
    then ([], Rec fs) 
    else case unfold_f fs of (vs, l, nvs, s, e) \<Rightarrow> (SRec vs l nvs # s, e))"
| "unfold (Proj e l) = (
    if is_value e 
    then ([], Proj e l) 
    else stack_extend (SProj l) (unfold e))"
| "unfold_f [] = undefined"
| "unfold_f ((l, e) # fs) = (
    if is_value e
    then case unfold_f fs of (vs, l', nvs, s, e') \<Rightarrow> ((l, e) # vs, l', nvs, s, e')
    else ([], l, fs, unfold e))"

fun fold :: "stack list \<Rightarrow> expr \<Rightarrow> expr" where
  "fold [] e = e"
| "fold (SApp1 e' # s) e = App (fold s e) e'"
| "fold (SApp2 e' # s) e = App e' (fold s e)"
| "fold (SRec vs l nvs # s) e = Rec (vs @ [(l, fold s e)] @ nvs)"
| "fold (SProj l # s) e = Proj (fold s e) l"

inductive reduce :: "expr \<Rightarrow> expr \<Rightarrow> bool" (infix "\<leadsto>\<^sub>\<beta>" 60) where
  ev_beta [simp]: "is_value e\<^sub>2 \<Longrightarrow> App (Abs t e\<^sub>1) e\<^sub>2 \<leadsto>\<^sub>\<beta> subst 0 e\<^sub>2 e\<^sub>1" 
| ev_proj [simp]: "is_value_f fs \<Longrightarrow> lookup_assoc l fs = Some e \<Longrightarrow> Proj (Rec fs) l \<leadsto>\<^sub>\<beta> e" 

inductive evaluate :: "expr \<Rightarrow> expr \<Rightarrow> bool" (infix "\<leadsto>" 60) where
  ev_stack [simp]: "unfold e = (s, r) \<Longrightarrow> r \<leadsto>\<^sub>\<beta> r' \<Longrightarrow> e \<leadsto> fold s r'"

inductive_cases [elim]: "e \<leadsto> e'"

(* safety *)

lemma [simp]: "unfold e = (s, e') \<Longrightarrow> fold s e' = e"
  and [simp]: "unfold_f fs = (vs, l, nvs, s, e') \<Longrightarrow> \<not> is_value_f fs \<Longrightarrow> 
    vs @ [(l, fold s e')] @ nvs = fs"
  by (induction e and fs arbitrary: s e' and vs l nvs s e' rule: unfold_unfold_f.induct) 
     (auto split: if_splits prod.splits)

lemma canonical_arrow [simp]: "\<Gamma> \<turnstile> e : Arrow t\<^sub>1 t\<^sub>2 \<Longrightarrow> is_value e \<Longrightarrow> \<exists>e'. e = Abs t\<^sub>1 e'"
  by (induction \<Gamma> e "Arrow t\<^sub>1 t\<^sub>2" rule: typecheck_typecheck_fs.inducts(1)) simp_all

lemma canonical_record [simp]: "\<Gamma> \<turnstile> e : Record ts \<Longrightarrow> is_value e \<Longrightarrow> 
    \<exists>fs. e = Rec fs \<and> is_value_f fs \<and> \<Gamma> \<turnstile>\<^sub>f fs : ts"
  by (induction \<Gamma> e "Record ts" rule: typecheck_typecheck_fs.inducts(1)) simp_all

lemma [simp]: "\<Gamma> \<turnstile>\<^sub>f fs : ts \<Longrightarrow> lookup_assoc l ts = Some t \<Longrightarrow> \<exists>e. lookup_assoc l fs = Some e"
  by (induction \<Gamma> fs ts rule: typecheck_typecheck_fs.inducts(2)) (simp, simp_all split: if_splits)

theorem progress: "[] \<turnstile> e : t \<Longrightarrow> is_value e \<or> (\<exists>e'. e \<leadsto> e')"
    and "[] \<turnstile>\<^sub>f fs : ts \<Longrightarrow> \<not> is_value_f fs \<Longrightarrow> unfold_f fs = (vs, lr, nvs, s, r) \<Longrightarrow> \<exists>r'. r \<leadsto>\<^sub>\<beta> r'"
  proof (induction "[] :: type list" e t and "[] :: type list" fs ts arbitrary: and vs lr nvs s r 
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
        then obtain vs l nvs s e where X: "unfold (Rec fs) = (SRec vs l nvs # s, e)" 
          by (cases "unfold_f fs") simp_all
        with False tc_rec obtain e' where "e \<leadsto>\<^sub>\<beta> e'" by (cases "unfold_f fs") fastforce+
        with X have "Rec fs \<leadsto> fold (SRec vs l nvs # s) e'" using ev_stack by fastforce
        thus ?thesis by fastforce
      qed simp_all
  next case (tc_proj e ts l t)
    thus ?case 
      proof (cases "is_value e")
      case True
        with tc_proj obtain fs where E: "e = Rec fs \<and> is_value_f fs \<and> [] \<turnstile>\<^sub>f fs : ts" by fastforce
        hence X: "unfold (Proj (Rec fs) l) = ([], Proj (Rec fs) l)" by simp
        from tc_proj E obtain e' where "lookup_assoc l fs = Some e'" by fastforce
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

lemma [simp]: "\<Gamma> \<turnstile>\<^sub>f fs : ts \<Longrightarrow> keys ts = keys fs"
  by (induction \<Gamma> fs ts rule: typecheck_typecheck_fs.inducts(2)) simp_all

lemma [simp]: "\<Gamma> \<turnstile> e : t \<Longrightarrow> unfold e = (s, e') \<Longrightarrow> \<exists>t'. (\<Gamma> \<turnstile> s : t' \<rightarrow> t) \<and> (\<Gamma> \<turnstile> e' : t')"
  and [simp]: "\<Gamma> \<turnstile>\<^sub>f fs : ts \<Longrightarrow> \<not> is_value_f fs \<Longrightarrow> unfold_f fs = (vs, l, nvs, s, e') \<Longrightarrow> 
    \<exists>t t' vts nvts. lookup_assoc l ts = Some t \<and> ts = vts @ [(l, t)] @ nvts \<and> 
      keys vs \<inter> keys nvs = {} \<and> l \<notin> keys vs \<and> l \<notin> keys nvs \<and> 
        keys fs = insert l (keys vs \<union> keys nvs) \<and> (\<Gamma> \<turnstile> s : t' \<rightarrow> t) \<and> (\<Gamma> \<turnstile> e' : t') \<and> 
          (\<Gamma> \<turnstile>\<^sub>f vs : vts) \<and> (\<Gamma> \<turnstile>\<^sub>f nvs : nvts)"
  proof (induction \<Gamma> e t and \<Gamma> fs ts arbitrary: s and vs l nvs s 
         rule: typecheck_typecheck_fs.inducts)
  case (tc_var x \<Gamma> t)
    moreover hence "\<Gamma> \<turnstile> Var x : t" by auto
    ultimately show ?case by force
  next case (tc_app \<Gamma> e\<^sub>1 t\<^sub>1 t\<^sub>2 e\<^sub>2)
    thus ?case 
      proof (cases "is_value e\<^sub>1")
      case True note T = True
        thus ?thesis
          proof (cases "is_value e\<^sub>2")
          case True
            from tc_app have "\<Gamma> \<turnstile> App e\<^sub>1 e\<^sub>2 : t\<^sub>2" by simp
            with tc_app T True show ?thesis by force
          next case False
            with tc_app True obtain s\<^sub>2 where "unfold e\<^sub>2 = (s\<^sub>2, e') \<and> s = SApp2 e\<^sub>1 # s\<^sub>2" 
              by (auto split: prod.splits)
            moreover with tc_app obtain t' where "(\<Gamma> \<turnstile> s\<^sub>2 : t' \<rightarrow> t\<^sub>1) \<and> \<Gamma> \<turnstile> e' : t'" by fastforce
            moreover with tc_app have "\<Gamma> \<turnstile> SApp2 e\<^sub>1 # s\<^sub>2 : t' \<rightarrow> t\<^sub>2" by simp
            ultimately show ?thesis by fastforce
          qed
      next case False
        with tc_app obtain s\<^sub>1 where "unfold e\<^sub>1 = (s\<^sub>1, e') \<and> s = SApp1 e\<^sub>2 # s\<^sub>1" 
          by (auto split: prod.splits)
        moreover with tc_app obtain t' where "(\<Gamma> \<turnstile> s\<^sub>1 : t' \<rightarrow> Arrow t\<^sub>1 t\<^sub>2) \<and> \<Gamma> \<turnstile> e' : t'" 
          by fastforce
        moreover with tc_app have "\<Gamma> \<turnstile> SApp1 e\<^sub>2 # s\<^sub>1 : t' \<rightarrow> t\<^sub>2" by fastforce
        ultimately show ?thesis by fastforce
      qed
  next case (tc_abs t\<^sub>1 \<Gamma> e t\<^sub>2)
    moreover hence "\<Gamma> \<turnstile> Abs t\<^sub>1 e : Arrow t\<^sub>1 t\<^sub>2" by auto
    ultimately show ?case by force
  next case (tc_rec \<Gamma> fs ts)
    thus ?case 
      proof (cases "is_value_f fs")
      case True
        moreover with tc_rec have "\<Gamma> \<turnstile> s : Record ts \<rightarrow> Record ts" by simp
        moreover from tc_rec True have "\<Gamma> \<turnstile> e' : Record ts" by fastforce
        ultimately show ?thesis by blast
      next case False
        then obtain vs l nvs ss ee' where F: "unfold_f fs = (vs, l, nvs, ss, ee')" 
          by (cases "unfold_f fs") simp_all
        with tc_rec False obtain t t' vts nvts where T: "lookup_assoc l ts = Some t \<and> 
          ts = vts @ [(l, t)] @ nvts \<and> keys vs \<inter> keys nvs = {} \<and> l \<notin> keys vs \<and> l \<notin> keys nvs \<and> 
            (\<Gamma> \<turnstile> ss : t' \<rightarrow> t) \<and> (\<Gamma> \<turnstile> e' : t') \<and> (\<Gamma> \<turnstile>\<^sub>f vs : vts) \<and> \<Gamma> \<turnstile>\<^sub>f nvs : nvts" by fastforce
        hence "\<Gamma> \<turnstile> SRec vs l nvs # ss : t' \<rightarrow> Record ts" using tc_srec by fastforce
        with tc_rec False F T show ?thesis by fastforce
      qed
  next case (tc_proj \<Gamma> e ts l t)
    thus ?case
      proof (cases "is_value e")
      case True
        moreover with tc_proj have "\<Gamma> \<turnstile> s : t \<rightarrow> t" by simp
        moreover from tc_proj True have "\<Gamma> \<turnstile> e' : t" by fastforce
        ultimately show ?thesis by blast
      next case False
        with tc_proj obtain ss where "unfold e = (ss, e') \<and> s = SProj l # ss" 
          by (auto split: prod.splits)
        moreover with tc_proj obtain t' where "(\<Gamma> \<turnstile> ss : t' \<rightarrow> Record ts) \<and> (\<Gamma> \<turnstile> e' : t')" 
          by fastforce
        moreover with tc_proj have "\<Gamma> \<turnstile> SProj l # ss : t' \<rightarrow> t" by fastforce
        ultimately show ?thesis by fastforce
      qed
  next case (tcf_cons \<Gamma> e tt fs ts l')
    thus ?case
      proof (cases "is_value e")
      case True
        with tcf_cons obtain vs' where V: "unfold_f fs = (vs', l, nvs, s, e') \<and> vs = (l', e) # vs'" 
          by (cases "unfold_f fs") fastforce+
        moreover with tcf_cons True obtain t t' vts nvts where T: "lookup_assoc l ts = Some t \<and> 
          ts = vts @ [(l, t)] @ nvts \<and> keys vs' \<inter> keys nvs = {} \<and> l \<notin> keys vs' \<and> l \<notin> keys nvs \<and> 
            keys fs = insert l (keys vs' \<union> keys nvs) \<and> (\<Gamma> \<turnstile> s : t' \<rightarrow> t) \<and> (\<Gamma> \<turnstile> e' : t') \<and> 
              (\<Gamma> \<turnstile>\<^sub>f vs' : vts) \<and> \<Gamma> \<turnstile>\<^sub>f nvs : nvts" by fastforce
        moreover from tcf_cons T have "lookup_assoc l ((l', tt) # ts) = Some t" by auto
        moreover from tcf_cons V T have "keys vs \<inter> keys nvs = {}" by simp
        moreover from tcf_cons V T have "l \<notin> keys vs" by auto
        moreover from V T have "keys ((l', e) # fs) = insert l (keys vs \<union> keys nvs)" by auto
        moreover from tcf_cons V T have "\<Gamma> \<turnstile>\<^sub>f vs : (l', tt) # vts" by simp
        ultimately show ?thesis by auto
      qed fastforce+
  qed simp_all

lemma "\<Gamma> \<turnstile> e : t \<Longrightarrow> True"
  and [simp]: "\<Gamma> \<turnstile>\<^sub>f vs : vts \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>f nvs : nvts \<Longrightarrow> keys vs \<inter> keys nvs = {} \<Longrightarrow> 
    \<Gamma> \<turnstile>\<^sub>f vs @ nvs : vts @ nvts"
  proof (induction \<Gamma> e t and \<Gamma> vs vts rule: typecheck_typecheck_fs.inducts) 
  case (tcf_cons \<Gamma> e t fs ts l)
    hence "l \<notin> keys (fs @ nvs)" by auto
    with tcf_cons show ?case by simp
  qed simp_all

lemma [simp]: "\<Gamma> \<turnstile> s : t' \<rightarrow> t \<Longrightarrow> \<Gamma> \<turnstile> e : t' \<Longrightarrow> \<Gamma> \<turnstile> fold s e : t"
  by (induction \<Gamma> s t' t rule: typecheck_stack.induct) simp_all

lemma [simp]: "keys (incr_fs x fs) = keys fs"
  by (induction x fs rule: incr_incr_fs.induct(2)) simp_all

lemma [simp]: "\<Gamma> \<turnstile> e : t \<Longrightarrow> x \<le> length \<Gamma> \<Longrightarrow> insert_at x t' \<Gamma> \<turnstile> incr x e : t"
  and [simp]: "\<Gamma> \<turnstile>\<^sub>f fs : ts \<Longrightarrow> x \<le> length \<Gamma> \<Longrightarrow> insert_at x t' \<Gamma> \<turnstile>\<^sub>f incr_fs x fs : ts"
  by (induction \<Gamma> e t and \<Gamma> fs ts arbitrary: x and x rule: typecheck_typecheck_fs.inducts) 
     fastforce+

lemma [simp]: "keys (subst_fs x e' fs) = keys fs"
  by (induction x e' fs rule: subst_subst_fs.induct(2)) simp_all

lemma [simp]: "insert_at x t' \<Gamma> \<turnstile> e : t \<Longrightarrow> x \<le> length \<Gamma> \<Longrightarrow> \<Gamma> \<turnstile> e' : t' \<Longrightarrow> \<Gamma> \<turnstile> subst x e' e : t"
  and [simp]: "insert_at x t' \<Gamma> \<turnstile>\<^sub>f fs : ts \<Longrightarrow> x \<le> length \<Gamma> \<Longrightarrow> \<Gamma> \<turnstile> e' : t' \<Longrightarrow> 
    \<Gamma> \<turnstile>\<^sub>f subst_fs x e' fs : ts"
  proof (induction "insert_at x t' \<Gamma>" e t and "insert_at x t' \<Gamma>" fs ts arbitrary: \<Gamma> x e' and \<Gamma> x e' 
         rule: typecheck_typecheck_fs.inducts)
  case (tc_var y t)
    thus ?case by (cases y) auto
  next case (tc_abs t\<^sub>1 e t\<^sub>2)
    moreover hence "insert_at 0 t\<^sub>1 \<Gamma> \<turnstile> incr 0 e' : t'" by (simp del: insert_at.simps(1))
    ultimately show ?case by simp
  qed fastforce+

lemma [elim]: "\<Gamma> \<turnstile>\<^sub>f fs : ts \<Longrightarrow> lookup_assoc l fs = Some e \<Longrightarrow> lookup_assoc l ts = Some t \<Longrightarrow> 
    \<Gamma> \<turnstile> e : t" 
  by (induction \<Gamma> fs ts rule: typecheck_typecheck_fs.inducts(2)) (simp, simp_all split: if_splits)

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