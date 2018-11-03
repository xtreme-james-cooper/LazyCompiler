theory Evaluate
imports Expression Typecheck
begin

datatype stack = 
  SApp1 expr
| SApp2 expr
| SRec "expr list" "expr list" 
| SProj nat

inductive typecheck_stack :: "type list \<Rightarrow> stack list \<Rightarrow> type \<Rightarrow> type \<Rightarrow> bool" 
    (infix "\<turnstile> _ : _ \<rightarrow>" 60) where
  tc_hole [simp]: "\<Gamma> \<turnstile> [] : t \<rightarrow> t"
| tc_sapp1 [simp]: "\<Gamma> \<turnstile> s : t \<rightarrow> Arrow t\<^sub>1 t\<^sub>2 \<Longrightarrow> \<Gamma> \<turnstile> e : t\<^sub>1 \<Longrightarrow> \<Gamma> \<turnstile> SApp1 e # s : t \<rightarrow> t\<^sub>2"
| tc_sapp2 [simp]: "\<Gamma> \<turnstile> e : Arrow t\<^sub>1 t\<^sub>2 \<Longrightarrow> \<Gamma> \<turnstile> s : t \<rightarrow> t\<^sub>1 \<Longrightarrow> \<Gamma> \<turnstile> SApp2 e # s : t \<rightarrow> t\<^sub>2"
| tc_srec [simp]: "\<Gamma> \<turnstile>\<^sub>f vs : vts \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>f nvs : nvts \<Longrightarrow> \<Gamma> \<turnstile> s : t \<rightarrow> t' \<Longrightarrow> 
    \<Gamma> \<turnstile> SRec vs nvs # s : t \<rightarrow> Record (vts @ [t'] @ nvts)"
| tc_sproj [simp]: "\<Gamma> \<turnstile> s : t \<rightarrow> Record ts \<Longrightarrow> lookup l ts = Some t' \<Longrightarrow> 
    \<Gamma> \<turnstile> SProj l # s : t \<rightarrow> t'"

fun stack_extend :: "stack \<Rightarrow> stack list \<times> expr \<Rightarrow> stack list \<times> expr" where
  "stack_extend s' se = (case se of (s, e) \<Rightarrow> (s' # s, e))"

fun unfold :: "expr \<Rightarrow> stack list \<times> expr" 
and unfold_f :: "expr list \<Rightarrow> expr list \<times> expr list \<times> stack list \<times> expr" where
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
    else case unfold_f fs of (vs, nvs, s, e) \<Rightarrow> (SRec vs nvs # s, e))"
| "unfold (Proj e l) = (
    if is_value e 
    then ([], Proj e l) 
    else stack_extend (SProj l) (unfold e))"
| "unfold_f [] = undefined"
| "unfold_f (e # fs) = (
    if is_value e
    then case unfold_f fs of (vs, nvs, s, e') \<Rightarrow> (e # vs, nvs, s, e')
    else ([], fs, unfold e))"

fun fold :: "stack list \<Rightarrow> expr \<Rightarrow> expr" where
  "fold [] e = e"
| "fold (SApp1 e' # s) e = App (fold s e) e'"
| "fold (SApp2 e' # s) e = App e' (fold s e)"
| "fold (SRec vs nvs # s) e = Rec (vs @ [fold s e] @ nvs)"
| "fold (SProj l # s) e = Proj (fold s e) l"

inductive reduce :: "expr \<Rightarrow> expr \<Rightarrow> bool" (infix "\<leadsto>\<^sub>\<beta>" 60) where
  ev_beta [simp]: "is_value e\<^sub>2 \<Longrightarrow> App (Abs t e\<^sub>1) e\<^sub>2 \<leadsto>\<^sub>\<beta> subst 0 e\<^sub>2 e\<^sub>1" 
| ev_proj [simp]: "is_value_f fs \<Longrightarrow> lookup l fs = Some e \<Longrightarrow> Proj (Rec fs) l \<leadsto>\<^sub>\<beta> e" 

inductive evaluate :: "expr \<Rightarrow> expr \<Rightarrow> bool" (infix "\<leadsto>" 60) where
  ev_stack [simp]: "unfold e = (s, r) \<Longrightarrow> r \<leadsto>\<^sub>\<beta> r' \<Longrightarrow> e \<leadsto> fold s r'"

inductive_cases [elim]: "e \<leadsto> e'"

lemma [simp]: "unfold e = (s, e') \<Longrightarrow> fold s e' = e"
  and [simp]: "unfold_f fs = (vs,  nvs, s, e') \<Longrightarrow> \<not> is_value_f fs \<Longrightarrow> 
    vs @ [fold s e'] @ nvs = fs"
  by (induction e and fs arbitrary: s e' and vs nvs s e' rule: unfold_unfold_f.induct) 
     (auto split: if_splits prod.splits)

lemma [simp]: "\<Gamma> \<turnstile> s : t' \<rightarrow> t \<Longrightarrow> \<Gamma> \<turnstile> e : t' \<Longrightarrow> \<Gamma> \<turnstile> fold s e : t"
  by (induction \<Gamma> s t' t rule: typecheck_stack.induct) simp_all

lemma [simp]: "\<Gamma> \<turnstile> e : t \<Longrightarrow> unfold e = (s, e') \<Longrightarrow> \<exists>t'. (\<Gamma> \<turnstile> s : t' \<rightarrow> t) \<and> (\<Gamma> \<turnstile> e' : t')"
  and [simp]: "\<Gamma> \<turnstile>\<^sub>f fs : ts \<Longrightarrow> \<not> is_value_f fs \<Longrightarrow> unfold_f fs = (vs, nvs, s, e') \<Longrightarrow> 
    \<exists>t t' vts nvts. ts = vts @ [t] @ nvts \<and> (\<Gamma> \<turnstile> s : t' \<rightarrow> t) \<and> (\<Gamma> \<turnstile> e' : t') \<and> (\<Gamma> \<turnstile>\<^sub>f vs : vts) \<and> 
      (\<Gamma> \<turnstile>\<^sub>f nvs : nvts)"
  proof (induction \<Gamma> e t and \<Gamma> fs ts arbitrary: s and vs nvs s rule: typecheck_typecheck_fs.inducts)
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
        then obtain vs nvs ss ee' where F: "unfold_f fs = (vs, nvs, ss, ee')" 
          by (cases "unfold_f fs") simp_all
        with tc_rec False obtain t t' vts nvts where T: "ts = vts @ [t] @ nvts \<and> 
            (\<Gamma> \<turnstile> ss : t' \<rightarrow> t) \<and> (\<Gamma> \<turnstile> e' : t') \<and> (\<Gamma> \<turnstile>\<^sub>f vs : vts) \<and> \<Gamma> \<turnstile>\<^sub>f nvs : nvts" by fastforce
        hence "\<Gamma> \<turnstile> SRec vs nvs # ss : t' \<rightarrow> Record ts" using tc_srec by fastforce
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
  next case (tcf_cons \<Gamma> e tt fs ts)
    thus ?case
      proof (cases "is_value e")
      case True
        with tcf_cons obtain vs' where V: "unfold_f fs = (vs', nvs, s, e') \<and> vs = e # vs'" 
          by (cases "unfold_f fs") fastforce+
        moreover with tcf_cons True obtain t t' vts nvts where T: "ts = vts @ [t] @ nvts \<and> 
          (\<Gamma> \<turnstile> s : t' \<rightarrow> t) \<and> (\<Gamma> \<turnstile> e' : t') \<and> (\<Gamma> \<turnstile>\<^sub>f vs' : vts) \<and> \<Gamma> \<turnstile>\<^sub>f nvs : nvts" by fastforce
        moreover hence "tt # ts = (tt # vts) @ [t] @ nvts" by simp
        moreover from tcf_cons V T have "\<Gamma> \<turnstile>\<^sub>f vs : tt # vts" by simp
        ultimately show ?thesis by blast
      next case False
        with tcf_cons obtain t' where "(\<Gamma> \<turnstile> s : t' \<rightarrow> tt) \<and> \<Gamma> \<turnstile> e' : t'" by fastforce
        moreover from tcf_cons False have "\<Gamma> \<turnstile>\<^sub>f vs : []" by simp
        moreover from tcf_cons False have "\<Gamma> \<turnstile>\<^sub>f nvs : ts" by simp
        ultimately show ?thesis by fastforce
      qed
  qed simp_all

end