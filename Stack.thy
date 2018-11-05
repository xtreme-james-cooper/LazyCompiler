theory Stack
imports Typecheck Misc
begin

datatype frame = 
  SApp1 expr
| SApp2 expr
| SRec "expr list" "expr list" 
| SProj nat
| SInj nat "type list"
| SCase "expr list" 

inductive typecheck_frame :: "type list \<Rightarrow> frame \<Rightarrow> type \<Rightarrow> type \<Rightarrow> bool" (infix "\<turnstile> _ : _ \<rightarrow>" 60) where
  tc_sapp1 [simp]: "\<Gamma> \<turnstile> e : t\<^sub>1 \<Longrightarrow> \<Gamma> \<turnstile> SApp1 e : Arrow t\<^sub>1 t\<^sub>2 \<rightarrow> t\<^sub>2"
| tc_sapp2 [simp]: "\<Gamma> \<turnstile> e : Arrow t\<^sub>1 t\<^sub>2 \<Longrightarrow> \<Gamma> \<turnstile> SApp2 e : t\<^sub>1 \<rightarrow> t\<^sub>2"
| tc_srec [simp]: "\<Gamma> \<turnstile>\<^sub>f vs : vts \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>f nvs : nvts \<Longrightarrow> 
    \<Gamma> \<turnstile> SRec vs nvs : t \<rightarrow> Record (vts @ [t] @ nvts)"
| tc_sproj [simp]: "lookup l ts = Some t \<Longrightarrow> \<Gamma> \<turnstile> SProj l : Record ts \<rightarrow> t"
| tc_sinj [simp]: "lookup l ts = Some t \<Longrightarrow> \<Gamma> \<turnstile> SInj l ts : t \<rightarrow> Variant ts"
| tc_scase [simp]: "\<Gamma> \<turnstile>\<^sub>c cs : ts \<rightarrow> t \<Longrightarrow> \<Gamma> \<turnstile> SCase cs : Variant ts \<rightarrow> t"

inductive_cases [elim]: "\<Gamma> \<turnstile> SApp1 e : t \<rightarrow> t'"
inductive_cases [elim]: "\<Gamma> \<turnstile> SApp2 e : t \<rightarrow> t'"
inductive_cases [elim]: "\<Gamma> \<turnstile> SRec vs nvs : t \<rightarrow> t'"
inductive_cases [elim]: "\<Gamma> \<turnstile> SProj l : t \<rightarrow> t'"
inductive_cases [elim]: "\<Gamma> \<turnstile> SInj l ts : t \<rightarrow> t'"
inductive_cases [elim]: "\<Gamma> \<turnstile> SCase cs : t \<rightarrow> t'"

inductive typecheck_stack :: "type list \<Rightarrow> frame list \<Rightarrow> type \<Rightarrow> type \<Rightarrow> bool" 
    (infix "\<turnstile>\<^sub>s _ : _ \<rightarrow>" 60) where
  tcs_nil [simp]: "\<Gamma> \<turnstile>\<^sub>s [] : t \<rightarrow> t"
| tcs_cons [simp]: "\<Gamma> \<turnstile>\<^sub>s s : t\<^sub>1 \<rightarrow> t\<^sub>2 \<Longrightarrow> \<Gamma> \<turnstile> f : t\<^sub>2 \<rightarrow> t\<^sub>3 \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>s f # s : t\<^sub>1 \<rightarrow> t\<^sub>3"

inductive_cases [elim]: "\<Gamma> \<turnstile>\<^sub>s [] : t \<rightarrow> t'"
inductive_cases [elim]: "\<Gamma> \<turnstile>\<^sub>s f # s : t \<rightarrow> t'"

fun unfold :: "expr \<Rightarrow> frame list \<times> expr" 
and unfold_f :: "expr list \<Rightarrow> expr list \<times> expr list \<times> frame list \<times> expr" where
  "unfold (Var y) = ([], Var y)"
| "unfold (Abs t e) = ([], Abs t e)"
| "unfold (App e\<^sub>1 e\<^sub>2) = (
    if is_value e\<^sub>1
    then if is_value e\<^sub>2
         then ([], App e\<^sub>1 e\<^sub>2)
         else cons_fst (SApp2 e\<^sub>1) (unfold e\<^sub>2)
    else cons_fst (SApp1 e\<^sub>2) (unfold e\<^sub>1))"
| "unfold (Rec fs) = (
    if is_value_f fs 
    then ([], Rec fs) 
    else case unfold_f fs of (vs, nvs, se) \<Rightarrow> cons_fst (SRec vs nvs) se)"
| "unfold (Proj e l) = (
    if is_value e 
    then ([], Proj e l) 
    else cons_fst (SProj l) (unfold e))"
| "unfold (Inj l ts e) = (
    if is_value e 
    then ([], Inj l ts e) 
    else cons_fst (SInj l ts) (unfold e))"
| "unfold (Case e cs) = (
    if is_value e 
    then ([], Case e cs) 
    else cons_fst (SCase cs) (unfold e))"
| "unfold_f [] = undefined"
| "unfold_f (e # fs) = (
    if is_value e
    then cons_fst e (unfold_f fs)
    else ([], fs, unfold e))"

fun fold' :: "frame \<Rightarrow> expr \<Rightarrow> expr" where
  "fold' (SApp1 e') e = App e e'"
| "fold' (SApp2 e') e = App e' e"
| "fold' (SRec vs nvs) e = Rec (vs @ [e] @ nvs)"
| "fold' (SProj l) e = Proj e l"
| "fold' (SInj l ts) e = Inj l ts e"
| "fold' (SCase cs) e = Case e cs"

fun fold :: "frame list \<Rightarrow> expr \<Rightarrow> expr" where
  "fold [] e = e"
| "fold (f # s) e = fold' f (fold s e)"

lemma [simp]: "unfold e = (s, e') \<Longrightarrow> fold s e' = e"
  and [simp]: "unfold_f fs = (vs, nvs, s, e') \<Longrightarrow> \<not> is_value_f fs \<Longrightarrow> vs @ [fold s e'] @ nvs = fs"
  by (induction e and fs arbitrary: s e' and vs nvs s e' rule: unfold_unfold_f.induct) 
     (auto split: if_splits prod.splits)

lemma [simp]: "\<Gamma> \<turnstile> f : t\<^sub>1 \<rightarrow> t\<^sub>2 \<Longrightarrow> \<Gamma> \<turnstile> e : t\<^sub>1 \<Longrightarrow> \<Gamma> \<turnstile> fold' f e : t\<^sub>2"
  by (induction \<Gamma> f t\<^sub>1 t\<^sub>2 rule: typecheck_frame.induct) simp_all

lemma [simp]: "\<Gamma> \<turnstile>\<^sub>s s : t' \<rightarrow> t \<Longrightarrow> \<Gamma> \<turnstile> e : t' \<Longrightarrow> \<Gamma> \<turnstile> fold s e : t"
  by (induction \<Gamma> s t' t rule: typecheck_stack.induct) simp_all

lemma [simp]: "\<Gamma> \<turnstile> e : t \<Longrightarrow> unfold e = (s, e') \<Longrightarrow> \<exists>t'. (\<Gamma> \<turnstile>\<^sub>s s : t' \<rightarrow> t) \<and> (\<Gamma> \<turnstile> e' : t')"
  and [simp]: "\<Gamma> \<turnstile>\<^sub>f fs : ts \<Longrightarrow> \<not> is_value_f fs \<Longrightarrow> unfold_f fs = (vs, nvs, s, e') \<Longrightarrow> 
    \<exists>t t' vts nvts. ts = vts @ [t] @ nvts \<and> (\<Gamma> \<turnstile>\<^sub>s s : t' \<rightarrow> t) \<and> (\<Gamma> \<turnstile> e' : t') \<and> (\<Gamma> \<turnstile>\<^sub>f vs : vts) \<and> 
      (\<Gamma> \<turnstile>\<^sub>f nvs : nvts)"
  and [simp]: "\<Gamma> \<turnstile>\<^sub>c cs : ts \<rightarrow> t \<Longrightarrow> True"
  proof (induction \<Gamma> e t and \<Gamma> fs ts arbitrary: s and vs nvs s 
         rule: typecheck_typecheck_fs_typecheck_cs.inducts)
  case (tc_var x \<Gamma> t)
    thus ?case by simp (metis tcs_nil typecheck_typecheck_fs_typecheck_cs.tc_var)
  next case (tc_app \<Gamma> e\<^sub>1 t\<^sub>1 t\<^sub>2 e\<^sub>2)
    thus ?case 
      proof (cases "is_value e\<^sub>1")
      case True note T = True
        thus ?thesis
          proof (cases "is_value e\<^sub>2")
          case True
            with tc_app T show ?thesis 
              by simp (metis tcs_nil typecheck_typecheck_fs_typecheck_cs.tc_app)
          next case False
            with tc_app True obtain s\<^sub>2 where "unfold e\<^sub>2 = (s\<^sub>2, e') \<and> s = SApp2 e\<^sub>1 # s\<^sub>2" 
              by (auto split: prod.splits)
            moreover with tc_app obtain t' where "(\<Gamma> \<turnstile>\<^sub>s s\<^sub>2 : t' \<rightarrow> t\<^sub>1) \<and> \<Gamma> \<turnstile> e' : t'" by fastforce
            moreover with tc_app have "\<Gamma> \<turnstile>\<^sub>s SApp2 e\<^sub>1 # s\<^sub>2 : t' \<rightarrow> t\<^sub>2" by fastforce
            ultimately show ?thesis by fastforce
          qed
      next case False
        with tc_app obtain s\<^sub>1 where "unfold e\<^sub>1 = (s\<^sub>1, e') \<and> s = SApp1 e\<^sub>2 # s\<^sub>1" 
          by (auto split: prod.splits)
        moreover with tc_app obtain t' where "(\<Gamma> \<turnstile>\<^sub>s s\<^sub>1 : t' \<rightarrow> Arrow t\<^sub>1 t\<^sub>2) \<and> \<Gamma> \<turnstile> e' : t'" 
          by fastforce
        moreover with tc_app have "\<Gamma> \<turnstile>\<^sub>s SApp1 e\<^sub>2 # s\<^sub>1 : t' \<rightarrow> t\<^sub>2" by fastforce
        ultimately show ?thesis by fastforce
      qed
  next case (tc_abs t\<^sub>1 \<Gamma> e t\<^sub>2)
    thus ?case by simp (metis tcs_nil typecheck_typecheck_fs_typecheck_cs.tc_abs)
  next case (tc_rec \<Gamma> fs ts)
    thus ?case 
      proof (cases "is_value_f fs")
      case True
        with tc_rec show ?thesis by simp (metis tcs_nil typecheck_typecheck_fs_typecheck_cs.tc_rec)
      next case False
        then obtain vs nvs ss ee' where F: "unfold_f fs = (vs, nvs, ss, ee')" 
          by (cases "unfold_f fs") simp_all
        with tc_rec False obtain t t' vts nvts where T: "ts = vts @ [t] @ nvts \<and> 
            (\<Gamma> \<turnstile>\<^sub>s ss : t' \<rightarrow> t) \<and> (\<Gamma> \<turnstile> e' : t') \<and> (\<Gamma> \<turnstile>\<^sub>f vs : vts) \<and> \<Gamma> \<turnstile>\<^sub>f nvs : nvts" by fastforce
        hence "\<Gamma> \<turnstile>\<^sub>s SRec vs nvs # ss : t' \<rightarrow> Record ts" using tc_srec by fastforce
        with tc_rec False F T show ?thesis by fastforce
      qed
  next case (tc_proj \<Gamma> e ts l t)
    thus ?case
      proof (cases "is_value e")
      case True
        with tc_proj show ?thesis by simp (metis tcs_nil typecheck_typecheck_fs_typecheck_cs.tc_proj)
      next case False
        with tc_proj obtain ss where "unfold e = (ss, e') \<and> s = SProj l # ss" 
          by (auto split: prod.splits)
        moreover with tc_proj obtain t' where "(\<Gamma> \<turnstile>\<^sub>s ss : t' \<rightarrow> Record ts) \<and> (\<Gamma> \<turnstile> e' : t')" 
          by fastforce
        moreover with tc_proj have "\<Gamma> \<turnstile>\<^sub>s SProj l # ss : t' \<rightarrow> t" by fastforce
        ultimately show ?thesis by fastforce
      qed
  next case (tc_inj \<Gamma> e t l ts)
    thus ?case
      proof (cases "is_value e")
      case True
        with tc_inj show ?thesis by simp (metis tcs_nil typecheck_typecheck_fs_typecheck_cs.tc_inj)
      next case False
        with tc_inj obtain s' where S: "unfold e = (s', e') \<and> s = SInj l ts # s'" 
          by (auto split: prod.splits)
        with tc_inj obtain t' where "(\<Gamma> \<turnstile>\<^sub>s s' : t' \<rightarrow> t) \<and> (\<Gamma> \<turnstile> e' : t')" by fastforce
        moreover with tc_inj S have "\<Gamma> \<turnstile>\<^sub>s s : t' \<rightarrow> Variant ts" using tc_sinj by fastforce
        ultimately show ?thesis by fastforce
      qed
  next case (tc_case \<Gamma> e ts cs t)
    thus ?case
      proof (cases "is_value e")
      case True
        with tc_case show ?thesis by simp (metis tcs_nil typecheck_typecheck_fs_typecheck_cs.tc_case)
      next case False
        with tc_case obtain s' where S: "unfold e = (s', e') \<and> s = SCase cs # s'" 
          by (auto split: prod.splits)
        with tc_case obtain t' where T: "(\<Gamma> \<turnstile>\<^sub>s s' : t' \<rightarrow> Variant ts) \<and> (\<Gamma> \<turnstile> e' : t')" by fastforce
        with tc_case S have "\<Gamma> \<turnstile>\<^sub>s s : t' \<rightarrow> t" using tc_scase by fastforce
        with T show ?thesis by fastforce
      qed
  next case (tcf_cons \<Gamma> e tt fs ts)
    thus ?case
      proof (cases "is_value e")
      case True
        with tcf_cons obtain vs' where V: "unfold_f fs = (vs', nvs, s, e') \<and> vs = e # vs'" 
          by (cases "unfold_f fs") fastforce+
        moreover with tcf_cons True obtain t t' vts nvts where T: "ts = vts @ [t] @ nvts \<and> 
          (\<Gamma> \<turnstile>\<^sub>s s : t' \<rightarrow> t) \<and> (\<Gamma> \<turnstile> e' : t') \<and> (\<Gamma> \<turnstile>\<^sub>f vs' : vts) \<and> \<Gamma> \<turnstile>\<^sub>f nvs : nvts" by fastforce
        moreover hence "tt # ts = (tt # vts) @ [t] @ nvts" by simp
        moreover from tcf_cons V T have "\<Gamma> \<turnstile>\<^sub>f vs : tt # vts" by simp
        ultimately show ?thesis by blast
      next case False
        with tcf_cons obtain t' where "(\<Gamma> \<turnstile>\<^sub>s s : t' \<rightarrow> tt) \<and> \<Gamma> \<turnstile> e' : t'" by fastforce
        moreover from tcf_cons False have "\<Gamma> \<turnstile>\<^sub>f vs : []" by simp
        moreover from tcf_cons False have "\<Gamma> \<turnstile>\<^sub>f nvs : ts" by simp
        ultimately show ?thesis by fastforce
      qed
  qed simp_all

end