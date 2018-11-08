theory Stack
imports Typecheck Misc
begin

datatype frame = 
  SApp1 expr
| SApp2 expr
| SLet expr
| SRec "expr list" "expr list" 
| SProj nat
| SInj nat "type list"
| SCase "expr list" 
| SFold type 
| SUnfold type 
| STyApp type 

inductive typecheck_frame :: "nat \<Rightarrow> type list \<Rightarrow> frame \<Rightarrow> type \<Rightarrow> type \<Rightarrow> bool" 
    (infix ",_ \<turnstile> _ : _ \<rightarrow>" 60) where
  tc_sapp1 [simp]: "\<Delta>,\<Gamma> \<turnstile> e : t\<^sub>1 \<Longrightarrow> \<Delta>,\<Gamma> \<turnstile> SApp1 e : Arrow t\<^sub>1 t\<^sub>2 \<rightarrow> t\<^sub>2"
| tc_sapp2 [simp]: "\<Delta>,\<Gamma> \<turnstile> e : Arrow t\<^sub>1 t\<^sub>2 \<Longrightarrow> \<Delta>,\<Gamma> \<turnstile> SApp2 e : t\<^sub>1 \<rightarrow> t\<^sub>2"
| tc_slet [simp]: "\<Delta>,insert_at 0 t\<^sub>1 \<Gamma> \<turnstile> e : t\<^sub>2 \<Longrightarrow> \<Delta>,\<Gamma> \<turnstile> SLet e : t\<^sub>1 \<rightarrow> t\<^sub>2"
| tc_srec [simp]: "\<Delta>,\<Gamma> \<turnstile>\<^sub>f vs : vts \<Longrightarrow> \<Delta>,\<Gamma> \<turnstile>\<^sub>f nvs : nvts \<Longrightarrow> 
    \<Delta>,\<Gamma> \<turnstile> SRec vs nvs : t \<rightarrow> Record (vts @ [t] @ nvts)"
| tc_sproj [simp]: "lookup l ts = Some t \<Longrightarrow> \<Delta>,\<Gamma> \<turnstile> SProj l : Record ts \<rightarrow> t"
| tc_sinj [simp]: "lookup l ts = Some t \<Longrightarrow> (\<forall>tt \<in> set ts. \<Delta> \<turnstile>\<^sub>k tt) \<Longrightarrow> 
    \<Delta>,\<Gamma> \<turnstile> SInj l ts : t \<rightarrow> Variant ts"
| tc_sfold [simp]: "Suc \<Delta> \<turnstile>\<^sub>k t \<Longrightarrow> \<Delta>,\<Gamma> \<turnstile> SFold t : subst\<^sub>t\<^sub>t 0 (Inductive t) t \<rightarrow> Inductive t"
| tc_unfold [simp]: "Suc \<Delta> \<turnstile>\<^sub>k t \<Longrightarrow> \<Delta>,\<Gamma> \<turnstile> SUnfold t : Inductive t \<rightarrow> subst\<^sub>t\<^sub>t 0 (Inductive t) t"
| tc_scase [simp]: "\<Delta>,\<Gamma> \<turnstile>\<^sub>c cs : ts \<rightarrow> t \<Longrightarrow> \<Delta>,\<Gamma> \<turnstile> SCase cs : Variant ts \<rightarrow> t"
| tc_styapp [simp]: "\<Delta> \<turnstile>\<^sub>k t' \<Longrightarrow> \<Delta>,\<Gamma> \<turnstile> STyApp t' : Forall t \<rightarrow> subst\<^sub>t\<^sub>t 0 t' t"

inductive_cases [elim]: "\<Delta>,\<Gamma> \<turnstile> SApp1 e : t \<rightarrow> t'"
inductive_cases [elim]: "\<Delta>,\<Gamma> \<turnstile> SApp2 e : t \<rightarrow> t'"
inductive_cases [elim]: "\<Delta>,\<Gamma> \<turnstile> SLet e : t \<rightarrow> t'"
inductive_cases [elim]: "\<Delta>,\<Gamma> \<turnstile> SRec vs nvs : t \<rightarrow> t'"
inductive_cases [elim]: "\<Delta>,\<Gamma> \<turnstile> SProj l : t \<rightarrow> t'"
inductive_cases [elim]: "\<Delta>,\<Gamma> \<turnstile> SInj l ts : t \<rightarrow> t'"
inductive_cases [elim]: "\<Delta>,\<Gamma> \<turnstile> SCase cs : t \<rightarrow> t'"
inductive_cases [elim]: "\<Delta>,\<Gamma> \<turnstile> SFold tt : t \<rightarrow> t'"
inductive_cases [elim]: "\<Delta>,\<Gamma> \<turnstile> SUnfold tt : t \<rightarrow> t'"
inductive_cases [elim]: "\<Delta>,\<Gamma> \<turnstile> STyApp tt : t \<rightarrow> t'"

inductive typecheck_stack :: "nat \<Rightarrow> type list \<Rightarrow> frame list \<Rightarrow> type \<Rightarrow> type \<Rightarrow> bool" 
    (infix ",_ \<turnstile>\<^sub>s _ : _ \<rightarrow>" 60) where
  tcs_nil [simp]: "\<Delta>,\<Gamma> \<turnstile>\<^sub>s [] : t \<rightarrow> t"
| tcs_cons [simp]: "\<Delta>,\<Gamma> \<turnstile>\<^sub>s s : t\<^sub>1 \<rightarrow> t\<^sub>2 \<Longrightarrow> \<Delta>,\<Gamma> \<turnstile> f : t\<^sub>2 \<rightarrow> t\<^sub>3 \<Longrightarrow> \<Delta>,\<Gamma> \<turnstile>\<^sub>s f # s : t\<^sub>1 \<rightarrow> t\<^sub>3"

inductive_cases [elim]: "\<Delta>,\<Gamma> \<turnstile>\<^sub>s [] : t \<rightarrow> t'"
inductive_cases [elim]: "\<Delta>,\<Gamma> \<turnstile>\<^sub>s f # s : t \<rightarrow> t'"

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
| "unfold (Let e\<^sub>1 e\<^sub>2) = (
    if is_value e\<^sub>1
    then ([], Let e\<^sub>1 e\<^sub>2) 
    else cons_fst (SLet e\<^sub>2) (unfold e\<^sub>1))"
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
| "unfold (Fold t e) = (
    if is_value e 
    then ([], Fold t e)
    else cons_fst (SFold t) (unfold e))"
| "unfold (Unfold t e) = (
    if is_value e 
    then ([], Unfold t e)
    else cons_fst (SUnfold t) (unfold e))"
| "unfold (TyAbs e) = ([], TyAbs e)"
| "unfold (TyApp e t) = (
    if is_value e 
    then ([], TyApp e t)
    else cons_fst (STyApp t) (unfold e))"
| "unfold_f [] = undefined"
| "unfold_f (e # fs) = (
    if is_value e
    then cons_fst e (unfold_f fs)
    else ([], fs, unfold e))"

fun fold' :: "frame \<Rightarrow> expr \<Rightarrow> expr" where
  "fold' (SApp1 e') e = App e e'"
| "fold' (SApp2 e') e = App e' e"
| "fold' (SLet e') e = Let e e'"
| "fold' (SRec vs nvs) e = Rec (vs @ [e] @ nvs)"
| "fold' (SProj l) e = Proj e l"
| "fold' (SInj l ts) e = Inj l ts e"
| "fold' (SCase cs) e = Case e cs"
| "fold' (SFold t) e = Fold t e"
| "fold' (SUnfold t) e = Unfold t e"
| "fold' (STyApp t) e = TyApp e t"

fun fold :: "frame list \<Rightarrow> expr \<Rightarrow> expr" where
  "fold [] e = e"
| "fold (f # s) e = fold' f (fold s e)"

lemma [simp]: "unfold e = (s, e') \<Longrightarrow> fold s e' = e"
  and [simp]: "unfold_f fs = (vs, nvs, s, e') \<Longrightarrow> \<not> is_value_f fs \<Longrightarrow> vs @ [fold s e'] @ nvs = fs"
  by (induction e and fs arbitrary: s e' and vs nvs s e' rule: unfold_unfold_f.induct) 
     (auto split: if_splits prod.splits)

lemma [simp]: "\<Delta>,\<Gamma> \<turnstile> f : t\<^sub>1 \<rightarrow> t\<^sub>2 \<Longrightarrow> \<Delta>,\<Gamma> \<turnstile> e : t\<^sub>1 \<Longrightarrow> \<Delta>,\<Gamma> \<turnstile> fold' f e : t\<^sub>2"
  by (induction \<Gamma> f t\<^sub>1 t\<^sub>2 rule: typecheck_frame.induct) simp_all

lemma [simp]: "\<Delta>,\<Gamma> \<turnstile>\<^sub>s s : t' \<rightarrow> t \<Longrightarrow> \<Delta>,\<Gamma> \<turnstile> e : t' \<Longrightarrow> \<Delta>,\<Gamma> \<turnstile> fold s e : t"
  by (induction \<Gamma> s t' t rule: typecheck_stack.induct) simp_all

lemma [simp]: "\<Delta>,\<Gamma> \<turnstile> e : t \<Longrightarrow> unfold e = (s, e') \<Longrightarrow> \<exists>t'. (\<Delta>,\<Gamma> \<turnstile>\<^sub>s s : t' \<rightarrow> t) \<and> (\<Delta>,\<Gamma> \<turnstile> e' : t')"
  and [simp]: "\<Delta>,\<Gamma> \<turnstile>\<^sub>f fs : ts \<Longrightarrow> \<not> is_value_f fs \<Longrightarrow> unfold_f fs = (vs, nvs, s, e') \<Longrightarrow> 
    \<exists>t t' vts nvts. ts = vts @ [t] @ nvts \<and> (\<Delta>,\<Gamma> \<turnstile>\<^sub>s s : t' \<rightarrow> t) \<and> (\<Delta>,\<Gamma> \<turnstile> e' : t') \<and> 
      (\<Delta>,\<Gamma> \<turnstile>\<^sub>f vs : vts) \<and> (\<Delta>,\<Gamma> \<turnstile>\<^sub>f nvs : nvts)"
  and [simp]: "\<Delta>,\<Gamma> \<turnstile>\<^sub>c cs : ts \<rightarrow> t \<Longrightarrow> True"
  proof (induction \<Delta> \<Gamma> e t and \<Delta> \<Gamma> fs ts arbitrary: s and vs nvs s 
         rule: typecheck_typecheck_fs_typecheck_cs.inducts)
  case (tc_var x \<Gamma> t)
    thus ?case by simp (metis tcs_nil typecheck_typecheck_fs_typecheck_cs.tc_var)
  next case (tc_app \<Delta> \<Gamma> e\<^sub>1 t\<^sub>1 t\<^sub>2 e\<^sub>2)
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
            moreover with tc_app obtain t' where "(\<Delta>,\<Gamma> \<turnstile>\<^sub>s s\<^sub>2 : t' \<rightarrow> t\<^sub>1) \<and> \<Delta>,\<Gamma> \<turnstile> e' : t'" 
              by fastforce
            moreover with tc_app have "\<Delta>,\<Gamma> \<turnstile>\<^sub>s SApp2 e\<^sub>1 # s\<^sub>2 : t' \<rightarrow> t\<^sub>2" by fastforce
            ultimately show ?thesis by fastforce
          qed
      next case False
        with tc_app obtain s\<^sub>1 where "unfold e\<^sub>1 = (s\<^sub>1, e') \<and> s = SApp1 e\<^sub>2 # s\<^sub>1" 
          by (auto split: prod.splits)
        moreover with tc_app obtain t' where "(\<Delta>,\<Gamma> \<turnstile>\<^sub>s s\<^sub>1 : t' \<rightarrow> Arrow t\<^sub>1 t\<^sub>2) \<and> \<Delta>,\<Gamma> \<turnstile> e' : t'" 
          by fastforce
        moreover with tc_app have "\<Delta>,\<Gamma> \<turnstile>\<^sub>s SApp1 e\<^sub>2 # s\<^sub>1 : t' \<rightarrow> t\<^sub>2" by fastforce
        ultimately show ?thesis by fastforce
      qed
  next case (tc_abs \<Delta> t\<^sub>1 \<Gamma> e t\<^sub>2)
    thus ?case by simp (metis tcs_nil typecheck_typecheck_fs_typecheck_cs.tc_abs)
  next case (tc_let \<Delta> \<Gamma> e\<^sub>1 t\<^sub>1 e\<^sub>2 t\<^sub>2)
    thus ?case
      proof (cases "is_value e\<^sub>1")
      case True
        with tc_let show ?thesis by simp (metis tcs_nil typecheck_typecheck_fs_typecheck_cs.tc_let)
      next case False
        with tc_let obtain s' where S: "unfold e\<^sub>1 = (s', e') \<and> s = SLet e\<^sub>2 # s'"
          by (auto split: prod.splits)
        with tc_let obtain t' where "(\<Delta>,\<Gamma> \<turnstile>\<^sub>s s' : t' \<rightarrow> t\<^sub>1) \<and> (\<Delta>,\<Gamma> \<turnstile> e' : t')" by fastforce
        moreover with tc_let S have X: "\<Delta>,\<Gamma> \<turnstile>\<^sub>s s : t' \<rightarrow> t\<^sub>2" by fastforce
        ultimately show ?thesis by fastforce
      qed
  next case (tc_rec \<Delta> \<Gamma> fs ts)
    thus ?case 
      proof (cases "is_value_f fs")
      case True
        with tc_rec show ?thesis by simp (metis tcs_nil typecheck_typecheck_fs_typecheck_cs.tc_rec)
      next case False
        then obtain vs nvs ss ee' where F: "unfold_f fs = (vs, nvs, ss, ee')" 
          by (cases "unfold_f fs") simp_all
        with tc_rec False obtain t t' vts nvts where T: "ts = vts @ [t] @ nvts \<and> 
          (\<Delta>,\<Gamma> \<turnstile>\<^sub>s ss : t' \<rightarrow> t) \<and> (\<Delta>,\<Gamma> \<turnstile> e' : t') \<and> (\<Delta>,\<Gamma> \<turnstile>\<^sub>f vs : vts) \<and> \<Delta>,\<Gamma> \<turnstile>\<^sub>f nvs : nvts" 
            by fastforce
        hence "\<Delta>,\<Gamma> \<turnstile>\<^sub>s SRec vs nvs # ss : t' \<rightarrow> Record ts" using tc_srec by fastforce
        with tc_rec False F T show ?thesis by fastforce
      qed
  next case (tc_proj \<Delta> \<Gamma> e ts l t)
    thus ?case
      proof (cases "is_value e")
      case True
        with tc_proj show ?thesis by simp (metis tcs_nil typecheck_typecheck_fs_typecheck_cs.tc_proj)
      next case False
        with tc_proj obtain ss where "unfold e = (ss, e') \<and> s = SProj l # ss" 
          by (auto split: prod.splits)
        moreover with tc_proj obtain t' where "(\<Delta>,\<Gamma> \<turnstile>\<^sub>s ss : t' \<rightarrow> Record ts) \<and> (\<Delta>,\<Gamma> \<turnstile> e' : t')" 
          by fastforce
        moreover with tc_proj have "\<Delta>,\<Gamma> \<turnstile>\<^sub>s SProj l # ss : t' \<rightarrow> t" by fastforce
        ultimately show ?thesis by fastforce
      qed
  next case (tc_inj \<Delta> \<Gamma> e t l ts)
    thus ?case
      proof (cases "is_value e")
      case True
        with tc_inj show ?thesis by simp (metis tcs_nil typecheck_typecheck_fs_typecheck_cs.tc_inj)
      next case False
        with tc_inj obtain s' where S: "unfold e = (s', e') \<and> s = SInj l ts # s'" 
          by (auto split: prod.splits)
        with tc_inj obtain t' where "(\<Delta>,\<Gamma> \<turnstile>\<^sub>s s' : t' \<rightarrow> t) \<and> (\<Delta>,\<Gamma> \<turnstile> e' : t')" by fastforce
        moreover with tc_inj S have "\<Delta>,\<Gamma> \<turnstile>\<^sub>s s : t' \<rightarrow> Variant ts" using tc_sinj by fastforce
        ultimately show ?thesis by fastforce
      qed
  next case (tc_case \<Delta> \<Gamma> e ts cs t)
    thus ?case
      proof (cases "is_value e")
      case True
        with tc_case show ?thesis by simp (metis tcs_nil typecheck_typecheck_fs_typecheck_cs.tc_case)
      next case False
        with tc_case obtain s' where S: "unfold e = (s', e') \<and> s = SCase cs # s'" 
          by (auto split: prod.splits)
        with tc_case obtain t' where T: "(\<Delta>,\<Gamma> \<turnstile>\<^sub>s s' : t' \<rightarrow> Variant ts) \<and> (\<Delta>,\<Gamma> \<turnstile> e' : t')" 
          by fastforce
        with tc_case S have "\<Delta>,\<Gamma> \<turnstile>\<^sub>s s : t' \<rightarrow> t" using tc_scase by fastforce
        with T show ?thesis by fastforce
      qed
  next case (tc_fold \<Delta> \<Gamma> e t)
    thus ?case
      proof (cases "is_value e")
      case True
        with tc_fold show ?thesis by simp (metis tcs_nil typecheck_typecheck_fs_typecheck_cs.tc_fold)
      next case False
        with tc_fold obtain s' where S: "unfold e = (s', e') \<and> s = SFold t # s'"
          by (auto split: prod.splits)
        with tc_fold obtain t' where T: "(\<Delta>,\<Gamma> \<turnstile>\<^sub>s s' : t' \<rightarrow> subst\<^sub>t\<^sub>t 0 (Inductive t) t) \<and> 
          (\<Delta>,\<Gamma> \<turnstile> e' : t')" by fastforce
        with tc_fold S have "\<Delta>,\<Gamma> \<turnstile>\<^sub>s s : t' \<rightarrow> Inductive t" by fastforce
        with T show ?thesis by fastforce
      qed
  next case (tc_unfold \<Delta> \<Gamma> e t)
    thus ?case
      proof (cases "is_value e")
      case True
        with tc_unfold show ?thesis 
          by simp (metis tcs_nil typecheck_typecheck_fs_typecheck_cs.tc_unfold)
      next case False
        with tc_unfold obtain s' where S: "unfold e = (s', e') \<and> s = SUnfold t # s'"
          by (auto split: prod.splits)
        with tc_unfold obtain t' where T: "(\<Delta>,\<Gamma> \<turnstile>\<^sub>s s' : t' \<rightarrow> Inductive t) \<and> 
          (\<Delta>,\<Gamma> \<turnstile> e' : t')" by fastforce
        with tc_unfold S have "\<Delta>,\<Gamma> \<turnstile>\<^sub>s s : t' \<rightarrow> subst\<^sub>t\<^sub>t 0 (Inductive t) t" by fastforce
        with T show ?thesis by fastforce
      qed
  next case (tc_tyabs \<Delta> \<Gamma> e t)
    thus ?case by simp (metis tcs_nil typecheck_typecheck_fs_typecheck_cs.tc_tyabs)
  next case (tc_tyapp \<Delta> \<Gamma> e t t')
    thus ?case
      proof (cases "is_value e")
      case True
        with tc_tyapp show ?thesis 
          by simp (metis tcs_nil typecheck_typecheck_fs_typecheck_cs.tc_tyapp)
      next case False
        with tc_tyapp obtain s' where S: "unfold e = (s', e') \<and> s = STyApp t' # s'" 
          by (auto split: prod.splits)
        with tc_tyapp obtain tt where T: "(\<Delta>,\<Gamma> \<turnstile>\<^sub>s s' : tt \<rightarrow> Forall t) \<and> (\<Delta>,\<Gamma> \<turnstile> e' : tt)" 
          by fastforce
        with tc_tyapp have "\<Delta>,\<Gamma> \<turnstile>\<^sub>s STyApp t' # s' : tt \<rightarrow> subst\<^sub>t\<^sub>t 0 t' t" by fastforce
        with S T show ?thesis by fastforce
      qed
  next case (tcf_cons \<Delta> \<Gamma> e tt fs ts)
    thus ?case
      proof (cases "is_value e")
      case True
        with tcf_cons obtain vs' where V: "unfold_f fs = (vs', nvs, s, e') \<and> vs = e # vs'" 
          by (cases "unfold_f fs") fastforce+
        moreover with tcf_cons True obtain t t' vts nvts where T: "ts = vts @ [t] @ nvts \<and> 
          (\<Delta>,\<Gamma> \<turnstile>\<^sub>s s : t' \<rightarrow> t) \<and> (\<Delta>,\<Gamma> \<turnstile> e' : t') \<and> (\<Delta>,\<Gamma> \<turnstile>\<^sub>f vs' : vts) \<and> \<Delta>,\<Gamma> \<turnstile>\<^sub>f nvs : nvts" 
            by fastforce
        moreover hence "tt # ts = (tt # vts) @ [t] @ nvts" by simp
        moreover from tcf_cons V T have "\<Delta>,\<Gamma> \<turnstile>\<^sub>f vs : tt # vts" by simp
        ultimately show ?thesis by blast
      next case False
        with tcf_cons obtain t' where "(\<Delta>,\<Gamma> \<turnstile>\<^sub>s s : t' \<rightarrow> tt) \<and> \<Delta>,\<Gamma> \<turnstile> e' : t'" by fastforce
        moreover from tcf_cons False have "\<Delta>,\<Gamma> \<turnstile>\<^sub>f vs : []" by simp
        moreover from tcf_cons False have "\<Delta>,\<Gamma> \<turnstile>\<^sub>f nvs : ts" by simp
        ultimately show ?thesis by fastforce
      qed
  qed simp_all

end