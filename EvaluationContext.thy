theory EvaluationContext
imports Typecheck Misc
begin

type_synonym frame = "expr \<Rightarrow> expr"

inductive typecheck_frame :: "nat \<Rightarrow> type list \<Rightarrow> frame \<Rightarrow> type \<Rightarrow> type \<Rightarrow> bool" 
    (infix ",_ \<turnstile> _ : _ \<rightarrow>" 60) where
  tc_frame [simp]: "(\<And>e. \<Delta>,\<Gamma> \<turnstile> e : t \<Longrightarrow> \<Delta>,\<Gamma> \<turnstile> f e : t') \<Longrightarrow> \<Delta>,\<Gamma> \<turnstile> f : t \<rightarrow> t'"

inductive_cases [elim]: "\<Delta>,\<Gamma> \<turnstile> f : t \<rightarrow> t'"

inductive typecheck_context :: "nat \<Rightarrow> type list \<Rightarrow> frame list \<Rightarrow> type \<Rightarrow> type \<Rightarrow> bool" 
    (infix ",_ \<turnstile>\<^sub>e\<^sub>c _ : _ \<rightarrow>" 60) where
  tcec_nil [simp]: "\<Delta>,\<Gamma> \<turnstile>\<^sub>e\<^sub>c [] : t \<rightarrow> t"
| tcec_cons [simp]: "\<Delta>,\<Gamma> \<turnstile>\<^sub>e\<^sub>c s : t\<^sub>1 \<rightarrow> t\<^sub>2 \<Longrightarrow> \<Delta>,\<Gamma> \<turnstile> f : t\<^sub>2 \<rightarrow> t\<^sub>3 \<Longrightarrow> \<Delta>,\<Gamma> \<turnstile>\<^sub>e\<^sub>c f # s : t\<^sub>1 \<rightarrow> t\<^sub>3"

inductive_cases [elim]: "\<Delta>,\<Gamma> \<turnstile>\<^sub>e\<^sub>c [] : t \<rightarrow> t'"
inductive_cases [elim]: "\<Delta>,\<Gamma> \<turnstile>\<^sub>e\<^sub>c f # s : t \<rightarrow> t'"

fun unfold :: "expr \<Rightarrow> frame list \<times> expr" 
and unfold_f :: "expr list \<Rightarrow> expr list \<times> expr list \<times> frame list \<times> expr" where
  "unfold (Var y) = ([], Var y)"
| "unfold (Abs t e) = ([], Abs t e)"
| "unfold (App e\<^sub>1 e\<^sub>2) = (
    if is_value e\<^sub>1
    then if is_value e\<^sub>2
         then ([], App e\<^sub>1 e\<^sub>2)
         else cons_fst (App e\<^sub>1) (unfold e\<^sub>2)
    else cons_fst (\<lambda>e. App e e\<^sub>2) (unfold e\<^sub>1))"
| "unfold (Let e\<^sub>1 e\<^sub>2) = (
    if is_value e\<^sub>1
    then ([], Let e\<^sub>1 e\<^sub>2) 
    else cons_fst (\<lambda>e. Let e e\<^sub>2) (unfold e\<^sub>1))"
| "unfold (Rec fs) = (
    if is_value_f fs 
    then ([], Rec fs) 
    else case unfold_f fs of (vs, nvs, se) \<Rightarrow> cons_fst (\<lambda>e. Rec (vs @ [e] @ nvs)) se)"
| "unfold (Proj e l) = (
    if is_value e 
    then ([], Proj e l) 
    else cons_fst (\<lambda>e. Proj e l) (unfold e))"
| "unfold (Inj l ts e) = (
    if is_value e 
    then ([], Inj l ts e) 
    else cons_fst (Inj l ts) (unfold e))"
| "unfold (Case e cs) = (
    if is_value e 
    then ([], Case e cs)
    else cons_fst (\<lambda>e. Case e cs) (unfold e))"
| "unfold (Fold t e) = (
    if is_value e 
    then ([], Fold t e)
    else cons_fst (Fold t) (unfold e))"
| "unfold (Unfold t e) = (
    if is_value e 
    then ([], Unfold t e)
    else cons_fst (Unfold t) (unfold e))"
| "unfold (TyAbs e) = ([], TyAbs e)"
| "unfold (TyApp e t) = (
    if is_value e 
    then ([], TyApp e t)
    else cons_fst (\<lambda>e. TyApp e t) (unfold e))"
| "unfold (TyLet t e) = ([], TyLet t e)"
| "unfold_f [] = undefined"
| "unfold_f (e # fs) = (
    if is_value e
    then cons_fst e (unfold_f fs)
    else ([], fs, unfold e))"

fun fold :: "frame list \<Rightarrow> expr \<Rightarrow> expr" where
  "fold [] e = e"
| "fold (f # s) e = f (fold s e)"

lemma [simp]: "unfold e = (s, e') \<Longrightarrow> fold s e' = e"
  and [simp]: "unfold_f fs = (vs, nvs, s, e') \<Longrightarrow> \<not> is_value_f fs \<Longrightarrow> vs @ [fold s e'] @ nvs = fs"
  by (induction e and fs arbitrary: s e' and vs nvs s e' rule: unfold_unfold_f.induct) 
     (auto split: if_splits prod.splits)

lemma [simp]: "\<Delta>,\<Gamma> \<turnstile> f : t\<^sub>1 \<rightarrow> t\<^sub>2 \<Longrightarrow> \<Delta>,\<Gamma> \<turnstile> e : t\<^sub>1 \<Longrightarrow> \<Delta>,\<Gamma> \<turnstile> f e : t\<^sub>2"
  by (induction \<Gamma> f t\<^sub>1 t\<^sub>2 rule: typecheck_frame.induct) simp_all

lemma [simp]: "\<Delta>,\<Gamma> \<turnstile>\<^sub>e\<^sub>c s : t' \<rightarrow> t \<Longrightarrow> \<Delta>,\<Gamma> \<turnstile> e : t' \<Longrightarrow> \<Delta>,\<Gamma> \<turnstile> fold s e : t"
  by (induction \<Gamma> s t' t rule: typecheck_context.induct) auto

lemma [simp]: "\<Delta>,\<Gamma> \<turnstile> e : t \<Longrightarrow> unfold e = (s, e') \<Longrightarrow> \<exists>t'. (\<Delta>,\<Gamma> \<turnstile>\<^sub>e\<^sub>c s : t' \<rightarrow> t) \<and> (\<Delta>,\<Gamma> \<turnstile> e' : t')"
  and [simp]: "\<Delta>,\<Gamma> \<turnstile>\<^sub>f fs : ts \<Longrightarrow> \<not> is_value_f fs \<Longrightarrow> unfold_f fs = (vs, nvs, s, e') \<Longrightarrow> 
    \<exists>t t' vts nvts. ts = vts @ [t] @ nvts \<and> (\<Delta>,\<Gamma> \<turnstile>\<^sub>e\<^sub>c s : t' \<rightarrow> t) \<and> (\<Delta>,\<Gamma> \<turnstile> e' : t') \<and> 
      (\<Delta>,\<Gamma> \<turnstile>\<^sub>f vs : vts) \<and> (\<Delta>,\<Gamma> \<turnstile>\<^sub>f nvs : nvts)"
  and [simp]: "\<Delta>,\<Gamma> \<turnstile>\<^sub>c cs : ts \<rightarrow> t \<Longrightarrow> True"
  proof (induction \<Delta> \<Gamma> e t and \<Delta> \<Gamma> fs ts arbitrary: s and vs nvs s 
         rule: typecheck_typecheck_fs_typecheck_cs.inducts)
  case (tc_var x \<Gamma> t)
    thus ?case by simp (metis tcec_nil typecheck_typecheck_fs_typecheck_cs.tc_var)
  next case (tc_app \<Delta> \<Gamma> e\<^sub>1 t\<^sub>1 t\<^sub>2 e\<^sub>2)
    thus ?case 
      proof (cases "is_value e\<^sub>1")
      case True note T = True
        thus ?thesis
          proof (cases "is_value e\<^sub>2")
          case True
            with tc_app T show ?thesis 
              by simp (metis tcec_nil typecheck_typecheck_fs_typecheck_cs.tc_app)
          next case False
            with tc_app True obtain s\<^sub>2 where "unfold e\<^sub>2 = (s\<^sub>2, e') \<and> s = App e\<^sub>1 # s\<^sub>2" by fastforce
            moreover with tc_app obtain t' where "(\<Delta>,\<Gamma> \<turnstile>\<^sub>e\<^sub>c s\<^sub>2 : t' \<rightarrow> t\<^sub>1) \<and> \<Delta>,\<Gamma> \<turnstile> e' : t'" 
              by fastforce
            moreover with tc_app have "\<Delta>,\<Gamma> \<turnstile>\<^sub>e\<^sub>c App e\<^sub>1 # s\<^sub>2 : t' \<rightarrow> t\<^sub>2" by fastforce
            ultimately show ?thesis by fastforce
          qed
      next case False
        with tc_app obtain s\<^sub>1 where "unfold e\<^sub>1 = (s\<^sub>1, e') \<and> s = (\<lambda>e. App e e\<^sub>2) # s\<^sub>1" by fastforce
        moreover with tc_app obtain t' where "(\<Delta>,\<Gamma> \<turnstile>\<^sub>e\<^sub>c s\<^sub>1 : t' \<rightarrow> Arrow t\<^sub>1 t\<^sub>2) \<and> \<Delta>,\<Gamma> \<turnstile> e' : t'" 
          by fastforce
        moreover with tc_app have "\<Delta>,\<Gamma> \<turnstile>\<^sub>e\<^sub>c (\<lambda>e. App e e\<^sub>2) # s\<^sub>1 : t' \<rightarrow> t\<^sub>2" by fastforce
        ultimately show ?thesis by fastforce
      qed
  next case (tc_abs \<Delta> t\<^sub>1 \<Gamma> e t\<^sub>2)
    thus ?case by simp (metis tcec_nil typecheck_typecheck_fs_typecheck_cs.tc_abs)
  next case (tc_let \<Delta> \<Gamma> e\<^sub>1 t\<^sub>1 e\<^sub>2 t\<^sub>2)
    thus ?case
      proof (cases "is_value e\<^sub>1")
      case True
        with tc_let show ?thesis by simp (metis tcec_nil typecheck_typecheck_fs_typecheck_cs.tc_let)
      next case False
        with tc_let obtain s' where S: "unfold e\<^sub>1 = (s', e') \<and> s = (\<lambda>e. Let e e\<^sub>2) # s'"
          by (auto split: prod.splits)
        with tc_let obtain t' where "(\<Delta>,\<Gamma> \<turnstile>\<^sub>e\<^sub>c s' : t' \<rightarrow> t\<^sub>1) \<and> (\<Delta>,\<Gamma> \<turnstile> e' : t')" by fastforce
        moreover with tc_let S have X: "\<Delta>,\<Gamma> \<turnstile>\<^sub>e\<^sub>c s : t' \<rightarrow> t\<^sub>2" by fastforce
        ultimately show ?thesis by fastforce
      qed
  next case (tc_rec \<Delta> \<Gamma> fs ts)
    thus ?case 
      proof (cases "is_value_f fs")
      case True
        with tc_rec show ?thesis by simp (metis tcec_nil typecheck_typecheck_fs_typecheck_cs.tc_rec)
      next case False
        then obtain vs nvs ss ee' where F: "unfold_f fs = (vs, nvs, ss, ee')" 
          by (cases "unfold_f fs") simp_all
        with tc_rec False obtain t t' vts nvts where T: "ts = vts @ [t] @ nvts \<and> 
          (\<Delta>,\<Gamma> \<turnstile>\<^sub>e\<^sub>c ss : t' \<rightarrow> t) \<and> (\<Delta>,\<Gamma> \<turnstile> e' : t') \<and> (\<Delta>,\<Gamma> \<turnstile>\<^sub>f vs : vts) \<and> \<Delta>,\<Gamma> \<turnstile>\<^sub>f nvs : nvts" 
            by fastforce
        hence "\<Delta>,\<Gamma> \<turnstile>\<^sub>e\<^sub>c (\<lambda>e. Rec (vs @ [e] @ nvs)) # ss : t' \<rightarrow> Record ts" by fastforce
        with tc_rec False F T show ?thesis by fastforce
      qed
  next case (tc_proj \<Delta> \<Gamma> e ts l t)
    thus ?case
      proof (cases "is_value e")
      case True
        with tc_proj show ?thesis by simp (metis tcec_nil typecheck_typecheck_fs_typecheck_cs.tc_proj)
      next case False
        with tc_proj obtain ss where "unfold e = (ss, e') \<and> s = (\<lambda>e. Proj e l) # ss" 
          by (auto split: prod.splits)
        moreover with tc_proj obtain t' where "(\<Delta>,\<Gamma> \<turnstile>\<^sub>e\<^sub>c ss : t' \<rightarrow> Record ts) \<and> (\<Delta>,\<Gamma> \<turnstile> e' : t')" 
          by fastforce
        moreover with tc_proj have "\<Delta>,\<Gamma> \<turnstile>\<^sub>e\<^sub>c (\<lambda>e. Proj e l) # ss : t' \<rightarrow> t" by fastforce
        ultimately show ?thesis by fastforce
      qed
  next case (tc_inj \<Delta> \<Gamma> e t l ts)
    thus ?case
      proof (cases "is_value e")
      case True
        with tc_inj show ?thesis by simp (metis tcec_nil typecheck_typecheck_fs_typecheck_cs.tc_inj)
      next case False
        with tc_inj obtain s' where S: "unfold e = (s', e') \<and> s = Inj l ts # s'" 
          by (auto split: prod.splits)
        with tc_inj obtain t' where "(\<Delta>,\<Gamma> \<turnstile>\<^sub>e\<^sub>c s' : t' \<rightarrow> t) \<and> (\<Delta>,\<Gamma> \<turnstile> e' : t')" by fastforce
        moreover with tc_inj S have "\<Delta>,\<Gamma> \<turnstile>\<^sub>e\<^sub>c s : t' \<rightarrow> Variant ts" by fastforce
        ultimately show ?thesis by fastforce
      qed
  next case (tc_case \<Delta> \<Gamma> e ts cs t)
    thus ?case
      proof (cases "is_value e")
      case True
        with tc_case show ?thesis by simp (metis tcec_nil typecheck_typecheck_fs_typecheck_cs.tc_case)
      next case False
        with tc_case obtain s' where S: "unfold e = (s', e') \<and> s = (\<lambda>e. Case e cs) # s'" 
          by (auto split: prod.splits)
        with tc_case obtain t' where T: "(\<Delta>,\<Gamma> \<turnstile>\<^sub>e\<^sub>c s' : t' \<rightarrow> Variant ts) \<and> (\<Delta>,\<Gamma> \<turnstile> e' : t')" 
          by fastforce
        with tc_case S have "\<Delta>,\<Gamma> \<turnstile>\<^sub>e\<^sub>c s : t' \<rightarrow> t" by fastforce
        with T show ?thesis by fastforce
      qed
  next case (tc_fold \<Delta> \<Gamma> e t)
    thus ?case
      proof (cases "is_value e")
      case True
        with tc_fold show ?thesis by simp (metis tcec_nil typecheck_typecheck_fs_typecheck_cs.tc_fold)
      next case False
        with tc_fold obtain s' where S: "unfold e = (s', e') \<and> s = Fold t # s'"
          by (auto split: prod.splits)
        with tc_fold obtain t' where T: "(\<Delta>,\<Gamma> \<turnstile>\<^sub>e\<^sub>c s' : t' \<rightarrow> subst\<^sub>t\<^sub>t 0 (Inductive t) t) \<and> 
          (\<Delta>,\<Gamma> \<turnstile> e' : t')" by fastforce
        with tc_fold S have "\<Delta>,\<Gamma> \<turnstile>\<^sub>e\<^sub>c s : t' \<rightarrow> Inductive t" by fastforce
        with T show ?thesis by fastforce
      qed
  next case (tc_unfold \<Delta> \<Gamma> e t)
    thus ?case
      proof (cases "is_value e")
      case True
        with tc_unfold show ?thesis 
          by simp (metis tcec_nil typecheck_typecheck_fs_typecheck_cs.tc_unfold)
      next case False
        with tc_unfold obtain s' where S: "unfold e = (s', e') \<and> s = Unfold t # s'"
          by (auto split: prod.splits)
        with tc_unfold obtain t' where T: "(\<Delta>,\<Gamma> \<turnstile>\<^sub>e\<^sub>c s' : t' \<rightarrow> Inductive t) \<and> 
          (\<Delta>,\<Gamma> \<turnstile> e' : t')" by fastforce
        with tc_unfold S have "\<Delta>,\<Gamma> \<turnstile>\<^sub>e\<^sub>c s : t' \<rightarrow> subst\<^sub>t\<^sub>t 0 (Inductive t) t" by fastforce
        with T show ?thesis by fastforce
      qed
  next case (tc_tyabs \<Delta> \<Gamma> e t)
    thus ?case by simp (metis tcec_nil typecheck_typecheck_fs_typecheck_cs.tc_tyabs)
  next case (tc_tyapp \<Delta> \<Gamma> e t t')
    thus ?case
      proof (cases "is_value e")
      case True
        with tc_tyapp show ?thesis 
          by simp (metis tcec_nil typecheck_typecheck_fs_typecheck_cs.tc_tyapp)
      next case False
        with tc_tyapp obtain s' where S: "unfold e = (s', e') \<and> s = (\<lambda>e. TyApp e t') # s'" 
          by (auto split: prod.splits)
        with tc_tyapp obtain tt where T: "(\<Delta>,\<Gamma> \<turnstile>\<^sub>e\<^sub>c s' : tt \<rightarrow> Forall t) \<and> (\<Delta>,\<Gamma> \<turnstile> e' : tt)" 
          by fastforce
        with tc_tyapp have "\<Delta>,\<Gamma> \<turnstile>\<^sub>e\<^sub>c (\<lambda>e. TyApp e t') # s' : tt \<rightarrow> subst\<^sub>t\<^sub>t 0 t' t" by fastforce
        with S T show ?thesis by fastforce
      qed
  next case (tc_tylet \<Delta> \<Gamma> t' e t)
    thus ?case by simp (metis tcec_nil typecheck_typecheck_fs_typecheck_cs.tc_tylet)
  next case (tcf_cons \<Delta> \<Gamma> e tt fs ts)
    thus ?case
      proof (cases "is_value e")
      case True
        with tcf_cons obtain vs' where V: "unfold_f fs = (vs', nvs, s, e') \<and> vs = e # vs'" 
          by (cases "unfold_f fs") fastforce+
        moreover with tcf_cons True obtain t t' vts nvts where T: "ts = vts @ [t] @ nvts \<and> 
          (\<Delta>,\<Gamma> \<turnstile>\<^sub>e\<^sub>c s : t' \<rightarrow> t) \<and> (\<Delta>,\<Gamma> \<turnstile> e' : t') \<and> (\<Delta>,\<Gamma> \<turnstile>\<^sub>f vs' : vts) \<and> \<Delta>,\<Gamma> \<turnstile>\<^sub>f nvs : nvts" 
            by fastforce
        moreover hence "tt # ts = (tt # vts) @ [t] @ nvts" by simp
        moreover from tcf_cons V T have "\<Delta>,\<Gamma> \<turnstile>\<^sub>f vs : tt # vts" by simp
        ultimately show ?thesis by blast
      next case False
        with tcf_cons obtain t' where "(\<Delta>,\<Gamma> \<turnstile>\<^sub>e\<^sub>c s : t' \<rightarrow> tt) \<and> \<Delta>,\<Gamma> \<turnstile> e' : t'" by fastforce
        moreover from tcf_cons False have "\<Delta>,\<Gamma> \<turnstile>\<^sub>f vs : []" by simp
        moreover from tcf_cons False have "\<Delta>,\<Gamma> \<turnstile>\<^sub>f nvs : ts" by simp
        ultimately show ?thesis by fastforce
      qed
  qed simp_all

end