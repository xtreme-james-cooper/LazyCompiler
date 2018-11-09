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
  apply (induction \<Delta> \<Gamma> e t and \<Delta> \<Gamma> fs ts arbitrary: s and vs nvs s 
         rule: typecheck_typecheck_fs_typecheck_cs.inducts)
  apply (simp_all split: prod.splits if_splits)
    apply (metis tcec_nil tc_var)
    apply (metis tcec_nil tc_abs)
    apply (metis tcec_nil tc_app)
    apply (metis tcec_cons tc_frame tc_app)
    apply (metis tcec_cons tc_frame tc_app)
    apply (metis tcec_nil tc_let)
    apply (metis tcec_cons tc_frame tc_let)
    apply (metis tcec_nil tc_rec)
    (* the case for records is somewhat tougher than the others, so needs special treatment *)
    using tcec_cons tc_frame tc_rec tcf_cons typecheck_list_append apply force 
    apply (metis tcec_nil tc_proj)
    apply (metis tcec_cons tc_frame tc_proj)
    apply (metis tcec_nil tc_inj)
    apply (metis tcec_cons tc_frame tc_inj)
    apply (metis tcec_nil tc_case)
    apply (metis tcec_cons tc_frame tc_case)
    apply (metis tcec_nil tc_fold)
    apply (metis tcec_cons tc_frame tc_fold)
    apply (metis tcec_nil tc_unfold)
    apply (metis tcec_cons tc_frame tc_unfold)
    apply (metis tcec_nil tc_tyabs)
    apply (metis tcec_nil tc_tyapp)
    apply (metis tcec_cons tc_frame tc_tyapp)
    apply (metis tcec_nil tc_tylet)
    apply (metis append_Cons tcf_cons)
    apply (metis append_Nil tcf_nil)
  done

end