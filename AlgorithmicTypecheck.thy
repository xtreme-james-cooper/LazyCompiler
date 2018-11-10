theory AlgorithmicTypecheck
imports Typecheck
begin

fun algo_kinding :: "nat \<Rightarrow> type \<Rightarrow> bool" (infix "\<tturnstile>\<^sub>k" 60) where
  "\<Delta> \<tturnstile>\<^sub>k TyVar x = (x < \<Delta>)"
| "\<Delta> \<tturnstile>\<^sub>k Arrow t\<^sub>1 t\<^sub>2 = (\<Delta> \<tturnstile>\<^sub>k t\<^sub>1 \<and> \<Delta> \<tturnstile>\<^sub>k t\<^sub>2)"
| "\<Delta> \<tturnstile>\<^sub>k Record ts = list_all (\<lambda>t. \<Delta> \<tturnstile>\<^sub>k t) ts"
| "\<Delta> \<tturnstile>\<^sub>k Variant ts = list_all (\<lambda>t. \<Delta> \<tturnstile>\<^sub>k t) ts"
| "\<Delta> \<tturnstile>\<^sub>k Inductive t = Suc \<Delta> \<tturnstile>\<^sub>k t"
| "\<Delta> \<tturnstile>\<^sub>k Forall t = Suc \<Delta> \<tturnstile>\<^sub>k t"

fun algo_typecheck :: "nat \<Rightarrow> type list \<Rightarrow> expr \<Rightarrow> type option" (infix ",_ \<tturnstile>" 60) 
and algo_typecheck_fs :: "nat \<Rightarrow> type list \<Rightarrow> expr list \<Rightarrow> type list option" (infix ",_ \<tturnstile>\<^sub>f" 60)
and algo_typecheck_cs :: "nat \<Rightarrow> type list \<Rightarrow> expr list \<Rightarrow> type list \<Rightarrow> type \<Rightarrow> bool" 
    (infix ",_ \<tturnstile>\<^sub>c _ : _ \<rightarrow>" 60) where
  "(\<Delta>,\<Gamma> \<tturnstile> Var x) = lookup x \<Gamma>"
| "(\<Delta>,\<Gamma> \<tturnstile> Abs t\<^sub>1 e) = (case \<Delta>,insert_at 0 t\<^sub>1 \<Gamma> \<tturnstile> e of
      Some t\<^sub>2 \<Rightarrow> if \<Delta> \<tturnstile>\<^sub>k t\<^sub>1 then Some (Arrow t\<^sub>1 t\<^sub>2) else None
    | None \<Rightarrow> None)"
| "(\<Delta>,\<Gamma> \<tturnstile> App e\<^sub>1 e\<^sub>2) = (case \<Delta>,\<Gamma> \<tturnstile> e\<^sub>1 of
      Some (Arrow t\<^sub>1 t\<^sub>2) \<Rightarrow> if (\<Delta>,\<Gamma> \<tturnstile> e\<^sub>2) = Some t\<^sub>1 then Some t\<^sub>2 else None
    | _ \<Rightarrow> None)"
| "(\<Delta>,\<Gamma> \<tturnstile> Let e\<^sub>1 e\<^sub>2) = (case \<Delta>,\<Gamma> \<tturnstile> e\<^sub>1 of
       Some t\<^sub>1 \<Rightarrow> \<Delta>,insert_at 0 t\<^sub>1 \<Gamma> \<tturnstile> e\<^sub>2
    | None \<Rightarrow> None)"
| "(\<Delta>,\<Gamma> \<tturnstile> Rec fs) = (case \<Delta>,\<Gamma> \<tturnstile>\<^sub>f fs of
      Some ts \<Rightarrow> Some (Record ts)
    | None \<Rightarrow> None)"
| "(\<Delta>,\<Gamma> \<tturnstile> Proj e l) = (case \<Delta>,\<Gamma> \<tturnstile> e of
      Some (Record ts) \<Rightarrow> lookup l ts
    | _ \<Rightarrow> None)"
| "(\<Delta>,\<Gamma> \<tturnstile> Inj l ts e) = (case \<Delta>,\<Gamma> \<tturnstile> e of
      Some t \<Rightarrow> if lookup l ts = Some t \<and> list_all (\<lambda>t. \<Delta> \<tturnstile>\<^sub>k t) ts then Some (Variant ts) else None
    | None \<Rightarrow> None)"
| "(\<Delta>,\<Gamma> \<tturnstile> Case e t cs) = (case \<Delta>,\<Gamma> \<tturnstile> e of
      Some (Variant ts) \<Rightarrow> if \<Delta>,\<Gamma> \<tturnstile>\<^sub>c cs : ts \<rightarrow> t then Some t else None
    | _ \<Rightarrow> None)"
| "(\<Delta>,\<Gamma> \<tturnstile> Fold t e) = (
      if (\<Delta>,\<Gamma> \<tturnstile> e) = Some (subst\<^sub>t\<^sub>t 0 (Inductive t) t) \<and> (Suc \<Delta> \<tturnstile>\<^sub>k t) 
      then Some (Inductive t)
      else None)"
| "(\<Delta>,\<Gamma> \<tturnstile> Unfold t e) = (
      if (\<Delta>,\<Gamma> \<tturnstile> e) = Some (Inductive t) \<and> (Suc \<Delta> \<tturnstile>\<^sub>k t) 
      then Some (subst\<^sub>t\<^sub>t 0 (Inductive t) t)
      else None)" 
| "(\<Delta>,\<Gamma> \<tturnstile> TyAbs e) = (case Suc \<Delta>,map (incr\<^sub>t\<^sub>t 0) \<Gamma> \<tturnstile> e of
      Some t \<Rightarrow> Some (Forall t)
    | None \<Rightarrow> None)"
| "(\<Delta>,\<Gamma> \<tturnstile> TyApp e t') = (case \<Delta>,\<Gamma> \<tturnstile> e of
      Some (Forall t) \<Rightarrow> if \<Delta> \<tturnstile>\<^sub>k t' then Some (subst\<^sub>t\<^sub>t 0 t' t) else None
    | _ \<Rightarrow> None)"
| "(\<Delta>,\<Gamma> \<tturnstile> TyLet t' e) = (if \<Delta> \<tturnstile>\<^sub>k t' then \<Delta>,\<Gamma> \<tturnstile> subst\<^sub>t\<^sub>e 0 t' e else None)"
| "(\<Delta>,\<Gamma> \<tturnstile>\<^sub>f []) = Some []"
| "(\<Delta>,\<Gamma> \<tturnstile>\<^sub>f e # fs) = (case \<Delta>,\<Gamma> \<tturnstile> e of
      Some t \<Rightarrow> (case \<Delta>,\<Gamma> \<tturnstile>\<^sub>f fs of
          Some ts \<Rightarrow> Some (t # ts)
        | None \<Rightarrow> None)
    | None \<Rightarrow> None)"
| "(\<Delta>,\<Gamma> \<tturnstile>\<^sub>c [] : ts \<rightarrow> t) = (ts = [])"
| "(\<Delta>,\<Gamma> \<tturnstile>\<^sub>c e # cs : ts \<rightarrow> t) = (case ts of 
      t' # ts' \<Rightarrow> (\<Delta>,insert_at 0 t' \<Gamma> \<tturnstile> e) = Some t \<and> (\<Delta>,\<Gamma> \<tturnstile>\<^sub>c cs : ts' \<rightarrow> t)
    | [] \<Rightarrow> False)"

lemma [simp]: "\<Delta> \<tturnstile>\<^sub>k k = \<Delta> \<turnstile>\<^sub>k k"
  proof (induction k arbitrary: \<Delta>)
  case (Record ts)
    thus ?case by (induction ts) auto
  next case (Variant ts)
    thus ?case by (induction ts) auto
  qed auto

lemma [simp]: "((\<Delta>,\<Gamma> \<tturnstile> e) = Some t) = (\<Delta>,\<Gamma> \<turnstile> e : t)"
  and [simp]: "((\<Delta>,\<Gamma> \<tturnstile>\<^sub>f fs) = Some ts) = (\<Delta>,\<Gamma> \<turnstile>\<^sub>f fs : ts)"
  and [simp]: "(\<Delta>,\<Gamma> \<tturnstile>\<^sub>c cs : ts \<rightarrow> t) = (\<Delta>,\<Gamma> \<turnstile>\<^sub>c cs : ts \<rightarrow> t)"
  proof (induction \<Delta> \<Gamma> e and \<Delta> \<Gamma> fs and \<Delta> \<Gamma> cs ts t arbitrary: t and ts and
         rule: algo_typecheck_algo_typecheck_fs_algo_typecheck_cs.induct) 
  case (3 \<Delta> \<Gamma> e\<^sub>1 e\<^sub>2)
    thus ?case
      proof (cases "\<Delta>,\<Gamma> \<tturnstile> e\<^sub>1")
      case (Some tt)
        thus ?thesis
          proof (cases tt)
          case (Arrow t\<^sub>1 t\<^sub>2)
            from 3 Some have "\<Delta>,\<Gamma> \<turnstile> e\<^sub>1 : tt" by auto
            from 3 Some have "tt = Arrow tx210 tx220 \<Longrightarrow> (\<Delta> ,\<Gamma> \<tturnstile> e\<^sub>2 = Some ttt) = \<Delta> ,\<Gamma> \<turnstile> e\<^sub>2 : ttt" by simp
        
            have "((if (\<Delta>,\<Gamma> \<tturnstile> e\<^sub>2) = Some t\<^sub>1 then Some t\<^sub>2 else None) = Some t) = \<Delta> ,\<Gamma> \<turnstile> App e\<^sub>1 e\<^sub>2 : t" by simp
            with Some Arrow show ?thesis by simp
          next case (TyVar x)
            from 3 Some TyVar have X: "\<Delta>,\<Gamma> \<turnstile> e\<^sub>1 : TyVar x" by auto
            have "\<Delta>,\<Gamma> \<turnstile> App e\<^sub>1 e\<^sub>2 : t \<Longrightarrow> False" by simp
            with Some TyVar show ?thesis by auto
          next case Record
            from 3 Some have "\<Delta>,\<Gamma> \<turnstile> e\<^sub>1 : tt" by auto
        
            have "((case tt of Arrow t\<^sub>1 t\<^sub>2 \<Rightarrow> if (\<Delta>,\<Gamma> \<tturnstile> e\<^sub>2) = Some t\<^sub>1 then Some t\<^sub>2 else None | _ \<Rightarrow> None) = Some t) = \<Delta> ,\<Gamma> \<turnstile> App e\<^sub>1 e\<^sub>2 : t" by simp
            with Some show ?thesis by simp
          next case Variant
            from 3 Some have "\<Delta>,\<Gamma> \<turnstile> e\<^sub>1 : tt" by auto
        
            have "((case tt of Arrow t\<^sub>1 t\<^sub>2 \<Rightarrow> if (\<Delta>,\<Gamma> \<tturnstile> e\<^sub>2) = Some t\<^sub>1 then Some t\<^sub>2 else None | _ \<Rightarrow> None) = Some t) = \<Delta> ,\<Gamma> \<turnstile> App e\<^sub>1 e\<^sub>2 : t" by simp
            with Some show ?thesis by simp
          next case Inductive
            from 3 Some have "\<Delta>,\<Gamma> \<turnstile> e\<^sub>1 : tt" by auto
        
            have "((case tt of Arrow t\<^sub>1 t\<^sub>2 \<Rightarrow> if (\<Delta>,\<Gamma> \<tturnstile> e\<^sub>2) = Some t\<^sub>1 then Some t\<^sub>2 else None | _ \<Rightarrow> None) = Some t) = \<Delta> ,\<Gamma> \<turnstile> App e\<^sub>1 e\<^sub>2 : t" by simp
            with Some show ?thesis by simp
          next case Forall
            from 3 Some have "\<Delta>,\<Gamma> \<turnstile> e\<^sub>1 : tt" by auto
        
            have "((case tt of Arrow t\<^sub>1 t\<^sub>2 \<Rightarrow> if (\<Delta>,\<Gamma> \<tturnstile> e\<^sub>2) = Some t\<^sub>1 then Some t\<^sub>2 else None | _ \<Rightarrow> None) = Some t) = \<Delta> ,\<Gamma> \<turnstile> App e\<^sub>1 e\<^sub>2 : t" by simp
            with Some show ?thesis by simp
          qed
      qed auto
  next case 4
    thus ?case apply (auto split: option.splits) by simp
  next case 6
    thus ?case apply (auto split: option.splits type.splits) by simp
  next case 7
    thus ?case apply (auto split: option.splits) by simp
  next case 8
    thus ?case apply (auto split: option.splits type.splits) by simp
  next case 12
    thus ?case apply (auto split: option.splits type.splits) by simp
  next case 15
    thus ?case apply (auto split: option.splits) by simp
  qed (auto split: option.splits list.splits type.splits)

end