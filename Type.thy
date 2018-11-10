theory Type
imports Main
begin

datatype kind = 
  Star
| KArrow kind kind

datatype type = 
  TyVar nat
| Arrow type type
| Record "type list"
| Variant "type list"
| Inductive kind type
| Forall kind type
| AbsTy kind type
| AppTy type type

primrec incr\<^sub>t\<^sub>t :: "nat \<Rightarrow> type \<Rightarrow> type" where
  "incr\<^sub>t\<^sub>t x (TyVar y) = TyVar (if x \<le> y then Suc y else y)"
| "incr\<^sub>t\<^sub>t x (Arrow t\<^sub>1 t\<^sub>2) = Arrow (incr\<^sub>t\<^sub>t x t\<^sub>1) (incr\<^sub>t\<^sub>t x t\<^sub>2)"
| "incr\<^sub>t\<^sub>t x (Record ts) = Record (map (incr\<^sub>t\<^sub>t x) ts)"
| "incr\<^sub>t\<^sub>t x (Variant ts) = Variant (map (incr\<^sub>t\<^sub>t x) ts)"
| "incr\<^sub>t\<^sub>t x (Inductive k t) = Inductive k (incr\<^sub>t\<^sub>t (Suc x) t)"
| "incr\<^sub>t\<^sub>t x (Forall k t) = Forall k (incr\<^sub>t\<^sub>t (Suc x) t)"
| "incr\<^sub>t\<^sub>t x (AbsTy k t) = AbsTy k (incr\<^sub>t\<^sub>t (Suc x) t)"
| "incr\<^sub>t\<^sub>t x (AppTy t\<^sub>1 t\<^sub>2) = AppTy (incr\<^sub>t\<^sub>t x t\<^sub>1) (incr\<^sub>t\<^sub>t x t\<^sub>2)"

primrec subst\<^sub>t\<^sub>t :: "nat \<Rightarrow> type \<Rightarrow> type \<Rightarrow> type" where
  "subst\<^sub>t\<^sub>t x t' (TyVar y) = (if x = y then t' else TyVar (if x < y then y - 1 else y))"
| "subst\<^sub>t\<^sub>t x t' (Arrow t\<^sub>1 t\<^sub>2) = Arrow (subst\<^sub>t\<^sub>t x t' t\<^sub>1) (subst\<^sub>t\<^sub>t x t' t\<^sub>2)"
| "subst\<^sub>t\<^sub>t x t' (Record ts) = Record (map (subst\<^sub>t\<^sub>t x t') ts)"
| "subst\<^sub>t\<^sub>t x t' (Variant ts) = Variant (map (subst\<^sub>t\<^sub>t x t') ts)"
| "subst\<^sub>t\<^sub>t x t' (Inductive k t) = Inductive k (subst\<^sub>t\<^sub>t (Suc x) (incr\<^sub>t\<^sub>t 0 t') t)"
| "subst\<^sub>t\<^sub>t x t' (Forall k t) = Forall k (subst\<^sub>t\<^sub>t (Suc x) (incr\<^sub>t\<^sub>t 0 t') t)"
| "subst\<^sub>t\<^sub>t x t' (AbsTy k t) = AbsTy k (subst\<^sub>t\<^sub>t (Suc x) (incr\<^sub>t\<^sub>t 0 t') t)"
| "subst\<^sub>t\<^sub>t x t' (AppTy t\<^sub>1 t\<^sub>2) = AppTy (subst\<^sub>t\<^sub>t x t' t\<^sub>1) (subst\<^sub>t\<^sub>t x t' t\<^sub>2)"

lemma [simp]: "y \<le> x \<Longrightarrow> incr\<^sub>t\<^sub>t y (incr\<^sub>t\<^sub>t x t) = incr\<^sub>t\<^sub>t (Suc x) (incr\<^sub>t\<^sub>t y t)"
  by (induction t arbitrary: x y) simp_all

lemma [simp]: "y \<le> x \<Longrightarrow> incr\<^sub>t\<^sub>t y o incr\<^sub>t\<^sub>t x = incr\<^sub>t\<^sub>t (Suc x) o incr\<^sub>t\<^sub>t y"
  by rule simp

lemma subst_incr_swap [simp]: "y \<le> x \<Longrightarrow> 
    subst\<^sub>t\<^sub>t y (incr\<^sub>t\<^sub>t x t') (incr\<^sub>t\<^sub>t (Suc x) t) = incr\<^sub>t\<^sub>t x (subst\<^sub>t\<^sub>t y t' t)" 
  by (induction t arbitrary: x y t') auto

lemma [simp]: "y \<le> x \<Longrightarrow> subst\<^sub>t\<^sub>t y (incr\<^sub>t\<^sub>t x t') o incr\<^sub>t\<^sub>t (Suc x) = incr\<^sub>t\<^sub>t x o subst\<^sub>t\<^sub>t y t'" 
  by rule simp

lemma [simp]: "subst\<^sub>t\<^sub>t x t' (incr\<^sub>t\<^sub>t x t) = t"
  proof (induction t arbitrary: x t')
  case (Record ts)
    thus ?case by (induction ts) simp_all
  next case (Variant ts)
    thus ?case by (induction ts) simp_all
  qed simp_all

lemma [simp]: "subst\<^sub>t\<^sub>t x t' o incr\<^sub>t\<^sub>t x = id"
  by rule simp

lemma [simp]: "y \<le> x \<Longrightarrow> incr\<^sub>t\<^sub>t y (subst\<^sub>t\<^sub>t x t' t) = subst\<^sub>t\<^sub>t (Suc x) (incr\<^sub>t\<^sub>t y t') (incr\<^sub>t\<^sub>t y t)"
  by (induction t arbitrary: x y t') auto

lemma [simp]: "y \<le> x \<Longrightarrow> incr\<^sub>t\<^sub>t y \<circ> subst\<^sub>t\<^sub>t x t' = subst\<^sub>t\<^sub>t (Suc x) (incr\<^sub>t\<^sub>t y t') \<circ> incr\<^sub>t\<^sub>t y"
  by rule simp

lemma [simp]: "y \<le> x \<Longrightarrow> 
    subst\<^sub>t\<^sub>t x t\<^sub>1' (subst\<^sub>t\<^sub>t y t\<^sub>2' t) = subst\<^sub>t\<^sub>t y (subst\<^sub>t\<^sub>t x t\<^sub>1' t\<^sub>2') (subst\<^sub>t\<^sub>t (Suc x) (incr\<^sub>t\<^sub>t y t\<^sub>1') t)"
  by (induction t arbitrary: x y t\<^sub>1' t\<^sub>2') auto

lemma [simp]: "y \<le> x \<Longrightarrow> 
    subst\<^sub>t\<^sub>t x t\<^sub>1' o subst\<^sub>t\<^sub>t y t\<^sub>2' = subst\<^sub>t\<^sub>t y (subst\<^sub>t\<^sub>t x t\<^sub>1' t\<^sub>2') o subst\<^sub>t\<^sub>t (Suc x) (incr\<^sub>t\<^sub>t y t\<^sub>1')"
  by rule simp

end