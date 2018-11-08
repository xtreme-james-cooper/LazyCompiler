theory Expression
imports Type
begin

datatype expr = 
  Var nat
| Abs type expr
| App expr expr
| Let expr expr
| Rec "expr list"
| Proj expr nat
| Inj nat "type list" expr
| Case expr "expr list"
| Fold type expr
| Unfold type expr
| TyAbs expr
| TyApp expr type

primrec incr\<^sub>t\<^sub>e :: "nat \<Rightarrow> expr \<Rightarrow> expr" where
  "incr\<^sub>t\<^sub>e x (Var y) = Var y"
| "incr\<^sub>t\<^sub>e x (Abs t e) = Abs (incr\<^sub>t\<^sub>t x t) (incr\<^sub>t\<^sub>e x e)"
| "incr\<^sub>t\<^sub>e x (App e\<^sub>1 e\<^sub>2) = App (incr\<^sub>t\<^sub>e x e\<^sub>1) (incr\<^sub>t\<^sub>e x e\<^sub>2)"
| "incr\<^sub>t\<^sub>e x (Let e\<^sub>1 e\<^sub>2) = Let (incr\<^sub>t\<^sub>e x e\<^sub>1) (incr\<^sub>t\<^sub>e x e\<^sub>2)"
| "incr\<^sub>t\<^sub>e x (Rec fs) = Rec (map (incr\<^sub>t\<^sub>e x) fs)"
| "incr\<^sub>t\<^sub>e x (Proj e l) = Proj (incr\<^sub>t\<^sub>e x e) l"
| "incr\<^sub>t\<^sub>e x (Inj l ts e) = Inj l (map (incr\<^sub>t\<^sub>t x) ts) (incr\<^sub>t\<^sub>e x e)"
| "incr\<^sub>t\<^sub>e x (Case e cs) = Case (incr\<^sub>t\<^sub>e x e) (map (incr\<^sub>t\<^sub>e x) cs)"
| "incr\<^sub>t\<^sub>e x (Fold t e) = Fold (incr\<^sub>t\<^sub>t (Suc x) t) (incr\<^sub>t\<^sub>e x e)"
| "incr\<^sub>t\<^sub>e x (Unfold t e) = Unfold (incr\<^sub>t\<^sub>t (Suc x) t) (incr\<^sub>t\<^sub>e x e)"
| "incr\<^sub>t\<^sub>e x (TyAbs e) = TyAbs (incr\<^sub>t\<^sub>e (Suc x) e)"
| "incr\<^sub>t\<^sub>e x (TyApp e t) = TyApp (incr\<^sub>t\<^sub>e x e) (incr\<^sub>t\<^sub>t x t)"

primrec subst\<^sub>t\<^sub>e :: "nat \<Rightarrow> type \<Rightarrow> expr \<Rightarrow> expr" where
  "subst\<^sub>t\<^sub>e x t' (Var y) = Var y"
| "subst\<^sub>t\<^sub>e x t' (Abs t e) = Abs (subst\<^sub>t\<^sub>t x t' t) (subst\<^sub>t\<^sub>e x t' e)"
| "subst\<^sub>t\<^sub>e x t' (App e\<^sub>1 e\<^sub>2) = App (subst\<^sub>t\<^sub>e x t' e\<^sub>1) (subst\<^sub>t\<^sub>e x t' e\<^sub>2)"
| "subst\<^sub>t\<^sub>e x t' (Let e\<^sub>1 e\<^sub>2) = Let (subst\<^sub>t\<^sub>e x t' e\<^sub>1) (subst\<^sub>t\<^sub>e x t' e\<^sub>2)"
| "subst\<^sub>t\<^sub>e x t' (Rec fs) = Rec (map (subst\<^sub>t\<^sub>e x t') fs)"
| "subst\<^sub>t\<^sub>e x t' (Proj e l) = Proj (subst\<^sub>t\<^sub>e x t' e) l"
| "subst\<^sub>t\<^sub>e x t' (Inj l ts e) = Inj l (map (subst\<^sub>t\<^sub>t x t') ts) (subst\<^sub>t\<^sub>e x t' e)"
| "subst\<^sub>t\<^sub>e x t' (Case e cs) = Case (subst\<^sub>t\<^sub>e x t' e) (map (subst\<^sub>t\<^sub>e x t') cs)"
| "subst\<^sub>t\<^sub>e x t' (Fold t e) = Fold (subst\<^sub>t\<^sub>t (Suc x) (incr\<^sub>t\<^sub>t 0 t') t) (subst\<^sub>t\<^sub>e x t' e)"
| "subst\<^sub>t\<^sub>e x t' (Unfold t e) = Unfold (subst\<^sub>t\<^sub>t (Suc x) (incr\<^sub>t\<^sub>t 0 t') t) (subst\<^sub>t\<^sub>e x t' e)"
| "subst\<^sub>t\<^sub>e x t' (TyAbs e) = TyAbs (subst\<^sub>t\<^sub>e (Suc x) (incr\<^sub>t\<^sub>t 0 t') e)"
| "subst\<^sub>t\<^sub>e x t' (TyApp e t) = TyApp (subst\<^sub>t\<^sub>e x t' e) (subst\<^sub>t\<^sub>t x t' t)"

primrec incr\<^sub>e\<^sub>e :: "nat \<Rightarrow> expr \<Rightarrow> expr" where
  "incr\<^sub>e\<^sub>e x (Var y) = Var (if x \<le> y then Suc y else y)"
| "incr\<^sub>e\<^sub>e x (Abs t e) = Abs t (incr\<^sub>e\<^sub>e (Suc x) e)"
| "incr\<^sub>e\<^sub>e x (App e\<^sub>1 e\<^sub>2) = App (incr\<^sub>e\<^sub>e x e\<^sub>1) (incr\<^sub>e\<^sub>e x e\<^sub>2)"
| "incr\<^sub>e\<^sub>e x (Let e\<^sub>1 e\<^sub>2) = Let (incr\<^sub>e\<^sub>e x e\<^sub>1) (incr\<^sub>e\<^sub>e (Suc x) e\<^sub>2)"
| "incr\<^sub>e\<^sub>e x (Rec fs) = Rec (map (incr\<^sub>e\<^sub>e x) fs)"
| "incr\<^sub>e\<^sub>e x (Proj e l) = Proj (incr\<^sub>e\<^sub>e x e) l"
| "incr\<^sub>e\<^sub>e x (Inj l ts e) = Inj l ts (incr\<^sub>e\<^sub>e x e)"
| "incr\<^sub>e\<^sub>e x (Case e cs) = Case (incr\<^sub>e\<^sub>e x e) (map (incr\<^sub>e\<^sub>e (Suc x)) cs)"
| "incr\<^sub>e\<^sub>e x (Fold t e) = Fold t (incr\<^sub>e\<^sub>e x e)"
| "incr\<^sub>e\<^sub>e x (Unfold t e) = Unfold t (incr\<^sub>e\<^sub>e x e)"
| "incr\<^sub>e\<^sub>e x (TyAbs e) = TyAbs (incr\<^sub>e\<^sub>e x e)"
| "incr\<^sub>e\<^sub>e x (TyApp e t) = TyApp (incr\<^sub>e\<^sub>e x e) t"

primrec subst\<^sub>e\<^sub>e :: "nat \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr" where
  "subst\<^sub>e\<^sub>e x e' (Var y) = (if x = y then e' else Var (if x < y then y - 1 else y))"
| "subst\<^sub>e\<^sub>e x e' (Abs t e) = Abs t (subst\<^sub>e\<^sub>e (Suc x) (incr\<^sub>e\<^sub>e 0 e') e)"
| "subst\<^sub>e\<^sub>e x e' (App e\<^sub>1 e\<^sub>2) = App (subst\<^sub>e\<^sub>e x e' e\<^sub>1) (subst\<^sub>e\<^sub>e x e' e\<^sub>2)"
| "subst\<^sub>e\<^sub>e x e' (Let e\<^sub>1 e\<^sub>2) = Let (subst\<^sub>e\<^sub>e x e' e\<^sub>1) (subst\<^sub>e\<^sub>e (Suc x) (incr\<^sub>e\<^sub>e 0 e') e\<^sub>2)"
| "subst\<^sub>e\<^sub>e x e' (Rec fs) = Rec (map (subst\<^sub>e\<^sub>e x e') fs)"
| "subst\<^sub>e\<^sub>e x e' (Proj e l) = Proj (subst\<^sub>e\<^sub>e x e' e) l"
| "subst\<^sub>e\<^sub>e x e' (Inj l ts e) = Inj l ts (subst\<^sub>e\<^sub>e x e' e)"
| "subst\<^sub>e\<^sub>e x e' (Case e cs) = Case (subst\<^sub>e\<^sub>e x e' e) (map (subst\<^sub>e\<^sub>e (Suc x) (incr\<^sub>e\<^sub>e 0 e')) cs)"
| "subst\<^sub>e\<^sub>e x e' (Fold t e) = Fold t (subst\<^sub>e\<^sub>e x e' e)"
| "subst\<^sub>e\<^sub>e x e' (Unfold t e) = Unfold t (subst\<^sub>e\<^sub>e x e' e)"
| "subst\<^sub>e\<^sub>e x e' (TyAbs e) = TyAbs (subst\<^sub>e\<^sub>e x (incr\<^sub>t\<^sub>e 0 e') e)"
| "subst\<^sub>e\<^sub>e x e' (TyApp e t) = TyApp (subst\<^sub>e\<^sub>e x e' e) t"

primrec is_value :: "expr \<Rightarrow> bool" 
    and is_value_f :: "expr list \<Rightarrow> bool" where
  "is_value (Var y) = False"
| "is_value (Abs t e) = True"
| "is_value (App e\<^sub>1 e\<^sub>2) = False"
| "is_value (Let e\<^sub>1 e\<^sub>2) = False"
| "is_value (Rec fs) = is_value_f fs"
| "is_value (Proj e l) = False"
| "is_value (Inj l ts e) = is_value e"
| "is_value (Case e cs) = False"
| "is_value (Fold t e) = is_value e"
| "is_value (Unfold t e) = False"
| "is_value (TyAbs e) = True"
| "is_value (TyApp e t) = False"
| "is_value_f [] = True"
| "is_value_f (e # fs) = (is_value e \<and> is_value_f fs)"

end