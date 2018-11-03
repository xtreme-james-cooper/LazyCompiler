theory Expression
imports Main
begin

datatype type = 
  Base
| Arrow type type
| Record "type list"

datatype expr = 
  Var nat
| Abs type expr
| App expr expr
| Rec "expr list"
| Proj expr nat

primrec incr :: "nat \<Rightarrow> expr \<Rightarrow> expr" where
  "incr x (Var y) = Var (if x \<le> y then Suc y else y)"
| "incr x (Abs t e) = Abs t (incr (Suc x) e)"
| "incr x (App e\<^sub>1 e\<^sub>2) = App (incr x e\<^sub>1) (incr x e\<^sub>2)"
| "incr x (Rec fs) = Rec (map (incr x) fs)"
| "incr x (Proj e l) = Proj (incr x e) l"

primrec subst :: "nat \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr" where
  "subst x e' (Var y) = (if x = y then e' else Var (if x < y then y - 1 else y))"
| "subst x e' (Abs t e) = Abs t (subst (Suc x) (incr 0 e') e)"
| "subst x e' (App e\<^sub>1 e\<^sub>2) = App (subst x e' e\<^sub>1) (subst x e' e\<^sub>2)"
| "subst x e' (Rec fs) = Rec (map (subst x e') fs)"
| "subst x e' (Proj e l) = Proj (subst x e' e) l"

primrec is_value :: "expr \<Rightarrow> bool" 
    and is_value_f :: "expr list \<Rightarrow> bool" where
  "is_value (Var y) = False"
| "is_value (Abs t e) = True"
| "is_value (App e\<^sub>1 e\<^sub>2) = False"
| "is_value (Rec fs) = is_value_f fs"
| "is_value (Proj e l) = False"
| "is_value_f [] = True"
| "is_value_f (e # fs) = (is_value e \<and> is_value_f fs)"

end