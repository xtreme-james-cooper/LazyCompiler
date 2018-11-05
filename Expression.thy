theory Expression
imports Type
begin

datatype expr = 
  Var nat
| Abs type expr
| App expr expr
| Rec "expr list"
| Proj expr nat
| Inj nat "type list" expr
| Case expr "expr list"

primrec incr\<^sub>e\<^sub>e :: "nat \<Rightarrow> expr \<Rightarrow> expr" where
  "incr\<^sub>e\<^sub>e x (Var y) = Var (if x \<le> y then Suc y else y)"
| "incr\<^sub>e\<^sub>e x (Abs t e) = Abs t (incr\<^sub>e\<^sub>e (Suc x) e)"
| "incr\<^sub>e\<^sub>e x (App e\<^sub>1 e\<^sub>2) = App (incr\<^sub>e\<^sub>e x e\<^sub>1) (incr\<^sub>e\<^sub>e x e\<^sub>2)"
| "incr\<^sub>e\<^sub>e x (Rec fs) = Rec (map (incr\<^sub>e\<^sub>e x) fs)"
| "incr\<^sub>e\<^sub>e x (Proj e l) = Proj (incr\<^sub>e\<^sub>e x e) l"
| "incr\<^sub>e\<^sub>e x (Inj l ts e) = Inj l ts (incr\<^sub>e\<^sub>e x e)"
| "incr\<^sub>e\<^sub>e x (Case e cs) = Case (incr\<^sub>e\<^sub>e x e) (map (incr\<^sub>e\<^sub>e (Suc x)) cs)"

primrec subst\<^sub>e\<^sub>e :: "nat \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr" where
  "subst\<^sub>e\<^sub>e x e' (Var y) = (if x = y then e' else Var (if x < y then y - 1 else y))"
| "subst\<^sub>e\<^sub>e x e' (Abs t e) = Abs t (subst\<^sub>e\<^sub>e (Suc x) (incr\<^sub>e\<^sub>e 0 e') e)"
| "subst\<^sub>e\<^sub>e x e' (App e\<^sub>1 e\<^sub>2) = App (subst\<^sub>e\<^sub>e x e' e\<^sub>1) (subst\<^sub>e\<^sub>e x e' e\<^sub>2)"
| "subst\<^sub>e\<^sub>e x e' (Rec fs) = Rec (map (subst\<^sub>e\<^sub>e x e') fs)"
| "subst\<^sub>e\<^sub>e x e' (Proj e l) = Proj (subst\<^sub>e\<^sub>e x e' e) l"
| "subst\<^sub>e\<^sub>e x e' (Inj l ts e) = Inj l ts (subst\<^sub>e\<^sub>e x e' e)"
| "subst\<^sub>e\<^sub>e x e' (Case e cs) = Case (subst\<^sub>e\<^sub>e x e' e) (map (subst\<^sub>e\<^sub>e (Suc x) (incr\<^sub>e\<^sub>e 0 e')) cs)"

primrec is_value :: "expr \<Rightarrow> bool" 
    and is_value_f :: "expr list \<Rightarrow> bool" where
  "is_value (Var y) = False"
| "is_value (Abs t e) = True"
| "is_value (App e\<^sub>1 e\<^sub>2) = False"
| "is_value (Rec fs) = is_value_f fs"
| "is_value (Proj e l) = False"
| "is_value (Inj l ts e) = is_value e"
| "is_value (Case e cs) = False"
| "is_value_f [] = True"
| "is_value_f (e # fs) = (is_value e \<and> is_value_f fs)"

end