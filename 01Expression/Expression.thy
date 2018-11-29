theory Expression
imports Type "../Utilities/Index"
begin

datatype expr = 
  Var nat
| Abs type expr
| App expr expr
| Let expr expr
| Rec "nat list"
| Proj expr nat
| Inj nat "type list" nat
| Case expr type "expr list"
| Fold type nat
| Unfold type expr
| TyAbs kind expr
| TyApp expr type
| TyLet type expr

primrec incr\<^sub>t\<^sub>e :: "nat \<Rightarrow> expr \<Rightarrow> expr" where
  "incr\<^sub>t\<^sub>e x (Var y) = Var y"
| "incr\<^sub>t\<^sub>e x (Abs t e) = Abs (incr\<^sub>t\<^sub>t x t) (incr\<^sub>t\<^sub>e x e)"
| "incr\<^sub>t\<^sub>e x (App e\<^sub>1 e\<^sub>2) = App (incr\<^sub>t\<^sub>e x e\<^sub>1) (incr\<^sub>t\<^sub>e x e\<^sub>2)"
| "incr\<^sub>t\<^sub>e x (Let e\<^sub>1 e\<^sub>2) = Let (incr\<^sub>t\<^sub>e x e\<^sub>1) (incr\<^sub>t\<^sub>e x e\<^sub>2)"
| "incr\<^sub>t\<^sub>e x (Rec xs) = Rec xs"
| "incr\<^sub>t\<^sub>e x (Proj e l) = Proj (incr\<^sub>t\<^sub>e x e) l"
| "incr\<^sub>t\<^sub>e x (Inj l ts y) = Inj l (map (incr\<^sub>t\<^sub>t x) ts) y"
| "incr\<^sub>t\<^sub>e x (Case e t cs) = Case (incr\<^sub>t\<^sub>e x e) (incr\<^sub>t\<^sub>t x t) (map (incr\<^sub>t\<^sub>e x) cs)"
| "incr\<^sub>t\<^sub>e x (Fold t y) = Fold (incr\<^sub>t\<^sub>t (Suc x) t) y"
| "incr\<^sub>t\<^sub>e x (Unfold t e) = Unfold (incr\<^sub>t\<^sub>t (Suc x) t) (incr\<^sub>t\<^sub>e x e)"
| "incr\<^sub>t\<^sub>e x (TyAbs k e) = TyAbs k (incr\<^sub>t\<^sub>e (Suc x) e)"
| "incr\<^sub>t\<^sub>e x (TyApp e t) = TyApp (incr\<^sub>t\<^sub>e x e) (incr\<^sub>t\<^sub>t x t)"
| "incr\<^sub>t\<^sub>e x (TyLet t e) = TyLet (incr\<^sub>t\<^sub>t x t) (incr\<^sub>t\<^sub>e (Suc x) e)"

primrec subst\<^sub>t\<^sub>e :: "nat \<Rightarrow> type \<Rightarrow> expr \<Rightarrow> expr" where
  "subst\<^sub>t\<^sub>e x t' (Var y) = Var y"
| "subst\<^sub>t\<^sub>e x t' (Abs t e) = Abs (subst\<^sub>t\<^sub>t x t' t) (subst\<^sub>t\<^sub>e x t' e)"
| "subst\<^sub>t\<^sub>e x t' (App e\<^sub>1 e\<^sub>2) = App (subst\<^sub>t\<^sub>e x t' e\<^sub>1) (subst\<^sub>t\<^sub>e x t' e\<^sub>2)"
| "subst\<^sub>t\<^sub>e x t' (Let e\<^sub>1 e\<^sub>2) = Let (subst\<^sub>t\<^sub>e x t' e\<^sub>1) (subst\<^sub>t\<^sub>e x t' e\<^sub>2)"
| "subst\<^sub>t\<^sub>e x t' (Rec xs) = Rec xs"
| "subst\<^sub>t\<^sub>e x t' (Proj e l) = Proj (subst\<^sub>t\<^sub>e x t' e) l"
| "subst\<^sub>t\<^sub>e x t' (Inj l ts y) = Inj l (map (subst\<^sub>t\<^sub>t x t') ts) y"
| "subst\<^sub>t\<^sub>e x t' (Case e t cs) = Case (subst\<^sub>t\<^sub>e x t' e) (subst\<^sub>t\<^sub>t x t' t) (map (subst\<^sub>t\<^sub>e x t') cs)"
| "subst\<^sub>t\<^sub>e x t' (Fold t y) = Fold (subst\<^sub>t\<^sub>t (Suc x) (incr\<^sub>t\<^sub>t 0 t') t) y"
| "subst\<^sub>t\<^sub>e x t' (Unfold t e) = Unfold (subst\<^sub>t\<^sub>t (Suc x) (incr\<^sub>t\<^sub>t 0 t') t) (subst\<^sub>t\<^sub>e x t' e)"
| "subst\<^sub>t\<^sub>e x t' (TyAbs k e) = TyAbs k (subst\<^sub>t\<^sub>e (Suc x) (incr\<^sub>t\<^sub>t 0 t') e)"
| "subst\<^sub>t\<^sub>e x t' (TyApp e t) = TyApp (subst\<^sub>t\<^sub>e x t' e) (subst\<^sub>t\<^sub>t x t' t)"
| "subst\<^sub>t\<^sub>e x t' (TyLet t e) = TyLet (subst\<^sub>t\<^sub>t x t' t) (subst\<^sub>t\<^sub>e (Suc x) (incr\<^sub>t\<^sub>t 0 t') e)"

primrec subst\<^sub>x\<^sub>e :: "nat \<Rightarrow> nat \<Rightarrow> expr \<Rightarrow> expr" where
  "subst\<^sub>x\<^sub>e x x' (Var y) = Var (if x = y then x' else decr x y)"
| "subst\<^sub>x\<^sub>e x x' (Abs t e) = Abs t (subst\<^sub>x\<^sub>e (Suc x) (Suc x') e)"
| "subst\<^sub>x\<^sub>e x x' (App e\<^sub>1 e\<^sub>2) = App (subst\<^sub>x\<^sub>e x x' e\<^sub>1) (subst\<^sub>x\<^sub>e x x' e\<^sub>2)"
| "subst\<^sub>x\<^sub>e x x' (Let e\<^sub>1 e\<^sub>2) = Let (subst\<^sub>x\<^sub>e x x' e\<^sub>1) (subst\<^sub>x\<^sub>e (Suc x) (Suc x') e\<^sub>2)"
| "subst\<^sub>x\<^sub>e x x' (Rec ys) = Rec (map (\<lambda>y. if x = y then x' else decr x y) ys)"
| "subst\<^sub>x\<^sub>e x x' (Proj e l) = Proj (subst\<^sub>x\<^sub>e x x' e) l"
| "subst\<^sub>x\<^sub>e x x' (Inj l ts y) = Inj l ts (if x = y then x' else decr x y)"
| "subst\<^sub>x\<^sub>e x x' (Case e t cs) = Case (subst\<^sub>x\<^sub>e x x' e) t (map (subst\<^sub>x\<^sub>e (Suc x) (Suc x')) cs)"
| "subst\<^sub>x\<^sub>e x x' (Fold t y) = Fold t (if x = y then x' else decr x y)"
| "subst\<^sub>x\<^sub>e x x' (Unfold t e) = Unfold t (subst\<^sub>x\<^sub>e x x' e)"
| "subst\<^sub>x\<^sub>e x x' (TyAbs k e) = TyAbs k (subst\<^sub>x\<^sub>e x x' e)"
| "subst\<^sub>x\<^sub>e x x' (TyApp e t) = TyApp (subst\<^sub>x\<^sub>e x x' e) t"
| "subst\<^sub>x\<^sub>e x x' (TyLet t e) = TyLet t (subst\<^sub>x\<^sub>e x x' e)"

definition extend_var_map :: "nat list \<Rightarrow> nat list" where
  "extend_var_map xs = 0 # map Suc xs"

primrec subst\<^sub>x\<^sub>e\<^sub>s :: "nat list \<Rightarrow> expr \<Rightarrow> expr" where
  "subst\<^sub>x\<^sub>e\<^sub>s xs (Var y) = Var (the (lookup xs y))"
| "subst\<^sub>x\<^sub>e\<^sub>s xs (Abs t e) = Abs t (subst\<^sub>x\<^sub>e\<^sub>s (extend_var_map xs) e)"
| "subst\<^sub>x\<^sub>e\<^sub>s xs (App e\<^sub>1 e\<^sub>2) = App (subst\<^sub>x\<^sub>e\<^sub>s xs e\<^sub>1) (subst\<^sub>x\<^sub>e\<^sub>s xs e\<^sub>2)"
| "subst\<^sub>x\<^sub>e\<^sub>s xs (Let e\<^sub>1 e\<^sub>2) = Let (subst\<^sub>x\<^sub>e\<^sub>s xs e\<^sub>1) (subst\<^sub>x\<^sub>e\<^sub>s (extend_var_map xs) e\<^sub>2)"
| "subst\<^sub>x\<^sub>e\<^sub>s xs (Rec ys) = Rec (map (\<lambda>y. the (lookup xs y)) ys)"
| "subst\<^sub>x\<^sub>e\<^sub>s xs (Proj e l) = Proj (subst\<^sub>x\<^sub>e\<^sub>s xs e) l"
| "subst\<^sub>x\<^sub>e\<^sub>s xs (Inj l ts y) = Inj l ts (the (lookup xs y))"
| "subst\<^sub>x\<^sub>e\<^sub>s xs (Case e t cs) = Case (subst\<^sub>x\<^sub>e\<^sub>s xs e) t (map (subst\<^sub>x\<^sub>e\<^sub>s (extend_var_map xs)) cs)"
| "subst\<^sub>x\<^sub>e\<^sub>s xs (Fold t y) = Fold t (the (lookup xs y))"
| "subst\<^sub>x\<^sub>e\<^sub>s xs (Unfold t e) = Unfold t (subst\<^sub>x\<^sub>e\<^sub>s xs e)"
| "subst\<^sub>x\<^sub>e\<^sub>s xs (TyAbs k e) = TyAbs k (subst\<^sub>x\<^sub>e\<^sub>s xs e)"
| "subst\<^sub>x\<^sub>e\<^sub>s xs (TyApp e t) = TyApp (subst\<^sub>x\<^sub>e\<^sub>s xs e) t"
| "subst\<^sub>x\<^sub>e\<^sub>s xs (TyLet t e) = TyLet t (subst\<^sub>x\<^sub>e\<^sub>s xs e)"

primrec decr\<^sub>x\<^sub>e :: "nat \<Rightarrow> expr \<Rightarrow> expr" where
  "decr\<^sub>x\<^sub>e x (Var y) = Var (decr x y)"
| "decr\<^sub>x\<^sub>e x (Abs t e) = Abs t (decr\<^sub>x\<^sub>e (Suc x) e)"
| "decr\<^sub>x\<^sub>e x (App e\<^sub>1 e\<^sub>2) = App (decr\<^sub>x\<^sub>e x e\<^sub>1) (decr\<^sub>x\<^sub>e x e\<^sub>2)"
| "decr\<^sub>x\<^sub>e x (Let e\<^sub>1 e\<^sub>2) = Let (decr\<^sub>x\<^sub>e x e\<^sub>1) (decr\<^sub>x\<^sub>e (Suc x) e\<^sub>2)"
| "decr\<^sub>x\<^sub>e x (Rec ys) = Rec (map (decr x) ys)"
| "decr\<^sub>x\<^sub>e x (Proj e l) = Proj (decr\<^sub>x\<^sub>e x e) l"
| "decr\<^sub>x\<^sub>e x (Inj l ts y) = Inj l ts (decr x y)"
| "decr\<^sub>x\<^sub>e x (Case e t cs) = Case (decr\<^sub>x\<^sub>e x e) t (map (decr\<^sub>x\<^sub>e (Suc x)) cs)"
| "decr\<^sub>x\<^sub>e x (Fold t y) = Fold t (decr x y)"
| "decr\<^sub>x\<^sub>e x (Unfold t e) = Unfold t (decr\<^sub>x\<^sub>e x e)"
| "decr\<^sub>x\<^sub>e x (TyAbs k e) = TyAbs k (decr\<^sub>x\<^sub>e x e)"
| "decr\<^sub>x\<^sub>e x (TyApp e t) = TyApp (decr\<^sub>x\<^sub>e x e) t"
| "decr\<^sub>x\<^sub>e x (TyLet t e) = TyLet t (decr\<^sub>x\<^sub>e x e)"

primrec incr\<^sub>e\<^sub>e :: "nat \<Rightarrow> expr \<Rightarrow> expr" where
  "incr\<^sub>e\<^sub>e x (Var y) = Var (incr x y)"
| "incr\<^sub>e\<^sub>e x (Abs t e) = Abs t (incr\<^sub>e\<^sub>e (Suc x) e)"
| "incr\<^sub>e\<^sub>e x (App e\<^sub>1 e\<^sub>2) = App (incr\<^sub>e\<^sub>e x e\<^sub>1) (incr\<^sub>e\<^sub>e x e\<^sub>2)"
| "incr\<^sub>e\<^sub>e x (Let e\<^sub>1 e\<^sub>2) = Let (incr\<^sub>e\<^sub>e x e\<^sub>1) (incr\<^sub>e\<^sub>e (Suc x) e\<^sub>2)"
| "incr\<^sub>e\<^sub>e x (Rec ys) = Rec (map (incr x) ys)"
| "incr\<^sub>e\<^sub>e x (Proj e l) = Proj (incr\<^sub>e\<^sub>e x e) l"
| "incr\<^sub>e\<^sub>e x (Inj l ts y) = Inj l ts (incr x y)"
| "incr\<^sub>e\<^sub>e x (Case e t cs) = Case (incr\<^sub>e\<^sub>e x e) t (map (incr\<^sub>e\<^sub>e (Suc x)) cs)"
| "incr\<^sub>e\<^sub>e x (Fold t y) = Fold t (incr x y)"
| "incr\<^sub>e\<^sub>e x (Unfold t e) = Unfold t (incr\<^sub>e\<^sub>e x e)"
| "incr\<^sub>e\<^sub>e x (TyAbs k e) = TyAbs k (incr\<^sub>e\<^sub>e x e)"
| "incr\<^sub>e\<^sub>e x (TyApp e t) = TyApp (incr\<^sub>e\<^sub>e x e) t"
| "incr\<^sub>e\<^sub>e x (TyLet t e) = TyLet t (incr\<^sub>e\<^sub>e x e)"

primrec subst\<^sub>e\<^sub>e :: "nat \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr" where
  "subst\<^sub>e\<^sub>e x e' (Var y) = (if x = y then e' else Var y)"
| "subst\<^sub>e\<^sub>e x e' (Abs t e) = Abs t (subst\<^sub>e\<^sub>e (Suc x) (incr\<^sub>e\<^sub>e 0 e') e)"
| "subst\<^sub>e\<^sub>e x e' (App e\<^sub>1 e\<^sub>2) = App (subst\<^sub>e\<^sub>e x e' e\<^sub>1) (subst\<^sub>e\<^sub>e x e' e\<^sub>2)"
| "subst\<^sub>e\<^sub>e x e' (Let e\<^sub>1 e\<^sub>2) = Let (subst\<^sub>e\<^sub>e x e' e\<^sub>1) (subst\<^sub>e\<^sub>e (Suc x) (incr\<^sub>e\<^sub>e 0 e') e\<^sub>2)"
| "subst\<^sub>e\<^sub>e x e' (Rec ys) = Rec ys"
| "subst\<^sub>e\<^sub>e x e' (Proj e l) = Proj (subst\<^sub>e\<^sub>e x e' e) l"
| "subst\<^sub>e\<^sub>e x e' (Inj l ts y) = Inj l ts y"
| "subst\<^sub>e\<^sub>e x e' (Case e t cs) = Case (subst\<^sub>e\<^sub>e x e' e) t (map (subst\<^sub>e\<^sub>e (Suc x) (incr\<^sub>e\<^sub>e 0 e')) cs)"
| "subst\<^sub>e\<^sub>e x e' (Fold t y) = Fold t y"
| "subst\<^sub>e\<^sub>e x e' (Unfold t e) = Unfold t (subst\<^sub>e\<^sub>e x e' e)"
| "subst\<^sub>e\<^sub>e x e' (TyAbs k e) = TyAbs k (subst\<^sub>e\<^sub>e x (incr\<^sub>t\<^sub>e 0 e') e)"
| "subst\<^sub>e\<^sub>e x e' (TyApp e t) = TyApp (subst\<^sub>e\<^sub>e x e' e) t"
| "subst\<^sub>e\<^sub>e x e' (TyLet t e) = TyLet t (subst\<^sub>e\<^sub>e x (incr\<^sub>t\<^sub>e 0 e') e)"

primrec is_value :: "expr \<Rightarrow> bool" where
  "is_value (Var x) = False"
| "is_value (Abs t e) = True"
| "is_value (App e\<^sub>1 e\<^sub>2) = False"
| "is_value (Let e\<^sub>1 e\<^sub>2) = is_value e\<^sub>2"
| "is_value (Rec fs) = True"
| "is_value (Proj e l) = False"
| "is_value (Inj l ts e) = True"
| "is_value (Case e t cs) = False"
| "is_value (Fold t e) = True"
| "is_value (Unfold t e) = False"
| "is_value (TyAbs k e) = True"
| "is_value (TyApp e t) = False"
| "is_value (TyLet t e) = False"

primrec head_var :: "expr \<Rightarrow> nat option" where
  "head_var (Var x) = Some x"
| "head_var (Abs t e) = None"
| "head_var (App e\<^sub>1 e\<^sub>2) = head_var e\<^sub>1"
| "head_var (Let e\<^sub>1 e\<^sub>2) = (case head_var e\<^sub>2 of
      Some (Suc n) \<Rightarrow> Some n
    | Some 0 \<Rightarrow> head_var e\<^sub>1
    | None \<Rightarrow> None)"
| "head_var (Rec fs) = None"
| "head_var (Proj e l) = head_var e"
| "head_var (Inj l ts e) = None"
| "head_var (Case e t cs) = head_var e"
| "head_var (Fold t e) = None"
| "head_var (Unfold t e) = head_var e"
| "head_var (TyAbs k e) = None"
| "head_var (TyApp e t) = head_var e"
| "head_var (TyLet t e) = None"

fun free_vars :: "expr \<Rightarrow> nat set" 
and free_vars\<^sub>c :: "expr list \<Rightarrow> nat set" where
  "free_vars (Var x) = {x}"
| "free_vars (Abs t e) = var_reduce 0 (free_vars e)"
| "free_vars (App e\<^sub>1 e\<^sub>2) = free_vars e\<^sub>1 \<union> free_vars e\<^sub>2"
| "free_vars (Let e\<^sub>1 e\<^sub>2) = free_vars e\<^sub>1 \<union> var_reduce 0 (free_vars e\<^sub>2)"
| "free_vars (Rec xs) = set xs"
| "free_vars (Proj e l) = free_vars e"
| "free_vars (Inj l ts x) = {x}"
| "free_vars (Case e t cs) = free_vars e \<union> free_vars\<^sub>c cs"
| "free_vars (Fold t x) = {x}"
| "free_vars (Unfold t e) = free_vars e"
| "free_vars (TyAbs k e) = free_vars e"
| "free_vars (TyApp e t) = free_vars e"
| "free_vars (TyLet t e) = free_vars e"
| "free_vars\<^sub>c [] = {}"
| "free_vars\<^sub>c (c # cs) = var_reduce 0 (free_vars c) \<union> free_vars\<^sub>c cs"

lemma [simp]: "size (subst\<^sub>t\<^sub>e x t e) = size e"
  proof (induction e arbitrary: x t)
  case (Rec es)
    thus ?case by (induction es) simp_all
  next case (Case e t cs)
    thus ?case by (induction cs) simp_all
  qed simp_all

lemma [simp]: "free_vars (subst\<^sub>t\<^sub>e x t e) = free_vars e"
  and [simp]: "free_vars\<^sub>c (map (subst\<^sub>t\<^sub>e x t) c) = free_vars\<^sub>c c"
  by (induction e and c arbitrary: x t and x t rule: free_vars_free_vars\<^sub>c.induct) simp_all

lemma [simp]: "free_vars (subst\<^sub>x\<^sub>e x y e) = 
    var_reduce x (free_vars e) \<union> (if x \<in> free_vars e then {y} else {})"
  and [simp]: "free_vars\<^sub>c (map (subst\<^sub>x\<^sub>e (Suc x) (Suc y)) c) = 
    var_reduce x (free_vars\<^sub>c c) \<union> (if x \<in> free_vars\<^sub>c c then {y} else {})"
  proof (induction e and c arbitrary: x y and x y rule: free_vars_free_vars\<^sub>c.induct)
  case 5
    thus ?case by (auto simp add: var_reduce_def)
  qed auto

lemma [simp]: "free_vars (incr\<^sub>e\<^sub>e x e) = incr x ` free_vars e"
  and [simp]: "free_vars\<^sub>c (map (incr\<^sub>e\<^sub>e (Suc x)) c) = incr x ` free_vars\<^sub>c c"
  by (induction e and c arbitrary: x and x rule: free_vars_free_vars\<^sub>c.induct) auto

lemma [simp]: "x \<notin> free_vars e \<Longrightarrow> free_vars (decr\<^sub>x\<^sub>e x e) = decr x ` free_vars e"
  and [simp]: "x \<notin> free_vars\<^sub>c c \<Longrightarrow> free_vars\<^sub>c (map (decr\<^sub>x\<^sub>e (Suc x)) c) = decr x ` free_vars\<^sub>c c"
  by (induction e and c arbitrary: x and x rule: free_vars_free_vars\<^sub>c.induct) auto

lemma [simp]: "x \<notin> free_vars\<^sub>c cs \<Longrightarrow> c \<in> set cs \<Longrightarrow> Suc x \<notin> free_vars c"
  by (induction cs) auto

lemma [simp]: "length (extend_var_map rs) = Suc (length rs)"
  by (simp add: extend_var_map_def)

end