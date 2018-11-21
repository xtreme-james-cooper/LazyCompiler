theory Stack
imports "../Utilities/Heap" "../01Expression/Expression"
begin

datatype val = 
  VAbs type expr
| VRec "nat list"
| VInj nat "type list" nat
| VFold type nat
| VTyAbs kind expr

datatype frame = 
  SRef nat
| SApp expr
| SProj nat
| SCase type "expr list"
| SUnfold type
| STyApp type

datatype focus = 
  Eval expr 
| Return val

datatype stack_state = StackState focus "frame list" "expr heap"

primrec free_vars\<^sub>s :: "frame \<Rightarrow> nat set" where
  "free_vars\<^sub>s (SRef x) = {x}"
| "free_vars\<^sub>s (SApp e) = free_vars e"
| "free_vars\<^sub>s (SProj l) = {}"
| "free_vars\<^sub>s (SCase t cs) = free_vars\<^sub>c cs"
| "free_vars\<^sub>s (SUnfold t) = {}"
| "free_vars\<^sub>s (STyApp t) = {}"

primrec free_vars\<^sub>s\<^sub>s :: "frame list \<Rightarrow> nat set" where
  "free_vars\<^sub>s\<^sub>s [] = {}"
| "free_vars\<^sub>s\<^sub>s (f # s) = free_vars\<^sub>s f \<union> free_vars\<^sub>s\<^sub>s s"

primrec devalue :: "val \<Rightarrow> expr" where
  "devalue (VAbs t e) = Abs t e"
| "devalue (VRec xs) = Rec xs"
| "devalue (VInj l ts x) = Inj l ts x"
| "devalue (VFold t x) = Fold t x"
| "devalue (VTyAbs k e) = TyAbs k e"

primrec revalue :: "expr \<Rightarrow> val \<times> expr list" where
  "revalue (Var x) = undefined "
| "revalue (Abs t e) = (VAbs t e, [])"
| "revalue (App e\<^sub>1 e\<^sub>2) = undefined"
| "revalue (Let e\<^sub>1 e\<^sub>2) = (case revalue e\<^sub>2 of (v, bs) \<Rightarrow> (v, e\<^sub>1 # bs))"
| "revalue (Rec xs) = (VRec xs, [])"
| "revalue (Proj e l) = undefined"
| "revalue (Inj l ts x) = (VInj l ts x, [])"
| "revalue (Case e t cs) = undefined"
| "revalue (Fold t x) = (VFold t x, [])"
| "revalue (Unfold t e) = undefined"
| "revalue (TyAbs k e) = (VTyAbs k e, [])"
| "revalue (TyApp e t) = undefined"
| "revalue (TyLet t e) = undefined"

lemma [simp]: "revalue (devalue v) = (v, [])"
  by (induction v) simp_all

lemma [simp]: "is_value e \<Longrightarrow> revalue e = (v, bs) \<Longrightarrow> foldr Let bs (devalue v) = e"
  by (induction e arbitrary: bs) (auto split: prod.splits)

end