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

primrec devalue :: "val \<Rightarrow> expr" where
  "devalue (VAbs t e) = Abs t e"
| "devalue (VRec xs) = Rec xs"
| "devalue (VInj l ts x) = Inj l ts x"
| "devalue (VFold t x) = Fold t x"
| "devalue (VTyAbs k e) = TyAbs k e"

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

end