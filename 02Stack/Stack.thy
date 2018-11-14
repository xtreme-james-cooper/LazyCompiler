theory Stack
imports "../Heap" "../01Expression/Expression"
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
| "devalue (VRec xs) = Rec (map Var xs)"
| "devalue (VInj l ts x) = Inj l ts (Var x)"
| "devalue (VFold t x) = Fold t (Var x)"
| "devalue (VTyAbs k e) = TyAbs k e"

fun devar :: "expr \<Rightarrow> nat" where
  "devar (Var x) = x"
| "devar _ = undefined"

fun unstack :: "expr \<Rightarrow> frame list \<Rightarrow> expr heap \<Rightarrow> expr" where
  "unstack e [] h = e"
| "unstack e (SRef x # s) h = unstack (Var x) s (update\<^sub>h h x e)"
| "unstack e (SApp e' # s) h = unstack (App e e') s h"
| "unstack e (SProj l # s) h = unstack (Proj e l) s h"
| "unstack e (SCase t cs # s) h = unstack (Case e t cs) s h"
| "unstack e (SUnfold t # s) h = unstack (Unfold t e) s h"
| "unstack e (STyApp t # s) h = unstack (TyApp e t) s h"

fun unstack_state :: "stack_state \<Rightarrow> expr" where
  "unstack_state (StackState (Eval e) s h) = unstack e s h"
| "unstack_state (StackState (Return v) s h) = unstack (devalue v) s h"

end