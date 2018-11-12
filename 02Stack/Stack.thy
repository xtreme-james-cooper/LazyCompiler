theory Stack
imports "../01Expression/Expression"
begin

datatype frame = 
  SApp expr
| SBind
| SProj nat
| SCase type "expr list"
| SUnfold type
| STyApp type

datatype stack_direction = Eval | Return

datatype stack_state = StackState stack_direction expr "frame list" "expr list"

fun unstack :: "expr \<Rightarrow> frame list \<Rightarrow> expr list \<Rightarrow> expr" where
  "unstack e [] h = e"
| "unstack e (SApp e' # s) h = unstack (App e e') s h"
| "unstack e (SBind # s) [] = undefined"
| "unstack e (SBind # s) (e' # h) = unstack (Let e' e) s h"
| "unstack e (SProj l # s) h = unstack (Proj e l) s h"
| "unstack e (SCase t cs # s) h = unstack (Case e t cs) s h"
| "unstack e (SUnfold t # s) h = unstack (Unfold t e) s h"
| "unstack e (STyApp t # s) h = unstack (TyApp e t) s h"

primrec unstack_state :: "stack_state \<Rightarrow> expr" where
  "unstack_state (StackState _ e s h) = unstack e s h"

end