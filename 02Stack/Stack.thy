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

end