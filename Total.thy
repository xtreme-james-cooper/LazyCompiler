theory Total
imports "01Expression/Determinism" "02Stack/StackDeterminism" "02Stack/StackCorrectness"
begin

theorem correct: "is_value e' \<Longrightarrow> revalue e' = (v, h) \<Longrightarrow> 
    iter (op \<leadsto>) e e' = iter (op \<leadsto>\<^sub>s) (StackState (Eval e) [] empty\<^sub>h) (StackState (Return v) [] hh)"
  by simp

end