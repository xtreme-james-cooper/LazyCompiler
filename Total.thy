theory Total
imports 
  "01Expression/01BigStep/BigStepDeterminism" "01Expression/02SmallStep/SmallStepDeterminism" 
  "01Expression/03EvaluationContext/ContextDeterminism" "02Stack/StackDeterminism" 
  "02Stack/StackCorrectness"
begin

theorem correct: "is_value e' \<Longrightarrow> revalue e' = (v, bs) \<Longrightarrow> 
    iter (op \<leadsto>) e e' = iter (op \<leadsto>\<^sub>s) (StackState (Eval e) [] empty\<^sub>h) (StackState (Return v) [] h)"
  by simp

end