theory StackCorrectness
imports StackConversion "../01Expression/Evaluate" "../Utilities/Iterate"
begin

lemma complete: "iter (op \<leadsto>) e e' \<Longrightarrow> 
    \<exists>\<Sigma> \<Sigma>'. iter (op \<leadsto>\<^sub>s) \<Sigma> \<Sigma>' \<and> unstack_state \<Sigma> e \<and> unstack_state \<Sigma>' e'"
  by simp

lemma sound: "iter (op \<leadsto>\<^sub>s) \<Sigma> \<Sigma>' \<Longrightarrow> 
    \<exists>e e'. iter (op \<leadsto>) e e' \<and> unstack_state \<Sigma> e \<and> unstack_state \<Sigma>' e'"
  by simp

theorem correct: "iter (op \<leadsto>) e e' \<Longrightarrow> is_value e' \<Longrightarrow> \<exists>v h. e' = devalue v \<and> 
    iter (op \<leadsto>\<^sub>s) (StackState (Eval e) [] empty\<^sub>h) (StackState (Return v) [] h)"
  by simp

end