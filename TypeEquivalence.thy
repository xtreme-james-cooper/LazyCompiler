theory TypeEquivalence
imports Kindcheck
begin

primrec normal_type :: "type \<Rightarrow> bool"
    and normal_types :: "type list \<Rightarrow> bool" where
  "normal_type (TyVar x) = True"
| "normal_type (Arrow t\<^sub>1 t\<^sub>2) = (normal_type t\<^sub>1 \<and> normal_type t\<^sub>2)"
| "normal_type (Record ts) = normal_types ts"
| "normal_type (Variant ts) = normal_types ts"
| "normal_type (Inductive k t) = normal_type t"
| "normal_type (Forall k t) = normal_type t"
| "normal_type (AbsTy k t) = normal_type t"
| "normal_type (AppTy t\<^sub>1 t\<^sub>2) = False"
| "normal_types [] = True"
| "normal_types (t # ts) = (normal_type t \<and> normal_types ts)"

inductive type_equiv :: "type \<Rightarrow> type \<Rightarrow> bool" (infix "=\<^sub>t" 60) 
      and type_equiv_list :: "type list \<Rightarrow> type list \<Rightarrow> bool" (infix "=\<^sub>t\<^sub>s" 60) where
  teq_refl [simp]: "t =\<^sub>t t"
| teq_sym [simp]: "t\<^sub>1 =\<^sub>t t\<^sub>2 \<Longrightarrow> t\<^sub>2 =\<^sub>t t\<^sub>1"
| teq_trans [simp]: "t\<^sub>1 =\<^sub>t t\<^sub>2 \<Longrightarrow> t\<^sub>2 =\<^sub>t t\<^sub>3 \<Longrightarrow> t\<^sub>1 =\<^sub>t t\<^sub>3"
| teq_arrow [simp]: "t\<^sub>1 =\<^sub>t t\<^sub>1' \<Longrightarrow> t\<^sub>2 =\<^sub>t t\<^sub>2' \<Longrightarrow> Arrow t\<^sub>1 t\<^sub>2 =\<^sub>t Arrow t\<^sub>1' t\<^sub>2'"
| teq_record [simp]: "ts =\<^sub>t\<^sub>s ts' \<Longrightarrow> Record ts =\<^sub>t Record ts'"
| teq_variant [simp]: "ts =\<^sub>t\<^sub>s ts' \<Longrightarrow> Variant ts =\<^sub>t Variant ts'"
| teq_induct [simp]: "t =\<^sub>t t' \<Longrightarrow> Inductive k t =\<^sub>t Inductive k t'"
| teq_forall [simp]: "t =\<^sub>t t' \<Longrightarrow> Forall k t =\<^sub>t Forall k t'"
| teq_absty [simp]: "t =\<^sub>t t' \<Longrightarrow> AbsTy k t =\<^sub>t AbsTy k t'"
| teq_appty [simp]: "t\<^sub>1 =\<^sub>t t\<^sub>1' \<Longrightarrow> t\<^sub>2 =\<^sub>t t\<^sub>2' \<Longrightarrow> AppTy t\<^sub>1 t\<^sub>2 =\<^sub>t AppTy t\<^sub>1' t\<^sub>2'"
| teq_tbeta [simp]: "AppTy (AbsTy k t\<^sub>1) t\<^sub>2 =\<^sub>t subst\<^sub>t\<^sub>t 0 t\<^sub>2 t\<^sub>1"
| teq_nil [simp]: "[] =\<^sub>t\<^sub>s []"
| teq_cons [simp]: "t =\<^sub>t t' \<Longrightarrow> ts =\<^sub>t\<^sub>s ts' \<Longrightarrow> t # ts =\<^sub>t\<^sub>s t' # ts'"

end