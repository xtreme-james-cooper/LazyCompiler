theory TypeNormalization
imports Vector
begin

datatype kind = 
  Star
| KArr kind kind

datatype type = 
  TyVar nat
| Arrow type type
| AbsTy kind type
| AppTy type type

primrec incr\<^sub>t\<^sub>t :: "nat \<Rightarrow> type \<Rightarrow> type" where
  "incr\<^sub>t\<^sub>t x (TyVar y) = TyVar (if x \<le> y then Suc y else y)"
| "incr\<^sub>t\<^sub>t x (Arrow t\<^sub>1 t\<^sub>2) = Arrow (incr\<^sub>t\<^sub>t x t\<^sub>1) (incr\<^sub>t\<^sub>t x t\<^sub>2)"
| "incr\<^sub>t\<^sub>t x (AbsTy k t) = AbsTy k (incr\<^sub>t\<^sub>t (Suc x) t)"
| "incr\<^sub>t\<^sub>t x (AppTy t\<^sub>1 t\<^sub>2) = AppTy (incr\<^sub>t\<^sub>t x t\<^sub>1) (incr\<^sub>t\<^sub>t x t\<^sub>2)"

primrec subst\<^sub>t\<^sub>t :: "nat \<Rightarrow> type \<Rightarrow> type \<Rightarrow> type" where
  "subst\<^sub>t\<^sub>t x t' (TyVar y) = (if x = y then t' else TyVar (if x < y then y - 1 else y))"
| "subst\<^sub>t\<^sub>t x t' (Arrow t\<^sub>1 t\<^sub>2) = Arrow (subst\<^sub>t\<^sub>t x t' t\<^sub>1) (subst\<^sub>t\<^sub>t x t' t\<^sub>2)"
| "subst\<^sub>t\<^sub>t x t' (AbsTy k t) = AbsTy k (subst\<^sub>t\<^sub>t (Suc x) (incr\<^sub>t\<^sub>t 0 t') t)"
| "subst\<^sub>t\<^sub>t x t' (AppTy t\<^sub>1 t\<^sub>2) = AppTy (subst\<^sub>t\<^sub>t x t' t\<^sub>1) (subst\<^sub>t\<^sub>t x t' t\<^sub>2)"

inductive kinding :: "kind list \<Rightarrow> type \<Rightarrow> kind \<Rightarrow> bool" (infix "\<turnstile>\<^sub>k _ : " 60) where
  k_var [simp]: "lookup x \<Delta> = Some k \<Longrightarrow> \<Delta> \<turnstile>\<^sub>k TyVar x : k"
| k_arrow [simp]: "\<Delta> \<turnstile>\<^sub>k t\<^sub>1 : Star \<Longrightarrow> \<Delta> \<turnstile>\<^sub>k t\<^sub>2 : Star \<Longrightarrow> \<Delta> \<turnstile>\<^sub>k Arrow t\<^sub>1 t\<^sub>2 : Star"
| k_absty [simp]: "insert_at 0 k\<^sub>1 \<Delta> \<turnstile>\<^sub>k t : k\<^sub>2 \<Longrightarrow> \<Delta> \<turnstile>\<^sub>k AbsTy k\<^sub>1 t : KArr k\<^sub>1 k\<^sub>2"
| k_appty [simp]: "\<Delta> \<turnstile>\<^sub>k t\<^sub>1 : KArr k\<^sub>1 k\<^sub>2 \<Longrightarrow> \<Delta> \<turnstile>\<^sub>k t\<^sub>2 : k\<^sub>1 \<Longrightarrow> \<Delta> \<turnstile>\<^sub>k AppTy t\<^sub>1 t\<^sub>2 : k\<^sub>1"

inductive_cases [elim]: "\<Delta> \<turnstile>\<^sub>k TyVar x : k"
inductive_cases [elim]: "\<Delta> \<turnstile>\<^sub>k Arrow t\<^sub>1 t\<^sub>2 : k"
inductive_cases [elim]: "\<Delta> \<turnstile>\<^sub>k AbsTy k' t : k"
inductive_cases [elim]: "\<Delta> \<turnstile>\<^sub>k AppTy t\<^sub>1 t\<^sub>2 : k"

lemma [simp]: "\<Delta> \<turnstile>\<^sub>k t : k \<Longrightarrow> x \<le> length \<Delta> \<Longrightarrow> insert_at x k' \<Delta> \<turnstile>\<^sub>k incr\<^sub>t\<^sub>t x t : k"
  by (induction \<Delta> t k arbitrary: x rule: kinding.induct) fastforce+

lemma [simp]: "insert_at x k' \<Delta> \<turnstile>\<^sub>k t : k \<Longrightarrow> \<Delta> \<turnstile>\<^sub>k t' : k' \<Longrightarrow> x \<le> length \<Delta> \<Longrightarrow> 
    \<Delta> \<turnstile>\<^sub>k subst\<^sub>t\<^sub>t x t' t : k"
  proof (induction "insert_at x k' \<Delta>" t k arbitrary: \<Delta> x t' rule: kinding.induct) 
  case (k_var y)
    thus ?case by (cases y) auto
  qed fastforce+

lemma [simp]: "\<Delta> \<turnstile>\<^sub>k t : k  \<Longrightarrow> x \<ge> length \<Delta> \<Longrightarrow> subst\<^sub>t\<^sub>t x t' t = t"
  proof (induction \<Delta> t k arbitrary: x t' rule: kinding.induct)
  case (k_var y \<Delta>)
    moreover hence "y < length \<Delta>" by auto
    ultimately show ?case by simp
  qed simp_all

lemma [elim]: "\<Delta> \<turnstile>\<^sub>k t : k \<Longrightarrow> (\<Delta> @ \<Delta>') \<turnstile>\<^sub>k t : k"
  proof (induction \<Delta> t k rule: kinding.induct)
  case (k_var x \<Delta> k)
    hence "lookup x (\<Delta> @ \<Delta>') = Some k" by auto
    thus ?case by simp
  qed simp_all

inductive equivalent :: "type \<Rightarrow> type \<Rightarrow> bool" (infix "=\<^sub>t" 60) where
  "t =\<^sub>t t"
| "t =\<^sub>t t' \<Longrightarrow> t' =\<^sub>t t"
| "t =\<^sub>t t' \<Longrightarrow> t' =\<^sub>t t'' \<Longrightarrow> t =\<^sub>t t''"
| "t\<^sub>1 =\<^sub>t t\<^sub>1' \<Longrightarrow> t\<^sub>2 =\<^sub>t t\<^sub>2' \<Longrightarrow> Arrow t\<^sub>1 t\<^sub>2 =\<^sub>t Arrow t\<^sub>1' t\<^sub>2'"
| "t =\<^sub>t t' \<Longrightarrow> AbsTy k t =\<^sub>t AbsTy k t'"
| "t\<^sub>1 =\<^sub>t t\<^sub>1' \<Longrightarrow> t\<^sub>2 =\<^sub>t t\<^sub>2' \<Longrightarrow> AppTy t\<^sub>1 t\<^sub>2 =\<^sub>t AppTy t\<^sub>1' t\<^sub>2'"
| "t\<^sub>1 =\<^sub>t t\<^sub>1' \<Longrightarrow> t\<^sub>2 =\<^sub>t t\<^sub>2' \<Longrightarrow> AppTy t\<^sub>1 t\<^sub>2 =\<^sub>t subst\<^sub>t\<^sub>t 0 t\<^sub>2 t\<^sub>1"

function (domintros) normalize :: "type \<Rightarrow> type" where
  "normalize t = (if \<not> (\<exists>k. [] \<turnstile>\<^sub>k t : k) then undefined else case t of 
      TyVar x \<Rightarrow> TyVar x
    | Arrow t\<^sub>1 t\<^sub>2 \<Rightarrow> Arrow (normalize t\<^sub>1) (normalize t\<^sub>2)
    | AbsTy k t \<Rightarrow> AbsTy k t
    | AppTy t\<^sub>1 t\<^sub>2 \<Rightarrow> normalize (subst\<^sub>t\<^sub>t 0 (normalize t\<^sub>2) (normalize t\<^sub>1)))"
  by pat_completeness auto

fun closed :: "type \<Rightarrow> kind \<Rightarrow> bool" where
  closed_unfold: "closed t k = (([] \<turnstile>\<^sub>k t : k) \<and> normalize_dom t \<and> (case k of
      Star \<Rightarrow> True
    | KArr k\<^sub>1 k\<^sub>2 \<Rightarrow> (\<forall>t'. closed t' k\<^sub>1 \<longrightarrow> closed (AppTy t t') k\<^sub>2)))"

primrec multisubst\<^sub>t\<^sub>t :: "type list \<Rightarrow> type \<Rightarrow> type" where
  "multisubst\<^sub>t\<^sub>t [] t = t"
| "multisubst\<^sub>t\<^sub>t (t' # ts) t = multisubst\<^sub>t\<^sub>t ts (subst\<^sub>t\<^sub>t 0 t' t)"

inductive multi_kinding :: "kind list \<Rightarrow> type list \<Rightarrow> kind list \<Rightarrow> bool" (infix "\<turnstile>\<^sub>k\<^sub>s _ :" 60) where
  k_nil [simp]: "\<Delta> \<turnstile>\<^sub>k\<^sub>s [] : []"
| k_cons [simp]:  "\<Delta> \<turnstile>\<^sub>k t : k \<Longrightarrow> \<Delta> \<turnstile>\<^sub>k\<^sub>s ts : ks \<Longrightarrow> \<Delta> \<turnstile>\<^sub>k\<^sub>s t # ts : k # ks"

inductive_cases [elim]: "\<Delta> \<turnstile>\<^sub>k\<^sub>s [] : ks"
inductive_cases [elim]: "\<Delta> \<turnstile>\<^sub>k\<^sub>s t # ts : ks"

lemma [simp]: "[] \<turnstile>\<^sub>k\<^sub>s ts : \<Delta> \<Longrightarrow> \<Delta> \<turnstile>\<^sub>k t : k \<Longrightarrow> [] \<turnstile>\<^sub>k multisubst\<^sub>t\<^sub>t ts t : k"
  proof (induction "[] :: kind list" ts \<Delta> arbitrary: t rule: multi_kinding.induct)
  case (k_cons t' k' ts ks)
    moreover hence "insert_at 0 k' ks \<turnstile>\<^sub>k t : k" by (cases ks) simp_all
    moreover from k_cons have "([] @ ks) \<turnstile>\<^sub>k t' : k'" by fastforce
    ultimately show ?case by simp
  qed simp_all

lemma [simp]: "[] \<turnstile>\<^sub>k t : k  \<Longrightarrow> multisubst\<^sub>t\<^sub>t ts t = t"
  by (induction ts) simp_all

lemma [simp]: "lookup x ts = Some t \<Longrightarrow> [] \<turnstile>\<^sub>k t : k \<Longrightarrow> multisubst\<^sub>t\<^sub>t ts (TyVar x) = t"
  by (induction x ts rule: lookup.induct) simp_all

lemma [simp]: "multisubst\<^sub>t\<^sub>t ts (Arrow t\<^sub>1 t\<^sub>2) = Arrow (multisubst\<^sub>t\<^sub>t ts t\<^sub>1) (multisubst\<^sub>t\<^sub>t ts t\<^sub>2)"
  by (induction ts arbitrary: t\<^sub>1 t\<^sub>2) simp_all

lemma kinded_is_closed [simp]: "\<Delta> \<turnstile>\<^sub>k t : k \<Longrightarrow> length ts = length \<Delta> \<Longrightarrow> 
  (\<And>i t' k'. lookup i ts = Some t' \<Longrightarrow> lookup i \<Delta> = Some k' \<Longrightarrow> closed t' k') \<Longrightarrow> 
    closed (multisubst\<^sub>t\<^sub>t ts t) k"
  proof (induction \<Delta> t k arbitrary: ts rule: kinding.induct)
  case (k_var x \<Delta> k)
    hence "x < length ts" by auto
    then obtain t' where "lookup x ts = Some t'" by fastforce
    moreover with k_var have "closed t' k" by simp
    moreover hence "[] \<turnstile>\<^sub>k t' : k" by simp
    ultimately show ?case by simp
  next case (k_arrow \<Delta> t\<^sub>1 t\<^sub>2)
    hence "normalize_dom (multisubst\<^sub>t\<^sub>t ts t\<^sub>1)" by simp
    moreover from k_arrow have "normalize_dom (multisubst\<^sub>t\<^sub>t ts t\<^sub>2)" by simp
    ultimately have "normalize_dom (Arrow (multisubst\<^sub>t\<^sub>t ts t\<^sub>1) (multisubst\<^sub>t\<^sub>t ts t\<^sub>2))" 
      using normalize.domintros by fast
    with k_arrow show ?case by simp
  next case (k_absty k\<^sub>1 \<Delta> t k\<^sub>2)


have "(\<And>x21 x22 x. tt = Arrow x21 x22 \<Longrightarrow> [] \<turnstile>\<^sub>k Arrow x21 x22 :  x \<Longrightarrow> normalize_dom x21) \<Longrightarrow>
(\<And>x21 x22 x. tt = Arrow x21 x22 \<Longrightarrow> [] \<turnstile>\<^sub>k Arrow x21 x22 :  x \<Longrightarrow> normalize_dom x22) \<Longrightarrow>
(\<And>x41 x42 x. tt = AppTy x41 x42 \<Longrightarrow> [] \<turnstile>\<^sub>k AppTy x41 x42 :  x \<Longrightarrow> normalize_dom x42) \<Longrightarrow>
(\<And>x41 x42 x. tt = AppTy x41 x42 \<Longrightarrow> [] \<turnstile>\<^sub>k AppTy x41 x42 :  x \<Longrightarrow> normalize_dom x41) \<Longrightarrow>
(\<And>x41 x42 x. tt = AppTy x41 x42 \<Longrightarrow> [] \<turnstile>\<^sub>k AppTy x41 x42 :  x \<Longrightarrow> normalize_dom (subst\<^sub>t\<^sub>t 0 (normalize x42) (normalize x41))) \<Longrightarrow>
normalize_dom tt" using normalize.domintros by blast


    from k_absty have "\<Delta> \<turnstile>\<^sub>k AbsTy k\<^sub>1 t : KArr k\<^sub>1 k\<^sub>2" by simp
    hence X: "[] \<turnstile>\<^sub>k multisubst\<^sub>t\<^sub>t ts (AbsTy k\<^sub>1 t) : KArr k\<^sub>1 k\<^sub>2" by simp


    have Y: "normalize_dom (multisubst\<^sub>t\<^sub>t ts (AbsTy k\<^sub>1 t))" by simp


    have "\<And>t'. closed t' k\<^sub>1 \<Longrightarrow> closed (AppTy (multisubst\<^sub>t\<^sub>t ts (AbsTy k\<^sub>1 t)) t') k\<^sub>2" by simp
    with X Y show ?case by simp
  next case k_appty

have "(\<And>x21 x22 x. tt = Arrow x21 x22 \<Longrightarrow> [] \<turnstile>\<^sub>k Arrow x21 x22 :  x \<Longrightarrow> normalize_dom x21) \<Longrightarrow>
(\<And>x21 x22 x. tt = Arrow x21 x22 \<Longrightarrow> [] \<turnstile>\<^sub>k Arrow x21 x22 :  x \<Longrightarrow> normalize_dom x22) \<Longrightarrow>
(\<And>x41 x42 x. tt = AppTy x41 x42 \<Longrightarrow> [] \<turnstile>\<^sub>k AppTy x41 x42 :  x \<Longrightarrow> normalize_dom x42) \<Longrightarrow>
(\<And>x41 x42 x. tt = AppTy x41 x42 \<Longrightarrow> [] \<turnstile>\<^sub>k AppTy x41 x42 :  x \<Longrightarrow> normalize_dom x41) \<Longrightarrow>
(\<And>x41 x42 x. tt = AppTy x41 x42 \<Longrightarrow> [] \<turnstile>\<^sub>k AppTy x41 x42 :  x \<Longrightarrow> normalize_dom (subst\<^sub>t\<^sub>t 0 (normalize x42) (normalize x41))) \<Longrightarrow>
normalize_dom tt" using normalize.domintros by blast
    thus ?case by simp
  qed 

lemma [simp]: "[] \<turnstile>\<^sub>k t : k \<Longrightarrow> normalize_dom t"
  proof -
    assume "[] \<turnstile>\<^sub>k t :  k"

    thus "normalize_dom t" by simp
  qed

termination normalize
  by simp

end