\<^marker>\<open>creator "Kevin Kappelmann"\<close>
section \<open>E-Unification Examples\<close>
theory E_Unification_Examples
  imports
    Main
    ML_Unification_HOL_Setup
    Unify_Fact_Tactic
begin

paragraph \<open>Summary\<close>
text \<open>Sample applications of e-unifiers, methods, etc. introduced in this session.\<close>

experiment
begin

paragraph \<open>Using the simplifier for unification.\<close>

inductive_set even :: "nat set" where
zero: "0 \<in> even" |
step: "n \<in> even \<Longrightarrow> Suc (Suc n) \<in> even"

text \<open>Premises of the form @{term "SIMPS_TO_UNIF lhs rhs"} are solved by
@{ML_structure Simplifier_Unification}. It first normalises @{term lhs} and then unifies the
normalisation with @{term rhs}. See also @{theory ML_Unification.ML_Unification_HOL_Setup}.\<close>

lemma [unif_hint]: "n \<noteq> 0 \<Longrightarrow> PROP SIMPS_TO_UNIF (n - 1) m \<Longrightarrow> n \<equiv> Suc m"
  unfolding SIMPS_TO_UNIF_eq by linarith

schematic_goal "(\<And>x. x + 2 = n) \<Longrightarrow> Suc ?x = n"
  by uassm

schematic_goal "6 \<in> even"
  apply (urule step)
  apply (urule step)
  apply (urule step)
  apply (urule zero)
  done

schematic_goal "(220 + (80 - 2 * 2)) \<in> even"
  apply (urule step)
  apply (urule step)+
  apply (urule zero)
  done

lemma
  assumes "[a,b,c] = [c,b,a]"
  shows "[a] @ [b,c] = [c,b,a]"
  using assms by uassm

lemma "(x + (y :: nat))^2 \<le> x^2 + 2*x*y + y^2"
  supply power2_sum[simp]
  by (ufact order.refl)


paragraph \<open>Providing canonical solutions for meta variables with unification hints\<close>

lemma [unif_hint]: "xs \<equiv> [] \<Longrightarrow> length xs \<equiv> 0" by simp

schematic_goal "length ?xs = 0"
  by (ufact refl)


paragraph \<open>Strenghten unification with unification hints\<close>

lemma
  assumes "x = y"
  shows "y = x"
  supply eq_commute[unif_hint]
  by (ufact assms)


paragraph \<open>Discharging meta impliciations with object-level implications\<close>

lemma [unif_hint]:
  "Trueprop A \<equiv> A' \<Longrightarrow> Trueprop B \<equiv> B' \<Longrightarrow> Trueprop (A \<longrightarrow> B) \<equiv> (PROP A' \<Longrightarrow> PROP B')"
  using atomize_imp[symmetric] by simp

lemma
  assumes "A \<longrightarrow> (B \<longrightarrow> C) \<longrightarrow> D"
  shows "A \<Longrightarrow> (B \<Longrightarrow> C) \<Longrightarrow> D"
  using assms by ufact

end

end
