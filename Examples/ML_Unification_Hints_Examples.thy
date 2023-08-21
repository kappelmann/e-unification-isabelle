\<^marker>\<open>creator "Kevin Kappelmann"\<close>
\<^marker>\<open>contributor "Paul Bachmann"\<close>
section \<open>Examples\<close>
theory ML_Unification_Hints_Examples
  imports
    Complex_Main
    ML_Unification.ML_Unification_Hints
    ML_Unification.Unify_Fact_Tactic
    Logging.ML_Attributes
begin

paragraph \<open>Summary\<close>
text \<open>Sample applications for unification hints.\<close>

ML\<open>
  val read_term_pattern = Proof_Context.read_term_pattern
  structure Util = Unification_Util

  (* @{functor_instance struct_name = Exmpl_Unification_Hints
      and functor_name = Named_Theorems_Unification_Hints
      and id = \<open>"exmpl"\<close>} *)

  val unify = Mixed_Unification.first_higherp_comb_higher_unify
    (* Exmpl_Unification_Hints.UHI.get_hints *)
\<close>

experiment
begin
subsection \<open>Reflection\<close>
subsubsection \<open>Formulas with quantifiers\<close>

datatype form = TrueF | FalseF | Less nat nat
  | And form form | Or form form | Neg form | ExQ form

primrec interp :: "form \<Rightarrow> ('a::ord) list \<Rightarrow> bool"
where
  "interp TrueF vs \<longleftrightarrow> True"
| "interp FalseF vs \<longleftrightarrow> False"
| "interp (Less i j) vs \<longleftrightarrow> vs ! i < vs ! j"
| "interp (And f1 f2) vs \<longleftrightarrow> interp f1 vs \<and> interp f2 vs"
| "interp (Or f1 f2) vs \<longleftrightarrow> interp f1 vs \<or> interp f2 vs"
| "interp (Neg f) vs \<longleftrightarrow> \<not> interp f vs"
| "interp (ExQ f) vs \<longleftrightarrow> (\<exists>v. interp f (v # vs))"

lemma [unif_hint]:
  "n \<equiv> Suc n' \<Longrightarrow> vs \<equiv> v # vs' \<Longrightarrow> vs' ! n' \<equiv> x \<Longrightarrow> vs ! n \<equiv> x"
  "n \<equiv> 0 \<Longrightarrow> vs \<equiv> x # vs' \<Longrightarrow> vs ! n \<equiv> x"
  by simp_all

lemma [unif_hint]:
  "\<lbrakk>e \<equiv> ExQ f; \<And>v. interp f (v # vs) \<equiv> P v\<rbrakk> \<Longrightarrow> interp e vs \<equiv> \<exists>v. P v"
  "\<lbrakk>e \<equiv> Less i j; x \<equiv> vs ! i; y \<equiv> vs ! j\<rbrakk> \<Longrightarrow> interp e vs \<equiv> x < y"
  "\<lbrakk>e \<equiv> And f1 f2; interp f1 vs \<equiv> r1; interp f2 vs \<equiv> r2\<rbrakk> \<Longrightarrow> interp e vs \<equiv> r1 \<and> r2"
  "\<lbrakk>e \<equiv> Or f1 f2; interp f1 vs \<equiv> r1; interp f2 vs \<equiv> r2\<rbrakk> \<Longrightarrow> interp e vs \<equiv> r1 \<or> r2"
  "e \<equiv> Neg f \<Longrightarrow> interp f vs \<equiv> r \<Longrightarrow> interp e vs \<equiv> \<not>r"
  "e \<equiv> TrueF \<Longrightarrow> interp e vs \<equiv> True"
  "e \<equiv> FalseF \<Longrightarrow> interp e vs \<equiv> False"
  by simp_all

schematic_goal "interp ?f (?vs :: ('a :: ord) list) = (\<exists>(x :: 'a). x < y \<and> \<not>(\<exists>z. x < z))"
  by (urule refl)

subsubsection \<open>Simple Arithmetic\<close>
datatype add_expr = Var int | Add add_expr add_expr

fun eval_add_expr :: "add_expr \<Rightarrow> int" where
  "eval_add_expr (Var i) = i"
| "eval_add_expr (Add ex1 ex2) = eval_add_expr ex1 + eval_add_expr ex2"

(*supply base case and inductive hint*)
lemma eval_add_expr_Var [unif_hint]: "e \<equiv> Var i \<Longrightarrow> eval_add_expr e \<equiv> i" by simp

lemma eval_add_expr_add [unif_hint]:
  "e \<equiv> Add e1 e2 \<Longrightarrow> eval_add_expr e1 \<equiv> m \<Longrightarrow> eval_add_expr e2 \<equiv> n \<Longrightarrow> eval_add_expr e \<equiv> m + n"
  by simp

ML_command\<open>
  val t1 = read_term_pattern @{context} "eval_add_expr ?e"
  val t2 = read_term_pattern @{context} "1 + (2 + 7) :: int"
  val _ = Util.log_unif_results @{context} (t1, t2) (unify [])
\<close>

schematic_goal "eval_add_expr ?e = (1 + (2 + 7) :: int)"
  by (urule refl)

subsubsection \<open>Arithmetic with Environment\<close>
datatype mul_expr =
  Unit
| Var nat
| Mul mul_expr mul_expr
| Inv mul_expr

fun eval_mul_expr :: "mul_expr \<times> real list \<Rightarrow> real" where
  "eval_mul_expr (Unit, \<Gamma>) = 1"
| "eval_mul_expr (Var i, \<Gamma>) = \<Gamma> ! i"
| "eval_mul_expr (Mul e1 e2, \<Gamma>) = eval_mul_expr (e1, \<Gamma>) * eval_mul_expr (e2, \<Gamma>)"
| "eval_mul_expr (Inv e, \<Gamma>) = inverse (eval_mul_expr (e, \<Gamma>))"

(*initial hint to split e into an expression and an environment*)
lemma eval_mul_expr_split [unif_hint]:
  "e \<equiv> (e1, \<Gamma>) \<Longrightarrow> n \<equiv> eval_mul_expr (e1, \<Gamma>) \<Longrightarrow> eval_mul_expr e \<equiv> n"
  by simp

(*hints for environment lookup*)
lemma eval_mul_expr_Var_Suc [unif_hint]:
  "e \<equiv> Var (Suc p) \<Longrightarrow> \<Gamma> \<equiv> s # \<Delta> \<Longrightarrow> n \<equiv> eval_mul_expr (Var p, \<Delta>) \<Longrightarrow> eval_mul_expr (e, \<Gamma>) \<equiv> n"
  by simp

lemma eval_mul_expr_Var_zero [unif_hint]: "e \<equiv> Var 0 \<Longrightarrow> \<Gamma> \<equiv> n # \<Theta> \<Longrightarrow> eval_mul_expr (e, \<Gamma>) \<equiv> n"
  by simp

lemma eval_mul_expr_Inv [unif_hint]:
  "e1 \<equiv> Inv e2 \<Longrightarrow> n \<equiv> eval_mul_expr (e2, \<Gamma>) \<Longrightarrow> eval_mul_expr (e1, \<Gamma>) \<equiv> inverse n"
  by simp

lemma eval_mul_expr_Mul [unif_hint]: "e \<equiv> Mul e1 e2 \<Longrightarrow> m \<equiv> eval_mul_expr (e1, \<Gamma>) \<Longrightarrow>
  n \<equiv> eval_mul_expr (e2, \<Gamma>) \<Longrightarrow> eval_mul_expr (e, \<Gamma>) \<equiv> m * n"
  by simp

lemma eval_mul_expr_Unit [unif_hint]: "e \<equiv> Unit \<Longrightarrow> eval_mul_expr (e, \<Gamma>) \<equiv> 1" by simp

ML_command\<open>
  val t1 = read_term_pattern @{context} "eval_mul_expr ?e"
  val t2 = read_term_pattern @{context} "1 * inverse 3 * 5 :: real"
  val _ = Util.log_unif_results' 1 @{context} (t2, t1) (unify [])
\<close>

schematic_goal "eval_mul_expr ?e \<equiv> 1 * inverse 3 * 5 :: real"
  by (urule reflexive)

lemma "1000 * 3 - 2 + 2 = (3000 :: nat)"
  using eval_nat_numeral[simp]
  by - (urule refl)
  (* by simp *)

lemma
  assumes "[a,b,c] = [c,b,a]"
  shows "[a] @ [b,c] = [c,b,a]"
  using assms by uassm
  (* using assms by simp *)

(* lemma [unif_hint]: "x^2 + 2*x*y + y^2 \<equiv> z \<Longrightarrow> (x + y)^2 \<equiv> z" *)

(* lemma "(x^2 + (x :: nat))^2 \<le> 16 * x^4" *)
  (* by simp *)

(* declare [[ML_Kdattr \<open>Logger.set_log_levels Logger.root_logger Logger.DEBUG\<close>]] *)

lemma [unif_hint]: "xs \<equiv> [] \<Longrightarrow> length xs \<equiv> 0" by simp
lemma [unif_hint]: "z \<equiv> 0 \<Longrightarrow> x \<equiv> (0 :: nat) \<Longrightarrow> y \<equiv> 0 \<Longrightarrow> x + y \<equiv> z" by simp

schematic_goal "length ?xs = 0 + length ?ys + (1 - 1)"
  by (urule refl)

lemma [unif_hint]: "(x = y) \<equiv> (y = x)"
  by (simp add: eq_commute)

lemma
  assumes "x = y"
  shows "y = x"
  by (ufact assms)

end

end
