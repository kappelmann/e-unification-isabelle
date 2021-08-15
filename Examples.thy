theory Examples
imports
  Hint_Unification
  Complex_Main
begin


ML‹
  open Utils
  val hint_unif = HO_Pat_Hint_Unif.hint_unify;
  val gen_ctxt = Context.the_generic_context
›

setup‹term_pat_setup›

(* set to 600 to trace the hint unification procedure in detail *)
declare [[log_level=500]]

(* Simple Recursive Hint Unification Examples *)
(* 1 *)
lemma suc_one [hints]:
  "x ≡ 1 ⟹ Suc x ≡ 2"
by linarith

lemma add_zero [hints]:
  "y ≡ z ⟹ x ≡ 0 ⟹ (y::nat) ≡ z + x"
by simp

ML‹
  val (t1,t2) = (@{term_pat "Suc (?n + 0)"},@{term_pat "2::nat"})›
  
ML‹
  val (env,thm) = hint_unif (gen_ctxt ()) (t1,t2) (Envir.empty 0);
  trace_unif_result @{context} (t1,t2) (env,thm)›

(* 2 *)
consts f :: "nat ⇒ nat" g :: "nat ⇒ nat" h :: "nat ⇒ nat"
       a :: nat b :: nat
       
lemma [hints]:"X ≡ f ⟹ X a ≡ X b"
  sorry

lemma [hints]:"X ≡ Y ⟹ h (g X) ≡ g (h Y)"
  sorry

ML‹
  val (t1,t2) = (@{term_pat "h (g (f a))"},@{term_pat "g (h (f b))"})›
  
ML‹
  val (env,thm) = hint_unif (gen_ctxt ()) (t1,t2) (Envir.empty 0);
  trace_unif_result @{context} (t1,t2) (env,thm)›

(* Simple Reflexive Tactics *)

datatype Expr = Var int | Op Expr Expr

fun eval :: "Expr ⇒ int" where
  "eval (Var i) = i"
| "eval (Op ex1 ex2) = (eval ex1) + (eval ex2)"

consts simpl :: "Expr ⇒ Expr"

lemma soundness :
  "P (eval (simpl x)) ⟹ P (eval x)"
sorry


(*supply base case and inductive hint*)
lemma h_base [hints]:
  "x ≡ Var i ⟹ eval x ≡ i"
by simp

lemma h_add [hints]:
  "x ≡ Op z1 z2 ⟹ m ≡ eval z1 ⟹ n ≡ eval z2 ⟹ eval x ≡ m + n"
by simp


ML‹
  val t1 = @{term_pat "eval ?y"};
  val t2 = @{term_pat "a + (b + c) ::int"}›

ML‹
  val (env,thm) = hint_unif (gen_ctxt ()) (t1,t2) (Envir.empty 0);
  trace_unif_result @{context} (t1,t2) (env,thm)›


(* Advanced Reflexive Tactics *)
datatype AdvExpr =
  EUnit
 |EVar nat
 |EMult AdvExpr AdvExpr
 |EOpp AdvExpr

fun eval_adv :: "AdvExpr × real list ⇒ real" where
  "eval_adv (EUnit,Γ) = 1"
 |"eval_adv (EVar i,Γ) = Γ!i"
 |"eval_adv (EMult ex1 ex2,Γ) = eval_adv (ex1,Γ) * eval_adv (ex2,Γ)"
 |"eval_adv (EOpp ex,Γ) = inverse (eval_adv (ex,Γ))"


(*hints for heap lookup*)
lemma h_var_base [hints]:
  "x ≡ EVar 0 ⟹ Γ ≡ n#Θ ⟹ eval_adv (x,Γ) ≡ n"
by simp

lemma h_var_rec [hints]:
  "x ≡ EVar (Suc p) ⟹ Γ ≡ s#Δ ⟹ n ≡ eval_adv (EVar p,Δ) ⟹ eval_adv (x,Γ) ≡ n"
by simp

(*hints for expressions*)
lemma h_unit [hints]:
  "x ≡ EUnit ⟹ eval_adv (x,Γ) ≡ 1"
by simp
  
lemma h_times [hints]:
  "x ≡ EMult z1 z2 ⟹ m ≡ eval_adv (z1,Γ) ⟹ n ≡ eval_adv (z2,Γ) ⟹ eval_adv (x,Γ) ≡ m * n"
by simp

lemma h_opp [hints]:
  "x ≡ EOpp z ⟹ n ≡ eval_adv (z,Γ) ⟹ eval_adv (x,Γ) ≡ inverse n"
by simp

ML‹
  val t1 = @{term_pat "eval_adv (?y,[3,5])"};
  val t2 = @{term_pat "1 * inverse 3 * 5::real"}›

ML‹
  val (env,thm) = hint_unif (gen_ctxt ()) (t1,t2) (Envir.empty 0);
  trace_unif_result @{context} (t1,t2) (env,thm)›

end
