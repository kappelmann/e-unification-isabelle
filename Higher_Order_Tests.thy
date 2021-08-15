theory Higher_Order_Tests
imports
  Hint_Unification
begin

ML_file ‹Test.ML›

ML‹
  open Test
  open Utils
  val hint_unif = HO_Pat_Hint_Unif.hint_unify
  fun std_unif ctxt ts env = (Pattern.unify ctxt ts env,@{thm Pure.reflexive})
  val ctxt = Context.the_generic_context›

setup‹term_pat_setup›
declare [[log_level=500]]

(* Symmetry *)
ML‹test_group symmetry std_unif "Free/Var" free_var_gen›
ML‹test_group symmetry hint_unif "Free/Var" free_var_gen›

(* Correct Environment is returned *)
ML‹test_group sigma_unifies std_unif "Free/Var" free_var_gen›
ML‹test_group sigma_unifies hint_unif "Free/Var" free_var_gen›

ML‹test_group sigma_unifies_var_term std_unif "Free/Var" free_var_gen›
ML‹test_group sigma_unifies_var_term hint_unif "Free/Var" free_var_gen›

ML‹test_group sigma_unifies_vars_replaced std_unif "Free/Var" free_var_gen›
ML‹test_group sigma_unifies_vars_replaced hint_unif "Free/Var" free_var_gen›

(** non-unifiability tests **)
(* Occurs check stops unification *)
ML‹test_group occurs_check std_unif "Var only" var_gen›
ML‹test_group occurs_check hint_unif "Var only" var_gen›

(** manual tests with Var/Free and TVar/TFree **)
(* should unify, using std_unif *)
ML‹list_pos (ctxt ()) std_unif "Var/Free, TVar/TFree combinations unify"
  [(Var(("A",0),TVar(("'a",0),[])),Free("A",TFree("'a",[]))),
   (Var(("A",0),TVar(("'a",0),[])),Var(("A",0),TFree("'a",[]))),
   (Var(("A",0),TVar(("'a",0),[])),Var(("B",0),TVar(("'a",0),[]))),
   (Var(("A",0),TVar(("'a",0),[])),Var(("A",0),TVar(("'b",0),[]))),
   (Var(("A",0),TFree("'a",[])),Free("A",TVar(("'a",0),[]))),
   (Free("A",TFree("'a",[])),Free("A",TVar(("'a",0),[])))]›

(* should unify, using hint_unif *)
ML‹list_pos (ctxt ()) hint_unif "Var/Free, TVar/TFree combinations unify"
  [(Var(("A",0),TVar(("'a",0),[])),Free("A",TFree("'a",[]))),
   (Var(("A",0),TVar(("'a",0),[])),Var(("A",0),TFree("'a",[]))),
   (Var(("A",0),TVar(("'a",0),[])),Var(("B",0),TVar(("'a",0),[]))),
   (Var(("A",0),TVar(("'a",0),[])),Var(("A",0),TVar(("'b",0),[]))),
   (Var(("A",0),TFree("'a",[])),Free("A",TVar(("'a",0),[]))),
   (Free("A",TFree("'a",[])),Free("A",TVar(("'a",0),[])))]›

(* should not unify, using std_unif *)
ML‹list_neg (ctxt ()) std_unif "Different Free/TFree fails"
  [(Free("A",TFree("'a",[])),Free("A",TFree("'b",[]))),
   (Free("A",TFree("'a",[])),Free("B",TFree("'a",[])))]›
(* should not unify, using hint_unif *)
ML‹list_neg (ctxt ()) hint_unif "Different Free/TFree fails"
  [(Free("A",TFree("'a",[])),Free("A",TFree("'b",[]))),
   (Free("A",TFree("'a",[])),Free("B",TFree("'a",[])))]›



(** hint tests **)
(*use <trace_test_result (ctxt()) (t1,t2) hint_unif> to view unification result*)

(* non-recursive hint tests *)
(*add_zero*)
ML‹
  val (t1,t2) = (@{term_pat "5::nat"}, @{term_pat "?b + 0 ::nat"});
  single_neg (ctxt ()) hint_unif "add_zero without hint" (t1,t2)›
lemma add_zero [hints]: "Y ≡ Z ⟹  X ≡ (0::nat) ⟹ Y + X ≡ Z"
  by simp
ML‹single_pos (ctxt ()) hint_unif "add_zero with hint" (t1,t2)›

(*mult_one*)
ML‹
  val (t1,t2) = (@{term_pat "1::nat"},@{term_pat "?a * ?b ::nat"});
  single_neg (ctxt ()) hint_unif "mult_one without hint" (t1,t2)›
lemma mult_one [hints]: "X ≡ 1 ⟹ Y ≡ 1 ⟹ X * Y ≡ (1::nat)"
  by simp
ML‹single_pos (ctxt ()) hint_unif "mult_one with hint" (t1,t2)›

(*id_eq*)
ML‹
  val (t1,t2) = (@{term_pat "5::nat"},@{term_pat "id ?a ::nat"});
  single_neg (ctxt ()) hint_unif "id_eq without hint" (t1,t2)›
lemma ID_EQ [hints]: "X ≡ Y ⟹ id X ≡ Y"
  by simp
ML‹single_pos (ctxt ()) hint_unif "id_eq with hint" (t1,t2)›

(*Suc 2 = 3*)
ML‹
  val (t1,t2) = (@{term_pat "Suc ?x ::nat"},@{term_pat "3::nat"});
  single_neg (ctxt ()) hint_unif "Suc ?x = 3 without hint" (t1,t2)›
lemma suc2 [hints]: "X ≡ 2 ⟹ Suc X ≡ 3"
  by linarith
ML‹single_pos (ctxt ()) hint_unif "Suc ?x = 3 with hint" (t1,t2)›

(*Suc x = 4, multiple matching hints, first one doesn't unify*)
definition x_def: "x≡3::nat"
ML‹
  val (t1,t2) =(@{term_pat "Suc x ::nat"},@{term_pat "4::nat"});
  single_neg (ctxt ()) hint_unif "Suc x = 4 without hint" (t1,t2)›
lemma suc_x_4 [hints]: "Suc x ≡ 4"
  by (simp add:x_def)
lemma suc3 [hints]: "X ≡ 3 ⟹ Suc X ≡ 4"
  by linarith
ML‹single_pos (ctxt ()) hint_unif "Suc x = 4 with multiple matching hints, only second one solves"
  (t1,t2)›

(* recursive hint tests *)

(*Suc (Suc 0) = 2*)
ML‹
  val (t1,t2) = (@{term_pat "Suc (Suc ?X) ::nat"},@{term_pat "2::nat"});
  single_neg (ctxt ()) hint_unif "Suc ?x = 3 without hint" (t1,t2)›
lemma suc0 [hints]: "X ≡ 0 ⟹ Suc X ≡ 1"
  by linarith
lemma suc1 [hints]: "X ≡ 1 ⟹ Suc X ≡ 2"
  by linarith
ML‹single_pos (ctxt ()) hint_unif "Suc ?x = 3 with hints" (t1,t2)›


consts f :: "nat ⇒ nat" g :: "nat ⇒ nat" h :: "nat ⇒ nat"
       a :: nat b :: nat y::nat

lemma [hints] : "X ≡ f (g 0) ⟹ Y ≡ g (f 0) ⟹ f (g X) ≡ g (f Y)"
  sorry
ML‹
  val (t1,t2) = (@{term_pat "f (g (f (g 0))) ::nat"}, @{term_pat "g (f (g (f 0))) ::nat"});
  single_pos (ctxt ()) hint_unif "" (t1,t2);›

(*same hint but with premises switched*)
consts f2 :: "nat ⇒ nat" g2 :: "nat ⇒ nat"
lemma [hints] : "Y ≡ g2 (f2 0) ⟹ X ≡ f2 (g2 0) ⟹ f2 (g2 X) ≡ g2 (f2 Y)"
  sorry
ML‹
  val (t1,t2) = (@{term_pat "f2 (g2 (f2 (g2 0))) ::nat"}, @{term_pat "g2 (f2 (g2 (f2 0))) ::nat"});
  single_pos (ctxt ()) hint_unif "" (t1,t2);›

lemma [hints]: "Y ≡ f X ⟹ X ≡ f (g 0) ⟹  f (g X) ≡ g (f Y)"
  sorry
ML‹
  val (t1,t2) = (@{term_pat "f (g (f (g 0))) ::nat"}, @{term_pat "g (f (f (f (g 0)))) ::nat"});
  single_pos (ctxt ()) hint_unif "" (t1,t2);›

(*same hint but with premises switched*)
lemma [hints]: "X ≡ f2 (g2 0) ⟹ Y ≡ f2 X ⟹  f2 (g2 X) ≡ g2 (f2 Y)"
  sorry
ML‹
  val (t1,t2) = (@{term_pat "f2 (g2 (f2 (g2 0))) ::nat"}, @{term_pat "g2 (f2 (f2 (f2 (g2 0)))) ::nat"});
  single_pos (ctxt ()) hint_unif "" (t1,t2);›

(*recursive calls with encapsulated hints*)
lemma [hints]:"X ≡ f ⟹ X a ≡ X b"
  sorry

lemma [hints]:"X ≡ Y ⟹ h (g X) ≡ g (h Y)"
  sorry

ML‹
  val (t1,t2) = (@{term_pat "h (g (f a))"},@{term_pat "g (h (f b))"});
  single_pos (ctxt ()) hint_unif "" (t1,t2);›

ML‹
  val (t1,t2) = (@{term_pat "id (id 2) ::nat"}, @{term_pat "Suc ?x ::nat"});
  single_pos (ctxt ()) hint_unif "" (t1,t2);›

consts r :: "nat ⇒ nat ⇒ nat" t :: "nat ⇒ nat"

(*recursive calls with alternating hints*)
lemma [hints]:"X ≡ Y ⟹ f X ≡ g Y"
  sorry

lemma [hints]:"X ≡ Y ⟹ f2 X ≡ g2 Y"
  sorry

ML‹
  val (t1,t2) = (@{term_pat "f2 (f (g 0)) ::nat"}, @{term_pat "g2 (f (g 0)) ::nat"});
  single_pos (ctxt ()) hint_unif "" (t1,t2);›

(*premise order: case where Xi depends on Xj with j>i cannot unify*)
consts l::nat m::nat 

lemma h1[hints]: "X1 ≡ X2 l ⟹ X2 ≡ f ⟹ X1 ≡ f m"
  sorry

ML‹
  val (t1,t2) = (@{term_pat "f l ::nat"}, @{term_pat "f m ::nat"});
  single_neg (ctxt ()) hint_unif "" (t1,t2);›


(*Higher-order-exclusive tests*)
ML‹
  val (t1,t2) = (@{term_pat "λx. f x"},@{term_pat "λx. f x"});
  trace_test_result (ctxt()) (t1,t2) hint_unif›

ML‹
  val (t1,t2) = (@{term_pat "λx. λy. (x::nat)"},@{term_pat "λy. λx. y"});
  trace_test_result (ctxt()) (t1,t2) hint_unif›

ML‹
  val (t1,t2) = (@{term_pat "λx. r x ?Y"},@{term_pat "λx. r x ?Y"});
  trace_test_result (ctxt()) (t1,t2) hint_unif›

lemma [hints]:"X≡(0::nat) ⟹ Y≡Z ⟹ X + Y ≡Z"
by linarith
ML‹
  val (t1,t2) = (@{term_pat "λx. (λy. 0 + 1::nat)"},@{term_pat "λx. (λy. 1::nat)"});
  trace_test_result (ctxt()) (t1,t2) hint_unif›

ML‹
  val (t1,t2) = (@{term_pat "(λx. 0 + Z + x::nat)"},@{term_pat "(λx. Z + x::nat)"});
  trace_test_result (ctxt()) (t1,t2) hint_unif›

ML‹
  val (t1,t2) = (@{term_pat "λx. (λy. 0 + Suc ?x::nat)"},@{term_pat "λx. (λy. 3::nat)"});
  trace_test_result (ctxt()) (t1,t2) hint_unif›

consts
  A :: "(nat ⇒ nat) × nat ⇒ nat"
  B :: "nat × nat ⇒ nat"
  C :: "nat"

ML‹
  val (t1,t2) = (@{term_pat "λu. B (?x,u)"},@{term_pat "λv. B (C,v)"});
  trace_test_result (ctxt()) (t1,t2) hint_unif›

ML‹
  val (t1,t2) = (@{term_pat "A (λu. B (?x,u),C)"},@{term_pat "A (λv. B (C,v),?y)"});
  trace_test_result (ctxt()) (t1,t2) hint_unif›

ML‹
  val (t1,t2) = (@{term_pat "A (λu. B (?x,C), C)"},@{term_pat "id (A (λu. ?y, C+0))"});
  trace_test_result (ctxt()) (t1,t2) hint_unif›

(*Bound case not working yet*)
ML‹
  val (t1,t2) = (@{term_pat "λx. (λx. 0+x::nat)"},@{term_pat "λx. (λx. x::nat)"});›

end
