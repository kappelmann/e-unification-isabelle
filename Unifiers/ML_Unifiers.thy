\<^marker>\<open>creator "Kevin Kappelmann"\<close>
section \<open>ML Unifiers\<close>
theory ML_Unifiers
  imports
    ML_Unification_Base
    ML_Functor_Instances
    Main
begin

paragraph \<open>Summary\<close>
text \<open>Unification modulo equations.\<close>

ML_file\<open>unification_combinator.ML\<close>
ML_file\<open>unification_combine.ML\<close>

ML\<open>
  @{functor_instance struct_name = Standard_Unification_Combine
    and functor_name = Unification_Combine
    and id = \<open>""\<close>}
\<close>

ML_file\<open>higher_order_unification.ML\<close>
ML_file\<open>higher_order_pattern_unification.ML\<close>
ML_file\<open>first_order_unification.ML\<close>

lemma eq_if_eq_eq_self: "(x \<equiv> y) \<equiv> (z \<equiv> z) \<Longrightarrow> x \<equiv> y" by simp
ML_file\<open>simplifier_unification.ML\<close>

ML_file\<open>mixed_unification.ML\<close>

ML\<open>
  let fun simp_unif _ = Simplifier_Unification.unify
    |> Unification_Combinator.norm_closed_unifier Higher_Order_Pattern_Unification.norm_term_unify
    |> Unification_Combinator.unifier_from_closed_unifier
  in
    Context.theory_map (Standard_Unification_Combine.Data.map (cons simp_unif))
    |> Theory.setup
  end
\<close>

end
