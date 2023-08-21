\<^marker>\<open>creator "Kevin Kappelmann"\<close>
section \<open>Unification Hints\<close>
theory ML_Unification_Hints
  imports
    ML_Functor_Instances
    ML_Term_Index
    ML_Unifiers
begin

ML_file\<open>unification_hints.ML\<close>

ML_file\<open>unification_hints_index.ML\<close>
ML_file\<open>named_theorems_unification_hints.ML\<close>
ML_file\<open>term_index_unification_hints.ML\<close>

(* ML\<open>
  @{functor_instance struct_name = Standard_Unification_Hints
    and functor_name = Term_Index_Unification_Hints
    and id = \<open>""\<close>
    and more_args = \<open>structure TI = struct open Discrimination_Tree end\<close>}
\<close>
local_setup \<open>Standard_Unification_Hints.setup_attribute NONE\<close> *)
ML\<open>
  @{functor_instance struct_name = Standard_Unification_Hints
    and functor_name = Named_Theorems_Unification_Hints
    and id = \<open>""\<close>}
\<close>

text\<open>Standard unification hints are accessible via @{attribute unif_hint},
@{attribute unif_hints_get_sym} specifies whether the symmetric versions of
stored hints should also be considered on retrieval.\<close>

ML\<open>
  let val hint_unif =
    Unification_Hints.try_hints (Standard_Unification_Hints.UHI.get_hints)
      Higher_Order_Pattern_Unification.match
      Envir_Normalisation.norm_term_unif
      Envir_Normalisation.norm_thm_unif
      (Mixed_Unification.first_higherp_comb_higher_unify
      |> Unification_Combinator.norm_unifier Envir_Normalisation.beta_norm_term_unif)
    #> Unification_Combinator.norm_closed_unifier Higher_Order_Pattern_Unification.norm_term_unify
  in
    Context.theory_map (Standard_Unification_Combine.Data.map (cons (K hint_unif)))
    |> Theory.setup
  end
\<close>

end
