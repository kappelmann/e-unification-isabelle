\<^marker>\<open>creator "Kevin Kappelmann"\<close>
section \<open>Unification Hints\<close>
theory ML_Unification_Hints
  imports
    ML_Functor_Instances
    ML_Term_Index
    ML_Unifiers
    ML_Unification_Parsers
begin

ML_file\<open>unification_hints_base.ML\<close>
ML_file\<open>unification_hints.ML\<close>
ML_file\<open>term_index_unification_hints.ML\<close>

ML\<open>
  @{functor_instance struct_name = Standard_Unification_Hints
    and functor_name = Term_Index_Unification_Hints
    and id = \<open>""\<close>
    and more_args = \<open>
      structure TI = Discrimination_Tree
      val init_args = {
        concl_unifier = SOME Higher_Order_Pattern_Unification.match,
        normalisers = SOME (Envir_Normalisation.norm_term_unif, Envir_Normalisation.norm_thm_unif),
        prems_unifier = SOME (Mixed_Unification.first_higherp_comb_higher_unify
          |> Unification_Combinator.norm_unifier Envir_Normalisation.beta_norm_term_unif),
        retrieval = SOME (Term_Index_Unification_Hints_Args.mk_sym_retrieval
          TI.norm_term TI.generalisations)
      }\<close>}
\<close>
local_setup \<open>Standard_Unification_Hints.setup_attribute NONE\<close>

text\<open>Standard unification hints are accessible via @{attribute unif_hint}.\<close>

ML\<open>
  let val hint_unif = Standard_Unification_Hints.try_hints
    |> Unification_Combinator.norm_unifier Higher_Order_Pattern_Unification.norm_term_unify
  in
    Context.theory_map (Standard_Unification_Combine.Data.map (cons (K hint_unif)))
    |> Theory.setup
  end
\<close>

end
