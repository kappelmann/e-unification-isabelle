(*  Title:      ML_Unification/mixed_unification.ML
    Author:     Kevin Kappelmann

Mixture of unification algorithms.
*)
signature MIXED_UNIFICATION =
sig
  include HAS_LOGGER

  (*first-order, then higher-order pattern, then standard combine, then
    higher-order fallback*)
  val first_higherp_comb_higher_unify : Unification_Base.unifier
  val norm_term_first_higherp_comb_higher_unify : Envir_Normalisation.term_normaliser
  val norm_thm_first_higherp_comb_higher_unify : Envir_Normalisation.thm_normaliser
end

structure Mixed_Unification : MIXED_UNIFICATION =
struct

val logger = Logger.setup_new_logger Unification_Base.logger "Mixed_Unification"

structure UC = Unification_Combinator

fun first_higherp_comb_higher_unify binders ctxt tp env =
  let
    val unify_types = Unification_Util.unify_types
    val comb_higher = UC.add_fallback_unifier
      Standard_Unification_Combine.e_unify Higher_Order_Unification.unify
    val higherp_comb_higher = UC.add_fallback_unifier
      (Higher_Order_Pattern_Unification.e_unify unify_types) comb_higher
    val fo_higherp_comb_higher = UC.add_fallback_unifier
      (First_Order_Unification.e_unify unify_types) higherp_comb_higher
  in
    (@{log Logger.DEBUG} ctxt (fn _ => Pretty.block [
      Pretty.str "First-order with higher-order pattern with \
        \Standard_Unification_Combinator with higher-order fallback unifying ",
      Unification_Util.pretty_unif_problem ctxt (apply2 (Envir_Normalisation.norm_term_unif env) tp)]
      |> Pretty.string_of);
    fo_higherp_comb_higher binders ctxt tp env)
  end

val norm_term_first_higherp_comb_higher_unify =
  Envir_Normalisation.beta_eta_short_norm_term_unif
val norm_thm_first_higherp_comb_higher_unify = Envir_Normalisation.beta_eta_short_norm_thm_unif

end
