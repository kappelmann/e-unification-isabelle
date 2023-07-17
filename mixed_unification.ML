(*  Title:      ML_Unification/mixed_unification.ML
    Author:     Kevin Kappelmann, Paul Bachmann

Mixture of unification algorithms.
*)
signature MIXED_UNIFICATION =
sig
  include HAS_LOGGER

  val first_order_higher_order_pattern_unify : Unification_Base.unifier
end

structure Mixed_Unification : MIXED_UNIFICATION =
struct

val logger = Logger.setup_new_logger Unification_Base.logger "Mixed_Unification"

val first_order_higher_order_pattern_unify = First_Order_Unification.e_unify
  Unification_Util.unify_types
  Higher_Order_Pattern_Unification.unify

end
