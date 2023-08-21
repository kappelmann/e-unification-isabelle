(*  Title:      ML_Unification/unification_combine.ML
    Author:     Kevin Kappelmann

Combining e-unifiers.
*)
signature UNIFICATION_COMBINE =
sig
  include HAS_LOGGER

  (*storing the e-unifiers*)
  structure Data : GENERIC_DATA

  val e_unify : Unification_Base.e_unifier
end

functor Unification_Combine(A : sig
  structure FIA : FUNCTOR_INSTANCE_ARGS
  end) : UNIFICATION_COMBINE =
struct

structure FIU = Functor_Instance_Util(A.FIA)

val logger = Logger.setup_new_logger Unification_Base.logger FIU.FIA.struct_name

structure UCB = Unification_Combinator
structure UB = Unification_Base

structure Data = Generic_Data(struct
  type T = UB.e_unifier list
  val empty = []
  val merge = uncurry append
end)

val get_e_unifiers = Data.get o Context.Proof

fun e_unify unif binders ctxt tp env =
  (@{log Logger.DEBUG} ctxt (fn _ =>
    Pretty.block [
      Pretty.str "Combining e-unifiers for ",
      Unification_Util.pretty_unif_problem ctxt (apply2 (Envir_Normalisation.norm_term_unif env) tp)
    ] |> Pretty.string_of);
  UCB.concat_e_unifiers (get_e_unifiers ctxt) unif binders ctxt tp env)

end
