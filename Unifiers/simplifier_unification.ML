(*  Title:      ML_Unification/simplifier_unification.ML
    Author:     Kevin Kappelmann

Solving unification problems with the simplifier.
*)
signature SIMPLIFIER_UNIFICATION =
sig
  include HAS_LOGGER

  val unify : Unification_Base.closed_unifier
end

structure Simplifier_Unification : SIMPLIFIER_UNIFICATION =
struct

val logger = Logger.setup_new_logger Unification_Base.logger "Simplifier_Unification"

val eq_eq_prem = Thm.cprem_of @{thm eq_if_eq_eq_self} 1

fun unify ctxt tp env =
  let fun mk_eq_if_eq_eq_self thm = @{thm eq_if_eq_eq_self}
    |> Thm.instantiate (Thm.first_order_match (eq_eq_prem, Thm.cprop_of thm))
    handle Pattern.MATCH =>
      (@{log Logger.TRACE} ctxt (fn _ => Pretty.block [
          Pretty.str "Normal forms are not equal. Result: ",
          Syntax.pretty_term ctxt (Thm.term_of (Thm.rhs_of thm))
        ] |> Pretty.string_of);
      Exn.reraise Pattern.MATCH)
  in
    (@{log Logger.DEBUG} ctxt (fn _ => Pretty.block [
        Pretty.str "Unifying via simplification ",
        Unification_Util.pretty_unif_problem ctxt tp
      ] |> Pretty.string_of);
    Logic.mk_equals tp
    |> Thm.cterm_of ctxt
    |> Simplifier.rewrite ctxt
    |> (fn conv_res => Thm.implies_elim (mk_eq_if_eq_eq_self conv_res) conv_res)
    |> Seq.single o pair env)
    handle
      TYPE _ => Seq.empty
    | Pattern.MATCH => Seq.empty
  end

end
