(*  Title:      ML_Unification/unify_of_base.ML
    Author:     Kevin Kappelmann

OF attribute with adjustable unifier.
*)
signature UNIFY_OF_BASE =
sig
  val unify_OF : ('a -> 'b -> thm -> Proof.context -> int -> tactic) ->
    'a -> 'b -> thm list -> Proof.context -> thm -> thm option
  val unify_OF_attribute : ('a -> 'b -> thm -> Proof.context -> int -> tactic) ->
    'a -> 'b -> thm list -> attribute
end

structure Unify_OF_Base : UNIFY_OF_BASE =
struct

fun unify_OF f norm_thm unify thms ctxt =
  map (fn thm => f norm_thm unify thm ctxt) thms |> RANGE |> HEADGOAL |> SINGLE

fun unify_OF_attribute f norm_thm unify thms = Thm.rule_attribute []
  (fn context => fn thm =>
    unify_OF f norm_thm unify thms (Context.proof_of context) thm
    |> (fn SOME thm => thm | _ => raise THM ("unify_OF: no unifiers", 0, thm :: thms)))

end