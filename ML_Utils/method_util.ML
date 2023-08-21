(*  Title:      ML_Utils/method_util.ML
    Author:     Kevin Kappelmann

Method utilities.
*)
signature METHOD_UTIL =
sig
  val METHOD_CONTEXT : (thm list -> 'a -> tactic) -> 'a -> Method.method
  val METHOD_CONTEXT' : (thm list -> 'a -> int -> tactic) -> 'a -> Method.method
end

structure Method_Util : METHOD_UTIL =
struct

fun METHOD_CONTEXT tac ctxt = METHOD (fn thms => tac thms ctxt)
fun METHOD_CONTEXT' tac ctxt = METHOD (fn thms => HEADGOAL (tac thms ctxt))

end
