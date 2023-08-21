(*  Title:      ML_Unification/ml_attribute_util.ML
    Author:     Kevin Kappelmann

Utilities for attributes.
*)
signature ML_ATTRIBUTE_UTIL =
sig
  val Kattribute_declaration : attribute -> Context.generic -> Context.generic
  val Kproof_attribute_declaration : attribute -> Proof.context -> Proof.context
end

structure ML_Attribute_Util : ML_ATTRIBUTE_UTIL =
struct

fun Kattribute_declaration attr = Thm.attribute_declaration attr Drule.dummy_thm
val Kproof_attribute_declaration = Context.proof_map o Kattribute_declaration

end