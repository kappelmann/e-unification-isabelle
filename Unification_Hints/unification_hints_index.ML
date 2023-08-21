(*  Title:      ML_Unification/unification_hints_index.ML
    Author:     Kevin Kappelmann

Indexed unification hints.
*)
signature UNIFICATION_HINT_INDEX =
sig
  (*gets stored hints; pass true if symmetric hints should also be retrieved*)
  val get_hints : bool -> Proof.context -> term * term -> Unification_Hints.unif_hint Seq.seq
end

signature UNIFICATION_HINTS_INDEXED =
sig
  structure Hint_Index : UNIFICATION_HINT_INDEX

  val get_symmetric: bool Config.T

  (*gets get_symmetric flag from context*)
  val get_hints : Proof.context -> term * term -> Unification_Hints.unif_hint Seq.seq
end

functor Unification_Hints_Indexed(P : sig
    structure FIA : FUNCTOR_INSTANCE_ARGS
    structure UHI : UNIFICATION_HINT_INDEX
  end) : UNIFICATION_HINTS_INDEXED =
struct

structure Hint_Index = P.UHI
structure FIU = Functor_Instance_Util(P.FIA)

val get_symmetric = Attrib.setup_config_bool (FIU.mk_binding_id_prefix "unif_hints_get_sym")
  (K true)

fun get_hints ctxt = Hint_Index.get_hints (Config.get ctxt get_symmetric) ctxt

end
