(*  Title:      ML_Unification/named_theorems_unification_hints.ML
    Author:     Kevin Kappelmann

Unification hints stored in a named theorem collection (NAMED_THMS).
*)
signature NAMED_THEOREMS_UNIFICATION_HINTS =
sig
  structure Hints : NAMED_THMS
  structure UHI : UNIFICATION_HINTS_INDEXED
end

functor Named_Theorems_Unification_Hints(P : sig structure FIA : FUNCTOR_INSTANCE_ARGS end)
  : NAMED_THEOREMS_UNIFICATION_HINTS =
struct

structure FIU = Functor_Instance_Util(P.FIA)

structure Hints = Named_Thms(
  val name = FIU.mk_binding_id_prefix "unif_hint"
  val description = "Unification Hints (" ^ FIU.FIA.struct_name ^ ")"
)
val _ = Theory.setup Hints.setup

structure UHI : UNIFICATION_HINT_INDEX =
struct
fun get_hints get_symmetric ctxt _ = Hints.get ctxt |> Seq.of_list |>
  get_symmetric ?
    (fn hintsq => Seq.interleave (hintsq, Seq.map Unification_Hints.symmetric_hint hintsq))
end

structure UHI = Unification_Hints_Indexed(struct
  structure FIA = FIU.FIA
  structure UHI = UHI
end)

end
