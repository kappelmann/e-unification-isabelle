(*  Title:      ML_Utils/functor_instance.ML
    Author:     Kevin Kappelmann

Functor instance arguments and utilities.
*)
signature FUNCTOR_INSTANCE_ARGS =
sig
  (*struct name of the functor instance*)
  val struct_name : string
  (*id for the functor instance*)
  val id : bstring
  (*position where the functor instance is created*)
  val pos : Position.T
end

signature FUNCTOR_INSTANCE_UTIL =
sig
  structure FIA : FUNCTOR_INSTANCE_ARGS

  (*create code calling the given function of the functor instance*)
  val code_struct_op : string -> ML_Code_Util.code

  val id_prefix : bstring

  val add_id_prefix : string -> bstring
  val mk_binding_id_prefix : bstring -> binding
end

functor Functor_Instance_Util(FIA : FUNCTOR_INSTANCE_ARGS) : FUNCTOR_INSTANCE_UTIL =
struct

val _ = @{assert} (FIA.struct_name <> "")

structure FIA = FIA
fun code_struct_op operation = ML_Code_Util.flat_read [FIA.struct_name, ".", operation]

val id_prefix = (FIA.id <> "" ? suffix "_") FIA.id

val add_id_prefix = prefix id_prefix
fun mk_binding_id_prefix binding = Binding.make (add_id_prefix binding, FIA.pos)

end