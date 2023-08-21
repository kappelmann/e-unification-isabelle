(*  Title:      ML_Unification/term_index_unification_hints.ML
    Author:     Kevin Kappelmann

Unification hints stored in a term index.
*)
signature TERM_INDEX_UNIFICATION_HINTS =
sig
  include HAS_LOGGER

  (*underlying term index*)
  structure TI : TERM_INDEX

  (*storing the term index retrieval function and the term index*)
  structure Data : GENERIC_DATA

  val get_retrieval : Context.generic -> Unification_Hints.unif_hint TI.retrieval
  val set_retrieval : Unification_Hints.unif_hint TI.retrieval -> Context.generic -> Context.generic

  val get_index : Context.generic -> Unification_Hints.unif_hint TI.term_index
  val map_index : (Unification_Hints.unif_hint TI.term_index ->
    Unification_Hints.unif_hint TI.term_index) -> Context.generic -> Context.generic

  val add_hint : Unification_Hints.unif_hint -> Context.generic -> Context.generic
  val del_hint : Unification_Hints.unif_hint -> Context.generic -> Context.generic

  val parse_attribute : attribute context_parser
  val setup_attribute : string option -> local_theory -> local_theory

  val get_hints_no_ctxt :
    Unification_Hints.unif_hint TI.retrieval -> Unification_Hints.unif_hint TI.term_index ->
    bool -> term * term -> Unification_Hints.unif_hint Seq.seq

  val get_hints_index_from_ctxt : Unification_Hints.unif_hint TI.retrieval -> bool ->
    Proof.context -> term * term -> Unification_Hints.unif_hint Seq.seq

  structure UHI : UNIFICATION_HINTS_INDEXED
end

functor Term_Index_Unification_Hints(A : sig
  structure FIA : FUNCTOR_INSTANCE_ARGS
  structure TI : TERM_INDEX
  end) : TERM_INDEX_UNIFICATION_HINTS =
struct

structure FIU = Functor_Instance_Util(A.FIA)

val logger = Logger.setup_new_logger Unification_Hints.logger FIU.FIA.struct_name

structure UH = Unification_Hints

structure TI = A.TI

fun are_hint_variants ctxt hp =
  let
    val tp = apply2 Thm.prop_of hp
    val env = Unification_Util.empty_envir tp
    fun match tp = First_Order_Unification.match [] ctxt tp env
  in
    match tp
    |> Seq.maps (fn _ => match (swap tp))
    |> not o fst o General_Util.seq_is_empty
  end

structure Data = Generic_Data(Pair_Generic_Data_Args(
  struct
    structure Data1 =
      struct
        type T = UH.unif_hint TI.retrieval
        fun empty ti = TI.unifiables ti o TI.norm_term
        val merge = fst
      end
    structure Data2 = Term_Index_Generic_Data_Args(
      struct
        type data = UH.unif_hint
        structure TI = TI
        fun data_eq tp = are_hint_variants (Context.the_local_context ()) tp
      end)
  end))

val set_retrieval = Data.map o apfst o K
val get_retrieval = fst o Data.get

val get_index = snd o Data.get
val map_index = Data.map o apsnd

val index_key_from_hint = UH.cdest_hint_concl #> fst #> Thm.term_of #> TI.norm_term

fun add_hint hint context =
  let
    val ctxt = Context.proof_of context
    val is_hint_variant = curry (are_hint_variants ctxt) hint
    val insert_hint = TI.insert is_hint_variant (index_key_from_hint hint, hint)
  in
    (map_index insert_hint context)
    handle Term_Index_Base.INSERT =>
      (@{log Logger.WARN} ctxt
        (fn _ => Pretty.block [
          Pretty.str "Hint ",
          UH.pretty_hint ctxt hint,
          Pretty.str " already added."
        ] |> Pretty.string_of);
      context)
  end

fun del_hint hint context =
  let
    val ctxt = Context.proof_of context
    val is_hint_variant = curry (are_hint_variants ctxt) hint
    val delete_hint = TI.delete is_hint_variant (index_key_from_hint hint)
  in
    (map_index delete_hint context)
    handle Term_Index_Base.DELETE =>
      (@{log Logger.WARN} ctxt
        (fn _ => Pretty.block [
          Pretty.str "Hint ",
          UH.pretty_hint ctxt hint,
          Pretty.str " not found."
        ] |> Pretty.string_of);
      context)
  end

val binding = FIU.mk_binding_id_prefix "unif_hint"

val parse_attribute = Attrib.add_del
  (Thm.declaration_attribute add_hint) (Thm.declaration_attribute del_hint)

val setup_attribute = Attrib.local_setup binding parse_attribute o
  the_default ("add/delete unification hints to/from the term index (" ^ FIU.FIA.struct_name ^ ")")

fun get_hints_no_ctxt retrieve ti get_symmetric (t1, t2) =
  let val retrieve = retrieve ti #> Seq.of_list
  in
    retrieve t1 |> get_symmetric ?
      (fn hintsq => Seq.interleave (hintsq,
        retrieve t2 |> Seq.map Unification_Hints.symmetric_hint))
  end

fun get_hints_index_from_ctxt retrieve get_symmetric ctxt =
  get_hints_no_ctxt retrieve (get_index (Context.Proof ctxt)) get_symmetric

structure UHI : UNIFICATION_HINT_INDEX =
struct
fun get_hints get_symmetric ctxt =
  uncurry get_hints_no_ctxt (Data.get (Context.Proof ctxt)) get_symmetric
end

structure UHI = Unification_Hints_Indexed(struct
  structure FIA = A.FIA
  structure UHI = UHI
end)

end
