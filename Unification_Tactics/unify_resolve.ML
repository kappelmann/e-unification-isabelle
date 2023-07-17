(*  Title:      ML_Unification/unify_resolve.ML
    Author:     Kevin Kappelmann

Resolution with adjustable unifier.
*)
signature UNIFY_RESOLVE =
sig
  include HAS_LOGGER

  val unify_resolve_tac : Normalisation.thm_normaliser ->
    Unification_Base.unifier -> thm -> Proof.context -> int -> tactic
  val unify_resolves_tac : Normalisation.thm_normaliser ->
    Unification_Base.unifier -> thm list -> Proof.context -> int -> tactic
  val any_unify_resolve_tac : Normalisation.thm_normaliser ->
    Unification_Base.unifier -> thm list -> Proof.context -> int -> tactic

  val unify_eresolve_tac_index : Normalisation.thm_normaliser ->
    Unification_Base.unifier -> Normalisation.thm_normaliser -> Unification_Base.unifier -> thm ->
    Proof.context -> int -> thm -> (int * thm) Seq.seq
  val unify_eresolve_tac : Normalisation.thm_normaliser -> Unification_Base.unifier ->
    Normalisation.thm_normaliser -> Unification_Base.unifier -> thm ->
    Proof.context -> int -> tactic
  val unify_eresolves_tac : Normalisation.thm_normaliser -> Unification_Base.unifier ->
    Normalisation.thm_normaliser -> Unification_Base.unifier -> thm list ->
    Proof.context -> int -> tactic
  val any_unify_eresolve_tac : Normalisation.thm_normaliser -> Unification_Base.unifier ->
    Normalisation.thm_normaliser -> Unification_Base.unifier -> thm list ->
    Proof.context -> int -> tactic

  val unify_dresolve_tac : Normalisation.thm_normaliser ->
    Unification_Base.unifier -> thm -> Proof.context -> int -> tactic
  val unify_dresolves_tac : Normalisation.thm_normaliser ->
    Unification_Base.unifier -> thm list -> Proof.context -> int -> tactic
  val any_unify_dresolve_tac : Normalisation.thm_normaliser ->
    Unification_Base.unifier -> thm list -> Proof.context -> int -> tactic

  val unify_fresolve_tac : Normalisation.thm_normaliser ->
    Unification_Base.unifier -> thm -> Proof.context -> int -> tactic
  val unify_fresolves_tac : Normalisation.thm_normaliser ->
    Unification_Base.unifier -> thm list -> Proof.context -> int -> tactic
  val any_unify_fresolve_tac : Normalisation.thm_normaliser ->
    Unification_Base.unifier -> thm list -> Proof.context -> int -> tactic

end

structure Unify_Resolve : UNIFY_RESOLVE =
struct

val logger = Logger.setup_new_logger Unification_Base.logger "Unify_Resolve"

structure UBase = Unification_Base
structure Util = Unification_Util
structure UTtil = Unification_Tactic_Util

fun unify_resolve_tac norm_thm unify rule ctxt =
  let fun tac cgoal i state =
    let
      val _ = @{log Logger.TRACE} ctxt (fn _ =>
          Pretty.block [
            Pretty.str ("Calling unification resolution tactic on subgoal "),
            Pretty.str (Int.toString i),
            Pretty.str ": ",
            Util.pretty_terms ctxt [Thm.term_of cgoal],
            Pretty.str (" and rule "),
            Util.pretty_thm ctxt rule
          ]
          |> Pretty.string_of
        )
      val lifted_rule = Thm.lift_rule cgoal rule |> Drule.incr_indexes state
      val nprems_rule = Thm.nprems_of rule
      val rparams = Term_Util.strip_all (Thm.term_of cgoal) |> fst
      val (binders, ctxt) = UBase.fix_binders rparams ctxt
      val conclp = (*only unify the conclusion of the rule and the goal*)
        apply2 Logic.strip_assums_concl (Thm.prop_of lifted_rule, Thm.term_of cgoal)
      val env_thmq = unify binders ctxt conclp (Envir.empty (Thm.maxidx_of lifted_rule))
      fun rewrite_tac (env, unif_thm) =
        UTtil.rewrite_subgoal_unif_concl norm_thm binders (env, unif_thm) ctxt
        THEN' Tactic_Util.no_lift_resolve_tac (norm_thm ctxt env lifted_rule) nprems_rule ctxt
    in Seq.maps (fn res => rewrite_tac res i state) env_thmq end
  in Tactic_Util.CSUBGOAL_DATA I tac end

fun unify_resolve_tacs norm_thm unify rules ctxt =
  map (fn rule => unify_resolve_tac norm_thm unify rule ctxt) rules

fun unify_resolves_tac norm_thm unify rules =
  unify_resolve_tacs norm_thm unify rules #> EVERY'

fun any_unify_resolve_tac norm_thm unify rules =
  unify_resolve_tacs norm_thm unify rules #> Tactic_Util.CONCAT'

fun unify_eresolve_tac_index norm_thm_resolve unify_resolve norm_thm_assume unify_assume
  rule ctxt i state =
  unify_resolve_tac norm_thm_resolve unify_resolve rule ctxt i state
  |> Seq.maps (Unify_Assume.unify_assume_tac_index norm_thm_assume unify_assume ctxt i)

fun unify_eresolve_tac norm_thm_resolve unify_resolve norm_thm_assume unify_assume
  rule ctxt i state =
  let val nprems = Thm.nprems_of rule
  in
    if nprems = 0 then
      (@{log Logger.WARN} ctxt (fn _ =>
        Pretty.block [
          Pretty.str "elim-resolution rule ",
          Util.pretty_thm ctxt rule,
          Pretty.str " has no premises."
        ] |> Pretty.string_of
      );
      Seq.empty)
    else
      unify_eresolve_tac_index norm_thm_resolve unify_resolve norm_thm_assume unify_assume rule ctxt i state
      |> Seq.maps (fn (n, state) =>
        Tactic_Util.EVERY_ARG (Tactic_Util.thin_tac n) (i upto i + nprems - 2) state)
  end

fun unify_eresolve_tacs norm_thm_resolve unify_resolve norm_thm_assume unify_assume rules ctxt =
  map (fn rule => unify_eresolve_tac norm_thm_resolve unify_resolve norm_thm_assume unify_assume rule ctxt)
    rules

fun unify_eresolves_tac norm_thm_resolve unify_resolve norm_thm_assume unify_assume rules =
  unify_eresolve_tacs norm_thm_resolve unify_resolve norm_thm_assume unify_assume rules
  #> EVERY'

fun any_unify_eresolve_tac norm_thm_resolve unify_resolve norm_thm_assume unify_assume rules =
  unify_eresolve_tacs norm_thm_resolve unify_resolve norm_thm_assume unify_assume rules
  #> Tactic_Util.CONCAT'

fun unify_dresolve_tac norm_thm unify rule =
  unify_eresolve_tac Normalisation.norm_thm_unif Higher_Order_Pattern_Unification.unify
    norm_thm unify (Tactic.make_elim rule)

fun unify_dresolve_tacs norm_thm unify rules ctxt =
  map (fn rule => unify_dresolve_tac norm_thm unify rule ctxt) rules

fun unify_dresolves_tac norm_thm unify rules =
  unify_dresolve_tacs norm_thm unify rules #> EVERY'

fun any_unify_dresolve_tac norm_thm unify rules =
  unify_dresolve_tacs norm_thm unify rules #> Tactic_Util.CONCAT'

fun unify_fresolve_tac norm_thm unify rule ctxt i state =
  let val nprems = Thm.nprems_of rule
  in
    if nprems = 0 then
      (@{log Logger.WARN} ctxt (fn _ =>
        Pretty.block [
          Pretty.str "forward-resolution rule ",
          Util.pretty_thm ctxt rule,
          Pretty.str " has no premises."
        ] |> Pretty.string_of
      );
      Seq.empty)
    else
      unify_eresolve_tac_index Normalisation.norm_thm_unif Higher_Order_Pattern_Unification.unify
        norm_thm unify (Tactic.make_elim rule) ctxt i state
      |> Seq.map snd
  end

fun unify_fresolve_tacs norm_thm unify rules ctxt =
  map (fn rule => unify_fresolve_tac norm_thm unify rule ctxt) rules

fun unify_fresolves_tac norm_thm unify rules =
  unify_fresolve_tacs norm_thm unify rules #> EVERY'

fun any_unify_fresolve_tac norm_thm unify rules =
  unify_fresolve_tacs norm_thm unify rules #> Tactic_Util.CONCAT'


(*TODO: parsing of further arguments:
1. proper vs improper method (resolve chained facts against first premises)
2. unify all vs unify any*)
structure Normaliser_Unifier = Generic_Data
(
  type T = Normalisation.thm_normaliser * Unification_Base.unifier;
  val empty = (Normalisation.norm_thm_unif, Mixed_Unification.first_order_higher_order_pattern_unify);
  fun merge (data1, _) = data1
)

val set_norm_unifier = Normaliser_Unifier.put
val set_unifier = Normaliser_Unifier.put o pair Normalisation.norm_thm_unif

local
val get_norm_unif = Normaliser_Unifier.get o Context.Proof
in
fun get_unifier_resolve_tac rules ctxt =
  let val (norm_thm, unif) = get_norm_unif ctxt
  in any_unify_resolve_tac norm_thm unif rules ctxt end
fun get_unifier_eresolve_tac rules ctxt =
  let val (norm_thm, unif) = get_norm_unif ctxt
  in any_unify_eresolve_tac norm_thm unif norm_thm unif rules ctxt end
fun get_unifier_dresolve_tac rules ctxt =
  let val (norm_thm, unif) = get_norm_unif ctxt
  in any_unify_dresolve_tac norm_thm unif rules ctxt end
fun get_unifier_fresolve_tac rules ctxt =
  let val (norm_thm, unif) = get_norm_unif ctxt
  in any_unify_fresolve_tac norm_thm unif rules ctxt end
end

val _ =
  Theory.setup (
    Method.setup \<^binding>\<open>unif_rule\<close>
      (Attrib.thms >> (fn rules => fn ctxt => SIMPLE_METHOD' (get_unifier_resolve_tac rules ctxt)))
      "resolve against any of the given theorems"
  )

end
