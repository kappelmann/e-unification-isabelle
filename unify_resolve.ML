(*  Title:      ML_Unification/unify_resolve.ML
    Author:     Kevin Kappelmann

Resolution with parametrised unification function.
*)
signature UNIFY_RESOLVE =
sig
  include HAS_LOGGER

  val no_lift_biresolve_tac : bool -> thm -> int -> Proof.context -> int -> tactic
  val no_lift_resolve_tac : thm -> int -> Proof.context -> int -> tactic
  val no_lift_eresolve_tac : thm -> int -> Proof.context -> int -> tactic

  val unify_resolve_tac : Normalisation.thm_normaliser ->
    Unification_Base.unifier -> thm -> Proof.context -> int -> tactic
  val unify_resolves_tac : Normalisation.thm_normaliser ->
    Unification_Base.unifier -> thm list -> Proof.context -> int -> tactic
  val any_unify_resolve_tac : Normalisation.thm_normaliser ->
    Unification_Base.unifier -> thm list -> Proof.context -> int -> tactic

end

structure Unify_Resolve : UNIFY_RESOLVE =
struct

val logger = Logger.setup_new_logger Unification_Base.logger "Unify_Resolve"

structure UBase = Unification_Base
structure Util = Unification_Util

fun no_lift_biresolve_tac eres brule nsubgoals ctxt =
  Thm.bicompose (SOME ctxt) {flatten = true, match = true, incremented = true}
  (eres, brule, nsubgoals)
  #> PRIMSEQ

val no_lift_resolve_tac = no_lift_biresolve_tac false
val no_lift_eresolve_tac = no_lift_biresolve_tac true

fun rewrite_subgoal_tac eq_thm =
  let
    val (lhs, rhs) = Thm.dest_equals (Thm.cconcl_of eq_thm)
    val eq_elim = Thm.instantiate' [] [SOME lhs, SOME rhs] Drule.equal_elim_rule1
    val thm = Thm.implies_elim eq_elim eq_thm
  in no_lift_resolve_tac thm 1 end

fun unify_resolve_tac norm_thm unify rule ctxt =
  let fun tac cgoal i state =
    let
      val _ = @{log Logger.DEBUG} ctxt (fn _ =>
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
      val lifted_rule = Thm.lift_rule cgoal rule
      val nprems_rule = Thm.nprems_of rule
      fun get_lifted_rule_concl_rparams lifted_rule =
        Logic.strip_prems (nprems_rule, [], Thm.prop_of lifted_rule)
        |> snd
        |> (`) Logic.strip_params
        |> apfst rev
      val (rparams, lifted_rule_concl) = get_lifted_rule_concl_rparams lifted_rule
      val (binders, ctxt) = UBase.fix_binders rparams ctxt
      val conclp = (*only unify the conclusion of the goal and the rule*)
        apply2 Logic.strip_assums_concl (lifted_rule_concl, Thm.term_of cgoal)
      val env_thmq = unify binders ctxt conclp (Envir.empty (Thm.maxidx_of lifted_rule))
      fun rewrite_tac (env, unif_thm) =
        let
          (*normalise wrt. environment*)
          val norm_thm = norm_thm ctxt env
          val unif_thm = norm_thm unif_thm
          val lifted_rule = norm_thm lifted_rule
          val (rparams, lifted_rule_concl) = get_lifted_rule_concl_rparams lifted_rule
          val _ = @{log Logger.TRACE} ctxt (fn _ => Pretty.block [
              Pretty.str "Lifting unification theorem ",
              Util.pretty_thm ctxt unif_thm
            ] |> Pretty.string_of)
          (*normalise types of binders*)
          val binders =
            map2 (fn (_, T) => fn ((n, _), Free (n', _)) => ((n, T), Free (n', T))) rparams binders
          (*certified premises with Bounds replaced by fresh Frees*)
          val cfree_prems = Logic.strip_assums_hyp lifted_rule_concl
            |> map (Thm.cterm_of ctxt o UBase.replace_binders binders)
          fun all_abstract ((x, T), free) =
            let val all_const = Logic.all_const T |> Thm.cterm_of ctxt
            in
              Unification_Base.abstract_rule x (Thm.cterm_of ctxt free)
              #> Drule.arg_cong_rule all_const
            end
          val unif_thm = (*introduce the premises*)
            fold_rev (Drule.imp_cong_rule o Thm.reflexive) cfree_prems unif_thm
            (*introduce abstractions for the fresh Frees*)
            |> fold all_abstract binders
          val _ = @{log Logger.TRACE} ctxt (fn _ => Pretty.block [
              Pretty.str "Lifted unification theorem ",
              Util.pretty_thm ctxt unif_thm
            ] |> Pretty.string_of)
        in
          (PRIMITIVE norm_thm |> K)
          THEN' rewrite_subgoal_tac unif_thm ctxt
          THEN' no_lift_resolve_tac lifted_rule nprems_rule ctxt
        end
    in Seq.maps (fn res => rewrite_tac res i state) env_thmq end
  in Tactic_Util.CSUBGOAL_DATA I tac end

fun unify_resolve_tacs norm_thm unify rules ctxt =
  map (fn rule => unify_resolve_tac norm_thm unify rule ctxt) rules

fun unify_resolves_tac norm_thm unify rules =
  unify_resolve_tacs norm_thm unify rules #> EVERY'

fun any_unify_resolve_tac norm_thm unify rules =
  unify_resolve_tacs norm_thm unify rules #> Tactic_Util.CONCAT'


end
