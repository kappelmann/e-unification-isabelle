(*  Title:      E_Unification/unify_resolve.ML
    Author:     Kevin Kappelmann

Resolution with parametrised unification function.
*)
signature UNIFY_RESOLVE =
sig
  include HAS_LOGGER

  val no_lift_biresolve_tac : bool -> thm -> int -> Proof.context -> int -> tactic
  val no_lift_resolve_tac : thm -> int -> Proof.context -> int -> tactic
  val no_lift_eresolve_tac : thm -> int -> Proof.context -> int -> tactic

  val unify_resolve_tac : Unification_Util.thm_normaliser ->
    Unification_Base.unifier -> thm -> Proof.context -> int -> tactic
  val unify_resolves_tac : Unification_Util.thm_normaliser ->
    Unification_Base.unifier -> thm list -> Proof.context -> int -> tactic
  val any_unify_resolve_tac : Unification_Util.thm_normaliser ->
    Unification_Base.unifier -> thm list -> Proof.context -> int -> tactic

end

structure Unify_Resolve : UNIFY_RESOLVE =
struct

val logger = Logger.setup_new_logger Unification_Base.logger "Unify_Resolve"

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
    val eq_elim = Thm.instantiate' [] [SOME lhs, SOME rhs] Drule.equal_elim_rule2
    val thm = Thm.implies_elim eq_elim eq_thm
  in no_lift_resolve_tac thm 1 end

fun unify_resolve_tac norm_thm unify rule ctxt =
  let fun tac cgoal i state =
    let
      val lifted_rule = Thm.lift_rule cgoal rule
      val nprems_rule = Thm.nprems_of rule
      fun get_lifted_rule_concl_rparams lifted_rule =
        Logic.strip_prems (nprems_rule, [], Thm.prop_of lifted_rule)
        |> snd
        |> (`) Logic.strip_params
        |> apfst rev
      val (rparams, lifted_rule_concl) = get_lifted_rule_concl_rparams lifted_rule
      val conclp = (Thm.term_of cgoal, lifted_rule_concl)
        (*only unify the conclusion of the goal and the rule*)
        |> apply2 (curry Logic.rlist_abs rparams o Logic.strip_assums_concl)
      val env_thmq = unify ctxt conclp (Envir.empty (Thm.maxidx_of lifted_rule))
      fun rewrite_tac (env, unif_thm) =
        let
          (*normalise wrt. environment*)
          val norm_thm_env = norm_thm ctxt env
          val unif_thm = norm_thm_env unif_thm
          val lifted_rule = norm_thm_env lifted_rule
          val (rparams, lifted_rule_concl) = get_lifted_rule_concl_rparams lifted_rule
          val _ = @{log Logger.DEBUG} ctxt (fn _ => Pretty.block [
              Pretty.str "Lifting unification theorem ",
              Util.pretty_thm ctxt unif_thm
            ] |> Pretty.string_of)
          (**re-introduce the premises to the equality theorem**)
          (*fix fresh Frees*)
          val ctxt = fold Variable.declare_thm [unif_thm, lifted_rule] ctxt
          val (binders, ctxt') = Util.fix_binders rparams ctxt
          val cfrees = map (Thm.cterm_of ctxt' o snd) binders
          (*premises with Bounds replaced by fresh Frees*)
          val cfree_prems = Logic.strip_assums_hyp lifted_rule_concl
            |> map (Thm.cterm_of ctxt' o Util.replace_binders binders)
          fun all_abstract ((x, T), cfree) =
            let val all_const = Logic.all_const T |> Thm.cterm_of ctxt'
            in
              Unification_Base.abstract_rule x cfree
              #> Drule.arg_cong_rule all_const
            end
          val unif_thm =
            (*replace Bounds with fresh Frees*)
            fold_rev (fn free => fn thm => Drule.fun_cong_rule thm free) cfrees unif_thm
            (*introduce the premises*)
            |> fold_rev (Drule.imp_cong_rule o Thm.reflexive) cfree_prems
            (*re-introduce abstractions for the introduced fresh Frees*)
            |> fold all_abstract (rparams ~~ cfrees)
          val _ = @{log Logger.DEBUG} ctxt (fn _ => Pretty.block [
              Pretty.str "Lifted unification theorem ",
              Util.pretty_thm ctxt unif_thm
            ] |> Pretty.string_of)
        in
          (PRIMITIVE norm_thm_env |> K)
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
