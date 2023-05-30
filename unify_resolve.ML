(*  Title:      E_Unification/unify_resolve.ML
    Author:     Kevin Kappelmann

Resolution with parametrised unification function.
*)
signature UNIFY_RESOLVE =
sig
  include HAS_LOGGER

  val no_lift_biresolve_tac : Proof.context -> bool -> thm -> int -> int -> tactic
  val no_lift_resolve_tac : Proof.context -> thm -> int -> int -> tactic
  val no_lift_eresolve_tac : Proof.context -> thm -> int -> int -> tactic

  val unify_resolve_tac : Unification_Util.thm_normaliser ->
    Unification_Base.unifier -> Proof.context -> thm -> int -> tactic
  val unify_resolve_tacs : Unification_Util.thm_normaliser ->
    Unification_Base.unifier -> Proof.context -> thm list -> (int -> tactic) list
  val unify_resolves_tac : Unification_Util.thm_normaliser ->
    Unification_Base.unifier -> Proof.context -> thm list -> int -> tactic
  val any_unify_resolve_tac : Unification_Util.thm_normaliser ->
    Unification_Base.unifier -> Proof.context -> thm list -> int -> tactic

end

structure Unify_Resolve : UNIFY_RESOLVE =
struct

val logger = Logger.setup_new_logger Unification_Base.logger "Unify_Resolve"

structure Util = Unification_Util

fun no_lift_biresolve_tac ctxt eres brule nsubgoals =
  Thm.bicompose (SOME ctxt) {flatten = true, match = true, incremented = true}
  (eres, brule, nsubgoals)
  #> PRIMSEQ

fun no_lift_resolve_tac ctxt = no_lift_biresolve_tac ctxt false

fun no_lift_eresolve_tac ctxt = no_lift_biresolve_tac ctxt true

fun rewrite_subgoal_tac ctxt eq_thm =
  let
    val (lhs, rhs) = Thm.dest_equals (Thm.cconcl_of eq_thm)
    val eq_elim = Thm.instantiate' [] [SOME lhs, SOME rhs] Drule.equal_elim_rule2
    val thm = Thm.implies_elim eq_elim eq_thm
  in no_lift_resolve_tac ctxt thm 1 end

fun unify_resolve_tac norm_thm unify ctxt rule =
  let fun tac (cgoal, i) state =
    let
      val lifted_rule = Thm.lift_rule cgoal rule
      val nprems = Thm.nprems_of rule
      val lifted_rule_concl =
        Logic.strip_prems (nprems, [], Thm.prop_of lifted_rule) |> snd
      val conclp = (Thm.term_of cgoal, lifted_rule_concl)
      val env_thmq = unify ctxt conclp (Util.empty_envir conclp)
      fun rewrite_tac (env, unif_thm) =
        let val norm_thm_inst = norm_thm ctxt env
        in
          (PRIMITIVE norm_thm_inst |> K)
          THEN' rewrite_subgoal_tac ctxt (norm_thm_inst unif_thm)
          THEN' no_lift_resolve_tac ctxt (norm_thm_inst lifted_rule) nprems
        end
    in Seq.maps (fn res => rewrite_tac res i state) env_thmq end
  in CSUBGOAL tac end

fun unify_resolve_tacs norm_thm unify ctxt =
  map (unify_resolve_tac norm_thm unify ctxt)

fun unify_resolves_tac norm_thm unify ctxt =
  unify_resolve_tacs norm_thm unify ctxt #> EVERY'

fun any_unify_resolve_tac norm_thm unify ctxt =
  unify_resolve_tacs norm_thm unify ctxt #> Util.CONCAT'


end
