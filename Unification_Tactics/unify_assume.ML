(*  Title:      ML_Unification/unify_assume.ML
    Author:     Kevin Kappelmann

Assumption tactic with parametrised unification function.
*)
signature UNIFY_ASSUME =
sig
  include HAS_LOGGER

  val unify_assms : Unification_Base.unifier -> Proof.context -> int -> thm ->
    ((int * term Unification_Base.binders) * (Envir.env * thm)) Seq.seq
  val unify_assume_tac_index : Normalisation.thm_normaliser -> Unification_Base.unifier ->
    Proof.context -> int -> thm -> (int * thm) Seq.seq
  val unify_assume_tac : Normalisation.thm_normaliser -> Unification_Base.unifier ->
    Proof.context -> int -> tactic
end

structure Unify_Assume : UNIFY_ASSUME =
struct

val logger = Logger.setup_new_logger Unification_Base.logger "Unify_Assume"

structure UBase = Unification_Base
structure UTtil = Unification_Tactic_Util

fun unify_assms unify ctxt i state =
  (let
    val (rparams, (prems, concl)) = Term_Util.strip_nth_subgoal i state
    val (binders, ctxt) = UBase.fix_binders rparams ctxt
    val empty_env = Envir.empty (Thm.maxidx_of state)
    fun unif_prem (i, prem) = unify binders ctxt (prem, concl) empty_env
      |> Seq.map (pair (i, binders))
      |> Seq.append
  in General_Util.fold_rev_index unif_prem prems Seq.empty end)
  handle TERM _ => Seq.empty

fun unify_assume_tac_index norm_thm unify ctxt i state =
  let fun rewrite_subgoal ((n, binders), res) i state =
    (UTtil.rewrite_subgoal_unif_concl norm_thm binders res ctxt
    THEN' (DETERM o Tactic_Util.nth_assume_tac n ctxt)) i state
    |> Seq.map (pair n)
  in
    unify_assms unify ctxt i state
    |> Seq.maps (fn unif_res => rewrite_subgoal unif_res i state)
  end

fun unify_assume_tac norm_thm unify ctxt i state =
  unify_assume_tac_index norm_thm unify ctxt i state |> Seq.map snd

end
