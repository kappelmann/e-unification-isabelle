(*  Title:      ML_Unification/unification_tactic_util.ML
    Author:     Kevin Kappelmann

Utilities used for tactics with e-unifications.
*)
signature UNIFICATION_TACTIC_UTIL =
sig
  include HAS_LOGGER

  (*creates equality theorem for a subgoal from an equality theorem for the subgoal's conclusion*)
  val eq_subgoal_from_eq_concl : term Unification_Base.binders -> thm ->
    term list -> Proof.context -> thm

  (*rewrite a subgoal given an equality theorem for the subgoal's conclusion*)
  val rewrite_subgoal_unif_concl : Normalisation.thm_normaliser ->
    term Unification_Base.binders -> (Envir.env * thm) -> Proof.context -> int -> tactic

end

structure Unification_Tactic_Util : UNIFICATION_TACTIC_UTIL =
struct

val logger = Logger.setup_new_logger Unification_Base.logger "Unification_Tactic_Util"

structure UBase = Unification_Base

fun eq_subgoal_from_eq_concl binders eq_thm prems ctxt =
  let
    (*certified premises with Bounds replaced by fresh Frees*)
    val cfree_prems = map (Thm.cterm_of ctxt o UBase.replace_binders binders) prems
    fun all_abstract ((x, T), free) =
      let val all_const = Logic.all_const T |> Thm.cterm_of ctxt
      in
        UBase.abstract_rule x (Thm.cterm_of ctxt free)
        #> Drule.arg_cong_rule all_const
      end
  in
    (*introduce the premises*)
    fold_rev (Drule.imp_cong_rule o Thm.reflexive) cfree_prems eq_thm
    (*introduce abstractions for the fresh Frees*)
    |> fold all_abstract binders
  end

fun rewrite_subgoal_unif_concl norm_thm binders (env, unif_thm) ctxt =
  let
    val norm_thm = norm_thm ctxt env
    fun rewrite_tac (rparams, (prems, _)) =
      let
        (*normalise types of binders*)
        val binders =
          map2 (fn (_, T) => fn ((n, _), Free (n', _)) => ((n, T), Free (n', T))) rparams binders
        val eq_thm = eq_subgoal_from_eq_concl binders (norm_thm unif_thm) prems ctxt
      in Tactic_Util.rewrite_subgoal_tac eq_thm ctxt end
  in
    (PRIMITIVE norm_thm |> K)
    THEN' Tactic_Util.SUBGOAL_STRIPPED I rewrite_tac
  end

end
