(*  Title:      E_Unification/unification_hints.ML
    Author:     Kevin Kappelmann, Paul Bachmann

Unification hints as introduced in "Hints in unification" by Asperti et al, 2009.
*)

signature UNIFICATION_HINTS =
sig
  include HAS_LOGGER

  val try_symmetric: bool Config.T
  structure Hints : NAMED_THMS
  type hint = thm
  val try_hints : Unification_Base.matcher -> Normalisation.term_normaliser ->
    Normalisation.thm_normaliser -> Unification_Base.unifier -> hint list ->
    Unification_Base.unifier
  val get_hints : Proof.context -> hint list
end

structure Unification_Hints : UNIFICATION_HINTS =
struct

val logger = Logger.setup_new_logger Unification_Base.logger "Unification_Hints"

structure Util = Unification_Util
structure GUtil = General_Util

structure Hints = Named_Thms(
  val name = @{binding "unif_hint"}
  val description = "Unification Hints"
)
val _ = Theory.setup Hints.setup

type hint = thm
val pretty_hint = Thm.pretty_thm

val try_symmetric = Attrib.setup_config_bool @{binding "unification_hints_try_sym"} (K true)

(*Tries to apply a hint to solve E-unification of (t1 \<equiv>? t2).
  Vars in hint are lifted wrt. passed binders.
  Unifies the hint's conclusion with (t1, t2) using match.
  Unifies resulting unification problems using unify.
  Normalises the theorems after unify with norm_thm_unif.
  Returns a sequence of (env, thm) pairs.
  Precondition: t1, t2 are normalised wrt the passed environment*)
fun try_hint try_symmetric match norm_term_unif norm_thm_unif unify binders ctxt (t1, t2)
  (Envir.Envir {maxidx, tenv, tyenv}) hint =
  let
    val dest_all_equals = Logic.strip_assums_concl #> Logic.dest_equals
    val rev_binders = rev binders
    val _ = @{log Logger.TRACE} ctxt (fn _ =>
        Pretty.block [Pretty.str "Trying hint: ", pretty_hint ctxt hint]
        |> Pretty.string_of
      )
    (*lift theorem to include bound variables and increase indices*)
    val hint_thm =
      Logic.list_all (map fst rev_binders, Var (("P", maxidx + 1), propT))
      |> Thm.cterm_of ctxt
      |> GUtil.flip Thm.lift_rule hint
    val (hint_prems, hint_concl) = Thm.prop_of hint_thm |> Logic.strip_horn
    val env = Envir.Envir {maxidx=Thm.maxidx_of hint_thm, tenv=tenv, tyenv=tyenv}

    (*match hint with unification pair, set flipped flag if symmetric hint matches*)
    val (P, Q) = dest_all_equals hint_concl
    val (no_hint_match, match_env_concl_thmpq) =
      let
        val match = match binders ctxt
        fun match_hint tl tr = match (P, tl) env
          |> Seq.maps (fn (env, thmL) => match (Q, tr) env |> Seq.map (apsnd (pair thmL)))
        fun PQq _ = match_hint t1 t2 |> Seq.map (rpair false)
        fun QPq _ = if try_symmetric
          then match_hint t2 t1 |> Seq.map (rpair true)
          else Seq.empty
      in Seq.APPEND (PQq, QPq) () |> Util.seq_is_empty end
  in
    if no_hint_match then
      (@{log Logger.TRACE} ctxt (K "Hint does not match."); Seq.empty)
    else
      let
        val _ = @{log Logger.DEBUG} ctxt (fn _ => Pretty.block [
            Pretty.str "Hint ",
            pretty_hint ctxt hint,
            Pretty.str " matched. Unifying premises..."
          ]
          |> Pretty.string_of)

        (*unify each hint premise and collect the theorems while iteratively extending the environment*)
        fun unif_prem prem = Seq.maps
          (fn (env, thms) => unify binders ctxt (dest_all_equals prem) env
            |> Seq.map (apsnd (fn thm => thm :: thms)))
        fun unify_prems ((match_env, concl_thmp), flipped) =
          fold unif_prem hint_prems (Seq.single (match_env, []))
          |> Seq.map (rpair (concl_thmp, flipped))

        fun inst_discharge ((env_res, prem_thms), (concl_thmp, flipped)) =
          let
            (*instantiate the theorems*)
            val norm_thm_unif = norm_thm_unif ctxt env_res
            val hint_thm_inst = norm_thm_unif hint_thm
            val norm_term_unif = norm_term_unif env_res
            val rev_cbinders = map (Thm.cterm_of ctxt o norm_term_unif o snd) rev_binders
            val forall_intr = Drule.forall_intr_list rev_cbinders
            val prem_thms_inst = map (forall_intr o norm_thm_unif) prem_thms |> rev
            val (concl_thmL, concl_thmR) = apply2 norm_thm_unif concl_thmp
            (*discharge the hint premises; flip the theorem if needed*)
            val thm_res = Drule.implies_elim_list hint_thm_inst prem_thms_inst
              |> Drule.forall_elim_list rev_cbinders
              |> GUtil.flip Unification_Base.transitive concl_thmR
              |> Unification_Base.transitive (Unification_Base.symmetric concl_thmL)
              |> flipped ? Unification_Base.symmetric
          in (env_res, thm_res) end
      in Seq.maps unify_prems match_env_concl_thmpq |> Seq.map inst_discharge end
  end

(*try to apply every hint from the hint list*)
fun try_hints match norm_term_unif norm_thm_unif unif hints binders ctxt (t1, t2) env =
  let val try_symmetric = Config.get ctxt try_symmetric
  in
    (@{log Logger.DEBUG} ctxt (fn _ =>
      Pretty.block [Pretty.str "Trying unification hints for ",
        Util.pretty_unif ctxt (t1, t2)]
      |> Pretty.string_of);
    Seq.of_list hints
    |> Seq.maps (try_hint try_symmetric match norm_term_unif norm_thm_unif
      unif binders ctxt (t1, t2) env))
  end

(*TODO: index hints in proper term index (cf. simplifier)*)
(* datatype unif_hints_set = Unif_Hints_Set of {hints : hint Net.net}

val empty_unif_hints_set = Unif_Hints_Set {hints = Net.empty}
val eq_ = Thm.eq_thm_prop (thm1, thm2)

fun merge_unif_hints_set uhs1 uhs2  =
  if pointer_eq (uhs1, uhs2) then uhs1
  else
    let
      val Unif_Hints_Set {hints = hints1} = uhs1;
      val Unif_Hints_Set {hints = hints2} = uhs2;
      val merged_hints = Net.merge eq_rrule (hints1, hints2);
    in Unif_Hints_Set {hints = merged_hints} end

structure Unif_Hints_Set = Generic_Data
(
  type T = unif_hints_set
  val empty = empty_unif_hints_set
  val extend = I
  val merge = merge_unif_hints_set
)

fun attrib f = Thm.declaration_attribute (map_ss o f);
val unif_hint_add = attrib undefined
val unif_hint_del = attrib undefined

val _ = Theory.setup (
  Attrib.setup @{binding unif_hint} (Attrib.add_del unif_hint_add unif_hint_del)
    "declaration of unification hint") *)

(*generates a list of hints from named theorems "hints"*)
(*TODO: sanity checks*)
val get_hints = Hints.get

end
