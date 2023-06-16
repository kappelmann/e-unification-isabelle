(*  Title:      E_Unification/unification_util.ML
    Author:     Kevin Kappelmann

Utilities used for e-unifications.
*)

signature UNIFICATION_UTIL =
sig
  include HAS_LOGGER

  (* pretty-printing *)
  val pretty_types : Proof.context -> typ list -> Pretty.T
  val pretty_terms : Proof.context -> term list -> Pretty.T
  val pretty_thm : Proof.context -> thm -> Pretty.T

  val pretty_tyenv : Proof.context -> Type.tyenv -> Pretty.T
  val pretty_tenv : Proof.context -> Envir.tenv -> Pretty.T
  val pretty_env : Proof.context -> Envir.env -> Pretty.T

  val pretty_unif : Proof.context -> (term * term) -> Pretty.T

  (* sequences *)
  (*raises exception if sequence is empty and returns the sequence otherwise*)
  val seq_try : exn -> 'a Seq.seq -> 'a Seq.seq
  val seq_is_empty : 'a Seq.seq -> (bool * 'a Seq.seq)

  (* terms and environments *)
  val maxidx_of_terms : term list -> int
  (*returns empty environment with maxidx set to maximum of given terms*)
  val empty_envir : term * term -> Envir.env

  val fresh_vars : string -> typ list -> int -> term list * int
  val fresh_var : string -> typ -> int -> term * int

  (* type unification *)

  (*raises Unification_Base.UNIF on failure*)
  val unify_types : Unification_Base.type_unifier
  (*raises Unification_Base.UNIF on failure*)
  val match_types : Unification_Base.type_matcher

  (* shared standard cases for unifiers *)
(* norm_term_type unify binders ctxt name T (tb1, tb2) env *)
  val abstract_abstract : Normalisation.term_type_normaliser -> Unification_Base.unifier ->
    Proof.context -> (term Unification_Base.binder) list -> string -> typ ->
    (term * term) -> Envir.env -> (Envir.env * thm) Seq.seq
  val rigid_rigid : Normalisation.term_type_normaliser -> Unification_Base.type_unifier ->
    Proof.context -> term -> (string * typ) -> Envir.env -> (Envir.env * thm) Seq.seq
  val bound_bound : Proof.context -> int -> int -> (term Unification_Base.binder) list ->
    thm Seq.seq
  val comb_comb : Normalisation.thm_type_normaliser -> Unification_Base.closed_unifier ->
    Proof.context -> (term * term) -> (term * term) -> Envir.env -> (Envir.env * thm) Seq.seq
  val args_args : Normalisation.thm_type_normaliser -> Unification_Base.closed_unifier ->
    Proof.context -> (Envir.env * thm) Seq.seq -> term list -> term list -> (Envir.env * thm) Seq.seq

  (* logging *)
  val log_unif_result : Proof.context -> term * term -> Envir.env * thm -> unit
  val log_unif_results : Proof.context -> term * term -> Unification_Base.closed_unifier -> unit
  val log_unif_results' : int -> Proof.context  -> term * term -> Unification_Base.closed_unifier -> unit

end

structure Unification_Util : UNIFICATION_UTIL =
struct

val logger = Logger.setup_new_logger Unification_Base.logger "Util"

(* pretty-printing *)
local
val pretty_term = Syntax.pretty_term
val pretty_type = Syntax.pretty_typ

fun pretty_env_aux show_entry =
  Vartab.dest
  #> map show_entry
  #> Pretty.list "[" "]"

fun pretty_env_entry show (s, t) = Pretty.block [show s, Pretty.str " := ", show t]

val pretty_record =
  map (fn (key, entry) => Pretty.block [Pretty.str key, Pretty.str "=", entry])
  #> Pretty.enum "," "{" "}"
in

fun pretty_types ctxt = Pretty.block o Pretty.commas o map (pretty_type ctxt)
fun pretty_terms ctxt = Pretty.block o Pretty.commas o map (pretty_term ctxt)
val pretty_thm = Thm.pretty_thm

fun pretty_tyenv ctxt =
  let
    val show_entry = pretty_env_entry (pretty_type ctxt)
    fun get_typs (v, (s, T)) = (TVar (v, s), T)
  in pretty_env_aux (show_entry o get_typs) end

fun pretty_tenv ctxt =
  let
    val show_entry = pretty_env_entry (pretty_term ctxt)
    fun get_trms (v, (T, t)) = (Var (v, T), t)
  in pretty_env_aux (show_entry o get_trms) end

fun pretty_env ctxt (Envir.Envir {maxidx, tyenv, tenv}) =
  pretty_record [
    ("maxidx", Pretty.str (string_of_int maxidx)),
    ("tyenv", pretty_tyenv ctxt tyenv),
    ("tenv", pretty_tenv ctxt tenv)
  ]

end

fun pretty_unif ctxt (t1, t2) =
  Pretty.block [pretty_terms ctxt [t1], Pretty.str " \<equiv>\<^sup>? " , pretty_terms ctxt [t2]]

(* sequences *)
fun seq_try exn sq = case Seq.pull sq of
    NONE => raise exn
  | SOME v => Seq.make (fn () => SOME v)

fun seq_is_empty sq = case Seq.pull sq of
    NONE => (true, Seq.empty)
  | SOME v => (false, Seq.make (fn () => SOME v))

(* terms and environments *)
fun maxidx_of_terms ts = fold (Integer.max o maxidx_of_term) ts ~1

fun empty_envir (t1, t2) = Envir.empty (maxidx_of_terms [t1, t2])

fun fresh_vars name Ts idx =
  let fun mk_var_inc T i = (Var ((name, i + 1), T), (i + 1))
  in fold_map mk_var_inc Ts idx end

fun fresh_var name = yield_singleton (fresh_vars name)

(* type unification *)

fun match_types ctxt (T, U) (env as Envir.Envir {maxidx, tenv, tyenv}) =
  (if pointer_eq (T, U) then env
  else
    let val tyenv' = Sign.typ_match (Proof_Context.theory_of ctxt) (T, U) tyenv
    in Envir.Envir {maxidx = maxidx, tenv = tenv, tyenv = tyenv'} end)
  handle Type.TYPE_MATCH =>
    (@{log Logger.DEBUG} ctxt
      (fn _ => Pretty.block [
          Pretty.str "Failed to match types ",
          pretty_types ctxt [Normalisation.norm_type_match tyenv T, U]
        ] |> Pretty.string_of);
    raise Unification_Base.UNIF)

fun unify_types ctxt (T, U) (env as Envir.Envir {maxidx, tenv, tyenv}) =
  (if pointer_eq (T, U) then env
  else
    let val (tyenv', maxidx') =
      Sign.typ_unify (Proof_Context.theory_of ctxt) (T, U) (tyenv, maxidx)
    in Envir.Envir {maxidx = maxidx', tenv = tenv, tyenv = tyenv'} end)
  handle Type.TUNIFY =>
    (@{log Logger.DEBUG} ctxt
      (fn _ => Pretty.block [
          Pretty.str "Failed to unify types ",
          pretty_types ctxt (map (Normalisation.norm_type_unif tyenv) [T, U])
        ] |> Pretty.string_of);
    raise Unification_Base.UNIF)

(* shared standard cases for unifiers *)

fun abstract_abstract norm_term_type unify ctxt binders name T tbp =
  let
    val (binder as (_, bvar), ctxt') = Unification_Base.fix_binder (name, T) ctxt
    fun norm_abstract (Envir.Envir {tyenv,...}) thm =
      let val bvar' = norm_term_type tyenv bvar
      in Unification_Base.abstract_rule name (Thm.cterm_of ctxt' bvar') thm end
  in
    unify (binder :: binders) ctxt' tbp
    #> Seq.map (fn (env, thm) => (env, norm_abstract env thm))
  end

fun rigid_rigid norm_term_type unify_types ctxt s (nt, Tt) env =
  let val (ns, Ts) = (if is_Const s then dest_Const else dest_Free) s
  in
    (if ns = nt then
      let val (env' as Envir.Envir {tyenv,...}) = unify_types ctxt (Ts, Tt) env
      in
        (env', Unification_Base.reflexive_term ctxt (norm_term_type tyenv s))
        |> Seq.single
      end
    else Seq.empty)
    handle Unification_Base.UNIF => Seq.empty (*types do not match*)
  end

fun bound_bound ctxt i j binders =
  if i = j
  then Unification_Base.nth_binder_data binders i |> Unification_Base.reflexive_term ctxt |> Seq.single
  else Seq.empty

fun comb_comb norm_thm_types unify ctxt (f, x) (g, y) env =
  let
    val unif' = unify ctxt
    val env_thmq = unif' (f, g) env
      |> Seq.maps (fn (env, thm_fg) => unif' (x, y) env |> Seq.map (apsnd (pair thm_fg)))
    fun combine (env, thmp) =
      (*normalise types for the combination theorem to succeed*)
      apply2 (norm_thm_types ctxt env) thmp
      |> uncurry Unification_Base.combination
      |> pair env
  in Seq.map combine env_thmq end

fun args_args norm_thm_types unify ctxt env_thmhq ss ts =
  (let
    val args = ss ~~ ts
    fun unif_arg tp = Seq.maps
      (fn (env, thms) => unify ctxt tp env |> Seq.map (apsnd (fn thm => thm :: thms)))
    fun unif_args env = fold unif_arg args (Seq.single (env, []))
    (*combine the theorems*)
    fun combine thmh (env_res, arg_thms) =
      let
        (*normalise types for the combination theorem to succeed*)
        val norm_thm_types' = norm_thm_types ctxt env_res
        fun norm_combine thm_arg thm = norm_thm_types' thm_arg |> Unification_Base.combination thm
      in (env_res, fold_rev norm_combine arg_thms (norm_thm_types' thmh)) end
  in Seq.maps (fn (env, thmh) => unif_args env |> Seq.map (combine thmh)) env_thmhq end)
  handle ListPair.UnequalLengths => Seq.empty

(* logging *)

fun log_unif_result ctxt _ (env, thm) =
  @{log} ctxt (fn _ => Pretty.block [
    Pretty.str "Environment: ",
    pretty_env ctxt env,
    Pretty.str "\nTheorem: ",
    pretty_thm ctxt thm
  ] |> Pretty.string_of)

fun log_unif_results ctxt tp unify =
  let val res = unify ctxt tp (empty_envir tp) |> Seq.list_of
  in fold (log_unif_result ctxt tp #> K) res () end

fun log_unif_results' n ctxt tp unify =
  let val res = unify ctxt tp (empty_envir tp) |> Seq.take n |> Seq.list_of
  in fold (log_unif_result ctxt tp #> K) res () end

end

