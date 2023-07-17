(*  Title:      ML_Unification/unification_base.ML
    Author:     Kevin Kappelmann

Basic definitions for unifiers.
*)

signature UNIFICATION_BASE =
sig
  include HAS_LOGGER

  val reflexive : cterm -> thm
  val combination : thm -> thm -> thm
  val symmetric : thm -> thm
  val transitive : thm -> thm -> thm
  val abstract_rule : string -> cterm -> thm -> thm
  val reflexive_term : Proof.context -> term -> thm

  (* binders with De Bruijn indexing *)
  (*During unification, when going underneath an abstraction, we store a binder as
  ((name, typ), fresh Free variable), where the fresh free variable can be used as a replacement for
  the corresponding bound variable, for example, when having to create a reflexivity theorem for the
  binder.*)
  type 'a binder = (string * typ) * 'a
  type 'a binders = ('a binder) list
  val fix_binders : (string * typ) list -> Proof.context -> term binders * Proof.context
  val fix_binder : (string * typ) -> Proof.context -> term binder * Proof.context
  (*returns types of binders*)
  val binder_types : 'a binders -> typ list
  (*returns free variable corresponding to the given binder*)
  val nth_binder_data : 'a binders -> int -> 'a
  (*replaces all binders by their corresponding free variable in the given term*)
  val replace_binders : term binders -> term -> term

  (*raised on unsupported input*)
  exception PATTERN

  (*raised on unification failure for non-sequence outputs*)
  exception UNIF
  type type_unifier = Proof.context -> typ * typ -> Envir.env -> Envir.env
  type type_matcher = type_unifier
  type closed_unifier = Proof.context -> term * term -> Envir.env -> (Envir.env * thm) Seq.seq
  (*(term binder) list stores fresh free variables associated to each loose bound variable*)
  type unifier = term binders -> closed_unifier
  type closed_matcher = closed_unifier
  type matcher = unifier

end

structure Unification_Base : UNIFICATION_BASE =
struct

val logger = Logger.setup_new_logger Logger.root_logger "Unif"

val reflexive = Thm.reflexive
val combination = Thm.combination
val symmetric = Thm.symmetric
val transitive = Thm.transitive
val abstract_rule = Thm.abstract_rule

val reflexive_term = reflexive oo Thm.cterm_of

(* binders *)
type 'a binder = (string * typ) * 'a
type 'a binders = ('a binder) list

fun fix_binders nTs ctxt =
  Variable.variant_fixes (map fst nTs) ctxt
  |>> map2 (fn (n, T) => fn n' => ((n, T), Free (n', T))) nTs

val fix_binder = yield_singleton fix_binders

fun binder_types binders = map (snd o fst) binders

fun nth_binder_data binders = snd o nth binders

(*replace all Bounds by corresponding Frees*)
fun replace_binders binders t = let val bvars = map snd binders
  in subst_bounds (bvars, t) end

exception PATTERN = Pattern.Pattern

exception UNIF = Pattern.Unif
type type_unifier = Proof.context -> typ * typ -> Envir.env -> Envir.env
type type_matcher = type_unifier
type closed_unifier = Proof.context -> term * term -> Envir.env ->
  (Envir.env * thm) Seq.seq
type unifier = term binders -> closed_unifier
type closed_matcher = closed_unifier
type matcher = unifier

end
