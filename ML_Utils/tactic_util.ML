(*  Title:      ML_Utils/tactic_util.ML
    Author:     Kevin Kappelmann

Tactic utilities.
*)
signature TACTIC_UTIL =
sig
  (* tactic combinators*)
  val HEADGOAL : (int -> 'a) -> 'a

  val TRY' : ('a -> tactic) -> 'a -> tactic

  val EVERY_ARG : ('a -> tactic) -> 'a list -> tactic
  val EVERY_ARG' : ('a -> 'b -> tactic) -> 'a list -> 'b -> tactic
  val CONCAT : tactic list -> tactic
  val CONCAT' : ('a -> tactic) list -> 'a -> tactic

  val FOCUS_PARAMS' : (Subgoal.focus -> int -> tactic) -> Proof.context -> int -> tactic
  val FOCUS_PARAMS_CTXT : (Proof.context -> tactic) -> Proof.context -> int -> tactic
  val FOCUS_PARAMS_CTXT' : (Proof.context -> int -> tactic) -> Proof.context -> int -> tactic
  val FOCUS_PARAMS_FIXED' : (Subgoal.focus -> int -> tactic) -> Proof.context -> int -> tactic
  val FOCUS_PREMS' : (Subgoal.focus -> int -> tactic) -> Proof.context -> int -> tactic
  val FOCUS' : (Subgoal.focus -> int -> tactic) -> Proof.context -> int -> tactic
  val SUBPROOF' : (Subgoal.focus -> int -> tactic) -> Proof.context -> int -> tactic

  val CSUBGOAL_DATA : (cterm -> 'a) -> ('a -> int -> tactic) -> int -> tactic
  val CSUBGOAL_STRIPPED : ((string * cterm) list * (cterm list * cterm) -> 'a) ->
    ('a -> int -> tactic) -> int -> tactic
  val SUBGOAL_DATA : (term -> 'a) -> ('a -> int -> tactic) -> int -> tactic
  val SUBGOAL_STRIPPED : ((string * typ) list * (term list * term) -> 'a) ->
    ('a -> int -> tactic) -> int -> tactic

  (* tactics *)
  val insert_tac : thm -> int -> tactic
  (*thin_tac n i deletes nth premise of the ith subgoal*)
  val thin_tac : int -> int -> tactic
  val thin_tacs : int list -> int -> tactic

  (*solve subgoal by assumption, preferring premise n*)
  val nth_assume_tac : int -> Proof.context -> int -> tactic

  (*resolution*)
  val no_lift_biresolve_tac : bool -> thm -> int -> Proof.context -> int -> tactic
  val no_lift_resolve_tac : thm -> int -> Proof.context -> int -> tactic
  val no_lift_eresolve_tac : thm -> int -> Proof.context -> int -> tactic

  (*rewrite subgoal according to the given equality theorem "lhs \<equiv> subgoal"*)
  val rewrite_subgoal_tac : thm -> Proof.context -> int -> tactic

  (*protect premises starting from the given index in the specified subgoal*)
  val protect_tac : int -> Proof.context -> int -> tactic
  (*unprotect the subgoal*)
  val unprotect_tac : int -> tactic
  (*protect premises starting from the given index in the specified subgoal,
    then apply tactic, then unprotect*)
  val protected_tac : int -> (int -> tactic) -> Proof.context -> int -> tactic

  (*focus on the specified subgoal, introducing only the specified list of premises
    as theorems in the focus*)
  val focus_prems_tac : int list -> (Subgoal.focus -> int -> tactic) ->
    Proof.context -> int -> tactic
  (*calls focus_prems_tac tac and then deletes all focused premises*)
  val focus_delete_prems_tac : int list -> (Subgoal.focus -> int -> tactic) ->
    Proof.context -> int -> tactic

  (*apply tactic to the specified goal (given as a cterm)*)
  val apply_tac : (int -> tactic) -> int -> cterm -> thm Seq.seq

end

structure Tactic_Util : TACTIC_UTIL =
struct

(* tactic combinators *)
fun HEADGOAL f = f 1

fun TRY' tac =  tac ORELSE' K all_tac

fun EVERY_ARG tac = EVERY o map tac
fun EVERY_ARG' tac = EVERY' o map tac

fun CONCAT tacs = fold_rev (curry op APPEND) tacs no_tac
fun CONCAT' tacs = fold_rev (curry op APPEND') tacs (K no_tac)


fun FOCUS_PARAMS' tac = Subgoal.FOCUS_PARAMS (HEADGOAL o tac)
fun FOCUS_PARAMS_FIXED' tac = Subgoal.FOCUS_PARAMS_FIXED (HEADGOAL o tac)
fun FOCUS_PREMS' tac = Subgoal.FOCUS_PREMS (HEADGOAL o tac)
fun FOCUS' tac = Subgoal.FOCUS (HEADGOAL o tac)
fun SUBPROOF' tac = Subgoal.SUBPROOF (HEADGOAL o tac)

fun FOCUS_PARAMS_CTXT tac = Subgoal.FOCUS_PARAMS (#context #> tac)
fun FOCUS_PARAMS_CTXT' tac = FOCUS_PARAMS' (#context #> tac)

fun CSUBGOAL_DATA f tac = CSUBGOAL (uncurry tac o apfst f)
fun CSUBGOAL_STRIPPED f = CSUBGOAL_DATA (f o Term_Util.strip_cgoal)
fun SUBGOAL_DATA f tac = SUBGOAL (uncurry tac o apfst f)
fun SUBGOAL_STRIPPED f = SUBGOAL_DATA (f o Term_Util.strip_goal)

(* tactics *)
fun insert_tac thm = resolve0_tac [thm COMP revcut_rl]

fun thin_tac n = rotate_tac n THEN' (DETERM o eresolve0_tac [thin_rl]) THEN' rotate_tac (~n)
fun thin_tacs delete_is = EVERY_ARG' thin_tac (sort int_ord delete_is |> map_index ((op -) o swap))

fun nth_assume_tac n ctxt = rotate_tac n THEN' assume_tac ctxt

(*resolution*)
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

fun apply_tac tac i = Goal.init #> tac i #> Seq.map Goal.conclude

fun protect_tac n ctxt =
  let fun protect ct i =
    let val nprems = Logic.count_prems (Thm.term_of ct)
    in
      if nprems < n then no_tac
      else
        let
          val ctrimmed = funpow n (Thm.dest_implies #> snd) ct
          val protect_thm = Drule.protectD
            |> Thm.instantiate (TVars.empty, Vars.make [((("A", 0), propT), ctrimmed)])
        in
        resolve_tac ctxt [protect_thm] i
        THEN REPEAT_DETERM_N (nprems - n) (thin_tac n i)
        THEN EVERY_ARG (fn n => nth_assume_tac n ctxt (i + 1)) (n upto nprems - 1)
      end
    end
  in if n < 0 then K no_tac else CSUBGOAL (uncurry protect) end

val unprotect_tac = resolve0_tac [Drule.protectI]

fun protected_tac n tac ctxt =
  protect_tac n ctxt
  THEN' tac
  THEN_ALL_NEW unprotect_tac

fun focus_prems_tac is tac ctxt =
  CONVERSION (Conversion_Util.move_prems_to_front_conv is)
  THEN' protect_tac (length is) ctxt
  THEN' FOCUS' (fn {context=ctxt, params=params, prems=prems,
    asms=asms, concl=concl, schematics=schematics} =>
    let val concl = Term_Util.unprotect concl
    in
      unprotect_tac
      THEN' tac {context=ctxt, params=params, prems=prems, asms=asms, concl=concl, schematics=schematics}
    end
  ) ctxt

fun focus_delete_prems_tac is tac ctxt =
  focus_prems_tac is tac ctxt
  THEN' thin_tacs (0 upto length is - 1)


end
