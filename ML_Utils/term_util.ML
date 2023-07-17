(*  Title:      ML_Utils/term_util.ML
    Author:     Kevin Kappelmann

Term utilities.
*)
signature TERM_UTIL =
sig
  (*return outer parameters in reversed order*)
  val strip_all : term -> (string * typ) list * term
  val strip_call : cterm -> (string * cterm) list * cterm

  val strip_imp : term -> term list * term
  val strip_cimp : cterm -> cterm list * cterm

  (*return outer parameters in reversed order*)
  val strip_goal : term -> (string * typ) list * (term list * term)
  val strip_cgoal : cterm -> (string * cterm) list * (cterm list * cterm)
  val strip_nth_subgoal : int -> thm -> (string * typ) list * (term list * term)
  val strip_nth_csubgoal : int -> thm -> (string * cterm) list * (cterm list * cterm)

  val unprotect : cterm -> cterm
end

structure Term_Util : TERM_UTIL =
struct

val strip_all =
  let fun strip params (Const ("Pure.all", _) $ Abs (a, T, t)) = strip ((a, T) :: params) t
        | strip params t = (params, t)
  in strip [] end

val strip_call =
  let fun strip params ct =
    ((let val (cp as (_, cx)) = Thm.dest_comb ct
    in case apply2 Thm.term_of cp of
        (Const ("Pure.all", _), Abs (a, _, _)) =>
          let val (cf, cb) = Thm.dest_abs_global cx
          in strip ((a, cf) :: params) cb end
      | _ => (params, ct)
    end)
    handle CTERM _ => (params, ct))
  in strip [] end

fun strip_imp t =
  (let
    val (prem, t) = Logic.dest_implies t
    val (prems, concl) = strip_imp t
  in (prem :: prems, concl) end)
  handle TERM _ => ([], t)

fun strip_cimp ct =
  (let
    val (cprem, ct) = Thm.dest_implies ct
    val (cprems, cconcl) = strip_cimp ct
  in (cprem :: cprems, cconcl) end)
  handle TERM _ => ([], ct)

val strip_goal = strip_all ##> strip_imp
val strip_cgoal = strip_call ##> strip_cimp
fun strip_nth_subgoal i = Thm.prop_of #> pair i #> Logic.nth_prem #> strip_goal
fun strip_nth_csubgoal i state = Thm.cprem_of state i |> strip_cgoal

val unprotect = Thm.dest_arg

end