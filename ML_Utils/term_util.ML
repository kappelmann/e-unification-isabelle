(*  Title:      ML_Utils/term_util.ML
    Author:     Kevin Kappelmann

Term utilities.
*)
signature TERM_UTIL =
sig
  val strip_imp : term -> term list * term
  val strip_cimp : cterm -> cterm list * cterm

  val unprotect : cterm -> cterm
end

structure Term_Util : TERM_UTIL =
struct

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

val unprotect = Thm.dest_arg

end