(*  Title:      ML_Utils/thm_util.ML
    Author:     Kevin Kappelmann

Theorem utilities.
*)
signature THM_UTIL =
sig
  val implies_elim_list_beta_eta_short : thm -> thm list -> thm
  val transitive_beta_eta_short : thm -> thm -> thm
  val protect : thm -> thm
end

structure Thm_Util : THM_UTIL =
struct

fun implies_elim_list_beta_eta_short thm prems =
  let val norm = Conversion_Util.thm_conv Drule.beta_eta_conversion
  in Drule.implies_elim_list (norm thm) (map norm prems) end

fun transitive_beta_eta_short thm1 thm2 =
  let val norm = Conversion_Util.thm_conv Drule.beta_eta_conversion
  in Thm.transitive (norm thm1) (norm thm2) end

fun protect thm = Drule.protectI
  |> Thm.instantiate (TVars.empty, Vars.make [((("A", 0), propT), Thm.cprop_of thm)])
  |> Thm.elim_implies thm

end