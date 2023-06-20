(*  Title:      ML_Utils/conversion_util.ML
    Author:     Kevin Kappelmann

Conversion utilities.
*)
signature CONVERSION_UTIL =
sig
  val move_prem_to_front_conv : int -> conv
  val move_prems_to_front_conv : int list -> conv
  val thm_conv : conv -> thm -> thm
  val binop_conv : conv -> conv -> conv
  val lhs_conv : conv -> conv
  val rhs_conv : conv -> conv
end

structure Conversion_Util : CONVERSION_UTIL =
struct

fun move_prem_to_front_conv 0 = Conv.all_conv
  | move_prem_to_front_conv i = Conv.implies_concl_conv (move_prem_to_front_conv (i - 1))
    then_conv Conv.rewr_conv Drule.swap_prems_eq

val move_prems_to_front_conv = sort (rev_order o int_ord)
  #> map_index (op +)
  #> map move_prem_to_front_conv
  #> Conv.every_conv

val thm_conv = Conv.fconv_rule

fun binop_conv conv_lhs conv_rhs =
  Conv.combination_conv (Conv.arg_conv conv_lhs) conv_rhs

val lhs_conv = Conv.arg1_conv
val rhs_conv = Conv.arg_conv

end
