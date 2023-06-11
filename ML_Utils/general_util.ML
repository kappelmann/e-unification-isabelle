(*  Title:      ML_Utils/general_util.ML
    Author:     Kevin Kappelmann

General ML utilities.
*)
signature GENERAL_UTIL =
sig
  val flip : ('a -> 'b -> 'c) -> 'b -> 'a -> 'c
  val nth_replace : int -> 'a -> 'a list -> 'a list
  val find_first_index : ('a -> bool) -> 'a list -> (int * 'a) option
  (*returns false if function throws an exception*)
  val try_bool : ('a -> bool) -> 'a -> bool
end

structure General_Util : GENERAL_UTIL =
struct

fun flip f x y = f y x
fun nth_replace n x = nth_map n (K x)

fun find_first_index p = get_index (Option.filter p)

fun try_bool f = try f #> (Option.getOpt o rpair false)

end