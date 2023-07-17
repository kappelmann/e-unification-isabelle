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

  val fold_rev_index: (int * 'a -> 'b -> 'b) -> 'a list -> 'b -> 'b
end

structure General_Util : GENERAL_UTIL =
struct

fun flip f x y = f y x
fun nth_replace n x = nth_map n (K x)

fun find_first_index p = get_index (Option.filter p)

fun try_bool f = try f #> (Option.getOpt o rpair false)

fun fold_rev_index f =
  let fun fold_aux _ [] y = y
        | fold_aux i (x :: xs) y = f (i, x) (fold_aux (i + 1) xs y)
  in fold_aux 0 end

end