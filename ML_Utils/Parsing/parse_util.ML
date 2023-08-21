(*  Title:      ML_Utils/parse_util.ML
    Author:     Kevin Kappelmann

Parsing utilities.
*)
signature PARSE_UTIL =
sig
  val !!!+ : 'a context_parser -> 'a context_parser

  (*indexed state monad (generalising parsers and context parsers)*)
  type ('i, 'j, 'a) istate = 'i -> 'a * 'j

  (*"if_ahead p1 f p2" applies f to result of p1 if p1 is successful; otherwise runs p2*)
  val if_ahead : ('a, 'b, 'c) istate -> ('c -> 'a -> 'd) -> ('a, 'a, 'd) istate ->
    ('a, 'a, 'd) istate

  (*if_ahead applied to end-of-file parser*)
  val if_eof : (string -> Token.T list -> 'a) -> 'a parser -> 'a parser
  val if_eof' : (string -> Context.generic * Token.T list -> 'a) -> 'a context_parser ->
    'a context_parser

  val option : 'a parser -> ('a option) parser
  val option' : 'a context_parser -> ('a option) context_parser

  val parse_position : 'a parser -> ('a * Position.T) parser
  val parse_position' : 'a context_parser -> ('a * Position.T) context_parser

  val fail : ('a -> string) -> 'a -> 'b
  (*scanner raising Scan.ABORT with given error message*)
  val abort : (Token.T list -> string) -> 'a parser
  val abort' : (Context.generic * Token.T list -> string) -> 'a context_parser

  (*filter_parser f c p runs parser p to obtain result x and returns x if f x holds and c x otherwise*)
  val filter_parser : ('a -> bool) -> ('a -> ('b, 'b, 'a) istate) -> ('c, 'b, 'a) istate ->
    ('c, 'b, 'a) istate
  val filter_parser_cut : ('a -> bool) -> ('a -> Token.T list -> string) -> 'a parser -> 'a parser
  val filter_parser_cut' : ('a -> bool) -> ('a -> Context.generic * Token.T list -> string) ->
    'a context_parser -> 'a context_parser

  val parse_nonempty_list : (Token.T list -> string) -> ('a list) parser -> ('a list) parser
  val parse_nonempty_list' : (Context.generic * Token.T list -> string) ->
    ('a list) context_parser -> ('a list) context_parser

  val parse_distinct_list : ('a * 'a -> bool) -> ('a list -> Token.T list -> string) ->
    ('a list) parser -> ('a list) parser
  val parse_distinct_list' : ('a * 'a -> bool) ->
    ('a list -> Context.generic * Token.T list -> string) -> ('a list) context_parser ->
    ('a list) context_parser

  val parse_nonempty_name : (Token.T list -> string) -> string parser

  val parse_code : ML_Code_Util.code parser
  val parse_nonempty_code : (Token.T list -> string) -> ML_Code_Util.code parser

  val parse_bool : bool parser
  val parse_eq : string parser

  val parse_thm : thm context_parser
  val parse_multi_thm : (thm list) context_parser
  val parse_thms : (thm list) context_parser
  val parse_nonempty_thms : (Context.generic * Token.T list -> string) -> (thm list) context_parser
end

structure Parse_Util : PARSE_UTIL =
struct

(*TODO: move to Isabelle kernel*)
fun get_tokens_pos [] = " (end-of-input)"
  | get_tokens_pos (tok :: _) = Position.here (Token.pos_of tok);

fun cut get_pos kind scan =
  let
    fun err (x, NONE) = (fn () => kind ^ get_pos x)
      | err (x, SOME msg) =
          (fn () =>
            let val s = msg () in
              if String.isPrefix kind s then s
              else kind ^ get_pos x ^ ": " ^ s
            end);
  in Scan.!! err scan end;

fun !!!+ scan = cut (get_tokens_pos o snd) "Outer syntax error" scan

fun enum1' sep scan = scan ::: Scan.repeat (Scan.lift (Parse.$$$ sep) |-- !!!+ scan);
fun enum' sep scan = enum1' sep scan || Scan.succeed [];
fun and_list1' scan = enum1' "and" scan;
fun and_list' scan = enum' "and" scan;

type ('i, 'j, 'a) istate = 'i -> 'a * 'j

fun if_ahead parse_ahead f parse =
  (Scan.ahead parse_ahead :|-- (fn st => fn xs => (f st xs, xs))) || parse

fun if_eof parse = if_ahead Parse.eof parse
fun if_eof' parse = if_ahead (Scan.lift Parse.eof) parse

fun option parse = if_eof (K o K NONE) (Scan.option parse)
fun option' parse = if_eof' (K o K NONE) (Scan.option parse)

fun gen_parse_position not_eof parse =
  (Scan.optional (Scan.ahead not_eof >> Token.pos_of) Position.none
  >> (snd o Position.default))
  -- parse
  >> swap

fun parse_position parse = gen_parse_position Parse.not_eof parse
fun parse_position' parse = gen_parse_position (Scan.lift Parse.not_eof) parse

fun fail msg_of = Scan.fail_with (fn x => fn _ => msg_of x)
fun gen_abort cut msg_of = fail msg_of |> cut

fun abort msg_of = gen_abort Parse.!!! msg_of
fun abort' msg_of = gen_abort !!!+ msg_of

fun filter_parser p err parse = parse :|-- (fn x => if p x then pair x else err x)
fun gen_filter_parser_cut abort p msg_of = filter_parser p (abort o msg_of)
fun filter_parser_cut p = gen_filter_parser_cut abort p
fun filter_parser_cut' p = gen_filter_parser_cut abort' p

fun gen_parse_nonempty_list filter_parser_cut msg_of =
  filter_parser_cut (not o null) (K msg_of)
fun parse_nonempty_list msg_of = gen_parse_nonempty_list filter_parser_cut msg_of
fun parse_nonempty_list' msg_of = gen_parse_nonempty_list filter_parser_cut' msg_of

fun gen_parse_distinct_list filter_parser_cut eq =
  filter_parser_cut (not o has_duplicates eq)
fun parse_distinct_list eq = gen_parse_distinct_list filter_parser_cut eq
fun parse_distinct_list' eq = gen_parse_distinct_list filter_parser_cut' eq

fun parse_nonempty_name msg_of = filter_parser_cut (curry (op <>) "") (K msg_of) Args.name

val parse_code = if_eof (K o K []) ML_Code_Util.parse_code
fun parse_nonempty_code msg_of = filter_parser_cut (not o null) (K msg_of) parse_code

val parse_bool = Scan.recover (Args.name >> Value.parse_bool)
  (fail (K "expected \"true\" or \"false\""))

val parse_eq = Parse.$$$ "\<equiv>" || Parse.$$$ "=" || fail (K "expected \"=\" or \"\<equiv>\"")

(*for better error messages than Attrib.thm and friends*)
fun parse_thm x = Attrib.thm x handle ERROR m => fail (K m) ()
fun parse_multi_thm x = Attrib.multi_thm x handle ERROR m => fail (K m) ()
val parse_thms = Scan.repeats parse_multi_thm
fun parse_nonempty_thms msg = parse_nonempty_list' msg parse_thms

end