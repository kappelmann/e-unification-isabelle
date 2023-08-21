(*  Title:      ML_Unification/unification_parser.ML
    Author:     Kevin Kappelmann

Common parsers needed for unification attributes, tactics, methods.
*)
signature UNIFICATION_PARSER =
sig
  val parse_normaliser : ML_Code_Util.code parser
  val parse_unifier : ML_Code_Util.code parser
end

structure Unification_Parser : UNIFICATION_PARSER =
struct

val parse_normaliser = Parse_Util.parse_nonempty_code (K "normaliser must not be empty")
val parse_unifier = Parse_Util.parse_nonempty_code (K "unifier must not be empty")

end