(*  Title:      ML_Unification/unification_parser.ML
    Author:     Kevin Kappelmann

Common parsers needed for unification attributes, tactics, methods.
*)
signature UNIFICATION_PARSER =
sig
  val parse_term_normaliser : ML_Code_Util.code parser
  val parse_thm_normaliser : ML_Code_Util.code parser
  val parse_unifier : ML_Code_Util.code parser
end

structure Unification_Parser : UNIFICATION_PARSER =
struct

val parse_term_normaliser = Parse_Util.nonempty_code (K "term normaliser must not be empty")
val parse_thm_normaliser = Parse_Util.nonempty_code (K "theorem normaliser must not be empty")
val parse_unifier = Parse_Util.nonempty_code (K "unifier must not be empty")

end