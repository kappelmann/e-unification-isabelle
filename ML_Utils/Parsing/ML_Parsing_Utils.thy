\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>ML Parsing Utils\<close>
theory ML_Parsing_Utils
  imports
    ML_Utils_Base
begin

paragraph \<open>Summary\<close>
text \<open>Parsing utilities for ML. We provide an antiquotation that takes a list of
keys and creates a corresponding record with getters and mappers and a parser for corresponding
key-value pairs.\<close>

ML_file\<open>parse_util.ML\<close>

ML_file\<open>parse_key_value.ML\<close>
ML_file\<open>parse_key_value_antiquot.ML\<close>

(*use the following to test the code generation*)
(* ML_command\<open>
  Parse_Key_Value_Antiquot.mk_all "Test" NONE ["ABC", "DEFG" ]
  |> split_lines |> map Pretty.str |> Pretty.fbreaks |> Pretty.block |> Pretty.writeln
\<close> *)

(*example parser*)
ML_command\<open>
  (*create record type and utility functions*)
  @{parse_entries (struct) Test [ABC, DEFG]}

  val parser =
    let
      (*create the key-value parser*)
      val parse_entry = Parse_Key_Value.parse_entry
        Test.parse_key (*parser for keys*)
        (Scan.succeed [])  (*delimiter parser*)
        (Test.parse_entry (*value parser*)
          Parse.string (*parser for ABC*)
          Parse.int) (*parser for DEFG*)
      val required_keys = [Test.key Test.ABC] (*required keys*)
      val default_entries = Test.empty_entries () (*default values for entries*)
    in Test.parse_entries_required Parse.and_list1 required_keys parse_entry default_entries end
  (*parses, for example,
    - \<open>ABC = hello and DEFG = 3\<close>,
    - \<open>DEFG = 3 and ABC = hello\<close>
  but not \<open>DEFG = 3\<close> since the key "ABC" is missing.*)
\<close>

end
