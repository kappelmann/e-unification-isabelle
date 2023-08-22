\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>ML Parsing Utils\<close>
theory ML_Parsing_Utils
  imports
    ML_Utils_Base
    Logging.ML_Attributes
begin

paragraph \<open>Summary\<close>
text \<open>ML Parsing utilities.\<close>

ML_file\<open>parse_util.ML\<close>

ML_file\<open>parse_key_value.ML\<close>
ML_file\<open>parse_key_value_antiquot.ML\<close>

(*use the following to test the code generation*)
(* ML\<open>
val _ = Parse_Key_Value_Antiquot.mk_all "Test" NONE ["ABC", "DEFG" ]
  |> split_lines |> map Pretty.str |> Pretty.fbreaks |> Pretty.block |> Pretty.writeln
\<close> *)

end
