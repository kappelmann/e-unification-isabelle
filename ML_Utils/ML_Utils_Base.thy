\<^marker>\<open>creator "Kevin Kappelmann"\<close>
theory ML_Utils_Base
  imports
    ML_Logger.ML_Logger
    ML_Logger.ML_Code_Utils
    ML_Binders
    ML_General_Utils
begin

paragraph \<open>Summary\<close>
text \<open>Basic ML utilities.\<close>

ML_file\<open>term_util.ML\<close>

lemma meta_eq_symmetric: "(A \<equiv> B) \<equiv> (B \<equiv> A)"
  by (rule equal_intr_rule) simp_all
ML_file\<open>conversion_util.ML\<close>

ML_file\<open>thm_util.ML\<close>

ML_file\<open>tactic_util.ML\<close>
ML_file\<open>method_util.ML\<close>

ML_file\<open>ml_attribute_util.ML\<close>

ML_file\<open>ml_syntax_util.ML\<close>

ML_file\<open>pair_generic_data_args.ML\<close>

end
