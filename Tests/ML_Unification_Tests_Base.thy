\<^marker>\<open>creator "Kevin Kappelmann"\<close>
section \<open>Unification Test Setup\<close>
theory ML_Unification_Tests_Base
  imports
    Main
    ML_Unification.ML_Unification
    SpecCheck.SpecCheck
begin
paragraph \<open>Summary\<close>
text \<open>Shared setup for unification tests.\<close>

ML_file \<open>tests_base.ML\<close>
ML_file \<open>first_order_unification_tests.ML\<close>


end