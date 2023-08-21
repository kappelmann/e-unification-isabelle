\<^marker>\<open>creator "Kevin Kappelmann"\<close>
section \<open>Unification Test Setup\<close>
theory ML_Unification_Tests_Base
  imports
    ML_Unification.ML_Unification_Hints
    SpecCheck.SpecCheck
    Main
begin
paragraph \<open>Summary\<close>
text \<open>Shared setup for unification tests.\<close>

ML\<open>
  @{functor_instance struct_name = Test_Unification_Hints
    and functor_name = Named_Theorems_Unification_Hints
    and id = \<open>"test"\<close>}
\<close>

ML_file \<open>tests_base.ML\<close>
ML_file \<open>first_order_unification_tests.ML\<close>

end