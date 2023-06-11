chapter "ML-Unification"

session ML_Utils in ML_Utils = "Pure" +
  theories
    ML_Utils

session ML_Unification = "Pure" +
  sessions
    Logging
    ML_Utils
  theories
    ML_Unification
    ML_Unification_Resolution

session ML_Unification_Tests in "Tests" = "HOL" +
  sessions
    SpecCheck
    ML_Unification
  directories
    "../Examples"
  theories
    First_Order_ML_Unification_Tests
    Higher_Order_Pattern_ML_Unification_Tests
    Higher_Order_ML_Unification_Tests
    ML_Unification_Hints_Examples
