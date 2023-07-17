\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Tactics With Adjustable Unifiers\<close>
theory ML_Unification_Tactics
  imports
    ML_Unification_Base
    ML_Unification
    Main
    Logging.ML_Attributes
begin

ML_file\<open>unification_tactic_util.ML\<close>
ML_file\<open>unify_assume.ML\<close>
ML_file\<open>unify_resolve.ML\<close>

(* declare [[ML_Kdattr \<open>set_unifier First_Order_Unification.unify\<close>]] *)

lemma
  assumes a: "\<And>x y. A x \<Longrightarrow> P x"
  shows "\<And>x. L x \<Longrightarrow> A x \<Longrightarrow> P x"
  by (unif_rule a)


end
