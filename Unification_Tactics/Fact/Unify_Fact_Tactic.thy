\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Fact Tactic\<close>
theory Unify_Fact_Tactic
  imports Unify_Resolve_Tactics
begin

ML_file\<open>unify_fact_base.ML\<close>
ML_file\<open>unify_fact.ML\<close>

ML\<open>
  @{functor_instance struct_name = Standard_Unify_Fact
    and functor_name = Unify_Fact
    and id = \<open>""\<close>
    and more_args = \<open>val init_args = {
      normaliser = SOME Envir_Normalisation.norm_thm_unif,
      unifier = SOME Mixed_Unification.first_higherp_comb_higher_unify
    }\<close>}
\<close>
local_setup \<open>Standard_Unify_Fact.setup_attribute NONE\<close>
local_setup \<open>Standard_Unify_Fact.setup_method NONE\<close>

experiment
begin
lemma
  assumes h1: "\<And>x y. PROP P x y"
  shows "\<And>x y z. PROP P y y"
  by (ufact h1)

lemma
  assumes h1: "\<And>x y. PROP A x \<Longrightarrow> PROP B x \<Longrightarrow> PROP P x"
  and h2: "\<And>x y. PROP B x \<Longrightarrow> PROP B x \<Longrightarrow> PROP P x"
  shows "\<And>x y. PROP A x \<Longrightarrow> PROP B x \<Longrightarrow> PROP P x"
  using h1 apply (ufact h2)
  (* using h1 *)
    (* and [[ufact unifier = Higher_Order_Pattern_Unification.unify]] *)
    (* apply (ufact h2 where unifier = Higher_Order_Pattern_Unification.unify) *)
  done
end

end
