\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Assumption Tactic\<close>
theory Unify_Assumption_Tactic
  imports
    ML_Functor_Instances
    ML_Unifiers
    ML_Unification_Parsers
begin

ML_file\<open>unify_assumption_base.ML\<close>
ML_file\<open>unify_assumption.ML\<close>

ML\<open>
  @{functor_instance struct_name = Standard_Unify_Assumption
    and functor_name = Unify_Assumption
    and id = \<open>""\<close>
    and more_args = \<open>val init_args = {
      normaliser = SOME Envir_Normalisation.norm_thm_unif,
      unifier = SOME Mixed_Unification.first_higherp_comb_higher_unify
    }\<close>}
\<close>
local_setup \<open>Standard_Unify_Assumption.setup_attribute NONE\<close>
local_setup \<open>Standard_Unify_Assumption.setup_method NONE\<close>

experiment
begin
schematic_goal "PROP P \<Longrightarrow> PROP P"
  by uassm

lemma
  assumes h: "\<And>P. PROP P"
  shows "PROP P x"
  using h by uassm

schematic_goal "\<And>x. PROP P (c :: 'a) \<Longrightarrow> PROP ?Y (x :: 'a)"
  (* using [[uassm unifier = First_Order_Unification.unify]] *)
  by uassm

schematic_goal a: "PROP ?P (y :: 'a) \<Longrightarrow> PROP ?P (?x :: 'a)"
  (* by assumption *)
  by uassm

schematic_goal
  "PROP ?P (x :: 'a) \<Longrightarrow> PROP P (?x :: 'a)"
  (* by assumption *)
  by uassm

schematic_goal
  "\<And>x. PROP D \<Longrightarrow> (\<And>P y. PROP P y x) \<Longrightarrow> PROP C \<Longrightarrow> PROP P x"
  (* by assumption *)
  by (uassm unifier = Higher_Order_Unification.unify)

lemma "\<And>x. PROP D \<Longrightarrow> (\<And>y. PROP A y \<Longrightarrow> PROP B x) \<Longrightarrow> PROP C \<Longrightarrow> PROP A x \<Longrightarrow> PROP B x"
  (* by assumption *)
  by uassm

lemma "\<And>x. PROP D \<Longrightarrow> (\<And>y. PROP A y \<Longrightarrow> PROP B x) \<Longrightarrow> PROP A x \<Longrightarrow> PROP C \<Longrightarrow> PROP B x"
  by assumption
  (* by uassm *)
end

end
