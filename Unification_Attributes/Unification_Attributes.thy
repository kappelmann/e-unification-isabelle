\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Unification Attributes\<close>
theory Unification_Attributes
  imports Unify_Resolve_Tactics
begin

ML_file\<open>unify_of_base.ML\<close>
ML_file\<open>unify_of.ML\<close>

ML\<open>
  @{functor_instance struct_name = Standard_Unify_OF
    and functor_name = Unify_OF
    and id = \<open>""\<close>
    and more_args = \<open>val init_args = {
      normaliser = SOME Envir_Normalisation.norm_thm_unif,
      unifier = SOME Mixed_Unification.first_higherp_comb_higher_unify,
      mode = SOME (Unify_OF_Args.PM.key Unify_OF_Args.PM.fact)
    }\<close>}
\<close>
local_setup \<open>Standard_Unify_OF.setup_attribute NONE\<close>

experiment
begin
lemma
  assumes h1: "(PROP A \<Longrightarrow> PROP D) \<Longrightarrow> PROP E \<Longrightarrow> PROP C"
  assumes h2: "PROP B \<Longrightarrow> PROP D"
  and h3: "PROP F \<Longrightarrow> PROP E"
  shows "(PROP A \<Longrightarrow> PROP B) \<Longrightarrow> PROP F \<Longrightarrow> PROP C"
  by (fact h1[uOF h2 h3 where mode = resolve])

lemma
  assumes h1: "\<And>x y z. PROP P x y \<Longrightarrow> PROP P y y \<Longrightarrow> (PROP A \<Longrightarrow> PROP A) \<Longrightarrow>
    (PROP A \<Longrightarrow> PROP B) \<Longrightarrow> PROP C"
  and h2: "\<And>x y. PROP P x y"
  and h3 : "PROP A \<Longrightarrow> PROP A"
  and h4 : "PROP D \<Longrightarrow> PROP B"
  shows "(PROP A \<Longrightarrow> PROP D) \<Longrightarrow> PROP C"
  by (fact h1[uOF h2 h2 h3, uOF h4 where mode = resolve])
end

lemma
  assumes h1: "\<And>P C. PROP P y \<Longrightarrow> PROP C y y"
  and h2: "PROP P y"
  shows "PROP C y y"
  (* thm h1[uOF h2] *)
  (* thm h1[OF h2] *)
  by (fact h1[uOF h2])
end
