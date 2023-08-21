\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Resolution Tactics\<close>
theory Unify_Resolve_Tactics
  imports Unify_Assumption_Tactic
begin

ML_file\<open>unify_resolve_base.ML\<close>
ML_file\<open>unify_resolve.ML\<close>

ML\<open>
  @{functor_instance struct_name = Standard_Unify_Resolve
    and functor_name = Unify_Resolve
    and id = \<open>""\<close>
    and more_args = \<open>val init_args = {
      normaliser = SOME Envir_Normalisation.norm_thm_unif,
      unifier = SOME Mixed_Unification.first_higherp_comb_higher_unify,
      mode = SOME (Unify_Resolve_Args.PM.key Unify_Resolve_Args.PM.any),
      chained = SOME (Unify_Resolve_Args.PCM.key Unify_Resolve_Args.PCM.resolve)
    }\<close>}
\<close>
local_setup \<open>Standard_Unify_Resolve.setup_set_args_attribute NONE\<close>
local_setup \<open>Standard_Unify_Resolve.setup_method NONE\<close>


experiment
begin
lemma
  assumes h1: "\<And>x y. PROP C y \<Longrightarrow> PROP D x \<Longrightarrow> PROP C x"
  and h2: "\<And>x y. PROP C x \<Longrightarrow> PROP D x"
  and h3: "\<And>x y. PROP C x"
  shows "\<And>x. PROP A x \<Longrightarrow> PROP B x \<Longrightarrow> PROP C x"
  (* apply (urule h1) *)
  (* apply (urule h1 where unifier = Higher_Order_Pattern_Unification.unify) *)
  (* apply (urule h1 where unifier = First_Order_Unification.unify) *)
  (* using [[urule unifier = First_Order_Unification.unify]] apply (urule h1) *)
  using h3
    apply (urule h1 h2 where mode = every)
    (* apply (urule h1 h2)+ *)
    (* apply (intro h1) *)
    (* apply (urule h1 where chained = fact)+ *)
    (* apply (urule h1 where chained = insert)+ *)
  done

lemma
  assumes h1: "\<And>x y. PROP C y \<Longrightarrow> PROP A x \<Longrightarrow> PROP C x"
  and h2: "\<And>x y. PROP C x \<Longrightarrow> PROP B x \<Longrightarrow> PROP D x"
  and h3: "\<And>x y. PROP C x"
  shows "\<And>x. PROP A x \<Longrightarrow> PROP B x \<Longrightarrow> PROP C x"
  using h3
    apply (urule (d) h1 h2 where mode = every)
  oops

lemma
  assumes h1: "\<And>x y. PROP C x \<Longrightarrow> PROP A x \<Longrightarrow> PROP C x"
  and h2: "\<And>x y. PROP E \<Longrightarrow> PROP C x"
  shows "\<And>x. PROP A x \<Longrightarrow> PROP B x \<Longrightarrow> PROP C x"
  (* using h3 apply (rule h1) *)
  using h2 apply (urule h1)
  oops

lemma
  assumes h1: "PROP A \<Longrightarrow> PROP B"
  and h2 : "PROP B \<Longrightarrow> PROP C"
  shows "PROP D \<Longrightarrow> PROP C"
  using h1 apply (urule h2)
  oops

lemma
  assumes h1: "PROP A \<Longrightarrow> PROP B"
  and h2 : "(PROP A \<Longrightarrow> PROP B) \<Longrightarrow> PROP C"
  shows "PROP D \<Longrightarrow> PROP C"
  (* using h1 apply (urule h2 where chained = fact) *)
  (* using h1 apply (urule h2 where chained = resolve) *)
  (* using h1 apply (urule h2 where chained = insert) *)
  oops
end
end
