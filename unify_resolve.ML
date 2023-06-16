(*  Title:      E_Unification/unify_resolve.ML
    Author:     Kevin Kappelmann

Resolution with parametrised unification function.
*)
signature UNIFY_RESOLVE =
sig
  include HAS_LOGGER

  val no_lift_biresolve_tac : bool -> thm -> int -> Proof.context -> int -> tactic
  val no_lift_resolve_tac : thm -> int -> Proof.context -> int -> tactic
  val no_lift_eresolve_tac : thm -> int -> Proof.context -> int -> tactic

  val unify_resolve_tac : Normalisation.thm_normaliser ->
    Unification_Base.unifier -> thm -> Proof.context -> int -> tactic
  val unify_resolves_tac : Normalisation.thm_normaliser ->
    Unification_Base.unifier -> thm list -> Proof.context -> int -> tactic
  val any_unify_resolve_tac : Normalisation.thm_normaliser ->
    Unification_Base.unifier -> thm list -> Proof.context -> int -> tactic

  val no_lift_any_unify_resolve_tac : Normalisation.thm_normaliser ->
    Unification_Base.unifier -> thm list -> Proof.context -> int -> tactic


end

structure Unify_Resolve : UNIFY_RESOLVE =
struct

val logger = Logger.setup_new_logger Unification_Base.logger "Unify_Resolve"

structure UBase = Unification_Base
structure Util = Unification_Util

fun no_lift_biresolve_tac eres brule nsubgoals ctxt =
  Thm.bicompose (SOME ctxt) {flatten = true, match = true, incremented = true}
  (eres, brule, nsubgoals)
  #> PRIMSEQ

val no_lift_resolve_tac = no_lift_biresolve_tac false
val no_lift_eresolve_tac = no_lift_biresolve_tac true

fun rewrite_subgoal_tac eq_thm =
  let
    val (lhs, rhs) = Thm.dest_equals (Thm.cconcl_of eq_thm)
    val eq_elim = Thm.instantiate' [] [SOME lhs, SOME rhs] Drule.equal_elim_rule2
    val thm = Thm.implies_elim eq_elim eq_thm
  in no_lift_resolve_tac thm 1 end

fun unify_resolve_tac norm_thm unify rule ctxt =
  let fun tac cgoal i state =
    let
      val _ = @{log Logger.DEBUG} ctxt (fn _ =>
          Pretty.block [
            Pretty.str ("Calling unification resolution tactic on subgoal "),
            Pretty.str (Int.toString i),
            Pretty.str ": ",
            Util.pretty_terms ctxt [Thm.term_of cgoal],
            Pretty.str (" and rule "),
            Util.pretty_thm ctxt rule
          ]
          |> Pretty.string_of
        )
      val lifted_rule = Thm.lift_rule cgoal rule
      val nprems_rule = Thm.nprems_of rule
      fun get_lifted_rule_concl_rparams lifted_rule =
        Logic.strip_prems (nprems_rule, [], Thm.prop_of lifted_rule)
        |> snd
        |> (`) Logic.strip_params
        |> apfst rev
      val (rparams, lifted_rule_concl) = get_lifted_rule_concl_rparams lifted_rule
      val (binders, ctxt) = UBase.fix_binders rparams ctxt
      val conclp = (*only unify the conclusion of the goal and the rule*)
        apply2 Logic.strip_assums_concl (Thm.term_of cgoal, lifted_rule_concl)
      val env_thmq = unify binders ctxt conclp (Envir.empty (Thm.maxidx_of lifted_rule))
      fun rewrite_tac (env, unif_thm) =
        let
          (*normalise wrt. environment*)
          val norm_thm = norm_thm ctxt env
          val unif_thm = norm_thm unif_thm
          val lifted_rule = norm_thm lifted_rule
          val (rparams, lifted_rule_concl) = get_lifted_rule_concl_rparams lifted_rule
          val _ = @{log Logger.TRACE} ctxt (fn _ => Pretty.block [
              Pretty.str "Lifting unification theorem ",
              Util.pretty_thm ctxt unif_thm
            ] |> Pretty.string_of)
          (*update types and certify fresh Frees of binders*)
          val cbinders = map2
            (fn (_, T) => apsnd (fn Free (n, _) => Thm.cterm_of ctxt (Free (n, T))))
            rparams binders
          (*certified premises with Bounds replaced by fresh Frees*)
          val cfree_prems = Logic.strip_assums_hyp lifted_rule_concl
            |> map (Thm.cterm_of ctxt o UBase.replace_binders binders)
          fun all_abstract ((x, T), cfree) =
            let val all_const = Logic.all_const T |> Thm.cterm_of ctxt
            in
              Unification_Base.abstract_rule x cfree
              #> Drule.arg_cong_rule all_const
            end
          val unif_thm = (*introduce the premises*)
            fold_rev (Drule.imp_cong_rule o Thm.reflexive) cfree_prems unif_thm
            (*introduce abstractions for the fresh Frees*)
            |> fold all_abstract cbinders
          val _ = @{log Logger.TRACE} ctxt (fn _ => Pretty.block [
              Pretty.str "Lifted unification theorem ",
              Util.pretty_thm ctxt unif_thm
            ] |> Pretty.string_of)
        in
          (PRIMITIVE norm_thm |> K)
          THEN' rewrite_subgoal_tac unif_thm ctxt
          THEN' no_lift_resolve_tac lifted_rule nprems_rule ctxt
        end
    in Seq.maps (fn res => rewrite_tac res i state) env_thmq end
  in Tactic_Util.CSUBGOAL_DATA I tac end

fun unify_resolve_tacs norm_thm unify rules ctxt =
  map (fn rule => unify_resolve_tac norm_thm unify rule ctxt) rules

fun unify_resolves_tac norm_thm unify rules =
  unify_resolve_tacs norm_thm unify rules #> EVERY'

fun any_unify_resolve_tac norm_thm unify rules =
  unify_resolve_tacs norm_thm unify rules #> Tactic_Util.CONCAT'

fun no_lift_unify_resolve_tac norm_thm unify rule ctxt =
  let fun tac cgoal i state =
    let
      val rule = Thm.incr_indexes (Thm.maxidx_of state + 1) rule
      (*fix parameters of goal*)
      val ((params, cgoal_focused), ctxt_focused) = Variable.focus_cterm NONE cgoal ctxt
        |>> apfst (map snd)
      val goal_focused = Thm.term_of cgoal_focused
      val _ = @{log Logger.DEBUG} ctxt_focused (fn _ =>
          Pretty.block [
            Pretty.str ("Calling unification resolution tactic on focused subgoal "),
            Pretty.str (Int.toString i),
            Pretty.str ": ",
            Util.pretty_terms ctxt_focused [goal_focused],
            Pretty.str (" and rule "),
            Util.pretty_thm ctxt_focused rule
          ]
          |> Pretty.string_of
        )
      val goal_concl = Logic.strip_imp_concl goal_focused
      val rule_concl = Thm.concl_of rule
      val rule_nprems = Thm.nprems_of rule
      val conclp = (goal_concl, rule_concl)
      val env_thmq = unify [] ctxt_focused conclp (Envir.empty (Thm.maxidx_of rule))
      fun update_goal (env, unif_thm) =
        let
          (*normalise all components wrt. env*)
          val norm_thm_inst = norm_thm ctxt_focused env
          val inst_state = norm_thm_inst state
          val inst_cgoal = Thm.cprem_of inst_state i
          val norm_param = Thm.reflexive
            #> norm_thm_inst
            #> Thm.cprop_of
            #> Thm.dest_equals_rhs
          val inst_params = map norm_param params
          val inst_rule = norm_thm_inst rule
          val inst_unif_thm = norm_thm_inst unif_thm
          val _ = @{log Logger.TRACE} ctxt_focused (fn _ =>
              Pretty.block [
                Pretty.str ("Unification resolution tactic result on subgoal "),
                Pretty.str (Int.toString i),
                Pretty.str ": ",
                Util.pretty_thm ctxt_focused inst_unif_thm
              ]
              |> Pretty.string_of
            )
          fun rewrite_rule eq_thm rule =
            let
              val (lhs, rhs) = Thm.dest_equals (Thm.cconcl_of eq_thm)
              val eq_elim = Thm.instantiate' [] [SOME lhs, SOME rhs] Drule.equal_elim_rule2
            in
              Thm.implies_elim eq_elim eq_thm
              |> HEADGOAL (no_lift_resolve_tac rule rule_nprems ctxt_focused)
            end
          fun lift_rule rule =
            let
              val maxidx_inst_goal = Thm.maxidx_of_cterm inst_cgoal
              val inst_paramTs = map Thm.typ_of_cterm inst_params
              val (param_vars, maxidx_params) =
                Util.fresh_vars "p" inst_paramTs maxidx_inst_goal
              val num_params = maxidx_params - maxidx_inst_goal
              val cparam_vars = map (Thm.cterm_of ctxt_focused) param_vars
              val rule =
                (*abstract parameters*)
                Drule.forall_intr_list inst_params rule
                (*instantiate meta variables*)
                |> Drule.forall_elim_list cparam_vars
                (*lift*)
                |> Thm.lift_rule inst_cgoal
              (*lifting the rule shifts the indexes of variables*)
              val idx_lift_offset = maxidx_inst_goal + 1
              (*computes the index of a variable before it was lifted*)
              fun comp_old_idx idx = idx - idx_lift_offset
              (*checks whether a variable corresponds to a goal parameter,
                as identified by the unifier*)
              val is_param =
                let val adjusted_param_names =
                  map (fn Var ((n, idx), _) => (n, idx + idx_lift_offset)) param_vars
                in member Term.eq_ix adjusted_param_names end
              (*compute the substitutions*)
              val rule_prop = Thm.prop_of rule
              val rule_tvars = build (Term.add_tvars rule_prop)
              fun adjust_tvar (var as ((n, idx), s)) acc =
                if idx <= maxidx_inst_goal then acc
                else
                  let val cvar = TVar ((n, comp_old_idx idx), s) |> Thm.ctyp_of ctxt
                  in TVars.add (var, cvar) acc end
              val inst_tvars = fold adjust_tvar rule_tvars TVars.empty
              val rule_vars = build (Term.add_vars rule_prop)
              fun mk_abs [] body = body
                | mk_abs (T :: Ts) body = Abs ("", T, mk_abs Ts body)
              fun add_abstractions (name as (n, idx), T) acc =
                if idx <= maxidx_inst_goal then acc
                else
                  let
                    val body = if is_param name
                      (*project to the correct, newly bound parameter*)
                      then Bound (num_params - 1 - (idx - 2 * idx_lift_offset))
                      (*ignore the newly introduced parameters*)
                      else
                        let val smallerT = strip_type T
                          |>> drop num_params
                          |> (op --->)
                        in Var ((n, comp_old_idx idx), smallerT) end
                    val cabs = mk_abs inst_paramTs body
                      |> Thm.cterm_of ctxt
                      |> Thm.instantiate_cterm (inst_tvars, Vars.empty)
                  in Vars.add ((name, Thm.typ_of_cterm cabs), cabs) acc end
              val inst_vars = fold add_abstractions rule_vars Vars.empty
              val rule = Thm.instantiate (inst_tvars, inst_vars) rule
                (*we must not forget to normalise since we may have created redexes*)
                (* |> norm_thm ctxt Envir.init *)
            in rule end
          val rulesq = rewrite_rule inst_unif_thm inst_rule |> Seq.map lift_rule
          val updated_statesq =
            Seq.maps (fn rule => no_lift_resolve_tac rule rule_nprems ctxt i inst_state) rulesq
        in updated_statesq end
    in Seq.maps update_goal env_thmq end
  in Tactic_Util.CSUBGOAL_DATA I tac end

fun no_lift_unify_resolve_tacs norm_thm unify rules ctxt =
  map (fn rule => no_lift_unify_resolve_tac norm_thm unify rule ctxt) rules

fun no_lift_unify_resolves_tac norm_thm unify rules =
  no_lift_unify_resolve_tacs norm_thm unify rules #> EVERY'

fun no_lift_any_unify_resolve_tac norm_thm unify rules =
  no_lift_unify_resolve_tacs norm_thm unify rules #> Tactic_Util.CONCAT'


end
