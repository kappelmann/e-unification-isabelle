(*  Title:      E_Unification/first_order_unification.ML
    Author:     Kevin Kappelmann, Paul Bachmann

First-order E-unification.
*)
signature FIRST_ORDER_UNIFICATION =
sig
  include HAS_LOGGER

  val e_match : Unification_Base.type_matcher -> Unification_Base.matcher ->
    Unification_Base.matcher
  val match : Unification_Base.matcher
  val match_hints : Unification_Base.matcher

  val e_unify : Unification_Base.type_unifier -> Unification_Base.unifier ->
    Unification_Base.unifier
  val unify : Unification_Base.unifier
  val unify_hints : Unification_Base.unifier

end

structure First_Order_Unification : FIRST_ORDER_UNIFICATION =
struct

val logger = Logger.setup_new_logger Unification_Base.logger "First_Order_Unification"

(* shared utils *)
structure UBase = Unification_Base
structure Util = Unification_Util
structure Norm = Normalisation

exception FALLBACK

(*check if sequence is empty or raise FALLBACK exception*)
fun seq_try sq = Util.seq_try FALLBACK sq

(* first-order E-matching *)
(*Note: by E-matching we mean "matching modulo equalities" in the general sense,
i.e. when matching p \<equiv>? t, t may contain variables.*)
fun e_match match_types match_theory binders ctxt (p, t) env =
  let
    (*standard first-order matcher that calls match_theory on failure;
    generated theorem is already normalised wrt. the resulting environment*)
    fun match binders ctxt (p, t) (env as Envir.Envir {tenv, tyenv,...}) =
      (case (p, t) of
        (Var (x, Tx), _) =>
          (case Envir.lookup1 tenv (x, Norm.norm_type_match tyenv Tx) of
            NONE =>
              if Term.is_open t then
                (@{log Logger.DEBUG} ctxt (fn _ => Pretty.block [
                    Pretty.str "Failed to match (open term) ",
                    Util.pretty_unif ctxt (p, t)
                  ]
                  |> Pretty.string_of);
                (*directly return empty sequence because the theory unifier
                cannot do anything meaningful at this point*)
                raise FALLBACK)
              else
                let val Tt = fastype_of1 (UBase.binder_types binders, t)
                in
                  ((match_types ctxt (Tx, Tt) env, Unification_Base.reflexive_term ctxt t)
                  (*insert new substitution x \<mapsto> t*)
                  |>> Envir.update ((x, Tt), t)
                  |> Seq.single)
                  handle Unification_Base.UNIF => Seq.empty (*types do not match*)
                end
          | SOME p' =>
            if Envir.aeconv (apply2 Envir.beta_norm (p', t)) then
              Seq.single (env, Unification_Base.reflexive_term ctxt t)
            else raise FALLBACK)
      | (Abs (np, Tp, tp), Abs (nt, Tt, tt)) =>
          ((let val name = if np = "" then nt else np
          in
            match_types ctxt (Tp, Tt) env
            |> Util.abstract_abstract (K I) match ctxt binders name Tt (tp, tt)
            |> seq_try
          end)
          handle Unification_Base.UNIF => Seq.empty) (*types do not match*)
      (*eta-expand on the fly*)
      | (Abs (np, Tp, tp), _) =>
          ((let val Ttarg = fastype_of1 (UBase.binder_types binders, t) |> Term.dest_funT |> fst
          in
            match_types ctxt (Tp, Ttarg) env
            |> Util.abstract_abstract (K I) match ctxt binders np Ttarg
                (tp, incr_boundvars 1 t $ Bound 0)
            |> seq_try
          end)
          handle TYPE _ => (@{log Logger.DEBUG} ctxt (fn _ => Pretty.block [
              Pretty.str "First-order matching failed. Term is not of function type ",
              Util.pretty_unif ctxt (p, t)
            ]
            |> Pretty.string_of);
            Seq.empty)
          | Unification_Base.UNIF => Seq.empty) (*types do not match*)
      | (_, Abs (nt, Tt, tt)) =>
          ((let val Tp = Envir.fastype env (UBase.binder_types binders) p
          in
            match_types ctxt (Tp, fastype_of1 (UBase.binder_types binders, t)) env
            |> Util.abstract_abstract (K I) match ctxt binders nt Tt
                (incr_boundvars 1 p $ Bound 0, tt)
            |> seq_try
          end)
          handle Unification_Base.UNIF => Seq.empty) (*types do not match*)
      | (Bound i, Bound j) => Util.bound_bound ctxt i j binders |> Seq.map (pair env)
      | (Free _, Free g) =>
          (*normalise the types in rigid-rigid cases*)
          Util.rigid_rigid Norm.norm_term_types_match match_types ctxt p g env
          |> seq_try
      | (Const _, Const d) =>
          Util.rigid_rigid Norm.norm_term_types_match match_types ctxt p d env
          |> seq_try
      | (f $ x, g $ y) =>
          (*Note: types of recursive theorems are already normalised ==> we have to
          pass the identity type normaliser*)
          Util.comb_comb (K o K I) (match binders) ctxt (f, x) (g, y) env |> seq_try
      | _ => raise FALLBACK)
      handle FALLBACK =>
        let
          val pt = (Norm.beta_norm_term_match env p, t)
          val _ = @{log Logger.DEBUG} ctxt (fn _ => Pretty.block [
              Pretty.str "First-order matching failed. Calling theory matcher for ",
              Util.pretty_unif ctxt pt
            ]
            |> Pretty.string_of)
        in match_theory binders ctxt pt env end
  in
    (@{log Logger.DEBUG} ctxt (fn _ =>
      Pretty.block [
        Pretty.str "First-order matching ",
        Util.pretty_unif ctxt (Norm.norm_term_match env p, t)
      ]
      |> Pretty.string_of);
    match binders ctxt (p, t) env)
  end

(*standard first-order matching*)
val match = e_match Util.match_types (K o K o K o K Seq.empty)

(*first-order matching with hints*)
fun match_hints binders ctxt =
  let
    (*we do not flip the hints since they may indicate on which side of the
      equation variables may be instantiated*)
    val ctxt' = Config.put Unification_Hints.try_symmetric false ctxt
    val hints = Unification_Hints.get_hints ctxt
    (*match already normalises the types*)
    val norm_term_match = Norm.norm_term_match
    val norm_thm_match = Norm.beta_eta_norm_thm (K I) norm_term_match
    fun match binders ctxt =
      let fun match_hint_prems binders ctxt (p, t) env =
        (*normalise wrt. new environment from hint application*)
        match binders ctxt (Norm.beta_norm_term_match env p, t) env
      in
        e_match Util.match_types
          (Unification_Hints.try_hints Higher_Order_Pattern_Unification.match
            norm_term_match norm_thm_match match_hint_prems hints)
          binders ctxt
      end
  in match binders ctxt' end

(* first-order E-unification *)

(*occurs check*)
fun occurs v (Var (x, _)) = x = v
  | occurs v (s $ t) = occurs v s orelse occurs v t
  | occurs v (Abs (_, _, t)) = occurs v t
  | occurs _ _ = false

fun e_unify unify_types unify_theory binders ctxt (s, t) env =
  let
    (*standard first-order unifier that calls unify_theory on failure*)
    fun unif binders ctxt (s, t) env =
      (case (s, t) of
        (Var (x, Tx), _) =>
          let val unif' = unif binders ctxt
          in
            (unif' (Envir.norm_term_same env s, t) env
            handle Same.SAME =>
              (unif' (s, Envir.norm_term_same env t) env
              handle Same.SAME =>
                if Term.is_open t then
                  (@{log Logger.DEBUG} ctxt (fn _ => Pretty.block [
                      Pretty.str "Failed to unify (open term) ",
                      Util.pretty_unif ctxt (s, t)
                    ]
                    |> Pretty.string_of);
                  raise FALLBACK)
                else
                  let
                    val vars_eq = is_Var t andalso x = fst (dest_Var t)
                    fun update_env env =
                      (*unifying x=x ==> no new term substitution necessary*)
                      if vars_eq then env
                      (*insert new substitution x \<mapsto> t*)
                      else Envir.vupdate ((x, Tx), t) env
                  in
                    if not vars_eq andalso occurs x t then
                      (@{log Logger.DEBUG} ctxt (fn _ => Pretty.block [
                          Pretty.str "Failed to unify (occurs check) ",
                          Util.pretty_unif ctxt (s, t)
                        ]
                        |> Pretty.string_of);
                      raise FALLBACK)
                    else
                      ((unify_types ctxt (Tx, Envir.fastype env (UBase.binder_types binders) t) env,
                        Unification_Base.reflexive_term ctxt s)
                      |>> update_env
                      |> Seq.single)
                      handle Unification_Base.UNIF => Seq.empty (*types do not unify*)
                  end))
          end
       | (_, Var _) => unif binders ctxt (t, s) env |> Seq.map (apsnd Unification_Base.symmetric)
       | (Abs (ns, Ts, ts), Abs (nt, Tt, tt)) =>
          ((let val name = if ns = "" then nt else ns
          in
            unify_types ctxt (Ts, Tt) env
            |> Util.abstract_abstract Norm.norm_term_types_unif unif ctxt binders name Ts (ts, tt)
            |> seq_try
          end)
          handle Unification_Base.UNIF => Seq.empty) (*types do not unify*)
      (*eta-expand on the fly*)
      | (Abs (ns, Ts, ts), _) =>
          ((let val Tp = apply2 (Envir.fastype env (UBase.binder_types binders)) (s, t)
          in
            unify_types ctxt Tp env
            |> Util.abstract_abstract Norm.norm_term_types_unif unif ctxt binders ns Ts
              (ts, incr_boundvars 1 t $ Bound 0)
            |> seq_try
          end)
          handle Unification_Base.UNIF => Seq.empty) (*types do not unify*)
      | (_, Abs _) => unif binders ctxt (t, s) env |> Seq.map (apsnd Unification_Base.symmetric)
      | (Bound i, Bound j) => Util.bound_bound ctxt i j binders |> Seq.map (pair env)
      (*we do not have to normalise types in rigid-rigid cases*)
      | (Free _, Free g) => Util.rigid_rigid (K I) unify_types ctxt s g env |> seq_try
      | (Const _, Const d) => Util.rigid_rigid (K I) unify_types ctxt s d env |> seq_try
      (*but we have to normalise types in comb cases*)
      | (f $ x, g $ y) =>
          Util.comb_comb Norm.norm_thm_types_unif (unif binders) ctxt (f, x) (g, y) env
          |> seq_try
      | _ => raise FALLBACK)
      handle FALLBACK =>
        let
          val tp = apply2 (Norm.beta_norm_term_unif env) (s, t)
          val _ = @{log Logger.DEBUG} ctxt (fn _ => Pretty.block [
              Pretty.str "First-order unification failed. Calling theory unifier for ",
              Util.pretty_unif ctxt tp
            ]
            |> Pretty.string_of)
        in unify_theory binders ctxt tp env end
  in
    (@{log Logger.DEBUG} ctxt (fn _ =>
      Pretty.block [
        Pretty.str "First-order unifying ",
        Util.pretty_unif ctxt (apply2 (Norm.norm_term_unif env) (s, t))
      ]
      |> Pretty.string_of);
    unif binders ctxt (s, t) env)
  end

(*standard first-order unification*)
val unify = e_unify Util.unify_types (K o K o K o K Seq.empty)

(*first-order unification with hints*)
fun unify_hints binders ctxt =
  let
    val hints = Unification_Hints.get_hints ctxt
    val norm_term_unif = Norm.norm_term_unif
    val norm_thm_unif = Norm.beta_eta_norm_thm Norm.norm_type_unif norm_term_unif
    fun unify binders ctxt =
      let fun unify_hint_prems binders ctxt tp env =
        (*normalise wrt. new environment from hint application*)
        unify binders ctxt (apply2 (Norm.beta_norm_term_unif env) tp) env
      in
        e_unify Util.unify_types
          (Unification_Hints.try_hints Higher_Order_Pattern_Unification.match
            norm_term_unif norm_thm_unif unify_hint_prems hints)
          binders ctxt
      end
  in unify binders ctxt end

end
