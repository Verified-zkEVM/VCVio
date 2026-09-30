/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public meta import VCVio.ProgramLogic.Tactics.Unary.Internals

/-!
# Unary VC Tactics

User-facing unary tactics of VCVio's probabilistic VC generator (`pvcstep`, `pvcgen`, and their
finish passes), plus `exp_norm` and `by_hoare`.

The `p` prefix sets them apart from core's `vcgen`, which walks `Std.WP` triples through the
`@[spec]` catalogue and stays available under its own name. `pvcstep` and `pvcgen` work on the
same core triples of oracle computations, read as expectations, and add the probabilistic layer:
lowering of `Pr{…}[…]` goals, bind-swap and congruence on probability equalities, oracle-query
and `simulateQ` rules, support and indicator leaf closure, and the `@[vcspec]` / `@[wpStep]`
registries. `rvcstep` and `rvcgen` are the relational counterparts.
-/

public meta section

open Lean Elab Tactic Meta

namespace OracleComp.ProgramLogic

/-! ## Unary VC tactics -/

private def binderIdentsToNames (ids : Syntax.TSepArray `Lean.binderIdent ",") : Array Name :=
  ids.getElems.map fun
    | `(binderIdent| $name:ident) => name.getId
    | _ => Name.anonymous

private def runVCGenFinish : TacticM Unit := do
  unless (← getGoals).isEmpty do
    -- Only `wp_*`, `propInd_*`, and `game_rule` are kept here; generic ring/if normalization
    -- (`one_mul`, `zero_add`, `ite_true`, `ite_false`, `dite_true`, …) is already in Mathlib's
    -- default simp-set and was rarely firing on the Triple/wp-shaped goals that reach this
    -- finish pass — building those extra simp entries on every `pvcgen` invocation was a
    -- constant tax without an observed win.
    let _ ← tryEvalTacticSyntax
      (← `(tactic| all_goals try simp only [
        OracleComp.ProgramLogic.wp_pure, OracleComp.ProgramLogic.wp_bind,
        OracleComp.ProgramLogic.wp_query, OracleComp.ProgramLogic.wp_ite,
        OracleComp.ProgramLogic.wp_dite, OracleComp.ProgramLogic.wp_map,
        OracleComp.ProgramLogic.wp_uniformSample,
        OracleComp.ProgramLogic.wp_const,
        propInd_true, propInd_false,
        propInd_eq_ite,
        game_rule]))
  unless (← getGoals).isEmpty do
    discard <| tryEvalTacticSyntax
      (← `(tactic| all_goals try
        (refine Std.WP.Triple.intro ?_
         repeat intro _
         simp [Lean.Order.PartialOrder.rel,
           MonadStateOf.get, MonadStateOf.set, MonadReaderOf.read, MonadWriter.tell,
           StateT.get, StateT.set, StateT.lift, ReaderT.read,
           StateT.run_bind, StateT.run_pure, StateT.run_get, StateT.run_set,
           StateT.run_lift, StateT.run_map,
           ReaderT.run_bind, ReaderT.run_pure, ReaderT.run_monadLift, ReaderT.run_read,
           ReaderT.run_map,
           WriterT.wp_apply_eq,
           OracleComp.Quantitative.WriterT.wp_bind,
           OracleComp.Quantitative.WriterT.wp_pure,
           OracleComp.Quantitative.WriterT.wp_tell,
           OracleComp.Quantitative.WriterT.wp_monadLift,
           OracleComp.Quantitative.WriterT.wp_map,
           WriterT.run_bind, WriterT.run_pure, WriterT.run_tell, WriterT.run_map,
           ExactWPMonad.wp_bind, ExactWPMonad.wp_pure, ExactWPMonad.wp_map,
           MonadLift.monadLift, pure_bind, bind_assoc, map_pure, Functor.map_map,
           one_mul, mul_one, mul_assoc]
         try exact le_rfl)))
  unless (← getGoals).isEmpty do
    discard <| tryEvalTacticSyntax
      (← `(tactic| all_goals try
        (simp_rw [← mul_assoc]
         dsimp [StateT.set, ReaderT.run, WriterT.run]
         simp [
           StateT.set, StateT.run_set, StateT.run_pure, StateT.run_monadLift,
           TacticInternals.Unary.wp_StateT_run_set_layer,
           TacticInternals.Unary.wp_StateT_run_set_layer',
           ReaderT.run, ReaderT.run_read, ReaderT.run_pure, ReaderT.run_monadLift,
           TacticInternals.Unary.wp_ReaderT_run_read_layer,
           TacticInternals.Unary.wp_ReaderT_run_read_layer',
           WriterT.wp_apply_eq,
           OracleComp.Quantitative.WriterT.wp_tell,
           OracleComp.Quantitative.WriterT.wp_monadLift,
           WriterT.run_tell, WriterT.run_pure, WriterT.run_monadLift, WriterT.run_map,
           ExactWPMonad.wp_bind, ExactWPMonad.wp_pure, ExactWPMonad.wp_map,
           MonadLift.monadLift, pure_bind, bind_assoc, map_pure, Functor.map_map,
           one_mul, mul_one, mul_assoc]
         try exact le_rfl)))
  unless (← getGoals).isEmpty do
    discard <| runBoundedPasses "pvcgen finish" TacticInternals.Unary.runVCGenClosePass
  unless (← getGoals).isEmpty do
    discard <| tryEvalTacticSyntax
      (← `(tactic| all_goals try
        (simp_rw [← mul_assoc]
         dsimp [StateT.set, ReaderT.run, WriterT.run]
         simp [
           StateT.set, StateT.run_set, StateT.run_pure, StateT.run_monadLift,
           TacticInternals.Unary.wp_StateT_run_set_layer,
           TacticInternals.Unary.wp_StateT_run_set_layer',
           ReaderT.run, ReaderT.run_read, ReaderT.run_pure, ReaderT.run_monadLift,
           TacticInternals.Unary.wp_ReaderT_run_read_layer,
           TacticInternals.Unary.wp_ReaderT_run_read_layer',
           WriterT.wp_apply_eq,
           OracleComp.Quantitative.WriterT.wp_tell,
           OracleComp.Quantitative.WriterT.wp_monadLift,
           WriterT.run_tell, WriterT.run_pure, WriterT.run_monadLift, WriterT.run_map,
           ExactWPMonad.wp_bind, ExactWPMonad.wp_pure, ExactWPMonad.wp_map,
           MonadLift.monadLift, pure_bind, bind_assoc, map_pure, Functor.map_map,
           one_mul, mul_one, mul_assoc]
         try exact le_rfl)))

private def runVCGenStepWithNames (names : Array Name) : TacticM Bool := do
  let target ← instantiateMVars (← getMainTarget)
  if target.isForall then
    return (← introMainGoalNames names)
  if isProbEqGoal target then
    if names.size ≥ 2 then
      if ← TacticInternals.Unary.runProbEqCongrWithNames names then
        return true
    if names.size = 1 then
      if ← TacticInternals.Unary.runProbEqCongrNoSupportWithNames names then
        return true
  if ← TacticInternals.Unary.runVCGenStep then
    introAllGoalsNames names
    renameInaccessibleNames names
    return true
  return false

private def runVCGenStepWithTheoremNames
    (thm : TSyntax `term) (names : Array Name) : TacticM Bool := do
  if ← TacticInternals.Unary.runVCGenStepWithTheorem thm then
    introAllGoalsNames names
    renameInaccessibleNames names
    return true
  return false

private def logPlannerNotes (steps : Array PlannedStep) : TacticM Unit := do
  let mut emitted : Array String := #[]
  for step in steps do
    for note in step.notes do
      unless note = "continuing in raw `wp` mode" do
        continue
      unless emitted.contains note do
        emitted := emitted.push note
        logInfo m!"Planner note: {note}"

/-- `pvcstep` applies one step of VCVio's probabilistic VC generator to a quantitative `Triple`,
raw `wp`, or probability goal about oracle computations. `pvcgen` repeats these steps
exhaustively, and `rvcstep` is the relational counterpart. Core's `vcgen` is a separate tactic
for `Std.WP` triples driven by the `@[spec]` catalogue; `pvcstep` reads core triples of oracle
computations as expectations and adds the probability-specific rules below.

For `Triple` goals: decomposes a bind via `Std.WP.Triple.bind` and automatically tries to close
the spec subgoal using hypotheses in the local context, with backward WP fallback.
Also handles `ite`/`dite` splitting, `match` case analysis, loop invariant auto-detection
from context, and WP-rule unfolding, including `simulateQ ... run'`.
After the built-in leaf rules, it may also use user-authored `@[vcspec]` lemmas whose
registered head symbol matches the current computation.

For `Pr{…}[…] = 1` and lower-bound goals such as `r ≤ Pr{let x ← oa}[p x]`: automatically lowers
the goal into a `Triple` form.

For equalities of events or output measures, such as `Pr{…}[…] = Pr{…}[…]` or
`𝒟[oa] = 𝒟[ob]`: tries bind-swap (`OracleComp.wp_prEvent_swap`, `OracleComp.wp_swap`,
`OracleComp.evalDist_bind_bind_swap`), bind congruence on the support of the shared prefix
(`wp_congr_of_support`, `OracleComp.evalDist_bind_congr_of_support`), and
swap-then-congr.

For other `Pr{…}[…]` goals: rewrites to raw `wp` form and keeps stepping structurally when a `wp`
rule applies, rather than immediately exiting the VCGen pipeline.

Variants:
- `pvcstep using cut` for an explicit intermediate postcondition.
- `pvcstep with thm` to force a specific unary theorem/assumption step.
- `pvcstep inv I` to apply a loop invariant `I` to a `replicate`/`foldlM`/`mapM` goal.
- `pvcstep rw` to perform one explicit top-level probability-equality rewrite step.
- `pvcstep rw under n` to rewrite one bind-swap under `n` shared bind prefixes.
- `pvcstep rw normalize` to run the bounded probability-equality planner explicitly.
- `pvcstep rw congr` to expose one shared bind plus its support hypothesis.
- `pvcstep rw congr'` to expose one shared bind without a support hypothesis.

Use `@[vcspec]` on unary `Triple` or raw `wp` theorems to opt them into bounded lookup. -/
syntax "pvcstep" ("using" term)? : tactic
@[inherit_doc tacticPvcstepUsing_, tactic_alt tacticPvcstepUsing_]
syntax "pvcstep" "with" term : tactic
@[inherit_doc tacticPvcstepUsing_, tactic_alt tacticPvcstepUsing_]
syntax "pvcstep" "as" "⟨" binderIdent,* "⟩" : tactic
@[inherit_doc tacticPvcstepUsing_, tactic_alt tacticPvcstepUsing_]
syntax "pvcstep" "using" term "as" "⟨" binderIdent,* "⟩" : tactic
@[inherit_doc tacticPvcstepUsing_, tactic_alt tacticPvcstepUsing_]
syntax "pvcstep" "with" term "as" "⟨" binderIdent,* "⟩" : tactic
@[inherit_doc tacticPvcstepUsing_, tactic_alt tacticPvcstepUsing_]
syntax "pvcstep?" : tactic

elab_rules : tactic
  | `(tactic| pvcstep as ⟨ $ids,* ⟩) => do
      let names := binderIdentsToNames ids
      if ← runVCGenStepWithNames names then return
      TacticInternals.Unary.throwVCGenStepError
  | `(tactic| pvcstep using $cut as ⟨ $ids,* ⟩) => do
      let names := binderIdentsToNames ids
      if ← TacticInternals.Unary.runHoareStepRuleUsing cut then
        introAllGoalsNames names
        renameInaccessibleNames names
        return
      TacticInternals.Unary.throwVCGenStepError
  | `(tactic| pvcstep with $thm as ⟨ $ids,* ⟩) => do
      let names := binderIdentsToNames ids
      if ← runVCGenStepWithTheoremNames thm names then return
      TacticInternals.Unary.throwVCGenStepError
  | `(tactic| pvcstep) => do
      if ← TacticInternals.Unary.runVCGenStep then return
      TacticInternals.Unary.throwVCGenStepError
  | `(tactic| pvcstep using $cut) => do
      if ← TacticInternals.Unary.runHoareStepRuleUsing cut then return
      TacticInternals.Unary.throwVCGenStepError
  | `(tactic| pvcstep with $thm) => do
      if ← TacticInternals.Unary.runVCGenStepWithTheorem thm then return
      TacticInternals.Unary.throwVCGenStepError
  | `(tactic| pvcstep?) => do
      let some step ← TacticInternals.Unary.runVCGenPlannedStep?
        | TacticInternals.Unary.throwVCGenStepError
      addTryThisTextSuggestion (← getRef) step.replayText
      logPlannerNotes #[step]

@[inherit_doc tacticPvcstepUsing_, tactic_alt tacticPvcstepUsing_]
syntax "pvcstep" &"rw" : tactic
@[inherit_doc tacticPvcstepUsing_, tactic_alt tacticPvcstepUsing_]
syntax "pvcstep" &"rw" " under " num : tactic
@[inherit_doc tacticPvcstepUsing_, tactic_alt tacticPvcstepUsing_]
syntax "pvcstep" &"rw" &"normalize" : tactic
@[inherit_doc tacticPvcstepUsing_, tactic_alt tacticPvcstepUsing_]
syntax "pvcstep" &"rw" &"congr" : tactic
@[inherit_doc tacticPvcstepUsing_, tactic_alt tacticPvcstepUsing_]
syntax "pvcstep" &"rw" &"congr'" : tactic
@[inherit_doc tacticPvcstepUsing_, tactic_alt tacticPvcstepUsing_]
syntax "pvcstep" &"rw" "as" "⟨" binderIdent,* "⟩" : tactic
@[inherit_doc tacticPvcstepUsing_, tactic_alt tacticPvcstepUsing_]
syntax "pvcstep" &"rw" " under " num "as" "⟨" binderIdent,* "⟩" : tactic
@[inherit_doc tacticPvcstepUsing_, tactic_alt tacticPvcstepUsing_]
syntax "pvcstep" &"rw" &"congr" "as" "⟨" binderIdent,* "⟩" : tactic
@[inherit_doc tacticPvcstepUsing_, tactic_alt tacticPvcstepUsing_]
syntax "pvcstep" &"rw" &"congr'" "as" "⟨" binderIdent,* "⟩" : tactic

elab_rules : tactic
  | `(tactic| pvcstep rw as ⟨ $ids,* ⟩) => do
      let names := binderIdentsToNames ids
      if ← TacticInternals.Unary.runProbEqAction .rewrite then
        introAllGoalsNames names
        renameInaccessibleNames names
        return
      TacticInternals.Unary.throwVCGenStepRwError 0
  | `(tactic| pvcstep rw under $n:num as ⟨ $ids,* ⟩) => do
      let depth := n.getNat
      let names := binderIdentsToNames ids
      if ← TacticInternals.Unary.runProbEqAction (.rewriteUnder depth) then
        introAllGoalsNames names
        renameInaccessibleNames names
        return
      TacticInternals.Unary.throwVCGenStepRwError depth
  | `(tactic| pvcstep rw congr as ⟨ $ids,* ⟩) => do
      let names := binderIdentsToNames ids
      if ← TacticInternals.Unary.runProbEqCongrChainWithNames true names then return
      TacticInternals.Unary.throwVCGenStepRwCongrError true
  | `(tactic| pvcstep rw congr' as ⟨ $ids,* ⟩) => do
      let names := binderIdentsToNames ids
      if ← TacticInternals.Unary.runProbEqCongrChainWithNames false names then return
      TacticInternals.Unary.throwVCGenStepRwCongrError false
  | `(tactic| pvcstep rw) => do
      if ← TacticInternals.Unary.runProbEqAction .rewrite then return
      TacticInternals.Unary.throwVCGenStepRwError 0
  | `(tactic| pvcstep rw under $n:num) => do
      let depth := n.getNat
      if ← TacticInternals.Unary.runProbEqAction (.rewriteUnder depth) then return
      TacticInternals.Unary.throwVCGenStepRwError depth
  | `(tactic| pvcstep rw normalize) => do
      if ← TacticInternals.Unary.runProbEqNormalize then return
      TacticInternals.Unary.throwVCGenStepRwNormalizeError
  | `(tactic| pvcstep rw congr) => do
      if ← TacticInternals.Unary.runProbEqAction .congr then return
      TacticInternals.Unary.throwVCGenStepRwCongrError true
  | `(tactic| pvcstep rw congr') => do
      if ← TacticInternals.Unary.runProbEqAction .congrNoSupport then return
      TacticInternals.Unary.throwVCGenStepRwCongrError false

@[inherit_doc tacticPvcstepUsing_, tactic_alt tacticPvcstepUsing_]
syntax "pvcstep" &"inv" term : tactic
@[inherit_doc tacticPvcstepUsing_, tactic_alt tacticPvcstepUsing_]
syntax "pvcstep" &"inv" term "as" "⟨" binderIdent,* "⟩" : tactic

elab_rules : tactic
  | `(tactic| pvcstep inv $inv as ⟨ $ids,* ⟩) => do
      let names := binderIdentsToNames ids
      if ← TacticInternals.Unary.runLoopInvExplicit inv then
        introAllGoalsNames names
        renameInaccessibleNames names
        return
      throwError
        "pvcstep inv: expected a `Triple` goal about `replicate`, `List.foldlM`, \
        or `List.mapM`."
  | `(tactic| pvcstep inv $inv) => do
      if ← TacticInternals.Unary.runLoopInvExplicit inv then return
      throwError
        "pvcstep inv: expected a `Triple` goal about `replicate`, `List.foldlM`, \
        or `List.mapM`."

/-- `pvcgen` exhaustively decomposes a quantitative `Triple`, raw `wp`, or probability goal
about oracle computations with spec-aware stepping. It is the exhaustive driver of VCVio's
probabilistic VC generator: `pvcstep` takes a single step, and `rvcgen` is the relational
counterpart.

Core's `vcgen` generates verification conditions for `Std.WP` triples from the `@[spec]`
catalogue, and stays available under that name alongside `pvcgen`. `pvcgen` works on the same
core triples, read as expectations (for `OracleComp`, `⦃ pre ⦄ oa ⦃ post ⦄` unfolds to
`pre ≤ wp⟦oa⟧ post`), and adds the probabilistic layer that core does not provide: lowering of
`Pr{…}[…]` goals, bind-swap and congruence on probability equalities, oracle-query and
`simulateQ` rules, support and indicator leaf closure, and lookup in the `@[vcspec]` and
`@[wpStep]` registries. Core's `vcgen` remains the tool for `Prop`-valued triples under a scoped
reading such as `OracleComp.Qualitative`, whose handler specifications are `@[spec]` rules.

Accepts `Triple` goals, raw `wp` goals, lower-bound / exact probability goals, and
`Pr{…}[…] = Pr{…}[…]` equality goals. Probability goals are automatically lowered or
dispatched (swap/congr) before structural decomposition continues.

Enhancements over simple structural decomposition:
- Lowers `Pr{…}[…]` goals into `Triple` or raw `wp` form before decomposition
- After bind decomposition, tries to close spec subgoals from local context
- Falls back to backward WP (`triple_bind_wp`) when no spec is available
- Splits `ite`/`dite` conditionals into branch goals with hypotheses
- Case-splits `match` expressions on their discriminants
- Auto-detects loop invariants from context for `replicate`/`foldlM`/`mapM`
- Keeps decomposing across all open goals after branch splits
- Understands `simulateQ` and `simulateQ ... run'` through the unary WP rules
- Normalizes remaining `wp` terms and indicator arithmetic via simp
- Finishes with bounded local consequence search on closed goals

Typical usage: bring specs into context with `have` or as function parameters, then
call `pvcgen` to automatically decompose and apply them.

Variants:
- `pvcgen using cut` performs one explicit bind step with intermediate postcondition `cut`,
  then continues with exhaustive decomposition on all resulting goals.
- `pvcgen inv I` applies an explicit loop invariant `I` to the first `replicate`/`foldlM`/`mapM`
  goal, then continues with exhaustive decomposition.
- `pvcgen?` runs `pvcgen` and suggests the explicit step script it followed. -/
syntax (name := pvcgenBasic) "pvcgen" : tactic
@[inherit_doc pvcgenBasic, tactic_alt pvcgenBasic]
syntax (name := pvcgenUsing) "pvcgen" "using" term : tactic
@[inherit_doc pvcgenBasic, tactic_alt pvcgenBasic]
syntax (name := pvcgenInv) "pvcgen" &"inv" term : tactic
@[inherit_doc pvcgenBasic, tactic_alt pvcgenBasic]
syntax (name := pvcgenSuggestion) "pvcgen?" : tactic

elab_rules (kind := pvcgenBasic) : tactic
  | `(tactic| pvcgen) => withVCGenRunTiming "pvcgen" do
      discard <| runBoundedPasses "pvcgen" TacticInternals.Unary.runVCGenPass
      withVCGenFinishTiming runVCGenFinish

elab_rules (kind := pvcgenSuggestion) : tactic
  | `(tactic| pvcgen?) => withVCGenRunTiming "pvcgen?" do
      let batches ← runBoundedPassesCollect "pvcgen?" TacticInternals.Unary.runVCGenPassPlanned
      let needsFinish := !(← getGoals).isEmpty
      withVCGenFinishTiming runVCGenFinish
      for batch in batches do
        logPlannerNotes batch
      let mut lines : List String :=
        batches.toList.filterMap renderPassReplayLine
      if needsFinish then
        lines := lines ++ [
          String.intercalate "" [
            "all_goals try simp only [OracleComp.ProgramLogic.wp_pure, ",
            "OracleComp.ProgramLogic.wp_bind, OracleComp.ProgramLogic.wp_query, ",
            "OracleComp.ProgramLogic.wp_ite, OracleComp.ProgramLogic.wp_dite, ",
            "OracleComp.ProgramLogic.wp_map, OracleComp.ProgramLogic.wp_uniformSample, ",
            "OracleComp.ProgramLogic.wp_const, propInd_true, ",
            "propInd_false, propInd_eq_ite, ",
            "ite_true, ite_false, ite_true, ite_false, dite_true, dite_false, ",
            "one_mul, mul_one, zero_mul, mul_zero, zero_add, add_zero, game_rule]",
          ],
          String.intercalate "" [
            "all_goals first | assumption | exact Std.WP.Spec.pure _ | ",
            "exact OracleComp.ProgramLogic.triple_zero _ _ | ",
            "(classical exact OracleComp.ProgramLogic.triple_support _) | ",
            "(exact OracleComp.ProgramLogic.triple_propInd_of_support _ _ (by assumption)) | ",
            "(exact OracleComp.ProgramLogic.triple_prEvent_eq_one _ _ (by assumption)) | ",
            "exact le_refl _ | (repeat intro; simp only [Std.WP.Triple.iff] at *; ",
            "solve_by_elim (maxDepth := 6) [OracleComp.ProgramLogic.wp_mono, le_trans])",
          ]
        ]
      if lines.isEmpty then
        lines := ["pvcgen"]
      addTryThisTextSuggestion (← getRef) <| String.intercalate "\n" lines

elab_rules (kind := pvcgenUsing) : tactic
  | `(tactic| pvcgen using $cut) => withVCGenRunTiming "pvcgen" do
      discard <| TacticInternals.Unary.tryLowerProbGoal
      if ← TacticInternals.Unary.runHoareStepRuleUsing cut then
        discard <| runBoundedPasses "pvcgen" TacticInternals.Unary.runVCGenPass
        withVCGenFinishTiming runVCGenFinish
      else
        TacticInternals.Unary.throwVCGenStepError

elab_rules (kind := pvcgenInv) : tactic
  | `(tactic| pvcgen inv $inv) => withVCGenRunTiming "pvcgen" do
      discard <| TacticInternals.Unary.tryLowerProbGoal
      if ← TacticInternals.Unary.runLoopInvExplicit inv then
        discard <| runBoundedPasses "pvcgen" TacticInternals.Unary.runVCGenPass
        withVCGenFinishTiming runVCGenFinish
      else
        throwError
          "pvcgen inv: expected a `Triple` goal about `replicate`, `List.foldlM`, \
          or `List.mapM`."

/-- `exp_norm` normalizes expectation / indicator arithmetic in the current goal.

Rewrites using linearity of expectation (`wp_add`, `wp_mul_const`), indicator algebra
(`propInd_true`, `propInd_false`, `propInd_and`), and standard WP step rules. -/
macro (name := expNorm) "exp_norm" : tactic =>
  `(tactic| simp only [
    propInd_true, propInd_false,
    propInd_and, propInd_eq_ite,
    propInd_not, propInd_le_one,
    propInd,
    OracleComp.ProgramLogic.wp_add, OracleComp.ProgramLogic.wp_mul_const,
    OracleComp.ProgramLogic.wp_const, OracleComp.ProgramLogic.wp_eq_tsum,
    OracleComp.ProgramLogic.wp_pure, OracleComp.ProgramLogic.wp_bind,
    OracleComp.ProgramLogic.wp_map, OracleComp.ProgramLogic.wp_ite,
    OracleComp.ProgramLogic.wp_dite,
    ite_true, ite_false, ite_true, ite_false, dite_true, dite_false,
    one_mul, mul_one, zero_mul, mul_zero, zero_add, add_zero,
    game_rule])

/-- `by_hoare` transforms a probability goal into a quantitative WP goal. -/
macro (name := byHoare) "by_hoare" : tactic =>
  `(tactic|
    simp only [prEvent_ite, prEvent_dite, evalDist_ite_apply, evalDist_dite_apply,
      OracleComp.ProgramLogic.prEvent_eq_wp_propInd,
      ← propInd_eq_ite])

end OracleComp.ProgramLogic
