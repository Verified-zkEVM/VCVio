/-
Copyright (c) 2024 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen
-/
module

public meta import ToMathlib.Control.OptionT
public import ToMathlib.Control.StateT
public import ToMathlib.Control.WriterT
public import VCVio.EvalDist.ProbabilityNotation
public import VCVio.OracleComp.Coercions.SubSpec.Routing
public import VCVio.OracleComp.QueryTracking.QueryLog
public import VCVio.OracleComp.SimSemantics.Append.Core
public import VCVio.OracleComp.SimSemantics.OptionT.Basic
public import VCVio.OracleComp.SimSemantics.QueryImpl.Compose
public import VCVio.OracleComp.SimSemantics.SimulateQ

/-!
# `vcv_norm` : a normalization tactic for VCVio monad goals

When one unfolds the `OracleReduction` security notions (soundness, knowledge soundness, their
adaptive and coin-bearing variants, completeness) to prove a *game-distribution =
experiment-distribution* equality, the goal is dominated by generic monad plumbing over
`OracleComp` / `simulateQ` / `StateT` / `OptionT` / `WriterT` / `loggingOracle` / `liftComp`.
This file packages that plumbing so the user is left only with the genuinely
construction-specific congruence leaves.

## Surface

- `vcv_norm` — the workhorse `simp only` normalizer: pushes `simulateQ` to the leaves through
  every transformer `run`, flattens `addLift` towers, turns `liftComp` over an `addLift` into the
  inner `simulateQ` (including nested sum interfaces), reduces `OptionT`/`StateT`/`WriterT` `run`s
  to canonical form, and *strips `loggingOracle` value-marginals* (via the `loggingStrip` simproc)
  whenever the log is unused.
- `vcv_strip_log` — just the `loggingStrip` simproc, for when only log-stripping is wanted.
- `vcv_congr` — drives the body equality through `bind_congr` / `simulateQ_bind_congr`, closing
  `rfl` leaves and leaving genuine handler-identity goals for the user.
- `vcv` — umbrella: `vcv_norm` then `vcv_congr`.

## The logging strip

`loggingOracle.run_simulateQ_bind_fst : (simulateQ loggingOracle oa).run >>= (fun x => ob x.1)
= oa >>= ob` is `@[simp]`, but it does **not** fire automatically: `?ob x.1` is not a
higher-order *pattern* (the argument `x.1 = Prod.fst x` is not a bound variable), so neither `simp`
nor `rw` can synthesize `?ob`.  The `loggingStrip` simproc synthesizes it by `kabstract`-ing the
`Prod.fst x` occurrences in the continuation body. It *refuses* to strip when the log component
`x.2` is genuinely used, or when the bind's left side is not literally that logged run (a run
mapped over, or one interpreted further).  Because it is a simproc it descends under binders, so
nested logs (the `prover → verifier → extractor` chains) strip at any depth.
-/

public section

open Lean Lean.Meta Lean.Elab.Tactic OracleComp OracleSpec

namespace VCVNorm

universe u v

/-! ## Generic `OptionT` shape facts -/

/-- `OptionT.run` of `Option.getM` is `pure` — the canonical de-abort of an already-resolved
`Option`. -/
theorem optionT_run_getM {m : Type u → Type v} [Monad m] {α : Type u} (o : Option α) :
    (OptionT.run o.getM : m (Option α)) = pure o := by
  cases o <;> rfl

/-- A pure `Option.elim` into `pure none`/`pure (some (g ·))` collapses to `pure (o.map g)`. -/
theorem optionT_elim_pure_map {m : Type u → Type v} [Monad m] {α γ : Type u}
    (g : α → γ) (o : Option α) :
    (o.elim (pure none) (fun s => pure (some (g s))) : m (Option γ)) = pure (o.map g) := by
  cases o <;> rfl

/-! ## Generic `simulateQ` bind congruence -/

/-- Congruence for `simulateQ` over a bind: equate the heads and, pointwise, the simulated tails. -/
theorem simulateQ_bind_congr {ι : Type} {spec : OracleSpec ι} {n : Type → Type v}
    [Monad n] [LawfulMonad n] {impl : QueryImpl spec n} {α β : Type}
    (x y : OracleComp spec α) (f g : α → OracleComp spec β)
    (h1 : x = y) (h2 : ∀ a, simulateQ impl (f a) = simulateQ impl (g a)) :
    simulateQ impl (x >>= f) = simulateQ impl (y >>= g) := by
  subst h1; simp only [simulateQ_bind]; exact bind_congr h2

/-- The `OptionT` `monadLift` (`liftM`) is `OptionT.lift`, allowing `vcv_norm` to reduce
lifted computations using the ordinary `OptionT.run_lift` law. -/
theorem optionT_liftM_eq_lift {m : Type u → Type v} [Monad m] {α : Type u} (comp : m α) :
    (liftM comp : OptionT m α) = OptionT.lift comp := rfl

/-! ## The `loggingStrip` simproc -/

/-- View `e` as a logging bind `(simulateQ loggingOracle oa).run >>= cont` (a monadic `Bind.bind`
whose lhs contains `simulateQ loggingOracle oa`); return `(oa, cont)`. -/
meta def matchLogBind (e : Expr) : MetaM (Option (Expr × Expr)) := do
  unless e.isAppOf ``Bind.bind && e.getAppNumArgs == 6 do return none
  let args := e.getAppArgs
  let lhs := args[4]!
  let cont := args[5]!
  let some sq := lhs.find? (fun s =>
    s.isAppOf ``simulateQ &&
      s.getAppArgs.any (fun a => a.getAppFn.constName? == some ``OracleSpec.loggingOracle)) |
    return none
  let sqArgs := sq.getAppArgs
  return some (sqArgs[sqArgs.size - 1]!, cont)

/-- Build `(rhs, proof : e = rhs)` stripping a `loggingOracle` value-marginal, or `none` if the log
component is actually used (so the strip would be unsound), or if `e` is not definitionally the
left side of `loggingOracle.run_simulateQ_bind_fst` at the located `oa`. -/
meta def mkStripEq (e oa cont : Expr) : MetaM (Option (Expr × Expr)) := do
  lambdaTelescope cont fun xs body => do
    unless xs.size == 1 do return none
    let x := xs[0]!
    let xTy ← whnf (← inferType x)
    let .app (.app prodC pα) pω := xTy | return none
    unless prodC.isAppOf ``Prod do return none
    let fstApp := mkApp3 (mkConst ``Prod.fst [(← getLevel pα), (← getLevel pω)]) pα pω x
    let bodyAbs ← kabstract body fstApp
    if bodyAbs.containsFVar x.fvarId! then return none
    let ob := Expr.lam `a pα bodyAbs BinderInfo.default
    let some proof ← observing? (mkAppM ``loggingOracle.run_simulateQ_bind_fst #[oa, ob]) |
      return none
    let some (_, lhs, rhs) := (← inferType proof).eq? | return none
    unless ← isDefEq e lhs do return none
    return some (rhs, ← mkExpectedTypeHint proof (← mkEq e rhs))

/-- Strip a `loggingOracle` value-marginal whenever the log is unused.  Fires under binders and on
nested logs, since `simp` re-descends into the produced term. -/
simproc_decl loggingStrip (Bind.bind _ _) := fun e => do
  let some (oa, cont) ← matchLogBind e | return .continue
  let some (rhs, proof) ← mkStripEq e oa cont | return .continue
  return .visit { expr := rhs, proof? := proof }

end VCVNorm

/-! ## The tactics -/

open Lean.Parser.Tactic in
/-- Push `simulateQ` to the leaves through every transformer `run`, flatten `addLift`, collapse
`liftComp`-over-`addLift`, reduce `OptionT`/`StateT`/`WriterT` `run`s, and strip unused
`loggingOracle` value-marginals.  Supports a location: `vcv_norm at h`.  For extra lemmas, follow
with an ordinary `simp only [...]`. -/
macro (name := vcvNorm) "vcv_norm" loc:(location)? : tactic =>
    `(tactic| simp only [
        -- simulateQ push-in (NB: simulateQ_spec_query, not simulateQ_query)
        simulateQ_pure, simulateQ_bind, simulateQ_map, simulateQ_spec_query,
        simulateQ_seq, simulateQ_seqLeft, simulateQ_seqRight, simulateQ_ite, simulateQ_id',
        simulateQ_query_bind, simulateQ_list_mapM, simulateQ_list_forM, simulateQ_list_forIn,
        simulateQ_option_elim, simulateQ_optionT_lift, simulateQ_optionT_bind,
        -- handler algebra
        QueryImpl.simulateQ_compose, QueryImpl.addLift_def,
        QueryImpl.liftTarget_self, QueryImpl.liftTarget_apply,
        QueryImpl.simulateQ_add_liftComp_left, QueryImpl.simulateQ_add_liftComp_right,
        OracleComp.simulateQ_add_liftComp_sum_left, OracleComp.simulateQ_add_add_liftComp_left,
        OracleComp.simulateQ_swapRight, OracleComp.simulateQ_insertMiddle,
        OracleComp.simulateQ_mergeRight,
        -- liftComp / monadLift
        OracleComp.liftComp_pure, OracleComp.liftComp_bind, OracleComp.liftComp_map,
        OracleComp.liftComp_self, monadLift_eq_self,
        -- OptionT run-level normal form
        OptionT.run_bind, OptionT.run_pure, OptionT.run_map, OptionT.run_mk,
        OptionT.run_monadLift, VCVNorm.optionT_liftM_eq_lift, OptionT.run_lift,
        Option.elimM, Option.elim_some,
        VCVNorm.optionT_run_getM, VCVNorm.optionT_elim_pure_map,
        -- StateT / WriterT run' normal form
        StateT.run'_map', StateT.run'_bind', StateT.run'_pure',
        StateT.run_bind, StateT.run_pure, WriterT.run_map',
        -- generic monad glue
        bind_assoc, pure_bind, bind_map_left, map_bind, map_pure, Option.map_map, Function.comp_def,
        -- logging value-marginal strip
        VCVNorm.loggingStrip] $(loc)?)

open Lean.Parser.Tactic in
/-- Strip all unused `loggingOracle` value-marginals reachable in the goal. -/
macro "vcv_strip_log" loc:(location)? : tactic =>
  `(tactic| simp only [VCVNorm.loggingStrip] $(loc)?)

/-- Drive a `simulateQ … = simulateQ …` body equality through `bind_congr` /
`simulateQ_bind_congr`, closing `rfl` leaves and leaving genuine handler-identity goals. -/
macro "vcv_congr" : tactic =>
  `(tactic|
    (repeat' first
      | rfl
      | refine VCVNorm.simulateQ_bind_congr _ _ _ _ rfl (fun a => ?_)
      | refine bind_congr (fun a => ?_)))

/-- Umbrella: normalize, then drive congruence. -/
macro "vcv" : tactic => `(tactic| (vcv_norm; vcv_congr))
