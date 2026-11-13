/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import VCVio.OracleComp.QueryTracking.WriterCost
public import VCVio.OracleComp.SimSemantics.StateT.StateProjection
import PolyFun.Control.Monad.Hom.Writer

/-!
# Joint writer costs and passive state accumulation

Both observations retain the same returned value and complete underlying handler state.
The supplied initial cost precedes every emitted charge, without commuting addition.
-/

public section

open OracleSpec

universe v

namespace OracleComp

/-- Accumulating a writer's cost in passive state keeps the entire joint endpoint.

The returned type may contain an ordinary error or Option.none.
A failure of the base monad remains the same failure on both sides.
-/
theorem run_withAddCost_eq_extendState
    {ι α σ C : Type} {spec : OracleSpec.{0, 0} ι}
    {m : Type → Type v} [Monad m] [LawfulMonad m] [AddMonoid C]
    (weight : spec.Domain → C) (body : OracleComp spec α)
    (impl : QueryImpl spec (StateT σ m)) (initial : σ) (start : C) :
    (fun z : (α × C) × σ => (z.1.1, (z.2, start + z.1.2))) <$>
      (simulateQ impl
        (simulateQ ((QueryImpl.id' spec).withAddCost weight) body).runAdd).run initial =
      (simulateQ
        (impl.extendState (fun input _before _reply _after counter => counter + weight input))
        body).run (initial, start) := by
  -- Put the initial cost before the computed writer cost, keeping the full endpoint.
  let appendCost : WriterT (Multiplicative C) (StateT σ m) →ᵐ StateT (σ × C) m := {
    toFun {_β} action := StateT.mk fun initial =>
      (fun output => (output.1.1,
        (output.2, initial.2 + Multiplicative.toAdd output.1.2))) <$>
          action.run.run initial.1
    toFun_pure' value := by
      apply StateT.ext
      rintro ⟨state, counter⟩
      simp [WriterT.run_pure, StateT.run_pure]
    toFun_bind' action next := by
      apply StateT.ext
      rintro ⟨state, counter⟩
      change
        (fun output : (_ × Multiplicative C) × σ =>
          (output.1.1, (output.2, counter + Multiplicative.toAdd output.1.2))) <$>
            (action >>= next).run.run state = (do
          let first ← (fun output : (_ × Multiplicative C) × σ =>
            (output.1.1, (output.2, counter + Multiplicative.toAdd output.1.2))) <$>
              action.run.run state
          (fun output : (_ × Multiplicative C) × σ =>
            (output.1.1, (output.2, first.2.2 + Multiplicative.toAdd output.1.2))) <$>
              (next first.1).run.run first.2.1)
      simp only [WriterT.run_bind, StateT.run_bind, StateT.run_map,
        map_bind, bind_map_left, Functor.map_map]
      apply bind_congr
      rintro ⟨⟨value, cost⟩, nextState⟩
      congr 1
      funext output
      simp [add_assoc] }
  let accumulated : AddWriterT C (OracleComp spec) →ᵐ StateT (σ × C) m :=
    appendCost ∘ᵐ WriterT.mapHom (ω := Multiplicative C) (simulateQ' impl)
  -- Existing free-fold naturality lifts the querywise equation without a new induction.
  have natural := PFunctor.FreeM.liftM_natural
    ((QueryImpl.id' spec).withAddCost weight) accumulated body
  change accumulated (simulateQ ((QueryImpl.id' spec).withAddCost weight) body) =
    simulateQ (fun input => accumulated
      (((QueryImpl.id' spec).withAddCost weight) input)) body at natural
  have querywise :
      (fun input => accumulated (((QueryImpl.id' spec).withAddCost weight) input)) =
        impl.extendState (fun input _before _reply _after counter => counter + weight input) := by
    funext input
    apply StateT.ext
    rintro ⟨state, counter⟩
    change (fun output : (spec.Range input × Multiplicative C) × σ =>
      (output.1.1, (output.2, counter + Multiplicative.toAdd output.1.2))) <$>
        (simulateQ impl (((QueryImpl.id' spec).withAddCost weight input).run)).run state = _
    simp [QueryImpl.withAddCost_apply, AddWriterT.addTell, WriterT.run_bind,
      QueryImpl.id', QueryImpl.extendState_apply, Functor.map_map]
  rw [querywise] at natural
  have atState := congrArg (fun action : StateT (σ × C) m α => action.run (initial, start)) natural
  change (fun output : (α × Multiplicative C) × σ =>
    (output.1.1, (output.2, start + Multiplicative.toAdd output.1.2))) <$>
      (simulateQ impl (simulateQ ((QueryImpl.id' spec).withAddCost weight) body).run).run
        initial = _ at atState
  simpa only [AddWriterT.runAdd, simulateQ_map, StateT.run_map, Functor.map_map,
    Prod.map, id_eq] using atState

end OracleComp
