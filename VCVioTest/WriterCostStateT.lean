/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import VCVio.OracleComp.QueryTracking.WriterCost.StateT
import Mathlib.Algebra.FreeMonoid.Basic

/-!
# Ordered costs and returned failure data

The controls retain arbitrary complete handler states and arbitrary initial costs.
List-word costs distinguish chronological accumulation from reversal.
-/

public section

open OracleComp OracleSpec

universe v

namespace WriterCostStateT

/-- An empty body returning None preserves both state fields and the supplied cost. -/
theorem empty_none {σ U X C : Type} [AddMonoid C]
    {m : Type → Type v} [Monad m]
    (weight : Nat → C) (impl : QueryImpl (Nat →ₒ Bool) (StateT (σ × U) m))
    (state : σ) (unrelated : U) (start : C) :
    (simulateQ (impl.extendState (fun q _ _ _ n => n + weight q))
      (pure none : OracleComp (Nat →ₒ Bool) (Option X))).run
        ((state, unrelated), start) = pure (none, ((state, unrelated), start)) := by
  simp

/-- A reached query retains its cost and complete post-state even when the body returns None. -/
theorem reached_none {σ U X C : Type} [AddMonoid C]
    {m : Type → Type v} [Monad m] [LawfulMonad m]
    (weight : Nat → C) (impl : QueryImpl (Nat →ₒ Bool) (StateT (σ × U) m))
    (initial : σ × U) (start : C) (input : Nat) :
    (simulateQ (impl.extendState (fun q _ _ _ n => n + weight q)) (do
      let _ ← liftM ((Nat →ₒ Bool).query input)
      pure (none : Option X))).run (initial, start) =
      (fun output => (none, (output.2, start + weight input))) <$>
        (impl input).run initial := by
  rw [← run_withAddCost_eq_extendState]
  simp [QueryImpl.withAddCost_apply, AddWriterT.runAdd,
    AddWriterT.addTell, WriterT.run_bind, QueryImpl.id', Functor.map_map, Prod.map]

/-- An ordinary error remains returned data, distinct from an aborted Option output. -/
theorem reached_error {σ U ε X C : Type} [AddMonoid C]
    {m : Type → Type v} [Monad m] [LawfulMonad m]
    (weight : Nat → C) (impl : QueryImpl (Nat →ₒ Bool) (StateT (σ × U) m))
    (initial : σ × U) (start : C) (input : Nat) (error : ε) :
    (simulateQ (impl.extendState (fun q _ _ _ n => n + weight q)) (do
      let _ ← liftM ((Nat →ₒ Bool).query input)
      pure (some (Except.error error) : Option (Except ε X)))).run (initial, start) =
      (fun output => (some (Except.error error), (output.2, start + weight input))) <$>
        (impl input).run initial := by
  rw [← run_withAddCost_eq_extendState]
  simp [QueryImpl.withAddCost_apply, AddWriterT.runAdd,
    AddWriterT.addTell, WriterT.run_bind, QueryImpl.id', Functor.map_map, Prod.map]

/-- Two charges follow an arbitrary warm prefix while retaining both replies and full state. -/
theorem ordered_word_cost {σ U : Type}
    {m : Type → Type v} [Monad m] [LawfulMonad m]
    (impl : QueryImpl (Nat →ₒ Bool) (StateT (σ × U) m))
    (initial : σ × U) (warmWord : List Nat) (first second : Nat) :
    (simulateQ (impl.extendState
      (fun q _ _ _ n => n + FreeAddMonoid.of q)) (do
        let a ← liftM ((Nat →ₒ Bool).query first)
        let b ← liftM ((Nat →ₒ Bool).query second)
        pure (a, b))).run (initial, FreeAddMonoid.ofList warmWord) =
      (fun output => (output.1, (output.2,
        FreeAddMonoid.ofList (warmWord ++ [first, second])))) <$>
        (simulateQ impl (do
          let a ← liftM ((Nat →ₒ Bool).query first)
          let b ← liftM ((Nat →ₒ Bool).query second)
          pure (a, b))).run initial := by
  rw [← run_withAddCost_eq_extendState]
  simp [simulateQ_bind, QueryImpl.withAddCost_apply, AddWriterT.runAdd,
    AddWriterT.addTell, WriterT.run_bind, QueryImpl.id', Functor.map_map, Prod.map,
    map_bind, bind_map_left]

/-- The warm word followed by charges one and two differs from their reversal. -/
theorem noncommutative_control :
    FreeAddMonoid.ofList [99, 1, 2] ≠ FreeAddMonoid.ofList [99, 2, 1] := by
  change ([99, 1, 2] : List Nat) ≠ [99, 2, 1]
  decide

/-- An outer failure of the base monad creates no returned state or fabricated cost log. -/
theorem outer_failure {σ C : Type} [AddMonoid C]
    (weight : Nat → C) (initial : σ) (start : C) (input : Nat) :
    let impl : QueryImpl (Nat →ₒ Bool) (StateT σ Option) :=
      fun _ => StateT.mk fun _ => none
    (fun output : (Bool × C) × σ =>
      (output.1.1, (output.2, start + output.1.2))) <$>
        (simulateQ impl (simulateQ ((QueryImpl.id' (Nat →ₒ Bool)).withAddCost weight)
          (liftM ((Nat →ₒ Bool).query input))).runAdd).run initial = none := by
  dsimp only
  rw [run_withAddCost_eq_extendState]
  simp [QueryImpl.extendState_apply]

end WriterCostStateT
