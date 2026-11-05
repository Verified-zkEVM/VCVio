/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import VCVio.OracleComp.SimSemantics.StateT.UntilBad.Bind
public import VCVio.OracleComp.Constructions.SampleableType.Measure
public import VCVio.EvalDist.Instances.OptionT

/-!
# Random continuations retain joint state and bad mass

The finite handlers disagree on the step that raises bad.
A state-dependent continuation samples a Boolean only on the good branch.
Other controls retain normal error data and a counter, and expose the need for a common
lossless continuation and a bound on the entire joint state.
-/

public section

open OracleComp OracleSpec

namespace UntilBadBindTest

/-- A single input with a Boolean answer. -/
abbrev spec := Unit →ₒ Bool

/-- The first handler raises bad and returns false. -/
@[expose] def first : QueryImpl spec (StateT Bool ProbComp) :=
  fun _ => StateT.mk fun _ => pure (false, true)

/-- The second handler remains good and returns true. -/
@[expose] def second : QueryImpl spec (StateT Bool ProbComp) :=
  fun _ => StateT.mk fun _ => pure (true, false)

private theorem dominated :
    QueryImpl.DominatedUntilBad first second id (fun _ => True) (· = true) := by
  intro q s _ _ P
  simp [first, second]

private theorem preserves_bad : QueryImpl.PreservesInv first (· = true) := by
  intro q s _ z hz
  simp only [first, StateT.run_mk, support_pure, Set.mem_singleton_iff] at hz
  subst z
  rfl

/-- An arbitrary random continuation may read both the answer and state. -/
example {γ : Type} (F : Bool × Bool → ProbComp γ) (P : γ → Prop) :
    Pr{let z ← (simulateQ second (liftM (spec.query ()))).run false; let y ← F z}[P y] ≤
      Pr{let z ← (simulateQ first (liftM (spec.query ()))).run false; let y ← F z}[
        P y ∨ z.2 = true] :=
  dominated.prEvent_simulateQ_run_bind_le_map_or_bad
    (fun _ _ _ _ _ => trivial) preserves_bad _ false trivial F P

/-- The same continuation draws only on the good branch and observes the returned answer. -/
@[expose] def after (z : Bool × Bool) : ProbComp Bool :=
  if z.2 then pure false else do
    let b ← $ᵗ Bool
    pure (b || z.1)

/-- The bad branch has no successful event, but its complete bad mass is retained. -/
example :
    Pr{
      let z ← (simulateQ second (liftM (spec.query ()))).run false
      let y ← after z}[y = true] = 1 ∧
    Pr{
      let z ← (simulateQ first (liftM (spec.query ()))).run false
      let y ← after z}[y = true] = 0 ∧
    Pr{
      let z ← (simulateQ first (liftM (spec.query ()))).run false
      let y ← after z}[y = true ∨ z.2 = true] = 1 := by
  simp [first, second, after, prEvent_norm]

/-- A concrete query counter increments for every occurrence. -/
@[expose] def counted : QueryImpl spec (StateT Nat ProbComp) :=
  fun _ => StateT.mk fun n => pure (true, n + 1)

/-- A normal error is data after two completed queries. -/
@[expose] def normalError : OracleComp spec (Except String Bool) := do
  let _ ← liftM (spec.query ())
  let _ ← liftM (spec.query ())
  pure (.error "normal")

/-- Complete normal error data and the nonzero count are retained before the random tail. -/
example :
    (do
      let z ← (simulateQ counted normalError).run 7
      let b ← $ᵗ Bool
      pure (z.1, z.2, b)) =
    (fun b => ((.error "normal" : Except String Bool), 9, b)) <$> ($ᵗ Bool) := by
  simp [normalError, counted, StateT.run_bind]

/-- Result marginals alone cannot justify a state-dependent postkernel. -/
example :
    (Prod.fst <$> (pure ((), false) : ProbComp (Unit × Bool))) =
      Prod.fst <$> (pure ((), true) : ProbComp (Unit × Bool)) ∧
    Pr{let z ← (pure ((), false) : ProbComp (Unit × Bool)); let y ← pure z.2}[y = true] = 0 ∧
    Pr{let z ← (pure ((), true) : ProbComp (Unit × Bool)); let y ← pure z.2}[y = true] = 1 := by
  simp

/-- Different continuations on the same initial value need not satisfy the comparison. -/
example : ¬(Pr{let _ ← (pure () : ProbComp Unit); let y ← pure true}[y = true] ≤
    Pr{let _ ← (pure () : ProbComp Unit); let y ← pure false}[y = true]) := by
  simp

/-- A lossy continuation can erase the bad prefix, so it is outside the public theorem. -/
example :
    let failOnBad : Bool → OptionT ProbComp Bool := fun bad =>
      if bad then failure else pure true
    Pr{let y ← failOnBad false}[y = true] = 1 ∧
    Pr{let y ← failOnBad true}[y = true ∨ True] = 0 := by
  simp [prEvent_norm]

/-- Function-valued states require no finite, countable or measurable-space hypothesis. -/
example {ι α γ : Type} {spec : OracleSpec ι}
    (impl₁ impl₂ : QueryImpl spec (StateT ((Nat → Bool) × Nat) ProbComp))
    (inv bad : ((Nat → Bool) × Nat) → Prop)
    (h : QueryImpl.DominatedUntilBad impl₁ impl₂ id inv bad)
    (hinv : QueryImpl.PreservesInv impl₁ inv) (hbad : QueryImpl.PreservesInv impl₁ bad)
    (oa : OracleComp spec α) (state : (Nat → Bool) × Nat) (hs : inv state)
    (F : α × ((Nat → Bool) × Nat) → ProbComp γ) (P : γ → Prop) :
    Pr{let z ← (simulateQ impl₂ oa).run state; let y ← F z}[P y] ≤
      Pr{let z ← (simulateQ impl₁ oa).run state; let y ← F z}[P y ∨ bad z.2] :=
  h.prEvent_simulateQ_run_bind_le_map_or_bad hinv hbad oa state hs F P

end UntilBadBindTest
