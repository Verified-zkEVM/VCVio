/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.ProgramLogic.Library.T2.Caching
public import VCVio.ProgramLogic.Library.T2.Combinators
public import VCVio.ProgramLogic.Unary.WP.NecessarySpecs

/-!
# Tests for the handler-combinator specifications

Core `vcgen` with the rules of `VCVio.ProgramLogic.Library.T2.Combinators`, composed with the
caching rules: sum handlers, bad-flag lifts and updates, auxiliary state, and the inherited frames
of opaque runs.
-/

public section

namespace VCVioTest.ProgramLogic.Library.T2Combinators

open OracleSpec OracleComp OracleComp.ProgramLogic Std.WP

open scoped OracleComp.Necessary

set_option experimental.vcgen true

variable {ι₁ ι₂ : Type} [DecidableEq ι₁] [DecidableEq ι₂] {spec₁ : OracleSpec.{0, 0} ι₁}
  {spec₂ : OracleSpec.{0, 0} ι₂}

/-- A sum of two caching handlers dispatches each query to its summand. -/
example (so₁ : QueryImpl spec₁ (OracleComp spec₁)) (t : spec₁.Domain) (t' : spec₂.Domain)
    (impl₂ : QueryImpl spec₂ (StateT spec₁.QueryCache (OracleComp spec₁)))
    (h₂ : ∀ t', ⦃ fun _ => True ⦄ impl₂ t' ⦃ fun _ _ => True ⦄) :
    ⦃ fun _ => True ⦄
      (do
        let a ← (so₁.withCaching + impl₂) (.inl t)
        let _ ← (so₁.withCaching + impl₂) (.inr t')
        return a)
    ⦃ fun _ _ => True ⦄ := by
  vcgen [h₂]

/-- A bad-flag lift runs the caching handler on the first component and keeps the flag. -/
example (t : spec₁.Domain) (b : Bool) :
    ⦃ fun s => s.2 = b ⦄
      (do
        let x ← (spec₁.cachingOracle).withBadFlag t
        let y ← (spec₁.cachingOracle).withBadFlag t
        return (x, y))
    ⦃ fun p s => p.1 = p.2 ∧ s.2 = b ⦄ := by
  vcgen
  grind

/-- A bad-flag update raises the flag exactly when the predicate fires. -/
example (t : spec₁.Domain) (f : (t : spec₁.Domain) → spec₁.QueryCache → spec₁.Range t → Bool)
    (hf : ∀ c u, f t c u = true) :
    ⦃ fun s => s.2 = false ⦄ (spec₁.cachingOracle).withBadUpdate f t ⦃ fun _ s => s.2 = true ⦄ := by
  vcgen
  simp_all

/-- An opaque run of a bad-flag update never lowers the flag. -/
example {α : Type} (oa : OracleComp spec₁ α)
    (f : (t : spec₁.Domain) → spec₁.QueryCache → spec₁.Range t → Bool) :
    ⦃ fun s => s.2 = true ⦄ (simulateQ ((spec₁.cachingOracle).withBadUpdate f) oa)
      ⦃ fun _ s => s.2 = true ⦄ := by
  vcgen
  grind

/-- An opaque run of a sum of a bad-flag lift and a bad-flag update never lowers the flag: the sum
inherits the frame. -/
example {α : Type} (oa : OracleComp (spec₁ + spec₂) α)
    (impl₂ : QueryImpl spec₂ (StateT spec₁.QueryCache (OracleComp spec₁)))
    (f : (t : spec₂.Domain) → spec₁.QueryCache → spec₂.Range t → Bool) :
    ⦃ fun s => s.2 = true ⦄
      (simulateQ ((spec₁.cachingOracle).withBadFlag + impl₂.withBadUpdate f) oa)
    ⦃ fun _ s => s.2 = true ⦄ := by
  vcgen
  grind

/-- An auxiliary counter extends a caching handler: it counts the queries. -/
example (t : spec₁.Domain) :
    ⦃ fun s => s.2 = 0 ⦄
      (do
        let _ ← QueryImpl.extendState (spec₁.cachingOracle) (fun _ _ _ _ n => n + 1) t
        QueryImpl.extendState (spec₁.cachingOracle) (fun _ _ _ _ n => n + 1) t)
    ⦃ fun v s => s.2 = 2 ∧ s.1 t = some v ⦄ := by
  vcgen
  grind

/-- A stateless handler lifted into `StateT` keeps the state. -/
example (so : QueryImpl spec₁ (OracleComp spec₁)) (t : spec₁.Domain) (n : ℕ) :
    ⦃ fun s => s = n ⦄ so.liftTarget (StateT ℕ (OracleComp spec₁)) t ⦃ fun _ s => s = n ⦄ := by
  vcgen [OracleComp.Necessary.Spec.ofSupport (so t)]

end VCVioTest.ProgramLogic.Library.T2Combinators
