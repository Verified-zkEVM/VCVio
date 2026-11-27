/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: VCVio Contributors
-/

module

public import VCVio.OracleComp.QueryTracking.RandomOracle.ExpectedHit
import VCVio.OracleComp.Constructions.SampleableType.Measure

/-!
# Charging a public reply after a hidden coin

The first call returns a constant while a hidden coin sets the next call’s eligibility.
The second kind of call exposes a fresh answer.
-/

public section

namespace VCVioTest.ExpectedMarkedHit

open OracleComp OracleSpec
open scoped ENNReal

/-- A hidden draw and a public draw, each returning a Boolean. -/
abbrev Q := (Bool →ₒ Bool)
/-- The hidden bit and the number of marked public draws. -/
abbrev Store := Bool × Nat

/-- The public draw pays one exactly when the prior hidden coin enables it. -/
def marked (t : Q.Domain) (s : Store) : Bool := t && s.1

/-- A hidden or public Boolean draw. -/
noncomputable def impl : QueryImpl Q (StateT Store ProbComp)
  | false => StateT.mk fun s => (fun b => (false, b, s.2)) <$> ($ᵗ Bool)
  | true => StateT.mk fun s => (fun b => (b, s.1, s.2 + if s.1 then 1 else 0)) <$> ($ᵗ Bool)

/-- Even the hidden step with a constant reply is allowed to change the state at random. -/
theorem expected_hit {α : Type} (caller : OracleComp Q α) :
    Pr{let z ← (simulateQ (impl.extendState
      (MarkedHit.update marked (fun _ _ answer => answer))) caller).run ((false, 0), false)}[
        z.2.2 = true] ≤
      (∑' z, Pr{let u ← (simulateQ impl caller).run (false, 0)}[u = z] * z.2.2) * (2 : ℝ≥0∞)⁻¹ := by
  apply MarkedHit.prEvent_le_expected impl Prod.snd marked (fun _ _ answer => answer)
  · rintro (no | yes) s z hz <;> simp only [impl, StateT.run_mk, support_map] at hz <;>
      obtain ⟨b, _, rfl⟩ := hz <;> simp [marked]
  · rintro (no | yes) s active
    · simp [marked] at active
    · change Pr{let z ← (fun b => (b, s.1, s.2 + if s.1 then 1 else 0)) <$> ($ᵗ Bool)}[
        z.1 = true] ≤ _
      rw [prEvent_map]
      exact le_of_eq (by simp [-SampleableType.prEvent_uniformSample,
        SampleableType.prEvent_uniformSample_eq_singleton_natCard, Nat.card_eq_fintype_card])

end VCVioTest.ExpectedMarkedHit
