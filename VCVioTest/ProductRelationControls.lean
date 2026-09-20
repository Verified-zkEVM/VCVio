/-
Copyright (c) 2026 Elias Judin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elias Judin
-/

module

public import VCVio.OracleComp.Constructions.SampleableType.NativeMeasure

/-!
# Independent obligations in product extraction

Two finite operational controls distinguish component soundness from refinement into the
target relation. Digests in this model are the witness pairs themselves; their decoder is
the identity, so binding is perfect and the extractor is fixed independently of the prover.
Even this stronger binding condition does not supply either missing logical obligation.

These are countermodels, not a composition theorem for shared-oracle adaptive provers.
They isolate the two missing-premise controls discussed in leanth PR 16,
`Leanth/LeanVM/Aggregation.lean`, revision `23929f8c922cd4461ab22dbfaa6520f3ad23a3b2`.
-/

namespace VCVioTest.ProductRelationControls

open OracleComp MeasureTheory ProbabilityTheory

public section

/-- An injective digest: the complete pair. -/
def digest (w : Bool × Bool) : Bool × Bool := w

/-- One fixed extractor for every computation in the controls. -/
def extract (d : Bool × Bool) : Bool × Bool := d

/-- Binding is exact, without a collision or probabilistic assumption. -/
theorem digest_injective : Function.Injective digest := fun _ _ h ↦ h

/-- The extractor reads precisely the uniquely bound witness. -/
theorem extract_digest (w : Bool × Bool) : extract (digest w) = w := by
  simp only [extract, digest]

/-- A random joint execution whose two individually valid components coincide. -/
def sameBit : ProbComp (Bool × Bool) := (fun b ↦ digest (b, b)) <$> uniformSample Bool

/-- Component relations can both hold with probability one while a stronger target relation
fails with probability one, even with a fixed extractor and perfect binding. -/
theorem missing_refinement_control :
    𝒟[sameBit] {d | (fun _ : Bool ↦ True) (extract d).1 ∧
      (fun _ : Bool ↦ True) (extract d).2} = 1 ∧
    𝒟[sameBit] {d | (extract d).1 ≠ (extract d).2} = 0 := by
  constructor <;>
    rw [sameBit, evalDist_map_of_discrete,
      Measure.map_apply (measurable_of_countable _) MeasurableSet.of_discrete] <;>
    simp [-Bool.univ_eq, digest, extract]

/-- A target relation obtained from both component relations. -/
def Target (w : Bool × Bool) : Prop := w.1 = true ∧ w.2 = true

/-- Correct component witnesses refine the target relation. -/
theorem relation_refinement (x y : Bool) (hx : x = true) (hy : y = true) :
    Target (x, y) := ⟨hx, hy⟩

/-- A bound pair with one invalid component. -/
def invalidFirst : ProbComp (Bool × Bool) :=
  (fun b ↦ digest (false, b)) <$> uniformSample Bool

/-- Relation refinement and perfect binding do not make an unsound component sound. -/
theorem missing_component_soundness_control :
    𝒟[invalidFirst] {d | Target (extract d)} = 0 ∧
    𝒟[invalidFirst] {d | (extract d).1 ≠ true} = 1 := by
  constructor <;>
    rw [invalidFirst, evalDist_map_of_discrete,
      Measure.map_apply (measurable_of_countable _) MeasurableSet.of_discrete] <;>
    simp [-Bool.univ_eq, Target, digest, extract]

end
end VCVioTest.ProductRelationControls
