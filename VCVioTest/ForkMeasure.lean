/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import VCVio.CryptoFoundations.ForkMeasure
public import VCVio.CryptoFoundations.SeededFork

/-!
# External canaries for the measure-level forking bounds

These examples deliberately live outside the defining modules. They lock the public hypotheses and
result shapes of the native seeded forking bound and the replay compatibility corollary, so changes
to either cannot silently make them unusable by downstream crypto proofs.
-/

public section

open MeasureTheory OracleSpec ENNReal Finset

namespace VCVioTest.ForkMeasure

/-- Match the canonical discrete-to-measure interpretation used by the compatibility wrappers. -/
noncomputable local instance measureSpecOfProbability
    {ι : Type} {spec : OracleSpec ι}
    [∀ i, MeasurableSpace (spec.Range i)] [IsProbabilitySpec spec] :
    PFunctor.IsMeasureSpec spec.toPFunctor :=
  PFunctor.IsProbabilitySpec.toMeasureSpec spec.toPFunctor

section seeded

variable {ι : Type} [DecidableEq ι] {spec : OracleSpec ι} {α : Type}
  [∀ i, MeasurableSpace (spec.Range i)] [∀ i, DiscreteMeasurableSpace (spec.Range i)]
  [OracleSpec.IsUniformMeasureSpec spec]

/-- The native seeded forking bound remains directly consumable from another module. -/
example (main : OracleComp spec α) (qb : ι → ℕ) (js : List ι) (i : ι)
    (cf : α → Option (Fin (qb i + 1)))
    [∀ j, SampleableType (spec.Range j)] [∀ j, DecidableEq (spec.Range j)]
    [unifSpec ⊂ₒ spec] [unifSpec ˡ⊂ₒ spec] [Fintype (spec.Range i)] :
    ((∑ s, Pr{let x ← main}[cf x = some s]) ^ 2 / ((qb i + 1 : ℕ) : ℝ≥0∞)
        - (∑ s, Pr{let x ← main}[cf x = some s]) /
            ((Fintype.card (spec.Range i) : ℕ) : ℝ≥0∞)) ≤
      Pr{let r ← OracleComp.seededFork main qb js i cf}[r.isSome] :=
  OracleComp.le_prEvent_isSome_seededFork_sq main qb js i cf

end seeded

section replay

variable {ι : Type} {spec : OracleSpec ι} [IsUniformSpec spec] {α : Type}
  [∀ i, MeasurableSpace (spec.Range i)]
  [∀ i, DiscreteMeasurableSpace (spec.Range i)]
  [MeasurableSpace α]

/-- The replay-fork measure wrapper retains its reachability premise and success-event bound. -/
example [DecidableEq ι] [∀ t, DecidableEq (spec.Range t)]
    (main : OracleComp spec α) (qb : ι → ℕ) (i : ι) (cf : α → Option (Fin (qb i + 1)))
    (hreach : OracleComp.PathCfReachable main qb i cf) :
    (let acc : ℝ≥0∞ := ∑ s, Pr[= some s | cf <$> main]
     let h : ℝ≥0∞ := Fintype.card (spec.Range i)
     let q := qb i + 1
     acc * (acc / q - h⁻¹)) ≤
      𝒟[OracleComp.contextFork main qb i cf] {result | result.isSome} :=
  OracleComp.le_evalDist_isSome_contextFork main qb i cf hreach

end replay

end VCVioTest.ForkMeasure
