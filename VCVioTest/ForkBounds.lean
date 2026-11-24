/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import VCVio.CryptoFoundations.ReplayFork
public import VCVio.CryptoFoundations.SeededFork

/-!
# External canaries for the forking bounds

These examples deliberately live outside the defining modules. They lock the public hypotheses and
result shapes of the seeded and replay forking bounds, so changes to either cannot silently make
them unusable by downstream crypto proofs.
-/

public section

open MeasureTheory OracleSpec ENNReal Finset

namespace VCVioTest.ForkBounds

section seeded

variable {ι : Type} [DecidableEq ι] {spec : OracleSpec ι} {α : Type}
  [OracleSpec.UniformAnswerMeasure spec]

/-- The seeded forking bound remains directly consumable from another module. -/
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

variable {ι : Type} [DecidableEq ι] {spec : OracleSpec ι} {α : Type}
  [OracleSpec.UniformAnswerMeasure spec]

/-- The replay forking bound retains its reachability premise and success-event shape. -/
example [∀ t, DecidableEq (spec.Range t)]
    (main : OracleComp spec α) (qb : ι → ℕ) (i : ι) [Fintype (spec.Range i)]
    (cf : α → Option (Fin (qb i + 1)))
    (hreach : OracleComp.PathCfReachable main qb i cf) :
    (let acc : ℝ≥0∞ := ∑ s, Pr{let x ← main}[cf x = some s]
     let h : ℝ≥0∞ := Fintype.card (spec.Range i)
     let q := qb i + 1
     acc * (acc / q - h⁻¹)) ≤
      Pr{let r ← OracleComp.contextFork main qb i cf}[r.isSome] :=
  OracleComp.le_prEvent_isSome_contextFork main qb i cf hreach

end replay

section replayUniformAt

/-- Answer measures on `Bool →ₒ Bool`: query `true` is a fair coin and query `false` always
answers `true`. -/
@[reducible]
noncomputable def coinOrTrue : AnswerMeasure (Bool →ₒ Bool) :=
  @PFunctor.AnswerMeasure.mk (Bool →ₒ Bool).toPFunctor (fun _ ↦ ⊤)
    (fun
      | true => @ProbabilityTheory.uniformOn Bool ⊤ Set.univ
      | false => @Measure.dirac Bool ⊤ true)
    (fun
      | true => inferInstanceAs (IsProbabilityMeasure (ProbabilityTheory.uniformOn Set.univ))
      | false => inferInstanceAs (IsProbabilityMeasure (Measure.dirac true)))

attribute [local instance] coinOrTrue

local instance : AnswerMeasure.IsUniformAt (Bool →ₒ Bool) true := ⟨rfl⟩

/-- The answer measure of query `false` is not uniform. -/
example : ¬ AnswerMeasure.IsUniformAt (Bool →ₒ Bool) false := fun h => by
  have h' := congrArg (· {false}) h.toMeasure_eq_uniformOn
  change Measure.dirac true {false} = ProbabilityTheory.uniformOn Set.univ {false} at h'
  rw [ProbabilityTheory.uniformOn_univ] at h'
  simp at h'
  exact ENNReal.inv_ne_zero.2 (by simp) h'.symm

/-- The replay forking bound at the uniform query of a specification whose answer measure is
not uniform at every query. -/
example {α : Type} (main : OracleComp (Bool →ₒ Bool) α) (qb : Bool → ℕ)
    (cf : α → Option (Fin (qb true + 1)))
    (hreach : OracleComp.PathCfReachable main qb true cf) :
    (let acc : ℝ≥0∞ := ∑ s, Pr{let x ← main}[cf x = some s]
     let h : ℝ≥0∞ := Fintype.card Bool
     let q := qb true + 1
     acc * (acc / q - h⁻¹)) ≤
      Pr{let r ← OracleComp.contextFork main qb true cf}[r.isSome] :=
  OracleComp.le_prEvent_isSome_contextFork main qb true cf hreach

end replayUniformAt

end VCVioTest.ForkBounds
