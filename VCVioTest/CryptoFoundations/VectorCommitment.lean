/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import VCVio.CryptoFoundations.VectorCommitment.Hiding
public import VCVio.CryptoFoundations.VectorCommitment.PositionBinding

/-!
# Vector commitment security checks

A scheme that commits to nothing is hiding against every adversary. A scheme that commits to the
message in the clear is not: an adversary that reads the commitment has advantage one. A check
that accepts everything is not position binding: two conflicting openings of one commitment win
with probability one. An adversary that makes no oracle queries meets the zero query budget.
-/

public section

open MeasureTheory OracleComp OracleSpec VectorCommitment

namespace VectorCommitmentTest

/-- Commits to the message itself; the opening and check are trivial. -/
def transparent : VectorCommitment Unit Unit Bool (Fin 1 → Bool) Unit Unit 1 where
  commit m := pure (m, ())
  opening _ _ := pure ()
  check _ _ _ := pure true

/-- Commits to nothing; the check accepts everything. -/
def constant : VectorCommitment Unit Unit Bool Unit Unit Unit 1 where
  commit _ := pure ((), ())
  opening _ _ := pure ()
  check _ _ _ := pure true

/-- Chooses two different messages, opens nothing, and reads the commitment. -/
def reader : HidingAdversary Unit Unit Bool (Fin 1 → Bool) Unit 1 where
  State := Unit
  choose := pure (fun _ ↦ false, fun _ ↦ true, ∅, ())
  distinguish _ cm _ := pure (cm 0)

/-! ## Hiding -/

/-- Both worlds of the constant scheme are the same computation. -/
example (adversary : HidingAdversary Unit Unit Bool Unit Unit 1) :
    constant.hidingExperiment adversary true = constant.hidingExperiment adversary false := rfl

/-- The constant scheme gives every adversary advantage zero. -/
example [MeasurableSpace (Unit → Unit)] (D : Measure (Unit → Unit))
    (adversary : HidingAdversary Unit Unit Bool Unit Unit 1) :
    constant.hidingAdvantage D adversary = 0 := by
  simp [hidingAdvantage, show constant.hidingExperiment adversary true =
    constant.hidingExperiment adversary false from rfl]

/-- Against a fixed function, the reader's bit is the world bit. -/
theorem transparent_hidingExperiment (H : Unit → Unit) (b : Bool) :
    simulateQ (fixedOracleImpl H) (transparent.hidingExperiment reader b) = pure b := by
  have agree : PartialVec.restrict (fun _ : Fin 1 ↦ false) ∅ =
      PartialVec.restrict (fun _ ↦ true) ∅ := by
    funext i
    simp [PartialVec.restrict_apply]
  cases b <;> simp [hidingExperiment, transparent, reader, agree]

/-- The transparent scheme gives the reader advantage one. -/
example [MeasurableSpace (Unit → Unit)] (D : Measure (Unit → Unit)) [IsProbabilityMeasure D] :
    transparent.hidingAdvantage D reader = 1 := by
  simp [hidingAdvantage, transparent_hidingExperiment]

/-- The reader makes no oracle queries. -/
example : reader.MakesAtMostQueries 0 := by
  intro cm pf
  simp [reader]

/-! ## Position binding -/

/-- Opens position `0` of one commitment to both `false` and `true`. -/
def forger : PositionBindingAdversary Unit Unit Bool Unit Unit 1 :=
  pure ((), (fun _ ↦ some false, ()), (fun _ ↦ some true, ()))

/-- A check that accepts everything is broken with probability one. -/
example [MeasurableSpace (Unit → Unit)] (D : Measure (Unit → Unit)) [IsProbabilityMeasure D] :
    constant.positionBindingAdvantage D forger = 1 := by
  simp [positionBindingAdvantage, positionBindingExperiment, forger, constant,
    PartialVec.Conflict]

/-- Identical openings never conflict. -/
example (a : PartialVec 1 Bool) : ¬ PartialVec.Conflict a a := PartialVec.not_conflict_self a

end VectorCommitmentTest
