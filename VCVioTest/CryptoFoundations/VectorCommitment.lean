/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import VCVio.CryptoFoundations.VectorCommitment.Hiding
public import VCVio.CryptoFoundations.VectorCommitment.PositionBinding
public import VCVio.CryptoFoundations.VectorCommitment.RomCompleteness
public import VCVio.CryptoFoundations.MerkleTree.Salted.Defs

/-!
# Vector commitment security checks

A scheme that commits to nothing is hiding against every adversary. A scheme that commits to the
message in the clear is not: an adversary that reads the commitment has advantage one. A check
that accepts everything is not position binding: two conflicting openings of one commitment win
with probability one. Simulation-based hiding of the constant scheme gives its two-message hiding
through the generic reduction, for adversaries within any query budget. Adversaries that make no
oracle queries meet the zero query budget. The salted Merkle commitment accepts honest openings
with probability one under the lazily sampled random oracle of the two advantages, and both
advantages can be stated for it.
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
example (adversary : HidingAdversary Unit Unit Bool Unit Unit 1) :
    constant.hidingAdvantage adversary = 0 := by
  rw [hidingAdvantage, show constant.hidingExperiment adversary true =
    constant.hidingExperiment adversary false from rfl, Measure.boolDist_self]

/-- The reader's experiment returns the world bit. -/
theorem transparent_hidingExperiment (b : Bool) :
    transparent.hidingExperiment reader b = pure b := by
  have agree : PartialVec.restrict (fun _ : Fin 1 ↦ false) ∅ =
      PartialVec.restrict (fun _ ↦ true) ∅ := by
    funext i
    simp [PartialVec.restrict_apply]
  cases b <;> simp [hidingExperiment, transparent, reader, agree]

/-- The transparent scheme gives the reader advantage one. -/
example : transparent.hidingAdvantage reader = 1 := by
  simp [hidingAdvantage_eq, transparent_hidingExperiment, ProbCompRuntime.rom_evalDist]

/-- A simulator for the constant scheme, which needs no information about the message. -/
def constantSimulator : HidingSimulator Unit Unit Bool Unit Unit 1 := fun _ _ ↦ pure ((), ())

/-- The constant scheme's real and simulated worlds are the same computation. -/
theorem constant_simulationHidingAdvantage
    (adversary : SimulationHidingAdversary Unit Unit Bool Unit Unit 1) :
    constant.simulationHidingAdvantage constantSimulator adversary = 0 := by
  have h : constant.simulationHidingRealExperiment adversary =
      simulationHidingIdealExperiment constantSimulator adversary := by
    simp [simulationHidingRealExperiment, simulationHidingIdealExperiment, constant,
      constantSimulator]
  rw [simulationHidingAdvantage, h, Measure.boolDist_self]

/-- Simulation-based hiding with error `0` gives two-message hiding with error `0`, here for an
adversary within a budget of `t` oracle queries. -/
example (t : ℕ) (adversary : HidingAdversary Unit Unit Bool Unit Unit 1)
    (hq : adversary.MakesAtMostQueries t) :
    constant.hidingAdvantage adversary = 0 := by
  refine le_antisymm ?_ (zero_le)
  simpa using hidingAdvantage_le_two_mul constant constantSimulator
    (fun b _ ↦ (constant_simulationHidingAdvantage b).le) adversary hq

/-- The reader's world adversaries inherit its zero query budget and its opening size. -/
example :
    (reader.toSimulation true).MakesAtMostQueries 0 ∧ (reader.toSimulation false).OpensExactly 0 :=
  ⟨HidingAdversary.makesAtMostQueries_toSimulation (by intro cm pf; simp [reader]) true,
    HidingAdversary.opensExactly_toSimulation
      (by intro c hc; rw [Set.mem_singleton_iff.mp hc]; rfl) false⟩

/-- The reader makes no oracle queries. -/
example : reader.MakesAtMostQueries 0 := by
  intro cm pf
  simp [reader]

/-! ## Position binding -/

/-- Opens position `0` of one commitment to both `false` and `true`. -/
def forger : PositionBindingAdversary Unit Unit Bool Unit Unit 1 :=
  pure ((), (fun _ ↦ some false, ()), (fun _ ↦ some true, ()))

/-- A check that accepts everything is broken with probability one. -/
example : constant.positionBindingAdvantage forger = 1 := by
  simp [positionBindingAdvantage, positionBindingExperiment, forger, constant,
    PartialVec.Conflict, ProbCompRuntime.rom_evalDist]

/-- The forger makes no oracle queries. -/
example : PositionBindingAdversary.MakesAtMostQueries forger 0 := by
  simp [PositionBindingAdversary.MakesAtMostQueries, forger]

/-- Identical openings never conflict. -/
example (a : PartialVec 1 Bool) : ¬ PartialVec.Conflict a a := PartialVec.not_conflict_self a

/-! ## The salted Merkle commitment -/

section SaltedMerkle

variable {X Y Salt Msg : Type} [DecidableEq X] [DecidableEq Y] [SampleableType Y]
  [SampleableType Salt] [DecidableEq Msg]
  (enc : MerkleTreeHashing.QueryEncoding X Unit Unit (Msg × Salt) Y) (d : ℕ)

/-- The salted Merkle commitment accepts every honest opening with probability one under the
lazily sampled random oracle, the oracle of its binding and hiding advantages. -/
example (msg : Fin (2 ^ d) → Msg) (Q : Finset (Fin (2 ^ d))) :
    (ProbCompRuntime.rom (X →ₒ Y)).evalDist
      ((SaltedMerkle.scheme enc d).toVectorCommitment.completenessExp msg Q) {true} = 1 :=
  (SaltedMerkle.perfectlyComplete enc d).perfectlyCompleteForAll.evalDist_rom_completenessExp msg Q

/-- Position binding can be stated for the salted Merkle commitment. -/
noncomputable example
    (adversary : PositionBindingAdversary X Y Msg Y (SaltedMerkle.Pf Y Salt d) (2 ^ d)) : ENNReal :=
  (SaltedMerkle.scheme enc d).toVectorCommitment.positionBindingAdvantage adversary

/-- Hiding can be stated for the salted Merkle commitment. -/
noncomputable example
    (adversary : HidingAdversary X Y Msg Y (SaltedMerkle.Pf Y Salt d) (2 ^ d)) : ENNReal :=
  (SaltedMerkle.scheme enc d).toVectorCommitment.hidingAdvantage adversary

end SaltedMerkle

end VectorCommitmentTest
