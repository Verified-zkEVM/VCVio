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
message in the clear is not: an adversary that reads the commitment has advantage one. A check that
accepts everything is not position binding: two conflicting openings of one commitment win with
probability one. A check that compares the claimed values with a commitment in the clear is position
binding with advantage zero. Simulation-based hiding of the constant scheme gives its two-message
hiding through the adversaries playing the two worlds, and simulation bounds on those adversaries
give twice the bound in general. The constant scheme satisfies `IsSimulationHiding` with error zero
by a simulator that makes no oracle queries, and hence `TwoMessageHiding` with error zero. The
scheme that commits in the clear satisfies `SimulationHiding` only at error at least `1 / 2`, even
against adversaries that make no oracle queries and open no positions. Adversaries that make no
oracle queries meet the zero query budget, and the adversaries playing the two worlds inherit it.
The salted Merkle commitment accepts honest openings with probability one under the lazily sampled
random oracle of the two advantages, and both advantages can be stated for it.
-/

public section

open OracleComp OracleSpec VectorCommitment

namespace VectorCommitmentTest

/-- Commits to the message itself; the opening is trivial and the check accepts exactly the
claimed values that agree with the commitment. -/
def transparent : VectorCommitment Unit Unit Bool (Fin 1 → Bool) Unit Unit 1 where
  commit m := pure (m, ())
  opening _ _ := pure ()
  check cm ans _ := pure (decide (PartialVec.Agrees (fun i ↦ some (cm i)) ans))

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
  rw [hidingAdvantage_eq, show constant.hidingExperiment adversary true =
    constant.hidingExperiment adversary false from rfl, ENNReal.absDiff_self]

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
  rw [simulationHidingAdvantage_eq, h, ENNReal.absDiff_self]

/-- Simulation-based hiding with error `0` gives two-message hiding with error `0`. -/
example (adversary : HidingAdversary Unit Unit Bool Unit Unit 1) :
    constant.hidingAdvantage adversary = 0 := by
  refine le_antisymm ?_ (zero_le)
  simpa [constant_simulationHidingAdvantage] using
    hidingAdvantage_le_simulationHidingAdvantage constant constantSimulator adversary

/-- A simulation bound `ε` for the adversaries playing the two worlds gives two-message advantage
at most `2 ε`. -/
example {X Y Msg Cm Td Pf : Type} {ℓ : ℕ} [DecidableEq X] [SampleableType Y] [DecidableEq Msg]
    (vc : VectorCommitment X Y Msg Cm Td Pf ℓ) (simulator : HidingSimulator X Y Msg Cm Pf ℓ)
    (adversary : HidingAdversary X Y Msg Cm Pf ℓ) {ε : ENNReal}
    (h : ∀ b, vc.simulationHidingAdvantage simulator (adversary.toSimulation b) ≤ ε) :
    vc.hidingAdvantage adversary ≤ 2 * ε :=
  (hidingAdvantage_le_simulationHidingAdvantage vc simulator adversary).trans
    ((add_le_add (h true) (h false)).trans_eq (two_mul ε).symm)

/-- The constant simulator makes no oracle queries. -/
theorem constantSimulator_makesAtMostQueries_zero : constantSimulator.MakesAtMostQueries 0 := by
  intro Q ans
  simp [constantSimulator]

/-- The constant scheme is simulation hiding with error `0` for every query budget and opening
size, by a simulator that makes no oracle queries. -/
theorem constant_isSimulationHiding (t q : ℕ) : constant.IsSimulationHiding 0 t q 0 :=
  ⟨constantSimulator, constantSimulator_makesAtMostQueries_zero,
    fun adversary _ _ ↦ (constant_simulationHidingAdvantage adversary).le⟩

/-- The constant scheme is two-message hiding with error `0`. -/
example (t q : ℕ) : constant.TwoMessageHiding t q 0 := by
  simpa using (constant_isSimulationHiding t q).twoMessageHiding

/-- Chooses the message that is `c` everywhere, opens nothing, and checks whether the commitment
reads `c`. -/
def constantReader (c : Bool) : SimulationHidingAdversary Unit Unit Bool (Fin 1 → Bool) Unit 1 where
  State := Unit
  choose := pure (fun _ ↦ c, ∅, ())
  distinguish _ cm _ := pure (cm 0 == c)

/-- The constant readers make no oracle queries. -/
theorem constantReader_makesAtMostQueries_zero (c : Bool) :
    (constantReader c).MakesAtMostQueries 0 := by
  intro cm pf
  simp [constantReader]

/-- The constant readers open no positions. -/
theorem constantReader_opensExactly_zero (c : Bool) : (constantReader c).OpensExactly 0 := by
  intro x hx
  rw [Set.mem_singleton_iff.mp hx]
  rfl

/-- Against the transparent scheme, the simulation-hiding advantage of the constant reader for `c`
plus the probability that the simulator's commitment on an empty opening reads `c` is at least
one. -/
theorem one_le_transparent_simulationHidingAdvantage_constantReader
    (simulator : HidingSimulator Unit Unit Bool (Fin 1 → Bool) Unit 1) (c : Bool) :
    1 ≤ transparent.simulationHidingAdvantage simulator (constantReader c) +
      (ProbCompRuntime.rom (Unit →ₒ Unit)).evalDist
        ((fun x ↦ x.1 0) <$> simulator ∅ (fun _ ↦ none)) {c} := by
  have hreal : transparent.simulationHidingRealExperiment (constantReader c) = pure true := by
    simp [simulationHidingRealExperiment, transparent, constantReader]
  have hideal : simulationHidingIdealExperiment simulator (constantReader c) =
      (fun b ↦ b == c) <$> ((fun x ↦ x.1 0) <$> simulator ∅ (fun _ ↦ none)) := by
    have hres : PartialVec.restrict (fun _ : Fin 1 ↦ c) ∅ = fun _ ↦ none := by
      funext i
      simp
    simp [simulationHidingIdealExperiment, constantReader, hres]
  rw [simulationHidingAdvantage_eq, hreal, hideal,
    ProbCompRuntime.evalDist_map _ _ (by fun_prop),
    MeasureTheory.Measure.map_apply (by fun_prop) (measurableSet_singleton true)]
  have hpre : (fun b : Bool ↦ b == c) ⁻¹' {true} = {c} := by
    ext b
    simp
  have hone : (ProbCompRuntime.rom (Unit →ₒ Unit)).evalDist (pure true) {true} = 1 := by
    simp [ProbCompRuntime.rom_evalDist]
  rw [hpre, hone, ENNReal.absDiff]
  exact le_tsub_add.trans (add_le_add le_self_add le_rfl)

/-- The transparent scheme is not simulation hiding below error `1 / 2`, even against adversaries
that make no oracle queries and open no positions: the simulator sees nothing of the message, so
its commitment reads one of the two constant messages with probability at most `1 / 2`. -/
theorem one_half_le_of_transparent_simulationHiding
    (simulator : HidingSimulator Unit Unit Bool (Fin 1 → Bool) Unit 1) {ε : ENNReal}
    (h : transparent.SimulationHiding simulator 0 0 ε) : 1 / 2 ≤ ε := by
  set μ := (ProbCompRuntime.rom (Unit →ₒ Unit)).evalDist
    ((fun x ↦ x.1 0) <$> simulator ∅ (fun _ ↦ none))
  have hle (c : Bool) : 1 ≤ ε + μ {c} :=
    (one_le_transparent_simulationHidingAdvantage_constantReader simulator c).trans
      (add_le_add (h _ (constantReader_makesAtMostQueries_zero c)
        (constantReader_opensExactly_zero c)) le_rfl)
  have hsum : μ {false} + μ {true} ≤ 1 := by
    rw [← MeasureTheory.measure_union (Set.disjoint_singleton.mpr (by decide))
      (measurableSet_singleton true)]
    exact (MeasureTheory.measure_mono (Set.subset_univ _)).trans
      (ProbCompRuntime.evalDist_apply_univ_le_one _ _)
  have h2 : 1 + 1 ≤ ε * 2 + 1 := calc
    1 + 1 ≤ (ε + μ {false}) + (ε + μ {true}) := add_le_add (hle false) (hle true)
    _ = ε * 2 + (μ {false} + μ {true}) := by ring
    _ ≤ ε * 2 + 1 := add_le_add le_rfl hsum
  exact ENNReal.div_le_of_le_mul ((ENNReal.add_le_add_iff_right ENNReal.one_ne_top).mp h2)

/-- The reader makes no oracle queries. -/
theorem reader_makesAtMostQueries_zero : reader.MakesAtMostQueries 0 := by
  intro cm pf
  simp [reader]

/-- The reader's world adversaries inherit its zero query budget. -/
example (b : Bool) : (reader.toSimulation b).MakesAtMostQueries 0 :=
  HidingAdversary.makesAtMostQueries_toSimulation reader_makesAtMostQueries_zero b

/-- The reader's world adversaries inherit its opening size. -/
example (b : Bool) : (reader.toSimulation b).OpensExactly 0 :=
  HidingAdversary.opensExactly_toSimulation
    (by intro c hc; rw [Set.mem_singleton_iff.mp hc]; rfl) b

/-! ## Position binding -/

/-- Opens position `0` of one commitment to both `false` and `true`. -/
def forger : PositionBindingAdversary Unit Unit Bool Unit Unit 1 :=
  pure ((), (fun _ ↦ some false, ()), (fun _ ↦ some true, ()))

/-- A check that accepts everything is broken with probability one. -/
example : constant.positionBindingAdvantage forger = 1 := by
  simp [positionBindingAdvantage_eq, positionBindingExperiment, forger, constant,
    PartialVec.Conflict, ProbCompRuntime.rom_evalDist]

/-- The forger makes no oracle queries. -/
example : forger.MakesAtMostQueries 0 := by
  simp [PositionBindingAdversary.MakesAtMostQueries, forger]

/-- A check that compares the claimed values with the commitment is never broken: two conflicting
openings cannot both agree with one commitment. -/
example (adversary : PositionBindingAdversary Unit Unit Bool (Fin 1 → Bool) Unit 1) :
    transparent.positionBindingAdvantage adversary = 0 := by
  have h : transparent.positionBindingExperiment adversary = (fun _ ↦ false) <$> adversary := by
    rw [positionBindingExperiment, map_eq_bind_pure_comp]
    congr 1
    funext x
    obtain ⟨cm, ⟨a₁, pf₁⟩, a₂, pf₂⟩ := x
    dsimp only
    split_ifs with hc
    · obtain ⟨q, x, y, hx, hy, hxy⟩ := hc
      simp only [transparent, pure_bind, Function.comp_apply, pure_inj, Bool.and_eq_false_iff,
        decide_eq_false_iff_not]
      by_contra hagree
      simp only [not_or, not_not] at hagree
      exact hxy (Option.some_injective _ ((hagree.1 q x hx).symm.trans (hagree.2 q y hy)))
    · rfl
  rw [positionBindingAdvantage_eq, h, ProbCompRuntime.evalDist_map _ _ measurable_const,
    MeasureTheory.Measure.map_apply measurable_const (measurableSet_singleton true)]
  simp

/-- Identical openings never conflict. -/
example (a : PartialVec 1 Bool) : ¬ PartialVec.Conflict a a := by simp

/-- Conflict is symmetric. -/
example (a b : PartialVec 1 Bool) (h : PartialVec.Conflict a b) : PartialVec.Conflict b a :=
  h.symm

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
  (SaltedMerkle.perfectlyComplete enc d).perfectlyCompleteForAll.evalDist_rom_completenessExp_eq_one
    msg Q

/-- The same holds for a random oracle programmed by an initial cache. -/
example (cache : (X →ₒ Y).QueryCache) (msg : Fin (2 ^ d) → Msg) (Q : Finset (Fin (2 ^ d))) :
    (ProbCompRuntime.rom (X →ₒ Y) cache).evalDist
      ((SaltedMerkle.scheme enc d).toVectorCommitment.completenessExp msg Q) {true} = 1 :=
  (SaltedMerkle.perfectlyComplete enc d).perfectlyCompleteForAll.evalDist_rom_completenessExp_eq_one
    msg Q

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
