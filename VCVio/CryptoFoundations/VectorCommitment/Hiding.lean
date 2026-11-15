/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import VCVio.CryptoFoundations.VectorCommitment.Basic
public import VCVio.OracleComp.QueryTracking.QueryBound.Basic
public import VCVio.OracleComp.QueryTracking.RandomOracle.Simulation
public import ToMathlib.MeasureTheory.Measure.Bool

/-!
# Hiding of vector commitments

Two-message hiding of commitment and opening. A hiding adversary chooses two messages and a set
`Q` of positions on which they agree, receives the commitment to one of them and the opening proof
for `Q`, and outputs a bit. Its advantage is the distance between the probabilities that it
outputs `true` in the two worlds.

Chiesa and Yogev (*Building Cryptographic Proofs from Hash Functions*, §18.6, Lemma 18.6.3) state
hiding with a simulator, for each opening size `q` fixed in advance, with error `ζ(q)`. This file
also states that simulation-based form (`simulationHidingAdvantage`) and proves that it implies
the two-message game: the two-message advantage is at most the sum of two simulation advantages
(`hidingAdvantage_le_simulationHidingAdvantage`), hence at most `2 ε` when every simulation
advantage is at most `ε` (`hidingAdvantage_le_two_mul`). The reduction keeps the chosen positions,
so the fixed-size form follows with error `2 ζ(q)`. Splitting this adaptive-size game by the size of
the chosen set gives error `2 Σ_q ζ(q)` over the `ℓ + 1` possible sizes; that split is not proved
here.

The adversary chooses `Q`, including its size, after seeing its own oracle answers and before the
commitment. A notion with the size of `Q` fixed in advance is weaker and follows by restricting
the adversary.

The advantage is stated in the random oracle model: both worlds run against the lazily sampled
random oracle `ProbCompRuntime.rom (X →ₒ Y)`, shared by the adversary's two stages and the scheme.

## Main definitions

* `VectorCommitment.HidingAdversary`, `VectorCommitment.hidingExperiment` and
  `VectorCommitment.hidingAdvantage`.
* `VectorCommitment.HidingAdversary.MakesAtMostQueries`: one oracle-query budget shared by both
  stages of the adversary.
* `VectorCommitment.HidingSimulator`, `VectorCommitment.SimulationHidingAdversary`, the real and
  ideal experiments, and `VectorCommitment.simulationHidingAdvantage`.
* `VectorCommitment.HidingAdversary.toSimulation`: the simulation-hiding adversary that plays
  world `b` of a two-message adversary.

## Main results

* `VectorCommitment.hidingAdvantage_eq`: the hiding advantage is the distance between the
  probabilities that the two worlds return `true`.
* `VectorCommitment.hidingAdvantage_le_simulationHidingAdvantage` and
  `VectorCommitment.hidingAdvantage_le_two_mul`: simulation-based hiding implies two-message
  hiding with twice the error.
-/

public section

open OracleComp OracleSpec MeasureTheory

namespace VectorCommitment

variable {X : Type} {Y : Type} {Msg : Type} {Cm Td Pf : Type} {ℓ : ℕ}

/-- A two-stage hiding adversary. `choose` returns two messages, a set of positions to open and a
state; `distinguish` sees the state, the commitment and the opening proof, and outputs a bit. The
messages are outputs of an oracle computation, so `Msg` is in `Type`. -/
structure HidingAdversary (X : Type) (Y : Type) (Msg : Type) (Cm Pf : Type) (ℓ : ℕ) where
  /-- State carried from the first stage to the second. -/
  State : Type
  /-- Choose the two messages, the positions to open and a state. -/
  choose : OracleComp (unifSpec + (X →ₒ Y))
    ((Fin ℓ → Msg) × (Fin ℓ → Msg) × Finset (Fin ℓ) × State)
  /-- Guess the world from the state, the commitment and the opening proof. -/
  distinguish : State → Cm → Pf → OracleComp (unifSpec + (X →ₒ Y)) Bool

/-- The hiding experiment in world `b`: commit to the second message when `b` is `true` and to the
first otherwise, open the chosen positions, and return the adversary's bit. If the messages differ
on the chosen positions, both worlds commit to the first message and return `false`, so such
messages give no advantage. -/
@[expose]
def hidingExperiment [DecidableEq Msg] (vc : VectorCommitment X Y Msg Cm Td Pf ℓ)
    (adversary : HidingAdversary X Y Msg Cm Pf ℓ) (b : Bool) :
    OracleComp (unifSpec + (X →ₒ Y)) Bool := do
  let (m₀, m₁, Q, st) ← adversary.choose
  let agree := decide (PartialVec.restrict m₀ Q = PartialVec.restrict m₁ Q)
  let (cm, td) ← vc.commit (if b && agree then m₁ else m₀)
  let pf ← liftComp (vc.opening Q td) (unifSpec + (X →ₒ Y))
  if agree then adversary.distinguish st cm pf else return false

/-- The hiding advantage: the `Measure.boolDist` of the two worlds of `hidingExperiment`, each run
against the lazily sampled random oracle. -/
@[expose]
noncomputable def hidingAdvantage [DecidableEq X] [SampleableType Y] [DecidableEq Msg]
    (vc : VectorCommitment X Y Msg Cm Td Pf ℓ) (adversary : HidingAdversary X Y Msg Cm Pf ℓ) :
    ENNReal :=
  ((ProbCompRuntime.rom (X →ₒ Y)).evalDist (vc.hidingExperiment adversary true)).boolDist
    ((ProbCompRuntime.rom (X →ₒ Y)).evalDist (vc.hidingExperiment adversary false))

/-- The hiding advantage is the distance between the probabilities that the two worlds return
`true`, against the lazily sampled random oracle. -/
theorem hidingAdvantage_eq [DecidableEq X] [SampleableType Y] [DecidableEq Msg]
    (vc : VectorCommitment X Y Msg Cm Td Pf ℓ) (adversary : HidingAdversary X Y Msg Cm Pf ℓ) :
    vc.hidingAdvantage adversary =
      ENNReal.absDiff
        ((ProbCompRuntime.rom (X →ₒ Y)).evalDist (vc.hidingExperiment adversary true) {true})
        ((ProbCompRuntime.rom (X →ₒ Y)).evalDist (vc.hidingExperiment adversary false) {true}) := by
  rw [hidingAdvantage, Measure.boolDist]

/-- A hiding adversary `MakesAtMostQueries q` when, for every commitment and proof, running both
stages makes at most `q` queries to the oracle on every path. Coins are free. -/
@[expose]
def HidingAdversary.MakesAtMostQueries (adversary : HidingAdversary X Y Msg Cm Pf ℓ) (q : ℕ) :
    Prop :=
  ∀ (cm : Cm) (pf : Pf),
    IsQueryBoundP
      (do
        let (_, _, _, st) ← adversary.choose
        adversary.distinguish st cm pf)
      (· matches .inr _) q

/-! ## Simulation-based hiding -/

/-- A hiding simulator produces a commitment and an opening proof for a set of positions from the
values at those positions alone. It may query the random oracle but not program it. -/
abbrev HidingSimulator (X : Type) (Y : Type) (Msg : Type) (Cm Pf : Type) (ℓ : ℕ) :=
  Finset (Fin ℓ) → PartialVec ℓ Msg → OracleComp (unifSpec + (X →ₒ Y)) (Cm × Pf)

/-- An adversary against simulation-based hiding: `choose` returns a message, a set of positions
and a state, and `distinguish` sees the state, a commitment and an opening proof. -/
structure SimulationHidingAdversary (X : Type) (Y : Type) (Msg : Type) (Cm Pf : Type) (ℓ : ℕ)
    where
  /-- State carried from the first stage to the second. -/
  State : Type
  /-- Choose the message, the positions to open and a state. -/
  choose : OracleComp (unifSpec + (X →ₒ Y)) ((Fin ℓ → Msg) × Finset (Fin ℓ) × State)
  /-- Distinguish a real commitment and opening from a simulated one. -/
  distinguish : State → Cm → Pf → OracleComp (unifSpec + (X →ₒ Y)) Bool

/-- The real world of simulation-based hiding: honestly commit to the chosen message and open the
chosen positions. -/
@[expose]
def simulationHidingRealExperiment (vc : VectorCommitment X Y Msg Cm Td Pf ℓ)
    (adversary : SimulationHidingAdversary X Y Msg Cm Pf ℓ) :
    OracleComp (unifSpec + (X →ₒ Y)) Bool := do
  let (m, Q, st) ← adversary.choose
  let (cm, td) ← vc.commit m
  let pf ← liftComp (vc.opening Q td) (unifSpec + (X →ₒ Y))
  adversary.distinguish st cm pf

/-- The ideal world of simulation-based hiding: the simulator sees only the chosen positions and
the values there. -/
@[expose]
def simulationHidingIdealExperiment (simulator : HidingSimulator X Y Msg Cm Pf ℓ)
    (adversary : SimulationHidingAdversary X Y Msg Cm Pf ℓ) :
    OracleComp (unifSpec + (X →ₒ Y)) Bool := do
  let (m, Q, st) ← adversary.choose
  let (cm, pf) ← simulator Q (PartialVec.restrict m Q)
  adversary.distinguish st cm pf

/-- The simulation-hiding advantage: the `Measure.boolDist` of the real and ideal worlds, each run
against the lazily sampled random oracle. Chiesa and Yogev, Lemma 18.6.3, bound the corresponding
statistical distance for each opening size. -/
@[expose]
noncomputable def simulationHidingAdvantage [DecidableEq X] [SampleableType Y]
    (vc : VectorCommitment X Y Msg Cm Td Pf ℓ) (simulator : HidingSimulator X Y Msg Cm Pf ℓ)
    (adversary : SimulationHidingAdversary X Y Msg Cm Pf ℓ) : ENNReal :=
  ((ProbCompRuntime.rom (X →ₒ Y)).evalDist (vc.simulationHidingRealExperiment adversary)).boolDist
    ((ProbCompRuntime.rom (X →ₒ Y)).evalDist
      (simulationHidingIdealExperiment simulator adversary))

/-- The simulation-hiding adversary that plays the two-message adversary's world `b`. It commits to
the message world `b` selects when the two messages agree on the chosen positions, and to the first
message otherwise, and it keeps the chosen positions, so it preserves a fixed opening size. -/
@[expose]
def HidingAdversary.toSimulation [DecidableEq Msg] (adversary : HidingAdversary X Y Msg Cm Pf ℓ)
    (b : Bool) : SimulationHidingAdversary X Y Msg Cm Pf ℓ where
  State := adversary.State × Bool
  choose := do
    let (m₀, m₁, Q, st) ← adversary.choose
    let agree := decide (PartialVec.restrict m₀ Q = PartialVec.restrict m₁ Q)
    return (if b && agree then m₁ else m₀, Q, (st, agree))
  distinguish s cm pf := if s.2 then adversary.distinguish s.1 cm pf else return false

/-- World `b` of the two-message experiment is the real world for the adversary playing it. -/
theorem hidingExperiment_eq_simulationHidingRealExperiment [DecidableEq Msg]
    (vc : VectorCommitment X Y Msg Cm Td Pf ℓ) (adversary : HidingAdversary X Y Msg Cm Pf ℓ)
    (b : Bool) :
    vc.hidingExperiment adversary b =
      vc.simulationHidingRealExperiment (adversary.toSimulation b) := by
  simp [hidingExperiment, simulationHidingRealExperiment, HidingAdversary.toSimulation]

/-- The simulator sees the same values in both worlds, so the two ideal worlds coincide. -/
theorem simulationHidingIdealExperiment_toSimulation [DecidableEq Msg]
    (simulator : HidingSimulator X Y Msg Cm Pf ℓ) (adversary : HidingAdversary X Y Msg Cm Pf ℓ) :
    simulationHidingIdealExperiment simulator (adversary.toSimulation true) =
      simulationHidingIdealExperiment simulator (adversary.toSimulation false) := by
  simp only [simulationHidingIdealExperiment, HidingAdversary.toSimulation, bind_assoc, pure_bind]
  congr 1
  funext c
  obtain ⟨m₀, m₁, Q, st⟩ := c
  by_cases h : PartialVec.restrict m₀ Q = PartialVec.restrict m₁ Q <;> simp [h]

/-- **Simulation-based hiding implies two-message hiding.** The two-message advantage is at most
the sum of the simulation-hiding advantages of the adversaries playing its two worlds. -/
theorem hidingAdvantage_le_simulationHidingAdvantage [DecidableEq X] [SampleableType Y]
    [DecidableEq Msg] (vc : VectorCommitment X Y Msg Cm Td Pf ℓ)
    (simulator : HidingSimulator X Y Msg Cm Pf ℓ) (adversary : HidingAdversary X Y Msg Cm Pf ℓ) :
    vc.hidingAdvantage adversary ≤
      vc.simulationHidingAdvantage simulator (adversary.toSimulation true) +
        vc.simulationHidingAdvantage simulator (adversary.toSimulation false) := by
  rw [hidingAdvantage, hidingExperiment_eq_simulationHidingRealExperiment,
    hidingExperiment_eq_simulationHidingRealExperiment, simulationHidingAdvantage,
    simulationHidingAdvantage, simulationHidingIdealExperiment_toSimulation]
  refine (Measure.boolDist_triangle _ ((ProbCompRuntime.rom (X →ₒ Y)).evalDist
    (simulationHidingIdealExperiment simulator (adversary.toSimulation false))) _).trans_eq ?_
  rw [Measure.boolDist_comm ((ProbCompRuntime.rom (X →ₒ Y)).evalDist
    (simulationHidingIdealExperiment simulator (adversary.toSimulation false)))]

/-- With simulation error at most `ε` for every adversary, the two-message advantage is at most
`2 ε`. Restricting both notions to a fixed opening size gives the same bound, because
`HidingAdversary.toSimulation` keeps the chosen positions. -/
theorem hidingAdvantage_le_two_mul [DecidableEq X] [SampleableType Y] [DecidableEq Msg]
    (vc : VectorCommitment X Y Msg Cm Td Pf ℓ) (simulator : HidingSimulator X Y Msg Cm Pf ℓ)
    {ε : ENNReal} (h : ∀ adversary, vc.simulationHidingAdvantage simulator adversary ≤ ε)
    (adversary : HidingAdversary X Y Msg Cm Pf ℓ) :
    vc.hidingAdvantage adversary ≤ 2 * ε := by
  calc vc.hidingAdvantage adversary
      ≤ vc.simulationHidingAdvantage simulator (adversary.toSimulation true) +
          vc.simulationHidingAdvantage simulator (adversary.toSimulation false) :=
        hidingAdvantage_le_simulationHidingAdvantage vc simulator adversary
    _ ≤ ε + ε := add_le_add (h _) (h _)
    _ = 2 * ε := (two_mul ε).symm

end VectorCommitment
