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
hiding with a simulator, for `t`-query adversaries opening a fixed number `q` of positions, with
error `ζ(q, t)`. This file also states that simulation-based form (`simulationHidingAdvantage`) and
proves that it implies the two-message game. The two-message advantage is at most the sum of two
simulation advantages (`hidingAdvantage_le_simulationHidingAdvantage`). The adversaries playing
the two worlds keep the oracle-query budget and the chosen positions, so a simulation bound `ε` for
`t`-query adversaries gives two-message advantage at most `2 ε` for `t`-query adversaries
(`hidingAdvantage_le_two_mul`), and likewise at a fixed opening size
(`hidingAdvantage_le_two_mul_of_card`), which gives `2 ζ(q, t)`. Splitting this adaptive-size game
by the size of the chosen set gives error `2 Σ_q ζ(q, t)` over the `ℓ + 1` possible sizes; that
split is not proved here.

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
* `VectorCommitment.SimulationHidingAdversary.MakesAtMostQueries` and the `OpensExactly`
  predicates on both adversary types: query budgets and opening sizes.

## Main results

* `VectorCommitment.hidingAdvantage_eq`: the hiding advantage is the distance between the
  probabilities that the two worlds return `true`.
* `VectorCommitment.hidingAdvantage_le_simulationHidingAdvantage`: the two-message advantage is at
  most the sum of the simulation advantages of the adversaries playing its two worlds.
* `VectorCommitment.HidingAdversary.makesAtMostQueries_toSimulation` and
  `VectorCommitment.HidingAdversary.opensExactly_toSimulation`: those adversaries keep the query
  budget and the opening size.
* `VectorCommitment.hidingAdvantage_le_two_mul` and
  `VectorCommitment.hidingAdvantage_le_two_mul_of_card`: query-bounded simulation-based hiding,
  optionally at a fixed opening size, implies two-message hiding with twice the error.
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

/-- If the simulation-hiding advantage is at most `ε` for every adversary satisfying `P`, then the
two-message advantage of an adversary is at most `2 ε`, provided the adversaries playing its two
worlds satisfy `P`. Simulation bounds such as Chiesa–Yogev's hold only for query-bounded adversaries
opening a fixed number of positions, so `P` is normally such a restriction; see
`hidingAdvantage_le_two_mul` and `hidingAdvantage_le_two_mul_of_card`. -/
theorem hidingAdvantage_le_two_mul_of [DecidableEq X] [SampleableType Y] [DecidableEq Msg]
    (vc : VectorCommitment X Y Msg Cm Td Pf ℓ) (simulator : HidingSimulator X Y Msg Cm Pf ℓ)
    {P : SimulationHidingAdversary X Y Msg Cm Pf ℓ → Prop} {ε : ENNReal}
    (h : ∀ adversary, P adversary → vc.simulationHidingAdvantage simulator adversary ≤ ε)
    (adversary : HidingAdversary X Y Msg Cm Pf ℓ) (hP : ∀ b, P (adversary.toSimulation b)) :
    vc.hidingAdvantage adversary ≤ 2 * ε := by
  calc vc.hidingAdvantage adversary
      ≤ vc.simulationHidingAdvantage simulator (adversary.toSimulation true) +
          vc.simulationHidingAdvantage simulator (adversary.toSimulation false) :=
        hidingAdvantage_le_simulationHidingAdvantage vc simulator adversary
    _ ≤ ε + ε := add_le_add (h _ (hP true)) (h _ (hP false))
    _ = 2 * ε := (two_mul ε).symm

/-! ### Query budgets and opening sizes -/

/-- A simulation-hiding adversary `MakesAtMostQueries q` when, for every commitment and proof,
running both stages makes at most `q` queries to the oracle on every path. Coins are free, and the
simulator's queries are not counted. -/
@[expose]
def SimulationHidingAdversary.MakesAtMostQueries
    (adversary : SimulationHidingAdversary X Y Msg Cm Pf ℓ) (q : ℕ) : Prop :=
  ∀ (cm : Cm) (pf : Pf),
    IsQueryBoundP
      (do
        let (_, _, st) ← adversary.choose
        adversary.distinguish st cm pf)
      (· matches .inr _) q

/-- A two-message hiding adversary opens exactly `q` positions. -/
@[expose]
def HidingAdversary.OpensExactly (adversary : HidingAdversary X Y Msg Cm Pf ℓ) (q : ℕ) : Prop :=
  ∀ c ∈ support adversary.choose, c.2.2.1.card = q

/-- A simulation-hiding adversary opens exactly `q` positions. -/
@[expose]
def SimulationHidingAdversary.OpensExactly (adversary : SimulationHidingAdversary X Y Msg Cm Pf ℓ)
    (q : ℕ) : Prop :=
  ∀ c ∈ support adversary.choose, c.2.1.card = q

/-- Replacing every continuation of a computation by one that satisfies every query budget its
original satisfies keeps the budget of the whole computation. -/
private theorem isQueryBoundP_bind_of_imp {ι : Type} {spec : OracleSpec ι} {α β : Type}
    {p : ι → Prop} [DecidablePred p] (oa : OracleComp spec α) {f g : α → OracleComp spec β}
    (hfg : ∀ x n, IsQueryBoundP (f x) p n → IsQueryBoundP (g x) p n) :
    ∀ n, IsQueryBoundP (oa >>= f) p n → IsQueryBoundP (oa >>= g) p n := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro n h
    rw [pure_bind] at h ⊢
    exact hfg a n h
  | query_bind t k ih =>
    intro n h
    rw [bind_assoc, isQueryBoundP_query_bind_iff] at h ⊢
    exact ⟨h.1, fun u ↦ ih u _ (h.2 u)⟩

/-- The adversaries playing the two worlds make no more oracle queries than the two-message
adversary: they run its stages and add only pure steps. -/
theorem HidingAdversary.makesAtMostQueries_toSimulation [DecidableEq Msg]
    {adversary : HidingAdversary X Y Msg Cm Pf ℓ} {q : ℕ} (h : adversary.MakesAtMostQueries q)
    (b : Bool) : (adversary.toSimulation b).MakesAtMostQueries q := by
  intro cm pf
  simp only [toSimulation, bind_assoc, pure_bind]
  refine isQueryBoundP_bind_of_imp adversary.choose (fun c n hc ↦ ?_) q (h cm pf)
  obtain ⟨m₀, m₁, Q, st⟩ := c
  by_cases hagree : PartialVec.restrict m₀ Q = PartialVec.restrict m₁ Q <;>
    simp_all

/-- The adversaries playing the two worlds open the positions the two-message adversary chose. -/
theorem HidingAdversary.opensExactly_toSimulation [DecidableEq Msg]
    {adversary : HidingAdversary X Y Msg Cm Pf ℓ} {q : ℕ} (h : adversary.OpensExactly q)
    (b : Bool) : (adversary.toSimulation b).OpensExactly q := by
  intro c hc
  simp only [toSimulation, Bool.and_eq_true, decide_eq_true_eq, bind_pure_comp,
    MonadAttach.support_map] at hc
  obtain ⟨c', hc', rfl⟩ := hc
  exact h c' hc'

/-- **Two-message hiding from query-bounded simulation-based hiding.** If every simulation-hiding
adversary making at most `t` oracle queries has advantage at most `ε`, then every two-message
hiding adversary making at most `t` oracle queries has advantage at most `2 ε`. -/
theorem hidingAdvantage_le_two_mul [DecidableEq X] [SampleableType Y] [DecidableEq Msg]
    (vc : VectorCommitment X Y Msg Cm Td Pf ℓ) (simulator : HidingSimulator X Y Msg Cm Pf ℓ)
    {t : ℕ} {ε : ENNReal}
    (h : ∀ adversary : SimulationHidingAdversary X Y Msg Cm Pf ℓ,
      adversary.MakesAtMostQueries t → vc.simulationHidingAdvantage simulator adversary ≤ ε)
    (adversary : HidingAdversary X Y Msg Cm Pf ℓ) (hq : adversary.MakesAtMostQueries t) :
    vc.hidingAdvantage adversary ≤ 2 * ε :=
  vc.hidingAdvantage_le_two_mul_of simulator h adversary
    (HidingAdversary.makesAtMostQueries_toSimulation hq)

/-- **Two-message hiding from simulation-based hiding at a fixed opening size**, the form of
Chiesa–Yogev Lemma 18.6.3: if every simulation-hiding adversary making at most `t` oracle queries
and opening exactly `q` positions has advantage at most `ε`, then so does every two-message hiding
adversary with the same budget and opening size, up to a factor of `2`. -/
theorem hidingAdvantage_le_two_mul_of_card [DecidableEq X] [SampleableType Y] [DecidableEq Msg]
    (vc : VectorCommitment X Y Msg Cm Td Pf ℓ) (simulator : HidingSimulator X Y Msg Cm Pf ℓ)
    {t q : ℕ} {ε : ENNReal}
    (h : ∀ adversary : SimulationHidingAdversary X Y Msg Cm Pf ℓ,
      adversary.MakesAtMostQueries t → adversary.OpensExactly q →
        vc.simulationHidingAdvantage simulator adversary ≤ ε)
    (adversary : HidingAdversary X Y Msg Cm Pf ℓ) (hq : adversary.MakesAtMostQueries t)
    (hcard : adversary.OpensExactly q) :
    vc.hidingAdvantage adversary ≤ 2 * ε :=
  vc.hidingAdvantage_le_two_mul_of simulator
    (P := fun a ↦ a.MakesAtMostQueries t ∧ a.OpensExactly q) (fun a ha ↦ h a ha.1 ha.2) adversary
    (fun b ↦ ⟨HidingAdversary.makesAtMostQueries_toSimulation hq b,
      HidingAdversary.opensExactly_toSimulation hcard b⟩)

end VectorCommitment
