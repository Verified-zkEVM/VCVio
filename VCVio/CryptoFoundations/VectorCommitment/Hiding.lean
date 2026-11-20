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

This file states two hiding notions for vector commitments, two-message hiding and simulation
hiding, in the random oracle model.

A two-message hiding adversary chooses two messages and a set `Q` of positions on which they agree,
receives the commitment to one of them and the opening proof for `Q`, and outputs a bit. Its
advantage is the distance between the probabilities that it outputs `true` in the two worlds.

A simulation-hiding adversary chooses one message and a set `Q` of positions, and receives either
the honest commitment and opening proof or a commitment and proof that a simulator produces from
`Q` and the values at `Q` alone. Chiesa–Yogev (*Building Cryptographic Proofs from Hash Functions*,
Version 1.2, Lemma 18.6.3) call this simulation form "hiding" and prove it for Merkle commitments.

Simulation hiding implies two-message hiding. The two-message advantage of an adversary is at most
the sum of the simulation advantages of the two named adversaries `adversary.toSimulation true` and
`adversary.toSimulation false`, which play its two worlds
(`twoMessageHidingAdvantage_le_simulationHidingAdvantage`). They keep the oracle-query budget and
the opening size of the two-message adversary, so a simulation error `ε` gives the two-message
adversary advantage at most `2 ε`.

Every experiment runs against the lazily sampled random oracle `ProbCompRuntime.rom (X →ₒ Y)`,
shared by the adversary's two stages, the scheme and the simulator. In the experiments the adversary
chooses `Q`, including its size, after seeing its own oracle answers and before the commitment.

## Statistical notions

`TwoMessageHiding` and `SimulationHidingWith` bound the advantage of every adversary that makes at
most `t` oracle queries and opens exactly `q` positions, whatever its computation. They fix the
opening size `q`, as Lemma 18.6.3 does, so an adversary that chooses the size of `Q` adaptively is
not covered by them.

A bound over every query-bounded adversary is meaningful here because security is statistical in
the pure random oracle model, the model Chiesa–Yogev (Version 1.2) work in: the oracle is sampled
when the experiment runs, the adversary reaches the scheme's coins only through its oracle queries,
and adversaries are computationally unbounded but make a bounded number of oracle queries. A
computational notion instead bounds the advantage of a named reduction, or of polynomial-time
adversary families (`SecurityGame.secureAgainst` with `SecurityFamily.IsOraclePPTBy`).

The notions bound the Bool-valued distinguishing advantage. Since they range over all
query-bounded adversaries, which may post-process their view, this is equivalent to the
statistical-distance form of Lemma 18.6.3; the Bool form is the one the hybrid argument and the
advantages use.

`SimulationHiding vc s ζ` fixes one simulator for all adversaries, opening sizes and query budgets,
chosen before them, as in Lemma 18.6.3. Its error `ζ q t` takes the opening size first and the query
budget second, as the error `ζ(…, q, t)` of that lemma does. It differs from the lemma in one
respect: the lemma asks for a polynomial-time simulator, while `SimulationHiding` bounds the
simulator's oracle queries (`VectorCommitment.HidingSimulator.MakesAtMostQueries`) and not its
computation. The running time of a simulator is a property of a concrete simulator, stated where
one is constructed.

## Main definitions

* `VectorCommitment.TwoMessageHidingAdversary`, `VectorCommitment.twoMessageHidingExperiment` and
  `VectorCommitment.twoMessageHidingAdvantage`.
* `VectorCommitment.HidingSimulator`, `VectorCommitment.SimulationHidingAdversary`,
  `VectorCommitment.simulationHidingRealExperiment`,
  `VectorCommitment.simulationHidingIdealExperiment` and
  `VectorCommitment.simulationHidingAdvantage`.
* `VectorCommitment.TwoMessageHidingAdversary.toSimulation`: the simulation-hiding adversary that
  plays world `b` of a two-message adversary.
* `VectorCommitment.TwoMessageHidingAdversary.MakesAtMostQueries` and
  `VectorCommitment.SimulationHidingAdversary.MakesAtMostQueries`: one oracle-query budget shared by
  both stages of the adversary.
* `VectorCommitment.TwoMessageHidingAdversary.OpensExactly` and
  `VectorCommitment.SimulationHidingAdversary.OpensExactly`: the number of opened positions.
* `VectorCommitment.HidingSimulator.MakesAtMostQueries`: an oracle-query budget for a simulator.
* `VectorCommitment.TwoMessageHiding` and `VectorCommitment.SimulationHidingWith`: the advantage
  bounds over every adversary within a query budget and an opening size, the latter for a given
  simulator.
* `VectorCommitment.SimulationHiding`: one simulator within a query budget achieves
  `VectorCommitment.SimulationHidingWith` at every opening size and query budget.

## Main results

* `VectorCommitment.twoMessageHidingAdvantage_eq` and
  `VectorCommitment.simulationHidingAdvantage_eq`: each advantage is the distance between the
  probabilities that its two worlds return `true`.
* `VectorCommitment.twoMessageHidingAdvantage_le_simulationHidingAdvantage`: the two-message
  advantage is at most the sum of the simulation advantages of the adversaries playing its two
  worlds.
* `VectorCommitment.TwoMessageHidingAdversary.makesAtMostQueries_toSimulation` and
  `VectorCommitment.TwoMessageHidingAdversary.opensExactly_toSimulation`: those adversaries keep the
  query budget and the opening size.
* `VectorCommitment.SimulationHidingWith.twoMessageHiding` and
  `VectorCommitment.SimulationHiding.twoMessageHiding`: simulation hiding at error `ε` gives
  two-message hiding at error `2 ε`.

## References

* [Chiesa–Yogev, *Building Cryptographic Proofs from Hash Functions*, Version 1.2, the random
  oracle model, bounded-query adversaries](https://github.com/hash-based-snargs-book/hash-based-snargs-book/blob/305fa3d9d19ee6dba135de64b3156d1760df8426/snargs-book.tex#L2460-L2474).
* [Chiesa–Yogev, *Building Cryptographic Proofs from Hash Functions*, Version 1.2,
  Lemma 18.6.3](https://github.com/hash-based-snargs-book/hash-based-snargs-book/blob/305fa3d9d19ee6dba135de64b3156d1760df8426/snargs-book.tex#L14234-L14288).
-/

public section

open OracleComp OracleSpec MeasureTheory

namespace VectorCommitment

variable {X : Type} {Y : Type} {Msg : Type} {Cm Td Pf : Type} {ℓ : ℕ}

/-! ## Two-message hiding -/

/-- A two-stage two-message hiding adversary. `choose` returns two messages, a set of positions to
open and a state; `distinguish` sees the state, the commitment and the opening proof, and outputs a
bit. The messages are outputs of an oracle computation, so `Msg` is in `Type`. -/
structure TwoMessageHidingAdversary (X : Type) (Y : Type) (Msg : Type) (Cm Pf : Type) (ℓ : ℕ) where
  /-- State carried from the first stage to the second. -/
  State : Type
  /-- Choose the two messages, the positions to open and a state. -/
  choose : OracleComp (unifSpec + (X →ₒ Y))
    ((Fin ℓ → Msg) × (Fin ℓ → Msg) × Finset (Fin ℓ) × State)
  /-- Guess the world from the state, the commitment and the opening proof. -/
  distinguish : State → Cm → Pf → OracleComp (unifSpec + (X →ₒ Y)) Bool

/-- The two-message hiding experiment in world `b`: commit to the second message when `b` is `true`
and to the first otherwise, open the chosen positions, and return the adversary's bit. If the
messages differ on the chosen positions, both worlds commit to the first message and return
`false`, so such messages give no advantage. -/
@[expose]
def twoMessageHidingExperiment [DecidableEq Msg] (vc : VectorCommitment X Y Msg Cm Td Pf ℓ)
    (adversary : TwoMessageHidingAdversary X Y Msg Cm Pf ℓ) (b : Bool) :
    OracleComp (unifSpec + (X →ₒ Y)) Bool := do
  let (m₀, m₁, Q, st) ← adversary.choose
  let agree := decide (PartialVec.restrict m₀ Q = PartialVec.restrict m₁ Q)
  let (cm, td) ← vc.commit (if b && agree then m₁ else m₀)
  let pf ← liftComp (vc.opening Q td) (unifSpec + (X →ₒ Y))
  if agree then adversary.distinguish st cm pf else return false

/-- The two-message hiding advantage: the `Measure.boolDist` of the two worlds of
`twoMessageHidingExperiment`, each run against the lazily sampled random oracle. -/
noncomputable def twoMessageHidingAdvantage [DecidableEq X] [SampleableType Y] [DecidableEq Msg]
    (vc : VectorCommitment X Y Msg Cm Td Pf ℓ)
    (adversary : TwoMessageHidingAdversary X Y Msg Cm Pf ℓ) : ENNReal :=
  ((ProbCompRuntime.rom (X →ₒ Y)).evalDist (vc.twoMessageHidingExperiment adversary true)).boolDist
    ((ProbCompRuntime.rom (X →ₒ Y)).evalDist (vc.twoMessageHidingExperiment adversary false))

/-- The two-message hiding advantage is the distance between the probabilities that the two worlds
return `true`, against the lazily sampled random oracle. -/
theorem twoMessageHidingAdvantage_eq [DecidableEq X] [SampleableType Y] [DecidableEq Msg]
    (vc : VectorCommitment X Y Msg Cm Td Pf ℓ)
    (adversary : TwoMessageHidingAdversary X Y Msg Cm Pf ℓ) :
    vc.twoMessageHidingAdvantage adversary =
      ENNReal.absDiff
        ((ProbCompRuntime.rom (X →ₒ Y)).evalDist (vc.twoMessageHidingExperiment adversary true)
          {true})
        ((ProbCompRuntime.rom (X →ₒ Y)).evalDist (vc.twoMessageHidingExperiment adversary false)
          {true}) := by
  rw [twoMessageHidingAdvantage, Measure.boolDist]

/-! ## Simulation hiding -/

/-- A hiding simulator produces a commitment and an opening proof for a set of positions from the
values at those positions alone. It may query the random oracle but not program it. -/
abbrev HidingSimulator (X : Type) (Y : Type) (Msg : Type) (Cm Pf : Type) (ℓ : ℕ) :=
  Finset (Fin ℓ) → PartialVec ℓ Msg → OracleComp (unifSpec + (X →ₒ Y)) (Cm × Pf)

/-- An adversary against simulation hiding: `choose` returns a message, a set of positions and a
state, and `distinguish` sees the state, a commitment and an opening proof. -/
structure SimulationHidingAdversary (X : Type) (Y : Type) (Msg : Type) (Cm Pf : Type) (ℓ : ℕ)
    where
  /-- State carried from the first stage to the second. -/
  State : Type
  /-- Choose the message, the positions to open and a state. -/
  choose : OracleComp (unifSpec + (X →ₒ Y)) ((Fin ℓ → Msg) × Finset (Fin ℓ) × State)
  /-- Distinguish a real commitment and opening from a simulated one. -/
  distinguish : State → Cm → Pf → OracleComp (unifSpec + (X →ₒ Y)) Bool

/-- The real world of simulation hiding: honestly commit to the chosen message and open the chosen
positions. -/
@[expose]
def simulationHidingRealExperiment (vc : VectorCommitment X Y Msg Cm Td Pf ℓ)
    (adversary : SimulationHidingAdversary X Y Msg Cm Pf ℓ) :
    OracleComp (unifSpec + (X →ₒ Y)) Bool := do
  let (m, Q, st) ← adversary.choose
  let (cm, td) ← vc.commit m
  let pf ← liftComp (vc.opening Q td) (unifSpec + (X →ₒ Y))
  adversary.distinguish st cm pf

/-- The ideal world of simulation hiding: the simulator sees only the chosen positions and the
values there. -/
@[expose]
def simulationHidingIdealExperiment (simulator : HidingSimulator X Y Msg Cm Pf ℓ)
    (adversary : SimulationHidingAdversary X Y Msg Cm Pf ℓ) :
    OracleComp (unifSpec + (X →ₒ Y)) Bool := do
  let (m, Q, st) ← adversary.choose
  let (cm, pf) ← simulator Q (PartialVec.restrict m Q)
  adversary.distinguish st cm pf

/-- The simulation-hiding advantage: the `Measure.boolDist` of the real and ideal worlds, each run
against the lazily sampled random oracle. -/
noncomputable def simulationHidingAdvantage [DecidableEq X] [SampleableType Y]
    (vc : VectorCommitment X Y Msg Cm Td Pf ℓ) (simulator : HidingSimulator X Y Msg Cm Pf ℓ)
    (adversary : SimulationHidingAdversary X Y Msg Cm Pf ℓ) : ENNReal :=
  ((ProbCompRuntime.rom (X →ₒ Y)).evalDist (vc.simulationHidingRealExperiment adversary)).boolDist
    ((ProbCompRuntime.rom (X →ₒ Y)).evalDist
      (simulationHidingIdealExperiment simulator adversary))

/-- The simulation-hiding advantage is the distance between the probabilities that the real and
ideal worlds return `true`, against the lazily sampled random oracle. -/
theorem simulationHidingAdvantage_eq [DecidableEq X] [SampleableType Y]
    (vc : VectorCommitment X Y Msg Cm Td Pf ℓ) (simulator : HidingSimulator X Y Msg Cm Pf ℓ)
    (adversary : SimulationHidingAdversary X Y Msg Cm Pf ℓ) :
    vc.simulationHidingAdvantage simulator adversary =
      ENNReal.absDiff
        ((ProbCompRuntime.rom (X →ₒ Y)).evalDist (vc.simulationHidingRealExperiment adversary)
          {true})
        ((ProbCompRuntime.rom (X →ₒ Y)).evalDist
          (simulationHidingIdealExperiment simulator adversary) {true}) := by
  rw [simulationHidingAdvantage, Measure.boolDist]

/-! ## Simulation hiding implies two-message hiding -/

/-- The simulation-hiding adversary that plays the two-message adversary's world `b`. It commits to
the message world `b` selects when the two messages agree on the chosen positions, and to the first
message otherwise, and it keeps the chosen positions, so it preserves a fixed opening size. -/
@[expose]
def TwoMessageHidingAdversary.toSimulation [DecidableEq Msg]
    (adversary : TwoMessageHidingAdversary X Y Msg Cm Pf ℓ) (b : Bool) :
    SimulationHidingAdversary X Y Msg Cm Pf ℓ where
  State := adversary.State × Bool
  choose := do
    let (m₀, m₁, Q, st) ← adversary.choose
    let agree := decide (PartialVec.restrict m₀ Q = PartialVec.restrict m₁ Q)
    return (if b && agree then m₁ else m₀, Q, (st, agree))
  distinguish s cm pf := if s.2 then adversary.distinguish s.1 cm pf else return false

/-- World `b` of the two-message experiment is the real world for the adversary playing it. -/
theorem twoMessageHidingExperiment_eq_simulationHidingRealExperiment [DecidableEq Msg]
    (vc : VectorCommitment X Y Msg Cm Td Pf ℓ)
    (adversary : TwoMessageHidingAdversary X Y Msg Cm Pf ℓ) (b : Bool) :
    vc.twoMessageHidingExperiment adversary b =
      vc.simulationHidingRealExperiment (adversary.toSimulation b) := by
  simp [twoMessageHidingExperiment, simulationHidingRealExperiment,
    TwoMessageHidingAdversary.toSimulation]

/-- The simulator sees the same values in both worlds, so the adversaries playing the two worlds
have the same ideal world. -/
theorem simulationHidingIdealExperiment_toSimulation [DecidableEq Msg]
    (simulator : HidingSimulator X Y Msg Cm Pf ℓ)
    (adversary : TwoMessageHidingAdversary X Y Msg Cm Pf ℓ) (b b' : Bool) :
    simulationHidingIdealExperiment simulator (adversary.toSimulation b) =
      simulationHidingIdealExperiment simulator (adversary.toSimulation b') := by
  simp only [simulationHidingIdealExperiment, TwoMessageHidingAdversary.toSimulation, bind_assoc,
    pure_bind]
  congr 1
  funext c
  obtain ⟨m₀, m₁, Q, st⟩ := c
  by_cases h : PartialVec.restrict m₀ Q = PartialVec.restrict m₁ Q <;> cases b <;> cases b' <;>
    simp [h]

/-- **Simulation hiding implies two-message hiding.** The two-message advantage is at most the sum
of the simulation-hiding advantages of the adversaries playing its two worlds.

A simulation bound `ε` for the two adversaries `adversary.toSimulation b` therefore gives the
two-message advantage at most `2 ε`. Simulation bounds hold for adversaries within a query budget
that open a fixed number of positions; the adversaries playing the two worlds inherit both
restrictions from `adversary` (`TwoMessageHidingAdversary.makesAtMostQueries_toSimulation`,
`TwoMessageHidingAdversary.opensExactly_toSimulation`). `SimulationHidingWith.twoMessageHiding`
states the consequence for the named hiding notions. -/
theorem twoMessageHidingAdvantage_le_simulationHidingAdvantage [DecidableEq X] [SampleableType Y]
    [DecidableEq Msg] (vc : VectorCommitment X Y Msg Cm Td Pf ℓ)
    (simulator : HidingSimulator X Y Msg Cm Pf ℓ)
    (adversary : TwoMessageHidingAdversary X Y Msg Cm Pf ℓ) :
    vc.twoMessageHidingAdvantage adversary ≤
      vc.simulationHidingAdvantage simulator (adversary.toSimulation true) +
        vc.simulationHidingAdvantage simulator (adversary.toSimulation false) := by
  rw [twoMessageHidingAdvantage, twoMessageHidingExperiment_eq_simulationHidingRealExperiment,
    twoMessageHidingExperiment_eq_simulationHidingRealExperiment, simulationHidingAdvantage,
    simulationHidingAdvantage,
    simulationHidingIdealExperiment_toSimulation simulator adversary true false]
  refine (Measure.boolDist_triangle _ ((ProbCompRuntime.rom (X →ₒ Y)).evalDist
    (simulationHidingIdealExperiment simulator (adversary.toSimulation false))) _).trans_eq ?_
  rw [Measure.boolDist_comm ((ProbCompRuntime.rom (X →ₒ Y)).evalDist
    (simulationHidingIdealExperiment simulator (adversary.toSimulation false)))]

/-! ## Query budgets and opening sizes -/

/-- A two-message hiding adversary `MakesAtMostQueries t` when, for every commitment and proof,
running both stages makes at most `t` queries to the oracle on every path. Coins are free. -/
@[expose]
def TwoMessageHidingAdversary.MakesAtMostQueries
    (adversary : TwoMessageHidingAdversary X Y Msg Cm Pf ℓ) (t : ℕ) : Prop :=
  ∀ (cm : Cm) (pf : Pf),
    IsQueryBoundP
      (do
        let (_, _, _, st) ← adversary.choose
        adversary.distinguish st cm pf)
      (· matches .inr _) t

/-- A simulation-hiding adversary `MakesAtMostQueries t` when, for every commitment and proof,
running both stages makes at most `t` queries to the oracle on every path. Coins are free, and the
simulator's queries are not counted. -/
@[expose]
def SimulationHidingAdversary.MakesAtMostQueries
    (adversary : SimulationHidingAdversary X Y Msg Cm Pf ℓ) (t : ℕ) : Prop :=
  ∀ (cm : Cm) (pf : Pf),
    IsQueryBoundP
      (do
        let (_, _, st) ← adversary.choose
        adversary.distinguish st cm pf)
      (· matches .inr _) t

/-- A two-message hiding adversary opens exactly `q` positions. -/
@[expose]
def TwoMessageHidingAdversary.OpensExactly (adversary : TwoMessageHidingAdversary X Y Msg Cm Pf ℓ)
    (q : ℕ) : Prop :=
  ∀ c ∈ support adversary.choose, match c with | (_, _, Q, _) => Q.card = q

/-- A simulation-hiding adversary opens exactly `q` positions. -/
@[expose]
def SimulationHidingAdversary.OpensExactly (adversary : SimulationHidingAdversary X Y Msg Cm Pf ℓ)
    (q : ℕ) : Prop :=
  ∀ c ∈ support adversary.choose, match c with | (_, Q, _) => Q.card = q

/-- A hiding simulator `MakesAtMostQueries s` when, for every set of positions and every partial
vector, it makes at most `s` queries to the oracle on every path. Coins are free. -/
@[expose]
def HidingSimulator.MakesAtMostQueries (simulator : HidingSimulator X Y Msg Cm Pf ℓ) (s : ℕ) :
    Prop :=
  ∀ (Q : Finset (Fin ℓ)) (ans : PartialVec ℓ Msg),
    IsQueryBoundP (simulator Q ans) (· matches .inr _) s

/-- The adversaries playing the two worlds make no more oracle queries than the two-message
adversary: they run its stages and add only pure steps. -/
theorem TwoMessageHidingAdversary.makesAtMostQueries_toSimulation [DecidableEq Msg]
    {adversary : TwoMessageHidingAdversary X Y Msg Cm Pf ℓ} {t : ℕ}
    (h : adversary.MakesAtMostQueries t) (b : Bool) :
    (adversary.toSimulation b).MakesAtMostQueries t := by
  intro cm pf
  simp only [toSimulation, bind_assoc, pure_bind]
  refine (h cm pf).bind_mono_right fun c _ n hc ↦ ?_
  obtain ⟨m₀, m₁, Q, st⟩ := c
  by_cases hagree : PartialVec.restrict m₀ Q = PartialVec.restrict m₁ Q <;>
    simp_all

/-- The adversaries playing the two worlds open the positions the two-message adversary chose. -/
theorem TwoMessageHidingAdversary.opensExactly_toSimulation [DecidableEq Msg]
    {adversary : TwoMessageHidingAdversary X Y Msg Cm Pf ℓ} {q : ℕ}
    (h : adversary.OpensExactly q) (b : Bool) : (adversary.toSimulation b).OpensExactly q := by
  intro c hc
  simp only [toSimulation, Bool.and_eq_true, decide_eq_true_eq, bind_pure_comp,
    MonadAttach.support_map] at hc
  obtain ⟨c', hc', rfl⟩ := hc
  exact h c' hc'

/-! ## Hiding notions -/

/-- Two-message hiding with error `ε`: every two-message hiding adversary that makes at most `t`
oracle queries and opens exactly `q` positions has `twoMessageHidingAdvantage` at most `ε`. -/
@[expose]
def TwoMessageHiding [DecidableEq X] [SampleableType Y] [DecidableEq Msg]
    (vc : VectorCommitment X Y Msg Cm Td Pf ℓ) (t q : ℕ) (ε : ENNReal) : Prop :=
  ∀ adversary : TwoMessageHidingAdversary X Y Msg Cm Pf ℓ,
    adversary.MakesAtMostQueries t → adversary.OpensExactly q →
      vc.twoMessageHidingAdvantage adversary ≤ ε

/-- Simulation hiding with the given simulator and error `ε`: every simulation-hiding adversary
that makes at most `t` oracle queries and opens exactly `q` positions has
`simulationHidingAdvantage` at most `ε` against `simulator`. -/
@[expose]
def SimulationHidingWith [DecidableEq X] [SampleableType Y]
    (vc : VectorCommitment X Y Msg Cm Td Pf ℓ) (simulator : HidingSimulator X Y Msg Cm Pf ℓ)
    (t q : ℕ) (ε : ENNReal) : Prop :=
  ∀ adversary : SimulationHidingAdversary X Y Msg Cm Pf ℓ,
    adversary.MakesAtMostQueries t → adversary.OpensExactly q →
      vc.simulationHidingAdvantage simulator adversary ≤ ε

/-- Simulation hiding with error `ζ`: one simulator that makes at most `s` oracle queries achieves
`SimulationHidingWith` with error `ζ q t` for every opening size `q` and every query budget `t`.
The simulator is chosen before the adversary, the opening size and the query budget. Only its
oracle queries are bounded, not its computation. -/
@[expose]
def SimulationHiding [DecidableEq X] [SampleableType Y] (vc : VectorCommitment X Y Msg Cm Td Pf ℓ)
    (s : ℕ) (ζ : ℕ → ℕ → ENNReal) : Prop :=
  ∃ simulator : HidingSimulator X Y Msg Cm Pf ℓ,
    simulator.MakesAtMostQueries s ∧ ∀ t q, vc.SimulationHidingWith simulator t q (ζ q t)

/-- **Simulation hiding implies two-message hiding** at twice the error, for the same query budget
and opening size. -/
theorem SimulationHidingWith.twoMessageHiding [DecidableEq X] [SampleableType Y] [DecidableEq Msg]
    {vc : VectorCommitment X Y Msg Cm Td Pf ℓ} {simulator : HidingSimulator X Y Msg Cm Pf ℓ}
    {t q : ℕ} {ε : ENNReal} (h : vc.SimulationHidingWith simulator t q ε) :
    vc.TwoMessageHiding t q (2 * ε) := fun adversary ht hq ↦
  (twoMessageHidingAdvantage_le_simulationHidingAdvantage vc simulator adversary).trans <|
    (add_le_add
      (h _ (TwoMessageHidingAdversary.makesAtMostQueries_toSimulation ht true)
        (TwoMessageHidingAdversary.opensExactly_toSimulation hq true))
      (h _ (TwoMessageHidingAdversary.makesAtMostQueries_toSimulation ht false)
        (TwoMessageHidingAdversary.opensExactly_toSimulation hq false))).trans_eq
      (two_mul ε).symm

/-- Simulation hiding with error `ζ` implies two-message hiding with error `2 * ζ q t` for every
query budget `t` and opening size `q`. -/
theorem SimulationHiding.twoMessageHiding [DecidableEq X] [SampleableType Y] [DecidableEq Msg]
    {vc : VectorCommitment X Y Msg Cm Td Pf ℓ} {s : ℕ} {ζ : ℕ → ℕ → ENNReal}
    (h : vc.SimulationHiding s ζ) (t q : ℕ) : vc.TwoMessageHiding t q (2 * ζ q t) :=
  let ⟨_, _, hS⟩ := h
  (hS t q).twoMessageHiding

end VectorCommitment
