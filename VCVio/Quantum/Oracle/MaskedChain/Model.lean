/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import VCVio.Quantum.Comp.RoundBound
public import VCVio.Quantum.Oracle.Parallel

/-!
# Endpoint recovery for idealized masked hash chains

A challenge with `q + 1` links samples `q + 2` independent uniform vertices and publishes
its first vertex and the masked links `H(xᵢ) + xᵢ₊₁`. The recovery key is the last vertex.
The adversary receives the public puzzle and outputs only one candidate endpoint.

The oracle is sampled once and is shared by challenge generation and the online execution.
There is no oracle preprocessing: the initial state, local interpretation and adversary
family are fixed independently of the sampled oracle and vertices. Honest generation's
queries are outside the online adversary's round bound. Lost mass counts as failure.

## References

* Afshar et al., *On the (Im)possibility of Time-Lock Puzzles in the Quantum Random Oracle
  Model*, §5, Definition 5.1. This game observes only the endpoint of the secret tuple.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

universe u v

namespace Quantum.MaskedChain

/-- The first vertex and `q + 1` masked links. -/
abbrev Puzzle (G : Type) (q : ℕ) := G × (Fin (q + 1) → G)

variable {G : Type} [Fintype G] [DecidableEq G]

/-- An online adversary with an oracle-independent initial quantum register and state.
Its program receives only the public masked-chain puzzle. -/
structure OnlineAdversary (L : LocalSig.{u, v}) (G : Type) [Fintype G] [DecidableEq G]
    (q : ℕ) where
  /-- Quantum workspace present before the challenge is received. -/
  initialReg : QReg
  /-- Oracle-independent initial state; missing mass is permitted. -/
  initialState : SubState initialReg
  /-- Online endpoint guess, with every final register permitted by the program model. -/
  run : Puzzle G q → QuantumComp L (qromBatchSpec G G) (fun _ ↦ G) initialReg

/-- Round and width bounds hold for every possible public challenge. -/
@[expose]
def OnlineAdversary.IsQueryBound {L : LocalSig.{u, v}} {q : ℕ}
    (adv : OnlineAdversary L G q) (rounds width : ℕ) : Prop :=
  ∀ puzzle, (adv.run puzzle).IsTotalQueryBound rounds ∧ (adv.run puzzle).IsWidthBound width

variable [AddCommGroup G]

/-- The idealized public puzzle generated from the actual oracle and sampled vertices. -/
@[expose]
def publicPuzzle {q : ℕ} (H : G → G) (vertices : Fin (q + 2) → G) : Puzzle G q :=
  (vertices 0, fun i ↦ H (vertices i.castSucc) + vertices i.succ)

/-- The distribution of endpoint equality in the idealized no-preprocessing experiment.
One sampled function supplies both the public masks and every quantum oracle call. -/
@[expose]
noncomputable def recoveryLaw {L : LocalSig.{u, v}} {q : ℕ}
    (I : L.Interp) (adv : OnlineAdversary L G q) : Measure Prop :=
  letI : MeasurableSpace (G → G) := ⊤
  letI : MeasurableSpace (Fin (q + 2) → G) := ⊤
  (uniformOn (Set.univ : Set (G → G))).bind fun H ↦
    (uniformOn (Set.univ : Set (Fin (q + 2) → G))).bind fun vertices ↦
      (parallelOracleRuntime H).evalDistMap I (adv.run (publicPuzzle H vertices)) adv.initialState
        (fun leaf ↦ leaf.2 = vertices (Fin.last (q + 1)))

/-- Unconditional probability that the adversary recovers the sampled endpoint. -/
@[expose]
noncomputable def recoveryAdvantage {L : LocalSig.{u, v}} {q : ℕ}
    (I : L.Interp) (adv : OnlineAdversary L G q) : ℝ≥0∞ :=
  recoveryLaw I adv {True}

variable {L : LocalSig.{u, v}}

/-- Expand the endpoint experiment into uniform averages over one oracle and one vertex tuple. -/
theorem recoveryAdvantage_eq_sum {q : ℕ} (I : L.Interp) (adv : OnlineAdversary L G q) :
    recoveryAdvantage I adv =
      ∑ H : G → G, (Fintype.card (G → G) : ℝ≥0∞)⁻¹ *
        ∑ vertices : Fin (q + 2) → G, (Fintype.card (Fin (q + 2) → G) : ℝ≥0∞)⁻¹ *
          (parallelOracleRuntime H).evalDistMap I (adv.run (publicPuzzle H vertices))
            adv.initialState (fun leaf ↦ leaf.2 = vertices (Fin.last (q + 1))) {True} := by
  classical
  let : MeasurableSpace (G → G) := ⊤
  let : MeasurableSpace (Fin (q + 2) → G) := ⊤
  unfold recoveryAdvantage recoveryLaw
  rw [uniformOn_univ_bind_apply _ _ (MeasurableSet.singleton True)]
  apply Finset.sum_congr rfl
  intro H _
  congr 1
  exact uniformOn_univ_bind_apply _ _ (MeasurableSet.singleton True)

private theorem sum_average_le {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (f : Ω → ℝ≥0∞) (b : ℝ≥0∞) (h : ∀ ω, f ω ≤ b) :
    ∑ ω, (Fintype.card Ω : ℝ≥0∞)⁻¹ * f ω ≤ b := by
  calc
    _ ≤ ∑ _ω : Ω, (Fintype.card Ω : ℝ≥0∞)⁻¹ * b := by
      gcongr
      exact h _
    _ = b := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc,
        ENNReal.mul_inv_cancel (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
          (ENNReal.natCast_ne_top _), one_mul]

/-- Missing mass counts as failure, so endpoint success is at most one. -/
theorem recoveryAdvantage_le_one {q : ℕ} (I : L.Interp) (adv : OnlineAdversary L G q) :
    recoveryAdvantage I adv ≤ 1 := by
  rw [recoveryAdvantage_eq_sum]
  apply sum_average_le
  intro H
  apply sum_average_le
  intro vertices
  exact measure_le_one (μ := (parallelOracleRuntime H).evalDistMap I
    (adv.run (publicPuzzle H vertices)) adv.initialState
    (fun leaf ↦ leaf.2 = vertices (Fin.last (q + 1)))) {True}

end Quantum.MaskedChain
