/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.CryptoFoundations.GroupModel.HashToGroup.Programmed
public import VCVio.CryptoFoundations.GroupModel.HashToGroup.Provenance
public import VCVio.CryptoFoundations.HardnessAssumptions.DiscreteLogRelation

/-! # Relations from collisions over a finite table of hash answers

A normalized collision subtracts representations after merging repeated receipts by origin.
When the labels are finite, the answer of every label can be sampled ahead of time, with one
challenge coordinate for each fixed input and each label. The named finder then wins the shared
relation experiment, and the discrete-log bound is `DiscreteLogRelation.experiment_le`. Neither
statement bounds the number of hash queries, and `g` need only be nonzero.

`HashToGroup.LazyRelation` treats the lazily sampled oracle on arbitrary labels, under a hash-query
budget, by a separate argument.
-/

public section

namespace GroupModel.HashToGroup

open OracleComp OracleSpec Interaction
open scoped ENNReal

variable {Label F G κ : Type} {n : ℕ}

/-- Execute a certified coin-bearing hash adversary with separate symbolic challenge coordinates.
Fixed inputs occupy identity coordinates; hash replies append their label origins. -/
@[expose] def normalizedExecution [DecidableEq Label] [CommSemiring F] [AddCommMonoid G]
    [Module F G] (B : Origin n Label → G)
    (A : Adversary F (fun _ : Unit => G) Unit (CoinQuery Label)
      (CoinReply (fun _ => Unit)) Unit) :
    ProbComp (Explained F Unit (fun _ : Unit => G) × State Label (Origin n Label)) :=
  runGameWithCoins B (fun l => pure (.inr l))
    (A.main ⟨(), fun _ => (List.ofFn fun i : Fin n => Sum.inl i).map B⟩)
    (initial (List.ofFn fun i : Fin n => Sum.inl i))

/-- Symbolic challenge executions validate outputs over the chronological origin log. -/
theorem normalizedExecution_valid [DecidableEq Label] [CommSemiring F] [AddCommMonoid G]
    [Module F G] (B : Origin n Label → G)
    (A : Adversary F (fun _ : Unit => G) Unit (CoinQuery Label)
      (CoinReply (fun _ => Unit)) Unit) (z)
    (hz : z ∈ support (normalizedExecution B A)) :
    z.1.Valid (fun _ => z.2.2.map B) :=
  runGameWithCoins_valid B _ _ _ (A.algebraic _) z hz

/-- The named normalized relation finder returns the merged difference, including the fixed
input coordinates, from a randomized certified execution. -/
@[expose] def normalizedReduction [DecidableEq Label] [CommRing F] [AddCommGroup G]
    [Module F G]
    (A : Adversary F (fun _ : Unit => G) Unit (CoinQuery Label)
      (CoinReply (fun _ => Unit)) Unit) :
    DiscreteLogRelation.Adversary F G (Origin n Label) unifSpec :=
  fun B => (fun z => mergedDifference z.2.2 z.1) <$> normalizedExecution B A

/-- Sample independent scalar challenge coordinates for the fixed inputs and all hash labels.
The full output retains provenance for the normalized winning event. -/
@[expose] noncomputable def normalizedTrial [FinEnum Label] [Field F]
    [SampleableType F] [AddCommGroup G] [Module F G] (n : ℕ) (g : G)
    (A : Adversary F (fun _ : Unit => G) Unit (CoinQuery Label)
      (CoinReply (fun _ => Unit)) Unit) :
    ProbComp ((Origin n Label → G) × Explained F Unit (fun _ : Unit => G) ×
      State Label (Origin n Label)) := do
  let x ← $ᵗ (Origin n Label → F)
  let B := fun i => x i • g
  let z ← normalizedExecution B A
  pure (B, z)

/-- Normalized collisions in the independently sampled challenge-table game reduce to the
shared relation experiment with no receipt-cancellation term. Fixed inputs are sampled as
separate challenge coordinates, not represented by arbitrary initial rows. -/
theorem normalizedTrial_le_relation [FinEnum Label] [Field F]
    [DecidableEq F] [SampleableType F] [AddCommGroup G] [Module F G] [DecidableEq G]
    (n : ℕ) (g : G)
    (A : Adversary F (fun _ : Unit => G) Unit (CoinQuery Label)
      (CoinReply (fun _ => Unit)) Unit) :
    Pr{let w ← normalizedTrial n g A}[NormalizedCollision w.2.2.2 w.2.1] ≤
      Pr{let b ← (DiscreteLogRelation.plainExperiment g
        (normalizedReduction (n := n) A))}[b = true] := by
  simp only [normalizedTrial, normalizedReduction, DiscreteLogRelation.plainExperiment,
    DiscreteLogRelation.experiment, DiscreteLogRelation.plainAdversary, StateT.run'_eq,
    DiscreteLogRelation.map_run_plainImpl, prEvent_norm]
  apply prEvent_bind_mono_of_support
  intro x _
  apply prEvent_mono_of_support
  intro z hz hc
  have hr : ∑ i, mergedDifference z.2.2 z.1 i • (x i • g) = 0 :=
    (normalizedRelation _ _ _ (normalizedExecution_valid _ A z hz) hc).relation
  simp only [decide_eq_true_eq]
  -- The experiment sums with the `Fintype` instance of its enumeration.
  exact ⟨mergedDifference_ne_zero _ _ hc, by convert hr⟩

/-- The challenge-table normalized collision bound has a single hidden-mask loss `1 / |F|`.
The named reduction samples independent masks for every challenge coordinate before running
its adaptive, coin-bearing adversary; the relation theorem proves their conditional independence. -/
theorem normalizedTrial_le_dlog [FinEnum Label] [Field F] [Fintype F]
    [DecidableEq F] [SampleableType F] [AddCommGroup G] [Module F G]
    (n : ℕ) (g : G) (hg : g ≠ 0)
    (A : Adversary F (fun _ : Unit => G) Unit (CoinQuery Label)
      (CoinReply (fun _ => Unit)) Unit) :
    Pr{let w ← normalizedTrial n g A}[NormalizedCollision w.2.2.2 w.2.1] ≤
      Pr{let b ← (DiffieHellman.dlogExperiment g
        (DiscreteLogRelation.plainReduction (normalizedReduction (n := n) A)))}[b = true] +
        1 / Fintype.card F := by
  classical
  exact (normalizedTrial_le_relation n g A).trans (DiscreteLogRelation.experiment_le _ () g hg _)

end GroupModel.HashToGroup
