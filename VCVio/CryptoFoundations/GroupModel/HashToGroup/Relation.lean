/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.CryptoFoundations.GroupModel.HashToGroup.Provenance
public import VCVio.CryptoFoundations.HardnessAssumptions.DiscreteLogRelation

/-! # Relations extracted from hash-to-group interactions

A normalized collision subtracts representations after merging repeated receipts by origin.
The challenge-table experiment gives each fixed-input slot and hash label its own coordinate.
Its reduction is an instance of the shared relation experiment; the subsequent discrete-log
bound uses the joint hidden-mask argument of `DiscreteLogRelation.experiment_le`.

The quantitative experiment samples a complete finite table. `HashToGroup.LazyRelation` connects
the honest lazy oracle on arbitrary labels to a finite challenge basis under a hash-query budget.
-/

public section

namespace GroupModel.HashToGroup

open OracleComp OracleSpec Interaction
open scoped ENNReal

variable {Label F G κ : Type} {n : ℕ}

/-- Two different coefficient lists explaining the same group element as two final outputs. -/
@[expose] def RepresentationCollision (out : Explained F Unit (fun _ : Unit => G)) : Prop :=
  ∃ (a b : List F) (g : G), out.coefficients () = [a, b] ∧
    out.value.groups () = [g, g] ∧ a ≠ b

/-- Subtract the first two output representations after substituting their recorded rows. -/
@[expose] def relationVector [Ring F] (rows : List (κ → F))
    (out : Explained F Unit (fun _ : Unit => G)) : κ → F :=
  transport rows (((out.coefficients ())[0]?).getD []) -
    transport rows (((out.coefficients ())[1]?).getD [])

/-- A collision of valid explanations transports to a vanishing group combination. -/
theorem basisMap_relationVector [CommRing F] [AddCommGroup G] [Module F G] [Fintype κ]
    (B : κ → G) (rows : List (κ → F)) (out : Explained F Unit (fun _ : Unit => G))
    (hv : out.Valid (fun _ => rows.map (basisMap B))) (hc : RepresentationCollision out) :
    basisMap B (relationVector rows out) = 0 := by
  obtain ⟨a, b, g, ha, hg, _⟩ := hc
  have h := hv ()
  simp only [ha, hg, List.forall₂_cons, List.forall₂_nil_right_iff, and_true] at h
  simp [relationVector, ha, map_sub, basisMap_transport, h.1.2, h.2.2]

/-- Execute a certified hash adversary, starting from specified rows for its fixed inputs. -/
@[expose] def execution [DecidableEq Label] [CommSemiring F] [AddCommMonoid G]
    [Module F G] [Fintype κ] (B : κ → G) (sample : Label → ProbComp (κ → F))
    (A : Adversary F (fun _ : Unit => G) Unit Label (fun _ => Unit) Unit)
    (rows : List (κ → F)) :
    ProbComp (Explained F Unit (fun _ : Unit => G) × State Label (κ → F)) :=
  runProgram B sample (A.main ⟨(), fun _ => rows.map (basisMap B)⟩) (initial rows)

/-- Every final explanation in a certified execution is valid over the recorded rows. -/
theorem execution_valid [DecidableEq Label] [CommSemiring F] [AddCommMonoid G]
    [Module F G] [Fintype κ] (B : κ → G) (sample : Label → ProbComp (κ → F))
    (A : Adversary F (fun _ : Unit => G) Unit Label (fun _ => Unit) Unit)
    (rows : List (κ → F)) (z)
    (hz : z ∈ support (execution B sample A rows)) :
    z.1.Valid (fun _ => z.2.2.map (basisMap B)) :=
  runProgram_valid B sample _ (initial rows) (A.algebraic _) z hz


/-- Execute a certified randomized hash adversary with the programmed coefficient log. -/
@[expose] def executionWithCoins [DecidableEq Label] [CommSemiring F] [AddCommMonoid G]
    [Module F G] [Fintype κ] (B : κ → G) (sample : Label → ProbComp (κ → F))
    (A : Adversary F (fun _ : Unit => G) Unit (CoinQuery Label)
      (CoinReply (fun _ => Unit)) Unit) (rows : List (κ → F)) :
    ProbComp (Explained F Unit (fun _ : Unit => G) × State Label (κ → F)) :=
  runProgramWithCoins B sample (A.main ⟨(), fun _ => rows.map (basisMap B)⟩) (initial rows)

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
@[expose] noncomputable def normalizedTrial [Fintype Label] [DecidableEq Label] [Field F]
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
theorem normalizedTrial_le_relation [Fintype Label] [DecidableEq Label] [Field F]
    [DecidableEq F] [SampleableType F] [AddCommGroup G] [Module F G] [DecidableEq G]
    (n : ℕ) (g : G)
    (A : Adversary F (fun _ : Unit => G) Unit (CoinQuery Label)
      (CoinReply (fun _ => Unit)) Unit) :
    Pr{let w ← normalizedTrial n g A}[NormalizedCollision w.2.2.2 w.2.1] ≤
      Pr{let b ← (DiscreteLogRelation.plainExperiment g
        (normalizedReduction (n := n) A))}[b = true] := by
  have hs : Pr{let w ← normalizedTrial n g A}[
      mergedDifference w.2.2.2 w.2.1 ≠ 0 ∧
        basisMap w.1 (mergedDifference w.2.2.2 w.2.1) = 0] =
      Pr{let b ← (DiscreteLogRelation.plainExperiment g
        (normalizedReduction (n := n) A))}[b = true] := by
    simp only [DiscreteLogRelation.plainExperiment, DiscreteLogRelation.experiment,
      DiscreteLogRelation.plainAdversary, StateT.run'_eq, DiscreteLogRelation.map_run_plainImpl]
    simp [normalizedTrial, normalizedReduction, basisMap, prEvent_norm]
  rw [← hs]
  apply prEvent_mono_of_support
  intro w hw hc
  simp only [normalizedTrial, mem_support_bind_iff] at hw
  obtain ⟨x, _, z, hz, hw⟩ := hw
  simp only [support_pure, Set.mem_singleton_iff] at hw
  subst w
  let witness := normalizedRelation _ _ _ (normalizedExecution_valid _ A z hz) hc
  exact ⟨witness.nonzero, witness.relation⟩

/-- The challenge-table normalized collision bound has a single hidden-mask loss `1 / |F|`.
The named reduction samples independent masks for every challenge coordinate before running
its adaptive, coin-bearing adversary; the relation theorem proves their conditional independence. -/
theorem normalizedTrial_le_dlog [Fintype Label] [DecidableEq Label] [Field F] [Fintype F]
    [DecidableEq F] [SampleableType F] [AddCommGroup G] [Module F G]
    (n : ℕ) (g : G) (hg : Function.Bijective (· • g : F → G))
    (A : Adversary F (fun _ : Unit => G) Unit (CoinQuery Label)
      (CoinReply (fun _ => Unit)) Unit) :
    Pr{let w ← normalizedTrial n g A}[NormalizedCollision w.2.2.2 w.2.1] ≤
      Pr{let b ← (DiffieHellman.dlogExperiment g
        (DiscreteLogRelation.plainReduction (normalizedReduction (n := n) A)))}[b = true] +
        1 / Fintype.card F := by
  classical
  exact (normalizedTrial_le_relation n g A).trans
    (DiscreteLogRelation.experiment_le _ () g hg _)

end GroupModel.HashToGroup
