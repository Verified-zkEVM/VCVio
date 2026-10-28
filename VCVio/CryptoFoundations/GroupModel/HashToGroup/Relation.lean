/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.CryptoFoundations.GroupModel.HashToGroup.Programmed
public import VCVio.CryptoFoundations.HardnessAssumptions.DiscreteLogRelation

/-! # Relations extracted from hash-to-group interactions

Subtracting two transported explanations produces a relation over the reduction basis unless
the coefficient substitution annihilates their difference. The bound retains this exact loss.
For chronological receipts it can be one: two replies to the same label have the same row.
The independent hidden-mask loss in the subsequent discrete-log reduction is `1 / |F|`.
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

/-- The named relation adversary runs the programmed interaction and subtracts its two final
representations. -/
@[expose] def relationReduction [DecidableEq Label] [CommRing F] [AddCommGroup G]
    [Module F G] (sample : (Fin n → G) → Label → ProbComp (Fin n → F))
    (A : Adversary F (fun _ : Unit => G) Unit Label (fun _ => Unit) Unit)
    (rows : List (Fin n → F)) : DiscreteLogRelation.Adversary F G n :=
  fun B => (fun z => relationVector z.2.2 z.1) <$> execution B (sample B) A rows

/-- Sample the relation problem's basis and retain the full programmed interaction for measuring
collisions and the exact cancellation loss. -/
@[expose] def relationTrial [DecidableEq Label] [Field F] [SampleableType F]
    [AddCommGroup G] [Module F G] (g : G)
    (sample : (Fin n → G) → Label → ProbComp (Fin n → F))
    (A : Adversary F (fun _ : Unit => G) Unit Label (fun _ => Unit) Unit)
    (rows : List (Fin n → F)) :
    ProbComp ((Fin n → G) × Explained F Unit (fun _ : Unit => G) ×
      State Label (Fin n → F)) := do
  let x ← $ᵗ (Fin n → F)
  let B := fun i => x i • g
  let z ← execution B (sample B) A rows
  pure (B, z)

/-- Finding two chronological representations reduces to the relation experiment, with exactly
the probability of a collision whose transported difference is zero as additive loss.
This loss need not be at most `1 / |F|` when receipts repeat a cached label. -/
theorem relationTrial_le [DecidableEq Label] [Field F] [DecidableEq F] [SampleableType F]
    [AddCommGroup G] [Module F G] [DecidableEq G] (g : G)
    (sample : (Fin n → G) → Label → ProbComp (Fin n → F))
    (A : Adversary F (fun _ : Unit => G) Unit Label (fun _ => Unit) Unit)
    (rows : List (Fin n → F)) :
    Pr{let w ← relationTrial g sample A rows}[RepresentationCollision w.2.1] ≤
      Pr{let b ← DiscreteLogRelation.experiment g (relationReduction sample A rows)}[b = true] +
        Pr{let w ← relationTrial g sample A rows}[
          RepresentationCollision w.2.1 ∧ relationVector w.2.2.2 w.2.1 = 0] := by
  let trial := relationTrial g sample A rows
  let win := fun w : (Fin n → G) × Explained F Unit (fun _ : Unit => G) ×
    State Label (Fin n → F) => RepresentationCollision w.2.1
  let success := fun w : (Fin n → G) × Explained F Unit (fun _ : Unit => G) ×
    State Label (Fin n → F) => relationVector w.2.2.2 w.2.1 ≠ 0 ∧
      basisMap w.1 (relationVector w.2.2.2 w.2.1) = 0
  have hs : Pr{let w ← trial}[success w] =
      Pr{let b ← DiscreteLogRelation.experiment g (relationReduction sample A rows)}[b = true] := by
    simp [trial, relationTrial, success, DiscreteLogRelation.experiment,
      relationReduction, basisMap, prEvent_norm]
  have hv (w) (hw : w ∈ support trial) :
      w.2.1.Valid (fun _ : Unit => w.2.2.2.map (basisMap w.1)) := by
    simp only [trial, relationTrial, mem_support_bind_iff] at hw
    obtain ⟨x, _, z, hz, hw⟩ := hw
    simp only [support_pure, Set.mem_singleton_iff] at hw
    subst w
    exact execution_valid _ _ A rows z hz
  have hb : Pr{let w ← trial}[win w ∧ ¬ success w] ≤
      Pr{let w ← trial}[win w ∧ relationVector w.2.2.2 w.2.1 = 0] := by
    apply prEvent_mono_of_support
    intro w hw h
    refine ⟨h.1, ?_⟩
    by_contra hn
    exact h.2 ⟨hn, basisMap_relationVector w.1 _ _ (hv w hw) h.1⟩
  calc _ ≤ Pr{let w ← trial}[success w] + Pr{let w ← trial}[win w ∧ ¬ success w] :=
      prEvent_le_prEvent_add_prEvent_and_not trial win success
    _ ≤ _ := by rw [hs]; exact add_le_add le_rfl hb

/-- The hash collision bound composed with the existing named discrete-log reduction. Its
losses are the exact chronological cancellation probability and the independent `1 / |F|`
hidden-mask loss of `DiscreteLogRelation.reduction`. -/
theorem relationTrial_le_dlog [DecidableEq Label] [Field F] [Fintype F] [DecidableEq F]
    [SampleableType F] [AddCommGroup G] [Module F G]
    (g : G) (hg : Function.Bijective (· • g : F → G))
    (sample : (Fin n → G) → Label → ProbComp (Fin n → F))
    (A : Adversary F (fun _ : Unit => G) Unit Label (fun _ => Unit) Unit)
    (rows : List (Fin n → F)) :
    Pr{let w ← relationTrial g sample A rows}[RepresentationCollision w.2.1] ≤
      Pr{let b ← (DiffieHellman.dlogExperiment g
        (DiscreteLogRelation.reduction (relationReduction sample A rows)))}[b = true] +
      1 / Fintype.card F + Pr{let w ← relationTrial g sample A rows}[
        RepresentationCollision w.2.1 ∧ relationVector w.2.2.2 w.2.1 = 0] := by
  classical
  exact (relationTrial_le g sample A rows).trans
    (add_le_add (DiscreteLogRelation.experiment_le g hg
      (relationReduction sample A rows)) le_rfl)

end GroupModel.HashToGroup
