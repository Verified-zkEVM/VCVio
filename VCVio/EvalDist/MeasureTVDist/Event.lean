/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.EvalDist.MeasureTVDist.Basic
public import VCVio.EvalDist.ProbabilityBounds

/-!
# Total variation from agreement off a bad event

Two computations that give every event the same probability away from a bad event are within the
bad event's probability in total variation, after any post-processing of their outputs. Events
are read through `Pr{…}`, so no measurable structure is needed on the outputs themselves.
Measurable post-processing never increases total variation.
-/

public section

open MeasureTheory
open scoped ENNReal

universe v

variable {m : Type → Type v} [Monad m] [LawfulMonad m] [EvalDistSemantics m]
  [LawfulEvalDistSemantics m] {α β : Type}

/-- Measurable post-processing of both computations cannot increase total variation. -/
theorem measureETVDist_map_le [MeasurableSpace α] [MeasurableSpace β] (mx my : m α) (f : α → β)
    (hf : Measurable f) : measureETVDist (f <$> mx) (f <$> my) ≤ measureETVDist mx my := by
  simp only [measureETVDist, evalDist_map mx hf, evalDist_map my hf]
  exact Measure.etvDist_map_le _ _ f hf

/-- Computations that agree on every event away from a bad event are, after any post-processing,
within the bad event's probability in total variation. -/
theorem measureETVDist_map_le_prEvent_of_agree [MeasurableSpace β] (mx my : m α) (f : α → β)
    (bad : α → Prop)
    (hagree : ∀ p : α → Prop,
      Pr{let x ← mx}[p x ∧ ¬bad x] = Pr{let y ← my}[p y ∧ ¬bad y])
    (hbad : Pr{let y ← my}[bad y] ≤ Pr{let x ← mx}[bad x]) :
    measureETVDist (f <$> mx) (f <$> my) ≤ Pr{let x ← mx}[bad x] := by
  refine iSup_le fun A => ?_
  have hsplit (mz : m α) : 𝒟[f <$> mz] A.1 =
      Pr{let x ← mz}[f x ∈ A.1 ∧ bad x] + Pr{let x ← mz}[f x ∈ A.1 ∧ ¬bad x] := by
    have h := prEvent_eq_evalDist (f <$> mz) (· ∈ A.1) A.2.mem
    rw [Set.ofPred_mem_eq] at h
    rw [← h, prEvent_map, prEvent_eq_prEvent_and_add_prEvent_and_not _ _ bad]
  rw [hsplit mx, hsplit my, hagree fun x => f x ∈ A.1]
  have h₁ : Pr{let x ← mx}[f x ∈ A.1 ∧ bad x] ≤ Pr{let x ← mx}[bad x] :=
    prEvent_mono mx _ _ fun _ hx => hx.2
  have h₂ : Pr{let y ← my}[f y ∈ A.1 ∧ bad y] ≤ Pr{let x ← mx}[bad x] :=
    (prEvent_mono my _ _ fun _ hy => hy.2).trans hbad
  refine ENNReal.absDiff_le_iff.2 ⟨?_, ?_⟩
  · calc _ ≤ Pr{let x ← mx}[bad x] + Pr{let y ← my}[f y ∈ A.1 ∧ ¬bad y] := add_le_add h₁ le_rfl
      _ ≤ _ := by rw [add_comm]; exact add_le_add le_add_self le_rfl
  · calc _ ≤ Pr{let x ← mx}[bad x] + Pr{let y ← my}[f y ∈ A.1 ∧ ¬bad y] := add_le_add h₂ le_rfl
      _ ≤ _ := by rw [add_comm]; exact add_le_add le_add_self le_rfl
