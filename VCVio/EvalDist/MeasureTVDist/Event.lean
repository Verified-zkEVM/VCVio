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
Measurable post-processing never increases total variation, and total variation bounds how much
more likely a measurable event can be under one computation than under the other.
-/

public section

open MeasureTheory
open scoped ENNReal

universe v

variable {m : Type → Type v} [Monad m] [LawfulMonad m] [EvalDistSemantics m]
  [LawfulEvalDistSemantics m] {α β : Type}

/-- An event is at most as likely as under another computation plus their extended total
variation. -/
theorem prEvent_le_prEvent_add_measureETVDist [MeasurableSpace α] (mx my : m α) (p : α → Prop)
    (hp : Measurable p) :
    Pr{let x ← mx}[p x] ≤ Pr{let y ← my}[p y] + measureETVDist mx my := by
  rw [prEvent_eq_evalDist mx p hp, prEvent_eq_evalDist my p hp]
  exact (ENNReal.absDiff_le_iff.1
    (measure_absDiff_apply_le_measureETVDist mx my (measurableSet_setOfPred.2 hp))).1

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

/-- **Post-processing through a public view.** Suppose the first computation's outputs are read
through a public view `pub`, and the two post-processings agree whenever that view is a good
output of the second computation: `fa a = fb b` when `pub a = b` and `b` is not bad. The
post-processed runs are then within the total variation of the public views plus the second
computation's bad mass. -/
theorem measureETVDist_map_le_map_add_prEvent_bad {γ : Type}
    [MeasurableSpace α] [DiscreteMeasurableSpace α] [MeasurableSpace β] [DiscreteMeasurableSpace β]
    [MeasurableSpace γ]
    (oa : m α) (ob : m β) (pub : α → β) (fa : α → γ) (fb : β → γ) (bad : β → Prop)
    (h_eq : ∀ a b, pub a = b → ¬ bad b → fa a = fb b) :
    measureETVDist (fa <$> oa) (fb <$> ob) ≤
      measureETVDist (pub <$> oa) ob + Pr{let y ← ob}[bad y] := by
  refine iSup_le fun A => ?_
  set T := measureETVDist (pub <$> oa) ob
  let Bd : Set β := {b | bad b}
  let G : Set β := {b | ¬ bad b ∧ fb b ∈ A.1}
  have hT (S : Set β) : ENNReal.absDiff (𝒟[pub <$> oa] S) (𝒟[ob] S) ≤ T :=
    measure_absDiff_apply_le_measureETVDist _ _ MeasurableSet.of_discrete
  have hbad : Pr{let y ← ob}[bad y] = 𝒟[ob] Bd := prEvent_eq_evalDist_of_discrete ob bad
  have hfa : 𝒟[fa <$> oa] A.1 = 𝒟[oa] (fa ⁻¹' A.1) := by
    rw [evalDist_map oa Measurable.of_discrete, Measure.map_apply Measurable.of_discrete A.2]
  have hfb : 𝒟[fb <$> ob] A.1 = 𝒟[ob] (fb ⁻¹' A.1) := by
    rw [evalDist_map ob Measurable.of_discrete, Measure.map_apply Measurable.of_discrete A.2]
  have hpub (S : Set β) : 𝒟[pub <$> oa] S = 𝒟[oa] (pub ⁻¹' S) := by
    rw [evalDist_map oa Measurable.of_discrete,
      Measure.map_apply Measurable.of_discrete MeasurableSet.of_discrete]
  -- The first run's mass of `A` is squeezed between the public masses of `G` and `G ∪ Bd`.
  have hlo : 𝒟[pub <$> oa] G ≤ 𝒟[fa <$> oa] A.1 := by
    rw [hpub, hfa]
    exact measure_mono fun a ha => show fa a ∈ A.1 from (h_eq a (pub a) rfl ha.1) ▸ ha.2
  have hhi : 𝒟[fa <$> oa] A.1 ≤ 𝒟[pub <$> oa] (G ∪ Bd) := by
    rw [hpub, hfa]
    refine measure_mono fun a ha => ?_
    by_cases hb : bad (pub a)
    · exact Or.inr hb
    · exact Or.inl ⟨hb, show fb (pub a) ∈ A.1 from (h_eq a (pub a) rfl hb) ▸ ha⟩
  -- The second run's mass of `A` is squeezed between its masses of `G` and `G ∪ Bd`.
  have hlo' : 𝒟[ob] G ≤ 𝒟[fb <$> ob] A.1 := by
    rw [hfb]
    exact measure_mono fun b hb => hb.2
  have hhi' : 𝒟[fb <$> ob] A.1 ≤ 𝒟[ob] G + 𝒟[ob] Bd := by
    rw [hfb]
    refine (measure_mono fun b hb => ?_).trans (measure_union_le G Bd)
    by_cases hbb : bad b
    · exact Or.inr hbb
    · exact Or.inl ⟨hbb, hb⟩
  rw [hbad]
  refine ENNReal.absDiff_le_iff.2 ⟨?_, ?_⟩
  · calc 𝒟[fa <$> oa] A.1 ≤ 𝒟[pub <$> oa] (G ∪ Bd) := hhi
      _ ≤ 𝒟[ob] (G ∪ Bd) + T := (ENNReal.absDiff_le_iff.1 (hT _)).1
      _ ≤ (𝒟[ob] G + 𝒟[ob] Bd) + T := add_le_add (measure_union_le G Bd) le_rfl
      _ ≤ (𝒟[fb <$> ob] A.1 + 𝒟[ob] Bd) + T := add_le_add (add_le_add hlo' le_rfl) le_rfl
      _ = 𝒟[fb <$> ob] A.1 + (T + 𝒟[ob] Bd) := by ring
  · calc 𝒟[fb <$> ob] A.1 ≤ 𝒟[ob] G + 𝒟[ob] Bd := hhi'
      _ ≤ (𝒟[pub <$> oa] G + T) + 𝒟[ob] Bd :=
        add_le_add (ENNReal.absDiff_le_iff.1 (hT _)).2 le_rfl
      _ ≤ (𝒟[fa <$> oa] A.1 + T) + 𝒟[ob] Bd := add_le_add (add_le_add hlo le_rfl) le_rfl
      _ = 𝒟[fa <$> oa] A.1 + (T + 𝒟[ob] Bd) := by ring
