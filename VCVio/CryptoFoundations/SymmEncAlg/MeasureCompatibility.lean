/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: VCVio Contributors
-/

module

public import VCVio.CryptoFoundations.SymmEncAlg
public import VCVio.CryptoFoundations.SymmEncAlg.Measure

/-!
# Compatibility between measure and point-probability symmetric-encryption predicates

These bridges keep the measure-native API and the legacy discrete API separate while recording
their exact agreement when both semantics assign the same mass to singleton events.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

universe v

namespace SymmEncAlg

variable {m : Type → Type v} [Monad m] {M K C : Type}

/-- A probability measure on a countable space is a Dirac mass exactly when the distinguished
singleton has mass one. -/
private theorem probabilityMeasure_eq_dirac_iff_apply_singleton_eq_one
    {α : Type} [MeasurableSpace α] [MeasurableSingletonClass α] [Countable α]
    (μ : Measure α) [IsProbabilityMeasure μ] (point : α) :
    μ = Measure.dirac point ↔ μ {point} = 1 := by
  let _ : DecidableEq α := Classical.decEq α
  constructor
  · intro h
    rw [h]
    simp
  · intro hpoint
    apply Measure.ext_of_singleton
    intro value
    by_cases hvalue : value = point
    · subst value
      simpa using hpoint
    · have hcomplement : μ ({point}ᶜ) = 0 := by
        rw [measure_compl (measurableSet_singleton point) (by simp [hpoint])]
        simp [hpoint]
      have hzero : μ {value} = 0 :=
        measure_mono_null (by
          simpa [Set.singleton_subset_iff] using Ne.symm hvalue) hcomplement
      simp [hvalue, hzero]

/-- Measure-level and point-probability correctness agree under singleton coherence. -/
theorem measureComplete_iff_complete [MeasurableSpace M] [MeasurableSingletonClass M]
    [Countable M] [MonadLiftT m PMF] [LawfulMonadLiftT m PMF]
    (encAlg : SymmEncAlg m M K C) (semantics : ProbabilitySemantics m)
    (hsingleton : ∀ (msg : M) (value : Option M),
      semantics.denote (encAlg.CompleteExp msg) {value} =
        Pr[= value | encAlg.CompleteExp msg]) :
    encAlg.measureComplete semantics ↔ encAlg.Complete := by
  constructor
  · intro hmeasure msg
    have heq := congrArg (fun μ : Measure (Option M) ↦ μ {some msg}) (hmeasure msg)
    simpa [hsingleton msg (some msg)] using heq
  · intro hcomplete msg
    let _ := semantics.isProbabilityMeasure (encAlg.CompleteExp msg)
    apply (probabilityMeasure_eq_dirac_iff_apply_singleton_eq_one
      (semantics.denote (encAlg.CompleteExp msg)) (some msg)).2
    rw [hsingleton]
    exact hcomplete msg

/-- Measure-level and pointwise ciphertext-row secrecy agree under singleton coherence. -/
theorem measurePerfectSecrecyAt_iff_ciphertextRowsEqualAt
    [MeasurableSpace C] [MeasurableSingletonClass C] [Countable C]
    [MonadLiftT m PMF] [LawfulMonadLiftT m PMF]
    [MonadLiftT m SetM] [EvalDistCompatible m]
    (encAlg : SymmEncAlg m M K C) (semantics : ProbabilitySemantics m)
    (hsingleton : ∀ (msg : M) (ciphertext : C),
      semantics.denote (encAlg.PerfectSecrecyCipherGivenMsgExp msg) {ciphertext} =
        Pr[= ciphertext | encAlg.PerfectSecrecyCipherGivenMsgExp msg]) :
    encAlg.measurePerfectSecrecyAt semantics ↔ encAlg.ciphertextRowsEqualAt := by
  constructor
  · intro hmeasure msg₀ msg₁ ciphertext
    have heq := congrArg (fun μ : Measure C ↦ μ {ciphertext}) (hmeasure msg₀ msg₁)
    simpa [hsingleton] using heq
  · intro hrows msg₀ msg₁
    apply Measure.ext_of_singleton
    intro ciphertext
    rw [hsingleton, hsingleton]
    exact hrows msg₀ msg₁ ciphertext

end SymmEncAlg
