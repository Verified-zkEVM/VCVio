/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.CryptoFoundations.SymmEncAlg.Defs
public import VCVio.EvalDist.MeasureSemantics

/-!
# Measure and kernel security for symmetric encryption

This module interprets the probability-independent symmetric-encryption experiments through a
`ProbabilitySemantics`. Correctness is equality with a Dirac measure. Perfect secrecy is equality of
the ciphertext-channel rows for every pair of messages, packaged as a Mathlib Markov kernel when
the row family is measurable.

The definitions do not select a discrete probability representation and do not assume that an
arbitrary monad is efficient. They isolate the semantic claim that concrete complexity proofs can
compose with separately.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

universe v

namespace SymmEncAlg

variable {m : Type → Type v} [Monad m] {M K C : Type}

/-! ## Correctness -/

/-- The round-trip experiment as a kernel from messages to decrypted outputs. -/
noncomputable def completeKernel [MeasurableSpace M]
    (semantics : ProbabilitySemantics m) (encAlg : SymmEncAlg m M K C)
    (hMeasurable : Measurable fun msg ↦ semantics.denote (encAlg.CompleteExp msg)) :
    Kernel M (Option M) :=
  ⟨fun msg ↦ semantics.denote (encAlg.CompleteExp msg), hMeasurable⟩

@[simp]
theorem completeKernel_apply [MeasurableSpace M]
    (semantics : ProbabilitySemantics m) (encAlg : SymmEncAlg m M K C)
    (hMeasurable : Measurable fun msg ↦ semantics.denote (encAlg.CompleteExp msg))
    (msg : M) :
    encAlg.completeKernel semantics hMeasurable msg =
      semantics.denote (encAlg.CompleteExp msg) := rfl

instance isMarkovKernel_completeKernel [MeasurableSpace M]
    (semantics : ProbabilitySemantics m) (encAlg : SymmEncAlg m M K C)
    (hMeasurable : Measurable fun msg ↦ semantics.denote (encAlg.CompleteExp msg)) :
    IsMarkovKernel (encAlg.completeKernel semantics hMeasurable) where
  isProbabilityMeasure msg := semantics.isProbabilityMeasure (encAlg.CompleteExp msg)

/-- Measure-level perfect correctness: every round trip has the Dirac law at the input message. -/
def measureComplete [MeasurableSpace M]
    (encAlg : SymmEncAlg m M K C) (semantics : ProbabilitySemantics m) : Prop :=
  ∀ msg, semantics.denote (encAlg.CompleteExp msg) = Measure.dirac (some msg)

/-- Kernel form of measure-level perfect correctness. -/
theorem measureComplete_iff_completeKernel_eq_dirac [MeasurableSpace M]
    (encAlg : SymmEncAlg m M K C) (semantics : ProbabilitySemantics m)
    (hMeasurable : Measurable fun msg ↦ semantics.denote (encAlg.CompleteExp msg)) :
    encAlg.measureComplete semantics ↔
      ∀ msg, encAlg.completeKernel semantics hMeasurable msg = Measure.dirac (some msg) :=
  Iff.rfl

/-! ## Perfect secrecy -/

/-- The fixed-message ciphertext experiment as a channel from messages to ciphertexts. -/
noncomputable def perfectSecrecyCipherKernel [MeasurableSpace M] [MeasurableSpace C]
    (semantics : ProbabilitySemantics m) (encAlg : SymmEncAlg m M K C)
    (hMeasurable : Measurable fun msg ↦
      semantics.denote (encAlg.PerfectSecrecyCipherGivenMsgExp msg)) :
    Kernel M C :=
  ⟨fun msg ↦ semantics.denote (encAlg.PerfectSecrecyCipherGivenMsgExp msg), hMeasurable⟩

@[simp]
theorem perfectSecrecyCipherKernel_apply [MeasurableSpace M] [MeasurableSpace C]
    (semantics : ProbabilitySemantics m) (encAlg : SymmEncAlg m M K C)
    (hMeasurable : Measurable fun msg ↦
      semantics.denote (encAlg.PerfectSecrecyCipherGivenMsgExp msg))
    (msg : M) :
    encAlg.perfectSecrecyCipherKernel semantics hMeasurable msg =
      semantics.denote (encAlg.PerfectSecrecyCipherGivenMsgExp msg) := rfl

instance isMarkovKernel_perfectSecrecyCipherKernel
    [MeasurableSpace M] [MeasurableSpace C]
    (semantics : ProbabilitySemantics m) (encAlg : SymmEncAlg m M K C)
    (hMeasurable : Measurable fun msg ↦
      semantics.denote (encAlg.PerfectSecrecyCipherGivenMsgExp msg)) :
    IsMarkovKernel (encAlg.perfectSecrecyCipherKernel semantics hMeasurable) where
  isProbabilityMeasure msg :=
    semantics.isProbabilityMeasure (encAlg.PerfectSecrecyCipherGivenMsgExp msg)

/-- Measure-level perfect secrecy: every pair of messages induces the same ciphertext measure. -/
def measurePerfectSecrecyAt [MeasurableSpace C]
    (encAlg : SymmEncAlg m M K C) (semantics : ProbabilitySemantics m) : Prop :=
  ∀ msg₀ msg₁,
    semantics.denote (encAlg.PerfectSecrecyCipherGivenMsgExp msg₀) =
      semantics.denote (encAlg.PerfectSecrecyCipherGivenMsgExp msg₁)

/-- Kernel-row form of measure-level perfect secrecy. -/
theorem measurePerfectSecrecyAt_iff_kernel_rows_eq [MeasurableSpace M] [MeasurableSpace C]
    (encAlg : SymmEncAlg m M K C) (semantics : ProbabilitySemantics m)
    (hMeasurable : Measurable fun msg ↦
      semantics.denote (encAlg.PerfectSecrecyCipherGivenMsgExp msg)) :
    encAlg.measurePerfectSecrecyAt semantics ↔
      ∀ msg₀ msg₁,
        encAlg.perfectSecrecyCipherKernel semantics hMeasurable msg₀ =
          encAlg.perfectSecrecyCipherKernel semantics hMeasurable msg₁ :=
  Iff.rfl

/-- A ciphertext law independent of the message establishes measure-level perfect secrecy. -/
theorem measurePerfectSecrecyAt_of_constant [MeasurableSpace C]
    (encAlg : SymmEncAlg m M K C) (semantics : ProbabilitySemantics m) (law : Measure C)
    (hlaw : ∀ msg, semantics.denote (encAlg.PerfectSecrecyCipherGivenMsgExp msg) = law) :
    encAlg.measurePerfectSecrecyAt semantics := by
  intro msg₀ msg₁
  rw [hlaw msg₀, hlaw msg₁]

end SymmEncAlg
