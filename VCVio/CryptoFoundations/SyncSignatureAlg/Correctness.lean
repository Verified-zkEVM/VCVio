/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import VCVio.CryptoFoundations.SyncSignatureAlg.Basic
import VCVio.OracleComp.EvalDist.Measure

/-!
# Joint and per-key correctness

The canonical discrete `ProbComp` runtime gives every reachable key positive probability and
preserves total key-generation mass. These facts transport per-key correctness to the joint
experiment. Arbitrary probability runtimes require separate sampling and generated-key laws.
-/

public section

namespace SyncSignatureAlg

open ENNReal MeasureTheory OracleComp

universe v

variable {m : Type → Type v} [Monad m] {M PK SK S E : Type}

/-- The joint successful-output probability is at most one. -/
theorem jointSuccessMass_le_one (alg : SyncSignatureAlg m M PK SK S E)
    (runtime : ProbCompRuntime m) (ep : E) (msg : M) :
    alg.jointSuccessMass runtime ep msg ≤ 1 :=
  (measure_mono (Set.subset_univ _)).trans (runtime.evalDist_apply_univ_le_one _)

/-- Joint correctness on every epoch is unrestricted joint correctness. -/
theorem completeOn_true_iff (alg : SyncSignatureAlg m M PK SK S E)
    (runtime : ProbCompRuntime m) (δ : ℝ≥0∞) :
    alg.CompleteOn runtime (fun _ => True) δ ↔ alg.Complete runtime δ := by
  simp only [CompleteOn, Complete, forall_const]

/-- Joint correctness bounds the actual key-generation/signing/verification execution. -/
theorem complete_iff (alg : SyncSignatureAlg m M PK SK S E)
    (runtime : ProbCompRuntime m) (δ : ℝ≥0∞) :
    alg.Complete runtime δ ↔ ∀ ep msg,
      1 - δ ≤ runtime.evalDist (alg.correctnessExperiment ep msg) {true} := Iff.rfl

/-- Increasing the joint error allowance preserves correctness. -/
theorem Complete.mono {alg : SyncSignatureAlg m M PK SK S E}
    {runtime : ProbCompRuntime m} {δ₁ δ₂ : ℝ≥0∞}
    (h : alg.Complete runtime δ₁) (hle : δ₁ ≤ δ₂) : alg.Complete runtime δ₂ :=
  fun ep msg => (tsub_le_tsub_left hle 1).trans (h ep msg)

/-- Zero joint error is exactly unit acceptance mass at every epoch and message. -/
theorem complete_zero_iff (alg : SyncSignatureAlg m M PK SK S E)
    (runtime : ProbCompRuntime m) :
    alg.Complete runtime 0 ↔ ∀ ep msg, alg.jointSuccessMass runtime ep msg = 1 := by
  constructor
  · intro h ep msg
    exact le_antisymm (alg.jointSuccessMass_le_one runtime ep msg) (by simpa using h ep msg)
  · intro h ep msg
    simpa using (h ep msg).ge

/-- In the canonical discrete runtime, generated keys are exactly reachable keys. -/
theorem generated_probComp_iff_mem_support (alg : SyncSignatureAlg ProbComp M PK SK S E)
    (ks : PK × SK) :
    alg.Generated ProbCompRuntime.probComp ks ↔ ks ∈ support alg.keygen := by
  simp [Generated, ProbCompRuntime.probComp_evalDist, prEvent_pos_iff]

/-- Canonical joint acceptance integrates the fixed-key acceptance probabilities. -/
theorem jointSuccessMass_probComp_eq_lintegral
    (alg : SyncSignatureAlg ProbComp M PK SK S E) (ep : E) (msg : M) :
    alg.jointSuccessMass ProbCompRuntime.probComp ep msg =
      let : MeasurableSpace (PK × SK) := ⊤
      ∫⁻ ks, alg.successMass ProbCompRuntime.probComp ks ep msg ∂𝒟[alg.keygen] := by
  let : MeasurableSpace (PK × SK) := ⊤
  simp only [jointSuccessMass, correctnessExperiment, ProbCompRuntime.probComp_evalDist,
    evalDist_bind_of_discrete]
  rw [Measure.bind_apply (measurableSet_singleton true) Measurable.of_discrete.aemeasurable]
  rfl

/-- A lower bound at every generated key bounds canonical joint acceptance. -/
theorem jointSuccessMass_probComp_ge_of_perKey
    (alg : SyncSignatureAlg ProbComp M PK SK S E) (ep : E) (msg : M) (bound : ℝ≥0∞)
    (h : ∀ ks, alg.Generated ProbCompRuntime.probComp ks →
      bound ≤ alg.successMass ProbCompRuntime.probComp ks ep msg) :
    bound ≤ alg.jointSuccessMass ProbCompRuntime.probComp ep msg := by
  let : MeasurableSpace (PK × SK) := ⊤
  rw [jointSuccessMass_probComp_eq_lintegral]
  calc
    bound = ∫⁻ _ : PK × SK, bound ∂𝒟[alg.keygen] := by simp
    _ ≤ _ := lintegral_mono_ae <| ae_evalDist_of_forall_mem_support alg.keygen
      fun ks hks => h ks ((alg.generated_probComp_iff_mem_support ks).2 hks)

/-- Per-key correctness implies joint correctness in the canonical discrete runtime. -/
theorem CompletePerKey.complete {alg : SyncSignatureAlg ProbComp M PK SK S E} {δ : ℝ≥0∞}
    (h : alg.CompletePerKey ProbCompRuntime.probComp δ) :
    alg.Complete ProbCompRuntime.probComp δ :=
  fun ep msg => alg.jointSuccessMass_probComp_ge_of_perKey ep msg _
    fun ks hks => h ks hks ep msg

/-- Active per-key correctness implies active joint correctness in the canonical runtime. -/
theorem CompleteOnPerKey.completeOn {alg : SyncSignatureAlg ProbComp M PK SK S E}
    {active : E → Prop} {δ : ℝ≥0∞}
    (h : alg.CompleteOnPerKey ProbCompRuntime.probComp active δ) :
    alg.CompleteOn ProbCompRuntime.probComp active δ :=
  fun ep hep msg => alg.jointSuccessMass_probComp_ge_of_perKey ep msg _
    fun ks hks => h ks hks ep hep msg

end SyncSignatureAlg
