/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Interval.Scheme
public import HashSig.GXMSS.Completeness

/-! # Correctness restricted to active epochs -/

public section

namespace GXMSS.Interval

open Encoding ENNReal GXMSS.IntervalMerkle

variable {PP T X H M R : Type} {h w v : ℕ}

/-- Every generated interval key satisfies the mixed-root and complete-chain equations. -/
theorem consistent_generated [SampleableType H] [SampleableType R] [DecidableEq H]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K : ℕ)
    (I : Interval h) (ks : PublicKey PP H × SecretKey PP H h v I)
    (hks : (scheme hash enc K I).Generated ProbCompRuntime.probComp ks) :
    Consistent hash I ks.1 ks.2 := by
  rw [SyncSignatureAlg.Generated, ProbCompRuntime.probComp_evalDist,
    ← prEvent_eq_evalDist_map] at hks
  obtain ⟨_, hmem, rfl⟩ := (OracleComp.prEvent_pos_iff _ _).mp hks
  simp only [scheme, keygen, mem_support_bind_iff, support_pure,
    Set.mem_singleton_iff] at hmem
  obtain ⟨pp, _, starts, _, fillers, _, rfl⟩ := hmem
  exact consistent_keys hash I pp starts fillers

/-- At an active epoch, honest signing accepts exactly the successful retry outputs. -/
theorem successMass_eq_retry_isActive [SampleableType H] [SampleableType R] [DecidableEq H]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K : ℕ)
    (I : Interval h) (ks : PublicKey PP H × SecretKey PP H h v I)
    (hc : Consistent hash I ks.1 ks.2) (ep : Fin (2 ^ h)) (he : Epoch.IsActive I ep)
    (msg : M) :
    (scheme hash enc K I).successMass ProbCompRuntime.probComp ks ep msg =
      IncomparableEncoding.Retry.successMass enc ProbCompRuntime.probComp ($ᵗ R)
        ks.2.complete.seed msg ep K := by
  classical
  let _ : MeasurableSpace (Option (Codeword v (2 ^ w) × R)) := ⊤
  let _ : DiscreteMeasurableSpace (Option (Codeword v (2 ^ w) × R)) := ⟨fun _ => trivial⟩
  simp only [SyncSignatureAlg.successMass, IncomparableEncoding.Retry.successMass,
    IncomparableEncoding.Retry.failureIndicatorDist, ProbCompRuntime.probComp_evalDist,
    scheme, sign, ite_eq_left he, Functor.map_map]
  rw [evalDist_map _ Measurable.of_discrete,
    evalDist_map _ Measurable.of_discrete,
    MeasureTheory.Measure.map_apply Measurable.of_discrete (measurableSet_singleton true),
    MeasureTheory.Measure.map_apply Measurable.of_discrete (measurableSet_singleton false)]
  apply MeasureTheory.measure_congr
  apply evalDist.ae_of_forall_mem_support
  · exact MeasurableSet.of_discrete
  intro o ho
  cases o with
  | none => simp [SyncSignatureAlg.accepts]
  | some wr =>
      have hv := IncomparableEncoding.Retry.value_eq_some_of_mem_retry enc
        ($ᵗ R) ks.2.complete.seed msg ep K wr.1 wr.2 ho
      have ha := verify_signatureOfWord_isActive hash enc I ks.1 ks.2 hc ep he msg wr hv
      simp [SyncSignatureAlg.accepts, ha]

/-- At an active epoch the exact correctness loss is independent retry exhaustion. -/
theorem successMass_eq_one_sub_pow_isActive
    [SampleableType H] [SampleableType R] [DecidableEq H]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K : ℕ)
    (I : Interval h) (ks : PublicKey PP H × SecretKey PP H h v I)
    (hc : Consistent hash I ks.1 ks.2) (ep : Fin (2 ^ h)) (he : Epoch.IsActive I ep)
    (msg : M) :
    (scheme hash enc K I).successMass ProbCompRuntime.probComp ks ep msg =
      1 - (enc.failureMass ProbCompRuntime.probComp ($ᵗ R) ks.2.complete.seed msg ep) ^ K := by
  rw [successMass_eq_retry_isActive hash enc K I ks hc ep he]
  exact IncomparableEncoding.Retry.successMass_eq_one_sub_pow enc ProbCompRuntime.probComp
    samplingLaws_probComp ($ᵗ R) (by unfold LosslessSampler; simp) ks.2.complete.seed msg ep K

/-- Inactive epochs have zero success mass because signing returns explicit failure. -/
theorem successMass_not_isActive [SampleableType H] [SampleableType R] [DecidableEq H]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K : ℕ)
    (I : Interval h) (ks : PublicKey PP H × SecretKey PP H h v I)
    (ep : Fin (2 ^ h)) (he : ¬ Epoch.IsActive I ep) (msg : M) :
    (scheme hash enc K I).successMass ProbCompRuntime.probComp ks ep msg = 0 := by
  simp [SyncSignatureAlg.successMass, scheme, sign_not_isActive hash enc K I ks.2 ep msg he,
    SyncSignatureAlg.accepts]

/-- Uniform encoding error gives per-generated-key correctness on the captured active interval.
The result includes zero retries and keeps unrestricted verification unchanged. -/
theorem complete_isActive [SampleableType H] [SampleableType R] [Fintype R] [DecidableEq H]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K : ℕ)
    (I : Interval h) (δ : ℝ≥0∞)
    (he : enc.UniformErrorAtMost ProbCompRuntime.probComp ($ᵗ R) δ) :
    (scheme hash enc K I).CompleteOn ProbCompRuntime.probComp (Epoch.IsActive I) (δ ^ K) := by
  intro ks hks ep hactive msg
  rw [successMass_eq_one_sub_pow_isActive hash enc K I ks
    (consistent_generated hash enc K I ks hks) ep hactive]
  exact tsub_le_tsub_left (pow_le_pow_left' (he.2.2 ks.2.complete.seed msg ep) K) 1

/-- At full range, active-epoch correctness supplies ordinary all-epoch correctness. -/
theorem complete_full [SampleableType H] [SampleableType R] [Fintype R] [DecidableEq H]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K : ℕ) (δ : ℝ≥0∞)
    (he : enc.UniformErrorAtMost ProbCompRuntime.probComp ($ᵗ R) δ) :
    (scheme hash enc K (Interval.full h)).Complete ProbCompRuntime.probComp (δ ^ K) := by
  intro ks hks ep msg
  exact complete_isActive hash enc K (Interval.full h) δ he ks hks ep (Epoch.isActive_full ep) msg

end GXMSS.Interval
