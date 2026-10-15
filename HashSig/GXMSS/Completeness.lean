/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Scheme

/-!
# Correctness of generalized XMSS

Generated-key consistency and the composition of chain completion with honest Merkle recovery
for Construction 3 of ePrint 2025/055. Returned exhaustion retains its full probability mass.
-/

public section

namespace GXMSS

open Encoding ENNReal

variable {PP T X H M R : Type} {h w v : ℕ}

/-- Seeds agree, stored endpoints are full chains, and the public root authenticates them. -/
@[expose] def Consistent (hash : HashInstance PP T X H h w v)
    (pk : PublicKey PP H) (sk : SecretKey PP H h v) : Prop :=
  pk.seed = sk.seed ∧ sk.endpoints = endpoints hash sk.seed sk.starts ∧
    pk.root = hash.merkleRoot sk.seed sk.endpoints

/-- Every deterministic key assembly satisfies all three consistency equations. -/
theorem consistent_keys (hash : HashInstance PP T X H h w v) (pp : PP)
    (starts : Fin (2 ^ h) → Fin v → H) :
    Consistent hash (keys hash pp starts).1 (keys hash pp starts).2 := by
  simp [Consistent, keys]

/-- Each full start array has the product of its independent coordinate masses. -/
theorem sampleStarts_probability [SampleableType H] (starts : Fin (2 ^ h) → Fin v → H) :
    Pr{let sampled ← sampleStarts H h v}[sampled = starts] =
      ∏ ep, ∏ i, Pr{let x ← $ᵗ H}[x = starts ep i] := by
  simp only [sampleStarts]
  rw [prEvent_eq_mOfFn]
  apply Finset.prod_congr rfl
  intro ep _
  rw [prEvent_eq_mOfFn]

/-- Finite start coordinates each have uniform inverse-cardinality mass, independently. -/
theorem sampleStarts_uniform_probability [SampleableType H] [Fintype H]
    (starts : Fin (2 ^ h) → Fin v → H) :
    Pr{let sampled ← sampleStarts H h v}[sampled = starts] =
      ∏ _ep : Fin (2 ^ h), ∏ _i : Fin v, (Fintype.card H : ℝ≥0∞)⁻¹ := by
  rw [sampleStarts_probability]
  simp_rw [SampleableType.prEvent_uniformSample_eq_singleton]

/-- Independent finite start sampling has no missing mass, including empty OTS vectors. -/
theorem sampleStarts_lossless [SampleableType H] :
    LosslessSampler ProbCompRuntime.probComp (sampleStarts H h v) := by
  rw [LosslessSampler, ProbCompRuntime.probComp_evalDist, ← prEvent_eq_evalDist_map]
  exact OracleComp.prEvent_true_eq_one _

/-- Key generation is lossless whenever its existing public-seed sampler is lossless. -/
theorem keygen_lossless [SampleableType H] (hash : HashInstance PP T X H h w v)
    (_hs : LosslessSampler ProbCompRuntime.probComp (HashInstance.thf hash).seedGen) :
    LosslessSampler ProbCompRuntime.probComp (keygen hash) := by
  rw [LosslessSampler, ProbCompRuntime.probComp_evalDist, ← prEvent_eq_evalDist_map]
  exact OracleComp.prEvent_true_eq_one _

/-- The paper's uniformity law on the existing seed sampler ensures lossless key generation. -/
theorem keygen_lossless_of_uniform [SampleableType H] [Fintype PP]
    (hash : HashInstance PP T X H h w v)
    (hs : UniformSampler ProbCompRuntime.probComp (HashInstance.thf hash).seedGen) :
    LosslessSampler ProbCompRuntime.probComp (keygen hash) := keygen_lossless hash hs.1

/-- Every runtime-producible key pair satisfies the raw-key consistency invariant. -/
theorem consistent_generated [SampleableType H] [SampleableType R] [DecidableEq H]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K : ℕ)
    (ks : PublicKey PP H × SecretKey PP H h v)
    (hks : (scheme hash enc K).Generated ProbCompRuntime.probComp ks) :
    Consistent hash ks.1 ks.2 := by
  rw [SyncSignatureAlg.Generated, ProbCompRuntime.probComp_evalDist,
    ← prEvent_eq_evalDist_map] at hks
  obtain ⟨_, hmem, rfl⟩ := (OracleComp.prEvent_pos_iff _ _).mp hks
  simp only [scheme, keygen, mem_support_bind_iff, support_pure,
    Set.mem_singleton_iff] at hmem
  obtain ⟨pp, _, starts, _, rfl⟩ := hmem
  exact consistent_keys hash pp starts

/-- An attacker-supplied signature is rejected whenever its randomizer fails to encode. -/
theorem verify_eq_false_of_encoding_failure [DecidableEq H]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (pk : PublicKey PP H) (ep : Fin (2 ^ h)) (msg : M) (sig : Signature R H h v)
    (hf : enc.value pk.seed msg sig.randomizer ep = none) :
    verify hash enc pk ep msg sig = false := by
  simp [verify, hf]

/-- A successful word/randomizer pair gives a verifying signature for every consistent key. -/
theorem verify_signatureOfWord [DecidableEq H] (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (pk : PublicKey PP H) (sk : SecretKey PP H h v) (hc : Consistent hash pk sk)
    (ep : Fin (2 ^ h)) (msg : M) (wr : Codeword v (2 ^ w) × R)
    (hw : enc.value sk.seed msg wr.2 ep = some wr.1) :
    verify hash enc pk ep msg (signatureOfWord hash sk ep wr) = true := by
  rcases hc with ⟨hseed, hend, hroot⟩
  have hchains : (fun i => hash.chain sk.seed ep i (wr.1 i)
      (2 ^ w - 1 - (wr.1 i).val)
      (hash.chain sk.seed ep i 0 (wr.1 i) (sk.starts ep i))) = sk.endpoints ep := by
    funext i
    rw [hash.chain_complete_digit, hend]
    rfl
  simp only [verify, signatureOfWord, hseed, hw]
  rw [hchains, hash.recoverRoot_authPath, hroot]
  simp

/-- Zero retries return failure without sampling or hashing. -/
theorem sign_zero [SampleableType R] (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (sk : SecretKey PP H h v) (ep : Fin (2 ^ h)) (msg : M) :
    sign hash enc 0 sk ep msg = pure none := by
  simp [sign, IncomparableEncoding.retry_zero]

/-- Every honest returned signature contributes exactly the successful retry mass.
The observation is applied after the canonical runtime evaluates signing. -/
theorem successMass_eq_retry [SampleableType H] [SampleableType R] [DecidableEq H]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K : ℕ)
    (ks : PublicKey PP H × SecretKey PP H h v) (hc : Consistent hash ks.1 ks.2)
    (ep : Fin (2 ^ h)) (msg : M) :
    (scheme hash enc K).successMass ProbCompRuntime.probComp ks ep msg =
      let secretKey := ks.2
      IncomparableEncoding.Retry.successMass enc ProbCompRuntime.probComp ($ᵗ R)
        secretKey.seed msg ep K := by
  classical
  dsimp
  let secretKey := ks.2
  let _ : MeasurableSpace (Option (Codeword v (2 ^ w) × R)) := ⊤
  let _ : DiscreteMeasurableSpace (Option (Codeword v (2 ^ w) × R)) :=
    ⟨fun _ => trivial⟩
  simp only [SyncSignatureAlg.successMass, IncomparableEncoding.Retry.successMass,
    IncomparableEncoding.Retry.failureIndicatorDist, ProbCompRuntime.probComp_evalDist,
    scheme, sign, Functor.map_map]
  rw [evalDist_map _ Measurable.of_discrete, evalDist_map _ Measurable.of_discrete,
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
        ($ᵗ R) secretKey.seed msg ep K wr.1 wr.2 ho
      have ha := verify_signatureOfWord hash enc ks.1 ks.2 hc ep msg wr hv
      simp [SyncSignatureAlg.accepts, ha]

/-- Every runtime-producible successful signature verifies for consistent raw keys. -/
theorem verify_of_mem_support_sign [SampleableType R] [DecidableEq H]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K : ℕ)
    (pk : PublicKey PP H) (sk : SecretKey PP H h v) (hc : Consistent hash pk sk)
    (ep : Fin (2 ^ h)) (msg : M) (sig : Signature R H h v)
    (hs : some sig ∈ support (sign hash enc K sk ep msg)) :
    verify hash enc pk ep msg sig = true := by
  simp only [sign, support_map, Set.mem_image] at hs
  obtain ⟨o, ho, he⟩ := hs
  cases o with
  | none => simp at he
  | some wr =>
    have heq : signatureOfWord hash sk ep wr = sig := by simpa using he
    rw [← heq]
    exact verify_signatureOfWord hash enc pk sk hc ep msg wr
      (IncomparableEncoding.Retry.value_eq_some_of_mem_retry enc
        ($ᵗ R) sk.seed msg ep K wr.1 wr.2 ho)

/-- Actual signing exhaustion is exactly the Kth power of one-attempt encoding failure. -/
theorem sign_failure_probability [SampleableType R]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K : ℕ)
    (sk : SecretKey PP H h v) (ep : Fin (2 ^ h)) (msg : M) :
    ProbCompRuntime.probComp.evalDist
      ((fun out => out = none) <$> sign hash enc K sk ep msg) {True} =
      (enc.failureMass ProbCompRuntime.probComp ($ᵗ R) sk.seed msg ep) ^ K := by
  have hf := IncomparableEncoding.Retry.failureMass_eq_pow enc ProbCompRuntime.probComp
    samplingLaws_probComp ($ᵗ R) sk.seed msg ep K
  rw [IncomparableEncoding.Retry.failureMass_eq_probability] at hf
  simpa [sign, ProbCompRuntime.probComp_evalDist, Functor.map_map] using hf

/-- Successful verification has mass one minus exact exhaustion, under lossless sampling. -/
theorem successMass_eq_one_sub_pow [SampleableType H] [SampleableType R]
    [DecidableEq H] (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K : ℕ)
    (ks : PublicKey PP H × SecretKey PP H h v) (hc : Consistent hash ks.1 ks.2)
    (ep : Fin (2 ^ h)) (msg : M) :
    (scheme hash enc K).successMass ProbCompRuntime.probComp ks ep msg =
      let secretKey := ks.2
      1 - (enc.failureMass ProbCompRuntime.probComp ($ᵗ R) secretKey.seed msg ep) ^ K := by
  dsimp
  let secretKey := ks.2
  rw [successMass_eq_retry hash enc K ks hc]
  exact IncomparableEncoding.Retry.successMass_eq_one_sub_pow enc ProbCompRuntime.probComp
    samplingLaws_probComp ($ᵗ R) (by
      rw [LosslessSampler, ProbCompRuntime.probComp_evalDist, ← prEvent_eq_evalDist_map]
      exact OracleComp.prEvent_true_eq_one _) secretKey.seed msg ep K

/-- Lemma 3: a uniform error upper bound gives correctness error at most its Kth power.
This holds also for zero retries and does not identify the bound with the exact failure mass. -/
theorem complete [SampleableType H] [SampleableType R] [Fintype R] [DecidableEq H]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K : ℕ) (δ : ℝ≥0∞)
    (he : enc.UniformErrorAtMost ProbCompRuntime.probComp ($ᵗ R) δ) :
    (scheme hash enc K).Complete ProbCompRuntime.probComp (δ ^ K) := by
  intro ks hks ep msg
  rw [successMass_eq_one_sub_pow hash enc K ks (consistent_generated hash enc K ks hks)]
  let errorLaw := he.2
  let pointwiseBound := errorLaw.2
  let secretKey := ks.2
  exact tsub_le_tsub_left (pow_le_pow_left' (pointwiseBound secretKey.seed msg ep) K) 1

/-- The paper sampling instance has both total key generation and Lemma 3 correctness.
Uniformity is a law of the existing THF sampler; no replacement sampler is introduced. -/
theorem complete_and_keygen_lossless [SampleableType H] [SampleableType R]
    [Fintype PP] [Fintype R] [DecidableEq H] (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K : ℕ) (δ : ℝ≥0∞)
    (hs : UniformSampler ProbCompRuntime.probComp (HashInstance.thf hash).seedGen)
    (he : enc.UniformErrorAtMost ProbCompRuntime.probComp ($ᵗ R) δ) :
    LosslessSampler ProbCompRuntime.probComp (scheme hash enc K).keygen ∧
      (scheme hash enc K).Complete ProbCompRuntime.probComp (δ ^ K) :=
  ⟨keygen_lossless_of_uniform hash hs, complete hash enc K δ he⟩

end GXMSS
