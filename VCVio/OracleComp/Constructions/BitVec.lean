/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.OracleComp.Constructions.SampleableType
public import VCVio.EvalDist.BitVec
public import VCVio.EvalDist.Prod
public import VCVio.EvalDist.BitVec.Measure
public import VCVio.OracleComp.Constructions.SampleableType.MeasureCompatibility
public import VCVio.OracleComp.Constructions.SampleableType.NativeMeasure
import VCVio.OracleComp.EvalDist.UniformCompatibility

/-!
# Uniform bit-vector sampling

Uniform XOR keys give a uniform ciphertext measure and make the ciphertext independent of
the message. Singleton-probability corollaries provide the same facts to discrete clients.
-/

@[expose] public section

open OracleSpec OracleComp ENNReal MeasureTheory ProbabilityTheory

/-- XOR with a sampled uniform bit vector has a native uniform output measure. -/
theorem evalDist_xor_uniformSample (sp : ℕ) (msg : BitVec sp) :
    𝒟[(fun k : BitVec sp => k ^^^ msg) <$> ($ᵗ BitVec sp)] = uniformOn Set.univ :=
  evalDist_xor_uniform_right _ msg (SampleableType.evalDist_bitVec sp)

/-- A sampled key makes the one-time-pad ciphertext independent of the message. -/
theorem evalDist_pair_xor_uniformSample (sp : ℕ) (mx : ProbComp (BitVec sp)) :
    𝒟[do
      let msg ← mx
      let key ← $ᵗ BitVec sp
      return (msg, key ^^^ msg)] =
        𝒟[mx].prod (uniformOn Set.univ : Measure (BitVec sp)) :=
  evalDist_pair_xor_uniform_right mx ($ᵗ BitVec sp) id
    (SampleableType.evalDist_bitVec sp)

/-- A sampled key gives every ciphertext the native uniform output measure. -/
theorem evalDist_cipher_from_pair_uniformSample
    (sp : ℕ) (mx : ProbComp (BitVec sp)) :
    𝒟[do
      let msg ← mx
      let key ← $ᵗ BitVec sp
      return key ^^^ msg] = uniformOn Set.univ := by
  exact evalDist_bind_xor_uniform mx ($ᵗ BitVec sp) id
    (OracleComp.evalDist_apply_univ_eq_one mx)
    (SampleableType.evalDist_bitVec sp)

lemma probOutput_xor_uniform (sp : ℕ) (msg σ : BitVec sp) :
    Pr[= σ | (fun k : BitVec sp => k ^^^ msg) <$> ($ᵗ BitVec sp)] =
      (Fintype.card (BitVec sp) : ℝ≥0∞)⁻¹ := by
  have hxor := evalDist_xor_uniform_right ($ᵗ BitVec sp) msg
    (SampleableType.evalDist_bitVec sp)
  rw [← evalDist_apply_singleton, hxor, uniformOn_univ_apply_singleton]

lemma probOutput_pair_xor_uniform (sp : ℕ) (mx : ProbComp (BitVec sp))
    (msg σ : BitVec sp) :
    Pr[= (msg, σ) | do
      let msg' ← mx
      let k ← $ᵗ BitVec sp
      return (msg', k ^^^ msg')] =
      Pr[= msg | mx] * (Fintype.card (BitVec sp) : ℝ≥0∞)⁻¹ := by
  have hpair := evalDist_pair_xor_uniform_right mx ($ᵗ BitVec sp) (fun msg' => msg')
    (SampleableType.evalDist_bitVec sp)
  rw [← evalDist_apply_singleton, hpair]
  have hsingleton : ({(msg, σ)} : Set (BitVec sp × BitVec sp)) = {msg} ×ˢ {σ} := by
    ext z
    simp
  rw [hsingleton, Measure.prod_prod, evalDist_apply_singleton,
    uniformOn_univ_apply_singleton]

lemma probOutput_cipher_from_pair_uniform (sp : ℕ) (mx : ProbComp (BitVec sp))
    (σ : BitVec sp) :
    Pr[= σ | do
      let msg' ← mx
      let k ← $ᵗ BitVec sp
      return (k ^^^ msg')] =
      (Fintype.card (BitVec sp) : ℝ≥0∞)⁻¹ := by
  have hmx : 𝒟[mx] Set.univ = 1 := OracleComp.evalDist_apply_univ_eq_one mx
  have hcipher := evalDist_bind_xor_uniform mx ($ᵗ BitVec sp) (fun msg' => msg') hmx
    (SampleableType.evalDist_bitVec sp)
  rw [← evalDist_apply_singleton, hcipher, uniformOn_univ_apply_singleton]
