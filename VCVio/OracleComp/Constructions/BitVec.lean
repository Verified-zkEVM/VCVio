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
the message.
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
