/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import Extern.MLDSA.Laws
public import LatticeCrypto.MLDSA.SecurityHVZK
public import VCVio.OracleComp.RunIO

/-!
# Tests for the ML-DSA mask sampler

- The endpoints of `[-γ₁ + 1, γ₁]`: `maskBounded` is not the symmetric `[-γ₁, γ₁]` or
  `[-γ₁ + 1, γ₁ - 1]`. These examples are what pin the range.
- The decoding sends the value `0` to `γ₁` and the value `2γ₁ - 1` to `-γ₁ + 1`, as FIPS 204's
  `ExpandMask` does.
- The mask sampler, the identification schemes and the HVZK simulator are plain `def`s: this file
  fails to compile if any of them becomes noncomputable. Outputs are random, so nothing is run.
- The response gate passes with probability above `1/2` at each FIPS 204 parameter set. This checks
  the parameters against the exact rate; it does not pin the range, since a slightly different
  range also passes above `1/2`.
- The statement of `identificationSchemeFull` rejects any `t₀` other than the secret key's.
- `identificationSchemeFull_perfectHVZK` applies at the concrete FIPS 204 primitives for ML-DSA-44,
  so its hypotheses hold there. The theorem itself, not this test, shows the simulator is right.
-/

public section

open OracleComp OracleSpec ENNReal
open LatticeCrypto MLDSA

namespace MLDSA.MaskBoxTest

/-- The vector with every coefficient of every component equal to the integer `c`. -/
private noncomputable def constVec (k : ℕ) (c : ℤ) : RqVec k :=
  Vector.ofFn fun _ => (Poly.ofPi fun _ => (c : Coeff) : Rq)

private lemma constVec_coeff (k : ℕ) (c : ℤ) (j : Fin k) (i : Fin ringDegree) :
    ((constVec k c).get j).get i = (c : Coeff) := by
  rw [constVec, Poly.get_vectorOfFn]
  exact Poly.get_ofPi _ i

/-- A small constant vector is in the mask range exactly when its value is in `[-γ₁ + 1, γ₁]`. -/
private lemma maskBounded_constVec_iff {gamma1 : ℕ} {c : ℤ}
    (hlo : -(modulus : ℤ) < c * 2) (hhi : c * 2 ≤ modulus) :
    maskBounded (constVec 1 c) gamma1 ↔ -(gamma1 : ℤ) < c ∧ c ≤ gamma1 := by
  have hrepr : centeredRepr (c : Coeff) = c := centeredRepr_intCast_eq c hlo hhi
  simp only [maskBounded, constVec_coeff, hrepr]
  exact ⟨fun h => h 0 ⟨0, by simp [ringDegree]⟩, fun h _ _ => h⟩

/-- The top endpoint `γ₁` is in the range. -/
example {gamma1 : ℕ} (h0 : 0 < gamma1) (hq : 2 * gamma1 < modulus) :
    maskBounded (constVec 1 gamma1) gamma1 :=
  (maskBounded_constVec_iff (by omega) (by omega)).mpr ⟨by omega, le_rfl⟩

/-- The bottom endpoint `-γ₁ + 1` is in the range. -/
example {gamma1 : ℕ} (h0 : 0 < gamma1) (hq : 2 * gamma1 < modulus) :
    maskBounded (constVec 1 (-(gamma1 : ℤ) + 1)) gamma1 :=
  (maskBounded_constVec_iff (by omega) (by omega)).mpr ⟨by omega, by omega⟩

/-- `-γ₁` is outside the range. -/
example {gamma1 : ℕ} (hq : 2 * gamma1 < modulus) :
    ¬maskBounded (constVec 1 (-(gamma1 : ℤ))) gamma1 := fun h =>
  absurd ((maskBounded_constVec_iff (by omega) (by omega)).mp h).1 (by omega)

/-- `γ₁ + 1` is outside the range. -/
example {gamma1 : ℕ} (hq : 2 * gamma1 + 2 ≤ modulus) :
    ¬maskBounded (constVec 1 ((gamma1 : ℤ) + 1)) gamma1 := fun h =>
  absurd ((maskBounded_constVec_iff (by omega) (by omega)).mp h).2 (by omega)

/-- The value `0` decodes to the top endpoint `γ₁`. -/
example {gamma1 : ℕ} (hq : 2 * gamma1 < modulus) :
    centeredRepr (maskDecodeCoeff gamma1 0) = gamma1 := by
  rw [centeredRepr_maskDecodeCoeff hq]
  simp

/-- The largest value `2γ₁ - 1` decodes to the bottom endpoint `-γ₁ + 1`. -/
example {gamma1 : ℕ} (h0 : 0 < gamma1) (hq : 2 * gamma1 < modulus) :
    centeredRepr (maskDecodeCoeff gamma1 (Fin.last _)) = -(gamma1 : ℤ) + 1 := by
  rw [centeredRepr_maskDecodeCoeff hq, Fin.val_last]
  omega

/-! ### Computability

Each `def` below elaborates without `noncomputable`, so code generation succeeds for the mask
sampler, the identification schemes and the HVZK simulator. -/

/-- The mask sampler as an executable `IO` action. -/
def sampleMaskVecIO (k gamma1 : ℕ) : IO (RqVec k) :=
  OracleComp.runIO (sampleMaskVec k gamma1)

/-- The identification scheme with `t₀` in the statement. -/
def identificationSchemeFullCompiled (p : Params) (prims : Primitives p) [NTTRingOps]
    [DecidableEq prims.High] :=
  identificationSchemeFull p prims

/-- The HVZK simulator as an executable `IO` action. -/
def hvzkSimulatorIO (p : Params) (prims : Primitives p) [NTTRingOps]
    [SampleableType (CommitHashBytes p)] (fpk : FullPublicKey p prims) :
    IO (Option (Commitment p prims × CommitHashBytes p × Response p prims)) :=
  OracleComp.runIO (hvzkSimulator p prims fpk)

private lemma half_lt_of_lt_two_mul {a b : ℕ} (hb : 0 < b) (h : b < 2 * a) :
    (1 / 2 : ℝ≥0∞) < (a : ℝ≥0∞) / b := by
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  have ha : (b : ℝ) < 2 * a := by exact_mod_cast h
  have key : (1 / 2 : ℝ) < (a : ℝ) / b := by
    rw [lt_div_iff₀ hb']
    linarith
  have hhalf : (1 / 2 : ℝ≥0∞) = ENNReal.ofReal (1 / 2) := by
    rw [ENNReal.ofReal_div_of_pos two_pos]
    simp
  have hdiv : (a : ℝ≥0∞) / b = ENNReal.ofReal ((a : ℝ) / b) := by
    rw [ENNReal.ofReal_div_of_pos hb']
    simp
  rw [hhalf, hdiv]
  exact (ENNReal.ofReal_lt_ofReal_iff (lt_trans (by norm_num) key)).mpr key

/-- The response gate's rate at a parameter set, from the box count. -/
private lemma half_lt_gate (p : Params) (hb : 0 < p.gamma1 - p.beta)
    (hq : 2 * p.gamma1 < modulus)
    (h : (2 * p.gamma1) ^ (ringDegree * p.l) <
      2 * (2 * (p.gamma1 - p.beta) - 1) ^ (ringDegree * p.l)) :
    (1 / 2 : ℝ≥0∞) <
      Pr{let z ← sampleMaskVec p.l p.gamma1}[polyVecNorm z < p.gamma1 - p.beta] := by
  rw [prEvent_sampleMaskVec_polyVecNorm_lt p.l hb (by omega) hq, ← Nat.cast_pow, ← Nat.cast_pow]
  have hpos : 0 < (2 * p.gamma1) ^ (ringDegree * p.l) := Nat.pow_pos (by omega)
  exact half_lt_of_lt_two_mul hpos h

/-- ML-DSA-44: a response passes the gate with probability above `1/2`. -/
theorem half_lt_gate_mldsa44 : (1 / 2 : ℝ≥0∞) <
    Pr{let z ← sampleMaskVec mldsa44.l mldsa44.gamma1}[
      polyVecNorm z < mldsa44.gamma1 - mldsa44.beta] :=
  half_lt_gate mldsa44 (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- ML-DSA-65: a response passes the gate with probability above `1/2`. -/
theorem half_lt_gate_mldsa65 : (1 / 2 : ℝ≥0∞) <
    Pr{let z ← sampleMaskVec mldsa65.l mldsa65.gamma1}[
      polyVecNorm z < mldsa65.gamma1 - mldsa65.beta] :=
  half_lt_gate mldsa65 (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- ML-DSA-87: a response passes the gate with probability above `1/2`. -/
theorem half_lt_gate_mldsa87 : (1 / 2 : ℝ≥0∞) <
    Pr{let z ← sampleMaskVec mldsa87.l mldsa87.gamma1}[
      polyVecNorm z < mldsa87.gamma1 - mldsa87.beta] :=
  half_lt_gate mldsa87 (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- The statement of `identificationSchemeFull` must carry the secret key's `t₀`: any other `t₀` is
rejected, whatever the public key. -/
example (p : Params) (prims : Primitives p) [NTTRingOps] (pk : PublicKey p prims)
    (sk : SecretKey p) (t0 : RqVec p.k) (h : t0 ≠ sk.t0) :
    validFullKeyPair p prims ⟨pk, t0⟩ sk = false := by
  simp [validFullKeyPair, h]

/-- `identificationSchemeFull_perfectHVZK` at the concrete FIPS 204 primitives for ML-DSA-44. -/
theorem perfectHVZK_concretePrimitives
    [DecidableEq (MLDSA.Concrete.concretePrimitives mldsa44).High] :
    letI : NTTRingOps := MLDSA.Concrete.concreteNTTRingOps
    (identificationSchemeFull mldsa44 (MLDSA.Concrete.concretePrimitives mldsa44)).PerfectHVZK
      (hvzkSimulator mldsa44 (MLDSA.Concrete.concretePrimitives mldsa44)) :=
  letI : NTTRingOps := MLDSA.Concrete.concreteNTTRingOps
  identificationSchemeFull_perfectHVZK mldsa44 (MLDSA.Concrete.concretePrimitives mldsa44)
    (MLDSA.Concrete.concretePrimitives_laws mldsa44 (.inl rfl))
    (MLDSA.Concrete.approved_gamma1_width mldsa44 (.inl rfl)).2

end MLDSA.MaskBoxTest
