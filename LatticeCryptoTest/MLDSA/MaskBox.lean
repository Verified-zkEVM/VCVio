/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import Extern.MLDSA.NonVacuity
public import LatticeCrypto.MLDSA.SecurityHVZK

/-!
# Tests for the ML-DSA mask box

- The endpoints of `[-γ₁ + 1, γ₁]`: the box is not the symmetric `[-γ₁, γ₁]` or `[-γ₁ + 1, γ₁ - 1]`.
- The response gate passes with probability above `1/2` at each FIPS 204 parameter set. A box wider
  than `ExpandMask`'s range lowers these rates.
- `uniform_bind_evalDistEq_of_cover` needs the continuation to ignore arguments outside the covered
  set: without that hypothesis its conclusion fails.
- `idsWithAbort_hvzk` holds at a `Primitives.Laws` witness for an approved parameter set.
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

/-- In `maskBounded` terms, a small constant vector is in the box exactly when its value is in
`[-γ₁ + 1, γ₁]`. -/
private lemma maskBounded_constVec_iff {gamma1 : ℕ} (hgamma1 : 0 < gamma1) {c : ℤ}
    (hlo : -(modulus : ℤ) < c * 2) (hhi : c * 2 ≤ modulus) :
    maskBounded (constVec 1 c) gamma1 ↔ -(gamma1 : ℤ) < c ∧ c ≤ gamma1 := by
  have hrepr : centeredRepr (c : Coeff) = c := centeredRepr_intCast_eq c hlo hhi
  rw [maskBounded_iff hgamma1]
  simp only [constVec_coeff, hrepr]
  exact ⟨fun h => h 0 ⟨0, by simp [ringDegree]⟩, fun h _ _ => h⟩

/-- The top endpoint `γ₁` is in the box. -/
example {gamma1 : ℕ} (h0 : 0 < gamma1) (hq : 2 * gamma1 < modulus) :
    maskBounded (constVec 1 gamma1) gamma1 :=
  (maskBounded_constVec_iff h0 (by omega) (by omega)).mpr ⟨by omega, le_rfl⟩

/-- The bottom endpoint `-γ₁ + 1` is in the box. -/
example {gamma1 : ℕ} (h0 : 0 < gamma1) (hq : 2 * gamma1 < modulus) :
    maskBounded (constVec 1 (-(gamma1 : ℤ) + 1)) gamma1 :=
  (maskBounded_constVec_iff h0 (by omega) (by omega)).mpr ⟨by omega, by omega⟩

/-- `-γ₁` is outside the box. -/
example {gamma1 : ℕ} (h0 : 0 < gamma1) (hq : 2 * gamma1 < modulus) :
    ¬maskBounded (constVec 1 (-(gamma1 : ℤ))) gamma1 := fun h =>
  absurd ((maskBounded_constVec_iff h0 (by omega) (by omega)).mp h).1 (by omega)

/-- `γ₁ + 1` is outside the box. -/
example {gamma1 : ℕ} (h0 : 0 < gamma1) (hq : 2 * gamma1 + 2 ≤ modulus) :
    ¬maskBounded (constVec 1 ((gamma1 : ℤ) + 1)) gamma1 := fun h =>
  absurd ((maskBounded_constVec_iff h0 (by omega) (by omega)).mp h).2 (by omega)

/-- The box stays inhabited at the degenerate `γ₁ = 0`. -/
example (k : ℕ) : maskBounded (0 : RqVec k) 0 := .inl rfl

lemma half_lt_of_lt_two_mul {a b : ℕ} (hb : 0 < b) (h : b < 2 * a) :
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
lemma half_lt_gate (p : Params) (hb : 0 < p.gamma1 - p.beta)
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

/-- `uniform_bind_evalDistEq_of_cover` fails without `hk`: both injections below cover `{1}`, but
the continuation tests for `0`, which only `f₁` reaches. -/
example :
    Pr{let x ← (do let a ← $ᵗ Bool; pure (decide (a.toNat = 0)) : ProbComp Bool)}[x = true] ≠
      Pr{let x ← (do
        let a ← $ᵗ Bool
        pure (decide (a.toNat + 1 = 0)) : ProbComp Bool)}[x = true] := by
  simp [SampleableType.prEvent_uniformSample]

/-- `idsWithAbort_hvzk` at a `Primitives.Laws` witness for ML-DSA-44. -/
theorem perfectHVZK_seedRevealingPrims [DecidableEq (seedRevealingPrims mldsa44).High] :
    letI : NTTRingOps := MLDSA.Concrete.concreteNTTRingOps
    (identificationScheme mldsa44 (seedRevealingPrims mldsa44)).PerfectHVZK
      (hvzkSimulatorReal mldsa44 (seedRevealingPrims mldsa44)) :=
  letI : NTTRingOps := MLDSA.Concrete.concreteNTTRingOps
  idsWithAbort_hvzk mldsa44 (seedRevealingPrims mldsa44)
    (seedRevealingPrims_laws mldsa44 (.inl rfl))

end MLDSA.MaskBoxTest
