/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import HashSig.SLHDSA.Security.ByteBound
public import VCVio.CryptoFoundations.HardnessAssumptions.KeyedHash.CoveringEval

/-!
# Exact rational evaluation of SLH-DSA security bounds

Executable rational formulas are connected to the extended-real bounds by equality proofs.
The honest-address evaluator uses the proved closed form rather than constructing the ledger.
-/

public section

open scoped ENNReal
open KeyedHash.Covering

namespace SLHDSA.Security

/-- The structured ROM bound, evaluated with exact rational arithmetic. -/
@[expose] def securityBoundEval (p : Params) (card c r qh qs : ℕ) : ℚ≥0 :=
  ((qh : ℚ≥0) + 1) * weightedTargetCoverEval p.h p.a p.k qs qh ((qs : ℚ≥0) / card) +
    ((c : ℚ≥0) * qh + ((r + 1) * GeneralScheme.verifyInternalQueryBound p : ℕ)) /
      (card : ℚ≥0)

/-- Executable structured evaluation equals the theorem's bound at every positive node size. -/
theorem rationalValue_securityBoundEval (p : Params) {card : ℕ} (hcard : card ≠ 0)
    (c r qh qs : ℕ) :
    rationalValue (securityBoundEval p card c r qh qs) = securityBound p card c r qh qs := by
  have hc : (card : ℚ≥0) ≠ 0 := by exact_mod_cast hcard
  simp only [securityBoundEval, rationalValue_add, rationalValue_mul,
    rationalValue_natCast, rationalValue_div _ hc, rationalValue_weightedTargetCoverEval]
  simp [securityBound, rationalValue, div_eq_mul_inv]

/-- The cardinality of honest addresses from its closed construction-count formula. -/
@[expose] def honestAdrsCountEval (p : Params) : ℕ :=
  targetCount p .forsF + targetCount p .forsH + targetCount p .forsTl +
    wotsInstanceCount p * p.len * (p.w - 1) + targetCount p .wotsTl + targetCount p .xmssH +
    wotsInstanceCount p * p.len + targetCount p .forsF

theorem honestAdrsCountEval_eq (vp : ValidatedParams) :
    honestAdrsCountEval vp.params = honestAdrsCount vp := (honestAdrsCount_eq vp).symm

/-- The deterministic single-SHAKE bound outside weak seeds. -/
@[expose] def byteBoundEval (p : Params) (qh qs : ℕ) : ℚ≥0 :=
  securityBoundEval p (256 ^ p.n) 2 1 qh qs + ((qs : ℚ≥0) + 1) / (256 ^ p.n : ℕ)

/-- The hedged single-SHAKE bound outside weak seeds. -/
@[expose] def byteBoundHedgedEval (p : Params) (qh qs : ℕ) : ℚ≥0 :=
  securityBoundEval p (256 ^ p.n) 2 1 qh qs + 1 / (256 ^ p.n : ℕ) +
    qs * ((qh : ℚ≥0) + qs + 1) / ((256 ^ p.n : ℕ) : ℚ≥0) ^ 2

/-- The deterministic bound at every seed for 256-bit nodes. -/
@[expose] def everySeedBoundEval (p : Params) (qh qs : ℕ) : ℚ≥0 :=
  securityBoundEval p (256 ^ p.n) 2 1 (qh + GeneralScheme.verifyInternalQueryBound p) qs +
    2 * ((qs : ℚ≥0) + 1) / (256 ^ p.n : ℕ)

/-- The hedged bound at every seed for 256-bit nodes. -/
@[expose] def everySeedBoundHedgedEval (p : Params) (qh qs : ℕ) : ℚ≥0 :=
  byteBoundHedgedEval p (qh + GeneralScheme.verifyInternalQueryBound p) qs +
    ((qs : ℚ≥0) + 1) / (256 ^ p.n : ℕ)

theorem rationalValue_byteBoundEval (vp : ValidatedParams) (qh qs : ℕ) :
    rationalValue (byteBoundEval vp.params qh qs) = byteBound vp qh qs := by
  simp only [byteBoundEval, rationalValue_add,
    rationalValue_securityBoundEval vp.params
      (pow_ne_zero vp.params.n (by norm_num : (256 : ℕ) ≠ 0)) 2 1 qh qs,
    rationalValue_div _ (by positivity : ((256 ^ vp.params.n : ℕ) : ℚ≥0) ≠ 0),
    rationalValue_natCast, rationalValue_one]

theorem rationalValue_byteBoundHedgedEval (vp : ValidatedParams) (qh qs : ℕ) :
    rationalValue (byteBoundHedgedEval vp.params qh qs) = byteBoundHedged vp qh qs := by
  simp only [byteBoundHedgedEval, rationalValue_add, rationalValue_mul,
    rationalValue_securityBoundEval vp.params
      (pow_ne_zero vp.params.n (by norm_num : (256 : ℕ) ≠ 0)) 2 1 qh qs,
    rationalValue_div _ (by positivity : ((256 ^ vp.params.n : ℕ) : ℚ≥0) ≠ 0),
    rationalValue_div _ (by positivity : (((256 ^ vp.params.n : ℕ) : ℚ≥0) ^ 2) ≠ 0),
    rationalValue_pow, rationalValue_natCast, rationalValue_one]

theorem rationalValue_everySeedBoundEval (vp : ValidatedParams) (qh qs : ℕ) :
    rationalValue (everySeedBoundEval vp.params qh qs) = everySeedBound vp qh qs := by
  simp only [everySeedBoundEval, rationalValue_add, rationalValue_mul,
    rationalValue_securityBoundEval vp.params
      (pow_ne_zero vp.params.n (by norm_num : (256 : ℕ) ≠ 0)),
    rationalValue_div _ (by positivity : ((256 ^ vp.params.n : ℕ) : ℚ≥0) ≠ 0),
    rationalValue_natCast, rationalValue_one]
  rfl

theorem rationalValue_everySeedBoundHedgedEval (vp : ValidatedParams) (qh qs : ℕ) :
    rationalValue (everySeedBoundHedgedEval vp.params qh qs) = everySeedBoundHedged vp qh qs := by
  simp only [everySeedBoundHedgedEval, rationalValue_add, rationalValue_byteBoundHedgedEval,
    rationalValue_div _ (by positivity : ((256 ^ vp.params.n : ℕ) : ℚ≥0) ≠ 0),
    rationalValue_natCast, rationalValue_one]

/-- The averaged deterministic byte bound, including the weak seeds' own security bound. -/
@[expose] def averagedByteBoundEval (p : Params) (qh qs : ℕ) : ℚ≥0 :=
  byteBoundEval p qh qs + (honestAdrsCountEval p : ℚ≥0) / 2 ^ 256 *
    (if p.n = 32 then min 1 (everySeedBoundEval p qh qs) else 1)

/-- The averaged hedged byte bound. -/
@[expose] def averagedByteBoundHedgedEval (p : Params) (qh qs : ℕ) : ℚ≥0 :=
  byteBoundHedgedEval p qh qs + (honestAdrsCountEval p : ℚ≥0) / 2 ^ 256 *
    (if p.n = 32 then min 1 (everySeedBoundHedgedEval p qh qs) else 1)

theorem rationalValue_averagedByteBoundEval (vp : ValidatedParams) (qh qs : ℕ) :
    rationalValue (averagedByteBoundEval vp.params qh qs) = byteBound vp qh qs +
      honestAdrsCount vp / 2 ^ 256 * weakSeedFactor vp (everySeedBound vp qh qs) := by
  unfold averagedByteBoundEval
  split_ifs <;>
    simp_all [rationalValue_add, rationalValue_mul, rationalValue_div, rationalValue_pow,
      rationalValue_natCast, rationalValue_byteBoundEval, rationalValue_everySeedBoundEval,
      honestAdrsCountEval_eq, weakSeedFactor_of_n_eq_32, weakSeedFactor_of_ne]

theorem rationalValue_averagedByteBoundHedgedEval (vp : ValidatedParams) (qh qs : ℕ) :
    rationalValue (averagedByteBoundHedgedEval vp.params qh qs) = byteBoundHedged vp qh qs +
      honestAdrsCount vp / 2 ^ 256 * weakSeedFactor vp (everySeedBoundHedged vp qh qs) := by
  unfold averagedByteBoundHedgedEval
  split_ifs <;>
    simp_all [rationalValue_add, rationalValue_mul, rationalValue_div, rationalValue_pow,
      rationalValue_natCast, rationalValue_byteBoundHedgedEval,
      rationalValue_everySeedBoundHedgedEval, honestAdrsCountEval_eq,
      weakSeedFactor_of_n_eq_32, weakSeedFactor_of_ne]

end SLHDSA.Security
