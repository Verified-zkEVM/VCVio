/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import HashSig.SLHDSA.Security.Profile

/-!
# General security expressions and profile mode equations

The equations retain separate hash/signing budgets, hedged product terms and the weak-seed
factor for 32-byte nodes. Profile selection binds the randomizer and executable evaluator.
-/

public section

open OracleComp OracleSpec
open scoped ENNReal
open SLHDSA SLHDSA.Security

namespace SLHDSA.Refactor.Semantics

/-- The per-seed deterministic expression retains the message-PRF contribution. -/
theorem byteBoundEquation (vp : ValidatedParams) (qh qs : Nat) :
    byteBound vp qh qs = securityBound vp.params (256 ^ vp.params.n) 2 1 qh qs +
      ((qs : ℝ≥0∞) + 1) / (256 ^ vp.params.n : Nat) := rfl

/-- The hedged expression retains the smaller product term. -/
theorem hedgedByteBoundEquation (vp : ValidatedParams) (qh qs : Nat) :
    byteBoundHedged vp qh qs = securityBound vp.params (256 ^ vp.params.n) 2 1 qh qs +
      1 / (256 ^ vp.params.n : Nat) +
      qs * ((qh : ℝ≥0∞) + qs + 1) / ((256 ^ vp.params.n : Nat) : ℝ≥0∞) ^ 2 := rfl

/-- The every-seed deterministic expression includes the linked verifier work. -/
theorem everySeedBoundEquation (vp : ValidatedParams) (qh qs : Nat) :
    everySeedBound vp qh qs = securityBound vp.params (256 ^ vp.params.n) 2 1
      (qh + GeneralScheme.verifyInternalQueryBound vp.params) qs +
      2 * ((qs : ℝ≥0∞) + 1) / (256 ^ vp.params.n : Nat) := rfl

/-- The every-seed hedged expression includes both verifier work and its residual term. -/
theorem hedgedEverySeedBoundEquation (vp : ValidatedParams) (qh qs : Nat) :
    everySeedBoundHedged vp qh qs =
      byteBoundHedged vp (qh + GeneralScheme.verifyInternalQueryBound vp.params) qs +
        ((qs : ℝ≥0∞) + 1) / (256 ^ vp.params.n : Nat) := rfl

/-- Only 32-byte nodes use the sharper bound at weak seeds. -/
theorem weakSeedFactorEquation (vp : ValidatedParams) (bound : ℝ≥0∞) :
    weakSeedFactor vp bound = if vp.params.n = 32 then min 1 bound else 1 := by
  by_cases h : vp.params.n = 32
  · rw [weakSeedFactor_of_n_eq_32 h]
    simp only [h, reduceIte]
  · rw [weakSeedFactor_of_ne h]
    simp only [h, reduceIte]

/-- Deterministic signing uses the public seed; hedged signing samples a fresh randomizer. -/
theorem profileRandomizerEquation (profile : ShakeProfile)
    (pk : PublicKeyCore (shakeCore profile.parameterSet.validatedParams)) :
    profile.randomizer pk = match profile.signingMode with
      | .deterministic => pure pk.pkSeed
      | .hedged => $ᵗ (shakeCore profile.parameterSet.validatedParams).Y := by
  cases h : profile.signingMode <;> simp only [ShakeProfile.randomizer, h]

/-- The wire algorithm uses the profile's context and a uniform public seed. -/
theorem profileAlgorithmEquation (profile : ShakeProfile) :
    profile.algorithm = wireShakeScheme profile.parameterSet.validatedParams profile.context
      profile.randomizer ($ᵗ (shakeCore profile.parameterSet.validatedParams).PkSeed) := rfl

/-- Each signing mode selects its matching exact rational evaluator. -/
theorem profileEvaluatorEquation (profile : ShakeProfile) (qh qs : Nat) :
    profile.boundEvaluator qh qs = match profile.signingMode with
      | .deterministic => averagedByteBoundEval profile.parameterSet.validatedParams.params qh qs
      | .hedged =>
        averagedByteBoundHedgedEval profile.parameterSet.validatedParams.params qh qs := rfl

end SLHDSA.Refactor.Semantics
