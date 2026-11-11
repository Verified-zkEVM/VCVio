/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import HashSig.SLHDSA.Security.Wire
public import HashSig.SLHDSA.Security.BoundEval

/-!
# Pure SHAKE security profiles

A profile binds an approved SHAKE parameter set, fixed pure-mode context, signing mode,
canonical wire codecs, independent uniform key seeds, and its proved exact bound evaluator.
The budget is the adversary's own ROM traffic. Whole-deployment work, prehashing, other
constructions, and a variable-output XOF adversary require their own certificates.
-/

public section

open OracleComp SignatureAlg
open KeyedHash.Covering
open scoped ENNReal

namespace SLHDSA.Security

/-- The FIPS pure-mode randomizer contract. -/
inductive PureSigningMode where
  /-- Use the public seed as FIPS 205's deterministic randomizer input. -/
  | deterministic
  /-- Draw an independent uniform randomizer input for every signature. -/
  | hedged
deriving DecidableEq, Repr

/-- Choices bound together by the pure-mode single-SHAKE security theorem. -/
structure ShakeProfile where
  /-- The exact approved FIPS parameter bundle. -/
  parameterSet : FipsParameterSet
  /-- The selected name denotes SHAKE rather than SHA-2. -/
  shakeFamily : parameterSet.hashFamily = .shake
  /-- The randomizer sampling contract. -/
  signingMode : PureSigningMode
  /-- The fixed pure-mode external context. -/
  context : PureContext

namespace ShakeProfile

/-- The randomizer source fixed by a profile. -/
@[expose] noncomputable def randomizer (profile : ShakeProfile) :
    PublicKeyCore (shakeCore profile.parameterSet.validatedParams) →
      ProbComp (shakeCore profile.parameterSet.validatedParams).Y :=
  match profile.signingMode with
  | .deterministic => fun pk => pure pk.pkSeed
  | .hedged => fun _ => $ᵗ (shakeCore profile.parameterSet.validatedParams).Y

/-- The profile's public pure byte interface, with the theorem's uniform public-seed sampler. -/
@[expose] noncomputable def algorithm (profile : ShakeProfile) :=
  wireShakeScheme profile.parameterSet.validatedParams profile.context profile.randomizer
    ($ᵗ (shakeCore profile.parameterSet.validatedParams).PkSeed)

/-- Exact rational evaluation of the bound for this profile's chosen signing mode. -/
@[expose] def boundEvaluator (profile : ShakeProfile) (qh qs : ℕ) : ℚ≥0 :=
  match profile.signingMode with
  | .deterministic => averagedByteBoundEval profile.parameterSet.validatedParams.params qh qs
  | .hedged => averagedByteBoundHedgedEval profile.parameterSet.validatedParams.params qh qs

/-- A profile carries its public wire game's security theorem and matching executable bound. -/
theorem strongUnforgeableAdvantage_le_boundEvaluator (profile : ShakeProfile)
    (adv : StrongUnforgeableAdversary profile.algorithm) {qh qs : ℕ}
    (hadv : adv.RomQueryBound qh qs) :
    strongUnforgeableAdvantage (shakeRuntime profile.parameterSet.validatedParams) adv ≤
      rationalValue (profile.boundEvaluator qh qs) := by
  rcases profile with ⟨set, family, mode, ctx⟩
  cases mode with
  | deterministic =>
    change _ ≤ rationalValue (averagedByteBoundEval set.validatedParams.params qh qs)
    rw [rationalValue_averagedByteBoundEval]
    exact wireStrongAdvantage_le_securityBound_validatedParams set ctx adv hadv
  | hedged =>
    change _ ≤ rationalValue (averagedByteBoundHedgedEval set.validatedParams.params qh qs)
    rw [rationalValue_averagedByteBoundHedgedEval]
    exact wireStrongAdvantage_le_securityBound_hedged_validatedParams set ctx adv hadv

end ShakeProfile
end SLHDSA.Security
