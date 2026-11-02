/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import HashSig.SLHDSA.Security.Profile

/-!
# SHAKE profiles and their original ROM budgets

Each profile fixes a valid pure context, an approved parameter set and deterministic or hedged
randomization. Its algorithm uses the production independent uniform key-seed sampler. The
security client uses the original adversary ROM caps `(qh, qs)` and the matching bound evaluator,
including its weak-seed/randomizer terms. It imposes no signing-lifetime restriction.
-/

public section

open OracleComp SignatureAlg KeyedHash.Covering
open SLHDSA SLHDSA.Security

namespace SLHDSA.Examples.Profiles

/-- The approved SHAKE-128s profile at a fixed valid context and selected signing mode. -/
@[expose] def shake128s (ctx : PureContext) (mode : PureSigningMode) : ShakeProfile where
  parameterSet := .SLHDSA_SHAKE_128s
  shakeFamily := rfl
  signingMode := mode
  context := ctx

/-- The approved SHAKE-192f profile at a fixed valid context and selected signing mode. -/
@[expose] def shake192f (ctx : PureContext) (mode : PureSigningMode) : ShakeProfile where
  parameterSet := .SLHDSA_SHAKE_192f
  shakeFamily := rfl
  signingMode := mode
  context := ctx

/-- The approved SHAKE-128s profile with deterministic signing. -/
abbrev deterministic128s (ctx : PureContext) := shake128s ctx .deterministic
/-- The approved SHAKE-128s profile with hedged signing. -/
abbrev hedged128s (ctx : PureContext) := shake128s ctx .hedged
/-- The approved SHAKE-192f profile with deterministic signing. -/
abbrev deterministic192f (ctx : PureContext) := shake192f ctx .deterministic
/-- The approved SHAKE-192f profile with hedged signing. -/
abbrev hedged192f (ctx : PureContext) := shake192f ctx .hedged

/-- Both 128s signing modes retain their own original evaluator and ROM budget. -/
theorem bound128s (ctx : PureContext) (mode : PureSigningMode)
    (adv : StrongUnforgeableAdversary (shake128s ctx mode).algorithm) {qh qs : Nat}
    (hadv : adv.RomQueryBound qh qs) :
    strongUnforgeableAdvantage
      (shakeRuntime FipsParameterSet.SLHDSA_SHAKE_128s.validatedParams) adv ≤
        rationalValue ((shake128s ctx mode).boundEvaluator qh qs) :=
  (shake128s ctx mode).strongUnforgeableAdvantage_le_boundEvaluator adv hadv

/-- Both 192f signing modes retain their own original evaluator and ROM budget. -/
theorem bound192f (ctx : PureContext) (mode : PureSigningMode)
    (adv : StrongUnforgeableAdversary (shake192f ctx mode).algorithm) {qh qs : Nat}
    (hadv : adv.RomQueryBound qh qs) :
    strongUnforgeableAdvantage
      (shakeRuntime FipsParameterSet.SLHDSA_SHAKE_192f.validatedParams) adv ≤
        rationalValue ((shake192f ctx mode).boundEvaluator qh qs) :=
  (shake192f ctx mode).strongUnforgeableAdvantage_le_boundEvaluator adv hadv

end SLHDSA.Examples.Profiles
