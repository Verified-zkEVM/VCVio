/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import HashSig.SLHDSA.SHAKE128s.Bridge.Wire
public import HashSig.SLHDSA.SHAKE128s.Statement.Theorems.StrongUnforgeability

/-!
# Fixed-context SHAKE-128s wire security

The deterministic pure-mode byte-wire game uses one shared fixed-30-byte oracle and independent
uniform key seeds. It inherits the specialized 127-bit work bound through exact advantage
equality and actual source-budget transport. Work includes each signing request, each direct
adversary hash and at most 3824 final-verification calls. The common fixed-context scope also
has the original general SHAKE bound, including its weak-seed term, so both conclusions hold
at their minimum.
-/

public section

open SignatureAlg
open scoped ENNReal

namespace SLHDSA.SHAKE128s

/-- The deterministic fixed-context wire advantage is bounded by the smaller of the general
SHAKE bound with its weak-seed term and the 127-bit work bound. The final verifier is charged
the checksum-sensitive intrinsic allowance, 3824 calls at SHAKE-128s. -/
theorem wireStrongAdvantage_le (ctx : SLHDSA.Security.PureContext)
    (adv : StrongUnforgeableAdversary (Bridge.wireAlgorithm ctx)) {qh qs : Nat}
    (hadv : adv.RomQueryBound qh qs) (hqs : qs ≤ signingLimit) :
    strongUnforgeableAdvantage (SLHDSA.Security.shakeRuntime FIPS205.params) adv ≤
      min (SLHDSA.Security.byteBound FIPS205.params qh qs +
        SLHDSA.Security.honestAdrsCount FIPS205.params / 2 ^ 256 *
          SLHDSA.Security.weakSeedFactor FIPS205.params
            (SLHDSA.Security.everySeedBound FIPS205.params qh qs))
        (((qh + qs + GeneralScheme.verifyInternalQueryBound FIPS205.params.params : Nat) :
          ℝ≥0∞) / ((2 ^ 127 : Nat) : ℝ≥0∞)) := by
  apply le_min
  · exact SLHDSA.Security.wireStrongAdvantage_le_securityBound_validatedParams
      .SLHDSA_SHAKE_128s ctx adv hadv
  · rw [Bridge.strongUnforgeableAdvantage_eq_fixedContext ctx adv]
    apply slhDsa_sufCma_127 _ (by rw [Bridge.verifyInternalQueryBound_eq]; omega)
      (Bridge.fixedContextAdversary ctx adv)
      (Bridge.withinSigningLimit_fixedContext ctx adv hadv hqs)
    exact Bridge.fixedContextAdversary_hasQueryBound ctx adv hadv

/-- The conservative work bound from the parameter-uniform verifier estimate. -/
theorem wireStrongAdvantage_le_workBound (ctx : SLHDSA.Security.PureContext)
    (adv : StrongUnforgeableAdversary (Bridge.wireAlgorithm ctx)) {qh qs : Nat}
    (hadv : adv.RomQueryBound qh qs) (hqs : qs ≤ signingLimit) :
    strongUnforgeableAdvantage (SLHDSA.Security.shakeRuntime FIPS205.params) adv ≤
      ((qh + qs + 3929 : Nat) : ℝ≥0∞) / ((2 ^ 127 : Nat) : ℝ≥0∞) := by
  apply ((wireStrongAdvantage_le ctx adv hadv hqs).trans (min_le_right _ _)).trans
  rw [Bridge.verifyInternalQueryBound_eq]
  gcongr
  omega

/-- The common wire bound with the conservative verifier estimate. -/
theorem wireStrongAdvantage_le_min_bound (ctx : SLHDSA.Security.PureContext)
    (adv : StrongUnforgeableAdversary (Bridge.wireAlgorithm ctx)) {qh qs : Nat}
    (hadv : adv.RomQueryBound qh qs) (hqs : qs ≤ signingLimit) :
    strongUnforgeableAdvantage (SLHDSA.Security.shakeRuntime FIPS205.params) adv ≤
      min (SLHDSA.Security.byteBound FIPS205.params qh qs +
        SLHDSA.Security.honestAdrsCount FIPS205.params / 2 ^ 256 *
          SLHDSA.Security.weakSeedFactor FIPS205.params
            (SLHDSA.Security.everySeedBound FIPS205.params qh qs))
        (((qh + qs + 3929 : Nat) : ℝ≥0∞) / ((2 ^ 127 : Nat) : ℝ≥0∞)) := by
  apply (wireStrongAdvantage_le ctx adv hadv hqs).trans
  rw [Bridge.verifyInternalQueryBound_eq]
  gcongr
  omega

end SLHDSA.SHAKE128s
