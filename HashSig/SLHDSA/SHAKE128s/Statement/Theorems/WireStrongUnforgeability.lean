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
adversary hash and at most 3929 final-verification calls. The common fixed-context scope also
has the original general SHAKE bound, including its weak-seed term, so both conclusions hold
at their minimum.
-/

public section

open SignatureAlg
open scoped ENNReal

namespace SLHDSA.SHAKE128s

/-- Deterministic SHAKE-128s at a valid fixed context has the 127-bit wire work bound. The only
adversary assumptions are its syntactic query budgets and the `2^64` signing-request lifetime. -/
theorem wireStrongAdvantage_le_workBound (ctx : SLHDSA.Security.PureContext)
    (adv : StrongUnforgeableAdversary (Bridge.wireAlgorithm ctx)) {qh qs : Nat}
    (hadv : adv.RomQueryBound qh qs) (hqs : qs ≤ signingLimit) :
    strongUnforgeableAdvantage (SLHDSA.Security.shakeRuntime FIPS205.params) adv ≤
      ((qh + qs + 3929 : Nat) : ℝ≥0∞) / ((2 ^ 127 : Nat) : ℝ≥0∞) := by
  rw [Bridge.strongUnforgeableAdvantage_eq_fixedContext ctx adv]
  have bound := slhDsa_sufCma_127 (qh + qs + Bridge.verifierCap)
    (by rw [Bridge.verifierCap_eq]; omega) (Bridge.fixedContextAdversary ctx adv)
    (Bridge.withinSigningLimit_fixedContext ctx adv hadv hqs)
    (Bridge.hasQueryBound_fixedContext ctx adv hadv)
  simpa only [Bridge.verifierCap_eq] using bound

/-- The same actual wire advantage obeys the minimum of the general SHAKE bound and the
specialized work bound, retaining the general bound's complete weak-seed contribution. -/
theorem wireStrongAdvantage_le_min_bound (ctx : SLHDSA.Security.PureContext)
    (adv : StrongUnforgeableAdversary (Bridge.wireAlgorithm ctx)) {qh qs : Nat}
    (hadv : adv.RomQueryBound qh qs) (hqs : qs ≤ signingLimit) :
    strongUnforgeableAdvantage (SLHDSA.Security.shakeRuntime FIPS205.params) adv ≤
      min (SLHDSA.Security.byteBound FIPS205.params qh qs +
        SLHDSA.Security.honestAdrsCount FIPS205.params / 2 ^ 256 *
          SLHDSA.Security.weakSeedFactor FIPS205.params
            (SLHDSA.Security.everySeedBound FIPS205.params qh qs))
        (((qh + qs + 3929 : Nat) : ℝ≥0∞) / ((2 ^ 127 : Nat) : ℝ≥0∞)) := by
  apply le_min
  · exact SLHDSA.Security.wireStrongAdvantage_le_securityBound_validatedParams
      .SLHDSA_SHAKE_128s ctx adv hadv
  · exact wireStrongAdvantage_le_workBound ctx adv hadv hqs

end SLHDSA.SHAKE128s
