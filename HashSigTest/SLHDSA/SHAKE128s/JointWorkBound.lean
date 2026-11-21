/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import HashSig.SLHDSA.SHAKE128s.Statement.Theorems.StrongUnforgeability

/-!
# Downstream use of the SHAKE-128s joint-work bound

The public FIPS interface gives literal bounds on both sides of the verifier threshold and
at saturation. Its strict comparison applies to the original adversary and joint resource cap.
-/

public section

namespace SLHDSA.SHAKE128s

open scoped ENNReal

example : jointWorkBound 568 = 0 := jointWorkBound_of_lt_569 (by decide)

example : jointWorkBound 569 =
    ((32 * 569 - 1 : Nat) : ℝ≥0∞) / ((16 * 2 ^ 128 : Nat) : ℝ≥0∞) +
      34 * (1591788895347057694892543 : ℝ≥0∞) / (2 ^ 256) :=
  jointWorkBound_of_middle (by decide) (by decide)

example : jointWorkBound (2 ^ 127) = 1 := jointWorkBound_of_ge_two_pow le_rfl

example (adv : Game.Adversary FIPS205.Answer (PublicKeyCore FIPS205.core)) {q : Nat}
    (low : 569 ≤ q) (high : q < 2 ^ 127) (life : Game.WithinSigningLimit FIPS205.scheme adv)
    (cap : (Game.securityGame FIPS205.scheme).HasQueryBound () Game.adversaryWork adv q) :
    (Game.securityGame FIPS205.scheme).advantage () adv < (q : ℝ≥0∞) / (2 ^ 127) :=
  (slhDsa_sufCma_le adv q life cap).trans_lt (jointWorkBound_lt_of_middle low high)

end SLHDSA.SHAKE128s
