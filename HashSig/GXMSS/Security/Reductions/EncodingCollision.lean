/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Security.Reductions.MerkleCollision

/-!
# Successful encoding target-collision bound

Returned Game 1 wins lost at Game 2 are bounded by the encoding target-collision reduction.
The signing-query bound counts repeated and failed calls and preserves missing mass.
-/

public section

namespace GXMSS.Unforgeability

open Encoding ENNReal OracleComp OracleSpec TweakableHash

variable {PP T X H M R : Type} {h w v : ℕ}

/-- The successful-record Game 1 to Game 2 hop using the fixed target-collision reduction.
The pathwise signing bound counts repeated and failed queries. The inequality compares returned
native mass without conditioning on termination or on successful retries. -/
@[expose]
def SuccessfulEncodingTargetCollisionBound
    [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (qs K : ℕ)
    (adv : Reductions.SchemeAdversary PP H M R h v) : Prop :=
  SigningQueryBound qs adv →
    Reductions.gameOneAdvantage hash enc K adv ≤
      Reductions.gameTwoAdvantage hash enc K adv +
        Encoding.TargetCollisionResistance.advantage
          (Reductions.encodingTargetCollisionReduction hash enc qs K adv)

/-- Returned Game 1 wins lost at Game 2 are charged to the successful recorded encoding target
in the authoritative collision game. -/
theorem successful_encoding_target_collision_bound
    [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (qs K : ℕ)
    (adv : Reductions.SchemeAdversary PP H M R h v) :
    SuccessfulEncodingTargetCollisionBound hash enc qs K adv := by
  intro hbound
  exact (Reductions.gameOneAdvantage_le_gameTwo_add_successfulDifference
    hash enc K adv).trans (add_le_add_right
      (Reductions.successfulEncodingDifferenceMass_le_encodingTargetCollisionAdvantage
        hash enc qs K adv hbound) _)

end GXMSS.Unforgeability
