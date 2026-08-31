/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import HashSig.SLHDSA.Security.Architecture
public import HashSig.SLHDSA.Security.GeneralScheme

/-!
# SLH-DSA strong-unforgeability canaries

These examples distinguish the three freshness cases used by the exact SUF-CMA event partition.
They use two requests and two signatures so a replay, new request, and same-request/new-signature
candidate have different observable outcomes.
-/

public section

namespace SLHDSA.SecurityTest

def request0 : Security.MessageInput := ⟨.pure, [], [0]⟩
def request1 : Security.MessageInput := ⟨.pure, [], [1]⟩

def signed : List (Security.MessageInput × Nat) := [(request0, 7)]

/-- A new request is fresh for both EUF-CMA and SUF-CMA, even with a reused signature value. -/
example : Security.Fresh (signed.map Prod.fst) request1 ∧
    Security.StrongFresh signed (request1, 7) := by
  simp [Security.Fresh, Security.StrongFresh, signed, request0, request1]

/-- Replaying the exact request/signature answer is not strongly fresh. -/
example : ¬ Security.StrongFresh signed (request0, 7) := by
  simp [Security.StrongFresh, signed]

/-- A distinct signature on an already signed request is precisely the same-message residual. -/
example : Security.SameMessageNewSignature signed (request0, 8) := by
  simp [Security.SameMessageNewSignature, Security.StrongFresh, signed]

/-- The generic probability identity elaborates at the actual arbitrary-depth scheme interface;
no one-layer adapter or second signature representation is needed. -/
example (vp : ValidatedParams) (prims : Primitives vp.params)
    [SampleableType prims.SkSeed] [SampleableType prims.SkPrf]
    [SampleableType prims.PkSeed] [SampleableType prims.Y]
    [DecidableEq prims.PkSeed] [DecidableEq prims.Y]
    (encode : Security.MessageInput → List Byte)
    (adversary : Security.ClassicalAdversary prims
      (GeneralScheme.securityInterface vp prims encode)) :
    Security.sufAdvantage prims (GeneralScheme.securityInterface vp prims encode)
        encode adversary =
      Security.eufAdvantage prims (GeneralScheme.securityInterface vp prims encode)
          encode adversary +
        Security.sameMessageAdvantage prims (GeneralScheme.securityInterface vp prims encode)
          encode adversary :=
  Security.sufAdvantage_eq_eufAdvantage_add_sameMessageAdvantage _ _ _ _

end SLHDSA.SecurityTest
