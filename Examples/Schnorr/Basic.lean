/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import VCVio.Schemes.Schnorr.BoundedChallenges
public import Mathlib.Algebra.Field.ZMod

/-!
# Reading a Schnorr transcript

The scalar field itself gives a small additive group for checking the transcript arithmetic.
With secret key 42, nonce 7 and challenge 3, the response is 32 modulo 101. This example
illustrates the verification equation; the tiny group provides no computational security.
The reusable protocol, simulator and reductions live under `VCVio/Schemes/Schnorr/`.
-/

public section

namespace Examples.Schnorr

local instance : Fact (Nat.Prime 101) := ⟨by decide⟩

-- Verify the public key, commitment, challenge and response in that order.
example : (_root_.Schnorr.sigma (ZMod 101) (ZMod 101) 1).verify 42 7 3 32 = true := by
  decide

-- The library's completeness theorem applies to every honest transcript in this group.
example : (_root_.Schnorr.sigma (ZMod 101) (ZMod 101) 1).PerfectlyComplete :=
  _root_.Schnorr.sigma_complete _ _ _

-- A four-bit challenge can be embedded without identifying two different challenges.
example : Function.Injective (_root_.Schnorr.boundedChallenge 101 16) :=
  _root_.Schnorr.boundedChallenge_injective _ _ (by decide)

end Examples.Schnorr
