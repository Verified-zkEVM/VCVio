/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
-- frontier: CslibFrontier.Crypto.Computational.Encryption.Basic

public import CslibFrontier.Crypto.Computational.Encryption.Basic

/-! # Message order at the two-stage ElGamal adversary interface -/

public section

namespace VCVioFrontier.ElGamal

open Cslib.Crypto.Encryption

/-- VCVio selects the first component on a true challenge bit. Frontier calls this message
`msg₁` and the false-branch message `msg₀`. Both stages share the saved adversary state. -/
@[expose] def oneTimeChoice {M W : Type} (encode : M → W) (choice : ChoiceOut M) :
    W × W × List Bool :=
  (encode (ChoiceOut.msg₁ choice), encode (ChoiceOut.msg₀ choice), ChoiceOut.state choice)

/-- Encode both typed messages and the saved state into Frontier’s phase-one response. -/
@[expose] def encodeChoice {M W S : Type} (encode : M → W) (state : S → List Bool)
    (choice : M × M × S) : ChoiceOut W :=
  ((encode choice.2.1, encode choice.1), state choice.2.2)

/-- Returning to VCVio’s convention preserves both encoded messages and their joint state. -/
@[simp] theorem oneTimeChoice_encodeChoice {M W S : Type} (encode : M → W)
    (state : S → List Bool) (choice : M × M × S) :
    oneTimeChoice id (encodeChoice encode state choice) =
      (encode choice.1, encode choice.2.1, state choice.2.2) := rfl

end VCVioFrontier.ElGamal
