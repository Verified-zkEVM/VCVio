/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Statement.Security

/-!
# The proof's game is the generic game at the proof's model

The security proof is carried out on a direct transcription of SLH-DSA-SHAKE-128s
(`HashSig.SLHDSA.SHAKE128s.Statement.Scheme`) and its unforgeability game
(`HashSig.SLHDSA.SHAKE128s.Statement.Security`). `model` packages that transcription as a
`Game.ExternalScheme`; its generic game is the proof's game, so the bit-security statements agree
(`hasSecurityBits_model_iff`).
-/

@[expose] public section

open OracleComp OracleSpec

namespace SlhDsaSecurity.Bridge

/-- The proof's transcription of SLH-DSA-SHAKE-128s, as a pure-mode scheme over one oracle with
`240`-bit answers. -/
noncomputable def model : Game.ExternalScheme HashOutput PublicKey SecretKey where
  keygen := Scheme.keygen
  sign := Scheme.sign
  verify := Scheme.verify

/-- The proof's game is the generic game at `model`. -/
theorem securityGame_model : Security.securityGame = Game.securityGame model := rfl

/-- The proof's bit-security statement is the generic one at `model`. -/
theorem hasSecurityBits_model_iff (Z : Finset Xmss.Unforgeability.QueryKind) (bits : Nat) :
    Security.HasSecurityBits Z bits ↔ Game.HasSecurityBits model Z bits := Iff.rfl

end SlhDsaSecurity.Bridge
