/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import LatticeCrypto.MLKEM.KEM
public import VCVio.CryptoFoundations.FujisakiOkamoto.Composed

/-!
# ML-KEM Security Interfaces

This file packages the implicit-rejection primitive `J` as a PRF scheme and presents ML-KEM
through the generic Fujisaki–Okamoto construction.

A complete IND-CCA theorem additionally requires a concrete K-PKE correctness bound, a fixed
decisional MLWE problem, explicit adversary reductions, and a Fujisaki–Okamoto bound whose error
terms use nonnegative types. Those ingredients are not consequences of the interface packaging
provided here.

## References

- NIST FIPS 203, Section 3.2 (security properties)
- HHK17: A Modular Analysis of the Fujisaki-Okamoto Transformation (TCC 2017)
- CRYSTALS-KYBER (TCHES 2018), Section 3 (security analysis)
-/

@[expose] public section


open OracleComp OracleSpec ENNReal AsymmEncAlg

namespace MLKEM

variable (params : Params) (ring : NTTRingOps) (encoding : Encoding params)
  (prims : Primitives params encoding)

/-! ### ML-KEM IND-CCA Security -/

section IND_CCA

variable [DecidableEq Message] [DecidableEq (KPKE.Ciphertext params encoding)]
  [SampleableType Message] [SampleableType Coins] [SampleableType SharedSecret]

/-- The PRF scheme modeling the implicit-rejection function `J(z ‖ c)` from FIPS 203.

The key space is `Seed32` (the fallback seed `z` stored in the decapsulation key), the domain
is the ciphertext type, and the range is `SharedSecret`. -/
def prfJ : PRFScheme Seed32 (KPKE.Ciphertext params encoding) SharedSecret where
  keygen := $ᵗ Seed32
  eval z c := prims.jReject z c.uEncoded c.vEncoded

/-- The Fujisaki-Okamoto-constructed KEM scheme derived from K-PKE with implicit rejection via J.

This is ML-KEM viewed through the HHK17 framework: encryption coins and shared keys are derived
from random oracles `H₁ : M →ₒ R` (coins) and `H₂ : M →ₒ K` (key derivation), with the key
derivation input being just the message (`kdInput m c = m`). Implicit rejection uses the PRF `J`.

In the concrete ML-KEM instantiation, both `H₁` and `H₂` are derived from a single hash function
`G(m ‖ H(ek))`, which can be modeled via `FujisakiOkamoto.singleRO`. This definition uses the
two-random-oracle formulation to expose the two derivation steps independently. -/
noncomputable abbrev foKEMScheme :=
  FujisakiOkamoto
    (KPKE.asExplicitCoins params ring encoding prims)
    (fun (m : Message) (_c : KPKE.Ciphertext params encoding) => m)
    (FujisakiOkamoto.implicitRejection (prfJ params encoding prims))

end IND_CCA

end MLKEM
