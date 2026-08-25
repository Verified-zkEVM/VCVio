/-
Copyright (c) 2026 Nicolas Consigny. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolas Consigny
-/

module
public import HashSig.SLHDSA.Scheme
public import VCVio.CryptoFoundations.PRF
public import VCVio.CryptoFoundations.TweakableHash

/-!
# SLH-DSA Cryptographic Primitive Families

This module packages the hash and pseudorandom-function primitives used by `slhdsaAlg` into the
generic `TweakableHash` and `PRFScheme` interfaces:

- `Primitives.fHash` and `Primitives.hHash` expose `F` and `H` as tweakable hash families with
  `Adrs` as the tweak;
- `Primitives.msgPrfScheme` exposes the message randomizer `PRF_msg`; and
- `Primitives.skPrfScheme` exposes the secret-value derivation function `PRF` at a public seed.

These packages identify the primitive families to which an SLH-DSA security reduction applies.
An aggregate EUF-CMA theorem additionally needs seed-aware SM-TCR and SM-DSPR games, an `H_msg`
interleaved-target-subset-resilience game, explicit reductions from the forger, and checked query
bounds. Primitive packaging alone does not supply those ingredients.

## References

- Bernstein, Hülsing, Kölbl, Niederhagen, Rijneveld, Schwabe, "The SPHINCS+ Signature Framework"
- Hülsing, Rijneveld, Song, Schwabe, "Mitigating Multi-Target Attacks in Hash-Based Signatures"
- NIST FIPS 205, §10 (security)
-/

@[expose] public section


open OracleComp OracleSpec ENNReal

namespace SLHDSA

variable {p : Params} (prims : Primitives p)

/-! ### The SLH-DSA hashes as tweakable hash families / PRFs -/

/-- The chain-step / FORS-leaf hash `F` as a tweakable hash family (tweak = `Adrs`). -/
def Primitives.fHash [SampleableType prims.PkSeed] :
    TweakableHash prims.PkSeed Adrs prims.Y prims.Y where
  seedGen := $ᵗ prims.PkSeed
  eval := prims.F

/-- The Merkle / FORS-tree node hash `H` as a tweakable hash family (tweak = `Adrs`, message =
the ordered sibling pair `(left, right)`). -/
def Primitives.hHash [SampleableType prims.PkSeed] :
    TweakableHash prims.PkSeed Adrs (prims.Y × prims.Y) prims.Y where
  seedGen := $ᵗ prims.PkSeed
  eval := fun pkSeed adrs m => prims.H pkSeed adrs m.1 m.2

/-- The message randomizer `PRF_msg` as a `PRFScheme` keyed by `SK.prf`; `eval` is
`prims.PRFmsg`. -/
def msgPrfScheme [SampleableType prims.SkPrf] :
    PRFScheme prims.SkPrf (prims.Y × List Byte) prims.Y where
  keygen := $ᵗ prims.SkPrf
  eval := fun skPrf rm => prims.PRFmsg skPrf rm.1 rm.2

/-- The secret-value `PRF` at public seed `pkSeed` as a `PRFScheme` keyed by `SK.seed`; `eval` is
`prims.PRF pkSeed`. -/
def skPrfScheme [SampleableType prims.SkSeed] (pkSeed : prims.PkSeed) :
    PRFScheme prims.SkSeed Adrs prims.Y where
  keygen := $ᵗ prims.SkSeed
  eval := fun skSeed adrs => prims.PRF pkSeed skSeed adrs

end SLHDSA
