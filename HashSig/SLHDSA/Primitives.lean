/-
Copyright (c) 2026 Nicolas Consigny. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolas Consigny
-/

module
public import HashSig.SLHDSA.Address

/-!
# SLH-DSA Primitive Interfaces

The abstract bundle of the six SLH-DSA hash/PRF functions (FIPS 205 §4.1), keeping the
hash family opaque while the WOTS+/XMSS/FORS/hypertree layers are defined generically over it.
A concrete instantiation (SHA-2 / SHAKE / keccak) supplies the fields later in a `Concrete`
layer without touching the proof-level development.

The carrier types are abstract fields of the bundle, mirroring how `MLDSA.Primitives` carries
abstract `High`/`Hint` types:

| field | FIPS 205 | role |
|---|---|---|
| `Thash`  | `T_ℓ(PK.seed, ADRS, Mₗ)`         | shared tweakable-hash collection |
| `PRF`    | `PRF(PK.seed, SK.seed, ADRS)`    | WOTS+/FORS secret values |
| `PRFmsg` | `PRF_msg(SK.prf, opt_rand, M)`   | message randomizer `R` |
| `Hmsg`   | `H_msg(R, PK.seed, PK.root, M)`  | message digest (`m` bytes) |

## A note on correctness vs. security

Unlike `MLDSA.Primitives`, this bundle carries **no algebraic `Laws`**: SLH-DSA correctness
(`verify ∘ sign = accept`) is a *deterministic hash-tree consistency identity* that holds for
**any** choice of the opaque hash fields — it reduces to the fact that `wotsPkFromSig`/
`computeRoot` re-fold the *same* `F`/`H`/`Tl` at the *same* addresses the honest signer used,
provable by structural induction with no hash hypotheses. The cryptographic assumptions needed
for unforgeability concern pseudorandomness of `PRF`/`PRFmsg`, multi-target collision and
decisional second-preimage resistance of the tweakable hashes, and interleaved target subset
resilience of `Hmsg`. `HashSig.SLHDSA.Security` packages the primitive families into generic
VCVio interfaces.

## References

- NIST FIPS 205, §4.1 (the six functions), §11 (their instantiations)
-/

@[expose] public section


namespace SLHDSA

/-- The SLH-DSA tweakable-hash / PRF bundle (FIPS 205 §4.1), abstract in the seed, secret, and
node carrier types.  `F`, `H = T₂`, and `T_ℓ` are not independent fields: they are arity-specific
views of one `Thash` collection, keyed by the exact address encoding used by the instantiation. -/
structure Primitives (p : Params) where
  /-- Public seed type (`PK.seed`). -/
  PkSeed : Type
  /-- Secret seed type (`SK.seed`), expanded by `PRF` into WOTS+/FORS secret values. -/
  SkSeed : Type
  /-- Message-PRF key type (`SK.prf`), keyed into `PRFmsg`. -/
  SkPrf : Type
  /-- Node / hash-output type (`n`-byte values: seeds, chain values, tree nodes, roots). -/
  Y : Type
  /-- Fixed-width canonical address key used by this instantiation. -/
  AdrsKey : Type
  /-- Canonicalize a structural address into the exact fixed-width key hashed by the
  instantiation.  SHA-2 uses `Bytes 22`; SHAKE uses `Bytes 32`. -/
  adrsToKey : Adrs → AdrsKey
  /-- The single variable-arity tweakable-hash collection underlying `F`, `H = T₂`, and `T_ℓ`.
  The ordered list length and contents are part of its input. -/
  Thash : PkSeed → AdrsKey → List Y → Y
  /-- `PRF(PK.seed, SK.seed, ADRS)`: derive a WOTS+/FORS secret value. -/
  PRF : PkSeed → SkSeed → Adrs → Y
  /-- `PRF_msg(SK.prf, opt_rand, M)`: derive the message randomizer `R`. -/
  PRFmsg : SkPrf → Y → List Byte → Y
  /-- `H_msg(R, PK.seed, PK.root, M)`: the `m`-byte message digest. -/
  Hmsg : Y → PkSeed → Y → List Byte → Bytes p.m
  /-- Expose the `n`-byte encoding of a node, so WOTS+/FORS can extract base-`w`/`a` digits
  from a node via `base2b` (the only byte-level bridge needed by the abstract layer). -/
  yToBytes : Y → Bytes p.n

namespace Primitives

variable {p : Params}

/-- `F(PK.seed, ADRS, M₁) = T₁(PK.seed, ADRS, [M₁])`. -/
@[reducible] def F (prims : Primitives p) (pkSeed : prims.PkSeed) (adrs : Adrs)
    (x : prims.Y) : prims.Y :=
  prims.Thash pkSeed (prims.adrsToKey adrs) [x]

/-- `H(PK.seed, ADRS, Mₗ ‖ Mᵣ) = T₂(PK.seed, ADRS, [Mₗ, Mᵣ])`. -/
@[reducible] def H (prims : Primitives p) (pkSeed : prims.PkSeed) (adrs : Adrs)
    (left right : prims.Y) : prims.Y :=
  prims.Thash pkSeed (prims.adrsToKey adrs) [left, right]

/-- `T_ℓ(PK.seed, ADRS, M)` for an ordered variable-length node list. -/
@[reducible] def Tl (prims : Primitives p) (pkSeed : prims.PkSeed) (adrs : Adrs)
    (xs : List prims.Y) : prims.Y :=
  prims.Thash pkSeed (prims.adrsToKey adrs) xs

end Primitives

end SLHDSA
