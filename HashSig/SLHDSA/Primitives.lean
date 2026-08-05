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
| `F`      | `F(PK.seed, ADRS, M₁)`            | chain step / FORS leaf hash |
| `H`      | `H(PK.seed, ADRS, M₂)` (`= T₂`)  | binary Merkle / FORS-tree node |
| `Tl`     | `T_ℓ(PK.seed, ADRS, Mₗ)`         | WOTS-pk and FORS-roots compression |
| `PRF`    | `PRF(PK.seed, SK.seed, ADRS)`    | WOTS+/FORS secret values |
| `PRFmsg` | `PRF_msg(SK.prf, opt_rand, M)`   | message randomizer `R` |
| `Hmsg`   | `H_msg(R, PK.seed, PK.root, M)`  | message digest (`m` bytes) |

## A note on correctness vs. security

Unlike `MLDSA.Primitives`, this bundle carries **no algebraic `Laws`**: SLH-DSA correctness
(`verify ∘ sign = accept`) is a *deterministic hash-tree consistency identity* that holds for
**any** choice of the opaque hash fields — it reduces to the fact that `wotsPkFromSig`/
`computeRoot` re-fold the *same* `F`/`H`/`Tl` at the *same* addresses the honest signer used,
provable by structural induction with no hash hypotheses. The cryptographic assumptions
(pseudorandomness of `PRF`/`PRFmsg`; multi-target preimage/target-collision resistance of
`F`/`H`/`Tl`) are needed only for *unforgeability* and are stated in `HashSig.SLHDSA.Security`
against the generic `VCVio.CryptoFoundations` tweakable-hash / multi-target surfaces.

## References

- NIST FIPS 205, §4.1 (the six functions), §11 (their instantiations)
-/

@[expose] public section


namespace SLHDSA

/-- The SLH-DSA tweakable-hash / PRF bundle (FIPS 205 §4.1), abstract in the seed, secret, and
node carrier types. Each function takes the public seed and a 32-byte address tweak (`Adrs`). -/
structure Primitives (p : Params) where
  /-- Public seed type (`PK.seed`). -/
  PkSeed : Type
  /-- Secret seed type (`SK.seed`), expanded by `PRF` into WOTS+/FORS secret values. -/
  SkSeed : Type
  /-- Message-PRF key type (`SK.prf`), keyed into `PRFmsg`. -/
  SkPrf : Type
  /-- Node / hash-output type (`n`-byte values: seeds, chain values, tree nodes, roots). -/
  Y : Type
  /-- `F(PK.seed, ADRS, M₁)`: one-block tweakable hash (WOTS+ chain step, FORS leaf). -/
  F : PkSeed → Adrs → Y → Y
  /-- `H(PK.seed, ADRS, Mₗ ‖ Mᵣ)`: two-block tweakable hash (`= T₂`, Merkle/FORS node). -/
  H : PkSeed → Adrs → Y → Y → Y
  /-- `T_ℓ(PK.seed, ADRS, M)`: compress a list of nodes
  (WOTS-pk over `len` chain ends, FORS roots over `k` trees). -/
  Tl : PkSeed → Adrs → List Y → Y
  /-- `PRF(PK.seed, SK.seed, ADRS)`: derive a WOTS+/FORS secret value. -/
  PRF : PkSeed → SkSeed → Adrs → Y
  /-- `PRF_msg(SK.prf, opt_rand, M)`: derive the message randomizer `R`. -/
  PRFmsg : SkPrf → Y → List Byte → Y
  /-- `H_msg(R, PK.seed, PK.root, M)`: the `m`-byte message digest. -/
  Hmsg : Y → PkSeed → Y → List Byte → Bytes p.m
  /-- Expose the `n`-byte encoding of a node, so WOTS+/FORS can extract base-`w`/`a` digits
  from a node via `base2b` (the only byte-level bridge needed by the abstract layer). -/
  yToBytes : Y → Bytes p.n

end SLHDSA
