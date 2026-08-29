/-
Copyright (c) 2026 Nicolas Consigny. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolas Consigny
-/

module
public import VCVio.OracleComp.ProbComp
public import VCVio.OracleComp.Constructions.SampleableType

/-!
# Tweakable Hash Families

A tweakable hash family `Th : PkSeed → Tweak → M → Y` generalizes `KeyedHashFamily` by
splitting the key into a *sampled* public seed and a *caller-supplied* abstract tweak. It is the
abstraction that the SLH-DSA / SPHINCS+ functions `F`, `H`, and `T_ℓ` instantiate (with the
tweak being the 32-byte address `ADRS`), and against which their multi-target security notions
(`TweakableHash.SM_DT_TCR_Advantage`, `TweakableHash.SM_DT_PRE_Advantage`) are stated.

This file provides the data abstraction only; the security games live under
`HardnessAssumptions/TweakableHash/`. They take a `TweakableHash` whole rather than a
partially-applied function, because `seedGen` is what samples
the public parameter that the game must withhold from the adversary during target selection.

With `Tweak := Unit` this is definitionally a keyed hash family
(`seedGen : ProbComp PkSeed`, `eval : PkSeed → M → Y`), so nothing is lost relative to the
existing `KeyedHashFamily` surface.

## Collections

`TweakableHashCollection` is a family of tweakable hashes sharing one public seed and one tweak
space, differing only in their message types — SLH-DSA's `F`, `H` and `T_ℓ` under one `PK.seed` and
one `ADRS` space. It carries no `seedGen` of its own: a game samples one seed, from the attacked
member's `TweakableHash.seedGen`, and hands it to every member. The security notions under
`HardnessAssumptions/TweakableHash/` are all stated in the collection form, with the stand-alone
notion recovered at an empty index type.
-/

@[expose] public section

open OracleComp

/-- A tweakable hash family: a sampled public seed plus a deterministic evaluation taking a
public seed, a tweak, and a message to a digest. -/
structure TweakableHash (PkSeed Tweak M Y : Type) where
  /-- Sample the public seed `PK.seed`. -/
  seedGen : ProbComp PkSeed
  /-- Evaluate the tweakable hash at a public seed, tweak, and message. -/
  eval : PkSeed → Tweak → M → Y

namespace TweakableHash

variable {PkSeed Tweak Y : Type}

/-- The two-input node hash `(left ‖ right) ↦ digest` at a fixed seed and tweak, as used to
combine sibling nodes in a Merkle tree. -/
def nodeHash (th : TweakableHash PkSeed Tweak (Y × Y) Y) (pk : PkSeed) (t : Tweak)
    (l r : Y) : Y :=
  th.eval pk t (l, r)

end TweakableHash

/-! ## Collections of tweakable hashes -/

/-- A collection of tweakable hashes indexed by `ι`, sharing one public seed, one tweak space and
one digest space, and differing only in their message types. This is the shape of SLH-DSA's `F`, `H`
and `T_ℓ` under a single `PK.seed` and a single `ADRS` space.

There is deliberately no `seedGen` field. A security game samples exactly one seed — from the
`TweakableHash.seedGen` of the member under attack — and evaluates every member at it. A collection
carrying its own sampler would let a game measure the attacked member and the simulated members at
two independent seeds. -/
structure TweakableHashCollection (ι PkSeed Tweak Y : Type) where
  /-- The message type of the member at index `i`. -/
  Msg : ι → Type
  /-- Evaluate the member at index `i` on a public seed, tweak, and message. -/
  eval : (i : ι) → PkSeed → Tweak → Msg i → Y

namespace TweakableHashCollection

/-- The empty collection, indexed by `Empty`. A game instantiated at this collection has a
collection oracle whose query type is uninhabited, hence unqueryable, which is exactly the
stand-alone form of the notion. -/
def empty (PkSeed Tweak Y : Type) : TweakableHashCollection Empty PkSeed Tweak Y where
  Msg i := i.elim
  eval i := i.elim

end TweakableHashCollection
