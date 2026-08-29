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
abstraction that the SLH-DSA / SPHINCS+ functions `F`, `H`, and `T_ℓ` instantiate (with the tweak
being the canonical encoded `ADRS` key), and against which their multi-target security notions
(`VCVio.CryptoFoundations.HardnessAssumptions.MultiTarget`) are stated.

This file provides the data abstractions only; the security games live in `MultiTarget`.
`TweakableHashCollection` packages members with a common public-seed, tweak, and digest space,
but possibly different message spaces.  This is the structure needed for hash-based signatures:
challenge queries to one member may depend on evaluations of other members under the same hidden
public seed.

With `Tweak := Unit` this is definitionally a keyed hash family
(`seedGen : ProbComp PkSeed`, `eval : PkSeed → M → Y`), so nothing is lost relative to the
existing `KeyedHashFamily` surface.
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

/-- A collection of tweakable hash functions sharing one public seed, tweak space, and digest
space.  The message type may depend on the collection member.  For the SLH-DSA public hash
collection, the index records the input arity and `Message i` is the type of exactly `i` nodes. -/
structure TweakableHashCollection (PkSeed Tweak Y : Type) where
  /-- Names of the functions in the collection. -/
  Index : Type
  /-- Message space of each collection member. -/
  Message : Index → Type
  /-- Evaluate a member of the collection. -/
  eval : (i : Index) → PkSeed → Tweak → Message i → Y

namespace TweakableHash

variable {PkSeed Tweak Y : Type}

/-- The two-input node hash `(left ‖ right) ↦ digest` at a fixed seed and tweak, as used to
combine sibling nodes in a Merkle tree. -/
def nodeHash (th : TweakableHash PkSeed Tweak (Y × Y) Y) (pk : PkSeed) (t : Tweak)
    (l r : Y) : Y :=
  th.eval pk t (l, r)

end TweakableHash

namespace TweakableHashCollection

variable {PkSeed Tweak Y : Type}

/-- A typed query to any member of a tweakable-hash collection. -/
structure Query (collection : TweakableHashCollection PkSeed Tweak Y) where
  /-- The queried collection member. -/
  index : collection.Index
  /-- The public tweak. -/
  tweak : Tweak
  /-- A message in the selected member's message space. -/
  message : collection.Message index

/-- Explicit oracle interface for evaluating an entire tweakable-hash collection. -/
@[reducible] def oracleSpec (collection : TweakableHashCollection PkSeed Tweak Y) :
    OracleSpec (Query collection) := fun _ => Y

end TweakableHashCollection
