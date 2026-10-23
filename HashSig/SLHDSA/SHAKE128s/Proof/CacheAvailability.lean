/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.ClaimedProbes
public import HashSig.SLHDSA.SHAKE128s.Proof.CoverageTail
public import HashSig.SLHDSA.SHAKE128s.Proof.OpenCache
public import HashSig.SLHDSA.SHAKE128s.Proof.RecordedBudget

/-!
# Availability, read off the cache

`OpenCache.lazyProgram` reads availability off the cache it carries, while
`CanonicalGraph.Available` is parameterised by the digits the signatures reveal and the FORS
positions they disclose. This file supplies the instance, and the two halves are supplied for
quite different reasons.

**The WOTS half does not depend on the run at all.** Each WOTS key of the hypertree signs exactly
one message — the honest node one layer below it — so the digit a signature on that key discloses is
a function of the seeds, not of which messages were requested. `GraphStakes.honestRevealed` is that
digit. Treating a chain as revealed up to that digit before any signature is issued is an
over-approximation of availability, and the residue reduction is unaffected: it leaves the forgery
holding a value *strictly below* that digit, which is unavailable either way.

**The FORS half is about the signing log, which the cache does not carry — but it determines
it.** Signing a message puts that message's `H_msg` input in the cache, and the digest cached
there is exactly what selects the fourteen FORS positions the signature opens. So "this
position was disclosed" is "some cached message-class input's answer selects it", a function of
the cache alone. The adversary can cache a message-class input without having had it signed, so
this over-approximates the signing log too — and that over-approximation is precisely the
coverage event, which `CoverageTail` charges separately. The fork in
`GraphStakes.forsSecret_signed_or_not_obtainable` is where the two meet.

**What monotonicity this supports, and what it does not.** `signedAt` reads cache *values*, so
it is monotone along growth that preserves entries: a cached answer is never rewritten, and a
position a cached digest selects stays selected. It is **not** monotone along growth of the
cache's domain alone, because that relation permits the answer at an input to change, and a
different answer selects different positions. No sound instance can be, since which positions a
digest opens is not a function of which inputs were asked.
-/

@[expose] public section

open OracleComp OracleSpec

namespace SlhDsaSecurity.CacheAvailability

open CanonicalGraph

/-! ## Entries that survive

The growth relation this file is monotone along: an entry already in the cache is still there,
with the same answer. It is what a run of the lazy handler actually does, and it is strictly
stronger than the growth of the cache's domain. -/

/-- Every entry of the first cache is still present, with its answer, in the second. -/
def Persists (left right : QueryCache HashSpec) : Prop :=
  ∀ (probe : Bytes) (value : HashOutput), left probe = some value → right probe = some value

/-- Every cache persists into itself. -/
theorem Persists.refl (cache : QueryCache HashSpec) : Persists cache cache := fun _ _ h => h

/-- Persistence composes. -/
theorem Persists.trans {left middle right : QueryCache HashSpec} (hfirst : Persists left middle)
    (hsecond : Persists middle right) : Persists left right :=
  fun probe value hvalue => hsecond probe value (hfirst probe value hvalue)

/-! ## The FORS positions a cache discloses

A digest discloses the positions it selects only if the *signer* computed it, and the cache says
whether it did: the signer derives the randomiser before the digest, so the `PRF_msg` entry at
`randomizerInput` is in the cache too, and the digest's randomiser is its truncation. Counting
every cached message-class digest instead would let the adversary pick a randomiser of its own,
query the digest itself, and so declare its own fourteen positions disclosed — which charges
nothing and makes the claim at them unavailable, so neither half of the budget sees it.

The gate this creates is that the adversary can make such an entry by querying at
`randomizerInput SK.prf PK.seed M`, which carries `SK.prf` in the clear. That is a guess at the
PRF seed, and it is not a canonical input, so neither of the charges here meets it: it belongs
to the `PRF_msg` class at the real seed and is charged on a class of its own.

**That charge is not taken here.** A guess at `SK.prf` cannot be charged at a fixed walk at all —
the walk fixes the secret and an adversary may carry it as a constant — so it is taken at
`Target.pairedRun`, where the seed is still random. -/

/-- A message input whose randomiser is the one the signer derives for that message, with the
derivation's own query in the cache. -/
def SignerRandomised (prfSeed : Digest) (pk : PublicKey) (cache : QueryCache HashSpec)
    (input : Bytes) : Prop :=
  ∃ (message : Bytes) (prfAnswer : HashOutput),
    cache (Hashing.randomizerInput prfSeed pk.seed message) = some prfAnswer ∧
      input = Hashing.messageInput (Hashing.truncate prfAnswer) pk message

open scoped Classical in
/-- **The FORS positions some cached digest of the signer's own discloses.** -/
noncomputable def signedAt (prfSeed : Digest) (pk : PublicKey) (cache : QueryCache HashSpec)
    (key : ForsKey) : Finset (Fin (forsTrees * 2 ^ forsHeight)) :=
  Finset.univ.filter fun index =>
    ∃ (input : Bytes) (answer : HashOutput), SignerRandomised prfSeed pk cache input ∧
      cache input = some answer ∧ SplitCharged.forsKeyOfDigest answer = key ∧
      ∃ tree : Fin forsTrees,
        GraphStakes.forsIndex (MessageDigest.forsIndices answer) tree = index

attribute [local irreducible] signedAt

/-! ## Availability -/

variable [HasQuery HashSpec Id]

/-! ## The handler keeps its entries

The growth `signedAt` is monotone along is the growth a run of the lazy handler performs: a hash
query either reads the cache, leaving it alone, or writes an input the cache had no entry at. -/

open OpenCache

end SlhDsaSecurity.CacheAvailability
