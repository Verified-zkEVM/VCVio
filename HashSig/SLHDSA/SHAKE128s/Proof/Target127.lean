/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.LateProvenance
public import HashSig.SLHDSA.SHAKE128s.Proof.RedrawCell
public import HashSig.SLHDSA.SHAKE128s.Proof.SignerRandomiser
public import HashSig.SLHDSA.SHAKE128s.Proof.SharedJoin
public import HashSig.SLHDSA.SHAKE128s.Proof.KeygenValue
public import HashSig.SLHDSA.SHAKE128s.Proof.ServedBridge
public import HashSig.SLHDSA.SHAKE128s.Proof.ServingCarrier
public import HashSig.SLHDSA.SHAKE128s.Proof.ChargedProbe
public import HashSig.SLHDSA.SHAKE128s.Proof.RecordedStripping
public import HashSig.SLHDSA.SHAKE128s.Proof.RecordedWalkTable
public import HashSig.SLHDSA.SHAKE128s.Proof.TableTail
public import HashSig.SLHDSA.SHAKE128s.Proof.TouchedKeys
public import HashSig.SLHDSA.SHAKE128s.Proof.CanonicalGraph.Input
public import HashSig.SLHDSA.SHAKE128s.Proof.HashSeparation
public import HashSig.SLHDSA.SHAKE128s.Proof.CarrierTail
public import HashSig.SLHDSA.SHAKE128s.Proof.Target
public import HashSig.SLHDSA.SHAKE128s.Proof.SigningFaithful

/-!
# The defect event of the `127` ledger: the seed guess and the signer's coincidence

This file defines the event `late` that the answer half is allowed to exclude and the shared
half pays for: `late := PrfHit ∨ SignerHit`, some query the adversary or the verifier made is a
`PRF_msg` input at the walk's `SK.prf`, or some signature's randomiser *is* `SK.prf`.

**The seed guess is the charge that stays.** With `SK.prf` in hand an adversary computes the
digest of any message before asking for its signature, and so chooses which signatures to request
by where their FORS leaves land: covering one target's fourteen leaves at its own instance takes
about `2 ^ 78` queries, after which the forgery is certain. So a query spent finding `SK.prf` buys
a forgery, at one stake per query, and the charge on the record's `PRF_msg` candidates is real.

**The ordering defect is not part of it.** A pre-queried digest that a later signature serves is
one whose randomiser the adversary guessed before the `PRF_msg` answer existed; that answer is a
fresh draw, so the event is thinned by `2 ^ -128` *on top of* whatever coverage it helps, and its
total effect is second order. The answer half absorbs it inside its own column, with nothing
excluded but the seed guess.

**The signer's coincidence is there because it keeps the seed hop's blind game blind**: when the
signer's own digest query happens to be a `PRF_msg` input at the real seed, the game reads the
seed through the signer and not through the adversary.

**The shared half is one obligation, not a sum of two.** A guess charge in the real order —
secret drawn first — is false at the expected count of the real run: an adversary that stops
guessing once it has hit makes `Pr[hit]` exceed `E[guesses] / 2 ^ 128` by a second-order amount.
The count has to be taken in the blind game, where the secret is drawn after the run. Two such
charges taken in two blind games cannot be added inside one record, since each count is bounded
by the record pathwise but only in its own game. So the input half's aiming guesses and the
`SK.prf` guesses are counted in **one** game blind to both, where `aiming + candidates ≤ record`
holds pathwise.
-/

public section

open OracleComp OracleSpec ENNReal

namespace SlhDsaSecurity.Target127

open Security WarmedGame Target SharedJoin RandomiserRecord LateProbes

/-- An input whose first `n` bytes are the encoding of `seed`. -/
@[expose] def SeedPrefixed (seed : Digest) (input : Bytes) : Prop :=
  ∃ rest : Bytes, input = bytesBE n seed ++ rest

/-- **The seed guess.** Some query of the adversary or the verifier is a `PRF_msg` input at the
walk's `SK.prf`. -/
@[expose] def PrfHit (pair : RecordedPair) : Prop :=
  RecordMeetsPrfClass pair.1.1.1.2.1 pair.2

/-- **The signer's coincidence**: some signature's randomiser is the walk's `SK.prf`. -/
@[expose] def SignerHit (pair : RecordedPair) : Prop :=
  RandomiserProvenance.SignerHitsSeed pair.1.1.1.2.1 pair.1.1.1.2.2 pair.2.2 pair.2.1.1.1.signed

/-- **The defect at the recorded pair**: the seed guess or the signer's coincidence. -/
@[expose] def Late (pair : RecordedPair) : Prop := PrfHit pair ∨ SignerHit pair

/-- **The defect at the split pair**, read through the recordings' forgetting. -/
@[expose] def late (pair : SplitPair) : Prop := Late (forgetRecordings pair)

/-- A `PRF_msg` input at `prf` is prefixed by `prf`. -/
theorem seedPrefixed_of_prfClass {prf : Digest} {input : Bytes}
    (hprf : RandomizerGate.PrfClass prf input) : SeedPrefixed prf input := by
  obtain ⟨seed, message, rfl⟩ := hprf
  exact ⟨bytesBE n seed ++ message, by simp [Hashing.randomizerInput, List.append_assoc]⟩

/-- Two seeds' prefixes are the same prefix only when the seeds are equal. -/
theorem eq_of_seedPrefixed {left right : Digest} {input : Bytes}
    (hleft : SeedPrefixed left input) (hright : SeedPrefixed right input) : left = right := by
  obtain ⟨leftRest, rfl⟩ := hleft
  obtain ⟨rightRest, hsame⟩ := hright
  have htake := congrArg (List.take n) hsame
  simp only [List.take_left' (length_bytesBE n left), List.take_left' (length_bytesBE n right)]
    at htake
  exact bytesBE_injective n htake

end SlhDsaSecurity.Target127
