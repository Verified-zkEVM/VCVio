/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.ServedLog
public import HashSig.SLHDSA.SHAKE128s.Proof.ServingCarrier
public import HashSig.SLHDSA.SHAKE128s.Proof.CacheProvenance
public import HashSig.SLHDSA.SHAKE128s.Proof.RandomizerGate
public import HashSig.SLHDSA.SHAKE128s.Proof.AddressBounds
public import HashSig.SLHDSA.SHAKE128s.Proof.SigningFaithful

/-!
# The carrier's served set and the log's, where they meet

The input half's charge reads availability at the handler's carrier; the extraction's events
read disclosure from the signing log, which is in the `Outcome` already. This file relates the
two: `CarrierBelowLog` is the containment the composition needs, `signerRandomised_of_servedLog`
shows that a logged served input passes the recorder's disclosing test, and
`sign_messageShape_randomizer` is the one `Scheme.sign` fact the agreement turns on.

**Which direction the composition needs.** `Served ⊆ servedLog`: a smaller served set makes
more cells unavailable, hence a bigger `InputBad`, so the charge covers the extraction's event
exactly when the carrier serves no more than the log does.

**What the agreement turns on.** A filed input is a query the signer made while serving a
framing, of that framing's own digest shape. For it to be the log's served input, the randomiser
in it has to be the one the signer published — and `sign_messageShape_randomizer` is that: on a
good walk the digest query is the *only* query `Scheme.sign` makes of that shape. The randomiser
query is excluded by length, the structural queries by `HashSeparation`, and nothing else is
left. This is a fact about `Scheme.sign`, so it holds at every moment of a request and needs no
run.
-/

@[expose] public section

open OracleComp OracleSpec

namespace SlhDsaSecurity.ServedBridge

open Security CacheReplay

attribute [local irreducible] WarmedGame.afterSeeds WarmedGame.tail
  Scheme.sign Scheme.keygenInternal Scheme.verify

/-! ## The one `Scheme.sign` fact the agreement turns on -/

/-- A request's own randomiser input is not of its own digest shape: the digest input carries
`PK.root` before the framing and the randomiser input does not, so they differ in length. -/
theorem randomizerInput_ne_messageInput (prf randomizer : Digest) (pk : PublicKey)
    (framed : Bytes) :
    Hashing.randomizerInput prf pk.seed framed ≠
      Hashing.messageInput randomizer pk framed := by
  intro heq
  rw [RandomizerGate.messageInput_eq_randomizerInput] at heq
  obtain ⟨-, -, hframed⟩ := Hashing.randomizerInput_injective heq
  have hlength := congrArg List.length hframed
  rw [List.length_append, length_bytesBE] at hlength
  have hn : 0 < n := by decide
  omega

/-- **The signer's only query of its own request's digest shape is its digest query.**

So an input filed while that request is being served carries the randomiser the signer derived,
which is the one its published signature holds. The structural queries are excluded by
`HashSeparation` once the key is no coincidence, and the randomiser query by length. -/
theorem sign_messageShape_randomizer (cache : QueryCache HashSpec) (sk : SecretKey)
    (request : Message) (framed : Bytes) (hframe : request.frame = some framed)
    (hpublic : ¬ HashSeparation.Possible (sk.publicKey.seed, sk.publicKey.root))
    (randomizer : Digest)
    (hprobe : QueriesUnder cache (Scheme.sign (m := OracleComp HashSpec) sk request)
      (Hashing.messageInput randomizer sk.publicKey framed)) :
    randomizer = HonestProbes.replayRandomizer cache sk framed := by
  rcases HonestProbes.probes_sign cache sk request framed hframe _ hprobe with
    ⟨parent, hparent⟩ | hmessage
  · exact absurd hparent (HashSeparation.message_tweakable_ne hpublic
      (withinBounds_structural parent))
  · rcases hmessage with hrandomiser | hdigest
    · exact absurd hrandomiser.symm (randomizerInput_ne_messageInput sk.prf randomizer
        sk.publicKey framed)
    · exact (Hashing.messageInput_injective hdigest).1

/-! ## The containment the composition needs -/

/-- **What the composition needs**: the carrier serves no more than the log does. -/
def CarrierBelowLog (pk : PublicKey) (state : ServingCarrier.Carrier)
    (result : (Outcome × Nat) × QueryCache HashSpec) : Prop :=
  ∀ input : Bytes, ServingCarrier.Served state input → ServedLog.servedLog pk result input

/-! ## The log's side, at a run

What a served input has to match. `ServedLog.servedLog` asks for a log entry whose answer parses
to a signature whose randomiser the input carries; a logged, served request supplies all three,
and the randomiser it supplies is the one the signer derived — which is
`SigningFaithful.logFaithful_tail` read as a statement about the served set rather than about
bytes. -/

/-- The randomiser a replayed signature carries is the one the cache replays. -/
theorem signInternal_randomizer (cache : QueryCache HashSpec) (sk : SecretKey)
    (framed : Bytes) :
    (@Scheme.signInternal Id Id.instMonad (replayQuery cache) sk framed).randomizer =
      HonestProbes.replayRandomizer cache sk framed := rfl

/-! ## The log and the recorder's disclosing test

`ServedLog.servedLog` says the signer served this input; `SplitWitness.disclosingKeep` is
`CacheAvailability.SignerRandomised`, which says the *cache* shows the signer randomised it. A
logged request's answer is the signature the signer published, so the input the log names is
built from the randomiser the signer derived; and the request's own `PRF_msg` entry is in the
cache by `SigningFaithful.randomiserCached_tail`, which is what `SignerRandomised` asks for.

The converse is not a fact about the log: `SignerRandomised` reads only the cache, so an
adversary that knows `SK.prf` makes it hold by querying `Hashing.randomizerInput SK.prf PK.seed m`
itself, with no request behind it. That direction is the randomiser defect's absence, and no
amount of log faithfulness reaches it. -/

/-- **A logged served input passes the recorder's disclosing test.** -/
theorem signerRandomised_of_servedLog (adversary : Adversary)
    {walk : ((Digest × Digest × Digest) × CanonicalGraph.Cells) × QueryCache HashSpec}
    {result : (Outcome × Nat) × QueryCache HashSpec}
    (hresult : result ∈ support (WarmedGame.tail adversary walk))
    (sk : SecretKey) (pk : PublicKey)
    (hsk : sk = ReplayGate.secretKeyOf ((walk.1, result.1), result.2))
    (hpk : pk = RoutedSplit.keyOf ((walk.1, result.1), result.2))
    (input : Bytes) (hserved : ServedLog.servedLog pk result input) :
    CacheAvailability.SignerRandomised sk.prf pk result.2 input := by
  subst hsk
  subst hpk
  obtain ⟨entry, hentry, framed, bytes, parsed, hframe, hanswer, hparsed, rfl⟩ := hserved
  have hfaithful := SigningFaithful.logFaithful_tail adversary hresult entry hentry framed hframe
  have hbytes : bytes =
      (@Scheme.signInternal Id Id.instMonad (replayQuery result.2)
        (ReplayGate.secretKeyOf ((walk.1, result.1), result.2)) framed).toBytes :=
    Option.some.inj (hanswer.symm.trans hfaithful)
  have hparsedEq : parsed =
      @Scheme.signInternal Id Id.instMonad (replayQuery result.2)
        (ReplayGate.secretKeyOf ((walk.1, result.1), result.2)) framed := by
    rw [hbytes, Signature.fromBytes_toBytes] at hparsed
    exact (Option.some.inj hparsed).symm
  have hcached := SigningFaithful.randomiserCached_tail adversary hresult entry hentry framed
    hframe
  cases hentryValue : result.2 (Hashing.randomizerInput
      (ReplayGate.secretKeyOf ((walk.1, result.1), result.2)).prf
      (ReplayGate.secretKeyOf ((walk.1, result.1), result.2)).publicKey.seed framed) with
  | none => exact absurd hentryValue hcached
  | some prfAnswer =>
    refine ⟨framed, prfAnswer, hentryValue, ?_⟩
    rw [hparsedEq, signInternal_randomizer, HonestProbes.replayRandomizer]
    simp [replay, hentryValue]

end SlhDsaSecurity.ServedBridge
