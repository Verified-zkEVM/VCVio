/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.RoutedSplit
public import HashSig.SLHDSA.SHAKE128s.Proof.CanonicalSignature
public import HashSig.SLHDSA.SHAKE128s.Proof.RandomizerGate

/-!
# The replay case is the signer's own signature, and so is no win

`RoutedSplit.cases_of_win_three` leaves one branch standing: a forgery whose FORS part and
hypertree are the ones the signer writes for the digest it carries, whose fourteen positions are
all disclosed, and whose own message input is the only disclosure. This file closes that branch.

The argument is short once the pieces are named. Disclosure is read off the signing log, so
`SelfServed` says the log holds a request whose own framing and own published randomiser name
the forgery's digest input. `ServedLog.entry_of_servedLog` reads that request back out of the
input — `Hashing.messageInput` is injective in each of its parts, so the entry's framing is the
forgery's message and the entry's randomiser is the forgery's randomiser, with no collision
bound anywhere. `LogFaithful` then says the entry's answer is the signature the signer writes
for that message, whose randomiser is therefore the forgery's. A `Signature` has three fields,
and the other two are canonical by hypothesis, so the forgery is `Scheme.signInternal` on the
nose, its bytes are the entry's bytes, and strong freshness is contradicted by the pair the log
returned.

Nothing is charged here. Indexing disclosure by the digest input rather than by the message is
what makes the branch close outright: an adversary that picks its own randomiser for a message
the signer signed names a different input, so it discloses nothing and never reaches this
branch, and a forgery that does reach it is reading the signer's own answer.

The log's faithfulness is the only thing the branch still asks of the game, so it is named here
rather than proved: `LogFaithful` is stated at the cache and the log, the two things the
target's trace carries, and not at the record.
-/

public section

open OracleComp OracleSpec

namespace SlhDsaSecurity.ReplayGate

open Security CanonicalGraph CacheReplay Extraction VerifierProbes SplitCharged RoutedSplit

/-- The secret key the walk's three seeds generate, read from this run's own cache. -/
@[expose] def secretKeyOf (x : Trace) : SecretKey :=
  ⟨x.1.1.1.1, x.1.1.1.2.1, keyOf x⟩

/-! ## What the log says

`LogFaithful` says each entry of the signing log carries the answer the signer computes for its
request, read at this run's own cache — which is the same answer it computed when the request
was made, because the cache only grows and a replayed query reads the entry that is there. -/

/-- Every logged request carries the signer's own answer. -/
@[expose] def LogFaithful (x : Trace) : Prop :=
  ∀ entry ∈ x.1.2.1.signed, ∀ framed : Bytes, entry.1.frame = some framed →
    entry.2 = some
      (@Scheme.signInternal Id Id.instMonad (replayQuery x.2) (secretKeyOf x) framed).toBytes

/-! ## The forgery's own input names a request the signer served -/

/-- **The log entry at the forgery's own digest input.** `SelfServed` names that input and
`Hashing.messageInput` is injective in each of its parts, so the entry's framing is the
forgery's message and the randomiser the signer published for it is the forgery's own. -/
theorem entry_of_replay {x : Trace} {message : Bytes} {parsed : Signature}
    (hself : SelfServed x message parsed) :
    ∃ entry ∈ x.1.2.1.signed, ∃ (bytes : Bytes) (logParsed : Signature),
      entry.1.frame = some message ∧ entry.2 = some bytes ∧
        Signature.fromBytes? bytes = some logParsed ∧
          logParsed.randomizer = parsed.randomizer :=
  ServedLog.entry_of_servedLog (keyOf x) (resultOf x) parsed.randomizer message hself

/-- **The forgery's randomiser is the one the signer derives for its message.** The entry's
answer is the signature the signer writes for that message, and parsing is a function, so the
randomiser the entry published — the forgery's — is the one that signature carries. -/
theorem randomizer_eq_of_replay {x : Trace} {message : Bytes} {parsed : Signature}
    (hfaithful : LogFaithful x) (hself : SelfServed x message parsed) :
    parsed.randomizer =
      @Hashing.randomizer Id Id.instMonad (replayQuery x.2) x.1.1.1.2.1 (keyOf x).seed message := by
  obtain ⟨entry, hentry, bytes, logParsed, hframe, hanswer, hlogParsed, hrandomizer⟩ :=
    entry_of_replay hself
  have hfaith := hfaithful entry hentry message hframe
  rw [hanswer] at hfaith
  rw [Option.some.inj hfaith, Signature.fromBytes_toBytes] at hlogParsed
  rw [← hrandomizer, ← Option.some.inj hlogParsed]
  rfl

/-! ## So the forgery is the signature the signer writes -/

/-- **A replay forgery is `Scheme.signInternal` on its own message.** The randomiser comes from
the log, the other two fields from `CanonicalAt`, and a `Signature` has no fourth field. -/
theorem eq_signInternal_of_replay {x : Trace} {message : Bytes} {parsed : Signature}
    (hfaithful : LogFaithful x) (hcanonical : CanonicalAt x message parsed)
    (hself : SelfServed x message parsed) :
    parsed = @Scheme.signInternal Id Id.instMonad (replayQuery x.2) (secretKeyOf x) message := by
  refine @CanonicalSignature.eq_signInternal (replayQuery x.2) (secretKeyOf x) message parsed
    (randomizer_eq_of_replay hfaithful hself) hcanonical.2.1 ?_
  rw [hcanonical.2.2, ← hcanonical.1]
  rfl

/-- **So a replay forgery does not win.** The log holds its message framed, with the bytes of
that very signature as the answer, and strong freshness excludes the returned pair. -/
theorem not_wins_of_replay {x : Trace} (hfaithful : LogFaithful x)
    (hreplay : ReplayForgery x) : ¬ Wins x.1.2.1 := by
  obtain ⟨message, parsed, hframe, hparsed, hcanonical, hself⟩ := hreplay
  obtain ⟨entry, hentry, -, -, hentryFrame, -, -, -⟩ := entry_of_replay hself
  intro hwin
  exact @CanonicalSignature.not_fresh_of_canonical (replayQuery x.2) (secretKeyOf x)
    x.1.2.1.signed x.1.2.1.forgery message parsed hparsed
    (eq_signInternal_of_replay hfaithful hcanonical hself)
    ⟨entry, hentry, Message.frame_injective hentryFrame hframe,
      hfaithful entry hentry message hentryFrame⟩ hwin.2

/-! ## The split the target asks for

With the replay case closed, a win on a good walk is one of two events, and the log's
faithfulness is the only thing the split still asks of the game. -/

attribute [local irreducible] WarmedGame.afterSeeds WarmedGame.graphWalk WarmedGame.tail
  WarmedGame.warmedRun Scheme.keygenInternal Scheme.verify Scheme.sign
  Security.signingOracle Security.countQueries

/-- **A win on a good walk is the answer side or the input side.** -/
theorem cases_of_win_charged (adversary : Adversary)
    {walk : ((Digest × Digest × Digest) × Cells) × QueryCache HashSpec}
    (hwalk : walk ∈ support WarmedGame.graphWalk)
    {result : (Outcome × Nat) × QueryCache HashSpec}
    (hresult : result ∈ support (WarmedGame.tail adversary walk))
    (hfaithful : LogFaithful ((walk.1, result.1), result.2))
    (hwin : Wins result.1.1) :
    AnswerBad ((walk.1, result.1), result.2) ∨ InputBad ((walk.1, result.1), result.2) := by
  rcases cases_of_win_three adversary hwalk hresult hwin with hanswer | hinput | hreplay
  · exact Or.inl hanswer
  · exact Or.inr hinput
  · exact absurd hwin (not_wins_of_replay hfaithful hreplay)

end SlhDsaSecurity.ReplayGate
