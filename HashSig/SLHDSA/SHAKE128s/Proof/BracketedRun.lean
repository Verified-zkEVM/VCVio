/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.ServingForget
public import HashSig.SLHDSA.SHAKE128s.Proof.LateProbes
public import HashSig.SLHDSA.SHAKE128s.Proof.CountedHandler

/-!
# What a bracketed tail is, and why the predicate looks like this

A recorder run is `simulateQ (recorder …) computation` for some
`computation : OracleComp OracleWorld _`. A carrier tail cannot be one: the brackets write the
state between queries, and an `OracleComp OracleWorld` can only sample or query. So the notion
has to widen, and this file holds the pieces of the widening.

**It is three stages, and the three-stage shape is forced by the recording, not by the
plumbing.** `PhaseFusion.fuse`'s `inl` branch runs `inner` before `outer`, and `inner` here is
`recordedAdversaryImpl + recordedSigningOracle` — so lifting key generation into the fused
computation would charge key generation's queries to the adversary's record and count them as
its work. Key generation and verification therefore run under the handler *directly*, and only
the adversary's phase is fused.

**The brackets' one condition is the lemma's.** The brackets have to leave the cache alone and
leave both recordings alone — exactly the hypotheses of `ServingForget.run_fuseServing_map`.
`Bracket` is defined to be what that lemma asks for, so the side condition and the lemma that
uses it cannot drift.

**The state is the counted one.** A bracketed game is not a single computation, so there is
nothing for `countAllHashes` to wrap and the count lives in the handler's state —
`CountedHandler` says why. That fixes the shape to `HandlerCarrier.State × ((Record × Record) ×
Nat)`: the carrier first, because `ServedAgreement.Files` reads it there; the recordings next,
because the recorder writes them; the count last, because nothing but the value reads it.
-/

public section

open OracleComp OracleSpec

namespace SLHDSA.SHAKE128s.BracketedRun

open Security RecorderView PhaseFusion CountedHandler

/-- The walk a tail is read at. -/
abbrev Walk : Type :=
  ((Digest × Digest × Digest) × CanonicalGraph.Cells) × QueryCache HashSpec

/-- The state a counted recorder runs over: carrier, two recordings, count. -/
abbrev CountedState : Type :=
  HandlerCarrier.State × ((DigestTape.Record × DigestTape.Record) × Nat)

variable {ω : Type} [Monoid ω]

/-- **The brackets touch neither the cache nor either recording.** The one condition a bracket
has to meet, and the one `ServingForget.run_fuseServing_map` asks for. -/
@[expose] def Bracket (f : CountedState → CountedState) : Prop :=
  ∀ state : CountedState, (f state).1.cache = state.1.cache ∧ (f state).2.1 = state.2.1

/-- The projection a bracketed run is read through: the cache and the two recordings. The
carrier's served set and framing go, and so does the count, which the value carries instead. -/
@[expose] def forgetCarrier (state : CountedState) : SplitPrefix.SplitState :=
  (state.1.cache, state.2.1)

end SLHDSA.SHAKE128s.BracketedRun
