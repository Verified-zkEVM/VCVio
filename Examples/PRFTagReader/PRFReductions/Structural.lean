/-
Copyright (c) 2026 Oleksandr Vovkotrub. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oleksandr Vovkotrub
-/

module

public import Examples.PRFTagReader.PRFReductions.IdealHandlers
public import VCVio.ProgramLogic.Unary.WP.Qualitative
import VCVio.ProgramLogic.Unary.HandlerSpecs
import VCVio.ProgramLogic.Unary.WP.QualitativeSpecs

/-!
# PRF Tag/Reader Protocol — Structural `query_bind` Reductions

Structural `query_bind`-decomposition lemmas for the composed ideal handlers (turning the
coupling induction into a sequence of `bind`-decomposition steps), together with per-query
reductions and `bad` monotonicity for `unlinkBadQueryImpl`. The monotonicity is a structural
triple proved by core `vcgen` and lifted to whole runs by `simulateQ_triple_preserves_invariant`.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal

namespace PRFTagReader

section UnlinkReduction

variable {TagId Nonce Digest K : Type} {sessionsPerTag : ℕ}
  [DecidableEq TagId] [Fintype TagId] [DecidableEq Nonce] [SampleableType Nonce]
  [DecidableEq Digest] [SampleableType Digest]

/-! ### Structural reductions of the composed ideal handlers on a `query_bind`

The next two lemmas expose `simulateQ … (query_bind t f)` run from a state as a single monadic
`bind`: the per-query handler applied to the head, then the recursive `simulateQ` of the
continuation threaded through the resulting state. They are pure rewriting facts (`simulateQ` is a
monad morphism), and they turn the coupling induction into a sequence of `bind`-decomposition
steps that the bind-comparison bounds (such as `prEvent_bind_le_add_bad_disagree`) can attack. -/

/-- `simulateQ multipleIdealQueryImpl` of a `query_bind`, run from a state and projected to its
output bit, is the per-query handler followed by the recursive simulation of the continuation. -/
lemma multipleIdeal_run'_query_bind
    (t : (UnlinkOracleSpec TagId Nonce Digest).Domain)
    (f : (UnlinkOracleSpec TagId Nonce Digest).Range t → UnlinkAdversary TagId Nonce Digest)
    (sM : UnlinkState TagId × ((TagId × Nonce) →ₒ Digest).QueryCache) :
    (simulateQ (multipleIdealQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag)) (liftM (OracleSpec.query t) >>= f)).run' sM =
      (multipleIdealQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag) t sM) >>= fun p =>
        (simulateQ (multipleIdealQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
          (sessionsPerTag := sessionsPerTag)) (f p.1)).run' p.2 := by
  rw [simulateQ_query_bind, StateT.run'_eq, StateT.run_bind, map_bind]
  rfl

/-- `simulateQ singleIdealQueryImpl` of a `query_bind`, run from a state and projected to its
output bit, is the per-query handler followed by the recursive simulation of the continuation. -/
lemma singleIdeal_run'_query_bind
    (t : (UnlinkOracleSpec TagId Nonce Digest).Domain)
    (f : (UnlinkOracleSpec TagId Nonce Digest).Range t → UnlinkAdversary TagId Nonce Digest)
    (sS : UnlinkState TagId × (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest).QueryCache) :
    (simulateQ (singleIdealQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag)) (liftM (OracleSpec.query t) >>= f)).run' sS =
      (singleIdealQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag) t sS) >>= fun p =>
        (simulateQ (singleIdealQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
          (sessionsPerTag := sessionsPerTag)) (f p.1)).run' p.2 := by
  rw [simulateQ_query_bind, StateT.run'_eq, StateT.run_bind, map_bind]
  rfl

/-- `simulateQ unlinkBadQueryImpl` of a `query_bind`, run from a state, is the per-query handler
followed by the recursive simulation of the continuation threaded through the resulting state. -/
lemma unlinkBad_run_query_bind
    (t : (UnlinkOracleSpec TagId Nonce Digest).Domain)
    (f : (UnlinkOracleSpec TagId Nonce Digest).Range t → UnlinkAdversary TagId Nonce Digest)
    (sB : UnlinkBadState TagId Nonce Digest) :
    (simulateQ (unlinkBadQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag)) (liftM (OracleSpec.query t) >>= f)).run sB =
      (unlinkBadQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag) t sB) >>= fun p =>
        (simulateQ (unlinkBadQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
          (sessionsPerTag := sessionsPerTag)) (f p.1)).run p.2 := by
  rw [simulateQ_query_bind, StateT.run_bind]
  rfl

/-- `unlinkBadQueryImpl` on a tag query with the slot budget exhausted: returns `none`, state
unchanged. -/
lemma unlinkBadQueryImpl_tag_run_of_not_lt (tag : TagId)
    (sB : UnlinkBadState TagId Nonce Digest)
    (hslot : ¬ sB.sessionsUsed tag < sessionsPerTag) :
    (unlinkBadQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag) (Sum.inl tag)) sB = pure (none, sB) := by
  unfold unlinkBadQueryImpl
  rw [QueryImpl.add_apply_inl]
  change (unlinkBadTagQueryImpl tag).run sB = _
  unfold unlinkBadTagQueryImpl
  simp [hslot]

/-- `unlinkBadQueryImpl` on a tag query with a free slot: sample a nonce and a fresh digest,
record the digest under `(tag, nonce)`, set the `bad` flag if `(tag, nonce)` was already cached,
and advance the session counter. -/
lemma unlinkBadQueryImpl_tag_run_of_lt (tag : TagId)
    (sB : UnlinkBadState TagId Nonce Digest)
    (hslot : sB.sessionsUsed tag < sessionsPerTag) :
    (unlinkBadQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag) (Sum.inl tag)) sB =
      ($ᵗ Nonce) >>= fun nonce =>
        ($ᵗ Digest) >>= fun auth =>
          pure (some (⟨nonce, auth⟩ : TagTranscript Nonce Digest),
            ({ sessionsUsed :=
                Function.update sB.sessionsUsed tag (sB.sessionsUsed tag + 1)
               responses := sB.responses.cacheQuery (tag, nonce)
                 (auth :: Option.getD (sB.responses (tag, nonce)) [])
               bad := sB.bad || (sB.responses (tag, nonce)).isSome
               cacheBad := sB.cacheBad } :
              UnlinkBadState TagId Nonce Digest)) := by
  unfold unlinkBadQueryImpl
  rw [QueryImpl.add_apply_inl]
  change (unlinkBadTagQueryImpl tag).run sB = _
  unfold unlinkBadTagQueryImpl
  simp [hslot]

/-- `unlinkBadQueryImpl` on a reader query: deterministic acceptance against the recorded
random-function responses, state untouched. -/
lemma unlinkBadQueryImpl_reader_run (transcript : TagTranscript Nonce Digest)
    (sB : UnlinkBadState TagId Nonce Digest) :
    (unlinkBadQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag) (Sum.inr transcript)) sB =
      pure (ReaderReply.ofBool (decide (∃ tag ∈ (Finset.univ : Finset TagId),
        transcript.auth ∈ ((sB.responses (tag, transcript.nonce)).getD []))), sB) := by
  unfold unlinkBadQueryImpl
  rw [QueryImpl.add_apply_inr]
  change (unlinkBadReaderQueryImpl transcript).run sB = _
  unfold unlinkBadReaderQueryImpl
  simp

section BadMonotone

open Std.WP OracleComp.ProgramLogic

/-- The `bad` flag of `unlinkBadQueryImpl` is monotone, as a structural triple: a query answered
from a state with `bad = true` ends in a state with `bad = true`. -/
theorem unlinkBadQueryImpl_triple_bad (t : (UnlinkOracleSpec TagId Nonce Digest).Domain) :
    ⦃ fun s => s.bad = true ⦄
      unlinkBadQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag) t
    ⦃ fun _ s' => s'.bad = true ⦄ := by
  rw [unlinkBadQueryImpl]
  delta UnlinkOracleSpec
  rcases t with tag | tr <;> vcgen [unlinkBadTagQueryImpl, unlinkBadReaderQueryImpl] with finish

/-- The `bad` flag of `unlinkBadQueryImpl` is monotone: a single per-query step started from a
state with `bad = true` keeps `bad = true`. -/
lemma unlinkBadQueryImpl_step_preserves_bad
    (t : (UnlinkOracleSpec TagId Nonce Digest).Domain)
    (sB : UnlinkBadState TagId Nonce Digest) (hbad : sB.bad = true) :
    ∀ z ∈ support ((unlinkBadQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag) t) sB), z.2.bad = true :=
  fun _ hz => (triple_stateT_iff_forall_support _ _ _ ⊥).1
    (unlinkBadQueryImpl_triple_bad t) sB hbad _ _ hz

/-- The `bad` flag of a full `simulateQ unlinkBadQueryImpl` run is monotone: started from a state
with `bad = true` the run keeps `bad = true`. The per-query triple
`unlinkBadQueryImpl_triple_bad` lifts to the whole run by
`simulateQ_triple_preserves_invariant`. -/
lemma simulateQ_unlinkBad_preserves_bad
    (adv : UnlinkAdversary TagId Nonce Digest)
    (sB : UnlinkBadState TagId Nonce Digest) (hbad : sB.bad = true) :
    ∀ z ∈ support ((simulateQ (unlinkBadQueryImpl (TagId := TagId) (Nonce := Nonce)
        (Digest := Digest) (sessionsPerTag := sessionsPerTag)) adv).run sB), z.2.bad = true :=
  fun _ hz => (triple_stateT_iff_forall_support _ _ _ ⊥).1
    (simulateQ_triple_preserves_invariant _ _ unlinkBadQueryImpl_triple_bad adv) sB hbad _ _ hz

end BadMonotone

end UnlinkReduction

end PRFTagReader
