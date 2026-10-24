/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Examples.PRFTagReader.Table
public import VCVio.ProgramLogic.Library

/-!
# Specifications for the PRF tag/reader table handlers

Specifications for the deterministic-table handlers `PRFTagReader.multipleTableHandler g` and
`PRFTagReader.singleTableHandler g` of `Examples.PRFTagReader.Table`, under the necessary reading
(`open scoped OracleComp.Necessary`).

* *Support.* `mem_support_*_tag_iff` and `mem_support_*_reader_iff` (in `simulateQ_nf`): a tag
  query with a free session slot draws any nonce, answers the table's digest at the session's
  slot and uses up the slot; with the slots exhausted it answers `none`; a reader query is the
  deterministic acceptance test and keeps the state.
* *One query.* `*_wp_tag` (`spec high`) quantifies over the answer and final state that the
  support description allows (one branch, which `vcgen` needs to continue); `*_wp_reader` names
  the answer.
* *Whole runs.* Both handlers are `QueryImpl.MonotoneState` for "every session counter only
  grows, and stays within `sessionsPerTag` once it is": `vcgen` frames an opaque adversary, and
  `MonotoneState.rel_of_mem_support` bounds the counters of every run.
-/

@[expose] public section

open OracleSpec OracleComp OracleComp.ProgramLogic Std.WP

open scoped OracleComp.Necessary

namespace PRFTagReader

variable {TagId Nonce Digest : Type} {sessionsPerTag : ℕ} [DecidableEq TagId] [Fintype TagId]
  [SampleableType Nonce] [DecidableEq Digest]

local notation "USpec" => UnlinkOracleSpec TagId Nonce Digest

/-! ## The single-session table handler -/

section single

variable (g : (TagId × Fin sessionsPerTag) × Nonce → Digest)

private theorem mem_support_singleTableHandler_tag_aux {tag : TagId} {s s' : UnlinkState TagId}
    {r : Option (TagTranscript Nonce Digest)} :
    (r, s') ∈ support (α := Option (TagTranscript Nonce Digest) × UnlinkState TagId)
      (singleTableHandler g (.inl tag) s) ↔
      (∃ h : s.sessionsUsed tag < sessionsPerTag, ∃ nonce,
        r = some ⟨nonce, g ((tag, ⟨s.sessionsUsed tag, h⟩), nonce)⟩ ∧
          s' = ⟨Function.update s.sessionsUsed tag (s.sessionsUsed tag + 1)⟩) ∨
      (¬ s.sessionsUsed tag < sessionsPerTag ∧ r = none ∧ s' = s) := by
  by_cases h : s.sessionsUsed tag < sessionsPerTag
  · rw [singleTableHandler_tag_run_of_lt g tag s h]
    simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff, Prod.mk.injEq,
      support_uniformSample, Set.mem_univ, true_and]
    aesop
  · rw [singleTableHandler_tag_run_of_not_lt g tag s h]
    simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq]
    aesop

/-- A reachable single-session tag step uses up the next slot of the tag, answering the table's
digest at that slot for some nonce, or answers `none` once the slots are exhausted. -/
@[simulateQ_nf]
theorem mem_support_singleTableHandler_tag_iff {tag : TagId} {s s' : UnlinkState TagId}
    {r : (USpec).Range (.inl tag)} :
    (r, s') ∈ support ((singleTableHandler g (.inl tag)).run s) ↔
      (∃ h : s.sessionsUsed tag < sessionsPerTag, ∃ nonce,
        r = some ⟨nonce, g ((tag, ⟨s.sessionsUsed tag, h⟩), nonce)⟩ ∧
          s' = ⟨Function.update s.sessionsUsed tag (s.sessionsUsed tag + 1)⟩) ∨
      (¬ s.sessionsUsed tag < sessionsPerTag ∧ r = none ∧ s' = s) :=
  mem_support_singleTableHandler_tag_aux g

private theorem mem_support_singleTableHandler_reader_aux {t : TagTranscript Nonce Digest}
    {s s' : UnlinkState TagId} {r : ReaderReply} :
    (r, s') ∈ support (α := ReaderReply × UnlinkState TagId) (singleTableHandler g (.inr t) s) ↔
      r = ReaderReply.ofBool (unlinkReaderAccepts (Slot := TagId × Fin sessionsPerTag)
        (fun slot nonce => g (slot, nonce)) (singlePattern sessionsPerTag) t) ∧ s' = s := by
  rw [singleTableHandler_reader_run g t s, support_pure, Set.mem_singleton_iff, Prod.mk.injEq]

/-- A reachable single-session reader step is the acceptance test, keeping the state. -/
@[simulateQ_nf]
theorem mem_support_singleTableHandler_reader_iff {t : TagTranscript Nonce Digest}
    {s s' : UnlinkState TagId} {r : (USpec).Range (.inr t)} :
    (r, s') ∈ support ((singleTableHandler g (.inr t)).run s) ↔
      r = ReaderReply.ofBool (unlinkReaderAccepts (Slot := TagId × Fin sessionsPerTag)
        (fun slot nonce => g (slot, nonce)) (singlePattern sessionsPerTag) t) ∧ s' = s :=
  mem_support_singleTableHandler_reader_aux g

/-- One single-session tag query, exactly. -/
@[spec high]
theorem singleTableHandler_wp_tag (tag : TagId)
    (post : (USpec).Range (.inl tag) → UnlinkState TagId → Prop) {epost : EStack⟨⟩} :
    ⦃ fun s => ∀ r s', ((∃ h : s.sessionsUsed tag < sessionsPerTag, ∃ nonce,
        r = some ⟨nonce, g ((tag, ⟨s.sessionsUsed tag, h⟩), nonce)⟩ ∧
          s' = ⟨Function.update s.sessionsUsed tag (s.sessionsUsed tag + 1)⟩) ∨
        (¬ s.sessionsUsed tag < sessionsPerTag ∧ r = none ∧ s' = s)) → post r s' ⦄
      singleTableHandler g (.inl tag) ⦃ post; epost ⦄ :=
  (triple_stateT_iff_forall_mem_support _ _ _ _).2 fun _ h r s' hz =>
    h r s' ((mem_support_singleTableHandler_tag_iff g).1 hz)

/-- One single-session reader query: the acceptance test, the state unchanged. -/
@[spec high]
theorem singleTableHandler_wp_reader (t : TagTranscript Nonce Digest)
    (post : (USpec).Range (.inr t) → UnlinkState TagId → Prop) {epost : EStack⟨⟩} :
    ⦃ fun s => post (ReaderReply.ofBool (unlinkReaderAccepts (Slot := TagId × Fin sessionsPerTag)
        (fun slot nonce => g (slot, nonce)) (singlePattern sessionsPerTag) t)) s ⦄
      singleTableHandler g (.inr t) ⦃ post; epost ⦄ :=
  (triple_stateT_iff_forall_mem_support _ _ _ _).2 fun _ h r s' hz => by
    obtain ⟨rfl, rfl⟩ := (mem_support_singleTableHandler_reader_iff g).1 hz
    exact h

/-- The single-session table handler only grows its session counters, within the cap. -/
instance monotoneState_singleTableHandler :
    (singleTableHandler g).MonotoneState
      fun s s' => (∀ tag, s.sessionsUsed tag ≤ s'.sessionsUsed tag) ∧
        ((∀ tag, s.sessionsUsed tag ≤ sessionsPerTag) →
          ∀ tag, s'.sessionsUsed tag ≤ sessionsPerTag) where
  refl _ := ⟨fun _ => le_rfl, id⟩
  trans _ _ _ h₁ h₂ := ⟨fun t => (h₁.1 t).trans (h₂.1 t), h₂.2 ∘ h₁.2⟩
  step t s := by
    rintro ⟨r, s'⟩ hz
    rcases t with tag | t
    · rcases (mem_support_singleTableHandler_tag_iff g).1 hz with ⟨h, -, -, rfl⟩ | ⟨-, -, rfl⟩
      · refine ⟨fun t => ?_, fun hs t => ?_⟩ <;> rcases eq_or_ne t tag with rfl | ht <;>
          simp_all
      · exact ⟨fun _ => le_rfl, id⟩
    · obtain ⟨-, rfl⟩ := (mem_support_singleTableHandler_reader_iff g).1 hz
      exact ⟨fun _ => le_rfl, id⟩

end single

/-! ## The multiple-session table handler -/

section multiple

variable (g : TagId × Nonce → Digest)

private theorem mem_support_multipleTableHandler_tag_aux {tag : TagId} {s s' : UnlinkState TagId}
    {r : Option (TagTranscript Nonce Digest)} :
    (r, s') ∈ support (α := Option (TagTranscript Nonce Digest) × UnlinkState TagId)
      (multipleTableHandler (sessionsPerTag := sessionsPerTag) g (.inl tag) s) ↔
      (s.sessionsUsed tag < sessionsPerTag ∧ ∃ nonce, r = some ⟨nonce, g (tag, nonce)⟩ ∧
          s' = ⟨Function.update s.sessionsUsed tag (s.sessionsUsed tag + 1)⟩) ∨
      (¬ s.sessionsUsed tag < sessionsPerTag ∧ r = none ∧ s' = s) := by
  by_cases h : s.sessionsUsed tag < sessionsPerTag
  · rw [multipleTableHandler_tag_run_of_lt g tag s h]
    simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff, Prod.mk.injEq,
      support_uniformSample, Set.mem_univ, true_and]
    aesop
  · rw [multipleTableHandler_tag_run_of_not_lt g tag s h]
    simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq]
    aesop

/-- A reachable multiple-session tag step answers the table's digest at the tag for some nonce
and uses up a slot, or answers `none` once the slots are exhausted. -/
@[simulateQ_nf]
theorem mem_support_multipleTableHandler_tag_iff {tag : TagId} {s s' : UnlinkState TagId}
    {r : (USpec).Range (.inl tag)} :
    (r, s') ∈ support ((multipleTableHandler (sessionsPerTag := sessionsPerTag) g
      (.inl tag)).run s) ↔
      (s.sessionsUsed tag < sessionsPerTag ∧ ∃ nonce, r = some ⟨nonce, g (tag, nonce)⟩ ∧
          s' = ⟨Function.update s.sessionsUsed tag (s.sessionsUsed tag + 1)⟩) ∨
      (¬ s.sessionsUsed tag < sessionsPerTag ∧ r = none ∧ s' = s) :=
  mem_support_multipleTableHandler_tag_aux g

private theorem mem_support_multipleTableHandler_reader_aux {t : TagTranscript Nonce Digest}
    {s s' : UnlinkState TagId} {r : ReaderReply} :
    (r, s') ∈ support (α := ReaderReply × UnlinkState TagId)
      (multipleTableHandler (sessionsPerTag := sessionsPerTag) g (.inr t) s) ↔
      r = ReaderReply.ofBool (unlinkReaderAccepts (Slot := TagId)
        (fun tag nonce => g (tag, nonce)) (multiplePattern sessionsPerTag) t) ∧ s' = s := by
  rw [multipleTableHandler_reader_run g t s, support_pure, Set.mem_singleton_iff, Prod.mk.injEq]

/-- A reachable multiple-session reader step is the acceptance test, keeping the state. -/
@[simulateQ_nf]
theorem mem_support_multipleTableHandler_reader_iff {t : TagTranscript Nonce Digest}
    {s s' : UnlinkState TagId} {r : (USpec).Range (.inr t)} :
    (r, s') ∈ support ((multipleTableHandler (sessionsPerTag := sessionsPerTag) g
      (.inr t)).run s) ↔
      r = ReaderReply.ofBool (unlinkReaderAccepts (Slot := TagId)
        (fun tag nonce => g (tag, nonce)) (multiplePattern sessionsPerTag) t) ∧ s' = s :=
  mem_support_multipleTableHandler_reader_aux g

/-- One multiple-session tag query, exactly. -/
@[spec high]
theorem multipleTableHandler_wp_tag (tag : TagId)
    (post : (USpec).Range (.inl tag) → UnlinkState TagId → Prop) {epost : EStack⟨⟩} :
    ⦃ fun s => ∀ r s', ((s.sessionsUsed tag < sessionsPerTag ∧ ∃ nonce,
        r = some ⟨nonce, g (tag, nonce)⟩ ∧
          s' = ⟨Function.update s.sessionsUsed tag (s.sessionsUsed tag + 1)⟩) ∨
        (¬ s.sessionsUsed tag < sessionsPerTag ∧ r = none ∧ s' = s)) → post r s' ⦄
      multipleTableHandler (sessionsPerTag := sessionsPerTag) g (.inl tag) ⦃ post; epost ⦄ :=
  (triple_stateT_iff_forall_mem_support _ _ _ _).2 fun _ h r s' hz =>
    h r s' ((mem_support_multipleTableHandler_tag_iff g).1 hz)

/-- One multiple-session reader query: the acceptance test, the state unchanged. -/
@[spec high]
theorem multipleTableHandler_wp_reader (t : TagTranscript Nonce Digest)
    (post : (USpec).Range (.inr t) → UnlinkState TagId → Prop) {epost : EStack⟨⟩} :
    ⦃ fun s => post (ReaderReply.ofBool (unlinkReaderAccepts (Slot := TagId)
        (fun tag nonce => g (tag, nonce)) (multiplePattern sessionsPerTag) t)) s ⦄
      multipleTableHandler (sessionsPerTag := sessionsPerTag) g (.inr t) ⦃ post; epost ⦄ :=
  (triple_stateT_iff_forall_mem_support _ _ _ _).2 fun _ h r s' hz => by
    obtain ⟨rfl, rfl⟩ := (mem_support_multipleTableHandler_reader_iff g).1 hz
    exact h

/-- The multiple-session table handler only grows its session counters, within the cap. -/
instance monotoneState_multipleTableHandler :
    (multipleTableHandler (sessionsPerTag := sessionsPerTag) g).MonotoneState
      fun s s' => (∀ tag, s.sessionsUsed tag ≤ s'.sessionsUsed tag) ∧
        ((∀ tag, s.sessionsUsed tag ≤ sessionsPerTag) →
          ∀ tag, s'.sessionsUsed tag ≤ sessionsPerTag) where
  refl _ := ⟨fun _ => le_rfl, id⟩
  trans _ _ _ h₁ h₂ := ⟨fun t => (h₁.1 t).trans (h₂.1 t), h₂.2 ∘ h₁.2⟩
  step t s := by
    rintro ⟨r, s'⟩ hz
    rcases t with tag | t
    · rcases (mem_support_multipleTableHandler_tag_iff g).1 hz with
        ⟨h, -, -, rfl⟩ | ⟨-, -, rfl⟩
      · refine ⟨fun t => ?_, fun hs t => ?_⟩ <;> rcases eq_or_ne t tag with rfl | ht <;>
          simp_all
      · exact ⟨fun _ => le_rfl, id⟩
    · obtain ⟨-, rfl⟩ := (mem_support_multipleTableHandler_reader_iff g).1 hz
      exact ⟨fun _ => le_rfl, id⟩

end multiple

end PRFTagReader
