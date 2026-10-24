/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Examples.PRFTagReader.MultipleToHybrid.EagerSetup
public import VCVio.ProgramLogic.Library

/-!
# Specifications for the eager-table instrumented multiple-session handlers

Specifications for `PRFTagReader.multipleBadTableHandler` and
`PRFTagReader.multipleBadTableHandlerFine` of `Examples.PRFTagReader.MultipleToHybrid.EagerSetup`,
under the necessary reading (`open scoped OracleComp.Necessary`). Both run the table handler
`multipleTableHandler g` on the first state component and advance the bad-world component with
`multipleBadAdvance` on a tag query (and, for the fine handler, `multipleBadReaderAdvance` on a
reader query).

* *One query.* `*_wp_tag` and `*_wp_reader` (`spec high`) read a step through the weakest
  precondition of `multipleTableHandler g`, so `vcgen` continues with its rules from
  `VCVio.ProgramLogic.Library.T3.PRFTagReader.Table`.
* *Support.* `mem_support_*_iff` (in `simulateQ_nf`): a reachable step is a table step with the
  bad-world component advanced.
* *Whole runs.* Both handlers are `QueryImpl.MonotoneState` for "neither bad flag is ever
  lowered", the frame `vcgen` uses for an opaque adversary.
-/

@[expose] public section

open OracleSpec OracleComp OracleComp.ProgramLogic Std.WP

open scoped OracleComp.Necessary

namespace PRFTagReader

section advance

variable {σ τ α : Type} (x : StateT σ ProbComp α) (mx : StateT (σ × τ) ProbComp α)
  (f : α → τ → τ)

/-- A step running `x` on the first component and advancing the second with its answer has the
weakest precondition of `x`. -/
private theorem wp_of_run_eq_bind_advance
    (h : ∀ p, mx.run p = x.run p.1 >>= fun r => pure (r.1, r.2, f r.1 p.2))
    (post : α → σ × τ → Prop) {epost : EStack⟨⟩} :
    ⦃ fun p => wp x (fun a s => post a (s, f a p.2)) epost p.1 ⦄ mx ⦃ post; epost ⦄ :=
  ⟨fun p => by
    rw [StateT.wp_apply_eq, StateT.wp_apply_eq, h, bind_pure_comp]
    exact WPMonad.map_le_wp_map (m := ProbComp) (fun r : α × σ => (r.1, r.2, f r.1 p.2))
      (x.run p.1) (fun z : α × σ × τ => post z.1 z.2) epost⟩

/-- The support form of `wp_of_run_eq_bind_advance`. -/
private theorem mem_support_of_run_eq_bind_advance
    (h : ∀ p, mx.run p = x.run p.1 >>= fun r => pure (r.1, r.2, f r.1 p.2)) {p p' : σ × τ}
    {a : α} : (a, p') ∈ support (mx.run p) ↔ (a, p'.1) ∈ support (x.run p.1) ∧ p'.2 = f a p.2 := by
  rw [h]
  simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff, Prod.exists]
  aesop

end advance

variable {TagId Nonce Digest : Type} [DecidableEq TagId] [DecidableEq Nonce]

/-- A tag advance never lowers either bad flag. -/
theorem multipleBadAdvance_bad_mono (tag : TagId) (sB : UnlinkBadState TagId Nonce Digest)
    (r : Option (TagTranscript Nonce Digest)) :
    (sB.bad = true → (multipleBadAdvance tag sB r).bad = true) ∧
      (sB.cacheBad = true → (multipleBadAdvance tag sB r).cacheBad = true) := by
  cases r <;> simp_all [multipleBadAdvance]

variable {sessionsPerTag : ℕ} [Fintype TagId] [DecidableEq Digest] [SampleableType Nonce]

local notation "USpec" => UnlinkOracleSpec TagId Nonce Digest
local notation "BState" => UnlinkState TagId × UnlinkBadState TagId Nonce Digest

section coarse

variable (g : TagId × Nonce → Digest)

/-- One tag query of the eager instrumented handler: a table tag step, then a tag advance. -/
@[spec high]
theorem multipleBadTableHandler_wp_tag (tag : TagId)
    (post : (USpec).Range (.inl tag) → BState → Prop) {epost : EStack⟨⟩} :
    ⦃ fun p => wp (multipleTableHandler (sessionsPerTag := sessionsPerTag) g (.inl tag))
        (fun a s => post a (s, multipleBadAdvance tag p.2 a)) epost p.1 ⦄
      multipleBadTableHandler sessionsPerTag g (.inl tag) ⦃ post; epost ⦄ :=
  wp_of_run_eq_bind_advance _ (multipleBadTableHandler sessionsPerTag g (.inl tag))
    (fun r sB => multipleBadAdvance tag sB r) (fun _ => rfl) post

/-- One reader query of the eager instrumented handler: a table reader step. -/
@[spec high]
theorem multipleBadTableHandler_wp_reader (t : TagTranscript Nonce Digest)
    (post : (USpec).Range (.inr t) → BState → Prop) {epost : EStack⟨⟩} :
    ⦃ fun p => wp (multipleTableHandler (sessionsPerTag := sessionsPerTag) g (.inr t))
        (fun a s => post a (s, p.2)) epost p.1 ⦄
      multipleBadTableHandler sessionsPerTag g (.inr t) ⦃ post; epost ⦄ :=
  wp_of_run_eq_bind_advance _ (multipleBadTableHandler sessionsPerTag g (.inr t)) (fun _ sB => sB)
    (fun _ => rfl) post

/-- A reachable step of the eager instrumented handler is a table step with the bad-world
component advanced on a tag query. -/
@[simulateQ_nf]
theorem mem_support_multipleBadTableHandler_iff {q : (USpec).Domain} {p p' : BState}
    {a : (USpec).Range q} :
    (a, p') ∈ support ((multipleBadTableHandler sessionsPerTag g q).run p) ↔
      (a, p'.1) ∈ support ((multipleTableHandler (sessionsPerTag := sessionsPerTag) g q).run p.1) ∧
        p'.2 = (match q, a with
          | .inl tag, a => multipleBadAdvance tag p.2 a
          | .inr _, _ => p.2) := by
  rcases q with tag | t
  · exact mem_support_of_run_eq_bind_advance _ (multipleBadTableHandler sessionsPerTag g (.inl tag))
      (fun r sB => multipleBadAdvance tag sB r) (fun _ => rfl)
  · exact mem_support_of_run_eq_bind_advance _ (multipleBadTableHandler sessionsPerTag g (.inr t))
      (fun _ sB => sB) (fun _ => rfl)

/-- The eager instrumented handler never lowers either bad flag. -/
instance monotoneState_multipleBadTableHandler :
    (multipleBadTableHandler sessionsPerTag g).MonotoneState
      fun p p' => (p.2.bad = true → p'.2.bad = true) ∧
        (p.2.cacheBad = true → p'.2.cacheBad = true) where
  refl _ := ⟨id, id⟩
  trans _ _ _ h₁ h₂ := ⟨h₂.1 ∘ h₁.1, h₂.2 ∘ h₁.2⟩
  step q p := by
    rintro ⟨a, p'⟩ hz
    obtain ⟨-, h⟩ := (mem_support_multipleBadTableHandler_iff g).1 hz
    rcases q with tag | t
    · exact h ▸ multipleBadAdvance_bad_mono tag p.2 a
    · exact h ▸ ⟨id, id⟩

end coarse

section fine

variable [NeZero sessionsPerTag] (g : TagId × Nonce → Digest)
  (gFine : ((TagId × Fin sessionsPerTag) × Nonce) → Digest)

/-- One tag query of the fine eager handler: a table tag step, then a tag advance. -/
@[spec high]
theorem multipleBadTableHandlerFine_wp_tag (tag : TagId)
    (post : (USpec).Range (.inl tag) → BState → Prop) {epost : EStack⟨⟩} :
    ⦃ fun p => wp (multipleTableHandler (sessionsPerTag := sessionsPerTag) g (.inl tag))
        (fun a s => post a (s, multipleBadAdvance tag p.2 a)) epost p.1 ⦄
      multipleBadTableHandlerFine g gFine (.inl tag) ⦃ post; epost ⦄ :=
  wp_of_run_eq_bind_advance _ (multipleBadTableHandlerFine g gFine (.inl tag))
    (fun r sB => multipleBadAdvance tag sB r) (fun _ => rfl) post

/-- One reader query of the fine eager handler: a table reader step, then a reader advance of
`cacheBad`. -/
@[spec high]
theorem multipleBadTableHandlerFine_wp_reader (t : TagTranscript Nonce Digest)
    (post : (USpec).Range (.inr t) → BState → Prop) {epost : EStack⟨⟩} :
    ⦃ fun p => wp (multipleTableHandler (sessionsPerTag := sessionsPerTag) g (.inr t))
        (fun a s => post a (s, multipleBadReaderAdvance gFine t p.2)) epost p.1 ⦄
      multipleBadTableHandlerFine g gFine (.inr t) ⦃ post; epost ⦄ :=
  wp_of_run_eq_bind_advance _ (multipleBadTableHandlerFine g gFine (.inr t))
    (fun _ sB => multipleBadReaderAdvance gFine t sB) (fun _ => rfl) post

/-- A reachable step of the fine eager handler is a table step with the bad-world component
advanced: by `multipleBadAdvance` on a tag query, by `multipleBadReaderAdvance` on a reader
query. -/
@[simulateQ_nf]
theorem mem_support_multipleBadTableHandlerFine_iff {q : (USpec).Domain} {p p' : BState}
    {a : (USpec).Range q} :
    (a, p') ∈ support ((multipleBadTableHandlerFine g gFine q).run p) ↔
      (a, p'.1) ∈ support ((multipleTableHandler (sessionsPerTag := sessionsPerTag) g q).run p.1) ∧
        p'.2 = (match q, a with
          | .inl tag, a => multipleBadAdvance tag p.2 a
          | .inr t, _ => multipleBadReaderAdvance gFine t p.2) := by
  rcases q with tag | t
  · exact mem_support_of_run_eq_bind_advance _ (multipleBadTableHandlerFine g gFine (.inl tag))
      (fun r sB => multipleBadAdvance tag sB r) (fun _ => rfl)
  · exact mem_support_of_run_eq_bind_advance _ (multipleBadTableHandlerFine g gFine (.inr t))
      (fun _ sB => multipleBadReaderAdvance gFine t sB) (fun _ => rfl)

/-- The fine eager handler never lowers either bad flag. -/
instance monotoneState_multipleBadTableHandlerFine :
    (multipleBadTableHandlerFine g gFine).MonotoneState
      fun p p' => (p.2.bad = true → p'.2.bad = true) ∧
        (p.2.cacheBad = true → p'.2.cacheBad = true) where
  refl _ := ⟨id, id⟩
  trans _ _ _ h₁ h₂ := ⟨h₂.1 ∘ h₁.1, h₂.2 ∘ h₁.2⟩
  step q p := by
    rintro ⟨a, p'⟩ hz
    obtain ⟨-, h⟩ := (mem_support_multipleBadTableHandlerFine_iff g gFine).1 hz
    rcases q with tag | t
    · exact h ▸ multipleBadAdvance_bad_mono tag p.2 a
    · exact h ▸ ⟨id, fun hc => by simp [hc]⟩

end fine

end PRFTagReader
