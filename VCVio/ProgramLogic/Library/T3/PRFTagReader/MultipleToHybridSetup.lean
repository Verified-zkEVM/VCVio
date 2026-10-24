/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Examples.PRFTagReader.MultipleToHybrid.Setup
public import VCVio.ProgramLogic.Library

/-!
# Specifications for the instrumented multiple-session handler

Specifications for `PRFTagReader.multipleBadQueryImpl` of
`Examples.PRFTagReader.MultipleToHybrid.Setup`, under the necessary reading
(`open scoped OracleComp.Necessary`): the multiple-session ideal handler
`multipleIdealQueryImpl` on the first state component, with the bad-world component advanced by
`multipleBadAdvance` on a tag query.

* *One query.* `multipleBadQueryImpl_wp_tag` and `multipleBadQueryImpl_wp_reader` (`spec high`)
  read a step through the weakest precondition of `multipleIdealQueryImpl`.
* *Support.* `mem_support_multipleBadQueryImpl_iff` (in `simulateQ_nf`).
* *Whole runs.* `multipleBadQueryImpl` is `QueryImpl.MonotoneState` for "neither bad flag is ever
  lowered", so `vcgen` frames an opaque adversary and `MonotoneState.rel_of_mem_support` gives
  the bad-flag monotonicity of every run.
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
private theorem wp_of_run_eq_bind_advance'
    (h : ∀ p, mx.run p = x.run p.1 >>= fun r => pure (r.1, r.2, f r.1 p.2))
    (post : α → σ × τ → Prop) {epost : EStack⟨⟩} :
    ⦃ fun p => wp x (fun a s => post a (s, f a p.2)) epost p.1 ⦄ mx ⦃ post; epost ⦄ :=
  ⟨fun p => by
    rw [StateT.wp_apply_eq, StateT.wp_apply_eq, h, bind_pure_comp]
    exact WPMonad.map_le_wp_map (m := ProbComp) (fun r : α × σ => (r.1, r.2, f r.1 p.2))
      (x.run p.1) (fun z : α × σ × τ => post z.1 z.2) epost⟩

/-- The support form of `wp_of_run_eq_bind_advance'`. -/
private theorem mem_support_of_run_eq_bind_advance'
    (h : ∀ p, mx.run p = x.run p.1 >>= fun r => pure (r.1, r.2, f r.1 p.2)) {p p' : σ × τ}
    {a : α} : (a, p') ∈ support (mx.run p) ↔ (a, p'.1) ∈ support (x.run p.1) ∧ p'.2 = f a p.2 := by
  rw [h]
  simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff, Prod.exists]
  aesop

end advance

variable {TagId Nonce Digest : Type} {sessionsPerTag : ℕ} [DecidableEq TagId] [Fintype TagId]
  [DecidableEq Nonce] [SampleableType Nonce] [DecidableEq Digest] [SampleableType Digest]

local notation "USpec" => UnlinkOracleSpec TagId Nonce Digest

/-- One tag query of the instrumented handler: an ideal tag step, then a tag advance. -/
@[spec high]
theorem multipleBadQueryImpl_wp_tag (tag : TagId)
    (post : (USpec).Range (.inl tag) → MultipleBadState TagId Nonce Digest sessionsPerTag → Prop)
    {epost : EStack⟨⟩} :
    ⦃ fun p => wp (multipleIdealQueryImpl (sessionsPerTag := sessionsPerTag) (.inl tag))
        (fun a s => post a (s, multipleBadAdvance tag p.2 a)) epost p.1 ⦄
      multipleBadQueryImpl TagId Nonce Digest sessionsPerTag (.inl tag) ⦃ post; epost ⦄ :=
  wp_of_run_eq_bind_advance' _ (multipleBadQueryImpl TagId Nonce Digest sessionsPerTag (.inl tag))
    (fun r sB => multipleBadAdvance tag sB r) (multipleBadQueryImpl_tag_run tag) post

/-- One reader query of the instrumented handler: an ideal reader step. -/
@[spec high]
theorem multipleBadQueryImpl_wp_reader (t : TagTranscript Nonce Digest)
    (post : (USpec).Range (.inr t) → MultipleBadState TagId Nonce Digest sessionsPerTag → Prop)
    {epost : EStack⟨⟩} :
    ⦃ fun p => wp (multipleIdealQueryImpl (sessionsPerTag := sessionsPerTag) (.inr t))
        (fun a s => post a (s, p.2)) epost p.1 ⦄
      multipleBadQueryImpl TagId Nonce Digest sessionsPerTag (.inr t) ⦃ post; epost ⦄ :=
  wp_of_run_eq_bind_advance' _ (multipleBadQueryImpl TagId Nonce Digest sessionsPerTag (.inr t))
    (fun _ sB => sB) (multipleBadQueryImpl_reader_run t) post

/-- A reachable step of the instrumented handler is an ideal step with the bad-world component
advanced on a tag query. -/
@[simulateQ_nf]
theorem mem_support_multipleBadQueryImpl_iff {q : (USpec).Domain}
    {p p' : MultipleBadState TagId Nonce Digest sessionsPerTag} {a : (USpec).Range q} :
    (a, p') ∈ support ((multipleBadQueryImpl TagId Nonce Digest sessionsPerTag q).run p) ↔
      (a, p'.1) ∈
        support ((multipleIdealQueryImpl (sessionsPerTag := sessionsPerTag) q).run p.1) ∧
        p'.2 = (match q, a with
          | .inl tag, a => multipleBadAdvance tag p.2 a
          | .inr _, _ => p.2) := by
  rcases q with tag | t
  · exact mem_support_of_run_eq_bind_advance' _
      (multipleBadQueryImpl TagId Nonce Digest sessionsPerTag (.inl tag))
      (fun r sB => multipleBadAdvance tag sB r) (multipleBadQueryImpl_tag_run tag)
  · exact mem_support_of_run_eq_bind_advance' _
      (multipleBadQueryImpl TagId Nonce Digest sessionsPerTag (.inr t)) (fun _ sB => sB)
      (multipleBadQueryImpl_reader_run t)

/-- The instrumented handler never lowers either bad flag. -/
instance monotoneState_multipleBadQueryImpl :
    (multipleBadQueryImpl TagId Nonce Digest sessionsPerTag).MonotoneState
      fun p p' => (p.2.bad = true → p'.2.bad = true) ∧
        (p.2.cacheBad = true → p'.2.cacheBad = true) where
  refl _ := ⟨id, id⟩
  trans _ _ _ h₁ h₂ := ⟨h₂.1 ∘ h₁.1, h₂.2 ∘ h₁.2⟩
  step q p := by
    rintro ⟨a, p'⟩ hz
    obtain ⟨-, h⟩ := mem_support_multipleBadQueryImpl_iff.1 hz
    rcases q with tag | t
    · rw [h]
      cases a <;> simp +contextual [multipleBadAdvance]
    · exact h ▸ ⟨id, id⟩

end PRFTagReader
