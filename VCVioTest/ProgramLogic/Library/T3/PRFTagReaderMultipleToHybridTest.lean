/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.ProgramLogic.Library.T3.PRFTagReader.MultipleToHybridEagerSetup
public import VCVio.ProgramLogic.Library.T3.PRFTagReader.MultipleToHybridSetup
public import VCVio.ProgramLogic.Library.T3.PRFTagReader.Table

/-!
# Tests for the instrumented multiple-session handler specifications

Core `vcgen` with the rules of `VCVio.ProgramLogic.Library.T3.PRFTagReader.MultipleToHybridSetup`
and `MultipleToHybridEagerSetup`, which hand over to the table rules of
`VCVio.ProgramLogic.Library.T3.PRFTagReader.Table`, and the bad-flag monotonicity lemmas of
`Examples.PRFTagReader.MultipleToHybrid` re-proved in one line.
-/

public section

namespace VCVioTest.ProgramLogic.Library.T3.PRFTagReaderMultipleToHybrid

open OracleSpec OracleComp OracleComp.ProgramLogic Std.WP PRFTagReader

open scoped OracleComp.Necessary

set_option experimental.vcgen true

variable {TagId Nonce Digest : Type} {sessionsPerTag : ℕ} [DecidableEq TagId] [Fintype TagId]
  [DecidableEq Nonce] [SampleableType Nonce] [DecidableEq Digest]

/-- A tag query of the eager instrumented handler hands over to the table rule: with a free slot
it answers a transcript, uses up the slot and records the transcript in the bad world. -/
example (g : TagId × Nonce → Digest) (tag : TagId) (k : ℕ) :
    ⦃ fun p => p.1.sessionsUsed tag = k ∧ k < sessionsPerTag ⦄
      multipleBadTableHandler sessionsPerTag g (.inl tag)
    ⦃ fun r p => r.isSome ∧ p.1.sessionsUsed tag = k + 1 ⦄ := by
  vcgen
  rename_i p hp r s' hr
  obtain ⟨-, nonce, rfl, rfl⟩ | ⟨h, -⟩ := hr
  · simp_all
  · omega

/-- An opaque eager adversary never lowers the tag-side bad flag. -/
example {α : Type} (g : TagId × Nonce → Digest)
    (adv : OracleComp (UnlinkOracleSpec TagId Nonce Digest) α) :
    ⦃ fun p => p.2.bad = true ∧ True ⦄ simulateQ (multipleBadTableHandler sessionsPerTag g) adv
    ⦃ fun _ p => p.2.bad = true ⦄ := by
  vcgen
  grind

/-- `multipleBadTableHandler_step_preserves_bad`, re-proved. -/
example (g : TagId × Nonce → Digest) (t : (UnlinkOracleSpec TagId Nonce Digest).Domain)
    (p : UnlinkState TagId × UnlinkBadState TagId Nonce Digest) (hbad : p.2.bad = true) :
    ∀ z ∈ support (multipleBadTableHandler sessionsPerTag g t p), z.2.2.bad = true :=
  fun z hz => ((monotoneState_multipleBadTableHandler g).step t p z hz).1 hbad

/-- `multipleBadTableHandlerFine_run_preserves_bad`, re-proved. -/
example [NeZero sessionsPerTag] {α : Type} (g : TagId × Nonce → Digest)
    (gFine : ((TagId × Fin sessionsPerTag) × Nonce) → Digest)
    (oa : OracleComp (UnlinkOracleSpec TagId Nonce Digest) α)
    (p : UnlinkState TagId × UnlinkBadState TagId Nonce Digest) (hbad : p.2.bad = true) :
    ∀ z ∈ support ((simulateQ (multipleBadTableHandlerFine g gFine) oa).run p), z.2.2.bad = true :=
  fun _ hz => (QueryImpl.MonotoneState.rel_of_mem_support hz).1 hbad

/-- `multipleBadQueryImpl_run_preserves_bad`, re-proved. -/
example [SampleableType Digest] {α : Type}
    (oa : OracleComp (UnlinkOracleSpec TagId Nonce Digest) α)
    (s : MultipleBadState TagId Nonce Digest sessionsPerTag) (hbad : s.2.bad = true) :
    ∀ z ∈ support ((simulateQ (multipleBadQueryImpl TagId Nonce Digest sessionsPerTag) oa).run s),
      z.2.2.bad = true :=
  fun _ hz => (QueryImpl.MonotoneState.rel_of_mem_support hz).1 hbad

/-- The fine eager handler's reader step raises `cacheBad` exactly by `cacheBadReader`. -/
example [NeZero sessionsPerTag] (g : TagId × Nonce → Digest)
    (gFine : ((TagId × Fin sessionsPerTag) × Nonce) → Digest) (t : TagTranscript Nonce Digest) :
    ⦃ fun p => p.2.cacheBad = false ⦄ multipleBadTableHandlerFine g gFine (.inr t)
    ⦃ fun _ p => p.2.cacheBad = cacheBadReader gFine t ⦄ := by
  vcgen
  simp_all

end VCVioTest.ProgramLogic.Library.T3.PRFTagReaderMultipleToHybrid
