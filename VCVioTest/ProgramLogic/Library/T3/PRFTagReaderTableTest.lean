/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.ProgramLogic.Library.T3.PRFTagReader.Table

/-!
# Tests for the PRF tag/reader table handler specifications

Core `vcgen` with the rules of `VCVio.ProgramLogic.Library.T3.PRFTagReader.Table`: tag sessions
are used up in order, readers answer deterministically, and an opaque adversary respects the
session cap.
-/

public section

namespace VCVioTest.ProgramLogic.Library.T3.PRFTagReaderTable

open OracleSpec OracleComp OracleComp.ProgramLogic Std.WP PRFTagReader

open scoped OracleComp.Necessary

set_option experimental.vcgen true

variable {TagId Nonce Digest : Type} {sessionsPerTag : ℕ} [DecidableEq TagId] [Fintype TagId]
  [SampleableType Nonce] [DecidableEq Digest]

/-- Two tag queries from a fresh counter with two slots both get a transcript, in slots `0` and
`1`, and use up both slots. -/
example (g : (TagId × Fin 2) × Nonce → Digest) (tag : TagId) :
    ⦃ fun s => s.sessionsUsed tag = 0 ⦄
      simulateQ (singleTableHandler g) (do
        let a ← query (spec := UnlinkOracleSpec TagId Nonce Digest) (.inl tag)
        let b ← query (spec := UnlinkOracleSpec TagId Nonce Digest) (.inl tag)
        return (a, b))
    ⦃ fun z s => z.1.isSome ∧ z.2.isSome ∧ s.sessionsUsed tag = 2 ⦄ := by
  vcgen
  rename_i s h x h₁ x' h₂
  obtain ⟨-, _, rfl, rfl⟩ | ⟨h₁, -⟩ := h₁
  · obtain ⟨-, _, rfl, rfl⟩ | ⟨h₂, -⟩ := h₂ <;> simp_all
  · omega

/-- With its slots exhausted, a tag query answers `none` and keeps the state. -/
example (g : TagId × Nonce → Digest) (tag : TagId) :
    ⦃ fun s => sessionsPerTag ≤ s.sessionsUsed tag ⦄
      multipleTableHandler (sessionsPerTag := sessionsPerTag) g (.inl tag)
    ⦃ fun r s => r.isNone ∧ sessionsPerTag ≤ s.sessionsUsed tag ⦄ := by
  vcgen
  grind

/-- A tag query followed by a reader query of its transcript: the reader accepts, since the
transcript's digest is the table's value at the tag. -/
example (g : TagId × Nonce → Digest) (tag : TagId) (t : TagTranscript Nonce Digest) :
    ⦃ fun s => s.sessionsUsed tag < sessionsPerTag ⦄
      simulateQ (multipleTableHandler (sessionsPerTag := sessionsPerTag) g) (do
        let a ← query (spec := UnlinkOracleSpec TagId Nonce Digest) (.inl tag)
        query (spec := UnlinkOracleSpec TagId Nonce Digest) (.inr (a.getD t)))
    ⦃ fun r _ => r = ReaderReply.ok ∨ r = ReaderReply.ko ⦄ := by
  vcgen
  rename_i r _ _
  cases r <;> simp

/-- An opaque adversary never exceeds the session cap, and never lowers a counter. -/
example {α : Type} (g : (TagId × Fin sessionsPerTag) × Nonce → Digest) (tag : TagId) (k : ℕ)
    (adv : OracleComp (UnlinkOracleSpec TagId Nonce Digest) α) :
    ⦃ fun s => (∀ tag, s.sessionsUsed tag ≤ sessionsPerTag) ∧ k ≤ s.sessionsUsed tag ⦄
      simulateQ (singleTableHandler g) adv
    ⦃ fun _ s => (∀ tag, s.sessionsUsed tag ≤ sessionsPerTag) ∧ k ≤ s.sessionsUsed tag ⦄ := by
  vcgen
  grind

end VCVioTest.ProgramLogic.Library.T3.PRFTagReaderTable
