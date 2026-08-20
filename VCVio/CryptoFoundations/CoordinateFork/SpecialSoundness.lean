/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import VCVio.CryptoFoundations.CoordinateFork
public import VCVio.CryptoFoundations.SigmaProtocol

/-!
# Coordinate-wise special soundness as a protocol property

The fixed-statement, extensional part of Definition 2.29 of Fenzi–Moghaddas–Nguyen for a
Σ-protocol whose challenge space is a product `ι → S`: a `k`-ary extractor turns any set of
accepting transcripts whose challenges form an `SS(S, ℓ, k)` set into a valid witness.

Two shape decisions, both following existing practice in
`VCVio/CryptoFoundations/SigmaProtocol.lean`:

* The extractor is a **parameter**, not a field. `SigmaProtocol.extract` is hardwired to arity two,
  so a `k`-ary extractor cannot be one; `HVZK` takes `simTranscript` as a parameter for the same
  reason, since the `sim` field only produces a commitment.
* The property is a `Prop` over the extractor's `support`, with no runtime clause, exactly like
  `SigmaProtocol.SpeciallySoundAt`. The paper additionally quantifies over the security parameter
  and demands polynomial time. Neither is represented here, so this is only its extensional,
  fixed-statement component. `Stmt` may bundle the paper's index and statement.

`CoordSpeciallySoundAt` at `ℓ = 1` is ordinary `k`-special soundness
(`coordSpeciallySoundAt_iff_kSpeciallySoundAt`), and at `k = 2` it is implied by the repository's
two-transcript `SpeciallySoundAt` for any extractor that in fact extracts from a pair of its input
transcripts (`coordSpeciallySoundAt_two_of_speciallySoundAt`).
-/

@[expose] public section

open Finset CoordinateWise OracleComp

namespace SigmaProtocol

variable {Stmt Wit Commit PrvState Resp : Type} {rel : Stmt → Wit → Bool}
variable {ι S : Type} [DecidableEq ι] [Fintype ι] [DecidableEq S] [Fintype S]
variable {k : ℕ} {x : Stmt}

/-! ## The definition -/

/-- The fixed-statement, extensional clause of **Definition 2.29**. `ext` is
`ℓ`-coordinate-wise `k`-special sound if every witness it can return from a set of accepting
transcripts whose challenges form an `SS(S, ℓ, k)` set is valid for `x`.

The transcripts share the commitment `pc`, as in the paper, where the extractor is given
`(a, cᵢ, zᵢ)` with a common first message `a`. The statement is an explicit extractor input, as it
is in the paper; it must not be recovered from the transcripts. -/
def CoordSpeciallySoundAt (σ : SigmaProtocol Stmt Wit Commit PrvState (ι → S) Resp rel) (k : ℕ)
    (ext : Stmt → Commit → Finset ((ι → S) × Resp) → ProbComp Wit) (x : Stmt) : Prop :=
  ∀ (pc : Commit) (T : Finset ((ι → S) × Resp)),
    (∀ p ∈ T, σ.verify x pc p.1 p.2 = true) →
    IsCoordSpecialSound k (T.image Prod.fst) →
    ∀ w ∈ support (ext x pc T), rel x w = true

/-- A Σ-protocol is `ℓ`-coordinate-wise `k`-special sound if `CoordSpeciallySoundAt` holds at every
statement. -/
def CoordSpeciallySound (σ : SigmaProtocol Stmt Wit Commit PrvState (ι → S) Resp rel) (k : ℕ)
    (ext : Stmt → Commit → Finset ((ι → S) × Resp) → ProbComp Wit) : Prop :=
  ∀ x, σ.CoordSpeciallySoundAt k ext x

/-- Ordinary `k`-special soundness at a statement, stated for a `k`-ary extractor: any set of
accepting transcripts with `k` distinct challenges yields a valid witness. This is the `ℓ = 1`
shape, kept separate so the collapse below is a statement about two independently-written
definitions. -/
def KSpeciallySoundAt (σ : SigmaProtocol Stmt Wit Commit PrvState (ι → S) Resp rel) (k : ℕ)
    (ext : Stmt → Commit → Finset ((ι → S) × Resp) → ProbComp Wit) (x : Stmt) : Prop :=
  ∀ (pc : Commit) (T : Finset ((ι → S) × Resp)),
    (∀ p ∈ T, σ.verify x pc p.1 p.2 = true) →
    (T.image Prod.fst).card = k →
    ∀ w ∈ support (ext x pc T), rel x w = true

/-! ## The `ℓ = 1` collapse -/

omit [DecidableEq ι] [Fintype S] in
/-- With a single coordinate, `SS(S, 1, k)` is just "`k` distinct challenges", so coordinate-wise
`k`-special soundness is ordinary `k`-special soundness. The `1 ≤ k` side condition is real: at
`k = 0` the truncated `k - 1` makes `SS(S, ℓ, 0)` and `SS(S, ℓ, 1)` the same condition. -/
theorem coordSpeciallySoundAt_iff_kSpeciallySoundAt [Unique ι]
    (σ : SigmaProtocol Stmt Wit Commit PrvState (ι → S) Resp rel) {k : ℕ} (hk : 1 ≤ k)
    (ext : Stmt → Commit → Finset ((ι → S) × Resp) → ProbComp Wit) (x : Stmt) :
    σ.CoordSpeciallySoundAt k ext x ↔ σ.KSpeciallySoundAt k ext x :=
  ⟨fun h pc T hacc hcard => h pc T hacc ((isCoordSpecialSound_iff_of_unique hk).mpr hcard),
    fun h pc T hacc hss => h pc T hacc ((isCoordSpecialSound_iff_of_unique hk).mp hss)⟩

/-! ## Relation to the two-transcript definition -/

omit [DecidableEq ι] [Fintype S] in
/-- Any `k`-ary extractor that in fact extracts from two of its input transcripts with distinct
challenges inherits soundness from the repository's two-transcript `SpeciallySoundAt`.

This is the honest bridge to `SigmaProtocol.extract`: that field has arity two, so it cannot serve
as `ext` directly, but `hfactor` says `ext` is built from it. -/
theorem coordSpeciallySoundAt_two_of_speciallySoundAt
    (σ : SigmaProtocol Stmt Wit Commit PrvState (ι → S) Resp rel)
    (ext : Stmt → Commit → Finset ((ι → S) × Resp) → ProbComp Wit)
    (hss : σ.SpeciallySoundAt x)
    (hfactor : ∀ pc T, ∀ w ∈ support (ext x pc T),
      ∃ p₁ ∈ T, ∃ p₂ ∈ T, p₁.1 ≠ p₂.1 ∧ w ∈ support (σ.extract p₁.1 p₁.2 p₂.1 p₂.2)) :
    σ.CoordSpeciallySoundAt 2 ext x := by
  intro pc T hacc _ w hw
  obtain ⟨p₁, hp₁, p₂, hp₂, hne, hmem⟩ := hfactor pc T w hw
  exact hss pc p₁.1 p₂.1 p₁.2 p₂.2 hne (hacc _ hp₁) (hacc _ hp₂) w hmem

/-! ## Satisfiability of the hypotheses

The premises of `CoordSpeciallySoundAt` quantify over a set of transcripts that is simultaneously
accepting and coordinate-wise special sound. If no such set existed the definition would hold
vacuously of every extractor, so the following exhibits one for any prover response function whose
verifier accepts on a `coordFamily`. -/

omit [DecidableEq ι] [Fintype S] in
/-- Reading a response function off an `SS(S, ℓ, k)` challenge set produces transcripts satisfying
both premises of `CoordSpeciallySoundAt`. -/
theorem isCoordSpecialSound_image_fst_transcripts [DecidableEq Resp]
    {X : Finset (ι → S)} (hX : IsCoordSpecialSound k X) (τ : (ι → S) → Resp) :
    IsCoordSpecialSound k ((transcripts τ X).image Prod.fst) := by
  rwa [image_fst_transcripts]

omit [Fintype S] in
/-- The premises of `CoordSpeciallySoundAt` are jointly satisfiable: `coordFamily` supplies the
challenge set, and any response function the verifier accepts on it supplies the transcripts. -/
theorem exists_accepting_isCoordSpecialSound
    (σ : SigmaProtocol Stmt Wit Commit PrvState (ι → S) Resp rel) (pc : Commit)
    (c₀ : ι → S) (R : ι → Finset S) (hnot : ∀ j, c₀ j ∉ R j)
    (hcard : ∀ j, (R j).card = k - 1) (τ : (ι → S) → Resp)
    (hacc : ∀ c ∈ coordFamily c₀ R, σ.verify x pc c (τ c) = true) :
    ∃ T : Finset ((ι → S) × Resp), (∀ p ∈ T, σ.verify x pc p.1 p.2 = true) ∧
      IsCoordSpecialSound k (T.image Prod.fst) := by
  classical
  refine ⟨transcripts τ (coordFamily c₀ R), fun p hp => ?_,
    isCoordSpecialSound_image_fst_transcripts (isCoordSpecialSound_coordFamily hnot hcard) τ⟩
  obtain ⟨c, y⟩ := p
  obtain ⟨h1, rfl⟩ := mem_transcripts.mp hp
  exact hacc c h1

end SigmaProtocol
