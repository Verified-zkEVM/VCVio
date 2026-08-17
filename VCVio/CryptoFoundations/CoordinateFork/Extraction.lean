/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import VCVio.CryptoFoundations.CoordinateFork.SpecialSoundness

/-!
# A fixed-statement extraction bound for coordinate-wise special soundness

This module proves the fixed-statement, table-model extraction-success inequality underlying the
`μ = 1` case of Lemma 2.31 of Fenzi–Moghaddas–Nguyen. Composing the coordinate-wise table fork with
an extensional `ℓ`-coordinate-wise `k`-special sound extractor yields a valid witness with
probability at least `ε - ℓ(k-1)/|S|`, where `ε` is the prover's accepting probability.

`coordExtract` is the composite: fork on the prover's response table to obtain `ℓ(k-1)+1` accepting
transcripts whose challenges are `SS(S, ℓ, k)`, then hand them to `ext`. Its success event is
`∃ w, r = some w ∧ rel x w`, which no aborting run satisfies — so the bound is a statement about
witnesses produced, not merely about the extractor terminating.

The input `P : ProbComp ((ι → S) → Resp)` is a distribution of complete response tables after the
commitment `pc`. This can encode a responder whose coins are fixed before answering challenges,
but no theorem here derives such a table distribution, or its cross-rewind coupling, from an
interactive malicious prover. Query count is also absent; see `CoordinateFork.lean` and
`docs/agents/forking.md`.

This is not the paper's full knowledge-soundness theorem: it has no security-parameter
quantification, joint bad-event experiment, oracle-query semantics, or expected-polynomial-time
claim. Only `μ = 1` is represented. The multi-round case needs a transcript-producing multi-round
extractor, which `CoordinateFork/MultiRound.lean` does not provide.
-/

@[expose] public section

open Finset CoordinateWise OracleComp OracleComp.EvalDist

open scoped ENNReal

namespace SigmaProtocol

variable {Stmt Wit Commit PrvState Resp : Type} {rel : Stmt → Wit → Bool}
variable {ι S : Type} [DecidableEq ι] [Fintype ι] [DecidableEq S] [Fintype S]
variable [SampleableType (ι → S)] [DecidableEq Resp]
variable {k : ℕ} {x : Stmt}

/-- The composite extractor: run the coordinate-wise fork against the prover's response table, then
apply the `k`-ary extractor to the accepting transcripts it returns. Aborts exactly when the fork
does. -/
noncomputable def coordExtract (σ : SigmaProtocol Stmt Wit Commit PrvState (ι → S) Resp rel)
    (k : ℕ) (ext : Stmt → Commit → Finset ((ι → S) × Resp) → ProbComp Wit) (x : Stmt)
    (pc : Commit)
    (P : ProbComp ((ι → S) → Resp)) : ProbComp (Option Wit) :=
  coordForkT (σ.verify x pc) k P >>= fun r =>
    match r with
    | none => pure none
    | some (τ, X) => some <$> ext x pc (transcripts τ X)

/-- The event that the composite extractor produced a valid witness. Aborting runs fail it, so a
bound on this event is not a bound on termination. -/
def Extracted (rel : Stmt → Wit → Bool) (x : Stmt) (r : Option Wit) : Prop :=
  ∃ w, r = some w ∧ rel x w = true

@[simp] theorem not_extracted_none : ¬ Extracted rel x none := by
  simp [Extracted]

omit [DecidableEq ι] [Fintype S] [SampleableType (ι → S)] in
/-- On a good fork the composite extractor certainly produces a valid witness. -/
theorem probEvent_extracted_eq_one_of_goodTranscripts
    {σ : SigmaProtocol Stmt Wit Commit PrvState (ι → S) Resp rel}
    {ext : Stmt → Commit → Finset ((ι → S) × Resp) → ProbComp Wit} {pc : Commit}
    (hss : σ.CoordSpeciallySoundAt k ext x) {τ : (ι → S) → Resp} {X : Finset (ι → S)}
    (hgood : GoodTranscripts (σ.verify x pc) k (some (τ, X))) :
    Pr[Extracted rel x | (some <$> ext x pc (transcripts τ X) : ProbComp (Option Wit))] = 1 := by
  rw [goodTranscripts_some_iff] at hgood
  obtain ⟨hsound, hacc⟩ := hgood
  rw [probEvent_map]
  refine probEvent_eq_one ⟨by simp, fun w hw => ⟨w, rfl, ?_⟩⟩
  refine hss pc (transcripts τ X) (fun p hp => ?_) ?_ w hw
  · obtain ⟨c, y⟩ := p
    obtain ⟨h1, rfl⟩ := mem_transcripts.mp hp
    exact hacc c h1
  · rwa [image_fst_transcripts]

/-- The fixed-statement, table-model extraction-success inequality underlying the `μ = 1`
Σ-protocol case of **Lemma 2.31**. Against an extensional `ℓ`-coordinate-wise `k`-special sound
extractor, the composite returns a valid witness with probability at least `ε - ℓ(k-1)/|S|`,
where `ε` is the probability that the prover's response is accepted on a uniform challenge.

This theorem alone is not a knowledge-soundness definition or an efficiency theorem. -/
theorem sub_div_le_probEvent_extracted_coordExtract [Nonempty S]
    (σ : SigmaProtocol Stmt Wit Commit PrvState (ι → S) Resp rel) (k : ℕ)
    (ext : Stmt → Commit → Finset ((ι → S) × Resp) → ProbComp Wit) (x : Stmt)
    (hss : σ.CoordSpeciallySoundAt k ext x) (pc : Commit)
    (P : ProbComp ((ι → S) → Resp)) :
    acceptRatio (acceptTable (σ.verify x pc) P)
        - (Fintype.card ι : ℝ≥0∞) * (k - 1 : ℕ) / Fintype.card S
      ≤ Pr[Extracted rel x | σ.coordExtract k ext x pc P] := by
  refine (sub_div_le_probEvent_goodTranscripts_coordForkT (σ.verify x pc) k P).trans ?_
  rw [coordExtract]
  refine le_of_eq_of_le (mul_one _).symm (mul_le_probEvent_bind le_rfl fun r _ hgood => ?_)
  obtain ⟨τ, X, rfl, hpay⟩ := hgood
  exact le_of_eq (probEvent_extracted_eq_one_of_goodTranscripts hss ⟨τ, X, rfl, hpay⟩).symm

end SigmaProtocol
