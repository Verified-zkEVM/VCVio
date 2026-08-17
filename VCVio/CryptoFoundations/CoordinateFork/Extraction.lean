/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import VCVio.CryptoFoundations.CoordinateFork.SpecialSoundness

/-!
# Coordinate-wise special soundness implies knowledge soundness, Σ-protocol case

Lemma 2.31 of Fenzi–Moghaddas–Nguyen at `μ = 1`: composing the coordinate-wise rewinding extractor
of `VCVio/CryptoFoundations/CoordinateFork.lean` with an `ℓ`-coordinate-wise `k`-special sound
extractor yields a valid witness with probability at least `ε - ℓ(k-1)/|S|`, where `ε` is the
prover's accepting probability.

`coordExtract` is the composite: fork on the prover's response table to obtain `ℓ(k-1)+1` accepting
transcripts whose challenges are `SS(S, ℓ, k)`, then hand them to `ext`. Its success event is
`∃ w, r = some w ∧ rel x w`, which no aborting run satisfies — so the bound is a statement about
witnesses produced, not merely about the extractor terminating.

The prover is modelled by its *response table* `P : ProbComp ((ι → S) → Resp)` after committing to
`pc`: a malicious prover that has sent its first message is exactly a distribution over functions
from challenges to responses. What is not modelled is the query count — see the module docstring of
`CoordinateFork.lean` and `docs/agents/forking.md`.

Only `μ = 1` is reachable here. The multi-round case needs a transcript-producing multi-round
extractor, which `CoordinateFork/MultiRound.lean` does not yet provide.
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
    (k : ℕ) (ext : Commit → Finset ((ι → S) × Resp) → ProbComp Wit) (x : Stmt) (pc : Commit)
    (P : ProbComp ((ι → S) → Resp)) : ProbComp (Option Wit) :=
  coordForkT (σ.verify x pc) k P >>= fun r =>
    match r with
    | none => pure none
    | some (τ, X) => some <$> ext pc (transcripts τ X)

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
    {ext : Commit → Finset ((ι → S) × Resp) → ProbComp Wit} {pc : Commit}
    (hss : σ.CoordSpeciallySoundAt k ext x) {τ : (ι → S) → Resp} {X : Finset (ι → S)}
    (hgood : GoodTranscripts (σ.verify x pc) k (some (τ, X))) :
    Pr[Extracted rel x | (some <$> ext pc (transcripts τ X) : ProbComp (Option Wit))] = 1 := by
  rw [goodTranscripts_some_iff] at hgood
  obtain ⟨hsound, hacc⟩ := hgood
  rw [probEvent_map]
  refine probEvent_eq_one ⟨by simp, fun w hw => ⟨w, rfl, ?_⟩⟩
  refine hss pc (transcripts τ X) (fun p hp => ?_) ?_ w hw
  · obtain ⟨c, y⟩ := p
    obtain ⟨h1, rfl⟩ := mem_transcripts.mp hp
    exact hacc c h1
  · rwa [image_fst_transcripts]

/-- **Lemma 2.31, Σ-protocol case.** Against an `ℓ`-coordinate-wise `k`-special sound extractor,
the composite extractor returns a valid witness with probability at least `ε - ℓ(k-1)/|S|`, where
`ε` is the probability that the prover's response is accepted on a uniform challenge.

The knowledge error is therefore `ℓ(k-1)/|S|`. Not proved: the extractor's expected running time,
the paper's other clause. -/
theorem sub_div_le_probEvent_extracted_coordExtract [Nonempty S]
    (σ : SigmaProtocol Stmt Wit Commit PrvState (ι → S) Resp rel) (k : ℕ)
    (ext : Commit → Finset ((ι → S) × Resp) → ProbComp Wit) (x : Stmt)
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
