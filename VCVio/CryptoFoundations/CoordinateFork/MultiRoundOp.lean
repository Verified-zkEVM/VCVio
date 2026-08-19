/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import VCVio.CryptoFoundations.CoordinateFork.Operational
public import VCVio.CryptoFoundations.CoordinateFork.Realizability

/-!
# The multi-round coordinate-wise extractor

`multiForkOp` is the recursion of §7.2 of Fenzi–Moghaddas–Nguyen: to extract from a
`(2μ+1)`-round protocol, extract a level-`μ-1` tree at every possible first challenge, and then run
the single-round loop of Figure 11 against the table recording which of those extractions
succeeded.

`probEvent_isSome_multiForkOp` is the point of the file. It shows the recursion's success
probability *is* the analytic functional `multiSucc` of
`VCVio/CryptoFoundations/CoordinateFork/MultiRound.lean`, so the independent Bernoulli coupling
that functional is defined by is no longer a modelling decision: it is what running the
sub-extractor independently at each first challenge actually produces.
`sub_le_probEvent_isSome_multiForkOp` then reads the `ε - μℓ(k-1)/N` bound off `sub_le_multiSucc`.

`multiForkOp_success` is the output clause: a successful run returns `(ℓ(k-1)+1)^μ` accepting
transcripts whose challenge sequences form a tree in the sense of Definition 2.30, which is what
`ToMathlib/Combinatorics/ChallengeTree.lean` defines and what Lemma 7.2 asks for.

Two things this does not do. The extractor consumes a fixed acceptance table on transcripts rather
than querying a prover, exactly as at `μ = 1`. And it carries no cost: the paper's
`(ℓ(k-1)+1)^μ` expected-query count multiplies the per-round count by the sub-extractor's, which is
Wald's identity over the resampling loop and needs the loop's queries to be a stopping time — a
separate argument from the `μ = 1` counting one, and the one §8.2 refines when the sub-extractor's
cost varies with the entry.
-/

@[expose] public section

open Finset CoordinateWise OracleComp OracleComp.EvalDist

open scoped ENNReal

namespace OracleComp

variable {ι S : Type} [DecidableEq ι] [Fintype ι] [DecidableEq S] [Fintype S]
variable [SampleableType (ι → S)]

/-- The `μ`-round extractor: extract recursively at every first challenge, then fork on the table
of which of those extractions succeeded. -/
noncomputable def multiForkOp : (μ : ℕ) → (k : ℕ) → (ρ : Transcript ι S μ → Bool) →
    ProbComp (Option (Finset (Transcript ι S μ)))
  | 0, _, ρ => pure (if ρ PUnit.unit then some {PUnit.unit} else none)
  | μ + 1, k, ρ => do
      let tbl ← Fintype.mPi fun c => multiForkOp μ k fun t => ρ (c, t)
      let r ← coordForkOp k fun c => (tbl c).isSome
      return r.1.map fun X => X.biUnion fun c => ((tbl c).getD ∅).image fun t => (c, t)

@[simp] theorem multiForkOp_zero (k : ℕ) (ρ : Transcript ι S 0 → Bool) :
    multiForkOp 0 k ρ = pure (if ρ PUnit.unit then some {PUnit.unit} else none) := rfl

theorem multiForkOp_succ (μ k : ℕ) (ρ : Transcript ι S (μ + 1) → Bool) :
    multiForkOp (μ + 1) k ρ =
      (do
        let tbl ← Fintype.mPi fun c => multiForkOp μ k fun t => ρ (c, t)
        let r ← coordForkOp k fun c => (tbl c).isSome
        return r.1.map fun X =>
          X.biUnion fun c => ((tbl c).getD ∅).image fun t => (c, t)) := rfl

/-! ## The output -/

/-- The challenge sequence of a transcript. -/
def Transcript.toList : ∀ {μ : ℕ}, Transcript ι S μ → List (ι → S)
  | 0, _ => []
  | _ + 1, t => t.1 :: Transcript.toList t.2

omit [DecidableEq ι] [Fintype ι] [DecidableEq S] [Fintype S] [SampleableType (ι → S)] in
@[simp] theorem Transcript.toList_zero (t : Transcript ι S 0) : Transcript.toList t = [] := rfl

omit [DecidableEq ι] [Fintype ι] [DecidableEq S] [Fintype S] [SampleableType (ι → S)] in
@[simp] theorem Transcript.toList_succ {μ : ℕ} (t : Transcript ι S (μ + 1)) :
    Transcript.toList t = t.1 :: Transcript.toList t.2 := rfl

omit [DecidableEq ι] [Fintype S] [SampleableType (ι → S)] in
/-- Prefixing a challenge commutes with reading challenge sequences. -/
theorem image_toList_image_prod {μ : ℕ} (c : ι → S) (T : Finset (Transcript ι S μ)) :
    Finset.image (Transcript.toList (μ := μ + 1))
        (T.image fun t : Transcript ι S μ => show Transcript ι S (μ + 1) from (c, t))
      = (T.image Transcript.toList).image fun l => c :: l := by
  rw [Finset.image_image, Finset.image_image]
  rfl

/-- **The output clause of Lemma 7.2.** A successful run returns accepting transcripts whose
challenge sequences form a tree of challenges in the sense of Definition 2.30. -/
theorem multiForkOp_success : ∀ (μ k : ℕ) (ρ : Transcript ι S μ → Bool)
    (T : Finset (Transcript ι S μ)), some T ∈ support (multiForkOp μ k ρ) →
      IsChallengeTree k μ (T.image Transcript.toList) ∧ ∀ t ∈ T, ρ t
  | 0, k, ρ, T, h => by
      classical
      rw [multiForkOp_zero, support_pure, Set.mem_singleton_iff] at h
      by_cases hρ : ρ PUnit.unit
      · rw [if_pos hρ] at h
        obtain rfl : T = {PUnit.unit} := Option.some.inj h
        refine ⟨?_, fun t _ => ?_⟩
        · rw [isChallengeTree_zero]
          refine Finset.ext fun l => ⟨fun hl => ?_, fun hl => ?_⟩
          · obtain ⟨t, -, rfl⟩ := Finset.mem_image.mp hl
            simp
          · rw [Finset.mem_singleton] at hl
            subst hl
            exact Finset.mem_image.mpr ⟨PUnit.unit, Finset.mem_singleton_self _, rfl⟩
        · obtain rfl : t = PUnit.unit := rfl
          exact hρ
      · rw [if_neg hρ] at h
        exact absurd h (by simp)
  | μ + 1, k, ρ, T, h => by
      classical
      rw [multiForkOp_succ, mem_support_bind_iff] at h
      obtain ⟨tbl, htbl, h⟩ := h
      rw [mem_support_bind_iff] at h
      obtain ⟨r, hr, h⟩ := h
      simp only [support_pure, Set.mem_singleton_iff] at h
      cases hr1 : r.1 with
      | none => rw [hr1] at h; simp at h
      | some X =>
      rw [hr1] at h
      simp only [Option.map_some, Option.some.injEq] at h
      subst h
      obtain ⟨hss, hacc⟩ := coordForkOp_success (X := X) (cost := r.2) (by rw [← hr1]; exact hr)
      -- Every child challenge names a successful sub-extraction.
      have hchild : ∀ c ∈ X, IsChallengeTree k μ (((tbl c).getD ∅).image Transcript.toList) ∧
          ∀ t ∈ (tbl c).getD ∅, ρ (c, t) := by
        intro c hc
        obtain ⟨Tc, hTc⟩ : ∃ Tc, tbl c = some Tc := Option.isSome_iff_exists.mp (hacc c hc)
        have hsub : some Tc ∈ support (multiForkOp μ k fun t => ρ (c, t)) := by
          rw [← hTc]; exact mem_support_mPi _ tbl htbl c
        rw [hTc]
        exact multiForkOp_success μ k _ Tc hsub
      refine ⟨?_, ?_⟩
      · rw [Finset.biUnion_image,
          Finset.biUnion_congr rfl fun a _ => image_toList_image_prod a ((tbl a).getD ∅)]
        exact isChallengeTree_biUnion hss fun c hc => (hchild c hc).1
      · intro t ht
        obtain ⟨c, hc, ht⟩ := Finset.mem_biUnion.mp ht
        obtain ⟨t', ht', rfl⟩ := Finset.mem_image.mp ht
        exact (hchild c hc).2 t' ht'

/-! ## The success probability -/

/-- One round of the recursion, in the shape `Realizability.lean` identifies with an independent
Bernoulli table: the sub-extractors run independently, one per first challenge. -/
theorem probEvent_isSome_multiForkOp_succ (μ k : ℕ) (ρ : Transcript ι S (μ + 1) → Bool) :
    Pr[fun r => r.isSome | multiForkOp (μ + 1) k ρ]
      = forkSucc k fun c => Pr[fun r => r.isSome | multiForkOp μ k fun t => ρ (c, t)] := by
  classical
  set sub : (ι → S) → ProbComp (Option (Finset (Transcript ι S μ))) :=
    fun c => multiForkOp μ k fun t => ρ (c, t) with hsub
  set q : (ι → S) → ℝ≥0∞ := fun c => Pr[fun r => r.isSome | sub c] with hq
  have hq1 : ∀ c, q c ≤ 1 := fun _ => probEvent_le_one
  -- Discarding the returned tree leaves the single-round loop's success event.
  have hmap : Pr[fun r => r.isSome | multiForkOp (μ + 1) k ρ]
      = expectedValue (Fintype.mPi sub)
        (fun tbl => Pr[fun r => r.1.isSome | coordForkOp k fun c => (tbl c).isSome]) := by
    rw [multiForkOp_succ, probEvent_bind_eq_tsum, expectedValue_def]
    refine tsum_congr fun tbl => congrArg _ ?_
    rw [bind_pure_comp, probEvent_map]
    exact congrArg _ (funext fun r => by simp)
  -- The single-round success probability is a functional of the sampled table.
  have hcount : ∀ tbl : (ι → S) → Option (Finset (Transcript ι S μ)),
      Pr[fun r => r.1.isSome | coordForkOp k fun c => (tbl c).isSome]
        = ((goodSet k fun c => (tbl c).isSome).card : ℝ≥0∞) / Fintype.card (ι → S) := fun tbl =>
    probEvent_isSome_coordForkOp k _
  rw [hmap]
  simp only [hcount]
  -- Reading the sampled table through `isSome` is exactly `acceptTable` on `indepTable`.
  rw [show expectedValue (Fintype.mPi sub)
        (fun tbl => ((goodSet k fun c => (tbl c).isSome).card : ℝ≥0∞) / Fintype.card (ι → S))
      = expectedValue (acceptTable (fun _ y => (Option.isSome y)) (indepTable sub))
        (fun ρ' => ((goodSet k ρ').card : ℝ≥0∞) / Fintype.card (ι → S)) from by
      rw [acceptTable, indepTable, expectedValue_map]]
  rw [forkSucc_eq_forkSuccOf k q hq1, forkSuccOf, expectedValue_def]
  refine tsum_congr fun ρ' => congrArg (· * _) ?_
  rw [probOutput_acceptTable_indepTable_eq_bernoulliTable (fun _ y => (Option.isSome y)) sub ρ']

/-- **The recursion's success probability is the analytic functional.** The independent Bernoulli
coupling `multiSucc` is defined by is not assumed here: it is what running the sub-extractor
independently at each first challenge produces. -/
theorem probEvent_isSome_multiForkOp : ∀ (μ k : ℕ) (ρ : Transcript ι S μ → Bool),
    Pr[fun r => r.isSome | multiForkOp μ k ρ]
      = multiSucc k fun t => if ρ t then 1 else 0
  | 0, k, ρ => by
      classical
      rw [multiForkOp_zero, multiSucc_zero]
      by_cases hρ : ρ PUnit.unit <;> simp [hρ]
  | μ + 1, k, ρ => by
      rw [probEvent_isSome_multiForkOp_succ, multiSucc_succ]
      exact congrArg (forkSucc k)
        (funext fun c => probEvent_isSome_multiForkOp μ k fun t => ρ (c, t))

/-- **The success clause of Lemma 7.2.** The `μ`-round recursion succeeds with probability at least
`ε - μℓ(k-1)/N`, where `ε` is the accepting ratio of the transcript table. -/
theorem sub_le_probEvent_isSome_multiForkOp [Nonempty S] (μ k : ℕ)
    (ρ : Transcript ι S μ → Bool) :
    avgTranscript (fun t => if ρ t then 1 else 0) - μ * roundLoss ι S k
      ≤ Pr[fun r => r.isSome | multiForkOp μ k ρ] := by
  rw [probEvent_isSome_multiForkOp]
  exact sub_le_multiSucc k _ fun t => by split <;> simp

end OracleComp
