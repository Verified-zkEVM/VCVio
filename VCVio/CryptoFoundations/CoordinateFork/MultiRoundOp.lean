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

`multiForkOpW` is the same recursion charging each entry examined what the extraction there cost
rather than counting it as one, and `expectedValue_weight_multiForkOpW_le` is the paper's
`(ℓ(k-1)+1)^μ`. Charging is what makes the levels multiply: `coordForkOpW`'s bound is proportional
to the average charge of an entry, so instantiating the charge at the level below and applying
`expectedValue_bind` composes. No independence argument enters, and neither does Wald's identity.
`probEvent_isSome_multiForkOpW` and `multiForkOpW_success` carry the success and output clauses
across, so all three clauses of Lemma 7.2 hold of the same computation.

What this still does not do is query a prover: the extractor consumes a fixed acceptance table on
transcripts, exactly as at `μ = 1`. Sampling the level-below table up front is the same modelling
device — the sub-extractor with its coins fixed is a function of the first challenge — and it is
only the *charge*, not the sampling, that models an implementation's running time.
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
    ProbComp (Option (Finset (Transcript ι S μ)) × ℕ)
  | 0, _, ρ => pure (if ρ PUnit.unit then some {PUnit.unit} else none, 1)
  | μ + 1, k, ρ => do
      let tbl ← Fintype.mPi fun c => multiForkOp μ k fun t => ρ (c, t)
      let r ← coordForkOp k fun c => (tbl c).1.isSome
      return (r.1.map fun X => X.biUnion fun c => ((tbl c).1.getD ∅).image fun t => (c, t), r.2)

@[simp] theorem multiForkOp_zero (k : ℕ) (ρ : Transcript ι S 0 → Bool) :
    multiForkOp 0 k ρ = pure (if ρ PUnit.unit then some {PUnit.unit} else none, 1) := rfl

theorem multiForkOp_succ (μ k : ℕ) (ρ : Transcript ι S (μ + 1) → Bool) :
    multiForkOp (μ + 1) k ρ =
      (do
        let tbl ← Fintype.mPi fun c => multiForkOp μ k fun t => ρ (c, t)
        let r ← coordForkOp k fun c => (tbl c).1.isSome
        return (r.1.map fun X =>
          X.biUnion fun c => ((tbl c).1.getD ∅).image fun t => (c, t), r.2)) := rfl

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
    (T : Finset (Transcript ι S μ)) (cost : ℕ), (some T, cost) ∈ support (multiForkOp μ k ρ) →
      IsChallengeTree k μ (T.image Transcript.toList) ∧ ∀ t ∈ T, ρ t
  | 0, k, ρ, T, cost, h => by
      classical
      rw [multiForkOp_zero, support_pure, Set.mem_singleton_iff] at h
      obtain ⟨h, -⟩ := Prod.ext_iff.mp h
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
  | μ + 1, k, ρ, T, cost, h => by
      classical
      rw [multiForkOp_succ, mem_support_bind_iff] at h
      obtain ⟨tbl, htbl, h⟩ := h
      rw [mem_support_bind_iff] at h
      obtain ⟨r, hr, h⟩ := h
      simp only [support_pure, Set.mem_singleton_iff] at h
      obtain ⟨h, -⟩ := Prod.ext_iff.mp h
      cases hr1 : r.1 with
      | none => rw [hr1] at h; simp at h
      | some X =>
      rw [hr1] at h
      simp only [Option.map_some, Option.some.injEq] at h
      subst h
      obtain ⟨hss, hacc⟩ := coordForkOp_success (X := X) (cost := r.2) (by rw [← hr1]; exact hr)
      -- Every child challenge names a successful sub-extraction.
      have hchild : ∀ c ∈ X, IsChallengeTree k μ (((tbl c).1.getD ∅).image Transcript.toList) ∧
          ∀ t ∈ (tbl c).1.getD ∅, ρ (c, t) := by
        intro c hc
        obtain ⟨Tc, hTc⟩ : ∃ Tc, (tbl c).1 = some Tc := Option.isSome_iff_exists.mp (hacc c hc)
        have hsub : (some Tc, (tbl c).2) ∈ support (multiForkOp μ k fun t => ρ (c, t)) := by
          rw [← hTc]; exact mem_support_mPi _ tbl htbl c
        rw [hTc]
        exact multiForkOp_success μ k _ Tc (tbl c).2 hsub
      refine ⟨?_, ?_⟩
      · rw [Finset.biUnion_image,
          Finset.biUnion_congr rfl fun a _ => image_toList_image_prod a ((tbl a).1.getD ∅)]
        exact isChallengeTree_biUnion hss fun c hc => (hchild c hc).1
      · intro t ht
        obtain ⟨c, hc, ht⟩ := Finset.mem_biUnion.mp ht
        obtain ⟨t', ht', rfl⟩ := Finset.mem_image.mp ht
        exact (hchild c hc).2 t' ht'

/-! ## The success probability -/

/-- One round of the recursion, in the shape `Realizability.lean` identifies with an independent
Bernoulli table: the sub-extractors run independently, one per first challenge. -/
theorem probEvent_isSome_multiForkOp_succ (μ k : ℕ) (ρ : Transcript ι S (μ + 1) → Bool) :
    Pr[fun r => r.1.isSome | multiForkOp (μ + 1) k ρ]
      = forkSucc k fun c => Pr[fun r => r.1.isSome | multiForkOp μ k fun t => ρ (c, t)] := by
  classical
  set sub : (ι → S) → ProbComp (Option (Finset (Transcript ι S μ)) × ℕ) :=
    fun c => multiForkOp μ k fun t => ρ (c, t) with hsub
  set q : (ι → S) → ℝ≥0∞ := fun c => Pr[fun r => r.1.isSome | sub c] with hq
  have hq1 : ∀ c, q c ≤ 1 := fun _ => probEvent_le_one
  -- Discarding the returned tree leaves the single-round loop's success event.
  have hmap : Pr[fun r => r.1.isSome | multiForkOp (μ + 1) k ρ]
      = expectedValue (Fintype.mPi sub)
        (fun tbl => Pr[fun r => r.1.isSome | coordForkOp k fun c => (tbl c).1.isSome]) := by
    rw [multiForkOp_succ, probEvent_bind_eq_tsum, expectedValue_def]
    refine tsum_congr fun tbl => congrArg _ ?_
    rw [bind_pure_comp, probEvent_map]
    exact congrArg _ (funext fun r => by simp)
  -- The single-round success probability is a functional of the sampled table.
  have hcount : ∀ tbl : (ι → S) → Option (Finset (Transcript ι S μ)) × ℕ,
      Pr[fun r => r.1.isSome | coordForkOp k fun c => (tbl c).1.isSome]
        = ((goodSet k fun c => (tbl c).1.isSome).card : ℝ≥0∞) / Fintype.card (ι → S) := fun tbl =>
    probEvent_isSome_coordForkOp k _
  rw [hmap]
  simp only [hcount]
  -- Reading the sampled table through `isSome` is exactly `acceptTable` on `indepTable`.
  rw [show expectedValue (Fintype.mPi sub)
        (fun tbl => ((goodSet k fun c => (tbl c).1.isSome).card : ℝ≥0∞) / Fintype.card (ι → S))
      = expectedValue (acceptTable (fun _ y => (Option.isSome y.1)) (indepTable sub))
        (fun ρ' => ((goodSet k ρ').card : ℝ≥0∞) / Fintype.card (ι → S)) from by
      rw [acceptTable, indepTable, expectedValue_map]]
  rw [forkSucc_eq_forkSuccOf k q hq1, forkSuccOf, expectedValue_def]
  refine tsum_congr fun ρ' => congrArg (· * _) ?_
  exact probOutput_acceptTable_indepTable_eq_bernoulliTable
    (fun (_ : ι → S) (y : Option (Finset (Transcript ι S μ)) × ℕ) => y.1.isSome) sub ρ'

/-- **The recursion's success probability is the analytic functional.** The independent Bernoulli
coupling `multiSucc` is defined by is not assumed here: it is what running the sub-extractor
independently at each first challenge produces. -/
theorem probEvent_isSome_multiForkOp : ∀ (μ k : ℕ) (ρ : Transcript ι S μ → Bool),
    Pr[fun r => r.1.isSome | multiForkOp μ k ρ]
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
      ≤ Pr[fun r => r.1.isSome | multiForkOp μ k ρ] := by
  rw [probEvent_isSome_multiForkOp]
  exact sub_le_multiSucc k _ fun t => by split <;> simp

/-! ## The number of lookups, per level -/

/-- **Each round looks at at most `1 + ℓ(k-1)` of the level below**, in expectation. The count
`multiForkOp` reports is the number of level-`μ` extractions the top-level loop examined.

The paper's `(ℓ(k-1)+1)^μ` is the product of these across levels, and that composition is *not*
proved here. It is Wald's identity — the total base-level work is `∑ᵢ Xᵢ` over the `T` lookups the
top loop makes, and `𝔼[∑ᵢ≤T Xᵢ] = 𝔼[T] · 𝔼[X]` needs `{T ≥ i}` to be independent of the `i`-th
sub-run. That holds because the loop chooses which challenge to look at *before* reading it, but
that fact is not available here: `multiForkOp` pre-samples the whole table of sub-extractions
through `Fintype.mPi`, which is what makes the coupling derivable for the success bound, and an
eager table cannot express "queried before read". Doing so needs the loop to consume its table
through an oracle, at which point the count is `expectedQueries` rather than returned data. -/
theorem expectedValue_cost_multiForkOp_le [Nonempty S] (μ k : ℕ)
    (ρ : Transcript ι S (μ + 1) → Bool) :
    expectedValue (multiForkOp (μ + 1) k ρ) (fun r => (r.2 : ℝ≥0∞))
      ≤ 1 + Fintype.card ι * (k - 1 : ℕ) := by
  have hinner : ∀ tbl : (ι → S) → Option (Finset (Transcript ι S μ)) × ℕ,
      expectedValue (do
          let r ← coordForkOp k fun c => (tbl c).1.isSome
          return (r.1.map fun X : Finset (ι → S) =>
            X.biUnion fun c => ((tbl c).1.getD ∅).image fun t : Transcript ι S μ =>
              show Transcript ι S (μ + 1) from (c, t), r.2))
        (fun p => (p.2 : ℝ≥0∞))
        ≤ 1 + Fintype.card ι * (k - 1 : ℕ) := by
    intro tbl
    rw [expectedValue_bind]
    refine le_trans (le_of_eq (tsum_congr fun r => congrArg _ ?_))
      (expectedValue_cost_coordForkOp_le k fun c => (tbl c).1.isSome)
    exact expectedValue_pure _ _
  rw [multiForkOp_succ, expectedValue_bind]
  exact le_trans (expectedValue_mono _ hinner)
    (le_of_eq (expectedValue_const (probFailure_of_liftM_PMF _) _))

/-! ## The weighted recursion

`multiForkOp` counts table lookups, and its per-level bound does not compose: multiplying the
levels needs the cost of a lookup to be the sub-extractor's, not one.

`multiForkOpW` is the same recursion with that accounting. The table it samples is the level-below
extractor with its coins fixed — a *pair* at each first challenge, recording what that extraction
returned and what it cost — and the fork then examines entries and is charged the cost each entry
recorded. The charge is therefore the running time of an implementation that extracts only at the
challenges the fork looks at, which is what the paper's `(ℓ(k-1)+1)^μ` counts; sampling the table
up front is the same modelling device as §7's fixed acceptance table
(`CoordinateFork/Realizability.lean`), and `evalDist_map_fst_multiForkOpW` confirms it changes
nothing about what the recursion returns.

`expectedValue_weight_multiForkOpW_le` is the payoff, and the composition the branch had been
missing. -/

/-- The `μ`-round extractor, charging each entry examined what the extraction there cost. -/
noncomputable def multiForkOpW : (μ : ℕ) → (k : ℕ) → (ρ : Transcript ι S μ → Bool) →
    ProbComp (Option (Finset (Transcript ι S μ)) × ℝ≥0∞)
  | 0, _, ρ => pure (if ρ PUnit.unit then some {PUnit.unit} else none, 1)
  | μ + 1, k, ρ => do
      let tbl ← Fintype.mPi fun c => multiForkOpW μ k fun t => ρ (c, t)
      let r ← coordForkOpW k (fun c => (tbl c).1.isSome) (fun c => (tbl c).2)
      return (r.1.map fun X => X.biUnion fun c => ((tbl c).1.getD ∅).image fun t => (c, t), r.2)

@[simp] theorem multiForkOpW_zero (k : ℕ) (ρ : Transcript ι S 0 → Bool) :
    multiForkOpW 0 k ρ = pure (if ρ PUnit.unit then some {PUnit.unit} else none, 1) := rfl

theorem multiForkOpW_succ (μ k : ℕ) (ρ : Transcript ι S (μ + 1) → Bool) :
    multiForkOpW (μ + 1) k ρ =
      (do
        let tbl ← Fintype.mPi fun c => multiForkOpW μ k fun t => ρ (c, t)
        let r ← coordForkOpW k (fun c => (tbl c).1.isSome) (fun c => (tbl c).2)
        return (r.1.map fun X => X.biUnion fun c => ((tbl c).1.getD ∅).image fun t => (c, t),
          r.2)) := rfl

omit [DecidableEq ι] [Fintype ι] [DecidableEq S] [Fintype S] [SampleableType (ι → S)] in
private theorem map_fst_bind_pair {β γ : Type} (m : ProbComp (Option (Finset (ι → S)) × β))
    (F : Option (Finset (ι → S)) → γ) :
    (·.1) <$> (m >>= fun r => (pure (F r.1, r.2) : ProbComp (γ × β)))
      = F <$> ((·.1) <$> m) := by
  rw [map_bind, Functor.map_map, map_eq_bind_pure_comp]
  exact bind_congr fun r => by rw [map_pure]; rfl

private theorem evalDist_bind_congr_left {α β : Type} {mx my : ProbComp α}
    (h : evalDist mx = evalDist my) (f : α → ProbComp β) :
    evalDist (mx >>= f) = evalDist (my >>= f) := by
  refine evalDist_ext fun y => ?_
  rw [probOutput_bind_eq_tsum, probOutput_bind_eq_tsum]
  exact tsum_congr fun x => by rw [evalDist_ext_iff.mp h x]

/-- **The weighted recursion returns what the counted one returns.** Every success and output
statement about `multiForkOp` therefore transfers to `multiForkOpW`. -/
theorem evalDist_map_fst_multiForkOpW : ∀ (μ k : ℕ) (ρ : Transcript ι S μ → Bool),
    evalDist ((·.1) <$> multiForkOpW μ k ρ) = evalDist ((·.1) <$> multiForkOp μ k ρ)
  | 0, k, ρ => by rw [multiForkOpW_zero, multiForkOp_zero]; simp
  | μ + 1, k, ρ => by
      classical
      -- The continuation sees the table only through its first components.
      have hinner : ∀ (t : (ι → S) → Option (Finset (Transcript ι S μ)))
          (Γ : (ι → S) → ℝ≥0∞),
          (·.1) <$> (coordForkOpW k (fun c => (t c).isSome) Γ >>= fun r =>
              (pure (r.1.map fun X => X.biUnion fun c => ((t c).getD ∅).image fun s => (c, s),
                r.2) : ProbComp (Option (Finset (Transcript ι S (μ + 1))) × ℝ≥0∞)))
            = (·.1) <$> (coordForkOp k (fun c => (t c).isSome) >>= fun r =>
              (pure (r.1.map fun X => X.biUnion fun c => ((t c).getD ∅).image fun s => (c, s),
                r.2) : ProbComp (Option (Finset (Transcript ι S (μ + 1))) × ℕ))) := by
        intro t Γ
        rw [map_fst_bind_pair, map_fst_bind_pair, map_fst_coordForkOpW]
      rw [multiForkOpW_succ, multiForkOp_succ, map_bind, map_bind]
      simp only [hinner]
      -- Both sides now bind the same continuation of the table's first components.
      set K : ((ι → S) → Option (Finset (Transcript ι S μ))) →
          ProbComp (Option (Finset (Transcript ι S (μ + 1)))) := fun t =>
        (·.1) <$> (coordForkOp k (fun c => (t c).isSome) >>= fun r =>
          (pure (r.1.map fun X => X.biUnion fun c => ((t c).getD ∅).image fun s => (c, s), r.2) :
            ProbComp (Option (Finset (Transcript ι S (μ + 1))) × ℕ))) with hK
      have hpush : ∀ {β : Type} (f : (ι → S) → ProbComp (Option (Finset (Transcript ι S μ)) × β)),
          (Fintype.mPi f >>= fun tbl => K fun c => (tbl c).1)
            = ((fun tbl c => (tbl c).1) <$> Fintype.mPi f) >>= K := by
        intro β f
        rw [map_eq_bind_pure_comp, bind_assoc]
        exact bind_congr fun tbl => by rw [Function.comp_apply, pure_bind]
      rw [hpush, hpush]
      refine evalDist_bind_congr_left ?_ K
      rw [evalDist_map_coord_mPi, evalDist_map_coord_mPi]
      exact evalDist_mPi_congr fun c => evalDist_map_fst_multiForkOpW μ k fun t => ρ (c, t)


omit [DecidableEq ι] [Fintype ι] [DecidableEq S] [Fintype S] [SampleableType (ι → S)] in
private theorem support_eq_of_evalDist_eq {α : Type} {mx my : ProbComp α}
    (h : evalDist mx = evalDist my) : support mx = support my :=
  Set.ext fun x => by rw [mem_support_iff, mem_support_iff, evalDist_ext_iff.mp h x]

omit [SampleableType (ι → S)] in
private theorem probEvent_isSome_eq_map {α β : Type} (m : ProbComp (Option α × β)) :
    Pr[fun r => r.1.isSome | m] = Pr[fun x => x.isSome | (·.1) <$> m] := by
  rw [probEvent_map]
  rfl

/-- **The success clause transfers.** The weighted recursion succeeds exactly as often as the
counted one, so `sub_le_multiSucc`'s `ε - μℓ(k-1)/N` bound applies to it unchanged. -/
theorem probEvent_isSome_multiForkOpW (μ k : ℕ) (ρ : Transcript ι S μ → Bool) :
    Pr[fun r => r.1.isSome | multiForkOpW μ k ρ]
      = Pr[fun r => r.1.isSome | multiForkOp μ k ρ] := by
  rw [probEvent_isSome_eq_map, probEvent_isSome_eq_map, probEvent_def, probEvent_def,
    evalDist_map_fst_multiForkOpW μ k ρ]

/-- Lemma 7.2's success bound, for the weighted recursion. -/
theorem sub_le_probEvent_isSome_multiForkOpW [Nonempty S] (μ k : ℕ)
    (ρ : Transcript ι S μ → Bool) :
    avgTranscript (fun t => if ρ t then 1 else 0) - μ * roundLoss ι S k
      ≤ Pr[fun r => r.1.isSome | multiForkOpW μ k ρ] := by
  rw [probEvent_isSome_multiForkOpW]
  exact sub_le_probEvent_isSome_multiForkOp μ k ρ

/-- **The output clause transfers.** A successful weighted run returns accepting transcripts whose
challenge sequences form a tree of challenges, exactly as `multiForkOp_success` says. -/
theorem multiForkOpW_success (μ k : ℕ) (ρ : Transcript ι S μ → Bool)
    (T : Finset (Transcript ι S μ)) (w : ℝ≥0∞) (h : (some T, w) ∈ support (multiForkOpW μ k ρ)) :
    IsChallengeTree k μ (T.image Transcript.toList) ∧ ∀ t ∈ T, ρ t := by
  classical
  have hmap : some T ∈ support ((·.1) <$> multiForkOpW μ k ρ) := by
    rw [support_map]
    exact ⟨_, h, rfl⟩
  rw [support_eq_of_evalDist_eq (evalDist_map_fst_multiForkOpW μ k ρ), support_map] at hmap
  obtain ⟨r, hr, hr'⟩ := hmap
  obtain ⟨T', cost⟩ := r
  obtain rfl : T' = some T := hr'
  exact multiForkOp_success μ k ρ T cost hr

/-- **The `(ℓ(k-1)+1)^μ` bound.** Each level charges the level below only at the entries it
examines, and `expectedValue_weight_coordForkOpW_le_of_le` multiplies the levels through
`expectedValue_bind`. This is the expected-query clause of Lemma 7.2. -/
theorem expectedValue_weight_multiForkOpW_le [Nonempty S] : ∀ (μ k : ℕ)
    (ρ : Transcript ι S μ → Bool),
    expectedValue (multiForkOpW μ k ρ) (fun r => r.2)
      ≤ (1 + Fintype.card ι * ((k - 1 : ℕ) : ℝ≥0∞)) ^ μ
  | 0, k, ρ => by rw [multiForkOpW_zero, expectedValue_pure, pow_zero]
  | μ + 1, k, ρ => by
    classical
    have hCne : (Fintype.card (ι → S) : ℝ≥0∞) ≠ 0 := by simp [Fintype.card_ne_zero]
    have hCtop : (Fintype.card (ι → S) : ℝ≥0∞) ≠ ⊤ := by finiteness
    have hfail : ∀ c : ι → S, Pr[⊥ | multiForkOpW μ k fun t => ρ (c, t)] = 0 :=
      fun c => probFailure_of_liftM_PMF _
    rw [multiForkOpW_succ, expectedValue_bind]
    -- Conditioned on the table, the fork's charge is bounded by the table's average entry.
    have hstep : ∀ tbl : (ι → S) → Option (Finset (Transcript ι S μ)) × ℝ≥0∞,
        expectedValue
            (coordForkOpW k (fun c => (tbl c).1.isSome) (fun c => (tbl c).2) >>= fun r =>
              (pure (r.1.map fun X => X.biUnion fun c => ((tbl c).1.getD ∅).image fun s => (c, s),
                r.2) : ProbComp (Option (Finset (Transcript ι S (μ + 1))) × ℝ≥0∞)))
            (fun r => r.2)
          ≤ (1 + Fintype.card ι * ((k - 1 : ℕ) : ℝ≥0∞)) *
              ((∑ c : ι → S, (tbl c).2) / Fintype.card (ι → S)) := by
      intro tbl
      rw [expectedValue_bind]
      refine le_trans (le_of_eq ?_)
        (expectedValue_weight_coordForkOpW_le k (fun c => (tbl c).1.isSome) (fun c => (tbl c).2))
      exact expectedValue_congr_of_mem_support _ fun r _ => by rw [expectedValue_pure]
    refine le_trans (expectedValue_mono _ hstep) ?_
    -- Average the table's entries: each is a level-`μ` run, so the induction hypothesis applies.
    simp only [ENNReal.div_eq_inv_mul, ← mul_assoc]
    rw [expectedValue_const_mul, expectedValue_finsetSum]
    have hcoord : ∀ c : ι → S,
        expectedValue (Fintype.mPi fun c' => multiForkOpW μ k fun t => ρ (c', t))
            (fun tbl => (tbl c).2)
          = expectedValue (multiForkOpW μ k fun t => ρ (c, t)) (fun p => p.2) :=
      fun c => expectedValue_coord_mPi _ hfail c (fun p => p.2)
    rw [Finset.sum_congr rfl fun c _ => hcoord c]
    calc (1 + (Fintype.card ι : ℝ≥0∞) * ((k - 1 : ℕ) : ℝ≥0∞))
            * ((Fintype.card (ι → S) : ℝ≥0∞))⁻¹
            * ∑ c : ι → S, expectedValue (multiForkOpW μ k fun t => ρ (c, t)) (fun p => p.2)
        ≤ (1 + (Fintype.card ι : ℝ≥0∞) * ((k - 1 : ℕ) : ℝ≥0∞))
            * ((Fintype.card (ι → S) : ℝ≥0∞))⁻¹
            * ∑ _c : ι → S, (1 + (Fintype.card ι : ℝ≥0∞) * ((k - 1 : ℕ) : ℝ≥0∞)) ^ μ :=
          mul_le_mul' le_rfl (Finset.sum_le_sum fun c _ =>
            expectedValue_weight_multiForkOpW_le μ k fun t => ρ (c, t))
      _ = (1 + (Fintype.card ι : ℝ≥0∞) * ((k - 1 : ℕ) : ℝ≥0∞)) ^ (μ + 1) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
            show (1 + (Fintype.card ι : ℝ≥0∞) * ((k - 1 : ℕ) : ℝ≥0∞))
                  * ((Fintype.card (ι → S) : ℝ≥0∞))⁻¹
                  * ((Fintype.card (ι → S) : ℝ≥0∞)
                      * (1 + (Fintype.card ι : ℝ≥0∞) * ((k - 1 : ℕ) : ℝ≥0∞)) ^ μ)
                = (((Fintype.card (ι → S) : ℝ≥0∞))⁻¹ * (Fintype.card (ι → S) : ℝ≥0∞))
                  * ((1 + (Fintype.card ι : ℝ≥0∞) * ((k - 1 : ℕ) : ℝ≥0∞))
                      * (1 + (Fintype.card ι : ℝ≥0∞) * ((k - 1 : ℕ) : ℝ≥0∞)) ^ μ) from by ring,
            ENNReal.inv_mul_cancel hCne hCtop, one_mul, ← pow_succ']

end OracleComp
