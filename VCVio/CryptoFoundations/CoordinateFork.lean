/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import ToMathlib.Combinatorics.ChallengeTree
public import VCVio.EvalDist.CoordinateFork
public import VCVio.OracleComp.Constructions.SampleableType

/-!
# The coordinate-wise rewinding extractor

Lemma 7.1 of Fenzi–Moghaddas–Nguyen: for a challenge space `ι → S` and an adversary accepting a
`ε` fraction of challenges, an extractor that resamples one coordinate at a time recovers a
coordinate-wise `k`-special sound set of accepting challenges with probability at least
`ε - ℓ * (k - 1) / N`, where `ℓ = Fintype.card ι` and `N = Fintype.card S`.

Following `seededFork`, randomness comes first and the core is deterministic: `coordFork` samples
an *acceptance table* `ρ : (ι → S) → Bool` and a challenge `c₀`, then runs `coordForkCore`. The
core succeeds exactly when `c₀` accepts and every column of `c₀` holds at least `k` accepting
values (`coordForkCore_isSome_iff`), which is `OracleComp.EvalDist.goodSet` — so the success
probability is a cardinality ratio and the bound is the already-proved counting inequality
averaged over tables.

Collecting the replacements is a *total* operation here: which `k - 1` accepting values a
coordinate contributes is irrelevant to both success and the output's special-soundness, so the
extractor takes the first `k - 1` in enumeration order. Sampling that order uniformly is what buys
the paper's expected query count of `ℓ * (k - 1) + 1`; it is not needed for the success bound and
is left to the query-cost development.
-/

@[expose] public section

open Finset CoordinateWise OracleComp OracleComp.EvalDist

open scoped ENNReal

namespace OracleComp

variable {ι S : Type} [DecidableEq ι] [Fintype ι] [DecidableEq S] [Fintype S]
variable {k : ℕ} {ρ : (ι → S) → Bool} {c₀ : ι → S}

/-! ## The deterministic core -/

/-- The replacements available at coordinate `j`: values other than the one `c₀` already uses that
keep the challenge accepting. -/
def hitSet (ρ : (ι → S) → Bool) (c₀ : ι → S) (j : ι) : Finset S :=
  (Finset.univ.erase (c₀ j)).filter fun x => ρ (Function.update c₀ j x)

/-- The `k - 1` replacements the extractor keeps at coordinate `j`. Any choice would do; this one
takes the first `k - 1` in enumeration order. -/
noncomputable def replacementSet (k : ℕ) (ρ : (ι → S) → Bool) (c₀ : ι → S) (j : ι) : Finset S :=
  ((hitSet ρ c₀ j).toList.take (k - 1)).toFinset

/-- The extractor's deterministic core: abort unless `c₀` accepts and every coordinate offers
`k - 1` accepting replacements, and otherwise return the challenge family they generate. -/
noncomputable def coordForkCore (k : ℕ) (ρ : (ι → S) → Bool) (c₀ : ι → S) :
    Option (Finset (ι → S)) :=
  if ρ c₀ ∧ ∀ j, k - 1 ≤ (hitSet ρ c₀ j).card then
    some (coordFamily c₀ (replacementSet k ρ c₀))
  else none

/-! ### The core's success condition -/

omit [Fintype ι] in
/-- An accepting challenge occupies one slot of each of its own columns, so the remaining
replacements number one fewer than the column count. -/
theorem card_hitSet_succ (hacc : ρ c₀) (j : ι) :
    (hitSet ρ c₀ j).card + 1 = columnCount (fun c => ρ c = true) j c₀ := by
  classical
  have hmem : c₀ j ∈ Finset.univ.filter fun x : S => ρ (Function.update c₀ j x) :=
    mem_filter_coord_self (accept := fun c => ρ c = true) hacc j
  have hpos : 0 < (Finset.univ.filter fun x : S => ρ (Function.update c₀ j x)).card :=
    Finset.card_pos.mpr ⟨_, hmem⟩
  rw [hitSet, Finset.filter_erase, Finset.card_erase_of_mem hmem]
  simp only [columnCount]
  omega

theorem coordForkCore_isSome_iff :
    (coordForkCore k ρ c₀).isSome ↔ c₀ ∈ goodSet k ρ := by
  classical
  -- Having `k - 1` replacements left over is the same as a column of at least `k` accepting
  -- values, because the accepting `c₀` itself occupies one slot.
  have hiff : (ρ c₀ ∧ ∀ j, k - 1 ≤ (hitSet ρ c₀ j).card) ↔
      (ρ c₀ ∧ ∀ j, k ≤ columnCount (fun c => ρ c = true) j c₀) := by
    constructor <;>
      · rintro ⟨hacc, hall⟩
        refine ⟨hacc, fun j => ?_⟩
        have h1 := card_hitSet_succ hacc j
        have h2 := hall j
        omega
  rw [coordForkCore]
  simp only [goodSet, Finset.mem_filter, Finset.mem_univ, true_and, ← hiff]
  split <;> simp_all

/-- The set of challenges on which the core succeeds is exactly `goodSet`. -/
theorem filter_isSome_coordForkCore (k : ℕ) (ρ : (ι → S) → Bool) :
    (Finset.univ.filter fun c₀ : ι → S => (coordForkCore k ρ c₀).isSome) = goodSet k ρ := by
  ext c₀
  simp [coordForkCore_isSome_iff]

/-! ### The core's output -/

omit [Fintype ι] in
theorem notMem_replacementSet (k : ℕ) (ρ : (ι → S) → Bool) (c₀ : ι → S) (j : ι) :
    c₀ j ∉ replacementSet k ρ c₀ j := by
  classical
  simp only [replacementSet, List.mem_toFinset]
  intro hmem
  have := List.mem_of_mem_take hmem
  rw [Finset.mem_toList, hitSet, Finset.mem_filter] at this
  exact (Finset.mem_erase.mp this.1).1 rfl

omit [Fintype ι] in
theorem card_replacementSet {j : ι} (hcard : k - 1 ≤ (hitSet ρ c₀ j).card) :
    (replacementSet k ρ c₀ j).card = k - 1 := by
  classical
  have hnodup : ((hitSet ρ c₀ j).toList.take (k - 1)).Nodup :=
    (Finset.nodup_toList _).sublist (List.take_sublist _ _)
  rw [replacementSet, List.toFinset_card_of_nodup hnodup, List.length_take,
    Finset.length_toList]
  omega

omit [Fintype ι] in
theorem accept_of_mem_replacementSet {j : ι} {x : S} (hx : x ∈ replacementSet k ρ c₀ j) :
    ρ (Function.update c₀ j x) := by
  classical
  simp only [replacementSet, List.mem_toFinset] at hx
  have := List.mem_of_mem_take hx
  rw [Finset.mem_toList, hitSet, Finset.mem_filter] at this
  exact this.2

/-- **The core's output guarantee.** On success the extractor returns a coordinate-wise
`k`-special sound set of accepting challenges, of size `ℓ * (k - 1) + 1`. -/
theorem coordForkCore_success {X : Finset (ι → S)} (h : coordForkCore k ρ c₀ = some X) :
    IsCoordSpecialSound k X ∧ ∀ c ∈ X, ρ c := by
  classical
  rw [coordForkCore] at h
  split at h
  · rename_i hcond
    obtain ⟨hacc, hall⟩ := hcond
    obtain rfl : X = coordFamily c₀ (replacementSet k ρ c₀) := (Option.some.inj h).symm
    have hnot : ∀ j, c₀ j ∉ replacementSet k ρ c₀ j := notMem_replacementSet k ρ c₀
    have hcards : ∀ j, (replacementSet k ρ c₀ j).card = k - 1 := fun j =>
      card_replacementSet (hall j)
    refine ⟨isCoordSpecialSound_coordFamily hnot hcards, fun c hc => ?_⟩
    rcases mem_coordFamily.mp hc with rfl | ⟨j, u, hu, rfl⟩
    · exact hacc
    · exact accept_of_mem_replacementSet hu
  · exact absurd h (by simp)

/-- The single-round output read as a one-round tree of challenges (Definition 2.30).

This is the `μ = 1` case of Lemma 7.2's output clause. The general case needs a multi-round
extractor that emits transcripts rather than a success probability, and is deferred. -/
theorem isChallengeTree_of_coordForkCore_success {X : Finset (ι → S)}
    (h : coordForkCore k ρ c₀ = some X) :
    IsChallengeTree k 1 (X.image fun c => [c]) :=
  isChallengeTree_one (coordForkCore_success h).1

/-! ## The extractor -/

variable [SampleableType (ι → S)]

/-- The coordinate-wise rewinding extractor: sample an acceptance table and a challenge, then run
the deterministic core.

The sampled table is returned alongside the challenge set. Without it, "the returned challenges
accept" could not be stated as a property of the output, and an existential over tables would be
satisfied by the all-accepting table rather than by the one that actually produced the set. -/
noncomputable def coordFork (k : ℕ) (D : ProbComp ((ι → S) → Bool)) :
    ProbComp (Option (((ι → S) → Bool) × Finset (ι → S))) := do
  let ρ ← D
  let c₀ ← $ᵗ (ι → S)
  return (coordForkCore k ρ c₀).map fun X => (ρ, X)

/-- What the extractor promises when it succeeds: the challenges it returns form an `SS(S, ℓ, k)`
set — in particular there are exactly `ℓ * (k - 1) + 1` of them — and every one of them accepts
under the very table that produced them. -/
def GoodOutput (k : ℕ) (r : Option (((ι → S) → Bool) × Finset (ι → S))) : Prop :=
  ∃ ρ X, r = some (ρ, X) ∧ IsCoordSpecialSound k X ∧ ∀ c ∈ X, ρ c

/-- Every successful run satisfies `GoodOutput`, with the table bound to the run that produced the
challenge set. -/
theorem coordFork_success {k : ℕ} {D : ProbComp ((ι → S) → Bool)}
    {ρ : (ι → S) → Bool} {X : Finset (ι → S)}
    (h : some (ρ, X) ∈ support (coordFork k D)) :
    ρ ∈ support D ∧ (∃ c₀, coordForkCore k ρ c₀ = some X) ∧
      IsCoordSpecialSound k X ∧ ∀ c ∈ X, ρ c := by
  simp only [coordFork, support_bind, Set.mem_iUnion, support_pure] at h
  obtain ⟨ρ', hρ', c₀, -, hX⟩ := h
  rw [Set.mem_singleton_iff] at hX
  obtain ⟨Y, hY, hpair⟩ := Option.map_eq_some_iff.mp hX.symm
  obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ hpair
  exact ⟨hρ', ⟨c₀, hY⟩, coordForkCore_success hY⟩

theorem goodOutput_of_mem_support {k : ℕ} {D : ProbComp ((ι → S) → Bool)}
    {r : Option (((ι → S) → Bool) × Finset (ι → S))} (h : r ∈ support (coordFork k D))
    (hr : r.isSome) : GoodOutput k r := by
  obtain ⟨⟨ρ, X⟩, rfl⟩ := Option.isSome_iff_exists.mp hr
  obtain ⟨-, -, hss, hacc⟩ := coordFork_success h
  exact ⟨ρ, X, rfl, hss, hacc⟩

/-- The success probability equals the chance that a uniform challenge lands in `goodSet`,
averaged over the table distribution. -/
theorem probEvent_isSome_coordFork (k : ℕ) (D : ProbComp ((ι → S) → Bool)) :
    Pr[fun r => r.isSome | coordFork k D] = forkSuccOf k D := by
  classical
  rw [coordFork, forkSuccOf, probEvent_bind_eq_tsum]
  refine tsum_congr fun ρ => congrArg _ ?_
  rw [probEvent_bind_eq_tsum]
  have hinner : ∀ c₀ : ι → S,
      Pr[fun r => r.isSome |
          (pure ((coordForkCore k ρ c₀).map fun X => (ρ, X)) : ProbComp _)]
        = if (coordForkCore k ρ c₀).isSome then 1 else 0 := by
    intro c₀; by_cases h : (coordForkCore k ρ c₀).isSome <;> simp [h]
  simp_rw [hinner, mul_ite, mul_one, mul_zero]
  rw [← probEvent_eq_tsum_ite, probEvent_uniformSample, filter_isSome_coordForkCore]

/-- Succeeding and satisfying `GoodOutput` are the same event: every successful run is good. -/
theorem probEvent_goodOutput_coordFork (k : ℕ) (D : ProbComp ((ι → S) → Bool)) :
    Pr[GoodOutput k | coordFork k D] = Pr[fun r => r.isSome | coordFork k D] := by
  refine le_antisymm (probEvent_mono fun r _ hr => ?_) (probEvent_mono fun r hr hs => ?_)
  · obtain ⟨ρ, X, rfl, -, -⟩ := hr
    rfl
  · exact goodOutput_of_mem_support hr hs

/-- **Lemma 7.1** of Fenzi–Moghaddas–Nguyen, success probability and output guarantee in a single
statement: with probability at least `ε - ℓ * (k - 1) / N` the extractor returns an `SS(S, ℓ, k)`
set of `ℓ * (k - 1) + 1` challenges, all accepting under the sampled table.

Because `GoodOutput` constrains the payload, the bound is sensitive to what the extractor actually
returns — an extractor emitting `some (ρ, ∅)` would fail it.

Not proved here: the paper's third clause, that the extractor makes an *expected* `ℓ(k-1)+1`
queries. This object consumes a pre-sampled acceptance table rather than querying an adversary,
so it establishes the information-theoretic content of the lemma and not its efficiency. See the
module docstring. -/
theorem sub_div_le_probEvent_goodOutput_coordFork [Nonempty S] (k : ℕ)
    (D : ProbComp ((ι → S) → Bool)) (hmass : Pr[⊥ | D] = 0) :
    acceptRatio D - (Fintype.card ι : ℝ≥0∞) * (k - 1 : ℕ) / Fintype.card S
      ≤ Pr[GoodOutput k | coordFork k D] := by
  rw [probEvent_goodOutput_coordFork, probEvent_isSome_coordFork]
  exact sub_div_le_tsum_probOutput_mul_goodSet D k hmass

end OracleComp
