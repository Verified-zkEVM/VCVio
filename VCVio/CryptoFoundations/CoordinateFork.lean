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
# A coordinate-wise fork over pre-sampled response tables

This module proves the information-theoretic, pre-sampled-table inequality underlying Lemma 7.1 of
Fenzi–Moghaddas–Nguyen. For a challenge space `ι → S` and a distribution of response tables with
accepting ratio `ε`, it returns a coordinate-wise `k`-special sound set of accepting transcripts
with probability at least `ε - ℓ * (k - 1) / N`, where `ℓ = Fintype.card ι` and
`N = Fintype.card S`.

Following `seededFork`, randomness comes first and the core is deterministic: `coordFork` samples
an *acceptance table* `ρ : (ι → S) → Bool` and a challenge `c₀`, then runs `coordForkCore`. The
core succeeds exactly when `c₀` accepts and every column of `c₀` holds at least `k` accepting
values (`coordForkCore_isSome_iff`), which is `OracleComp.EvalDist.goodSet` — so the success
probability is a cardinality ratio and the bound is the already-proved counting inequality
averaged over tables.

Prover responses enter as a second layer rather than a generalization of the core: a response
table `τ : (ι → S) → Y` and a verifier `V : (ι → S) → Y → Bool` induce the acceptance table
`fun c => V c (τ c)`, so `coordForkT` is `coordFork` composed with `acceptTable`
(`coordFork_acceptTable`) and its output guarantee `GoodTranscripts` is the paper's output clause:
at the data level it contains `ℓ(k-1)+1` accepting transcripts whose challenges are
`SS(S, ℓ, k)`.

Collecting replacements is a *total* lookup here: which `k - 1` accepting values a coordinate
contributes is irrelevant to the counting argument, so the core takes the first `k - 1` in
enumeration order. This is not the paper's oracle algorithm: the entire table is already available,
and neither query order, exhaustion, repeated execution, nor expected cost is represented. The
paper's expected-query clause therefore remains unproved.
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

/-- The `k - 1` replacements the table core keeps at coordinate `j`. Any choice would do; this one
takes the first `k - 1` in enumeration order. -/
noncomputable def replacementSet (k : ℕ) (ρ : (ι → S) → Bool) (c₀ : ι → S) (j : ι) : Finset S :=
  ((hitSet ρ c₀ j).toList.take (k - 1)).toFinset

/-- The deterministic table core: abort unless `c₀` accepts and every coordinate offers
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

/-- The single-round output read as a one-round tree in the challenge-only projection of
Definition 2.30. This says nothing about prover-message prefix consistency. -/
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

/-- The pre-sampled acceptance-table success and output inequality underlying **Lemma 7.1** of
Fenzi–Moghaddas–Nguyen: with probability at least `ε - ℓ * (k - 1) / N`, the computation returns an
`SS(S, ℓ, k)` set of `ℓ * (k - 1) + 1` challenges, all accepting under the sampled table.

Because `GoodOutput` constrains the payload, the bound is sensitive to what the computation
actually returns — one emitting `some (ρ, ∅)` would fail it.

Not proved here: existence of the paper's oracle extractor or its expected-query clause. This
object consumes a pre-sampled acceptance table rather than querying an adversary. -/
theorem sub_div_le_probEvent_goodOutput_coordFork [Nonempty S] (k : ℕ)
    (D : ProbComp ((ι → S) → Bool)) :
    acceptRatio D - (Fintype.card ι : ℝ≥0∞) * (k - 1 : ℕ) / Fintype.card S
      ≤ Pr[GoodOutput k | coordFork k D] := by
  rw [probEvent_goodOutput_coordFork, probEvent_isSome_coordFork]
  exact sub_div_le_tsum_probOutput_mul_goodSet D k (by simp)

omit [DecidableEq ι] [Fintype S] [SampleableType (ι → S)] in
theorem goodOutput_some_iff (k : ℕ) (ρ' : (ι → S) → Bool) (X : Finset (ι → S)) :
    GoodOutput k (some (ρ', X)) ↔ IsCoordSpecialSound k X ∧ ∀ c ∈ X, ρ' c := by
  refine ⟨fun ⟨ρ'', X', hEq, hss, hacc⟩ => ?_, fun ⟨hss, hacc⟩ => ⟨ρ', X, rfl, hss, hacc⟩⟩
  obtain ⟨rfl, rfl⟩ : ρ'' = ρ' ∧ X' = X := by simpa [eq_comm] using hEq
  exact ⟨hss, hacc⟩

/-! ## Transcripts

The paper's Lemma 7.1 outputs *pairs* `(cᵢ, yᵢ)` — challenge and prover response — where the
acceptance table above records only whether a challenge is accepted. Recording the response
instead, with a verification predicate, recovers that data shape in the table model.

Nothing above needs generalizing: a response table `τ : (ι → S) → Y` together with a verifier
`V : (ι → S) → Y → Bool` induces the acceptance table `fun c => V c (τ c)`, and at `Y := Bool`
with `V c y := y` that is the identity. -/

section Transcripts

variable {Y : Type} [DecidableEq Y]

/-- The acceptance table a response table induces under a verifier. -/
noncomputable def acceptTable (V : (ι → S) → Y → Bool) (D : ProbComp ((ι → S) → Y)) :
    ProbComp ((ι → S) → Bool) :=
  (fun τ c => V c (τ c)) <$> D

/-- The accepting transcripts carried by a challenge set, read off the response table. -/
def transcripts (τ : (ι → S) → Y) (X : Finset (ι → S)) : Finset ((ι → S) × Y) :=
  X.image fun c => (c, τ c)

omit [DecidableEq ι] [Fintype S] [SampleableType (ι → S)] in
theorem mem_transcripts {τ : (ι → S) → Y} {X : Finset (ι → S)} {c : ι → S} {y : Y} :
    (c, y) ∈ transcripts τ X ↔ c ∈ X ∧ y = τ c := by
  simp only [transcripts, Finset.mem_image, Prod.mk.injEq]
  exact ⟨fun ⟨c', hc', h1, h2⟩ => ⟨h1 ▸ hc', by rw [← h2, h1]⟩,
    fun ⟨hc, hy⟩ => ⟨c, hc, rfl, hy.symm⟩⟩

omit [DecidableEq ι] [Fintype S] [SampleableType (ι → S)] in
@[simp] theorem image_fst_transcripts (τ : (ι → S) → Y) (X : Finset (ι → S)) :
    (transcripts τ X).image Prod.fst = X := by
  ext c; simp [transcripts]

omit [DecidableEq ι] [Fintype S] [SampleableType (ι → S)] in
theorem card_transcripts (τ : (ι → S) → Y) (X : Finset (ι → S)) :
    (transcripts τ X).card = X.card :=
  Finset.card_image_of_injective X fun c c' h => by simpa using congrArg Prod.fst h

/-- What the table computation promises with responses in play: `ℓ(k-1)+1` transcripts, all
accepted by the verifier, whose challenges form an `SS(S, ℓ, k)` set. -/
def GoodTranscripts (V : (ι → S) → Y → Bool) (k : ℕ)
    (r : Option (((ι → S) → Y) × Finset (ι → S))) : Prop :=
  ∃ τ X, r = some (τ, X) ∧ IsCoordSpecialSound k X ∧ ∀ p ∈ transcripts τ X, V p.1 p.2

/-- Reading a response table as its induced acceptance table. -/
def toAcceptPair (V : (ι → S) → Y → Bool)
    (p : ((ι → S) → Y) × Finset (ι → S)) : ((ι → S) → Bool) × Finset (ι → S) :=
  (fun c => V c (p.1 c), p.2)

omit [DecidableEq ι] [Fintype S] [SampleableType (ι → S)] in
theorem goodTranscripts_some_iff (V : (ι → S) → Y → Bool) (k : ℕ) (τ : (ι → S) → Y)
    (X : Finset (ι → S)) :
    GoodTranscripts V k (some (τ, X)) ↔ IsCoordSpecialSound k X ∧ ∀ c ∈ X, V c (τ c) := by
  refine ⟨fun ⟨τ', X', hEq, hss, hacc⟩ => ?_, fun ⟨hss, hacc⟩ =>
    ⟨τ, X, rfl, hss, fun p hp => by
      obtain ⟨c, y⟩ := p
      obtain ⟨h1, rfl⟩ := mem_transcripts.mp hp
      exact hacc c h1⟩⟩
  obtain ⟨h1, h2⟩ := Prod.ext_iff.mp (Option.some.inj hEq)
  subst h1; subst h2
  exact ⟨hss, fun c hc => hacc (c, τ c) (mem_transcripts.mpr ⟨hc, rfl⟩)⟩

omit [DecidableEq ι] [Fintype S] [SampleableType (ι → S)] in
theorem goodTranscripts_iff_goodOutput (V : (ι → S) → Y → Bool) (k : ℕ)
    (r : Option (((ι → S) → Y) × Finset (ι → S))) :
    GoodTranscripts V k r ↔ GoodOutput k (r.map (toAcceptPair V)) := by
  cases r with
  | none => simp [GoodTranscripts, GoodOutput]
  | some p =>
      obtain ⟨τ, X⟩ := p
      rw [goodTranscripts_some_iff]
      exact (goodOutput_some_iff k _ X).symm

/-- The table computation with responses: sample a response table and a challenge, run the core
against the induced acceptance table, and return the table with the challenge set it found. -/
noncomputable def coordForkT (V : (ι → S) → Y → Bool) (k : ℕ) (D : ProbComp ((ι → S) → Y)) :
    ProbComp (Option (((ι → S) → Y) × Finset (ι → S))) := do
  let τ ← D
  let c₀ ← $ᵗ (ι → S)
  return (coordForkCore k (fun c => V c (τ c)) c₀).map fun X => (τ, X)

omit [DecidableEq Y] in
/-- The response-carrying extractor is a faithful relabelling of the acceptance-table one. -/
theorem coordFork_acceptTable (V : (ι → S) → Y → Bool) (k : ℕ)
    (D : ProbComp ((ι → S) → Y)) :
    coordFork k (acceptTable V D) =
      (fun r => r.map (toAcceptPair V)) <$> coordForkT V k D := by
  simp only [coordFork, coordForkT, acceptTable, map_eq_bind_pure_comp, bind_assoc, pure_bind,
    Function.comp_apply]
  refine bind_congr fun τ => bind_congr fun c₀ => ?_
  cases coordForkCore k (fun c => V c (τ c)) c₀ <;> rfl

theorem probEvent_goodTranscripts_coordForkT (V : (ι → S) → Y → Bool) (k : ℕ)
    (D : ProbComp ((ι → S) → Y)) :
    Pr[GoodTranscripts V k | coordForkT V k D] =
      Pr[GoodOutput k | coordFork k (acceptTable V D)] := by
  rw [coordFork_acceptTable, probEvent_map]
  exact congrArg _ (funext fun r => propext (goodTranscripts_iff_goodOutput V k r))

/-- The response-table form of the inequality underlying **Lemma 7.1**. With probability at least
`ε - ℓ(k-1)/N`, it returns `ℓ(k-1)+1` accepting transcripts whose challenges form an
`SS(S, ℓ, k)` set. -/
theorem sub_div_le_probEvent_goodTranscripts_coordForkT [Nonempty S] (V : (ι → S) → Y → Bool)
    (k : ℕ) (D : ProbComp ((ι → S) → Y)) :
    acceptRatio (acceptTable V D) - (Fintype.card ι : ℝ≥0∞) * (k - 1 : ℕ) / Fintype.card S
      ≤ Pr[GoodTranscripts V k | coordForkT V k D] := by
  rw [probEvent_goodTranscripts_coordForkT]
  exact sub_div_le_probEvent_goodOutput_coordFork k _

end Transcripts

end OracleComp
