/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import ToMathlib.Combinatorics.CoordinateWise

/-!
# Trees of challenges for multi-round protocols

A `μ`-round transcript is a list of `μ` challenge vectors. A *tree of challenges* is a finite set
of such transcripts in which, under every prefix the set realizes, the available next challenges
form a coordinate-wise `k`-special sound set of exactly `ℓ * (k - 1) + 1` elements.

`IsChallengeTree` states this by recursion on the number of rounds, which is the shape the
multi-round extractor's induction consumes: peeling one round exposes the root challenge set
together with a level-`(μ - 1)` tree under each of its members. `card_of_isChallengeTree` records
that a tree holds exactly `(ℓ * (k - 1) + 1) ^ μ` transcripts.

This is only the recursively branching **challenge projection** of Definition 2.30 of
Fenzi–Moghaddas–Nguyen. Prover messages, their prefix consistency, acceptance, and the connection
to an executed protocol are not represented by this type.
-/

@[expose] public section

open Finset

namespace CoordinateWise

variable {ι S : Type*} [Fintype ι] [DecidableEq S] {k : ℕ}

/-- `IsChallengeTree k μ T`: the transcripts in `T` have `μ` rounds, and under every prefix they
realize, the set of available next challenges is coordinate-wise `k`-special sound with exactly
`Fintype.card ι * (k - 1) + 1` members. -/
def IsChallengeTree (k : ℕ) : ℕ → Finset (List (ι → S)) → Prop
  | 0, T => T = {[]}
  | μ + 1, T => ∃ children : Finset (ι → S), ∃ sub : (ι → S) → Finset (List (ι → S)),
      IsCoordSpecialSound k children ∧
      (∀ c ∈ children, IsChallengeTree k μ (sub c)) ∧
      T = children.biUnion fun c => (sub c).image fun t => c :: t

@[simp] theorem isChallengeTree_zero {T : Finset (List (ι → S))} :
    IsChallengeTree k 0 T ↔ T = {[]} := Iff.rfl

theorem isChallengeTree_succ {μ : ℕ} {T : Finset (List (ι → S))} :
    IsChallengeTree k (μ + 1) T ↔
      ∃ children : Finset (ι → S), ∃ sub : (ι → S) → Finset (List (ι → S)),
        IsCoordSpecialSound k children ∧
        (∀ c ∈ children, IsChallengeTree k μ (sub c)) ∧
        T = children.biUnion fun c => (sub c).image fun t => c :: t := Iff.rfl

/-- Grafting a level-`μ` tree under each member of a coordinate-wise `k`-special sound challenge
set produces a level-`(μ + 1)` tree. This is the step the multi-round extractor performs after a
single round of coordinate-wise rewinding. -/
theorem isChallengeTree_biUnion {μ : ℕ} {children : Finset (ι → S)}
    {sub : (ι → S) → Finset (List (ι → S))} (hss : IsCoordSpecialSound k children)
    (hsub : ∀ c ∈ children, IsChallengeTree k μ (sub c)) :
    IsChallengeTree k (μ + 1) (children.biUnion fun c => (sub c).image fun t => c :: t) :=
  ⟨children, sub, hss, hsub, rfl⟩

/-- A coordinate-wise `k`-special sound challenge set is exactly a one-round tree in this
challenge-only projection. -/
theorem isChallengeTree_one {children : Finset (ι → S)} (hss : IsCoordSpecialSound k children) :
    IsChallengeTree k 1 (children.image fun c => [c]) := by
  have h := isChallengeTree_biUnion (μ := 0) (sub := fun _ => ({[]} : Finset (List (ι → S))))
    hss fun _ _ => rfl
  refine (?_ : (children.image fun c => [c]) = _) ▸ h
  ext t
  simp [Finset.mem_biUnion, Finset.mem_image, eq_comm]

/-- Transcripts in a level-`μ` tree have exactly `μ` rounds. -/
theorem length_of_mem_isChallengeTree : ∀ {μ : ℕ} {T : Finset (List (ι → S))},
    IsChallengeTree k μ T → ∀ t ∈ T, t.length = μ
  | 0, T, h, t, ht => by subst h; simpa using congrArg List.length (Finset.mem_singleton.mp ht)
  | _ + 1, T, h, t, ht => by
      obtain ⟨children, sub, -, hsub, rfl⟩ := h
      obtain ⟨c, hc, hct⟩ := Finset.mem_biUnion.mp ht
      obtain ⟨t', ht', rfl⟩ := Finset.mem_image.mp hct
      simpa using length_of_mem_isChallengeTree (hsub c hc) t' ht'

/-- Distinct root challenges graft disjoint transcript blocks, since the transcripts differ in
their first entry. -/
theorem pairwiseDisjoint_cons_image {children : Finset (ι → S)}
    (sub : (ι → S) → Finset (List (ι → S))) :
    ∀ c ∈ children, ∀ c' ∈ children, c ≠ c' →
      Disjoint ((sub c).image fun t => c :: t) ((sub c').image fun t => c' :: t) := by
  intro c _ c' _ hcc'
  refine Finset.disjoint_left.mpr ?_
  simp only [Finset.mem_image]
  rintro x ⟨t, -, rfl⟩ ⟨t', -, hx⟩
  have hheads : c' = c := by simpa using congrArg List.head? hx
  exact hcc' hheads.symm

/-- A level-`μ` tree holds exactly `(ℓ * (k - 1) + 1) ^ μ` transcripts. -/
theorem card_of_isChallengeTree : ∀ {μ : ℕ} {T : Finset (List (ι → S))},
    IsChallengeTree k μ T → T.card = (Fintype.card ι * (k - 1) + 1) ^ μ
  | 0, T, h => by subst h; simp
  | μ + 1, T, h => by
      obtain ⟨children, sub, hss, hsub, rfl⟩ := h
      rw [Finset.card_biUnion (pairwiseDisjoint_cons_image sub)]
      have hinner : ∀ c ∈ children, ((sub c).image fun t => c :: t).card =
          (Fintype.card ι * (k - 1) + 1) ^ μ := fun c hc => by
        rw [Finset.card_image_of_injective _ (List.cons_injective (a := c)),
          card_of_isChallengeTree (hsub c hc)]
      rw [Finset.sum_const_nat hinner, hss.2, pow_succ, mul_comm]

end CoordinateWise
