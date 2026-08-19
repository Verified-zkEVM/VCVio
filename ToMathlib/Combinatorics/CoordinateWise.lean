/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.ENNReal.Inv
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Tactic.Ring

/-!
# Coordinate-wise special soundness

A challenge is a vector `x : ι → S`, and two challenges are *coordinate-`j` neighbours* when they
differ in coordinate `j` and agree everywhere else (`Function.DiffersOnlyAt`). A finite set of
challenges is *coordinate-wise `k`-special sound* (`IsCoordSpecialSound`) when it contains a
central vector having `k - 1` neighbours in **every** coordinate, and has exactly the
`ℓ * (k - 1) + 1` members the paper's `SS(S, ℓ, k)` prescribes.

`coordFamily` builds such a set from a centre and a family of per-coordinate replacement values,
which is the output shape targeted by coordinate-wise rewinding. `card_coordFamily` records its
exact size `Fintype.card ι * (k - 1) + 1`, and `isCoordSpecialSound_iff_of_unique` records
that a single coordinate recovers ordinary `k`-special soundness.

## Main definitions

* `Function.DiffersOnlyAt j x y` — `x` and `y` differ in coordinate `j` and only there.
* `CoordinateWise.HasCoordNeighbours k X` — `X` has a centre with `k - 1` neighbours in every
  coordinate.
* `CoordinateWise.IsCoordSpecialSound k X` — that, plus the cardinality: `X ∈ SS(S, ℓ, k)`.
* `CoordinateWise.coordFamily e A` — the challenge set with centre `e` whose coordinate-`j`
  neighbours replace `e j` by each value of `A j`.
* `CoordinateWise.columnCount accept j c` — how many values of coordinate `j` keep `c` accepting.

## Main results

Together these are the combinatorial ingredients used in Lemma 7.1 of
Fenzi–Moghaddas–Nguyen. In the pre-sampled-table model, success means that `c` accepts and every
column of `c` holds at least `k` accepting values. The operational resampling loop and its running
time are outside this file.

* `CoordinateWise.sub_div_le_div_card_filter` — the table success condition holds for at least an
  `ε - ℓ * (k - 1) / N` fraction of challenges, where `ε` is the accepting fraction. This is the
  counting inequality used in Lemma 7.1; it does not construct or cost an oracle extractor.
* `CoordinateWise.isCoordSpecialSound_coordFamily` and `CoordinateWise.card_coordFamily` — what
  the table core's candidate output must satisfy to be an `SS(S, ℓ, k)` set.
* `CoordinateWise.le_card_of_hasCoordNeighbours` — the paper's cardinality is already forced as a
  lower bound by the neighbour condition alone.

Only the identification of these cardinality ratios with probabilities under uniform sampling is
left to the probability layer.
-/

@[expose] public section

open Finset

open scoped ENNReal

namespace Function

variable {ι S : Type*}

/-- `x` and `y` differ in coordinate `j`, and agree in every other coordinate. -/
def DiffersOnlyAt (j : ι) (x y : ι → S) : Prop :=
  x j ≠ y j ∧ ∀ j', j' ≠ j → x j' = y j'

namespace DiffersOnlyAt

variable {j j' : ι} {x y : ι → S}

theorem symm (h : DiffersOnlyAt j x y) : DiffersOnlyAt j y x :=
  ⟨h.1.symm, fun j' hj' => (h.2 j' hj').symm⟩

theorem irrefl (x : ι → S) (j : ι) : ¬ DiffersOnlyAt j x x := fun h => h.1 rfl

theorem ne (h : DiffersOnlyAt j x y) : x ≠ y := fun hxy => h.1 (congrFun hxy j)

/-- Differing in only one coordinate pins that coordinate down. -/
theorem coord_eq (h : DiffersOnlyAt j x y) (h' : DiffersOnlyAt j' x y) : j = j' := by
  by_contra hne
  exact h.1 (h'.2 j hne)

end DiffersOnlyAt

variable [DecidableEq ι]

theorem differsOnlyAt_update {j : ι} {x : ι → S} {u : S} (hu : x j ≠ u) :
    DiffersOnlyAt j x (Function.update x j u) :=
  ⟨by simpa using hu, fun j' hj' => (Function.update_of_ne hj' _ _).symm⟩

theorem differsOnlyAt_iff_exists_update {j : ι} {x y : ι → S} :
    DiffersOnlyAt j x y ↔ ∃ u, x j ≠ u ∧ y = Function.update x j u := by
  refine ⟨fun h => ⟨y j, h.1, funext fun j' => ?_⟩,
    fun ⟨_, hu, hy⟩ => hy ▸ differsOnlyAt_update hu⟩
  by_cases hj : j' = j
  · subst hj; simp
  · rw [Function.update_of_ne hj, h.2 j' hj]

end Function

namespace CoordinateWise

open Function

variable {ι S : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq S]
variable {k : ℕ} {X : Finset (ι → S)} {e : ι → S} {A : ι → Finset S}

/-- The neighbour condition: some *central* vector of `X` has, in every coordinate, `k - 1`
further members of `X` differing from it in that coordinate and only there. -/
def HasCoordNeighbours (k : ℕ) (X : Finset (ι → S)) : Prop :=
  ∃ e ∈ X, ∀ j : ι, ∃ J ⊆ X.erase e, J.card = k - 1 ∧ ∀ y ∈ J, DiffersOnlyAt j e y

/-- A finite set of challenge vectors is coordinate-wise `k`-special sound when it has the
neighbour structure *and* exactly `ℓ * (k - 1) + 1` members.

This is `SS(S, ℓ, k)` of Fenzi–Moghaddas–Nguyen, with `ι` playing the role of `[ℓ]`; the paper's
sets are indexed by `[K]` with `K = ℓ(k - 1) + 1`, so the cardinality is part of the notion. By
`le_card_of_hasCoordNeighbours` the neighbour condition already forces `K ≤ X.card`, so the
conjunct below only rules out sets carrying extra challenges beyond the `K` the extractor
produces. -/
def IsCoordSpecialSound (k : ℕ) (X : Finset (ι → S)) : Prop :=
  HasCoordNeighbours k X ∧ X.card = Fintype.card ι * (k - 1) + 1

omit [DecidableEq ι] in
/-- The neighbour condition alone forces the paper's cardinality as a lower bound: a vector
differing from the centre in only one coordinate determines that coordinate
(`Function.DiffersOnlyAt.coord_eq`), so the `ℓ` neighbour blocks are pairwise disjoint. -/
theorem le_card_of_hasCoordNeighbours (h : HasCoordNeighbours k X) :
    Fintype.card ι * (k - 1) + 1 ≤ X.card := by
  classical
  obtain ⟨e, heX, hJ⟩ := h
  choose J hJsub hJcard hJdiff using hJ
  have hdisj : ∀ j ∈ (Finset.univ : Finset ι), ∀ j' ∈ (Finset.univ : Finset ι), j ≠ j' →
      Disjoint (J j) (J j') := fun j _ j' _ hjj' =>
    Finset.disjoint_left.mpr fun y hy hy' => hjj' ((hJdiff j y hy).coord_eq (hJdiff j' y hy'))
  have hblocks : (Finset.univ.biUnion J).card = Fintype.card ι * (k - 1) := by
    rw [Finset.card_biUnion hdisj, Finset.sum_congr rfl fun j _ => hJcard j, Finset.sum_const,
      Finset.card_univ]
    simp
  have hle := Finset.card_le_card
    (Finset.biUnion_subset.mpr fun j _ => hJsub j : Finset.univ.biUnion J ⊆ X.erase e)
  have hpos : 1 ≤ X.card := Finset.card_pos.mpr ⟨e, heX⟩
  rw [hblocks, Finset.card_erase_of_mem heX] at hle
  omega

/-- The challenge set centred at `e` whose coordinate-`j` neighbours replace `e j` by each value
of `A j`. This is the output shape targeted by coordinate-wise rewinding. -/
def coordFamily (e : ι → S) (A : ι → Finset S) : Finset (ι → S) :=
  insert e (Finset.univ.biUnion fun j => (A j).image fun u => Function.update e j u)

theorem mem_coordFamily {x : ι → S} :
    x ∈ coordFamily e A ↔ x = e ∨ ∃ j, ∃ u ∈ A j, x = Function.update e j u := by
  simp [coordFamily, eq_comm]

omit [Fintype ι] [DecidableEq S] in
/-- Every non-central member of `coordFamily e A` is a coordinate neighbour of the centre. -/
theorem differsOnlyAt_of_mem (hA : ∀ j, e j ∉ A j) {j : ι} {u : S} (hu : u ∈ A j) :
    DiffersOnlyAt j e (Function.update e j u) :=
  differsOnlyAt_update fun h => hA j (h ▸ hu)

theorem centre_notMem_biUnion (hA : ∀ j, e j ∉ A j) :
    e ∉ Finset.univ.biUnion fun j => (A j).image fun u => Function.update e j u := by
  simp only [Finset.mem_biUnion, Finset.mem_image, Finset.mem_univ, true_and]
  rintro ⟨j, u, hu, hupd⟩
  exact (differsOnlyAt_of_mem hA hu).ne hupd.symm

/-- Distinct coordinates contribute disjoint neighbour blocks: a vector in the `j` block has its
`j`-th coordinate changed, while a vector in the `j'` block leaves it alone. -/
theorem pairwiseDisjoint_neighbours (hA : ∀ j, e j ∉ A j) :
    ∀ j ∈ (Finset.univ : Finset ι), ∀ j' ∈ (Finset.univ : Finset ι), j ≠ j' →
      Disjoint ((A j).image fun u => Function.update e j u)
        ((A j').image fun u => Function.update e j' u) := by
  intro j _ j' _ hjj'
  refine Finset.disjoint_left.mpr ?_
  simp only [Finset.mem_image]
  rintro x ⟨u, hu, rfl⟩ ⟨u', hu', hx⟩
  have key : e j = u := by
    have h := congrFun hx j
    rwa [Function.update_of_ne hjj' _ _, Function.update_self] at h
  exact hA j (by rw [key]; exact hu)

/-- A coordinate family has exactly `ℓ * (k - 1) + 1` challenges. -/
theorem card_coordFamily (hA : ∀ j, e j ∉ A j) (hcard : ∀ j, (A j).card = k - 1) :
    (coordFamily e A).card = Fintype.card ι * (k - 1) + 1 := by
  rw [coordFamily, Finset.card_insert_of_notMem (centre_notMem_biUnion hA),
    Finset.card_biUnion (pairwiseDisjoint_neighbours hA)]
  have himg : ∀ j : ι, ((A j).image fun u => Function.update e j u).card = k - 1 := fun j => by
    rw [Finset.card_image_of_injective _ (Function.update_injective e j), hcard j]
  rw [Finset.sum_congr rfl fun j _ => himg j, Finset.sum_const, Finset.card_univ]
  simp

theorem hasCoordNeighbours_coordFamily
    (hA : ∀ j, e j ∉ A j) (hcard : ∀ j, (A j).card = k - 1) :
    HasCoordNeighbours k (coordFamily e A) := by
  refine ⟨e, Finset.mem_insert_self _ _, fun j => ?_⟩
  refine ⟨(A j).image fun u => Function.update e j u, ?_, ?_, ?_⟩
  · intro x hx
    simp only [Finset.mem_image] at hx
    obtain ⟨u, hu, rfl⟩ := hx
    exact Finset.mem_erase.mpr ⟨(differsOnlyAt_of_mem hA hu).ne.symm,
      mem_coordFamily.mpr (Or.inr ⟨j, u, hu, rfl⟩)⟩
  · rw [Finset.card_image_of_injective _ (Function.update_injective e j), hcard j]
  · intro y hy
    simp only [Finset.mem_image] at hy
    obtain ⟨u, hu, rfl⟩ := hy
    exact differsOnlyAt_of_mem hA hu

theorem isCoordSpecialSound_coordFamily
    (hA : ∀ j, e j ∉ A j) (hcard : ∀ j, (A j).card = k - 1) :
    IsCoordSpecialSound k (coordFamily e A) :=
  ⟨hasCoordNeighbours_coordFamily hA hcard, card_coordFamily hA hcard⟩

omit [DecidableEq ι] in
/-- With a single coordinate, coordinate-wise `k`-special soundness is ordinary `k`-special
soundness: exactly `k` distinct challenges. -/
theorem isCoordSpecialSound_iff_of_unique [Unique ι] (hk : 1 ≤ k) :
    IsCoordSpecialSound k X ↔ X.card = k := by
  have hcard : Fintype.card ι * (k - 1) + 1 = k := by rw [Fintype.card_unique]; omega
  constructor
  · rintro ⟨-, hc⟩
    rw [hc, hcard]
  · intro hX
    obtain ⟨e, heX⟩ : X.Nonempty := Finset.card_pos.mp (by omega)
    refine ⟨⟨e, heX, fun j => ?_⟩, by rw [hcard, hX]⟩
    refine ⟨X.erase e, Finset.Subset.refl _, ?_, fun y hy => ?_⟩
    · rw [Finset.card_erase_of_mem heX, hX]
    · have hyne : y ≠ e := (Finset.mem_erase.mp hy).1
      exact ⟨fun h => hyne (funext fun j' => by rw [Subsingleton.elim j' j, ← h]),
        fun j' hj' => absurd (Subsingleton.elim j' j) hj'⟩

/-! ## Column counts

Fixing every coordinate of a challenge except `j` leaves a *column* of `Fintype.card S`
challenges. The number of accepting challenges in that column is what limits how often
coordinate `j` can be resampled, and `card_mul_card_filter_columnCount_lt` is the whole content
of the union-bound step in Lemma 7.1 of Fenzi–Moghaddas–Nguyen — stated as a counting inequality,
with no probability anywhere. -/

section ColumnCount

variable [Fintype S] (accept : (ι → S) → Prop) [DecidablePred accept]

/-- The number of values of coordinate `j` that keep `c` accepting. -/
def columnCount (j : ι) (c : ι → S) : ℕ :=
  (Finset.univ.filter fun x : S => accept (Function.update c j x)).card

variable {accept}

omit [Fintype ι] [DecidableEq S] in
/-- A column count depends only on the coordinates other than `j`. -/
@[simp] theorem columnCount_update (j : ι) (c : ι → S) (y : S) :
    columnCount accept j (Function.update c j y) = columnCount accept j c := by
  simp [columnCount, Function.update_idem]

omit [Fintype ι] [DecidableEq S] [Fintype S] [DecidablePred accept] in
/-- A challenge is recovered from its column representative by refilling coordinate `j`. -/
theorem update_coord_self {j : ι} {c r : ι → S} {d : S} (h : Function.update c j d = r) :
    Function.update r j (c j) = c := by
  subst h; simp

omit [DecidablePred accept] in
/-- The challenges sharing a column representative are exactly the refillings of coordinate
`j`. -/
theorem filter_update_eq_image {j : ι} {d : S} {r : ι → S} (hrj : r j = d) :
    (Finset.univ.filter fun c : ι → S => Function.update c j d = r)
      = Finset.univ.image fun x : S => Function.update r j x := by
  ext c
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
  refine ⟨fun hc => ⟨c j, update_coord_self hc⟩, ?_⟩
  rintro ⟨x, hx⟩
  rw [← hx, Function.update_idem, ← hrj, Function.update_eq_self]

omit [DecidableEq S] in
/-- Scaled by `Fintype.card S`, the accepting challenges whose column at `j` holds fewer than `k`
accepting values take up at most a `(k - 1) / Fintype.card S` fraction of all challenges.

Fixing the coordinates other than `j` leaves `Fintype.card S` challenges, of which exactly
`columnCount accept j c` are accepting; when that count is below `k` it contributes at most
`k - 1`. -/
theorem card_mul_card_filter_columnCount_lt [Nonempty S] (j : ι) (k : ℕ) :
    Fintype.card S *
        (Finset.univ.filter fun c : ι → S => accept c ∧ columnCount accept j c < k).card
      ≤ (k - 1) * Fintype.card (ι → S) := by
  classical
  obtain ⟨d⟩ := (inferInstance : Nonempty S)
  have hmaps : Set.MapsTo (fun c : ι → S => Function.update c j d)
      ↑(Finset.univ : Finset (ι → S))
      ↑((Finset.univ : Finset (ι → S)).image fun c => Function.update c j d) := fun c _ =>
    Finset.mem_coe.mpr (Finset.mem_image_of_mem _ (Finset.mem_univ c))
  -- Column representatives have their `j`-th coordinate pinned to `d`.
  have hrj : ∀ r ∈ (Finset.univ : Finset (ι → S)).image fun c => Function.update c j d,
      r j = d := by
    rintro r hr
    obtain ⟨c₀, -, rfl⟩ := Finset.mem_image.mp hr
    simp
  have hcard_fiber : ∀ r ∈ (Finset.univ : Finset (ι → S)).image fun c => Function.update c j d,
      (Finset.univ.filter fun c : ι → S => Function.update c j d = r).card = Fintype.card S :=
    fun r hr => by
      rw [filter_update_eq_image (hrj r hr),
        Finset.card_image_of_injective _ (Function.update_injective r j), Finset.card_univ]
  -- Every challenge lies in exactly one column, so the columns partition the whole space.
  have htotal : Fintype.card (ι → S) =
      ((Finset.univ : Finset (ι → S)).image fun c => Function.update c j d).card *
        Fintype.card S := by
    have hsum := Finset.card_eq_sum_card_fiberwise hmaps
    rw [Finset.card_univ] at hsum
    rw [hsum, Finset.sum_const_nat hcard_fiber]
  -- A column contributes only when it is thin, and then it contributes its own count.
  have hbad : ∀ r ∈ (Finset.univ : Finset (ι → S)).image fun c => Function.update c j d,
      ((Finset.univ.filter fun c : ι → S => accept c ∧ columnCount accept j c < k).filter
        fun c => Function.update c j d = r).card ≤ k - 1 := by
    intro r _
    rcases Finset.eq_empty_or_nonempty
        ((Finset.univ.filter fun c : ι → S => accept c ∧ columnCount accept j c < k).filter
          fun c => Function.update c j d = r) with hempty | ⟨w, hw⟩
    · simp [hempty]
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
      obtain ⟨⟨-, hcol⟩, hwrep⟩ := hw
      -- The column count is constant on a column, so the representative is thin too.
      have hcolr : columnCount accept j r < k := by rw [← hwrep]; simpa using hcol
      have hsub : ((Finset.univ.filter fun c : ι → S =>
          accept c ∧ columnCount accept j c < k).filter fun c => Function.update c j d = r) ⊆
          (Finset.univ.filter fun x : S => accept (Function.update r j x)).image
            fun x => Function.update r j x := by
        intro c hc
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc
        obtain ⟨⟨hacc, -⟩, hcrep⟩ := hc
        refine Finset.mem_image.mpr ⟨c j, ?_, update_coord_self hcrep⟩
        simpa only [Finset.mem_filter, Finset.mem_univ, true_and, update_coord_self hcrep]
      calc ((Finset.univ.filter fun c : ι → S =>
              accept c ∧ columnCount accept j c < k).filter
                fun c => Function.update c j d = r).card
          ≤ ((Finset.univ.filter fun x : S => accept (Function.update r j x)).image
              fun x => Function.update r j x).card := Finset.card_le_card hsub
        _ = columnCount accept j r :=
            Finset.card_image_of_injective _ (Function.update_injective r j)
        _ ≤ k - 1 := by omega
  -- Assemble: at most `k - 1` per column, and there are `|ι → S| / |S|` columns.
  calc Fintype.card S *
        (Finset.univ.filter fun c : ι → S => accept c ∧ columnCount accept j c < k).card
      = Fintype.card S * ∑ r ∈ (Finset.univ : Finset (ι → S)).image
            (fun c => Function.update c j d),
          ((Finset.univ.filter fun c : ι → S => accept c ∧ columnCount accept j c < k).filter
            fun c => Function.update c j d = r).card := by
        rw [← Finset.card_eq_sum_card_fiberwise (fun c _ => hmaps (Finset.mem_univ c))]
    _ ≤ Fintype.card S * ∑ _r ∈ (Finset.univ : Finset (ι → S)).image
            (fun c => Function.update c j d), (k - 1) :=
        Nat.mul_le_mul_left _ (Finset.sum_le_sum hbad)
    _ = (k - 1) * (((Finset.univ : Finset (ι → S)).image
            fun c => Function.update c j d).card * Fintype.card S) := by
        rw [Finset.sum_const_nat (m := k - 1) fun _ _ => rfl]; ring
    _ = (k - 1) * Fintype.card (ι → S) := by rw [htotal]

omit [DecidableEq S] in
/-- **Weighted column counting.** Give every accepting challenge a weight of `w` divided by its own
column count at `j`. Each column then contributes at most `w` in total, whatever its count, because
a column with `l` accepting values gives each of them weight `w / l`. Summed over the
`|ι → S| / |S|` columns this is at most `w * |ι → S| / |S|`, which is the statement below with the
division cleared.

This is the counting content of the `𝔼[Tᵢ] ≤ k - 1` step in Lemma 7.1 of
Fenzi–Moghaddas–Nguyen: there `w = (k - 1) * |S|`, and the weight attached to an accepting
challenge is the expected number of draws its coordinate resampling makes. -/
theorem card_mul_sum_div_columnCount_le [Nonempty S] (j : ι) (w : ℝ≥0∞) :
    (Fintype.card S : ℝ≥0∞) *
        ∑ c : ι → S, (if accept c then w / columnCount accept j c else 0)
      ≤ w * Fintype.card (ι → S) := by
  classical
  obtain ⟨d⟩ := (inferInstance : Nonempty S)
  set reps : Finset (ι → S) :=
    (Finset.univ : Finset (ι → S)).image fun c => Function.update c j d with hreps
  have hmaps : ∀ c ∈ (Finset.univ : Finset (ι → S)), Function.update c j d ∈ reps := fun c _ =>
    Finset.mem_image_of_mem _ (Finset.mem_univ c)
  have hrj : ∀ r ∈ reps, r j = d := by
    rintro r hr
    obtain ⟨c₀, -, rfl⟩ := Finset.mem_image.mp hr
    simp
  have hcard_fiber : ∀ r ∈ reps,
      ((Finset.univ : Finset (ι → S)).filter fun c => Function.update c j d = r).card
        = Fintype.card S := by
    intro r hr
    rw [filter_update_eq_image (hrj r hr),
      Finset.card_image_of_injective _ (Function.update_injective r j), Finset.card_univ]
  have htotal : reps.card * Fintype.card S = Fintype.card (ι → S) := by
    have hsum := Finset.card_eq_sum_card_fiberwise hmaps
    rw [Finset.card_univ] at hsum
    rw [hsum, Finset.sum_const_nat hcard_fiber]
  -- A single column contributes at most `w`, whether or not it holds an accepting challenge.
  have hcol : ∀ r ∈ reps,
      (∑ c ∈ (Finset.univ : Finset (ι → S)).filter fun c => Function.update c j d = r,
        (if accept c then w / columnCount accept j c else 0)) ≤ w := by
    intro r hr
    rw [filter_update_eq_image (hrj r hr),
      Finset.sum_image fun x _ y _ h => Function.update_injective r j h]
    have hconst : ∀ x : S,
        (if accept (Function.update r j x) then w / columnCount accept j (Function.update r j x)
          else 0) = if accept (Function.update r j x) then w / columnCount accept j r else 0 := by
      intro x
      rw [columnCount_update]
    rw [Finset.sum_congr rfl fun x _ => hconst x, ← Finset.sum_filter, Finset.sum_const,
      nsmul_eq_mul, ← columnCount]
    rcases Nat.eq_zero_or_pos (columnCount accept j r) with hzero | hpos
    · simp [hzero]
    · refine le_of_eq (ENNReal.mul_div_cancel ?_ (by finiteness))
      exact_mod_cast hpos.ne'
  calc (Fintype.card S : ℝ≥0∞) *
        ∑ c : ι → S, (if accept c then w / columnCount accept j c else 0)
      = (Fintype.card S : ℝ≥0∞) * ∑ r ∈ reps,
          ∑ c ∈ (Finset.univ : Finset (ι → S)).filter fun c => Function.update c j d = r,
            (if accept c then w / columnCount accept j c else 0) := by
        rw [Finset.sum_fiberwise_of_maps_to hmaps]
    _ ≤ (Fintype.card S : ℝ≥0∞) * ∑ _r ∈ reps, w :=
        mul_le_mul' le_rfl (Finset.sum_le_sum hcol)
    _ = w * ((reps.card : ℝ≥0∞) * Fintype.card S) := by
        rw [Finset.sum_const, nsmul_eq_mul]; ring
    _ = w * Fintype.card (ι → S) := by rw [← Nat.cast_mul, htotal]

variable {c : ι → S}

omit [Fintype ι] [DecidableEq S] in
/-- An accepting challenge is one of the accepting values of each of its own columns. -/
theorem mem_filter_coord_self (hacc : accept c) (j : ι) :
    c j ∈ Finset.univ.filter fun x : S => accept (Function.update c j x) := by
  simpa [Function.update_eq_self] using hacc


omit [DecidableEq S] in
/-- The union-bound counting inequality used in Lemma 7.1: scaled by `Fintype.card S`, the
accepting challenges that fail somewhere exceed those that succeed everywhere by at most
`ℓ * (k - 1) * |ι → S|`.

Dividing through by `Fintype.card S * Fintype.card (ι → S)` turns this into the paper's
`ε - ℓ * (k - 1) / N`. -/
theorem card_mul_card_filter_accept_le [Nonempty S] (k : ℕ) :
    Fintype.card S * (Finset.univ.filter fun c : ι → S => accept c).card
      ≤ Fintype.card S * (Finset.univ.filter fun c : ι → S =>
            accept c ∧ ∀ j, k ≤ columnCount accept j c).card
          + Fintype.card ι * ((k - 1) * Fintype.card (ι → S)) := by
  classical
  -- Every accepting challenge either succeeds in every coordinate or fails in some coordinate.
  have hcover : (Finset.univ.filter fun c : ι → S => accept c) ⊆
      (Finset.univ.filter fun c : ι → S => accept c ∧ ∀ j, k ≤ columnCount accept j c) ∪
        Finset.univ.biUnion fun j =>
          Finset.univ.filter fun c : ι → S => accept c ∧ columnCount accept j c < k := by
    intro c hc
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc
    by_cases hall : ∀ j, k ≤ columnCount accept j c
    · exact Finset.mem_union_left _ (by simp [hc, hall])
    · push Not at hall
      obtain ⟨j, hj⟩ := hall
      exact Finset.mem_union_right _
        (Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, by simp [hc, hj]⟩)
  have hcard : (Finset.univ.filter fun c : ι → S => accept c).card ≤
      (Finset.univ.filter fun c : ι → S =>
          accept c ∧ ∀ j, k ≤ columnCount accept j c).card
        + ∑ j : ι, (Finset.univ.filter fun c : ι → S =>
            accept c ∧ columnCount accept j c < k).card :=
    le_trans (Finset.card_le_card hcover)
      (le_trans (Finset.card_union_le _ _)
        (Nat.add_le_add_left Finset.card_biUnion_le _))
  calc Fintype.card S * (Finset.univ.filter fun c : ι → S => accept c).card
      ≤ Fintype.card S * ((Finset.univ.filter fun c : ι → S =>
            accept c ∧ ∀ j, k ≤ columnCount accept j c).card
          + ∑ j : ι, (Finset.univ.filter fun c : ι → S =>
              accept c ∧ columnCount accept j c < k).card) := Nat.mul_le_mul_left _ hcard
    _ = Fintype.card S * (Finset.univ.filter fun c : ι → S =>
            accept c ∧ ∀ j, k ≤ columnCount accept j c).card
          + ∑ j : ι, Fintype.card S * (Finset.univ.filter fun c : ι → S =>
              accept c ∧ columnCount accept j c < k).card := by
        rw [Nat.mul_add, Finset.mul_sum]
    _ ≤ Fintype.card S * (Finset.univ.filter fun c : ι → S =>
            accept c ∧ ∀ j, k ≤ columnCount accept j c).card
          + ∑ _j : ι, (k - 1) * Fintype.card (ι → S) :=
        Nat.add_le_add_left
          (Finset.sum_le_sum fun j _ => card_mul_card_filter_columnCount_lt j k) _
    _ = _ := by rw [Finset.sum_const_nat (m := (k - 1) * Fintype.card (ι → S)) fun _ _ => rfl,
        Finset.card_univ]

omit [DecidableEq S] in
/-- The table success bound used in Lemma 7.1, as a ratio of cardinalities.

Writing `ε` for the fraction of accepting challenges and `N = Fintype.card S`, the fraction of
challenges that both accept and have every column thick is at least `ε - ℓ * (k - 1) / N`.
Uniform sampling identifies each side with a probability, which is the only step left to the
probability layer. -/
theorem sub_div_le_div_card_filter [Nonempty S] (k : ℕ) :
    ((Finset.univ.filter fun c : ι → S => accept c).card : ℝ≥0∞) / Fintype.card (ι → S)
        - (Fintype.card ι : ℝ≥0∞) * (k - 1 : ℕ) / Fintype.card S
      ≤ ((Finset.univ.filter fun c : ι → S =>
            accept c ∧ ∀ j, k ≤ columnCount accept j c).card : ℝ≥0∞)
          / Fintype.card (ι → S) := by
  have hN : (Fintype.card S : ℝ≥0∞) ≠ 0 := by simp
  have hNtop : (Fintype.card S : ℝ≥0∞) ≠ ⊤ := by finiteness
  have hT : (Fintype.card (ι → S) : ℝ≥0∞) ≠ 0 := by simp
  have hTtop : (Fintype.card (ι → S) : ℝ≥0∞) ≠ ⊤ := by finiteness
  have hcN := ENNReal.mul_inv_cancel hN hNtop
  have hcT := ENNReal.mul_inv_cancel hT hTtop
  have hcast : (Fintype.card S : ℝ≥0∞) *
        ((Finset.univ.filter fun c : ι → S => accept c).card : ℝ≥0∞)
      ≤ (Fintype.card S : ℝ≥0∞) * ((Finset.univ.filter fun c : ι → S =>
            accept c ∧ ∀ j, k ≤ columnCount accept j c).card : ℝ≥0∞)
          + (Fintype.card ι : ℝ≥0∞) * ((k - 1 : ℕ) * Fintype.card (ι → S)) := by
    exact_mod_cast card_mul_card_filter_accept_le (accept := accept) k
  -- Scale the counting bound by `(N * |ι → S|)⁻¹`; both denominators then cancel.
  rw [tsub_le_iff_right, div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv]
  calc ((Finset.univ.filter fun c : ι → S => accept c).card : ℝ≥0∞) *
        ((Fintype.card (ι → S) : ℝ≥0∞))⁻¹
      = ((Fintype.card S : ℝ≥0∞) *
          ((Finset.univ.filter fun c : ι → S => accept c).card : ℝ≥0∞)) *
          (((Fintype.card S : ℝ≥0∞))⁻¹ * ((Fintype.card (ι → S) : ℝ≥0∞))⁻¹) := by
        rw [show ((Fintype.card S : ℝ≥0∞) *
              ((Finset.univ.filter fun c : ι → S => accept c).card : ℝ≥0∞)) *
              (((Fintype.card S : ℝ≥0∞))⁻¹ * ((Fintype.card (ι → S) : ℝ≥0∞))⁻¹)
            = ((Fintype.card S : ℝ≥0∞) * ((Fintype.card S : ℝ≥0∞))⁻¹) *
              (((Finset.univ.filter fun c : ι → S => accept c).card : ℝ≥0∞) *
                ((Fintype.card (ι → S) : ℝ≥0∞))⁻¹) from by ring, hcN, one_mul]
    _ ≤ ((Fintype.card S : ℝ≥0∞) * ((Finset.univ.filter fun c : ι → S =>
            accept c ∧ ∀ j, k ≤ columnCount accept j c).card : ℝ≥0∞)
          + (Fintype.card ι : ℝ≥0∞) * ((k - 1 : ℕ) * Fintype.card (ι → S))) *
          (((Fintype.card S : ℝ≥0∞))⁻¹ * ((Fintype.card (ι → S) : ℝ≥0∞))⁻¹) := by
        gcongr
    _ = _ := by
        rw [add_mul,
          show ((Fintype.card S : ℝ≥0∞) * ((Finset.univ.filter fun c : ι → S =>
                accept c ∧ ∀ j, k ≤ columnCount accept j c).card : ℝ≥0∞)) *
              (((Fintype.card S : ℝ≥0∞))⁻¹ * ((Fintype.card (ι → S) : ℝ≥0∞))⁻¹)
            = ((Fintype.card S : ℝ≥0∞) * ((Fintype.card S : ℝ≥0∞))⁻¹) *
              (((Finset.univ.filter fun c : ι → S =>
                  accept c ∧ ∀ j, k ≤ columnCount accept j c).card : ℝ≥0∞) *
                ((Fintype.card (ι → S) : ℝ≥0∞))⁻¹) from by ring,
          show ((Fintype.card ι : ℝ≥0∞) * ((k - 1 : ℕ) * Fintype.card (ι → S))) *
              (((Fintype.card S : ℝ≥0∞))⁻¹ * ((Fintype.card (ι → S) : ℝ≥0∞))⁻¹)
            = ((Fintype.card (ι → S) : ℝ≥0∞) * ((Fintype.card (ι → S) : ℝ≥0∞))⁻¹) *
              ((Fintype.card ι : ℝ≥0∞) * ((k - 1 : ℕ) : ℝ≥0∞) *
                ((Fintype.card S : ℝ≥0∞))⁻¹) from by ring,
          hcN, hcT, one_mul, one_mul]

end ColumnCount

/-! ## The worked example of Fenzi–Moghaddas–Nguyen §2.9

`(0, 0, 0)` differs in, and only in, each coordinate from two other vectors of the displayed
seven-element set, so that set lies in `SS(S, 3, 3)`. -/

section Example

private def centre : Fin 3 → Fin 7 := ![0, 0, 0]

private def replacements : Fin 3 → Finset (Fin 7) := ![{2, 3}, {1, 2}, {5, 4}]

example : coordFamily centre replacements =
    {![2, 0, 0], ![0, 1, 0], ![0, 0, 0], ![0, 0, 5], ![0, 0, 4], ![0, 2, 0], ![3, 0, 0]} := by
  decide

example : IsCoordSpecialSound 3 (coordFamily centre replacements) :=
  isCoordSpecialSound_coordFamily (by decide) (by decide)

example : (coordFamily centre replacements).card = 7 := by decide

example : (coordFamily centre replacements).card = Fintype.card (Fin 3) * (3 - 1) + 1 :=
  card_coordFamily (by decide) (by decide)

end Example

end CoordinateWise
