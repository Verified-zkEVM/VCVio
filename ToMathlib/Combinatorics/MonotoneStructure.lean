/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import Mathlib.Order.Lattice.Nat
public import Mathlib.SetTheory.Cardinal.Finite
public import ToMathlib.Combinatorics.CoordinateWise

/-!
# Monotone structures and the `t`-value of coordinate-wise special soundness

Section 7.3 of Fenzi–Moghaddas–Nguyen, *Lattice-Based Polynomial Commitments* (eprint 2023/846):
why the generic `Γ`-out-of-`C` extractor of Attema–Fehr–Rambaud cannot be used for coordinate-wise
special soundness.

Coordinate-wise `k`-special soundness is the special case of `Γ`-out-of-`C` special soundness at
`C := S ^ ℓ` and `Γ := {C' : ∃ X ∈ SS(S, ℓ, k), X ⊆ C'}` (`coordStructure`). The generic extractor's
expected runtime is `2 ^ tᵧ - 1`, where `tᵧ` is the `t`-value of Definition 7.4, so a lower bound on
`tᵧ` is a lower bound on that runtime. The result here is

`Fintype.card S ^ (Fintype.card ι - 1) + 1 ≤ tValue (coordStructure 2) ∅`

(`pow_add_one_le_tValue`), exponential in `ℓ = Fintype.card ι` — whereas the extractor of §7 is
linear in `ℓ`. The `2 ^ t - 1` runtime itself is Lemma 5 of [AFR23] and is cited, not proved here.

## Main definitions

* `usefulElements Γ T` — Definition 7.3: the elements outside `T` that turn some `Γ`-set containing
  `T` into a non-`Γ`-set when removed.
* `IsUsefulSequence Γ T cs` — each entry of `cs` is useful given `T` and the entries before it.
* `tValue Γ T` — Definition 7.4: the greatest length of such a sequence. Well-defined because a
  useful sequence is `Nodup` and avoids `T` (`nodup_of_isUsefulSequence`).

## The lower bound

Fix a coordinate `j₀` and two values `d ≠ d'`. The slice `coordSlice j₀ d` of challenges with `j₀`
coordinate `d` contains no `SS(S, ℓ, 2)` set, because two challenges differing only in coordinate
`j₀` cannot both lie in it; but adjoining a single challenge off the slice creates one. That makes
every not-yet-taken element of the slice useful, and then one element off the slice useful again,
for a sequence of length `|slice| + 1 = |S| ^ (ℓ - 1) + 1`.
-/

@[expose] public section

open Finset Function

namespace CoordinateWise

/-! ## Monotone structures -/

section MonotoneStructure

variable {C : Type*} [DecidableEq C] [Finite C] {Γ : Finset C → Prop} {T : Finset C}
variable {cs : List C}

/-- **Definition 7.3** of Fenzi–Moghaddas–Nguyen (Useful Elements, after Attema–Fehr–Rambaud). An
element outside `T` is *useful* for `T` when some `Γ`-set containing `T` stops being a `Γ`-set once
that element is removed. -/
def usefulElements (Γ : Finset C → Prop) (T : Finset C) : Set C :=
  {c | c ∉ T ∧ ∃ A : Finset C, Γ A ∧ T ⊆ A ∧ ¬ Γ (A.erase c)}

omit [Finite C] in
theorem notMem_of_mem_usefulElements {c : C} (h : c ∈ usefulElements Γ T) : c ∉ T := h.1

omit [Finite C] in
/-- A useful element belongs to every witnessing `Γ`-set: otherwise removing it would change
nothing. -/
theorem mem_of_witness {c : C} {A : Finset C} (hA : Γ A) (herase : ¬ Γ (A.erase c)) : c ∈ A := by
  by_contra hc
  exact herase (by rwa [Finset.erase_eq_of_notMem hc])

omit [Finite C] in
/-- The paper writes `T ⊂ A` in Definition 7.3, this file writes `T ⊆ A`; the two agree, because a
useful element lies in the witness and outside `T`. -/
theorem mem_usefulElements_iff {c : C} :
    c ∈ usefulElements Γ T ↔ c ∉ T ∧ ∃ A : Finset C, Γ A ∧ T ⊂ A ∧ ¬ Γ (A.erase c) := by
  refine ⟨fun ⟨hcT, A, hA, hTA, herase⟩ => ⟨hcT, A, hA, ⟨hTA, fun hAT => hcT ?_⟩, herase⟩,
    fun ⟨hcT, A, hA, hTA, herase⟩ => ⟨hcT, A, hA, hTA.subset, herase⟩⟩
  exact hAT (mem_of_witness hA herase)

/-- The witness sequences of **Definition 7.4**: each entry is useful given the starting set
together with the entries before it. -/
def IsUsefulSequence (Γ : Finset C → Prop) : Finset C → List C → Prop
  | _, [] => True
  | T, c :: cs => c ∈ usefulElements Γ T ∧ IsUsefulSequence Γ (insert c T) cs

omit [Finite C] in
@[simp] theorem isUsefulSequence_nil : IsUsefulSequence Γ T [] := trivial

omit [Finite C] in
@[simp] theorem isUsefulSequence_cons {c : C} :
    IsUsefulSequence Γ T (c :: cs) ↔
      c ∈ usefulElements Γ T ∧ IsUsefulSequence Γ (insert c T) cs := Iff.rfl

omit [Finite C] in
/-- A useful sequence has no repeats and avoids its starting set: each entry is useful for a set
already containing all the earlier ones. -/
theorem nodup_of_isUsefulSequence :
    ∀ {T : Finset C} {cs : List C}, IsUsefulSequence Γ T cs → cs.Nodup ∧ ∀ c ∈ cs, c ∉ T
  | _, [], _ => ⟨List.nodup_nil, by simp⟩
  | T, c :: cs, h => by
      obtain ⟨hnd, havoid⟩ := nodup_of_isUsefulSequence h.2
      refine ⟨List.nodup_cons.mpr ⟨fun hc => havoid c hc (Finset.mem_insert_self c T), hnd⟩, ?_⟩
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact h.1.1
      · exact fun hxT => havoid x hx (Finset.mem_insert_of_mem hxT)

theorem length_le_card_of_isUsefulSequence (h : IsUsefulSequence Γ T cs) :
    cs.length ≤ Nat.card C := by
  classical
  have : Fintype C := Fintype.ofFinite C
  rw [Nat.card_eq_fintype_card, ← List.toFinset_card_of_nodup (nodup_of_isUsefulSequence h).1]
  exact Finset.card_le_univ _

/-- **Definition 7.4** (`t`-value, after Attema–Fehr–Rambaud). -/
noncomputable def tValue (Γ : Finset C → Prop) (T : Finset C) : ℕ :=
  sSup {t | ∃ cs : List C, cs.length = t ∧ IsUsefulSequence Γ T cs}

theorem bddAbove_useful_lengths :
    BddAbove {t | ∃ cs : List C, cs.length = t ∧ IsUsefulSequence Γ T cs} :=
  ⟨Nat.card C, fun _ ⟨_, hlen, h⟩ => hlen ▸ length_le_card_of_isUsefulSequence h⟩

/-- The `t`-value is finite, so the lower bound below is a statement with content. -/
theorem tValue_le_card : tValue Γ T ≤ Nat.card C :=
  csSup_le ⟨0, [], rfl, trivial⟩ fun _ ⟨_, hlen, h⟩ =>
    hlen ▸ length_le_card_of_isUsefulSequence h

/-- Every useful sequence bounds the `t`-value from below. -/
theorem length_le_tValue (h : IsUsefulSequence Γ T cs) : cs.length ≤ tValue Γ T :=
  le_csSup bddAbove_useful_lengths ⟨cs, rfl, h⟩

omit [Finite C] in
/-- Concatenating useful sequences, the second one starting from everything the first consumed. -/
theorem isUsefulSequence_append :
    ∀ {T : Finset C} {cs ds : List C}, IsUsefulSequence Γ T cs →
      IsUsefulSequence Γ (T ∪ cs.toFinset) ds → IsUsefulSequence Γ T (cs ++ ds)
  | T, [], ds, _, h' => by simpa using h'
  | T, c :: cs, ds, h, h' => by
      refine ⟨h.1, isUsefulSequence_append h.2 ?_⟩
      exact (show insert c T ∪ cs.toFinset = T ∪ (c :: cs).toFinset from by
        rw [List.toFinset_cons, Finset.insert_union, Finset.union_insert]) ▸ h'

omit [Finite C] in
/-- Enumerating a set all of whose untaken elements stay useful gives a useful sequence. -/
theorem isUsefulSequence_of_forall_mem_usefulElements {A : Finset C}
    (h : ∀ T' ⊆ A, ∀ c ∈ A, c ∉ T' → c ∈ usefulElements Γ T') :
    ∀ {T : Finset C} {cs : List C}, T ⊆ A → cs.Nodup → (∀ c ∈ cs, c ∈ A) →
      (∀ c ∈ cs, c ∉ T) → IsUsefulSequence Γ T cs
  | _, [], _, _, _, _ => trivial
  | T, c :: cs, hT, hnd, hmem, hdisj => by
      refine ⟨h T hT c (hmem c (by simp)) (hdisj c (by simp)), ?_⟩
      refine isUsefulSequence_of_forall_mem_usefulElements h
        (Finset.insert_subset (hmem c (by simp)) hT)
        (List.nodup_cons.mp hnd).2 (fun x hx => hmem x (by simp [hx])) fun x hx hxT => ?_
      rcases Finset.mem_insert.mp hxT with rfl | hxT
      · exact (List.nodup_cons.mp hnd).1 hx
      · exact hdisj x (by simp [hx]) hxT

end MonotoneStructure

/-! ## The coordinate-wise monotone structure -/

section Coord

variable {ι S : Type} [DecidableEq ι] [Fintype ι] [DecidableEq S] [Fintype S]
variable {k : ℕ} {j₀ : ι} {d d' : S}

/-- The monotone structure induced by coordinate-wise `k`-special soundness: the challenge sets
containing an `SS(S, ℓ, k)` set. -/
def coordStructure (k : ℕ) (X' : Finset (ι → S)) : Prop :=
  ∃ X ⊆ X', IsCoordSpecialSound k X

/-- The challenges whose `j₀` coordinate is `d`. -/
def coordSlice (j₀ : ι) (d : S) : Finset (ι → S) :=
  Finset.univ.filter fun c => c j₀ = d

@[simp] theorem mem_coordSlice {c : ι → S} : c ∈ coordSlice j₀ d ↔ c j₀ = d := by
  simp [coordSlice]

omit [DecidableEq ι] [Fintype S] in
/-- A coordinate-wise special sound set contains two challenges differing only in any prescribed
coordinate — the neighbour condition at that coordinate, which needs `2 ≤ k` to be nonempty. -/
theorem exists_differsOnlyAt_of_isCoordSpecialSound (hk : 2 ≤ k) {X : Finset (ι → S)}
    (hX : IsCoordSpecialSound k X) (j : ι) :
    ∃ e ∈ X, ∃ y ∈ X, DiffersOnlyAt j e y := by
  obtain ⟨⟨e, heX, hnb⟩, -⟩ := hX
  obtain ⟨J, hJ, hcard, hdiff⟩ := hnb j
  obtain ⟨y, hy⟩ : J.Nonempty := Finset.card_pos.mp (by omega)
  exact ⟨e, heX, y, Finset.mem_of_mem_erase (hJ hy), hdiff y hy⟩

/-- Two challenges in a common slice agree in the sliced coordinate, so they cannot differ there
and nowhere else. -/
theorem not_differsOnlyAt_of_mem_coordSlice {e y : ι → S} (he : e ∈ coordSlice j₀ d)
    (hy : y ∈ coordSlice j₀ d) : ¬ DiffersOnlyAt j₀ e y := fun h =>
  h.1 ((mem_coordSlice.mp he).trans (mem_coordSlice.mp hy).symm)

/-- A slice contains no coordinate-wise special sound set: everything in it agrees at `j₀`. -/
theorem not_coordStructure_coordSlice (hk : 2 ≤ k) (j₀ : ι) (d : S) :
    ¬ coordStructure k (coordSlice j₀ d) := by
  rintro ⟨X, hXsub, hX⟩
  obtain ⟨e, heX, y, hyX, hdiff⟩ := exists_differsOnlyAt_of_isCoordSpecialSound hk hX j₀
  exact not_differsOnlyAt_of_mem_coordSlice (hXsub heX) (hXsub hyX) hdiff

/-- Adjoining one challenge off the slice creates an `SS(S, ℓ, 2)` set: the adjoined challenge is
the `j₀` neighbour of its slice partner, and every other coordinate has a neighbour inside the
slice. -/
theorem coordStructure_insert_update [Nontrivial S] (hd : d' ≠ d) {c : ι → S}
    (hc : c ∈ coordSlice j₀ d) :
    coordStructure 2 (insert (Function.update c j₀ d') (coordSlice j₀ d)) := by
  classical
  have hx : ∀ j : ι, ∃ u : S, u ≠ c j := fun j => exists_ne (c j)
  choose x hx using hx
  refine ⟨coordFamily c fun j => if j = j₀ then {d'} else {x j}, fun z hz => ?_,
    isCoordSpecialSound_coordFamily (fun j => ?_) fun j => ?_⟩
  · rcases mem_coordFamily.mp hz with rfl | ⟨j, u, hu, rfl⟩
    · exact Finset.mem_insert_of_mem hc
    · by_cases hj : j = j₀
      · subst hj
        rw [if_pos rfl, Finset.mem_singleton] at hu
        exact hu ▸ Finset.mem_insert_self _ _
      · rw [if_neg hj, Finset.mem_singleton] at hu
        exact Finset.mem_insert_of_mem
          (mem_coordSlice.mpr (by rw [Function.update_of_ne (Ne.symm hj), mem_coordSlice.mp hc]))
  · by_cases hj : j = j₀
    · subst hj
      intro hmem
      have hcd : c j = d' := by simpa using hmem
      exact hd (hcd.symm.trans (mem_coordSlice.mp hc))
    · simpa [hj] using fun h => hx j h.symm
  · by_cases hj : j = j₀ <;> simp [hj]

/-- Removing the slice partner destroys it again: in `slice ∪ {b}` the only pair differing solely
at `j₀` is `b` together with the challenge that `b` was built from. -/
theorem not_coordStructure_erase_update (hk : 2 ≤ k) (d' : S) {c : ι → S}
    (hc : c ∈ coordSlice j₀ d) :
    ¬ coordStructure k ((insert (Function.update c j₀ d') (coordSlice j₀ d)).erase c) := by
  classical
  set b := Function.update c j₀ d' with hb
  have hbj : b j₀ = d' := by simp [hb]
  have hkey : ∀ y ∈ insert b (coordSlice j₀ d), DiffersOnlyAt j₀ b y → y = c := by
    intro y hy hdiff
    have hyslice : y ∈ coordSlice j₀ d := by
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact absurd rfl hdiff.1
      · exact hy
    refine funext fun i => ?_
    by_cases hi : i = j₀
    · subst hi; rw [mem_coordSlice.mp hyslice, mem_coordSlice.mp hc]
    · rw [← hdiff.2 i hi, hb, Function.update_of_ne hi]
  rintro ⟨X, hXsub, hX⟩
  obtain ⟨e, heX, y, hyX, hdiff⟩ := exists_differsOnlyAt_of_isCoordSpecialSound hk hX j₀
  have he := Finset.mem_of_mem_erase (hXsub heX)
  have hy := Finset.mem_of_mem_erase (hXsub hyX)
  rcases Finset.mem_insert.mp he with rfl | heslice
  · exact (Finset.ne_of_mem_erase (hXsub hyX)) (hkey y hy hdiff)
  · rcases Finset.mem_insert.mp hy with rfl | hyslice
    · exact (Finset.ne_of_mem_erase (hXsub heX)) (hkey e he hdiff.symm)
    · exact not_differsOnlyAt_of_mem_coordSlice heslice hyslice hdiff

/-! ### The useful sequence -/

/-- Every element of the slice not yet taken is useful. -/
theorem mem_usefulElements_of_mem_coordSlice [Nontrivial S] (hd : d' ≠ d) {T : Finset (ι → S)}
    (hT : T ⊆ coordSlice j₀ d) {c : ι → S} (hc : c ∈ coordSlice j₀ d) (hcT : c ∉ T) :
    c ∈ usefulElements (coordStructure 2) T :=
  ⟨hcT, insert (Function.update c j₀ d') (coordSlice j₀ d),
    coordStructure_insert_update hd hc,
    hT.trans (Finset.subset_insert _ _),
    not_coordStructure_erase_update le_rfl d' hc⟩

/-- Once the whole slice is taken, one challenge off it is still useful: adjoining it creates an
`SS(S, ℓ, 2)` set, and the slice alone is not one. -/
theorem mem_usefulElements_update_of_coordSlice [Nontrivial S] (hd : d' ≠ d) (v : ι → S) :
    Function.update v j₀ d' ∈ usefulElements (coordStructure 2) (coordSlice j₀ d) := by
  classical
  have hv : Function.update v j₀ d ∈ coordSlice j₀ d := by simp
  have hupd : Function.update (Function.update v j₀ d) j₀ d' = Function.update v j₀ d' := by
    simp [Function.update_idem]
  refine ⟨by simp [hd], insert (Function.update v j₀ d') (coordSlice j₀ d), ?_,
    Finset.subset_insert _ _, ?_⟩
  · have hins := coordStructure_insert_update (j₀ := j₀) hd hv
    rwa [hupd] at hins
  · rw [Finset.erase_insert (by simp [hd])]
    exact not_coordStructure_coordSlice le_rfl j₀ d

/-- **The lower bound of §7.3.** Enumerating the slice and then one challenge off it is a useful
sequence, so the `t`-value is at least one more than the slice's size. -/
theorem card_coordSlice_add_one_le_tValue [Nontrivial S] (hd : d' ≠ d) :
    (coordSlice j₀ d).card + 1 ≤ tValue (coordStructure 2) (∅ : Finset (ι → S)) := by
  classical
  set cs := (coordSlice j₀ d).toList with hcs
  have hcsF : cs.toFinset = coordSlice j₀ d := by simp [hcs]
  have h₁ : IsUsefulSequence (coordStructure 2) ∅ cs :=
    isUsefulSequence_of_forall_mem_usefulElements
      (fun T' hT' c hc hcT' => mem_usefulElements_of_mem_coordSlice hd hT' hc hcT')
      (Finset.empty_subset _) (Finset.nodup_toList _)
      (fun c hc => Finset.mem_toList.mp hc) (by simp)
  have h₂ : IsUsefulSequence (coordStructure 2) (∅ ∪ cs.toFinset)
      [Function.update (Classical.arbitrary (ι → S)) j₀ d'] := by
    refine ⟨?_, trivial⟩
    rw [Finset.empty_union, hcsF]
    exact mem_usefulElements_update_of_coordSlice hd _
  have := length_le_tValue (isUsefulSequence_append h₁ h₂)
  simpa [hcs, Finset.length_toList] using this

/-- A slice has `|S| ^ (ℓ - 1)` elements: it is determined by the coordinates other than `j₀`. -/
theorem card_coordSlice (j₀ : ι) (d : S) :
    (coordSlice j₀ d).card = Fintype.card S ^ (Fintype.card ι - 1) := by
  classical
  have hbij : (coordSlice j₀ d).card = (Finset.univ : Finset ({j : ι // j ≠ j₀} → S)).card := by
    refine Finset.card_bij (fun c _ j => c j.1) (fun _ _ => Finset.mem_univ _) ?_ ?_
    · intro a ha b hb hab
      refine funext fun i => ?_
      by_cases hi : i = j₀
      · subst hi; rw [mem_coordSlice.mp ha, mem_coordSlice.mp hb]
      · exact congrFun hab ⟨i, hi⟩
    · intro f _
      refine ⟨fun i => if h : i = j₀ then d else f ⟨i, h⟩, mem_coordSlice.mpr (by simp), ?_⟩
      exact funext fun j => by simp [j.2]
  rw [hbij, Finset.card_univ, Fintype.card_pi, Finset.prod_const, Finset.card_univ,
    Fintype.card_subtype_compl, Fintype.card_subtype_eq]

omit [DecidableEq ι] in
/-- **Section 7.3.** The `t`-value of the coordinate-wise monotone structure is at least
`|S| ^ (ℓ - 1) + 1`. Since the generic `Γ`-out-of-`C` extractor of [AFR23] runs in expected time
`2 ^ tᵧ - 1`, its runtime is exponential in `ℓ`, whereas the extractor of §7 is linear in `ℓ`. That
is why coordinate-wise special soundness needs its own extractor. -/
theorem pow_add_one_le_tValue [Nontrivial S] [Nonempty ι] :
    Fintype.card S ^ (Fintype.card ι - 1) + 1 ≤
      tValue (coordStructure 2) (∅ : Finset (ι → S)) := by
  classical
  obtain ⟨d, d', hne⟩ := exists_pair_ne S
  rw [← card_coordSlice (Classical.arbitrary ι) d]
  exact card_coordSlice_add_one_le_tValue (d' := d') hne.symm

end Coord

end CoordinateWise
