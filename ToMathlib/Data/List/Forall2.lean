/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import Mathlib.Data.List.Forall2
public import Mathlib.Data.List.Range

/-!
# `List.Forall₂` against `filterMap` and against the list of a vector

When a partial map `f` is defined at every entry of `l`, with values related by `R` to the
matching entries of `l'`, the list `l.filterMap f` of its values is related to `l'` entrywise. A
list read off along `List.range n` is related entrywise to the list of a vector of length `n`
exactly when each read value is related to the vector's entry at the same index.
-/

public section

namespace List

variable {α β γ : Type*}

/-- When `f` is defined at every entry of `l` with a value related by `R` to the matching entry of
`l'`, the defined values `l.filterMap f` are related to `l'` entrywise. -/
theorem forall₂_filterMap_of_forall₂ {f : α → Option β} {R : β → γ → Prop} :
    ∀ {l : List α} {l' : List γ}, Forall₂ (fun a c ↦ ∃ b, f a = some b ∧ R b c) l l' →
      Forall₂ R (l.filterMap f) l'
  | _, _, .nil => .nil
  | _, _, .cons ⟨_, hb, h⟩ hl => by
    rw [filterMap_cons, hb]
    exact .cons h (forall₂_filterMap_of_forall₂ hl)

end List

namespace Vector

variable {α β : Type*}

/-- A list read off along `List.range n` is related entrywise to the list of a vector of length
`n` exactly when each read value is related to the vector's entry at the same index. -/
theorem forall₂_map_range_toList_iff {R : α → β → Prop} {n : ℕ} {f : ℕ → α} {v : Vector β n} :
    List.Forall₂ R ((List.range n).map f) v.toList ↔ ∀ i : Fin n, R (f i) v[i] := by
  rw [List.forall₂_iff_get]
  simp only [List.length_map, List.length_range, Vector.length_toList, List.get_eq_getElem,
    List.getElem_map, List.getElem_range, Vector.getElem_toList, true_and]
  exact ⟨fun h i ↦ h i i.isLt i.isLt, fun h i hi _ ↦ h ⟨i, hi⟩⟩

end Vector
