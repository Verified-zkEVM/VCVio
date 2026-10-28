/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.CryptoFoundations.GroupModel.HashToGroup.Provenance
public import VCVio.OracleComp.QueryTracking.RandomOracle.SlotRenaming

/-! # Transport from label origins to finite challenge slots

Fixed inputs keep separate coordinates. Hash origins are renamed by an injective partial slot
assignment. On the received origins this renaming preserves unequal merged representations.
-/

public section

namespace GroupModel.HashToGroup

open OracleComp OracleSpec Interaction

variable {F G Label : Type} {n q : ℕ}

/-- Fixed-input origins followed by the chronological labels in a hash receipt log. -/
@[expose] def receiptOrigins (n : ℕ) (log : List (Label × G)) : List (Origin n Label) :=
  List.ofFn Sum.inl ++ log.map (Sum.inr ∘ Prod.fst)

/-- The reduction-basis coordinate corresponding to a fixed input or an assigned hash label.
An unassigned hash origin has the zero row; bounded executions assign every received origin. -/
@[expose] def slotRow [Semiring F] (slots : Label → Option (Fin q)) :
    Origin n Label → (Origin n (Fin q) → F)
  | .inl i => Pi.single (.inl i) 1
  | .inr l => match slots l with
    | some i => Pi.single (.inr i) 1
    | none => 0

/-- Read a finite-slot representation at each original symbolic coordinate. -/
@[expose] def slotPullback [Semiring F] (slots : Label → Option (Fin q)) :
    (Origin n (Fin q) → F) →ₗ[F] (Origin n Label → F) where
  toFun c := Sum.elim (fun i => c (.inl i))
    (fun l => match slots l with | some i => c (.inr i) | none => 0)
  map_add' a b := by
    funext i
    cases i with
    | inl i => rfl
    | inr l => cases hs : slots l <;> simp [hs]
  map_smul' a b := by
    funext i
    cases i with
    | inl i => rfl
    | inr l => cases hs : slots l <;> simp [hs]

private theorem slotPullback_slotRow [Semiring F] [DecidableEq Label]
    (slots : Label → Option (Fin q))
    (hi : ∀ l k i, slots l = some i → slots k = some i → l = k)
    (v : Origin n Label) (hv : ∀ l, v = .inr l → slots l ≠ none) :
    slotPullback slots (slotRow (F := F) slots v) = Pi.single v 1 := by
  funext u
  cases v with
  | inl i =>
    cases u with
    | inl j => simp [slotPullback, slotRow, Pi.single_apply]
    | inr l => cases hs : slots l <;> simp [slotPullback, slotRow, Pi.single_apply, hs]
  | inr l =>
    obtain ⟨i, hl⟩ := Option.ne_none_iff_exists'.mp (hv l rfl)
    cases u with
    | inl j => simp [slotPullback, slotRow, hl, Pi.single_apply]
    | inr k =>
      cases hk : slots k with
      | none =>
        have hkl : k ≠ l := by intro h; subst k; simp [hl] at hk
        simp [slotPullback, slotRow, hl, hk, Pi.single_apply, hkl]
      | some j =>
        have he : j = i ↔ k = l := by
          constructor
          · intro h
            subst j
            exact hi k l i hk hl
          · intro h
            subst k
            exact Option.some.inj (hk.symm.trans hl)
        simp [slotPullback, slotRow, hl, hk, Pi.single_apply, he]

/-- Substituting slot rows preserves the merged representation when pulled back to labels. -/
theorem slotPullback_transport [Semiring F] [DecidableEq Label]
    (slots : Label → Option (Fin q))
    (hi : ∀ l k i, slots l = some i → slots k = some i → l = k)
    (origins : List (Origin n Label))
    (ho : ∀ l, .inr l ∈ origins → slots l ≠ none) (c : List F) :
    slotPullback slots (transport (origins.map (slotRow slots)) c) = merge origins c := by
  rw [transport, evaluate_linearMap]
  unfold merge transport
  congr 1
  rw [List.map_map]
  apply List.map_congr_left
  intro v hv
  exact slotPullback_slotRow slots hi v (fun l hl => ho l (hl ▸ hv))

/-- The difference of the first two explanations after substitution into finite challenge slots. -/
@[expose] def slotDifference [Ring F] (slots : Label → Option (Fin q))
    (origins : List (Origin n Label)) (out : Explained F Unit (fun _ : Unit => G)) :
    Origin n (Fin q) → F :=
  transport (origins.map (slotRow slots)) (((out.coefficients ())[0]?).getD []) -
    transport (origins.map (slotRow slots)) (((out.coefficients ())[1]?).getD [])

/-- A normalized collision cannot disappear under an injective assignment of all received
hash origins to finite slots. Repeated receipt positions are merged before this assertion. -/
theorem slotDifference_ne_zero [Ring F] [DecidableEq Label]
    (slots : Label → Option (Fin q))
    (hi : ∀ l k i, slots l = some i → slots k = some i → l = k)
    (origins : List (Origin n Label))
    (ho : ∀ l, .inr l ∈ origins → slots l ≠ none)
    (out : Explained F Unit (fun _ : Unit => G)) (hc : NormalizedCollision origins out) :
    slotDifference slots origins out ≠ 0 := by
  intro hz
  have he := congrArg (slotPullback slots) hz
  simp only [slotDifference, map_sub, map_zero,
    slotPullback_transport slots hi origins ho] at he
  exact mergedDifference_ne_zero origins out hc he

end GroupModel.HashToGroup
