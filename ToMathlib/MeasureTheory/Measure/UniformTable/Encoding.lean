/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import ToMathlib.MeasureTheory.Measure.UniformTable
public import Mathlib.Logic.Equiv.Set

/-!
# Splitting a uniform table along an encoding

An injective encoding selects cells of a table. Each selected response is split into its
visible value and a complementary tail; all cells outside the encoding's image are retained.
The resulting whole-table equivalence transports uniform sampling exactly. In particular,
tails are fixed across repeated reads and no outside-image cell is discarded.
-/

public section

open MeasureTheory

namespace Equiv

variable {D I M : Type*} {A Tail : I → Type*}

/-- Encoded inputs together with all outside-image inputs form the complete raw domain. -/
@[expose]
noncomputable def encodingDomain (encode : I → D) (hinj : Function.Injective encode) :
    I ⊕ {x : D // x ∉ Set.range encode} ≃ D := by
  classical
  exact ((ofInjective encode hinj).sumCongr (Equiv.refl _)).trans
    (Equiv.Set.sumCompl (Set.range encode))

/-- The encoded summand is mapped to its raw input. -/
@[simp]
theorem encodingDomain_inl (encode : I → D) (hinj : Function.Injective encode) (i : I) :
    encodingDomain encode hinj (.inl i) = encode i := rfl

/-- The outside-image summand retains its raw input. -/
@[simp]
theorem encodingDomain_inr (encode : I → D) (hinj : Function.Injective encode)
    (x : {x : D // x ∉ Set.range encode}) :
    encodingDomain encode hinj (.inr x) = x := rfl

/-- A raw table is equivalent to its visible encoded table, its encoded tail table, and its
complete outside-image table. No response algebra is required. -/
@[expose]
noncomputable def tableSplit (encode : I → D) (hinj : Function.Injective encode)
    (split : ∀ i, M ≃ A i × Tail i) :
    (D → M) ≃ (((∀ i, A i) × (∀ i, Tail i)) ×
      ({x : D // x ∉ Set.range encode} → M)) :=
  (arrowCongr (encodingDomain encode hinj).symm (Equiv.refl M)).trans
    ((sumArrowEquivProdArrow I _ M).trans
      (((piCongrRight split).trans (arrowProdEquivProdArrow I A Tail)).prodCongr
        (Equiv.refl _)))

/-- The visible table reads the visible part of each encoded raw response. -/
@[simp]
theorem tableSplit_apply_typed (encode : I → D) (hinj : Function.Injective encode)
    (split : ∀ i, M ≃ A i × Tail i) (H : D → M) (i : I) :
    (tableSplit encode hinj split H).1.1 i = (split i (H (encode i))).1 := rfl

/-- The tail table retains the complementary part of each encoded raw response. -/
@[simp]
theorem tableSplit_apply_tail (encode : I → D) (hinj : Function.Injective encode)
    (split : ∀ i, M ≃ A i × Tail i) (H : D → M) (i : I) :
    (tableSplit encode hinj split H).1.2 i = (split i (H (encode i))).2 := rfl

/-- The outside-image table retains every unencoded cell. -/
@[simp]
theorem tableSplit_apply_junk (encode : I → D) (hinj : Function.Injective encode)
    (split : ∀ i, M ≃ A i × Tail i) (H : D → M)
    (x : {x : D // x ∉ Set.range encode}) :
    (tableSplit encode hinj split H).2 x = H x := rfl

/-- Completing a split table at an encoded input rejoins its visible and tail coordinates. -/
@[simp]
theorem tableSplit_symm_apply_encode (encode : I → D) (hinj : Function.Injective encode)
    (split : ∀ i, M ≃ A i × Tail i)
    (tables : ((∀ i, A i) × (∀ i, Tail i)) × ({x : D // x ∉ Set.range encode} → M))
    (i : I) :
    (tableSplit encode hinj split).symm tables (encode i) =
      (split i).symm (tables.1.1 i, tables.1.2 i) := by
  apply (split i).injective
  have h := (tableSplit encode hinj split).apply_symm_apply tables
  have h₁ := congrArg (fun t ↦ t.1.1 i) h
  have h₂ := congrArg (fun t ↦ t.1.2 i) h
  rw [apply_symm_apply]
  exact Prod.ext h₁ h₂

/-- Completing a split table preserves the supplied value at every outside-image input. -/
@[simp]
theorem tableSplit_symm_apply_junk (encode : I → D) (hinj : Function.Injective encode)
    (split : ∀ i, M ≃ A i × Tail i)
    (tables : ((∀ i, A i) × (∀ i, Tail i)) × ({x : D // x ∉ Set.range encode} → M))
    (x : {x : D // x ∉ Set.range encode}) :
    (tableSplit encode hinj split).symm tables x = tables.2 x := by
  exact congrArg (fun t ↦ t.2 x) ((tableSplit encode hinj split).apply_symm_apply tables)

end Equiv

namespace ProbabilityTheory

/-- Reindexing a finite uniform average preserves any measure-valued continuation, including
one that observes the sampled parameter jointly with its output. -/
theorem uniformOn_univ_bind_equiv {α β γ : Type*} [Finite α] [Finite β]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    [MeasurableSpace β] [MeasurableSingletonClass β] [MeasurableSpace γ]
    (e : α ≃ β) (f : β → Measure γ) :
    (uniformOn Set.univ : Measure β).bind f =
      (uniformOn Set.univ : Measure α).bind (fun a ↦ f (e a)) := by
  let : Fintype α := Fintype.ofFinite α
  let : Fintype β := Fintype.ofFinite β
  ext s hs
  rw [uniformOn_univ_bind_apply _ _ hs, uniformOn_univ_bind_apply _ _ hs,
    Fintype.card_congr e]
  exact (e.sum_comp (fun b ↦ (Fintype.card β : ENNReal)⁻¹ * f b s)).symm

/-- Splitting a uniformly sampled finite raw table gives a uniformly sampled complete split
parameter. Its visible values, fixed tails and outside-image cells are all retained. -/
theorem uniformOn_univ_map_tableSplit {D I M : Type*} {A Tail : I → Type*}
    [Finite D] [Finite M]
    (encode : I → D) (hinj : Function.Injective encode)
    (split : ∀ i, M ≃ A i × Tail i)
    [MeasurableSpace (D → M)] [MeasurableSingletonClass (D → M)]
    [MeasurableSpace (((∀ i, A i) × (∀ i, Tail i)) ×
      ({x : D // x ∉ Set.range encode} → M))]
    [MeasurableSingletonClass (((∀ i, A i) × (∀ i, Tail i)) ×
      ({x : D // x ∉ Set.range encode} → M))] :
    (uniformOn Set.univ : Measure (D → M)).map (Equiv.tableSplit encode hinj split) =
      uniformOn Set.univ := by
  have : Finite (((∀ i, A i) × (∀ i, Tail i)) ×
      ({x : D // x ∉ Set.range encode} → M)) :=
    Finite.of_equiv (D → M) (Equiv.tableSplit encode hinj split)
  exact uniformOn_univ_map_equiv (Equiv.tableSplit encode hinj split)

end ProbabilityTheory
