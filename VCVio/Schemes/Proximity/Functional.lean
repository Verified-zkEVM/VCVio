/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kobi Gurkan, Quang Dao
-/

module
public import VCVio.Schemes.Proximity.Distribution
public import VCVio.Schemes.Proximity.Extraction
public import VCVio.CryptoFoundations.GroupModel.LinearFunctional.TraceExtraction

/-! # Proximity's finite signing functional

The proof cover consists of base indices, even for an infinite slot type. The signing
functional retains chronological coefficient positions. Its scalar interpretations are the
good reduction's linear coefficient and the bad reduction's two mask coefficients.
-/

public section

open OracleComp OracleSpec GroupModel.Interaction GroupModel.LinearFunctional

namespace Proximity.AGM

/-- The chronological output and public reply labels of a Proximity execution. -/
abbrev Trace (F Slot G₁ G₂ : Type) (dimension : ℕ) :=
  Explained F (Proximity.Message F Slot dimension) (Group G₁ G₂) ×
    Weighted.Transcript (Index Slot dimension) (Proximity.Message F Slot dimension)

/-- The weights of a message on a finite proof cover of base indices. -/
@[expose] def weights {F Slot : Type} [Semiring F] [DecidableEq Slot] {dimension : ℕ}
    (S : Finset (Index Slot dimension)) (m : Proximity.Message F Slot dimension) : S → F :=
  Weighted.value (fun i => labelWeight S i) (terms m)

/-- The signing functional, with zero at the initial generator and all hash positions. -/
@[expose] def functional {F Slot G₁ G₂ : Type} [Semiring F] [DecidableEq Slot]
    {dimension : ℕ} (S : Finset (Index Slot dimension)) (z : Trace F Slot G₁ G₂ dimension) :
    S → F := evaluate (coefficients z.1)
      ([0] ++ z.2.map (Sum.elim (fun _ => 0) (weights S)))

/-- The difference of target weights and the represented signing weights. -/
@[expose] def gap {F Slot G₁ G₂ : Type} [Ring F] [DecidableEq Slot] {dimension : ℕ}
    (S : Finset (Index Slot dimension)) (z : Trace F Slot G₁ G₂ dimension) : S → F :=
  weights S z.1.value.data - functional S z

/-- The scalar linear map interpreting a finite coefficient vector. -/
@[expose] def tableEval {F ι : Type} [CommSemiring F] [Fintype ι]
    (ρ : ι → F) : (ι → F) →ₗ[F] F := ∑ i, ρ i • LinearMap.proj i

/-- A finite coefficient vector is interpreted by its scalar dot product. -/
theorem tableEval_apply {F ι : Type} [CommSemiring F] [Fintype ι]
    (ρ v : ι → F) : tableEval ρ v = ∑ i, v i * ρ i := by
  simp [tableEval, mul_comm]

/-- The message weights interpret to the weighted scalar hash, using zero outside the cover. -/
theorem tableEval_weights {F Slot : Type} [CommSemiring F] [DecidableEq Slot]
    {dimension : ℕ} (S : Finset (Index Slot dimension)) (ρ : S → F)
    (m : Proximity.Message F Slot dimension) :
    tableEval ρ (weights S m) = Weighted.value (extendTable S 0 ρ) (terms m) := by
  rw [weights, ← Weighted.value_map]
  congr 1
  funext i
  simpa only [tableEval_apply] using sum_labelWeight_mul S i ρ

/-- Applying a linear map to the signing functional preserves every chronological position. -/
theorem functional_map {F Slot G₁ G₂ V : Type} [Semiring F] [DecidableEq Slot]
    [AddCommMonoid V] [Module F V] {dimension : ℕ}
    (S : Finset (Index Slot dimension)) (z : Trace F Slot G₁ G₂ dimension)
    (f : (S → F) →ₗ[F] V) :
    f (functional S z) = evaluate (coefficients z.1)
      ([0] ++ z.2.map (Sum.elim (fun _ => 0) (fun m => f (weights S m)))) := by
  rw [functional, ← evaluate_map]
  congr 1
  simp only [List.map_append, List.map_cons, List.map_nil, map_zero, List.map_map]
  congr 1
  apply List.map_congr_left
  intro q _
  cases q <;> simp

/-- The good reduction's linear coefficient is the scalar interpretation of signing weights. -/
theorem functional_good {F Slot G₁ G₂ : Type} [CommSemiring F] [DecidableEq Slot]
    {dimension : ℕ} (S : Finset (Index Slot dimension)) (ρ : S → F)
    (z : Trace F Slot G₁ G₂ dimension) :
    (goodRepresentation (extendTable S 0 ρ) z.1 z.2).lin = tableEval ρ (functional S z) := by
  rw [functional_map]
  unfold goodRepresentation
  have h := evaluate_map (LinearMap.snd F F F) (coefficients z.1)
    ([(1, 0)] ++ z.2.map (Sum.elim (fun i => (extendTable S 0 ρ i, (0 : F)))
      (fun m => ((0 : F), Weighted.value (extendTable S 0 ρ) (terms m)))))
  simp only [LinearMap.snd_apply] at h
  dsimp only
  rw [← h]
  congr 1
  simp only [List.map_append, List.map_cons, List.map_nil, List.map_map,
    LinearMap.snd_apply]
  congr 1
  apply List.map_congr_left
  intro q _
  cases q <;> simp [tableEval_weights]

/-- The good verification gap is the finite linear functional of the scalar table. -/
theorem gap_eq {F Slot G₁ G₂ : Type} [CommRing F] [DecidableEq Slot] {dimension : ℕ}
    (S : Finset (Index Slot dimension)) (ρ : S → F) (z : Trace F Slot G₁ G₂ dimension) :
    Weighted.value (extendTable S 0 ρ) (terms z.1.value.data) -
        (goodRepresentation (extendTable S 0 ρ) z.1 z.2).lin =
      ∑ i, gap S z i * ρ i := by
  rw [functional_good, ← tableEval_weights, ← map_sub, tableEval_apply]
  rfl

/-- Each covered base has exactly the direct scheme's coordinate weight. -/
theorem weights_apply {F Slot : Type} [CommSemiring F] [DecidableEq Slot]
    {dimension : ℕ} (S : Finset (Index Slot dimension))
    (m : Proximity.Message F Slot dimension) (i : S) :
    weights S m i = coordinateWeight i.val m := by
  rcases hi : i.val.1 with _ | k <;>
    simp [weights, Weighted.value, terms, labelWeight, List.map_ofFn, List.sum_ofFn,
      coordinateWeight, hi, Prod.ext_iff, eq_comm]
  by_cases hs : m.2 = i.val.2 <;> simp [hs]

/-- Summing one coordinate's weights across the covered slots recovers that vector entry. -/
theorem weights_coordinate {F Slot : Type} [CommSemiring F] [DecidableEq Slot]
    {dimension : ℕ} (S : Finset (Index Slot dimension))
    (m : Proximity.Message F Slot dimension) (h : Weighted.ReplyCovered terms S (.inr m))
    (k : Fin dimension) :
    tableEval (fun i : S => if i.val.1 = some k then 1 else 0) (weights S m) = m.1 k := by
  classical
  have hm : (some k, m.2) ∈ S := h ((some k, m.2), m.1 k) (by simp [terms])
  rw [tableEval_apply, Finset.sum_eq_single (⟨(some k, m.2), hm⟩ : S)]
  · simp [weights_apply, coordinateWeight]
  · intro i _ hi
    by_cases hk : i.val.1 = some k
    · have hs : i.val.2 ≠ m.2 := by
        intro hs
        apply hi
        exact Subtype.ext (Prod.ext hk hs)
      simp [weights_apply, coordinateWeight, hs]
    · simp [hk]
  · simp

/-- Projection of covered base weights to their vector coordinates. -/
@[expose] def vectorMap {F Slot : Type} [CommSemiring F] {dimension : ℕ}
    (S : Finset (Index Slot dimension)) : (S → F) →ₗ[F] (Fin dimension → F) :=
  LinearMap.pi fun k => tableEval (fun i : S => if i.val.1 = some k then 1 else 0)

/-- The covered weights of a message project to its actual vector. -/
theorem vectorMap_weights {F Slot : Type} [CommSemiring F] [DecidableEq Slot]
    {dimension : ℕ} (S : Finset (Index Slot dimension))
    (m : Proximity.Message F Slot dimension) (h : Weighted.ReplyCovered terms S (.inr m)) :
    vectorMap S (weights S m) = m.1 := by
  funext k
  exact weights_coordinate S m h k

/-- The same projection sends the signing functional to the source's signing-vector sum. -/
theorem vectorMap_functional {F Slot G₁ G₂ : Type} [CommSemiring F] [DecidableEq Slot]
    {dimension : ℕ} (S : Finset (Index Slot dimension)) (z : Trace F Slot G₁ G₂ dimension)
    (h : ∀ q ∈ z.2, Weighted.ReplyCovered terms S q) :
    vectorMap S (functional S z) = signingVector (coefficients z.1) z.2 := by
  rw [functional_map]
  unfold signingVector
  congr 2
  apply List.map_congr_left
  intro q hq
  cases q with
  | inl i => rfl
  | inr m => exact vectorMap_weights S m (h (.inr m) hq)

/-- A noncolliding target vector forces a nonzero gap in the finite base cover. -/
theorem gap_ne_zero {F Slot G₁ G₂ : Type} [CommRing F] [DecidableEq Slot]
    {dimension : ℕ} (S : Finset (Index Slot dimension)) (z : Trace F Slot G₁ G₂ dimension)
    (htarget : Weighted.ReplyCovered terms S (.inr z.1.value.data))
    (htrace : ∀ q ∈ z.2, Weighted.ReplyCovered terms S q)
    (hnc : z.1.value.data.1 ≠ signingVector (coefficients z.1) z.2) :
    ∃ i : S, gap S z i ≠ 0 := by
  by_contra h
  push Not at h
  have hw : weights S z.1.value.data = functional S z := by
    funext i
    exact sub_eq_zero.mp (h i)
  apply hnc
  rw [← vectorMap_weights S _ htarget, hw, vectorMap_functional S z htrace]

/-- The affine signing representation consists of the two interpretations of the functional. -/
theorem functional_bad {F Slot G₁ G₂ : Type} [CommSemiring F] [DecidableEq Slot]
    {dimension : ℕ} (S : Finset (Index Slot dimension)) (a b : S → F)
    (z : Trace F Slot G₁ G₂ dimension) :
    evaluate (coefficients z.1) ([(0, 0)] ++ z.2.map
      (Sum.elim (fun _ => ((0 : F), (0 : F)))
        (fun m => (Weighted.value (extendTable S 0 a) (terms m),
          Weighted.value (extendTable S 0 b) (terms m))))) =
      (tableEval a (functional S z), tableEval b (functional S z)) := by
  have h := functional_map S z ((tableEval a).prod (tableEval b))
  simpa only [LinearMap.prod_apply, Function.prod, Prod.zero_eq_mk, tableEval_weights] using h.symm

end Proximity.AGM
