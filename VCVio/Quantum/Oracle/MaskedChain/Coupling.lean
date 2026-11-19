/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import ToMathlib.MeasureTheory.Measure.UniformTable.Bounds
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Order.Interval.Finset.Fin

/-!
# Classical couplings for masked chains

Head-priority oracle programming assigns a repeated input the value at its least index.
A permutation of a uniform table and independent programming values shows that the programmed
table stays uniform even when inputs repeat. Additive mask reparameterization preserves the
hidden vertices while moving the fresh randomness to the published masks.

These facts concern the full classical challenge data, rather than only oracle marginals.
They support comparisons whose final observer checks the adversary's output against a hidden
chain endpoint.

## References

* Afshar et al., *On the (Im)possibility of Time-Lock Puzzles in the Quantum Random Oracle
  Model*, Asiacrypt 2023, §5, Definition 5.1 and the proof of Theorem 5.3.
-/

public section

open MeasureTheory ProbabilityTheory
namespace Quantum.MaskedChain
universe u v
variable {X : Type u} {Y : Type v} [DecidableEq X]

/-- Exchange a table cell with an auxiliary value, retaining the displaced cell value. -/
@[expose]
def swapCoordinate (x : X) : ((X → Y) × Y) ≃ ((X → Y) × Y) where
  toFun p := (Function.update p.1 x p.2, p.1 x)
  invFun p := (Function.update p.1 x p.2, p.1 x)
  left_inv p := by
    apply Prod.ext
    · funext z
      by_cases hz : z = x <;> simp [hz, Function.update]
    · simp
  right_inv p := by
    apply Prod.ext
    · funext z
      by_cases hz : z = x <;> simp [hz, Function.update]
    · simp

/-- Program a finite list of cells, giving its lowest index priority on repeated inputs. -/
@[expose]
def patch : (n : ℕ) → (Fin n → X) → (X → Y) → (Fin n → Y) → X → Y
  | 0, _, H, _ => H
  | n + 1, xs, H, ys => Function.update (patch n (Fin.tail xs) H (Fin.tail ys)) (xs 0) (ys 0)

/-- A permutation that programs the table and retains all displaced values in auxiliary cells. -/
@[expose]
def patchEquiv : (n : ℕ) → (xs : Fin n → X) →
    ((X → Y) × (Fin n → Y)) ≃ ((X → Y) × (Fin n → Y))
  | 0, _ => Equiv.refl _
  | n + 1, xs =>
    let headSwap := (Equiv.prodCongr (Equiv.refl (X → Y))
      (Equiv.prodComm Y (Fin n → Y))).trans (Equiv.prodAssoc (X → Y) (Fin n → Y) Y).symm
    let frontSwap := (Equiv.prodAssoc (X → Y) (Fin n → Y) Y).trans
      ((Equiv.prodCongr (Equiv.refl (X → Y)) (Equiv.prodComm (Fin n → Y) Y)).trans
        (Equiv.prodAssoc (X → Y) Y (Fin n → Y)).symm)
    (Equiv.prodCongr (Equiv.refl (X → Y))
      (Fin.consEquiv (fun _ : Fin (n + 1) ↦ Y)).symm).trans <|
      headSwap.trans <|
        (Equiv.prodCongr (patchEquiv n (Fin.tail xs)) (Equiv.refl Y)).trans <|
          frontSwap.trans <|
            (Equiv.prodCongr (swapCoordinate (xs 0)) (Equiv.refl (Fin n → Y))).trans <|
              frontSwap.symm.trans <|
                headSwap.symm.trans
                  (Equiv.prodCongr (Equiv.refl (X → Y))
                    (Fin.consEquiv (fun _ : Fin (n + 1) ↦ Y)))

/-- The first component of the programming permutation is the head-priority patched table. -/
theorem patchEquiv_fst (n : ℕ) (xs : Fin n → X) (H : X → Y) (ys : Fin n → Y) :
    (patchEquiv n xs (H,ys)).1 = patch n xs H ys := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change Function.update ((patchEquiv n (Fin.tail xs) (H, Fin.tail ys)).1)
      (xs 0) (ys 0) = _
    rw [ih]
    rfl

/-- Programming leaves an untouched input unchanged. -/
theorem patch_eq_of_avoids (n : ℕ) (xs : Fin n → X) (H : X → Y)
    (ys : Fin n → Y) (z : X) (h : ∀ i, xs i ≠ z) :
    patch n xs H ys z = H z := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [patch, Function.update_of_ne (Ne.symm (h 0))]
    exact ih (Fin.tail xs) (Fin.tail ys) (fun i ↦ h i.succ)

/-- With distinct inputs, each programmed cell has its independently chosen value. -/
theorem patch_eq_at_injective (n : ℕ) (xs : Fin n → X) (H : X → Y)
    (ys : Fin n → Y) (h : Function.Injective xs) (i : Fin n) :
    patch n xs H ys (xs i) = ys i := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    cases i using Fin.cases with
    | zero => simp [patch]
    | succ i =>
      have hx : xs i.succ ≠ xs 0 := by
        intro he
        have hi := h he
        simp at hi
      rw [patch, Function.update_of_ne hx]
      exact ih (Fin.tail xs) (Fin.tail ys)
        (fun i j hij ↦ Fin.succ_inj.mp (h hij)) i

/-! ## Prefixes and disagreement inputs -/

/-- Program the first `m` cells, saturating when `m` exceeds the tuple length. -/
@[expose]
def patchPrefix : {n : ℕ} → (X → Y) → (Fin n → X) → (Fin n → Y) → ℕ → X → Y
  | 0, H, _, _, _ => H
  | _ + 1, H, _, _, 0 => H
  | _ + 1, H, xs, ys, m + 1 =>
    Function.update (patchPrefix H (Fin.tail xs) (Fin.tail ys) m) (xs 0) (ys 0)

/-- Programming zero cells leaves the oracle unchanged. -/
@[simp]
theorem patchPrefix_zero {n : ℕ} (H : X → Y) (xs : Fin n → X) (ys : Fin n → Y) :
    patchPrefix H xs ys 0 = H := by cases n <;> rfl

/-- A prefix covering the complete tuple is the full head-priority patch. -/
@[simp]
theorem patchPrefix_full (n : ℕ) (H : X → Y) (xs : Fin n → X) (ys : Fin n → Y) :
    patchPrefix H xs ys n = patch n xs H ys := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [patchPrefix, patch, ih]

/-- A nonempty prefix programs the first cell after its tail prefix. -/
theorem patchPrefix_succ {n : ℕ} (H : X → Y) (xs : Fin (n + 1) → X)
    (ys : Fin (n + 1) → Y) (m : ℕ) :
    patchPrefix H xs ys (m + 1) =
      Function.update (patchPrefix H (Fin.tail xs) (Fin.tail ys) m) (xs 0) (ys 0) := rfl

/-- A prefix depends only on the inputs and values it programs. -/
theorem patchPrefix_congr {n : ℕ} (H : X → Y) {xs xs' : Fin n → X}
    {ys ys' : Fin n → Y} (m : ℕ)
    (hx : ∀ i, i.val < m → xs i = xs' i)
    (hy : ∀ i, i.val < m → ys i = ys' i) :
    patchPrefix H xs ys m = patchPrefix H xs' ys' m := by
  induction n generalizing m with
  | zero => rfl
  | succ n ih =>
    cases m with
    | zero => rfl
    | succ m =>
      rw [patchPrefix_succ, patchPrefix_succ, hx 0 (by simp), hy 0 (by simp)]
      congr 1
      exact ih m (fun i hi ↦ hx i.succ (by simpa using hi))
        (fun i hi ↦ hy i.succ (by simpa using hi))

/-- Inputs whose index has not yet been programmed by a prefix. -/
@[expose]
def tailInputs {n : ℕ} (xs : Fin n → X) (m : ℕ) : Set X :=
  {z | ∃ i, m ≤ i.val ∧ xs i = z}

/-- Full and prefix programming agree away from the remaining input cells.
Earlier entries retain priority even if later entries repeat their inputs. -/
theorem patch_eq_patchPrefix_of_not_mem_tailInputs (n : ℕ) (H : X → Y) (xs : Fin n → X)
    (ys : Fin n → Y) (m : ℕ) (z : X) (hz : z ∉ tailInputs xs m) :
    patch n xs H ys z = patchPrefix H xs ys m z := by
  induction n generalizing m with
  | zero => rfl
  | succ n ih =>
    cases m with
    | zero =>
      exact patch_eq_of_avoids (n + 1) xs H ys z (fun i h ↦ hz ⟨i, Nat.zero_le _, h⟩)
    | succ m =>
      rw [patch, patchPrefix_succ]
      by_cases h : z = xs 0
      · simp [h]
      · rw [Function.update_of_ne h, Function.update_of_ne h]
        apply ih (Fin.tail xs) (Fin.tail ys) m
        rintro ⟨i, hi, he⟩
        exact hz ⟨i.succ, by simpa using hi, he⟩

section Measure
variable [Finite X] [Finite Y] [Nonempty Y]
  [MeasurableSpace Y] [MeasurableSingletonClass Y]

/-- Programming independent uniform values into a uniform table leaves its marginal uniform.
No distinctness assumption on the programmed inputs is required. -/
theorem map_uniform_patch (n : ℕ) (xs : Fin n → X) :
    (uniformOn Set.univ : Measure ((X → Y) × (Fin n → Y))).map
        (fun p ↦ patch n xs p.1 p.2) =
      (uniformOn Set.univ : Measure (X → Y)) := by
  calc
    _ = ((uniformOn Set.univ : Measure ((X → Y) × (Fin n → Y))).map
        (patchEquiv n xs)).map Prod.fst := by
      rw [Measure.map_map Measurable.of_discrete Measurable.of_discrete]
      congr 1
      funext p
      exact (patchEquiv_fst n xs p.1 p.2).symm
    _ = ((uniformOn Set.univ : Measure ((X → Y) × (Fin n → Y)))).map Prod.fst := by
      rw [uniformOn_univ_map_equiv]
    _ = _ := by rw [uniformOn_univ_prod, Measure.map_fst_prod, measure_univ, one_smul]
end Measure

section Mask
variable {G : Type*} [AddGroup G]

/-- Add the following hidden vertex to each mask value; subtraction is the inverse map. -/
@[expose]
def maskEquiv {n : ℕ} (xs : Fin (n + 1) → G) : (Fin n → G) ≃ (Fin n → G) where
  toFun ys i := ys i + xs i.succ
  invFun ms i := ms i - xs i.succ
  left_inv ys := by funext i; simp
  right_inv ms := by funext i; simp

end Mask

/-! ## Fresh chain inputs -/

section FutureInputs

variable {R : Type*} [Fintype R] [Nonempty R]
  [MeasurableSpace R] [MeasurableSingletonClass R]
open scoped Classical in
/-- Future chain inputs have weighted incidence at most the number of remaining links
divided by the answer-space cardinality. The final hidden endpoint is excluded
from the input set. -/
theorem future_hit_sum_le (q h : ℕ) (hh : h ≤ q) (z : R) :
    (∑ xs : Fin (q + 2) → R,
      Set.indicator (tailInputs (fun i : Fin (q + 1) ↦ xs i.castSucc) (h + 1))
        (fun _ ↦ (Fintype.card (Fin (q + 2) → R) : ℝ)⁻¹) z) ≤
      ((q - h : ℕ) : ℝ) / Fintype.card R := by
  let : DecidableEq R := Classical.decEq R
  let s : Finset (Fin (q + 2)) :=
    Finset.Ico ⟨h + 1, by omega⟩ (Fin.last (q + 1))
  have hcard : s.card = q - h := by
    simp only [s, Fin.card_Ico, Fin.val_last]
    omega
  have he (xs : Fin (q + 2) → R) :
      (∃ i ∈ s, xs i = z) ↔
        z ∈ tailInputs (fun i : Fin (q + 1) ↦ xs i.castSucc) (h + 1) := by
    constructor
    · rintro ⟨i, hi, he⟩
      have hi' : (⟨h + 1, by omega⟩ : Fin (q + 2)) ≤ i ∧
          i < Fin.last (q + 1) := Finset.mem_Ico.mp hi
      exact ⟨⟨i.val, hi'.2⟩, hi'.1, he⟩
    · rintro ⟨i, hi, he⟩
      exact ⟨i.castSucc, Finset.mem_Ico.mpr ⟨hi, i.isLt⟩, he⟩
  have hb := uniform_hit_sum_le s z
  rw [hcard] at hb
  convert hb using 1
  apply Finset.sum_congr rfl
  intro xs _
  by_cases hx : ∃ i ∈ s, xs i = z
  · have hz := (he xs).mp hx
    simp [hx, hz]
  · have hz := mt (he xs).mpr hx
    simp [hx, hz]

end FutureInputs

/-! ## Joint masked-chain coupling -/

section JointCoupling

variable {X Y : Type*} [DecidableEq X] [Finite X] [Finite Y] [Nonempty Y]
  [MeasurableSpace Y] [MeasurableSingletonClass Y]

/-- A uniform table can be replaced by a patched uniform table inside any nonnegative observer. -/
theorem lintegral_uniform_patch (n : ℕ) (xs : Fin n → X) (f : (X → Y) → ENNReal) :
    (∫⁻ H, ∫⁻ ys, f (patch n xs H ys)
      ∂(uniformOn Set.univ : Measure (Fin n → Y))
      ∂(uniformOn Set.univ : Measure (X → Y))) =
      ∫⁻ H, f H ∂(uniformOn Set.univ : Measure (X → Y)) := by
  have h := congrArg (fun μ : Measure (X → Y) ↦ ∫⁻ H, f H ∂μ) (map_uniform_patch n xs)
  rw [lintegral_map Measurable.of_discrete Measurable.of_discrete,
    uniformOn_univ_prod, lintegral_prod _ Measurable.of_discrete.aemeasurable] at h
  exact h

variable {G : Type*} [AddGroup G]

/-- Publish each queried oracle value masked by the following hidden vertex. -/
@[expose]
def oracleMasks {n : ℕ} (H : G → G) (xs : Fin (n + 1) → G) : Fin n → G :=
  fun i ↦ H (xs i.castSucc) + xs i.succ

/-- On distinct hidden vertices, the published masks are the independent programming values
translated by the following vertices. -/
theorem oracleMasks_patch_of_injective [DecidableEq G] (n : ℕ) (H : G → G)
    (xs : Fin (n + 1) → G) (ys : Fin n → G) (hx : Function.Injective xs) :
    oracleMasks (patch n (fun i ↦ xs i.castSucc) H ys) xs = maskEquiv xs ys := by
  funext i
  change patch n (fun j ↦ xs j.castSucc) H ys (xs i.castSucc) + xs i.succ =
    ys i + xs i.succ
  exact congrArg (fun v ↦ v + xs i.succ)
    (patch_eq_at_injective n (fun j ↦ xs j.castSucc) H ys
      (fun a b hab ↦ Fin.castSucc_injective n (hx hab)) i)

variable [DecidableEq G] [MeasurableSpace G] [MeasurableSingletonClass G]

omit [DecidableEq G] in
/-- Move independent randomness from programming values to published masks, retaining both
the programming values and the full hidden vertex tuple in the observer. -/
theorem lintegral_maskEquiv [Finite G] {n : ℕ} (xs : Fin (n + 1) → G)
    (f : (Fin n → G) → (Fin n → G) → ENNReal) :
    (∫⁻ ys, f ys (maskEquiv xs ys) ∂(uniformOn Set.univ : Measure (Fin n → G))) =
      ∫⁻ masks, f ((maskEquiv xs).symm masks) masks
        ∂(uniformOn Set.univ : Measure (Fin n → G)) := by
  have h := congrArg (fun μ : Measure (Fin n → G) ↦
    ∫⁻ masks, f ((maskEquiv xs).symm masks) masks ∂μ)
    (uniformOn_univ_map_equiv (maskEquiv xs))
  rw [lintegral_map Measurable.of_discrete Measurable.of_discrete] at h
  simpa using h

private theorem lintegral_le_add_of_eq_off {A : Type*} [Finite A]
    [MeasurableSpace A] [MeasurableSingletonClass A] (μ : Measure A)
    (f g : A → ENNReal) (bad : Set A) (hf : ∀ a, f a ≤ 1)
    (hgood : ∀ a, a ∉ bad → f a = g a) :
    (∫⁻ a, f a ∂μ) ≤ (∫⁻ a, g a ∂μ) + μ bad := by
  calc
    _ ≤ ∫⁻ a, g a + bad.indicator 1 a ∂μ := by
      apply lintegral_mono
      intro a
      by_cases ha : a ∈ bad
      · simpa [ha] using (hf a).trans (le_add_left le_rfl : (1 : ENNReal) ≤ g a + 1)
      · simp [ha, hgood a ha]
    _ = _ := by
      rw [lintegral_add_left Measurable.of_discrete,
        lintegral_indicator_one MeasurableSet.of_discrete]

open scoped Classical in
/-- Compare oracle-derived masks with independent programmed masks, charging vertex collisions.
The observer retains the oracle and complete hidden vertices. After programming, the mask
choices agree outside collisions, preserving events that check the hidden endpoint. -/
theorem real_le_patched_add_collision [Fintype G] (n : ℕ)
    (F : (G → G) → (Fin (n + 1) → G) → (Fin n → G) → ENNReal)
    (hF : ∀ H xs masks, F H xs masks ≤ 1) :
    (∫⁻ xs, ∫⁻ H, F H xs (oracleMasks H xs)
        ∂(uniformOn Set.univ : Measure (G → G))
        ∂(uniformOn Set.univ : Measure (Fin (n + 1) → G))) ≤
      (∫⁻ xs, ∫⁻ H, ∫⁻ ys,
          F (patch n (fun i ↦ xs i.castSucc) H ys) xs (maskEquiv xs ys)
          ∂(uniformOn Set.univ : Measure (Fin n → G))
          ∂(uniformOn Set.univ : Measure (G → G))
          ∂(uniformOn Set.univ : Measure (Fin (n + 1) → G))) +
        (((n + 1).choose 2 : ℕ) : ENNReal) / Fintype.card G := by
  refine (lintegral_le_add_of_eq_off (uniformOn Set.univ) _ _
    {xs | ¬ Function.Injective xs} ?_ ?_).trans
      (add_le_add le_rfl (uniform_collision_le (R := G) (n + 1)))
  · intro xs
    calc
      _ ≤ ∫⁻ _H, (1 : ENNReal) ∂(uniformOn Set.univ : Measure (G → G)) :=
        lintegral_mono fun H ↦ hF H xs (oracleMasks H xs)
      _ = 1 := by simp
  · intro xs hx
    have hinj : Function.Injective xs := not_not.mp hx
    rw [← lintegral_uniform_patch n (fun i ↦ xs i.castSucc)
      (fun H ↦ F H xs (oracleMasks H xs))]
    congr 1
    funext H
    congr 1
    funext ys
    rw [oracleMasks_patch_of_injective n H xs ys hinj]

open scoped Classical in
/-- Sample public masks independently before deriving the programming values.
The real oracle-derived-mask experiment is bounded by the independently masked experiment
plus the vertex-collision probability.
The bounded observer retains the oracle, all hidden vertices, and the published masks. -/
theorem real_le_maskFirst_add_collision [Fintype G] (n : ℕ)
    (F : (G → G) → (Fin (n + 1) → G) → (Fin n → G) → ENNReal)
    (hF : ∀ H xs masks, F H xs masks ≤ 1) :
    (∫⁻ xs, ∫⁻ H, F H xs (oracleMasks H xs)
        ∂(uniformOn Set.univ : Measure (G → G))
        ∂(uniformOn Set.univ : Measure (Fin (n + 1) → G))) ≤
      (∫⁻ xs, ∫⁻ H, ∫⁻ masks,
          F (patch n (fun i ↦ xs i.castSucc) H ((maskEquiv xs).symm masks)) xs masks
          ∂(uniformOn Set.univ : Measure (Fin n → G))
          ∂(uniformOn Set.univ : Measure (G → G))
          ∂(uniformOn Set.univ : Measure (Fin (n + 1) → G))) +
        (((n + 1).choose 2 : ℕ) : ENNReal) / Fintype.card G := by
  refine (real_le_patched_add_collision n F hF).trans_eq ?_
  congr 1
  congr 1
  funext xs
  congr 1
  funext H
  exact lintegral_maskEquiv xs (fun ys masks ↦
    F (patch n (fun i ↦ xs i.castSucc) H ys) xs masks)

end JointCoupling

end Quantum.MaskedChain
