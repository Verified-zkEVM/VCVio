/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kobi Gurkan, Quang Dao
-/

module
public import VCVio.CryptoFoundations.GroupModel.LinearFunctional.Interaction
public import VCVio.CryptoFoundations.GroupModel.LinearFunctional.LazyExecution
public import VCVio.CryptoFoundations.GroupModel.LinearFunctional.Masking
public import VCVio.CryptoFoundations.GroupModel.LinearFunctional.FiniteLabels
import Mathlib.Algebra.Module.Pi

/-! # Linear functionals extracted from chronological replies

This follows Gurkan's linear-functional proof of BLS security in the algebraic group model
of Fuchsbauer, Kiltz and Loss (CRYPTO 2018). The first two coefficient positions explain a
generator and public key; subsequent positions correspond to chronological reply occurrences.
The signing functional has a separate constant for the received public-key coefficient.
-/

public section

open GroupModel.Interaction

namespace GroupModel.LinearFunctional

/-- The constant public-key coefficient and signing-reply functional extracted from a trace.
The label weights may describe any linear query family. -/
@[expose] def traceFunctional {F M ι : Type} [Semiring F]
    (w : M → ι → F) (coeff : List F) (tr : Transcript M) : F × (ι → F) :=
  evaluate coeff ([(0, 0), (1, 0)] ++
    tr.map (fun q => if q.1 then (0, w q.2) else (0, 0)))

private def tableEval {F ι : Type} [CommSemiring F] [Fintype ι]
    (ρ : ι → F) : (ι → F) →ₗ[F] F := ∑ i, ρ i • LinearMap.proj i

private theorem tableEval_apply {F ι : Type} [CommSemiring F] [Fintype ι]
    (ρ v : ι → F) : tableEval ρ v = ∑ i, v i * ρ i := by
  simp [tableEval, mul_comm]

/-- A finite table can be interpreted before or after chronological coefficient evaluation.
The input functionals and their initial positions are arbitrary. -/
theorem evaluate_weighted_table {F ι : Type} [CommSemiring F] [Fintype ι]
    (coeff : List F) (inputs : List (ι → F)) (ρ : ι → F) :
    evaluate coeff (inputs.map fun v => ∑ i, v i * ρ i) =
      ∑ i, evaluate coeff inputs i * ρ i := by
  have hf : (⇑(tableEval ρ)) = (fun v => ∑ i, v i * ρ i) :=
    funext (tableEval_apply ρ)
  simpa only [hf] using evaluate_map (tableEval ρ) coeff inputs

/-- Finite weighted sums commute with evaluation over an arbitrary list of input labels. -/
theorem evaluate_weighted_map {F ι X : Type} [CommSemiring F] [Fintype ι]
    (coeff : List F) (inputs : List X) (w : X → ι → F) (ρ : ι → F) :
    evaluate coeff (inputs.map fun x => ∑ i, w x i * ρ i) =
      ∑ i, evaluate coeff (inputs.map fun x => w x i) * ρ i := by
  simp only [evaluate_map_eq_sum, smul_eq_mul, Finset.mul_sum, Finset.sum_mul, mul_assoc]
  exact Finset.sum_comm

/-- Interpreting the signing functional by a scalar table gives the good reduction's linear
coefficient, including the coefficient on the received public-key point. -/
theorem traceFunctional_good {F M ι : Type} [CommSemiring F] [Fintype ι]
    (w : M → ι → F) (coeff : List F) (tr : Transcript M) (ρ : ι → F) :
    (evaluate coeff ([((1 : F), (0 : F)), (0, 1)] ++ tr.map (fun q =>
      if q.1 then (0, ∑ i, w q.2 i * ρ i) else (∑ i, w q.2 i * ρ i, 0)))).2 =
      (traceFunctional w coeff tr).1 + ∑ i, (traceFunctional w coeff tr).2 i * ρ i := by
  let f : (F × (ι → F)) →ₗ[F] F := LinearMap.fst F F (ι → F) +
    (tableEval ρ).comp (LinearMap.snd F F (ι → F))
  have h := evaluate_map f coeff
    ([(0, 0), (1, 0)] ++ tr.map (fun q => if q.1 then (0, w q.2) else (0, 0)))
  have h' := evaluate_map (LinearMap.snd F F F) coeff
    ([((1 : F), (0 : F)), (0, 1)] ++ tr.map (fun q =>
      if q.1 then (0, ∑ i, w q.2 i * ρ i) else (∑ i, w q.2 i * ρ i, 0)))
  simp only [LinearMap.snd_apply] at h'
  rw [← h']
  have hf (z : F × (ι → F)) : f z = z.1 + ∑ i, z.2 i * ρ i := by
    simp [f, tableEval_apply]
  rw [← hf]
  unfold traceFunctional
  rw [← h]
  congr 1
  simp only [List.map_append, List.map_cons, List.map_nil, List.map_map, hf,
    LinearMap.snd_apply, Pi.zero_apply, zero_mul, Finset.sum_const_zero, add_zero]
  congr 1
  apply List.map_congr_left
  intro q _
  cases hq : q.1 <;> simp [hq, f, tableEval_apply]

/-- Interpreting the same functional by two mask tables gives the bad reduction's slope and
constant. The public-key coefficient contributes only to the constant. -/
theorem traceFunctional_bad {F M ι : Type} [CommSemiring F] [Fintype ι]
    (w : M → ι → F) (coeff : List F) (tr : Transcript M) (a b : ι → F) :
    evaluate coeff ([(0, 0), (0, 1)] ++ tr.map (fun q =>
      if q.1 then (∑ i, w q.2 i * a i, ∑ i, w q.2 i * b i) else (0, 0))) =
      (∑ i, (traceFunctional w coeff tr).2 i * a i,
        (traceFunctional w coeff tr).1 + ∑ i, (traceFunctional w coeff tr).2 i * b i) := by
  let f : (F × (ι → F)) →ₗ[F] F × F :=
    ((tableEval a).comp (LinearMap.snd F F (ι → F))).prod
      (LinearMap.fst F F (ι → F) + (tableEval b).comp (LinearMap.snd F F (ι → F)))
  have h := evaluate_map f coeff
    ([(0, 0), (1, 0)] ++ tr.map (fun q => if q.1 then (0, w q.2) else (0, 0)))
  have hf (z : F × (ι → F)) : f z =
      (∑ i, z.2 i * a i, z.1 + ∑ i, z.2 i * b i) := by
    simp [f, tableEval_apply]
  rw [← hf]
  unfold traceFunctional
  rw [← h]
  congr 1
  simp only [List.map_append, List.map_cons, List.map_nil, List.map_map, hf,
    Pi.zero_apply, zero_mul, Finset.sum_const_zero, add_zero]
  congr 1
  apply List.map_congr_left
  intro q _
  cases hq : q.1 <;> simp [hq, f, tableEval_apply]

private theorem evaluate_eq_zero {F V : Type} [Semiring F]
    [AddCommMonoid V] [Module F V] (coeff : List F) (inputs : List V)
    (h : ∀ v ∈ inputs, v = 0) : evaluate coeff inputs = 0 := by
  simp only [evaluate, List.mapIdx_eq_ofFn, List.sum_ofFn]
  apply Finset.sum_eq_zero
  intro i _
  rw [h _ (List.get_mem inputs i)]
  exact smul_zero _

/-- A coordinate absent from every signing weight has zero coefficient in the extracted
signing functional, independently of all adaptive coefficient choices. -/
theorem traceFunctional_apply_eq_zero {F M ι : Type} [Semiring F]
    (w : M → ι → F) (coeff : List F) (tr : Transcript M) (j : ι)
    (h : ∀ q ∈ tr, q.1 = true → w q.2 j = 0) :
    (traceFunctional w coeff tr).2 j = 0 := by
  let f : (F × (ι → F)) →ₗ[F] F :=
    (LinearMap.proj j).comp (LinearMap.snd F F (ι → F))
  have he := evaluate_map f coeff
    ([(0, 0), (1, 0)] ++ tr.map (fun q => if q.1 then (0, w q.2) else (0, 0)))
  have hf (v : F × (ι → F)) : f v = v.2 j := rfl
  rw [hf] at he
  unfold traceFunctional
  rw [← he]
  apply evaluate_eq_zero
  intro v hv
  simp only [List.mem_map] at hv
  obtain ⟨x, hx, rfl⟩ := hv
  rcases List.mem_append.mp hx with hx | hx
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl <;> simp [hf]
  · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hx
    cases hb : q.1 <;> simp [hb, hf, h q hq]

/-- Coordinate weights for labels in a finite proof cover. -/
@[expose] def labelWeight {F M : Type} [Zero F] [One F] [DecidableEq M]
    (S : Finset M) (m : M) (i : S) : F := if m = i.val then 1 else 0

/-- A coordinate lookup is the weighted evaluation of a finite table, with zero outside it. -/
theorem sum_labelWeight_mul {F M : Type} [Semiring F] [DecidableEq M]
    (S : Finset M) (m : M) (ρ : S → F) :
    ∑ i, labelWeight S m i * ρ i = extendTable S 0 ρ m := by
  classical
  by_cases hm : m ∈ S
  · rw [extendTable, dite_eq_left hm]
    rw [Finset.sum_eq_single (⟨m, hm⟩ : S)]
    · simp [labelWeight]
    · intro i _ hi
      have hne : m ≠ i.val := by
        intro h
        exact hi (Subtype.ext h.symm)
      simp [labelWeight, hne]
    · simp
  · have hn : ∀ i : S, m ≠ i.val := fun i h => hm (h ▸ i.property)
    simp [labelWeight, hn, extendTable, hm]

end GroupModel.LinearFunctional
