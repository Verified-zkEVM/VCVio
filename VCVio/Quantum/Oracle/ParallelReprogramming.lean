/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import VCVio.Quantum.Oracle.Parallel
public import QuantumFoundations.MatrixMap.Comparison
public import QuantumFoundations.MatrixMap.Conjugation

/-!
# Reprogramming one parallel oracle round

The difference of two parallel additive oracles is supported on the union of query slots
whose inputs belong to the disagreement set. Its squared Kraus weight is at most four times
the input weight on this union. Repeated inputs require no distinctness assumption.

A common completely positive trace-nonincreasing finishing map may follow either oracle.
It can depend on fixed classical challenge data, and the input may include an arbitrary
spectator register. Thus conditioning on hidden points retains their correlation with the
final verification event; an adversary-only marginal comparison is unnecessary.

## References

* C. Zalka, Grover's quantum searching algorithm is optimal, arXiv:quant-ph/9711070v2,
  §4, equations 23–26.
* Afshar et al., On the (Im)possibility of Time-Lock Puzzles in the Quantum Random Oracle
  Model, §5, Lemma 5.4.
-/

public section

open Matrix
open scoped ENNReal ComplexOrder Kronecker Matrix.Norms.L2Operator

namespace Quantum

private theorem sub_kronecker_eq {A B C D : Type*} (U V : Matrix A B ℂ)
    (W : Matrix C D ℂ) :
    (U - V) ⊗ₖ W = U ⊗ₖ W - V ⊗ₖ W := by
  classical
  ext ⟨a, c⟩ ⟨b, d⟩
  simp [kroneckerMap_apply, sub_mul]

open Classical in
private theorem sum_union_incidence_le {X : Type} {Ω : Type*} [Fintype Ω]
    (w : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω) (S : Ω → Set X) (δ : ℝ)
    (hS : ∀ x, ∑ ω, (if x ∈ S ω then w ω else 0) ≤ δ)
    (k : ℕ) (z : Fin k → X) :
    ∑ ω, (if ∃ i, z i ∈ S ω then w ω else 0) ≤ k * δ := by
  classical
  calc
    _ ≤ ∑ ω, ∑ i : Fin k, if z i ∈ S ω then w ω else 0 := by
      apply Finset.sum_le_sum
      intro ω _
      split_ifs with hh
      · obtain ⟨i, hi⟩ := hh
        simpa only [hi, ite_true] using
          (Finset.single_le_sum (f := fun j : Fin k ↦ if z j ∈ S ω then w ω else 0)
            (fun j _ ↦ by split_ifs <;> first | exact hw ω | exact le_rfl) (Finset.mem_univ i))
      · exact Finset.sum_nonneg (fun i _ ↦ by split_ifs <;> first | exact hw ω | exact le_rfl)
    _ = ∑ i : Fin k, ∑ ω, if z i ∈ S ω then w ω else 0 := Finset.sum_comm
    _ ≤ ∑ _i : Fin k, δ := Finset.sum_le_sum fun i _ ↦ hS (z i)
    _ = k * δ := by simp


section projectors

variable {X Y : Type} [DecidableEq X] [DecidableEq Y]

open Classical in
/-- The basis projector onto tuples with at least one query input in `S`. -/
@[expose]
noncomputable def parallelInputProjector (k : ℕ) (S : Set X) :
    Matrix (Fin k → X × Y) (Fin k → X × Y) ℂ :=
  Matrix.diagonal fun z ↦ if ∃ i, (z i).1 ∈ S then 1 else 0

/-- The query-union projector is Hermitian. -/
theorem parallelInputProjector_conjTranspose (k : ℕ) (S : Set X) :
    (parallelInputProjector (Y := Y) k S)ᴴ = parallelInputProjector k S := by
  classical
  simp only [parallelInputProjector, diagonal_conjTranspose]
  congr 1
  funext z
  split_ifs <;> simp_all

variable [Fintype X] [Fintype Y]

/-- Projecting onto the query union twice is the same as projecting once. -/
theorem parallelInputProjector_mul_self (k : ℕ) (S : Set X) :
    parallelInputProjector (Y := Y) k S * parallelInputProjector k S =
      parallelInputProjector k S := by
  classical
  simp only [parallelInputProjector, diagonal_mul_diagonal]
  congr 1
  funext z
  split_ifs <;> simp_all

open Classical in
/-- The weight of the query union is the sum of the selected diagonal weights. -/
theorem re_trace_conj_parallelInputProjector (k : ℕ) (S : Set X)
    (ρ : Matrix (Fin k → X × Y) (Fin k → X × Y) ℂ) :
    (MatrixMap.conj (parallelInputProjector (Y := Y) k S) ρ).trace.re =
      ∑ z, if ∃ i, (z i).1 ∈ S then (ρ z z).re else 0 := by
  classical
  rw [MatrixMap.conj_apply, parallelInputProjector_conjTranspose]
  simp only [parallelInputProjector,
    Matrix.trace, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro z _
  split_ifs <;> simp_all

open Classical in
private theorem sum_hit_weight_le (k : ℕ) (z : Fin k → X) {r : ℝ} (hr : 0 ≤ r) :
    ∑ y : X, (if ∃ i, z i = y then r else 0) ≤ k * r := by
  classical
  calc
    _ ≤ ∑ y : X, ∑ i : Fin k, if z i = y then r else 0 := by
      apply Finset.sum_le_sum
      intro y _
      split_ifs with hy
      · obtain ⟨i, hi⟩ := hy
        simpa only [hi, ite_true] using
          (Finset.single_le_sum (f := fun j : Fin k ↦ if z j = y then r else 0)
            (fun j _ ↦ by split_ifs <;> positivity) (Finset.mem_univ i))
      · exact Finset.sum_nonneg (fun i _ ↦ by split_ifs <;> positivity)
    _ = k * r := by
      rw [Finset.sum_comm]
      simp

/-- Summing the query-union weights over all possible single hidden inputs costs at most
one input trace per slot, including repeated inputs and zero-width tuples. -/
theorem sum_re_trace_conj_parallelInputProjector_singleton_le (k : ℕ)
    {ρ : Matrix (Fin k → X × Y) (Fin k → X × Y) ℂ} (hρ : ρ.PosSemidef) :
    ∑ y : X, (MatrixMap.conj
      (parallelInputProjector (Y := Y) k {y}) ρ).trace.re ≤ k * ρ.trace.re := by
  classical
  simp only [re_trace_conj_parallelInputProjector, Set.mem_singleton_iff]
  rw [Finset.sum_comm, Matrix.trace, Complex.re_sum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro z _
  exact sum_hit_weight_le k (fun i ↦ (z i).1) (Complex.nonneg_iff.mp hρ.diag_nonneg).1

/-- The singleton-union mass bound retains an arbitrary spectator register, including
private quantum memory or a classical challenge register. -/
theorem sum_re_trace_conj_parallelInputProjector_singleton_frame_le
    {E : Type*} [Fintype E] [DecidableEq E] (k : ℕ)
    {ρ : Matrix ((Fin k → X × Y) × E) ((Fin k → X × Y) × E) ℂ}
    (hρ : ρ.PosSemidef) :
    ∑ y : X, (MatrixMap.conj (parallelInputProjector (Y := Y) k {y} ⊗ₖ
      (1 : Matrix E E ℂ)) ρ).trace.re ≤ k * ρ.trace.re := by
  classical
  simp_rw [MatrixMap.trace_conj_kronecker_one_apply]
  exact (sum_re_trace_conj_parallelInputProjector_singleton_le k hρ.traceRight).trans_eq
    (by rw [MatrixMap.trace_traceRight])


/-- If every fixed input lies in a sampled disagreement set with weighted incidence at most
`δ`, a width-`k` query has expected union weight at most `k * δ` times the input trace.
The same input operator is used for every sampled set: it is independent of the sampled
challenge. The nonnegative weights need not be normalized. -/
theorem sum_mul_re_trace_conj_parallelInputProjector_le {Ω : Type*} [Fintype Ω]
    (w : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω) (S : Ω → Set X) (δ : ℝ)
    (hS : ∀ x, ∑ ω, Set.indicator (S ω) (fun _ ↦ w ω) x ≤ δ) (k : ℕ)
    {ρ : Matrix (Fin k → X × Y) (Fin k → X × Y) ℂ} (hρ : ρ.PosSemidef) :
    ∑ ω, w ω * (MatrixMap.conj (parallelInputProjector (Y := Y) k (S ω)) ρ).trace.re ≤
      k * δ * ρ.trace.re := by
  classical
  simp only [re_trace_conj_parallelInputProjector, Finset.mul_sum]
  rw [Finset.sum_comm, Matrix.trace, Complex.re_sum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro z _
  have hz := sum_union_incidence_le w hw S δ
    (fun x ↦ by simpa only [Set.indicator_apply] using hS x) k (fun i ↦ (z i).1)
  have hn : 0 ≤ (ρ z z).re := (Complex.nonneg_iff.mp hρ.diag_nonneg).1
  calc
    _ = (∑ ω, if ∃ i, (z i).1 ∈ S ω then w ω else 0) * (ρ z z).re := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro ω _
      split_ifs <;> simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hz hn

/-- The expected query-union mass bound with an arbitrary spectator. A pointwise incidence
bound `δ = s / card X` gives the usual `k * s / card X` estimate for hidden reprogramming
points independent of the pre-query state. -/
theorem sum_mul_re_trace_conj_parallelInputProjector_frame_le
    {Ω E : Type*} [Fintype Ω] [Fintype E] [DecidableEq E]
    (w : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω) (S : Ω → Set X) (δ : ℝ)
    (hS : ∀ x, ∑ ω, Set.indicator (S ω) (fun _ ↦ w ω) x ≤ δ) (k : ℕ)
    {ρ : Matrix ((Fin k → X × Y) × E) ((Fin k → X × Y) × E) ℂ}
    (hρ : ρ.PosSemidef) :
    ∑ ω, w ω * (MatrixMap.conj (parallelInputProjector (Y := Y) k (S ω) ⊗ₖ
      (1 : Matrix E E ℂ)) ρ).trace.re ≤ k * δ * ρ.trace.re := by
  classical
  simp_rw [MatrixMap.trace_conj_kronecker_one_apply]
  exact (sum_mul_re_trace_conj_parallelInputProjector_le w hw S δ hS k hρ.traceRight).trans_eq
    (by rw [MatrixMap.trace_traceRight])

end projectors

section disagreement

variable {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [AddCommGroup Y]

/-- Two oracle functions agreeing outside `S` have parallel-unitary difference supported
on tuples with a query in `S`. -/
theorem parallelOracleUnitary_sub_eq_mul_projector (H H' : X → Y) (k : ℕ) (S : Set X)
    (h : ∀ x ∉ S, H x = H' x) :
    parallelOracleUnitary H k - parallelOracleUnitary H' k =
      (parallelOracleUnitary H k - parallelOracleUnitary H' k) *
        parallelInputProjector (Y := Y) k S := by
  classical
  ext a b
  simp only [Matrix.sub_apply, Matrix.mul_diagonal, parallelInputProjector]
  by_cases hb : ∃ i, (b i).1 ∈ S
  · simp [hb]
  · have he : parallelOracleEquiv H k b = parallelOracleEquiv H' k b := by
      ext i <;> simp [h _ (fun hi ↦ hb ⟨i, hi⟩)]
    simp only [parallelOracleUnitary, basisMatrix, Matrix.of_apply]
    simp [hb, he]

variable {E : Type*} [Fintype E] [DecidableEq E]

/-- A parallel-round disagreement, with any spectator register, has squared Kraus weight
at most four times its input weight on the union of slots querying `S`. -/
theorem re_trace_parallel_disagreement_le (H H' : X → Y) (k : ℕ) (S : Set X)
    (h : ∀ x ∉ S, H x = H' x)
    {ρ : Matrix ((Fin k → X × Y) × E) ((Fin k → X × Y) × E) ℂ}
    (hρ : ρ.PosSemidef) :
    (MatrixMap.conj ((parallelOracleUnitary H k - parallelOracleUnitary H' k) ⊗ₖ
      (1 : Matrix E E ℂ)) ρ).trace.re ≤
      4 * (MatrixMap.conj (parallelInputProjector (Y := Y) k S ⊗ₖ
        (1 : Matrix E E ℂ)) ρ).trace.re := by
  classical
  let U := parallelOracleUnitary H k ⊗ₖ (1 : Matrix E E ℂ)
  let V := parallelOracleUnitary H' k ⊗ₖ (1 : Matrix E E ℂ)
  let P := parallelInputProjector (Y := Y) k S ⊗ₖ (1 : Matrix E E ℂ)
  have hi (G : X → Y) :
      (parallelOracleUnitary G k ⊗ₖ (1 : Matrix E E ℂ))ᴴ *
        (parallelOracleUnitary G k ⊗ₖ (1 : Matrix E E ℂ)) = 1 := by
    have hG : (parallelOracleUnitary G k)ᴴ * parallelOracleUnitary G k = 1 :=
      Matrix.mem_unitaryGroup_iff'.mp (parallelOracleUnitary_mem_unitaryGroup G k)
    rw [conjTranspose_kronecker, conjTranspose_one, ← mul_kronecker_mul, hG,
      Matrix.one_mul, one_kronecker_one]
  have hU : ‖U‖ ≤ 1 := Matrix.l2_opNorm_le_one_of_conjTranspose_mul_self (hi H)
  have hV : ‖V‖ ≤ 1 := Matrix.l2_opNorm_le_one_of_conjTranspose_mul_self (hi H')
  have hUV : ‖U - V‖ ≤ 2 := (norm_sub_le _ _).trans (by linarith)
  have hs : U - V = (U - V) * P := by
    dsimp [U, V, P]
    rw [← sub_kronecker_eq, ← mul_kronecker_mul, Matrix.one_mul,
      ← parallelOracleUnitary_sub_eq_mul_projector H H' k S h]
  have hPρ := hρ.mul_mul_conjTranspose_same P
  rw [sub_kronecker_eq]
  change (MatrixMap.conj (U - V) ρ).trace.re ≤ 4 * (MatrixMap.conj P ρ).trace.re
  calc
    _ = (MatrixMap.conj (U - V) (MatrixMap.conj P ρ)).trace.re := by
      conv_lhs => rw [hs]
      rw [MatrixMap.conj_mul, LinearMap.comp_apply]
    _ ≤ ‖U - V‖ ^ 2 * (MatrixMap.conj P ρ).trace.re :=
      MatrixMap.re_trace_conj_le _ hPρ
    _ ≤ _ := by
      have ht : 0 ≤ (MatrixMap.conj P ρ).trace.re := hPρ.trace_re_nonneg
      gcongr
      nlinarith [norm_nonneg (U - V)]

/-- Reprogramming one parallel round changes the square root of the acceptance weight by
at most the square root of four times the disagreement-union weight. The common finishing
map can include all subsequent oracle-dependent computation after fixing the challenge data. -/
theorem rpow_inv_two_parallel_reprogramming_le {C : Type*} [Fintype C]
    (H H' : X → Y) (k : ℕ) (S : Set X) (h : ∀ x ∉ S, H x = H' x)
    (Φ : MatrixMap ((Fin k → X × Y) × E) C) (hΦ : Φ.IsCP) (hT : Φ.IsTNI)
    {ρ : Matrix ((Fin k → X × Y) × E) ((Fin k → X × Y) × E) ℂ}
    (hρ : ρ.PosSemidef) :
    ENNReal.ofReal (Φ (MatrixMap.conj (parallelOracleUnitary H k ⊗ₖ
      (1 : Matrix E E ℂ)) ρ)).trace.re ^ (2⁻¹ : ℝ) ≤
      ENNReal.ofReal (Φ (MatrixMap.conj (parallelOracleUnitary H' k ⊗ₖ
        (1 : Matrix E E ℂ)) ρ)).trace.re ^ (2⁻¹ : ℝ) +
      (4 * ENNReal.ofReal (MatrixMap.conj
        (parallelInputProjector (Y := Y) k S ⊗ₖ (1 : Matrix E E ℂ)) ρ).trace.re) ^
          (2⁻¹ : ℝ) := by
  classical
  have hf := MatrixMap.finish_comparison (fun _ : Unit ↦ Φ) (fun _ ↦ hΦ) (fun _ ↦ hT)
    hρ (fun _ ↦ parallelOracleUnitary H k ⊗ₖ (1 : Matrix E E ℂ))
      (fun _ ↦ parallelOracleUnitary H' k ⊗ₖ (1 : Matrix E E ℂ))
  simp only [tsum_fintype, Finset.univ_unique, Finset.sum_singleton] at hf
  refine hf.trans (add_le_add le_rfl (ENNReal.rpow_le_rpow ?_ (by norm_num)))
  rw [← sub_kronecker_eq, ← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_mul (by norm_num)]
  exact ENNReal.ofReal_le_ofReal (re_trace_parallel_disagreement_le H H' k S h hρ)

end disagreement

end Quantum
