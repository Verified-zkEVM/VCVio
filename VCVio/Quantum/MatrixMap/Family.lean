/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import Mathlib.Analysis.Normed.Group.InfiniteSum
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import VCVio.Quantum.MatrixMap

/-!
# Summable families of matrix maps

The branches of a quantum instrument form a family of completely positive maps indexed by the
classical outcomes, possibly infinitely many. This file develops such families in finite
dimension, with no countability or finiteness assumption on the index type.

The key fact is analytic. Let `Φ i` be completely positive maps with a common codomain whose
finite partial sums are trace nonincreasing. On a positive semidefinite input `ρ` the matrices
`Φ i ρ` are positive semidefinite, the norm of every entry of such a matrix is at most its trace,
and the traces of finitely many of them sum to at most the trace of `ρ`. So `i ↦ Φ i ρ` is summable,
entry by entry. Positive semidefinite matrices span all matrices, so the family is summable on
every input. For outcome-dependent codomains, `summable_trace_apply` supplies a summable family
of scalar traces. Everything is stated pointwise on matrices, which carry their product topology;
no topology is put on spaces of linear maps.

## Main definitions

* `Quantum.MatrixMap.IsCPTNIFamily Φ`: every member is completely positive, and on positive
  semidefinite inputs the traces of the members over every finite set of labels sum to at most
  the trace of the input. The codomain of `Φ i` may depend on `i`.
* `Quantum.MatrixMap.familySum Φ`: the pointwise sum `ρ ↦ ∑' i, Φ i ρ` of a family with a common
  codomain, when that sum converges on every input, and `0` otherwise.
* `Quantum.MatrixMap.familyTrace Φ`: the trace functional `ρ ↦ ∑' i, trace (Φ i ρ)`, when the
  traces are summable on every input, and `0` otherwise. Neither fallback is reached by a
  completely positive family with trace-nonincreasing partial sums.
* `Quantum.MatrixMap.familyBind Φ Ψ`: Kleisli composition of families: run the first branch
  family, then the outcome-selected continuation, summing over intermediate outcomes. The member
  at `c` is `familySum fun i ↦ Ψ i c ∘ₗ Φ i`.

## Main results

* `Quantum.MatrixMap.IsCPTNIFamily.summable_apply`: a completely positive family with a common
  codomain and trace-nonincreasing finite partial sums is summable on every matrix.
* `Quantum.MatrixMap.isCP_familySum`, `Quantum.MatrixMap.IsCPTNIFamily.isTNI_familySum`: the sum
  of such a family is completely positive and trace nonincreasing.
* `Quantum.MatrixMap.IsCPTNIFamily.countable_support`: such a family has countable support, also
  when its codomain depends on the label.
* `Quantum.MatrixMap.familyBind_assoc_of_summable`, `Quantum.MatrixMap.single_id_familyBind`,
  `Quantum.MatrixMap.familyBind_single_id`: the monad laws for Kleisli composition. The unit laws
  hold for all families. Associativity, and the formulas `familySum_familyBind_of_summable` and
  `familyTrace_familyBind_of_summable`, hold for all families with the summability that makes
  their sums pointwise and lets the two sums be exchanged; completely positive families with
  trace-nonincreasing partial sums have it (`Quantum.MatrixMap.familyBind_assoc` and the like).
* `Quantum.MatrixMap.amplify_familySum`, `Quantum.MatrixMap.familyBind_mapRange_amplify`:
  amplification commutes with sums and with Kleisli composition, for all families.
-/

public section

open scoped ComplexOrder
open Matrix

/-! ## Matrices -/

namespace Matrix

variable {n ι : Type*}

/-- Every entry of a positive semidefinite complex matrix has norm at most the trace. -/
theorem PosSemidef.norm_apply_le_trace_re [Fintype n] {M : Matrix n n ℂ} (hM : M.PosSemidef)
    (i j : n) : ‖M i j‖ ≤ M.trace.re := by
  classical
  open scoped MatrixOrder in
  obtain ⟨Y, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hM.nonneg
  have hentry : ∀ i j, (star Y * Y) i j = ∑ k, star (Y k i) * Y k j := fun i j ↦ by
    simp [Matrix.mul_apply, Matrix.star_apply]
  have hcol : ∀ l, ∑ k, ‖Y k l‖ ^ 2 ≤ (star Y * Y).trace.re := fun l ↦ by
    have htr : (star Y * Y).trace.re = ∑ l, ∑ k, ‖Y k l‖ ^ 2 := by
      simp only [Matrix.trace, Matrix.diag, hentry, Complex.re_sum]
      refine Finset.sum_congr rfl fun l _ ↦ Finset.sum_congr rfl fun k _ ↦ ?_
      have h : star (Y k l) * Y k l = ((‖Y k l‖ ^ 2 : ℝ) : ℂ) := by
        rw [Complex.star_def, Complex.conj_mul', Complex.ofReal_pow]
      rw [h, Complex.ofReal_re]
    rw [htr]
    exact Finset.single_le_sum (f := fun l ↦ ∑ k, ‖Y k l‖ ^ 2)
      (fun l _ ↦ Finset.sum_nonneg fun k _ ↦ sq_nonneg _) (Finset.mem_univ l)
  calc ‖(star Y * Y) i j‖ = ‖∑ k, star (Y k i) * Y k j‖ := by rw [hentry]
    _ ≤ ∑ k, ‖star (Y k i) * Y k j‖ := norm_sum_le _ _
    _ = ∑ k, ‖Y k i‖ * ‖Y k j‖ := by simp
    _ ≤ ∑ k, (‖Y k i‖ ^ 2 + ‖Y k j‖ ^ 2) / 2 := Finset.sum_le_sum fun k _ ↦ by
        nlinarith [sq_nonneg (‖Y k i‖ - ‖Y k j‖)]
    _ = ((∑ k, ‖Y k i‖ ^ 2) + ∑ k, ‖Y k j‖ ^ 2) / 2 := by
        rw [← Finset.sum_div, Finset.sum_add_distrib]
    _ ≤ ((star Y * Y).trace.re + (star Y * Y).trace.re) / 2 := by gcongr <;> exact hcol _
    _ = (star Y * Y).trace.re := by ring

/-- The trace of a positive semidefinite complex matrix is real. -/
theorem PosSemidef.ofReal_trace_re [Fintype n] {M : Matrix n n ℂ} (hM : M.PosSemidef) :
    ((M.trace.re : ℝ) : ℂ) = M.trace :=
  Complex.ext (Complex.ofReal_re _) <| by
    rw [Complex.ofReal_im]
    exact (Complex.nonneg_iff.mp hM.trace_nonneg).2

/-- A sum of positive semidefinite complex matrices is positive semidefinite. This holds for
every family: the sum of a family that is not summable is zero. -/
theorem PosSemidef.tsum [Finite n] {f : ι → Matrix n n ℂ} (hf : ∀ i, (f i).PosSemidef) :
    (∑' i, f i).PosSemidef := by
  classical
  cases nonempty_fintype n
  open scoped MatrixOrder in
  exact Matrix.nonneg_iff_posSemidef.mp (tsum_nonneg fun i ↦ (hf i).nonneg)

/-- Positive semidefinite complex matrices span all complex matrices. -/
theorem span_posSemidef [Finite n] :
    Submodule.span ℂ {M : Matrix n n ℂ | M.PosSemidef} = ⊤ := by
  classical
  cases nonempty_fintype n
  open scoped MatrixOrder in
  simpa only [Matrix.nonneg_iff_posSemidef] using CStarAlgebra.span_nonneg (A := Matrix n n ℂ)

/-- To prove a property of all complex matrices that is stable under sums and scalar multiples,
it suffices to prove it for positive semidefinite matrices. -/
theorem induction_on_posSemidef [Finite n] {p : Matrix n n ℂ → Prop} (M : Matrix n n ℂ)
    (posSemidef : ∀ M : Matrix n n ℂ, M.PosSemidef → p M)
    (add : ∀ M N, p M → p N → p (M + N)) (smul : ∀ (c : ℂ) M, p M → p (c • M)) : p M := by
  have hM : M ∈ Submodule.span ℂ {M : Matrix n n ℂ | M.PosSemidef} := by
    rw [span_posSemidef]
    exact Submodule.mem_top
  induction hM using Submodule.span_induction with
  | mem x hx => exact posSemidef x hx
  | zero => exact posSemidef 0 PosSemidef.zero
  | add x y _ _ hx hy => exact add x y hx hy
  | smul c x _ hx => exact smul c x hx

/-- A family of linear maps out of complex matrices that is summable on every positive
semidefinite matrix is summable on every matrix. -/
theorem summable_apply_of_posSemidef [Finite n] {E : Type*} [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousConstSMul ℂ E]
    {f : ι → Matrix n n ℂ →ₗ[ℂ] E} (h : ∀ M : Matrix n n ℂ, M.PosSemidef → Summable fun i ↦ f i M)
    (M : Matrix n n ℂ) : Summable fun i ↦ f i M := by
  induction M using induction_on_posSemidef with
  | posSemidef M hM => exact h M hM
  | add M N hM hN => simpa only [map_add] using hM.add hN
  | smul c M hM => simpa only [map_smul] using hM.const_smul c

/-- The entries of the sum of a summable family of matrices are the sums of the entries. -/
theorem tsum_apply_apply {m : Type*} {f : ι → Matrix m n ℂ} (hf : Summable f) (i : m) (j : n) :
    (∑' k, f k) i j = ∑' k, f k i j :=
  (congrFun (Pi.tsum_apply (x := i) hf) j).trans (Pi.tsum_apply (Pi.summable.mp hf i))

/-- A family of matrices is summable when all its entries are. -/
theorem summable_of_apply_apply {m : Type*} {f : ι → Matrix m n ℂ}
    (hf : ∀ i j, Summable fun k ↦ f k i j) : Summable f :=
  Pi.summable.mpr fun i ↦ Pi.summable.mpr fun j ↦ hf i j

/-- The traces of a summable family of square matrices are summable. -/
theorem summable_trace [Fintype n] {f : ι → Matrix n n ℂ} (hf : Summable f) :
    Summable fun i ↦ (f i).trace :=
  hf.map (traceLinearMap n ℂ ℂ) (LinearMap.continuous_of_finiteDimensional _)

/-- The trace of the sum of a summable family of square matrices is the sum of the traces. -/
theorem trace_tsum [Fintype n] {f : ι → Matrix n n ℂ} (hf : Summable f) :
    (∑' i, f i).trace = ∑' i, (f i).trace :=
  hf.map_tsum (traceLinearMap n ℂ ℂ) (LinearMap.continuous_of_finiteDimensional _)

end Matrix

namespace Quantum

namespace MatrixMap

variable {A : Type*} {ι κ μ : Type*}

/-! ## Sums of summable families of matrices -/

section tsum

variable [Finite A] {B : Type*}

/-- A matrix map commutes with sums of summable families. -/
theorem map_tsum (Φ : MatrixMap A B) {f : ι → Matrix A A ℂ} (hf : Summable f) :
    Φ (∑' i, f i) = ∑' i, Φ (f i) := by
  cases nonempty_fintype A
  exact hf.map_tsum Φ (LinearMap.continuous_of_finiteDimensional Φ)

/-- A matrix map sends summable families to summable families. -/
theorem summable_comp (Φ : MatrixMap A B) {f : ι → Matrix A A ℂ} (hf : Summable f) :
    Summable fun i ↦ Φ (f i) := by
  cases nonempty_fintype A
  exact hf.map Φ (LinearMap.continuous_of_finiteDimensional Φ)

end tsum

/-! ## Completely positive families with trace-nonincreasing partial sums -/

section IsCPTNIFamily

variable [Fintype A] {B : ι → Type*} [∀ i, Fintype (B i)] {C : κ → Type*} [∀ c, Fintype (C c)]

/-- A family of completely positive maps whose finite partial sums are jointly trace
nonincreasing: `∑ i ∈ s, tr (Φ i ρ) ≤ tr ρ` for every finite set `s` and every positive
semidefinite `ρ`. The output system of `Φ i` may depend on `i`.

The bound is joint, not per member: on a nonzero-dimensional system, two copies of the identity
map form no such family. These are the branch families of the instruments in
`VCVio.Quantum.SubInstrument` and `VCVio.Quantum.DSubInstrument`. -/
structure IsCPTNIFamily (Φ : (i : ι) → MatrixMap A (B i)) : Prop where
  /-- Every member is completely positive. -/
  isCP : ∀ i, (Φ i).IsCP
  /-- On positive semidefinite inputs, the traces of the members over a finite set of labels sum
  to at most the trace of the input. -/
  sum_trace_re_le : ∀ (s : Finset ι) (ρ : Matrix A A ℂ), ρ.PosSemidef →
    ∑ i ∈ s, (Φ i ρ).trace.re ≤ ρ.trace.re

namespace IsCPTNIFamily

variable {Φ : (i : ι) → MatrixMap A (B i)}

/-- Each member of a completely positive family preserves positive semidefiniteness. -/
theorem posSemidef_apply (h : IsCPTNIFamily Φ) (i : ι) {ρ : Matrix A A ℂ} (hρ : ρ.PosSemidef) :
    (Φ i ρ).PosSemidef :=
  (h.isCP i).posSemidef hρ

/-- On a positive semidefinite input, each member has nonnegative trace. -/
theorem trace_re_apply_nonneg (h : IsCPTNIFamily Φ) (i : ι) {ρ : Matrix A A ℂ}
    (hρ : ρ.PosSemidef) : 0 ≤ (Φ i ρ).trace.re :=
  (h.posSemidef_apply i hρ).trace_re_nonneg

/-- Each member of the family is trace nonincreasing. -/
theorem isTNI (h : IsCPTNIFamily Φ) (i : ι) : (Φ i).IsTNI := fun ρ hρ ↦ by
  simpa using h.sum_trace_re_le {i} ρ hρ

/-- On a positive semidefinite input, the traces of the members form a summable family. -/
theorem summable_trace_re_apply (h : IsCPTNIFamily Φ) {ρ : Matrix A A ℂ} (hρ : ρ.PosSemidef) :
    Summable fun i ↦ (Φ i ρ).trace.re :=
  summable_of_sum_le (fun i ↦ h.trace_re_apply_nonneg i hρ) fun s ↦ h.sum_trace_re_le s ρ hρ

/-- On a positive semidefinite input, the traces of the members sum to at most the trace of the
input. -/
theorem tsum_trace_re_apply_le (h : IsCPTNIFamily Φ) {ρ : Matrix A A ℂ} (hρ : ρ.PosSemidef) :
    ∑' i, (Φ i ρ).trace.re ≤ ρ.trace.re :=
  Real.tsum_le_of_sum_le (fun i ↦ h.trace_re_apply_nonneg i hρ) fun s ↦
    h.sum_trace_re_le s ρ hρ

/-- On every input, the traces of the members form a summable family. -/
theorem summable_trace_apply (h : IsCPTNIFamily Φ) (ρ : Matrix A A ℂ) :
    Summable fun i ↦ (Φ i ρ).trace := by
  refine Matrix.summable_apply_of_posSemidef
    (f := fun i ↦ Matrix.traceLinearMap (B i) ℂ ℂ ∘ₗ Φ i) (fun ρ hρ ↦ ?_) ρ
  exact (Complex.summable_ofReal.mpr (h.summable_trace_re_apply hρ)).congr fun i ↦
    (h.posSemidef_apply i hρ).ofReal_trace_re

/-- A member whose trace vanishes on every input is zero: it maps positive semidefinite inputs to
positive semidefinite matrices of trace zero, and these span all inputs. -/
theorem eq_zero_of_trace_apply_eq_zero (h : IsCPTNIFamily Φ) {i : ι}
    (h0 : ∀ ρ : Matrix A A ℂ, (Φ i ρ).trace = 0) : Φ i = 0 :=
  LinearMap.ext fun ρ ↦ by
    rw [LinearMap.zero_apply]
    induction ρ using Matrix.induction_on_posSemidef with
    | posSemidef ρ hρ => exact (h.posSemidef_apply i hρ).trace_eq_zero_iff.mp (h0 ρ)
    | add ρ σ hρ hσ => rw [map_add, hρ, hσ, add_zero]
    | smul c ρ hρ => rw [map_smul, hρ, smul_zero]

/-- **Countable support.** A completely positive family with trace-nonincreasing partial sums,
whose codomain may depend on the label, has countable support: only countably many members are
nonzero. For a common codomain the set is `Function.support Φ`. A nonzero member has nonzero
trace on some matrix unit, and on each of the finitely many matrix units the traces of the
members form a summable family. -/
theorem countable_support (h : IsCPTNIFamily Φ) : {i | Φ i ≠ 0}.Countable := by
  classical
  have key : {i | Φ i ≠ 0} ⊆ ⋃ x : A × A,
      Function.support fun i ↦ (Φ i (Matrix.single x.1 x.2 1)).trace := by
    intro i (hi : Φ i ≠ 0)
    by_contra hcon
    simp only [Set.mem_iUnion, Function.mem_support, not_exists, not_not] at hcon
    have h0 : ∀ r s, (Φ i (Matrix.single r s 1)).trace = 0 := fun r s ↦ hcon (r, s)
    refine hi (h.eq_zero_of_trace_apply_eq_zero fun ρ ↦ ?_)
    have hρ : ρ = ∑ r, ∑ s, ρ r s • Matrix.single r s (1 : ℂ) := by
      simp only [Matrix.smul_single, smul_eq_mul, mul_one]
      exact Matrix.matrix_eq_sum_single ρ
    rw [hρ]
    simp only [map_sum, map_smul, Matrix.trace_sum, Matrix.trace_smul, h0, smul_zero,
      Finset.sum_const_zero]
  exact (Set.countable_iUnion fun x ↦ (h.summable_trace_apply _).countable_support).mono key

/-- The real part of the sum of the traces of the members is the sum of their real parts. -/
theorem re_tsum_trace_apply (h : IsCPTNIFamily Φ) (ρ : Matrix A A ℂ) :
    (∑' i, (Φ i ρ).trace).re = ∑' i, (Φ i ρ).trace.re :=
  Complex.re_tsum (h.summable_trace_apply ρ)

/-- Postcomposing the members of a completely positive family with trace-nonincreasing partial
sums with completely positive, trace-nonincreasing maps gives such a family. -/
theorem comp (h : IsCPTNIFamily Φ) {D : ι → Type*} [∀ i, Fintype (D i)]
    {Ψ : (i : ι) → MatrixMap (B i) (D i)} (hcp : ∀ i, (Ψ i).IsCP) (htni : ∀ i, (Ψ i).IsTNI) :
    IsCPTNIFamily fun i ↦ Ψ i ∘ₗ Φ i where
  isCP i := (hcp i).comp (h.isCP i)
  sum_trace_re_le s ρ hρ :=
    (Finset.sum_le_sum fun i _ ↦ htni i _ (h.posSemidef_apply i hρ)).trans
      (h.sum_trace_re_le s ρ hρ)

/-- Following each member `Φ i` by the member at `c` of a continuation family `Ψ i` gives a
family with trace-nonincreasing partial sums. -/
theorem comp_eval (h : IsCPTNIFamily Φ) {Ψ : (i : ι) → (c : κ) → MatrixMap (B i) (C c)}
    (hΨ : ∀ i, IsCPTNIFamily (Ψ i)) (c : κ) : IsCPTNIFamily fun i ↦ Ψ i c ∘ₗ Φ i :=
  h.comp (fun i ↦ (hΨ i).isCP c) fun i ↦ (hΨ i).isTNI c

/-- The family of all two-step composites `Ψ i c ∘ₗ Φ i`, indexed by pairs, has
trace-nonincreasing partial sums. This gives the joint summability behind every exchange of
sums. -/
theorem prod (h : IsCPTNIFamily Φ) {Ψ : (i : ι) → (c : κ) → MatrixMap (B i) (C c)}
    (hΨ : ∀ i, IsCPTNIFamily (Ψ i)) : IsCPTNIFamily fun x : ι × κ ↦ Ψ x.1 x.2 ∘ₗ Φ x.1 where
  isCP x := ((hΨ x.1).isCP x.2).comp (h.isCP x.1)
  sum_trace_re_le s ρ hρ := by
    classical
    calc ∑ x ∈ s, ((Ψ x.1 x.2 ∘ₗ Φ x.1) ρ).trace.re
        ≤ ∑ x ∈ s.image Prod.fst ×ˢ s.image Prod.snd, ((Ψ x.1 x.2 ∘ₗ Φ x.1) ρ).trace.re :=
          Finset.sum_le_sum_of_subset_of_nonneg
            (fun x hx ↦ Finset.mem_product.mpr
              ⟨Finset.mem_image_of_mem _ hx, Finset.mem_image_of_mem _ hx⟩)
            fun x _ _ ↦ (hΨ x.1).trace_re_apply_nonneg x.2 (h.posSemidef_apply x.1 hρ)
      _ = ∑ i ∈ s.image Prod.fst, ∑ c ∈ s.image Prod.snd, (Ψ i c (Φ i ρ)).trace.re :=
          Finset.sum_product _ _ _
      _ ≤ ∑ i ∈ s.image Prod.fst, (Φ i ρ).trace.re :=
          Finset.sum_le_sum fun i _ ↦ (hΨ i).sum_trace_re_le _ _ (h.posSemidef_apply i hρ)
      _ ≤ ρ.trace.re := h.sum_trace_re_le _ ρ hρ

/-- Amplifying every member by an ancilla preserves trace-nonincreasing partial sums. -/
theorem amplify (h : IsCPTNIFamily Φ) (R : Type*) [Fintype R] :
    IsCPTNIFamily fun i ↦ (Φ i).amplify R where
  isCP i := (h.isCP i).amplify
  sum_trace_re_le s ρ hρ := by
    simp only [trace_amplify_apply, Complex.re_sum]
    rw [Finset.sum_comm, trace_eq_sum_trace_submatrix ρ, Complex.re_sum]
    exact Finset.sum_le_sum fun r _ ↦ h.sum_trace_re_le s _ (hρ.submatrix _)

/-- A completely positive family that vanishes outside a finite set `s` has trace-nonincreasing
partial sums when its partial sum over `s` does. -/
theorem of_forall_notMem (s : Finset ι) (hs : ∀ i ∉ s, Φ i = 0) (hcp : ∀ i, (Φ i).IsCP)
    (h : ∀ ρ : Matrix A A ℂ, ρ.PosSemidef → ∑ i ∈ s, (Φ i ρ).trace.re ≤ ρ.trace.re) :
    IsCPTNIFamily Φ where
  isCP := hcp
  sum_trace_re_le t ρ hρ := by
    classical
    calc ∑ i ∈ t, (Φ i ρ).trace.re ≤ ∑ i ∈ t ∪ s, (Φ i ρ).trace.re :=
          Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left fun i _ _ ↦
            ((hcp i).posSemidef hρ).trace_re_nonneg
      _ = ∑ i ∈ s, (Φ i ρ).trace.re :=
          (Finset.sum_subset Finset.subset_union_right fun i _ hi ↦ by simp [hs i hi]).symm
      _ ≤ ρ.trace.re := h ρ hρ

/-- A completely positive family over a finite type of labels has trace-nonincreasing partial
sums when its full sum does. -/
theorem of_fintype [Fintype ι] (hcp : ∀ i, (Φ i).IsCP)
    (h : ∀ ρ : Matrix A A ℂ, ρ.PosSemidef → ∑ i, (Φ i ρ).trace.re ≤ ρ.trace.re) :
    IsCPTNIFamily Φ :=
  of_forall_notMem Finset.univ (fun i hi ↦ absurd (Finset.mem_univ i) hi) hcp h

end IsCPTNIFamily

/-- The zero family has trace-nonincreasing partial sums. -/
theorem isCPTNIFamily_zero : IsCPTNIFamily (0 : (i : ι) → MatrixMap A (B i)) :=
  .of_forall_notMem ∅ (fun _ _ ↦ rfl) (fun _ ↦ IsCP.zero) fun ρ hρ ↦ by
    simpa using hρ.trace_re_nonneg

/-- A family with a single completely positive, trace-nonincreasing member has
trace-nonincreasing partial sums. -/
theorem isCPTNIFamily_single [DecidableEq ι] (i : ι) {Φ : MatrixMap A (B i)} (hcp : Φ.IsCP)
    (htni : Φ.IsTNI) : IsCPTNIFamily (B := B) (Pi.single i Φ) :=
  .of_forall_notMem (Φ := Pi.single (M := fun j ↦ MatrixMap A (B j)) i Φ) {i}
    (fun j hj ↦ by rw [Pi.single_eq_of_ne (Finset.notMem_singleton.mp hj)])
    (fun j ↦ by
      obtain rfl | h := eq_or_ne j i
      · rw [Pi.single_eq_same]
        exact hcp
      · rw [Pi.single_eq_of_ne h]
        exact .zero)
    fun ρ hρ ↦ by
      rw [Finset.sum_singleton, Pi.single_eq_same]
      exact htni ρ hρ

end IsCPTNIFamily

/-! ## Families with a common codomain -/

section common

variable {B C : Type*}

/-- On a finite partial sum, the real part of the trace is the sum of the real parts of the
traces of the members. -/
theorem trace_re_sum_apply [Fintype B] (s : Finset ι) (Φ : ι → MatrixMap A B)
    (ρ : Matrix A A ℂ) : ((∑ i ∈ s, Φ i) ρ).trace.re = ∑ i ∈ s, (Φ i ρ).trace.re := by
  rw [LinearMap.sum_apply, Matrix.trace_sum, Complex.re_sum]

/-- For a common codomain, trace-nonincreasing partial sums in the sense of
`Quantum.MatrixMap.IsCPTNIFamily` are trace nonincrease, `Quantum.MatrixMap.IsTNI`, of every
finite partial sum. -/
theorem isCPTNIFamily_iff [Fintype A] [Fintype B] {Φ : ι → MatrixMap A B} :
    IsCPTNIFamily Φ ↔ (∀ i, (Φ i).IsCP) ∧ ∀ s : Finset ι, (∑ i ∈ s, Φ i).IsTNI := by
  refine ⟨fun h ↦ ⟨h.isCP, fun s ρ hρ ↦ ?_⟩, fun h ↦ ⟨h.1, fun s ρ hρ ↦ ?_⟩⟩
  · rw [trace_re_sum_apply]
    exact h.sum_trace_re_le s ρ hρ
  · rw [← trace_re_sum_apply]
    exact h.2 s ρ hρ

namespace IsCPTNIFamily

variable [Fintype A] [Fintype B] {Φ : ι → MatrixMap A B}

/-- Every finite partial sum of the family is trace nonincreasing. -/
theorem isTNI_sum (h : IsCPTNIFamily Φ) (s : Finset ι) : (∑ i ∈ s, Φ i).IsTNI :=
  (isCPTNIFamily_iff.mp h).2 s

/-- A completely positive family whose finite partial sums are trace nonincreasing. -/
theorem of_isTNI_sum (hcp : ∀ i, (Φ i).IsCP) (h : ∀ s : Finset ι, (∑ i ∈ s, Φ i).IsTNI) :
    IsCPTNIFamily Φ :=
  isCPTNIFamily_iff.mpr ⟨hcp, h⟩

/-- **Summability.** A completely positive family with trace-nonincreasing partial sums is
summable on every matrix. -/
theorem summable_apply (h : IsCPTNIFamily Φ) (ρ : Matrix A A ℂ) : Summable fun i ↦ Φ i ρ := by
  refine Matrix.summable_apply_of_posSemidef (f := Φ) (fun ρ hρ ↦ ?_) ρ
  exact Matrix.summable_of_apply_apply fun x y ↦
    (h.summable_trace_re_apply hρ).of_norm_bounded fun i ↦
      (h.posSemidef_apply i hρ).norm_apply_le_trace_re x y

end IsCPTNIFamily

/-! ### The sum of a family -/

open Classical in
/-- The pointwise sum `ρ ↦ ∑' i, Φ i ρ` of a family of matrix maps with a common codomain. It is
defined to be zero when the family is not summable on some input; for a completely positive
family with trace-nonincreasing partial sums it is always the pointwise sum
(`Quantum.MatrixMap.IsCPTNIFamily.familySum_apply`). -/
@[expose]
noncomputable def familySum (Φ : ι → MatrixMap A B) : MatrixMap A B :=
  if h : ∀ ρ, Summable fun i ↦ Φ i ρ then
    { toFun ρ := ∑' i, Φ i ρ
      map_add' ρ σ := by
        simp only [map_add]
        exact (h ρ).tsum_add (h σ)
      map_smul' c ρ := by
        simp only [map_smul, RingHom.id_apply]
        exact (h ρ).tsum_const_smul c }
  else 0

/-- The sum of a family that is summable on every input is the pointwise sum. -/
theorem familySum_apply {Φ : ι → MatrixMap A B} (h : ∀ ρ, Summable fun i ↦ Φ i ρ)
    (ρ : Matrix A A ℂ) : familySum Φ ρ = ∑' i, Φ i ρ := by
  rw [familySum, dite_eq_left h]
  rfl

/-- A family that vanishes outside a finite set is summable on every input. -/
theorem summable_apply_of_forall_notMem {Φ : ι → MatrixMap A B} {s : Finset ι}
    (hs : ∀ i ∉ s, Φ i = 0) (ρ : Matrix A A ℂ) : Summable fun i ↦ Φ i ρ :=
  summable_of_ne_finset_zero fun i hi ↦ by rw [hs i hi, LinearMap.zero_apply]

/-- The sum of a family that vanishes outside a finite set is the finite sum over that set. -/
theorem familySum_eq_sum_of_forall_notMem {Φ : ι → MatrixMap A B} {s : Finset ι}
    (hs : ∀ i ∉ s, Φ i = 0) : familySum Φ = ∑ i ∈ s, Φ i :=
  LinearMap.ext fun ρ ↦ by
    rw [familySum_apply (summable_apply_of_forall_notMem hs), LinearMap.sum_apply,
      tsum_eq_sum fun i hi ↦ by rw [hs i hi, LinearMap.zero_apply]]

/-- The sum of a family over a finite type of labels is the finite sum. -/
theorem familySum_eq_sum_univ [Fintype ι] (Φ : ι → MatrixMap A B) :
    familySum Φ = ∑ i, Φ i :=
  familySum_eq_sum_of_forall_notMem fun i hi ↦ absurd (Finset.mem_univ i) hi

/-- The sum of the zero family is zero. -/
@[simp]
theorem familySum_zero : familySum (0 : ι → MatrixMap A B) = 0 := by
  rw [familySum_eq_sum_of_forall_notMem (Φ := 0) (s := ∅) fun _ _ ↦ rfl, Finset.sum_empty]

/-- The sum of a family with a single member is that member. -/
@[simp]
theorem familySum_single [DecidableEq ι] (i : ι) (Φ : MatrixMap A B) :
    familySum (Pi.single i Φ) = Φ := by
  rw [familySum_eq_sum_of_forall_notMem (Φ := Pi.single i Φ) (s := {i})
    fun j hj ↦ by rw [Pi.single_eq_of_ne (Finset.notMem_singleton.mp hj)], Finset.sum_singleton,
    Pi.single_eq_same]

/-- Amplifying the members of a family summable on every input gives a family summable on every
input. -/
theorem summable_amplify_apply {Φ : ι → MatrixMap A B} (h : ∀ ρ, Summable fun i ↦ Φ i ρ)
    (R : Type*) (ρ : Matrix (A × R) (A × R) ℂ) : Summable fun i ↦ (Φ i).amplify R ρ :=
  Matrix.summable_of_apply_apply fun x y ↦
    Pi.summable.mp (Pi.summable.mp (h (ρ.submatrix (·, x.2) (·, y.2))) x.1) y.1

/-- Conversely, a family whose amplification by a nonempty ancilla is summable on every input is
itself summable on every input: a matrix `ρ` is a diagonal block of `ρ.submatrix Prod.fst Prod.fst`.
-/
theorem summable_apply_of_summable_amplify_apply {R : Type*} [Nonempty R] {Φ : ι → MatrixMap A B}
    (h : ∀ ρ, Summable fun i ↦ (Φ i).amplify R ρ) (ρ : Matrix A A ℂ) :
    Summable fun i ↦ Φ i ρ := by
  obtain ⟨r⟩ := ‹Nonempty R›
  exact Matrix.summable_of_apply_apply fun x y ↦
    Pi.summable.mp (Pi.summable.mp (h (ρ.submatrix Prod.fst Prod.fst)) (x, r)) (y, r)

/-- Amplification commutes with the sum of every family of matrix maps. When the family is not
summable on some input, neither is the amplified family (for a nonempty ancilla), and both sides
are zero. -/
theorem amplify_familySum (Φ : ι → MatrixMap A B) (R : Type*) :
    (familySum Φ).amplify R = familySum fun i ↦ (Φ i).amplify R := by
  by_cases h : ∀ ρ, Summable fun i ↦ Φ i ρ
  · refine LinearMap.ext fun ρ ↦ ?_
    ext x y
    rw [amplify_apply, familySum_apply h, familySum_apply (summable_amplify_apply h R),
      Matrix.tsum_apply_apply (h _), Matrix.tsum_apply_apply (summable_amplify_apply h R ρ)]
    rfl
  · rcases isEmpty_or_nonempty R with hR | hR
    · refine LinearMap.ext fun ρ ↦ ?_
      ext x
      exact isEmptyElim x.2
    · have h' : ¬ ∀ ρ, Summable fun i ↦ (Φ i).amplify R ρ := fun h' ↦
        h (summable_apply_of_summable_amplify_apply h')
      have e : familySum Φ = 0 := by rw [familySum, dite_eq_right h]
      have e' : familySum (fun i ↦ (Φ i).amplify R) = 0 := by rw [familySum, dite_eq_right h']
      rw [e, e', amplify_zero]

/-- `familySum Φ` is completely positive when every `Φ i` is completely positive.
If the family is summable on every input, this is its pointwise sum. Otherwise `familySum Φ`
is the zero map, which is also completely positive. `IsCPTNIFamily.summable_apply` excludes
that fallback for the branch families of subinstruments. -/
theorem isCP_familySum [Finite B] {Φ : ι → MatrixMap A B} (hcp : ∀ i, (Φ i).IsCP) :
    (familySum Φ).IsCP := by
  by_cases h : ∀ ρ, Summable fun i ↦ Φ i ρ
  · intro k ρ hρ
    rw [amplify_familySum, familySum_apply (summable_amplify_apply h _)]
    exact Matrix.PosSemidef.tsum fun i ↦ hcp i k ρ hρ
  · rw [familySum, dite_eq_right h]
    exact .zero

/-- The trace of the sum of a family summable on every input is the sum of the traces. -/
theorem trace_familySum_apply [Fintype B] {Φ : ι → MatrixMap A B}
    (h : ∀ ρ, Summable fun i ↦ Φ i ρ) (ρ : Matrix A A ℂ) :
    (familySum Φ ρ).trace = ∑' i, (Φ i ρ).trace := by
  rw [familySum_apply h, Matrix.trace_tsum (h ρ)]

/-- Postcomposing the sum of a family summable on every input with a matrix map gives the sum of
the postcomposed family. -/
theorem comp_familySum [Finite B] (Ψ : MatrixMap B C) {Φ : ι → MatrixMap A B}
    (h : ∀ ρ, Summable fun i ↦ Φ i ρ) : Ψ ∘ₗ familySum Φ = familySum fun i ↦ Ψ ∘ₗ Φ i :=
  LinearMap.ext fun ρ ↦ by
    rw [LinearMap.comp_apply, familySum_apply h,
      familySum_apply (Φ := fun i ↦ Ψ ∘ₗ Φ i) fun ρ ↦ summable_comp Ψ (h ρ), map_tsum Ψ (h ρ)]
    rfl

namespace IsCPTNIFamily

variable [Fintype A] [Fintype B] {Φ : ι → MatrixMap A B}

/-- The sum of a completely positive family with trace-nonincreasing partial sums is the
pointwise sum. -/
theorem familySum_apply (h : IsCPTNIFamily Φ) (ρ : Matrix A A ℂ) :
    familySum Φ ρ = ∑' i, Φ i ρ :=
  MatrixMap.familySum_apply h.summable_apply ρ

/-- The sum of a completely positive family with trace-nonincreasing partial sums is trace
nonincreasing. -/
theorem isTNI_familySum (h : IsCPTNIFamily Φ) : (familySum Φ).IsTNI := fun ρ hρ ↦ by
  rw [trace_familySum_apply h.summable_apply, h.re_tsum_trace_apply]
  exact h.tsum_trace_re_apply_le hρ

/-- On a positive semidefinite input, each member has trace at most that of the sum. -/
theorem trace_re_apply_le_familySum (h : IsCPTNIFamily Φ) (i : ι) {ρ : Matrix A A ℂ}
    (hρ : ρ.PosSemidef) : (Φ i ρ).trace.re ≤ (familySum Φ ρ).trace.re := by
  rw [trace_familySum_apply h.summable_apply, h.re_tsum_trace_apply]
  exact (h.summable_trace_re_apply hρ).le_tsum i fun j _ ↦ h.trace_re_apply_nonneg j hρ

end IsCPTNIFamily

end common

/-! ## The trace functional -/

section familyTrace

variable {B : ι → Type*} [∀ i, Fintype (B i)]

open Classical in
/-- The total trace of a family of maps whose output system may depend on the label:
`ρ ↦ ∑' i, tr (Φ i ρ)`. The output matrices have different types and cannot be added, but their
traces can. When the traces are not summable on some input, the functional is `0` everywhere;
`IsCPTNIFamily.summable_trace_apply` shows this never happens for a physical branch family. For
finitely many labels it is the trace of the block-diagonal output. -/
@[expose]
noncomputable def familyTrace (Φ : (i : ι) → MatrixMap A (B i)) : Matrix A A ℂ →ₗ[ℂ] ℂ :=
  if h : ∀ ρ, Summable fun i ↦ (Φ i ρ).trace then
    { toFun ρ := ∑' i, (Φ i ρ).trace
      map_add' ρ σ := by
        simp only [map_add, Matrix.trace_add]
        exact (h ρ).tsum_add (h σ)
      map_smul' c ρ := by
        simp only [map_smul, Matrix.trace_smul, smul_eq_mul, RingHom.id_apply]
        exact (h ρ).tsum_mul_left c }
  else 0

/-- The trace functional of a family whose traces are summable on every input is the sum of the
traces. -/
theorem familyTrace_apply {Φ : (i : ι) → MatrixMap A (B i)}
    (h : ∀ ρ, Summable fun i ↦ (Φ i ρ).trace) (ρ : Matrix A A ℂ) :
    familyTrace Φ ρ = ∑' i, (Φ i ρ).trace := by
  rw [familyTrace, dite_eq_left h]
  rfl

/-- The trace functional of a completely positive family with trace-nonincreasing partial sums
is the sum of the traces. -/
theorem IsCPTNIFamily.familyTrace_apply [Fintype A] {Φ : (i : ι) → MatrixMap A (B i)}
    (h : IsCPTNIFamily Φ) (ρ : Matrix A A ℂ) : familyTrace Φ ρ = ∑' i, (Φ i ρ).trace :=
  MatrixMap.familyTrace_apply h.summable_trace_apply ρ

/-- The trace functional as a sum over any finite set outside which the family vanishes. -/
theorem familyTrace_apply_of_forall_notMem {Φ : (i : ι) → MatrixMap A (B i)} {s : Finset ι}
    (hs : ∀ i ∉ s, Φ i = 0) (ρ : Matrix A A ℂ) :
    familyTrace Φ ρ = ∑ i ∈ s, (Φ i ρ).trace := by
  have hz : ∀ ρ, ∀ i ∉ s, (Φ i ρ).trace = 0 := fun ρ i hi ↦ by
    rw [hs i hi, LinearMap.zero_apply, Matrix.trace_zero]
  rw [familyTrace_apply fun ρ ↦ summable_of_ne_finset_zero (hz ρ), tsum_eq_sum (hz ρ)]

/-- The trace functional as a sum over a finite type of labels. -/
theorem familyTrace_apply_univ [Fintype ι] (Φ : (i : ι) → MatrixMap A (B i))
    (ρ : Matrix A A ℂ) : familyTrace Φ ρ = ∑ i, (Φ i ρ).trace :=
  familyTrace_apply_of_forall_notMem (fun i hi ↦ absurd (Finset.mem_univ i) hi) ρ

/-- The trace functional of the zero family is zero. -/
@[simp]
theorem familyTrace_zero : familyTrace (0 : (i : ι) → MatrixMap A (B i)) = 0 :=
  LinearMap.ext fun ρ ↦ by
    rw [familyTrace_apply_of_forall_notMem (Φ := 0) (s := ∅) (fun _ _ ↦ rfl), Finset.sum_empty,
      LinearMap.zero_apply]

/-- The trace functional of a family with a single member is the trace after that member. -/
@[simp]
theorem familyTrace_single [DecidableEq ι] (i : ι) (Φ : MatrixMap A (B i)) :
    familyTrace (B := B) (Pi.single i Φ) = Matrix.traceLinearMap (B i) ℂ ℂ ∘ₗ Φ := by
  refine LinearMap.ext fun ρ ↦ ?_
  rw [familyTrace_apply_of_forall_notMem (Φ := Pi.single (M := fun j ↦ MatrixMap A (B j)) i Φ)
    (s := {i}) (fun j hj ↦ by rw [Pi.single_eq_of_ne (Finset.notMem_singleton.mp hj)]) ρ,
    Finset.sum_singleton, Pi.single_eq_same]
  rfl

/-- For a common codomain, the trace functional of a family summable on every input is the trace
after its sum. -/
theorem familyTrace_eq_trace_familySum {B : Type*} [Fintype B] {Φ : ι → MatrixMap A B}
    (h : ∀ ρ, Summable fun i ↦ Φ i ρ) :
    familyTrace Φ = Matrix.traceLinearMap B ℂ ℂ ∘ₗ familySum Φ :=
  LinearMap.ext fun ρ ↦ by
    rw [familyTrace_apply fun ρ ↦ Matrix.summable_trace (h ρ), LinearMap.comp_apply,
      Matrix.traceLinearMap_apply, trace_familySum_apply h]

/-- For a common codomain, the sum of a family summable on every input is trace preserving
exactly when the trace functional of the family is the trace. -/
theorem isTP_familySum_iff [Fintype A] {B : Type*} [Fintype B] {Φ : ι → MatrixMap A B}
    (h : ∀ ρ, Summable fun i ↦ Φ i ρ) :
    (familySum Φ).IsTP ↔ ∀ ρ : Matrix A A ℂ, familyTrace Φ ρ = ρ.trace := by
  rw [familyTrace_eq_trace_familySum h]
  rfl

/-- The trace functional of a family amplified by `R` sums the trace functional of the family on
the diagonal ancilla blocks. -/
theorem familyTrace_mapRange_amplify {R : Type*} [Fintype R] {Φ : (i : ι) → MatrixMap A (B i)}
    (h : ∀ ρ, Summable fun i ↦ (Φ i ρ).trace) (ρ : Matrix (A × R) (A × R) ℂ) :
    familyTrace (fun i ↦ (Φ i).amplify R) ρ = ∑ r, familyTrace Φ (ρ.submatrix (·, r) (·, r)) := by
  have h' : ∀ ρ : Matrix (A × R) (A × R) ℂ, Summable fun i ↦ ((Φ i).amplify R ρ).trace :=
    fun ρ ↦ by
      simp_rw [trace_amplify_apply]
      exact summable_sum fun r _ ↦ h _
  rw [familyTrace_apply h', tsum_congr fun i ↦ trace_amplify_apply (Φ i) ρ,
    Summable.tsum_finsetSum fun r _ ↦ h _]
  exact Finset.sum_congr rfl fun r _ ↦ (familyTrace_apply h _).symm

end familyTrace

/-! ## Kleisli composition -/

section familyBind

variable {B : ι → Type*} {C : κ → Type*} {E : μ → Type*}

/-- Kleisli composition of families of matrix maps whose codomains may depend on the label: the
family whose member at `c` is the sum `familySum fun i ↦ Ψ i c ∘ₗ Φ i`. For completely positive
families with trace-nonincreasing partial sums it is again such a family
(`Quantum.MatrixMap.IsCPTNIFamily.familyBind`), with member at `c` the pointwise sum
`ρ ↦ ∑' i, Ψ i c (Φ i ρ)` (`Quantum.MatrixMap.familyBind_apply`). -/
@[expose]
noncomputable def familyBind (Φ : (i : ι) → MatrixMap A (B i))
    (Ψ : (i : ι) → (c : κ) → MatrixMap (B i) (C c)) (c : κ) : MatrixMap A (C c) :=
  familySum fun i ↦ Ψ i c ∘ₗ Φ i

/-- The member of a Kleisli composite at `c`, as a sum over any finite set outside which the
first family vanishes. -/
theorem familyBind_apply_of_forall_notMem {Φ : (i : ι) → MatrixMap A (B i)}
    (Ψ : (i : ι) → (c : κ) → MatrixMap (B i) (C c)) {s : Finset ι} (hs : ∀ i ∉ s, Φ i = 0)
    (c : κ) : familyBind Φ Ψ c = ∑ i ∈ s, Ψ i c ∘ₗ Φ i :=
  familySum_eq_sum_of_forall_notMem fun i hi ↦ by rw [hs i hi, LinearMap.comp_zero]

/-- The member of a Kleisli composite at `c`, as a sum over a finite type of labels. -/
theorem familyBind_apply_univ [Fintype ι] (Φ : (i : ι) → MatrixMap A (B i))
    (Ψ : (i : ι) → (c : κ) → MatrixMap (B i) (C c)) (c : κ) :
    familyBind Φ Ψ c = ∑ i, Ψ i c ∘ₗ Φ i :=
  familyBind_apply_of_forall_notMem Ψ (fun i hi ↦ absurd (Finset.mem_univ i) hi) c

/-- A Kleisli composite vanishes at `c` when the first family vanishes outside a finite set `s`
and every continuation reached from `s` vanishes at `c`. -/
theorem familyBind_apply_eq_zero {Φ : (i : ι) → MatrixMap A (B i)}
    (Ψ : (i : ι) → (c : κ) → MatrixMap (B i) (C c)) {s : Finset ι} (hs : ∀ i ∉ s, Φ i = 0)
    {c : κ} (hc : ∀ i ∈ s, Ψ i c = 0) : familyBind Φ Ψ c = 0 := by
  rw [familyBind_apply_of_forall_notMem Ψ hs]
  exact Finset.sum_eq_zero fun i hi ↦ by rw [hc i hi, LinearMap.zero_comp]

/-- Binding the zero family gives the zero family. -/
@[simp]
theorem zero_familyBind (Ψ : (i : ι) → (c : κ) → MatrixMap (B i) (C c)) :
    familyBind (0 : (i : ι) → MatrixMap A (B i)) Ψ = 0 :=
  funext fun c ↦ by
    rw [familyBind_apply_of_forall_notMem Ψ (Φ := 0) (s := ∅) (fun _ _ ↦ rfl), Finset.sum_empty]
    rfl

/-- Binding the zero continuations gives the zero family. -/
@[simp]
theorem familyBind_zero (Φ : (i : ι) → MatrixMap A (B i)) :
    familyBind Φ (0 : (i : ι) → (c : κ) → MatrixMap (B i) (C c)) = 0 :=
  funext fun c ↦ by
    have h : (fun i ↦ (0 : (i : ι) → (c : κ) → MatrixMap (B i) (C c)) i c ∘ₗ Φ i) = 0 :=
      funext fun i ↦ LinearMap.zero_comp _
    rw [familyBind, h, familySum_zero]
    rfl

/-- Left unit law: binding the unit family at `i` selects the continuation at `i`. -/
@[simp]
theorem single_id_familyBind [DecidableEq ι] (i : ι)
    (Ψ : (j : ι) → (c : κ) → MatrixMap (B j) (C c)) :
    familyBind (B := B) (Pi.single i (LinearMap.id : MatrixMap (B i) (B i))) Ψ = Ψ i :=
  funext fun c ↦ by
    rw [familyBind_apply_of_forall_notMem Ψ (s := {i})
      (fun j hj ↦ Pi.single_eq_of_ne (Finset.notMem_singleton.mp hj) _),
      Finset.sum_singleton, Pi.single_eq_same, LinearMap.comp_id]

/-- Right unit law: binding with the unit families is the identity. -/
@[simp]
theorem familyBind_single_id [DecidableEq ι] (Φ : (i : ι) → MatrixMap A (B i)) :
    familyBind Φ (fun i ↦ Pi.single (M := fun j ↦ MatrixMap (B i) (B j)) i LinearMap.id) =
      Φ :=
  funext fun c ↦ by
    rw [familyBind, familySum_eq_sum_of_forall_notMem (s := {c}) fun i hi ↦ by
      rw [Pi.single_eq_of_ne (Ne.symm (Finset.notMem_singleton.mp hi)), LinearMap.zero_comp],
      Finset.sum_singleton, Pi.single_eq_same, LinearMap.id_comp]

/-- Amplifying every member of a Kleisli composite by `R` gives the Kleisli composite of the
amplified families. This holds for all families. -/
theorem familyBind_mapRange_amplify (R : Type*) (Φ : (i : ι) → MatrixMap A (B i))
    (Ψ : (i : ι) → (c : κ) → MatrixMap (B i) (C c)) :
    (fun c ↦ (familyBind Φ Ψ c).amplify R) =
      familyBind (fun i ↦ (Φ i).amplify R) fun i c ↦ (Ψ i c).amplify R :=
  funext fun c ↦ by
    rw [familyBind, amplify_familySum]
    rfl

/-! ### Summable Kleisli composites

The laws below hold for all families of matrix maps whose composites are summable as needed.
Their hypotheses say exactly which sums must converge: those that make the sums in the statement
pointwise sums, and the joint summability over pairs of labels that justifies exchanging two
sums. Completely positive families with trace-nonincreasing partial sums satisfy all of them, and
the corresponding laws for such families follow below. -/

/-- The member of a Kleisli composite at `c` is the pointwise sum `ρ ↦ ∑' i, Ψ i c (Φ i ρ)` when
these sums converge on every input. -/
theorem familyBind_apply_of_summable {Φ : (i : ι) → MatrixMap A (B i)}
    {Ψ : (i : ι) → (c : κ) → MatrixMap (B i) (C c)} {c : κ}
    (h : ∀ ρ, Summable fun i ↦ Ψ i c (Φ i ρ)) (ρ : Matrix A A ℂ) :
    familyBind Φ Ψ c ρ = ∑' i, Ψ i c (Φ i ρ) :=
  familySum_apply (Φ := fun i ↦ Ψ i c ∘ₗ Φ i) h ρ

/-- **Associativity** of Kleisli composition of summable families. The hypotheses are that each
member of the first composite is a pointwise sum (`hΦΨ`), that each member of the second
composite is a pointwise sum (`hΨΧ`), and that the three-step composites are jointly summable
over pairs of labels (`hΦΨΧ`), which justifies exchanging the two sums. -/
theorem familyBind_assoc_of_summable [∀ c, Finite (C c)] {Φ : (i : ι) → MatrixMap A (B i)}
    {Ψ : (i : ι) → (c : κ) → MatrixMap (B i) (C c)} {Χ : (c : κ) → (m : μ) → MatrixMap (C c) (E m)}
    (hΦΨ : ∀ c ρ, Summable fun i ↦ Ψ i c (Φ i ρ))
    (hΨΧ : ∀ i m σ, Summable fun c ↦ Χ c m (Ψ i c σ))
    (hΦΨΧ : ∀ m ρ, Summable fun x : ι × κ ↦ Χ x.2 m (Ψ x.1 x.2 (Φ x.1 ρ))) :
    familyBind (familyBind Φ Ψ) Χ = familyBind Φ fun i ↦ familyBind (Ψ i) Χ := by
  funext m
  have hL : ∀ ρ c, Χ c m (familyBind Φ Ψ c ρ) = ∑' i, Χ c m (Ψ i c (Φ i ρ)) := fun ρ c ↦ by
    rw [familyBind_apply_of_summable (Φ := Φ) (Ψ := Ψ) (hΦΨ c), map_tsum (Χ c m) (hΦΨ c ρ)]
  have hR : ∀ ρ i, familyBind (Ψ i) Χ m (Φ i ρ) = ∑' c, Χ c m (Ψ i c (Φ i ρ)) := fun ρ i ↦
    familyBind_apply_of_summable (Φ := Ψ i) (Ψ := Χ) (hΨΧ i m) (Φ i ρ)
  refine LinearMap.ext fun ρ ↦ ?_
  rw [familyBind, familySum_apply (Φ := fun c ↦ Χ c m ∘ₗ familyBind Φ Ψ c)
      (fun ρ ↦ (hΦΨΧ m ρ).prod_symm.prod.congr fun c ↦ (hL ρ c).symm),
    familyBind, familySum_apply (Φ := fun i ↦ familyBind (Ψ i) Χ m ∘ₗ Φ i)
      (fun ρ ↦ (hΦΨΧ m ρ).prod.congr fun i ↦ (hR ρ i).symm)]
  simp only [LinearMap.comp_apply, hL, hR]
  exact Summable.tsum_comm (f := fun i c ↦ Χ c m (Ψ i c (Φ i ρ))) (hΦΨΧ m ρ)

/-- The sum of a Kleisli composite with a common final codomain sums, over the members of the
first family, the sum of the continuation after that member. The hypotheses are that each member
of the composite is a pointwise sum (`hΦΨ`), that each continuation is summable on every input
(`hΨ`), and that the composites are jointly summable over pairs of labels (`hΦΨ'`). -/
theorem familySum_familyBind_of_summable {D : Type*} {Φ : (i : ι) → MatrixMap A (B i)}
    {Ψ : (i : ι) → κ → MatrixMap (B i) D} (hΦΨ : ∀ c ρ, Summable fun i ↦ Ψ i c (Φ i ρ))
    (hΨ : ∀ i σ, Summable fun c ↦ Ψ i c σ)
    (hΦΨ' : ∀ ρ, Summable fun x : ι × κ ↦ Ψ x.1 x.2 (Φ x.1 ρ)) :
    familySum (familyBind Φ Ψ) = familySum fun i ↦ familySum (Ψ i) ∘ₗ Φ i := by
  have hL : ∀ ρ c, familyBind Φ Ψ c ρ = ∑' i, Ψ i c (Φ i ρ) := fun ρ c ↦
    familyBind_apply_of_summable (Φ := Φ) (Ψ := Ψ) (hΦΨ c) ρ
  have hR : ∀ ρ i, familySum (Ψ i) (Φ i ρ) = ∑' c, Ψ i c (Φ i ρ) := fun ρ i ↦
    familySum_apply (Φ := Ψ i) (hΨ i) (Φ i ρ)
  refine LinearMap.ext fun ρ ↦ ?_
  rw [familySum_apply (Φ := familyBind Φ Ψ)
      (fun ρ ↦ (hΦΨ' ρ).prod_symm.prod.congr fun c ↦ (hL ρ c).symm),
    familySum_apply (Φ := fun i ↦ familySum (Ψ i) ∘ₗ Φ i)
      (fun ρ ↦ (hΦΨ' ρ).prod.congr fun i ↦ (hR ρ i).symm)]
  simp only [LinearMap.comp_apply, hL, hR]
  exact Summable.tsum_comm (f := fun i c ↦ Ψ i c (Φ i ρ)) (hΦΨ' ρ)

/-- The trace functional of a Kleisli composite sums, over the members of the first family, the
trace functional of the continuation after that member. The hypotheses are that each member of
the composite is a pointwise sum (`hΦΨ`), that the traces of each continuation are summable on
every input (`hΨ`), and that the traces of the composites are jointly summable over pairs of
labels (`hΦΨ'`). -/
theorem familyTrace_familyBind_of_summable [∀ c, Fintype (C c)] {Φ : (i : ι) → MatrixMap A (B i)}
    {Ψ : (i : ι) → (c : κ) → MatrixMap (B i) (C c)}
    (hΦΨ : ∀ c ρ, Summable fun i ↦ Ψ i c (Φ i ρ))
    (hΨ : ∀ i σ, Summable fun c ↦ (Ψ i c σ).trace)
    (hΦΨ' : ∀ ρ, Summable fun x : ι × κ ↦ (Ψ x.1 x.2 (Φ x.1 ρ)).trace) (ρ : Matrix A A ℂ) :
    familyTrace (familyBind Φ Ψ) ρ = ∑' i, familyTrace (Ψ i) (Φ i ρ) := by
  have hL : ∀ ρ c, (familyBind Φ Ψ c ρ).trace = ∑' i, (Ψ i c (Φ i ρ)).trace := fun ρ c ↦ by
    rw [familyBind_apply_of_summable (Φ := Φ) (Ψ := Ψ) (hΦΨ c), Matrix.trace_tsum (hΦΨ c ρ)]
  rw [familyTrace_apply (Φ := familyBind Φ Ψ)
      (fun ρ ↦ (hΦΨ' ρ).prod_symm.prod.congr fun c ↦ (hL ρ c).symm),
    tsum_congr (hL ρ), tsum_congr fun i ↦ familyTrace_apply (Φ := Ψ i) (hΨ i) (Φ i ρ)]
  exact Summable.tsum_comm (f := fun i c ↦ (Ψ i c (Φ i ρ)).trace) (hΦΨ' ρ)

/-! ### Completely positive families -/

variable [Fintype A] [∀ i, Fintype (B i)] [∀ c, Fintype (C c)] [∀ m, Fintype (E m)]

/-- The member of a Kleisli composite of completely positive families with trace-nonincreasing
partial sums at `c` is the pointwise sum `ρ ↦ ∑' i, Ψ i c (Φ i ρ)`. -/
theorem familyBind_apply {Φ : (i : ι) → MatrixMap A (B i)}
    {Ψ : (i : ι) → (c : κ) → MatrixMap (B i) (C c)} (hΦ : IsCPTNIFamily Φ)
    (hΨ : ∀ i, IsCPTNIFamily (Ψ i)) (c : κ) (ρ : Matrix A A ℂ) :
    familyBind Φ Ψ c ρ = ∑' i, Ψ i c (Φ i ρ) :=
  (hΦ.comp_eval hΨ c).familySum_apply ρ

/-- The real part of the trace of a member of a Kleisli composite of completely positive families
with trace-nonincreasing partial sums. -/
theorem trace_re_familyBind_apply {Φ : (i : ι) → MatrixMap A (B i)}
    {Ψ : (i : ι) → (c : κ) → MatrixMap (B i) (C c)} (hΦ : IsCPTNIFamily Φ)
    (hΨ : ∀ i, IsCPTNIFamily (Ψ i)) (c : κ) (ρ : Matrix A A ℂ) :
    (familyBind Φ Ψ c ρ).trace.re = ∑' i, (Ψ i c (Φ i ρ)).trace.re := by
  rw [familyBind, trace_familySum_apply (hΦ.comp_eval hΨ c).summable_apply,
    (hΦ.comp_eval hΨ c).re_tsum_trace_apply]
  rfl

/-- A Kleisli composite of completely positive families with trace-nonincreasing partial sums is
again such a family. -/
theorem IsCPTNIFamily.familyBind {Φ : (i : ι) → MatrixMap A (B i)}
    {Ψ : (i : ι) → (c : κ) → MatrixMap (B i) (C c)} (hΦ : IsCPTNIFamily Φ)
    (hΨ : ∀ i, IsCPTNIFamily (Ψ i)) : IsCPTNIFamily (MatrixMap.familyBind Φ Ψ) where
  isCP c := isCP_familySum fun i ↦ ((hΨ i).isCP c).comp (hΦ.isCP i)
  sum_trace_re_le s ρ hρ := by
    have hs : ∀ c, Summable fun i ↦ (Ψ i c (Φ i ρ)).trace.re := fun c ↦
      (hΦ.comp_eval hΨ c).summable_trace_re_apply hρ
    calc ∑ c ∈ s, (MatrixMap.familyBind Φ Ψ c ρ).trace.re
        = ∑ c ∈ s, ∑' i, (Ψ i c (Φ i ρ)).trace.re :=
          Finset.sum_congr rfl fun c _ ↦ trace_re_familyBind_apply hΦ hΨ c ρ
      _ = ∑' i, ∑ c ∈ s, (Ψ i c (Φ i ρ)).trace.re :=
          (Summable.tsum_finsetSum fun c _ ↦ hs c).symm
      _ ≤ ∑' i, (Φ i ρ).trace.re :=
          Summable.tsum_le_tsum
            (fun i ↦ (hΨ i).sum_trace_re_le s _ (hΦ.posSemidef_apply i hρ))
            (summable_sum fun c _ ↦ hs c) (hΦ.summable_trace_re_apply hρ)
      _ ≤ ρ.trace.re := hΦ.tsum_trace_re_apply_le hρ

/-- Associativity of Kleisli composition of completely positive families with
trace-nonincreasing partial sums. Such families satisfy the summability hypotheses of
`Quantum.MatrixMap.familyBind_assoc_of_summable`; the joint summability over pairs of labels comes
from `Quantum.MatrixMap.IsCPTNIFamily.prod`. -/
theorem familyBind_assoc {Φ : (i : ι) → MatrixMap A (B i)}
    {Ψ : (i : ι) → (c : κ) → MatrixMap (B i) (C c)} {Χ : (c : κ) → (m : μ) → MatrixMap (C c) (E m)}
    (hΦ : IsCPTNIFamily Φ) (hΨ : ∀ i, IsCPTNIFamily (Ψ i)) (hΧ : ∀ c, IsCPTNIFamily (Χ c)) :
    familyBind (familyBind Φ Ψ) Χ = familyBind Φ fun i ↦ familyBind (Ψ i) Χ :=
  familyBind_assoc_of_summable (fun c ↦ (hΦ.comp_eval hΨ c).summable_apply)
    (fun i m ↦ ((hΨ i).comp_eval hΧ m).summable_apply)
    fun m ↦ ((hΦ.prod hΨ).comp_eval (fun x ↦ hΧ x.2) m).summable_apply

/-- The sum of a Kleisli composite of completely positive families with trace-nonincreasing
partial sums and a common final codomain sums, over the members of the first family, the sum of
the continuation after that member. This is `Quantum.MatrixMap.familySum_familyBind_of_summable`
for such families. -/
theorem familySum_familyBind {D : Type*} [Fintype D] {Φ : (i : ι) → MatrixMap A (B i)}
    {Ψ : (i : ι) → κ → MatrixMap (B i) D} (hΦ : IsCPTNIFamily Φ)
    (hΨ : ∀ i, IsCPTNIFamily (Ψ i)) :
    familySum (familyBind Φ Ψ) = familySum fun i ↦ familySum (Ψ i) ∘ₗ Φ i :=
  familySum_familyBind_of_summable (fun c ↦ (hΦ.comp_eval hΨ c).summable_apply)
    (fun i ↦ (hΨ i).summable_apply) (hΦ.prod hΨ).summable_apply

/-- The trace functional of a Kleisli composite of completely positive families with
trace-nonincreasing partial sums sums, over the members of the first family, the trace
functional of the continuation after that member. This is
`Quantum.MatrixMap.familyTrace_familyBind_of_summable` for such families. -/
theorem familyTrace_familyBind {Φ : (i : ι) → MatrixMap A (B i)}
    {Ψ : (i : ι) → (c : κ) → MatrixMap (B i) (C c)} (hΦ : IsCPTNIFamily Φ)
    (hΨ : ∀ i, IsCPTNIFamily (Ψ i)) (ρ : Matrix A A ℂ) :
    familyTrace (familyBind Φ Ψ) ρ = ∑' i, familyTrace (Ψ i) (Φ i ρ) :=
  familyTrace_familyBind_of_summable (fun c ↦ (hΦ.comp_eval hΨ c).summable_apply)
    (fun i ↦ (hΨ i).summable_trace_apply) (hΦ.prod hΨ).summable_trace_apply ρ

end familyBind

end MatrixMap

end Quantum
