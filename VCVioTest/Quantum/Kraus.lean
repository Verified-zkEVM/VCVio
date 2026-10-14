/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.Quantum.SubInstrument

/-!
# Choi matrix and Kraus decomposition regression tests

On a system with an arbitrary finite basis `A`:

* the Choi matrix of the identity channel is the unnormalized maximally entangled matrix, and
  comparing Choi matrices shows that the identity channel has the single Kraus operator `1`;
* the completely dephasing channel `ρ ↦ diagonal (diag ρ)` has Choi matrix supported on the
  diagonal of `A × A`, and comparing Choi matrices gives its Kraus operators `single a a 1`; it is
  trace preserving, and the converse of the trace condition recovers the completeness relation;
* keeping only the diagonal entries in a set `S` of basis states, the branch of a
  computational-basis measurement on the event `S`, is trace nonincreasing, and the converse of
  the trace condition gives `∑ a : S, (single a a 1)ᴴ * single a a 1 ≤ 1` in the Loewner order;
* the computational-basis measurement, as a subinstrument, has Kraus operators for all branches
  at once satisfying the completeness relation, and measuring twice has the path operators
  `single b b 1 * single a a 1`.
-/

public section

open Quantum Matrix
open scoped ComplexOrder

namespace VCVioTest.QuantumKraus

variable {A : Type*} [DecidableEq A]

/-! ## The identity channel -/

/-- The Choi matrix of the identity channel is the unnormalized maximally entangled matrix. -/
theorem choi_id :
    MatrixMap.choi (LinearMap.id : MatrixMap A A) =
      Matrix.of fun x y ↦ if x.2 = x.1 ∧ y.2 = y.1 then 1 else 0 := by
  ext x y
  simp [Matrix.single_apply]

/-- The identity channel has the single Kraus operator `1`, by comparison of Choi matrices. -/
theorem id_eq_sum_conj [Fintype A] :
    (LinearMap.id : MatrixMap A A) = ∑ _ : Unit, MatrixMap.conj (1 : Matrix A A ℂ) := by
  rw [← MatrixMap.choi_inj]
  ext x y
  rw [MatrixMap.choi_sum_conj_apply, choi_id]
  simp only [Matrix.of_apply, Matrix.one_apply, Finset.univ_unique, Finset.sum_singleton]
  split_ifs <;> simp_all [eq_comm]

/-- The identity channel is recovered from its Choi matrix. -/
example [Fintype A] :
    MatrixMap.ofChoi (Matrix.of fun x y : A × A ↦ if x.2 = x.1 ∧ y.2 = y.1 then 1 else 0) =
      (LinearMap.id : MatrixMap A A) := by
  rw [← choi_id, MatrixMap.ofChoi_choi]

/-! ## The completely dephasing channel -/

/-- The completely dephasing channel: it keeps the diagonal of its input. -/
@[expose]
def dephase : MatrixMap A A where
  toFun ρ := Matrix.diagonal (Matrix.diag ρ)
  map_add' ρ σ := by
    ext i j
    by_cases h : i = j <;> simp [h]
  map_smul' c ρ := by
    ext i j
    by_cases h : i = j <;> simp [h]

/-- The completely dephasing channel keeps the diagonal of its input. -/
theorem dephase_apply (ρ : Matrix A A ℂ) : dephase ρ = Matrix.diagonal (Matrix.diag ρ) :=
  rfl

/-- The Choi matrix of the completely dephasing channel is supported on `x.1 = x.2 = y.1 = y.2`.
-/
theorem choi_dephase :
    MatrixMap.choi (dephase : MatrixMap A A) =
      Matrix.of fun x y ↦ if x.1 = y.1 ∧ x.2 = x.1 ∧ y.2 = x.1 then 1 else 0 := by
  ext x y
  by_cases h : x.1 = y.1 <;> simp [dephase_apply, Matrix.single_apply, h]

/-- The completely dephasing channel has Kraus operators `single a a 1`, by comparison of Choi
matrices. -/
theorem dephase_eq_sum_conj [Fintype A] :
    (dephase : MatrixMap A A) = ∑ a, MatrixMap.conj (Matrix.single a a (1 : ℂ)) := by
  rw [← MatrixMap.choi_inj]
  ext x y
  rw [MatrixMap.choi_sum_conj_apply, choi_dephase]
  simp only [Matrix.of_apply, Matrix.single_apply]
  rw [Finset.sum_eq_single x.1 (fun a _ ha ↦ by simp [ha]) (by simp)]
  split_ifs <;> simp_all
  grind

/-- The completely dephasing channel is completely positive. -/
theorem isCP_dephase [Finite A] : (dephase : MatrixMap A A).IsCP := by
  cases nonempty_fintype A
  rw [dephase_eq_sum_conj]
  exact MatrixMap.isCP_sum_conj _

/-- The completely dephasing channel is trace preserving. -/
theorem isTP_dephase [Fintype A] : (dephase : MatrixMap A A).IsTP := fun ρ ↦ by
  simp [dephase_apply, Matrix.trace]

/-- The converse of the trace-preservation condition recovers the completeness relation of the
diagonal matrix units. -/
theorem sum_conjTranspose_single_mul_single [Fintype A] :
    ∑ a : A, (Matrix.single a a (1 : ℂ))ᴴ * Matrix.single a a 1 = 1 :=
  MatrixMap.isTP_sum_conj_iff.mp (by rw [← dephase_eq_sum_conj]; exact isTP_dephase)

/-- The general theorem gives the completely dephasing channel some Kraus operators. -/
example [Fintype A] :
    ∃ K : A × A → Matrix A A ℂ, (dephase : MatrixMap A A) = ∑ k, MatrixMap.conj (K k) :=
  isCP_dephase.exists_kraus

/-! ## Measurement on an event -/

/-- Keeping the diagonal entries of the input at the basis states in `S` and discarding the rest:
the branch of a computational-basis measurement on the event `S`. -/
def measureIn [Fintype A] (S : Finset A) : MatrixMap A A :=
  ∑ a : S, MatrixMap.conj (Matrix.single (a : A) (a : A) (1 : ℂ))

/-- The diagonal matrix units form a completely positive family with trace-nonincreasing
partial sums. -/
theorem isCPTNIFamily_single [Fintype A] :
    MatrixMap.IsCPTNIFamily fun a : A ↦ MatrixMap.conj (Matrix.single a a (1 : ℂ)) :=
  .of_fintype (fun a ↦ MatrixMap.isCP_conj _) fun ρ hρ ↦ by
    have h := isTP_dephase (A := A)
    rw [dephase_eq_sum_conj] at h
    simpa only [MatrixMap.trace_re_sum_apply] using h.isTNI ρ hρ

/-- Measurement on an event is trace nonincreasing. -/
theorem isTNI_measureIn [Fintype A] (S : Finset A) : (measureIn S).IsTNI := by
  rw [measureIn, Finset.sum_coe_sort S fun a ↦ MatrixMap.conj (Matrix.single a a (1 : ℂ))]
  exact isCPTNIFamily_single.isTNI_sum S

open scoped MatrixOrder in
/-- The converse of the trace-nonincrease condition: the Kraus operators of measurement on an
event satisfy `∑ a : S, (single a a 1)ᴴ * single a a 1 ≤ 1`. -/
example [Fintype A] (S : Finset A) :
    ∑ a : S, (Matrix.single (a : A) (a : A) (1 : ℂ))ᴴ * Matrix.single (a : A) (a : A) 1 ≤ 1 :=
  Matrix.le_iff.mpr (MatrixMap.isTNI_sum_conj_iff.mp (isTNI_measureIn S))

/-! ## Instruments -/

/-- The computational-basis measurement as a subinstrument. -/
noncomputable def measure [Fintype A] : SubInstrument A A A :=
  SubInstrument.ofKraus (fun a ↦ Matrix.single a a (1 : ℂ)) sum_conjTranspose_single_mul_single

/-- The computational-basis measurement has Kraus operators for all branches at once, with the
completeness relation. -/
example [Fintype A] : ∃ K : A → A × A → Matrix A A ℂ,
    (∀ a, (measure : SubInstrument A A A).branch a = ∑ k, MatrixMap.conj (K a k)) ∧
      ∑ a, ∑ k, (K a k)ᴴ * K a k = 1 :=
  (SubInstrument.lossless_ofKraus _ _).exists_kraus

/-- Each branch of a measurement has Kraus operators. -/
example [Fintype A] (a : A) :
    ∃ K : A × A → Matrix A A ℂ, (measure : SubInstrument A A A).branch a =
      ∑ k, MatrixMap.conj (K k) :=
  measure.exists_kraus_branch a

/-- Measuring twice: the branch at `b` sums the Kraus maps of the path operators
`single b b 1 * single a a 1`. -/
example [Fintype A] (b : A) :
    ((measure : SubInstrument A A A).bind fun _ ↦ measure).branch b =
      ∑ x : A × Unit × Unit,
        MatrixMap.conj (Matrix.single b b (1 : ℂ) * Matrix.single x.1 x.1 1) :=
  SubInstrument.branch_bind_eq_sum_conj_mul _ _ (K := fun a _ ↦ Matrix.single a a 1)
    (L := fun _ b _ ↦ Matrix.single b b 1) (fun _ ↦ by simp [measure])
    (fun _ _ ↦ by simp [measure]) b

end VCVioTest.QuantumKraus
