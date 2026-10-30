/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.Quantum.Semantics

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

Explicit calculations also check a complex rectangular Choi matrix, direct Stinespring recovery
of qubit dephasing, and a noncommuting postselection/bit-flip path. Ordinary-import canaries
check constant-output relabelling after sequencing and framing, chained losslessness proofs,
and rewrites with the constant-output laws.
-/

public section

open Quantum Matrix
open scoped ComplexOrder

namespace VCVioTest.QuantumKraus

/-! ## Constant-output composition through ordinary imports -/

noncomputable section constantOutput

variable {A B C α β γ : Type*} [Fintype A] [Fintype B] [Fintype C]

/-- Relabelling after sequencing infers the output system without an expected type. -/
example (p : SubInstrument A B α) (k : α → SubInstrument B C β) (f : β → γ) :=
  (p.bind k).map f

/-- Relabelling after framing infers the extended output system. -/
example (p : SubInstrument A B α) (f : α → β) := (p.frame Unit).map f

/-- Sequencing and relabelling preserve losslessness by chained field notation. -/
example (p : SubInstrument A B α) (k : α → SubInstrument B C β)
    (hp : p.Lossless) (hk : ∀ a, (k a).Lossless) (f : β → γ) :
    ((p.bind k).map f).Lossless := by
  exact (hp.bind hk).map f

/-- Framing and relabelling preserve losslessness by chained field notation. -/
example (p : SubInstrument A B α) (hp : p.Lossless) (f : α → β) :
    ((p.frame Unit).map f).Lossless := by
  exact (hp.frame Unit).map f

/-- Dependent total-map laws simplify framed and relabelled constant-output computations. -/
example (p : SubInstrument A B α) (f : α → β) :
    ((p.frame Unit).map f).total = p.total.amplify Unit := by
  simp

/-- The right unit law rewrites the constant bind facade. -/
example (p : SubInstrument A B α) : p.bind SubInstrument.pure = p := by
  rw [SubInstrument.bind_pure]

/-- The left unit law rewrites constant return followed by constant bind. -/
example (a : α) (k : α → SubInstrument A B β) : (SubInstrument.pure a).bind k = k a := by
  rw [SubInstrument.pure_bind]

/-- Associativity rewrites nested constant binds. -/
example {D : Type*} [Fintype D] (p : SubInstrument A B α)
    (k : α → SubInstrument B C β) (l : β → SubInstrument C D γ) :
    (p.bind k).bind l = p.bind fun a ↦ (k a).bind l := by
  rw [SubInstrument.bind_assoc]

/-- Relabelling rewrites to a constant bind followed by return. -/
example (p : SubInstrument A B α) (f : α → β) :
    p.map f = p.bind fun a ↦ SubInstrument.pure (f a) := by
  rw [SubInstrument.map_eq_bind_pure]

/-- Failure before sequencing rewrites through the constant facades. -/
example (k : α → SubInstrument B C β) :
    (SubInstrument.fail : SubInstrument A B α).bind k = SubInstrument.fail := by
  rw [SubInstrument.fail_bind]

/-- Failing continuations rewrite through the constant bind facade. -/
example (p : SubInstrument A B α) :
    (p.bind fun _ ↦ SubInstrument.fail : SubInstrument A C β) = SubInstrument.fail := by
  rw [SubInstrument.bind_fail]

/-- Framing rewrites through constant sequencing. -/
example (p : SubInstrument A B α) (k : α → SubInstrument B C β) :
    (p.bind k).frame Unit = (p.frame Unit).bind fun a ↦ (k a).frame Unit := by
  rw [SubInstrument.frame_bind]

/-- Framing constant return rewrites to return on the extended register. -/
example (a : α) : (SubInstrument.pure a : SubInstrument A A α).frame Unit =
    (SubInstrument.pure a : SubInstrument (A × Unit) (A × Unit) α) := by
  rw [SubInstrument.frame_pure]

end constantOutput

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
def measureBasisEvent [Fintype A] (S : Finset A) : MatrixMap A A :=
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
theorem isTNI_measureBasisEvent [Fintype A] (S : Finset A) : (measureBasisEvent S).IsTNI := by
  rw [measureBasisEvent, Finset.sum_coe_sort S fun a ↦ MatrixMap.conj (Matrix.single a a (1 : ℂ))]
  exact isCPTNIFamily_single.isTNI_sum S

open scoped MatrixOrder in
/-- The converse of the trace-nonincrease condition: the Kraus operators of measurement on an
event satisfy `∑ a : S, (single a a 1)ᴴ * single a a 1 ≤ 1`. -/
example [Fintype A] (S : Finset A) :
    ∑ a : S, (Matrix.single (a : A) (a : A) (1 : ℂ))ᴴ * Matrix.single (a : A) (a : A) 1 ≤ 1 :=
  Matrix.le_iff.mpr (MatrixMap.isTNI_sum_conj_iff.mp (isTNI_measureBasisEvent S))

/-! ## Instruments -/

/-- The computational-basis measurement as a subinstrument. -/
noncomputable def measure [Fintype A] : SubInstrument A A A :=
  SubInstrument.ofKraus (fun a ↦ Matrix.single a a (1 : ℂ)) sum_conjTranspose_single_mul_single

/-- The computational-basis measurement has Kraus operators for all branches at once, with the
completeness relation. -/
example [Fintype A] : ∃ K : A → A × A → Matrix A A ℂ,
    (∀ a, measure.branch a = ∑ k, MatrixMap.conj (K a k)) ∧
      ∑ a, ∑ k, (K a k)ᴴ * K a k = 1 :=
  (DSubInstrument.lossless_ofKraus (fun a ↦ Matrix.single a a (1 : ℂ))
    sum_conjTranspose_single_mul_single).exists_kraus

/-- Each branch of a measurement has Kraus operators. -/
example [Fintype A] (a : A) :
    ∃ K : A × A → Matrix A A ℂ, measure.branch a =
      ∑ k, MatrixMap.conj (K k) :=
  measure.exists_kraus_branch a

/-- Measuring twice: the branch at `b` sums the Kraus maps of the path operators
`single b b 1 * single a a 1`. -/
example [Fintype A] (b : A) :
    (measure.bind fun _ ↦ measure).branch b =
      ∑ x : A × Unit × Unit,
        MatrixMap.conj (Matrix.single b b (1 : ℂ) * Matrix.single x.1 x.1 1) :=
  DSubInstrument.branch_bind_eq_sum_conj_mul _ _ (K := fun a _ ↦ Matrix.single a a 1)
    (L := fun _ b _ ↦ Matrix.single b b 1) (fun _ ↦ by simp [measure])
    (fun _ _ ↦ by simp [measure]) b

/-- The joint completeness theorem elaborates with genuinely different output dimensions:
outcome zero has a one-dimensional output and outcome one has a two-dimensional output. -/
example (p : DSubInstrument (Fin 2) (Fin 2) (fun i ↦ Fin (i.val + 1))) (hp : p.Lossless) :
    ∃ K : (i : Fin 2) → Fin (i.val + 1) × Fin 2 → Matrix (Fin (i.val + 1)) (Fin 2) ℂ,
      (∀ i, p.branch i = ∑ k, MatrixMap.conj (K i k)) ∧
      ∑ i, ∑ k, (K i k)ᴴ * K i k = 1 :=
  hp.exists_kraus

/-! ## Phase and tensor-order calculations -/

/-- A rectangular Kraus operator with a non-real entry. -/
def phaseRect : Matrix (Fin 3) (Fin 2) ℂ :=
  !![1, Complex.I; 0, 0; 0, 0]

-- K = [[1, i], [0, 0], [0, 0]]. In output-first order
-- (0,0), (0,1), (1,0), (1,1), (2,0), (2,1), its Choi matrix has upper-left block
-- [[1, -i], [i, 1]] and all other entries zero. Input-first order moves the i entries.
/-- The exact rectangular Choi matrix records conjugation and output-first tensor order. -/
example :
    MatrixMap.choi (MatrixMap.conj phaseRect) =
      (!![1, -Complex.I, 0, 0, 0, 0;
          Complex.I, 1, 0, 0, 0, 0;
          0, 0, 0, 0, 0, 0;
          0, 0, 0, 0, 0, 0;
          0, 0, 0, 0, 0, 0;
          0, 0, 0, 0, 0, 0] : Matrix (Fin 6) (Fin 6) ℂ).submatrix
        finProdFinEquiv finProdFinEquiv := by
  ext ⟨b, a⟩ ⟨b', a'⟩
  fin_cases b <;> fin_cases a <;> fin_cases b' <;> fin_cases a' <;>
    simp [MatrixMap.choi_apply, MatrixMap.conj_apply, phaseRect, Matrix.mul_apply,
      Matrix.single_apply, Matrix.vecMul, dotProduct, finProdFinEquiv, Matrix.submatrix_apply]

/-! ## Stinespring calculation -/

-- K₀ = [[1, 0], [0, 0]], K₁ = [[0, 0], [0, 1]], so
-- S = [[1, 0], [0, 0], [0, 0], [0, 1]] in output-first order.
-- For ρ = [[a, b], [c, d]], SρS† has corner entries a, b, c, d and zeros elsewhere;
-- tracing the right factor gives [[a, 0], [0, d]].
/-- The qubit dephasing channel is recovered by a Stinespring operator and partial trace. -/
example :
    MatrixMap.traceRight (Fin 2) (Fin 2) ∘ₗ
      MatrixMap.conj (MatrixMap.stinespring fun a : Fin 2 ↦ Matrix.single a a (1 : ℂ)) =
        dephase := by
  apply LinearMap.ext
  intro ρ
  ext b b'
  fin_cases b <;> fin_cases b' <;>
    simp [LinearMap.comp_apply, MatrixMap.traceRight_apply, MatrixMap.conj_apply,
      MatrixMap.stinespring_apply, Matrix.mul_apply, Matrix.single_apply, dephase_apply]

/-! ## Noncommuting Kraus paths -/

/-- The bit-flip operator exchanges the two computational-basis vectors. -/
def bitFlip : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

/-- The bit-flip operator is an isometry. -/
theorem conjTranspose_bitFlip_mul : bitFlipᴴ * bitFlip = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [bitFlip, Matrix.mul_apply]

/-- The single-outcome bit-flip instrument. -/
noncomputable def bitFlipInstrument : SubInstrument (Fin 2) (Fin 2) Unit :=
  SubInstrument.ofKraus (fun _ ↦ bitFlip) (by simpa using conjTranspose_bitFlip_mul)

/-- Postselection on the zero outcome of a computational-basis measurement. -/
noncomputable def postselectZero : SubInstrument (Fin 2) (Fin 2) Unit :=
  SubInstrument.ofMap (MatrixMap.conj (Matrix.single 0 0 1)) (MatrixMap.isCP_conj _)
    (by simpa using (isCPTNIFamily_single (A := Fin 2)).isTNI_sum {0})

-- P₀ = [[1, 0], [0, 0]] and X = [[0, 1], [1, 0]].
-- The unique path has XP₀ = [[0, 0], [1, 0]], while P₀X = [[0, 1], [0, 0]].
/-- Postselection followed by bit flip has the path operator `X * P₀`. -/
theorem postselect_flip_path :
    (postselectZero.bind fun _ ↦ bitFlipInstrument).branch () =
      MatrixMap.conj (bitFlip * Matrix.single 0 0 1) := by
  have h := DSubInstrument.branch_bind_eq_sum_conj_mul postselectZero (fun _ ↦ bitFlipInstrument)
    (K := fun _ _ : Unit ↦ Matrix.single 0 0 (1 : ℂ))
    (L := fun _ _ _ : Unit ↦ bitFlip)
    (fun _ ↦ by simp [postselectZero]) (fun _ _ ↦ by simp [bitFlipInstrument]) ()
  simpa using h

-- On input P₀, the path XP₀ yields P₁ = [[0, 0], [0, 1]].
-- Reversing the path product to P₀X yields the zero matrix on the same input.
/-- The noncommuting path sends the zero basis state to the one basis state. -/
example :
    (postselectZero.bind fun _ ↦ bitFlipInstrument).branch () (Matrix.single 0 0 1) =
      Matrix.single 1 1 1 := by
  rw [postselect_flip_path]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [bitFlip, MatrixMap.conj_apply, Matrix.mul_apply, Matrix.single_apply,
      Matrix.vecMul, dotProduct]

/-- Reversing the operators of the same path annihilates the zero basis state. -/
example :
    MatrixMap.conj (Matrix.single 0 0 1 * bitFlip) (Matrix.single 0 0 1) = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [bitFlip, MatrixMap.conj_apply, Matrix.mul_apply, Matrix.single_apply]

end VCVioTest.QuantumKraus
