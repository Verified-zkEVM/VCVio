/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.Quantum.Oracle.Emulated

/-!
# The tensor-product interface of emulated oracles

In ePrint 2025/2166, §4.1 (p. 28), an adversary queries an emulated oracle
`EO = (Init, (U_i)_i)` on the registers `I ⊗ X_1 ⊗ ⋯ ⊗ X_k`: an index register and one register
per port, all present at every query. A query applies `U = ∑ᵢ |i⟩⟨i|_I ⊗ (U_i)_{X_i S}`, which
acts on `X_i` and the private register `S` when the index is `i`, and as the identity on the
other port registers.

This file formalises that interface and proves it equivalent to the coherent single-port view
`Quantum.EmulatedOracle.coherent` on `Σ i, In i`, against which `VCVio.Quantum.Oracle.Emulated`
states the query masses.

## Main definitions

* `Quantum.EmulatedOracle.tensIn In`: the register `P × ∀ j, In j`, the paper's
  `I ⊗ X_1 ⊗ ⋯ ⊗ X_k`.
* `Quantum.EmulatedOracle.widen`: the emulated oracle whose port `i` acts by `U_i ⊗ 1` on `In i`
  beside the registers of the other ports.
* `Quantum.EmulatedOracle.tensor`: the emulated oracle with one port on `tensIn In`. Its unitary is
  the coherent unitary of `E.widen`, moved along the reindexing
  `P × ∀ j, In j ≃ Σ i, In i × ∀ j ≠ i, In j` of `Equiv.piSplitAt`
  (`Quantum.EmulatedOracle.tensor_U_eq`). Its entries are those of the paper's
  `∑ᵢ |i⟩⟨i| ⊗ U_i ⊗ 1` (`Quantum.EmulatedOracle.tensor_U_apply`).
* `Quantum.EmulatedOracle.tensorMass`: the total mass `TotalMass(A, i)` of Definitions 4.1 and 4.3
  (pp. 28–29) for programs against the tensor-product interface. Its masses add up to the query
  mass of the port (`Quantum.EmulatedOracle.sum_tensorMass`, Remark 4.2). They are the index
  masses of the projectors `Quantum.EmulatedOracle.tensIndexProj` onto the values of the index
  register (`Quantum.EmulatedOracle.tensorMass_eq_indexMass`), a coherent index that the
  tensor-product unitary respects (`Quantum.EmulatedOracle.isCoherentIndex_tensIndexProj`,
  `Quantum.EmulatedOracle.respectsIndex_tensor_U`).

## Main statements

The two interfaces simulate each other by calls through basis embeddings
(`Quantum.QuantumComp.embedCalls`). Both simulations preserve runs, observed laws, the mass on
every index, and query budgets.

* From the tensor-product interface to the coherent one, `Quantum.QuantumComp.tensorToCoherent`
  embeds `|i, x⟩` as `|⟨i, x_i⟩⟩ ⊗ |x[i ↦ x₀]⟩`, with `x₀` a fixed basis element of `In i`: the
  coherent register beside a copy of all the port registers, slot `i` reset. No hypothesis is
  needed. See `Quantum.EmulatedOracle.run_tensorToCoherent`,
  `Quantum.EmulatedOracle.outcomeLawWith_tensorToCoherent`,
  `Quantum.EmulatedOracle.totalMass_tensorToCoherent`,
  `Quantum.EmulatedOracle.lossless_run_tensorToCoherent` and
  `Quantum.QuantumComp.isQueryBound_tensorToCoherent`.
* From the coherent interface to the tensor-product one, `Quantum.QuantumComp.coherentToTensor`
  embeds `|⟨i, a⟩⟩` as `|i, x₀[i ↦ a]⟩`, for a fixed basis element `x₀` of every port register.
  It needs every port register to be nonempty. See `Quantum.EmulatedOracle.run_coherentToTensor`,
  `Quantum.EmulatedOracle.outcomeLawWith_coherentToTensor`,
  `Quantum.EmulatedOracle.tensorMass_coherentToTensor`,
  `Quantum.EmulatedOracle.lossless_run_coherentToTensor` and
  `Quantum.QuantumComp.isQueryBound_coherentToTensor`.

Every adversary against the paper's interface therefore has an adversary against the coherent
view with the same observed laws, the same masses and the same number of queries; conversely
when every port register is nonempty. The hypothesis is needed: with one empty and one nonempty
port register, the tensor-product register is empty and the coherent register is not.

The translations are stated for programs over `Quantum.LocalSig.instruments`, whose local
operations are arbitrary subinstruments.
-/

public section

open Matrix
open scoped ENNReal Kronecker ComplexOrder

universe v w uL vL

namespace Quantum

namespace EmulatedOracle

variable {P : Type} [Fintype P] [DecidableEq P] {In : P → QReg}

/-! ## The tensor-product register and the oracle on it -/

/-- The registers of the ports other than `i`. -/
@[expose, reducible]
def otherIn (In : P → QReg) (i : P) : QReg :=
  QReg.of (∀ j : {j // j ≠ i}, In j)

/-- The tensor-product query register `P × ∀ j, In j`: the index together with the registers of
all the ports (the paper's `I ⊗ X_1 ⊗ ⋯ ⊗ X_k`, p. 28). -/
@[expose, reducible]
def tensIn (In : P → QReg) : QReg :=
  QReg.of (P × ∀ j, In j)

/-- The signature of the tensor-product interface: one unitary port on `tensIn In`. -/
@[expose, reducible]
def tensSpec (In : P → QReg) : QuantumOracleSpec.{0, 0} :=
  uSpec Unit fun _ ↦ tensIn In

/-- The tensor-product register as a direct sum: `(i, x) ↦ ⟨i, (x i, x restricted to j ≠ i)⟩`. -/
@[expose]
def tensEquiv (In : P → QReg) : tensIn In ≃ Σ i, In i × otherIn In i :=
  (Equiv.sigmaEquivProd P (∀ j, In j)).symm.trans
    (Equiv.sigmaCongrRight fun i ↦ Equiv.piSplitAt i fun j ↦ In j)

/-- `tensEquiv` on a basis element. -/
theorem tensEquiv_apply (i : P) (x : ∀ j, In j) :
    tensEquiv In (i, x) = ⟨i, (x i, fun j ↦ x j)⟩ :=
  rfl

/-- Each port acting beside the registers of the other ports: the unitary of the port `i` of
`E.widen` is `U_i ⊗ 1` on `(In i × ∀ j ≠ i, In j) × S`. -/
@[expose]
noncomputable def widen (E : EmulatedOracle P In) :
    EmulatedOracle P fun i ↦ QReg.of (In i × otherIn In i) where
  S := E.S
  init := E.init
  U i := Matrix.reindex (QuantumRuntime.queryEquivOut (In i) E.S (otherIn In i))
    (QuantumRuntime.queryEquivOut (In i) E.S (otherIn In i))
    (E.U i ⊗ₖ (1 : Matrix (otherIn In i) (otherIn In i) ℂ))
  unitary i := reindex_mem_unitaryGroup _
    (Matrix.kronecker_mem_unitary (E.unitary i) (one_mem _))

/-- **The tensor-product interface** (ePrint 2025/2166, p. 28): one port on `tensIn In`,
answered by `∑ᵢ |i⟩⟨i| ⊗ U_i ⊗ 1` (`Quantum.EmulatedOracle.tensor_U_apply`). It is the coherent
oracle of `E.widen`, with its port register moved along `Quantum.EmulatedOracle.tensEquiv`. -/
@[expose, reducible]
noncomputable def tensor (E : EmulatedOracle P In) : EmulatedOracle Unit fun _ ↦ tensIn In where
  S := E.S
  init := E.init
  U _ := Matrix.reindex ((tensEquiv In).prodCongr (Equiv.refl E.S)).symm
    ((tensEquiv In).prodCongr (Equiv.refl E.S)).symm (E.widen.coherent.U ())
  unitary _ := reindex_mem_unitaryGroup _ (E.widen.coherent.unitary ())

variable (E : EmulatedOracle P In)

/-- **The tensor-product unitary through the reindexing.** Along
`P × ∀ j, In j ≃ Σ i, In i × ∀ j ≠ i, In j`, the unitary of the tensor-product interface is the
coherent unitary of the oracle whose port `i` acts by `U_i ⊗ 1`. -/
theorem tensor_U_eq :
    Matrix.reindex ((tensEquiv In).prodCongr (Equiv.refl E.S))
      ((tensEquiv In).prodCongr (Equiv.refl E.S)) (E.tensor.U ()) = E.widen.coherent.U () := by
  ext a b
  exact congrArg₂ (E.widen.coherent.U ()) (Equiv.apply_symm_apply _ a)
    (Equiv.apply_symm_apply _ b)

omit [Fintype P] [DecidableEq P] in
/-- The restrictions to the ports other than `i` agree exactly when the two families agree off
`i`. -/
theorem restrict_eq_restrict_iff (i : P) (x x' : ∀ j, In j) :
    ((fun j : {j // j ≠ i} ↦ x j) = fun j : {j // j ≠ i} ↦ x' j) ↔ ∀ j, j ≠ i → x j = x' j :=
  ⟨fun h j hj ↦ congrFun h ⟨j, hj⟩, fun h ↦ funext fun j ↦ h j j.2⟩

/-- **The entries of the tensor-product unitary** are those of `∑ᵢ |i⟩⟨i| ⊗ U_i ⊗ 1`: zero
unless the indices agree and the registers of the other ports agree, and otherwise the entry of
`U_i` on the register of the port `i` and the private register. -/
theorem tensor_U_apply (i i' : P) (x x' : ∀ j, In j) (d d' : E.S) :
    E.tensor.U () ((i, x), d) ((i', x'), d') =
      if i = i' ∧ ∀ j, j ≠ i → x j = x' j then E.U i (x i, d) (x' i, d') else 0 := by
  by_cases hi : i = i'
  · subst hi
    refine (E.widen.coherent_U_apply_self i (x i, fun j ↦ x j) (x' i, fun j ↦ x' j) d d').trans ?_
    change (E.U i ⊗ₖ (1 : Matrix (otherIn In i) (otherIn In i) ℂ)) ((x i, d), fun j ↦ x j)
      ((x' i, d'), fun j ↦ x' j) = _
    rw [Matrix.kroneckerMap_apply, Matrix.one_apply]
    by_cases h : ∀ j, j ≠ i → x j = x' j
    · rw [ite_eq_left ((restrict_eq_restrict_iff i x x').mpr h), mul_one,
        ite_eq_left ⟨rfl, h⟩]
    · rw [ite_eq_right (mt (restrict_eq_restrict_iff i x x').mp h), mul_zero,
        ite_eq_right fun h' ↦ h h'.2]
  · refine (E.widen.coherent_U_apply_of_ne hi (x i, fun j ↦ x j) (x' i', fun j ↦ x' j) d
      d').trans ?_
    simp [hi]

/-! ## Masses on the tensor-product interface -/

/-- The projector of the tensor-product register onto the index `i`, tensored with the identity
on the private register (the paper's `P_mass^(i) = |i⟩⟨i|_I`, p. 28). -/
@[expose]
noncomputable def tensorProj (i : P) : Matrix (tensIn In × E.S) (tensIn In × E.S) ℂ :=
  Matrix.diagonal fun a ↦ if a.1.1 = i then 1 else 0

/-- The projector of the tensor-product register onto the index `i`, on the input register of
the port alone (the paper's `|i⟩⟨i|_I`, p. 28): the projector onto the fibre of `i` under
`Prod.fst`. These are the blocks of the coherent index of `Quantum.EmulatedOracle.tensSpec`
(`Quantum.EmulatedOracle.isCoherentIndex_tensIndexProj`). -/
@[expose, reducible]
noncomputable def tensIndexProj (In : P → QReg) (i : P) : Matrix (tensIn In) (tensIn In) ℂ :=
  fiberProj (fun a : tensIn In ↦ a.1) i

/-- The projector onto an index, with the private register, is the projector of the
tensor-product register beside the identity. -/
theorem tensorProj_eq_kronecker (i : P) :
    E.tensorProj i = tensIndexProj In i ⊗ₖ (1 : Matrix E.S E.S ℂ) := by
  rw [tensIndexProj, fiberProj_kronecker_one]
  rfl

/-- The projectors onto the indices form a coherent index on the signature of the
tensor-product interface, so the square-root hybrid bounds of
`VCVio.Quantum.Comp.HybridIndex` apply to it. -/
theorem isCoherentIndex_tensIndexProj :
    Hybrid.IsCoherentIndex (spec := tensSpec In) (fun _ ↦ tensIndexProj In)
      (fun _ ↦ tensIndexProj In) :=
  isCoherentIndex_fiberProj fun _ (a : tensIn In) ↦ a.1

/-- **The tensor-product unitary respects the index**: it sends the block of each index into
itself, `(Pᵢ ⊗ 1) U (Pᵢ ⊗ 1) = U (Pᵢ ⊗ 1)` for the projectors
`Quantum.EmulatedOracle.tensIndexProj`. -/
theorem respectsIndex_tensor_U :
    Hybrid.RespectsIndex (spec := tensSpec In) (fun _ ↦ tensIndexProj In)
      (fun _ ↦ tensIndexProj In) fun _ _ ↦ E.tensor.U () := fun _ _ i ↦ by
  beta_reduce
  rw [← tensorProj_eq_kronecker]
  ext ⟨⟨k, x⟩, d⟩ ⟨⟨k', x'⟩, d'⟩
  rw [tensorProj, Matrix.mul_diagonal, Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases h : k = k'
  · subst h
    by_cases hk : k = i <;> simp [hk]
  · rw [E.tensor_U_apply]
    simp [h]

/-- The weight of the index-`i` component of an operator on the tensor-product register. -/
theorem trace_conj_tensorProj (i : P) (σ : Matrix (tensIn In × E.S) (tensIn In × E.S) ℂ) :
    (MatrixMap.conj (E.tensorProj i) σ).trace = ∑ a, if a.1.1 = i then σ a a else 0 := by
  simp only [MatrixMap.conj_apply, tensorProj, Matrix.diagonal_conjTranspose, Matrix.trace,
    Matrix.diag_apply, Matrix.diagonal_mul, Matrix.mul_diagonal]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  by_cases h : a.1.1 = i <;> simp [h]

/-- The weights of the index components add up to the trace. -/
theorem sum_trace_conj_tensorProj (σ : Matrix (tensIn In × E.S) (tensIn In × E.S) ℂ) :
    ∑ i, (MatrixMap.conj (E.tensorProj i) σ).trace = σ.trace := by
  calc ∑ i, (MatrixMap.conj (E.tensorProj i) σ).trace
      = ∑ i, ∑ a, if a.1.1 = i then σ a a else 0 :=
        Finset.sum_congr rfl fun i _ ↦ E.trace_conj_tensorProj i σ
    _ = ∑ a, ∑ i, if a.1.1 = i then σ a a else 0 := Finset.sum_comm
    _ = σ.trace := Finset.sum_congr rfl fun a _ ↦ by simp

/-- **Total query mass on the tensor-product interface** (ePrint 2025/2166, Definitions 4.1 and
4.3, pp. 28–29): the weight of the index-`i` component of the input of every call of `x` to the
tensor-product oracle, summed over the calls, for `x` run from the joint operator `ρ` on
`A × S`. -/
@[expose]
noncomputable def tensorMass {L : LocalSig.{uL, vL}} (I : L.Interp) {W : QReg → Type w}
    {A : QReg} (x : QuantumComp L (tensSpec In) W A) (ρ : Matrix (A × E.S) (A × E.S) ℂ) (i : P) :
    ℝ≥0∞ :=
  ∑' j, E.tensor.toRuntime.queryWeight I
    (fun _ σ ↦ ENNReal.ofReal (MatrixMap.conj (E.tensorProj i) σ).trace.re) x ρ j

section mass

variable {L : LocalSig.{uL, vL}} (I : L.Interp) {W : QReg → Type w} {A : QReg}

/-- **Total masses are index masses** on the tensor-product interface. The mass on `i` is the
total index mass `Quantum.QuantumRuntime.indexMass` of the block `⟨(), i⟩` for the projectors
`Quantum.EmulatedOracle.tensIndexProj`, the masses consumed by the square-root hybrid bounds of
`VCVio.Quantum.Comp.HybridIndex`. -/
theorem tensorMass_eq_indexMass (x : QuantumComp L (tensSpec In) W A)
    (ρ : Matrix (A × E.S) (A × E.S) ℂ) (i : P) :
    E.tensorMass I x ρ i =
      E.tensor.toRuntime.indexMass I (fun _ ↦ tensIndexProj In) x ρ ⟨(), i⟩ := by
  refine tsum_congr fun j ↦ congrArg (fun w ↦ E.tensor.toRuntime.queryWeight I w x ρ j)
    (funext fun _ ↦ funext fun σ ↦ ?_)
  rw [tsum_eq_single i fun k hk ↦ by simp [hk], ite_eq_left rfl, tensorProj_eq_kronecker]

/-- **Remark 4.2** (p. 28) on the tensor-product interface: on a positive semidefinite
input, the masses on the indices add up to the query mass of the port. It is the completeness of
the index projectors in `Quantum.QuantumRuntime.tsum_indexMass_eq_queryMass`. -/
theorem sum_tensorMass (x : QuantumComp L (tensSpec In) W A)
    {ρ : Matrix (A × E.S) (A × E.S) ℂ} (hρ : ρ.PosSemidef) :
    ∑ i, E.tensorMass I x ρ i = E.tensor.toRuntime.queryMass I x ρ () := by
  simp only [E.tensorMass_eq_indexMass I x ρ]
  rw [← tsum_fintype (L := .unconditional P)]
  exact E.tensor.toRuntime.tsum_indexMass_eq_queryMass I (fun _ ↦ tensIndexProj In) ()
    (sum_conjTranspose_mul_fiberProj _) x hρ

/-- **Masses and query budgets on the tensor-product interface.** A program making at most `t`
queries has masses on the indices adding up to at most `t` times the trace of the initial
state. -/
theorem sum_tensorMass_le {x : QuantumComp L (tensSpec In) W A} {t : ℕ}
    (hx : x.IsQueryBoundAt () t) {ρ : Matrix (A × E.S) (A × E.S) ℂ} (hρ : ρ.PosSemidef) :
    ∑ i, E.tensorMass I x ρ i ≤ t * ENNReal.ofReal ρ.trace.re := by
  rw [E.sum_tensorMass I x hρ]
  exact E.tensor.toRuntime.queryMass_le_of_isQueryBoundAt I hx hρ

end mass

/-! ## From the tensor-product interface to the coherent one -/

/-- A family of basis elements with the entry `i` reset to a fixed basis element of `In i`
(chosen from the entry itself, so independent of it). -/
@[expose]
noncomputable def resetAt (i : P) (x : ∀ j, In j) : ∀ j, In j :=
  Function.update x i (Classical.choice ⟨x i⟩)

omit [Fintype P] in
/-- Two families reset at `i` agree exactly when they agree off `i`. -/
theorem resetAt_eq_resetAt_iff (i : P) (x x' : ∀ j, In j) :
    resetAt i x = resetAt i x' ↔ ∀ j, j ≠ i → x j = x' j := by
  refine ⟨fun h j hj ↦ ?_, fun h ↦ funext fun j ↦ ?_⟩
  · simpa [resetAt, Function.update_of_ne hj] using congrFun h j
  · by_cases hj : j = i
    · subst hj
      simp [resetAt]
    · simp [resetAt, Function.update_of_ne hj, h j hj]

/-- **The embedding of the tensor-product register into the coherent register**:
`|i, x⟩ ↦ |⟨i, x i⟩⟩ ⊗ |x[i ↦ x₀]⟩`. Beside the coherent register is a copy of all the port
registers, with the entry `i` reset; together with `x i` in the coherent register, it records
`x`. -/
@[expose]
noncomputable def tensorEmbedding (In : P → QReg) :
    PortEmbedding (fun _ : Unit ↦ tensIn In) (cohIn In) where
  G _ := QReg.of (∀ j, In j)
  toFun _ p := (⟨p.1, p.2 p.1⟩, resetAt p.1 p.2)
  injective _ := by
    rintro ⟨i, x⟩ ⟨i', x'⟩ h
    simp only [Prod.mk.injEq, Sigma.mk.inj_iff] at h
    obtain ⟨⟨rfl, hx⟩, hr⟩ := h
    refine Prod.ext rfl (funext fun j ↦ ?_)
    by_cases hj : j = i
    · subst hj
      exact eq_of_heq hx
    · exact (resetAt_eq_resetAt_iff i x x').mp hr j hj

/-- The coherent unitary, beside the reset copy of the port registers and compressed along
`Quantum.EmulatedOracle.tensorEmbedding`, is the tensor-product unitary. -/
theorem coherent_compress_tensorEmbedding (q : Unit) :
    (E.coherent.U () ⊗ₖ
      (1 : Matrix ((tensorEmbedding In).G q) ((tensorEmbedding In).G q) ℂ)).submatrix
        ((tensorEmbedding In).withPrivate q E.S) ((tensorEmbedding In).withPrivate q E.S) =
      E.tensor.U q := by
  ext ⟨⟨i, x⟩, d⟩ ⟨⟨i', x'⟩, d'⟩
  rw [E.tensor_U_apply]
  change E.coherent.U () (⟨i, x i⟩, d) (⟨i', x' i'⟩, d') *
    (1 : Matrix (∀ j, In j) (∀ j, In j) ℂ) (resetAt i x) (resetAt i' x') = _
  by_cases hi : i = i'
  · subst hi
    rw [coherent_U_apply_self, Matrix.one_apply]
    by_cases h : ∀ j, j ≠ i → x j = x' j
    · rw [ite_eq_left ((resetAt_eq_resetAt_iff i x x').mpr h), mul_one,
        ite_eq_left ⟨rfl, h⟩]
    · rw [ite_eq_right (mt (resetAt_eq_resetAt_iff i x x').mp h), mul_zero,
        ite_eq_right fun h' ↦ h h'.2]
  · rw [coherent_U_apply_of_ne _ hi]
    simp [hi]

end EmulatedOracle

namespace QuantumComp

variable {P : Type} [Fintype P] [DecidableEq P] {In : P → QReg} {W : QReg → Type w} {A : QReg}

open EmulatedOracle

/-- **Tensor-product programs as coherent programs.** Before each call, the isometry of
`Quantum.EmulatedOracle.tensorEmbedding` moves `|i, x⟩` to `|⟨i, x i⟩⟩ ⊗ |x[i ↦ x₀]⟩`; after
it, its adjoint reads the result back. -/
@[expose]
noncomputable def tensorToCoherent
    (x : QuantumComp LocalSig.instruments.{v} (tensSpec In) W A) :
    QuantumComp LocalSig.instruments.{v} (cohSpec In) W A :=
  x.embedCalls (tensorEmbedding In)

/-- The translation of a tensor-product program makes as many calls. -/
theorem isQueryBound_tensorToCoherent
    {x : QuantumComp LocalSig.instruments.{v} (tensSpec In) W A} {b : Unit → ℕ}
    (hx : x.IsQueryBound b) : x.tensorToCoherent.IsQueryBound b := by
  have hb : (fun _ : Unit ↦ ∑ q, b q) = b := funext fun u ↦ by cases u; simp
  exact hb ▸ isQueryBound_embedCalls (tensorEmbedding In) hx

end QuantumComp

namespace EmulatedOracle

variable {P : Type} [Fintype P] [DecidableEq P] {In : P → QReg} (E : EmulatedOracle P In)
  {W : QReg → Type w} {A : QReg}

/-- **Tensor-product programs run as their coherent translations.** -/
theorem run_tensorToCoherent (x : QuantumComp LocalSig.instruments.{v} (tensSpec In) W A) :
    E.coherent.toRuntime.run .instruments x.tensorToCoherent =
      E.tensor.toRuntime.run .instruments x :=
  E.tensor.run_embedCalls (tensorEmbedding In) (E.coherent.unitary ())
    E.coherent_compress_tensorEmbedding x

/-- **The coherent translation of a tensor-product program changes no observed law.** -/
theorem outcomeLawWith_tensorToCoherent
    (x : QuantumComp LocalSig.instruments.{v} (tensSpec In) W A) {γ : Type*} [MeasurableSpace γ]
    (ρ : SubState A) (f : (Σ u, W u) → γ) :
    E.coherent.toRuntime.evalDistMap .instruments x.tensorToCoherent ρ f =
      E.tensor.toRuntime.evalDistMap .instruments x ρ f :=
  E.tensor.outcomeLawWith_embedCalls (tensorEmbedding In) (E.coherent.unitary ())
    E.coherent_compress_tensorEmbedding x ρ f

/-- **The coherent translation of a lossless tensor-product program runs losslessly.** -/
theorem lossless_run_tensorToCoherent
    {x : QuantumComp LocalSig.instruments.{v} (tensSpec In) W A} (hx : x.Lossless .instruments) :
    (E.coherent.toRuntime.run .instruments x.tensorToCoherent).Lossless :=
  E.tensor.lossless_run_embedCalls (tensorEmbedding In) (E.coherent.unitary ())
    E.coherent_compress_tensorEmbedding hx

/-- **The coherent translation of a tensor-product program keeps every mass**: its total mass
on `i` against the coherent oracle is the total mass on `i` of the original program against the
tensor-product oracle. -/
theorem totalMass_tensorToCoherent (x : QuantumComp LocalSig.instruments.{v} (tensSpec In) W A)
    (ρ : Matrix (A × E.S) (A × E.S) ℂ) (i : P) :
    E.totalMass .instruments x.tensorToCoherent ρ i = E.tensorMass .instruments x ρ i :=
  tsum_congr fun j ↦ E.tensor.queryWeight_embedCalls (tensorEmbedding In)
    (E.coherent.unitary ()) E.coherent_compress_tensorEmbedding (fun a ↦ a.1 = i)
    (w₂ := fun σ ↦ ENNReal.ofReal (MatrixMap.conj (E.indexProj i) σ).trace.re)
    (fun σ ↦ by rw [E.trace_conj_indexProj])
    (w₁ := fun _ σ ↦ ENNReal.ofReal (MatrixMap.conj (E.tensorProj i) σ).trace.re)
    (fun _ σ ↦ by rw [E.trace_conj_tensorProj]; rfl) x ρ j

/-! ## From the coherent interface to the tensor-product one -/

/-- A fixed basis element of every port register. -/
@[expose]
noncomputable def basePoint (In : P → QReg) [∀ j, Nonempty (In j)] : ∀ j, In j :=
  fun _ ↦ Classical.choice inferInstance

/-- **The embedding of the coherent register into the tensor-product register**, when every port
register is nonempty: `|⟨i, a⟩⟩ ↦ |i, x₀[i ↦ a]⟩` for the fixed basis elements `x₀`. -/
@[expose]
noncomputable def coherentEmbedding (In : P → QReg) [∀ j, Nonempty (In j)] :
    PortEmbedding (fun _ : Unit ↦ cohIn In) (tensIn In) where
  G _ := QReg.of Unit
  toFun _ a := ((a.1, Function.update (basePoint In) a.1 a.2), ())
  injective _ := by
    rintro ⟨i, a⟩ ⟨i', a'⟩ h
    simp only [Prod.mk.injEq, and_true] at h
    obtain ⟨rfl, h⟩ := h
    have h' := congrFun h i
    simp only [Function.update_self] at h'
    rw [h']

/-- The tensor-product unitary, compressed along `Quantum.EmulatedOracle.coherentEmbedding`, is
the coherent unitary. -/
theorem tensor_compress_coherentEmbedding [∀ j, Nonempty (In j)] (q : Unit) :
    (E.tensor.U () ⊗ₖ
      (1 : Matrix ((coherentEmbedding In).G q) ((coherentEmbedding In).G q) ℂ)).submatrix
        ((coherentEmbedding In).withPrivate q E.S) ((coherentEmbedding In).withPrivate q E.S) =
      E.coherent.U q := by
  ext ⟨⟨i, a⟩, d⟩ ⟨⟨i', a'⟩, d'⟩
  change E.tensor.U () ((i, Function.update (basePoint In) i a), d)
    ((i', Function.update (basePoint In) i' a'), d') * (1 : Matrix Unit Unit ℂ) () () = _
  rw [Matrix.one_apply_eq, mul_one, E.tensor_U_apply]
  by_cases hi : i = i'
  · subst hi
    have h : ∀ j, j ≠ i → Function.update (basePoint In) i a j =
        Function.update (basePoint In) i a' j := fun j hj ↦ by
      rw [Function.update_of_ne hj, Function.update_of_ne hj]
    rw [coherent_U_apply_self, ite_eq_left ⟨rfl, h⟩, Function.update_self, Function.update_self]
  · rw [coherent_U_apply_of_ne _ hi]
    simp [hi]

end EmulatedOracle

namespace QuantumComp

variable {P : Type} [Fintype P] [DecidableEq P] {In : P → QReg} {W : QReg → Type w} {A : QReg}

open EmulatedOracle

/-- **Coherent programs as tensor-product programs**, when every port register is nonempty.
Before each call, the isometry of `Quantum.EmulatedOracle.coherentEmbedding` moves `|⟨i, a⟩⟩` to
`|i, x₀[i ↦ a]⟩`; after it, its adjoint reads the result back. -/
@[expose]
noncomputable def coherentToTensor [∀ j, Nonempty (In j)]
    (x : QuantumComp LocalSig.instruments.{v} (cohSpec In) W A) :
    QuantumComp LocalSig.instruments.{v} (tensSpec In) W A :=
  x.embedCalls (coherentEmbedding In)

/-- The translation of a coherent program makes as many calls. -/
theorem isQueryBound_coherentToTensor [∀ j, Nonempty (In j)]
    {x : QuantumComp LocalSig.instruments.{v} (cohSpec In) W A} {b : Unit → ℕ}
    (hx : x.IsQueryBound b) : x.coherentToTensor.IsQueryBound b := by
  have hb : (fun _ : Unit ↦ ∑ q, b q) = b := funext fun u ↦ by cases u; simp
  exact hb ▸ isQueryBound_embedCalls (coherentEmbedding In) hx

end QuantumComp

namespace EmulatedOracle

variable {P : Type} [Fintype P] [DecidableEq P] {In : P → QReg} [∀ j, Nonempty (In j)]
  (E : EmulatedOracle P In) {W : QReg → Type w} {A : QReg}

/-- **Coherent programs run as their tensor-product translations.** -/
theorem run_coherentToTensor (x : QuantumComp LocalSig.instruments.{v} (cohSpec In) W A) :
    E.tensor.toRuntime.run .instruments x.coherentToTensor =
      E.coherent.toRuntime.run .instruments x :=
  E.coherent.run_embedCalls (coherentEmbedding In) (E.tensor.unitary ())
    E.tensor_compress_coherentEmbedding x

/-- **The tensor-product translation of a coherent program changes no observed law.** -/
theorem outcomeLawWith_coherentToTensor
    (x : QuantumComp LocalSig.instruments.{v} (cohSpec In) W A) {γ : Type*} [MeasurableSpace γ]
    (ρ : SubState A) (f : (Σ u, W u) → γ) :
    E.tensor.toRuntime.evalDistMap .instruments x.coherentToTensor ρ f =
      E.coherent.toRuntime.evalDistMap .instruments x ρ f :=
  E.coherent.outcomeLawWith_embedCalls (coherentEmbedding In) (E.tensor.unitary ())
    E.tensor_compress_coherentEmbedding x ρ f

/-- **The tensor-product translation of a lossless coherent program runs losslessly.** -/
theorem lossless_run_coherentToTensor
    {x : QuantumComp LocalSig.instruments.{v} (cohSpec In) W A} (hx : x.Lossless .instruments) :
    (E.tensor.toRuntime.run .instruments x.coherentToTensor).Lossless :=
  E.coherent.lossless_run_embedCalls (coherentEmbedding In) (E.tensor.unitary ())
    E.tensor_compress_coherentEmbedding hx

/-- **The tensor-product translation of a coherent program keeps every mass.** -/
theorem tensorMass_coherentToTensor (x : QuantumComp LocalSig.instruments.{v} (cohSpec In) W A)
    (ρ : Matrix (A × E.S) (A × E.S) ℂ) (i : P) :
    E.tensorMass .instruments x.coherentToTensor ρ i = E.totalMass .instruments x ρ i :=
  tsum_congr fun j ↦ E.coherent.queryWeight_embedCalls (coherentEmbedding In)
    (E.tensor.unitary ()) E.tensor_compress_coherentEmbedding (fun a ↦ a.1 = i)
    (w₂ := fun σ ↦ ENNReal.ofReal (MatrixMap.conj (E.tensorProj i) σ).trace.re)
    (fun σ ↦ by rw [E.trace_conj_tensorProj])
    (w₁ := fun _ σ ↦ ENNReal.ofReal (MatrixMap.conj (E.indexProj i) σ).trace.re)
    (fun _ σ ↦ by rw [E.trace_conj_indexProj]; rfl) x ρ j

end EmulatedOracle

end Quantum
