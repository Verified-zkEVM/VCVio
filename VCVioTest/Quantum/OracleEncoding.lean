/-
Copyright (c) 2026 Quang Dao, Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Alexander Hicks
-/

module
public import VCVio.Quantum.Oracle.Encoding
public import VCVio.CryptoFoundations.TimeLockPuzzle.Quantum
public import Mathlib.Data.ZMod.Basic

/-!
# Coherent raw-oracle encoding regressions

A three-cell raw table contains a full-response typed cell, a truncated-response typed cell,
and an outside-image cell. Their responses and tails remain available to every raw query.
A separate physical counterexample shows that discarding a zero-initialized response tail
can destroy coherence even when the retained response is identically zero.
-/

public section

open Quantum Matrix MeasureTheory
open scoped ENNReal Kronecker ComplexOrder

namespace VCVioTest.QuantumOracleEncoding

abbrev Word := ZMod 2 × ZMod 2

/-- Two differently typed cells in a three-cell raw domain. -/
@[expose, reducible]
def encode (b : Bool) : Fin 3 := if b then 1 else 0

private theorem encode_injective : Function.Injective encode := by
  intro a b h
  cases a <;> cases b <;> simp_all [encode]

/-- The first cell retains a full response; the second keeps only its first component. -/
@[expose, reducible]
def Answer : Bool → Type
  | false => Word
  | true => ZMod 2

/-- Only the truncated cell has a nontrivial tail. -/
@[expose, reducible]
def Tail : Bool → Type
  | false => Unit
  | true => ZMod 2

/-- Splitting retains the complementary component rather than sampling it again. -/
@[expose, reducible]
def split : (b : Bool) → Word ≃ Answer b × Tail b
  | false => (Equiv.prodPUnit Word).symm
  | true => Equiv.refl Word

/-- A raw table with different encoded and outside-image answers. -/
@[expose, reducible]
def rawTable (x : Fin 3) : Word := if x = 2 then (0, 1) else (1, 0)

/-- The truncated cell retains both its visible answer and its fixed tail. -/
example : (Equiv.tableSplit encode encode_injective split rawTable).1.1 true = 1 ∧
    (Equiv.tableSplit encode encode_injective split rawTable).1.2 true = 0 := by
  simp [rawTable, encode]

private theorem two_not_encoded : (2 : Fin 3) ∉ Set.range encode := by
  rintro ⟨b, h⟩
  cases b <;> norm_num [encode] at h

/-- The full response at an outside-image point is retained as well. -/
example : (Equiv.tableSplit encode encode_injective split rawTable).2
    ⟨2, two_not_encoded⟩ = (0, 1) := by simp [rawTable]

/-- Completing the split table restores an off-diagonal operator between an encoded cell
and an outside-image cell, including their different response words. -/
example :
    MatrixMap.conj
        (oracleUnitary ((Equiv.tableSplit encode encode_injective split).symm
          (Equiv.tableSplit encode encode_injective split rawTable)))
        (Matrix.single (0, (0, 0)) (2, (0, 0)) Complex.I) =
      (Matrix.single (0, (1, 0)) (2, (0, 1)) Complex.I :
        Matrix (Fin 3 × Word) (Fin 3 × Word) ℂ) := by
  rw [Equiv.symm_apply_apply, oracleUnitary, conj_basisMatrix_equiv,
    Matrix.submatrix_single_equiv]
  simp [oracleEquiv, rawTable]

/-- The full answering table and final branch stay joint under the encoding, even for an
adaptive raw program and a subnormalized input. The observer retains an outside-image answer. -/
example {A : QReg} {W : QReg → Type}
    (x : QuantumComp LocalSig.instruments (qromBatchSpec (Fin 3) Word) W A)
    (ρ : SubState A) :
    letI : MeasurableSpace (Word × (Σ B, W B)) := ⊤
    sampledEvalDistMap (fun H : Fin 3 → Word ↦ parallelOracleRuntime H) .instruments x ρ
        (fun H leaf ↦ (H 2, leaf)) =
      sampledEvalDistMap
        (fun tables ↦ parallelOracleRuntime
          ((Equiv.tableSplit encode encode_injective split).symm tables))
        .instruments x ρ
        (fun tables leaf ↦
          (((Equiv.tableSplit encode encode_injective split).symm tables) 2, leaf)) := by
  let : MeasurableSpace (Word × (Σ B, W B)) := ⊤
  exact sampledEvalDistMap_tableSplit encode encode_injective split .instruments x ρ _

/-- Reparameterizing the actual three-phase experiment retains the hidden generator secret,
key and output jointly with the outside-image oracle cell, for arbitrary preprocessing. -/
example (tlp : Quantum.TimeLockPuzzle (qromBatchSpec (Fin 3) Word) Unit Word)
    (adv : Quantum.TimeLockPuzzle.Adversary (qromBatchSpec (Fin 3) Word) Unit Word) :
    letI : Fintype (((∀ i, Answer i) × (∀ i, Tail i)) ×
        ({z : Fin 3 // z ∉ Set.range encode} → Word)) :=
      Fintype.ofEquiv (Fin 3 → Word) (Equiv.tableSplit encode encode_injective split)
    letI : MeasurableSpace (Word × tlp.Secret × Word × Word) := ⊤
    Quantum.TimeLockPuzzle.sampledDelayLawWith
        (fun H : Fin 3 → Word ↦ parallelOracleRuntime H) tlp adv
        (fun H t ↦ (H 2, t.secret, t.key, t.output)) =
      Quantum.TimeLockPuzzle.sampledDelayLawWith
        (fun tables ↦ parallelOracleRuntime
          ((Equiv.tableSplit encode encode_injective split).symm tables)) tlp adv
        (fun tables t ↦ (((Equiv.tableSplit encode encode_injective split).symm tables) 2,
          t.secret, t.key, t.output)) := by
  let : Fintype (((∀ i, Answer i) × (∀ i, Tail i)) ×
      ({z : Fin 3 // z ∉ Set.range encode} → Word)) :=
    Fintype.ofEquiv (Fin 3 → Word) (Equiv.tableSplit encode encode_injective split)
  let : MeasurableSpace (Word × tlp.Secret × Word × Word) := ⊤
  exact Quantum.TimeLockPuzzle.sampledDelayLawWith_equiv
    (Equiv.tableSplit encode encode_injective split).symm parallelOracleRuntime tlp adv
    (fun H t ↦ (H 2, t.secret, t.key, t.output))

/-! ## Discarding a response tail can dephase a query -/

/-- The density matrix of a coherent uniform input bit. -/
private noncomputable def plus : SubState Bool where
  matrix := Matrix.of fun _ _ ↦ 1 / 2
  posSemidef := by
    have h : (Matrix.of fun _ _ ↦ 1 / 2 : Matrix Bool Bool ℂ) =
        (Matrix.of fun _ _ ↦ 1 / 2)ᴴ * Matrix.of fun _ _ ↦ 1 / 2 := by
      ext i j
      simp [Matrix.mul_apply]
    rw [h]
    exact Matrix.posSemidef_conjTranspose_mul_self _
  trace_re_le_one := by norm_num [Matrix.trace, Fintype.sum_bool]

/-- The visible response is zero at both inputs, while the hidden response tail differs. -/
private def tailTable (b : Bool) : Word := (0, if b then 1 else 0)

/-- Input, visible response and response tail, with both responses initially zero. -/
private noncomputable def zeroTailInput : SubState ((Bool × ZMod 2) × ZMod 2) :=
  (plus.prod (SubState.basis 0)).prod (SubState.basis 0)

/-- The coherence counterexample uses a normalized physical input. -/
private theorem trace_zeroTailInput : zeroTailInput.matrix.trace = 1 := by
  simp only [zeroTailInput, SubState.matrix_prod, Matrix.trace_kronecker,
    SubState.trace_basis, mul_one]
  norm_num [plus, Matrix.trace]

/-- The raw oracle written on the input/visible/tail parenthesization. -/
private def rawTailGate : ((Bool × ZMod 2) × ZMod 2) ≃ ((Bool × ZMod 2) × ZMod 2) :=
  (Equiv.prodAssoc Bool (ZMod 2) (ZMod 2)).trans
    ((oracleEquiv tailTable).trans (Equiv.prodAssoc Bool (ZMod 2) (ZMod 2)).symm)

/-- Tracing out an untouched tail preserves the input coherence. -/
private theorem coherence_before :
    MatrixMap.traceRight (Bool × ZMod 2) (ZMod 2) zeroTailInput.matrix
      (false, 0) (true, 0) = 1 / 2 := by
  simp [MatrixMap.traceRight_apply, zeroTailInput, SubState.matrix_prod,
    SubState.matrix_basis, Matrix.kroneckerMap_apply, Matrix.single_apply, plus]

/-- Computing the raw answer into a zero tail and discarding it loses that coherence. -/
private theorem coherence_after :
    MatrixMap.traceRight (Bool × ZMod 2) (ZMod 2)
      (MatrixMap.conj (basisMatrix rawTailGate) zeroTailInput.matrix)
      (false, 0) (true, 0) = 0 := by
  rw [conj_basisMatrix_equiv, MatrixMap.traceRight_apply]
  apply Finset.sum_eq_zero
  intro t _
  by_cases ht : t = 0
  · subst t
    norm_num [Matrix.submatrix_apply, zeroTailInput, SubState.matrix_prod,
      SubState.matrix_basis, Matrix.kroneckerMap_apply, Matrix.single_apply, plus,
      rawTailGate, tailTable, oracleEquiv]
  · have hz : (0 : ZMod 2) ≠ t := Ne.symm ht
    simp [Matrix.submatrix_apply, zeroTailInput, SubState.matrix_prod,
      SubState.matrix_basis, Matrix.kroneckerMap_apply, plus,
      rawTailGate, tailTable, oracleEquiv, hz]

/-- A zero retained answer does not justify discarding the raw response tail: the resulting
channel differs from the identity truncated oracle on a normalized physical input state. -/
example : zeroTailInput.matrix.trace = 1 ∧
    MatrixMap.traceRight (Bool × ZMod 2) (ZMod 2)
        (MatrixMap.conj (basisMatrix rawTailGate) zeroTailInput.matrix) ≠
      MatrixMap.traceRight (Bool × ZMod 2) (ZMod 2) zeroTailInput.matrix := by
  refine ⟨trace_zeroTailInput, ?_⟩
  intro h
  have he := congrArg (fun ρ ↦ ρ (false, 0) (true, 0)) h
  rw [coherence_before, coherence_after] at he
  norm_num at he

end VCVioTest.QuantumOracleEncoding
