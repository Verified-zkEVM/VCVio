/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.Quantum.Comp.TotalQueryBound

/-!
# Projective classical reads

Classical addresses select projective instruments on an emulated oracle's private register.
The ordinary coherent port and the read ports share that register. Read outcomes are retained.
-/

public section

open Matrix
open scoped Kronecker ENNReal ComplexOrder

universe u v w

namespace Quantum

/-- A complete family of commuting projective answers, commuting with ordinary queries. -/
structure ProjectiveClassicalAnswers {P : Type u} {In : P → QReg}
    (E : EmulatedOracle P In) (Addr Ans : Type) [Fintype Ans] [DecidableEq Ans] where
  /-- The projector for each classical address and outcome. -/
  A : Addr → Ans → Matrix E.S E.S ℂ
  /-- Answer projectors are Hermitian. -/
  hermitian : ∀ x a, (A x a)ᴴ = A x a
  /-- Distinct answers are orthogonal, and each answer is idempotent. -/
  orthogonal : ∀ x a b, A x a * A x b = if a = b then A x a else 0
  /-- All answers together exhaust the private state. -/
  complete : ∀ x, ∑ a, A x a = 1
  /-- Reads at different classical addresses commute. -/
  commute_cells : ∀ x a x' b, A x a * A x' b = A x' b * A x a
  /-- An ordinary query commutes with each answer projector. -/
  commute_ordinary : ∀ p x a,
    E.U p * (1 ⊗ₖ A x a) = (1 ⊗ₖ A x a) * E.U p

namespace ProjectiveClassicalAnswers

variable {P : Type u} {In : P → QReg} {E : EmulatedOracle P In}
  {Addr Ans : Type} [Fintype Ans] [DecidableEq Ans]
  (H : ProjectiveClassicalAnswers E Addr Ans)

/-- Projective completeness implies Kraus completeness. -/
theorem kraus_complete (x : Addr) : ∑ a, (H.A x a)ᴴ * H.A x a = 1 := by
  simp only [H.hermitian, H.orthogonal, ite_true]
  exact H.complete x

/-- Read an address, retaining its answer and the projected private state. -/
@[expose]
noncomputable def instrument (x : Addr) : SubInstrument E.S E.S Ans :=
  SubInstrument.ofKraus (H.A x) (H.kraus_complete x)

/-- The answer branch is conjugation by its defining projector. -/
@[simp]
theorem instrument_branch (x : Addr) (a : Ans) :
    (H.instrument x).branch a = MatrixMap.conj (H.A x a) := rfl

/-- A projective read loses no mass. -/
theorem lossless_instrument (x : Addr) : (H.instrument x).Lossless :=
  DSubInstrument.lossless_ofKraus (H.A x) (H.kraus_complete x)

/-- Restore the trivial public register beside the private register. -/
def readEquiv : E.S ≃ Unit × E.S := (Equiv.uniqueProd E.S Unit).symm

/-- The private read with its trivial public input and output register. -/
@[expose]
noncomputable def step (x : Addr) : SubInstrument (Unit × E.S) (Unit × E.S) Ans :=
  (H.instrument x).reindex (readEquiv (E := E)) (readEquiv (E := E))

/-- Restoring the trivial public register preserves losslessness. -/
theorem lossless_step (x : Addr) : (H.step x).Lossless :=
  (H.lossless_instrument x).reindex _ _

/-- The step's actual branch acts on the private factor alone. -/
theorem step_branch (x : Addr) (a : Ans) :
    (H.step x).branch a = MatrixMap.conj ((1 : Matrix Unit Unit ℂ) ⊗ₖ H.A x a) := by
  have h : Matrix.reindex (readEquiv (E := E)) (readEquiv (E := E)) (H.A x a) =
      (1 : Matrix Unit Unit ℂ) ⊗ₖ H.A x a := by
    ext ⟨i, d⟩ ⟨j, d'⟩
    simp [readEquiv, Matrix.reindex_apply, Matrix.kroneckerMap_apply]
  ext ρ : 1
  rw [step, SubInstrument.branch_reindex_apply, instrument_branch, ← h,
    MatrixMap.conj_reindex_apply, MatrixMap.conj_apply]

end ProjectiveClassicalAnswers

/-- A read address is a classical port label; the returned answer is classical data. -/
@[expose, reducible]
def classicalReadSpec (Addr Ans : Type) : QuantumOracleSpec where
  Port := Addr
  In _ := QReg.of Unit
  Out _ := QReg.of Unit
  Result _ := Ans

/-- Ordinary ports together with classical read ports. -/
abbrev withReadSpec (spec : QuantumOracleSpec.{u, 0}) (Addr Ans : Type) :=
  spec.sum (classicalReadSpec Addr Ans)

namespace EmulatedOracle

variable {P : Type} [Fintype P] [DecidableEq P] {In : P → QReg}
  (E : EmulatedOracle P In) {Addr Ans : Type} [Fintype Ans] [DecidableEq Ans]
  (H : ProjectiveClassicalAnswers E Addr Ans)

/-- Ordinary coherent calls and classical reads use the same private memory. -/
@[expose, reducible]
noncomputable def withClassicalReads : QuantumRuntime (withReadSpec (cohSpec In) Addr Ans) :=
  E.coherent.toRuntime.extend (t := classicalReadSpec Addr Ans) H.step

/-- The ordinary arm is precisely the coherent runtime step. -/
@[simp]
theorem withClassicalReads_step_inl (p : (cohSpec In).Port) :
    (E.withClassicalReads H).step (.inl p) = E.coherent.toRuntime.step p := rfl

/-- The read arm is precisely the restored projective instrument. -/
@[simp]
theorem withClassicalReads_step_inr (x : Addr) :
    (E.withClassicalReads H).step (.inr x) = H.step x := rfl

/-- Every mixed-runtime step is lossless. -/
theorem lossless_withClassicalReads_step (p : (withReadSpec (cohSpec In) Addr Ans).Port) :
    ((E.withClassicalReads H).step p).Lossless := by
  cases p with
  | inl p => exact E.coherent.lossless_toRuntime_step p
  | inr x => exact H.lossless_step x

/-- A read call with a reference register, with its trivial public factor removed. -/
@[expose]
noncomputable def read (x : Addr) (B : QReg) : SubInstrument (B × E.S) (B × E.S) Ans :=
  ((E.withClassicalReads H).queryStep (A := QReg.of (Unit × B)) (.inr x) B
    (Equiv.refl _)).reindex
      ((Equiv.uniqueProd B Unit).prodCongr (Equiv.refl E.S))
      ((Equiv.uniqueProd B Unit).prodCongr (Equiv.refl E.S))

/-- The actual runtime read branch is the answer projector beside the reference identity. -/
theorem read_branch (x : Addr) (B : QReg) (a : Ans) :
    (E.read H x B).branch a = MatrixMap.conj ((1 : Matrix B B ℂ) ⊗ₖ H.A x a) := by
  ext ρ : 1
  refine (SubInstrument.branch_reindex_apply
    ((Equiv.uniqueProd B Unit).prodCongr (Equiv.refl E.S))
    ((Equiv.uniqueProd B Unit).prodCongr (Equiv.refl E.S))
    ((E.withClassicalReads H).queryStep (A := QReg.of (Unit × B)) (.inr x) B
      (Equiv.refl _)) a ρ).trans ?_
  have hq := (E.withClassicalReads H).queryStep_branch_eq_conj
    (i := Sum.inr x) (r := a) (H.step_branch x a) B
    (A := QReg.of (Unit × B)) (Equiv.refl _)
  change _ = MatrixMap.conj
    (basisMatrix (QuantumRuntime.queryEquivOut Unit E.S B) *
      (((1 : Matrix Unit Unit ℂ) ⊗ₖ H.A x a) ⊗ₖ (1 : Matrix B B ℂ)) *
      basisMatrix (QuantumRuntime.queryEquivIn (Equiv.refl (Unit × B)) E.S)) at hq
  rw [basisMatrix_equiv_eq_conjTranspose (QuantumRuntime.queryEquivOut Unit E.S B),
    conjTranspose_basisMatrix_mul_mul_basisMatrix] at hq
  rw [hq, MatrixMap.conj_apply]
  ext ⟨b, d⟩ ⟨b', d'⟩
  simp [MatrixMap.conj_apply, Matrix.mul_apply, Fintype.sum_prod_type,
    Matrix.one_apply, QuantumRuntime.queryEquivIn, QuantumRuntime.queryEquivOut,
    Equiv.uniqueProd, apply_ite (starRingEnd ℂ)]

/-- A runtime read with any reference register is lossless. -/
theorem lossless_read (x : Addr) (B : QReg) : (E.read H x B).Lossless :=
  ((E.withClassicalReads H).lossless_queryStep (i := .inr x) (H.lossless_step x) B
    (A := QReg.of (Unit × B)) (Equiv.refl _)).reindex _ _

/-- Extra private registers are carried through each actual read branch unchanged. -/
theorem read_frame_branch (x : Addr) (B G : QReg) (a : Ans) :
    ((E.read H x B).frame G).branch a =
      MatrixMap.conj (((1 : Matrix B B ℂ) ⊗ₖ H.A x a) ⊗ₖ (1 : Matrix G G ℂ)) := by
  rw [DSubInstrument.branch_frame_apply, E.read_branch H, MatrixMap.amplify_conj]

end EmulatedOracle
namespace QuantumRuntime

variable {spec : QuantumOracleSpec.{u, 0}} {Addr Ans : Type} {D : QReg}

/-- A mixed weight charges the selected ordinary mass on the left and every read's full trace.
Thus trusted classical reads contribute to the same total weight as selected ordinary calls. -/
@[expose]
noncomputable def withReadWeight
    (w : ∀ i, Matrix (spec.In i × D) (spec.In i × D) ℂ → ℝ≥0∞) :
    ∀ i, Matrix ((withReadSpec spec Addr Ans).In i × D)
      ((withReadSpec spec Addr Ans).In i × D) ℂ → ℝ≥0∞
  | .inl i, ρ => w i ρ
  | .inr _, ρ => ENNReal.ofReal ρ.trace.re

/-- The combined weight is trace-bounded when the ordinary selected weight is. -/
theorem withReadWeight_le_trace
    {w : ∀ i, Matrix (spec.In i × D) (spec.In i × D) ℂ → ℝ≥0∞}
    (hw : ∀ i ρ, ρ.PosSemidef → w i ρ ≤ ENNReal.ofReal ρ.trace.re)
    (i : (withReadSpec spec Addr Ans).Port)
    (ρ : Matrix ((withReadSpec spec Addr Ans).In i × D)
      ((withReadSpec spec Addr Ans).In i × D) ℂ) (hρ : ρ.PosSemidef) :
    withReadWeight w i ρ ≤ ENNReal.ofReal ρ.trace.re := by
  cases i with
  | inl i => exact hw i ρ hρ
  | inr x => exact le_rfl

end QuantumRuntime

end Quantum
