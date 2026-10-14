/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.Quantum.Oracle.Compressed.Size

/-!
# The truncated compressed oracle

Chiesa, Di, Hu and Zheng (*How to Prove Post-Quantum Security for Succinct Non-Interactive
Reductions*, ePrint 2025/2166, §4.3) cut the database register of Zhandry's compressed oracle
(Crypto 2019) down to databases with at most `t` nonempty cells: with the projector
`P_size^(t) = Σ_{|D| ≤ t} |D⟩⟨D|`, the truncated oracle is `O^(t) = P_size^(t) cO P_size^(t)`.
Against a program with at most `q ≤ t` queries the truncation is invisible; the paper uses this
through the size invariant without numbering it.

* `Quantum.sizeProjector X Y t` is `P_size^(t)` acting on the database component of the joint
  register `(X × Y) × Database X Y`, the operator `1 ⊗ P_size^(t)`.
* `Quantum.truncatedOracle X Y t` is `O^(t)`. It is a contraction, not necessarily an isometry
  (`Quantum.posSemidef_one_sub_conjTranspose_truncatedOracle_mul_self`).
* `Quantum.truncatedRuntime X Y t` answers each call with the subinstrument
  `Quantum.truncatedQuery X Y t`, conjugation by `O^(t)`. Since `O^(t)` is a contraction,
  not necessarily an isometry, this map is trace non-increasing, not necessarily trace preserving:
  the weight it drops is that of the components whose database would leave the range of
  `P_size^(t)`. A one-outcome subinstrument expresses exactly this operator, with no completion
  by an extra failure outcome that the paper does not have, and it is a runtime step of the
  general model as it stands.

**Truncation is invisible** (`Quantum.jointPost_truncatedRuntime`,
`Quantum.outcomeLawWith_truncatedRuntime`): for a general program with at most `q` calls on every
path and `q ≤ t`, the joint post-state at every leaf, hence every observed law, is the same
against the truncated runtime as against the compressed runtime, hence, by Lemma 4.4 of
ePrint 2025/2166 (Zhandry's Lemma 4, `Quantum.outcomeLawWith_compressedRuntime`), as in the quantum
random-oracle model. The proof is the size invariant (`Quantum.forallQueries_compressedRuntime`):
every call receives an operator supported on databases with at most `q - 1 < t` cells, on which
`P_size^(t)` acts as the identity before and after the compressed oracle.

The phase form of equation (4) of ePrint 2025/2166, `O^(t)_ph = H_Y O^(t)_std H_Y`, needs the
Fourier transform on `Y`, which this development does not set up; it is not stated here.
-/

public section

open Matrix MeasureTheory
open scoped ComplexOrder

universe u v w

namespace Quantum

/-! ## Programs without calls -/

/-- A program that makes no call passes every condition on the operators presented to calls. -/
theorem QuantumRuntime.forallQueries_of_isQueryBound_zero {L : LocalSig.{u, v}}
    {spec : QuantumOracleSpec} {W : QReg → Type w} {A : QReg} (R : QuantumRuntime spec)
    (I : L.Interp) {P : ∀ (i : spec.Port) (E : QReg),
      Matrix ((spec.In i × R.D) × E) ((spec.In i × R.D) × E) ℂ → Prop}
    {x : QuantumComp L spec W A} (hx : x.IsQueryBound fun _ ↦ 0)
    (ρ : Matrix (A × R.D) (A × R.D) ℂ) : R.ForallQueries I P x ρ := by
  induction x using QuantumComp.inductionOn with
  | pure _ _ => trivial
  | primBind _ o k ih => exact fun b ↦ ih b (fun i ↦ hx i b) _
  | queryBind _ i E ℓ k ih => exact absurd hx.of_queryBind.1 (lt_irrefl 0)

/-! ## Projectors onto a support -/

namespace QuerySupportedOn

variable {M R Z : Type*} [Fintype M] [DecidableEq M]

/-- Conjugating by a diagonal operator whose entries are `1` on the support does not change an
operator supported there. -/
theorem conj_diagonal_eq_self {q : M → Z} {S : Set Z} {d : M → ℂ} (hd : ∀ m, q m ∈ S → d m = 1)
    {ρ : Matrix M M ℂ} (h : QuerySupportedOn q S ρ) : MatrixMap.conj (diagonal d) ρ = ρ := by
  ext m m'
  simp only [MatrixMap.conj_apply, diagonal_conjTranspose, mul_diagonal, diagonal_mul,
    Pi.star_apply]
  by_cases hm : ρ m m' = 0
  · simp [hm]
  · obtain ⟨h₁, h₂⟩ := h m m' hm
    simp [hd m h₁, hd m' h₂]

/-- Conjugating the first factor by a diagonal operator whose entries are `1` on the support does
not change an operator supported there through the first factor. -/
theorem amplify_conj_diagonal_eq_self {q : M → Z} {S : Set Z} {d : M → ℂ}
    (hd : ∀ m, q m ∈ S → d m = 1) {ρ : Matrix (M × R) (M × R) ℂ}
    (h : QuerySupportedOn (fun m : M × R ↦ q m.1) S ρ) :
    (MatrixMap.conj (diagonal d)).amplify R ρ = ρ := by
  ext ⟨m, r⟩ ⟨m', r'⟩
  rw [MatrixMap.amplify_apply, (h.block r r').conj_diagonal_eq_self hd]
  rfl

end QuerySupportedOn

/-- The complement `1 - P` of a Hermitian projector `P` is positive semidefinite, since it is
`(1 - P)ᴴ (1 - P)`. -/
theorem posSemidef_one_sub_of_projector {n : Type*} [Fintype n] [DecidableEq n]
    {P : Matrix n n ℂ} (hP : Pᴴ = P) (hPP : P * P = P) : (1 - P).PosSemidef := by
  have e : (1 - P)ᴴ * (1 - P) = 1 - P := by
    rw [conjTranspose_sub, conjTranspose_one, hP, Matrix.sub_mul, Matrix.mul_sub,
      Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.one_mul, hPP, sub_self, sub_zero]
  rw [← e]
  exact posSemidef_conjTranspose_mul_self (1 - P)

/-- If `P` is a Hermitian projector and `U` is an isometry, then `P U P` is a contraction:
`1 - (P U P)ᴴ (P U P)` is positive semidefinite. -/
theorem posSemidef_one_sub_conjTranspose_mul_self_of_projector {n : Type*} [Fintype n]
    [DecidableEq n] {P U : Matrix n n ℂ} (hP : Pᴴ = P) (hPP : P * P = P) (hU : Uᴴ * U = 1) :
    (1 - (P * U * P)ᴴ * (P * U * P)).PosSemidef := by
  have hP₁ := posSemidef_one_sub_of_projector hP hPP
  have e : 1 - (P * U * P)ᴴ * (P * U * P) = (1 - P) + Pᴴ * (Uᴴ * (1 - P) * U) * P := by
    rw [conjTranspose_mul, conjTranspose_mul, hP]
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc P P, hPP, ← Matrix.mul_assoc Uᴴ U, hU, Matrix.one_mul, hPP]
    abel
  rw [e]
  exact hP₁.add ((hP₁.conjTranspose_mul_mul_same U).conjTranspose_mul_mul_same P)

/-! ## The truncated oracle -/

section truncated

variable (X Y : Type*) [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]

/-- The projector `P_size^(t)` of ePrint 2025/2166 onto the databases with at most `t` nonempty
cells, acting on the database component of the joint register: the operator `1 ⊗ P_size^(t)`. -/
@[expose]
noncomputable def sizeProjector (t : ℕ) :
    Matrix ((X × Y) × Database X Y) ((X × Y) × Database X Y) ℂ :=
  diagonal fun m ↦ if m.2.size ≤ t then 1 else 0

variable {X Y}

omit [Fintype Y] in
theorem conjTranspose_sizeProjector (t : ℕ) : (sizeProjector X Y t)ᴴ = sizeProjector X Y t := by
  rw [sizeProjector, diagonal_conjTranspose]
  congr 1
  funext m
  split_ifs <;> simp [*]

theorem sizeProjector_mul_self (t : ℕ) :
    sizeProjector X Y t * sizeProjector X Y t = sizeProjector X Y t := by
  rw [sizeProjector, diagonal_mul_diagonal]
  congr 1
  funext m
  split_ifs <;> simp

omit [Fintype Y] in
theorem posSemidef_one_sub_sizeProjector (t : ℕ) : (1 - sizeProjector X Y t).PosSemidef := by
  rw [sizeProjector, ← diagonal_one, diagonal_sub, posSemidef_diagonal_iff]
  intro m
  split_ifs <;> simp

variable [AddCommGroup Y]

variable (X Y) in
/-- The truncated compressed oracle `O^(t) = P_size^(t) cO P_size^(t)` of ePrint 2025/2166. -/
@[expose]
noncomputable def truncatedOracle (t : ℕ) :
    Matrix ((X × Y) × Database X Y) ((X × Y) × Database X Y) ℂ :=
  sizeProjector X Y t * compressedOracle X Y * sizeProjector X Y t

/-- The truncated oracle is a contraction, not necessarily an isometry. -/
theorem posSemidef_one_sub_conjTranspose_truncatedOracle_mul_self (t : ℕ) :
    (1 - (truncatedOracle X Y t)ᴴ * truncatedOracle X Y t).PosSemidef :=
  posSemidef_one_sub_conjTranspose_mul_self_of_projector (conjTranspose_sizeProjector t)
    (sizeProjector_mul_self t) conjTranspose_compressedOracle_mul_self

variable (X Y) in
/-- One query to the truncated compressed oracle: conjugation by `O^(t)`. It is a one-outcome
subinstrument that is trace non-increasing, not necessarily trace preserving, since `O^(t)` is a
contraction, not necessarily an isometry. -/
@[expose]
noncomputable def truncatedQuery (t : ℕ) :
    SubInstrument ((X × Y) × Database X Y) ((X × Y) × Database X Y) Unit :=
  SubInstrument.ofMap (MatrixMap.conj (truncatedOracle X Y t)) (MatrixMap.isCP_conj _)
    (MatrixMap.isTNI_conj (posSemidef_one_sub_conjTranspose_truncatedOracle_mul_self t))

@[simp]
theorem branch_truncatedQuery_apply (t : ℕ) (u : Unit) :
    (truncatedQuery X Y t).branch u = MatrixMap.conj (truncatedOracle X Y t) :=
  rfl

/-- On an operator presented to a call that is supported on databases with at most `n < t`
nonempty cells, the truncated and the compressed oracle, framed by any remainder, agree. -/
theorem amplify_conj_truncatedOracle_eq {E : Type*} {n t : ℕ} (hnt : n < t)
    {σ : Matrix (((X × Y) × Database X Y) × E) (((X × Y) × Database X Y) × E) ℂ}
    (hσ : QuerySupportedOn (fun m : ((X × Y) × Database X Y) × E ↦ m.1.2.size) (Set.Iic n) σ) :
    (MatrixMap.conj (truncatedOracle X Y t)).amplify E σ =
      (MatrixMap.conj (compressedOracle X Y)).amplify E σ := by
  have hd (m : (X × Y) × Database X Y) (hm : m.2.size ∈ Set.Iic t) :
      (fun m : (X × Y) × Database X Y ↦ if m.2.size ≤ t then (1 : ℂ) else 0) m = 1 := by
    simp [Set.mem_Iic.mp hm]
  have h₁ := QuerySupportedOn.amplify_conj_diagonal_eq_self hd
    (hσ.mono (Set.Iic_subset_Iic.mpr hnt.le))
  have h₂ := QuerySupportedOn.amplify_conj_diagonal_eq_self hd
    (hσ.amplify_conj_compressedOracle.mono (Set.Iic_subset_Iic.mpr hnt))
  rw [truncatedOracle, MatrixMap.conj_mul, MatrixMap.conj_mul, MatrixMap.amplify_comp,
    MatrixMap.amplify_comp, LinearMap.comp_apply, LinearMap.comp_apply, sizeProjector, h₁, h₂]

end truncated

/-! ## The truncated runtime -/

section truncatedRuntime

variable {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]

variable (X Y) in
/-- The truncated compressed oracle as a runtime: the database register started with every cell
empty, each call answered by `Quantum.truncatedQuery X Y t`. It is reducible for the same reason
as `Quantum.compressedRuntime`. -/
@[expose, reducible]
noncomputable def truncatedRuntime (t : ℕ) : QuantumRuntime (qromSpec X Y) where
  D := QReg.of (Database X Y)
  init := SubState.basis Database.empty
  step _ := truncatedQuery X Y t

theorem truncatedRuntime_step (t : ℕ) (i : Unit) :
    (truncatedRuntime X Y t).step i = truncatedQuery X Y t :=
  rfl

variable {L : LocalSig.{u, v}} {W : QReg → Type w} {A B : QReg} {α : Type w}

/-- **Truncation is invisible** (ePrint 2025/2166, §4.3). For a program that makes at most `q`
calls on every path and `q ≤ t`, the joint post-state at every leaf is the same against the
truncated runtime as against the compressed runtime. -/
theorem jointPost_truncatedRuntime (I : L.Interp) {x : QuantumComp L (qromSpec X Y) W A}
    {q t : ℕ} (hx : x.IsQueryBound fun _ ↦ q) (hqt : q ≤ t) (ρ : SubState A) (p : Σ u, W u) :
    (truncatedRuntime X Y t).jointPost I x ρ p = (compressedRuntime X Y).jointPost I x ρ p := by
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · exact (QuantumRuntime.jointPost_eq_of_forallQueries (D := (compressedRuntime X Y).D)
      (σ := (compressedRuntime X Y).init) (s₁ := (compressedRuntime X Y).step)
      (s₂ := (truncatedRuntime X Y t).step) (P := fun _ _ _ ↦ False) I
      (fun _ _ _ h ↦ h.elim)
      ((compressedRuntime X Y).forallQueries_of_isQueryBound_zero I hx _) p).symm
  · exact (QuantumRuntime.jointPost_eq_of_forallQueries (D := (compressedRuntime X Y).D)
      (σ := (compressedRuntime X Y).init) (s₁ := (compressedRuntime X Y).step)
      (s₂ := (truncatedRuntime X Y t).step)
      (P := fun _ E σ ↦ QuerySupportedOn (fun m : ((X × Y) × Database X Y) × E ↦ m.1.2.size)
        (Set.Iic (q - 1)) σ) I
      (fun _ _ _ hσ _ ↦
        (amplify_conj_truncatedOracle_eq (n := q - 1) (t := t) (by omega) hσ).symm)
      (forallQueries_compressedRuntime_prod_init I hx ρ) p).symm

/-- **Truncation is invisible**, for observed laws: for a program that makes at most `q`
calls on every path and `q ≤ t`, every observed law is the same against the truncated runtime as
against the compressed runtime. -/
theorem outcomeLawWith_truncatedRuntime {γ : Type*} [MeasurableSpace γ] (I : L.Interp)
    {x : QuantumComp L (qromSpec X Y) W A} {q t : ℕ} (hx : x.IsQueryBound fun _ ↦ q)
    (hqt : q ≤ t) (ρ : SubState A) (f : (Σ u, W u) → γ) :
    (truncatedRuntime X Y t).outcomeLawWith I x ρ f =
      (compressedRuntime X Y).outcomeLawWith I x ρ f := by
  simp only [QuantumRuntime.outcomeLawWith]
  refine congrArg Measure.sum (funext fun p ↦ ?_)
  rw [jointPost_truncatedRuntime I hx hqt]

/-- For a program that makes at most `q ≤ t` calls on every path, every observed law against the
truncated runtime is the law of the quantum random-oracle model. -/
theorem outcomeLawWith_truncatedRuntime_eq_qromLawWith [SampleableType (X → Y)] {γ : Type*}
    [MeasurableSpace γ] (I : L.Interp) {x : QuantumComp L (qromSpec X Y) W A} {q t : ℕ}
    (hx : x.IsQueryBound fun _ ↦ q) (hqt : q ≤ t) (ρ : SubState A) (f : (Σ u, W u) → γ) :
    (truncatedRuntime X Y t).outcomeLawWith I x ρ f = qromLawWith I x ρ fun _ ↦ f := by
  rw [outcomeLawWith_truncatedRuntime I hx hqt, outcomeLawWith_compressedRuntime]

/-- **Truncation is invisible**, for fixed-register programs. -/
theorem outcomeLaw₂_truncatedRuntime [MeasurableSpace α] (I : L.Interp)
    {x : QuantumComp₂ L (qromSpec X Y) A B α} {q t : ℕ} (hx : x.IsQueryBound fun _ ↦ q)
    (hqt : q ≤ t) (ρ : SubState A) :
    (truncatedRuntime X Y t).outcomeLaw₂ I x ρ = (compressedRuntime X Y).outcomeLaw₂ I x ρ := by
  rw [QuantumRuntime.outcomeLaw₂_eq_outcomeLawWith, QuantumRuntime.outcomeLaw₂_eq_outcomeLawWith]
  exact outcomeLawWith_truncatedRuntime (W := QuantumComp₂.Leaf B α) I hx hqt ρ _

/-- For a fixed-register program that makes at most `q ≤ t` calls on every path, the law of its
value against the truncated runtime is the law of the quantum random-oracle model. -/
theorem outcomeLaw₂_truncatedRuntime_eq_qromLaw₂ [SampleableType (X → Y)] [MeasurableSpace α]
    (I : L.Interp) {x : QuantumComp₂ L (qromSpec X Y) A B α} {q t : ℕ}
    (hx : x.IsQueryBound fun _ ↦ q) (hqt : q ≤ t) (ρ : SubState A) :
    (truncatedRuntime X Y t).outcomeLaw₂ I x ρ = qromLaw₂ I x ρ := by
  rw [outcomeLaw₂_truncatedRuntime I hx hqt, outcomeLaw₂_compressedRuntime]

end truncatedRuntime

end Quantum
