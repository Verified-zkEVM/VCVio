/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.Quantum.Oracle.Compressed.CollisionBlocks
public import VCVio.Quantum.Oracle.Emulated

/-!
# Charged collision bounds for coherent oracle interfaces

The operator certificate of bounds-note (NOTE) equations (87)–(89), (91) lifts through a
coherent port index. It formalizes NOTE's refinement of ePrint 2025/2166 §9.3's
collision-event argument (Lemma 9.6, p. 61; event bound, pp. 64–65).
Its charge is the actual input mass on the selected ordinary interfaces, including programs
with entangled workspaces and adaptive local instruments.
-/

public section

open Matrix
open scoped Kronecker ComplexOrder ENNReal

namespace Quantum
namespace EmulatedOracle

section blocks

variable {P : Type} [Fintype P] [DecidableEq P] {In : P → QReg} {D : QReg}

/-- Lift a dependent family of port operators to the coherent register. -/
@[expose]
def coherentBlocks (A : ∀ p, Matrix (In p × D) (In p × D) ℂ) :
    Matrix (cohIn In × D) (cohIn In × D) ℂ :=
  (blockDiagonal' A).submatrix (Equiv.sigmaProdDistrib (fun p ↦ In p) D)
    (Equiv.sigmaProdDistrib (fun p ↦ In p) D)

/-- Coherent blocks preserve addition. -/
theorem coherentBlocks_add (A B : ∀ p, Matrix (In p × D) (In p × D) ℂ) :
    coherentBlocks (A + B) = coherentBlocks A + coherentBlocks B := by
  simp only [coherentBlocks, blockDiagonal'_add, submatrix_add]
  rfl

/-- Coherent blocks preserve subtraction. -/
theorem coherentBlocks_sub (A B : ∀ p, Matrix (In p × D) (In p × D) ℂ) :
    coherentBlocks (A - B) = coherentBlocks A - coherentBlocks B := by
  simp only [coherentBlocks, blockDiagonal'_sub, submatrix_sub]
  rfl

/-- Coherent blocks preserve scalar multiplication. -/
theorem coherentBlocks_smul (r : ℝ) (A : ∀ p, Matrix (In p × D) (In p × D) ℂ) :
    coherentBlocks (r • A) = r • coherentBlocks A := by
  simp only [coherentBlocks, blockDiagonal'_smul, submatrix_smul]
  rfl

/-- Coherent blocks preserve products. -/
theorem coherentBlocks_mul (A B : ∀ p, Matrix (In p × D) (In p × D) ℂ) :
    coherentBlocks (A * B) = coherentBlocks A * coherentBlocks B := by
  change (blockDiagonal' (fun p ↦ A p * B p)).submatrix _ _ = _
  rw [blockDiagonal'_mul, submatrix_mul _ _ _ (Equiv.sigmaProdDistrib _ D) _
    (Equiv.sigmaProdDistrib _ D).bijective]
  rfl

/-- Coherent blocks preserve adjoints. -/
theorem coherentBlocks_adjoint (A : ∀ p, Matrix (In p × D) (In p × D) ℂ) :
    coherentBlocks (fun p ↦ (A p)ᴴ) = (coherentBlocks A)ᴴ := by
  simp only [coherentBlocks, ← blockDiagonal'_conjTranspose, conjTranspose_submatrix]

/-- Positive semidefinite port operators give a positive semidefinite coherent operator. -/
theorem posSemidef_coherentBlocks {A : ∀ p, Matrix (In p × D) (In p × D) ℂ}
    (hA : ∀ p, (A p).PosSemidef) : (coherentBlocks A).PosSemidef :=
  (posSemidef_blockDiagonal' hA).submatrix _

/-- A common private-register operator is unchanged by coherent block assembly. -/
theorem coherentBlocks_database (A : Matrix D D ℂ) :
    coherentBlocks (fun p ↦ (1 : Matrix (In p) (In p) ℂ) ⊗ₖ A) =
      (1 : Matrix (cohIn In) (cohIn In) ℂ) ⊗ₖ A := by
  ext ⟨⟨p, a⟩, d⟩ ⟨⟨p', a'⟩, d'⟩
  by_cases h : p = p'
  · subst p'
    simp [coherentBlocks, blockDiagonal'_apply_eq, one_apply]
  · simp [coherentBlocks, blockDiagonal'_apply_ne _ _ _ h, one_apply, h]

/-- The coherent unitary is the coherent assembly of the individual port unitaries. -/
theorem coherentBlocks_unitary (E : EmulatedOracle P In) :
    coherentBlocks E.U = E.coherent.U () := rfl

/-- The charge operator selects the ordinary port components. -/
@[expose]
noncomputable def selectedCharge (selected : P → Bool) (θ : ℝ) :
    Matrix (cohIn In × D) (cohIn In × D) ℂ :=
  coherentBlocks (fun p ↦ (if selected p then θ else 0) • 1)

/-- Coherent assembly preserves both local operator inequalities of the collision certificate. -/
theorem coherent_collision_bounds (E : EmulatedOracle P In)
    (A B Q : Matrix E.S E.S ℂ) (selected : P → Bool) (θ r : ℝ)
    (h : ∀ p,
      let Δ := chargedDrop (E.U p) (1 ⊗ₖ A) (1 ⊗ₖ B)
        (if selected p then θ else 0)
      let C := (1 ⊗ₖ Q) * E.U p - E.U p * (1 ⊗ₖ Q)
      Δ.PosSemidef ∧ (r • Δ - Cᴴ * C).PosSemidef) :
    let U := E.coherent.U ()
    let Δ := (1 ⊗ₖ A) + selectedCharge selected θ - Uᴴ * (1 ⊗ₖ B) * U
    let C := (1 ⊗ₖ Q) * U - U * (1 ⊗ₖ Q)
    Δ.PosSemidef ∧ (r • Δ - Cᴴ * C).PosSemidef := by
  let F (M : Matrix E.S E.S ℂ) := fun p ↦ (1 : Matrix (In p) (In p) ℂ) ⊗ₖ M
  let T : ∀ p, Matrix (In p × E.S) (In p × E.S) ℂ :=
    fun p ↦ (if selected p then θ else 0) • 1
  let C := F Q * E.U - E.U * F Q
  let Δ := F A + T - (fun p ↦ (E.U p)ᴴ) * F B * E.U
  have hd : (coherentBlocks Δ).PosSemidef := posSemidef_coherentBlocks (fun p ↦ (h p).1)
  have hl : (coherentBlocks (r • Δ - (fun p ↦ (C p)ᴴ) * C)).PosSemidef :=
    posSemidef_coherentBlocks (fun p ↦ (h p).2)
  dsimp only [Δ, C] at hd hl
  simp only [coherentBlocks_sub, coherentBlocks_add, coherentBlocks_mul,
    coherentBlocks_smul] at hd hl
  rw [coherentBlocks_adjoint E.U] at hd hl
  rw [coherentBlocks_adjoint (F Q * E.U - E.U * F Q)] at hl
  simp only [coherentBlocks_sub, coherentBlocks_mul] at hl
  simp only [F, coherentBlocks_database, coherentBlocks_unitary] at hd hl
  exact ⟨hd, hl⟩

/-- Coherent diagonal blocks form the diagonal with the corresponding port-dependent entries. -/
theorem coherentBlocks_diagonal (f : ∀ p, In p × D → ℂ) :
    coherentBlocks (fun p ↦ diagonal (f p)) =
      diagonal (fun a : cohIn In × D ↦ f a.1.1 (a.1.2, a.2)) := by
  rw [coherentBlocks, blockDiagonal'_diagonal, submatrix_diagonal_equiv]
  rfl

/-- The selected charge is diagonal in the coherent index. -/
theorem selectedCharge_eq_diagonal (selected : P → Bool) (θ : ℝ) :
    selectedCharge (In := In) (D := D) selected θ =
      diagonal (fun a : cohIn In × D ↦ ((if selected a.1.1 then θ else 0 : ℝ) : ℂ)) := by
  unfold selectedCharge
  have he : (fun p ↦ (if selected p then θ else 0) • (1 : Matrix (In p × D) (In p × D) ℂ)) =
      fun p ↦ diagonal (fun _ : In p × D ↦ ((if selected p then θ else 0 : ℝ) : ℂ)) := by
    funext p
    rw [← diagonal_one, ← diagonal_smul]
    congr 1
    funext a
    cases selected p <;> simp
  rw [he, coherentBlocks_diagonal]

/-- The charge trace is the selected ordinary input mass times the scalar charge. -/
theorem trace_selectedCharge (E : EmulatedOracle P In) (selected : P → Bool) (θ : ℝ)
    (σ : Matrix (cohIn In × E.S) (cohIn In × E.S) ℂ) :
    (selectedCharge selected θ * σ).trace =
      (θ : ℂ) * ∑ p, if selected p then (MatrixMap.conj (E.indexProj p) σ).trace else 0 := by
  simp_rw [E.trace_conj_indexProj]
  have hs : (∑ p, if selected p then
      ∑ a : cohIn In × E.S, if a.1.1 = p then σ a a else 0 else 0) =
      ∑ a : cohIn In × E.S, if selected a.1.1 then σ a a else 0 := by
    calc
      _ = ∑ p, ∑ a : cohIn In × E.S,
          if selected p then (if a.1.1 = p then σ a a else 0) else 0 := by
        apply Finset.sum_congr rfl
        intro p _
        cases selected p <;> simp
      _ = ∑ a : cohIn In × E.S, ∑ p,
          if selected p then (if a.1.1 = p then σ a a else 0) else 0 := Finset.sum_comm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro a _
        rw [Finset.sum_eq_single a.1.1]
        · simp
        · intro p _ hp
          simp [Ne.symm hp]
        · simp
  rw [hs, selectedCharge_eq_diagonal, Finset.mul_sum]
  simp only [Matrix.trace, diag_apply, diagonal_mul]
  apply Finset.sum_congr rfl
  intro a _
  cases selected a.1.1 <;> simp

/-- The weight of the selected ordinary interfaces on the current coherent input. -/
@[expose]
noncomputable def selectedMass (E : EmulatedOracle P In) (selected : P → Bool)
    (σ : Matrix (cohIn In × E.S) (cohIn In × E.S) ℂ) : ℝ≥0∞ :=
  ∑ p, if selected p then ENNReal.ofReal (MatrixMap.conj (E.indexProj p) σ).trace.re else 0

/-- The nonnegative charge trace equals the scalar charge times the selected mass. -/
theorem ofReal_trace_selectedCharge (E : EmulatedOracle P In) (selected : P → Bool)
    {θ : ℝ} (hθ : 0 ≤ θ) {σ : Matrix (cohIn In × E.S) (cohIn In × E.S) ℂ}
    (hσ : σ.PosSemidef) : ENNReal.ofReal (selectedCharge selected θ * σ).trace.re =
      ENNReal.ofReal θ * E.selectedMass selected σ := by
  rw [trace_selectedCharge E, Complex.re_ofReal_mul, Complex.re_sum,
    ENNReal.ofReal_mul hθ, ENNReal.ofReal_sum_of_nonneg]
  · congr 1
    apply Finset.sum_congr rfl
    intro p _
    cases selected p <;> simp
  · intro p _
    split_ifs
    · exact (hσ.mul_mul_conjTranspose_same _).trace_re_nonneg
    · simp

/-- The actual total query mass on the selected ordinary interfaces. -/
@[expose]
noncomputable def selectedTotalMass (E : EmulatedOracle P In) {L : LocalSig}
    (I : L.Interp) {W : QReg → Type*} {A : QReg} (selected : P → Bool)
    (x : QuantumComp L (cohSpec In) W A) (ρ : Matrix (A × E.S) (A × E.S) ℂ) : ℝ≥0∞ :=
  ∑ p, if selected p then E.totalMass I x ρ p else 0

/-- Summing the selected input mass over query positions gives its actual total mass. -/
theorem tsum_queryWeight_selectedMass (E : EmulatedOracle P In) {L : LocalSig}
    (I : L.Interp) {W : QReg → Type*} {A : QReg} (selected : P → Bool)
    (x : QuantumComp L (cohSpec In) W A) (ρ : Matrix (A × E.S) (A × E.S) ℂ) :
    ∑' n, E.coherent.toRuntime.queryWeight I (fun _ σ ↦ E.selectedMass selected σ) x ρ n =
      E.selectedTotalMass I selected x ρ := by
  let f := fun p (_ : Unit) (σ : Matrix (cohIn In × E.S) (cohIn In × E.S) ℂ) ↦
    if selected p then ENNReal.ofReal (MatrixMap.conj (E.indexProj p) σ).trace.re else 0
  have hw n : E.coherent.toRuntime.queryWeight I
      (fun _ σ ↦ E.selectedMass selected σ) x ρ n =
      ∑' p, E.coherent.toRuntime.queryWeight I (f p) x ρ n := by
    rw [QuantumRuntime.tsum_queryWeight]
    congr 1
    funext i σ
    exact (tsum_fintype _).symm
  simp_rw [hw]
  rw [ENNReal.tsum_comm, tsum_fintype]
  apply Finset.sum_congr rfl
  intro p _
  cases hp : selected p
  · simp only [f, hp, Bool.false_eq_true, ite_false]
    have hz n := E.coherent.toRuntime.queryWeight_const_mul I
      (w := fun _ _ ↦ 0) 0 x ρ n
    simp only [zero_mul] at hz
    simp only [hz, tsum_zero]
  · simp [f, hp, totalMass]

/-- Selected mass up to the query budget is bounded both by actual mass and by the budget. -/
theorem sum_queryWeight_selectedMass_le (E : EmulatedOracle P In) {L : LocalSig}
    (I : L.Interp) {W : QReg → Type*} {A : QReg} (selected : P → Bool)
    {x : QuantumComp L (cohSpec In) W A} {t : ℕ} (hx : x.IsQueryBoundAt () t)
    {ρ : Matrix (A × E.S) (A × E.S) ℂ} (hρ : ρ.PosSemidef) (htr : ρ.trace.re ≤ 1) :
    ∑ n ∈ Finset.range t,
      E.coherent.toRuntime.queryWeight I (fun _ σ ↦ E.selectedMass selected σ) x ρ n ≤
        min (E.selectedTotalMass I selected x ρ) t := by
  have hm : E.selectedTotalMass I selected x ρ ≤ t := by
    calc
      _ ≤ ∑ p, E.totalMass I x ρ p := by
        apply Finset.sum_le_sum
        intro p _
        split_ifs <;> simp
      _ ≤ t * ENNReal.ofReal ρ.trace.re := E.sum_totalMass_le I hx hρ
      _ ≤ t * 1 := by gcongr; exact ENNReal.ofReal_le_one.mpr htr
      _ = _ := mul_one _
  have hs : (∑ n ∈ Finset.range t,
      E.coherent.toRuntime.queryWeight I (fun _ σ ↦ E.selectedMass selected σ) x ρ n) ≤
      E.selectedTotalMass I selected x ρ := by
    rw [← E.tsum_queryWeight_selectedMass I selected x ρ]
    exact ENNReal.sum_le_tsum _
  exact le_min hs (hs.trans hm)

/-- A positive operator leak inequality bounds its weight on every positive input. -/
theorem ofReal_trace_conj_le {J : Type*} [Fintype J]
    (C Δ : Matrix J J ℂ) {r : ℝ} (hr : 0 ≤ r)
    (h : (r • Δ - Cᴴ * C).PosSemidef) {σ : Matrix J J ℂ} (hσ : σ.PosSemidef) :
    ENNReal.ofReal (MatrixMap.conj C σ).trace.re ≤
      ENNReal.ofReal r * ENNReal.ofReal (Δ * σ).trace.re := by
  have ht := h.trace_mul_re_nonneg hσ
  simp only [Matrix.sub_mul, Matrix.smul_mul, Matrix.trace_sub, Matrix.trace_smul,
    Complex.sub_re, Complex.real_smul, Complex.re_ofReal_mul] at ht
  rw [← ENNReal.ofReal_mul hr, MatrixMap.trace_conj_apply]
  exact ENNReal.ofReal_le_ofReal (sub_nonneg.mp ht)

/-- Portwise squared operator bounds lift to coherent selected mass on a supported input.
The private projector may depend on the query position; no measurement of its grade or of
its coherent port index is performed. -/
theorem ofReal_trace_coherentBlocks_conj_le_selectedMass (E : EmulatedOracle P In)
    (C : ∀ p, Matrix (In p × E.S) (In p × E.S) ℂ)
    (P₀ : Matrix E.S E.S ℂ) (selected : P → Bool) {r : ℝ} (hr : 0 ≤ r)
    (hC : ∀ p,
      ((if selected p then r else 0) • (1 : Matrix (In p × E.S) (In p × E.S) ℂ) -
        (C p * (1 ⊗ₖ P₀))ᴴ * (C p * (1 ⊗ₖ P₀))).PosSemidef)
    {σ : Matrix (cohIn In × E.S) (cohIn In × E.S) ℂ} (hσ : σ.PosSemidef)
    (hsupp : MatrixMap.conj ((1 : Matrix (cohIn In) (cohIn In) ℂ) ⊗ₖ P₀) σ = σ) :
    ENNReal.ofReal (MatrixMap.conj (coherentBlocks C) σ).trace.re ≤
      ENNReal.ofReal r * E.selectedMass selected σ := by
  let B := fun p ↦ C p * ((1 : Matrix (In p) (In p) ℂ) ⊗ₖ P₀)
  have hb := posSemidef_coherentBlocks hC
  change (coherentBlocks ((fun p ↦ (if selected p then r else 0) • 1) -
    (fun p ↦ (B p)ᴴ) * B)).PosSemidef at hb
  rw [coherentBlocks_sub, coherentBlocks_mul, coherentBlocks_adjoint] at hb
  have he : coherentBlocks B = coherentBlocks C *
      ((1 : Matrix (cohIn In) (cohIn In) ℂ) ⊗ₖ P₀) := by
    change coherentBlocks (C * (fun p ↦ (1 : Matrix (In p) (In p) ℂ) ⊗ₖ P₀)) = _
    rw [coherentBlocks_mul, coherentBlocks_database]
  rw [he] at hb
  have ht := ofReal_trace_conj_le
    (coherentBlocks C * ((1 : Matrix (cohIn In) (cohIn In) ℂ) ⊗ₖ P₀))
    (selectedCharge selected r) (r := 1) (by norm_num)
    (by simpa only [one_smul, selectedCharge] using hb) hσ
  rw [MatrixMap.conj_mul, LinearMap.comp_apply, hsupp] at ht
  simpa only [ENNReal.ofReal_one, one_mul, E.ofReal_trace_selectedCharge selected hr hσ]
    using ht

/-- The collision bound of NOTE (87)–(89), (91) from per-port operator inequalities
and zero initial potential.
This supports NOTE's refinement of the paper's §9.3 collision-event argument
(Lemma 9.6, p. 61; event bound, pp. 64–65).
The mass on the right is the actual mass of the selected interfaces of the program. -/
theorem eventWeight_le_collision_of_port_bounds (E : EmulatedOracle P In) {L : LocalSig}
    (I : L.Interp) {W : QReg → Type*} {A : QReg} (selected : P → Bool)
    (Q : Matrix E.S E.S ℂ) (hQ : Qᴴ = Q) (hQQ : Q * Q = Q)
    (K : ℕ → Matrix E.S E.S ℂ) {t : ℕ} (N : ℝ) (hN : 0 < N)
    (hport : ∀ n < t, ∀ p,
      let Δ := chargedDrop (E.U p) (1 ⊗ₖ ((K n)ᴴ * K n))
        (1 ⊗ₖ ((K (n + 1))ᴴ * K (n + 1))) (if selected p then (t : ℝ) / 2 else 0)
      let C := (1 ⊗ₖ Q) * E.U p - E.U p * (1 ⊗ₖ Q)
      Δ.PosSemidef ∧ (collisionRate t n N • Δ - Cᴴ * C).PosSemidef)
    (x : QuantumComp L (cohSpec In) W A) (hx : x.IsQueryBound (fun _ ↦ t))
    {ρ : Matrix (A × E.S) (A × E.S) ℂ} (hρ : ρ.PosSemidef) (htr : ρ.trace.re ≤ 1)
    (hρQ : MatrixMap.conj ((1 : Matrix A A ℂ) ⊗ₖ Q) ρ = 0)
    (hinit : QuantumRuntime.potential (K 0) ρ = 0) :
    E.coherent.toRuntime.eventWeight I Q x ρ ≤
      ENNReal.ofReal ((7 * t + 5) * t / (4 * N)) *
        min (E.selectedTotalMass I selected x ρ) t := by
  classical
  let U := E.coherent.U ()
  let Δ n := (1 ⊗ₖ ((K n)ᴴ * K n)) + selectedCharge selected ((t : ℝ) / 2) -
    Uᴴ * (1 ⊗ₖ ((K (n + 1))ᴴ * K (n + 1))) * U
  let δ := fun n (_ : Unit) (σ : Matrix (cohIn In × E.S) (cohIn In × E.S) ℂ) ↦
    ENNReal.ofReal (Δ n * σ).trace.re
  have hb n (hn : n < t) := E.coherent_collision_bounds ((K n)ᴴ * K n)
    ((K (n + 1))ᴴ * K (n + 1)) Q selected ((t : ℝ) / 2)
    (collisionRate t n N) (hport n hn)
  have hd n (hn : n < t) (i : Unit)
      (σ : Matrix (cohIn In × E.S) (cohIn In × E.S) ℂ) (hσ : σ.PosSemidef) :
      δ n i σ + ∑' r, QuantumRuntime.potential (K (n + 1))
          ((E.coherent.toRuntime.step i).branch r σ) ≤
        QuantumRuntime.potential (K n) σ + ENNReal.ofReal ((t : ℝ) / 2) *
          E.selectedMass selected σ := by
    cases i
    have h := QuantumRuntime.drop_of_posSemidef (fun _ : Unit ↦ U) (K n) (K (n + 1))
      (selectedCharge selected ((t : ℝ) / 2)) hσ
      (by simpa only [Fintype.sum_unique] using (hb n hn).1)
    simp only [Fintype.sum_unique] at h
    rw [E.ofReal_trace_selectedCharge selected (by positivity) hσ] at h
    exact h
  have hl n (hn : n < t) (i : Unit)
      (σ : Matrix (cohIn In × E.S) (cohIn In × E.S) ℂ) (hσ : σ.PosSemidef) :
      ∑' r : Unit, ENNReal.ofReal (MatrixMap.conj
          ((1 ⊗ₖ Q) * E.coherent.U i - E.coherent.U i * (1 ⊗ₖ Q)) σ).trace.re ≤
        ENNReal.ofReal (collisionRate t n N) * δ n i σ := by
    cases i
    simpa only [tsum_fintype, Fintype.sum_unique] using
      ofReal_trace_conj_le _ _ (collisionRate_nonneg t n hN.le) (hb n hn).2 hσ
  by_cases ht : 0 < t
  · exact QuantumRuntime.eventWeight_le_of_collisionCertificate I
      E.coherent.toRuntime_step_branch hQ hQQ E.init x hx Finset.univ (by simp)
      ht (by simp) N hN K δ (fun _ σ ↦ E.selectedMass selected σ) hd hl hρ hρQ hinit
      (E.selectedTotalMass I selected x ρ)
      (E.sum_queryWeight_selectedMass_le I selected (hx ()) hρ htr)
  · have ht0 : t = 0 := by omega
    have h := QuantumRuntime.eventWeight_le_of_potential I
      E.coherent.toRuntime_step_branch hQ hQQ E.init x hx Finset.univ (by simp)
      (N := t) (by simp) K δ
      (fun _ _ σ ↦ ENNReal.ofReal ((t : ℝ) / 2) * E.selectedMass selected σ)
      (fun n ↦ ENNReal.ofReal (collisionRate t n N)) hd hl hρ hρQ
    simpa only [ht0, Finset.range_zero, Finset.sum_empty, zero_mul, Nat.cast_zero,
      mul_zero, zero_div, ENNReal.ofReal_zero] using h

end blocks

end EmulatedOracle
end Quantum
