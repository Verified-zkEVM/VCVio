/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.Quantum.VC.Proof.Online
import all VCVio.Quantum.VC.Proof.Online

/-!
# Online indistinguishability from recording commutators

The private recording swap identifies the two recording laws. Population-restricted ordinary
port bounds give both square-root comparisons of ePrint 2025/2166, Definition 7.3, P5,
pp. 50–51, and Lemma 9.7, pp. 65–70. The probability cap also covers infinite mass budgets.
-/

public section

open Matrix
open scoped Kronecker ENNReal ComplexOrder Matrix.Norms.L2Operator
namespace Quantum

namespace EmulatedOracle
variable {P : Type} [Fintype P] [DecidableEq P] {In : P → QReg}
/-- Conjugate every oracle port by a private unitary while keeping the initial state. -/
@[expose, reducible]
noncomputable def rotatePrivate (E : EmulatedOracle P In) (V : Matrix E.S E.S ℂ)
    (hV : V ∈ unitaryGroup _ ℂ) : EmulatedOracle P In where
  S := E.S
  init := E.init
  U p := (1 ⊗ₖ V)ᴴ * E.U p * (1 ⊗ₖ V)
  unitary p := by
    have h := kronecker_mem_unitary (one_mem (unitaryGroup (In p) ℂ)) hV
    exact mul_mem (mul_mem (Unitary.star_mem h) (E.unitary p)) h

/-- A private unitary rotation fixing initialization preserves every coherent observation law. -/
theorem outcomeLawWith_rotatePrivate (E : EmulatedOracle P In) (V : Matrix E.S E.S ℂ)
    (hV : V ∈ unitaryGroup _ ℂ) (hinit : MatrixMap.conj Vᴴ E.init.matrix = E.init.matrix)
    {L : LocalSig} (I : L.Interp) {W : QReg → Type*} {A : QReg}
    (x : QuantumComp L (cohSpec In) W A) (ρ : SubState A)
    {γ : Type*} [MeasurableSpace γ] (f : (Σ B, W B) → γ) :
    (E.rotatePrivate V hV).coherent.toRuntime.outcomeLawWith I x ρ f =
      E.coherent.toRuntime.outcomeLawWith I x ρ f := by
  have hv : V * Vᴴ = 1 := by
    simpa only [star_eq_conjTranspose] using mem_unitaryGroup_iff.mp hV
  apply outcomeLawWith_eq_of_intertwine E.coherent (E.rotatePrivate V hV).coherent Vᴴ
    (by simpa only [conjTranspose_conjTranspose] using hv)
  · intro i
    cases i
    apply coherent_U_mul_one_kronecker
    intro p
    change ((1 ⊗ₖ V)ᴴ * E.U p * (1 ⊗ₖ V)) * (1 ⊗ₖ Vᴴ) = (1 ⊗ₖ Vᴴ) * E.U p
    have he : (1 ⊗ₖ V) * ((1 : Matrix (In p) (In p) ℂ) ⊗ₖ Vᴴ) = 1 := by
      rw [← mul_kronecker_mul, hv, Matrix.one_mul,
        one_kronecker_one]
    rw [Matrix.mul_assoc, he, Matrix.mul_one, conjTranspose_kronecker, conjTranspose_one]
  · exact hinit
end EmulatedOracle

section
variable {A : Type*} [Fintype A] [DecidableEq A]
/-- Conjugating twice by a self-adjoint unitary fixes every operator. -/
theorem conjugate_involution (V U : Matrix A A ℂ) (hv : Vᴴ = V) (hV : Vᴴ * V = 1) :
    Vᴴ * (Vᴴ * U * V) * V = U := by
  have hh : V * V = 1 := by rwa [hv] at hV
  rw [hv]
  calc
    V * (V * U * V) * V = (V * V) * U * (V * V) := by simp only [Matrix.mul_assoc]
    _ = U := by rw [hh, Matrix.one_mul, Matrix.mul_one]
/-- Equal operators have zero source-projected discrepancy. -/
theorem gram_zero_of_eq (U V P : Matrix A A ℂ) (h : V = U) :
    ((0 : ℝ) • 1 - ((U - V) * P)ᴴ * ((U - V) * P)).PosSemidef := by
  subst V
  simpa using (PosSemidef.zero : (0 : Matrix A A ℂ).PosSemidef)
end
namespace VCOracle
variable {k : ℕ} {X Y Cm Z Yr Cell : Type} {Dm : Fin k → Type}
  [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Cm] [DecidableEq Cm] [Fintype Z] [DecidableEq Z] [AddGroup Z]
  [Fintype Yr] [DecidableEq Yr] [Fintype Cell] [DecidableEq Cell]
  [∀ i, Fintype (Dm i)] [∀ i, DecidableEq (Dm i)]
  (E : VCOracle k X Y) (ME : MultiExtractor k Cm Dm E.S) (code : TpDCode k Dm Z)
  (bot : Cell) (U : Matrix (Yr × Cell) (Yr × Cell) ℂ) (hU : U ∈ unitaryGroup _ ℂ)
/-- The ordinary-port recording comparison satisfies the source-projected Gram bound. -/
theorem withRecord_rotated_ordinary_gram
    (g : E.S → ℕ) (j : ℕ) (r : ℝ) (i : Fin k)
    (h : ‖permutationDefect (RecReg.swapEquiv ME) (E.U i) *
      diagonal (fun a : (X × Y) × E.S × RecReg k Cm Dm Cell ↦
        if g a.2.1 + RecReg.population bot a.2.2 ≤ j then (1 : ℂ) else 0)‖ ^ 2 ≤ r) :
    let F := (E.withRecordME ME code bot U hU).rotatePrivate (RecReg.swapUnitary ME)
      (RecReg.swapUnitary_mem_unitaryGroup ME)
    let C : Matrix ((X × Y) × E.S × RecReg k Cm Dm Cell)
        ((X × Y) × E.S × RecReg k Cm Dm Cell) ℂ :=
      (show Matrix ((X × Y) × E.S × RecReg k Cm Dm Cell)
          ((X × Y) × E.S × RecReg k Cm Dm Cell) ℂ from
        (E.withRecord ME code bot U hU).U (.inl (.inl i))) -
      (show Matrix ((X × Y) × E.S × RecReg k Cm Dm Cell)
          ((X × Y) × E.S × RecReg k Cm Dm Cell) ℂ from F.U (.inl (.inl i)))
    let P := (1 : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ diagonal
      (fun a : E.S × RecReg k Cm Dm Cell ↦
        if g a.1 + RecReg.population bot a.2 ≤ j then (1 : ℂ) else 0)
    (r • 1 - (C * P)ᴴ * (C * P)).PosSemidef := by
  exact posSemidef_rotated_port_difference_of_source_bound ME (E.U i) g bot j r h

/-- The private recording swap commutes with extraction (ePrint 2025/2166, Lemma 9.7, p. 69). -/
theorem withRecord_rotated_extract :
    let F := (E.withRecordME ME code bot U hU).rotatePrivate (RecReg.swapUnitary ME)
      (RecReg.swapUnitary_mem_unitaryGroup ME)
    F.U (.inl (.inr ())) = (E.withRecord ME code bot U hU).U (.inl (.inr ())) := by
  exact extractUnitary_swap_conjugacy ME code

/-- Conjugating split recording gives unsplit recording (ePrint 2025/2166, Lemma 9.13, p. 67). -/
theorem withRecord_rotated_record :
    let F := (E.withRecordME ME code bot U hU).rotatePrivate (RecReg.swapUnitary ME)
      (RecReg.swapUnitary_mem_unitaryGroup ME)
    F.U (.inr ()) = (E.withRecord ME code bot U hU).U (.inr ()) := by
  have hc := recordUnitary_swap_conjugacy ME U
  have hv := kronecker_mem_unitary (one_mem (unitaryGroup (TpIC k Cm × Yr) ℂ))
    (RecReg.swapUnitary_mem_unitaryGroup (Cell := Cell) ME)
  have hh : ((1 : Matrix (TpIC k Cm × Yr) (TpIC k Cm × Yr) ℂ) ⊗ₖ
      RecReg.swapUnitary (Cell := Cell) ME)ᴴ = 1 ⊗ₖ RecReg.swapUnitary ME := by
    rw [conjTranspose_kronecker, conjTranspose_one, RecReg.swapUnitary_conjTranspose]
  have he := conjugate_involution _ (recordUnitary (S := E.S) U) hh
    (mem_unitaryGroup_iff'.mp hv)
  rw [hc] at he
  exact he

/-- Recording comparison for arbitrary local instruments, coherent port choice and subnormalized
inputs. Ordinary source-projected commutator bounds and the joint population grade give both
square-root event inequalities, charging the ordinary mass in the unsplit recording execution.
This is the runtime form of ePrint 2025/2166, Lemma 9.7, pp. 65–70. -/
theorem outcomeLawWith_recording_rpow_bounds
    (g : E.S → ℕ)
    (hE : ∀ i a b s r, E.U i (a, s) (b, r) ≠ 0 → g s ≤ g r + 1)
    (hinit : QuerySupportedOn g (Set.Iic 0) E.init.matrix)
    (rate : ℕ → ℝ) (hrate : ∀ j, 0 ≤ rate j)
    {L : LocalSig} (I : L.Interp) {W : QReg → Type*} {A : QReg}
    {x : QuantumComp L (EmulatedOracle.cohSpec (recIn k X Y Cm Z Yr)) W A}
    {t : ℕ} (hx : x.IsQueryBound fun _ ↦ t) (ρ : SubState A)
    (hC : ∀ j < t, ∀ i,
      ‖permutationDefect (RecReg.swapEquiv ME) (E.U i) *
        diagonal (fun a : (X × Y) × E.S × RecReg k Cm Dm Cell ↦
          if g a.2.1 + RecReg.population bot a.2.2 ≤ j then (1 : ℂ) else 0)‖ ^ 2 ≤ rate j)
    {γ : Type*} [MeasurableSpace γ] (f : (Σ B, W B) → γ) {event : Set γ}
    (hevent : MeasurableSet event) :
    let R := E.withRecord ME code bot U hU
    let T := E.withRecordME ME code bot U hU
    let err := ((∑ j ∈ Finset.range t, ENNReal.ofReal (rate j)) *
      ∑ i : Fin k, R.totalMass I x (ρ.matrix ⊗ₖ R.init.matrix) (.inl (.inl i))) ^ (2⁻¹ : ℝ)
    R.coherent.toRuntime.outcomeLawWith I x ρ f event ^ (2⁻¹ : ℝ) ≤
      T.coherent.toRuntime.outcomeLawWith I x ρ f event ^ (2⁻¹ : ℝ) + err ∧
    T.coherent.toRuntime.outcomeLawWith I x ρ f event ^ (2⁻¹ : ℝ) ≤
      R.coherent.toRuntime.outcomeLawWith I x ρ f event ^ (2⁻¹ : ℝ) + err := by
  let R := E.withRecord ME code bot U hU
  let T := E.withRecordME ME code bot U hU
  let V := RecReg.swapUnitary (Cell := Cell) ME
  have hV := RecReg.swapUnitary_mem_unitaryGroup (Cell := Cell) ME
  let F := T.rotatePrivate V hV
  have hg : QuerySupportedOn
      (fun a : A × R.S ↦ g a.2.1 + RecReg.population bot a.2.2) (Set.Iic 0)
        (ρ.matrix ⊗ₖ R.init.matrix) := recording_initial_grade E bot g hinit ρ
  have hb := R.outcomeLawWith_rpow_bounds_of_graded_ports
    (fun a ↦ g a.1 + RecReg.population bot a.2)
    (fun p a b d d' h ↦ withRecord_U_grade E ME code bot g hE U hU p b a d' d h)
    F.U F.coherent.toRuntime.step (fun i a ↦ F.coherent.toRuntime_step_branch i a)
    I hx ρ hg ordinaryPort rate (fun j _ ↦ hrate j) (fun j hj p ↦ ?_) f hevent
  · have hi : MatrixMap.conj Vᴴ T.init.matrix = T.init.matrix := by
      have hh := RecReg.swapUnitary_conjTranspose (Cell := Cell) ME
      exact (congrArg (fun M ↦ MatrixMap.conj M T.init.matrix) hh).trans
        (RecReg.swapUnitary_initial ME E.init.matrix bot)
    have hl := T.outcomeLawWith_rotatePrivate V hV hi I x ρ f
    dsimp only at hb ⊢
    rw [selectedTotalMass_ordinaryPort] at hb
    change _ ∧ _ at hb
    rw [show (QuantumRuntime.mk R.S R.init F.coherent.toRuntime.step).outcomeLawWith I x ρ f =
      F.coherent.toRuntime.outcomeLawWith I x ρ f from rfl, hl] at hb
    exact hb
  · rcases p with (i | u) | u
    · exact withRecord_rotated_ordinary_gram E ME code bot U hU g j (rate j) i (hC j hj i)
    · cases u
      exact gram_zero_of_eq _ _ _ (withRecord_rotated_extract E ME code bot U hU)
    · cases u
      exact gram_zero_of_eq _ _ _ (withRecord_rotated_record E ME code bot U hU)

end VCOracle

namespace QuantumRuntime
variable {spec : QuantumOracleSpec} {L : LocalSig} {W : QReg → Type*} {A : QReg}
/-- Every observed event of a quantum runtime has subprobability mass. -/
theorem outcomeLawWith_le_one (R : QuantumRuntime spec) (I : L.Interp)
    (x : QuantumComp L spec W A) (ρ : SubState A)
    {γ : Type*} [MeasurableSpace γ] (f : (Σ B, W B) → γ) (s : Set γ) :
    R.outcomeLawWith I x ρ f s ≤ 1 := by
  let : MeasurableSpace (Σ B, W B) := ⊤
  calc
    _ ≤ R.outcomeLawWith I x ρ f Set.univ := MeasureTheory.measure_mono (Set.subset_univ _)
    _ = R.outcomeLaw I x ρ Set.univ := by
      rw [R.outcomeLawWith_apply_univ, ← R.outcomeLawWith_apply_univ I x ρ (fun p ↦ p),
        R.outcomeLawWith_id]
    _ ≤ 1 := MeasureTheory.measure_le_one _ _
end QuantumRuntime

/-- Square-root comparisons of subprobabilities allow an error cap of one. -/
theorem rpow_bounds_cap {p q ε : ℝ≥0∞} (hp : p ≤ 1) (hq : q ≤ 1)
    (h : p ^ (2⁻¹ : ℝ) ≤ q ^ (2⁻¹ : ℝ) + ε ^ (2⁻¹ : ℝ) ∧
      q ^ (2⁻¹ : ℝ) ≤ p ^ (2⁻¹ : ℝ) + ε ^ (2⁻¹ : ℝ)) :
    p ^ (2⁻¹ : ℝ) ≤ q ^ (2⁻¹ : ℝ) + (min 1 ε) ^ (2⁻¹ : ℝ) ∧
      q ^ (2⁻¹ : ℝ) ≤ p ^ (2⁻¹ : ℝ) + (min 1 ε) ^ (2⁻¹ : ℝ) := by
  rcases le_total ε 1 with hε | hε
  · simpa only [min_eq_right hε] using h
  · rw [min_eq_left hε, ENNReal.one_rpow]
    have hp' : p ^ (2⁻¹ : ℝ) ≤ 1 := by
      simpa using ENNReal.rpow_le_rpow hp (by norm_num : (0 : ℝ) ≤ 2⁻¹)
    have hq' : q ^ (2⁻¹ : ℝ) ≤ 1 := by
      simpa using ENNReal.rpow_le_rpow hq (by norm_num : (0 : ℝ) ≤ 2⁻¹)
    exact ⟨hp'.trans le_add_self, hq'.trans le_add_self⟩
universe v w
namespace VCOracle
variable {k : ℕ} {X Y Cm Z : Type} {Dm : Fin k → Type}
  [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Cm] [DecidableEq Cm] [Fintype Z] [DecidableEq Z] [AddGroup Z]
  [∀ i, Fintype (Dm i)] [∀ i, DecidableEq (Dm i)]
/-- P5 from ordinary-port source commutators and recording population grading.
The local operator hypothesis is quantified over finite recording cell types, independently
of the recording unitary and adversary. The conclusion covers every coherent adaptive program
and arbitrary local instruments in `OnlineIndistinguishable` (ePrint 2025/2166, Definition 7.3,
pp. 50–51). -/
theorem onlineIndistinguishable_of_recording_source_bounds
    (E : VCOracle k X Y) (ME : MultiExtractor k Cm Dm E.S) (code : TpDCode k Dm Z)
    (g : E.S → ℕ)
    (hE : ∀ i a b s r, E.U i (a, s) (b, r) ≠ 0 → g s ≤ g r + 1)
    (hinit : QuerySupportedOn g (Set.Iic 0) E.init.matrix)
    (rate : ℕ → ℝ) (hrate : ∀ j, 0 ≤ rate j)
    (hC : ∀ (Cell : Type) [Fintype Cell] [DecidableEq Cell] (bot : Cell) (j : ℕ) (i : Fin k),
      ‖permutationDefect (RecReg.swapEquiv ME) (E.U i) *
        diagonal (fun a : (X × Y) × E.S × RecReg k Cm Dm Cell ↦
          if g a.2.1 + RecReg.population bot a.2.2 ≤ j then (1 : ℂ) else 0)‖ ^ 2 ≤ rate j) :
    OnlineIndistinguishable.{v, w} E ME code
      (fun t wVC _ _ ↦ min 1 ((∑ j ∈ Finset.range t, ENNReal.ofReal (rate j)) * wVC)) := by
  intro Yr Cell _ _ _ _ bot U hU t wVC wME wRec A W x f ρ hx h₁ _ _
  have hb := outcomeLawWith_recording_rpow_bounds E ME code bot U hU g hE hinit rate hrate
    .instruments hx ρ (fun j _ i ↦ hC Cell bot j i) f (measurableSet_singleton true)
  dsimp only at hb ⊢
  have hm := ENNReal.rpow_le_rpow (mul_le_mul_right h₁
    (∑ j ∈ Finset.range t, ENNReal.ofReal (rate j))) (by norm_num : (0 : ℝ) ≤ 2⁻¹)
  exact rpow_bounds_cap
    ((E.withRecord ME code bot U hU).coherent.toRuntime.outcomeLawWith_le_one
      .instruments x ρ f {true})
    ((E.withRecordME ME code bot U hU).coherent.toRuntime.outcomeLawWith_le_one
      .instruments x ρ f {true})
    ⟨hb.1.trans (add_le_add le_rfl hm), hb.2.trans (add_le_add le_rfl hm)⟩
end VCOracle
section
variable {k : ℕ} {X Y Cm Z : Type} {Dm : Fin k → Type}
  [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]
  [Fintype Cm] [DecidableEq Cm] [Fintype Z] [DecidableEq Z] [AddGroup Z]
  [∀ i, Fintype (Dm i)] [∀ i, DecidableEq (Dm i)]
/-- The empty compressed-oracle family has total database size zero. -/
theorem compressedVCOracle_initial_totalSize :
    QuerySupportedOn (fun D : Fin k → Database X Y ↦ ∑ i, (D i).size) (Set.Iic 0)
      (compressedVCOracle k X Y).init.matrix := by
  change QuerySupportedOn _ _
    (SubState.basis (fun _ : Fin k ↦ (Database.empty : Database X Y))).matrix
  rw [SubState.matrix_basis]
  intro a b hab
  rw [Matrix.single_apply] at hab
  split_ifs at hab with he
  · rcases he with ⟨rfl, rfl⟩
    simp [Database.size]
  · exact (hab rfl).elim

/-- P5 for the old compressed oracle from occupied-key joint-label instabilities.
The coefficient 24 is from the bounds note, equation (30), and the repair note, equation (2);
the recording argument follows ePrint 2025/2166, Lemma 9.7, pp. 65–70. Empty occupied sets
contribute zero, and nonempty sectors are combined by a maximum, without measuring their keys. -/
theorem compressed_online_of_instability [OracleSpec.UniformAnswerMeasure (X →ₒ Y)]
    (ME : MultiExtractor k Cm Dm (Fin k → Database X Y)) (code : TpDCode k Dm Z)
    (rate : ℕ → ℝ) (hrate : ∀ j, 0 ≤ rate j)
    (hi : ∀ (t : ℕ) (i : Fin k) (keys : Finset (TpIC k Cm)),
      1 ≤ keys.card → keys.card ≤ t → ∀ Dfix : Fin k → Database X Y,
        24 * (Database.instability
          (fun D ↦ fun q : keys ↦ ME.extract q.1 (Function.update Dfix i D))
          (t - keys.card + 1)).toReal ≤ rate t) :
    OnlineIndistinguishable.{v, w} (compressedVCOracle k X Y) ME code
      (fun t wVC _ _ ↦ min 1 ((∑ j ∈ Finset.range t, ENNReal.ofReal (rate j)) * wVC)) := by
  apply VCOracle.onlineIndistinguishable_of_recording_source_bounds
    (compressedVCOracle k X Y) ME code (fun D ↦ ∑ i, (D i).size)
    (compressedVCOracle_U_totalSize_le) compressedVCOracle_initial_totalSize rate hrate
  intro Cell _ _ bot j i
  exact l2_opNorm_compressed_recordingDefect_source_sq_le ME bot i j (rate j) (hrate j)
    (hi j i)
end

end Quantum
