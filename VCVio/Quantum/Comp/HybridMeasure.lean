/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.Quantum.Comp.HybridIndex

/-!
# Leaving a subspace: ePrint 2025/2166, Cor 5.8

ePrint 2025/2166, Cor 5.8, bounds the probability that the register `S` of an emulated oracle,
measured after a `q`-query adversary, has left a set `Q` of basis states it started in:
`q · ∑ᵢ ‖[P Uᵢ P, M]‖² · TotalMass(i)`, where `P` is a projector containing every state reached
and `M = Q ⊗ 1_B + (1 - Q) ⊗ X_B` is the purified measurement of `Q` on an extra bit `B`.

This file proves it for general programs (`Quantum.QuantumComp`) run against a runtime whose
steps are the Kraus maps `conj (U i r)`, with countably many outcomes. The proof follows the
paper's extra-bit construction: the runtime extended by a bit `B` that its steps leave alone
(`U ⊗ 1_B`, here the controlled operator `Quantum.Hybrid.ctrl (U i r) (U i r)`) simulates the
runtime from the bit `|0⟩`, and the square-root hybrid with the projector `P ⊗ 1_B` and the
isometry `M` (`Quantum.QuantumRuntime.rpow_inv_two_tsum_trace_conj_run_le_of_inImage'`) is
applied with the run against the extended runtime on both sides. Instead of a last query that
measures, the observable at the leaves is the bit `1` of `B`: it sees nothing in the run itself,
and `M` sends exactly the weight of `S ∉ Q` there.

## Notes on the statement

* **What is bounded is `Pr[S ∉ Q]`.** The paper writes `Pr[S ∈ Q]`, but under its condition 2
  the initial state lies in `Q`, so `Pr[S ∈ Q] = 1` for the adversary making no query; the
  proof in the paper bounds the probability of the bit `1`, which is `Pr[S ∉ Q]`.
* **Condition 3 (`P Q = Q P`) is not needed.** The general square-root hybrid assumes no
  commutation of the projector and the isometry, and the Kraus weights it produces are those of
  the commutator `[P̂ Û P̂, M̂]` as in the paper.
* `Q` is any orthogonal projector of `D`, not only the projector onto a set of basis states, and
  `P` any contraction.

## Main definitions

* `Quantum.Hybrid.bitFlip`: the bit flip `X_B`.
* `Quantum.Hybrid.purifiedMeas Q`: the purified measurement `Q ⊗ 1_B + (1 - Q) ⊗ X_B`.
* `Quantum.Hybrid.measComm P Q U`: the commutators `[P̂ Û P̂, M̂]` of Cor 5.8.

## Main statements

* `Quantum.QuantumRuntime.ForallQueries.of_simulation`: condition 1 under simulation.
* `Quantum.QuantumRuntime.tsum_trace_conj_one_sub_le_of_inImage`: Cor 5.8 with the masses of
  each call, `Pr[S ∉ Q] ≤ (∑ⱼ √(∑ᵢ Cᵢ · mass(i, j)))²`.
* `Quantum.QuantumRuntime.tsum_trace_conj_one_sub_le_of_inImage_of_isQueryBound`: Cor 5.8,
  `Pr[S ∉ Q] ≤ q · ∑ᵢ Cᵢ · TotalMass(i)` for programs within a query budget, with
  `Cᵢ = ∑ᵣ ‖[P̂ Uᵢ,ᵣ P̂, M̂]‖²`.
* `Quantum.QuantumRuntime.tsum_trace_conj_one_sub_le_of_inImage_indexMass` and
  `Quantum.QuantumRuntime.tsum_trace_conj_one_sub_le_of_inImage_indexMass_of_isQueryBound`:
  Cor 5.8 with the masses of a coherent index, as in the paper
  (`VCVio.Quantum.Comp.HybridIndex`), with the constants `∑ᵣ ‖[P̂ Uᵢ,ᵣ P̂, M̂] B̂ᵢ,ₖ‖²`, when the
  operators `U i r` respect the index. The extended runtime respects it too
  (`Quantum.Hybrid.RespectsIndex.ctrl`), and so do the commutators.
-/

public section

open IPFunctor Matrix
open scoped ENNReal ComplexOrder Kronecker

universe u v u₁ v₁ w

namespace Quantum

namespace Hybrid

/-! ## The purified measurement -/

variable {D : Type*} [Fintype D] [DecidableEq D]

/-- The bit flip `X` on `Bool`. -/
@[expose]
def bitFlip : Matrix Bool Bool ℂ :=
  Matrix.of fun b c ↦ if b = !c then 1 else 0

theorem bitFlip_mul_bitFlip : bitFlip * bitFlip = 1 := by
  ext b c
  cases b <;> cases c <;> simp [bitFlip, Matrix.mul_apply]

theorem conjTranspose_bitFlip : bitFlipᴴ = bitFlip := by
  ext b c
  cases b <;> cases c <;> simp [bitFlip]

/-- **The purified measurement** of ePrint 2025/2166, Cor 5.8: `Q ⊗ 1_B + (1 - Q) ⊗ X_B`, which
flips the bit `B` on the complement of `Q`. -/
@[expose]
def purifiedMeas (Q : Matrix D D ℂ) : Matrix (D × Bool) (D × Bool) ℂ :=
  Q ⊗ₖ (1 : Matrix Bool Bool ℂ) + (1 - Q) ⊗ₖ bitFlip

theorem kronecker_one_mul_inj (M : Matrix D D ℂ) (b : Bool) :
    (M ⊗ₖ (1 : Matrix Bool Bool ℂ)) * inj D b = inj D b * M := by
  ext ⟨d, c⟩ d'
  cases b <;> cases c <;> simp [inj, Matrix.mul_apply, Matrix.one_apply]

theorem kronecker_bitFlip_mul_inj (M : Matrix D D ℂ) (b : Bool) :
    (M ⊗ₖ bitFlip) * inj D b = inj D (!b) * M := by
  ext ⟨d, c⟩ d'
  cases b <;> cases c <;> simp [inj, bitFlip, Matrix.mul_apply]

/-- On the bit `0`, the purified measurement is `|0⟩ Q + |1⟩ (1 - Q)`. -/
theorem purifiedMeas_mul_inj_false (Q : Matrix D D ℂ) :
    purifiedMeas Q * inj D false = inj D false * Q + inj D true * (1 - Q) := by
  rw [purifiedMeas, Matrix.add_mul, kronecker_one_mul_inj, kronecker_bitFlip_mul_inj]
  rfl

omit [Fintype D] in
theorem conjTranspose_purifiedMeas {Q : Matrix D D ℂ} (hQ : Qᴴ = Q) :
    (purifiedMeas Q)ᴴ = purifiedMeas Q := by
  simp [purifiedMeas, conjTranspose_kronecker, conjTranspose_bitFlip, hQ]

/-- The purified measurement of an orthogonal projector is unitary. -/
theorem purifiedMeas_isometry {Q : Matrix D D ℂ} (hQ : Qᴴ = Q) (hQQ : Q * Q = Q) :
    (purifiedMeas Q)ᴴ * purifiedMeas Q = 1 := by
  have h₁ : Q * (1 - Q) = 0 := by rw [Matrix.mul_sub, Matrix.mul_one, hQQ, sub_self]
  have h₂ : (1 - Q) * Q = 0 := by rw [Matrix.sub_mul, Matrix.one_mul, hQQ, sub_self]
  have h₃ : (1 - Q) * (1 - Q) = 1 - Q := by rw [Matrix.sub_mul, Matrix.one_mul, h₁, sub_zero]
  rw [conjTranspose_purifiedMeas hQ]
  simp only [purifiedMeas, Matrix.add_mul, Matrix.mul_add, ← mul_kronecker_mul, Matrix.mul_one,
    bitFlip_mul_bitFlip, hQQ, h₁, h₂, h₃, zero_kronecker, add_zero, zero_add]
  rw [← add_kronecker, add_sub_cancel, one_kronecker_one]

/-- The bit `1` after the purified measurement from the bit `0` is the complement of `Q`. -/
theorem conjTranspose_inj_true_mul_purifiedMeas_mul_inj_false {Q : Matrix D D ℂ} (hQ : Qᴴ = Q) :
    (inj D true)ᴴ * (purifiedMeas Q)ᴴ * inj D false = 1 - Q := by
  rw [conjTranspose_purifiedMeas hQ, Matrix.mul_assoc, purifiedMeas_mul_inj_false, Matrix.mul_add,
    ← Matrix.mul_assoc, ← Matrix.mul_assoc, conjTranspose_inj_mul_inj, conjTranspose_inj_mul_inj]
  simp

/-- `P ⊗ 1_B` is a contraction when `P` is. -/
theorem posSemidef_one_sub_kronecker_one {P : Matrix D D ℂ} (hP : (1 - Pᴴ * P).PosSemidef) :
    (1 - (P ⊗ₖ (1 : Matrix Bool Bool ℂ))ᴴ * (P ⊗ₖ (1 : Matrix Bool Bool ℂ))).PosSemidef := by
  have e : 1 - (P ⊗ₖ (1 : Matrix Bool Bool ℂ))ᴴ * (P ⊗ₖ (1 : Matrix Bool Bool ℂ)) =
      (1 - Pᴴ * P) ⊗ₖ (1 : Matrix Bool Bool ℂ) := by
    rw [conjTranspose_kronecker, conjTranspose_one, ← mul_kronecker_mul, Matrix.one_mul]
    ext ⟨a, b⟩ ⟨a', b'⟩
    by_cases ha : a = a' <;> by_cases hb : b = b' <;> simp [ha, hb]
  rw [e]
  exact hP.kronecker Matrix.PosSemidef.one

omit [Fintype D] in
theorem conjTranspose_sel {Y : Type*} [DecidableEq Y] (b : Bool) :
    (sel (D := D) Y b)ᴴ = (1 : Matrix Y Y ℂ) ⊗ₖ inj D b := by
  rw [sel, conjTranspose_kronecker, conjTranspose_one, conjTranspose_conjTranspose]

theorem ctrl_mul_conjTranspose_sel_false {O J : Type*} [Fintype O] [DecidableEq O] [Fintype J]
    [DecidableEq J] (K : Matrix (O × D) (J × D) ℂ) :
    ctrl K K * (sel J false)ᴴ = (sel O false)ᴴ * K := by
  simp only [ctrl, Matrix.add_mul, Matrix.mul_assoc, sel_mul_conjTranspose_sel]
  simp

/-- Lifting by `|0⟩` on the bit `B` commutes with the condition of lying in the image of `P`. -/
theorem conj_lift_eq_of_conj_eq {J E : Type*} [Fintype J] [DecidableEq J] [Fintype E]
    [DecidableEq E] {P : Matrix D D ℂ} {τ : Matrix ((J × D) × E) ((J × D) × E) ℂ}
    (h : MatrixMap.conj (((1 : Matrix J J ℂ) ⊗ₖ P) ⊗ₖ (1 : Matrix E E ℂ)) τ = τ) :
    MatrixMap.conj (((1 : Matrix J J ℂ) ⊗ₖ (P ⊗ₖ (1 : Matrix Bool Bool ℂ))) ⊗ₖ
        (1 : Matrix E E ℂ))
      (MatrixMap.conj (((1 : Matrix J J ℂ) ⊗ₖ inj D false) ⊗ₖ (1 : Matrix E E ℂ)) τ) =
      MatrixMap.conj (((1 : Matrix J J ℂ) ⊗ₖ inj D false) ⊗ₖ (1 : Matrix E E ℂ)) τ := by
  have e : (((1 : Matrix J J ℂ) ⊗ₖ (P ⊗ₖ (1 : Matrix Bool Bool ℂ))) ⊗ₖ (1 : Matrix E E ℂ)) *
      (((1 : Matrix J J ℂ) ⊗ₖ inj D false) ⊗ₖ (1 : Matrix E E ℂ)) =
      (((1 : Matrix J J ℂ) ⊗ₖ inj D false) ⊗ₖ (1 : Matrix E E ℂ)) *
        (((1 : Matrix J J ℂ) ⊗ₖ P) ⊗ₖ (1 : Matrix E E ℂ)) := by
    simp only [← mul_kronecker_mul, Matrix.one_mul, kronecker_one_mul_inj]
  rw [← LinearMap.comp_apply (MatrixMap.conj _), ← MatrixMap.conj_mul, e, MatrixMap.conj_mul,
    LinearMap.comp_apply, h]

variable {spec : QuantumOracleSpec.{u₁, v₁}}

/-- **The commutators of ePrint 2025/2166, Cor 5.8**, `[P̂ Û P̂, M̂]`, on the input or output, the
register `D` and the bit `B`: `Û = U ⊗ 1_B` is `ctrl U U`, `P̂ = 1 ⊗ (P ⊗ 1_B)` and
`M̂ = 1 ⊗ purifiedMeas Q`. -/
@[expose]
def measComm (P Q : Matrix D D ℂ)
    (U : ∀ i, spec.Result i → Matrix (spec.Out i × D) (spec.In i × D) ℂ) (i : spec.Port)
    (r : spec.Result i) : Matrix (spec.Out i × (D × Bool)) (spec.In i × (D × Bool)) ℂ :=
  ((1 : Matrix (spec.Out i) (spec.Out i) ℂ) ⊗ₖ (P ⊗ₖ (1 : Matrix Bool Bool ℂ))) *
      ctrl (U i r) (U i r) *
      ((1 : Matrix (spec.In i) (spec.In i) ℂ) ⊗ₖ (P ⊗ₖ (1 : Matrix Bool Bool ℂ))) *
      ((1 : Matrix (spec.In i) (spec.In i) ℂ) ⊗ₖ purifiedMeas Q) -
    ((1 : Matrix (spec.Out i) (spec.Out i) ℂ) ⊗ₖ purifiedMeas Q) *
      (((1 : Matrix (spec.Out i) (spec.Out i) ℂ) ⊗ₖ (P ⊗ₖ (1 : Matrix Bool Bool ℂ))) *
        ctrl (U i r) (U i r) *
        ((1 : Matrix (spec.In i) (spec.In i) ℂ) ⊗ₖ (P ⊗ₖ (1 : Matrix Bool Bool ℂ))))

/-- The steps extended by a bit, `U ⊗ 1_B` (here `ctrl U U`), respect a coherent index when the
steps `U` do. -/
theorem RespectsIndex.ctrl {κ : spec.Port → Type*} {B : ∀ i, κ i → Matrix (spec.In i) (spec.In i) ℂ}
    {B' : ∀ i, κ i → Matrix (spec.Out i) (spec.Out i) ℂ}
    {U : ∀ i, spec.Result i → Matrix (spec.Out i × D) (spec.In i × D) ℂ}
    (hU : RespectsIndex B B' U) :
    RespectsIndex B B' (D := D × Bool) fun i r ↦ ctrl (U i r) (U i r) := fun i r k ↦ by
  have h : ∀ b, (B' i k ⊗ₖ (1 : Matrix (D × Bool) (D × Bool) ℂ)) *
      ((sel (D := D) (spec.Out i) b)ᴴ * U i r * sel (D := D) (spec.In i) b) *
        (B i k ⊗ₖ (1 : Matrix (D × Bool) (D × Bool) ℂ)) =
      (sel (D := D) (spec.Out i) b)ᴴ * U i r * sel (D := D) (spec.In i) b *
        (B i k ⊗ₖ (1 : Matrix (D × Bool) (D × Bool) ℂ)) := fun b ↦
    mul_mul_eq_of_comm_right
      (by rw [sel]; exact (kronecker_one_mul_one_kronecker (B i k) (inj D b)ᴴ).symm)
      (mul_mul_eq_of_comm_left
        (by rw [conjTranspose_sel]; exact kronecker_one_mul_one_kronecker (B' i k) (inj D b))
        (hU i r k))
  simp only [Hybrid.ctrl, Matrix.mul_add, Matrix.add_mul, h]

end Hybrid

/-! ## Condition 1 under simulation -/

namespace QuantumRuntime

open Hybrid

variable {spec : QuantumOracleSpec.{u₁, v₁}} {L : LocalSig.{u, v}} (I : L.Interp)
  {X : QReg → Type w} {A : QReg}

/-- **Condition 1 under simulation.** If `R₂` simulates `R₁` through `id ⊗ V`, and `P₁` of an
operator presented to a call gives `P₂` of its image under `id ⊗ V`, then every call of the run
against `R₂` from `id ⊗ V` of `ρ` receives an operator satisfying `P₂` when every call of the run
against `R₁` from `ρ` receives one satisfying `P₁`. -/
theorem ForallQueries.of_simulation {R₁ R₂ : QuantumRuntime spec} {V : MatrixMap R₁.D R₂.D}
    (h : ∀ i r, (R₂.step i).branch r ∘ₗ V.amplifyLeft (spec.In i) =
      V.amplifyLeft (spec.Out i) ∘ₗ (R₁.step i).branch r)
    {P₁ : ∀ (i : spec.Port) (E : QReg),
      Matrix ((spec.In i × R₁.D) × E) ((spec.In i × R₁.D) × E) ℂ → Prop}
    {P₂ : ∀ (i : spec.Port) (E : QReg),
      Matrix ((spec.In i × R₂.D) × E) ((spec.In i × R₂.D) × E) ℂ → Prop}
    (hP : ∀ i E τ, P₁ i E τ → P₂ i E ((V.amplifyLeft (spec.In i)).amplify E τ))
    {x : QuantumComp L spec X A} {ρ : Matrix (A × R₁.D) (A × R₁.D) ℂ}
    (hx : R₁.ForallQueries I P₁ x ρ) : R₂.ForallQueries I P₂ x (V.amplifyLeft A ρ) := by
  induction x using QuantumComp.inductionOn with
  | pure _ _ => trivial
  | primBind B o k ih =>
    intro b
    have e : ((I o).frame R₂.D).branch b (V.amplifyLeft B ρ) =
        V.amplifyLeft _ (((I o).frame R₁.D).branch b ρ) :=
      LinearMap.congr_fun (MatrixMap.amplify_comp_amplifyLeft ((I o).branch b) V) ρ
    rw [e]
    exact ih b (hx b)
  | queryBind B i E ℓ k ih =>
    refine ⟨?_, fun r ↦ ?_⟩
    · have e : (SubInstrument.relabel (queryEquivIn ℓ R₂.D)).branch () (V.amplifyLeft B ρ) =
          (V.amplifyLeft (spec.In i)).amplify E
            ((SubInstrument.relabel (queryEquivIn ℓ R₁.D)).branch () ρ) :=
        LinearMap.congr_fun (intertwines_relabel_queryEquivIn V ℓ ()) ρ
      rw [e]
      exact hP i E _ hx.1
    · have e : (R₂.queryStep i E ℓ).branch r (V.amplifyLeft B ρ) =
          V.amplifyLeft _ ((R₁.queryStep i E ℓ).branch r ρ) :=
        LinearMap.congr_fun (intertwines_queryStep (fun r ↦ h i r) E ℓ r) ρ
      rw [e]
      exact ih r (hx.2 r)

/-! ## The runtime extended by a bit -/

section Extended

variable {D : QReg} {σ : SubState D}
  {s : ∀ i, SubInstrument (spec.In i × D) (spec.Out i × D) (spec.Result i)}
  {U : ∀ i, spec.Result i → Matrix (spec.Out i × D) (spec.In i × D) ℂ}
  (hU : ∀ i r, (s i).branch r = MatrixMap.conj (U i r))
include hU

omit hU in
/-- The zero substate, the initial state of the extended runtime in the proofs: it is never
used, since the extended runtime is run from a given joint operator. -/
private noncomputable def zeroInit (B : QReg) : SubState B :=
  ⟨0, Matrix.PosSemidef.zero, by simp⟩

/-- The steps extended by a bit `B` that they leave alone, `U ⊗ 1_B`. -/
private noncomputable def extSteps :
    ∀ i, SubInstrument (spec.In i × QReg.of (D × Bool)) (spec.Out i × QReg.of (D × Bool))
      (spec.Result i) := fun i ↦
  ctrlStep (U i) (U i) ((s i).posSemidef_one_sub_sum_of_branch_eq_conj (hU i))
    ((s i).posSemidef_one_sub_sum_of_branch_eq_conj (hU i))

/-- The extended runtime simulates the runtime from the bit `0`. -/
private theorem extSteps_simulation (i : spec.Port) (r : spec.Result i) :
    (extSteps hU i).branch r ∘ₗ (MatrixMap.conj (inj D false)).amplifyLeft (spec.In i) =
      (MatrixMap.conj (inj D false)).amplifyLeft (spec.Out i) ∘ₗ (s i).branch r := by
  change MatrixMap.conj (ctrl (U i r) (U i r)) ∘ₗ _ = _
  rw [hU, MatrixMap.amplifyLeft_conj, MatrixMap.amplifyLeft_conj, ← MatrixMap.conj_mul,
    ← MatrixMap.conj_mul, ← conjTranspose_sel, ← conjTranspose_sel]
  exact congrArg _ (ctrl_mul_conjTranspose_sel_false (U i r))

omit hU in
private theorem trace_amplifyLeft_conj_inj {J : Type*} [Fintype J]
    (τ : Matrix (J × D) (J × D) ℂ) :
    ((MatrixMap.conj (inj D false)).amplifyLeft J τ).trace = τ.trace := by
  classical
  have h : (inj D false)ᴴ * inj D false = 1 := by
    simpa using conjTranspose_inj_mul_inj (D := D) false false
  rw [MatrixMap.amplifyLeft_conj, trace_conj_of_isometry (one_kronecker_isometry h)]

private theorem queryMassAt_ext (x : QuantumComp L spec X A) (ρ : Matrix (A × D) (A × D) ℂ)
    (i : spec.Port) (j : ℕ) :
    (QuantumRuntime.mk (QReg.of (D × Bool)) (zeroInit _) (extSteps hU)).queryMassAt I x
        ((MatrixMap.conj (inj D false)).amplifyLeft A ρ) i j =
      (QuantumRuntime.mk D σ s).queryMassAt I x ρ i j := by
  simp only [queryMassAt]
  rw [queryWeight_simulation I (R₁ := QuantumRuntime.mk D σ s)
    (R₂ := QuantumRuntime.mk (QReg.of (D × Bool)) (zeroInit _) (extSteps hU))
    (V := MatrixMap.conj (inj D false)) (extSteps_simulation hU)]
  refine congrArg (fun w ↦ (QuantumRuntime.mk D σ s).queryWeight I w x ρ j)
    (funext fun i' ↦ funext fun τ ↦ ?_)
  rw [trace_amplifyLeft_conj_inj]

/-- Condition 1 for the extended runtime and `P ⊗ 1_B`, on a lifted operator. -/
private theorem inImageAt_ext {P : Matrix D D ℂ} {i : spec.Port} {E : QReg}
    {τ : Matrix ((spec.In i × D) × E) ((spec.In i × D) × E) ℂ} (hτ : InImageAt P s i E τ) :
    InImageAt (P ⊗ₖ (1 : Matrix Bool Bool ℂ)) (extSteps hU) i E
      (((MatrixMap.conj (inj D false)).amplifyLeft (spec.In i)).amplify E τ) := by
  refine ⟨?_, fun r ↦ ?_⟩
  · rw [MatrixMap.amplifyLeft_conj, MatrixMap.amplify_conj]
    exact conj_lift_eq_of_conj_eq hτ.1
  · have e : ((extSteps hU i).frame E).branch r
          (((MatrixMap.conj (inj D false)).amplifyLeft (spec.In i)).amplify E τ) =
        ((MatrixMap.conj (inj D false)).amplifyLeft (spec.Out i)).amplify E
          (((s i).frame E).branch r τ) :=
      LinearMap.congr_fun (congrArg (fun Φ ↦ MatrixMap.amplify Φ E)
        (extSteps_simulation hU i r)) τ
    rw [e, MatrixMap.amplifyLeft_conj, MatrixMap.amplify_conj]
    exact conj_lift_eq_of_conj_eq (hτ.2 r)

omit hU in
/-- Condition 2 for the purified measurement: the lifted initial operator is invariant. -/
private theorem conj_purifiedMeas_lift {Q : Matrix D D ℂ} (ρ : SubState A)
    (hQσ : Q * σ.matrix = σ.matrix) :
    MatrixMap.conj ((1 : Matrix A A ℂ) ⊗ₖ purifiedMeas Q)
        ((MatrixMap.conj (inj D false)).amplifyLeft A (ρ.matrix ⊗ₖ σ.matrix)) =
      (MatrixMap.conj (inj D false)).amplifyLeft A (ρ.matrix ⊗ₖ σ.matrix) := by
  have hσH : σ.matrixᴴ = σ.matrix := σ.posSemidef.isHermitian.eq
  set K := inj D false * Q + inj D true * (1 - Q) with hK
  have hKσ : K * σ.matrix = inj D false * σ.matrix := by
    rw [hK, Matrix.add_mul, Matrix.mul_assoc, hQσ, Matrix.mul_assoc, Matrix.sub_mul,
      Matrix.one_mul, hQσ, sub_self, Matrix.mul_zero, add_zero]
  have hm : K * σ.matrix * Kᴴ = inj D false * σ.matrix * (inj D false)ᴴ := by
    calc K * σ.matrix * Kᴴ = inj D false * σ.matrix * Kᴴ := by rw [hKσ]
      _ = inj D false * (K * σ.matrixᴴ)ᴴ := by
        rw [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
      _ = inj D false * (inj D false * σ.matrix)ᴴ := by rw [hσH, hKσ]
      _ = inj D false * σ.matrix * (inj D false)ᴴ := by
        rw [conjTranspose_mul, hσH, Matrix.mul_assoc]
  rw [MatrixMap.amplifyLeft_conj, ← LinearMap.comp_apply (MatrixMap.conj _),
    ← MatrixMap.conj_mul, ← mul_kronecker_mul, Matrix.one_mul, purifiedMeas_mul_inj_false, ← hK]
  simp only [MatrixMap.conj_apply, conjTranspose_kronecker, conjTranspose_one,
    ← mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one, hm]

omit hU in
private theorem posSemidef_one_sub_sel_true (p : Σ u, X u) :
    (1 - (sel p.1 true : Matrix (p.1 × D) (p.1 × (D × Bool)) ℂ)ᴴ *
      (sel p.1 true : Matrix (p.1 × D) (p.1 × (D × Bool)) ℂ)).PosSemidef := by
  rw [← conjTranspose_sel_mul_sel_add (D := D) (Y := p.1), add_sub_cancel_right]
  exact Matrix.posSemidef_conjTranspose_mul_self _

omit hU in
private theorem conj_sel_true_lift (p : Σ u, X u) (τ : Matrix (p.1 × D) (p.1 × D) ℂ) :
    MatrixMap.conj (sel (D := D) p.1 true)
      ((MatrixMap.conj (inj D false)).amplifyLeft p.1 τ) = 0 := by
  rw [MatrixMap.amplifyLeft_conj, ← LinearMap.comp_apply (MatrixMap.conj _),
    ← MatrixMap.conj_mul, sel, ← mul_kronecker_mul, conjTranspose_inj_mul_inj]
  simp

omit hU in
private theorem conj_sel_true_purifiedMeas_lift {Q : Matrix D D ℂ} (hQ : Qᴴ = Q)
    (p : Σ u, X u) (τ : Matrix (p.1 × D) (p.1 × D) ℂ) :
    MatrixMap.conj (sel (D := D) p.1 true * ((1 : Matrix p.1 p.1 ℂ) ⊗ₖ (purifiedMeas Q)ᴴ))
      ((MatrixMap.conj (inj D false)).amplifyLeft p.1 τ) =
      MatrixMap.conj ((1 : Matrix p.1 p.1 ℂ) ⊗ₖ (1 - Q)) τ := by
  rw [MatrixMap.amplifyLeft_conj, ← LinearMap.comp_apply (MatrixMap.conj _),
    ← MatrixMap.conj_mul, sel]
  simp only [← mul_kronecker_mul, Matrix.one_mul,
    conjTranspose_inj_true_mul_purifiedMeas_mul_inj_false hQ]

open scoped Matrix.Norms.L2Operator

omit hU in
private theorem lemmaKraus_ext_eq_neg (P Q : Matrix D D ℂ) (i : spec.Port) (r : spec.Result i) :
    lemmaKraus (D := QReg.of (D × Bool)) (P ⊗ₖ (1 : Matrix Bool Bool ℂ)) (purifiedMeas Q)
        (fun i r ↦ ctrl (U i r) (U i r)) (fun i r ↦ ctrl (U i r) (U i r)) i r =
      -measComm P Q U i r :=
  (neg_sub _ _).symm

omit hU in
private theorem l2_opNorm_lemmaKraus_ext (P Q : Matrix D D ℂ) (i : spec.Port)
    (r : spec.Result i) :
    ‖lemmaKraus (D := QReg.of (D × Bool)) (P ⊗ₖ (1 : Matrix Bool Bool ℂ)) (purifiedMeas Q)
        (fun i r ↦ ctrl (U i r) (U i r)) (fun i r ↦ ctrl (U i r) (U i r)) i r‖ =
      ‖measComm P Q U i r‖ := by
  rw [lemmaKraus_ext_eq_neg, norm_neg]

omit hU in
private theorem C_eq (P Q : Matrix D D ℂ) (i : spec.Port) (c : ℝ≥0∞) :
    (∑' r, ENNReal.ofReal (‖lemmaKraus (D := QReg.of (D × Bool))
        (P ⊗ₖ (1 : Matrix Bool Bool ℂ)) (purifiedMeas Q) (fun i r ↦ ctrl (U i r) (U i r))
        (fun i r ↦ ctrl (U i r) (U i r)) i r‖ ^ 2)) * c =
      (∑' r, ENNReal.ofReal (‖measComm P Q U i r‖ ^ 2)) * c :=
  congrArg (· * c) (tsum_congr fun r ↦
    congrArg (fun t ↦ ENNReal.ofReal (t ^ 2)) (l2_opNorm_lemmaKraus_ext P Q i r))

/-- The core of Cor 5.8: the square root of `Pr[S ∉ Q]` is at most the sum over the calls of the
square roots of the Kraus weights of the commutators on the inputs of the calls of the run
against the extended runtime. -/
private theorem rpow_inv_two_tsum_trace_conj_one_sub_le (x : QuantumComp L spec X A)
    (ρ : SubState A) {P Q : Matrix D D ℂ} (hP : (1 - Pᴴ * P).PosSemidef) (hQ : Qᴴ = Q)
    (hQQ : Q * Q = Q) (hQσ : Q * σ.matrix = σ.matrix)
    (h : (QuantumRuntime.mk D σ s).ForallQueries I (InImageAt P s) x (ρ.matrix ⊗ₖ σ.matrix)) :
    (∑' p, ENNReal.ofReal (MatrixMap.conj ((1 : Matrix p.1 p.1 ℂ) ⊗ₖ (1 - Q))
        ((QuantumRuntime.mk D σ s).jointPost I x ρ p).matrix).trace.re) ^ (2⁻¹ : ℝ) ≤
      ∑' j, (QuantumRuntime.mk (QReg.of (D × Bool)) (zeroInit _) (extSteps hU)).queryWeight I
        (krausWeight (lemmaKraus (D := QReg.of (D × Bool)) (P ⊗ₖ (1 : Matrix Bool Bool ℂ))
          (purifiedMeas Q) (fun i r ↦ ctrl (U i r) (U i r)) (fun i r ↦ ctrl (U i r) (U i r))))
        x ((MatrixMap.conj (inj D false)).amplifyLeft A (ρ.matrix ⊗ₖ σ.matrix)) j ^
          (2⁻¹ : ℝ) := by
  have hΓ : ((MatrixMap.conj (inj D false)).amplifyLeft A (ρ.matrix ⊗ₖ σ.matrix)).PosSemidef := by
    rw [MatrixMap.amplifyLeft_conj]
    exact (ρ.prod σ).posSemidef.mul_mul_conjTranspose_same _
  have h' := ForallQueries.of_simulation I (R₁ := QuantumRuntime.mk D σ s)
    (R₂ := QuantumRuntime.mk (QReg.of (D × Bool)) (zeroInit _) (extSteps hU))
    (V := MatrixMap.conj (inj D false)) (extSteps_simulation hU)
    (P₂ := InImageAt (P ⊗ₖ (1 : Matrix Bool Bool ℂ)) (extSteps hU))
    (fun _ _ _ hτ ↦ inImageAt_ext hU hτ) h
  have key := rpow_inv_two_tsum_trace_conj_run_le_of_inImage' I
    (σ₀ := zeroInit _) (σ₁ := zeroInit _) (s₀ := extSteps hU) (s₁ := extSteps hU)
    (U := fun i r ↦ ctrl (U i r) (U i r)) (W := fun i r ↦ ctrl (U i r) (U i r))
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (posSemidef_one_sub_kronecker_one hP)
    (purifiedMeas_isometry hQ hQQ) x (Z := fun p ↦ p.1 × D) (fun p ↦ sel p.1 true)
    posSemidef_one_sub_sel_true hΓ (conj_purifiedMeas_lift ρ hQσ) h' h'
  have hbr : ∀ p, ((QuantumRuntime.mk (QReg.of (D × Bool)) (zeroInit _) (extSteps hU)).run I
      x).branch p ((MatrixMap.conj (inj D false)).amplifyLeft A (ρ.matrix ⊗ₖ σ.matrix)) =
      (MatrixMap.conj (inj D false)).amplifyLeft p.1
        (((QuantumRuntime.mk D σ s).run I x).branch p (ρ.matrix ⊗ₖ σ.matrix)) := fun p ↦
    LinearMap.congr_fun (simulation I (R₁ := QuantumRuntime.mk D σ s)
      (R₂ := QuantumRuntime.mk (QReg.of (D × Bool)) (zeroInit _) (extSteps hU))
      (V := MatrixMap.conj (inj D false)) (extSteps_simulation hU) x p) _
  simp only [hbr, conj_sel_true_lift, conj_sel_true_purifiedMeas_lift hQ, Matrix.trace_zero,
    Complex.zero_re, ENNReal.ofReal_zero, tsum_zero,
    ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 2⁻¹), zero_add] at key
  simpa only [matrix_jointPost] using key

/-- The Kraus weight of the commutators at the `j`-th call of the run against the extended
runtime is at most the masses of the `j`-th call of the run against the runtime. -/
private theorem queryWeight_ext_le (x : QuantumComp L spec X A) (ρ : SubState A)
    (P Q : Matrix D D ℂ) (j : ℕ) :
    (QuantumRuntime.mk (QReg.of (D × Bool)) (zeroInit _) (extSteps hU)).queryWeight I
        (krausWeight (lemmaKraus (D := QReg.of (D × Bool)) (P ⊗ₖ (1 : Matrix Bool Bool ℂ))
          (purifiedMeas Q) (fun i r ↦ ctrl (U i r) (U i r)) (fun i r ↦ ctrl (U i r) (U i r))))
        x ((MatrixMap.conj (inj D false)).amplifyLeft A (ρ.matrix ⊗ₖ σ.matrix)) j ≤
      ∑' i, (∑' r, ENNReal.ofReal (‖measComm P Q U i r‖ ^ 2)) *
        (QuantumRuntime.mk D σ s).queryMassAt I x (ρ.matrix ⊗ₖ σ.matrix) i j := by
  have hΓ : (((MatrixMap.conj (inj D false)).amplifyLeft A (ρ.matrix ⊗ₖ σ.matrix) :
      Matrix (A × (QuantumRuntime.mk (QReg.of (D × Bool)) (zeroInit _) (extSteps hU)).D)
        (A × (QuantumRuntime.mk (QReg.of (D × Bool)) (zeroInit _) (extSteps hU)).D) ℂ)).PosSemidef
      := by
    convert (ρ.prod σ).posSemidef.mul_mul_conjTranspose_same ((1 : Matrix A A ℂ) ⊗ₖ inj D false)
      using 1
    exact LinearMap.congr_fun (MatrixMap.amplifyLeft_conj _) _
  refine (queryWeight_le_tsum_mul_queryMassAt
    (QuantumRuntime.mk (QReg.of (D × Bool)) (zeroInit _) (extSteps hU)) I
    (fun i ↦ ∑' r, ENNReal.ofReal (‖measComm P Q U i r‖ ^ 2))
    (fun i _ hτ ↦ (krausWeight_le _ i hτ).trans_eq (C_eq P Q i _)) x hΓ j).trans_eq ?_
  exact tsum_congr fun i ↦ congrArg (_ * ·) (queryMassAt_ext (σ := σ) I hU x _ i j)

/-- The total Kraus weight of the commutators over the run against the extended runtime is at
most the total masses of the run against the runtime. -/
private theorem tsum_queryWeight_ext_le (x : QuantumComp L spec X A) (ρ : SubState A)
    (P Q : Matrix D D ℂ) :
    ∑' j, (QuantumRuntime.mk (QReg.of (D × Bool)) (zeroInit _) (extSteps hU)).queryWeight I
        (krausWeight (lemmaKraus (D := QReg.of (D × Bool)) (P ⊗ₖ (1 : Matrix Bool Bool ℂ))
          (purifiedMeas Q) (fun i r ↦ ctrl (U i r) (U i r)) (fun i r ↦ ctrl (U i r) (U i r))))
        x ((MatrixMap.conj (inj D false)).amplifyLeft A (ρ.matrix ⊗ₖ σ.matrix)) j ≤
      ∑' i, (∑' r, ENNReal.ofReal (‖measComm P Q U i r‖ ^ 2)) *
        (QuantumRuntime.mk D σ s).queryMass I x (ρ.matrix ⊗ₖ σ.matrix) i := by
  refine (ENNReal.tsum_le_tsum fun j ↦ queryWeight_ext_le I hU x ρ P Q j).trans_eq ?_
  rw [ENNReal.tsum_comm]
  simp only [queryMass, ENNReal.tsum_mul_left]

/-- **ePrint 2025/2166, Cor 5.8, with the masses of each call**, for general programs. Let the
steps of a runtime with initial state `σ` be the Kraus maps of `U i r`, let `P` be a contraction
and `Q` an orthogonal projector of the register `D`, with `σ` in the image of `Q` (condition 2),
and let the operator presented to every call of the run from `ρ ⊗ σ`, and every output of the
step on it, be fixed by `1 ⊗ P` (condition 1). Then the probability that `D`, measured by `Q`
at the end, has left `Q` is at most `(∑ⱼ √(∑ᵢ Cᵢ · mass(i, j)))²`, with
`Cᵢ = ∑ᵣ ‖[P̂ Uᵢ,ᵣ P̂, M̂]‖²` for the purified measurement `M` of `Q` and the masses of the ports.
The masses of a coherent index, as in §4.2, are in
`Quantum.QuantumRuntime.tsum_trace_conj_one_sub_le_of_inImage_indexMass`.

No commutation of `P` and `Q` is assumed (condition 3 of the paper), and the paper's
`Pr[S ∈ Q]` is read as `Pr[S ∉ Q]`, which is what its proof bounds. -/
theorem tsum_trace_conj_one_sub_le_of_inImage (x : QuantumComp L spec X A) (ρ : SubState A)
    {P Q : Matrix D D ℂ} (hP : (1 - Pᴴ * P).PosSemidef) (hQ : Qᴴ = Q) (hQQ : Q * Q = Q)
    (hQσ : Q * σ.matrix = σ.matrix)
    (h : (QuantumRuntime.mk D σ s).ForallQueries I (InImageAt P s) x (ρ.matrix ⊗ₖ σ.matrix)) :
    ∑' p, ENNReal.ofReal (MatrixMap.conj ((1 : Matrix p.1 p.1 ℂ) ⊗ₖ (1 - Q))
        ((QuantumRuntime.mk D σ s).jointPost I x ρ p).matrix).trace.re ≤
      (∑' j, (∑' i, (∑' r, ENNReal.ofReal (‖measComm P Q U i r‖ ^ 2)) *
        (QuantumRuntime.mk D σ s).queryMassAt I x (ρ.matrix ⊗ₖ σ.matrix) i j) ^ (2⁻¹ : ℝ)) ^
          2 := by
  have hw := (rpow_inv_two_tsum_trace_conj_one_sub_le I hU x ρ hP hQ hQQ hQσ h).trans <|
    ENNReal.tsum_le_tsum fun j ↦
      ENNReal.rpow_le_rpow (queryWeight_ext_le I hU x ρ P Q j) (by norm_num)
  rw [← ENNReal.rpow_two]
  calc _ = ((∑' p, ENNReal.ofReal (MatrixMap.conj ((1 : Matrix p.1 p.1 ℂ) ⊗ₖ (1 - Q))
        ((QuantumRuntime.mk D σ s).jointPost I x ρ p).matrix).trace.re) ^ (2⁻¹ : ℝ)) ^
          (2 : ℝ) := (rpow_inv_two_rpow_two _).symm
    _ ≤ _ := ENNReal.rpow_le_rpow hw (by norm_num)

/-- **ePrint 2025/2166, Cor 5.8**, for general programs within a query budget: under the
hypotheses of `Quantum.QuantumRuntime.tsum_trace_conj_one_sub_le_of_inImage`, with at most
`q = ∑ i ∈ t, b i` calls, the probability that `D` has left `Q` is at most
`q · ∑ᵢ (∑ᵣ ‖[P̂ Uᵢ,ᵣ P̂, M̂]‖²) · TotalMass(i)`, by Cauchy–Schwarz over the calls. -/
theorem tsum_trace_conj_one_sub_le_of_inImage_of_isQueryBound {x : QuantumComp L spec X A}
    {b : spec.Port → ℕ} (hx : x.IsQueryBound b) (t : Finset spec.Port) (ht : ∀ i ∉ t, b i = 0)
    (ρ : SubState A) {P Q : Matrix D D ℂ} (hP : (1 - Pᴴ * P).PosSemidef) (hQ : Qᴴ = Q)
    (hQQ : Q * Q = Q) (hQσ : Q * σ.matrix = σ.matrix)
    (h : (QuantumRuntime.mk D σ s).ForallQueries I (InImageAt P s) x (ρ.matrix ⊗ₖ σ.matrix)) :
    ∑' p, ENNReal.ofReal (MatrixMap.conj ((1 : Matrix p.1 p.1 ℂ) ⊗ₖ (1 - Q))
        ((QuantumRuntime.mk D σ s).jointPost I x ρ p).matrix).trace.re ≤
      ((∑ i ∈ t, b i : ℕ) : ℝ≥0∞) * ∑' i, (∑' r, ENNReal.ofReal (‖measComm P Q U i r‖ ^ 2)) *
        (QuantumRuntime.mk D σ s).queryMass I x (ρ.matrix ⊗ₖ σ.matrix) i := by
  refine (ENNReal.rpow_le_rpow_iff (by norm_num : (0 : ℝ) < 2⁻¹)).mp ?_
  refine (rpow_inv_two_tsum_trace_conj_one_sub_le I hU x ρ hP hQ hQQ hQσ h).trans
    ((tsum_rpow_inv_two_queryWeight_le_of_isQueryBound I _ hx t ht _).trans ?_)
  gcongr
  exact tsum_queryWeight_ext_le I hU x ρ P Q

/-! ### Cor 5.8 with the masses of a coherent index -/

omit hU in
private theorem trace_conj_kronecker_one_amplifyLeft {J : Type*} [Fintype J]
    (M : Matrix J J ℂ) (τ : Matrix (J × D) (J × D) ℂ) :
    (MatrixMap.conj (M ⊗ₖ (1 : Matrix (QReg.of (D × Bool)) (QReg.of (D × Bool)) ℂ))
        ((MatrixMap.conj (inj D false)).amplifyLeft J τ)).trace =
      (MatrixMap.conj (M ⊗ₖ (1 : Matrix D D ℂ)) τ).trace := by
  classical
  have h : (inj D false)ᴴ * inj D false = 1 := by
    simpa using conjTranspose_inj_mul_inj (D := D) false false
  rw [MatrixMap.amplifyLeft_conj, ← LinearMap.comp_apply (MatrixMap.conj _),
    ← MatrixMap.conj_mul, kronecker_one_mul_one_kronecker, MatrixMap.conj_mul,
    LinearMap.comp_apply, trace_conj_of_isometry (one_kronecker_isometry h)]

private theorem indexMassAt_ext {κ : spec.Port → Type*}
    (B : ∀ i, κ i → Matrix (spec.In i) (spec.In i) ℂ) (x : QuantumComp L spec X A)
    (ρ : Matrix (A × D) (A × D) ℂ) (c : Σ i, κ i) (j : ℕ) :
    (QuantumRuntime.mk (QReg.of (D × Bool)) (zeroInit _) (extSteps hU)).indexMassAt I B x
        ((MatrixMap.conj (inj D false)).amplifyLeft A ρ) c j =
      (QuantumRuntime.mk D σ s).indexMassAt I B x ρ c j := by
  simp only [indexMassAt]
  rw [queryWeight_simulation I (R₁ := QuantumRuntime.mk D σ s)
    (R₂ := QuantumRuntime.mk (QReg.of (D × Bool)) (zeroInit _) (extSteps hU))
    (V := MatrixMap.conj (inj D false)) (extSteps_simulation hU)]
  refine congrArg (fun w ↦ (QuantumRuntime.mk D σ s).queryWeight I w x ρ j)
    (funext fun i' ↦ funext fun τ ↦ tsum_congr fun k ↦ ?_)
  split_ifs
  · rw [trace_conj_kronecker_one_amplifyLeft]
  · rfl

omit hU in
private theorem respectsIndex_lemmaKraus_ext {κ : spec.Port → Type*}
    {B : ∀ i, κ i → Matrix (spec.In i) (spec.In i) ℂ}
    {B' : ∀ i, κ i → Matrix (spec.Out i) (spec.Out i) ℂ} (hUB : RespectsIndex B B' U)
    (P Q : Matrix D D ℂ) :
    RespectsIndex B B' (lemmaKraus (D := QReg.of (D × Bool)) (P ⊗ₖ (1 : Matrix Bool Bool ℂ))
      (purifiedMeas Q) (fun i r ↦ ctrl (U i r) (U i r)) (fun i r ↦ ctrl (U i r) (U i r))) :=
  RespectsIndex.lemmaKraus hUB.ctrl hUB.ctrl _ _

/-- The Kraus weight of the commutators at the `j`-th call of the run against the extended
runtime is at most the index masses of the `j`-th call of the run against the runtime. -/
private theorem queryWeight_ext_le_indexMassAt {κ : spec.Port → Type*} [∀ i, Fintype (κ i)]
    {B : ∀ i, κ i → Matrix (spec.In i) (spec.In i) ℂ}
    {B' : ∀ i, κ i → Matrix (spec.Out i) (spec.Out i) ℂ} (hB : IsCoherentIndex B B')
    (hUB : RespectsIndex B B' U) (x : QuantumComp L spec X A) (ρ : SubState A)
    (P Q : Matrix D D ℂ) (j : ℕ) :
    (QuantumRuntime.mk (QReg.of (D × Bool)) (zeroInit _) (extSteps hU)).queryWeight I
        (krausWeight (lemmaKraus (D := QReg.of (D × Bool)) (P ⊗ₖ (1 : Matrix Bool Bool ℂ))
          (purifiedMeas Q) (fun i r ↦ ctrl (U i r) (U i r)) (fun i r ↦ ctrl (U i r) (U i r))))
        x ((MatrixMap.conj (inj D false)).amplifyLeft A (ρ.matrix ⊗ₖ σ.matrix)) j ≤
      ∑' c, (∑' r, ENNReal.ofReal (‖measComm P Q U c.1 r *
          (B c.1 c.2 ⊗ₖ (1 : Matrix (D × Bool) (D × Bool) ℂ))‖ ^ 2)) *
        (QuantumRuntime.mk D σ s).indexMassAt I B x (ρ.matrix ⊗ₖ σ.matrix) c j := by
  have hΓ : (((MatrixMap.conj (inj D false)).amplifyLeft A (ρ.matrix ⊗ₖ σ.matrix) :
      Matrix (A × (QuantumRuntime.mk (QReg.of (D × Bool)) (zeroInit _) (extSteps hU)).D)
        (A × (QuantumRuntime.mk (QReg.of (D × Bool)) (zeroInit _) (extSteps hU)).D) ℂ)).PosSemidef
      := by
    convert (ρ.prod σ).posSemidef.mul_mul_conjTranspose_same ((1 : Matrix A A ℂ) ⊗ₖ inj D false)
      using 1
    exact LinearMap.congr_fun (MatrixMap.amplifyLeft_conj _) _
  refine ((QuantumRuntime.mk (QReg.of (D × Bool)) (zeroInit _)
    (extSteps hU)).queryWeight_krausWeight_le_tsum_mul_indexMassAt I hB
    (respectsIndex_lemmaKraus_ext hUB P Q) x hΓ j).trans_eq ?_
  simp only [indexMassAt_ext (σ := σ) I hU]
  refine tsum_congr fun c ↦ congrArg (· * _) (tsum_congr fun r ↦ ?_)
  rw [lemmaKraus_ext_eq_neg, Matrix.neg_mul, norm_neg]

/-- **ePrint 2025/2166, Cor 5.8, with the masses of a coherent index, per call** (§4.1–4.2, for
general programs). Under the hypotheses of
`Quantum.QuantumRuntime.tsum_trace_conj_one_sub_le_of_inImage`, if the steps `U i r` respect a
coherent index `B, B'`, the probability that `D` has left `Q` is at most
`(∑ⱼ √(∑_{i,k} Cᵢ,ₖ · mass(⟨i, k⟩, j)))²`, with `Cᵢ,ₖ = ∑ᵣ ‖[P̂ Uᵢ,ᵣ P̂, M̂] (B i k ⊗ 1)‖²` and
the index masses of the run. For the paper's emulated oracles `B i k` projects the index
register onto `k`, and `Cᵢ,ₖ` is the commutator of the block `k`, `‖[P Uₖ P, M]‖²`. -/
theorem tsum_trace_conj_one_sub_le_of_inImage_indexMass {κ : spec.Port → Type*}
    [∀ i, Fintype (κ i)] {B : ∀ i, κ i → Matrix (spec.In i) (spec.In i) ℂ}
    {B' : ∀ i, κ i → Matrix (spec.Out i) (spec.Out i) ℂ} (hB : IsCoherentIndex B B')
    (hUB : RespectsIndex B B' U) (x : QuantumComp L spec X A) (ρ : SubState A)
    {P Q : Matrix D D ℂ} (hP : (1 - Pᴴ * P).PosSemidef) (hQ : Qᴴ = Q) (hQQ : Q * Q = Q)
    (hQσ : Q * σ.matrix = σ.matrix)
    (h : (QuantumRuntime.mk D σ s).ForallQueries I (InImageAt P s) x (ρ.matrix ⊗ₖ σ.matrix)) :
    ∑' p, ENNReal.ofReal (MatrixMap.conj ((1 : Matrix p.1 p.1 ℂ) ⊗ₖ (1 - Q))
        ((QuantumRuntime.mk D σ s).jointPost I x ρ p).matrix).trace.re ≤
      (∑' j, (∑' c, (∑' r, ENNReal.ofReal (‖measComm P Q U c.1 r *
          (B c.1 c.2 ⊗ₖ (1 : Matrix (D × Bool) (D × Bool) ℂ))‖ ^ 2)) *
        (QuantumRuntime.mk D σ s).indexMassAt I B x (ρ.matrix ⊗ₖ σ.matrix) c j) ^ (2⁻¹ : ℝ)) ^
          2 := by
  have hw := (rpow_inv_two_tsum_trace_conj_one_sub_le I hU x ρ hP hQ hQQ hQσ h).trans <|
    ENNReal.tsum_le_tsum fun j ↦
      ENNReal.rpow_le_rpow (queryWeight_ext_le_indexMassAt I hU hB hUB x ρ P Q j) (by norm_num)
  rw [← ENNReal.rpow_two]
  calc _ = ((∑' p, ENNReal.ofReal (MatrixMap.conj ((1 : Matrix p.1 p.1 ℂ) ⊗ₖ (1 - Q))
        ((QuantumRuntime.mk D σ s).jointPost I x ρ p).matrix).trace.re) ^ (2⁻¹ : ℝ)) ^
          (2 : ℝ) := (rpow_inv_two_rpow_two _).symm
    _ ≤ _ := ENNReal.rpow_le_rpow hw (by norm_num)

/-- **ePrint 2025/2166, Cor 5.8, with the masses of a coherent index**, for general programs
within a query budget: with at most `q = ∑ i ∈ t, b i` calls, the probability that `D` has left
`Q` is at most `q · ∑_{i,k} Cᵢ,ₖ · TotalMass(⟨i, k⟩)`,
`Cᵢ,ₖ = ∑ᵣ ‖[P̂ Uᵢ,ᵣ P̂, M̂] (B i k ⊗ 1)‖²`. -/
theorem tsum_trace_conj_one_sub_le_of_inImage_indexMass_of_isQueryBound {κ : spec.Port → Type*}
    [∀ i, Fintype (κ i)] {B : ∀ i, κ i → Matrix (spec.In i) (spec.In i) ℂ}
    {B' : ∀ i, κ i → Matrix (spec.Out i) (spec.Out i) ℂ} (hB : IsCoherentIndex B B')
    (hUB : RespectsIndex B B' U) {x : QuantumComp L spec X A} {b : spec.Port → ℕ}
    (hx : x.IsQueryBound b) (t : Finset spec.Port) (ht : ∀ i ∉ t, b i = 0) (ρ : SubState A)
    {P Q : Matrix D D ℂ} (hP : (1 - Pᴴ * P).PosSemidef) (hQ : Qᴴ = Q) (hQQ : Q * Q = Q)
    (hQσ : Q * σ.matrix = σ.matrix)
    (h : (QuantumRuntime.mk D σ s).ForallQueries I (InImageAt P s) x (ρ.matrix ⊗ₖ σ.matrix)) :
    ∑' p, ENNReal.ofReal (MatrixMap.conj ((1 : Matrix p.1 p.1 ℂ) ⊗ₖ (1 - Q))
        ((QuantumRuntime.mk D σ s).jointPost I x ρ p).matrix).trace.re ≤
      ((∑ i ∈ t, b i : ℕ) : ℝ≥0∞) * ∑' c, (∑' r, ENNReal.ofReal (‖measComm P Q U c.1 r *
          (B c.1 c.2 ⊗ₖ (1 : Matrix (D × Bool) (D × Bool) ℂ))‖ ^ 2)) *
        (QuantumRuntime.mk D σ s).indexMass I B x (ρ.matrix ⊗ₖ σ.matrix) c := by
  refine (ENNReal.rpow_le_rpow_iff (by norm_num : (0 : ℝ) < 2⁻¹)).mp ?_
  refine (rpow_inv_two_tsum_trace_conj_one_sub_le I hU x ρ hP hQ hQQ hQσ h).trans
    ((tsum_rpow_inv_two_queryWeight_le_of_isQueryBound I _ hx t ht _).trans ?_)
  gcongr
  refine (ENNReal.tsum_le_tsum fun j ↦
    queryWeight_ext_le_indexMassAt I hU hB hUB x ρ P Q j).trans_eq ?_
  rw [ENNReal.tsum_comm]
  simp only [indexMass, ENNReal.tsum_mul_left]

end Extended

end QuantumRuntime

end Quantum
