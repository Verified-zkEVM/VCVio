/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.Quantum.Comp.Hybrid

/-!
# The square-root hybrid bound with a projector and a symmetry

ePrint 2025/2166, Lemma 5.7, compares two emulated oracles through a projector `P` and a unitary
`V` on their internal register. Under its three conditions,

1. every state reached lies in the image of `P`;
2. the initial state is invariant under `V`;
3. `P` commutes with `V`;

the square roots of the probabilities of an event differ by at most
`∑ⱼ √(∑ᵢ ‖P (V Uᵢ V† − Wᵢ) P‖² · mass(i, j))`.

This file proves it for general programs (`Quantum.QuantumComp`) run against two runtimes on the
same register `D` whose steps are Kraus maps, `conj (U i r)` and `conj (W i r)`, with countably
many outcomes. Condition 1 is the hypothesis `ForallQueries (InImageAt P s)` on the run against
each runtime: the operator presented to every call, and every output of the step on it, are
fixed by the Kraus map of `1 ⊗ P` (`Quantum.Hybrid.InImageAt`). Condition 2 is asked of the
initial joint operator. Condition 3 is needed only to put the constants in the form of the paper
(`Quantum.QuantumRuntime.rpow_inv_two_outcomeLawWith_le_of_inImage_mass`, with the masses of the
classical ports; the masses of a coherent index, as in §4.2, are in
`VCVio.Quantum.Comp.HybridIndex`); the general bound
(`Quantum.QuantumRuntime.rpow_inv_two_tsum_trace_conj_run_le_of_inImage`) holds without it, with
the Kraus weights of `(1 ⊗ V) P̂ U P̂ - P̂ W P̂ (1 ⊗ V)`, `P̂ = 1 ⊗ P`. Neither `P` nor `V` needs to
be more than a contraction and an isometry respectively.

## Proof

Under condition 1, the runs are those against the compressed runtimes with steps
`conj (P̂ U P̂)` and `conj (P̂ W P̂)` (`Quantum.QuantumRuntime.run_branch_apply_eq_of_forallQueries`
and `Quantum.QuantumRuntime.queryWeight_eq_of_forallQueries`). Conjugating the first compressed
runtime by `V` gives a runtime simulated through `conj V`, and condition 2 makes the start
invariant (`Quantum.QuantumRuntime.queryWeight_simulation`). The core bound
`Quantum.QuantumRuntime.rpow_inv_two_tsum_trace_conj_run_le` then compares the rotated and the
second compressed runtime.

## Main definitions

* `Quantum.SubInstrument.sandwich`: a subinstrument between two completely positive,
  trace-nonincreasing maps.
* `Quantum.Hybrid.InImageAt P s`: condition 1 at a call.
* `Quantum.Hybrid.compressSteps` and `Quantum.Hybrid.rotateSteps`: the steps compressed by `P`
  and rotated by `V`.
* `Quantum.Hybrid.lemmaKraus P V U W`, the operators `V̂ P̂ U P̂ - P̂ W P̂ V̂` of the general bound,
  and `Quantum.Hybrid.projDiff P V U W`, the operators `P̂ (V̂ U V̂ᴴ - W) P̂` of the paper, with
  the same operator norms under condition 3 (`Quantum.Hybrid.l2_opNorm_lemmaKraus`).

## Main statements

* `Quantum.QuantumRuntime.queryWeight_simulation` and
  `Quantum.QuantumRuntime.queryWeight_eq_of_forallQueries`: query weights under simulation and
  under agreement on the presented operators.
* `Quantum.QuantumRuntime.rpow_inv_two_tsum_trace_conj_run_le_of_inImage` and its converse.
* `Quantum.QuantumRuntime.rpow_inv_two_outcomeLawWith_le_of_inImage` and its converse, for
  events, and `Quantum.QuantumRuntime.rpow_inv_two_outcomeLawWith_le_of_inImage_mass`, ePrint
  2025/2166, Lemma 5.7, with the masses of the classical ports, and
  `Quantum.QuantumRuntime.rpow_inv_two_outcomeLawWith_le_of_inImage_of_isQueryBound` for
  programs within a query budget. Both directions use the Kraus weights, or the masses, of the
  run against the first runtime: the primed forms are the converses.
* `Quantum.QuantumRuntime.max_tsub_rpow_inv_two_outcomeLawWith_le_of_inImage_mass` and
  `Quantum.QuantumRuntime.max_tsub_rpow_inv_two_outcomeLawWith_le_of_inImage_of_isQueryBound`:
  the two-sided statement `|√p₀ - √p₁| ≤ …` of Lemma 5.7, with the masses of one run, and
  `Quantum.QuantumRuntime.max_tsub_rpow_inv_two_outcomeLawWith_sq_le_of_inImage_of_isQueryBound`,
  squared as in the paper.
-/

public section

open IPFunctor Matrix
open scoped ENNReal ComplexOrder Kronecker

universe u v u₁ v₁ w

namespace Quantum

/-! ## Sandwiched subinstruments -/

namespace SubInstrument

variable {A A' B B' : Type*} [Fintype A] [Fintype A'] [Fintype B] [Fintype B'] {α : Type*}

/-- A subinstrument preceded by the completely positive, trace-nonincreasing map `Φ` and
followed by `Ψ`. -/
@[expose]
noncomputable def sandwich (p : SubInstrument A B α) (Φ : MatrixMap A' A) (Ψ : MatrixMap B B')
    (hΦ : Φ.IsCP) (hΦ' : Φ.IsTNI) (hΨ : Ψ.IsCP) (hΨ' : Ψ.IsTNI) : SubInstrument A' B' α where
  branch a := Ψ ∘ₗ p.branch a ∘ₗ Φ
  isCP_branch a := hΨ.comp ((p.isCP_branch a).comp hΦ)
  isTNI_sum s ρ hρ := by
    have hΦρ := hΦ.posSemidef hρ
    rw [MatrixMap.trace_re_sum_apply]
    calc ∑ a ∈ s, ((Ψ ∘ₗ p.branch a ∘ₗ Φ) ρ).trace.re
        ≤ ∑ a ∈ s, (p.branch a (Φ ρ)).trace.re :=
          Finset.sum_le_sum fun a _ ↦ hΨ' _ ((p.isCP_branch a).posSemidef hΦρ)
      _ = ((∑ a ∈ s, p.branch a) (Φ ρ)).trace.re := (MatrixMap.trace_re_sum_apply _ _ _).symm
      _ ≤ (Φ ρ).trace.re := p.isTNI_sum s _ hΦρ
      _ ≤ ρ.trace.re := hΦ' ρ hρ

@[simp]
theorem branch_sandwich (p : SubInstrument A B α) (Φ : MatrixMap A' A) (Ψ : MatrixMap B B')
    (hΦ : Φ.IsCP) (hΦ' : Φ.IsTNI) (hΨ : Ψ.IsCP) (hΨ' : Ψ.IsTNI) (a : α) :
    (p.sandwich Φ Ψ hΦ hΦ' hΨ hΨ').branch a = Ψ ∘ₗ p.branch a ∘ₗ Φ :=
  rfl

end SubInstrument

namespace Hybrid

/-! ## Contractions -/

/-- A product of contractions is a contraction. -/
theorem posSemidef_one_sub_mul {l m n : Type*} [Fintype l] [Fintype m] [Finite n]
    [DecidableEq m] [DecidableEq n] {K : Matrix l m ℂ} {L : Matrix m n ℂ}
    (hK : (1 - Kᴴ * K).PosSemidef) (hL : (1 - Lᴴ * L).PosSemidef) :
    (1 - (K * L)ᴴ * (K * L)).PosSemidef := by
  have h : 1 - (K * L)ᴴ * (K * L) = (1 - Lᴴ * L) + Lᴴ * (1 - Kᴴ * K) * L := by
    simp only [Matrix.conjTranspose_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one,
      Matrix.mul_assoc]
    abel
  rw [h]
  exact hL.add (hK.conjTranspose_mul_mul_same L)

/-- `1 ⊗ X` is a contraction when `X` is. -/
theorem posSemidef_one_sub_one_kronecker {k m n : Type*} [Fintype k] [DecidableEq k] [Fintype m]
    [Finite n] [DecidableEq n] {X : Matrix m n ℂ}
    (h : (1 - Xᴴ * X).PosSemidef) :
    (1 - ((1 : Matrix k k ℂ) ⊗ₖ X)ᴴ * ((1 : Matrix k k ℂ) ⊗ₖ X)).PosSemidef := by
  have e : 1 - ((1 : Matrix k k ℂ) ⊗ₖ X)ᴴ * ((1 : Matrix k k ℂ) ⊗ₖ X) =
      (1 : Matrix k k ℂ) ⊗ₖ (1 - Xᴴ * X) := by
    rw [conjTranspose_kronecker, conjTranspose_one, ← mul_kronecker_mul, Matrix.one_mul]
    ext ⟨a, b⟩ ⟨a', b'⟩
    by_cases ha : a = a' <;> by_cases hb : b = b' <;> simp [ha, hb]
  rw [e]
  exact Matrix.PosSemidef.one.kronecker h

/-- The adjoint of an isometry of a square matrix is a contraction. -/
theorem posSemidef_one_sub_conjTranspose {n : Type*} [Fintype n] [DecidableEq n]
    {V : Matrix n n ℂ} (hV : Vᴴ * V = 1) : (1 - Vᴴᴴ * Vᴴ).PosSemidef := by
  rw [conjTranspose_conjTranspose, _root_.mul_eq_one_comm.mp hV, sub_self]
  exact Matrix.PosSemidef.zero

/-- An isometry is a contraction. -/
theorem posSemidef_one_sub_of_isometry {m n : Type*} [Fintype m] [DecidableEq n]
    {V : Matrix m n ℂ} (hV : Vᴴ * V = 1) : (1 - Vᴴ * V).PosSemidef := by
  rw [hV, sub_self]
  exact Matrix.PosSemidef.zero

/-- The Kraus map of an isometry preserves the trace. -/
theorem trace_conj_of_isometry {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    {K : Matrix m n ℂ}
    (hK : Kᴴ * K = 1) (M : Matrix n n ℂ) : (MatrixMap.conj K M).trace = M.trace :=
  MatrixMap.isTP_conj hK M

/-- `(1 ⊗ V)ᴴ (1 ⊗ V) = 1` for an isometry `V`. -/
theorem one_kronecker_isometry {k m n : Type*} [Fintype k] [DecidableEq k] [Fintype m]
    [DecidableEq n] {V : Matrix m n ℂ} (hV : Vᴴ * V = 1) :
    ((1 : Matrix k k ℂ) ⊗ₖ V)ᴴ * ((1 : Matrix k k ℂ) ⊗ₖ V) = 1 := by
  rw [conjTranspose_kronecker, conjTranspose_one, ← mul_kronecker_mul, Matrix.one_mul, hV,
    one_kronecker_one]

/-- `(1 ⊗ Vᴴ) (1 ⊗ V) = 1` for an isometry `V`. -/
theorem one_kronecker_conjTranspose_mul {k m n : Type*} [Fintype k] [DecidableEq k] [Fintype m]
    [DecidableEq n] {V : Matrix m n ℂ} (hV : Vᴴ * V = 1) :
    ((1 : Matrix k k ℂ) ⊗ₖ Vᴴ) * ((1 : Matrix k k ℂ) ⊗ₖ V) = 1 := by
  rw [← mul_kronecker_mul, Matrix.one_mul, hV, one_kronecker_one]

/-- `(1 ⊗ V) (1 ⊗ Vᴴ) = 1` for a coisometry `V`. -/
theorem one_kronecker_mul_conjTranspose {k m n : Type*} [Fintype k] [DecidableEq k] [Fintype n]
    [DecidableEq m] {V : Matrix m n ℂ} (hV : V * Vᴴ = 1) :
    ((1 : Matrix k k ℂ) ⊗ₖ V) * ((1 : Matrix k k ℂ) ⊗ₖ V)ᴴ = 1 := by
  rw [conjTranspose_kronecker, conjTranspose_one, ← mul_kronecker_mul, Matrix.one_mul, hV,
    one_kronecker_one]

theorem one_kronecker_mul_one_kronecker {k m n l : Type*} [Fintype k] [DecidableEq k]
    [Fintype n] (A : Matrix m n ℂ) (B : Matrix n l ℂ) :
    ((1 : Matrix k k ℂ) ⊗ₖ A) * ((1 : Matrix k k ℂ) ⊗ₖ B) = (1 : Matrix k k ℂ) ⊗ₖ (A * B) := by
  rw [← mul_kronecker_mul, Matrix.one_mul]

theorem one_kronecker_mul_one_kronecker_mul {k m n l j : Type*} [Fintype k] [DecidableEq k]
    [Fintype n] [Fintype l] (A : Matrix m n ℂ) (B : Matrix n l ℂ) (C : Matrix (k × l) j ℂ) :
    ((1 : Matrix k k ℂ) ⊗ₖ A) * (((1 : Matrix k k ℂ) ⊗ₖ B) * C) =
      ((1 : Matrix k k ℂ) ⊗ₖ (A * B)) * C := by
  rw [← Matrix.mul_assoc, one_kronecker_mul_one_kronecker]

/-! ## Kraus-sandwiched steps -/

variable {J O J' O' α : Type*} [Fintype J] [Fintype O] [Fintype J'] [DecidableEq J']
  [Fintype O'] [DecidableEq O]

/-- A step conjugated by the contraction `Ki` before and the contraction `Ko` after. -/
@[expose]
noncomputable def krausSandwich (s : SubInstrument J O α) (Ki : Matrix J J' ℂ)
    (Ko : Matrix O' O ℂ) (hi : (1 - Kiᴴ * Ki).PosSemidef) (ho : (1 - Koᴴ * Ko).PosSemidef) :
    SubInstrument J' O' α :=
  s.sandwich (MatrixMap.conj Ki) (MatrixMap.conj Ko) (MatrixMap.isCP_conj _)
    (MatrixMap.isTNI_conj hi) (MatrixMap.isCP_conj _) (MatrixMap.isTNI_conj ho)

theorem branch_krausSandwich (s : SubInstrument J O α) (Ki : Matrix J J' ℂ) (Ko : Matrix O' O ℂ)
    (hi : (1 - Kiᴴ * Ki).PosSemidef) (ho : (1 - Koᴴ * Ko).PosSemidef) (a : α) :
    (krausSandwich s Ki Ko hi ho).branch a =
      MatrixMap.conj Ko ∘ₗ s.branch a ∘ₗ MatrixMap.conj Ki :=
  rfl

/-- Sandwiching a step with Kraus operators `K a` gives the Kraus operators `Ko * K a * Ki`. -/
theorem branch_krausSandwich_of_eq_conj {s : SubInstrument J O α} {K : α → Matrix O J ℂ}
    (hK : ∀ a, s.branch a = MatrixMap.conj (K a)) (Ki : Matrix J J' ℂ) (Ko : Matrix O' O ℂ)
    (hi : (1 - Kiᴴ * Ki).PosSemidef) (ho : (1 - Koᴴ * Ko).PosSemidef) (a : α) :
    (krausSandwich s Ki Ko hi ho).branch a = MatrixMap.conj (Ko * K a * Ki) := by
  rw [branch_krausSandwich, hK, Matrix.mul_assoc, MatrixMap.conj_mul, MatrixMap.conj_mul]

end Hybrid

/-! ## Query weights under simulation and agreement -/

namespace QuantumRuntime

open Hybrid SubInstrument

variable {spec : QuantumOracleSpec.{u₁, v₁}} {L : LocalSig.{u, v}} (I : L.Interp)
  {X : QReg → Type w} {A : QReg}

/-- The input of a call after `id ⊗ V` on the runtime register is `id ⊗ V` of the input. -/
theorem callInput_amplifyLeft {R S : Type*} [Fintype R] [Fintype S] [DecidableEq R]
    [DecidableEq S] (V : MatrixMap R S) {A J E : Type*} [Fintype A] [Fintype J] [Fintype E]
    [DecidableEq A] [DecidableEq J] [DecidableEq E] (ℓ : A ≃ J × E)
    (ρ : Matrix (A × R) (A × R) ℂ) :
    callInput ℓ S (V.amplifyLeft A ρ) = V.amplifyLeft J (callInput ℓ R ρ) := by
  simp only [callInput, LinearMap.comp_apply]
  rw [← LinearMap.comp_apply ((relabel (queryEquivIn ℓ S)).branch ()),
    intertwines_relabel_queryEquivIn V ℓ (), LinearMap.comp_apply,
    ← LinearMap.comp_apply (MatrixMap.traceRight (J × S) E), MatrixMap.traceRight_comp_amplify,
    LinearMap.comp_apply]

section simulation

variable {R₁ R₂ : QuantumRuntime spec} {V : MatrixMap R₁.D R₂.D}

/-- **Query weights under simulation.** If `R₂` simulates `R₁` through `id ⊗ V`, the weights of
the run against `R₂` from `id ⊗ V` of `ρ` are the weights, composed with `id ⊗ V`, of the run
against `R₁` from `ρ`. -/
theorem queryWeight_simulation
    (h : ∀ i r, (R₂.step i).branch r ∘ₗ V.amplifyLeft (spec.In i) =
      V.amplifyLeft (spec.Out i) ∘ₗ (R₁.step i).branch r)
    (w : ∀ i, Matrix (spec.In i × R₂.D) (spec.In i × R₂.D) ℂ → ℝ≥0∞)
    (x : QuantumComp L spec X A) (ρ : Matrix (A × R₁.D) (A × R₁.D) ℂ) (j : ℕ) :
    R₂.queryWeight I w x (V.amplifyLeft A ρ) j =
      R₁.queryWeight I (fun i σ ↦ w i (V.amplifyLeft (spec.In i) σ)) x ρ j := by
  induction x using QuantumComp.inductionOn generalizing j with
  | pure _ _ => rfl
  | primBind B o k ih =>
    simp only [queryWeight_primBind]
    refine tsum_congr fun b ↦ ?_
    rw [← ih b]
    exact congrArg (fun M ↦ R₂.queryWeight I w (k b) M j)
      (LinearMap.congr_fun (MatrixMap.amplify_comp_amplifyLeft ((I o).branch b) V) ρ)
  | queryBind B i E ℓ k ih =>
    cases j with
    | zero =>
      simp only [queryWeight_queryBind_zero]
      rw [callInput_amplifyLeft]
    | succ j =>
      simp only [queryWeight_queryBind_succ]
      refine tsum_congr fun r ↦ ?_
      rw [← ih r]
      exact congrArg (fun M ↦ R₂.queryWeight I w (k r) M j)
        (LinearMap.congr_fun (intertwines_queryStep (fun r ↦ h i r) E ℓ r) ρ)

end simulation

/-- **Only the presented operators matter**, for query weights: two runtimes on the same
register whose steps agree on every operator satisfying `P` give the same weights on an operator
from which every call of the run against the first runtime receives an operator satisfying
`P`. -/
theorem queryWeight_eq_of_forallQueries {D : QReg} {σ₁ σ₂ : SubState D}
    {s₁ s₂ : ∀ i, SubInstrument (spec.In i × D) (spec.Out i × D) (spec.Result i)}
    {P : ∀ (i : spec.Port) (E : QReg), Matrix ((spec.In i × D) × E) ((spec.In i × D) × E) ℂ → Prop}
    (hs : ∀ i E σ, P i E σ → ∀ r, ((s₁ i).frame E).branch r σ = ((s₂ i).frame E).branch r σ)
    (w : ∀ i, Matrix (spec.In i × D) (spec.In i × D) ℂ → ℝ≥0∞) {x : QuantumComp L spec X A}
    {ρ : Matrix (A × D) (A × D) ℂ} (hx : (QuantumRuntime.mk D σ₁ s₁).ForallQueries I P x ρ)
    (j : ℕ) :
    (QuantumRuntime.mk D σ₁ s₁).queryWeight I w x ρ j =
      (QuantumRuntime.mk D σ₂ s₂).queryWeight I w x ρ j := by
  induction x using QuantumComp.inductionOn generalizing j with
  | pure _ _ => rfl
  | primBind _ o k ih =>
    simp only [queryWeight_primBind]
    exact tsum_congr fun b ↦ ih b (hx b) j
  | queryBind _ i E ℓ k ih =>
    cases j with
    | zero => rfl
    | succ j =>
      simp only [queryWeight_queryBind_succ]
      refine tsum_congr fun r ↦ ?_
      have hq : ((QuantumRuntime.mk D σ₁ s₁).queryStep i E ℓ).branch r ρ =
          ((QuantumRuntime.mk D σ₂ s₂).queryStep i E ℓ).branch r ρ := by
        rw [queryStep_branch_apply, queryStep_branch_apply]
        exact congrArg _ (hs i E _ hx.1 r)
      rw [← hq]
      exact ih r (hx.2 r) j

end QuantumRuntime

/-! ## Condition 1 and the compressed and rotated runtimes -/

namespace Hybrid

variable {spec : QuantumOracleSpec.{u₁, v₁}} {D : QReg}

/-- **Condition 1 of ePrint 2025/2166, Lemma 5.7**, at a call: the operator `τ` presented to a
call of port `i` with remainder `E`, and every output of the step `s i` on it, lie in the image
of `P` on the runtime register, that is are fixed by the Kraus map of `(1 ⊗ P) ⊗ 1`. -/
@[expose]
def InImageAt (P : Matrix D D ℂ)
    (s : ∀ i, SubInstrument (spec.In i × D) (spec.Out i × D) (spec.Result i)) (i : spec.Port)
    (E : QReg) (τ : Matrix ((spec.In i × D) × E) ((spec.In i × D) × E) ℂ) : Prop :=
  MatrixMap.conj (((1 : Matrix (spec.In i) (spec.In i) ℂ) ⊗ₖ P) ⊗ₖ (1 : Matrix E E ℂ)) τ = τ ∧
    ∀ r, MatrixMap.conj (((1 : Matrix (spec.Out i) (spec.Out i) ℂ) ⊗ₖ P) ⊗ₖ (1 : Matrix E E ℂ))
      (((s i).frame E).branch r τ) = ((s i).frame E).branch r τ

/-- The steps compressed by a contraction `P` of the runtime register: `conj (P̂ U P̂)` for steps
`conj U`, with `P̂ = 1 ⊗ P`. -/
@[expose]
noncomputable def compressSteps (P : Matrix D D ℂ) (hP : (1 - Pᴴ * P).PosSemidef)
    (s : ∀ i, SubInstrument (spec.In i × D) (spec.Out i × D) (spec.Result i)) :
    ∀ i, SubInstrument (spec.In i × D) (spec.Out i × D) (spec.Result i) := fun i ↦
  krausSandwich (s i) ((1 : Matrix (spec.In i) (spec.In i) ℂ) ⊗ₖ P)
    ((1 : Matrix (spec.Out i) (spec.Out i) ℂ) ⊗ₖ P) (posSemidef_one_sub_one_kronecker hP)
    (posSemidef_one_sub_one_kronecker hP)

/-- The steps rotated by an isometry `V` of the runtime register: `conj (V̂ U V̂ᴴ)` for steps
`conj U`, with `V̂ = 1 ⊗ V`. -/
@[expose]
noncomputable def rotateSteps (V : Matrix D D ℂ) (hV : Vᴴ * V = 1)
    (s : ∀ i, SubInstrument (spec.In i × D) (spec.Out i × D) (spec.Result i)) :
    ∀ i, SubInstrument (spec.In i × D) (spec.Out i × D) (spec.Result i) := fun i ↦
  krausSandwich (s i) ((1 : Matrix (spec.In i) (spec.In i) ℂ) ⊗ₖ Vᴴ)
    ((1 : Matrix (spec.Out i) (spec.Out i) ℂ) ⊗ₖ V)
    (posSemidef_one_sub_one_kronecker (posSemidef_one_sub_conjTranspose hV))
    (posSemidef_one_sub_one_kronecker (posSemidef_one_sub_of_isometry hV))

/-- The operators whose Kraus weights bound the hybrid with a projector `P` and an isometry `V`:
`V̂ P̂ U P̂ - P̂ W P̂ V̂`, with `P̂ = 1 ⊗ P` and `V̂ = 1 ⊗ V` on the input or output and the
runtime register. Under `P V = V P` and for a unitary `V`, its operator norm is that of
`P̂ (V̂ U V̂ᴴ - W) P̂` (`Quantum.Hybrid.l2_opNorm_lemmaKraus`). -/
@[expose]
def lemmaKraus (P V : Matrix D D ℂ)
    (U W : ∀ i, spec.Result i → Matrix (spec.Out i × D) (spec.In i × D) ℂ) (i : spec.Port)
    (r : spec.Result i) : Matrix (spec.Out i × D) (spec.In i × D) ℂ :=
  ((1 : Matrix (spec.Out i) (spec.Out i) ℂ) ⊗ₖ V) *
      (((1 : Matrix (spec.Out i) (spec.Out i) ℂ) ⊗ₖ P) * U i r *
        ((1 : Matrix (spec.In i) (spec.In i) ℂ) ⊗ₖ P)) -
    ((1 : Matrix (spec.Out i) (spec.Out i) ℂ) ⊗ₖ P) * W i r *
      ((1 : Matrix (spec.In i) (spec.In i) ℂ) ⊗ₖ P) *
        ((1 : Matrix (spec.In i) (spec.In i) ℂ) ⊗ₖ V)

/-- The operators of ePrint 2025/2166, Lemma 5.7: `P̂ (V̂ U V̂ᴴ - W) P̂`, with `P̂ = 1 ⊗ P` and
`V̂ = 1 ⊗ V` on the input or output and the runtime register. -/
@[expose]
def projDiff (P V : Matrix D D ℂ)
    (U W : ∀ i, spec.Result i → Matrix (spec.Out i × D) (spec.In i × D) ℂ) (i : spec.Port)
    (r : spec.Result i) : Matrix (spec.Out i × D) (spec.In i × D) ℂ :=
  ((1 : Matrix (spec.Out i) (spec.Out i) ℂ) ⊗ₖ P) *
      (((1 : Matrix (spec.Out i) (spec.Out i) ℂ) ⊗ₖ V) * U i r *
          ((1 : Matrix (spec.In i) (spec.In i) ℂ) ⊗ₖ Vᴴ) - W i r) *
    ((1 : Matrix (spec.In i) (spec.In i) ℂ) ⊗ₖ P)

/-- Under condition 3 of ePrint 2025/2166, Lemma 5.7 (`P V = V P`) and for an isometry `V`,
`V̂ P̂ U P̂ - P̂ W P̂ V̂ = P̂ (V̂ U V̂ᴴ - W) P̂ V̂`. -/
theorem lemmaKraus_eq_projDiff_mul {P V : Matrix D D ℂ} (hV : Vᴴ * V = 1) (hPV : P * V = V * P)
    (U W : ∀ i, spec.Result i → Matrix (spec.Out i × D) (spec.In i × D) ℂ) (i : spec.Port)
    (r : spec.Result i) :
    lemmaKraus P V U W i r =
      projDiff P V U W i r * ((1 : Matrix (spec.In i) (spec.In i) ℂ) ⊗ₖ V) := by
  have hVP : Vᴴ * (V * P) = P := by rw [← Matrix.mul_assoc, hV, Matrix.one_mul]
  simp only [lemmaKraus, projDiff, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc,
    one_kronecker_mul_one_kronecker, one_kronecker_mul_one_kronecker_mul, hPV, hVP]

open scoped Matrix.Norms.L2Operator in
/-- Under condition 3 of ePrint 2025/2166, Lemma 5.7, and for a unitary `V`, the operators
`lemmaKraus P V U W` have the operator norms of `P̂ (V̂ U V̂ᴴ - W) P̂`. -/
theorem l2_opNorm_lemmaKraus {P V : Matrix D D ℂ} (hV : Vᴴ * V = 1) (hPV : P * V = V * P)
    (U W : ∀ i, spec.Result i → Matrix (spec.Out i × D) (spec.In i × D) ℂ) (i : spec.Port)
    (r : spec.Result i) : ‖lemmaKraus P V U W i r‖ = ‖projDiff P V U W i r‖ := by
  rw [lemmaKraus_eq_projDiff_mul hV hPV, MatrixMap.l2_opNorm_mul_coisometry
    (one_kronecker_mul_conjTranspose (_root_.mul_eq_one_comm.mp hV))]

variable {P V : Matrix D D ℂ} (hP : (1 - Pᴴ * P).PosSemidef) (hV : Vᴴ * V = 1)
  {s : ∀ i, SubInstrument (spec.In i × D) (spec.Out i × D) (spec.Result i)}

/-- Under condition 1 at a call, the compressed step acts as the step. -/
theorem compressSteps_frame_branch_eq {i : spec.Port} {E : QReg}
    {τ : Matrix ((spec.In i × D) × E) ((spec.In i × D) × E) ℂ} (hτ : InImageAt P s i E τ)
    (r : spec.Result i) :
    ((compressSteps P hP s i).frame E).branch r τ = ((s i).frame E).branch r τ := by
  change (MatrixMap.conj _).amplify E (((s i).branch r).amplify E
    ((MatrixMap.conj _).amplify E τ)) = _
  rw [MatrixMap.amplify_conj, MatrixMap.amplify_conj, hτ.1]
  exact hτ.2 r

/-- The rotated steps simulate the steps through `conj V`. -/
theorem rotateSteps_simulation (i : spec.Port) (r : spec.Result i) :
    (rotateSteps V hV s i).branch r ∘ₗ (MatrixMap.conj V).amplifyLeft (spec.In i) =
      (MatrixMap.conj V).amplifyLeft (spec.Out i) ∘ₗ (s i).branch r := by
  rw [MatrixMap.amplifyLeft_conj, MatrixMap.amplifyLeft_conj]
  change ((MatrixMap.conj _).comp (((s i).branch r).comp (MatrixMap.conj _))).comp
    (MatrixMap.conj _) = _
  rw [LinearMap.comp_assoc, LinearMap.comp_assoc, ← MatrixMap.conj_mul, ← mul_kronecker_mul,
    Matrix.one_mul, hV, one_kronecker_one, MatrixMap.conj_one, LinearMap.comp_id]

/-- Squaring a bound by a square root in `ℝ≥0∞`: if `a ≤ √c` then `a² ≤ c`. -/
theorem sq_le_of_le_rpow_inv_two {a c : ℝ≥0∞} (h : a ≤ c ^ (2⁻¹ : ℝ)) : a ^ 2 ≤ c :=
  calc a ^ 2 ≤ (c ^ (2⁻¹ : ℝ)) ^ 2 := pow_le_pow_left₀ zero_le h 2
    _ = c := by simpa using ENNReal.rpow_inv_natCast_pow (n := 2) two_ne_zero c

end Hybrid

/-! ## The bound -/

namespace QuantumRuntime

open Hybrid

variable {spec : QuantumOracleSpec.{u₁, v₁}} {L : LocalSig.{u, v}} (I : L.Interp)
  {X : QReg → Type w} {A : QReg}
  {D : QReg} {s₀ s₁ : ∀ i, SubInstrument (spec.In i × D) (spec.Out i × D) (spec.Result i)}
  {U W : ∀ i, spec.Result i → Matrix (spec.Out i × D) (spec.In i × D) ℂ}
  {σ₀ σ₁ : SubState D}
  (hU : ∀ i r, (s₀ i).branch r = MatrixMap.conj (U i r))
  (hW : ∀ i r, (s₁ i).branch r = MatrixMap.conj (W i r))
  {P V : Matrix D D ℂ} (hP : (1 - Pᴴ * P).PosSemidef) (hV : Vᴴ * V = 1)
include hU hW hP hV

omit hU hW in
/-- The three identities that reduce the bound to the core bound for the rotated compressed
first runtime and the compressed second runtime. -/
private theorem inImage_reduce (x : QuantumComp L spec X A) {ρ : Matrix (A × D) (A × D) ℂ}
    (hVρ : MatrixMap.conj ((1 : Matrix A A ℂ) ⊗ₖ V) ρ = ρ)
    (h₀ : (QuantumRuntime.mk D σ₀ s₀).ForallQueries I (InImageAt P s₀) x ρ)
    (h₁ : (QuantumRuntime.mk D σ₁ s₁).ForallQueries I (InImageAt P s₁) x ρ)
    {Z : (Σ u, X u) → Type*} (O : ∀ p : Σ u, X u, Matrix (Z p) (p.1 × D) ℂ) :
    (∀ p, MatrixMap.conj (O p) (((QuantumRuntime.mk D σ₀ s₀).run I x).branch p ρ) =
      MatrixMap.conj (O p * ((1 : Matrix p.1 p.1 ℂ) ⊗ₖ Vᴴ))
        (((QuantumRuntime.mk D σ₀ (rotateSteps V hV (compressSteps P hP s₀))).run I x).branch p
          ρ)) ∧
    (∀ p, ((QuantumRuntime.mk D σ₁ s₁).run I x).branch p ρ =
      ((QuantumRuntime.mk D σ₁ (compressSteps P hP s₁)).run I x).branch p ρ) ∧
    ∀ j, (QuantumRuntime.mk D σ₀ (rotateSteps V hV (compressSteps P hP s₀))).queryWeight I
        (krausWeight fun i r ↦
          ((1 : Matrix (spec.Out i) (spec.Out i) ℂ) ⊗ₖ V) *
              (((1 : Matrix (spec.Out i) (spec.Out i) ℂ) ⊗ₖ P) * U i r *
                ((1 : Matrix (spec.In i) (spec.In i) ℂ) ⊗ₖ P)) *
              ((1 : Matrix (spec.In i) (spec.In i) ℂ) ⊗ₖ Vᴴ) -
            ((1 : Matrix (spec.Out i) (spec.Out i) ℂ) ⊗ₖ P) * W i r *
              ((1 : Matrix (spec.In i) (spec.In i) ℂ) ⊗ₖ P)) x ρ j =
      (QuantumRuntime.mk D σ₀ s₀).queryWeight I (krausWeight (lemmaKraus P V U W)) x ρ j := by
  have hs₀ : ∀ i E τ, InImageAt P s₀ i E τ → ∀ r,
      ((s₀ i).frame E).branch r τ = ((compressSteps P hP s₀ i).frame E).branch r τ :=
    fun _ _ _ hτ r ↦ (compressSteps_frame_branch_eq hP hτ r).symm
  have hs₁ : ∀ i E τ, InImageAt P s₁ i E τ → ∀ r,
      ((s₁ i).frame E).branch r τ = ((compressSteps P hP s₁ i).frame E).branch r τ :=
    fun _ _ _ hτ r ↦ (compressSteps_frame_branch_eq hP hτ r).symm
  have hρV : ρ = (MatrixMap.conj V).amplifyLeft A ρ := by
    rw [MatrixMap.amplifyLeft_conj, hVρ]
  refine ⟨fun p ↦ ?_, fun p ↦ run_branch_apply_eq_of_forallQueries I hs₁ h₁ p, fun j ↦ ?_⟩
  · have hsim := LinearMap.congr_fun (simulation I
      (R₁ := QuantumRuntime.mk D σ₀ (compressSteps P hP s₀))
      (R₂ := QuantumRuntime.mk D σ₀ (rotateSteps V hV (compressSteps P hP s₀)))
      (V := MatrixMap.conj V) (rotateSteps_simulation hV) x p) ρ
    rw [LinearMap.comp_apply, LinearMap.comp_apply, ← hρV, MatrixMap.amplifyLeft_conj] at hsim
    rw [hsim, ← LinearMap.comp_apply (MatrixMap.conj (O p * ((1 : Matrix p.1 p.1 ℂ) ⊗ₖ Vᴴ))),
      ← MatrixMap.conj_mul, Matrix.mul_assoc, one_kronecker_conjTranspose_mul hV, Matrix.mul_one,
      run_branch_apply_eq_of_forallQueries (σ₂ := σ₀) I hs₀ h₀ p]
  · rw [hρV, queryWeight_simulation I (R₁ := QuantumRuntime.mk D σ₀ (compressSteps P hP s₀))
      (R₂ := QuantumRuntime.mk D σ₀ (rotateSteps V hV (compressSteps P hP s₀)))
      (V := MatrixMap.conj V) (rotateSteps_simulation hV), ← hρV,
      ← queryWeight_eq_of_forallQueries (σ₂ := σ₀) I hs₀ _ h₀]
    refine congrArg (fun w ↦ (QuantumRuntime.mk D σ₀ s₀).queryWeight I w x ρ j)
      (funext fun i ↦ funext fun σ ↦ ?_)
    simp only [krausWeight, MatrixMap.amplifyLeft_conj, lemmaKraus]
    refine tsum_congr fun r ↦ ?_
    rw [← LinearMap.comp_apply, ← MatrixMap.conj_mul, Matrix.sub_mul,
      Matrix.mul_assoc _ ((1 : Matrix (spec.In i) (spec.In i) ℂ) ⊗ₖ Vᴴ),
      one_kronecker_conjTranspose_mul hV, Matrix.mul_one]

/-- **The square-root hybrid bound with a projector and an isometry** (ePrint 2025/2166,
Lemma 5.7, for general programs). Let the steps of two runtimes on the register `D` be the Kraus
maps of `U i r` and `W i r`, let `P` be a contraction and `V` an isometry of `D`, and let the
joint operator `ρ` be invariant under `1 ⊗ V` (condition 2). If the operator presented to every
call of each run, and every output of the step on it, are fixed by `1 ⊗ P` (condition 1), then
for contractions `O p` at the leaves the square root of the summed weights `tr (O p ρ_p (O p)ᴴ)`
of the first run is at most that of the second for `O p (1 ⊗ Vᴴ)`, plus the sum over the calls of
the square roots of the Kraus weights of `V̂ P̂ U P̂ - P̂ W P̂ V̂` on the inputs of the calls of the
first run. No commutation of `P` and `V` is assumed. -/
theorem rpow_inv_two_tsum_trace_conj_run_le_of_inImage (x : QuantumComp L spec X A)
    {Z : (Σ u, X u) → Type*} [∀ p, Fintype (Z p)] (O : ∀ p : Σ u, X u, Matrix (Z p) (p.1 × D) ℂ)
    (hO : ∀ p, (1 - (O p)ᴴ * O p).PosSemidef) {ρ : Matrix (A × D) (A × D) ℂ}
    (hρ : ρ.PosSemidef) (hVρ : MatrixMap.conj ((1 : Matrix A A ℂ) ⊗ₖ V) ρ = ρ)
    (h₀ : (QuantumRuntime.mk D σ₀ s₀).ForallQueries I (InImageAt P s₀) x ρ)
    (h₁ : (QuantumRuntime.mk D σ₁ s₁).ForallQueries I (InImageAt P s₁) x ρ) :
    (∑' p, ENNReal.ofReal (MatrixMap.conj (O p)
        (((QuantumRuntime.mk D σ₀ s₀).run I x).branch p ρ)).trace.re) ^ (2⁻¹ : ℝ) ≤
      (∑' p, ENNReal.ofReal (MatrixMap.conj (O p * ((1 : Matrix p.1 p.1 ℂ) ⊗ₖ Vᴴ))
          (((QuantumRuntime.mk D σ₁ s₁).run I x).branch p ρ)).trace.re) ^ (2⁻¹ : ℝ) +
        ∑' j, (QuantumRuntime.mk D σ₀ s₀).queryWeight I (krausWeight (lemmaKraus P V U W)) x
          ρ j ^ (2⁻¹ : ℝ) := by
  obtain ⟨e₀, e₁, e₂⟩ := inImage_reduce I hP hV x hVρ h₀ h₁ O
  have hO' : ∀ p, (1 - (O p * ((1 : Matrix p.1 p.1 ℂ) ⊗ₖ Vᴴ))ᴴ *
      (O p * ((1 : Matrix p.1 p.1 ℂ) ⊗ₖ Vᴴ))).PosSemidef := fun p ↦
    posSemidef_one_sub_mul (hO p)
      (posSemidef_one_sub_one_kronecker (posSemidef_one_sub_conjTranspose hV))
  have h := rpow_inv_two_tsum_trace_conj_run_le I σ₀ σ₁
    (s₀ := rotateSteps V hV (compressSteps P hP s₀)) (s₁ := compressSteps P hP s₁)
    (fun i r ↦ branch_krausSandwich_of_eq_conj
      (fun r ↦ branch_krausSandwich_of_eq_conj (hU i) _ _ _ _ r) _ _ _ _ r)
    (fun i r ↦ branch_krausSandwich_of_eq_conj (hW i) _ _ _ _ r) x _ hO' hρ
  simp only [← e₀, ← e₁] at h
  refine h.trans_eq ?_
  congr 1
  exact tsum_congr fun j ↦ congrArg (· ^ (2⁻¹ : ℝ)) (e₂ j)

/-- **The square-root hybrid bound with a projector and an isometry**, converse direction. -/
theorem rpow_inv_two_tsum_trace_conj_run_le_of_inImage' (x : QuantumComp L spec X A)
    {Z : (Σ u, X u) → Type*} [∀ p, Fintype (Z p)] (O : ∀ p : Σ u, X u, Matrix (Z p) (p.1 × D) ℂ)
    (hO : ∀ p, (1 - (O p)ᴴ * O p).PosSemidef) {ρ : Matrix (A × D) (A × D) ℂ}
    (hρ : ρ.PosSemidef) (hVρ : MatrixMap.conj ((1 : Matrix A A ℂ) ⊗ₖ V) ρ = ρ)
    (h₀ : (QuantumRuntime.mk D σ₀ s₀).ForallQueries I (InImageAt P s₀) x ρ)
    (h₁ : (QuantumRuntime.mk D σ₁ s₁).ForallQueries I (InImageAt P s₁) x ρ) :
    (∑' p, ENNReal.ofReal (MatrixMap.conj (O p * ((1 : Matrix p.1 p.1 ℂ) ⊗ₖ Vᴴ))
        (((QuantumRuntime.mk D σ₁ s₁).run I x).branch p ρ)).trace.re) ^ (2⁻¹ : ℝ) ≤
      (∑' p, ENNReal.ofReal (MatrixMap.conj (O p)
          (((QuantumRuntime.mk D σ₀ s₀).run I x).branch p ρ)).trace.re) ^ (2⁻¹ : ℝ) +
        ∑' j, (QuantumRuntime.mk D σ₀ s₀).queryWeight I (krausWeight (lemmaKraus P V U W)) x
          ρ j ^ (2⁻¹ : ℝ) := by
  obtain ⟨e₀, e₁, e₂⟩ := inImage_reduce I hP hV x hVρ h₀ h₁ O
  have hO' : ∀ p, (1 - (O p * ((1 : Matrix p.1 p.1 ℂ) ⊗ₖ Vᴴ))ᴴ *
      (O p * ((1 : Matrix p.1 p.1 ℂ) ⊗ₖ Vᴴ))).PosSemidef := fun p ↦
    posSemidef_one_sub_mul (hO p)
      (posSemidef_one_sub_one_kronecker (posSemidef_one_sub_conjTranspose hV))
  have h := rpow_inv_two_tsum_trace_conj_run_le' I σ₀ σ₁
    (s₀ := rotateSteps V hV (compressSteps P hP s₀)) (s₁ := compressSteps P hP s₁)
    (fun i r ↦ branch_krausSandwich_of_eq_conj
      (fun r ↦ branch_krausSandwich_of_eq_conj (hU i) _ _ _ _ r) _ _ _ _ r)
    (fun i r ↦ branch_krausSandwich_of_eq_conj (hW i) _ _ _ _ r) x _ hO' hρ
  simp only [← e₀, ← e₁] at h
  refine h.trans_eq ?_
  congr 1
  exact tsum_congr fun j ↦ congrArg (· ^ (2⁻¹ : ℝ)) (e₂ j)

/-! ## Events -/

omit hU hW hP in
/-- The observable of a set of leaves, rotated by `1 ⊗ V`. -/
private theorem tsum_indicator_eq_isometry {γ : Type*} (f : (Σ u, X u) → γ) (s : Set γ)
    [DecidablePred (· ∈ s)] (B : ∀ p : Σ u, X u, Matrix (p.1 × D) (p.1 × D) ℂ) :
    ∑' p, ENNReal.ofReal (B p).trace.re * s.indicator 1 (f p) =
      ∑' p, ENNReal.ofReal (MatrixMap.conj
        (if f p ∈ s then (1 : Matrix p.1 p.1 ℂ) ⊗ₖ V else 0) (B p)).trace.re := by
  refine tsum_congr fun p ↦ ?_
  by_cases h : f p ∈ s
  · simp only [h, ↓reduceIte, Set.indicator_of_mem h, Pi.one_apply, mul_one]
    rw [trace_conj_of_isometry (one_kronecker_isometry hV)]
  · simp [h]

omit hU hW hP in
private theorem tsum_indicator_eq_coisometry {γ : Type*} (f : (Σ u, X u) → γ) (s : Set γ)
    [DecidablePred (· ∈ s)] (B : ∀ p : Σ u, X u, Matrix (p.1 × D) (p.1 × D) ℂ) :
    ∑' p, ENNReal.ofReal (B p).trace.re * s.indicator 1 (f p) =
      ∑' p, ENNReal.ofReal (MatrixMap.conj
        ((if f p ∈ s then (1 : Matrix p.1 p.1 ℂ) ⊗ₖ V else 0) *
          ((1 : Matrix p.1 p.1 ℂ) ⊗ₖ Vᴴ)) (B p)).trace.re := by
  have hV' : V * Vᴴ = 1 := _root_.mul_eq_one_comm.mp hV
  refine tsum_congr fun p ↦ ?_
  by_cases h : f p ∈ s
  · simp [h, one_kronecker_mul_one_kronecker, hV']
  · simp [h]

omit hU hW hP in
private theorem posSemidef_one_sub_indicator_isometry {γ : Type*} (f : (Σ u, X u) → γ)
    (s : Set γ) [DecidablePred (· ∈ s)] (p : Σ u, X u) :
    (1 - (if f p ∈ s then (1 : Matrix p.1 p.1 ℂ) ⊗ₖ V else 0)ᴴ *
      (if f p ∈ s then (1 : Matrix p.1 p.1 ℂ) ⊗ₖ V else 0)).PosSemidef := by
  by_cases h : f p ∈ s
  · simp only [h, ↓reduceIte]
    exact posSemidef_one_sub_of_isometry (one_kronecker_isometry hV)
  · simp [h, Matrix.PosSemidef.one]

omit hU hW hP hV in
private theorem conj_one_kronecker_kronecker (ρ : Matrix A A ℂ) {σ : Matrix D D ℂ}
    (hVσ : MatrixMap.conj V σ = σ) :
    MatrixMap.conj ((1 : Matrix A A ℂ) ⊗ₖ V) (ρ ⊗ₖ σ) = ρ ⊗ₖ σ := by
  rw [MatrixMap.conj_apply] at hVσ ⊢
  rw [conjTranspose_kronecker, conjTranspose_one, ← mul_kronecker_mul, ← mul_kronecker_mul,
    Matrix.one_mul, Matrix.mul_one, hVσ]

/-- **The square-root hybrid bound with a projector and an isometry, for events** (ePrint
2025/2166, Lemma 5.7, for general programs). Two runtimes with the same register and initial
state `σ₀`, invariant under `V` (condition 2), and steps the Kraus maps of `U i r` and `W i r`,
satisfying condition 1 for the contraction `P` along both runs, give laws of any observation `f`
of the leaves whose square roots differ, on every measurable set, by at most the sum over the
calls of the square roots of the Kraus weights of `V̂ P̂ U P̂ - P̂ W P̂ V̂` on the inputs of the
calls of the run against the first runtime. -/
theorem rpow_inv_two_outcomeLawWith_le_of_inImage {γ : Type*} [MeasurableSpace γ]
    (x : QuantumComp L spec X A) (ρ : SubState A) (f : (Σ u, X u) → γ) {s : Set γ}
    (hs : MeasurableSet s) (hVσ : MatrixMap.conj V σ₀.matrix = σ₀.matrix)
    (h₀ : (QuantumRuntime.mk D σ₀ s₀).ForallQueries I (InImageAt P s₀) x
      (ρ.matrix ⊗ₖ σ₀.matrix))
    (h₁ : (QuantumRuntime.mk D σ₀ s₁).ForallQueries I (InImageAt P s₁) x
      (ρ.matrix ⊗ₖ σ₀.matrix)) :
    (QuantumRuntime.mk D σ₀ s₀).outcomeLawWith I x ρ f s ^ (2⁻¹ : ℝ) ≤
      (QuantumRuntime.mk D σ₀ s₁).outcomeLawWith I x ρ f s ^ (2⁻¹ : ℝ) +
        ∑' j, (QuantumRuntime.mk D σ₀ s₀).queryWeight I (krausWeight (lemmaKraus P V U W)) x
          (ρ.matrix ⊗ₖ σ₀.matrix) j ^ (2⁻¹ : ℝ) := by
  classical
  rw [outcomeLawWith_apply _ _ _ _ _ hs, outcomeLawWith_apply _ _ _ _ _ hs]
  simp only [matrix_jointPost]
  rw [tsum_indicator_eq_isometry hV f s
      (fun p ↦ ((QuantumRuntime.mk D σ₀ s₀).run I x).branch p (ρ.matrix ⊗ₖ σ₀.matrix)),
    tsum_indicator_eq_coisometry hV f s
      (fun p ↦ ((QuantumRuntime.mk D σ₀ s₁).run I x).branch p (ρ.matrix ⊗ₖ σ₀.matrix))]
  exact rpow_inv_two_tsum_trace_conj_run_le_of_inImage I (σ₁ := σ₀) hU hW hP hV x _
    (posSemidef_one_sub_indicator_isometry hV f s) (ρ.prod σ₀).posSemidef
    (conj_one_kronecker_kronecker _ hVσ) h₀ h₁

/-- **The square-root hybrid bound with a projector and an isometry, for events**, converse
direction. -/
theorem rpow_inv_two_outcomeLawWith_le_of_inImage' {γ : Type*} [MeasurableSpace γ]
    (x : QuantumComp L spec X A) (ρ : SubState A) (f : (Σ u, X u) → γ) {s : Set γ}
    (hs : MeasurableSet s) (hVσ : MatrixMap.conj V σ₀.matrix = σ₀.matrix)
    (h₀ : (QuantumRuntime.mk D σ₀ s₀).ForallQueries I (InImageAt P s₀) x
      (ρ.matrix ⊗ₖ σ₀.matrix))
    (h₁ : (QuantumRuntime.mk D σ₀ s₁).ForallQueries I (InImageAt P s₁) x
      (ρ.matrix ⊗ₖ σ₀.matrix)) :
    (QuantumRuntime.mk D σ₀ s₁).outcomeLawWith I x ρ f s ^ (2⁻¹ : ℝ) ≤
      (QuantumRuntime.mk D σ₀ s₀).outcomeLawWith I x ρ f s ^ (2⁻¹ : ℝ) +
        ∑' j, (QuantumRuntime.mk D σ₀ s₀).queryWeight I (krausWeight (lemmaKraus P V U W)) x
          (ρ.matrix ⊗ₖ σ₀.matrix) j ^ (2⁻¹ : ℝ) := by
  classical
  rw [outcomeLawWith_apply _ _ _ _ _ hs, outcomeLawWith_apply _ _ _ _ _ hs]
  simp only [matrix_jointPost]
  rw [tsum_indicator_eq_isometry hV f s
      (fun p ↦ ((QuantumRuntime.mk D σ₀ s₀).run I x).branch p (ρ.matrix ⊗ₖ σ₀.matrix)),
    tsum_indicator_eq_coisometry hV f s
      (fun p ↦ ((QuantumRuntime.mk D σ₀ s₁).run I x).branch p (ρ.matrix ⊗ₖ σ₀.matrix))]
  exact rpow_inv_two_tsum_trace_conj_run_le_of_inImage' I (σ₁ := σ₀) hU hW hP hV x _
    (posSemidef_one_sub_indicator_isometry hV f s) (ρ.prod σ₀).posSemidef
    (conj_one_kronecker_kronecker _ hVσ) h₀ h₁

open scoped Matrix.Norms.L2Operator

omit hU hW hP in
private theorem krausWeight_lemmaKraus_le (hPV : P * V = V * P) (i : spec.Port)
    {τ : Matrix (spec.In i × D) (spec.In i × D) ℂ} (hτ : τ.PosSemidef) :
    krausWeight (lemmaKraus P V U W) i τ ≤
      (∑' r, ENNReal.ofReal (‖projDiff P V U W i r‖ ^ 2)) * ENNReal.ofReal τ.trace.re := by
  refine (krausWeight_le _ i hτ).trans_eq ?_
  simp only [l2_opNorm_lemmaKraus hV hPV]

omit hU hW hP in
/-- The Kraus weights of `lemmaKraus P V U W` on the calls of a run, under condition 3, by the
masses of the classical ports of that run. -/
private theorem tsum_rpow_queryWeight_lemmaKraus_le_mass (hPV : P * V = V * P)
    (x : QuantumComp L spec X A) (ρ : SubState A) :
    ∑' j, (QuantumRuntime.mk D σ₀ s₀).queryWeight I (krausWeight (lemmaKraus P V U W)) x
        (ρ.matrix ⊗ₖ σ₀.matrix) j ^ (2⁻¹ : ℝ) ≤
      ∑' j, (∑' i, (∑' r, ENNReal.ofReal (‖projDiff P V U W i r‖ ^ 2)) *
        (QuantumRuntime.mk D σ₀ s₀).queryMassAt I x (ρ.matrix ⊗ₖ σ₀.matrix) i j) ^
          (2⁻¹ : ℝ) :=
  ENNReal.tsum_le_tsum fun j ↦ ENNReal.rpow_le_rpow
    ((QuantumRuntime.mk D σ₀ s₀).queryWeight_le_tsum_mul_queryMassAt I _
      (fun i _ hτ ↦ krausWeight_lemmaKraus_le hV hPV i hτ) x (ρ.prod σ₀).posSemidef j)
    (by norm_num)

omit hU hW hP in
/-- The Kraus weights of `lemmaKraus P V U W` on the calls of a run within a query budget, under
condition 3, by the total masses of the classical ports of that run. -/
private theorem tsum_rpow_queryWeight_lemmaKraus_le_of_isQueryBound (hPV : P * V = V * P)
    {x : QuantumComp L spec X A} {b : spec.Port → ℕ} (hx : x.IsQueryBound b)
    (t : Finset spec.Port) (ht : ∀ i ∉ t, b i = 0) (ρ : SubState A) :
    ∑' j, (QuantumRuntime.mk D σ₀ s₀).queryWeight I (krausWeight (lemmaKraus P V U W)) x
        (ρ.matrix ⊗ₖ σ₀.matrix) j ^ (2⁻¹ : ℝ) ≤
      (((∑ i ∈ t, b i : ℕ) : ℝ≥0∞) *
        ∑' i, (∑' r, ENNReal.ofReal (‖projDiff P V U W i r‖ ^ 2)) *
          (QuantumRuntime.mk D σ₀ s₀).queryMass I x (ρ.matrix ⊗ₖ σ₀.matrix) i) ^
        (2⁻¹ : ℝ) := by
  refine (tsum_rpow_inv_two_queryWeight_le_of_isQueryBound I _ hx t ht _).trans ?_
  gcongr
  exact (QuantumRuntime.mk D σ₀ s₀).tsum_queryWeight_le_tsum_mul_queryMass I _
    (fun i _ hτ ↦ krausWeight_lemmaKraus_le hV hPV i hτ) x (ρ.prod σ₀).posSemidef

/-- **ePrint 2025/2166, Lemma 5.7, with the masses of the classical ports**, for general
programs: under conditions 1 to 3, the square root of the probability of an event against the
first runtime exceeds the one against the second by at most
`∑ⱼ √(∑ᵢ (∑ᵣ ‖P̂ (V̂ U V̂ᴴ - W) P̂‖²) · mass(i, j))`, with the masses of the ports at the `j`-th
calls of the run against the first runtime. The converse, with the same masses, is
`Quantum.QuantumRuntime.rpow_inv_two_outcomeLawWith_le_of_inImage_mass'`, and the two-sided form
`Quantum.QuantumRuntime.max_tsub_rpow_inv_two_outcomeLawWith_le_of_inImage_mass`. The paper's
masses are those of a coherent index (§4.2); that form is
`Quantum.QuantumRuntime.rpow_inv_two_outcomeLawWith_le_of_inImage_indexMass`. -/
theorem rpow_inv_two_outcomeLawWith_le_of_inImage_mass {γ : Type*} [MeasurableSpace γ]
    (x : QuantumComp L spec X A) (ρ : SubState A) (f : (Σ u, X u) → γ) {s : Set γ}
    (hs : MeasurableSet s) (hVσ : MatrixMap.conj V σ₀.matrix = σ₀.matrix)
    (hPV : P * V = V * P)
    (h₀ : (QuantumRuntime.mk D σ₀ s₀).ForallQueries I (InImageAt P s₀) x
      (ρ.matrix ⊗ₖ σ₀.matrix))
    (h₁ : (QuantumRuntime.mk D σ₀ s₁).ForallQueries I (InImageAt P s₁) x
      (ρ.matrix ⊗ₖ σ₀.matrix)) :
    (QuantumRuntime.mk D σ₀ s₀).outcomeLawWith I x ρ f s ^ (2⁻¹ : ℝ) ≤
      (QuantumRuntime.mk D σ₀ s₁).outcomeLawWith I x ρ f s ^ (2⁻¹ : ℝ) +
        ∑' j, (∑' i, (∑' r, ENNReal.ofReal (‖projDiff P V U W i r‖ ^ 2)) *
          (QuantumRuntime.mk D σ₀ s₀).queryMassAt I x (ρ.matrix ⊗ₖ σ₀.matrix) i j) ^
            (2⁻¹ : ℝ) :=
  (rpow_inv_two_outcomeLawWith_le_of_inImage I hU hW hP hV x ρ f hs hVσ h₀ h₁).trans <|
    add_le_add le_rfl <| tsum_rpow_queryWeight_lemmaKraus_le_mass I hV hPV x ρ

/-- **ePrint 2025/2166, Lemma 5.7, with the masses of the classical ports**, converse
direction: under conditions 1 to 3, the square root of the probability of an event against the
second runtime exceeds the one against the first by at most the same
`∑ⱼ √(∑ᵢ (∑ᵣ ‖P̂ (V̂ U V̂ᴴ - W) P̂‖²) · mass(i, j))`, with the masses of the run against the
first runtime. -/
theorem rpow_inv_two_outcomeLawWith_le_of_inImage_mass' {γ : Type*} [MeasurableSpace γ]
    (x : QuantumComp L spec X A) (ρ : SubState A) (f : (Σ u, X u) → γ) {s : Set γ}
    (hs : MeasurableSet s) (hVσ : MatrixMap.conj V σ₀.matrix = σ₀.matrix)
    (hPV : P * V = V * P)
    (h₀ : (QuantumRuntime.mk D σ₀ s₀).ForallQueries I (InImageAt P s₀) x
      (ρ.matrix ⊗ₖ σ₀.matrix))
    (h₁ : (QuantumRuntime.mk D σ₀ s₁).ForallQueries I (InImageAt P s₁) x
      (ρ.matrix ⊗ₖ σ₀.matrix)) :
    (QuantumRuntime.mk D σ₀ s₁).outcomeLawWith I x ρ f s ^ (2⁻¹ : ℝ) ≤
      (QuantumRuntime.mk D σ₀ s₀).outcomeLawWith I x ρ f s ^ (2⁻¹ : ℝ) +
        ∑' j, (∑' i, (∑' r, ENNReal.ofReal (‖projDiff P V U W i r‖ ^ 2)) *
          (QuantumRuntime.mk D σ₀ s₀).queryMassAt I x (ρ.matrix ⊗ₖ σ₀.matrix) i j) ^
            (2⁻¹ : ℝ) :=
  (rpow_inv_two_outcomeLawWith_le_of_inImage' I hU hW hP hV x ρ f hs hVσ h₀ h₁).trans <|
    add_le_add le_rfl <| tsum_rpow_queryWeight_lemmaKraus_le_mass I hV hPV x ρ

/-- **ePrint 2025/2166, Lemma 5.7, with the masses of the classical ports**, two-sided: under
conditions 1 to 3, `|√p₀ - √p₁| ≤ ∑ⱼ √(∑ᵢ (∑ᵣ ‖P̂ (V̂ U V̂ᴴ - W) P̂‖²) · mass(i, j))` for the
probabilities `p₀` and `p₁` of an event against the two runtimes, with the masses of the run
against the first runtime. In `ℝ≥0∞` the distance `|a - b|` is `max (a - b) (b - a)`. -/
theorem max_tsub_rpow_inv_two_outcomeLawWith_le_of_inImage_mass {γ : Type*}
    [MeasurableSpace γ] (x : QuantumComp L spec X A) (ρ : SubState A) (f : (Σ u, X u) → γ)
    {s : Set γ} (hs : MeasurableSet s) (hVσ : MatrixMap.conj V σ₀.matrix = σ₀.matrix)
    (hPV : P * V = V * P)
    (h₀ : (QuantumRuntime.mk D σ₀ s₀).ForallQueries I (InImageAt P s₀) x
      (ρ.matrix ⊗ₖ σ₀.matrix))
    (h₁ : (QuantumRuntime.mk D σ₀ s₁).ForallQueries I (InImageAt P s₁) x
      (ρ.matrix ⊗ₖ σ₀.matrix)) :
    max ((QuantumRuntime.mk D σ₀ s₀).outcomeLawWith I x ρ f s ^ (2⁻¹ : ℝ) -
        (QuantumRuntime.mk D σ₀ s₁).outcomeLawWith I x ρ f s ^ (2⁻¹ : ℝ))
      ((QuantumRuntime.mk D σ₀ s₁).outcomeLawWith I x ρ f s ^ (2⁻¹ : ℝ) -
        (QuantumRuntime.mk D σ₀ s₀).outcomeLawWith I x ρ f s ^ (2⁻¹ : ℝ)) ≤
      ∑' j, (∑' i, (∑' r, ENNReal.ofReal (‖projDiff P V U W i r‖ ^ 2)) *
        (QuantumRuntime.mk D σ₀ s₀).queryMassAt I x (ρ.matrix ⊗ₖ σ₀.matrix) i j) ^
          (2⁻¹ : ℝ) :=
  max_le
    (tsub_le_iff_left.2
      (rpow_inv_two_outcomeLawWith_le_of_inImage_mass I hU hW hP hV x ρ f hs hVσ hPV h₀ h₁))
    (tsub_le_iff_left.2
      (rpow_inv_two_outcomeLawWith_le_of_inImage_mass' I hU hW hP hV x ρ f hs hVσ hPV h₀ h₁))

/-- **ePrint 2025/2166, Lemma 5.7, for programs within a query budget**: with at most
`q = ∑ i ∈ t, b i` calls, the square root of the probability of an event against the first
runtime exceeds the one against the second by at most `√(q · ∑ᵢ Cᵢ · mass i)`, where
`Cᵢ = ∑ᵣ ‖P̂ (V̂ Uᵢ V̂ᴴ - Wᵢ) P̂‖²` and `mass i` is the total query mass of port `i` in the run
against the first runtime, by Cauchy–Schwarz as in Cor 5.8. The converse, with the same masses,
is `Quantum.QuantumRuntime.rpow_inv_two_outcomeLawWith_le_of_inImage_of_isQueryBound'`, and the
two-sided and squared forms are
`Quantum.QuantumRuntime.max_tsub_rpow_inv_two_outcomeLawWith_le_of_inImage_of_isQueryBound` and
`Quantum.QuantumRuntime.max_tsub_rpow_inv_two_outcomeLawWith_sq_le_of_inImage_of_isQueryBound`.
For the masses of a coherent index, see
`Quantum.QuantumRuntime.rpow_inv_two_outcomeLawWith_le_of_inImage_indexMass_of_isQueryBound`. -/
theorem rpow_inv_two_outcomeLawWith_le_of_inImage_of_isQueryBound {γ : Type*}
    [MeasurableSpace γ] {x : QuantumComp L spec X A} {b : spec.Port → ℕ} (hx : x.IsQueryBound b)
    (t : Finset spec.Port) (ht : ∀ i ∉ t, b i = 0) (ρ : SubState A) (f : (Σ u, X u) → γ)
    {s : Set γ} (hs : MeasurableSet s) (hVσ : MatrixMap.conj V σ₀.matrix = σ₀.matrix)
    (hPV : P * V = V * P)
    (h₀ : (QuantumRuntime.mk D σ₀ s₀).ForallQueries I (InImageAt P s₀) x
      (ρ.matrix ⊗ₖ σ₀.matrix))
    (h₁ : (QuantumRuntime.mk D σ₀ s₁).ForallQueries I (InImageAt P s₁) x
      (ρ.matrix ⊗ₖ σ₀.matrix)) :
    (QuantumRuntime.mk D σ₀ s₀).outcomeLawWith I x ρ f s ^ (2⁻¹ : ℝ) ≤
      (QuantumRuntime.mk D σ₀ s₁).outcomeLawWith I x ρ f s ^ (2⁻¹ : ℝ) +
        (((∑ i ∈ t, b i : ℕ) : ℝ≥0∞) *
          ∑' i, (∑' r, ENNReal.ofReal (‖projDiff P V U W i r‖ ^ 2)) *
            (QuantumRuntime.mk D σ₀ s₀).queryMass I x (ρ.matrix ⊗ₖ σ₀.matrix) i) ^
          (2⁻¹ : ℝ) :=
  (rpow_inv_two_outcomeLawWith_le_of_inImage I hU hW hP hV x ρ f hs hVσ h₀ h₁).trans <|
    add_le_add le_rfl <| tsum_rpow_queryWeight_lemmaKraus_le_of_isQueryBound I hV hPV hx t ht ρ

/-- **ePrint 2025/2166, Lemma 5.7, for programs within a query budget**, converse direction:
the square root of the probability of an event against the second runtime exceeds the one
against the first by at most the same `√(q · ∑ᵢ Cᵢ · mass i)`, with the total query masses of the
run against the first runtime. -/
theorem rpow_inv_two_outcomeLawWith_le_of_inImage_of_isQueryBound' {γ : Type*}
    [MeasurableSpace γ] {x : QuantumComp L spec X A} {b : spec.Port → ℕ} (hx : x.IsQueryBound b)
    (t : Finset spec.Port) (ht : ∀ i ∉ t, b i = 0) (ρ : SubState A) (f : (Σ u, X u) → γ)
    {s : Set γ} (hs : MeasurableSet s) (hVσ : MatrixMap.conj V σ₀.matrix = σ₀.matrix)
    (hPV : P * V = V * P)
    (h₀ : (QuantumRuntime.mk D σ₀ s₀).ForallQueries I (InImageAt P s₀) x
      (ρ.matrix ⊗ₖ σ₀.matrix))
    (h₁ : (QuantumRuntime.mk D σ₀ s₁).ForallQueries I (InImageAt P s₁) x
      (ρ.matrix ⊗ₖ σ₀.matrix)) :
    (QuantumRuntime.mk D σ₀ s₁).outcomeLawWith I x ρ f s ^ (2⁻¹ : ℝ) ≤
      (QuantumRuntime.mk D σ₀ s₀).outcomeLawWith I x ρ f s ^ (2⁻¹ : ℝ) +
        (((∑ i ∈ t, b i : ℕ) : ℝ≥0∞) *
          ∑' i, (∑' r, ENNReal.ofReal (‖projDiff P V U W i r‖ ^ 2)) *
            (QuantumRuntime.mk D σ₀ s₀).queryMass I x (ρ.matrix ⊗ₖ σ₀.matrix) i) ^
          (2⁻¹ : ℝ) :=
  (rpow_inv_two_outcomeLawWith_le_of_inImage' I hU hW hP hV x ρ f hs hVσ h₀ h₁).trans <|
    add_le_add le_rfl <| tsum_rpow_queryWeight_lemmaKraus_le_of_isQueryBound I hV hPV hx t ht ρ

/-- **ePrint 2025/2166, Lemma 5.7, for programs within a query budget**, two-sided:
`|√p₀ - √p₁| ≤ √(q · ∑ᵢ Cᵢ · mass i)`, with the total query masses of the run against the first
runtime. In `ℝ≥0∞` the distance `|a - b|` is `max (a - b) (b - a)`. -/
theorem max_tsub_rpow_inv_two_outcomeLawWith_le_of_inImage_of_isQueryBound {γ : Type*}
    [MeasurableSpace γ] {x : QuantumComp L spec X A} {b : spec.Port → ℕ} (hx : x.IsQueryBound b)
    (t : Finset spec.Port) (ht : ∀ i ∉ t, b i = 0) (ρ : SubState A) (f : (Σ u, X u) → γ)
    {s : Set γ} (hs : MeasurableSet s) (hVσ : MatrixMap.conj V σ₀.matrix = σ₀.matrix)
    (hPV : P * V = V * P)
    (h₀ : (QuantumRuntime.mk D σ₀ s₀).ForallQueries I (InImageAt P s₀) x
      (ρ.matrix ⊗ₖ σ₀.matrix))
    (h₁ : (QuantumRuntime.mk D σ₀ s₁).ForallQueries I (InImageAt P s₁) x
      (ρ.matrix ⊗ₖ σ₀.matrix)) :
    max ((QuantumRuntime.mk D σ₀ s₀).outcomeLawWith I x ρ f s ^ (2⁻¹ : ℝ) -
        (QuantumRuntime.mk D σ₀ s₁).outcomeLawWith I x ρ f s ^ (2⁻¹ : ℝ))
      ((QuantumRuntime.mk D σ₀ s₁).outcomeLawWith I x ρ f s ^ (2⁻¹ : ℝ) -
        (QuantumRuntime.mk D σ₀ s₀).outcomeLawWith I x ρ f s ^ (2⁻¹ : ℝ)) ≤
      (((∑ i ∈ t, b i : ℕ) : ℝ≥0∞) *
        ∑' i, (∑' r, ENNReal.ofReal (‖projDiff P V U W i r‖ ^ 2)) *
          (QuantumRuntime.mk D σ₀ s₀).queryMass I x (ρ.matrix ⊗ₖ σ₀.matrix) i) ^
        (2⁻¹ : ℝ) :=
  max_le
    (tsub_le_iff_left.2 (rpow_inv_two_outcomeLawWith_le_of_inImage_of_isQueryBound I hU hW hP hV
      hx t ht ρ f hs hVσ hPV h₀ h₁))
    (tsub_le_iff_left.2 (rpow_inv_two_outcomeLawWith_le_of_inImage_of_isQueryBound' I hU hW hP hV
      hx t ht ρ f hs hVσ hPV h₀ h₁))

/-- **ePrint 2025/2166, Lemma 5.7, for programs within a query budget**, in the squared form of
the paper: `(√p₀ - √p₁)² ≤ q · ∑ᵢ Cᵢ · mass i`, where `Cᵢ = ∑ᵣ ‖P̂ (V̂ Uᵢ V̂ᴴ - Wᵢ) P̂‖²` and
`mass i` is the total query mass of port `i` in the run against the first runtime. In `ℝ≥0∞`
the distance `|a - b|` is `max (a - b) (b - a)`. -/
theorem max_tsub_rpow_inv_two_outcomeLawWith_sq_le_of_inImage_of_isQueryBound {γ : Type*}
    [MeasurableSpace γ] {x : QuantumComp L spec X A} {b : spec.Port → ℕ} (hx : x.IsQueryBound b)
    (t : Finset spec.Port) (ht : ∀ i ∉ t, b i = 0) (ρ : SubState A) (f : (Σ u, X u) → γ)
    {s : Set γ} (hs : MeasurableSet s) (hVσ : MatrixMap.conj V σ₀.matrix = σ₀.matrix)
    (hPV : P * V = V * P)
    (h₀ : (QuantumRuntime.mk D σ₀ s₀).ForallQueries I (InImageAt P s₀) x
      (ρ.matrix ⊗ₖ σ₀.matrix))
    (h₁ : (QuantumRuntime.mk D σ₀ s₁).ForallQueries I (InImageAt P s₁) x
      (ρ.matrix ⊗ₖ σ₀.matrix)) :
    max ((QuantumRuntime.mk D σ₀ s₀).outcomeLawWith I x ρ f s ^ (2⁻¹ : ℝ) -
        (QuantumRuntime.mk D σ₀ s₁).outcomeLawWith I x ρ f s ^ (2⁻¹ : ℝ))
      ((QuantumRuntime.mk D σ₀ s₁).outcomeLawWith I x ρ f s ^ (2⁻¹ : ℝ) -
        (QuantumRuntime.mk D σ₀ s₀).outcomeLawWith I x ρ f s ^ (2⁻¹ : ℝ)) ^ 2 ≤
      ((∑ i ∈ t, b i : ℕ) : ℝ≥0∞) *
        ∑' i, (∑' r, ENNReal.ofReal (‖projDiff P V U W i r‖ ^ 2)) *
          (QuantumRuntime.mk D σ₀ s₀).queryMass I x (ρ.matrix ⊗ₖ σ₀.matrix) i :=
  sq_le_of_le_rpow_inv_two
    (max_tsub_rpow_inv_two_outcomeLawWith_le_of_inImage_of_isQueryBound I hU hW hP hV hx t ht ρ f
      hs hVσ hPV h₀ h₁)

end QuantumRuntime

end Quantum
