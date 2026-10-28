/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.Quantum.Comp.HybridProjected

/-!
# The square-root hybrid bound with the masses of a coherent index

In ePrint 2025/2166, §4.1–4.2, an emulated oracle is called coherently on an index register `I`:
it applies `U = ∑ᵢ |i⟩⟨i|_I ⊗ Uᵢ`, and the mass of the `j`-th query on the index `i` is
`mass(A, i, j) = ‖P_mass^(i) |ψ_j⟩‖²` with `P_mass^(i) = |i⟩⟨i|_I`. Lemma 5.7 then bounds the
change of the square root of the probability of an event by
`∑ⱼ √(∑ᵢ ‖P (V Uᵢ V† − Wᵢ) P‖² · mass(i, j))`: each index is charged the operator norm of the
change on its own block only.

This file proves the bounds of `VCVio.Quantum.Comp.Hybrid` and `VCVio.Quantum.Comp.HybridProjected`
in this form, for general programs (`Quantum.QuantumComp`) and general runtimes. The index is
not built into the model: a port whose input register carries an index is an ordinary port, and
the index is described by operators `B i k` on the input register of each port `i` and `B' i k`
on its output register. The masses are the index masses
`Quantum.QuantumRuntime.indexMassAt B` of `VCVio.Quantum.Comp.QueryMass`, which are query weights.
The single-port case is the paper's coherent index; one block per port with `B i k = 1` gives
back the classical-port bounds.

These index masses, of the projections onto the values of the index, are what the hybrid
argument of the paper needs. The bounds with the masses of the classical ports charge each call
the operator norm of the whole change, which can be strictly larger: for `U = 1` and
`W = diag(1, -1)` called from the index `0`, the blockwise bound is `0` and the whole-operator
bound is `2`.

## Hypotheses

* `Quantum.Hybrid.IsCoherentIndex B B'`: on every port, the `B i k` are idempotents adding up to
  the identity, and the `B' i k` have mutually orthogonal ranges. Orthogonal projections
  `|k⟩⟨k| ⊗ 1` onto the values of an index register satisfy it with `B' = B`.
* `Quantum.Hybrid.RespectsIndex B B' F`: every `F i r` sends the block `B i k ⊗ 1` into the block
  `B' i k ⊗ 1`. An operator `∑ₖ |k⟩⟨k| ⊗ Fₖ`, block diagonal in the index as in the paper,
  respects the index. Only the operators whose Kraus weights are bounded need to respect it: the
  difference `U - W`, or the operators `Quantum.Hybrid.lemmaKraus P V U W`, which respect it when
  `U` and `W` do (`Quantum.Hybrid.RespectsIndex.lemmaKraus`).

## The blockwise bound

For an operator `F` respecting the index and a positive semidefinite `σ`,
`tr (F σ Fᴴ) ≤ ∑ₖ ‖F B̂ₖ‖² · tr (B̂ₖ σ B̂ₖᴴ)` with `B̂ₖ = B k ⊗ 1`
(`Quantum.MatrixMap.re_trace_conj_le_sum_of_blocks`): the blocks of the output are orthogonal,
so the cross terms vanish, and each block is bounded by its own operator norm. Summed over the
Kraus operators and pushed through the query weights, this bounds the Kraus weights of the hybrid
by the index masses (`Quantum.QuantumRuntime.queryWeight_krausWeight_le_tsum_mul_indexMassAt`).

## Main statements

* `Quantum.QuantumRuntime.krausWeight_le_tsum_index`: the blockwise bound on a Kraus weight.
* `Quantum.QuantumRuntime.rpow_inv_two_tsum_trace_conj_run_le_indexMass` and
  `Quantum.QuantumRuntime.rpow_inv_two_outcomeLawWith_le_indexMass`: the square-root hybrid bound
  `∑ⱼ √(∑_{i,k} (∑ᵣ ‖(Uᵢ,ᵣ - Wᵢ,ᵣ) B̂ᵢ,ₖ‖²) · mass(⟨i, k⟩, j))`, per call;
  `Quantum.QuantumRuntime.rpow_inv_two_outcomeLawWith_le_indexMass_of_isQueryBound` with a query
  budget.
* `Quantum.QuantumRuntime.rpow_inv_two_outcomeLawWith_le_of_inImage_indexMass`: ePrint 2025/2166,
  Lemma 5.7, in the form of the paper, with the constants `‖P̂ (V̂ Uᵢ,ᵣ V̂ᴴ - Wᵢ,ᵣ) P̂ B̂ᵢ,ₖ‖²`;
  `Quantum.QuantumRuntime.rpow_inv_two_outcomeLawWith_le_of_inImage_indexMass_of_isQueryBound`
  with a query budget. Both bound `√p₀ - √p₁` with the index masses of the run against the first
  runtime; the primed forms bound `√p₁ - √p₀` with the same masses.
* `Quantum.QuantumRuntime.max_tsub_rpow_inv_two_outcomeLawWith_le_of_inImage_indexMass`: the
  two-sided statement `|√p₀ - √p₁| ≤ ∑ⱼ √(…)` of Lemma 5.7, with the masses of one run;
  with a query budget,
  `max_tsub_rpow_inv_two_outcomeLawWith_le_of_inImage_indexMass_of_isQueryBound`, and squared,
  as in the paper,
  `max_tsub_rpow_inv_two_outcomeLawWith_sq_le_of_inImage_indexMass_of_isQueryBound`.

The same bounds for Cor 5.8 are in `VCVio.Quantum.Comp.HybridMeasure`.
-/

public section

open IPFunctor Matrix
open scoped ENNReal ComplexOrder Kronecker

universe u v u₁ v₁ w

namespace Quantum

namespace Hybrid

/-! ## Blocks and commutation -/

/-- `A ⊗ 1` and `1 ⊗ X` commute: both products are `A ⊗ X`. -/
theorem kronecker_one_mul_one_kronecker {m n p q : Type*} [Fintype n] [DecidableEq n]
    [Fintype p] [DecidableEq p] [Fintype m] [DecidableEq m] [Fintype q] [DecidableEq q]
    (A : Matrix m n ℂ) (X : Matrix p q ℂ) :
    (A ⊗ₖ (1 : Matrix p p ℂ)) * ((1 : Matrix n n ℂ) ⊗ₖ X) =
      ((1 : Matrix m m ℂ) ⊗ₖ X) * (A ⊗ₖ (1 : Matrix q q ℂ)) := by
  rw [← mul_kronecker_mul, ← mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul, Matrix.one_mul,
    Matrix.mul_one]

section Blocks

variable {l m n n' : Type*} [Fintype l] [Fintype m] [Fintype n] [Fintype n']

/-- Sending a block into a block is preserved by a left factor that intertwines the blocks of
the output. -/
theorem mul_mul_eq_of_comm_left {Bo : Matrix l l ℂ} {L : Matrix l m ℂ} {Bm : Matrix m m ℂ}
    {F : Matrix m n ℂ} {Bi : Matrix n n ℂ} (hL : Bo * L = L * Bm) (h : Bm * F * Bi = F * Bi) :
    Bo * (L * F) * Bi = L * F * Bi := by
  calc Bo * (L * F) * Bi = L * (Bm * F * Bi) := by
        rw [← Matrix.mul_assoc, hL]
        simp only [Matrix.mul_assoc]
    _ = L * F * Bi := by rw [h, Matrix.mul_assoc]

/-- Sending a block into a block is preserved by a right factor that intertwines the blocks of
the input. -/
theorem mul_mul_eq_of_comm_right {Bo : Matrix m m ℂ} {F : Matrix m n ℂ} {Bi : Matrix n n ℂ}
    {R : Matrix n n' ℂ} {Bi' : Matrix n' n' ℂ} (hR : R * Bi' = Bi * R)
    (h : Bo * F * Bi = F * Bi) : Bo * (F * R) * Bi' = F * R * Bi' := by
  calc Bo * (F * R) * Bi' = Bo * F * Bi * R := by simp only [Matrix.mul_assoc, hR]
    _ = F * R * Bi' := by rw [h]; simp only [Matrix.mul_assoc, hR]

end Blocks

variable {spec : QuantumOracleSpec.{u₁, v₁}} {κ : spec.Port → Type*}

/-- **A coherent index** on the ports of a signature (ePrint 2025/2166, §4.1). For every port
`i`, operators `B i k` on its input register and `B' i k` on its output register, labelled by the
values `k : κ i` of the index, such that the `B i k` are idempotents adding up to the identity and
the `B' i k` have mutually orthogonal ranges. The orthogonal projections `|k⟩⟨k| ⊗ 1` onto the
values of an index register carried by the input and the output satisfy it with `B' = B`. -/
structure IsCoherentIndex [∀ i, Fintype (κ i)] (B : ∀ i, κ i → Matrix (spec.In i) (spec.In i) ℂ)
    (B' : ∀ i, κ i → Matrix (spec.Out i) (spec.Out i) ℂ) : Prop where
  /-- The input blocks of each port add up to the identity. -/
  sum_eq_one : ∀ i, ∑ k, B i k = 1
  /-- The input blocks are idempotents. -/
  mul_self : ∀ i k, B i k * B i k = B i k
  /-- The output blocks have mutually orthogonal ranges. -/
  conjTranspose_mul_of_ne : ∀ i a b, a ≠ b → (B' i b)ᴴ * B' i a = 0

/-- **Operators that respect a coherent index.** Every `F i r` sends the block `B i k ⊗ 1` of its
input into the block `B' i k ⊗ 1` of its output:
`(B' i k ⊗ 1) F i r (B i k ⊗ 1) = F i r (B i k ⊗ 1)`.
An operator `∑ₖ |k⟩⟨k| ⊗ Fₖ` that is block diagonal in the index, as the emulated oracles of
ePrint 2025/2166, §4.1, respects the projections `|k⟩⟨k| ⊗ 1`. -/
@[expose]
def RespectsIndex (B : ∀ i, κ i → Matrix (spec.In i) (spec.In i) ℂ)
    (B' : ∀ i, κ i → Matrix (spec.Out i) (spec.Out i) ℂ) {D : Type*} [Fintype D] [DecidableEq D]
    (F : ∀ i, spec.Result i → Matrix (spec.Out i × D) (spec.In i × D) ℂ) : Prop :=
  ∀ i r k, (B' i k ⊗ₖ (1 : Matrix D D ℂ)) * F i r * (B i k ⊗ₖ (1 : Matrix D D ℂ)) =
    F i r * (B i k ⊗ₖ (1 : Matrix D D ℂ))

variable {B : ∀ i, κ i → Matrix (spec.In i) (spec.In i) ℂ}
  {B' : ∀ i, κ i → Matrix (spec.Out i) (spec.Out i) ℂ}

section Respects

variable {D : Type*} [Fintype D] [DecidableEq D]
  {F G : ∀ i, spec.Result i → Matrix (spec.Out i × D) (spec.In i × D) ℂ}

/-- Respecting an index is preserved by sums. -/
theorem RespectsIndex.add (hF : RespectsIndex B B' F) (hG : RespectsIndex B B' G) :
    RespectsIndex B B' fun i r ↦ F i r + G i r := fun i r k ↦ by
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.add_mul, hF i r k, hG i r k]

/-- Respecting an index is preserved by differences. -/
theorem RespectsIndex.sub (hF : RespectsIndex B B' F) (hG : RespectsIndex B B' G) :
    RespectsIndex B B' fun i r ↦ F i r - G i r := fun i r k ↦ by
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.sub_mul, hF i r k, hG i r k]

/-- Respecting an index is preserved by operators `1 ⊗ X` on the runtime register, on both
sides. -/
theorem RespectsIndex.one_kronecker_mul_mul (hF : RespectsIndex B B' F) (X Y : Matrix D D ℂ) :
    RespectsIndex B B' fun i r ↦
      ((1 : Matrix (spec.Out i) (spec.Out i) ℂ) ⊗ₖ X) * F i r *
        ((1 : Matrix (spec.In i) (spec.In i) ℂ) ⊗ₖ Y) := fun i r k ↦
  mul_mul_eq_of_comm_right (kronecker_one_mul_one_kronecker (B i k) Y).symm
    (mul_mul_eq_of_comm_left (kronecker_one_mul_one_kronecker (B' i k) X) (hF i r k))

/-- The operators `V̂ P̂ U P̂ - P̂ W P̂ V̂` of the general hybrid bound respect a coherent index
when `U` and `W` do: operators `1 ⊗ X` on the runtime register commute with the blocks. -/
theorem RespectsIndex.lemmaKraus {D : QReg}
    {U W : ∀ i, spec.Result i → Matrix (spec.Out i × D) (spec.In i × D) ℂ}
    (hU : RespectsIndex B B' U) (hW : RespectsIndex B B' W) (P V : Matrix D D ℂ) :
    RespectsIndex B B' (lemmaKraus P V U W) := fun i r k ↦ by
  have h₁ := (hU.one_kronecker_mul_mul P P) i r k
  have h₂ := (hW.one_kronecker_mul_mul P P) i r k
  simp only at h₁ h₂
  rw [Hybrid.lemmaKraus, Matrix.mul_sub, Matrix.sub_mul, Matrix.sub_mul,
    mul_mul_eq_of_comm_left (kronecker_one_mul_one_kronecker (B' i k) V) h₁,
    mul_mul_eq_of_comm_right (kronecker_one_mul_one_kronecker (B i k) V).symm h₂]

end Respects

section Kronecker

variable [∀ i, Fintype (κ i)] {D : Type*} [Fintype D] [DecidableEq D]

omit [Fintype D] in
/-- The input blocks of a coherent index, on the input and the runtime register, add up to the
identity. -/
theorem IsCoherentIndex.sum_kronecker_one (hB : IsCoherentIndex B B') (i : spec.Port) :
    ∑ k, B i k ⊗ₖ (1 : Matrix D D ℂ) = 1 := by
  rw [← one_kronecker_one, ← hB.sum_eq_one i]
  ext ⟨a, b⟩ ⟨c, d⟩
  simp [Matrix.sum_apply, Finset.sum_mul]

/-- The input blocks of a coherent index, on the input and the runtime register, are
idempotents. -/
theorem IsCoherentIndex.kronecker_one_mul_self (hB : IsCoherentIndex B B') (i : spec.Port)
    (k : κ i) :
    (B i k ⊗ₖ (1 : Matrix D D ℂ)) * (B i k ⊗ₖ (1 : Matrix D D ℂ)) = B i k ⊗ₖ (1 : Matrix D D ℂ) :=
  by rw [← mul_kronecker_mul, hB.mul_self i k, Matrix.one_mul]

/-- The output blocks of a coherent index, on the output and the runtime register, have mutually
orthogonal ranges. -/
theorem IsCoherentIndex.conjTranspose_kronecker_one_mul_of_ne (hB : IsCoherentIndex B B')
    (i : spec.Port) {a b : κ i} (hab : a ≠ b) :
    (B' i b ⊗ₖ (1 : Matrix D D ℂ))ᴴ * (B' i a ⊗ₖ (1 : Matrix D D ℂ)) = 0 := by
  rw [conjTranspose_kronecker, conjTranspose_one, ← mul_kronecker_mul,
    hB.conjTranspose_mul_of_ne i a b hab, zero_kronecker]

end Kronecker

end Hybrid

namespace QuantumRuntime

open Hybrid

variable {spec : QuantumOracleSpec.{u₁, v₁}} {L : LocalSig.{u, v}} (I : L.Interp)
  {X : QReg → Type w} {A : QReg} {κ : spec.Port → Type*} [∀ i, Fintype (κ i)]
  {B : ∀ i, κ i → Matrix (spec.In i) (spec.In i) ℂ}
  {B' : ∀ i, κ i → Matrix (spec.Out i) (spec.Out i) ℂ}

/-! ## Kraus weights by index masses -/

section L2Operator

open scoped Matrix.Norms.L2Operator

omit [∀ i, Fintype (κ i)] in
/-- The constants of the blockwise bound, summed over the blocks of a port and against the
weights of the blocks. -/
private theorem tsum_tsum_mul_comm {ι K : Type*} (a : ι → K → ℝ≥0∞) (b : K → ℝ≥0∞) :
    ∑' r, ∑' k, a r k * b k = ∑' k, (∑' r, a r k) * b k := by
  rw [ENNReal.tsum_comm]
  simp only [ENNReal.tsum_mul_right]

/-- **Kraus weights block by block.** For an operator family `F` respecting a coherent index,
the Kraus weight of an input `σ` of a call of port `i` is at most
`∑ₖ (∑ᵣ ‖F i r (B i k ⊗ 1)‖²) · tr ((B i k ⊗ 1) σ (B i k ⊗ 1)ᴴ)`. -/
theorem krausWeight_le_tsum_index {D : QReg} (hB : IsCoherentIndex B B')
    {F : ∀ i, spec.Result i → Matrix (spec.Out i × D) (spec.In i × D) ℂ}
    (hF : RespectsIndex B B' F) (i : spec.Port) {σ : Matrix (spec.In i × D) (spec.In i × D) ℂ}
    (hσ : σ.PosSemidef) :
    krausWeight F i σ ≤ ∑' k, (∑' r, ENNReal.ofReal (‖F i r * (B i k ⊗ₖ (1 : Matrix D D ℂ))‖ ^ 2)) *
      ENNReal.ofReal (MatrixMap.conj (B i k ⊗ₖ (1 : Matrix D D ℂ)) σ).trace.re := by
  rw [krausWeight, ← tsum_tsum_mul_comm]
  refine ENNReal.tsum_le_tsum fun r ↦ ?_
  rw [tsum_fintype]
  exact MatrixMap.ofReal_trace_conj_le_sum_of_blocks (F i r) (hB.sum_kronecker_one i)
    (hB.kronecker_one_mul_self i) (fun a b hab ↦ hB.conjTranspose_kronecker_one_mul_of_ne i hab)
    (hF i r) hσ

/-- **Kraus weights by index masses.** For an operator family `F` respecting a coherent index,
the Kraus weight of the `j`-th call is at most the index masses of the `j`-th call weighted by
`∑ᵣ ‖F i r (B i k ⊗ 1)‖²`. -/
theorem queryWeight_krausWeight_le_tsum_mul_indexMassAt (R : QuantumRuntime spec)
    (hB : IsCoherentIndex B B')
    {F : ∀ i, spec.Result i → Matrix (spec.Out i × R.D) (spec.In i × R.D) ℂ}
    (hF : RespectsIndex B B' F) (x : QuantumComp L spec X A)
    {ρ : Matrix (A × R.D) (A × R.D) ℂ} (hρ : ρ.PosSemidef) (j : ℕ) :
    R.queryWeight I (krausWeight F) x ρ j ≤
      ∑' c, (∑' r, ENNReal.ofReal (‖F c.1 r * (B c.1 c.2 ⊗ₖ (1 : Matrix R.D R.D ℂ))‖ ^ 2)) *
        R.indexMassAt I B x ρ c j :=
  R.queryWeight_le_tsum_mul_indexMassAt I B
    (fun c ↦ ∑' r, ENNReal.ofReal (‖F c.1 r * (B c.1 c.2 ⊗ₖ (1 : Matrix R.D R.D ℂ))‖ ^ 2))
    (fun i _ hσ ↦ krausWeight_le_tsum_index hB hF i hσ) x hρ j

/-- **Summed Kraus weights by total index masses.** -/
theorem tsum_queryWeight_krausWeight_le_tsum_mul_indexMass (R : QuantumRuntime spec)
    (hB : IsCoherentIndex B B')
    {F : ∀ i, spec.Result i → Matrix (spec.Out i × R.D) (spec.In i × R.D) ℂ}
    (hF : RespectsIndex B B' F) (x : QuantumComp L spec X A)
    {ρ : Matrix (A × R.D) (A × R.D) ℂ} (hρ : ρ.PosSemidef) :
    ∑' j, R.queryWeight I (krausWeight F) x ρ j ≤
      ∑' c, (∑' r, ENNReal.ofReal (‖F c.1 r * (B c.1 c.2 ⊗ₖ (1 : Matrix R.D R.D ℂ))‖ ^ 2)) *
        R.indexMass I B x ρ c :=
  R.tsum_queryWeight_le_tsum_mul_indexMass I B
    (fun c ↦ ∑' r, ENNReal.ofReal (‖F c.1 r * (B c.1 c.2 ⊗ₖ (1 : Matrix R.D R.D ℂ))‖ ^ 2))
    (fun i _ hσ ↦ krausWeight_le_tsum_index hB hF i hσ) x hρ

end L2Operator

/-! ## The square-root hybrid bound -/

section Bound

open scoped Matrix.Norms.L2Operator

variable {D : QReg} {s₀ s₁ : ∀ i, SubInstrument (spec.In i × D) (spec.Out i × D) (spec.Result i)}
  {U W : ∀ i, spec.Result i → Matrix (spec.Out i × D) (spec.In i × D) ℂ}
  (σ₀ σ₁ : SubState D)
  (hU : ∀ i r, (s₀ i).branch r = MatrixMap.conj (U i r))
  (hW : ∀ i r, (s₁ i).branch r = MatrixMap.conj (W i r))
  (hB : IsCoherentIndex B B')
include hU hW hB

/-- **The square-root hybrid bound with the masses of a coherent index** (ePrint 2025/2166,
Lemma 5.7 with the masses of §4.2, for general programs). Under the hypotheses of
`Quantum.QuantumRuntime.rpow_inv_two_tsum_trace_conj_run_le`, if the differences `U i r - W i r`
respect a coherent index `B, B'`, the sum over the calls is at most
`∑ⱼ √(∑_{i,k} (∑ᵣ ‖(U i r - W i r) (B i k ⊗ 1)‖²) · mass(⟨i, k⟩, j))` with the index masses of the
run against the first runtime: each block is charged the norm of the change on that block only. -/
theorem rpow_inv_two_tsum_trace_conj_run_le_indexMass
    (hUW : RespectsIndex B B' fun i r ↦ U i r - W i r) (x : QuantumComp L spec X A)
    {Z : (Σ u, X u) → Type*} [∀ p, Fintype (Z p)] (O : ∀ p : Σ u, X u, Matrix (Z p) (p.1 × D) ℂ)
    (hO : ∀ p, (1 - (O p)ᴴ * O p).PosSemidef) {ρ : Matrix (A × D) (A × D) ℂ}
    (hρ : ρ.PosSemidef) :
    (∑' p, ENNReal.ofReal (MatrixMap.conj (O p)
        (((QuantumRuntime.mk D σ₀ s₀).run I x).branch p ρ)).trace.re) ^ (2⁻¹ : ℝ) ≤
      (∑' p, ENNReal.ofReal (MatrixMap.conj (O p)
          (((QuantumRuntime.mk D σ₁ s₁).run I x).branch p ρ)).trace.re) ^ (2⁻¹ : ℝ) +
        ∑' j, (∑' c, (∑' r, ENNReal.ofReal
          (‖(U c.1 r - W c.1 r) * (B c.1 c.2 ⊗ₖ (1 : Matrix D D ℂ))‖ ^ 2)) *
            (QuantumRuntime.mk D σ₀ s₀).indexMassAt I B x ρ c j) ^ (2⁻¹ : ℝ) :=
  (rpow_inv_two_tsum_trace_conj_run_le I σ₀ σ₁ hU hW x O hO hρ).trans <| add_le_add le_rfl <|
    ENNReal.tsum_le_tsum fun j ↦ ENNReal.rpow_le_rpow
      ((QuantumRuntime.mk D σ₀ s₀).queryWeight_krausWeight_le_tsum_mul_indexMassAt I hB hUW x hρ
        j) (by norm_num)

/-- **The square-root hybrid bound for events, with the masses of a coherent index** (ePrint
2025/2166, Lemma 5.7 with the masses of §4.2, for general programs and `P = V = 1`): the square
roots of the laws of any observation of the leaves differ, on every measurable set, by at most
`∑ⱼ √(∑_{i,k} (∑ᵣ ‖(U i r - W i r) (B i k ⊗ 1)‖²) · mass(⟨i, k⟩, j))`. -/
theorem rpow_inv_two_outcomeLawWith_le_indexMass
    (hUW : RespectsIndex B B' fun i r ↦ U i r - W i r) {γ : Type*} [MeasurableSpace γ]
    (x : QuantumComp L spec X A) (ρ : SubState A) (f : (Σ u, X u) → γ) {s : Set γ}
    (hs : MeasurableSet s) :
    (QuantumRuntime.mk D σ₀ s₀).evalDistMap I x ρ f s ^ (2⁻¹ : ℝ) ≤
      (QuantumRuntime.mk D σ₀ s₁).evalDistMap I x ρ f s ^ (2⁻¹ : ℝ) +
        ∑' j, (∑' c, (∑' r, ENNReal.ofReal
          (‖(U c.1 r - W c.1 r) * (B c.1 c.2 ⊗ₖ (1 : Matrix D D ℂ))‖ ^ 2)) *
            (QuantumRuntime.mk D σ₀ s₀).indexMassAt I B x (ρ.matrix ⊗ₖ σ₀.matrix) c j) ^
          (2⁻¹ : ℝ) :=
  (rpow_inv_two_outcomeLawWith_le I σ₀ hU hW x ρ f hs).trans <| add_le_add le_rfl <|
    ENNReal.tsum_le_tsum fun j ↦ ENNReal.rpow_le_rpow
      ((QuantumRuntime.mk D σ₀ s₀).queryWeight_krausWeight_le_tsum_mul_indexMassAt I hB hUW x
        (ρ.prod σ₀).posSemidef j) (by norm_num)

/-- **The square-root hybrid bound for events, with the masses of a coherent index, for programs
within a query budget**: with at most `q = ∑ i ∈ t, b i` calls, the sum over the calls is at most
`√(q · ∑_{i,k} Cᵢ,ₖ · TotalMass(⟨i, k⟩))`, `Cᵢ,ₖ = ∑ᵣ ‖(U i r - W i r) (B i k ⊗ 1)‖²`. -/
theorem rpow_inv_two_outcomeLawWith_le_indexMass_of_isQueryBound
    (hUW : RespectsIndex B B' fun i r ↦ U i r - W i r) {γ : Type*} [MeasurableSpace γ]
    {x : QuantumComp L spec X A} {b : spec.Port → ℕ} (hx : x.IsQueryBound b)
    (t : Finset spec.Port) (ht : ∀ i ∉ t, b i = 0) (ρ : SubState A) (f : (Σ u, X u) → γ)
    {s : Set γ} (hs : MeasurableSet s) :
    (QuantumRuntime.mk D σ₀ s₀).evalDistMap I x ρ f s ^ (2⁻¹ : ℝ) ≤
      (QuantumRuntime.mk D σ₀ s₁).evalDistMap I x ρ f s ^ (2⁻¹ : ℝ) +
        (((∑ i ∈ t, b i : ℕ) : ℝ≥0∞) * ∑' c, (∑' r, ENNReal.ofReal
          (‖(U c.1 r - W c.1 r) * (B c.1 c.2 ⊗ₖ (1 : Matrix D D ℂ))‖ ^ 2)) *
            (QuantumRuntime.mk D σ₀ s₀).indexMass I B x (ρ.matrix ⊗ₖ σ₀.matrix) c) ^
          (2⁻¹ : ℝ) := by
  refine (rpow_inv_two_outcomeLawWith_le I σ₀ hU hW x ρ f hs).trans (add_le_add le_rfl ?_)
  refine (tsum_rpow_inv_two_queryWeight_le_of_isQueryBound I _ hx t ht _).trans ?_
  gcongr
  exact (QuantumRuntime.mk D σ₀ s₀).tsum_queryWeight_krausWeight_le_tsum_mul_indexMass I hB hUW x
    (ρ.prod σ₀).posSemidef

end Bound

/-! ## The square-root hybrid bound with a projector and an isometry -/

section Projected

open scoped Matrix.Norms.L2Operator

variable {D : QReg} {s₀ s₁ : ∀ i, SubInstrument (spec.In i × D) (spec.Out i × D) (spec.Result i)}
  {U W : ∀ i, spec.Result i → Matrix (spec.Out i × D) (spec.In i × D) ℂ}
  {σ₀ : SubState D}
  (hU : ∀ i r, (s₀ i).branch r = MatrixMap.conj (U i r))
  (hW : ∀ i r, (s₁ i).branch r = MatrixMap.conj (W i r))
  {P V : Matrix D D ℂ} (hP : (1 - Pᴴ * P).PosSemidef) (hV : Vᴴ * V = 1)
  (hB : IsCoherentIndex B B')

omit [∀ i, Fintype (κ i)] in
/-- Under condition 3 and for a unitary `V`, the operators `lemmaKraus P V U W` have, on each
block of the input, the operator norms of `P̂ (V̂ U V̂ᴴ - W) P̂` on that block. -/
private theorem l2_opNorm_lemmaKraus_mul_kronecker_one (hV : Vᴴ * V = 1) (hPV : P * V = V * P)
    (i : spec.Port) (r : spec.Result i) (k : κ i) :
    ‖lemmaKraus P V U W i r * (B i k ⊗ₖ (1 : Matrix D D ℂ))‖ =
      ‖projDiff P V U W i r * (B i k ⊗ₖ (1 : Matrix D D ℂ))‖ := by
  rw [lemmaKraus_eq_projDiff_mul hV hPV, Matrix.mul_assoc,
    ← kronecker_one_mul_one_kronecker (B i k) V, ← Matrix.mul_assoc,
    MatrixMap.l2_opNorm_mul_coisometry
      (one_kronecker_mul_conjTranspose (_root_.mul_eq_one_comm.mp hV))]

include hV hB in
/-- The Kraus weights of `lemmaKraus P V U W` on the calls of a run, under condition 3 and when
they respect a coherent index, by the index masses of that run. -/
private theorem tsum_rpow_queryWeight_lemmaKraus_le_indexMass (hPV : P * V = V * P)
    (hK : RespectsIndex B B' (lemmaKraus P V U W)) (x : QuantumComp L spec X A)
    (ρ : SubState A) :
    ∑' j, (QuantumRuntime.mk D σ₀ s₀).queryWeight I (krausWeight (lemmaKraus P V U W)) x
        (ρ.matrix ⊗ₖ σ₀.matrix) j ^ (2⁻¹ : ℝ) ≤
      ∑' j, (∑' c, (∑' r, ENNReal.ofReal
          (‖projDiff P V U W c.1 r * (B c.1 c.2 ⊗ₖ (1 : Matrix D D ℂ))‖ ^ 2)) *
            (QuantumRuntime.mk D σ₀ s₀).indexMassAt I B x (ρ.matrix ⊗ₖ σ₀.matrix) c j) ^
          (2⁻¹ : ℝ) :=
  ENNReal.tsum_le_tsum fun j ↦ ENNReal.rpow_le_rpow
    (((QuantumRuntime.mk D σ₀ s₀).queryWeight_krausWeight_le_tsum_mul_indexMassAt I hB hK x
      (ρ := ρ.matrix ⊗ₖ σ₀.matrix) (ρ.prod σ₀).posSemidef j).trans_eq
        (by simp only [l2_opNorm_lemmaKraus_mul_kronecker_one hV hPV])) (by norm_num)

include hV hB in
/-- The Kraus weights of `lemmaKraus P V U W` on the calls of a run within a query budget, under
condition 3 and when they respect a coherent index, by the total index masses of that run. -/
private theorem tsum_rpow_queryWeight_lemmaKraus_le_indexMass_of_isQueryBound
    (hPV : P * V = V * P) (hK : RespectsIndex B B' (lemmaKraus P V U W))
    {x : QuantumComp L spec X A} {b : spec.Port → ℕ} (hx : x.IsQueryBound b)
    (t : Finset spec.Port) (ht : ∀ i ∉ t, b i = 0) (ρ : SubState A) :
    ∑' j, (QuantumRuntime.mk D σ₀ s₀).queryWeight I (krausWeight (lemmaKraus P V U W)) x
        (ρ.matrix ⊗ₖ σ₀.matrix) j ^ (2⁻¹ : ℝ) ≤
      (((∑ i ∈ t, b i : ℕ) : ℝ≥0∞) * ∑' c, (∑' r, ENNReal.ofReal
          (‖projDiff P V U W c.1 r * (B c.1 c.2 ⊗ₖ (1 : Matrix D D ℂ))‖ ^ 2)) *
            (QuantumRuntime.mk D σ₀ s₀).indexMass I B x (ρ.matrix ⊗ₖ σ₀.matrix) c) ^
          (2⁻¹ : ℝ) := by
  refine (tsum_rpow_inv_two_queryWeight_le_of_isQueryBound I _ hx t ht _).trans ?_
  gcongr
  refine ((QuantumRuntime.mk D σ₀ s₀).tsum_queryWeight_krausWeight_le_tsum_mul_indexMass I hB hK x
    (ρ := ρ.matrix ⊗ₖ σ₀.matrix) (ρ.prod σ₀).posSemidef).trans_eq ?_
  simp only [l2_opNorm_lemmaKraus_mul_kronecker_one hV hPV]

include hU hW hP hV hB

/-- **ePrint 2025/2166, Lemma 5.7, in the form of the paper** (with the masses of a coherent
index, §4.1–4.2, for general programs). Under conditions 1 to 3 for a contraction `P` and a
unitary `V`, if the operators `lemmaKraus P V U W` respect a coherent index `B, B'` (as they do
when `U` and `W` respect it, `Quantum.Hybrid.RespectsIndex.lemmaKraus`), the square root of the
probability of an event against the first runtime exceeds the one against the second by at most
`∑ⱼ √(∑_{i,k} (∑ᵣ ‖P̂ (V̂ Uᵢ,ᵣ V̂ᴴ - Wᵢ,ᵣ) P̂ (B i k ⊗ 1)‖²) · mass(⟨i, k⟩, j))`, with the index
masses of the run against the first runtime. For the paper's emulated oracles `B i k` projects
the index register onto `k`, and the constant is the norm of the change on the block `k`.

This is one direction. The converse, with the same masses of the run against the first runtime,
is `Quantum.QuantumRuntime.rpow_inv_two_outcomeLawWith_le_of_inImage_indexMass'`, and the
two-sided form of the paper is
`Quantum.QuantumRuntime.max_tsub_rpow_inv_two_outcomeLawWith_le_of_inImage_indexMass`. -/
theorem rpow_inv_two_outcomeLawWith_le_of_inImage_indexMass {γ : Type*} [MeasurableSpace γ]
    (x : QuantumComp L spec X A) (ρ : SubState A) (f : (Σ u, X u) → γ) {s : Set γ}
    (hs : MeasurableSet s) (hVσ : MatrixMap.conj V σ₀.matrix = σ₀.matrix)
    (hPV : P * V = V * P) (hK : RespectsIndex B B' (lemmaKraus P V U W))
    (h₀ : (QuantumRuntime.mk D σ₀ s₀).ForallQueries I (InImageAt P s₀) x
      (ρ.matrix ⊗ₖ σ₀.matrix))
    (h₁ : (QuantumRuntime.mk D σ₀ s₁).ForallQueries I (InImageAt P s₁) x
      (ρ.matrix ⊗ₖ σ₀.matrix)) :
    (QuantumRuntime.mk D σ₀ s₀).evalDistMap I x ρ f s ^ (2⁻¹ : ℝ) ≤
      (QuantumRuntime.mk D σ₀ s₁).evalDistMap I x ρ f s ^ (2⁻¹ : ℝ) +
        ∑' j, (∑' c, (∑' r, ENNReal.ofReal
          (‖projDiff P V U W c.1 r * (B c.1 c.2 ⊗ₖ (1 : Matrix D D ℂ))‖ ^ 2)) *
            (QuantumRuntime.mk D σ₀ s₀).indexMassAt I B x (ρ.matrix ⊗ₖ σ₀.matrix) c j) ^
          (2⁻¹ : ℝ) :=
  (rpow_inv_two_outcomeLawWith_le_of_inImage I hU hW hP hV x ρ f hs hVσ h₀ h₁).trans <|
    add_le_add le_rfl <| tsum_rpow_queryWeight_lemmaKraus_le_indexMass I hV hB hPV hK x ρ

/-- **ePrint 2025/2166, Lemma 5.7, in the form of the paper**, converse direction: under the
hypotheses of `Quantum.QuantumRuntime.rpow_inv_two_outcomeLawWith_le_of_inImage_indexMass`, the
square root of the probability of an event against the second runtime exceeds the one against
the first by at most the same
`∑ⱼ √(∑_{i,k} (∑ᵣ ‖P̂ (V̂ Uᵢ,ᵣ V̂ᴴ - Wᵢ,ᵣ) P̂ (B i k ⊗ 1)‖²) · mass(⟨i, k⟩, j))`, with the index
masses of the run against the first runtime. -/
theorem rpow_inv_two_outcomeLawWith_le_of_inImage_indexMass' {γ : Type*} [MeasurableSpace γ]
    (x : QuantumComp L spec X A) (ρ : SubState A) (f : (Σ u, X u) → γ) {s : Set γ}
    (hs : MeasurableSet s) (hVσ : MatrixMap.conj V σ₀.matrix = σ₀.matrix)
    (hPV : P * V = V * P) (hK : RespectsIndex B B' (lemmaKraus P V U W))
    (h₀ : (QuantumRuntime.mk D σ₀ s₀).ForallQueries I (InImageAt P s₀) x
      (ρ.matrix ⊗ₖ σ₀.matrix))
    (h₁ : (QuantumRuntime.mk D σ₀ s₁).ForallQueries I (InImageAt P s₁) x
      (ρ.matrix ⊗ₖ σ₀.matrix)) :
    (QuantumRuntime.mk D σ₀ s₁).evalDistMap I x ρ f s ^ (2⁻¹ : ℝ) ≤
      (QuantumRuntime.mk D σ₀ s₀).evalDistMap I x ρ f s ^ (2⁻¹ : ℝ) +
        ∑' j, (∑' c, (∑' r, ENNReal.ofReal
          (‖projDiff P V U W c.1 r * (B c.1 c.2 ⊗ₖ (1 : Matrix D D ℂ))‖ ^ 2)) *
            (QuantumRuntime.mk D σ₀ s₀).indexMassAt I B x (ρ.matrix ⊗ₖ σ₀.matrix) c j) ^
          (2⁻¹ : ℝ) :=
  (rpow_inv_two_outcomeLawWith_le_of_inImage' I hU hW hP hV x ρ f hs hVσ h₀ h₁).trans <|
    add_le_add le_rfl <| tsum_rpow_queryWeight_lemmaKraus_le_indexMass I hV hB hPV hK x ρ

/-- **ePrint 2025/2166, Lemma 5.7, in the form of the paper**, two-sided: under the hypotheses of
`Quantum.QuantumRuntime.rpow_inv_two_outcomeLawWith_le_of_inImage_indexMass`, the probabilities
`p₀` and `p₁` of an event against the two runtimes satisfy
`|√p₀ - √p₁| ≤ ∑ⱼ √(∑_{i,k} (∑ᵣ ‖P̂ (V̂ Uᵢ,ᵣ V̂ᴴ - Wᵢ,ᵣ) P̂ (B i k ⊗ 1)‖²) · mass(⟨i, k⟩, j))`,
with the index masses of the run against the first runtime only, as in the paper. In `ℝ≥0∞`
the distance `|a - b|` is `max (a - b) (b - a)`. -/
theorem max_tsub_rpow_inv_two_outcomeLawWith_le_of_inImage_indexMass {γ : Type*}
    [MeasurableSpace γ] (x : QuantumComp L spec X A) (ρ : SubState A) (f : (Σ u, X u) → γ)
    {s : Set γ}
    (hs : MeasurableSet s) (hVσ : MatrixMap.conj V σ₀.matrix = σ₀.matrix)
    (hPV : P * V = V * P) (hK : RespectsIndex B B' (lemmaKraus P V U W))
    (h₀ : (QuantumRuntime.mk D σ₀ s₀).ForallQueries I (InImageAt P s₀) x
      (ρ.matrix ⊗ₖ σ₀.matrix))
    (h₁ : (QuantumRuntime.mk D σ₀ s₁).ForallQueries I (InImageAt P s₁) x
      (ρ.matrix ⊗ₖ σ₀.matrix)) :
    max ((QuantumRuntime.mk D σ₀ s₀).evalDistMap I x ρ f s ^ (2⁻¹ : ℝ) -
        (QuantumRuntime.mk D σ₀ s₁).evalDistMap I x ρ f s ^ (2⁻¹ : ℝ))
      ((QuantumRuntime.mk D σ₀ s₁).evalDistMap I x ρ f s ^ (2⁻¹ : ℝ) -
        (QuantumRuntime.mk D σ₀ s₀).evalDistMap I x ρ f s ^ (2⁻¹ : ℝ)) ≤
      ∑' j, (∑' c, (∑' r, ENNReal.ofReal
          (‖projDiff P V U W c.1 r * (B c.1 c.2 ⊗ₖ (1 : Matrix D D ℂ))‖ ^ 2)) *
            (QuantumRuntime.mk D σ₀ s₀).indexMassAt I B x (ρ.matrix ⊗ₖ σ₀.matrix) c j) ^
          (2⁻¹ : ℝ) :=
  max_le
    (tsub_le_iff_left.2 (rpow_inv_two_outcomeLawWith_le_of_inImage_indexMass I hU hW hP hV hB x
      ρ f hs hVσ hPV hK h₀ h₁))
    (tsub_le_iff_left.2 (rpow_inv_two_outcomeLawWith_le_of_inImage_indexMass' I hU hW hP hV hB x
      ρ f hs hVσ hPV hK h₀ h₁))

/-- **ePrint 2025/2166, Lemma 5.7, in the form of the paper, for programs within a query
budget**: with at most `q = ∑ i ∈ t, b i` calls, the square root of the probability of an event
against the first runtime exceeds the one against the second by at most
`√(q · ∑_{i,k} Cᵢ,ₖ · TotalMass(⟨i, k⟩))`, `Cᵢ,ₖ = ∑ᵣ ‖P̂ (V̂ Uᵢ,ᵣ V̂ᴴ - Wᵢ,ᵣ) P̂ (B i k ⊗ 1)‖²`,
with the total index masses of the run against the first runtime. The converse, with the same
masses, is `rpow_inv_two_outcomeLawWith_le_of_inImage_indexMass_of_isQueryBound'`; the
two-sided form is `max_tsub_rpow_inv_two_outcomeLawWith_le_of_inImage_indexMass_of_isQueryBound`
and the squared form of the paper is
`max_tsub_rpow_inv_two_outcomeLawWith_sq_le_of_inImage_indexMass_of_isQueryBound`, all in
`Quantum.QuantumRuntime`. -/
theorem rpow_inv_two_outcomeLawWith_le_of_inImage_indexMass_of_isQueryBound {γ : Type*}
    [MeasurableSpace γ] {x : QuantumComp L spec X A} {b : spec.Port → ℕ} (hx : x.IsQueryBound b)
    (t : Finset spec.Port) (ht : ∀ i ∉ t, b i = 0) (ρ : SubState A) (f : (Σ u, X u) → γ)
    {s : Set γ} (hs : MeasurableSet s) (hVσ : MatrixMap.conj V σ₀.matrix = σ₀.matrix)
    (hPV : P * V = V * P) (hK : RespectsIndex B B' (lemmaKraus P V U W))
    (h₀ : (QuantumRuntime.mk D σ₀ s₀).ForallQueries I (InImageAt P s₀) x
      (ρ.matrix ⊗ₖ σ₀.matrix))
    (h₁ : (QuantumRuntime.mk D σ₀ s₁).ForallQueries I (InImageAt P s₁) x
      (ρ.matrix ⊗ₖ σ₀.matrix)) :
    (QuantumRuntime.mk D σ₀ s₀).evalDistMap I x ρ f s ^ (2⁻¹ : ℝ) ≤
      (QuantumRuntime.mk D σ₀ s₁).evalDistMap I x ρ f s ^ (2⁻¹ : ℝ) +
        (((∑ i ∈ t, b i : ℕ) : ℝ≥0∞) * ∑' c, (∑' r, ENNReal.ofReal
          (‖projDiff P V U W c.1 r * (B c.1 c.2 ⊗ₖ (1 : Matrix D D ℂ))‖ ^ 2)) *
            (QuantumRuntime.mk D σ₀ s₀).indexMass I B x (ρ.matrix ⊗ₖ σ₀.matrix) c) ^
          (2⁻¹ : ℝ) :=
  (rpow_inv_two_outcomeLawWith_le_of_inImage I hU hW hP hV x ρ f hs hVσ h₀ h₁).trans <|
    add_le_add le_rfl <|
      tsum_rpow_queryWeight_lemmaKraus_le_indexMass_of_isQueryBound I hV hB hPV hK hx t ht ρ

/-- **ePrint 2025/2166, Lemma 5.7, in the form of the paper, for programs within a query
budget**, converse direction: the square root of the probability of an event against the second
runtime exceeds the one against the first by at most the same
`√(q · ∑_{i,k} Cᵢ,ₖ · TotalMass(⟨i, k⟩))`, with the total index masses of the run against the
first runtime. -/
theorem rpow_inv_two_outcomeLawWith_le_of_inImage_indexMass_of_isQueryBound' {γ : Type*}
    [MeasurableSpace γ] {x : QuantumComp L spec X A} {b : spec.Port → ℕ} (hx : x.IsQueryBound b)
    (t : Finset spec.Port) (ht : ∀ i ∉ t, b i = 0) (ρ : SubState A) (f : (Σ u, X u) → γ)
    {s : Set γ} (hs : MeasurableSet s) (hVσ : MatrixMap.conj V σ₀.matrix = σ₀.matrix)
    (hPV : P * V = V * P) (hK : RespectsIndex B B' (lemmaKraus P V U W))
    (h₀ : (QuantumRuntime.mk D σ₀ s₀).ForallQueries I (InImageAt P s₀) x
      (ρ.matrix ⊗ₖ σ₀.matrix))
    (h₁ : (QuantumRuntime.mk D σ₀ s₁).ForallQueries I (InImageAt P s₁) x
      (ρ.matrix ⊗ₖ σ₀.matrix)) :
    (QuantumRuntime.mk D σ₀ s₁).evalDistMap I x ρ f s ^ (2⁻¹ : ℝ) ≤
      (QuantumRuntime.mk D σ₀ s₀).evalDistMap I x ρ f s ^ (2⁻¹ : ℝ) +
        (((∑ i ∈ t, b i : ℕ) : ℝ≥0∞) * ∑' c, (∑' r, ENNReal.ofReal
          (‖projDiff P V U W c.1 r * (B c.1 c.2 ⊗ₖ (1 : Matrix D D ℂ))‖ ^ 2)) *
            (QuantumRuntime.mk D σ₀ s₀).indexMass I B x (ρ.matrix ⊗ₖ σ₀.matrix) c) ^
          (2⁻¹ : ℝ) :=
  (rpow_inv_two_outcomeLawWith_le_of_inImage' I hU hW hP hV x ρ f hs hVσ h₀ h₁).trans <|
    add_le_add le_rfl <|
      tsum_rpow_queryWeight_lemmaKraus_le_indexMass_of_isQueryBound I hV hB hPV hK hx t ht ρ

/-- **ePrint 2025/2166, Lemma 5.7, in the form of the paper, for programs within a query
budget**, two-sided: `|√p₀ - √p₁| ≤ √(q · ∑_{i,k} Cᵢ,ₖ · TotalMass(⟨i, k⟩))`, with the total
index masses of the run against the first runtime. In `ℝ≥0∞` the distance `|a - b|` is
`max (a - b) (b - a)`. -/
theorem max_tsub_rpow_inv_two_outcomeLawWith_le_of_inImage_indexMass_of_isQueryBound {γ : Type*}
    [MeasurableSpace γ] {x : QuantumComp L spec X A} {b : spec.Port → ℕ} (hx : x.IsQueryBound b)
    (t : Finset spec.Port) (ht : ∀ i ∉ t, b i = 0) (ρ : SubState A) (f : (Σ u, X u) → γ)
    {s : Set γ} (hs : MeasurableSet s) (hVσ : MatrixMap.conj V σ₀.matrix = σ₀.matrix)
    (hPV : P * V = V * P) (hK : RespectsIndex B B' (lemmaKraus P V U W))
    (h₀ : (QuantumRuntime.mk D σ₀ s₀).ForallQueries I (InImageAt P s₀) x
      (ρ.matrix ⊗ₖ σ₀.matrix))
    (h₁ : (QuantumRuntime.mk D σ₀ s₁).ForallQueries I (InImageAt P s₁) x
      (ρ.matrix ⊗ₖ σ₀.matrix)) :
    max ((QuantumRuntime.mk D σ₀ s₀).evalDistMap I x ρ f s ^ (2⁻¹ : ℝ) -
        (QuantumRuntime.mk D σ₀ s₁).evalDistMap I x ρ f s ^ (2⁻¹ : ℝ))
      ((QuantumRuntime.mk D σ₀ s₁).evalDistMap I x ρ f s ^ (2⁻¹ : ℝ) -
        (QuantumRuntime.mk D σ₀ s₀).evalDistMap I x ρ f s ^ (2⁻¹ : ℝ)) ≤
      (((∑ i ∈ t, b i : ℕ) : ℝ≥0∞) * ∑' c, (∑' r, ENNReal.ofReal
          (‖projDiff P V U W c.1 r * (B c.1 c.2 ⊗ₖ (1 : Matrix D D ℂ))‖ ^ 2)) *
            (QuantumRuntime.mk D σ₀ s₀).indexMass I B x (ρ.matrix ⊗ₖ σ₀.matrix) c) ^
          (2⁻¹ : ℝ) :=
  max_le
    (tsub_le_iff_left.2 (rpow_inv_two_outcomeLawWith_le_of_inImage_indexMass_of_isQueryBound I hU
      hW hP hV hB hx t ht ρ f hs hVσ hPV hK h₀ h₁))
    (tsub_le_iff_left.2 (rpow_inv_two_outcomeLawWith_le_of_inImage_indexMass_of_isQueryBound' I
      hU hW hP hV hB hx t ht ρ f hs hVσ hPV hK h₀ h₁))

/-- **ePrint 2025/2166, Lemma 5.7, in the form of the paper, for programs within a query
budget**, squared as in the paper: `(√p₀ - √p₁)² ≤ q · ∑_{i,k} Cᵢ,ₖ · TotalMass(⟨i, k⟩)`, where
`Cᵢ,ₖ = ∑ᵣ ‖P̂ (V̂ Uᵢ,ᵣ V̂ᴴ - Wᵢ,ᵣ) P̂ (B i k ⊗ 1)‖²` and the total index masses are those of the
run against the first runtime. In `ℝ≥0∞` the distance `|a - b|` is `max (a - b) (b - a)`. -/
theorem max_tsub_rpow_inv_two_outcomeLawWith_sq_le_of_inImage_indexMass_of_isQueryBound {γ : Type*}
    [MeasurableSpace γ] {x : QuantumComp L spec X A} {b : spec.Port → ℕ} (hx : x.IsQueryBound b)
    (t : Finset spec.Port) (ht : ∀ i ∉ t, b i = 0) (ρ : SubState A) (f : (Σ u, X u) → γ)
    {s : Set γ} (hs : MeasurableSet s) (hVσ : MatrixMap.conj V σ₀.matrix = σ₀.matrix)
    (hPV : P * V = V * P) (hK : RespectsIndex B B' (lemmaKraus P V U W))
    (h₀ : (QuantumRuntime.mk D σ₀ s₀).ForallQueries I (InImageAt P s₀) x
      (ρ.matrix ⊗ₖ σ₀.matrix))
    (h₁ : (QuantumRuntime.mk D σ₀ s₁).ForallQueries I (InImageAt P s₁) x
      (ρ.matrix ⊗ₖ σ₀.matrix)) :
    max ((QuantumRuntime.mk D σ₀ s₀).evalDistMap I x ρ f s ^ (2⁻¹ : ℝ) -
        (QuantumRuntime.mk D σ₀ s₁).evalDistMap I x ρ f s ^ (2⁻¹ : ℝ))
      ((QuantumRuntime.mk D σ₀ s₁).evalDistMap I x ρ f s ^ (2⁻¹ : ℝ) -
        (QuantumRuntime.mk D σ₀ s₀).evalDistMap I x ρ f s ^ (2⁻¹ : ℝ)) ^ 2 ≤
      ((∑ i ∈ t, b i : ℕ) : ℝ≥0∞) * ∑' c, (∑' r, ENNReal.ofReal
          (‖projDiff P V U W c.1 r * (B c.1 c.2 ⊗ₖ (1 : Matrix D D ℂ))‖ ^ 2)) *
            (QuantumRuntime.mk D σ₀ s₀).indexMass I B x (ρ.matrix ⊗ₖ σ₀.matrix) c := by
  rw [← ENNReal.rpow_two]
  exact (ENNReal.le_rpow_inv_iff (by norm_num : (0 : ℝ) < 2)).mp
    (max_tsub_rpow_inv_two_outcomeLawWith_le_of_inImage_indexMass_of_isQueryBound I hU hW hP hV hB
      hx t ht ρ f hs hVσ hPV hK h₀ h₁)

end Projected

end QuantumRuntime

end Quantum
