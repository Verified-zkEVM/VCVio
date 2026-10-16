/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.Quantum.Comp.HybridProjected

/-!
# Potential certificates for events of a runtime

This file formalizes the bounds note's (NOTE) refinement of the collision-event argument in
ePrint 2025/2166 §9.3 (Lemma 9.6, p. 61; event bound, pp. 64–65).
The paper uses the size projection, Corollaries 5.8/5.6, and a coefficient-80 per-database
bound.
Corollaries 5.6 and 5.8 appear on pp. 31 and 33.
NOTE introduces the charged potential: an operator on the runtime register whose
trace can decrease up to a charge per call and dominates leakage from the good subspace.
Here we prove its general certificate for arbitrary programs against runtimes with Kraus
steps (NOTE (107)). The quadratic schedule and 7/4 coefficient are NOTE's refinement
(NOTE (77)–(78), (87)–(91)), instantiated in the collision modules.

## The certificate

Let the bad event be a projector `Q` on the runtime register `D`, and let `Q̂ = 1 ⊗ Q`. For the
`n`-th call there is a potential `Φₙ = Kₙᴴ Kₙ` on `D`, a *drop* weight `δₙ`, a *charge* `θₙ`, a
rate `λₙ` and a per-port additive term `eₙ`, such that on every positive semidefinite input `σ`
of a call of port `i`,

* (drop) `δₙ σ + ∑ᵣ tr ((1 ⊗ Φₙ₊₁) Uᵣ σ Uᵣᴴ) ≤ tr ((1 ⊗ Φₙ) σ) + θₙ σ`, and
* (leak) for every `s > 0`, `∑ᵣ tr ([Q̂, Uᵣ] σ [Q̂, Uᵣ]ᴴ) ≤ (1 + s) λₙ δₙ σ + (1 + s⁻¹) eₙ σ`.

Then a run from a state with no weight on `Q` ends with weight at most
`(√(∑ₙ λₙ) · √(tr ((1 ⊗ Φ₀) ρ) + ∑ₙ Θₙ) + ∑ₙ √Eₙ)²` on `Q`, where `Θₙ` and `Eₙ` are the charge and
the additive term summed over the inputs of the `n`-th calls
(`Quantum.QuantumRuntime.rpow_inv_two_eventWeight_le_of_potential`). The additive terms `eₙ`
account both for ports that change the event and for local approximation errors, such as the
phase-projection replacement in bounds-note (107). They can be zero when the local leak
estimate is exact; in that case the bound is `(∑ₙ λₙ) · (tr ((1 ⊗ Φ₀) ρ) + ∑ₙ Θₙ)`.

Both conditions are stated on traces, so that runtimes with countably many outcomes and drops
that are not given by operators are covered. Loewner inequalities between operators give them
(`Quantum.QuantumRuntime.drop_of_posSemidef` and `Quantum.QuantumRuntime.leak_of_posSemidef`).

## Proof

The drop condition telescopes along the run: summed over the first `N` calls, the drops are at
most the initial potential plus the charges
(`Quantum.QuantumRuntime.sum_range_queryWeight_le_potential`), since the potential does not grow
under local operations, which act on the program register only. The pinched runtime, with Kraus
operators `Q̂ Uᵣ Q̂ + Q̂⊥ Uᵣ Q̂⊥`, never puts weight on `Q` (`Quantum.QuantumRuntime.simulation`),
and differs from the given runtime by Kraus operators of the same Kraus weights as the commutators
`[Q̂, Uᵣ]`. The square-root hybrid bound
(`Quantum.QuantumRuntime.rpow_inv_two_tsum_trace_conj_run_le`) bounds the square root of the
weight on `Q` by the sum over the calls of the square roots of these Kraus weights, which the
leak condition, optimized over `s`, bounds by `√(λₙ mₙ) + √Eₙ`, with `mₙ` the summed drops of the
`n`-th calls. Cauchy–Schwarz over the calls and the telescoped drops conclude.

## Main definitions

* `Quantum.QuantumRuntime.potential K ρ`: the potential `tr ((1 ⊗ Kᴴ K) ρ)`, in `ℝ≥0∞`.
* `Quantum.Hybrid.pinch P P' U`: the Kraus operator `P' U P + (1 - P') U (1 - P)`, and
  `Quantum.QuantumRuntime.pinchStep`, the pinched step of a runtime.
* `Quantum.QuantumRuntime.eventWeight`: the weight of the leaves of a run on `1 ⊗ Q`.

## Main statements

* `Quantum.QuantumRuntime.sum_range_queryWeight_le_potential`: telescoping of the drops.
* `Quantum.QuantumRuntime.drop_of_posSemidef` and `Quantum.QuantumRuntime.leak_of_posSemidef`:
  the two conditions from Loewner inequalities.
* `Quantum.QuantumRuntime.eventWeight_pinch_eq_zero`: the pinched runtime keeps the event
  empty; `Quantum.QuantumRuntime.krausWeight_sub_pinch`: it differs from the runtime by the
  Kraus weights of the commutators.
* `Quantum.QuantumRuntime.rpow_inv_two_eventWeight_le_of_potential`: the potential certificate,
  with per-port additive terms; `Quantum.QuantumRuntime.eventWeight_le_of_potential`: the case
  without additive leak costs; `Quantum.QuantumRuntime.eventWeight_le_trace`: the trivial
  bound, for the minimum with one.
-/

public section

open IPFunctor Matrix
open scoped ENNReal ComplexOrder Kronecker

universe u v u₁ v₁ w

namespace Quantum

/-! ## A scalar lemma -/

/-- **Optimizing Young's inequality**, over the reals: if `x ≤ (1 + s) a + (1 + s⁻¹) c` for every
`s > 0`, then `x ≤ (√a + √c)²`. -/
theorem _root_.Real.le_sq_sqrt_add_sqrt_of_forall {x a c : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c)
    (h : ∀ s : ℝ, 0 < s → x ≤ (1 + s) * a + (1 + s⁻¹) * c) : x ≤ (√a + √c) ^ 2 := by
  rcases ha.eq_or_lt with rfl | ha'
  · simp only [mul_zero, zero_add] at h
    rw [Real.sqrt_zero, zero_add, Real.sq_sqrt hc]
    refine le_of_forall_pos_le_add fun ε hε ↦ (h ((c + 1) / ε) (by positivity)).trans ?_
    rw [inv_div, add_mul, one_mul]
    have : ε / (c + 1) * c ≤ ε := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      nlinarith
    linarith
  rcases hc.eq_or_lt with rfl | hc'
  · simp only [mul_zero, add_zero] at h
    rw [Real.sqrt_zero, add_zero, Real.sq_sqrt ha]
    refine le_of_forall_pos_le_add fun ε hε ↦ (h (ε / (a + 1)) (by positivity)).trans ?_
    rw [add_mul, one_mul]
    have : ε / (a + 1) * a ≤ ε := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      nlinarith
    linarith
  have hpa : √a ^ 2 = a := Real.sq_sqrt ha
  have hqc : √c ^ 2 = c := Real.sq_sqrt hc
  have hp := Real.sqrt_pos.mpr ha'
  have hq := Real.sqrt_pos.mpr hc'
  refine (h (√c / √a) (div_pos hq hp)).trans (le_of_eq ?_)
  set p := √a
  set q := √c
  rw [← hpa, ← hqc, inv_div]
  field_simp
  ring

/-- **Optimizing Young's inequality**: if `x ≤ (1 + s) a + (1 + s⁻¹) c` for every `s > 0`, then
`√x ≤ √a + √c`. -/
theorem _root_.ENNReal.rpow_inv_two_le_add_of_forall {x a c : ℝ≥0∞}
    (h : ∀ s : ℝ, 0 < s → x ≤ ENNReal.ofReal (1 + s) * a + ENNReal.ofReal (1 + s⁻¹) * c) :
    x ^ (2⁻¹ : ℝ) ≤ a ^ (2⁻¹ : ℝ) + c ^ (2⁻¹ : ℝ) := by
  rcases eq_top_or_lt_top a with rfl | ha
  · simp [ENNReal.top_rpow_of_pos (by norm_num : (0 : ℝ) < 2⁻¹)]
  rcases eq_top_or_lt_top c with rfl | hc
  · simp [ENNReal.top_rpow_of_pos (by norm_num : (0 : ℝ) < 2⁻¹)]
  have hfin : ∀ s : ℝ, ENNReal.ofReal (1 + s) * a + ENNReal.ofReal (1 + s⁻¹) * c ≠ ⊤ :=
    fun s ↦ ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top ha.ne,
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hc.ne⟩
  have hx : x ≠ ⊤ := ne_top_of_le_ne_top (hfin 1) (h 1 one_pos)
  rw [← ENNReal.ofReal_toReal hx, ← ENNReal.ofReal_toReal ha.ne, ← ENNReal.ofReal_toReal hc.ne,
    ENNReal.ofReal_rpow_inv_two, ENNReal.ofReal_rpow_inv_two, ENNReal.ofReal_rpow_inv_two,
    ← ENNReal.ofReal_add (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)]
  refine ENNReal.ofReal_le_ofReal ((Real.sqrt_le_sqrt (Real.le_sq_sqrt_add_sqrt_of_forall
    ENNReal.toReal_nonneg ENNReal.toReal_nonneg fun s hs ↦ ?_)).trans_eq
    (Real.sqrt_sq (by positivity)))
  refine (ENNReal.toReal_mono (hfin s) (h s hs)).trans_eq ?_
  rw [ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ha.ne)
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hc.ne), ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_ofReal (by positivity)]

/-! ## The pinched Kraus operators -/

namespace Hybrid

variable {J O : Type*} [Fintype J] [DecidableEq J] [Fintype O] [DecidableEq O]

/-- **Pinching** a Kraus operator `U` by projectors `P` on its input and `P'` on its output:
`P' U P + (1 - P') U (1 - P)`, which maps the image of `P` into that of `P'` and its kernel into
the kernel of `P'`. -/
@[expose]
def pinch (P : Matrix J J ℂ) (P' : Matrix O O ℂ) (U : Matrix O J ℂ) : Matrix O J ℂ :=
  P' * U * P + (1 - P') * U * (1 - P)

variable {P : Matrix J J ℂ} {P' : Matrix O O ℂ}

/-- The algebra of a projector and its complement, right-associated. -/
private theorem proj_facts {n : Type*} [Fintype n] [DecidableEq n] {P : Matrix n n ℂ}
    (hPP : P * P = P) {m : Type*} (X : Matrix n m ℂ) :
    P * (P * X) = P * X ∧ P * ((1 - P) * X) = 0 ∧ (1 - P) * (P * X) = 0 ∧
      (1 - P) * ((1 - P) * X) = (1 - P) * X := by
  have h1 : P * (1 - P) = 0 := by rw [Matrix.mul_sub, Matrix.mul_one, hPP, sub_self]
  have h2 : (1 - P) * P = 0 := by rw [Matrix.sub_mul, Matrix.one_mul, hPP, sub_self]
  have h3 : (1 - P) * (1 - P) = 1 - P := by
    rw [Matrix.sub_mul, Matrix.one_mul, h1, sub_zero]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [← Matrix.mul_assoc]
  · rw [hPP]
  · rw [h1, Matrix.zero_mul]
  · rw [h2, Matrix.zero_mul]
  · rw [h3]

variable (hP : Pᴴ = P) (hPP : P * P = P) (hP' : P'ᴴ = P') (hPP' : P' * P' = P')

include hP hP' hPP' in
/-- **The pinched operator and the leak.** `Wᴴ W` plus the leaks `P Uᴴ (1 - P') U P` and
`(1 - P) Uᴴ P' U (1 - P)` across the projectors is the pinching of `Uᴴ U`. -/
theorem conjTranspose_pinch_mul_pinch_add (U : Matrix O J ℂ) :
    (pinch P P' U)ᴴ * pinch P P' U +
        (P * Uᴴ * (1 - P') * U * P + (1 - P) * Uᴴ * P' * U * (1 - P)) =
      P * (Uᴴ * U) * P + (1 - P) * (Uᴴ * U) * (1 - P) := by
  obtain ⟨a1, -, a3, -⟩ := proj_facts hPP' (U * P)
  obtain ⟨-, b2, -, b4⟩ := proj_facts hPP' (U * (1 - P))
  have hc : (1 - P)ᴴ = 1 - P := by rw [conjTranspose_sub, conjTranspose_one, hP]
  have hc' : (1 - P')ᴴ = 1 - P' := by rw [conjTranspose_sub, conjTranspose_one, hP']
  have hU : Uᴴ * U = Uᴴ * P' * U + Uᴴ * (1 - P') * U := by
    rw [← Matrix.add_mul, ← Matrix.mul_add, add_sub_cancel, Matrix.mul_one]
  rw [hU, pinch]
  generalize 1 - P = Pc at *
  generalize 1 - P' = Pc' at *
  simp only [conjTranspose_add, conjTranspose_mul, hP, hP', hc, hc', Matrix.mul_add,
    Matrix.add_mul, Matrix.mul_assoc, a1, a3, b2, b4, Matrix.mul_zero, add_zero, zero_add]
  abel

include hPP hPP' in
/-- The pinched operator commutes with the projectors: `P' W = W P`. -/
theorem mul_pinch (U : Matrix O J ℂ) : P' * pinch P P' U = pinch P P' U * P := by
  obtain ⟨a1, a2, -, -⟩ := proj_facts hPP' (U * P)
  obtain ⟨-, b2, -, -⟩ := proj_facts hPP' (U * (1 - P))
  have h2 : (1 - P) * P = 0 := by rw [Matrix.sub_mul, Matrix.one_mul, hPP, sub_self]
  rw [pinch]
  generalize 1 - P = Pc at *
  generalize 1 - P' = Pc' at *
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, a1, b2, hPP, h2, Matrix.mul_zero,
    add_zero]

include hP hP' hPP' in
/-- **The difference with the pinched operator and the commutator have the same Kraus weights**:
`(U - W)ᴴ (U - W) = Cᴴ C` with `C = P' U - U P`. -/
theorem conjTranspose_sub_pinch_mul (U : Matrix O J ℂ) :
    (U - pinch P P' U)ᴴ * (U - pinch P P' U) = (P' * U - U * P)ᴴ * (P' * U - U * P) := by
  obtain ⟨-, a2, -, a4⟩ := proj_facts hPP' (U * P)
  obtain ⟨b1, -, b3, -⟩ := proj_facts hPP' (U * (1 - P))
  have hc : (1 - P)ᴴ = 1 - P := by rw [conjTranspose_sub, conjTranspose_one, hP]
  have hc' : (1 - P')ᴴ = 1 - P' := by rw [conjTranspose_sub, conjTranspose_one, hP']
  have e1 : U - pinch P P' U = P' * U * (1 - P) + (1 - P') * U * P := by
    rw [pinch]
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul]
    abel
  have e2 : P' * U - U * P = P' * U * (1 - P) - (1 - P') * U * P := by
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul]
    abel
  rw [e1, e2]
  generalize 1 - P = Pc at *
  generalize 1 - P' = Pc' at *
  simp only [conjTranspose_add, conjTranspose_sub, conjTranspose_mul, hP, hP', hc, hc',
    Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, a2, a4, b1,
    b3, Matrix.mul_zero, add_zero, zero_add, sub_zero, zero_sub]
  abel

include hP hPP hP' hPP' in
/-- **Pinching keeps contractions.** If `1 - ∑ᵣ (U r)ᴴ U r` is positive semidefinite, so is
`1 - ∑ᵣ (W r)ᴴ W r` for the pinched operators `W r`. -/
theorem posSemidef_one_sub_sum_pinch {α : Type*} (s : Finset α) {U : α → Matrix O J ℂ}
    (hU : (1 - ∑ r ∈ s, (U r)ᴴ * U r).PosSemidef) :
    (1 - ∑ r ∈ s, (pinch P P' (U r))ᴴ * pinch P P' (U r)).PosSemidef := by
  have hc : (1 - P)ᴴ = 1 - P := by rw [conjTranspose_sub, conjTranspose_one, hP]
  have hc' : (1 - P')ᴴ = 1 - P' := by rw [conjTranspose_sub, conjTranspose_one, hP']
  have hcc' : (1 - P') * (1 - P') = 1 - P' := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, hPP', sub_self, sub_zero]
  have hsplit : (1 : Matrix J J ℂ) = P * 1 * P + (1 - P) * 1 * (1 - P) := by
    simp only [Matrix.mul_one, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, hPP]
    abel
  have hleak : ∀ r, P * (U r)ᴴ * (1 - P') * U r * P + (1 - P) * (U r)ᴴ * P' * U r * (1 - P) =
      ((1 - P') * U r * P)ᴴ * ((1 - P') * U r * P) +
        (P' * U r * (1 - P))ᴴ * (P' * U r * (1 - P)) := fun r ↦ by
    simp only [conjTranspose_mul, hP, hc, hc', hP', Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (1 - P') (1 - P'), hcc', ← Matrix.mul_assoc P' P', hPP']
  have h : 1 - ∑ r ∈ s, (pinch P P' (U r))ᴴ * pinch P P' (U r) =
      (Pᴴ * (1 - ∑ r ∈ s, (U r)ᴴ * U r) * P +
        (1 - P)ᴴ * (1 - ∑ r ∈ s, (U r)ᴴ * U r) * (1 - P)) +
      ∑ r ∈ s, (((1 - P') * U r * P)ᴴ * ((1 - P') * U r * P) +
        (P' * U r * (1 - P))ᴴ * (P' * U r * (1 - P))) := by
    set S := ∑ r ∈ s, (U r)ᴴ * U r
    set Lk := ∑ r ∈ s, (((1 - P') * U r * P)ᴴ * ((1 - P') * U r * P) +
      (P' * U r * (1 - P))ᴴ * (P' * U r * (1 - P)))
    have hsum : ∑ r ∈ s, (pinch P P' (U r))ᴴ * pinch P P' (U r) =
        P * S * P + (1 - P) * S * (1 - P) - Lk := by
      rw [eq_sub_iff_add_eq, ← Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul,
        Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun r _ ↦ ?_
      rw [← hleak]
      exact conjTranspose_pinch_mul_pinch_add hP hP' hPP' (U r)
    rw [hsum, hP, hc]
    calc 1 - (P * S * P + (1 - P) * S * (1 - P) - Lk)
        = (P * 1 * P + (1 - P) * 1 * (1 - P)) - (P * S * P + (1 - P) * S * (1 - P) - Lk) := by
          rw [← hsplit]
      _ = _ := by
          simp only [Matrix.mul_sub, Matrix.sub_mul]
          abel
  rw [h]
  refine ((hU.conjTranspose_mul_mul_same P).add (hU.conjTranspose_mul_mul_same (1 - P))).add
    (Matrix.posSemidef_sum _ fun r _ ↦ ?_)
  exact (posSemidef_conjTranspose_mul_self _).add (posSemidef_conjTranspose_mul_self _)

end Hybrid

namespace QuantumRuntime

open SubInstrument

/-! ## Potentials -/

section potential

variable {D Z : Type*} [Fintype D] [Fintype Z]

/-- **Potential.** The trace `tr ((1 ⊗ Kᴴ K) ρ)` of an operator `ρ` on `A × D` against the
potential `Φ = Kᴴ K` on `D`, in `ℝ≥0∞`. Every positive semidefinite `Φ` has this form, with
`K = Φ^{1/2}`; a diagonal `Φ` has it with the diagonal `K` of the square roots. -/
@[expose]
noncomputable def potential (K : Matrix Z D ℂ) {A : Type*} [Fintype A]
    (ρ : Matrix (A × D) (A × D) ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal ((MatrixMap.conj K).amplifyLeft A ρ).trace.re

variable (K : Matrix Z D ℂ)

/-- The potential as the trace of `(1 ⊗ Kᴴ K) ρ`. -/
theorem potential_eq {A : Type*} [Fintype A] [DecidableEq A] (ρ : Matrix (A × D) (A × D) ℂ) :
    potential K ρ = ENNReal.ofReal (((1 : Matrix A A ℂ) ⊗ₖ (Kᴴ * K)) * ρ).trace.re := by
  rw [potential, MatrixMap.amplifyLeft_conj, MatrixMap.trace_conj_apply,
    conjTranspose_kronecker, conjTranspose_one, ← mul_kronecker_mul, Matrix.one_mul]

/-- The potential of the input of a call is that of the state. -/
theorem potential_callInput [DecidableEq D] {A J E : Type*} [Fintype A] [Fintype J] [Fintype E]
    [DecidableEq A]
    [DecidableEq J] [DecidableEq E] (ℓ : A ≃ J × E) (ρ : Matrix (A × D) (A × D) ℂ) :
    potential K (callInput ℓ D ρ) = potential K ρ := by
  classical
  rw [potential, potential, ← callInput_amplifyLeft, trace_callInput]

/-- **Local operations do not increase the potential**: the potentials of the branches of a
dependent subinstrument on the program register, framed by `D`, add up to at most the potential
of a positive semidefinite state. -/
theorem tsum_potential_frame_le {A : Type*} [Fintype A] {ι : Type*}
    {B : ι → Type*} [∀ b, Fintype (B b)] (p : DSubInstrument A ι B)
    {ρ : Matrix (A × D) (A × D) ℂ} (hρ : ρ.PosSemidef) :
    ∑' b, potential K ((p.frame D).branch b ρ) ≤ potential K ρ := by
  classical
  have h : ∀ b, (MatrixMap.conj K).amplifyLeft (B b) ((p.frame D).branch b ρ) =
      (p.frame Z).branch b ((MatrixMap.conj K).amplifyLeft A ρ) := fun b ↦
    (LinearMap.congr_fun (DSubInstrument.Intertwines.frame_amplifyLeft p (MatrixMap.conj K) b)
      ρ).symm
  simp only [potential, h]
  refine (p.frame Z).isCPTNIFamily.tsum_ofReal_trace_re_le ?_
  rw [MatrixMap.amplifyLeft_conj]
  exact hρ.mul_mul_conjTranspose_same _

/-- A finite-dimensional potential trace is finite. -/
theorem potential_ne_top {A : Type*} [Fintype A]
    (ρ : Matrix (A × D) (A × D) ℂ) : potential K ρ ≠ ⊤ :=
  ENNReal.ofReal_ne_top

end potential

variable {spec : QuantumOracleSpec.{u₁, v₁}} (R : QuantumRuntime spec) {L : LocalSig.{u, v}}
  (I : L.Interp) {X : QReg → Type w} {A : QReg} {Z : Type*} [Fintype Z]

/-- The potential after a call is that of the output of the step on the input of the call. -/
theorem potential_queryStep (K : Matrix Z R.D ℂ) (i : spec.Port) (E : QReg)
    (ℓ : A ≃ spec.In i × E) (r : spec.Result i) (ρ : Matrix (A × R.D) (A × R.D) ℂ) :
    potential K ((R.queryStep i E ℓ).branch r ρ) =
      potential K ((R.step i).branch r (callInput ℓ R.D ρ)) := by
  classical
  have h := LinearMap.congr_fun (intertwines_relabel_queryEquivOut (MatrixMap.conj K)
    (spec.Out i) E ()) (((R.step i).frame E).branch r ((relabel (queryEquivIn ℓ R.D)).branch () ρ))
  simp only [LinearMap.comp_apply] at h
  rw [potential, potential, queryStep_branch_apply, ← h, trace_relabel_branch_apply,
    branch_frame_apply, ← MatrixMap.trace_traceRight, ← LinearMap.comp_apply
      (MatrixMap.traceRight _ E), MatrixMap.traceRight_comp_amplify, LinearMap.comp_apply,
    ← LinearMap.comp_apply (MatrixMap.traceRight _ E), MatrixMap.traceRight_comp_amplify,
    LinearMap.comp_apply, callInput, LinearMap.comp_apply]

/-! ## Telescoping the drops -/

/-- **Telescoping the drops** (bounds note, eq. (107), first half). Let `K n` give the potential
`Φₙ = (K n)ᴴ (K n)` before the `n`-th call, and suppose that on every positive semidefinite input
`σ` of a call `n < N` of port `i`, the drop `w n i σ` and the potentials of the outputs of the
step are at most the potential of the input plus the charge `c n i σ`:
`w n i σ + ∑ᵣ tr ((1 ⊗ Φₙ₊₁) Uᵣ(σ)) ≤ tr ((1 ⊗ Φₙ) σ) + c n i σ`. Then the drops of the first `N`
calls of any program, summed over its paths, are at most the initial potential plus the charges.

Local operations act on the program register only, so they do not increase the potential. -/
theorem sum_range_queryWeight_le_potential (x : QuantumComp L spec X A) (N : ℕ)
    (K : ℕ → Matrix Z R.D ℂ)
    (w c : ℕ → ∀ i, Matrix (spec.In i × R.D) (spec.In i × R.D) ℂ → ℝ≥0∞)
    (h : ∀ n < N, ∀ i σ, σ.PosSemidef →
      w n i σ + ∑' r, potential (K (n + 1)) ((R.step i).branch r σ) ≤
        potential (K n) σ + c n i σ)
    {ρ : Matrix (A × R.D) (A × R.D) ℂ} (hρ : ρ.PosSemidef) :
    ∑ j ∈ Finset.range N, R.queryWeight I (w j) x ρ j ≤
      potential (K 0) ρ + ∑ j ∈ Finset.range N, R.queryWeight I (c j) x ρ j := by
  induction x using QuantumComp.inductionOn generalizing N K w c with
  | pure _ _ => simp
  | primBind B o k ih =>
    simp only [queryWeight_primBind]
    rw [← Summable.tsum_finsetSum (fun _ _ ↦ ENNReal.summable),
      ← Summable.tsum_finsetSum (fun _ _ ↦ ENNReal.summable)]
    calc ∑' b, ∑ j ∈ Finset.range N, R.queryWeight I (w j) (k b) (((I o).frame R.D).branch b ρ) j
        ≤ ∑' b, (potential (K 0) (((I o).frame R.D).branch b ρ) +
            ∑ j ∈ Finset.range N, R.queryWeight I (c j) (k b)
              (((I o).frame R.D).branch b ρ) j) :=
          ENNReal.tsum_le_tsum fun b ↦
            ih b N K w c h (((I o).frame R.D).posSemidef_branch_apply b hρ)
      _ ≤ _ := by
          rw [ENNReal.tsum_add]
          gcongr
          exact tsum_potential_frame_le (K 0) (I o) hρ
  | queryBind B i E ℓ k ih =>
    cases N with
    | zero => simp
    | succ N =>
      rw [Finset.sum_range_succ', Finset.sum_range_succ']
      simp only [queryWeight_queryBind_succ, queryWeight_queryBind_zero]
      rw [← Summable.tsum_finsetSum (fun _ _ ↦ ENNReal.summable),
        ← Summable.tsum_finsetSum (fun _ _ ↦ ENNReal.summable)]
      have hσ := posSemidef_callInput ℓ hρ
      have h0 := h 0 (Nat.succ_pos N) i _ hσ
      have hk : ∀ r, ∑ j ∈ Finset.range N, R.queryWeight I (w (j + 1)) (k r)
            ((R.queryStep i E ℓ).branch r ρ) j ≤
          potential (K 1) ((R.step i).branch r (callInput ℓ R.D ρ)) +
            ∑ j ∈ Finset.range N, R.queryWeight I (c (j + 1)) (k r)
              ((R.queryStep i E ℓ).branch r ρ) j := fun r ↦ by
        rw [← potential_queryStep]
        exact ih r N (fun n ↦ K (n + 1)) (fun n ↦ w (n + 1)) (fun n ↦ c (n + 1))
          (fun n hn ↦ h (n + 1) (by omega)) ((R.queryStep i E ℓ).posSemidef_branch_apply r hρ)
      calc ∑' r, ∑ j ∈ Finset.range N, R.queryWeight I (w (j + 1)) (k r)
              ((R.queryStep i E ℓ).branch r ρ) j + w 0 i (callInput ℓ R.D ρ)
          ≤ ∑' r, (potential (K 1) ((R.step i).branch r (callInput ℓ R.D ρ)) +
              ∑ j ∈ Finset.range N, R.queryWeight I (c (j + 1)) (k r)
                ((R.queryStep i E ℓ).branch r ρ) j) + w 0 i (callInput ℓ R.D ρ) := by
            gcongr with r
            exact hk r
        _ = (w 0 i (callInput ℓ R.D ρ) +
              ∑' r, potential (K 1) ((R.step i).branch r (callInput ℓ R.D ρ))) +
            ∑' r, ∑ j ∈ Finset.range N, R.queryWeight I (c (j + 1)) (k r)
              ((R.queryStep i E ℓ).branch r ρ) j := by
            rw [ENNReal.tsum_add]
            ring
        _ ≤ (potential (K 0) (callInput ℓ R.D ρ) + c 0 i (callInput ℓ R.D ρ)) +
            ∑' r, ∑ j ∈ Finset.range N, R.queryWeight I (c (j + 1)) (k r)
              ((R.queryStep i E ℓ).branch r ρ) j := by
            gcongr
        _ = _ := by
            rw [potential_callInput]
            ring

/-- Query weights are additive in the weight. -/
theorem queryWeight_add (w w' : ∀ i, Matrix (spec.In i × R.D) (spec.In i × R.D) ℂ → ℝ≥0∞)
    (x : QuantumComp L spec X A) (ρ : Matrix (A × R.D) (A × R.D) ℂ) (j : ℕ) :
    R.queryWeight I (fun i σ ↦ w i σ + w' i σ) x ρ j =
      R.queryWeight I w x ρ j + R.queryWeight I w' x ρ j := by
  induction x using QuantumComp.inductionOn generalizing j with
  | pure _ _ => simp
  | primBind _ o k ih =>
    simp only [queryWeight_primBind, ih, ENNReal.tsum_add]
  | queryBind _ i E ℓ k ih =>
    cases j with
    | zero => rfl
    | succ j => simp only [queryWeight_queryBind_succ, ih, ENNReal.tsum_add]

/-! ## The conditions from Loewner inequalities -/

section Loewner

variable {J O D : Type*} [Fintype J] [DecidableEq J] [Fintype O] [DecidableEq O] [Fintype D]
  {α : Type*} [Fintype α]

/-- **The drop condition from operators.** With the drop operator
`Δ = 1 ⊗ Kᴴ K + Θ - ∑ᵣ (U r)ᴴ (1 ⊗ K'ᴴ K') (U r)`, the drop `tr (Δ σ)` and the potentials of the
outputs add up to the potential of the input plus the charge `tr (Θ σ)`. -/
theorem drop_of_posSemidef (U : α → Matrix (O × D) (J × D) ℂ) (K K' : Matrix Z D ℂ)
    (Θ : Matrix (J × D) (J × D) ℂ) {σ : Matrix (J × D) (J × D) ℂ} (hσ : σ.PosSemidef)
    (hΔ : ((1 : Matrix J J ℂ) ⊗ₖ (Kᴴ * K) + Θ -
      ∑ r, (U r)ᴴ * ((1 : Matrix O O ℂ) ⊗ₖ (K'ᴴ * K')) * U r).PosSemidef) :
    ENNReal.ofReal (((1 : Matrix J J ℂ) ⊗ₖ (Kᴴ * K) + Θ -
        ∑ r, (U r)ᴴ * ((1 : Matrix O O ℂ) ⊗ₖ (K'ᴴ * K')) * U r) * σ).trace.re +
      ∑' r, potential K' (MatrixMap.conj (U r) σ) ≤
      potential K σ + ENNReal.ofReal (Θ * σ).trace.re := by
  have hK' : ((1 : Matrix O O ℂ) ⊗ₖ (K'ᴴ * K')).PosSemidef := by
    rw [show (1 : Matrix O O ℂ) ⊗ₖ (K'ᴴ * K') =
        ((1 : Matrix O O ℂ) ⊗ₖ K')ᴴ * ((1 : Matrix O O ℂ) ⊗ₖ K') by
          rw [conjTranspose_kronecker, conjTranspose_one, ← mul_kronecker_mul, Matrix.one_mul]]
    exact posSemidef_conjTranspose_mul_self _
  have hK : ((1 : Matrix J J ℂ) ⊗ₖ (Kᴴ * K)).PosSemidef := by
    rw [show (1 : Matrix J J ℂ) ⊗ₖ (Kᴴ * K) =
        ((1 : Matrix J J ℂ) ⊗ₖ K)ᴴ * ((1 : Matrix J J ℂ) ⊗ₖ K) by
          rw [conjTranspose_kronecker, conjTranspose_one, ← mul_kronecker_mul, Matrix.one_mul]]
    exact posSemidef_conjTranspose_mul_self _
  have hr : ∀ r, potential K' (MatrixMap.conj (U r) σ) =
      ENNReal.ofReal ((U r)ᴴ * ((1 : Matrix O O ℂ) ⊗ₖ (K'ᴴ * K')) * U r * σ).trace.re := fun r ↦ by
    rw [potential_eq, MatrixMap.conj_apply, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      Matrix.trace_mul_cycle, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc]
    congr 3
    simp only [Matrix.mul_assoc]
  have hnn : ∀ r, 0 ≤ ((U r)ᴴ * ((1 : Matrix O O ℂ) ⊗ₖ (K'ᴴ * K')) * U r * σ).trace.re :=
    fun r ↦ (hK'.conjTranspose_mul_mul_same (U r)).trace_mul_re_nonneg hσ
  rw [tsum_fintype, Finset.sum_congr rfl fun r _ ↦ hr r,
    ← ENNReal.ofReal_sum_of_nonneg fun r _ ↦ hnn r,
    ← ENNReal.ofReal_add (hΔ.trace_mul_re_nonneg hσ) (Finset.sum_nonneg fun r _ ↦ hnn r),
    potential_eq]
  refine (ENNReal.ofReal_le_ofReal (le_of_eq ?_)).trans
    (ENNReal.ofReal_add_le)
  simp only [Matrix.sub_mul, Matrix.add_mul, Matrix.sum_mul, Matrix.trace_sub, Matrix.trace_add,
    Matrix.trace_sum, Complex.sub_re, Complex.add_re, Complex.re_sum]
  ring

omit [Fintype Z] [DecidableEq J] [DecidableEq O] in
/-- **The leak condition from operators.** If
`(1 + s) λ Δ + (1 + s⁻¹) Ε - ∑ᵣ (C r)ᴴ (C r)` is positive semidefinite, then the Kraus weight of
the `C r` on `σ` is at most `(1 + s) λ tr (Δ σ) + (1 + s⁻¹) tr (Ε σ)`. -/
theorem leak_of_posSemidef (C : α → Matrix O J ℂ) (Δ Ε : Matrix J J ℂ) {lam s : ℝ}
    (hlam : 0 ≤ lam) (hs : 0 < s) {σ : Matrix J J ℂ} (hσ : σ.PosSemidef) (hΔ : Δ.PosSemidef)
    (hC : (((1 + s) * lam : ℝ) • Δ + ((1 + s⁻¹ : ℝ) : ℝ) • Ε - ∑ r, (C r)ᴴ * C r).PosSemidef) :
    ∑' r, ENNReal.ofReal (MatrixMap.conj (C r) σ).trace.re ≤
      ENNReal.ofReal (1 + s) * (ENNReal.ofReal lam * ENNReal.ofReal (Δ * σ).trace.re) +
        ENNReal.ofReal (1 + s⁻¹) * ENNReal.ofReal (Ε * σ).trace.re := by
  have hnn : ∀ r, 0 ≤ (MatrixMap.conj (C r) σ).trace.re := fun r ↦
    (hσ.mul_mul_conjTranspose_same _).trace_re_nonneg
  have hpos := hC.trace_mul_re_nonneg hσ
  simp only [Matrix.sub_mul, Matrix.add_mul, Matrix.sum_mul, Matrix.smul_mul, Matrix.trace_sub,
    Matrix.trace_add, Matrix.trace_sum, Matrix.trace_smul, Complex.sub_re, Complex.add_re,
    Complex.re_sum, Complex.real_smul, Complex.re_ofReal_mul] at hpos
  rw [tsum_fintype, ← ENNReal.ofReal_sum_of_nonneg fun r _ ↦ hnn r,
    ← ENNReal.ofReal_mul hlam, ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity)]
  refine (ENNReal.ofReal_le_ofReal ?_).trans ENNReal.ofReal_add_le
  simp only [MatrixMap.trace_conj_apply]
  have := hΔ.trace_mul_re_nonneg hσ
  nlinarith

end Loewner

/-! ## The event and the pinched runtime -/

/-- **Event weight.** The weight `∑ₚ tr ((1 ⊗ Q) ρₚ (1 ⊗ Q)ᴴ)` of the leaves `ρₚ` of a run on the
projector `1 ⊗ Q` of the runtime register: the probability, for a substate `ρ` of trace one,
that measuring `Q` on the runtime register at the end of the run gives the event. -/
@[expose]
noncomputable def eventWeight (Q : Matrix R.D R.D ℂ) (x : QuantumComp L spec X A)
    (ρ : Matrix (A × R.D) (A × R.D) ℂ) : ℝ≥0∞ :=
  ∑' p, ENNReal.ofReal (MatrixMap.conj ((1 : Matrix p.1 p.1 ℂ) ⊗ₖ Q)
    ((R.run I x).branch p ρ)).trace.re

section Pinch

open Hybrid

variable {D : QReg} {s : ∀ i, SubInstrument (spec.In i × D) (spec.Out i × D) (spec.Result i)}
  {U : ∀ i, spec.Result i → Matrix (spec.Out i × D) (spec.In i × D) ℂ}
  {Q : Matrix D D ℂ}

omit [Fintype Z] in
private theorem one_kronecker_proj {n : Type*} [Fintype n] [DecidableEq n] (hQ : Qᴴ = Q)
    (hQQ : Q * Q = Q) :
    ((1 : Matrix n n ℂ) ⊗ₖ Q)ᴴ = (1 : Matrix n n ℂ) ⊗ₖ Q ∧
      ((1 : Matrix n n ℂ) ⊗ₖ Q) * ((1 : Matrix n n ℂ) ⊗ₖ Q) = (1 : Matrix n n ℂ) ⊗ₖ Q := by
  refine ⟨by rw [conjTranspose_kronecker, conjTranspose_one, hQ], ?_⟩
  rw [← mul_kronecker_mul, Matrix.one_mul, hQQ]

/-- **The pinched step**: the subinstrument with the Kraus operators
`Q̂ (U i r) Q̂ + Q̂⊥ (U i r) Q̂⊥`, `Q̂ = 1 ⊗ Q`, of a step with Kraus operators `U i r`. -/
@[expose]
noncomputable def pinchStep (hU : ∀ i r, (s i).branch r = MatrixMap.conj (U i r))
    (hQ : Qᴴ = Q) (hQQ : Q * Q = Q) (i : spec.Port) :
    SubInstrument (spec.In i × D) (spec.Out i × D) (spec.Result i) where
  branch r := MatrixMap.conj (pinch (1 ⊗ₖ Q) (1 ⊗ₖ Q) (U i r))
  isCP_branch _ := MatrixMap.isCP_conj _
  isTNI_sum t := by
    rw [← Finset.sum_coe_sort t]
    refine MatrixMap.isTNI_sum_conj_iff.mpr ?_
    rw [Finset.sum_coe_sort t
      (fun r ↦ (pinch (1 ⊗ₖ Q) (1 ⊗ₖ Q) (U i r))ᴴ * pinch (1 ⊗ₖ Q) (1 ⊗ₖ Q) (U i r))]
    exact posSemidef_one_sub_sum_pinch (one_kronecker_proj hQ hQQ).1
      (one_kronecker_proj hQ hQQ).2 (one_kronecker_proj hQ hQQ).1 (one_kronecker_proj hQ hQQ).2 t
      ((s i).posSemidef_one_sub_sum_of_branch_eq_conj (hU i) t)

variable (hU : ∀ i r, (s i).branch r = MatrixMap.conj (U i r)) (hQ : Qᴴ = Q) (hQQ : Q * Q = Q)
  (σ₀ : SubState D)

omit [Fintype Z] in
/-- **The pinched runtime keeps the event empty**: run from an operator with no weight on
`1 ⊗ Q`, it leaves no weight on `1 ⊗ Q`. -/
theorem eventWeight_pinch_eq_zero (x : QuantumComp L spec X A)
    {ρ : Matrix (A × D) (A × D) ℂ} (hρQ : MatrixMap.conj ((1 : Matrix A A ℂ) ⊗ₖ Q) ρ = 0) :
    (QuantumRuntime.mk D σ₀ (pinchStep hU hQ hQQ)).eventWeight I Q x ρ = 0 := by
  have h : ∀ i r, ((QuantumRuntime.mk D σ₀ (pinchStep hU hQ hQQ)).step i).branch r ∘ₗ
      (MatrixMap.conj Q).amplifyLeft (spec.In i) = (MatrixMap.conj Q).amplifyLeft (spec.Out i) ∘ₗ
        ((QuantumRuntime.mk D σ₀ (pinchStep hU hQ hQQ)).step i).branch r := fun i r ↦ by
    rw [show ((QuantumRuntime.mk D σ₀ (pinchStep hU hQ hQQ)).step i).branch r =
      MatrixMap.conj (pinch (1 ⊗ₖ Q) (1 ⊗ₖ Q) (U i r)) from rfl, MatrixMap.amplifyLeft_conj,
      MatrixMap.amplifyLeft_conj, ← MatrixMap.conj_mul, ← MatrixMap.conj_mul]
    exact congrArg _ (mul_pinch (one_kronecker_proj hQ hQQ).2 (one_kronecker_proj hQ hQQ).2
      (U i r)).symm
  refine ENNReal.tsum_eq_zero.mpr fun p ↦ ?_
  have hp := LinearMap.congr_fun (simulation I (R₁ := QuantumRuntime.mk D σ₀ (pinchStep hU hQ hQQ))
    (R₂ := QuantumRuntime.mk D σ₀ (pinchStep hU hQ hQQ)) h x p) ρ
  simp only [LinearMap.comp_apply, MatrixMap.amplifyLeft_conj, hρQ, map_zero] at hp
  rw [← hp]
  simp

omit [Fintype Z] in
include hQ hQQ in
/-- The Kraus weight of the difference between a step and its pinching is that of the
commutators `[Q̂, U i r]`. -/
theorem krausWeight_sub_pinch (i : spec.Port) (σ : Matrix (spec.In i × D) (spec.In i × D) ℂ) :
    krausWeight (fun i r ↦ U i r - pinch (1 ⊗ₖ Q) (1 ⊗ₖ Q) (U i r)) i σ =
      ∑' r, ENNReal.ofReal (MatrixMap.conj
        ((1 ⊗ₖ Q) * U i r - U i r * (1 ⊗ₖ Q)) σ).trace.re := by
  refine tsum_congr fun r ↦ ?_
  rw [MatrixMap.trace_conj_apply, MatrixMap.trace_conj_apply, conjTranspose_sub_pinch_mul
    (one_kronecker_proj hQ hQQ).1 (one_kronecker_proj hQ hQQ).1 (one_kronecker_proj hQ hQQ).2]

/-! ## The certificate -/

include hU hQ hQQ in
/-- **The potential certificate** of NOTE (107), with per-port additive terms. This supports
NOTE's refinement of the paper's §9.3 collision-event argument (Lemma 9.6,
p. 61; event bound, pp. 64–65).
Let a runtime have Kraus operators `U i r`, let `Q` be a projector on its
register, and let a program call it at most `N` times. Suppose that for every call `n < N`, on
every positive semidefinite input `σ` of a call of port `i`,

* (drop) `δₙ σ + ∑ᵣ tr ((1 ⊗ Φₙ₊₁) Uᵣ σ Uᵣᴴ) ≤ tr ((1 ⊗ Φₙ) σ) + θₙ σ`, with `Φₙ = (K n)ᴴ (K n)`;
* (leak) for every `s > 0`, `∑ᵣ tr (Cᵣ σ Cᵣᴴ) ≤ (1 + s) λₙ δₙ σ + (1 + s⁻¹) eₙ σ`, where
  `Cᵣ = Q̂ Uᵣ - Uᵣ Q̂` and `Q̂ = 1 ⊗ Q`.

Then, from an operator `ρ` with no weight on `1 ⊗ Q`, the square root of the weight of the run on
`1 ⊗ Q` is at most `√(∑ₙ λₙ) · √(tr ((1 ⊗ Φ₀) ρ) + ∑ₙ Θₙ) + ∑ₙ √Eₙ`, where `Θₙ` and `Eₙ` are
`θₙ` and `eₙ` summed over the inputs of the `n`-th calls (as query weights).

The terms `eₙ` are additive leak costs. They can account for event-changing ports or for
approximation errors in the local operator bound. With `e = 0` the bound is
`√(∑ₙ λₙ (tr ((1 ⊗ Φ₀) ρ) + ∑ₙ Θₙ))`. -/
theorem rpow_inv_two_eventWeight_le_of_potential (x : QuantumComp L spec X A)
    {b : spec.Port → ℕ} (hx : x.IsQueryBound b) (t : Finset spec.Port) (ht : ∀ i ∉ t, b i = 0)
    {N : ℕ} (hN : ∑ i ∈ t, b i ≤ N) (K : ℕ → Matrix Z D ℂ)
    (δ θ e : ℕ → ∀ i, Matrix (spec.In i × D) (spec.In i × D) ℂ → ℝ≥0∞) (lam : ℕ → ℝ≥0∞)
    (hdrop : ∀ n < N, ∀ i σ, σ.PosSemidef →
      δ n i σ + ∑' r, potential (K (n + 1)) ((s i).branch r σ) ≤ potential (K n) σ + θ n i σ)
    (hleak : ∀ n < N, ∀ i σ, σ.PosSemidef → ∀ ε : ℝ, 0 < ε →
      ∑' r, ENNReal.ofReal (MatrixMap.conj ((1 ⊗ₖ Q) * U i r - U i r * (1 ⊗ₖ Q)) σ).trace.re ≤
        ENNReal.ofReal (1 + ε) * (lam n * δ n i σ) + ENNReal.ofReal (1 + ε⁻¹) * e n i σ)
    {ρ : Matrix (A × D) (A × D) ℂ} (hρ : ρ.PosSemidef)
    (hρQ : MatrixMap.conj ((1 : Matrix A A ℂ) ⊗ₖ Q) ρ = 0) :
    (QuantumRuntime.mk D σ₀ s).eventWeight I Q x ρ ^ (2⁻¹ : ℝ) ≤
      (∑ n ∈ Finset.range N, lam n) ^ (2⁻¹ : ℝ) *
          (potential (K 0) ρ + ∑ n ∈ Finset.range N,
            (QuantumRuntime.mk D σ₀ s).queryWeight I (θ n) x ρ n) ^ (2⁻¹ : ℝ) +
        ∑ n ∈ Finset.range N, (QuantumRuntime.mk D σ₀ s).queryWeight I (e n) x ρ n ^ (2⁻¹ : ℝ) := by
  set R := QuantumRuntime.mk D σ₀ s
  set m : ℕ → ℝ≥0∞ := fun n ↦ R.queryWeight I (δ n) x ρ n
  set E : ℕ → ℝ≥0∞ := fun n ↦ R.queryWeight I (e n) x ρ n
  have hP := one_kronecker_proj (n := A) hQ hQQ
  -- The square-root hybrid bound against the pinched runtime.
  have hO : ∀ p : Σ u, X u, (1 - ((1 : Matrix p.1 p.1 ℂ) ⊗ₖ Q)ᴴ *
      ((1 : Matrix p.1 p.1 ℂ) ⊗ₖ Q)).PosSemidef := fun p ↦ by
    obtain ⟨h1, h2⟩ := one_kronecker_proj (n := p.1) hQ hQQ
    have : 1 - ((1 : Matrix p.1 p.1 ℂ) ⊗ₖ Q)ᴴ * ((1 : Matrix p.1 p.1 ℂ) ⊗ₖ Q) =
        (1 - (1 : Matrix p.1 p.1 ℂ) ⊗ₖ Q)ᴴ * (1 - (1 : Matrix p.1 p.1 ℂ) ⊗ₖ Q) := by
      rw [conjTranspose_sub, conjTranspose_one, h1, Matrix.sub_mul, Matrix.mul_sub,
        Matrix.mul_sub, h2]
      simp
    rw [this]
    exact posSemidef_conjTranspose_mul_self _
  have hhyb := rpow_inv_two_tsum_trace_conj_run_le I σ₀ σ₀ hU
    (fun i r ↦ (rfl : (pinchStep hU hQ hQQ i).branch r = _)) x
    (fun p ↦ (1 : Matrix p.1 p.1 ℂ) ⊗ₖ Q) hO hρ
  have hzero := eventWeight_pinch_eq_zero I hU hQ hQQ σ₀ x hρQ
  rw [eventWeight] at hzero
  rw [hzero, ENNReal.zero_rpow_of_pos (by norm_num), zero_add] at hhyb
  refine hhyb.trans ?_
  -- Only the first `N` calls count.
  have hz : ∀ j ∉ Finset.range N, R.queryWeight I
      (krausWeight fun i r ↦ U i r - pinch (1 ⊗ₖ Q) (1 ⊗ₖ Q) (U i r)) x ρ j ^ (2⁻¹ : ℝ) = 0 :=
    fun j hj ↦ by
      rw [R.queryWeight_eq_zero_of_isQueryBound I hx t ht
        (hN.trans (by simpa using hj)) ρ, ENNReal.zero_rpow_of_pos (by norm_num)]
  rw [tsum_eq_sum hz]
  -- Each call: optimize the leak condition.
  have hcall : ∀ n ∈ Finset.range N, R.queryWeight I
      (krausWeight fun i r ↦ U i r - pinch (1 ⊗ₖ Q) (1 ⊗ₖ Q) (U i r)) x ρ n ^ (2⁻¹ : ℝ) ≤
        lam n ^ (2⁻¹ : ℝ) * m n ^ (2⁻¹ : ℝ) + E n ^ (2⁻¹ : ℝ) := fun n hn ↦ by
    rw [← ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
    refine ENNReal.rpow_inv_two_le_add_of_forall fun ε hε ↦ ?_
    calc R.queryWeight I
          (krausWeight fun i r ↦ U i r - pinch (1 ⊗ₖ Q) (1 ⊗ₖ Q) (U i r)) x ρ n
        ≤ R.queryWeight I (fun i σ ↦ ENNReal.ofReal (1 + ε) * (lam n * δ n i σ) +
            ENNReal.ofReal (1 + ε⁻¹) * e n i σ) x ρ n :=
          R.queryWeight_mono I (fun i σ hσ ↦ by
            rw [krausWeight_sub_pinch hQ hQQ]
            exact hleak n (Finset.mem_range.mp hn) i σ hσ ε hε) x hρ n
      _ = ENNReal.ofReal (1 + ε) * (lam n * m n) + ENNReal.ofReal (1 + ε⁻¹) * E n := by
          rw [queryWeight_add]
          simp only [← mul_assoc]
          rw [R.queryWeight_const_mul I, R.queryWeight_const_mul I]
  refine (Finset.sum_le_sum hcall).trans ?_
  rw [Finset.sum_add_distrib]
  gcongr
  -- Cauchy–Schwarz over the calls and the telescoped drops.
  refine (ENNReal.inner_le_Lp_mul_Lq _ _ _ Real.HolderConjugate.two_two).trans ?_
  simp only [rpow_inv_two_rpow_two, one_div]
  gcongr
  exact R.sum_range_queryWeight_le_potential I x N K δ θ hdrop hρ

include hU hQ hQQ in
/-- **The potential certificate without additive leak costs**: with leaks bounded by
`λₙ δₙ` (the case `eₙ = 0` of `rpow_inv_two_eventWeight_le_of_potential`), the weight on `1 ⊗ Q`
is at most `(∑ₙ λₙ) · (tr ((1 ⊗ Φ₀) ρ) + ∑ₙ Θₙ)`. -/
theorem eventWeight_le_of_potential (x : QuantumComp L spec X A)
    {b : spec.Port → ℕ} (hx : x.IsQueryBound b) (t : Finset spec.Port) (ht : ∀ i ∉ t, b i = 0)
    {N : ℕ} (hN : ∑ i ∈ t, b i ≤ N) (K : ℕ → Matrix Z D ℂ)
    (δ θ : ℕ → ∀ i, Matrix (spec.In i × D) (spec.In i × D) ℂ → ℝ≥0∞) (lam : ℕ → ℝ≥0∞)
    (hdrop : ∀ n < N, ∀ i σ, σ.PosSemidef →
      δ n i σ + ∑' r, potential (K (n + 1)) ((s i).branch r σ) ≤ potential (K n) σ + θ n i σ)
    (hleak : ∀ n < N, ∀ i σ, σ.PosSemidef →
      ∑' r, ENNReal.ofReal (MatrixMap.conj ((1 ⊗ₖ Q) * U i r - U i r * (1 ⊗ₖ Q)) σ).trace.re ≤
        lam n * δ n i σ)
    {ρ : Matrix (A × D) (A × D) ℂ} (hρ : ρ.PosSemidef)
    (hρQ : MatrixMap.conj ((1 : Matrix A A ℂ) ⊗ₖ Q) ρ = 0) :
    (QuantumRuntime.mk D σ₀ s).eventWeight I Q x ρ ≤
      (∑ n ∈ Finset.range N, lam n) *
        (potential (K 0) ρ + ∑ n ∈ Finset.range N,
          (QuantumRuntime.mk D σ₀ s).queryWeight I (θ n) x ρ n) := by
  have h := rpow_inv_two_eventWeight_le_of_potential I hU hQ hQQ σ₀ x hx t ht hN K δ θ
    (fun _ _ _ ↦ 0) lam hdrop (fun n hn i σ hσ ε hε ↦ (hleak n hn i σ hσ).trans (by
      rw [mul_zero, add_zero]
      exact le_mul_of_one_le_left zero_le (ENNReal.one_le_ofReal.mpr (by linarith)))) hρ hρQ
  have h0 : ∀ n, (QuantumRuntime.mk D σ₀ s).queryWeight I (fun _ _ ↦ 0) x ρ n = 0 := fun n ↦ by
    simpa using (QuantumRuntime.mk D σ₀ s).queryWeight_const_mul I (w := fun _ _ ↦ 0) 0 x ρ n
  simp only [h0, ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 2⁻¹), Finset.sum_const_zero,
    add_zero] at h
  rw [← ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)] at h
  have := ENNReal.rpow_le_rpow h (by norm_num : (0 : ℝ) ≤ 2)
  simpa only [rpow_inv_two_rpow_two] using this

omit [Fintype Z] in
/-- The weight on `1 ⊗ Q` is at most the trace of the initial operator. -/
theorem eventWeight_le_trace (R : QuantumRuntime spec) {Q : Matrix R.D R.D ℂ} (hQ : Qᴴ = Q)
    (hQQ : Q * Q = Q) (x : QuantumComp L spec X A) {ρ : Matrix (A × R.D) (A × R.D) ℂ}
    (hρ : ρ.PosSemidef) : R.eventWeight I Q x ρ ≤ ENNReal.ofReal ρ.trace.re := by
  refine (ENNReal.tsum_le_tsum fun p ↦ ENNReal.ofReal_le_ofReal ?_).trans
    ((R.run I x).isCPTNIFamily.tsum_ofReal_trace_re_le hρ)
  obtain ⟨h1, h2⟩ := one_kronecker_proj (n := p.1) hQ hQQ
  have hM := (R.run I x).posSemidef_branch_apply p hρ
  rw [MatrixMap.trace_conj_apply, h1, h2, ← sub_nonneg]
  have hsub : ((R.run I x).branch p ρ).trace.re -
      (((1 : Matrix p.1 p.1 ℂ) ⊗ₖ Q) * (R.run I x).branch p ρ).trace.re =
      ((1 - (1 : Matrix p.1 p.1 ℂ) ⊗ₖ Q) * (R.run I x).branch p ρ).trace.re := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub, Complex.sub_re]
  rw [hsub]
  refine Matrix.PosSemidef.trace_mul_re_nonneg ?_ hM
  rw [show (1 : Matrix (p.1 × R.D) (p.1 × R.D) ℂ) - 1 ⊗ₖ Q =
    (1 - 1 ⊗ₖ Q)ᴴ * (1 - 1 ⊗ₖ Q) by
      rw [conjTranspose_sub, conjTranspose_one, h1, Matrix.sub_mul, Matrix.mul_sub,
        Matrix.mul_sub, h2]
      simp]
  exact posSemidef_conjTranspose_mul_self _

end Pinch

end QuantumRuntime

end Quantum
