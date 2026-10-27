/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.Quantum.Comp.TotalQueryBound
public import VCVio.Quantum.Oracle.Compressed.Size

/-!
# Graded runtimes

A grading `g` of the runtime register that every step raises by at most one bounds the grade of
the support after a program with a query budget. The same bound lets a comparison of query
weights be checked only on the grades that the actual `j`-th query can reach.
-/

public section

open Matrix OracleSpec
open scoped ENNReal ComplexOrder

universe u w uL vL u₁ v₁

namespace Quantum

namespace QuerySupportedOn

/-- Preparing a call input traces out the unused workspace. This preserves support on grades read
from the private register. -/
theorem callInput {A J E D Z : Type*} [Fintype A] [Fintype J] [Fintype E] [Fintype D]
    [DecidableEq A] [DecidableEq J] [DecidableEq E] [DecidableEq D]
    {g : D → Z} {T : Set Z} {ρ : Matrix (A × D) (A × D) ℂ}
    (hρ : QuerySupportedOn (fun m : A × D ↦ g m.2) T ρ) (ℓ : A ≃ J × E) :
    QuerySupportedOn (fun m : J × D ↦ g m.2) T (QuantumRuntime.callInput ℓ D ρ) := by
  intro a b hab
  simp only [QuantumRuntime.callInput, LinearMap.comp_apply, MatrixMap.traceRight_apply,
    SubInstrument.relabel_branch_apply, submatrix_apply] at hab
  obtain ⟨e, -, he⟩ := Finset.exists_ne_zero_of_sum_ne_zero hab
  exact hρ _ _ he

variable {spec : QuantumOracleSpec.{u₁, v₁}} (R : QuantumRuntime spec) (g : R.D → ℕ)

/-- **One call of a graded runtime.** If every step of `R` takes support on grades at most `t` to
support on grades at most `t + 1`, so does every call, with any remainder `E` carried along. -/
theorem queryStep_of_step
    (hR : ∀ i r t (σ : Matrix (spec.In i × R.D) (spec.In i × R.D) ℂ),
      QuerySupportedOn (fun m : spec.In i × R.D ↦ g m.2) (Set.Iic t) σ →
        QuerySupportedOn (fun m : spec.Out i × R.D ↦ g m.2) (Set.Iic (t + 1))
          ((R.step i).branch r σ))
    {A : QReg} {t : ℕ} (i : spec.Port) (E : QReg) (ℓ : A ≃ spec.In i × E) (r : spec.Result i)
    {ρ : Matrix (A × R.D) (A × R.D) ℂ}
    (h : QuerySupportedOn (fun m : A × R.D ↦ g m.2) (Set.Iic t) ρ) :
    QuerySupportedOn (fun m : (spec.Out i × E) × R.D ↦ g m.2) (Set.Iic (t + 1))
      ((R.queryStep i E ℓ).branch r ρ) := by
  rw [QuantumRuntime.queryStep_branch_apply, DSubInstrument.branch_frame_apply]
  have h₁ := (h.branch_relabel (QuantumRuntime.queryEquivIn ℓ R.D)).imp
    (q' := fun m : (spec.In i × R.D) × E ↦ g m.1.2) (S' := Set.Iic t) fun m hm ↦ by
      obtain ⟨y, rfl⟩ := (QuantumRuntime.queryEquivIn ℓ R.D).surjective m
      rwa [Function.comp_apply, Equiv.symm_apply_apply] at hm
  have h₂ := QuerySupportedOn.amplify_fst (q := fun m : spec.In i × R.D ↦ g m.2)
    (q' := fun m : spec.Out i × R.D ↦ g m.2) (fun σ hσ ↦ hR i r t σ hσ) h₁
  refine (h₂.branch_relabel (QuantumRuntime.queryEquivOut _ R.D E)).imp fun m hm ↦ ?_
  obtain ⟨y, rfl⟩ := (QuantumRuntime.queryEquivOut _ R.D E).surjective m
  rwa [Function.comp_apply, Equiv.symm_apply_apply] at hm

/-- Spending one call of a nonzero budget lowers its total by one. -/
theorem sum_update_sub_one_add_one {P : Type*} [Fintype P] [DecidableEq P] {b : P → ℕ} {i : P}
    (hb : 0 < b i) : ∑ j, Function.update b i (b i - 1) j + 1 = ∑ j, b j := by
  rw [Finset.sum_update_of_mem (Finset.mem_univ i), ← Finset.compl_eq_univ_sdiff,
    Fintype.sum_eq_add_sum_compl i b]
  omega

variable {L : LocalSig.{uL, vL}} {W : QReg → Type w} {A : QReg}

/-- **The grade after a program.** If every step of `R` raises the grade of the support by at most
one, a program within the budget `b` takes support on grades at most `t` to support on grades at
most `t + ∑ i, b i` on every branch. -/
theorem run_of_step [Fintype spec.Port]
    (hR : ∀ i r t (σ : Matrix (spec.In i × R.D) (spec.In i × R.D) ℂ),
      QuerySupportedOn (fun m : spec.In i × R.D ↦ g m.2) (Set.Iic t) σ →
        QuerySupportedOn (fun m : spec.Out i × R.D ↦ g m.2) (Set.Iic (t + 1))
          ((R.step i).branch r σ))
    (I : L.Interp) {x : QuantumComp L spec W A} {b : spec.Port → ℕ} (hx : x.IsQueryBound b)
    {t : ℕ} {ρ : Matrix (A × R.D) (A × R.D) ℂ}
    (hρ : QuerySupportedOn (fun m : A × R.D ↦ g m.2) (Set.Iic t) ρ) (p : Σ u, W u) :
    QuerySupportedOn (fun m : p.1 × R.D ↦ g m.2) (Set.Iic (t + ∑ i, b i))
      ((R.run I x).branch p ρ) := by
  classical
  induction x using QuantumComp.inductionOn generalizing b t with
  | pure _ y =>
    rw [QuantumRuntime.run_pure]
    by_cases hp : p = ⟨_, y⟩
    · subst hp
      rw [DSubInstrument.branch_ret_self]
      exact hρ.mono (Set.Iic_subset_Iic.mpr (Nat.le_add_right t _))
    · rw [DSubInstrument.branch_ret_of_ne _ hp]
      exact querySupportedOn_zero _ _
  | primBind _ o k ih =>
    rw [QuantumRuntime.run_primBind, DSubInstrument.branch_bind_apply]
    exact QuerySupportedOn.tsum fun c ↦ ih c ((QuantumComp.isQueryBound_primBind_iff o k b).mp
      hx c) (QuerySupportedOn.amplify_snd (q := g) hρ _)
  | queryBind _ i E ℓ k ih =>
    obtain ⟨hq, hk⟩ := (QuantumComp.isQueryBound_queryBind_iff i E ℓ k b).mp hx
    rw [QuantumRuntime.run_queryBind, DSubInstrument.branch_bind_apply]
    refine QuerySupportedOn.tsum fun r ↦ ?_
    have h := ih r (hk r) (queryStep_of_step R g hR i E ℓ r hρ)
    rwa [Nat.add_assoc, Nat.add_comm 1, sum_update_sub_one_add_one hq] at h

/-- A total call budget bounds the grade independently of the number of ports. -/
theorem run_of_total_step
    (hR : ∀ i r t (σ : Matrix (spec.In i × R.D) (spec.In i × R.D) ℂ),
      QuerySupportedOn (fun m : spec.In i × R.D ↦ g m.2) (Set.Iic t) σ →
        QuerySupportedOn (fun m : spec.Out i × R.D ↦ g m.2) (Set.Iic (t + 1))
          ((R.step i).branch r σ))
    (I : L.Interp) {x : QuantumComp L spec W A} {n : ℕ} (hx : x.IsTotalQueryBound n)
    {t : ℕ} {ρ : Matrix (A × R.D) (A × R.D) ℂ}
    (hρ : QuerySupportedOn (fun m : A × R.D ↦ g m.2) (Set.Iic t) ρ) (p : Σ u, W u) :
    QuerySupportedOn (fun m : p.1 × R.D ↦ g m.2) (Set.Iic (t + n))
      ((R.run I x).branch p ρ) := by
  classical
  induction x using QuantumComp.inductionOn generalizing n t with
  | pure _ y =>
    rw [QuantumRuntime.run_pure]
    by_cases hp : p = ⟨_, y⟩
    · subst hp
      rw [DSubInstrument.branch_ret_self]
      exact hρ.mono (Set.Iic_subset_Iic.mpr (Nat.le_add_right t _))
    · rw [DSubInstrument.branch_ret_of_ne _ hp]
      exact querySupportedOn_zero _ _
  | primBind _ o k ih =>
    rw [QuantumComp.isTotalQueryBound_primBind_iff] at hx
    rw [QuantumRuntime.run_primBind, DSubInstrument.branch_bind_apply]
    exact QuerySupportedOn.tsum fun c ↦ ih c (hx c) (QuerySupportedOn.amplify_snd (q := g) hρ _)
  | queryBind _ i E ℓ k ih =>
    obtain ⟨hq, hk⟩ := (QuantumComp.isTotalQueryBound_queryBind_iff i E ℓ k n).mp hx
    rw [QuantumRuntime.run_queryBind, DSubInstrument.branch_bind_apply]
    refine QuerySupportedOn.tsum fun r ↦ ?_
    have h := ih r (hk r) (queryStep_of_step R g hR i E ℓ r hρ)
    convert h using 1
    congr 1
    omega
end QuerySupportedOn

namespace QuantumRuntime

variable {spec : QuantumOracleSpec.{u₁, v₁}} {L : LocalSig.{uL, vL}}
  (R : QuantumRuntime spec) (I : L.Interp) (g : R.D → ℕ)

/-- A local comparison needed only on grade `t + j` bounds the weight of the actual `j`-th
query from an input of grade `t`, when every step raises the grade by at most one. All
intervening local instruments and query outcomes are included. The hypothesis is on one-step
operators, not on complete executions. -/
theorem queryWeight_mono_of_grade
    (hR : ∀ i r t (σ : Matrix (spec.In i × R.D) (spec.In i × R.D) ℂ),
      QuerySupportedOn (fun m : spec.In i × R.D ↦ g m.2) (Set.Iic t) σ →
        QuerySupportedOn (fun m : spec.Out i × R.D ↦ g m.2) (Set.Iic (t + 1))
          ((R.step i).branch r σ))
    {w w' : ∀ i, Matrix (spec.In i × R.D) (spec.In i × R.D) ℂ → ℝ≥0∞}
    {W : QReg → Type w} {A : QReg} (x : QuantumComp L spec W A)
    {ρ : Matrix (A × R.D) (A × R.D) ℂ} (hρ : ρ.PosSemidef) (t j : ℕ)
    (hgrade : QuerySupportedOn (fun m : A × R.D ↦ g m.2) (Set.Iic t) ρ)
    (hw : ∀ i σ, σ.PosSemidef →
      QuerySupportedOn (fun m : spec.In i × R.D ↦ g m.2) (Set.Iic (t + j)) σ →
        w i σ ≤ w' i σ) :
    R.queryWeight I w x ρ j ≤ R.queryWeight I w' x ρ j := by
  induction x using QuantumComp.inductionOn generalizing t j with
  | pure _ _ => simp
  | primBind _ o k ih =>
    simp only [queryWeight_primBind]
    exact ENNReal.tsum_le_tsum fun b ↦
      ih b (((I o).frame R.D).posSemidef_branch_apply b hρ) t j
        (hgrade.amplify_snd _) hw
  | queryBind _ i E ℓ k ih =>
    cases j with
    | zero =>
      exact hw i _ (posSemidef_callInput ℓ hρ) (by simpa using hgrade.callInput ℓ)
    | succ j =>
      simp only [queryWeight_queryBind_succ]
      refine ENNReal.tsum_le_tsum fun r ↦
        ih r ((R.queryStep i E ℓ).posSemidef_branch_apply r hρ) (t + 1) j
          (QuerySupportedOn.queryStep_of_step R g hR i E ℓ r hgrade) ?_
      simpa only [Nat.add_assoc, Nat.add_comm 1] using hw

end QuantumRuntime

namespace EmulatedOracle

variable {P : Type u} {In : P → QReg} (F : EmulatedOracle P In) (g : F.S → ℕ)

/-- The steps of an emulated oracle whose unitaries raise the grade by at most one raise the grade
of the support by at most one. -/
theorem querySupportedOn_toRuntime_step
    (hF : ∀ i a a' d d', F.U i (a', d') (a, d) ≠ 0 → g d' ≤ g d + 1)
    (i : P) (r : Unit) (t : ℕ)
    (σ : Matrix (In i × F.S) (In i × F.S) ℂ)
    (hσ : QuerySupportedOn (fun m : In i × F.S ↦ g m.2) (Set.Iic t) σ) :
    QuerySupportedOn (fun m : In i × F.S ↦ g m.2) (Set.Iic (t + 1))
      ((F.toRuntime.step i).branch r σ) := by
  rw [toRuntime_step_branch]
  exact QuerySupportedOn.conj hσ fun m' m hK hm ↦
    (hF i m.1 m'.1 m.2 m'.2 hK).trans (Nat.add_le_add_right hm 1)

omit F g in
/-- The coherent unitary raises the grade by at most one when every port does. -/
theorem coherent_U_grade {P : Type} [Fintype P] [DecidableEq P] {In : P → QReg}
    (F : EmulatedOracle P In) (g : F.S → ℕ)
    (hF : ∀ i a a' d d', F.U i (a', d') (a, d) ≠ 0 → g d' ≤ g d + 1) (i : Unit)
    (a a' : cohIn In) (d d' : F.S) (h : F.coherent.U i (a', d') (a, d) ≠ 0) :
    g d' ≤ g d + 1 := by
  obtain ⟨p', b'⟩ := a'
  obtain ⟨p, b⟩ := a
  by_cases hp : p' = p
  · subst hp
    rw [coherent_U_apply_self] at h
    exact hF p' b b' d d' h
  · exact absurd (coherent_U_apply_of_ne F hp b' b d' d) h

end EmulatedOracle

end Quantum
