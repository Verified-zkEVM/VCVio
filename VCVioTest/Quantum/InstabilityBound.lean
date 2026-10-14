/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.Quantum.Oracle.Compressed.CommutatorBound

/-!
# Instability and commutator-bound regression tests

* **The two-block partition of Chiesa, Manohar and Spooner** (TCC 2019, Lemma 5.10): the
  databases with `D x₀ = y₀` against the rest. One fresh answer leaves the second class with
  probability at most `1 / |Y|` and never leaves the first, so the instability is at most
  `1 / |Y|` and the commutator with the truncated compressed oracle is at most `80 / |Y|` in
  squared norm.
* **The trivial partition**: a constant labelling has instability `0`, and the purified
  measurement of a constant label commutes exactly with the truncated compressed oracle.
* **A concrete instance**, `X = Unit` and `Y = ZMod 2`: the two-block partition at `y₀ = 0` has
  instability exactly `1 / 2` for every query bound `t ≥ 1`, the finest partition (the database
  itself) has instability exactly `1`, and both have instability `0` at query bound `0`.
* **Universe polymorphism**: the block lemmas and Lemma 5.10 instantiate at `Type 1`.
-/

public section

open Quantum Matrix OracleSpec
open scoped ENNReal Kronecker Matrix.Norms.L2Operator

namespace VCVioTest.InstabilityBound

/-! ## The two-block partition -/

section twoBlock

variable {X Y : Type} [DecidableEq X] [Fintype Y] [DecidableEq Y]

/-- The two-block labelling of Chiesa, Manohar and Spooner: does the database answer `y₀` at
`x₀`? -/
def answers (x₀ : X) (y₀ : Y) (D : Database X Y) : Bool :=
  decide (D x₀ = some y₀)

/-- At most one fresh answer moves a database across the two blocks. -/
theorem card_filter_answers_le (x₀ : X) (y₀ : Y) {D : Database X Y} {x : X} (hx : D x = none) :
    (Finset.univ.filter fun u : Y ↦
      answers x₀ y₀ (Function.update D x (some u)) ≠ answers x₀ y₀ D).card ≤ 1 := by
  refine (Finset.card_le_card fun u hu ↦ ?_).trans (Finset.card_singleton y₀).le
  have hu' := (Finset.mem_filter.mp hu).2
  simp only [answers] at hu'
  rw [Finset.mem_singleton]
  by_cases hxx : x₀ = x
  · subst hxx
    simpa [hx] using hu'
  · simp [Function.update_of_ne hxx] at hu'

variable [UniformAnswerMeasure (X →ₒ Y)]

/-- The two-block partition has instability at most `1 / |Y|`. -/
theorem instability_answers_le [Finite X] (x₀ : X) (y₀ : Y) (t : ℕ) :
    Database.instability (answers x₀ y₀) t ≤ (Fintype.card Y : ℝ≥0∞)⁻¹ := by
  have := Fintype.ofFinite X
  rw [Database.instability_eq_iSup]
  refine iSup_le fun i ↦ iSup_le fun D ↦ iSup_le fun hi ↦ iSup_le fun _ ↦ iSup_le fun x ↦
    iSup_le fun hx ↦ ?_
  subst hi
  rw [← one_div]
  exact ENNReal.div_le_div_right (by exact_mod_cast card_filter_answers_le x₀ y₀ hx) _

/-- **The two-block commutator bound.** Recording in a qubit `B = ZMod 2` whether the database
answers `y₀` at `x₀` almost commutes with the truncated compressed oracle, up to `80 / |Y|`. -/
example [Fintype X] [AddCommGroup Y] (x₀ : X) (y₀ : Y) (t : ℕ) :
    ‖labelControlled (fun a ↦ (if answers x₀ y₀ a.1.2 then 1 else 0 : ZMod 2))
          (fun i ↦ (1 : Matrix ((X × Y) × Database X Y) ((X × Y) × Database X Y) ℂ) ⊗ₖ
            xorShift (ZMod 2) i) * (truncatedOracle X Y t ⊗ₖ (1 : Matrix (ZMod 2) (ZMod 2) ℂ)) -
        (truncatedOracle X Y t ⊗ₖ (1 : Matrix (ZMod 2) (ZMod 2) ℂ)) *
          labelControlled (fun a ↦ (if answers x₀ y₀ a.1.2 then 1 else 0 : ZMod 2))
            (fun i ↦ (1 : Matrix ((X × Y) × Database X Y) ((X × Y) × Database X Y) ℂ) ⊗ₖ
              xorShift (ZMod 2) i)‖ ^ 2 ≤ 80 / Fintype.card Y := by
  refine (l2_opNorm_commutator_xorMeasurement_sq_le
    (fun D ↦ (if answers x₀ y₀ D then 1 else 0 : ZMod 2)) t).trans ?_
  have hle : Database.instability (fun D ↦ (if answers x₀ y₀ D then 1 else 0 : ZMod 2)) t ≤
      Database.instability (answers x₀ y₀) t := by
    rw [Database.instability_eq_iSup, Database.instability_eq_iSup]
    refine iSup_le fun i ↦ iSup_le fun D ↦ iSup_le fun hi ↦ iSup_le fun hD ↦ iSup_le fun x ↦
      iSup_le fun hx ↦ ?_
    subst hi
    refine le_iSup_of_le (answers x₀ y₀ D) <| le_iSup_of_le D <| le_iSup_of_le rfl <|
      le_iSup_of_le hD <| le_iSup_of_le x <| le_iSup_of_le hx ?_
    refine ENNReal.div_le_div_right (Nat.cast_le.mpr (Finset.card_le_card fun u hu ↦ ?_)) _
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun h ↦ (Finset.mem_filter.mp hu).2 (by
      rw [h])⟩
  have h := ENNReal.toReal_mono (by simp) (hle.trans (instability_answers_le x₀ y₀ t))
  rw [ENNReal.toReal_inv, ENNReal.toReal_natCast] at h
  calc 80 * (Database.instability _ t).toReal ≤ 80 * (Fintype.card Y : ℝ)⁻¹ := by gcongr
    _ = 80 / Fintype.card Y := by ring

end twoBlock

/-! ## The trivial partition -/

section trivial

variable {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]
  [UniformAnswerMeasure (X →ₒ Y)] {E : Type} [Fintype E] [DecidableEq E]

/-- A constant labelling has instability `0`. -/
example (t : ℕ) : Database.instability (fun _ : Database X Y ↦ ()) t = 0 :=
  Database.instability_const () t

/-- **The trivial partition commutes.** The purified measurement of a constant label, with any
unitary `U` on the register `E`, commutes with the truncated compressed oracle. -/
example (t : ℕ) {U : Matrix E E ℂ} (hU : U ∈ unitaryGroup E ℂ) :
    labelControlled (fun a ↦ (fun _ : Database X Y ↦ ()) a.1.2)
        (fun _ ↦ (1 : Matrix ((X × Y) × Database X Y) ((X × Y) × Database X Y) ℂ) ⊗ₖ U) *
        (truncatedOracle X Y t ⊗ₖ (1 : Matrix E E ℂ)) =
      (truncatedOracle X Y t ⊗ₖ (1 : Matrix E E ℂ)) *
        labelControlled (fun a ↦ (fun _ : Database X Y ↦ ()) a.1.2)
          (fun _ ↦ (1 : Matrix ((X × Y) × Database X Y) ((X × Y) × Database X Y) ℂ) ⊗ₖ U) := by
  have h := l2_opNorm_commutator_purifiedMeasurement_sq_le (fun _ : Database X Y ↦ ()) t
    (U := fun _ ↦ U) fun _ ↦ hU
  rw [Database.instability_const, ENNReal.toReal_zero, mul_zero] at h
  exact sub_eq_zero.mp (norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp
    (le_antisymm h (sq_nonneg _))))

end trivial

/-! ## A concrete instance: one cell, one bit -/

section concrete

noncomputable local instance : UniformAnswerMeasure (Unit →ₒ ZMod 2) :=
  UniformAnswerMeasure.ofFiniteNonempty _

/-- The two-block partition at `y₀ = 0` has instability exactly `1 / 2` once a query is allowed:
from the empty database, the answer `0` leaves the class `false`. -/
example (t : ℕ) (ht : 1 ≤ t) : Database.instability (answers () (0 : ZMod 2)) t = 2⁻¹ := by
  refine le_antisymm ((instability_answers_le () 0 t).trans_eq (by simp)) ?_
  rw [Database.instability_eq_iSup]
  refine le_iSup_of_le false <| le_iSup_of_le Database.empty <| le_iSup_of_le (by decide) <|
    le_iSup_of_le (by rw [Database.size_empty]; omega) <| le_iSup_of_le () <|
      le_iSup_of_le rfl (le_of_eq ?_)
  have hcard : (Finset.univ.filter fun u : ZMod 2 ↦
      answers () 0 (Function.update Database.empty () (some u)) ≠ false).card = 1 := by
    decide
  rw [hcard]
  simp

/-- The finest partition, labelling each database by itself, has instability exactly `1` once a
query is allowed: every answer changes the database. -/
example (t : ℕ) (ht : 1 ≤ t) :
    Database.instability (fun D : Database Unit (ZMod 2) ↦ D) t = 1 := by
  refine le_antisymm (Database.instability_le_one _ t) ?_
  rw [Database.instability_eq_iSup]
  refine le_iSup_of_le Database.empty <| le_iSup_of_le Database.empty <| le_iSup_of_le rfl <|
    le_iSup_of_le (by rw [Database.size_empty]; omega) <| le_iSup_of_le () <|
      le_iSup_of_le rfl (le_of_eq ?_)
  have hcard : (Finset.univ.filter fun u : ZMod 2 ↦
      Function.update (Database.empty : Database Unit (ZMod 2)) () (some u) ≠
        Database.empty).card = 2 := by
    decide
  rw [hcard, ZMod.card]
  refine (ENNReal.div_self ?_ ?_).symm <;> simp

/-- With query bound `0` no database is admissible, and the instability is `0`. -/
example : Database.instability (fun D : Database Unit (ZMod 2) ↦ D) 0 = 0 :=
  Database.instability_zero _

end concrete

/-! ## Universe polymorphism

The block lemmas and Lemma 5.10 apply at any universe; only the statements involving the
instability need `X Y : Type`. -/

section universes

variable {X Y : Type 1} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]

example {t : ℕ} {m' m : (X × AddChar Y ℂ) × Database X Y}
    (h : truncatedPhaseOracle X Y t m' m ≠ 0) :
    (m'.1, Function.update m'.2 m'.1.1 none) = (m.1, Function.update m.2 m.1.1 none) :=
  phaseBlock_eq_of_truncatedPhaseOracle_ne_zero h

example {ι E : Type 1} [DecidableEq ι] [Fintype E] [DecidableEq E] (π : Database X Y → ι)
    (t : ℕ) {W : ι → Matrix (((X × Y) × Database X Y) × E) (((X × Y) × Database X Y) × E) ℂ}
    (hW : ∀ k a b, W k a b ≠ 0 → π a.1.2 = π b.1.2) (hU : ∀ k, W k ∈ unitaryGroup _ ℂ)
    (hA : ∀ k, W k * (truncatedOracle X Y t ⊗ₖ (1 : Matrix E E ℂ)) =
      (truncatedOracle X Y t ⊗ₖ (1 : Matrix E E ℂ)) * W k) :
    ‖labelControlled (fun a ↦ π a.1.2) W * (truncatedOracle X Y t ⊗ₖ (1 : Matrix E E ℂ)) -
        (truncatedOracle X Y t ⊗ₖ (1 : Matrix E E ℂ)) * labelControlled (fun a ↦ π a.1.2) W‖ ≤
      2 * ‖pinch (fun m : (X × Y) × Database X Y ↦ π m.2) (truncatedOracle X Y t) -
        truncatedOracle X Y t‖ :=
  l2_opNorm_commutator_truncatedOracle_le_pinch π t hW hU hA

end universes

end VCVioTest.InstabilityBound
