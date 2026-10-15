/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.Quantum.Oracle.Compressed.CommutatorSharp
public import VCVio.Quantum.Oracle.Compressed.ProjectorEvent

/-!
# Instability and commutator-bound regression tests

[CDHZ] is A. Chiesa, Z. Di, Z. Hu and Y. Zheng, ePrint 2025/2166.

* **The two-block partition of Chiesa, Manohar and Spooner** (TCC 2019, Lemma 5.10): the
  databases with `D x₀ = y₀` against the rest. One fresh answer leaves the second class with
  probability at most `1 / |Y|` and never leaves the first, so the instability is at most
  `1 / |Y|`. In squared norm, the commutator of its XOR measurement with the truncated
  compressed oracle is at most `24 / |Y|` (and `80 / |Y|` with the constant of [CDHZ]), its
  pinching error and cross blocks are at most `6 / |Y|`, and a computation of total query mass
  `w` over `q` queries, with an inactive selector that applies the identity, reaches the class
  `true` from outside it with squared mass at most `6 q w / |Y|`.
* **The trivial partition**: a constant labelling has instability `0`, so the purified
  measurement and the label projector of a constant label commute exactly with the truncated
  compressed oracle, and its pinching is exact.
* **A concrete instance**, `X = Unit` and `Y = ZMod 2`: the two-block partition at `y₀ = 0` has
  instability exactly `1 / 2` for every query bound `t ≥ 1`, so its pinching error is at most
  `3` and its XOR commutator at most `12` in squared norm; the finest partition (the database
  itself) has instability exactly `1`, and both have instability `0` at query bound `0`.
* **Sharpness**: for `X = Unit`, `Y = ZMod 2` and the sign character, the scalar control of the
  labelling `D () = 1` has `‖[V, O^(t)]‖² ≥ 3`, so `5 I < ‖[V, O^(t)]‖²`; for four-bit answers
  (`N = 16`) the constant `20` fails.
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

/-- The two-block labelling as a bit. -/
def answersBit (x₀ : X) (y₀ : Y) (D : Database X Y) : ZMod 2 :=
  if answers x₀ y₀ D then 1 else 0

/-- The bit labelling coarsens the two-block labelling, so its instability is at most
`1 / |Y|`. -/
theorem instability_answersBit_le [Finite X] (x₀ : X) (y₀ : Y) (t : ℕ) :
    Database.instability (answersBit x₀ y₀) t ≤ (Fintype.card Y : ℝ≥0∞)⁻¹ :=
  (Database.instability_comp_le (fun b : Bool ↦ (if b then 1 else 0 : ZMod 2)) (answers x₀ y₀)
    t).trans (instability_answers_le x₀ y₀ t)

omit [DecidableEq Y] in
/-- An instability of at most `1 / |Y|` is at most `1 / |Y|` as a real number. -/
theorem toReal_instability_le_inv_card [Nonempty Y] {ι : Type*} {π : Database X Y → ι} {t : ℕ}
    (h : Database.instability π t ≤ (Fintype.card Y : ℝ≥0∞)⁻¹) :
    (Database.instability π t).toReal ≤ (Fintype.card Y : ℝ)⁻¹ := by
  have h' := ENNReal.toReal_mono (by simp [Fintype.card_ne_zero]) h
  rwa [ENNReal.toReal_inv, ENNReal.toReal_natCast] at h'

section sharp

variable [Fintype X] [AddCommGroup Y]

/-- **The two-block commutator bound.** Recording in a qubit whether the database answers `y₀` at
`x₀` almost commutes with the truncated compressed oracle, up to `24 / |Y|`. -/
example (x₀ : X) (y₀ : Y) (t : ℕ) :
    ‖labelControlled (fun a ↦ answersBit x₀ y₀ a.1.2)
          (fun i ↦ (1 : Matrix ((X × Y) × Database X Y) ((X × Y) × Database X Y) ℂ) ⊗ₖ
            xorShift (ZMod 2) i) * (truncatedOracle X Y t ⊗ₖ (1 : Matrix (ZMod 2) (ZMod 2) ℂ)) -
        (truncatedOracle X Y t ⊗ₖ (1 : Matrix (ZMod 2) (ZMod 2) ℂ)) *
          labelControlled (fun a ↦ answersBit x₀ y₀ a.1.2)
            (fun i ↦ (1 : Matrix ((X × Y) × Database X Y) ((X × Y) × Database X Y) ℂ) ⊗ₖ
              xorShift (ZMod 2) i)‖ ^ 2 ≤ 24 / Fintype.card Y := by
  refine (l2_opNorm_commutator_xorMeasurement_sq_le_twentyFour_mul (answersBit x₀ y₀) t).trans ?_
  calc 24 * (Database.instability (answersBit x₀ y₀) t).toReal ≤
        24 * (Fintype.card Y : ℝ)⁻¹ := by
        gcongr
        exact toReal_instability_le_inv_card (instability_answersBit_le x₀ y₀ t)
    _ = 24 / Fintype.card Y := by ring

/-- The constant `80` of [CDHZ, Theorem 5.4] gives `80 / |Y|` for the two-block XOR
measurement. -/
example (x₀ : X) (y₀ : Y) (t : ℕ) :
    ‖labelControlled (fun a ↦ answersBit x₀ y₀ a.1.2)
          (fun i ↦ (1 : Matrix ((X × Y) × Database X Y) ((X × Y) × Database X Y) ℂ) ⊗ₖ
            xorShift (ZMod 2) i) * (truncatedOracle X Y t ⊗ₖ (1 : Matrix (ZMod 2) (ZMod 2) ℂ)) -
        (truncatedOracle X Y t ⊗ₖ (1 : Matrix (ZMod 2) (ZMod 2) ℂ)) *
          labelControlled (fun a ↦ answersBit x₀ y₀ a.1.2)
            (fun i ↦ (1 : Matrix ((X × Y) × Database X Y) ((X × Y) × Database X Y) ℂ) ⊗ₖ
              xorShift (ZMod 2) i)‖ ^ 2 ≤ 80 / Fintype.card Y := by
  refine (l2_opNorm_commutator_xorMeasurement_sq_le (answersBit x₀ y₀) t).trans ?_
  have h := ENNReal.toReal_mono (by simp) (instability_answersBit_le x₀ y₀ t)
  rw [ENNReal.toReal_inv, ENNReal.toReal_natCast] at h
  calc 80 * (Database.instability (answersBit x₀ y₀) t).toReal ≤ 80 * (Fintype.card Y : ℝ)⁻¹ := by
        gcongr
    _ = 80 / Fintype.card Y := by ring

/-- **The sharp two-block pinching bound** of Chiesa, Manohar and Spooner (Lemma 5.10):
`‖pinch O^(t) - O^(t)‖² ≤ 6 / |Y|`. -/
example (x₀ : X) (y₀ : Y) (t : ℕ) :
    ‖pinch (fun m : (X × Y) × Database X Y ↦ answers x₀ y₀ m.2) (truncatedOracle X Y t) -
        truncatedOracle X Y t‖ ^ 2 ≤ 6 / Fintype.card Y := by
  refine (l2_opNorm_pinch_truncatedOracle_sub_sq_le_six_mul (answers x₀ y₀) t
    ⟨true, false, fun D ↦ by cases answers x₀ y₀ D <;> simp⟩).trans ?_
  calc 6 * (Database.instability (answers x₀ y₀) t).toReal ≤ 6 * (Fintype.card Y : ℝ)⁻¹ := by
        gcongr
        exact toReal_instability_le_inv_card (instability_answers_le x₀ y₀ t)
    _ = 6 / Fintype.card Y := by ring

/-- **The two-block cross block.** The part of the truncated oracle that moves a database out of
the class `false` into the class `true` has squared norm at most `6 / |Y|`. -/
example (x₀ : X) (y₀ : Y) (t : ℕ) :
    ‖labelProjector (fun m : (X × Y) × Database X Y ↦ answers x₀ y₀ m.2) true *
        truncatedOracle X Y t *
          labelProjector (fun m : (X × Y) × Database X Y ↦ answers x₀ y₀ m.2) false‖ ^ 2 ≤
      6 / Fintype.card Y := by
  refine (l2_opNorm_labelProjector_mul_truncatedOracle_mul_sq_le_six_mul (answers x₀ y₀) t
    (i := true) (j := false) (by decide)).trans ?_
  calc 6 * (Database.instability (answers x₀ y₀) t).toReal ≤ 6 * (Fintype.card Y : ℝ)⁻¹ := by
        gcongr
        exact toReal_instability_le_inv_card (instability_answers_le x₀ y₀ t)
    _ = 6 / Fintype.card Y := by ring

/-- **The two-block event bound.** A computation with a selector qubit `κ = Bool` queries the
truncated oracle on the selector `true` and applies the identity on the inactive selector
`false`. If its other operations commute with the projector onto the class `true` and it starts
outside that class, the squared mass of the final state in that class is at most `6 q w / |Y|`,
where `w` is the total mass on the selector `true` before the queries. -/
example {E : Type} [Fintype E] [DecidableEq E] (x₀ : X) (y₀ : Y) (t q : ℕ)
    (ψ : ℕ → (((X × Y) × Database X Y) × E) × Bool → ℂ)
    (A : ℕ → Matrix ((((X × Y) × Database X Y) × E) × Bool) ((((X × Y) × Database X Y) × E) × Bool)
      ℂ)
    (hA : ∀ j < q, ‖A j‖ ≤ 1)
    (hAQ : ∀ j < q, A j * blockDiagonal (fun _ ↦ labelProjector
        (fun m : (X × Y) × Database X Y ↦ answers x₀ y₀ m.2) true ⊗ₖ (1 : Matrix E E ℂ)) =
      blockDiagonal (fun _ ↦ labelProjector
        (fun m : (X × Y) × Database X Y ↦ answers x₀ y₀ m.2) true ⊗ₖ (1 : Matrix E E ℂ)) * A j)
    (hψ : ∀ j < q, ψ (j + 1) =
      A j *ᵥ (blockDiagonal (fun k : Bool ↦
        if k then truncatedOracle X Y t ⊗ₖ (1 : Matrix E E ℂ) else 1) *ᵥ ψ j))
    (h0 : blockDiagonal (fun _ ↦ labelProjector
        (fun m : (X × Y) × Database X Y ↦ answers x₀ y₀ m.2) true ⊗ₖ (1 : Matrix E E ℂ)) *ᵥ
      ψ 0 = 0) :
    ∑ a, ‖(blockDiagonal (fun _ ↦ labelProjector
        (fun m : (X × Y) × Database X Y ↦ answers x₀ y₀ m.2) true ⊗ₖ (1 : Matrix E E ℂ)) *ᵥ
          ψ q) a‖ ^ 2 ≤
      6 * q * (Fintype.card Y : ℝ)⁻¹ *
        ∑ j ∈ Finset.range q, ∑ k ∈ ({true} : Finset Bool), ∑ x, ‖ψ j (x, k)‖ ^ 2 := by
  refine (sum_norm_labelProjector_mulVec_sq_le_six_mul_mul_sum (answers x₀ y₀) t true
    {true} q ψ A (fun _ k ↦ if k then truncatedOracle X Y t ⊗ₖ (1 : Matrix E E ℂ) else 1) hA hAQ
    (fun _ _ k hk ↦ by simp [Finset.mem_singleton.mp hk])
    (fun _ _ k hk ↦ by simp [Finset.mem_singleton.not.mp hk, l2_opNorm_one_le])
    (fun _ _ k hk ↦ by simp [Finset.mem_singleton.not.mp hk]) hψ h0).trans ?_
  have hw : 0 ≤ ∑ j ∈ Finset.range q, ∑ k ∈ ({true} : Finset Bool), ∑ x, ‖ψ j (x, k)‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦
      Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  have hI := toReal_instability_le_inv_card (instability_answers_le x₀ y₀ t)
  gcongr

end sharp

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

/-- **The label projector of a constant label commutes** with the truncated compressed oracle, by
the projector commutator bound `6 I`. -/
example (t : ℕ) :
    labelProjector (fun m : (X × Y) × Database X Y ↦ (fun _ : Database X Y ↦ ()) m.2) () *
        truncatedOracle X Y t =
      truncatedOracle X Y t *
        labelProjector (fun m : (X × Y) × Database X Y ↦ (fun _ : Database X Y ↦ ()) m.2) () := by
  have h := l2_opNorm_labelProjector_commutator_truncatedOracle_sq_le_six_mul
    (fun _ : Database X Y ↦ ()) t ()
  rw [Database.instability_const, ENNReal.toReal_zero, mul_zero] at h
  exact sub_eq_zero.mp (norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp
    (le_antisymm h (sq_nonneg _))))

/-- **The pinching of a constant label is exact**, by the sharp pinching bound `8 I`. -/
example (t : ℕ) :
    pinch (fun m : (X × Y) × Database X Y ↦ (fun _ : Database X Y ↦ ()) m.2)
      (truncatedOracle X Y t) = truncatedOracle X Y t := by
  have h := l2_opNorm_pinch_truncatedOracle_sub_sq_le_eight_mul (fun _ : Database X Y ↦ ()) t
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
theorem instability_answers_unit_zero (t : ℕ) (ht : 1 ≤ t) :
    Database.instability (answers () (0 : ZMod 2)) t = 2⁻¹ := by
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

/-- With one cell and one bit, the two-block pinching error is at most `6 · 1 / 2 = 3`. -/
example (t : ℕ) (ht : 1 ≤ t) :
    ‖pinch (fun m : (Unit × ZMod 2) × Database Unit (ZMod 2) ↦ answers () (0 : ZMod 2) m.2)
        (truncatedOracle Unit (ZMod 2) t) - truncatedOracle Unit (ZMod 2) t‖ ^ 2 ≤ 3 := by
  refine (l2_opNorm_pinch_truncatedOracle_sub_sq_le_six_mul (answers () (0 : ZMod 2)) t
    ⟨true, false, fun D ↦ by cases answers () (0 : ZMod 2) D <;> simp⟩).trans_eq ?_
  rw [instability_answers_unit_zero t ht, ENNReal.toReal_inv, ENNReal.toReal_ofNat]
  norm_num

/-- With one cell and one bit, the two-block XOR commutator is at most `24 · 1 / 2 = 12`. -/
example (t : ℕ) (ht : 1 ≤ t) :
    ‖labelControlled (fun a ↦ answersBit () (0 : ZMod 2) a.1.2)
          (fun i ↦ (1 : Matrix ((Unit × ZMod 2) × Database Unit (ZMod 2))
            ((Unit × ZMod 2) × Database Unit (ZMod 2)) ℂ) ⊗ₖ xorShift (ZMod 2) i) *
          (truncatedOracle Unit (ZMod 2) t ⊗ₖ (1 : Matrix (ZMod 2) (ZMod 2) ℂ)) -
        (truncatedOracle Unit (ZMod 2) t ⊗ₖ (1 : Matrix (ZMod 2) (ZMod 2) ℂ)) *
          labelControlled (fun a ↦ answersBit () (0 : ZMod 2) a.1.2)
            (fun i ↦ (1 : Matrix ((Unit × ZMod 2) × Database Unit (ZMod 2))
              ((Unit × ZMod 2) × Database Unit (ZMod 2)) ℂ) ⊗ₖ xorShift (ZMod 2) i)‖ ^ 2 ≤
      12 := by
  refine (l2_opNorm_commutator_xorMeasurement_sq_le_twentyFour_mul (answersBit () (0 : ZMod 2))
    t).trans ?_
  have h := Database.instability_comp_le (fun b : Bool ↦ (if b then 1 else 0 : ZMod 2))
    (answers () (0 : ZMod 2)) t
  rw [instability_answers_unit_zero t ht] at h
  have h' := ENNReal.toReal_mono (by simp) h
  rw [ENNReal.toReal_inv, ENNReal.toReal_ofNat] at h'
  calc 24 * (Database.instability (answersBit () (0 : ZMod 2)) t).toReal ≤ 24 * 2⁻¹ := by
        gcongr
        exact h'
    _ = 12 := by norm_num

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

/-- **The sharp lower bound, one cell and one bit.** Labelling by whether the database answers
`1` and controlling the sign by that label gives `‖[V, O^(t)]‖² ≥ 24 / 2 - 36 / 2² = 3`. -/
example (t : ℕ) (ht : 1 ≤ t) :
    3 ≤ ‖labelControlled
            (fun m : (Unit × ZMod 2) × Database Unit (ZMod 2) ↦ decide (m.2 () = some 1))
            (fun b ↦ (if b then -1 else 1 : ℂ) • (1 : Matrix _ _ ℂ)) *
            truncatedOracle Unit (ZMod 2) t -
          truncatedOracle Unit (ZMod 2) t *
            labelControlled
              (fun m : (Unit × ZMod 2) × Database Unit (ZMod 2) ↦ decide (m.2 () = some 1))
              (fun b ↦ (if b then -1 else 1 : ℂ) • (1 : Matrix _ _ ℂ))‖ ^ 2 := by
  refine le_trans (le_of_eq ?_) (le_l2_opNorm_commutator_truncatedOracle_sq () signChar_one ht)
  rw [ZMod.card]
  norm_num

/-- **The constant `5` fails for one cell and one bit.** The instability of the same labelling is
at most `1 / 2`, so `5 I < ‖[V, O^(t)]‖²`; with `N = 2` every constant below `6` fails. -/
example (t : ℕ) (ht : 1 ≤ t) :
    5 * (Database.instability (fun D : Database Unit (ZMod 2) ↦ decide (D () = some 1)) t).toReal <
      ‖labelControlled
            (fun m : (Unit × ZMod 2) × Database Unit (ZMod 2) ↦ decide (m.2 () = some 1))
            (fun b ↦ (if b then -1 else 1 : ℂ) • (1 : Matrix _ _ ℂ)) *
            truncatedOracle Unit (ZMod 2) t -
          truncatedOracle Unit (ZMod 2) t *
            labelControlled
              (fun m : (Unit × ZMod 2) × Database Unit (ZMod 2) ↦ decide (m.2 () = some 1))
              (fun b ↦ (if b then -1 else 1 : ℂ) • (1 : Matrix _ _ ℂ))‖ ^ 2 :=
  mul_instability_lt_l2_opNorm_commutator_truncatedOracle_sq () signChar_one ht (by norm_num)
    (by rw [ZMod.card]; norm_num)

end concrete

/-! ## Sixteen answers: the constant `20` fails -/

section sixteen

noncomputable local instance : UniformAnswerMeasure (Unit →ₒ (Fin (3 + 1) → ZMod 2)) :=
  UniformAnswerMeasure.ofFiniteNonempty _

/-- **The constant `20` of [CDHZ, Lemma 5.9] fails for the commutator** with four-bit answers
(`N = 16 ≥ 10`): some answer `y₀` makes `20 I < ‖[V, O^(t)]‖²`. -/
example (t : ℕ) (ht : 1 ≤ t) :
    ∃ y₀ : Fin (3 + 1) → ZMod 2,
      20 * (Database.instability
          (fun D : Database Unit (Fin (3 + 1) → ZMod 2) ↦ decide (D () = some y₀)) t).toReal <
        ‖labelControlled (fun m : (Unit × (Fin (3 + 1) → ZMod 2)) ×
              Database Unit (Fin (3 + 1) → ZMod 2) ↦ decide (m.2 () = some y₀))
              (fun b ↦ (if b then -1 else 1 : ℂ) • (1 : Matrix _ _ ℂ)) *
              truncatedOracle Unit (Fin (3 + 1) → ZMod 2) t -
            truncatedOracle Unit (Fin (3 + 1) → ZMod 2) t *
              labelControlled (fun m : (Unit × (Fin (3 + 1) → ZMod 2)) ×
                Database Unit (Fin (3 + 1) → ZMod 2) ↦ decide (m.2 () = some y₀))
                (fun b ↦ (if b then -1 else 1 : ℂ) • (1 : Matrix _ _ ℂ))‖ ^ 2 := by
  obtain ⟨χ, y₀, hχ⟩ := exists_addChar_eq_neg_one_bitString 3
  exact ⟨y₀, twenty_mul_instability_lt_l2_opNorm_commutator_truncatedOracle_sq () hχ ht
    (by simp [ZMod.card])⟩

end sixteen

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
