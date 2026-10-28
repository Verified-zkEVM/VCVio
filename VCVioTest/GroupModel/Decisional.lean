/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.CryptoFoundations.GroupModel.GenericDDH
public import Mathlib.Algebra.Field.ZMod

/-! # Relation-kernel examples and table-length separation

The DDH polynomial lists have the same linear relations, while repeated variables
introduce a relation. Zero padding preserves the relation kernel but is observable
through the fresh handle returned by a group operation.
-/

public section

open OracleComp OracleSpec MeasureTheory MvPolynomial
open scoped ENNReal

namespace GroupModel

private instance : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

/-- Repeating one variable creates a linear relation absent from independent variables. -/
theorem repeated_variable_not_sameKernel :
    letI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
    ¬ SameKernel (F := ZMod 5) (ι := Fin 3)
      (fun _ : Unit => [1, X 0, X 0]) (fun _ : Unit => [1, X 0, X 1]) := by
  intro h
  have he := h.eq_iff () (Pi.single 1 1) (Pi.single 2 1)
  simp [evRepr_apply, Pi.single_apply] at he

/-- Uniform generic DDH runs on the two four-entry tables differ by at most
`3 * choose (4 + q + 1) 2 / 5`, jointly with the hidden point. -/
theorem ddh_uniform_bound {α : Type} [MeasurableSpace (((Fin 3) → ZMod 5) × α)]
    {q : ℕ} (oa : OracleComp (genSpec (ZMod 5) groupSig) α)
    (hq : IsQueryBoundP oa (fun i => isGroupOp i = true) q) :
    measureETVDist
      (do let x ← $ᵗ ((Fin 3) → ZMod 5)
          let z ← runGen (symbolic (ZMod 5) groupSig (Fin 3))
            (fun _ p => MvPolynomial.eval x p) oa (fun _ => [1, X 0, X 1, X 0 * X 1])
          pure (x, z.1))
      (do let x ← $ᵗ ((Fin 3) → ZMod 5)
          let z ← runGen (symbolic (ZMod 5) groupSig (Fin 3))
            (fun _ p => MvPolynomial.eval x p) oa (fun _ => [1, X 0, X 1, X 2])
          pure (x, z.1)) ≤ 3 * ((4 + q + 1).choose 2 : ℝ≥0∞) / 5 := by
  let : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hb := measureETVDist_runGen_sameKernel_uniform_le oa hq
    (fun _ => [1, X 0, X 1, X 0 * X 1]) (fun _ => [1, X 0, X 1, X 2])
    ddhTables_degreeLE.1 ddhTables_degreeLE.2 ddhTables_sameKernel
  calc
    _ ≤ ((4 + q + 1).choose 2 : ℝ≥0∞) * (2 / 5) +
        ((4 + q + 1).choose 2 : ℝ≥0∞) * (1 / 5) := by
      simpa [ZMod.card, groupSig, discreteSig] using hb
    _ = _ := by
      simp only [div_eq_mul_inv]
      rw [← mul_add, ← add_mul]
      norm_num
      ac_rfl

/-- The vanishing condition alone cannot hide unequal lengths: a fresh handle separates
empty and singleton-zero tables with joint uniform-run distance one. -/
theorem empty_zero_uniform_separation :
    letI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
    let T₀ : Tbl (fun _ : Unit => MvPolynomial (Fin 3) (ZMod 5)) := fun _ => []
    let T₁ : Tbl (fun _ : Unit => MvPolynomial (Fin 3) (ZMod 5)) := fun _ => [0]
    let oa : OracleComp (genSpec (ZMod 5) groupSig) Handle :=
      (genSpec (ZMod 5) groupSig).query (.inl (.add () 0 0))
    let : MeasurableSpace (((Fin 3) → ZMod 5) × Handle) := ⊤
    (∀ s (r : Repr (ZMod 5)), evRepr (T₀ s) r = 0 ↔ evRepr (T₁ s) r = 0) ∧
    ¬ SameKernel T₀ T₁ ∧
    measureETVDist
      (do let x ← $ᵗ ((Fin 3) → ZMod 5)
          let z ← runGen (symbolic (ZMod 5) groupSig (Fin 3))
            (fun _ p => MvPolynomial.eval x p) oa T₀
          pure (x, z.1))
      (do let x ← $ᵗ ((Fin 3) → ZMod 5)
          let z ← runGen (symbolic (ZMod 5) groupSig (Fin 3))
            (fun _ p => MvPolynomial.eval x p) oa T₁
          pure (x, z.1)) = 1 := by
  dsimp only
  refine ⟨by simp [evRepr_apply], ?_, ?_⟩
  · intro h
    have hl := (h ()).1
    simp at hl
  · let : MeasurableSpace (((Fin 3) → ZMod 5) × Handle) := ⊤
    let left : ProbComp (((Fin 3) → ZMod 5) × Handle) := do
      let x ← $ᵗ ((Fin 3) → ZMod 5)
      pure (x, 0)
    let right : ProbComp (((Fin 3) → ZMod 5) × Handle) := do
      let x ← $ᵗ ((Fin 3) → ZMod 5)
      pure (x, 1)
    change measureETVDist left right = 1
    apply le_antisymm (measureETVDist_le_one left right)
    have h := prEvent_le_prEvent_add_measureETVDist left right
      (fun w => w.2 = 0) Measurable.of_discrete
    simpa [left, right] using h

end GroupModel
