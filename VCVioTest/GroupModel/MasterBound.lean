/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.CryptoFoundations.GroupModel.MasterBound
public import Mathlib.Algebra.Field.ZMod

/-!
Sharpness of the master bound at a zero default

Over `ZMod 5`, comparing the single polynomial `X` with the out-of-range handle `1`
attains the `1/5` collision bound with no group operations.
-/

public section

open OracleComp OracleSpec MeasureTheory
open scoped ENNReal

namespace GroupModel

private theorem uniform_unit_zero :
    Pr{let x ← $ᵗ (Unit → ZMod 5)}[x () = 0] = (1 / 5 : ℝ≥0∞) := by
  have he : ∀ x : Unit → ZMod 5, x () = 0 ↔ x = fun _ => 0 := by
    intro x
    constructor
    · intro h
      funext u
      cases u
      exact h
    · rintro rfl
      rfl
  rw [prEvent_congr _ _ _ he, SampleableType.prEvent_uniformSample_eq_singleton]
  simp [ZMod.card]

/-- On `[X]`, the free equality query `eq 0 1` attains the master bound `1/5`, including the
hidden point and full table in the observed output. -/
theorem masterBound_zero_default :
    let tbl : Tbl (fun _ : Unit => MvPolynomial Unit (ZMod 5)) := fun _ => [MvPolynomial.X ()]
    let oa : OracleComp (genSpec (ZMod 5) groupSig) Bool :=
      (genSpec (ZMod 5) groupSig).query (.inl (.eq () 0 1))
    let M := symbolic (ZMod 5) groupSig Unit
    let : MeasurableSpace ((Unit → ZMod 5) ×
      (Bool × Tbl (fun _ : Unit => MvPolynomial Unit (ZMod 5)))) := ⊤
    measureETVDist
      (do let x ← $ᵗ (Unit → ZMod 5)
          let z ← runGen M (fun _ p => MvPolynomial.eval x p) oa tbl
          pure (x, z))
      (do let x ← $ᵗ (Unit → ZMod 5)
          let z ← runGen M (fun _ => id) oa tbl
          pure (x, z)) = 1 / 5 ∧
      (((1 + 0 + 1).choose 2 : ℕ) : ℝ≥0∞) * (1 / 5) = 1 / 5 := by
  let : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  dsimp only
  let tbl : Tbl (fun _ : Unit => MvPolynomial Unit (ZMod 5)) := fun _ => [MvPolynomial.X ()]
  let oa : OracleComp (genSpec (ZMod 5) groupSig) Bool :=
    (genSpec (ZMod 5) groupSig).query (.inl (.eq () 0 1))
  let : MeasurableSpace ((Unit → ZMod 5) ×
    (Bool × Tbl (fun _ : Unit => MvPolynomial Unit (ZMod 5)))) := ⊤
  have hq : IsQueryBoundP oa (fun i => isGroupOp i = true) 0 := by
    exact ⟨by decide, fun _ => trivial⟩
  have hd : DegreeLE (fun _ => 1) tbl := by
    intro s p hp
    simp only [tbl, List.mem_singleton] at hp
    subst p
    simp
  have h := measureETVDist_runGen_symbolic_uniform_le oa hq tbl hd
  constructor
  · apply le_antisymm
    · simpa [tbl, oa, ZMod.card, groupSig, discreteSig] using h
    · let M := symbolic (ZMod 5) groupSig Unit
      let left : ProbComp ((Unit → ZMod 5) ×
          (Bool × Tbl (fun _ : Unit => MvPolynomial Unit (ZMod 5)))) := do
        let x ← $ᵗ (Unit → ZMod 5)
        let z ← runGen M (fun _ p => MvPolynomial.eval x p) oa tbl
        pure (x, z)
      let right : ProbComp ((Unit → ZMod 5) ×
          (Bool × Tbl (fun _ : Unit => MvPolynomial Unit (ZMod 5)))) := do
        let x ← $ᵗ (Unit → ZMod 5)
        let z ← runGen M (fun _ => id) oa tbl
        pure (x, z)
      have ho (x : Unit → ZMod 5) :
          runGen M (fun _ p => MvPolynomial.eval x p) oa tbl =
            pure (decide (x () = 0), tbl) := by
        change (pure (decide (MvPolynomial.eval x (MvPolynomial.X ()) =
          MvPolynomial.eval x 0), tbl) :
          ProbComp (Bool × Tbl (fun _ : Unit => MvPolynomial Unit (ZMod 5)))) =
            pure (decide (x () = 0), tbl)
        simp
      have he : runGen M (fun _ => id) oa tbl = pure (false, tbl) := by
        change (pure (decide ((MvPolynomial.X () : MvPolynomial Unit (ZMod 5)) = 0), tbl) :
          ProbComp (Bool × Tbl (fun _ : Unit => MvPolynomial Unit (ZMod 5)))) = pure (false, tbl)
        simp [MvPolynomial.X_ne_zero]
      have hl : Pr{let w ← left}[w.2.1 = true] = (1 / 5 : ℝ≥0∞) := by
        simpa [left, ho] using uniform_unit_zero
      have hr : Pr{let w ← right}[w.2.1 = true] = 0 := by simp [right, he]
      have hv := prEvent_le_prEvent_add_measureETVDist left right
        (fun w => w.2.1 = true) Measurable.of_discrete
      rw [hl, hr, zero_add] at hv
      exact hv
  · norm_num

/-- The exact run's collision probability averaged over the uniform hidden point is
exactly `1/5`: the polynomial `X` collides with the zero default precisely at zero. -/
theorem masterBound_collision_attained :
    let tbl : Tbl (fun _ : Unit => MvPolynomial Unit (ZMod 5)) := fun _ => [MvPolynomial.X ()]
    let oa : OracleComp (genSpec (ZMod 5) groupSig) Bool :=
      (genSpec (ZMod 5) groupSig).query (.inl (.eq () 0 1))
    let : MeasurableSpace (Unit → ZMod 5) := ⊤
    (∫⁻ x, collisionProbGen (symbolic (ZMod 5) groupSig Unit)
      (fun _ p => MvPolynomial.eval x p) oa tbl ∂𝒟[($ᵗ (Unit → ZMod 5) :
        ProbComp (Unit → ZMod 5))]) = 1 / 5 := by
  let : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  dsimp only
  let tbl : Tbl (fun _ : Unit => MvPolynomial Unit (ZMod 5)) := fun _ => [MvPolynomial.X ()]
  let oa : OracleComp (genSpec (ZMod 5) groupSig) Bool :=
    (genSpec (ZMod 5) groupSig).query (.inl (.eq () 0 1))
  let : MeasurableSpace (Unit → ZMod 5) := ⊤
  have hc (x : Unit → ZMod 5) :
      collisionProbGen (symbolic (ZMod 5) groupSig Unit)
        (fun _ p => MvPolynomial.eval x p) oa tbl =
      Pr{let _ ← (pure () : ProbComp Unit)}[x () = 0] := by
    change Pr{let z ← (pure
      (decide ((MvPolynomial.X () : MvPolynomial Unit (ZMod 5)) = 0), tbl,
        decide ((MvPolynomial.X () : MvPolynomial Unit (ZMod 5)) ≠ 0 ∧
          MvPolynomial.eval x (MvPolynomial.X ()) = MvPolynomial.eval x 0)) :
        ProbComp (Bool × Tbl (fun _ : Unit => MvPolynomial Unit (ZMod 5)) × Bool))}[
      z.2.2 = true] = _
    simp [MvPolynomial.X_ne_zero]
  change (∫⁻ x, collisionProbGen (symbolic (ZMod 5) groupSig Unit)
    (fun _ p => MvPolynomial.eval x p) oa tbl ∂𝒟[($ᵗ (Unit → ZMod 5) :
      ProbComp (Unit → ZMod 5))]) = _
  simp_rw [hc]
  rw [← prEvent_bind_of_discrete ($ᵗ (Unit → ZMod 5)) (fun x => pure (x () = 0))]
  simpa only [bind_pure_comp] using uniform_unit_zero

end GroupModel
