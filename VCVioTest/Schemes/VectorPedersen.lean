/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.Schemes.VectorPedersen
public import Mathlib.Algebra.Field.ZMod

/-!
 # Vector Pedersen regression tests

Two-coordinate commitments over `ZMod 101` exercise the named relation and DLog reductions,
the generic bound, and perfect hiding at a generating blinding base. All fixtures are local.
-/

public section

open OracleComp OracleSpec CommitmentScheme DiscreteLogRelation
open scoped ENNReal

namespace VectorPedersen

/-- Two-coordinate binding over `ZMod 101` reduces to the named discrete-log adversary. -/
theorem binding_zmod_101 :
    letI : Fact (Nat.Prime 101) := ⟨by decide⟩
    ∀ binder : BindingAdversary (Option (Fin 2) → ZMod 101) (Fin 2 → ZMod 101)
        (ZMod 101) (ZMod 101),
      (scheme (uniformSetup (F := ZMod 101) 1)).bindingAdvantage binder ≤
        Pr{let b ← (DiffieHellman.dlogExperiment 1
          (plainReduction (bindingReduction binder)))}[b = true] + (1 / 101 : ℝ≥0∞) := by
  let : Fact (Nat.Prime 101) := ⟨by decide⟩
  intro binder
  simpa [ZMod.card] using bindingAdvantage_le_dlog (1 : ZMod 101)
    (by
      simp only [smul_eq_mul, mul_one]
      exact ⟨fun _ _ h => h, fun x => ⟨x, rfl⟩⟩) binder

/-- Blinding by `1` perfectly hides a two-coordinate message over arbitrary fixed message bases. -/
theorem hiding_zmod_101 :
    letI : Fact (Nat.Prime 101) := ⟨by decide⟩
    (scheme (F := ZMod 101)
      (pure (fun i : Option (Fin 2) => i.elim (1 : ZMod 101) ![3, 7]))).PerfectlyHiding := by
  let : Fact (Nat.Prime 101) := ⟨by decide⟩
  exact perfectlyHiding ![3, 7] (1 : ZMod 101)
    (by
      simp only [smul_eq_mul, mul_one]
      exact ⟨fun _ _ h => h, fun x => ⟨x, rfl⟩⟩)

/-- A free-equality generic binder on three initial bases has advantage at most `7 / 101`. -/
theorem generic_binding_zmod_101 :
    letI : Fact (Nat.Prime 101) := ⟨by decide⟩
    let A : GenericBinder (ZMod 101) (Fin 2) := show
      OracleComp (GroupModel.genSpec (ZMod 101) GroupModel.groupSig)
        (ℕ × (Fin 2 → ZMod 101) × ZMod 101 × (Fin 2 → ZMod 101) × ZMod 101) from do
      let eq : Bool ← (GroupModel.genSpec (ZMod 101) GroupModel.groupSig).query (.inl (.eq () 0 1))
      pure (0, ![1, 0], 0, (if eq then ![0, 1] else ![1, 0]), 0)
    (scheme (uniformSetup (F := ZMod 101) (ι := Fin 2) (1 : ZMod 101))).bindingAdvantage
      (ofGeneric A) ≤ (7 / 101 : ℝ≥0∞) := by
  let : Fact (Nat.Prime 101) := ⟨by decide⟩
  dsimp only
  apply (bindingAdvantage_ofGeneric_le (1 : ZMod 101) one_ne_zero _ 0 ?_).trans
  · norm_num [ZMod.card, Nat.choose]
  · exact ⟨by decide, fun _ => trivial⟩

end VectorPedersen
