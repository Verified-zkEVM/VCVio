/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import VCVio.Quantum.Comp.ChargeWeight

/-!
# Prefix charge and total-weight regressions

An oracle call with no possible classical answer still spends its charge before its
continuation. Charging it zero permits the call, but does not remove it from the program.
Its exact total weight includes its pre-answer input even when execution then aborts.
-/

public section

open Quantum Matrix
open scoped ENNReal ComplexOrder

namespace VCVioTest.QuantumChargeWeight

/-- The oracle accepts a trivial register but never returns a classical answer. -/
@[expose, reducible]
def blockedSpec : QuantumOracleSpec where
  Port := Unit
  In _ := QReg.of Unit
  Out _ := QReg.of Unit
  Result _ := Empty

/-- The continuation is empty, but the query itself is present. -/
noncomputable def blocked :
    QuantumComp LocalSig.instruments blockedSpec (fun _ ↦ Unit) (QReg.of Unit) :=
  QuantumComp.queryBind () (QReg.of Unit) (Equiv.prodPUnit Unit).symm fun r ↦ nomatch r

/-- The initial call needs three units of charge despite having no continuation cases. -/
example (n : ℕ) : blocked.IsQueryChargeBound (fun _ ↦ 3) n ↔ 3 ≤ n := by
  simp [blocked, blockedSpec]

/-- An insufficient prefix budget cannot be justified by an impossible answer. -/
example : ¬ blocked.IsQueryChargeBound (fun _ ↦ 3) 2 := by
  simp [blocked, blockedSpec]

/-- Zero-charge calls remain legal at budget zero. -/
example : blocked.IsQueryChargeBound (fun _ ↦ 0) 0 := by
  simp [blocked, blockedSpec]

/-- The same program still makes one query and rejects a zero total-call budget. -/
example : blocked.IsTotalQueryBound 1 ∧ ¬ blocked.IsTotalQueryBound 0 := by
  simp [blocked, blockedSpec]

/-- The unit-charge API counts the one actual query. -/
example : blocked.IsQueryChargeBound (fun _ ↦ 1) 1 :=
  (QuantumComp.isQueryChargeBound_one_iff blocked 1).mpr (by simp [blocked, blockedSpec])

/-- Total weight includes the pre-answer query input even when no answer exists. -/
example (R : QuantumRuntime blockedSpec)
    (ρ : Matrix ((QReg.of Unit) × R.D) ((QReg.of Unit) × R.D) ℂ) :
    R.totalWeight .instruments (fun _ σ ↦ 3 * ENNReal.ofReal σ.trace.re) blocked ρ =
      3 * ENNReal.ofReal ρ.trace.re := by
  rw [blocked, QuantumRuntime.totalWeight_queryBind]
  simp [blockedSpec]

/-- The generic mass estimate handles the same aborting call with the precise prefix charge. -/
example (R : QuantumRuntime blockedSpec)
    (ρ : Matrix ((QReg.of Unit) × R.D) ((QReg.of Unit) × R.D) ℂ) (hρ : ρ.PosSemidef) :
    R.totalWeight .instruments (fun _ σ ↦ 3 * ENNReal.ofReal σ.trace.re) blocked ρ ≤
      3 * ENNReal.ofReal ρ.trace.re :=
  R.totalWeight_le_of_isQueryChargeBound .instruments (fun _ ↦ 3)
    (fun _ _ _ ↦ le_rfl) (by simp [blocked, blockedSpec]) hρ

end VCVioTest.QuantumChargeWeight
