/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.OracleComp.Constructions.SampleableType.Measure

/-!
# Uniform samples: list membership and overwritten table coordinates

The list-membership bound is attained by a list without repetitions and counts a repeated entry
twice. The table couplings apply when the overwritten coordinate is the same twice, and need the
overwriting value to be uniform: overwriting with a constant changes the distribution.
-/

public section

open OracleComp ENNReal

namespace VCVioTest.SampleableTypeUpdate

/-- The bound is attained by a one-element list. -/
example : Pr{let x ← $ᵗ Bool}[x ∈ [true]] = 1 / Fintype.card Bool :=
  (prEvent_congr _ _ _ fun _ => List.mem_singleton).trans
    ((SampleableType.prEvent_uniformSample_eq_singleton true).trans (one_div _).symm)

example : Pr{let x ← $ᵗ Bool}[x ∈ [true]] ≤ [true].length / Fintype.card Bool :=
  SampleableType.prEvent_uniformSample_mem_le _

/-- A repeated entry is counted twice, so the bound for `[true, true]` is `1`, not the actual
`1 / 2`. -/
example : ([true, true].length : ℝ≥0∞) / Fintype.card Bool = 1 := by
  simpa using ENNReal.div_self two_ne_zero ofNat_ne_top

example (p : Bool × (Bool → Bool) → Prop) :
    Pr{let u ← $ᵗ Bool; let x ← $ᵗ (Bool × (Bool → Bool))}[
        p (x.1, Function.update x.2 true u)] =
      Pr{let x ← $ᵗ (Bool × (Bool → Bool))}[p x] :=
  SampleableType.prEvent_uniformSample_prod_update (R := fun _ : Bool => Bool) true p

/-- The two overwritten coordinates may coincide; the second value wins. -/
example (p : Unit × (Fin 3 → Bool) → Prop) :
    Pr{let u₀ ← $ᵗ Bool; let x ← $ᵗ (Unit × (Fin 3 → Bool)); let u₁ ← $ᵗ Bool}[
        p (x.1, Function.update (Function.update x.2 0 u₀) 0 u₁)] =
      Pr{let x ← $ᵗ (Unit × (Fin 3 → Bool))}[p x] :=
  SampleableType.prEvent_uniformSample_prod_update_update (R := fun _ : Fin 3 => Bool) 0 0 p

/-- Overwriting a coordinate with a constant, rather than a uniform value, changes the
distribution. -/
example :
    Pr{let x ← $ᵗ (Bool × (Bool → Bool))}[Function.update x.2 true true true = true] ≠
      Pr{let x ← $ᵗ (Bool × (Bool → Bool))}[x.2 true = true] := by
  rw [(SampleableType.prEvent_uniformSample_eq_one_iff _).2 fun _ => by simp, ne_comm, Ne,
    SampleableType.prEvent_uniformSample_eq_one_iff]
  exact fun h => Bool.false_ne_true (h (true, fun _ => false))

end VCVioTest.SampleableTypeUpdate
