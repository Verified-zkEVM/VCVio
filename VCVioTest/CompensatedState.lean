/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: VCVio Contributors
-/

module

public import VCVio.OracleComp.SimSemantics.StateT.Compensated
public import VCVio.OracleComp.Constructions.SampleableType.Measure

/-!
# Expected reserve on an adaptive early return

Each true bit increments both counters. A false first reply stops the run immediately,
so the estimate also covers paths that return after one call.
-/

public section

open OracleSpec OracleComp
open scoped ENNReal

namespace VCVioTest.CompensatedState

/-- Each call increments both counters by its sampled bit, then returns that same bit. -/
@[expose] noncomputable def tick : QueryImpl (Unit →ₒ Bool) (StateT (Nat × Nat) ProbComp) :=
  fun _ => StateT.mk fun s =>
    (fun b : Bool => (b, (s.1 + b.toNat, s.2 + b.toNat))) <$> ($ᵗ Bool)

/-- A false first coin stops the caller; a true first coin causes a second query. -/
@[expose] def untilFalse : OracleComp (Unit →ₒ Bool) Bool := do
  if ← query (spec := Unit →ₒ Bool) () then query (spec := Unit →ₒ Bool) () else pure false

/-- With equal starting counters, the expected reserve covers the caller's expected charge. -/
theorem early_return (n : Nat) :
    let run := (simulateQ tick untilFalse).run (n, n)
    (∑' z, Pr{let u ← run}[u = z] * (z.2.1 : ℝ≥0∞)) + n ≤ n +
      ∑' z, Pr{let u ← run}[u = z] * (z.2.2 : ℝ≥0∞) := by
  let I := fun s : Nat × Nat => s.1 = s.2
  have preserves : tick.PreservesInv I := by
    rintro _ ⟨l, r⟩ equal z hz
    simp only [tick, StateT.run_mk, support_map] at hz
    obtain ⟨b, _, rfl⟩ := hz
    exact congrArg (· + b.toNat) equal
  apply QueryImpl.run_compensated tick I preserves (fun s => s.1) (fun s => s.2)
    (fun _ _ => ENNReal.natCast_ne_top _) _ untilFalse _ rfl
  intro t s inv
  have eq : (∑' z, Pr{let u ← (tick t).run s}[u = z] * (z.2.1 : ℝ≥0∞)) =
      ∑' z, Pr{let u ← (tick t).run s}[u = z] * (z.2.2 : ℝ≥0∞) := by
    apply tsum_congr
    intro z
    by_cases seen : z ∈ support ((tick t).run s)
    · rw [show z.2.1 = z.2.2 from preserves t s inv z seen]
    · simp [prEvent_eq_zero_of_not_mem_support _ seen]
  rw [eq, show s.1 = s.2 from inv, add_comm]

end VCVioTest.CompensatedState
