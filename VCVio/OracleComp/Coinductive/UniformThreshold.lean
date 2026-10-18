/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import VCVio.OracleComp.Coinductive.BitRealization
public import Mathlib.Data.Rat.Cast.Order

/-!
# A persistent uniform threshold implemented with fair bits

A dyadic prefix records the interval containing one persistent uniform value. A rational
threshold query returns as soon as this entire interval lies on one side of the threshold;
otherwise it reads another bit. The retained prefix is shared by subsequent queries.
All decisions use exact rational arithmetic. `runIO` uses the generic resumable machine
driver with an injected bit source. A bounded chunk keeps its residual prefix for resumption.
-/

public section

open OracleComp PFunctor

namespace UniformThreshold

/-- A dyadic cell of width `2⁻depth` in the unit interval. -/
structure Prefix where
  /-- Number of bits already read. -/
  depth : ℕ
  /-- Integer represented by those bits, most significant bit first. -/
  cell : ℕ
  /-- The encoded cell lies inside the unit interval. -/
  isLt : cell < 2 ^ depth
  deriving DecidableEq, Repr

namespace Prefix

instance : MeasurableSpace Prefix := ⊤

instance : DiscreteMeasurableSpace Prefix := ⟨fun _ => MeasurableSpace.measurableSet_top⟩

instance : Countable Prefix := Function.Injective.countable
    (f := fun p : Prefix => (p.depth, p.cell)) (by
  rintro ⟨n, a, h⟩ ⟨m, b, j⟩ e
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj e
  rfl)

/-- The empty bit prefix. -/
@[expose] def empty : Prefix := ⟨0, 0, by decide⟩

/-- The left endpoint, computed exactly. -/
@[expose] def lower (p : Prefix) : ℚ := p.cell / (2 : ℚ) ^ p.depth

/-- The excluded right endpoint, computed exactly. -/
@[expose] def upper (p : Prefix) : ℚ := (p.cell + 1) / (2 : ℚ) ^ p.depth

/-- Append one bit to the dyadic cell. -/
@[expose] def push (p : Prefix) (bit : Bool) : Prefix where
  depth := p.depth + 1
  cell := 2 * p.cell + if bit then 1 else 0
  isLt := by
    have h := p.isLt
    rw [pow_succ]
    cases bit <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega

/-- Each random-bit query increases the represented bit count by exactly one. -/
@[simp] theorem depth_push (p : Prefix) (b : Bool) : (p.push b).depth = p.depth + 1 := by rfl

/-- Dyadic cells have positive width. -/
theorem lower_lt_upper (p : Prefix) : p.lower < p.upper := by
  unfold lower upper
  exact (div_lt_div_iff_of_pos_right (by positivity)).mpr (by linarith)

/-- Appending zero leaves the lower endpoint unchanged. -/
@[simp] theorem lower_push_false (p : Prefix) : (p.push false).lower = p.lower := by
  simp only [push, lower, Bool.false_eq_true, ↓reduceIte, add_zero, Nat.cast_mul,
    Nat.cast_ofNat, pow_succ]
  field_simp

/-- The boundary between the two refinements is their common midpoint. -/
theorem upper_push_false_eq_lower_push_true (p : Prefix) :
    (p.push false).upper = (p.push true).lower := by
  simp [push, lower, upper]

/-- Appending one leaves the upper endpoint unchanged. -/
@[simp] theorem upper_push_true (p : Prefix) : (p.push true).upper = p.upper := by
  simp only [push, upper, ↓reduceIte, Nat.cast_add, Nat.cast_mul,
    Nat.cast_ofNat, Nat.cast_one, pow_succ]
  field_simp
  ring

end Prefix

/-- Decide `U < q` when the prefix determines it; `none` requests another bit. -/
@[expose] def classify (q : ℚ) (p : Prefix) : Option Bool :=
  if p.upper ≤ q then some true else if q ≤ p.lower then some false else none

/-- The fair-bit machine for a single query, preserving its refined prefix on return. -/
@[expose, implicit_reducible]
def machine (q : ℚ) : OracleMachine coinSpec Prefix (Bool × Prefix) :=
  DynSystem.DynComputation.ofStep (fun p => match classify q p with
    | some answer => .inl (answer, p)
    | none => .inr ⟨(), p.push⟩) id

/-- The machine exposes exactly a resolved answer or one fair-bit request. -/
theorem machine_view (q : ℚ) (p : Prefix) :
    (machine q).view p = match classify q p with
      | some answer => .inl (answer, p)
      | none => .inr ⟨(), p.push⟩ :=
  DynSystem.DynComputation.view_ofStep _ _ _

/-- Thresholds are rational queries with Boolean answers. -/
@[expose, reducible] def spec : OracleSpec ℚ := fun _ => Bool

/-- Executable rational-arithmetic machines, independent of the measure-valued service bundle. -/
@[expose, reducible] def machineHandler :
    MachineHandler spec.toPFunctor coinSpec.toPFunctor Prefix := machine

/-- Execute a query with an injected bit source, retaining the prefix across invocations. -/
def runIO (drawBit : IO Bool) (q : ℚ) (p : Prefix) : IO (Bool × Prefix) :=
  (machine q).runIO (fun _ => drawBit) p

/-- Every resolved true answer holds for every real in the represented interval. -/
theorem classify_true_sound (q : ℚ) (p : Prefix) (h : classify q p = some true)
    {u : ℝ} (hu : u < (p.upper : ℝ)) : u < (q : ℝ) := by
  have hq : p.upper ≤ q := by
    by_contra hq
    simp [classify, hq] at h
  exact hu.trans_le (by exact_mod_cast hq)

/-- Every resolved false answer holds for every real in the represented interval. -/
theorem classify_false_sound (q : ℚ) (p : Prefix) (h : classify q p = some false)
    {u : ℝ} (hu : (p.lower : ℝ) ≤ u) : (q : ℝ) ≤ u := by
  have hq : q ≤ p.lower := by
    by_contra hq
    simp [classify, hq] at h
  exact (by exact_mod_cast hq : (q : ℝ) ≤ (p.lower : ℝ)).trans hu

/-- A bit is requested only when the threshold lies strictly inside the dyadic cell. -/
theorem classify_eq_none_iff (q : ℚ) (p : Prefix) :
    classify q p = none ↔ p.lower < q ∧ q < p.upper := by
  unfold classify
  split_ifs <;> simp_all

/-- At most one of the two refined cells can still straddle the threshold. -/
theorem child_resolves (q : ℚ) (p : Prefix) :
    classify q (p.push false) ≠ none ∨ classify q (p.push true) ≠ none := by
  by_contra h
  push Not at h
  have hl := (classify_eq_none_iff q (p.push false)).mp h.1
  have hr := (classify_eq_none_iff q (p.push true)).mp h.2
  rw [Prefix.upper_push_false_eq_lower_push_true] at hl
  exact (lt_irrefl q) (hl.2.trans hr.1)

end UniformThreshold
