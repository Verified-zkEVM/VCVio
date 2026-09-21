/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio
public import VCVio.Native

/-!
# Instance search under the full library

The clients of `VCVioTest.OracleComp.SpecInstanceSearch`, repeated with the native probability
surface and the whole library (including its compatibility instances) in scope.
-/

public section

universe u

namespace VCVioTest.OracleComp.SpecInstanceSearchNative

set_option synthInstance.maxHeartbeats 2000 in
-- A reintroduced search loop must fail here rather than eventually succeed (VCVio#772).
theorem classical_if_le {F : Type} [Field F] (x y : F) : ∃ n : ℕ, n ≤ 1 := by
  classical
  exact ⟨if x = y then 1 else 0, by split <;> simp⟩

set_option synthInstance.maxHeartbeats 2000 in
-- A reintroduced search loop must fail here rather than eventually succeed (VCVio#772).
noncomputable example {α : Type u} : DecidableEq α := by
  classical
  infer_instance

set_option synthInstance.maxHeartbeats 2000 in
-- A reintroduced search loop must fail here rather than eventually succeed (VCVio#772).
open Classical in
theorem card_filter_le {F : Type} [Field F] [Fintype F] (p : F → Prop) :
    (Finset.univ.filter p).card ≤ Fintype.card F :=
  Finset.card_filter_le _ _

set_option synthInstance.maxHeartbeats 2000 in
-- A reintroduced search loop must fail here rather than eventually succeed (VCVio#772).
/--
error: failed to synthesize instance of type class
  DecidableEq α

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
set_option synthInstance.maxHeartbeats 2000 in
-- A reintroduced search loop must fail here rather than eventually succeed (VCVio#772).
example {α : Type} : DecidableEq α := inferInstance

end VCVioTest.OracleComp.SpecInstanceSearchNative
