/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio
public import VCVio.Native
import VCVioTest.OracleComp.SpecInstanceSearch

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
/-- Equality on a dependent family under `classical` comes from `Classical.propDecidable`, not
from a specification invented around the family, even with every compatibility instance of the
library in scope. -/
noncomputable def classicalDepDecEq {α : Type u} {β : α → Type u} (a : α) :
    DecidableEq (β a) := by
  classical
  infer_instance

run_cmd Lean.Elab.Command.liftCoreM <|
  VCVioTest.OracleComp.SpecInstanceSearch.assertNoSpecEquality ``classicalDepDecEq

set_option synthInstance.maxHeartbeats 2000 in
-- A reintroduced search loop must fail here rather than eventually succeed (VCVio#772).
/-- Under uniform measure semantics, the cardinality of one answer type is an ordinary
per-query hypothesis; the semantics class carries no finiteness data. -/
example {ι : Type} {spec : OracleSpec ι} [∀ t, MeasurableSpace (spec.Range t)]
    [∀ t, DiscreteMeasurableSpace (spec.Range t)] [OracleSpec.IsUniformMeasureSpec spec]
    (t : spec.Domain) [Fintype (spec.Range t)] (u : spec.Range t) :
    OracleSpec.IsMeasureSpec.toMeasure t {u} = (Fintype.card (spec.Range t) : ENNReal)⁻¹ :=
  OracleSpec.IsUniformMeasureSpec.toMeasure_singleton t u

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
