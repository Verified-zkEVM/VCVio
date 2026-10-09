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
surface and the whole library (including its compatibility instances) in scope, followed by the
routing of `Nonempty`/`Finite` goals around the sampler-derived instances
`SampleableType.nonempty`/`SampleableType.finite`.
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

/-! ## Sampler-derived propositions

`SampleableType.nonempty` and `SampleableType.finite` conclude `Nonempty β` and `Finite β` for
a plain type variable, so they are wildcard-keyed like `Finite.of_fintype`, and they carry
`priority := 100` so that they are tried after every ordinary instance. Ordinary finiteness and
nonemptiness facts must therefore elaborate without sampler code, while a type whose finiteness
is known through nothing but its sampler still gets one. -/

open Lean Meta Elab Command Term in
/-- Synthesize an instance of `type` and fail if the term found mentions the sampler class, one
of its instances, or a declaration in its namespace. -/
meta def assertNoSampler (type : TSyntax `term) : CommandElabM Unit := liftTermElabM do
  let type ← elabType type
  let inst ← instantiateMVars (← synthInstance type)
  for used in inst.getUsedConstants do
    if (`SampleableType).isPrefixOf used || used.toString.contains "SampleableType" then
      throwError "{type} is answered by sampler declaration {used}"

set_option synthInstance.maxHeartbeats 2000 in
-- A wildcard-keyed sampler instance must not be reached before the ordinary instances.
-- Nonemptiness of `Fin 3` comes from `Inhabited`, not from its sampler.
run_cmd assertNoSampler (← `(Nonempty (Fin 3)))

set_option synthInstance.maxHeartbeats 2000 in
-- A wildcard-keyed sampler instance must not be reached before the ordinary instances.
-- Finiteness of `Fin 3` comes from `Fintype`, not from its sampler.
run_cmd assertNoSampler (← `(Finite (Fin 3)))

set_option synthInstance.maxHeartbeats 2000 in
-- A wildcard-keyed sampler instance must not be reached before the ordinary instances.
-- Finiteness of a function type comes from `Pi.instFintype`, not from its sampler.
run_cmd assertNoSampler (← `(Finite (Fin 4 → Bool)))

set_option synthInstance.maxHeartbeats 2000 in
-- A wildcard-keyed sampler instance must not be reached before the ordinary instances.
-- Nonemptiness of a product comes from `Prod.instNonempty`, not from its sampler.
run_cmd assertNoSampler (← `(Nonempty (Fin 2 × Bool)))

set_option synthInstance.maxHeartbeats 2000 in
-- A sampler-only answer type must be found by the fallback instance within a small budget.
/-- An answer type whose only known structure is its sampler is finite through the sampler. -/
example {ι : Type} {spec : OracleSpec ι} [∀ t, SampleableType (spec.Range t)]
    (t : spec.Domain) : Finite (spec.Range t) :=
  inferInstance

set_option synthInstance.maxHeartbeats 2000 in
-- A sampler-only answer type must be found by the fallback instance within a small budget.
/-- An answer type whose only known structure is its sampler is nonempty through the sampler. -/
example {ι : Type} {spec : OracleSpec ι} [∀ t, SampleableType (spec.Range t)]
    (t : spec.Domain) : Nonempty (spec.Range t) :=
  inferInstance

set_option synthInstance.maxHeartbeats 2000 in
-- A wildcard-keyed sampler instance must fail fast on a family with no sampler.
/--
error: failed to synthesize instance of type class
  Nonempty (β a)

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
set_option synthInstance.maxHeartbeats 2000 in
example {α : Type} {β : α → Type} (a : α) : Nonempty (β a) := inferInstance

end VCVioTest.OracleComp.SpecInstanceSearchNative
