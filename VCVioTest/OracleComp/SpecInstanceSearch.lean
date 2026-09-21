/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.OracleComp.OracleSpec

/-!
# Instance search around oracle specifications

`OracleSpec.Domain` is reducible, so an instance concluding `DecidableEq spec.Domain` is indexed
as `DecidableEq ι` for every `ι`. With `spec` absent from that key, ordinary equality search on
an unrelated type used to invent a metavariable specification, recurse through the `ofFn`
instance, and time out (VCVio#772). Index equality is therefore taken from `ι` itself, and the
bundled range data remain instances.

These clients import only `OracleSpec`. The heartbeat bounds make a reintroduced loop fail as a
search failure rather than eventually succeed, and the dependency checks reject elaborated terms
that route ordinary equality through oracle-specification instances.
-/

public section

universe u

namespace VCVioTest.OracleComp.SpecInstanceSearch

open Lean in
/-- Fail if the value of `decl` uses bundled specification equality: an `OracleSpec.DecidableEq`
or `PFunctor.DecidableEq` instance, or a projection out of one. -/
meta def assertNoSpecEquality (decl : Name) : CoreM Unit := do
  let env ← getEnv
  let some value := env.find? decl |>.bind (·.value?) | throwError "{decl} has no value"
  let classes := [``OracleSpec.DecidableEq, ``PFunctor.DecidableEq]
  for used in value.getUsedConstants do
    let head := (env.find? used).bind (·.type.getForallBody.getAppFn.constName?)
    if classes.any (·.isPrefixOf used) || head.any (classes.contains ·) then
      throwError "{decl} depends on {used}"

/-! ## Unconstrained equality search -/

set_option synthInstance.maxHeartbeats 2000 in
-- A reintroduced search loop must fail here rather than eventually succeed (VCVio#772).
/-- `classical` supplies equality on an arbitrary type inside a proof. -/
theorem classical_if_le {F : Type} (x y : F) : ∃ n : ℕ, n ≤ 1 := by
  classical
  exact ⟨if x = y then 1 else 0, by split <;> simp⟩

set_option synthInstance.maxHeartbeats 2000 in
-- A reintroduced search loop must fail here rather than eventually succeed (VCVio#772).
/-- Equality on an arbitrary type comes from `Classical.propDecidable`. -/
noncomputable def classicalDecEq {α : Type u} : DecidableEq α := by
  classical
  infer_instance

run_cmd Lean.Elab.Command.liftCoreM <| assertNoSpecEquality ``classicalDecEq

set_option synthInstance.maxHeartbeats 2000 in
-- A reintroduced search loop must fail here rather than eventually succeed (VCVio#772).
open Classical in
/-- A coding-theory-style cardinality goal with a classical filter predicate. -/
theorem card_filter_le {α : Type} [Fintype α] (p : α → Prop) :
    (Finset.univ.filter p).card ≤ Fintype.card α :=
  Finset.card_filter_le _ _

/-! Missing instances fail within the heartbeat bound instead of searching for a specification. -/

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

set_option synthInstance.maxHeartbeats 2000 in
-- A reintroduced search loop must fail here rather than eventually succeed (VCVio#772).
/--
error: failed to synthesize instance of type class
  Fintype α

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
set_option synthInstance.maxHeartbeats 2000 in
-- A reintroduced search loop must fail here rather than eventually succeed (VCVio#772).
example {α : Type} : Fintype α := inferInstance

set_option synthInstance.maxHeartbeats 2000 in
-- A reintroduced search loop must fail here rather than eventually succeed (VCVio#772).
/--
error: failed to synthesize instance of type class
  Inhabited α

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
set_option synthInstance.maxHeartbeats 2000 in
-- A reintroduced search loop must fail here rather than eventually succeed (VCVio#772).
example {α : Type} : Inhabited α := inferInstance

/-! ## Known specifications keep their bundled data -/

set_option synthInstance.maxHeartbeats 2000 in
-- A reintroduced search loop must fail here rather than eventually succeed (VCVio#772).
/-- Index equality of a concrete specification is equality of its index type. -/
def natBoolDomainDecEq : DecidableEq (ℕ →ₒ Bool).Domain := inferInstance

run_cmd Lean.Elab.Command.liftCoreM <| assertNoSpecEquality ``natBoolDomainDecEq

set_option synthInstance.maxHeartbeats 2000 in
-- A reintroduced search loop must fail here rather than eventually succeed (VCVio#772).
/-- Dependent range equality is found through the bundled specification data. -/
def natBoolRangeDecEq (t : (ℕ →ₒ Bool).Domain) : DecidableEq ((ℕ →ₒ Bool).Range t) :=
  inferInstance

set_option synthInstance.maxHeartbeats 2000 in
-- A reintroduced search loop must fail here rather than eventually succeed (VCVio#772).
example : natBoolRangeDecEq 0 true true = .isTrue rfl := rfl

set_option synthInstance.maxHeartbeats 2000 in
-- A reintroduced search loop must fail here rather than eventually succeed (VCVio#772).
/-- Summed specifications combine both components' equality data computably. -/
example : ((ℕ →ₒ Bool) + unifSpec).DecidableEq := inferInstance

set_option synthInstance.maxHeartbeats 2000 in
-- A reintroduced search loop must fail here rather than eventually succeed (VCVio#772).
example : decide ((.inr 3 : ((ℕ →ₒ Bool) + unifSpec).Domain) = .inr 3) = true := rfl

set_option synthInstance.maxHeartbeats 2000 in
-- A reintroduced search loop must fail here rather than eventually succeed (VCVio#772).
example (t : ((ℕ →ₒ Bool) + unifSpec).Domain) :
    Fintype (((ℕ →ₒ Bool) + unifSpec).Range t) := inferInstance

set_option synthInstance.maxHeartbeats 2000 in
-- A reintroduced search loop must fail here rather than eventually succeed (VCVio#772).
example (t : ((ℕ →ₒ Bool) + unifSpec).Domain) :
    Inhabited (((ℕ →ₒ Bool) + unifSpec).Range t) := inferInstance

/-! ## Specifications above `Type 0` -/

set_option synthInstance.maxHeartbeats 2000 in
-- A reintroduced search loop must fail here rather than eventually succeed (VCVio#772).
example {ι : Type (u + 1)} [DecidableEq ι] (F : ι → Type (u + 2))
    [∀ i, DecidableEq (F i)] : (OracleSpec.ofFn F).DecidableEq := inferInstance

set_option synthInstance.maxHeartbeats 2000 in
-- A reintroduced search loop must fail here rather than eventually succeed (VCVio#772).
example {ι : Type (u + 1)} (spec : OracleSpec.{u + 1, u + 2} ι) [spec.DecidableEq]
    (t : spec.Domain) : DecidableEq (spec.Range t) := inferInstance

set_option synthInstance.maxHeartbeats 2000 in
-- A reintroduced search loop must fail here rather than eventually succeed (VCVio#772).
noncomputable example {α : Type (u + 1)} : DecidableEq α := by
  classical
  infer_instance

end VCVioTest.OracleComp.SpecInstanceSearch
