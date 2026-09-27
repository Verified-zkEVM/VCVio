/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.OracleComp.OracleSpec

/-!
# Instance search around oracle specifications

`OracleSpec.Domain` and `OracleSpec.Range` are reducible, so a global instance concluding
`DecidableEq spec.Domain` or `DecidableEq (spec.Range t)` for a generic `spec` is indexed as
`DecidableEq ι`, respectively `DecidableEq (?spec ?t)`: a candidate for every equality goal, with
`spec` undetermined. Ordinary equality search on an unrelated type then invents a specification
through `ofFn` and either times out (VCVio#772) or, once the exact instances fail and a
`classical` fallback is the only alternative, answers `DecidableEq (β a)` for a dependent family
`β` through oracle-specification data. VCVio therefore has no such instances: index equality is
an ordinary `[DecidableEq ι]` hypothesis, answer-type data are ordinary hypotheses on
`spec.Range t`, and concrete specifications reduce to their answer types. The `Fintype` and
`Inhabited` projections had the same shape; they were only ever reached on failing searches
because no classical fallback exists for those classes.

These clients import only `OracleSpec`. The heartbeat bounds make a reintroduced loop fail as a
search failure rather than eventually succeed, and the dependency checks reject elaborated terms
that route ordinary instances through oracle-specification data.
-/

public section

universe u

namespace VCVioTest.OracleComp.SpecInstanceSearch

open Lean in
/-- Fail if the value of `decl` uses bundled specification data: an instance of one of the
retired `OracleSpec` or `PFunctor` instance-bundle classes, or a projection out of one. The
names are matched syntactically so the check keeps guarding against a reintroduced class. -/
meta def assertNoSpecEquality (decl : Name) : CoreM Unit := do
  let env ← getEnv
  let some value := env.find? decl |>.bind (·.value?) | throwError "{decl} has no value"
  let classes := [`OracleSpec.DecidableEq, `PFunctor.DecidableEq, `OracleSpec.Fintype,
    `PFunctor.Fintype, `OracleSpec.Inhabited, `PFunctor.Inhabited]
  for used in value.getUsedConstants do
    let head := (env.find? used).bind (·.type.getForallBody.getAppFn.constName?)
    if classes.any (·.isPrefixOf used) || head.any (classes.contains ·) then
      throwError "{decl} depends on {used}"

-- The oracle-specification instance-bundle classes no longer exist.
run_cmd do
  let env ← Lean.getEnv
  for name in [`OracleSpec.DecidableEq, `OracleSpec.Fintype, `OracleSpec.Inhabited] do
    if env.contains name then
      throwError "retired instance-bundle class {name} is back"

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
/-- Equality on a dependent family under `classical` comes from `Classical.propDecidable`, not
from a specification invented around the family. -/
noncomputable def classicalDepDecEq {α : Type u} {β : α → Type u} (a : α) :
    DecidableEq (β a) := by
  classical
  infer_instance

run_cmd Lean.Elab.Command.liftCoreM <| assertNoSpecEquality ``classicalDepDecEq

set_option synthInstance.maxHeartbeats 2000 in
-- A reintroduced search loop must fail here rather than eventually succeed (VCVio#772).
/-- Equality on an applied type family is its own instance. -/
def finDecEq (n : ℕ) : DecidableEq (Fin n) := inferInstance

run_cmd Lean.Elab.Command.liftCoreM <| assertNoSpecEquality ``finDecEq

set_option synthInstance.maxHeartbeats 2000 in
-- A reintroduced search loop must fail here rather than eventually succeed (VCVio#772).
/-- Finiteness of an applied type family is its own instance. -/
@[instance_reducible] def finFintype (n : ℕ) : Fintype (Fin n) := inferInstance

run_cmd Lean.Elab.Command.liftCoreM <| assertNoSpecEquality ``finFintype

set_option synthInstance.maxHeartbeats 2000 in
-- A reintroduced search loop must fail here rather than eventually succeed (VCVio#772).
/-- Inhabitedness of an applied type family is its own instance. -/
@[instance_reducible] def listInhabited (α : Type u) : Inhabited (List α) := inferInstance

run_cmd Lean.Elab.Command.liftCoreM <| assertNoSpecEquality ``listInhabited

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

set_option synthInstance.maxHeartbeats 2000 in
-- A reintroduced search loop must fail here rather than eventually succeed (VCVio#772).
/--
error: failed to synthesize instance of type class
  DecidableEq (β a)

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
set_option synthInstance.maxHeartbeats 2000 in
-- A reintroduced search loop must fail here rather than eventually succeed (VCVio#772).
example {α : Type} {β : α → Type} (a : α) : DecidableEq (β a) := inferInstance

set_option synthInstance.maxHeartbeats 2000 in
-- A reintroduced search loop must fail here rather than eventually succeed (VCVio#772).
/--
error: failed to synthesize instance of type class
  Fintype (β a)

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
set_option synthInstance.maxHeartbeats 2000 in
-- A reintroduced search loop must fail here rather than eventually succeed (VCVio#772).
example {α : Type} {β : α → Type} (a : α) : Fintype (β a) := inferInstance

set_option synthInstance.maxHeartbeats 2000 in
-- A reintroduced search loop must fail here rather than eventually succeed (VCVio#772).
/--
error: failed to synthesize instance of type class
  Inhabited (β a)

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
set_option synthInstance.maxHeartbeats 2000 in
-- A reintroduced search loop must fail here rather than eventually succeed (VCVio#772).
example {α : Type} {β : α → Type} (a : α) : Inhabited (β a) := inferInstance

/-! ## Known specifications reduce to their answer types -/

set_option synthInstance.maxHeartbeats 2000 in
-- A reintroduced search loop must fail here rather than eventually succeed (VCVio#772).
/-- Index equality of a concrete specification is equality of its index type. -/
def natBoolDomainDecEq : DecidableEq (ℕ →ₒ Bool).Domain := inferInstance

run_cmd Lean.Elab.Command.liftCoreM <| assertNoSpecEquality ``natBoolDomainDecEq

set_option synthInstance.maxHeartbeats 2000 in
-- A reintroduced search loop must fail here rather than eventually succeed (VCVio#772).
/-- Dependent range equality of a concrete specification is equality of its answer type. -/
def natBoolRangeDecEq (t : (ℕ →ₒ Bool).Domain) : DecidableEq ((ℕ →ₒ Bool).Range t) :=
  inferInstance

run_cmd Lean.Elab.Command.liftCoreM <| assertNoSpecEquality ``natBoolRangeDecEq

set_option synthInstance.maxHeartbeats 2000 in
-- A reintroduced search loop must fail here rather than eventually succeed (VCVio#772).
example : natBoolRangeDecEq 0 true true = .isTrue rfl := rfl

set_option synthInstance.maxHeartbeats 2000 in
-- A reintroduced search loop must fail here rather than eventually succeed (VCVio#772).
/-- Summed specifications combine both components' equality data computably. -/
example : ∀ t, DecidableEq (((ℕ →ₒ Bool) + unifSpec).Range t) := inferInstance

set_option synthInstance.maxHeartbeats 2000 in
-- A reintroduced search loop must fail here rather than eventually succeed (VCVio#772).
example : decide ((.inr 3 : ((ℕ →ₒ Bool) + unifSpec).Domain) = .inr 3) = true := rfl

set_option synthInstance.maxHeartbeats 2000 in
-- A reintroduced search loop must fail here rather than eventually succeed (VCVio#772).
example : decide ((.inl 0 : ((ℕ →ₒ Bool) + unifSpec).Domain) = .inr 3) = false := rfl

set_option synthInstance.maxHeartbeats 2000 in
-- A reintroduced search loop must fail here rather than eventually succeed (VCVio#772).
/-- Range equality of a sum is decided computably on the summand's answer type. -/
def sumRangeDecEq (t : ((ℕ →ₒ Bool) + unifSpec).Domain) :
    DecidableEq (((ℕ →ₒ Bool) + unifSpec).Range t) := inferInstance

set_option synthInstance.maxHeartbeats 2000 in
-- A reintroduced search loop must fail here rather than eventually succeed (VCVio#772).
example : (sumRangeDecEq (.inr 3) (0 : Fin 4) (1 : Fin 4)).decide = false := rfl

set_option synthInstance.maxHeartbeats 2000 in
-- A reintroduced search loop must fail here rather than eventually succeed (VCVio#772).
example (t : ((ℕ →ₒ Bool) + unifSpec).Domain) :
    Fintype (((ℕ →ₒ Bool) + unifSpec).Range t) := inferInstance

set_option synthInstance.maxHeartbeats 2000 in
-- A reintroduced search loop must fail here rather than eventually succeed (VCVio#772).
example (t : ((ℕ →ₒ Bool) + unifSpec).Domain) :
    Inhabited (((ℕ →ₒ Bool) + unifSpec).Range t) := inferInstance

/-! ## Spellings of an answer type agree

`spec.Range t`, `spec t`, and `spec.toPFunctor.B t` are one type at reducible transparency,
which is the transparency of local-instance matching and of discrimination-tree keys, so a
hypothesis stated in any spelling serves goals stated in the others. The sum instances answer
both spellings too, and agree definitionally with the summand's own instance. -/

section spellings

variable {ι ι' : Type u} {spec : OracleSpec.{u, u} ι} {spec' : OracleSpec.{u, u} ι'}

section forallHypotheses

variable [∀ t, DecidableEq (spec.Range t)] [∀ t, Fintype (spec' t)]

set_option synthInstance.maxHeartbeats 2000 in
-- A reintroduced search loop must fail here rather than eventually succeed (VCVio#772).
example (t : ι) : DecidableEq (spec t) := inferInstance

set_option synthInstance.maxHeartbeats 2000 in
-- A reintroduced search loop must fail here rather than eventually succeed (VCVio#772).
example (t : spec.toPFunctor.A) : DecidableEq (spec.toPFunctor.B t) := inferInstance

set_option synthInstance.maxHeartbeats 2000 in
-- A reintroduced search loop must fail here rather than eventually succeed (VCVio#772).
example (t : ι') : Fintype (spec'.Range t) := inferInstance

set_option synthInstance.maxHeartbeats 2000 in
-- A reintroduced search loop must fail here rather than eventually succeed (VCVio#772).
example : ∀ a, Fintype (spec'.toPFunctor.B a) := inferInstance

end forallHypotheses

section perQueryHypotheses

variable (t : ι) [Inhabited (spec t)] [DecidableEq (spec.Range t)]

set_option synthInstance.maxHeartbeats 2000 in
-- A reintroduced search loop must fail here rather than eventually succeed (VCVio#772).
example : Inhabited (spec.toPFunctor.B t) := inferInstance

set_option synthInstance.maxHeartbeats 2000 in
-- A reintroduced search loop must fail here rather than eventually succeed (VCVio#772).
example : DecidableEq (spec t) := inferInstance

end perQueryHypotheses

section sums

variable [∀ t, DecidableEq (spec t)] [∀ t, DecidableEq (spec'.Range t)]
  [∀ t, Inhabited (spec.Range t)] [∀ t, Inhabited (spec' t)]

set_option synthInstance.maxHeartbeats 2000 in
-- A reintroduced search loop must fail here rather than eventually succeed (VCVio#772).
example (t : ι ⊕ ι') : DecidableEq ((spec + spec') t) := inferInstance

set_option synthInstance.maxHeartbeats 2000 in
-- A reintroduced search loop must fail here rather than eventually succeed (VCVio#772).
example (t : ι ⊕ ι') : Inhabited ((spec + spec').toPFunctor.B t) := inferInstance

set_option synthInstance.maxHeartbeats 2000 in
-- A reintroduced search loop must fail here rather than eventually succeed (VCVio#772).
example (t : ι') : Inhabited ((spec + spec') (.inr t)) := inferInstance

/-- On a summand's branch, the sum instance is the summand's instance. -/
example (t : ι) (a b : spec t) :
    (inferInstance : DecidableEq ((spec + spec').Range (.inl t))) a b =
      (inferInstance : DecidableEq (spec t)) a b := rfl

end sums

end spellings

/-! ## Specifications above `Type 0` -/

set_option synthInstance.maxHeartbeats 2000 in
-- A reintroduced search loop must fail here rather than eventually succeed (VCVio#772).
example {ι : Type (u + 1)} (F : ι → Type (u + 2)) [∀ i, DecidableEq (F i)] :
    ∀ t, DecidableEq ((OracleSpec.ofFn F).Range t) := inferInstance

set_option synthInstance.maxHeartbeats 2000 in
-- A reintroduced search loop must fail here rather than eventually succeed (VCVio#772).
example {ι : Type (u + 1)} (spec : OracleSpec.{u + 1, u + 2} ι)
    [∀ t, DecidableEq (spec.Range t)] (t : spec.Domain) : DecidableEq (spec.Range t) :=
  inferInstance

set_option synthInstance.maxHeartbeats 2000 in
-- A reintroduced search loop must fail here rather than eventually succeed (VCVio#772).
example {ι : Type (u + 1)} {ι' : Type (u + 1)} (spec : OracleSpec.{u + 1, u + 2} ι)
    (spec' : OracleSpec.{u + 1, u + 2} ι') [∀ t, Fintype (spec.Range t)]
    [∀ t, Fintype (spec'.Range t)] (t : (spec + spec').Domain) :
    Fintype ((spec + spec').Range t) := inferInstance

set_option synthInstance.maxHeartbeats 2000 in
-- A reintroduced search loop must fail here rather than eventually succeed (VCVio#772).
noncomputable example {α : Type (u + 1)} : DecidableEq α := by
  classical
  infer_instance

end VCVioTest.OracleComp.SpecInstanceSearch
