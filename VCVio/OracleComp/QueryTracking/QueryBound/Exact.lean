/-
Copyright (c) 2026 Tom Wambsgans, Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans, Alexander Hicks
-/

module
public import VCVio.OracleComp.OracleComp

/-!
# Exact structural query counts

`ExactQueryCount` certifies a common query count on every branch of a free oracle program.
Bind adds counts and map preserves them, with independent index, response and result universes.
No probability interpretation or response inhabitance is required. Empty response types can
make structural counts nonunique; runtime costs on support are a separate observation.
-/

public section
open OracleComp OracleSpec

namespace OracleComp.QueryBound
section
universe i a r

/-- Branch-uniform exact-count certificate over the existing free oracle tree. -/
inductive ExactQueryCount {ι : Type i} {spec : OracleSpec.{i, a} ι} {α : Type r} :
    OracleComp spec α → Nat → Prop where
  /-- A returned value has structural count zero. -/
  | pure (value : α) : ExactQueryCount (pure value) 0
  /-- The existing query node adds one to a common count for every typed response. -/
  | query (input : spec.Domain) (next : spec.Range input → OracleComp spec α)
      (count : Nat) (hnext : ∀ output, ExactQueryCount (next output) count) :
      ExactQueryCount
        (OracleComp.ofFreeM (PFunctor.FreeM.liftBind (P := spec.toPFunctor) input
          (fun output => OracleComp.toFreeM (next output)))) (count + 1)


end

namespace ExactQueryCount

/-- Branch-uniform counts add across heterogeneous bind. -/
theorem bind.{i, a, r, s} :
  ∀ {ι : Type i} {spec : OracleSpec.{i, a} ι} {α : Type r} {β : Type s}
    {computation : OracleComp spec α} {count : Nat},
    ExactQueryCount computation count →
    ∀ (next : α → OracleComp spec β) (nextCount : Nat),
      (∀ value, ExactQueryCount (next value) nextCount) →
      ExactQueryCount
        (OracleComp.ofFreeM (PFunctor.FreeM.bind (P := spec.toPFunctor)
          (OracleComp.toFreeM computation) (fun value => OracleComp.toFreeM (next value))))
        (count + nextCount) := by
  intro ι spec α β computation count hcomputation next nextCount hnext
  induction hcomputation with
  | pure value =>
      simpa only [OracleComp.toFreeM, PFunctor.FreeM.pure_bind,
        OracleComp.ofFreeM, Nat.zero_add] using hnext value
  | query input rest restCount hrest ih =>
      change OracleComp.QueryBound.ExactQueryCount
        (OracleComp.ofFreeM
          (PFunctor.FreeM.liftBind (P := spec.toPFunctor) input
            (fun output => PFunctor.FreeM.bind (P := spec.toPFunctor)
              (OracleComp.toFreeM (rest output))
              (fun value => OracleComp.toFreeM (next value)))))
        ((restCount + 1) + nextCount)
      have step := OracleComp.QueryBound.ExactQueryCount.query (spec := spec) input
        (fun output => OracleComp.ofFreeM
          (PFunctor.FreeM.bind (P := spec.toPFunctor)
            (OracleComp.toFreeM (rest output))
            (fun value => OracleComp.toFreeM (next value))))
        (restCount + nextCount) ih
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using step

/-- Mapping returned values preserves a branch-uniform query count. -/
theorem map.{i, a, r, s} :
  ∀ {ι : Type i} {spec : OracleSpec.{i, a} ι} {α : Type r} {β : Type s}
    {computation : OracleComp spec α} {count : Nat},
    ExactQueryCount computation count → ∀ f : α → β,
      ExactQueryCount
        (OracleComp.ofFreeM (PFunctor.FreeM.map (P := spec.toPFunctor) f
          (OracleComp.toFreeM computation))) count := by
  intro ι spec α β computation count hcomputation f
  induction hcomputation with
  | pure value =>
      exact OracleComp.QueryBound.ExactQueryCount.pure (f value)
  | query input rest restCount hrest ih =>
      exact OracleComp.QueryBound.ExactQueryCount.query (spec := spec) input
        (fun output => OracleComp.ofFreeM
          (PFunctor.FreeM.map (P := spec.toPFunctor) f
            (OracleComp.toFreeM (rest output)))) restCount ih

end ExactQueryCount
end OracleComp.QueryBound
