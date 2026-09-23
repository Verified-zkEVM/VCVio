/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import VCVio.OracleComp.OracleQuery

/-!
# Oracle-query construction and elimination

The oracle facade uses the public polynomial-object interface. These examples exercise its
constructor equations and extensionality through ordinary imports at independent universe levels.
-/

public section

run_cmd do
  let env ← Lean.getEnv
  for name in [`PMF, `SPMF] do
    if env.contains name then
      throwError "oracle-query facade unexpectedly imports {name}"

universe u v w

namespace VCVioTest.OracleComp.Query

variable {ι : Type u} {spec : OracleSpec.{u, v} ι} {α β : Type w}

example (t : spec.Domain) (f : spec.Range t → α) : (OracleQuery.mk t f).input = t := by
  simp

example (t : spec.Domain) (f : spec.Range t → α) : (OracleQuery.mk t f).cont = f := by
  simp

example (q : OracleQuery spec α) (f : α → β) : (f <$> q).input = q.input := by
  simp

example (q : OracleQuery spec α) (f : α → β) : (f <$> q).cont = f ∘ q.cont := by
  simp

example (q q' : OracleQuery spec α) (ht : q.input = q'.input)
    (hf : q.cont ≍ q'.cont) : q = q' := by
  ext
  · exact ht
  · exact hf

example (t : spec.Domain) (f g : spec.Range t → α) (hfg : ∀ x, f x = g x) :
    OracleQuery.mk t f = OracleQuery.mk t g := by
  exact OracleQuery.ext' t (funext hfg)

example (q : OracleQuery spec α) :
    ∃ t f, q = OracleQuery.mk t f := by
  cases q using PFunctor.Obj.rec with
  | mk t f => exact ⟨t, f, rfl⟩

end VCVioTest.OracleComp.Query
