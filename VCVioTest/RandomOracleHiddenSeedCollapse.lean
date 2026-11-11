/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import VCVio.OracleComp.QueryTracking.RandomOracle.HiddenSeedCollapse

/-!
# The ideal hidden-seed game through the duplicated interface

A public random oracle on `ℕ` with one derivation, programs over the duplicated forwarded
interface: the collapse sends both copies of a query to the same query, and the ideal game run
from empty caches is the duplicated lazy random oracle run from the empty joint cache.
-/

public section

open OracleComp OracleSpec

namespace VCVioTest.HiddenSeedCollapse

/-- A public random oracle on `ℕ` and one derivation, joined into one signature. -/
abbrev joint : OracleSpec (ℕ ⊕ Unit) := (ℕ →ₒ Bool) + (Unit →ₒ Bool)

/-- Both copies of a derivation become the same derivation query. -/
example : SecretEncoding.collapseFwd (ℕ →ₒ Bool) Unit Bool (.inr (.inl (.inr ()))) =
    SecretEncoding.collapseFwd (ℕ →ₒ Bool) Unit Bool (.inr (.inr (.inr ()))) := rfl

/-- Query the public point `0` through each copy and compare the answers. -/
def sameTwice : OracleComp (unifSpec + (joint + joint)) Bool := do
  let a ← (unifSpec + (joint + joint)).query (.inr (.inl (.inl 0)))
  let b ← (unifSpec + (joint + joint)).query (.inr (.inr (.inl 0)))
  return a == b

/-- From empty caches, the ideal game read through the collapse is the duplicated lazy random
oracle from the empty joint cache. -/
example : Prod.map id (QueryCache.addEquiv (ℕ →ₒ Bool) (Unit →ₒ Bool)) <$>
      (simulateQ (SecretEncoding.idealImpl (ℕ →ₒ Bool) Unit Bool)
        (simulateQ (SecretEncoding.collapseFwd (ℕ →ₒ Bool) Unit Bool) sameTwice)).run (∅, ∅) =
    (simulateQ (unifFwdImpl joint + AnswerTape.dupRandomOracle joint) sameTwice).run ∅ := by
  rw [SecretEncoding.map_run_simulateQ_idealImpl_collapseFwd, QueryCache.addEquiv_empty]

end VCVioTest.HiddenSeedCollapse
