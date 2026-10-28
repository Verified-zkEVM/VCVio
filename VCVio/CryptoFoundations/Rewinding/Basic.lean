/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.OracleComp.QueryTracking.WriterCost
public import VCVio.OracleComp.SimSemantics.StateT.Basic
public import VCVio.OracleComp.SimSemantics.Append.Core

/-!
# Frozen worlds for black-box reruns

A reset policy separates persistent oracle information from a cursor local to one execution.
The persistent world grows throughout an extraction attempt; the cursor starts afresh on every
complete rerun. Private randomness belongs to the world, so rerunning never refreshes it.
-/

public section

open OracleComp OracleSpec
open scoped ENNReal

namespace Rewinding

variable {ι σ : Type} {spec : OracleSpec ι}

/-- The extractor's own fresh randomness, independent of the prover's frozen randomness. -/
@[expose] def coins {S : Type} : QueryImpl unifSpec (StateT S ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT S ProbComp)

/-- An implementation of oracle effects with persistent, consistently extendible answers.

`faithful` identifies a single execution with the honest implementation. `grows` preserves
information already drawn. `frozen` makes a completed query, including its cursor update,
replayable in every extension of its resulting world. `commute` permits independent executions
to discover the same frozen world in either order; it retains both cursor updates, so it also
applies to adaptive continuations. -/
structure ResetPolicy (init : ProbComp σ) (impl : QueryImpl spec (StateT σ ProbComp)) where
  /-- Information shared by all reruns of one attempt. -/
  World : Type
  /-- Extension of persistent information. -/
  [order : Preorder World]
  /-- The world before any oracle effects have been observed. -/
  empty : World
  /-- Execution-local position in the fixed private randomness. -/
  Cursor : Type
  /-- The cursor at the start of every rerun. -/
  begin : Cursor
  /-- Answer an oracle query, extending the world and advancing the local cursor. -/
  answer : QueryImpl spec (StateT (World × Cursor) ProbComp)
  /-- A single execution has the honest output distribution. -/
  faithful : ∀ {α : Type} (oa : OracleComp spec α),
    (simulateQ answer oa).run' (empty, begin) =ᵈ
      (do (simulateQ impl oa).run' (← init))
  /-- Faithfulness also holds in the presence of independent ambient randomness. This form
  permits independently initialized policies to be composed. -/
  faithful_coins : ∀ {α : Type} (oa : OracleComp (unifSpec + spec) α),
    (simulateQ (coins (S := World × Cursor) + answer) oa).run' (empty, begin) =ᵈ
      (do (simulateQ (coins (S := σ) + impl) oa).run' (← init))
  /-- A query only extends the persistent world. -/
  grows : ∀ q w c z, z ∈ support ((answer q).run (w, c)) → w ≤ z.2.1
  /-- Every observed answer and cursor transition is fixed in extensions of its post-world. -/
  frozen : ∀ q w w' c z, z ∈ support ((answer q).run (w, c)) → z.2.1 ≤ w' →
    (answer q).run (w', c) = pure (z.1, (w', z.2.2))
  /-- Discovering two answers in either order preserves their joint distribution, their local
  cursor updates, and the final persistent world. -/
  commute : ∀ q₁ q₂ c₁ c₂ w,
    (do
      let z₁ ← (answer q₁).run (w, c₁)
      let z₂ ← (answer q₂).run (z₁.2.1, c₂)
      pure ((z₁.1, z₁.2.2), (z₂.1, z₂.2.2), z₂.2.1)) =ᵈ
    (do
      let z₂ ← (answer q₂).run (w, c₂)
      let z₁ ← (answer q₁).run (z₂.2.1, c₁)
      pure ((z₁.1, z₁.2.2), (z₂.1, z₂.2.2), z₁.2.1))

attribute [instance] ResetPolicy.order

/-- The black-box oracle whose input selects a complete run and whose answer is its output. -/
abbrev rerunSpec (Q α : Type) : OracleSpec Q := Q →ₒ α

/-- Answer from a fixed function and charge one complete run. -/
@[expose] def counted {Q α : Type} (f : Q → α) :
    QueryImpl (rerunSpec Q α) (StateT ℕ ProbComp) :=
  fun q => do
    modify (· + 1)
    pure (f q)

variable {init : ProbComp σ} {impl : QueryImpl spec (StateT σ ProbComp)}

/-- Execute one selected computation from the beginning, preserving the world and charging
one complete run. The caller has no access to the computation's internal state or cursor. -/
@[expose] def ResetPolicy.rerun (P : ResetPolicy init impl) {Q α : Type}
    (run : Q → OracleComp spec α) :
    QueryImpl (rerunSpec Q α) (StateT (P.World × ℕ) ProbComp) :=
  fun q => StateT.mk fun s =>
    (fun z => (z.1, (z.2.1, s.2 + 1))) <$>
      (simulateQ P.answer (run q)).run (s.1, P.begin)

/-- Run a black-box algorithm against frozen reruns, returning its output and number of
complete runs. Each attempt starts with an empty world and a zero run count. -/
@[expose] def ResetPolicy.attempt (P : ResetPolicy init impl) {Q α β : Type}
    (run : Q → OracleComp spec α) (alg : OracleComp (unifSpec + rerunSpec Q α) β) :
    ProbComp (β × ℕ) :=
  (fun z => (z.1, z.2.2)) <$>
    (simulateQ (coins (S := P.World × ℕ) + P.rerun run) alg).run (P.empty, 0)

/-- Expected complete-run count, using the additive writer's natural-valued expectation. -/
@[expose] noncomputable def expectedCalls {β : Type} (mx : ProbComp (β × ℕ)) : ℝ≥0∞ :=
  AddWriterT.expectedCostNat (WriterT.mk ((fun z => (z.1, Multiplicative.ofAdd z.2)) <$> mx))

end Rewinding
