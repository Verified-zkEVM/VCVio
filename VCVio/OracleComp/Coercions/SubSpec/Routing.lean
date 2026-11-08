/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
module

public import VCVio.OracleComp.Coercions.SubSpec
public import VCVio.OracleComp.SimSemantics.Append.Core

/-!
# Routing nested sum interfaces

Handlers and simulation laws that exchange, insert or merge oracle slots of nested sum
interfaces.
-/

public section

/-! ## Routing sum interfaces -/

namespace QueryImpl

variable {ι κ ν : Type} {a : OracleSpec ι} {b : OracleSpec κ} {c : OracleSpec ν}

/-- Route `(a + b) + c` queries to `(a + c) + b`. -/
@[expose] def swapRight : QueryImpl ((a + b) + c) (OracleComp ((a + c) + b))
  | .inl (.inl q) => query (spec := (a + c) + b) (.inl (.inl q))
  | .inl (.inr q) => query (spec := (a + c) + b) (.inr q)
  | .inr q => query (spec := (a + c) + b) (.inl (.inr q))

/-- Embed two oracle slots around an additional middle slot. -/
@[expose] def insertMiddle : QueryImpl (a + b) (OracleComp ((a + c) + b))
  | .inl q => query (spec := (a + c) + b) (.inl (.inl q))
  | .inr q => query (spec := (a + c) + b) (.inr q)

/-- Merge two copies of the right-hand oracle interface. -/
@[expose] def mergeRight : QueryImpl (((a + c) + b) + c)
    (OracleComp ((a + b) + c))
  | .inl (.inl (.inl q)) => query (spec := (a + b) + c) (.inl (.inl q))
  | .inl (.inl (.inr q)) => query (spec := (a + b) + c) (.inr q)
  | .inl (.inr q) => query (spec := (a + b) + c) (.inl (.inr q))
  | .inr q => query (spec := (a + b) + c) (.inr q)

end QueryImpl

namespace OracleComp

variable {ι κ ν α : Type} {a : OracleSpec ι} {b : OracleSpec κ} {c : OracleSpec ν}

/-- Exchange the last two oracle slots of a computation without changing its operations. -/
@[expose] def swapRight (p : OracleComp ((a + b) + c) α) : OracleComp ((a + c) + b) α :=
  simulateQ QueryImpl.swapRight p

/-- Reordering the handlers with the computation preserves its execution, including state. -/
theorem simulateQ_swapRight {m : Type → Type} [Monad m] [LawfulMonad m]
    (ha : QueryImpl a m) (hb : QueryImpl b m) (hc : QueryImpl c m)
    (p : OracleComp ((a + b) + c) α) :
    simulateQ ((ha + hc) + hb) p.swapRight = simulateQ ((ha + hb) + hc) p := by
  apply QueryImpl.simulateQ_simulateQ_eq_of_apply
  intro q
  rcases q with (q | q) | q <;>
    simp [QueryImpl.swapRight]

/-- Embed a computation without querying the additional middle oracle. -/
@[expose] def insertMiddle (p : OracleComp (a + b) α) : OracleComp ((a + c) + b) α :=
  simulateQ QueryImpl.insertMiddle p

/-- The unused slot does not affect the computation. -/
theorem simulateQ_insertMiddle {m : Type → Type} [Monad m] [LawfulMonad m]
    (ha : QueryImpl a m) (hb : QueryImpl b m) (hc : QueryImpl c m)
    (p : OracleComp (a + b) α) :
    simulateQ ((ha + hc) + hb) p.insertMiddle = simulateQ (ha + hb) p := by
  apply QueryImpl.simulateQ_simulateQ_eq_of_apply
  intro q
  cases q <;> simp [QueryImpl.insertMiddle]

/-- Route both copies of the right-hand interface to a single slot. -/
@[expose] def mergeRight (p : OracleComp (((a + c) + b) + c) α) :
    OracleComp ((a + b) + c) α := simulateQ QueryImpl.mergeRight p

/-- Merging identical oracle handlers preserves the interpreted computation, including state. -/
theorem simulateQ_mergeRight {m : Type → Type} [Monad m] [LawfulMonad m]
    (ha : QueryImpl a m) (hb : QueryImpl b m) (hc : QueryImpl c m)
    (p : OracleComp (((a + c) + b) + c) α) :
    simulateQ ((ha + hb) + hc) p.mergeRight = simulateQ (((ha + hc) + hb) + hc) p := by
  apply QueryImpl.simulateQ_simulateQ_eq_of_apply
  intro q
  rcases q with ((q | q) | q) | q <;> simp [QueryImpl.mergeRight]

end OracleComp
