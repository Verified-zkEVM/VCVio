/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import HashSigTest.SLHDSA.Refactor.ForsProgram
public import VCVio.OracleComp.QueryTracking.ListCache
public import VCVio.OracleComp.QueryTracking.WriterCost
public import Mathlib.Algebra.FreeMonoid.Basic

/-!
# Direct functional-cell execution of the canonical FORS component

The logical cell table is the ordinary computable function used by the generic theorem.
The component and graph share one existing cache, trace and ordered-cost interpretation.
-/

public section

universe u

open OracleComp OracleSpec SLHDSA SLHDSA.Graph

namespace SLHDSA.Refactor.ForsGraphSupport

/-- The node carrier is Nat and the independent secret-seed carrier is Bool. -/
abbrev core := SLHDSA.Refactor.ForsProgramTest.core
/-- Two one-level FORS trees form a bounded arithmetic-valid fixture. -/
abbrev params := SLHDSA.Refactor.ForsProgramTest.params
/-- Each actual call retains its full natural address and ordered payload. -/
abbrev Spec := (Adrs × List Nat) →ₒ Nat
/-- An observable request contains its natural address and ordered node values. -/
abbrev Label := Adrs × List Nat
/-- The result retains the existing intrinsically sized FORS signature. -/
abbrev Signature := ForsSigCore params core

/-- The actual bottom-layer FORS key at the origin. -/
def key : ForsKey params := ⟨⟨0, by decide⟩, ⟨0, by decide⟩⟩

/-- Arbitrary nonseed values are retained in a computable functional logical table. -/
def initial : Node params → Nat
  | .secretSeed => 7
  | .structural node => 1000 + node.address.word3

/-- The actual canonical effectful FORS body, with the explicit query-based provider. -/
def actual : OracleComp Spec Signature :=
  forsSignWithSecret core
    (fun address value => query (spec := Spec) (address, [value]))
    (fun address left right => query (spec := Spec) (address, [left, right]))
    (fun address => query (spec := Spec) (address, [7])) [] key.address

/-- The same existing traversal executes with ordinary function cells and derived key equality. -/
def graph : OracleComp Spec Signature :=
  Fors.reconstruct core key [] <$>
    RandomOracleTraversal.evaluate (StructuralNode.input (by decide : params.Valid))
      updateCell (ForsSchedule.signing key []) initial

/-- Both executable paths are exactly the two sides of the checked generic programme theorem. -/
theorem actual_eq_graph : actual = graph :=
  Fors.forsSignWithSecret_eq_evaluate params (by decide) core 7 key [] initial rfl

/-- Complete observations preserve the signature, arbitrary final outer state and ordered cost.
The only internal projection is the existing signature readback from logical graph cells. -/
theorem full_observation (m : Type → Type u) [Monad m] (State C : Type) [AddMonoid C]
    (handler : QueryImpl Spec (StateT State m)) (cost : Label → C) (state : State) :
    ((simulateQ (handler.withAddCost cost) actual).runAdd).run state =
      ((simulateQ (handler.withAddCost cost) graph).runAdd).run state :=
  congrArg (fun program => ((simulateQ (handler.withAddCost cost) program).runAdd).run state)
    actual_eq_graph

/-- Full input and answer events are observable separately from actual cache misses. -/
structure Trace where
  /-- The number of actual draws after cache misses. -/
  misses : Nat := 0
  /-- Every attempted input and its actual answer in chronological order. -/
  replies : List (Label × Nat) := []
  deriving Repr, DecidableEq

/-- First-binding association lists retain every initial and sampled entry. -/
abbrev Cache := List (Label × Nat)
/-- Cost retains a weighted total and the entire noncommutative input/weight sequence. -/
abbrev Cost := Nat × FreeAddMonoid (Label × Nat)
/-- One shared outer cache and reply trace are carried across component invocations. -/
abbrev Backend := StateT Cache (StateM Trace)

/-- The deterministic draw is nonconstant in both the address and ordered payload. -/
def answer (label : Label) : Nat :=
  100 * label.1.type + 10 * label.1.word3 + label.2.sum

/-- Only actual cache misses draw a new answer. -/
def draw : QueryImpl Spec (StateM Trace) := fun label => do
  modify fun trace => { trace with misses := trace.misses + 1 }
  return answer label

/-- Every attempted query and reply is logged outside the existing first-binding cache. -/
def handler : QueryImpl Spec Backend :=
  (QueryImpl.ListCache.handler draw).postInsert (fun label value =>
    liftM (modify (fun trace : Trace =>
      { trace with replies := trace.replies ++ [(label, value)] }) : StateM Trace Unit))

/-- Input-dependent source weights retain both their sum and complete chronological sequence. -/
def cost (label : Label) : Cost :=
  let weight := (if label.1.type = 6 then 3 else 5) + label.1.word3
  (weight, .of (label, weight))

/-- The canonical provider address uses the actual FORS-PRF type code. -/
def prf (index : Nat) : Adrs := ⟨0, 0, 6, 0, 0, index⟩

/-- The canonical leaf address uses the actual FORS-tree type code. -/
def leaf (index : Nat) : Adrs := ⟨0, 0, 3, 0, 0, index⟩

/-- The first binding is deliberately distinct from both a fresh draw and a shadowed binding. -/
def warm : Cache := [((prf 0, [7]), 777), ((prf 0, [7]), 999)]

/-- Observe the entire actual result, ordered cost, retained cache and reply/miss trace. -/
def run {A : Type} (program : OracleComp Spec A) : ((A × Cost) × Cache) × Trace :=
  (((simulateQ (handler.withAddCost cost) program).runAdd).run warm).run {}

/-- Repeated component invocations share the same outer cache/cost/trace and still execute all
    calls. -/
def twice (program : OracleComp Spec Signature) : OracleComp Spec (Signature × Signature) := do
  let first ← program
  let second ← program
  return (first, second)

/-- Exact complete single-invocation observation for the executable backend. -/
theorem run_eq : run actual = run graph := congrArg run actual_eq_graph

/-- Exact complete repeated observation; the outer shared cache is never reset between
    components. -/
theorem run_twice_eq : run (twice actual) = run (twice graph) :=
  congrArg (fun program => run (twice program)) actual_eq_graph

/-- Every field of every existing intrinsically shaped signature is retained for comparison. -/
def signatureView (signature : Signature) : List (Nat × List Nat) :=
  signature.toList.map fun tree => (tree.sk, tree.auth.toList)

end SLHDSA.Refactor.ForsGraphSupport
