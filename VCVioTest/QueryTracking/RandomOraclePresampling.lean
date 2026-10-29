/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import VCVio.OracleComp.QueryTracking.RandomOracle.Presampling
import VCVio.OracleComp.QueryTracking.WriterCost

/-! # Ordinary clients of random-oracle presampling value laws -/

public section

open OracleComp OracleSpec OracleComp.RandomOracleTraversal

namespace VCVioTest.QueryTracking.RandomOraclePresampling

/-- A client retaining its whole return type can pre-sample a fresh cache coordinate. -/
theorem arbitrary_value_fresh {ι Input Output α : Type} {privateSpec : OracleSpec.{0, 0} ι}
    [DecidableEq Input] [SampleableType Output]
    (privateImpl : QueryImpl privateSpec ProbComp)
    (computation : OracleComp (privateSpec + (Input →ₒ Output)) α)
    (cache : QueryCache (Input →ₒ Output)) (target : Input) (hfresh : cache target = none) :
    let H := privateImpl.liftTarget (StateT (QueryCache (Input →ₒ Output)) ProbComp) +
      (randomOracle : QueryImpl (Input →ₒ Output)
        (StateT (QueryCache (Input →ₒ Output)) ProbComp))
    (Prod.fst <$> (simulateQ H computation).run cache) =ᵈ
      (do
        let value ← ($ᵗ Output : ProbComp Output)
        Prod.fst <$> (simulateQ H computation).run (cache.cacheQuery target value)) :=
  OracleComp.RandomOraclePresampling.evalDist_prepend_fresh
    privateImpl computation cache target hfresh

/-- A fresh traversal preserves every component of an arbitrary returned value. -/
theorem arbitrary_value_traversal {ι Input Output α Index State : Type}
    {privateSpec : OracleSpec.{0, 0} ι} [DecidableEq Input] [SampleableType Output]
    (privateImpl : QueryImpl privateSpec ProbComp)
    (computation : OracleComp (privateSpec + (Input →ₒ Output)) α)
    (input : Index → State → Input) (step : Index → State → Output → State)
    (hseparated : Separated input) (nodes : List Index) (state : State)
    (cache : QueryCache (Input →ₒ Output)) (hnodup : nodes.Nodup)
    (hfresh : FreshFor input nodes cache) :
    let H := privateImpl.liftTarget (StateT (QueryCache (Input →ₒ Output)) ProbComp) +
      (randomOracle : QueryImpl (Input →ₒ Output)
        (StateT (QueryCache (Input →ₒ Output)) ProbComp))
    (Prod.fst <$> (simulateQ H computation).run cache) =ᵈ
      (Prod.fst <$> (simulateQ H
        ((liftM (evaluate input step nodes state) :
            OracleComp (privateSpec + (Input →ₒ Output)) State) >>=
          fun _ => computation)).run cache) :=
  OracleComp.RandomOraclePresampling.evalDist_prepend_traversal
    privateImpl computation input step hseparated nodes state cache hnodup hfresh

/-- A traversal preserves a jointly returned result and downstream request count. -/
theorem selected_traversal {ι Input Output α Index State : Type}
    {privateSpec : OracleSpec.{0, 0} ι} [DecidableEq Input] [SampleableType Output]
    (privateImpl : QueryImpl privateSpec ProbComp)
    (computation : OracleComp (privateSpec + (Input →ₒ Output)) (α × Nat))
    (input : Index → State → Input) (step : Index → State → Output → State)
    (hseparated : Separated input) (nodes : List Index) (state : State)
    (cache : QueryCache (Input →ₒ Output)) (hnodup : nodes.Nodup)
    (hfresh : FreshFor input nodes cache) :
    let H := privateImpl.liftTarget (StateT (QueryCache (Input →ₒ Output)) ProbComp) +
      (randomOracle : QueryImpl (Input →ₒ Output)
        (StateT (QueryCache (Input →ₒ Output)) ProbComp))
    (Prod.fst <$> (simulateQ H computation).run cache) =ᵈ
      (Prod.fst <$> (simulateQ H
        ((liftM (evaluate input step nodes state) :
            OracleComp (privateSpec + (Input →ₒ Output)) State) >>=
          fun _ => computation)).run cache) :=
  OracleComp.RandomOraclePresampling.evalDist_prepend_traversal
    privateImpl computation input step hseparated nodes state cache hnodup hfresh


/-! ## A supported execution path and its retained observations -/

private abbrev HashSpec := Nat →ₒ Fin 2
private abbrev World := unifSpec + HashSpec

private def requestCost : World.Domain → Nat
  | .inl _ => 0
  | .inr _ => 1

private def handler : QueryImpl World (StateT (QueryCache HashSpec) ProbComp) :=
  unifFwdImpl HashSpec + (randomOracle :
    QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp))

private def queryTwice : OracleComp World (Fin 2 × Fin 2) := do
  let first ← query (spec := World) (Sum.inr 0)
  let second ← query (spec := World) (Sum.inr 0)
  pure (first, second)

private def selected {α : Type} (program : OracleComp World α) :
    OracleComp World (α × Nat) :=
  (simulateQ ((QueryImpl.ofLift World (OracleComp World)).withAddCost requestCost)
    program).runAdd

private def warmup (nodes : List Nat) : OracleComp World Unit :=
  liftM (evaluate (fun node (_ : Unit) => node)
    (fun _ _ (_ : Fin 2) => ()) nodes ())

private def warmedTwice : OracleComp World ((Fin 2 × Fin 2) × Nat) := do
  let _ ← warmup [0, 1]
  selected queryTwice

private def unusedFresh : OracleComp World (Nat × Nat) := do
  let _ ← warmup [1]
  selected (pure 7)

private def supportedAnswer : QueryImpl unifSpec (StateT Nat Id) := fun size => do
  modify (· + 1)
  pure ⟨0, Nat.succ_pos size⟩

private structure Observation (α : Type) where
  value : α
  selectedRequests : Nat
  fullRequests : Nat
  draws : Nat
  cached0 : Bool
  cached1 : Bool

private def observe {α : Type} (program : OracleComp World (α × Nat)) : Observation α :=
  let probability := ((simulateQ (handler.withAddCost requestCost) program).runAdd).run ∅
  let ((((value, selectedCount), fullCount), cache), draws) :=
    (simulateQ supportedAnswer probability).run 0
  { value, selectedRequests := selectedCount, fullRequests := fullCount, draws,
    cached0 := (cache 0).isSome, cached1 := (cache 1).isSome }

private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

/-- A supported resampling path overwrites a present answer, unlike lazy sampling. -/
private def cachedTargetPaths : (Fin 2 × Fin 2) × (Fin 2 × Fin 2) :=
  let cache := (∅ : QueryCache HashSpec).cacheQuery 0 1
  let unchanged := Prod.fst <$> (simulateQ handler queryTwice).run cache
  let overwritten : ProbComp (Fin 2 × Fin 2) := do
    let value ← ($ᵗ Fin 2 : ProbComp (Fin 2))
    Prod.fst <$> (simulateQ handler queryTwice).run (cache.cacheQuery 0 value)
  (((simulateQ supportedAnswer unchanged).run 0).1,
    ((simulateQ supportedAnswer overwritten).run 0).1)

/-- Check returned values, selected requests and discarded cache/draw differences. -/
def run (complete : String → IO Unit) : IO Unit := do
  let cold := observe (selected queryTwice)
  let warmed := observe warmedTwice
  check (cold.value == (0, 0) && warmed.value == cold.value)
    "C3 supported-path returned pair changed"
  check (cold.selectedRequests == 2 && warmed.selectedRequests == 2)
    "C3 selected downstream requests changed"
  check (cold.fullRequests == 2 && warmed.fullRequests == 4)
    "C3 full requests do not include the actual warmup"
  check (cold.draws == 1 && warmed.draws == 2)
    "C3 repeated requests or fresh draws changed"
  check (cold.cached0 && warmed.cached0 && !cold.cached1 && warmed.cached1)
    "C3 warmed cache distinction changed"
  let pureCold := observe (selected (pure 7 : OracleComp World Nat))
  let pureWarm := observe unusedFresh
  check (pureCold.value == 7 && pureWarm.value == 7 &&
      pureCold.selectedRequests == 0 && pureWarm.selectedRequests == 0)
    "C3 unused fresh-entry value or selected cost changed"
  check (pureCold.fullRequests == 0 && pureWarm.fullRequests == 1 &&
      pureCold.draws == 0 && pureWarm.draws == 1 &&
      !pureCold.cached1 && pureWarm.cached1)
    "C3 unused fresh-entry cache or full cost changed"
  let (cachedReply, overwrittenReply) := cachedTargetPaths
  check (cachedReply == (1, 1) && overwrittenReply == (0, 0))
    "C3 cached-target resampling path did not distinguish the present answer"
  complete "c3-presampling"

end VCVioTest.QueryTracking.RandomOraclePresampling
