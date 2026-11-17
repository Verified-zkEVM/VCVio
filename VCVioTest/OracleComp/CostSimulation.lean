/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import VCVio.OracleComp.QueryTracking.CostModel.Simulation

/-!
# Vector costs for response-dependent oracle substitution

Each source query is implemented by two target queries with the same label. The source program's
second query label depends on the first reply. The cost bound covers both response branches, and
executing fixed handlers distinguishes four repeated false-label calls from two calls per label.
An empty answer type separately checks that complete-path bounds do not imply availability.
-/

public section

open OracleSpec OracleComp

namespace VCVioTest.OracleComp.CostSimulation

/-- Two query labels, both returning booleans. -/
abbrev signature : OracleSpec Bool := fun _ => Bool

/-- One natural-number counter for each target query label. -/
abbrev Profile := Bool → Nat

/-- A target query charges one unit at its own label. -/
def targetCost : CostModel signature Profile :=
  ⟨fun label coordinate => if coordinate = label then 1 else 0⟩

/-- A source query pays for two target queries at its own label. -/
def sourceCost : CostModel signature Profile :=
  ⟨fun label coordinate => if coordinate = label then 2 else 0⟩

/-- Each source query retains the second of two target replies at its own label. -/
def route : QueryImpl signature (OracleComp signature) := fun label => do
  let _ ← (signature.query label : OracleComp signature Bool)
  (signature.query label : OracleComp signature Bool)

/-- The observed first reply selects the next source query. -/
def program : OracleComp signature Bool := do
  let reply ← (signature.query false : OracleComp signature Bool)
  (signature.query reply : OracleComp signature Bool)

/-- The actual route's repeated queries fit the source query's two-unit charge. -/
theorem route_bound (label : Bool) :
    WorstCaseCostBound (route label) targetCost (sourceCost.queryCost label) := by
  have hquery := worstCaseCostBound_query label targetCost
  have hcost : targetCost.queryCost label + targetCost.queryCost label =
      sourceCost.queryCost label := by
    funext coordinate
    by_cases h : coordinate = label <;> simp [targetCost, sourceCost, h]
  simpa only [route, hcost, WorstCaseCostBound, AddWriterT.PathwiseCostAtMost] using
    hquery.bind (fun _ => hquery)

/-- Two repeated calls do not fit a single unit at their observed coordinate. -/
example : ¬ WorstCaseCostBound (route false) targetCost (fun _ => 1) := by
  intro bound
  have member : (false, Multiplicative.ofAdd (targetCost.queryCost false)) ∈
      support (costDist (signature.query false : OracleComp signature Bool) targetCost) := by
    rw [costDist_query]
    simp
  have tooSmall := (worstCaseCostBound_query_bind_iff _ _ _ _).mp bound false _ member
  exact Nat.not_succ_le_self 1 (tooSmall false)

/-- Four false-label calls or two calls per label fit the same vector bound. -/
def bound : Profile := fun coordinate => if coordinate then 2 else 4

/-- Both possible first replies fit the source vector bound. -/
theorem program_bound : WorstCaseCostBound program sourceCost bound := by
  have hfirst := worstCaseCostBound_query false sourceCost
  have hnext (reply : Bool) :
      WorstCaseCostBound (signature.query reply : OracleComp signature Bool) sourceCost
        (fun _ => 2) := by
    intro result member coordinate
    refine (worstCaseCostBound_query reply sourceCost result member coordinate).trans ?_
    by_cases h : coordinate = reply <;> simp [sourceCost, h]
  have hcost : sourceCost.queryCost false + (fun _ => 2) = bound := by
    funext coordinate
    cases coordinate <;> rfl
  simpa only [program, hcost, WorstCaseCostBound, AddWriterT.PathwiseCostAtMost] using
    hfirst.bind hnext

/-- The same concrete routing code receives the transferred vector bound. -/
example : WorstCaseCostBound (simulateQ route program) targetCost bound :=
  program_bound.simulateQ route route_bound

/-- Cost instrumentation preserves the actual routed computation's returned values. -/
example : Prod.fst <$> costDist (simulateQ route program) targetCost = simulateQ route program :=
  fst_map_costDist _ _

/-- Every supported routed result is retained by the source support witness. -/
example (result : Bool × Multiplicative Profile)
    (member : result ∈ support (costDist (simulateQ route program) targetCost)) :
    ∃ charge : Profile,
      (result.1, Multiplicative.ofAdd charge) ∈ support (costDist program sourceCost) ∧
        Multiplicative.toAdd result.2 ≤ charge :=
  mem_support_costDist_simulateQ route program sourceCost targetCost route_bound result member

/-- Execute the actual route with a handler returning the same fixed bit at every query. -/
def fixedRun (reply : Bool) : Bool × Profile :=
  (simulateQ (QueryImpl.withAddCost (fun _ => pure reply : QueryImpl signature Id)
      targetCost.queryCost)
    (simulateQ route program)).runAdd.run

example : (fixedRun false).1 = false ∧ (fixedRun false).2 false = 4 ∧
    (fixedRun false).2 true = 0 := by
  simp [fixedRun, program, route, QueryImpl.withAddCost_apply, targetCost]

example : (fixedRun true).1 = true ∧ (fixedRun true).2 false = 2 ∧
    (fixedRun true).2 true = 2 := by
  simp [fixedRun, program, route, QueryImpl.withAddCost_apply, targetCost]

/-- Run both concrete response branches and check their replies and vector query charges. -/
def run : IO Unit := do
  let first := fixedRun false
  let second := fixedRun true
  unless first.1 == false && second.1 == true &&
      [first.2 false, first.2 true, second.2 false, second.2 true] == [4, 0, 2, 2] do
    throw (IO.userError "Unexpected replies or vector costs from substituted programs")
  IO.println "Oracle cost substitution checks passed."

/-- A query with no possible response. -/
abbrev emptySignature : OracleSpec Unit := fun _ => Empty

/-- With no completed response, the complete-path bound is vacuous even at budget zero. -/
example : WorstCaseCostBound (do
      let _ ← (emptySignature.query () : OracleComp emptySignature Empty)
      pure ()) (⟨fun _ => 1⟩ : CostModel emptySignature Nat) 0 := by
  rw [worstCaseCostBound_query_bind_iff]
  intro response
  exact response.elim

end VCVioTest.OracleComp.CostSimulation
