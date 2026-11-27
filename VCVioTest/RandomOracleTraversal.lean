/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import VCVio.OracleComp.QueryTracking.RandomOracle.Traversal
public import VCVio.OracleComp.QueryTracking.WriterCost
import VCVio.OracleComp.Constructions.SampleableType.Measure

/-!
# Adaptive state and cached-call observations of oracle traversal

Two finite coordinates have disjoint namespaces in an infinite input type. Their payloads
depend on earlier full answers. A repeated-query example retains a preloaded answer and charges
both calls before delegating to the cache.
-/

public section

open OracleComp OracleSpec

namespace VCVioTest.RandomOracleTraversal

/-- Coordinate namespaces retain an unbounded state-dependent payload. -/
@[expose] def input (node : Fin 2) (state : Nat) : Fin 2 × Nat := (node, state)

/-- Every full answer changes the payload of the following query. -/
@[expose] def step (_ : Fin 2) (state : Nat) (answer : Fin 3) : Nat := state + answer.val + 1

/-- Different coordinates cannot collide even if their payload states differ. -/
theorem input_separated : OracleComp.RandomOracleTraversal.Separated input := by
  intro left right hne leftState rightState heq
  exact hne (congrArg Prod.fst heq)

/-- The complete adaptive state and infinite-domain oracle cache have the fresh-sampling law. -/
theorem adaptive_full_state_cache :
    (simulateQ randomOracle
      (OracleComp.RandomOracleTraversal.evaluate input step [0, 1] 5)).run ∅ =
    OracleComp.RandomOracleTraversal.sample input step [0, 1] 5 ∅ :=
  OracleComp.RandomOracleTraversal.evaluate_eq_sample input step input_separated
    [0, 1] (by decide) 5 ∅ (by intro node _ state; rfl)

/-- The same actual coordinate list has the complete three-valued answer-table law. -/
theorem adaptive_full_table :
    (simulateQ randomOracle
      (OracleComp.RandomOracleTraversal.evaluate input step [0, 1] 5)).run ∅ =ᵈ
    ((fun outputs => OracleComp.RandomOracleTraversal.program input step outputs [0, 1] 5 ∅) <$>
      ($ᵗ (Fin 2 → Fin 3) : ProbComp (Fin 2 → Fin 3))) := by
  have tables :
      @uniformSample (Fin 2 → Fin 3) instSampleableTypePiFintype =ᵈ
        ($ᵗ (Fin 2 → Fin 3) : ProbComp (Fin 2 → Fin 3)) := by
    let _ : MeasurableSpace (Fin 2 → Fin 3) := ⊤
    exact EvalDistEq.of_evalDist_eq
      (SampleableType.evalDist_uniformSample_inst_irrel _ _)
  exact (OracleComp.RandomOracleTraversal.evalDist_evaluate_eq_uniform_program
    input step input_separated [0, 1] (by decide) 5 ∅
      (by intro node _ state; rfl)).trans (tables.map _)

/-- The zero input has a deliberately nonzero cached answer. -/
@[expose] def preloaded : QueryCache (Nat →ₒ Fin 3) :=
  (∅ : QueryCache (Nat →ₒ Fin 3)).cacheQuery 0 2

/-- Repeated queries retain the preloaded answer and each contribute before-cache cost. -/
theorem repeated_cached_calls :
    ((simulateQ ((randomOracle : QueryImpl (Nat →ₒ Fin 3)
        (StateT (QueryCache (Nat →ₒ Fin 3)) ProbComp)).withAddCost (fun _ => (1 : Nat)))
      (OracleComp.RandomOracleTraversal.evaluate (fun (_ : Unit) (_ : Nat) => 0)
        (fun _ state (answer : Fin 3) => state + answer.val) [(), ()] 0)).runAdd).run preloaded =
      pure ((4, 2), preloaded) := by
  simp [OracleComp.RandomOracleTraversal.evaluate, simulateQ_bind,
    QueryImpl.withAddCost_apply, AddWriterT.runAdd_bind,
    AddWriterT.runAdd_liftM, AddWriterT.runAdd_addTell, StateT.run_bind,
    preloaded]

end VCVioTest.RandomOracleTraversal
