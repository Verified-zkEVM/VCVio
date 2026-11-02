/-
Copyright (c) 2026 Tom Wambsgans, Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans, Alexander Hicks
-/

module
public import HashSig.SLHDSA.SHAKE128s.Proof.WarmedGame

/-! # Ordinary consumers of the warmed SLH-DSA outcome laws

The comparison retains the full counted outcome. A local recursive traversal supplies an
operational comparison with the canonical lifted traversal; final caches are not identified by
the probability laws.
-/

public section

open OracleComp OracleSpec SLHDSA.SHAKE128s

namespace HashSigTest.SLHDSA.Refactor.Presampling

private noncomputable def recursiveTraversal {State Index : Type}
    (input : Index → State → Bytes) (step : Index → State → HashOutput → State) :
    List Index → State → OracleComp OracleWorld State
  | [], state => pure state
  | node :: nodes, state => do
      let answer ← query (spec := OracleWorld) (Sum.inr (input node state))
      recursiveTraversal input step nodes (step node state answer)

/-- The recursive world traversal is the canonical lifted program on all inputs. -/
private theorem recursiveTraversal_eq_worldEvaluate {State Index : Type}
    (input : Index → State → Bytes) (step : Index → State → HashOutput → State)
    (nodes : List Index) (state : State) :
    recursiveTraversal input step nodes state = Presample.worldEvaluate input step nodes state := by
  rw [Presample.worldEvaluate_eq_liftM, GraphFreshSampling.evaluate_eq_traversal]
  induction nodes generalizing state with
  | nil => rfl
  | cons node rest ih =>
      rw [recursiveTraversal, OracleComp.RandomOracleTraversal.evaluate, liftM_bind]
      exact congrArg (Bind.bind _) (funext fun answer => ih (step node state answer))

/-- The actual game retains its complete outcome and selected count under warming. -/
theorem counted_outcome_law (adversary : Security.Adversary) :
    ((fun result => result.1.2) <$> WarmedGame.warmedRun adversary) =ᵈ
      (Prod.fst <$> WholeGameStructural.instrumentedRun adversary) :=
  WarmedGame.evalDist_outcome adversary

/-- Every event of the jointly returned outcome and selected count has the same probability. -/
theorem counted_event_law (adversary : Security.Adversary) (event : Security.Outcome × Nat → Prop) :
    Pr{let result ← WholeGameStructural.instrumentedRun adversary}[event result.1] =
      Pr{let result ← WarmedGame.warmedRun adversary}[event result.1.2] :=
  WarmedGame.prEvent_warmed adversary event

end HashSigTest.SLHDSA.Refactor.Presampling
