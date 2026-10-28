/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.OracleComp.QueryTracking.RandomOracle.Simulation
public import Mathlib.Algebra.Module.BigOperators

/-! # Weighted queries to a shared base oracle

A finite list of weighted labels describes one linear target. All labels are queried through
one oracle, so repeated labels, including labels shared by different targets, use the same
random-oracle cache. The construction does not require a finite label or message type.
-/

public section

open OracleComp OracleSpec

namespace GroupModel.LinearFunctional

/-- Query a list of bases in order and sum their scalar multiples. -/
@[expose] def weightedQuery {F I G : Type} [AddMonoid G] [SMul F G] :
    List (I × F) → OracleComp (I →ₒ G) G
  | [] => pure 0
  | (i, w) :: rest => do
      let h ← (I →ₒ G).query i
      let tail ← weightedQuery rest
      return w • h + tail

/-- A fixed oracle table interprets a weighted query as its list sum. -/
theorem simulateQ_weightedQuery {F I G : Type} [AddMonoid G] [SMul F G]
    (H : I → G) (terms : List (I × F)) :
    simulateQ (fun i => pure (H i) : QueryImpl (I →ₒ G) ProbComp) (weightedQuery terms) =
      pure ((terms.map fun p => p.2 • H p.1).sum) := by
  induction terms with
  | nil => simp [weightedQuery]
  | cons p rest ih => simp [weightedQuery, ih]

/-- Forwarding randomness and fixing the base oracle gives the same weighted list sum. -/
theorem simulateQ_unifFwd_weightedQuery {F I G : Type} [AddMonoid G] [SMul F G]
    (H : I → G) (terms : List (I × F)) :
    simulateQ (unifFwdAnswerImpl (QueryImpl.ofFn H))
      (liftM (weightedQuery terms) : OracleComp (unifSpec + (I →ₒ G)) G) =
      pure ((terms.map fun p => p.2 • H p.1).sum) := by
  change simulateQ (unifSpec.passthrough + (fun i => pure (H i) : QueryImpl (I →ₒ G) ProbComp))
    (OracleComp.liftComp (weightedQuery terms) (unifSpec + (I →ₒ G))) = _
  exact (QueryImpl.simulateQ_add_liftComp_right
    (unifSpec.passthrough : QueryImpl unifSpec ProbComp)
    (fun i => pure (H i) : QueryImpl (I →ₒ G) ProbComp) (weightedQuery terms)).trans
    (simulateQ_weightedQuery H terms)

end GroupModel.LinearFunctional
