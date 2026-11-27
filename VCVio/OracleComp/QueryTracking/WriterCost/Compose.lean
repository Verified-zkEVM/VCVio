/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import VCVio.OracleComp.QueryTracking.WriterCost.Map

/-!
# Joint composition of additive query observers

Two additive observers retain the same returned value and query traffic as one paired policy.
Each cost accumulates in its original chronological order; neither monoid needs commutativity.
-/

public section

open OracleSpec

namespace OracleComp

/-- Two identity-forwarding cost folds retain the complete result and both ordered costs. -/
theorem simulateQ_withAddCost_runAdd {ι : Type} (spec : OracleSpec ι)
    {α C D : Type} [AddMonoid C] [AddMonoid D]
    (leftCost : spec.Domain → C) (rightCost : spec.Domain → D) (body : OracleComp spec α) :
    (simulateQ ((QueryImpl.id' spec).withAddCost rightCost)
      ((simulateQ ((QueryImpl.id' spec).withAddCost leftCost) body).runAdd)).runAdd =
      (fun result => ((result.1, result.2.1), result.2.2)) <$>
        (simulateQ ((QueryImpl.id' spec).withAddCost
          (fun input => (leftCost input, rightCost input))) body).runAdd := by
  induction body using OracleComp.inductionOn with
  | pure value => simp
  | query_bind input next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, AddWriterT.runAdd_bind]
      simp [QueryImpl.withAddCost_apply, AddWriterT.runAdd_bind, ih, Functor.map_map]

end OracleComp
