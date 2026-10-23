/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.Experiment

/-!
# Moving a query cost from the handler into the computation

The adversary's phase of the experiment charges each hash query through a handler wrapped with
`QueryImpl.withAddCost`, which tells the cost to a writer as it answers. A handler cannot read
back what its writer has accumulated, so the same count can be produced by the computation
itself: `run_simulateQ_withAddCost` shows that running a computation under the cost-wrapped
handler equals first rewriting it with `addCostOracle` into one that carries its own count and
then answering it with the uncharged handler. This is an equality of computations, not only of
their laws; `run_withAddCost_apply` is the single-query case.
-/

@[expose] public section

open OracleComp OracleSpec

namespace SlhDsaSecurity.WriterState

/-! ## Counting before answering, and counting after

A cost may be charged in two places: by the handler, which tells it as it answers, or by the
computation, which is first rewritten into one that carries its own count and is then answered
by an uncharged handler. The two give the same thing, and the lemma below is that equality.

Which place the charge sits in is not bookkeeping when the handler answers more than one party.
A handler charges every query that reaches it, so a computation that grows — by lifting the
verifier beside the adversary, say — is charged for the newcomer too. A count inside the
computation charges only the part it wraps, and stays put when something else is lifted
alongside. That is why the experiment's counts are moved into the computation before its phases
are put under one handler, and why they come out as the same values afterwards.
-/

/-- Running one cost-wrapped query answers it and pairs the answer with its cost. -/
theorem run_withAddCost_apply {ι : Type} {spec : OracleSpec ι} {ω : Type} [AddCommMonoid ω]
    {m : Type → Type} [Monad m] [LawfulMonad m] (impl : QueryImpl spec m)
    (costFn : spec.Domain → ω) (queried : spec.Domain) :
    ((impl.withAddCost costFn) queried).run =
      (fun value => (value, Multiplicative.ofAdd (costFn queried))) <$> impl queried := by
  simp only [QueryImpl.withAddCost, QueryImpl.withCost_apply, WriterT.run_bind,
    WriterT.run_tell, bind_assoc, pure_bind, WriterT.run_monadLift, map_eq_bind_pure_comp,
    Function.comp_def, mul_one]

/-- **Counting in the computation is counting in the handler.** -/
theorem run_simulateQ_withAddCost {ι : Type} {spec : OracleSpec ι} {ω : Type} [AddCommMonoid ω]
    {m : Type → Type} [Monad m] [LawfulMonad m] (impl : QueryImpl spec m)
    (costFn : spec.Domain → ω) {α : Type} (computation : OracleComp spec α) :
    (simulateQ (impl.withAddCost costFn) computation).run =
      simulateQ impl ((simulateQ (addCostOracle costFn) computation).run) := by
  induction computation using OracleComp.inductionOn with
  | pure value => simp only [simulateQ_pure, WriterT.run_pure]
  | query_bind queried next ih =>
    rw [simulateQ_bind, simulateQ_spec_query, WriterT.run_bind, run_withAddCost_apply,
      simulateQ_bind, simulateQ_spec_query, WriterT.run_bind, addCostOracle,
      run_withAddCost_apply, QueryImpl.ofLift_apply, simulateQ_bind, simulateQ_map,
      simulateQ_spec_query, bind_map_left, bind_map_left]
    refine bind_congr fun value => ?_
    simp only []
    rw [ih value, simulateQ_map, addCostOracle]

end SlhDsaSecurity.WriterState
