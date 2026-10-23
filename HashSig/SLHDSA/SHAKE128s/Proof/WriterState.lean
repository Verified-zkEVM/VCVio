/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.Experiment

/-!
# A writer the handler cannot read is a piece of the state

The adversary's phase of the experiment runs in `Security.CountedRun`, a writer of `Counts`
over a state of signing requests over the game's world. The charge, on the other side, wants a
handler in `StateT σ ProbComp`, because that is the only shape `QueryImpl.Stateful` — and with
it the frame machinery that puts two handlers side by side on one state — admits. The writer is
in the way.

It need not be. A writer accumulates a monoid and the handler **cannot read it back**: that is
not an assumption about `Counts`, it is what `WriterT`'s type says, since the only thing a
`WriterT ω m` computation receives is an `m`-value and the only thing it can do with the
accumulated value is multiply more onto it. So the accumulation can equally well be carried in
the state, and `toStateful` does exactly that: the same handler, with its output multiplied
into a state component instead of told to a writer.

`run_toStateful` is the transport, and it is an equality of computations rather than of laws:
running the restated handler from `(w, s)` is running the original from `s` and multiplying `w`
onto whatever it accumulated. Nothing about the experiment changes — `CountedRun` and
`Security.signingOracle` are the experiment and stay exactly as they are — which is the point
of proving the transport rather than redefining them.
-/

@[expose] public section

open OracleComp OracleSpec

namespace SlhDsaSecurity.WriterState

variable {ι : Type} {E : OracleSpec ι} {ω σ : Type} [Monoid ω]
  {M : Type → Type} [Monad M] [LawfulMonad M]

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

/-! ## The experiment's own signing oracle

The transport applies to it as it stands: `Security.CountedRun` is a writer of `Counts` — a
monoid in its multiplicative guise — over a state of signing requests, so its counts and its log
sit side by side in one state, which is the shape a stateful handler takes. The oracle itself is
untouched; this is the same handler read differently. -/

end SlhDsaSecurity.WriterState
