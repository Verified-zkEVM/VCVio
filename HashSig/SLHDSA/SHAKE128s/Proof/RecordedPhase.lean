/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.RecordedQueries
public import HashSig.SLHDSA.SHAKE128s.Proof.WriterState

/-!
# The phase's charge and its record, moved inside the computation together

A handler charges every query that reaches it, which is harmless while it answers the adversary
alone and wrong as soon as the phases are put under one handler: the verifier's queries, counted
as verification work, would be charged as the adversary's hash work on top of it, and
`Counts.work` adds the two. So the charge moves into the computation, where it counts the phase
it wraps and nothing that is later lifted alongside.

**The record moves with it, and must.** `RecordedQueries` accumulates the record in the *same*
writer as the counters, which is what makes `Multiset.card recorded = counts.work` hold by
construction at every query. Leaving the recording on the handler while the charge moved inward
would split that writer and break the invariant without breaking anything that typechecks. So
the cost function below is `Tally`-valued — a hash call and its input recorded on the
adversary's own queries, one signing request and nothing recorded on its requests — and
`Faithful` remains a property of that cost function, unaffected by where it is applied.

What is left answering tells nothing and keeps only the log, so it is already the stateful
handler the composition wants: `QueryImpl.Stateful.link` puts an outer handler and an inner one
together over the product of their states, and `simulateQ_link_run` says that running the
composite *is* the nesting the experiment writes. That is what the move is for — the signer
becomes something a handler does rather than something the computation does, so its reads of
the cell table are frozen when the run is stalled.

**Why not the frame machinery next door.** A `Frame`'s two lenses must be *separated*, so
`parSumWith` would give the hash half and the signing half states that cannot interfere, and
they could then not accumulate into one counter. The experiment's single counter would have
become two components whose product is the real count, changing the accounting shape for
nothing. The two halves are already summed over one target monad in the game, so once the
charge has moved they are a single handler, and `link` uses a product only where one genuinely
belongs: between the outer handler's state and the inner handler's.

**A warning for anything working over the sum spec.**
`(OracleWorld + SigningSpec).Range (Sum.inr request)` and `SigningSpec.Range request` are equal
only semireducibly, so a lemma phrased at the summand will not rewrite an occurrence sitting at
the sum: `rw` reports the pattern missing and `simp` declines without saying why, and unfolding
past it yields terms that are not type-correct at `instances` transparency. The rule is to
phrase each lemma at the index its goal has — `run_unchargedPhase_inr` is about
`unchargedPhase signer (Sum.inr request)`, not about the signer — and to convert the index once,
inside that lemma's own proof, where it is local. No lifting law is involved; an instance search
that fails here is failing downstream of the mismatch and cannot fix it.
-/

@[expose] public section

open OracleComp OracleSpec

namespace SlhDsaSecurity.RecordedPhase

variable {α : Type}

open Security RecordedQueries

/-- What the adversary's phase charges and records, query by query. -/
def phaseCost : (OracleWorld + SigningSpec).Domain → Tally
  | .inl input => (Counts.single .hash (hashCost input), recordOf input)
  | .inr _ => (Counts.single .signing 1, 0)

/-- The signer with nothing charged and nothing recorded: it answers and records to the log. -/
noncomputable def unchargedSigner (signer : Message → OracleComp OracleWorld (Option Bytes)) :
    QueryImpl SigningSpec (StateT SigningLog (OracleComp OracleWorld)) := fun request => do
  let answer ← liftM (signer request)
  modify (fun signed => signed ++ [⟨request, answer⟩])
  return answer

/-- The phase's pair of oracles with nothing charged and nothing recorded. -/
noncomputable def unchargedPhase (signer : Message → OracleComp OracleWorld (Option Bytes)) :
    QueryImpl (OracleWorld + SigningSpec) (StateT SigningLog (OracleComp OracleWorld)) :=
  QueryImpl.ofLift OracleWorld (StateT SigningLog (OracleComp OracleWorld)) +
    unchargedSigner signer

/-- A cost told in front of a lifted state computation, at any writer. -/
theorem run_tell_liftM {ω : Type} [AddCommMonoid ω] {α : Type} (cost : ω)
    (x : StateT SigningLog (OracleComp OracleWorld) α) (log : SigningLog) :
    ((WriterT.run ((do tell (Multiplicative.ofAdd cost); liftM x :
        AddWriterT ω (StateT SigningLog (OracleComp OracleWorld)) α))).run log) =
      (fun step => ((step.1, Multiplicative.ofAdd cost), step.2)) <$> x.run log := by
  rw [WriterT.run_bind, WriterT.run_tell, StateT.run_bind, StateT.run_pure, pure_bind,
    StateT.run_map, run_liftM_inner]
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def, mul_one]

/-- The uncharged phase's run at a signing request: it signs, appends, and returns. -/
theorem run_unchargedPhase_inr (signer : Message → OracleComp OracleWorld (Option Bytes))
    (request : Message) (log : SigningLog) :
    ((unchargedPhase signer (Sum.inr request)).run log) =
      signer request >>= fun answer => pure (answer, log ++ [⟨request, answer⟩]) := by
  change ((unchargedSigner signer request).run log) = _
  rw [unchargedSigner]
  simp only [StateT.run_bind, StateT.run_liftM, StateT.run_modify, StateT.run_pure,
    bind_assoc, pure_bind]

/-- **The phase's pair of oracles is the uncharged pair, charged and recorded in front.** -/
theorem phase_eq (signer : Message → OracleComp OracleWorld (Option Bytes)) :
    recordedAdversaryImpl + recordedSigningOracle signer =
      (unchargedPhase signer).withAddCost phaseCost := by
  funext queried
  cases queried with
  | inl input =>
    rw [QueryImpl.add_apply_inl, recordedAdversaryImpl, QueryImpl.withAddCost_apply,
      QueryImpl.withAddCost_apply]
    rfl
  | inr request =>
    funext log
    change (WriterT.run (recordedSigningOracle signer request)).run log =
      (WriterT.run (((unchargedPhase signer).withAddCost phaseCost) (Sum.inr request))).run log
    rw [QueryImpl.withAddCost, QueryImpl.withCost_apply, run_recordedSigningOracle,
      run_tell_liftM, run_unchargedPhase_inr]
    simp [phaseCost]

/-- **The phase with its charge and its record inside the computation.** What answers tells
nothing, so a computation lifted alongside the adversary's is neither charged nor recorded for
being there. -/
theorem run_phase_counted (signer : Message → OracleComp OracleWorld (Option Bytes)) {α : Type}
    (computation : OracleComp (OracleWorld + SigningSpec) α) :
    WriterT.run (simulateQ (recordedAdversaryImpl + recordedSigningOracle signer) computation) =
      simulateQ (unchargedPhase signer)
        ((simulateQ (addCostOracle phaseCost) computation).run) := by
  rw [phase_eq, WriterState.run_simulateQ_withAddCost]

end SlhDsaSecurity.RecordedPhase
