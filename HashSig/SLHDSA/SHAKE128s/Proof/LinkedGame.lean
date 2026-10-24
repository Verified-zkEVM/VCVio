/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.KeygenValue
public import HashSig.SLHDSA.SHAKE128s.Proof.RecordedPhase

/-!
# The game as one computation and one handler

With the keys handed in and the phase's charge and record moved inside the computation, the
experiment's nesting is undone. `linkedAfterSeeds` is the game written as a single
computation over `OracleWorld + SigningSpec` — the adversary's own phase counted and recorded
where it stands, the verifier lifted beside it with its own instrumentation intact — and
`unchargedPhase` is the single handler that answers it.

Three things the shape is chosen to preserve, each of which would be a silent failure.

* **The outcome.** `signed` is no longer a value the computation returns; it is the handler's
  final state. So the outcome is assembled after the run, by `outcomeOf`, from the value and
  that state. The law below is an equality of computations with `outcomeOf` applied pointwise,
  so every field — `counts` and `signed` among them — is literally the same value on both sides.
* **The counts.** The verifier keeps `countRecorded verifierCost` around it, so its queries are
  charged as verification work and not as the adversary's. That is the whole reason the charge
  moved into the computation first: a handler charges every query that reaches it, and the
  verifier's queries now reach this one.
* **The record.** `countRecorded` is a computation-level wrapper, so lifting the verifier keeps
  its queries in the record, and the adversary's are recorded by `phaseCost` where it stands.
  The honest phase is recorded by neither, which is what the stripping bought.

**On the lift, which is not as innocent as it looks.** There are at least three terms denoting "a
world computation in the phase's spec" — the coercion as this file's elaborator synthesizes it, the
coercion as VCVio's `QueryImpl.simulateQ_add_liftComp_left` is stated at, and the left injection
written out by hand — and *no two of them are definitionally equal*. Checking that is one `rfl`, and
it fails. So `liftWorld` pins the one the upstream lemma uses, by supplying the instance argument,
and is the only place in this development that supplies it; everything else goes through
`liftWorld`. Nothing is taken on trust by doing so: `recordedAfterSeedsAt` contains no lift at all,
so `recordedAfterSeedsAt_eq` never asks two lifts to agree, and it is that law rather than the
lift's identity that says the construction is the game.

What the signer gains by moving is what the whole exercise is for: it is something the handler
does, so its reads of the cell table are frozen when the run is stalled.
-/

public section

open OracleComp OracleSpec

namespace SlhDsaSecurity.LinkedGame

variable {α : Type}

open Security RecordedQueries RecordedPhase KeygenValue

/-! ## The lift, pinned -/

/-- A world computation in the phase's spec, at the instance the composition lemmas use. -/
@[expose] noncomputable def liftWorld {α : Type} (computation : OracleComp OracleWorld α) :
    OracleComp (OracleWorld + SigningSpec) α :=
  @OracleComp.liftComp _ _ OracleWorld α computation (OracleWorld + SigningSpec)
    (instMonadLiftTOfMonadLift (m := OracleQuery OracleWorld) (n := OracleQuery OracleWorld)
      (o := OracleQuery (OracleWorld + SigningSpec)))

/-- **A pair of handlers answers a lifted world computation with its left half.** -/
theorem simulateQ_liftWorld {α : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (world : QueryImpl OracleWorld m) (signing : QueryImpl SigningSpec m)
    (computation : OracleComp OracleWorld α) :
    simulateQ (world + signing) (liftWorld computation) = simulateQ world computation :=
  QueryImpl.simulateQ_add_liftComp_left world signing computation

/-- Simulating a world computation by the handler that forwards every query is that
computation, with the log left alone. -/
theorem run_simulateQ_ofLift {α : Type} (computation : OracleComp OracleWorld α) :
    ∀ log : SigningLog,
      (simulateQ (QueryImpl.ofLift OracleWorld (StateT SigningLog (OracleComp OracleWorld)))
          computation).run log = (fun value => (value, log)) <$> computation := by
  induction computation using OracleComp.inductionOn with
  | pure value => intro log; simp
  | query_bind queried next ih =>
    intro log
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, QueryImpl.ofLift_apply,
      StateT.run_monadLift, map_bind, bind_assoc, pure_bind, ih]

/-- **The uncharged phase forwards a lifted world computation**, leaving the log alone. -/
theorem run_unchargedPhase_lift {α : Type}
    (signer : Message → OracleComp OracleWorld (Option Bytes))
    (computation : OracleComp OracleWorld α) (log : SigningLog) :
    (simulateQ (unchargedPhase signer) (liftWorld computation)).run log =
      (fun value => (value, log)) <$> computation := by
  rw [unchargedPhase, simulateQ_liftWorld]
  exact run_simulateQ_ofLift computation log

/-! ## The game, as one computation -/

/-- The game as one computation: the adversary's phase counted and recorded where it stands,
the verifier lifted beside it with its own instrumentation. -/
@[expose]
noncomputable def linkedAfterSeeds (adversary : Adversary) (keys : SecretKey × PublicKey) :
    OracleComp (OracleWorld + SigningSpec)
      ((Forgery × Multiplicative Tally) × (Bool × Tally)) := do
  let adversaryStep ← (simulateQ (addCostOracle phaseCost) (adversary.main keys.2)).run
  let verifierStep ← liftWorld (countRecorded verifierCost
    (Scheme.verify keys.2 adversaryStep.1.message adversaryStep.1.signature))
  pure (adversaryStep, verifierStep)

/-- The outcome and the record, assembled from the run's value and the handler's final log. -/
@[expose]
def outcomeOf (result : ((Forgery × Multiplicative Tally) × (Bool × Tally)) × SigningLog) :
    Outcome × Multiset Bytes :=
  ({ forgery := result.1.1.1
     signed := result.2
     verified := result.1.2.1
     counts := (Multiplicative.toAdd result.1.1.2).1 + result.1.2.2.1 },
    (Multiplicative.toAdd result.1.1.2).2 + result.1.2.2.2)

/-- **The game is that computation under that handler.** An equality of computations, so the
outcome and the record come out as the same values they always did.

The nesting never looks at which signer it is nesting, since `RecordedPhase.run_phase_counted`
and `run_unchargedPhase_lift` are stated at an arbitrary one. -/
theorem recordedAfterSeedsAt_eq (adversary : Adversary) (keys : SecretKey × PublicKey)
    (warm : QueryCache HashSpec) :
    recordedAfterSeedsAt adversary keys warm =
      outcomeOf <$> (simulateQ (unchargedPhase (StrippedGame.strippedSign warm keys.1))
        (linkedAfterSeeds adversary keys)).run [] := by
  rw [recordedAfterSeedsAt, linkedAfterSeeds, simulateQ_bind, StateT.run_bind,
    ← run_phase_counted, map_bind]
  refine bind_congr fun adversaryStep => ?_
  rw [simulateQ_bind, StateT.run_bind, run_unchargedPhase_lift, bind_map_left, map_bind]
  refine bind_congr fun verifierStep => ?_
  rw [simulateQ_pure, StateT.run_pure, map_pure]
  rfl

end SlhDsaSecurity.LinkedGame
