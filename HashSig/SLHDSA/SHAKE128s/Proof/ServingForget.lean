/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.PhaseFusion
public import HashSig.SLHDSA.SHAKE128s.Proof.WarmedGame

/-!
# What the brackets are invisible to

The carrier tail runs the game under a handler that **files** and under a signing oracle that
raises and lowers a **framing**. The question every consumer asks is what these change. The
answer is the recordings and the carrier, and nothing else. This file states that once and
generically, so that the equations such a tail owes are instances of one lemma.

**It has to be a projection law, because the brackets are not invisible to the handler.** A
filing test that reads the framing is exactly a test whose answer the brackets change. What is
invisible is everything a projection keeps. Given a map `π` out of the outer state that the
brackets leave alone and that the handler's own runs commute with (`ForgetsAlong`), the
bracketed phase **is** the unbracketed one through `π` (`run_fuseServing_map`).

For the carrier that map is "take the cache": the handler's runs commute with it because the
recorder answers exactly as the shared oracle does, and the brackets leave it alone because they
write only the framing. So the game's forgery, its log, its counts and its cache come out
unchanged, while the recordings, which `π` drops, are free to differ.

A second form, `run_fuseServing_conj`, lets `π` carry each bracket to a bracket on the other
side instead of collapsing it. `bind_of_forgetsAlong` and `bind_of_fuseServing_conj` restate the
transports in bind form, so that stages chain by `bind_congr`.
-/

@[expose] public section

open OracleComp OracleSpec

namespace SlhDsaSecurity.ServingForget

variable {α β γ : Type}

open Security PhaseFusion

variable {ω : Type} [Monoid ω] {S S' : Type}

/-- **A handler forgets along `π`**: running it and projecting is projecting and running. The
only thing a bracketed presentation asks of the handler underneath it. -/
def ForgetsAlong (π : S → S') (outer : QueryImpl OracleWorld (StateT S ProbComp))
    (outer' : QueryImpl OracleWorld (StateT S' ProbComp)) : Prop :=
  ∀ {β : Type} (computation : OracleComp OracleWorld β) (state : S),
    (fun z : β × S => (z.1, π z.2)) <$> (simulateQ outer computation).run state =
      (simulateQ outer' computation).run (π state)

/-- **One step of the bracketed phase is one step of the unbracketed one, through `π`.** The
adversary's step is the fused step unchanged; the signing step brackets, and `π` cannot see
the bracket. -/
theorem run_fuseServing_step_map (π : S → S')
    (outer : QueryImpl OracleWorld (StateT S ProbComp))
    (outer' : QueryImpl OracleWorld (StateT S' ProbComp))
    (inner : QueryImpl (OracleWorld + SigningSpec)
      (WriterT ω (StateT SigningLog (OracleComp OracleWorld))))
    (before : Message → S → S) (after : S → S)
    (hbefore : ∀ (request : Message) (state : S), π (before request state) = π state)
    (hafter : ∀ state : S, π (after state) = π state)
    (hforget : ForgetsAlong π outer outer')
    (queried : (OracleWorld + SigningSpec).Domain) (accumulated : ω) (log : SigningLog)
    (state : S) :
    (fun step : (OracleWorld + SigningSpec).Range queried × (ω × SigningLog × S) =>
        (step.1, (step.2.1, step.2.2.1, π step.2.2.2))) <$>
      ((fuseServing outer inner before after) queried).run (accumulated, log, state) =
      ((fuse outer' inner) queried).run (accumulated, log, π state) := by
  rcases queried with world | request
  · change (fun step : (OracleWorld + SigningSpec).Range (Sum.inl world) ×
        (ω × SigningLog × S) => (step.1, (step.2.1, step.2.2.1, π step.2.2.2))) <$>
      ((fuse outer inner) (Sum.inl world)).run (accumulated, log, state) = _
    rw [fuse_run, fuse_run, map_eq_bind_pure_comp, bind_assoc,
      ← hforget (((inner (Sum.inl world)).run).run log) state, map_eq_bind_pure_comp, bind_assoc]
    refine bind_congr fun step => ?_
    simp [Function.comp_def]
  · change (fun step : (OracleWorld + SigningSpec).Range (Sum.inr request) ×
        (ω × SigningLog × S) => (step.1, (step.2.1, step.2.2.1, π step.2.2.2))) <$>
      ((simulateQ outer (((inner (Sum.inr request)).run).run log)).run (before request state) >>=
        fun step => (pure (step.1.1.1, (accumulated * step.1.1.2, step.1.2, after step.2)) :
          ProbComp _)) = _
    rw [fuse_run]
    simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def, hafter]
    conv_rhs => rw [← hbefore request state,
      ← hforget (((inner (Sum.inr request)).run).run log) (before request state)]
    simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def]

/-- **And therefore the whole phase.** -/
theorem run_fuseServing_map (π : S → S')
    (outer : QueryImpl OracleWorld (StateT S ProbComp))
    (outer' : QueryImpl OracleWorld (StateT S' ProbComp))
    (inner : QueryImpl (OracleWorld + SigningSpec)
      (WriterT ω (StateT SigningLog (OracleComp OracleWorld))))
    (before : Message → S → S) (after : S → S)
    (hbefore : ∀ (request : Message) (state : S), π (before request state) = π state)
    (hafter : ∀ state : S, π (after state) = π state)
    (hforget : ForgetsAlong π outer outer') {α : Type}
    (computation : OracleComp (OracleWorld + SigningSpec) α) :
    ∀ (accumulated : ω) (log : SigningLog) (state : S),
      (fun step : α × (ω × SigningLog × S) =>
          (step.1, (step.2.1, step.2.2.1, π step.2.2.2))) <$>
        (simulateQ (fuseServing outer inner before after) computation).run
          (accumulated, log, state) =
      (simulateQ (fuse outer' inner) computation).run (accumulated, log, π state) := by
  induction computation using OracleComp.inductionOn with
  | pure value =>
    intro accumulated log state
    simp only [simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind queried next ih =>
    intro accumulated log state
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind,
      simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
      ← run_fuseServing_step_map π outer outer' inner before after hbefore hafter hforget queried
        accumulated log state,
      bind_map_left]
    refine bind_congr fun step => ?_
    exact ih step.1 step.2.1 step.2.2.1 step.2.2.2

/-! ## The same, with the brackets transported rather than killed

`run_fuseServing_map` is for a `π` that cannot see a bracket, so its right-hand side is the
**unbracketed** fusion. The conjugation law below asks `π` to *carry* each bracket to a bracket
on the other side, rather than to collapse it, and concludes at `fuseServing` on both sides.
`run_fuseServing_map` is the case where both target brackets are the identity.
-/

/-- **One step of the bracketed phase, with the brackets carried through `π`.** -/
theorem run_fuseServing_step_conj (π : S → S')
    (outer : QueryImpl OracleWorld (StateT S ProbComp))
    (outer' : QueryImpl OracleWorld (StateT S' ProbComp))
    (inner : QueryImpl (OracleWorld + SigningSpec)
      (WriterT ω (StateT SigningLog (OracleComp OracleWorld))))
    (before : Message → S → S) (after : S → S)
    (before' : Message → S' → S') (after' : S' → S')
    (hbefore : ∀ (request : Message) (state : S),
      π (before request state) = before' request (π state))
    (hafter : ∀ state : S, π (after state) = after' (π state))
    (hforget : ForgetsAlong π outer outer')
    (queried : (OracleWorld + SigningSpec).Domain) (accumulated : ω) (log : SigningLog)
    (state : S) :
    (fun step : (OracleWorld + SigningSpec).Range queried × (ω × SigningLog × S) =>
        (step.1, (step.2.1, step.2.2.1, π step.2.2.2))) <$>
      ((fuseServing outer inner before after) queried).run (accumulated, log, state) =
      ((fuseServing outer' inner before' after') queried).run (accumulated, log, π state) := by
  rcases queried with world | request
  · change (fun step : (OracleWorld + SigningSpec).Range (Sum.inl world) ×
        (ω × SigningLog × S) =>
        (step.1, (step.2.1, step.2.2.1, π step.2.2.2))) <$>
      ((fuse outer inner) (Sum.inl world)).run (accumulated, log, state) =
      ((fuse outer' inner) (Sum.inl world)).run (accumulated, log, π state)
    rw [fuse_run, fuse_run, map_eq_bind_pure_comp, bind_assoc,
      ← hforget (((inner (Sum.inl world)).run).run log) state, map_eq_bind_pure_comp,
      bind_assoc]
    refine bind_congr fun step => ?_
    simp [Function.comp_def]
  · change (fun step : (OracleWorld + SigningSpec).Range (Sum.inr request) ×
        (ω × SigningLog × S) =>
        (step.1, (step.2.1, step.2.2.1, π step.2.2.2))) <$>
      ((simulateQ outer (((inner (Sum.inr request)).run).run log)).run (before request state) >>=
        fun step => (pure (step.1.1.1, (accumulated * step.1.1.2, step.1.2, after step.2)) :
          ProbComp _)) =
      ((simulateQ outer' (((inner (Sum.inr request)).run).run log)).run
          (before' request (π state)) >>= fun step =>
        (pure (step.1.1.1, (accumulated * step.1.1.2, step.1.2, after' step.2)) : ProbComp _))
    rw [← hbefore request state,
      ← hforget (((inner (Sum.inr request)).run).run log) (before request state)]
    simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def, hafter]

/-- **And therefore the whole phase, with the brackets carried.** -/
theorem run_fuseServing_conj (π : S → S')
    (outer : QueryImpl OracleWorld (StateT S ProbComp))
    (outer' : QueryImpl OracleWorld (StateT S' ProbComp))
    (inner : QueryImpl (OracleWorld + SigningSpec)
      (WriterT ω (StateT SigningLog (OracleComp OracleWorld))))
    (before : Message → S → S) (after : S → S)
    (before' : Message → S' → S') (after' : S' → S')
    (hbefore : ∀ (request : Message) (state : S),
      π (before request state) = before' request (π state))
    (hafter : ∀ state : S, π (after state) = after' (π state))
    (hforget : ForgetsAlong π outer outer') {α : Type}
    (computation : OracleComp (OracleWorld + SigningSpec) α) :
    ∀ (accumulated : ω) (log : SigningLog) (state : S),
      (fun step : α × (ω × SigningLog × S) =>
          (step.1, (step.2.1, step.2.2.1, π step.2.2.2))) <$>
        (simulateQ (fuseServing outer inner before after) computation).run
          (accumulated, log, state) =
      (simulateQ (fuseServing outer' inner before' after') computation).run
        (accumulated, log, π state) := by
  induction computation using OracleComp.inductionOn with
  | pure value =>
    intro accumulated log state
    simp only [simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind queried next ih =>
    intro accumulated log state
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind,
      simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
      ← run_fuseServing_step_conj π outer outer' inner before after before' after' hbefore
        hafter hforget queried accumulated log state,
      bind_map_left]
    refine bind_congr fun step => ?_
    exact ih step.1 step.2.1 step.2.2.1 step.2.2.2

/-- **The transport in bind form**, so that three stages chain by `bind_congr` rather than by a
rewrite that has to match on both sides. -/
theorem bind_of_forgetsAlong {β γ : Type} (π : S → S')
    (outer : QueryImpl OracleWorld (StateT S ProbComp))
    (outer' : QueryImpl OracleWorld (StateT S' ProbComp))
    (hforget : ForgetsAlong π outer outer')
    (computation : OracleComp OracleWorld β) (state : S)
    (continuation : β × S' → ProbComp γ) :
    (simulateQ outer computation).run state >>= (fun z => continuation (z.1, π z.2)) =
      (simulateQ outer' computation).run (π state) >>= continuation := by
  rw [← hforget computation state, map_eq_bind_pure_comp, bind_assoc]
  simp only [pure_bind, Function.comp_def]

/-- **And the fused stage in bind form.** -/
theorem bind_of_fuseServing_conj {α γ : Type} (π : S → S')
    (outer : QueryImpl OracleWorld (StateT S ProbComp))
    (outer' : QueryImpl OracleWorld (StateT S' ProbComp))
    (inner : QueryImpl (OracleWorld + SigningSpec)
      (WriterT ω (StateT SigningLog (OracleComp OracleWorld))))
    (before : Message → S → S) (after : S → S)
    (before' : Message → S' → S') (after' : S' → S')
    (hbefore : ∀ (request : Message) (state : S),
      π (before request state) = before' request (π state))
    (hafter : ∀ state : S, π (after state) = after' (π state))
    (hforget : ForgetsAlong π outer outer')
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (accumulated : ω) (log : SigningLog) (state : S)
    (continuation : α × (ω × SigningLog × S') → ProbComp γ) :
    (simulateQ (fuseServing outer inner before after) computation).run
          (accumulated, log, state) >>=
        (fun z => continuation (z.1, (z.2.1, z.2.2.1, π z.2.2.2))) =
      (simulateQ (fuseServing outer' inner before' after') computation).run
        (accumulated, log, π state) >>= continuation := by
  rw [← run_fuseServing_conj π outer outer' inner before after before' after' hbefore hafter
      hforget computation accumulated log state, map_eq_bind_pure_comp, bind_assoc]
  simp only [pure_bind, Function.comp_def]

end SlhDsaSecurity.ServingForget
