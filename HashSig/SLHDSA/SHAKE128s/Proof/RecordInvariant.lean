/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.BracketedRun

/-!
# What a bracketed run keeps true of its recordings

`ServedAgreement.Files` is the interface a bracketed run is read through for the **carrier** —
the cache, the framing and the served set — and it keeps `τ`, where the two recordings live,
opaque. That opacity is the property that let it transport through the counter, so it is not a
gap to be filled in place: the recordings want their own interface, in the same shape.

This is that shape, and it is smaller, because everything the recordings need is of one form:
**a property of the state that every step preserves is preserved by a run, and by a bracketed
phase if the brackets preserve it too.** `BracketedRun.Bracket` already says the brackets touch
neither the cache nor either recording, so for any invariant reading only those two the bracket
condition is discharged rather than assumed.

Nothing here knows what a recording is. `right_record_nodup` and `messageClass_of_record` become
instances by supplying one step fact each, which is the only place the recorder's own shape
enters.

**Nor does anything here know what a state is.** The five laws below are state-machine
arguments and are stated at an arbitrary `S`; only `bracket_invariant`, which reads
`BracketedRun.Bracket`, stays at `CountedState`. That matters because the split-counted tail
carries a `Counts` where the counted one carries a `Nat`, and an invariant interface that could
not follow it there would have to be written twice.
-/

@[expose] public section

open OracleComp OracleSpec

namespace SlhDsaSecurity.RecordInvariant

variable {α : Type}

open Security BracketedRun PhaseFusion

variable {ω : Type} [Monoid ω] {S : Type}

/-- **A property every step preserves is preserved by a run.** -/
theorem run_invariant {Inv : S → Prop}
    (handler : QueryImpl OracleWorld (StateT S ProbComp))
    (hstep : ∀ (queried : OracleWorld.Domain) (state : S)
      (step : OracleWorld.Range queried × S),
      step ∈ support ((handler queried).run state) → Inv state → Inv step.2)
    {α : Type} (computation : OracleComp OracleWorld α) :
    ∀ (state : S) (result : α × S),
      result ∈ support ((simulateQ handler computation).run state) → Inv state →
        Inv result.2 := by
  induction computation using OracleComp.inductionOn with
  | pure value =>
    intro state result hmem hinv
    rw [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
    rw [hmem]
    exact hinv
  | query_bind queried next ih =>
    intro state result hmem hinv
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hmem
    obtain ⟨step, hs, hrest⟩ := hmem
    exact ih step.1 step.2 result hrest (hstep queried state step hs hinv)

/-- **And by a bracketed phase**, given that the brackets preserve it. -/
theorem phase_invariant {Inv : S → Prop}
    (handler : QueryImpl OracleWorld (StateT S ProbComp))
    (inner : QueryImpl (OracleWorld + SigningSpec)
      (WriterT ω (StateT SigningLog (OracleComp OracleWorld))))
    (before : Message → S → S) (after : S → S)
    (hstep : ∀ (queried : OracleWorld.Domain) (state : S)
      (step : OracleWorld.Range queried × S),
      step ∈ support ((handler queried).run state) → Inv state → Inv step.2)
    (hbefore : ∀ (request : Message) (state : S), Inv state → Inv (before request state))
    (hafter : ∀ state : S, Inv state → Inv (after state))
    {α : Type} (computation : OracleComp (OracleWorld + SigningSpec) α) :
    ∀ (accumulated : ω) (log : SigningLog) (carrier : S)
      (result : α × (ω × SigningLog × S)),
      result ∈ support ((simulateQ (fuseServing handler inner before after) computation).run
        (accumulated, log, carrier)) → Inv carrier → Inv result.2.2.2 := by
  induction computation using OracleComp.inductionOn with
  | pure value =>
    intro accumulated log carrier result hmem hinv
    rw [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
    rw [show result.2.2.2 = carrier from by rw [hmem]]
    exact hinv
  | query_bind queried next ih =>
    intro accumulated log carrier result hmem hinv
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hmem
    obtain ⟨step, hs, hrest⟩ := hmem
    refine ih step.1 step.2.1 step.2.2.1 step.2.2.2 result hrest ?_
    rcases queried with world | request
    · have hs' : step ∈ support
          ((simulateQ handler (((inner (Sum.inl world)).run).run log)).run carrier >>= fun z =>
            (pure (z.1.1.1, (accumulated * z.1.1.2, z.1.2, z.2)) :
              ProbComp ((OracleWorld + SigningSpec).Range (Sum.inl world) ×
                (ω × SigningLog × S)))) := hs
      obtain ⟨z, hz, hpure⟩ := support_bind_exists hs'
      rw [show step.2.2.2 = z.2 from congrArg (fun p => p.2.2.2) hpure]
      exact run_invariant handler hstep _ carrier z hz hinv
    · have hs' : step ∈ support
          ((simulateQ handler (((inner (Sum.inr request)).run).run log)).run
              (before request carrier) >>= fun z =>
            (pure (z.1.1.1, (accumulated * z.1.1.2, z.1.2, after z.2)) :
              ProbComp ((OracleWorld + SigningSpec).Range (Sum.inr request) ×
                (ω × SigningLog × S)))) := hs
      obtain ⟨z, hz, hpure⟩ := support_bind_exists hs'
      rw [show step.2.2.2 = after z.2 from congrArg (fun p => p.2.2.2) hpure]
      exact hafter z.2
        (run_invariant handler hstep _ (before request carrier) z hz
          (hbefore request carrier hinv))

/-! ## An invariant the opening bracket breaks and the closing one restores

`phase_invariant` asks the brackets to preserve the invariant, which is right for anything
reading the cache or the recordings and wrong for anything reading the **framing**: the opening
bracket's whole job is to write it. Such an invariant is not preserved inside a signing sub-run
and there is no weaker statement that is — the sub-run genuinely has a request in flight.

What is true is that the closing bracket restores it regardless of what it is given, because it
writes rather than tests. So the law to ask for is `hafter` unconditional, and then the signing
branch needs nothing about the sub-run at all: the invariant holds at every state the phase
itself is at, and the region where it fails is exactly one signing sub-run. -/

/-- **An invariant restored by the closing bracket survives the phase**, with no condition on
what the opening bracket or the sub-run did. -/
theorem phase_invariant_of_after {Inv : S → Prop}
    (handler : QueryImpl OracleWorld (StateT S ProbComp))
    (inner : QueryImpl (OracleWorld + SigningSpec)
      (WriterT ω (StateT SigningLog (OracleComp OracleWorld))))
    (before : Message → S → S) (after : S → S)
    (hstep : ∀ (queried : OracleWorld.Domain) (state : S)
      (step : OracleWorld.Range queried × S),
      step ∈ support ((handler queried).run state) → Inv state → Inv step.2)
    (hafter : ∀ state : S, Inv (after state))
    {α : Type} (computation : OracleComp (OracleWorld + SigningSpec) α) :
    ∀ (accumulated : ω) (log : SigningLog) (carrier : S)
      (result : α × (ω × SigningLog × S)),
      result ∈ support ((simulateQ (fuseServing handler inner before after) computation).run
        (accumulated, log, carrier)) → Inv carrier → Inv result.2.2.2 := by
  induction computation using OracleComp.inductionOn with
  | pure value =>
    intro accumulated log carrier result hmem hinv
    rw [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
    rw [show result.2.2.2 = carrier from by rw [hmem]]
    exact hinv
  | query_bind queried next ih =>
    intro accumulated log carrier result hmem hinv
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hmem
    obtain ⟨step, hs, hrest⟩ := hmem
    refine ih step.1 step.2.1 step.2.2.1 step.2.2.2 result hrest ?_
    rcases queried with world | request
    · have hs' : step ∈ support
          ((simulateQ handler (((inner (Sum.inl world)).run).run log)).run carrier >>= fun z =>
            (pure (z.1.1.1, (accumulated * z.1.1.2, z.1.2, z.2)) :
              ProbComp ((OracleWorld + SigningSpec).Range (Sum.inl world) ×
                (ω × SigningLog × S)))) := hs
      obtain ⟨z, hz, hpure⟩ := support_bind_exists hs'
      rw [show step.2.2.2 = z.2 from congrArg (fun p => p.2.2.2) hpure]
      exact run_invariant handler hstep _ carrier z hz hinv
    · have hs' : step ∈ support
          ((simulateQ handler (((inner (Sum.inr request)).run).run log)).run
              (before request carrier) >>= fun z =>
            (pure (z.1.1.1, (accumulated * z.1.1.2, z.1.2, after z.2)) :
              ProbComp ((OracleWorld + SigningSpec).Range (Sum.inr request) ×
                (ω × SigningLog × S)))) := hs
      obtain ⟨z, -, hpure⟩ := support_bind_exists hs'
      rw [show step.2.2.2 = after z.2 from congrArg (fun p => p.2.2.2) hpure]
      exact hafter z.2

/-! ## What the writer accumulates

A phase threads its writer through the state, so a fact about the record a step wrote is a fact
about a *factor* of the final accumulator rather than a summand of a returned value. These two
say that the accumulator only ever gains factors, which is what lets a step's own record be
found in the phase's. -/

/-! ## The bracket condition, discharged rather than assumed

An invariant that reads only the cache and the two recordings is preserved by any `Bracket`,
because that is exactly what a bracket is defined to leave alone. -/

end SlhDsaSecurity.RecordInvariant
