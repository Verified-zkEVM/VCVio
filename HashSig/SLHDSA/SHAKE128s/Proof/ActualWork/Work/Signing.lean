/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.ActualWork.Work.Verification
public import HashSig.SLHDSA.SHAKE128s.Proof.ActualWork.Work.HashQuery
public import HashSig.SLHDSA.SHAKE128s.Proof.ActualWork.Coverage.Keygen
public import HashSig.SLHDSA.Security.LabBudget
import all HashSig.SLHDSA.SHAKE128s.Proof.ActualWork.Coverage.Keygen
import all HashSig.SLHDSA.SHAKE128s.Proof.ActualWork.Work.Verification
import all HashSig.SLHDSA.Security.NativeCounts

/-! # Joint work accounting for a signing client that can reject requests -/

public section

namespace SLHDSA.SHAKE128s.Bridge.SharedExperiment.SigningCounts
open OracleComp OracleSpec SignatureAlg
open SLHDSA SLHDSA.Security SLHDSA.SHAKE128s
open Guarded VerificationOffsets

private abbrev State :=
  (CoverageDeferred.S FIPS205.core × Coverage.RoleState FIPS205.core) × Paid
private abbrev flatten (before : World) : State :=
  ((before.2.2.1, before.2.2.2), before.1)
private abbrev pack {α : Type} (raw : Raw.QueryCache) (small : α × State) : Result α :=
  ((((small.1, (PUnit.unit, small.2.2)), raw), small.2.1.1), small.2.1.2)

private def embed : QueryImpl (Lab + O) (OracleComp LabCommon)
  | .inl query => liftM (LabCommon.query (.inl (.inl query)))
  | .inr event => liftM (LabCommon.query (.inr event))

private def smallFallback (fallback : (i : LabCommon.Domain) → LabCommon.Range i) :
    (i : (Lab + O).Domain) → (Lab + O).Range i
  | .inl query => fallback (.inl (.inl query))
  | .inr event => fallback (.inr event)

private noncomputable abbrev smallHandler (s : FIPS205.core.PkSeed) (caps : Nat × Nat)
    (fallback : (i : LabCommon.Domain) → LabCommon.Range i) :=
  NativeCounts.guardedImpl FIPS205.core s caps (policy true s) (metadataCost true s)
    (smallFallback fallback)

private theorem native_query (s : FIPS205.core.PkSeed) (caps : Nat × Nat)
    (fallback : (i : LabCommon.Domain) → LabCommon.Range i) (i : (Lab + O).Domain)
    (before : World) :
    execute s caps fallback (embed i) before =
      pack before.2.1 <$> (smallHandler s caps fallback i).run (flatten before) := by
  classical
  rcases before with ⟨paid, raw, state, role⟩
  have link (x : (Lab + O).Domain) :
      ((NativeCounts.nativeImpl FIPS205.core s (metadataCost true s) x).run (state, role)) =
      (fun z => (z.1.1, (z.1.2, z.2))) <$>
        (simulateQ (Coverage.roleRunImpl FIPS205.core)
          ((CoverageDeferred.relative FIPS205.core s (metadataCost true s) x).run state)).run
            role := rfl
  cases i with
  | inl query =>
    by_cases h : paid.1 + (0, 0) ≤ caps <;> cases aborted : paid.2 <;>
      simp [embed, execute, smallHandler, NativeCounts.guardedImpl, flatten,
        QueryImpl.guardQueryBudget,
        aborted, h, routeLab, QueryImpl.add, QueryImpl.id', QueryImpl.liftTarget, link,
        StateT.run_map, Functor.map_map, pack, smallFallback]
  | inr event =>
    by_cases h : paid.1 + policy true s event ≤ caps <;> cases aborted : paid.2 <;>
      simp [embed, execute, smallHandler, NativeCounts.guardedImpl, flatten,
        QueryImpl.guardQueryBudget,
        aborted, h, routeLab, QueryImpl.add, QueryImpl.id', QueryImpl.liftTarget, link,
        StateT.run_map, Functor.map_map, pack, smallFallback]

/-- Native-only programs use the guarded native handler and preserve the raw table. -/
private theorem native_program {α : Type} (s : FIPS205.core.PkSeed) (caps : Nat × Nat)
    (fallback : (i : LabCommon.Domain) → LabCommon.Range i)
    (program : OracleComp (Lab + O) α) (before : World) :
    execute s caps fallback (simulateQ embed program) before =
      pack before.2.1 <$> (simulateQ (smallHandler s caps fallback) program).run
        (flatten before) := by
  induction program using OracleComp.inductionOn generalizing before with
  | pure x => simp [execute, pack]
  | query_bind input next ih =>
    rw [simulateQ_bind, VerificationOffsets.execute_bind, simulateQ_spec_query,
      native_query, bind_map_left]
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind]
    apply bind_congr
    intro p
    exact ih p.1 (world (pack before.2.1 p))

private def observe : Lab.Domain → Option R.Domain
  | .inl (.inl native) => some (sourceInput native)
  | _ => none

private noncomputable abbrev body (s : FIPS205.core.PkSeed) (pk sk : PK) (request : Message) :=
  (partialView true s).sign pk sk request

private noncomputable abbrev smallCallback (s : FIPS205.core.PkSeed)
    (pk sk : PK) (request : Message) : OracleComp (Lab + O) (Option (List Byte)) := do
  let _ ← (liftM ((Lab + O).query (.inr (.signingAttempt request))) : OracleComp (Lab + O) PUnit)
  simulateQ (NativeCounts.phaseObservation FIPS205.core observe .signer) (body s pk sk request)

/-- The marked signing callback on an external request, including its signing-attempt event. -/
noncomputable abbrev signSource (s : FIPS205.core.PkSeed) (pk sk : PK) (request : Message) :=
  simulateQ commonProjection ((SigningView.Events.viewWithEvents (commonView true s)).sign
    pk sk request)

private theorem callback_eq (s : FIPS205.core.PkSeed) (pk sk : PK) (request : Message) :
    signSource s pk sk request = simulateQ embed (smallCallback s pk sk request) := by
  simp only [signSource, smallCallback, SigningView.Events.viewWithEvents, SigningView.Events.emit,
    simulateQ_bind, simulateQ_spec_query, commonView, SigningView.map_sign,
    ← QueryImpl.simulateQ_compose, body]
  apply bind_congr
  intro _
  congr 1
  funext input
  rcases input with ((native | derivation) | label) <;>
    simp [QueryImpl.apply_compose, NativeCounts.phaseObservation, observe, embed,
      commonProjection, commonEvent, SigningView.Events.phaseImpl, SigningView.Events.emit,
      QueryImpl.add]

private theorem body_bound (s : FIPS205.core.PkSeed) (pk sk : PK) (request : Message) :
    IsQueryBoundP (body s pk sk request) (NativeCounts.IsLabHmsg FIPS205.core) 1 := by
  cases framing : (External.encodePureMessage request.context request.message).toOption with
  | none => simp [body, partialView, SigningView.rejectingEncoding_sign, framing]
  | some message =>
    have count := isQueryBoundP_labScheme_sign_of_hmsg
      (core := FIPS205.core) (q := NativeCounts.IsLabHmsg FIPS205.core) (n := 1)
      s (fun pk => pure pk.pkSeed)
      (by
        rintro (((sample | point) | derive) | (touch | node)) hi <;>
          simp_all only [NativeCounts.IsLabHmsg, Coverage.IsHmsgQuery, IsPublicLabQuery])
      pk sk message (fun randomness => by
        change IsQueryBoundP
          (liftM ((labSpec FIPS205.core).query
            (.inl (.inl (.inr (.inl (.hmsg randomness s sk.pkRoot message)))))))
          (NativeCounts.IsLabHmsg FIPS205.core) 1
        exact (isQueryBoundP_query_iff _ _ _).2 (fun _ => Nat.zero_lt_one))
    simpa only [body, partialView, ite_true, SigningView.rejectingEncoding_sign, framing,
      isQueryBoundP_map_iff] using count

private theorem observed_hmsg (t : Lab.Domain) (h : NativeCounts.IsLabHmsg FIPS205.core t) :
    ∃ label, observe t = some label := by
  rcases t with ((native | derive) | labels)
  · exact ⟨_, rfl⟩
  · exact h.elim
  · exact h.elim

private theorem observed_second (s : FIPS205.core.PkSeed) (phase : SigningView.Phase)
    (input : Lab.Domain) (label : R.Domain) (_ : observe input = some label) :
    (policy true s (.ambient phase label)).2 = 0 := by
  cases phase <;> simp [policy, originalPolicy, Game.Counted.sourcePolicy, Game.Counted.sourceKind]

private theorem observed_paid (s : FIPS205.core.PkSeed) (phase : SigningView.Phase)
    (input : Lab.Domain) (label : R.Domain) (matchLabel : observe input = some label)
    (hmsg : NativeCounts.IsLabHmsg FIPS205.core input)
    (hp : NativeCounts.phaseClass phase = .forger) :
    1 ≤ (policy true s (.ambient phase label)).1 := by
  rcases input with (((sample | ((thash | hmsgPoint) | nonce)) | derive) | labels) <;>
    try exact hmsg.elim
  cases matchLabel
  cases phase <;> simp_all [policy, originalPolicy, NativeCounts.phaseClass,
    Game.Counted.sourcePolicy,
    Game.Counted.sourceKind, Game.hashCost, RandomOracleModel.hashCost, sourceInput]

/-- The paid budget covers the role counts. For a nonweak key, observed hash work also
covers the forger count. -/
abbrev Invariant (nonweak : Prop) (state : World) : Prop :=
  NativeCounts.CountInvariant FIPS205.core ((state.2.2.1, state.2.2.2), state.1) ∧
    (nonweak → state.2.2.2.2.1.cnt .forger ≤ state.2.2.1.2.1)

private theorem invariant_of_offsets {p : Prop} {before after : World}
    (earlier : Invariant p before) (step : offsets p before after) : Invariant p after := by
  obtain ⟨⟨c,z⟩, m⟩ := earlier
  obtain ⟨hs, hc, hz, hm⟩ := step
  change before.2.2.2.2.1.cnt .signer ≤ before.1.1.2 at c
  change before.1.1.2 + before.2.2.2.2.1.cnt .forger ≤ before.1.1.1 at z
  refine ⟨⟨hc.trans (c.trans_eq hs.symm), ?_⟩, ?_⟩
  · change after.1.1.2 + after.2.2.2.2.1.cnt .forger ≤ after.1.1.1
    omega
  · intro h
    have := m h
    have := hm h
    omega

/-- The attempt is charged before framing. A denied attempt freezes all native state. -/
theorem marked_signing_counts (s : FIPS205.core.PkSeed) (pk sk : PK) (request : Message)
    (caps : Nat × Nat) (fallback : (i : LabCommon.Domain) → LabCommon.Range i)
    (p : Prop) (before : World) (prior : Invariant p before)
    (out : Result (Option (List Byte)))
    (member : out ∈ support (execute s caps fallback (signSource s pk sk request) before)) :
    let admitted := before.1.2 = false ∧ before.1.1 + (32, 1) ≤ caps
    Invariant p (world out) ∧
      out.1.1.1.2.2.1.2 = before.1.1.2 + (if admitted then 1 else 0) ∧
      (¬admitted → world out = ((before.1.1, true), before.2)) := by
  classical
  rw [callback_eq, native_program, support_map] at member
  obtain ⟨small, hs, rfl⟩ := member
  have attempt : policy true s (.signingAttempt request) = (32, 1) := by
    simp [policy, originalPolicy, reserveExtra, Game.Counted.sourcePolicy]
  have unit : 1 ≤ (policy true s (.signingAttempt request)).1 ∧
      (policy true s (.signingAttempt request)).2 = 1 := by rw [attempt]; decide
  have funded := NativeCounts.signing_callback FIPS205.core observe (policy true s)
    (metadataCost true s) observed_hmsg (observed_second s) (observed_paid s)
    s caps (smallFallback fallback) request unit rfl (fun _ => rfl) (body s pk sk request)
    (body_bound s pk sk request) (flatten before) prior.1 small hs
  have entryRun := hs
  simp only [smallCallback, simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
    mem_support_bind_iff] at entryRun
  obtain ⟨entry, he, hb⟩ := entryRun
  have entryFacts := NativeCounts.signing_entry FIPS205.core (policy true s) (metadataCost true s)
    s caps (smallFallback fallback) request unit (flatten before) prior.1 entry he
  have initialMeta : entry.2.1.1.2.1 = before.2.2.1.2.1 ∧ entry.2.1.2 = before.2.2.2 := by
    cases aborted : before.1.2 with
    | true => rw [entryFacts.2.1 aborted]; exact ⟨rfl, rfl⟩
    | false =>
      by_cases fits : before.1.1 + policy true s (.signingAttempt request) ≤ caps
      · rw [entryFacts.2.2.1 ⟨aborted, fits⟩]
        exact ⟨Nat.add_zero _, rfl⟩
      · rw [entryFacts.2.2.2 ⟨aborted, fits⟩]
        exact ⟨rfl, rfl⟩
  have phase := NativeCounts.phase_offsets FIPS205.core observe (policy true s)
    (metadataCost true s)
    observed_hmsg (observed_second s) (observed_paid s) s caps (smallFallback fallback) .signer
    (fun _ => True) (body s pk sk request) (allQueriesSatisfy_of_forall (fun _ => trivial) _)
    entry.2 small hb
  have metadata := phase.1.2.2.2 (fun _ _ _ _ _ h => by cases h)
  refine ⟨⟨funded.1, ?_⟩, ?_, ?_⟩
  · intro nw
    have old := prior.2 nw
    rw [initialMeta.1, initialMeta.2] at metadata
    change small.2.1.2.2.1.cnt .forger ≤ small.2.1.1.2.1
    omega
  · simpa only [attempt, flatten] using funded.2.2.1
  · intro denied
    have frozen := funded.2.2.2.2 (by simpa only [attempt, flatten] using denied)
    change (small.2.2, before.2.1, small.2.1.1, small.2.1.2) = _
    rw [frozen]

private abbrev Safe {α : Type} (s : FIPS205.core.PkSeed) (caps : Nat × Nat)
    (fallback : (i : LabCommon.Domain) → LabCommon.Range i) (p : Prop)
    (action : OracleComp LabCommon α) : Prop :=
  ∀ before, Invariant p before → ∀ out ∈ support (execute s caps fallback action before),
    Invariant p (world out)

private theorem safe_pure {α : Type} (s : FIPS205.core.PkSeed) (caps : Nat × Nat)
    (fallback : (i : LabCommon.Domain) → LabCommon.Range i) (p : Prop) (x : α) :
    Safe s caps fallback p (pure x) := by
  intro before prior out mem
  simp only [execute, simulateQ_pure, StateT.run_pure, support_pure,
    Set.mem_singleton_iff] at mem
  subst out
  exact prior

private theorem safe_bind {α β : Type} {s : FIPS205.core.PkSeed} {caps : Nat × Nat}
    {fallback : (i : LabCommon.Domain) → LabCommon.Range i} {p : Prop}
    {action : OracleComp LabCommon α} {rest : α → OracleComp LabCommon β}
    (first : Safe s caps fallback p action) (next : ∀ x, Safe s caps fallback p (rest x)) :
    Safe s caps fallback p (action >>= rest) := by
  intro before prior out mem
  rw [VerificationOffsets.execute_bind, mem_support_bind_iff] at mem
  obtain ⟨mid, hm, hout⟩ := mem
  exact next _ _ (first before prior mid hm) out hout

private noncomputable def clientAmbient : QueryImpl R (OracleComp LabCommon)
  | .inl n => simulateQ commonProjection
      (SigningView.Events.phaseImpl A Message .adversary (.inl (.inl (.inl (.inl n)))))
  | .inr raw => simulateQ commonProjection
      (SigningView.Events.phaseImpl A Message .adversary (.inr raw))

private theorem uniform_safe (s : FIPS205.core.PkSeed) (caps : Nat × Nat)
    (fallback : (i : LabCommon.Domain) → LabCommon.Range i) (p : Prop) (n : unifSpec.Domain) :
    Safe s caps fallback p (clientAmbient (.inl n)) := by
  let input : Lab.Domain := .inl (.inl (.inl n))
  let prog := (liftM (Lab.query input) : OracleComp Lab (unifSpec.Range n))
  have eqn : clientAmbient (.inl n) = simulateQ embed
      (simulateQ (NativeCounts.phaseObservation FIPS205.core observe .adversary) prog) := by
    simp [clientAmbient, prog, input, NativeCounts.phaseObservation,
      SigningView.Events.phaseImpl, SigningView.Events.emit,
      commonProjection, commonEvent, observe, sourceInput, embed, QueryImpl.add]
  intro before prior out mem
  rw [eqn, native_program, support_map] at mem
  obtain ⟨small, hs, rfl⟩ := mem
  have good : prog.AllQueriesSatisfy (fun t => t = input) :=
    (allQueriesSatisfy_query_iff _ _).2 rfl
  have phase := (NativeCounts.phase_offsets FIPS205.core observe (policy true s)
    (metadataCost true s) observed_hmsg (observed_second s) (observed_paid s) s caps
    (smallFallback fallback) .adversary _ prog good (flatten before) small hs).1
  exact invariant_of_offsets prior
    ⟨phase.1, phase.2.1 (by decide), phase.2.2.1,
      fun _ => phase.2.2.2 (fun t ht _ _ hh _ => (ht ▸ hh).elim)⟩

private noncomputable abbrev clientHandler (s : FIPS205.core.PkSeed) (pk sk : PK) :
    QueryImpl (R + Sign) (WriterT (QueryLog Sign) (OracleComp LabCommon)) :=
  QueryImpl.add (clientAmbient.liftTarget (WriterT (QueryLog Sign) (OracleComp LabCommon)))
    (QueryImpl.withLogging (spec := Sign) (signSource s pk sk))

private theorem logged_safe {α : Type} (s : FIPS205.core.PkSeed) (pk sk : PK)
    (caps : Nat × Nat) (fallback : (i : LabCommon.Domain) → LabCommon.Range i)
    (p : Prop) (program : OracleComp (R + Sign) α) :
    Safe s caps fallback p (simulateQ (clientHandler s pk sk) program).run := by
  induction program using OracleComp.inductionOn with
  | pure x => exact safe_pure _ _ _ _ _
  | query_bind input next ih =>
    rw [simulateQ_bind, simulateQ_spec_query, WriterT.run_bind]
    apply safe_bind
    · rcases input with (n | raw) | request
      · change Safe _ _ _ _ ((fun reply => (reply, (∅ : QueryLog Sign))) <$>
          clientAmbient (.inl n))
        rw [map_eq_bind_pure_comp]
        exact safe_bind (uniform_safe _ _ _ _ _) (fun _ => safe_pure _ _ _ _ _)
      · change Safe _ _ _ _ ((fun reply => (reply, (∅ : QueryLog Sign))) <$>
          clientAmbient (.inr raw))
        rw [map_eq_bind_pure_comp]
        apply safe_bind _ (fun _ => safe_pure _ _ _ _ _)
        intro before prior out mem
        have rawStep := marked_raw_count_offsets s .adversary raw (Or.inl rfl) caps fallback
          before.1 before.2.1 before.2.2.1 before.2.2.2 out mem
        exact invariant_of_offsets prior
          ⟨rawStep.1, rawStep.2.1, rawStep.2.2.2, fun _ => rawStep.2.2.1⟩
      · change Safe _ _ _ _ ((QueryImpl.withLogging (spec := Sign) (signSource s pk sk))
          request).run
        rw [QueryImpl.run_withLogging_apply]
        exact safe_bind (fun before prior out mem =>
          (marked_signing_counts s pk sk request caps fallback p before prior out mem).1)
          (fun _ => safe_pure _ _ _ _ _)
    · rintro ⟨answer, left⟩
      dsimp only
      rw [map_eq_bind_pure_comp]
      exact safe_bind (ih answer) (fun _ => safe_pure _ _ _ _ _)

private theorem actual_client_eq (s : FIPS205.core.PkSeed) (pk sk : PK)
    (adv : Game.Adversary FIPS205.Answer PK) :
    let marked := SigningView.Events.viewWithEvents (commonView true s)
    simulateQ commonProjection (marked.runWithSigningOracle pk sk
      (SigningView.Events.mainWithEvents (commonMain adv) pk)) =
      (simulateQ (clientHandler s pk sk) (Game.Counted.externalMain adv pk)).run := by
  let marked := SigningView.Events.viewWithEvents (commonView true s)
  let Log := QueryLog Sign
  let mainLift : QueryImpl (R + Sign) (OracleComp (A + Sign)) :=
    QueryImpl.add
      (QueryImpl.add
        (QueryImpl.ofLift unifSpec (OracleComp (A + Sign)))
        (fun raw => liftM ((A + Sign).query (.inl (.inr raw)))))
      (fun request => liftM ((A + Sign).query (.inr request)))
  let phaseMain : QueryImpl (A + Sign)
      (OracleComp (SigningView.Events.Spec A Message + Sign)) :=
    SigningView.mapClient (SigningView.Events.phaseImpl A Message .adversary)
  let service : QueryImpl (SigningView.Events.Spec A Message + Sign)
      (WriterT Log (OracleComp (SigningView.Events.Spec A Message))) :=
    QueryImpl.add
      ((QueryImpl.id' (SigningView.Events.Spec A Message)).liftTarget
        (WriterT Log (OracleComp (SigningView.Events.Spec A Message))))
      (marked.signingOracle pk sk)
  have mainUniform (sample : unifSpec.Domain) :
      mainLift (.inl (.inl sample)) =
        (liftM ((A + Sign).query (.inl (.inl (.inl (.inl (.inl sample)))))) :
          OracleComp (A + Sign) (unifSpec.Range sample)) := rfl
  have mainRaw (raw : Raw.Domain) : mainLift (.inl (.inr raw)) =
      (liftM ((A + Sign).query (.inl (.inr raw))) : OracleComp (A + Sign) (Raw.Range raw)) := rfl
  have mainSign (request : Sign.Domain) : mainLift (.inr request) =
      (liftM ((A + Sign).query (.inr request)) : OracleComp (A + Sign) (Sign.Range request)) := rfl
  have phaseAmbient (input : A.Domain) : phaseMain (.inl input) =
      simulateQ (fun event : (SigningView.Events.Spec A Message).Domain =>
        (liftM ((SigningView.Events.Spec A Message + Sign).query (.inl event)) :
          OracleComp (SigningView.Events.Spec A Message + Sign)
            ((SigningView.Events.Spec A Message).Range event)))
          (SigningView.Events.phaseImpl A Message .adversary input) := rfl
  have phaseSign (request : Sign.Domain) : phaseMain (.inr request) =
      (liftM ((SigningView.Events.Spec A Message + Sign).query (.inr request)) :
        OracleComp (SigningView.Events.Spec A Message + Sign) (Sign.Range request)) := rfl
  have serviceSign (request : Sign.Domain) :
      service (.inr request) = marked.signingOracle pk sk request := rfl
  have markedLog (request : Sign.Domain) :
      ((marked.signingOracle pk sk) request).run = (do
        let reply ← marked.sign pk sk request
        pure (reply, [⟨request, reply⟩])) :=
    QueryImpl.run_withLogging_apply (loggedSpec := Sign) (marked.sign pk sk) request
  have serviceAmbient {alpha : Type}
      (program : OracleComp (SigningView.Events.Spec A Message) alpha) :
      (simulateQ service
        (simulateQ (fun input : (SigningView.Events.Spec A Message).Domain =>
          (liftM ((SigningView.Events.Spec A Message + Sign).query (.inl input)) :
            OracleComp (SigningView.Events.Spec A Message + Sign)
              ((SigningView.Events.Spec A Message).Range input))) program)).run =
        (fun answer => (answer, (∅ : Log))) <$> program := by
    have same : simulateQ service
        (simulateQ (fun input : (SigningView.Events.Spec A Message).Domain =>
          (liftM ((SigningView.Events.Spec A Message + Sign).query (.inl input)) :
            OracleComp (SigningView.Events.Spec A Message + Sign)
              ((SigningView.Events.Spec A Message).Range input))) program) =
        simulateQ ((QueryImpl.id' (SigningView.Events.Spec A Message)).liftTarget
          (WriterT Log (OracleComp (SigningView.Events.Spec A Message)))) program := by
      apply QueryImpl.simulateQ_simulateQ_eq_of_apply
      intro input
      simp only [simulateQ_spec_query, service, QueryImpl.add]
    rw [same, writerT_run_simulateQ_liftTarget, simulateQ_id']
  have clientEquation :
      simulateQ commonProjection (marked.runWithSigningOracle pk sk
        (SigningView.Events.mainWithEvents (commonMain adv) pk)) =
      (simulateQ (clientHandler s pk sk) (Game.Counted.externalMain adv pk)).run := by
    have mainEquation : SigningView.Events.mainWithEvents (commonMain adv) pk =
        simulateQ phaseMain (simulateQ mainLift (Game.Counted.externalMain adv pk)) := by
      rfl
    rw [SigningView.runWithSigningOracle, mainEquation]
    simp only [QueryImpl.passthrough_add, ← QueryImpl.add_eq_hAdd]
    rw [← QueryImpl.simulateQ_compose, ← QueryImpl.simulateQ_compose]
    change simulateQ commonProjection
      (simulateQ (service ∘ₛ phaseMain ∘ₛ mainLift)
        (Game.Counted.externalMain adv pk)).run = _
    apply simulateQ_WriterT_compose (service ∘ₛ phaseMain ∘ₛ mainLift)
      commonProjection (clientHandler s pk sk)
    intro input
    rcases input with (sample | raw) | request
    all_goals
      simp [QueryImpl.apply_compose, mainUniform, mainRaw, mainSign,
        phaseAmbient, phaseSign, serviceAmbient, serviceSign,
        clientHandler, QueryImpl.add,
        markedLog, simulateQ_map,
        clientAmbient, signSource, marked]
    all_goals rfl
  exact clientEquation

private theorem suffix_safe (s : FIPS205.core.PkSeed) (root : FIPS205.core.Y) (sk : PK)
    (adv : Game.Adversary FIPS205.Answer PK) (caps : Nat × Nat)
    (fallback : (i : LabCommon.Domain) → LabCommon.Range i) :
    Safe s caps fallback (¬IsWeakKey FIPS205.params (⟨s, root⟩ : PK))
      (SLHDSA.SHAKE128s.MarkedPrefix.suffixSource s adv ⟨s, root⟩ sk) := by
  let pk : PK := ⟨s, root⟩
  let marked := SigningView.Events.viewWithEvents (commonView true s)
  have client := logged_safe s pk sk caps fallback (¬IsWeakKey FIPS205.params pk)
    (Game.Counted.externalMain adv pk)
  rw [← actual_client_eq] at client
  simp only [SLHDSA.SHAKE128s.MarkedPrefix.suffixSource, simulateQ_bind, simulateQ_pure]
  apply safe_bind client
  rintro ⟨forgery, log⟩
  apply safe_bind _ (fun _ => safe_pure _ _ _ _ _)
  intro before prior out mem
  exact invariant_of_offsets prior
    (marked_verify_count_offsets s root forgery.1 forgery.2 caps fallback before out mem)

private theorem source_support {ι κ σ α : Type} {spec : OracleSpec.{0, 0} ι}
    {target : OracleSpec.{0, 0} κ}
    (impl : QueryImpl spec (StateT σ (OracleComp target))) (program : OracleComp spec α)
    (state : σ) (z : α × σ) (member : z ∈ support ((simulateQ impl program).run state)) :
    z.1 ∈ support program := by
  apply support_simulateQ_run'_subset impl program state
  rw [StateT.run'_eq, support_map]
  exact ⟨z, member, rfl⟩

private theorem prefix_paid_seed (s : FIPS205.core.PkSeed) (caps : Nat × Nat)
    (fallback : (i : LabCommon.Domain) → LabCommon.Range i) (rel : CoverageDeferred.S FIPS205.core)
    (role : Coverage.RoleState FIPS205.core) (out : Result (PK × PK))
    (member : out ∈ support (execute s caps fallback (SLHDSA.SHAKE128s.MarkedPrefix.keygenSource s)
      (((0, 0), false), ∅, rel, role))) :
    out.1.1.1.2.2 = ((0, 0), false) ∧ out.1.1.1.1.1.pkSeed = s := by
  let _ : MonadLiftT (OracleComp LabCommon) (StateT PUnit.{1} (OracleComp LabCommon)) :=
    ⟨fun action => StateT.lift action⟩
  let src := SLHDSA.SHAKE128s.MarkedPrefix.keygenSource s
  let forwarder := (QueryImpl.id' LabCommon).liftTarget (StateT PUnit.{1} (OracleComp LabCommon))
  let cost := Sum.elim (fun _ : A.Domain => (0, 0)) (policy true s)
  let guarded := QueryImpl.guardQueryBudget caps cost forwarder fallback
  let start : PUnit.{1} × Paid := (PUnit.unit, ((0, 0), false))
  have relMem := source_support (Coverage.roleRunImpl FIPS205.core) _ role out member
  have rawMem := source_support
    (CoverageDeferred.relative FIPS205.core s (metadataCost true s)) _ rel out.1 relMem
  have guardMem := source_support (routeLab s) _ ∅ out.1.1 rawMem
  change out.1.1.1 ∈ support ((simulateQ guarded src).run start) at guardMem
  have keyMem := source_support guarded src start out.1.1.1 guardMem
  have privateSource := SLHDSA.SHAKE128s.MarkedPrefix.keygen_source_private s
  have transparent {β : Type} (action : OracleComp LabCommon β)
      (privateQueries : action.AllQueriesSatisfy SLHDSA.SHAKE128s.MarkedPrefix.PrivateCommon) :
      (simulateQ guarded action).run start = (·, start) <$> action := by
    induction action using OracleComp.inductionOn with
    | pure x => simp
    | query_bind input rest ih =>
      rw [allQueriesSatisfy_query_bind_iff] at privateQueries
      have free : cost input = (0, 0) :=
        SLHDSA.SHAKE128s.MarkedPrefix.private_source_cost_zero s input privateQueries.1
      have fits : ((0, 0) : Nat × Nat) ≤ caps := bot_le
      have step : (guarded input).run start =
          (·, start) <$> (liftM (LabCommon.query input) : OracleComp LabCommon _) := by
        simp [guarded, QueryImpl.guardQueryBudget, start, free, fits, forwarder,
          QueryImpl.liftTarget, QueryImpl.id', Functor.map_map]
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, step, bind_map_left, map_bind]
      exact bind_congr fun answer => ih answer (privateQueries.2 answer)
  rw [transparent src privateSource, support_map] at guardMem
  obtain ⟨keys, _, eqGuard⟩ := guardMem
  refine ⟨(congrArg (fun z : (PK × PK) × (PUnit.{1} × Paid) => z.2.2) eqGuard).symm, ?_⟩
  have key := support_simulateQ_subset commonProjection _ keyMem
  have key := support_simulateQ_subset (SigningView.Events.phaseImpl A Message .keygen) _ key
  have key := support_simulateQ_subset (fun input : Lab.Domain =>
    (liftM (A.query (.inl input)) : OracleComp A (Lab.Range input))) _ key
  change out.1.1.1.1 ∈ support ((labScheme FIPS205.core (fun pk => pure pk.pkSeed) s).keygen)
    at key
  simp only [labScheme, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at key
  obtain ⟨root, _, same⟩ := key
  exact congrArg (fun keys : PK × PK => keys.1.pkSeed) same

/-- The complete rejecting experiment funds native digest counts through its paid resource state
and, for a nonweak returned key, through its selected-message counter. -/
theorem marked_whole_count_bounds (s : FIPS205.core.PkSeed)
    (adv : Game.Adversary FIPS205.Answer PK) (caps : Nat × Nat)
    (fallback : (i : LabCommon.Domain) → LabCommon.Range i)
    (rel : CoverageDeferred.S FIPS205.core)
    (family : (j : Coverage.TapeClass) → List (Coverage.tapeClassRange FIPS205.core j))
    (out : Result Full)
    (member : out ∈ support
      (SLHDSA.SHAKE128s.MarkedPrefix.wholeRun s adv caps fallback rel family)) :
    out.2.2.1.cnt .signer ≤ out.1.1.1.2.2.1.2 ∧
      out.1.1.1.2.2.1.2 + out.2.2.1.cnt .forger ≤ out.1.1.1.2.2.1.1 ∧
      (¬IsWeakKey FIPS205.params out.1.1.1.1.1.1 → out.2.2.1.cnt .forger ≤ out.1.2.2.1) := by
  rw [SLHDSA.SHAKE128s.MarkedPrefix.marked_wholeRun_eq_prefix_suffix,
    mem_support_bind_iff] at member
  obtain ⟨mid, hm, hz⟩ := member
  let initial : Coverage.RoleState FIPS205.core := ((∅, family), (AnswerTape.ClassPos.init, ∅))
  have shape := prefix_paid_seed s caps fallback rel initial mid hm
  have preserved := (SLHDSA.SHAKE128s.MarkedPrefix.marked_keygen_uniform_and_role_state_unchanged
    s caps fallback ((0, 0), false) ∅ rel initial).2 mid hm
  generalize hpk : mid.1.1.1.1.1 = pk at hz shape
  obtain ⟨seed, root⟩ := pk
  have seedEq : seed = s := shape.2
  subst seed
  let before := world mid
  have start : Invariant (¬IsWeakKey FIPS205.params (⟨s, root⟩ : PK)) before := by
    simp [before, Invariant, NativeCounts.CountInvariant, shape.1, preserved,
      initial, AnswerTape.ClassPos.init]
  have done := suffix_safe s root mid.1.1.1.1.2 adv caps fallback before start out hz
  obtain ⟨funded, conditional⟩ := done
  refine ⟨funded.1, funded.2, ?_⟩
  have sourceMember := source_support (Coverage.roleRunImpl FIPS205.core) _ _ out hz
  have sourceMember := source_support
    (CoverageDeferred.relative FIPS205.core s (metadataCost true s)) _ _ out.1 sourceMember
  have sourceMember := source_support (routeLab s) _ _ out.1.1 sourceMember
  have sourceMember := source_support _ _ _ out.1.1.1 sourceMember
  have original := support_simulateQ_subset commonProjection _ sourceMember
  simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at original
  obtain ⟨⟨_, _⟩, _, verdict, _, eqOut⟩ := original
  have same := congrArg (fun full : Full => full.1.1) eqOut
  simpa only [same] using conditional

/-- A rejected framing still spends an admitted attempt and returns the original optional reply. -/
theorem malformed_signing_admission (s : FIPS205.core.PkSeed) (pk sk : PK) (request : Message)
    (invalid : (External.encodePureMessage request.context request.message).toOption = none)
    (caps : Nat × Nat) (fallback : (i : LabCommon.Domain) → LabCommon.Range i)
    (before : World) (out : Result (Option (List Byte)))
    (member : out ∈ support (execute s caps fallback (signSource s pk sk request) before)) :
    let admitted := before.1.2 = false ∧ before.1.1 + (32, 1) ≤ caps
    out.1.1.1.1 = none ∧
      out.1.1.1.2.2.1.2 = before.1.1.2 + (if admitted then 1 else 0) ∧
      (¬admitted → world out = ((before.1.1, true), before.2)) := by
  classical
  rw [callback_eq, native_program, support_map] at member
  obtain ⟨small, hs, rfl⟩ := member
  have zero : body s pk sk request = pure none := by
    simp [body, partialView, SigningView.rejectingEncoding_sign, invalid]
  have amount : policy true s (.signingAttempt request) = (32, 1) := by
    simp [policy, originalPolicy, reserveExtra, Game.Counted.sourcePolicy]
  simp only [smallCallback, zero, simulateQ_pure, simulateQ_bind, simulateQ_spec_query,
    StateT.run_pure, StateT.run_bind, mem_support_bind_iff, support_pure,
    Set.mem_singleton_iff] at hs
  obtain ⟨entry, he, shape⟩ := hs
  subst small
  simp only [smallHandler, NativeCounts.guardedImpl, QueryImpl.guardQueryBudget, flatten,
    StateT.run_mk, Sum.elim_inr, amount] at he
  split_ifs at he with aborted fits
  · simp only [support_pure, Set.mem_singleton_iff] at he
    subst entry
    have frozen : before = ((before.1.1, true), before.2) := Prod.ext (Prod.ext rfl aborted) rfl
    simpa [world, aborted] using frozen
  · rw [NativeCounts.nativeImpl_marker] at he
    simp only [map_pure, support_pure, Set.mem_singleton_iff] at he
    subst entry
    have clear : before.1.2 = false := Bool.eq_false_iff.mpr aborted
    simp [world, clear, fits]
  · simp only [support_pure, Set.mem_singleton_iff] at he
    subst entry
    simp [world, fits]

/-- Every guarded terminal respects both resource caps, including aborted and weak-key outcomes. -/
theorem marked_whole_paid_le_caps (s : FIPS205.core.PkSeed)
    (adv : Game.Adversary FIPS205.Answer PK) (caps : Nat × Nat)
    (fallback : (i : LabCommon.Domain) → LabCommon.Range i)
    (rel : CoverageDeferred.S FIPS205.core)
    (family : (j : Coverage.TapeClass) → List (Coverage.tapeClassRange FIPS205.core j))
    (out : Result Full)
    (member : out ∈ support
      (SLHDSA.SHAKE128s.MarkedPrefix.wholeRun s adv caps fallback rel family)) :
    out.1.1.1.2.2.1 ≤ caps := by
  let _ : MonadLiftT (OracleComp LabCommon) (StateT PUnit.{1} (OracleComp LabCommon)) :=
    ⟨fun action => StateT.lift action⟩
  let fwd := (QueryImpl.id' LabCommon).liftTarget (StateT PUnit.{1} (OracleComp LabCommon))
  let cost := Sum.elim (fun _ : A.Domain => (0, 0)) (policy true s)
  let guard := QueryImpl.guardQueryBudget caps cost fwd fallback
  let valid := fun st : PUnit.{1} × Paid => st.2.1 ≤ caps
  have relMem := source_support (Coverage.roleRunImpl FIPS205.core) _ _ out member
  have routeMem := source_support
    (CoverageDeferred.relative FIPS205.core s (metadataCost true s)) _ rel out.1 relMem
  have guardMem := source_support (routeLab s) _ ∅ out.1.1 routeMem
  apply simulateQ_run_preserves_inv_of_query guard valid _ (commonSource true s adv)
    (PUnit.unit, ((0, 0), false)) (show ((0, 0) : Nat × Nat) ≤ caps from bot_le) _ guardMem
  intro input before prior res mem
  simp only [guard, QueryImpl.guardQueryBudget, StateT.run_mk] at mem
  split_ifs at mem with aborted fits
  · simp only [support_pure, Set.mem_singleton_iff] at mem
    exact mem ▸ prior
  · rw [support_map] at mem
    obtain ⟨_, _, rfl⟩ := mem
    exact fits
  · simp only [support_pure, Set.mem_singleton_iff] at mem
    exact mem ▸ prior

end SLHDSA.SHAKE128s.Bridge.SharedExperiment.SigningCounts

open SLHDSA.SHAKE128s.Bridge.SharedExperiment.SigningCounts
