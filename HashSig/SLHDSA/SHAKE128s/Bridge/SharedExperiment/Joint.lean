/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import HashSig.SLHDSA.SHAKE128s.Bridge.SharedExperiment.Joint.Source
import HashSig.SLHDSA.Security.LabEquiv.Experiment
import VCVio.OracleComp.SimSemantics.WriterT.Measure
import HashSig.SLHDSA.Security.KeyDiscipline
import VCVio.OracleComp.SimSemantics.StateT.StateSeparating

/-!
# Guarded eager joint observations

The guarded derivation and lab sources have equal eager observations. Generated keys remain
visible on abort, together with the complete physical graph, raw cache and metadata.
-/

public section

open OracleComp OracleSpec SignatureAlg
open SLHDSA.SHAKE128s
open SLHDSA.Security
open scoped ENNReal

namespace SLHDSA.SHAKE128s.Bridge.SharedExperiment.Guarded

private abbrev Log := QueryLog (Message →ₒ Option (List Byte))
private abbrev World := ((LabState FIPS205.core × Raw.QueryCache) × Meta) × Paid

/-- Exact original-source observation of a LAB query; labels and derivations are silent. -/
private def originalLabel : Lab.Domain → Option R.Domain
  | .inl (.inl (.inl n)) => some (.inl n)
  | .inl (.inl (.inr typed)) => some (.inr (encode FIPS205.params typed))
  | _ => none

private def projection :
    QueryImpl (SigningView.Events.Spec Lab Message) (OracleComp (Lab + O)) :=
  QueryImpl.add
    (fun input => liftM ((Lab + O).query (.inl input)))
    (fun event => match event with
      | .signingAttempt request => liftM ((Lab + O).query (.inr (.signingAttempt request)))
      | .ambient phase input => match originalLabel input with
        | some label => liftM ((Lab + O).query (.inr (.ambient phase label)))
        | none => pure PUnit.unit)

/-- Existing eager graph with the actual raw table framed unchanged during honest components. -/
private noncomputable def eagerGuard (s : FIPS205.core.PkSeed)
    (reserve trackRaw : Bool) (caps : Nat × Nat)
    (fallback : (input : (Lab + O).Domain) → (Lab + O).Range input) :
    QueryImpl (Lab + O) (StateT World ProbComp) :=
  let framed := (slhGraph FIPS205.core s).eagerImpl.extendState
    (fun _ _ _ _ (privateTable : Raw.QueryCache) => privateTable)
  let observed := (eraseObsImpl (Ev := Ev) framed).extendState
    (aux (metadataCost trackRaw s))
  QueryImpl.guardQueryBudget caps
    (Sum.elim (fun _ : Lab.Domain => (0, 0)) (policy reserve s)) observed fallback

private def frame (table : Raw.QueryCache) (n : Nat) (phase : SigningView.Phase)
    (counts : Nat × Nat) (graph : LabState FIPS205.core) : World :=
  (((graph, table), (n, phase)), (counts, false))

private theorem zero_phase_run {alpha : Type} (s : FIPS205.core.PkSeed)
    (reserve trackRaw : Bool) (caps counts : Nat × Nat) (hfit : counts ≤ caps)
    (fallback : (input : (Lab + O).Domain) → (Lab + O).Range input)
    (table : Raw.QueryCache) (n : Nat) (phase : SigningView.Phase)
    (hphase : phase = .keygen ∨ phase = .signer) (program : OracleComp Lab alpha)
    (graph : LabState FIPS205.core) :
    (simulateQ (eagerGuard s reserve trackRaw caps fallback)
      (simulateQ projection (simulateQ (SigningView.Events.phaseImpl Lab Message phase)
        program))).run (frame table n phase counts graph) =
      Prod.map id (frame table n phase counts) <$>
        (simulateQ (slhGraph FIPS205.core s).eagerImpl program).run graph := by
  let impl := ((eagerGuard s reserve trackRaw caps fallback) ∘ₛ projection) ∘ₛ
    SigningView.Events.phaseImpl Lab Message phase
  have addZero : ∀ c : Nat × Nat, c + (0, 0) = c := by rintro ⟨a, b⟩; rfl
  have step : ∀ input graph,
      Prod.map id (frame table n phase counts) <$>
        ((slhGraph FIPS205.core s).eagerImpl input).run graph =
      (impl input).run (frame table n phase counts graph) := by
    intro input graph
    rcases hphase with rfl | rfl <;>
      rcases input with (((native | typed) | derive) | label) <;>
      simp [impl, QueryImpl.compose, SigningView.Events.phaseImpl,
        QueryImpl.preInsert, SigningView.Events.emit, projection, originalLabel,
        QueryImpl.add, Game.Counted.sourceKind, addZero,
        eagerGuard, QueryImpl.guardQueryBudget, frame, QueryImpl.extendState,
        eraseObsImpl, aux, metadataCost, selectedRaw, policy, originalPolicy,
        reserveExtra, Game.Counted.sourcePolicy, hfit, Functor.map_map, id_eq] <;> rfl
  have h := map_run_simulateQ_eq_of_query_map_eq
    (slhGraph FIPS205.core s).eagerImpl impl (frame table n phase counts) step program graph
  simpa only [impl, QueryImpl.simulateQ_compose] using h.symm

private theorem total_keygen_law (s : FIPS205.core.PkSeed) (graph : LabState FIPS205.core) :
    (simulateQ (slhGraph FIPS205.core s).eagerImpl (partialView false s).keygen).run graph =ᵈ
      (simulateQ (slhGraph FIPS205.core s).eagerImpl (partialView true s).keygen).run graph := by
  have hd := Concrete.keyDiscipline_approvedPrimitives .SLHDSA_SHAKE_128s
  have kg := deriveScheme_keygen_labTriple FIPS205.core hd s
    (optRand := fun pk => pure pk.pkSeed)
  let _ : MeasurableSpace ((PK × PK) × LabState FIPS205.core) := ⊤
  exact EvalDistEq.of_evalDist_eq (kg.evalDist_run_eq (s := graph) trivial)

private theorem total_sign_law (s : FIPS205.core.PkSeed) (root : FIPS205.core.Y)
    (request : Message) (graph : LabState FIPS205.core) :
    (simulateQ (slhGraph FIPS205.core s).eagerImpl
      ((partialView false s).sign ⟨s, root⟩ ⟨s, root⟩ request)).run graph =ᵈ
    (simulateQ (slhGraph FIPS205.core s).eagerImpl
      ((partialView true s).sign ⟨s, root⟩ ⟨s, root⟩ request)).run graph := by
  have hd := Concrete.keyDiscipline_approvedPrimitives .SLHDSA_SHAKE_128s
  have signing := fun msg => deriveScheme_sign_labTriple FIPS205.core hd s
    (optRand := fun pk => pure pk.pkSeed) ⟨s, root⟩ ⟨s, root⟩ msg rfl
  let _ : MeasurableSpace (GeneralScheme.SignatureCore FIPS205.params FIPS205.core ×
    LabState FIPS205.core) := ⊤
  simp only [partialView, Bool.false_eq_true, ↓reduceIte, SigningView.rejectingEncoding_sign]
  split
  · exact EvalDistEq.rfl
  · simp only [simulateQ_map, StateT.run_map]
    exact (EvalDistEq.of_evalDist_eq ((signing _).evalDist_run_eq (s := graph) trivial)).map _

private noncomputable def callback (useLab : Bool) (s : FIPS205.core.PkSeed) (root : FIPS205.core.Y)
    (request : Message) : OracleComp (Lab + O) (Option (List Byte) × Log) :=
  simulateQ projection ((QueryImpl.withLogging
    ((SigningView.Events.viewWithEvents (partialView useLab s)).sign ⟨s, root⟩ ⟨s, root⟩)
    request).run)

private def logReply (request : Message) (reply : Option (List Byte)) :
    Option (List Byte) × Log := (reply, [⟨request, reply⟩])

private theorem callback_decompose (useLab : Bool) (s : FIPS205.core.PkSeed)
    (root : FIPS205.core.Y) (request : Message)
    (reserve trackRaw : Bool) (caps : Nat × Nat)
    (fallback : (input : (Lab + O).Domain) → (Lab + O).Range input) (state : World) :
    (simulateQ (eagerGuard s reserve trackRaw caps fallback)
      (callback useLab s root request)).run state =
    ((eagerGuard s reserve trackRaw caps fallback (.inr (.signingAttempt request))).run state
      >>= fun first =>
        Prod.map (logReply request) id <$>
          (simulateQ (eagerGuard s reserve trackRaw caps fallback)
            (simulateQ projection (simulateQ (SigningView.Events.phaseImpl Lab Message .signer)
              ((partialView useLab s).sign ⟨s, root⟩ ⟨s, root⟩ request)))).run first.2) := by
  simp [callback, SigningView.Events.viewWithEvents,
    SigningView.Events.emit, projection, QueryImpl.add, simulateQ_bind, simulateQ_map,
    StateT.run_bind, StateT.run_map, Functor.map_map]
  rfl

private theorem signing_event_run (s : FIPS205.core.PkSeed) (request : Message)
    (reserve trackRaw : Bool) (caps counts : Nat × Nat)
    (fallback : (input : (Lab + O).Domain) → (Lab + O).Range input)
    (graph : LabState FIPS205.core) (table : Raw.QueryCache) (metadata : Meta) (aborted : Bool) :
    (eagerGuard s reserve trackRaw caps fallback (.inr (.signingAttempt request))).run
        (((graph, table), metadata), (counts, aborted)) =
      pure (PUnit.unit,
        if aborted = false ∧ counts + policy reserve s (.signingAttempt request) ≤ caps
        then frame table metadata.1 .signer
          (counts + policy reserve s (.signingAttempt request)) graph
        else (((graph, table), metadata), (counts, true))) := by
  have hf : fallback (.inr (.signingAttempt request)) = PUnit.unit := @Subsingleton.elim PUnit _ _ _
  cases aborted <;>
    simp [eagerGuard, QueryImpl.guardQueryBudget, QueryImpl.extendState, eraseObsImpl,
      aux, metadataCost, selectedRaw, frame, hf]
  split <;> rfl

private theorem guard_frozen (s : FIPS205.core.PkSeed) (reserve trackRaw : Bool)
    (caps : Nat × Nat) (fallback : (input : (Lab + O).Domain) → (Lab + O).Range input)
    {alpha : Type} (program : OracleComp (Lab + O) alpha) (state : World)
    (hs : state.2.2 = true) :
    ∀ result ∈ support ((simulateQ (eagerGuard s reserve trackRaw caps fallback)
      program).run state), result.2 = state := by
  apply simulateQ_run_preservesInv _ (fun st => st = state) _ program state rfl
  intro input current hc result hr
  subst current
  have h : result = (fallback input, state) := by
    simpa [eagerGuard, QueryImpl.guardQueryBudget, hs] using hr
  exact congrArg Prod.snd h

private theorem callback_admitted (useLab : Bool) (s : FIPS205.core.PkSeed)
    (root : FIPS205.core.Y) (request : Message)
    (reserve trackRaw : Bool) (caps counts : Nat × Nat)
    (fallback : (input : (Lab + O).Domain) → (Lab + O).Range input)
    (graph : LabState FIPS205.core) (table : Raw.QueryCache) (metadata : Meta)
    (hfit : counts + policy reserve s (.signingAttempt request) ≤ caps) :
    (simulateQ (eagerGuard s reserve trackRaw caps fallback)
      (callback useLab s root request)).run (((graph, table), metadata), (counts, false)) =
      Prod.map (logReply request)
          (frame table metadata.1 .signer (counts + policy reserve s (.signingAttempt request))) <$>
        (simulateQ (slhGraph FIPS205.core s).eagerImpl
          ((partialView useLab s).sign ⟨s, root⟩ ⟨s, root⟩ request)).run graph := by
  rw [callback_decompose, signing_event_run]
  simp only [hfit, and_self, ↓reduceIte, pure_bind]
  rw [zero_phase_run s reserve trackRaw caps _ hfit fallback table metadata.1 .signer
    (Or.inr rfl)]
  simp only [Functor.map_map]
  rfl

/-- The generated keys and full logged callback agree under the original guard. -/
private theorem honest_keygen_and_callback :
  ∀ (s : FIPS205.core.PkSeed) (reserve trackRaw : Bool) (caps : Nat × Nat)
    (fallbackHonest fallbackLab :
      (input : (Lab + O).Domain) → (Lab + O).Range input)
    (graph : LabState FIPS205.core) (privateTable : Raw.QueryCache),
    let honest := SigningView.Events.viewWithEvents (partialView false s)
    let lab := SigningView.Events.viewWithEvents (partialView true s)
    let honestGuard := eagerGuard s reserve trackRaw caps fallbackHonest
    let labGuard := eagerGuard s reserve trackRaw caps fallbackLab
    let initial : World :=
      (((graph, privateTable), (0, .keygen)), ((0, 0), false))
    let honestKeygen := (simulateQ honestGuard (simulateQ projection honest.keygen)).run initial
    let labKeygen := (simulateQ labGuard (simulateQ projection lab.keygen)).run initial
    (honestKeygen =ᵈ labKeygen) ∧
    (∀ result ∈ support labKeygen,
      result.1.2 = result.1.1 ∧ result.1.1.pkSeed = s ∧
      result.2.1.1.2 = privateTable ∧ result.2.1.2 = (0, .keygen) ∧
      result.2.2 = ((0, 0), false)) ∧
    ∀ (root : FIPS205.core.Y) (request : Message)
      (metadata : Meta) (counts : Nat × Nat) (aborted : Bool),
      let key : PK := ⟨s, root⟩
      let state : World := (((graph, privateTable), metadata), (counts, aborted))
      let honestCallback := (simulateQ honestGuard (simulateQ projection
        ((QueryImpl.withLogging (honest.sign key key) request).run))).run state
      let labCallback := (simulateQ labGuard (simulateQ projection
        ((QueryImpl.withLogging (lab.sign key key) request).run))).run state
      let observation := fun result : ((Option (List Byte) × Log) × World) =>
        ((key, key), (if result.2.2.2 then none else some result.1), result.2)
      (observation <$> honestCallback) =ᵈ (observation <$> labCallback) ∧
      (∀ result ∈ support labCallback,
        let admitted := aborted = false ∧
          counts + policy reserve s (.signingAttempt request) ≤ caps
        result.1.2 = [⟨request, result.1.1⟩] ∧
        result.2.1.1.2 = privateTable ∧
        result.2.2 = (if admitted then
          (counts + policy reserve s (.signingAttempt request), false)
          else (counts, true)) ∧
        result.2.1.2 = (if admitted then (metadata.1, .signer) else metadata) ∧
        (¬admitted → result.2.1.1.1 = graph)) := by
  intro s reserve trackRaw caps fallbackHonest fallbackLab graph privateTable
  dsimp only
  have zeroFit : (0, 0) ≤ caps := ⟨Nat.zero_le _, Nat.zero_le _⟩
  have keygen_shape : ∀ r ∈ support
      ((simulateQ (slhGraph FIPS205.core s).eagerImpl (partialView true s).keygen).run graph),
      r.1.2 = r.1.1 ∧ r.1.1.pkSeed = s := by
    intro r hr
    simp only [partialView, ↓reduceIte, SigningView.rejectingEncoding_keygen,
      labScheme, simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure] at hr
    obtain ⟨z, _, hr⟩ := mem_support_bind_peel _ _ hr
    have hr' := OracleComp.eq_of_mem_support_pure _ hr
    subst r
    exact ⟨rfl, rfl⟩
  constructor
  · change (simulateQ (eagerGuard s reserve trackRaw caps fallbackHonest)
      (simulateQ projection (simulateQ
        (SigningView.Events.phaseImpl Lab Message .keygen) (partialView false s).keygen))).run
          (frame privateTable 0 .keygen (0, 0) graph) =ᵈ
      (simulateQ (eagerGuard s reserve trackRaw caps fallbackLab)
      (simulateQ projection (simulateQ
        (SigningView.Events.phaseImpl Lab Message .keygen) (partialView true s).keygen))).run
          (frame privateTable 0 .keygen (0, 0) graph)
    rw [zero_phase_run s reserve trackRaw caps (0, 0) zeroFit fallbackHonest privateTable 0
      .keygen (Or.inl rfl), zero_phase_run s reserve trackRaw caps (0, 0) zeroFit
      fallbackLab privateTable 0 .keygen (Or.inl rfl)]
    exact (total_keygen_law s graph).map _
  constructor
  · intro result hr
    change result ∈ support ((simulateQ (eagerGuard s reserve trackRaw caps fallbackLab)
      (simulateQ projection (simulateQ
      (SigningView.Events.phaseImpl Lab Message .keygen) (partialView true s).keygen))).run
        (frame privateTable 0 .keygen (0, 0) graph)) at hr
    rw [zero_phase_run s reserve trackRaw caps (0, 0) zeroFit fallbackLab privateTable 0
      .keygen (Or.inl rfl)] at hr
    obtain ⟨r, hraw, rfl⟩ := mem_support_map_peel _ _ hr
    exact ⟨(keygen_shape r hraw).1, (keygen_shape r hraw).2, rfl, rfl, rfl⟩
  intro root request metadata counts aborted
  let state : World := (((graph, privateTable), metadata), (counts, aborted))
  let finalState : World := (((graph, privateTable), metadata), (counts, true))
  let observation := fun result : ((Option (List Byte) × Log) × World) =>
    (((⟨s, root⟩, ⟨s, root⟩) : PK × PK),
      (if result.2.2.2 then none else some result.1), result.2)
  change (observation <$> (simulateQ (eagerGuard s reserve trackRaw caps fallbackHonest)
      (callback false s root request)).run state) =ᵈ
      (observation <$> (simulateQ (eagerGuard s reserve trackRaw caps fallbackLab)
        (callback true s root request)).run state) ∧ _
  have rejected (hbad : ¬(aborted = false ∧
      counts + policy reserve s (.signingAttempt request) ≤ caps))
      (fb : (input : (Lab + O).Domain) → (Lab + O).Range input)
      (useLab : Bool) :
      ∀ r ∈ support ((simulateQ (eagerGuard s reserve trackRaw caps fb)
        (callback useLab s root request)).run state),
        r.1.2 = [⟨request, r.1.1⟩] ∧ r.2 = finalState := by
    intro r hr
    rw [callback_decompose, signing_event_run] at hr
    simp only [ite_eq_right hbad, pure_bind] at hr
    obtain ⟨v, hv, rfl⟩ := mem_support_map_peel _ _ hr
    exact ⟨rfl, guard_frozen s reserve trackRaw caps fb _ finalState rfl v hv⟩
  constructor
  · by_cases had : aborted = false ∧
        counts + policy reserve s (.signingAttempt request) ≤ caps
    · rcases had with ⟨rfl, hfit⟩
      rw [callback_admitted false s root request reserve trackRaw caps counts fallbackHonest
        graph privateTable metadata hfit,
        callback_admitted true s root request reserve trackRaw caps counts fallbackLab
        graph privateTable metadata hfit]
      simp only [Functor.map_map]
      exact (total_sign_law s root request graph).map _
    · have hc (fb : (input : (Lab + O).Domain) → (Lab + O).Range input) (useLab : Bool) :
          (observation <$> (simulateQ (eagerGuard s reserve trackRaw caps fb)
            (callback useLab s root request)).run state) =ᵈ
          (pure ((⟨s, root⟩, ⟨s, root⟩), none, finalState) :
            ProbComp ((PK × PK) × Option (Option (List Byte) × Log) × World)) := by
        rw [map_eq_bind_pure_comp]
        refine (OracleComp.EvalDistEq.bind_congr_of_support _ (fun r hr => ?_)).trans
          (OracleComp.EvalDistEq.bind_const _ _)
        simp only [Function.comp_apply, observation, (rejected had fb useLab r hr).2,
          finalState, ↓reduceIte]
        exact EvalDistEq.rfl
      exact (hc fallbackHonest false).trans (hc fallbackLab true).symm
  · intro result hr
    change result ∈ support ((simulateQ (eagerGuard s reserve trackRaw caps fallbackLab)
      (callback true s root request)).run state) at hr
    by_cases had : aborted = false ∧
        counts + policy reserve s (.signingAttempt request) ≤ caps
    · rcases had with ⟨rfl, hfit⟩
      dsimp only [state] at hr
      rw [callback_admitted true s root request reserve trackRaw caps counts fallbackLab
        graph privateTable metadata hfit] at hr
      obtain ⟨r, _, rfl⟩ := mem_support_map_peel _ _ hr
      simp only [hfit, and_self, ↓reduceIte,
        not_true_eq_false, false_implies, and_true]
      exact ⟨rfl, rfl, rfl, rfl⟩
    · have h := rejected had fallbackLab true result hr
      simp only [ite_eq_right had]
      exact ⟨h.1, congrArg (fun w : World => w.1.1.2) h.2,
        congrArg Prod.snd h.2, congrArg (fun w : World => w.1.2) h.2,
        fun _ => congrArg (fun w : World => w.1.1.1) h.2⟩


private abbrev LabObs := Lab + O

private def embedD : QueryImpl DCommon (OracleComp LabCommon)
  | .inl (.inl native) => liftM (LabCommon.query (.inl (.inl (.inl native))))
  | .inl (.inr raw) => liftM (LabCommon.query (.inl (.inr raw)))
  | .inr event => liftM (LabCommon.query (.inr event))

private def embedDO : QueryImpl (deriveSpec FIPS205.core + O) (OracleComp LabObs)
  | .inl native => liftM (LabObs.query (.inl (.inl native)))
  | .inr event => liftM (LabObs.query (.inr event))

private noncomputable def honestFallback
    (s : FIPS205.core.PkSeed)
    (fallback : (input : LabCommon.Domain) → LabCommon.Range input) :
    (input : LabCommon.Domain) → LabCommon.Range input
  | .inl (.inl (.inl native)) => deriveFallback s (.inl (.inl native))
  | .inl (.inl (.inr label)) => fallback (.inl (.inl (.inr label)))
  | .inl (.inr raw) => deriveFallback s (.inl (.inr raw))
  | .inr event => deriveFallback s (.inr event)

private noncomputable def observeLab (s : FIPS205.core.PkSeed) (trackRaw : Bool) :
    QueryImpl LabObs (StateT Meta (OracleComp Lab)) :=
  letI : MonadLiftT (OracleComp Lab) (StateT Meta (OracleComp Lab)) :=
    ⟨fun action => StateT.lift action⟩
  QueryImpl.add ((QueryImpl.id' Lab).liftTarget (StateT Meta (OracleComp Lab)))
    (fun event => StateT.mk fun metadata => pure (PUnit.unit,
      aux (spec := Lab) (metadataCost trackRaw s)
        (.inr event) PUnit.unit PUnit.unit PUnit.unit metadata))

private theorem observe_free_square {alpha : Type} (s : FIPS205.core.PkSeed)
    (trackRaw : Bool) (program : OracleComp (deriveSpec FIPS205.core + O) alpha)
    (metadata : Meta) :
    liftComp ((simulateQ (observeD s trackRaw) program).run metadata) Lab =
      (simulateQ (observeLab s trackRaw) (simulateQ embedDO program)).run metadata := by
  let liftLab := QueryImpl.ofLift (deriveSpec FIPS205.core) (OracleComp Lab)
  let combined := (observeLab s trackRaw) ∘ₛ embedDO
  have square : ∀ input state,
      simulateQ liftLab ((observeD s trackRaw input).run state) =
        (combined input).run state := by
    intro input state
    rcases input with native | event
    · rcases native with native | derive <;>
        simp [liftLab, combined, observeD, observeLab, embedDO, QueryImpl.add,
          QueryImpl.liftTarget, QueryImpl.id',
          OracleComp.liftM_eq_liftM_liftM, aux] <;> rfl
    · cases event <;>
        simp [liftLab, combined, observeD, observeLab, embedDO, QueryImpl.add,
          QueryImpl.liftTarget, QueryImpl.id', aux]
  have h := simulateQ_StateT_compose (observeD s trackRaw) liftLab combined square
    program metadata
  have hlift : (fun input =>
      (liftM ((deriveSpec FIPS205.core).query input) :
        OracleComp Lab ((deriveSpec FIPS205.core).Range input))) = liftLab := by
    funext input
    rcases input with native | derive <;> rfl
  rw [liftComp_def, hlift]
  simpa only [combined, QueryImpl.simulateQ_compose] using h


private theorem guard_free_square {alpha : Type} (s : FIPS205.core.PkSeed)
    (reserve : Bool) (caps : Nat × Nat)
    (fallback : (input : LabCommon.Domain) → LabCommon.Range input)
    (program : OracleComp DCommon alpha) (counts : Nat × Nat) (aborted : Bool) :
    letI : MonadLiftT (OracleComp DCommon) (StateT PUnit (OracleComp DCommon)) :=
      ⟨fun action => StateT.lift action⟩
    letI : MonadLiftT (OracleComp LabCommon) (StateT PUnit (OracleComp LabCommon)) :=
      ⟨fun action => StateT.lift action⟩
    let leftForward := (QueryImpl.id' DCommon).liftTarget (StateT PUnit (OracleComp DCommon))
    let rightForward := (QueryImpl.id' LabCommon).liftTarget
      (StateT PUnit (OracleComp LabCommon))
    simulateQ embedD ((simulateQ (QueryImpl.guardQueryBudget caps
      (Sum.elim (fun _ : DNative.Domain => (0, 0)) (policy reserve s))
      leftForward (deriveFallback s)) program).run (PUnit.unit, (counts, aborted))) =
    (simulateQ (QueryImpl.guardQueryBudget caps
      (Sum.elim (fun _ : A.Domain => (0, 0)) (policy reserve s))
      rightForward (honestFallback s fallback)) (simulateQ embedD program)).run
        (PUnit.unit, (counts, aborted)) := by
  dsimp only
  let _ : MonadLiftT (OracleComp DCommon) (StateT PUnit (OracleComp DCommon)) :=
    ⟨fun action => StateT.lift action⟩
  let _ : MonadLiftT (OracleComp LabCommon) (StateT PUnit (OracleComp LabCommon)) :=
    ⟨fun action => StateT.lift action⟩
  let leftForward := (QueryImpl.id' DCommon).liftTarget (StateT PUnit (OracleComp DCommon))
  let rightForward := (QueryImpl.id' LabCommon).liftTarget
    (StateT PUnit (OracleComp LabCommon))
  let left := QueryImpl.guardQueryBudget caps
    (Sum.elim (fun _ : DNative.Domain => (0, 0)) (policy reserve s))
    leftForward (deriveFallback s)
  let right := QueryImpl.guardQueryBudget caps
    (Sum.elim (fun _ : A.Domain => (0, 0)) (policy reserve s))
    rightForward (honestFallback s fallback)
  have square : ∀ input state,
      simulateQ embedD ((left input).run state) = ((right ∘ₛ embedD) input).run state := by
    intro input state
    rcases state with ⟨token, count, flag⟩
    cases flag <;>
      rcases input with (native | raw) | event <;>
      simp [left, right, leftForward, rightForward, QueryImpl.guardQueryBudget,
        QueryImpl.compose, embedD, honestFallback, QueryImpl.id', QueryImpl.liftTarget]
  have h := simulateQ_StateT_compose left embedD (right ∘ₛ embedD) square
    program (PUnit.unit, (counts, aborted))
  simpa only [left, right, QueryImpl.simulateQ_compose] using h


private theorem route_free_square {alpha : Type} (s : FIPS205.core.PkSeed)
    (program : OracleComp DCommon alpha) (table : Raw.QueryCache) :
    simulateQ embedDO ((simulateQ (routeD s) program).run table) =
      (simulateQ (routeLab s) (simulateQ embedD program)).run table := by
  let combined := (routeLab s) ∘ₛ embedD
  have square : ∀ input state,
      simulateQ embedDO ((routeD s input).run state) = (combined input).run state := by
    intro input state
    rcases input with (native | raw) | event
    · simp [routeD, combined, routeLab, embedD, embedDO, QueryImpl.add]
    · dsimp only [routeD, combined, routeLab, embedD, QueryImpl.compose, QueryImpl.add]
      simp only [simulateQ_spec_query, StateT.run_mk]
      change simulateQ embedDO
          (simulateQ (QueryImpl.ofLift (unifSpec + H)
            (OracleComp (deriveSpec FIPS205.core + O)))
              (((encoding s).tableRouter raw).run state)) =
          simulateQ (QueryImpl.ofLift (unifSpec + H) (OracleComp LabObs))
            (((encoding s).tableRouter raw).run state)
      rw [← QueryImpl.simulateQ_compose]
      congr 1
      funext input
      rcases input with native | (typed | prf) <;>
        simp [QueryImpl.compose, QueryImpl.ofLift, embedDO,
          OracleComp.liftM_eq_liftM_liftM] <;> rfl
    · simp [routeD, combined, routeLab, embedD, embedDO, QueryImpl.add]
  have h := simulateQ_StateT_compose (routeD s) embedDO combined square program table
  simpa only [combined, QueryImpl.simulateQ_compose] using h

private theorem observe_eager_square {alpha : Type} (s : FIPS205.core.PkSeed)
    (trackRaw : Bool) (program : OracleComp LabObs alpha)
    (metadata : Meta) (graph : LabState FIPS205.core) :
    (fun r : (alpha × Meta) × LabState FIPS205.core => (r.1.1, (r.2, r.1.2))) <$>
        (simulateQ (slhGraph FIPS205.core s).eagerImpl
          ((simulateQ (observeLab s trackRaw) program).run metadata)).run graph =
      (simulateQ ((eraseObsImpl (Ev := Ev) (slhGraph FIPS205.core s).eagerImpl).extendState
        (aux (spec := Lab) (metadataCost trackRaw s))) program).run (graph, metadata) := by
  let actual := (eraseObsImpl (Ev := Ev) (slhGraph FIPS205.core s).eagerImpl).extendState
    (aux (spec := Lab) (metadataCost trackRaw s))
  let combined := ((slhGraph FIPS205.core s).eagerImpl.mapStateTBase
    (observeLab s trackRaw)).flattenStateT
  have square : ∀ input state,
      Prod.map id Prod.swap <$> (combined input).run state =
        (actual input).run (Prod.swap state) := by
    intro input state
    rcases state with ⟨metadata, graph⟩
    rcases input with native | event <;>
      simp [combined, actual, QueryImpl.flattenStateT, QueryImpl.mapStateTBase,
        observeLab, eraseObsImpl, QueryImpl.extendState, QueryImpl.add,
        QueryImpl.liftTarget, QueryImpl.id',
        Functor.map_map, StateT.run_map, Prod.map, Prod.swap, aux]
  have h := map_run_simulateQ_eq_of_query_map_eq combined actual Prod.swap square
    program (metadata, graph)
  rw [simulateQ_mapStateTBase_run_eq_map_flattenStateT]
  have mapEq : (Prod.map id Prod.swap :
      alpha × (Meta × LabState FIPS205.core) → alpha × (LabState FIPS205.core × Meta)) =
      (fun r => (r.1, (r.2.2, r.2.1))) := by funext r; rfl
  rw [mapEq] at h
  simpa only [combined, actual, Functor.map_map, Function.comp_def, Prod.swap] using h

private abbrev Cache := (LabState FIPS205.core × Raw.QueryCache) × Meta

private def routeState : (Raw.QueryCache × (LabState FIPS205.core × Meta)) ≃ Cache where
  toFun r := ((r.2.1, r.1), r.2.2)
  invFun r := (r.1.2, (r.1.1, r.2))
  left_inv _ := rfl
  right_inv _ := rfl

private noncomputable def wholeObserved (s : FIPS205.core.PkSeed) (trackRaw : Bool) :
    QueryImpl LabCommon (StateT Cache ProbComp) :=
  QueryImpl.Stateful.transportState (QueryImpl.Stateful.link (routeLab s)
    ((eraseObsImpl (Ev := Ev) (slhGraph FIPS205.core s).eagerImpl).extendState
      (aux (spec := Lab) (metadataCost trackRaw s)))) routeState

private noncomputable def wholeGuard (s : FIPS205.core.PkSeed)
    (reserve trackRaw : Bool) (caps : Nat × Nat)
    (fallback : (input : LabCommon.Domain) → LabCommon.Range input) :
    QueryImpl LabCommon (StateT World ProbComp) :=
  QueryImpl.guardQueryBudget caps
    (Sum.elim (fun _ : A.Domain => (0, 0)) (policy reserve s))
    (wholeObserved s trackRaw) fallback


private def liftBase : QueryImpl LabCommon (OracleComp (LabCommon + Sign)) :=
  fun input => liftM ((LabCommon + Sign).query (.inl input))

private def liftClient : QueryImpl (SigningView.Events.Spec A Message + Sign)
    (OracleComp (LabCommon + Sign)) :=
  QueryImpl.add
    (fun input => simulateQ liftBase
      (commonProjection input))
    (fun request => liftM ((LabCommon + Sign).query (.inr request)))

private noncomputable def afterKeygen (s : FIPS205.core.PkSeed)
    (adv : Game.Adversary FIPS205.Answer PK) (key : PK) :
    OracleComp (LabCommon + Sign) ((Message × List Byte) × Bool) := do
  let forgery ← simulateQ liftClient
    (SigningView.Events.mainWithEvents (commonMain adv) key)
  let verified ← simulateQ liftBase
    (simulateQ commonProjection
      ((SigningView.Events.viewWithEvents (commonView true s)).verify
        key forgery.1 forgery.2))
  return (forgery, verified)

private def componentFallback
    (fallback : (input : LabCommon.Domain) → LabCommon.Range input) :
    (input : (Lab + O).Domain) → (Lab + O).Range input
  | .inl native => fallback (.inl (.inl native))
  | .inr event => fallback (.inr event)

private noncomputable def clientHandler (useLab : Bool) (s : FIPS205.core.PkSeed)
    (reserve trackRaw : Bool) (caps : Nat × Nat)
    (fallback : (input : LabCommon.Domain) → LabCommon.Range input)
    (root : FIPS205.core.Y) :
    QueryImpl (LabCommon + Sign)
      (WriterT Log (StateT World ProbComp)) :=
  QueryImpl.add
    (fun input => WriterT.mk ((fun value => (value, (∅ : Log))) <$>
      (wholeGuard s reserve trackRaw caps fallback input)))
    (fun request => WriterT.mk
      (simulateQ (eagerGuard s reserve trackRaw caps
        (componentFallback fallback))
        (callback useLab s root request)))

private theorem common_verify_eq (s : FIPS205.core.PkSeed)
    (pk : PK) (request : Message) (wire : List Byte) :
    (commonView false s).verify pk request wire =
      (commonView true s).verify pk request wire := by
  have verify : (partialView false s).verify pk request wire =
      (partialView true s).verify pk request wire := by
    simp only [partialView, Bool.false_eq_true, ↓reduceIte,
      SigningView.rejectingEncoding_verify, SignatureAlg.map_verify]
    cases hframe : (External.encodePureMessage request.context request.message).toOption with
    | none => rfl
    | some message =>
      cases hdecode : (SLHDSA.decodeSignature FIPS205.params
          (SLHDSA.Concrete.shakeWireCodec FIPS205.params.params) wire).toOption with
      | none => rfl
      | some signature =>
        simpa only [SignatureAlg.map_verify] using
          map_labLiftHom_deriveScheme_verify FIPS205.core
            (fun pk : PK => (pure pk.pkSeed : ProbComp FIPS205.core.Y)) s pk message signature
  simpa only [commonView, SigningView.map_verify, simulateQ'_apply] using
    congrArg (fun body => simulateQ (fun input : Lab.Domain =>
      (liftM (A.query (.inl input)) : OracleComp A (Lab.Range input))) body) verify

private theorem guarded_base_clip (s : FIPS205.core.PkSeed)
    (reserve trackRaw : Bool) (caps : Nat × Nat)
    (leftFallback rightFallback : (input : LabCommon.Domain) → LabCommon.Range input)
    (input : LabCommon.Domain) (state : World) :
    let clip := fun r : (LabCommon.Range input × World) =>
      (if r.2.2.2 then none else some r.1, r.2)
    (clip <$> ((wholeGuard s reserve trackRaw caps leftFallback) input).run state) =ᵈ
      (clip <$> ((wholeGuard s reserve trackRaw caps rightFallback) input).run state) := by
  dsimp only
  rcases state with ⟨cache, counts, flag⟩
  cases flag
  · by_cases hfit : counts +
        Sum.elim (fun _ : A.Domain => (0, 0)) (policy reserve s) input ≤ caps
    · simp only [wholeGuard, QueryImpl.guardQueryBudget, StateT.run_mk, hfit,
        Bool.false_eq_true, ↓reduceIte]
      exact EvalDistEq.rfl
    · simp only [wholeGuard, QueryImpl.guardQueryBudget, StateT.run_mk,
        Bool.false_eq_true, ↓reduceIte, ite_eq_right hfit, map_pure]
      exact EvalDistEq.rfl
  · simp only [wholeGuard, QueryImpl.guardQueryBudget, StateT.run_mk,
      ↓reduceIte, map_pure]
    exact EvalDistEq.rfl


private theorem client_step_clip (s : FIPS205.core.PkSeed) (root : FIPS205.core.Y)
    (reserve trackRaw : Bool) (caps : Nat × Nat)
    (leftFallback rightFallback : (input : LabCommon.Domain) → LabCommon.Range input)
    (input : (LabCommon + Sign).Domain) (state : World) :
    let clip := fun r :
        (((LabCommon + Sign).Range input × Log) ×
          World) =>
      (if r.2.2.2 then none else some r.1, r.2)
    (clip <$> ((clientHandler false s reserve trackRaw caps leftFallback root) input).run.run
      state) =ᵈ
    (clip <$> ((clientHandler true s reserve trackRaw caps rightFallback root) input).run.run
      state) := by
  dsimp only
  rcases input with native | request
  · have h := (guarded_base_clip s reserve trackRaw caps leftFallback rightFallback
        native state).map
      (fun r : Option (LabCommon.Range native) × World =>
        (r.1.map (fun answer => (answer, (∅ : Log))), r.2))
    dsimp only [clientHandler, QueryImpl.add]
    simp only [WriterT.run_mk, StateT.run_map, Functor.map_map]
    change ((fun r : LabCommon.Range native × World =>
      (if r.2.2.2 then none else some (r.1, (∅ : Log)), r.2)) <$>
        (wholeGuard s reserve trackRaw caps leftFallback native).run state) =ᵈ
      ((fun r : LabCommon.Range native × World =>
        (if r.2.2.2 then none else some (r.1, (∅ : Log)), r.2)) <$>
        (wholeGuard s reserve trackRaw caps rightFallback native).run state)
    simp only [Functor.map_map] at h
    convert h using 1 <;> congr 1 <;> funext r <;> cases r.2.2.2 <;> rfl
  · rcases state with ⟨⟨⟨graph, table⟩, metadata⟩, counts, flag⟩
    have h := ((honest_keygen_and_callback s reserve trackRaw
      caps (componentFallback leftFallback) (componentFallback rightFallback) graph table).2.2
        root request metadata counts flag).1.map Prod.snd
    dsimp only [clientHandler, QueryImpl.add]
    simp only [WriterT.run_mk, callback]
    simp only [Functor.map_map] at h
    simpa only [OracleSpec.Range, OracleSpec.add_apply_inr] using h

private theorem client_absorption (useLab : Bool) (s : FIPS205.core.PkSeed)
    (root : FIPS205.core.Y) (reserve trackRaw : Bool) (caps : Nat × Nat)
    (fallback : (input : LabCommon.Domain) → LabCommon.Range input)
    (input : (LabCommon + Sign).Domain) (state : World)
    (hs : state.2.2 = true) :
    ∀ r ∈ support ((clientHandler useLab s reserve trackRaw caps fallback root input).run.run
      state), r.2 = state := by
  intro r hr
  rcases input with native | request
  · have hr' : r = ((fallback native, ∅), state) := by
      simpa [clientHandler, QueryImpl.add, wholeGuard, QueryImpl.guardQueryBudget, hs]
        using hr
    exact congrArg Prod.snd hr'
  · exact guard_frozen s reserve trackRaw caps
      (componentFallback fallback) _ state hs r hr

private theorem logged_client_law {alpha : Type} (s : FIPS205.core.PkSeed)
    (root : FIPS205.core.Y) (reserve trackRaw : Bool) (caps : Nat × Nat)
    (leftFallback rightFallback : (input : LabCommon.Domain) → LabCommon.Range input)
    (program : OracleComp (LabCommon + Sign) alpha)
    (state : World) :
    let clip := fun r : ((alpha × Log) ×
        World) =>
      (if r.2.2.2 then none else some r.1, r.2)
    (clip <$> (simulateQ (clientHandler false s reserve trackRaw caps leftFallback root)
      program).run.run state) =ᵈ
    (clip <$> (simulateQ (clientHandler true s reserve trackRaw caps rightFallback root)
      program).run.run state) := by
  exact OracleComp.evalDistEq_simulateQ_run_writerT_stateT_clip
    (fun current : World => current.2.2)
    (clientHandler false s reserve trackRaw caps leftFallback root)
    (clientHandler true s reserve trackRaw caps rightFallback root)
    (client_step_clip s root reserve trackRaw caps leftFallback rightFallback)
    (client_absorption false s root reserve trackRaw caps leftFallback)
    (client_absorption true s root reserve trackRaw caps rightFallback)
    program state


private theorem guarded_routing_frontend {alpha : Type} (s : FIPS205.core.PkSeed)
    (reserve trackRaw : Bool) (caps : Nat × Nat)
    (fallback : (input : LabCommon.Domain) → LabCommon.Range input)
    (program : OracleComp LabCommon alpha)
    (graph : LabState FIPS205.core) (table : Raw.QueryCache) (metadata : Meta)
    (counts : Nat × Nat) (aborted : Bool) :
    letI : MonadLiftT (OracleComp LabCommon) (StateT PUnit (OracleComp LabCommon)) :=
      ⟨fun action => StateT.lift action⟩
    let forwarder := (QueryImpl.id' LabCommon).liftTarget
      (StateT PUnit (OracleComp LabCommon))
    let guarded := (simulateQ (QueryImpl.guardQueryBudget caps
      (Sum.elim (fun _ : A.Domain => (0, 0)) (policy reserve s)) forwarder fallback)
      program).run (PUnit.unit, (counts, aborted))
    (fun r : ((alpha × (PUnit × Paid)) × Raw.QueryCache) × (LabState FIPS205.core × Meta) =>
      (r.1.1.1, (((r.2.1, r.1.2), r.2.2), r.1.1.2.2))) <$>
      (simulateQ ((eraseObsImpl (Ev := Ev) (slhGraph FIPS205.core s).eagerImpl).extendState
        (aux (spec := Lab) (metadataCost trackRaw s)))
        ((simulateQ (routeLab s) guarded).run table)).run (graph, metadata) =
      (simulateQ (wholeGuard s reserve trackRaw caps fallback) program).run
        (((graph, table), metadata), (counts, aborted)) := by
  dsimp only
  let _ : MonadLiftT (OracleComp LabCommon) (StateT PUnit (OracleComp LabCommon)) :=
    ⟨fun action => StateT.lift action⟩
  let observed := (eraseObsImpl (Ev := Ev) (slhGraph FIPS205.core s).eagerImpl).extendState
    (aux (spec := Lab) (metadataCost trackRaw s))
  let linked := QueryImpl.Stateful.link (routeLab s) observed
  let forwarder := (QueryImpl.id' LabCommon).liftTarget
    (StateT PUnit (OracleComp LabCommon))
  let guarded := (simulateQ (QueryImpl.guardQueryBudget caps
    (Sum.elim (fun _ : A.Domain => (0, 0)) (policy reserve s)) forwarder fallback)
    program).run (PUnit.unit, (counts, aborted))
  have step : ∀ input state, Prod.map id routeState <$> (linked input).run state =
      (wholeObserved s trackRaw input).run (routeState state) := by
    intro input state
    simp [wholeObserved, linked, observed, QueryImpl.Stateful.transportState_apply_run]
  have transport := map_run_simulateQ_eq_of_query_map_eq linked
    (wholeObserved s trackRaw) routeState step guarded (table, (graph, metadata))
  rw [QueryImpl.Stateful.simulateQ_link_run] at transport
  have h := QueryImpl.map_run_simulateQ_guardQueryBudget_free_eq caps
    (Sum.elim (fun _ : A.Domain => (0, 0)) (policy reserve s))
    (wholeObserved s trackRaw) fallback program ((graph, table), metadata) counts aborted
  dsimp only at h
  change (fun result : (alpha × (PUnit × Paid)) × Cache =>
      (result.1.1, result.2, result.1.2.2)) <$>
      (simulateQ (wholeObserved s trackRaw) guarded).run
        (routeState (table, (graph, metadata))) = _ at h
  rw [← transport] at h
  simpa only [wholeGuard, guarded, linked, observed, routeState,
    QueryImpl.Stateful.Frame.linkReshape, QueryImpl.Stateful.Frame.prod,
    Functor.map_map, Function.comp_def, Prod.map, id_eq, Equiv.coe_fn_mk,
    PFunctor.Lens.State.fst_put, PFunctor.Lens.State.snd_put, forwarder] using h


private def nativeCommon : QueryImpl (Lab + O) (OracleComp LabCommon)
  | .inl input => liftM (LabCommon.query (.inl (.inl input)))
  | .inr event => liftM (LabCommon.query (.inr event))

private theorem whole_native_query (s : FIPS205.core.PkSeed)
    (reserve trackRaw : Bool) (caps : Nat × Nat)
    (fallback : (input : LabCommon.Domain) → LabCommon.Range input)
    (input : (Lab + O).Domain) :
    ((wholeGuard s reserve trackRaw caps fallback) ∘ₛ nativeCommon) input =
      eagerGuard s reserve trackRaw caps
        (componentFallback fallback) input := by
  apply StateT.ext
  rintro ⟨⟨⟨graph, table⟩, metadata⟩, counts, flag⟩
  rcases input with native | event <;>
    simp [QueryImpl.compose, nativeCommon, wholeGuard,
      eagerGuard, componentFallback,
      QueryImpl.guardQueryBudget, wholeObserved,
      QueryImpl.Stateful.transportState_apply_run, QueryImpl.Stateful.link_impl_apply_run,
      routeState, routeLab, QueryImpl.add, QueryImpl.extendState, eraseObsImpl,
      QueryImpl.Stateful.Frame.prod, QueryImpl.Stateful.Frame.linkReshape,
      PFunctor.Lens.State.fst_put, PFunctor.Lens.State.snd_put, aux,
      Functor.map_map, Prod.map, id_eq]

private theorem whole_native {alpha : Type} (s : FIPS205.core.PkSeed)
    (reserve trackRaw : Bool) (caps : Nat × Nat)
    (fallback : (input : LabCommon.Domain) → LabCommon.Range input)
    (program : OracleComp (Lab + O) alpha) :
    simulateQ (wholeGuard s reserve trackRaw caps fallback)
      (simulateQ nativeCommon program) =
      simulateQ (eagerGuard s reserve trackRaw caps
        (componentFallback fallback)) program := by
  apply QueryImpl.simulateQ_simulateQ_eq_of_apply
  exact whole_native_query s reserve trackRaw caps fallback


private def liftLabA : QueryImpl Lab (OracleComp A) :=
  fun input => liftM (A.query (.inl input))

private theorem liftLabA_eq : liftLabA =
    (fun input : Lab.Domain =>
      (liftM (A.query (.inl input)) : OracleComp A (Lab.Range input))) := by
  funext input
  rcases input with (((native | typed) | derive) | label) <;> rfl

private theorem common_phase {alpha : Type} (phase : SigningView.Phase)
    (program : OracleComp Lab alpha) :
    simulateQ commonProjection
      (simulateQ (SigningView.Events.phaseImpl A Message phase)
        (simulateQ liftLabA program)) =
      simulateQ nativeCommon (simulateQ projection
        (simulateQ (SigningView.Events.phaseImpl Lab Message phase) program)) := by
  simp only [← QueryImpl.simulateQ_compose]
  apply congrArg (fun impl : QueryImpl Lab (OracleComp LabCommon) => simulateQ impl program)
  funext input
  rcases input with (((native | typed) | derive) | label) <;>
    simp [QueryImpl.compose, SigningView.Events.phaseImpl, QueryImpl.preInsert,
      SigningView.Events.emit, commonProjection, commonEvent, sourceInput,
      projection, originalLabel,
      nativeCommon, liftLabA, QueryImpl.add]

private theorem common_keygen (useLab : Bool) (s : FIPS205.core.PkSeed) :
    simulateQ commonProjection
      (SigningView.Events.viewWithEvents (commonView useLab s)).keygen =
      simulateQ nativeCommon (simulateQ projection
        (SigningView.Events.viewWithEvents
          (partialView useLab s)).keygen) := by
  simp only [commonView, SigningView.Events.viewWithEvents,
    SigningView.map_keygen]
  rw [← liftLabA_eq]
  exact common_phase .keygen (partialView useLab s).keygen

private theorem common_sign (useLab : Bool) (s : FIPS205.core.PkSeed)
    (pk sk : PK) (request : Message) :
    simulateQ commonProjection
      ((SigningView.Events.viewWithEvents (commonView useLab s)).sign pk sk request) =
      simulateQ nativeCommon (simulateQ projection
        ((SigningView.Events.viewWithEvents
          (partialView useLab s)).sign pk sk request)) := by
  simp only [SigningView.Events.viewWithEvents, simulateQ_bind]
  have hemit : simulateQ commonProjection (SigningView.Events.emit A Message
      (.signingAttempt request)) =
      simulateQ nativeCommon (simulateQ projection
        (SigningView.Events.emit Lab Message (.signingAttempt request))) := by
    simp [SigningView.Events.emit, commonProjection, commonEvent,
      projection, nativeCommon, QueryImpl.add]
  rw [hemit]
  apply bind_congr
  intro _
  simp only [commonView, SigningView.map_sign]
  rw [← liftLabA_eq]
  exact common_phase .signer ((partialView useLab s).sign pk sk request)

private theorem client_native (useLab : Bool) (s : FIPS205.core.PkSeed)
    (root : FIPS205.core.Y) (reserve trackRaw : Bool) (caps : Nat × Nat)
    (fallback : (input : LabCommon.Domain) → LabCommon.Range input) :
    (clientHandler useLab s reserve trackRaw caps fallback root) ∘ₛ liftBase =
      (wholeGuard s reserve trackRaw caps fallback).liftTarget
        (WriterT Log
          (StateT World ProbComp)) := by
  funext input
  simp only [QueryImpl.compose, liftBase, simulateQ_spec_query, clientHandler,
    QueryImpl.add, QueryImpl.liftTarget_apply]
  apply WriterT.ext
  apply StateT.ext
  intro state
  simp [StateT.run_map]

private theorem client_main {alpha : Type} (useLab : Bool) (s : FIPS205.core.PkSeed)
    (root : FIPS205.core.Y) (reserve trackRaw : Bool) (caps : Nat × Nat)
    (fallback : (input : LabCommon.Domain) → LabCommon.Range input)
    (body : OracleComp (SigningView.Events.Spec A Message + Sign) alpha) :
    simulateQ (wholeGuard s reserve trackRaw caps fallback)
      (simulateQ commonProjection
        ((SigningView.Events.viewWithEvents (commonView useLab s)).runWithSigningOracle
          ⟨s, root⟩ ⟨s, root⟩ body)) =
      (simulateQ (clientHandler useLab s reserve trackRaw caps fallback root)
        (simulateQ liftClient body)).run := by
  let red : QueryImpl (SigningView.Events.Spec A Message + Sign)
      (WriterT Log
        (OracleComp (SigningView.Events.Spec A Message))) :=
    QueryImpl.add (spec₁ := SigningView.Events.Spec A Message) (spec₂ := Sign)
      (SigningView.Events.Spec A Message).passthrough
      ((SigningView.Events.viewWithEvents (commonView useLab s)).signingOracle
        ⟨s, root⟩ ⟨s, root⟩)
  let impl := (wholeGuard s reserve trackRaw caps fallback) ∘ₛ commonProjection
  let game := (clientHandler useLab s reserve trackRaw caps fallback root) ∘ₛ liftClient
  have step : ∀ input, simulateQ impl ((red input).run) = (game input).run := by
    intro input
    rcases input with native | request
    · dsimp only [game, liftClient, QueryImpl.compose, QueryImpl.add]
      rw [← QueryImpl.simulateQ_compose, client_native,
        writerT_run_simulateQ_liftTarget]
      simp [red, impl, QueryImpl.add]
    · simp only [red, impl, game, liftClient, QueryImpl.compose, QueryImpl.add,
        simulateQ_spec_query, SigningView.signingOracle, WriterT.run_mk,
        clientHandler, callback,
        QueryImpl.run_withLogging_apply, simulateQ_bind, simulateQ_pure]
      rw [QueryImpl.simulateQ_compose, common_sign, whole_native]
  have h := simulateQ_WriterT_compose red impl game step body
  simpa only [SigningView.runWithSigningOracle, red, impl, game,
    QueryImpl.simulateQ_compose, QueryImpl.passthrough_add,
    ← QueryImpl.add_eq_hAdd] using h

private theorem common_keygen_run (useLab : Bool) (s : FIPS205.core.PkSeed)
    (reserve trackRaw : Bool) (caps : Nat × Nat)
    (fallback : (input : LabCommon.Domain) → LabCommon.Range input) :
    simulateQ (wholeGuard s reserve trackRaw caps fallback)
      (simulateQ commonProjection
        (SigningView.Events.viewWithEvents (commonView useLab s)).keygen) =
      simulateQ (eagerGuard s reserve trackRaw caps
        (componentFallback fallback))
        (simulateQ projection
          (SigningView.Events.viewWithEvents
            (partialView useLab s)).keygen) := by
  rw [common_keygen, whole_native]


private def nativeIn : DNative.Domain → A.Domain
  | .inl native => .inl (.inl native)
  | .inr raw => .inr raw

private def nativeEmbed : QueryImpl DNative (OracleComp A)
  | .inl native => liftM (A.query (.inl (.inl native)))
  | .inr raw => liftM (A.query (.inr raw))

private def markedEmbed :
    QueryImpl (SigningView.Events.Spec DNative Message)
      (OracleComp (SigningView.Events.Spec A Message))
  | .inl (.inl native) => liftM ((SigningView.Events.Spec A Message).query
      (.inl (.inl (.inl native))))
  | .inl (.inr raw) => liftM ((SigningView.Events.Spec A Message).query (.inl (.inr raw)))
  | .inr (.signingAttempt request) => liftM ((SigningView.Events.Spec A Message).query
      (.inr (.signingAttempt request)))
  | .inr (.ambient phase input) => liftM ((SigningView.Events.Spec A Message).query
      (.inr (.ambient phase (nativeIn input))))

/- The exact finite observation square: one native input is one native output;
   an ambient marker remains one ambient marker. -/
private theorem phase_embed {alpha : Type} (phase : SigningView.Phase)
    (body : OracleComp DNative alpha) :
    simulateQ markedEmbed
      (simulateQ (SigningView.Events.phaseImpl DNative Message phase) body) =
    simulateQ (SigningView.Events.phaseImpl A Message phase)
      (simulateQ nativeEmbed body) := by
  simp only [← QueryImpl.simulateQ_compose]
  apply congrArg (fun impl : QueryImpl DNative
    (OracleComp (SigningView.Events.Spec A Message)) => simulateQ impl body)
  funext input
  rcases input with native | raw <;>
    simp [QueryImpl.compose, SigningView.Events.phaseImpl, QueryImpl.preInsert,
      SigningView.Events.emit, nativeEmbed, markedEmbed, nativeIn]

/- Original-source markers agree on both sides: private derivations are silent,
   and each signing attempt emits one marker. -/
private theorem projection_embed :
    embedD ∘ₛ sparseProjection = commonProjection ∘ₛ markedEmbed := by
  funext input
  rcases input with native | event
  · rcases native with native | raw
    · rcases native with native | derive
      · rcases native with sample | typed <;>
          simp [QueryImpl.compose, sparseProjection, commonProjection, QueryImpl.add,
            QueryImpl.ofLift, embedD, markedEmbed, OracleComp.liftM_eq_liftM_liftM,
            OracleSpec.query, OracleQuery.cont, PFunctor.Obj.fst, PFunctor.Obj.snd]
        all_goals simp [OracleQuery.mk, PFunctor.Obj.mk]
      · simp [QueryImpl.compose, sparseProjection, commonProjection, QueryImpl.add,
          QueryImpl.ofLift, embedD, markedEmbed, OracleComp.liftM_eq_liftM_liftM,
          OracleSpec.query, OracleQuery.cont, PFunctor.Obj.fst, PFunctor.Obj.snd]
        simp [OracleQuery.mk, PFunctor.Obj.mk]
    · simp [QueryImpl.compose, sparseProjection, commonProjection, QueryImpl.add,
        QueryImpl.ofLift, embedD, markedEmbed, OracleComp.liftM_eq_liftM_liftM,
        OracleSpec.query, OracleQuery.cont, PFunctor.Obj.fst, PFunctor.Obj.snd]
      simp [OracleQuery.mk, PFunctor.Obj.mk]
  · cases event with
    | signingAttempt request =>
      simp [QueryImpl.compose, sparseProjection, commonProjection, QueryImpl.add,
        embedD, markedEmbed, commonEvent]
    | ambient phase native =>
      rcases native with native | raw
      · rcases native with native | derive
        · rcases native with sample | typed <;>
            simp [QueryImpl.compose, sparseProjection, commonProjection, QueryImpl.add,
              embedD, markedEmbed, nativeIn, commonEvent, nativeObservation, sourceInput]
        · simp [QueryImpl.compose, sparseProjection, commonProjection, QueryImpl.add,
            markedEmbed, nativeIn, commonEvent, nativeObservation]
      · simp [QueryImpl.compose, sparseProjection, commonProjection, QueryImpl.add,
          embedD, markedEmbed, nativeIn, commonEvent, nativeObservation]

private theorem marked_view_embed
    (view : SigningView (OracleComp DNative) Message PK PK (List Byte) (Option (List Byte))) :
    (SigningView.Events.viewWithEvents view).map (simulateQ' markedEmbed) =
      SigningView.Events.viewWithEvents (view.map (simulateQ' nativeEmbed)) := by
  unfold SigningView.map SigningView.Events.viewWithEvents
  congr 1
  · exact phase_embed .keygen view.keygen
  · funext pk sk request
    simp only [simulateQ_bind]
    rw [phase_embed]
    simp [SigningView.Events.emit, markedEmbed]
  · funext pk request wire
    exact phase_embed .verification (view.verify pk request wire)

private theorem marked_main_embed
    (main : PK → OracleComp (DNative + Sign) (Message × List Byte)) (pk : PK) :
    simulateQ (SigningView.mapClient markedEmbed)
      (SigningView.Events.mainWithEvents main pk) =
    SigningView.Events.mainWithEvents
      (fun key => simulateQ (SigningView.mapClient nativeEmbed) (main key)) pk := by
  simp only [SigningView.Events.mainWithEvents, ← QueryImpl.simulateQ_compose]
  congr 1
  funext input
  rcases input with native | request
  · rcases native with native | raw <;>
      simp [QueryImpl.compose, QueryImpl.add, SigningView.mapClient,
        SigningView.Events.phaseImpl, QueryImpl.preInsert, SigningView.Events.emit,
        nativeEmbed, markedEmbed, nativeIn]
  · simp [QueryImpl.compose, QueryImpl.add, SigningView.mapClient]

/- Unmarked logged-service interpretation composes with the concrete one-query
   marked inclusion. -/
private theorem full_experiment_embed
    (view : SigningView (OracleComp DNative) Message PK PK (List Byte) (Option (List Byte)))
    (main : PK → OracleComp (DNative + Sign) (Message × List Byte)) :
    simulateQ markedEmbed (SigningView.Events.fullExperiment view main) =
      SigningView.Events.fullExperiment (view.map (simulateQ' nativeEmbed))
        (fun key => simulateQ (SigningView.mapClient nativeEmbed) (main key)) := by
  have hkeygen :
      simulateQ markedEmbed (SigningView.Events.viewWithEvents view).keygen =
        (SigningView.Events.viewWithEvents (view.map (simulateQ' nativeEmbed))).keygen := by
    simpa only [SigningView.map_keygen, simulateQ'_apply] using
      congrArg SigningView.keygen (marked_view_embed view)
  simp only [SigningView.Events.fullExperiment, simulateQ_bind, simulateQ_pure]
  rw [hkeygen]
  apply bind_congr
  intro keys
  rw [SigningView.simulateQ_runWithSigningOracle, marked_view_embed, marked_main_embed]
  apply bind_congr
  intro result
  have hverify :
      simulateQ markedEmbed
        ((SigningView.Events.viewWithEvents view).verify keys.1 result.1.1 result.1.2) =
      (SigningView.Events.viewWithEvents (view.map (simulateQ' nativeEmbed))).verify
        keys.1 result.1.1 result.1.2 := by
    simpa only [SigningView.map_verify, simulateQ'_apply] using
      congrArg (fun mappedView : SigningView (OracleComp (SigningView.Events.Spec A Message))
        Message PK PK (List Byte) (Option (List Byte)) =>
          mappedView.verify keys.1 result.1.1 result.1.2) (marked_view_embed view)
  rw [hverify]

/- This is just composition of the three ONE-query inclusions:
   deriveSpec→DNative→A equals deriveSpec→Lab→A. No scheme internals. -/
private theorem derive_program_embed {alpha : Type}
    (body : OracleComp (deriveSpec FIPS205.core) alpha) :
    simulateQ nativeEmbed
      (simulateQ (QueryImpl.ofLift (deriveSpec FIPS205.core) (OracleComp DNative)) body) =
    simulateQ (fun input : Lab.Domain =>
      (liftM (A.query (.inl input)) : OracleComp A (Lab.Range input)))
      ((labLiftHom FIPS205.core).toMonadHom body) := by
  change simulateQ nativeEmbed (simulateQ _ body) = simulateQ _ (simulateQ _ body)
  rw [← QueryImpl.simulateQ_compose, ← QueryImpl.simulateQ_compose]
  congr 1
  funext input
  rcases input with native | derive <;>
    simp [QueryImpl.compose, QueryImpl.ofLift, nativeEmbed,
      OracleComp.liftM_eq_liftM_liftM, OracleSpec.query] <;> rfl

private theorem raw_main_embed
    (adv : Game.Adversary FIPS205.Answer PK) (pk : PK) :
    simulateQ (SigningView.mapClient nativeEmbed) (rawMainD adv pk) =
      commonMain adv pk := by
  simp only [rawMainD, commonMain, ← QueryImpl.simulateQ_compose]
  congr 1
  funext input
  rcases input with (sample | raw) | request <;>
    simp [QueryImpl.compose, QueryImpl.add, SigningView.mapClient, nativeEmbed,
      QueryImpl.ofLift, OracleComp.liftM_eq_liftM_liftM, OracleSpec.query]
  rfl

private theorem unresolved_view_embed (s : FIPS205.core.PkSeed) :
    (unresolvedView s).map (simulateQ' nativeEmbed) = commonView false s := by
  unfold unresolvedView commonView partialView
  simp only [Bool.false_eq_true, ↓reduceIte]
  unfold SigningView.map SigningView.rejectingEncoding
  congr 1
  · simp only [SignatureAlg.map_keygen]
    exact derive_program_embed _
  · funext pk sk request
    cases frame : (External.encodePureMessage request.context request.message).toOption with
    | none => simp [SigningView.Encoding.sign, frame]
    | some message =>
      simp only [SigningView.Encoding.sign, frame, SignatureAlg.map_sign,
        simulateQ_map]
      rw [derive_program_embed]
  · funext pk request wire
    cases frame : (External.encodePureMessage request.context request.message).toOption with
    | none => simp [SigningView.Encoding.verify, frame]
    | some message =>
      cases decoder : (SLHDSA.decodeSignature FIPS205.params
          (SLHDSA.Concrete.shakeWireCodec FIPS205.params.params) wire).toOption with
      | none => simp [SigningView.Encoding.verify, frame, decoder]
      | some signature =>
        simp only [SigningView.Encoding.verify, frame, decoder, SignatureAlg.map_verify]
        exact derive_program_embed _

private theorem source_free_square (s : FIPS205.core.PkSeed)
    (adv : Game.Adversary FIPS205.Answer PK) :
    simulateQ embedD (fixedSource s adv) = commonSource false s adv := by
  unfold fixedSource commonSource
  rw [← QueryImpl.simulateQ_compose, projection_embed,
    QueryImpl.simulateQ_compose, full_experiment_embed, unresolved_view_embed]
  exact congrArg (fun main : PK → OracleComp (A + Sign) (Message × List Byte) =>
    simulateQ commonProjection
      (SigningView.Events.fullExperiment (commonView false s) main))
    (funext (fun pk => raw_main_embed adv pk))

private theorem common_marked_verify (useLab : Bool) (s : FIPS205.core.PkSeed)
    (pk : PK) (request : Message) (wire : List Byte) :
    (SigningView.Events.viewWithEvents (commonView useLab s)).verify pk request wire =
      (SigningView.Events.viewWithEvents (commonView true s)).verify pk request wire := by
  cases useLab
  · simp only [SigningView.Events.viewWithEvents, common_verify_eq]
  · rfl

private theorem client_after (useLab : Bool) (s : FIPS205.core.PkSeed)
    (root : FIPS205.core.Y) (reserve trackRaw : Bool) (caps : Nat × Nat)
    (fallback : (input : LabCommon.Domain) → LabCommon.Range input)
    (adv : Game.Adversary FIPS205.Answer PK) :
    (simulateQ (clientHandler useLab s reserve trackRaw caps fallback root)
      (afterKeygen s adv ⟨s, root⟩)).run =
    (do
      let result ← simulateQ (wholeGuard s reserve trackRaw caps fallback)
        (simulateQ commonProjection
          ((SigningView.Events.viewWithEvents (commonView useLab s)).runWithSigningOracle
            ⟨s, root⟩ ⟨s, root⟩
            (SigningView.Events.mainWithEvents (commonMain adv) ⟨s, root⟩)))
      let verified ← simulateQ (wholeGuard s reserve trackRaw caps fallback)
        (simulateQ commonProjection
          ((SigningView.Events.viewWithEvents (commonView true s)).verify
            ⟨s, root⟩ result.1.1 result.1.2))
      pure ((result.1, verified), result.2)) := by
  have native {alpha : Type} (program : OracleComp LabCommon alpha) :
      (simulateQ (clientHandler useLab s reserve trackRaw caps fallback root)
        (simulateQ liftBase program)).run =
        (fun value => (value, (∅ : Log))) <$>
          simulateQ (wholeGuard s reserve trackRaw caps fallback) program := by
    rw [← QueryImpl.simulateQ_compose, client_native, writerT_run_simulateQ_liftTarget]
  simp only [afterKeygen, simulateQ_bind, simulateQ_pure, WriterT.run_bind',
    WriterT.run_pure', native, ← client_main, bind_map_left, map_pure]
  simp [Prod.map]


private def jointObservation (r : Full × World) :=
  (r.1.1, (if r.2.2.2 then none else some r.1.2),
    r.2.1.1.2, r.2.1.2, r.2.2, r.2.1.1.1)

private theorem common_continuation (useLab : Bool) (s : FIPS205.core.PkSeed)
    (root : FIPS205.core.Y) (reserve trackRaw : Bool) (caps : Nat × Nat)
    (fallback : (input : LabCommon.Domain) → LabCommon.Range input)
    (adv : Game.Adversary FIPS205.Answer PK) :
    simulateQ (wholeGuard s reserve trackRaw caps fallback)
      (simulateQ commonProjection (do
        let result ← (SigningView.Events.viewWithEvents (commonView useLab s)).runWithSigningOracle
          (⟨s, root⟩ : PK) (⟨s, root⟩ : PK)
          (SigningView.Events.mainWithEvents (commonMain adv) (⟨s, root⟩ : PK))
        let verified ← (SigningView.Events.viewWithEvents (commonView useLab s)).verify
          (⟨s, root⟩ : PK) result.1.1 result.1.2
        pure (((⟨s, root⟩ : PK), (⟨s, root⟩ : PK)),
          (⟨result.1, result.2, verified⟩ : RawOutcome)))) =
      (fun r : ((Message × List Byte) × Bool) × Log =>
        (((⟨s, root⟩ : PK), (⟨s, root⟩ : PK)), (⟨r.1.1, r.2, r.1.2⟩ : RawOutcome))) <$>
        (simulateQ (clientHandler useLab s reserve trackRaw caps fallback root)
          (afterKeygen s adv (⟨s, root⟩ : PK))).run := by
  rw [client_after]
  simp only [simulateQ_bind, simulateQ_pure, common_marked_verify,
    map_bind, map_pure]

private theorem common_whole_law (s : FIPS205.core.PkSeed)
    (adv : Game.Adversary FIPS205.Answer PK) (reserve trackRaw : Bool)
    (caps : Nat × Nat)
    (leftFallback rightFallback : (input : LabCommon.Domain) → LabCommon.Range input) :
    let initial : World :=
      ((((∅, ∅), ∅), (0, .keygen)), ((0, 0), false))
    (jointObservation <$> (simulateQ (wholeGuard s reserve trackRaw caps leftFallback)
      (commonSource false s adv)).run initial) =ᵈ
    (jointObservation <$> (simulateQ (wholeGuard s reserve trackRaw caps rightFallback)
      (commonSource true s adv)).run initial) := by
  dsimp only
  have hk := honest_keygen_and_callback s reserve trackRaw caps
    (componentFallback leftFallback) (componentFallback rightFallback) (∅, ∅) ∅
  unfold commonSource SigningView.Events.fullExperiment
  conv_lhs => rw [simulateQ_bind, simulateQ_bind]
  conv_rhs => rw [simulateQ_bind, simulateQ_bind]
  simp only [StateT.run_bind, map_bind, common_keygen_run]
  refine (hk.1.bind_congr (fun result => EvalDistEq.rfl)).trans ?_
  apply OracleComp.EvalDistEq.bind_congr_of_support
  intro result hr
  obtain ⟨hsk, hseed, _, _, _⟩ := hk.2.1 result hr
  rcases result with ⟨⟨⟨seed, root⟩, sk⟩, state⟩
  dsimp only at hsk hseed
  subst seed
  subst sk
  rw [common_continuation, common_continuation]
  simp only [StateT.run_map, Functor.map_map]
  have h := (logged_client_law s root reserve trackRaw caps
    leftFallback rightFallback (afterKeygen s adv (⟨s, root⟩ : PK)) state).map
      (fun r : Option ((((Message × List Byte) × Bool) × Log)) ×
          World =>
        (((⟨s, root⟩ : PK), (⟨s, root⟩ : PK)),
          r.1.map (fun body => (⟨body.1.1, body.2, body.1.2⟩ : RawOutcome)),
          r.2.1.1.2, r.2.1.2, r.2.2, r.2.1.1.1))
  simp only [Functor.map_map] at h
  convert h using 1 <;> congr 1 <;> funext r <;>
    cases hflag : r.2.2.2 <;> simp [jointObservation, hflag]


/-- The actual guarded derivation source and lab source have equal complete eager observations. -/
theorem guarded_eager_lab_stage :
  ∀ (s : FIPS205.core.PkSeed) (adv : Game.Adversary FIPS205.Answer PK)
    (reserve trackRaw : Bool) (caps : Nat × Nat)
    (fallbackLab : (input : LabCommon.Domain) → LabCommon.Range input),
    letI : MonadLiftT (OracleComp DCommon) (StateT PUnit (OracleComp DCommon)) :=
      ⟨fun action => StateT.lift action⟩
    let forwarder : QueryImpl DCommon (StateT PUnit (OracleComp DCommon)) :=
      (QueryImpl.id' DCommon).liftTarget (StateT PUnit (OracleComp DCommon))
    let fixedGuarded : OracleComp DCommon (Full × (PUnit × Paid)) :=
      (simulateQ (QueryImpl.guardQueryBudget caps
        (Sum.elim (fun _ : DNative.Domain => (0, 0)) (policy reserve s))
        forwarder (deriveFallback s)) (fixedSource s adv)).run
          (PUnit.unit, ((0, 0), false))
    let freeProgram : OracleComp (deriveSpec FIPS205.core)
        (((Full × (PUnit × Paid)) × Raw.QueryCache) × Meta) :=
      (simulateQ (observeD s trackRaw)
        ((simulateQ (routeD s) fixedGuarded).run ∅)).run (0, .keygen)
    let honest := (simulateQ (slhGraph FIPS205.core s).eagerImpl
      (liftComp freeProgram (labSpec FIPS205.core))).run (∅, ∅)
    let labHandler := (eraseObsImpl (Ev := Ev) (slhGraph FIPS205.core s).eagerImpl).extendState
      (aux (spec := Lab) (metadataCost trackRaw s))
    let lab := (simulateQ labHandler
      (guardedRoutedSource s adv reserve caps fallbackLab)).run ((∅, ∅), (0, .keygen))
    let honestObservation := fun result :
        ((((Full × (PUnit × Paid)) × Raw.QueryCache) × Meta) ×
          LabState FIPS205.core) =>
      let full := result.1.1.1.1
      let paid := result.1.1.1.2.2
      (full.1, (if paid.2 then none else some full.2),
        result.1.1.2, result.1.2, paid, result.2)
    let labObservation := fun result :
        (((Full × (PUnit × Paid)) × Raw.QueryCache) ×
          (LabState FIPS205.core × Meta)) =>
      let full := result.1.1.1
      let paid := result.1.1.2.2
      (full.1, (if paid.2 then none else some full.2),
        result.1.2, result.2.2, paid, result.2.1)
    (honestObservation <$> honest) =ᵈ (labObservation <$> lab) := by
  intro s adv reserve trackRaw caps fallbackLab
  dsimp only
  rw [observe_free_square, route_free_square,
    (guard_free_square s reserve caps fallbackLab), source_free_square, guardedRoutedSource]
  let _ : MonadLiftT (OracleComp LabCommon) (StateT PUnit (OracleComp LabCommon)) :=
    ⟨fun action => StateT.lift action⟩
  let forwarder := (QueryImpl.id' LabCommon).liftTarget
    (StateT PUnit (OracleComp LabCommon))
  let guarded := (simulateQ (QueryImpl.guardQueryBudget caps
    (Sum.elim (fun _ : A.Domain => (0, 0)) (policy reserve s)) forwarder
    (honestFallback s fallbackLab)) (commonSource false s adv)).run
      (PUnit.unit, ((0, 0), false))
  have ho := observe_eager_square s trackRaw ((simulateQ (routeLab s) guarded).run ∅)
    (0, .keygen) (∅, ∅)
  have hl := guarded_routing_frontend s reserve trackRaw caps
    (honestFallback s fallbackLab) (commonSource false s adv) (∅, ∅) ∅
    (0, .keygen) (0, 0) false
  have hr := guarded_routing_frontend s reserve trackRaw caps
    fallbackLab (commonSource true s adv) (∅, ∅) ∅ (0, .keygen) (0, 0) false
  dsimp only at hl hr
  have h := common_whole_law s adv reserve trackRaw caps
    (honestFallback s fallbackLab) fallbackLab
  dsimp only at h
  rw [← hl, ← hr] at h
  change (jointObservation <$> (_ <$> _)) =ᵈ _ at h
  rw [← ho] at h
  simpa only [jointObservation, guarded, forwarder, Functor.map_map,
    Function.comp_def] using h

end SLHDSA.SHAKE128s.Bridge.SharedExperiment.Guarded
