/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import HashSig.SLHDSA.SHAKE128s.Statement.Game
public import VCVio.CryptoFoundations.SignatureAlg.RomQueryCount
public import VCVio.OracleComp.QueryTracking.WriterCost.Map
public import VCVio.OracleComp.QueryTracking.QueryBound.Simulation

/-!
# Pathwise budgets of the counted signature game

The adversary's own hash and signing queries determine its phase counters. Internal signer
queries remain beneath those counters, and every returned signing answer extends the log.
-/

public section

open OracleComp OracleSpec SignatureAlg

namespace SLHDSA.SHAKE128s.Game

namespace Projection

open Counted


/-- Projection to the three client counters preserves additive accumulation. -/
def phaseCountsHom : SourceCounts →+ Counts where
  toFun := phaseCounts
  map_zero' := by funext kind; cases kind <;> rfl
  map_add' left right := by funext kind; cases kind <;> rfl

/-- Projection commutes with the complete shared component observer. -/
theorem costed_map {Output α : Type} (phase : SigningView.Phase)
    (body : OracleComp (World Output) α) :
    AddWriterT.mapCostHom phaseCountsHom (SigningView.costed sourcePolicy phase body) =
      SigningView.costed phasePolicy phase body := by
  exact QueryImpl.mapCostHom_simulateQ_withAddCost phaseCountsHom
    (QueryImpl.id' (World Output)) (fun input => sourcePolicy (.ambient phase input)) body

/-- The declared phase projection retains the complete chronological reply log. -/
def phaseMorphism {Output : Type} :
    SigningView.LoggedCostM (World Output) Message (Option Bytes) SourceCounts →ᵐ
      SigningView.LoggedCostM (World Output) Message (Option Bytes) Counts :=
  WriterT.mapBaseAppendHom (AddWriterT.mapCostHom phaseCountsHom)

/-- Projection retains each direct query and each actual signing reply. -/
theorem handler_map {Output : Type}
    (signer : Message → OracleComp (World Output) (Option Bytes))
    (input : (World Output + SigningSpec).Domain) :
    phaseMorphism (SigningView.countedHandlerUsing sourcePolicy signer input) =
      SigningView.countedHandlerUsing phasePolicy signer input := by
  cases input with
  | inl input =>
    apply WriterT.ext
    simp [phaseMorphism, SigningView.countedHandlerUsing, AddWriterT.mapCostHom,
      WriterT.mapOutputHom, QueryImpl.withAddCost_apply, phaseCountsHom, phasePolicy,
      Functor.map_map]
    rfl
  | inr request =>
    apply WriterT.ext
    simp only [phaseMorphism, SigningView.countedHandlerUsing, QueryImpl.add_apply_inr,
      WriterT.run_mapBaseAppendHom, SigningView.countedSigningOracleUsing_run,
      MonadHom.mmap_bind, MonadHom.mmap_pure, costed_map]
    congr 1

/-- The complete client phase projects its cost while retaining the actual result and reply log. -/
theorem phase_map {Output α : Type}
    (signer : Message → OracleComp (World Output) (Option Bytes))
    (body : OracleComp (World Output + SigningSpec) α) :
    AddWriterT.mapCostHom phaseCountsHom
      (SigningView.countedPhaseUsing sourcePolicy signer body) =
        SigningView.countedPhaseUsing phasePolicy signer body := by
  have equality : phaseMorphism
      (simulateQ (SigningView.countedHandlerUsing sourcePolicy signer) body) =
        simulateQ (SigningView.countedHandlerUsing phasePolicy signer) body := by
    calc
      _ = simulateQ (fun input => phaseMorphism
          (SigningView.countedHandlerUsing sourcePolicy signer input)) body :=
        PFunctor.FreeM.liftM_natural _ (phaseMorphism (Output := Output)) body
      _ = _ := by simp only [handler_map]
  have observed := congrArg (fun program => program.run) equality
  simpa only [phaseMorphism, WriterT.run_mapBaseAppendHom,
    SigningView.countedPhaseUsing] using observed

/-- The same cost projection commutes with the whole client-and-verifier suffix. -/
theorem suffix_map {Output PK SK : Type}
    (view : SigningView (OracleComp (World Output)) Message PK SK Bytes (Option Bytes))
    (pk : PK) (sk : SK)
    (main : PK → OracleComp (World Output + SigningSpec) (Message × Bytes)) :
    AddWriterT.mapCostHom phaseCountsHom
      (SigningView.countedAfterKeygen sourcePolicy view pk sk main) =
        SigningView.countedAfterKeygen phasePolicy view pk sk main := by
  simp only [SigningView.countedAfterKeygen, MonadHom.mmap_bind, MonadHom.mmap_pure,
    SigningView.countedPhase, phase_map, costed_map]

end Projection

variable {Output PK SK α β : Type}

/-- A pure adversary result adds no count and retains the complete signing prefix. -/
@[simp] theorem runPhase_pure (scheme : ExternalScheme Output PK SK) (sk : SK)
    (x : α) (signed : SigningLog) :
    runPhase scheme sk (pure x) signed = pure ((x, 0), signed) := by
  simp [runPhase, Counted.runPhase, SignatureAlg.SigningView.countedPhaseUsing]

/-- Sequencing adds the actual phase counters and threads the complete signing log. -/
theorem runPhase_bind (scheme : ExternalScheme Output PK SK) (sk : SK)
    (program : OracleComp (World Output + SigningSpec) α)
    (next : α → OracleComp (World Output + SigningSpec) β) (signed : SigningLog) :
    runPhase scheme sk (program >>= next) signed = do
      let ((x, firstCounts), intermediate) ← runPhase scheme sk program signed
      let ((y, lastCounts), finalLog) ← runPhase scheme sk (next x) intermediate
      return ((y, firstCounts + lastCounts), finalLog) := by
  simp [runPhase, Counted.runPhase, SignatureAlg.SigningView.countedPhaseUsing_bind,
    AddWriterT.runAdd_bind, Prod.map, List.append_assoc]

/-- An ambient call leaves the signing log intact and charges only its direct hash cost. -/
theorem runPhase_query_world (scheme : ExternalScheme Output PK SK) (sk : SK)
    (input : (World Output).Domain) (signed : SigningLog) :
    runPhase scheme sk (liftM ((World Output + SigningSpec).query (Sum.inl input))) signed =
      (fun answer => ((answer, Counts.single .hash (hashCost input)), signed)) <$>
        (query input : OracleComp (World Output) _) := by
  simp [runPhase, Counted.runPhase, SignatureAlg.SigningView.countedPhaseUsing,
    SignatureAlg.SigningView.countedHandlerUsing, Counted.phasePolicy,
    Counted.sourcePolicy, Counted.sourceKind, QueryImpl.withAddCost_apply, Counts.single]

/-- Every completed signing call charges one request and appends its answer, including `none`. -/
theorem runPhase_query_sign (scheme : ExternalScheme Output PK SK) (sk : SK)
    (request : Message) (signed : SigningLog) :
    runPhase scheme sk (liftM ((World Output + SigningSpec).query (Sum.inr request))) signed =
      (fun answer => ((answer, Counts.single .signing 1), signed ++ [⟨request, answer⟩])) <$>
        scheme.sign sk request := by
  unfold runPhase
  rw [SigningView.countedPhaseUsing_signingQuery]
  simp [Counted.costed_phasePolicy_signer, Counted.phasePolicy, Counted.sourcePolicy,
    AddWriterT.runAdd_bind, Prod.map]

/-- Forwarding an ambient call before its continuation adds precisely its direct hash charge. -/
theorem runPhase_query_bind_world (scheme : ExternalScheme Output PK SK) (sk : SK)
    (input : (World Output).Domain)
    (next : (World Output).Range input → OracleComp (World Output + SigningSpec) α)
    (signed : SigningLog) :
    runPhase scheme sk
        (liftM ((World Output + SigningSpec).query (Sum.inl input)) >>= next) signed = do
      let answer ← query input
      let ((value, counts), finalLog) ← runPhase scheme sk (next answer) signed
      return ((value, Counts.single .hash (hashCost input) + counts), finalLog) := by
  rw [runPhase_bind, runPhase_query_world]
  simp only [bind_map_left]

/-- A signing request's continuation starts after retaining its complete returned log entry. -/
theorem runPhase_query_bind_sign (scheme : ExternalScheme Output PK SK) (sk : SK)
    (request : Message) (next : Option Bytes → OracleComp (World Output + SigningSpec) α)
    (signed : SigningLog) :
    runPhase scheme sk
        (liftM ((World Output + SigningSpec).query (Sum.inr request)) >>= next) signed = do
      let answer ← scheme.sign sk request
      let ((value, counts), finalLog) ←
        runPhase scheme sk (next answer) (signed ++ [⟨request, answer⟩])
      return ((value, Counts.single .signing 1 + counts), finalLog) := by
  rw [runPhase_bind, runPhase_query_sign]
  simp only [bind_map_left]

/-- Syntactic adversary budgets bound the actual phase counters on every response path. The
entire old signing prefix is retained, and each new log entry accounts for exactly one charge. -/
theorem runPhase_bounds (scheme : ExternalScheme Output PK SK) (sk : SK)
    (program : OracleComp (World Output + SigningSpec) α) (signed : SigningLog)
    {qh qs : Nat}
    (hh : IsQueryBoundP program
      (SignatureAlg.IsHashQuery (hs := RandomOracleModel.HashSpec Bytes Output)
        (M := Message) (S := Option Bytes)) qh)
    (hs : IsQueryBoundP program
      (SignatureAlg.IsSignQuery (hs := RandomOracleModel.HashSpec Bytes Output)
        (M := Message) (S := Option Bytes)) qs)
    {z : (α × Counts) × SigningLog} (hz : z ∈ support (runPhase scheme sk program signed)) :
    z.1.2 .hash ≤ qh ∧ z.1.2 .signing ≤ qs ∧ z.1.2 .verification = 0 ∧
      ∃ suffix, z.2 = signed ++ suffix ∧ suffix.length = z.1.2 .signing := by
  induction program using OracleComp.inductionOn generalizing qh qs signed z with
  | pure value =>
      rw [runPhase_pure] at hz
      have hz' := eq_of_mem_support_pure _ hz
      subst z
      exact ⟨Nat.zero_le _, Nat.zero_le _, rfl, [], by simp, rfl⟩
  | query_bind input next ih =>
      rw [isQueryBoundP_query_bind_iff] at hh hs
      rcases input with (privateSample | hashInput) | request
      · rw [runPhase_query_bind_world] at hz
        obtain ⟨answer, _, hz⟩ := mem_support_bind_peel _ _ hz
        obtain ⟨⟨⟨value, counts⟩, finalLog⟩, hphase, hz⟩ := mem_support_bind_peel _ _ hz
        have hz' := eq_of_mem_support_pure _ hz
        subst z
        have hh' := hh.2 answer
        have hs' := hs.2 answer
        simp only [SignatureAlg.IsHashQuery, SignatureAlg.IsSignQuery, ↓reduceIte] at hh' hs'
        simpa [Counts.single, hashCost, RandomOracleModel.hashCost] using
          ih answer (signed := signed) hh' hs' hphase
      · rw [runPhase_query_bind_world] at hz
        obtain ⟨answer, _, hz⟩ := mem_support_bind_peel _ _ hz
        obtain ⟨⟨⟨value, counts⟩, finalLog⟩, hphase, hz⟩ := mem_support_bind_peel _ _ hz
        have hz' := eq_of_mem_support_pure _ hz
        subst z
        have hh' := hh.2 answer
        have hs' := hs.2 answer
        simp only [SignatureAlg.IsHashQuery, SignatureAlg.IsSignQuery, ↓reduceIte] at hh' hs'
        obtain ⟨hhash, hsign, hverifier, suffix, hlog, hlength⟩ :=
          ih answer (signed := signed) hh' hs' hphase
        dsimp only at hhash hsign hverifier hlog hlength
        have hpositive : 0 < qh := by simpa [SignatureAlg.IsHashQuery] using hh.1
        refine ⟨?_, ?_, ?_, suffix, hlog, ?_⟩
        · simp only [Pi.add_apply, Counts.single, Pi.single_eq_same, hashCost,
            RandomOracleModel.hashCost]
          omega
        · simpa [Counts.single] using hsign
        · simpa [Counts.single] using hverifier
        · simpa [Counts.single] using hlength
      · rw [runPhase_query_bind_sign] at hz
        obtain ⟨answer, _, hz⟩ := mem_support_bind_peel _ _ hz
        obtain ⟨⟨⟨value, counts⟩, finalLog⟩, hphase, hz⟩ := mem_support_bind_peel _ _ hz
        have hz' := eq_of_mem_support_pure _ hz
        subst z
        have hh' := hh.2 answer
        have hs' := hs.2 answer
        simp only [SignatureAlg.IsHashQuery, SignatureAlg.IsSignQuery, ↓reduceIte] at hh' hs'
        obtain ⟨hhash, hsign, hverifier, suffix, hlog, hlength⟩ :=
          ih answer (signed := signed ++ [⟨request, answer⟩]) hh' hs' hphase
        dsimp only at hhash hsign hverifier hlog hlength
        have hpositive : 0 < qs := by simpa [SignatureAlg.IsSignQuery] using hs.1
        refine ⟨?_, ?_, ?_, ⟨request, answer⟩ :: suffix, ?_, ?_⟩
        · simpa [Counts.single] using hhash
        · simp only [Pi.add_apply, Counts.single, Pi.single_eq_same]
          omega
        · simpa [Counts.single] using hverifier
        · simpa [List.append_assoc] using hlog
        · simp [Counts.single, hlength, Nat.add_comm]

open Counted Projection in
/-- The actual game phase observes additive counters before adding final verification work. -/
theorem afterKeygen_eq_runPhase (scheme : ExternalScheme Output PK SK)
    (adversary : Adversary Output PK) (keys : SK × PK) :
    afterKeygen scheme adversary keys = do
      let ((forgery, adversaryCounts), signed) ←
        runPhase scheme keys.1 (adversary.main keys.2) []
      let (verified, verifierCounts) ← countQueries
        (fun input => Counts.single .verification (hashCost input))
        (scheme.verify keys.2 forgery.message forgery.signature)
      return {
        forgery := forgery
        signed := signed
        verified := verified
        counts := adversaryCounts + verifierCounts } := by
  let view := externalView scheme
  let main := externalMain adversary
  let observe : SigningView.Outcome Message Bytes (Option Bytes) × Counts → Outcome :=
    fun result => {
      forgery := ⟨result.1.forgery.1, result.1.forgery.2⟩
      signed := result.1.rawLog
      verified := result.1.verified
      counts := result.2 }
  calc
    _ = observe <$> (AddWriterT.mapCostHom phaseCountsHom
        (SigningView.countedAfterKeygen sourcePolicy view keys.2 keys.1 main)).runAdd := by
      simp [afterKeygen, canonicalAfterKeygen, legacyOutcome, observe, view, main,
        AddWriterT.runAdd_mapCostHom, phaseCountsHom, Functor.map_map]
    _ = observe <$>
        (SigningView.countedAfterKeygen phasePolicy view keys.2 keys.1 main).runAdd := by
      rw [suffix_map]
    _ = _ := by
      simp [observe, view, main, SigningView.countedAfterKeygen, externalView, externalMain,
        SigningView.countedPhase, SigningView.countedPhaseUsing, runPhase, Counted.runPhase,
        simulateQ_map, AddWriterT.runAdd_bind,
        countQueries, SigningView.costed, phasePolicy, sourcePolicy, sourceKind,
        Functor.map_map, Prod.map]


/-- The same actual phase bounds hold from every initial random-oracle cache. -/
theorem runPhase_bounds_cached [SampleableType Output]
    (scheme : ExternalScheme Output PK SK) (sk : SK)
    (program : OracleComp (World Output + SigningSpec) α) (signed : SigningLog)
    {qh qs : Nat}
    (hh : IsQueryBoundP program
      (SignatureAlg.IsHashQuery (hs := RandomOracleModel.HashSpec Bytes Output)
        (M := Message) (S := Option Bytes)) qh)
    (hs : IsQueryBoundP program
      (SignatureAlg.IsSignQuery (hs := RandomOracleModel.HashSpec Bytes Output)
        (M := Message) (S := Option Bytes)) qs)
    (cache : QueryCache (RandomOracleModel.HashSpec Bytes Output))
    {z : (α × Counts) × SigningLog}
    (hz : z ∈ support ((simulateQ (RandomOracleModel.impl Bytes Output)
      (runPhase scheme sk program signed)).run' cache)) :
    z.1.2 .hash ≤ qh ∧ z.1.2 .signing ≤ qs ∧ z.1.2 .verification = 0 ∧
      ∃ suffix, z.2 = signed ++ suffix ∧ suffix.length = z.1.2 .signing :=
  runPhase_bounds scheme sk program signed hh hs
    (support_simulateQ_run'_subset (RandomOracleModel.impl Bytes Output) _ cache hz)

/-- Source-selected adversary work is exactly signing, direct hashing and final verification. -/
theorem sum_adversaryWork_sourceCounts (outcome : Outcome) (keygenHashes laterHashes : Nat) :
    ∑ kind ∈ adversaryWork, sourceCounts outcome keygenHashes laterHashes kind =
      outcome.counts .signing + outcome.counts .hash + outcome.counts .verification := by
  simp [adversaryWork, sourceCounts, Nat.add_assoc]

end SLHDSA.SHAKE128s.Game
