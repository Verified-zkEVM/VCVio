/-
Copyright (c) 2026 Tom Wambsgans, Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans, Alexander Hicks
-/

module
public import HashSig.SLHDSA.SHAKE128s.Statement.Game.Data
public import VCVio.CryptoFoundations.SignatureAlg.CountedExperiment

/-!
# Source-counted external signature experiments

The shared counted owner executes every phase. Source vectors retain every attempted signing
request, raw reply and ambient hash; projections expose the external game's phase observations.
-/

public section
open OracleComp OracleSpec SignatureAlg
universe v
namespace SLHDSA.SHAKE128s.Game

variable {Output PK SK : Type}

/-- Run a computation, and also return the sum of `cost` over its queries. -/
@[expose] def countQueries {α : Type} (cost : (World Output).Domain → Counts)
    (computation : OracleComp (World Output) α) : OracleComp (World Output) (α × Counts) :=
  (SignatureAlg.SigningView.costed
    (fun event : SignatureAlg.SigningView.Event (World Output) Message =>
      match event with
      | .ambient _ input => cost input
      | .signingAttempt _ => 0) .adversary computation).runAdd

/-- Run a computation, and also return its number of hash calls. -/
@[expose] def countAllHashes {α : Type} (computation : OracleComp (World Output) α) :
    OracleComp (World Output) (α × Nat) :=
  (SignatureAlg.SigningView.costed
    (fun event : SignatureAlg.SigningView.Event (World Output) Message =>
      match event with
      | .ambient _ input => hashCost input
      | .signingAttempt _ => 0) .adversary computation).runAdd

namespace Counted

/-- The five source coordinates of the original signature game. -/
abbrev SourceCounts := Unforgeability.QueryCounts

/-- The original source coordinate for each ambient-query phase. -/
@[expose] def sourceKind : SigningView.Phase → Unforgeability.QueryKind
  | .keygen => .keygen
  | .adversary => .hash
  | .signer => .signer
  | .verification => .verifier

/-- Every hash costs one in its phase; every signing attempt costs one, including rejection. -/
@[expose] def sourcePolicy {Output : Type} :
    SigningView.Event (World Output) Message → SourceCounts
  | .ambient phase input => Pi.single (sourceKind phase) (hashCost input)
  | .signingAttempt _ => Pi.single .sign 1

/-- A signing view of the same external algorithms, with public/secret key-pair order. -/
@[expose] def externalView {Output PK SK : Type} (scheme : ExternalScheme Output PK SK) :
    SigningView (OracleComp (World Output)) Message PK SK Bytes (Option Bytes) where
  keygen := Prod.swap <$> scheme.keygen
  sign _ sk request := scheme.sign sk request
  verify := scheme.verify
  readback := id

/-- Recover the three original phase coordinates from the full source vector. -/
@[expose] def phaseCounts (cost : SourceCounts) : Counts
  | .signing => cost .sign
  | .hash => cost .hash
  | .verification => cost .verifier

/-- A single source coordinate projects to its corresponding client-phase counter. -/
@[simp] theorem phaseCounts_single (kind : Unforgeability.QueryKind) (amount : Nat) :
    phaseCounts (Pi.single kind amount) =
      match kind with
      | .sign => Counts.single .signing amount
      | .hash => Counts.single .hash amount
      | .verifier => Counts.single .verification amount
      | .keygen | .signer => 0 := by
  cases kind <;> funext index <;> cases index <;>
    simp [phaseCounts, Counts.single]

/-- The total hashes after key generation include direct, signer and verification calls. -/
@[expose] def laterHashes (cost : SourceCounts) : Nat :=
  cost .hash + cost .signer + cost .verifier

/-- Present the original adversary's final forgery as a message/signature pair. -/
@[expose] def externalMain {Output PK : Type} (adversary : Adversary Output PK)
    (pk : PK) : OracleComp (World Output + SigningSpec) (Message × Bytes) :=
  (fun forgery => (forgery.message, forgery.signature)) <$> adversary.main pk

/-- The shared counted program for the same external algorithms and adversary. -/
@[expose] def canonicalExperiment {Output PK SK : Type}
    (scheme : ExternalScheme Output PK SK) (adversary : Adversary Output PK) :
    OracleComp (World Output)
      (SigningView.Observation Message Bytes (Option Bytes) SourceCounts) :=
  SigningView.countedExperiment sourcePolicy (externalView scheme) (externalMain adversary)

/-- Recover the original outcome, including its full raw log and three phase counters. -/
@[expose] def legacyOutcome
    (observed : SigningView.Observation Message Bytes (Option Bytes) SourceCounts) :
    Outcome :=
  { forgery := ⟨observed.forgery.1, observed.forgery.2⟩
    signed := observed.rawLog
    verified := observed.verified
    counts := phaseCounts observed.cost }

/-- Recover the original outcome and its complete source vector from one observation. -/
@[expose] def legacyObservation
    (observed : SigningView.Observation Message Bytes (Option Bytes) SourceCounts) :
    Outcome × SourceCounts :=
  (legacyOutcome observed,
    sourceCounts (legacyOutcome observed) (observed.cost .keygen) (laterHashes observed.cost))

/-- The source subtraction reconstructs the entire declared vector, for every observation. -/
theorem legacyObservation_counts
    (observed : SigningView.Observation Message Bytes (Option Bytes) SourceCounts) :
    (legacyObservation observed).2 = observed.cost := by
  funext kind
  cases kind with
  | sign => rfl
  | hash => rfl
  | keygen => rfl
  | verifier => rfl
  | signer =>
      change observed.cost .hash + observed.cost .signer + observed.cost .verifier -
        observed.cost .hash - observed.cost .verifier = observed.cost .signer
      omega

/-- The phase counters ignore signer-internal traffic and all private samples. -/
@[expose] def phasePolicy {Output : Type} :
    SigningView.Event (World Output) Message → Counts :=
  fun event => phaseCounts (sourcePolicy event)

/-- Signer traffic executes in full while contributing no client-phase counter. -/
theorem costed_phasePolicy_signer {Output α : Type}
    (body : OracleComp (World Output) α) :
    SigningView.costed phasePolicy .signer body =
      (liftM body : SigningView.CostM (World Output) Counts α) := by
  induction body using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind input next ih =>
    simp only [SigningView.costed, simulateQ_bind, simulateQ_spec_query,
      QueryImpl.withAddCost_apply, phasePolicy, sourcePolicy, sourceKind,
      phaseCounts_single] at ih ⊢
    simp_rw [ih]
    apply WriterT.ext
    simp [AddWriterT.addTell, WriterT.run_bind]

/-- Present the shared writer's raw suffix as an append to a supplied state prefix. -/
@[expose] def legacyRun {Output C α : Type}
    (program : SigningView.LoggedCostM (World Output) Message (Option Bytes) C α) :
    AddWriterT C (StateT SigningLog (OracleComp (World Output))) α :=
  WriterT.mk (StateT.mk fun signed =>
    (fun result => ((result.1.1, Multiplicative.ofAdd result.2), signed ++ result.1.2)) <$>
      program.run.runAdd)

/-- The representation adapter retains arbitrary raw prefixes and the complete declared cost. -/
theorem legacyRun_run {Output C α : Type}
    (program : SigningView.LoggedCostM (World Output) Message (Option Bytes) C α)
    (signed : SigningLog) :
    (legacyRun program).runAdd.run signed =
      (fun result => ((result.1.1, result.2), signed ++ result.1.2)) <$>
        program.run.runAdd := by
  simp [legacyRun, AddWriterT.runAdd, Functor.map_map]

/-- A cached interpretation retains the whole legacy result and cost under every continuation. -/
theorem legacyRun_run_bind {Output C α Cache β : Type}
    {m : Type → Type v} [Monad m] [LawfulMonad m]
    (program : SigningView.LoggedCostM (World Output) Message (Option Bytes) C α)
    (signed : SigningLog) (handler : QueryImpl (World Output) (StateT Cache m))
    (initial : Cache) (next : (((α × C) × SigningLog) × Cache) → m β) :
    ((simulateQ handler ((legacyRun program).runAdd.run signed)).run initial >>= next) =
      ((simulateQ handler program.run.runAdd).run initial >>= fun result =>
        next (((result.1.1.1, result.1.2), signed ++ result.1.1.2), result.2)) := by
  rw [legacyRun_run, simulateQ_map, StateT.run_map, bind_map_left]

/-- A signing callback charges one attempt and appends its actual reply to every prefix. -/
theorem legacyRun_signing_run {Output : Type}
    (signer : Message → OracleComp (World Output) (Option Bytes))
    (request : Message) (signed : SigningLog) :
    ((legacyRun (SigningView.countedSigningOracleUsing phasePolicy signer request)).run).run
        signed =
      signer request >>= fun answer =>
        pure ((answer, Multiplicative.ofAdd (Counts.single .signing 1)),
          signed ++ [⟨request, answer⟩]) := by
  simp [legacyRun, SigningView.countedSigningOracleUsing_run, costed_phasePolicy_signer,
    phasePolicy, sourcePolicy, phaseCounts_single, AddWriterT.runAdd_bind, Prod.map]

/-- Run the actual callback phase, projecting its cost and retaining an arbitrary raw prefix. -/
@[expose] def runPhase {Output PK SK α : Type} (scheme : ExternalScheme Output PK SK)
    (sk : SK) (program : OracleComp (World Output + SigningSpec) α) (signed : SigningLog) :
    OracleComp (World Output) ((α × Counts) × SigningLog) :=
  (fun result => ((result.1.1, result.2), signed ++ result.1.2)) <$>
    (SigningView.countedPhaseUsing phasePolicy (scheme.sign sk) program).runAdd

/-- The client and final verifier retain their full source vector at supplied keys. -/
@[expose] def canonicalAfterKeygen {Output PK SK : Type}
    (scheme : ExternalScheme Output PK SK) (adversary : Adversary Output PK)
    (keys : SK × PK) :
    OracleComp (World Output)
      (SigningView.Observation Message Bytes (Option Bytes) SourceCounts) :=
  (fun result => { toOutcome := result.1, cost := result.2 }) <$>
    (SigningView.countedAfterKeygen sourcePolicy (externalView scheme)
      keys.2 keys.1 (externalMain adversary)).runAdd

end Counted

export Counted (runPhase)

end SLHDSA.SHAKE128s.Game
