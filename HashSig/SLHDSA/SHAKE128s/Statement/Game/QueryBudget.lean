/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import HashSig.SLHDSA.SHAKE128s.Statement.Game
public import VCVio.CryptoFoundations.SignatureAlg.RomQueryCount
public import VCVio.OracleComp.QueryTracking.QueryBound.Simulation

/-!
# Pathwise budgets of the counted signature game

The adversary's own hash and signing queries determine its phase counters. Internal signer
queries remain beneath those counters, and every returned signing answer extends the log.
-/

public section

open OracleComp OracleSpec

namespace SLHDSA.SHAKE128s.Game

variable {Output PK SK α β : Type}

/-- The actual counted handler of the adversary phase. -/
@[expose] def phaseHandler (scheme : ExternalScheme Output PK SK) (sk : SK) :
    QueryImpl (World Output + SigningSpec) (CountedRun Output) :=
  (QueryImpl.ofLift (World Output)
    (StateT SigningLog (OracleComp (World Output)))).withAddCost
      (fun input => Counts.single .hash (hashCost input)) + signingOracle scheme sk

/-- Run an adversary program with its actual additive phase counters and an initial log. -/
@[expose] def runPhase (scheme : ExternalScheme Output PK SK) (sk : SK)
    (program : OracleComp (World Output + SigningSpec) α) (signed : SigningLog) :
    OracleComp (World Output) ((α × Counts) × SigningLog) :=
  (simulateQ (phaseHandler scheme sk) program).runAdd.run signed

/-- A pure adversary result adds no count and retains the complete signing prefix. -/
@[simp] theorem runPhase_pure (scheme : ExternalScheme Output PK SK) (sk : SK)
    (x : α) (signed : SigningLog) :
    runPhase scheme sk (pure x) signed = pure ((x, 0), signed) := by
  simp [runPhase]

/-- Sequencing adds the actual phase counters and threads the complete signing log. -/
theorem runPhase_bind (scheme : ExternalScheme Output PK SK) (sk : SK)
    (program : OracleComp (World Output + SigningSpec) α)
    (next : α → OracleComp (World Output + SigningSpec) β) (signed : SigningLog) :
    runPhase scheme sk (program >>= next) signed = do
      let ((x, firstCounts), intermediate) ← runPhase scheme sk program signed
      let ((y, lastCounts), finalLog) ← runPhase scheme sk (next x) intermediate
      return ((y, firstCounts + lastCounts), finalLog) := by
  simp [runPhase, AddWriterT.runAdd_bind, StateT.run_bind, Prod.map]

/-- An ambient call leaves the signing log intact and charges only its direct hash cost. -/
theorem runPhase_query_world (scheme : ExternalScheme Output PK SK) (sk : SK)
    (input : (World Output).Domain) (signed : SigningLog) :
    runPhase scheme sk (liftM ((World Output + SigningSpec).query (Sum.inl input))) signed =
      (fun answer => ((answer, Counts.single .hash (hashCost input)), signed)) <$>
        (query input : OracleComp (World Output) _) := by
  simp [runPhase, phaseHandler, QueryImpl.withAddCost_apply, QueryImpl.ofLift_apply,
    AddWriterT.runAdd_bind, AddWriterT.runAdd_liftM]

private theorem run_lift_world (computation : OracleComp (World Output) α)
    (signed : SigningLog) :
    ((liftM computation : CountedRun Output α).run).run signed =
      (fun x => ((x, (1 : Multiplicative Counts)), signed)) <$> computation := by
  change ((computation >>= fun x => pure (x, signed)) >>= fun p =>
    pure ((p.1, (1 : Multiplicative Counts)), p.2)) = _
  simp

private theorem run_modifyGet (f : SigningLog → α × SigningLog) (signed : SigningLog) :
    ((modifyGet f : CountedRun Output α).run).run signed =
      pure (((f signed).1, (1 : Multiplicative Counts)), (f signed).2) := rfl

/-- Every completed signing call charges one request and appends its answer, including `none`. -/
theorem runPhase_query_sign (scheme : ExternalScheme Output PK SK) (sk : SK)
    (request : Message) (signed : SigningLog) :
    runPhase scheme sk (liftM ((World Output + SigningSpec).query (Sum.inr request))) signed =
      (fun answer => ((answer, Counts.single .signing 1), signed ++ [⟨request, answer⟩])) <$>
        scheme.sign sk request := by
  simp [runPhase, phaseHandler, signingOracle, AddWriterT.runAdd, modify, Prod.map,
    run_lift_world, run_modifyGet]

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
  rcases keys with ⟨sk, pk⟩
  simp [afterKeygen, runPhase, phaseHandler, AddWriterT.runAdd, Prod.map]

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
