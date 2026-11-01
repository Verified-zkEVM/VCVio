/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Statement.Security
public import HashSig.SLHDSA.SHAKE128s.Statement.Game.CompleteBudget
public import HashSig.SLHDSA.SHAKE128s.Bridge.SharedExperiment.Recorded

/-!
# The forgery experiment and its counted views

The definitions the security proof works with: `Security.experiment`, the whole SUF-CMA
experiment (key generation, the adversary's phase with its signing oracle, and verification of
the forgery) as one oracle computation; its random-oracle runs `Security.run` and
`Security.runAll`, the latter with the total hash count; and the views of the scheme used by the
charges, namely the count `Checksum.chainVerificationCalls` of chain steps in Algorithm 8 and
the parse `MessageDigest.parse` of a message digest into a FORS instance and its indices.
-/

public section

open OracleComp OracleSpec ENNReal

namespace SLHDSA.SHAKE128s

/-- Number of calls to `F` in Algorithm 8, before the final WOTS public-key compression. -/
@[expose] def Checksum.chainVerificationCalls (digits : MessageDigits) : Nat :=
  (∑ i, (w - 1 - (digits i).val)) +
    ∑ i : Fin checksumDigits, (w - 1 - (Checksum.checksumDigit (Checksum.checksum digits) i).val)

namespace MessageDigest

/-- A FORS instance, identified by its 63-bit hypertree tree-and-leaf index. -/
abbrev Instance := Fin (2 ^ totalHeight)
/-- What a message digest selects: a FORS instance and a leaf index in each of its trees. -/
abbrev View := Instance × (ForsTree → ForsLeaf)

/-- The 63-bit FORS-instance index and the FORS indices. -/
@[expose] def parse (output : HashOutput) : View :=
  ((treeIndex output ++ leafIndex output).toFin, forsIndices output)

end MessageDigest

namespace Security

export Game (Counts.work)

/-- Key generation, then the adversary's phase and verification. -/
@[expose]
noncomputable def experiment (adversary : Adversary) : OracleComp OracleWorld Outcome :=
  Game.Counted.legacyOutcome <$> Game.Counted.canonicalExperiment externalScheme adversary

/-- Key generation precedes the full supplied-key client and verification observation. -/
theorem experiment_eq_keygen_bind (adversary : Adversary) :
    experiment adversary = Scheme.keygen >>= afterKeygen adversary := by
  have eraseSuffix (keys : SecretKey × PublicKey) :
      (Game.countAllHashes (afterKeygen adversary keys) >>= fun z => pure z.1) =
        afterKeygen adversary keys := by
    simpa only [map_eq_bind_pure_comp, Function.comp_def] using
      (Game.fst_map_countAllHashes (afterKeygen adversary keys))
  have projected := congrArg
    (fun p : OracleComp OracleWorld (Outcome × Unforgeability.QueryCounts) => Prod.fst <$> p)
    (Game.experimentBySource_eq_countAllHashes externalScheme adversary)
  have h : experiment adversary =
      (Game.countAllHashes (Scheme.keygen : OracleComp OracleWorld (SecretKey × PublicKey)) >>=
        fun keys => Game.countAllHashes (afterKeygen adversary keys.1) >>= fun z => pure z.1) := by
    simpa only [experiment, Game.experimentBySource, Game.Counted.legacyObservation,
      map_bind, map_pure, Functor.map_map, Function.comp_def, externalScheme, afterKeygen]
      using projected
  rw [h]
  simp_rw [eraseSuffix]
  simpa only [bind_map_left] using
    congrArg (fun p : OracleComp OracleWorld (SecretKey × PublicKey) => p >>= afterKeygen adversary)
      (Game.fst_map_countAllHashes
        (Scheme.keygen : OracleComp OracleWorld (SecretKey × PublicKey)))

/-- The writer/state presentation retains the exact shared phase and every raw log prefix. -/
theorem legacyPhase_eq_runPhase {α : Type} (sk : SecretKey)
    (body : OracleComp (OracleWorld + SigningSpec) α) (signed : SigningLog) :
    ((simulateQ
      ((QueryImpl.ofLift OracleWorld (StateT SigningLog (OracleComp OracleWorld))).withAddCost
        (fun input => Counts.single .hash (hashCost input)) + signingOracle sk)
      body).runAdd).run signed =
      Game.runPhase externalScheme sk body signed := by
  let handler : QueryImpl (OracleWorld + SigningSpec) CountedRun :=
    (QueryImpl.ofLift OracleWorld (StateT SigningLog (OracleComp OracleWorld))).withAddCost
      (fun input => Counts.single .hash (hashCost input)) + signingOracle sk
  let phase {γ : Type} (program : OracleComp (OracleWorld + SigningSpec) γ)
      (initialLog : SigningLog) : OracleComp OracleWorld ((γ × Counts) × SigningLog) :=
    ((simulateQ handler program).runAdd).run initialLog
  have phase_pure {γ : Type} (value : γ) (initialLog : SigningLog) :
      phase (pure value) initialLog = pure ((value, 0), initialLog) := by
    simp [phase]
  have phase_bind {γ δ : Type}
      (program : OracleComp (OracleWorld + SigningSpec) γ)
      (next : γ → OracleComp (OracleWorld + SigningSpec) δ) (initialLog : SigningLog) :
      phase (program >>= next) initialLog = (do
        let ((value, firstCounts), middle) ← phase program initialLog
        let ((result, lastCounts), finalLog) ← phase (next value) middle
        return ((result, firstCounts + lastCounts), finalLog)) := by
    simp [phase, simulateQ_bind, AddWriterT.runAdd_bind, StateT.run_bind,
      map_eq_bind_pure_comp, Prod.map]
  have phase_world (input : OracleWorld.Domain) (initialLog : SigningLog) :
      phase (liftM ((OracleWorld + SigningSpec).query (.inl input))) initialLog =
        (fun answer => ((answer, Counts.single .hash (hashCost input)), initialLog)) <$>
          (query input : OracleComp OracleWorld _) := by
    simp [phase, handler, QueryImpl.withAddCost_apply, QueryImpl.ofLift,
      AddWriterT.runAdd_bind, Prod.map]
  have phase_sign (request : Message) (initialLog : SigningLog) :
      phase (liftM ((OracleWorld + SigningSpec).query (.inr request))) initialLog =
        (fun answer => ((answer, Counts.single .signing 1), initialLog ++ [⟨request, answer⟩])) <$>
          (Scheme.sign sk request : OracleComp OracleWorld (Option Bytes)) := by
    simp [phase, handler, signingOracle, AddWriterT.runAdd,
      Game.Counted.legacyRun_signing_run, Functor.map_map, Prod.map,
      Counts.single, Game.Counts.single]
  change phase body signed = _
  induction body using OracleComp.inductionOn generalizing signed with
  | pure value =>
    rw [phase_pure, Game.runPhase_pure]
  | query_bind input next ih =>
    rcases input with input | request
    · rw [phase_bind, phase_world, Game.runPhase_query_bind_world]
      simp only [bind_map_left, ih, Counts.single, Game.Counts.single,
        hashCost, Game.hashCost]
    · rw [phase_bind, phase_sign, Game.runPhase_query_bind_sign]
      simp only [bind_map_left, ih, externalScheme, Counts.single, Game.Counts.single]


/-- The experiment run against a lazily sampled random oracle. -/
@[expose] noncomputable def run (adversary : Adversary) : ProbComp Outcome :=
  RandomOracleModel.run (experiment adversary)

/-- The experiment with its total hash count. -/
@[expose] noncomputable def runAll (adversary : Adversary) : ProbComp (Outcome × Nat) :=
  RandomOracleModel.run (countAllHashes (experiment adversary))

/-- The probability that the adversary wins the experiment, read off `runAll`. -/
@[expose] noncomputable def totalAdvantage (adversary : Adversary) : ℝ≥0∞ :=
  Pr{let result ← runAll adversary}[Wins result.1]

end Security

end SLHDSA.SHAKE128s
