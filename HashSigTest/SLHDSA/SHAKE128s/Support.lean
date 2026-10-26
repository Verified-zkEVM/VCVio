/-
Copyright (c) 2026 Tom Wambsgans, Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans, Alexander Hicks
-/

module
public import HashSig.SLHDSA.SHAKE128s.Statement.Game
public import VCVio.OracleComp.QueryTracking.ListCache

/-!
# Executable counted-game fixtures

The executable runners retain the counted game's exact programs. A parameterized toy scheme
and an association-list cache expose hash calls, answer draws and private samples separately.
-/

public section

open OracleComp OracleSpec

namespace SLHDSA.SHAKE128s.TestSupport

open Game

variable {Output PK SK : Type}

/-- Execute the adversary phase and final verifier with the game's source counters. -/
@[expose] def executableAfterKeygen (scheme : ExternalScheme Output PK SK)
    (adversary : Adversary Output PK) (keys : SK × PK) :
    OracleComp (World Output) Outcome := do
  let (sk, pk) := keys
  let ((forgery, adversaryCounts), signed) ←
    (simulateQ
      ((QueryImpl.ofLift (World Output)
          (StateT SigningLog (OracleComp (World Output)))).withAddCost
          (fun input => Counts.single .hash (hashCost input)) + signingOracle scheme sk)
      (adversary.main pk)).run.run []
  let (verified, verifierCounts) ← countQueries
    (fun input => Counts.single .verification (hashCost input))
    (scheme.verify pk forgery.message forgery.signature)
  return {
    forgery := forgery
    signed := signed
    verified := verified
    counts := Multiplicative.toAdd adversaryCounts + verifierCounts }

/-- The executable phase is the actual counted phase of the game. -/
theorem executableAfterKeygen_eq (scheme : ExternalScheme Output PK SK)
    (adversary : Adversary Output PK) (keys : SK × PK) :
    executableAfterKeygen scheme adversary keys = Game.afterKeygen scheme adversary keys := rfl

/-- Execute key generation and the complete experiment with all source counters. -/
@[expose] def executableExperimentBySource (scheme : ExternalScheme Output PK SK)
    (adversary : Adversary Output PK) :
    OracleComp (World Output) (Outcome × Unforgeability.QueryCounts) := do
  let (keys, keygenHashes) ← countAllHashes scheme.keygen
  let (outcome, laterHashes) ← countAllHashes (executableAfterKeygen scheme adversary keys)
  return (outcome, sourceCounts outcome keygenHashes laterHashes)

/-- The executable experiment is the actual source-counted game program. -/
theorem executableExperimentBySource_eq (scheme : ExternalScheme Output PK SK)
    (adversary : Adversary Output PK) :
    executableExperimentBySource scheme adversary = Game.experimentBySource scheme adversary := rfl

/-- Hash each listed input, retaining every repeated call. -/
def hashInputs (inputs : List Bytes) : OracleComp (World Output) Unit := do
  for input in inputs do
    let _ : Output ← query (spec := RandomOracleModel.HashSpec Bytes Output) input

/-- Configurable hash work and replies of a toy signing scheme. -/
structure ToySchemeConfig (PK : Type) where
  /-- The public key returned by key generation. -/
  publicKey : PK
  /-- Key-generation hash inputs. -/
  keygenInputs : List Bytes := [[0]]
  /-- Hash inputs used by each signing request. -/
  signerInputs : List Bytes := [[1], [2]]
  /-- Hash inputs used by final verification. -/
  verifierInputs : List Bytes := [[4]]
  /-- The signing response, including rejection. -/
  signingReply : Option Bytes := some [0]
  /-- The literal signatures accepted by the verifier. -/
  acceptedSignatures : List Bytes := [[0], [1]]

/-- A toy scheme whose public-key carrier and hash-answer carrier remain parameters. -/
def toyScheme (config : ToySchemeConfig PK) : ExternalScheme Output PK Unit where
  keygen := do
    hashInputs config.keygenInputs
    return ((), config.publicKey)
  sign _ _ := do
    hashInputs config.signerInputs
    return config.signingReply
  verify _ _ signature := do
    hashInputs config.verifierInputs
    return config.acceptedSignatures.contains signature

/-- The ambient queries, signing requests and final output of a toy adversary. -/
structure ToyAdversaryConfig where
  /-- Direct adversary hash inputs. -/
  directInputs : List Bytes := [[3], [3]]
  /-- Number of free, private samples. -/
  privateSamples : Nat := 2
  /-- Every signing request issued by the adversary. -/
  signingRequests : List Message
  /-- The final claimed forgery. -/
  forgery : Forgery

/-- A toy adversary with explicit repeated queries and an attacker-chosen forgery. -/
def toyAdversary (config : ToyAdversaryConfig) : Adversary Output PK where
  main _ := do
    for input in config.directInputs do
      let _ : Output ← query (spec := RandomOracleModel.HashSpec Bytes Output) input
    for _ in List.range config.privateSamples do
      let _ ← query (spec := unifSpec) 0
    for request in config.signingRequests do
      let _ ← query (spec := SigningSpec) request
    return config.forgery

/-- Observable backend activity, independent of the game's source counters. -/
structure BackendTrace where
  /-- Every hash query, including cache hits. -/
  hashCalls : Nat := 0
  /-- Calls to the fresh-answer provider on cache misses. -/
  answerDraws : Nat := 0
  /-- Private uniform requests made by the client. -/
  privateSamples : Nat := 0
  /-- The chronological hash-query inputs. -/
  hashInputs : List Bytes := []

/-- A cached oracle over an independently recorded backend trace. -/
abbrev CachedBackend (Output : Type) := StateT (List (Bytes × Output)) (StateM BackendTrace)

/-- Produce one deterministic test answer and record that the cache requested a fresh answer. -/
def drawAnswer (answer : Output) :
    QueryImpl (RandomOracleModel.HashSpec Bytes Output) (StateM BackendTrace) := fun _ => do
  modify fun trace => { trace with answerDraws := trace.answerDraws + 1 }
  return answer

/-- Forward private samples freely and count hash calls before the association-list cache. -/
def cachedHandler (answer : Output) : QueryImpl (World Output) (CachedBackend Output)
  | .inl n => do
      liftM (modify (fun trace : BackendTrace =>
        { trace with privateSamples := trace.privateSamples + 1 }) : StateM BackendTrace Unit)
      return (⟨0, Nat.zero_lt_succ n⟩ : Fin (n + 1))
  | .inr input => do
      liftM (modify (fun trace : BackendTrace =>
        { trace with
          hashCalls := trace.hashCalls + 1
          hashInputs := trace.hashInputs ++ [input] }) :
        StateM BackendTrace Unit)
      QueryImpl.ListCache.handler (drawAnswer answer) input

/-- Execute the real counted program against a deterministic cached test backend. -/
@[expose] def runWithCache (answer : Output) (scheme : ExternalScheme Output PK SK)
    (adversary : Adversary Output PK) (cache : List (Bytes × Output) := []) :
    ((Outcome × Unforgeability.QueryCounts) × List (Bytes × Output)) × BackendTrace :=
  ((simulateQ (cachedHandler answer)
    (executableExperimentBySource scheme adversary)).run cache).run {}

/-- The backend executes the actual source-counted game program. -/
theorem runWithCache_eq (answer : Output) (scheme : ExternalScheme Output PK SK)
    (adversary : Adversary Output PK) (cache : List (Bytes × Output)) :
    runWithCache answer scheme adversary cache =
      ((simulateQ (cachedHandler answer)
        (Game.experimentBySource scheme adversary)).run cache).run {} := by
  rw [runWithCache, executableExperimentBySource_eq]

/-- The three selected coordinates of source-counted adversary work. -/
@[expose] def selectedWork (counts : Unforgeability.QueryCounts) : Nat :=
  counts .sign + counts .hash + counts .verifier

/-- The observed work equals the game's selected counting mode. -/
theorem selectedWork_eq_sum_adversaryWork (counts : Unforgeability.QueryCounts) :
    selectedWork counts = ∑ kind ∈ Game.adversaryWork, counts kind := by
  simp [selectedWork, Game.adversaryWork, Nat.add_assoc]

/-- Fail an executable when a fixture observation differs from its expectation. -/
def ensure (label : String) (condition : Bool) : IO Unit :=
  unless condition do throw (IO.userError s!"SLH-DSA counted-game check failed: {label}")

end SLHDSA.SHAKE128s.TestSupport
