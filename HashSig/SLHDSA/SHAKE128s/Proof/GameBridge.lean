/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.CacheReplay
public import HashSig.SLHDSA.SHAKE128s.Proof.VerifierNaturality
public import HashSig.SLHDSA.SHAKE128s.Proof.Correctness.Naturality
public import HashSig.SLHDSA.SHAKE128s.Proof.Extraction.HypertreeChain
public import HashSig.SLHDSA.SHAKE128s.Proof.CanonicalGraph.Programming
public import HashSig.SLHDSA.SHAKE128s.Proof.HypertreeDispatch

/-!
# From the game's run to the extraction's `Id` statements

The extraction chain states everything with `(m := Id)` under the development's
`[HasQuery HashSpec Id]` variable; the game runs in `OracleComp`. Two facts bridge them.

* `VerifierNaturality` and `Correctness.Naturality` give the naturality of every scheme
  operation: simulating it through any `impl` agreeing with the ambient `query` yields the same
  operation in the target monad. `CacheReplay.replay cache` agrees with
  `CacheReplay.replayQuery cache` by definition, so that hypothesis is `rfl`.
* `CacheReplay.run_eq_replay` says a hash-only run's result is what replaying it against its
  own final cache computes.

Composing them: whatever the game computed, the `Id`-level operation under `replayQuery` of the
final cache computed too. So an accepted forgery in the game *is* an accepted forgery in the
sense `HypertreeDispatch.cases_of_accepted` consumes, and the honest key the extraction compares
against is the one key generation actually produced.
-/

@[expose] public section

open OracleComp OracleSpec

namespace SlhDsaSecurity.GameBridge

/-- The replay implementation agrees with the replay instance, by definition. -/
theorem replay_agrees (cache : QueryCache HashSpec) (input : Bytes) :
    CacheReplay.replay cache input =
      (@query _ HashSpec Id (CacheReplay.replayQuery cache) input : Id HashOutput) := rfl

/-- **What the game verified, the replayed verifier verifies.** -/
theorem verify_eq_replay (pk : PublicKey) (request : Message) (signature : Bytes)
    (initialCache finalCache : QueryCache HashSpec) (verified : Bool)
    (hmem : (verified, finalCache) ∈
      support ((simulateQ randomOracle
        (Scheme.verify (m := OracleComp HashSpec) pk request signature)).run initialCache)) :
    verified = @Scheme.verify Id Id.instMonad (CacheReplay.replayQuery finalCache) pk request signature := by
  rw [CacheReplay.run_eq_replay _ initialCache finalCache verified hmem]
  exact @VerifierNaturality.verify_simulate Id Id.instMonad _
    (CacheReplay.replay finalCache) (CacheReplay.replayQuery finalCache)
    (replay_agrees finalCache) pk request signature

/-- The generated public key carries the public seed and the honest top root — the two
hypotheses `HypertreeDispatch.cases_of_accepted` takes. -/
theorem keygen_publicKey (secretSeed prfSeed publicSeed : Digest)
    (cache : QueryCache HashSpec) :
    (@Scheme.keygenInternal Id Id.instMonad (CacheReplay.replayQuery cache)
        secretSeed prfSeed publicSeed).2.seed = publicSeed ∧
      (@Scheme.keygenInternal Id Id.instMonad (CacheReplay.replayQuery cache)
        secretSeed prfSeed publicSeed).2.root =
        @SlhDsaSecurity.Extraction.HypertreeChain.honestNode (CacheReplay.replayQuery cache)
          secretSeed publicSeed (layers - 1) 0 :=
  ⟨rfl, rfl⟩

/-! ## Identifying the cells the game produced

Every charge is parameterised by the honest cells, and in the experiment those are whatever
key generation and signing wrote into the oracle. `CanonicalGraph.Programming.value_eq_of_cache_agreement`
says a cell table is *the* graph evaluation as soon as the cache agrees with it at the
canonical inputs — which is exactly what a run that made those queries leaves behind.

Read under `CacheReplay.replayQuery`, a hash call is a cache lookup, so the agreement
hypothesis becomes a statement purely about the game's own cache. -/

/-- **A cache carrying the canonical entries determines the graph's cells.** -/
theorem value_eq_cellsOfOutputs (publicSeed secretSeed : Digest)
    (outputs : CanonicalGraph.Programming.Outputs) (cache : QueryCache HashSpec)
    (hagrees : ∀ (input : Bytes) (output : HashOutput),
      CanonicalGraph.Programming.cacheFrom publicSeed
          (CanonicalGraph.Programming.cellsOfOutputs secretSeed outputs) outputs
          CanonicalGraph.Programming.order ∅ input = some output →
        cache input = some output) :
    @CanonicalGraph.value (CacheReplay.replayQuery cache) secretSeed publicSeed =
      CanonicalGraph.Programming.cellsOfOutputs secretSeed outputs := by
  refine @CanonicalGraph.Programming.value_eq_of_cache_agreement
    (CacheReplay.replayQuery cache) publicSeed secretSeed outputs ?_
  intro input output hentry
  have hcache := hagrees input output hentry
  show ((cache input).getD default : Id HashOutput) = output
  rw [hcache]
  rfl

/-! ## Unfolding an acceptance

`verify_eq_replay` says the game's verdict is the replayed verifier's. This takes that verdict
apart: a `true` from `Scheme.verify` means the request framed, the signature parsed, and the
hypertree verified against the FORS key recovered from the signature — which is exactly the
shape `HypertreeDispatch.cases_of_accepted` consumes.

Both steps are case analysis on the `Option`s in `Scheme.verify`, with no hashing involved:
an invalid context or a malformed signature is rejected before any oracle call, so there is
nothing to charge and nothing to extract. -/

variable [HasQuery HashSpec Id]

/-- An acceptance frames, parses, and passes the internal verifier. -/
theorem verifyInternal_of_verify (pk : PublicKey) (request : Message) (signature : Bytes)
    (haccept : Scheme.verify (m := Id) pk request signature = true) :
    ∃ (message : Bytes) (parsed : Signature),
      request.frame = some message ∧ Signature.fromBytes? signature = some parsed ∧
        Scheme.verifyInternal (m := Id) pk message parsed = true := by
  unfold Scheme.verify at haccept
  cases hframe : request.frame with
  | none => rw [hframe] at haccept; exact absurd haccept (by simp)
  | some message =>
    rw [hframe] at haccept
    cases hparsed : Signature.fromBytes? signature with
    | none => rw [hparsed] at haccept; exact absurd haccept (by simp)
    | some parsed =>
      rw [hparsed] at haccept
      exact ⟨message, parsed, rfl, rfl, haccept⟩

/-- The internal verifier's acceptance is a hypertree acceptance at the recovered FORS key. -/
theorem hypertree_of_verifyInternal (pk : PublicKey) (message : Bytes) (parsed : Signature)
    (haccept : Scheme.verifyInternal (m := Id) pk message parsed = true) :
    SlhDsaSecurity.Hypertree.verify (m := Id)
        (SlhDsaSecurity.Fors.publicKeyFromSignature (m := Id) parsed.fors
          (MessageDigest.forsIndices
            (Hashing.messageDigest (m := Id) parsed.randomizer pk message))
          pk.seed
          (Scheme.forsAddress
            (Hashing.messageDigest (m := Id) parsed.randomizer pk message)))
        parsed.hypertree pk
        (MessageDigest.treeIndex
          (Hashing.messageDigest (m := Id) parsed.randomizer pk message))
        (MessageDigest.leafIndex
          (Hashing.messageDigest (m := Id) parsed.randomizer pk message)).toFin = true :=
  haccept

/-! ## The chain, composed

Everything above joins into one implication: a forgery the *game* accepted, against the key
the game generated, yields one of the three things the charges pay for. No step here is
probabilistic — it is the structural reduction of SLH-DSA verification, carried from
`Security.experiment`'s own verifier down to events about the oracle's answers.

The honest FORS key is left existentially quantified because it is whatever the genuine
secrets produce at the address the forgery's digest selects; the FORS side of the argument
(`ForsDispatch.forsCollision_or_canonical_secrets`) takes it from there. -/

end SlhDsaSecurity.GameBridge
