/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
import Lean.Elab.Command
import Lean.Util.CollectAxioms
public import HashSig.GXMSS.Encoding.Incomparable
public import HashSig.GXMSS.Security.Auxiliary.Encoding
public import HashSig.GXMSS.Security.Reductions.WinternitzEncodingTargetCollision
public import HashSig.GXMSS.Security.Reductions.TargetSumEncodingTargetCollision
public import HashSigTest.GXMSS.EncodingInstances
import all HashSig.GXMSS.Security.Reductions.EncodingTargetCollisionReduction
import all HashSig.GXMSS.Security.Reductions.WinternitzEncodingTargetCollision
import all HashSig.GXMSS.Security.Reductions.TargetSumEncodingTargetCollision

/-!
# Encoding error and adaptive target-collision probes

One global singleton code and three randomizers distinguish returned failure from success:
zero fails, while one and two yield the same word. A stateful draw stream pins first-success
stopping and exhaustion. Transcript probes distinguish pair freshness, epoch locality, exhausted
record consumption and duplicate rejection. The adaptive adversary chooses its candidate randomizer
from the oracle's reply. These finite examples establish no concrete encoding security bound.
-/

public section

namespace GXMSS.Encoding.SecurityProbe

/-- The security retry entry point is definitionally the shared foundation computation. -/
theorem retry_eq_shared {m : Type → Type*} [Monad m]
    {PP M R E : Type} {n radix : ℕ} (enc : IncomparableEncoding PP M R E n radix)
    (sample : m R) (pp : PP) (msg : M) (ep : E) (k : ℕ) :
    TargetCollisionResistance.retry enc sample pp msg ep k = enc.retry sample pp msg ep k := rfl


open TargetCollisionResistance OracleComp OracleSpec

/-- The only codeword is the one-digit zero word. -/
@[expose] def word : Codeword 1 2 := fun _ => 0

/-- Zero randomness fails; either nonzero randomizer encodes to the same global word. -/
@[expose] def enc : IncomparableEncoding Bool Bool (Fin 3) Bool 1 2 where
  code := {word}
  incomparable := by
    intro x hx y hy hne
    exact (hne ((Set.mem_singleton_iff.mp hx).trans (Set.mem_singleton_iff.mp hy).symm)).elim
  encode _ _ r _ := if r = 0 then none else some ⟨word, by simp⟩

/-- Draw the next randomizer from an explicit stream; exhausted streams supply zero. -/
@[expose] def draw : StateM (List (Fin 3)) (Fin 3) := fun s =>
  match s with
  | [] => (0, [])
  | r :: rest => (r, rest)

/-- Encoding failure is a returned value, independently of any sampler divergence. -/
theorem returned_failure : enc.value false false 0 false = none := rfl

/-- A successful randomizer returns the singleton codeword. -/
theorem successful_encoding : enc.value false false 1 false = some word := rfl

/-- Zero retries neither draw nor change the randomizer stream. -/
theorem zero_retries :
    (retry enc draw false false false 0).run [1, 2] = (none, [1, 2]) := rfl

/-- The first success ends the retry loop before consuming the next randomizer. -/
theorem first_success :
    (retry enc draw false false false 3).run [0, 1, 2] =
      (some (word, 1), [2]) := rfl

/-- Exhaustion occurs after exactly the permitted failing draws. -/
theorem exhausted_retries :
    (retry enc draw false false false 2).run [0, 0, 1] = (none, [1]) := rfl

/-- An exhausted eligible query consumes one entry and its epoch. -/
theorem exhaustion_consumes_epoch :
    (finish 1 ([] : Transcript Bool (Fin 3) Bool 1 2) false false none).2 =
      [⟨false, false, none⟩] ∧
    used (finish 1 ([] : Transcript Bool (Fin 3) Bool 1 2) false false none).2 false = true :=
  ⟨rfl, rfl⟩

/-- A zero record budget returns failure without adding a record. -/
theorem zero_record_budget :
    finish 0 ([] : Transcript Bool (Fin 3) Bool 1 2) false false (some (word, 1)) =
      (none, []) := rfl

/-- A second request cannot replace even the message of an exhausted first request. -/
theorem duplicate_preserves_failure :
    finish 2 ([⟨false, false, none⟩] : Transcript Bool (Fin 3) Bool 1 2)
      true false (some (word, 1)) = (none, [⟨false, false, none⟩]) := rfl

/-- Same message and word with different randomness is a winning target collision. -/
theorem same_message_different_randomness :
    valid enc false [⟨false, false, some (word, 1)⟩] (false, 2, false) = true := by decide

/-- Replaying the exact message/randomness pair loses. -/
theorem exact_pair_replay :
    valid enc false [⟨false, false, some (word, 1)⟩] (false, 1, false) = false := by decide

/-- A target from another epoch cannot witness a collision. -/
theorem other_epoch_rejected :
    valid enc false [⟨false, false, some (word, 1)⟩] (false, 2, true) = false := by decide

/-- A failed record contains no successful word that could witness a collision. -/
theorem failed_record_loses :
    valid enc false [⟨false, false, none⟩] (false, 2, false) = false := by decide

/-- An explicit deterministic sampling instance isolates adaptive oracle behavior. -/
@[expose] def problem : Problem Bool Bool (Fin 3) Bool 1 2 where
  enc := enc
  paramGen := pure false
  randomGen := pure 1
  numRecords := 1
  numRetries := 1

/-- Ask the actual challenge oracle with explicitly fixed query and response types. -/
@[expose] def challenge (msg ep : Bool) :
    OracleComp (unifSpec + challengeSpec Bool (Fin 3) Bool 1 2)
      (Option (Codeword 1 2 × Fin 3)) :=
  liftM ((unifSpec + challengeSpec Bool (Fin 3) Bool 1 2).query (.inr (msg, ep)))

/-- The candidate randomizer depends on the returned challenge response. -/
@[expose] def adaptive : Adversary problem where
  find _ := do
    let answer ← challenge false false
    return (false, if answer.isSome then 2 else 0, false)

/-- The complete adaptive experiment returns a winning collision after a successful response. -/
theorem adaptive_success : experiment adaptive = pure true := rfl

/-- Zero retries still consume the epoch, but no failed target allows the adaptive collision. -/
@[expose] def zeroRetryProblem : Problem Bool Bool (Fin 3) Bool 1 2 :=
  { problem with numRetries := 0 }

/-- The actual zero-retry handler records exhaustion, distinguishing a dropped-record bug. -/
theorem handler_exhaustion_records :
    (challengeOracle zeroRetryProblem false (false, false)).run [] =
      pure (none, [⟨false, false, none⟩]) := rfl

/-- The actual handler rejects a duplicate and preserves its failed first record. -/
theorem handler_duplicate_preserves_failure :
    (challengeOracle problem false (true, false)).run [⟨false, false, none⟩] =
      pure (none, [⟨false, false, none⟩]) := rfl

/-- Returned failure lets the adversary continue with a different message at the same epoch. -/
@[expose] def afterFailure : Adversary zeroRetryProblem where
  find _ := do
    let _ ← challenge false false
    let _ ← challenge true false
    return (true, 2, false)

/-- Both failed and duplicate replies are data; the completed experiment returns a losing bit. -/
theorem adaptive_failure_continues : experiment afterFailure = pure false := rfl

/-- A zero target capacity rejects before any VCVio randomizer draw. -/
theorem hash_zero_capacity {PP M R E Tweak Y : Type} {n radix : ℕ}
    [SampleableType R] [DecidableEq Tweak]
    (bridge : TargetCollisionReduction.Bridge PP M R E Tweak Y n radix)
    (pp : PP) (ep : E) (msg : M) :
    (TweakableHash.SM_DT_RTCR_challengeOracle
      (TargetCollisionReduction.hashProblem bridge 0 1) pp (bridge.epochToTweak ep, msg)).run [] =
        pure (none, []) := by
  simp [TweakableHash.SM_DT_RTCR_challengeOracle, TargetCollisionReduction.hashProblem]

/-- The target game performs no draw at retry capacity zero. -/
theorem hash_zero_retry {PP M R E Tweak Y : Type} {n radix : ℕ}
    [SampleableType R]
    (bridge : TargetCollisionReduction.Bridge PP M R E Tweak Y n radix)
    (pp : PP) (ep : E) (msg : M) :
    TweakableHash.SM_DT_RTCR_resample
      (TargetCollisionReduction.hashProblem bridge 1 0) pp (bridge.epochToTweak ep) msg 0 =
        pure none := rfl

/-- A one-digit zero word fails a target-sum predicate of one. -/
theorem target_sum_invalid_word :
    TargetSumCollision.accepts (v := 1) (w := 1) (target := 1) word = false := by decide

/- Check the imported origins and complete axiom dependencies of the shared reduction,
its two encoding instances, and two supporting theorems. -/
run_cmd Lean.Elab.Command.liftTermElabM do
  let targets : List (Lean.Name × Lean.Name) := [
    (``GXMSS.Encoding.TargetCollisionReduction.advantage_le_hash,
      `HashSig.GXMSS.Security.Reductions.EncodingTargetCollisionReduction),
    (``GXMSS.Encoding.WinternitzCollision.advantage_le_hash,
      `HashSig.GXMSS.Security.Reductions.WinternitzEncodingTargetCollision),
    (``GXMSS.Encoding.TargetSumCollision.advantage_le_hash,
      `HashSig.GXMSS.Security.Reductions.TargetSumEncodingTargetCollision),
    (``GXMSS.Encoding.WinternitzCollision.word_injective,
      `HashSig.GXMSS.Security.Reductions.WinternitzEncodingTargetCollision),
    (``GXMSS.Encoding.TargetCollisionReduction.canonicalRandomizer_uniform,
      `HashSig.GXMSS.Security.Reductions.EncodingTargetCollisionReduction)]
  let env ← Lean.getEnv
  for target in targets do
    let name := target.1
    let expectedOrigin := target.2
    let some constInfo := env.find? name
      | throwError "{name} is missing from the imported environment"
    let .thmInfo info := constInfo
      | throwError "{name} is not an imported theorem"
    let some moduleIdx := env.getModuleIdxFor? name
      | throwError "{name} has no imported-module origin"
    let origin := env.header.moduleNames[moduleIdx.toNat]!
    unless origin == expectedOrigin do
      throwError "{name} originates in {origin}, not {expectedOrigin}"
    Lean.Meta.forallTelescope info.type fun _ result => do
      let resultType ← Lean.Meta.inferType result
      unless (← Lean.Meta.isDefEq resultType (Lean.mkSort Lean.Level.zero)) do
        throwError "{name} is not a universally closed proposition"
    let axioms ← Lean.collectAxioms name
    let allowed := [``propext, ``Classical.choice, ``Quot.sound]
    let unexpected := axioms.filter fun ax => !allowed.contains ax
    unless unexpected.isEmpty do
      throwError "unapproved transitive axioms for {name}: {unexpected.toList}"
    Lean.logInfo m!"Imported encoding theorem {name} origin: {origin}"
    Lean.logInfo m!"Imported encoding theorem {name} axioms: {axioms.toList}"

end GXMSS.Encoding.SecurityProbe
