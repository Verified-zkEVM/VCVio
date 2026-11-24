/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import VCVio.CryptoFoundations.IncomparableEncoding.TargetCollisionReduction

/-!
# Encoding target-collision game tests

A one-word code and three randomizers separate encoding failure, pair freshness and repeated-epoch
rejection. The adaptive adversaries choose their collision after seeing the oracle's replies.
-/

public section

namespace IncomparableEncoding.TargetCollisionProbe

open TargetCollisionResistance OracleComp OracleSpec

/-- The only codeword is the one-digit zero word. -/
@[expose] def word : Codeword 1 2 := fun _ => 0

/-- Zero randomness fails; either nonzero randomizer encodes to the same global word. -/
@[expose] def enc : IncomparableEncoding Bool Bool (Fin 3) Bool 1 2 where
  code := {word}
  incomparable := by
    intro x hx y hy hne
    exact (hne ((Set.mem_singleton_iff.mp hx).trans (Set.mem_singleton_iff.mp hy).symm)).elim
  encode _ _ r _ := if r = 0 then none else some word
  mem_code_of_encode_eq_some := by
    intro _ _ r _ x h
    split at h <;> simp_all [eq_comm]

/-- Draw the next randomizer from an explicit stream; exhausted streams supply zero. -/
@[expose] def draw : StateM (List (Fin 3)) (Fin 3) := fun s =>
  match s with
  | [] => (0, [])
  | r :: rest => (r, rest)

/-- Encoding failure is a returned value, independently of any sampler divergence. -/
theorem returned_failure : enc.encode false false 0 false = none := rfl

/-- A successful randomizer returns the singleton codeword. -/
theorem successful_encoding : enc.encode false false 1 false = some word := rfl

/-- The first success ends the retry loop before consuming the next randomizer. -/
theorem first_success :
    (enc.retry draw false false false 3).run [0, 1, 2] =
      (some (word, 1), [2]) := rfl

/-- Exhaustion occurs after exactly the permitted failing draws. -/
theorem exhausted_retries :
    (enc.retry draw false false false 2).run [0, 0, 1] = (none, [1]) := rfl

/-- An exhausted eligible query consumes one entry and its epoch. -/
theorem exhaustion_consumes_epoch :
    (finish 1 ([] : Transcript Bool (Fin 3) Bool 1 2) false false none).2 =
      [⟨false, false, none⟩] ∧
    used (finish 1 ([] : Transcript Bool (Fin 3) Bool 1 2) false false none).2 false = true :=
  ⟨rfl, rfl⟩

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

end IncomparableEncoding.TargetCollisionProbe
