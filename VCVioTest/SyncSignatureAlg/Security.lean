/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import VCVio.CryptoFoundations.SyncSignatureAlg.Security

/-!
# Synchronized-signature security distinguishing probes

Two Boolean epochs and messages suffice to distinguish exact pair replay, alternative valid
signatures, cross-epoch freshness and failed eligible requests. The deliberately insecure toy
verifier accepts both signatures, although its signer returns only one signature.
-/

public section

namespace SyncSignatureUnforgeability.Probe

open OracleComp OracleSpec

/-- A deterministic signer returns `false` except on the message `true`, which returns failure. -/
@[expose] def toy : SyncSignatureAlg ProbComp Bool Unit Unit Bool Bool where
  keygen := pure ((), ())
  sign _ _ msg := pure (if msg then none else some false)
  verify _ _ _ _ := true

/-- One successful request at epoch `false` and no request at epoch `true`. -/
@[expose] def signed : History Bool Bool Bool :=
  fun ep => if ep then none else some (false, some false)

/-- One failed eligible request at epoch `false`. -/
@[expose] def failed : History Bool Bool Bool :=
  fun ep => if ep then none else some (true, none)

/-- Exact replay loses both notions. -/
theorem replay_loses :
    strongValid toy ((), (false, false, false), signed) = false ∧
    valid toy ((), (false, false, false), signed) = false := by
  decide

/-- A different valid signature on the same epoch and message satisfies only strong validity. -/
theorem alternative_signature_valid_only_strong :
    strongValid toy ((), (false, false, true), signed) = true ∧
    valid toy ((), (false, false, true), signed) = false := by
  decide

/-- Requesting a message at another epoch does not spoil freshness at an unused epoch. -/
theorem cross_epoch_freshness :
    strongValid toy ((), (true, false, false), signed) = true ∧
    valid toy ((), (true, false, false), signed) = true := by
  decide

/-- Failure records the message: a later valid forgery for it wins only strong security. -/
theorem failed_message_valid_only_strong :
    strongValid toy ((), (false, true, true), failed) = true ∧
    valid toy ((), (false, true, true), failed) = false := by
  decide

/-- Both signatures verify despite the signer's deterministic successful answer. -/
theorem deterministic_does_not_imply_unique_valid :
    toy.sign () false false = pure (some false) ∧
    toy.verify () false false false = true ∧ toy.verify () false false true = true ∧
    (false : Bool) ≠ true := by
  simp [toy]

/-- A failed oracle answer is followed by a request at another epoch. -/
@[expose] def continueAfterFailure : OracleComp unifSpec
    (Option Bool × Option Bool × History Bool Bool Bool) := do
  let (first, history) ← signingOracle toy () (false, true) emptyHistory
  let (second, history) ← signingOracle toy () (true, false) history
  pure (first, second, history)

/-- The failed request consumes its epoch and successful interaction continues at the other one. -/
theorem failure_consumes_and_continues :
    continueAfterFailure = pure (none, some false,
      fun ep => if ep then some (false, some false) else some (true, none)) := by
  change (pure (none, some false,
    Function.update (Function.update emptyHistory false (some (true, none)))
      true (some (false, some false))) : ProbComp _) = _
  congr 3
  funext ep
  cases ep <;> rfl

/-- A repeated request after a failed request returns failure without overwriting the message. -/
theorem duplicate_failed_preserves :
    signingOracle toy () (false, false) failed = pure (none, failed) := by
  exact signingOracle_used toy () failed false false true none rfl

/-- A repeated request after success returns failure without overwriting the returned pair. -/
theorem duplicate_signed_preserves :
    signingOracle toy () (false, true) signed = pure (none, signed) := by
  exact signingOracle_used toy () signed false true false (some false) rfl

/-- The second query's epoch and message depend on the first optional response. -/
@[expose] def adaptive : Adversary unifSpec Unit Bool Bool Bool where
  forge _ := do
    let answer ← query (spec := unifSpec + signingSpec Bool Bool Bool)
      (Sum.inr (false, true))
    match answer with
    | none =>
      let second ← query (spec := unifSpec + signingSpec Bool Bool Bool)
        (Sum.inr (true, false))
      pure (true, false, second.getD true)
    | some sig => pure (false, true, sig)

/-- The adaptive interaction continues after failure and returns the later signed forgery. -/
theorem adaptive_failure_result :
    interaction toy adaptive = pure ((), (true, false, false),
      fun ep => if ep then some (false, some false) else some (true, none)) := by
  change (pure ((), (true, false, false),
    Function.update (Function.update emptyHistory false (some (true, none)))
      true (some (false, some false))) : ProbComp _) = _
  congr 4
  funext ep
  cases ep <;> rfl


universe u

variable {ι : Type u} {spec : OracleSpec ι}
variable {M PK SK S E : Type}

/-- The endpoint checks its winning predicate only after interpreting the shared interaction. -/
theorem unforgeableExp_post_runtime [DecidableEq E] [DecidableEq M]
    (alg : SyncSignatureAlg (OracleComp spec) M PK SK S E)
    (runtime : ProbCompRuntime (OracleComp spec)) (adv : Adversary spec PK E M S) :
    unforgeableExp alg runtime adv =
      runtime.evalDist (valid alg <$> interaction alg adv) := rfl

/-- The endpoint checks its winning predicate only after interpreting the shared interaction. -/
theorem strongUnforgeableExp_post_runtime [DecidableEq E] [DecidableEq M] [DecidableEq S]
    (alg : SyncSignatureAlg (OracleComp spec) M PK SK S E)
    (runtime : ProbCompRuntime (OracleComp spec)) (adv : Adversary spec PK E M S) :
    strongUnforgeableExp alg runtime adv =
      runtime.evalDist (strongValid alg <$> interaction alg adv) := rfl

end SyncSignatureUnforgeability.Probe
