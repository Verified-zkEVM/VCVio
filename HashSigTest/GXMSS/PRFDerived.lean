/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSigTest.GXMSS.Scheme
public import HashSig.GXMSS.PRFDerived

/-!
# PRF-derived GXMSS construction tests

Typed queries, the one-key derivation, and finite indexed retry behavior are checked with
an evaluator whose later successful response remains available after first success.
-/

public section

namespace GXMSS.PRFDerivedProbe

open GXMSS.Encoding IncomparableEncoding

/-- The seed query has its own constructor, disjoint from either indexed family. -/
theorem public_seed_query_disjoint :
    (PRFDerived.Query.publicSeed : PRFDerived.Query Bool Unit 3 1) ≠
      .start false 2 0 ∧
    (PRFDerived.Query.publicSeed : PRFDerived.Query Bool Unit 3 1) ≠
      .retry false 2 () 0 := by
  exact ⟨PRFDerived.publicSeed_ne_start false 2 0,
    PRFDerived.publicSeed_ne_retry false 2 () 0⟩

/-- The public parameter distinguishes otherwise identical start queries. -/
theorem shared_seed_start_parameter_distinct :
    (PRFDerived.Query.start false 2 0 : PRFDerived.Query Bool Unit 3 1) ≠
      .start true 2 0 := by
  intro equality
  exact Bool.false_ne_true
    ((PRFDerived.start_eq_iff false true 2 2 0 0).mp equality).1

/-- The public parameter also distinguishes otherwise identical retry queries. -/
theorem shared_seed_retry_parameter_distinct :
    (PRFDerived.Query.retry false 2 () 0 : PRFDerived.Query Bool Unit 3 1) ≠
      .retry true 2 () 0 := by
  intro equality
  exact Bool.false_ne_true
    ((PRFDerived.retry_eq_iff false true 2 2 () () 0 0).mp equality).1

/-- A single response domain carries the public parameter, start, and retry values. -/
@[expose] def sharedSeedEvaluator :
    PRFDerived.Evaluator Bool Unit Unit (List ℕ × Bool) 3 1
  | _, .publicSeed => ([], false)
  | _, .start _ epoch _ => ([90 + epoch.val], false)
  | _, .retry _ _ _ attempt => ([], attempt == 1 || attempt == 2)

/-- All three views read the same keyed response type. -/
@[expose] def sharedSeedInterpretation :
    PRFDerived.Interpretation Unit (List ℕ) Bool (List ℕ × Bool) where
  publicParameter := fun _ => ()
  chainStart := Prod.fst
  retryRandomizer := Prod.snd

/-- Transient starts use the parameter derived for the public key. -/
theorem shared_seed_start_at_epoch_two :
    (PRFDerived.transientCore (GXMSS.ChainProbe.traceInstance 3 3)
      sharedSeedEvaluator sharedSeedInterpretation true).starts 2 0 = [92] := rfl

/-- The returned secret key is exactly the sampled evaluator key. -/
theorem shared_seed_only_secret_key :
    (PRFDerived.keys (GXMSS.ChainProbe.traceInstance 3 3)
      sharedSeedEvaluator sharedSeedInterpretation true).2 = true := rfl

/-- Zero-based queries yield the exact ordered attempt sequence. -/
theorem shared_seed_retry_order :
    PRFDerived.retryRandomizers 3 sharedSeedEvaluator
      sharedSeedInterpretation true () 2 () = [false, true, true] := rfl

/-- The second attempt succeeds and the third derived value remains unconsumed. -/
theorem shared_seed_retry_success :
    let sk := (PRFDerived.keys (GXMSS.ChainProbe.traceInstance 3 3)
      sharedSeedEvaluator sharedSeedInterpretation true).2
    let transition := PRFDerived.run 3 sharedSeedEvaluator sharedSeedInterpretation
      (GXMSS.ChainProbe.traceInstance 3 3) GXMSS.Probe.enc sk 2 ()
    let result := transition.result
    result.successfulAttempt = some 2 ∧
      result.consumed = [false, true] ∧ transition.epoch = 2 := by
  exact ⟨rfl, rfl, rfl⟩

/-- A false attempt-prefix observation cannot satisfy the successful trace. -/
theorem shared_seed_retry_prefix_negative :
    let sk := (PRFDerived.keys (GXMSS.ChainProbe.traceInstance 3 3)
      sharedSeedEvaluator sharedSeedInterpretation true).2
    let transition := PRFDerived.run 3 sharedSeedEvaluator sharedSeedInterpretation
      (GXMSS.ChainProbe.traceInstance 3 3) GXMSS.Probe.enc sk 2 ()
    transition.result.consumed ≠ [true, false] := by
  decide

/-- A later successful value does not enter the consumed attempt prefix. -/
theorem shared_seed_retry_tail_unconsumed :
    let sk := (PRFDerived.keys (GXMSS.ChainProbe.traceInstance 3 3)
      sharedSeedEvaluator sharedSeedInterpretation true).2
    let transition := PRFDerived.run 3 sharedSeedEvaluator sharedSeedInterpretation
      (GXMSS.ChainProbe.traceInstance 3 3) GXMSS.Probe.enc sk 2 ()
    transition.result.consumed ≠ [false, true, true] := by
  decide

/-- The same response type can supply an all-failing retry sequence. -/
@[expose] def allFailEvaluator :
    PRFDerived.Evaluator Bool Unit Unit (List ℕ × Bool) 3 1
  | _, .publicSeed => ([], false)
  | _, .start _ epoch _ => ([90 + epoch.val], false)
  | _, .retry _ _ _ _ => ([], false)

/-- A positive budget exhausts only after consuming every derived attempt. -/
theorem shared_seed_retry_full_exhaustion :
    let sk := (PRFDerived.keys (GXMSS.ChainProbe.traceInstance 3 3)
      allFailEvaluator sharedSeedInterpretation true).2
    let transition := PRFDerived.run 3 allFailEvaluator sharedSeedInterpretation
      (GXMSS.ChainProbe.traceInstance 3 3) GXMSS.Probe.enc sk 2 ()
    let result := transition.result
    result.isExhausted = true ∧
      result.consumed = [false, false, false] ∧ transition.epoch = 2 := by
  exact ⟨rfl, rfl, rfl⟩

/-- Zero retries return exhaustion while still recording the spent epoch. -/
theorem shared_seed_retry_exhaustion :
    let sk := (PRFDerived.keys (GXMSS.ChainProbe.traceInstance 3 3)
      sharedSeedEvaluator sharedSeedInterpretation true).2
    let transition := PRFDerived.run 0 sharedSeedEvaluator sharedSeedInterpretation
      (GXMSS.ChainProbe.traceInstance 3 3) GXMSS.Probe.enc sk 2 ()
    let result := transition.result
    result.isExhausted = true ∧
      result.consumed = [] ∧ transition.epoch = 2 := by
  exact ⟨rfl, rfl, rfl⟩

/-! ## Indexed retry controls -/

/-- The second indexed attempt succeeds with its one-based index and exact prefix. -/
theorem indexed_second_attempt_trace :
    GXMSS.Encoding.RetryProbe.enc.retryIndexed (m := Id) () () () 3
      (fun i => i.val == 1) =
        IncomparableEncoding.IndexedResult.success
          GXMSS.Encoding.RetryProbe.word true 2 [false, true] := rfl

/-- The observed success cannot be confused with the first-attempt trace. -/
theorem indexed_second_attempt_not_first :
    GXMSS.Encoding.RetryProbe.enc.retryIndexed (m := Id) () () () 3
      (fun i => i.val == 1) ≠
        IncomparableEncoding.IndexedResult.success
          GXMSS.Encoding.RetryProbe.word true 1 [true] := by
  intro equality
  have impossible : (2 : ℕ) = 1 := by
    simpa only [indexed_second_attempt_trace] using
      congrArg (fun result : IncomparableEncoding.IndexedResult Bool 1 2 =>
        match result with
        | .success _ _ attempt _ => attempt
        | .exhausted _ => 0) equality
  omega

/-- A zero budget does not evaluate an indexed sampler. -/
theorem indexed_zero_trace :
    GXMSS.Encoding.RetryProbe.enc.retryIndexed (m := Id) () () () 0
      (fun i => nomatch i) =
        IncomparableEncoding.IndexedResult.exhausted [] := rfl

/-- Positive-budget exhaustion retains all three ordered failed attempts. -/
theorem indexed_exhaustion_trace :
    GXMSS.Encoding.RetryProbe.enc.retryIndexed (m := Id) () () () 3
      (fun i => (i.val == 0) && false) =
        IncomparableEncoding.IndexedResult.exhausted [false, false, false] := rfl

/-- The fixed sampler has the indexed operation's exact output observation. -/
theorem fixed_sampler_specialization :
    (GXMSS.Encoding.RetryProbe.enc.retry GXMSS.Encoding.RetryProbe.draw () () () 3).run
      [false, true, false] =
    (IncomparableEncoding.IndexedResult.output <$>
      GXMSS.Encoding.RetryProbe.enc.retryIndexed () () () 3
        (fun _ => GXMSS.Encoding.RetryProbe.draw)).run [false, true, false] := by
  rw [GXMSS.Encoding.RetryProbe.enc.retry_eq_indexed_constant
    GXMSS.Encoding.RetryProbe.draw () () () 3]

end GXMSS.PRFDerivedProbe
