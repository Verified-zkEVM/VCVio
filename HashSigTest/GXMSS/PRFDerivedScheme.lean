/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.PRFDerivedScheme
public import HashSigTest.GXMSS.Scheme

/-! # Shared-response PRF-derived construction controls

Typed seed/start/retry coordinates and the concrete retry transcript exercise the shared-response
construction, reusing the direct scheme fixtures.
-/

public section

namespace GXMSS.Probe

/-! ## Shared-seed derived construction -/

/-- The public parameter distinguishes otherwise identical start queries. -/
theorem shared_seed_start_parameter_distinct :
    (GXMSS.PRFDerived.Query.start false 2 0 :
      GXMSS.PRFDerived.Query Bool Unit 3 1) ≠
        .start true 2 0 := by
  intro equality
  exact Bool.false_ne_true
    ((GXMSS.PRFDerived.start_eq_iff false true 2 2 0 0).mp equality).1

/-- The public parameter also distinguishes otherwise identical retry queries. -/
theorem shared_seed_retry_parameter_distinct :
    (GXMSS.PRFDerived.Query.retry false 2 () 0 :
      GXMSS.PRFDerived.Query Bool Unit 3 1) ≠
        .retry true 2 () 0 := by
  intro equality
  exact Bool.false_ne_true
    ((GXMSS.PRFDerived.retry_eq_iff false true 2 2 () () 0 0).mp equality).1

/-- A single-domain toy response contains both interpreted values. -/
@[expose] def sharedSeedEvaluator :
    GXMSS.PRFDerived.Evaluator Bool Unit Unit (List ℕ × Bool) 3 1
  | _, .publicSeed => ([], false)
  | _, .start _ epoch _ => ([90 + epoch.val], false)
  | _, .retry _ _ _ attempt => ([], attempt == 1 || attempt == 2)

/-- The query family selects the relevant view of the one response domain. -/
@[expose] def sharedSeedInterpretation :
    GXMSS.PRFDerived.Interpretation Unit (List ℕ) Bool (List ℕ × Bool) where
  publicParameter := fun _ => ()
  chainStart := Prod.fst
  retryRandomizer := Prod.snd

/-- Transient starts use the same public parameter as the public key. -/
theorem shared_seed_start_at_epoch_two :
    (GXMSS.PRFDerived.transientCore (ChainProbe.traceInstance 3 3)
      sharedSeedEvaluator sharedSeedInterpretation true).starts 2 0 = [92] := rfl

/-- The returned secret key is exactly the sampled evaluator key. -/
theorem shared_seed_only_secret_key :
    (GXMSS.PRFDerived.keys (ChainProbe.traceInstance 3 3)
      sharedSeedEvaluator sharedSeedInterpretation true).2 = true := rfl

/-- The derived queries are ordered by their zero-based attempt, including a
later successful value that first-success signing must leave unconsumed. -/
theorem shared_seed_retry_order :
    GXMSS.PRFDerived.retryRandomizers 3 sharedSeedEvaluator
      sharedSeedInterpretation true () 2 () = [false, true, true] := rfl

/-- First success records its one-based attempt and the complete ordered consumed prefix. -/
theorem shared_seed_retry_success :
    let sk := (GXMSS.PRFDerived.keys (ChainProbe.traceInstance 3 3)
      sharedSeedEvaluator sharedSeedInterpretation true).2
    let transition := GXMSS.PRFDerived.run 3 sharedSeedEvaluator sharedSeedInterpretation
      (ChainProbe.traceInstance 3 3) enc sk 2 ()
    let result := transition.result
    result.attempt? = some 2 ∧
      result.consumed = [false, true] ∧ transition.epoch = 2 := by
  exact ⟨rfl, rfl, rfl⟩

/-- Zero retries return exhaustion while recording the spent epoch. -/
theorem shared_seed_retry_exhaustion :
    let sk := (GXMSS.PRFDerived.keys (ChainProbe.traceInstance 3 3)
      sharedSeedEvaluator sharedSeedInterpretation true).2
    let transition := GXMSS.PRFDerived.run 0 sharedSeedEvaluator sharedSeedInterpretation
      (ChainProbe.traceInstance 3 3) enc sk 2 ()
    let result := transition.result
    result.output.isNone = true ∧
      result.consumed = [] ∧ transition.epoch = 2 := by
  exact ⟨rfl, rfl, rfl⟩

/-- The full eager list distinguishes all three queried attempt coordinates. -/
theorem shared_seed_retry_coordinates :
    GXMSS.PRFDerived.retryCoordinates (h := 3) (v := 1) 3 () 2 () =
      [.retry () 2 () 0, .retry () 2 () 1, .retry () 2 () 2] := rfl

/-- Every failed retry is retained in the exhaustion transcript. -/
theorem shared_seed_nonempty_exhaustion :
    let sk := GXMSS.PRFDerived.transientCore (ChainProbe.traceInstance 3 3)
      sharedSeedEvaluator sharedSeedInterpretation true
    let result := GXMSS.PRFDerived.signResult (ChainProbe.traceInstance 3 3) enc sk 2 ()
      [false, false, false]
    result.output = none ∧ result.attempt? = none ∧
      result.consumed = [false, false, false] := by
  exact ⟨rfl, rfl, rfl⟩

/-- The first successful draw leaves both later eagerly derived randomizers unconsumed. -/
theorem shared_seed_first_success :
    let sk := GXMSS.PRFDerived.transientCore (ChainProbe.traceInstance 3 3)
      sharedSeedEvaluator sharedSeedInterpretation true
    let result := GXMSS.PRFDerived.signResult (ChainProbe.traceInstance 3 3) enc sk 2 ()
      [true, false, true]
    result.attempt? = some 1 ∧ result.consumed = [true] ∧ result.output.isSome = true := by
  exact ⟨rfl, rfl, rfl⟩

end GXMSS.Probe
