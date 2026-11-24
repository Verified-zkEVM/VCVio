/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import VCVio.CryptoFoundations.SyncSignatureAlg.Unforgeability
public import VCVio.OracleComp.Constructions.SampleableType.Measure
public import VCVio.EvalDist.Instances.OptionT

/-!
# Actual signing callback and full-record controls

The canonical callback returns optional signatures with correlated randomizer, OTS and path fields.
An optional-effect variant aborts on a selected active message. Its run observation distinguishes
an abort from a returned signing failure, while repeated requests skip the callback entirely.
-/

public section
namespace VCVioTest.SigningKernel
open OracleSpec OracleComp SyncSignatureUnforgeability

/-- Randomizer, one OTS value and one authentication label. -/
abbrev Payload := Bool × Bool × Bool

/-- A canonical callback with a genuinely random complete successful payload. -/
@[expose] def kernel (ep msg : Bool) : ProbComp (Option Payload) :=
  if ep then
    if msg then pure none
    else do
      let randomizer ← $ᵗ Bool
      pure (some (randomizer, randomizer, true))
  else pure none

/-- The complete successful signature ties its OTS field to its randomizer and fixes its path. -/
@[expose] def FullPayload (ep msg : Bool) (sig : Payload) : Prop :=
  ep = true ∧ msg = false ∧ sig.2.1 = sig.1 ∧ sig.2.2 = true

/-- Every actual successful callback output satisfies the entire payload predicate. -/
theorem kernel_full (ep msg : Bool) (sig : Payload)
    (hs : some sig ∈ support (kernel ep msg)) : FullPayload ep msg sig := by
  cases ep with
  | false => simp [kernel] at hs
  | true =>
    cases msg with
    | true => simp [kernel] at hs
    | false =>
      change some sig ∈ support (do
        let r ← ($ᵗ Bool : ProbComp Bool)
        pure (some (r, r, true))) at hs
      rw [mem_support_bind_iff] at hs
      obtain ⟨r, _, hr⟩ := hs
      simp only [support_pure, Set.mem_singleton_iff, Option.some.injEq] at hr
      subst sig
      exact ⟨rfl, rfl, rfl, rfl⟩

/-- Returned failure consumes the epoch and retains its original message. -/
theorem returned_failure_records :
    signingKernelOracle kernel (false, false) emptyHistory =
      pure (none, Function.update emptyHistory false (some (false, none))) := by
  rw [signingKernelOracle_unused _ _ _ _ rfl]
  rfl

/-- Optional effects additionally permit an actual abort before returning a signing result. -/
@[expose] def partialKernel (ep msg : Bool) : OptionT ProbComp (Option Payload) :=
  if ep && msg then failure else liftM (kernel ep msg)

/-- Optional-effect returned failure still returns a complete updated history. -/
theorem optional_failure_records :
    (signingKernelOracle partialKernel (false, false) emptyHistory).run =
      pure (some (none, Function.update emptyHistory false (some (false, none)))) := by
  rw [signingKernelOracle_unused _ _ _ _ rfl]
  rfl

/-- The optional run observation has no returned pair after an actual fresh abort. -/
theorem fresh_abort :
    (signingKernelOracle partialKernel (true, true) emptyHistory).run = pure none := by
  rw [signingKernelOracle_unused _ _ _ _ rfl]
  rfl

/-- The same aborting callback is skipped after an already consumed successful epoch. -/
theorem duplicate_skips_abort :
    let history : History Bool Bool Payload :=
      Function.update emptyHistory true (some (false, some (false, false, true)))
    (signingKernelOracle partialKernel (true, true) history).run =
      pure (some (none, history)) := by
  dsimp only
  exact congrArg (fun out : OptionT ProbComp (Option Payload × History Bool Bool Payload) =>
    out.run) (signingKernelOracle_used partialKernel _ true true false
      (some (false, false, true)) (by rfl))

/-- Ambient oracle effects pass through the common runner while retaining the full history. -/
theorem ambient_forwarded :
    runWithSigningKernel kernel
      (OracleComp.liftComp ($ᵗ Bool : ProbComp Bool) (unifSpec + signingSpec Bool Bool Payload))
      emptyHistory = (fun b => (b, emptyHistory)) <$> ($ᵗ Bool : ProbComp Bool) := by
  unfold runWithSigningKernel oraclesWithSigningKernel
  rw [QueryImpl.simulateQ_add_liftComp_left, simulateQ_liftTarget, QueryImpl.simulateQ_toQueryImpl]
  simp

/-- Actual mixed programs preserve the full signature predicate, not just successful decoding. -/
theorem run_full {A : Type}
    (program : OracleComp (unifSpec + signingSpec Bool Bool Payload) A)
    (out : A × History Bool Bool Payload)
    (hout : out ∈ support (runWithSigningKernel kernel program emptyHistory)) :
    SuccessfulHistorySatisfies FullPayload out.2 :=
  runWithSigningKernel_preserves_successfulHistorySatisfies kernel FullPayload kernel_full
    program emptyHistory (successfulHistorySatisfies_empty _) out hout

end VCVioTest.SigningKernel
