/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: VCVio Contributors
-/

module
public import VCVio.CryptoFoundations.SignatureAlg.CountedExperiment.Realization
public import Mathlib.Algebra.FreeMonoid.Basic

/-!
# A dependent two-query realization with ordered costs

A macro port expands into two physical target queries in a fixed order.
An injected adaptive client still receives the same raw error or successful reply.
The target secret-key carrier is arbitrary, while the source stores only Unit.
-/

public section

namespace VCVioTest.CryptoFoundations.SigningViewCountedRealization

open OracleComp OracleSpec SignatureAlg SignatureAlg.SigningView

/-- A target query returns a finite value whose bound depends on its natural-number index. -/
abbrev Target := OracleSpec.ofFn (fun q : Nat × Bool => Fin (q.1 + 1))
/-- One source macro returns the first of two equally indexed target replies. -/
abbrev Macro := OracleSpec.ofFn (fun n : Nat => Fin (n + 1))
/-- The source exposes both the original target ports and a two-call macro port. -/
abbrev Source := Target + Macro
/-- Ordered Boolean words record charges without a commutativity law. -/
abbrev Cost := FreeAddMonoid Bool
/-- A normal signing rejection is distinct from a successful candidate signature. -/
abbrev Reply := Except Unit Nat

/-- Interpret a macro by querying the false-labelled port before the true-labelled port. -/
def expand : QueryImpl Source (OracleComp Target)
  | .inl q => liftM (Target.query q)
  | .inr n => do
    let first ← Target.query (n, false)
    let _ ← Target.query (n, true)
    return first

/-- Give the original client access only to the forwarded target ports. -/
def inject : QueryImpl Target (OracleComp Source) := fun q =>
  liftM (Source.query (.inl q))

/-- Every target call contributes its label, and signing attempts contribute no label. -/
def targetCost : Event Target Nat → Cost
  | .ambient _ (_, bit) => FreeAddMonoid.of bit
  | .signingAttempt _ => 0

/-- A macro contributes both labels while a forwarded query contributes one label. -/
def sourceCost : Event Source Nat → Cost
  | .ambient _ (.inl (_, bit)) => FreeAddMonoid.of bit
  | .ambient _ (.inr _) => FreeAddMonoid.of false + FreeAddMonoid.of true
  | .signingAttempt _ => 0

-- The macro's source charge is exactly the two target charges, in chronological order.
theorem expansion_cost (phase : Phase) (q : Source.Domain) :
    costed targetCost phase (expand q) = (do
      AddWriterT.addTell (sourceCost (.ambient phase q)); liftM (expand q)) := by
  cases q with
  | inl q =>
    simp [expand, costed_query, sourceCost, targetCost]
  | inr n =>
    apply WriterT.ext
    simp [expand, costed_bind, costed_query, costed_pure, sourceCost, targetCost,
      WriterT.run_bind, monad_norm]

theorem injection_left_inverse : expand ∘ₛ inject = QueryImpl.id' Target := by
  funext q
  simp [QueryImpl.apply_compose, inject, expand]

/-- A Unit-keyed service rejects even requests and answers odd requests through a macro. -/
def sourceView (pk : Nat) : SigningView (OracleComp Source) Nat Nat Unit Nat Reply where
  keygen := pure (pk, ())
  sign _ _ request := if request % 2 = 0 then pure (.error ()) else do
    let first ← Source.query (.inr (request + 1))
    return .ok first.val
  verify key request sig := pure (decide (sig ≤ key + request))
  readback reply := match reply with | .error _ => none | .ok sig => some sig

/-- The target service uses an arbitrary fixed key and makes its two calls explicitly. -/
def targetView {SK : Type} (pk : Nat) (fixedKey : SK) :
    SigningView (OracleComp Target) Nat Nat SK Nat Reply where
  keygen := pure (pk, fixedKey)
  sign _ _ request := if request % 2 = 0 then pure (.error ()) else do
    let first ← Target.query (request + 1, false)
    let _ ← Target.query (request + 1, true)
    return .ok first.val
  verify key request sig := pure (decide (sig ≤ key + request))
  readback reply := match reply with | .error _ => none | .ok sig => some sig

-- This client observes a normal signing error before choosing its next request adaptively.
/-- An error-aware client chooses an odd signing request from a dependent target reply. -/
def adaptiveA (pk : Nat) : OracleComp (Target + (Nat →ₒ Reply)) (Nat × Nat) := do
  let rejected ← (Target + (Nat →ₒ Reply)).query (.inr 0)
  let choice ← (Target + (Nat →ₒ Reply)).query (.inl (pk + 1, false))
  let request := 2 * choice.val + 1
  let reply ← (Target + (Nat →ₒ Reply)).query (.inr request)
  return (request + 2, match rejected, reply with
    | .error _, .ok sig => sig
    | _, _ => 0)

/-- The same named adaptive client retains its complete observation and ordered cost. -/
theorem adaptive_realization {SK : Type} (pk : Nat) (fixedKey : SK) :
    simulateQ expand (countedExperiment sourceCost (sourceView pk)
      (fun key => simulateQ (inject.addLift (QueryImpl.id' (Nat →ₒ Reply))) (adaptiveA key))) =
      countedExperiment targetCost (targetView pk fixedKey) adaptiveA := by
  apply countedExperiment_realize_injected expand inject injection_left_inverse
    sourceCost targetCost (sourceView pk) (targetView pk fixedKey) (fun _ => fixedKey)
  · exact expansion_cost
  · intro request
    rfl
  · simp [sourceView, targetView]
  · intro key sk request
    simp [sourceView, targetView, expand, apply_ite]
  · intro key request sig
    simp [sourceView, targetView]

/-- Any full-state handler and continuation observe the exact same joint endpoint. -/
theorem full_state_continuation {SK State β : Type} {m : Type → Type}
    [Monad m] [LawfulMonad m] (pk : Nat) (fixedKey : SK)
    (handler : QueryImpl Target (StateT State m)) (initial : State)
    (finish : Observation Nat Nat Reply Cost × State → m β) :
    ((simulateQ (handler ∘ₛ expand) (countedExperiment sourceCost (sourceView pk)
      (fun key => simulateQ (inject.addLift (QueryImpl.id' (Nat →ₒ Reply)))
        (adaptiveA key)))).run initial >>= finish) =
      ((simulateQ handler (countedExperiment targetCost (targetView pk fixedKey)
        adaptiveA)).run initial >>= finish) := by
  rw [QueryImpl.simulateQ_compose, adaptive_realization pk fixedKey]

end VCVioTest.CryptoFoundations.SigningViewCountedRealization
