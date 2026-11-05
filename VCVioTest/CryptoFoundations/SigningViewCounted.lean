/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import VCVio.CryptoFoundations.SignatureAlg.CountedExperiment
public import VCVio.OracleComp.QueryTracking.ListCache
public import Mathlib.Algebra.FreeMonoid.Basic

/-!
# Ordered signing-experiment observations

Runtime checks retain every source coordinate and the chronological input-dependent policy
trace. Rejected requests, repeated queries, uniform samples and warm caches exercise the same
counted experiment with distinct declared policies.
-/

public section

namespace VCVioTest.CryptoFoundations.SigningViewCounted

open OracleComp OracleSpec SignatureAlg.SigningView

private abbrev HashSpec := Nat →ₒ Nat
private abbrev World := unifSpec + HashSpec
private abbrev Cost := Nat × FreeAddMonoid (Nat × Nat)

private def phaseCode : Phase → Nat
  | .keygen => 1 | .adversary => 2 | .signer => 3 | .verification => 4

private def policy : Event World Nat → Cost
  | .ambient phase (.inl n) => (0, .of (phaseCode phase, 1000 + n))
  | .ambient phase (.inr input) =>
    (10 * phaseCode phase + input, .of (phaseCode phase, input))
  | .signingAttempt request => (7 + request, .of (5, request))

private def hash (input : Nat) : OracleComp World Nat := query (spec := HashSpec) input

private def scheme : SignatureAlg.SigningView (OracleComp World) Nat Unit Unit Nat (Except Nat Nat)
    where
  keygen := do
    let _ ← hash 1
    return ((), ())
  sign _ _ request := if request = 0 then pure (.error 2) else do
    let _ ← hash 3
    let _ ← hash 3
    return .ok (request + 10)
  verify _ request _ := if request = 0 then pure false else do
    let _ ← hash 5
    return true
  readback := Except.toOption

private def adversary (_ : Unit) : OracleComp (World + (Nat →ₒ Except Nat Nat)) (Nat × Nat) := do
  let _ ← query (spec := unifSpec) 0
  let _ ← query (spec := unifSpec) 0
  let rejected ← query (spec := Nat →ₒ Except Nat Nat) 0
  let input := match rejected with | .error code => code | .ok _ => 99
  let first : Nat ← query (spec := HashSpec) input
  let second : Nat ← query (spec := HashSpec) input
  let _ ← query (spec := Nat →ₒ Except Nat Nat) 1
  return (1, first + second)

private def handler : QueryImpl World (StateT (List (Nat × Nat)) Id)
  | .inl n => fun cache => pure (⟨0, Nat.zero_lt_succ n⟩, cache)
  | .inr input => QueryImpl.ListCache.handler (m := Id) (fun n => pure (n + 100)) input

private def uniformPolicy : Event World Nat → Cost
  | .ambient phase (.inl n) => (n + 1, .of (phaseCode phase, 1000 + n))
  | event => policy event

private abbrev SourceCounts := (Phase ⊕ Unit) → Nat

private def sourcePolicy : Event World Nat → SourceCounts
  | .ambient _ (.inl _) => 0
  | .ambient phase (.inr _) => Pi.single (.inl phase) 1
  | .signingAttempt _ => Pi.single (.inr ()) 1

private def runFrom (initial : List (Nat × Nat)) :
    Observation Nat Nat (Except Nat Nat) Cost × List (Nat × Nat) :=
  (simulateQ handler (countedExperiment policy scheme adversary)).run initial

private def check (test : Bool) (message : String) : IO Unit :=
  unless test do throw (IO.userError message)

/-- Execute finite checks of the complete outcome, ordered cost and shared-cache observations. -/
def run : IO Unit := do
  let (outcome, cache) := runFrom []
  check (outcome.forgery == (1, 204) && outcome.verified &&
    decide (outcome.rawLog = [⟨0, .error 2⟩, ⟨1, .ok 11⟩]) && outcome.cost.1 == 181 &&
    outcome.cost.2.toList ==
      [(1, 1), (2, 1000), (2, 1000), (5, 0), (2, 2), (2, 2),
        (5, 1), (3, 3), (3, 3), (4, 5)] &&
    cache == [(5, 105), (3, 103), (2, 102), (1, 101)])
    "cold joint outcome, tagged error, noncommutative cost and cache"
  let (source, _) := (simulateQ handler (countedExperiment sourcePolicy scheme adversary)).run []
  let counts := source.cost
  check (counts (.inl .keygen) == 1 && counts (.inl .adversary) == 2 &&
    counts (.inl .signer) == 2 && counts (.inl .verification) == 1 && counts (.inr ()) == 2)
    "all phase coordinates include repeated physical calls and the rejected attempt"
  let (uniformCharged, uniformCache) := (simulateQ handler
    (countedExperiment uniformPolicy scheme adversary)).run []
  check (uniformCharged.cost.1 == 183 && uniformCharged.cost.2.toList == outcome.cost.2.toList &&
    uniformCharged.forgery == outcome.forgery && uniformCharged.verified == outcome.verified &&
    decide (uniformCharged.rawLog = outcome.rawLog) && uniformCache == cache)
    "charging uniform replies retains the same whole outcome and cache"
  let (warm, warmCache) := runFrom [(9, 109), (2, 909)]
  check (warm.forgery == (1, 1818) && warm.verified &&
    decide (warm.rawLog = outcome.rawLog) && warm.cost.1 == 181 &&
    warm.cost.2.toList == outcome.cost.2.toList &&
    warmCache == [(5, 105), (3, 103), (1, 101), (9, 109), (2, 909)])
    "both warm replies affect the candidate and remain charged; unrelated cache entry retained"
  check (decide (returnedPairs Except.toOption outcome.rawLog = [(1, 11)]))
    "normal errors remain raw log data but have no successful readback"
  IO.println "Signing-view joint error, ordered-cost, warm-cache and phase-policy controls: PASS"

end VCVioTest.CryptoFoundations.SigningViewCounted
