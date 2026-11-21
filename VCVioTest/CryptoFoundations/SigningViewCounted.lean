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
trace. Rejected requests, repeated queries, private samples and warm caches exercise the same
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

private def scheme : SignatureAlg.SigningView (OracleComp World) Nat Unit Unit Nat (Option Nat)
    where
  keygen := do
    let _ ← hash 1
    return ((), ())
  sign _ _ request := if request = 0 then pure none else do
    let _ ← hash 3
    let _ ← hash 3
    return some (request + 10)
  verify _ request _ := if request = 0 then pure false else do
    let _ ← hash 5
    return true
  readback := id

private def adversary (_ : Unit) : OracleComp (World + (Nat →ₒ Option Nat)) (Nat × Nat) := do
  let _ ← query (spec := unifSpec) 0
  let _ ← query (spec := unifSpec) 0
  let _ ← query (spec := Nat →ₒ Option Nat) 0
  let first : Nat ← query (spec := HashSpec) 2
  let second : Nat ← query (spec := HashSpec) 2
  let _ ← query (spec := Nat →ₒ Option Nat) 1
  return (1, first + second)

private def handler : QueryImpl World (StateT (List (Nat × Nat)) Id)
  | .inl n => fun cache => pure (⟨0, Nat.zero_lt_succ n⟩, cache)
  | .inr input => QueryImpl.ListCache.handler (m := Id) (fun n => pure (n + 100)) input

private def privatePolicy : Event World Nat → Cost
  | .ambient phase (.inl n) => (n + 1, .of (phaseCode phase, 1000 + n))
  | event => policy event

private abbrev SourceCounts := (Phase ⊕ Unit) → Nat

private def sourcePolicy : Event World Nat → SourceCounts
  | .ambient _ (.inl _) => 0
  | .ambient phase (.inr _) => Pi.single (.inl phase) 1
  | .signingAttempt _ => Pi.single (.inr ()) 1

private def runFrom (initial : List (Nat × Nat)) :
    Observation Nat Nat (Option Nat) Cost × List (Nat × Nat) :=
  (simulateQ handler (countedExperiment policy scheme adversary)).run initial

private def check (test : Bool) (message : String) : IO Unit :=
  unless test do throw (IO.userError message)

/-- Execute the source, ordered-cost, cache, freshness and rejection assertions. -/
def run : IO Unit := do
  let (outcome, cache) := runFrom []
  let (source, _) := (simulateQ handler (countedExperiment sourcePolicy scheme adversary)).run []
  let counts := source.cost
  check (counts (.inl .keygen) == 1 && counts (.inl .adversary) == 2 &&
    counts (.inl .signer) == 2 && counts (.inl .verification) == 1 && counts (.inr ()) == 2)
    "all five source coordinates"
  check (counts (.inl .keygen) + counts (.inl .adversary) +
    counts (.inl .signer) + counts (.inl .verification) == 6) "all hash calls"
  check (counts (.inr ()) + counts (.inl .adversary) + counts (.inl .verification) == 5)
    "selected work includes rejected attempts"
  let privateCharged := (simulateQ handler
    (countedExperiment privatePolicy scheme adversary)).run []
  check (privateCharged.1.cost.1 == 183) "private-query policy reuses the same experiment"
  check (outcome.cost.1 == 181) "input-dependent nonunit policy"
  check (outcome.cost.2.toList ==
    [(1, 1), (2, 1000), (2, 1000), (5, 0), (2, 2), (2, 2),
      (5, 1), (3, 3), (3, 3), (4, 5)]) "chronological source/input attribution"
  check (decide (outcome.rawLog = [⟨0, none⟩, ⟨1, some 11⟩])) "raw rejected+successful replies"
  check (cache == [(5, 105), (3, 103), (2, 102), (1, 101)]) "one shared cache"
  check (outcome.forgery == (1, 204)) "cold oracle replies affect the candidate"
  let (warm, cache) := runFrom [(9, 109), (2, 909)]
  check (warm.cost.1 == 181) "cache hits remain charged"
  check (cache == [(5, 105), (3, 103), (1, 101), (9, 109), (2, 909)]) "arbitrary initial cache"
  check (warm.forgery == (1, 1818)) "both repeated replies retain the distinct cached answer"
  check (!(returnedPairs id outcome.rawLog).contains outcome.forgery && outcome.verified)
    "different valid signature remains fresh"
  let replayBody (pk : Unit) := (fun _ => (1, 11)) <$> adversary pk
  let replay := (simulateQ handler (countedExperiment policy scheme replayBody)).run []
  check ((returnedPairs id replay.1.rawLog).contains replay.1.forgery && replay.1.verified)
    "an actual verified exact replay is not fresh"
  let invalid := (simulateQ handler
    (countedExperiment policy scheme (fun _ => pure (0, 12)))).run []
  check (invalid.1.cost.1 == 11 && !invalid.1.verified && invalid.2 == [(1, 101)])
    "invalid final request rejects before verifier work"
  IO.println "Signing-view source, ordered-cost, raw-log, cache and rejection tests: PASS"

end VCVioTest.CryptoFoundations.SigningViewCounted
