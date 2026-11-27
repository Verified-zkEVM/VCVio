/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import VCVio.CryptoFoundations.SignatureAlg.CountedExperiment.Encoding
public import VCVio.OracleComp.QueryTracking.ListCache
public import Mathlib.Algebra.FreeMonoid.Basic

/-!
# Encoded signing services under adaptive requests

An adaptive client observes rejection before a successful request. The same internal algorithm
supports distinct request policies, while the existing counted experiment retains raw replies,
ordered costs and one cache. Signature decoding rejects malformed final candidates before work.
-/

public section

namespace VCVioTest.CryptoFoundations.SigningViewEncoding

open OracleComp OracleSpec SignatureAlg.SigningView

private abbrev World := Nat →ₒ Nat
private abbrev WireSig := List Nat
private abbrev Cost := Nat × FreeAddMonoid (Nat × Nat)

private def phaseCode : Phase → Nat
  | .keygen => 1 | .adversary => 2 | .signer => 3 | .verification => 4

private def policy : Event World Nat → Cost
  | .ambient phase input => (100 * phaseCode phase + input, .of (phaseCode phase, input))
  | .signingAttempt request => (17 + request, .of (5, request))

private def alg : SignatureAlg (OracleComp World) Nat Nat Nat Nat where
  keygen := pure (7, 11)
  sign pk sk message := do
    let first ← query (spec := World) (pk * 100 + sk * 10 + message)
    let second ← query (spec := World) (pk * 100 + sk * 10 + message)
    return first + second
  verify pk message _ := do
    let _ ← query (spec := World) (900 + pk * 10 + message)
    return true

private def frame (request : Nat) : Option Nat :=
  if request = 0 then none else some request

private def decode : WireSig → Option Nat
  | [signature] => some signature
  | _ => none

private def view (requestFrame : Nat → Option Nat) :=
  rejectingEncoding alg requestFrame (fun signature => [signature]) decode

private def adversary (_ : Nat) :
    OracleComp (World + (Nat →ₒ Option WireSig)) (Nat × WireSig) := do
  let rejected ← query (spec := Nat →ₒ Option WireSig) 0
  match rejected with
  | some _ =>
    let _ ← query (spec := World) 99
    return (0, [0])
  | none =>
    let signed ← query (spec := Nat →ₒ Option WireSig) 4
    match signed with
    | none => return (4, [])
    | some signature => return (4, signature)

private def draw (input : Nat) : StateT Nat Id Nat := do
  modify Nat.succ
  return input + 1000

private def handler : QueryImpl World (StateT (List (Nat × Nat)) (StateT Nat Id)) :=
  QueryImpl.ListCache.handler (m := StateT Nat Id) draw

private def execute (requestFrame : Nat → Option Nat)
    (body : Nat → OracleComp (World + (Nat →ₒ Option WireSig)) (Nat × WireSig))
    (initial : List (Nat × Nat) := []) :
    (Observation Nat WireSig (Option WireSig) Cost × List (Nat × Nat)) × Nat :=
  ((simulateQ handler (countedExperiment policy (view requestFrame) body)).run initial).run 0

private def check (test : Bool) (message : String) : IO Unit :=
  unless test do throw (IO.userError message)

/-- Execute adaptive rejection, PK, ordered-cost, cache and canonical-candidate checks. -/
def run : IO Unit := do
  let ((outcome, cache), draws) := execute frame adversary
  check (outcome.cost.1 == 3640) "encoded service charges both attempts and all inner calls"
  check (outcome.cost.2.toList == [(5, 0), (5, 4), (3, 814), (3, 814), (4, 974)])
    "encoded service retains the supplied PK and chronological input costs"
  check (decide (outcome.rawLog = [⟨0, none⟩, ⟨4, some [3628]⟩]))
    "encoded service continues after the returned None and logs both replies"
  check (outcome.forgery == (4, [3628]) && outcome.verified && draws == 2)
    "encoded service uses both cache replies in the returned signature"
  check (cache == [(974, 1974), (814, 1814)]) "encoded service shares the actual cache"
  check ((returnedPairs id outcome.rawLog).contains outcome.forgery)
    "encoded exact replay remains a returned pair"
  let different (pk : Nat) := (fun _ => (4, [999])) <$> adversary pk
  let different := (execute frame different).1.1
  check (different.verified && !(returnedPairs id different.rawLog).contains different.forgery)
    "encoded different signature remains fresh"
  let ((warm, cache), draws) := execute frame adversary [(814, 91)]
  check (warm.forgery == (4, [182]) && warm.cost.1 == 3640 && draws == 1 &&
    cache == [(974, 1974), (814, 91)]) "encoded repeated hits stay charged with one new draw"
  let malformed (pk : Nat) := (fun result => (result.1, result.2 ++ [0])) <$> adversary pk
  let ((invalid, cache), draws) := execute frame malformed
  check (!invalid.verified && invalid.cost.1 == 2266 && draws == 1 &&
    cache == [(814, 1814)]) "encoded malformed candidate rejects before inner verification"
  let invalidRequest (pk : Nat) := (fun result => (0, result.2)) <$> adversary pk
  let ((invalid, cache), draws) := execute frame invalidRequest
  check (!invalid.verified && invalid.cost.1 == 2266 && draws == 1 &&
    cache == [(814, 1814)]) "encoded invalid final request rejects before inner verification"
  let stricter (request : Nat) := if request ≤ 4 then none else some request
  let ((strict, cache), draws) := execute stricter adversary
  check (strict.cost.1 == 38 && !strict.verified && draws == 0 && cache.isEmpty &&
    decide (strict.rawLog = [⟨0, none⟩, ⟨4, none⟩]))
    "encoded changed request policy retains rejected attempts without signer work"
  IO.println "Encoded signing service adaptive rejection, PK, costs and cache tests: PASS"

end VCVioTest.CryptoFoundations.SigningViewEncoding
