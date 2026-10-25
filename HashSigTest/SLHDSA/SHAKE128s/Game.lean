/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import HashSigTest.SLHDSA.SHAKE128s.Support

/-!
# Runtime controls for source-counted signature games

Literal work and backend counters distinguish direct hash calls from fresh answers, retain
rejected and repeated signing requests, and exclude the honest key generator and signer.
-/

public section

open OracleComp OracleSpec

namespace SLHDSA.SHAKE128s.GameTest

open Game TestSupport

/-- A nonempty-context signing request shared by the runtime controls. -/
def request : Message := ⟨[5], [6]⟩

/-- One key-generation hash, two signer hashes and one verifier hash. -/
def schemeConfig : ToySchemeConfig Unit := { publicKey := () }

/-- Two identical direct hashes, two private samples and one signing request. -/
def adversaryConfig : ToyAdversaryConfig := {
  signingRequests := [request]
  forgery := ⟨request, [1]⟩ }

/-- Execute a configured Bool-output toy game against the cached backend. -/
def run (scheme : ToySchemeConfig Unit) (adversary : ToyAdversaryConfig)
    (cache : List (Bytes × Bool) := []) :=
  runWithCache false (toyScheme (Output := Bool) scheme)
    (toyAdversary (Output := Bool) (PK := Unit) adversary) cache

/-- Observe all required source counters and their literal total work. -/
def checkBase : IO Unit := do
  let (((outcome, counts), _), trace) := run schemeConfig adversaryConfig
  ensure "keygen source count" (counts .keygen == 1)
  ensure "signer source count" (counts .signer == 2)
  ensure "direct hash source count" (counts .hash == 2)
  ensure "signing-request source count" (counts .sign == 1)
  ensure "verifier source count" (counts .verifier == 1)
  ensure "selected work is four" (selectedWork counts == 4)
  ensure "six full hash calls" (trace.hashCalls == 6)
  ensure "five fresh-answer draws" (trace.answerDraws == 5)
  ensure "two free private samples" (trace.privateSamples == 2)
  ensure "chronological hash inputs"
    (trace.hashInputs == [[0], [3], [3], [1], [2], [4]])
  ensure "actual signing request and response"
    (decide (outcome.signed = [⟨request, some [0]⟩]))
  ensure "fresh signature on previously signed message wins" (decide (Game.Wins outcome))

/-- A prewarmed direct input still incurs both direct hash charges. -/
def checkWarmCache : IO Unit := do
  let (((_, counts), _), trace) := run schemeConfig adversaryConfig [([3], false)]
  ensure "warm-cache direct calls" (counts .hash == 2)
  ensure "warm-cache selected work" (selectedWork counts == 4)
  ensure "warm-cache full hash calls" (trace.hashCalls == 6)
  ensure "warm-cache fresh-answer draws" (trace.answerDraws == 4)

/-- Extra repeated honest hashes change their source counts without changing selected work. -/
def checkExcludedHashes : IO Unit := do
  let config := { schemeConfig with
    keygenInputs := [[0], [0], [0]]
    signerInputs := [[1], [2], [2], [2]] }
  let (((_, counts), _), trace) := run config adversaryConfig
  ensure "three keygen hashes" (counts .keygen == 3)
  ensure "four signer hashes" (counts .signer == 4)
  ensure "asymmetric direct count two" (counts .hash == 2)
  ensure "asymmetric signing count one" (counts .sign == 1)
  ensure "asymmetric verifier count one" (counts .verifier == 1)
  ensure "asymmetric chronological source inputs"
    (trace.hashInputs == [[0], [0], [0], [3], [3], [1], [2], [2], [2], [4]])
  ensure "honest hashes excluded from work" (selectedWork counts == 4)
  ensure "ten full hash calls" (trace.hashCalls == 10)
  ensure "honest repeats reuse five answers" (trace.answerDraws == 5)

/-- Repeated final-verifier calls each add one unit of selected work. -/
def checkVerifierMultiplicity : IO Unit := do
  let config := { schemeConfig with verifierInputs := [[4], [4], [4]] }
  let (((_, counts), _), trace) := run config adversaryConfig
  ensure "three verifier hash calls" (counts .verifier == 3)
  ensure "verifier work rises to six" (selectedWork counts == 6)
  ensure "eight full hash calls" (trace.hashCalls == 8)
  ensure "verifier repeats reuse five answers" (trace.answerDraws == 5)

/-- Rejection retains the request charge and its actual `none` log entry. -/
def checkRejectedSigning : IO Unit := do
  let config := { schemeConfig with signingReply := none }
  let (((outcome, counts), _), trace) := run config adversaryConfig
  ensure "rejected signing request charged" (counts .sign == 1)
  ensure "rejected request retains work" (selectedWork counts == 4)
  ensure "rejected answer retained in log" (decide (outcome.signed = [⟨request, none⟩]))
  ensure "rejected signer hashes remain excluded" (counts .signer == 2 && trace.hashCalls == 6)

/-- Losing verification and an exact replay retain their counted work. -/
def checkLosses : IO Unit := do
  let replay := { adversaryConfig with forgery := ⟨request, [0]⟩ }
  let (((replayed, replayCounts), _), _) := run schemeConfig replay
  ensure "replay signature verifies" replayed.verified
  ensure "exact replay is not fresh" (!decide (Game.Fresh replayed.signed replayed.forgery))
  ensure "exact replay loses" (!decide (Game.Wins replayed))
  ensure "replay verification still counted" (selectedWork replayCounts == 4)
  let invalid := { adversaryConfig with forgery := ⟨request, [9]⟩ }
  let (((rejected, invalidCounts), _), _) := run schemeConfig invalid
  ensure "invalid signature loses" (!rejected.verified && !decide (Game.Wins rejected))
  ensure "losing work still counted" (selectedWork invalidCounts == 4)

/-- Private samples consume neither the hash budget nor the signing budget. -/
def checkPrivateOnly : IO Unit := do
  let scheme := { schemeConfig with verifierInputs := [] }
  let adversary := { adversaryConfig with directInputs := [], signingRequests := [] }
  let (((outcome, counts), _), trace) := run scheme adversary
  ensure "private-only direct count zero" (counts .hash == 0)
  ensure "private-only signing count zero" (counts .sign == 0)
  ensure "private-only selected work zero" (selectedWork counts == 0)
  ensure "private-only two samples" (trace.privateSamples == 2)
  ensure "private-only keygen hash excluded" (trace.hashCalls == 1 && counts .keygen == 1)
  ensure "private-only log empty" outcome.signed.isEmpty

/-- Identical signing requests are each charged, even when all signer inputs are cached. -/
def checkRepeatedSigning : IO Unit := do
  let adversary := { adversaryConfig with
    directInputs := []
    privateSamples := 0
    signingRequests := [request, request] }
  let (((outcome, counts), _), trace) := run schemeConfig adversary
  ensure "both signing requests charged" (counts .sign == 2)
  ensure "repeated-sign direct count zero" (counts .hash == 0)
  ensure "repeated-sign selected work three" (selectedWork counts == 3)
  ensure "both signing answers retained"
    (decide (outcome.signed = [⟨request, some [0]⟩, ⟨request, some [0]⟩]))
  ensure "four signer calls across cache hits" (counts .signer == 4)
  ensure "six calls but four draws" (trace.hashCalls == 6 && trace.answerDraws == 4)

/-- Execute every counted-game control. -/
def check : IO Unit := do
  checkBase
  checkWarmCache
  checkExcludedHashes
  checkVerifierMultiplicity
  checkRejectedSigning
  checkLosses
  checkPrivateOnly
  checkRepeatedSigning
  IO.println "SLH-DSA counted game: PASS (work 4; hashes 6; misses 5; private samples 2)"

end SLHDSA.SHAKE128s.GameTest

/-- Run source-counting controls for the actual counted game. -/
def main : IO Unit := SLHDSA.SHAKE128s.GameTest.check
