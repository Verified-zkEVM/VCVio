/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import VCVio.CryptoFoundations.SignatureAlg.CountedExperiment.Unforgeability
public import VCVio.OracleComp.QueryTracking.ListCache
public import Mathlib.Algebra.FreeMonoid.Basic

/-!
# Total-signature unforgeability observations

The mathematical clients retain arbitrary policies and independent oracle-index/runtime levels.
The executable fixture distinguishes message freshness from pair freshness while retaining the
unconditional verifier, full raw log, shared initial cache and chronological additive cost.
-/

public section

open OracleComp OracleSpec SignatureAlg
open SignatureAlg.SigningView

universe i r

namespace VCVioTest.CryptoFoundations.SigningViewUnforgeability

open scoped Classical in
/-- The original ordinary experiment is the message observer of the same counted execution. -/
theorem unforgeableExperiment_eq_countedObservation {ι : Type i} {spec : OracleSpec.{i, 0} ι}
    {Request PK SK Sig C : Type} [AddMonoid C] (policy : Event spec Request → C)
    (alg : SignatureAlg (OracleComp spec) Request PK SK Sig)
    (adv : UnforgeableAdversary alg) :
    unforgeableExperiment adv =
      (fun observed => !observed.rawLog.wasQueried observed.forgery.1 && observed.verified) <$>
        countedExperiment policy (ofTotal alg) adv.main :=
  (ofTotal_countedUnforgeableProgram policy alg adv).symm

open scoped Classical in
/-- Ordinary and strong probability identities at index level i and runtime level r. -/
private theorem generalAdvantageIdentities {ι : Type i} {spec : OracleSpec.{i, 0} ι}
    {Request PK SK Sig C : Type} [AddMonoid C] (policy : Event spec Request → C)
    (runtime : ProbCompRuntime.{i, r} (OracleComp spec))
    (alg : SignatureAlg (OracleComp spec) Request PK SK Sig)
    (adv : UnforgeableAdversary alg) (strong : StrongUnforgeableAdversary alg) :
    (runtime.evalDist
      ((fun observed => !observed.rawLog.wasQueried observed.forgery.1 && observed.verified) <$>
        countedExperiment policy (ofTotal alg) adv.main) {true} =
      unforgeableAdvantage runtime adv) ∧
    (runtime.evalDist
      ((fun observed => decide (Wins (ofTotal alg).readback (erase observed))) <$>
        countedExperiment policy (ofTotal alg) strong.main) {true} =
      strongUnforgeableAdvantage runtime strong) :=
  ⟨ofTotal_countedUnforgeableAdvantage policy runtime alg adv,
    ofTotal_countedStrongUnforgeableAdvantage policy runtime alg strong⟩

open scoped Classical in
/-- Ordinary and strong probability identities at index level 0 and runtime level 0. -/
private theorem smallAdvantageIdentities {ι : Type 0} {spec : OracleSpec.{0, 0} ι}
    {Request PK SK Sig C : Type} [AddMonoid C] (policy : Event spec Request → C)
    (runtime : ProbCompRuntime.{0, 0} (OracleComp spec))
    (alg : SignatureAlg (OracleComp spec) Request PK SK Sig)
    (adv : UnforgeableAdversary alg) (strong : StrongUnforgeableAdversary alg) :
    (runtime.evalDist
      ((fun observed => !observed.rawLog.wasQueried observed.forgery.1 && observed.verified) <$>
        countedExperiment policy (ofTotal alg) adv.main) {true} =
      unforgeableAdvantage runtime adv) ∧
    (runtime.evalDist
      ((fun observed => decide (Wins (ofTotal alg).readback (erase observed))) <$>
        countedExperiment policy (ofTotal alg) strong.main) {true} =
      strongUnforgeableAdvantage runtime strong) :=
  ⟨ofTotal_countedUnforgeableAdvantage policy runtime alg adv,
    ofTotal_countedStrongUnforgeableAdvantage policy runtime alg strong⟩

open scoped Classical in
/-- Ordinary and strong probability identities at index level 1 and runtime level 2. -/
private theorem independentAdvantageIdentities {ι : Type 1} {spec : OracleSpec.{1, 0} ι}
    {Request PK SK Sig C : Type} [AddMonoid C] (policy : Event spec Request → C)
    (runtime : ProbCompRuntime.{1, 2} (OracleComp spec))
    (alg : SignatureAlg (OracleComp spec) Request PK SK Sig)
    (adv : UnforgeableAdversary alg) (strong : StrongUnforgeableAdversary alg) :
    (runtime.evalDist
      ((fun observed => !observed.rawLog.wasQueried observed.forgery.1 && observed.verified) <$>
        countedExperiment policy (ofTotal alg) adv.main) {true} =
      unforgeableAdvantage runtime adv) ∧
    (runtime.evalDist
      ((fun observed => decide (Wins (ofTotal alg).readback (erase observed))) <$>
        countedExperiment policy (ofTotal alg) strong.main) {true} =
      strongUnforgeableAdvantage runtime strong) :=
  ⟨ofTotal_countedUnforgeableAdvantage policy runtime alg adv,
    ofTotal_countedStrongUnforgeableAdvantage policy runtime alg strong⟩

private abbrev HashSpec := Nat →ₒ Nat
private abbrev Cost := FreeAddMonoid (Nat × Nat)

private def phaseCode : Phase → Nat
  | .keygen => 1 | .adversary => 2 | .signer => 3 | .verification => 4

private def policy : Event HashSpec Bool → Cost
  | .ambient phase input => .of (phaseCode phase, input)
  | .signingAttempt request => .of (5, if request then 1 else 0)

private def scheme : SignatureAlg (OracleComp HashSpec) Bool Unit Unit Nat where
  keygen := do
    let _ : Nat ← query (spec := HashSpec) 1
    return ((), ())
  sign _ _ request := do
    let _ : Nat ← query (spec := HashSpec) 3
    let _ : Nat ← query (spec := HashSpec) 3
    return if request then 11 else 10
  verify _ _ signature := do
    let _ : Nat ← query (spec := HashSpec) 5
    return signature == 11 || signature == 12

private def adversary (_ : Unit) : OracleComp (HashSpec + (Bool →ₒ Nat)) (Bool × Nat) := do
  let first : Nat ← query (spec := HashSpec) 2
  let signature : Nat ← query (spec := Bool →ₒ Nat) true
  let second : Nat ← query (spec := HashSpec) 2
  return (first == second, signature + 1)

private def handler : QueryImpl HashSpec (StateT (List (Nat × Nat)) Id) :=
  QueryImpl.ListCache.handler (m := Id) (fun input => pure (input + 100))

private def runFrom (initial : List (Nat × Nat)) :
    Observation Bool Nat Nat Cost × List (Nat × Nat) :=
  (simulateQ handler (countedExperiment policy (ofTotal scheme) adversary)).run initial

private def check (test : Bool) (message : String) : IO Unit :=
  unless test do throw (IO.userError message)

/-- Check the actual total execution, then report its completion to the existing driver. -/
def run (complete : String → IO Unit) : IO Unit := do
  let (observed, cache) := runFrom []
  check (observed.cost.toList ==
    [(1, 1), (2, 2), (5, 1), (3, 3), (3, 3), (2, 2), (4, 5)])
    "F4 chronological noncommutative cost and repeated calls"
  check (decide (observed.rawLog = [⟨true, 11⟩])) "F4 complete raw signing log"
  check (cache == [(5, 105), (3, 103), (2, 102), (1, 101)])
    "F4 same shared final cache and unconditional verifier query"
  check observed.verified "F4 verifier accepts the different valid signature"
  check (!(!observed.rawLog.wasQueried observed.forgery.1 && observed.verified))
    "F4 ordinary observer rejects the queried message"
  check (!(returnedPairs some observed.rawLog).contains observed.forgery && observed.verified)
    "F4 strong observer accepts the fresh returned pair"
  check (observed.forgery == (true, 12)) "F4 exact different-signature candidate"
  let replayBody (pk : Unit) := (fun _ => (true, 11)) <$> adversary pk
  let replay := (simulateQ handler
    (countedExperiment policy (ofTotal scheme) replayBody)).run []
  check ((returnedPairs some replay.1.rawLog).contains replay.1.forgery && replay.1.verified)
    "F4 exact verified replay remains pair stale"
  check (replay.1.cost.toList == observed.cost.toList && replay.2 == cache)
    "F4 stale candidate still executes the complete verifier"
  let (warm, warmCache) := runFrom [(9, 109), (2, 909)]
  check (warmCache == [(5, 105), (3, 103), (1, 101), (9, 109), (2, 909)])
    "F4 arbitrary initial cache retained with repeated cached replies"
  check (warm.cost.toList == observed.cost.toList && warm.forgery == observed.forgery)
    "F4 cache hits retain call multiplicity and outcome"
  let invalid := (simulateQ handler
    (countedExperiment policy (ofTotal scheme) (fun _ => pure (false, 13)))).run []
  check (!invalid.1.verified && invalid.2 == [(5, 105), (1, 101)])
    "F4 invalid fresh candidate still executes final verification"
  check (invalid.1.cost.toList == [(1, 1), (4, 5)]) "F4 invalid verifier cost retained"
  complete "f4-unforgeability"
  IO.println "Total-signature ordinary/strong observers, unconditional verification, ordered cost, \
    raw log and shared cache: PASS"

end VCVioTest.CryptoFoundations.SigningViewUnforgeability
