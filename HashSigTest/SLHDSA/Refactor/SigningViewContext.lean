/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import HashSig.SLHDSA.SHAKE128s.Bridge.SharedExperiment.Wire
import HashSigTest.SLHDSA.SHAKE128s.WireBridge
public import Mathlib.Algebra.FreeMonoid.Basic

/-!
# Complete context observations under a cached execution

Public mathematical clients retain the actual FIPS observation and arbitrary cached continuation.
A bounded existing toy configuration exercises the production counted engine, fixed-context
adapter, chronological cost and complete cache. It does not execute the full FIPS key generator.
-/

public section

universe v

open OracleComp OracleSpec SignatureAlg
open SLHDSA SLHDSA.Security SLHDSA.SHAKE128s
open SLHDSA.SHAKE128s.Bridge.SharedExperiment

namespace SLHDSA.Refactor.SigningViewContext

/-- The complete mapped wire observation is the actual fixed-context external observation. -/
theorem mapped_wire_observation_eq_external :
  ∀ {C : Type} [AddMonoid C]
    (policy : SigningView.Event (Game.World FIPS205.Answer) Message → C)
    (ctx : PureContext) (adversary : StrongUnforgeableAdversary (Bridge.wireAlgorithm ctx)),
    contextObservation ctx <$>
      SigningView.countedExperiment (contextPolicy ctx policy)
        (SigningView.ofTotal (Bridge.wireAlgorithm ctx)) adversary.main =
      SigningView.countedExperiment policy (externalView FIPS205.scheme)
        (externalMain (Bridge.fixedContextAdversary ctx adversary)) := by
  intro C inst policy ctx adversary
  exact (countedExperiment_wire_eq_externalView policy ctx adversary).symm

/-- A literal fully quantified assignment client of the production continuation equality. -/
private theorem same_cache_continuation :
  ∀ {C : Type} [AddMonoid C]
    (policy : SigningView.Event (Game.World FIPS205.Answer) Message → C)
    (ctx : PureContext) (adversary : StrongUnforgeableAdversary (Bridge.wireAlgorithm ctx))
    {Cache β : Type} {m : Type → Type v} [Monad m] [LawfulMonad m]
    (handler : QueryImpl (Game.World FIPS205.Answer) (StateT Cache m)) (initial : Cache)
    (next : SigningView.Observation Message (List Byte) (Option (List Byte)) C × Cache → m β),
    ((simulateQ handler (SigningView.countedExperiment (contextPolicy ctx policy)
      (SigningView.ofTotal (Bridge.wireAlgorithm ctx)) adversary.main)).run initial >>=
        fun result => next (contextObservation ctx result.1, result.2)) =
      ((simulateQ handler (SigningView.countedExperiment policy (externalView FIPS205.scheme)
        (externalMain (Bridge.fixedContextAdversary ctx adversary)))).run initial >>= next) :=
  countedExperiment_wire_run_bind_eq_externalView

private abbrev Cost := FreeAddMonoid Nat
private abbrev Cache := List (List Byte × FIPS205.Answer)
private abbrev Observed := SigningView.Observation Message (List Byte) (Option (List Byte)) Cost

private def ctx : PureContext := ⟨[0xCA, 0xFE], by decide⟩

private def policy : SigningView.Event (Game.World FIPS205.Answer) Message → Cost
  | .ambient .keygen _ => .of 11
  | .ambient .adversary (.inl _) => .of 23
  | .ambient .adversary (.inr _) => .of 22
  | .ambient .signer _ => .of 44
  | .ambient .verification _ => .of 77
  | .signingAttempt request => .of
      (if request.context == [0xCA, 0xFE] && request.message == [0x41] then 31
      else if request.context == [0xCA, 0xFE] && request.message == [0x42] then 32 else 99)

private def config (accepted : Bool) : TestSupport.ToySchemeConfig (PublicKeyCore FIPS205.core) :=
  { publicKey := WireBridgeTest.publicKey
    keygenInputs := [[0x90]]
    signerInputs := [[0x92], [0x92]]
    verifierInputs := [[0x93]]
    signingReply := some [0xBE, 0xEF]
    acceptedSignatures := if accepted then [[0xBE, 0xEE]] else [] }

private def body : StrongUnforgeableAdversary (Bridge.wireAlgorithm ctx) where
  main _ := do
    let _ : FIPS205.Answer ← query (spec := Bridge.WireAdversarySpec) (.inl (.inr [0x91]))
    let _ : FIPS205.Answer ← query (spec := Bridge.WireAdversarySpec) (.inl (.inr [0x91]))
    let _ : Fin 2 ← query (spec := Bridge.WireAdversarySpec) (.inl (.inl 1))
    let _ : List Byte ← query (spec := Bridge.WireAdversarySpec) (.inr [0x41])
    let _ : List Byte ← query (spec := Bridge.WireAdversarySpec) (.inr [0x41])
    let _ : List Byte ← query (spec := Bridge.WireAdversarySpec) (.inr [0x42])
    return ([0x41], [0xBE, 0xEE])

private def program (accepted : Bool) : OracleComp (Game.World FIPS205.Answer) Observed :=
  SigningView.countedExperiment policy
    (externalView (TestSupport.toyScheme (Output := FIPS205.Answer) (config accepted)))
    (externalMain (Bridge.fixedContextAdversary ctx body))

private def answer : FIPS205.Answer := Vector.replicate 30 0xA7

private def initial : Cache :=
  [([0x99], Vector.replicate 30 0x99), ([0x91], Vector.replicate 30 0xA6)]

private def expectedCost : Cost :=
  .ofList [11, 22, 22, 23, 31, 44, 44, 31, 44, 44, 32, 44, 44, 77]

private def expectedSource (accepted : Bool) :
    SigningView.Observation (List Byte) (List Byte) (List Byte) Cost :=
  { forgery := ([0x41], [0xBE, 0xEE])
    rawLog := [⟨[0x41], [0xBE, 0xEF]⟩, ⟨[0x41], [0xBE, 0xEF]⟩, ⟨[0x42], [0xBE, 0xEF]⟩]
    verified := accepted
    cost := expectedCost }

private def expectedTarget (accepted : Bool) : Observed :=
  { forgery := (⟨[0x41], [0xCA, 0xFE]⟩, [0xBE, 0xEE])
    rawLog := [⟨⟨[0x41], [0xCA, 0xFE]⟩, some [0xBE, 0xEF]⟩,
      ⟨⟨[0x41], [0xCA, 0xFE]⟩, some [0xBE, 0xEF]⟩,
      ⟨⟨[0x42], [0xCA, 0xFE]⟩, some [0xBE, 0xEF]⟩]
    verified := accepted
    cost := .ofList [11, 22, 22, 23, 31, 44, 44, 31, 44, 44, 32, 44, 44, 77] }

private def expectedCache : Cache :=
  [([0x93], Vector.replicate 30 0xA7), ([0x92], Vector.replicate 30 0xA7),
    ([0x90], Vector.replicate 30 0xA7), ([0x99], Vector.replicate 30 0x99),
    ([0x91], Vector.replicate 30 0xA6)]

private def expectedTrace : TestSupport.BackendTrace :=
  { hashCalls := 10
    answerDraws := 3
    privateSamples := 1
    hashInputs := [[0x90], [0x91], [0x91], [0x92], [0x92], [0x92], [0x92], [0x92], [0x92], [0x93]] }

private def runBase (accepted : Bool) : (Observed × Cache) × TestSupport.BackendTrace :=
  ((simulateQ (TestSupport.cachedHandler answer) (program accepted)).run initial).run {}

private def runContinuation (accepted : Bool) :
    ((Observed × FIPS205.Answer) × Cache) × TestSupport.BackendTrace :=
  (((simulateQ (TestSupport.cachedHandler answer) (program accepted)).run initial >>=
    fun joint => do
      let chosen : List Byte := if joint.1.verified then [0x91] else [0x92]
      let (reply, cache) ← TestSupport.cachedHandler answer (.inr chosen) joint.2
      return ((joint.1, reply), cache)).run {})

private def observedEq (left right : Observed) : Bool :=
  decide (left.forgery = right.forgery) && decide (left.rawLog = right.rawLog) &&
    left.verified == right.verified && left.cost.toList == right.cost.toList

private def traceEq (left right : TestSupport.BackendTrace) : Bool :=
  left.hashCalls == right.hashCalls && left.answerDraws == right.answerDraws &&
    left.privateSamples == right.privateSamples && left.hashInputs == right.hashInputs

private def expectedContinuationTrace (accepted : Bool) : TestSupport.BackendTrace :=
  { hashCalls := 11
    answerDraws := 3
    privateSamples := 1
    hashInputs := [[0x90], [0x91], [0x91], [0x92], [0x92], [0x92], [0x92], [0x92],
      [0x92], [0x93]] ++ [if accepted then [0x91] else [0x92]] }

private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

/-- Execute complete bounded context observations before reporting their completion. -/
def run (complete : String → IO Unit) : IO Unit := do
  for accepted in [true, false] do
    let ((observed, cache), trace) := runBase accepted
    check (decide (observed.forgery = (expectedTarget accepted).forgery))
      "F5 actual fixed context and final candidate"
    check (decide (observed.rawLog = (expectedTarget accepted).rawLog))
      "F5 whole chronological raw log with duplicate replies"
    check (observed.verified == accepted) "F5 actual unconditional verifier result"
    check (observed.cost.toList == expectedCost.toList)
      "F5 chronological noncommutative cost across all phases"
    check (observedEq observed (expectedTarget accepted)) "F5 whole actual observation"
    check (cache == expectedCache && traceEq trace expectedTrace)
      "F5 exact produced warm cache and backend trace"
    check (observedEq (contextObservation ctx (expectedSource accepted)) (expectedTarget accepted))
      "F5 intrinsic context map retains every observation field"
    let (((continued, reply), finalCache), finalTrace) := runContinuation accepted
    check (observedEq continued (expectedTarget accepted) &&
      reply == Vector.replicate 30 (if accepted then 0xA6 else 0xA7) &&
      finalCache == expectedCache && traceEq finalTrace (expectedContinuationTrace accepted))
      "F5 effectful continuation retains actual observation reply cache and trace"
  for reply in [some [0xBE, 0xEF], none] do
    let (forgery, events) := WireBridgeTest.run reply
    check (forgery.message.message == [0x42] && forgery.message.context == [0xCA, 0xFE] &&
      forgery.signature == reply.getD []) "F5 actual optional forwarding and rejection fallback"
    check (decide (events = [.sample 1, .hash [0x91], .hash [0x91],
      .sign ⟨[0x41], [0xCA, 0xFE]⟩])) "F5 actual fixed-context handler chronology"
  WireBridgeTest.checkBoundaries
  complete "f5-context"
  IO.println "Signing-view context checks passed"

end SLHDSA.Refactor.SigningViewContext
