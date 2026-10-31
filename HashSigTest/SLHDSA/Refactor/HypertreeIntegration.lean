/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import HashSig.SLHDSA.SecretProvider
public import VCVio.OracleComp.QueryTracking.WriterCost

/-!
# Small effectful entry-policy cases

Callback examples expose ordered log, cache and component-call counts.
The count is one unit per example callback, not a cryptographic hash-work certificate.
Proof clients identify the actual provider adapter. The executable checks the shared loop with
small effectful components; it does not execute a fixed-parameter cryptographic signer.
-/

public section

open OracleComp OracleSpec

universe v

namespace SLHDSA.Refactor.HypertreeIntegration

/-- The native singleton entry retains the actual effectful recovery and its failure. -/
theorem native_provider_singleton_recovery (vp : ValidatedParams)
    (core : CorePrimitives vp.params) {m : Type → Type v} [Monad m]
    (hash : Adrs → core.Y → m core.Y) (compress : Adrs → List core.Y → m core.Y)
    (nodeHash : Adrs → core.Y → core.Y → m core.Y) (secret : Adrs → m core.Y)
    (position : LayerPosition vp) (remaining : position.layer.val + 1 = vp.params.d)
    (message : core.Y) :
    GeneralHypertree.signFromPositionWithSecret core hash compress nodeHash secret true position 1
        remaining message = (do
      let signature ← xmssSignWithSecret core hash compress nodeHash secret message
        position.toAdrs position.leaf.val
      let _ ← xmssPkFromSigWith core hash compress nodeHash position.leaf.val signature message
        position.toAdrs
      return #v[signature] : m (Vector (XmssSig vp.params core) 1)) := by
  simp only [GeneralHypertree.signFromPositionWithSecret_one, reduceIte]

/-- The native singleton skip profile invokes no recovery callback. -/
theorem native_provider_singleton_skip (vp : ValidatedParams)
    (core : CorePrimitives vp.params) {m : Type → Type v} [Monad m]
    (hash : Adrs → core.Y → m core.Y) (compress : Adrs → List core.Y → m core.Y)
    (nodeHash : Adrs → core.Y → core.Y → m core.Y) (secret : Adrs → m core.Y)
    (position : LayerPosition vp) (remaining : position.layer.val + 1 = vp.params.d)
    (message : core.Y) :
    GeneralHypertree.signFromPositionWithSecret core hash compress nodeHash secret false position 1
        remaining message = (do
      let signature ← xmssSignWithSecret core hash compress nodeHash secret message
        position.toAdrs position.leaf.val
      return #v[signature] : m (Vector (XmssSig vp.params core) 1)) := by
  simp only [GeneralHypertree.signFromPositionWithSecret_one, Bool.false_eq_true, ite_false]

/-- The provider interpretation retains output, log, cache and ordered cost jointly. -/
theorem native_provider_jointObservation (vp : ValidatedParams) (core : CorePrimitives vp.params)
    {ι : Type} {spec : OracleSpec ι}
    (hash : Adrs → core.Y → OracleComp spec core.Y)
    (compress : Adrs → List core.Y → OracleComp spec core.Y)
    (nodeHash : Adrs → core.Y → core.Y → OracleComp spec core.Y)
    (secret : Adrs → OracleComp spec core.Y) (entryFlag : Bool)
    (position : LayerPosition vp) (remaining : Nat)
    (hremaining : position.layer.val + remaining = vp.params.d) (message : core.Y)
    {Log Cache C : Type} [AddMonoid C] {m : Type → Type v} [Monad m]
    (handler : QueryImpl spec (StateT (Log × Cache) m))
    (cost : spec.Domain → C) (initial : Log × Cache) :
    ((simulateQ (handler.withAddCost cost)
      (GeneralHypertree.signFromPositionWithSecret core hash compress nodeHash secret entryFlag
        position remaining hremaining message)).runAdd).run initial =
    ((simulateQ (handler.withAddCost cost)
      (Hypertree.Program.signLayers (GeneralHypertree.nextRemainingPosition vp)
        (fun _ current value => xmssSignWithSecret core hash compress nodeHash secret value
          current.val.toAdrs current.val.leaf.val)
        (fun _ current signature value => xmssPkFromSigWith core hash compress nodeHash
          current.val.leaf.val signature value current.val.toAdrs)
        entryFlag remaining ⟨position, hremaining⟩ message)).runAdd).run initial := rfl

/-- A singleton recovering entry propagates failure from its discarded component recovery. -/
theorem singleton_recovery_failure :
    Hypertree.Program.signLayers (Position := fun _ => Unit) (m := Option) (fun _ _ => ())
      (fun _ _ (message : Nat) => some message)
      (fun _ _ _ _ => none) true 1 () 7 = none := rfl

/-- A singleton skip entry never executes a failing recovery callback. -/
theorem singleton_skip_avoids_recovery_failure :
    Hypertree.Program.signLayers (Position := fun _ => Unit) (m := Option) (fun _ _ => ())
      (fun _ _ (message : Nat) => some message)
      (fun _ _ _ _ => none) false 1 () 7 = some #v[7] := rfl

/-- A component call with its actual position, signature and incoming message. -/
inductive Event where
  | sign (position message : Nat)
  | recover (position signature message : Nat)
  deriving DecidableEq

/-- Chronological component calls, a cache marker and accumulated component count. -/
abbrev SmallState := List Event × Nat × Nat

/-- Advance the toy position by one layer. -/
def next (_r position : Nat) : Nat := position + 1

/-- Record one signing call before returning its position-dependent signature. -/
def signOne (_r position message : Nat) : StateM SmallState Nat := do
  modify fun state => (state.1 ++ [.sign position message], state.2.1 + 10, state.2.2 + 1)
  return message + position

/-- Record one recovery and update the cache marker before returning the next message. -/
def recoverOne (_r position signature message : Nat) : StateM SmallState Nat := do
  modify fun state =>
    (state.1 ++ [.recover position signature message], state.2.1 + 100, state.2.2 + 1)
  return signature + 100

/-- Run the actual shared loop from a fixed nonempty state. -/
def runSign (entryFlag : Bool) (layers : Nat) : Vector Nat layers × SmallState :=
  (Hypertree.Program.signLayers (Position := fun _ => Nat) next signOne recoverOne entryFlag
    layers 4 10).run ([], 5, 9)

/-- No component executes for a zero-layer entry. -/
theorem zero_trace : runSign true 0 = (#v[], [], 5, 9) := by decide

/-- The skip profile changes state only through its signing callback. -/
theorem singleton_skip_trace :
    runSign false 1 = (#v[14], [.sign 4 10], 15, 10) := by decide

/-- The recovering profile retains the discarded recovery in the final state. -/
theorem singleton_recover_trace :
    runSign true 1 = (#v[14], [.sign 4 10, .recover 4 14 10], 115, 11) := by decide

/-- Both singleton profiles return the same signature value. -/
theorem singleton_output_eq : (runSign true 1).1 = (runSign false 1).1 := by decide

/-- Equal singleton signatures do not imply equal observed states. -/
theorem singleton_state_ne : (runSign true 1).2 ≠ (runSign false 1).2 := by decide

/-- A nonfinal entry resets the profile and recovers only between its two layers. -/
theorem two_entry_true_resets :
    (runSign true 2).2 = ([.sign 4 10, .recover 4 14 10, .sign 5 114], 125, 12) := by decide

/-- Both entry flags select the same two-layer computation. -/
theorem two_entry_flags_same : runSign true 2 = runSign false 2 := by
  simp only [runSign, Hypertree.Program.signLayers_add_two]

private def ensure (label : String) (condition : Bool) : IO Unit :=
  unless condition do
    throw (IO.userError s!"hypertree program check failed: {label}")

private def checkSingleton (result : Vector Nat 1 × SmallState) : IO Unit :=
  ensure "singleton recovery retains its discarded component effects"
    (decide (result = (#v[14], [.sign 4 10, .recover 4 14 10], 115, 11)))

private def checkTwo (result : Vector Nat 2 × SmallState) : IO Unit :=
  ensure "nonfinal recovery feeds the next message and resets the singleton flag"
    (decide (result = (#v[14, 119],
      [.sign 4 10, .recover 4 14 10, .sign 5 114], 125, 12)))

private def failingSign (_r position message : Nat) :
    OptionT (StateM SmallState) Nat :=
  show StateM SmallState (Option Nat) from do
    let signature ← signOne 0 position message
    return some signature

private def failingRecovery (_r position signature message : Nat) :
    OptionT (StateM SmallState) Nat :=
  show StateM SmallState (Option Nat) from do
    let _ ← recoverOne 0 position signature message
    return none

private def runFailure (flag : Bool) : Option (Vector Nat 1) × SmallState :=
  ((Hypertree.Program.signLayers (Position := fun _ => Nat) next
    failingSign failingRecovery flag 1 4 10).run).run ([], 5, 9)

private def runRecovery : Nat × SmallState :=
  (Hypertree.Program.recoverLayers (Position := fun _ => Nat) next recoverOne
    2 4 10 #v[14, 119]).run ([], 5, 9)

/-- Execute small shared-loop checks retaining component state, count and failure jointly. -/
def runTests : IO Unit := do
  ensure "zero entry performs no component action" (decide (runSign true 0 = (#v[], [], 5, 9)))
  checkSingleton (runSign true 1)
  ensure "singleton skip executes only signing"
    (decide (runSign false 1 = (#v[14], [.sign 4 10], 15, 10)))
  ensure "singleton failure retains the discarded recovery effects"
    (decide (runFailure true = (none, [.sign 4 10, .recover 4 14 10], 115, 11)))
  ensure "singleton skip avoids a failing recovery"
    (decide (runFailure false = (some #v[14], [.sign 4 10], 15, 10)))
  checkTwo (runSign true 2)
  checkTwo (runSign false 2)
  ensure "recovery includes the final layer and passes each recovered root onward"
    (decide (runRecovery = (219,
      [.recover 4 14 10, .recover 5 119 114], 205, 11)))
  IO.println "SLH-DSA hypertree program singleton: PASS"
  IO.println "SLH-DSA hypertree program nonfinal: PASS"
  IO.println "SLH-DSA hypertree program recovery: PASS"

private def runCarry : Vector Nat 2 × SmallState :=
  (show StateM SmallState (Vector Nat 2) from do
    let first ← signOne 1 4 10
    let root ← recoverOne 1 4 first 10
    let rest ← Hypertree.Program.signLayers (Position := fun _ => Nat) next
      signOne recoverOne true 1 5 root
    return rest.insertIdx 0 first).run ([], 5, 9)

private def runSkipBetween : Vector Nat 2 × SmallState :=
  (show StateM SmallState (Vector Nat 2) from do
    let first ← signOne 1 4 10
    let second ← signOne 0 5 10
    return #v[first, second]).run ([], 5, 9)

/-- Run changed computations against the unchanged singleton and nonfinal assertions. -/
def runControl (name : String) : IO Unit :=
  if name == "skip-singleton" then checkSingleton (runSign false 1)
  else if name == "carry-singleton" then checkTwo runCarry
  else if name == "skip-between" then checkTwo runSkipBetween
  else throw (IO.userError s!"unknown hypertree program control: {name}")

end SLHDSA.Refactor.HypertreeIntegration
