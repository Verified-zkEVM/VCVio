/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import HashSig.SLHDSA.SigningView.Encoding
public import HashSig.SLHDSA.Security.ByteRouter
public import HashSig.SLHDSA.SHAKE128s.FIPS205.Params
public import VCVio.OracleComp.QueryTracking.Enforcement
public import HashSig.SLHDSA.External
public import HashSig.SLHDSA.Concrete.Codec
public import HashSig.SLHDSA.SHAKE128s.Bridge.SharedExperiment.Defs

/-!
# SHAKE pure views of the existing external request carrier

The bridge attaches the existing context/message frame to the reusable internal constructor.
Parameters, randomizers and public-seed programs remain those of the supplied SHAKE algorithm.
The fixed-parameter marked sources retain the original external client, partial replies and public
verification. A source budget guard runs before the complete raw-query router.
-/

public section

open OracleComp OracleSpec
open SLHDSA.Security

namespace SLHDSA.SHAKE128s.Bridge.SharedExperiment

/-- Use the existing external request and frame with every SHAKE parameter and sampling mode. -/
@[expose] noncomputable def pureShakeView (vp : ValidatedParams)
    (randomizer : PublicKeyCore (shakeCore vp) → ProbComp (shakeCore vp).Y)
    (seeds : ProbComp (shakeCore vp).PkSeed) :
    SignatureAlg.SigningView (OracleComp (unifSpec + shakeSpec vp)) Message
      (PublicKeyCore (shakeCore vp)) (SecretKeyCore (shakeCore vp))
      (List Byte) (Option (List Byte)) :=
  SLHDSA.SigningView.fromInternalPure vp (Concrete.shakeWireCodec vp.params)
    (shakeRomScheme vp randomizer seeds)
    (fun request => (External.encodePureMessage request.context request.message).toOption)

/-- Every sampling mode retains the complete internal key-generation program. -/
@[simp] theorem pureShakeView_keygen (vp : ValidatedParams)
    (randomizer : PublicKeyCore (shakeCore vp) → ProbComp (shakeCore vp).Y)
    (seeds : ProbComp (shakeCore vp).PkSeed) :
    (pureShakeView vp randomizer seeds).keygen = (shakeRomScheme vp randomizer seeds).keygen := rfl

/-! ## Guarded marked sources -/

namespace Guarded

@[expose] public section

open SignatureAlg

abbrev PK := PublicKeyCore FIPS205.core
abbrev Raw := shakeSpec FIPS205.params
abbrev H := hashSpec FIPS205.core
abbrev R := Game.World FIPS205.Answer
abbrev Ev := SigningView.Event R Message
abbrev O := ObsSpec Ev
abbrev Native := unifSpec + (H + Raw)
abbrev Common := Native + O
abbrev DNative := deriveSpec FIPS205.core + Raw
abbrev DCommon := DNative + O
abbrev Sign := Message →ₒ Option (List Byte)
abbrev RawOutcome := SigningView.Outcome Message (List Byte) (Option (List Byte))
abbrev Full := (PK × PK) × RawOutcome
abbrev Paid := (Nat × Nat) × Bool
abbrev Meta := Nat × SigningView.Phase
abbrev Lab := labSpec FIPS205.core
abbrev A := Lab + Raw
abbrev LabCommon := A + O

/-- The actual structured-to-byte FIPS oracle encoding at a fixed public seed. -/
noncomputable def encoding (pkSeed : FIPS205.core.PkSeed) :=
  shakeEncoding FIPS205.params (by decide) (by decide) pkSeed

/-- Original signing-attempt and adversary/verifier hash charges. -/
def originalPolicy (event : Ev) : Nat × Nat :=
  let counts := Game.Counted.sourcePolicy event
  ((∑ kind ∈ ({.sign, .hash, .verifier} : Finset Unforgeability.QueryKind), counts kind),
    counts .sign)

/-- Public reserve charges selected by the actual byte router. -/
noncomputable def reserveExtra (pkSeed : FIPS205.core.PkSeed) : Ev → Nat
  | .signingAttempt _ => 31
  | .ambient .adversary (.inr input) | .ambient .verification (.inr input) =>
      match (encoding pkSeed).route input with
      | none => 0
      | some (.inl (.hmsg ..)) => 30
      | some typed =>
          if ((slhNodeKeys FIPS205.core pkSeed).node typed).isSome then 31 else 15
  | _ => 0

/-- False selects Original; true selects the public reserve policy at the fixed public seed. -/
noncomputable def policy (reserve : Bool) (pkSeed : FIPS205.core.PkSeed) (event : Ev) :
    Nat × Nat :=
  originalPolicy event + (if reserve then reserveExtra pkSeed event else 0, 0)

/-- Routed adversary and verifier message-digest observations. -/
noncomputable def selectedRaw (pkSeed : FIPS205.core.PkSeed) : Ev → Nat
  | .ambient .adversary (.inr input) | .ambient .verification (.inr input) =>
      match (encoding pkSeed).route input with
      | some (.inl (.hmsg ..)) => 1
      | _ => 0
  | _ => 0

/-- Zero or selected-raw bookkeeping for the same original event port. -/
noncomputable def metadataCost (trackRaw : Bool) (pkSeed : FIPS205.core.PkSeed)
    (event : Ev) : Nat := if trackRaw then selectedRaw pkSeed event else 0

/-- Existing Nat/phase bookkeeping, updated only by admitted original-source observations. -/
def aux {ι Cache : Type} {spec : OracleSpec.{0, 0} ι}
    (charge : Ev → Nat) (input : (spec + O).Domain)
    (_before : Cache) (_answer : (spec + O).Range input) (_after : Cache)
    (metadata : Meta) : Meta :=
  match input with
  | .inl _ => metadata
  | .inr (.ambient phase native) =>
      (metadata.1 + charge (.ambient phase native), phase)
  | .inr (.signingAttempt request) =>
      (metadata.1 + charge (.signingAttempt request), .signer)

/-- Internal fallback: index zero for sampling, zero bytes for raw answers and unit for events. -/
def rawFallback : (input : (R + O).Domain) → (R + O).Range input
  | .inl (.inl n) => (⟨0, Nat.succ_pos n⟩ : Fin (n + 1))
  | .inl (.inr _) => Vector.replicate _ 0
  | .inr _ => PUnit.unit

/-- The unresolved fallback uses the same zero node for either private derivation variant. -/
noncomputable def deriveFallback (pkSeed : FIPS205.core.PkSeed) :
    (input : DCommon.Domain) → DCommon.Range input
  | .inl (.inl (.inl (.inl n))) => rawFallback (.inl (.inl n))
  | .inl (.inl (.inl (.inr typed))) =>
      (encoding pkSeed).trunc typed
        (rawFallback (.inl (.inr ((encoding pkSeed).encode typed))))
  | .inl (.inl (.inr _)) => Vector.replicate _ 0
  | .inl (.inr bytes) => rawFallback (.inl (.inr bytes))
  | .inr _ => PUnit.unit

/-- Sparse original-source labels: private derivations emit no raw marker. -/
def nativeObservation : DNative.Domain → Option R.Domain
  | .inl (.inl (.inl n)) => some (.inl n)
  | .inl (.inl (.inr typed)) => some (.inr (encode FIPS205.params typed))
  | .inl (.inr _) => none
  | .inr bytes => some (.inr bytes)

/-- Original-source events of the unresolved chronological experiment. -/
def sparseProjection :
    QueryImpl (SigningView.Events.Spec DNative Message) (OracleComp DCommon) :=
  QueryImpl.add (QueryImpl.ofLift DNative (OracleComp DCommon))
    (fun event => match event with
      | .signingAttempt request => liftM (DCommon.query (.inr (.signingAttempt request)))
      | .ambient phase input => match nativeObservation input with
        | some label => liftM (DCommon.query (.inr (.ambient phase label)))
        | none => pure PUnit.unit)
/-- The actual external raw client with unresolved honest derivation ports. -/
def rawMainD (adv : Game.Adversary FIPS205.Answer PK) (pk : PK) :
    OracleComp (DNative + Sign) (Message × List Byte) :=
  simulateQ (QueryImpl.add
    (QueryImpl.add
      (fun n => liftM ((DNative + Sign).query (.inl (.inl (.inl (.inl n))))))
      (fun bytes => liftM ((DNative + Sign).query (.inl (.inr bytes)))))
    (fun request => liftM ((DNative + Sign).query (.inr request))))
    (Game.Counted.externalMain adv pk)

/-- Strict FIPS framing and canonical signatures around the derivation scheme. -/
noncomputable def unresolvedView (pkSeed : FIPS205.core.PkSeed) :
    SigningView (OracleComp DNative) Message PK PK (List Byte) (Option (List Byte)) :=
  SigningView.rejectingEncoding
    ((deriveScheme FIPS205.core (fun pk => pure pk.pkSeed) pkSeed).map
      (simulateQ' (QueryImpl.ofLift (deriveSpec FIPS205.core) (OracleComp DNative))))
    (fun request => (External.encodePureMessage request.context request.message).toOption)
    (SLHDSA.encodeSignature FIPS205.params
      (SLHDSA.Concrete.shakeWireCodec FIPS205.params.params))
    (fun wire => (SLHDSA.decodeSignature FIPS205.params
      (SLHDSA.Concrete.shakeWireCodec FIPS205.params.params) wire).toOption)

/-- This program has no secret-seed parameter; honest private queries remain unresolved. -/
noncomputable def fixedSource (pkSeed : FIPS205.core.PkSeed)
    (adv : Game.Adversary FIPS205.Answer PK) : OracleComp DCommon Full :=
  simulateQ sparseProjection
    (SigningView.Events.fullExperiment (unresolvedView pkSeed) (rawMainD adv))


/-- The framed partial signing view over the existing lab interface. -/
noncomputable def partialView (useLab : Bool) (s : FIPS205.core.PkSeed) :
    SigningView (OracleComp Lab) Message PK PK (List Byte) (Option (List Byte)) :=
  SigningView.rejectingEncoding
    (if useLab then labScheme FIPS205.core (fun pk => pure pk.pkSeed) s
      else (deriveScheme FIPS205.core (fun pk => pure pk.pkSeed) s).map
        (labLiftHom FIPS205.core).toMonadHom)
    (fun request : Message =>
      (External.encodePureMessage request.context request.message).toOption)
    (SLHDSA.encodeSignature FIPS205.params
      (SLHDSA.Concrete.shakeWireCodec FIPS205.params.params))
    (fun wire => (SLHDSA.decodeSignature FIPS205.params
      (SLHDSA.Concrete.shakeWireCodec FIPS205.params.params) wire).toOption)


/-- Route complete raw queries while forwarding lab queries and source events. -/
noncomputable def routeLab (pkSeed : FIPS205.core.PkSeed) : QueryImpl LabCommon
    (StateT (QueryCache Raw) (OracleComp (Lab + O))) :=
  QueryImpl.add (spec₁ := Lab + Raw) (spec₂ := O)
    (QueryImpl.add (spec₁ := Lab) (spec₂ := Raw)
      (fun input => StateT.mk fun privateCache => do
        let answer ← (liftM ((Lab + O).query (.inl input)) :
          OracleComp (Lab + O) (Lab.Range input))
        pure (answer, privateCache))
      (fun raw => StateT.mk fun privateCache =>
        simulateQ (QueryImpl.ofLift (unifSpec + H) (OracleComp (Lab + O)))
          (((encoding pkSeed).tableRouter raw).run privateCache)))
    (fun event => StateT.mk fun privateCache => do
      let answer ← (liftM ((Lab + O).query (.inr event)) :
        OracleComp (Lab + O) PUnit)
      pure (answer, privateCache))

/-- Lift the framed signing view to the shared lab and raw-query interface. -/
noncomputable def commonView (useLab : Bool) (s : FIPS205.core.PkSeed) :
    SigningView (OracleComp A) Message PK PK (List Byte) (Option (List Byte)) :=
  (partialView useLab s).map
    (simulateQ' (fun input : Lab.Domain =>
      (liftM (A.query (.inl input)) : OracleComp A (Lab.Range input))))

/-- The original external client with its raw queries and partial signing service. -/
def commonMain (adv : Game.Adversary FIPS205.Answer PK) (pk : PK) :
    OracleComp (A + Sign) (Message × List Byte) :=
  simulateQ (QueryImpl.add (spec₁ := R) (spec₂ := Sign)
    (QueryImpl.add (spec₁ := unifSpec) (spec₂ := Raw)
      (QueryImpl.ofLift unifSpec (OracleComp (A + Sign)))
      (fun raw => liftM ((A + Sign).query (.inl (.inr raw)))))
    (fun request => liftM ((A + Sign).query (.inr request))))
    (Game.Counted.externalMain adv pk)

/-- Original byte-source labels of public native inputs. -/
def sourceInput : (unifSpec + H).Domain → R.Domain
  | .inl n => .inl n
  | .inr typed => .inr (encode FIPS205.params typed)

/-- Preserve original public markers and silence private derivation and label traffic. -/
def commonEvent : SigningView.Event A Message → Option Ev
  | .signingAttempt request => some (.signingAttempt request)
  | .ambient phase (.inl (.inl (.inl native))) =>
      some (.ambient phase (sourceInput native))
  | .ambient phase (.inr raw) => some (.ambient phase (.inr raw))
  | _ => none

/-- Forward native traffic and the original sparse source observations. -/
def commonProjection :
    QueryImpl (SigningView.Events.Spec A Message) (OracleComp LabCommon) :=
  QueryImpl.add
    (fun input : A.Domain => (liftM (LabCommon.query (.inl input)) :
      OracleComp LabCommon (A.Range input)))
    (fun event => match commonEvent event with
      | some rawEvent => liftM (LabCommon.query (.inr rawEvent))
      | none => pure PUnit.unit)

/-- The complete marked signing experiment, including the generated key pair. -/
noncomputable def commonSource (useLab : Bool) (s : FIPS205.core.PkSeed)
    (adv : Game.Adversary FIPS205.Answer PK) : OracleComp LabCommon Full :=
  simulateQ commonProjection
    (SigningView.Events.fullExperiment (commonView useLab s) (commonMain adv))



/-- The complete marked lab experiment guarded before its stateful raw router. -/
noncomputable def guardedRoutedSource
    (pkSeed : FIPS205.core.PkSeed) (adv : Game.Adversary FIPS205.Answer PK)
    (reserve : Bool) (caps : Nat × Nat)
    (fallbackCommon : (input : LabCommon.Domain) → LabCommon.Range input) :
    OracleComp (Lab + O) ((Full × (PUnit × Paid)) × Raw.QueryCache) :=
  letI : MonadLiftT (OracleComp LabCommon) (StateT PUnit (OracleComp LabCommon)) :=
    ⟨fun action => StateT.lift action⟩
  let forwarder := (QueryImpl.id' LabCommon).liftTarget
    (StateT PUnit (OracleComp LabCommon))
  let guarded := (simulateQ (QueryImpl.guardQueryBudget caps
    (Sum.elim (fun _ : A.Domain => (0, 0)) (policy reserve pkSeed)) forwarder fallbackCommon)
    (commonSource true pkSeed adv)).run (PUnit.unit, ((0, 0), false))
  (simulateQ (routeLab pkSeed) guarded).run ∅


/-- Internalize the raw table without resolving any private derivation. -/
noncomputable def routeD (pkSeed : FIPS205.core.PkSeed) :
    QueryImpl DCommon
      (StateT Raw.QueryCache (OracleComp (deriveSpec FIPS205.core + O))) :=
  QueryImpl.add
    (QueryImpl.add
      (fun input : (deriveSpec FIPS205.core).Domain => StateT.mk fun privateCache => do
        let answer ← (liftM ((deriveSpec FIPS205.core + O).query (.inl input)) :
          OracleComp (deriveSpec FIPS205.core + O) ((deriveSpec FIPS205.core).Range input))
        pure (answer, privateCache))
      (fun bytes => StateT.mk fun privateCache =>
        simulateQ (QueryImpl.ofLift (unifSpec + H)
          (OracleComp (deriveSpec FIPS205.core + O)))
          (((encoding pkSeed).tableRouter bytes).run privateCache)))
    (fun event => StateT.mk fun privateCache => do
      let answer ← (liftM ((deriveSpec FIPS205.core + O).query (.inr event)) :
        OracleComp (deriveSpec FIPS205.core + O) PUnit)
      pure (answer, privateCache))

/-- Retain the actual passive metadata in the secret-free source program. -/
noncomputable def observeD (pkSeed : FIPS205.core.PkSeed) (trackRaw : Bool) :
    QueryImpl (deriveSpec FIPS205.core + O)
      (StateT Meta (OracleComp (deriveSpec FIPS205.core))) :=
  QueryImpl.add
    ((QueryImpl.id' (deriveSpec FIPS205.core)).liftTarget
      (StateT Meta (OracleComp (deriveSpec FIPS205.core))))
    (fun event => StateT.mk fun metadata =>
      pure (PUnit.unit,
        aux (spec := deriveSpec FIPS205.core) (metadataCost trackRaw pkSeed)
          (.inr event) PUnit.unit PUnit.unit PUnit.unit metadata))

end

end Guarded

end SLHDSA.SHAKE128s.Bridge.SharedExperiment
