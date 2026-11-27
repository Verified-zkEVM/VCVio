/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import VCVio.CryptoFoundations.SignatureAlg.CountedExperiment
public import VCVio.OracleComp.Coercions.Add.Basic
public import VCVio.OracleComp.QueryTracking.ObservationOracle
public import HashSig.SLHDSA.Security.LabScheme
public import HashSig.SLHDSA.Security.CoverageRun
public import VCVio.OracleComp.QueryTracking.RandomOracle.Defer

/-! # Relative native execution with phase and work metadata

The deferred graph and its pending cells execute through the existing native role interface.
Message digests and nonces retain their actual inputs and mirror their answers in the graph cache.
Observation markers update the existing metadata without issuing a native query.
-/

public section
open OracleSpec OracleComp SignatureAlg

namespace SLHDSA.Security.CoverageDeferred

variable {vp : ValidatedParams} (core : CorePrimitives vp.params)
variable {ιm Request : Type} {markerSpec : OracleSpec.{0, 0} ιm}

/-- The deferred graph cache and persistent pending cells. -/
abbrev D : Type := LabState core × List (DeriveQuery core ⊕ NodeKey core)

/-- The graph state with its declared cost and current execution phase. -/
abbrev S : Type := D core × (Nat × SigningView.Phase)

/-- The native role of each signature-experiment phase. -/
@[expose]
def phaseRole : SigningView.Phase → Coverage.Role
  | .keygen | .signer => .signer
  | .adversary | .verification => .forger

/-- Event markers update phase and cost; native inputs leave the metadata unchanged. -/
@[expose]
def phaseCostAux (policy : SigningView.Event markerSpec Request → Nat)
    (input : (labSpec core + ObsSpec (SigningView.Event markerSpec Request)).Domain)
    (_before : D core)
    (_answer : ((labSpec core + ObsSpec (SigningView.Event markerSpec Request))).Range input)
    (_after : D core) (metadata : Nat × SigningView.Phase) : Nat × SigningView.Phase :=
  match input with
  | .inl _ => metadata
  | .inr (.ambient phase native) => (metadata.1 + policy (.ambient phase native), phase)
  | .inr (.signingAttempt request) => (metadata.1 + policy (.signingAttempt request), .signer)


variable [SampleableType core.Y] [SampleableType (Bytes vp.params.m)]
  [DecidableEq core.Y] [DecidableEq core.PkSeed] [DecidableEq core.AdrsKey]
  [DecidableEq core.SkPrf]

/-- The deferred graph handler with message digests and nonces routed to the native oracle. -/
@[expose]
noncomputable def relative (pkSeed : core.PkSeed)
    (policy : SigningView.Event markerSpec Request → Nat) :
    QueryImpl ((labSpec core + ObsSpec (SigningView.Event markerSpec Request)))
      (StateT (S core) (OracleComp (Coverage.roleSpec core))) :=
  fun input => StateT.mk fun state =>
    match input with
    | .inr event =>
        pure (⟨⟩, (state.1, phaseCostAux core policy (.inr event) state.1 ⟨⟩ state.1 state.2))
    | .inl (.inl (.inl (.inr (.inl (.hmsg R seed root message))))) => do
        let digest ← Coverage.roleImpl core (phaseRole state.2.2)
          (.inl (.inr (.inl (.hmsg R seed root message))))
        return (digest, (((state.1.1.1.cacheQuery (.inl (.hmsg R seed root message)) digest,
          state.1.1.2), state.1.2), state.2))
    | .inl (.inl (.inr (.inr (salt, message)))) => do
        let R ← Coverage.roleImpl core (phaseRole state.2.2) (.inr (.inr (salt, message)))
        return (R, (((state.1.1.1,
          state.1.1.2.cacheQuery (.inl (.inr (salt, message))) R), state.1.2), state.2))
    | .inl native => do
        let result ← liftComp
          (((slhGraph core pkSeed).deferredImpl native).run state.1) (Coverage.roleSpec core)
        return (result.1, (result.2, state.2))

/-- A marker changes only the declared cost and phase metadata. -/
theorem relative_marker (pkSeed : core.PkSeed)
    (policy : SigningView.Event markerSpec Request → Nat)
    (event : SigningView.Event markerSpec Request) (state : S core) :
    (relative core pkSeed policy (.inr event)).run state =
      pure (⟨⟩, (state.1, phaseCostAux core policy (.inr event) state.1 ⟨⟩ state.1 state.2)) := by
  simp only [relative, StateT.run_mk]

/-- Every message-digest call forwards the actual key and message, then mirrors its answer. -/
theorem relative_hmsg (pkSeed : core.PkSeed)
    (policy : SigningView.Event markerSpec Request → Nat)
    (R : core.Y) (seed : core.PkSeed) (root : core.Y) (message : List Byte) (state : S core) :
    (relative core pkSeed policy
      (.inl (.inl (.inl (.inr (.inl (.hmsg R seed root message))))))).run state = (do
        let digest ← Coverage.roleImpl core (phaseRole state.2.2)
          (.inl (.inr (.inl (.hmsg R seed root message))))
        pure (digest, (((state.1.1.1.cacheQuery (.inl (.hmsg R seed root message)) digest,
          state.1.1.2), state.1.2), state.2))) := by
  simp only [relative, StateT.run_mk]

/-- Every nonce derivation forwards its exact salt/message cell, then mirrors the answer. -/
theorem relative_rand (pkSeed : core.PkSeed)
    (policy : SigningView.Event markerSpec Request → Nat)
    (salt : core.Y) (message : List Byte) (state : S core) :
    ((relative core pkSeed policy) (.inl (.inl (.inr (.inr (salt, message)))))).run state =
      (fun R => (R, (((state.1.1.1,
        state.1.1.2.cacheQuery (.inl (.inr (salt, message))) R), state.1.2), state.2))) <$>
        Coverage.roleImpl core (phaseRole state.2.2) (.inr (.inr (salt, message))) := by
  simp only [relative, StateT.run_mk, map_eq_bind_pure_comp, Function.comp_def]
  rfl

private def IsSelectedNative : (labSpec core).Domain → Prop
  | .inl (.inl (.inr (.inl (.hmsg _ _ _ _)))) => True
  | .inl (.inr (.inr _)) => True
  | _ => False

/-- The remaining native calls execute the existing deferred handler privately. -/
private theorem relative_other (pkSeed : core.PkSeed)
    (policy : SigningView.Event markerSpec Request → Nat)
    (input : (labSpec core).Domain) (other : ¬IsSelectedNative core input) (state : S core) :
    (relative core pkSeed policy (.inl input)).run state = (do
      let result ← liftComp
        (((slhGraph core pkSeed).deferredImpl input).run state.1) (Coverage.roleSpec core)
      pure (result.1, (result.2, state.2))) := by
  rcases input with (((n | (hash | prf)) | (secret | nonce)) | (touch | read))
  · simp only [relative, StateT.run_mk]
  · cases hash <;> first | exact (other trivial).elim | simp only [relative, StateT.run_mk]
  · simp only [relative, StateT.run_mk]
  · simp only [relative, StateT.run_mk]
  · exact (other trivial).elim
  · simp only [relative, StateT.run_mk]
  · simp only [relative, StateT.run_mk]


end SLHDSA.Security.CoverageDeferred
