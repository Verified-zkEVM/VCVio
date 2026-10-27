/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import HashSig.SLHDSA.SHAKE128s.Bridge.SharedExperiment.Factory
public import HashSig.SLHDSA.SHAKE128s.Bridge.Wire.Equality

import all HashSig.SLHDSA.SHAKE128s.Bridge.Wire.Equality

/-!
# Fixed-context wire observations and cached continuations

The actual optional FIPS signer and strict verifier agree with the total wire algorithms at
challenger-generated keys. Context attachment retains the complete raw reply log, chronological
cost in any additive monoid, and the same cached continuation under an arbitrary lawful runtime.
-/

public section

universe v

open OracleComp OracleSpec SignatureAlg
open SLHDSA SLHDSA.Security SLHDSA.SHAKE128s

namespace SLHDSA.SHAKE128s.Bridge.SharedExperiment

/-- Pull the target request observation back along fixed-context attachment only. -/
@[expose] def contextPolicy {C : Type} (ctx : PureContext)
    (policy : SigningView.Event (Game.World FIPS205.Answer) Message → C) :
    SigningView.Event (Game.World FIPS205.Answer) (List Byte) → C
  | .ambient phase input => policy (.ambient phase input)
  | .signingAttempt message => policy (.signingAttempt ⟨message, ctx.bytes⟩)

/-- Attach the context and successful reply constructor without changing accumulated cost. -/
@[expose] def contextObservation {C : Type} (ctx : PureContext)
    (observed : SigningView.Observation (List Byte) (List Byte) (List Byte) C) :
    SigningView.Observation Message (List Byte) (Option (List Byte)) C :=
  { forgery := (⟨observed.forgery.1, ctx.bytes⟩, observed.forgery.2)
    rawLog := Bridge.fixedContextLog ctx observed.rawLog
    verified := observed.verified
    cost := observed.cost }

/-- The actual key-generation computations differ only in public-key representation. -/
private theorem wire_keygen_eq_externalView :
  ∀ (ctx : PureContext),
    (Bridge.wireAlgorithm ctx).keygen =
      Prod.map Bridge.encodeWirePublicKey id <$> (externalView FIPS205.scheme).keygen := by
  intro ctx
  rw [Bridge.wireAlgorithm_keygen, externalView_fips205_keygen]
  rfl

/-- Generated-key consistency identifies the actual optional signing reply. -/
private theorem wire_sign_eq_externalView_of_generated :
  ∀ (ctx : PureContext)
    (keys : PublicKeyCore FIPS205.core × SecretKeyCore FIPS205.core),
    keys ∈ support (externalView FIPS205.scheme).keygen → ∀ (message : List Byte),
    (externalView FIPS205.scheme).sign keys.1 keys.2 ⟨message, ctx.bytes⟩ =
      some <$> (Bridge.wireAlgorithm ctx).sign
        (Bridge.encodeWirePublicKey keys.1) keys.2 message := by
  intro ctx keys member message
  have generated : keys ∈ support FIPS205.internal.keygen := by
    rwa [externalView_fips205_keygen] at member
  have consistent := Bridge.internal_keygen_consistent keys generated
  change FIPS205.scheme.sign keys.2 ⟨message, ctx.bytes⟩ = _
  exact Bridge.fixedContext_sign_eq_wire_sign ctx keys.2 keys.1 consistent message

/-- Strict verification agrees for every typed public key and raw candidate. -/
private theorem wire_verify_eq_externalView :
  ∀ (ctx : PureContext) (pk : PublicKeyCore FIPS205.core) (message signature : List Byte),
    (externalView FIPS205.scheme).verify pk ⟨message, ctx.bytes⟩ signature =
      (Bridge.wireAlgorithm ctx).verify (Bridge.encodeWirePublicKey pk) message signature := by
  intro ctx pk message signature
  simpa only [externalView, Bridge.encodeWirePublicKey] using
    (Bridge.fixedContext_verify_eq_wire_verify ctx pk message signature)

private def attachLog {C : Type} [AddMonoid C] (ctx : PureContext) :
    WriterT (QueryLog (List Byte →ₒ List Byte))
      (SigningView.CostM (Game.World FIPS205.Answer) C) →ᵐ
    WriterT (QueryLog (Message →ₒ Option (List Byte)))
      (SigningView.CostM (Game.World FIPS205.Answer) C) where
  toFun {_α} body := WriterT.mk ((fun result => (result.1, Bridge.fixedContextLog ctx result.2))
    <$> body.run)
  toFun_pure' _ := by rfl
  toFun_bind' body next := by
    ext
    simp [WriterT.run_bind, Bridge.fixedContextLog_append, Functor.map_map,
      bind_map_left, map_bind]

private theorem costed_contextPolicy {C α : Type} [AddMonoid C]
    (ctx : PureContext)
    (policy : SigningView.Event (Game.World FIPS205.Answer) Message → C)
    (phase : SigningView.Phase) (body : OracleComp (Game.World FIPS205.Answer) α) :
    SigningView.costed policy phase body =
      SigningView.costed (contextPolicy ctx policy) phase body := rfl

private theorem countedHandler_attach {C : Type} [AddMonoid C]
    (policy : SigningView.Event (Game.World FIPS205.Answer) Message → C)
    (ctx : PureContext) (keys : PublicKeyCore FIPS205.core × SecretKeyCore FIPS205.core)
    (generated : keys ∈ support (externalView FIPS205.scheme).keygen)
    (input : Bridge.WireAdversarySpec.Domain) :
    simulateQ (SigningView.countedHandler policy (externalView FIPS205.scheme) keys.1 keys.2)
        (Bridge.fixedContextHandler ctx input) =
      attachLog ctx (SigningView.countedHandler (contextPolicy ctx policy)
        (SigningView.ofTotal (Bridge.wireAlgorithm ctx))
        (Bridge.encodeWirePublicKey keys.1) keys.2 input) := by
  cases input with
  | inl input =>
      rw [Bridge.fixedContextHandler_world, simulateQ_spec_query]
      ext
      simp [SigningView.countedHandler,
        QueryImpl.withAddCost_apply, attachLog, contextPolicy, Bridge.fixedContextLog,
        WriterT.liftM_def, Functor.map_map]
  | inr message =>
      rw [Bridge.fixedContextHandler_sign, simulateQ_map, simulateQ_spec_query]
      simp only [SigningView.countedHandler, QueryImpl.add_apply_inr]
      ext
      simp only [WriterT.run_map, SigningView.countedSigningOracle_run]
      rw [wire_sign_eq_externalView_of_generated ctx keys generated message]
      simp [attachLog, SigningView.countedSigningOracle_run, SigningView.ofTotal,
        SigningView.costed, contextPolicy, Bridge.fixedContextLog, simulateQ_map,
        Functor.map_map]



/-- Adaptive context attachment retains the full raw log and ordered policy cost. -/
private theorem countedPhase_wire_eq_externalView :
  ∀ {C : Type} [AddMonoid C]
    (policy : SigningView.Event (Game.World FIPS205.Answer) Message → C)
    (ctx : PureContext) (keys : PublicKeyCore FIPS205.core × SecretKeyCore FIPS205.core),
    keys ∈ support (externalView FIPS205.scheme).keygen →
    ∀ {α : Type} (body : OracleComp Bridge.WireAdversarySpec α),
    (SigningView.countedPhase policy (externalView FIPS205.scheme) keys.1 keys.2
      (simulateQ (Bridge.fixedContextHandler ctx) body)).runAdd =
        (fun result : (α × QueryLog (List Byte →ₒ List Byte)) × C =>
          ((result.1.1, Bridge.fixedContextLog ctx result.1.2), result.2)) <$>
          (SigningView.countedPhase (contextPolicy ctx policy)
            (SigningView.ofTotal (Bridge.wireAlgorithm ctx))
            (Bridge.encodeWirePublicKey keys.1) keys.2 body).runAdd := by
  intro C inst policy ctx keys generated α body
  have interpreted := QueryImpl.simulateQ_simulateQ_eq_of_apply
    (countedHandler_attach policy ctx keys generated) body
  have natural := PFunctor.FreeM.liftM_natural
    (SigningView.countedHandler (contextPolicy ctx policy)
      (SigningView.ofTotal (Bridge.wireAlgorithm ctx))
      (Bridge.encodeWirePublicKey keys.1) keys.2)
    (attachLog ctx) body
  have raw := interpreted.trans natural.symm
  have result := congrArg (fun computation => computation.run.runAdd) raw
  simpa only [SigningView.countedPhase, attachLog, AddWriterT.runAdd,
    WriterT.run_mk, WriterT.run_map, Functor.map_map, Prod.map, simulateQ, id_eq] using result

private theorem generated_key_support {ι Request C K : Type} {spec : OracleSpec ι} [AddMonoid C]
    (policy : SigningView.Event spec Request → C) (body : OracleComp spec K)
    (tagged : K × C) (member : tagged ∈ support (SigningView.costed policy .keygen body).runAdd) :
    tagged.1 ∈ support body := by
  rw [← SigningView.costed_erases policy .keygen body, support_map]
  exact ⟨tagged, member, rfl⟩


private theorem countedPhase_map {ι C Request PK SK Sig Reply α β : Type}
    {spec : OracleSpec ι} [AddMonoid C] (policy : SigningView.Event spec Request → C)
    (view : SigningView (OracleComp spec) Request PK SK Sig Reply)
    (pk : PK) (sk : SK) (f : α → β)
    (body : OracleComp (spec + (Request →ₒ Reply)) α) :
    SigningView.countedPhase policy view pk sk (f <$> body) =
      (fun result => (f result.1, result.2)) <$>
        SigningView.countedPhase policy view pk sk body := by
  unfold SigningView.countedPhase
  rw [simulateQ_map]
  rfl


private theorem costed_wire_verifier {C : Type} [AddMonoid C]
    (policy : SigningView.Event (Game.World FIPS205.Answer) Message → C)
    (ctx : PureContext) (pk : PublicKeyCore FIPS205.core) (message signature : List Byte) :
    SigningView.costed policy .verification
        ((externalView FIPS205.scheme).verify pk ⟨message, ctx.bytes⟩ signature) =
      SigningView.costed (contextPolicy ctx policy) .verification
        ((SigningView.ofTotal (Bridge.wireAlgorithm ctx)).verify
          (Bridge.encodeWirePublicKey pk) message signature) := by
  simp only [SigningView.ofTotal]
  rw [wire_verify_eq_externalView ctx pk message signature]
  exact costed_contextPolicy ctx policy .verification
    ((Bridge.wireAlgorithm ctx).verify (Bridge.encodeWirePublicKey pk) message signature)


/-- Full actual context observations retain arbitrary chronological additive cost. -/
theorem countedExperiment_wire_eq_externalView :
  ∀ {C : Type} [AddMonoid C]
    (policy : SigningView.Event (Game.World FIPS205.Answer) Message → C)
    (ctx : PureContext) (adversary : StrongUnforgeableAdversary (Bridge.wireAlgorithm ctx)),
    SigningView.countedExperiment policy (externalView FIPS205.scheme)
      (externalMain (Bridge.fixedContextAdversary ctx adversary)) =
        contextObservation ctx <$>
          SigningView.countedExperiment (contextPolicy ctx policy)
            (SigningView.ofTotal (Bridge.wireAlgorithm ctx)) adversary.main := by
  intro C inst policy ctx adversary
  have keygen : SigningView.costed (contextPolicy ctx policy) .keygen
      (SigningView.ofTotal (Bridge.wireAlgorithm ctx)).keygen =
      Prod.map Bridge.encodeWirePublicKey id <$>
        SigningView.costed policy .keygen (externalView FIPS205.scheme).keygen := by
    have transported := congrArg
      (SigningView.costed (contextPolicy ctx policy) .keygen)
      (wire_keygen_eq_externalView ctx)
    calc
      _ = SigningView.costed (contextPolicy ctx policy) .keygen
          (Prod.map Bridge.encodeWirePublicKey id <$>
            (externalView FIPS205.scheme).keygen) := transported
      _ = _ := simulateQ_map _ _ _
  unfold SigningView.countedExperiment
  rw [keygen]
  generalize commonEq :
    SigningView.costed policy .keygen (externalView FIPS205.scheme).keygen = common
  simp only [AddWriterT.runAdd_bind, AddWriterT.runAdd_pure,
    map_bind, bind_map_left, Functor.map_map]
  apply OracleComp.bind_congr_of_forall_mem_support
  intro tagged member
  have actualMember : tagged ∈ support
      (SigningView.costed policy .keygen (externalView FIPS205.scheme).keygen).runAdd := by
    rwa [commonEq]
  have generated := generated_key_support policy
    (externalView FIPS205.scheme).keygen tagged actualMember
  simp only [externalMain, Bridge.fixedContextAdversary, Bridge.fixedContextMain,
    Functor.map_map, countedPhase_map, AddWriterT.runAdd_map, bind_map_left,
    Functor.map_map]
  rw [countedPhase_wire_eq_externalView policy ctx tagged.1 generated]
  simp only [bind_map_left, Prod.map, id_eq, Bridge.encodeWirePublicKey]
  apply OracleComp.bind_congr_of_forall_mem_support
  rintro ⟨⟨forgery, signed⟩, phaseCost⟩ _
  rw [costed_wire_verifier policy ctx tagged.1.1 forgery.1 forgery.2]
  simp only [Bridge.encodeWirePublicKey]
  generalize verificationEq :
    (SigningView.costed (contextPolicy ctx policy) .verification
      ((SigningView.ofTotal (Bridge.wireAlgorithm ctx)).verify
        ((publicKeyCodec (Concrete.shakeWireCodec FIPS205.params.params)).encode tagged.1.1)
        forgery.1 forgery.2)).runAdd = verification
  apply OracleComp.bind_congr_of_forall_mem_support
  rintro ⟨verified, verificationCost⟩ _
  simp only [map_pure, contextObservation]

/-- The same handler and initial cache pass the complete observation to any continuation. -/
theorem countedExperiment_wire_run_bind_eq_externalView :
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
        (externalMain (Bridge.fixedContextAdversary ctx adversary)))).run initial >>= next) := by
  intro C inst policy ctx adversary Cache β m instM instL handler initial next
  rw [countedExperiment_wire_eq_externalView policy ctx adversary]
  generalize programEq : SigningView.countedExperiment (contextPolicy ctx policy)
    (SigningView.ofTotal (Bridge.wireAlgorithm ctx)) adversary.main = program
  rw [simulateQ_map]
  simp only [StateT.run_map, bind_map_left]

end SLHDSA.SHAKE128s.Bridge.SharedExperiment
