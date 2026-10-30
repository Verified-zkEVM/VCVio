/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import VCVio.OracleComp.SimSemantics.QueryImpl.Relabel
public import ToMathlib.Control.WriterT.Map
public import VCVio.CryptoFoundations.SignatureAlg.CountedExperiment

/-!
# Answer representations of counted signature experiments

Queries retain their inputs while their dependent answers are read through an equivalence.
A pointwise policy square preserves the complete candidate, raw replies, verification and
ordered cost. Requests, signatures and signing replies remain separate types.
-/

public section

universe idx

open OracleComp OracleSpec SignatureAlg SignatureAlg.SigningView

namespace SignatureAlg.SigningView

variable {ι : Type idx} {R S : OracleSpec.{idx, 0} ι}
variable {Request PK SK Sig Reply C : Type} [AddMonoid C]

/-- An execution event at the same input and phase in the target answer representation. -/
@[expose] def relabelEvent : Event R Request → Event S Request
  | .ambient phase input => .ambient phase input
  | .signingAttempt request => .signingAttempt request

/-- Signing requests and their reply carrier are unchanged by ambient answer conversion. -/
@[expose] def relabelSigningAnswers (e : ∀ input, R input ≃ S input) :
    ∀ input, (R + (Request →ₒ Reply)).Range input ≃ (S + (Request →ₒ Reply)).Range input
  | .inl input => e input
  | .inr _ => Equiv.refl _

/-- Interpret the same view's component programs through the answer conversion. -/
@[expose] def relabelView (e : ∀ input, R input ≃ S input)
    (view : SigningView (OracleComp R) Request PK SK Sig Reply) :
    SigningView (OracleComp S) Request PK SK Sig Reply where
  keygen := simulateQ (QueryImpl.relabel e) view.keygen
  sign pk sk request := simulateQ (QueryImpl.relabel e) (view.sign pk sk request)
  verify pk request signature := simulateQ (QueryImpl.relabel e) (view.verify pk request signature)
  readback := view.readback

/-- The same signing-enabled main program reads converted ambient answers. -/
@[expose] def relabelMain (e : ∀ input, R input ≃ S input)
    (main : PK → OracleComp (R + (Request →ₒ Reply)) (Request × Sig)) :
    PK → OracleComp (S + (Request →ₒ Reply)) (Request × Sig) :=
  fun pk => simulateQ (QueryImpl.relabel (relabelSigningAnswers e)) (main pk)

/-- The view's actual reply readback is unchanged. -/
theorem imageView_readback (e : ∀ input, R input ≃ S input)
    (view : SigningView (OracleComp R) Request PK SK Sig Reply) (reply : Reply) :
    (relabelView e view).readback reply = view.readback reply := rfl

/-- The answer-conversion fold packaged as the existing free-monad morphism. -/
private def ambientMorphism (e : ∀ input, R input ≃ S input) :
    OracleComp R →ᵐ OracleComp S := simulateQ' (QueryImpl.relabel e)

/-- The existing multiplicative writer morphism retains the entire ordered additive cost. -/
private def costMorphism (e : ∀ input, R input ≃ S input) :
    CostM R C →ᵐ CostM S C := WriterT.mapHom (ambientMorphism e)

/-- The append writer morphism retains every chronological signing reply. -/
private def phaseMorphism (e : ∀ input, R input ≃ S input) :
    LoggedCostM R Request Reply C →ᵐ LoggedCostM S Request Reply C :=
  WriterT.mapBaseAppendHom (costMorphism e)

/-- Base conversion leaves the accumulated additive cost untouched. -/
private theorem costMorphism_runAdd (e : ∀ input, R input ≃ S input) {α : Type}
    (body : CostM R C α) :
    (costMorphism e body).runAdd = ambientMorphism e body.runAdd := by
  simp only [costMorphism, AddWriterT.runAdd, WriterT.run_mapHom, MonadHom.mmap_map]

/-- A fixed charge has no ambient query to convert. -/
private theorem costMorphism_addTell (e : ∀ input, R input ≃ S input) (cost : C) :
    costMorphism e (AddWriterT.addTell cost : CostM R C PUnit) = AddWriterT.addTell cost := by
  apply WriterT.ext
  simp [costMorphism, ambientMorphism, AddWriterT.addTell]

/-- Lifting into the reply writer retains the empty raw log. -/
private theorem phaseMorphism_lift (e : ∀ input, R input ≃ S input) {α : Type}
    (body : CostM R C α) :
    phaseMorphism e (liftM body : LoggedCostM R Request Reply C α) =
      (liftM (costMorphism e body) : LoggedCostM S Request Reply C α) := by
  apply WriterT.ext
  simp [phaseMorphism, MonadHom.mmap_map]

/-- One ambient query preserves its actual phase-specific charge before reading back its answer. -/
private theorem costQuerySquare (e : ∀ input, R input ≃ S input)
    (policyR : Event R Request → C) (policyS : Event S Request → C)
    (diagram : ∀ event, policyR event = policyS (relabelEvent event))
    (phase : Phase) (input : R.Domain) :
    costMorphism e
        (((QueryImpl.id' R).withAddCost (fun input => policyR (.ambient phase input))) input) =
      simulateQ ((QueryImpl.id' S).withAddCost (fun input => policyS (.ambient phase input)))
        (QueryImpl.relabel e input) := by
  have hcost : policyR (.ambient phase input) = policyS (.ambient phase input) :=
    diagram (.ambient phase input)
  apply WriterT.ext
  simp [costMorphism, ambientMorphism, QueryImpl.withAddCost_apply, QueryImpl.id'_apply,
    QueryImpl.relabel_apply, AddWriterT.addTell, Functor.map_map, hcost]

/-- Costed components commute with answer conversion through the existing fold naturality. -/
private theorem costedSquare (e : ∀ input, R input ≃ S input)
    (policyR : Event R Request → C) (policyS : Event S Request → C)
    (diagram : ∀ event, policyR event = policyS (relabelEvent event)) (phase : Phase)
    {α : Type} (body : OracleComp R α) :
    costMorphism e (costed policyR phase body) =
      costed policyS phase (simulateQ (QueryImpl.relabel e) body) := by
  calc
    _ = simulateQ (fun input => costMorphism e
          (((QueryImpl.id' R).withAddCost
            (fun input => policyR (.ambient phase input))) input)) body :=
      PFunctor.FreeM.liftM_natural _ (costMorphism e) body
    _ = simulateQ (QueryImpl.compose
          ((QueryImpl.id' S).withAddCost (fun input => policyS (.ambient phase input)))
          (QueryImpl.relabel e)) body := by
      congr 1
      funext input
      exact costQuerySquare e policyR policyS diagram phase input
    _ = _ := QueryImpl.simulateQ_compose _ _ body

/-- Attempt charging and the actual signing reply commute with answer conversion. -/
private theorem signingOracleSquare (e : ∀ input, R input ≃ S input)
    (policyR : Event R Request → C) (policyS : Event S Request → C)
    (view : SigningView (OracleComp R) Request PK SK Sig Reply)
    (diagram : ∀ event, policyR event = policyS (relabelEvent event))
    (pk : PK) (sk : SK) (request : Request) :
    phaseMorphism e (countedSigningOracle policyR view pk sk request) =
      countedSigningOracle policyS (relabelView e view) pk sk request := by
  have hcharge : policyR (.signingAttempt request) = policyS (.signingAttempt request) :=
    diagram (.signingAttempt request)
  apply WriterT.ext
  simp only [phaseMorphism, WriterT.run_mapBaseAppendHom, countedSigningOracle_run,
    MonadHom.mmap_bind, MonadHom.mmap_pure, costMorphism_addTell,
    costedSquare e policyR policyS diagram .signer, relabelView, hcharge]

/-- The client handler retains direct-query charges and chronological raw replies. -/
private theorem countedHandlerSquare (e : ∀ input, R input ≃ S input)
    (policyR : Event R Request → C) (policyS : Event S Request → C)
    (view : SigningView (OracleComp R) Request PK SK Sig Reply)
    (diagram : ∀ event, policyR event = policyS (relabelEvent event))
    (pk : PK) (sk : SK) (input : (R + (Request →ₒ Reply)).Domain) :
    phaseMorphism e (countedHandler policyR view pk sk input) =
      simulateQ (countedHandler policyS (relabelView e view) pk sk)
        (QueryImpl.relabel (relabelSigningAnswers e) input) := by
  cases input with
  | inl input =>
    change phaseMorphism e
        (liftM (((QueryImpl.id' R).withAddCost
          (fun query => policyR (.ambient .adversary query))) input)) =
      simulateQ (countedHandler policyS (relabelView e view) pk sk)
        (QueryImpl.relabel (relabelSigningAnswers e) (Sum.inl input))
    rw [phaseMorphism_lift, costQuerySquare e policyR policyS diagram .adversary]
    simp only [QueryImpl.relabel_apply, relabelSigningAnswers, simulateQ_map, simulateQ_spec_query,
      countedHandler, QueryImpl.add_apply_inl, QueryImpl.liftTarget_apply]
    apply WriterT.ext
    simp [Functor.map_map]
  | inr request =>
    simpa [countedHandler, QueryImpl.relabel_apply, relabelSigningAnswers] using
      signingOracleSquare e policyR policyS view diagram pk sk request

/-- The signing-enabled client phase retains its full raw reply log and ordered cost. -/
private theorem countedPhaseSquare (e : ∀ input, R input ≃ S input)
    (policyR : Event R Request → C) (policyS : Event S Request → C)
    (view : SigningView (OracleComp R) Request PK SK Sig Reply)
    (diagram : ∀ event, policyR event = policyS (relabelEvent event))
    (pk : PK) (sk : SK) {α : Type}
    (body : OracleComp (R + (Request →ₒ Reply)) α) :
    costMorphism e (countedPhase policyR view pk sk body) =
      countedPhase policyS (relabelView e view) pk sk
        (simulateQ (QueryImpl.relabel (relabelSigningAnswers e)) body) := by
  have natural : phaseMorphism e (simulateQ (countedHandler policyR view pk sk) body) =
      simulateQ (countedHandler policyS (relabelView e view) pk sk)
        (simulateQ (QueryImpl.relabel (relabelSigningAnswers e)) body) := by
    calc
      _ = simulateQ (fun input => phaseMorphism e
            (countedHandler policyR view pk sk input)) body :=
        PFunctor.FreeM.liftM_natural _ (phaseMorphism e) body
      _ = simulateQ (QueryImpl.compose
            (countedHandler policyS (relabelView e view) pk sk)
            (QueryImpl.relabel (relabelSigningAnswers e))) body := by
        congr 1
        funext input
        exact countedHandlerSquare e policyR policyS view diagram pk sk input
      _ = _ := QueryImpl.simulateQ_compose _ _ body
  have h := congrArg (fun result : LoggedCostM S Request Reply C α => result.run) natural
  simpa only [phaseMorphism, WriterT.run_mapBaseAppendHom, countedPhase] using h

/-- Answer conversion preserves the complete counted experiment under the actual policy square. -/
theorem countedExperiment_relabel (e : ∀ input, R input ≃ S input)
    (policyR : Event R Request → C) (policyS : Event S Request → C)
    (view : SigningView (OracleComp R) Request PK SK Sig Reply)
    (main : PK → OracleComp (R + (Request →ₒ Reply)) (Request × Sig))
    (diagram : ∀ event, policyR event = policyS (relabelEvent event)) :
    simulateQ (QueryImpl.relabel e) (countedExperiment policyR view main) =
      countedExperiment policyS (relabelView e view) (relabelMain e main) := by
  change ambientMorphism e (countedExperiment policyR view main) = _
  simp only [countedExperiment, MonadHom.mmap_map, ← costMorphism_runAdd,
    MonadHom.mmap_bind, MonadHom.mmap_pure,
    costedSquare e policyR policyS diagram .keygen,
    costedSquare e policyR policyS diagram .verification,
    countedPhaseSquare e policyR policyS view diagram, relabelView, relabelMain]

end SignatureAlg.SigningView
