/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: VCVio Contributors
-/

module
public import VCVio.CryptoFoundations.SignatureAlg.CountedExperiment
public import VCVio.OracleComp.SimSemantics.QueryImpl.Compose
import PolyFun.Control.Monad.Hom.Writer

/-!
# Exact realization of counted signing experiments

A named oracle interpretation preserves complete observations when its query charges agree.
Secret keys may change through an explicit map while public keys and raw replies remain exact.
Readback is separate: a raw observation does not itself interpret which replies are signatures.
-/

public section

namespace SignatureAlg.SigningView

open OracleComp OracleSpec

variable {ι κ Request PK SKs SKt Sig Reply C : Type}
  {S : OracleSpec.{0, 0} ι} {T : OracleSpec.{0, 0} κ} [AddMonoid C]

private abbrev mapCost (impl : QueryImpl S (OracleComp T)) : CostM S C →ᵐ CostM T C :=
  WriterT.mapHom (ω := Multiplicative C) (simulateQ' impl)

private theorem mapCost_runAdd (impl : QueryImpl S (OracleComp T)) {α : Type}
    (body : CostM S C α) :
    (mapCost impl body).runAdd = simulateQ impl body.runAdd := by
  simp only [mapCost, AddWriterT.runAdd, WriterT.run_mapHom, simulateQ_map]

private theorem mapCost_addTell (impl : QueryImpl S (OracleComp T)) (amount : C) :
    mapCost impl (AddWriterT.addTell amount) = AddWriterT.addTell amount := by
  apply WriterT.ext
  simp only [mapCost, WriterT.run_mapHom, AddWriterT.run_addTell, simulateQ_pure]

private theorem mapCost_lift (impl : QueryImpl S (OracleComp T)) {α : Type}
    (body : OracleComp S α) :
    mapCost impl (liftM body : CostM S C α) = liftM (simulateQ impl body) := by
  apply WriterT.ext
  simp only [mapCost, WriterT.run_mapHom, WriterT.run_monadLift, simulateQ_map]

private theorem mapCost_query (impl : QueryImpl S (OracleComp T))
    (cs : Event S Request → C) (phase : Phase) (q : S.Domain) :
    mapCost impl (((QueryImpl.id' S).withAddCost (fun t => cs (.ambient phase t))) q) = (do
      AddWriterT.addTell (cs (.ambient phase q))
      liftM (impl q)) := by
  simp only [QueryImpl.withAddCost_apply, MonadHom.mmap_bind, mapCost_addTell,
    mapCost_lift, QueryImpl.id'_apply, simulateQ_spec_query]

private theorem mapCost_costed (impl : QueryImpl S (OracleComp T))
    (cs : Event S Request → C) (ct : Event T Request → C)
    (compatible : ∀ phase q, costed ct phase (impl q) = (do
      AddWriterT.addTell (cs (.ambient phase q)); liftM (impl q)))
    (phase : Phase) {α : Type} (body : OracleComp S α) :
    mapCost impl (costed cs phase body) = costed ct phase (simulateQ impl body) := by
  have natural := PFunctor.FreeM.liftM_natural
    ((QueryImpl.id' S).withAddCost (fun q => cs (.ambient phase q))) (mapCost impl) body
  change mapCost impl (costed cs phase body) =
    simulateQ (fun q => mapCost impl
      (((QueryImpl.id' S).withAddCost (fun t => cs (.ambient phase t))) q)) body at natural
  rw [natural]
  simp only [mapCost_query, ← compatible]
  change simulateQ (((QueryImpl.id' T).withAddCost
    (fun q => ct (.ambient phase q))) ∘ₛ impl) body = _
  rw [QueryImpl.simulateQ_compose]
  rfl

/-- Exact query-cost compatibility extends to each complete phase component.

The cost monoid need not be commutative.
The interpretation may expand a source query into several target queries.
-/
theorem costed_simulateQ (impl : QueryImpl S (OracleComp T))
    (cs : Event S Request → C) (ct : Event T Request → C)
    (compatible : ∀ phase q, costed ct phase (impl q) = (do
      AddWriterT.addTell (cs (.ambient phase q)); liftM (impl q)))
    (phase : Phase) {α : Type} (body : OracleComp S α) :
    simulateQ impl (costed cs phase body).runAdd =
      (costed ct phase (simulateQ impl body)).runAdd := by
  rw [← mapCost_runAdd, mapCost_costed impl cs ct compatible]

-- Map only the base of the existing chronological append writer.
private def mapLog (impl : QueryImpl S (OracleComp T)) :
    LoggedCostM S Request Reply C →ᵐ LoggedCostM T Request Reply C where
  toFun {_α} action := WriterT.mk (mapCost impl action.run)
  toFun_pure' value := by
    apply WriterT.ext
    simp only [WriterT.run_mk, WriterT.run_pure', MonadHom.mmap_pure]
  toFun_bind' action next := by
    apply WriterT.ext
    simp only [WriterT.run_mk, WriterT.run_bind', MonadHom.mmap_bind, MonadHom.mmap_map]

private theorem mapLog_signing (impl : QueryImpl S (OracleComp T))
    (cs : Event S Request → C) (ct : Event T Request → C)
    (source : SigningView (OracleComp S) Request PK SKs Sig Reply)
    (target : SigningView (OracleComp T) Request PK SKt Sig Reply) (keyMap : SKs → SKt)
    (compatible : ∀ phase q, costed ct phase (impl q) = (do
      AddWriterT.addTell (cs (.ambient phase q)); liftM (impl q)))
    (attempt : ∀ request, cs (.signingAttempt request) = ct (.signingAttempt request))
    (sign : ∀ pk sk request, simulateQ impl (source.sign pk sk request) =
      target.sign pk (keyMap sk) request) (pk : PK) (sk : SKs) (request : Request) :
    mapLog impl (countedSigningOracle cs source pk sk request) =
      countedSigningOracle ct target pk (keyMap sk) request := by
  apply WriterT.ext
  change mapCost impl (countedSigningOracle cs source pk sk request).run = _
  rw [countedSigningOracle_run, countedSigningOracle_run]
  simp only [MonadHom.mmap_bind, mapCost_addTell, mapCost_costed impl cs ct compatible,
    sign, MonadHom.mmap_pure, attempt]

private theorem mapLog_handler (impl : QueryImpl S (OracleComp T))
    (cs : Event S Request → C) (ct : Event T Request → C)
    (source : SigningView (OracleComp S) Request PK SKs Sig Reply)
    (target : SigningView (OracleComp T) Request PK SKt Sig Reply) (keyMap : SKs → SKt)
    (compatible : ∀ phase q, costed ct phase (impl q) = (do
      AddWriterT.addTell (cs (.ambient phase q)); liftM (impl q)))
    (attempt : ∀ request, cs (.signingAttempt request) = ct (.signingAttempt request))
    (sign : ∀ pk sk request, simulateQ impl (source.sign pk sk request) =
      target.sign pk (keyMap sk) request) (pk : PK) (sk : SKs)
    (input : (S + (Request →ₒ Reply)).Domain) :
    mapLog impl (countedHandler cs source pk sk input) =
      ((countedHandler ct target pk (keyMap sk)) ∘ₛ
        impl.addLift (QueryImpl.id' (Request →ₒ Reply))) input := by
  cases input with
  | inl q =>
    apply WriterT.ext
    change (mapLog impl (liftM (((QueryImpl.id' S).withAddCost
      (fun input => cs (.ambient .adversary input))) q))).run = _
    simp only [mapLog, WriterT.run_mk, WriterT.run_monadLift', MonadHom.mmap_map]
    change (fun x => (x, ∅)) <$> mapCost impl
      (((QueryImpl.id' S).withAddCost (fun t => cs (.ambient .adversary t))) q) = _
    rw [mapCost_query, ← compatible]
    simp only [QueryImpl.apply_compose, QueryImpl.addLift_def, QueryImpl.add_apply_inl,
      QueryImpl.liftTarget_apply, countedHandler, countedHandlerUsing,
      QueryImpl.simulateQ_add_liftM_left,
      writerT_run_simulateQ_liftTarget]
    rfl
  | inr request =>
    simp only [countedHandler, countedHandlerUsing, QueryImpl.add_apply_inr,
      QueryImpl.apply_compose,
      QueryImpl.addLift_def, QueryImpl.liftTarget_apply, QueryImpl.id'_apply,
      QueryImpl.simulateQ_add_liftM_right, simulateQ_spec_query]
    exact mapLog_signing impl cs ct source target keyMap compatible attempt sign pk sk request

private theorem mapCost_phase (impl : QueryImpl S (OracleComp T))
    (cs : Event S Request → C) (ct : Event T Request → C)
    (source : SigningView (OracleComp S) Request PK SKs Sig Reply)
    (target : SigningView (OracleComp T) Request PK SKt Sig Reply) (keyMap : SKs → SKt)
    (compatible : ∀ phase q, costed ct phase (impl q) = (do
      AddWriterT.addTell (cs (.ambient phase q)); liftM (impl q)))
    (attempt : ∀ request, cs (.signingAttempt request) = ct (.signingAttempt request))
    (sign : ∀ pk sk request, simulateQ impl (source.sign pk sk request) =
      target.sign pk (keyMap sk) request) (pk : PK) (sk : SKs)
    {α : Type} (body : OracleComp (S + (Request →ₒ Reply)) α) :
    mapCost impl (countedPhase cs source pk sk body) =
      countedPhase ct target pk (keyMap sk)
        (simulateQ (impl.addLift (QueryImpl.id' (Request →ₒ Reply))) body) := by
  have natural := PFunctor.FreeM.liftM_natural (countedHandler cs source pk sk)
    (mapLog impl) body
  change mapLog impl (simulateQ (countedHandler cs source pk sk) body) =
    simulateQ (fun q => mapLog impl (countedHandler cs source pk sk q)) body at natural
  change (mapLog impl (simulateQ (countedHandler cs source pk sk) body)).run = _
  rw [natural]
  simp only [mapLog_handler impl cs ct source target keyMap compatible attempt sign]
  rw [QueryImpl.simulateQ_compose]
  rfl

private theorem costed_map (policy : Event T Request → C) (phase : Phase)
    {α β : Type} (body : OracleComp T α) (f : α → β) :
    costed policy phase (f <$> body) = f <$> costed policy phase body := by
  exact simulateQ_map _ body f

-- Keep the existing finite experiment body separate from its final cost packaging.
private def experimentBody {ι SK : Type} {spec : OracleSpec ι}
    (policy : Event spec Request → C)
    (view : SigningView (OracleComp spec) Request PK SK Sig Reply)
    (A : PK → OracleComp (spec + (Request →ₒ Reply)) (Request × Sig)) :
    CostM spec C (Outcome Request Sig Reply) := do
  let (pk, sk) ← costed policy .keygen view.keygen
  let (forgery, rawLog) ← countedPhase policy view pk sk (A pk)
  let verified ← costed policy .verification (view.verify pk forgery.1 forgery.2)
  return ⟨forgery, rawLog, verified⟩

/-- Realize the complete counted experiment at the supplied named source client.

The equality retains every raw signing reply and the ordered cost of every phase.
Only secret keys change through `keyMap`.
No readback or winning-event premise is needed for this raw observation equality.
-/
theorem countedExperiment_realize (impl : QueryImpl S (OracleComp T))
    (cs : Event S Request → C) (ct : Event T Request → C)
    (source : SigningView (OracleComp S) Request PK SKs Sig Reply)
    (target : SigningView (OracleComp T) Request PK SKt Sig Reply) (keyMap : SKs → SKt)
    (compatible : ∀ phase q, costed ct phase (impl q) = (do
      AddWriterT.addTell (cs (.ambient phase q)); liftM (impl q)))
    (attempt : ∀ request, cs (.signingAttempt request) = ct (.signingAttempt request))
    (keygen : target.keygen = (fun keys : PK × SKs => (keys.1, keyMap keys.2)) <$>
      simulateQ impl source.keygen)
    (sign : ∀ pk sk request, simulateQ impl (source.sign pk sk request) =
      target.sign pk (keyMap sk) request)
    (verify : ∀ pk request sig, simulateQ impl (source.verify pk request sig) =
      target.verify pk request sig)
    (AS : PK → OracleComp (S + (Request →ₒ Reply)) (Request × Sig)) :
    simulateQ impl (countedExperiment cs source AS) =
      countedExperiment ct target
        (fun pk => simulateQ (impl.addLift (QueryImpl.id' (Request →ₒ Reply))) (AS pk)) := by
  have body : mapCost impl (experimentBody cs source AS) =
      experimentBody ct target
        (fun pk => simulateQ (impl.addLift (QueryImpl.id' (Request →ₒ Reply))) (AS pk)) := by
    unfold experimentBody
    rw [keygen, costed_map]
    simp only [MonadHom.mmap_bind, mapCost_costed impl cs ct compatible, bind_map_left]
    apply congrArg (fun next => costed ct .keygen (simulateQ impl source.keygen) >>= next)
    funext keys
    rcases keys with ⟨pk, sk⟩
    apply congrArg₂
      (fun (action : CostM T C ((Request × Sig) × QueryLog (Request →ₒ Reply)))
        (next : ((Request × Sig) × QueryLog (Request →ₒ Reply)) →
          CostM T C (Outcome Request Sig Reply)) => action >>= next)
    · exact mapCost_phase impl cs ct source target keyMap compatible attempt sign pk sk (AS pk)
    · funext result
      rcases result with ⟨forgery, rawLog⟩
      simp only [verify, MonadHom.mmap_pure]
  change simulateQ impl ((fun result =>
    ({ toOutcome := result.1, cost := result.2 } : Observation Request Sig Reply C)) <$>
      (experimentBody cs source AS).runAdd) = _
  rw [simulateQ_map, ← mapCost_runAdd, body]
  rfl

/-- Inject the original target client into the source interface and recover that same client.

The left inverse is an exact free-program law, not a choice of another adversary.
-/
theorem countedExperiment_realize_injected (impl : QueryImpl S (OracleComp T))
    (inject : QueryImpl T (OracleComp S)) (roundtrip : impl ∘ₛ inject = QueryImpl.id' T)
    (cs : Event S Request → C) (ct : Event T Request → C)
    (source : SigningView (OracleComp S) Request PK SKs Sig Reply)
    (target : SigningView (OracleComp T) Request PK SKt Sig Reply) (keyMap : SKs → SKt)
    (compatible : ∀ phase q, costed ct phase (impl q) = (do
      AddWriterT.addTell (cs (.ambient phase q)); liftM (impl q)))
    (attempt : ∀ request, cs (.signingAttempt request) = ct (.signingAttempt request))
    (keygen : target.keygen = (fun keys : PK × SKs => (keys.1, keyMap keys.2)) <$>
      simulateQ impl source.keygen)
    (sign : ∀ pk sk request, simulateQ impl (source.sign pk sk request) =
      target.sign pk (keyMap sk) request)
    (verify : ∀ pk request sig, simulateQ impl (source.verify pk request sig) =
      target.verify pk request sig)
    (A : PK → OracleComp (T + (Request →ₒ Reply)) (Request × Sig)) :
    simulateQ impl (countedExperiment cs source
      (fun pk => simulateQ (inject.addLift (QueryImpl.id' (Request →ₒ Reply))) (A pk))) =
      countedExperiment ct target A := by
  rw [countedExperiment_realize impl cs ct source target keyMap compatible attempt
    keygen sign verify]
  have front : (impl.addLift (QueryImpl.id' (Request →ₒ Reply))) ∘ₛ
      (inject.addLift (QueryImpl.id' (Request →ₒ Reply))) =
        QueryImpl.id' (T + (Request →ₒ Reply)) := by
    ext (q | request)
    · simp only [QueryImpl.apply_compose, QueryImpl.addLift_def, QueryImpl.add_apply_inl,
        QueryImpl.liftTarget_apply, QueryImpl.simulateQ_add_liftM_left]
      have h := congrFun roundtrip q
      rw [simulateQ_liftTarget]
      exact congrArg (fun body : OracleComp T (T.Range q) =>
        (liftM body : OracleComp (T + (Request →ₒ Reply)) (T.Range q))) h
    · simp only [QueryImpl.apply_compose, QueryImpl.addLift_def, QueryImpl.add_apply_inr,
        QueryImpl.liftTarget_apply, QueryImpl.id'_apply,
        QueryImpl.simulateQ_add_liftM_right, simulateQ_spec_query]
      rfl
  simp only [← QueryImpl.simulateQ_compose, front, simulateQ_id']

end SignatureAlg.SigningView
