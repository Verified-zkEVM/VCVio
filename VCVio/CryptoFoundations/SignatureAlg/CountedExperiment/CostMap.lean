/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import VCVio.CryptoFoundations.SignatureAlg.CountedExperiment
public import ToMathlib.Control.WriterT.Map

/-! # Homomorphic observations of counted signature experiments -/

public section

open OracleComp OracleSpec

universe idx

namespace SignatureAlg.SigningView

variable {ι : Type idx} {spec : OracleSpec ι}
variable {Request PK SK Sig Reply C D : Type} [AddMonoid C] [AddMonoid D]

private theorem costed_mapCost (f : C →+ D) (policy : Event spec Request → C)
    (phase : Phase) {α : Type} (body : OracleComp spec α) :
    AddWriterT.mapCostHom f (costed policy phase body) =
      costed (fun event => f (policy event)) phase body := by
  unfold costed
  calc
    _ = simulateQ (fun input => AddWriterT.mapCostHom f
      (((QueryImpl.id' spec).withAddCost (fun input => policy (.ambient phase input))) input))
        body := PFunctor.FreeM.liftM_natural _ (AddWriterT.mapCostHom f) body
    _ = _ := by
      congr 1
      funext input
      apply WriterT.ext
      simp [QueryImpl.withAddCost_apply, AddWriterT.mapCostHom, WriterT.mapOutputHom,
        AddWriterT.addTell, Functor.map_map]

private theorem mapCost_addTell (f : C →+ D) (cost : C) :
    AddWriterT.mapCostHom f (AddWriterT.addTell cost : CostM spec C PUnit) =
      AddWriterT.addTell (f cost) := by
  apply WriterT.ext
  simp [AddWriterT.mapCostHom, WriterT.mapOutputHom, AddWriterT.addTell]

private def mapPhaseCost (f : C →+ D) :
    LoggedCostM spec Request Reply C →ᵐ LoggedCostM spec Request Reply D :=
  WriterT.mapBaseAppendHom (AddWriterT.mapCostHom f)

private theorem mapPhaseCost_lift (f : C →+ D) {α : Type} (body : CostM spec C α) :
    mapPhaseCost f (liftM body : LoggedCostM spec Request Reply C α) =
      (liftM (AddWriterT.mapCostHom f body) : LoggedCostM spec Request Reply D α) := by
  apply WriterT.ext
  simp [mapPhaseCost, MonadHom.mmap_map]

private theorem countedSigningOracle_mapCost (f : C →+ D) (policy : Event spec Request → C)
    (view : SignatureAlg.SigningView (OracleComp spec) Request PK SK Sig Reply)
    (pk : PK) (sk : SK) (request : Request) :
    mapPhaseCost f (countedSigningOracle policy view pk sk request) =
      countedSigningOracle (fun event => f (policy event)) view pk sk request := by
  apply WriterT.ext
  simp only [mapPhaseCost, WriterT.run_mapBaseAppendHom, countedSigningOracle_run,
    MonadHom.mmap_bind, MonadHom.mmap_pure, mapCost_addTell, costed_mapCost]

private theorem countedHandler_mapCost (f : C →+ D) (policy : Event spec Request → C)
    (view : SignatureAlg.SigningView (OracleComp spec) Request PK SK Sig Reply)
    (pk : PK) (sk : SK) (input : (spec + (Request →ₒ Reply)).Domain) :
    mapPhaseCost f (countedHandler policy view pk sk input) =
      countedHandler (fun event => f (policy event)) view pk sk input := by
  cases input with
  | inl input =>
    change mapPhaseCost f
      (liftM (((QueryImpl.id' spec).withAddCost
        (fun query => policy (.ambient .adversary query))) input)) =
      liftM (((QueryImpl.id' spec).withAddCost
        (fun query => f (policy (.ambient .adversary query)))) input)
    rw [mapPhaseCost_lift]
    congr 1
    apply WriterT.ext
    simp [QueryImpl.withAddCost_apply, AddWriterT.mapCostHom, WriterT.mapOutputHom,
      AddWriterT.addTell, Functor.map_map]
  | inr request => exact countedSigningOracle_mapCost f policy view pk sk request

private theorem countedPhase_mapCost (f : C →+ D) (policy : Event spec Request → C)
    (view : SignatureAlg.SigningView (OracleComp spec) Request PK SK Sig Reply)
    (pk : PK) (sk : SK) {α : Type} (body : OracleComp (spec + (Request →ₒ Reply)) α) :
    AddWriterT.mapCostHom f (countedPhase policy view pk sk body) =
      countedPhase (fun event => f (policy event)) view pk sk body := by
  have natural := PFunctor.FreeM.liftM_natural (countedHandler policy view pk sk)
    (mapPhaseCost f) body
  have handlers : (fun input => mapPhaseCost f (countedHandler policy view pk sk input)) =
      countedHandler (fun event => f (policy event)) view pk sk :=
    funext (countedHandler_mapCost f policy view pk sk)
  rw [handlers] at natural
  exact congrArg WriterT.run natural

/-- An additive observation maps accumulated costs and retains the complete experiment. -/
theorem countedExperiment_mapCost (f : C →+ D) (policy : Event spec Request → C)
    (view : SignatureAlg.SigningView (OracleComp spec) Request PK SK Sig Reply)
    (adv : PK → OracleComp (spec + (Request →ₒ Reply)) (Request × Sig)) :
    (fun observed => ({ toOutcome := observed.toOutcome, cost := f observed.cost } :
      Observation Request Sig Reply D)) <$> countedExperiment policy view adv =
        countedExperiment (fun event => f (policy event)) view adv := by
  let body : CostM spec C (Outcome Request Sig Reply) := do
    let (pk, sk) ← costed policy .keygen view.keygen
    let (forgery, rawLog) ← countedPhase policy view pk sk (adv pk)
    let verified ← costed policy .verification (view.verify pk forgery.1 forgery.2)
    return ⟨forgery, rawLog, verified⟩
  have equality : AddWriterT.mapCostHom f body = (do
    let (pk, sk) ← costed (fun event => f (policy event)) .keygen view.keygen
    let (forgery, rawLog) ← countedPhase (fun event => f (policy event)) view pk sk (adv pk)
    let verified ← costed (fun event => f (policy event)) .verification
      (view.verify pk forgery.1 forgery.2)
    return (⟨forgery, rawLog, verified⟩ : Outcome Request Sig Reply)) := by
      simp only [body, MonadHom.mmap_bind, MonadHom.mmap_pure, costed_mapCost,
        countedPhase_mapCost]
  have mapped := congrArg (fun program : CostM spec D (Outcome Request Sig Reply) =>
    (fun result => ({ toOutcome := result.1, cost := result.2 } :
      Observation Request Sig Reply D)) <$> program.runAdd) equality
  simpa only [body, countedExperiment, countedAfterKeygen, AddWriterT.runAdd_mapCostHom,
    Functor.map_map, Prod.map, id_eq] using mapped

end SignatureAlg.SigningView
