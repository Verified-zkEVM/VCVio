module

import Std
import SelectedWork

/-! # Importing audit for the reviewed joint-observer contract -/

public section

open OracleSpec OracleComp SignatureAlg.SigningView SignatureAlg.SigningView.Events

universe v

/-- The reviewed joint-observer target, with no added public assumptions. -/
def reviewedTarget : Prop :=
  ∀
    {ι Request PK SK Sig Reply Cache : Type} {spec : OracleSpec.{0, 0} ι}
    {m : Type → Type v} [Monad m] [LawfulMonad m]
    (policy : Event spec Request → Nat)
    (view : SignatureAlg.SigningView (OracleComp spec) Request PK SK Sig Reply)
    (adv : PK → OracleComp (spec + (Request →ₒ Reply)) (Request × Sig))
    (handler : QueryImpl spec (StateT Cache m)) (initial : Cache)
    (initialCost : Nat),
    (simulateQ
      ((handlerWithEvents (Request := Request) handler).extendState
        (fun input _ _ _ n => n + inputCost policy input))
      ((viewWithEvents view).experiment (mainWithEvents adv))).run (initial, initialCost) =
      (fun result =>
        (erase result.1, (result.2, initialCost + result.1.cost))) <$>
        (simulateQ handler (countedExperiment policy view adv)).run initial

/-- The imported theorem has exactly the reviewed universally quantified target. -/
theorem checkedTarget : reviewedTarget.{v} :=
  @SignatureAlg.SigningView.Events.selectedCost_run

#check @checkedTarget
#print axioms checkedTarget
#check @SignatureAlg.SigningView.Events.viewWithEvents
#check @SignatureAlg.SigningView.Events.mainWithEvents
#print axioms SignatureAlg.SigningView.Events.selectedCost_run
