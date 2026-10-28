/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.Schemes.BLS.Generic.ReductionTranslation
public import VCVio.Schemes.BLS.Generic.ReductionInitialization
import all VCVio.Schemes.BLS.Generic.Adversary
import all VCVio.Schemes.BLS.AGM.Adversary
import all VCVio.Schemes.BLS.Generic.ReductionPrograms

/-! # Scalar extraction from the common BLS execution view

Chronological replay and the final target lookup depend only on the target message, coefficient
list, and transcript. They use the same private scalar oracle as the preceding execution.
-/

public section

open OracleComp OracleSpec GroupModel GroupModel.Interaction

namespace BLS.Generic

variable {F M R T : Type} {G : Bool → Type}

attribute [local implicit_reducible] spec PFam

/-- Replay chronological representations and evaluate the adversary's final coefficients. -/
@[expose] def scalarExtract [CommSemiring F]
    (hashRep signRep : R → F × F) (initial : List (F × F))
    (view : M × List F × LinearFunctional.Transcript M) :
    OracleComp (unifSpec + (M →ₒ R)) (F × F × R) := do
  let basis ← LinearFunctional.readTranscript hashRep signRep view.2.2
  let target ← (unifSpec + (M →ₒ R)).query (.inr view.1)
  let repr := evaluate view.2.1 (initial ++ basis)
  return (repr.1, repr.2, target)

/-- Real interpretation of the generic extractor is determined by the common execution view. -/
theorem run'_reductionExtract [CommSemiring F] [DecidableEq F]
    [∀ b, AddCommMonoid (G b)] [∀ b, Module F (G b)] [∀ b, DecidableEq (G b)]
    [AddCommMonoid T] [Module F T] [DecidableEq T]
    [∀ s, DecidableEq (PFam (G false) (G true) T s)]
    (e : G false →ₗ[F] G true →ₗ[F] T) (A : Adversary F M)
    (z : PSort → Handle) (pk₁ pk₂ : Handle)
    (hash sign : R → OracleComp (genSpec F pairingSig) Handle)
    (hashValue signValue : R → G false)
    (hashRep signRep : R → F × F) (initial : List (F × F))
    (root tbl : Tbl (PFam (G false) (G true) T))
    (real : RealReductionState F M G T)
    (hhash : RealizesPoint e root hash hashValue) (hsign : RealizesPoint e root sign signValue)
    (h : ReductionRelated root z (initialReductionState pk₁ pk₂) tbl real) :
    (simulateQ (openImpl (pairingReal e) (fun _ => id))
      (reductionExtract A z pk₁ pk₂ hash sign hashRep signRep initial)).run' tbl =
    ((fun a => realReductionView a.1 a.2) <$>
      (simulateQ (realReductionHandler e hashValue signValue) (A reductionInput)).run real) >>=
        scalarExtract hashRep signRep initial := by
  have hv := congrArg (fun p => p >>= scalarExtract hashRep signRep initial)
    (run_reductionHandler_view e z hash sign hashValue signValue root hhash hsign
      (A reductionInput) (initialReductionState pk₁ pk₂) tbl real h)
  rw [← hv]
  simp only [reductionExtract, scalarExtract, reductionView, StateT.run'_eq,
    simulateQ_bind, StateT.run_bind,
    bind_map_left, map_bind, openImpl_scalar, bind_pure_comp]
  apply bind_congr
  intro a
  simp only [openImpl]
  rfl

/-- The algebraic extraction program uses exactly the real generic execution's coefficients. -/
theorem extractionProgram_toAlgebraic {G₁ G₂ Gₜ : Type} [Field F]
    [AddCommGroup G₁] [Module F G₁] [DecidableEq G₁]
    [AddCommGroup G₂] [Module F G₂] [DecidableEq G₂]
    [AddCommGroup Gₜ] [Module F Gₜ] [DecidableEq Gₜ]
    (e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ) (A : Adversary F M) (hA : FollowsProtocol A)
    (g₁ : G₁) (g₂ : G₂) (pk : G₁ × G₂) (hash sign : R → G₁)
    (hashRep signRep : R → F × F) (initial : List (F × F)) :
    (fun a =>
      let repr := evaluate
        (if (a.1.value.groups false).isEmpty then [] else (a.1.coefficients false).headD []) a.2.1
      (repr.1, repr.2, a.2.2)) <$>
      LinearFunctional.extractionProgram (fun out => out.value.data)
        hash sign hashRep signRep initial
        (simulateQ (fun q => AGM.oracle q.value)
          ((A.toAlgebraic hA e g₁ g₂).main (AGM.initialInput g₁ g₂ pk))) =
    ((fun a => realReductionView a.1 a.2) <$>
      (simulateQ (realReductionHandler (G := AGM.Group G₁ G₂) e hash sign)
        (A reductionInput)).run (initialRealReductionState
          (fun | false => g₁ | true => g₂) (fun | false => pk.1 | true => pk.2))) >>=
      scalarExtract hashRep signRep initial := by
  have hv := congrArg (fun p => p >>= scalarExtract hashRep signRep initial)
    (explainProgram_transcript_view e hash sign (A reductionInput)
      (initialRealReductionState (F := F) (M := M)
        (fun | false => g₁ | true => g₂) (fun | false => pk.1 | true => pk.2)).1 [])
  simp only [bind_map_left, scalarExtract] at hv
  simp only [LinearFunctional.extractionProgram, map_bind, map_pure]
  convert hv using 1
  · congr 2
    have hgroups : AGM.groupInputs [g₁, pk.1] [g₂, pk.2] =
        fun b => [(match b with | false => g₁ | true => g₂),
          (match b with | false => pk.1 | true => pk.2)] := by
      funext b
      cases b <;> rfl
    simp only [Adversary.toAlgebraic, Pairing.toExplained, AGM.initialInput,
      initialRealReductionState, reductionInput, hgroups]
    rfl
  · simp only [bind_map_left, scalarExtract]
    rfl

end BLS.Generic
