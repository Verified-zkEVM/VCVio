/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Examples.Schnorr.BoundedChallenges
public import Mathlib.Algebra.Field.ZMod

/-!
# Challenge restriction boundary checks

The algebraic fixture uses three challenges in the field of order seven. The lossy-map
counterexample separates completeness from special soundness. Empty and oversized domains
check the boundary of the bounded-challenge embedding; no security claim is made for this field.
-/

public section

open OracleComp OracleSpec

namespace SigmaChallengeRestrictionTest

/-- An unsatisfiable relation with a verifier that accepts its only original challenge. -/
@[expose]
def vacuousSigma : SigmaProtocol Unit Unit Unit Unit Unit Unit (fun _ _ => false) where
  commit _ _ := pure ((), ())
  respond _ _ _ _ := pure ()
  verify _ _ _ _ := true
  sim _ := pure ()
  extract _ _ _ _ := pure ()

theorem singleton_specially_sound : vacuousSigma.SpeciallySound := by
  intro x pc c₁ c₂ p₁ p₂ hne
  exact False.elim (hne (Subsingleton.elim _ _))

theorem collapsed_challenges_not_sound :
    ¬ (vacuousSigma.restrictChallenges (fun _ : Bool => ())).SpeciallySound := by
  intro h
  have hbad := h () () false true () () (by decide) rfl rfl () (by simp [vacuousSigma,
    SigmaProtocol.restrictChallenges])
  exact Bool.false_ne_true hbad

instance : Fact (Nat.Prime 7) := ⟨by decide⟩

example : vacuousSigma.toChallengeVerifyProtocol.restrictChallenges id =
    vacuousSigma.toChallengeVerifyProtocol := by
  simp

example :
    (vacuousSigma.toChallengeVerifyProtocol.restrictChallenges
      (fun _ : Bool => ())).restrictChallenges (fun _ : Fin 2 => false) =
    vacuousSigma.toChallengeVerifyProtocol.restrictChallenges
      ((fun _ : Bool => ()) ∘ fun _ : Fin 2 => false) := by
  simp

example : vacuousSigma.restrictChallenges id = vacuousSigma := by
  simp

example :
    Schnorr.restrictedSigma (ZMod 7) (ZMod 7) 1 id = Schnorr.sigma (ZMod 7) (ZMod 7) 1 := by
  simp

example : Schnorr.restrictedSimTranscript (ZMod 7) (ZMod 7) 1 id 3 =
    Schnorr.simTranscript (ZMod 7) (ZMod 7) 1 3 := by
  simp

example : Function.Injective (Schnorr.boundedChallenge 7 3) :=
  Schnorr.boundedChallenge_injective 7 3 (by decide)

example : Function.Injective (Schnorr.boundedChallenge 7 7) :=
  Schnorr.boundedChallenge_injective 7 7 le_rfl

example : Function.Injective (Schnorr.boundedChallenge 0 0) :=
  Schnorr.boundedChallenge_injective 0 0 le_rfl

example : ¬ Function.Injective (Schnorr.boundedChallenge 7 8) := by
  intro h
  have heq := h (a₁ := (0 : Fin 8)) (a₂ := (7 : Fin 8)) (by decide)
  exact (by decide : (0 : Fin 8) ≠ 7) heq

example :
    (Schnorr.restrictedSigma (ZMod 7) (ZMod 7) 1
      (Schnorr.boundedChallenge 7 3)).PerfectlyComplete :=
  Schnorr.restrictedSigma_complete _ _ _ _

example :
    (Schnorr.restrictedSigma (ZMod 7) (ZMod 7) 1
      (Schnorr.boundedChallenge 7 3)).SpeciallySound :=
  Schnorr.restrictedSigma_speciallySound _ _ _ _
    (Schnorr.boundedChallenge_injective 7 3 (by decide))

example :
    (Schnorr.restrictedSigma (ZMod 7) (ZMod 7) 1
      (Schnorr.boundedChallenge 7 3)).UniqueResponses := by
  apply Schnorr.restrictedSigma_uniqueResponses
  intro x y h
  simpa using h

example :
    ((Schnorr.sigma (ZMod 7) (ZMod 7) 1).restrictChallenges
      (Schnorr.boundedChallenge 7 3)).restrictChallenges (fun _ : Unit => (1 : Fin 3)) =
    (Schnorr.sigma (ZMod 7) (ZMod 7) 1).restrictChallenges
      (Schnorr.boundedChallenge 7 3 ∘ fun _ : Unit => (1 : Fin 3)) := by
  simp

/-- Simulation uses the actual restricted challenge distribution, even for a constant map. -/
example :
    letI : MeasurableSpace (ZMod 7) := ⊤
    letI : DiscreteMeasurableSpace (ZMod 7) := ⟨fun _ => trivial⟩
    𝒟[(Schnorr.restrictedSigma (ZMod 7) (ZMod 7) 1
      (fun _ : Bool => (2 : ZMod 7))).realTranscript 3 3] =
    𝒟[Schnorr.restrictedSimTranscript (ZMod 7) (ZMod 7) 1
      (fun _ : Bool => (2 : ZMod 7)) 3] := by
  exact Schnorr.restrictedSigma_hvzk_measure _ _ _ _ _ _ (by decide)

end SigmaChallengeRestrictionTest
