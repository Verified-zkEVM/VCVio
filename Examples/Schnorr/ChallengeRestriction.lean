/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/

module

public import Examples.Schnorr.SigmaProtocol
public import VCVio.CryptoFoundations.SigmaProtocol.ChallengeRestriction

/-!
# Schnorr with a chosen finite challenge space

Both transforms consume the same commitment, response algebra, and witness extractor.
An injective map into the scalar field supplies the special-soundness guarantee needed for
extraction. Simulation is proved for the actual new challenge distribution by a bijective
change of the uniformly sampled response, rather than assumed to follow from restriction.
-/

public section

open OracleComp OracleSpec MeasureTheory ProbabilityTheory

namespace Schnorr

variable (F : Type) [Field F] [SampleableType F]
variable (G : Type) [AddCommGroup G] [Module F G] [SampleableType G] [DecidableEq G]
variable {C : Type}

/-- Schnorr's original algorithms, with challenges encoded in the scalar field. -/
@[expose]
def restrictedSigma (g : G) (encode : C → F) :
    SigmaProtocol G F G F C F (fun pk sk => decide (sk • g = pk)) :=
  (sigma F G g).restrictChallenges encode

@[simp] theorem restrictedSigma_id (g : G) :
    restrictedSigma F G g id = sigma F G g := rfl

/-- Honest Schnorr responses verify for every challenge policy. -/
theorem restrictedSigma_complete [SampleableType C] (g : G) (encode : C → F) :
    (restrictedSigma F G g encode).PerfectlyComplete :=
  (sigma_complete F G g).restrictChallenges encode

/-- Distinct encoded challenges let the original Schnorr extractor recover a discrete log. -/
theorem restrictedSigma_speciallySound (g : G) (encode : C → F)
    (hinj : Function.Injective encode) :
    (restrictedSigma F G g encode).SpeciallySound :=
  (sigma_speciallySound F G g).restrictChallenges encode hinj

/-- Schnorr has unique responses when scalar multiplication by the generator is injective. -/
theorem restrictedSigma_uniqueResponses (g : G) (encode : C → F)
    (hg : Function.Injective (fun z : F => z • g)) :
    (restrictedSigma F G g encode).UniqueResponses := by
  intro pk pc c z₁ z₂ hv₁ hv₂
  apply hg
  exact (of_decide_eq_true hv₁).trans (of_decide_eq_true hv₂).symm

/-- Simulate a transcript using a challenge in `C` and a uniform scalar response. -/
@[expose]
def restrictedSimTranscript [SampleableType C]
    (g : G) (encode : C → F) (pk : G) : ProbComp (G × C × F) := do
  let c ← $ᵗ C
  let z ← $ᵗ F
  return (z • g - encode c • pk, c, z)

omit [SampleableType G] [DecidableEq G] in
@[simp] theorem restrictedSimTranscript_id (g : G) (pk : G) :
    restrictedSimTranscript F G g id pk = simTranscript F G g pk := rfl

private theorem evalDist_uniformPair_map
    {A B T : Type} [SampleableType A] [SampleableType B]
    [MeasurableSpace A] [DiscreteMeasurableSpace A]
    [MeasurableSpace B] [DiscreteMeasurableSpace B] [MeasurableSpace T]
    (f : A → B → T) :
    𝒟[do let a ← $ᵗ A; let b ← $ᵗ B; pure (f a b)] =
      (uniformOn (Set.univ : Set (A × B))).map (fun ab => f ab.1 ab.2) := by
  have heq : (do let a ← $ᵗ A; let b ← $ᵗ B; pure (f a b)) =
      (fun ab : A × B => f ab.1 ab.2) <$>
        (do let a ← $ᵗ A; let b ← $ᵗ B; pure (a, b)) := by
    simp [map_bind, monad_norm]
  rw [heq, evalDist_map_of_discrete, evalDist_pair,
    SampleableType.evalDist_uniformSample, SampleableType.evalDist_uniformSample,
    ← uniformOn_univ_prod]

/-- The restricted Schnorr simulator has exactly the honest transcript measure on valid keys.
The challenge map need not be injective for this simulation fact. -/
theorem restrictedSigma_hvzk_measure [SampleableType C]
    [MeasurableSpace F] [DiscreteMeasurableSpace F]
    [MeasurableSpace C] [DiscreteMeasurableSpace C] [MeasurableSpace G]
    (g : G) (encode : C → F) (pk : G) (sk : F) (hkey : sk • g = pk) :
    𝒟[(restrictedSigma F G g encode).realTranscript pk sk] =
      𝒟[restrictedSimTranscript F G g encode pk] := by
  let changeVars : F × C → C × F := fun rc => (rc.2, rc.1 + encode rc.2 * sk)
  have hbij : Function.Bijective changeVars := by
    constructor
    · rintro ⟨r, c⟩ ⟨r', c'⟩ h
      have hc : c = c' := congrArg Prod.fst h
      subst c'
      have hr := congrArg Prod.snd h
      exact Prod.ext (add_right_cancel hr) rfl
    · rintro ⟨c, z⟩
      exact ⟨(z - encode c * sk, c), by simp [changeVars]⟩
  have hmap := map_uniformOn_univ_of_bijective
    (Measurable.of_discrete : Measurable changeVars) hbij
  simp only [ChallengeVerifyProtocol.realTranscript, restrictedSigma,
    SigmaProtocol.restrictChallenges, ChallengeVerifyProtocol.restrictChallenges,
    sigma, restrictedSimTranscript, monad_norm]
  rw [evalDist_uniformPair_map, evalDist_uniformPair_map, ← hmap,
    Measure.map_map Measurable.of_discrete Measurable.of_discrete]
  congr 1
  funext rc
  simp [changeVars, add_smul, mul_smul, hkey]

end Schnorr
