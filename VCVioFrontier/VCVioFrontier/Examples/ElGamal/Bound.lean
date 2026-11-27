/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
-- frontier: CslibFrontier.Crypto.Computational.ElGamal.ProbComp

public import VCVioFrontier.Examples.ElGamal.Honest
public import VCVioFrontier.Examples.ElGamal.Security
import CslibFrontier.Crypto.Negligible.Dyadic

/-!
# One-time ElGamal for bounded fair-coin algorithms

For any two-stage word adversary implementing a family of typed adversaries, the distinguishing
advantage of the implemented scheme is at most twice the advantage of its own uniform DDH
distinguisher plus the finite-coin exponent sampling error.
-/

public section

namespace VCVioFrontier.ElGamal

open Turing.MultiTapeTM Cslib.Crypto MeasureTheory OracleComp
open scoped ENNReal NNReal

variable {F : PrimeOrderGroupFamily} {desc : ℕ → F.Desc} {adv : TypedAdversary F desc}

/-- The unguarded VCVio one-time game with its challenge bit fixed, before scoring the guess. -/
@[expose] noncomputable def typedBranch (adv : TypedAdversary F desc) (b : Bool) (n : ℕ) :
    _root_.ProbComp Bool :=
  AsymmEncAlg.IND_CPA_OneTime_branch (adv n) b

/-- The realized word adversary produces the same fixed-bit guess in the exact-exponent ideal
game, including its complete saved state. All its messages here came from group elements. -/
theorem AdversaryRealization.typedBranch_eval (R : AdversaryRealization F desc adv)
    (b : Bool) (n : ℕ) :
    Cslib.ProbComp.eval (typedBranch adv b n) =
      F.elGamalGroupCPAGameOn (fun _ _ _ _ => true) (fun k => PMF.pure (desc k)) R.words b n := by
  simp only [typedBranch, AsymmEncAlg.IND_CPA_OneTime_branch, typedScheme, elGamalAsymmEnc,
    Cslib.ProbComp.eval_bind, Cslib.ProbComp.eval_pure, eval_uniformSample,
    PrimeOrderGroupFamily.elGamalGroupCPAGameOn, PrimeOrderGroupFamily.elGamalMsgCPAGameOn,
    PrimeOrderGroupFamily.elGamalMsgCPAGameWith, Cslib.Probability.PMF.monad_bind_eq_bind,
    PMF.bind_bind, PMF.pure_bind, ite_true,
    Encryption.ChoiceOut.msg₀, Encryption.ChoiceOut.msg₁, Encryption.ChoiceOut.msgs]
  apply congrArg (PMF.bind _)
  funext sk
  rw [R.choose]
  simp only [PMF.bind_map]
  apply congrArg (PMF.bind _)
  funext choice
  apply congrArg (PMF.bind _)
  funext r
  cases b <;>
    simp only [encodeChoice, Bool.false_eq_true, ↓reduceIte, F.add_encode, R.guess, ← mul_smul,
      mul_comm, add_comm]

private theorem typedBranch_advantage (adv : TypedAdversary F desc) (n : ℕ) :
    (𝒟[typedBranch adv false n]).boolDist (𝒟[typedBranch adv true n]) =
      (typedScheme F (desc n)).IND_CPA_OneTime_Advantage ProbCompRuntime.probComp (adv n) :=
  (AsymmEncAlg.IND_CPA_OneTime_Advantage_eq_boolDist (adv n)).symm

private theorem perturbedRows (actual ideal : Bool → Measure Bool) (ε : ℝ≥0∞)
    (step : ∀ b, (actual b).boolDist (ideal b) ≤ ε) :
    (actual false).boolDist (actual true) ≤ (ideal false).boolDist (ideal true) + (ε + ε) := by
  calc
    _ ≤ (actual false).boolDist (ideal false) + (ideal false).boolDist (actual true) :=
      Measure.boolDist_triangle _ _ _
    _ ≤ ε + ((ideal false).boolDist (ideal true) + (ideal true).boolDist (actual true)) :=
      add_le_add (step false) (Measure.boolDist_triangle _ _ _)
    _ ≤ ε + ((ideal false).boolDist (ideal true) + ε) :=
      add_le_add le_rfl (add_le_add le_rfl ((Measure.boolDist_comm _ _).trans_le (step true)))
    _ = _ := by ac_rfl

/-- Under both fixed challenge bits use the bounded fair-coin encryption scheme, its original
realized adversary, and the strict machine implementing that adversary's own DDH reduction. -/
theorem AdversaryRealization.wordGame_advantage_le (R : AdversaryRealization F desc adv) (n : ℕ) :
    (𝒟[wordGame F desc (fun _ _ _ _ => true) R.words false n]).boolDist
        (𝒟[wordGame F desc (fun _ _ _ _ => true) R.words true n]) ≤
      2 * (Game.advantage (F.ddhRealGame (fun k => PMF.pure (desc k)) (ddhReduction F R.words) n)
        (F.ddhRandomGame (fun k => PMF.pure (desc k)) (ddhReduction F R.words) n) : ℝ≥0∞) +
        ((4 / 2 ^ n : ℝ≥0) : ℝ≥0∞) := by
  let actual (b : Bool) := 𝒟[wordGame F desc (fun _ _ _ _ => true) R.words b n]
  let ideal (b : Bool) := 𝒟[typedBranch adv b n]
  have step (b : Bool) : (actual b).boolDist (ideal b) ≤ ((2 / 2 ^ n : ℝ≥0) : ℝ≥0∞) := by
    unfold actual ideal
    rw [evalDist_eq_toMeasure (typedBranch adv b n), R.typedBranch_eval]
    exact wordGame_measure_approximation F desc _ _ b n
  have delta : ((2 / 2 ^ n : ℝ≥0) : ℝ≥0∞) + ((2 / 2 ^ n : ℝ≥0) : ℝ≥0∞) =
      ((4 / 2 ^ n : ℝ≥0) : ℝ≥0∞) := by
    rw [← ENNReal.coe_add, ← add_div]
    norm_num
  have h := perturbedRows actual ideal _ step
  simpa only [actual, ideal, typedBranch_advantage, R.advantage_eq, delta] using h

/-- The implemented word games of every realized adversary are computationally indistinguishable
under the strict uniform machine DDH assumption. -/
theorem AdversaryRealization.wordGame_secure (R : AdversaryRealization F desc adv)
    (hDDH : F.DDH (fun k => PMF.pure (desc k))) :
    negligible fun n =>
      (𝒟[wordGame F desc (fun _ _ _ _ => true) R.words false n]).boolDist
        (𝒟[wordGame F desc (fun _ _ _ _ => true) R.words true n]) := by
  apply negligible_of_le (fun n => R.wordGame_advantage_le n)
  apply negligible_add
  · simpa only [R.advantage_eq] using R.negligible_advantage hDDH
  · exact (negligible_coe_iff _).2 (negligible_const_div_two_pow 4)

/-- The two word procedures run against VCVio's implemented scheme. Message ordering follows
VCVio's convention that the hidden bit selects the first message when true. -/
@[expose] def implementedAdversary (F : PrimeOrderGroupFamily) (desc : ℕ → F.Desc)
    (A : Encryption.WordAdversary) (n : ℕ) :
    (wordScheme F desc n).IND_CPA_OneTime_Adversary where
  State := List Bool
  chooseMessages pk := oneTimeChoice id <$> A.choose n pk
  distinguish := A.guess n

/-- VCVio's hidden-bit advantage of the two word procedures equals the distinguishing
advantage of the implemented fixed-bit experiments. -/
theorem implementedAdversary_advantage (A : Encryption.WordAdversary) (n : ℕ) :
    (wordScheme F desc n).IND_CPA_OneTime_Advantage ProbCompRuntime.probComp
        (implementedAdversary F desc A n) =
      (𝒟[wordGame F desc (fun _ _ _ _ => true) A false n]).boolDist
        (𝒟[wordGame F desc (fun _ _ _ _ => true) A true n]) := by
  rw [AsymmEncAlg.IND_CPA_OneTime_Advantage_eq_boolDist]
  simp [AsymmEncAlg.IND_CPA_OneTime_branch, implementedAdversary, oneTimeChoice, wordGame,
    Encryption.gameOn, Encryption.ChoiceOut.msg₀, Encryption.ChoiceOut.msg₁,
    Encryption.ChoiceOut.msgs, monad_norm]

/-- A concrete bound in the original VCVio one-time experiment for the implemented scheme and
the realized adversary's own DDH reduction. -/
theorem AdversaryRealization.implemented_advantage_le (R : AdversaryRealization F desc adv)
    (n : ℕ) :
    (wordScheme F desc n).IND_CPA_OneTime_Advantage ProbCompRuntime.probComp
        (implementedAdversary F desc R.words n) ≤
      2 * (Game.advantage (F.ddhRealGame (fun k => PMF.pure (desc k)) (ddhReduction F R.words) n)
        (F.ddhRandomGame (fun k => PMF.pure (desc k)) (ddhReduction F R.words) n) : ℝ≥0∞) +
        ((4 / 2 ^ n : ℝ≥0) : ℝ≥0∞) := by
  rw [implementedAdversary_advantage]
  exact R.wordGame_advantage_le n

/-- The implemented one-time scheme is secure against every uniform word adversary realizing
a typed two-stage group-message adversary, under the usual machine DDH assumption. -/
theorem implemented_secureAgainst (hDDH : F.DDH (fun n => PMF.pure (desc n))) :
    (SecurityGame.mk fun A : Encryption.WordAdversary => fun n =>
      (wordScheme F desc n).IND_CPA_OneTime_Advantage ProbCompRuntime.probComp
        (implementedAdversary F desc A n)).secureAgainst
      (fun A => ∃ (typed : TypedAdversary F desc) (R : AdversaryRealization F desc typed),
        R.words = A) := by
  rintro _ ⟨typed, R, rfl⟩
  simpa only [implementedAdversary_advantage] using R.wordGame_secure hDDH

end VCVioFrontier.ElGamal
