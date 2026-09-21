/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Examples.Schnorr.Transforms
public import Examples.Schnorr.Signature
public import Examples.Schnorr.BoundedChallenges
public import Mathlib.Algebra.Field.ZMod
public import VCVio.CryptoFoundations.Fischlin.ExtractionCost

/-!
# Bounded Schnorr consumers of Fiat–Shamir and Fischlin guarantees

A three-challenge protocol over the field of order seven exercises both concrete extractors
and their query guarantees. The small field supplies algebraic regression cases.
-/

public section

open OracleComp OracleSpec MeasureTheory
open scoped ENNReal

namespace SchnorrTransformsTest

instance : Fact (Nat.Prime 7) := ⟨by decide⟩

/-- Sample the small field directly as `Fin 7`, without constructing a global enumeration. -/
local instance sampleField : SampleableType (ZMod 7) :=
  inferInstanceAs (SampleableType (Fin 7))

/-- Identity challenges recover the original full-field Fiat–Shamir signature algorithm. -/
theorem identity_signature :
    FiatShamir (m := OracleComp (unifSpec + (Unit × ZMod 7 →ₒ ZMod 7)))
      (Schnorr.restrictedSigma (ZMod 7) (ZMod 7) 1 id)
      (DiffieHellman.dlogGenerable (F := ZMod 7) 1) Unit =
        Schnorr.signature (ZMod 7) (ZMod 7) 1 Unit := rfl

/-- Bounded integer challenges are distinct as scalars in this small test field. -/
theorem toy_embedding : Function.Injective (Schnorr.boundedChallenge 7 3) :=
  Schnorr.boundedChallenge_injective 7 3 (by decide)

/-- Small-field Schnorr fixture with three encoded challenges. -/
@[expose]
def toySigma := Schnorr.restrictedSigma (ZMod 7) (ZMod 7) 1
  (Schnorr.boundedChallenge 7 3)

/-- An accepting transcript with challenge one. -/
@[expose]
def toyProof : FischlinProof (ZMod 7) (Fin 3) (ZMod 7) 1 :=
  fun _ => (2, 1, 5)

/-- Another accepting transcript with the same commitment and challenge two. -/
@[expose]
def toyInput : FischlinROInput (ZMod 7) (ZMod 7) (Fin 3) (ZMod 7) 1 Unit :=
  ⟨3, (), [2], 0, 2, 1⟩

/-- The concrete sigma extractor recovers the scalar from two accepting transcripts. -/
theorem toy_extract : toySigma.extract 1 5 2 1 = pure 3 := by
  change pure ((5 - 1) * (1 - 2)⁻¹ : ZMod 7) = pure 3
  apply congrArg pure
  calc
    _ = (-4 : ZMod 7) := by
      rw [show (1 - 2 : ZMod 7) = -1 by ring, inv_neg, inv_one]
      ring
    _ = 3 := by decide

/-- The named online extractor returns the expected witness from an actual accepting log pair. -/
theorem toy_online_extract :
    Fischlin.onlineExtract toySigma 1 1 Unit 3 toyProof [⟨toyInput, 0⟩] = pure (some 3) := by
  have hv : toySigma.verify 3 2 2 1 = true := by decide
  have hne : (2 : Fin 3) ≠ 1 := by decide
  simp [Fischlin.onlineExtract, toyProof, toyInput, List.finRange_succ, List.ofFn_succ,
    hv, toy_extract, hne]

/-- An empty preverification log supplies no witness, even if a later verifier accepts. -/
theorem empty_log_no_witness :
    Fischlin.onlineExtract toySigma 1 1 Unit 3 toyProof [] = pure none := by
  simp [Fischlin.onlineExtract, List.finRange_succ]

/-- A proof submitted without querying the Fiat–Shamir oracle. -/
@[expose]
def prover : FiatShamir.KnowledgeProver (Stmt := ZMod 7) (Commit := ZMod 7)
    (Chal := Fin 3) (Resp := ZMod 7) Unit := fun _ _ => pure (0, 0)

example (Q : ℕ) :
    let a := FiatShamir.knowledgeAcceptance toySigma
      (DiffieHellman.dlogGenerable (F := ZMod 7) 1) Unit prover 3 ()
    a * (a / (Q + 1 : ENNReal) - FiatShamir.challengeSpaceInv (Fin 3)) ≤
      Pr{
        let w ← Schnorr.fsExtractor (ZMod 7) (ZMod 7) 1 (Schnorr.boundedChallenge 7 3)
          Unit prover () Q 3
      }[w • (1 : ZMod 7) = 3] := by
  simpa only [toySigma, smul_eq_mul] using Schnorr.fs_extraction (ZMod 7) (ZMod 7) 1
    (Schnorr.boundedChallenge 7 3) Unit toy_embedding prover 3 () Q (by trivial)

example : IsQueryBoundP
    (FiatShamir.nmaForkExtract toySigma (DiffieHellman.dlogGenerable (F := ZMod 7) 1) Unit
      (FiatShamir.proverWithFinalQuery toySigma (DiffieHellman.dlogGenerable (F := ZMod 7) 1)
        Unit prover ()) 0 3) (· = .inr ()) 2 :=
  Schnorr.fs_extractor_challenge_queries (ZMod 7) (ZMod 7) 1
    (Schnorr.boundedChallenge 7 3) Unit prover 3 () 0 (by trivial)

example (ρ b S : ℕ) :
    ∫⁻ q, (q : ENNReal) ∂𝒟[Fischlin.signingQueryCount toySigma ρ b Unit
      (DiffieHellman.dlogGenerable (F := ZMod 7) 1) S 3 3 ()] =
      ρ * (2 ^ b : ENNReal) * (1 - (1 - (2 ^ b : ENNReal)⁻¹) ^ 3) := by
  simpa only [toySigma, show FinEnum.card (Fin 3) = 3 from rfl] using
    Schnorr.fischlin_expected_sign_queries (ZMod 7) (ZMod 7) 1
      (Schnorr.boundedChallenge 7 3) Unit ρ b S 3 3 ()

example (ρ b S Q : ℕ) (hρ : 0 < ρ)
    (adv : Fischlin.KnowledgeSoundnessAdv (Stmt := ZMod 7) (Commit := ZMod 7)
      (Chal := Fin 3) (Resp := ZMod 7) ρ b Unit)
    (hQ : ∀ pk msg, Fischlin.ROQueryBound ρ b Unit (adv.run pk msg) Q) :
    Pr{
      let z ← Fischlin.knowledgeRun toySigma
        (DiffieHellman.dlogGenerable (F := ZMod 7) 1) ρ b S Unit adv 3 ()
    }[z.1 = true] -
        Fischlin.knowledgeSoundnessError Q ρ b S ≤
      Pr{
        let z ← Fischlin.knowledgeRun toySigma
          (DiffieHellman.dlogGenerable (F := ZMod 7) 1) ρ b S Unit adv 3 ()
      }[z.2.any (fun w => decide (w • (1 : ZMod 7) = 3)) = true] := by
  have hg : Function.Injective (fun z : ZMod 7 => z • (1 : ZMod 7)) := by
    intro x y h
    simpa only [smul_eq_mul, mul_one] using h
  exact Schnorr.fischlin_extraction (ZMod 7) (ZMod 7) 1 (Schnorr.boundedChallenge 7 3)
    Unit toy_embedding hg ρ b S adv Q hρ hQ 3 ()

example (ρ b S : ℕ) (hρ : 0 < ρ) :
    let scheme := Fischlin (m := OracleComp (unifSpec +
      fischlinROSpec (ZMod 7) (ZMod 7) (Fin 3) (ZMod 7) ρ b Unit)) toySigma
      (DiffieHellman.dlogGenerable (F := ZMod 7) 1) ρ b S Unit
    (1 : ENNReal) - Fischlin.completenessError ρ b S 3 ≤
      (Fischlin.runtime ρ b Unit).evalDist (do
        let (pk, sk) ← scheme.keygen
        let sig ← scheme.sign pk sk ()
        scheme.verify pk () sig) {true} := by
  simpa only [toySigma, show FinEnum.card (Fin 3) = 3 from rfl] using
    Schnorr.fischlin_complete (ZMod 7) (ZMod 7) 1 (Schnorr.boundedChallenge 7 3)
      Unit ρ b S hρ ()

example : Fischlin.onlineExtractWithScanCount toySigma 1 1 Unit 3 toyProof
    [⟨toyInput, 0⟩] = pure (some 3, 1) := by
  rw [Fischlin.onlineExtractWithScanCount_cons_of_match toySigma 1 Unit 3 toyProof
    ⟨toyInput, 0⟩ [] rfl (by decide) (by decide) (by decide)]
  simp only [toyProof, toyInput, toy_extract, map_pure]

end SchnorrTransformsTest
