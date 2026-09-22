/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Examples.Schnorr.ChallengeRestriction
public import VCVio.CryptoFoundations.HardnessAssumptions.DiffieHellman
public import VCVio.CryptoFoundations.FiatShamir.Sigma.KnowledgeExtraction
public import VCVio.CryptoFoundations.FiatShamir.Sigma.ExtractionCost
public import VCVio.CryptoFoundations.Fischlin.ExtractionGuarantee
public import VCVio.CryptoFoundations.Fischlin.ExpectedSigningCost

/-!
# Two extraction methods for one Schnorr protocol family

Fiat–Shamir replays a bounded prover. Fischlin scans the prover's existing oracle log,
requiring unique responses and adding an honest-prover search. Both theorems discharge
their algebraic hypotheses using the same challenge-restricted Schnorr definition.
The games fix their statement and context before execution and start with an empty oracle.
-/

public section

open OracleComp OracleSpec DiffieHellman
open scoped ENNReal

namespace Schnorr

variable (F : Type) [Field F] [SampleableType F]
variable (G : Type) [AddCommGroup G] [Module F G] [SampleableType G] [DecidableEq G]
variable {C : Type} [DecidableEq C]
variable (g : G) (encode : C → F) (M : Type) [DecidableEq M]

/-- Zero supplies the explicit default scalar for proof formatting. -/
local instance inhabitedScalar : Inhabited F := ⟨0⟩

section fiatShamir

variable [SampleableType C]

/-- Schnorr's named Fiat–Shamir witness finder with the selected challenge policy. -/
@[expose]
def fsExtractor
    (prover : FiatShamir.KnowledgeProver (Stmt := G) (Commit := G) (Chal := C) (Resp := F) M)
    (msg : M) (Q : ℕ) : G → ProbComp F :=
  FiatShamir.knowledgeExtractor (restrictedSigma F G g encode)
    (dlogGenerable (F := F) g) M prover msg Q

/-- Acceptance of a bounded Fiat–Shamir prover gives a quantitative discrete-log recovery bound
for the named replay extractor, using the cardinality of the actual challenge type `C`. -/
theorem fs_extraction [Inhabited C] [Fintype C] (hinj : Function.Injective encode)
    (prover : FiatShamir.KnowledgeProver (Stmt := G) (Commit := G) (Chal := C) (Resp := F) M)
    (pk : G) (msg : M) (Q : ℕ)
    (hQ : FiatShamir.nmaHashQueryBound (M := M) (oa := prover pk msg) Q) :
    let a := FiatShamir.knowledgeAcceptance (restrictedSigma F G g encode)
      (dlogGenerable (F := F) g) M prover pk msg
    a * (a / (Q + 1 : ℝ≥0∞) - FiatShamir.challengeSpaceInv C) ≤
      Pr{let w ← fsExtractor F G g encode M prover msg Q pk}[w • g = pk] := by
  simpa only [fsExtractor, decide_eq_true_eq] using
    FiatShamir.knowledgeExtractor_success (restrictedSigma F G g encode)
      (dlogGenerable (F := F) g) M
      (restrictedSigma_speciallySound F G g encode hinj) prover pk msg Q hQ

/-- The replay program of the same Schnorr witness finder has a pathwise challenge budget. -/
theorem fs_extractor_challenge_queries
    (prover : FiatShamir.KnowledgeProver (Stmt := G) (Commit := G) (Chal := C) (Resp := F) M)
    (pk : G) (msg : M) (Q : ℕ)
    (hQ : FiatShamir.nmaHashQueryBound (M := M) (oa := prover pk msg) Q) :
    IsQueryBoundP
      (FiatShamir.nmaForkExtract (restrictedSigma F G g encode) (dlogGenerable (F := F) g) M
        (FiatShamir.proverWithFinalQuery (restrictedSigma F G g encode)
          (dlogGenerable (F := F) g) M prover msg) Q pk)
      (· = .inr ()) (2 * (Q + 1)) :=
  FiatShamir.knowledgeExtractor_challenge_bound (restrictedSigma F G g encode)
    (dlogGenerable (F := F) g) M prover pk msg Q hQ

end fiatShamir

variable [DecidableEq F] [Inhabited C] [FinEnum C]

/-- Fischlin's actual online extractor recovers a discrete log except for the single-proof
knowledge error, with Schnorr special soundness and unique responses discharged. -/
theorem fischlin_extraction (hinj : Function.Injective encode)
    (hg : Function.Injective (fun z : F => z • g))
    (ρ b S : ℕ)
    (prover : Fischlin.KnowledgeSoundnessAdv (Stmt := G) (Commit := G)
      (Chal := C) (Resp := F) ρ b M)
    (Q : ℕ) (hρ : 0 < ρ)
    (hQ : ∀ pk msg, Fischlin.ROQueryBound ρ b M (prover.run pk msg) Q)
    (pk : G) (msg : M) :
    Pr{
      let z ← Fischlin.knowledgeRun (restrictedSigma F G g encode)
        (dlogGenerable (F := F) g) ρ b S M prover pk msg
    }[z.1 = true] -
        Fischlin.knowledgeSoundnessError Q ρ b S ≤
      Pr{
        let z ← Fischlin.knowledgeRun (restrictedSigma F G g encode)
          (dlogGenerable (F := F) g) ρ b S M prover pk msg
      }[z.2.any (fun w => decide (w • g = pk)) = true] :=
  Fischlin.extraction_success_ge_acceptance_sub_error (restrictedSigma F G g encode)
    (dlogGenerable (F := F) g) ρ b S M
    (restrictedSigma_speciallySound F G g encode hinj)
    (restrictedSigma_uniqueResponses F G g encode hg) prover Q hρ hQ pk msg

/-- The same restricted Schnorr protocol supplies the honest Fischlin completeness guarantee. -/
theorem fischlin_complete (ρ b S : ℕ) (hρ : 0 < ρ) (msg : M) :
    let scheme := Fischlin
      (m := OracleComp (unifSpec + fischlinROSpec G G C F ρ b M))
      (restrictedSigma F G g encode) (dlogGenerable (F := F) g) ρ b S M
    (1 : ℝ≥0∞) - Fischlin.completenessError ρ b S (FinEnum.card C) ≤
      (Fischlin.runtime ρ b M).evalDist (do
        let (pk, sk) ← scheme.keygen
        let sig ← scheme.sign pk sk msg
        scheme.verify pk msg sig) {true} :=
  Fischlin.almostComplete (restrictedSigma F G g encode)
    (dlogGenerable (F := F) g) ρ b S M hρ (restrictedSigma_complete F G g encode) msg

/-- Schnorr's actual Fischlin signer has the finite geometric expected hash cost. -/
theorem fischlin_expected_sign_queries (ρ b S : ℕ) (pk : G) (sk : F) (msg : M) :
    ∫⁻ (q : ℕ), (q : ℝ≥0∞) ∂𝒟[Fischlin.signingQueryCount
      (restrictedSigma F G g encode) ρ b M (dlogGenerable (F := F) g) S pk sk msg] =
      ρ * (2 ^ b : ℝ≥0∞) * (1 - (1 - (2 ^ b : ℝ≥0∞)⁻¹) ^ FinEnum.card C) :=
  Fischlin.sign_expectedQueries_eq_geometric (restrictedSigma F G g encode) ρ b M
    (dlogGenerable (F := F) g) S pk sk msg

end Schnorr
