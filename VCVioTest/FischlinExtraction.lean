/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.CryptoFoundations.Fischlin.ExtractionGuarantee
public import VCVio.CryptoFoundations.Fischlin.ExtractionCost
public import VCVioTest.FiatShamirKnowledgeExtraction

/-!
# Fischlin extraction and log-inspection consumers

A deterministic fixture checks empty scans, early stopping at the first matching record,
and preservation of the actual extracted witness. The guarantee uses the prover's log before
verification; verification queries do not become evidence supplied to the online extractor.
-/

public section

open OracleComp OracleSpec Fischlin FiatShamirKnowledgeExtractionTest

namespace FischlinExtractionTest

/-- A one-repetition proof with a fixed challenge. -/
@[expose]
def proof : FischlinProof Bool Bool Unit 1 := fun _ => (false, false, ())

/-- An accepting logged response with a different challenge from the proof. -/
@[expose]
def record : FischlinROInput Unit Bool Bool Unit 1 Unit :=
  ⟨(), (), [false], 0, true, ()⟩

/-- A prover that has made no queries when it submits its proof. -/
@[expose]
def prover : KnowledgeSoundnessAdversary (Stmt := Unit) (Commit := Bool) (Chal := Bool)
    (Resp := Unit) 1 1 Unit where
  run _ _ := pure proof

example (ρ : ℕ) (π : FischlinProof Bool Bool Unit ρ) :
    onlineExtractWithScanCount protocol ρ 1 Unit () π [] = pure (none, 0) :=
  onlineExtractWithScanCount_nil protocol ρ 1 Unit () π

example (π : FischlinProof Bool Bool Unit 0)
    (log : QueryLog (fischlinROSpec Unit Bool Bool Unit 0 1 Unit)) :
    onlineExtractWithScanCount protocol 0 1 Unit () π log = pure (none, 0) :=
  onlineExtractWithScanCount_zero protocol 1 Unit () π log

-- The arbitrary tail is never scanned after a first-record match.
example (log : QueryLog (fischlinROSpec Unit Bool Bool Unit 1 1 Unit)) :
    onlineExtractWithScanCount protocol 1 1 Unit () proof (⟨record, 0⟩ :: log) =
      pure (some (), 1) := by
  rw [onlineExtractWithScanCount_cons_of_match protocol 1 Unit () proof ⟨record, 0⟩ log
    rfl (by decide) rfl (by decide)]
  simp [protocol]

example (log : QueryLog (fischlinROSpec Unit Bool Bool Unit 1 1 Unit)) :
    Prod.fst <$> onlineExtractWithScanCount protocol 1 1 Unit () proof log =
      onlineExtract protocol 1 1 Unit () proof log :=
  onlineExtractWithScanCount_fst protocol 1 1 Unit () proof log

example (log : QueryLog (fischlinROSpec Unit Bool Bool Unit 1 1 Unit))
    (z : Option Unit × ℕ)
    (hz : z ∈ support (onlineExtractWithScanCount protocol 1 1 Unit () proof log)) :
    z.2 ≤ log.length := by
  simpa only [one_mul] using onlineExtractWithScanCount_le protocol 1 1 Unit () proof log hz

example : onlineExtract protocol 1 1 Unit () proof [] = pure none := by
  rw [← onlineExtractWithScanCount_fst, onlineExtractWithScanCount_nil, map_pure]

example : (fun z : Bool × Option Unit => z.1 && !(z.2.any (fun _ => true))) <$>
      knowledgeRun protocol relation 1 1 0 Unit prover () () =
    knowledgeSoundnessExp protocol relation 1 1 0 Unit prover.run () () :=
  knowledgeRun_bad protocol relation 1 1 0 Unit prover () ()

example :
    Pr{let z ← knowledgeRun protocol relation 1 1 0 Unit prover () ()}[z.1 = true] -
        knowledgeSoundnessError 0 1 1 0 ≤
      Pr{let z ← knowledgeRun protocol relation 1 1 0 Unit prover () ()}[
        z.2.any (fun _ => true) = true] :=
  extraction_success_ge_acceptance_sub_error protocol relation 1 1 0 Unit
    (by intro x pc c₁ c₂ p₁ p₂ hne hv₁ hv₂ w hw; rfl)
    (by intro x pc c p₁ p₂ hv₁ hv₂; exact Subsingleton.elim _ _)
    prover 0 (by decide) (by intro x msg; trivial) () ()

end FischlinExtractionTest
