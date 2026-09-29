/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Oleksandr Vovkotrub
-/

module

public import VCVio.CryptoFoundations.Fischlin.KnowledgeSoundness.Induction
public import VCVio.EvalDist.ProbabilityNotation

/-!
# Acceptance and witness recovery for Fischlin

The joint execution retains both the actual verifier verdict and the witness returned by
`onlineExtract`. Its bad projection is the existing knowledge-soundness experiment, so the
checked bad-event bound gives a lower bound on recovery by that particular extractor.
The statement and message are fixed before the prover starts, the random oracle starts empty,
and the extractor receives only the prover's pre-verification query log.
-/

public section

open OracleComp OracleSpec MeasureTheory
open scoped ENNReal

namespace Fischlin

variable {Stmt Wit Commit PrvState Chal Resp : Type} {rel : Stmt → Wit → Bool}
variable [DecidableEq Stmt] [DecidableEq Commit] [DecidableEq Chal] [DecidableEq Resp]
  [FinEnum Chal] [Inhabited Chal] [Inhabited Resp]
variable (σ : SigmaProtocol Stmt Wit Commit PrvState Chal Resp rel)
  (hr : GenerableRelation Stmt Wit rel) (ρ b S : ℕ) (M : Type) [DecidableEq M]

/-- Run the prover, verify with the continuing oracle, then extract from the pre-verification
log. The result retains the verdict and the actual optional witness. -/
@[expose]
def knowledgeRun (adv : KnowledgeSoundnessAdversary (Stmt := Stmt)
    (Commit := Commit) (Chal := Chal) (Resp := Resp) ρ b M)
    (x : Stmt) (msg : M) : ProbComp (Bool × Option Wit) := do
  let roSpec := fischlinROSpec Stmt Commit Chal Resp ρ b M
  let ro : QueryImpl roSpec (StateT roSpec.QueryCache ProbComp) := randomOracle
  let ((π, roLog), cache) ←
    (simulateQ (unifSpec.passthrough + ro.withLogging) (adv.run x msg)).run.run ∅
  let (verified, _) ← (simulateQ (unifSpec.passthrough + ro)
    ((Fischlin (m := OracleComp (unifSpec + roSpec)) σ hr ρ b S M).verify x msg π)).run cache
  let extracted ← onlineExtract σ ρ b M x π roLog
  return (verified, extracted)

/-- The bad projection of the joint run is exactly the existing soundness experiment. -/
theorem knowledgeRun_bad (adv : KnowledgeSoundnessAdversary ρ b M) (x : Stmt) (msg : M) :
    (fun z : Bool × Option Wit => z.1 && !(z.2.any (rel x))) <$>
        knowledgeRun σ hr ρ b S M adv x msg =
      knowledgeSoundnessExperiment σ hr ρ b S M adv.run x msg := by
  simp only [knowledgeRun, knowledgeSoundnessExperiment, map_bind, map_pure]
  rfl

/-- The actual online extractor recovers a valid witness with probability at least acceptance
minus the single-proof knowledge error. -/
theorem extraction_success_ge_acceptance_sub_error
    (hss : σ.SpeciallySound) (hur : σ.UniqueResponses)
    (adv : KnowledgeSoundnessAdversary ρ b M) (Q : ℕ) (hρ : 0 < ρ)
    (hQ : ∀ x msg, ROQueryBound ρ b M (adv.run x msg) Q) (x : Stmt) (msg : M) :
    Pr{let z ← knowledgeRun σ hr ρ b S M adv x msg}[z.1 = true] -
        knowledgeSoundnessError Q ρ b S ≤
      Pr{let z ← knowledgeRun σ hr ρ b S M adv x msg}[z.2.any (rel x) = true] := by
  classical
  let : MeasurableSpace (Bool × Option Wit) := ⊤
  let run := knowledgeRun σ hr ρ b S M adv x msg
  have hbad : 𝒟[run] {z | z.1 = true ∧ z.2.any (rel x) ≠ true} ≤
      knowledgeSoundnessError Q ρ b S := by
    have heq : 𝒟[run] {z | z.1 = true ∧ z.2.any (rel x) ≠ true} =
        𝒟[knowledgeSoundnessExperiment σ hr ρ b S M adv.run x msg] {true} := by
      rw [← knowledgeRun_bad, evalDist_map_apply_of_discrete _ _ (measurableSet_singleton true)]
      congr 1
      ext z
      simp [Bool.not_eq_true]
    rw [heq]
    exact knowledgeSoundness σ hr ρ b S M hss hur adv Q hρ hQ x msg
  rw [prEvent_eq_evalDist_of_discrete, prEvent_eq_evalDist_of_discrete]
  apply tsub_le_iff_right.mpr
  calc
    𝒟[run] {z | z.1 = true} ≤ 𝒟[run]
        ({z | z.2.any (rel x) = true} ∪ {z | z.1 = true ∧ z.2.any (rel x) ≠ true}) :=
      measure_mono (by intro z hz; by_cases h : z.2.any (rel x) = true <;> simp_all)
    _ ≤ 𝒟[run] {z | z.2.any (rel x) = true} +
        𝒟[run] {z | z.1 = true ∧ z.2.any (rel x) ≠ true} := measure_union_le _ _
    _ ≤ _ := add_le_add le_rfl hbad

end Fischlin
