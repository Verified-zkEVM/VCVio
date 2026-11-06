/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.CryptoFoundations.Rewinding.FixedTape
meta import VCVio.CryptoFoundations.Rewinding.FixedTape
meta import VCVio.OracleComp.RunIO
import VCVio.OracleComp.RunIO

/-!
# Fixed-tape rerun regression

Two complete executions of a private coin flip consume the same frozen tape entry. The
black-box caller receives equal answers, while its complete-run counter records both calls.
-/

public section

open OracleComp OracleSpec Rewinding

namespace VCVioTest.Rewinding

/-- A black-box caller requests the same private coin flip twice. -/
@[expose] def twoReruns : OracleComp (unifSpec + rerunSpec Unit (Fin 2)) (Fin 2 × Fin 2) := do
  let x ← query (spec := unifSpec + rerunSpec Unit (Fin 2)) (Sum.inr ())
  let y ← query (spec := unifSpec + rerunSpec Unit (Fin 2)) (Sum.inr ())
  pure (x, y)

/-- Both reruns read the same tape entry and each charges one complete run. -/
theorem attempt_twoReruns :
    fixedTape.attempt (fun _ : Unit => ($[0..1] : ProbComp (Fin 2))) twoReruns =
      (fun b => ((b, b), 2)) <$> ($[0..1] : ProbComp (Fin 2)) := by
  unfold ResetPolicy.attempt fixedTape ResetPolicy.rerun twoReruns
  simp [simulateQ_bind, QueryImpl.add_apply_inr, StateT.run_bind,
    FixedTape.answer, FixedTape.advance,
    uniformSample, ProbComp.uniformFin_def,
    map_eq_bind_pure_comp, bind_assoc]
  rfl

/-- The fixed private coin agrees across two reruns with probability one, and the count is two. -/
theorem twoReruns_equal_count :
    Pr{let z ← fixedTape.attempt
        (fun _ : Unit => ($[0..1] : ProbComp (Fin 2))) twoReruns}[z.1.1 = z.1.2 ∧ z.2 = 2] = 1 := by
  rw [attempt_twoReruns]
  simp

/-- The expected number of complete runs in the two-call experiment is exactly two. -/
theorem expectedCalls_twoReruns :
    expectedCalls (fixedTape.attempt
      (fun _ : Unit => ($[0..1] : ProbComp (Fin 2))) twoReruns) = 2 := by
  rw [attempt_twoReruns]
  simp [expectedCalls, AddWriterT.expectedCostNat, AddWriterT.expectedCost,
    AddWriterT.costs_def]

/-- Execute repeated attempts and check the joint agreement and complete-run count. -/
def runTwoRerunsCheck : IO Unit := do
  for _ in List.range 8 do
    let z ← OracleComp.runIO
      (fixedTape.attempt (fun _ : Unit => ($[0..1] : ProbComp (Fin 2))) twoReruns)
    unless z.1.1 == z.1.2 && z.2 == 2 do
      throw <| IO.userError "fixed-tape rerun mismatch"

run_cmd liftM runTwoRerunsCheck

end VCVioTest.Rewinding
