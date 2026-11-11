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
Reruns on different inputs share the frozen coin, the cursor advances only the queried stream,
and the extractor's own coins stay fresh.
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
  simp [QueryImpl.add_apply_inr, StateT.run_bind,
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

/-- Advancing the cursor moves only the queried stream. -/
example : FixedTape.advance (fun _ => 0) 3 1 = 0 := by decide

example : FixedTape.advance (fun _ => 0) 3 3 = 1 := by decide

/-- A rerun whose output depends on its input: the same private coin, read directly or flipped. -/
@[expose] def flipRun (q : Bool) : ProbComp (Fin 2) :=
  (fun b => if q then b else Fin.rev b) <$> ($[0..1] : ProbComp (Fin 2))

/-- A black-box caller reruns on two different inputs. -/
@[expose] def twoInputs : OracleComp (unifSpec + rerunSpec Bool (Fin 2)) (Fin 2 × Fin 2) := do
  let x ← query (spec := unifSpec + rerunSpec Bool (Fin 2)) (Sum.inr true)
  let y ← query (spec := unifSpec + rerunSpec Bool (Fin 2)) (Sum.inr false)
  pure (x, y)

/-- Reruns on different inputs read the same frozen private coin: the two answers are a coin and
its flip. A policy that keyed the private tape by input would make them independent. -/
theorem attempt_twoInputs :
    fixedTape.attempt flipRun twoInputs =
      (fun b => ((b, Fin.rev b), 2)) <$> ($[0..1] : ProbComp (Fin 2)) := by
  unfold ResetPolicy.attempt fixedTape ResetPolicy.rerun twoInputs flipRun
  simp [QueryImpl.add_apply_inr, StateT.run_bind,
    FixedTape.answer, FixedTape.advance,
    uniformSample, ProbComp.uniformFin_def,
    map_eq_bind_pure_comp, bind_assoc]
  rfl

/-- The extractor flips two of its own coins and requests no rerun. -/
@[expose] def twoCoins : OracleComp (unifSpec + rerunSpec Unit (Fin 2)) (Fin 2 × Fin 2) := do
  let x ← query (spec := unifSpec + rerunSpec Unit (Fin 2)) (Sum.inl 1)
  let y ← query (spec := unifSpec + rerunSpec Unit (Fin 2)) (Sum.inl 1)
  pure (x, y)

/-- The extractor's own coins are fresh, not frozen: two flips are independent and no complete
run is charged. -/
theorem attempt_twoCoins :
    fixedTape.attempt (fun _ : Unit => ($[0..1] : ProbComp (Fin 2))) twoCoins =
      (do let a ← ($[0..1] : ProbComp (Fin 2))
          let b ← ($[0..1] : ProbComp (Fin 2))
          pure ((a, b), 0)) := by
  unfold ResetPolicy.attempt ResetPolicy.rerun twoCoins
  simp [QueryImpl.add_apply_inl, StateT.run_bind, coins,
    map_eq_bind_pure_comp, bind_assoc]
  rfl

/-- Execute repeated attempts and check the joint agreement and complete-run count. -/
def runTwoRerunsCheck : IO Unit := do
  for _ in List.range 8 do
    let z ← OracleComp.runIO
      (fixedTape.attempt (fun _ : Unit => ($[0..1] : ProbComp (Fin 2))) twoReruns)
    unless z.1.1 == z.1.2 && z.2 == 2 do
      throw <| IO.userError "fixed-tape rerun mismatch"

run_cmd liftM runTwoRerunsCheck

end VCVioTest.Rewinding
