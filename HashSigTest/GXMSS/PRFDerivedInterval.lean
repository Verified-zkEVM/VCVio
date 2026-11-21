/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Interval.PRFDerivedScheme
public import HashSigTest.GXMSS.PRFDerivedScheme

/-!
# Interval PRF-derived signing controls

Active signing retains first-success evidence, while an inactive request records its spent epoch
and returns failure without a retry prefix. Retry coordinates use the complete-query embedding.
-/

public section
namespace GXMSS.PRFIntervalProbe
open GXMSS.Probe GXMSS.IntervalMerkle

/-- A nonempty interior interval has both active and inactive epochs. -/
@[expose] def interior : Interval 3 := ⟨2, 4, by decide⟩

/-- Frontier and complete coordinates share one response type and one evaluator key. -/
@[expose] def evaluate :
    GXMSS.Interval.PRFDerived.Evaluator Bool Unit Unit (List ℕ × Bool) 3 1
  | key, .complete query => sharedSeedEvaluator key query
  | _, .filler _ _ _ => ([777], false)

/-- The filler projection is additional to the three complete projections. -/
@[expose] def projection :
    GXMSS.Interval.PRFDerived.Interpretation Unit (List ℕ) Bool (List ℕ × Bool) where
  toComplete := sharedSeedInterpretation
  fillerDigest := Prod.fst

/-- An active interval signature retains the same successful attempt and consumed prefix. -/
theorem active_prefix :
    let transition := GXMSS.Interval.PRFDerived.run (ChainProbe.traceInstance 3 3) enc
      evaluate projection 3 interior true 2 ()
    transition.result.attempt? = some 2 ∧ transition.result.consumed = [false, true] ∧
      transition.epoch = 2 := by
  exact ⟨rfl, rfl, rfl⟩

/-- An inactive epoch returns failure without consuming a randomizer. -/
theorem inactive_prefix :
    let transition := GXMSS.Interval.PRFDerived.run (ChainProbe.traceInstance 3 3) enc
      evaluate projection 3 interior true 0 ()
    transition.result.output = none ∧ transition.result.consumed = [] ∧
      transition.epoch = 0 := by
  exact ⟨rfl, rfl, rfl⟩

/-- The actual interval key generator uses its captured evaluator-key sampler. -/
theorem keygen_actual :
    GXMSS.Interval.PRFDerived.keygen (pure true) (ChainProbe.traceInstance 3 3)
      interior evaluate projection =
      pure (GXMSS.Interval.PRFDerived.keys (ChainProbe.traceInstance 3 3)
        interior evaluate projection true) := by
  simp [GXMSS.Interval.PRFDerived.keygen]

end GXMSS.PRFIntervalProbe
