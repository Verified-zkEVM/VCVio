/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import HashSigTest.SLHDSA.Refactor.ForsGraphSupport

/-! # Native exact observation of direct functional graph cells -/

public section

open SLHDSA.Refactor.ForsGraphSupport

private def ensure (message : String) (condition : Bool) : IO Unit :=
  unless condition do throw (IO.userError message)

private def replies : List (Label × Nat) :=
  [((prf 0, [7]), 777), ((prf 1, [7]), 617), ((leaf 1, [617]), 927),
    ((prf 2, [7]), 627), ((prf 3, [7]), 637), ((leaf 3, [637]), 967)]

private def events : List (Label × Nat) :=
  [((prf 0, [7]), 3), ((prf 1, [7]), 4), ((leaf 1, [617]), 6),
    ((prf 2, [7]), 5), ((prf 3, [7]), 6), ((leaf 3, [637]), 8)]

private def retained : Cache :=
  [((leaf 3, [637]), 967), ((prf 3, [7]), 637), ((prf 2, [7]), 627),
    ((leaf 1, [617]), 927), ((prf 1, [7]), 617)] ++ warm

/-- Run actual canonical callbacks and the same interpreted generic traversal with functional
    cells. -/
def main : IO Unit := do
  let (((actualSig, actualCost), actualCache), actualTrace) := run actual
  let (((graphSig, graphCost), graphCache), graphTrace) := run graph
  ensure "single complete signature/cache/cost/trace equality"
    (decide (signatureView actualSig = signatureView graphSig ∧
      actualCost.1 = graphCost.1 ∧ actualCost.2.toList = graphCost.2.toList ∧
      actualCache = graphCache ∧ actualTrace = graphTrace))
  ensure "distinct warm first-binding secret and complete authentication values"
    (signatureView actualSig == [(777, [927]), (627, [967])])
  ensure "all six attempts charged with input-dependent ordered cost32"
    (actualCost.1 == 32 && decide (actualCost.2.toList = events))
  ensure "complete retained cache and full input/answer trace with five misses"
    (decide (actualCache = retained ∧ actualTrace.replies = replies ∧ actualTrace.misses = 5))
  let ((((first, second), actualCost), actualCache), actualTrace) := run (twice actual)
  let ((((graphFirst, graphSecond), graphCost), graphCache), graphTrace) := run (twice graph)
  ensure "repeated complete signature/cache/cost/trace equality"
    (decide (signatureView first = signatureView graphFirst ∧
      signatureView second = signatureView graphSecond ∧ actualCost.1 = graphCost.1 ∧
      actualCost.2.toList = graphCost.2.toList ∧ actualCache = graphCache ∧ actualTrace =
          graphTrace))
  ensure "both complete signatures retain the same warm answers"
    (signatureView first == [(777, [927]), (627, [967])] &&
      signatureView second == [(777, [927]), (627, [967])])
  ensure "all twelve calls charged despite second-run hits; exact ordered cost64"
    (actualCost.1 == 64 && decide (actualCost.2.toList = events ++ events))
  ensure "repeat preserves complete cache and logs every input/answer with no extra draws"
    (decide (actualCache = retained ∧ actualTrace.replies = replies ++ replies ∧
      actualTrace.misses = 5))
  IO.println "Direct functional FORS graph: full signature/cache/trace/ordered-cost PASS"
