/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Examples.PRFTagReader.CacheRepresentation
public import VCVioTest.PRFReductionBudgets

/-!
# List-cached PRF services through ordinary imports

The adaptive tag/reader client uses the same cache cell for its tag response and
subsequent reader check. The tests exercise both concrete initial projections and
reply-dependent collision instrumentation, including the exhausted-tag boundary.
-/

public section

namespace PRFTagReader.CachedPRF.Tests

open OracleComp OracleSpec QueryBudgets.Tests

example : projectMultiple (TagId := Bool) (Nonce := Bool) (Digest := Bool)
    (UnlinkState.init, []) = (UnlinkState.init, ∅) := by simp

example : projectSingle (TagId := Bool) (Nonce := Bool) (Digest := Bool)
    (sessionsPerTag := 0) (UnlinkState.init, []) = (UnlinkState.init, ∅) := by simp

example : projectBad (TagId := Bool) (Nonce := Bool) (Digest := Bool)
    ((UnlinkState.init, []), UnlinkBadState.init) =
      ((UnlinkState.init, ∅), UnlinkBadState.init) := by simp

-- A first tag response records its cell; repeating that nonce raises the bad flag.
example :
    (advance (.inl false) (some ⟨false, true⟩)
      (advance (.inl false) (some ⟨false, true⟩)
        (UnlinkBadState.init : UnlinkBadState Bool Bool Bool))).bad = true := by
  decide

example :
    (advance (.inl true) (some ⟨false, true⟩)
      (advance (.inl false) (some ⟨false, true⟩)
        (UnlinkBadState.init : UnlinkBadState Bool Bool Bool))).bad = false := by
  decide

example (state : UnlinkBadState Bool Bool Bool) :
    advance (.inl false) none state = state := rfl

example (state : UnlinkBadState Bool Bool Bool) :
    advance (.inr ⟨false, true⟩) ReaderReply.ok state = state := rfl

-- Shadowed initial cells also project through the full adaptive client.
example :
    Prod.map id projectMultiple <$>
      (simulateQ (multiple (sessionsPerTag := 2)) adaptive).run
        (UnlinkState.init, [((false, false), true), ((false, false), false)]) =
    (simulateQ (multipleIdealQueryImpl (sessionsPerTag := 2)) adaptive).run
      (projectMultiple
        (UnlinkState.init, [((false, false), true), ((false, false), false)])) :=
  map_run_simulateQ_eq_of_query_map_eq _ _ projectMultiple multiple_local adaptive _

example :
    Network.verdict (multiple (sessionsPerTag := 2)) 2 adaptive (UnlinkState.init, []) =
      Network.verdict (multipleIdealQueryImpl (sessionsPerTag := 2)) 2 adaptive
        (UnlinkState.init, ∅) := by
  simpa using verdict_projection _ _ projectMultiple multiple_local 2 adaptive
    (Network.totalQueryBound adaptive 1 1 adaptive_reader_bound adaptive_tag_bound)
    (UnlinkState.init, [])

end PRFTagReader.CachedPRF.Tests
